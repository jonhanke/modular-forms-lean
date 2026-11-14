import ModularFormsKB.Miyake.Wave4.MiyakeHecke
import ModularFormsKB.Miyake.Wave3.HeckeStatements
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.ElementaryDivisors

/-!
# Miyake, Lemma 4.5.2 and Theorem 4.5.9 (generation): the generators of `ℛ(N)`

Miyake, *Modular Forms* (Springer 1989), §4.5, pp. 133 and 142.

* **Lemma 4.5.2** (`exists_single_eq_heckeTPair`): every double coset `Γ₀(N) α Γ₀(N)` of
  `Δ₀(N)` is `T(l, m) = Γ₀(N) diag(l, m) Γ₀(N)` for some `l ∣ m` with `(l, N) = 1`; `l` is the
  greatest common divisor of the entries of `α` and `l m = det α`. The proof reads the double
  coset off the elementary divisors (Tau Ceti `HeckeRing.GL2.mem_doubleCoset_of_det_eq_of_dvd_iff`,
  Shimura Proposition 3.32).
* **Theorem 4.5.9**, generation half (`closure_heckeGenerator_eq_top`): `ℛ(N)` is generated as a
  ring by `T(p)`, `T(p, p)` (`p ∤ N`) and `T(q)` (`q ∣ N`). Miyake's proof: by Lemma 4.5.2 the
  `T(l, m)` span `ℛ(N)`; `T(l, m) = T(l, l) T(1, m/l)`, `T(l, l)` is a product of `T(p, p)`,
  `T(1, n)` is a product of `T(1, p^e)` (Lemma 4.5.8 (1)), and `T(1, p^e)` is a polynomial in
  `T(p)`, `T(p, p)` (Lemma 4.5.7 (1)). Stated here from the double-coset relations
  `DoubleCosetRelations N` of wave 4; `Wave5/DoubleCosetRelations.lean` supplies them.

The algebraic independence of the generators (the other half of Theorem 4.5.9) is not proved
here.
-/

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups HeckeCosetModule

noncomputable section

namespace ModularFormsKB.Miyake.Wave5

open ModularFormsKB.Miyake.Wave4

variable (N : ℕ) [NeZero N]

/-- **Miyake, Lemma 4.5.2** (at level `Γ₀(N)`): every double coset of `Δ₀(N)` modulo `Γ₀(N)` is
some `T(l, m)` with `0 < l`, `l ∣ m`, `(l, N) = 1`. -/
@[kb "miyake1989" "Lemma 4.5.2, p. 133"]
theorem exists_single_eq_heckeTPair
    (D : HeckeCoset (HeckeRing.GL2.Delta0 N) ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ))) :
    ∃ l m : ℕ, 0 < l ∧ l ∣ m ∧ 0 < m ∧ l.Coprime N ∧
      HeckeCosetModule.single ℤ D 1 = heckeTPair N l m := by
  classical
  obtain ⟨A, hA, hdetpos, hAN, hAu⟩ := (HeckeRing.GL2.mem_Delta0_iff N).mp D.rep.2
  -- `g` is the greatest common divisor of the entries of `A`
  set g : ℕ := Int.gcd ((A 0 0).gcd (A 0 1) : ℤ) ((A 1 0).gcd (A 1 1) : ℤ) with hg
  have hdvdg : ∀ e : ℤ, (∀ i j, e ∣ A i j) ↔ e ∣ (g : ℤ) := by
    intro e
    constructor
    · intro h
      exact Int.dvd_coe_gcd (Int.dvd_coe_gcd (h 0 0) (h 0 1)) (Int.dvd_coe_gcd (h 1 0) (h 1 1))
    · intro h i j
      have h1 : e ∣ ((A 0 0).gcd (A 0 1) : ℤ) := h.trans (Int.gcd_dvd_left _ _)
      have h2 : e ∣ ((A 1 0).gcd (A 1 1) : ℤ) := h.trans (Int.gcd_dvd_right _ _)
      fin_cases i <;> fin_cases j
      · exact h1.trans (Int.gcd_dvd_left _ _)
      · exact h1.trans (Int.gcd_dvd_right _ _)
      · exact h2.trans (Int.gcd_dvd_left _ _)
      · exact h2.trans (Int.gcd_dvd_right _ _)
  have hgA : ∀ i j, (g : ℤ) ∣ A i j := (hdvdg g).mpr dvd_rfl
  have hAdet : 0 < A.det := by
    rw [← Int.cast_pos (R := ℚ), Int.cast_det, ← hA]
    exact hdetpos
  have hgg : (g : ℤ) * g ∣ A.det := by
    rw [Matrix.det_fin_two]
    exact dvd_sub (mul_dvd_mul (hgA 0 0) (hgA 1 1)) (mul_dvd_mul (hgA 0 1) (hgA 1 0))
  have hgpos : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h
    · exfalso
      rw [h0, Nat.cast_zero, zero_mul, zero_dvd_iff] at hgg
      exact hAdet.ne' hgg
    · exact h
  -- `n = det A` and `m = n / g`
  set n : ℕ := A.det.toNat with hn
  have hnA : (n : ℤ) = A.det := Int.toNat_of_nonneg hAdet.le
  have hggn : g * g ∣ n := by
    rw [← Int.natCast_dvd_natCast, hnA]; exact_mod_cast hgg
  set m : ℕ := n / g with hm
  have hgm : g * m = n := Nat.mul_div_cancel' ((Nat.dvd_mul_right g g).trans hggn)
  have hgdm : g ∣ m := by
    rw [hm]; exact Nat.dvd_div_of_mul_dvd hggn
  have hnpos : 0 < n := by
    have : (0 : ℤ) < n := hnA ▸ hAdet
    exact_mod_cast this
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h
    · rw [h0, mul_zero] at hgm; omega
    · exact h
  -- `g` is prime to `N`, because it divides the upper-left entry
  have hAco : Int.gcd (A 0 0) N = 1 := Int.isUnit_intCast_iff_gcd_eq_one.mp hAu
  have hgN : g.Coprime N := by
    have h1 : g ∣ (A 0 0).natAbs := Int.natCast_dvd.mp (hgA 0 0)
    exact Nat.Coprime.coprime_dvd_left h1 hAco
  have hpos : ∀ i, 0 < (![g, m] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [hgpos, hmpos]
  have hcop : Nat.Coprime ((![g, m] : Fin 2 → ℕ) 0) N := hgN
  have hα := HeckeRing.GL2.natDiagGL_mem_Delta0_of_coprime N ![g, m] fun _ ↦ hcop
  have hmem := HeckeRing.GL2.mem_doubleCoset_of_det_eq_of_dvd_iff N hα D.rep.2
    (A := Matrix.diagonal fun i ↦ ((![g, m] : Fin 2 → ℕ) i : ℤ)) (B := A)
    (HeckeRing.GLn.natDiagGL_coe_eq_map_intCast 2 _ hpos) hA
    (by
      rw [Matrix.det_diagonal, Fin.prod_univ_two, ← hnA, ← hgm]
      simp)
    (by
      intro e
      rw [hdvdg e]
      constructor
      · intro h
        simpa using h 0 0
      · intro h i j
        rcases eq_or_ne i j with rfl | hij
        · fin_cases i
          · simpa using h
          · simpa using h.trans (Int.natCast_dvd_natCast.mpr hgdm)
        · rw [Matrix.diagonal_apply_ne _ hij]; exact dvd_zero e)
  refine ⟨g, m, hgpos, hgdm, hmpos, hgN, ?_⟩
  have hD : D = HeckeRing.GL2.diagCosetGamma0 N ![g, m] (fun _ ↦ hcop) := by
    rw [HeckeRing.GL2.diagCosetGamma0_def, ← HeckeCoset.mk_rep D]
    exact HeckeCoset.mk_eq_mk_of_mem (g₂ := ⟨_, hα⟩) hmem
  rw [hD]
  exact (HeckeRing.GL2.diagElemGamma0_of_pos_of_coprime N hpos hcop).symm

/-- The ring generated by Miyake's generators of `ℛ(N)`. -/
local notation "𝒮" => Subring.closure (Set.range (heckeGenerator N))

private lemma heckeTPair_scalar_mul' (c b : ℕ) :
    heckeTPair N c (c * b) = heckeTPair N c c * heckeTPair N 1 b := by
  have h := HeckeRing.GL2.diagElemGamma0_const_mul N c ![1, b]
  have e1 : ((fun _ : Fin 2 ↦ c) : Fin 2 → ℕ) = ![c, c] := by ext i; fin_cases i <;> rfl
  have e2 : ((fun _ : Fin 2 ↦ c) * ![1, b] : Fin 2 → ℕ) = ![c, c * b] := by
    ext i; fin_cases i <;> simp
  rw [e2, e1] at h
  exact h.symm

private lemma heckeTPair_one_one : heckeTPair N 1 1 = 1 := by
  have := HeckeRing.GL2.heckeTGeneratorGamma0_one N
  rwa [HeckeRing.GL2.heckeTGeneratorGamma0_def] at this

private lemma heckeTPair_zero_right (l : ℕ) : heckeTPair N l 0 = 0 :=
  HeckeRing.GL2.diagElemGamma0_of_not_pos N fun h ↦ by simpa using h 1

private lemma gen_mem {p : ℕ} (hp : p.Prime) : heckeTPair N 1 p ∈ 𝒮 := by
  by_cases hpN : p ∣ N
  · have h : heckeGenerator N (.inr (.inr ⟨p, hp, hpN⟩)) = heckeTPair N 1 p :=
      HeckeRing.GL2.heckeTGeneratorGamma0_def N p
    exact h ▸ Subring.subset_closure ⟨_, rfl⟩
  · have h : heckeGenerator N (.inl ⟨p, hp, hpN⟩) = heckeTPair N 1 p :=
      HeckeRing.GL2.heckeTGeneratorGamma0_def N p
    exact h ▸ Subring.subset_closure ⟨_, rfl⟩

private lemma scalar_mem (l : ℕ) : heckeTPair N l l ∈ 𝒮 := by
  induction l using Nat.recOnMul with
  | zero => rw [heckeTPair_zero_right]; exact zero_mem _
  | one => rw [heckeTPair_one_one]; exact one_mem _
  | prime p hp =>
    by_cases hpN : p ∣ N
    · have hnc : ¬ Nat.Coprime p N := by rwa [hp.coprime_iff_not_dvd, not_not]
      rw [show heckeTPair N p p = 0 from
        HeckeRing.GL2.diagElemGamma0_of_not_coprime N (a := ![p, p]) (by simpa using hnc)]
      exact zero_mem _
    · have h : heckeGenerator N (.inr (.inl ⟨p, hp, hpN⟩)) = heckeTPair N p p :=
        HeckeRing.GL2.heckeTScalarGamma0_def N p
      exact h ▸ Subring.subset_closure ⟨_, rfl⟩
  | mul a b ha hb =>
    have h := HeckeRing.GL2.heckeTScalarGamma0_mul N a b
    simp only [HeckeRing.GL2.heckeTScalarGamma0_def] at h
    have h' : heckeTPair N (a * b) (a * b) = heckeTPair N a a * heckeTPair N b b := h.symm
    rw [h']
    exact mul_mem ha hb

private lemma primePow_mem (hR : DoubleCosetRelations N) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    heckeTPair N 1 (p ^ e) ∈ 𝒮 := by
  by_cases hpN : p ∣ N
  · induction e with
    | zero => rw [pow_zero, heckeTPair_one_one]; exact one_mem _
    | succ e ih =>
      rw [← hR.one_prime_mul_of_dvd hp hpN e]
      exact mul_mem (gen_mem N hp) ih
  · induction e using Nat.twoStepInduction with
    | zero => rw [pow_zero, heckeTPair_one_one]; exact one_mem _
    | one => rw [pow_one]; exact gen_mem N hp
    | more e ih0 ih1 =>
      have h := hR.one_prime_mul hp hpN (e := e + 1) (by omega)
      have hsc : heckeTPair N p (p ^ (e + 1)) = heckeTPair N p p * heckeTPair N 1 (p ^ e) := by
        rw [← heckeTPair_scalar_mul', ← pow_succ']
      rw [hsc] at h
      have h' : heckeTPair N 1 (p ^ (e + 2)) = heckeTPair N 1 p * heckeTPair N 1 (p ^ (e + 1)) -
          ((if e + 1 = 1 then p + 1 else p : ℕ) : ℤ) •
            (heckeTPair N p p * heckeTPair N 1 (p ^ e)) := by
        rw [h]; abel
      rw [h', zsmul_eq_mul]
      refine sub_mem (mul_mem (gen_mem N hp) ih1) (mul_mem (intCast_mem _ _) ?_)
      exact mul_mem (scalar_mem N p) ih0

private lemma one_pair_mem (hR : DoubleCosetRelations N) (n : ℕ) : heckeTPair N 1 n ∈ 𝒮 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => rw [heckeTPair_zero_right]; exact zero_mem _
  | one => rw [heckeTPair_one_one]; exact one_mem _
  | prime_pow p e hp _ => exact primePow_mem N hR hp e
  | coprime a b _ _ hab ha hb =>
    have h := hR.mul_of_coprime (one_dvd a) (one_dvd b) (by simpa using hab)
    rw [one_mul] at h
    rw [← h]
    exact mul_mem ha hb

private lemma pair_mem (hR : DoubleCosetRelations N) {l m : ℕ} (hlm : l ∣ m) :
    heckeTPair N l m ∈ 𝒮 := by
  obtain ⟨b, rfl⟩ := hlm
  rw [heckeTPair_scalar_mul']
  exact mul_mem (scalar_mem N l) (one_pair_mem N hR b)

/-- **Miyake, Theorem 4.5.9**, generation half: given the double-coset relations of
Lemmas 4.5.7 (1) and 4.5.8 (1), the ring `ℛ(N)` is generated by `T(p)`, `T(p, p)` (`p ∤ N`)
and `T(q)` (`q ∣ N`). -/
theorem closure_heckeGenerator_eq_top_of_relations (hR : DoubleCosetRelations N) :
    Subring.closure (Set.range (heckeGenerator N)) = ⊤ := by
  refine eq_top_iff.mpr fun t _ ↦ ?_
  refine HeckeCosetModule.induction_linear ℤ t (zero_mem _) (fun f g hf hg ↦ add_mem hf hg) ?_
  intro D b
  obtain ⟨l, m, hl, hlm, -, -, hD⟩ := exists_single_eq_heckeTPair N D
  have h1 : HeckeCosetModule.single ℤ D 1 ∈ Subring.closure (Set.range (heckeGenerator N)) :=
    hD ▸ pair_mem N hR hlm
  induction b using Int.induction_on with
  | zero => rw [HeckeCosetModule.single_zero]; exact zero_mem _
  | succ i hi => rw [HeckeCosetModule.single_add]; exact add_mem hi h1
  | pred i hi =>
    have hneg : HeckeCosetModule.single ℤ D (-1) = -HeckeCosetModule.single ℤ D 1 := by
      refine eq_neg_of_add_eq_zero_left ?_
      rw [← HeckeCosetModule.single_add, neg_add_cancel, HeckeCosetModule.single_zero]
    rw [sub_eq_add_neg, HeckeCosetModule.single_add, hneg]
    exact add_mem hi (neg_mem h1)

end ModularFormsKB.Miyake.Wave5
