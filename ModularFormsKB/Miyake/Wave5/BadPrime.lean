import ModularFormsKB.Miyake.Wave4.MiyakeHecke
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.BadPrimeCoset
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.PrimeCosets
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.UpperTriCosets
import TauCeti.NumberTheory.HeckeRing.Degree
import TauCeti.Data.ZMod.Divisibility

/-!
# Miyake, Lemma 4.5.6 and Lemma 4.5.7 (1) for a prime `p` dividing the level

Miyake, *Modular Forms* (Springer 1989), §4.5, pp. 138–140.

For a prime `p ∣ N` and `e ≥ 0`:

* Lemma 4.5.6 (1): `Γ₀(N) diag(1, p^e) Γ₀(N) = ⊔_{0 ≤ m < p^e} Γ₀(N) [1 m; 0 p^e]`
  (`doubleCoset_one_prime_pow_eq_iUnion_of_dvd`), and the union is disjoint;
* Lemma 4.5.6 (2): the degree of `T(1, p^e)` is `p^e` (`degree_one_prime_pow_of_dvd`);
* Lemma 4.5.7 (1): `T(1, p) T(1, p^e) = T(1, p^{e+1})` (`heckeTPair_one_prime_mul_of_dvd`).

The proof of Lemma 4.5.7 (1) is Miyake's: every product of an element of `T(1, p)` and one of
`T(1, p^e)` is primitive (its upper-left entry is prime to `p`), so it lies in `T(1, p^{e+1})`
(Tau Ceti `HeckeRing.GL2.mem_doubleCoset_natDiagGL_of_primitive`); the product is therefore
`a T(1, p^{e+1})`, and comparing degrees, `p · p^e = a p^{e+1}`, gives `a = 1`.
-/

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups HeckeCosetModule Pointwise

noncomputable section

namespace ModularFormsKB.Miyake.Wave5

open ModularFormsKB.Miyake.Wave4 HeckeRing.GLn

variable (N : ℕ) [NeZero N]

/-! ### Index of `Γ₀(M p)` in `Γ₀(M)` for `p ∣ M` -/

/-- The lower unitriangular representative `[1 0; c M 1]`. -/
private def lowerRep (M : ℕ) (c : ℤ) : SL(2, ℤ) :=
  ⟨!![1, 0; c * (M : ℤ), 1], by simp [Matrix.det_fin_two_of]⟩

private lemma lowerRep_mem (M : ℕ) (c : ℤ) : lowerRep M c ∈ Gamma0 M := by
  rw [Gamma0_mem]
  simp [lowerRep]

private lemma lowerRep_inv_mul_10 (M : ℕ) (c : ℤ) (σ : SL(2, ℤ)) :
    ((lowerRep M c)⁻¹ * σ).1 1 0 = σ.1 1 0 - c * (M : ℤ) * σ.1 0 0 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [Matrix.SpecialLinearGroup.inv_apply_one_zero, Matrix.SpecialLinearGroup.inv_apply_one_one]
  simp [lowerRep]
  ring

private lemma lowerRep_diff (M : ℕ) (c₁ c₂ : ℤ) :
    ((lowerRep M c₁)⁻¹ * lowerRep M c₂).1 1 0 = (c₂ - c₁) * (M : ℤ) := by
  rw [lowerRep_inv_mul_10]
  simp [lowerRep]
  ring

private def lowerRepSub (M : ℕ) (c : ℤ) : ↥(Gamma0 M) := ⟨lowerRep M c, lowerRep_mem M c⟩

private lemma relIndex_Gamma0_mul_prime {p M : ℕ} (hp : 0 < p) (hpM : p ∣ M) (hM : 0 < M) :
    (Gamma0 (M * p)).relIndex (Gamma0 M) = p := by
  have : NeZero p := ⟨hp.ne'⟩
  have hMz : (M : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hM.ne'
  refine Nat.card_eq_of_equiv_fin (Equiv.ofBijective
    (fun c : Fin p ↦ (QuotientGroup.mk (lowerRepSub M (c : ℕ)) :
      ↥(Gamma0 M) ⧸ (Gamma0 (M * p)).subgroupOf (Gamma0 M))) ⟨?_, ?_⟩).symm
  · intro ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ hf
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, mem_Gamma0_iff_dvd] at hf
    simp only [lowerRepSub, InvMemClass.coe_inv, MulMemClass.coe_mul] at hf
    rw [lowerRep_diff] at hf
    push_cast at hf
    rw [mul_comm (M : ℤ) (p : ℤ), mul_dvd_mul_iff_right hMz] at hf
    have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hf (by simp; omega)
    exact Fin.mk_eq_mk.mpr (by omega)
  · intro x
    obtain ⟨⟨σ, hσ_K⟩, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨q, hq⟩ : (M : ℤ) ∣ σ.1 1 0 := mem_Gamma0_iff_dvd.mp hσ_K
    have h00_unit : IsUnit ((σ.1 0 0 : ℤ) : ZMod p) :=
      isUnit_intCast_apply_zero_zero_of_mem_Gamma0
        (mem_Gamma0_iff_dvd.mpr (hq ▸ dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hpM) q))
    obtain ⟨c₀, hc₀⟩ := ZMod.exists_dvd_sub_val_mul p q (σ.1 0 0) h00_unit
    refine ⟨⟨c₀.val, ZMod.val_lt c₀⟩, ?_⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [lowerRepSub, InvMemClass.coe_inv, MulMemClass.coe_mul]
    rw [mem_Gamma0_iff_dvd, lowerRep_inv_mul_10, hq]
    push_cast
    calc (M : ℤ) * (p : ℤ) ∣ (M : ℤ) * (q - ↑c₀.val * σ.1 0 0) := mul_dvd_mul_left _ hc₀
      _ = _ := by ring

private lemma relIndex_Gamma0_mul_prime_pow {p : ℕ} (hp : 0 < p) (hpN : p ∣ N) (e : ℕ) :
    (Gamma0 (N * p ^ e)).relIndex (Gamma0 N) = p ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hle : Gamma0 (N * p ^ (e + 1)) ≤ Gamma0 (N * p ^ e) :=
      Gamma0_le_Gamma0_of_dvd (Nat.mul_dvd_mul_left N (pow_dvd_pow p e.le_succ))
    have hpM : p ∣ N * p ^ e := hpN.mul_right _
    have hM : 0 < N * p ^ e := Nat.mul_pos (Nat.pos_of_neZero N) (pow_pos hp e)
    have h := relIndex_Gamma0_mul_prime hp hpM hM
    have h' : (Gamma0 (N * p ^ (e + 1))).relIndex (Gamma0 (N * p ^ e)) = p := by
      rw [pow_succ, ← mul_assoc]; exact h
    have := Subgroup.relIndex_mul_relIndex _ _ _ hle
      (Gamma0_le_Gamma0_of_dvd (dvd_mul_right N (p ^ e)))
    rw [h', ih] at this
    rw [← this, pow_succ, mul_comm]


/-! ### The intersection `diag(1, m) Γ₀(N) diag(1, m)⁻¹ ∩ Γ₀(N) = Γ₀(N m)` -/

private lemma exists_conj_of_dvd (N : ℕ) {m : ℕ} (hm : 0 < m) {σ : SL(2, ℤ)}
    (hσ : ((N * m : ℕ) : ℤ) ∣ σ 1 0) :
    ∃ τ : SL(2, ℤ), τ ∈ Gamma0 N ∧
      natDiagGL 2 ![1, m] * mapGL ℚ τ = mapGL ℚ σ * natDiagGL 2 ![1, m] := by
  obtain ⟨c, hc⟩ := hσ
  push_cast at hc
  have hdet := Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one σ
  let τ : SL(2, ℤ) := ⟨!![σ 0 0, (m : ℤ) * σ 0 1; (N : ℤ) * c, σ 1 1], by
    rw [Matrix.det_fin_two_of]
    rw [hc] at hdet
    linear_combination hdet⟩
  have h10 : (τ 1 0 : ℤ) = (N : ℤ) * c := rfl
  refine ⟨τ, Gamma0_mem.mpr (by rw [h10]; push_cast; simp), ?_⟩
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, HeckeRing.GL2.coe_natDiagGL_one hm,
    coe_mapGL_int_rat_fin_two τ, coe_mapGL_int_rat_fin_two σ]
  have h00 : (τ 0 0 : ℤ) = σ 0 0 := rfl
  have h01 : (τ 0 1 : ℤ) = (m : ℤ) * σ 0 1 := rfl
  have h11 : (τ 1 1 : ℤ) = σ 1 1 := rfl
  rw [h00, h01, h10, h11]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc] <;> ring

private lemma dvd_of_conj {m : ℕ} (hm : 0 < m) {σ τ : SL(2, ℤ)}
    (h : natDiagGL 2 ![1, m] * mapGL ℚ τ = mapGL ℚ σ * natDiagGL 2 ![1, m]) :
    σ 1 0 = (m : ℤ) * τ 1 0 := by
  have h10 := congr_arg (fun M : GL (Fin 2) ℚ ↦ (M : Matrix (Fin 2) (Fin 2) ℚ) 1 0) h
  simp only [Units.val_mul, HeckeRing.GL2.coe_natDiagGL_one hm,
    coe_mapGL_int_rat_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at h10
  simp at h10
  exact_mod_cast h10.symm

private lemma conj_inf_eq {m : ℕ} (hm : 0 < m) :
    (ConjAct.toConjAct (natDiagGL 2 ![1, m]) • ((Gamma0 N).map (mapGL ℚ))) ⊓
      ((Gamma0 N).map (mapGL ℚ)) = (Gamma0 (N * m)).map (mapGL ℚ) := by
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨h_smul, σ, hσ, rfl⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
      ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at h_smul
    obtain ⟨τ, hτ, hτeq⟩ := Subgroup.mem_map.mp h_smul
    have hcomm : natDiagGL 2 ![1, m] * mapGL ℚ τ = mapGL ℚ σ * natDiagGL 2 ![1, m] := by
      rw [hτeq]; group
    have := dvd_of_conj hm hcomm
    refine ⟨σ, mem_Gamma0_iff_dvd.mpr ?_, rfl⟩
    obtain ⟨k, hk⟩ := mem_Gamma0_iff_dvd.mp hτ
    exact ⟨k, by rw [this, hk]; push_cast; ring⟩
  · rintro ⟨σ, hσ, rfl⟩
    have hσ' := mem_Gamma0_iff_dvd.mp hσ
    have hσN : σ ∈ Gamma0 N := mem_Gamma0_iff_dvd.mpr (dvd_trans (by simp) hσ')
    obtain ⟨τ, hτ, hcomm⟩ := exists_conj_of_dvd N hm hσ'
    refine ⟨?_, σ, hσN, rfl⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
      ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
    refine Subgroup.mem_map.mpr ⟨τ, hτ, ?_⟩
    rw [mul_assoc, eq_comm, inv_mul_eq_iff_eq_mul]
    exact hcomm.symm

/-- **Miyake, Lemma 4.5.6 (2)** for `p ∣ N`: the double coset `Γ₀(N) diag(1, p^e) Γ₀(N)` has
degree `p^e`. -/
@[kb "miyake1989" "Lemma 4.5.6 (2), p. 138 (p dividing N)"]
theorem degree_one_prime_pow_of_dvd {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (e : ℕ) :
    (HeckeRing.GL2.diagCosetGamma0 N ![1, p ^ e] fun _ ↦ Nat.coprime_one_left N).degree =
      p ^ e := by
  have hm : 0 < p ^ e := pow_pos hp.pos e
  refine (HeckeCoset.degree_mk (H₁ := (Gamma0 N).map (mapGL ℚ)) (H₂ := (Gamma0 N).map (mapGL ℚ))
    ⟨natDiagGL 2 ![1, p ^ e],
      HeckeRing.GL2.natDiagGL_mem_Delta0_of_coprime N _ fun _ ↦ Nat.coprime_one_left N⟩).trans ?_
  show (ConjAct.toConjAct (natDiagGL 2 ![1, p ^ e]) •
    ((Gamma0 N).map (mapGL ℚ))).relIndex ((Gamma0 N).map (mapGL ℚ)) = p ^ e
  rw [← Subgroup.inf_relIndex_right, conj_inf_eq N hm,
    Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective,
    relIndex_Gamma0_mul_prime_pow N hp.pos hpN e]


/-! ### The product `T(1, p) T(1, p^e)` -/

private lemma key_mem {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (e : ℕ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) :
    natDiagGL 2 ![1, p] * mapGL ℚ γ * natDiagGL 2 ![1, p ^ e] ∈
      DoubleCoset.doubleCoset (natDiagGL 2 ![1, p ^ (e + 1)])
        ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
  have hdet := Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
  have hγ10 := mem_Gamma0_iff_dvd.mp hγ
  refine HeckeRing.GL2.mem_doubleCoset_natDiagGL_of_intWitness N (p ^ (e + 1)) _
    !![γ 0 0, γ 0 1 * (p : ℤ) ^ e; (p : ℤ) * γ 1 0, (p : ℤ) ^ (e + 1) * γ 1 1] ?_ ?_ ?_ ?_
  · rw [Units.val_mul, Units.val_mul, HeckeRing.GL2.coe_natDiagGL_one hp.pos,
      HeckeRing.GL2.coe_natDiagGL_one (pow_pos hp.pos e),
      coe_mapGL_int_rat_fin_two γ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
      Fin.isValue, Matrix.empty_val', Matrix.cons_val_fin_one]
    exact dvd_mul_of_dvd_right hγ10 _
  · have hdetQ : ((γ 0 0 : ℚ)) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast hdet
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
      HeckeRing.GL2.coe_natDiagGL_one hp.pos, HeckeRing.GL2.coe_natDiagGL_one (pow_pos hp.pos e),
      coe_mapGL_int_rat_fin_two γ]
    simp only [Matrix.det_fin_two_of, Matrix.det_fin_two]
    simp
    push_cast
    linear_combination (p : ℚ) ^ (e + 1) * hdetQ
  · have hndvd : ¬ (p : ℤ) ∣ γ 0 0 := fun h ↦ by
      have h1 : (p : ℤ) ∣ 1 := by
        rw [← hdet]
        exact dvd_sub (dvd_mul_of_dvd_left h _)
          (dvd_mul_of_dvd_right ((Int.natCast_dvd_natCast.mpr hpN).trans hγ10) _)
      exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1)
    have hcop : IsCoprime (γ 0 0) (p : ℤ) :=
      ((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr hndvd).symm
    have := (hcop.pow_right (n := e + 1))
    simpa using Int.isCoprime_iff_gcd_eq_one.mp this

/-- **Miyake, Lemma 4.5.7 (1)** for `p ∣ N`: `T(1, p) T(1, p^e) = T(1, p^{e+1})` in `ℛ(N)`. -/
@[kb "miyake1989" "Lemma 4.5.7 (1), p. 140 (p dividing N)"]
theorem heckeTPair_one_prime_mul_of_dvd {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (e : ℕ) :
    heckeTPair N 1 p * heckeTPair N 1 (p ^ e) = heckeTPair N 1 (p ^ (e + 1)) := by
  classical
  have hp0 := hp.pos
  have hpe : 0 < p ^ e := pow_pos hp0 e
  have hpe1 : 0 < p ^ (e + 1) := pow_pos hp0 _
  have hc1 : Nat.Coprime (![1, p] 0) N := by simp
  have hc2 : Nat.Coprime (![1, p ^ e] 0) N := by simp
  have hc3 : Nat.Coprime (![1, p ^ (e + 1)] 0) N := by simp
  have hpos1 : ∀ i, 0 < (![1, p] : Fin 2 → ℕ) i := fun i ↦ by fin_cases i <;> simp [hp0]
  have hpos2 : ∀ i, 0 < (![1, p ^ e] : Fin 2 → ℕ) i := fun i ↦ by fin_cases i <;> simp [hpe]
  have hpos3 : ∀ i, 0 < (![1, p ^ (e + 1)] : Fin 2 → ℕ) i := fun i ↦ by
    fin_cases i <;> simp [hpe1]
  unfold heckeTPair
  rw [HeckeRing.GL2.diagElemGamma0_of_pos_of_coprime N hpos1 hc1,
    HeckeRing.GL2.diagElemGamma0_of_pos_of_coprime N hpos2 hc2,
    HeckeRing.GL2.diagElemGamma0_of_pos_of_coprime N hpos3 hc3]
  have hdeg1 : (HeckeRing.GL2.diagCosetGamma0 N ![1, p] fun _ ↦ hc1).degree = p := by
    simpa using degree_one_prime_pow_of_dvd N hp hpN 1
  have hdeg2 : (HeckeRing.GL2.diagCosetGamma0 N ![1, p ^ e] fun _ ↦ hc2).degree = p ^ e :=
    degree_one_prime_pow_of_dvd N hp hpN e
  have hdeg3 : (HeckeRing.GL2.diagCosetGamma0 N ![1, p ^ (e + 1)] fun _ ↦ hc3).degree =
      p ^ (e + 1) := degree_one_prime_pow_of_dvd N hp hpN (e + 1)
  have hmap : ∀ q, HeckeCoset.mulMap ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ))
      (HeckeRing.GL2.diagCosetGamma0 N ![1, p] fun _ ↦ hc1).rep
      (HeckeRing.GL2.diagCosetGamma0 N ![1, p ^ e] fun _ ↦ hc2).rep q =
      HeckeRing.GL2.diagCosetGamma0 N ![1, p ^ (e + 1)] fun _ ↦ hc3 := by
    intro q
    obtain ⟨L₁, hL₁, R₁, hR₁, hα⟩ :=
      HeckeRing.GL2.exists_rep_diagCosetGamma0_eq_mul_natDiagGL_mul N ![1, p] fun _ ↦ hc1
    obtain ⟨L₂, hL₂, R₂, hR₂, hβ⟩ :=
      HeckeRing.GL2.exists_rep_diagCosetGamma0_eq_mul_natDiagGL_mul N ![1, p ^ e] fun _ ↦ hc2
    have hσ := q.1.out.2
    have hτ := q.2.out.2
    obtain ⟨γ, hγ, hγeq⟩ := Subgroup.mem_map.mp
      (((Gamma0 N).map (mapGL ℚ)).mul_mem (((Gamma0 N).map (mapGL ℚ)).mul_mem hR₁ hτ) hL₂)
    obtain ⟨l', hl', r', hr', hk⟩ := DoubleCoset.mem_doubleCoset.mp (key_mem N hp hpN e hγ)
    rw [HeckeRing.GL2.diagCosetGamma0_def N ![1, p ^ (e + 1)] fun _ ↦ hc3]
    refine HeckeCoset.mulMap_eq_of_eq_mul_mul (l := (q.1.out : GL (Fin 2) ℚ) * L₁ * l')
      (r := r' * R₂) (((Gamma0 N).map (mapGL ℚ)).mul_mem
        (((Gamma0 N).map (mapGL ℚ)).mul_mem hσ hL₁) hl')
      (((Gamma0 N).map (mapGL ℚ)).mul_mem hr' hR₂) ?_
    refine (congrArg₂ (fun a b : GL (Fin 2) ℚ ↦ (q.1.out : GL (Fin 2) ℚ) * a *
      ((q.2.out : GL (Fin 2) ℚ) * b)) hα hβ).trans ?_
    calc (q.1.out : GL (Fin 2) ℚ) * (L₁ * natDiagGL 2 ![1, p] * R₁) *
          ((q.2.out : GL (Fin 2) ℚ) * (L₂ * natDiagGL 2 ![1, p ^ e] * R₂))
        = (q.1.out : GL (Fin 2) ℚ) * L₁ * (natDiagGL 2 ![1, p] * (R₁ * q.2.out * L₂) *
            natDiagGL 2 ![1, p ^ e]) * R₂ := by group
      _ = _ := by
        rw [← hγeq, hk]
        group
  have hzero : ∀ A : HeckeCoset (HeckeRing.GL2.Delta0 N) ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)), (HeckeRing.GL2.diagCosetGamma0 N ![1, p ^ (e + 1)] fun _ ↦ hc3) ≠ A →
      DoubleCoset.multiplicity ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
        ((Gamma0 N).map (mapGL ℚ))
        ((HeckeRing.GL2.diagCosetGamma0 N ![1, p] fun _ ↦ hc1).rep : GL (Fin 2) ℚ)
        ((HeckeRing.GL2.diagCosetGamma0 N ![1, p ^ e] fun _ ↦ hc2).rep : GL (Fin 2) ℚ)
        (A.rep : GL (Fin 2) ℚ) = 0 := by
    intro A hA
    by_contra h0
    refine hA ?_
    have hmem := (HeckeCoset.mem_image_mulMap_iff _ _ A).mpr h0
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hmem
    obtain ⟨q, hq⟩ := hmem
    rw [← hq, hmap q]
  generalize HeckeRing.GL2.diagCosetGamma0 N ![1, p] (fun _ ↦ hc1) = D₁ at *
  generalize HeckeRing.GL2.diagCosetGamma0 N ![1, p ^ e] (fun _ ↦ hc2) = D₂ at *
  generalize HeckeRing.GL2.diagCosetGamma0 N ![1, p ^ (e + 1)] (fun _ ↦ hc3) = D₃ at *
  have hmul : HeckeCosetModule.single ℤ D₁ (1 : ℤ) * HeckeCosetModule.single ℤ D₂ (1 : ℤ) =
      HeckeCosetModule.structureConstants ℤ ((Gamma0 N).map (mapGL ℚ))
        ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) D₁.rep D₂.rep := by
    rw [HeckeCosetModule.single_mul_single]
    exact (one_smul ℤ _).trans (one_smul ℤ _)
  have hSC : HeckeCosetModule.structureConstants ℤ ((Gamma0 N).map (mapGL ℚ))
        ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) D₁.rep D₂.rep =
      HeckeCosetModule.single ℤ D₃ (DoubleCoset.multiplicity ((Gamma0 N).map (mapGL ℚ))
        ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) (D₁.rep : GL (Fin 2) ℚ)
        (D₂.rep : GL (Fin 2) ℚ) (D₃.rep : GL (Fin 2) ℚ) : ℤ) := by
    ext A
    rw [HeckeCosetModule.structureConstants_apply, HeckeCosetModule.single_apply]
    split_ifs with h
    · rw [← h]
    · rw [hzero A h, Nat.cast_zero]
  have hd : LeftCosetModule.deg _ ((Gamma0 N).map (mapGL ℚ)) ℤ
      (HeckeCosetModule.single ℤ D₁ (1 : ℤ) * HeckeCosetModule.single ℤ D₂ (1 : ℤ)) =
      (p : ℤ) * (p : ℤ) ^ e := by
    rw [map_mul, LeftCosetModule.deg_single, LeftCosetModule.deg_single, hdeg1, hdeg2]
    simp
  have hd' := hd
  rw [hmul, hSC, LeftCosetModule.deg_single, hdeg3, nsmul_eq_mul] at hd'
  have hpz : (0 : ℤ) < (p : ℤ) ^ (e + 1) := by positivity
  have hm1 : (DoubleCoset.multiplicity ((Gamma0 N).map (mapGL ℚ))
        ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) (D₁.rep : GL (Fin 2) ℚ)
        (D₂.rep : GL (Fin 2) ℚ) (D₃.rep : GL (Fin 2) ℚ) : ℤ) = 1 := by
    have h2 : (p : ℤ) ^ (e + 1) * (DoubleCoset.multiplicity ((Gamma0 N).map (mapGL ℚ))
        ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) (D₁.rep : GL (Fin 2) ℚ)
        (D₂.rep : GL (Fin 2) ℚ) (D₃.rep : GL (Fin 2) ℚ) : ℤ) = (p : ℤ) ^ (e + 1) * 1 := by
      push_cast at hd'
      linear_combination hd'
    exact mul_left_cancel₀ hpz.ne' h2
  rw [hmul, hSC, hm1]

end ModularFormsKB.Miyake.Wave5
