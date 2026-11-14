import ModularFormsKB.Miyake.Wave7.StarHecke
import ModularFormsKB.Miyake.Wave6.HeckeIndependence
import ModularFormsKB.Miyake.Wave6.LevelChange
import ModularFormsKB.Miyake.Wave4.HeckeCoefficients
import TauCeti.NumberTheory.ModularForms.Petersson.Normal
import TauCeti.NumberTheory.ModularForms.Petersson.Eigenbasis

/-!
# Miyake §4.5: Theorem 4.5.4 (2), (3) and Theorem 4.5.10 for `T*(n)`

Miyake, *Modular Forms* (Springer 1989), §4.5, pp. 136–137 and 139.

* Theorem 4.5.4 (2): `T(l, m)` and `T*(m, l)` (resp. `T(n)` and `T*(n)`) are mutually adjoint for
  the Petersson inner product on `𝒮_k(N, χ)`. Proved here when `(l m, N) = 1` (resp.
  `(n, N) = 1`), from Tau Ceti's adjoint formula for the prime operators `T(p)`, `p ∤ N`
  (`isAdjointPair_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0`), the double-coset relations of
  waves 4–5, and Theorem 4.5.4 (1). Miyake's statement also covers `(m, N) ≠ 1`; that case is not
  proved here (loose end).
* Theorem 4.5.4 (3): `𝒮_k(N, χ)` has a basis of common eigenfunctions of all `T(n)` and
  `T(l, m)` with `(n, N) = 1`, `(l m, N) = 1`; from Tau Ceti's Petersson-orthonormal eigenbasis
  (`exists_peterssonOrthonormalBasis_eigenformAwayFromLevel`).
* Theorem 4.5.10 for `T*(n)` when `(n, M) = 1`.

The Petersson product is Tau Ceti's `CuspForm.peterssonInnerCosets` on `S_k(Γ₁(N))`, which is a
positive multiple of Miyake's; adjointness does not see the normalisation.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
  HeckeRing.GL2 HeckeRing.GLn
open scoped MatrixGroups ModularForm

noncomputable section

namespace ModularFormsKB.Miyake.Wave7

open ModularFormsKB.Miyake.Wave4

variable {N : ℕ} [NeZero N]

/-- The Petersson product of two elements of `𝒮_k(N, χ)` (Tau Ceti's, on `S_k(Γ₁(N))`). -/
abbrev pet {k : ℤ} {χ : DirichletCharacter ℂ N} (f g : cuspSpace k χ) : ℂ :=
  CuspForm.peterssonInnerCosets (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)

section Helpers

variable {k : ℤ} {χ : DirichletCharacter ℂ N}

private theorem pet_add_left' (f₁ f₂ g : cuspSpace k χ) : pet (f₁ + f₂) g = pet f₁ g + pet f₂ g :=
  CuspForm.peterssonInnerCosets_add_left _ _ _

private theorem pet_add_right' (f g₁ g₂ : cuspSpace k χ) : pet f (g₁ + g₂) = pet f g₁ + pet f g₂ :=
  CuspForm.peterssonInnerCosets_add_right _ _ _

private theorem pet_smul_left' (c : ℂ) (f g : cuspSpace k χ) :
    pet (c • f) g = starRingEnd ℂ c * pet f g :=
  CuspForm.peterssonInnerCosets_smul_left _ _ _

private theorem pet_smul_right' (c : ℂ) (f g : cuspSpace k χ) :
    pet f (c • g) = c * pet f g :=
  CuspForm.peterssonInnerCosets_smul_right _ _ _

private theorem pet_conj_symm' (f g : cuspSpace k χ) :
    starRingEnd ℂ (pet g f) = pet f g :=
  CuspForm.peterssonInnerCosets_conj_symm _ _

/-- `A` is adjoint to `conj (χ n) • A` for the Petersson product. -/
private def Adj (A : Module.End ℂ (cuspSpace k χ)) (n : ℕ) : Prop :=
  ∀ f g, pet (A f) g = pet f (starRingEnd ℂ (χ (n : ZMod N)) • A g)

private theorem Adj.add {A B : Module.End ℂ (cuspSpace k χ)} {n : ℕ} (hA : Adj A n)
    (hB : Adj B n) : Adj (A + B) n := by
  intro f g
  simp only [LinearMap.add_apply, pet_add_left', hA f g, hB f g, smul_add, pet_add_right']

private theorem Adj.zero (n : ℕ) : Adj (0 : Module.End ℂ (cuspSpace k χ)) n := by
  intro f g
  have h0 : ∀ g : cuspSpace k χ, pet 0 g = 0 := fun g => by
    have := pet_smul_left' (0 : ℂ) 0 g
    simpa using this
  have h1 : ∀ f : cuspSpace k χ, pet f 0 = 0 := fun f => by
    have := pet_smul_right' (0 : ℂ) f 0
    simpa using this
  simp [h0, h1]

private theorem Adj.zsmul {A : Module.End ℂ (cuspSpace k χ)} {n : ℕ} (hA : Adj A n) (c : ℤ) :
    Adj (c • A) n := by
  intro f g
  rw [← Int.cast_smul_eq_zsmul ℂ c A]
  simp only [LinearMap.smul_apply, pet_smul_left', pet_smul_right', hA f g, map_intCast]
  ring

private theorem Adj.mul {A B : Module.End ℂ (cuspSpace k χ)} {a b : ℕ} (hA : Adj A a)
    (hB : Adj B b) (hAB : A * B = B * A) : Adj (A * B) (a * b) := by
  intro f g
  have hc : A (B g) = B (A g) := LinearMap.congr_fun hAB g
  have e : (A * B) f = A (B f) := rfl
  have e' : (A * B) g = A (B g) := rfl
  rw [e, e', hA (B f) g, hB f (starRingEnd ℂ (χ (a : ZMod N)) • A g), map_smul, ← hc,
    Nat.cast_mul, map_mul, map_mul, mul_smul, smul_comm]

omit [NeZero N] in
private theorem mul_conj_unit' (χ : DirichletCharacter ℂ N) {x : ZMod N} (hx : IsUnit x) :
    χ x * starRingEnd ℂ (χ x) = 1 := by
  have h1 : ‖χ x‖ = 1 := by
    have := DirichletCharacter.unit_norm_eq_one χ hx.unit
    simpa using this
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp

private theorem Adj.scalar (c : ℕ) (hc : 0 < c) (hcN : c.Coprime N) :
    Adj (heckeTT k χ c c) (c * c) := by
  rw [heckeTT_self k χ hc]
  intro f g
  have hu : IsUnit (c : ZMod N) := (ZMod.isUnit_iff_coprime c N).mpr hcN
  have h1 := mul_conj_unit' χ hu
  have hr : starRingEnd ℂ ((c : ℂ) ^ (k - 2)) = (c : ℂ) ^ (k - 2) := by
    rw [map_zpow₀, Complex.conj_natCast]
  simp only [LinearMap.smul_apply, one_apply_eq_self, pet_smul_left', pet_smul_right',
    Nat.cast_mul, map_mul, hr]
  have : χ (c : ZMod N) * starRingEnd ℂ (χ (c : ZMod N)) = 1 := h1
  linear_combination (-(starRingEnd ℂ (χ (c : ZMod N)) * (c : ℂ) ^ (k - 2) * pet f g)) * this

private theorem heckeT_prime_eq (k : ℤ) (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) :
    HeckeRing.GL2.heckeRingHomCuspCharSpace k χ.toUnitHom
        (HeckeRing.GL2.heckeTGeneratorGamma0 N p) = heckeTT k χ 1 p := by
  have h := heckeT_eq_sum_heckeTT k χ hp.ne_zero
  rw [← HeckeRing.GL2.heckeTCompositeGamma0_prime N hp] at *
  rw [show HeckeRing.GL2.heckeRingHomCuspCharSpace k χ.toUnitHom
    (HeckeRing.GL2.heckeTCompositeGamma0 N p) = heckeT k χ p from rfl, h]
  have : (p.divisors.filter fun l => l ∣ p / l) = {1} := by
    rw [hp.divisors]
    ext l
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, h2⟩
      · rfl
      · exfalso; simp [Nat.div_self hp.pos] at h2; exact hp.one_lt.ne' h2
    · rintro rfl; simp
  rw [this, Finset.sum_singleton, Nat.div_one]

/-- Closure principle for double coset elements `T(l, m)`, graded by a natural number. -/
private theorem general_hecke {P : HeckeRingGamma0 N → ℕ → Prop}
    (hadd : ∀ x y n, P x n → P y n → P (x + y) n)
    (hzsmul : ∀ (c : ℤ) x n, P x n → P (c • x) n)
    (hmul : ∀ x y a b, P x a → P y b → P (x * y) (a * b))
    (hprime : ∀ p : ℕ, p.Prime → ¬ p ∣ N → P (heckeTPair N 1 p) p)
    (hscalar : ∀ c : ℕ, 0 < c → c.Coprime N → P (heckeTPair N c c) (c * c)) :
    ∀ l m : ℕ, 0 < l → 0 < m → l ∣ m → (l * m).Coprime N → P (heckeTPair N l m) (l * m) := by
  have hsub : ∀ x y n, P x n → P y n → P (x - y) n := fun x y n hx hy => by
    rw [sub_eq_add_neg, ← neg_one_zsmul]
    exact hadd _ _ _ hx (hzsmul _ _ _ hy)
  have R := Wave5.doubleCosetRelations N
  -- prime powers
  have hpow : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ e : ℕ, 1 ≤ e →
      P (heckeTPair N 1 (p ^ e)) (p ^ e) := by
    intro p hp hpN e
    induction e using Nat.strong_induction_on with
    | _ e ih =>
      intro he
      have hsc : P (heckeTPair N p p) (p * p) :=
        hscalar p hp.pos ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN)
      match e, he with
      | 1, _ => simpa using hprime p hp hpN
      | 2, _ =>
        have h := R.one_prime_mul hp hpN (e := 1) le_rfl
        have h2 : heckeTPair N 1 (p ^ (1 + 1)) =
            heckeTPair N 1 p * heckeTPair N 1 (p ^ 1) -
              ((if 1 = 1 then p + 1 else p : ℕ) : ℤ) • heckeTPair N p (p ^ 1) := by
          rw [h]; abel
        rw [h2]
        have e1 : P (heckeTPair N 1 p * heckeTPair N 1 (p ^ 1)) (p * p ^ 1) :=
          hmul _ _ _ _ (hprime p hp hpN) (by simpa using hprime p hp hpN)
        have e2 : P (heckeTPair N p (p ^ 1)) (p * p) := by simpa using hsc
        have := hsub _ _ (p * p ^ 1) e1 (hzsmul ((if 1 = 1 then p + 1 else p : ℕ) : ℤ)
          (heckeTPair N p (p ^ 1)) (p * p ^ 1) (by simpa [pow_one] using e2))
        simpa [pow_succ] using this
      | e + 3, _ =>
        have h := R.one_prime_mul hp hpN (e := e + 2) (by omega)
        have h2 : heckeTPair N 1 (p ^ (e + 2 + 1)) =
            heckeTPair N 1 p * heckeTPair N 1 (p ^ (e + 2)) -
              ((if e + 2 = 1 then p + 1 else p : ℕ) : ℤ) • heckeTPair N p (p ^ (e + 2)) := by
          rw [h]; abel
        rw [h2]
        have ih1 := ih (e + 2) (by omega) (by omega)
        have ih2 := ih (e + 1) (by omega) (by omega)
        have e1 : P (heckeTPair N 1 p * heckeTPair N 1 (p ^ (e + 2))) (p * p ^ (e + 2)) :=
          hmul _ _ _ _ (hprime p hp hpN) ih1
        have e3 : heckeTPair N p (p ^ (e + 2)) =
            heckeTPair N p p * heckeTPair N 1 (p ^ (e + 1)) := by
          rw [Wave6.heckeTPair_scalar_mul, mul_one, ← pow_succ']
        have e2 : P (heckeTPair N p (p ^ (e + 2))) (p * p * p ^ (e + 1)) := by
          rw [e3]; exact hmul _ _ _ _ hsc ih2
        have := hsub _ _ (p * p ^ (e + 2)) e1 (hzsmul ((if e + 2 = 1 then p + 1 else p : ℕ) : ℤ)
          (heckeTPair N p (p ^ (e + 2))) (p * p ^ (e + 2)) (by
          have hh : p * p * p ^ (e + 1) = p * p ^ (e + 2) := by ring
          rwa [hh] at e2))
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
  -- T(1, n)
  have hone : ∀ n : ℕ, 0 < n → n.Coprime N → P (heckeTPair N 1 n) n := by
    intro n
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => intro h; omega
    | one => intro _ h; simpa using hscalar 1 one_pos (Nat.coprime_one_left N)
    | prime_pow p e hp he =>
      intro _ hc
      have hpN : ¬ p ∣ N := fun hd => by
        have := Nat.Coprime.coprime_dvd_left (dvd_pow_self p he.ne') hc
        exact hp.coprime_iff_not_dvd.mp this hd
      exact hpow p hp hpN e he
    | coprime a b ha hb hab iha ihb =>
      intro _ hc
      have hcA : a.Coprime N := Nat.Coprime.coprime_dvd_left (dvd_mul_right a b) hc
      have hcB : b.Coprime N := Nat.Coprime.coprime_dvd_left (dvd_mul_left b a) hc
      have := R.mul_of_coprime (l := 1) (m := a) (l' := 1) (m' := b) (one_dvd _) (one_dvd _)
        (by simpa using hab)
      rw [one_mul] at this
      rw [← this]
      exact hmul _ _ _ _ (iha (by omega) hcA) (ihb (by omega) hcB)
  intro l m hl hm hlm hc
  obtain ⟨b, rfl⟩ := hlm
  have hb : 0 < b := Nat.pos_of_mul_pos_left hm
  have hcl : l.Coprime N := (Nat.coprime_mul_iff_left.mp hc).1
  have hcb : b.Coprime N := (Nat.Coprime.coprime_dvd_left ⟨l * l, by ring⟩ hc)
  have e := Wave6.heckeTPair_scalar_mul (N := N) l 1 b
  rw [mul_one] at e
  rw [← e, show l * (l * b) = l * l * b by ring]
  exact hmul _ _ _ _ (hscalar l hl hcl) (hone b hb hcb)

private theorem Adj.prime {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) :
    Adj (heckeTT k χ 1 p) p := by
  have hcop : p.Coprime N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  rw [← heckeT_prime_eq k χ hp]
  intro f g
  have hadj := HeckeRing.GL2.isAdjointPair_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0
    (χ := χ.toUnitHom) k hp hcop f g
  simp only [LinearMap.flip_apply,
    TauCeti.CuspForm.peterssonInnerCosetsCharSpaceₛₗ_apply_apply] at hadj
  have hu : IsUnit (p : ZMod N) := (ZMod.isUnit_iff_coprime p N).mpr hcop
  have h1 := mul_conj_unit' χ hu
  have h2 : ((χ.toUnitHom (ZMod.unitOfCoprime p hcop) : ℂˣ) : ℂ) = χ (p : ZMod N) := by
    rw [MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime]
  rw [h2] at hadj
  have h3 : (χ (p : ZMod N))⁻¹ = starRingEnd ℂ (χ (p : ZMod N)) :=
    inv_eq_of_mul_eq_one_right h1
  rw [h3] at hadj
  have := congrArg (starRingEnd ℂ) hadj
  rw [CuspForm.peterssonInnerCosets_conj_symm, CuspForm.peterssonInnerCosets_conj_symm] at this
  exact this

private theorem Adj.heckeTT {l m : ℕ} (hl : 0 < l) (hm : 0 < m) (hlm : l ∣ m)
    (hlmN : (l * m).Coprime N) : Adj (heckeTT k χ l m) (l * m) := by
  let ρ := HeckeRing.GL2.heckeRingHomCuspCharSpace k χ.toUnitHom
  have hadd : ∀ (x y : HeckeRingGamma0 N) (n : ℕ), Adj (ρ x) n → Adj (ρ y) n →
      Adj (ρ (x + y)) n := fun x y n hx hy => by
    rw [map_add]; exact hx.add hy
  have hzsmul : ∀ (c : ℤ) (x : HeckeRingGamma0 N) (n : ℕ), Adj (ρ x) n → Adj (ρ (c • x)) n :=
    fun c x n hx => by rw [map_zsmul]; exact hx.zsmul c
  have hmul : ∀ (x y : HeckeRingGamma0 N) (a b : ℕ), Adj (ρ x) a → Adj (ρ y) b →
      Adj (ρ (x * y)) (a * b) := fun x y a b hx hy => by
    rw [map_mul]
    refine hx.mul hy ?_
    rw [← map_mul, ← map_mul, Wave4.heckeRing_mul_comm]
  exact general_hecke (N := N) (P := fun x n => Adj (ρ x) n) hadd hzsmul hmul
    (fun p hp hpN => Adj.prime hp hpN) (fun c hc hcN => Adj.scalar c hc hcN) l m hl hm hlm hlmN

end Helpers

/-- **Miyake, Theorem 4.5.4 (2)** for `T(l, m)`, `(l m, N) = 1`: `T(l, m)` and `T*(m, l)` are
mutually adjoint for the Petersson inner product on `𝒮_k(N, χ)`. -/
@[kb "miyake1989" "Theorem 4.5.4 (2), p. 136 ((l m, N) = 1)"]
theorem pet_heckeTT_left (k : ℤ) (χ : DirichletCharacter ℂ N) {l m : ℕ} (hl : 0 < l)
    (hlm : l ∣ m) (hm : 0 < m) (hlmN : (l * m).Coprime N) (f g : cuspSpace k χ) :
    pet (heckeTT k χ l m f) g = pet f (heckeTStar k χ m l g) := by
  rw [Adj.heckeTT hl hm hlm hlmN f g, heckeTStar_eq_smul_heckeTT k χ hl hm hlmN, Nat.cast_mul]
  rfl

/-- **Miyake, Theorem 4.5.4 (2)** for `T(l, m)`, the other half: `⟨f | T*(m, l), g⟩ = ⟨f, g | T(l, m)⟩`. -/
@[kb "miyake1989" "Theorem 4.5.4 (2), p. 136 ((l m, N) = 1)"]
theorem pet_heckeTStar_left (k : ℤ) (χ : DirichletCharacter ℂ N) {l m : ℕ} (hl : 0 < l)
    (hlm : l ∣ m) (hm : 0 < m) (hlmN : (l * m).Coprime N) (f g : cuspSpace k χ) :
    pet (heckeTStar k χ m l f) g = pet f (heckeTT k χ l m g) := by
  rw [← pet_conj_symm' (heckeTStar k χ m l f) g, ← pet_heckeTT_left k χ hl hlm hm hlmN g f,
    pet_conj_symm']

/-- **Miyake, Theorem 4.5.4 (2)** for `T(n)`, `(n, N) = 1`: `T(n)` and `T*(n)` are mutually adjoint
for the Petersson inner product on `𝒮_k(N, χ)`. -/
@[kb "miyake1989" "Theorem 4.5.4 (2), p. 136 ((n, N) = 1)"]
theorem pet_heckeT_left (k : ℤ) (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : 0 < n)
    (hnN : n.Coprime N) (f g : cuspSpace k χ) :
    pet (heckeT k χ n f) g = pet f (heckeTStarN k χ n g) := by
  have hA : Adj (heckeT k χ n) n := by
    rw [heckeT_eq_sum_heckeTT k χ hn.ne']
    refine Finset.sum_induction _ (fun A => Adj A n) (fun A B hA hB => hA.add hB) (Adj.zero n) ?_
    intro l hl
    obtain ⟨hmem, -⟩ := Finset.mem_filter.mp hl
    have hld : l ∣ n := Nat.dvd_of_mem_divisors hmem
    have hlpos : 0 < l := Nat.pos_of_dvd_of_pos hld hn
    have hmul : l * (n / l) = n := Nat.mul_div_cancel' hld
    have hm : 0 < n / l := Nat.div_pos (Nat.le_of_dvd hn hld) hlpos
    have hl2 : l ∣ n / l := (Finset.mem_filter.mp hl).2
    have := Adj.heckeTT (k := k) (χ := χ) hlpos hm hl2 (by rwa [hmul])
    rwa [hmul] at this
  rw [hA f g, heckeTStarN_eq_smul_heckeT k χ hn hnN]
  rfl

/-- **Miyake, Theorem 4.5.4 (2)** for `T(n)`, the other half. -/
@[kb "miyake1989" "Theorem 4.5.4 (2), p. 136 ((n, N) = 1)"]
theorem pet_heckeTStarN_left (k : ℤ) (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : 0 < n)
    (hnN : n.Coprime N) (f g : cuspSpace k χ) :
    pet (heckeTStarN k χ n f) g = pet f (heckeT k χ n g) := by
  rw [← pet_conj_symm' (heckeTStarN k χ n f) g, ← pet_heckeT_left k χ hn hnN g f,
    pet_conj_symm']

/-- **Miyake, Theorem 4.5.4 (3)**: `𝒮_k(N, χ)` has a basis consisting of common eigenfunctions of
all `T(n)` and `T(l, m)` with `(n, N) = 1`, `l ∣ m`, `(l m, N) = 1`. -/
@[kb "miyake1989" "Theorem 4.5.4 (3), p. 136"]
theorem exists_basis_common_eigen (k : ℤ) (χ : DirichletCharacter ℂ N) :
    ∃ (I : Type) (b : Module.Basis I ℂ (cuspSpace k χ)),
      ∀ i, (∀ n : ℕ, 0 < n → n.Coprime N → ∃ c : ℂ, heckeT k χ n (b i) = c • b i) ∧
        ∀ l m : ℕ, 0 < l → l ∣ m → (l * m).Coprime N →
          ∃ c : ℂ, heckeTT k χ l m (b i) = c • b i := by
  obtain ⟨I, b, -, -, -, hb⟩ :=
    HeckeRing.GL2.exists_peterssonOrthonormalBasis_eigenformAwayFromLevel k χ.toUnitHom
  refine ⟨I, b, fun i => ?_⟩
  let ρ := HeckeRing.GL2.heckeRingHomCuspCharSpace k χ.toUnitHom
  have hE : ∀ n : ℕ, 0 < n → n.Coprime N → ∃ c : ℂ,
      ρ (HeckeRing.GL2.heckeTCompositeGamma0 N n) (b i) = c • b i := by
    obtain ⟨f, hχ, hx⟩ := hb i
    obtain ⟨F, χ', hF, a, haF, _⟩ := f
    obtain rfl : χ' = χ.toUnitHom := hχ
    have hbi : (⟨F, hF⟩ : cuspSpace k χ) = b i := Subtype.ext hx
    intro n hn hnN
    exact ⟨a ⟨n, hn⟩ hnN, by rw [← hbi]; exact haF ⟨n, hn⟩ hnN⟩
  refine ⟨fun n hn hnN => hE n hn hnN, ?_⟩
  intro l m hl hlm hlmN
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : HeckeRing.GL2.diagElemGamma0 N ![l, 0] = 0 :=
      HeckeRing.GL2.diagElemGamma0_of_not_pos N (fun h => by simpa using h 1)
    refine ⟨0, ?_⟩
    rw [zero_smul]
    change ρ (HeckeRing.GL2.diagElemGamma0 N ![l, 0]) (b i) = 0
    rw [h0, map_zero, LinearMap.zero_apply]
  have hadd : ∀ (x y : HeckeRingGamma0 N) (n : ℕ), (∃ c : ℂ, ρ x (b i) = c • b i) →
      (∃ c : ℂ, ρ y (b i) = c • b i) → ∃ c : ℂ, ρ (x + y) (b i) = c • b i := by
    rintro x y n ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by rw [map_add, LinearMap.add_apply, hc, hd, add_smul]⟩
  have hzsmul : ∀ (c : ℤ) (x : HeckeRingGamma0 N) (n : ℕ), (∃ c : ℂ, ρ x (b i) = c • b i) →
      ∃ c' : ℂ, ρ (c • x) (b i) = c' • b i := by
    rintro c x n ⟨d, hd⟩
    exact ⟨(c : ℂ) * d, by
      rw [map_zsmul, LinearMap.smul_apply, hd, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]⟩
  have hmul : ∀ (x y : HeckeRingGamma0 N) (a b' : ℕ), (∃ c : ℂ, ρ x (b i) = c • b i) →
      (∃ c : ℂ, ρ y (b i) = c • b i) → ∃ c : ℂ, ρ (x * y) (b i) = c • b i := by
    rintro x y a b' ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨d * c, by rw [map_mul, Module.End.mul_eq_comp, LinearMap.comp_apply, hd, map_smul, hc, smul_smul]⟩
  have hprime : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ c : ℂ, ρ (heckeTPair N 1 p) (b i) = c • b i := by
    intro p hp hpN
    obtain ⟨c, hc⟩ := hE p hp.pos ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN)
    refine ⟨c, ?_⟩
    have e : ρ (heckeTPair N 1 p) = ρ (HeckeRing.GL2.heckeTCompositeGamma0 N p) := by
      rw [HeckeRing.GL2.heckeTCompositeGamma0_prime N hp]
      exact (heckeT_prime_eq k χ hp).symm
    rw [e, hc]
  have hscalar : ∀ c : ℕ, 0 < c → c.Coprime N →
      ∃ c' : ℂ, ρ (heckeTPair N c c) (b i) = c' • b i := by
    intro c hc _
    exact ⟨χ c * (c : ℂ) ^ (k - 2), by
      rw [show ρ (heckeTPair N c c) = heckeTT k χ c c from rfl, heckeTT_self k χ hc]; rfl⟩
  exact general_hecke (N := N) (P := fun x _ => ∃ c : ℂ, ρ x (b i) = c • b i) hadd hzsmul hmul
    hprime hscalar l m hl hm hlm hlmN

/-- **Miyake, Theorem 4.5.10** for `T*(n)` with `(n, M) = 1`: for `N ∣ M`, the operator `T*(n)` of
level `M` restricted to `𝒮_k(N, χ) ⊂ 𝒮_k(M, χ)` is `T*(n)` of level `N`. -/
@[kb "miyake1989" "Theorem 4.5.10, p. 139 (T*(n), (n, M) = 1)"]
theorem heckeTStarN_embed {M : ℕ} [NeZero M] (k : ℤ) (χ : DirichletCharacter ℂ N) (h : N ∣ M)
    {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (f : cuspSpace k χ) :
    heckeTStarN k (DirichletCharacter.changeLevel h χ) n (Wave6.embed k χ h f) =
      Wave6.embed k χ h (heckeTStarN k χ n f) := by
  have hnN : n.Coprime N := Nat.Coprime.coprime_dvd_right h hnM
  rw [heckeTStarN_eq_smul_heckeT k _ hn hnM, heckeTStarN_eq_smul_heckeT k χ hn hnN,
    LinearMap.smul_apply, LinearMap.smul_apply,
    Wave6.heckeT_embed k χ h hn.ne' (Or.inr hnM), map_smul,
    Wave6.changeLevel_apply_of_dvd h χ (Or.inr hnM) (dvd_refl n)]

end ModularFormsKB.Miyake.Wave7
