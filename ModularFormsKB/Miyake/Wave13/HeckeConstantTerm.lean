import ModularFormsKB.Miyake.Wave4.HeckeCoefficients
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime.Power

/-!
# Miyake Lemma 4.5.14 at the constant term

Miyake, *Modular Forms* (Springer 1989), Lemma 4.5.14 (p. 147): if `f(z) = Σ c(n) qⁿ` lies in
`𝒢_k(N, χ)` and `(f ∣ T(m))(z) = Σ b(n) qⁿ` (`m ≥ 1`), then
`b(n) = Σ_{0 < d ∣ (m, n)} χ(d) d^{k-1} c(mn/d²)` for every `n ≥ 0`.

Wave 4 proved the lemma on cusp forms and, on `𝒢_k(N, χ)`, at the indices `n ≥ 1`
(`Wave4.coeffMod_heckeTMod`, through Tau Ceti's coefficient-one argument, which says nothing about
the constant term). This file proves the remaining index `n = 0`, where `(m, 0) = m` and the
formula reads `b(0) = Σ_{d ∣ m} χ(d) d^{k-1} c(0)` (`coeffMod_heckeTMod_zero`), and assembles the
lemma for every `n` (`coeffMod_heckeTMod_all`). This settles LE-MF-0182.

**Proof.** At a prime `p ∤ N`, Tau Ceti's formula for `Tₚ` at every index
(`qExpansion_coeff_prime_pow_succ_mul_heckeRingHomCharSpace_heckeTGeneratorGamma0`, read at the
index `0`) gives `b(0) = (1 + χ(p) p^{k-1}) c(0)`; the recurrence
`T(p^{r+2}) = T(p) T(p^{r+1}) - χ(p) p^{k-1} T(p^r)` then gives
`b(0) = Σ_{i ≤ r} (χ(p) p^{k-1})^i c(0)` for `T(p^r)`. At a prime `p ∣ N`, `T(p^r)` shifts the
coefficients by `p^r` (`qExpansion_coeff_heckeRingHomCharSpace_heckeTGeneratorRecGamma0_of_dvd_level`),
so `b(0) = c(0)`, and `χ(p) = 0`. Finally `T(mn) = T(m) T(n)` for coprime `m`, `n`
(Lemma 4.5.8 (2)) and the divisor sum `Σ_{d ∣ m} χ(d) d^{k-1}` is multiplicative.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave13

open Wave4

variable {N : ℕ}

/-- The divisor sum `σ_{k-1, χ}(m) = Σ_{d ∣ m} χ(d) d^{k-1}`, the eigenvalue of `T(m)` on the
constant term. -/
def divisorSumChar (k : ℤ) (χ : DirichletCharacter ℂ N) (m : ℕ) : ℂ :=
  ∑ d ∈ m.divisors, χ d * (d : ℂ) ^ (k - 1)

/-- The arithmetic function `d ↦ χ(d) d^{k-1}` (zero at `0`). -/
def charPowArith (k : ℤ) (χ : DirichletCharacter ℂ N) : ArithmeticFunction ℂ :=
  ⟨fun d ↦ if d = 0 then 0 else χ d * (d : ℂ) ^ (k - 1), by simp⟩

lemma charPowArith_apply {k : ℤ} {χ : DirichletCharacter ℂ N} {d : ℕ} (hd : d ≠ 0) :
    charPowArith k χ d = χ d * (d : ℂ) ^ (k - 1) := by
  simp [charPowArith, hd]

lemma isMultiplicative_charPowArith (k : ℤ) (χ : DirichletCharacter ℂ N) :
    (charPowArith k χ).IsMultiplicative := by
  refine ⟨by simp [charPowArith], fun {m n} hmn ↦ ?_⟩
  by_cases hm : m = 0
  · subst hm; simp [charPowArith]
  by_cases hn : n = 0
  · subst hn; simp [charPowArith]
  rw [charPowArith_apply (mul_ne_zero hm hn), charPowArith_apply hm, charPowArith_apply hn]
  push_cast
  rw [map_mul, mul_zpow]
  ring

lemma divisorSumChar_eq_mul_zeta (k : ℤ) (χ : DirichletCharacter ℂ N) (m : ℕ) :
    divisorSumChar k χ m = (charPowArith k χ * ArithmeticFunction.zeta) m := by
  rw [ArithmeticFunction.coe_mul_zeta_apply, divisorSumChar]
  exact Finset.sum_congr rfl fun d hd ↦ (charPowArith_apply (Nat.pos_of_mem_divisors hd).ne').symm

/-- The divisor sum is multiplicative. -/
lemma divisorSumChar_mul {k : ℤ} {χ : DirichletCharacter ℂ N} {m n : ℕ} (hmn : m.Coprime n) :
    divisorSumChar k χ (m * n) = divisorSumChar k χ m * divisorSumChar k χ n := by
  simp only [divisorSumChar_eq_mul_zeta]
  exact ((isMultiplicative_charPowArith k χ).mul
    ArithmeticFunction.isMultiplicative_zeta.natCast).map_mul_of_coprime hmn

lemma divisorSumChar_one (k : ℤ) (χ : DirichletCharacter ℂ N) : divisorSumChar k χ 1 = 1 := by
  simp [divisorSumChar]

/-- At a prime power, `σ_{k-1, χ}(p^r) = Σ_{i ≤ r} (χ(p) p^{k-1})^i`. -/
lemma divisorSumChar_prime_pow {k : ℤ} {χ : DirichletCharacter ℂ N} {p : ℕ} (hp : p.Prime)
    (r : ℕ) :
    divisorSumChar k χ (p ^ r) = ∑ i ∈ Finset.range (r + 1), (χ p * (p : ℂ) ^ (k - 1)) ^ i := by
  rw [divisorSumChar, Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  push_cast
  rw [map_pow, mul_pow]
  congr 1
  rw [← zpow_natCast (p : ℂ) i, ← zpow_mul, ← zpow_natCast ((p : ℂ) ^ (k - 1)) i, ← zpow_mul]
  congr 1
  ring

/-- At a prime power of a prime dividing the level, `σ_{k-1, χ}(p^r) = 1`. -/
lemma divisorSumChar_prime_pow_of_dvd {k : ℤ} {χ : DirichletCharacter ℂ N} {p : ℕ}
    (hp : p.Prime) (hpN : p ∣ N) (r : ℕ) : divisorSumChar k χ (p ^ r) = 1 := by
  have hχ : χ p = 0 := by
    refine MulChar.map_nonunit _ fun hu ↦ ?_
    have hc := (ZMod.isUnit_iff_coprime p N).mp hu
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp hc hpN
  rw [divisorSumChar_prime_pow hp, Finset.sum_range_succ']
  simp [hχ]

/-- Tau Ceti's scalar `χ(unitOfCoprime p)` is `χ(p)`. -/
lemma toUnitHom_unitOfCoprime (χ : DirichletCharacter ℂ N) {p : ℕ} (hpN : p.Coprime N) :
    ((χ.toUnitHom (ZMod.unitOfCoprime p hpN) : ℂˣ) : ℂ) = χ p := by
  rw [MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime]

variable [NeZero N]

/-- The constant term of `T(p^r) F` at a prime `p ∤ N`, for Tau Ceti's recurrence family. -/
lemma coeffMod_heckeTGeneratorRec_zero {k : ℤ} {χ : DirichletCharacter ℂ N} {p : ℕ}
    (hp : p.Prime) (hpN : p.Coprime N) (r : ℕ) (F : modSpace k χ) :
    coeffMod (heckeRingHomCharSpace k χ.toUnitHom (heckeTGeneratorRecGamma0 N p r) F) 0 =
      (∑ i ∈ Finset.range (r + 1), (χ p * (p : ℂ) ^ (k - 1)) ^ i) * coeffMod F 0 := by
  -- the generator: `b(0) = c(0) + χ(p) p^{k-1} c(0)`
  have hgen : ∀ G : modSpace k χ,
      coeffMod (heckeRingHomCharSpace k χ.toUnitHom (heckeTGeneratorGamma0 N p) G) 0 =
        (1 + χ p * (p : ℂ) ^ (k - 1)) * coeffMod G 0 := by
    intro G
    have h := qExpansion_coeff_prime_pow_succ_mul_heckeRingHomCharSpace_heckeTGeneratorGamma0
      (k := k) (χ := χ.toUnitHom) hp hpN G 0 0
    simp only [mul_zero, toUnitHom_unitOfCoprime] at h
    simp only [coeffMod, h]
    ring
  induction r using Nat.twoStepInduction generalizing F with
  | zero =>
    rw [heckeTGeneratorRecGamma0_zero, map_one, one_apply_eq_self]
    simp
  | one =>
    rw [heckeTGeneratorRecGamma0_one, hgen, Finset.sum_range_succ, Finset.sum_range_one]
    simp
  | more r ih1 ih2 =>
    rw [heckeRingHomCharSpace_heckeTGeneratorRecGamma0_succ_succ_apply k χ.toUnitHom hpN F r]
    have hsub : ∀ A B : modSpace k χ, ∀ t : ℂ, coeffMod (A - t • B) 0 =
        coeffMod A 0 - t * coeffMod B 0 := by
      intro A B t
      simp only [coeffMod, Submodule.coe_sub, Submodule.coe_smul]
      rw [← TauCeti.ModularForm.qExpansionLinearMap_apply one_pos
        (TauCeti.one_mem_strictPeriods_Gamma1_map _), map_sub, map_smul,
        TauCeti.ModularForm.qExpansionLinearMap_apply,
        TauCeti.ModularForm.qExpansionLinearMap_apply]
      simp
    rw [hsub, hgen, ih2, ih1, toUnitHom_unitOfCoprime]
    simp only [Finset.sum_range_succ]
    ring

/-- **Miyake, Lemma 4.5.14** at the constant term (LE-MF-0182): for `f ∈ 𝒢_k(N, χ)` and `m ≥ 1`,
the constant term of `f ∣ T(m)` is `b(0) = Σ_{0 < d ∣ m} χ(d) d^{k-1} c(0)`. -/
@[kb "miyake1989" "Lemma 4.5.14, p. 147 (modular forms, n = 0)"]
theorem coeffMod_heckeTMod_zero (k : ℤ) (χ : DirichletCharacter ℂ N) {m : ℕ} (hm : m ≠ 0)
    (f : modSpace k χ) :
    coeffMod (heckeTMod k χ m f) 0 = ∑ d ∈ m.divisors, χ d * (d : ℂ) ^ (k - 1) * coeffMod f 0 := by
  rw [← Finset.sum_mul]
  change _ = divisorSumChar k χ m * _
  induction m using Nat.recOnPosPrimePosCoprime generalizing f with
  | prime_pow p r hp _ =>
    have hp' : p.Prime := hp
    unfold heckeTMod
    rw [heckeTCompositeGamma0_prime_pow N hp' r]
    by_cases hpN : p.Coprime N
    · rw [coeffMod_heckeTGeneratorRec_zero hp' hpN, divisorSumChar_prime_pow hp']
    · have hdvd : p ∣ N := (Nat.Prime.dvd_iff_not_coprime hp').mpr hpN
      have h := qExpansion_coeff_heckeRingHomCharSpace_heckeTGeneratorRecGamma0_of_dvd_level
        (k := k) (χ := χ.toUnitHom) hp' hdvd f 0 r
      rw [mul_zero] at h
      rw [divisorSumChar_prime_pow_of_dvd hp' hdvd, one_mul]
      exact h
  | zero => exact absurd rfl hm
  | one =>
    unfold heckeTMod
    rw [heckeTCompositeGamma0_one, map_one, one_apply_eq_self, divisorSumChar_one, one_mul]
  | coprime a b _ _ hab iha ihb =>
    have ha : a ≠ 0 := fun h ↦ hm (by simp [h])
    have hb : b ≠ 0 := fun h ↦ hm (by simp [h])
    have hT : heckeTMod k χ (a * b) = heckeTMod k χ a * heckeTMod k χ b := by
      unfold heckeTMod
      rw [heckeTCompositeGamma0_mul_of_coprime N hab, map_mul]
    rw [hT, mul_apply_eq_comp, iha ha, ihb hb, divisorSumChar_mul hab]
    ring

/-- **Miyake, Lemma 4.5.14** on `𝒢_k(N, χ)`, every index: if `f = Σ c(n) qⁿ ∈ 𝒢_k(N, χ)` and
`f ∣ T(m) = Σ b(n) qⁿ` (`m ≥ 1`), then `b(n) = Σ_{0 < d ∣ (m, n)} χ(d) d^{k-1} c(mn/d²)` for every
`n ≥ 0`. -/
@[kb "miyake1989" "Lemma 4.5.14, p. 147 (modular forms)"]
theorem coeffMod_heckeTMod_all (k : ℤ) (χ : DirichletCharacter ℂ N) {m : ℕ} (hm : m ≠ 0)
    (f : modSpace k χ) (n : ℕ) :
    coeffMod (heckeTMod k χ m f) n =
      ∑ d ∈ (Nat.gcd m n).divisors, χ d * (d : ℂ) ^ (k - 1) * coeffMod f (m * n / d ^ 2) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Nat.gcd_zero_right, mul_zero, Nat.zero_div]
    exact coeffMod_heckeTMod_zero k χ hm f
  · exact coeffMod_heckeTMod k χ hm f hn

end ModularFormsKB.Miyake.Wave13
