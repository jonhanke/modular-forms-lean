import ModularFormsKB.Milne.Ch0.Introduction
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-!
# Milne, Example 0.3: nonsingularity of `Y² = 4X³ - aX - b`

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Introduction, pdf p. 8. Mathlib has the direction
"nonzero discriminant implies nonsingular" for Weierstrass curves
(`WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero`); here both directions, for the book's model and its
notion of nonsingular plane curve.
-/

open MvPolynomial

namespace ModularFormsKB.Milne

theorem E03_exists_root {K : Type*} [Field K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0) (A B : K)
    (h : A ^ 3 - 27 * B ^ 2 = 0) : ∃ x : K, 12 * x ^ 2 = A ∧ 4 * x ^ 3 - A * x - B = 0 := by
  by_cases h3 : (3 : K) = 0
  · have h12 : (12 : K) = 0 := by linear_combination 4 * h3
    have h27 : (27 : K) = 0 := by linear_combination 9 * h3
    have hA : A = 0 := by
      have : A ^ 3 = 0 := by rw [h27] at h; linear_combination h
      exact pow_eq_zero_iff (by norm_num) |>.1 this
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (B / 4) (by norm_num : 0 < 3)
    have h4 : (4 : K) ≠ 0 := by
      have : (4 : K) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    refine ⟨x, by rw [h12, hA]; ring, ?_⟩
    have : 4 * x ^ 3 = B := by rw [hx]; field_simp
    rw [hA]; linear_combination this
  · by_cases hA : A = 0
    · have h27 : (27 : K) ≠ 0 := by
        have : (27 : K) = 3 ^ 3 := by norm_num
        rw [this]; exact pow_ne_zero _ h3
      have hB : B = 0 := by
        have : B ^ 2 = 0 := by
          rw [hA] at h
          have : 27 * B ^ 2 = 0 := by linear_combination -h
          exact (mul_eq_zero.1 this).resolve_left h27
        exact pow_eq_zero_iff (by norm_num) |>.1 this
      exact ⟨0, by rw [hA]; ring, by rw [hA, hB]; ring⟩
    · refine ⟨-3 * B / (2 * A), ?_, ?_⟩
      · field_simp
        linear_combination (-4) * h
      · field_simp
        linear_combination (4 * B) * h

/-- The affine plane curve `Y² = 4X³ - aX - b`, i.e. `f(X, Y) = Y² - 4X³ + aX + b` (Milne, Example 0.3). -/
noncomputable def weierstrassPlaneCurve {k : Type*} [Field k] (a b : k) : AffinePlaneCurve k where
  f := X 1 ^ 2 - 4 * X 0 ^ 3 + C a * X 0 + C b
  ne_zero := by
    intro h
    have h1 := congrArg (aeval (![0, 1] : Fin 2 → k)) h
    have h0 := congrArg (aeval (![0, 0] : Fin 2 → k)) h
    simp at h1 h0
    simp [h0] at h1

/-- **Milne, Example 0.3.** For a field `k` of characteristic `≠ 2`, the curve `Y² = 4X³ - aX - b` is nonsingular if
and only if its discriminant `a³ - 27b²` is nonzero. -/
@[kb "milne2017mf" "Example 0.3, pdf p. 8"]
theorem weierstrassPlaneCurve_isNonsingular_iff {k : Type*} [Field k] (hk : ringChar k ≠ 2) (a b : k) :
    (weierstrassPlaneCurve a b).IsNonsingular ↔ a ^ 3 - 27 * b ^ 2 ≠ 0 := by
  have h2k : (2 : k) ≠ 0 := by
    intro h
    have hd : ringChar k ∣ 2 := (ringChar.spec k 2).1 (by exact_mod_cast h)
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · exact hk h1
  have h2 : (2 : AlgebraicClosure k) ≠ 0 := by
    intro h
    apply h2k
    apply (algebraMap k (AlgebraicClosure k)).injective
    rw [map_zero]
    exact (map_ofNat (algebraMap k (AlgebraicClosure k)) 2).trans h
  have key : ∀ p : AlgebraicClosure k × AlgebraicClosure k,
      (weierstrassPlaneCurve a b).IsSingularPoint p ↔
        p.2 = 0 ∧ 12 * p.1 ^ 2 = algebraMap k _ a ∧
          4 * p.1 ^ 3 - algebraMap k _ a * p.1 - algebraMap k _ b = 0 := by
    intro p
    obtain ⟨x, y⟩ := p
    simp only [AffinePlaneCurve.IsSingularPoint, weierstrassPlaneCurve]
    have p4 : ∀ i, pderiv i (4 : MvPolynomial (Fin 2) k) = 0 := by
      intro i
      have : (4 : MvPolynomial (Fin 2) k) = C 4 := (map_ofNat C 4).symm
      rw [this, pderiv_C]
    simp [pderiv_X, p4]
    constructor
    · rintro ⟨h1, h2', h3⟩
      have hy : y = 0 := h3.resolve_left h2
      subst hy
      refine ⟨rfl, by linear_combination -h2', by linear_combination -h1⟩
    · rintro ⟨hy, h2', h3⟩
      subst hy
      refine ⟨by linear_combination -h3, by linear_combination -h2', by simp⟩
  have hmap : a ^ 3 - 27 * b ^ 2 = 0 ↔
      (algebraMap k (AlgebraicClosure k)) a ^ 3 - 27 * (algebraMap k (AlgebraicClosure k)) b ^ 2 = 0 := by
    rw [← map_pow, ← map_pow, ← map_ofNat (algebraMap k (AlgebraicClosure k)) 27, ← map_mul, ← map_sub,
      ← map_zero (algebraMap k (AlgebraicClosure k))]
    exact (algebraMap k (AlgebraicClosure k)).injective.eq_iff.symm
  constructor
  · intro hnon hd
    obtain ⟨x, hx1, hx2⟩ := E03_exists_root h2 _ _ (hmap.1 hd)
    exact hnon (x, 0) ((key _).2 ⟨rfl, hx1, hx2⟩)
  · intro hd p hp
    obtain ⟨-, h1, h3⟩ := (key p).1 hp
    apply hd
    rw [hmap, ← h1]
    have hb : algebraMap k (AlgebraicClosure k) b = 4 * p.1 ^ 3 - 12 * p.1 ^ 2 * p.1 := by
      rw [h1]; linear_combination -h3
    rw [hb]
    ring

end ModularFormsKB.Milne
