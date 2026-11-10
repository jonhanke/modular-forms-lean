import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# The algebra behind Kronecker's congruence

Let $K$ be a field and $p \ge 2$. If $G(X, Y) \in K[X, Y]$ is symmetric, monic of degree $p + 1$ in $Y$, and
$G(X, X^p) = 0$, then $G = X^{p+1} + Y^{p+1} - X^pY^p - XY = -(Y - X^p)(X - Y^p)$: the irreducible polynomials
$Y - X^p$ and (by symmetry) $X - Y^p$ divide $G$, they are not associated, and degrees in $Y$ match. With
$G = F \bmod p$ and $G(X, X^p) = 0$ from $j(pz) \equiv j(z)^p$, this is Kronecker's congruence (Milne, Section 6,
Theorem 6.1, pdf p. 89). Variables: `X 0` is $X$, `X 1` is $Y$.
-/

open Polynomial

noncomputable section

namespace ModularFormsKB.Milne.KroneckerAlgebra

variable {K : Type*} [Field K]

/-- $K[X, Y] \to K[X][Y]$, $X \mapsto X$ (inner), $Y \mapsto Y$ (outer). -/
def toPoly : MvPolynomial (Fin 2) K →+* K[X][X] := MvPolynomial.eval₂Hom (C.comp C) ![C X, X]

/-- The inverse of `toPoly`. -/
def ofPoly : K[X][X] →+* MvPolynomial (Fin 2) K :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)) (MvPolynomial.X 1)

theorem ofPoly_toPoly : ofPoly.comp (toPoly (K := K)) = RingHom.id _ := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · simp [toPoly, ofPoly]
  · fin_cases i <;> simp [toPoly, ofPoly]

theorem toPoly_ofPoly : (toPoly (K := K)).comp ofPoly = RingHom.id _ := by
  refine Polynomial.ringHom_ext' ?_ ?_
  · refine Polynomial.ringHom_ext' ?_ ?_
    · ext r; simp [toPoly, ofPoly]
    · simp [toPoly, ofPoly]
  · simp [toPoly, ofPoly]

/-- $K[X, Y] \cong K[X][Y]$. -/
def polyEquiv : MvPolynomial (Fin 2) K ≃+* K[X][X] :=
  RingEquiv.ofRingHom (toPoly (K := K)) ofPoly toPoly_ofPoly ofPoly_toPoly

@[simp] theorem polyEquiv_apply (G : MvPolynomial (Fin 2) K) : polyEquiv G = toPoly G := rfl

theorem toPoly_X0 : toPoly (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) = C X := by simp [toPoly]

theorem toPoly_X1 : toPoly (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) = X := by simp [toPoly]

theorem eval_toPoly (G : MvPolynomial (Fin 2) K) (p : ℕ) :
    (toPoly G).eval (X ^ p) = MvPolynomial.aeval ![(X : K[X]), X ^ p] G := by
  have : (Polynomial.evalRingHom (X ^ p : K[X])).comp (toPoly (K := K)) =
      (MvPolynomial.aeval ![(X : K[X]), X ^ p]).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
    · simp [toPoly]
    · fin_cases i <;> simp [toPoly]
  exact congrArg (fun f ↦ f G) this

theorem eq_kronecker (p : ℕ) (hp : 2 ≤ p) (G : MvPolynomial (Fin 2) K)
    (hsym : MvPolynomial.rename (Equiv.swap 0 1) G = G)
    (hroot : MvPolynomial.aeval ![(X : K[X]), X ^ p] G = 0)
    (hmon : (MvPolynomial.eval₂ (C.comp C) ![C X, X] G : K[X][X]).Monic)
    (hdeg : (MvPolynomial.eval₂ (C.comp C) ![C X, X] G : K[X][X]).natDegree = p + 1) :
    G = MvPolynomial.X 0 ^ (p + 1) + MvPolynomial.X 1 ^ (p + 1) -
      MvPolynomial.X 0 ^ p * MvPolynomial.X 1 ^ p - MvPolynomial.X 0 * MvPolynomial.X 1 := by
  set A : MvPolynomial (Fin 2) K := MvPolynomial.X 1 - MvPolynomial.X 0 ^ p with hA
  set B : MvPolynomial (Fin 2) K := MvPolynomial.rename (Equiv.swap 0 1) A with hB
  have hBe : B = MvPolynomial.X 0 - MvPolynomial.X 1 ^ p := by
    simp [hB, hA, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hTA : toPoly A = X - C (X ^ p) := by
    simp [hA, toPoly_X0, toPoly_X1]
  have hTB : toPoly B = C X - X ^ p := by
    rw [hBe]; simp [toPoly_X0, toPoly_X1]
  -- `A ∣ G`.
  have hAG : A ∣ G := by
    have h1 : toPoly A ∣ toPoly G := by
      rw [hTA, dvd_iff_isRoot, IsRoot, eval_toPoly, hroot]
    rw [← polyEquiv_apply, ← polyEquiv_apply] at h1
    exact (map_dvd_iff polyEquiv).1 h1
  -- `B ∣ G`.
  have hBG : B ∣ G := by
    have := map_dvd (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)) hAG
    rwa [hsym] at this
  -- Irreducibility.
  have hAirr : Irreducible A := by
    have h : Irreducible (toPoly A) := by
      rw [hTA]
      exact (monic_X_sub_C _).irreducible_of_degree_eq_one (degree_X_sub_C _)
    rw [← polyEquiv_apply] at h
    exact (MulEquiv.irreducible_iff (polyEquiv (K := K))).1 h
  have hBirr : Irreducible B := by
    rw [hB, ← MvPolynomial.renameEquiv_apply (R := K)]
    exact (MulEquiv.irreducible_iff (MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1))).2 hAirr
  -- `A ∤ B`.
  have hAB : ¬ A ∣ B := by
    intro h
    obtain ⟨Q, hQ⟩ := h
    have h1 := congrArg (MvPolynomial.aeval ![(X : K[X]), X ^ p]) hQ
    have hA0 : MvPolynomial.aeval ![(X : K[X]), X ^ p] A = 0 := by simp [hA]
    rw [map_mul, hA0, zero_mul, hBe] at h1
    simp only [map_sub, map_pow, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one] at h1
    have h2 := congrArg (Polynomial.coeff · 1) h1
    simp only [coeff_sub, coeff_X_one, ← pow_mul, coeff_X_pow, coeff_zero] at h2
    have : ¬ (1 = p * p) := by nlinarith
    simp [this] at h2
  have hrel : IsRelPrime A B := hAirr.isRelPrime_iff_not_dvd.2 hAB
  obtain ⟨Q, hQ⟩ := hrel.mul_dvd hAG hBG
  -- Degrees in `Y`.
  have hTG : toPoly G = (X - C (X ^ p)) * (X ^ p - C X) * (-toPoly Q) := by
    rw [hQ, map_mul, map_mul, hTA, hTB]; ring
  have hm1 : ((X - C (X ^ p)) * (X ^ p - C X) : K[X][X]).Monic :=
    (monic_X_sub_C _).mul (monic_X_pow_sub_C _ (by omega))
  have hd1 : ((X - C (X ^ p)) * (X ^ p - C X) : K[X][X]).natDegree = p + 1 := by
    rw [(monic_X_sub_C _).natDegree_mul (monic_X_pow_sub_C _ (by omega)), natDegree_X_sub_C,
      natDegree_X_pow_sub_C]; ring
  have hmon' : (toPoly G).Monic := hmon
  have hdeg' : (toPoly G).natDegree = p + 1 := hdeg
  rw [hTG] at hmon' hdeg'
  have hmQ : (-toPoly Q).Monic := hm1.of_mul_monic_left hmon'
  have hdQ : (-toPoly Q).natDegree = 0 := by
    rw [hm1.natDegree_mul hmQ, hd1] at hdeg'; omega
  have hQ1 : -toPoly Q = 1 := hmQ.natDegree_eq_zero.1 hdQ
  have hfin : toPoly G = toPoly (MvPolynomial.X 0 ^ (p + 1) + MvPolynomial.X 1 ^ (p + 1) -
      MvPolynomial.X 0 ^ p * MvPolynomial.X 1 ^ p - MvPolynomial.X 0 * MvPolynomial.X 1) := by
    rw [hTG, hQ1]
    simp only [map_sub, map_add, map_mul, map_pow, toPoly_X0, toPoly_X1]
    ring
  rw [← polyEquiv_apply, ← polyEquiv_apply] at hfin
  exact polyEquiv.injective hfin

end ModularFormsKB.Milne.KroneckerAlgebra
