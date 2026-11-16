/-
# The congruent number curves $E_n : y^2 = x^3 - n^2x$ as Weierstrass curves over $\mathbb Q$

`congruentCurve n` is Mathlib's Weierstrass curve $[0, 0, 0, -n^2, 0]$ over $\mathbb Q$; for $n \ne 0$ it is elliptic
($\Delta = 64n^6$). `congruentCurve 1` is Tau Ceti's `TauCeti.CurveX3SubX.curve ℚ`.

**Proved here:**
- `congruentCurve_Δ`, `isElliptic_congruentCurve`: $\Delta(E_n) = 64n^6$, so $E_n$ is elliptic for $n \ne 0$;
- `hasPointYNeZero_iff_exists_point`: Tunnell's predicate `HasPointYNeZero n` is the existence of an affine point of
  Mathlib's $E_n(\mathbb Q)$ with $y \ne 0$;
- `two_smul_eq_zero_of_y_eq_zero`: the affine points with $y = 0$ have order two;
- `hasPointYNeZero_of_finrank_pos`: if $E_n(\mathbb Q)$ has positive rank, it has a point with $y \ne 0$ (a point of
  infinite order is not $2$-torsion);
- `isCongruent_of_finrank_pos`: positive rank makes $n$ congruent.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.Tunnell
import TauCeti.AlgebraicGeometry.EllipticCurve.BirchSwinnertonDyer.Statement
import TauCeti.AlgebraicGeometry.EllipticCurve.LocalPolynomial
import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
import TauCeti.AlgebraicGeometry.EllipticCurve.CurveX3SubX
import TauCeti.AlgebraicGeometry.EllipticCurve.QuadraticTwist.Basic

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open WeierstrassCurve

/-- **The congruent number curve** $E_n : y^2 = x^3 - n^2x$ over $\mathbb Q$. -/
def congruentCurve (n : ℕ) : WeierstrassCurve ℚ := ⟨0, 0, 0, -((n : ℚ) ^ 2), 0⟩

@[simp] theorem congruentCurve_a₁ (n : ℕ) : (congruentCurve n).a₁ = 0 := rfl
@[simp] theorem congruentCurve_a₂ (n : ℕ) : (congruentCurve n).a₂ = 0 := rfl
@[simp] theorem congruentCurve_a₃ (n : ℕ) : (congruentCurve n).a₃ = 0 := rfl
@[simp] theorem congruentCurve_a₄ (n : ℕ) : (congruentCurve n).a₄ = -((n : ℚ) ^ 2) := rfl
@[simp] theorem congruentCurve_a₆ (n : ℕ) : (congruentCurve n).a₆ = 0 := rfl

/-- $E_1$ is Tau Ceti's curve $y^2 = x^3 - x$. -/
theorem congruentCurve_one : congruentCurve 1 = TauCeti.CurveX3SubX.curve ℚ := by
  ext <;> simp [congruentCurve, TauCeti.CurveX3SubX.curve]

/-- $\Delta(E_n) = 64n^6$. -/
theorem congruentCurve_Δ (n : ℕ) : (congruentCurve n).Δ = 64 * (n : ℚ) ^ 6 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, congruentCurve_a₁, congruentCurve_a₂, congruentCurve_a₃, congruentCurve_a₄,
    congruentCurve_a₆]
  ring

/-- **$E_n$ is elliptic for $n \ne 0$.** -/
instance isElliptic_congruentCurve (n : ℕ) [NeZero n] : (congruentCurve n).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, congruentCurve_Δ, isUnit_iff_ne_zero]
  have : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  positivity

/-- The affine equation of $E_n$ is $y^2 = x^3 - n^2x$. -/
theorem congruentCurve_equation_iff (n : ℕ) (x y : ℚ) :
    (congruentCurve n).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.toAffine, congruentCurve_a₁, congruentCurve_a₂, congruentCurve_a₃,
    congruentCurve_a₄, congruentCurve_a₆]
  constructor <;> intro h <;> linear_combination h

/-- **Tunnell's `HasPointYNeZero n` is a point of Mathlib's $E_n(\mathbb Q)$ with $y \ne 0$** ($n \ne 0$). -/
theorem hasPointYNeZero_iff_exists_point (n : ℕ) [NeZero n] :
    Tunnell.HasPointYNeZero n ↔ ∃ (x y : ℚ) (h : (congruentCurve n).toAffine.Nonsingular x y), y ≠ 0 ∧
      (WeierstrassCurve.Affine.Point.some x y h : (congruentCurve n).toAffine.Point) ≠ 0 := by
  constructor
  · rintro ⟨x, y, hy, h⟩
    have he : (congruentCurve n).toAffine.Equation x y := (congruentCurve_equation_iff n x y).2 h
    exact ⟨x, y, (WeierstrassCurve.Affine.equation_iff_nonsingular).1 he, hy, by simp⟩
  · rintro ⟨x, y, h, hy, -⟩
    exact ⟨x, y, hy, (congruentCurve_equation_iff n x y).1 h.1⟩

/-- **The points with $y = 0$ have order dividing two** ($-(x, y) = (x, -y)$ on $E_n$). -/
theorem two_smul_eq_zero_of_y_eq_zero {n : ℕ} {x y : ℚ} (h : (congruentCurve n).toAffine.Nonsingular x y)
    (hy : y = 0) : (2 : ℤ) • (WeierstrassCurve.Affine.Point.some x y h : (congruentCurve n).toAffine.Point) = 0 := by
  have hneg : -(WeierstrassCurve.Affine.Point.some x y h : (congruentCurve n).toAffine.Point) =
      WeierstrassCurve.Affine.Point.some x y h := by
    rw [WeierstrassCurve.Affine.Point.neg_some]
    subst hy
    congr 1
    simp [WeierstrassCurve.Affine.negY]
  rw [two_zsmul]
  nth_rewrite 2 [← hneg]
  exact add_neg_cancel _

/-- **Positive rank gives a point with $y \ne 0$**: if every point had $y = 0$, every point would be $2$-torsion
(`two_smul_eq_zero_of_y_eq_zero`) and the rank would vanish. -/
theorem hasPointYNeZero_of_finrank_pos {n : ℕ}
    (h : 0 < Module.finrank ℤ (congruentCurve n).toAffine.Point) : Tunnell.HasPointYNeZero n := by
  by_contra hne
  have htors : ∀ P : (congruentCurve n).toAffine.Point, ∃ a : ℤ, a ≠ 0 ∧ a • P = 0 := by
    intro P
    refine ⟨2, by norm_num, ?_⟩
    cases P with
    | zero => exact smul_zero (A := (congruentCurve n).toAffine.Point) (2 : ℤ)
    | some x y hP =>
      by_cases hy : y = 0
      · exact two_smul_eq_zero_of_y_eq_zero hP hy
      · exact absurd ⟨x, y, hy, (congruentCurve_equation_iff n x y).1 hP.1⟩ hne
  have h0 : Module.finrank ℤ (congruentCurve n).toAffine.Point = 0 :=
    Module.finrank_eq_zero_of_rank_eq_zero (rank_eq_zero_iff.2 htors)
  omega

/-- **Positive rank makes $n$ congruent.** -/
theorem isCongruent_of_finrank_pos {n : ℕ} (hn : 0 < n)
    (h : 0 < Module.finrank ℤ (congruentCurve n).toAffine.Point) : Tunnell.IsCongruent n :=
  (Tunnell.isCongruent_iff_point hn).2 (hasPointYNeZero_of_finrank_pos h)

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
