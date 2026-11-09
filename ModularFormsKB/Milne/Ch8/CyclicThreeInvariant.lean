import ModularFormsKB.Milne.Ch8.CyclicTwoInvariant
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-!
# The invariant of a Weierstrass curve with a point of order three

Let $W$ be a Weierstrass curve over a commutative ring $R$ and $x_0$ a root of the $3$-division polynomial
$\Psi_3 = 3x^4 + b_2x^3 + 3b_4x^2 + 3b_6x + b_8$ (the $x$-coordinate of a point of order three). Moving $x_0$ to $0$
gives a curve with $b_2' = A = b_2 + 12x_0$, $b_4' = B = 6x_0^2 + b_2x_0 + b_4$ (`CyclicTwo.coeffA`,
`CyclicTwo.coeffB`), $b_6' = C = 4x_0^3 + b_2x_0^2 + 2b_4x_0 + b_6$ (`coeffC`) and $b_8' = \Psi_3(x_0) = 0$. In the
normal form $y^2 + a_1xy + a_3y = x^3$ of a point $(0, 0)$ of order three, $A = a_1^2$, $B = a_1a_3$, $C = a_3^2$, so
the **invariant** $t = a_1^3/a_3$ is $AB/C$ (`inv3`). When $C$ is a unit ($C = (2y_0 + a_1x_0 + a_3)^2$ on the curve),
$(t - 27)C^2 = \Delta$ (`inv3_sub_mul`), so for elliptic $W$, $t - 27$ is a unit (`isUnit_inv3_sub`). The invariant is
unchanged by changes of variables (`inv3_variableChange`) and natural under ring maps (`inv3_map`).
-/

universe u

namespace ModularFormsKB.Milne.CyclicThree

open WeierstrassCurve CyclicTwo

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- $C = 4x_0^3 + b_2x_0^2 + 2b_4x_0 + b_6$, the value of the $2$-division cubic. -/
def coeffC (x₀ : R) : R := 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆

/-- The value of the $3$-division polynomial: $3x_0^4 + b_2x_0^3 + 3b_4x_0^2 + 3b_6x_0 + b_8$. -/
def psi3 (x₀ : R) : R := 3 * x₀ ^ 4 + W.b₂ * x₀ ^ 3 + 3 * W.b₄ * x₀ ^ 2 + 3 * W.b₆ * x₀ + W.b₈

theorem psi3_eq (x₀ : R) : psi3 W x₀ = W.Ψ₃.eval x₀ := by
  simp only [psi3, Ψ₃, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_ofNat]

variable {W}

/-- **The discriminant through a root of $\Psi_3$**: $ABC - 27C^2 - \Delta = \Psi_3(x_0)(A^2 - 32B)$. -/
theorem Δ_eq (x₀ : R) :
    coeffA W x₀ * coeffB W x₀ * coeffC W x₀ - 27 * coeffC W x₀ ^ 2 - W.Δ =
      psi3 W x₀ * (coeffA W x₀ ^ 2 - 32 * coeffB W x₀) := by
  simp only [coeffA, coeffB, coeffC, psi3, Δ, b₂, b₄, b₆, b₈]
  ring

/-- On the curve, $C = (2y_0 + a_1x_0 + a_3)^2$. -/
theorem coeffC_eq {x₀ y₀ : R} (h : W.toAffine.Equation x₀ y₀) :
    coeffC W x₀ = (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 := by
  rw [Affine.equation_iff] at h
  simp only [coeffC, b₂, b₄, b₆]
  linear_combination (-4) * h

variable (W) in
/-- **The invariant** $t = AB/C$. -/
noncomputable def inv3 {x₀ : R} (hC : IsUnit (coeffC W x₀)) : R :=
  coeffA W x₀ * coeffB W x₀ * ↑hC.unit⁻¹

theorem inv3_mul {x₀ : R} (hC : IsUnit (coeffC W x₀)) :
    inv3 W hC * coeffC W x₀ = coeffA W x₀ * coeffB W x₀ := by
  rw [inv3, mul_assoc, hC.val_inv_mul, mul_one]

theorem inv3_eq_iff {x₀ : R} (hC : IsUnit (coeffC W x₀)) (l : R) :
    inv3 W hC = l ↔ l * coeffC W x₀ = coeffA W x₀ * coeffB W x₀ := by
  rw [← inv3_mul hC]
  constructor
  · rintro rfl; rfl
  · intro h; exact (hC.mul_left_injective h).symm

theorem inv3_sub_mul {x₀ : R} (hC : IsUnit (coeffC W x₀)) (h₃ : psi3 W x₀ = 0) :
    (inv3 W hC - 27) * coeffC W x₀ ^ 2 = W.Δ := by
  have e := Δ_eq (W := W) x₀
  rw [h₃, zero_mul] at e
  have hm := inv3_mul hC
  linear_combination coeffC W x₀ * hm + e

theorem isUnit_inv3_sub {x₀ : R} (hC : IsUnit (coeffC W x₀)) (h₃ : psi3 W x₀ = 0) (hΔ : IsUnit W.Δ) :
    IsUnit (inv3 W hC - 27) := by
  rw [← inv3_sub_mul hC h₃] at hΔ
  exact isUnit_of_mul_isUnit_left hΔ

/-- **Naturality of the invariant under ring maps.** -/
theorem inv3_map {R' : Type u} [CommRing R'] (φ : R →+* R') {x₀ : R} (hC : IsUnit (coeffC W x₀))
    (hC' : IsUnit (coeffC (W.map φ) (φ x₀))) : inv3 (W.map φ) hC' = φ (inv3 W hC) := by
  rw [inv3_eq_iff]
  have := congrArg φ (inv3_mul hC)
  simp only [map_mul, map_pow, coeffA, coeffB, coeffC, map_add, map_ofNat, map_b₂, map_b₄, map_b₆] at this ⊢
  exact this

/-- **Invariance under changes of variables**: the point $x_0'$ of $C \cdot W$ is the point $u^2x_0' + r$ of $W$. -/
theorem inv3_variableChange (C : VariableChange R) {x₀ : R}
    (hC : IsUnit (coeffC (C • W) x₀)) (hC' : IsUnit (coeffC W ((C.u : R) ^ 2 * x₀ + C.r))) :
    inv3 (C • W) hC = inv3 W hC' := by
  rw [inv3_eq_iff]
  set v : R := ((C.u⁻¹ : Rˣ) : R)
  set u : R := (C.u : R)
  have hv : v * u = 1 := by simp [v, u]
  have h2 : u ^ 2 * v ^ 2 = 1 := by linear_combination (v * u + 1) * hv
  have h4 : u ^ 4 * v ^ 4 = 1 := by linear_combination ((v * u) ^ 2 + 1) * h2
  have h6 : u ^ 6 * v ^ 6 = 1 := by linear_combination ((v * u) ^ 4 + (v * u) ^ 2 + 1) * h2
  have hl := inv3_mul hC'
  simp only [coeffA, coeffB, coeffC, variableChange_b₂, variableChange_b₄, variableChange_b₆] at hl ⊢
  have hu6 : IsUnit (u ^ 6) := (Units.isUnit _).pow 6
  apply hu6.mul_left_injective
  simp only
  set l := inv3 W hC'
  set X := u ^ 2 * x₀ + C.r
  have hA : u ^ 2 * (v ^ 2 * (W.b₂ + 12 * C.r) + 12 * x₀) = W.b₂ + 12 * X := by
    linear_combination (W.b₂ + 12 * C.r) * h2
  have hB : u ^ 4 * (6 * x₀ ^ 2 + v ^ 2 * (W.b₂ + 12 * C.r) * x₀ + v ^ 4 * (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2)) =
      6 * X ^ 2 + W.b₂ * X + W.b₄ := by
    linear_combination u ^ 2 * x₀ * (W.b₂ + 12 * C.r) * h2 + (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2) * h4
  have hCC : u ^ 6 * (4 * x₀ ^ 3 + v ^ 2 * (W.b₂ + 12 * C.r) * x₀ ^ 2 +
      2 * (v ^ 4 * (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2)) * x₀ +
      v ^ 6 * (W.b₆ + 2 * C.r * W.b₄ + C.r ^ 2 * W.b₂ + 4 * C.r ^ 3)) =
      4 * X ^ 3 + W.b₂ * X ^ 2 + 2 * W.b₄ * X + W.b₆ := by
    linear_combination u ^ 4 * x₀ ^ 2 * (W.b₂ + 12 * C.r) * h2 +
      2 * u ^ 2 * x₀ * (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2) * h4 +
      (W.b₆ + 2 * C.r * W.b₄ + C.r ^ 2 * W.b₂ + 4 * C.r ^ 3) * h6
  linear_combination l * hCC + hl -
    (u ^ 4 * (6 * x₀ ^ 2 + v ^ 2 * (W.b₂ + 12 * C.r) * x₀ + v ^ 4 * (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2))) * hA -
    (W.b₂ + 12 * X) * hB

end ModularFormsKB.Milne.CyclicThree
