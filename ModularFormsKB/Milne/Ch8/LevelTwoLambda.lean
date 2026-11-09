import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# The Legendre parameter of a Weierstrass curve with two points of order two

Let $W$ be a Weierstrass curve over a commutative ring $R$ in which $2$ is a unit, with inverse $i_2$, and let
$(x_1, y_1), (x_2, y_2)$ be points of order two: $2y_i + a_1x_i + a_3 = 0$. Completing the square, $x_1, x_2$ are roots
of $4x^3 + b_2x^2 + 2b_4x + b_6$ (`cubic_eq_zero`); the third root is $e_3 = -b_2/4 - x_1 - x_2$ (`thirdRoot`), and
$$\Delta = 16\,(x_1 - x_2)^2(x_1 - e_3)^2(x_2 - e_3)^2$$
when $x_2 - x_1$ is a unit (`Δ_eq`). The **Legendre parameter** is $\lambda = (e_3 - x_1)/(x_2 - x_1)$ (`lam`): the
Legendre form $y^2 = x(x - 1)(x - \lambda)$ has the points $(0, 0), (1, 0)$ and third root $\lambda$. For elliptic $W$,
$\lambda$ and $\lambda - 1$ are units (`isUnit_lam`, `isUnit_lam_sub_one`). It is invariant under changes of variables
(`lam_variableChange`) and natural under ring maps (`lam_map`).
-/

universe u

namespace ModularFormsKB.Milne.LevelTwoLambda

open WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The third root $e_3 = -b_2/4 - x_1 - x_2$ of the $2$-division cubic, for $i_2 = 1/2$. -/
def thirdRoot (i₂ x₁ x₂ : R) : R := -W.b₂ * i₂ ^ 2 - x₁ - x₂

/-- **The Legendre parameter** $\lambda = (e_3 - x_1)/(x_2 - x_1)$. -/
noncomputable def lam (i₂ : R) {x₁ x₂ : R} (h : IsUnit (x₂ - x₁)) : R :=
  (thirdRoot W i₂ x₁ x₂ - x₁) * ↑h.unit⁻¹

variable {W}

/-- **The $x$-coordinate of a point of order two is a root of the $2$-division cubic.** -/
theorem cubic_eq_zero {x y : R} (h : W.toAffine.Equation x y) (hy : 2 * y + W.a₁ * x + W.a₃ = 0) :
    4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 := by
  rw [Affine.equation_iff] at h
  simp only [b₂, b₄, b₆]
  linear_combination (-4) * h + (2 * y + W.a₁ * x + W.a₃) * hy

variable {i₂ : R} (hi : 2 * i₂ = 1) {x₁ x₂ : R} (h₁ : 4 * x₁ ^ 3 + W.b₂ * x₁ ^ 2 + 2 * W.b₄ * x₁ + W.b₆ = 0)
  (h₂ : 4 * x₂ ^ 3 + W.b₂ * x₂ ^ 2 + 2 * W.b₄ * x₂ + W.b₆ = 0) (hx : IsUnit (x₂ - x₁))

include hi in
theorem b₂_eq : W.b₂ = -4 * (x₁ + x₂ + thirdRoot W i₂ x₁ x₂) := by
  simp only [thirdRoot]
  linear_combination (-W.b₂ * (2 * i₂ + 1)) * hi

include hi h₁ h₂ hx in
theorem b₄_eq : W.b₄ = 2 * (x₁ * x₂ + (x₁ + x₂) * thirdRoot W i₂ x₁ x₂) := by
  have hb := b₂_eq (W := W) (x₁ := x₁) (x₂ := x₂) hi
  set e := thirdRoot W i₂ x₁ x₂
  -- `(x₁ - x₂) (4(x₁² + x₁x₂ + x₂²) + b₂(x₁ + x₂) + 2b₄) = 0`
  have hd : (x₂ - x₁) * (4 * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) + W.b₂ * (x₁ + x₂) + 2 * W.b₄) = 0 := by
    linear_combination h₂ - h₁
  have h0 := (hx.mul_right_eq_zero).mp hd
  rw [hb] at h0
  linear_combination i₂ * h0 - (W.b₄ - 2 * (x₁ * x₂ + (x₁ + x₂) * e)) * hi

include hi h₁ h₂ hx in
theorem b₆_eq : W.b₆ = -4 * (x₁ * x₂ * thirdRoot W i₂ x₁ x₂) := by
  have hb := b₂_eq (W := W) (x₁ := x₁) (x₂ := x₂) hi
  have hb4 := b₄_eq hi h₁ h₂ hx
  rw [hb, hb4] at h₁
  linear_combination h₁

include hi h₁ h₂ hx in
/-- **The discriminant** of a Weierstrass curve with two points of order two, $2$ invertible:
$\Delta = 16 (x_1 - x_2)^2 (x_1 - e_3)^2 (x_2 - e_3)^2$. -/
theorem Δ_eq : W.Δ = 16 * ((x₁ - x₂) * (x₁ - thirdRoot W i₂ x₁ x₂) * (x₂ - thirdRoot W i₂ x₁ x₂)) ^ 2 := by
  have hb := b₂_eq (W := W) (x₁ := x₁) (x₂ := x₂) hi
  have hb4 := b₄_eq hi h₁ h₂ hx
  have hb6 := b₆_eq hi h₁ h₂ hx
  have h8 := W.b_relation
  set e := thirdRoot W i₂ x₁ x₂
  rw [hb, hb4, hb6] at h8
  rw [Δ, hb, hb4, hb6]
  linear_combination (-4 * (x₁ + x₂ + e) ^ 2) * h8

include hi h₁ h₂ hx in
theorem isUnit_diffs (hΔ : IsUnit W.Δ) :
    IsUnit (thirdRoot W i₂ x₁ x₂ - x₁) ∧ IsUnit (thirdRoot W i₂ x₁ x₂ - x₂) := by
  rw [Δ_eq hi h₁ h₂ hx] at hΔ
  have h := isUnit_of_mul_isUnit_right hΔ
  rw [isUnit_pow_iff two_ne_zero] at h
  have ha := isUnit_of_mul_isUnit_left h
  have hb := isUnit_of_mul_isUnit_right h
  have hc := isUnit_of_mul_isUnit_right ha
  refine ⟨?_, ?_⟩
  · have : thirdRoot W i₂ x₁ x₂ - x₁ = -(x₁ - thirdRoot W i₂ x₁ x₂) := by ring
    rw [this]; exact hc.neg
  · have : thirdRoot W i₂ x₁ x₂ - x₂ = -(x₂ - thirdRoot W i₂ x₁ x₂) := by ring
    rw [this]; exact hb.neg

theorem lam_mul (i₂ : R) {x₁ x₂ : R} (hx : IsUnit (x₂ - x₁)) :
    lam W i₂ hx * (x₂ - x₁) = thirdRoot W i₂ x₁ x₂ - x₁ := by
  rw [lam, mul_assoc, hx.val_inv_mul, mul_one]

include hi h₁ h₂ in
theorem isUnit_lam (hΔ : IsUnit W.Δ) : IsUnit (lam W i₂ hx) :=
  (isUnit_diffs hi h₁ h₂ hx hΔ).1.mul (Units.isUnit _)

include hi h₁ h₂ in
theorem isUnit_lam_sub_one (hΔ : IsUnit W.Δ) : IsUnit (lam W i₂ hx - 1) := by
  have h : lam W i₂ hx - 1 = (thirdRoot W i₂ x₁ x₂ - x₂) * ↑hx.unit⁻¹ := by
    have h1 := lam_mul (W := W) i₂ hx
    have h2 : ((hx.unit⁻¹ : Rˣ) : R) * (x₂ - x₁) = 1 := hx.val_inv_mul
    linear_combination (↑hx.unit⁻¹ : R) * h1 - (lam W i₂ hx - 1) * h2
  rw [h]
  exact (isUnit_diffs hi h₁ h₂ hx hΔ).2.mul (Units.isUnit _)

/-- **$\lambda$ is characterized by $\lambda (x_2 - x_1) = e_3 - x_1$.** -/
theorem lam_eq_iff (i₂ : R) {x₁ x₂ : R} (hx : IsUnit (x₂ - x₁)) (l : R) :
    lam W i₂ hx = l ↔ l * (x₂ - x₁) = thirdRoot W i₂ x₁ x₂ - x₁ := by
  rw [← lam_mul i₂ hx]
  constructor
  · rintro rfl; rfl
  · intro h; exact (hx.mul_left_injective h).symm

/-- **Naturality of $\lambda$ under ring maps.** -/
theorem lam_map {R' : Type u} [CommRing R'] (φ : R →+* R') (i₂ : R) {x₁ x₂ : R} (hx : IsUnit (x₂ - x₁))
    (hx' : IsUnit (φ x₂ - φ x₁)) : lam (W.map φ) (φ i₂) hx' = φ (lam W i₂ hx) := by
  rw [lam_eq_iff, ← map_sub, ← map_mul, lam_mul]
  simp [thirdRoot, map_b₂]

/-- **Invariance of $\lambda$ under changes of variables**: the points $(x_i', y_i')$ of $C \cdot W$ correspond to the
points with $x_i = u^2x_i' + r$ of $W$. -/
theorem lam_variableChange (C : VariableChange R) (i₂ : R) (hi : 2 * i₂ = 1) {x₁ x₂ : R} (hx : IsUnit (x₂ - x₁))
    (hx' : IsUnit (((C.u : R) ^ 2 * x₂ + C.r) - ((C.u : R) ^ 2 * x₁ + C.r))) :
    lam (C • W) i₂ hx = lam W i₂ hx' := by
  rw [lam_eq_iff]
  set v : R := ((C.u⁻¹ : Rˣ) : R)
  have hv : v * (C.u : R) = 1 := by simp [v]
  have hl := lam_mul (W := W) i₂ hx'
  simp only [thirdRoot, variableChange_b₂] at hl ⊢
  -- multiply through by `u²`
  have hu2 : IsUnit ((C.u : R) ^ 2) := (Units.isUnit _).pow 2
  apply hu2.mul_left_injective
  simp only
  linear_combination hl + ((W.b₂ + 12 * C.r) * i₂ ^ 2 * (v * (C.u : R) + 1)) * hv +
    (3 * C.r * (2 * i₂ + 1)) * hi

end ModularFormsKB.Milne.LevelTwoLambda
