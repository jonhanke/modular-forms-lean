import ModularFormsKB.Milne.Ch8.LevelTwoLambda

/-!
# The invariant of a Weierstrass curve with a point of order two

Let $W$ be a Weierstrass curve over a commutative ring $R$, and let $x_0$ be a root of the $2$-division cubic
$4x^3 + b_2x^2 + 2b_4x + b_6$ (the $x$-coordinate of a point of order two, `LevelTwoLambda.cubic_eq_zero`). Moving it
to $0$ gives a curve with $b_2' = A = b_2 + 12x_0$, $b_4' = B = 6x_0^2 + b_2x_0 + b_4$, $b_6' = 0$ (`coeffA`,
`coeffB`), and $4\Delta = B^2(A^2 - 32B)$ (`four_mul_Δ`). With $2$ invertible the curve is $y^2 = x(x^2 + ax + b)$
with $a = A/4$, $b = B/2$, and the **invariant** $t = a^2/b = A^2/(8B)$ (`inv`). For elliptic $W$, $B$ and
$t - 4 = (A^2 - 32B)/(8B)$ are units (`isUnit_coeffB`, `isUnit_inv_sub_four`). The invariant is unchanged by
changes of variables ($A \mapsto u^{-2}A$, $B \mapsto u^{-4}B$, `inv_variableChange`) and natural under ring maps
(`inv_map`).
-/

universe u

namespace ModularFormsKB.Milne.CyclicTwo

open WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- $A = b_2 + 12x_0$. -/
def coeffA (x₀ : R) : R := W.b₂ + 12 * x₀

/-- $B = 6x_0^2 + b_2x_0 + b_4$. -/
def coeffB (x₀ : R) : R := 6 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄

variable {W}

/-- **The discriminant through a root of the $2$-division cubic**: $4\Delta = B^2(A^2 - 32B)$. -/
theorem four_mul_Δ {x₀ : R} (h₀ : 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆ = 0) :
    4 * W.Δ = coeffB W x₀ ^ 2 * (coeffA W x₀ ^ 2 - 32 * coeffB W x₀) := by
  have h8 := W.b_relation
  have hb6 : W.b₆ = -(4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀) := by linear_combination h₀
  rw [hb6] at h8
  rw [Δ, hb6]
  simp only [coeffA, coeffB]
  linear_combination (-W.b₂ ^ 2) * h8

variable (W) in
/-- **The invariant** $t = A^2/(8B)$. -/
noncomputable def inv {x₀ : R} (hB : IsUnit (8 * coeffB W x₀)) : R := coeffA W x₀ ^ 2 * ↑hB.unit⁻¹

theorem inv_mul {x₀ : R} (hB : IsUnit (8 * coeffB W x₀)) : inv W hB * (8 * coeffB W x₀) = coeffA W x₀ ^ 2 := by
  rw [inv, mul_assoc, hB.val_inv_mul, mul_one]

theorem inv_eq_iff {x₀ : R} (hB : IsUnit (8 * coeffB W x₀)) (l : R) :
    inv W hB = l ↔ l * (8 * coeffB W x₀) = coeffA W x₀ ^ 2 := by
  rw [← inv_mul hB]
  constructor
  · rintro rfl; rfl
  · intro h; exact (hB.mul_left_injective h).symm

variable {x₀ : R} (h₀ : 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆ = 0)

include h₀ in
theorem isUnit_coeffB (h2 : IsUnit (2 : R)) (hΔ : IsUnit W.Δ) : IsUnit (8 * coeffB W x₀) := by
  have h4 : IsUnit (4 * W.Δ) := by
    have : (4 : R) = 2 * 2 := by norm_num
    rw [this]; exact (h2.mul h2).mul hΔ
  rw [four_mul_Δ h₀] at h4
  have hB := isUnit_of_mul_isUnit_left h4
  rw [isUnit_pow_iff two_ne_zero] at hB
  have h8 : (8 : R) = 2 * 2 * 2 := by norm_num
  rw [h8]
  exact ((h2.mul h2).mul h2).mul hB

include h₀ in
theorem isUnit_inv_sub_four (h2 : IsUnit (2 : R)) (hΔ : IsUnit W.Δ) :
    IsUnit (inv W (isUnit_coeffB h₀ h2 hΔ) - 4) := by
  have hB := isUnit_coeffB h₀ h2 hΔ
  have h4 : IsUnit (4 * W.Δ) := by
    have : (4 : R) = 2 * 2 := by norm_num
    rw [this]; exact (h2.mul h2).mul hΔ
  rw [four_mul_Δ h₀] at h4
  have hd := isUnit_of_mul_isUnit_right h4
  have hm : (inv W hB - 4) * (8 * coeffB W x₀) = coeffA W x₀ ^ 2 - 32 * coeffB W x₀ := by
    rw [sub_mul, inv_mul]; ring
  rw [← hm] at hd
  exact isUnit_of_mul_isUnit_left hd

/-- **Naturality of the invariant under ring maps.** -/
theorem inv_map {R' : Type u} [CommRing R'] (φ : R →+* R') {x₀ : R} (hB : IsUnit (8 * coeffB W x₀))
    (hB' : IsUnit (8 * coeffB (W.map φ) (φ x₀))) : inv (W.map φ) hB' = φ (inv W hB) := by
  rw [inv_eq_iff]
  have := congrArg φ (inv_mul hB)
  simp only [map_mul, map_pow, coeffA, coeffB, map_add, map_ofNat, map_b₂, map_b₄] at this ⊢
  exact this

/-- **Invariance under changes of variables**: the point $x_0'$ of $C \cdot W$ is the point $u^2x_0' + r$ of $W$. -/
theorem inv_variableChange (C : VariableChange R) {x₀ : R}
    (hB : IsUnit (8 * coeffB (C • W) x₀)) (hB' : IsUnit (8 * coeffB W ((C.u : R) ^ 2 * x₀ + C.r))) :
    inv (C • W) hB = inv W hB' := by
  rw [inv_eq_iff]
  set v : R := ((C.u⁻¹ : Rˣ) : R)
  have hv : v * (C.u : R) = 1 := by simp [v]
  have hl := inv_mul hB'
  simp only [coeffA, coeffB, variableChange_b₂, variableChange_b₄] at hl ⊢
  have hu4 : IsUnit ((C.u : R) ^ 4) := (Units.isUnit _).pow 4
  apply hu4.mul_left_injective
  simp only
  set l := inv W hB'
  -- `u² A' = A` and `u⁴ B' = B`, with `v u = 1`
  have hA : (C.u : R) ^ 2 * (v ^ 2 * (W.b₂ + 12 * C.r) + 12 * x₀) = W.b₂ + 12 * ((C.u : R) ^ 2 * x₀ + C.r) := by
    linear_combination (W.b₂ + 12 * C.r) * (v * (C.u : R) + 1) * hv
  have hB4 : (C.u : R) ^ 4 * (6 * x₀ ^ 2 + v ^ 2 * (W.b₂ + 12 * C.r) * x₀ +
      v ^ 4 * (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2)) =
      6 * ((C.u : R) ^ 2 * x₀ + C.r) ^ 2 + W.b₂ * ((C.u : R) ^ 2 * x₀ + C.r) + W.b₄ := by
    linear_combination ((C.u : R) ^ 2 * (W.b₂ + 12 * C.r) * x₀ * (v * (C.u : R) + 1) +
      (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2) * (v * (C.u : R) + 1) * ((v * (C.u : R)) ^ 2 + 1)) * hv
  linear_combination 8 * l * hB4 + hl -
    ((C.u : R) ^ 2 * (v ^ 2 * (W.b₂ + 12 * C.r) + 12 * x₀) + (W.b₂ + 12 * ((C.u : R) ^ 2 * x₀ + C.r))) * hA

end ModularFormsKB.Milne.CyclicTwo
