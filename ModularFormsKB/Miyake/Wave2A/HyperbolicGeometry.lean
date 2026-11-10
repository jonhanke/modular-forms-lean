import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.GaussBonnet
import TauCeti.Analysis.Complex.UpperHalfPlane.Bisector.Geometry
import ModularFormsKB.Citation
/-!
# Miyake §1.4: hyperbolic circles, bisectors and triangles

Miyake, *Modular Forms* (Springer 1989), §1.4, pp. 12–13, in the upper half plane model.

* Corollary 1.4.2 (1): the set of points at hyperbolic distance `r > 0` from `z₀` is a circle
  (Mathlib's `UpperHalfPlane.image_coe_sphere`: Euclidean centre `center z₀ r`, radius
  `Im z₀ · sinh r`) which is orthogonal to every geodesic through `z₀`
  (`ModularFormsKB.Miyake.sphere_orthogonal_geodesic`).
* Corollary 1.4.2 (2): the set of points equidistant from two distinct points is a geodesic
  (`ModularFormsKB.Miyake.setOf_dist_eq_eq_range_geodesicLine`, from Tau Ceti).
* Lemma 1.4.4: the hyperbolic area of a geodesic triangle with vertices in `ℍ ∪ ℝ ∪ {∞}` and
  angles `θ₁, θ₂, θ₃` is `π - (θ₁ + θ₂ + θ₃)`
  (`ModularFormsKB.Miyake.volume_triangle`), the case `n = 3` of Tau Ceti's Gauss–Bonnet formula
  `TauCeti.UpperHalfPlane.ConvexPolygon.volume_carrier`. The area is that of the closed triangle
  (Tau Ceti's `carrier`); its boundary has measure zero, so this is also the area of Miyake's
  open triangle `D`.

## Geodesics
The geodesics of `ℍ` (Miyake, Theorem 1.4.1) are the vertical half-lines `{Re z = a}` and the
semicircles `{|z - a| = s}`, `a ∈ ℝ`, `s > 0`, orthogonal to the real axis.
Two circles `|z - c₁| = ρ₁`, `|z - c₂| = ρ₂` meet orthogonally if and only if
`|c₁ - c₂|² = ρ₁² + ρ₂²`, and a circle is orthogonal to a line if and only if its centre lies
on the line; these are the conditions stated in Corollary 1.4.2 (1).
-/

open UpperHalfPlane Complex MeasureTheory
open scoped Real

namespace ModularFormsKB.Miyake

/-- **Miyake, Corollary 1.4.2 (1).** The hyperbolic circle of radius `r > 0` about `z₀` is the
Euclidean circle with centre `c = center z₀ r` and radius `ρ = Im z₀ · sinh r`; it is
orthogonal to every geodesic through `z₀`: the centre lies on the vertical geodesic through
`z₀`, and for every semicircular geodesic `|z - a| = s` through `z₀` one has
`|c - a|² = ρ² + s²`. -/
@[kb "miyake1989" "Corollary 1.4.2 (1), p. 12"]
theorem sphere_orthogonal_geodesic (z₀ : ℍ) {r : ℝ} (hr : 0 < r) :
    ((↑) '' Metric.sphere z₀ r = Metric.sphere ((center z₀ r : ℍ) : ℂ) (z₀.im * Real.sinh r)) ∧
      (center z₀ r).re = z₀.re ∧
      ∀ (a s : ℝ), dist (z₀ : ℂ) (a : ℂ) = s →
        dist ((center z₀ r : ℍ) : ℂ) (a : ℂ) ^ 2 = (z₀.im * Real.sinh r) ^ 2 + s ^ 2 := by
  refine ⟨image_coe_sphere z₀ r, center_re z₀ r, fun a s hs => ?_⟩
  rw [← hs, Complex.dist_eq, Complex.dist_eq, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, coe_re, coe_im, Complex.ofReal_re,
    Complex.ofReal_im, center_re, center_im, sub_zero]
  linear_combination z₀.im ^ 2 * Real.cosh_sq r

/-- **Miyake, Corollary 1.4.2 (2).** For distinct `z₁, z₂ ∈ ℍ`, the set of points of `ℍ`
equidistant from `z₁` and `z₂` is a geodesic, namely Tau Ceti's perpendicular bisector
`geodesicLine (perpBisector z₁ z₂)` (a geodesic of `ℍ` is a `PSL₂(ℝ)`-translate of the imaginary
axis). This is a restatement of Tau Ceti's
`TauCeti.UpperHalfPlane.mem_range_geodesicLine_perpBisector_iff`. -/
@[kb "miyake1989" "Corollary 1.4.2 (2), p. 12"]
theorem setOf_dist_eq_eq_range_geodesicLine {z₁ z₂ : ℍ} (h : z₁ ≠ z₂) :
    {z : ℍ | dist z z₁ = dist z z₂} =
      Set.range (TauCeti.UpperHalfPlane.geodesicLine (TauCeti.UpperHalfPlane.perpBisector z₁ z₂)) := by
  ext z
  rw [TauCeti.UpperHalfPlane.mem_range_geodesicLine_perpBisector_iff h]
  rfl

/-- **Miyake, Lemma 1.4.4.** The hyperbolic area of a geodesic triangle with vertices in
`ℍ ∪ ℝ ∪ {∞}` and interior angles `θ₁, θ₂, θ₃` (an ideal vertex has angle `0`) is
`π - (θ₁ + θ₂ + θ₃)`. -/
@[kb "miyake1989" "Lemma 1.4.4, p. 13"]
theorem volume_triangle (P : TauCeti.UpperHalfPlane.ConvexPolygon 3) :
    volume P.carrier = ENNReal.ofReal (π - (P.interiorAngle 0 + P.interiorAngle 1 +
      P.interiorAngle 2)) := by
  rw [P.volume_carrier, Fin.sum_univ_three]
  norm_num

end ModularFormsKB.Miyake
