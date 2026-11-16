import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import ModularFormsKB.Citation
/-!
# Jacobi's multipliers of the transformations of orders 3 and 5

Jacobi, *Fundamenta nova* (1829), § 34 (restating §§ 13–16), pp. 81–82. With `u = k^{1/4}`, `v = λ^{1/4}` the
modular equations of orders `3` and `5` are

  `u⁴ - v⁴ + 2uv(1 - u²v²) = 0`,  `u⁶ - v⁶ + 5u²v²(u² - v²) + 4uv(1 - u⁴v⁴) = 0`,

and Jacobi rewrites them as

  `((v + 2u³)/v) ((u - 2v³)/u) = -3`,  `((u + v⁵)/(u(1 + u³v))) ((v - u⁵)/(v(1 - uv³))) = 5`,

so that the multipliers are `M = v/(v + 2u³) = (2v³ - u)/(3u)` and
`M = v(1 - uv³)/(v - u⁵) = (u + v⁵)/(5u(1 + u³v))`.

These are identities of rational functions, stated over any field of characteristic `0` (in particular for real
`u`, `v`) whenever the denominators are non-zero; in characteristic `2` the first equivalence fails. The link of `u`, `v` with the moduli `k`, `λ` of a
transformation is not used.
-/

namespace ModularFormsKB.Historical.Jacobi

variable {F : Type*} [Field F] [CharZero F]

/-- Jacobi's modular equation of order `3` in `u = k^{1/4}`, `v = λ^{1/4}`. -/
def modEqThree (u v : F) : F := u ^ 4 - v ^ 4 + 2 * u * v * (1 - u ^ 2 * v ^ 2)

/-- Jacobi's modular equation of order `5` in `u = k^{1/4}`, `v = λ^{1/4}`. -/
def modEqFive (u v : F) : F :=
  u ^ 6 - v ^ 6 + 5 * u ^ 2 * v ^ 2 * (u ^ 2 - v ^ 2) + 4 * u * v * (1 - u ^ 4 * v ^ 4)

/-- **Jacobi, order 3** (*Fundamenta nova*, § 34, p. 81): for `u, v ≠ 0`, the modular
equation of order `3` is equivalent to `((v + 2u³)/v)((u - 2v³)/u) = -3`; when it holds and `v + 2u³ ≠ 0`, the
two expressions of the multiplier agree: `v/(v + 2u³) = (2v³ - u)/(3u)`. -/
@[kb "jacobi1829" "§ 34, p. 81"]
theorem jacobiMultiplierThree {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) :
    (modEqThree u v = 0 ↔ (v + 2 * u ^ 3) / v * ((u - 2 * v ^ 3) / u) = -3) ∧
      (modEqThree u v = 0 → v + 2 * u ^ 3 ≠ 0 →
        v / (v + 2 * u ^ 3) = (2 * v ^ 3 - u) / (3 * u)) := by
  have key : (v + 2 * u ^ 3) * (u - 2 * v ^ 3) + 3 * (u * v) = 2 * modEqThree u v := by
    unfold modEqThree; ring
  refine ⟨⟨fun h ↦ ?_, fun h ↦ ?_⟩, fun h hd ↦ ?_⟩
  · rw [h, mul_zero] at key
    field_simp
    linear_combination key
  · field_simp at h
    have h2 : (2 : F) * modEqThree u v = 0 := by linear_combination -key + h
    exact (mul_eq_zero.1 h2).resolve_left (by norm_num)
  · rw [h, mul_zero] at key
    rw [div_eq_div_iff hd (mul_ne_zero (by norm_num) hu)]
    unfold modEqThree at h; linear_combination 2 * h

/-- **Jacobi, order 5** (*Fundamenta nova*, § 34, p. 82): for `u, v ≠ 0`,
`1 + u³v ≠ 0`, `1 - uv³ ≠ 0`, the modular equation of order `5` is equivalent to
`((u + v⁵)/(u(1 + u³v)))((v - u⁵)/(v(1 - uv³))) = 5`; when it holds and `v - u⁵ ≠ 0`, the two expressions of
the multiplier agree: `v(1 - uv³)/(v - u⁵) = (u + v⁵)/(5u(1 + u³v))`. -/
@[kb "jacobi1829" "§ 34, p. 82"]
theorem jacobiMultiplierFive {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (h1 : 1 + u ^ 3 * v ≠ 0)
    (h2 : 1 - u * v ^ 3 ≠ 0) :
    (modEqFive u v = 0 ↔
        (u + v ^ 5) / (u * (1 + u ^ 3 * v)) * ((v - u ^ 5) / (v * (1 - u * v ^ 3))) = 5) ∧
      (modEqFive u v = 0 → v - u ^ 5 ≠ 0 →
        v * (1 - u * v ^ 3) / (v - u ^ 5) = (u + v ^ 5) / (5 * u * (1 + u ^ 3 * v))) := by
  have key : (u + v ^ 5) * (v - u ^ 5) - 5 * (u * (1 + u ^ 3 * v)) * (v * (1 - u * v ^ 3)) =
      -modEqFive u v := by
    unfold modEqFive; ring
  refine ⟨⟨fun h ↦ ?_, fun h ↦ ?_⟩, fun h hd ↦ ?_⟩
  · rw [h, neg_zero] at key
    field_simp
    linear_combination key
  · field_simp at h
    linear_combination key - h
  · rw [h, neg_zero] at key
    rw [div_eq_div_iff hd (mul_ne_zero (mul_ne_zero (by norm_num) hu) h1)]
    unfold modEqFive at h; linear_combination h

end ModularFormsKB.Historical.Jacobi
