import ModularFormsKB.Milne.Wave4B.HasseWeil
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Curve

/-!
# Milne wave 7: the geometric conductor exponent is `2` at a cusp when `p ≠ 2, 3`

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 11, the definition of the
geometric conductor (D116, pdf p. 111): $N = \prod_p p^{f_p}$ with $f_p = 0$ at good reduction, $f_p = 1$ at a node,
and "$f_p \ge 2$ if $E(p)$ has a cusp (with equality unless $p = 2, 3$)". Wave 4B proved the three cases
(`Wave4B.not_dvd_geometricConductor_iff`, `Wave4B.geometricConductor_exponent_eq_one_iff`,
`Wave4B.sq_dvd_geometricConductor_iff`); this file proves the parenthetical equality.

The exponent of the library's `Wave4B.geometricConductor` at `p` is Tau Ceti's algorithmic Ogg exponent
`v(Δ_min) - m + 1`, with `m` the number of components of the symbol at which Tate's algorithm stops
(`WeierstrassCurve.algorithmicOggExponent`). Tau Ceti proves `ϖ^(m+1) ∣ Δ` at every additive symbol
(`WeierstrassCurve.IsTateTerminal.pow_componentCount_add_one_dvd_Δ`). We prove the reverse bound
`¬ ϖ^(m+2) ∣ Δ` when `ϖ ∤ 2` and `ϖ ∤ 3` (`isTateTerminal_not_pow_componentCount_add_two_dvd_Δ`), so `v(Δ) = m + 1` and
the exponent is `2`.

**Proof.** Each stopping condition of Tate's algorithm (`WeierstrassCurve.IsTateTerminal`) gives the `ϖ`-adic
valuations of `a₁, …, a₆` (or of `b₂, b₆, b₈`) from below, and one of them exactly. Writing
`b_i = ϖ^{k_i} B_i`, the formula `Δ = -b₂²b₈ - 8b₄³ - 27b₆² + 9b₂b₄b₆` gives `Δ = ϖ^{m+1} Z`, and modulo `ϖ` the
cofactor `Z` is a product of `2`, `3` and a residue known to be nonzero:

| symbol | `m` | `Z mod ϖ` |
|---|---|---|
| `II` | 1 | `-432 A₆²` (`a₆ = ϖ A₆`) |
| `III` | 2 | `-8 B₄³` (`b₄ = ϖ B₄`, and `ϖ ∤ B₄` by `4b₈ = b₂b₆ - b₄²`) |
| `IV` | 3 | `-27 B₆²` (`b₆ = ϖ² B₆`) |
| `I₀*` | 5 | `16 disc(T³ + A₂T² + A₄T + A₆)` |
| `I*_{2k+1}` | `2k+6` | `-16 A₂³ B₆` (`a₂ = ϖ A₂`, `b₆ = ϖ^{2k+4} B₆`) |
| `I*_{2k+2}` | `2k+7` | `16 A₂² (A₄² - 4A₂A₆)` |
| `IV*` | 7 | `-27 B₆²` (`b₆ = ϖ⁴ B₆`) |
| `III*` | 8 | `-64 A₄³` (`a₄ = ϖ³ A₄`) |
| `II*` | 9 | `-432 A₆²` (`a₆ = ϖ⁵ A₆`) |

This is the tame case of Ogg's formula, checked directly on Tate's algorithm (Silverman, *Advanced Topics in the
Arithmetic of Elliptic Curves*, GTM 151, IV.9, Table 4.1, where `v(Δ) = m + 1` at every additive type for residue
characteristic at least `5`).
-/

open WeierstrassCurve TauCeti IsLocalRing IsDiscreteValuationRing IsDedekindDomain

namespace ModularFormsKB.Milne.Wave7

/-! ### Valuations in a domain -/

section Valuation

variable {R : Type*} [CommRing R] {ϖ : R}

/-- If `x = ϖⁿ Z` with `ϖ ∤ Z`, then `ϖⁿ⁺¹ ∤ x`. -/
theorem not_pow_succ_dvd_of_eq [IsDomain R] (hϖ : Prime ϖ) {x Z : R} {n : ℕ} (hx : x = ϖ ^ n * Z) (hZ : ¬ ϖ ∣ Z) :
    ¬ ϖ ^ (n + 1) ∣ x := by
  intro h
  rw [hx, pow_succ] at h
  exact hZ ((mul_dvd_mul_iff_left (pow_ne_zero n hϖ.ne_zero)).1 h)

/-- If `x = ϖⁿ A` and `ϖⁿ⁺¹ ∤ x`, then `ϖ ∤ A`. -/
theorem not_dvd_of_not_pow_succ_dvd {x A : R} {n : ℕ} (hx : x = ϖ ^ n * A) (h : ¬ ϖ ^ (n + 1) ∣ x) :
    ¬ ϖ ∣ A := by
  rintro ⟨c, rfl⟩
  exact h ⟨c, by rw [hx]; ring⟩

/-- Reduction modulo `(ϖ)`. -/
def modϖ (ϖ : R) : R →+* R ⧸ Ideal.span ({ϖ} : Set R) := Ideal.Quotient.mk _

/-- Divisibility by `ϖ` is vanishing in `R ⧸ (ϖ)`. -/
theorem dvd_iff_mk_eq_zero (x : R) : ϖ ∣ x ↔ modϖ ϖ x = 0 :=
  (Ideal.Quotient.eq_zero_iff_dvd ϖ x).symm

theorem mk_self_eq_zero : modϖ ϖ ϖ = 0 :=
  (dvd_iff_mk_eq_zero ϖ).1 dvd_rfl

/-- `ϖ ∤ 2ᵃ 3ᵇ` when `ϖ ∤ 2` and `ϖ ∤ 3`. -/
theorem not_dvd_two_pow_mul_three_pow (hϖ : Prime ϖ) (h2 : ¬ ϖ ∣ 2) (h3 : ¬ ϖ ∣ 3) (a b : ℕ) :
    ¬ ϖ ∣ (2 : R) ^ a * 3 ^ b := by
  intro h
  rcases hϖ.dvd_or_dvd h with h | h
  · exact h2 (hϖ.dvd_of_dvd_pow h)
  · exact h3 (hϖ.dvd_of_dvd_pow h)

/-- `ϖ ∤ u x` when `ϖ ∤ u` and `ϖ ∤ x`. -/
theorem not_dvd_mul (hϖ : Prime ϖ) {u x : R} (hu : ¬ ϖ ∣ u) (hx : ¬ ϖ ∣ x) : ¬ ϖ ∣ u * x := by
  intro h
  rcases hϖ.dvd_or_dvd h with h | h
  · exact hu h
  · exact hx h

/-- `ϖ ∤ xⁿ` when `ϖ ∤ x`. -/
theorem not_dvd_pow (hϖ : Prime ϖ) {x : R} (hx : ¬ ϖ ∣ x) (n : ℕ) : ¬ ϖ ∣ x ^ n :=
  fun h ↦ hx (hϖ.dvd_of_dvd_pow h)

end Valuation

/-! ### The discriminant at each additive stopping condition -/

section Terminal

variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {ϖ : R}

theorem Δ_eq_b (W : WeierstrassCurve R) :
    W.Δ = -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 + 9 * W.b₂ * W.b₄ * W.b₆ :=
  rfl

/-- Symbol `II`: `v(Δ) = 2`. -/
theorem not_dvd_Δ_II [IsDomain R] (hϖ : Prime ϖ) (h2 : ¬ ϖ ∣ 2) (h3 : ¬ ϖ ∣ 3) (h : W.IsTateTerminal ϖ .II) :
    ¬ ϖ ^ 3 ∣ W.Δ := by
  obtain ⟨⟨B2, hb2⟩, ⟨A3, h3a⟩, ⟨A4, h4a⟩, ⟨A6, h6a⟩, h6⟩ := h
  have hA6 : ¬ ϖ ∣ A6 := not_dvd_of_not_pow_succ_dvd (n := 1) (by rw [h6a, pow_one]) h6
  have hb4 : W.b₄ = ϖ * (2 * A4 + W.a₁ * A3) := by simp only [b₄]; rw [h3a, h4a]; ring
  have hb6 : W.b₆ = ϖ * (ϖ * A3 ^ 2 + 4 * A6) := by simp only [b₆]; rw [h3a, h6a]; ring
  have hb8 : W.b₈ = ϖ * (W.a₁ ^ 2 * A6 + 4 * W.a₂ * A6 - ϖ * W.a₁ * A3 * A4 + ϖ * W.a₂ * A3 ^ 2 -
      ϖ * A4 ^ 2) := by
    simp only [b₈]; rw [h3a, h4a, h6a]; ring
  refine not_pow_succ_dvd_of_eq (n := 2) hϖ (Z := ϖ * (-B2 ^ 2 * (W.a₁ ^ 2 * A6 + 4 * W.a₂ * A6 -
      ϖ * W.a₁ * A3 * A4 + ϖ * W.a₂ * A3 ^ 2 - ϖ * A4 ^ 2) - 8 * (2 * A4 + W.a₁ * A3) ^ 3 +
      9 * B2 * (2 * A4 + W.a₁ * A3) * (ϖ * A3 ^ 2 + 4 * A6)) - 27 * (ϖ * A3 ^ 2 + 4 * A6) ^ 2) ?_ ?_
  · rw [Δ_eq_b, hb2, hb4, hb6, hb8]; ring
  · rw [dvd_iff_mk_eq_zero]
    have e : modϖ ϖ (ϖ * (-B2 ^ 2 * (W.a₁ ^ 2 * A6 + 4 * W.a₂ * A6 -
        ϖ * W.a₁ * A3 * A4 + ϖ * W.a₂ * A3 ^ 2 - ϖ * A4 ^ 2) - 8 * (2 * A4 + W.a₁ * A3) ^ 3 +
        9 * B2 * (2 * A4 + W.a₁ * A3) * (ϖ * A3 ^ 2 + 4 * A6)) - 27 * (ϖ * A3 ^ 2 + 4 * A6) ^ 2) =
        modϖ ϖ (-((2 : R) ^ 4 * 3 ^ 3 * A6 ^ 2)) := by
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, mk_self_eq_zero, zero_mul,
        mul_zero, zero_add, add_zero, zero_sub, sub_zero]
      ring
    rw [e, ← dvd_iff_mk_eq_zero, dvd_neg]
    exact not_dvd_mul hϖ (not_dvd_two_pow_mul_three_pow hϖ h2 h3 4 3) (not_dvd_pow hϖ hA6 2)

/-- Symbol `III`: `v(Δ) = 3`. -/
theorem not_dvd_Δ_III [IsDomain R] (hϖ : Prime ϖ) (h2 : ¬ ϖ ∣ 2) (h3 : ¬ ϖ ∣ 3) (h : W.IsTateTerminal ϖ .III) :
    ¬ ϖ ^ 4 ∣ W.Δ := by
  obtain ⟨⟨B2, hb2⟩, ⟨A3, h3a⟩, ⟨A4, h4a⟩, ⟨A6, h6a⟩, h8⟩ := h
  have hb8 : W.b₈ = ϖ ^ 2 * (W.a₁ ^ 2 * A6 + 4 * W.a₂ * A6 - W.a₁ * A3 * A4 + W.a₂ * A3 ^ 2 - A4 ^ 2) := by
    simp only [b₈]; rw [h3a, h4a, h6a]; ring
  have hC8 := not_dvd_of_not_pow_succ_dvd hb8 h8
  set C8 := W.a₁ ^ 2 * A6 + 4 * W.a₂ * A6 - W.a₁ * A3 * A4 + W.a₂ * A3 ^ 2 - A4 ^ 2
  have hb4 : W.b₄ = ϖ * (2 * A4 + W.a₁ * A3) := by simp only [b₄]; rw [h3a, h4a]; ring
  set B4 := 2 * A4 + W.a₁ * A3
  have hb6 : W.b₆ = ϖ ^ 2 * (A3 ^ 2 + 4 * A6) := by simp only [b₆]; rw [h3a, h6a]; ring
  set B6 := A3 ^ 2 + 4 * A6
  -- `4 b₈ = b₂ b₆ - b₄²` gives `4 C₈ = ϖ B₂ B₆ - B₄²`, so `ϖ ∤ B₄`
  have hrel : ϖ ^ 2 * (4 * C8) = ϖ ^ 2 * (ϖ * B2 * B6 - B4 ^ 2) := by
    have := W.b_relation
    rw [hb2, hb4, hb6, hb8] at this
    linear_combination this
  have hrel' := mul_left_cancel₀ (pow_ne_zero 2 hϖ.ne_zero) hrel
  have hB4 : ¬ ϖ ∣ B4 := by
    intro hB4
    have : ϖ ∣ 4 * C8 := by
      rw [hrel']
      exact dvd_sub (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) (dvd_pow hB4 two_ne_zero)
    rcases hϖ.dvd_or_dvd this with h4 | h4
    · exact h2 (hϖ.dvd_of_dvd_pow (show ϖ ∣ (2 : R) ^ 2 by norm_num [h4]))
    · exact hC8 h4
  refine not_pow_succ_dvd_of_eq (n := 3) hϖ (Z := -8 * B4 ^ 3 + ϖ * (-B2 ^ 2 * C8 - 27 * B6 ^ 2 +
      9 * B2 * B4 * B6)) ?_ ?_
  · rw [Δ_eq_b, hb2, hb4, hb6, hb8]; ring
  · rw [dvd_iff_mk_eq_zero]
    have e : modϖ ϖ (-8 * B4 ^ 3 + ϖ * (-B2 ^ 2 * C8 - 27 * B6 ^ 2 + 9 * B2 * B4 * B6)) =
        modϖ ϖ (-((2 : R) ^ 3 * 3 ^ 0 * B4 ^ 3)) := by
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, mk_self_eq_zero, zero_mul,
        mul_zero, zero_add, add_zero, zero_sub, sub_zero]
      ring
    rw [e, ← dvd_iff_mk_eq_zero, dvd_neg]
    exact not_dvd_mul hϖ (not_dvd_two_pow_mul_three_pow hϖ h2 h3 3 0)
      (not_dvd_pow hϖ hB4 3)

/-- Symbol `IV`: `v(Δ) = 4`. -/
theorem not_dvd_Δ_IV [IsDomain R] (hϖ : Prime ϖ) (h2 : ¬ ϖ ∣ 2) (h3 : ¬ ϖ ∣ 3) (h : W.IsTateTerminal ϖ .IV) :
    ¬ ϖ ^ 5 ∣ W.Δ := by
  obtain ⟨⟨B2, hb2⟩, ⟨A3, h3a⟩, ⟨A4, h4a⟩, ⟨A6, h6a⟩, ⟨B8, hb8⟩, h6⟩ := h
  have hb6 : W.b₆ = ϖ ^ 2 * (A3 ^ 2 + 4 * A6) := by simp only [b₆]; rw [h3a, h6a]; ring
  have hB6 := not_dvd_of_not_pow_succ_dvd hb6 h6
  set B6 := A3 ^ 2 + 4 * A6
  have hb4 : W.b₄ = ϖ * (2 * A4 + W.a₁ * A3) := by simp only [b₄]; rw [h3a, h4a]; ring
  set B4 := 2 * A4 + W.a₁ * A3
  -- `4 b₈ = b₂ b₆ - b₄²` gives `B₄² = ϖ (B₂ B₆ - 4 B₈)`, so `ϖ ∣ B₄`
  have hrel : ϖ ^ 2 * B4 ^ 2 = ϖ ^ 2 * (ϖ * (B2 * B6 - 4 * B8)) := by
    have := W.b_relation
    rw [hb2, hb4, hb6, hb8] at this
    linear_combination this
  have hrel' := mul_left_cancel₀ (pow_ne_zero 2 hϖ.ne_zero) hrel
  obtain ⟨C4, hC4⟩ : ϖ ∣ B4 := hϖ.dvd_of_dvd_pow (n := 2) ⟨_, hrel'⟩
  have hb4' : W.b₄ = ϖ ^ 2 * C4 := by rw [hb4, hC4]; ring
  refine not_pow_succ_dvd_of_eq (n := 4) hϖ (Z := -27 * B6 ^ 2 + ϖ * (-B2 ^ 2 * B8 - 8 * ϖ * C4 ^ 3 +
      9 * B2 * C4 * B6)) ?_ ?_
  · rw [Δ_eq_b, hb2, hb4', hb6, hb8]; ring
  · rw [dvd_iff_mk_eq_zero]
    have e : modϖ ϖ (-27 * B6 ^ 2 + ϖ * (-B2 ^ 2 * B8 - 8 * ϖ * C4 ^ 3 + 9 * B2 * C4 * B6)) =
        modϖ ϖ (-((2 : R) ^ 0 * 3 ^ 3 * B6 ^ 2)) := by
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, mk_self_eq_zero, zero_mul,
        mul_zero, zero_add, add_zero, zero_sub, sub_zero]
      ring
    rw [e, ← dvd_iff_mk_eq_zero, dvd_neg]
    exact not_dvd_mul hϖ (not_dvd_two_pow_mul_three_pow hϖ h2 h3 0 3) (not_dvd_pow hϖ hB6 2)

/-- Symbol `I₀*`: `v(Δ) = 6`. -/
theorem not_dvd_Δ_IStar_zero [IsDomain R] (hϖ : Prime ϖ) (h2 : ¬ ϖ ∣ 2) (h3 : ¬ ϖ ∣ 3)
    (h : W.IsTateTerminal ϖ (.IStar 0)) : ¬ ϖ ^ 7 ∣ W.Δ := by
  obtain ⟨⟨A1, h1a⟩, ⟨A2, h2a⟩, ⟨A3, h3a⟩, ⟨A4, h4a⟩, ⟨A6, h6a⟩, hd⟩ := h
  have hdisc : (Cubic.mk 1 W.a₂ W.a₄ W.a₆).discr = ϖ ^ 6 * (A2 ^ 2 * A4 ^ 2 - 4 * A4 ^ 3 - 4 * A2 ^ 3 * A6 -
      27 * A6 ^ 2 + 18 * A2 * A4 * A6) := by
    simp only [Cubic.discr]; rw [h2a, h4a, h6a]; ring
  have hD := not_dvd_of_not_pow_succ_dvd hdisc hd
  set D := A2 ^ 2 * A4 ^ 2 - 4 * A4 ^ 3 - 4 * A2 ^ 3 * A6 - 27 * A6 ^ 2 + 18 * A2 * A4 * A6
  have hb2 : W.b₂ = ϖ * (ϖ * A1 ^ 2 + 4 * A2) := by simp only [b₂]; rw [h1a, h2a]; ring
  have hb4 : W.b₄ = ϖ ^ 2 * (2 * A4 + ϖ * A1 * A3) := by simp only [b₄]; rw [h1a, h3a, h4a]; ring
  have hb6 : W.b₆ = ϖ ^ 3 * (ϖ * A3 ^ 2 + 4 * A6) := by simp only [b₆]; rw [h3a, h6a]; ring
  have hb8 : W.b₈ = ϖ ^ 4 * (ϖ * A1 ^ 2 * A6 + 4 * A2 * A6 - ϖ * A1 * A3 * A4 + ϖ * A2 * A3 ^ 2 -
      A4 ^ 2) := by
    simp only [b₈]; rw [h1a, h2a, h3a, h4a, h6a]; ring
  set B2 := ϖ * A1 ^ 2 + 4 * A2
  set B4 := 2 * A4 + ϖ * A1 * A3
  set B6 := ϖ * A3 ^ 2 + 4 * A6
  set B8 := ϖ * A1 ^ 2 * A6 + 4 * A2 * A6 - ϖ * A1 * A3 * A4 + ϖ * A2 * A3 ^ 2 - A4 ^ 2
  refine not_pow_succ_dvd_of_eq (n := 6) hϖ (Z := -B2 ^ 2 * B8 - 8 * B4 ^ 3 - 27 * B6 ^ 2 +
      9 * B2 * B4 * B6) ?_ ?_
  · rw [Δ_eq_b, hb2, hb4, hb6, hb8]; ring
  · rw [dvd_iff_mk_eq_zero]
    have e : modϖ ϖ (-B2 ^ 2 * B8 - 8 * B4 ^ 3 - 27 * B6 ^ 2 + 9 * B2 * B4 * B6) =
        modϖ ϖ ((2 : R) ^ 4 * 3 ^ 0 * D) := by
      simp only [B2, B4, B6, B8, D, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
        mk_self_eq_zero, zero_mul, mul_zero, zero_add, add_zero, zero_sub, sub_zero]
      ring
    rw [e, ← dvd_iff_mk_eq_zero]
    exact not_dvd_mul hϖ (not_dvd_two_pow_mul_three_pow hϖ h2 h3 4 0) hD

/-- Symbol `I*_{2k+1}` (odd stage `k` of the subprocedure): `v(Δ) = 2k + 7`. -/
theorem not_dvd_Δ_IStar_odd [IsDomain R] (hϖ : Prime ϖ) (h2 : ¬ ϖ ∣ 2) (h3 : ¬ ϖ ∣ 3) {k : ℕ}
    (hk : WeierstrassCurve.IsTateOddStage ϖ k W) (h6 : ¬ ϖ ^ (2 * k + 5) ∣ W.b₆) :
    ¬ ϖ ^ (2 * k + 8) ∣ W.Δ := by
  obtain ⟨⟨A1, h1a⟩, ⟨A2, h2a⟩, h2', ⟨A3, h3a⟩, ⟨A4, h4a⟩, ⟨A6, h6a⟩⟩ := isTateOddStage_iff.1 hk
  have hA2 : ¬ ϖ ∣ A2 := not_dvd_of_not_pow_succ_dvd (n := 1) (by rw [h2a, pow_one]) h2'
  have hb6 : W.b₆ = ϖ ^ (2 * k + 4) * (A3 ^ 2 + 4 * A6) := by simp only [b₆]; rw [h3a, h6a]; ring
  have hB6 := not_dvd_of_not_pow_succ_dvd hb6 h6
  set B6 := A3 ^ 2 + 4 * A6
  have hb2 : W.b₂ = ϖ * (ϖ * A1 ^ 2 + 4 * A2) := by simp only [b₂]; rw [h1a, h2a]; ring
  have hb4 : W.b₄ = ϖ ^ (k + 3) * (2 * A4 + A1 * A3) := by simp only [b₄]; rw [h1a, h3a, h4a]; ring
  have hb8 : W.b₈ = ϖ ^ (2 * k + 5) * (A2 * B6 + ϖ * (A1 ^ 2 * A6 - A1 * A3 * A4 - A4 ^ 2)) := by
    simp only [b₈, B6]; rw [h1a, h2a, h3a, h4a, h6a]; ring
  set B2 := ϖ * A1 ^ 2 + 4 * A2
  set B4 := 2 * A4 + A1 * A3
  set B8 := A2 * B6 + ϖ * (A1 ^ 2 * A6 - A1 * A3 * A4 - A4 ^ 2)
  refine not_pow_succ_dvd_of_eq (n := 2 * k + 7) hϖ (Z := -B2 ^ 2 * B8 -
      ϖ * (8 * ϖ ^ (k + 1) * B4 ^ 3 + 27 * ϖ ^ (2 * k) * B6 ^ 2 - 9 * ϖ ^ k * B2 * B4 * B6)) ?_ ?_
  · rw [Δ_eq_b, hb2, hb4, hb6, hb8]; ring
  · rw [dvd_iff_mk_eq_zero]
    have e : modϖ ϖ (-B2 ^ 2 * B8 - ϖ * (8 * ϖ ^ (k + 1) * B4 ^ 3 + 27 * ϖ ^ (2 * k) * B6 ^ 2 -
        9 * ϖ ^ k * B2 * B4 * B6)) = modϖ ϖ (-((2 : R) ^ 4 * 3 ^ 0 * (A2 ^ 3 * B6))) := by
      simp only [B2, B8, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, mk_self_eq_zero,
        zero_mul, mul_zero, zero_add, add_zero, zero_sub, sub_zero]
      ring
    rw [e, ← dvd_iff_mk_eq_zero, dvd_neg]
    exact not_dvd_mul hϖ (not_dvd_two_pow_mul_three_pow hϖ h2 h3 4 0)
      (not_dvd_mul hϖ (not_dvd_pow hϖ hA2 3) hB6)

/-- Symbol `I*_{2k+2}` (even stage `k` of the subprocedure): `v(Δ) = 2k + 8`. -/
theorem not_dvd_Δ_IStar_even [IsDomain R] (hϖ : Prime ϖ) (h2 : ¬ ϖ ∣ 2) (h3 : ¬ ϖ ∣ 3) {k : ℕ}
    (hk : WeierstrassCurve.IsTateEvenStage ϖ k W) (hd : ¬ ϖ ^ (2 * k + 7) ∣ discrim W.a₂ W.a₄ W.a₆) :
    ¬ ϖ ^ (2 * k + 9) ∣ W.Δ := by
  obtain ⟨⟨A1, h1a⟩, ⟨A2, h2a⟩, h2', ⟨A3, h3a⟩, ⟨A4, h4a⟩, ⟨A6, h6a⟩⟩ := isTateEvenStage_iff.1 hk
  have hA2 : ¬ ϖ ∣ A2 := not_dvd_of_not_pow_succ_dvd (n := 1) (by rw [h2a, pow_one]) h2'
  have hdisc : discrim W.a₂ W.a₄ W.a₆ = ϖ ^ (2 * k + 6) * (A4 ^ 2 - 4 * A2 * A6) := by
    simp only [discrim]; rw [h2a, h4a, h6a]; ring
  have hD := not_dvd_of_not_pow_succ_dvd hdisc hd
  set D := A4 ^ 2 - 4 * A2 * A6
  have hb2 : W.b₂ = ϖ * (ϖ * A1 ^ 2 + 4 * A2) := by simp only [b₂]; rw [h1a, h2a]; ring
  have hb4 : W.b₄ = ϖ ^ (k + 3) * (2 * A4 + ϖ * A1 * A3) := by simp only [b₄]; rw [h1a, h3a, h4a]; ring
  have hb6 : W.b₆ = ϖ ^ (2 * k + 5) * (ϖ * A3 ^ 2 + 4 * A6) := by simp only [b₆]; rw [h3a, h6a]; ring
  have hb8 : W.b₈ = ϖ ^ (2 * k + 6) * (-D + ϖ * (A1 ^ 2 * A6 - A1 * A3 * A4 + A2 * A3 ^ 2)) := by
    simp only [b₈, D]; rw [h1a, h2a, h3a, h4a, h6a]; ring
  set B2 := ϖ * A1 ^ 2 + 4 * A2
  set B4 := 2 * A4 + ϖ * A1 * A3
  set B6 := ϖ * A3 ^ 2 + 4 * A6
  set B8 := -D + ϖ * (A1 ^ 2 * A6 - A1 * A3 * A4 + A2 * A3 ^ 2)
  refine not_pow_succ_dvd_of_eq (n := 2 * k + 8) hϖ (Z := -B2 ^ 2 * B8 -
      ϖ * (8 * ϖ ^ k * B4 ^ 3 + 27 * ϖ ^ (2 * k + 1) * B6 ^ 2 - 9 * ϖ ^ k * B2 * B4 * B6)) ?_ ?_
  · rw [Δ_eq_b, hb2, hb4, hb6, hb8]; ring
  · rw [dvd_iff_mk_eq_zero]
    have e : modϖ ϖ (-B2 ^ 2 * B8 - ϖ * (8 * ϖ ^ k * B4 ^ 3 + 27 * ϖ ^ (2 * k + 1) * B6 ^ 2 -
        9 * ϖ ^ k * B2 * B4 * B6)) = modϖ ϖ ((2 : R) ^ 4 * 3 ^ 0 * (A2 ^ 2 * D)) := by
      simp only [B2, B8, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, mk_self_eq_zero,
        zero_mul, mul_zero, zero_add, add_zero, zero_sub, sub_zero]
      ring
    rw [e, ← dvd_iff_mk_eq_zero]
    exact not_dvd_mul hϖ (not_dvd_two_pow_mul_three_pow hϖ h2 h3 4 0)
      (not_dvd_mul hϖ (not_dvd_pow hϖ hA2 2) hD)

/-- Symbol `IV*`: `v(Δ) = 8`. -/
theorem not_dvd_Δ_IVStar [IsDomain R] (hϖ : Prime ϖ) (h2 : ¬ ϖ ∣ 2) (h3 : ¬ ϖ ∣ 3) (h : W.IsTateTerminal ϖ .IVStar) :
    ¬ ϖ ^ 9 ∣ W.Δ := by
  obtain ⟨⟨A1, h1a⟩, ⟨A2, h2a⟩, ⟨A3, h3a⟩, ⟨A4, h4a⟩, ⟨A6, h6a⟩, h6⟩ := h
  have hb6 : W.b₆ = ϖ ^ 4 * (A3 ^ 2 + 4 * A6) := by simp only [b₆]; rw [h3a, h6a]; ring
  have hB6 := not_dvd_of_not_pow_succ_dvd hb6 h6
  set B6 := A3 ^ 2 + 4 * A6
  have hb2 : W.b₂ = ϖ ^ 2 * (A1 ^ 2 + 4 * A2) := by simp only [b₂]; rw [h1a, h2a]; ring
  have hb4 : W.b₄ = ϖ ^ 3 * (2 * A4 + A1 * A3) := by simp only [b₄]; rw [h1a, h3a, h4a]; ring
  have hb8 : W.b₈ = ϖ ^ 6 * (A1 ^ 2 * A6 + 4 * A2 * A6 - A1 * A3 * A4 + A2 * A3 ^ 2 - A4 ^ 2) := by
    simp only [b₈]; rw [h1a, h2a, h3a, h4a, h6a]; ring
  set B2 := A1 ^ 2 + 4 * A2
  set B4 := 2 * A4 + A1 * A3
  set B8 := A1 ^ 2 * A6 + 4 * A2 * A6 - A1 * A3 * A4 + A2 * A3 ^ 2 - A4 ^ 2
  refine not_pow_succ_dvd_of_eq (n := 8) hϖ (Z := -27 * B6 ^ 2 + ϖ * (-ϖ * B2 ^ 2 * B8 - 8 * B4 ^ 3 +
      9 * B2 * B4 * B6)) ?_ ?_
  · rw [Δ_eq_b, hb2, hb4, hb6, hb8]; ring
  · rw [dvd_iff_mk_eq_zero]
    have e : modϖ ϖ (-27 * B6 ^ 2 + ϖ * (-ϖ * B2 ^ 2 * B8 - 8 * B4 ^ 3 + 9 * B2 * B4 * B6)) =
        modϖ ϖ (-((2 : R) ^ 0 * 3 ^ 3 * B6 ^ 2)) := by
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, mk_self_eq_zero, zero_mul,
        mul_zero, zero_add, add_zero, zero_sub, sub_zero, neg_zero]
      ring
    rw [e, ← dvd_iff_mk_eq_zero, dvd_neg]
    exact not_dvd_mul hϖ (not_dvd_two_pow_mul_three_pow hϖ h2 h3 0 3) (not_dvd_pow hϖ hB6 2)

/-- Symbol `III*`: `v(Δ) = 9`. -/
theorem not_dvd_Δ_IIIStar [IsDomain R] (hϖ : Prime ϖ) (h2 : ¬ ϖ ∣ 2) (h3 : ¬ ϖ ∣ 3)
    (h : W.IsTateTerminal ϖ .IIIStar) : ¬ ϖ ^ 10 ∣ W.Δ := by
  obtain ⟨⟨A1, h1a⟩, ⟨A2, h2a⟩, ⟨A3, h3a⟩, ⟨A4, h4a⟩, ⟨A6, h6a⟩, h4⟩ := h
  have hA4 : ¬ ϖ ∣ A4 := not_dvd_of_not_pow_succ_dvd h4a h4
  have hb2 : W.b₂ = ϖ ^ 2 * (A1 ^ 2 + 4 * A2) := by simp only [b₂]; rw [h1a, h2a]; ring
  have hb4 : W.b₄ = ϖ ^ 3 * (2 * A4 + ϖ * A1 * A3) := by simp only [b₄]; rw [h1a, h3a, h4a]; ring
  have hb6 : W.b₆ = ϖ ^ 5 * (ϖ * A3 ^ 2 + 4 * A6) := by simp only [b₆]; rw [h3a, h6a]; ring
  have hb8 : W.b₈ = ϖ ^ 6 * (ϖ * A1 ^ 2 * A6 + 4 * ϖ * A2 * A6 - ϖ * A1 * A3 * A4 +
      ϖ ^ 2 * A2 * A3 ^ 2 - A4 ^ 2) := by
    simp only [b₈]; rw [h1a, h2a, h3a, h4a, h6a]; ring
  set B2 := A1 ^ 2 + 4 * A2
  set B4 := 2 * A4 + ϖ * A1 * A3
  set B6 := ϖ * A3 ^ 2 + 4 * A6
  set B8 := ϖ * A1 ^ 2 * A6 + 4 * ϖ * A2 * A6 - ϖ * A1 * A3 * A4 + ϖ ^ 2 * A2 * A3 ^ 2 - A4 ^ 2
  refine not_pow_succ_dvd_of_eq (n := 9) hϖ (Z := -8 * B4 ^ 3 + ϖ * (-B2 ^ 2 * B8 - 27 * B6 ^ 2 +
      9 * B2 * B4 * B6)) ?_ ?_
  · rw [Δ_eq_b, hb2, hb4, hb6, hb8]; ring
  · rw [dvd_iff_mk_eq_zero]
    have e : modϖ ϖ (-8 * B4 ^ 3 + ϖ * (-B2 ^ 2 * B8 - 27 * B6 ^ 2 + 9 * B2 * B4 * B6)) =
        modϖ ϖ (-((2 : R) ^ 6 * 3 ^ 0 * A4 ^ 3)) := by
      simp only [B4, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, mk_self_eq_zero,
        zero_mul, mul_zero, zero_add, add_zero, zero_sub, sub_zero]
      ring
    rw [e, ← dvd_iff_mk_eq_zero, dvd_neg]
    exact not_dvd_mul hϖ (not_dvd_two_pow_mul_three_pow hϖ h2 h3 6 0) (not_dvd_pow hϖ hA4 3)

/-- Symbol `II*`: `v(Δ) = 10`. -/
theorem not_dvd_Δ_IIStar [IsDomain R] (hϖ : Prime ϖ) (h2 : ¬ ϖ ∣ 2) (h3 : ¬ ϖ ∣ 3) (h : W.IsTateTerminal ϖ .IIStar) :
    ¬ ϖ ^ 11 ∣ W.Δ := by
  obtain ⟨⟨A1, h1a⟩, ⟨A2, h2a⟩, ⟨A3, h3a⟩, ⟨A4, h4a⟩, ⟨A6, h6a⟩, h6⟩ := h
  have hA6 : ¬ ϖ ∣ A6 := not_dvd_of_not_pow_succ_dvd h6a h6
  have hb2 : W.b₂ = ϖ ^ 2 * (A1 ^ 2 + 4 * A2) := by simp only [b₂]; rw [h1a, h2a]; ring
  have hb4 : W.b₄ = ϖ ^ 4 * (2 * A4 + A1 * A3) := by simp only [b₄]; rw [h1a, h3a, h4a]; ring
  have hb6 : W.b₆ = ϖ ^ 5 * (ϖ * A3 ^ 2 + 4 * A6) := by simp only [b₆]; rw [h3a, h6a]; ring
  have hb8 : W.b₈ = ϖ ^ 7 * (A1 ^ 2 * A6 + 4 * A2 * A6 - ϖ * A1 * A3 * A4 + ϖ * A2 * A3 ^ 2 -
      ϖ * A4 ^ 2) := by
    simp only [b₈]; rw [h1a, h2a, h3a, h4a, h6a]; ring
  set B2 := A1 ^ 2 + 4 * A2
  set B4 := 2 * A4 + A1 * A3
  set B6 := ϖ * A3 ^ 2 + 4 * A6
  set B8 := A1 ^ 2 * A6 + 4 * A2 * A6 - ϖ * A1 * A3 * A4 + ϖ * A2 * A3 ^ 2 - ϖ * A4 ^ 2
  refine not_pow_succ_dvd_of_eq (n := 10) hϖ (Z := -27 * B6 ^ 2 + ϖ * (-B2 ^ 2 * B8 - 8 * ϖ * B4 ^ 3 +
      9 * B2 * B4 * B6)) ?_ ?_
  · rw [Δ_eq_b, hb2, hb4, hb6, hb8]; ring
  · rw [dvd_iff_mk_eq_zero]
    have e : modϖ ϖ (-27 * B6 ^ 2 + ϖ * (-B2 ^ 2 * B8 - 8 * ϖ * B4 ^ 3 + 9 * B2 * B4 * B6)) =
        modϖ ϖ (-((2 : R) ^ 4 * 3 ^ 3 * A6 ^ 2)) := by
      simp only [B6, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, mk_self_eq_zero,
        zero_mul, mul_zero, zero_add, add_zero, zero_sub, sub_zero]
      ring
    rw [e, ← dvd_iff_mk_eq_zero, dvd_neg]
    exact not_dvd_mul hϖ (not_dvd_two_pow_mul_three_pow hϖ h2 h3 4 3) (not_dvd_pow hϖ hA6 2)

/-- **`v(Δ) ≤ m + 1` at every additive symbol, away from `2` and `3`.** If Tate's algorithm stops on `W` at a symbol
`s` other than the `Iₙ`, with `m` components, and the uniformizer divides neither `2` nor `3`, then `ϖ^(m+2) ∤ Δ`.
With Tau Ceti's `ϖ^(m+1) ∣ Δ` (`IsTateTerminal.pow_componentCount_add_one_dvd_Δ`) this gives `v(Δ) = m + 1`. -/
theorem isTateTerminal_not_pow_componentCount_add_two_dvd_Δ [IsDomain R] (hϖ : Prime ϖ) (h2 : ¬ ϖ ∣ 2)
    (h3 : ¬ ϖ ∣ 3) {s : ReductionSymbol} (h : W.IsTateTerminal ϖ s) (hs : ∀ n, s ≠ .I n) :
    ¬ ϖ ^ (s.componentCount + 2) ∣ W.Δ := by
  match s, h with
  | .I n, _ => exact absurd rfl (hs n)
  | .II, h => exact not_dvd_Δ_II hϖ h2 h3 h
  | .III, h => exact not_dvd_Δ_III hϖ h2 h3 h
  | .IV, h => exact not_dvd_Δ_IV hϖ h2 h3 h
  | .IStar 0, h => exact not_dvd_Δ_IStar_zero hϖ h2 h3 h
  | .IStar (n + 1), h =>
    rcases isTateTerminal_IStar_add_one.1 h with ⟨k, rfl, hk, h6⟩ | ⟨k, rfl, hk, hd⟩
    · rw [ReductionSymbol.componentCount_IStar, show 2 * k + 1 + 5 + 2 = 2 * k + 8 by omega]
      exact not_dvd_Δ_IStar_odd hϖ h2 h3 hk h6
    · rw [ReductionSymbol.componentCount_IStar, show 2 * k + 1 + 1 + 5 + 2 = 2 * k + 9 by omega]
      exact not_dvd_Δ_IStar_even hϖ h2 h3 hk hd
  | .IVStar, h => exact not_dvd_Δ_IVStar hϖ h2 h3 h
  | .IIIStar, h => exact not_dvd_Δ_IIIStar hϖ h2 h3 h
  | .IIStar, h => exact not_dvd_Δ_IIStar hϖ h2 h3 h

end Terminal

/-! ### The algorithmic Ogg exponent over a discrete valuation ring -/

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [PerfectField (ResidueField R)]

/-- **Ogg's formula in the tame case, read off Tate's algorithm.** Over a discrete valuation ring in which `2` and
`3` are units, an elliptic curve with additive reduction has algorithmic Ogg exponent `2`. -/
theorem algorithmicOggExponent_eq_two (W : WeierstrassCurve K) [W.IsElliptic] (h2 : IsUnit (2 : R))
    (h3 : IsUnit (3 : R)) (hW : (W.minimal R).HasAdditiveReduction R) :
    W.algorithmicOggExponent R = 2 := by
  obtain ⟨W', D, ϖ, hmin, hD, hϖ, h⟩ := W.exists_isTateTerminal_reductionSymbol R
  have hs : ∀ n, W.reductionSymbol R ≠ .I n := (forall_reductionSymbol_ne_I_iff W).2 hW
  have hnd2 : ¬ ϖ ∣ 2 := fun hd ↦ hϖ.not_isUnit (isUnit_of_dvd_unit hd h2)
  have hnd3 : ¬ ϖ ∣ 3 := fun hd ↦ hϖ.not_isUnit (isUnit_of_dvd_unit hd h3)
  set m := (W.reductionSymbol R).componentCount
  have hup := h.pow_componentCount_add_one_dvd_Δ hϖ.prime hs
  have hlow := isTateTerminal_not_pow_componentCount_add_two_dvd_Δ hϖ.prime hnd2 hnd3 h hs
  have hv := W.localMinimalDiscriminantValuation_eq_addVal_of_isMinimal_baseChange R D hD
  have h1 : ((m + 1 : ℕ) : ℕ∞) ≤ addVal R W'.Δ := by
    rw [← hϖ.addVal_pow]; exact addVal_le_iff_dvd.2 hup
  have h2' : ¬ ((m + 2 : ℕ) : ℕ∞) ≤ addVal R W'.Δ := by
    rw [← hϖ.addVal_pow]; exact fun hle ↦ hlow (addVal_le_iff_dvd.1 hle)
  rw [← hv] at h1 h2'
  have hm : W.localMinimalDiscriminantValuation R = m + 1 := by
    have a := ENat.natCast_le_natCast.1 h1
    have b : ¬ m + 2 ≤ W.localMinimalDiscriminantValuation R := fun hh ↦ h2' (ENat.natCast_le_natCast.2 hh)
    omega
  have := natCast_algorithmicOggExponent (R := R) W
  rw [ReductionSymbol.algorithmicOggExponent_eq, hm] at this
  push_cast at this
  omega

end DVR

/-! ### D116: Milne's "with equality unless `p = 2, 3`" -/

/-- In `ℤ_(p)` an integer prime to `p` is a unit. -/
theorem isUnit_natCast_localization {p : ℕ} {v : HeightOneSpectrum ℤ} (hv : v.asIdeal = Ideal.span {(p : ℤ)})
    {a : ℕ} (ha : ¬ (p : ℤ) ∣ a) : IsUnit (a : Localization.AtPrime v.asIdeal) := by
  have := (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime v.asIdeal) v.asIdeal (a : ℤ)).2
    (by rw [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff, SetLike.mem_coe, hv,
      Ideal.mem_span_singleton]; exact ha)
  simpa using this

/-- **D116, the cusp case with equality** (Milne, p. 111: "$f_p \ge 2$ if $E(p)$ has a cusp (with equality unless
$p = 2, 3$)"): for a prime $p \ne 2, 3$, the exponent of $p$ in the geometric conductor is exactly $2$ when a minimal
model of $E$ at $p$ has additive reduction: $p^2 \mid N$ and $p^3 \nmid N$. -/
@[kb "milne2017mf" "Section 11, geometric conductor, D116 (pdf p. 111): f_p = 2 at a cusp for p ≠ 2, 3"]
theorem geometricConductor_exponent_eq_two (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {v : HeightOneSpectrum ℤ} (hv : v.asIdeal = Ideal.span {(p : ℤ)})
    (hE : (E.minimal (Localization.AtPrime v.asIdeal)).HasAdditiveReduction (Localization.AtPrime v.asIdeal)) :
    p ^ 2 ∣ Wave4B.geometricConductor E ∧ ¬ p ^ 3 ∣ Wave4B.geometricConductor E := by
  have hnd : ∀ q : ℕ, q.Prime → q ≠ p → ¬ (p : ℤ) ∣ q := by
    intro q hq hqp hd
    have := (Nat.prime_dvd_prime_iff_eq hp hq).1 (Int.natCast_dvd_natCast.1 hd)
    exact hqp this.symm
  have h2 : IsUnit (2 : Localization.AtPrime v.asIdeal) := by
    simpa using isUnit_natCast_localization hv (hnd 2 Nat.prime_two (Ne.symm hp2))
  have h3 : IsUnit (3 : Localization.AtPrime v.asIdeal) := by
    simpa using isUnit_natCast_localization hv (hnd 3 Nat.prime_three (Ne.symm hp3))
  have hf := algorithmicOggExponent_eq_two (R := Localization.AtPrime v.asIdeal) E h2 h3 hE
  rw [Wave4B.pow_dvd_geometricConductor_iff E hv, Wave4B.pow_dvd_geometricConductor_iff E hv, hf]
  omega

/-- **D116 at a prime $p \ne 2, 3$**: the exponent is exactly $2$ if and only if the reduction has a cusp. -/
@[kb "milne2017mf" "Section 11, geometric conductor, D116 (pdf p. 111): f_p = 2 iff cusp, for p ≠ 2, 3"]
theorem geometricConductor_exponent_eq_two_iff (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {v : HeightOneSpectrum ℤ} (hv : v.asIdeal = Ideal.span {(p : ℤ)}) :
    (p ^ 2 ∣ Wave4B.geometricConductor E ∧ ¬ p ^ 3 ∣ Wave4B.geometricConductor E) ↔
      (E.minimal (Localization.AtPrime v.asIdeal)).HasAdditiveReduction (Localization.AtPrime v.asIdeal) :=
  ⟨fun h ↦ (Wave4B.sq_dvd_geometricConductor_iff E hv).1 h.1,
    geometricConductor_exponent_eq_two E hp hp2 hp3 hv⟩

end ModularFormsKB.Milne.Wave7
