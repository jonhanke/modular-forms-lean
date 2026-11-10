import ModularFormsKB.Milne.Ch4.Unfolding
import ModularFormsKB.Citation
/-!
# Miyake §2.6: Poincaré series for modular groups (specializations)

Miyake, *Modular Forms* (Springer 1989), §2.6, pp. 64–68, Theorems 2.6.6, 2.6.9, 2.6.10 and
Corollary 2.6.11, in the special case available in this library:

* `Γ` a modular group (a finite-index subgroup of `SL₂(ℤ)`), the cusp `x = ∞`, `σ = 1`;
* trivial character `χ`, even weight `K = 2k ≥ 4` (Miyake: any character, any `k ≥ 3`);
* Miyake's `g_K^{(m)} = F_K(z; φ_m, χ, Γ_∞, Γ)` with `φ_m(z) = e^{2πimz/h}` is the series
  `ModularFormsKB.Milne.poincareSeries Γ k m = Σ_{Γ_∞ \ Γ} e^{2πim γz/h} (cz + d)^{-2k}`
  (the sum over `Γ_∞ \ Γ` in `SL₂(ℤ)` equals Miyake's sum since the weight is even);
* Miyake's `∫_{Γ\H} f(z) \overline{g(z)} Im(z)^K dv(z)` is `ModularFormsKB.Milne.milnePetersson`.

All statements are corollaries of the results proved for Milne's notes
(`ModularFormsKB/Milne/Ch4/Poincare.lean`, `PoincareModular.lean`, `Unfolding.lean`).
-/

open UpperHalfPlane ModularForm Filter Topology Matrix.SpecialLinearGroup
open scoped MatrixGroups Real

namespace ModularFormsKB.Miyake

open ModularFormsKB.Milne

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- **Miyake, Theorem 2.6.6 (1), for modular groups at `∞`.** For even weight `2k ≥ 4`, the
Poincaré series `Σ_{Γ_∞\Γ} e^{2πimγz/h}(cz+d)^{-2k}` is dominated on each compact subset of `ℍ`
by a summable series, so it converges absolutely and uniformly on compact sets. -/
@[kb "miyake1989" "Theorem 2.6.6 (1), p. 64"]
theorem poincareSeries_locallyUniform {k : ℕ} (hk : 2 ≤ k) (m : ℕ) {K : Set ℍ}
    (hK : IsCompact K) :
    ∃ u : StabInftyCosets Γ → ℝ, Summable u ∧ ∀ x, ∀ z ∈ K, ‖poincareTerm Γ k m x z‖ ≤ u x :=
  poincareSeries_bound Γ hk m hK

/-- **Miyake, Theorem 2.6.9 (1), for modular groups at `∞`.** For `m ≥ 1` and even weight
`2k ≥ 4`, the Poincaré series `g^{(m)}` is a cusp form for `Γ`. -/
@[kb "miyake1989" "Theorem 2.6.9 (1), p. 67"]
theorem poincareSeries_isCuspForm {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm : 1 ≤ m) :
    ∃ F : CuspForm (Γ.map (mapGL ℝ)) (2 * k : ℕ), ⇑F = poincareSeries Γ k m :=
  (poincareSeriesModular Γ hk).cusp m hm

open scoped Classical in
/-- **Miyake, Theorem 2.6.9 (2), for modular groups at `∞`.** For even weight `2k ≥ 4`, the
Eisenstein series `g^{(0)}` is a modular form for `Γ`; at a cusp `γ ∞` (`γ ∈ SL₂(ℤ)`) its
expansion has constant term `1` if the cusp is `Γ`-equivalent to `∞` and `0` otherwise. -/
@[kb "miyake1989" "Theorem 2.6.9 (2), p. 67"]
theorem poincareSeries_zero_isModularForm {k : ℕ} (hk : 2 ≤ k) :
    (∃ F : ModularForm (Γ.map (mapGL ℝ)) (2 * k : ℕ), ⇑F = poincareSeries Γ k 0) ∧
      ∀ γ : SL(2, ℤ), Tendsto (poincareSeries Γ k 0 ∣[(2 * k : ℤ)] γ) atImInfty
        (𝓝 (if ∃ δ ∈ Γ, (δ * γ) 1 0 = 0 then 1 else 0)) :=
  ⟨(poincareSeriesModular Γ hk).modular 0, (poincareSeriesModular Γ hk).value⟩

/-- **Miyake, Theorem 2.6.10, for modular groups at `∞`.** For a cusp form
`f = Σ_{n≥1} a_n e^{2πinz/h}` of even weight `K = 2k ≥ 4` on `Γ` and `m ≥ 1`,
`∫_{Γ\H} f \overline{g^{(m)}} Im(z)^K dv = a_m (4πm)^{1-K} h^K (K-2)!`. -/
@[kb "miyake1989" "Theorem 2.6.10, p. 67"]
theorem petersson_poincareSeries {k : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm : 1 ≤ m)
    (f : CuspForm (Γ.map (mapGL ℝ)) (2 * k : ℕ)) :
    milnePetersson Γ k f (poincareSeries Γ k m) =
      (qExpansion (widthAtInfty Γ) f).coeff m * (4 * π * m : ℂ) ^ (1 - 2 * (k : ℤ)) *
        (widthAtInfty Γ : ℂ) ^ (2 * k) * (2 * k - 2).factorial := by
  rw [(poincarePetersson Γ hk).formula m hm f]
  have h4 : (4 * π : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    exact mul_ne_zero (by norm_num) this
  rw [mul_zpow, show (1 - 2 * (k : ℤ)) = -((2 * k - 1 : ℕ) : ℤ) by omega]
  simp only [zpow_neg, zpow_natCast]
  field_simp

/-- **Miyake, Theorem 2.6.10 (`m = 0`), for modular groups at `∞`.** Cusp forms of even weight
`2k ≥ 4` are orthogonal to the Eisenstein series `g^{(0)}`. -/
@[kb "miyake1989" "Theorem 2.6.10, p. 67"]
theorem petersson_poincareSeries_zero {k : ℕ} (hk : 2 ≤ k)
    (f : CuspForm (Γ.map (mapGL ℝ)) (2 * k : ℕ)) :
    milnePetersson Γ k f (poincareSeries Γ k 0) = 0 := by
  rw [milnePetersson_poincare_eq_strip Γ hk 0 f, integral_unfoldIntegrand Γ hk 0 f]
  have h : (1 - 2 * (k : ℤ)) ≠ 0 := by omega
  simp [zero_zpow _ h]

/-- **Miyake, Corollary 2.6.11, for modular groups at `∞`.** For even weight `2k ≥ 4`, the
Poincaré series `g^{(m)}`, `m ≥ 1`, span the space of cusp forms of `Γ`. -/
@[kb "miyake1989" "Corollary 2.6.11, p. 68"]
theorem cuspForm_mem_span_poincareSeries {k : ℕ} (hk : 2 ≤ k)
    (f : CuspForm (Γ.map (mapGL ℝ)) (2 * k : ℕ)) :
    ⇑f ∈ Submodule.span ℂ (Set.range fun m : {m : ℕ // 1 ≤ m} ↦ poincareSeries Γ k m) :=
  poincareSeries_span_cuspForm Γ hk f

end ModularFormsKB.Miyake
