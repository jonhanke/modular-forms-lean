import ModularFormsKB.Historical.Weber.ThetaDuplication
import ModularFormsKB.Citation
/-!
# Weber's relations of the second order between `f`, `f₁`, `f₂` (Weber 1891, § 29, (16)–(19))

Weber, *Elliptische Functionen und algebraische Zahlen* (1891), § 29, (16)–(19), p. 88 (also *Lehrbuch der
Algebra* III (1908), § 5, pp. 17–18 and § 34, p. 115): for `ω` in the
upper half plane,

* `f₁(2ω) f₂(ω) = √2`,
* `f₂(ω)⁴ (f(2ω)⁸ + f₂(2ω)⁸) = 2 (f(ω)⁸ + f₁(ω)⁸)`,
* `f(ω) f((ω - 1)/(ω + 1)) = √2`,
* `f₁(ω) f₂(ω/2) = √2`,
* `f(ω) f₂((ω + 1)/2) = e^{πi/24} √2`.

`f = weberF`, `f₁ = weberF₁`, `f₂ = weberF₂` are the `η`-quotients of `ThetaEta.lean`. The first, fourth and fifth
relations follow from the definitions and `η(ω + 1) = e^{2πi/24} η(ω)`; the third from Mathlib's inversion formula
`η(-1/ω) = √(-iω) η(ω)`; the second needs Weber's `f⁸ = f₁⁸ + f₂⁸` at `2ω` and the duplication formula
`ϑ₀₀(ω)² - ϑ₀₁(ω)² = 2 ϑ₁₀(2ω)²` (`ThetaDuplication.lean`).
-/

noncomputable section

open Complex
open scoped Real

namespace ModularFormsKB.Historical.Weber

open ModularFormsKB.WeberHeegnerStark (weberF weberF₂)

/-- **Weber 1891, § 29, (16)–(19)** (p. 88): the five relations of the second order. -/
@[kb "weber1891" "§ 29, (16)-(19), p. 88"]
def WeberSecondOrderRelations : Prop :=
  ∀ ω : ℂ, 0 < ω.im →
    weberF₁ (2 * ω) * weberF₂ ω = ((√2 : ℝ) : ℂ) ∧
    weberF₂ ω ^ 4 * (weberF (2 * ω) ^ 8 + weberF₂ (2 * ω) ^ 8) = 2 * (weberF ω ^ 8 + weberF₁ ω ^ 8) ∧
    weberF ω * weberF ((ω - 1) / (ω + 1)) = ((√2 : ℝ) : ℂ) ∧
    weberF₁ ω * weberF₂ (ω / 2) = ((√2 : ℝ) : ℂ) ∧
    weberF ω * weberF₂ ((ω + 1) / 2) = cexp (π * I / 24) * ((√2 : ℝ) : ℂ)

section Proofs

lemma im_neg_one_div_pos {z : ℂ} (hz : 0 < z.im) : 0 < (-1 / z).im := by
  have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz
  rw [neg_div, Complex.neg_im, one_div, Complex.inv_im, neg_div, neg_neg]
  exact div_pos hz (Complex.normSq_pos.mpr hz0)

lemma eta_S_eq {w : ℂ} (hw : 0 < w.im) :
    ModularForm.eta (-1 / w) = (Complex.sqrt I)⁻¹ * (Complex.sqrt w * ModularForm.eta w) := by
  have h := ModularForm.eta_comp_eq_csqrt_I_inv hw
  simpa [Function.comp, smul_eq_mul] using h

lemma csqrt_ne_zero {w : ℂ} (hw : w ≠ 0) : Complex.sqrt w ≠ 0 := by
  rw [_root_.sqrt_eq_exp hw]; exact Complex.exp_ne_zero _

lemma csqrt_two_mul {w : ℂ} (hw : w ≠ 0) :
    Complex.sqrt (2 * w) = ((√2 : ℝ) : ℂ) * Complex.sqrt w := by
  have hl : Complex.log (2 * w) = Complex.log 2 + Complex.log w := by
    have := Complex.log_ofReal_mul (r := 2) (by norm_num) hw
    simpa using this
  have h2 : ((√2 : ℝ) : ℂ) = cexp (Complex.log 2 / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num), Complex.ofReal_exp]
    congr 1
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_log (by norm_num)]
    push_cast; ring
  rw [_root_.sqrt_eq_exp (mul_ne_zero two_ne_zero hw), _root_.sqrt_eq_exp hw, h2, hl,
    ← Complex.exp_add]
  congr 1; ring

/-- `f₁(2ω) f₂(ω) = √2` (Weber 1891, § 29, (16)). -/
theorem weber_f₁_two_mul_f₂ {ω : ℂ} (hω : 0 < ω.im) :
    weberF₁ (2 * ω) * weberF₂ ω = ((√2 : ℝ) : ℂ) := weber_prod12 hω

/-- `f₁(ω) f₂(ω/2) = √2` (Weber 1891, § 29, (19)). -/
theorem weber_f₁_f₂_half {ω : ℂ} (hω : 0 < ω.im) :
    weberF₁ ω * weberF₂ (ω / 2) = ((√2 : ℝ) : ℂ) := by
  have h1 : ModularForm.eta (ω / 2) ≠ 0 := ModularForm.eta_ne_zero (by simpa using hω)
  have h2 : ModularForm.eta ω ≠ 0 := ModularForm.eta_ne_zero hω
  unfold weberF₁ weberF₂
  rw [show 2 * (ω / 2) = ω by ring]
  field_simp

/-- `f(ω) f₂((ω+1)/2) = e^{πi/24} √2` (Weber 1891, § 29, (19)). -/
theorem weber_f_f₂_shift {ω : ℂ} (hω : 0 < ω.im) :
    weberF ω * weberF₂ ((ω + 1) / 2) = cexp (π * I / 24) * ((√2 : ℝ) : ℂ) := by
  have h1 : ModularForm.eta ((ω + 1) / 2) ≠ 0 := ModularForm.eta_ne_zero (by simpa using hω)
  have h2 : ModularForm.eta ω ≠ 0 := ModularForm.eta_ne_zero hω
  unfold weberF weberF₂
  rw [show 2 * ((ω + 1) / 2) = ω + 1 by ring, eta_add_one]
  have key : cexp (π * I / 24) = cexp (-(π * I) / 24) * cexp (2 * π * I / 24) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [key]
  field_simp

/-- `f(ω) f((ω-1)/(ω+1)) = √2` (Weber 1891, § 29, (18)). -/
theorem weber_f_f_moebius {ω : ℂ} (hω : 0 < ω.im) :
    weberF ω * weberF ((ω - 1) / (ω + 1)) = ((√2 : ℝ) : ℂ) := by
  have hz : 0 < (ω + 1).im := by simpa using hω
  have hz2 : 0 < ((ω + 1) / 2).im := by simpa using hz
  have hz0 : ω + 1 ≠ 0 := fun h ↦ by simp [h] at hz
  have e1 : ((ω - 1) / (ω + 1) + 1) / 2 = -1 / (ω + 1) + 1 := by
    field_simp; ring
  have e2 : (ω - 1) / (ω + 1) = -1 / ((ω + 1) / 2) + 1 := by
    field_simp; ring
  have hη1 : ModularForm.eta ((ω + 1) / 2) ≠ 0 := ModularForm.eta_ne_zero hz2
  have hη2 : ModularForm.eta ω ≠ 0 := ModularForm.eta_ne_zero hω
  have hsq : Complex.sqrt (ω + 1) = ((√2 : ℝ) : ℂ) * Complex.sqrt ((ω + 1) / 2) := by
    rw [show ω + 1 = 2 * ((ω + 1) / 2) by ring]
    rw [show 2 * ((ω + 1) / 2) / 2 = (ω + 1) / 2 by ring]
    exact csqrt_two_mul (div_ne_zero hz0 two_ne_zero)
  have hs1 : Complex.sqrt ((ω + 1) / 2) ≠ 0 := csqrt_ne_zero (div_ne_zero hz0 two_ne_zero)
  have hI : Complex.sqrt I ≠ 0 := csqrt_ne_zero Complex.I_ne_zero
  unfold weberF
  rw [e1, e2, eta_add_one (-1 / (ω + 1)), eta_add_one (-1 / ((ω + 1) / 2)),
    eta_S_eq hz, eta_S_eq hz2, hsq]
  have hη3 : ModularForm.eta (ω + 1) = cexp (2 * π * I / 24) * ModularForm.eta ω := eta_add_one ω
  rw [hη3]
  field_simp
  rw [← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_zero]
  congr 1; push_cast; ring

/-- The second relation: `f₂(ω)⁴ (f(2ω)⁸ + f₂(2ω)⁸) = 2 (f(ω)⁸ + f₁(ω)⁸)`, from `f⁸ = f₁⁸ + f₂⁸` at `2ω`,
the duplication formula `ϑ₀₀² - ϑ₀₁² = 2 ϑ₁₀(2·)²` and `f f₁ f₂ = √2`. -/
lemma weber_second_relation (h : WeberEighthPowers) (hD : ThetaDuplication) {ω : ℂ} (hω : 0 < ω.im) :
    weberF₂ ω ^ 4 * (weberF (2 * ω) ^ 8 + weberF₂ (2 * ω) ^ 8) =
      2 * (weberF ω ^ 8 + weberF₁ ω ^ 8) := by
  have hω2 : 0 < (2 * ω).im := by simpa using hω
  have h8 := h (2 * ω) hω2
  have hdup := (hD ω hω).2.2
  rw [weberTheta00_eq hω, weberTheta01_eq hω, weberTheta10_eq hω2] at hdup
  have he : ModularForm.eta ω ≠ 0 := ModularForm.eta_ne_zero hω
  have hs := sqrt2_sq
  have hs0 := sqrt2_ne
  have hf2 : weberF₂ ω * ModularForm.eta ω = ((√2 : ℝ) : ℂ) * ModularForm.eta (2 * ω) := by
    unfold weberF₂; field_simp
  have hF1 := weber_prod12 hω
  have hT := weber_triple hω
  generalize ((√2 : ℝ) : ℂ) = s at *
  generalize weberF₂ ω = t at *
  generalize weberF₁ (2 * ω) = F1 at *
  generalize weberF₂ (2 * ω) = F2 at *
  generalize weberF (2 * ω) = F at *
  generalize weberF ω = f at *
  generalize weberF₁ ω = g at *
  generalize ModularForm.eta (2 * ω) = e2 at *
  generalize ModularForm.eta ω = e at *
  have ht : t ≠ 0 := by
    rintro rfl
    simp at hF1; exact hs0 hF1.symm
  have hX : f ^ 4 - g ^ 4 = t ^ 2 * F2 ^ 4 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 he)
    linear_combination hdup - F2 ^ 4 * ((t * e + s * e2) * hf2 + e2 ^ 2 * hs)
  have hA : t ^ 8 * F1 ^ 8 = 16 := by
    have : (F1 * t) ^ 8 = (s ^ 2) ^ 4 := by rw [hF1]; ring
    rw [hs] at this
    linear_combination this
  have hB : (f * g * t) ^ 4 = 4 := by
    have : (f * g * t) ^ 4 = (s ^ 2) ^ 2 := by rw [hT]; ring
    rw [hs] at this
    linear_combination this
  rw [h8]
  apply mul_left_cancel₀ (pow_ne_zero 4 ht)
  linear_combination hA - 2 * t ^ 4 * ((t ^ 2 * F2 ^ 4 + (f ^ 4 - g ^ 4)) * hX) - 4 * hB

/-- **Weber 1891, § 29, (16)–(19)** (p. 88): the five relations of the second
order. The relations other than the second are unconditional (`weber_f₁_two_mul_f₂`, `weber_f_f_moebius`,
`weber_f₁_f₂_half`, `weber_f_f₂_shift`); the second uses `f⁸ = f₁⁸ + f₂⁸` and the theta duplication formula. -/
@[kb "weber1891" "§ 29, (16)-(19), p. 88"]
theorem weberSecondOrderRelations (h : WeberEighthPowers) (hD : ThetaDuplication) :
    WeberSecondOrderRelations := fun _ hω ↦
  ⟨weber_f₁_two_mul_f₂ hω, weber_second_relation h hD hω, weber_f_f_moebius hω,
    weber_f₁_f₂_half hω, weber_f_f₂_shift hω⟩

/-- **Weber 1891, § 29, (16)–(19)**, unconditional: the inputs `WeberEighthPowers`
and `ThetaDuplication` are proved (`weberEighthPowers`, `thetaDuplication`). -/
@[kb "weber1891" "§ 29, (16)-(19), p. 88"]
theorem weberSecondOrderRelations' : WeberSecondOrderRelations :=
  weberSecondOrderRelations weberEighthPowers thetaDuplication

end Proofs

end ModularFormsKB.Historical.Weber
