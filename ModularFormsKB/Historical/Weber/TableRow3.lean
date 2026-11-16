import ModularFormsKB.Historical.Weber.ClassInvariantTable

/-!
# Weber's Tabelle VI, `m = 3`: `f(√-3) = ∛2`

Proved from `η(-1/z)² = -iz η(z)²`, `η(z+1) = e^{2πi/24} η(z)` and `f f₁ f₂ = √2`, by comparing absolute
values at `σ = (1 + i√3)/2` (where `-1/σ = σ - 1`), and then using positivity of `f(i√3)`.
-/

noncomputable section

open Complex
open scoped Real

namespace ModularFormsKB.Historical.Weber

open ModularFormsKB.WeberHeegnerStark (weberF weberF₂)

section Row3

lemma norm_eta_S {z : ℂ} (hz : 0 < z.im) :
    ‖ModularForm.eta (-1 / z)‖ ^ 2 = ‖z‖ * ‖ModularForm.eta z‖ ^ 2 := by
  have h := congrArg norm (eta_S_sq hz)
  rw [norm_pow, norm_mul, norm_mul, norm_pow, norm_neg, Complex.norm_I, one_mul] at h
  exact h

lemma norm_eta_add_one (z : ℂ) : ‖ModularForm.eta (z + 1)‖ = ‖ModularForm.eta z‖ := by
  rw [eta_add_one, norm_mul, Complex.norm_exp]
  simp

lemma norm_cexp_neg_pi (x : ℂ) : ‖cexp (-(π * I) / 24) * x‖ = ‖x‖ := by
  rw [norm_mul, Complex.norm_exp]
  simp

/-- **Tabelle VI, `m = 3`** (Weber 1891, Anhang): `f(√-3) = ∛2`.
Proof: at `σ = (1+i√3)/2` (`-1/σ = σ-1`, `2σ-1 = i√3`) the `η` inversion formula and `η(z+1) = e^{2πi/24} η(z)`
give `|η((σ+1)/2)| = |η(σ/2)| = √2 |η(2σ)|`; with `f f₁ f₂ = √2` (`weber_triple`) this yields
`|η(σ)|³ = 2 |η(2σ)|³`; and `|f(i√3)| = |η(σ)| / |η(2σ)|`, so `f(i√3)³ = 2` with `f(i√3) > 0`
(`weberF_pos`). -/
@[kb "weber1908" "Tabelle VI, m = 3, p. 721"]
theorem tableRow3 : TableRow3 := by
  unfold TableRow3
  have h3 : (0 : ℝ) < √3 := by positivity
  have hs2 : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow]; simp
  obtain ⟨σ, hσ⟩ : ∃ σ : ℂ, σ = (1 + I * ((√3 : ℝ) : ℂ)) / 2 := ⟨_, rfl⟩
  have hσim : 0 < σ.im := by rw [hσ]; simp
  have hσn : ‖σ‖ = 1 := by
    have : ‖σ‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hσ]
      simp
      have := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      nlinarith
    have h0 := norm_nonneg σ
    nlinarith
  have hσ0 : σ ≠ 0 := fun h ↦ by rw [h] at hσim; simp at hσim
  have key : (σ - 1) * σ = -1 := by
    rw [hσ]
    linear_combination (-1 / 4 : ℂ) * hs2 + (((√3 : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq
  have e1 : -1 / (2 * σ) = (σ - 1) / 2 := by
    rw [div_eq_iff (mul_ne_zero two_ne_zero hσ0)]
    linear_combination (-1 : ℂ) * key
  have e2 : -1 / (σ / 2) = 2 * σ - 2 := by
    rw [div_eq_iff (div_ne_zero hσ0 two_ne_zero)]
    linear_combination (-1 : ℂ) * key
  have n2 : ‖(2 : ℂ)‖ = 2 := by simp
  have him2 : 0 < (2 * σ).im := by simpa using hσim
  have himh : 0 < (σ / 2).im := by
    have : (σ / 2).im = σ.im / 2 := by simp
    rw [this]; linarith
  have hA : ModularForm.eta (2 * σ) ≠ 0 := ModularForm.eta_ne_zero him2
  have hB : ModularForm.eta σ ≠ 0 := ModularForm.eta_ne_zero hσim
  have ha : 0 < ‖ModularForm.eta (2 * σ)‖ := norm_pos_iff.mpr hA
  have hb : 0 < ‖ModularForm.eta σ‖ := norm_pos_iff.mpr hB
  have hp : ‖ModularForm.eta ((σ + 1) / 2)‖ ^ 2 = 2 * ‖ModularForm.eta (2 * σ)‖ ^ 2 := by
    have h := norm_eta_S him2
    rw [e1, norm_mul, hσn, n2] at h
    have h2 := norm_eta_add_one ((σ - 1) / 2)
    rw [show (σ - 1) / 2 + 1 = (σ + 1) / 2 by ring] at h2
    rw [h2, h]; ring
  have hq : ‖ModularForm.eta (σ / 2)‖ ^ 2 = 2 * ‖ModularForm.eta (2 * σ)‖ ^ 2 := by
    have h := norm_eta_S himh
    rw [e2, norm_div, hσn, n2] at h
    have h1 := norm_eta_add_one (2 * σ - 2)
    have h2 := norm_eta_add_one (2 * σ - 2 + 1)
    rw [show 2 * σ - 2 + 1 + 1 = 2 * σ by ring] at h2
    rw [← h1, ← h2] at h
    linarith
  have hpq : ‖ModularForm.eta ((σ + 1) / 2)‖ = ‖ModularForm.eta (σ / 2)‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hp.trans hq.symm)
  -- the triple product, in norms
  have htr := congrArg norm (weber_triple hσim)
  have nF : ‖weberF σ‖ = ‖ModularForm.eta ((σ + 1) / 2)‖ / ‖ModularForm.eta σ‖ := by
    unfold weberF; rw [norm_div, norm_cexp_neg_pi]
  have nF1 : ‖weberF₁ σ‖ = ‖ModularForm.eta (σ / 2)‖ / ‖ModularForm.eta σ‖ := by
    unfold weberF₁; rw [norm_div]
  have nF2 : ‖weberF₂ σ‖ = √2 * ‖ModularForm.eta (2 * σ)‖ / ‖ModularForm.eta σ‖ := by
    unfold weberF₂
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [norm_mul, norm_mul, nF, nF1, nF2, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    ← hpq] at htr
  obtain ⟨P, hP⟩ : ∃ P, P = ‖ModularForm.eta ((σ + 1) / 2)‖ := ⟨_, rfl⟩
  obtain ⟨a, haa⟩ : ∃ a, a = ‖ModularForm.eta (2 * σ)‖ := ⟨_, rfl⟩
  obtain ⟨b, hbb⟩ : ∃ b, b = ‖ModularForm.eta σ‖ := ⟨_, rfl⟩
  rw [← hP, ← haa, ← hbb] at htr
  rw [← hP, ← haa] at hp
  rw [← haa] at ha
  rw [← hbb] at hb
  have hr2 : (0 : ℝ) < √2 := by positivity
  have hcube : b ^ 3 = 2 * a ^ 3 := by
    have E : √2 * (P ^ 2 * a) = √2 * b ^ 3 := by
      field_simp at htr
      linear_combination √2 * htr
    have E2 := mul_left_cancel₀ hr2.ne' E
    rw [← E2, hp]; ring
  -- f(i√3)
  have hI3 : I * ((√3 : ℝ) : ℂ) = 2 * σ - 1 := by rw [hσ]; ring
  have hσ' : (I * ((√3 : ℝ) : ℂ) + 1) / 2 = σ := by rw [hσ]; ring
  obtain ⟨d, hd0, hd⟩ := weberF_pos h3
  have hnd : d = b / a := by
    have h1 : ‖weberF (I * ((√3 : ℝ) : ℂ))‖ = d := by
      rw [hd, Complex.norm_real, Real.norm_of_nonneg hd0.le]
    rw [← h1]
    unfold weberF
    rw [norm_div, norm_cexp_neg_pi, hσ', ← hbb]
    have h2 := norm_eta_add_one (I * ((√3 : ℝ) : ℂ))
    rw [hI3, sub_add_cancel] at h2
    rw [hI3, ← h2, ← haa]
  have hd3 : d ^ 3 = 2 := by
    rw [hnd, div_pow, hcube]; field_simp
  have hc3 : ((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hdd : d = (2 : ℝ) ^ (1 / 3 : ℝ) :=
    (pow_left_inj₀ hd0.le (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp (hd3.trans hc3.symm)
  have hs : sqrtNeg 3 = I * ((√3 : ℝ) : ℂ) := by simp [sqrtNeg]
  rw [hs, hd, hdd]

end Row3

end ModularFormsKB.Historical.Weber
