import ModularFormsKB.Historical.Jacobi.ThetaNullwerte
import ModularFormsKB.Historical.Weber.ThetaEta
import ModularFormsKB.Historical.Weber.ClassInvariantTable
import ModularFormsKB.Citation
/-!
# Jacobi's product formulas for the complete integral

Jacobi, *Fundamenta nova* (1829), § 36, pp. 87–90. For `0 < k < 1` with nome `q = e^{-πK'/K}` (here: for `y > 0`,
`q = e^{-πy}` and `k = ϑ₂²/ϑ₃²`, whose nome is `q` by `jacobiThetaConstants`):

* 9)  `2K/π = {∏ (1 - q^{2n})/(1 - q^{2n-1})}² {∏ (1 + q^{2n-1})/(1 + q^{2n})}²`;
* 10) `2kK/π = 4√q {∏ (1 - q^{4n})/(1 - q^{4n-2})}²`;
* 11) `2k'K/π = {∏ (1 - qⁿ)/(1 + qⁿ)}²`;
* 12) `2√k K/π = 2 q^{1/4} {∏ (1 - q^{2n})/(1 - q^{2n-1})}²`;
* 13) `2√k' K/π = {∏ (1 - q^{2n})/(1 + q^{2n})}²`;

and (§ 36, p. 89) `∏ (1 - q^{2n})⁶ = 2kk'K³/(π³√q)`. Products over `n ≥ 1`, written with `n + 1` for `n ≥ 0`.
Proved from `ϑ₃² = 2K/π`, `ϑ₂² = 2kK/π`, `ϑ₄² = 2k'K/π` (`ThetaNullwerte.lean`), the product forms
`ϑ₀₀ = η f²`, `ϑ₀₁ = η f₁²`, `ϑ₁₀ = η f₂²` (`Weber/ThetaEta.lean`, from the triple product), and Weber's
`f f₁ f₂ = √2`, which in products is `∏ (1 - q^{2n-1}) ∏ (1 + q^{2n-1}) ∏ (1 + q^{2n}) = 1`, the form of Euler's
`∏ (1 + qⁿ) ∏ (1 - q^{2n-1}) = 1` that Jacobi quotes from the *Introductio*.
-/

noncomputable section

open Complex TauCeti.Real
open scoped Real

namespace ModularFormsKB.Historical.Jacobi

open ModularFormsKB.Historical.Weber

private lemma facts {y : ℝ} (hy : 0 < y) (q s : ℂ) (hq : q = ((Real.exp (-π * y) : ℝ) : ℂ))
    (hs : s = ((Real.exp (-π * y / 24) : ℝ) : ℂ)) :
    ‖q‖ < 1 ∧ s ≠ 0 ∧ s ^ 12 = ((Real.exp (-π * y / 2) : ℝ) : ℂ) ∧
      s ^ 6 = ((Real.exp (-π * y / 4) : ℝ) : ℂ) ∧
      (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) ≠ 0 ∧ (∏' n : ℕ, (1 - q ^ (2 * n + 1))) ≠ 0 ∧
      (∏' n : ℕ, (1 + q ^ (2 * n + 1))) ≠ 0 ∧ (∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) ≠ 0 ∧
      ((thetaNull3 y : ℝ) : ℂ) = (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) *
        (∏' n : ℕ, (1 + q ^ (2 * n + 1))) ^ 2 ∧
      ((thetaNull4 y : ℝ) : ℂ) = (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) *
        (∏' n : ℕ, (1 - q ^ (2 * n + 1))) ^ 2 ∧
      ((thetaNull2 y : ℝ) : ℂ) = 2 * s ^ 6 * (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) *
        (∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) ^ 2 ∧
      (∏' n : ℕ, (1 - q ^ (2 * n + 1))) * (∏' n : ℕ, (1 + q ^ (2 * n + 1))) *
        (∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) = 1 := by
  have hω : 0 < (I * (y : ℂ)).im := im_I_mul_ofReal_pos hy
  have hq' : q = cexp (π * I * (I * y)) := by
    rw [hq, Complex.ofReal_exp]; congr 1; push_cast
    linear_combination (-(π : ℂ) * y) * Complex.I_sq
  have hs' : s = cexp (π * I * (I * y) / 24) := by
    rw [hs, Complex.ofReal_exp]; congr 1; push_cast
    linear_combination (-(π : ℂ) * y / 24) * Complex.I_sq
  have hqn : ‖q‖ < 1 := hq' ▸ norm_cexp_pi_mul_lt_one hω
  have hs0 : s ≠ 0 := by rw [hs']; exact Complex.exp_ne_zero _
  have hs6 : s ^ 6 = ((Real.exp (-π * y / 4) : ℝ) : ℂ) := by
    rw [hs, ← Complex.ofReal_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have hs12 : s ^ 12 = ((Real.exp (-π * y / 2) : ℝ) : ℂ) := by
    rw [hs, ← Complex.ofReal_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have hη := ModularForm.eta_ne_zero hω
  have he := eta_eq_q hq' hs'
  have hP : ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) ≠ 0 := by
    rw [he] at hη; exact right_ne_zero_of_mul hη
  have h3 : ((thetaNull3 y : ℝ) : ℂ) = (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) *
      (∏' n : ℕ, (1 + q ^ (2 * n + 1))) ^ 2 := by
    rw [← weberTheta00_I_mul hy, weberTheta00_eq hω, he, weberF_eq_q hω hq' hs']
    field_simp
  have h4 : ((thetaNull4 y : ℝ) : ℂ) = (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) *
      (∏' n : ℕ, (1 - q ^ (2 * n + 1))) ^ 2 := by
    rw [← weberTheta01_I_mul hy, weberTheta01_eq hω, he, weberF₁_eq_q hω hq' hs']
    field_simp
  have h2 : ((thetaNull2 y : ℝ) : ℂ) = 2 * s ^ 6 * (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) *
      (∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) ^ 2 := by
    have h22 : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow]; simp
    rw [← weberTheta10_I_mul hy, weberTheta10_eq hω, he, weberF₂_eq_q hω hq' hs']
    linear_combination (s ^ 6 * (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) *
      (∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) ^ 2) * h22
  have hne3 : ((thetaNull3 y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (thetaNull3_pos hy).ne'
  have hne4 : ((thetaNull4 y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (thetaNull4_pos hy).ne'
  have hne2 : ((thetaNull2 y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (thetaNull2_pos hy).ne'
  have hB : ∏' n : ℕ, (1 + q ^ (2 * n + 1)) ≠ 0 := by
    intro h; rw [h] at h3; exact hne3 (by rw [h3]; ring)
  have hA : ∏' n : ℕ, (1 - q ^ (2 * n + 1)) ≠ 0 := by
    intro h; rw [h] at h4; exact hne4 (by rw [h4]; ring)
  have hC : ∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1)) ≠ 0 := by
    intro h; rw [h] at h2; exact hne2 (by rw [h2]; ring)
  have ht := weber_triple hω
  rw [weberF_eq_q hω hq' hs', weberF₁_eq_q hω hq' hs', weberF₂_eq_q hω hq' hs'] at ht
  have h2' : ((√2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  have hABC : (∏' n : ℕ, (1 - q ^ (2 * n + 1))) * (∏' n : ℕ, (1 + q ^ (2 * n + 1))) *
        (∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) = 1 := by
    field_simp at ht
    linear_combination ht
  exact ⟨hqn, hs0, hs12, hs6, hP, hA, hB, hC, h3, h4, h2, hABC⟩


private lemma quot_facts {q : ℂ} (hqn : ‖q‖ < 1)
    (hP : (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) ≠ 0) (hA : (∏' n : ℕ, (1 - q ^ (2 * n + 1))) ≠ 0)
    (hB : (∏' n : ℕ, (1 + q ^ (2 * n + 1))) ≠ 0) (hC : (∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) ≠ 0)
    (hABC : (∏' n : ℕ, (1 - q ^ (2 * n + 1))) * (∏' n : ℕ, (1 + q ^ (2 * n + 1))) *
        (∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) = 1) :
    (∏' n : ℕ, (1 - q ^ (2 * (n + 1))) / (1 - q ^ (2 * n + 1))) =
        (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) / (∏' n : ℕ, (1 - q ^ (2 * n + 1))) ∧
      (∏' n : ℕ, (1 + q ^ (2 * n + 1)) / (1 + q ^ (2 * (n + 1)))) =
        (∏' n : ℕ, (1 + q ^ (2 * n + 1))) / (∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) ∧
      (∏' n : ℕ, (1 - q ^ (4 * (n + 1))) / (1 - q ^ (4 * n + 2))) =
        ((∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) * (∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1)))) /
          ((∏' n : ℕ, (1 - q ^ (2 * n + 1))) * (∏' n : ℕ, (1 + q ^ (2 * n + 1)))) ∧
      (∏' n : ℕ, (1 - q ^ (n + 1)) / (1 + q ^ (n + 1))) =
        ((∏' n : ℕ, (1 - q ^ (2 * n + 1))) * (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)))) /
          ((∏' n : ℕ, (1 + q ^ (2 * n + 1))) * (∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1)))) ∧
      (∏' n : ℕ, (1 - q ^ (2 * (n + 1))) / (1 + q ^ (2 * (n + 1)))) =
        (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) / (∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) := by
  have hq2 := norm_sq_lt_one hqn
  have hmP : Multipliable fun n : ℕ ↦ 1 - (q ^ 2) ^ (n + 1) :=
    ModularForm.multipliable_one_sub_pow hq2
  have hmA := multipliable_one_sub_pow_odd hqn
  have hmB := multipliable_one_add_pow_odd hqn
  have hmC := multipliable_one_add_pow_succ hq2
  have hmD := multipliable_one_add_pow_succ hqn
  have hmF := ModularForm.multipliable_one_sub_pow hqn
  have hPe : ∀ n : ℕ, 1 - q ^ (2 * (n + 1)) = 1 - (q ^ 2) ^ (n + 1) := fun n ↦ by rw [pow_mul]
  have hCe : ∀ n : ℕ, 1 + q ^ (2 * (n + 1)) = 1 + (q ^ 2) ^ (n + 1) := fun n ↦ by rw [pow_mul]
  have hP' : (fun n : ℕ ↦ 1 - q ^ (2 * (n + 1))) = fun n ↦ 1 - (q ^ 2) ^ (n + 1) := funext hPe
  have hC' : (fun n : ℕ ↦ 1 + q ^ (2 * (n + 1))) = fun n ↦ 1 + (q ^ 2) ^ (n + 1) := funext hCe
  have e1 : ∏' n : ℕ, (1 - q ^ (4 * (n + 1))) =
      (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) * ∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1)) := by
    rw [← hmP.tprod_mul hmC]
    exact tprod_congr fun n ↦ by ring
  have e2 : ∏' n : ℕ, (1 - q ^ (4 * n + 2)) =
      (∏' n : ℕ, (1 - q ^ (2 * n + 1))) * ∏' n : ℕ, (1 + q ^ (2 * n + 1)) := by
    rw [← hmA.tprod_mul hmB]
    exact tprod_congr fun n ↦ by ring
  have hm1 : Multipliable fun n : ℕ ↦ 1 - q ^ (4 * (n + 1)) :=
    (hmP.mul hmC).congr fun n ↦ by ring
  have hm2 : Multipliable fun n : ℕ ↦ 1 - q ^ (4 * n + 2) :=
    (hmA.mul hmB).congr fun n ↦ by ring
  have hAD : (∏' n : ℕ, (1 - q ^ (2 * n + 1))) * ∏' n : ℕ, (1 + q ^ (n + 1)) = 1 := by
    have h := tprod_one_sub_mul_one_add hqn
    rw [tprod_one_sub_pow_split hqn] at h
    apply mul_left_cancel₀ hP
    linear_combination h
  have hD : ∏' n : ℕ, (1 + q ^ (n + 1)) =
      (∏' n : ℕ, (1 + q ^ (2 * n + 1))) * ∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1)) := by
    linear_combination (∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) * (∏' n : ℕ, (1 + q ^ (2 * n + 1))) * hAD -
      (∏' n : ℕ, (1 + q ^ (n + 1))) * hABC
  have hD0 : (∏' n : ℕ, (1 + q ^ (n + 1))) ≠ 0 := by rw [hD]; exact mul_ne_zero hB hC
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [hPe]
    exact (hmP.tprod_div₀ hmA hA)
  · simp only [hCe]
    exact hmB.tprod_div₀ hmC hC
  · rw [← e1, ← e2]
    exact hm1.tprod_div₀ hm2 (by rw [e2]; exact mul_ne_zero hA hB)
  · rw [← hD, ← tprod_one_sub_pow_split hqn]
    exact hmF.tprod_div₀ hmD hD0
  · simp only [hPe, hCe]
    exact hmP.tprod_div₀ hmC hC

private lemma alg_facts (A B C P s : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hs : s ≠ 0)
    (h : A * B * C = 1) :
    (P * B ^ 2) ^ 2 = (P / A) ^ 2 * (B / C) ^ 2 ∧
    (2 * s ^ 6 * P * C ^ 2) ^ 2 = 4 * s ^ 12 * ((P * C) / (A * B)) ^ 2 ∧
    (P * A ^ 2) ^ 2 = ((A * P) / (B * C)) ^ 2 ∧
    (2 * s ^ 6 * P * C ^ 2) * (P * B ^ 2) = 2 * s ^ 6 * (P / A) ^ 2 ∧
    (P * B ^ 2) * (P * A ^ 2) = (P / C) ^ 2 ∧
    P ^ 6 = ((2 * s ^ 6 * P * C ^ 2) * (P * B ^ 2) * (P * A ^ 2)) ^ 2 / (4 * s ^ 12) := by
  have hA' : A = (B * C)⁻¹ := by
    field_simp
    linear_combination h
  subst hA'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- **Jacobi's product formulas 9)–13)** (*Fundamenta nova* § 36, pp. 89–90), in the
nome `q = e^{-πy}`, `y > 0`, with `k = ϑ₂²/ϑ₃²` (`jacobiModulusOf y`), `k' = √(1 - k²)`, `K = K(k)`; `√q = e^{-πy/2}`,
`q^{1/4} = e^{-πy/4}`. -/
@[kb "jacobi1829" "§ 36, 9)–13), pp. 89–90"]
theorem jacobiProductFormulas {y : ℝ} (hy : 0 < y) :
    let k := jacobiModulusOf y
    let K := legendreK k
    let q : ℂ := (Real.exp (-π * y) : ℝ)
    ((2 * K / π : ℝ) : ℂ) = (∏' n : ℕ, (1 - q ^ (2 * (n + 1))) / (1 - q ^ (2 * n + 1))) ^ 2 *
        (∏' n : ℕ, (1 + q ^ (2 * n + 1)) / (1 + q ^ (2 * (n + 1)))) ^ 2 ∧
      ((2 * k * K / π : ℝ) : ℂ) = 4 * ((Real.exp (-π * y / 2) : ℝ) : ℂ) *
        (∏' n : ℕ, (1 - q ^ (4 * (n + 1))) / (1 - q ^ (4 * n + 2))) ^ 2 ∧
      ((2 * √(1 - k ^ 2) * K / π : ℝ) : ℂ) = (∏' n : ℕ, (1 - q ^ (n + 1)) / (1 + q ^ (n + 1))) ^ 2 ∧
      ((2 * √k * K / π : ℝ) : ℂ) = 2 * ((Real.exp (-π * y / 4) : ℝ) : ℂ) *
        (∏' n : ℕ, (1 - q ^ (2 * (n + 1))) / (1 - q ^ (2 * n + 1))) ^ 2 ∧
      ((2 * √(√(1 - k ^ 2)) * K / π : ℝ) : ℂ) =
        (∏' n : ℕ, (1 - q ^ (2 * (n + 1))) / (1 + q ^ (2 * (n + 1)))) ^ 2 := by
  obtain ⟨hk0, hk1, hk', hKK, e3, e2, e4⟩ := jacobiThetaConstants hy
  have t3 := thetaNull3_pos hy
  have t2 := thetaNull2_pos hy
  have t4 := thetaNull4_pos hy
  have hkd : jacobiModulusOf y = thetaNull2 y ^ 2 / thetaNull3 y ^ 2 := rfl
  have hsk : √(jacobiModulusOf y) = thetaNull2 y / thetaNull3 y := by
    rw [hkd, ← div_pow]; exact Real.sqrt_sq (by positivity)
  have hsk' : √(√(1 - jacobiModulusOf y ^ 2)) = thetaNull4 y / thetaNull3 y := by
    rw [hk', ← div_pow]; exact Real.sqrt_sq (by positivity)
  have R1 : 2 * legendreK (jacobiModulusOf y) / π = thetaNull3 y ^ 2 := e3.symm
  have R2 : 2 * jacobiModulusOf y * legendreK (jacobiModulusOf y) / π = thetaNull2 y ^ 2 := e2.symm
  have R3 : 2 * √(1 - jacobiModulusOf y ^ 2) * legendreK (jacobiModulusOf y) / π = thetaNull4 y ^ 2 :=
    e4.symm
  have R4 : 2 * √(jacobiModulusOf y) * legendreK (jacobiModulusOf y) / π =
      thetaNull2 y * thetaNull3 y := by
    rw [hsk, show 2 * (thetaNull2 y / thetaNull3 y) * legendreK (jacobiModulusOf y) / π =
      thetaNull2 y / thetaNull3 y * (2 * legendreK (jacobiModulusOf y) / π) by ring, R1]
    field_simp
  have R5 : 2 * √(√(1 - jacobiModulusOf y ^ 2)) * legendreK (jacobiModulusOf y) / π =
      thetaNull3 y * thetaNull4 y := by
    rw [hsk', show 2 * (thetaNull4 y / thetaNull3 y) * legendreK (jacobiModulusOf y) / π =
      thetaNull4 y / thetaNull3 y * (2 * legendreK (jacobiModulusOf y) / π) by ring, R1]
    field_simp
  intro k K q
  simp only [k, K]
  obtain ⟨hqn, hs0, hs12, hs6, hP, hA, hB, hC, h3, h4, h2, hABC⟩ :=
    facts hy q ((Real.exp (-π * y / 24) : ℝ) : ℂ) rfl rfl
  obtain ⟨c1, c2, c3, c4, c5⟩ := quot_facts hqn hP hA hB hC hABC
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := alg_facts _ _ _ (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)))
    _ hA hB hC hs0 hABC
  rw [c1, c2, c3, c4, c5, R1, R2, R3, R4, R5]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  rw [h3, h4, h2, ← hs12, ← hs6]
  exact ⟨a1, a2, a3, a4, a5⟩

/-- **Jacobi's evaluation of `∏ (1 - q^{2n})⁶`** (*Fundamenta nova* § 36, p. 89):
`∏ (1 - q^{2n})⁶ = 2kk'K³/(π³√q)`, in the nome `q = e^{-πy}`, `y > 0`, `k = ϑ₂²/ϑ₃²`. Equivalently
`ϑ₂ϑ₃ϑ₄ = 2η³`. -/
@[kb "jacobi1829" "§ 36, p. 89"]
theorem jacobiEulerProductSixth {y : ℝ} (hy : 0 < y) :
    let k := jacobiModulusOf y
    let q : ℂ := (Real.exp (-π * y) : ℝ)
    (∏' n : ℕ, (1 - q ^ (2 * (n + 1)))) ^ 6 =
      ((2 * k * √(1 - k ^ 2) * legendreK k ^ 3 / (π ^ 3 * Real.exp (-π * y / 2)) : ℝ) : ℂ) := by
  obtain ⟨hk0, hk1, hk', hKK, e3, e2, e4⟩ := jacobiThetaConstants hy
  have t3 := thetaNull3_pos hy
  have t2 := thetaNull2_pos hy
  have t4 := thetaNull4_pos hy
  have hE := Real.exp_pos (-π * y / 2)
  have R6 : 2 * jacobiModulusOf y * √(1 - jacobiModulusOf y ^ 2) * legendreK (jacobiModulusOf y) ^ 3 /
      (π ^ 3 * Real.exp (-π * y / 2)) =
      (thetaNull2 y * thetaNull3 y * thetaNull4 y) ^ 2 / (4 * Real.exp (-π * y / 2)) := by
    have : (thetaNull2 y * thetaNull3 y * thetaNull4 y) ^ 2 =
        thetaNull2 y ^ 2 * thetaNull3 y ^ 2 * thetaNull4 y ^ 2 := by ring
    rw [this, e3, e2, e4]
    field_simp
    ring
  intro k q
  simp only [k]
  obtain ⟨hqn, hs0, hs12, hs6, hP, hA, hB, hC, h3, h4, h2, hABC⟩ :=
    facts hy q ((Real.exp (-π * y / 24) : ℝ) : ℂ) rfl rfl
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := alg_facts _ _ _ (∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)))
    _ hA hB hC hs0 hABC
  rw [R6]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [h3, h4, h2, ← hs12]
  have hPe : ∏' n : ℕ, (1 - q ^ (2 * (n + 1))) = ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) :=
    tprod_congr fun n ↦ by rw [pow_mul]
  rw [hPe]
  exact a6

end ModularFormsKB.Historical.Jacobi
