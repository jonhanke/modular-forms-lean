import ModularFormsKB.Historical.Kronecker.ThetaE2
import ModularFormsKB.Citation
/-!
# Kronecker's Eisenstein double sums `∑ (mv + nw)^{-2}` (Werke 5, II, arts. VI–VII)

Kronecker, *Werke* 5 (1930), II (*Die Legendre'sche Relation*):

* art. VI, (35)–(36), p. 157: summing with `m` inner ("Eisenstein summation"),
  `∑_{(m,n) ≠ (0,0)} (mv + nw)^{-2} = -(1/(3v²)) ϑ'''(0, εw/v)/ϑ'(0, εw/v) = (π²/(3v²)) E₂(εw/v)`,
  where `ε = ±1` makes `εw/v` lie in the upper half plane;
* art. VII, p. 160: the two special values
  `∑ (m + ni)^{-2} = π` and `∑ (2m - n + ni√3)^{-2} = π/(2√3)`.

In Mathlib the Eisenstein-summed series is `EisensteinSeries.G2 τ = ∑'[symmetricIcc] a, ∑' b, (aτ + b)^{-2}`
(outer index the coefficient of `τ`, summed over symmetric intervals; inner index the constant), and
`E₂ = G₂/(2ζ(2))`. Kronecker's sums are these after `mv + nw = v(m + nτ)`, `τ = w/v`. Lean's convention
`0^{-2} = 0` makes the term `(m, n) = (0, 0)` vanish, so it may stay in the sum. The theorems here are
wrappers of Mathlib's `G₂`, of `kroneckerThetaE2` and of `G2_rho` / `Ramanujan.E2_I`.

Both signs of `ε` are formalized: `KroneckerEisensteinSumFormula` (`ε = 1`, `0 < (w/v).im`) and
`KroneckerEisensteinSumFormulaNeg` (`ε = -1`, `(w/v).im < 0`), the second from the first by the reindexing
`n ↦ -n` of the outer sum, which preserves the symmetric intervals `[-N, N]`.
-/

noncomputable section

open Complex
open scoped Real UpperHalfPlane

namespace ModularFormsKB.Historical.Kronecker

/-- Kronecker's Eisenstein-summed double sum `∑_n ∑_m (mv + nw)^{-2}` (`m` inner; the outer sum over `n` taken
over symmetric intervals `[-N, N]`). -/
def kroneckerEisensteinSum (v w : ℂ) : ℂ :=
  ∑'[SummationFilter.symmetricIcc ℤ] n : ℤ, ∑' m : ℤ, ((m : ℂ) * v + n * w) ^ (-2 : ℤ)

/-- **Kronecker, Werke 5, II art. VI, (35)–(36), p. 157**, case `ε = 1`: for
`v ≠ 0` and `τ = w/v` in the upper half plane,
`∑ (mv + nw)^{-2} = (π²/(3v²)) E₂(τ)` and `= -(1/(3v²)) ϑ'''(0, τ)/ϑ'(0, τ)` (Kronecker's `ϑ`, `kroneckerTheta`). -/
@[kb "kronecker1930" "Werke 5, II art. VI, (35)-(36), p. 157"]
def KroneckerEisensteinSumFormula : Prop :=
  ∀ (v w : ℂ) (_hv : v ≠ 0) (hτ : 0 < (w / v).im),
    kroneckerEisensteinSum v w = (π : ℂ) ^ 2 / (3 * v ^ 2) * EisensteinSeries.E2 ⟨w / v, hτ⟩ ∧
    kroneckerEisensteinSum v w = -(1 / (3 * v ^ 2)) *
      (iteratedDeriv 3 (fun ζ ↦ kroneckerTheta ζ (w / v)) 0 / deriv (fun ζ ↦ kroneckerTheta ζ (w / v)) 0)

/-- **Kronecker, Werke 5, II art. VII, p. 160**: with `m` inner,
`∑ (m + ni)^{-2} = π` and `∑ (2m - n + ni√3)^{-2} = π/(2√3)`. -/
@[kb "kronecker1930" "Werke 5, II art. VII, p. 160"]
def KroneckerEisensteinSumValues : Prop :=
  kroneckerEisensteinSum 1 I = π ∧
  kroneckerEisensteinSum 2 (-1 + ((√3 : ℝ) : ℂ) * I) = π / (2 * (√3 : ℝ))

lemma kroneckerEisensteinSum_eq_G2 (v w : ℂ) (_hv : v ≠ 0) (hτ : 0 < (w / v).im) :
    kroneckerEisensteinSum v w = (v ^ 2)⁻¹ * EisensteinSeries.G2 ⟨w / v, hτ⟩ := by
  unfold kroneckerEisensteinSum EisensteinSeries.G2 EisensteinSeries.e2Summand
  rw [← tsum_mul_left]
  congr 1
  funext n
  rw [← tsum_mul_left]
  congr 1
  funext m
  simp only [EisensteinSeries.eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [show (m : ℂ) * v + n * w = v * (n * (w / v) + m) by field_simp; ring, mul_zpow]
  simp [zpow_neg, zpow_ofNat]

lemma G2_eq_E2 (z : ℍ) : EisensteinSeries.G2 z = (π : ℂ) ^ 2 / 3 * EisensteinSeries.E2 z := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [EisensteinSeries.E2, Pi.smul_apply, smul_eq_mul, riemannZeta_two]
  field_simp
  ring

lemma deriv_kroneckerTheta_ne_zero (w : ℍ) : deriv (fun ζ ↦ kroneckerTheta ζ w) 0 ≠ 0 := by
  have hw : 0 < (w : ℂ).im := w.im_pos
  have h1 := congrFun (iteratedDeriv_kroneckerTheta (w : ℂ) hw 1) 0
  rw [iteratedDeriv_one] at h1
  rw [h1, tsum_gTerm_one hw]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero two_ne_zero hπ) (pow_ne_zero _ (ModularForm.eta_ne_zero hw))

/-- Kronecker, Werke 5, II art. VI, (35)–(36), case `ε = 1`. -/
@[kb "kronecker1930" "Werke 5, II art. VI, (35)-(36), p. 157"]
theorem kroneckerEisensteinSumFormula : KroneckerEisensteinSumFormula := by
  intro v w hv hτ
  have hv2 : v ^ 2 ≠ 0 := pow_ne_zero _ hv
  have hE : kroneckerEisensteinSum v w = (π : ℂ) ^ 2 / (3 * v ^ 2) * EisensteinSeries.E2 ⟨w / v, hτ⟩ := by
    rw [kroneckerEisensteinSum_eq_G2 v w hv hτ, G2_eq_E2]
    field_simp
  refine ⟨hE, ?_⟩
  have hθ := kroneckerThetaE2 ⟨w / v, hτ⟩
  have hd := deriv_kroneckerTheta_ne_zero ⟨w / v, hτ⟩
  rw [hE, hθ]
  field_simp

/-- Kronecker, Werke 5, II art. VII, p. 160. -/
@[kb "kronecker1930" "Werke 5, II art. VII, p. 160"]
theorem kroneckerEisensteinSumValues : KroneckerEisensteinSumValues := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow]; simp
  have hs0 : ((√3 : ℝ) : ℂ) ≠ 0 := by simp
  constructor
  · have hτ : 0 < (I / 1).im := by simp
    rw [kroneckerEisensteinSum_eq_G2 1 I one_ne_zero hτ, G2_eq_E2]
    have : (⟨I / 1, hτ⟩ : ℍ) = UpperHalfPlane.I := by ext; simp
    rw [this, kronecker_E2_I]
    field_simp
  · have hτ : 0 < ((-1 + ((√3 : ℝ) : ℂ) * I) / 2).im := by simp
    rw [kroneckerEisensteinSum_eq_G2 2 _ two_ne_zero hτ]
    have : (⟨(-1 + ((√3 : ℝ) : ℂ) * I) / 2, hτ⟩ : ℍ) = rhoPoint := by
      ext; rw [rhoPoint_coe]; push_cast; ring
    rw [this, G2_rho]
    field_simp

/-- **Kronecker, Werke 5, II art. VI, (35)–(36), p. 157**, case `ε = -1`: for
`v ≠ 0` and `(w/v).im < 0`, with `τ = -w/v` in the upper half plane,
`∑ (mv + nw)^{-2} = (π²/(3v²)) E₂(τ) = -(1/(3v²)) ϑ'''(0, τ)/ϑ'(0, τ)`. -/
@[kb "kronecker1930" "Werke 5, II art. VI, (35)-(36), p. 157"]
def KroneckerEisensteinSumFormulaNeg : Prop :=
  ∀ (v w : ℂ) (_hv : v ≠ 0) (hτ : 0 < (-w / v).im),
    kroneckerEisensteinSum v w = (π : ℂ) ^ 2 / (3 * v ^ 2) * EisensteinSeries.E2 ⟨-w / v, hτ⟩ ∧
    kroneckerEisensteinSum v w = -(1 / (3 * v ^ 2)) *
      (iteratedDeriv 3 (fun ζ ↦ kroneckerTheta ζ (-w / v)) 0 /
        deriv (fun ζ ↦ kroneckerTheta ζ (-w / v)) 0)

lemma hasSum_symmetricIcc_comp_neg {f : ℤ → ℂ} {a : ℂ}
    (h : HasSum f a (SummationFilter.symmetricIcc ℤ)) :
    HasSum (fun n ↦ f (-n)) a (SummationFilter.symmetricIcc ℤ) := by
  unfold HasSum at h ⊢
  rw [SummationFilter.symmetricIcc_filter, Filter.tendsto_map'_iff] at h ⊢
  refine h.congr fun N ↦ ?_
  simp only [Function.comp]
  refine Finset.sum_nbij' (fun b ↦ -b) (fun b ↦ -b) ?_ ?_ ?_ ?_ ?_
  · intro b hb; simp only [Finset.mem_Icc] at hb ⊢; omega
  · intro b hb; simp only [Finset.mem_Icc] at hb ⊢; omega
  · intro b _; simp
  · intro b _; simp
  · intro b _; simp

lemma hasSum_kronecker_inner (v w : ℂ) (hv : v ≠ 0) (hτ : 0 < (w / v).im) :
    HasSum (fun n : ℤ ↦ ∑' m : ℤ, ((m : ℂ) * v + n * w) ^ (-2 : ℤ))
      ((v ^ 2)⁻¹ * EisensteinSeries.G2 ⟨w / v, hτ⟩) (SummationFilter.symmetricIcc ℤ) := by
  set z : ℍ := ⟨w / v, hτ⟩ with hz
  have hS : Summable (fun m ↦ EisensteinSeries.e2Summand m z) (SummationFilter.symmetricIcc ℤ) :=
    (EisensteinSeries.hasSum_e2Summand_symmetricIcc z).summable
  have hG : HasSum (fun m ↦ EisensteinSeries.e2Summand m z) (EisensteinSeries.G2 z)
      (SummationFilter.symmetricIcc ℤ) := hS.hasSum
  have hterm : ∀ n : ℤ, ∑' m : ℤ, ((m : ℂ) * v + n * w) ^ (-2 : ℤ) =
      (v ^ 2)⁻¹ * EisensteinSeries.e2Summand n z := by
    intro n
    unfold EisensteinSeries.e2Summand
    rw [← tsum_mul_left]
    congr 1
    funext m
    simp only [EisensteinSeries.eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hz]
    change _ = (v ^ 2)⁻¹ * ((n : ℂ) * (w / v) + m) ^ (-(2 : ℤ))
    rw [show (m : ℂ) * v + n * w = v * (n * (w / v) + m) by field_simp; ring, mul_zpow]
    simp [zpow_neg, zpow_ofNat]
  simp_rw [hterm]
  exact hG.mul_left _

lemma kroneckerEisensteinSum_neg (v w : ℂ) (hv : v ≠ 0) (hτ : 0 < (-w / v).im) :
    kroneckerEisensteinSum v w = kroneckerEisensteinSum v (-w) := by
  have hsum := hasSum_kronecker_inner v (-w) hv hτ
  have hneg := hasSum_symmetricIcc_comp_neg hsum
  unfold kroneckerEisensteinSum
  calc ∑'[SummationFilter.symmetricIcc ℤ] n : ℤ, ∑' m : ℤ, ((m : ℂ) * v + n * w) ^ (-2 : ℤ)
      = ∑'[SummationFilter.symmetricIcc ℤ] n : ℤ,
          ∑' m : ℤ, ((m : ℂ) * v + ((-n : ℤ) : ℂ) * (-w)) ^ (-2 : ℤ) := by
        simp only [Int.cast_neg, neg_mul_neg]
    _ = _ := hneg.tsum_eq
    _ = _ := hsum.tsum_eq.symm

/-- Kronecker, Werke 5, II art. VI, (35)–(36), case `ε = -1`. -/
@[kb "kronecker1930" "Werke 5, II art. VI, (35)-(36), p. 157"]
theorem kroneckerEisensteinSumFormulaNeg : KroneckerEisensteinSumFormulaNeg := by
  intro v w hv hτ
  have hτ' : 0 < ((-w) / v).im := hτ
  rw [kroneckerEisensteinSum_neg v w hv hτ]
  exact kroneckerEisensteinSumFormula v (-w) hv hτ'

end ModularFormsKB.Historical.Kronecker
