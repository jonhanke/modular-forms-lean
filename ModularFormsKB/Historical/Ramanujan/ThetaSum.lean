import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import ModularFormsKB.Citation
/-!
# Ramanujan's Question 629 (ii)

Ramanujan, Question 629 (J. Indian Math. Soc. 7, p. 40; *Collected Papers*, p. 330), (ii):
`∑_{n ≥ 1} e^{-πn²} (πn² - 1/4) = 1/8`.

It follows by differentiating `ϑ(1/x) = √x ϑ(x)`, `ϑ(x) = ∑_{n ∈ ℤ} e^{-πn²x}`, at `x = 1`.
-/

noncomputable section

open Real HurwitzZeta

namespace ModularFormsKB.Historical.Ramanujan

/-- **Ramanujan, Question 629 (ii)** (*Collected Papers*, p. 330):
`∑_{n ≥ 1} e^{-πn²} (πn² - 1/4) = 1/8`. The index is shifted to start at `0`. -/
@[kb "ramanujan1927" "Question 629 (ii), p. 330"]
def Question629 : Prop :=
  HasSum (fun n : ℕ ↦ Real.exp (-π * ((n : ℝ) + 1) ^ 2) * (π * ((n : ℝ) + 1) ^ 2 - 1 / 4)) (1 / 8)

/-- `∑_{n ∈ ℤ} e^{-π n² x}` as a function of `x`. -/
private def thetaH (x : ℝ) : ℝ := ∑' n : ℤ, rexp (-π * (n : ℝ) ^ 2 * x)

private lemma hasSum_thetaH {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℤ ↦ rexp (-π * (n : ℝ) ^ 2 * x)) (thetaH x) := by
  have := hasSum_int_evenKernel 0 hx
  have e : evenKernel 0 x = thetaH x := by
    simpa [thetaH] using this.tsum_eq.symm
  rw [← e]
  simpa using this

private lemma even_eq {x : ℝ} (hx : 0 < x) : evenKernel 0 x = thetaH x := by
  simpa [thetaH] using (hasSum_int_evenKernel 0 hx).tsum_eq.symm

private lemma thetaH_functional {x : ℝ} (hx : 0 < x) :
    thetaH (1 / x) = x ^ (1 / 2 : ℝ) * thetaH x := by
  have h1 := evenKernel_functional_equation 0 x
  rw [← evenKernel_eq_cosKernel_of_zero, even_eq hx, even_eq (by positivity)] at h1
  have hp : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  rw [h1]
  field_simp

private lemma hasDerivAt_thetaH :
    Summable (fun n : ℤ ↦ (-π * (n : ℝ) ^ 2) * rexp (-π * (n : ℝ) ^ 2 * 1)) ∧
    HasDerivAt thetaH (∑' n : ℤ, (-π * (n : ℝ) ^ 2) * rexp (-π * (n : ℝ) ^ 2 * 1)) 1 := by
  have hu0 := summable_pow_mul_jacobiTheta₂_term_bound 0 (T := 1 / 2) (by norm_num) 2
  have hu := hu0.mul_left π
  set g : ℤ → ℝ → ℝ := fun n x ↦ rexp (-π * (n : ℝ) ^ 2 * x) with hg_def
  set g' : ℤ → ℝ → ℝ := fun n x ↦ (-π * (n : ℝ) ^ 2) * rexp (-π * (n : ℝ) ^ 2 * x) with hg'_def
  have hg : ∀ n y, y ∈ Set.Ioi (1 / 2 : ℝ) → HasDerivAt (g n) (g' n y) y := by
    intro n y _
    have := ((hasDerivAt_id y).const_mul (-π * (n : ℝ) ^ 2)).exp
    simpa [hg_def, hg'_def, mul_comm] using this
  have hg' : ∀ n y, y ∈ Set.Ioi (1 / 2 : ℝ) → ‖g' n y‖ ≤ π * ((((|n| : ℤ) : ℝ) ^ 2 : ℝ) *
        rexp (-π * ((1 / 2) * (n : ℝ) ^ 2 - 2 * 0 * ((|n| : ℤ) : ℝ)))) := by
    intro n y hy
    have hy' : (1 / 2 : ℝ) < y := hy
    simp only [hg'_def]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonpos (by nlinarith [Real.pi_pos, sq_nonneg (n : ℝ)])]
    have : ((|n| : ℤ) : ℝ) ^ 2 = (n : ℝ) ^ 2 := by rw [Int.cast_abs]; exact sq_abs _
    have h2 : rexp (-π * (n : ℝ) ^ 2 * y) ≤ rexp (-π * ((1 / 2) * (n : ℝ) ^ 2 - 2 * 0 * ((|n| : ℤ) : ℝ))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos, sq_nonneg (n : ℝ), mul_nonneg Real.pi_pos.le (sq_nonneg (n : ℝ))]
    rw [this]
    nlinarith [Real.pi_pos, sq_nonneg (n : ℝ), mul_nonneg Real.pi_pos.le (sq_nonneg (n : ℝ))]
  have hsum : Summable fun n ↦ g' n 1 :=
    Summable.of_norm_bounded hu (fun n ↦ hg' n 1 (by norm_num))
  have hs1 : Summable fun n ↦ g n 1 := (hasSum_thetaH one_pos).summable
  have := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi isPreconnected_Ioi hg hg'
    (show (1 : ℝ) ∈ Set.Ioi (1 / 2 : ℝ) by norm_num) hs1
    (show (1 : ℝ) ∈ Set.Ioi (1 / 2 : ℝ) by norm_num)
  have e : thetaH = fun z ↦ ∑' n, g n z := rfl
  rw [e]
  exact ⟨hsum, this⟩

private lemma half_sum {f : ℤ → ℝ} {m : ℝ} (hf : HasSum f m) (heven : ∀ n, f (-n) = f n) :
    HasSum (fun n : ℕ ↦ f ((n : ℤ) + 1)) ((m - f 0) / 2) := by
  have h := hf.nat_add_neg
  have h2 := (hasSum_nat_add_iff' 1).mpr h
  have h3 := h2.div_const 2
  convert h3 using 1
  · funext n
    have e : f (-((n + 1 : ℕ) : ℤ)) = f ((n + 1 : ℕ) : ℤ) := heven _
    rw [e]
    push_cast
    ring
  · simp [heven]

/-- Ramanujan, Question 629 (ii). -/
@[kb "ramanujan1927" "Question 629 (ii), p. 330"]
theorem question629 : Question629 := by
  obtain ⟨hsumD, hD⟩ := hasDerivAt_thetaH
  set D := ∑' n : ℤ, (-π * (n : ℝ) ^ 2) * rexp (-π * (n : ℝ) ^ 2 * 1) with hDdef
  have hD' : HasDerivAt thetaH D (1 : ℝ)⁻¹ := by rwa [inv_one]
  have hA := hD'.comp (1 : ℝ) (hasDerivAt_inv (one_ne_zero (α := ℝ)))
  have hB := ((Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := 1 / 2) (Or.inl one_ne_zero))).mul hD
  have heq : ((fun x : ℝ ↦ x ^ (1 / 2 : ℝ)) * thetaH) =ᶠ[nhds 1] (thetaH ∘ fun x : ℝ ↦ x⁻¹) := by
    filter_upwards [Ioi_mem_nhds (one_pos : (0 : ℝ) < 1)] with x hx
    simp only [Pi.mul_apply, Function.comp, ← one_div]
    exact (thetaH_functional hx).symm
  have hB' := hB.congr_of_eventuallyEq heq.symm
  have hu := hB'.unique hA
  simp only [Real.one_rpow, one_pow, inv_one] at hu
  have hDv : D = -thetaH 1 / 4 := by
    norm_num at hu
    linarith
  have f1 := hasSum_thetaH one_pos
  have h1 := half_sum f1 (fun n ↦ by simp)
  have f2 := hsumD.hasSum
  have h2 := half_sum f2 (fun n ↦ by simp)
  have h3 := (h2.neg).sub (h1.div_const 4)
  unfold Question629
  show HasSum (fun n : ℕ ↦ Real.exp (-π * ((n : ℝ) + 1) ^ 2) *
    (π * ((n : ℝ) + 1) ^ 2 - 1 / 4)) (1 / 8)
  convert h3 using 1
  · funext n
    push_cast
    ring_nf
  · rw [← hDdef, hDv]
    simp
    ring


end ModularFormsKB.Historical.Ramanujan