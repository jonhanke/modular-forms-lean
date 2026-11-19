import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

/-!
# Lattice theta series $\sum_p c(p)\,v_p^\lambda e^{-\pi u|v_p|^2}$: convergence, bounds, Mellin transform

Tools for `EisensteinFE.lean`. For $a \ge 1$, $z = x + iy \in \mathbf H$ and $p = (p_1,p_2) \in \mathbb Z^2$ put
$v_p = ap_1z + p_2$ (`genVec`). For a bounded weight $c : \mathbb Z^2 \to \mathbb C$ and $\lambda \ge 1$,
$$\Theta(z,u) = \sum_p c(p)\,v_p^\lambda e^{-\pi u|v_p|^2} \quad (u > 0), \qquad
S(z,\sigma) = \sum_p c(p)\,v_p^\lambda|v_p|^{-2\sigma} \quad (\operatorname{Re}\sigma > 1 + \lambda/2).$$
The term $p = 0$ vanishes ($\lambda \ge 1$). Bounds: $|\Theta(z,u)| \le B(1+y^{-2})e^{-\pi(u-1)\min(1,y^2)}$ for $u \ge 1$
(uniformly in $x$), and $|\Theta(z,u)| \le B(y^A + y^{-A})u^{-\lambda-1}$ for $0 < u \le 1$. Mellin transform:
$\int_0^\infty\Theta(z,u)u^{\sigma-1}du = \Gamma(\sigma)\pi^{-\sigma}S(z,\sigma)$.
-/

open MeasureTheory Set Filter Topology Complex Asymptotics
open scoped UpperHalfPlane
open scoped Real

noncomputable section

namespace ModularFormsKB.Miyake.HeckeTrick

/-- The lattice vector $v_p = ap_1z + p_2$. -/
def genVec (a : ℕ) (z : ℍ) (p : ℤ × ℤ) : ℂ := (a : ℂ) * p.1 * z + p.2

/-- The theta series $\Theta(z,u) = \sum_p c(p)\,v_p^\lambda e^{-\pi u|v_p|^2}$.
**Restriction:** the series converges for $u > 0$ and $a \ge 1$ when $c$ has at most polynomial growth (for $u \le 0$ it
diverges unless $c$ decays fast). Elsewhere the value is $0$ by Lean's convention for a non-summable `∑'`, not an
analytic continuation or the intended value. -/
def genTheta (a lam : ℕ) (c : ℤ × ℤ → ℂ) (z : ℍ) (u : ℝ) : ℂ :=
  ∑' p : ℤ × ℤ, c p * genVec a z p ^ lam * ((Real.exp (-π * u * ‖genVec a z p‖ ^ 2) : ℝ) : ℂ)

/-- The lattice sum $S(z,\sigma) = \sum_p c(p)\,v_p^\lambda|v_p|^{-2\sigma}$.
**Restriction:** the lattice sum converges absolutely for $\operatorname{Re}\sigma > (\lambda + 2)/2$ when $c$ is
bounded and $a \ge 1$ (terms of size $|v_p|^{\lambda - 2\operatorname{Re}\sigma}$). Elsewhere the value is $0$ by
Lean's convention for a non-summable `∑'`, not an analytic continuation or the intended value. -/
def genSeries (a lam : ℕ) (c : ℤ × ℤ → ℂ) (z : ℍ) (σ : ℂ) : ℂ :=
  ∑' p : ℤ × ℤ, c p * genVec a z p ^ lam * ((‖genVec a z p‖ : ℝ) : ℂ) ^ (-2 * σ)

/-! ### One-dimensional Gaussian sums -/

/-- The theta constant $\sum_n e^{-\pi n^2}$. -/
def gaussT : ℝ := ∑' n : ℤ, Real.exp (-π * 1 * (n : ℝ) ^ 2)

theorem summable_gauss {β : ℝ} (hβ : 0 < β) :
    Summable fun n : ℤ ↦ Real.exp (-π * β * (n : ℝ) ^ 2) := by
  rw [summable_int_iff_summable_nat_and_neg]
  have key : Summable fun n : ℕ ↦ Real.exp (-π * β * (n : ℝ) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n ↦ (Real.exp_pos _).le) (fun n ↦ ?_)
      (summable_geometric_of_lt_one (r := Real.exp (-π * β)) (by positivity)
        (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])))
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith
    nlinarith [Real.pi_pos, mul_pos Real.pi_pos hβ]
  refine ⟨key, ?_⟩
  simpa using key

theorem gaussT_nonneg : 0 ≤ gaussT := tsum_nonneg (fun _ ↦ (Real.exp_pos _).le)

theorem tsum_gauss_le {β : ℝ} (hβ : 0 < β) :
    ∑' n : ℤ, Real.exp (-π * β * (n : ℝ) ^ 2) ≤ gaussT * (1 + 1 / Real.sqrt β) := by
  have hT := gaussT_nonneg
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  rcases le_or_gt 1 β with h | h
  · calc _ ≤ gaussT := by
          refine Summable.tsum_le_tsum (fun n ↦ ?_) (summable_gauss hβ) (summable_gauss one_pos)
          apply Real.exp_le_exp.2
          nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg (n : ℝ)),
            mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg (n : ℝ))) (sub_nonneg.2 h)]
      _ ≤ _ := by
          have : 0 ≤ 1 / Real.sqrt β := by positivity
          nlinarith
  · rw [Real.tsum_exp_neg_mul_int_sq hβ]
    have hb : (1 : ℝ) ≤ 1 / β := by rw [le_div_iff₀ hβ]; linarith
    have h2 : ∑' n : ℤ, Real.exp (-π / β * (n : ℝ) ^ 2) ≤ gaussT := by
      have hsm : Summable fun n : ℤ ↦ Real.exp (-π / β * (n : ℝ) ^ 2) := by
        have := summable_gauss (β := 1 / β) (by positivity)
        refine this.congr (fun n ↦ ?_)
        congr 2; ring
      refine Summable.tsum_le_tsum (fun n ↦ ?_) hsm (summable_gauss one_pos)
      apply Real.exp_le_exp.2
      have : -π / β = -π * (1 / β) := by ring
      rw [this]
      nlinarith [Real.pi_pos, sq_nonneg (n : ℝ), mul_nonneg Real.pi_pos.le (sq_nonneg (n : ℝ))]
    have hr : (1 : ℝ) / β ^ (1 / 2 : ℝ) = 1 / Real.sqrt β := by rw [Real.sqrt_eq_rpow]
    rw [hr]
    have : 0 ≤ 1 / Real.sqrt β := by positivity
    calc 1 / Real.sqrt β * ∑' n : ℤ, Real.exp (-π / β * (n : ℝ) ^ 2) ≤ 1 / Real.sqrt β * gaussT :=
          by gcongr
      _ ≤ _ := by nlinarith

theorem gauss_shift_le (t : ℝ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (n : ℤ) :
    Real.exp (-π * s * (t + n) ^ 2) ≤
      Real.exp (π / 4) * Real.exp (-π * (s / 2) * ((n + round t : ℤ) : ℝ) ^ 2) := by
  have h0 : |t - round t| ≤ 1 / 2 := abs_sub_round t
  set t₀ := t - round t with ht₀
  have h1 : t₀ ^ 2 ≤ 1 / 4 := by
    have := abs_le.1 h0
    nlinarith [this.1, this.2]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have e : t + n = t₀ + ((n + round t : ℤ) : ℝ) := by
    rw [ht₀]; push_cast; ring
  rw [e]
  set m : ℝ := ((n + round t : ℤ) : ℝ)
  have : (t₀ + m) ^ 2 ≥ m ^ 2 / 2 - 1 / 4 := by nlinarith [sq_nonneg (t₀ + m / 2)]
  have hp := Real.pi_pos
  have hsm : s * ((t₀ + m) ^ 2) ≥ s * (m ^ 2 / 2 - 1 / 4) := mul_le_mul_of_nonneg_left this hs.le
  have : s ≤ 1 := hs1
  nlinarith [mul_le_mul_of_nonneg_left hsm hp.le, mul_nonneg hp.le (sub_nonneg.2 hs1)]

theorem sqrt_half_ge {s : ℝ} (hs : 0 < s) : Real.sqrt s / 2 ≤ Real.sqrt (s / 2) := by
  apply Real.le_sqrt_of_sq_le
  rw [div_pow, Real.sq_sqrt hs.le]; linarith

theorem summable_gauss_shift (t : ℝ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Summable fun n : ℤ ↦ Real.exp (-π * s * (t + n) ^ 2) := by
  have hs' : 0 < s / 2 := by positivity
  have hG : Summable fun m : ℤ ↦ Real.exp (π / 4) * Real.exp (-π * (s / 2) * (m : ℝ) ^ 2) :=
    (summable_gauss hs').mul_left _
  have hG' := (Equiv.addRight (round t)).summable_iff.2 hG
  exact Summable.of_nonneg_of_le (fun n ↦ (Real.exp_pos _).le)
    (fun n ↦ gauss_shift_le t hs hs1 n) hG'

theorem tsum_gauss_shift_le (t : ℝ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∑' n : ℤ, Real.exp (-π * s * (t + n) ^ 2) ≤
      3 * Real.exp (π / 4) * gaussT * (1 / Real.sqrt s) := by
  have hs' : 0 < s / 2 := by positivity
  have hG : Summable fun m : ℤ ↦ Real.exp (π / 4) * Real.exp (-π * (s / 2) * (m : ℝ) ^ 2) :=
    (summable_gauss hs').mul_left _
  have hG' := (Equiv.addRight (round t)).summable_iff.2 hG
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hsq1 : Real.sqrt s ≤ 1 := by
    rw [Real.sqrt_le_one]; exact hs1
  have h3 : 1 + 1 / Real.sqrt (s / 2) ≤ 3 * (1 / Real.sqrt s) := by
    have h1 : 1 / Real.sqrt (s / 2) ≤ 1 / (Real.sqrt s / 2) :=
      one_div_le_one_div_of_le (by positivity) (sqrt_half_ge hs)
    have h2 : 1 / (Real.sqrt s / 2) = 2 * (1 / Real.sqrt s) := by field_simp
    have h4 : 1 ≤ 1 / Real.sqrt s := by rw [le_div_iff₀ hsq]; linarith
    linarith
  calc ∑' n : ℤ, Real.exp (-π * s * (t + n) ^ 2)
      ≤ ∑' n : ℤ, (fun m : ℤ ↦ Real.exp (π / 4) * Real.exp (-π * (s / 2) * (m : ℝ) ^ 2))
          (n + round t) :=
        Summable.tsum_le_tsum (fun n ↦ gauss_shift_le t hs hs1 n)
          (summable_gauss_shift t hs hs1) hG'
    _ = ∑' m : ℤ, Real.exp (π / 4) * Real.exp (-π * (s / 2) * (m : ℝ) ^ 2) :=
        (Equiv.addRight (round t)).tsum_eq
          (fun m : ℤ ↦ Real.exp (π / 4) * Real.exp (-π * (s / 2) * (m : ℝ) ^ 2))
    _ = Real.exp (π / 4) * ∑' m : ℤ, Real.exp (-π * (s / 2) * (m : ℝ) ^ 2) := tsum_mul_left
    _ ≤ Real.exp (π / 4) * (gaussT * (1 + 1 / Real.sqrt (s / 2))) := by
        gcongr; exact tsum_gauss_le hs'
    _ ≤ Real.exp (π / 4) * (gaussT * (3 * (1 / Real.sqrt s))) := by
        have := gaussT_nonneg
        gcongr
    _ = _ := by ring


/-! ### Two-dimensional Gaussian lattice sums -/

theorem genVec_normSq (a : ℕ) (z : ℍ) (p : ℤ × ℤ) :
    ‖genVec a z p‖ ^ 2 = ((a : ℝ) * p.1 * z.re + p.2) ^ 2 + ((a : ℝ) * p.1 * z.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [genVec]
  ring

theorem gauss_fiber_eq (a : ℕ) (z : ℍ) (s : ℝ) (c n : ℤ) :
    Real.exp (-π * s * ‖genVec a z (c, n)‖ ^ 2) =
      Real.exp (-π * (s * ((a : ℝ) * z.im) ^ 2) * (c : ℝ) ^ 2) *
        Real.exp (-π * s * (((a : ℝ) * c * z.re) + n) ^ 2) := by
  rw [← Real.exp_add, genVec_normSq]
  congr 1
  ring

/-- The constant in the Gaussian lattice sum bound. -/
def gaussK : ℝ := 3 * Real.exp (π / 4) * gaussT ^ 2

theorem gauss_lattice {a : ℕ} (ha : 1 ≤ a) (z : ℍ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Summable (fun p : ℤ × ℤ ↦ Real.exp (-π * s * ‖genVec a z p‖ ^ 2)) ∧
    ∑' p : ℤ × ℤ, Real.exp (-π * s * ‖genVec a z p‖ ^ 2) ≤
      gaussK * (1 / s) * (1 + z.im⁻¹) := by
  have hy := z.im_pos
  have ha' : (1 : ℝ) ≤ a := Nat.one_le_cast.2 ha
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hsq1 : Real.sqrt s ≤ 1 := by rw [Real.sqrt_le_one]; exact hs1
  have hT := gaussT_nonneg
  set R : ℝ := 3 * Real.exp (π / 4) * gaussT * (1 / Real.sqrt s) with hR
  have hR0 : 0 ≤ R := by positivity
  set e1 : ℤ → ℝ := fun c ↦ Real.exp (-π * (s * ((a : ℝ) * z.im) ^ 2) * (c : ℝ) ^ 2) with he1
  have hay : 0 < s * ((a : ℝ) * z.im) ^ 2 := by positivity
  have he1s : Summable e1 := summable_gauss hay
  set f : ℤ × ℤ → ℝ := fun p ↦ Real.exp (-π * s * ‖genVec a z p‖ ^ 2) with hf
  have hf0 : 0 ≤ f := fun p ↦ (Real.exp_pos _).le
  have hfib : ∀ c : ℤ, Summable fun n : ℤ ↦ f (c, n) := fun c ↦ by
    have := (summable_gauss_shift ((a : ℝ) * c * z.re) hs hs1).mul_left (e1 c)
    refine this.congr (fun n ↦ ?_)
    simp only [hf, he1]
    rw [gauss_fiber_eq]
  have hfibsum : ∀ c : ℤ, ∑' n : ℤ, f (c, n) ≤ e1 c * R := fun c ↦ by
    have : ∑' n : ℤ, f (c, n) = e1 c * ∑' n : ℤ,
        Real.exp (-π * s * (((a : ℝ) * c * z.re) + n) ^ 2) := by
      rw [← tsum_mul_left]
      refine tsum_congr (fun n ↦ ?_)
      simp only [hf, he1]
      rw [gauss_fiber_eq]
    rw [this]
    have := tsum_gauss_shift_le ((a : ℝ) * c * z.re) hs hs1
    have h1 : 0 ≤ e1 c := (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_left this h1
  have hout : Summable fun c : ℤ ↦ ∑' n : ℤ, f (c, n) :=
    Summable.of_nonneg_of_le (fun c ↦ tsum_nonneg (fun n ↦ hf0 _)) hfibsum (he1s.mul_right R)
  have hsum : Summable f := (summable_prod_of_nonneg hf0).2 ⟨hfib, hout⟩
  refine ⟨hsum, ?_⟩
  rw [hsum.tsum_prod' hfib]
  calc ∑' c : ℤ, ∑' n : ℤ, f (c, n) ≤ ∑' c : ℤ, e1 c * R :=
        Summable.tsum_le_tsum hfibsum hout (he1s.mul_right R)
    _ = (∑' c : ℤ, e1 c) * R := tsum_mul_right
    _ ≤ (gaussT * (1 + 1 / Real.sqrt (s * ((a : ℝ) * z.im) ^ 2))) * R := by
        gcongr; exact tsum_gauss_le hay
    _ ≤ (gaussT * ((1 / Real.sqrt s) * (1 + z.im⁻¹))) * R := by
        gcongr
        have h1 : Real.sqrt (s * ((a : ℝ) * z.im) ^ 2) = Real.sqrt s * ((a : ℝ) * z.im) := by
          rw [Real.sqrt_mul hs.le, Real.sqrt_sq (by positivity)]
        rw [h1]
        have h2 : 1 / (Real.sqrt s * ((a : ℝ) * z.im)) ≤ 1 / (Real.sqrt s * z.im) :=
          one_div_le_one_div_of_le (by positivity) (by nlinarith [mul_pos hsq hy])
        have h3 : 1 ≤ 1 / Real.sqrt s := by rw [le_div_iff₀ hsq]; linarith
        have h4 : 1 / (Real.sqrt s * z.im) = (1 / Real.sqrt s) * z.im⁻¹ := by field_simp
        nlinarith
    _ = gaussK * (1 / s) * (1 + z.im⁻¹) := by
        have : (1 / Real.sqrt s) * (1 / Real.sqrt s) = 1 / s := by
          rw [one_div_mul_one_div, Real.mul_self_sqrt hs.le]
        simp only [hR, gaussK]
        rw [← this]
        ring

theorem pow_exp_le (lam : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    w ^ lam * Real.exp (-π * w ^ 2 / 2) ≤ (lam.factorial : ℝ) := by
  have hf : (1 : ℝ) ≤ lam.factorial := Nat.one_le_cast.2 (Nat.factorial_pos _)
  have hx : 0 ≤ π * w ^ 2 / 2 := by positivity
  have hE := Real.pow_div_factorial_le_exp (π * w ^ 2 / 2) hx lam
  have hfp : (0 : ℝ) < lam.factorial := by linarith
  have key : w ^ lam ≤ (lam.factorial : ℝ) * Real.exp (π * w ^ 2 / 2) := by
    rcases le_or_gt w 1 with h | h
    · have h1 : w ^ lam ≤ 1 := pow_le_one₀ hw h
      have h2 : (1 : ℝ) ≤ Real.exp (π * w ^ 2 / 2) := Real.one_le_exp hx
      nlinarith
    · have h1 : w ^ lam ≤ (w ^ 2) ^ lam := by
        rw [← pow_mul]
        exact pow_le_pow_right₀ h.le (by omega)
      have h2 : (w ^ 2) ^ lam ≤ (π * w ^ 2 / 2) ^ lam := by
        apply pow_le_pow_left₀ (by positivity)
        nlinarith [Real.two_le_pi, sq_nonneg w]
      have h3 : (π * w ^ 2 / 2) ^ lam ≤ (lam.factorial : ℝ) * Real.exp (π * w ^ 2 / 2) := by
        rw [div_le_iff₀ hfp] at hE
        linarith
      linarith
  have : Real.exp (-π * w ^ 2 / 2) = (Real.exp (π * w ^ 2 / 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [this, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  linarith

theorem term_norm (c : ℤ × ℤ → ℂ) (a lam : ℕ) (z : ℍ) (u : ℝ) (p : ℤ × ℤ) :
    ‖c p * genVec a z p ^ lam * ((Real.exp (-π * u * ‖genVec a z p‖ ^ 2) : ℝ) : ℂ)‖ =
      ‖c p‖ * ‖genVec a z p‖ ^ lam * Real.exp (-π * u * ‖genVec a z p‖ ^ 2) := by
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem term_le (a lam : ℕ) {c : ℤ × ℤ → ℂ} {C : ℝ} (hc : ∀ p, ‖c p‖ ≤ C) (z : ℍ) {u : ℝ}
    (hu : 0 < u) (p : ℤ × ℤ) :
    ‖c p * genVec a z p ^ lam * ((Real.exp (-π * u * ‖genVec a z p‖ ^ 2) : ℝ) : ℂ)‖ *
        (Real.sqrt u) ^ lam ≤
      C * lam.factorial * Real.exp (-π * (u / 2) * ‖genVec a z p‖ ^ 2) := by
  rw [term_norm]
  set r := ‖genVec a z p‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hsq : 0 ≤ Real.sqrt u := Real.sqrt_nonneg _
  have hw : (Real.sqrt u * r) ^ 2 = u * r ^ 2 := by rw [mul_pow, Real.sq_sqrt hu.le]
  have h1 := pow_exp_le lam (mul_nonneg hsq hr0)
  rw [hw] at h1
  have e : Real.exp (-π * u * r ^ 2) =
      Real.exp (-π * (u * r ^ 2) / 2) * Real.exp (-π * (u / 2) * r ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : ‖c p‖ ≤ C := hc p
  have h3 : 0 ≤ Real.exp (-π * (u / 2) * r ^ 2) := (Real.exp_pos _).le
  calc ‖c p‖ * r ^ lam * Real.exp (-π * u * r ^ 2) * Real.sqrt u ^ lam
      = ‖c p‖ * ((Real.sqrt u * r) ^ lam * Real.exp (-π * (u * r ^ 2) / 2)) *
          Real.exp (-π * (u / 2) * r ^ 2) := by rw [e, mul_pow]; ring
    _ ≤ C * lam.factorial * Real.exp (-π * (u / 2) * r ^ 2) := by
        have h4 : 0 ≤ (Real.sqrt u * r) ^ lam * Real.exp (-π * (u * r ^ 2) / 2) := by positivity
        have := mul_le_mul h2 h1 h4 ((norm_nonneg _).trans h2)
        exact mul_le_mul_of_nonneg_right this h3

theorem rpow_neg_lam_sub_one (lam : ℕ) {u : ℝ} (hu : 0 < u) :
    u ^ (-(lam : ℝ) - 1) = 1 / (u ^ lam * u) := by
  rw [Real.rpow_sub hu, Real.rpow_neg hu.le, Real.rpow_natCast, Real.rpow_one]
  field_simp

variable {a lam : ℕ} {c : ℤ × ℤ → ℂ} {C : ℝ}

theorem summable_norm_term (ha : 1 ≤ a) (hc : ∀ p, ‖c p‖ ≤ C) (z : ℍ) {u : ℝ} (hu : 0 < u) :
    Summable fun p : ℤ × ℤ ↦
      ‖c p * genVec a z p ^ lam * ((Real.exp (-π * u * ‖genVec a z p‖ ^ 2) : ℝ) : ℂ)‖ := by
  have hq : 0 < Real.sqrt u ^ lam := by positivity
  have hs : 0 < min (u / 2) 1 := lt_min (by positivity) one_pos
  have hF := (gauss_lattice (a := a) ha z hs (min_le_right _ _)).1
  have hC : 0 ≤ C := (norm_nonneg _).trans (hc 0)
  refine Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _) (fun p ↦ ?_)
    (hF.mul_left (C * lam.factorial / Real.sqrt u ^ lam))
  have h1 := term_le a lam hc z hu p
  have h2 : Real.exp (-π * (u / 2) * ‖genVec a z p‖ ^ 2) ≤
      Real.exp (-π * min (u / 2) 1 * ‖genVec a z p‖ ^ 2) := by
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_pos, sq_nonneg ‖genVec a z p‖, min_le_left (u / 2) 1,
      mul_nonneg Real.pi_pos.le (sq_nonneg ‖genVec a z p‖)]
  rw [div_mul_eq_mul_div, le_div_iff₀ hq]
  refine h1.trans ?_
  have : 0 ≤ C * lam.factorial := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 this]

theorem tsum_norm_term_le (ha : 1 ≤ a) (hc : ∀ p, ‖c p‖ ≤ C) :
    ∃ B > (0 : ℝ), ∀ (z : ℍ) (u : ℝ), 0 < u → u ≤ 1 →
      ∑' p : ℤ × ℤ, ‖c p * genVec a z p ^ lam *
          ((Real.exp (-π * u * ‖genVec a z p‖ ^ 2) : ℝ) : ℂ)‖ ≤
        B * (1 + z.im⁻¹) * u ^ (-(lam : ℝ) - 1) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hc 0)
  have hK : 0 ≤ gaussK := by unfold gaussK; have := gaussT_nonneg; positivity
  refine ⟨2 * C * lam.factorial * gaussK + 1, by positivity, fun z u hu hu1 ↦ ?_⟩
  have hq : 0 < Real.sqrt u ^ lam := by positivity
  have hs : 0 < u / 2 := by positivity
  have hF := gauss_lattice (a := a) ha z hs (by linarith)
  have hsum := summable_norm_term (lam := lam) (c := c) ha hc z hu
  have hbd : ∀ p : ℤ × ℤ, ‖c p * genVec a z p ^ lam *
      ((Real.exp (-π * u * ‖genVec a z p‖ ^ 2) : ℝ) : ℂ)‖ ≤
      (C * lam.factorial / Real.sqrt u ^ lam) *
        Real.exp (-π * (u / 2) * ‖genVec a z p‖ ^ 2) := fun p ↦ by
    rw [div_mul_eq_mul_div, le_div_iff₀ hq]
    exact term_le a lam hc z hu p
  have h1 := Summable.tsum_le_tsum hbd hsum (hF.1.mul_left _)
  rw [tsum_mul_left] at h1
  refine h1.trans ?_
  have h2 := mul_le_mul_of_nonneg_left hF.2 (by positivity : 0 ≤ C * lam.factorial / Real.sqrt u ^ lam)
  refine h2.trans ?_
  rw [rpow_neg_lam_sub_one lam hu]
  have hy : 0 ≤ 1 + z.im⁻¹ := by have := z.im_pos; positivity
  have hsqu : u ≤ Real.sqrt u := by
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hpow : u ^ lam ≤ Real.sqrt u ^ lam := pow_le_pow_left₀ hu.le hsqu lam
  have hup : 0 < u ^ lam := by positivity
  have e : C * lam.factorial / Real.sqrt u ^ lam * (gaussK * (1 / (u / 2)) * (1 + z.im⁻¹)) =
      (2 * C * lam.factorial * gaussK) * (1 + z.im⁻¹) * (1 / (Real.sqrt u ^ lam * u)) := by
    field_simp
  rw [e]
  have h5 : 1 / (Real.sqrt u ^ lam * u) ≤ 1 / (u ^ lam * u) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have h6 : 0 ≤ (2 * C * lam.factorial * gaussK) * (1 + z.im⁻¹) := by positivity
  have h7 : 0 ≤ 1 / (u ^ lam * u) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h5 h6, mul_nonneg h6 h7]

theorem summable_genTheta (ha : 1 ≤ a) (hc : ∀ p, ‖c p‖ ≤ C) (z : ℍ) {u : ℝ} (hu : 0 < u) :
    Summable fun p : ℤ × ℤ ↦
      ‖c p * genVec a z p ^ lam * ((Real.exp (-π * u * ‖genVec a z p‖ ^ 2) : ℝ) : ℂ)‖ :=
  summable_norm_term ha hc z hu

/-- The point $az \in \mathbf H$. -/
def mulUHP (a : ℕ) (ha : 1 ≤ a) (z : ℍ) : ℍ :=
  ⟨(a : ℂ) * z, by
    have : (0 : ℝ) < a := by exact_mod_cast ha
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos this z.im_pos⟩

theorem equiv_symm_ne_zero {p : ℤ × ℤ} (hp : p ≠ 0) : (finTwoArrowEquiv ℤ).symm p ≠ 0 := by
  intro h
  apply hp
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp at h0 h1
  exact Prod.ext h0 h1

theorem genVec_lower (ha : 1 ≤ a) (z : ℍ) {p : ℤ × ℤ} (hp : p ≠ 0) :
    EisensteinSeries.r (mulUHP a ha z) * ‖(finTwoArrowEquiv ℤ).symm p‖ ≤ ‖genVec a z p‖ := by
  have hx : (finTwoArrowEquiv ℤ).symm p ≠ 0 := equiv_symm_ne_zero hp
  have := EisensteinSeries.r_mul_max_le (mulUHP a ha z) hx
  refine this.trans (le_of_eq ?_)
  congr 1
  simp only [finTwoArrowEquiv_symm_apply, mulUHP, genVec]
  simp
  ring

theorem summable_genSeries (ha : 1 ≤ a) (hc : ∀ p, ‖c p‖ ≤ C) (z : ℍ) {σ : ℂ}
    (hσ : 1 + (lam : ℝ) / 2 < σ.re) :
    Summable fun p : ℤ × ℤ ↦ ‖c p * genVec a z p ^ lam * ((‖genVec a z p‖ : ℝ) : ℂ) ^ (-2 * σ)‖ := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hc 0)
  set k : ℝ := 2 * σ.re - lam with hk
  have hk2 : 2 < k := by rw [hk]; linarith
  have hrp := EisensteinSeries.r_pos (mulUHP a ha z)
  set r := EisensteinSeries.r (mulUHP a ha z) with hr
  have hsum : Summable fun p : ℤ × ℤ ↦ ‖(finTwoArrowEquiv ℤ).symm p‖ ^ (-k) :=
    (finTwoArrowEquiv ℤ).symm.summable_iff.2 (EisensteinSeries.summable_one_div_norm_rpow hk2)
  refine Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _) (fun p ↦ ?_)
    (hsum.mul_left (C * r ^ (-k)))
  by_cases hp : p = 0
  · subst hp
    have h0 : genVec a z 0 = 0 := by simp [genVec]
    have hne : (-2 * σ) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [show (0:ℝ) ≤ lam by positivity]
    rw [h0]
    simp only [norm_zero, Complex.ofReal_zero, Complex.zero_cpow hne, mul_zero, norm_zero]
    have : 0 ≤ ‖(finTwoArrowEquiv ℤ).symm (0 : ℤ × ℤ)‖ ^ (-k) := by positivity
    positivity
  · have hlow := genVec_lower ha z hp
    have hxn : 0 < ‖(finTwoArrowEquiv ℤ).symm p‖ :=
      norm_pos_iff.2 (equiv_symm_ne_zero hp)
    have hv : 0 < ‖genVec a z p‖ := lt_of_lt_of_le (mul_pos hrp hxn) hlow
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hv]
    have e : ‖genVec a z p‖ ^ lam * ‖genVec a z p‖ ^ (-2 * σ).re = ‖genVec a z p‖ ^ (-k) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hv]
      congr 1
      simp [hk]; ring
    rw [mul_assoc, e]
    have h1 : ‖genVec a z p‖ ^ (-k) ≤ (r * ‖(finTwoArrowEquiv ℤ).symm p‖) ^ (-k) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos hrp hxn) hlow (by linarith)
    rw [Real.mul_rpow hrp.le hxn.le] at h1
    have := mul_le_mul (hc p) h1 (by positivity) hC
    calc _ ≤ C * (r ^ (-k) * ‖(finTwoArrowEquiv ℤ).symm p‖ ^ (-k)) := this
      _ = _ := by ring

theorem min_le_normSq (ha : 1 ≤ a) (z : ℍ) {p : ℤ × ℤ} (hp : p ≠ 0) :
    min 1 (z.im ^ 2) ≤ ‖genVec a z p‖ ^ 2 := by
  have ha' : (1 : ℝ) ≤ a := Nat.one_le_cast.2 ha
  rw [genVec_normSq]
  by_cases h1 : p.1 = 0
  · have h2 : p.2 ≠ 0 := by
      intro h; apply hp; exact Prod.ext h1 h
    have h3 : 0 < p.2 ^ 2 := by positivity
    have h4 : (1 : ℤ) ≤ p.2 ^ 2 := h3
    have h5 : (1 : ℝ) ≤ (p.2 : ℝ) ^ 2 := by exact_mod_cast h4
    simp only [h1, Int.cast_zero, mul_zero, zero_mul, zero_add]
    calc min 1 (z.im ^ 2) ≤ 1 := min_le_left _ _
      _ ≤ _ := by nlinarith [sq_nonneg ((0:ℝ) * z.im)]
  · have h3 : 0 < p.1 ^ 2 := by positivity
    have h4 : (1 : ℤ) ≤ p.1 ^ 2 := h3
    have h5 : (1 : ℝ) ≤ (p.1 : ℝ) ^ 2 := by exact_mod_cast h4
    have h6 : z.im ^ 2 ≤ ((a : ℝ) * p.1 * z.im) ^ 2 := by
      have : ((a : ℝ) * p.1 * z.im) ^ 2 = (a : ℝ) ^ 2 * (p.1 : ℝ) ^ 2 * z.im ^ 2 := by ring
      rw [this]
      have : 1 ≤ (a : ℝ) ^ 2 * (p.1 : ℝ) ^ 2 := by nlinarith
      nlinarith [sq_nonneg z.im]
    calc min 1 (z.im ^ 2) ≤ z.im ^ 2 := min_le_right _ _
      _ ≤ _ := by nlinarith [sq_nonneg ((a : ℝ) * p.1 * z.re + p.2)]

theorem norm_genTheta_le_tsum (ha : 1 ≤ a) (hc : ∀ p, ‖c p‖ ≤ C) (z : ℍ) {u : ℝ} (hu : 0 < u) :
    ‖genTheta a lam c z u‖ ≤ ∑' p : ℤ × ℤ, ‖c p * genVec a z p ^ lam *
          ((Real.exp (-π * u * ‖genVec a z p‖ ^ 2) : ℝ) : ℂ)‖ :=
  norm_tsum_le_tsum_norm (summable_norm_term ha hc z hu)

/-- The bound for $u \ge 1$, uniform in $x$. -/
theorem norm_genTheta_le_of_one_le (ha : 1 ≤ a) (hlam : 1 ≤ lam) (hc : ∀ p, ‖c p‖ ≤ C) :
    ∃ B > (0 : ℝ), ∀ (z : ℍ) (u : ℝ), 1 ≤ u →
      ‖genTheta a lam c z u‖ ≤ B * (1 + z.im⁻¹ ^ 2) * Real.exp (-π * (u - 1) * min 1 (z.im ^ 2)) := by
  obtain ⟨B0, hB0, hB⟩ := tsum_norm_term_le (a := a) (lam := lam) (c := c) ha hc
  refine ⟨2 * B0, by positivity, fun z u hu ↦ ?_⟩
  have hu0 : 0 < u := by linarith
  have hy := z.im_pos
  set m := min 1 (z.im ^ 2) with hm
  have hterm : ∀ p : ℤ × ℤ, ‖c p * genVec a z p ^ lam *
        ((Real.exp (-π * u * ‖genVec a z p‖ ^ 2) : ℝ) : ℂ)‖ ≤
      Real.exp (-π * (u - 1) * m) * ‖c p * genVec a z p ^ lam *
        ((Real.exp (-π * 1 * ‖genVec a z p‖ ^ 2) : ℝ) : ℂ)‖ := fun p ↦ by
    rw [term_norm, term_norm]
    by_cases hp : p = 0
    · subst hp
      have h0 : genVec a z 0 = 0 := by simp [genVec]
      rw [h0]
      simp [zero_pow (by omega : lam ≠ 0)]
    · have hmn := min_le_normSq ha z hp
      have h1 : Real.exp (-π * u * ‖genVec a z p‖ ^ 2) ≤
          Real.exp (-π * (u - 1) * m) * Real.exp (-π * 1 * ‖genVec a z p‖ ^ 2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.2 hu),
          mul_le_mul_of_nonneg_left hmn (mul_nonneg Real.pi_pos.le (sub_nonneg.2 hu))]
      have h2 : 0 ≤ ‖c p‖ * ‖genVec a z p‖ ^ lam := by positivity
      calc ‖c p‖ * ‖genVec a z p‖ ^ lam * Real.exp (-π * u * ‖genVec a z p‖ ^ 2)
          ≤ ‖c p‖ * ‖genVec a z p‖ ^ lam * (Real.exp (-π * (u - 1) * m) *
              Real.exp (-π * 1 * ‖genVec a z p‖ ^ 2)) := mul_le_mul_of_nonneg_left h1 h2
        _ = _ := by ring
  have hs1 := summable_norm_term (lam := lam) (c := c) ha hc z one_pos
  have h1 := Summable.tsum_le_tsum hterm (summable_norm_term (lam := lam) (c := c) ha hc z hu0)
    (hs1.mul_left _)
  rw [tsum_mul_left] at h1
  have h2 := hB z 1 one_pos le_rfl
  rw [Real.one_rpow] at h2
  have hE : 0 ≤ Real.exp (-π * (u - 1) * m) := (Real.exp_pos _).le
  have h3 := mul_le_mul_of_nonneg_left h2 hE
  have h4 : 1 + z.im⁻¹ ≤ 2 * (1 + z.im⁻¹ ^ 2) := by nlinarith [sq_nonneg (z.im⁻¹ - 1)]
  have h5 : B0 * (1 + z.im⁻¹) ≤ B0 * (2 * (1 + z.im⁻¹ ^ 2)) := mul_le_mul_of_nonneg_left h4 hB0.le
  have h6 := mul_le_mul_of_nonneg_left h5 hE
  calc ‖genTheta a lam c z u‖ ≤ _ := norm_genTheta_le_tsum ha hc z hu0
    _ ≤ _ := h1
    _ ≤ _ := h3
    _ = Real.exp (-π * (u - 1) * m) * (B0 * (1 + z.im⁻¹)) := by rw [mul_one]
    _ ≤ _ := h6
    _ = _ := by ring

/-- The bound for $0 < u \le 1$, uniform in $x$. -/
theorem norm_genTheta_le_of_le_one (ha : 1 ≤ a) (hc : ∀ p, ‖c p‖ ≤ C) :
    ∃ B > (0 : ℝ), ∃ A > (0 : ℝ), ∀ (z : ℍ) (u : ℝ), 0 < u → u ≤ 1 →
      ‖genTheta a lam c z u‖ ≤ B * (z.im ^ A + z.im⁻¹ ^ A) * u ^ (-(lam : ℝ) - 1) := by
  obtain ⟨B0, hB0, hB⟩ := tsum_norm_term_le (a := a) (lam := lam) (c := c) ha hc
  refine ⟨2 * B0, by positivity, 1, one_pos, fun z u hu hu1 ↦ ?_⟩
  have hy := z.im_pos
  have h1 := (norm_genTheta_le_tsum (lam := lam) ha hc z hu).trans (hB z u hu hu1)
  refine h1.trans ?_
  rw [Real.rpow_one, Real.rpow_one]
  have hup : 0 < u ^ (-(lam : ℝ) - 1) := Real.rpow_pos_of_pos hu _
  have h2 : 1 + z.im⁻¹ ≤ 2 * (z.im + z.im⁻¹) := by
    rcases le_or_gt 1 z.im with h | h
    · linarith [inv_nonneg.2 hy.le]
    · have := (one_lt_inv₀ hy).2 h
      linarith
  have := mul_le_mul_of_nonneg_left h2 hB0.le
  nlinarith [mul_le_mul_of_nonneg_right this hup.le]

/-- Rapid decay at $\infty$ (no constant term, $\lambda \ge 1$). -/
theorem genTheta_isBigO_atTop (ha : 1 ≤ a) (hlam : 1 ≤ lam) (hc : ∀ p, ‖c p‖ ≤ C) (z : ℍ) (r : ℝ) :
    (genTheta a lam c z) =O[atTop] (· ^ r) := by
  obtain ⟨B, hB, hbd⟩ := norm_genTheta_le_of_one_le ha hlam hc
  have hy := z.im_pos
  set κ : ℝ := π * min 1 (z.im ^ 2) with hκ
  have hκ0 : 0 < κ := by positivity
  have h1 : (genTheta a lam c z) =O[atTop] fun u : ℝ ↦ Real.exp (-κ * u) := by
    refine Asymptotics.IsBigO.of_bound (B * (1 + z.im⁻¹ ^ 2) * Real.exp κ) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    refine (hbd z u hu).trans (le_of_eq ?_)
    have e : Real.exp (-π * (u - 1) * min 1 (z.im ^ 2)) = Real.exp κ * Real.exp (-κ * u) := by
      rw [← Real.exp_add]; congr 1; simp only [hκ]; ring
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, e]
    ring
  exact h1.trans (isLittleO_exp_neg_mul_rpow_atTop hκ0 r).isBigO

theorem continuousOn_genTheta (ha : 1 ≤ a) (hc : ∀ p, ‖c p‖ ≤ C) (z : ℍ) :
    ContinuousOn (genTheta a lam c z) (Ioi 0) := by
  intro u₀ hu₀
  have hu0 : 0 < u₀ := hu₀
  have hh : 0 < u₀ / 2 := by positivity
  have hon : ContinuousOn (genTheta a lam c z) (Ioi (u₀ / 2)) := by
    unfold genTheta
    refine continuousOn_tsum (u := fun p : ℤ × ℤ ↦ ‖c p * genVec a z p ^ lam *
      ((Real.exp (-π * (u₀ / 2) * ‖genVec a z p‖ ^ 2) : ℝ) : ℂ)‖) (fun p ↦ ?_)
      (summable_norm_term ha hc z hh) (fun p u hu ↦ ?_)
    · exact (continuous_const.mul (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).mul continuous_const)))).continuousOn
    · rw [term_norm, term_norm]
      have hu' : u₀ / 2 < u := hu
      have : Real.exp (-π * u * ‖genVec a z p‖ ^ 2) ≤
          Real.exp (-π * (u₀ / 2) * ‖genVec a z p‖ ^ 2) := by
        apply Real.exp_le_exp.2
        nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg ‖genVec a z p‖),
          mul_le_mul_of_nonneg_left hu'.le (mul_nonneg Real.pi_pos.le (sq_nonneg ‖genVec a z p‖))]
      have h2 : 0 ≤ ‖c p‖ * ‖genVec a z p‖ ^ lam := by positivity
      exact mul_le_mul_of_nonneg_left this h2
  exact (hon.continuousAt (isOpen_Ioi.mem_nhds (show u₀ / 2 < u₀ by linarith))).continuousWithinAt

theorem summable_gauss_lattice (ha : 1 ≤ a) (z : ℍ) {s : ℝ} (hs : 0 < s) :
    Summable (fun p : ℤ × ℤ ↦ Real.exp (-π * s * ‖genVec a z p‖ ^ 2)) := by
  have hs' : 0 < min s 1 := lt_min hs one_pos
  refine Summable.of_nonneg_of_le (fun p ↦ (Real.exp_pos _).le) (fun p ↦ ?_)
    (gauss_lattice (a := a) ha z hs' (min_le_right _ _)).1
  apply Real.exp_le_exp.2
  nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg ‖genVec a z p‖), min_le_left s 1,
    mul_le_mul_of_nonneg_right (min_le_left s 1)
      (mul_nonneg Real.pi_pos.le (sq_nonneg ‖genVec a z p‖))]

theorem key_ineq (A d y y₀ k : ℝ) (hy₀ : 0 < y₀) (hd : d ^ 2 ≤ y₀ ^ 2 / 16)
    (hy : 3 * y₀ / 4 ≤ y) :
    (A ^ 2 + (k * y₀) ^ 2) / 2 ≤ (A + k * d) ^ 2 + (k * y) ^ 2 := by
  have h1 : (A + k * d) ^ 2 ≥ A ^ 2 / 2 - (k * d) ^ 2 := by nlinarith [sq_nonneg (A + 2 * (k * d))]
  have h2 : y ^ 2 - d ^ 2 ≥ y₀ ^ 2 / 2 := by nlinarith
  have h3 : k ^ 2 * (y ^ 2 - d ^ 2) ≥ k ^ 2 * (y₀ ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg k)
  nlinarith

theorem normSq_nbhd (a : ℕ) (z₀ w : ℍ) (hw : ‖(w : ℂ) - z₀‖ < z₀.im / 4) (p : ℤ × ℤ) :
    ‖genVec a z₀ p‖ ^ 2 / 2 ≤ ‖genVec a w p‖ ^ 2 := by
  have hy₀ := z₀.im_pos
  have h1 := Complex.abs_re_le_norm ((w : ℂ) - z₀)
  have h2 := Complex.abs_im_le_norm ((w : ℂ) - z₀)
  simp only [Complex.sub_re, Complex.sub_im] at h1 h2
  have hd : (w.re - z₀.re) ^ 2 ≤ z₀.im ^ 2 / 16 := by
    have : |w.re - z₀.re| ≤ z₀.im / 4 := (h1.trans hw.le)
    have := sq_le_sq' (by linarith [abs_le.1 this]) (abs_le.1 this).2
    nlinarith
  have hy : 3 * z₀.im / 4 ≤ w.im := by
    have := (abs_le.1 (h2.trans hw.le)).1
    have : -(z₀.im / 4) ≤ (w : ℂ).im - (z₀ : ℂ).im := this
    simp only [UpperHalfPlane.im] at *
    linarith
  rw [genVec_normSq, genVec_normSq]
  have := key_ineq ((a : ℝ) * p.1 * z₀.re + p.2) (w.re - z₀.re) w.im z₀.im ((a : ℝ) * p.1) hy₀ hd hy
  have e : (a : ℝ) * p.1 * w.re + p.2 = ((a : ℝ) * p.1 * z₀.re + p.2) + (a : ℝ) * p.1 * (w.re - z₀.re) := by
    ring
  rw [e]
  exact this

/-- Continuity in $z$ for fixed $u > 0$. -/
theorem continuous_genTheta_z (ha : 1 ≤ a) (hc : ∀ p, ‖c p‖ ≤ C) {u : ℝ} (hu : 0 < u) :
    Continuous fun z : ℍ ↦ genTheta a lam c z u := by
  rw [continuous_iff_continuousAt]
  intro z₀
  have hC : 0 ≤ C := (norm_nonneg _).trans (hc 0)
  have hq : 0 < Real.sqrt u ^ lam := by positivity
  set N : Set ℍ := {w | ‖(w : ℂ) - z₀‖ < z₀.im / 4} with hN
  have hNo : IsOpen N :=
    isOpen_lt (UpperHalfPlane.continuous_coe.sub continuous_const).norm continuous_const
  have hz₀ : z₀ ∈ N := by
    simp only [hN, Set.mem_ofPred_eq, sub_self, norm_zero]; have := z₀.im_pos; positivity
  have hon : ContinuousOn (fun z : ℍ ↦ genTheta a lam c z u) N := by
    unfold genTheta
    refine continuousOn_tsum (u := fun p : ℤ × ℤ ↦ (C * lam.factorial / Real.sqrt u ^ lam) *
      Real.exp (-π * (u / 4) * ‖genVec a z₀ p‖ ^ 2)) (fun p ↦ ?_)
      ((summable_gauss_lattice (a := a) ha z₀ (by positivity : 0 < u / 4)).mul_left _)
      (fun p w hw ↦ ?_)
    · have hv : Continuous fun w : ℍ ↦ genVec a w p := by
        unfold genVec
        exact (continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const
      exact (continuous_const.mul (hv.pow lam) |>.mul (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul (hv.norm.pow 2))))).continuousOn
    · have h1 := term_le a lam hc w hu p
      have h2 := normSq_nbhd a z₀ w hw p
      have h3 : Real.exp (-π * (u / 2) * ‖genVec a w p‖ ^ 2) ≤
          Real.exp (-π * (u / 4) * ‖genVec a z₀ p‖ ^ 2) := by
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ π * (u / 2))
        nlinarith
      have h4 : 0 ≤ C * lam.factorial := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hq]
      exact h1.trans (by nlinarith [mul_le_mul_of_nonneg_left h3 h4])
  exact hon.continuousAt (hNo.mem_nhds hz₀)

/-! ### The Mellin transform -/

theorem genVec_norm_pos (ha : 1 ≤ a) (z : ℍ) {p : ℤ × ℤ} (hp : p ≠ 0) : 0 < ‖genVec a z p‖ := by
  have hrp := EisensteinSeries.r_pos (mulUHP a ha z)
  have hxn : 0 < ‖(finTwoArrowEquiv ℤ).symm p‖ := norm_pos_iff.2 (equiv_symm_ne_zero hp)
  exact lt_of_lt_of_le (mul_pos hrp hxn) (genVec_lower ha z hp)

theorem cpow_aux {r : ℝ} (hr : 0 < r) (σ : ℂ) :
    (1 / ((π * r ^ 2 : ℝ) : ℂ)) ^ σ = (π : ℂ) ^ (-σ) * (r : ℂ) ^ (-2 * σ) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hx : (0 : ℝ) < 1 / (π * r ^ 2) := by positivity
  have e1 : (1 / ((π * r ^ 2 : ℝ) : ℂ)) = ((1 / (π * r ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [e1, Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hπ.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), ← Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_log hπ.le, ← Complex.ofReal_log hr.le]
  have : Real.log (1 / (π * r ^ 2)) = -(Real.log π + 2 * Real.log r) := by
    rw [one_div, Real.log_inv, Real.log_mul hπ.ne' (by positivity), Real.log_pow]
    push_cast; ring
  rw [this]; push_cast; ring

theorem real_integral_aux {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ∫ t in Ioi (0 : ℝ), t ^ (s - 1) * Real.exp (-(π * r ^ 2 * t)) =
      Real.Gamma s * π ^ (-s) * r ^ (-2 * s) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs (by positivity)]
  have h1 : (1 / (π * r ^ 2)) ^ s = π ^ (-s) * r ^ (-2 * s) := by
    rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
      Real.mul_rpow hπ.le (by positivity)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    congr 1
    push_cast; ring
  rw [h1]; ring

/-- The $p$-th term of the integrand of the Mellin transform. -/
def Fterm (a lam : ℕ) (c : ℤ × ℤ → ℂ) (z : ℍ) (σ : ℂ) (p : ℤ × ℤ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (σ - 1) * (c p * genVec a z p ^ lam * ((Real.exp (-π * t * ‖genVec a z p‖ ^ 2) : ℝ) : ℂ))

theorem Fterm_zero (hlam : 1 ≤ lam) (z : ℍ) (σ : ℂ) (t : ℝ) :
    Fterm a lam c z σ 0 t = 0 := by
  have h0 : genVec a z 0 = 0 := by simp [genVec]
  simp [Fterm, h0, zero_pow (by omega : lam ≠ 0)]

theorem norm_Fterm (z : ℍ) {σ : ℂ} (p : ℤ × ℤ) {t : ℝ} (ht : 0 < t) :
    ‖Fterm a lam c z σ p t‖ = ‖c p‖ * ‖genVec a z p‖ ^ lam *
      (t ^ (σ.re - 1) * Real.exp (-(π * ‖genVec a z p‖ ^ 2 * t))) := by
  unfold Fterm
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, term_norm]
  have : -π * t * ‖genVec a z p‖ ^ 2 = -(π * ‖genVec a z p‖ ^ 2 * t) := by ring
  rw [this]
  simp only [Complex.sub_re, Complex.one_re]
  ring

theorem integrable_Fterm (ha : 1 ≤ a) (hlam : 1 ≤ lam) (z : ℍ) {σ : ℂ} (hσ : 0 < σ.re)
    (p : ℤ × ℤ) : Integrable (Fterm a lam c z σ p) (volume.restrict (Ioi (0 : ℝ))) := by
  by_cases hp : p = 0
  · subst hp
    have : Fterm a lam c z σ 0 = fun _ => 0 := funext (Fterm_zero hlam z σ)
    rw [this]; exact integrable_zero _ _ _
  · have hv := genVec_norm_pos ha z hp
    have hg : Integrable (fun t : ℝ ↦ ‖c p‖ * ‖genVec a z p‖ ^ lam *
        (t ^ (σ.re - 1) * Real.exp (-(π * ‖genVec a z p‖ ^ 2 * t))))
        (volume.restrict (Ioi (0 : ℝ))) := by
      refine Integrable.const_mul ?_ _
      have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := σ.re - 1)
        (b := π * ‖genVec a z p‖ ^ 2) (by linarith) one_pos (by positivity)
      refine this.congr_fun (fun t ht ↦ ?_) measurableSet_Ioi
      simp only [Real.rpow_one, neg_mul]
    refine hg.mono' ?_ ?_
    · unfold Fterm
      exact ((Complex.measurable_ofReal.pow_const (σ - 1)).mul (measurable_const.mul
        (Complex.measurable_ofReal.comp (Real.measurable_exp.comp
          ((measurable_const.mul measurable_id).mul measurable_const))))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht ↦ ?_)
      rw [norm_Fterm z p ht]

theorem integral_norm_Fterm (ha : 1 ≤ a) (hlam : 1 ≤ lam) (z : ℍ) {σ : ℂ} (hσ : 0 < σ.re)
    (p : ℤ × ℤ) :
    ∫ t in Ioi (0 : ℝ), ‖Fterm a lam c z σ p t‖ =
      Real.Gamma σ.re * π ^ (-σ.re) *
        ‖c p * genVec a z p ^ lam * ((‖genVec a z p‖ : ℝ) : ℂ) ^ (-2 * σ)‖ := by
  by_cases hp : p = 0
  · subst hp
    have h0 : genVec a z 0 = 0 := by simp [genVec]
    simp [Fterm_zero hlam, h0, zero_pow (by omega : lam ≠ 0)]
  · have hv := genVec_norm_pos ha z hp
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ norm_Fterm z p ht), integral_const_mul,
      real_integral_aux hv hσ, norm_mul, norm_mul, norm_pow,
      Complex.norm_cpow_eq_rpow_re_of_pos hv]
    simp only [mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.neg_re, neg_mul, zero_mul,
      sub_zero]
    ring

theorem integral_Fterm (ha : 1 ≤ a) (hlam : 1 ≤ lam) (z : ℍ) {σ : ℂ} (hσ : 0 < σ.re)
    (p : ℤ × ℤ) :
    ∫ t in Ioi (0 : ℝ), Fterm a lam c z σ p t =
      Gamma σ * (π : ℂ) ^ (-σ) *
        (c p * genVec a z p ^ lam * ((‖genVec a z p‖ : ℝ) : ℂ) ^ (-2 * σ)) := by
  by_cases hp : p = 0
  · subst hp
    have h0 : genVec a z 0 = 0 := by simp [genVec]
    simp [Fterm_zero hlam, h0, zero_pow (by omega : lam ≠ 0)]
  · have hv := genVec_norm_pos ha z hp
    have e : ∀ t : ℝ, Fterm a lam c z σ p t = (c p * genVec a z p ^ lam) *
        ((t : ℂ) ^ (σ - 1) *
          Complex.exp (-(((π * ‖genVec a z p‖ ^ 2 : ℝ) : ℂ) * (t : ℂ)))) := fun t ↦ by
      unfold Fterm
      rw [Complex.ofReal_exp]
      push_cast
      ring_nf
    simp_rw [e]
    rw [integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi hσ (by positivity),
      cpow_aux hv]
    ring

/-- **The Mellin transform of the theta series:** $\int_0^\infty\Theta(z,u)u^{\sigma-1}du =
\Gamma(\sigma)\pi^{-\sigma}S(z,\sigma)$ for $\operatorname{Re}\sigma > 1 + \lambda/2$. -/
theorem mellin_genTheta (ha : 1 ≤ a) (hlam : 1 ≤ lam) (hc : ∀ p, ‖c p‖ ≤ C) (z : ℍ) {σ : ℂ}
    (hσ : 1 + (lam : ℝ) / 2 < σ.re) :
    mellin (genTheta a lam c z) σ = Gamma σ * (π : ℂ) ^ (-σ) * genSeries a lam c z σ := by
  have hσ0 : 0 < σ.re := by
    have : (0 : ℝ) ≤ lam / 2 := by positivity
    linarith
  have hS := summable_genSeries (lam := lam) (c := c) ha hc z hσ
  have h1 : ∀ t : ℝ, (t : ℂ) ^ (σ - 1) • genTheta a lam c z t =
      ∑' p, Fterm a lam c z σ p t := fun t ↦ by
    unfold genTheta Fterm
    rw [smul_eq_mul, ← tsum_mul_left]
  have hsum : Summable fun p : ℤ × ℤ ↦ ∫ t in Ioi (0 : ℝ), ‖Fterm a lam c z σ p t‖ := by
    simp_rw [integral_norm_Fterm ha hlam z hσ0]
    exact hS.mul_left _
  rw [mellin]
  simp_rw [h1]
  rw [← integral_tsum_of_summable_integral_norm (fun p ↦ integrable_Fterm ha hlam z hσ0 p) hsum]
  simp_rw [integral_Fterm ha hlam z hσ0]
  rw [tsum_mul_left]
  rfl

end ModularFormsKB.Miyake.HeckeTrick
