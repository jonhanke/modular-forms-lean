/-
# Rapid decay of the Rankin kernel at every cusp, on the fundamental domain

For $f \in S_{k+1/2}(4N,\chi)$ ($N \ge 1$), a
bound $|\theta_{\psi,t}(z)| \le C(1+y^{-2})$, every $\gamma \in \mathrm{SL}_2(\mathbb Z)$ and every $A$, the function
$|G_\psi(\gamma\tau)|\big(\operatorname{Im}(\gamma\tau)^A + \operatorname{Im}(\gamma\tau)^{-A}\big)$ is bounded on
`ModularGroup.fd` (`rankinKernel_bound_fd`). Proof: on $\mathcal F$, $|c\tau+d|$ lies between a positive constant and a
multiple of $\operatorname{Im}\tau$, so all factors are polynomial in $\operatorname{Im}\tau$ except the cusp quantity of $f$,
which decays exponentially (`HeckeBound.cuspNorm_sq_isBigO_exp`); conclude with Mathlib's
`ModularGroup.exists_bound_fundamental_domain_of_isBigO` applied to a continuous majorant.
-/
import ModularFormsKB.HalfIntegral.Abstract.ShimuraRankin
import ModularFormsKB.HalfIntegral.Abstract.PeterssonConvergence
import ModularFormsKB.HalfIntegral.HeckeBound

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup UpperHalfPlane Filter Asymptotics MeasureTheory
open scoped Real

theorem rpow_le_rpow_abs_aux {q U : ℝ} (hq : 0 < q) (h1 : 1 / U ≤ q) (h2 : q ≤ U) (s : ℝ) :
    q ^ s ≤ U ^ |s| := by
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs]; exact Real.rpow_le_rpow hq.le h2 hs
  · rw [abs_of_neg hs]
    have hU : 0 < U := lt_of_lt_of_le hq h2
    have hqi : q⁻¹ ≤ U := by
      have : (1 / U)⁻¹ ≥ q⁻¹ := inv_anti₀ (by positivity) h1
      simpa using this
    have : q ^ s = (q⁻¹) ^ (-s) := by
      rw [Real.inv_rpow hq.le, Real.rpow_neg hq.le, inv_inv]
    rw [this]
    exact Real.rpow_le_rpow (inv_nonneg.2 hq.le) hqi (by linarith)

theorem denom_sq_ge_aux {x v c d : ℝ} (hx : |x| ≤ 1 / 2) (hv : 1 ≤ x ^ 2 + v ^ 2) (hcd : 1 ≤ c ^ 2 + d ^ 2) :
    1 / 2 ≤ (c * x + d) ^ 2 + (c * v) ^ 2 := by
  have hx' := abs_le.1 hx
  have h1 : c ^ 2 ≤ c ^ 2 * (x ^ 2 + v ^ 2) := by nlinarith [sq_nonneg c]
  have h2 : -(|c * d|) ≤ 2 * c * d * x := by
    rcases le_total 0 (c * d) with h | h
    · rw [abs_of_nonneg h]; nlinarith [mul_nonneg h (by linarith : (0:ℝ) ≤ 2 * x + 1)]
    · rw [abs_of_nonpos h]; nlinarith [mul_nonneg (neg_nonneg.2 h) (by linarith : (0:ℝ) ≤ 1 - 2 * x)]
  have h3 : |c * d| ≤ (c ^ 2 + d ^ 2) / 2 := by
    rw [abs_mul]; nlinarith [sq_abs c, sq_abs d, sq_nonneg (|c| - |d|)]
  nlinarith

theorem rankinKernel_bound_fd (M : MultiplierSystem) {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)} (hN : 0 < N)
    {f : UpperHalfPlane → ℂ} (hf : f ∈ M.cuspForms k N χ) {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ}
    (hθc : Continuous fun τ : UpperHalfPlane ↦ thetaTwist ψ t τ)
    (hθ : ∃ C : ℝ, ∀ τ : UpperHalfPlane, ‖thetaTwist ψ t τ‖ ≤ C * (1 + τ.im ^ (-2 : ℝ)))
    (γ : SL(2, ℤ)) (A : ℝ) :
    ∃ C : ℝ, ∀ τ ∈ ModularGroup.fd,
      ‖rankinKernel k ψ t f (γ • τ)‖ * ((γ • τ).im ^ A + (γ • τ).im ^ (-A)) ≤ C := by
  obtain ⟨C0, hC0⟩ := hθ
  set C : ℝ := |C0| with hCdef
  have hC0n : 0 ≤ C := abs_nonneg _
  set c : ℝ := ((γ 1 0 : ℤ) : ℝ) with hc
  set d : ℝ := ((γ 1 1 : ℤ) : ℝ) with hd
  set w : ℝ := (k : ℝ) + 1 / 2 with hw
  set β : ℝ := ((k + charParity ψ + 1 : ℕ) : ℝ) / 2 with hβ
  have hw0 : 0 ≤ w := by positivity
  have hβ0 : 0 ≤ β := by positivity
  set m : ℝ := 2 * (|c| + |d|) + 1 with hm
  have hm1 : 1 ≤ m := by have := abs_nonneg c; have := abs_nonneg d; linarith
  set m' : ℝ := 4 + m ^ 2 with hm'
  have hm'4 : 4 ≤ m' := by nlinarith [sq_nonneg m]
  have hmm' : m ≤ m' := by nlinarith
  have hm2 : m ^ 2 ≤ m' := by nlinarith [sq_nonneg m]
  set B : ℝ := w + 2 + β + |A| with hB
  have hDne : ∀ τ : ℍ, ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ≠ 0 := by
    intro τ
    rw [← denom_SL_eq]; exact (norm_pos_iff.2 (denom_ne_zero _ τ)).ne'
  have hcn_cont : Continuous (Abstract.cuspNorm k f γ) := by
    have hγ : Continuous (fun τ : ℍ ↦ γ • τ) := continuous_const_smul (γ : GL (Fin 2) ℝ)
    unfold Abstract.cuspNorm
    refine Continuous.mul ?_ ((hf.holo.continuous.comp hγ).norm)
    exact Continuous.rpow_const (by fun_prop : Continuous fun τ : ℍ ↦ ‖(γ 1 0 : ℂ) * τ + γ 1 1‖)
      fun τ ↦ Or.inl (hDne τ)
  set h : ℍ → ℝ := fun τ ↦ Abstract.cuspNorm k f γ τ * (m' * τ.im) ^ B with hh
  have hcn_nn : ∀ τ, 0 ≤ Abstract.cuspNorm k f γ τ := fun τ ↦
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _)
  have hh_cont : Continuous h := by
    refine hcn_cont.mul ?_
    exact (continuous_const.mul UpperHalfPlane.continuous_im).rpow_const fun τ ↦
      Or.inl (mul_pos (by linarith) τ.im_pos).ne'
  have hh_tend : Tendsto h atImInfty (nhds 0) := by
    have hg := (MultiplierSystem.tendsto_cuspNorm_sq_mul M k N hN χ hf γ (2 * B))
    have hs := (hg.sqrt).const_mul (m' ^ B)
    rw [Real.sqrt_zero, mul_zero] at hs
    refine hs.congr fun τ ↦ ?_
    have hu := τ.im_pos
    have : Abstract.cuspNorm k f γ τ ^ 2 * τ.im ^ (2 * B) =
        (Abstract.cuspNorm k f γ τ * τ.im ^ B) ^ 2 := by
      rw [mul_pow, ← Real.rpow_natCast (τ.im ^ B) 2, ← Real.rpow_mul hu.le]; norm_num; left; rw [mul_comm]
    rw [this, Real.sqrt_sq (mul_nonneg (hcn_nn τ) (Real.rpow_nonneg hu.le _))]
    show _ = Abstract.cuspNorm k f γ τ * (m' * τ.im) ^ B
    rw [Real.mul_rpow (by linarith) hu.le]
    ring
  have hO : h =O[atImInfty] fun τ : ℍ ↦ τ.im ^ (0 : ℝ) := by
    simpa using hh_tend.isBigO_one ℝ
  obtain ⟨F, hF⟩ := ModularGroup.exists_bound_fundamental_domain_of_isBigO hh_cont hO
  refine ⟨4 * C * F, fun τ hτ ↦ ?_⟩
  have hFτ : h τ ≤ F := by
    have := hF τ hτ
    rw [Real.rpow_zero, mul_one, Real.norm_of_nonneg (mul_nonneg (hcn_nn τ)
      (Real.rpow_nonneg (by have := τ.im_pos; positivity) _))] at this
    exact this
  have hu := τ.im_pos
  set u := τ.im with hu_def
  have hu2 : 1 / 2 ≤ u := by
    have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hτ
    by_contra hlt; push_neg at hlt; nlinarith
  set D := ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ with hD
  have hDpos : 0 < D := lt_of_le_of_ne (norm_nonneg _) (hDne τ).symm
  have hx : |(τ : ℂ).re| ≤ 1 / 2 := hτ.2
  have hnorm : 1 ≤ (τ : ℂ).re ^ 2 + u ^ 2 := by
    have := hτ.1
    rw [Complex.normSq_apply] at this
    simp only [UpperHalfPlane.coe_im, sq] at *
    nlinarith
  have hcd : 1 ≤ c ^ 2 + d ^ 2 := by
    have hz : 1 ≤ (γ 1 0) ^ 2 + (γ 1 1) ^ 2 := by
      by_contra hlt; push_neg at hlt
      have h0 : γ 1 0 = 0 := by nlinarith
      have h1 : γ 1 1 = 0 := by nlinarith
      have := γ.det_coe
      rw [Matrix.det_fin_two, h0, h1] at this
      simp at this
    have : (1 : ℝ) ≤ ((γ 1 0 : ℤ) : ℝ) ^ 2 + ((γ 1 1 : ℤ) : ℝ) ^ 2 := by exact_mod_cast hz
    exact this
  have hD2eq : D ^ 2 = (c * (τ : ℂ).re + d) ^ 2 + (c * u) ^ 2 := by
    rw [hD, Complex.sq_norm, Complex.normSq_apply]
    simp [hc, hd, hu_def]
    ring
  have hD2 : 1 / 2 ≤ D ^ 2 := by
    rw [hD2eq]; exact denom_sq_ge_aux hx hnorm hcd
  have hDle : D ≤ m * u := by
    have h1 : D ≤ |c| * ‖(τ : ℂ)‖ + |d| := by
      calc D ≤ ‖(γ 1 0 : ℂ) * τ‖ + ‖(γ 1 1 : ℂ)‖ := norm_add_le _ _
        _ = |c| * ‖(τ : ℂ)‖ + |d| := by
          rw [norm_mul]
          simp [hc, hd, Complex.norm_intCast]
    have h2 : ‖(τ : ℂ)‖ ≤ 2 * u := by
      have := Complex.norm_le_abs_re_add_abs_im (τ : ℂ)
      have h3 : |(τ : ℂ).im| = u := abs_of_pos hu
      linarith
    have := abs_nonneg c
    have := abs_nonneg d
    rw [hm]
    nlinarith [mul_le_mul_of_nonneg_left h2 (abs_nonneg c)]
  have hq : (γ • τ).im = u / D ^ 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, normSq_eq_norm_sq, denom_SL_eq]
  have hqpos : 0 < (γ • τ).im := (γ • τ).im_pos
  set q := (γ • τ).im with hq_def
  set U := m' * u with hU
  have hUpos : 0 < U := by positivity
  have hU4 : 4 * u ≤ U := by
    rw [hU]; exact mul_le_mul_of_nonneg_right hm'4 hu.le
  have hU1 : 1 ≤ U := by linarith
  have hqU : q ≤ U := by
    rw [hq, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hD2 hUpos.le
    linarith
  have h1U : 1 / U ≤ q := by
    rw [hq, div_le_div_iff₀ hUpos (by positivity)]
    have h3 : D ^ 2 ≤ (m * u) ^ 2 := pow_le_pow_left₀ hDpos.le hDle 2
    have h4 : m ^ 2 * u ^ 2 ≤ m' * u ^ 2 := mul_le_mul_of_nonneg_right hm2 (sq_nonneg u)
    have e : u * U = m' * u ^ 2 := by rw [hU]; ring
    have e2 : (m * u) ^ 2 = m ^ 2 * u ^ 2 := by ring
    linarith
  have hDU : D ≤ U := by
    calc D ≤ m * u := hDle
      _ ≤ U := by rw [hU]; exact mul_le_mul_of_nonneg_right hmm' hu.le
  have hker : ‖rankinKernel k ψ t f (γ • τ)‖ =
      ‖f (γ • τ)‖ * ‖thetaTwist ψ t ((γ • τ : ℍ) : ℂ)‖ * q ^ β := by
    unfold rankinKernel
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg hqpos.le _)]
  have hfeq : ‖f (γ • τ)‖ = Abstract.cuspNorm k f γ τ * D ^ w := by
    unfold Abstract.cuspNorm
    rw [mul_right_comm, ← Real.rpow_add hDpos]
    simp [hD, hw]
  have hθ1 : ‖thetaTwist ψ t ((γ • τ : ℍ) : ℂ)‖ ≤ C * (1 + q ^ (-2 : ℝ)) :=
    (hC0 (γ • τ)).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hq2 : q ^ (-2 : ℝ) ≤ U ^ (2 : ℝ) := by
    have := rpow_le_rpow_abs_aux hqpos h1U hqU (-2)
    simpa using this
  have hU2 : 1 ≤ U ^ (2 : ℝ) := Real.one_le_rpow hU1 (by norm_num)
  have hθ2 : ‖thetaTwist ψ t ((γ • τ : ℍ) : ℂ)‖ ≤ C * (2 * U ^ (2 : ℝ)) :=
    hθ1.trans (mul_le_mul_of_nonneg_left (by linarith) hC0n)
  have hqβ : q ^ β ≤ U ^ β := Real.rpow_le_rpow hqpos.le hqU hβ0
  have hDw : D ^ w ≤ U ^ w := Real.rpow_le_rpow hDpos.le hDU hw0
  have hqA : q ^ A + q ^ (-A) ≤ 2 * U ^ |A| := by
    have h1 := rpow_le_rpow_abs_aux hqpos h1U hqU A
    have h2 := rpow_le_rpow_abs_aux hqpos h1U hqU (-A)
    rw [abs_neg] at h2
    linarith
  have hcn := hcn_nn τ
  have hUB : U ^ B = U ^ w * U ^ (2 : ℝ) * U ^ β * U ^ |A| := by
    rw [hB, Real.rpow_add hUpos, Real.rpow_add hUpos, Real.rpow_add hUpos]
  have hθn := norm_nonneg (thetaTwist ψ t ((γ • τ : ℍ) : ℂ))
  have hDw0 : 0 ≤ D ^ w := Real.rpow_nonneg hDpos.le _
  calc ‖rankinKernel k ψ t f (γ • τ)‖ * (q ^ A + q ^ (-A))
      = (Abstract.cuspNorm k f γ τ * D ^ w) * ‖thetaTwist ψ t ((γ • τ : ℍ) : ℂ)‖ * q ^ β *
          (q ^ A + q ^ (-A)) := by rw [hker, hfeq]
    _ ≤ (Abstract.cuspNorm k f γ τ * U ^ w) * (C * (2 * U ^ (2 : ℝ))) * U ^ β * (2 * U ^ |A|) := by
        have hq0 : 0 ≤ q ^ β := Real.rpow_nonneg hqpos.le _
        have hqA0 : 0 ≤ q ^ A + q ^ (-A) := by positivity
        have hUβ : 0 ≤ U ^ β := Real.rpow_nonneg hUpos.le _
        have hUA : 0 ≤ 2 * U ^ |A| := by positivity
        gcongr
    _ = 4 * C * (Abstract.cuspNorm k f γ τ * U ^ B) := by rw [hUB]; ring
    _ = 4 * C * h τ := by rw [hh]
    _ ≤ 4 * C * F := by gcongr

end ModularFormsKB.HalfIntegral
