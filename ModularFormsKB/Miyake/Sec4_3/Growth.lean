import ModularFormsKB.Miyake.Sec4_3.Defs
import ModularFormsKB.Citation
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Periodic

/-!
# Miyake Theorem 2.1.4 for $\Gamma_1(N)$: growth near the real axis gives holomorphy at the cusps

* `Miyake.isModularForm_of_growth`: a holomorphic function on $\mathbb H$, invariant under
  $\Gamma_1(N)$ in weight $k$, with $f(z) = O(\operatorname{Im}(z)^{-\nu})$ as $\operatorname{Im} z \to 0$,
  is a modular form for $\Gamma_1(N)$.
* `Miyake.isCuspForm_of_growth`: if moreover $\nu < k$, it is a cusp form.

Used for Weil's converse theorem (Miyake Theorem 4.3.15).
-/

open Complex Filter Asymptotics CongruenceSubgroup
open UpperHalfPlane hiding I
open Function Topology
open scoped Real MatrixGroups ModularForm Manifold

noncomputable section

namespace Miyake

theorem tendsto_of_periodic_growth {H : ℍ → ℂ} {h : ℝ} (hh : 0 < h)
    (hper : Periodic (H ∘ ofComplex) h) (hH : MDiff H) {C p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ τ : ℍ, 1 ≤ τ.im → ‖H τ‖ ≤ C * τ.im ^ p) :
    ∃ L, Tendsto H atImInfty (𝓝 L) := by
  set g : ℂ → ℂ := H ∘ ofComplex with hg
  set F := Periodic.cuspFunction h g with hF
  have hhol : ∀ᶠ z in comap Complex.im atTop, DifferentiableAt ℂ g z :=
    eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
      (fun z hz ↦ UpperHalfPlane.mdifferentiableAt_iff.mp (hH ⟨z, hz⟩))
  have hdiff := Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero hh hper hhol
  have hφ : Tendsto (fun q => (Periodic.invQParam h q).im) (𝓝[≠] 0) atTop :=
    tendsto_comap_iff.mp (Periodic.invQParam_tendsto hh)
  have hlit : (fun y : ℝ => y ^ p) =o[atTop] fun y => Real.exp (2 * π / h * y) :=
    isLittleO_rpow_exp_pos_mul_atTop p (by positivity)
  have h1 := hlit.comp_tendsto hφ
  have hbig : (fun q => F q - F 0) =O[𝓝[≠] 0] fun q => ((Periodic.invQParam h q).im) ^ p := by
    refine IsBigO.of_bound (|C| + ‖F 0‖) ?_
    filter_upwards [hφ.eventually_ge_atTop 1, self_mem_nhdsWithin] with q hq1 hq0
    have hq0' : q ≠ 0 := hq0
    have hpos : 0 < (Periodic.invQParam h q).im := by linarith
    have e1 : F q = H ⟨_, hpos⟩ := by
      rw [hF, Periodic.cuspFunction_eq_of_ne_zero _ _ hq0', hg]
      simp [ofComplex_apply_of_im_pos hpos]
    have hb' := hb ⟨_, hpos⟩ hq1
    have hy : 1 ≤ ((Periodic.invQParam h q).im) ^ p := Real.one_le_rpow hq1 hp
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖F q - F 0‖ ≤ ‖F q‖ + ‖F 0‖ := norm_sub_le _ _
      _ ≤ C * (Periodic.invQParam h q).im ^ p + ‖F 0‖ := by
          rw [e1]; gcongr; simpa using hb'
      _ ≤ |C| * (Periodic.invQParam h q).im ^ p + ‖F 0‖ * (Periodic.invQParam h q).im ^ p := by
          have : C * (Periodic.invQParam h q).im ^ p ≤ |C| * (Periodic.invQParam h q).im ^ p :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
          nlinarith [norm_nonneg (F 0)]
      _ = _ := by ring
  have h2 : (fun q : ℂ => Real.exp (2 * π / h * (Periodic.invQParam h q).im)) =ᶠ[𝓝[≠] 0]
      fun q => ‖(q - 0)⁻¹‖ := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq' : q ≠ 0 := hq
    rw [Periodic.im_invQParam, sub_zero, norm_inv]
    have : 2 * π / h * (-h / (2 * π) * Real.log ‖q‖) = - Real.log ‖q‖ := by
      field_simp [hh.ne', Real.pi_ne_zero]
    rw [this, Real.exp_neg, Real.exp_log (norm_pos_iff.mpr hq')]
  have hlo : (fun z => F z - F 0) =o[𝓝[≠] 0] fun z => (z - 0)⁻¹ := by
    have := hbig.trans_isLittleO (h1.congr' EventuallyEq.rfl h2)
    exact (isLittleO_norm_right.mp this)
  have hlim := tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO hdiff hlo
  refine ⟨limUnder (𝓝[≠] 0) F, ?_⟩
  have e : ∀ τ : ℍ, F (Periodic.qParam h (τ : ℂ)) = H τ := fun τ => by
    simpa [hg] using Periodic.eq_cuspFunction hh.ne' hper (τ : ℂ)
  have := hlim.comp ((Periodic.qParam_tendsto hh).comp tendsto_coe_atImInfty)
  refine this.congr (fun τ => ?_)
  simpa using e τ



theorem rpow_helper (y D a K e s : ℝ) (hy : 0 < y) (ha : 0 < a) (haD : a * y ≤ D)
    (hDK : D ≤ K * y) :
    D ^ e * y ^ s ≤ (K ^ e + a ^ e) * y ^ (e + s) := by
  have hD : 0 < D := lt_of_lt_of_le (by positivity) haD
  have hK : 0 ≤ K := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have hya : 0 < y ^ s := by positivity
  rw [Real.rpow_add hy]
  have key : D ^ e ≤ (K ^ e + a ^ e) * y ^ e := by
    rcases le_or_gt 0 e with he | he
    · calc D ^ e ≤ (K * y) ^ e := Real.rpow_le_rpow hD.le hDK he
        _ = K ^ e * y ^ e := Real.mul_rpow hK hy.le
        _ ≤ _ := by
          have : 0 ≤ a ^ e := by positivity
          nlinarith [Real.rpow_nonneg hy.le e]
    · calc D ^ e ≤ (a * y) ^ e := Real.rpow_le_rpow_of_nonpos (by positivity) haD he.le
        _ = a ^ e * y ^ e := Real.mul_rpow ha.le hy.le
        _ ≤ _ := by
          have : 0 ≤ K ^ e := Real.rpow_nonneg hK e
          nlinarith [Real.rpow_nonneg hy.le e]
  calc D ^ e * y ^ s ≤ ((K ^ e + a ^ e) * y ^ e) * y ^ s :=
        mul_le_mul_of_nonneg_right key hya.le
    _ = _ := by ring

theorem slash_bound {k : ℤ} {N : ℕ} {f : ℍ → ℂ} {ν C : ℝ}
    (hbound : ∀ τ : ℍ, τ.im ≤ 1 → ‖f τ‖ ≤ C * τ.im ^ (-ν))
    (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) :
    ∃ C' : ℝ, ∀ τ : ℍ, 1 ≤ τ.im → 0 ≤ τ.re → τ.re ≤ N →
      ‖(f ∣[k] γ) τ‖ ≤ C' * τ.im ^ (ν - k) := by
  set a : ℝ := |(γ 1 0 : ℝ)| with ha
  set d : ℝ := |(γ 1 1 : ℝ)| with hd
  have ha1 : 1 ≤ a := by
    rw [ha]
    have : (1 : ℤ) ≤ |γ 1 0| := Int.one_le_abs hc
    have : ((1 : ℤ) : ℝ) ≤ ((|γ 1 0| : ℤ) : ℝ) := by exact_mod_cast this
    simpa using this
  set K : ℝ := a * (N + 1) + d with hK
  refine ⟨|C| * (K ^ (2 * ν - k) + a ^ (2 * ν - k)), fun τ hy hre0 hreN => ?_⟩
  have hypos : 0 < τ.im := τ.im_pos
  have hden : denom γ τ = (γ 1 0 : ℂ) * τ + γ 1 1 := by simp [denom]
  set D : ℝ := ‖denom γ τ‖ with hDdef
  have hlow : a * τ.im ≤ D := by
    have h1 : |(denom γ τ).im| ≤ ‖denom γ τ‖ := Complex.abs_im_le_norm _
    have h2 : (denom γ τ).im = (γ 1 0 : ℝ) * τ.im := by
      rw [hden]; simp
    rw [h2, abs_mul, abs_of_pos hypos] at h1
    exact h1
  have hup : D ≤ K * τ.im := by
    rw [hDdef, hden]
    calc ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ≤ ‖(γ 1 0 : ℂ) * τ‖ + ‖(γ 1 1 : ℂ)‖ := norm_add_le _ _
      _ ≤ a * (N + τ.im) + d := by
          have e1 : ‖(γ 1 0 : ℂ) * τ‖ = a * ‖(τ : ℂ)‖ := by
            rw [norm_mul, ha]; simp
          have e2 : ‖(γ 1 1 : ℂ)‖ = d := by rw [hd]; simp
          have e3 : ‖(τ : ℂ)‖ ≤ N + τ.im := by
            calc ‖(τ : ℂ)‖ ≤ |(τ : ℂ).re| + |(τ : ℂ).im| := Complex.norm_le_abs_re_add_abs_im _
              _ ≤ N + τ.im := by
                have : |(τ : ℂ).re| ≤ N := by
                  rw [abs_of_nonneg (by simpa using hre0)]; simpa using hreN
                have h' : |(τ : ℂ).im| = τ.im := abs_of_pos hypos
                linarith
          rw [e1, e2]
          have : a * ‖(τ : ℂ)‖ ≤ a * (N + τ.im) := mul_le_mul_of_nonneg_left e3 (by linarith)
          linarith
      _ ≤ K * τ.im := by
          have hd0 : 0 ≤ d := abs_nonneg _
          rw [hK]
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ a) (Nat.cast_nonneg N : (0:ℝ) ≤ N)) (sub_nonneg.mpr hy), mul_nonneg hd0 (sub_nonneg.mpr hy)]
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hlow
  have him : (γ • τ).im = τ.im / D ^ 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq]
    simp [Complex.normSq_eq_norm_sq, hDdef]
  have him1 : (γ • τ).im ≤ 1 := by
    rw [him, div_le_one (by positivity)]
    have h2 : (a * τ.im) ^ 2 ≤ D ^ 2 := by gcongr
    have h1 : 1 ≤ a * τ.im := by nlinarith
    have h3 : τ.im ≤ a * τ.im := by nlinarith
    nlinarith
  have hfb := hbound _ him1
  have hslash : ‖(f ∣[k] γ) τ‖ = ‖f (γ • τ)‖ * D ^ (-k) := by
    rw [ModularForm.SL_slash_apply, norm_mul, norm_zpow]
  rw [hslash]
  have hpowD : D ^ (-k) = D ^ ((-k : ℤ) : ℝ) := (Real.rpow_intCast _ _).symm
  have hy' : (γ • τ).im ^ (-ν) = τ.im ^ (-ν) * D ^ (2 * ν) := by
    rw [him, Real.div_rpow hypos.le (sq_nonneg D), ← Real.rpow_two, ← Real.rpow_mul hDpos.le,
      div_eq_mul_inv]
    congr 2
    rw [← Real.rpow_neg hDpos.le]
    congr 1; ring
  have hpos' : 0 ≤ τ.im ^ (-ν) := by positivity
  have hDe : D ^ (2 * ν) * D ^ (((-k : ℤ) : ℝ)) = D ^ (2 * ν - k) := by
    rw [← Real.rpow_add hDpos]; congr 1
  have hh := rpow_helper τ.im D a K (2 * ν - k) (-ν) hypos (by linarith) hlow hup
  have hsum : 2 * ν - k + -ν = ν - k := by ring
  rw [hsum] at hh
  calc ‖f (γ • τ)‖ * D ^ (-k) ≤ (|C| * ((γ • τ).im ^ (-ν))) * D ^ (-k) := by
        gcongr
        exact hfb.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    _ = |C| * (τ.im ^ (-ν) * (D ^ (2 * ν) * D ^ (((-k : ℤ) : ℝ)))) := by
        rw [hy', hpowD]; ring
    _ = |C| * (D ^ (2 * ν - k) * τ.im ^ (-ν)) := by rw [hDe]; ring
    _ ≤ |C| * ((K ^ (2 * ν - k) + a ^ (2 * ν - k)) * τ.im ^ (ν - k)) := by gcongr
    _ = _ := by ring



theorem slash_periodic {k : ℤ} {N : ℕ} {f : ℍ → ℂ}
    (hinv : ∀ γ ∈ Gamma1 N, f ∣[k] γ = f) (γ : SL(2, ℤ)) (τ : ℍ) :
    (f ∣[k] γ) ((N : ℝ) +ᵥ τ) = (f ∣[k] γ) τ := by
  set t : SL(2, ℤ) := ModularGroup.T ^ (N : ℤ) with ht
  have e : ∀ i j, t i j = (!![1, (N : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j := fun i j =>
    congrFun (congrFun (ModularGroup.coe_T_zpow (N : ℤ)) i) j
  have htG : t ∈ CongruenceSubgroup.Gamma N := by
    rw [Gamma_mem, e, e, e, e]
    simp
  have hconj : γ * t * γ⁻¹ ∈ Gamma1 N := by
    have := (CongruenceSubgroup.Gamma_normal (N := N)).conj_mem t htG γ
    rw [Gamma1_mem]
    rw [Gamma_mem] at this
    exact ⟨this.1, this.2.2.2, this.2.2.1⟩
  have h1 : (f ∣[k] γ) ∣[k] t = f ∣[k] γ := by
    rw [← SlashAction.slash_mul]
    have : γ * t = (γ * t * γ⁻¹) * γ := by group
    rw [this, SlashAction.slash_mul, hinv _ hconj]
  have h2 := congrFun h1 τ
  rw [ModularForm.SL_slash_apply, UpperHalfPlane.modular_T_zpow_smul] at h2
  have hd : denom t τ = 1 := by
    rw [ModularGroup.denom_apply, e, e]
    simp
  rw [hd] at h2
  simpa using h2


theorem slash_bound_all {k : ℤ} {N : ℕ} (hN : 0 < N) {f : ℍ → ℂ} {ν C : ℝ}
    (hinv : ∀ γ ∈ Gamma1 N, f ∣[k] γ = f)
    (hbound : ∀ τ : ℍ, τ.im ≤ 1 → ‖f τ‖ ≤ C * τ.im ^ (-ν))
    (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖(f ∣[k] γ) τ‖ ≤ C' * τ.im ^ (ν - k) := by
  obtain ⟨C₀, hC₀⟩ := slash_bound (k := k) (N := N) hbound γ hc
  refine ⟨|C₀|, abs_nonneg _, fun τ hτ => ?_⟩
  have hper := UpperHalfPlane.periodic_comp_ofComplex (slash_periodic hinv γ)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set m : ℤ := ⌊τ.re / N⌋ with hm
  have him : 0 < ((τ : ℂ) - m * N).im := by simpa using τ.im_pos
  set τ' : ℍ := ⟨(τ : ℂ) - m * N, him⟩ with hτ'
  have hHeq : (f ∣[k] γ) τ' = (f ∣[k] γ) τ := by
    have := hper.sub_int_mul_eq (x := (τ : ℂ)) m
    simpa [Function.comp, ofComplex_apply_of_im_pos him, ofComplex_apply] using this
  have hre : τ'.re = τ.re - m * N := by simp [hτ']
  have himeq : τ'.im = τ.im := by simp [hτ']
  have h1 : (m : ℝ) ≤ τ.re / N := Int.floor_le _
  have h2 : τ.re / N < m + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hNpos] at h1
  rw [div_lt_iff₀ hNpos] at h2
  rw [← hHeq]
  refine (hC₀ τ' (by rw [himeq]; exact hτ) (by rw [hre]; linarith) (by rw [hre]; linarith)).trans ?_
  rw [himeq]
  exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)


/-- The matrix `[[1,0],[N,1]]`. -/
def tau0 (N : ℕ) : SL(2, ℤ) :=
  ⟨!![1, 0; (N : ℤ), 1], by simp [Matrix.det_fin_two]⟩

theorem tau0_mem (N : ℕ) : tau0 N ∈ Gamma1 N := by
  rw [Gamma1_mem]
  simp [tau0]

theorem tau0_10 {N : ℕ} (hN : 0 < N) : tau0 N 1 0 ≠ 0 := by
  simp [tau0]
  omega

theorem isBoundedAtImInfty_slash_of_ne {k : ℤ} {N : ℕ} (hN : 0 < N) {f : ℍ → ℂ}
    (hf : MDiff f) (hinv : ∀ γ ∈ Gamma1 N, f ∣[k] γ = f)
    {ν C : ℝ} (hbound : ∀ τ : ℍ, τ.im ≤ 1 → ‖f τ‖ ≤ C * τ.im ^ (-ν))
    (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) : IsBoundedAtImInfty (f ∣[k] γ) := by
  obtain ⟨C', hC'0, hC'⟩ := slash_bound_all hN hinv hbound γ hc
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨L, hL⟩ := tendsto_of_periodic_growth (H := f ∣[k] γ) (h := N) hNpos
    (UpperHalfPlane.periodic_comp_ofComplex (slash_periodic hinv γ))
    (hf.slash k (γ : GL (Fin 2) ℝ)) (C := C') (p := max (ν - k) 0) (le_max_right _ _)
    (fun τ hτ => (hC' τ hτ).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hτ (le_max_left _ _)) hC'0))
  exact hL.isBigO_one ℝ

theorem isZeroAtImInfty_slash_of_ne {k : ℤ} {N : ℕ} (hN : 0 < N) {f : ℍ → ℂ}
    (hinv : ∀ γ ∈ Gamma1 N, f ∣[k] γ = f)
    {ν C : ℝ} (hνk : ν < k) (hbound : ∀ τ : ℍ, τ.im ≤ 1 → ‖f τ‖ ≤ C * τ.im ^ (-ν))
    (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0) : IsZeroAtImInfty (f ∣[k] γ) := by
  obtain ⟨C', hC'0, hC'⟩ := slash_bound_all hN hinv hbound γ hc
  have hlim : Tendsto (fun τ : ℍ => C' * τ.im ^ (-((k : ℝ) - ν))) atImInfty (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (sub_pos.mpr hνk)).comp
      (tendsto_comap (f := UpperHalfPlane.im) (x := atTop))).const_mul C'
    simp only [mul_zero] at this
    exact this
  refine squeeze_zero_norm' ?_ hlim
  have : ∀ᶠ τ : ℍ in atImInfty, 1 ≤ τ.im :=
    (UpperHalfPlane.atImInfty_mem _).mpr ⟨1, fun z hz => hz⟩
  filter_upwards [this] with τ hτ
  have := hC' τ hτ
  have e : ν - k = -((k : ℝ) - ν) := by ring
  rwa [e] at this

theorem isBoundedAtImInfty_slash {k : ℤ} {N : ℕ} (hN : 0 < N) {f : ℍ → ℂ}
    (hf : MDiff f) (hinv : ∀ γ ∈ Gamma1 N, f ∣[k] γ = f)
    {ν C : ℝ} (hbound : ∀ τ : ℍ, τ.im ≤ 1 → ‖f τ‖ ≤ C * τ.im ^ (-ν))
    (γ : SL(2, ℤ)) : IsBoundedAtImInfty (f ∣[k] γ) := by
  by_cases hc : γ 1 0 = 0
  · have h0 := isBoundedAtImInfty_slash_of_ne hN hf hinv hbound (tau0 N) (tau0_10 hN)
    rw [hinv _ (tau0_mem N)] at h0
    exact UpperHalfPlane.IsBoundedAtImInfty.slash k (g := (γ : GL (Fin 2) ℝ)) (by simpa using hc) h0
  · exact isBoundedAtImInfty_slash_of_ne hN hf hinv hbound γ hc

theorem isZeroAtImInfty_slash {k : ℤ} {N : ℕ} (hN : 0 < N) {f : ℍ → ℂ}
    (hinv : ∀ γ ∈ Gamma1 N, f ∣[k] γ = f)
    {ν C : ℝ} (hνk : ν < k) (hbound : ∀ τ : ℍ, τ.im ≤ 1 → ‖f τ‖ ≤ C * τ.im ^ (-ν))
    (γ : SL(2, ℤ)) : IsZeroAtImInfty (f ∣[k] γ) := by
  by_cases hc : γ 1 0 = 0
  · have h0 := isZeroAtImInfty_slash_of_ne hN hinv hνk hbound (tau0 N) (tau0_10 hN)
    rw [hinv _ (tau0_mem N)] at h0
    exact UpperHalfPlane.IsZeroAtImInfty.slash k (g := (γ : GL (Fin 2) ℝ)) (by simpa using hc) h0
  · exact isZeroAtImInfty_slash_of_ne hN hinv hνk hbound γ hc

theorem slash_inv_mapGL {k : ℤ} {N : ℕ} {f : ℍ → ℂ}
    (hinv : ∀ γ ∈ Gamma1 N, f ∣[k] γ = f) :
    ∀ g ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] g = f := by
  intro g hg
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
  exact hinv γ hγ


/-- **Miyake Theorem 2.1.4, for $\Gamma_1(N)$.** Let $f$ be holomorphic on $\mathbb H$ with
$f|_k\gamma = f$ for all $\gamma \in \Gamma_1(N)$. If $f(z) = O(\operatorname{Im}(z)^{-\nu})$ as
$\operatorname{Im} z \to 0$ uniformly in $\operatorname{Re} z$ (here: on $\operatorname{Im} z \le 1$),
then $f$ is a modular form for $\Gamma_1(N)$. Relation: special case ($\Gamma = \Gamma_1(N)$). -/
@[kb "miyake1989" "§2.1, Theorem 2.1.4, p. 41"]
theorem isModularForm_of_growth {k : ℤ} {N : ℕ} (hN : 0 < N) {f : ℍ → ℂ}
    (hf : MDiff f) (hinv : ∀ γ ∈ Gamma1 N, f ∣[k] γ = f)
    {ν C : ℝ} (hbound : ∀ τ : ℍ, τ.im ≤ 1 → ‖f τ‖ ≤ C * τ.im ^ (-ν)) :
    ∃ F : ModularForm (Gamma1 N) k, ⇑F = f := by
  have : NeZero N := ⟨hN.ne'⟩
  refine ⟨⟨⟨f, slash_inv_mapGL hinv⟩, hf, fun {c} hc => ?_⟩, rfl⟩
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
  exact fun γ _ => isBoundedAtImInfty_slash hN hf hinv hbound γ

/-- **Miyake Theorem 2.1.4, cusp form part, for $\Gamma_1(N)$**: under the hypotheses of
`Miyake.isModularForm_of_growth`, if $\nu < k$ then $f$ is a cusp form. Relation: special case. -/
@[kb "miyake1989" "§2.1, Theorem 2.1.4, p. 41"]
theorem isCuspForm_of_growth {k : ℤ} {N : ℕ} (hN : 0 < N) {f : ℍ → ℂ}
    (hf : MDiff f) (hinv : ∀ γ ∈ Gamma1 N, f ∣[k] γ = f)
    {ν C : ℝ} (hνk : ν < k) (hbound : ∀ τ : ℍ, τ.im ≤ 1 → ‖f τ‖ ≤ C * τ.im ^ (-ν)) :
    ∃ F : CuspForm (Gamma1 N) k, ⇑F = f := by
  have : NeZero N := ⟨hN.ne'⟩
  refine ⟨⟨⟨f, slash_inv_mapGL hinv⟩, hf, fun {c} hc => ?_⟩, rfl⟩
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
  exact fun γ _ => isZeroAtImInfty_slash hN hinv hνk hbound γ

end Miyake
