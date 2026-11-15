import ModularFormsKB.Milne.Wave13.PolePoincare

/-!
# The series `S_u` is a meromorphic modular form with a pole exactly on `Γu`

See `ModularFormsKB.Milne.Wave13.PolePoincare` for the estimates.

* `S Γ u k z = ∑_{ξ ∈ Γ} ((az + b) - u(cz + d))^{-2k}`;
* `S_slash_apply`, `S_slash_eq`: `S|γ = ∑_ξ term(ξγ)`, and `S|γ = S` for `γ ∈ Γ`;
* `exists_decomp`: near each `z₀ ∈ ℍ`, `S` is a finite sum of terms plus a holomorphic function;
* `meromorphicAt_S`, `analyticAt_S`, `continuousAt_S`, `tendsto_norm_S`;
* `meromorphicAt_cusp_S`, `isMeromorphicModularForm_S`.
-/

open UpperHalfPlane Complex Filter Topology Matrix ModularForm EisensteinSeries Function
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.Wave13

variable (Γ : Subgroup SL(2, ℤ)) (u : ℍ) (k : ℕ)

/-- **The Poincaré series with a pole at `u`**: `S_u(z) = ∑_{ξ ∈ Γ} ((az + b) - u(cz + d))^{-2k}`. -/
def S (z : ℍ) : ℂ := ∑' ξ : Γ, term u k ξ z

theorem denom_zpow (γ : SL(2, ℤ)) (z : ℍ) :
    denom γ z ^ (-(2 * (k : ℤ))) = (denom γ z ^ (2 * k))⁻¹ := by
  rw [_root_.zpow_neg]
  norm_cast

theorem S_slash_apply (γ : SL(2, ℤ)) (z : ℍ) :
    (S Γ u k ∣[(2 * (k : ℤ))] γ) z = ∑' ξ : Γ, term u k ((ξ : SL(2, ℤ)) * γ) z := by
  have hd := pow_ne_zero (2 * k) (denom_ne_zero γ z)
  rw [SL_slash_apply, S, denom_zpow]
  simp_rw [term_smul]
  rw [tsum_mul_left, mul_comm, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

theorem S_slash_eq {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) : S Γ u k ∣[(2 * (k : ℤ))] γ = S Γ u k := by
  funext z
  rw [S_slash_apply, S]
  exact (Equiv.mulRight (⟨γ, hγ⟩ : Γ)).tsum_eq (fun ξ : Γ ↦ term u k (ξ : SL(2, ℤ)) z)

theorem S_eq_tsum {z : ℂ} (hz : 0 < z.im) : (S Γ u k ∘ ofComplex) z = ∑' ξ : Γ, term u k ξ z := by
  simp [S, ofComplex_apply_of_im_pos hz]

/-! ### Local structure in `ℍ` -/

variable {k}

/-- **Local decomposition**: near `z₀`, `S` is the sum of finitely many terms and of a function holomorphic at `z₀`;
the finite set contains every `ξ` moving `z₀` to within `Im(u)/2` of `u`. -/
theorem exists_decomp (hk : 3 ≤ k) (z₀ : ℍ) :
    ∃ s : Finset Γ, ∃ T : ℂ → ℂ, AnalyticAt ℂ T z₀ ∧
      (∀ ξ : Γ, ‖(((ξ : SL(2, ℤ)) • z₀ : ℍ) : ℂ) - u‖ < u.im / 2 → ξ ∈ s) ∧
      (S Γ u k ∘ ofComplex) =ᶠ[𝓝 (z₀ : ℂ)] fun z ↦ ∑ ξ ∈ s, term u k ξ z + T z := by
  classical
  set A := |z₀.re| + 1
  set B := z₀.im / 2
  set C := 2 * z₀.im
  have hB : 0 < B := by have := z₀.im_pos; positivity
  have hEx := finite_exceptional u A B C hB
  set Ex := {ξ : SL(2, ℤ) | ∃ z : ℍ, |z.re| ≤ A ∧ B ≤ z.im ∧ z.im ≤ C ∧ ‖((ξ • z : ℍ) : ℂ) - u‖ < u.im / 2}
  have hExΓ : ((↑) ⁻¹' Ex : Set Γ).Finite := hEx.preimage Subtype.val_injective.injOn
  set s := hExΓ.toFinset
  set U : Set ℂ := {z | |z.re| < A} ∩ {z | B < z.im} ∩ {z | z.im < C}
  have hU : IsOpen U :=
    ((isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im)).inter (isOpen_lt Complex.continuous_im continuous_const)
  have hUH : ∀ z ∈ U, 0 < z.im := fun z hz ↦ hB.trans hz.1.2
  have hz₀U : (z₀ : ℂ) ∈ U := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show |(z₀ : ℂ).re| < A; simp [A]
    · show B < (z₀ : ℂ).im; simp only [coe_im, B]; linarith [z₀.im_pos]
    · show (z₀ : ℂ).im < C; simp only [coe_im, C]; linarith [z₀.im_pos]
  set ρ := EisensteinSeries.r ⟨⟨A, B⟩, hB⟩
  have hρ : 0 < ρ := r_pos _
  have hr : 0 < u.im / 2 := by have := u.im_pos; positivity
  let e : {ξ : Γ // ξ ∉ s} → SL(2, ℤ) := fun i ↦ i.1
  have he : Injective e := fun i j h ↦ Subtype.ext (Subtype.ext h)
  have hsep : ∀ i z (hz : z ∈ U), u.im / 2 ≤ ‖((e i • (⟨z, hUH z hz⟩ : ℍ) : ℍ) : ℂ) - u‖ := by
    intro i z hz
    by_contra hlt
    push Not at hlt
    apply i.2
    rw [Set.Finite.mem_toFinset]
    exact ⟨⟨z, hUH z hz⟩, hz.1.1.le, hz.1.2.le, hz.2.le, hlt⟩
  have hρU : ∀ z (hz : z ∈ U), ρ ≤ EisensteinSeries.r ⟨z, hUH z hz⟩ := fun z hz ↦
    r_lower_bound_on_verticalStrip _ hB ⟨hz.1.1.le, hz.1.2.le⟩
  obtain ⟨hD, hsum⟩ := differentiableOn_tsum u k he hk hU hUH hr hρ hρU hsep
  refine ⟨s, fun z ↦ ∑' i : {ξ : Γ // ξ ∉ s}, term u k (e i) z, hD.analyticAt (hU.mem_nhds hz₀U), ?_, ?_⟩
  · intro ξ hξ
    rw [Set.Finite.mem_toFinset]
    exact ⟨z₀, le_of_lt (by simp [A]), by simp only [B]; linarith [z₀.im_pos],
      by simp only [C]; linarith [z₀.im_pos], hξ⟩
  · filter_upwards [hU.mem_nhds hz₀U] with z hz
    rw [S_eq_tsum Γ u k (hUH z hz)]
    have hs' : Summable fun ξ : Γ ↦ term u k ξ z :=
      (Finset.summable_compl_iff (f := fun ξ : Γ ↦ term u k ξ z) s).1 (hsum z hz).1
    exact (hs'.sum_add_tsum_subtype_compl s).symm

theorem meromorphicAt_S (hk : 3 ≤ k) (z₀ : ℍ) : MeromorphicAt (S Γ u k ∘ ofComplex) z₀ := by
  obtain ⟨s, T, hT, -, hS⟩ := exists_decomp Γ u hk z₀
  have h1 : MeromorphicAt (fun z ↦ ∑ ξ ∈ s, term u k (ξ : SL(2, ℤ)) z) (z₀ : ℂ) :=
    MeromorphicAt.fun_sum fun ξ _ ↦ meromorphicAt_term u k _ _
  exact (h1.add hT.meromorphicAt).congr (hS.filter_mono nhdsWithin_le_nhds).symm

theorem lin_ne_zero {ξ : SL(2, ℤ)} {z : ℍ} (h : ξ • z ≠ u) : lin u ξ z ≠ 0 := by
  rw [lin_eq]
  refine mul_ne_zero (denom_ne_zero ξ z) (sub_ne_zero.2 fun h' ↦ h ?_)
  exact UpperHalfPlane.ext h'

/-- Away from the orbit `Γ⁻¹u`, `S` is holomorphic. -/
theorem analyticAt_S (hk : 3 ≤ k) {z₀ : ℍ} (h : ∀ ξ : Γ, (ξ : SL(2, ℤ)) • z₀ ≠ u) :
    AnalyticAt ℂ (S Γ u k ∘ ofComplex) z₀ := by
  obtain ⟨s, T, hT, -, hS⟩ := exists_decomp Γ u hk z₀
  have ha : AnalyticAt ℂ (fun z ↦ ∑ ξ ∈ s, term u k ξ z + T z) z₀ :=
    (Finset.analyticAt_fun_sum s fun ξ _ ↦ analyticAt_term u k (lin_ne_zero u (h ξ))).add hT
  exact ha.congr hS.symm

theorem continuousAt_S (hk : 3 ≤ k) {z₀ : ℍ} (h : ∀ ξ : Γ, (ξ : SL(2, ℤ)) • z₀ ≠ u) :
    ContinuousAt (S Γ u k) z₀ := by
  have hc := (analyticAt_S Γ u hk h).continuousAt.comp (continuous_coe.continuousAt (x := z₀))
  refine hc.congr (Eventually.of_forall fun z ↦ ?_)
  simp

/-! ### The pole at `u` -/

/-- A central element of `SL₂(ℤ)` contributes `(z - u)^{-2k}`. -/
theorem term_of_mem_center {ξ : SL(2, ℤ)} (hξ : ξ ∈ Subgroup.center SL(2, ℤ)) (z : ℂ) :
    term u k ξ z = ((z - u) ^ (2 * k))⁻¹ := by
  obtain ⟨r, hr, hrξ⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hξ
  have h00 : ξ 0 0 = r := by rw [← hrξ, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
  have h01 : ξ 0 1 = 0 := by rw [← hrξ, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide)]
  have h10 : ξ 1 0 = 0 := by rw [← hrξ, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide)]
  have h11 : ξ 1 1 = r := by rw [← hrξ, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
  have hr2 : ((r : ℂ)) ^ 2 = 1 := by
    have : r ^ 2 = 1 := by simpa using hr
    exact_mod_cast congrArg (fun x : ℤ ↦ (x : ℂ)) this
  rw [term, lin, h00, h01, h10, h11]
  congr 1
  simp only [Int.cast_zero, zero_mul, add_zero, zero_add]
  rw [show (r : ℂ) * z - u * r = r * (z - u) by ring, mul_pow, pow_mul, hr2, one_pow, one_mul]

theorem tendsto_norm_aux (hk : 0 < k) {c : ℕ} (hc : 0 < c) {A : ℂ → ℂ} (hA : ContinuousAt A u) :
    Tendsto (fun z : ℂ ↦ ‖(c : ℂ) * ((z - u) ^ (2 * k))⁻¹ + A z‖) (𝓝[≠] (u : ℂ)) atTop := by
  have h0 : Tendsto (fun z : ℂ ↦ z - u) (𝓝[≠] (u : ℂ)) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_sub_right (u : ℂ)).tendsto (u : ℂ)).mono_left (nhdsWithin_le_nhds (s := {(u : ℂ)}ᶜ))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_ne_zero.2 hz
  have h1 : Tendsto (fun z : ℂ ↦ (c : ℝ) * ‖(z - u)⁻¹‖ ^ (2 * k)) (𝓝[≠] (u : ℂ)) atTop :=
    ((tendsto_pow_atTop (by omega)).comp (tendsto_norm_inv_nhdsNE_zero_atTop.comp h0)).const_mul_atTop
      (by exact_mod_cast hc)
  have h2 : Tendsto (fun z : ℂ ↦ -‖A z‖) (𝓝[≠] (u : ℂ)) (𝓝 (-‖A u‖)) :=
    ((hA.norm.tendsto).mono_left nhdsWithin_le_nhds).neg
  refine tendsto_atTop_mono (fun z ↦ ?_) (h1.atTop_add h2)
  have := norm_sub_le ((c : ℂ) * ((z - u) ^ (2 * k))⁻¹ + A z) (A z)
  rw [add_sub_cancel_right, norm_mul, Complex.norm_natCast, norm_inv, norm_pow] at this
  simp only [Function.comp_apply, norm_inv, inv_pow] at *
  linarith

/-- **`|S_u(z)| → ∞` as `z → u`**, when `u` is not an elliptic point of `SL₂(ℤ)` (its stabilizer is central). -/
theorem tendsto_norm_S (hk : 3 ≤ k) (hu : ∀ ξ : SL(2, ℤ), ξ • u = u → ξ ∈ Subgroup.center SL(2, ℤ)) :
    Tendsto (fun z ↦ ‖S Γ u k z‖) (𝓝[≠] u) atTop := by
  classical
  obtain ⟨s, T, hT, hmem, hS⟩ := exists_decomp Γ u hk u
  set s₁ := s.filter fun ξ : Γ ↦ (ξ : SL(2, ℤ)) • u = u
  set s₂ := s.filter fun ξ : Γ ↦ ¬ (ξ : SL(2, ℤ)) • u = u
  have h1 : (1 : Γ) ∈ s₁ := by
    rw [Finset.mem_filter]
    exact ⟨hmem 1 (by simp [u.im_pos]), by simp⟩
  have hc : 0 < s₁.card := Finset.card_pos.2 ⟨1, h1⟩
  set A : ℂ → ℂ := fun z ↦ ∑ ξ ∈ s₂, term u k ξ z + T z
  have hA : AnalyticAt ℂ A u := by
    refine (Finset.analyticAt_fun_sum s₂ fun ξ hξ ↦ analyticAt_term u k (lin_ne_zero u ?_)).add hT
    exact (Finset.mem_filter.1 hξ).2
  have hS' : (S Γ u k ∘ ofComplex) =ᶠ[𝓝 (u : ℂ)] fun z ↦ (s₁.card : ℂ) * ((z - u) ^ (2 * k))⁻¹ + A z := by
    filter_upwards [hS] with z hz
    rw [hz, ← Finset.sum_filter_add_sum_filter_not s (fun ξ ↦ (ξ : SL(2, ℤ)) • u = u), add_assoc]
    congr 1
    rw [Finset.sum_congr rfl fun ξ hξ ↦ term_of_mem_center u (hu _ (Finset.mem_filter.1 hξ).2) z]
    simp [s₁]
  have hC := (tendsto_norm_aux u (by omega) hc hA.continuousAt).congr' ((hS'.filter_mono nhdsWithin_le_nhds).mono
    fun z hz ↦ (congrArg norm hz).symm)
  have hcoe : Tendsto (fun z : ℍ ↦ (z : ℂ)) (𝓝[≠] u) (𝓝[≠] (u : ℂ)) :=
    continuous_coe.continuousWithinAt.tendsto_nhdsWithin fun z hz h ↦ hz (UpperHalfPlane.ext h)
  refine (hC.comp hcoe).congr fun z ↦ ?_
  simp

/-! ### The cusps -/

/-- High up, every `ξz` stays at distance `≥ Im(u)/2` from `u`. -/
theorem sep_of_im_ge (ξ : SL(2, ℤ)) {z : ℍ} (hz : max (2 * u.im) (2 / u.im) ≤ z.im) :
    u.im / 2 ≤ ‖((ξ • z : ℍ) : ℂ) - u‖ := by
  have hu := u.im_pos
  have hz0 := z.im_pos
  have h2u : 2 * u.im ≤ z.im := (le_max_left _ _).trans hz
  have h2u' : 2 / u.im ≤ z.im := (le_max_right _ _).trans hz
  have habs : |(ξ • z).im - u.im| ≤ ‖((ξ • z : ℍ) : ℂ) - u‖ := by
    have := abs_im_le_norm (((ξ • z : ℍ) : ℂ) - u)
    simpa using this
  have him : (ξ • z).im = z.im / Complex.normSq (denom ξ z) := by
    simpa using ModularGroup.im_smul_eq_div_normSq ξ z
  have hn : Complex.normSq (denom ξ z) = ((ξ 1 0 : ℝ) * z.re + ξ 1 1) ^ 2 + ((ξ 1 0 : ℝ) * z.im) ^ 2 := by
    rw [denom_sl, Complex.normSq_apply]
    simp
    ring
  by_cases hc : ξ 1 0 = 0
  · have hdet := ξ.det_coe
    rw [det_fin_two, hc, mul_zero, sub_zero] at hdet
    have h11 : (ξ 1 1 : ℝ) ^ 2 = 1 := by
      have : ξ 1 1 = 1 ∨ ξ 1 1 = -1 := Int.eq_one_or_neg_one_of_mul_eq_one' hdet |>.elim
        (fun h ↦ Or.inl h.2) (fun h ↦ Or.inr h.2)
      rcases this with h | h <;> simp [h]
    rw [hn, hc] at him
    simp only [Int.cast_zero, zero_mul, zero_add, h11, div_one] at him
    have := (abs_le.1 habs).2
    rw [abs_le] at habs
    linarith [habs.2, le_abs_self ((ξ • z).im - u.im)]
  · have hc1 : (1 : ℝ) ≤ (ξ 1 0 : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ ξ 1 0 ^ 2 := by nlinarith [sq_nonneg (ξ 1 0), Int.one_le_abs hc, sq_abs (ξ 1 0)]
      exact_mod_cast this
    have hN : z.im ^ 2 ≤ Complex.normSq (denom ξ z) := by
      rw [hn]; nlinarith [sq_nonneg ((ξ 1 0 : ℝ) * z.re + ξ 1 1), sq_nonneg z.im]
    have hle : (ξ • z).im ≤ u.im / 2 := by
      rw [him, div_le_iff₀ (by nlinarith)]
      have : 1 ≤ u.im / 2 * z.im := by
        rw [div_le_iff₀ hu] at h2u'; nlinarith
      nlinarith
    have := neg_abs_le ((ξ • z).im - u.im)
    linarith

variable [Γ.FiniteIndex]

theorem meromorphicAt_cusp_S (hk : 3 ≤ k) (γ : SL(2, ℤ)) :
    MeromorphicAt (Periodic.cuspFunction (cuspWidth Γ γ) ((S Γ u k ∣[(2 * (k : ℤ))] γ) ∘ ofComplex)) 0 := by
  obtain ⟨n, hn, hw⟩ := UncondDiff.exists_nat_cuspWidth Γ γ
  have hpos : 0 < cuspWidth Γ γ := by rw [hw]; exact_mod_cast hn
  have hper : Periodic ((S Γ u k ∣[(2 * (k : ℤ))] γ) ∘ ofComplex) (cuspWidth Γ γ) :=
    UncondDim.periodic_slash (fun δ hδ ↦ S_slash_eq Γ u k hδ) γ
  set Y := max (2 * u.im) (2 / u.im)
  have hY : 0 < Y := lt_max_of_lt_left (by linarith [u.im_pos])
  have hr : 0 < u.im / 2 := by linarith [u.im_pos]
  let e : Γ → SL(2, ℤ) := fun ξ ↦ (ξ : SL(2, ℤ)) * γ
  have he : Injective e := fun a b h ↦ Subtype.ext (mul_right_cancel h)
  -- holomorphy near `i∞`
  have hdiff : ∀ᶠ z in comap Complex.im atTop, DifferentiableAt ℂ ((S Γ u k ∣[(2 * (k : ℤ))] γ) ∘ ofComplex) z := by
    refine eventually_comap.2 (eventually_atTop.2 ⟨Y + 1, fun b hb z hz ↦ ?_⟩)
    set U : Set ℂ := {w | |w.re| < |z.re| + 1} ∩ {w | Y < w.im}
    have hU : IsOpen U := (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im)
    have hUH : ∀ w ∈ U, 0 < w.im := fun w hw ↦ hY.trans hw.2
    have hzU : z ∈ U := ⟨show |z.re| < |z.re| + 1 by linarith, show Y < z.im by rw [hz]; linarith⟩
    have hρU : ∀ w (hw : w ∈ U), EisensteinSeries.r ⟨⟨|z.re| + 1, Y⟩, hY⟩ ≤ EisensteinSeries.r ⟨w, hUH w hw⟩ :=
      fun w hw ↦ r_lower_bound_on_verticalStrip _ hY ⟨hw.1.le, hw.2.le⟩
    have hsep : ∀ i w (hw : w ∈ U), u.im / 2 ≤ ‖((e i • (⟨w, hUH w hw⟩ : ℍ) : ℍ) : ℂ) - u‖ :=
      fun i w hw ↦ sep_of_im_ge u (e i) (z := ⟨w, hUH w hw⟩) hw.2.le
    obtain ⟨hD, -⟩ := differentiableOn_tsum u k he hk hU hUH hr (r_pos _) hρU hsep
    refine (hD.differentiableAt (hU.mem_nhds hzU)).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hzU] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos (hUH w hw)]
    rw [S_slash_apply]
  -- boundedness near `i∞`
  have hbd : BoundedAtFilter (comap Complex.im atTop) ((S Γ u k ∣[(2 * (k : ℤ))] γ) ∘ ofComplex) := by
    set ρ := EisensteinSeries.r ⟨⟨n, Y⟩, hY⟩
    refine Asymptotics.IsBigO.of_bound (cst u k (u.im / 2) ρ * ∑' i, bnd k (e i)) ?_
    refine eventually_comap.2 (eventually_atTop.2 ⟨Y, fun b hb z hz ↦ ?_⟩)
    have hz0 : 0 < z.im := hY.trans_le (hz ▸ hb)
    set zH : ℍ := ⟨z, hz0⟩
    obtain ⟨m, hm⟩ := ModularGroup_T_zpow_mem_verticalStrip zH hn
    set w : ℍ := ModularGroup.T ^ ((n : ℤ) * m) • zH
    have hw' : (w : ℂ) = z + (m : ℂ) * n := by
      simp only [w, modular_T_zpow_smul, coe_vadd, zH, UpperHalfPlane.coe_mk]
      push_cast; ring
    have hwY : Y ≤ w.im := by
      have := hm.2; simp only [zH, UpperHalfPlane.mk_im] at this; rw [← hz] at hb; linarith
    have hF : ((S Γ u k ∣[(2 * (k : ℤ))] γ) ∘ ofComplex) z = (S Γ u k ∣[(2 * (k : ℤ))] γ) w := by
      have h1 := (hper.int_mul m) z
      have h2 : z + (m : ℂ) * ((cuspWidth Γ γ : ℝ) : ℂ) = (w : ℂ) := by rw [hw, hw']; push_cast; ring
      rw [← h1, h2]
      simp only [Function.comp_apply, ofComplex_apply]
    rw [hF, S_slash_apply, Pi.one_apply, norm_one, mul_one]
    exact (summable_and_norm_tsum_le u k he hk w hr (r_pos _)
      (r_lower_bound_on_verticalStrip _ hY ⟨hm.1, hwY⟩) fun i ↦ sep_of_im_ge u (e i) hwY).2
  have hD0 := Periodic.differentiableAt_cuspFunction_zero hpos hper hdiff hbd
  have hev := Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero hpos hper hdiff
  have hnhds : ∀ᶠ q in 𝓝 (0 : ℂ),
      DifferentiableAt ℂ (Periodic.cuspFunction (cuspWidth Γ γ) ((S Γ u k ∣[(2 * (k : ℤ))] γ) ∘ ofComplex)) q := by
    filter_upwards [eventually_nhdsWithin_iff.1 hev] with q hq
    by_cases h0 : q = 0
    · rw [h0]; exact hD0
    · exact hq h0
  exact (Complex.analyticAt_iff_eventually_differentiableAt.2 hnhds).meromorphicAt

/-- **`S_u` is a meromorphic modular form of weight `2k` for every finite-index `Γ`**, `k ≥ 3`. -/
@[kb "milne2017mf" "Section 4, Poincare series (pdf pp. 60-64), with a pole: a meromorphic modular form"]
theorem isMeromorphicModularForm_S (hk : 3 ≤ k) : IsMeromorphicModularForm Γ k (S Γ u k) where
  slash _ hγ := S_slash_eq Γ u k hγ
  meromorphic z := meromorphicAt_S Γ u hk z
  meromorphic_cusp γ := meromorphicAt_cusp_S Γ u hk γ

end ModularFormsKB.Milne.Wave13
