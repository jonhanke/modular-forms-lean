import ModularFormsKB.Milne.Ch3.WeierstrassUniformization

/-!
# Milne, Chapter 3: the invariants `g₂, g₃` determine the lattice

If two lattices have the same `g₂` and `g₃`, they are equal (`lattice_eq_of_g₂_eq_of_g₃_eq`). The proof compares
`℘_Λ` and `℘_Λ'` near `0`: their difference `h` is holomorphic at `0`, vanishes there to order at least `5`
(the Taylor coefficients are `(n+1) G_{n+2}`, and `G₄, G₆` are fixed by `g₂, g₃`), and by the differential
equation `℘'' = 6℘² - g₂/2` it satisfies `z² h'' = h · (12 + O(z²))`. A zero of exact order `N` of such a
function forces `N(N-1) = 12`, i.e. `N = 4`; so `h` vanishes identically, `℘_Λ = ℘_Λ'`, and the lattices are the
pole sets.

As a consequence, two lattices have the same `j`-invariant exactly when they are homothetic
(`j_eq_iff_homothetic`), the third part of `ComplexUniformization`.
-/

open Complex Filter Topology Set PeriodPair

namespace ModularFormsKB.Milne

/-- **A zero of a solution of `z² h'' = h b`, `b(0) = 12`, of order at least `5` is of infinite order.** -/
theorem analyticOrderAt_eq_top_of_ode {h b : ℂ → ℂ} (hh : AnalyticAt ℂ h 0) (hb : ContinuousAt b 0)
    (hb0 : b 0 = 12) (hode : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ^ 2 * deriv (deriv h) z = h z * b z)
    (hord : (5 : ℕ∞) ≤ analyticOrderAt h 0) : analyticOrderAt h 0 = ⊤ := by
  by_contra hne
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.1 hne
  rw [← hN] at hord
  have hN5 : 5 ≤ N := by exact_mod_cast hord
  obtain ⟨g, hg, hg0, hhg⟩ := hh.analyticOrderAt_eq_natCast.1 hN.symm
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
  have hgev : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ g z := hg.eventually_analyticAt
  have hgev' : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ (deriv g) z := hg.deriv.eventually_analyticAt
  have e0 : h =ᶠ[𝓝 0] fun z ↦ z ^ (k + 2) * g z := by
    filter_upwards [hhg] with z hz; simp [hz]
  have e1 : deriv h =ᶠ[𝓝 0] fun z ↦ ((k : ℂ) + 2) * z ^ (k + 1) * g z + z ^ (k + 2) * deriv g z := by
    filter_upwards [e0.eventuallyEq_nhds, hgev] with z hz hgz
    rw [hz.deriv_eq, ((hasDerivAt_pow (k + 2) z).fun_mul hgz.differentiableAt.hasDerivAt).deriv]
    push_cast; ring
  have e2 : deriv (deriv h) =ᶠ[𝓝 0] fun z ↦ ((k : ℂ) + 2) * ((k : ℂ) + 1) * z ^ k * g z +
      2 * ((k : ℂ) + 2) * z ^ (k + 1) * deriv g z + z ^ (k + 2) * deriv (deriv g) z := by
    filter_upwards [e1.eventuallyEq_nhds, hgev, hgev'] with z hz hgz hgz'
    rw [hz.deriv_eq]
    have d1 := ((hasDerivAt_pow (k + 1) z).const_mul ((k : ℂ) + 2)).fun_mul hgz.differentiableAt.hasDerivAt
    have d2 := (hasDerivAt_pow (k + 2) z).fun_mul hgz'.differentiableAt.hasDerivAt
    rw [(d1.fun_add d2).deriv]
    push_cast; ring
  have hc0 : ContinuousAt g 0 := hg.continuousAt
  have hc1 : ContinuousAt (deriv g) 0 := hg.deriv.continuousAt
  have hc2 : ContinuousAt (deriv (deriv g)) 0 := hg.deriv.deriv.continuousAt
  have hlim : Tendsto (fun z ↦ ((k : ℂ) + 2) * ((k : ℂ) + 1) * g z + 2 * ((k : ℂ) + 2) * z * deriv g z +
      z ^ 2 * deriv (deriv g) z) (𝓝[≠] 0) (𝓝 (((k : ℂ) + 2) * ((k : ℂ) + 1) * g 0)) := by
    have hc : ContinuousAt (fun z ↦ ((k : ℂ) + 2) * ((k : ℂ) + 1) * g z + 2 * ((k : ℂ) + 2) * z *
        deriv g z + z ^ 2 * deriv (deriv g) z) 0 := by
      exact ((continuousAt_const.mul hc0).add ((continuousAt_const.mul continuousAt_id).mul hc1)).add
        ((continuousAt_id.pow 2).mul hc2)
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    simpa using this
  have hlim2 : Tendsto (fun z ↦ g z * b z) (𝓝[≠] 0) (𝓝 (g 0 * 12)) := by
    have := (hc0.mul hb).tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    simp only [Pi.mul_apply, hb0] at this
    exact this
  have heq : (fun z ↦ ((k : ℂ) + 2) * ((k : ℂ) + 1) * g z + 2 * ((k : ℂ) + 2) * z * deriv g z +
      z ^ 2 * deriv (deriv g) z) =ᶠ[𝓝[≠] 0] fun z ↦ g z * b z := by
    filter_upwards [hode, nhdsWithin_le_nhds e0, nhdsWithin_le_nhds e2, self_mem_nhdsWithin]
      with z hz h0 h2 hz0
    rw [h2, h0] at hz
    have hzk : z ^ (k + 2) ≠ 0 := pow_ne_zero _ hz0
    apply mul_left_cancel₀ hzk
    linear_combination hz
  have hlim' := tendsto_nhds_unique (hlim.congr' heq) hlim2
  have h12 : ((k : ℂ) + 2) * ((k : ℂ) + 1) = 12 :=
    mul_right_cancel₀ hg0 (by linear_combination hlim')
  have h12' : (k + 2) * (k + 1) = 12 := by exact_mod_cast h12
  nlinarith

/-! ### The differential equation `℘'' = 6℘² - g₂/2` -/

theorem derivWeierstrassP_mul_ode {L : PeriodPair} {z : ℂ} (hz : z ∉ L.lattice) :
    ℘'[L] z * (2 * deriv ℘'[L] z - (12 * ℘[L] z ^ 2 - L.g₂)) = 0 := by
  have hU : (L.lattice : Set ℂ)ᶜ ∈ 𝓝 z := L.isClosed_lattice.isOpen_compl.mem_nhds hz
  have heq : (fun u ↦ ℘'[L] u ^ 2) =ᶠ[𝓝 z] fun u ↦ 4 * ℘[L] u ^ 3 - L.g₂ * ℘[L] u - L.g₃ := by
    filter_upwards [hU] with u hu using L.derivWeierstrassP_sq u hu
  have hP : HasDerivAt ℘[L] (℘'[L] z) z := by
    have := (analyticAt_weierstrassP hz).differentiableAt.hasDerivAt
    rwa [deriv_weierstrassP] at this
  have hP' : HasDerivAt ℘'[L] (deriv ℘'[L] z) z :=
    (analyticAt_derivWeierstrassP hz).differentiableAt.hasDerivAt
  have h1 := (hP'.fun_pow 2).deriv
  have h2 := ((((hP.fun_pow 3).const_mul 4).fun_sub (hP.const_mul L.g₂)).sub_const L.g₃).deriv
  have := heq.deriv_eq
  rw [h1, h2] at this
  push_cast at this
  linear_combination this

theorem deriv_derivWeierstrassP_eq (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2 := by
  have hgen : ∀ u, u ∉ L.lattice → ℘'[L] u ≠ 0 → deriv ℘'[L] u = 6 * ℘[L] u ^ 2 - L.g₂ / 2 := by
    intro u hu hne
    have := derivWeierstrassP_mul_ode hu
    have := (mul_eq_zero.1 this).resolve_left hne
    linear_combination this / 2
  by_cases hne : ℘'[L] z ≠ 0
  · exact hgen z hz hne
  have hE : EllFun L ℘'[L] := EllFun.of_ne_top isDoublyPeriodic_derivWeierstrassP (z₀ := 0)
    (by rw [meromorphicOrderAt_derivWeierstrassP L.lattice.zero_mem]; decide)
  have han := analyticAt_derivWeierstrassP hz
  have hev : ∀ᶠ u in 𝓝[≠] z, ℘'[L] u ≠ 0 := by
    rcases han.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (meromorphicOrderAt_eq_top_iff.2 (nhdsWithin_le_nhds h)) (hE.2 z)
    · exact h
  have hU : (L.lattice : Set ℂ)ᶜ ∈ 𝓝 z := L.isClosed_lattice.isOpen_compl.mem_nhds hz
  have hc1 : ContinuousAt (deriv ℘'[L]) z := han.deriv.continuousAt
  have hc2 : ContinuousAt (fun u ↦ 6 * ℘[L] u ^ 2 - L.g₂ / 2) z :=
    ((continuousAt_const.mul ((analyticAt_weierstrassP hz).continuousAt.pow 2)).sub
      continuousAt_const)
  have heq : deriv ℘'[L] =ᶠ[𝓝[≠] z] fun u ↦ 6 * ℘[L] u ^ 2 - L.g₂ / 2 := by
    filter_upwards [hev, nhdsWithin_le_nhds hU] with u hu hu' using hgen u hu' hu
  exact tendsto_nhds_unique ((hc1.tendsto.mono_left nhdsWithin_le_nhds).congr' heq)
    (hc2.tendsto.mono_left nhdsWithin_le_nhds)

/-! ### Taylor coefficients at `0` -/

theorem weierstrassPExcept_zero_zero (L : PeriodPair) : L.weierstrassPExcept 0 0 = 0 := by
  unfold weierstrassPExcept
  refine (tsum_congr fun l ↦ ?_).trans tsum_zero
  split_ifs
  · rfl
  · simp

theorem iteratedDeriv_weierstrassPExcept_zero_eq (L L' : PeriodPair) (h₂ : L.g₂ = L'.g₂)
    (h₃ : L.g₃ = L'.g₃) {n : ℕ} (hn : n ≤ 4) :
    iteratedDeriv n (L.weierstrassPExcept 0) 0 = iteratedDeriv n (L'.weierstrassPExcept 0) 0 := by
  rw [L.iteratedDeriv_weierstrassPExcept_self, L'.iteratedDeriv_weierstrassPExcept_self,
    L.sumInvPow_zero, L'.sumInvPow_zero, weierstrassPExcept_zero_zero, weierstrassPExcept_zero_zero]
  have hG4 : L.G 4 = L'.G 4 := by
    have : 60 * L.G 4 = 60 * L'.G 4 := h₂
    exact mul_left_cancel₀ (by norm_num) this
  have hG6 : L.G 6 = L'.G 6 := by
    have : 140 * L.G 6 = 140 * L'.G 6 := h₃
    exact mul_left_cancel₀ (by norm_num) this
  interval_cases n
  · rfl
  · simp [L.G_eq_zero_of_odd 3 (by decide), L'.G_eq_zero_of_odd 3 (by decide)]
  · simp [hG4]
  · simp [L.G_eq_zero_of_odd 5 (by decide), L'.G_eq_zero_of_odd 5 (by decide)]
  · simp [hG6]

/-! ### `g₂, g₃` determine the lattice -/

theorem weierstrassPExcept_zero_eq (M : PeriodPair) {z : ℂ} (_hz : z ≠ 0) :
    M.weierstrassPExcept 0 z = ℘[M] z - 1 / z ^ 2 := by
  have := M.weierstrassPExcept_def ⟨0, M.lattice.zero_mem⟩ z
  simpa [sub_eq_add_neg] using this

/-- **The lattice is determined by `g₂` and `g₃`.** -/
theorem lattice_eq_of_g₂_eq_of_g₃_eq {L L' : PeriodPair} (h₂ : L.g₂ = L'.g₂) (h₃ : L.g₃ = L'.g₃) :
    L.lattice = L'.lattice := by
  set h : ℂ → ℂ := fun z ↦ L.weierstrassPExcept 0 z - L'.weierstrassPExcept 0 z with hh_def
  have hφ : AnalyticAt ℂ (L.weierstrassPExcept 0) 0 := L.analyticAt_weierstrassPExcept 0
  have hφ' : AnalyticAt ℂ (L'.weierstrassPExcept 0) 0 := L'.analyticAt_weierstrassPExcept 0
  have hh : AnalyticAt ℂ h 0 := hφ.sub hφ'
  have hU : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice ∧ z ∉ L'.lattice := by
    filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
      nhdsWithin_le_nhds (L'.compl_lattice_sdiff_singleton_mem_nhds 0), self_mem_nhdsWithin]
      with z h1 h2 h0
    exact ⟨fun hz ↦ h1 ⟨hz, h0⟩, fun hz ↦ h2 ⟨hz, h0⟩⟩
  set b : ℂ → ℂ := fun z ↦ 12 + 6 * z ^ 2 * (L.weierstrassPExcept 0 z + L'.weierstrassPExcept 0 z)
  have hb : ContinuousAt b 0 := by
    have c1 : ContinuousAt (fun z : ℂ ↦ (6 : ℂ) * z ^ 2) 0 :=
      continuousAt_const.mul (continuousAt_id.pow 2)
    have c2 : ContinuousAt (fun z : ℂ ↦ L.weierstrassPExcept 0 z + L'.weierstrassPExcept 0 z) 0 :=
      hφ.continuousAt.add hφ'.continuousAt
    exact continuousAt_const.add (c1.mul c2)
  have hb0 : b 0 = 12 := by simp [b]
  have hode : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ^ 2 * deriv (deriv h) z = h z * b z := by
    filter_upwards [hU, self_mem_nhdsWithin] with z hzL hz0
    obtain ⟨hzL, hzL'⟩ := hzL
    have hz0 : z ≠ 0 := hz0
    have hloc : h =ᶠ[𝓝 z] fun u ↦ ℘[L] u - ℘[L'] u := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz0] with u hu
      simp only [h, weierstrassPExcept_zero_eq L hu, weierstrassPExcept_zero_eq L' hu]; ring
    have hd1 : deriv h =ᶠ[𝓝 z] fun u ↦ ℘'[L] u - ℘'[L'] u := by
      filter_upwards [hloc.eventuallyEq_nhds, L.isClosed_lattice.isOpen_compl.mem_nhds hzL,
        L'.isClosed_lattice.isOpen_compl.mem_nhds hzL'] with u hu h1 h2
      rw [hu.deriv_eq, deriv_fun_sub (analyticAt_weierstrassP h1).differentiableAt
        (analyticAt_weierstrassP h2).differentiableAt, deriv_weierstrassP, deriv_weierstrassP]
    have hd2 : deriv (deriv h) z = deriv ℘'[L] z - deriv ℘'[L'] z := by
      rw [hd1.deriv_eq, deriv_fun_sub (analyticAt_derivWeierstrassP hzL).differentiableAt
        (analyticAt_derivWeierstrassP hzL').differentiableAt]
    rw [hd2, deriv_derivWeierstrassP_eq L hzL, deriv_derivWeierstrassP_eq L' hzL', h₂]
    simp only [h, b, weierstrassPExcept_zero_eq L hz0, weierstrassPExcept_zero_eq L' hz0]
    field_simp
    ring
  have hord : ((5 : ℕ) : ℕ∞) ≤ analyticOrderAt h 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hh]
    intro i hi
    rw [hh_def, iteratedDeriv_fun_sub hφ.contDiffAt hφ'.contDiffAt,
      iteratedDeriv_weierstrassPExcept_zero_eq L L' h₂ h₃ (by omega), sub_self]
  have htop := analyticOrderAt_eq_top_of_ode hh hb hb0 hode hord
  rw [analyticOrderAt_eq_top] at htop
  -- `℘_L = ℘_L'` near `0`, hence everywhere off a discrete set
  have hF : MeromorphicOn (fun z ↦ ℘[L] z - ℘[L'] z) univ := fun z _ ↦
    (L.meromorphic_weierstrassP z).sub (L'.meromorphic_weierstrassP z)
  have h0top : meromorphicOrderAt (fun z ↦ ℘[L] z - ℘[L'] z) 0 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [nhdsWithin_le_nhds htop, self_mem_nhdsWithin] with z hz hz0
    have := hz
    simp only [h, weierstrassPExcept_zero_eq L hz0, weierstrassPExcept_zero_eq L' hz0] at this
    linear_combination this
  have hcod := ((meromorphicOn_univ.1 hF).exists_meromorphicOrderAt_eq_top_iff_eventually_zero).1
    ⟨0, h0top⟩
  have hloc : ∀ z, ℘[L] =ᶠ[𝓝[≠] z] ℘[L'] := fun z ↦ by
    filter_upwards [(eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.1 hcod) z] with u hu
    exact sub_eq_zero.1 hu
  have hmem : ∀ (M : PeriodPair) (z : ℂ), z ∈ M.lattice ↔ meromorphicOrderAt ℘[M] z < 0 := by
    intro M z
    constructor
    · intro hz; rw [M.order_weierstrassP z hz]; decide
    · intro hneg; by_contra hz
      exact not_le.2 hneg (analyticAt_weierstrassP hz).meromorphicOrderAt_nonneg
  ext z
  rw [hmem L z, hmem L' z, meromorphicOrderAt_congr (hloc z)]

/-! ### `j(Λ) = j(Λ')` exactly when `Λ' = αΛ` -/

theorem variableChange_shortWeierstrass {L L' : PeriodPair} {C : WeierstrassCurve.VariableChange ℂ}
    (hC : C • L.weierstrassCurve = L'.weierstrassCurve) :
    L'.g₂ = L.g₂ / (C.u : ℂ) ^ 4 ∧ L'.g₃ = L.g₃ / (C.u : ℂ) ^ 6 := by
  have h1 := congrArg WeierstrassCurve.a₁ hC
  have h2 := congrArg WeierstrassCurve.a₂ hC
  have h3 := congrArg WeierstrassCurve.a₃ hC
  have h4 := congrArg WeierstrassCurve.a₄ hC
  have h6 := congrArg WeierstrassCurve.a₆ hC
  simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆, weierstrassCurve_a₁, weierstrassCurve_a₂,
    weierstrassCurve_a₃, weierstrassCurve_a₄, weierstrassCurve_a₆] at h1 h2 h3 h4 h6
  have hu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
  have hs : C.s = 0 := by
    have : (↑C.u⁻¹ : ℂ) * (0 + 2 * C.s) = 0 := h1
    simpa [hu] using this
  have hr : C.r = 0 := by
    have : (↑C.u⁻¹ : ℂ) ^ 2 * (0 - C.s * 0 + 3 * C.r - C.s ^ 2) = 0 := h2
    simp [hs, hu] at this; exact this
  have ht : C.t = 0 := by
    have : (↑C.u⁻¹ : ℂ) ^ 3 * (0 + C.r * 0 + 2 * C.t) = 0 := h3
    simp [hr, hu] at this; exact this
  simp only [hs, hr, ht] at h4 h6
  constructor
  · have : (↑C.u⁻¹ : ℂ) ^ 4 * (-(L.g₂ / 4)) = -(L'.g₂ / 4) := by simpa using h4
    rw [Units.val_inv_eq_inv_val] at this
    field_simp at this ⊢
    linear_combination this
  · have : (↑C.u⁻¹ : ℂ) ^ 6 * (-(L.g₃ / 4)) = -(L'.g₃ / 4) := by simpa using h6
    rw [Units.val_inv_eq_inv_val] at this
    field_simp at this ⊢
    linear_combination this

/-- **Two lattices have the same `j`-invariant exactly when they are homothetic.** -/
theorem j_eq_iff_homothetic (L L' : PeriodPair) :
    L.weierstrassCurve.j = L'.weierstrassCurve.j ↔
      ∃ α : ℂ, α ≠ 0 ∧ L'.lattice = L.lattice.map (LinearMap.mulLeft ℤ α) := by
  constructor
  · intro hj
    obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq L.weierstrassCurve
      L'.weierstrassCurve hj
    obtain ⟨h₂, h₃⟩ := variableChange_shortWeierstrass hC
    refine ⟨C.u, C.u.ne_zero, ?_⟩
    rw [← lattice_smul]
    exact lattice_eq_of_g₂_eq_of_g₃_eq (by rw [g₂_smul, h₂]) (by rw [g₃_smul, h₃])
  · rintro ⟨α, hα, h⟩
    set c := Units.mk0 α hα
    have hG : L'.G = (c • L).G := G_eq_of_lattice_eq (by rw [lattice_smul]; exact h)
    have e2 : L'.g₂ = L.g₂ / α ^ 4 := by
      rw [show L'.g₂ = 60 * L'.G 4 from rfl, hG, show 60 * (c • L).G 4 = (c • L).g₂ from rfl, g₂_smul]
      rfl
    have e3 : L'.g₃ = L.g₃ / α ^ 6 := by
      rw [show L'.g₃ = 140 * L'.G 6 from rfl, hG, show 140 * (c • L).G 6 = (c • L).g₃ from rfl, g₃_smul]
      rfl
    have hΔ := g₂_cube_sub_g₃_sq_ne_zero L
    rw [weierstrassCurve_j, weierstrassCurve_j, e2, e3]
    field_simp

end ModularFormsKB.Milne
