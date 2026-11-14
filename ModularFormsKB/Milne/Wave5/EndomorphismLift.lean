import ModularFormsKB.Milne.Wave5.PointMapEval
import ModularFormsKB.Milne.Ch12.JIntegralCM

/-!
# Milne wave 5: every endomorphism of `E(Λ)` is `[z] ↦ [αz]`

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31, Proposition 3.3 with Proposition 3.12 (pdf
pp. 42, 47): a holomorphic map `ℂ/Λ → ℂ/Λ` fixing `0` is `[z] ↦ [αz]`, and `ℂ/Λ ≅ E(Λ)`. The library states the
consequence for Tau Ceti's algebraic endomorphisms as the named statement `EndomorphismLiftStatement`
(`ModularFormsKB/Milne/Ch3/ComplexUniformization.lean`). It is proved here.

**Proof.** Let `f = φ` be a nonzero endomorphism. By Tau Ceti `x ∘ φ = r(x)`, and `y ∘ φ = y s(x)`
(`exists_fieldPullback_genericY_eq`), so away from finitely many `x`-values
`φ(℘(z), ℘'(z)/2) = (r(℘(z)), ℘'(z)/2 · s(℘(z)))` (`pointMap_ofIsogeny_some_eq`). Choose `z₀` generic, with the
image point `P(u₀)` not of order two; `℘` has a holomorphic local inverse at `u₀`, and `ψ(z) = ℘⁻¹(r(℘(z)))` satisfies
`P(ψ(z)) = φ(P(z))` near `z₀` (the `y`-coordinates agree by continuity, being square roots of the same number and
nonzero at `z₀`). This replaces Milne's lifting of a map of tori through the covering `ℂ → ℂ/Λ`. Then
`c(w) = ψ(z₀ + w) - ψ(z₀)` satisfies `P(c(w)) = φ(P(w))` for small `w`; `c(w + w') - c(w) - c(w')` lies in `Λ` and
is small, hence `0`; so `c(w) = 2ⁿ c(w/2ⁿ) → c'(0) w`, i.e. `c(w) = αw` with `α = ψ'(z₀)`. Finally
`φ(P(z)) = n φ(P(z/n)) = n P(αz/n) = P(αz)` for `n` large.
-/

open Complex PeriodPair TauCeti TauCeti.Isogeny Polynomial Filter Topology WeierstrassCurve.Affine

namespace ModularFormsKB.Milne.Wave5

variable (L : PeriodPair)

/-! ### From a local lift to multiplication by a constant -/

/-- **A local holomorphic lift at one point is multiplication by a constant.** If `P(ψ(z)) = f(P(z))` near `z₀` and
`ψ` has derivative `α` at `z₀`, then `f(P(z)) = P(αz)` for every `z`. -/
theorem pointMap_eq_weierstrassPoint_mul_of_local
    (f : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine) {z₀ α : ℂ} {ψ : ℂ → ℂ}
    (hψ : HasDerivAt ψ α z₀)
    (hloc : ∀ᶠ z in 𝓝 z₀, L.weierstrassPoint (ψ z) = f.pointMap (L.weierstrassPoint z)) (z : ℂ) :
    f.pointMap (L.weierstrassPoint z) = L.weierstrassPoint (α * z) := by
  set c : ℂ → ℂ := fun w ↦ ψ (z₀ + w) - ψ z₀ with hc_def
  have hc : HasDerivAt c α 0 := by
    have h1 : HasDerivAt (fun w : ℂ ↦ z₀ + w) 1 0 := (hasDerivAt_id 0).const_add z₀
    have h2 : HasDerivAt ψ α (z₀ + 0) := by rwa [add_zero]
    have := (h2.comp (0 : ℂ) h1).sub_const (ψ z₀)
    simpa [hc_def, Function.comp_def] using this
  have hc0 : c 0 = 0 := by simp [hc_def]
  -- the lifting property for `c` near `0`
  have hz₀ : L.weierstrassPoint (ψ z₀) = f.pointMap (L.weierstrassPoint z₀) := hloc.self_of_nhds
  have hloc0 : ∀ᶠ w in 𝓝 (0 : ℂ), L.weierstrassPoint (c w) = f.pointMap (L.weierstrassPoint w) := by
    have ht : Tendsto (fun w : ℂ ↦ z₀ + w) (𝓝 0) (𝓝 z₀) := by
      have hc : Continuous fun w : ℂ ↦ z₀ + w := by fun_prop
      simpa using hc.tendsto 0
    filter_upwards [ht.eventually hloc] with w hw
    have hsub : L.weierstrassPoint w = L.weierstrassPoint (z₀ + w) - L.weierstrassPoint z₀ := by
      rw [weierstrassPoint_add]; abel_nf
    rw [hsub, Hom.pointMap_sub, ← hw, ← hz₀, hc_def]
    simp only
    rw [show ψ (z₀ + w) = (ψ (z₀ + w) - ψ z₀) + ψ z₀ by ring, weierstrassPoint_add]
    abel_nf
  -- the lattice is discrete
  obtain ⟨ε, hε, hball⟩ := Metric.exists_ball_inter_eq_singleton_of_mem_discrete
    (s := (L.lattice : Set ℂ)) ⟨inferInstanceAs (DiscreteTopology L.lattice)⟩ (zero_mem L.lattice)
  obtain ⟨η₁, hη₁, h₁⟩ := Metric.eventually_nhds_iff.1 hloc0
  obtain ⟨η₂, hη₂, h₂⟩ := Metric.continuousAt_iff.1 hc.continuousAt (ε / 3) (by positivity)
  set η := min η₁ η₂ with hη_def
  have hη : 0 < η := lt_min hη₁ hη₂
  have hlift : ∀ w : ℂ, ‖w‖ < η → L.weierstrassPoint (c w) = f.pointMap (L.weierstrassPoint w) :=
    fun w hw ↦ h₁ (by simpa using hw.trans_le (min_le_left _ _))
  have hsmall : ∀ w : ℂ, ‖w‖ < η → ‖c w‖ < ε / 3 := fun w hw ↦ by
    have := h₂ (x := w) (by simpa using hw.trans_le (min_le_right _ _))
    simpa [hc0] using this
  -- local additivity
  have hadd : ∀ w w' : ℂ, ‖w‖ < η / 2 → ‖w'‖ < η / 2 → c (w + w') = c w + c w' := by
    intro w w' hw hw'
    have hw1 : ‖w‖ < η := by linarith
    have hw1' : ‖w'‖ < η := by linarith
    have hww : ‖w + w'‖ < η := (norm_add_le _ _).trans_lt (by linarith)
    set δ := c (w + w') - c w - c w'
    have hδ : δ ∈ L.lattice := by
      rw [← L.weierstrassPoint_eq_zero_iff]
      have e : L.weierstrassPoint δ = L.weierstrassPoint (c (w + w')) - L.weierstrassPoint (c w) -
          L.weierstrassPoint (c w') := by
        simp only [δ, sub_eq_add_neg, weierstrassPoint_add, weierstrassPoint_neg]
      rw [e, hlift _ hww, hlift _ hw1, hlift _ hw1', ← Hom.pointMap_sub, ← Hom.pointMap_sub]
      rw [show L.weierstrassPoint (w + w') - L.weierstrassPoint w - L.weierstrassPoint w' = 0 by
        rw [weierstrassPoint_add]; abel]
      exact Hom.pointMap_zero f
    have hδs : ‖δ‖ < ε := by
      have := hsmall _ hww; have := hsmall _ hw1; have := hsmall _ hw1'
      calc ‖δ‖ ≤ ‖c (w + w')‖ + ‖c w‖ + ‖c w'‖ := by
            simp only [δ]
            exact (norm_sub_le _ _).trans (by linarith [norm_sub_le (c (w + w')) (c w)])
        _ < ε := by linarith
    have : δ ∈ Metric.ball (0 : ℂ) ε ∩ (L.lattice : Set ℂ) := ⟨by simpa using hδs, hδ⟩
    rw [hball] at this
    have h0 : δ = 0 := this
    simp only [δ] at h0
    linear_combination h0
  -- `c w = 2ⁿ c (w / 2ⁿ)`
  have hpow : ∀ n : ℕ, ∀ w : ℂ, ‖w‖ < η / 2 → c w = 2 ^ n * c (w / 2 ^ n) := by
    intro n
    induction n with
    | zero => intro w _; simp
    | succ n ih =>
      intro w hw
      have hs : ‖w / 2 ^ (n + 1)‖ < η / 2 := by
        rw [norm_div, norm_pow, RCLike.norm_ofNat]
        exact (div_le_self (norm_nonneg _) (one_le_pow₀ (by norm_num))).trans_lt hw
      have e : w / 2 ^ n = w / 2 ^ (n + 1) + w / 2 ^ (n + 1) := by
        rw [pow_succ]; field_simp; ring
      rw [ih w hw, e, hadd _ _ hs hs, pow_succ]
      ring
  -- `c w = α w` for small `w`
  have hlin : ∀ w : ℂ, ‖w‖ < η / 2 → c w = α * w := by
    intro w hw
    rcases eq_or_ne w 0 with rfl | hw0
    · simp [hc0]
    have hslope := hc.tendsto_slope_zero
    have hseq : Tendsto (fun n : ℕ ↦ w / 2 ^ n) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
      · have : Tendsto (fun n : ℕ ↦ w * ((1 / 2 : ℂ) ^ n)) atTop (𝓝 (w * 0)) :=
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)).const_mul w
        simpa [div_eq_mul_inv] using this
      · exact div_ne_zero hw0 (pow_ne_zero _ two_ne_zero)
    have hcomp := hslope.comp hseq
    have hconst : (fun t : ℂ ↦ t⁻¹ • (c (0 + t) - c 0)) ∘ (fun n : ℕ ↦ w / 2 ^ n) =
        fun _ ↦ c w / w := by
      funext n
      simp only [Function.comp, zero_add, hc0, sub_zero, smul_eq_mul]
      rw [hpow n w hw]
      field_simp
    rw [hconst] at hcomp
    have := tendsto_nhds_unique tendsto_const_nhds hcomp
    field_simp at this
    linear_combination this
  -- extend by divisibility
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * ‖z‖ / η)
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  set w := z / (n + 1 : ℂ)
  have hw : ‖w‖ < η / 2 := by
    have hnorm : ‖(n + 1 : ℂ)‖ = n + 1 := by
      rw [show (n + 1 : ℂ) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]; push_cast; ring
    rw [norm_div, hnorm, div_lt_iff₀ hn1]
    rw [div_lt_iff₀ hη] at hn
    nlinarith [norm_nonneg z]
  have hz : z = (n + 1 : ℕ) • w := by
    rw [nsmul_eq_mul]; push_cast; simp only [w]; field_simp
  have hαz : α * z = (n + 1 : ℕ) • (α * w) := by rw [hz, nsmul_eq_mul, nsmul_eq_mul]; ring
  have hP : ∀ (m : ℕ) (u : ℂ), L.weierstrassPoint (m • u) = m • L.weierstrassPoint u := by
    intro m u
    induction m with
    | zero => simp
    | succ m ih => rw [succ_nsmul, weierstrassPoint_add, ih, succ_nsmul]
  rw [hαz, hP, hz, hP, Hom.pointMap_nsmul, ← hlift w (by linarith), hlin w hw]

/-! ### A local holomorphic lift at a generic point -/

/-- The right side `x³ - (g₂/4) x - g₃/4` of the Weierstrass equation of `E(Λ)`. -/
noncomputable def cubicPoly : ℂ[X] := X ^ 3 - C (L.g₂ / 4) * X - C (L.g₃ / 4)

theorem cubicPoly_ne_zero : cubicPoly L ≠ 0 := by
  intro h
  have := congrArg (Polynomial.coeff · 3) h
  simp [cubicPoly] at this

theorem sq_eq_cubicPoly {x y : ℂ} (h : L.weierstrassCurve.toAffine.Equation x y) :
    y ^ 2 = (cubicPoly L).eval x := by
  rw [equation_iff] at h
  simp only [weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, weierstrassCurve_a₄,
    weierstrassCurve_a₆] at h
  simp only [cubicPoly, eval_sub, eval_pow, eval_X, eval_mul, eval_C]
  linear_combination h

/-- **A nonzero endomorphism of `E(Λ)` lifts to a holomorphic map near some point**: there are `z₀`, `ψ` with a
derivative at `z₀`, and `P(ψ(z)) = f(P(z))` for `z` near `z₀`. -/
theorem exists_local_lift (f : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine) (hf : f ≠ 0) :
    ∃ (z₀ α : ℂ) (ψ : ℂ → ℂ), HasDerivAt ψ α z₀ ∧
      ∀ᶠ z in 𝓝 z₀, L.weierstrassPoint (ψ z) = f.pointMap (L.weierstrassPoint z) := by
  classical
  obtain ⟨φ, rfl⟩ := (Hom.eq_zero_or_exists_ofIsogeny f).resolve_left hf
  obtain ⟨s, hs⟩ := exists_fieldPullback_genericY_eq φ L.weierstrassCurve_a₁ L.weierstrassCurve_a₃
    L.weierstrassCurve_a₁ L.weierstrassCurve_a₃
  set r := φ.xRatFunc
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero] at hs
    exact genericY_ne_zero_of_a₁_a₃ L.weierstrassCurve_a₁ L.weierstrassCurve_a₃
      ((map_eq_zero_iff _ φ.fieldPullback.toRingHom.injective).1 hs)
  have hsn : s.num ≠ 0 := by rwa [Ne, RatFunc.num_eq_zero_iff]
  set B : ℂ[X] := r.denom * s.denom * s.num * cubicPoly L
  have hB : B ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero r.denom_ne_zero s.denom_ne_zero) hsn)
    (cubicPoly_ne_zero L)
  obtain ⟨x₀, hx₀⟩ := Infinite.exists_notMem_finset B.roots.toFinset
  have hBx : B.eval x₀ ≠ 0 := fun h ↦ hx₀ (Multiset.mem_toFinset.2 ((mem_roots hB).2 h))
  simp only [B, eval_mul, mul_ne_zero_iff] at hBx
  obtain ⟨⟨⟨hrd, hsd⟩, hsnx⟩, hcub⟩ := hBx
  obtain ⟨z₀, hz₀, hxz₀⟩ := L.exists_weierstrassP_eq x₀
  -- the rational functions and the image coordinates
  set R : ℂ → ℂ := fun t ↦ r.num.eval t / r.denom.eval t
  set S : ℂ → ℂ := fun t ↦ s.num.eval t / s.denom.eval t
  have hformula : ∀ z, z ∉ L.lattice → r.denom.eval (℘[L] z) ≠ 0 → s.denom.eval (℘[L] z) ≠ 0 →
      ∃ h' : L.weierstrassCurve.toAffine.Nonsingular (R (℘[L] z)) (℘'[L] z / 2 * S (℘[L] z)),
        (Hom.ofIsogeny φ).pointMap (L.weierstrassPoint z) = .some _ _ h' := by
    intro z hz hr' hs'
    rw [L.weierstrassPoint_of_notMem hz]
    exact pointMap_ofIsogeny_some_eq φ hs _ hr' hs'
  obtain ⟨h₀, himg⟩ := hformula z₀ hz₀ (by rwa [hxz₀]) (by rwa [hxz₀])
  have hy₀ : ℘'[L] z₀ / 2 ≠ 0 := by
    intro h
    have := sq_eq_cubicPoly L (L.equation_weierstrassP hz₀)
    rw [h, hxz₀] at this
    exact hcub (by simpa using this.symm)
  have hd₀ : ℘'[L] z₀ / 2 * S (℘[L] z₀) ≠ 0 :=
    mul_ne_zero hy₀ (div_ne_zero (by rwa [hxz₀]) (by rwa [hxz₀]))
  obtain ⟨u₀, hu₀⟩ := L.weierstrassPoint_surjective (.some _ _ h₀)
  have hu₀L : u₀ ∉ L.lattice := fun h ↦ by
    rw [L.weierstrassPoint_of_mem h] at hu₀
    exact Point.some_ne_zero _ hu₀.symm
  rw [L.weierstrassPoint_of_notMem hu₀L, Point.some.injEq] at hu₀
  obtain ⟨hpu, hdu⟩ := hu₀
  have hder0 : ℘'[L] u₀ ≠ 0 := fun h ↦ hd₀ (by rw [← hdu, h, zero_div])
  -- the local inverse of `℘` at `u₀`
  have hstrict : HasStrictDerivAt ℘[L] (℘'[L] u₀) u₀ := by
    have := (L.analyticOnNhd_weierstrassP u₀ hu₀L).hasStrictDerivAt
    rwa [L.deriv_weierstrassP] at this
  obtain ⟨g, hg_def⟩ : ∃ g, g = hstrict.localInverse _ _ _ hder0 := ⟨_, rfl⟩
  have hgl : ∀ᶠ u in 𝓝 u₀, g (℘[L] u) = u := hg_def ▸ hstrict.eventually_left_inverse hder0
  have hgr : ∀ᶠ v in 𝓝 (℘[L] u₀), ℘[L] (g v) = v := hg_def ▸ hstrict.eventually_right_inverse hder0
  have hgd : DifferentiableAt ℂ g (℘[L] u₀) :=
    hg_def ▸ (hstrict.to_localInverse hder0).hasDerivAt.differentiableAt
  obtain ⟨Rz, hRz_def⟩ : ∃ Rz : ℂ → ℂ, Rz = fun z ↦ R (℘[L] z) := ⟨_, rfl⟩
  have hwpz : DifferentiableAt ℂ ℘[L] z₀ :=
    (L.analyticOnNhd_weierstrassP z₀ hz₀).differentiableAt
  have hRz : DifferentiableAt ℂ Rz z₀ := by
    rw [hRz_def]
    exact ((r.num.differentiable _).comp z₀ hwpz).div ((r.denom.differentiable _).comp z₀ hwpz)
      (by simpa [hxz₀] using hrd)
  have hRz₀ : Rz z₀ = ℘[L] u₀ := by rw [hRz_def]; exact hpu.symm
  have hg : DifferentiableAt ℂ g (Rz z₀) := by rw [hRz₀]; exact hgd
  obtain ⟨ψ, hψ_def⟩ : ∃ ψ : ℂ → ℂ, ψ = fun z ↦ g (Rz z) := ⟨_, rfl⟩
  have hψ : DifferentiableAt ℂ ψ z₀ := by rw [hψ_def]; exact hg.comp z₀ hRz
  have hψ₀ : ψ z₀ = u₀ := by
    rw [hψ_def]; simp only [hRz₀]
    exact hgl.self_of_nhds
  refine ⟨z₀, deriv ψ z₀, ψ, hψ.hasDerivAt, ?_⟩
  -- the eventual conditions near `z₀`
  have e1 : ∀ᶠ z in 𝓝 z₀, z ∉ L.lattice := L.isClosed_lattice.isOpen_compl.mem_nhds hz₀
  have e2 : ∀ᶠ z in 𝓝 z₀, r.denom.eval (℘[L] z) ≠ 0 :=
    ((r.denom.continuous.continuousAt).comp hwpz.continuousAt).eventually_ne (by simpa [hxz₀] using hrd)
  have e3 : ∀ᶠ z in 𝓝 z₀, s.denom.eval (℘[L] z) ≠ 0 :=
    ((s.denom.continuous.continuousAt).comp hwpz.continuousAt).eventually_ne (by simpa [hxz₀] using hsd)
  have e4 : ∀ᶠ z in 𝓝 z₀, ℘[L] (ψ z) = Rz z := by
    have h := hgr
    rw [← hRz₀] at h
    filter_upwards [hRz.continuousAt.eventually h] with z hz
    rw [hψ_def]; exact hz
  have hψc : ContinuousAt ψ z₀ := hψ.continuousAt
  have e5 : ∀ᶠ z in 𝓝 z₀, ψ z ∉ L.lattice := by
    have : ∀ᶠ u in 𝓝 (ψ z₀), u ∉ L.lattice := by
      rw [hψ₀]; exact L.isClosed_lattice.isOpen_compl.mem_nhds hu₀L
    exact hψc.eventually this
  have hdc : ContinuousAt (fun z ↦ ℘'[L] (ψ z) / 2 + ℘'[L] z / 2 * S (℘[L] z)) z₀ := by
    have h1 : ContinuousAt ℘'[L] (ψ z₀) := by
      rw [hψ₀]; exact (L.analyticOnNhd_derivWeierstrassP u₀ hu₀L).continuousAt
    have h2 : ContinuousAt ℘'[L] z₀ := (L.analyticOnNhd_derivWeierstrassP z₀ hz₀).continuousAt
    have h3 : ContinuousAt (fun z ↦ S (℘[L] z)) z₀ :=
      ((s.num.continuous.continuousAt).comp hwpz.continuousAt).div
        ((s.denom.continuous.continuousAt).comp hwpz.continuousAt) (by simpa [hxz₀] using hsd)
    exact ((h1.comp hψc).div_const 2).add ((h2.div_const 2).mul h3)
  have e6 : ∀ᶠ z in 𝓝 z₀, ℘'[L] (ψ z) / 2 + ℘'[L] z / 2 * S (℘[L] z) ≠ 0 := by
    refine hdc.eventually_ne ?_
    simp only [hψ₀, hdu]
    rw [← two_mul]
    exact mul_ne_zero two_ne_zero hd₀
  filter_upwards [e1, e2, e3, e4, e5, e6] with z hz1 hz2 hz3 hz4 hz5 hz6
  rw [hRz_def] at hz4
  obtain ⟨h', hP⟩ := hformula z hz1 hz2 hz3
  rw [hP, L.weierstrassPoint_of_notMem hz5]
  have hsq : (℘'[L] (ψ z) / 2) ^ 2 = (℘'[L] z / 2 * S (℘[L] z)) ^ 2 := by
    rw [sq_eq_cubicPoly L (L.equation_weierstrassP hz5), sq_eq_cubicPoly L h'.left, hz4]
  have hy : ℘'[L] (ψ z) / 2 = ℘'[L] z / 2 * S (℘[L] z) := by
    have : (℘'[L] (ψ z) / 2 - ℘'[L] z / 2 * S (℘[L] z)) *
        (℘'[L] (ψ z) / 2 + ℘'[L] z / 2 * S (℘[L] z)) = 0 := by linear_combination hsq
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hz6)
  exact point_some_eq_some _ _ hz4 hy

/-- **`EndomorphismLiftStatement`** (Milne, Proposition 3.3 with Proposition 3.12; Silverman VI.4.1): every
endomorphism of `E(Λ)` is induced by multiplication by a complex number. -/
@[kb "milne2017mf" "Proposition 3.3, pdf p. 42: endomorphisms of E(Lambda) are z -> alpha z"]
theorem endomorphismLiftStatement : EndomorphismLiftStatement := by
  refine ⟨fun L f ↦ ?_⟩
  rcases eq_or_ne f 0 with rfl | hf
  · exact ⟨0, fun z ↦ by simp⟩
  obtain ⟨z₀, α, ψ, hψ, hloc⟩ := exists_local_lift L f hf
  exact ⟨α, pointMap_eq_weierstrassPoint_mul_of_local L f hψ hloc⟩

/-- **Milne, Corollary 12.15** (unconditional): an elliptic curve over a number field with complex multiplication by
an order over that field has integral `j`-invariant. -/
@[kb "milne2017mf" "Corollary 12.15, pdf p. 125"]
theorem cmJIntegral : CMJIntegral := cmJIntegral_of_endomorphismLift endomorphismLiftStatement

/-- **Milne, Theorem 12.14** (unconditional): an elliptic curve over a number field with complex multiplication by an
order over that field has potential good reduction at every prime. -/
@[kb "milne2017mf" "Theorem 12.14, pdf p. 125"]
theorem cmPotentialGoodReduction : CMPotentialGoodReduction :=
  cmPotentialGoodReduction_of_endomorphismLift endomorphismLiftStatement

end ModularFormsKB.Milne.Wave5
