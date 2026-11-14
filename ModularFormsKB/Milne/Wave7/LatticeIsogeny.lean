import ModularFormsKB.Milne.Wave5.MultiplicationIsogeny

/-!
# Milne wave 7: multiplication by `α` with `αΛ ⊆ Λ'` is a morphism `E(Λ) → E(Λ')`

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Proposition 3.3 with Propositions 3.11
and 3.12 (pdf pp. 42–47); Silverman, *The Arithmetic of Elliptic Curves*, VI.4.1. Wave 5 proved this for `Λ' = Λ`
(`Wave5.multiplicationIsogenyStatement`); this file proves it for two lattices by the same construction: `℘_{Λ'}(αz)`
and `℘'_{Λ'}(αz)/2` are elliptic functions for `Λ`, hence rational in `℘_Λ(z)`, `℘'_Λ(z)/2`, and their classes give a
pullback `ℂ[E(Λ')] → ℂ(E(Λ))`; it maps infinity to infinity because `℘_{Λ'}(αz)` has a pole at `0`.
-/

open Complex PeriodPair TauCeti TauCeti.Isogeny Polynomial Filter Topology WeierstrassCurve.Affine Bornology
open ModularFormsKB.Milne.Wave5

open scoped RatFunc

namespace ModularFormsKB.Milne.Wave7

variable {L L' : PeriodPair} {α : ℂ}

/-- `℘_{Λ'}(αz)` is an elliptic function for `Λ` when `αΛ ⊆ Λ'`. -/
theorem isDoublyPeriodic_weierstrassP_mul' (hα : ∀ x ∈ L.lattice, α * x ∈ L'.lattice) :
    IsDoublyPeriodic L.lattice (fun z ↦ ℘[L'] (α * z)) := by
  refine ⟨fun z _ ↦ (L'.meromorphic_weierstrassP (α * z)).comp_analyticAt (by fun_prop), fun ω hω z ↦ ?_⟩
  show ℘[L'] (α * (z + ω)) = ℘[L'] (α * z)
  rw [mul_add]
  exact L'.weierstrassP_add_coe (α * z) ⟨α * ω, hα ω hω⟩

/-- `℘'_{Λ'}(αz)/2` is an elliptic function for `Λ` when `αΛ ⊆ Λ'`. -/
theorem isDoublyPeriodic_derivWeierstrassP_mul' (hα : ∀ x ∈ L.lattice, α * x ∈ L'.lattice) :
    IsDoublyPeriodic L.lattice (fun z ↦ ℘'[L'] (α * z) / 2) := by
  refine ⟨fun z _ ↦ ((L'.meromorphic_derivWeierstrassP (α * z)).comp_analyticAt (by fun_prop)).div
    (MeromorphicAt.const 2 z), fun ω hω z ↦ ?_⟩
  show ℘'[L'] (α * (z + ω)) / 2 = ℘'[L'] (α * z) / 2
  rw [mul_add]
  rw [L'.derivWeierstrassP_add_coe (α * z) ⟨α * ω, hα ω hω⟩]

/-- **Multiplication by `α ≠ 0` with `αΛ ⊆ Λ'` is a morphism `E(Λ) → E(Λ')`.** -/
theorem exists_hom_weierstrassPoint_mul' (hα0 : α ≠ 0) (hα : ∀ x ∈ L.lattice, α * x ∈ L'.lattice) :
    ∃ f : Hom L.weierstrassCurve.toAffine L'.weierstrassCurve.toAffine,
      ∀ z, f.pointMap (L.weierstrassPoint z) = L'.weierstrassPoint (α * z) := by
  classical
  set W := L.weierstrassCurve.toAffine
  set V := L'.weierstrassCurve.toAffine
  set K := W.FunctionField
  obtain ⟨A₁, B₁, hB₁, h₁⟩ := exists_evWP_ratio (isDoublyPeriodic_weierstrassP_mul' hα)
  obtain ⟨A₂, B₂, hB₂, h₂⟩ := exists_evWP_ratio (isDoublyPeriodic_derivWeierstrassP_mul' hα)
  have hL := eventually_notMem_lattice_codiscrete L
  have hLα : ∀ᶠ z in codiscrete ℂ, α * z ∉ L'.lattice := by
    simpa using eventually_codiscrete_comp_affine (eventually_notMem_lattice_codiscrete L') hα0 0
  have hmk_ne : ∀ B : ℂ[X][X], (∀ᶠ z in codiscrete ℂ, evWP L B z ≠ 0) → CoordinateRing.mk W B ≠ 0 := by
    intro B hB h0
    obtain ⟨z, hz, hzL⟩ := (hB.and hL).exists
    apply hz
    rw [evWP_eq_of_mk_eq L (B := 0) (by rw [h0, map_zero]) hzL]
    simp [evWP]
  set ι := algebraMap W.CoordinateRing K
  have hι : Function.Injective ι := FaithfulSMul.algebraMap_injective _ _
  have hιne : ∀ B : ℂ[X][X], (∀ᶠ z in codiscrete ℂ, evWP L B z ≠ 0) → ι (CoordinateRing.mk W B) ≠ 0 :=
    fun B hB ↦ (map_ne_zero_iff _ hι).2 (hmk_ne B hB)
  set xA := ι (CoordinateRing.mk W A₁)
  set xB := ι (CoordinateRing.mk W B₁)
  set yA := ι (CoordinateRing.mk W A₂)
  set yB := ι (CoordinateRing.mk W B₂)
  have hxB : xB ≠ 0 := hιne B₁ hB₁
  have hyB : yB ≠ 0 := hιne B₂ hB₂
  set X' := xA / xB
  set Y' := yA / yB
  -- the Weierstrass equation of `E(Λ')` for `(X', Y')`
  have hD : CoordinateRing.mk W (A₂ ^ 2 * B₁ ^ 3 - (A₁ ^ 3 + C (C (-(L'.g₂ / 4))) * A₁ * B₁ ^ 2 +
      C (C (-(L'.g₃ / 4))) * B₁ ^ 3) * B₂ ^ 2) = 0 := by
    apply mk_eq_zero_of_eventually
    filter_upwards [h₁, h₂, hLα] with z hz1 hz2 hz3
    have hsq := sq_eq_cubicPoly L' (L'.equation_weierstrassP hz3)
    simp only [cubicPoly, eval_sub, eval_pow, eval_X, eval_mul, eval_C] at hsq
    simp only [evWP_sub, evWP_mul, evWP_add, evWP_pow, evWP_C, eval_C]
    rw [← hz1, ← hz2]
    linear_combination (evWP L B₁ z) ^ 3 * (evWP L B₂ z) ^ 2 * hsq
  have hkey : yA ^ 2 * xB ^ 3 = (xA ^ 3 + algebraMap ℂ K (-(L'.g₂ / 4)) * xA * xB ^ 2 +
      algebraMap ℂ K (-(L'.g₃ / 4)) * xB ^ 3) * yB ^ 2 := by
    have := congrArg ι hD
    simp only [map_sub, map_mul, map_pow, map_add, map_zero] at this
    exact sub_eq_zero.1 this
  have heq : (V⁄K).toAffine.Equation X' Y' := by
    rw [equation_iff]
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, V, weierstrassCurve_a₁,
      weierstrassCurve_a₂, weierstrassCurve_a₃, weierstrassCurve_a₄, weierstrassCurve_a₆, map_zero,
      zero_mul, add_zero]
    simp only [X', Y']
    field_simp
    linear_combination hkey
  set p : CoordinatePullback W V := CoordinateRing.evalAlgHom heq
  have hpX : p (AdjoinRoot.of V.polynomial X) = X' := CoordinateRing.evalAlgHom_of_X heq
  have hpY : p (AdjoinRoot.root V.polynomial) = Y' := CoordinateRing.evalAlgHom_root heq
  -- `X'` is fixed by negation, hence a rational function `r(x)`
  set σ := (negIsogeny W).fieldPullback
  have hσB : ι (CoordinateRing.mk W (B₁.comp (-X))) ≠ 0 := by
    rw [← fieldPullback_negIsogeny_mk]
    exact (map_ne_zero_iff _ σ.toRingHom.injective).2 hxB
  have hσX : σ X' = X' := by
    simp only [X', xA, xB]
    rw [map_div₀, fieldPullback_negIsogeny_mk, fieldPullback_negIsogeny_mk, div_eq_div_iff hσB hxB,
      ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    rw [← sub_eq_zero, ← map_sub]
    apply mk_eq_zero_of_eventually
    have hneg := eventually_codiscrete_comp_affine h₁ (neg_ne_zero.2 one_ne_zero) 0
    filter_upwards [h₁, hneg] with z hz hz'
    simp only [neg_mul, one_mul, add_zero, mul_neg, weierstrassP_neg] at hz'
    simp only [evWP_sub, evWP_mul, evWP_comp_neg]
    rw [← hz, ← hz']
    ring
  obtain ⟨r, hr⟩ := (mem_ratFuncRange W).1 ((fieldPullback_negIsogeny_eq_self_iff W).1 hσX)
  rw [IsScalarTower.toAlgHom_apply] at hr
  have hmkr : CoordinateRing.mk W (A₁ * C r.denom) = CoordinateRing.mk W (B₁ * C r.num) := by
    apply hι
    have h' : algebraMap (RatFunc ℂ) K r = aeval (genericX W) r.num / aeval (genericX W) r.denom := by
      nth_rewrite 1 [← RatFunc.num_div_denom r]
      rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        algebraMap_eq_aeval_genericX, algebraMap_eq_aeval_genericX]
    have hden : aeval (genericX W) r.denom ≠ 0 := by
      rw [← algebraMap_eq_aeval_genericX]
      exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℂ[X] K)).2 r.denom_ne_zero
    rw [hr] at h'
    have hC : ∀ a, ι (CoordinateRing.mk W (C a)) = aeval (genericX W) a := fun a ↦ algebraMap_mk_C a
    simp only [map_mul, hC]
    rw [div_eq_div_iff hxB hden] at h'
    linear_combination h'
  have hrel : ∀ᶠ z in codiscrete ℂ, ℘[L'] (α * z) * r.denom.eval (℘[L] z) = r.num.eval (℘[L] z) := by
    filter_upwards [h₁, hB₁, hL] with z hz hzB hzL
    have := evWP_eq_of_mk_eq L hmkr hzL
    simp only [evWP_mul, evWP_C, ← hz] at this
    apply mul_left_cancel₀ hzB
    linear_combination this
  have hdenne : ∀ᶠ z in codiscrete ℂ, r.denom.eval (℘[L] z) ≠ 0 := by
    filter_upwards [hrel] with z hz h0
    rw [h0, mul_zero] at hz
    obtain ⟨a, b, hab⟩ := RatFunc.isCoprime_num_denom r
    have := congrArg (eval (℘[L] z)) hab
    simp only [eval_add, eval_mul, eval_one, h0, ← hz, mul_zero, add_zero] at this
    exact zero_ne_one this
  -- `r` has positive degree: `℘_{Λ'}(αz)` has a pole at `0`
  have hcob : Tendsto ℘[L] (𝓝[≠] 0) (cobounded ℂ) :=
    tendsto_cobounded_of_meromorphicOrderAt_neg (by rw [L.order_weierstrassP 0 (zero_mem _)]; decide)
  have hcob' : Tendsto ℘[L'] (𝓝[≠] 0) (cobounded ℂ) :=
    tendsto_cobounded_of_meromorphicOrderAt_neg (by rw [L'.order_weierstrassP 0 (zero_mem _)]; decide)
  have hcobα : Tendsto (fun z ↦ ℘[L'] (α * z)) (𝓝[≠] 0) (cobounded ℂ) := by
    refine hcob'.comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous fun z : ℂ ↦ α * z := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz using mul_ne_zero hα0 hz
  have hdeg : r.denom.natDegree < r.num.natDegree := by
    by_contra hle
    push Not at hle
    set n := r.denom.natDegree
    have hlead : r.denom.coeff n ≠ 0 := by
      rw [← leadingCoeff]; exact leadingCoeff_ne_zero.2 r.denom_ne_zero
    have hnum := (tendsto_eval_div_pow hle).comp hcob
    have hden := (tendsto_eval_div_pow (le_refl n)).comp hcob
    have hlim : Tendsto (fun z ↦ ℘[L'] (α * z)) (𝓝[≠] 0) (𝓝 (r.num.coeff n / r.denom.coeff n)) := by
      refine (hnum.div hden hlead).congr' ?_
      filter_upwards [nhdsNE_le_codiscrete 0 hrel, nhdsNE_le_codiscrete 0 hdenne,
        hcob.eventually (eventually_ne_cobounded 0)] with z h1 h2 h3
      simp only [Pi.div_apply, Function.comp_apply]
      rw [div_div_div_cancel_right₀ (pow_ne_zero _ h3), div_eq_iff h2]
      exact h1.symm
    exact hlim.not_tendsto (Metric.disjoint_nhds_cobounded _) hcobα
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hpole : 1 < infinityPlace W X' := by
    rw [← hr, infinityPlace_algebraMap_ratFunc _ hr0, ← WithZero.exp_zero, WithZero.exp_lt_exp,
      RatFunc.intDegree]
    omega
  have hmaps : p.MapsInfinity :=
    CoordinatePullback.mapsInfinity_of_one_lt_infinityPlace p (AdjoinRoot.of V.polynomial X)
      (by rw [hpX]; exact hpole)
  let φ : Isogeny W V := ⟨p, hmaps⟩
  have hφX : φ.fieldPullback (genericX V) = X' := by
    rw [genericX_def, fieldPullback_algebraMap, CoordinateRing.mk, AdjoinRoot.mk_C]
    exact hpX
  have hφY : φ.fieldPullback (genericY V) = Y' := by
    rw [genericY_def, fieldPullback_algebraMap, CoordinateRing.mk, AdjoinRoot.mk_X]
    exact hpY
  have hxr : φ.xRatFunc = r := (eq_xRatFunc_iff.2 (hr.trans hφX.symm)).symm
  have hgood : ∀ᶠ z in codiscrete ℂ,
      (Hom.ofIsogeny φ).pointMap (L.weierstrassPoint z) = L'.weierstrassPoint (α * z) := by
    filter_upwards [hL, hLα, h₂, hB₂, hrel, hdenne] with z hzL hzα hz2 hzB2 hzr hzd
    rw [L.weierstrassPoint_of_notMem hzL, L'.weierstrassPoint_of_notMem hzα]
    have hd' : φ.xRatFunc.denom.eval (℘[L] z) ≠ 0 := by rwa [hxr]
    have hne := (pointMap_ofIsogeny_some_eq_zero_iff (φ := φ) (L.nonsingular_weierstrassP hzL)).not.mpr hd'
    have hxc := xCoord_pointMap_ofIsogeny_some (φ := φ) (L.nonsingular_weierstrassP hzL) hd'
    have hyc := yCoord_pointMap_ofIsogeny_some φ (L.nonsingular_weierstrassP hzL) (p := A₂) (q := B₂)
      hzB2 hφY hne
    generalize (Hom.ofIsogeny φ).pointMap _ = Q at hne hxc hyc ⊢
    rcases Q with _ | ⟨c, d, hc⟩
    · exact absurd rfl hne
    rw [Point.xCoord_some, hxr] at hxc
    rw [Point.yCoord_some] at hyc
    refine point_some_eq_some _ _ ?_ ?_
    · rw [hxc, div_eq_iff hzd]; exact hzr.symm
    · rw [hyc, div_eq_iff (show evalEval _ _ B₂ ≠ 0 from hzB2)]; exact hz2.symm
  refine ⟨Hom.ofIsogeny φ, fun z ↦ ?_⟩
  obtain ⟨w, hw1, hw2⟩ :=
    (hgood.and (eventually_codiscrete_comp_affine hgood (neg_ne_zero.2 one_ne_zero) z)).exists
  have hz : z = w + (-1 * w + z) := by ring
  rw [hz, weierstrassPoint_add, Hom.pointMap_add, hw1, hw2, ← weierstrassPoint_add]
  congr 1
  ring

variable (L L')

/-- **Multiplication by `α` with `αΛ ⊆ Λ'` is a morphism `E(Λ) → E(Λ')`** acting on points by `[z] ↦ [αz]`. -/
@[kb "milne2017mf" "Proposition 3.3, pdf p. 42: z -> alpha z with alpha Lambda in Lambda' is a morphism"]
theorem exists_hom_of_mul_mem (α : ℂ) (hα : ∀ x ∈ L.lattice, α * x ∈ L'.lattice) :
    ∃ f : Hom L.weierstrassCurve.toAffine L'.weierstrassCurve.toAffine,
      ∀ z, f.pointMap (L.weierstrassPoint z) = L'.weierstrassPoint (α * z) := by
  rcases eq_or_ne α 0 with rfl | hα0
  · exact ⟨0, fun z ↦ by simp⟩
  exact exists_hom_weierstrassPoint_mul' hα0 hα

end ModularFormsKB.Milne.Wave7
