import ModularFormsKB.Milne.Wave13.PoleSeries
import ModularFormsKB.Milne.Wave10.LittlePicard

/-!
# Riemann–Roch on `X(Γ)` for every subgroup `Γ` of finite index in `SL₂(ℤ)`

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Theorem 1.20 (pdf p. 21), Corollary 1.21 (p. 21),
Theorem 1.27 (p. 22), Theorem 2.22 (p. 37), Theorem 4.9 (p. 51), Proposition 4.12 (p. 53): Milne states them for every
subgroup of finite index; wave 12 proved them for congruence subgroups (separating a generic fibre of `j` by level-`N`
Eisenstein quotients). Here the separating functions are `S_u / E₆`, with `S_u` the Poincaré series with a pole at
`u` (`ModularFormsKB.Milne.Wave13.S`) and `E₆` the level-one Eisenstein series of weight `6`:

* at a generic point `τ` (`j(τ) ≠ 0, 1728`, not a branch value of `j`, `E₆(τ) ≠ 0`), for two points `[γτ] ≠ [γ'τ]` of
  `X(Γ)` the function `S_{γτ} / E₆` is a meromorphic function on `X(Γ)` with a pole at `[γτ]` and a finite value at
  `[γ'τ]` (`separates`);
* hence `riemannRoch_of_finiteIndex` (Wave 11's criterion `Wave11.riemannRoch_of_separated_fiber`) and the
  unconditional `dimensionFormula_of_finiteIndex`, `valenceFormula_of_finiteIndex`, `riemannHurwitz_of_finiteIndex`,
  `genus_of_finiteIndex`, `canonicalDegree_of_finiteIndex`.
-/

open UpperHalfPlane CongruenceSubgroup Matrix MulAction TauCeti.RiemannSurface
open ModularFormsKB.Milne.RiemannSurface MeromorphicFunction Subgroup.CompactifiedQuotient
open TauCeti.ModularForm TauCeti.ModularGroup Filter Topology EisensteinSeries ModularForm
open scoped MatrixGroups Manifold Pointwise

noncomputable section

namespace ModularFormsKB.Milne.Wave13

/-! ### The level-one Eisenstein series `E₆` -/

/-- `E₆`, Mathlib's Eisenstein series of level `1` and weight `6 = 2 · 3`. -/
abbrev E6 : ℍ → ℂ := eisensteinSeries (N := 1) ![0, 1] (2 * ((3 : ℕ) : ℤ))

/-- `E₆` as a modular form of level one. -/
def E6MF : ModularForm ((Gamma 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) (2 * ((3 : ℕ) : ℤ)) :=
  eisensteinSeriesMF (by norm_num) ![0, 1]

theorem coe_E6MF : (E6MF : ℍ → ℂ) = E6 := rfl

theorem mem_Gamma_one (γ : SL(2, ℤ)) : γ ∈ Gamma 1 := by rw [Gamma_one_top]; exact Subgroup.mem_top _

theorem E6_slash (γ : SL(2, ℤ)) : E6 ∣[2 * ((3 : ℕ) : ℤ)] γ = E6 :=
  UncondDim.slash_eq_of_mem E6MF (mem_Gamma_one γ)

/-- `E₆` is a (meromorphic) modular form of weight `6` for every finite-index `Γ`. -/
theorem isMeromorphicModularForm_E6 (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    IsMeromorphicModularForm Γ ((3 : ℕ) : ℤ) E6 := by
  refine ⟨fun γ _ ↦ E6_slash γ, fun z ↦ (UncondDim.analyticAt_of_mdifferentiable E6MF.holo' z).meromorphicAt,
    fun γ ↦ ?_⟩
  obtain ⟨n, hn, hw⟩ := UncondDiff.exists_nat_cuspWidth Γ γ
  have hpos : 0 < cuspWidth Γ γ := by rw [hw]; exact_mod_cast hn
  have hb : IsBoundedAtImInfty (E6 ∣[2 * ((3 : ℕ) : ℤ)] γ) := by
    rw [E6_slash]
    have := isBoundedAtImInfty_eisensteinSeriesSIF (N := 1) ![0, 1] (k := 2 * ((3 : ℕ) : ℤ)) (by norm_num) 1
    have h2 : E6 = ⇑(eisensteinSeriesSIF (N := 1) ![0, 1] (2 * ((3 : ℕ) : ℤ))) := rfl
    rw [h2]
    simpa using this
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E6 ∣[2 * ((3 : ℕ) : ℤ)] γ) := by
    rw [E6_slash]; exact E6MF.holo'
  exact (UpperHalfPlane.analyticAt_cuspFunction_zero hpos
    (UncondDim.periodic_slash (fun δ _ ↦ E6_slash δ) γ) hhol hb).meromorphicAt

theorem exists_ne_zero_E6 : ∃ z, E6 z ≠ 0 := by
  by_contra h
  push Not at h
  have ht := Wave12.tendsto_eisensteinSeries (N := 1) ![0, 1] (2 * ((3 : ℕ) : ℤ)) (by norm_num)
  simp only [h] at ht
  have h0 := tendsto_nhds_unique ht tendsto_const_nhds
  rw [Wave12.eisLim_eq_ofReal _ _ (by decide)] at h0
  have : Wave12.eisLimReal (N := 1) ![0, 1] = 0 := by exact_mod_cast h0
  linarith [Wave12.one_le_eisLimReal (N := 1)]

theorem E6_smul_ne_zero {τ : ℍ} (h : E6 τ ≠ 0) (δ : SL(2, ℤ)) : E6 (δ • τ) ≠ 0 := by
  have := congrFun (E6_slash δ) τ
  rw [SL_slash_apply] at this
  intro h0
  rw [h0, zero_mul] at this
  exact h this.symm

/-! ### Generic points -/

/-- At a point where `j ≠ 0, 1728`, the stabilizer in `SL₂(ℤ)` is the centre `{±1}`. -/
theorem mem_center_of_jRegular {u : ℍ} (hu : j u ∈ Wave10.jRegular) {ξ : SL(2, ℤ)} (h : ξ • u = u) :
    ξ ∈ Subgroup.center SL(2, ℤ) := by
  have hfree := (Wave10.mem_freeLocus_iff_j u).2 hu
  rw [TauCeti.mem_freeLocus] at hfree
  have hmem : (⟨sl2zToPSL2R ξ, ⟨(ξ : PSL(2, ℤ)), psl2zToPSL2R_mk ξ⟩⟩ : psl2zToPSL2R.range) ∈
      stabilizer psl2zToPSL2R.range u := by
    rw [mem_stabilizer_iff, Subgroup.smul_def]
    simp only
    rw [sl2zToPSL2R_smul_eq, h]
  rw [hfree, Subgroup.mem_bot] at hmem
  have h1 : sl2zToPSL2R ξ = 1 := congrArg Subtype.val hmem
  rw [← sl2zToPSL2R_ker]
  exact h1

/-! ### Separation -/

theorem tendsto_of_proj {Γ : Subgroup SL(2, ℤ)} {G : modularCurve Γ → ℂ} {F : ℍ → ℂ}
    (hG : ∀ z, F z = G (modularCurve.proj Γ z)) {τ : ℍ} {c : OnePoint ℂ}
    (h : Tendsto (fun z ↦ (F z : OnePoint ℂ)) (𝓝[≠] τ) (𝓝 c)) :
    Tendsto (fun x ↦ (G x : OnePoint ℂ)) (𝓝[≠] (modularCurve.proj Γ τ)) (𝓝 c) := by
  rw [Filter.tendsto_def]
  intro V hV
  obtain ⟨U, hU, hτU, hUV⟩ := mem_nhdsWithin.1 (Filter.tendsto_def.1 h V hV)
  have hopen : IsOpen (modularCurve.proj Γ '' U) := by
    have h1 : IsOpenMap (Quotient.mk (MulAction.orbitRel (Γ.map sl2zToPSL2R) ℍ)) :=
      isOpenMap_quotient_mk'_mul
    exact isOpenMap_ofQuotient.comp h1 U hU
  refine mem_nhdsWithin.2 ⟨_, hopen, ⟨τ, hτU, rfl⟩, ?_⟩
  rintro _ ⟨⟨z, hz, rfl⟩, hne⟩
  have hzτ : z ≠ τ := fun h' ↦ hne (by rw [h']; rfl)
  show (G (modularCurve.proj Γ z) : OnePoint ℂ) ∈ V
  rw [← hG z]
  exact hUV ⟨hz, hzτ⟩

theorem tendsto_infty_div {u : ℍ} {S g : ℍ → ℂ} (hS : Tendsto (fun z ↦ ‖S z‖) (𝓝[≠] u) atTop)
    (hg : ContinuousAt g u) (hgu : g u ≠ 0) :
    Tendsto (fun z ↦ ((S z / g z : ℂ) : OnePoint ℂ)) (𝓝[≠] u) (𝓝 OnePoint.infty) := by
  have hM : 0 < ‖g u‖ + 1 := by positivity
  have hev : ∀ᶠ z in 𝓝[≠] u, g z ≠ 0 ∧ ‖g z‖ ≤ ‖g u‖ + 1 := by
    have h1 := hg.eventually_ne hgu
    have h2 : ∀ᶠ z in 𝓝 u, ‖g z‖ < ‖g u‖ + 1 :=
      hg.norm.eventually (gt_mem_nhds (by linarith))
    exact ((h1.and h2).mono fun z hz ↦ ⟨hz.1, hz.2.le⟩).filter_mono nhdsWithin_le_nhds
  have hnorm : Tendsto (fun z ↦ ‖S z / g z‖) (𝓝[≠] u) atTop := by
    refine tendsto_atTop_mono' _ (hev.mono fun z hz ↦ ?_) (hS.atTop_div_const hM)
    show ‖S z‖ / (‖g u‖ + 1) ≤ ‖S z / g z‖
    rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (norm_pos_iff.2 hz.1) hz.2
  have hcob := tendsto_norm_atTop_iff_cobounded.1 hnorm
  rw [Metric.cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact] at hcob
  exact OnePoint.tendsto_coe_infty.comp hcob

/-- **The meromorphic functions on `X(Γ)` separate the points of a generic fibre of `j`**, for every finite-index
`Γ`: `S_{γτ} / E₆` has a pole at `[γτ]` and a finite value at `[γ'τ]`. -/
theorem separates {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {τ : ℍ} (hj : j τ ∈ Wave10.jRegular) (hE : E6 τ ≠ 0)
    {γ γ' : SL(2, ℤ)}
    (hne : (ofQuotient (Quotient.mk _ (γ • τ)) : ModularCurveX Γ) ≠ ofQuotient (Quotient.mk _ (γ' • τ))) :
    ∃ g : MeromorphicFunction (ModularCurveX Γ),
      g (ofQuotient (Quotient.mk _ (γ • τ))) ≠ g (ofQuotient (Quotient.mk _ (γ' • τ))) := by
  set u := γ • τ
  have hk : 3 ≤ 3 := le_rfl
  have hju : j u ∈ Wave10.jRegular := by rw [j_smul_SL2Z]; exact hj
  set F : ℍ → ℂ := fun z ↦ S Γ u 3 z / E6 z
  have hF : IsModularFunction Γ F :=
    Wave12.isModularFunction_div (isMeromorphicModularForm_S Γ u hk) (isMeromorphicModularForm_E6 Γ)
  obtain ⟨G, hGm, hG⟩ := UncondDiff.exists_descent hF
  refine ⟨ofMeromorphic hGm, ?_⟩
  have hE6c : ∀ z, ContinuousAt E6 z := fun z ↦ E6MF.holo'.continuous.continuousAt
  -- the other point is not in the orbit of `u`
  have horb : ∀ ξ : Γ, (ξ : SL(2, ℤ)) • (γ' • τ) ≠ u := by
    intro ξ h
    apply hne
    congr 1
    refine Quotient.sound ?_
    change γ • τ ∈ MulAction.orbit _ (γ' • τ)
    rw [MulAction.mem_orbit_iff]
    refine ⟨⟨sl2zToPSL2R ξ, Subgroup.mem_map_of_mem _ ξ.2⟩, ?_⟩
    rw [Subgroup.smul_def]
    simp only
    rw [sl2zToPSL2R_smul_eq]
    exact h
  -- value at `[γ'τ]`: finite
  have hval' : ofMeromorphic hGm (ofQuotient (Quotient.mk _ (γ' • τ))) = (F (γ' • τ) : OnePoint ℂ) := by
    have hc : ContinuousAt F (γ' • τ) :=
      (continuousAt_S Γ u hk horb).div (hE6c _) (E6_smul_ne_zero hE γ')
    show ofMeromorphic hGm (modularCurve.proj Γ (γ' • τ)) = _
    rw [ofMeromorphic_apply_of_continuousAt _ (Wave12.continuousAt_of_proj hG hc), hG]
  -- value at `[γτ]`: `∞`
  have hval : ofMeromorphic hGm (ofQuotient (Quotient.mk _ u)) = OnePoint.infty := by
    have ht := tendsto_infty_div (tendsto_norm_S Γ u hk fun ξ h ↦ mem_center_of_jRegular hju h)
      (hE6c u) (E6_smul_ne_zero hE γ)
    show sphereMap G (modularCurve.proj Γ u) = _
    exact sphereMap_eq_of_tendsto (tendsto_of_proj hG ht)
  rw [hval, hval']
  exact (OnePoint.coe_ne_infty _).symm

/-! ### Riemann–Roch and its consequences -/

/-- **Milne, Theorem 1.20 (Riemann–Roch) on `X(Γ)` for every subgroup `Γ` of finite index in `SL₂(ℤ)`.** -/
@[kb "milne2017mf" "Theorem 1.20 (Riemann-Roch), pdf p. 21, for X(Gamma), Gamma of finite index"]
theorem riemannRoch_of_finiteIndex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    RiemannRochStatement (ModularCurveX Γ) := by
  have hf := Wave10.isNonconstant_jMeromorphic Γ
  set F := toFiniteHolomorphicMap (Wave10.jMeromorphic Γ) hf
  set B : Set (OnePoint ℂ) := F.branchValues ∪ {((0 : ℂ) : OnePoint ℂ), ((1728 : ℂ) : OnePoint ℂ)}
  have hBf : B.Finite := F.finite_branchValues.union (by simp)
  obtain ⟨τ, -, hB, hG⟩ := Wave12.exists_generic' 1 ({()} : Finset Unit) (fun _ ↦ E6)
    (fun _ _ ↦ E6MF.holo') (fun _ _ ↦ exists_ne_zero_E6) hBf
  have hE : E6 τ ≠ 0 := hG () (Finset.mem_singleton_self _)
  have hj : j τ ∈ Wave10.jRegular := by
    refine ⟨fun h ↦ hB (Or.inr (by simp [h])), fun h ↦ hB (Or.inr (by simp [h]))⟩
  have hBτ : (j τ : OnePoint ℂ) ∉ F.branchValues := fun h ↦ hB (Or.inl h)
  refine Wave11.riemannRoch_of_separated_fiber hf hBτ ?_
  have hΓ' : barGamma Γ ≤ barGamma Γ := le_rfl
  have := Wave12.isFiniteRelIndex_barGamma hΓ'
  let π := TauCeti.Fuchsian.compactifiedQuotientFiniteHolomorphicMap hΓ'
  intro y hy y' hy' hyy
  refine Wave12.exists_ne_of_pairwise_separated π (Wave12.exists_ne_zero_apply_eq_zero_of_nonconstant hf) hyy ?_
  have hfib : ∀ x, π x = y ∨ π x = y' → ∃ γ : SL(2, ℤ), x = ofQuotient (Quotient.mk _ (γ • τ)) := by
    intro x hx
    refine Wave12.exists_eq_ofQuotient' hΓ' ?_
    have hy0 : modularCurveXJ Γ y = (j τ : OnePoint ℂ) := hy
    have hy0' : modularCurveXJ Γ y' = (j τ : OnePoint ℂ) := hy'
    rcases hx with h | h
    · rw [← hy0, ← h]; rfl
    · rw [← hy0', ← h]; rfl
  intro x hx x' hx' hxx'
  obtain ⟨γ, rfl⟩ := hfib x hx
  obtain ⟨γ', rfl⟩ := hfib x' hx'
  exact separates hj hE hxx'

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- **Milne, Theorem 4.9 (the dimension formula)** for every subgroup of finite index, unconditional. -/
@[kb "milne2017mf" "Section 4, Theorem 4.9 (pdf p. 51), for every subgroup of finite index"]
theorem dimensionFormula_of_finiteIndex : DimensionFormula Γ :=
  Wave10.dimensionFormula_of_riemannRoch' Γ (riemannRoch_of_finiteIndex Γ)

/-- **Milne, Proposition 4.12 (the valence formula)** for every subgroup of finite index, unconditional. -/
@[kb "milne2017mf" "Section 4, Proposition 4.12 (pdf p. 53), for every subgroup of finite index"]
theorem valenceFormula_of_finiteIndex : ValenceFormula Γ :=
  Wave10.valenceFormula_of_riemannRoch Γ (riemannRoch_of_finiteIndex Γ)

/-- **Milne, Theorem 1.27 (Riemann–Hurwitz) for maps `X(Γ) → ℙ¹`**, `Γ` of finite index, unconditional. -/
@[kb "milne2017mf" "Theorem 1.27 (Riemann-Hurwitz), pdf p. 22, for X(Gamma) -> P^1, Gamma of finite index"]
theorem riemannHurwitz_of_finiteIndex : RiemannHurwitzStatement (ModularCurveX Γ) (OnePoint ℂ) :=
  Wave10.riemannHurwitz_modularCurveX Γ (riemannRoch_of_finiteIndex Γ)

/-- **Milne, Corollary 1.21 (`deg K = 2g - 2`) on `X(Γ)`**, `Γ` of finite index, unconditional. -/
@[kb "milne2017mf" "Corollary 1.21, pdf p. 21, for X(Gamma), Gamma of finite index"]
theorem canonicalDegree_of_finiteIndex : CanonicalDegreeStatement (ModularCurveX Γ) :=
  Wave10.canonicalDegreeStatement_of_riemannRoch (riemannRoch_of_finiteIndex Γ)

/-- **Milne, Theorem 2.22 (the genus formula)** for every subgroup of finite index, unconditional: the analytic
genus of `X(Γ)` is `1 + m/12 - ν₂/4 - ν₃/3 - ν∞/2`. -/
@[kb "milne2017mf" "Theorem 2.22, pdf p. 37, for every subgroup of finite index"]
theorem genus_of_finiteIndex :
    (genus (ModularCurveX Γ) : ℚ) =
      1 + (genusIndex Γ : ℚ) / 12 - (nuTwo Γ : ℚ) / 4 - (nuThree Γ : ℚ) / 3 - (nuInfty Γ : ℚ) / 2 :=
  Wave10.genus_modularCurveX_of_riemannRoch Γ (riemannRoch_of_finiteIndex Γ)

end ModularFormsKB.Milne.Wave13
