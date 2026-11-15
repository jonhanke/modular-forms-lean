import ModularFormsKB.Milne.Wave12.PrimePower
import ModularFormsKB.Milne.Wave12.EisensteinLimit
import ModularFormsKB.Milne.Ch4.UncondDimension
import ModularFormsKB.Milne.Wave4A.GenusGammaN
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.MDifferentiable

/-!
# Riemann–Roch on `X(Γ)` for every congruence subgroup `Γ`

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Theorem 1.20 (pdf p. 21), Theorem 1.27 (p. 22),
Theorem 2.22 (p. 37), Theorem 4.9 (p. 51), Proposition 4.12 (p. 53).

The functions `j(Mδz)` separate the points of a generic fibre of `j` on `X(Γ_sc(N))`
(`ModularFormsKB.Milne.Wave12.scMer_separates`), but not on `X(N)` when `-1` and `1` are not the only square roots of
`1` modulo `N`: two points `[σγ'τ]`, `[γ'τ]` with `σ ≡ λ·1 (mod N)` have the same image in `X(Γ_sc(N))`. These are
separated by quotients of Eisenstein series of level `N` and weight `4`:

  `f_a = E_4^a / D`,  `D = ∑_b E_4^b` (the sum over all `b ∈ (ℤ/Nℤ)²`, invariant under all of `SL₂(ℤ)`).

`f_a` is a modular function for `Γ(N)` (`isModularFunction_ratio`), hence a meromorphic function on `X(N)`
(`ratioMer`), with `f_a(δz) = E_4^{aδ}(z) / D(z)` (`ratio_smul`). For `a = (0, 1)γ'⁻¹` the two points above take
the values `E_4^{(0,λ)}(τ)/D(τ)` and `E_4^{(0,1)}(τ)/D(τ)`, which differ at a generic `τ`: as `z → i∞`,
`E_4^{(0,λ)}(z) → 0` for `λ ≠ ±1` and `E_4^{(0,1)}(z) → c ≥ 1` (`ModularFormsKB.Milne.Wave12.tendsto_eisensteinSeries`).
So the meromorphic functions on `X(N)` separate a generic fibre of `j` (`separates_GammaN`), and separation descends
to every `X(Γ)`, `Γ ⊇ Γ(N)`:

* **`riemannRoch_of_Gamma_le`**: Theorem 1.20 on `X(Γ)` for every `Γ ⊇ Γ(N)`, `N ≥ 1`;
* `dimensionFormula_of_Gamma_le`, `valenceFormula_of_Gamma_le`, `genus_of_Gamma_le`, `riemannHurwitz_of_Gamma_le`:
  Theorem 4.9, Proposition 4.12, Theorem 2.22, Theorem 1.27 for these `Γ`;
* `genus_X_Gamma`: Example 2.23, the genus of `X(N)`.
-/

open UpperHalfPlane CongruenceSubgroup Matrix MulAction TauCeti.RiemannSurface
open ModularFormsKB.Milne.RiemannSurface MeromorphicFunction Subgroup.CompactifiedQuotient
open TauCeti.ModularForm Filter Topology EisensteinSeries ModularForm
open scoped MatrixGroups Manifold Pointwise

noncomputable section

namespace ModularFormsKB.Milne.Wave12

/-! ### Quotients of meromorphic modular forms of the same weight -/

section Quot

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f g : ℍ → ℂ}

theorem div_slash_apply (γ : SL(2, ℤ)) (z : ℍ) :
    ((fun w ↦ f w / g w) ∣[(2 * 0 : ℤ)] γ) z = (f ∣[2 * k] γ) z / (g ∣[2 * k] γ) z := by
  rw [SL_slash_apply, SL_slash_apply, SL_slash_apply]
  have h : denom γ z ^ (-(2 * k)) ≠ 0 := zpow_ne_zero _ (denom_ne_zero γ z)
  simp only [mul_zero, neg_zero, zpow_zero, mul_one]
  rw [mul_div_mul_right _ _ h]

/-- The quotient of two meromorphic modular forms of the same weight is a modular function. -/
theorem isModularFunction_div (hf : IsMeromorphicModularForm Γ k f) (hg : IsMeromorphicModularForm Γ k g) :
    IsModularFunction Γ (fun w ↦ f w / g w) := by
  refine ⟨fun γ hγ ↦ ?_, fun z ↦ ?_, fun γ ↦ ?_⟩
  · funext z
    rw [div_slash_apply (k := k), hf.slash γ hγ, hg.slash γ hγ]
  · exact (hf.meromorphic z).div (hg.meromorphic z)
  · refine ((hf.meromorphic_cusp γ).div (hg.meromorphic_cusp γ)).congr ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    simp only [Pi.div_apply, Function.Periodic.cuspFunction_eq_of_ne_zero _ _ hq, Function.comp_apply]
    rw [div_slash_apply (k := k)]

end Quot

/-! ### Values of descended functions -/

theorem continuousAt_of_proj {Γ : Subgroup SL(2, ℤ)} {G : modularCurve Γ → ℂ} {g : ℍ → ℂ}
    (hG : ∀ z, g z = G (modularCurve.proj Γ z)) {τ : ℍ} (hg : ContinuousAt g τ) :
    ContinuousAt G (modularCurve.proj Γ τ) := by
  rw [ContinuousAt, Filter.tendsto_def]
  intro V hV
  rw [← hG τ] at hV
  obtain ⟨U, hUV, hU, hτU⟩ := mem_nhds_iff.1 (hg.preimage_mem_nhds hV)
  have hopen : IsOpen (modularCurve.proj Γ '' U) := by
    have h1 : IsOpenMap (Quotient.mk (MulAction.orbitRel (Γ.map sl2zToPSL2R) ℍ)) :=
      isOpenMap_quotient_mk'_mul
    exact isOpenMap_ofQuotient.comp h1 U hU
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨τ, hτU, rfl⟩) ?_
  rintro _ ⟨w, hw, rfl⟩
  show G (modularCurve.proj Γ w) ∈ V
  rw [← hG w]
  exact hUV hw

/-! ### Eisenstein series of level `N` and weight `4` -/

variable (N : ℕ) [NeZero N]

/-- `E_4^a`, Mathlib's Eisenstein series of level `N`, weight `4 = 2 · 2`. -/
abbrev eis (a : Fin 2 → ZMod N) : ℍ → ℂ := eisensteinSeries a (2 * 2)

/-- `E_4^a` as a modular form for `Γ(N)`. -/
def eisMF (a : Fin 2 → ZMod N) :
    ModularForm ((Gamma N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) (2 * 2) :=
  eisensteinSeriesMF (by norm_num) a

theorem coe_eisMF (a : Fin 2 → ZMod N) : (eisMF N a : ℍ → ℂ) = eis N a := rfl

/-- `D = ∑_b E_4^b`. -/
def DMF : ModularForm ((Gamma N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) (2 * 2) :=
  ∑ b : Fin 2 → ZMod N, eisMF N b

/-- `D` as a function. -/
def D : ℍ → ℂ := DMF N

theorem D_apply (z : ℍ) : D N z = ∑ b : Fin 2 → ZMod N, eis N b z := by
  simp only [D, DMF]
  rw [show ((∑ b : Fin 2 → ZMod N, eisMF N b : ModularForm _ _) : ℍ → ℂ) =
      ∑ b : Fin 2 → ZMod N, (eisMF N b : ℍ → ℂ) from
    map_sum (FunLike.coeAddMonoidHom (ModularForm _ (2 * 2)) ℍ ℂ) _ _]
  simp only [Finset.sum_apply]
  rfl

theorem eis_smul (a : Fin 2 → ZMod N) (δ : SL(2, ℤ)) (z : ℍ) :
    eis N a (δ • z) = denom δ z ^ (2 * 2 : ℤ) *
      eis N (a ᵥ* (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) δ : Matrix (Fin 2) (Fin 2) (ZMod N))) z := by
  have h := congrFun (eisensteinSeries_slash_apply a (2 * 2) δ) z
  rw [SL_slash_apply] at h
  dsimp only [eis]
  rw [← h, mul_left_comm, ← zpow_add₀ (denom_ne_zero δ z)]
  simp

/-- Right multiplication by `δ` modulo `N` permutes `(ℤ/Nℤ)²`. -/
def vecMulEquiv (δ : SL(2, ℤ)) : (Fin 2 → ZMod N) ≃ (Fin 2 → ZMod N) where
  toFun b := b ᵥ* (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) δ : Matrix (Fin 2) (Fin 2) (ZMod N))
  invFun b := b ᵥ* (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) δ⁻¹ : Matrix (Fin 2) (Fin 2) (ZMod N))
  left_inv b := by
    simp only [vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, mul_inv_cancel, map_one,
      Matrix.SpecialLinearGroup.coe_one, vecMul_one]
  right_inv b := by
    simp only [vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, inv_mul_cancel, map_one,
      Matrix.SpecialLinearGroup.coe_one, vecMul_one]

theorem D_smul (δ : SL(2, ℤ)) (z : ℍ) : D N (δ • z) = denom δ z ^ (2 * 2 : ℤ) * D N z := by
  rw [D_apply, D_apply, Finset.mul_sum, Finset.sum_congr rfl (fun b _ ↦ eis_smul N b δ z)]
  exact Fintype.sum_equiv (vecMulEquiv N δ) _ (fun b ↦ denom δ z ^ (2 * 2 : ℤ) * eis N b z) (fun b ↦ rfl)

theorem isMeromorphicModularForm_eis (a : Fin 2 → ZMod N) : IsMeromorphicModularForm (Gamma N) 2 (eis N a) :=
  UncondDim.isMeromorphicModularForm (eisMF N a)

theorem isMeromorphicModularForm_D : IsMeromorphicModularForm (Gamma N) 2 (D N) :=
  UncondDim.isMeromorphicModularForm (DMF N)

theorem mdifferentiable_eis (a : Fin 2 → ZMod N) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (eis N a) :=
  (eisMF N a).holo'

theorem mdifferentiable_D : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (D N) := (DMF N).holo'

/-! ### The modular functions `E_4^a / D` on `X(N)` -/

/-- `f_a = E_4^a / D`. -/
def ratio (a : Fin 2 → ZMod N) (z : ℍ) : ℂ := eis N a z / D N z

theorem ratio_smul (a : Fin 2 → ZMod N) (δ : SL(2, ℤ)) {z : ℍ} :
    ratio N a (δ • z) =
      eis N (a ᵥ* (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) δ : Matrix (Fin 2) (Fin 2) (ZMod N))) z /
        D N z := by
  rw [ratio, eis_smul, D_smul, mul_div_mul_left _ _ (zpow_ne_zero _ (denom_ne_zero δ z))]

theorem isModularFunction_ratio (a : Fin 2 → ZMod N) : IsModularFunction (Gamma N) (ratio N a) :=
  isModularFunction_div (isMeromorphicModularForm_eis N a) (isMeromorphicModularForm_D N)

theorem exists_ratio_descent (a : Fin 2 → ZMod N) :
    ∃ G : modularCurve (Gamma N) → ℂ, (∀ x, TauCeti.RiemannSurface.MeromorphicAt G x) ∧
      ∀ z, ratio N a z = G (modularCurve.proj (Gamma N) z) :=
  UncondDiff.exists_descent (isModularFunction_ratio N a)

/-- **`E_4^a / D` as a meromorphic function on `X(N)`.** -/
def ratioMer (a : Fin 2 → ZMod N) : MeromorphicFunction (ModularCurveX (Gamma N)) :=
  ofMeromorphic (exists_ratio_descent N a).choose_spec.1

theorem ratioMer_apply (a : Fin 2 → ZMod N) {z : ℍ} (hz : D N z ≠ 0) :
    ratioMer N a (ofQuotient (Quotient.mk _ z)) = (ratio N a z : OnePoint ℂ) := by
  have hspec := (exists_ratio_descent N a).choose_spec.2
  have hc : ContinuousAt (ratio N a) z :=
    ((mdifferentiable_eis N a).continuous.continuousAt).div
      ((mdifferentiable_D N).continuous.continuousAt) hz
  show ofMeromorphic _ (modularCurve.proj (Gamma N) z) = _
  rw [ofMeromorphic_apply_of_continuousAt _ (continuousAt_of_proj hspec hc), hspec z]

/-! ### The generic point -/

theorem exists_ne_zero_D : ∃ z, D N z ≠ 0 := by
  by_contra h
  push Not at h
  have ht : Tendsto (fun t ↦ D N (ptI t)) atTop (𝓝 (∑ b : Fin 2 → ZMod N, eisLim b (2 * 2))) := by
    simp only [D_apply]
    exact tendsto_finsetSum _ fun b _ ↦ tendsto_eisensteinSeries b _ (by norm_num)
  simp only [h] at ht
  have h0 := tendsto_nhds_unique ht tendsto_const_nhds
  have hreal : (∑ b : Fin 2 → ZMod N, eisLim b (2 * 2)) = ((∑ b : Fin 2 → ZMod N, eisLimReal b : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun b _ ↦ eisLim_eq_ofReal b _ (by decide)
  rw [hreal] at h0
  have hpos : 1 ≤ ∑ b : Fin 2 → ZMod N, eisLimReal b :=
    le_trans (one_le_eisLimReal (N := N))
      (Finset.single_le_sum (fun b _ ↦ eisLimReal_nonneg b) (Finset.mem_univ _))
  have : (∑ b : Fin 2 → ZMod N, eisLimReal b) = 0 := by exact_mod_cast h0
  linarith

theorem exists_eis_ne {l : ZMod N} (h1 : l ≠ 1) (h2 : l ≠ -1) :
    ∃ z, eis N ![0, l] z - eis N ![0, 1] z ≠ 0 := by
  by_contra h
  push Not at h
  have ht := (tendsto_eisensteinSeries (N := N) ![0, l] (2 * 2) (by norm_num)).sub
    (tendsto_eisensteinSeries (N := N) ![0, 1] (2 * 2) (by norm_num))
  simp only [h] at ht
  have h0 := tendsto_nhds_unique ht tendsto_const_nhds
  rw [eisLim_eq_zero (N := N) ![0, l] _ ?_, eisLim_eq_ofReal _ _ (by decide), zero_sub, neg_eq_zero] at h0
  · have : eisLimReal (N := N) ![0, 1] = 0 := by exact_mod_cast h0
    linarith [one_le_eisLimReal (N := N)]
  · rintro s (rfl | rfl) heq
    · exact h1 (by simpa using congrFun heq 1)
    · exact h2 (by simpa using congrFun heq 1)

/-! ### Separation on `X(N)` -/

theorem isFiniteRelIndex_barGamma {Δ Γ : Subgroup SL(2, ℤ)} [Δ.FiniteIndex] [Γ.FiniteIndex]
    (hΓ : barGamma Δ ≤ barGamma Γ) : (barGamma Δ).IsFiniteRelIndex (barGamma Γ) := by
  have h1 : (barGamma Δ).relIndex psl2zToPSL2R.range ≠ 0 :=
    Subgroup.IsFiniteRelIndex.relIndex_ne_zero
  have h2 := Subgroup.relIndex_mul_relIndex (barGamma Δ) (barGamma Γ) psl2zToPSL2R.range hΓ
    Γ.map_sl2zToPSL2R_le_range_psl2zToPSL2R
  exact ⟨fun h ↦ h1 (by rw [← h2, h, zero_mul])⟩


theorem Gamma_map_le_GammaSc_map : barGamma (Gamma N) ≤ barGamma (GammaSc N) :=
  Subgroup.map_mono (Gamma_le_GammaSc N)

/-- **The meromorphic functions on `X(N)` separate the points of a generic fibre of `j`.** -/
theorem separates_GammaN {τ : ℍ}
    (hτ : ∀ c c' : LevelTwo.Cosets N, c ≠ c' → LevelTwo.cosetVal (pos N) c τ ≠ LevelTwo.cosetVal (pos N) c' τ)
    (hD : D N τ ≠ 0)
    (hE : ∀ l : ZMod N, l ≠ 1 → l ≠ -1 → eis N ![0, l] τ ≠ eis N ![0, 1] τ)
    {γ γ' : SL(2, ℤ)}
    (hne : (ofQuotient (Quotient.mk _ (γ • τ)) : ModularCurveX (Gamma N)) ≠ ofQuotient (Quotient.mk _ (γ' • τ))) :
    ∃ g : MeromorphicFunction (ModularCurveX (Gamma N)),
      g (ofQuotient (Quotient.mk _ (γ • τ))) ≠ g (ofQuotient (Quotient.mk _ (γ' • τ))) := by
  by_contra hall
  push Not at hall
  -- Step 1: the images in `X(Γ_sc(N))` agree.
  have := isFiniteRelIndex_barGamma (Gamma_map_le_GammaSc_map N)
  let ρ := TauCeti.Fuchsian.compactifiedQuotientFiniteHolomorphicMap (Gamma_map_le_GammaSc_map N)
  have himg : (ofQuotient (Quotient.mk _ (γ • τ)) : ModularCurveX (GammaSc N)) =
      ofQuotient (Quotient.mk _ (γ' • τ)) := by
    by_contra hne'
    obtain ⟨h, hh⟩ := scMer_separates N hτ hne'
    apply hh
    have := hall (comap ρ ρ.holomorphic ρ.nonconstant h)
    simpa [ρ] using this
  -- Step 2: `γτ = σγ'τ` with `σ ∈ Γ_sc(N)`.
  have hq := Quotient.exact (ofQuotient.inj himg)
  change γ • τ ∈ MulAction.orbit _ (γ' • τ) at hq
  obtain ⟨⟨_, ⟨σ, hσ, rfl⟩⟩, hσ'⟩ := MulAction.mem_orbit_iff.1 hq
  rw [Subgroup.smul_def] at hσ'
  simp only at hσ'
  rw [sl2zToPSL2R_smul_eq, ← mul_smul] at hσ'
  obtain ⟨r, hr2, hr⟩ := mem_GammaSc_iff.1 hσ
  -- Step 3: `σ ≡ ±1` would make the points equal.
  have hpt : (ofQuotient (Quotient.mk _ (γ • τ)) : ModularCurveX (Gamma N)) =
      ofQuotient (Quotient.mk _ ((σ * γ') • τ)) := by rw [hσ']
  by_cases hr1 : r = 1 ∨ r = -1
  · apply hne
    rw [hpt]
    congr 1
    refine Quotient.sound ?_
    change (σ * γ') • τ ∈ MulAction.orbit _ (γ' • τ)
    rw [MulAction.mem_orbit_iff]
    have hσN : σ ∈ Gamma N ∨ -σ ∈ Gamma N := by
      rw [Gamma_mem', Gamma_mem']
      rcases hr1 with rfl | rfl
      · left
        ext i k
        have := congrFun (congrFun hr i) k
        simpa [eq_comm] using this
      · right
        ext i k
        have := congrFun (congrFun hr i) k
        fin_cases i <;> fin_cases k <;> simp [Matrix.scalar_apply] at this ⊢ <;> first | linear_combination this | linear_combination -this
    rcases hσN with h | h
    · refine ⟨⟨sl2zToPSL2R σ, Subgroup.mem_map_of_mem _ h⟩, ?_⟩
      rw [Subgroup.smul_def]
      simp only
      rw [sl2zToPSL2R_smul_eq, ← mul_smul]
    · refine ⟨⟨sl2zToPSL2R (-σ), Subgroup.mem_map_of_mem _ h⟩, ?_⟩
      rw [Subgroup.smul_def]
      simp only
      rw [sl2zToPSL2R_neg, sl2zToPSL2R_smul_eq, ← mul_smul]
  -- Step 4: otherwise an Eisenstein quotient separates them.
  push Not at hr1
  set a : Fin 2 → ZMod N :=
    ![0, 1] ᵥ* (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ'⁻¹ : Matrix (Fin 2) (Fin 2) (ZMod N))
  have hDγ : ∀ δ : SL(2, ℤ), D N (δ • τ) ≠ 0 := fun δ ↦ by
    rw [D_smul]; exact mul_ne_zero (zpow_ne_zero _ (denom_ne_zero δ τ)) hD
  have h := hall (ratioMer N a)
  rw [hpt, ratioMer_apply N a (hDγ _), ratioMer_apply N a (hDγ _), ratio_smul, ratio_smul] at h
  have h' := OnePoint.coe_injective h
  have hmap : ∀ δ : SL(2, ℤ), ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) δ : SL(2, ZMod N)) :
      Matrix (Fin 2) (Fin 2) (ZMod N)) = (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) δ :
      Matrix (Fin 2) (Fin 2) (ZMod N)) := fun _ ↦ rfl
  have ha1 : a ᵥ* (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ' : Matrix (Fin 2) (Fin 2) (ZMod N)) =
      ![0, 1] := by
    simp only [a, vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, inv_mul_cancel, map_one,
      Matrix.SpecialLinearGroup.coe_one, vecMul_one]
  have haσ : a ᵥ* (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) (σ * γ') :
      Matrix (Fin 2) (Fin 2) (ZMod N)) = ![0, r] := by
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, ← hr, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    simp only [a, vecMul_vecMul]
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, ← Matrix.SpecialLinearGroup.coe_mul, ← map_mul,
      inv_mul_cancel, map_one, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_smul, vecMul_one]
    ext i
    fin_cases i <;> simp
  rw [ha1, haσ] at h'
  exact hE r hr1.1 hr1.2 (by rw [div_left_inj' hD] at h'; exact h')

/-! ### Riemann–Roch on `X(Γ)`, `Γ ⊇ Γ(N)` -/

/-- **Milne, Theorem 1.20 (Riemann–Roch) on `X(Γ)` for every `Γ ⊇ Γ(N)`**, `N ≥ 1`: for every congruence subgroup. -/
@[kb "milne2017mf" "Theorem 1.20 (Riemann-Roch), pdf p. 21, for X(Gamma), Gamma a congruence subgroup"]
theorem riemannRoch_of_Gamma_le {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hΓ : Gamma N ≤ Γ) :
    RiemannRochStatement (ModularCurveX Γ) := by
  have hf := Wave10.isNonconstant_jMeromorphic Γ
  set F := toFiniteHolomorphicMap (Wave10.jMeromorphic Γ) hf
  classical
  let S : Finset (Option (ZMod N)) :=
    Finset.univ.filter fun o ↦ o.elim True fun l ↦ l ≠ 1 ∧ l ≠ -1
  let G : Option (ZMod N) → ℍ → ℂ := fun o ↦ o.elim (D N) fun l z ↦ eis N ![0, l] z - eis N ![0, 1] z
  obtain ⟨τ, hτ, hB, hG⟩ := exists_generic' N S G
    (fun o _ ↦ by
      rcases o with _ | l
      · exact mdifferentiable_D N
      · exact (mdifferentiable_eis N _).sub (mdifferentiable_eis N _))
    (fun o ho ↦ by
      rcases o with _ | l
      · exact exists_ne_zero_D N
      · have hl : l ≠ 1 ∧ l ≠ -1 := by simpa [S] using ho
        exact exists_eis_ne N hl.1 hl.2)
    F.finite_branchValues
  have hD : D N τ ≠ 0 := hG none (by simp [S])
  have hE : ∀ l : ZMod N, l ≠ 1 → l ≠ -1 → eis N ![0, l] τ ≠ eis N ![0, 1] τ := fun l h1 h2 ↦
    sub_ne_zero.1 (hG (some l) (by simp [S, h1, h2]))
  refine Wave11.riemannRoch_of_separated_fiber hf hB ?_
  have hΓ' : barGamma (Gamma N) ≤ barGamma Γ := Subgroup.map_mono hΓ
  have := isFiniteRelIndex_barGamma hΓ'
  let π := TauCeti.Fuchsian.compactifiedQuotientFiniteHolomorphicMap hΓ'
  intro y hy y' hy' hyy
  refine exists_ne_of_pairwise_separated π (exists_ne_zero_apply_eq_zero_of_nonconstant hf) hyy ?_
  have hfib : ∀ x, π x = y ∨ π x = y' → ∃ γ : SL(2, ℤ), x = ofQuotient (Quotient.mk _ (γ • τ)) := by
    intro x hx
    refine exists_eq_ofQuotient' hΓ' ?_
    have hy0 : modularCurveXJ Γ y = (j τ : OnePoint ℂ) := hy
    have hy0' : modularCurveXJ Γ y' = (j τ : OnePoint ℂ) := hy'
    rcases hx with h | h
    · rw [← hy0, ← h]; rfl
    · rw [← hy0', ← h]; rfl
  intro x hx x' hx' hxx'
  obtain ⟨γ, rfl⟩ := hfib x hx
  obtain ⟨γ', rfl⟩ := hfib x' hx'
  exact separates_GammaN N hτ hD hE hxx'

variable {N} {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hΓ : Gamma N ≤ Γ)
include hΓ

/-- **Milne, Theorem 4.9 (the dimension formula) for every congruence subgroup**, unconditional. -/
@[kb "milne2017mf" "Section 4, Theorem 4.9 (pdf p. 51), for every congruence subgroup"]
theorem dimensionFormula_of_Gamma_le : DimensionFormula Γ :=
  Wave10.dimensionFormula_of_riemannRoch' Γ (riemannRoch_of_Gamma_le N hΓ)

/-- **Milne, Proposition 4.12 (the valence formula) for every congruence subgroup**, unconditional. -/
@[kb "milne2017mf" "Section 4, Proposition 4.12 (pdf p. 53), for every congruence subgroup"]
theorem valenceFormula_of_Gamma_le : ValenceFormula Γ :=
  Wave10.valenceFormula_of_riemannRoch Γ (riemannRoch_of_Gamma_le N hΓ)

/-- **Milne, Theorem 1.27 (Riemann–Hurwitz) for maps `X(Γ) → ℙ¹`, `Γ` a congruence subgroup**, unconditional. -/
@[kb "milne2017mf" "Theorem 1.27 (Riemann-Hurwitz), pdf p. 22, for X(Gamma) -> P^1, Gamma a congruence subgroup"]
theorem riemannHurwitz_of_Gamma_le : RiemannHurwitzStatement (ModularCurveX Γ) (OnePoint ℂ) :=
  Wave10.riemannHurwitz_modularCurveX Γ (riemannRoch_of_Gamma_le N hΓ)

/-- **Milne, Theorem 2.22 (the genus formula) for every congruence subgroup**, unconditional: the analytic genus of
`X(Γ)` is `1 + m/12 - ν₂/4 - ν₃/3 - ν∞/2`. -/
@[kb "milne2017mf" "Theorem 2.22, pdf p. 37, for every congruence subgroup"]
theorem genus_of_Gamma_le :
    (genus (ModularCurveX Γ) : ℚ) =
      1 + (genusIndex Γ : ℚ) / 12 - (nuTwo Γ : ℚ) / 4 - (nuThree Γ : ℚ) / 3 - (nuInfty Γ : ℚ) / 2 :=
  Wave10.genus_modularCurveX_of_riemannRoch Γ (riemannRoch_of_Gamma_le N hΓ)

omit hΓ in
/-- **Milne, Example 2.23 (the genus of `X(N)`)**, unconditional: for `N ≥ 2`, `g(X(N)) = 1 + μ_N (N - 6) / (12 N)`,
`μ_N` the index of `±Γ(N)` (wave 4A proved it from Riemann–Hurwitz on `X(N)`, `genus_modularCurveX_Gamma`). -/
@[kb "milne2017mf" "Example 2.23, pdf p. 38, the genus of X(N)"]
theorem genus_X_Gamma {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    (RiemannSurface.genus (ModularCurveX (Gamma N)) : ℚ) =
      1 + ((Miyake.adjoinNegOne (Gamma N)).index : ℚ) * (N - 6) / (12 * N) :=
  genus_modularCurveX_Gamma hN (riemannHurwitz_of_Gamma_le (Γ := Gamma N) le_rfl)

end ModularFormsKB.Milne.Wave12
