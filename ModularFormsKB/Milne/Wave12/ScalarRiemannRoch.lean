import ModularFormsKB.Milne.Wave12.FiberDescent
import ModularFormsKB.Milne.Wave11.Separation
import ModularFormsKB.Milne.Ch6.X0MinPoly
import ModularFormsKB.Milne.Ch6.X0Functions
import ModularFormsKB.Milne.Wave10.ModularCurveJ

/-!
# Riemann–Roch on `X(Γ)` for every `Γ` containing the matrices scalar modulo some `M`

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Theorem 1.20 (pdf p. 21), with the argument of the
proof of Theorem 6.1 (pdf p. 88).

Let `Γ_sc(M) ≤ SL₂(ℤ)` be the matrices congruent to a scalar modulo `M` (`GammaSc M`). It is the intersection of the
conjugates `δ⁻¹ Γ₀(M) δ`; already the three conjugates by `1`, `S` and `(1 0; 1 1)` cut it out
(`mem_GammaSc_of_conj`). On `X(Γ_sc(M))` the functions `j(Mδz)`, `δ ∈ SL₂(ℤ)`, are meromorphic (`scMer`). At a point
`τ` of `ℍ` where the `ψ(M)` functions `j(Mγz)`, `Γ₀(M)γ ∈ Γ₀(M)\SL₂(ℤ)`, take pairwise distinct values (Milne's
generic point in the proof of Theorem 6.1: they are pairwise distinct functions, `LevelTwo.exists_cosetVal_ne`), the
functions `j(Mδz)` separate the points of the fibre of `j` over `j(τ)` (`scMer_separates`): if `[γτ]` and `[γ'τ]` are
not separated, then `δ ε δ⁻¹ ∈ Γ₀(M)` for `ε = γ'⁻¹γ` and every `δ`, so `ε ∈ Γ_sc(M)` and the two points agree.

If the image of `Γ` in `PSL₂(ℝ)` contains that of `Γ_sc(M)`, separation descends along `X(Γ_sc(M)) → X(Γ)`
(`Wave12.exists_ne_of_pairwise_separated`), the fibre of `j : X(Γ) → ℙ¹` over a generic `j(τ)` off the branch values
is separated, and Riemann–Roch holds on `X(Γ)` (**`riemannRoch_of_GammaSc_le`**, through
`Wave11.riemannRoch_of_separated_fiber`).

The functions `j(αz)`, `α ∈ GL₂⁺(ℚ)`, all factor through some `X(Γ_sc(M))`, so this argument cannot reach a `Γ` whose
image does not contain any `Γ̄_sc(M)` (for instance `Γ(15)`, since `4 ≡ 1 (mod 3)` and `4 ≡ -1 (mod 5)`).
-/

open UpperHalfPlane CongruenceSubgroup Matrix MulAction TauCeti.RiemannSurface
open ModularFormsKB.Milne.RiemannSurface MeromorphicFunction Subgroup.CompactifiedQuotient
open TauCeti.ModularForm
open scoped MatrixGroups Manifold Pointwise

noncomputable section

namespace ModularFormsKB.Milne.Wave12

/-! ### The group `Γ_sc(M)` -/

/-- **`Γ_sc(M)`**: the matrices of `SL₂(ℤ)` congruent to a scalar matrix modulo `M` (the preimage of the centre of
`SL₂(ℤ/Mℤ)`). -/
def GammaSc (M : ℕ) : Subgroup SL(2, ℤ) :=
  (Subgroup.center SL(2, ZMod M)).comap (SpecialLinearGroup.map (Int.castRingHom (ZMod M)))

instance (M : ℕ) : (GammaSc M).Normal := Subgroup.Normal.comap inferInstance _

theorem mem_GammaSc_iff {M : ℕ} {γ : SL(2, ℤ)} :
    γ ∈ GammaSc M ↔ ∃ r : ZMod M, r ^ 2 = 1 ∧ scalar (Fin 2) r =
      (SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
  rw [GammaSc, Subgroup.mem_comap, Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]

theorem Gamma_le_GammaSc (M : ℕ) : Gamma M ≤ GammaSc M := by
  intro γ hγ
  rw [Gamma_mem'] at hγ
  show _ ∈ Subgroup.center _
  rw [hγ]
  exact Subgroup.one_mem _

instance (M : ℕ) [NeZero M] : (GammaSc M).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma_le_GammaSc M)

theorem GammaSc_le_Gamma0 (M : ℕ) : GammaSc M ≤ Gamma0 M := by
  intro γ hγ
  obtain ⟨r, -, hr⟩ := mem_GammaSc_iff.1 hγ
  rw [Gamma0_mem]
  have := congrFun (congrFun hr 1) 0
  simpa using this.symm

/-- The lower unipotent matrix `(1 0; 1 1)`. -/
def lowerT : SL(2, ℤ) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩

theorem coe_lowerT : (lowerT : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 1, 1] := rfl

/-- **`Γ_sc(M)` is cut out by three conjugates of `Γ₀(M)`**: if `ε`, `S ε S⁻¹` and `L ε L⁻¹` (`L = (1 0; 1 1)`) lie in
`Γ₀(M)`, then `ε` is scalar modulo `M`. -/
theorem mem_GammaSc_of_conj {M : ℕ} (ε : SL(2, ℤ)) (h1 : ε ∈ Gamma0 M)
    (hS : ModularGroup.S * ε * ModularGroup.S⁻¹ ∈ Gamma0 M) (hL : lowerT * ε * lowerT⁻¹ ∈ Gamma0 M) :
    ε ∈ GammaSc M := by
  rw [Gamma0_mem] at h1 hS hL
  have hc : ((ε 1 0 : ℤ) : ZMod M) = 0 := h1
  have hb : ((ε 0 1 : ℤ) : ZMod M) = 0 := by
    have : (ModularGroup.S * ε * ModularGroup.S⁻¹) 1 0 = - ε 0 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_S, Matrix.adjugate_fin_two_of]
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      simp
    rw [this] at hS
    push_cast at hS
    exact neg_eq_zero.1 hS
  have had : ((ε 0 0 : ℤ) : ZMod M) = ((ε 1 1 : ℤ) : ZMod M) := by
    have : (lowerT * ε * lowerT⁻¹) 1 0 = ε 0 0 + ε 1 0 - ε 0 1 - ε 1 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_inv, coe_lowerT, Matrix.adjugate_fin_two_of]
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      simp
      ring
    rw [this] at hL
    push_cast at hL
    rw [hc, hb] at hL
    linear_combination hL
  have hdet := ε.det_coe
  rw [det_fin_two] at hdet
  refine mem_GammaSc_iff.2 ⟨((ε 0 0 : ℤ) : ZMod M), ?_, ?_⟩
  · have := congrArg (Int.cast : ℤ → ZMod M) hdet
    push_cast at this
    rw [hb, hc, ← had] at this
    linear_combination this
  · rw [Matrix.scalar_apply]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [Matrix.diagonal, hb, hc, had]

/-! ### The functions `j(Mδz)` on `X(Γ_sc(M))` -/

variable (M : ℕ) [NeZero M]

theorem pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)

omit [NeZero M] in
theorem barGammaSc_le_Gamma0 : barGamma (GammaSc M) ≤ barGamma (Gamma0 M) :=
  Subgroup.map_mono (GammaSc_le_Gamma0 M)

/-- The map `X(Γ_sc(M)) → X₀(M)`, `[z] ↦ [δz]`. -/
def scMap (δ : SL(2, ℤ)) : ModularCurveX (GammaSc M) → X0 M :=
  Subgroup.compactifiedQuotientMap (barGammaSc_le_Gamma0 M) ∘
    Subgroup.compactifiedQuotientConj (Subgroup.conjAct_sl2zToPSL2R_smul_map (GammaSc M) δ)

omit [NeZero M] in
theorem mdifferentiable_scMap (δ : SL(2, ℤ)) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (scMap M δ) :=
  (Subgroup.CompactifiedQuotient.mdifferentiable_compactifiedQuotientMap _).comp
    (Subgroup.CompactifiedQuotient.mdifferentiable_compactifiedQuotientConj _)

omit [NeZero M] in
theorem scMap_ofQuotient (δ : SL(2, ℤ)) (z : ℍ) :
    scMap M δ (ofQuotient (Quotient.mk _ z)) = ofQuotient (Quotient.mk _ (δ • z)) := by
  simp only [scMap, Function.comp_apply, Subgroup.compactifiedQuotientConj_ofQuotient,
    Subgroup.quotientConjHomeomorph_mk, Subgroup.compactifiedQuotientMap_ofQuotient, sl2zToPSL2R_smul_eq]
  rfl

/-- **`j(Mδz)` as a meromorphic function on `X(Γ_sc(M))`.** -/
def scMer (δ : SL(2, ℤ)) : MeromorphicFunction (ModularCurveX (GammaSc M)) where
  toFun := jNX M (pos M) ∘ scMap M δ
  mdifferentiable' := (jNX M (pos M)).mdifferentiable.comp (mdifferentiable_scMap M δ)
  ne_infty' := fun h ↦ by
    have := congrFun h (ofQuotient (Quotient.mk _ UpperHalfPlane.I))
    simp only [Function.comp_apply, scMap_ofQuotient] at this
    rw [isJNOnX0_jNX M (pos M)] at this
    exact OnePoint.coe_ne_infty _ this

theorem scMer_ofQuotient (δ : SL(2, ℤ)) (z : ℍ) :
    scMer M δ (ofQuotient (Quotient.mk _ z)) = (j (scaleH M (pos M) (δ • z)) : OnePoint ℂ) := by
  show jNX M (pos M) (scMap M δ _) = _
  rw [scMap_ofQuotient]
  exact isJNOnX0_jNX M (pos M) _

/-! ### Points of a fibre of `j` -/

theorem modularCurveXJ_ofQuotient (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (z : ℍ) :
    modularCurveXJ Γ (ofQuotient (Quotient.mk _ z)) = (j z : OnePoint ℂ) := by
  simp [modularCurveXJ, modularCurveXMap, TauCeti.ModularGroup.jQuotient_mk]

theorem modularCurveXJ_ofCusp (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (C : (barGamma Γ).CuspOrbit) :
    modularCurveXJ Γ (ofCusp C) = (OnePoint.infty : OnePoint ℂ) := by
  simp [modularCurveXJ, modularCurveXMap]

/-- A point of `X(Δ)` lying over a point of `X(Γ)` where `j = j(τ)` is the class of some `γτ`. -/
theorem exists_eq_ofQuotient' {Δ Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hΓ : barGamma Δ ≤ barGamma Γ)
    {x : ModularCurveX Δ} {τ : ℍ}
    (h : modularCurveXJ Γ (Subgroup.compactifiedQuotientMap hΓ x) = (j τ : OnePoint ℂ)) :
    ∃ γ : SL(2, ℤ), x = ofQuotient (Quotient.mk _ (γ • τ)) := by
  cases x with
  | ofQuotient p =>
    induction p using Quotient.inductionOn with
    | h w =>
      rw [Subgroup.compactifiedQuotientMap_ofQuotient] at h
      have h' : modularCurveXJ Γ (ofQuotient (Quotient.mk _ w)) = (j τ : OnePoint ℂ) := h
      rw [modularCurveXJ_ofQuotient] at h'
      obtain ⟨γ, hγ⟩ := TauCeti.ModularGroup.j_eq_j_iff.1 (OnePoint.coe_injective h').symm
      exact ⟨γ, by rw [hγ]⟩
  | ofCusp C =>
    rw [Subgroup.compactifiedQuotientMap_ofCusp, modularCurveXJ_ofCusp] at h
    exact absurd h.symm (OnePoint.coe_ne_infty _)

omit [NeZero M] in
/-- A point of `X(Γ_sc(M))` lying over a point of `X(Γ)` where `j = j(τ)` is the class of some `γτ`. -/
theorem exists_eq_ofQuotient {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hΓ : barGamma (GammaSc M) ≤ barGamma Γ)
    {x : ModularCurveX (GammaSc M)} {τ : ℍ}
    (h : modularCurveXJ Γ (Subgroup.compactifiedQuotientMap hΓ x) = (j τ : OnePoint ℂ)) :
    ∃ γ : SL(2, ℤ), x = ofQuotient (Quotient.mk _ (γ • τ)) :=
  exists_eq_ofQuotient' hΓ h

/-! ### Separation -/

/-- **The functions `j(Mδz)` separate the points of a generic fibre of `j` on `X(Γ_sc(M))`.** -/
theorem scMer_separates {τ : ℍ}
    (hτ : ∀ c c' : LevelTwo.Cosets M, c ≠ c' → LevelTwo.cosetVal (pos M) c τ ≠ LevelTwo.cosetVal (pos M) c' τ)
    {γ γ' : SL(2, ℤ)}
    (hne : (ofQuotient (Quotient.mk _ (γ • τ)) : ModularCurveX (GammaSc M)) ≠ ofQuotient (Quotient.mk _ (γ' • τ))) :
    ∃ g : MeromorphicFunction (ModularCurveX (GammaSc M)),
      g (ofQuotient (Quotient.mk _ (γ • τ))) ≠ g (ofQuotient (Quotient.mk _ (γ' • τ))) := by
  by_contra hall
  push Not at hall
  set ε := γ'⁻¹ * γ
  have key : ∀ δ₀ : SL(2, ℤ), δ₀ * ε * δ₀⁻¹ ∈ Gamma0 M := by
    intro δ₀
    have h := hall (scMer M (δ₀ * γ'⁻¹))
    rw [scMer_ofQuotient, scMer_ofQuotient] at h
    have h2 := OnePoint.coe_injective h
    by_contra hn
    have hc : (Quotient.mk _ (δ₀ * ε) : LevelTwo.Cosets M) ≠ Quotient.mk _ δ₀ := by
      intro heq
      apply hn
      have : QuotientGroup.rightRel (Gamma0 M) (δ₀ * ε) δ₀ := Quotient.exact heq
      rw [QuotientGroup.rightRel_apply] at this
      have := inv_mem this
      simpa [mul_assoc] using this
    apply hτ _ _ hc
    rw [LevelTwo.cosetVal_mk, LevelTwo.cosetVal_mk]
    simp only [LevelTwo.jN]
    rw [← mul_smul, ← mul_smul] at h2
    simpa [ε, mul_assoc] using h2
  have hε : ε ∈ GammaSc M :=
    mem_GammaSc_of_conj ε (by simpa using key 1) (key _) (key _)
  apply hne
  congr 1
  refine Quotient.sound ?_
  change γ • τ ∈ MulAction.orbit _ (γ' • τ)
  rw [MulAction.mem_orbit_iff]
  have hmem : γ' * ε * γ'⁻¹ ∈ GammaSc M := (inferInstance : (GammaSc M).Normal).conj_mem _ hε γ'
  refine ⟨⟨sl2zToPSL2R (γ' * ε * γ'⁻¹), Subgroup.mem_map_of_mem _ hmem⟩, ?_⟩
  rw [Subgroup.smul_def]
  simp only
  rw [sl2zToPSL2R_smul_eq, ← mul_smul]
  simp [ε, mul_assoc]

/-- **Milne's generic point**, with finitely many further holomorphic functions, none identically zero, required not
to vanish. -/
theorem exists_generic' {ι : Type*} (s : Finset ι) (G : ι → ℍ → ℂ)
    (hG : ∀ i ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (G i)) (hGne : ∀ i ∈ s, ∃ z, G i z ≠ 0)
    {B : Set (OnePoint ℂ)} (hB : B.Finite) :
    ∃ τ : ℍ, (∀ c c' : LevelTwo.Cosets M, c ≠ c' →
      LevelTwo.cosetVal (pos M) c τ ≠ LevelTwo.cosetVal (pos M) c' τ) ∧ (j τ : OnePoint ℂ) ∉ B ∧
      ∀ i ∈ s, G i τ ≠ 0 := by
  classical
  have hB' : {c : ℂ | (c : OnePoint ℂ) ∈ B}.Finite := hB.preimage OnePoint.coe_injective.injOn
  let S1 : Finset (LevelTwo.Cosets M × LevelTwo.Cosets M) := Finset.univ.filter fun p ↦ p.1 ≠ p.2
  let g : ((LevelTwo.Cosets M × LevelTwo.Cosets M) ⊕ ℂ) ⊕ ι → ℍ → ℂ :=
    Sum.elim (Sum.elim (fun p z ↦ LevelTwo.cosetVal (pos M) p.1 z - LevelTwo.cosetVal (pos M) p.2 z)
      (fun c z ↦ j z - c)) G
  have hmd_c : ∀ c : LevelTwo.Cosets M, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (LevelTwo.cosetVal (pos M) c) := by
    intro c
    induction c using Quotient.inductionOn with
    | h γ => exact LevelTwo.mdiff_jN_smul (pos M) γ
  have hmd_j : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : ℍ ↦ j z) :=
    LevelTwo.mdiff_j_comp (φ := id) 1 0 1 one_pos one_pos (fun τ ↦ by simp)
  obtain ⟨τ, hτ⟩ := LevelTwo.exists_forall_ne_zero ((S1.disjSum hB'.toFinset).disjSum s) g
    (fun i hi ↦ by
      rcases i with (p | c) | i
      · exact (hmd_c p.1).sub (hmd_c p.2)
      · exact hmd_j.sub mdifferentiable_const
      · exact hG i (Finset.inr_mem_disjSum.1 hi))
    (fun i hi ↦ by
      rcases i with (p | c) | i
      · have hp : p.1 ≠ p.2 := by simpa [S1] using hi
        exact LevelTwo.exists_cosetVal_ne (pos M) hp
      · obtain ⟨z, hz⟩ := LevelTwo.exists_eval_j_ne_zero (Polynomial.X_sub_C_ne_zero c)
        exact ⟨z, by simpa [g] using hz⟩
      · exact hGne i (Finset.inr_mem_disjSum.1 hi))
  refine ⟨τ, fun c c' hcc' h ↦ ?_, fun hj ↦ ?_, fun i hi ↦ hτ (Sum.inr i) (Finset.inr_mem_disjSum.2 hi)⟩
  · have := hτ (Sum.inl (Sum.inl (c, c')))
      (Finset.inl_mem_disjSum.2 (Finset.inl_mem_disjSum.2 (by simp [S1, hcc'])))
    exact this (by simp [g, h])
  · have := hτ (Sum.inl (Sum.inr (j τ))) (Finset.inl_mem_disjSum.2 (Finset.inr_mem_disjSum.2 (by simpa using hj)))
    exact this (by simp [g])

/-- **Milne's generic point**: a point `τ` where the `ψ(M)` coset functions take pairwise distinct values and `j(τ)`
avoids a given finite set. -/
theorem exists_generic {B : Set (OnePoint ℂ)} (hB : B.Finite) :
    ∃ τ : ℍ, (∀ c c' : LevelTwo.Cosets M, c ≠ c' →
      LevelTwo.cosetVal (pos M) c τ ≠ LevelTwo.cosetVal (pos M) c' τ) ∧ (j τ : OnePoint ℂ) ∉ B := by
  obtain ⟨τ, h1, h2, -⟩ := exists_generic' M (∅ : Finset Empty) (fun _ _ ↦ 0) (by simp) (by simp) hB
  exact ⟨τ, h1, h2⟩

/-! ### Riemann–Roch -/

theorem isFiniteRelIndex_barGammaSc {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (hΓ : barGamma (GammaSc M) ≤ barGamma Γ) : (barGamma (GammaSc M)).IsFiniteRelIndex (barGamma Γ) := by
  have h1 : (barGamma (GammaSc M)).relIndex psl2zToPSL2R.range ≠ 0 :=
    Subgroup.IsFiniteRelIndex.relIndex_ne_zero
  have h2 := Subgroup.relIndex_mul_relIndex (barGamma (GammaSc M)) (barGamma Γ) psl2zToPSL2R.range hΓ
    Γ.map_sl2zToPSL2R_le_range_psl2zToPSL2R
  exact ⟨fun h ↦ h1 (by rw [← h2, h, zero_mul])⟩

/-- **Milne, Theorem 1.20 (Riemann–Roch) on `X(Γ)` when `Γ̄ ⊇ Γ̄_sc(M)`**: for every finite-index `Γ ≤ SL₂(ℤ)` whose
image in `PSL₂(ℝ)` contains the image of the matrices scalar modulo some `M ≥ 1`. -/
@[kb "milne2017mf" "Theorem 1.20 (Riemann-Roch), pdf p. 21, for X(Gamma), Gamma containing the matrices scalar mod M"]
theorem riemannRoch_of_GammaSc_le {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (hΓ : barGamma (GammaSc M) ≤ barGamma Γ) : RiemannRochStatement (ModularCurveX Γ) := by
  have hf := Wave10.isNonconstant_jMeromorphic Γ
  set F := toFiniteHolomorphicMap (Wave10.jMeromorphic Γ) hf
  obtain ⟨τ, hτ, hB⟩ := exists_generic M F.finite_branchValues
  refine Wave11.riemannRoch_of_separated_fiber hf hB ?_
  have := isFiniteRelIndex_barGammaSc M hΓ
  let π := TauCeti.Fuchsian.compactifiedQuotientFiniteHolomorphicMap hΓ
  intro y hy y' hy' hyy
  refine exists_ne_of_pairwise_separated π
    (exists_ne_zero_apply_eq_zero_of_nonconstant hf) hyy ?_
  have hfib : ∀ x, π x = y ∨ π x = y' → ∃ γ : SL(2, ℤ), x = ofQuotient (Quotient.mk _ (γ • τ)) := by
    intro x hx
    refine exists_eq_ofQuotient M hΓ ?_
    have hy0 : modularCurveXJ Γ y = (j τ : OnePoint ℂ) := hy
    have hy0' : modularCurveXJ Γ y' = (j τ : OnePoint ℂ) := hy'
    rcases hx with h | h
    · rw [← hy0, ← h]; rfl
    · rw [← hy0', ← h]; rfl
  intro x hx x' hx' hxx'
  obtain ⟨γ, rfl⟩ := hfib x hx
  obtain ⟨γ', rfl⟩ := hfib x' hx'
  exact scMer_separates M hτ hxx'

end ModularFormsKB.Milne.Wave12
