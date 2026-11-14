import ModularFormsKB.Miyake.Wave7.StarHecke
import ModularFormsKB.Miyake.Wave7.Parity
import ModularFormsKB.Miyake.Wave6.OldSpace
import ModularFormsKB.Miyake.Wave4.Newforms
import TauCeti.NumberTheory.ModularForms.Newforms.Fricke

/-!
# Miyake §4.6: Theorem 4.6.15

Miyake, *Modular Forms* (Springer 1989), Theorem 4.6.15, p. 166.

* (1) `ω_N = [0 -1; N 0]` induces isomorphisms `𝒮_k^0(N, χ) ≃ 𝒮_k^0(N, conj χ)` and
  `𝒮_k^1(N, χ) ≃ 𝒮_k^1(N, conj χ)` (`newSpaceOmegaEquiv`, `oldSpaceOmegaEquiv`), where
  `𝒮_k^0` is wave 4's `newSpace` and `𝒮_k^1` is wave 6's `oldSpace` (Miyake's definitions).
* (2) If `f` is a primitive form of `𝒮_k^0(N, χ)`, then `f_ρ(z) = Σ conj(a_n) e(nz)` is a primitive
  form of `𝒮_k^0(N, conj χ)` and `f |_k ω_N = c f_ρ` (`exists_isPrimitive_conj_omega`).

Inputs from Tau Ceti: the Fricke operator `frickeOperatorCusp` (Miyake's `f ↦ f|_k ω_N`, in
Mathlib's slash normalisation), its preservation of the old and new subspaces, and Atkin–Li's
pseudo-eigenvalue theorem `Newform.exists_normalizedFrickeOperatorCusp_eq_smul_conj` (which Tau
Ceti itself attributes to Miyake's Theorem 4.6.15 (2)). On `𝒮_k(N, χ)` the character `conj χ` is
`χ⁻¹`.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

noncomputable section

namespace ModularFormsKB.Miyake.Wave8

open ModularFormsKB.Miyake.Wave4 ModularFormsKB.Miyake.Wave6 ModularFormsKB.Miyake.Wave7

variable {N : ℕ} [NeZero N]

theorem frickeOperatorCusp_mem_cuspSpace (k : ℤ) (χ : DirichletCharacter ℂ N)
    (f : cuspSpace k χ) :
    TauCeti.frickeOperatorCusp k (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
      cuspSpace k χ⁻¹ := by
  have := TauCeti.frickeOperatorCusp_mem_cuspFormCharSpace k χ.toUnitHom f.2
  rw [← toUnitHom_inv_eq_inv] at this
  exact this

/-- Miyake's `f ↦ f |_k ω_N` from `𝒮_k(N, χ)` to `𝒮_k(N, conj χ)` (Mathlib's slash
normalisation; Miyake's differs by the positive constant `N^{1-k/2}`). -/
def omegaMap (k : ℤ) (χ : DirichletCharacter ℂ N) : cuspSpace k χ →ₗ[ℂ] cuspSpace k χ⁻¹ :=
  ((TauCeti.frickeOperatorCusp k).comp (cuspSpace k χ).subtype).codRestrict _
    (frickeOperatorCusp_mem_cuspSpace k χ)

theorem coe_omegaMap (k : ℤ) (χ : DirichletCharacter ℂ N) (f : cuspSpace k χ) :
    ⇑((omegaMap k χ f : cuspSpace k χ⁻¹) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] omega N :=
  rfl

theorem coe_omegaMap_omegaMap (k : ℤ) (χ : DirichletCharacter ℂ N) (f : cuspSpace k χ) :
    ((omegaMap k χ⁻¹ (omegaMap k χ f) : cuspSpace k χ⁻¹⁻¹) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      TauCeti.frickeScalar N k • (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  TauCeti.frickeOperatorCusp_frickeOperatorCusp_apply k _

theorem omegaMap_injective (k : ℤ) (χ : DirichletCharacter ℂ N) :
    Function.Injective (omegaMap k χ) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ ?_
  have h := coe_omegaMap_omegaMap k χ f
  rw [hf, map_zero] at h
  apply Subtype.ext
  have h' : TauCeti.frickeScalar N k • (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = 0 := h.symm
  exact (smul_eq_zero.mp h').resolve_left (TauCeti.frickeScalar_ne_zero k)

/-- **Miyake, Theorem 4.6.15 (1)**, new part: `ω_N` maps `𝒮_k^0(N, χ)` into `𝒮_k^0(N, conj χ)`. -/
theorem omegaMap_mem_newSpace (k : ℤ) (χ : DirichletCharacter ℂ N) {f : cuspSpace k χ}
    (hf : f ∈ newSpace k χ) : omegaMap k χ f ∈ newSpace k χ⁻¹ := by
  have h := TauCeti.normalizedFrickeOperatorCusp_mem_cuspFormsNew hf
  rw [TauCeti.normalizedFrickeOperatorCusp_def, LinearMap.smul_apply] at h
  exact (Submodule.smul_mem_iff _ (TauCeti.atkinLehnerNormalizer_ne_zero (NeZero.ne N) k)).mp h

/-- Membership in Miyake's `𝒮_k^1(N, χ)` read in `S_k(Γ₁(N))`. -/
theorem mem_oldSpace_iff (k : ℤ) (χ : DirichletCharacter ℂ N) (f : cuspSpace k χ) :
    f ∈ oldSpace k χ ↔ (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ TauCeti.cuspFormsOld N k := by
  constructor
  · intro hf
    have : (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ (oldSpace k χ).map (cuspSpace k χ).subtype :=
      ⟨f, hf, rfl⟩
    rw [map_oldSpace] at this
    exact this.1
  · intro hf
    have : (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ (oldSpace k χ).map (cuspSpace k χ).subtype := by
      rw [map_oldSpace]; exact ⟨hf, f.2⟩
    obtain ⟨g, hg, hge⟩ := this
    rwa [← Subtype.ext hge]

/-- **Miyake, Theorem 4.6.15 (1)**, old part: `ω_N` maps `𝒮_k^1(N, χ)` into `𝒮_k^1(N, conj χ)`. -/
theorem omegaMap_mem_oldSpace (k : ℤ) (χ : DirichletCharacter ℂ N) {f : cuspSpace k χ}
    (hf : f ∈ oldSpace k χ) : omegaMap k χ f ∈ oldSpace k χ⁻¹ := by
  rw [mem_oldSpace_iff] at hf ⊢
  exact TauCeti.frickeOperatorCusp_mem_cuspFormsOld hf

/-- Undoing `ω_N`: every `g ∈ 𝒮_k(N, conj χ)` is `ω_N f` for `f = c · (g |_k ω_N)`. -/
theorem exists_omegaMap_eq (k : ℤ) (χ : DirichletCharacter ℂ N) (g : cuspSpace k χ⁻¹) :
    ∃ f : cuspSpace k χ, omegaMap k χ f = g ∧
      (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
        (TauCeti.frickeScalar N k)⁻¹ • TauCeti.frickeOperatorCusp k
          (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  have hmem : (TauCeti.frickeScalar N k)⁻¹ • TauCeti.frickeOperatorCusp k
      (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspSpace k χ := by
    have h := frickeOperatorCusp_mem_cuspSpace k χ⁻¹ g
    rw [inv_inv] at h
    exact Submodule.smul_mem _ _ h
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_, rfl⟩
  show TauCeti.frickeOperatorCusp k ((TauCeti.frickeScalar N k)⁻¹ •
    TauCeti.frickeOperatorCusp k (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) = g
  rw [map_smul, TauCeti.frickeOperatorCusp_frickeOperatorCusp_apply, smul_smul,
    inv_mul_cancel₀ (TauCeti.frickeScalar_ne_zero k), one_smul]

/-- **Miyake, Theorem 4.6.15 (1)**: `ω_N` induces an isomorphism
`𝒮_k^0(N, χ) ≃ 𝒮_k^0(N, conj χ)`. -/
@[kb "miyake1989" "Theorem 4.6.15 (1), p. 166 (new part)"]
def newSpaceOmegaEquiv (k : ℤ) (χ : DirichletCharacter ℂ N) :
    newSpace k χ ≃ₗ[ℂ] newSpace k χ⁻¹ :=
  LinearEquiv.ofBijective
    (((omegaMap k χ).comp (newSpace k χ).subtype).codRestrict _
      fun f ↦ omegaMap_mem_newSpace k χ f.2)
    ⟨fun f g h ↦ Subtype.ext (omegaMap_injective k χ (congrArg Subtype.val h)), fun g ↦ by
      obtain ⟨f, hf, hfe⟩ := exists_omegaMap_eq k χ g
      have hnew : f ∈ newSpace k χ := by
        show (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ TauCeti.cuspFormsNew N k
        rw [hfe]
        exact Submodule.smul_mem _ _ (omegaMap_mem_newSpace k χ⁻¹ g.2)
      exact ⟨⟨f, hnew⟩, Subtype.ext hf⟩⟩

theorem coe_newSpaceOmegaEquiv (k : ℤ) (χ : DirichletCharacter ℂ N) (f : newSpace k χ) :
    ⇑(((newSpaceOmegaEquiv k χ f : newSpace k χ⁻¹) : cuspSpace k χ⁻¹) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ⇑((f : cuspSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] omega N :=
  rfl

/-- **Miyake, Theorem 4.6.15 (1)**: `ω_N` induces an isomorphism
`𝒮_k^1(N, χ) ≃ 𝒮_k^1(N, conj χ)`. -/
@[kb "miyake1989" "Theorem 4.6.15 (1), p. 166 (old part)"]
def oldSpaceOmegaEquiv (k : ℤ) (χ : DirichletCharacter ℂ N) :
    oldSpace k χ ≃ₗ[ℂ] oldSpace k χ⁻¹ :=
  LinearEquiv.ofBijective
    (((omegaMap k χ).comp (oldSpace k χ).subtype).codRestrict _
      fun f ↦ omegaMap_mem_oldSpace k χ f.2)
    ⟨fun f g h ↦ Subtype.ext (omegaMap_injective k χ (congrArg Subtype.val h)), fun g ↦ by
      obtain ⟨f, hf, hfe⟩ := exists_omegaMap_eq k χ g
      have hold : f ∈ oldSpace k χ := by
        rw [mem_oldSpace_iff, hfe]
        refine Submodule.smul_mem _ _ ?_
        have := (mem_oldSpace_iff k χ⁻¹ g).mp g.2
        exact TauCeti.frickeOperatorCusp_mem_cuspFormsOld this
      exact ⟨⟨f, hold⟩, Subtype.ext hf⟩⟩

theorem coe_oldSpaceOmegaEquiv (k : ℤ) (χ : DirichletCharacter ℂ N) (f : oldSpace k χ) :
    ⇑(((oldSpaceOmegaEquiv k χ f : oldSpace k χ⁻¹) : cuspSpace k χ⁻¹) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ⇑((f : cuspSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] omega N :=
  rfl

/-- **Miyake, Theorem 4.6.15 (2)**: if `f = Σ a_n e(nz)` is a primitive form of `𝒮_k^0(N, χ)`,
then `f_ρ = Σ conj(a_n) e(nz)` is a primitive form of `𝒮_k^0(N, conj χ)`, and
`f |_k ω_N = c f_ρ` for some `c ∈ ℂ`. -/
@[kb "miyake1989" "Theorem 4.6.15 (2), p. 166"]
theorem exists_isPrimitive_conj_omega (k : ℤ) (χ : DirichletCharacter ℂ N) {f : cuspSpace k χ}
    (hf : IsPrimitive f) :
    ∃ g : cuspSpace k χ⁻¹, (∀ n, coeff g n = starRingEnd ℂ (coeff f n)) ∧ IsPrimitive g ∧
      ∃ c : ℂ, ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] omega N =
        c • ⇑(g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  obtain ⟨F, hχ, hF⟩ := (isPrimitive_iff_exists_newform f).mp hf
  have hχc : F.conj.χ = (χ⁻¹).toUnitHom := by
    rw [F.χ_conj, hχ, toUnitHom_inv_eq_inv]
  have hmem : F.conj.toCuspForm ∈ cuspSpace k χ⁻¹ := by
    change _ ∈ TauCeti.cuspFormCharSpace k (χ⁻¹).toUnitHom
    rw [← hχc]
    exact F.conj.mem_charSpace
  refine ⟨⟨_, hmem⟩, fun n ↦ ?_, (isPrimitive_iff_exists_newform _).mpr ⟨F.conj, hχc, rfl⟩, ?_⟩
  · show (qExpansion 1 F.conj.toCuspForm).coeff n =
      starRingEnd ℂ ((qExpansion 1 (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n)
    rw [F.qExpansion_conj, PowerSeries.coeff_map, hF]
  · obtain ⟨c, hc⟩ := F.exists_normalizedFrickeOperatorCusp_eq_smul_conj
    have ha := TauCeti.atkinLehnerNormalizer_ne_zero (NeZero.ne N) k
    refine ⟨(TauCeti.atkinLehnerNormalizer N k)⁻¹ * c, ?_⟩
    rw [TauCeti.normalizedFrickeOperatorCusp_def, LinearMap.smul_apply, hF] at hc
    have h := congrArg (fun F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k ↦
      (TauCeti.atkinLehnerNormalizer N k)⁻¹ • ⇑F) hc
    simp only [CuspForm.coe_smul, smul_smul, inv_mul_cancel₀ ha, one_smul] at h
    rw [← TauCeti.coe_frickeOperatorCusp, h]

end ModularFormsKB.Miyake.Wave8
