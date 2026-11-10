import ModularFormsKB.Milne.Ch4.EisensteinGammaN
import ModularFormsKB.Milne.Ch4.Unfolding
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.Analysis.InnerProductSpace.Dual
import TauCeti.NumberTheory.ModularForms.SturmBound
import ModularFormsKB.Citation
/-!
# Miyake §2.1 and §2.6: the orthogonal complement of the cusp forms

Miyake, *Modular Forms* (Springer 1989), §2.1, p. 44, Theorem 2.1.7 (1), and §2.6, p. 69,
Corollary 2.6.12, for modular groups and even weight, trivial character.

* `Γ` is a subgroup of finite index of `SL₂(ℤ)` (Miyake's modular group), viewed in `GL₂(ℝ)`;
  the weight is `2k` (Miyake's `k` even); the character `χ` is trivial.
* Miyake's Petersson inner product `(f, g) = v(Γ\H)⁻¹ ∫_{Γ\H} f(z) \overline{g(z)} Im(z)^{2k} dv(z)`
  (defined when one of `f, g` is a cusp form) is `ModularFormsKB.Milne.milnePetersson Γ k f g`,
  the same integral without the factor `v(Γ\H)⁻¹` (a sum over `Γ\SL₂(ℤ)` of integrals over the
  standard fundamental domain). The normalising factor does not affect orthogonality.
* Miyake's `𝒩_k(Γ) = {g ∈ 𝒢_k(Γ) | (f, g) = 0 for all f ∈ 𝒮_k(Γ)}` is `peterssonComplement Γ k`.

Theorem 2.1.7 (1), `𝒢_k(Γ) = 𝒮_k(Γ) ⊕ 𝒩_k(Γ)`, is `isCompl_cuspFormSubmodule_peterssonComplement`
(Miyake: "an easy exercise of linear algebra"; here from the positive definiteness of the
Petersson product on cusp forms, Tau Ceti's `CuspForm.peterssonInnerCosetsCore`, the Riesz
representation theorem on the finite-dimensional space `𝒮_k(Γ)` (Tau Ceti's
`TauCeti.finiteDimensional_cuspForm_finiteIndex`), following the local inner-product-space
device of Tau Ceti's `TauCeti/NumberTheory/ModularForms/Petersson/Orthogonal.lean`).
Corollary 2.6.12 for `Γ = Γ(N)`, `2k ≥ 4`: `𝒩_k(Γ(N))` is spanned by the
Eisenstein series (`peterssonComplement_Gamma_eq_span_eisensteinSeries`), from Milne's Remark
4.38 (b) (`ModularFormsKB.Milne.orthogonal_cuspForms_iff_mem_eisenstein'`). Miyake's Eisenstein
series `g_i` of (2.6.14) are indexed by the cusps; Mathlib's `eisensteinSeries a` for
`a ∈ (ℤ/N)²` span the same space (Miyake, §2.6 and §7.1).
-/

open UpperHalfPlane ModularForm EisensteinSeries
open Matrix.SpecialLinearGroup
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake

open ModularFormsKB.Milne

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ)

/-- Additivity of `milnePetersson Γ k f ·` on modular forms, for a cusp form `f`. -/
theorem milnePetersson_add_right (f : CuspForm (Γ.map (mapGL ℝ)) (2 * k))
    (g₁ g₂ : ModularForm (Γ.map (mapGL ℝ)) (2 * k)) :
    milnePetersson Γ k f ⇑(g₁ + g₂) = milnePetersson Γ k f g₁ + milnePetersson Γ k f g₂ := by
  simp only [milnePetersson, ← Finset.sum_add_distrib, FunLike.coe_add]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [SlashAction.add_slash]
  exact UpperHalfPlane.peterssonInner_add_left _ _ _ _ _
    (integrableOn_milnePetersson Γ k f g₁ _).1 (integrableOn_milnePetersson Γ k f g₂ _).1

/-- Additivity of `milnePetersson Γ k · g` on cusp forms, for a modular form `g`. -/
theorem milnePetersson_add_left' (f₁ f₂ : CuspForm (Γ.map (mapGL ℝ)) (2 * k))
    (g : ModularForm (Γ.map (mapGL ℝ)) (2 * k)) :
    milnePetersson Γ k ⇑(f₁ + f₂) g = milnePetersson Γ k f₁ g + milnePetersson Γ k f₂ g := by
  simp only [milnePetersson, ← Finset.sum_add_distrib, FunLike.coe_add]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [SlashAction.add_slash]
  exact UpperHalfPlane.peterssonInner_add_right _ _ _ _ _
    (integrableOn_milnePetersson Γ k f₁ g _).1 (integrableOn_milnePetersson Γ k f₂ g _).1

/-- Miyake's `𝒩_k(Γ)` (weight `2k`, trivial character): the modular forms `g` with `(f, g) = 0`
for every cusp form `f`. -/
@[kb "miyake1989" "Section 2.1, definition of N_k(Gamma), p. 44"]
def peterssonComplement : Submodule ℂ (ModularForm (Γ.map (mapGL ℝ)) (2 * k)) where
  carrier := {g | ∀ f : CuspForm (Γ.map (mapGL ℝ)) (2 * k), milnePetersson Γ k f g = 0}
  add_mem' {a b} ha hb f := by
    rw [milnePetersson_add_right, ha f, hb f, add_zero]
  zero_mem' f := by
    simpa using milnePetersson_zero_right_aux Γ k f
  smul_mem' c g hg f := by
    simp only [FunLike.coe_smul]
    rw [milnePetersson_smul_right_aux, hg f, mul_zero]

theorem mem_peterssonComplement {g : ModularForm (Γ.map (mapGL ℝ)) (2 * k)} :
    g ∈ peterssonComplement Γ k ↔
      ∀ f : CuspForm (Γ.map (mapGL ℝ)) (2 * k), milnePetersson Γ k f g = 0 := Iff.rfl

section Riesz

/-- The Petersson core of Tau Ceti, installed locally to use Riesz representation. -/
local instance peterssonCoreInst :
    InnerProductSpace.Core ℂ (CuspForm (Γ.map (mapGL ℝ)) (2 * k)) :=
  CuspForm.peterssonInnerCosetsCore

local instance peterssonNormedInst : NormedAddCommGroup (CuspForm (Γ.map (mapGL ℝ)) (2 * k)) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

local instance peterssonIPSInst : InnerProductSpace ℂ (CuspForm (Γ.map (mapGL ℝ)) (2 * k)) :=
  InnerProductSpace.ofCore _

/-- For every modular form `g` there is a cusp form `s` with `(f, s) = (f, g)` for every cusp
form `f` (Riesz representation on the finite-dimensional space `𝒮_k(Γ)`). -/
theorem exists_cuspForm_petersson_eq (g : ModularForm (Γ.map (mapGL ℝ)) (2 * k)) :
    ∃ s : CuspForm (Γ.map (mapGL ℝ)) (2 * k), ∀ f : CuspForm (Γ.map (mapGL ℝ)) (2 * k),
      milnePetersson Γ k f s = milnePetersson Γ k f g := by
  let ℓ : CuspForm (Γ.map (mapGL ℝ)) (2 * k) →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ milnePetersson Γ k f g
      map_add' := fun f₁ f₂ ↦ milnePetersson_add_left' Γ k f₁ f₂ g
      map_smul' := fun c f ↦ by
        simp only [FunLike.coe_smul, RingHom.id_apply, smul_eq_mul]
        exact milnePetersson_smul_left Γ k c f g }
  refine ⟨(InnerProductSpace.toDual ℂ _).symm (LinearMap.toContinuousLinearMap ℓ), fun f ↦ ?_⟩
  exact InnerProductSpace.toDual_symm_apply (𝕜 := ℂ)
    (E := CuspForm (Γ.map (mapGL ℝ)) (2 * k)) (x := f) (y := LinearMap.toContinuousLinearMap ℓ)

end Riesz

/-- **Miyake, Theorem 2.1.7 (1)** (modular groups, even weight, trivial character):
`𝒢_k(Γ) = 𝒮_k(Γ) ⊕ 𝒩_k(Γ)`. -/
@[kb "miyake1989" "Theorem 2.1.7 (1), p. 44"]
theorem isCompl_cuspFormSubmodule_peterssonComplement :
    IsCompl (cuspFormSubmodule (Γ.map (mapGL ℝ)) (2 * k)) (peterssonComplement Γ k) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro g ⟨F, rfl⟩ hg
    have h0 : milnePetersson Γ k F F = 0 := hg F
    have : F = 0 := CuspForm.peterssonInnerCosets_definite F h0
    simp [this]
  · rw [codisjoint_iff, eq_top_iff]
    intro g _
    obtain ⟨s, hs⟩ := exists_cuspForm_petersson_eq Γ k g
    have hn : g - CuspForm.toModularFormₗ s ∈ peterssonComplement Γ k := by
      intro f
      have e : g = (g - CuspForm.toModularFormₗ s) + CuspForm.toModularFormₗ s := by abel
      have h1 := milnePetersson_add_right Γ k f (g - CuspForm.toModularFormₗ s)
        (CuspForm.toModularFormₗ s)
      rw [← e] at h1
      have h2 : milnePetersson Γ k f ⇑(CuspForm.toModularFormₗ s) = milnePetersson Γ k f s :=
        rfl
      rw [h2, hs f] at h1
      linear_combination -h1
    have e : g = CuspForm.toModularFormₗ s + (g - CuspForm.toModularFormₗ s) := by abel
    rw [e]
    exact Submodule.add_mem_sup ⟨s, rfl⟩ hn

/-- **Miyake, Corollary 2.6.12** for `Γ(N)` (weight `2k ≥ 4`, trivial character): `𝒩_k(Γ(N))`
is the space spanned by the Eisenstein series. -/
@[kb "miyake1989" "Corollary 2.6.12, p. 69"]
theorem peterssonComplement_Gamma_eq_span_eisensteinSeries (N : ℕ) [NeZero N] {k : ℕ}
    (hk : 2 ≤ k) (g : ModularForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (2 * k : ℤ)) :
    g ∈ peterssonComplement (CongruenceSubgroup.Gamma N) k ↔
      ⇑g ∈ Submodule.span ℂ
        (Set.range fun a : Fin 2 → ZMod N ↦ eisensteinSeries a (2 * k : ℤ)) :=
  orthogonal_cuspForms_iff_mem_eisenstein' N hk g

end ModularFormsKB.Miyake
