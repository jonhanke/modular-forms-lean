/-
# Inner product cores for the Petersson products of the Kohnen–Zagier adjoint

The adjoint $\mathcal S_D^*$ of the $D$-th Shimura lift is built
from Riesz representation on the finite-dimensional space $S^+_{k+1/2}(4)$. This file gives the two Petersson products
the structure of an `InnerProductSpace.Core`, and proves Riesz representation for a core:

- `plusInnerCore`: $\langle f, g\rangle = $ `peterssonFour k f g` on $S^+_{k+1/2}(4)$ (additive by
  `MultiplierSystem.peterssonFour_add_left`, definite by `MultiplierSystem.peterssonNormSqFour_ne_zero`);
- `levelOneInnerCore`: $\langle F, G\rangle = $ `peterssonOne k F G` on $S_{2k}(\mathrm{SL}_2(\mathbb Z))$ (additive because
  $\overline F G v^{2k}$ is bounded on the fundamental domain, definite by `peterssonNormSqOne_ne_zero`);
- `exists_riesz`: on a finite-dimensional space with a core, every linear functional is $x \mapsto \langle h, x\rangle$.
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import ModularFormsKB.HalfIntegral.Abstract.PeterssonDefinite
import ModularFormsKB.HalfIntegral.Abstract.KohnenZagierReduction

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup MeasureTheory UpperHalfPlane ModularForm
open scoped Real ComplexConjugate

/-- **Riesz representation for a core:** on a finite-dimensional space with an inner product core, every linear
functional is $x \mapsto \langle h, x\rangle$ for some $h$. -/
theorem exists_riesz {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (c : InnerProductSpace.Core ℂ V) (ψ : V →ₗ[ℂ] ℂ) : ∃ h : V, ∀ x, c.inner h x = ψ x := by
  letI : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  refine ⟨(InnerProductSpace.toDual ℂ V).symm (LinearMap.toContinuousLinearMap ψ), fun x ↦ ?_⟩
  exact InnerProductSpace.toDual_symm_apply (x := x) (y := LinearMap.toContinuousLinearMap ψ)

/-! ### Level one: sesquilinearity of `peterssonOne` -/

/-- $\overline F G v^{2k}$ is integrable on the fundamental domain for level one cusp forms. -/
theorem integrableOn_peterssonIntegrand_one (k : ℕ) (F G : CuspForm 𝒮ℒ (2 * k : ℕ)) :
    IntegrableOn (peterssonIntegrand 1 (((2 * k : ℕ) : ℝ)) F G) ModularGroup.fd := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left ((2 * k : ℕ) : ℤ) 𝒮ℒ F G
  have heq : peterssonIntegrand 1 (((2 * k : ℕ) : ℝ)) F G =
      petersson ((2 * k : ℕ) : ℤ) F G := by
    funext τ
    simp only [peterssonIntegrand, petersson, one_smul, Real.rpow_natCast, zpow_natCast, Complex.ofReal_pow]
  rw [heq]
  have hcont : Continuous (petersson ((2 * k : ℕ) : ℤ) F G) :=
    petersson_continuous _ (ModularFormClass.holo F).continuous (ModularFormClass.holo G).continuous
  exact Measure.integrableOn_of_bounded (M := C) volume_fd_lt_top.ne hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ ↦ hC τ)

private theorem two_mul_cast (k : ℕ) : (2 * (k : ℝ)) = (((2 * k : ℕ) : ℝ)) := by push_cast; ring

theorem peterssonOne_eq (k : ℕ) (F G : ℍ → ℂ) :
    peterssonOne k F G = peterssonReps [1] (((2 * k : ℕ) : ℝ)) F G := by
  rw [peterssonOne, ← two_mul_cast]

theorem peterssonOne_add_left (k : ℕ) (F F' G : CuspForm 𝒮ℒ (2 * k : ℕ)) :
    peterssonOne k (⇑F + ⇑F') G = peterssonOne k F G + peterssonOne k F' G := by
  rw [peterssonOne_eq, peterssonOne_eq, peterssonOne_eq]
  exact peterssonReps_add_left _ _ _ _ _
    (fun γ hγ ↦ by rw [List.mem_singleton.1 hγ]; exact integrableOn_peterssonIntegrand_one k F G)
    (fun γ hγ ↦ by rw [List.mem_singleton.1 hγ]; exact integrableOn_peterssonIntegrand_one k F' G)

theorem peterssonOne_add_right (k : ℕ) (F G G' : CuspForm 𝒮ℒ (2 * k : ℕ)) :
    peterssonOne k F (⇑G + ⇑G') = peterssonOne k F G + peterssonOne k F G' := by
  rw [peterssonOne_eq, peterssonOne_eq, peterssonOne_eq]
  exact peterssonReps_add_right _ _ _ _ _
    (fun γ hγ ↦ by rw [List.mem_singleton.1 hγ]; exact integrableOn_peterssonIntegrand_one k F G)
    (fun γ hγ ↦ by rw [List.mem_singleton.1 hγ]; exact integrableOn_peterssonIntegrand_one k F G')

/-! ### The cores -/

variable (M : MultiplierSystem) (k : ℕ)

/-- **The inner product core of $S^+_{k+1/2}(4)$** given by the Petersson product `peterssonFour`. -/
noncomputable def plusInnerCore : InnerProductSpace.Core ℂ (M.plusCuspForms k 1 1) where
  inner f g := peterssonFour k f.1 g.1
  conj_inner_symm f g := (peterssonFour_conj_symm k g.1 f.1).symm
  re_inner_nonneg f := by
    show 0 ≤ (peterssonFour k f.1 f.1).re
    rw [peterssonFour_self]
    exact (peterssonNormSqFour_nonneg k f.1).1
  add_left f g h := MultiplierSystem.peterssonFour_add_left M k 1 one_pos 1
    (M.plusCuspForms_le k 1 1 f.2) (M.plusCuspForms_le k 1 1 g.2) (M.plusCuspForms_le k 1 1 h.2)
  smul_left f g r := by
    show peterssonFour k ((r • f : M.plusCuspForms k 1 1) : ℍ → ℂ) g.1 = _
    rw [Submodule.coe_smul, peterssonFour, peterssonReps_smul_left, peterssonFour]
    ring
  definite f hf := by
    by_contra hne
    have h0 : (f : ℍ → ℂ) ≠ 0 := fun h ↦ hne (Subtype.ext h)
    exact M.peterssonNormSqFour_ne_zero k 1 one_pos 1 (M.plusCuspForms_le k 1 1 f.2) h0 hf

/-- **The inner product core of $S_{2k}(\mathrm{SL}_2(\mathbb Z))$** given by `peterssonOne`. -/
noncomputable def levelOneInnerCore : InnerProductSpace.Core ℂ (CuspForm 𝒮ℒ (2 * k : ℕ)) where
  inner F G := peterssonOne k F G
  conj_inner_symm F G := by
    simp only [peterssonOne]
    exact (peterssonReps_conj_symm _ _ _ _).symm
  re_inner_nonneg F := by
    show 0 ≤ (peterssonOne k F F).re
    rw [peterssonOne_self]
    exact (peterssonNormSqOne_nonneg k F).1
  add_left F F' G := by
    simpa using peterssonOne_add_left k F F' G
  smul_left F G r := by
    simp only [peterssonOne]
    exact peterssonReps_smul_left _ _ _ _ r
  definite F hF := by
    by_contra hne
    exact peterssonNormSqOne_ne_zero k F hne hF

end ModularFormsKB.HalfIntegral
