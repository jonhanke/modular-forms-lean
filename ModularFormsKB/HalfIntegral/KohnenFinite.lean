/-
# $S_{k+1/2}(4N,\chi)$ is finite-dimensional

For the theta multiplier, multiplication by $\theta$ is an injective linear map from $S_{k+1/2}(4N,\chi)$ into the
integral weight $k+1$ modular forms on $\Gamma_1(4N)$ ($j(\gamma,\tau)^2 = \chi_{-4}(d)(c\tau+d)$, `thetaMult_sq`, and
$\chi(d) = \chi_{-4}(d) = 1$ for $\gamma \in \Gamma_1(4N)$; $\theta \neq 0$ since $\theta(\tau) \neq 0$ for
$\operatorname{Im}\tau > 1$, `theta_ne_zero_of_one_lt_im`). The latter space is finite-dimensional (Tau Ceti
`finiteDimensional_modularForm_finiteIndex`, from the Sturm bound; the product is `halfIntMul`), hence so is the former
(`finiteDimensional_thetaCuspForms`), and so is Kohnen's plus space (`finiteDimensional_plusSpace`).
-/
import ModularFormsKB.HalfIntegral.KohnenPlusHecke
import ModularFormsKB.HalfIntegral.ThetaForms
import ModularFormsKB.HalfIntegral.Abstract.ThetaInstance
import Mathlib.Analysis.Complex.Basic
import TauCeti.NumberTheory.ModularForms.SturmBound

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup ModularForm

local notation "ℍ" => UpperHalfPlane

/-- A cusp form is a modular form. -/
theorem isHalfIntModularForm_of_mem_cuspForms {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)} {f : ℍ → ℂ}
    (hf : f ∈ thetaMultiplierSystem.cuspForms k N χ) : IsHalfIntModularForm k N χ f :=
  ⟨hf.holo, hf.transforms, fun γ ↦ (hf.zero_at_cusps γ).boundedAtFilter⟩

/-- $\theta \in M_{1/2}(4N, 1)$ for every $N$. -/
theorem theta_isHalfIntModularForm_level (N : ℕ) :
    IsHalfIntModularForm 0 N 1 (fun τ : ℍ ↦ theta τ) := by
  have h := theta_isHalfIntModularForm'
  refine ⟨h.holo, fun γ hγ τ ↦ ?_, h.bdd_at_cusps⟩
  have h1 := h.transforms γ (by simpa using Gamma0_mul_le N hγ) τ
  rw [MulChar.one_apply (isUnit_d_of_mem_Gamma0 hγ)]
  simpa [MulChar.one_apply (isUnit_d_of_mem_Gamma0 (Gamma0_mul_le N hγ))] using h1

/-- **Multiplication by $\theta$**, linear and injective into $M_{k+1}(\Gamma_1(4N))$. -/
noncomputable def mulTheta (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) :
    thetaMultiplierSystem.cuspForms k N χ →ₗ[ℂ] ModularForm (Gamma1 (4 * N)) ((k + 0 + 1 : ℕ) : ℤ) where
  toFun f := halfIntMul (isHalfIntModularForm_of_mem_cuspForms f.2) (theta_isHalfIntModularForm_level N)
  map_add' f g := by ext τ; exact add_mul _ _ _
  map_smul' c f := by ext τ; exact mul_assoc c _ _

theorem mulTheta_injective (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) :
    Function.Injective (mulTheta k N χ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have hz : ∀ τ : ℍ, f.1 τ * theta τ = 0 := fun τ ↦ congrArg (fun F : ModularForm _ _ ↦ F τ) hf
  have hf0 : ∀ τ : ℍ, 1 < τ.im → f.1 τ = 0 := fun τ hτ ↦
    (mul_eq_zero.mp (hz τ)).resolve_right (theta_ne_zero_of_one_lt_im hτ)
  have hhol : DifferentiableOn ℂ (f.1 ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp f.2.holo
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hana := hhol.analyticOnNhd hU
  have hconn : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  have hz0 : (2 * Complex.I) ∈ {z : ℂ | 0 < z.im} := by simp
  have hev : (f.1 ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds (2 * Complex.I)] 0 := by
    have : {z : ℂ | 1 < z.im} ∈ nhds (2 * Complex.I) :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by simp)
    filter_upwards [this] with z hz
    have hz' : 0 < z.im := lt_trans one_pos hz
    simp only [Function.comp_apply, Pi.zero_apply]
    have := hf0 (UpperHalfPlane.ofComplex z) (by rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz']; simpa using hz)
    exact this
  have h0 := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz0 hev
  apply Subtype.ext
  funext τ
  have := h0 τ.im_pos
  simpa using this

/-- **$S_{k+1/2}(4N,\chi)$ is finite-dimensional** for the theta multiplier. -/
instance finiteDimensional_thetaCuspForms (k N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ (4 * N)) :
    FiniteDimensional ℂ (thetaMultiplierSystem.cuspForms k N χ) :=
  Module.Finite.of_injective (mulTheta k N χ) (mulTheta_injective k N χ)

/-- **Kohnen's plus space is finite-dimensional.** -/
instance finiteDimensional_plusSpace (k : ℕ) : FiniteDimensional ℂ (PlusSpace k) :=
  Module.Finite.of_injective (Submodule.inclusion (thetaMultiplierSystem.plusCuspForms_le k 1 1))
    (Submodule.inclusion_injective _)

end ModularFormsKB.HalfIntegral
