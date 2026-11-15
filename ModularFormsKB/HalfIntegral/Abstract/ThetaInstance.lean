/-
# The theta multiplier as an abstract multiplier system

`ModularFormsKB/HalfIntegral/Abstract/Multiplier.lean`
works over an abstract `MultiplierSystem`; `ModularFormsKB/HalfIntegral/Forms.lean` defines the spaces with the concrete theta
multiplier `thetaMult` (Shimura 1973 `shimura1973`, §1 [unverified]). This file
* builds the instance `thetaMultiplierSystem` with $j(\gamma,\tau) = $ `thetaMult γ τ`, from the cocycle relation
  (`thetaMult_mul`), the absolute value (`norm_thetaMult`), holomorphy (`thetaMult_differentiableOn`) and
  $j(T,\tau) = 1$;
* proves that the abstract spaces for this instance are the concrete ones: `thetaMultiplierSystem_modularForms` and
  `thetaMultiplierSystem_cuspForms` (equalities of submodules);
* states $\theta \in M_{1/2}(4, 1)$ in the abstract space (`theta_mem_thetaMultiplierSystem_modularForms`).

So every named input of `Abstract/Shimura.lean`, `Abstract/Kohnen.lean` and `Abstract/Waldspurger.lean` can be specialized
to `thetaMultiplierSystem`, and then speaks about `halfIntModularForms` and `halfIntCuspForms`.

**Index shift.** Matrix entries are 0-based: $c = \gamma_{1,0}$, $d = \gamma_{1,1}$.
-/
import ModularFormsKB.HalfIntegral.Abstract.Multiplier
import ModularFormsKB.HalfIntegral.ThetaForms
import ModularFormsKB.HalfIntegral.Cocycle

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup
open scoped Manifold

local notation "ℍ" => UpperHalfPlane

/-- $j(T, z) = 1$ for the theta multiplier. -/
lemma thetaMult_T (z : ℂ) : thetaMult ModularGroup.T z = 1 := by
  have h10 : ModularGroup.T 1 0 = 0 := by simp [ModularGroup.T]
  have h11 : ModularGroup.T 1 1 = 1 := by simp [ModularGroup.T]
  rw [thetaMult, h10, h11, thetaMultCD_zero_one]

/-- **The theta multiplier as an abstract multiplier system** on $\Gamma_0(4)$:
$j(\gamma,\tau) = \varepsilon_d^{-1}\left(\tfrac cd\right)(c\tau+d)^{1/2}$ (`thetaMult`). -/
noncomputable def thetaMultiplierSystem : MultiplierSystem where
  j γ τ := thetaMult γ τ
  cocycle γ₁ h₁ γ₂ h₂ τ := thetaMult_mul h₁ h₂ τ
  ne_zero γ hγ τ := by
    intro h
    have h1 := norm_thetaMult hγ (τ : ℂ)
    rw [h, norm_zero] at h1
    have h2 : ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ≠ 0 := norm_ne_zero_iff.mpr (cuspDenom_ne_zero γ τ)
    have h3 : (0 : ℝ) < ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h2)) _
    linarith
  holo γ _ := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine (thetaMult_differentiableOn γ).congr fun z hz => ?_
    simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  norm_sq γ hγ τ := by
    rw [norm_thetaMult hγ, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  j_T τ := thetaMult_T τ

@[simp] lemma thetaMultiplierSystem_j (γ : SL(2, ℤ)) (τ : ℍ) :
    thetaMultiplierSystem.j γ τ = thetaMult γ τ := rfl

/-- The abstract transformation law for the theta multiplier system is `HalfIntTransforms`. -/
theorem thetaMultiplierSystem_transforms_iff (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (f : ℍ → ℂ) :
    thetaMultiplierSystem.Transforms k N χ f ↔ HalfIntTransforms k N χ f := Iff.rfl

/-- **Comparison of modular forms:** for the theta multiplier system, the abstract $M_{k+1/2}(4N,\chi)$ condition is
`IsHalfIntModularForm` of `Forms.lean`. -/
theorem thetaMultiplierSystem_isModularForm_iff (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (f : ℍ → ℂ) :
    thetaMultiplierSystem.IsModularForm k N χ f ↔ IsHalfIntModularForm k N χ f :=
  ⟨fun h => ⟨h.holo, h.transforms, h.bdd_at_cusps⟩, fun h => ⟨h.holo, h.transforms, h.bdd_at_cusps⟩⟩

/-- **Comparison of cusp forms:** for the theta multiplier system, the abstract $S_{k+1/2}(4N,\chi)$ condition is
`IsHalfIntCuspForm` of `Forms.lean`. -/
theorem thetaMultiplierSystem_isCuspForm_iff (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (f : ℍ → ℂ) :
    thetaMultiplierSystem.IsCuspForm k N χ f ↔ IsHalfIntCuspForm k N χ f :=
  ⟨fun h => ⟨h.holo, h.transforms, h.zero_at_cusps⟩, fun h => ⟨h.holo, h.transforms, h.zero_at_cusps⟩⟩

/-- **The abstract $M_{k+1/2}(4N,\chi)$ for the theta multiplier is `halfIntModularForms`.** -/
@[kb "shimura1973" "the abstract M_{k+1/2}(4N, χ) for the theta multiplier is the concrete space [unverified]"]
theorem thetaMultiplierSystem_modularForms (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) :
    thetaMultiplierSystem.modularForms k N χ = halfIntModularForms k N χ :=
  Submodule.ext fun f => thetaMultiplierSystem_isModularForm_iff k N χ f

/-- **The abstract $S_{k+1/2}(4N,\chi)$ for the theta multiplier is `halfIntCuspForms`.** -/
@[kb "shimura1973" "the abstract S_{k+1/2}(4N, χ) for the theta multiplier is the concrete space [unverified]"]
theorem thetaMultiplierSystem_cuspForms (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) :
    thetaMultiplierSystem.cuspForms k N χ = halfIntCuspForms k N χ :=
  Submodule.ext fun f => thetaMultiplierSystem_isCuspForm_iff k N χ f

/-- **$\theta \in M_{1/2}(4, 1)$ in the abstract space** of the theta multiplier system (Shimura 1973 `shimura1973`, §1). -/
@[kb "shimura1973" "theta lies in the abstract M_{1/2}(4) of the theta multiplier system [unverified]"]
theorem theta_mem_thetaMultiplierSystem_modularForms :
    (fun τ : ℍ ↦ theta τ) ∈ thetaMultiplierSystem.modularForms 0 1 1 := by
  rw [thetaMultiplierSystem_modularForms]
  exact theta_mem_halfIntModularForms

end ModularFormsKB.HalfIntegral
