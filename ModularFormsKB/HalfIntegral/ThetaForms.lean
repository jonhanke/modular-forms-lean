/-
# $\theta \in M_{1/2}(4, 1)$ and the powers $\theta^n$

Assembles the transformation law (`theta_transformationLaw`), the cusp bounds
(`theta_cusp_bdd_of_bound` with `norm_theta_le`), and the product and power constructions of `Products.lean`:
* $\theta \in M_{1/2}(4, 1)$ (`theta_mem_halfIntModularForms`);
* $\theta^{2k+1} \in M_{k+1/2}(4, 1)$ (`theta_pow_odd_mem`). With Shimura's multiplier $j^{2k+1}$ in the law, the
  character of an odd power is trivial;
* $\theta^{2m}(\gamma\tau) = \chi_{-4}(d)^m (c\tau+d)^m\,\theta^{2m}(\tau)$ on $\Gamma_0(4)$ (`theta_pow_even_transforms`),
  and $\theta^{2m}$, $m \ge 1$, is a Mathlib `ModularForm` of weight $m$ on $\Gamma_1(4)$ (`thetaPowEven`).

So $\theta^n$ has weight $n/2$ on $\Gamma_0(4)$, with character $\chi_{-4}^{n/2}$ for even $n$, and trivial character
(relative to $j^n$) for odd $n$.
-/
import ModularFormsKB.HalfIntegral.Products
import ModularFormsKB.HalfIntegral.Cusps
import ModularFormsKB.HalfIntegral.ThetaBound

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup UpperHalfPlane
open scoped ModularForm

/-- **$\theta \in M_{1/2}(4, 1)$**: holomorphic on $\mathbb H$, $\theta(\gamma z) = j(\gamma,z)\theta(z)$ on $\Gamma_0(4)$, and bounded
at every cusp (Shimura 1973 `shimura1973`, §1). -/
@[kb "shimura1973" "theta is a modular form of weight 1/2 on Gamma0(4) [unverified]"]
theorem theta_isHalfIntModularForm' : IsHalfIntModularForm 0 1 1 (fun τ : ℍ ↦ theta τ) :=
  theta_isHalfIntModularForm theta_transformationLaw (theta_cusp_bdd_of_bound norm_theta_le)

/-- $\theta$ as an element of the submodule $M_{1/2}(4,1)$. -/
theorem theta_mem_halfIntModularForms : (fun τ : ℍ ↦ theta τ) ∈ halfIntModularForms 0 1 1 :=
  theta_isHalfIntModularForm'

/-- **$\theta^{2k+1} \in M_{k+1/2}(4, 1)$.** -/
theorem theta_pow_odd_mem (k : ℕ) :
    (fun τ : ℍ ↦ theta τ) ^ (2 * k + 1) ∈ halfIntModularForms k 1 1 :=
  theta_isHalfIntModularForm'.pow_odd k

/-- **Even powers:** $\theta(\gamma\tau)^{2m} = \chi_{-4}(d)^m (c\tau+d)^m\,\theta(\tau)^{2m}$ for $\gamma \in \Gamma_0(4)$. -/
theorem theta_pow_even_transforms (m : ℕ) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (τ : ℍ) :
    theta ↑(γ • τ) ^ (2 * m) =
      (ZMod.χ₄ (γ 1 1 : ZMod 4) : ℂ) ^ m * ((γ 1 0 : ℂ) * τ + γ 1 1) ^ m * theta τ ^ (2 * m) := by
  rw [theta_transformationLaw γ hγ τ, mul_pow, pow_mul, thetaMult_sq hγ, mul_pow]

/-- **$\theta^{2m+2}$ as a modular form of weight $m+1$ on $\Gamma_1(4)$** (Mathlib's `ModularForm`), the product
$\theta^{2m+1} \cdot \theta$. -/
noncomputable def thetaPowEven (m : ℕ) : ModularForm (Gamma1 (4 * 1)) ((m + 0 + 1 : ℕ) : ℤ) :=
  halfIntMul (theta_isHalfIntModularForm'.pow_odd m) theta_isHalfIntModularForm'

theorem coe_thetaPowEven (m : ℕ) :
    (thetaPowEven m : ℍ → ℂ) = (fun τ : ℍ ↦ theta τ) ^ (2 * m + 2) := by
  rw [thetaPowEven, coe_halfIntMul, ← pow_succ]

end ModularFormsKB.HalfIntegral
