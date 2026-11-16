/-
# Normalization check: $\theta$ is fixed by $W(4)$

With the normalization of `kohnenW4`
($(g|W(4))(\tau) = (-2i\tau)^{-(k+1/2)}g(-1/4\tau)$), the theta series $\theta$ of weight $\tfrac12$ ($k = 0$) satisfies
$\theta|W(4) = \theta$; this is the Fricke law `theta_fricke`. Together with $\theta|U(4) = \theta$ (the coefficients
$r(n)$ of $\theta$ satisfy $r(4n) = r(n)$) it gives the eigenvalue $\alpha_0 = 1$ of `kohnenAlpha`.
-/
import ModularFormsKB.HalfIntegral.Abstract.KohnenProjection
import ModularFormsKB.HalfIntegral.Theta

namespace ModularFormsKB.HalfIntegral

open Complex

local notation "ℍ" => UpperHalfPlane

/-- **$\theta|W(4) = \theta$** in weight $\tfrac12$. -/
theorem kohnenW4_theta : kohnenW4 0 (fun τ : ℍ ↦ theta (τ : ℂ)) = fun τ : ℍ ↦ theta (τ : ℂ) := by
  funext τ
  simp only [kohnenW4, coe_frickePt, CharP.cast_eq_zero, zero_add]
  rw [theta_fricke _ τ.im_pos, ← mul_assoc, Complex.cpow_neg, inv_mul_cancel₀, one_mul]
  exact Complex.cpow_ne_zero_iff.2 (Or.inl (mul_ne_zero (by simp) τ.ne_zero))

theorem kohnenAlpha_zero : kohnenAlpha 0 = 1 := by simp [kohnenAlpha]

end ModularFormsKB.HalfIntegral
