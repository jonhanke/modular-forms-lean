/-
# Tunnell's forms as products of theta series (definitions)

With $\theta(\tau) = \sum_{n \in \mathbb Z} q^{n^2}$ (`HalfIntegral.theta`), put
$$\theta_{\mathrm{odd}}(\tau) = \theta(\tau) - \theta(4\tau) = \sum_{x \text{ odd}} q^{x^2},\qquad
\phi_8(\tau) = 2\theta(32\tau) - \theta(8\tau) = \sum_{z \in \mathbb Z} (-1)^z q^{8z^2}.$$
Then Tunnell's forms (Koblitz 1984, Ch. IV §4 `koblitz1984` [unverified]: $\eta(8\tau)\eta(16\tau)\theta(2\tau)$ and
$\eta(8\tau)\eta(16\tau)\theta(4\tau)$) are
$$g_{\mathrm{odd}} = \tfrac12\,\theta_{\mathrm{odd}}(\tau)\,\theta(2\tau)\,\phi_8(\tau),\qquad
g_{\mathrm{even}} = \tfrac12\,\theta_{\mathrm{odd}}(\tau)\,\theta(4\tau)\,\phi_8(\tau),$$
since for odd $m$ the coefficient of $q^m$ is
$\tfrac12(\#\{z \text{ even}\} - \#\{z \text{ odd}\}) = B(m) - \tfrac12A(m)$ (resp. $D(2m) - \tfrac12C(2m)$), and $0$
for even $m$ ($x$ is odd).

This file only defines the products; `TunnellThetaQ.lean` proves the $q$-series identities, `TunnellThetaLaw.lean`
the transformation law on $\Gamma_0(128)$ (`thetaTwist_law` for each factor), and `TunnellThetaCusp.lean` the
vanishing at every cusp: $\theta_{\mathrm{odd}}$ vanishes at the cusps $a/c$ with $16 \mid c$, $\phi_8$ at the others.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.TunnellAux
import ModularFormsKB.HalfIntegral.Abstract.ThetaInstance
import ModularFormsKB.Miyake.Sec4_9.Spherical.UnaryLaw

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open Complex
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- $\theta_{\mathrm{odd}}(\tau) = \theta(\tau) - \theta(4\tau) = \sum_{x \text{ odd}} q^{x^2}$. -/
noncomputable def thetaOddPart (τ : ℍ) : ℂ := HalfIntegral.theta τ - HalfIntegral.theta (4 * τ)

/-- $\phi_8(\tau) = 2\theta(32\tau) - \theta(8\tau) = \sum_z (-1)^z q^{8z^2}$. -/
noncomputable def thetaSignPart (τ : ℍ) : ℂ := 2 * HalfIntegral.theta (32 * τ) - HalfIntegral.theta (8 * τ)

/-- **Tunnell's odd form as a product of theta series**: $\tfrac12\theta_{\mathrm{odd}}(\tau)\theta(2\tau)\phi_8(\tau)$. -/
noncomputable def tunnellOddTheta (τ : ℍ) : ℂ :=
  thetaOddPart τ * HalfIntegral.theta (2 * τ) * thetaSignPart τ / 2

/-- **Tunnell's even form as a product of theta series**: $\tfrac12\theta_{\mathrm{odd}}(\tau)\theta(4\tau)\phi_8(\tau)$. -/
noncomputable def tunnellEvenTheta (τ : ℍ) : ℂ :=
  thetaOddPart τ * HalfIntegral.theta (4 * τ) * thetaSignPart τ / 2

/-- $\theta(t z)$ is Shimura's twisted theta series for the trivial character modulo $1$, so `thetaTwist_law` gives
its law on $\Gamma_0(4t)$. -/
theorem theta_mul_eq_thetaTwist (t : ℕ) (z : ℂ) :
    HalfIntegral.theta (t * z) = HalfIntegral.thetaTwist (1 : DirichletCharacter ℂ 1) t z := by
  have hp : HalfIntegral.charParity (1 : DirichletCharacter ℂ 1) = 0 := by
    simp [HalfIntegral.charParity]
  rw [HalfIntegral.theta_eq_tsum, HalfIntegral.thetaTwist, hp]
  refine tsum_congr fun n ↦ ?_
  simp only [inv_one, MulChar.one_apply (isUnit_of_subsingleton _), pow_zero, one_mul]
  congr 1
  ring

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
