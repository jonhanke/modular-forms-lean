import ModularFormsKB.Elliptic.HasNewform
import TauCeti.NumberTheory.ModularForms.Petersson.FiniteIndex
import TauCeti.Analysis.SpecialFunctions.Elliptic.Period.Lattice
import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# Zagier's modular degree formula, as a statement

Let $E$ have the newform $f$ of level $N$ and let $\varphi : X_0(N) \to E$ be a modular parametrization with
$\varphi^*\omega = c \cdot 2\pi i f(\tau)\,d\tau$, $\omega$ the invariant differential of the given model of $E$ and
$c$ the Manin constant. Zagier (1985, §2 [unverified]) writes the degree as
$$4\pi^2c^2\,\|f\|^2 = \deg\varphi\cdot\operatorname{vol}(\mathbb C/\Lambda),\qquad
\|f\|^2 = \int_{\Gamma_0(N)\backslash\mathbb H}|f(\tau)|^2\,dx\,dy,$$
$\Lambda$ the period lattice of $\omega$.

No library has the curve $X_0(N)$ over $\mathbb Q$ with its map to $E$, so the parametrization enters analytically
(`ModularParametrization`):
- a holomorphic $\Phi : \mathbb H \to \mathbb C$ with $\Phi' = c\cdot 2\pi i f$ (the lift of $\varphi$ through
  $\mathbb C \to \mathbb C/\Lambda \cong E(\mathbb C)$);
- $\Phi(\gamma\tau) - \Phi(\tau) \in \Lambda$ for $\gamma \in \Gamma_0(N)$;
- the degree: for almost every $w \in \mathbb C$, the number of points of the open fundamental domain of $\Gamma_0(N)$
  (the translates $q^{-1}\mathcal F^\circ$ over the cosets $q$ of $\Gamma_0(N)$ in $\mathrm{SL}_2(\mathbb Z)$) with
  $\Phi \equiv w \bmod \Lambda$.

$\Lambda$ is Tau Ceti's `WeierstrassCurve.periodLattice` of $E$ over $\mathbb C$ (the periods of
$dx/(2y + a_1x + a_3)$), its covolume Mathlib's `ZLattice.covolume`, and $\|f\|^2$ is Tau Ceti's Petersson product on
$\Gamma_1(N)$ (`CuspForm.peterssonInnerCosets`, the integral of $|f|^2y^2\,d\mu$ over $\pm\Gamma_1(N)\backslash\mathbb H$)
divided by the index $[\Gamma_0(N) : \pm\Gamma_1(N)]$ (`peterssonNormSqGamma0`).

- `ZagierDegreeFormula` (named statement): the formula for every such parametrization. Given the analytic data it
  is the area formula for $\Phi$ on a fundamental domain, so it is elementary; it is stated here, not proved (LE
  recorded). The arithmetic content, the existence of $\varphi$ with its Manin constant, is the input
  `EichlerShimuraCurve`/`ModularityTheorem` side and is not stated here.

The Petersson norm as $L(\operatorname{Sym}^2 f, 2)$ is not formalized here; the norm here is the
Petersson integral itself.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Complex MeasureTheory
open scoped MatrixGroups Real

namespace ModularFormsKB.Elliptic

open HeckeRing.GL2

/-- The period lattice $\Lambda_E \subset \mathbb C$ of the invariant differential of the model $E$ over $\mathbb Q$
(Tau Ceti's `periodLattice` of $E \otimes \mathbb C$). -/
noncomputable def periodLatticeQ (E : WeierstrassCurve ℚ) [E.IsElliptic] : Submodule ℤ ℂ :=
  (E.baseChange ℂ).periodLattice

/-- The Petersson norm $\|f\|^2 = \int_{\Gamma_0(N)\backslash\mathbb H}|f|^2\,dx\,dy$ of a form on $\Gamma_1(N)$: Tau
Ceti's coset product over $\pm\Gamma_1(N)$ divided by the index of $\pm\Gamma_1(N)$ in $\Gamma_0(N)$. -/
noncomputable def peterssonNormSqGamma0 {N : ℕ} [NeZero N] (f : Newform N 2) : ℝ :=
  (CuspForm.peterssonInnerCosets f.toCuspForm f.toCuspForm).re / ((Gamma1 N).withCenter.relIndex (Gamma0 N) : ℝ)

/-- **An analytic modular parametrization** of $E$ by the newform $f$ of level $N$, with Manin constant $c$ and
degree $d$: $\Phi' = c\cdot 2\pi i f$, $\Phi$ is $\Gamma_0(N)$-equivariant modulo the period lattice, and almost every
point of $\mathbb C/\Lambda$ has exactly $d$ preimages in the open fundamental domain of $\Gamma_0(N)$. Data, not a
cited result. -/
structure ModularParametrization (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2) where
  /-- The Manin constant $c$. -/
  manin : ℚ
  manin_ne_zero : manin ≠ 0
  /-- The lift $\Phi : \mathbb H \to \mathbb C$ of the parametrization. -/
  Φ : ℍ → ℂ
  hasDerivAt : ∀ τ : ℍ, HasDerivAt (fun z : ℂ ↦ Φ (ofComplex z)) ((manin : ℂ) * (2 * π * Complex.I) * f.toCuspForm τ) τ
  periods_mem : ∀ γ ∈ Gamma0 N, ∀ τ : ℍ, Φ (γ • τ) - Φ τ ∈ periodLatticeQ E
  /-- The degree $d$ of the parametrization. -/
  degree : ℕ
  degree_spec : ∀ᵐ w : ℂ, Nat.card {p : (SL(2, ℤ) ⧸ Gamma0 N) × ModularGroup.fdo //
    Φ (p.1.out⁻¹ • (p.2 : ℍ)) - w ∈ periodLatticeQ E} = degree

/-- **Zagier's modular degree formula** (row 26; Zagier 1985 [unverified]), as a named statement:
$4\pi^2c^2\|f\|^2 = \deg\varphi\cdot\operatorname{covol}(\Lambda_E)$ for every analytic modular parametrization. -/
@[kb "zagier1985" "§2, the degree of a modular parametrization: 4π²c²‖f‖² = deg φ · vol(ℂ/Λ) [unverified]"]
structure ZagierDegreeFormula : Prop where
  formula : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2), HasNewform E N f →
    ∀ P : ModularParametrization E N f,
      4 * π ^ 2 * (P.manin : ℝ) ^ 2 * peterssonNormSqGamma0 f =
        P.degree * ZLattice.covolume (periodLatticeQ E)

end ModularFormsKB.Elliptic
