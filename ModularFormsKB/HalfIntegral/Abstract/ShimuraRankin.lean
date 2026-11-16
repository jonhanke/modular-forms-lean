/-
# Shimura's twisted functional equations by Rankin's method: definitions and named inputs

Shimura 1973 `shimura1973` (proof of the
Main Theorem [unverified]) obtains the functional equations of `ShimuraTwistedFE` from the Rankin-type integral of
$f \in S_{k+1/2}(4N,\chi)$ against a twisted theta series $\theta_{\psi,t}$ and a nonholomorphic Eisenstein series. This
file holds the objects and the four named inputs:

* (a) `thetaTwist ψ t` $= \sum_{n\in\mathbb Z}\bar\psi(n)n^\nu e(tn^2z)$, $\nu$ = `charParity ψ`, and its law
  `ThetaTwistLaw M` on $\Gamma_0(4tr^2)$ (Shimura 1973, Prop. 2.2 [unverified]; numerically checked,
  `scripts/HalfIntegral/check_theta_twist.py`);
* (b) the Eisenstein series `eisensteinLattice L λ ω` (a lattice sum over $L\mathbb Z\times\mathbb Z$), its dual
  `eisensteinDual` (Gauss sums `gaussAt` on the first coordinate) and Hecke's functional equation `EisensteinFE`
  (numerically checked at the level of the theta identity, `scripts/HalfIntegral/check_eisenstein_poisson.py`);
* (c) the unfolding principle `RankinUnfolding` (integrals over $\Gamma_0(L)\backslash\mathbb H$ are sums over right coset
  representatives of integrals over `ModularGroup.fd`, as in `peterssonReps`);
* (d) the dual unfolding identity `ShimuraDualUnfolding`, the Shimura-specific remainder: an identity of absolutely
  convergent expressions for $\operatorname{Re}w$ large.

The Rankin data for a twisting character $\psi$ mod $r$: weight $\lambda = k - \nu$, level `rankinLevel N t r` $= 16Ntr^2$,
character `rankinChar k N χ t ψ` $= \chi\kappa\psi$ with $\kappa$ Tau Ceti's Kronecker character of $4(-1)^kt$, kernel
`rankinKernel k ψ t f` $= f\,\overline{\theta_{\psi,t}}\,y^{(k+\nu+1)/2}$, and the variable change $s = (w-k+1)/2$
(`rankinS`).

**Index shift.** Matrix entries are 0-based: $c = \gamma_{1,0}$, $d = \gamma_{1,1}$.
-/
import ModularFormsKB.HalfIntegral.Abstract.ShimuraWeil
import ModularFormsKB.HalfIntegral.Theta
import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.NumberTheory.Modular

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup MeasureTheory Set
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-! ### (a) The twisted theta series -/

/-- **The parity of a character:** $\nu = 0$ if $\psi(-1) = 1$, else $\nu = 1$. -/
noncomputable def charParity {r : ℕ} (ψ : DirichletCharacter ℂ r) : ℕ :=
  if ψ (-1) = 1 then 0 else 1

/-- **The twisted theta series** $\theta_{\psi,t}(z) = \sum_{n\in\mathbb Z}\bar\psi(n)\,n^\nu e(tn^2z)$ of weight
$\tfrac12+\nu$ (Shimura 1973 `shimura1973`, §2 [unverified]). -/
noncomputable def thetaTwist {r : ℕ} (ψ : DirichletCharacter ℂ r) (t : ℕ) (z : ℂ) : ℂ :=
  ∑' n : ℤ, ψ⁻¹ (n : ZMod r) * (n : ℂ) ^ charParity ψ * cexp (2 * π * I * t * (n : ℂ) ^ 2 * z)

/-- **The transformation law of the twisted theta series, for the multiplier `M.j`** (Shimura 1973 `shimura1973`,
Prop. 2.2): for every $r \ge 1$ (an earlier restriction to $r = 1$ or an odd prime has been removed), $t \ge 1$
and $\gamma \in \Gamma_0(4tr^2)$,
$\theta_{\psi,t}(\gamma z) = \bar\psi(d)\,(t/|d|)\,(cz+d)^\nu\,j(\gamma,z)\,\theta_{\psi,t}(z)$; and the multiplier squares to the
weight-one factor, $j(\gamma,z)^2 = (\tfrac{-1}{d})(cz+d)$ on $\Gamma_0(4)$. For the theta multiplier both fields are
proved: `HalfIntegral.thetaTwistLaw_thetaMultiplierSystem` (`Miyake/Sec4_9/Spherical/UnaryLaw.lean`). In
Shimura's form the factor is $(\tfrac{-1}{d})^\nu j^{2\nu+1}$ with his sign convention for $d < 0$. For other `M` the
structure is an assumption about `M`. -/
@[kb "shimura1973" "Prop. 2.2: the twisted theta series theta(z; psi) of weight 1/2 + nu on Gamma0(4 r^2), with t [unverified]"]
structure ThetaTwistLaw (M : MultiplierSystem) : Prop where
  law : ∀ (r : ℕ) (ψ : DirichletCharacter ℂ r) (t : ℕ), 1 ≤ t → 1 ≤ r →
    ∀ γ ∈ Gamma0 (4 * t * r ^ 2), ∀ τ : ℍ,
      thetaTwist ψ t ((γ • τ : ℍ) : ℂ) = ψ⁻¹ (γ 1 1 : ZMod r) * (jacobiSym t (γ 1 1).natAbs : ℂ) *
        ((γ 1 0 : ℂ) * τ + γ 1 1) ^ charParity ψ * M.j γ τ * thetaTwist ψ t τ
  j_sq : ∀ γ ∈ Gamma0 4, ∀ τ : ℍ,
    M.j γ τ ^ 2 = (ZMod.χ₄ (γ 1 1 : ZMod 4) : ℂ) * ((γ 1 0 : ℂ) * τ + γ 1 1)

/-! ### (b) The Eisenstein series of weight `λ` and its functional equation -/

/-- The summand $v^\lambda|v|^{-\lambda-2s}$ of the Eisenstein series. -/
noncomputable def eisTerm (lam : ℕ) (s v : ℂ) : ℂ :=
  v ^ lam * (((‖v‖ : ℝ) : ℂ) ^ (-(lam : ℂ) - 2 * s))

/-- **The Eisenstein series of weight $\lambda$, level $L$, character $\omega$** (a lattice sum, Hecke's normalization):
$E(z,s) = y^s\sum_{(c,d)\in L\mathbb Z\times\mathbb Z}\omega(d)(cz+d)^\lambda|cz+d|^{-\lambda-2s}$, absolutely convergent for
$\operatorname{Re}s > 1$ (the term $(0,0)$ vanishes for $\lambda \ge 1$). -/
noncomputable def eisensteinLattice (L lam : ℕ) (ω : DirichletCharacter ℂ L) (z : ℍ) (s : ℂ) : ℂ :=
  ((z.im : ℂ) ^ s) * ∑' p : ℤ × ℤ, ω (p.2 : ZMod L) * eisTerm lam s ((L : ℂ) * p.1 * z + p.2)

/-- **The Gauss sum at $m$:** $G(\omega,m) = \sum_{a=0}^{L-1}\omega(a)e(am/L)$. -/
noncomputable def gaussAt (L : ℕ) (ω : DirichletCharacter ℂ L) (m : ℤ) : ℂ :=
  ∑ a ∈ Finset.range L, ω a * cexp (2 * π * I * a * m / L)

/-- **The dual Eisenstein series** $\check E(z,s) = y^s\sum_{(m,n)\in\mathbb Z^2}G(\omega,-m)(mz+n)^\lambda|mz+n|^{-\lambda-2s}$
(the Poisson dual of `eisensteinLattice`; for primitive $\omega$ it is $\omega(-1)\tau(\omega)$ times the series at the cusp
$0$ with character $\bar\omega$, in general a combination of series at several cusps). -/
noncomputable def eisensteinDual (L lam : ℕ) (ω : DirichletCharacter ℂ L) (z : ℍ) (s : ℂ) : ℂ :=
  ((z.im : ℂ) ^ s) * ∑' p : ℤ × ℤ, gaussAt L ω (-p.1) * eisTerm lam s ((p.1 : ℂ) * z + p.2)

/-- **Hecke's functional equation of the Eisenstein series** (Hecke 1927 `hecke1927`; Miyake 1989 `miyake1989`, §7.2
[unverified]). For $L \ge 2$, $\lambda \ge 1$ and a character $\omega$ mod $L$ with $\omega(-1) = (-1)^\lambda$ there is
$E^*(z,s)$, entire in $s$, continuous in $z$, with
$E^*(z,s) = L^s\pi^{-s}\Gamma(s+\tfrac\lambda2)E(z,s)$ for $\operatorname{Re}s > 1$,
$E^*(z,s) = L^{-s}\pi^{-(1-s)}\Gamma(1-s+\tfrac\lambda2)\check E(z,1-s)$ for $\operatorname{Re}s < 0$, and
$|E^*(z,s)| \le B(y^A+y^{-A})$ on every vertical strip. Proof: Mellin transform of the lattice theta identity
$\Theta(u) = (L^2y)^{-1}(Ly)^{-\lambda}u^{-1-\lambda}\check\Theta(1/(L^2y^2u))$ (Poisson summation in $\mathbb R^2$ for
$v^\lambda e^{-\pi u|v|^2}$), with no constant terms since $\lambda \ge 1$. Valid for imprimitive $\omega$. -/
@[kb "hecke1927" "functional equation of the lattice Eisenstein series with a character, by Poisson summation [unverified]"]
structure EisensteinFE : Prop where
  fe : ∀ (L lam : ℕ) (ω : DirichletCharacter ℂ L), 2 ≤ L → 1 ≤ lam → ω (-1) = (-1) ^ lam →
    ∃ E : ℍ → ℂ → ℂ, (∀ z, Differentiable ℂ (E z)) ∧ (∀ s, Continuous fun z ↦ E z s) ∧
      (∀ z s, 1 < s.re →
        E z s = (L : ℂ) ^ s * (π : ℂ) ^ (-s) * Gamma (s + lam / 2) * eisensteinLattice L lam ω z s) ∧
      (∀ z s, s.re < 0 →
        E z s = (L : ℂ) ^ (-s) * (π : ℂ) ^ (-(1 - s)) * Gamma (1 - s + lam / 2) * eisensteinDual L lam ω z (1 - s)) ∧
      ∀ σ₁ σ₂ : ℝ, ∃ A B : ℝ, ∀ z s, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖E z s‖ ≤ B * (z.im ^ A + z.im ^ (-A))

/-! ### (c) Integrals over `Γ₀(L)\ℍ` and the unfolding principle -/

/-- **Right coset representatives** of $\Gamma_0(L)$ in $\mathrm{SL}_2(\mathbb Z)$: every $g$ lies in exactly one coset
$\Gamma_0(L)\gamma$, $\gamma$ in the list. -/
def IsGamma0Reps (L : ℕ) (R : List SL(2, ℤ)) : Prop :=
  ∀ g : SL(2, ℤ), ∃! i : Fin R.length, g * (R.get i)⁻¹ ∈ Gamma0 L

/-- **The integral over $\Gamma_0(L)\backslash\mathbb H$ through right coset representatives** $R$:
$\sum_{\gamma\in R}\int_{\mathcal F}h(\gamma\tau)\,d\mu(\tau)$, $\mathcal F$ = `ModularGroup.fd`, $d\mu = dx\,dy/y^2$. -/
noncomputable def repsIntegral (R : List SL(2, ℤ)) (h : ℍ → ℂ) : ℂ :=
  (R.map fun γ ↦ ∫ τ in ModularGroup.fd, h (γ • τ)).sum

/-- The point $x + iy$ of $\mathbb H$ for $y > 0$ (and $i$ otherwise). -/
noncomputable def stripPt (x y : ℝ) : ℍ :=
  if hy : 0 < y then ⟨(x : ℂ) + y * I, by simpa using hy⟩ else UpperHalfPlane.I

/-- **The strip integral** $\int_0^\infty\!\int_0^1 G(x+iy)\,y^{s-2}\,dx\,dy$ (the integral of $G\,y^s$ over
$\Gamma_\infty\backslash\mathbb H$ for $d\mu = dx\,dy/y^2$). -/
noncomputable def stripMellin (G : ℍ → ℂ) (s : ℂ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), (∫ x in (0 : ℝ)..1, G (stripPt x y)) * ((y : ℂ) ^ (s - 2))

/-- **The unitary weight-$\lambda$ law** $G(\gamma z) = \omega(d)\big(\tfrac{cz+d}{|cz+d|}\big)^\lambda G(z)$ on $\Gamma_0(L)$:
then $G\,E(\cdot,s)$ is $\Gamma_0(L)$-invariant. -/
def UnitaryLaw (L lam : ℕ) (ω : DirichletCharacter ℂ L) (G : ℍ → ℂ) : Prop :=
  ∀ γ ∈ Gamma0 L, ∀ τ : ℍ, G (γ • τ) = ω (γ 1 1 : ZMod L) *
    (((γ 1 0 : ℂ) * τ + γ 1 1) / ((‖(γ 1 0 : ℂ) * τ + γ 1 1‖ : ℝ) : ℂ)) ^ lam * G τ

/-- **The Rankin–Selberg unfolding principle** (Rankin 1939 `rankin1939`, Selberg 1940 `selberg1940` [unverified]): for
$L \ge 1$, right coset representatives $R$ of $\Gamma_0(L)$, a continuous $G$ with the unitary weight-$\lambda$ law and
$\int_0^\infty\!\int_0^1|G|\,y^{\sigma-2} < \infty$, $\sigma = \operatorname{Re}s > 1$:
$\sum_{\gamma\in R}\int_{\mathcal F}G(\gamma\tau)E(\gamma\tau,s)\,d\mu = 2L(2s,\omega)\int_0^\infty\!\int_0^1G\,y^{s-2}\,dx\,dy.$
The factor $2$ counts $\pm(c,d)$ and $L(2s,\omega)$ the common divisor of $(c,d)$; the rest is that the translates of
`ModularGroup.fd` by $\Gamma_\infty\backslash\mathrm{SL}_2(\mathbb Z)$ tile the strip up to measure zero, which is not
formalized (as for `PoincareUnfolding`). -/
@[kb "rankin1939" "the unfolding of a Petersson-type integral against an Eisenstein series [unverified]"]
structure RankinUnfolding : Prop where
  unfold : ∀ (L lam : ℕ) (ω : DirichletCharacter ℂ L) (R : List SL(2, ℤ)), 1 ≤ L → IsGamma0Reps L R →
    ∀ G : ℍ → ℂ, Continuous G → UnitaryLaw L lam ω G → ∀ s : ℂ, 1 < s.re →
      IntegrableOn (fun p : ℝ × ℝ ↦ ‖G (stripPt p.1 p.2)‖ * p.2 ^ (s.re - 2)) (Icc 0 1 ×ˢ Ioi 0) →
      repsIntegral R (fun τ ↦ G τ * eisensteinLattice L lam ω τ s) =
        2 * LSeries (fun n ↦ ω n) (2 * s) * stripMellin G s

/-! ### (d) The Rankin data and the dual unfolding identity -/

/-- The level $16Ntr^2$ of the Rankin integral. -/
def rankinLevel (N t r : ℕ) : ℕ := 16 * N * t * r ^ 2

/-- The Kronecker discriminant $4(-1)^kt$. -/
def rankinDisc (k t : ℕ) : ℤ := 4 * (-1) ^ k * t

theorem rankinDisc_mod_four (k t : ℕ) : rankinDisc k t ≡ 0 [ZMOD 4] ∨ rankinDisc k t ≡ 1 [ZMOD 4] := by
  left
  unfold rankinDisc
  exact (Int.modEq_zero_iff_dvd).2 ⟨(-1) ^ k * t, by ring⟩

theorem rankinDisc_ne_zero (k : ℕ) {t : ℕ} (ht : 1 ≤ t) : rankinDisc k t ≠ 0 := by
  unfold rankinDisc
  have : (t : ℤ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))) this

theorem rankinDisc_natAbs (k t : ℕ) : (rankinDisc k t).natAbs = 4 * t := by
  unfold rankinDisc
  rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow]
  simp

theorem four_dvd_rankinLevel (N t r : ℕ) : 4 * N ∣ rankinLevel N t r :=
  ⟨4 * t * r ^ 2, by unfold rankinLevel; ring⟩

theorem disc_dvd_rankinLevel (k N t r : ℕ) : (rankinDisc k t).natAbs ∣ rankinLevel N t r :=
  ⟨4 * N * r ^ 2, by rw [rankinDisc_natAbs]; unfold rankinLevel; ring⟩

theorem mod_dvd_rankinLevel (N t r : ℕ) : r ∣ rankinLevel N t r :=
  ⟨16 * N * t * r, by unfold rankinLevel; ring⟩

/-- **The character of the Rankin integral** $\omega = \chi\kappa\psi$ mod $16Ntr^2$, $\kappa$ the Kronecker character of
$4(-1)^kt$ (Tau Ceti's `kroneckerChar`); $\omega(n) = \psi(n)\chi_t(n)$ for $n \ge 1$. (For $t = 0$ the discriminant is $0$
and $\kappa$ is replaced by the trivial character; $t = 0$ is never used.) -/
noncomputable def rankinChar (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ) {r : ℕ}
    (ψ : DirichletCharacter ℂ r) : DirichletCharacter ℂ (rankinLevel N t r) :=
  DirichletCharacter.changeLevel (four_dvd_rankinLevel N t r) χ *
    (if h : rankinDisc k t = 0 then 1 else
      DirichletCharacter.changeLevel (disc_dvd_rankinLevel k N t r)
        (TauCeti.kroneckerChar ℂ (rankinDisc k t) (rankinDisc_mod_four k t) h)) *
    DirichletCharacter.changeLevel (mod_dvd_rankinLevel N t r) ψ

/-- **The Rankin kernel** $G_\psi(z) = f(z)\,\overline{\theta_{\psi,t}(z)}\,y^{(k+\nu+1)/2}$. -/
noncomputable def rankinKernel (k : ℕ) {r : ℕ} (ψ : DirichletCharacter ℂ r) (t : ℕ) (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  f z * (starRingEnd ℂ) (thetaTwist ψ t z) * ((z.im ^ (((k + charParity ψ + 1 : ℕ) : ℝ) / 2) : ℝ) : ℂ)

/-- The variable change $s = (w-k+1)/2$ between the Rankin integral and the Dirichlet series in $w$. -/
noncomputable def rankinS (k : ℕ) (w : ℂ) : ℂ := (w - k + 1) / 2

/-- **The Rankin integral** $\sum_{\gamma\in R}\int_{\mathcal F}G_\psi(\gamma\tau)\,E^*(\gamma\tau,s)\,d\mu$ for a given
completed Eisenstein series `E`. -/
noncomputable def rankinIntegral (k : ℕ) {r : ℕ} (ψ : DirichletCharacter ℂ r) (t : ℕ) (f : ℍ → ℂ)
    (R : List SL(2, ℤ)) (E : ℍ → ℂ → ℂ) (s : ℂ) : ℂ :=
  repsIntegral R fun τ ↦ rankinKernel k ψ t f τ * E τ s

/-- **The dual Rankin integral** $\sum_{\gamma\in R}\int_{\mathcal F}G_\psi(\gamma\tau)\,\check E(\gamma\tau,s)\,d\mu$
(absolutely convergent for $\operatorname{Re}s > 1$). -/
noncomputable def rankinDual (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ) {r : ℕ}
    (ψ : DirichletCharacter ℂ r) (f : ℍ → ℂ) (R : List SL(2, ℤ)) (s : ℂ) : ℂ :=
  repsIntegral R fun τ ↦ rankinKernel k ψ t f τ *
    eisensteinDual (rankinLevel N t r) (k - charParity ψ) (rankinChar k N χ t ψ) τ s

/-- **The normalizing factor** $\rho_\psi(w)$, an exponential in $w$: with $s = (w-k+1)/2$, $L = 16Ntr^2$,
$$\rho_\psi(w) = \frac{(2\pi/\sqrt{4Nr^2})^{-w}}{4\,L^s\pi^{-s}(4\pi t)^{-(w+\nu)/2}\,2^{1-w}\sqrt\pi},$$
so that $\rho_\psi(w)\cdot(\text{Rankin integral at }s) = (2\pi/\sqrt{4Nr^2})^{-w}\Gamma(w)D_\psi(w)$ for $\operatorname{Re}w$
large. -/
noncomputable def rankinRho (k N t : ℕ) {r : ℕ} (ψ : DirichletCharacter ℂ r) (w : ℂ) : ℂ :=
  (((2 * π / Real.sqrt (4 * N * r ^ 2 : ℕ) : ℝ) : ℂ) ^ (-w)) /
    (4 * ((rankinLevel N t r : ℂ) ^ rankinS k w) * ((π : ℂ) ^ (-rankinS k w)) *
      (((4 * π * t : ℝ) : ℂ) ^ (-(w + charParity ψ) / 2)) * ((2 : ℂ) ^ (1 - w)) * ((Real.sqrt π : ℝ) : ℂ))

/-- **The factor in front of the dual Rankin integral:** with $\tilde s = (k+1-w)/2$ (so $1-\tilde s = (w-k+1)/2$),
$\rho_\psi(2k-w)\,L^{-\tilde s}\pi^{-(1-\tilde s)}\Gamma(1-\tilde s+\tfrac\lambda2)$; it is what `EisensteinFE` puts in front
of $\check E$ when the Rankin integral is evaluated at $\tilde s$. -/
noncomputable def rankinDualFactor (k N t : ℕ) {r : ℕ} (ψ : DirichletCharacter ℂ r) (w : ℂ) : ℂ :=
  rankinRho k N t ψ (2 * k - w) * ((rankinLevel N t r : ℂ) ^ (-rankinS k (2 * k - w))) *
    ((π : ℂ) ^ (-(1 - rankinS k (2 * k - w)))) *
    Gamma (1 - rankinS k (2 * k - w) + ((k - charParity ψ : ℕ) : ℂ) / 2)

/-- **Shimura's dual unfolding identity** (Shimura 1973 `shimura1973`, proof of the Main Theorem [unverified]). For
$k \ge 2$, squarefree $t \ge 1$ and $f \in S_{k+1/2}(4N,\chi)$ with $q$-expansion $a$ there is $b$ of polynomial growth,
$b(0) = 0$, such that for $\psi = 1$ (modulo $1$) and for every primitive $\psi$ modulo an odd prime $m \nmid 4N$, for every
list $R$ of right coset representatives of $\Gamma_0(16Ntm^2)$ and $\operatorname{Re}w$ large,
$$\text{(`rankinDualFactor`)}\cdot\check{\mathcal R}_\psi\big(\tfrac{w-k+1}2\big) =
  i^{2k}C_\psi\,(2\pi/\sqrt{4Nm^2})^{-w}\Gamma(w)\sum_n\bar\psi(n)b(n)n^{-w},$$
$C_1 = 1$ and $C_\psi$ = `weilConstant (χ ^ 2) ψ`. Both sides converge absolutely; no continuation is involved. The standard
proof unfolds $\check E$ at the cusps where $G(\omega,-m) \ne 0$, using the expansions of $f$ and $\theta_{\psi,t}$ there;
$b$ is the coefficient sequence of $F|W_{4N}$, $F$ the lift. Given `EisensteinFE`, `RankinUnfolding`, `ThetaTwistLaw` and
Shimura's theorem, the identity holds. -/
@[kb "shimura1973" "proof of the Main Theorem: the dual side of the Rankin integral, the cusps other than infinity [unverified]"]
structure ShimuraDualUnfolding (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop where
  dual : 2 ≤ k → ∀ t : ℕ, 1 ≤ t → Squarefree t → ∀ f ∈ M.cuspForms k N χ, ∀ a : ℕ → ℂ, Abstract.HasQExp f a →
    ∃ b : ℕ → ℂ, CoeffGrowth b ∧ b 0 = 0 ∧
      (∀ R : List SL(2, ℤ), IsGamma0Reps (rankinLevel N t 1) R → ∃ σ : ℝ, ∀ w : ℂ, σ < w.re →
        rankinDualFactor k N t (1 : DirichletCharacter ℂ 1) w *
            rankinDual k N χ t (1 : DirichletCharacter ℂ 1) f R (rankinS k w) =
          I ^ (2 * k) * (gammaFactor (4 * N) w * LSeries b w)) ∧
      ∀ m : ℕ, m.Prime → m ≠ 2 → m.Coprime (4 * N) → ∀ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive →
        ∀ R : List SL(2, ℤ), IsGamma0Reps (rankinLevel N t m) R → ∃ σ : ℝ, ∀ w : ℂ, σ < w.re →
          rankinDualFactor k N t ψ w * rankinDual k N χ t ψ f R (rankinS k w) =
            I ^ (2 * k) * weilConstant (χ ^ 2) ψ * (gammaFactor (4 * N * m ^ 2) w * LSeries (twist ψ⁻¹ b) w)

end ModularFormsKB.HalfIntegral
