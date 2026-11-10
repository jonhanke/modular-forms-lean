/-
# Shimura's theorem, Niwa's refinement and Shintani's lift: named inputs

All statements are relative to an abstract multiplier system
`M : MultiplierSystem` (`ModularFormsKB/HalfIntegral/Abstract/Multiplier.lean`); they are meant for the theta multiplier, and for
an arbitrary `M` they may be false (as inputs they are then vacuous). Deep results enter as **named `Prop` structures** with
`@[kb]` sources, never as axioms. The formal coefficient identities they rely on are proved in
`ModularFormsKB/HalfIntegral/Hecke.lean` and `ModularFormsKB/HalfIntegral/ShimuraLift.lean`.

**What follows formally.** `ShimuraTheorem.lift_heckeT` combines Shimura's theorem (an input) with the proved coefficient
identity `shimuraCoeff_heckeT`: the $q$-expansion of the lift of $T(p^2)f$ is $T(p)$ of the $q$-expansion of the lift of $f$.

**Index shift.** Matrix entries are 0-based: $c = \gamma_{1,0}$, $d = \gamma_{1,1}$.
-/
import ModularFormsKB.HalfIntegral.Abstract.Multiplier
import ModularFormsKB.HalfIntegral.ShimuraLift
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup
open scoped Real
open scoped Manifold

local notation "ℍ" => UpperHalfPlane

/-- **Integral weight $w$ on $\Gamma_0(L)$ with character $\psi$:** holomorphic, $F(\gamma\tau) = \psi(d)(c\tau+d)^w F(\tau)$ on
$\Gamma_0(L)$, and $|c\tau+d|^{-w}|F(\gamma\tau)|$ bounded at $i\infty$ for every $\gamma \in \mathrm{SL}_2(\mathbb Z)$. -/
structure IsIntModularForm (w L : ℕ) (ψ : DirichletCharacter ℂ L) (F : ℍ → ℂ) : Prop where
  holo : MDiff F
  transforms : ∀ γ ∈ Gamma0 L, ∀ τ : ℍ,
    F (γ • τ) = ψ (γ 1 1 : ZMod L) * ((γ 1 0 : ℂ) * τ + γ 1 1) ^ w * F τ
  bdd_at_cusps : ∀ γ : SL(2, ℤ),
    UpperHalfPlane.IsBoundedAtImInfty (fun τ : ℍ ↦ ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-(w : ℝ)) * ‖F (γ • τ)‖)

/-- **Integral weight $w$ cusp form on $\Gamma_0(L)$ with character $\psi$.** -/
structure IsIntCuspForm (w L : ℕ) (ψ : DirichletCharacter ℂ L) (F : ℍ → ℂ) : Prop where
  holo : MDiff F
  transforms : ∀ γ ∈ Gamma0 L, ∀ τ : ℍ,
    F (γ • τ) = ψ (γ 1 1 : ZMod L) * ((γ 1 0 : ℂ) * τ + γ 1 1) ^ w * F τ
  zero_at_cusps : ∀ γ : SL(2, ℤ),
    UpperHalfPlane.IsZeroAtImInfty (fun τ : ℍ ↦ ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-(w : ℝ)) * ‖F (γ • τ)‖)

/-- **Hecke stability of $M_{k+1/2}(4N,\chi)$ and $S_{k+1/2}(4N,\chi)$** (Shimura 1973 `shimura1973`, Thm. 1.7
[unverified]): for every prime $p \nmid 4N$, the $q$-expansion of a form, transformed by Shimura's coefficient formula
`heckeT`, is again the $q$-expansion of a form in the same space. -/
@[kb "shimura1973" "Thm. 1.7: T(p²) preserves M_{k+1/2}(4N, χ) and S_{k+1/2}(4N, χ), coefficient formula [unverified]"]
structure HeckeStable (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop where
  modular : ∀ p : ℕ, p.Prime → ¬ p ∣ 4 * N → ∀ f ∈ M.modularForms k N χ, ∀ a : ℕ → ℂ, Abstract.HasQExp f a →
    ∃ g ∈ M.modularForms k N χ, Abstract.HasQExp g (heckeT k N χ p a)
  cusp : ∀ p : ℕ, p.Prime → ¬ p ∣ 4 * N → ∀ f ∈ M.cuspForms k N χ, ∀ a : ℕ → ℂ, Abstract.HasQExp f a →
    ∃ g ∈ M.cuspForms k N χ, Abstract.HasQExp g (heckeT k N χ p a)

/-- **Shimura's theorem** (Shimura 1973 `shimura1973`, Main Theorem [unverified]; level $4N$ as a consequence of Niwa's
level $2N$): for $k \ge 2$, squarefree $t \ge 1$ and $f \in S_{k+1/2}(4N,\chi)$ with $q$-expansion $a$, there is a cusp form
$F \in S_{2k}(4N, \chi^2)$ whose $n$-th coefficient is $A_t(n) = $ `shimuraCoeff k N χ t a n` for every $n \ge 1$.
(Shimura proved $F$ is a modular form of some level and conjectured level $2N$; $k = 1$ needs $f$ orthogonal to the
unary theta series and is not stated.) -/
@[kb "shimura1973" "Main Theorem: the t-th lift of a cusp form of weight k+1/2 is a cusp form of weight 2k, k ≥ 2 [unverified]"]
structure ShimuraTheorem (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop where
  lift : 2 ≤ k → ∀ t : ℕ, 1 ≤ t → Squarefree t → ∀ f ∈ M.cuspForms k N χ, ∀ a : ℕ → ℂ, Abstract.HasQExp f a →
    ∃ F : ℍ → ℂ, IsIntCuspForm (2 * k) (4 * N) (χ ^ 2) F ∧
      ∃ c : ℕ → ℂ, Abstract.HasQExp F c ∧ ∀ n, 1 ≤ n → c n = shimuraCoeff k N χ t a n

/-- **Hecke equivariance of the Shimura lift, on $q$-expansions.** If $F$ is a $t$-th lift of $f$ (coefficients $A_t$ for
$n \ge 1$) and $F'$ a $t$-th lift of $T(p^2)f$, then for every $n \ge 1$ the coefficients of $F'$ are those of $T(p)F$
(weight $2k$, character $\chi^2$). This is the formal identity `shimuraCoeff_heckeT_of_squarefree` read through the
lifts; no analytic input is used. -/
theorem lift_heckeT_coeff (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {p t : ℕ} (hp : p.Prime) (ht : Squarefree t)
    {a c c' : ℕ → ℂ} (hc : ∀ n, 1 ≤ n → c n = shimuraCoeff k N χ t a n)
    (hc' : ∀ n, 1 ≤ n → c' n = shimuraCoeff k N χ t (heckeT k N χ p a) n) {n : ℕ} (hn : 1 ≤ n) :
    c' n = heckeTInt (2 * k) (4 * N) (χ ^ 2) p c n := by
  rw [hc' n hn, shimuraCoeff_heckeT_of_squarefree k N χ hp ht a hn, heckeTInt, heckeTInt,
    hc (p * n) (Nat.one_le_iff_ne_zero.2 (mul_ne_zero hp.ne_zero (Nat.one_le_iff_ne_zero.1 hn)))]
  split_ifs with h
  · rw [hc (n / p) (Nat.div_pos (Nat.le_of_dvd hn h) hp.pos)]
  · rfl

/-- **Niwa's level** (Niwa 1975 `niwa1975` [unverified]): the $t$-th lift of $f \in S_{k+1/2}(4N,\chi)$, $k \ge 2$, is a cusp
form on $\Gamma_0(2N)$, with a character $\psi$ mod $2N$ inducing $\chi^2$ mod $4N$. -/
@[kb "niwa1975" "the Shimura lift has level 2N [unverified]"]
structure NiwaLevel (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop where
  lift : 2 ≤ k → ∀ t : ℕ, 1 ≤ t → Squarefree t → ∀ f ∈ M.cuspForms k N χ, ∀ a : ℕ → ℂ, Abstract.HasQExp f a →
    ∃ ψ : DirichletCharacter ℂ (2 * N), DirichletCharacter.changeLevel (⟨2, by ring⟩ : 2 * N ∣ 4 * N) ψ = χ ^ 2 ∧
      ∃ F : ℍ → ℂ, IsIntCuspForm (2 * k) (2 * N) ψ F ∧
        ∃ c : ℕ → ℂ, Abstract.HasQExp F c ∧ ∀ n, 1 ≤ n → c n = shimuraCoeff k N χ t a n

/-- **The six right cosets of $\Gamma_0(4)$ in $\mathrm{SL}_2(\mathbb Z)$:** $1, S, ST, ST^2, ST^3, ST^2S$ (bottom rows
$(0,1), (1,0), (1,1), (1,2), (1,3), (2,-1)$, one for each point of $\mathbb P^1(\mathbb Z/4)$). -/
def gamma0FourReps : List SL(2, ℤ) :=
  [1, ModularGroup.S, ModularGroup.S * ModularGroup.T, ModularGroup.S * ModularGroup.T ^ 2,
    ModularGroup.S * ModularGroup.T ^ 3, ModularGroup.S * ModularGroup.T ^ 2 * ModularGroup.S]

/-- **Petersson integral over $\Gamma \backslash \mathbb H$ through right coset representatives** $R$:
$\sum_{\gamma \in R}\int_{\mathcal F} \overline{f(\gamma\tau)}\,g(\gamma\tau)\,\operatorname{Im}(\gamma\tau)^{w}\,d\mu(\tau)$, with
$\mathcal F$ = `ModularGroup.fd` and $d\mu = dx\,dy/y^2$ (Mathlib's `volume` on $\mathbb H$). Not normalized by the index. -/
noncomputable def peterssonReps (R : List SL(2, ℤ)) (w : ℝ) (f g : ℍ → ℂ) : ℂ :=
  (R.map fun γ ↦ ∫ τ in ModularGroup.fd,
    (starRingEnd ℂ) (f (γ • τ)) * g (γ • τ) * (((γ • τ).im ^ w : ℝ) : ℂ)).sum

/-- **Niwa's theta-kernel identity, for a given kernel $\Theta$** (Niwa 1975 `niwa1975` [unverified]). Niwa writes the
$t$-th lift as $F(w) = \langle f, \Theta(\cdot, w)\rangle$, a Petersson integral over $\Gamma_0(4N)\backslash\mathbb H$ of
$f$ against a theta kernel $\Theta(z, w)$ attached to an indefinite ternary quadratic form of signature $(2,1)$ and level
$4N$, with a polynomial weight. The kernel itself is **not yet defined in Lean**: this `Prop` is the identity for a supplied
`Θ` and a supplied list `R` of right coset representatives of $\Gamma_0(4N)$; it becomes Niwa's theorem once `Θ` is
instantiated with Niwa's kernel (normalization to be checked against the source). -/
@[kb "niwa1975" "the Shimura lift is the theta integral against Niwa's kernel [unverified]"]
structure NiwaThetaKernel (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ)
    (R : List SL(2, ℤ)) (Θ : ℍ → ℍ → ℂ) : Prop where
  lift : ∀ f ∈ M.cuspForms k N χ, ∀ a : ℕ → ℂ, Abstract.HasQExp f a →
    ∃ c : ℕ → ℂ, (∀ n, 1 ≤ n → c n = shimuraCoeff k N χ t a n) ∧
      Abstract.HasQExp (fun w ↦ peterssonReps R ((k : ℝ) + 1 / 2) (fun z ↦ Θ z w) f) c

/-- **Shintani's lift, as the adjoint of the Shimura lift** (Shintani 1975 `shintani1975` [unverified]): for $k \ge 2$ and
squarefree $t$ there is a $\mathbb C$-linear map $\Phi$ from integral weight $2k$ cusp forms on $\Gamma_0(2N)$ (character $\psi$)
to $S_{k+1/2}(4N,\chi)$ such that $\langle F, G\rangle_{2N} = \langle f, \Phi G\rangle_{4N}$ whenever $F$ is a $t$-th lift of $f$.
**Partial statement:** for finite-dimensional spaces an adjoint exists abstractly; the content of Shintani's theorem is
the explicit formula for the coefficients of $\Phi G$ as cycle integrals of $G$ against binary quadratic forms of
discriminant $(-1)^k t\,n$, which needs cycle integrals and is not yet stated. Constants in the Petersson normalizations
are absorbed into $\Phi$. -/
@[kb "shintani1975" "Shintani's lift is adjoint to the Shimura lift [unverified; cycle-integral formula not stated]"]
structure ShintaniAdjoint (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N))
    (ψ : DirichletCharacter ℂ (2 * N)) (t : ℕ) (R₂ R₄ : List SL(2, ℤ)) : Prop where
  adjoint : ∃ Φ : (ℍ → ℂ) →ₗ[ℂ] (ℍ → ℂ),
    (∀ G, IsIntCuspForm (2 * k) (2 * N) ψ G → Φ G ∈ M.cuspForms k N χ) ∧
    ∀ f ∈ M.cuspForms k N χ, ∀ a : ℕ → ℂ, Abstract.HasQExp f a →
      ∀ F c, IsIntCuspForm (2 * k) (2 * N) ψ F → Abstract.HasQExp F c →
        (∀ n, 1 ≤ n → c n = shimuraCoeff k N χ t a n) →
        ∀ G, IsIntCuspForm (2 * k) (2 * N) ψ G →
          peterssonReps R₂ (2 * k) F G = peterssonReps R₄ ((k : ℝ) + 1 / 2) f (Φ G)

end ModularFormsKB.HalfIntegral
