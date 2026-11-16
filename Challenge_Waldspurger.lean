/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import ModularFormsKB.HalfIntegral.Waldspurger.Packets
import ModularFormsKB.HalfIntegral.Waldspurger.Coefficients
import ModularFormsKB.HalfIntegral.Waldspurger.Gross
import ModularFormsKB.HalfIntegral.Rankin.ThetaShimura
import ModularFormsKB.HalfIntegral.Rankin.Unfolding
import ModularFormsKB.Miyake.HeckeTrick.LatticeInversion
import ModularFormsKB.HalfIntegral.Rankin.FrickeKernel

/-!
# Headline statements of modular-forms-lean 0.5.0: Waldspurger's theorems, the Shimura lift and Gross's example for p = 11

The main results of the library for Waldspurger's theorems on the Shimura correspondence, Kohnen's formula for odd
squarefree level, and Gross's weight 3/2 form for the prime 11, one theorem each (a few closely related concrete facts
are combined into one conjunction), with every proof a deliberate `sorry`: to check what is claimed, read this file.
`Solution_Waldspurger.lean` proves the same statements from the library, and `lake comparator` (configured by
`comparator/Waldspurger.json`) checks that each proved statement is exactly the one here and uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

**Unconditional theorems** (no named input; they are proved from the definitions, and `#print axioms` shows only the
standard axioms):

* the combinatorics of sign patterns (`LocalData`, `TwistData`): half of all patterns are admissible, the parity
  criterion, the closed form of the fibre dimension, multiplicity one, and the product formula for the local signs of
  a square class;
* Kohnen's pattern for odd squarefree level: it is admissible, it carries a fundamental discriminant exactly when
  Kohnen's condition `(D/p) = w_p` holds, and the fibre of the corresponding local data is one-dimensional;
* Gross's example for p = 11: the coefficients of `g = (θ₁ - θ₂)/2` vanish unless `-n ≡ 0, 1 mod 4` (Kohnen's plus
  condition) and whenever 11 splits in `ℚ(√-n)`, they take the listed values for `n ≤ 16`, and the Brandt matrices
  `B(2)`, `B(3)`, `B(5)` of the two maximal order classes of the quaternion algebra ramified at `{11, ∞}` have the
  stated row sums, symmetry and eigenvectors;
* (0.4.0) two former named inputs of Shimura's theorem, now proved: Hecke's functional equation of the lattice
  Eisenstein series with a character (`eisensteinLattice_functionalEquation`) and the Rankin–Selberg unfolding
  (`rankin_unfolding`).

**Conditional theorems.** Each has the form *(named inputs) → statement*: its first hypothesis is a named `Prop`
structure whose fields are classical theorems that the library does not prove, each with its source. The inputs are
hypotheses, not axioms, so `#print axioms` shows only the standard axioms. The theorem says: whoever proves the named
inputs has proved the conclusion. All locators below (theorem, corollary or page numbers) are unverified: the papers
were not checked.

## Named inputs (assumed, not proved here)

* `ModularFormsKB.HalfIntegral.Waldspurger.WaldspurgerSquareClass`: J.-L. Waldspurger, *Sur les coefficients de
  Fourier des formes modulaires de poids demi-entier*, J. Math. Pures Appl. 60 (1981), Corollaire 2. For a Hecke
  eigenform `g` of weight
  `k + 1/2` whose Shimura lift is `F`, and squarefree `n₁`, `n₂` prime to `4N` in one square class,
  `c(n₁)² L(F, χ'_{n₂}, k) n₂^(k-1/2) = c(n₂)² L(F, χ'_{n₁}, k) n₁^(k-1/2)`. It is stated for quadratic `χ` and `n_i`
  prime to `4N`, hence weaker than the source;
* `ModularFormsKB.HalfIntegral.Waldspurger.KohnenSquarefree`: W. Kohnen, *Fourier coefficients of modular forms of
  half-integral weight*, Math. Ann. 271 (1985), Theorem 1. Kohnen's formula for `N` odd squarefree, relating
  `|c(|D|)|²` to the central value `L(f, D, k)` for fundamental `D` satisfying Kohnen's condition, and the vanishing of
  `c(|D|)` when the condition fails. The Petersson quotient `⟨g, g⟩ / ⟨f, f⟩` of the source is replaced by an
  unspecified positive real constant `κ` (the Petersson product of level `4N` is not constructed in the library);
* `ModularFormsKB.HalfIntegral.Waldspurger.WaldspurgerCoefficients`: J.-L. Waldspurger, *Correspondances de Shimura
  et quaternions*, Forum Math. 3 (1991), main theorem (locator unverified): for an admissible sign pattern `ε`, the
  automorphic representation `σ_ε` has a nonzero `t`-th Fourier coefficient iff `ε` is the pattern of local signs
  selected by `t` and `L(1/2, π ⊗ χ_t) ≠ 0`;
* `ModularFormsKB.HalfIntegral.Waldspurger.WaldspurgerFibreDimension`: the same paper of Waldspurger (1991; locator
  unverified): the
  space of forms whose Shimura lifts are multiples of `b` (inside a subspace `S`) has the dimension
  `LocalData.fibreDim`, the sum over admissible patterns of the products of the local fixed-vector dimensions;
* `ModularFormsKB.HalfIntegral.Waldspurger.Gross.GrossRatio`: B. H. Gross, *Heights and the special values of
  L-series*, 1987 (Gross 1987; locator unverified): for fundamental discriminants `D₁, D₂ < 0` in which 11 is inert,
  `c(|D₁|)² √|D₂| L(f, D₂, 1) = c(|D₂|)² √|D₁| L(f, D₁, 1)`, where `f` is the newform of level 11. The ratio form was
  checked numerically for the discriminants tested (it is Waldspurger's theorem on the inert square classes);
* (0.4.0) `ModularFormsKB.HalfIntegral.ShimuraDualUnfolding`: the dual side of the Rankin integral in Shimura's proof
  of his Main Theorem (G. Shimura, *On modular forms of half integral weight*, Ann. of Math. 97 (1973); locator
  unverified): for `k ≥ 2`, squarefree `t` and a cusp form `f` of weight `k + 1/2`, the Rankin integral at the cusps
  other than `∞`, twisted by every primitive character `ψ` of odd prime conductor prime to `4N`, is
  `i^{2k}` (times Weil's constant) times the completed Dirichlet series of one sequence `b` (and of its twist by
  `ψ̄`). It is the input of `shimuraLift_theta_of_dualUnfolding`, Shimura's theorem for the theta multiplier.
* (0.5.0) `ModularFormsKB.HalfIntegral.ShimuraFrickeKernelUnfolding`: a smaller input than `ShimuraDualUnfolding`,
  from the same proof of Shimura (1973; locator unverified). The library now proves that `f|W_{4N}` is a cusp form for
  the conjugate character, with a `q`-expansion, and rewrites the dual Rankin integral as an integral over
  `Γ₀(L)\ℍ` of an explicit kernel built from `f|W_{4N}`, the theta series `θ_ψ̄` and an Eisenstein series at `∞`
  (`frickeKernelIntegral`). The input is the unfolding of that integral: for `k ≥ 2`, squarefree `t ≥ 1` and every
  cusp form `f` with coefficients `a`, there is one sequence `b` of polynomial growth with `b(0) = 0` such that, for
  `ψ = 1` and for every primitive `ψ` of odd prime conductor prime to `4N`, the kernel integral times its gamma
  factor is `i^{2k}` (times Weil's constant) times the completed Dirichlet series of `b` (and of its twist by `ψ̄`). It
  is the input of `shimuraLift_theta_of_frickeKernel`.

Mathlib has no L-functions of elliptic curves or of modular forms of half-integral weight in this setting. The central
values enter only through abstract functions (`L` in `KohnenSquarefree`, `Lval` in `GrossRatio`, and the entire
continuations in `WaldspurgerSquareClass`), constrained only by the named inputs and, for `L` in `KohnenSquarefree` and the continuations in
`WaldspurgerSquareClass`, by the requirement that they be an entire continuation of the Dirichlet series
(`IsEntireLSeries`).

## Definitions used

Besides Mathlib, the statements use these definitions of the library; a reader checking a statement should check them
too (all in the namespace `ModularFormsKB.HalfIntegral.Waldspurger` unless noted):

* the sign-pattern combinatorics: `LocalData` (the local data `discrete`, `dim`, `rootLocal`), `LocalData.rootNumber`,
  `LocalData.IsAdmissible`, `LocalData.admissible`, `LocalData.negSet`, `LocalData.componentDim`, `LocalData.fibreDim`,
  `TwistData` and `TwistData.localSign`;
* the classical instance: `Places`, `classicalLocal`, `ClassicalClasses`, `classicalTwist`, `kohnenPattern`, `signOf`;
* in the inputs: `WaldspurgerCoefficients`, `WaldspurgerSquareClass`, `LiftsTo`, `SameSquareClass`,
  `shimuraTwistCoeff`, `KohnenSquarefree`, `WaldspurgerFibreDimension`, `shimuraFibre`, and, in the namespace
  `ModularFormsKB.HalfIntegral`, `MultiplierSystem` (with `cuspForms` and `plusCuspForms`), `IsEntireLSeries`,
  `kroneckerDisc` and `IsFundamentalDiscriminant`;
* for Gross's form: `Gross.grossQ₁`, `Gross.grossQ₂` (the ternary quadratic forms), `Gross.thetaCount` (the number of
  representations, counted in a box that contains every solution), `Gross.grossCoeff` (`(r_{Q₁}(n) - r_{Q₂}(n)) / 2`),
  `Gross.brandt₂`, `Gross.brandt₃`, `Gross.brandt₅`, `Gross.brandtWeight`, `Gross.grossEigen`, `Gross.GrossRatio`. The
  identification of `Q₁`, `Q₂` and the Brandt matrices with the quaternionic objects of Gross is checked numerically by
  a script, not in Lean.
* (0.4.0) in the namespace `ModularFormsKB.HalfIntegral`, for Shimura's theorem: `eisensteinLattice`,
  `eisensteinDual` (the lattice Eisenstein series and its Poisson dual), `IsGamma0Reps`, `UnitaryLaw`, `stripPt`,
  `repsIntegral`, `stripMellin` (the unfolding), `thetaMultiplierSystem`, `MultiplierSystem.cuspForms`,
  `Abstract.HasQExp`, `IsIntCuspForm`, `shimuraCoeff`, and in the input `ShimuraDualUnfolding`: `CoeffGrowth`,
  `rankinLevel`, `rankinDualFactor`, `rankinDual`, `rankinS`, `gammaFactor`, `weilConstant`, `twist`.
-/

namespace ModularFormsKB.Headlines

section Waldspurger

open ModularFormsKB.HalfIntegral ModularFormsKB.HalfIntegral.Waldspurger
  ModularFormsKB.HalfIntegral.Waldspurger.Gross

local notation "ℍ" => UpperHalfPlane

/-! ### Sign patterns, unconditional -/

/-- **Half of all sign patterns are admissible:** $2^{|\iota| - 1}$ of them, when the set $\iota$ of places is
nonempty. -/
theorem waldspurger_card_admissible {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (D : LocalData ι) :
    D.admissible.card = 2 ^ (Fintype.card ι - 1) := by
  sorry

/-- **Hilbert-reciprocity parity:** when the global root number is $+1$, a pattern is admissible iff it is $-1$ at an
even number of places. -/
theorem waldspurger_isAdmissible_iff_even {ι : Type*} [Fintype ι] [DecidableEq ι] (D : LocalData ι)
    (h : D.rootNumber = 1) (ε : ι → ℤˣ) : D.IsAdmissible ε ↔ Even (LocalData.negSet ε).card := by
  sorry

/-- **Closed form of the fibre dimension:**
$2\dim = \prod_v (d_v^+ + d_v^-) + \varepsilon(\tfrac12,\pi)\prod_v(d_v^+ - d_v^-)$. -/
theorem waldspurger_two_mul_fibreDim {ι : Type*} [Fintype ι] [DecidableEq ι] (D : LocalData ι) :
    2 * (D.fibreDim : ℤ) = ∏ v, ((D.dim v 1 : ℤ) + D.dim v (-1)) +
      (D.rootNumber : ℤ) * ∏ v, ((D.dim v 1 : ℤ) - D.dim v (-1)) := by
  sorry

/-- **Multiplicity one:** if at every place at most one member of the packet has fixed vectors, and then at most a
line, the fibre has dimension at most one. -/
theorem waldspurger_fibreDim_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] (D : LocalData ι)
    (h : ∀ v, D.dim v 1 + D.dim v (-1) ≤ 1) : D.fibreDim ≤ 1 := by
  sorry

/-- **The product of the local signs selected by a square class $t$** is
$\varepsilon(\tfrac12,\pi)\,\varepsilon(\tfrac12,\pi\otimes\chi_t)$. -/
theorem waldspurger_prod_localSign {ι : Type*} [Fintype ι] [DecidableEq ι] {D : LocalData ι} {T : Type*}
    (X : TwistData D T) (t : T) : ∏ v, X.localSign t v = D.rootNumber * X.twistRoot t := by
  sorry

/-- **The pattern selected by $t$ is admissible iff $\varepsilon(\tfrac12, \pi\otimes\chi_t) = +1$.** -/
theorem waldspurger_isAdmissible_localSign_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {D : LocalData ι}
    {T : Type*} (X : TwistData D T) (t : T) : D.IsAdmissible (X.localSign t) ↔ X.twistRoot t = 1 := by
  sorry

/-! ### Kohnen's pattern for odd squarefree level, unconditional -/

/-- **Kohnen's pattern is admissible** for every newform (local signs given by the Atkin-Lehner eigenvalues `w`). -/
theorem waldspurger_kohnenPattern_isAdmissible (k N : ℕ) (w : N.primeFactors → ℤˣ)
    (dimFin : N.primeFactors → ℤˣ → ℕ) :
    (classicalLocal k N w dimFin).IsAdmissible (kohnenPattern k N w) := by
  sorry

/-- **Kohnen's condition:** $D$ lies in Kohnen's pattern iff $\left(\frac Dp\right) = w_p$ for every $p \mid N$. -/
theorem waldspurger_localSign_eq_kohnenPattern_iff (k N : ℕ) (w : N.primeFactors → ℤˣ)
    (dimFin : N.primeFactors → ℤˣ → ℕ) (D : ClassicalClasses k N) :
    (classicalTwist k N w dimFin).localSign D = kohnenPattern k N w ↔
      ∀ p : N.primeFactors, signOf (jacobiSym D.1 p) = w p := by
  sorry

/-- **The plus space is one-dimensional over $f$:** if the local fixed vectors are a line in $\sigma_p^{w_p}$ and zero
in $\sigma_p^{-w_p}$ at each $p \mid N$, the fibre dimension is $1$. -/
theorem waldspurger_kohnen_fibreDim (k N : ℕ) (w : N.primeFactors → ℤˣ) :
    (classicalLocal k N w (fun p ε ↦ if ε = w p then 1 else 0)).fibreDim = 1 := by
  sorry

/-! ### Gross's example for p = 11, unconditional -/

/-- **Kohnen's plus condition for Gross's form:** $c(n) = 0$ unless $-n \equiv 0, 1 \bmod 4$. -/
theorem gross_grossCoeff_eq_zero_of_mod_four {n : ℕ} (h : n % 4 = 1 ∨ n % 4 = 2) : grossCoeff n = 0 := by
  sorry

/-- **$c(n) = 0$ when $11$ splits in $\mathbb Q(\sqrt{-n})$**, i.e. $\left(\frac{-n}{11}\right) = 1$: neither of the two
ternary forms represents $n$. -/
theorem gross_grossCoeff_eq_zero_of_split {n : ℕ} (h : jacobiSym (-(n : ℤ)) 11 = 1) : grossCoeff n = 0 := by
  sorry

/-- **The first coefficients of Gross's form** $g = -q^3 + q^4 + q^{11} + q^{12} - q^{15} - 2q^{16} - \dots$ (with
$c(7) = 0$), computed from the definition `grossCoeff`. -/
theorem gross_grossCoeff_values :
    grossCoeff 3 = -1 ∧ grossCoeff 4 = 1 ∧ grossCoeff 7 = 0 ∧ grossCoeff 11 = 1 ∧ grossCoeff 12 = 1 ∧
      grossCoeff 15 = -1 ∧ grossCoeff 16 = -2 := by
  sorry

/-- **Brandt matrices for $p = 11$, row sums and symmetry:** the rows of $B(m)$ sum to $\sigma(m)$ for $m = 2, 3, 5$,
and $w_jB_{ij} = w_iB_{ji}$. -/
theorem gross_brandt_rowSum_symm :
    (∀ i, ∑ j, brandt₂ i j = 3) ∧ (∀ i, ∑ j, brandt₃ i j = 4) ∧ (∀ i, ∑ j, brandt₅ i j = 6) ∧
      (∀ i j, brandtWeight j * brandt₂ i j = brandtWeight i * brandt₂ j i) ∧
      (∀ i j, brandtWeight j * brandt₃ i j = brandtWeight i * brandt₃ j i) ∧
      (∀ i j, brandtWeight j * brandt₅ i j = brandtWeight i * brandt₅ j i) := by
  sorry

/-- **$e = (1, -1)$ is an eigenvector with the eigenvalues of $f$:** $B(m)^{\mathsf T}e = a_m e$ with
$a_2 = -2$, $a_3 = -1$, $a_5 = 1$. -/
theorem gross_brandt_eigen :
    brandt₂.transpose.mulVec grossEigen = (-2 : ℤ) • grossEigen ∧
      brandt₃.transpose.mulVec grossEigen = (-1 : ℤ) • grossEigen ∧
      brandt₅.transpose.mulVec grossEigen = (1 : ℤ) • grossEigen := by
  sorry

/-- **The Eisenstein eigenvector:** $(1,1)$ has eigenvalue $\sigma(m)$ under $B(m)$. -/
theorem gross_brandt_eisenstein :
    brandt₂.mulVec ![1, 1] = (3 : ℤ) • ![1, 1] ∧ brandt₃.mulVec ![1, 1] = (4 : ℤ) • ![1, 1] ∧
      brandt₅.mulVec ![1, 1] = (6 : ℤ) • ![1, 1] := by
  sorry

/-! ### Waldspurger on square classes, conditional -/

/-- **One constant per square class, conditional on Waldspurger's theorem on square classes** (named input
`WaldspurgerSquareClass`): if $L(F,\chi'_{n_0},k) \ne 0$ for one $n_0$ in the class, then
$c(n)^2 = A\,L(F,\chi'_n,k)\,n^{k-1/2}$ for all $n$ in the class, with one constant $A$. -/
theorem waldspurger_exists_constant {M : MultiplierSystem} {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)}
    (hW : WaldspurgerSquareClass M k N χ) (hk : 1 ≤ k) (hχ : χ ^ 2 = 1)
    {g : ℍ → ℂ} {c : ℕ → ℂ} {F : ℍ → ℂ} {b : ℕ → ℂ} (hg : LiftsTo M k N χ g c F b)
    (L : ℕ → ℂ → ℂ) (hL : ∀ n, IsEntireLSeries (shimuraTwistCoeff k N χ n b) ((k : ℝ) + 1) (L n))
    {n₀ : ℕ} (h₀ : 1 ≤ n₀) (hsq₀ : Squarefree n₀) (hcop₀ : Nat.Coprime n₀ (4 * N)) (hL₀ : L n₀ k ≠ 0) :
    ∃ A : ℂ, ∀ n : ℕ, 1 ≤ n → Squarefree n → Nat.Coprime n (4 * N) → SameSquareClass N n₀ n →
      c n ^ 2 = A * L n k * ((n : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) := by
  sorry

/-- **Vanishing of coefficients detects vanishing of central values**, conditional on `WaldspurgerSquareClass`: on a
square class containing some $n_0$ with $c(n_0) \ne 0$ and $L(F,\chi'_{n_0},k) \ne 0$. -/
theorem waldspurger_coeff_eq_zero_iff {M : MultiplierSystem} {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)}
    (hW : WaldspurgerSquareClass M k N χ) (hk : 1 ≤ k) (hχ : χ ^ 2 = 1)
    {g : ℍ → ℂ} {c : ℕ → ℂ} {F : ℍ → ℂ} {b : ℕ → ℂ} (hg : LiftsTo M k N χ g c F b)
    (L : ℕ → ℂ → ℂ) (hL : ∀ n, IsEntireLSeries (shimuraTwistCoeff k N χ n b) ((k : ℝ) + 1) (L n))
    {n₀ : ℕ} (h₀ : 1 ≤ n₀) (hsq₀ : Squarefree n₀) (hcop₀ : Nat.Coprime n₀ (4 * N)) (hc₀ : c n₀ ≠ 0)
    (hL₀ : L n₀ k ≠ 0) {n : ℕ} (hn : 1 ≤ n) (hsq : Squarefree n) (hcop : Nat.Coprime n (4 * N))
    (hcl : SameSquareClass N n₀ n) : c n = 0 ↔ L n k = 0 := by
  sorry

/-! ### Kohnen's formula, conditional -/

/-- **Nonnegativity of central values, conditional on Kohnen's formula** (named input `KohnenSquarefree`, with the
Petersson quotient an unspecified positive constant): $L(f, D, k)$ is real and $\ge 0$ for every fundamental $D$
satisfying Kohnen's condition. -/
theorem waldspurger_kohnen_central_nonneg {k N : ℕ} {w : N.primeFactors → ℤˣ} {c b : ℕ → ℂ} {L : ℤ → ℂ → ℂ}
    (h : KohnenSquarefree k N w c b L) {D : ℤ} (hD : IsFundamentalDiscriminant D)
    (hsign : 0 < (-1) ^ k * D) (hw : ∀ ℓ : N.primeFactors, kroneckerDisc D ℓ = w ℓ) :
    (L D k).im = 0 ∧ 0 ≤ (L D k).re := by
  sorry

/-- **Ratio form on Kohnen's discriminants, conditional on `KohnenSquarefree`:**
$|c(|D_1|)|^2|D_2|^{k-1/2}L(f,D_2,k) = |c(|D_2|)|^2|D_1|^{k-1/2}L(f,D_1,k)$. -/
theorem waldspurger_kohnen_ratio {k N : ℕ} {w : N.primeFactors → ℤˣ} {c b : ℕ → ℂ} {L : ℤ → ℂ → ℂ}
    (h : KohnenSquarefree k N w c b L) {D₁ D₂ : ℤ} (hD₁ : IsFundamentalDiscriminant D₁)
    (hD₂ : IsFundamentalDiscriminant D₂) (hs₁ : 0 < (-1) ^ k * D₁) (hs₂ : 0 < (-1) ^ k * D₂)
    (hw₁ : ∀ ℓ : N.primeFactors, kroneckerDisc D₁ ℓ = w ℓ) (hw₂ : ∀ ℓ : N.primeFactors, kroneckerDisc D₂ ℓ = w ℓ) :
    ((‖c D₁.natAbs‖ ^ 2 : ℝ) : ℂ) * ((D₂.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) * L D₂ k =
      ((‖c D₂.natAbs‖ ^ 2 : ℝ) : ℂ) * ((D₁.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) * L D₁ k := by
  sorry

/-- **Nonvanishing criterion, conditional on `KohnenSquarefree`:** for $D$ satisfying Kohnen's condition,
$c(|D|) \ne 0 \iff L(f, D, k) \ne 0$. -/
theorem waldspurger_kohnen_coeff_ne_zero_iff {k N : ℕ} {w : N.primeFactors → ℤˣ} {c b : ℕ → ℂ}
    {L : ℤ → ℂ → ℂ} (h : KohnenSquarefree k N w c b L) (hk : 1 ≤ k) {D : ℤ}
    (hD : IsFundamentalDiscriminant D) (hsign : 0 < (-1) ^ k * D)
    (hw : ∀ ℓ : N.primeFactors, kroneckerDisc D ℓ = w ℓ) :
    c D.natAbs ≠ 0 ↔ L D k ≠ 0 := by
  sorry

/-! ### Waldspurger's coefficient theorem and fibre dimension, conditional -/

/-- **A carried square class has root number $+1$, conditional on Waldspurger's coefficient theorem** (named input
`WaldspurgerCoefficients`): if an admissible $\sigma_\varepsilon$ has a nonzero $t$-th coefficient, then
$\varepsilon(\tfrac12,\pi\otimes\chi_t) = +1$. -/
theorem waldspurger_twistRoot_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] {D : LocalData ι} {T : Type*}
    {X : TwistData D T} {carries : (ι → ℤˣ) → T → Prop} {centralNonzero : T → Prop}
    (h : WaldspurgerCoefficients X carries centralNonzero) {ε : ι → ℤˣ}
    (hε : D.IsAdmissible ε) {t : T} (ht : carries ε t) : X.twistRoot t = 1 := by
  sorry

/-- **Each square class is carried by at most one admissible pattern, conditional on `WaldspurgerCoefficients`.** -/
theorem waldspurger_carries_unique {ι : Type*} [Fintype ι] [DecidableEq ι] {D : LocalData ι} {T : Type*}
    {X : TwistData D T} {carries : (ι → ℤˣ) → T → Prop} {centralNonzero : T → Prop}
    (h : WaldspurgerCoefficients X carries centralNonzero) {ε ε' : ι → ℤˣ}
    (hε : D.IsAdmissible ε) (hε' : D.IsAdmissible ε') {t : T} (ht : carries ε t) (ht' : carries ε' t) :
    ε = ε' := by
  sorry

/-- **The plus fibre is a line, conditional on Waldspurger's dimension formula** (named input
`WaldspurgerFibreDimension`, with Kohnen's local data): the forms in Kohnen's plus space whose Shimura lifts are
multiples of $b$ form a space of dimension one. -/
theorem waldspurger_finrank_plusFibre_eq_one {M : MultiplierSystem} {k N : ℕ} {b : ℕ → ℂ}
    {w : N.primeFactors → ℤˣ}
    (h : WaldspurgerFibreDimension M k N 1 b (M.plusCuspForms k N 1)
      (classicalLocal k N w (fun p ε ↦ if ε = w p then 1 else 0))) :
    Module.finrank ℂ ↥(shimuraFibre M k N 1 b ⊓ M.plusCuspForms k N 1) = 1 := by
  sorry

/-! ### Gross's formula, conditional -/

/-- **Vanishing transfers along the inert square classes, conditional on Gross's ratio** (named input `GrossRatio`,
with `Lval D` standing for $L(f, D, 1)$, $f$ the newform of level $11$): given $L(f, D_0, 1) \ne 0$ and
$c(|D_0|) \ne 0$ for one inert $D_0$, $c(|D|) = 0$ iff $L(f, D, 1) = 0$ for every inert $D$. -/
theorem gross_grossCoeff_eq_zero_iff {Lval : ℤ → ℝ} (hG : GrossRatio Lval) {D₀ : ℤ}
    (hF₀ : IsFundamentalDiscriminant D₀) (hD₀ : D₀ < 0)
    (h₀ : jacobiSym D₀ 11 = -1) (hc₀ : grossCoeff D₀.natAbs ≠ 0) (hL₀ : Lval D₀ ≠ 0) {D : ℤ}
    (hF : IsFundamentalDiscriminant D) (hD : D < 0)
    (h : jacobiSym D 11 = -1) : grossCoeff D.natAbs = 0 ↔ Lval D = 0 := by
  sorry

end Waldspurger

section ShimuraTheta

open Complex MatrixGroups CongruenceSubgroup MeasureTheory Set ModularFormsKB.HalfIntegral
open scoped Real UpperHalfPlane

/-- **Hecke's functional equation of the lattice Eisenstein series with a character** (Hecke 1927; Miyake, §7.2),
unconditional since 0.4.0 (it was a named input of Shimura's theorem). For `L ≥ 2`, `λ ≥ 1` and a Dirichlet character
`ω` modulo `L` with `ω(-1) = (-1)^λ`, there is `E*(z, s)`, entire in `s` and continuous in `z`, with
`E*(z, s) = L^s π^{-s} Γ(s + λ/2) E(z, s)` for `Re s > 1` (`E` the series
`y^s ∑_{(c,d) ∈ Lℤ × ℤ} ω(d) (cz+d)^λ |cz+d|^{-λ-2s}`), `E*(z, s) = L^{-s} π^{-(1-s)} Γ(1 - s + λ/2) Ě(z, 1 - s)` for
`Re s < 0` (`Ě` the Poisson dual series with Gauss sums), and `|E*(z, s)| ≤ B (y^A + y^{-A})` on every vertical strip.
The library proves it by Poisson summation on the lattice `ℤz + ℤ` (the lattice theta inversion) and Mellin
transform. -/
theorem eisensteinLattice_functionalEquation :
    ∀ (L lam : ℕ) (ω : DirichletCharacter ℂ L), 2 ≤ L → 1 ≤ lam → ω (-1) = (-1) ^ lam →
      ∃ E : ℍ → ℂ → ℂ, (∀ z, Differentiable ℂ (E z)) ∧ (∀ s, Continuous fun z ↦ E z s) ∧
        (∀ z s, 1 < s.re →
          E z s = (L : ℂ) ^ s * (π : ℂ) ^ (-s) * Gamma (s + lam / 2) * eisensteinLattice L lam ω z s) ∧
        (∀ z s, s.re < 0 →
          E z s = (L : ℂ) ^ (-s) * (π : ℂ) ^ (-(1 - s)) * Gamma (1 - s + lam / 2) *
            eisensteinDual L lam ω z (1 - s)) ∧
        ∀ σ₁ σ₂ : ℝ, ∃ A B : ℝ, ∀ z s, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖E z s‖ ≤ B * (z.im ^ A + z.im ^ (-A)) := by
  sorry

/-- **The Rankin–Selberg unfolding** (Rankin 1939, Selberg 1940), unconditional since 0.4.0 (it was a named input of
Shimura's theorem). Let `L ≥ 1`, `ω` a Dirichlet character modulo `L`, `R` a list of right coset representatives of
`Γ₀(L)` in `SL₂(ℤ)`, and `G` continuous on `ℍ` with the unitary weight-`λ` law
`G(γz) = ω(d) ((cz+d)/|cz+d|)^λ G(z)` on `Γ₀(L)`. For `Re s > 1`, if `|G(x + iy)| y^{Re s - 2}` is integrable on the
strip `[0, 1] × (0, ∞)`, then the integral of `G(z) E(z, s)` over `Γ₀(L)\ℍ` (as `∑_{γ ∈ R} ∫_𝓕 (…)(γτ) dμ(τ)`, `𝓕` the
standard fundamental domain, `dμ = dx dy / y²`) equals `2 L(2s, ω) ∫_0^∞ ∫_0^1 G(x + iy) y^{s-2} dx dy`. -/
theorem rankin_unfolding :
    ∀ (L lam : ℕ) (ω : DirichletCharacter ℂ L) (R : List SL(2, ℤ)), 1 ≤ L → IsGamma0Reps L R →
      ∀ G : ℍ → ℂ, Continuous G → UnitaryLaw L lam ω G → ∀ s : ℂ, 1 < s.re →
        IntegrableOn (fun p : ℝ × ℝ ↦ ‖G (stripPt p.1 p.2)‖ * p.2 ^ (s.re - 2)) (Icc 0 1 ×ˢ Ioi 0) →
        repsIntegral R (fun τ ↦ G τ * eisensteinLattice L lam ω τ s) =
          2 * LSeries (fun n ↦ ω n) (2 * s) * stripMellin G s := by
  sorry

/-- **Shimura's theorem for the theta multiplier, conditional on the dual unfolding identity** (Shimura 1973, Main
Theorem; new in 0.4.0). Assume the named input `ShimuraDualUnfolding thetaMultiplierSystem k N χ` (the dual side of
the Rankin integral at the cusps other than `∞`; the only named input left: the twisted theta law, Hecke's
functional equation and the Rankin unfolding are proved). Then for `k ≥ 2`, squarefree `t ≥ 1` and every cusp form
`f` of weight `k + 1/2` on `Γ₀(4N)` with character `χ` (theta multiplier) and `q`-expansion coefficients `a`, there
is a cusp form `F` of weight `2k` on `Γ₀(4N)` with character `χ²` whose coefficients `c(n)`, `n ≥ 1`, are Shimura's
`∑_{d ∣ n} χ_t(d) d^{k-1} a(tn²/d²)` (`shimuraCoeff`). -/
theorem shimuraLift_theta_of_dualUnfolding (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (hN : 0 < N)
    (hD : ShimuraDualUnfolding thetaMultiplierSystem k N χ) :
    2 ≤ k → ∀ t : ℕ, 1 ≤ t → Squarefree t → ∀ f ∈ thetaMultiplierSystem.cuspForms k N χ, ∀ a : ℕ → ℂ,
      Abstract.HasQExp f a →
      ∃ F : ℍ → ℂ, IsIntCuspForm (2 * k) (4 * N) (χ ^ 2) F ∧
        ∃ c : ℕ → ℂ, Abstract.HasQExp F c ∧ ∀ n, 1 ≤ n → c n = shimuraCoeff k N χ t a n := by
  sorry

/-- **Shimura's theorem for the theta multiplier, conditional on the unfolding of the Fricke kernel** (Shimura 1973,
Main Theorem; new in 0.5.0). Assume the named input `ShimuraFrickeKernelUnfolding thetaMultiplierSystem k N χ`, a
smaller input than the `ShimuraDualUnfolding` of `shimuraLift_theta_of_dualUnfolding` (the part of the dual side
before the unfolding is now proved). Then for `k ≥ 2`, squarefree `t ≥ 1` and every cusp form `f` of weight `k + 1/2`
on `Γ₀(4N)` with character `χ` (theta multiplier) and coefficients `a`, there is a cusp form `F` of weight `2k` on
`Γ₀(4N)` with character `χ²` whose coefficients `c(n)`, `n ≥ 1`, are `∑_{d ∣ n} χ_t(d) d^{k-1} a(tn²/d²)`. -/
theorem shimuraLift_theta_of_frickeKernel (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (hN : 0 < N)
    (hK : ShimuraFrickeKernelUnfolding thetaMultiplierSystem k N χ) :
    2 ≤ k → ∀ t : ℕ, 1 ≤ t → Squarefree t → ∀ f ∈ thetaMultiplierSystem.cuspForms k N χ, ∀ a : ℕ → ℂ,
      Abstract.HasQExp f a →
      ∃ F : ℍ → ℂ, IsIntCuspForm (2 * k) (4 * N) (χ ^ 2) F ∧
        ∃ c : ℕ → ℂ, Abstract.HasQExp F c ∧ ∀ n, 1 ≤ n → c n = shimuraCoeff k N χ t a n := by
  sorry

end ShimuraTheta

end ModularFormsKB.Headlines
