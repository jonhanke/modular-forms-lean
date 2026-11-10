import ModularFormsKB.Milne.Wave4B.ModularFermat
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Conductor

/-!
# Milne, Section 11: the geometric conductor, the strong Hasse–Weil conjecture and Theorems 11.19, 11.23

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 11, pdf pp. 111–118.

## Items
- **D116** (p. 111): the **geometric conductor** $N = \prod_p p^{f_p}$ of an elliptic curve $E$ over $\mathbb Q$, with
  $f_p = 0$ at good reduction, $f_p = 1$ when the reduction has a node, $f_p \ge 2$ when it has a cusp
  (`geometricConductor`). It is the norm of Tau Ceti's `WeierstrassCurve.algorithmicConductor ℤ E`, whose exponents
  are read off Tate's algorithm on a minimal model; the three defining properties are
  `not_dvd_geometricConductor_iff`, `geometricConductor_exponent_eq_one_iff` and `sq_dvd_geometricConductor_iff`.
  Milne's parenthetical "with equality unless $p = 2, 3$" (Ogg's formula) is not proved here.
- **Conjecture 11.17** (strong Hasse–Weil conjecture, p. 117) for one curve (`StrongHasseWeil`, a predicate, not a
  result).
- **Conjecture 11.22** in full (Taniyama–Weil: a nonconstant map $X_0(N) \to E$ with $N$ the geometric conductor;
  `TaniyamaWeilConjecture`, a predicate).
- **Theorem 11.19** (p. 117; Weil's converse theorem, Eichler–Shimura and Faltings), as a named statement
  `ModularIffStrongHasseWeil`; its consequence in Milne's form: `isModularEllipticCurve_iff_strongHasseWeil`.
- **Theorem 11.23** (p. 118): the strong Hasse–Weil conjecture for all elliptic curves over $\mathbb Q$ is equivalent
  to the Taniyama–Weil conjecture (`forall_strongHasseWeil_iff_taniyamaWeil`), proved from Theorem 11.19 as in Milne
  ("We have proved the following").

## Conventions
The coefficients $a_n$ of $L(E,s) = \sum a_n n^{-s}$ are those of Mathlib's `WeierstrassCurve.LFunction`, whose local
factors at bad primes are Milne's (split node $(1-p^{-s})^{-1}$, nonsplit node $(1+p^{-s})^{-1}$, cusp $1$). The Gauss
sum $g(\chi) = \sum_{n=1}^m \chi(n)e^{2\pi i n/m}$ is Mathlib's `gaussSum χ ZMod.stdAddChar`. For a primitive
Dirichlet character $\chi$ modulo $m$ prime to $N$ Milne puts
$\Lambda_\chi(E,s) = N^{s/2}(m/2\pi)^s\Gamma(s)\sum a_n\chi(n)n^{-s}$; the Dirichlet series converges for
$\operatorname{Re}s > 3/2$, and "analytic continuation" means an entire function agreeing with it there. The sign
$\pm$ of Milne's functional equation is allowed to depend on $\chi$, as in his statement.
-/

open Complex CategoryTheory

namespace ModularFormsKB.Milne.Wave4B

open ModularFormsKB.Milne IsDedekindDomain

/-! ### D116: the geometric conductor -/

/-- **The geometric conductor** (Milne, p. 111; D116) of an elliptic curve $E$ over $\mathbb Q$: the positive integer
$\prod_p p^{f_p}$, here the norm of Tau Ceti's conductor ideal `WeierstrassCurve.algorithmicConductor ℤ E`. -/
@[kb "milne2017mf" "Section 11, geometric conductor, D116 (pdf p. 111)"]
noncomputable def geometricConductor (E : WeierstrassCurve ℚ) [E.IsElliptic] : ℕ :=
  Ideal.absNorm (WeierstrassCurve.algorithmicConductor ℤ E)

theorem geometricConductor_pos (E : WeierstrassCurve ℚ) [E.IsElliptic] : 0 < geometricConductor E :=
  Nat.pos_of_ne_zero <| Ideal.absNorm_eq_zero_iff.not.2 (WeierstrassCurve.algorithmicConductor_ne_bot ℤ E)

/-- In D116, $f_p$ (the exponent of $p$ in $N$) is read off the reduction of a minimal model at $v = (p)$:
$p^n \mid N$ exactly when $n \le f_p$. -/
theorem pow_dvd_geometricConductor_iff (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ}
    {v : HeightOneSpectrum ℤ} (hv : v.asIdeal = Ideal.span {(p : ℤ)}) (n : ℕ) :
    p ^ n ∣ geometricConductor E ↔ n ≤ E.algorithmicOggExponent (Localization.AtPrime v.asIdeal) :=
  WeierstrassCurve.pow_dvd_absNorm_algorithmicConductor_iff hv n

/-- D116, $f_p = 0$ exactly at good reduction: $p \nmid N$ if and only if a minimal model of $E$ at $(p)$ has good
reduction. -/
theorem not_dvd_geometricConductor_iff (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ}
    {v : HeightOneSpectrum ℤ} (hv : v.asIdeal = Ideal.span {(p : ℤ)}) :
    ¬ p ∣ geometricConductor E ↔
      (E.minimal (Localization.AtPrime v.asIdeal)).HasGoodReduction (Localization.AtPrime v.asIdeal) := by
  have h := pow_dvd_geometricConductor_iff E hv 1
  rw [pow_one] at h
  rw [h, not_le, Nat.lt_one_iff, WeierstrassCurve.algorithmicOggExponent_eq_zero_iff]

/-- D116, $f_p = 1$ exactly when the reduction has a node: $p \mid N$ and $p^2 \nmid N$ if and only if a minimal
model of $E$ at $(p)$ has multiplicative reduction. -/
theorem geometricConductor_exponent_eq_one_iff (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ}
    {v : HeightOneSpectrum ℤ} (hv : v.asIdeal = Ideal.span {(p : ℤ)}) :
    (p ∣ geometricConductor E ∧ ¬ p ^ 2 ∣ geometricConductor E) ↔
      (E.minimal (Localization.AtPrime v.asIdeal)).HasMultiplicativeReduction
        (Localization.AtPrime v.asIdeal) := by
  have h1 := pow_dvd_geometricConductor_iff E hv 1
  rw [pow_one] at h1
  rw [h1, pow_dvd_geometricConductor_iff E hv 2, ← WeierstrassCurve.algorithmicOggExponent_eq_one_iff]
  omega

/-- D116, $f_p \ge 2$ exactly when the reduction has a cusp: $p^2 \mid N$ if and only if a minimal model of $E$ at
$(p)$ has additive reduction. -/
theorem sq_dvd_geometricConductor_iff (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ}
    {v : HeightOneSpectrum ℤ} (hv : v.asIdeal = Ideal.span {(p : ℤ)}) :
    p ^ 2 ∣ geometricConductor E ↔
      (E.minimal (Localization.AtPrime v.asIdeal)).HasAdditiveReduction (Localization.AtPrime v.asIdeal) := by
  rw [pow_dvd_geometricConductor_iff E hv 2, WeierstrassCurve.two_le_algorithmicOggExponent_iff]

/-! ### Conjecture 11.17: the strong Hasse–Weil conjecture -/

/-- Milne's completed twisted $L$-function on the half-plane of convergence:
$\Lambda_\chi(E,s) = N^{s/2}(m/2\pi)^s\Gamma(s)\sum_n a_n\chi(n)n^{-s}$, $N$ the geometric conductor. -/
noncomputable def completedTwistedLSeries (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (χ : DirichletCharacter ℂ m) (s : ℂ) : ℂ :=
  (geometricConductor E : ℂ) ^ (s / 2) * ((m : ℂ) / (2 * Real.pi)) ^ s * Gamma s *
    LSeries (fun n ↦ (E.LFunction n : ℂ) * χ n) s

/-- `Λ` is an analytic continuation of $\Lambda_\chi(E,s)$ to $\mathbb C$, bounded in vertical strips: an entire
function equal to `completedTwistedLSeries E χ` on $\operatorname{Re} s > 3/2$ and bounded on every strip
$\sigma_1 \le \operatorname{Re} s \le \sigma_2$. -/
def IsBoundedEntireContinuation (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ} (χ : DirichletCharacter ℂ m)
    (Λ : ℂ → ℂ) : Prop :=
  Differentiable ℂ Λ ∧ (∀ s : ℂ, 3 / 2 < s.re → Λ s = completedTwistedLSeries E χ s) ∧
    ∀ σ₁ σ₂ : ℝ, ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖Λ s‖ ≤ C

/-- **The strong Hasse–Weil conjecture** for an elliptic curve $E$ over $\mathbb Q$ (Milne, Conjecture 11.17,
p. 117), as a predicate: for every $m \ge 1$ prime to the geometric conductor $N$ and every primitive Dirichlet
character $\chi$ modulo $m$, $\Lambda_\chi(E,s)$ and $\Lambda_{\bar\chi}(E,s)$ have analytic continuations to
$\mathbb C$, bounded in vertical strips, with
$\Lambda_\chi(E,s) = \pm\,\chi(N)\,g(\chi)/g(\bar\chi)\cdot\Lambda_{\bar\chi}(E,2-s)$. -/
@[kb "milne2017mf" "Section 11, Conjecture 11.17 (pdf p. 117)"]
def StrongHasseWeil (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  ∀ (m : ℕ) [NeZero m], Nat.Coprime m (geometricConductor E) →
    ∀ χ : DirichletCharacter ℂ m, χ.IsPrimitive →
      ∃ Λ Λ' : ℂ → ℂ, IsBoundedEntireContinuation E χ Λ ∧ IsBoundedEntireContinuation E χ⁻¹ Λ' ∧
        ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∀ s : ℂ,
          Λ s = ε * χ (geometricConductor E) * (gaussSum χ ZMod.stdAddChar / gaussSum χ⁻¹ ZMod.stdAddChar) *
            Λ' (2 - s)

/-! ### Modularity at a given level; Conjecture 11.22 -/

/-- $E$ admits a nonconstant map $X_0(N) \to E$ over $\mathbb Q$ (the condition of D118 at the level $N$). -/
def IsModularOfLevel (E : WeierstrassCurve ℚ) (N : ℕ) : Prop :=
  ∃ (hN : 0 < N) (C : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral C)
    (fC : C ⟶ AlgebraicGeometry.Spec (CommRingCat.of ℚ)),
    IsCanonicalModelX0 N hN fC ∧
      ∃ φ : (C ⟶ E.projModel), φ ≫ E.projModelOver = fC ∧ ∃ x y : C, φ.base x ≠ φ.base y

theorem isModularEllipticCurve_iff_exists_level (E : WeierstrassCurve ℚ) :
    IsModularEllipticCurve E ↔ ∃ N, IsModularOfLevel E N :=
  Iff.rfl

/-- **The Taniyama–Weil conjecture** (Milne, Conjecture 11.22, p. 118), as a predicate: every elliptic curve $E$ over
$\mathbb Q$ admits a nonconstant map $X_0(N) \to E$ over $\mathbb Q$ with $N$ the geometric conductor of $E$. -/
@[kb "milne2017mf" "Section 11, Conjecture 11.22 (pdf p. 118)"]
def TaniyamaWeilConjecture : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], IsModularOfLevel E (geometricConductor E)

/-- The last clause of Conjecture 11.22: the Taniyama–Weil conjecture implies that every elliptic curve over
$\mathbb Q$ is modular (`TaniyamaConjecture`, the hypothesis of Theorem 11.24). -/
theorem TaniyamaWeilConjecture.taniyamaConjecture (h : TaniyamaWeilConjecture) : TaniyamaConjecture :=
  fun E _ ↦ ⟨_, h E⟩

/-! ### Theorems 11.19 and 11.23 -/

/-- **Theorem 11.19** (Milne, p. 117; Weil's converse theorem, the Eichler–Shimura relation and Faltings's isogeny
theorem [unverified]), as a named statement: an elliptic curve $E$ over $\mathbb Q$ is modular if and only if it
satisfies the strong Hasse–Weil conjecture, and in fact then there is a nonconstant map $X_0(N) \to E$ with $N$ the
geometric conductor of $E$. -/
@[kb "milne2017mf" "Section 11, Theorem 11.19 (pdf p. 117)"]
structure ModularIffStrongHasseWeil : Prop where
  strongHasseWeil_of_modular :
    ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], IsModularEllipticCurve E → StrongHasseWeil E
  modularOfConductor_of_strongHasseWeil :
    ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], StrongHasseWeil E → IsModularOfLevel E (geometricConductor E)

/-- **Theorem 11.19** in Milne's form, from the named statement: $E$ is modular if and only if it satisfies the strong
Hasse–Weil conjecture. -/
theorem isModularEllipticCurve_iff_strongHasseWeil (h : ModularIffStrongHasseWeil) (E : WeierstrassCurve ℚ)
    [E.IsElliptic] : IsModularEllipticCurve E ↔ StrongHasseWeil E :=
  ⟨h.strongHasseWeil_of_modular E, fun hE ↦ ⟨_, h.modularOfConductor_of_strongHasseWeil E hE⟩⟩

/-- The "in fact" clause of Theorem 11.19: a modular elliptic curve admits a nonconstant map from $X_0(N)$ with $N$
its geometric conductor. -/
theorem isModularOfLevel_geometricConductor (h : ModularIffStrongHasseWeil) {E : WeierstrassCurve ℚ}
    [E.IsElliptic] (hE : IsModularEllipticCurve E) : IsModularOfLevel E (geometricConductor E) :=
  h.modularOfConductor_of_strongHasseWeil E (h.strongHasseWeil_of_modular E hE)

/-- **Theorem 11.23** (Milne, p. 118): the strong Hasse–Weil conjecture for all elliptic curves over $\mathbb Q$ is
equivalent to the Taniyama–Weil conjecture; proved from Theorem 11.19 (`ModularIffStrongHasseWeil`) as in Milne. -/
@[kb "milne2017mf" "Section 11, Theorem 11.23 (pdf p. 118)"]
theorem forall_strongHasseWeil_iff_taniyamaWeil (h : ModularIffStrongHasseWeil) :
    (∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], StrongHasseWeil E) ↔ TaniyamaWeilConjecture :=
  ⟨fun hS E _ ↦ h.modularOfConductor_of_strongHasseWeil E (hS E),
    fun hT E _ ↦ h.strongHasseWeil_of_modular E ⟨_, hT E⟩⟩

end ModularFormsKB.Milne.Wave4B
