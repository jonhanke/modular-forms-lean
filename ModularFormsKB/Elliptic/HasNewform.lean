import ModularFormsKB.Milne.Wave4B.HasseWeil
import ModularFormsKB.Milne.Wave4B.Faltings
import TauCeti.NumberTheory.ModularForms.Newforms.Newform
import TauCeti.AlgebraicGeometry.EllipticCurve.LFunction.Isogeny

/-!
# Elliptic curves with a newform: `HasNewform`, the modularity theorem, Eichler–Shimura, Milne 11.21

## Definitions and named statements
- `HasNewform E N f`: $E$ an elliptic curve over $\mathbb Q$, $f$ a Tau Ceti newform of level $N$ and weight
  $2$ with trivial nebentypus, whose Fourier coefficients are those of Mathlib's $L$-function of $E$:
  $a_n(f) = $ `E.LFunction n` for every $n$. This is a predicate (a condition on $E$, $N$, $f$), not a cited result.
- `ModularityTheorem` (Wiles 1995, Taylor–Wiles 1995, Breuil–Conrad–Diamond–Taylor 2001 [unverified]), a
  named statement: every elliptic curve $E$ over $\mathbb Q$ has a newform of level the geometric conductor of $E$
  (`Milne.Wave4B.geometricConductor`, Milne's D116; its agreement with Ogg's formula is a loose end).
- `EichlerShimuraCurve` (Shimura 1971, Theorem 7.14 [unverified]; Milne, Theorem 11.14 and the paragraph
  before 11.21), a named statement: every newform of weight $2$, trivial nebentypus and rational coefficients has an
  elliptic curve with these coefficients.
- `LevelEqConductor` (Carayol 1986 [unverified]; Milne quotes it after 11.21 as "the level equals the conductor"),
  a named statement: if $E$ has a newform of level $N$, then $N$ is the geometric conductor of $E$.

## Proved here
- `HasNewform.eq`: the newform of $E$ at a given level is unique (Tau Ceti
  `Newform.injective_qExpansion_coeff_pnat`); `HasNewform.coeff_int`: its coefficients are integers.
- `HasNewform.of_isogeny`: isogenous curves share their newforms (Tau Ceti `Isogeny.LFunction_eq`).
- `exists_hasNewform`: from `ModularityTheorem`, every $E$ has a newform of level its conductor, unique by
  `HasNewform.eq`.
- **Milne Proposition 11.21**, the bijection between isogeny classes of elliptic curves of conductor $N$ and
  newforms of level $N$ with rational coefficients, as four statements:
  `newform_of_conductor` (the map, from `ModularityTheorem`), `newform_eq_of_isogeny` (it is constant on isogeny
  classes, unconditional), `isogenous_of_hasNewform` (injective, from Faltings's `FaltingsIsogenyTheorem`, Milne
  11.20) and `exists_curve_of_newform` (surjective, from `EichlerShimuraCurve` and `LevelEqConductor`).

## Conventions
The coefficients $a_n(f)$ are `(qExpansion 1 f.toCuspForm).coeff n`, the $q$-expansion at $\infty$ of width $1$
(Tau Ceti's newforms are forms on $\Gamma_1(N)$). Mathlib's `E.LFunction` is an arithmetic function, so
`E.LFunction 0 = 0`, which matches $a_0(f) = 0$ for a cusp form. "Rational coefficients" is
$a_n(f) \in \mathbb Q$ for all $n$; then they are integers by Shimura's construction, but the statement asks only for
rationality, as Milne does.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups

namespace ModularFormsKB.Elliptic

open HeckeRing.GL2 ModularFormsKB.Milne.Wave4B

/-- The geometric conductor of an elliptic curve is positive, as an instance (it is the level of Tau Ceti's
newforms in `ModularityTheorem`). -/
instance geometricConductor.neZero (E : WeierstrassCurve ℚ) [E.IsElliptic] : NeZero (geometricConductor E) :=
  ⟨(geometricConductor_pos E).ne'⟩

/-- **$E$ has the newform $f$ of level $N$** (row 19): $f$ is a Tau Ceti newform of weight $2$ on $\Gamma_1(N)$ with
trivial nebentypus whose Fourier coefficients are those of Mathlib's $L$-function of $E$,
$a_n(f) = $ `E.LFunction n` for every $n \ge 0$. A predicate, not a cited result. -/
@[kb "milne2017mf" "Section 11, before Thm. 11.19 and 11.21: E corresponds to the newform f, L(E,s) = L(f,s)"]
structure HasNewform (E : WeierstrassCurve ℚ) (N : ℕ) [NeZero N] (f : Newform N 2) : Prop where
  /-- The nebentypus is trivial: $f$ is a form on $\Gamma_0(N)$. -/
  χ_eq_one : f.χ = 1
  /-- The Fourier coefficients of $f$ are those of $L(E, s)$. -/
  coeff_eq : ∀ n : ℕ, (qExpansion 1 f.toCuspForm).coeff n = (E.LFunction n : ℂ)

namespace HasNewform

variable {E E' : WeierstrassCurve ℚ} {N : ℕ} [NeZero N] {f g : Newform N 2}

/-- **The newform of $E$ at a given level is unique** (row 19): two newforms of level $N$ with the coefficients of
$L(E, s)$ are equal (Tau Ceti `Newform.injective_qExpansion_coeff_pnat`). -/
theorem eq (hf : HasNewform E N f) (hg : HasNewform E N g) : f = g :=
  Newform.injective_qExpansion_coeff_pnat <| funext fun n ↦ by
    show (qExpansion 1 f.toCuspForm).coeff n = (qExpansion 1 g.toCuspForm).coeff n
    rw [hf.coeff_eq, hg.coeff_eq]

/-- **The coefficients of the newform of $E$ are integers** (row 19). -/
theorem coeff_int (hf : HasNewform E N f) (n : ℕ) : ∃ m : ℤ, (qExpansion 1 f.toCuspForm).coeff n = m :=
  ⟨_, hf.coeff_eq n⟩

/-- The coefficients of the newform of $E$ are rational. -/
theorem coeff_rat (hf : HasNewform E N f) (n : ℕ) : ∃ r : ℚ, (qExpansion 1 f.toCuspForm).coeff n = r :=
  ⟨E.LFunction n, by rw [hf.coeff_eq]; push_cast; rfl⟩

/-- **Isogenous curves share their newforms**: $L(E, s)$ is an isogeny invariant (Tau Ceti `Isogeny.LFunction_eq`). -/
theorem of_isogeny [E.IsElliptic] [E'.IsElliptic] (φ : TauCeti.Isogeny E.toAffine E'.toAffine)
    (hf : HasNewform E N f) : HasNewform E' N f :=
  ⟨hf.χ_eq_one, fun n ↦ by rw [hf.coeff_eq, φ.LFunction_eq]⟩

/-- Two curves with the same newform have the same $L$-function. -/
theorem LFunction_eq (hf : HasNewform E N f) (hf' : HasNewform E' N f) : E.LFunction = E'.LFunction := by
  ext n
  exact_mod_cast (hf.coeff_eq n).symm.trans (hf'.coeff_eq n)

end HasNewform

/-! ### Row 20: the modularity theorem -/

/-- **The modularity theorem** (row 20; Wiles 1995, Taylor–Wiles 1995, Breuil–Conrad–Diamond–Taylor 2001
[unverified]; Milne, Theorem 11.24 and Conjecture 11.22 in analytic form), as a named statement: every elliptic curve
$E$ over $\mathbb Q$ has a newform of weight $2$ and trivial nebentypus of level $N$ the geometric conductor of $E$,
with $a_n(f) = $ `E.LFunction n` for every $n$. -/
@[kb "milne2017mf" "Section 11, Thm. 11.24 / Conj. 11.22 in the form L(E,s) = L(f,s), f a newform of level N_E"]
structure ModularityTheorem : Prop where
  exists_newform : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    ∃ f : Newform (geometricConductor E) 2, HasNewform E (geometricConductor E) f

/-- **Row 20**: from `ModularityTheorem`, every elliptic curve over $\mathbb Q$ has a unique newform of level its
geometric conductor with the coefficients of $L(E, s)$. -/
theorem exists_hasNewform (h : ModularityTheorem) (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃! f : Newform (geometricConductor E) 2, HasNewform E (geometricConductor E) f := by
  obtain ⟨f, hf⟩ := h.exists_newform E
  exact ⟨f, hf, fun g hg ↦ hg.eq hf⟩

/-! ### Row 24: Eichler–Shimura, Carayol, and Milne Proposition 11.21 -/

/-- **The Eichler–Shimura construction** (row 24; Shimura 1971, Theorem 7.14 [unverified]; Milne, Theorem 11.14 and
before 11.21), as a named statement: every newform of weight $2$, trivial nebentypus and rational Fourier coefficients
has an elliptic curve $E$ over $\mathbb Q$ with $L(E, s) = L(f, s)$ (a quotient of the Jacobian of $X_0(N)$). -/
@[kb "milne2017mf" "Section 11, Thm. 11.14 and before Prop. 11.21 (Eichler-Shimura: newform with rational coefficients gives E)"]
structure EichlerShimuraCurve : Prop where
  exists_curve : ∀ (N : ℕ) [NeZero N] (f : Newform N 2), f.χ = 1 →
    (∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 f.toCuspForm).coeff n = r) →
      ∃ E : WeierstrassCurve ℚ, E.IsElliptic ∧ HasNewform E N f

/-- **The level of the newform is the conductor** (Carayol 1986 [unverified]; Milne, after Proposition 11.21), as a
named statement: if $E$ has a newform of level $N$, then $N$ is the geometric conductor of $E$. -/
@[kb "milne2017mf" "Section 11, after Prop. 11.21: the level of f equals the conductor of E (Carayol)"]
structure LevelEqConductor : Prop where
  level_eq : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2),
    HasNewform E N f → N = geometricConductor E

/-- **Milne Proposition 11.21, the map** (from `ModularityTheorem`): an elliptic curve of conductor $N$ has a newform of
level $N$, with rational coefficients. -/
@[kb "milne2017mf" "Section 11, Prop. 11.21 (pdf p. 118): the map E ↦ f_E"]
theorem newform_of_conductor (h : ModularityTheorem) (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N]
    (hN : geometricConductor E = N) :
    ∃ f : Newform N 2, HasNewform E N f ∧ f.χ = 1 ∧ ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 f.toCuspForm).coeff n = r := by
  subst hN
  obtain ⟨f, hf⟩ := h.exists_newform E
  exact ⟨f, hf, hf.χ_eq_one, hf.coeff_rat⟩

/-- **Milne Proposition 11.21, the map is constant on isogeny classes** (unconditional): isogenous curves have the
same newform. -/
@[kb "milne2017mf" "Section 11, Prop. 11.21 (pdf p. 118): f_E depends only on the isogeny class"]
theorem newform_eq_of_isogeny {E E' : WeierstrassCurve ℚ} [E.IsElliptic] [E'.IsElliptic] {N : ℕ} [NeZero N]
    {f f' : Newform N 2} (φ : TauCeti.Isogeny E.toAffine E'.toAffine) (hf : HasNewform E N f)
    (hf' : HasNewform E' N f') : f = f' :=
  (hf.of_isogeny φ).eq hf'

/-- **Milne Proposition 11.21, injectivity** (from Faltings's theorem, Milne 11.20): two elliptic curves with the
same newform are isogenous. -/
@[kb "milne2017mf" "Section 11, Prop. 11.21 (pdf p. 118): injectivity, by Faltings (Thm. 11.20)"]
theorem isogenous_of_hasNewform (hF : FaltingsIsogenyTheorem) {E E' : WeierstrassCurve ℚ} [hE : E.IsElliptic]
    [hE' : E'.IsElliptic] {N : ℕ} [NeZero N] {f : Newform N 2} (hf : HasNewform E N f) (hf' : HasNewform E' N f) :
    Nonempty (TauCeti.Isogeny E.toAffine E'.toAffine) :=
  hF.isogenous E E' hE hE' (hf.LFunction_eq hf')

/-- **Milne Proposition 11.21, surjectivity** (from `EichlerShimuraCurve` and `LevelEqConductor`): every newform of
level $N$, weight $2$, trivial nebentypus and rational coefficients comes from an elliptic curve of conductor $N$. -/
@[kb "milne2017mf" "Section 11, Prop. 11.21 (pdf p. 118): surjectivity, by Eichler-Shimura and Carayol"]
theorem exists_curve_of_newform (hES : EichlerShimuraCurve) (hC : LevelEqConductor) {N : ℕ} [NeZero N]
    (f : Newform N 2) (hχ : f.χ = 1) (hrat : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 f.toCuspForm).coeff n = r) :
    ∃ E : WeierstrassCurve ℚ, ∃ _ : E.IsElliptic, HasNewform E N f ∧ geometricConductor E = N := by
  obtain ⟨E, hE, hf⟩ := hES.exists_curve N f hχ hrat
  exact ⟨E, hE, hf, (hC.level_eq E N f hf).symm⟩

end ModularFormsKB.Elliptic
