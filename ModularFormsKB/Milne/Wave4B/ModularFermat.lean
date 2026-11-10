import ModularFormsKB.Milne.Ch7.CanonicalModel
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ProjModel
import TauCeti.AlgebraicGeometry.EllipticCurve.FreyCurve.Basic
import Mathlib.NumberTheory.FLT.Four

/-!
# Milne, Section 11: modular elliptic curves, the Taniyama conjecture and Fermat's last theorem

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 11, pdf pp. 117–118.

## Items
- **D118** (p. 117): an elliptic curve $E$ over $\mathbb Q$ is **modular** if there is a nonconstant map
  $X_0(N) \to E$ defined over $\mathbb Q$ (`IsModularEllipticCurve`). Here $X_0(N)$ is any canonical model of
  $X_0(N)$ over $\mathbb Q$ in the sense of Section 7 (`IsCanonicalModelX0`, a complete regular curve over
  $\mathbb Q$ with function field $\mathbb Q(j, j_N)$; by Theorem 7.2 it is unique up to isomorphism), $E$ is the
  projective Weierstrass model (Tau Ceti's `WeierstrassCurve.projModel`), and "nonconstant" means that the underlying
  map of topological spaces is not constant.
- **Conjecture 11.22**, the part "every elliptic curve over $\mathbb Q$ is a modular elliptic curve"
  (`TaniyamaConjecture`, a hypothesis, not a result).
- **Theorem 11.25** (Ribet, after Frey; named statement `FreyCurveNotModular`): for a prime $p > 2$ and nonzero
  integers $a, b, c$ with $\gcd(a,b,c) = 1$ and $a^p + b^p = c^p$, the curve $Y^2 = X(X - a^p)(X + b^p)$ is not
  modular. (Tau Ceti's `TauCeti.freyCurve`.)
- **Theorem 11.24**: the Taniyama conjecture implies Fermat's last theorem (`fermatLastTheorem_of_taniyama`),
  proved from Theorem 11.25; the exponent $4$ is Mathlib's `fermatLastTheoremFour`.
-/

open AlgebraicGeometry CategoryTheory

namespace ModularFormsKB.Milne.Wave4B

open ModularFormsKB.Milne

/-- **Modular elliptic curve** (Milne, p. 117; D118): an elliptic curve $E$ over $\mathbb Q$ is modular if for some
$N \ge 1$ there is a nonconstant morphism over $\mathbb Q$ from the canonical model $X_0(N)_{\mathbb Q}$ to $E$. -/
@[kb "milne2017mf" "Section 11, modular elliptic curve, before Remark 11.18 (pdf p. 117)"]
def IsModularEllipticCurve (E : WeierstrassCurve ℚ) : Prop :=
  ∃ (N : ℕ) (hN : 0 < N) (C : Scheme.{0}) (_ : IsIntegral C) (fC : C ⟶ Spec (CommRingCat.of ℚ)),
    IsCanonicalModelX0 N hN fC ∧
      ∃ φ : (C ⟶ E.projModel), φ ≫ E.projModelOver = fC ∧ ∃ x y : C, φ.base x ≠ φ.base y

/-- **The Taniyama conjecture** (Milne, Conjecture 11.22, last clause): every elliptic curve over $\mathbb Q$ is a
modular elliptic curve. A hypothesis of Theorem 11.24, not a cited result. -/
def TaniyamaConjecture : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → IsModularEllipticCurve E

/-- **Theorem 11.25** (Milne; Ribet 1990, after Frey [unverified]), as a named statement: for a prime $p > 2$ and
nonzero integers $a, b, c$ with $\gcd(a, b, c) = 1$ and $a^p + b^p = c^p$, the elliptic curve
$Y^2 = X(X - a^p)(X + b^p)$ over $\mathbb Q$ is not modular. -/
@[kb "milne2017mf" "Section 11, Theorem 11.25 (pdf p. 118)"]
structure FreyCurveNotModular : Prop where
  not_modular : ∀ p : ℕ, p.Prime → 2 < p → ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 →
    ({a, b, c} : Finset ℤ).gcd id = 1 → a ^ p + b ^ p = c ^ p →
      ¬ IsModularEllipticCurve (TauCeti.freyCurve ((a : ℚ) ^ p) ((b : ℚ) ^ p))

/-- The Frey curve of a nontrivial solution is an elliptic curve: its discriminant is
$16\,a^{2p}b^{2p}c^{2p} \ne 0$. -/
theorem isElliptic_freyCurve_of_ne {p : ℕ} {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a ^ p + b ^ p = c ^ p) : (TauCeti.freyCurve ((a : ℚ) ^ p) ((b : ℚ) ^ p)).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, TauCeti.freyCurve_Δ]
  have hc' : ((a : ℚ) ^ p + (b : ℚ) ^ p) = (c : ℚ) ^ p := by exact_mod_cast h
  rw [hc']
  have : (16 : ℚ) * ((a : ℚ) ^ p) ^ 2 * ((b : ℚ) ^ p) ^ 2 * ((c : ℚ) ^ p) ^ 2 ≠ 0 := by
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    have hc'' : (c : ℚ) ≠ 0 := by exact_mod_cast hc
    positivity
  exact this.isUnit

/-- **Theorem 11.24** (Milne, p. 118): the Taniyama conjecture implies Fermat's last theorem, from Theorem 11.25
(`FreyCurveNotModular`). -/
@[kb "milne2017mf" "Section 11, Theorem 11.24 (pdf p. 118)"]
theorem fermatLastTheorem_of_taniyama (hR : FreyCurveNotModular) (hT : TaniyamaConjecture) :
    FermatLastTheorem := by
  refine FermatLastTheorem.of_odd_primes fun p hp hodd ↦ ?_
  have hp2 : 2 < p := by
    rcases hp.eq_two_or_odd' with h | h
    · subst h; exact absurd hodd (by decide)
    · exact lt_of_le_of_ne hp.two_le (fun h2 ↦ by subst h2; exact absurd hodd (by decide))
  rw [fermatLastTheoremFor_iff_int]
  refine fermatLastTheoremWith_of_fermatLastTheoremWith_coprime fun a b c ha hb hc hgcd heq ↦ ?_
  have hE := isElliptic_freyCurve_of_ne ha hb hc heq
  exact hR.not_modular p hp hp2 a b c ha hb hc hgcd heq (hT _ hE)

end ModularFormsKB.Milne.Wave4B
