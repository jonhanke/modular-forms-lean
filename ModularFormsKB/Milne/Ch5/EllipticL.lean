import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.LSeries.Basic
import ModularFormsKB.Citation
/-!
# Milne, Chapter 5: the $L$-function of an elliptic curve over $\mathbb Q$ (p. 69)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf p. 69.

Milne defines $L(E, s) = \prod_{p\ \mathrm{good}}(1 - a(p)p^{-s} + p^{1-2s})^{-1}\prod_{p\ \mathrm{bad}}(\cdots)$ with
$1 - a(p) + p = \#E(\mathbb F_p)$ for good $p$, leaving the factors at the bad primes unspecified. Only the good part
is formalized: for a Weierstrass equation $W$ with integer coefficients, a prime $p$ is good when $p \nmid \Delta(W)$,
$\#E(\mathbb F_p)$ counts the points of the reduction including the point at infinity (`ellipticPointCount`), and the
good part of the Euler product is `ellipticLGood`. (Milne's "good" refers to a minimal model; for a non-minimal integral
model a few good primes are treated as bad.)

## Items
- $a(p)$ (`ellipticAp`) and the good part of $L(E, s)$ (`ellipticLGood`), p. 69.
-/

namespace ModularFormsKB.Milne

/-- $\#E(\mathbb F_p)$: the number of points (including the point at infinity) of the reduction of $W$ modulo $p$. -/
noncomputable def ellipticPointCount (W : WeierstrassCurve ℤ) (p : ℕ) : ℕ :=
  Nat.card (W.map (Int.castRingHom (ZMod p))).toAffine.Point

/-- **$a(p)$** (p. 69): $1 - a(p) + p = \#E(\mathbb F_p)$, i.e. $a(p) = p + 1 - \#E(\mathbb F_p)$. -/
@[kb "milne2017mf" "Section 5, the L-function of an elliptic curve, a(p) (pdf p. 69)"]
noncomputable def ellipticAp (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  (p : ℤ) + 1 - ellipticPointCount W p

/-- **The good part of $L(E, s)$** (p. 69): $\prod_{p \nmid \Delta(W)}(1 - a(p)p^{-s} + p^{1-2s})^{-1}$. -/
@[kb "milne2017mf" "Section 5, the L-function of an elliptic curve (pdf p. 69); good primes only"]
noncomputable def ellipticLGood (W : WeierstrassCurve ℤ) (s : ℂ) : ℂ :=
  ∏' p : {p : Nat.Primes // ¬ (p : ℤ) ∣ W.Δ},
    (1 - (ellipticAp W p : ℂ) * ((p : ℕ) : ℂ) ^ (-s) + ((p : ℕ) : ℂ) ^ (1 - 2 * s))⁻¹

/-- $1 - a(p) + p = \#E(\mathbb F_p)$, the defining relation (p. 69). -/
@[kb "milne2017mf" "Section 5, the L-function of an elliptic curve, a(p) (pdf p. 69)"]
theorem one_sub_ellipticAp_add (W : WeierstrassCurve ℤ) (p : ℕ) :
    1 - ellipticAp W p + p = ellipticPointCount W p := by
  unfold ellipticAp
  ring

end ModularFormsKB.Milne
