import ModularFormsKB.Iwaniec1997.Kloosterman

/-!
# Iwaniec, Chapter 4: evaluations and bounds for Kloosterman sums (statements)

H. Iwaniec, *Topics in Classical Automorphic Forms* (`iwaniec1997`), Sections 4.3, 4.4 and 4.6. Page numbers are printed
pages.

This file records the book's results on Kloosterman and Salié sums that are **not proved here** as named
propositions (definitions of type `Prop`), so that later work can prove them or use them as explicit hypotheses:

- Selberg's identity (4.10): `SelbergIdentity`; its consequence (4.11) is proved from it
  (`kloosterman_eq_kloosterman_mul_one_of_selberg`).
- Salié's evaluations: Lemma 4.1 (`SalieLemma41`), Lemma 4.2 (`SalieLemma42`), Proposition 4.3
  (`SalieProposition43`); the bound Corollary 4.4 (`KloostermanPrimePowerBound`).
- Weil's bound (4.19) at prime moduli, a consequence of the Riemann hypothesis for curves over finite fields (Weil
  1948), is the **named input** `WeilKloostermanBound`. The Riemann hypothesis for curves is proved in this repository
  (`ModularFormsKB.Milne.weilCurveTheorem`), but the reduction from Kloosterman sums to the curve
  $y^p - y = \ldots$ (or to $\ell$-adic sheaves) is not formalized, so the bound is assumed, not proved.
- Theorem 4.5, $|S(m,n;c)| \le (m,n,c)^{1/2} c^{1/2}\tau(c)$: `KloostermanWeilBound`.
- Lemma 4.8 (the quadratic Gauss sum): `GaussSumEvaluation`; Lemma 4.9 (`SalieLemma49`) and Corollary 4.10
  (`SalieBound`).

The power moments (4.21) are defined (`kloostermanMoment`); their evaluations (4.22), (4.23) are proved in
`ModularFormsKB.Iwaniec1997.KloostermanMoments`.
-/

open Complex Finset
open scoped ComplexConjugate

noncomputable section

namespace ModularFormsKB.Iwaniec1997

/-- The divisor function $\tau(c)$, the number of positive divisors of $c$. -/
def divisorCount (c : ℕ) : ℕ := c.divisors.card

/-- **Selberg's identity (4.10)** (not proved here): for $c \ge 1$,
$S(m,n;c) = \sum_{d \mid (c,m,n)} d\, S(mn d^{-2}, 1; c d^{-1})$. -/
@[kb "iwaniec1997" "Section 4.3, (4.10), p. 59"]
def SelbergIdentity : Prop :=
  ∀ (m n : ℤ) (c : ℕ), 0 < c →
    kloosterman m n c = ∑ d ∈ (Nat.gcd c (Int.gcd m n)).divisors,
      (d : ℂ) * kloosterman (m * n / ((d : ℤ) ^ 2)) 1 (c / d)

/-- **(4.11)**, from Selberg's identity (4.10): if $(c,m,n) = 1$ then $S(m,n;c) = S(mn,1;c)$. -/
@[kb "iwaniec1997" "Section 4.3, (4.11), p. 59"]
theorem kloosterman_eq_kloosterman_mul_one_of_selberg (hS : SelbergIdentity) {m n : ℤ} {c : ℕ} (hc : 0 < c)
    (h : Nat.gcd c (Int.gcd m n) = 1) : kloosterman m n c = kloosterman (m * n) 1 c := by
  rw [hS m n c hc, h]
  simp

/-- The value $e(x/c)$ for an integer $x$, as an element of $\mathbb C$: `ZMod.stdAddChar` at $x \bmod c$. -/
abbrev eMod (c : ℕ) [NeZero c] (x : ℤ) : ℂ := ZMod.stdAddChar (x : ZMod c)

/-- **Lemma 4.1** (Salié; not proved here): if $c = p^{2\alpha}$ with $\alpha \ge 1$ and $(c, 2n) = 1$, then
$S(n,n;c) = c^{1/2}\big(e(2n/c) + e(-2n/c)\big)$. -/
@[kb "iwaniec1997" "Section 4.3, Lemma 4.1, (4.13), p. 59"]
def SalieLemma41 : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), ∀ (α : ℕ), 1 ≤ α → ∀ (n : ℤ), IsCoprime ((p ^ (2 * α) : ℕ) : ℤ) (2 * n) →
    haveI : NeZero (p ^ (2 * α)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    kloosterman n n (p ^ (2 * α)) =
      (Real.sqrt (p ^ (2 * α) : ℕ) : ℂ) * (eMod (p ^ (2 * α)) (2 * n) + eMod (p ^ (2 * α)) (-2 * n))

/-- **Lemma 4.2** (Salié; not proved here): if $c = p^{2\alpha+1}$ with $\alpha \ge 1$ and $(c, 2n) = 1$, then
$S(n,n;c) = 2\big(\tfrac{n}{c}\big) c^{1/2}\,\mathrm{Re}\,\varepsilon_c e(2n/c)$. -/
@[kb "iwaniec1997" "Section 4.3, Lemma 4.2, (4.14), p. 60"]
def SalieLemma42 : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), ∀ (α : ℕ), 1 ≤ α → ∀ (n : ℤ), IsCoprime ((p ^ (2 * α + 1) : ℕ) : ℤ) (2 * n) →
    haveI : NeZero (p ^ (2 * α + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    kloosterman n n (p ^ (2 * α + 1)) =
      2 * (jacobiSym n (p ^ (2 * α + 1)) : ℂ) * (Real.sqrt (p ^ (2 * α + 1) : ℕ) : ℂ) *
        ((epsilonFactor (p ^ (2 * α + 1)) * eMod (p ^ (2 * α + 1)) (2 * n)).re : ℂ)

/-- **Proposition 4.3** (Salié; not proved here): if $c = p^\beta$ with $\beta \ge 2$ and $(c, 2n) = 1$, then
$S(n,n;c) = 2\big(\tfrac{n}{c}\big) c^{1/2}\,\mathrm{Re}\,\varepsilon_c e(2n/c)$. -/
@[kb "iwaniec1997" "Section 4.3, Proposition 4.3, (4.16), p. 60"]
def SalieProposition43 : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), ∀ (β : ℕ), 2 ≤ β → ∀ (n : ℤ), IsCoprime ((p ^ β : ℕ) : ℤ) (2 * n) →
    haveI : NeZero (p ^ β) := ⟨pow_ne_zero _ hp.ne_zero⟩
    kloosterman n n (p ^ β) =
      2 * (jacobiSym n (p ^ β) : ℂ) * (Real.sqrt (p ^ β : ℕ) : ℂ) *
        ((epsilonFactor (p ^ β) * eMod (p ^ β) (2 * n)).re : ℂ)

/-- **Corollary 4.4** (not proved here): if $c = p^\beta$ with $\beta \ge 2$ and $(c, 2mn) = 1$, then
$|S(m,n;c)| \le 2c^{1/2}$. -/
@[kb "iwaniec1997" "Section 4.3, Corollary 4.4, (4.17), p. 61"]
def KloostermanPrimePowerBound : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (β : ℕ), 2 ≤ β → ∀ (m n : ℤ), IsCoprime ((p ^ β : ℕ) : ℤ) (2 * m * n) →
    ‖kloosterman m n (p ^ β)‖ ≤ 2 * Real.sqrt (p ^ β : ℕ)

/-- **Weil's bound (4.19)**, a named input (Weil 1948, from the Riemann hypothesis for curves over finite fields):
for a prime $p$ and integers $m, n$ not both divisible by $p$, $|S(m,n;p)| \le 2p^{1/2}$. The book states (4.19)
without the coprimality condition written out; it is needed, since $S(0,0;p) = p - 1$. When $p$ divides exactly one
of $m, n$ the sum is a Ramanujan sum equal to $-1$, so the bound then holds trivially. -/
@[kb "iwaniec1997" "Section 4.3, Weil's bound (4.18), (4.19), p. 61"]
structure WeilKloostermanBound : Prop where
  /-- The bound at a prime modulus. -/
  bound : ∀ (p : ℕ), p.Prime → ∀ (m n : ℤ), ¬ ((p : ℤ) ∣ m ∧ (p : ℤ) ∣ n) →
    ‖kloosterman m n p‖ ≤ 2 * Real.sqrt p

/-- **Theorem 4.5** (not proved here): for any $c \ge 1$ and integers $m, n$,
$|S(m,n;c)| \le (m,n,c)^{1/2} c^{1/2} \tau(c)$. -/
@[kb "iwaniec1997" "Section 4.3, Theorem 4.5, (4.20), p. 61"]
def KloostermanWeilBound : Prop :=
  ∀ (c : ℕ), 1 ≤ c → ∀ (m n : ℤ),
    ‖kloosterman m n c‖ ≤
      Real.sqrt (Nat.gcd (Int.gcd m n) c) * Real.sqrt c * divisorCount c

/-- **The power moments (4.21)**: $V_k(p) = \sum^*_{a \bmod p} S^k(a,1;p)$, the sum over $a \not\equiv 0$. -/
@[kb "iwaniec1997" "Section 4.4, (4.21), p. 61"]
def kloostermanMoment (k p : ℕ) [NeZero p] : ℂ :=
  ∑ a : (ZMod p)ˣ, (kloostermanMod p (a : ZMod p) 1) ^ k

/-- **Lemma 4.8** (not proved here): if $(c, 2n) = 1$ then $g(n,c) = \big(\tfrac{n}{c}\big)\varepsilon_c c^{1/2}$. -/
@[kb "iwaniec1997" "Section 4.6, Lemma 4.8, (4.38), p. 66"]
def GaussSumEvaluation : Prop :=
  ∀ (c : ℕ) [NeZero c] (n : ℤ), IsCoprime (c : ℤ) (2 * n) →
    quadGaussSum n c = (jacobiSym n c : ℂ) * epsilonFactor c * (Real.sqrt c : ℂ)

/-- **Lemma 4.9** (not proved here): if $(c, 2n) = 1$ then
$T(m,n;c) = \big(\tfrac{n}{c}\big) g(c) \sum_{y^2 \equiv mn \,(c)} e(2y/c)$, where $g(c) = g(1,c)$. -/
@[kb "iwaniec1997" "Section 4.6, Lemma 4.9, (4.44), p. 68"]
def SalieLemma49 : Prop :=
  ∀ (c : ℕ) [NeZero c] (m n : ℤ), IsCoprime (c : ℤ) (2 * n) →
    salie m n c = (jacobiSym n c : ℂ) * quadGaussSum 1 c *
      ∑ y ∈ (univ : Finset (ZMod c)).filter (fun y ↦ y ^ 2 = ((m * n : ℤ) : ZMod c)),
        ZMod.stdAddChar (2 * y)

/-- **Corollary 4.10** (not proved here): if $(c, 2n) = 1$ then $|T(m,n;c)| \le c^{1/2}\tau(c)$. -/
@[kb "iwaniec1997" "Section 4.6, Corollary 4.10, (4.45), p. 68"]
def SalieBound : Prop :=
  ∀ (c : ℕ) [NeZero c] (m n : ℤ), IsCoprime (c : ℤ) (2 * n) →
    ‖salie m n c‖ ≤ Real.sqrt c * divisorCount c

end ModularFormsKB.Iwaniec1997
