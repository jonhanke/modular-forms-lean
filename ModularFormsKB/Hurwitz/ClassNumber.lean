/-
# Hurwitz class numbers, sums of three squares, and the divisor functions of the class number relations

The **Hurwitz class number** $H(D)$, $D \ge 1$, is the number of
$\mathrm{SL}_2(\mathbb Z)$-classes of positive definite integral binary quadratic forms $ax^2+bxy+cy^2$ of discriminant
$b^2-4ac=-D$ (primitive or not), where the classes of the multiples of $x^2+y^2$ count $1/2$ and those of the multiples of
$x^2+xy+y^2$ count $1/3$; $H(0) = -1/12$ (Zagier 1975 `zagier1975`; Hirzebruch–Zagier 1976 `hirzebruchzagier1976`, §2.2;
Cohen 1975 `cohen1975` [unverified]).

**Imported from Tau Ceti, not reproved.** Tau Ceti defines `TauCeti.hurwitzClassNumber D` as the weighted count of the
reduced forms $|b| \le a \le c$ (with $b \ge 0$ if $|b| = a$ or $a = c$), and proves that it is the weighted count of
classes, each class weighted by $2/|\mathrm{Stab}|$ (`TauCeti.hurwitzClassNumber_eq_finsum`, Chris Birkbeck). We use that
definition as is (`hurwitzClassNumber_eq_classCount` restates the comparison here, with the citation).

**Defined here.** $r_3(n) = \#\{(x,y,z) \in \mathbb Z^3 : x^2+y^2+z^2 = n\}$ (`r3`, a finite decidable count over the box
$|x|,|y|,|z| \le \sqrt n$, with `mem_threeSquareReps` showing the box loses nothing) and
$\lambda(n) = \sum_{d \mid n} \min(d, n/d)$ (`kroneckerLambda`), the correction term of the Kronecker–Hurwitz relation.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import TauCeti.NumberTheory.BinaryQuadraticForm.Reduction
import ModularFormsKB.Citation
namespace ModularFormsKB.Hurwitz

open Finset MulAction
open scoped MatrixGroups

/-- **The Hurwitz class number counts classes of forms** (Tau Ceti's `TauCeti.hurwitzClassNumber_eq_finsum`; Zagier 1975
`zagier1975` for the definition [unverified]): for $D \ne 0$, $H(D) = \sum_{\text{classes}} 2/|\mathrm{Stab}|$ over the
$\mathrm{SL}_2(\mathbb Z)$-classes of positive definite forms of discriminant $-D$; the weight is $1/2$ on the classes of
multiples of $x^2+y^2$, $1/3$ on those of multiples of $x^2+xy+y^2$ and $1$ otherwise. -/
@[kb "zagier1975" "H(D) counts SL2(Z)-classes of positive definite forms of discriminant -D with weights 2/|Stab| (Tau Ceti) [unverified]"]
theorem hurwitzClassNumber_eq_classCount (D : ℕ) [NeZero D] :
    TauCeti.hurwitzClassNumber D =
      ∑ᶠ q : orbitRel.Quotient SL(2, ℤ) (TauCeti.BinaryQuadraticForm.posDef D),
        2 / (TauCeti.cardStabilizerOnOrbit q : ℚ) :=
  TauCeti.hurwitzClassNumber_eq_finsum D

/-! ### More values -/

/-- $H(11) = 1$: the reduced form $x^2+xy+3y^2$. -/
theorem hurwitzClassNumber_eleven : TauCeti.hurwitzClassNumber 11 = 1 := by decide +kernel

/-- $H(15) = 2$: $x^2+xy+4y^2$ and $2x^2+xy+2y^2$. -/
theorem hurwitzClassNumber_fifteen : TauCeti.hurwitzClassNumber 15 = 2 := by decide +kernel

/-- $H(20) = 2$: $x^2+5y^2$ and $2x^2+2xy+3y^2$. -/
theorem hurwitzClassNumber_twenty : TauCeti.hurwitzClassNumber 20 = 2 := by decide +kernel

/-- $H(23) = 3$: $x^2+xy+6y^2$ and $2x^2\pm xy+3y^2$. -/
theorem hurwitzClassNumber_twentyThree : TauCeti.hurwitzClassNumber 23 = 3 := by decide +kernel

/-! ### Sums of three squares -/

/-- The representations of $n$ as $x^2+y^2+z^2$ with $(x,y,z)$ in the box $|x|,|y|,|z| \le \sqrt n$. -/
def threeSquareReps (n : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  {v ∈ Icc (-(n.sqrt : ℤ)) n.sqrt ×ˢ Icc (-(n.sqrt : ℤ)) n.sqrt ×ˢ Icc (-(n.sqrt : ℤ)) n.sqrt |
    v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = n}

/-- **$r_3(n)$**, the number of $(x,y,z) \in \mathbb Z^3$ with $x^2+y^2+z^2 = n$. -/
def r3 (n : ℕ) : ℕ := #(threeSquareReps n)

/-- An integer with $x^2 \le n$ satisfies $|x| \le \lfloor\sqrt n\rfloor$. -/
theorem mem_Icc_sqrt_of_sq_le {x : ℤ} {n : ℕ} (h : x ^ 2 ≤ n) : x ∈ Icc (-(n.sqrt : ℤ)) n.sqrt := by
  have h1 : x.natAbs ^ 2 ≤ n := by
    have : ((x.natAbs ^ 2 : ℕ) : ℤ) = x ^ 2 := by push_cast; exact sq_abs x
    omega
  have h2 : x.natAbs ≤ n.sqrt := Nat.le_sqrt'.2 h1
  rw [mem_Icc]
  omega

/-- **The box loses nothing:** $(x,y,z) \in$ `threeSquareReps n` exactly when $x^2+y^2+z^2 = n$. -/
@[simp] theorem mem_threeSquareReps {n : ℕ} {v : ℤ × ℤ × ℤ} :
    v ∈ threeSquareReps n ↔ v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = n := by
  refine mem_filter.trans ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  have h1 := sq_nonneg v.1
  have h2 := sq_nonneg v.2.1
  have h3 := sq_nonneg v.2.2
  simp only [mem_product]
  exact ⟨mem_Icc_sqrt_of_sq_le (by linarith), mem_Icc_sqrt_of_sq_le (by linarith),
    mem_Icc_sqrt_of_sq_le (by linarith)⟩

/-- The first values $r_3(0), \dots, r_3(8) = 1, 6, 12, 8, 6, 24, 24, 0, 12$. -/
theorem r3_values : (List.range 9).map r3 = [1, 6, 12, 8, 6, 24, 24, 0, 12] := by decide +kernel

/-! ### The divisor functions -/

/-- **$\lambda(n) = \sum_{d \mid n} \min(d, n/d)$**, the correction term in the Kronecker–Hurwitz class number relation
(Hirzebruch–Zagier 1976 `hirzebruchzagier1976`, §2.2 writes it as $\sum_{d\mid n}\min(d,n/d)$ [unverified]). -/
def kroneckerLambda (n : ℕ) : ℕ := ∑ d ∈ n.divisors, min d (n / d)

end ModularFormsKB.Hurwitz
