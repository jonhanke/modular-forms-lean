import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import ModularFormsKB.Citation
/-!
# Iwaniec, Chapter 4: the classical Kloosterman sum

H. Iwaniec, *Topics in Classical Automorphic Forms* (`iwaniec1997`), Sections 4.2 and 4.3. Page numbers are the printed
pages (the pdf page is the printed page plus 7).

The classical Kloosterman sum (4.4) is
$$S(m,n;c) = \sum_{ad \equiv 1 \ (\mathrm{mod}\ c)} e\Big(\frac{am + dn}{c}\Big),\qquad e(x) = e^{2\pi i x}.$$
We index it by $d$ running over the units of $\mathbb Z/c$, with $a = \bar d$ the inverse of $d$, and write $e(x/c)$
as Mathlib's standard additive character `ZMod.stdAddChar` of $\mathbb Z/c$ (`ZMod.stdAddChar_coe`). The primary
definition `kloostermanMod c m n` takes $m, n$ already reduced modulo $c$; `kloosterman m n c` is the book's
$S(m,n;c)$ for integers $m, n$ and a positive modulus $c$.

## Items
- (4.4) `kloosterman`, `kloostermanMod`; the explicit form `kloostermanMod_eq_sum_exp`.
- (4.8) `kloosterman_comm`.
- (4.9) `kloosterman_mul_left_eq_mul_right`.
- $S(m,n;c)$ is real: `conj_kloosterman` (used for (4.18) and the angle (4.32)).
- The trivial bound $|S(m,n;c)| \le \varphi(c)$ (`norm_kloosterman_le_totient`), the modulus $c = 1$
  (`kloosterman_one`), and $S(0,0;c) = \varphi(c)$ (`kloosterman_zero_zero`).
- The Salié sum (4.36) `salie`, the quadratic Gauss sum (4.37) `quadGaussSum`, the factor (4.39) `epsilonFactor`.
-/

open Complex Finset
open scoped ComplexConjugate Real

noncomputable section

namespace ModularFormsKB.Iwaniec1997

/-- The classical Kloosterman sum with arguments reduced modulo $c$:
$\sum_{d \in (\mathbb Z/c)^\times} e\big((m\bar d + nd)/c\big)$, where $e(x/c)$ is `ZMod.stdAddChar`. -/
@[kb "iwaniec1997" "Section 4.2, (4.4), p. 58"]
def kloostermanMod (c : ℕ) [NeZero c] (m n : ZMod c) : ℂ :=
  ∑ d : (ZMod c)ˣ, ZMod.stdAddChar (m * ((d⁻¹ : (ZMod c)ˣ) : ZMod c) + n * (d : ZMod c))

/-- **The classical Kloosterman sum** (4.4): for integers $m, n$ and a positive integer $c$,
$S(m,n;c) = \sum_{ad\equiv 1\,(c)} e\big((am + dn)/c\big)$. The book only uses $c \ge 1$; the value at $c = 0$ is set
to $0$ so that sums over moduli can be written without side conditions. -/
@[kb "iwaniec1997" "Section 4.2, (4.4), p. 58; also (3.27), p. 55"]
def kloosterman (m n : ℤ) (c : ℕ) : ℂ :=
  if h : c = 0 then 0 else
    haveI : NeZero c := ⟨h⟩
    kloostermanMod c (m : ZMod c) (n : ZMod c)

/-- The definition of `kloosterman` for a positive modulus. -/
theorem kloosterman_def (m n : ℤ) (c : ℕ) [NeZero c] :
    kloosterman m n c = kloostermanMod c (m : ZMod c) (n : ZMod c) := by
  simp [kloosterman, NeZero.ne c]

/-- The junk value $S(m,n;0) = 0$. -/
@[simp] theorem kloosterman_zero_modulus (m n : ℤ) : kloosterman m n 0 = 0 := by
  simp [kloosterman]

/-- $S(m,n;c)$ only depends on $m$ and $n$ modulo $c$. -/
theorem kloosterman_congr {m m' n n' : ℤ} {c : ℕ} (hm : (m : ZMod c) = m') (hn : (n : ZMod c) = n') :
    kloosterman m n c = kloosterman m' n' c := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have : NeZero c := ⟨hc⟩
  simp only [kloosterman_def, hm, hn]

/-- The explicit form of (4.4): with $a \bar d$ and $d$ lifted to integers $a, d$ (any lifts),
the summand is $e^{2\pi i (am + dn)/c}$. -/
theorem kloostermanMod_eq_sum_exp (c : ℕ) [NeZero c] (m n : ℤ) :
    kloostermanMod c m n = ∑ d : (ZMod c)ˣ,
      exp (2 * π * I * ((((d⁻¹ : (ZMod c)ˣ) : ZMod c).val : ℤ) * m + ((d : ZMod c).val : ℤ) * n) / c) := by
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  trans ZMod.stdAddChar
    ((((((d⁻¹ : (ZMod c)ˣ) : ZMod c).val : ℤ) * m + ((d : ZMod c).val : ℤ) * n : ℤ)) : ZMod c)
  · congr 1
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id]
    ring
  · rw [ZMod.stdAddChar_coe]
    push_cast
    ring_nf

/-- **(4.8)**: $S(m,n;c) = S(n,m;c)$. -/
@[kb "iwaniec1997" "Section 4.3, (4.8), p. 59"]
theorem kloostermanMod_comm (c : ℕ) [NeZero c] (m n : ZMod c) :
    kloostermanMod c m n = kloostermanMod c n m := by
  unfold kloostermanMod
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun d ↦ ?_
  simp only [Equiv.inv_apply, inv_inv]
  rw [add_comm]

/-- **(4.8)**: $S(m,n;c) = S(n,m;c)$. -/
@[kb "iwaniec1997" "Section 4.3, (4.8), p. 59"]
theorem kloosterman_comm (m n : ℤ) (c : ℕ) : kloosterman m n c = kloosterman n m c := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have : NeZero c := ⟨hc⟩
  simp only [kloosterman_def, kloostermanMod_comm c (m : ZMod c)]

/-- **(4.9)** with the multiplier a unit $u$ of $\mathbb Z/c$: $S(um,n;c) = S(m,un;c)$. -/
theorem kloostermanMod_unit_mul (c : ℕ) [NeZero c] (u : (ZMod c)ˣ) (m n : ZMod c) :
    kloostermanMod c (u * m) n = kloostermanMod c m (u * n) := by
  unfold kloostermanMod
  refine Fintype.sum_equiv (Equiv.mulLeft u⁻¹) _ _ fun d ↦ ?_
  simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, Units.val_mul]
  congr 1
  have hu : (u : ZMod c) * ((u⁻¹ : (ZMod c)ˣ) : ZMod c) = 1 := by simp
  linear_combination (-(n * (d : ZMod c))) * hu

/-- **(4.9)**: $S(am,n;c) = S(m,an;c)$ if $(a,c) = 1$. -/
@[kb "iwaniec1997" "Section 4.3, (4.9), p. 59"]
theorem kloosterman_mul_left_eq_mul_right {a : ℤ} (m n : ℤ) (c : ℕ) [NeZero c] (ha : IsCoprime a (c : ℤ)) :
    kloosterman (a * m) n c = kloosterman m (a * n) c := by
  have hu : IsUnit (a : ZMod c) := by
    obtain ⟨u, v, huv⟩ := ha
    have h := congrArg (Int.cast : ℤ → ZMod c) huv
    push_cast at h
    rw [ZMod.natCast_self, mul_zero, add_zero] at h
    exact IsUnit.of_mul_eq_one (u : ZMod c) (by rw [mul_comm]; exact h)
  obtain ⟨u, hu⟩ := hu
  simp only [kloosterman_def, Int.cast_mul, ← hu]
  exact kloostermanMod_unit_mul c u _ _

/-- The values of the standard additive character have absolute value one. -/
theorem norm_stdAddChar (c : ℕ) [NeZero c] (x : ZMod c) : ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- Complex conjugation of the standard additive character is evaluation at $-x$. -/
theorem conj_stdAddChar (c : ℕ) [NeZero c] (x : ZMod c) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, norm_stdAddChar]
  simp

/-- $S(m,n;c)$ is real (substitute $d \mapsto -d$). -/
theorem conj_kloostermanMod (c : ℕ) [NeZero c] (m n : ZMod c) :
    conj (kloostermanMod c m n) = kloostermanMod c m n := by
  unfold kloostermanMod
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.neg _) _ _ fun d ↦ ?_
  rw [conj_stdAddChar]
  congr 1
  simp only [Equiv.neg_apply, Units.val_neg, inv_neg, mul_neg]
  ring

/-- $S(m,n;c)$ is real. -/
@[kb "iwaniec1997" "Section 4.4, reality of S(m,n;c) used in (4.18), p. 61"]
theorem conj_kloosterman (m n : ℤ) (c : ℕ) : conj (kloosterman m n c) = kloosterman m n c := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have : NeZero c := ⟨hc⟩
  simp only [kloosterman_def, conj_kloostermanMod]

/-- $S(m,n;c)$ is real: its imaginary part vanishes. -/
theorem kloosterman_im (m n : ℤ) (c : ℕ) : (kloosterman m n c).im = 0 :=
  Complex.conj_eq_iff_im.1 (conj_kloosterman m n c)

/-- The trivial bound $|S(m,n;c)| \le \varphi(c)$. -/
@[kb "iwaniec1997" "Section 4.1, trivial bound (4.1), p. 57"]
theorem norm_kloosterman_le_totient (m n : ℤ) (c : ℕ) [NeZero c] :
    ‖kloosterman m n c‖ ≤ Nat.totient c := by
  rw [kloosterman_def, kloostermanMod]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_stdAddChar, sum_const, card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul, mul_one]
  exact le_rfl

/-- $S(0,0;c) = \varphi(c)$. -/
theorem kloosterman_zero_zero (c : ℕ) [NeZero c] : kloosterman 0 0 c = Nat.totient c := by
  simp [kloosterman_def, kloostermanMod, ZMod.card_units_eq_totient]

/-- For the modulus $c = 1$, $S(m,n;1) = 1$. -/
theorem kloosterman_one (m n : ℤ) : kloosterman m n 1 = 1 := by
  rw [kloosterman_def, kloostermanMod]
  have : ∀ x : ZMod 1, x = 0 := fun x ↦ Subsingleton.elim _ _
  simp [this]

/-- **The Salié sum** (4.36): $T(m,n;c) = \sum_{ad\equiv 1\,(c)} \big(\tfrac{d}{c}\big)\, e\big((am + dn)/c\big)$, with
the Jacobi symbol $\big(\tfrac{d}{c}\big)$ (here at the least nonnegative residue of $d$). -/
@[kb "iwaniec1997" "Section 4.6, Salié sum (4.36), p. 66"]
def salie (m n : ℤ) (c : ℕ) [NeZero c] : ℂ :=
  ∑ d : (ZMod c)ˣ, (jacobiSym ((d : ZMod c).val : ℤ) c : ℂ) *
    ZMod.stdAddChar ((m : ZMod c) * ((d⁻¹ : (ZMod c)ˣ) : ZMod c) + (n : ZMod c) * (d : ZMod c))

/-- **The quadratic Gauss sum** (4.15), (4.37): $g(n,c) = \sum_{t \bmod c} e(nt^2/c)$. -/
@[kb "iwaniec1997" "Section 4.6, (4.37), p. 66; also (4.15), p. 60"]
def quadGaussSum (n : ℤ) (c : ℕ) [NeZero c] : ℂ :=
  ∑ t : ZMod c, ZMod.stdAddChar ((n : ZMod c) * t ^ 2)

/-- The factor $\varepsilon_c$ of (4.14): $1$ if $c \equiv 1 \pmod 4$ and $i$ if $c \equiv -1 \pmod 4$
(only used for odd $c$; for even $c$ the value is $i$ and is never used). -/
@[kb "iwaniec1997" "Section 4.6, (4.39), p. 66; also Lemma 4.2, p. 60"]
def epsilonFactor (c : ℕ) : ℂ := if c % 4 = 1 then 1 else I

end ModularFormsKB.Iwaniec1997
