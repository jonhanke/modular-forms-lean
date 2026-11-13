/-
# Tunnell's theorem on congruent numbers

Sources: Tunnell 1983 `tunnell1983` (locators [unverified]: the paper was not checked); the criterion as stated in
Milne, *Elliptic Curves*, Introduction, "Congruent numbers" (checked), which attributes it to Tunnell and refers to
Koblitz 1984.

A positive integer $n$ is **congruent** if it is the area of a right triangle with rational sides (`IsCongruent`).
**Proved here, unconditionally:** $n$ is congruent iff $E_n : y^2 = x^3 - n^2x$ has a rational point with $y \ne 0$
(`isCongruent_iff_point`); the triangles exhibiting $5$, $6$, $7$ and $41$ as congruent (`isCongruent_five`, ...).

**Tunnell's counts** (odd $n$): $A(n) = \#\{x^2 + 2y^2 + 8z^2 = n\}$, $B(n) = \#\{x^2 + 2y^2 + 32z^2 = n\}$; (even $n$):
$C(n) = \#\{x^2 + 4y^2 + 8z^2 = n/2\}$, $D(n) = \#\{x^2 + 4y^2 + 32z^2 = n/2\}$, all over $\mathbb Z^3$ (`tunnellA`, ...,
computable; small values by `decide`). Tunnell proves, from Waldspurger's theorem applied to the weight $3/2$ forms
$\theta_{1,2,8} - \tfrac12\theta_{1,2,32}$ (level $128$) and its even analogue, whose Shimura lift is the weight $2$ newform of
$E_1 : y^2 = x^3 - x$ (conductor $32$):
$$ L(E_n, 1) = \frac{\beta\,(A(n) - 2B(n))^2}{16\sqrt n}\ (n \text{ odd}),\qquad L(E_n,1) = \frac{\beta\,(C(n) - 2D(n))^2}{8\sqrt n}\ (n\text{ even}),$$
$n$ squarefree, $\beta = \int_1^\infty dx/\sqrt{x^3 - x}$ (`TunnellFormula`, a named input; both constants checked
numerically for all squarefree $n \le 59$). With Coates–Wiles (`CoatesWiles`:
$L(E_n,1) \ne 0$ implies $E_n(\mathbb Q)$ has only the $2$-torsion points) this gives **unconditionally**:
$A(n) \ne 2B(n) \Rightarrow n$ not congruent (`not_isCongruent_of_odd`); **conditionally on the weak Birch and
Swinnerton-Dyer conjecture** for $E_n$ (`WeakBSD`): $A(n) = 2B(n) \Rightarrow n$ congruent, so the criterion is an
equivalence (`isCongruent_iff_odd`, `isCongruent_iff_even`).

The value $L(E_n, 1)$ enters only through the abstract function `Lval` (Mathlib has no $L$-functions of elliptic curves);
the named inputs pin it down jointly.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import ModularFormsKB.Citation
namespace ModularFormsKB.HalfIntegral.Waldspurger.Tunnell

/-! ## Congruent numbers and the curve $y^2 = x^3 - n^2x$ -/

/-- **$n$ is a congruent number:** the area of a right triangle with rational sides. -/
def IsCongruent (n : ℕ) : Prop :=
  ∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b / 2 = n

/-- **$E_n(\mathbb Q)$ has a point with $y \ne 0$**, i.e. a point that is not $2$-torsion. -/
def HasPointYNeZero (n : ℕ) : Prop :=
  ∃ x y : ℚ, y ≠ 0 ∧ y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x

/-- From a triangle to a point: $x = (c/2)^2$, $y = c(b^2 - a^2)/8$. -/
theorem hasPointYNeZero_of_isCongruent {n : ℕ} (h : IsCongruent n) : HasPointYNeZero n := by
  obtain ⟨a, b, c, ha, hb, h, hab⟩ := h
  have hn : (n : ℚ) = a * b / 2 := hab.symm
  have hc : c ≠ 0 := by
    rintro rfl
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]
  have hne : b ^ 2 - a ^ 2 ≠ 0 := by
    intro h0
    have hba : b = a := by nlinarith [sq_nonneg (b - a), sq_nonneg (b + a)]
    subst hba
    have h2 : (c / b) ^ 2 = 2 := by
      field_simp
      nlinarith
    apply irrational_sqrt_two
    refine ⟨|c / b|, ?_⟩
    have : ((|c / b| : ℚ) : ℝ) ^ 2 = 2 := by
      have := congrArg (fun q : ℚ => (q : ℝ)) h2
      push_cast at this ⊢
      rw [sq_abs]; exact_mod_cast h2
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ((|c / b| : ℚ) : ℝ)), this]
  refine ⟨(c / 2) ^ 2, c * (b ^ 2 - a ^ 2) / 8, by positivity, ?_⟩
  rw [hn]
  have hc2 : c ^ 2 = a ^ 2 + b ^ 2 := h.symm
  have : c ^ 4 = (a ^ 2 + b ^ 2) ^ 2 := by rw [← hc2]; ring
  field_simp
  ring_nf
  nlinarith [this, hc2]

/-- From a point to a triangle: $a = |x^2 - n^2|/|y|$, $b = 2n|x|/|y|$, $c = (x^2 + n^2)/|y|$. -/
theorem isCongruent_of_hasPointYNeZero {n : ℕ} (hn : 0 < n) (h : HasPointYNeZero n) : IsCongruent n := by
  obtain ⟨x, y, hy, h⟩ := h
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hx : x ≠ 0 := by
    rintro rfl
    apply hy; simpa using h
  have hxn : x ^ 2 - (n : ℚ) ^ 2 ≠ 0 := by
    intro h0
    apply hy
    have : y ^ 2 = 0 := by rw [h]; linear_combination x * h0
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have hy' : 0 < |y| := abs_pos.mpr hy
  refine ⟨|x ^ 2 - (n : ℚ) ^ 2| / |y|, 2 * n * |x| / |y|, (x ^ 2 + (n : ℚ) ^ 2) / |y|,
    ?_, ?_, ?_, ?_⟩
  · exact div_pos (abs_pos.mpr hxn) hy'
  · exact div_pos (by have := abs_pos.mpr hx; positivity) hy'
  · rw [div_pow, div_pow, div_pow, sq_abs, mul_pow, sq_abs, ← add_div]
    congr 1
    simp only [sq_abs]
    ring
  · have h1 : |x| * |x ^ 2 - (n : ℚ) ^ 2| = y ^ 2 := by
      rw [← abs_mul]
      have e : x * (x ^ 2 - (n : ℚ) ^ 2) = y ^ 2 := by rw [h]; ring
      rw [e, abs_of_nonneg (sq_nonneg y)]
    have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
    have hy3 : |y| ^ 2 = y ^ 2 := sq_abs y
    field_simp
    rw [hy3]
    linear_combination h1

/-- **$n$ is congruent iff $E_n$ has a rational point with $y \ne 0$.** -/
theorem isCongruent_iff_point {n : ℕ} (hn : 0 < n) : IsCongruent n ↔ HasPointYNeZero n :=
  ⟨hasPointYNeZero_of_isCongruent, isCongruent_of_hasPointYNeZero hn⟩

/-- $6$: the triangle $(3, 4, 5)$. -/
theorem isCongruent_six : IsCongruent 6 := by
  exact ⟨3, 4, 5, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- $5$ (Fibonacci): the triangle $(3/2, 20/3, 41/6)$. -/
theorem isCongruent_five : IsCongruent 5 := by
  exact ⟨3/2, 20/3, 41/6, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- $7$ (Euler): the triangle $(24/5, 35/12, 337/60)$. -/
theorem isCongruent_seven : IsCongruent 7 := by
  exact ⟨24/5, 35/12, 337/60, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- $41$: the triangle $(40/3, 123/20, 881/60)$ ($E_{41}$ has rank $2$, root number $+1$, $L(E_{41}, 1) = 0$). -/
theorem isCongruent_fortyOne : IsCongruent 41 := by
  exact ⟨40/3, 123/20, 881/60, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## Tunnell's counts -/

/-- **Representation count** $\#\{(x,y,z) \in \mathbb Z^3 : x^2 + \alpha y^2 + \beta z^2 = m\}$, computed over the box
$|x|, |y|, |z| \le m$ (which contains every solution for $\alpha, \beta \ge 1$: `mem_box_of_rep`). -/
def repCount (α β m : ℕ) : ℕ :=
  ((Finset.Icc (-(m : ℤ)) m ×ˢ Finset.Icc (-(m : ℤ)) m ×ˢ Finset.Icc (-(m : ℤ)) m).filter
    (fun v : ℤ × ℤ × ℤ ↦ v.1 ^ 2 + (α : ℤ) * v.2.1 ^ 2 + (β : ℤ) * v.2.2 ^ 2 = (m : ℤ))).card

/-- Every solution lies in the box, so `repCount` counts all of $\mathbb Z^3$. -/
theorem mem_box_of_rep {α β m : ℕ} (hα : 1 ≤ α) (hβ : 1 ≤ β) {x y z : ℤ}
    (h : x ^ 2 + α * y ^ 2 + β * z ^ 2 = m) :
    |x| ≤ m ∧ |y| ≤ m ∧ |z| ≤ m := by
  have hα' : (1 : ℤ) ≤ α := by exact_mod_cast hα
  have hβ' : (1 : ℤ) ≤ β := by exact_mod_cast hβ
  have hm : (0 : ℤ) ≤ m := by positivity
  have hx := sq_nonneg x
  have hy := sq_nonneg y
  have hz := sq_nonneg z
  have key : ∀ w : ℤ, w ^ 2 ≤ m → |w| ≤ m := by
    intro w hw
    have : w ^ 2 ≤ (m : ℤ) ^ 2 := by
      nlinarith [Int.le_self_sq (m : ℤ)]
    exact abs_le_of_sq_le_sq this hm
  refine ⟨key x ?_, key y ?_, key z ?_⟩ <;> nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ α - 1) hy,
    mul_nonneg (by linarith : (0:ℤ) ≤ β - 1) hz]

/-- $A(n) = \#\{x^2 + 2y^2 + 8z^2 = n\}$. -/
def tunnellA (n : ℕ) : ℕ := repCount 2 8 n

/-- $B(n) = \#\{x^2 + 2y^2 + 32z^2 = n\}$. -/
def tunnellB (n : ℕ) : ℕ := repCount 2 32 n

/-- $C(n) = \#\{x^2 + 4y^2 + 8z^2 = n/2\}$ ($n$ even). -/
def tunnellC (n : ℕ) : ℕ := repCount 4 8 (n / 2)

/-- $D(n) = \#\{x^2 + 4y^2 + 32z^2 = n/2\}$ ($n$ even). -/
def tunnellD (n : ℕ) : ℕ := repCount 4 32 (n / 2)

theorem tunnellA_one : tunnellA 1 = 2 := by decide
theorem tunnellB_one : tunnellB 1 = 2 := by decide
theorem tunnellA_three : tunnellA 3 = 4 := by decide
theorem tunnellB_three : tunnellB 3 = 4 := by decide
theorem tunnellA_five : tunnellA 5 = 0 := by decide +kernel
theorem tunnellB_five : tunnellB 5 = 0 := by decide +kernel
theorem tunnellA_eleven : tunnellA 11 = 12 := by decide +kernel
theorem tunnellB_eleven : tunnellB 11 = 4 := by decide +kernel
theorem tunnellC_two : tunnellC 2 = 2 := by decide
theorem tunnellD_two : tunnellD 2 = 2 := by decide

/-! ## Named inputs and the criterion -/

/-- **Tunnell's formula** (Tunnell 1983 `tunnell1983`, Thm. 2 [unverified]; the constants are checked
numerically): for squarefree $n$, with `Lval n` $= L(E_n, 1)$ and $\beta = \int_1^\infty dx/\sqrt{x^3-x}$,
$L(E_n,1) = \beta(A(n) - 2B(n))^2/(16\sqrt n)$ for odd $n$ and $\beta(C(n) - 2D(n))^2/(8\sqrt n)$ for even $n$. -/
@[kb "tunnell1983" "L(E_n,1) = β(A(n)-2B(n))²/(16√n) (n odd), β(C(n)-2D(n))²/(8√n) (n even) [unverified]"]
structure TunnellFormula (Lval : ℕ → ℝ) (β : ℝ) : Prop where
  beta_pos : 0 < β
  odd : ∀ n : ℕ, Squarefree n → Odd n →
    Lval n = β * ((tunnellA n : ℝ) - 2 * tunnellB n) ^ 2 / (16 * Real.sqrt n)
  even : ∀ n : ℕ, Squarefree n → Even n →
    Lval n = β * ((tunnellC n : ℝ) - 2 * tunnellD n) ^ 2 / (8 * Real.sqrt n)

/-- **Coates–Wiles for the congruent number curves** (Coates–Wiles 1977 `coateswiles1977` [unverified]; $E_n$ has complex
multiplication by $\mathbb Z[i]$): if $L(E_n, 1) \ne 0$ then $E_n(\mathbb Q)$ is finite, hence consists of the four
$2$-torsion points ($y = 0$). -/
@[kb "coateswiles1977" "L(E,1) ≠ 0 ⇒ E(Q) finite for CM curves; for E_n: no point with y ≠ 0 [unverified]"]
structure CoatesWiles (Lval : ℕ → ℝ) : Prop where
  no_point : ∀ n : ℕ, 0 < n → Squarefree n → Lval n ≠ 0 → ¬ HasPointYNeZero n

/-- **The weak Birch and Swinnerton-Dyer conjecture for $E_n$** (a conjecture, not a theorem): if $L(E_n,1) = 0$ then
$E_n(\mathbb Q)$ is infinite, hence has a point with $y \ne 0$. -/
@[kb "bsd" "conjecture: L(E_n,1) = 0 ⇒ rank E_n(Q) > 0 [conjectural]"]
structure WeakBSD (Lval : ℕ → ℝ) : Prop where
  point : ∀ n : ℕ, 0 < n → Squarefree n → Lval n = 0 → HasPointYNeZero n

/-- $L(E_n,1) = 0$ iff $A(n) = 2B(n)$ (odd squarefree $n$), from Tunnell's formula. -/
theorem lval_eq_zero_iff_odd {Lval : ℕ → ℝ} {β : ℝ} (hT : TunnellFormula Lval β) {n : ℕ} (hn : 0 < n)
    (hsq : Squarefree n) (hodd : Odd n) : Lval n = 0 ↔ tunnellA n = 2 * tunnellB n := by
  rw [hT.odd n hsq hodd]
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hb := hT.beta_pos
  constructor
  · intro h
    have h' : ((tunnellA n : ℝ) - 2 * tunnellB n) ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h hb.ne'
        · exact h
      · exact absurd h (by positivity)
    have : (tunnellA n : ℝ) = 2 * tunnellB n := by nlinarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h']
    exact_mod_cast this
  · intro h
    have : (tunnellA n : ℝ) = 2 * tunnellB n := by exact_mod_cast h
    rw [this]; simp

/-- $L(E_n,1) = 0$ iff $C(n) = 2D(n)$ (even squarefree $n$). -/
theorem lval_eq_zero_iff_even {Lval : ℕ → ℝ} {β : ℝ} (hT : TunnellFormula Lval β) {n : ℕ} (hn : 0 < n)
    (hsq : Squarefree n) (heven : Even n) : Lval n = 0 ↔ tunnellC n = 2 * tunnellD n := by
  rw [hT.even n hsq heven]
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hb := hT.beta_pos
  constructor
  · intro h
    have h' : ((tunnellC n : ℝ) - 2 * tunnellD n) ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h hb.ne'
        · exact h
      · exact absurd h (by positivity)
    have : (tunnellC n : ℝ) = 2 * tunnellD n := by nlinarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h']
    exact_mod_cast this
  · intro h
    have : (tunnellC n : ℝ) = 2 * tunnellD n := by exact_mod_cast h
    rw [this]; simp

/-- **Tunnell, unconditional half** (from Tunnell's formula and Coates–Wiles): an odd squarefree $n$ with
$A(n) \ne 2B(n)$ is not congruent. -/
theorem not_isCongruent_of_odd {Lval : ℕ → ℝ} {β : ℝ} (hT : TunnellFormula Lval β) (hCW : CoatesWiles Lval) {n : ℕ}
    (hn : 0 < n) (hsq : Squarefree n) (hodd : Odd n) (h : tunnellA n ≠ 2 * tunnellB n) : ¬ IsCongruent n := by
  intro hc
  exact hCW.no_point n hn hsq (fun h0 => h ((lval_eq_zero_iff_odd hT hn hsq hodd).mp h0))
    ((isCongruent_iff_point hn).mp hc)

/-- **Tunnell, unconditional half, even $n$.** -/
theorem not_isCongruent_of_even {Lval : ℕ → ℝ} {β : ℝ} (hT : TunnellFormula Lval β) (hCW : CoatesWiles Lval) {n : ℕ}
    (hn : 0 < n) (hsq : Squarefree n) (heven : Even n) (h : tunnellC n ≠ 2 * tunnellD n) : ¬ IsCongruent n := by
  intro hc
  exact hCW.no_point n hn hsq (fun h0 => h ((lval_eq_zero_iff_even hT hn hsq heven).mp h0))
    ((isCongruent_iff_point hn).mp hc)

/-- **Tunnell's criterion, odd $n$** (conditional on the weak Birch and Swinnerton-Dyer conjecture): an odd squarefree
$n$ is congruent iff $A(n) = 2B(n)$. -/
theorem isCongruent_iff_odd {Lval : ℕ → ℝ} {β : ℝ} (hT : TunnellFormula Lval β) (hCW : CoatesWiles Lval)
    (hBSD : WeakBSD Lval) {n : ℕ} (hn : 0 < n) (hsq : Squarefree n) (hodd : Odd n) :
    IsCongruent n ↔ tunnellA n = 2 * tunnellB n := by
  constructor
  · intro hc
    by_contra h
    exact not_isCongruent_of_odd hT hCW hn hsq hodd h hc
  · intro h
    exact (isCongruent_iff_point hn).mpr
      (hBSD.point n hn hsq ((lval_eq_zero_iff_odd hT hn hsq hodd).mpr h))

/-- **Tunnell's criterion, even $n$** (conditional on the weak Birch and Swinnerton-Dyer conjecture). -/
theorem isCongruent_iff_even {Lval : ℕ → ℝ} {β : ℝ} (hT : TunnellFormula Lval β) (hCW : CoatesWiles Lval)
    (hBSD : WeakBSD Lval) {n : ℕ} (hn : 0 < n) (hsq : Squarefree n) (heven : Even n) :
    IsCongruent n ↔ tunnellC n = 2 * tunnellD n := by
  constructor
  · intro hc
    by_contra h
    exact not_isCongruent_of_even hT hCW hn hsq heven h hc
  · intro h
    exact (isCongruent_iff_point hn).mpr
      (hBSD.point n hn hsq ((lval_eq_zero_iff_even hT hn hsq heven).mpr h))

/-- **$1$, $3$ and $11$ are not congruent** (from Tunnell's formula and Coates–Wiles: $A - 2B = -2, -4, 4$). -/
theorem not_isCongruent_one_three_eleven {Lval : ℕ → ℝ} {β : ℝ} (hT : TunnellFormula Lval β)
    (hCW : CoatesWiles Lval) : ¬ IsCongruent 1 ∧ ¬ IsCongruent 3 ∧ ¬ IsCongruent 11 := by
  refine ⟨?_, ?_, ?_⟩
  · exact not_isCongruent_of_odd hT hCW (by norm_num) (by decide +kernel) (by decide)
      (by rw [tunnellA_one, tunnellB_one]; norm_num)
  · exact not_isCongruent_of_odd hT hCW (by norm_num) (by decide +kernel) (by decide)
      (by rw [tunnellA_three, tunnellB_three]; norm_num)
  · exact not_isCongruent_of_odd hT hCW (by norm_num) (by decide +kernel) (by decide)
      (by rw [tunnellA_eleven, tunnellB_eleven]; norm_num)

/-- **Consistency check:** $5$ is congruent (proved: `isCongruent_five`), and indeed $A(5) = 2B(5)$ ($= 0$), as the
criterion predicts. -/
theorem tunnell_five_consistent : IsCongruent 5 ∧ tunnellA 5 = 2 * tunnellB 5 :=
  ⟨isCongruent_five, by rw [tunnellA_five, tunnellB_five]⟩

end ModularFormsKB.HalfIntegral.Waldspurger.Tunnell
