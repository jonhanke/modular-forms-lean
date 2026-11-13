/-
# Gross's weight 3/2 form for prime level 11

Source: Gross 1987 `gross1987` (locators [unverified]: the paper was not checked; the constants were checked
numerically).

Let $B$ be the quaternion algebra over $\mathbb Q$ ramified at $\{11, \infty\}$. It has two classes of maximal orders,
$R_1 = \mathbb Z\langle 1, i, \tfrac{1+j}2, \tfrac{i+k}2\rangle \subset (-1,-11)_{\mathbb Q}$ and
$R_2 = \mathbb Z\langle 1, \tfrac{1+i}2, \tfrac{j+k}2, \tfrac{i\pm k}3\rangle \subset (-3,-11)_{\mathbb Q}$, with unit groups of orders
$4$ and $6$ ($w_1 = 2$, $w_2 = 3$; mass $\tfrac12 + \tfrac13 = \tfrac{11-1}{12}$). Gross attaches to $R_i$ the ternary
lattice $S_i = \{x \in \mathbb Z + 2R_i : \operatorname{tr} x = 0\}$ with the norm form; on $R_i/\mathbb Z$ it is
$Q(y) = 4\,\mathrm{N}(y) - \operatorname{tr}(y)^2$, which in the bases used for the numerical check is
$$Q_1 = 4x_0^2 + 4x_0x_2 + 11x_1^2 + 12x_2^2, \qquad Q_2 = 3x_0^2 + 4x_0x_2 + 44x_1^2 + 44x_1x_2 + 16x_2^2$$
(`grossQ₁`, `grossQ₂`; the identification with Gross's $S_i$ is checked by the script, not in Lean). Their theta series
$\theta_i = \sum_{x\in\mathbb Z^3} q^{Q_i(x)}$ have weight $3/2$ and level $44$, and for the eigenvector $e = (1, -1)$ of the
Brandt matrices (eigenvalues $a_m$ of the newform of $X_0(11)$) the form
$$ g = \tfrac12(\theta_1 - \theta_2) = -q^3 + q^4 + q^{11} + q^{12} - q^{15} - 2q^{16} - \dots $$
(`grossCoeff`) is a weight $3/2$ Hecke eigenform whose Shimura lift is $f = q\prod(1-q^n)^2(1-q^{11n})^2$.

**Proved here:** $Q_i(x) \equiv 0, 3 \bmod 4$, so $g$ satisfies Kohnen's plus condition (`grossQ₁_mod_four`,
`grossCoeff_eq_zero_of_mod_four`); **the local obstruction at 11**: if $Q_i$ represents $n$ with $11 \nmid n$ then
$\left(\frac{-n}{11}\right) = -1$ (`jacobiSym_neg_grossQ₁`, `jacobiSym_neg_grossQ₂`), so $c(n) = 0$ whenever $11$ splits in
$\mathbb Q(\sqrt{-n})$ (`grossCoeff_eq_zero_of_split`) — Kohnen's condition $\left(\frac{D}{11}\right) = w_{11} = -1$ and
Waldspurger's local sign at $11$ (`Packets.lean`), seen directly on the quadratic forms; small coefficients
(`grossCoeff_three`, ...); the Brandt matrices $B(2), B(3), B(5)$ as explicit matrices with row sums $\sigma(m)$, the
symmetry $w_jB_{ij} = w_iB_{ji}$, and $B(m)^{\mathsf T}e = a_m e$ with $a_2, a_3, a_5 = -2, -1, 1$ (`brandt_two_eigen`, ...).

**Named:** Gross's formula, in the ratio form checked numerically: for fundamental $D_1, D_2 < 0$ with $11$ inert in
both $\mathbb Q(\sqrt{D_i})$, $c(|D_1|)^2\sqrt{|D_2|}\,L(f,D_2,1) = c(|D_2|)^2\sqrt{|D_1|}\,L(f,D_1,1)$
(`GrossRatio`; the constant $L(f,1)L(f,D,1)\sqrt{|D|}/c(|D|)^2 = 0.7406\ldots$ is the same for all inert $D$ tested,
including $D = -3, -4$, and twice that for $11 \mid D$).

**Connection to quadratic forms** (by citation; no library of quadratic forms is imported): $Q_1$ and $Q_2$ have the same
determinant ($\det$ of the matrix of second derivatives $= 3872 = 2^5\cdot 11^2$, `grossQ_hessian_det`) and lie in one
genus, of two classes; $\tfrac12\theta_1 + \tfrac13\theta_2$ is the genus (Siegel–Eisenstein) average, and $g$ is the cuspidal
part, which by Gross and Waldspurger measures the failure of the class to represent what the genus represents.
-/
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import ModularFormsKB.Citation
import ModularFormsKB.HalfIntegral.Abstract.Kohnen

namespace ModularFormsKB.HalfIntegral.Waldspurger.Gross

/-- $Q_1(x) = 4x_0^2 + 4x_0x_2 + 11x_1^2 + 12x_2^2$ (Gross's ternary form for $R_1$). -/
def grossQ₁ (x : ℤ × ℤ × ℤ) : ℤ :=
  4 * x.1 ^ 2 + 4 * x.1 * x.2.2 + 11 * x.2.1 ^ 2 + 12 * x.2.2 ^ 2

/-- $Q_2(x) = 3x_0^2 + 4x_0x_2 + 44x_1^2 + 44x_1x_2 + 16x_2^2$ (Gross's ternary form for $R_2$). -/
def grossQ₂ (x : ℤ × ℤ × ℤ) : ℤ :=
  3 * x.1 ^ 2 + 4 * x.1 * x.2.2 + 44 * x.2.1 ^ 2 + 44 * x.2.1 * x.2.2 + 16 * x.2.2 ^ 2

/-- The box $[-m, m]^3$. -/
def box (m : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  Finset.Icc (-(m : ℤ)) m ×ˢ Finset.Icc (-(m : ℤ)) m ×ˢ Finset.Icc (-(m : ℤ)) m

/-- $r_Q(n) = \#\{x : Q(x) = n\}$, counted over the box $[-n, n]^3$ (which contains every solution for $Q_1, Q_2$:
`mem_box_of_grossQ₁`, `mem_box_of_grossQ₂`). -/
def thetaCount (Q : ℤ × ℤ × ℤ → ℤ) (n : ℕ) : ℕ :=
  ((box n).filter (fun x ↦ Q x = n)).card

private theorem sq_bound {t n : ℤ} (hn : 0 ≤ n) (h : t ^ 2 ≤ n) : -n ≤ t ∧ t ≤ n := by
  have h1 : |t| ≤ n := by
    rcases eq_or_ne t 0 with rfl | ht
    · simpa using hn
    · have : 1 ≤ |t| := Int.one_le_abs ht
      have e : |t| ^ 2 = t ^ 2 := sq_abs t
      nlinarith
  exact abs_le.mp h1

/-- $Q_1 = (2x_0 + x_2)^2 + 11x_1^2 + 11x_2^2$: positive definite, and solutions of $Q_1 = n$ lie in $[-n,n]^3$. -/
theorem mem_box_of_grossQ₁ {n : ℕ} {x : ℤ × ℤ × ℤ} (h : grossQ₁ x = n) : x ∈ box n := by
  obtain ⟨a, b, c⟩ := x
  simp only [grossQ₁] at h
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have hb : b ^ 2 ≤ n := by nlinarith [sq_nonneg (2 * a + c), sq_nonneg c, sq_nonneg b]
  have hc : c ^ 2 ≤ n := by nlinarith [sq_nonneg (2 * a + c), sq_nonneg c, sq_nonneg b]
  have ha : (2 * a + c) ^ 2 ≤ n := by nlinarith [sq_nonneg (2 * a + c), sq_nonneg c, sq_nonneg b]
  have h1 := sq_bound hn hb
  have h2 := sq_bound hn hc
  have h3 := sq_bound hn ha
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

/-- Solutions of $Q_2 = n$ lie in $[-n, n]^3$. -/
theorem mem_box_of_grossQ₂ {n : ℕ} {x : ℤ × ℤ × ℤ} (h : grossQ₂ x = n) : x ∈ box n := by
  obtain ⟨a, b, c⟩ := x
  simp only [grossQ₂] at h
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have hc : c ^ 2 ≤ n := by
    nlinarith [sq_nonneg (3 * a + 2 * c), sq_nonneg (2 * b + c), sq_nonneg c]
  have hb : (2 * b + c) ^ 2 ≤ n := by
    nlinarith [sq_nonneg (3 * a + 2 * c), sq_nonneg (2 * b + c), sq_nonneg c]
  have ha : a ^ 2 ≤ n := by
    nlinarith [sq_nonneg (3 * a + 2 * c), sq_nonneg (2 * b + c), sq_nonneg c,
      sq_nonneg (2 * (3 * a + 2 * c) + 11 * c)]
  have h1 := sq_bound hn ha
  have h2 := sq_bound hn hb
  have h3 := sq_bound hn hc
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

/-- **The coefficients of Gross's form** $g = \tfrac12(\theta_1 - \theta_2)$: $c(n) = (r_{Q_1}(n) - r_{Q_2}(n))/2$
(an integer: both counts are even for $n \ge 1$, as $x \mapsto -x$ has no fixed point). -/
def grossCoeff (n : ℕ) : ℤ :=
  ((thetaCount grossQ₁ n : ℤ) - thetaCount grossQ₂ n) / 2

/-- $Q_1(x) \equiv 0$ or $3 \bmod 4$. -/
theorem grossQ₁_mod_four (x : ℤ × ℤ × ℤ) : grossQ₁ x % 4 = 0 ∨ grossQ₁ x % 4 = 3 := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' b
  · have e : grossQ₁ (a, b, c) = 4 * (a ^ 2 + a * c + 3 * c ^ 2 + 11 * k ^ 2) := by
      subst hk; simp only [grossQ₁]; ring
    omega
  · have e : grossQ₁ (a, b, c) =
        4 * (a ^ 2 + a * c + 3 * c ^ 2 + 11 * (k ^ 2 + k)) + 11 := by
      subst hk; simp only [grossQ₁]; ring
    omega

/-- $Q_2(x) \equiv 0$ or $3 \bmod 4$. -/
theorem grossQ₂_mod_four (x : ℤ × ℤ × ℤ) : grossQ₂ x % 4 = 0 ∨ grossQ₂ x % 4 = 3 := by
  obtain ⟨a, b, c⟩ := x
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' a
  · have e : grossQ₂ (a, b, c) = 4 * (3 * k ^ 2 + 2 * k * c + 11 * b ^ 2 + 11 * b * c + 4 * c ^ 2) := by
      subst hk; simp only [grossQ₂]; ring
    omega
  · have e : grossQ₂ (a, b, c) =
        4 * (3 * (k ^ 2 + k) + (2 * k + 1) * c + 11 * b ^ 2 + 11 * b * c + 4 * c ^ 2) + 3 := by
      subst hk; simp only [grossQ₂]; ring
    omega

/-- **Kohnen's plus condition for $g$:** $c(n) = 0$ unless $-n \equiv 0, 1 \bmod 4$. -/
theorem grossCoeff_eq_zero_of_mod_four {n : ℕ} (h : n % 4 = 1 ∨ n % 4 = 2) : grossCoeff n = 0 := by
  have h0 : ∀ Q : ℤ × ℤ × ℤ → ℤ, (∀ x, Q x % 4 = 0 ∨ Q x % 4 = 3) → thetaCount Q n = 0 := by
    intro Q hQ
    unfold thetaCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    have := hQ x
    omega
  unfold grossCoeff
  rw [h0 _ grossQ₁_mod_four, h0 _ grossQ₂_mod_four]
  simp

private theorem sq_mod_eleven (y : ℤ) :
    y ^ 2 % 11 = 0 ∨ y ^ 2 % 11 = 1 ∨ y ^ 2 % 11 = 3 ∨ y ^ 2 % 11 = 4 ∨ y ^ 2 % 11 = 5 ∨
      y ^ 2 % 11 = 9 := by
  have h : y % 11 = 0 ∨ y % 11 = 1 ∨ y % 11 = 2 ∨ y % 11 = 3 ∨ y % 11 = 4 ∨ y % 11 = 5 ∨
      y % 11 = 6 ∨ y % 11 = 7 ∨ y % 11 = 8 ∨ y % 11 = 9 ∨ y % 11 = 10 := by omega
  rcases h with h | h | h | h | h | h | h | h | h | h | h <;>
    simp [pow_two, Int.mul_emod, h]

private theorem jac_aux1 (y m : ℤ) : jacobiSym (-(y ^ 2 + 11 * m)) 11 ≠ 1 := by
  rw [jacobiSym.mod_left]
  rcases sq_mod_eleven y with h | h | h | h | h | h
  · have e : (-(y ^ 2 + 11 * m)) % ((11 : ℕ) : ℤ) = 0 := by push_cast; omega
    rw [e]; norm_num
  · have e : (-(y ^ 2 + 11 * m)) % ((11 : ℕ) : ℤ) = 10 := by push_cast; omega
    rw [e]; norm_num
  · have e : (-(y ^ 2 + 11 * m)) % ((11 : ℕ) : ℤ) = 8 := by push_cast; omega
    rw [e]; norm_num
  · have e : (-(y ^ 2 + 11 * m)) % ((11 : ℕ) : ℤ) = 7 := by push_cast; omega
    rw [e]; norm_num
  · have e : (-(y ^ 2 + 11 * m)) % ((11 : ℕ) : ℤ) = 6 := by push_cast; omega
    rw [e]; norm_num
  · have e : (-(y ^ 2 + 11 * m)) % ((11 : ℕ) : ℤ) = 2 := by push_cast; omega
    rw [e]; norm_num

private theorem jac_aux2 (y m : ℤ) : jacobiSym (-(3 * y ^ 2 + 11 * m)) 11 ≠ 1 := by
  rw [jacobiSym.mod_left]
  rcases sq_mod_eleven y with h | h | h | h | h | h
  · have e : (-(3 * y ^ 2 + 11 * m)) % ((11 : ℕ) : ℤ) = 0 := by push_cast; omega
    rw [e]; norm_num
  · have e : (-(3 * y ^ 2 + 11 * m)) % ((11 : ℕ) : ℤ) = 8 := by push_cast; omega
    rw [e]; norm_num
  · have e : (-(3 * y ^ 2 + 11 * m)) % ((11 : ℕ) : ℤ) = 2 := by push_cast; omega
    rw [e]; norm_num
  · have e : (-(3 * y ^ 2 + 11 * m)) % ((11 : ℕ) : ℤ) = 10 := by push_cast; omega
    rw [e]; norm_num
  · have e : (-(3 * y ^ 2 + 11 * m)) % ((11 : ℕ) : ℤ) = 7 := by push_cast; omega
    rw [e]; norm_num
  · have e : (-(3 * y ^ 2 + 11 * m)) % ((11 : ℕ) : ℤ) = 6 := by push_cast; omega
    rw [e]; norm_num

/-- **Local obstruction at 11 for $Q_1$:** $Q_1 \equiv (2x_0 + x_2)^2 \bmod 11$, so $\left(\frac{-Q_1(x)}{11}\right) \ne 1$. -/
theorem jacobiSym_neg_grossQ₁ (x : ℤ × ℤ × ℤ) : jacobiSym (-grossQ₁ x) 11 ≠ 1 := by
  obtain ⟨a, b, c⟩ := x
  have e : -grossQ₁ (a, b, c) = -((2 * a + c) ^ 2 + 11 * (b ^ 2 + c ^ 2)) := by
    simp only [grossQ₁]; ring
  rw [e]
  exact jac_aux1 _ _

/-- **Local obstruction at 11 for $Q_2$:** $Q_2 \equiv 3(x_0 + 8x_2)^2 \bmod 11$ and $-3$ is not a square mod $11$. -/
theorem jacobiSym_neg_grossQ₂ (x : ℤ × ℤ × ℤ) : jacobiSym (-grossQ₂ x) 11 ≠ 1 := by
  obtain ⟨a, b, c⟩ := x
  have e : -grossQ₂ (a, b, c) =
      -(3 * (a + 8 * c) ^ 2 + 11 * (-4 * a * c + 4 * b ^ 2 + 4 * b * c - 16 * c ^ 2)) := by
    simp only [grossQ₂]; ring
  rw [e]
  exact jac_aux2 _ _

/-- **$c(n) = 0$ when $11$ splits in $\mathbb Q(\sqrt{-n})$**, i.e. $\left(\frac{-n}{11}\right) = 1$: neither form represents $n$. -/
theorem grossCoeff_eq_zero_of_split {n : ℕ} (h : jacobiSym (-(n : ℤ)) 11 = 1) : grossCoeff n = 0 := by
  have h0 : ∀ Q : ℤ × ℤ × ℤ → ℤ, (∀ x, jacobiSym (-Q x) 11 ≠ 1) → thetaCount Q n = 0 := by
    intro Q hQ
    unfold thetaCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    apply hQ x
    rw [hx]; exact h
  unfold grossCoeff
  rw [h0 _ jacobiSym_neg_grossQ₁, h0 _ jacobiSym_neg_grossQ₂]
  simp

private theorem thetaCount_small (Q : ℤ × ℤ × ℤ → ℤ) (n : ℕ)
    (h1 : ∀ x, Q x = n → x ∈ box n) (h2 : ∀ x, Q x = n → x ∈ box 2) :
    thetaCount Q n = ((box 2).filter (fun x ↦ Q x = n)).card := by
  unfold thetaCount
  congr 1
  ext x
  simp only [Finset.mem_filter]
  exact ⟨fun ⟨_, h⟩ ↦ ⟨h2 x h, h⟩, fun ⟨_, h⟩ ↦ ⟨h1 x h, h⟩⟩

private theorem small₁ {n : ℕ} (hn : n ≤ 16) {x : ℤ × ℤ × ℤ} (h : grossQ₁ x = n) : x ∈ box 2 := by
  obtain ⟨a, b, c⟩ := x
  simp only [grossQ₁] at h
  have hn' : (n : ℤ) ≤ 16 := by exact_mod_cast hn
  have hb : -1 ≤ b ∧ b ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (2 * a + c), sq_nonneg c, sq_nonneg b]
  have hc : -1 ≤ c ∧ c ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (2 * a + c), sq_nonneg c, sq_nonneg b]
  have ha : -4 ≤ 2 * a + c ∧ 2 * a + c ≤ 4 := by
    constructor <;> nlinarith [sq_nonneg (2 * a + c), sq_nonneg c, sq_nonneg b]
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> push_cast <;> omega

private theorem small₂ {n : ℕ} (hn : n ≤ 16) {x : ℤ × ℤ × ℤ} (h : grossQ₂ x = n) : x ∈ box 2 := by
  obtain ⟨a, b, c⟩ := x
  simp only [grossQ₂] at h
  have hn' : (n : ℤ) ≤ 16 := by exact_mod_cast hn
  have hc : -2 ≤ c ∧ c ≤ 2 := by
    constructor <;> nlinarith [sq_nonneg (3 * a + 2 * c), sq_nonneg (2 * b + c), sq_nonneg c]
  have hb : -1 ≤ 2 * b + c ∧ 2 * b + c ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (3 * a + 2 * c), sq_nonneg (2 * b + c), sq_nonneg c]
  have ha : -2 ≤ a ∧ a ≤ 2 := by
    constructor <;> nlinarith [sq_nonneg (3 * a + 2 * c), sq_nonneg (2 * b + c), sq_nonneg c,
      sq_nonneg (2 * (3 * a + 2 * c) + 11 * c)]
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> push_cast <;> omega

private theorem grossCoeff_small {n : ℕ} (hn : n ≤ 16) :
    grossCoeff n = ((((box 2).filter (fun x ↦ grossQ₁ x = n)).card : ℤ) -
      ((box 2).filter (fun x ↦ grossQ₂ x = n)).card) / 2 := by
  unfold grossCoeff
  rw [thetaCount_small _ _ (fun x h ↦ mem_box_of_grossQ₁ h) (fun x h ↦ small₁ hn h),
    thetaCount_small _ _ (fun x h ↦ mem_box_of_grossQ₂ h) (fun x h ↦ small₂ hn h)]

theorem grossCoeff_three : grossCoeff 3 = -1 := by
  rw [grossCoeff_small (by norm_num)]
  decide +kernel
theorem grossCoeff_four : grossCoeff 4 = 1 := by
  rw [grossCoeff_small (by norm_num)]
  decide +kernel
theorem grossCoeff_seven : grossCoeff 7 = 0 := by
  rw [grossCoeff_small (by norm_num)]
  decide +kernel
theorem grossCoeff_eleven : grossCoeff 11 = 1 := by
  rw [grossCoeff_small (by norm_num)]
  decide +kernel
theorem grossCoeff_twelve : grossCoeff 12 = 1 := by
  rw [grossCoeff_small (by norm_num)]
  decide +kernel
theorem grossCoeff_fifteen : grossCoeff 15 = -1 := by
  rw [grossCoeff_small (by norm_num)]
  decide +kernel
theorem grossCoeff_sixteen : grossCoeff 16 = -2 := by
  rw [grossCoeff_small (by norm_num)]
  decide +kernel

/-- **Hecke relation at $p = 2$ on the square class of $3$:** $c(3\cdot 2^2) = \big(a_2 - \left(\frac{-3}{2}\right)\big)c(3)$
with $a_2 = -2$, $\left(\frac{-3}{2}\right) = -1$ (the relation `Corresponds.coeff_mul_prime_sq` at an odd prime, here
checked at $p = 2$ on the numbers). -/
theorem grossCoeff_twelve_hecke : grossCoeff 12 = (-2 - (-1)) * grossCoeff 3 := by
  rw [grossCoeff_twelve, grossCoeff_three]; norm_num

/-- The matrix of second derivatives of $Q_1$ and of $Q_2$ have the same determinant $3872 = 2^5\cdot 11^2$. -/
theorem grossQ_hessian_det :
    (!![8, 0, 4; 0, 22, 0; 4, 0, 24] : Matrix (Fin 3) (Fin 3) ℤ).det = 3872 ∧
      (!![6, 0, 4; 0, 88, 44; 4, 44, 32] : Matrix (Fin 3) (Fin 3) ℤ).det = 3872 := by
  constructor <;> simp [Matrix.det_fin_three]

/-! ## Brandt matrices for $p = 11$ -/

/-- $B(2) = \begin{pmatrix}1&2\\3&0\end{pmatrix}$: $B(m)_{ii} = \#\{x\in R_i : \mathrm N(x) = m\}/|R_i^\times|$, rows summing to
$\sigma(m)$ (computed numerically). -/
def brandt₂ : Matrix (Fin 2) (Fin 2) ℤ := !![1, 2; 3, 0]
/-- $B(3) = \begin{pmatrix}2&2\\3&1\end{pmatrix}$. -/
def brandt₃ : Matrix (Fin 2) (Fin 2) ℤ := !![2, 2; 3, 1]
/-- $B(5) = \begin{pmatrix}4&2\\3&3\end{pmatrix}$. -/
def brandt₅ : Matrix (Fin 2) (Fin 2) ℤ := !![4, 2; 3, 3]

/-- The weights $w_i = |R_i^\times|/2$. -/
def brandtWeight : Fin 2 → ℤ := ![2, 3]

/-- The eigenvector $e = (1, -1)$ attached to $f$. -/
def grossEigen : Fin 2 → ℤ := ![1, -1]

/-- Rows sum to $\sigma(m)$, and $w_jB_{ij} = w_iB_{ji}$. -/
theorem brandt_rowSum_symm :
    (∀ i, ∑ j, brandt₂ i j = 3) ∧ (∀ i, ∑ j, brandt₃ i j = 4) ∧ (∀ i, ∑ j, brandt₅ i j = 6) ∧
      (∀ i j, brandtWeight j * brandt₂ i j = brandtWeight i * brandt₂ j i) ∧
      (∀ i j, brandtWeight j * brandt₃ i j = brandtWeight i * brandt₃ j i) ∧
      (∀ i j, brandtWeight j * brandt₅ i j = brandtWeight i * brandt₅ j i) := by
  unfold brandt₂ brandt₃ brandt₅ brandtWeight
  decide +kernel

/-- **$e$ is an eigenvector with the eigenvalues of $f$:** $B(m)^{\mathsf T}e = a_m e$, $a_2 = -2$, $a_3 = -1$, $a_5 = 1$. -/
theorem brandt_eigen :
    brandt₂.transpose.mulVec grossEigen = (-2 : ℤ) • grossEigen ∧
      brandt₃.transpose.mulVec grossEigen = (-1 : ℤ) • grossEigen ∧
      brandt₅.transpose.mulVec grossEigen = (1 : ℤ) • grossEigen := by
  unfold brandt₂ brandt₃ brandt₅ grossEigen
  decide +kernel

/-- **The Eisenstein eigenvector:** $(1,1)$ has eigenvalue $\sigma(m)$ under $B(m)$. -/
theorem brandt_eisenstein :
    brandt₂.mulVec ![1, 1] = (3 : ℤ) • ![1, 1] ∧ brandt₃.mulVec ![1, 1] = (4 : ℤ) • ![1, 1] ∧
      brandt₅.mulVec ![1, 1] = (6 : ℤ) • ![1, 1] := by
  unfold brandt₂ brandt₃ brandt₅
  decide +kernel

/-! ## Gross's formula (named) -/

/-- **Gross's formula, ratio form** (Gross 1987 `gross1987`, Prop. on special values [unverified]; the ratio form
is Waldspurger's theorem on the square classes of the inert discriminants): for fundamental discriminants $D_1, D_2 < 0$
with $11$ inert in $\mathbb Q(\sqrt{D_i})$, and `Lval D` $= L(f, D, 1) = L(f\otimes\chi_D, 1)$ for the newform $f$ of level
$11$,
$c(|D_1|)^2\sqrt{|D_2|}\,L(f,D_2,1) = c(|D_2|)^2\sqrt{|D_1|}\,L(f,D_1,1)$. -/
@[kb "gross1987" "L(f,1)L(f,D,1)√|D| proportional to c(|D|)² for 11 inert, level 11 [unverified]"]
structure GrossRatio (Lval : ℤ → ℝ) : Prop where
  ratio : ∀ D₁ D₂ : ℤ, IsFundamentalDiscriminant D₁ → IsFundamentalDiscriminant D₂ → D₁ < 0 → D₂ < 0 →
    jacobiSym D₁ 11 = -1 → jacobiSym D₂ 11 = -1 →
    (grossCoeff D₁.natAbs : ℝ) ^ 2 * Real.sqrt D₂.natAbs * Lval D₂ =
      (grossCoeff D₂.natAbs : ℝ) ^ 2 * Real.sqrt D₁.natAbs * Lval D₁

/-- **Vanishing transfers along the inert square classes:** given Gross's ratio and $L(f, D_0, 1) \ne 0$, $c(|D_0|) \ne 0$
for one inert $D_0$ (e.g. $D_0 = -3$, $c(3) = -1$), $c(|D|) = 0$ iff $L(f, D, 1) = 0$ for every inert $D$. -/
theorem grossCoeff_eq_zero_iff {Lval : ℤ → ℝ} (hG : GrossRatio Lval) {D₀ : ℤ}
    (hF₀ : IsFundamentalDiscriminant D₀) (hD₀ : D₀ < 0)
    (h₀ : jacobiSym D₀ 11 = -1) (hc₀ : grossCoeff D₀.natAbs ≠ 0) (hL₀ : Lval D₀ ≠ 0) {D : ℤ}
    (hF : IsFundamentalDiscriminant D) (hD : D < 0)
    (h : jacobiSym D 11 = -1) : grossCoeff D.natAbs = 0 ↔ Lval D = 0 := by
  have hr := hG.ratio D D₀ hF hF₀ hD hD₀ h h₀
  have p1 : 0 < Real.sqrt (D.natAbs : ℝ) := Real.sqrt_pos.mpr (by
    have : 0 < D.natAbs := Int.natAbs_pos.mpr (by omega)
    exact_mod_cast this)
  have p0 : 0 < Real.sqrt (D₀.natAbs : ℝ) := Real.sqrt_pos.mpr (by
    have : 0 < D₀.natAbs := Int.natAbs_pos.mpr (by omega)
    exact_mod_cast this)
  have hc0 : (grossCoeff D₀.natAbs : ℝ) ≠ 0 := by exact_mod_cast hc₀
  constructor
  · intro hc
    have hc' : (grossCoeff D.natAbs : ℝ) = 0 := by exact_mod_cast hc
    rw [hc'] at hr
    have := hr.symm
    have hD0 : D ≠ 0 := by omega
    simpa [hc0, p1.ne', hD0] using this
  · intro hL
    rw [hL] at hr
    have : (grossCoeff D.natAbs : ℝ) = 0 := by
      have hD00 : D₀ ≠ 0 := by omega
      simpa [p0.ne', hL₀, hD00] using hr
    exact_mod_cast this

end ModularFormsKB.HalfIntegral.Waldspurger.Gross
