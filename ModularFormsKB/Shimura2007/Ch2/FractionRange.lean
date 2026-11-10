import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import ModularFormsKB.Citation
/-!
# Shimura 2007, Lemma 6.2: an elementary range lemma

G. Shimura, *Elementary Dirichlet Series and Modular Forms* (Springer 2007), Lemma 6.2, p. 45
(pdf p. 51). It locates the arguments $\varepsilon/s + j/d$ of the Euler polynomials in
Theorem 6.3 inside $[0, 1]$.

Shimura's $[d/s]$ is the integer part; for positive integers it is `d / s` (natural division),
and his $g$ is `shimuraG ε d s` with $\varepsilon = \pm 1$ encoded by a boolean (`true` for $+1$).
-/

namespace ModularFormsKB.Shimura2007

/-- Shimura's $g$ of Lemma 6.2: $g = [d/s] + 1$ if $\varepsilon = 1$ (`true`) and $g = -[d/s]$ if
$\varepsilon = -1$ (`false`). -/
def shimuraG (ε : Bool) (d s : ℕ) : ℤ :=
  if ε then ((d / s : ℕ) : ℤ) + 1 else -((d / s : ℕ) : ℤ)

/-- The sign $\varepsilon = \pm 1$ as a rational number. -/
def signOf (ε : Bool) : ℚ := if ε then 1 else -1

private lemma key (d s : ℕ) (hs : 0 < s) :
    ∃ n r : ℕ, d = s * n + r ∧ r < s ∧ d / s = n ∧ (r = 0 ↔ s ∣ d) :=
  ⟨d / s, d % s, (Nat.div_add_mod d s).symm, Nat.mod_lt d hs, rfl,
    (Nat.dvd_iff_mod_eq_zero).symm⟩

/-- **Lemma 6.2**: for positive integers $d, s$, $\varepsilon = \pm1$ and $g$ as above,
$0 \le \varepsilon/s + j/d \le 1$ for every $j \in \mathbb Z$ with $1 - g \le j \le d - g$;
moreover $0 < \varepsilon/s + j/d < 1$ for all such $j$ if $d/s \notin \mathbb Z$. -/
@[kb "shimura2007" "Lemma 6.2, p. 45"]
theorem lemma_6_2 (ε : Bool) {d s : ℕ} (hd : 0 < d) (hs : 0 < s) (j : ℤ)
    (hj1 : 1 - shimuraG ε d s ≤ j) (hj2 : j ≤ d - shimuraG ε d s) :
    (0 ≤ signOf ε / s + j / d ∧ signOf ε / s + j / d ≤ 1) ∧
      (¬ s ∣ d → 0 < signOf ε / s + j / d ∧ signOf ε / s + j / d < 1) := by
  obtain ⟨n, r, hdr, hrs, hn, hr0⟩ := key d s hs
  have hsQ : (0 : ℚ) < s := by exact_mod_cast hs
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hdrQ : (d : ℚ) = s * n + r := by exact_mod_cast hdr
  have hrsQ : (r : ℚ) < s := by exact_mod_cast hrs
  have hr0Q : (0 : ℚ) ≤ r := by positivity
  have e : ∀ x : ℚ, signOf ε / s + x / d = (signOf ε * d + x * s) / (s * d) := by
    intro x; field_simp
  have hsd : (0 : ℚ) < s * d := mul_pos hsQ hdQ
  simp only [e, le_div_iff₀ hsd, div_le_one hsd, lt_div_iff₀ hsd, div_lt_one hsd, zero_mul]
  cases ε with
  | true =>
    simp only [shimuraG, hn, ite_true] at hj1 hj2
    simp only [signOf, ite_true, one_mul]
    have h1 : ((-(n : ℤ) : ℤ) : ℚ) ≤ j := by exact_mod_cast (by omega : -(n : ℤ) ≤ j)
    have h2 : (j : ℚ) ≤ ((d : ℤ) - n - 1 : ℤ) := by exact_mod_cast (by omega : j ≤ (d : ℤ) - n - 1)
    push_cast at h1 h2
    refine ⟨⟨by nlinarith, by nlinarith⟩, fun hnd ↦ ⟨?_, by nlinarith⟩⟩
    have hrpos : (0 : ℚ) < r := by
      have : r ≠ 0 := fun h ↦ hnd (hr0.mp h)
      exact_mod_cast Nat.pos_of_ne_zero this
    nlinarith
  | false =>
    simp only [shimuraG, hn, Bool.false_eq_true, ite_false] at hj1 hj2
    simp only [signOf, Bool.false_eq_true, ite_false, neg_one_mul]
    have h1 : (((n : ℤ) + 1 : ℤ) : ℚ) ≤ j := by exact_mod_cast (by omega : (n : ℤ) + 1 ≤ j)
    have h2 : (j : ℚ) ≤ ((d : ℤ) + n : ℤ) := by exact_mod_cast (by omega : j ≤ (d : ℤ) + n)
    push_cast at h1 h2
    refine ⟨⟨by nlinarith, by nlinarith⟩, fun hnd ↦ ⟨by nlinarith, ?_⟩⟩
    have hrpos : (0 : ℚ) < r := by
      have : r ≠ 0 := fun h ↦ hnd (hr0.mp h)
      exact_mod_cast Nat.pos_of_ne_zero this
    nlinarith

end ModularFormsKB.Shimura2007
