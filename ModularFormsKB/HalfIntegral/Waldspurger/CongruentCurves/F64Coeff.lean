/-
# The coefficients of $f_{64}$ as a sum over a coset

$f_{64} = f_{32} \otimes \left(\frac 2\cdot\right)$ has coefficients $\left(\frac 2m\right) b(m)$ (`congruentCoeff 2 m`). Here
we show that these are the sums $\sum a$ over the pairs $(a, q) \in \mathbb Z^2$ with $a \equiv 1 \bmod 4$ and
$a^2 + 4q^2 = m$ (`sec64`, with $c = 2q$ the imaginary part): for $m \equiv 1 \bmod 8$ every such $(a, c)$ has
$4 \mid c$, so the condition $a + c \equiv 1 \bmod 4$ of $b$ is the condition $a \equiv 1 \bmod 4$; for
$m \equiv 5 \bmod 8$ one has $c \equiv 2 \bmod 4$ and $\alpha \mapsto -\alpha$ exchanges the two conditions, so the sum
changes sign, as does $\left(\frac 2m\right)$; for the other $m$ both sides vanish.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.F32Theta

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

/-- The pairs $(a, q)$ with $a \equiv 1 \bmod 4$ and $a^2 + 4q^2 = m$, in the box $|a|, |q| \le m$. -/
def sec64 (m : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(m : ℤ)) m) ×ˢ (Finset.Icc (-(m : ℤ)) m)).filter
    (fun v ↦ v.1 ^ 2 + 4 * v.2 ^ 2 = m ∧ v.1 % 4 = 1)

theorem mem_sec64 (m : ℕ) (p : ℤ × ℤ) : p ∈ sec64 m ↔ p.1 ^ 2 + 4 * p.2 ^ 2 = m ∧ p.1 % 4 = 1 := by
  simp only [sec64, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨h1, h2⟩
    have a1 := abs_le_sq p.1
    have a2 := abs_le_sq p.2
    have b1 := abs_le.mp (show |p.1| ≤ m by nlinarith [sq_nonneg p.2])
    have b2 := abs_le.mp (show |p.2| ≤ m by nlinarith [sq_nonneg p.1])
    exact ⟨⟨⟨b1.1, b1.2⟩, ⟨b2.1, b2.2⟩⟩, h1, h2⟩

/-- For odd `a` and even `c`: either `a² + c² ≡ 1 mod 8` and `4 ∣ c`, or `a² + c² ≡ 5 mod 8` and `c ≡ 2 mod 4`. -/
theorem sq_mod_eight (a c : ℤ) (ha : a % 2 = 1) (hc : c % 2 = 0) :
    ((a ^ 2 + c ^ 2) % 8 = 1 ∧ c % 4 = 0) ∨ ((a ^ 2 + c ^ 2) % 8 = 5 ∧ c % 4 = 2) := by
  have h8a : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
  have h8c : c % 8 = 0 ∨ c % 8 = 2 ∨ c % 8 = 4 ∨ c % 8 = 6 := by omega
  have e : (a ^ 2 + c ^ 2) % 8 = ((a % 8) ^ 2 + (c % 8) ^ 2) % 8 := by
    simp [pow_two, Int.add_emod, Int.mul_emod]
  rw [e]
  rcases h8a with h | h | h | h <;> rcases h8c with h' | h' | h' | h' <;> rw [h, h'] <;>
    first | (left; constructor <;> first | rfl | omega) | (right; constructor <;> first | rfl | omega)

theorem sum_im_sec64 (m : ℕ) : ∑ x ∈ sec64 m, x.2 = 0 := by
  have h : ∑ x ∈ sec64 m, x.2 = ∑ x ∈ sec64 m, -x.2 := by
    refine Finset.sum_nbij' (fun x ↦ (x.1, -x.2)) (fun x ↦ (x.1, -x.2)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [mem_sec64] at hx ⊢
      simpa using hx
    · intro x hx
      rw [mem_sec64] at hx ⊢
      simpa using hx
    · intro x _; simp
    · intro x _; simp
    · intro x _; simp
  linarith [Finset.sum_neg_distrib (s := sec64 m) (f := fun x : ℤ × ℤ ↦ x.2)]

theorem mem_primaryOfNorm_iff' (m : ℕ) (p : ℤ × ℤ) : p ∈ primaryOfNorm m ↔
    p.1 ^ 2 + p.2 ^ 2 = m ∧ p.1 % 2 = 1 ∧ p.2 % 2 = 0 ∧ (p.1 + p.2) % 4 = 1 := by
  simp only [primaryOfNorm, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨h1, h2, h3, h4⟩
    have a1 := abs_le_sq p.1
    have a2 := abs_le_sq p.2
    have b1 := abs_le.mp (show |p.1| ≤ m by nlinarith [sq_nonneg p.2])
    have b2 := abs_le.mp (show |p.2| ≤ m by nlinarith [sq_nonneg p.1])
    exact ⟨⟨⟨b1.1, b1.2⟩, ⟨b2.1, b2.2⟩⟩, h1, h2, h3, h4⟩

theorem empty_case (m : ℕ) (h1 : m % 8 ≠ 1) (h5 : m % 8 ≠ 5) :
    (∀ p : ℤ × ℤ, p ∉ sec64 m) ∧ (∀ p : ℤ × ℤ, p ∉ primaryOfNorm m) := by
  refine ⟨fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · rw [mem_sec64] at hp
    obtain ⟨hn, h4⟩ := hp
    have := sq_mod_eight p.1 (2 * p.2) (by omega) (by omega)
    have e : (2 * p.2) ^ 2 = 4 * p.2 ^ 2 := by ring
    rw [e, hn] at this
    omega
  · rw [mem_primaryOfNorm_iff'] at hp
    obtain ⟨hn, h2, h3, h4⟩ := hp
    have := sq_mod_eight p.1 p.2 h2 h3
    rw [hn] at this
    omega

theorem sum_re_sec64 (m : ℕ) : ∑ x ∈ sec64 m, x.1 = jacobiSym 2 m * f32Coeff m := by
  by_cases h : m % 8 = 1
  · -- m ≡ 1 mod 8
    have hj : jacobiSym 2 m = 1 := by
      rw [jacobiSym.at_two (Nat.odd_iff.mpr (by omega)),ZMod.χ₈_nat_eq_if_mod_eight]
      have h2 : m % 2 = 1 := by omega
      simp [h, h2]
    rw [hj, one_mul, f32Coeff]
    refine Finset.sum_nbij' (fun x ↦ (x.1, 2 * x.2)) (fun x ↦ (x.1, x.2 / 2)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [mem_sec64] at hx
      obtain ⟨hn, h4⟩ := hx
      rw [mem_primaryOfNorm_iff']
      have := sq_mod_eight x.1 (2 * x.2) (by omega) (by omega)
      have e : (2 * x.2) ^ 2 = 4 * x.2 ^ 2 := by ring
      rw [e, hn] at this
      refine ⟨by simp only; rw [← hn]; ring, by omega, by simp only; omega, by simp only; omega⟩
    · intro x hx
      rw [mem_primaryOfNorm_iff'] at hx
      obtain ⟨hn, h2, h3, h4⟩ := hx
      have := sq_mod_eight x.1 x.2 h2 h3
      rw [hn] at this
      obtain ⟨k, hk⟩ : ∃ k, x.2 = 2 * k := ⟨x.2 / 2, by omega⟩
      rw [mem_sec64]
      refine ⟨?_, by simp only; omega⟩
      simp only
      rw [hk] at hn ⊢
      rw [show 2 * k / 2 = k by omega]
      rw [← hn]; ring
    · intro x _; simp
    · intro x hx
      rw [mem_primaryOfNorm_iff'] at hx
      ext <;> simp only <;> omega
    · intro x _; simp
  by_cases h' : m % 8 = 5
  · -- m ≡ 5 mod 8
    have hj : jacobiSym 2 m = -1 := by
      rw [jacobiSym.at_two (Nat.odd_iff.mpr (by omega)),ZMod.χ₈_nat_eq_if_mod_eight]
      have h2 : m % 2 = 1 := by omega
      simp [h', h2]
    rw [hj, f32Coeff]
    push_cast
    rw [neg_one_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_nbij' (fun x ↦ (-x.1, 2 * x.2)) (fun x ↦ (-x.1, x.2 / 2)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [mem_sec64] at hx
      obtain ⟨hn, h4⟩ := hx
      rw [mem_primaryOfNorm_iff']
      have := sq_mod_eight x.1 (2 * x.2) (by omega) (by omega)
      have e : (2 * x.2) ^ 2 = 4 * x.2 ^ 2 := by ring
      rw [e, hn] at this
      refine ⟨by simp only; rw [← hn]; ring, by simp only; omega, by simp only; omega, by simp only; omega⟩
    · intro x hx
      rw [mem_primaryOfNorm_iff'] at hx
      obtain ⟨hn, h2, h3, h4⟩ := hx
      have := sq_mod_eight x.1 x.2 h2 h3
      rw [hn] at this
      obtain ⟨k, hk⟩ : ∃ k, x.2 = 2 * k := ⟨x.2 / 2, by omega⟩
      rw [mem_sec64]
      refine ⟨?_, by simp only; omega⟩
      simp only
      rw [hk] at hn ⊢
      rw [show 2 * k / 2 = k by omega]
      rw [← hn]; ring
    · intro x _; ext <;> simp
    · intro x hx
      rw [mem_primaryOfNorm_iff'] at hx
      ext <;> simp only <;> omega
    · intro x _; simp
  · obtain ⟨hs, hp⟩ := empty_case m h h'
    rw [f32Coeff, Finset.sum_eq_zero (fun x hx ↦ absurd hx (hs x)), Finset.sum_eq_zero (fun x hx ↦ absurd hx (hp x))]
    simp

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
