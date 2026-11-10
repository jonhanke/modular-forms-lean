import ModularFormsKB.Iwaniec1997.KloostermanBounds

/-!
# Iwaniec, Chapter 4: Ramanujan sums at a prime and the moments $V_1(p)$, $V_2(p)$

H. Iwaniec, *Topics in Classical Automorphic Forms* (`iwaniec1997`), Section 4.4, pp. 61-62, and Section 3.3,
Example 1, p. 55.

## Items
- The Ramanujan sum at a prime modulus: `kloostermanMod_zero_left_prime`, `kloostermanMod_zero_right_prime`
  ($S(0,n;p) = S(n,0;p) = -1$ for $p \nmid n$).
- (4.22) `kloostermanMoment_one`: $V_1(p) = 1$.
- (4.23) `kloostermanMoment_two`: $V_2(p) = p^2 - p - 1$.
-/

open Complex Finset

noncomputable section

namespace ModularFormsKB.Iwaniec1997

variable {p : ℕ} [Fact p.Prime]

/-- A sum over the units of $\mathbb Z/p$ is the sum over all elements minus the term at $0$. -/
theorem sum_units_zmod (f : ZMod p → ℂ) :
    ∑ a : (ZMod p)ˣ, f (a : ZMod p) = ∑ x : ZMod p, f x - f 0 := by
  calc ∑ a : (ZMod p)ˣ, f (a : ZMod p) = ∑ x : {x : ZMod p // x ≠ 0}, f x :=
        Fintype.sum_equiv (unitsEquivNeZero (G₀ := ZMod p)) _ _ fun _ ↦ rfl
    _ = ∑ x ∈ univ.erase (0 : ZMod p), f x :=
        (Finset.sum_subtype (univ.erase (0 : ZMod p)) (p := fun x : ZMod p ↦ x ≠ 0) (by simp) f).symm
    _ = ∑ x : ZMod p, f x - f 0 := Finset.sum_erase_eq_sub (mem_univ _)

/-- $\sum_{x \bmod p} e(xb/p) = p$ if $b = 0$ and $0$ otherwise. -/
theorem sum_stdAddChar_mul (b : ZMod p) :
    ∑ x : ZMod p, ZMod.stdAddChar (x * b) = if b = 0 then (p : ℂ) else 0 := by
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p)]
  simp [ZMod.card]

/-- $\sum_{a \in (\mathbb Z/p)^\times} e(ab/p) = -1$ for $b \ne 0$. -/
theorem sum_units_stdAddChar_mul {b : ZMod p} (hb : b ≠ 0) :
    ∑ a : (ZMod p)ˣ, ZMod.stdAddChar ((a : ZMod p) * b) = -1 := by
  rw [sum_units_zmod (fun x ↦ ZMod.stdAddChar (x * b)), sum_stdAddChar_mul,
    ite_eq_right_of_eq_false _ _ (eq_false hb)]
  simp

/-- The sum of $e(d/p)$ over the units is $-1$. -/
theorem sum_units_stdAddChar : ∑ d : (ZMod p)ˣ, ZMod.stdAddChar (d : ZMod p) = -1 := by
  simpa using sum_units_stdAddChar_mul (p := p) (b := 1) one_ne_zero

/-- **Ramanujan sum at a prime**: $S(0,n;p) = -1$ if $p \nmid n$. -/
@[kb "iwaniec1997" "Section 3.3, Example 1, Ramanujan sum, p. 55"]
theorem kloostermanMod_zero_left_prime {n : ZMod p} (hn : n ≠ 0) : kloostermanMod p 0 n = -1 := by
  unfold kloostermanMod
  simp only [zero_mul, zero_add]
  simp_rw [mul_comm n]
  exact sum_units_stdAddChar_mul hn

/-- **Ramanujan sum at a prime**: $S(n,0;p) = -1$ if $p \nmid n$. -/
@[kb "iwaniec1997" "Section 3.3, Example 1, Ramanujan sum, p. 55"]
theorem kloostermanMod_zero_right_prime {n : ZMod p} (hn : n ≠ 0) : kloostermanMod p n 0 = -1 := by
  rw [kloostermanMod_comm, kloostermanMod_zero_left_prime hn]

/-- **(4.22)**: $V_1(p) = 1$. -/
@[kb "iwaniec1997" "Section 4.4, (4.22), p. 62"]
theorem kloostermanMoment_one : kloostermanMoment 1 p = 1 := by
  unfold kloostermanMoment kloostermanMod
  simp only [pow_one, one_mul]
  rw [Finset.sum_comm]
  have : ∀ d : (ZMod p)ˣ, ∑ a : (ZMod p)ˣ, ZMod.stdAddChar ((a : ZMod p) * ((d⁻¹ : (ZMod p)ˣ) : ZMod p)
      + (d : ZMod p)) = -ZMod.stdAddChar (d : ZMod p) := by
    intro d
    simp_rw [AddChar.map_add_eq_mul]
    rw [← Finset.sum_mul, sum_units_stdAddChar_mul (Units.ne_zero _)]
    ring
  simp_rw [this, Finset.sum_neg_distrib, sum_units_stdAddChar]
  simp

/-- For units $x, y$ of $\mathbb Z/p$, $\bar x + \bar y = 0$ iff $y = -x$. -/
theorem units_inv_add_inv_eq_zero_iff (x y : (ZMod p)ˣ) :
    ((x⁻¹ : (ZMod p)ˣ) : ZMod p) + ((y⁻¹ : (ZMod p)ˣ) : ZMod p) = 0 ↔ (y : ZMod p) = -(x : ZMod p) := by
  have hx : (x : ZMod p) ≠ 0 := x.ne_zero
  have hy : (y : ZMod p) ≠ 0 := y.ne_zero
  simp only [Units.val_inv_eq_inv_val]
  constructor
  · intro h
    field_simp at h
    linear_combination h
  · intro h
    rw [h]
    field_simp
    ring

/-- **(4.23)**: $V_2(p) = p^2 - p - 1$. -/
@[kb "iwaniec1997" "Section 4.4, (4.23), p. 62"]
theorem kloostermanMoment_two : kloostermanMoment 2 p = (p : ℂ) ^ 2 - p - 1 := by
  have hS0 : kloostermanMod p 0 1 = -1 := kloostermanMod_zero_left_prime one_ne_zero
  have hexp : ∀ a : ZMod p, kloostermanMod p a 1 ^ 2 =
      ∑ x : (ZMod p)ˣ, ∑ y : (ZMod p)ˣ, ZMod.stdAddChar ((x : ZMod p) + (y : ZMod p)) *
        ZMod.stdAddChar (a * (((x⁻¹ : (ZMod p)ˣ) : ZMod p) + ((y⁻¹ : (ZMod p)ˣ) : ZMod p))) := by
    intro a
    unfold kloostermanMod
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hall : ∑ a : ZMod p, kloostermanMod p a 1 ^ 2 = (p : ℂ) * (p - 1) := by
    simp_rw [hexp]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (univ : Finset (ZMod p))), ← Finset.mul_sum]
    have : ∀ x y : (ZMod p)ˣ, ∑ a : ZMod p, ZMod.stdAddChar
        (a * (((x⁻¹ : (ZMod p)ˣ) : ZMod p) + ((y⁻¹ : (ZMod p)ˣ) : ZMod p))) =
        if (y : ZMod p) = -(x : ZMod p) then (p : ℂ) else 0 := by
      intro x y
      rw [sum_stdAddChar_mul]
      simp only [units_inv_add_inv_eq_zero_iff]
    simp_rw [this]
    have h2 : ∀ x : (ZMod p)ˣ, ∑ y : (ZMod p)ˣ, ZMod.stdAddChar ((x : ZMod p) + (y : ZMod p)) *
        (if (y : ZMod p) = -(x : ZMod p) then (p : ℂ) else 0) = p := by
      intro x
      rw [Finset.sum_eq_single (-x)]
      · simp
      · intro y _ hy
        have : (y : ZMod p) ≠ -(x : ZMod p) := fun h ↦ hy (Units.ext (by simpa using h))
        simp [this]
      · simp
    simp_rw [h2]
    simp [ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : p.Prime)]
    rw [Nat.cast_sub (Fact.out : p.Prime).one_le]
    simp [mul_comm]
  unfold kloostermanMoment
  rw [sum_units_zmod (fun a ↦ kloostermanMod p a 1 ^ 2), hall, hS0]
  ring

end ModularFormsKB.Iwaniec1997
