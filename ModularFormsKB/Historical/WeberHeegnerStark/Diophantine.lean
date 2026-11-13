import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# The integer points of the Heegner quartic `y² = 2u(u³ + 1)`

Ported from Tau Ceti (`TauCeti/NumberTheory/ClassNumberOne/HeegnerQuartic.lean` and
`FourthPowerCubic.lean`, snapshot d2083f0f, Apache 2.0, The Tau Ceti contributors).

In Heegner's and Stark's proof of the class number one theorem, the values of `γ₂` at the CM
points of class number one are read off from the integer points of the quartic `y² = 2u(u³ + 1)`.
This file determines these points: they are `(u, y) = (-1, 0), (0, 0), (1, ±2), (2, ±6)`, and
deduces that `γ` is one of `0, -32, -96, -960, -5280, -640320`.

The proof is a descent through coprime factorizations. For `x³ = 2 y² + 1` we use that
`ℤ[√-2]` is a Euclidean domain (proved here by rounding division, modelled on Mathlib's
`GaussianInt`), hence a principal ideal domain with units `±1`; the other equations are handled
over `ℤ` by squeezing a square between consecutive squares.

## Main results

* `eq_zero_of_pow_three_eq_two_mul_sq_add_one`: `x³ = 2 y² + 1` forces `y = 0`.
* `sq_eq_two_mul_mul_pow_three_add_one_iff`: the integer points of `y² = 2u(u³ + 1)`.
* `heegner_gamma_mem`: the six possible values of `γ`.

## References

* H. M. Stark, *On the "gap" in a theorem of Heegner*, J. Number Theory 1 (1969), 16–27.
* L. J. Mordell, *Diophantine Equations*, Academic Press, 1969.
-/

namespace ModularFormsKB.WeberHeegnerStark

open Zsqrtd

/-- Rounding quotient in `ℤ[√-2]`. -/
private def zq (x y : ℤ√(-2)) : ℤ√(-2) :=
  ⟨(2 * (x * star y).re + y.norm) / (2 * y.norm),
    (2 * (x * star y).im + y.norm) / (2 * y.norm)⟩

private lemma round_err {a n : ℤ} (hn : 0 < n) :
    4 * (a - n * ((2 * a + n) / (2 * n))) ^ 2 ≤ n ^ 2 := by
  have h1 := Int.mul_ediv_add_emod (2 * a + n) (2 * n)
  have h2 := Int.emod_nonneg (2 * a + n) (by omega : 2 * n ≠ 0)
  have h3 := Int.emod_lt_of_pos (2 * a + n) (by omega : 0 < 2 * n)
  generalize (2 * a + n) / (2 * n) = q at h1 ⊢
  generalize (2 * a + n) % (2 * n) = r at h1 h2 h3
  have h4 : -n ≤ 2 * (a - n * q) := by nlinarith
  have h5 : 2 * (a - n * q) ≤ n := by nlinarith
  nlinarith

private lemma norm_pos' {y : ℤ√(-2)} (hy : y ≠ 0) : 0 < y.norm :=
  lt_of_le_of_ne (norm_nonneg (by norm_num) y) (Ne.symm fun h => hy ((norm_eq_zero_iff
    (by norm_num) y).1 h))

private lemma norm_zq_lt (x : ℤ√(-2)) {y : ℤ√(-2)} (hy : y ≠ 0) :
    (x - y * zq x y).norm < y.norm := by
  have hn : 0 < y.norm := norm_pos' hy
  have key : (x - y * zq x y).norm * y.norm =
      ((x * star y).re - y.norm * (zq x y).re) ^ 2 +
        2 * ((x * star y).im - y.norm * (zq x y).im) ^ 2 := by
    have : (x - y * zq x y).norm * (star y).norm =
        ((x - y * zq x y) * star y).norm := (norm_mul _ _).symm
    rw [norm_conj] at this
    rw [this]
    have e : (x - y * zq x y) * star y = x * star y - (y.norm : ℤ√(-2)) * zq x y := by
      rw [norm_eq_mul_conj]; ring
    rw [e, norm_def]
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, re_mul, im_mul, re_intCast, im_intCast]
    ring
  have h1 : 4 * ((x * star y).re - y.norm * (zq x y).re) ^ 2 ≤ y.norm ^ 2 :=
    round_err (a := (x * star y).re) hn
  have h2 : 4 * ((x * star y).im - y.norm * (zq x y).im) ^ 2 ≤ y.norm ^ 2 :=
    round_err (a := (x * star y).im) hn
  by_contra hlt
  rw [not_lt] at hlt
  nlinarith [mul_le_mul_of_nonneg_right hlt hn.le, mul_pos hn hn]

private instance instEuclideanDomain : EuclideanDomain (ℤ√(-2)) :=
  { (inferInstance : CommRing (ℤ√(-2))), (inferInstance : Nontrivial (ℤ√(-2))) with
    quotient := zq
    remainder := fun x y => x - y * zq x y
    quotient_zero := fun x => by
      ext <;> simp [zq]
    quotient_mul_add_remainder_eq := fun x y => by ring
    r := fun a b => (a.norm.natAbs < b.norm.natAbs)
    r_wellFounded := (measure fun a : ℤ√(-2) => a.norm.natAbs).wf
    remainder_lt := fun x y hy => by
      have := norm_zq_lt x hy
      have h0 := norm_nonneg (by norm_num : (-2 : ℤ) ≤ 0) (x - y * zq x y)
      omega
    mul_left_not_lt := fun a b hb => by
      rw [not_lt, norm_mul, Int.natAbs_mul]
      have : 0 < b.norm := norm_pos' hb
      exact Nat.le_mul_of_pos_right _ (by omega) }

/-- **The equation `x³ = 2 y² + 1`.** Every integer solution has `y = 0`, so `(x, y) = (1, 0)` is
the only one. -/
theorem eq_zero_of_pow_three_eq_two_mul_sq_add_one {x y : ℤ} (h : x ^ 3 = 2 * y ^ 2 + 1) :
    y = 0 := by
  -- Factor `x³ = (1 + y √-2)(1 - y √-2)` in the principal ideal domain `ℤ[√-2]`.
  set α : ℤ√(-2) := ⟨1, y⟩ with hα
  have hprod : α * star α = (x : ℤ√(-2)) ^ 3 := by
    rw [← Int.cast_pow, h]
    ext <;> simp [hα, -Int.cast_pow, -Int.cast_add, -Int.cast_mul]
    ring
  have hodd : Odd (x ^ 3) := ⟨y ^ 2, h⟩
  obtain ⟨r, s, hrs⟩ := Int.isCoprime_two_left.2 hodd
  have hcop : IsCoprime α (star α) := by
    refine ⟨r + s * star α, r, ?_⟩
    ext <;> simp [hα]
    · linear_combination hrs - s * h
    · ring
  -- So `α` is a cube up to a unit, and the units of `ℤ[√-2]` are `±1`.
  obtain ⟨δ, u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hcop hprod
  have hnorm : (u : ℤ√(-2)).norm = 1 :=
    (norm_eq_one_iff' (by norm_num) _).2 u.isUnit
  rw [norm_def] at hnorm
  have him : (u : ℤ√(-2)).im = 0 := by
    nlinarith [mul_self_nonneg (u : ℤ√(-2)).re, mul_self_nonneg (u : ℤ√(-2)).im]
  have hu2 : (u : ℤ√(-2)) ^ 2 = 1 := by
    simp only [him] at hnorm
    ext <;> simp [sq, him]
    linarith
  have hcube : (δ * u) ^ 3 = α := by
    rw [mul_pow, pow_succ (u : ℤ√(-2)) 2, hu2, one_mul, hu]
  generalize δ * (u : ℤ√(-2)) = ε at hcube
  obtain ⟨p, q⟩ := ε
  have hre := congrArg Zsqrtd.re hcube
  have hy := congrArg Zsqrtd.im hcube
  simp only [pow_succ, pow_zero, one_mul, re_mul, im_mul, hα] at hre hy
  have hp' : p * (p ^ 2 - 6 * q ^ 2) = 1 := by linear_combination hre
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hp' with rfl | rfl
  · have hq : q ^ 2 = 0 := by linarith
    rw [pow_eq_zero_iff two_ne_zero] at hq
    subst hq
    linarith
  · omega

/-- **The equation `m⁶ + 1 = 2 s²`.** Every integer solution has `m² = 1`. -/
theorem sq_eq_one_of_pow_six_add_one_eq_two_mul_sq {m s : ℤ} (h : m ^ 6 + 1 = 2 * s ^ 2) :
    m ^ 2 = 1 := by
  obtain ⟨k, hk⟩ : Odd m := by
    rcases Int.even_or_odd m with hm | hm
    · have h1 : Even (m ^ 6 + 1) := ⟨s ^ 2, by rw [h]; ring⟩
      exact absurd (Int.even_pow.2 ⟨hm, by norm_num⟩) (Int.even_add_one.1 h1)
    · exact hm
  -- `m² + 1 = 2 e` and `(m⁴ - m² + 1) e = s²`, so the odd factor `m⁴ - m² + 1` will be a square.
  set e := 2 * k ^ 2 + 2 * k + 1 with he_def
  have he : m ^ 2 + 1 = 2 * e := by rw [hk]; ring
  have hprod : (m ^ 4 - m ^ 2 + 1) * e = s ^ 2 :=
    mul_left_cancel₀ (two_ne_zero (α := ℤ)) (by rw [hk] at h ⊢; linear_combination h)
  -- `e² ≡ 1 (mod 3)` and `m⁴ - m² + 1 = 2 e (m² - 2) + 3`, so the two factors are coprime.
  have h3 : ((e ^ 2 - 1 : ℤ) : ZMod 3) = 0 := by
    rw [he_def]
    push_cast
    generalize (k : ZMod 3) = t
    revert t
    decide
  obtain ⟨r, hr⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 h3
  push_cast at hr
  have hcop : IsCoprime (m ^ 4 - m ^ 2 + 1) e :=
    ⟨-r, e + 2 * r * (m ^ 2 - 2), by linear_combination hr - r * (m ^ 2 - 2) * he⟩
  have hm1 : 1 ≤ m ^ 2 := by
    have : m ≠ 0 := by omega
    have : 0 < m ^ 2 := by positivity
    omega
  obtain ⟨q, hq | hq⟩ := Int.sq_of_isCoprime hcop hprod
  · -- The square `m⁴ - m² + 1` lies strictly between `(m² - 1)²` and `(m²)²` unless `m² = 1`.
    by_contra hne
    have hm2 : 2 ≤ m ^ 2 := by omega
    have h1 : |m ^ 2 - 1| < |q| := sq_lt_sq.1 (by nlinarith)
    have h2 : |q| < |m ^ 2| := sq_lt_sq.1 (by nlinarith)
    rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ m ^ 2 - 1)] at h1
    rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ m ^ 2)] at h2
    omega
  · nlinarith [sq_nonneg q, mul_nonneg (sq_nonneg m) (sub_nonneg.2 hm1)]

/-- **The equation `s² = 8 m⁶ + 1`.** Every integer solution has `m = 0` or `m² = 1`. -/
theorem eq_zero_or_sq_eq_one_of_sq_eq_eight_mul_pow_six_add_one {m s : ℤ}
    (h : s ^ 2 = 8 * m ^ 6 + 1) : m = 0 ∨ m ^ 2 = 1 := by
  have hs : Odd s := by
    rcases Int.even_or_odd s with hs | hs
    · exact absurd (⟨4 * m ^ 6, by rw [h]; ring⟩ : Odd (s ^ 2))
        (Int.not_odd_iff_even.2 (Int.even_pow.2 ⟨hs, two_ne_zero⟩))
    · exact hs
  -- Replacing `s` by `-s` if necessary, `s = 4 β + 1`.
  wlog hs4 : s % 4 = 1 generalizing s with H
  · have := Int.odd_iff.1 hs
    exact H (s := -s) (by rw [neg_sq, h]) hs.neg (by omega)
  set β := s / 4
  have hprod : β * (2 * β + 1) = m ^ 6 :=
    mul_left_cancel₀ (by norm_num : (8 : ℤ) ≠ 0) <| by
      rw [show s = 4 * β + 1 by omega] at h
      linear_combination h
  -- The coprime factors `β` and `2 β + 1` are sixth powers up to sign, which leads to the
  -- equations `x³ = 2 y² + 1` and `m⁶ + 1 = 2 s²`.
  have hcop : IsCoprime β (2 * β + 1) := ⟨-2, 1, by ring⟩
  obtain ⟨a, ha⟩ := exists_associated_pow_of_mul_eq_pow' hcop hprod
  obtain ⟨b, hb⟩ := exists_associated_pow_of_mul_eq_pow' hcop.symm (by rw [mul_comm, hprod])
  have ha6 : 0 ≤ a ^ 6 := by positivity
  have hb6 : 0 ≤ b ^ 6 := by positivity
  have hβ0 (hβ : β = 0) : m = 0 := by
    rw [hβ, zero_mul, eq_comm, pow_eq_zero_iff (by norm_num)] at hprod
    exact hprod
  rcases Int.associated_iff.1 ha with ha | ha <;> rcases Int.associated_iff.1 hb with hb | hb
  · -- `b⁶ = 2 a⁶ + 1`, so `a = 0`.
    have := eq_zero_of_pow_three_eq_two_mul_sq_add_one (x := b ^ 2) (y := a ^ 3)
      (by linear_combination hb - 2 * ha)
    rw [pow_eq_zero_iff (by norm_num)] at this
    exact .inl (hβ0 (by rw [← ha, this]; ring))
  · linarith
  · exact .inl (hβ0 (by omega))
  · -- `b⁶ + 1 = 2 a⁶`, so `b² = 1`, `β = -1` and `m⁶ = 1`.
    have hb2 := sq_eq_one_of_pow_six_add_one_eq_two_mul_sq (m := b) (s := a ^ 3)
      (by linear_combination hb - 2 * ha)
    have hβ : β = -1 := by
      have : b ^ 6 = (b ^ 2) ^ 3 := by ring
      rw [this, hb2] at hb
      omega
    rw [hβ] at hprod
    refine .inr ((pow_eq_one_iff_of_nonneg (sq_nonneg m) (by norm_num : 3 ≠ 0)).1 ?_)
    linear_combination -hprod

/-- The even case `u = 2 w` of the Heegner quartic: `w (8 w³ + 1)` is a square only for
`w = 0, 1`. -/
private theorem eq_zero_or_eq_one_of_mul_eight_mul_pow_three_add_one_eq_sq {w t : ℤ}
    (h : w * (8 * w ^ 3 + 1) = t ^ 2) : w = 0 ∨ w = 1 := by
  -- The factors `w` and `8 w³ + 1` are coprime, so both are squares up to sign.
  have hcop : IsCoprime w (8 * w ^ 3 + 1) := ⟨-8 * w ^ 2, 1, by ring⟩
  obtain ⟨m, hm | hm⟩ := Int.sq_of_isCoprime hcop h <;>
    obtain ⟨s, hs | hs⟩ := Int.sq_of_isCoprime hcop.symm (by rw [mul_comm, h])
  · -- `s² = 8 m⁶ + 1`.
    rcases eq_zero_or_sq_eq_one_of_sq_eq_eight_mul_pow_six_add_one (m := m) (s := s)
      (by rw [← hs, hm]; ring) with rfl | hm1
    · simp [hm]
    · simp [hm, hm1]
  · nlinarith [pow_nonneg (hm ▸ sq_nonneg m : 0 ≤ w) 3, sq_nonneg s]
  · -- `8 w³ + 1 = s² ≥ 0` with `w ≤ 0` forces `w = 0`.
    have hw3 : w ^ 3 ≤ 0 := Odd.pow_nonpos (by decide) (hm ▸ neg_nonpos.2 (sq_nonneg m))
    have : w ^ 3 = 0 := by nlinarith [sq_nonneg s]
    exact .inl ((pow_eq_zero_iff (by norm_num)).1 this)
  · -- `s² + 1 = -8 w³` is impossible modulo `4`.
    exfalso
    rcases Int.even_or_odd s with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;> ring_nf at hs <;> omega

/-- The odd case of the Heegner quartic: if `u³ + 1 = 2 v` and `u v` is a square, then
`u = ±1`. -/
private theorem eq_neg_one_or_eq_one_of_mul_eq_sq {u v t : ℤ} (hv : u ^ 3 + 1 = 2 * v)
    (h : u * v = t ^ 2) : u = -1 ∨ u = 1 := by
  -- The factors `u` and `v` are coprime, so both are squares up to sign.
  have hcop : IsCoprime u v := ⟨-u ^ 2, 2, by linear_combination -hv⟩
  obtain ⟨m, hm | hm⟩ := Int.sq_of_isCoprime hcop h
  · have hu : 0 ≤ u := hm ▸ sq_nonneg m
    obtain ⟨s, hs | hs⟩ := Int.sq_of_isCoprime hcop.symm (by rw [mul_comm, h])
    · -- `m⁶ + 1 = 2 s²`.
      have := sq_eq_one_of_pow_six_add_one_eq_two_mul_sq (m := m) (s := s)
        (by rw [← hs, ← hv, hm]; ring)
      simp [hm, this]
    · nlinarith [pow_nonneg hu 3, sq_nonneg s]
  · -- `u ≤ 0` and `u³ + 1 = ± 2 s²`; in both cases `u³ = -1`.
    have hu : u ≤ 0 := hm ▸ neg_nonpos.2 (sq_nonneg m)
    suffices hu3 : (-u) ^ 3 = 1 by
      have := (pow_eq_one_iff_of_nonneg (neg_nonneg.2 hu) (by norm_num)).1 hu3
      omega
    obtain ⟨s, hs | hs⟩ := Int.sq_of_isCoprime hcop.symm (by rw [mul_comm, h])
    · -- `u ≠ 0`, since `u³ + 1 = 2 v` is even.
      have hu1 : u ≤ -1 := by
        rcases hu.lt_or_eq with hu | rfl
        · omega
        · norm_num at hv; omega
      nlinarith [sq_nonneg s, sq_nonneg u, mul_nonneg (neg_nonneg.2 hu) (sq_nonneg u)]
    · -- `m⁶ = 2 s² + 1`.
      have := eq_zero_of_pow_three_eq_two_mul_sq_add_one (x := m ^ 2) (y := s)
        (by linear_combination -hv - 2 * hs + (m ^ 4 - m ^ 2 * u + u ^ 2) * hm)
      rw [this] at hs
      linear_combination -hv - 2 * hs

/-- **The integer points of the Heegner quartic.** The integer solutions of `y² = 2u(u³ + 1)` are
exactly `(u, y) = (-1, 0), (0, 0), (1, ±2), (2, ±6)`. -/
theorem sq_eq_two_mul_mul_pow_three_add_one_iff {u y : ℤ} :
    y ^ 2 = 2 * u * (u ^ 3 + 1) ↔
      (u, y) ∈ ({(-1, 0), (0, 0), (1, 2), (1, -2), (2, 6), (2, -6)} : Finset (ℤ × ℤ)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  refine ⟨fun h ↦ ?_, ?_⟩
  swap
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      norm_num
  -- It suffices to show `u ∈ {-1, 0, 1, 2}`, since `y` is then determined up to sign by `y²`.
  suffices hu : u = -1 ∨ u = 0 ∨ u = 1 ∨ u = 2 by
    have hy (c : ℤ) (hc : y ^ 2 = c ^ 2) : y = c ∨ y = -c := sq_eq_sq_iff_eq_or_eq_neg.1 hc
    rcases hu with rfl | rfl | rfl | rfl
    · rcases hy 0 (by linarith) with rfl | rfl <;> simp
    · rcases hy 0 (by linarith) with rfl | rfl <;> simp
    · rcases hy 2 (by linarith) with rfl | rfl <;> simp
    · rcases hy 6 (by linarith) with rfl | rfl <;> simp
  -- `y = 2 t` with `2 t² = u (u³ + 1)`; split according to the parity of `u`.
  obtain ⟨t, rfl⟩ : Even y := (Int.even_pow.1 ⟨u * (u ^ 3 + 1), by rw [h]; ring⟩).1
  have ht : 2 * t ^ 2 = u * (u ^ 3 + 1) :=
    mul_left_cancel₀ (two_ne_zero (α := ℤ)) (by linear_combination h)
  rcases Int.even_or_odd u with ⟨w, rfl⟩ | ⟨k, hk⟩
  · rcases eq_zero_or_eq_one_of_mul_eight_mul_pow_three_add_one_eq_sq (w := w) (t := t)
      (mul_left_cancel₀ (two_ne_zero (α := ℤ)) (by linear_combination -ht)) with rfl | rfl <;>
      simp
  · obtain ⟨v, hv⟩ : ∃ v, u ^ 3 + 1 = 2 * v :=
      ⟨4 * k ^ 3 + 6 * k ^ 2 + 3 * k + 1, by rw [hk]; ring⟩
    rcases eq_neg_one_or_eq_one_of_mul_eq_sq (t := t) hv
      (mul_left_cancel₀ (two_ne_zero (α := ℤ)) (by linear_combination -ht - u * hv)) with
      rfl | rfl <;> simp

/-- The integer conditions `c⁴ = 16` and `2(b² - 2ac) - (2b - a²)² = 0`, which say that the
fourth-power cubic of `X³ + a X² + b X + c` has the shape `X³ - γ X - 16`, are parametrized by the
integer points of `y² = 2u(u³ + 1)`. -/
private theorem exists_heegner_of_coeffs {a b c : ℤ} (hc : c ^ 4 = 16)
    (h : 2 * (b ^ 2 - 2 * a * c) - (2 * b - a ^ 2) ^ 2 = 0) :
    (c = 2 ∨ c = -2) ∧
      ∃ u y : ℤ, y ^ 2 = 2 * u * (u ^ 3 + 1) ∧ a = -c * u ∧ b = 4 * u ^ 2 - 2 * y := by
  have hc' : c = 2 ∨ c = -2 := by
    simpa [Nat.even_iff] using (pow_eq_pow_iff_of_ne_zero (by decide : (4 : ℕ) ≠ 0)).mp
      (show c ^ 4 = (2 : ℤ) ^ 4 by simpa using hc)
  refine ⟨hc', ?_⟩
  -- `(2b - a²)² = 2(b² - 2ac)` is even, hence so are `2b - a²`, `a²` and `a`.
  have ha : Even a := by
    have hsq : Even ((2 * b - a ^ 2) ^ 2) := ⟨b ^ 2 - 2 * a * c, by linear_combination -h⟩
    have heven : Even (2 * b - a ^ 2) := (Int.even_pow.1 hsq).1
    have ha2 : Even (a ^ 2) := by
      have := (even_two_mul b).sub heven
      rwa [sub_sub_cancel] at this
    exact (Int.even_pow.1 ha2).1
  obtain ⟨k, rfl⟩ := ha
  -- With `a = 2k`, Newton's identity reads `(a² - b)² = 4(2k⁴ - kc)`, so `a² - b` is even.
  have ht : Even ((k + k) ^ 2 - b) := by
    have h2 : 2 * (((k + k) ^ 2 - b) ^ 2 - 4 * (2 * k ^ 4 - k * c)) = 0 := by
      linear_combination -h
    have hsq : Even (((k + k) ^ 2 - b) ^ 2) := ⟨2 * (2 * k ^ 4 - k * c), by linarith⟩
    exact (Int.even_pow.1 hsq).1
  obtain ⟨m, hm⟩ := ht
  obtain rfl : b = (k + k) ^ 2 - (m + m) := by linarith
  have hy : 8 * (m ^ 2 - (2 * k ^ 4 - k * c)) = 0 := by linear_combination -h
  rcases hc' with rfl | rfl
  · exact ⟨-k, m, by linarith, by ring, by ring⟩
  · exact ⟨k, m, by linarith, by ring, by ring⟩

/-- **Heegner's coefficient condition.** Let `X³ + aX² + bX + c` be a monic integer cubic with
roots `r_i`. The cubic with roots `r_i²` has coefficients `e₁' = a² − 2b`, `e₂' = b² − 2ac`,
`e₃' = c²`, and the cubic with roots `r_i⁴` is
`X³ − (e₁'² − 2e₂')X² + (e₂'² − 2e₁'e₃')X − c⁴`. The hypothesis `h1` says its `X²` coefficient
vanishes, `hc` that its constant term is `−16`, and `hγ` that its `X` coefficient is `−γ`
(so the fourth-power cubic is `X³ − γX − 16`). Then `γ` is one of
`0, −32, −96, −960, −5280, −640320` (the values of `γ₂` at discriminants
`−3, −11, −19, −43, −67, −163`).

The proof turns `h1, hc` into `c = ±2` and an integer point `(u, y)` of `y² = 2u(u³ + 1)` with
`a = −c u`, `b = 4u² − 2y`, and then computes `γ` at the six points. -/
theorem heegner_gamma_mem {a b c γ : ℤ}
    (h1 : (a ^ 2 - 2 * b) ^ 2 = 2 * (b ^ 2 - 2 * a * c)) (hc : c ^ 4 = 16)
    (hγ : γ = -((b ^ 2 - 2 * a * c) ^ 2 - 2 * (a ^ 2 - 2 * b) * c ^ 2)) :
    γ ∈ ({0, -32, -96, -960, -5280, -640320} : Finset ℤ) := by
  have h : 2 * (b ^ 2 - 2 * a * c) - (2 * b - a ^ 2) ^ 2 = 0 := by linear_combination -h1
  obtain ⟨hc', u, y, hy, rfl, rfl⟩ := exists_heegner_of_coeffs hc h
  have := sq_eq_two_mul_mul_pow_three_add_one_iff.1 hy
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at this ⊢
  rcases hc' with rfl | rfl <;>
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num at hγ <;> simp [hγ]

end ModularFormsKB.WeberHeegnerStark
