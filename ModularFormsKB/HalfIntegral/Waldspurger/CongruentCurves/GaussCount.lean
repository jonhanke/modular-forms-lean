/-
# Gauss's point count for $y^2 = x^3 - x$

Proof of `GaussCountX3SubX` (statement in `PointCount.lean`), following
Ireland–Rosen, *A Classical Introduction to Modern Number Theory*, Ch. 18 §4 Thm 5 (via Jacobi sums of a quartic
character), proved here from scratch in $\mathbb Z[i]$.

Layout:
1. `rep_unique`, `f32Coeff_eq`: for $p = x^2 + y^2$ with $x$ odd, $y$ even, $x + y + 1 \equiv 0 \bmod 4$,
   `f32Coeff p = -2 * x` (uniqueness of the representation of a prime as a sum of two squares).
2. Quartic character `l` of $\mathbb F_p$ with values in $\mathbb Z[i]$, its Jacobi sum $J = J(l, l^2)$,
   $\sum_x \chi(x^3 - x) = J + \bar J$, $J \bar J = p$, and $J \equiv -1 \bmod (2 + 2i)$.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.PointCount
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

namespace GaussCount

/-! ### Part 1: uniqueness of the representation -/

lemma rep_unique {p : ℤ} {a c x y : ℤ} (h1 : a ^ 2 + c ^ 2 = p) (h2 : x ^ 2 + y ^ 2 = p)
    (ha : a % 2 = 1) (hc : c % 2 = 0) (hx : x % 2 = 1) (hy : y % 2 = 0)
    (hd : p ∣ a * x + c * y) : (a = x ∧ c = y) ∨ (a = -x ∧ c = -y) := by
  obtain ⟨k, hk⟩ := hd
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have hp0 : 0 < p := by
    have := sq_pos_of_ne_zero ha0
    nlinarith [sq_nonneg c]
  have hid : (a * x + c * y) ^ 2 + (a * y - c * x) ^ 2 = p ^ 2 := by
    have : (a * x + c * y) ^ 2 + (a * y - c * x) ^ 2 = (a ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2) := by ring
    rw [this, h1, h2]; ring
  rw [hk] at hid
  have hk2 : k ^ 2 ≤ 1 := by
    by_contra h
    replace h := not_le.mp h
    have h' : 2 ≤ k ^ 2 := by omega
    nlinarith [sq_nonneg (a * y - c * x), mul_le_mul_of_nonneg_left h' (sq_nonneg p), mul_pos hp0 hp0]
  have hk3 : k = -1 ∨ k = 0 ∨ k = 1 := by
    have h1' : k ≤ 1 := by nlinarith
    have h2' : -1 ≤ k := by nlinarith
    omega
  rcases hk3 with rfl | rfl | rfl
  · have hm : a * y - c * x = 0 := by
      have : (a * y - c * x) ^ 2 = 0 := by nlinarith
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    right
    have e1 : (a + x) ^ 2 + (c + y) ^ 2 = 0 := by nlinarith
    constructor <;> nlinarith [sq_nonneg (a + x), sq_nonneg (c + y)]
  · exfalso
    obtain ⟨a', ha'⟩ : ∃ a', a = 2 * a' + 1 := ⟨a / 2, by omega⟩
    obtain ⟨x', hx'⟩ : ∃ x', x = 2 * x' + 1 := ⟨x / 2, by omega⟩
    obtain ⟨c', hc'⟩ : ∃ c', c = 2 * c' := ⟨c / 2, by omega⟩
    obtain ⟨y', hy'⟩ : ∃ y', y = 2 * y' := ⟨y / 2, by omega⟩
    have : 2 * (2 * a' * x' + a' + x' + 2 * c' * y') + 1 = 0 := by
      rw [ha', hx', hc', hy'] at hk; linarith
    generalize 2 * a' * x' + a' + x' + 2 * c' * y' = t at this
    omega
  · have hm : a * y - c * x = 0 := by
      have : (a * y - c * x) ^ 2 = 0 := by nlinarith
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    left
    have e1 : (a - x) ^ 2 + (c - y) ^ 2 = 0 := by nlinarith
    constructor <;> nlinarith [sq_nonneg (a - x), sq_nonneg (c - y)]

lemma f32Coeff_eq {p : ℕ} (hp : p.Prime) {x y : ℤ} (h : x ^ 2 + y ^ 2 = p) (hx : x % 2 = 1)
    (hy : y % 2 = 0) (h4 : (x + y + 1) % 4 = 0) : f32Coeff p = -2 * x := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h' : (x.natAbs) ^ 2 = p := by
      have : ((x.natAbs : ℤ)) ^ 2 = p := by rw [Int.natAbs_sq]; simpa using h
      exact_mod_cast this
    have hd : x.natAbs ∣ p := ⟨x.natAbs, by rw [← h', sq]⟩
    have h2 := hp.two_le
    rcases hp.eq_one_or_self_of_dvd _ hd with h1 | h1
    · rw [h1] at h'; omega
    · rw [h1] at h'; nlinarith
  have hxb : -(p : ℤ) ≤ x ∧ x ≤ p := by
    constructor <;> nlinarith [sq_nonneg y, Int.le_self_sq x, Int.le_self_sq (-x)]
  have hyb : -(p : ℤ) ≤ y ∧ y ≤ p := by
    constructor <;> nlinarith [sq_nonneg x, Int.le_self_sq y, Int.le_self_sq (-y)]
  have hset : primaryOfNorm p = {(-x, y), (-x, -y)} := by
    ext ⟨a, c⟩
    simp only [primaryOfNorm, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨-, h1, h2, h3, h5⟩
      have hdiv : (p : ℤ) ∣ (a * x + c * y) * (a * x - c * y) :=
        ⟨p - y ^ 2 - c ^ 2, by linear_combination x ^ 2 * h1 + ((p : ℤ) - c ^ 2) * h⟩
      have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      rcases hpz.dvd_or_dvd hdiv with hd | hd
      · rcases rep_unique h1 h h2 h3 hx hy hd with ⟨h6, h7⟩ | ⟨h6, h7⟩
        · omega
        · right; exact ⟨h6, h7⟩
      · have hd' : (p : ℤ) ∣ a * x + (-c) * y := by
          have : a * x + (-c) * y = a * x - c * y := by ring
          rw [this]; exact hd
        rcases rep_unique (c := -c) (by linear_combination h1) h h2 (by omega) hx hy hd' with
          ⟨h6, h7⟩ | ⟨h6, h7⟩
        · omega
        · left; exact ⟨h6, by omega⟩
    · rintro (⟨h6, h7⟩ | ⟨h6, h7⟩)
      · subst h6; subst h7
        refine ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, by linear_combination h, by omega, by omega, by omega⟩
      · subst h6; subst h7
        refine ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, by linear_combination h, by omega, by omega, by omega⟩
  rw [f32Coeff, hset, Finset.sum_pair (by simp [Prod.ext_iff]; omega)]
  ring

/-! ### Part 2: a quartic character with values in `ℤ[i]` -/

section Quartic

variable {p : ℕ} [Fact p.Prime]

local notation "qc" => quadraticChar (ZMod p)

lemma gi_pow4 {z : GaussianInt} (h : z ^ 4 = 1) :
    z = 1 ∨ z = -1 ∨ z = ⟨0, 1⟩ ∨ z = ⟨0, -1⟩ := by
  have hi : (⟨0, 1⟩ : GaussianInt) * ⟨0, 1⟩ = -1 := by ext <;> simp
  have h0 : (z - 1) * (z + 1) * (z - ⟨0, 1⟩) * (z + ⟨0, 1⟩) = 0 := by
    linear_combination h + (1 - z ^ 2) * hi
  rcases mul_eq_zero.1 h0 with h0 | h0
  · rcases mul_eq_zero.1 h0 with h0 | h0
    · rcases mul_eq_zero.1 h0 with h0 | h0
      · left; exact sub_eq_zero.1 h0
      · right; left; exact eq_neg_of_add_eq_zero_left h0
    · right; right; left; exact sub_eq_zero.1 h0
  · right; right; right
    have : z = -⟨0, 1⟩ := eq_neg_of_add_eq_zero_left h0
    rw [this]; ext <;> simp

variable (l : MulChar (ZMod p) GaussianInt)

lemma l_pow4 (hl : orderOf l = 4) {u : ZMod p} (hu : u ≠ 0) : l u ^ 4 = 1 := by
  have h := congrArg (fun χ : MulChar (ZMod p) GaussianInt => χ u) (pow_orderOf_eq_one l)
  simp only [hl] at h
  rwa [MulChar.pow_apply' l (by norm_num), MulChar.one_apply (isUnit_iff_ne_zero.2 hu)] at h

lemma l_val (hl : orderOf l = 4) (u : ZMod p) :
    l u = 0 ∨ l u = 1 ∨ l u = -1 ∨ l u = ⟨0, 1⟩ ∨ l u = ⟨0, -1⟩ := by
  by_cases hu : u = 0
  · left; rw [hu]; exact MulChar.map_zero l
  · right; exact gi_pow4 (l_pow4 l hl hu)

lemma l_sq_sq (hl : orderOf l = 4) {v : ZMod p} (hv : v ≠ 0) : l (v * v) ^ 2 = 1 := by
  rw [map_mul, ← pow_two, ← pow_mul]; exact l_pow4 l hl hv

omit [Fact p.Prime] in
lemma l_sq_ne_one (hl : orderOf l = 4) : l ^ 2 ≠ 1 := by
  intro h
  have := orderOf_dvd_of_pow_eq_one h
  rw [hl] at this
  omega

lemma l_sq_eq_q (hl : orderOf l = 4) (u : ZMod p) : l u ^ 2 = (qc u : GaussianInt) := by
  by_cases hu : u = 0
  · subst hu
    rw [MulChar.map_zero l, quadraticChar_zero]; norm_num
  by_cases hs : IsSquare u
  · obtain ⟨v, rfl⟩ := hs
    have hv : v ≠ 0 := by rintro rfl; simp at hu
    rw [l_sq_sq l hl hv, (quadraticChar_one_iff_isSquare hu).2 ⟨v, rfl⟩]; simp
  · have hqu : qc u = -1 := quadraticChar_neg_one_iff_not_isSquare.2 hs
    rw [hqu]
    have h4 : (l u ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact l_pow4 l hl hu
    have h1 : l u ^ 2 ≠ 1 := by
      intro h1
      apply l_sq_ne_one l hl
      apply MulChar.ext'
      intro w
      rw [MulChar.pow_apply' l (by norm_num)]
      by_cases hw : w = 0
      · subst hw
        rw [MulChar.map_zero l, MulChar.map_zero (1 : MulChar (ZMod p) GaussianInt)]; norm_num
      rw [MulChar.one_apply (isUnit_iff_ne_zero.2 hw)]
      by_cases hws : IsSquare w
      · obtain ⟨v, rfl⟩ := hws
        have hv : v ≠ 0 := by rintro rfl; simp at hw
        exact l_sq_sq l hl hv
      · have hqw : qc w = -1 := quadraticChar_neg_one_iff_not_isSquare.2 hws
        have hqinv : qc u⁻¹ = -1 := by
          have h2 : qc u * qc u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hu]; simp
          rw [hqu] at h2; linarith
        have hsq : IsSquare (w * u⁻¹) := by
          rw [← quadraticChar_one_iff_isSquare (mul_ne_zero hw (inv_ne_zero hu)), map_mul, hqw, hqinv]
          norm_num
        obtain ⟨v, hv⟩ := hsq
        have hv0 : v ≠ 0 := by
          rintro rfl
          simp [hw, hu] at hv
        have hw' : w = u * (v * v) := by
          rw [← hv]; field_simp
        rw [hw', map_mul, mul_pow, h1, one_mul]
        exact l_sq_sq l hl hv0
    have h5 : (l u ^ 2 - 1) * (l u ^ 2 + 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.1 h5 with h | h
    · exact absurd (sub_eq_zero.1 h) h1
    · push_cast; exact eq_neg_of_add_eq_zero_left h

lemma sum_sq_eq {R : Type*} [CommRing R] (hF : ringChar (ZMod p) ≠ 2) (G : ZMod p → R) :
    ∑ x : ZMod p, G (x ^ 2) = ∑ w : ZMod p, ((qc w : R) + 1) * G w := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun x : ZMod p => x ^ 2) (fun x => G (x ^ 2))]
  refine Finset.sum_congr rfl fun w _ => ?_
  have : ∀ x ∈ Finset.univ.filter (fun x : ZMod p => x ^ 2 = w), G (x ^ 2) = G w := by
    intro x hx; rw [(Finset.mem_filter.1 hx).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  have h := quadraticChar_card_sqrts hF w
  have h2 : ((Finset.univ.filter (fun x : ZMod p => x ^ 2 = w)).card : ℤ) = qc w + 1 := by
    have hh : Finset.univ.filter (fun x : ZMod p => x ^ 2 = w) = {x : ZMod p | x ^ 2 = w}.toFinset := by
      ext x; simp
    rw [hh]; exact h
  have h3 := congrArg (Int.cast : ℤ → R) h2
  push_cast at h3
  rw [h3]

/-- The Jacobi sum $J(l, l^2) = \sum_u l(u)\,\chi(1-u)$, $\chi$ the quadratic character. -/
noncomputable def Jq (l : MulChar (ZMod p) GaussianInt) : GaussianInt :=
  ∑ u : ZMod p, l u * (qc (1 - u) : GaussianInt)

/-- Its conjugate $\sum_u \bar l(u)\,\chi(1-u)$. -/
noncomputable def Jq' (l : MulChar (ZMod p) GaussianInt) : GaussianInt :=
  ∑ u : ZMod p, l u ^ 3 * (qc (1 - u) : GaussianInt)

lemma T_eq (hp4 : p % 4 = 1) (hl : orderOf l = 4) :
    ((∑ x : ZMod p, qc (x ^ 3 - x) : ℤ) : GaussianInt) = Jq l + Jq' l := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hq1 : qc (-1) = 1 :=
    (quadraticChar_one_iff_isSquare (neg_ne_zero.2 one_ne_zero)).2
      (FiniteField.isSquare_neg_one_iff.2 (by rw [ZMod.card]; omega))
  have step : ∀ x : ZMod p, ((qc (x ^ 3 - x) : ℤ) : GaussianInt) =
      (fun w => l w * (qc (1 - w) : GaussianInt)) (x ^ 2) := by
    intro x
    have e : x ^ 3 - x = x * (-1 * (1 - x ^ 2)) := by ring
    have e2 : l (x ^ 2) = l x ^ 2 := by rw [pow_two, pow_two, map_mul]
    simp only
    rw [e, map_mul, map_mul, hq1, e2]
    push_cast
    rw [← l_sq_eq_q l hl x]
    ring
  push_cast
  rw [Finset.sum_congr rfl fun x _ => step x, sum_sq_eq hF (fun w : ZMod p => l w * (qc (1 - w) : GaussianInt)), Jq, Jq', ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← l_sq_eq_q l hl w]; ring

lemma Jq'_eq_star (hl : orderOf l = 4) : Jq' l = star (Jq l) := by
  simp only [Jq, Jq', star_sum, star_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [star_intCast]
  have : l u ^ 3 = star (l u) := by
    rcases l_val l hl u with h | h | h | h | h <;> rw [h] <;> ext <;> simp [pow_succ]
  rw [this]; ring

lemma Jq_eq_jacobiSum (hl : orderOf l = 4) : Jq l = jacobiSum l (l ^ 2) := by
  simp only [Jq, jacobiSum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [MulChar.pow_apply' l (by norm_num), l_sq_eq_q l hl]

lemma J_mul_J' (hl : orderOf l = 4) : Jq l * Jq' l = (p : GaussianInt) := by
  apply GaussianInt.toComplex_injective
  have hl1 : l ≠ 1 := fun h => by
    have := pow_ne_one_of_lt_orderOf (x := l) (n := 1) (by norm_num) (by rw [hl]; norm_num)
    exact this (by simpa using h)
  have hl2 : l ^ 2 ≠ 1 := l_sq_ne_one l hl
  have hl3 : l * l ^ 2 ≠ 1 := by
    rw [← pow_succ']
    exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hl]; norm_num)
  have hinj := GaussianInt.toComplex_injective
  have hchar : ringChar ℂ ≠ ringChar (ZMod p) := by
    rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]; exact (Fact.out : p.Prime).ne_zero.symm
  have hmain := jacobiSum_mul_jacobiSum_inv hchar
    ((MulChar.ringHomComp_ne_one_iff hinj).mpr hl1)
    ((MulChar.ringHomComp_ne_one_iff hinj).mpr hl2)
    (by rw [← MulChar.ringHomComp_mul]; exact (MulChar.ringHomComp_ne_one_iff hinj).mpr hl3)
  have hz : ∀ u, GaussianInt.toComplex (l u) = 0 ∨ GaussianInt.toComplex (l u) ^ 4 = 1 := by
    intro u
    by_cases hu : u = 0
    · left; rw [hu, MulChar.map_zero, map_zero]
    · right; rw [← map_pow, l_pow4 l hl hu, map_one]
  have hinv : ∀ z : ℂ, (z = 0 ∨ z ^ 4 = 1) → z⁻¹ = z ^ 3 ∧ (z ^ 2)⁻¹ = z ^ 2 := by
    rintro z (h | h)
    · subst h; simp
    · constructor
      · exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact h)
      · exact inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact h)
  have hJ1 : jacobiSum (l.ringHomComp GaussianInt.toComplex) ((l ^ 2).ringHomComp GaussianInt.toComplex)
      = GaussianInt.toComplex (Jq l) := by
    rw [jacobiSum_ringHomComp, Jq_eq_jacobiSum l hl]
  have hJ2 : jacobiSum (l.ringHomComp GaussianInt.toComplex)⁻¹ ((l ^ 2).ringHomComp GaussianInt.toComplex)⁻¹
      = GaussianInt.toComplex (Jq' l) := by
    simp only [jacobiSum, Jq', map_sum, map_mul, MulChar.inv_apply_eq_inv', MulChar.ringHomComp_apply]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [MulChar.pow_apply' l (by norm_num), (hinv _ (hz u)).1, map_pow]
    have := (hinv _ (hz (1 - u))).2
    rw [this, ← l_sq_eq_q l hl (1 - u)]
    simp
  rw [map_mul, ← hJ1, ← hJ2, hmain, ZMod.card]
  simp

/-! ### The congruence $J \equiv -1 \bmod (2 + 2i)$ -/

/-- The ideal $(2 + 2i)$ of $\mathbb Z[i]$. -/
def I22 : Ideal GaussianInt := Ideal.span {(⟨2, 2⟩ : GaussianInt)}

lemma four_mem : (4 : GaussianInt) ∈ I22 :=
  Ideal.mem_span_singleton.2 ⟨⟨1, -1⟩, by ext <;> simp⟩

lemma two_mul_sub_one_mem {w : GaussianInt} (hw : w = 1 ∨ w = -1 ∨ w = ⟨0, 1⟩ ∨ w = ⟨0, -1⟩) :
    2 * (w - 1) ∈ I22 := by
  rcases hw with rfl | rfl | rfl | rfl
  · simp
  · exact Ideal.mem_span_singleton.2 ⟨⟨-1, 1⟩, by ext <;> simp⟩
  · exact Ideal.mem_span_singleton.2 ⟨⟨0, 1⟩, by ext <;> simp⟩
  · exact Ideal.mem_span_singleton.2 ⟨⟨-1, 0⟩, by ext <;> simp⟩

lemma two_ne_zero_zmod (hp4 : p % 4 = 1) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h1 := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h)
  have := Nat.le_of_dvd (by norm_num) h1
  have := (Fact.out : p.Prime).two_le
  omega

lemma J2_eq (hp4 : p % 4 = 1) (hl : orderOf l = 4) :
    jacobiSum l l = l (((2 : ZMod p)⁻¹) ^ 2) * Jq l := by
  have h2 := two_ne_zero_zmod (p := p) hp4
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have h22 : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have hl1 : l ≠ 1 := fun h => by
    have := pow_ne_one_of_lt_orderOf (x := l) (n := 1) (by norm_num) (by rw [hl]; norm_num)
    exact this (by simpa using h)
  have e1 : ∀ u : ZMod p, l u * l (1 - u) =
      l (((2 : ZMod p)⁻¹) ^ 2) * l (1 - (2 * u - 1) ^ 2) := by
    intro u
    rw [← map_mul, ← map_mul]
    congr 1
    linear_combination (-(u * (1 - u) * (1 + 2 * 2⁻¹))) * h22
  have hs1 : ∑ u : ZMod p, l (1 - (2 * u - 1) ^ 2) = ∑ v : ZMod p, l (1 - v ^ 2) :=
    Equiv.sum_comp ((Equiv.mulLeft₀ 2 h2).trans (Equiv.subRight 1)) (fun v => l (1 - v ^ 2))
  have hs2 := sum_sq_eq hF (fun w => l (1 - w))
  have hs3 : ∑ w : ZMod p, l (1 - w) = 0 := by
    have := Equiv.sum_comp (Equiv.subLeft 1) l
    simp only [Equiv.subLeft_apply] at this
    rw [this]
    exact MulChar.sum_eq_zero_of_ne_one hl1
  have hs4 : ∑ w : ZMod p, ((qc w : GaussianInt) + 1) * l (1 - w) = Jq l := by
    simp only [add_mul, one_mul, Finset.sum_add_distrib]
    rw [hs3, add_zero, Jq]
    rw [← Equiv.sum_comp (Equiv.subLeft 1) (fun w => (qc w : GaussianInt) * l (1 - w))]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Equiv.subLeft_apply, sub_sub_cancel]
    ring
  rw [jacobiSum, Finset.sum_congr rfl fun u _ => e1 u, ← Finset.mul_sum, hs1]
  congr 1
  rw [← hs4]; exact hs2

lemma e_sq (hp4 : p % 4 = 1) (hl : orderOf l = 4) :
    l (((2 : ZMod p)⁻¹) ^ 2) * l (((2 : ZMod p)⁻¹) ^ 2) = 1 := by
  have h2 := two_ne_zero_zmod (p := p) hp4
  have e2 : l (((2 : ZMod p)⁻¹) ^ 2) = l (2 : ZMod p)⁻¹ ^ 2 := by rw [pow_two, pow_two, map_mul]
  rw [e2, ← pow_add]
  exact l_pow4 l hl (inv_ne_zero h2)

local notation "π₂₂" => Ideal.Quotient.mk I22

lemma J2_mod (hp4 : p % 4 = 1) (hl : orderOf l = 4) :
    ∃ c : ℕ, c + 3 = p ∧
      π₂₂ (jacobiSum l l) = π₂₂ (l (((2 : ZMod p)⁻¹) ^ 2)) + (c : GaussianInt ⧸ I22) := by
  classical
  have h2 := two_ne_zero_zmod (p := p) hp4
  have h22 : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  set i : ZMod p := 2⁻¹ with hi
  have hi0 : i ≠ 0 := inv_ne_zero h2
  have hi1 : i ≠ 1 := by
    intro h
    rw [h] at h22
    have : (1 : ZMod p) = 0 := by linear_combination h22
    exact one_ne_zero this
  have h1i : 1 - i = i := by linear_combination (-1) * h22
  obtain ⟨S, hS⟩ : ∃ S : Finset (ZMod p), S = (Finset.univ \ {0, 1}).erase i := ⟨_, rfl⟩
  have hmem : i ∈ (Finset.univ \ {0, 1} : Finset (ZMod p)) := by
    simp [hi0, hi1]
  have hSmem : ∀ u, u ∈ S ↔ (u ≠ i ∧ u ≠ 0 ∧ u ≠ 1) := by
    intro u; rw [hS]
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or, ne_eq]
  have hcard : S.card + 3 = p := by
    have h1 : ((Finset.univ \ {0, 1} : Finset (ZMod p))).card = p - 2 := by
      rw [Finset.card_univ_sdiff, ZMod.card, Finset.card_pair zero_ne_one]
    have h3 := Finset.card_erase_of_mem hmem
    have := (Fact.out : p.Prime).two_le
    rw [← hS] at h3
    omega
  refine ⟨S.card, hcard, ?_⟩
  rw [jacobiSum_eq_sum_sdiff, ← Finset.add_sum_erase _ _ hmem, ← hS, map_add, map_sum]
  have hwi : l i * l (1 - i) = l (i ^ 2) := by rw [h1i, pow_two, map_mul]
  rw [hwi]
  congr 1
  have hinv : ∑ u ∈ S, (π₂₂ (l u * l (1 - u)) - 1) = 0 := by
    refine Finset.sum_involution (fun u _ => 1 - u) ?_ ?_ ?_ ?_
    · intro u hu
      obtain ⟨hui, hu0, hu1⟩ := (hSmem u).1 hu
      have hw : (l u * l (1 - u)) ^ 4 = 1 := by
        rw [mul_pow, l_pow4 l hl hu0, l_pow4 l hl (sub_ne_zero.2 (Ne.symm hu1)), one_mul]
      have hm := two_mul_sub_one_mem (gi_pow4 hw)
      have e : π₂₂ (2 * (l u * l (1 - u) - 1)) = 2 * (π₂₂ (l u * l (1 - u)) - 1) := by
        rw [map_mul π₂₂, map_ofNat π₂₂ 2, map_sub, map_one]
      have : π₂₂ (l u * l (1 - u)) - 1 + (π₂₂ (l (1 - u) * l (1 - (1 - u))) - 1) =
          π₂₂ (2 * (l u * l (1 - u) - 1)) := by
        rw [sub_sub_cancel, mul_comm (l (1 - u)) (l u), e]
        ring
      rw [this]; exact Ideal.Quotient.eq_zero_iff_mem.2 hm
    · intro u hu _ h
      obtain ⟨hui, hu0, hu1⟩ := (hSmem u).1 hu
      have h' : 2 * u = 1 := by linear_combination (-1) * h
      exact hui (by linear_combination i * h' - u * h22)
    · intro u hu
      obtain ⟨hui, hu0, hu1⟩ := (hSmem u).1 hu
      rw [hSmem]
      refine ⟨fun h => hui ?_, fun h => hu1 ?_, fun h => hu0 ?_⟩
      · linear_combination (-1) * h + h1i
      · linear_combination (-1) * h
      · linear_combination (-1) * h
    · intro u hu
      simp
  calc ∑ u ∈ S, π₂₂ (l u * l (1 - u))
      = ∑ u ∈ S, (π₂₂ (l u * l (1 - u)) - 1) + ∑ u ∈ S, (1 : GaussianInt ⧸ I22) := by
        rw [← Finset.sum_add_distrib]; simp
    _ = S.card := by rw [hinv]; simp

lemma J_cong (hp4 : p % 4 = 1) (hl : orderOf l = 4) : (⟨2, 2⟩ : GaussianInt) ∣ Jq l + 1 := by
  obtain ⟨c, hc, hmod⟩ := J2_mod l hp4 hl
  have hee := e_sq l hp4 hl
  have hJ : Jq l = l (((2 : ZMod p)⁻¹) ^ 2) * jacobiSum l l := by
    rw [J2_eq l hp4 hl, ← mul_assoc, hee, one_mul]
  have hcases : l (((2 : ZMod p)⁻¹) ^ 2) = 1 ∨ l (((2 : ZMod p)⁻¹) ^ 2) = -1 := by
    have : (l (((2 : ZMod p)⁻¹) ^ 2) - 1) * (l (((2 : ZMod p)⁻¹) ^ 2) + 1) = 0 := by
      linear_combination hee
    rcases mul_eq_zero.1 this with h | h
    · left; exact sub_eq_zero.1 h
    · right; exact eq_neg_of_add_eq_zero_left h
  obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 1 := ⟨p / 4, by omega⟩
  have h4 : (4 : GaussianInt ⧸ I22) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 four_mem
    rwa [map_ofNat π₂₂ 4] at this
  have hc' : (c : GaussianInt ⧸ I22) + 2 = 4 * k := by
    have : c + 2 = 4 * k := by omega
    exact_mod_cast congrArg (Nat.cast : ℕ → GaussianInt ⧸ I22) this
  have : Jq l + 1 ∈ I22 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, map_one, hJ, map_mul, hmod]
    rcases hcases with he | he
    · rw [he, map_one]; linear_combination hc' + (k : GaussianInt ⧸ I22) * h4
    · rw [he, map_neg, map_one]
      linear_combination (-1) * hc' + (1 - (k : GaussianInt ⧸ I22)) * h4
  exact Ideal.mem_span_singleton.1 this

end Quartic

end GaussCount

open GaussCount in
/-- **Gauss's point count for $y^2 = x^3 - x$** (Gauss; Ireland–Rosen Ch. 18 §4 Thm. 5): for $p \equiv 1 \bmod 4$,
$a_p(E_1) = b(p)$. -/
theorem gaussCountX3SubX : GaussCountX3SubX := by
  refine ⟨fun p _ hp4 => ?_⟩
  have hp := (Fact.out : p.Prime)
  have hp2 : p ≠ 2 := by omega
  have hprim : IsPrimitiveRoot (⟨0, 1⟩ : GaussianInt) 4 := by
    apply IsPrimitiveRoot.of_map_of_injective (f := GaussianInt.toComplex) _
      GaussianInt.toComplex_injective
    have : GaussianInt.toComplex ⟨0, 1⟩ = Complex.I := by simp [GaussianInt.toComplex_def']
    rw [this]; exact Complex.isPrimitiveRoot_I
  obtain ⟨l, hl⟩ := MulChar.exists_mulChar_orderOf (ZMod p) (by rw [ZMod.card]; omega) hprim
  have hN := J_mul_J' l hl
  rw [Jq'_eq_star l hl] at hN
  have hT := T_eq l hp4 hl
  rw [Jq'_eq_star l hl] at hT
  generalize hTdef : (∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - x)) = T at hT
  obtain ⟨w, hw⟩ := J_cong l hp4 hl
  generalize Jq l = J at hN hT hw
  have hN1 := congrArg Zsqrtd.re hN
  have hT1 := congrArg Zsqrtd.re hT
  have hw1 := congrArg Zsqrtd.re hw
  have hw2 := congrArg Zsqrtd.im hw
  simp at hN1 hT1 hw1 hw2
  rw [frobeniusTrace_congruentCurveMod hp2]
  simp only [Nat.cast_one, one_pow, one_mul]
  rw [hTdef, hT1]
  rw [f32Coeff_eq hp (x := J.re) (y := J.im) (by nlinarith) (by omega) (by omega) (by omega)]
  ring

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
