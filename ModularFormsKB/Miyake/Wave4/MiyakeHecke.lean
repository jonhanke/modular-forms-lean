import ModularFormsKB.Miyake.Wave4.Notation
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Composite
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.ElementaryDivisors

/-!
# Miyake §4.5: `T(n)` as the sum of the double cosets of determinant `n`; Lemmas 4.5.6–4.5.8

Miyake, *Modular Forms* (Springer 1989), §4.5, pp. 136–142.

Miyake defines (p. 136)

  `T(n) = Σ_{l m = n, l ∣ m, (l, N) = 1} T(l, m)`,   `T(l, m) = Γ₀(N) diag(l, m) Γ₀(N)`,

the sum of all double cosets of `Δ₀(N)` of determinant `n` (by Lemma 4.5.2 every such double coset
is one `T(l, m)`). This is `miyakeHeckeT N n`; the coprimality guard is built into Tau Ceti's
`diagElemGamma0`, which is `0` when `(l, N) ≠ 1`.

Tau Ceti instead builds `heckeTCompositeGamma0 N n` from the recurrence that Miyake proves as
Lemma 4.5.7. The double-coset relations of Lemmas 4.5.7 (1) and 4.5.8 (1) at level `N` are in neither Mathlib
nor Tau Ceti; they are the named input `DoubleCosetRelations N`. From it this file proves
Lemma 4.5.7 (2) and Lemma 4.5.8 (2) for Miyake's `T(n)` and that the two definitions agree
(`miyakeHeckeT_eq_heckeTCompositeGamma0`), so that every statement of wave 4 written with
`heckeTCompositeGamma0` is about Miyake's `T(n)`, conditionally on the input.
-/

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups HeckeCosetModule

noncomputable section

namespace ModularFormsKB.Miyake.Wave4

/-- Shorthand for the Hecke ring `ℛ(N) = ℛ(Γ₀(N), Δ₀(N))` over `ℤ`. -/
abbrev HeckeRingGamma0 (N : ℕ) [NeZero N] : Type :=
  𝕋 (HeckeRing.GL2.Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ

variable (N : ℕ) [NeZero N]

/-- Miyake's `T(l, m) = Γ₀(N) diag(l, m) Γ₀(N)` (p. 133), `0` unless `l, m ≥ 1` and
`(l, N) = 1`. -/
abbrev heckeTPair (l m : ℕ) : HeckeRingGamma0 N := HeckeRing.GL2.diagElemGamma0 N ![l, m]

/-- **Miyake's `T(n)`** (p. 136): `Σ_{l m = n, l ∣ m, (l, N) = 1} T(l, m)`. -/
def miyakeHeckeT (n : ℕ) : HeckeRingGamma0 N :=
  ∑ l ∈ n.divisors with l ∣ n / l, heckeTPair N l (n / l)

/-- **Named input: Miyake, Lemmas 4.5.7 (1) and 4.5.8 (1)** (pp. 140–141), the relations among
the double cosets `T(l, m)` of `ℛ(N)` that Miyake proves by counting right cosets
(Lemma 4.5.6) and comparing degrees. Tau Ceti proves the level-one analogue
(`HeckeRing.GLn.diagElem_mul_of_coprime`) but not these level-`N` products, so they are assumed
here and every consequence below is conditional on them.

* `mul_of_coprime` (Lemma 4.5.8 (1)): `T(l, m) T(l', m') = T(l l', m m')` if `(l m, l' m') = 1`
  (with `l ∣ m`, `l' ∣ m'`, as in Miyake's `T(l, m)`).
* `one_prime_mul` (Lemma 4.5.7 (1), `p ∤ N`): `T(1, p) T(1, p^e) = T(1, p^{e+1}) + c T(p, p^e)`
  with `c = p + 1` if `e = 1`, `c = p` if `e ≥ 2` (Miyake writes `p T(p, p) T(1, p^{e-1})` for the
  last term, which is `p T(p, p^e)` by `HeckeRing.GL2.diagElemGamma0_const_mul`).
* `one_prime_mul_of_dvd` (Lemma 4.5.7 (1), `p ∣ N`): `T(1, p) T(1, p^e) = T(1, p^{e+1})`. -/
@[kb "miyake1989" "Lemma 4.5.7 (1), p. 140; Lemma 4.5.8 (1), p. 141 (double cosets, assumed)"]
structure DoubleCosetRelations (N : ℕ) [NeZero N] : Prop where
  mul_of_coprime : ∀ {l m l' m' : ℕ}, l ∣ m → l' ∣ m' → (l * m).Coprime (l' * m') →
    heckeTPair N l m * heckeTPair N l' m' = heckeTPair N (l * l') (m * m')
  one_prime_mul : ∀ {p : ℕ}, p.Prime → ¬ p ∣ N → ∀ {e : ℕ}, 1 ≤ e →
    heckeTPair N 1 p * heckeTPair N 1 (p ^ e) =
      heckeTPair N 1 (p ^ (e + 1)) + ((if e = 1 then p + 1 else p : ℕ) : ℤ) • heckeTPair N p (p ^ e)
  one_prime_mul_of_dvd : ∀ {p : ℕ}, p.Prime → p ∣ N → ∀ e : ℕ,
    heckeTPair N 1 p * heckeTPair N 1 (p ^ e) = heckeTPair N 1 (p ^ (e + 1))

private lemma heckeTPair_scalar_mul (c b : ℕ) :
    heckeTPair N c (c * b) = heckeTPair N c c * heckeTPair N 1 b := by
  have h := HeckeRing.GL2.diagElemGamma0_const_mul N c ![1, b]
  have e1 : ((fun _ : Fin 2 ↦ c) : Fin 2 → ℕ) = ![c, c] := by ext i; fin_cases i <;> rfl
  have e2 : ((fun _ : Fin 2 ↦ c) * ![1, b] : Fin 2 → ℕ) = ![c, c * b] := by
    ext i; fin_cases i <;> simp
  rw [e2, e1] at h
  exact h.symm

private lemma heckeTPair_scalar_pow {p : ℕ} (i : ℕ) :
    heckeTPair N p p ^ i = heckeTPair N (p ^ i) (p ^ i) := by
  have := HeckeRing.GL2.heckeTScalarGamma0_pow N p i
  simpa [HeckeRing.GL2.heckeTScalarGamma0_def] using this

private lemma miyakeHeckeT_prime_pow_sum {p : ℕ} (hp : p.Prime) (e : ℕ) :
    miyakeHeckeT N (p ^ e) = ∑ i ∈ Finset.range (e / 2 + 1),
      heckeTPair N p p ^ i * heckeTPair N 1 (p ^ (e - 2 * i)) := by
  unfold miyakeHeckeT
  rw [Nat.divisors_prime_pow hp, Finset.filter_map, Finset.sum_map]
  have hf : Finset.filter ((fun l => l ∣ p ^ e / l) ∘ ⇑(⟨fun i => p ^ i, Nat.pow_right_injective hp.two_le⟩ : ℕ ↪ ℕ)) (Finset.range (e + 1)) = Finset.range (e / 2 + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Function.comp, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩
      rw [Nat.pow_div (by omega) hp.pos, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at h2
      omega
    · intro h
      refine ⟨by omega, ?_⟩
      rw [Nat.pow_div (by omega) hp.pos, Nat.pow_dvd_pow_iff_le_right hp.one_lt]
      omega
  rw [hf]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range] at hi
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div (by omega) hp.pos, heckeTPair_scalar_pow]
  have : p ^ (e - i) = p ^ i * p ^ (e - 2 * i) := by rw [← pow_add]; congr 1; omega
  rw [this, heckeTPair_scalar_mul]

/-- The Hecke ring as a commutative ring (local, as in Tau Ceti's `Composite.lean`). -/
@[instance_reducible]
private noncomputable def commRingR : CommRing (HeckeRingGamma0 N) :=
  { (inferInstance : Ring (HeckeRingGamma0 N)) with
    mul_comm := HeckeCosetModule.mul_comm_of_antiInvolution ℤ
      (HeckeRing.GL2.atkinLehnerAntiInvolution N)
      (HeckeRing.GL2.atkinLehnerAntiInvolution_onHeckeCoset_eq_self N) }

private lemma M_zero {p : ℕ} (hp : p.Prime) : miyakeHeckeT N (p ^ 0) = 1 := by
  rw [miyakeHeckeT_prime_pow_sum N hp 0]
  simp

private lemma M_one {p : ℕ} (hp : p.Prime) : miyakeHeckeT N (p ^ 1) = heckeTPair N 1 p := by
  rw [miyakeHeckeT_prime_pow_sum N hp 1]
  simp

private lemma M_add_two {p : ℕ} (hp : p.Prime) (e : ℕ) :
    miyakeHeckeT N (p ^ (e + 2)) =
      heckeTPair N 1 (p ^ (e + 2)) + heckeTPair N p p * miyakeHeckeT N (p ^ e) := by
  rw [miyakeHeckeT_prime_pow_sum N hp (e + 2), miyakeHeckeT_prime_pow_sum N hp e]
  have hs : ∑ i ∈ Finset.range (e / 2 + 1),
        heckeTPair N p p ^ (i + 1) * heckeTPair N 1 (p ^ (e + 2 - 2 * (i + 1))) =
      heckeTPair N p p * ∑ i ∈ Finset.range (e / 2 + 1),
        heckeTPair N p p ^ i * heckeTPair N 1 (p ^ (e - 2 * i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show e + 2 - 2 * (i + 1) = e - 2 * i by omega, pow_succ', mul_assoc]
  have : (e + 2) / 2 + 1 = e / 2 + 1 + 1 := by omega
  rw [this, Finset.sum_range_succ', hs, add_comm]
  simp

private lemma rel_one (hR : DoubleCosetRelations N) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) :
    heckeTPair N 1 p * heckeTPair N 1 p =
      heckeTPair N 1 (p ^ 2) + ((p : ℤ) + 1) • heckeTPair N p p := by
  have h := hR.one_prime_mul hp hpN (e := 1) le_rfl
  simp only [pow_one, ↓reduceIte, Nat.reduceAdd] at h
  rw [h, Nat.cast_add, Nat.cast_one]

private lemma rel_succ (hR : DoubleCosetRelations N) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (k : ℕ) :
    heckeTPair N 1 p * heckeTPair N 1 (p ^ (k + 2)) =
      heckeTPair N 1 (p ^ (k + 3)) + (p : ℤ) • (heckeTPair N p p * heckeTPair N 1 (p ^ (k + 1))) := by
  have h := hR.one_prime_mul hp hpN (e := k + 2) (by omega)
  have hne : ¬ (k + 2 = 1) := by omega
  simp only [hne, ↓reduceIte] at h
  have e : heckeTPair N p (p ^ (k + 2)) = heckeTPair N p p * heckeTPair N 1 (p ^ (k + 1)) := by
    rw [← heckeTPair_scalar_mul, ← pow_succ']
  rw [h, e]

private lemma claim (hR : DoubleCosetRelations N) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (k : ℕ) :
    heckeTPair N 1 p * miyakeHeckeT N (p ^ (k + 1)) =
      miyakeHeckeT N (p ^ (k + 2)) + (p : ℤ) • (heckeTPair N p p * miyakeHeckeT N (p ^ k)) := by
  let _ := commRingR N
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases k with _ | _ | k
  · have m2 := M_add_two N hp 0
    have rl := rel_one N hR hp hpN
    simp only [zero_add] at m2 ⊢
    rw [M_one N hp, m2, M_zero N hp]
    simp only [zsmul_eq_mul] at rl ⊢
    push_cast at rl ⊢
    linear_combination rl
  · have m2 : miyakeHeckeT N (p ^ 2) = heckeTPair N 1 (p ^ 2) +
        heckeTPair N p p * miyakeHeckeT N (p ^ 0) := M_add_two N hp 0
    have m3 : miyakeHeckeT N (p ^ 3) = heckeTPair N 1 (p ^ 3) +
        heckeTPair N p p * miyakeHeckeT N (p ^ 1) := M_add_two N hp 1
    have r : heckeTPair N 1 p * heckeTPair N 1 (p ^ 2) = heckeTPair N 1 (p ^ 3) +
        (p : ℤ) • (heckeTPair N p p * heckeTPair N 1 (p ^ 1)) := rel_succ N hR hp hpN 0
    show heckeTPair N 1 p * miyakeHeckeT N (p ^ 2) =
      miyakeHeckeT N (p ^ 3) + (p : ℤ) • (heckeTPair N p p * miyakeHeckeT N (p ^ 1))
    rw [m2, m3, M_zero N hp, M_one N hp]
    rw [pow_one] at r
    simp only [zsmul_eq_mul] at r ⊢
    push_cast at r ⊢
    linear_combination r
  · have ih' : heckeTPair N 1 p * miyakeHeckeT N (p ^ (k + 1)) =
        miyakeHeckeT N (p ^ (k + 2)) + (p : ℤ) • (heckeTPair N p p * miyakeHeckeT N (p ^ k)) :=
      ih k (by omega)
    have a1 : miyakeHeckeT N (p ^ (k + 4)) = heckeTPair N 1 (p ^ (k + 4)) +
        heckeTPair N p p * miyakeHeckeT N (p ^ (k + 2)) := M_add_two N hp (k + 2)
    have a2 : miyakeHeckeT N (p ^ (k + 3)) = heckeTPair N 1 (p ^ (k + 3)) +
        heckeTPair N p p * miyakeHeckeT N (p ^ (k + 1)) := M_add_two N hp (k + 1)
    have a3 := M_add_two N hp k
    have r : heckeTPair N 1 p * heckeTPair N 1 (p ^ (k + 3)) =
        heckeTPair N 1 (p ^ (k + 4)) +
          (p : ℤ) • (heckeTPair N p p * heckeTPair N 1 (p ^ (k + 2))) :=
      rel_succ N hR hp hpN (k + 1)
    show heckeTPair N 1 p * miyakeHeckeT N (p ^ (k + 3)) =
      miyakeHeckeT N (p ^ (k + 4)) + (p : ℤ) • (heckeTPair N p p * miyakeHeckeT N (p ^ (k + 2)))
    rw [a2, a1]
    simp only [zsmul_eq_mul] at r ih' a3 ⊢
    push_cast at r ih' a3 ⊢
    linear_combination r + heckeTPair N p p * ih' - (p : HeckeRingGamma0 N) * heckeTPair N p p * a3


private lemma P_pow_of_dvd (hR : DoubleCosetRelations N) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (e : ℕ) : heckeTPair N 1 (p ^ e) = heckeTPair N 1 p ^ e := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ' (heckeTPair N 1 p), ← ih, hR.one_prime_mul_of_dvd hp hpN e]

private lemma M_of_dvd {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (e : ℕ) :
    miyakeHeckeT N (p ^ e) = heckeTPair N 1 (p ^ e) := by
  have hnc : ¬ Nat.Coprime p N := by rwa [hp.coprime_iff_not_dvd, not_not]
  have hS : heckeTPair N p p = 0 :=
    HeckeRing.GL2.diagElemGamma0_of_not_coprime N (a := ![p, p]) (by simpa using hnc)
  rw [miyakeHeckeT_prime_pow_sum N hp e, Finset.sum_range_succ']
  simp [hS]

private lemma M_eq_rec (hR : DoubleCosetRelations N) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    miyakeHeckeT N (p ^ e) = HeckeRing.GL2.heckeTGeneratorRecGamma0 N p e := by
  by_cases hpN : p ∣ N
  · have hnc : ¬ Nat.Coprime p N := by rwa [hp.coprime_iff_not_dvd, not_not]
    rw [HeckeRing.GL2.heckeTGeneratorRecGamma0_eq_generator_pow_of_not_coprime N hnc,
      M_of_dvd N hp hpN, P_pow_of_dvd N hR hp hpN]
    rfl
  · induction e using Nat.twoStepInduction with
    | zero => rw [M_zero N hp, HeckeRing.GL2.heckeTGeneratorRecGamma0_zero]
    | one =>
      rw [M_one N hp, HeckeRing.GL2.heckeTGeneratorRecGamma0_one,
        HeckeRing.GL2.heckeTGeneratorGamma0_def]
    | more e h0 h1 =>
      rw [HeckeRing.GL2.heckeTGeneratorRecGamma0_succ_succ, ← h0, ← h1, smul_mul_assoc,
        HeckeRing.GL2.heckeTGeneratorGamma0_def, HeckeRing.GL2.heckeTScalarGamma0_def]
      have := claim N hR hp hpN e
      rw [eq_sub_iff_add_eq]
      exact this.symm

private lemma gcd_aux {m n l : ℕ} (hmn : m.Coprime n) (hll : l * l ∣ m * n) :
    l.gcd m ∣ m / l.gcd m ∧ l.gcd n ∣ n / l.gcd n := by
  constructor
  · have h1 : l.gcd m * l.gcd m ∣ m * n :=
      (mul_dvd_mul (Nat.gcd_dvd_left l m) (Nat.gcd_dvd_left l m)).trans hll
    have c1 : (l.gcd m).Coprime n := Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right l m) hmn
    exact Nat.dvd_div_of_mul_dvd ((Nat.coprime_mul_iff_left.2 ⟨c1, c1⟩).dvd_of_dvd_mul_right h1)
  · have h1 : l.gcd n * l.gcd n ∣ m * n :=
      (mul_dvd_mul (Nat.gcd_dvd_left l n) (Nat.gcd_dvd_left l n)).trans hll
    have c1 : (l.gcd n).Coprime m :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right l n) hmn.symm
    exact Nat.dvd_div_of_mul_dvd ((Nat.coprime_mul_iff_left.2 ⟨c1, c1⟩).dvd_of_dvd_mul_left h1)

private lemma M_mul_of_coprime (hR : DoubleCosetRelations N) {m n : ℕ} (hmn : m.Coprime n) :
    miyakeHeckeT N m * miyakeHeckeT N n = miyakeHeckeT N (m * n) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [miyakeHeckeT]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [miyakeHeckeT]
  unfold miyakeHeckeT
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun x => x.1 * x.2) (fun l => (l.gcd m, l.gcd n)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, Nat.mem_divisors] at h ⊢
    obtain ⟨⟨⟨ha, -⟩, ha2⟩, ⟨⟨hb, -⟩, hb2⟩⟩ := h
    refine ⟨⟨mul_dvd_mul ha hb, (Nat.mul_pos hm hn).ne'⟩, ?_⟩
    rw [← Nat.div_mul_div_comm ha hb]
    exact mul_dvd_mul ha2 hb2
  · intro l h
    simp only [Finset.mem_product, Finset.mem_filter, Nat.mem_divisors] at h ⊢
    obtain ⟨⟨hl, -⟩, hl2⟩ := h
    obtain ⟨g1, g2⟩ := gcd_aux hmn (Nat.mul_dvd_of_dvd_div hl hl2)
    exact ⟨⟨⟨Nat.gcd_dvd_right _ _, hm.ne'⟩, g1⟩, ⟨⟨Nat.gcd_dvd_right _ _, hn.ne'⟩, g2⟩⟩
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, Nat.mem_divisors] at h
    obtain ⟨⟨⟨ha, -⟩, -⟩, ⟨⟨hb, -⟩, -⟩⟩ := h
    have cb : b.Coprime m := Nat.Coprime.coprime_dvd_left hb hmn.symm
    have ca : a.Coprime n := Nat.Coprime.coprime_dvd_left ha hmn
    simp only [Prod.mk.injEq]
    constructor
    · rw [Nat.Coprime.gcd_mul_right_cancel a cb]; exact Nat.gcd_eq_left ha
    · rw [Nat.Coprime.gcd_mul_left_cancel b ca]; exact Nat.gcd_eq_left hb
  · intro l h
    simp only [Finset.mem_filter, Nat.mem_divisors] at h
    obtain ⟨⟨hl, -⟩, -⟩ := h
    show l.gcd m * l.gcd n = l
    rw [← Nat.Coprime.gcd_mul l hmn]
    exact Nat.gcd_eq_left hl
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_product, Finset.mem_filter, Nat.mem_divisors] at h
    obtain ⟨⟨⟨ha, -⟩, ha2⟩, ⟨⟨hb, -⟩, hb2⟩⟩ := h
    have := hR.mul_of_coprime ha2 hb2
      (by rw [Nat.mul_div_cancel' ha, Nat.mul_div_cancel' hb]; exact hmn)
    simp only
    rw [this, Nat.div_mul_div_comm ha hb]

/-- **Miyake, Lemma 4.5.7 (2)** for Miyake's `T(n)`: for a prime `p ∤ N` and `e ≥ 1`,
`T(p) T(p^e) = T(p^{e+1}) + p T(p, p) T(p^{e-1})`. -/
@[kb "miyake1989" "Lemma 4.5.7 (2), p. 140 (p prime to N)"]
theorem miyakeHeckeT_prime_mul (hR : DoubleCosetRelations N) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) {e : ℕ} (he : 1 ≤ e) :
    miyakeHeckeT N p * miyakeHeckeT N (p ^ e) =
      miyakeHeckeT N (p ^ (e + 1)) +
        (p : ℤ) • (heckeTPair N p p * miyakeHeckeT N (p ^ (e - 1))) := by
  have h1 : miyakeHeckeT N p = heckeTPair N 1 p := by
    have := M_one N hp
    rwa [pow_one] at this
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  rw [h1, Nat.add_sub_cancel]
  exact claim N hR hp hpN k

/-- **Miyake, Lemma 4.5.7 (2)** for Miyake's `T(n)`: for a prime `p ∣ N`,
`T(p) T(p^e) = T(p^{e+1})`. -/
@[kb "miyake1989" "Lemma 4.5.7 (2), p. 140 (p dividing N)"]
theorem miyakeHeckeT_prime_mul_of_dvd (hR : DoubleCosetRelations N) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (e : ℕ) :
    miyakeHeckeT N p * miyakeHeckeT N (p ^ e) = miyakeHeckeT N (p ^ (e + 1)) := by
  have h1 : miyakeHeckeT N p = heckeTPair N 1 p := by
    have := M_one N hp
    rwa [pow_one] at this
  rw [h1, M_of_dvd N hp hpN, M_of_dvd N hp hpN]
  exact hR.one_prime_mul_of_dvd hp hpN e

/-- **Miyake, Lemma 4.5.8 (2)** for Miyake's `T(n)`: `T(m) T(n) = T(mn)` for coprime `m`, `n`. -/
@[kb "miyake1989" "Lemma 4.5.8 (2), p. 141 (Miyake's T(n))"]
theorem miyakeHeckeT_mul_of_coprime (hR : DoubleCosetRelations N) {m n : ℕ} (hmn : m.Coprime n) :
    miyakeHeckeT N m * miyakeHeckeT N n = miyakeHeckeT N (m * n) :=
  M_mul_of_coprime N hR hmn

/-- **Miyake's `T(n)` is Tau Ceti's composite Hecke element**, for `n ≥ 1`, given the
double-coset relations of Lemmas 4.5.7 (1) and 4.5.8 (1). -/
theorem miyakeHeckeT_eq_heckeTCompositeGamma0 (hR : DoubleCosetRelations N) {n : ℕ} (hn : n ≠ 0) :
    miyakeHeckeT N n = HeckeRing.GL2.heckeTCompositeGamma0 N n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => exact absurd rfl hn
  | one =>
    have := M_eq_rec N hR Nat.prime_two 0
    simpa using this
  | prime_pow p e hp he =>
    rw [HeckeRing.GL2.heckeTCompositeGamma0_prime_pow N hp, M_eq_rec N hR hp]
  | coprime a b ha hb hab iha ihb =>
    rw [← M_mul_of_coprime N hR hab, HeckeRing.GL2.heckeTCompositeGamma0_mul_of_coprime N hab,
      iha (by omega), ihb (by omega)]

end ModularFormsKB.Miyake.Wave4
