import ModularFormsKB.Milne.Ch11.ZetaFiniteField

/-!
# Bombieri's argument, II: valuation lemmas

H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Section 5.2 [unverified]; Bombieri 1973.

- `eq_zero_of_sum_pow_mul_eq_zero`: if $f_1, \dots, f_s$ are nonzero with pairwise distinct orders at a place $P_0$,
  all in $(-q_0, 0]$, then $\sum_i g_i^{q_0} f_i = 0$ forces all $g_i = 0$: the orders $q_0 v(g_i) + v(f_i)$ of the
  nonzero summands are pairwise distinct (distinct modulo $q_0$), so the least one is attained once.
- `valuation_pow_card_sub_lt_one`: at a place $P$ of degree one, $x^q - x$ lies in the maximal ideal for every $x$
  regular at $P$ ($q = \#k$), because the residue of $x$ lies in $k$.
- `mul_card_le_of_ord`: a nonzero $z$ with $v_P(z) \ge c$ at every $P \in T$, no poles outside $P_0 \notin T$, and
  $v_{P_0}(z) \ge -M$, $P_0$ rational, satisfies $c\,\#T \le M$ (the principal divisor of $z$ has degree $0$).
-/

open TauCeti TauCeti.AlgebraicGeometry Finset

namespace ModularFormsKB.Milne

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-- **Bombieri's independence lemma.** -/
theorem eq_zero_of_sum_pow_mul_eq_zero (P₀ : Place k F) (q₀ : ℕ) {s : ℕ} (f : Fin s → F)
    (hf : ∀ i, f i ≠ 0) (hinj : Function.Injective (fun i => P₀.ord (f i)))
    (hrange : ∀ i, -(q₀ : ℤ) < P₀.ord (f i) ∧ P₀.ord (f i) ≤ 0) (g : Fin s → F)
    (h : ∑ i, g i ^ q₀ * f i = 0) : ∀ i, g i = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨i₀, hi₀⟩ := hcon
  have hqpos : (0 : ℤ) < q₀ := by have := hrange i₀; omega
  have hq₀ne : q₀ ≠ 0 := by omega
  set S : Finset (Fin s) := Finset.univ.filter (fun i => g i ≠ 0) with hS
  have hSne : S.Nonempty := ⟨i₀, by simp [hS, hi₀]⟩
  let w : Fin s → ℤ := fun i => P₀.ord (g i ^ q₀ * f i)
  have hw : ∀ i ∈ S, w i = q₀ * P₀.ord (g i) + P₀.ord (f i) := by
    intro i hi
    have hgi : g i ≠ 0 := by simpa [hS] using hi
    simp only [w]
    rw [P₀.ord_mul (pow_ne_zero _ hgi) (hf i), P₀.ord_pow]
  obtain ⟨j, hjS, hjmin⟩ := Finset.exists_min_image S w hSne
  have hne : ∀ i ∈ S, ∀ l ∈ S, i ≠ l → w i ≠ w l := by
    intro i hi l hl hil heq
    rw [hw i hi, hw l hl] at heq
    apply hil
    apply hinj
    have h1 := hrange i
    have h2 := hrange l
    simp only
    have hdiv : (q₀ : ℤ) ∣ P₀.ord (f i) - P₀.ord (f l) :=
      ⟨P₀.ord (g l) - P₀.ord (g i), by linarith⟩
    obtain ⟨m, hm⟩ := hdiv
    have : m = 0 := by
      by_contra hm0
      rcases lt_or_gt_of_ne hm0 with h | h
      · nlinarith
      · nlinarith
    rw [this] at hm
    linarith
  have hsum : ∑ i, g i ^ q₀ * f i = ∑ i ∈ S, g i ^ q₀ * f i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have : g i = 0 := by simpa [hS] using hi
    simp [this, hq₀ne]
  have hjg : g j ≠ 0 := by simpa [hS] using hjS
  rw [hsum] at h
  refine Place.sum_ne_zero_of_forall_ord_lt (P := P₀) (f := fun i => g i ^ q₀ * f i) hjS
    (mul_ne_zero (pow_ne_zero _ hjg) (hf j)) ?_ h
  intro i hi hij
  exact lt_of_le_of_ne (hjmin i hi) (hne j hjS i hi (Ne.symm hij))

/-- **At a rational place, $x^q - x$ vanishes for every regular $x$.** -/
theorem valuation_pow_card_sub_lt_one [Finite k] (hF : IsFunctionField k F) (P : Place k F)
    (hP : P.degree = 1) (x : F) (hx : P.valuation x ≤ 1) :
    P.valuation (x ^ Nat.card k - x) < 1 := by
  obtain ⟨c, hc⟩ :=
    (Place.degree_eq_one_iff_forall_exists_valuation_sub_lt_one (P := P)).mp hP x hx
  have hmem : (⟨x, hx⟩ : P.integers) - algebraMap k P.integers c ∈
      IsLocalRing.maximalIdeal P.integers := by
    rw [Place.mem_maximalIdeal_iff_valuation_lt_one]
    have : (((⟨x, hx⟩ : P.integers) - algebraMap k P.integers c : P.integers) : F)
        = x - algebraMap k F c := by
      rw [← ValuationSubring.algebraMap_apply P.integers (_ - algebraMap k P.integers c),
        _root_.map_sub, ← IsScalarTower.algebraMap_apply k P.integers F,
        ValuationSubring.algebraMap_apply]
    rw [this]; exact hc
  have hcq : algebraMap k P.integers c ^ Nat.card k = algebraMap k P.integers c := by
    have := Fintype.ofFinite k
    rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hdvd := sub_dvd_pow_sub_pow (⟨x, hx⟩ : P.integers) (algebraMap k P.integers c) (Nat.card k)
  have h1 : (⟨x, hx⟩ : P.integers) ^ Nat.card k - algebraMap k P.integers c ^ Nat.card k
      ∈ IsLocalRing.maximalIdeal P.integers := by
    obtain ⟨d, hd⟩ := hdvd
    rw [hd]; exact Ideal.mul_mem_right _ _ hmem
  rw [hcq] at h1
  have h2 := Ideal.sub_mem _ h1 hmem
  have h3 : ((⟨x, hx⟩ : P.integers) ^ Nat.card k - algebraMap k P.integers c) -
      ((⟨x, hx⟩ : P.integers) - algebraMap k P.integers c)
      = (⟨x, hx⟩ : P.integers) ^ Nat.card k - ⟨x, hx⟩ := by ring
  rw [h3] at h2
  have := (Place.mem_maximalIdeal_iff_valuation_lt_one (P := P)).mp h2
  simpa using this

/-- **Counting zeros against poles.** -/
theorem mul_card_le_of_ord (hF : IsFunctionField k F) (z : F) (hz : z ≠ 0) (P₀ : Place k F)
    (hP₀ : P₀.degree = 1) (T : Finset (Place k F)) (hT : P₀ ∉ T) (c M : ℕ)
    (h1 : ∀ P ∈ T, (c : ℤ) ≤ P.ord z) (h2 : ∀ P, P ≠ P₀ → 0 ≤ P.ord z) (h3 : -(M : ℤ) ≤ P₀.ord z) :
    c * T.card ≤ M := by
  classical
  have hdeg := Divisor.degree_principal hF (Units.mk0 z hz)
  rw [Divisor.degree_apply] at hdeg
  set D := Divisor.principal hF (Units.mk0 z hz) with hD
  have hcoeff : ∀ P, D P = P.ord z := fun P => by
    exact Divisor.coeff_principal hF (Units.mk0 z hz) P
  let U : Finset (Place k F) := insert P₀ T ∪ D.support
  have hsub : D.support ⊆ U := Finset.subset_union_right
  rw [Finsupp.sum_of_support_subset D hsub _ (by intro i _; simp)] at hdeg
  have hsplit := Finset.sum_sdiff (f := fun P => D P * (P.degree : ℤ))
    (Finset.subset_union_left : insert P₀ T ⊆ U)
  have hrest : 0 ≤ ∑ P ∈ U \ insert P₀ T, D P * (P.degree : ℤ) := by
    apply Finset.sum_nonneg
    intro P hP
    have hP' : P ≠ P₀ := fun h => (Finset.mem_sdiff.mp hP).2 (by simp [h])
    rw [hcoeff]
    exact mul_nonneg (h2 P hP') (by positivity)
  rw [Finset.sum_insert hT] at hsplit
  have hT1 : ∑ P ∈ T, (c : ℤ) * 1 ≤ ∑ P ∈ T, D P * (P.degree : ℤ) := by
    apply Finset.sum_le_sum
    intro P hP
    rw [hcoeff]
    have := Place.one_le_degree_of_isFunctionField (P := P) hF
    have hc0 : (0 : ℤ) ≤ c := by positivity
    calc (c : ℤ) * 1 ≤ P.ord z * 1 := by nlinarith [h1 P hP]
      _ ≤ P.ord z * P.degree := by
        apply mul_le_mul_of_nonneg_left (by exact_mod_cast this) (by linarith [h1 P hP])
  have hP₀t : D P₀ * (P₀.degree : ℤ) ≥ -(M : ℤ) := by
    rw [hcoeff, hP₀]; simpa using h3
  simp at hT1
  have : (c : ℤ) * T.card ≤ M := by linarith
  exact_mod_cast this

end ModularFormsKB.Milne
