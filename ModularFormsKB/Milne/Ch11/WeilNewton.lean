import ModularFormsKB.Milne.Ch11.WeilZeta

/-!
# The Newton identity for the zeta function of a function field

For a function field $F$ over a finite field $k$, with $A_n$ the number of effective divisors of degree $n$
(`effectiveDivisorCount`) and $N_m = \sum_{d \mid m} d\,B_d$ (`curvePointCount`),
$$ n A_n = \sum_{m=1}^{n} N_m A_{n-m}, $$
the coefficientwise form of $tZ'(t) = Z(t)\sum_{m \ge 1} N_m t^m$ (the logarithmic derivative of the Euler product
$Z(t) = \prod_P (1 - t^{\deg P})^{-1}$; Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Section 5.1).

Proof: $n A_n = \sum_{\deg D = n} \deg D = \sum_D \sum_P v_P(D) \deg P$; writing $v_P(D) = \#\{j \ge 1 : j \le v_P(D)\}$
and using the bijection $D \mapsto D - jP$ between effective divisors of degree $n$ with $v_P(D) \ge j$ and
effective divisors of degree $n - j\deg P$, this is $\sum_{P}\sum_{j \ge 1,\ j\deg P \le n} \deg P\, A_{n - j\deg P}$;
grouping by $m = j \deg P$ gives $\sum_m A_{n-m}\sum_{\deg P \mid m}\deg P = \sum_m A_{n-m} N_m$.
-/

open Finset

namespace ModularFormsKB.Milne

universe u v


section Aux

open TauCeti TauCeti.AlgebraicGeometry

variable {k : Type u} {F : Type v} [Field k] [Finite k] [Field F] [Algebra k F]

open Classical in
/-- The finite set of effective divisors of degree `m`. -/
noncomputable def effSet (hF : TauCeti.IsFunctionField k F) (m : ℕ) : Finset (TauCeti.Divisor k F) :=
  (TauCeti.Divisor.finite_setOf_nonneg_degree_le hF m).toFinset.filter
    (fun D => TauCeti.Divisor.degree D = m)

theorem mem_effSet (hF : TauCeti.IsFunctionField k F) (m : ℕ) (D : TauCeti.Divisor k F) :
    D ∈ effSet hF m ↔ 0 ≤ D ∧ TauCeti.Divisor.degree D = m := by
  classical
  simp only [effSet, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.le⟩, h2⟩

theorem effectiveDivisorCount_eq_card (hF : TauCeti.IsFunctionField k F) (m : ℕ) :
    effectiveDivisorCount k F m = (effSet hF m).card := by
  unfold effectiveDivisorCount
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun D => (mem_effSet hF m D).symm)

theorem shift_card (hF : TauCeti.IsFunctionField k F) (n j : ℕ) (P : TauCeti.Place k F)
    (h : j * P.degree ≤ n) :
    ((effSet hF n).filter (fun D => (j : ℤ) ≤ D.coeff P)).card = (effSet hF (n - j * P.degree)).card := by
  classical
  refine Finset.card_nbij' (fun D => D - j • WeilDivisor.ofPoint P) (fun D => D + j • WeilDivisor.ofPoint P)
    ?_ ?_ ?_ ?_
  · intro D hD
    simp only [Finset.mem_coe, Finset.mem_filter, mem_effSet] at hD ⊢
    obtain ⟨⟨hE, hdeg⟩, hj⟩ := hD
    refine ⟨?_, ?_⟩
    · rw [WeilDivisor.le_iff]
      intro x
      rw [WeilDivisor.coeff_zero, WeilDivisor.coeff_sub, WeilDivisor.coeff_nsmul]
      by_cases hx : x = P
      · subst hx; rw [WeilDivisor.coeff_ofPoint_self]; linarith
      · rw [WeilDivisor.coeff_ofPoint_of_ne hx]; simpa using WeilDivisor.coeff_nonneg hE x
    · rw [TauCeti.Divisor.degree_sub, hdeg]
      simp only [map_nsmul, TauCeti.Divisor.degree_ofPoint, nsmul_eq_mul]
      push_cast [Nat.cast_sub h]; ring
  · intro D hD
    simp only [Finset.mem_coe, Finset.mem_filter, mem_effSet] at hD ⊢
    obtain ⟨hE, hdeg⟩ := hD
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [WeilDivisor.le_iff]
      intro x
      rw [WeilDivisor.coeff_zero, WeilDivisor.coeff_add, WeilDivisor.coeff_nsmul]
      by_cases hx : x = P
      · subst hx; rw [WeilDivisor.coeff_ofPoint_self]; have := WeilDivisor.coeff_nonneg hE x; positivity
      · rw [WeilDivisor.coeff_ofPoint_of_ne hx]; simpa using WeilDivisor.coeff_nonneg hE x
    · rw [TauCeti.Divisor.degree_add, hdeg]
      simp only [map_nsmul, TauCeti.Divisor.degree_ofPoint, nsmul_eq_mul]
      push_cast [Nat.cast_sub h]; ring
    · rw [WeilDivisor.coeff_add, WeilDivisor.coeff_nsmul, WeilDivisor.coeff_ofPoint_self]
      have := WeilDivisor.coeff_nonneg hE P
      simp only [mul_one]; linarith
  · intro D _; simp
  · intro D _; simp

theorem shift_zero (hF : TauCeti.IsFunctionField k F) (n j : ℕ) (P : TauCeti.Place k F)
    (h : n < j * P.degree) :
    ((effSet hF n).filter (fun D => (j : ℤ) ≤ D.coeff P)).card = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro D hD hj
  rw [mem_effSet] at hD
  obtain ⟨hE, hdeg⟩ := hD
  have hE' := fun x => WeilDivisor.coeff_nonneg hE x
  have hle : 0 ≤ TauCeti.Divisor.degree (D - j • WeilDivisor.ofPoint P) := by
    apply TauCeti.Divisor.degree_nonneg
    rw [WeilDivisor.le_iff]
    intro x
    rw [WeilDivisor.coeff_zero, WeilDivisor.coeff_sub, WeilDivisor.coeff_nsmul]
    by_cases hx : x = P
    · subst hx; rw [WeilDivisor.coeff_ofPoint_self]; linarith
    · rw [WeilDivisor.coeff_ofPoint_of_ne hx]; simpa using hE' x
  rw [TauCeti.Divisor.degree_sub, hdeg] at hle
  simp only [map_nsmul, TauCeti.Divisor.degree_ofPoint, nsmul_eq_mul] at hle
  have : ((n : ℤ)) < j * P.degree := by exact_mod_cast h
  linarith


theorem sum_Icc_ite (x : ℤ) (n : ℕ) (h0 : 0 ≤ x) (hn : x ≤ n) :
    ∑ j ∈ Finset.Icc 1 n, (if (j : ℤ) ≤ x then (1 : ℤ) else 0) = x := by
  obtain ⟨c, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  rw [Finset.sum_boole]
  have : (Finset.Icc 1 n).filter (fun j : ℕ => (j : ℤ) ≤ c) = Finset.Icc 1 c := by
    ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [this]; simp

theorem regroup_inner (n d : ℕ) (hd : 1 ≤ d) (g : ℕ → ℕ) :
    ∑ j ∈ Finset.Icc 1 n, (if j * d ≤ n then d * g (n - j * d) else 0) =
      ∑ m ∈ Finset.Icc 1 n, (if d ∣ m then d * g (n - m) else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun j => j * d) (fun m => m / d) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hj ⊢
    refine ⟨⟨?_, by omega⟩, Dvd.intro_left _ rfl⟩
    nlinarith
  · intro m hm
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    obtain ⟨⟨h1, h2⟩, c, rfl⟩ := hm
    have hc : d * c / d = c := Nat.mul_div_cancel_left _ hd
    rw [hc]
    have : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; simp at h1
      · exact h
    refine ⟨⟨this, ?_⟩, by rw [mul_comm]; exact h2⟩
    nlinarith
  · intro j _; exact Nat.mul_div_cancel _ (by omega)
  · intro m hm
    simp only [Finset.mem_coe, Finset.mem_filter] at hm
    exact Nat.div_mul_cancel hm.2
  · intro j _; rfl

theorem placeCount_eq (hF : TauCeti.IsFunctionField k F) (n d : ℕ) (hd : d ≤ n) :
    Nat.card {P : TauCeti.Place k F // P.degree = d} =
      (((TauCeti.Place.finite_setOf_degree_le hF n).toFinset).filter (fun P => P.degree = d)).card := by
  classical
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun P => ?_)
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩

theorem curvePointCount_eq (hF : TauCeti.IsFunctionField k F) (n m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    ∑ P ∈ (TauCeti.Place.finite_setOf_degree_le hF n).toFinset,
        (if P.degree ∣ m then P.degree else 0) = curvePointCount k F m := by
  classical
  set S := (TauCeti.Place.finite_setOf_degree_le hF n).toFinset
  rw [← Finset.sum_filter]
  unfold curvePointCount
  rw [← Finset.sum_fiberwise_of_maps_to (s := S.filter (fun P => P.degree ∣ m)) (t := m.divisors)
    (g := TauCeti.Place.degree)]
  · refine Finset.sum_congr rfl fun d hd => ?_
    have hdm := Nat.mem_divisors.mp hd
    have hdn : d ≤ n := (Nat.le_of_dvd (by omega) hdm.1).trans hmn
    rw [placeCount_eq hF n d hdn]
    have : (S.filter (fun P => P.degree ∣ m)).filter (fun P => P.degree = d) =
        S.filter (fun P => P.degree = d) := by
      ext P; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨a, _⟩, b⟩; exact ⟨a, b⟩
      · rintro ⟨a, b⟩; exact ⟨⟨a, b ▸ hdm.1⟩, b⟩
    rw [this, Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.mp hP).2]), Finset.sum_const,
      smul_eq_mul, mul_comm]
  · intro P hP
    simp only [Finset.mem_filter] at hP
    exact Nat.mem_divisors.mpr ⟨hP.2, by omega⟩

end Aux

/-- **The Newton identity** $n A_n = \sum_{m=1}^{n} N_m A_{n-m}$. -/
theorem effectiveDivisorCount_newton (k : Type u) (F : Type v) [Field k] [Finite k] [Field F] [Algebra k F]
    (hF : TauCeti.IsFunctionField k F) (n : ℕ) :
    n * effectiveDivisorCount k F n =
      ∑ j ∈ range n, curvePointCount k F (j + 1) * effectiveDivisorCount k F (n - 1 - j) := by
  classical
  set S := (TauCeti.Place.finite_setOf_degree_le hF n).toFinset with hS
  -- degree of an effective divisor of degree n as a double sum
  have hdeg : ∀ D ∈ effSet hF n, TauCeti.Divisor.degree D =
      ∑ P ∈ S, ∑ j ∈ Finset.Icc 1 n, (if (j : ℤ) ≤ D.coeff P then (P.degree : ℤ) else 0) := by
    intro D hD
    rw [mem_effSet] at hD
    obtain ⟨hE, hdD⟩ := hD
    have hE0 : 0 ≤ D := hE
    rw [TauCeti.Divisor.degree_eq_sum_support]
    have hsub : D.support ⊆ S := by
      intro P hP
      have := TauCeti.Divisor.degree_le_degree_of_coeff_ne_zero hE0 (TauCeti.AlgebraicGeometry.WeilDivisor.mem_support_iff.mp hP)
      rw [hS, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      rw [hdD] at this; exact_mod_cast this
    rw [Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun P _ => ?_
      have hc := sum_Icc_ite (D.coeff P) n (TauCeti.AlgebraicGeometry.WeilDivisor.coeff_le_coeff hE0 P)
        ((TauCeti.Divisor.coeff_le_degree hF hE0 P).trans hdD.le)
      have e : (D.coeff P) * (P.degree : ℤ) = (∑ j ∈ Finset.Icc 1 n,
          (if (j : ℤ) ≤ D.coeff P then (1 : ℤ) else 0)) * P.degree := by rw [hc]
      refine e.trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    · intro P _ hP
      have : D P = 0 := by simpa using hP
      simp [this]
  have h1 : ((n * effectiveDivisorCount k F n : ℕ) : ℤ) =
      ∑ D ∈ effSet hF n, TauCeti.Divisor.degree D := by
    rw [effectiveDivisorCount_eq_card hF]
    rw [Finset.sum_congr rfl (fun D hD => ((mem_effSet hF n D).mp hD).2)]
    simp; ring
  have h2 : ∑ D ∈ effSet hF n, TauCeti.Divisor.degree D =
      ((∑ P ∈ S, ∑ j ∈ Finset.Icc 1 n, (if j * P.degree ≤ n then
        P.degree * effectiveDivisorCount k F (n - j * P.degree) else 0) : ℕ) : ℤ) := by
    rw [Finset.sum_congr rfl hdeg, Finset.sum_comm]
    push_cast
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    by_cases hj : j * P.degree ≤ n
    · rw [if_pos hj, shift_card hF n j P hj, effectiveDivisorCount_eq_card hF]; push_cast; ring
    · rw [if_neg hj, shift_zero hF n j P (by omega)]; simp
  have h3 : n * effectiveDivisorCount k F n =
      ∑ P ∈ S, ∑ j ∈ Finset.Icc 1 n, (if j * P.degree ≤ n then
        P.degree * effectiveDivisorCount k F (n - j * P.degree) else 0) := by
    have := h1.trans h2
    exact_mod_cast this
  rw [h3]
  have h4 : ∀ P ∈ S, ∑ j ∈ Finset.Icc 1 n, (if j * P.degree ≤ n then
        P.degree * effectiveDivisorCount k F (n - j * P.degree) else 0) =
      ∑ m ∈ Finset.Icc 1 n, (if P.degree ∣ m then
        P.degree * effectiveDivisorCount k F (n - m) else 0) := by
    intro P _
    exact regroup_inner n P.degree (P.one_le_degree_of_isFunctionField hF) _
  rw [Finset.sum_congr rfl h4, Finset.sum_comm]
  have h5 : ∀ m ∈ Finset.Icc 1 n, ∑ P ∈ S, (if P.degree ∣ m then
        P.degree * effectiveDivisorCount k F (n - m) else 0) =
      curvePointCount k F m * effectiveDivisorCount k F (n - m) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [← curvePointCount_eq hF n m hm.1 hm.2, Finset.sum_mul]
    refine Finset.sum_congr rfl fun P _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h5]
  have hI : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by ext; simp
  rw [hI, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by simp) fun j _ => ?_
  rw [add_comm 1 j]
  congr 2
  omega

/-- The named statement `ZetaNewtonIdentity` holds. -/
theorem zetaNewtonIdentity : ZetaNewtonIdentity.{u, v} :=
  ⟨fun k F _ _ _ _ hF n => effectiveDivisorCount_newton k F hF n⟩

end ModularFormsKB.Milne
