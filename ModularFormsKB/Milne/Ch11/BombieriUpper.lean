import ModularFormsKB.Milne.Ch11.WeilBombieriSplit
import ModularFormsKB.Milne.Ch11.BombieriPoleOrders
import ModularFormsKB.Milne.Ch11.BombieriValuation

/-!
# Bombieri's upper bound $N \le q + 1 + (2g+1)\sqrt q$

H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Section 5.2 [unverified]; E. Bombieri, *Counting
points on curves over finite fields (d'après S. A. Stepanov)*, Séminaire Bourbaki 430 (1973).

Let $q = q_0^2$, $q_0 > (g+1)^2$, $P_0$ a rational place, $T$ the other rational places, $m = q_0 - 1$, $n = q_0 + 2g$.
Take $f_1, \dots, f_s \in \mathcal L(mP_0)$ with pairwise distinct orders at $P_0$, $s \ge m + 1 - g$
(`exists_injective_ord_mem_riemannRochSpace`). The $k$-linear map
$(g_i) \mapsto \sum_i f_i^{q_0} g_i$, $\mathcal L(nP_0)^s \to \mathcal L((q_0m + n)P_0)$, has a nonzero kernel element
by Riemann–Roch since $(q_0 - g)(q_0 + g + 1) > q + g + 1$. Put $w = \sum_i f_i g_i^{q_0} \ne 0$
(`eq_zero_of_sum_pow_mul_eq_zero`, since the $-v_{P_0}(f_i) \in [0, q_0)$ are distinct) and
$z = w^{q_0} = \sum_i f_i^{q_0} g_i^{q}$. At $P \in T$, $z = \sum_i f_i^{q_0}(g_i^q - g_i)$ vanishes
(`valuation_pow_card_sub_lt_one`), hence $w$ vanishes and $v_P(z) \ge q_0$; $z$ has poles only at $P_0$, of order at
most $q_0 m + q n$. So $q_0\,\#T \le q_0 m + qn$ (`mul_card_le_of_ord`), i.e. $N - 1 \le q_0 - 1 + q_0(q_0 + 2g)$, which is
$N \le q + (2g+1)q_0$.
-/

open Finset TauCeti TauCeti.AlgebraicGeometry

namespace ModularFormsKB.Milne

universe u v

/-- A square root of a power of a prime is a power of that prime. -/
lemma eq_prime_pow_of_mul_self_eq {p e a : ℕ} (hp : p.Prime) (h : a * a = p ^ e) : ∃ i, a = p ^ i := by
  have : a ∣ p ^ e := ⟨a, h.symm⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp this
  exact ⟨i, hi⟩

set_option maxHeartbeats 1000000 in
/-- **Bombieri's upper bound.** -/
theorem bombieriUpperBound : BombieriUpperBound.{u, v} := by
  refine ⟨fun k F _ _ _ _ hF hex hsq hbig => ?_⟩
  classical
  set q : ℕ := Nat.card k with hq
  set g : ℕ := genus k F with hg
  obtain ⟨q₀, hq₀⟩ := hsq
  by_cases hN : Nat.card {P : Place k F // P.degree = 1} = 0
  · rw [hN]; push_cast; positivity
  obtain ⟨⟨P₀, hP₀⟩⟩ := (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hN)).1
  -- the characteristic and `q₀ = p ^ i`
  letI := Fintype.ofFinite k
  obtain ⟨p, hchar, e, hp, hpe⟩ := FiniteField.card' k
  have hqpe : q = p ^ (e : ℕ) := by rw [hq, Nat.card_eq_fintype_card, hpe]
  obtain ⟨i, hi⟩ := eq_prime_pow_of_mul_self_eq hp (hq₀ ▸ hqpe)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP F p := charP_of_injective_algebraMap (algebraMap k F).injective p
  have hq₀pos : 0 < q₀ := by rw [hi]; exact pow_pos hp.pos i
  have hgq : (g + 1) ^ 2 < q₀ := by
    have h4 : ((g + 1) ^ 2) ^ 2 < q₀ ^ 2 := by
      rw [← pow_mul, sq q₀, ← hq₀]; exact hbig
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp h4
  set m : ℕ := q₀ - 1 with hm
  set n : ℕ := q₀ + 2 * g with hn
  have hm' : (m : ℤ) = q₀ - 1 := by
    rw [hm, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hq₀pos.ne')]; simp
  obtain ⟨s, f, hs, hfmem, hf0, hinj, hfle⟩ := exists_injective_ord_mem_riemannRochSpace hF P₀ hP₀ m
  have hrange : ∀ j, -(q₀ : ℤ) < P₀.ord (f j) ∧ P₀.ord (f j) ≤ 0 := by
    intro j
    have := ((mem_riemannRochSpace_zsmul_ofPoint_iff (hf0 j)).mp (hfmem j)).1
    exact ⟨by omega, hfle j⟩
  set Dn : Divisor k F := (n : ℤ) • WeilDivisor.ofPoint P₀ with hDn
  set Dt : Divisor k F := ((q₀ * m + n : ℕ) : ℤ) • WeilDivisor.ofPoint P₀ with hDt
  have hmemt : ∀ j (x : F), x ∈ riemannRochSpace Dn → f j ^ q₀ * x ∈ riemannRochSpace Dt := by
    intro j x hx
    have := mul_mem_riemannRochSpace_add (pow_mem_riemannRochSpace_zsmul (hfmem j) q₀) hx
    convert this using 2
    rw [hDt, hDn, smul_smul, ← add_smul]; push_cast; ring_nf
  let Φ : (Fin s → riemannRochSpace Dn) →ₗ[k] riemannRochSpace Dt :=
    { toFun := fun G => ⟨∑ j, f j ^ q₀ * (G j : F),
        Submodule.sum_mem _ fun j _ => hmemt j _ (G j).2⟩
      map_add' := by
        intro G H; ext; simp [mul_add, sum_add_distrib]
      map_smul' := by
        intro c G; ext; simp [Finset.smul_sum, mul_smul_comm] }
  haveI := finiteDimensional_riemannRochSpace hF Dn
  haveI := finiteDimensional_riemannRochSpace hF Dt
  -- dimensions
  have hdegDn : Divisor.degree Dn = n := by
    rw [hDn, Divisor.degree_zsmul, Divisor.degree_ofPoint, hP₀]; simp
  have hdegDt : Divisor.degree Dt = (q₀ * m + n : ℕ) := by
    rw [hDt, Divisor.degree_zsmul, Divisor.degree_ofPoint, hP₀]; simp
  have hdimDn : (n : ℤ) + 1 - g ≤ Divisor.dim Dn := by
    have := Divisor.degree_add_one_sub_genus_le_dim hF Dn
    rw [hdegDn] at this; exact this
  obtain ⟨W, hW⟩ := exists_isRiemannRochDivisor hF hex
  have hdimDt : (Divisor.dim Dt : ℤ) ≤ (q₀ * m + n : ℕ) + 1 - g := by
    have hRR := hW Dt
    have hWdeg := hW.degree_eq hF hex
    have h0 : Divisor.dim (W - Dt) = 0 := by
      apply Divisor.dim_eq_zero_of_degree_neg hF
      rw [Divisor.degree_sub, hWdeg, hdegDt]
      push_cast
      rw [hn]; push_cast; nlinarith
    rw [h0, hdegDt] at hRR
    push_cast at hRR ⊢
    linarith
  have hlt : Module.finrank k (riemannRochSpace Dt) <
      Module.finrank k (Fin s → riemannRochSpace Dn) := by
    rw [Module.finrank_pi_fintype, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    rw [← Divisor.dim_def, ← Divisor.dim_def]
    have hgq' : ((g : ℤ) + 1) ^ 2 < q₀ := by exact_mod_cast hgq
    have hs' : (q₀ : ℤ) - g ≤ s := by rw [hm'] at hs; linarith
    have hdn' : (q₀ : ℤ) + g + 1 ≤ Divisor.dim Dn := by
      rw [hn] at hdimDn; push_cast at hdimDn; linarith
    have hpos : (0 : ℤ) ≤ (q₀ : ℤ) - g := by nlinarith
    have hprod : ((q₀ : ℤ) - g) * ((q₀ : ℤ) + g + 1) ≤ (s : ℤ) * Divisor.dim Dn :=
      mul_le_mul hs' hdn' (by positivity) (by positivity)
    have hdt' : (Divisor.dim Dt : ℤ) ≤ (q₀ : ℤ) * q₀ + g + 1 := by
      rw [hn] at hdimDt; push_cast at hdimDt; rw [hm'] at hdimDt; linarith
    have : (Divisor.dim Dt : ℤ) < (s : ℤ) * Divisor.dim Dn := by nlinarith
    exact_mod_cast this
  obtain ⟨G, hGker, hG0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt (f := Φ) hlt)
  have hG : ∑ j, f j ^ q₀ * (G j : F) = 0 := by
    have h1 := congrArg Subtype.val (LinearMap.mem_ker.mp hGker)
    exact h1
  set w : F := ∑ j, f j * (G j : F) ^ q₀ with hwdef
  have hw : w ≠ 0 := by
    intro hw0
    have hall := eq_zero_of_sum_pow_mul_eq_zero P₀ q₀ f hf0 hinj hrange (fun j => (G j : F))
      (by rw [← hw0, hwdef]; exact sum_congr rfl fun j _ => mul_comm _ _)
    exact hG0 (funext fun j => Subtype.ext (hall j))
  set z : F := w ^ q₀ with hzdef
  have hz0 : z ≠ 0 := pow_ne_zero _ hw
  have hzsum : z = ∑ j, f j ^ q₀ * (G j : F) ^ q := by
    have hfrob : ∀ x : F, x ^ q₀ = iterateFrobenius F p i x := fun x => by
      rw [iterateFrobenius_def, hi]
    rw [hzdef, hwdef, hfrob, map_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [← hfrob, mul_pow, ← pow_mul, hq₀]
  -- `z` has poles only at `P₀`, of order at most `q₀ m + q n`
  set Dz : Divisor k F := ((q₀ * m + q * n : ℕ) : ℤ) • WeilDivisor.ofPoint P₀ with hDz
  have hzmem : z ∈ riemannRochSpace Dz := by
    rw [hzsum]
    refine Submodule.sum_mem _ fun j _ => ?_
    have := mul_mem_riemannRochSpace_add (pow_mem_riemannRochSpace_zsmul (hfmem j) q₀)
      (pow_mem_riemannRochSpace_zsmul (G j).2 q)
    convert this using 2
    rw [hDz, hDn, smul_smul, smul_smul, ← add_smul]; push_cast; ring_nf
  obtain ⟨hzP₀, hzQ⟩ := (mem_riemannRochSpace_zsmul_ofPoint_iff hz0).mp hzmem
  -- regularity of the `f j` and `G j` away from `P₀`
  have hfreg : ∀ j (P : Place k F), P ≠ P₀ → P.valuation (f j) ≤ 1 := by
    intro j P hP
    have := ((mem_riemannRochSpace_zsmul_ofPoint_iff (hf0 j)).mp (hfmem j)).2 P hP
    rw [P.valuation_eq_exp_neg_ord (hf0 j), ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  have hGreg : ∀ j (P : Place k F), P ≠ P₀ → P.valuation (G j : F) ≤ 1 := by
    intro j P hP
    by_cases h0 : (G j : F) = 0
    · rw [h0, map_zero]; exact zero_le
    have := ((mem_riemannRochSpace_zsmul_ofPoint_iff h0).mp (G j).2).2 P hP
    rw [P.valuation_eq_exp_neg_ord h0, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  -- the other rational places
  have hTfin := Place.finite_setOf_degree_le hF 1
  set T : Finset (Place k F) := hTfin.toFinset.filter (fun P => P.degree = 1 ∧ P ≠ P₀) with hT
  have hP₀T : P₀ ∉ T := by simp [hT]
  have hzT : ∀ P ∈ T, (q₀ : ℤ) ≤ P.ord z := by
    intro P hPT
    have hP1 : P.degree = 1 := (Finset.mem_filter.mp hPT).2.1
    have hPne : P ≠ P₀ := (Finset.mem_filter.mp hPT).2.2
    have hz' : z = ∑ j, f j ^ q₀ * ((G j : F) ^ q - G j) := by
      rw [hzsum]; simp only [mul_sub, sum_sub_distrib, hG, sub_zero]
    have hv : P.valuation z < 1 := by
      rw [hz']
      refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
      rw [map_mul, map_pow]
      have h1 : P.valuation (f j) ^ q₀ ≤ 1 := pow_le_one' (hfreg j P hPne) q₀
      have h2 := valuation_pow_card_sub_lt_one hF P hP1 (G j : F) (hGreg j P hPne)
      exact lt_of_le_of_lt (mul_le_of_le_one_left' h1) h2
    have hord : 1 ≤ P.ord z := by
      rw [P.valuation_eq_exp_neg_ord hz0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hv; omega
    have hzw : P.ord z = q₀ * P.ord w := by rw [hzdef, P.ord_pow]
    rw [hzw] at hord ⊢
    have hw1 : 1 ≤ P.ord w := by
      by_contra hcon
      push Not at hcon
      have : (q₀ : ℤ) * P.ord w ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
      omega
    nlinarith
  have hcount := mul_card_le_of_ord hF z hz0 P₀ hP₀ T hP₀T q₀ (q₀ * m + q * n) hzT hzQ
    (by exact_mod_cast hzP₀)
  -- `N = #T + 1`
  have hNT : Nat.card {P : Place k F // P.degree = 1} = T.card + 1 := by
    have e1 : Nat.card {P : Place k F // P.degree = 1} =
        (hTfin.toFinset.filter (fun P => P.degree = 1)).card := by
      rw [← Nat.card_eq_finsetCard]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun P => by
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
        omega)
    have e2 : hTfin.toFinset.filter (fun P => P.degree = 1) = insert P₀ T := by
      ext P
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_insert, hT]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hP : P = P₀
        · exact Or.inl hP
        · exact Or.inr ⟨h1, h2, hP⟩
      · rintro (rfl | ⟨h1, h2, -⟩)
        · exact ⟨by omega, hP₀⟩
        · exact ⟨h1, h2⟩
    rw [e1, e2, Finset.card_insert_of_notMem hP₀T]
  have hTle : T.card ≤ m + q₀ * n := by
    have : q₀ * T.card ≤ q₀ * (m + q₀ * n) := by
      calc q₀ * T.card ≤ q₀ * m + q * n := hcount
        _ = q₀ * (m + q₀ * n) := by rw [hq₀]; ring
    exact Nat.le_of_mul_le_mul_left this hq₀pos
  have hNle : Nat.card {P : Place k F // P.degree = 1} ≤ q + (2 * g + 1) * q₀ := by
    rw [hNT, hq₀]
    have hm1 : m + 1 = q₀ := by omega
    calc T.card + 1 ≤ m + q₀ * n + 1 := by omega
      _ = (m + 1) + q₀ * n := by ring
      _ = q₀ + q₀ * n := by rw [hm1]
      _ = q₀ * q₀ + (2 * g + 1) * q₀ := by rw [hn]; ring
  have hsqrt : Real.sqrt (q : ℝ) = q₀ := by
    rw [hq₀]; push_cast; exact Real.sqrt_mul_self (by positivity)
  rw [hsqrt]
  have : (Nat.card {P : Place k F // P.degree = 1} : ℝ) ≤ (q : ℝ) + (2 * g + 1) * q₀ := by
    exact_mod_cast hNle
  linarith

/-- **Theorem 11.4** (Milne; Weil) from F. K. Schmidt's theorem and the even-degree lower bound: Bombieri's upper
bound is proved (`bombieriUpperBound`). -/
theorem weilCurveTheorem_of_schmidt_of_lowerBound (hS : SchmidtDegreeOne.{u, v})
    (hL : HasseWeilLowerBoundEven.{u, v}) : WeilCurveTheorem.{u, v} :=
  weilCurveTheorem_of_schmidt_of_upper_of_lower hS bombieriUpperBound hL

end ModularFormsKB.Milne
