import Mathlib

/-!
# Algebra of the $L$-polynomial: reciprocal roots and the logarithmic derivative

Elementary facts used to pass from the $L$-polynomial of a function field over $\mathbb F_q$ to Weil's
$\alpha_1, \dots, \alpha_{2g}$ (Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Theorem 5.1.15 and
its proof):

- `exists_reciprocalRoots`: an integer polynomial $L$ of degree $2g$ with $L(0) = 1$ satisfying the functional
  equation $q^i c_{2g-i} = q^g c_i$ factors over $\mathbb C$ as $\prod_i (1 - \alpha_i t)$ with nonzero algebraic
  integers $\alpha_i$ permuted by $\alpha \mapsto q/\alpha$.
- `newton_of_mul_eq_prod`: if $(1-t)(1-qt)Z(t) = \prod_i(1 - \alpha_i t)$ with $Z = \sum A_n t^n$, then
  $n A_n = \sum_{k=1}^{n} (1 + q^k - \sum_i \alpha_i^k) A_{n-k}$ (the logarithmic derivative $tZ'/Z$).
-/

open Finset Polynomial

namespace ModularFormsKB.Milne

/-! ### Helpers for `exists_reciprocalRoots` -/

lemma one_sub_C_mul_X_eq (a : ℂ) (ha : a ≠ 0) :
    (1 - C a * X : ℂ[X]) = C (-a) * (X - C a⁻¹) := by
  rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ ha]
  simp only [map_neg, map_one]
  ring

lemma prod_one_sub_eq {ι : Type*} [Fintype ι] (a : ι → ℂ) (ha : ∀ i, a i ≠ 0) :
    ∏ i, (1 - C (a i) * X : ℂ[X]) = C (∏ i, -a i) * ∏ i, (X - C (a i)⁻¹) := by
  rw [map_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => one_sub_C_mul_X_eq _ (ha i)

lemma roots_prod_one_sub {ι : Type*} [Fintype ι] (a : ι → ℂ) (ha : ∀ i, a i ≠ 0) :
    (∏ i, (1 - C (a i) * X : ℂ[X])).roots = Finset.univ.val.map (fun i => (a i)⁻¹) := by
  rw [prod_one_sub_eq a ha,
    roots_C_mul _ (Finset.prod_ne_zero_iff.mpr fun i _ => neg_ne_zero.mpr (ha i))]
  have := roots_multiset_prod_X_sub_C (Finset.univ.val.map (fun i => (a i)⁻¹))
  rw [Multiset.map_map] at this
  exact this

lemma exists_enum (s : Multiset ℂ) (n : ℕ) (h : Multiset.card s = n) :
    ∃ e : Fin n → ℂ, Finset.univ.val.map e = s := by
  obtain ⟨l, rfl⟩ : ∃ l : List ℂ, (l : Multiset ℂ) = s := ⟨s.toList, by simp⟩
  simp only [Multiset.coe_card] at h
  subst h
  exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]⟩

lemma exists_perm_of_map_eq {ι κ : Type*} [Fintype ι] [DecidableEq κ] (f g : ι → κ)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) :
    ∃ σ : Equiv.Perm ι, ∀ i, f i = g (σ i) := by
  have hc : ∀ c, Fintype.card {a // f a = c} = Fintype.card {b // g b = c} := by
    intro c
    have := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.card_def, Finset.filter_val, eq_comm] using this
  let e : ∀ c, {a // f a = c} ≃ {b // g b = c} := fun c => Fintype.equivOfCardEq (hc c)
  exact ⟨Equiv.ofFiberEquiv e, fun i => (Equiv.ofFiberEquiv_map e i).symm⟩

lemma exists_reciprocalRoots_aux (g : ℕ) (L : ℤ[X]) (hdeg : L.natDegree = 2 * g)
    (h0 : L.coeff 0 = 1) :
    ∃ α : Fin (2 * g) → ℂ, (∀ i, IsIntegral ℤ (α i)) ∧ (∀ i, α i ≠ 0) ∧
      L.map (Int.castRingHom ℂ) = ∏ i, (1 - C (α i) * X) := by
  set Lc := L.map (Int.castRingHom ℂ) with hLc
  have hLcdeg : Lc.natDegree = 2 * g := by
    rw [hLc, natDegree_map_eq_of_injective (RingHom.injective_int _)]; exact hdeg
  have hLc0 : Lc.eval 0 = 1 := by
    rw [← coeff_zero_eq_eval_zero, hLc, coeff_map, h0]; simp
  have hLcne : Lc ≠ 0 := by
    intro h; rw [h] at hLc0; simp at hLc0
  have hcard : Multiset.card Lc.roots = 2 * g := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hLcdeg]
  obtain ⟨r, hr⟩ := exists_enum Lc.roots (2 * g) hcard
  have hfac : C Lc.leadingCoeff * (Lc.roots.map (fun a => X - C a)).prod = Lc :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C (hcard.trans hLcdeg.symm)
  rw [← hr, Multiset.map_map] at hfac
  have hfac' : C Lc.leadingCoeff * ∏ i, (X - C (r i)) = Lc := hfac
  have hrroot : ∀ i, Lc.eval (r i) = 0 := by
    intro i
    have : r i ∈ Lc.roots := by
      rw [← hr]; exact Multiset.mem_map_of_mem r (Finset.mem_univ i)
    exact (mem_roots hLcne).mp this
  have hr0 : ∀ i, r i ≠ 0 := by
    intro i h
    have := hrroot i
    rw [h, hLc0] at this
    exact one_ne_zero this
  have hα0 : ∀ i, (r i)⁻¹ ≠ 0 := fun i => inv_ne_zero (hr0 i)
  have hprod := prod_one_sub_eq (fun i => (r i)⁻¹) hα0
  simp only [inv_inv] at hprod
  have hPi : (∏ i, (0 - r i) : ℂ) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    simpa using hr0 i
  have hev1 : Lc.leadingCoeff * ∏ i, (0 - r i) = 1 := by
    have := congrArg (Polynomial.eval 0) hfac'
    simpa [eval_prod, hLc0] using this
  have hev2 : (∏ i, -(r i)⁻¹ : ℂ) * ∏ i, (0 - r i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    have := hr0 i
    field_simp
    ring
  have hlead : Lc.leadingCoeff = ∏ i, -(r i)⁻¹ := mul_right_cancel₀ hPi (hev1.trans hev2.symm)
  refine ⟨fun i => (r i)⁻¹, ?_, hα0, ?_⟩
  · intro i
    have hmonic : L.reverse.Monic := by
      unfold Monic
      rw [reverse_leadingCoeff, trailingCoeff,
        natTrailingDegree_eq_zero.mpr (Or.inr (by rw [h0]; exact one_ne_zero)), h0]
    refine ⟨L.reverse, hmonic, ?_⟩
    have : Invertible (r i) := invertibleOfNonzero (hr0 i)
    have h1 := (eval₂_reverse_eq_zero_iff (Int.castRingHom ℂ) (r i) L).mpr (by
      rw [← eval_map]; exact hrroot i)
    rw [invOf_eq_inv] at h1
    convert h1
  · rw [hprod, ← hlead, ← hfac']
    simp [hfac']

lemma evalFE (g q : ℕ) (L : ℤ[X]) (hdeg : L.natDegree = 2 * g) (hq0 : (q : ℂ) ≠ 0)
    (hFE : ∀ i, i ≤ 2 * g → (q : ℤ) ^ i * L.coeff (2 * g - i) = (q : ℤ) ^ g * L.coeff i)
    (x : ℂ) (hx : x ≠ 0) :
    (L.map (Int.castRingHom ℂ)).eval x =
      (q : ℂ) ^ g * x ^ (2 * g) * (L.map (Int.castRingHom ℂ)).eval ((q : ℂ) * x)⁻¹ := by
  have hdeg' : (L.map (Int.castRingHom ℂ)).natDegree < 2 * g + 1 := by
    rw [natDegree_map_eq_of_injective (RingHom.injective_int _), hdeg]; omega
  rw [eval_eq_sum_range' hdeg', eval_eq_sum_range' hdeg', Finset.mul_sum,
    ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ 2 * g := by simp at hj; omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hj'
  have hjk : 2 * g + 1 - 1 - j = k := by omega
  have hF := hFE j hj'
  have hF' : (q : ℂ) ^ j * (L.coeff k : ℂ) = (q : ℂ) ^ g * (L.coeff j : ℂ) := by
    have := hF
    rw [show 2 * g - j = k by omega] at this
    exact_mod_cast this
  rw [hjk, coeff_map, coeff_map, hk]
  simp only [eq_intCast]
  have hF'' : (q : ℂ) ^ g * (L.coeff j : ℂ) = (q : ℂ) ^ j * (L.coeff k : ℂ) := hF'.symm
  have e : (q : ℂ) ^ g * x ^ (j + k) * ((L.coeff j : ℂ) * ((q : ℂ) * x)⁻¹ ^ j) =
      ((q : ℂ) ^ g * (L.coeff j : ℂ)) * (x ^ (j + k) * ((q : ℂ) * x)⁻¹ ^ j) := by ring
  have hqj : (q : ℂ) ^ j ≠ 0 := pow_ne_zero _ hq0
  have hxj : x ^ j ≠ 0 := pow_ne_zero _ hx
  have hinv : ((q : ℂ) * x)⁻¹ ^ j = ((q : ℂ) ^ j)⁻¹ * (x ^ j)⁻¹ := by
    rw [mul_inv, mul_pow, inv_pow, inv_pow]
  rw [e, hF'', hinv, pow_add]
  field_simp

/-- **Reciprocal roots of the $L$-polynomial.** -/
theorem exists_reciprocalRoots (g q : ℕ) (hq : 1 ≤ q) (L : ℤ[X]) (hdeg : L.natDegree = 2 * g)
    (h0 : L.coeff 0 = 1)
    (hFE : ∀ i, i ≤ 2 * g → (q : ℤ) ^ i * L.coeff (2 * g - i) = (q : ℤ) ^ g * L.coeff i) :
    ∃ α : Fin (2 * g) → ℂ, (∀ i, IsIntegral ℤ (α i)) ∧ (∀ i, α i ≠ 0) ∧
      L.map (Int.castRingHom ℂ) = ∏ i, (1 - C (α i) * X) ∧
      ∃ σ : Equiv.Perm (Fin (2 * g)), ∀ i, (q : ℂ) / α i = α (σ i) := by
  obtain ⟨α, hint, hα0, hP⟩ := exists_reciprocalRoots_aux g L hdeg h0
  refine ⟨α, hint, hα0, hP, ?_⟩
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hβ0 : ∀ i, (q : ℂ) / α i ≠ 0 := fun i => div_ne_zero hq0 (hα0 i)
  set Q : ℂ[X] := ∏ i, (1 - C ((q : ℂ) / α i) * X) with hQ
  have hpt : ∀ x : ℂ, x ≠ 0 →
      (C ((q : ℂ) ^ g) * L.map (Int.castRingHom ℂ)).eval x =
        (C (∏ i, -α i) * Q).eval x := by
    intro x hx
    have hqx : (q : ℂ) * x ≠ 0 := mul_ne_zero hq0 hx
    have h1 := evalFE g q L hdeg hq0 hFE x hx
    rw [hP] at h1
    simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_one, eval_X] at h1 ⊢
    rw [hP]
    simp only [eval_prod, eval_sub, eval_one, eval_mul, eval_C, eval_X]
    rw [h1]
    have e1 : (q : ℂ) ^ g * ((q : ℂ) ^ g * x ^ (2 * g) * ∏ i, (1 - α i * ((q : ℂ) * x)⁻¹)) =
        ∏ i : Fin (2 * g), ((q : ℂ) * x) * (1 - α i * ((q : ℂ) * x)⁻¹) := by
      have hp : ∏ i : Fin (2 * g), ((q : ℂ) * x) = (q : ℂ) ^ g * (q : ℂ) ^ g * x ^ (2 * g) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← pow_add, ← two_mul]
      rw [Finset.prod_mul_distrib, hp]
      ring
    rw [e1]
    simp only [hQ, eval_prod, eval_sub, eval_one, eval_mul, eval_C, eval_X]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have := hα0 i
    field_simp
    ring
  have hCQ : C ((q : ℂ) ^ g) * L.map (Int.castRingHom ℂ) = C (∏ i, -α i) * Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := {x : ℂ | x ≠ 0})
    · intro x hx; exact hpt x hx
    · exact Set.infinite_univ.sdiff (Set.finite_singleton 0) |>.mono
        (by intro x hx; simpa using hx)
  have hc : (q : ℂ) ^ g = ∏ i, -α i := by
    have := congrArg (Polynomial.eval 0) hCQ
    rw [hP, hQ] at this
    simpa [eval_prod] using this
  have hLQ : L.map (Int.castRingHom ℂ) = Q := by
    rw [← hc] at hCQ
    exact mul_left_cancel₀ (by simpa using pow_ne_zero g hq0) hCQ
  have hroots := congrArg Polynomial.roots hLQ
  rw [hP, hQ, roots_prod_one_sub α hα0, roots_prod_one_sub _ hβ0] at hroots
  have hm : Finset.univ.val.map (fun i => (q : ℂ) / α i) = Finset.univ.val.map α := by
    have := congrArg (Multiset.map (fun z : ℂ => z⁻¹)) hroots
    simpa [Multiset.map_map, Function.comp_def] using this.symm
  obtain ⟨σ, hσ⟩ := exists_perm_of_map_eq _ _ hm
  exact ⟨σ, hσ⟩

/-! ### Helpers for `newton_of_mul_eq_prod` -/

/-- The power series `∑_{n ≥ 1} γ ^ n t ^ n`. -/
noncomputable def sPS (γ : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => if n = 0 then 0 else γ ^ n

lemma one_sub_mul_sPS (γ : ℂ) : (1 - PowerSeries.C γ * PowerSeries.X) * sPS γ =
    PowerSeries.C γ * PowerSeries.X := by
  ext n
  rcases n with _ | n
  · simp [sPS, sub_mul]
  · rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul]
    rcases n with _ | n
    · simp [sPS]
    · simp [sPS, pow_succ]; ring

lemma X_mul_derivative_prod_one_sub (ι : Type*) [DecidableEq ι] (s : Finset ι) (a : ι → ℂ) :
    PowerSeries.X * PowerSeries.derivative (∏ i ∈ s, (1 - PowerSeries.C (a i) * PowerSeries.X)) =
      -(∏ i ∈ s, (1 - PowerSeries.C (a i) * PowerSeries.X)) * ∑ i ∈ s, sPS (a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, sum_insert hj, Derivation.leibniz]
    simp only [smul_eq_mul, map_sub, PowerSeries.derivative_one, PowerSeries.derivative_X,
      Derivation.leibniz, PowerSeries.derivative_C, mul_one, mul_zero, zero_sub]
    have := one_sub_mul_sPS (a j)
    calc _ = (1 - PowerSeries.C (a j) * PowerSeries.X) * (PowerSeries.X *
          PowerSeries.derivative (∏ i ∈ s, (1 - PowerSeries.C (a i) * PowerSeries.X))) -
          PowerSeries.C (a j) * PowerSeries.X *
            ∏ i ∈ s, (1 - PowerSeries.C (a i) * PowerSeries.X) := by ring
      _ = _ := by
        rw [ih]
        linear_combination ((∏ i ∈ s, (1 - PowerSeries.C (a i) * PowerSeries.X))) * this

/-- **The logarithmic derivative of the zeta function** in coefficients. -/
theorem newton_of_mul_eq_prod {m : ℕ} (q : ℂ) (α : Fin m → ℂ) (A : ℕ → ℂ)
    (h : (1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X) * PowerSeries.mk A =
      ((∏ i, (1 - C (α i) * X) : ℂ[X]) : PowerSeries ℂ)) (n : ℕ) :
    (n : ℂ) * A n = ∑ j ∈ range n, (1 + q ^ (j + 1) - ∑ i, α i ^ (j + 1)) * A (n - 1 - j) := by
  have hcoe : ((∏ i, (1 - C (α i) * X) : ℂ[X]) : PowerSeries ℂ) =
      ∏ i, (1 - PowerSeries.C (α i) * PowerSeries.X) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    simp
  rw [hcoe] at h
  set Z : PowerSeries ℂ := PowerSeries.mk A with hZ
  set W : PowerSeries ℂ := (1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X) with hWdef
  set P : PowerSeries ℂ := ∏ i, (1 - PowerSeries.C (α i) * PowerSeries.X) with hPdef
  have hW : PowerSeries.X * PowerSeries.derivative W = -W * (sPS 1 + sPS q) := by
    have := X_mul_derivative_prod_one_sub (Fin 2) Finset.univ ![1, q]
    simpa [Fin.sum_univ_two, Fin.prod_univ_two, hWdef] using this
  have hP : PowerSeries.X * PowerSeries.derivative P = -P * ∑ i, sPS (α i) :=
    X_mul_derivative_prod_one_sub (Fin m) Finset.univ α
  have h1 : PowerSeries.X * (W • PowerSeries.derivative Z + Z • PowerSeries.derivative W) =
      PowerSeries.X * PowerSeries.derivative P := by
    have hd : PowerSeries.derivative P =
        W • PowerSeries.derivative Z + Z • PowerSeries.derivative W := by
      rw [← h]; exact Derivation.leibniz _ _ _
    rw [hd]
  simp only [smul_eq_mul] at h1
  have hW0 : W ≠ 0 := by
    intro h0
    have := congrArg PowerSeries.constantCoeff h0
    simp [hWdef] at this
  have h2 : PowerSeries.X * PowerSeries.derivative Z =
      Z * (sPS 1 + sPS q - ∑ i, sPS (α i)) := by
    apply mul_left_cancel₀ hW0
    linear_combination h1 - Z * hW + hP + (∑ i, sPS (α i)) * h
  have h3 := congrArg (PowerSeries.coeff n) h2
  have hG : ∀ k, PowerSeries.coeff k (sPS 1 + sPS q - ∑ i, sPS (α i)) =
      if k = 0 then 0 else 1 + q ^ k - ∑ i, α i ^ k := by
    intro k
    rcases k with _ | k
    · simp [sPS]
    · simp [sPS, map_sum]
  have hL : PowerSeries.coeff n (PowerSeries.X * PowerSeries.derivative Z) = n * A n := by
    rcases n with _ | n
    · simp
    · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
      simp [hZ]; ring
  rw [hL, PowerSeries.coeff_mul] at h3
  rw [h3, ← Finset.Nat.sum_antidiagonal_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
  simp only [Prod.swap, hG, ite_true, mul_zero, add_zero, Nat.succ_ne_zero, ite_false, hZ,
    PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm]
  have : n - 1 - j = n - (j + 1) := by omega
  rw [this]

end ModularFormsKB.Milne
