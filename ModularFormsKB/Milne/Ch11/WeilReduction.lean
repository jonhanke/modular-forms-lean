import ModularFormsKB.Milne.Ch11.ZetaFiniteField

/-!
# Milne, Section 11: Theorem 11.4 from the zeta function and a Hasse–Weil bound

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 11, pdf p. 110;
H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed. (`stichtenoth2009`), Sections 5.1–5.2.

The proof of Weil's theorem (`WeilCurveTheorem`) splits into two inputs of a very different nature:

- `WeilZetaRationality`: the zeta function $Z(t) = \sum_{D \ge 0} t^{\deg D}$ of a function field $F/\mathbb F_q$ of
  genus $g$ is $L(t)/((1-t)(1-qt))$ with $L(t) = \prod_{i=1}^{2g}(1 - \alpha_i t) \in \mathbb Z[t]$, the functional
  equation $L(t) = q^g t^{2g} L(1/qt)$ permutes the $\alpha_i$ by $\alpha \mapsto q/\alpha$, and the logarithmic
  derivative of the Euler product gives $N_n = 1 + q^n - \sum_i \alpha_i^n$ (Stichtenoth, Theorem 5.1.15 and
  Corollary 5.1.16). This is Riemann–Roch bookkeeping.
- `HasseWeilBound`: $|N_n - (q^n + 1)| \le C q^{n/2}$ for some $C$ independent of $n$ (Stichtenoth, Theorem 5.2.3 by
  the Stepanov–Bombieri method, with $C = 2g + 1$).

Granting these, the Riemann hypothesis $|\alpha_i| = q^{1/2}$ is elementary (Stichtenoth, Theorem 5.1.15 (c),
"(1) ⇒ (2)"): `norm_le_one_of_norm_sum_pow_le` shows that complex numbers $\beta_1, \dots, \beta_m$ whose power sums
are bounded satisfy $|\beta_i| \le 1$, by averaging $\sum_i (\beta_i \bar\beta_l / |\beta_l|^2)^n$ over $n$; applied
to $\beta_i = \alpha_i q^{-1/2}$ it gives $|\alpha_i| \le q^{1/2}$, and $\alpha \mapsto q/\alpha$ gives the reverse.

## Main results

- `norm_le_one_of_norm_sum_pow_le`: bounded power sums force $|\beta_i| \le 1$.
- `weilCurveTheorem_of_zetaRationality_of_hasseWeilBound`: `WeilCurveTheorem` from the two inputs.
-/

open Finset

namespace ModularFormsKB.Milne

universe u v

/-! ### Bounded power sums -/

/-- A geometric sum $\sum_{n=1}^{N} z^n$ with $|z| \le 1$ and $z \ne 1$ is bounded by $2/|z - 1|$, independently
of $N$. -/
lemma norm_sum_range_pow_succ_le {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) (N : ℕ) :
    ‖∑ n ∈ range N, z ^ (n + 1)‖ ≤ 2 / ‖z - 1‖ := by
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr hz1'
  have e : ∑ n ∈ range N, z ^ (n + 1) = z * ((z ^ N - 1) / (z - 1)) := by
    rw [← geom_sum_eq hz1, mul_sum]
    exact sum_congr rfl fun n _ => by ring
  rw [e, norm_mul, norm_div, le_div_iff₀ hpos, mul_assoc, div_mul_cancel₀ _ hpos.ne']
  have h1 : ‖z ^ N - 1‖ ≤ 2 := by
    calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by
          gcongr
          · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz
          · simp
      _ = 2 := by norm_num
  calc ‖z‖ * ‖z ^ N - 1‖ ≤ 1 * 2 := by gcongr
    _ = 2 := by norm_num

/-- A real geometric sum $\sum_{n=1}^N r^n$ with $0 \le r < 1$ is at most $1/(1-r)$. -/
lemma sum_range_pow_succ_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (N : ℕ) :
    ∑ n ∈ range N, r ^ (n + 1) ≤ 1 / (1 - r) := by
  have key : ∀ N : ℕ, (∑ n ∈ range N, r ^ (n + 1)) * (1 - r) = r * (1 - r ^ N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [sum_range_succ, add_mul, ih]; ring
  have hpos : 0 < 1 - r := by linarith
  rw [le_div_iff₀ hpos, key]
  have : 0 ≤ r ^ N := pow_nonneg h0 N
  nlinarith

/-- **Bounded power sums** (Stichtenoth, proof of Theorem 5.1.15): if the power sums $\sum_i \beta_i^n$, $n \ge 1$,
of finitely many complex numbers are bounded, then $|\beta_i| \le 1$ for all $i$. -/
theorem norm_le_one_of_norm_sum_pow_le {m : ℕ} (β : Fin m → ℂ) (C : ℝ)
    (h : ∀ n : ℕ, 1 ≤ n → ‖∑ i, β i ^ n‖ ≤ C) (i : Fin m) : ‖β i‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨l, -, hl⟩ := exists_max_image univ (fun j => ‖β j‖) ⟨i, mem_univ i⟩
  set ρ := ‖β l‖ with hρdef
  have hρ : 1 < ρ := lt_of_lt_of_le hlt (hl i (mem_univ i))
  have hρ0 : 0 < ρ := by linarith
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (h 1 le_rfl)
  set w : ℂ := starRingEnd ℂ (β l) / ((ρ : ℂ) ^ 2) with hw
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
  have hwnorm : ‖w‖ = 1 / ρ := by
    rw [hw, norm_div, Complex.norm_conj, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρ0, ← hρdef]
    field_simp
  have hlw : β l * w = 1 := by
    rw [hw, mul_div_assoc', Complex.mul_conj, Complex.normSq_eq_norm_sq, ← hρdef]
    push_cast
    exact div_self (pow_ne_zero 2 hρc)
  set z : Fin m → ℂ := fun j => β j * w with hz
  have hznorm : ∀ j, ‖z j‖ ≤ 1 := by
    intro j
    rw [hz, norm_mul, hwnorm, mul_one_div, div_le_one hρ0]
    exact hl j (mem_univ j)
  -- the averaged sum
  set A : ℕ → ℂ := fun N => ∑ n ∈ range N, (∑ j, β j ^ (n + 1)) * w ^ (n + 1) with hA
  have hA' : ∀ N, A N = ∑ j, ∑ n ∈ range N, z j ^ (n + 1) := by
    intro N
    rw [hA, sum_comm]
    simp only [sum_mul, hz, mul_pow]
  -- upper bound
  have hup : ∀ N, ‖A N‖ ≤ C * (1 / (1 - 1 / ρ)) := by
    intro N
    calc ‖A N‖ ≤ ∑ n ∈ range N, ‖(∑ j, β j ^ (n + 1)) * w ^ (n + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range N, C * (1 / ρ) ^ (n + 1) := by
          refine sum_le_sum fun n _ => ?_
          rw [norm_mul, norm_pow, hwnorm]
          gcongr
          exact h (n + 1) (by omega)
      _ = C * ∑ n ∈ range N, (1 / ρ) ^ (n + 1) := by rw [mul_sum]
      _ ≤ C * (1 / (1 - 1 / ρ)) := by
          gcongr
          exact sum_range_pow_succ_le (by positivity) ((div_lt_one hρ0).mpr hρ) N
  -- lower bound
  set S := univ.filter (fun j => z j = 1) with hS
  set K : ℝ := ∑ j, if z j = 1 then 0 else 2 / ‖z j - 1‖ with hK
  have hlS : l ∈ S := by simp [hS, hz, hlw]
  have hcard : 1 ≤ S.card := card_pos.mpr ⟨l, hlS⟩
  have hlow : ∀ N : ℕ, (N : ℝ) - K ≤ ‖A N‖ := by
    intro N
    set e : Fin m → ℂ := fun j => if z j = 1 then (N : ℂ) else 0 with he
    have hsum_e : ∑ j, e j = ((S.card * N : ℕ) : ℂ) := by
      rw [he, ← sum_filter, sum_const, nsmul_eq_mul, ← hS]
      push_cast; ring
    have hdiff : ‖A N - ∑ j, e j‖ ≤ K := by
      rw [hA', ← sum_sub_distrib, hK]
      refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
      by_cases hj : z j = 1
      · simp [he, hj]
      · simp only [he, hj, ite_false, sub_zero]
        exact norm_sum_range_pow_succ_le (hznorm j) hj N
    have hnorm_e : ‖∑ j, e j‖ = (S.card * N : ℕ) := by
      rw [hsum_e, Complex.norm_natCast]
    have hge : (N : ℝ) ≤ (S.card * N : ℕ) := by
      push_cast
      have : (1 : ℝ) ≤ S.card := by exact_mod_cast hcard
      nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have := norm_sub_norm_le (∑ j, e j) (A N)
    rw [norm_sub_rev] at this
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (K + C * (1 / (1 - 1 / ρ)))
  linarith [hup N, hlow N]

/-- **Bounded power sums, from some point on**: if the power sums $\sum_i \beta_i^n$ are bounded for $n \ge n_0$,
then $|\beta_i| \le 1$ for all $i$. -/
theorem norm_le_one_of_norm_sum_pow_le_of_ge {m : ℕ} (β : Fin m → ℂ) (C : ℝ) (n₀ : ℕ)
    (h : ∀ n : ℕ, n₀ ≤ n → ‖∑ i, β i ^ n‖ ≤ C) (i : Fin m) : ‖β i‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨l, -, hl⟩ := exists_max_image univ (fun j => ‖β j‖) ⟨i, mem_univ i⟩
  set ρ := ‖β l‖ with hρdef
  have hρ : 1 < ρ := lt_of_lt_of_le hlt (hl i (mem_univ i))
  have hρ0 : 0 < ρ := by linarith
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (h n₀ le_rfl)
  set w : ℂ := starRingEnd ℂ (β l) / ((ρ : ℂ) ^ 2) with hw
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
  have hwnorm : ‖w‖ = 1 / ρ := by
    rw [hw, norm_div, Complex.norm_conj, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρ0, ← hρdef]
    field_simp
  have hlw : β l * w = 1 := by
    rw [hw, mul_div_assoc', Complex.mul_conj, Complex.normSq_eq_norm_sq, ← hρdef]
    push_cast
    exact div_self (pow_ne_zero 2 hρc)
  set z : Fin m → ℂ := fun j => β j * w with hz
  have hznorm : ∀ j, ‖z j‖ ≤ 1 := by
    intro j
    rw [hz, norm_mul, hwnorm, mul_one_div, div_le_one hρ0]
    exact hl j (mem_univ j)
  -- the averaged sum
  set A : ℕ → ℂ := fun N => ∑ n ∈ range N, (∑ j, β j ^ (n + n₀ + 1)) * w ^ (n + n₀ + 1) with hA
  have hA' : ∀ N, A N = ∑ j, ∑ n ∈ range N, z j ^ (n + n₀ + 1) := by
    intro N
    rw [hA, sum_comm]
    simp only [sum_mul, hz, mul_pow]
  -- upper bound
  have hup : ∀ N, ‖A N‖ ≤ C * (1 / (1 - 1 / ρ)) := by
    intro N
    calc ‖A N‖ ≤ ∑ n ∈ range N, ‖(∑ j, β j ^ (n + n₀ + 1)) * w ^ (n + n₀ + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range N, C * (1 / ρ) ^ (n + 1) := by
          refine sum_le_sum fun n _ => ?_
          rw [norm_mul, norm_pow, hwnorm]
          have hr0 : 0 ≤ 1 / ρ := by positivity
          have hr1 : 1 / ρ ≤ 1 := (div_le_one hρ0).mpr hρ.le
          calc ‖∑ j, β j ^ (n + n₀ + 1)‖ * (1 / ρ) ^ (n + n₀ + 1)
              ≤ C * (1 / ρ) ^ (n + n₀ + 1) := by gcongr; exact h _ (by omega)
            _ ≤ C * (1 / ρ) ^ (n + 1) := by
                exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr1 (by omega)) hC
      _ = C * ∑ n ∈ range N, (1 / ρ) ^ (n + 1) := by rw [mul_sum]
      _ ≤ C * (1 / (1 - 1 / ρ)) := by
          gcongr
          exact sum_range_pow_succ_le (by positivity) ((div_lt_one hρ0).mpr hρ) N
  -- lower bound
  set S := univ.filter (fun j => z j = 1) with hS
  set K : ℝ := ∑ j, if z j = 1 then 0 else 2 / ‖z j - 1‖ with hK
  have hlS : l ∈ S := by simp [hS, hz, hlw]
  have hcard : 1 ≤ S.card := card_pos.mpr ⟨l, hlS⟩
  have hlow : ∀ N : ℕ, (N : ℝ) - K ≤ ‖A N‖ := by
    intro N
    set e : Fin m → ℂ := fun j => if z j = 1 then (N : ℂ) else 0 with he
    have hsum_e : ∑ j, e j = ((S.card * N : ℕ) : ℂ) := by
      rw [he, ← sum_filter, sum_const, nsmul_eq_mul, ← hS]
      push_cast; ring
    have hdiff : ‖A N - ∑ j, e j‖ ≤ K := by
      rw [hA', ← sum_sub_distrib, hK]
      refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
      by_cases hj : z j = 1
      · simp [he, hj, one_pow]
      · simp only [he, hj, ite_false, sub_zero]
        have e : ∑ n ∈ range N, z j ^ (n + n₀ + 1) = z j ^ n₀ * ∑ n ∈ range N, z j ^ (n + 1) := by
          rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
        rw [e, norm_mul, norm_pow]
        calc ‖z j‖ ^ n₀ * ‖∑ n ∈ range N, z j ^ (n + 1)‖ ≤ 1 * (2 / ‖z j - 1‖) := by
              gcongr
              · exact pow_le_one₀ (norm_nonneg _) (hznorm j)
              · exact norm_sum_range_pow_succ_le (hznorm j) hj N
          _ = 2 / ‖z j - 1‖ := one_mul _
    have hnorm_e : ‖∑ j, e j‖ = (S.card * N : ℕ) := by
      rw [hsum_e, Complex.norm_natCast]
    have hge : (N : ℝ) ≤ (S.card * N : ℕ) := by
      push_cast
      have : (1 : ℝ) ≤ S.card := by exact_mod_cast hcard
      nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have := norm_sub_norm_le (∑ j, e j) (A N)
    rw [norm_sub_rev] at this
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (K + C * (1 / (1 - 1 / ρ)))
  linarith [hup N, hlow N]

/-- If the power sums $\sum_i\beta_i^n$ are bounded for the multiples $n$ of $d \ge 1$ with $n \ge n_0$, then
$|\beta_i| \le 1$. -/
theorem norm_le_one_of_norm_sum_pow_le_of_dvd {m : ℕ} (β : Fin m → ℂ) (C : ℝ) (n₀ d : ℕ) (hd : 1 ≤ d)
    (h : ∀ n : ℕ, n₀ ≤ n → d ∣ n → ‖∑ i, β i ^ n‖ ≤ C) (i : Fin m) : ‖β i‖ ≤ 1 := by
  have h' := norm_le_one_of_norm_sum_pow_le_of_ge (fun j => β j ^ d) C n₀ (fun n hn => by
    simp only [← pow_mul]
    exact h _ (le_trans hn (Nat.le_mul_of_pos_left n hd)) (dvd_mul_right d n)) i
  rw [norm_pow] at h'
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp h'

/-! ### The two inputs and the reduction -/

/-- **Rationality and functional equation of the zeta function of a function field** (Stichtenoth, Theorem 5.1.15
(a), (b) and Corollary 5.1.16; F. K. Schmidt 1931), as a named statement: for a function field $F$ over a finite
field $k$ with $q$ elements, $k$ algebraically closed in $F$, of genus $g$, the reciprocal roots
$\alpha_1, \dots, \alpha_{2g}$ of the $L$-polynomial are nonzero algebraic integers, $N_n = 1 + q^n - \sum\alpha_i^n$
for $n \ge 1$, and $i \mapsto q/\alpha_i$ permutes them. -/
@[kb "stichtenoth2009" "Theorem 5.1.15 (a), (b), Corollary 5.1.16"]
structure WeilZetaRationality : Prop where
  rational : ∀ (k : Type u) (F : Type v) [Field k] [Finite k] [Field F] [Algebra k F],
    TauCeti.IsFunctionField k F → IsIntegrallyClosedIn k F →
    ∃ α : Fin (2 * TauCeti.genus k F) → ℂ, (∀ i, IsIntegral ℤ (α i)) ∧ (∀ i, α i ≠ 0) ∧
      (∀ n : ℕ, 1 ≤ n → (curvePointCount k F n : ℂ) =
        1 + (Nat.card k : ℂ) ^ n - ∑ i, α i ^ n) ∧
      (∃ σ : Equiv.Perm (Fin (2 * TauCeti.genus k F)), ∀ i, (Nat.card k : ℂ) / α i = α (σ i))

/-- **The Hasse–Weil bound up to a constant** (Stichtenoth, Theorem 5.2.3, proved there by the Stepanov–Bombieri
method with constant $2g+1$), as a named statement: for a function field $F$ over a finite field $k$ with $q$
elements, $k$ algebraically closed in $F$, there is $C$ with $|N_n - (q^n + 1)| \le C q^{n/2}$ for all $n \ge 1$. -/
@[kb "stichtenoth2009" "Theorem 5.2.3 (Hasse–Weil bound, Bombieri's proof)"]
structure HasseWeilBound : Prop where
  bound : ∀ (k : Type u) (F : Type v) [Field k] [Finite k] [Field F] [Algebra k F],
    TauCeti.IsFunctionField k F → IsIntegrallyClosedIn k F →
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(curvePointCount k F n : ℝ) - ((Nat.card k : ℝ) ^ n + 1)| ≤ C * Real.sqrt (Nat.card k) ^ n

/-- **Theorem 11.4** (Milne; Weil) from the rationality of the zeta function and the Hasse–Weil bound
(Stichtenoth, Theorem 5.1.15 (c)): the bound makes the power sums of $\alpha_i q^{-1/2}$ bounded, so
$|\alpha_i| \le q^{1/2}$, and $\alpha \mapsto q/\alpha$ gives $|\alpha_i| \ge q^{1/2}$. -/
theorem weilCurveTheorem_of_zetaRationality_of_hasseWeilBound
    (hZ : WeilZetaRationality.{u, v}) (hB : HasseWeilBound.{u, v}) : WeilCurveTheorem.{u, v} := by
  refine ⟨fun k F _ _ _ _ hF hex => ?_⟩
  obtain ⟨α, hint, hne, hN, σ, hσ⟩ := hZ.rational k F hF hex
  obtain ⟨C, hC⟩ := hB.bound k F hF hex
  refine ⟨α, hint, hN, ⟨σ, hσ⟩, ?_⟩
  set q : ℝ := (Nat.card k : ℝ) with hq
  have hq0 : 0 < q := by rw [hq]; exact_mod_cast Nat.card_pos
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hsq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq0.le
  -- `|α_i| ≤ √q` for every `i`
  have hle : ∀ i, ‖α i‖ ≤ Real.sqrt q := by
    intro i
    set β : Fin (2 * TauCeti.genus k F) → ℂ := fun j => α j / (Real.sqrt q : ℂ) with hβ
    have hsc : (Real.sqrt q : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    have hb := norm_le_one_of_norm_sum_pow_le β C (fun n hn => by
      have hsum : ∑ j, β j ^ n = (∑ j, α j ^ n) / (Real.sqrt q : ℂ) ^ n := by
        rw [sum_div]; exact sum_congr rfl fun j _ => by rw [hβ, div_pow]
      have hαsum : ∑ j, α j ^ n =
          (((q ^ n + 1 - curvePointCount k F n : ℝ)) : ℂ) := by
        push_cast
        rw [hN n hn, hq]; push_cast; ring
      rw [hsum, hαsum, norm_div, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hs0, div_le_iff₀ (pow_pos hs0 n), abs_sub_comm]
      have := hC n hn
      convert this using 2) i
    rw [hβ, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0, div_le_one hs0] at hb
    exact hb
  intro i
  refine le_antisymm (hle i) ?_
  have h2 := hle (σ i)
  rw [← hσ i, norm_div, Complex.norm_natCast, ← hq, div_le_iff₀ (norm_pos_iff.mpr (hne i))] at h2
  -- `q ≤ √q · |α_i|` gives `√q ≤ |α_i|`
  by_contra hlt
  push Not at hlt
  have : Real.sqrt q * ‖α i‖ < Real.sqrt q * Real.sqrt q := mul_lt_mul_of_pos_left hlt hs0
  nlinarith [hsq]

end ModularFormsKB.Milne
