import ModularFormsKB.Milne.Ch11.WeilBombieri

/-!
# Milne, Section 11: Bombieri's upper bound and a lower bound, separately

`BombieriBound` (`ModularFormsKB.Milne.Ch11.WeilBombieri`) packages an upper and a lower bound proved by different
methods (Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Section 5.2): the upper bound
$N \le q + 1 + (2g+1)\sqrt q$ for $q$ a square with $q > (g+1)^4$ is Bombieri's argument with Riemann–Roch spaces and
the Frobenius (`BombieriUpperBound`); the lower bound comes from the upper bound for twisted forms of a Galois closure
and only needs some constant depending on $F$ (`HasseWeilLowerBoundEven`). This file proves `HasseWeilBoundEven` and
**Theorem 11.4** from `SchmidtDegreeOne`, `BombieriUpperBound` and `HasseWeilLowerBoundEven`.
-/

open Finset TauCeti

namespace ModularFormsKB.Milne

universe u v

/-- **Bombieri's upper bound** (Stichtenoth, Section 5.2; Bombieri 1973 after Stepanov), as a named statement: for a
function field $F$ over a finite field $k$ with $q$ elements, $k$ algebraically closed in $F$, of genus $g$, if $q$ is
a square and $q > (g + 1)^4$ then the number $N$ of places of degree one satisfies $N \le q + 1 + (2g + 1)\sqrt q$. -/
@[kb "stichtenoth2009" "Section 5.2, Bombieri's upper bound"]
structure BombieriUpperBound : Prop where
  bound : ∀ (k : Type u) (F : Type v) [Field k] [Finite k] [Field F] [Algebra k F],
    IsFunctionField k F → IsIntegrallyClosedIn k F → IsSquare (Nat.card k) →
    (genus k F + 1) ^ 4 < Nat.card k →
    (Nat.card {P : Place k F // P.degree = 1} : ℝ) ≤
      (Nat.card k : ℝ) + 1 + (2 * genus k F + 1) * Real.sqrt (Nat.card k)

/-- **A lower bound in even degrees** (Stichtenoth, Section 5.2, the Galois-closure argument), as a named
statement: there are $C$ and $n_0$ with $N_n \ge q^n + 1 - C q^{n/2}$ for even $n \ge n_0$. -/
@[kb "stichtenoth2009" "Section 5.2, lower bound via a Galois closure"]
structure HasseWeilLowerBoundEven : Prop where
  bound : ∀ (k : Type u) (F : Type v) [Field k] [Finite k] [Field F] [Algebra k F],
    IsFunctionField k F → IsIntegrallyClosedIn k F →
    ∃ (C : ℝ) (n₀ : ℕ), ∀ n : ℕ, n₀ ≤ n → 2 ∣ n →
      (Nat.card k : ℝ) ^ n + 1 - C * Real.sqrt (Nat.card k) ^ n ≤ curvePointCount k F n

/-- Bombieri's upper bound, transported to $N_n(F)$ for even $n$ through the constant field extension of degree
$n$. -/
theorem curvePointCount_le_of_bombieriUpper (hU : BombieriUpperBound.{v, v}) {k : Type u} {F : Type v}
    [Field k] [Finite k] [Field F] [Algebra k F] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (n : ℕ) (hn : 4 * (genus k F + 1) + 1 ≤ n) (h2 : 2 ∣ n) :
    (curvePointCount k F n : ℝ) ≤
      (Nat.card k : ℝ) ^ n + 1 + (2 * genus k F + 1) * Real.sqrt (Nat.card k) ^ n := by
  set q : ℕ := Nat.card k with hq
  have hq2 : 2 ≤ q := Finite.one_lt_card
  obtain ⟨F', k', hfd, hdeg, h⟩ := exists_constantCompositum_finrank_eq (k := k) (F := F) n (by omega)
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  have hex' : IsIntegrallyClosedIn k' F' := IsIntegrallyClosedIn.of_constantCompositum_eq_top hex h
  have hg : genus k' F' = genus k F := genus_eq_genus_of_constantCompositum_eq_top hF hex h
  have : Finite k' := Module.finite_of_finite k
  have hcard : Nat.card k' = q ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := k), hdeg]
  obtain ⟨m, rfl⟩ := h2
  have hsq : IsSquare (Nat.card k') := ⟨q ^ m, by rw [hcard]; ring⟩
  have hbig : (genus k' F' + 1) ^ 4 < Nat.card k' := by
    rw [hg, hcard]; exact pow_four_lt_pow _ _ _ hq2 (by omega)
  have hb := hU.bound k' F' hF' hex' hsq hbig
  rw [card_degree_one_constantCompositum hF hex h, hdeg, hg, hcard] at hb
  have hsqrt : Real.sqrt ((q : ℝ) ^ (2 * m)) = Real.sqrt q ^ (2 * m) := by
    rw [show (q : ℝ) ^ (2 * m) = (Real.sqrt q ^ (2 * m)) ^ 2 by
      rw [← pow_mul, show 2 * m * 2 = 2 * (2 * m) by ring, pow_mul (Real.sqrt (q : ℝ)) 2,
        Real.sq_sqrt (by positivity)]]
    exact Real.sqrt_sq (by positivity)
  push_cast at hb
  rw [hsqrt] at hb
  exact_mod_cast hb

/-- **`HasseWeilBoundEven` from Bombieri's upper bound and the even-degree lower bound.** -/
theorem hasseWeilBoundEven_of_upper_of_lower (hU : BombieriUpperBound.{v, v})
    (hL : HasseWeilLowerBoundEven.{u, v}) : HasseWeilBoundEven.{u, v} := by
  refine ⟨fun k F _ _ _ _ hF hex => ?_⟩
  obtain ⟨C, n₀, hC⟩ := hL.bound k F hF hex
  refine ⟨max C (2 * genus k F + 1), max n₀ (4 * (genus k F + 1) + 1), fun n hn h2 => ?_⟩
  have hup := curvePointCount_le_of_bombieriUpper hU hF hex n (le_trans (le_max_right _ _) hn) h2
  have hlow := hC n (le_trans (le_max_left _ _) hn) h2
  have hs : 0 ≤ Real.sqrt (Nat.card k) ^ n := by positivity
  rw [abs_le]
  constructor
  · nlinarith [le_max_left C (2 * (genus k F : ℝ) + 1), mul_le_mul_of_nonneg_right
      (le_max_left C (2 * (genus k F : ℝ) + 1)) hs]
  · nlinarith [mul_le_mul_of_nonneg_right (le_max_right C (2 * (genus k F : ℝ) + 1)) hs]

/-- **Theorem 11.4** (Milne; Weil) from F. K. Schmidt's theorem, Bombieri's upper bound and the even-degree lower
bound. -/
theorem weilCurveTheorem_of_schmidt_of_upper_of_lower (hS : SchmidtDegreeOne.{u, v})
    (hU : BombieriUpperBound.{v, v}) (hL : HasseWeilLowerBoundEven.{u, v}) : WeilCurveTheorem.{u, v} :=
  weilCurveTheorem_of_schmidt_of_even hS (hasseWeilBoundEven_of_upper_of_lower hU hL)

end ModularFormsKB.Milne
