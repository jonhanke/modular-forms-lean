import ModularFormsKB.Milne.Ch11.WeilEven
import ModularFormsKB.Milne.Ch11.WeilConstantExtensionExists
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Genus.Basic
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Genus.Change

/-!
# Milne, Section 11: the even-degree Hasse–Weil bound from Bombieri's bound

**Bombieri's bound** (Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Theorem 5.2.3 and its proof in
Section 5.2, after Stepanov and Bombieri): for a function field $F$ over $\mathbb F_q$ with exact constant field,
$q$ a square and $q > (g + 1)^4$, the number $N$ of rational places satisfies $|N - (q + 1)| \le (2g + 1)\sqrt q$.
It is stated here as the named statement `BombieriBound` (the upper bound is Bombieri's argument with Riemann–Roch
spaces and the Frobenius; the lower bound in Stichtenoth uses the Galois closure of $F/\mathbb F_q(x)$).

Applied to the constant field extensions $F\cdot\mathbb F_{q^n}$ ($n$ even, $q^n > (g+1)^4$), which have the same
genus, exact constants and $N_1 = N_n(F)$ (`card_degree_one_constantCompositum`), it gives `HasseWeilBoundEven`.
Together with `ModularFormsKB.Milne.Ch11.WeilEven` this proves **Theorem 11.4** from `SchmidtDegreeOne` and
`BombieriBound` (`weilCurveTheorem_of_schmidt_of_bombieri`).
-/

open Finset TauCeti

namespace ModularFormsKB.Milne

universe u v

/-- **Bombieri's bound** (Stichtenoth, Theorem 5.2.3 / Section 5.2; Stepanov, Bombieri 1973), as a named statement:
for a function field $F$ over a finite field $k$ with $q$ elements, $k$ algebraically closed in $F$, of genus $g$,
if $q$ is a square and $q > (g+1)^4$ then the number $N$ of places of degree one satisfies
$|N - (q + 1)| \le (2g + 1)\sqrt q$. -/
@[kb "stichtenoth2009" "Section 5.2, Bombieri's proof of the Hasse–Weil bound"]
structure BombieriBound : Prop where
  bound : ∀ (k : Type u) (F : Type v) [Field k] [Finite k] [Field F] [Algebra k F],
    IsFunctionField k F → IsIntegrallyClosedIn k F → IsSquare (Nat.card k) →
    (genus k F + 1) ^ 4 < Nat.card k →
    |(Nat.card {P : Place k F // P.degree = 1} : ℝ) - ((Nat.card k : ℝ) + 1)| ≤
      (2 * genus k F + 1) * Real.sqrt (Nat.card k)

/-- $(g + 1)^4 < q^n$ for $q \ge 2$ and $n \ge 4(g + 1)$. -/
lemma pow_four_lt_pow (g q n : ℕ) (hq : 2 ≤ q) (hn : 4 * (g + 1) ≤ n) : (g + 1) ^ 4 < q ^ n := by
  have h1 : g + 1 < 2 ^ (g + 1) := Nat.lt_two_pow_self
  calc (g + 1) ^ 4 < (2 ^ (g + 1)) ^ 4 := Nat.pow_lt_pow_left h1 (by norm_num)
    _ = 2 ^ (4 * (g + 1)) := by rw [← pow_mul, mul_comm]
    _ ≤ q ^ (4 * (g + 1)) := Nat.pow_le_pow_left hq _
    _ ≤ q ^ n := Nat.pow_le_pow_right (by omega) hn

/-- **`HasseWeilBoundEven` from `BombieriBound`** (applied to constant field extensions inside an algebraic
closure of $F$, whence the universe `v` for the constants). -/
theorem hasseWeilBoundEven_of_bombieri (hB : BombieriBound.{v, v}) : HasseWeilBoundEven.{u, v} := by
  refine ⟨fun k F _ _ _ _ hF hex => ?_⟩
  set q : ℕ := Nat.card k with hq
  have hq2 : 2 ≤ q := Finite.one_lt_card
  refine ⟨2 * genus k F + 1, 4 * (genus k F + 1) + 1, fun n hn h2 => ?_⟩
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
  have hb := hB.bound k' F' hF' hex' hsq hbig
  rw [card_degree_one_constantCompositum hF hex h, hdeg, hg, hcard] at hb
  have hsqrt : Real.sqrt ((q : ℝ) ^ (2 * m)) = Real.sqrt q ^ (2 * m) := by
    rw [show (q : ℝ) ^ (2 * m) = (Real.sqrt q ^ (2 * m)) ^ 2 by
      rw [← pow_mul, show 2 * m * 2 = 2 * (2 * m) by ring, pow_mul (Real.sqrt (q : ℝ)) 2,
        Real.sq_sqrt (by positivity)]]
    exact Real.sqrt_sq (by positivity)
  push_cast at hb
  rw [hsqrt] at hb
  exact_mod_cast hb

/-- **Theorem 11.4** (Milne; Weil's Riemann hypothesis for curves over finite fields) from F. K. Schmidt's theorem
and Bombieri's bound. -/
theorem weilCurveTheorem_of_schmidt_of_bombieri (hS : SchmidtDegreeOne.{u, v}) (hB : BombieriBound.{v, v}) :
    WeilCurveTheorem.{u, v} :=
  weilCurveTheorem_of_schmidt_of_even hS (hasseWeilBoundEven_of_bombieri hB)

end ModularFormsKB.Milne
