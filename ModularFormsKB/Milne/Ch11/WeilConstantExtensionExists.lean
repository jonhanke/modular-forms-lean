import ModularFormsKB.Milne.Ch11.WeilConstantExtension
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic

/-!
# Constant field extensions of a given degree over a finite field

For a function field $F$ over a finite field $k$ and every $n \ge 1$ there is a constant field extension
$F' = F\cdot k'$ inside an algebraic closure of $F$ with $[k' : k] = n$: take for $k'$ the splitting field of
$X^{q^n} - X$ over $k$ (Tau Ceti, `exists_finiteDimensional_normal_splits_constantCompositum_eq_top`), which is the
field with $q^n$ elements.
-/

open TauCeti

namespace ModularFormsKB.Milne

universe u v

open Polynomial in
/-- A splitting field of `X^(q^n) - X` over a field `k` with `q` elements has degree `n`. -/
theorem finrank_of_isSplittingField_pow_sub_X {k K : Type*} [Field k] [Finite k] [Field K]
    [Algebra k K] (n : ℕ) (hn : 1 ≤ n)
    [hs : Polynomial.IsSplittingField k K (X ^ (Nat.card k ^ n) - X : k[X])] :
    Module.finrank k K = n := by
  classical
  have := Fintype.ofFinite k
  have : FiniteDimensional k K := Polynomial.IsSplittingField.finiteDimensional K (X ^ (Nat.card k ^ n) - X : k[X])
  have : Finite K := Module.finite_of_finite k
  set f : k[X] := X ^ (Nat.card k ^ n) - X with hf
  have hq2 : 2 ≤ Nat.card k := Nat.succ_le_of_lt Finite.one_lt_card
  have hlt : 1 < Nat.card k ^ n :=
    Nat.one_lt_pow (by omega) (by omega)
  have hdeg : f.natDegree = Nat.card k ^ n := natDegree_X_pow_sub_X hlt
  have hsep : f.Separable := by
    apply galois_poly_separable (ringChar k)
    rw [← CharP.cast_eq_zero_iff k (ringChar k)]
    have : ((Nat.card k : ℕ) : k) = 0 := by
      rw [Nat.card_eq_fintype_card]; exact FiniteField.cast_card_eq_zero k
    rw [Nat.cast_pow, this, zero_pow (by omega)]
  have hsplit : (f.map (algebraMap k K)).Splits := Polynomial.IsSplittingField.splits K f
  have hcard := Polynomial.card_rootSet_eq_natDegree (K := K) hsep hsplit
  -- every element of `K` is a root of `f`
  have hall : ∀ x : K, x ^ (Nat.card k ^ n) = x := by
    have hle : Algebra.adjoin k (f.rootSet K) ≤
        AlgHom.equalizer ((FiniteField.frobeniusAlgHom k K) ^ n) (AlgHom.id k K) := by
      rw [Algebra.adjoin_le_iff]
      intro x hx
      rw [mem_rootSet] at hx
      have h0 := hx.2
      simp only [hf, map_sub, map_pow, aeval_X] at h0
      show ((FiniteField.frobeniusAlgHom k K) ^ n) x = x
      rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, Fintype.card_eq_nat_card]
      exact sub_eq_zero.mp h0
    rw [Polynomial.IsSplittingField.adjoin_rootSet] at hle
    intro x
    have := hle (Algebra.mem_top (x := x))
    change ((FiniteField.frobeniusAlgHom k K) ^ n) x = x at this
    rwa [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate,
      Fintype.card_eq_nat_card] at this
  have huniv : f.rootSet K = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    rw [mem_rootSet]
    refine ⟨X_pow_sub_X_ne_zero hlt, ?_⟩
    simp only [hf, map_sub, map_pow, aeval_X]
    rw [hall x, sub_self]
  have hK : Nat.card K = Nat.card k ^ n := by
    rw [← hdeg, ← hcard, ← Nat.card_eq_fintype_card, huniv, Nat.card_univ]
  rw [Module.natCard_eq_pow_finrank (K := k) (V := K)] at hK
  exact Nat.pow_right_injective hq2 hK

/-- A constant field extension of degree $n$. -/
theorem exists_constantCompositum_finrank_eq {k : Type u} {F : Type v} [Field k] [Finite k] [Field F]
    [Algebra k F] (n : ℕ) (hn : 1 ≤ n) :
    ∃ (F' : IntermediateField F (AlgebraicClosure F)) (k' : IntermediateField k F'),
      FiniteDimensional k k' ∧ Module.finrank k k' = n ∧ constantCompositum F k' F' = ⊤ := by
  obtain ⟨F', k', hfd, -, -, hsf, hc⟩ :=
    exists_finiteDimensional_normal_splits_constantCompositum_eq_top F
      (f := (Polynomial.X ^ (Nat.card k ^ n) - Polynomial.X : Polynomial k))
  exact ⟨F', k', hfd, finrank_of_isSplittingField_pow_sub_X n hn, hc⟩

end ModularFormsKB.Milne
