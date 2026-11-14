import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Data.Int.CardIntervalMod
import ModularFormsKB.Citation
/-!
# Miyake §4.1: the monomial basis of level-one modular forms, Theorem 4.1.8

Miyake, *Modular Forms* (Springer 1989), Theorem 4.1.8, p. 102: for an even weight `k`, the
monomials `G₄^m G₆^n` with `4m + 6n = k` form a basis of the modular forms of weight `k` for the
full modular group.

Miyake's `G_k` in this theorem is the normalized Eisenstein series `G_k = 1 + O(q)` ((4.1.19),
(4.1.20), p. 101), which is Mathlib's `ModularForm.E₄`, `ModularForm.E₆` (constant term `1`).
The monomial `E₄^m E₆^n` is the weight-`k` component of `(E₄)^m (E₆)^n` in Mathlib's graded ring
`⨁ k, ModularForm 𝒮ℒ k`.

Proof: the monomials span (Mathlib's `ModularForm.evalE₄E₆_surjective`), and their number is
`dim M_k` (Mathlib's `ModularForm.dimension_level_one`), so they are linearly independent. The
statement holds for every `k : ℕ` (for odd `k`, and for `k = 2`, both sides are zero; for `k = 0`
the basis is `{1}`); Miyake states it for even `k ≥ 4`.
-/

open ModularForm
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave6

/-- The exponent pairs `(m, n)` with `4m + 6n = k`. -/
abbrev MonomialIndex (k : ℕ) : Type := {mn : ℕ × ℕ // 4 * mn.1 + 6 * mn.2 = k}

/-- The monomial `E₄^m E₆^n` as a modular form of weight `k = 4m + 6n` for `SL₂(ℤ)`. -/
def e4e6Monomial (k : ℕ) (mn : MonomialIndex k) : ModularForm 𝒮ℒ (k : ℤ) :=
  ((DirectSum.of (ModularForm 𝒮ℒ) 4 E₄) ^ mn.1.1 * (DirectSum.of (ModularForm 𝒮ℒ) 6 E₆) ^ mn.1.2)
    (k : ℤ)

/-- The index type is finite. -/
instance (k : ℕ) : Finite (MonomialIndex k) :=
  Finite.of_injective
    (fun mn : MonomialIndex k =>
      ((⟨mn.1.1, by have := mn.2; lia⟩ : Fin (k + 1)), (⟨mn.1.2, by have := mn.2; lia⟩ : Fin (k + 1))))
    (fun a b h => by
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [Fin.mk.injEq] at h1 h2
      exact Subtype.ext (Prod.ext h1 h2))

/-- Every weight-`k` component of an element of the range of `evalE₄E₆` lies in the span of the
monomials. -/
lemma evalE₄E₆_apply_mem_span (k : ℕ) (P : MvPolynomial (Fin 2) ℂ) :
    (evalE₄E₆ P) (k : ℤ) ∈ Submodule.span ℂ (Set.range (e4e6Monomial k)) := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have h1 : evalE₄E₆ (MvPolynomial.monomial u a) =
        a • ((DirectSum.of (ModularForm 𝒮ℒ) 4 E₄) ^ u 0 *
          (DirectSum.of (ModularForm 𝒮ℒ) 6 E₆) ^ u 1) := by
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
      simp [MvPolynomial.C_eq_smul_one, map_mul, map_pow, evalE₄E₆_X_zero, evalE₄E₆_X_one,
        smul_mul_assoc]
    rw [h1]
    change a • ((_ * _ : DirectSum ℤ (ModularForm 𝒮ℒ)) (k : ℤ)) ∈ _
    refine Submodule.smul_mem _ _ ?_
    by_cases hk : 4 * u 0 + 6 * u 1 = k
    · exact Submodule.subset_span ⟨⟨(u 0, u 1), hk⟩, rfl⟩
    · rw [DirectSum.ofPow, DirectSum.ofPow, DirectSum.of_mul_of,
        DirectSum.of_eq_of_ne]
      · exact Submodule.zero_mem _
      · intro h
        apply hk
        have : (k : ℤ) = ((4 * u 0 + 6 * u 1 : ℕ) : ℤ) := by
          rw [h]; push_cast; simp [smul_eq_mul]; ring
        have h' : 4 * u 0 + 6 * u 1 = k := by exact_mod_cast this.symm
        exact h'
  | add p q hp hq =>
    rw [map_add]
    exact add_mem hp hq

/-- The monomials span. -/
lemma span_e4e6Monomial_eq_top (k : ℕ) :
    Submodule.span ℂ (Set.range (e4e6Monomial k)) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  obtain ⟨P, hP⟩ := evalE₄E₆_surjective (DirectSum.of _ (k : ℤ) f)
  have := evalE₄E₆_apply_mem_span k P
  rwa [hP, DirectSum.of_eq_same] at this

/-- The monomial index set is in bijection with `n < k/6+1`, `n ≡ k/2 (2)` for even `k`. -/
def monomialIndexEquiv (k : ℕ) (hk : Even k) :
    MonomialIndex k ≃ {n : ℕ // n < k / 6 + 1 ∧ n ≡ k / 2 [MOD 2]} where
  toFun mn := ⟨mn.1.2, by
    have := mn.2; obtain ⟨j, hj⟩ := hk
    simp only [Nat.ModEq]; constructor <;> lia⟩
  invFun n := ⟨((k - 6 * n.1) / 4, n.1), by
    have := n.2; obtain ⟨j, hj⟩ := hk
    simp only [Nat.ModEq] at this; lia⟩
  left_inv mn := by
    have := mn.2
    apply Subtype.ext
    apply Prod.ext
    · simp only; lia
    · rfl
  right_inv n := rfl

/-- Counting the monomials. -/
lemma card_monomialIndex (k : ℕ) :
    Nat.card (MonomialIndex k) = if Odd k then 0 else
      if k ≡ 2 [MOD 12] then k / 12 else k / 12 + 1 := by
  by_cases hk : Even k
  · rw [if_neg (Nat.not_odd_iff_even.mpr hk), Nat.card_congr (monomialIndexEquiv k hk)]
    have h := Nat.count_modEq_card (k / 6 + 1) (r := 2) (by norm_num) (k / 2)
    rw [Nat.count_eq_card_filter_range] at h
    have h2 : Nat.card {n : ℕ // n < k / 6 + 1 ∧ n ≡ k / 2 [MOD 2]} =
        ((Finset.range (k / 6 + 1)).filter (· ≡ k / 2 [MOD 2])).card := by
      rw [← Nat.card_eq_finsetCard]
      exact Nat.card_congr (Equiv.subtypeEquivRight (fun n => by simp))
    rw [h2, h]
    obtain ⟨j, hj⟩ := hk
    simp only [Nat.ModEq]
    split_ifs <;> lia
  · rw [Nat.not_even_iff_odd] at hk
    rw [if_pos hk]
    haveI : IsEmpty (MonomialIndex k) := ⟨fun mn => by
      have := mn.2; obtain ⟨j, hj⟩ := hk; lia⟩
    exact Nat.card_of_isEmpty

/-- **Miyake, Theorem 4.1.8**: the monomials `E₄^m E₆^n`, `4m + 6n = k`, are linearly independent
and span the modular forms of weight `k` for `SL₂(ℤ)`. -/
@[kb "miyake1989" "Theorem 4.1.8, p. 102"]
theorem linearIndependent_e4e6Monomial_and_span_eq_top (k : ℕ) :
    LinearIndependent ℂ (e4e6Monomial k) ∧
      Submodule.span ℂ (Set.range (e4e6Monomial k)) = ⊤ := by
  refine ⟨?_, span_e4e6Monomial_eq_top k⟩
  haveI : Fintype (MonomialIndex k) := Fintype.ofFinite _
  have hfin : Module.finrank ℂ (ModularForm 𝒮ℒ (k : ℤ)) = Nat.card (MonomialIndex k) := by
    rw [card_monomialIndex]
    by_cases hk : Odd k
    · rw [if_pos hk]
      exact Module.finrank_eq_of_rank_eq (by
        simpa using levelOne_odd_weight_rank_zero (k := (k : ℤ)) (by exact_mod_cast hk))
    · rw [if_neg hk]
      have hev : Even k := Nat.not_odd_iff_even.mp hk
      have := dimension_level_one k hev
      split_ifs at this ⊢
      · exact Module.finrank_eq_of_rank_eq (by simpa using this)
      · exact Module.finrank_eq_of_rank_eq (by simpa using this)
  refine linearIndependent_of_top_le_span_of_card_eq_finrank
    (span_e4e6Monomial_eq_top k).ge ?_
  rw [hfin, Nat.card_eq_fintype_card]

/-- **Miyake, Theorem 4.1.8** as a basis. -/
@[kb "miyake1989" "Theorem 4.1.8, p. 102 (basis)"]
def e4e6Basis (k : ℕ) : Module.Basis (MonomialIndex k) ℂ (ModularForm 𝒮ℒ (k : ℤ)) :=
  Module.Basis.mk (linearIndependent_e4e6Monomial_and_span_eq_top k).1
    (linearIndependent_e4e6Monomial_and_span_eq_top k).2.ge

@[simp] lemma e4e6Basis_apply (k : ℕ) (mn : MonomialIndex k) :
    e4e6Basis k mn = e4e6Monomial k mn :=
  Module.Basis.mk_apply _ _ _

end ModularFormsKB.Miyake.Wave6
