import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.GroupTheory.OrderOfElement
import ModularFormsKB.Citation
/-!
# Miyake §§4.1–4.2: the modular group `SL₂(ℤ)`

Miyake, *Modular Forms* (Springer 1989).

* Lemma 4.1.5 (p. 99): with `Γ = SL₂(ℤ)` and `Γ_∞` its stabilizer of `∞` (the matrices with
  lower-left entry `0`), the correspondence `[[a, b], [c, d]] ↦ (c, d)` is a bijection from
  `Γ_∞ \ Γ` onto the coprime pairs `(c, d) ∈ ℤ²` modulo `±1`
  (`ModularFormsKB.Miyake.exists_gammaInftyCosetsEquivCoprimePairs`).
* Lemma 4.2.6 (p. 107): an elliptic element of a modular group has order `2` or `3` as a
  transformation, that is, in `SL₂(ℤ) / {±1}` (`ModularFormsKB.Miyake.orderOf_isElliptic`).
  The statement is proved for every elliptic element of `SL₂(ℤ)`, which covers every modular
  group (a finite-index subgroup of `SL₂(ℤ)`).

Matrix entries are 0-based: Miyake's `c` is `γ 1 0`, `d` is `γ 1 1`.
-/

open Matrix
open scoped MatrixGroups

namespace ModularFormsKB.Miyake

/-- `Γ_∞`: the stabilizer of `∞` in `SL₂(ℤ)`, the matrices with lower-left entry `0`
(equivalently `{±[[1, m], [0, 1]]}`). -/
def gammaInfty : Subgroup SL(2, ℤ) where
  carrier := {g | g 1 0 = 0}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, ha]

/-- Coprime pairs `(c, d) ∈ ℤ²`. -/
def CoprimePair : Type := {v : Fin 2 → ℤ // IsCoprime (v 0) (v 1)}

/-- The relation `v ~ ±v` on coprime pairs. -/
def coprimePairSetoid : Setoid CoprimePair where
  r v w := w.1 = v.1 ∨ w.1 = -v.1
  iseqv := by
    refine ⟨fun v => Or.inl rfl, fun {v w} h => ?_, fun {u v w} h1 h2 => ?_⟩
    · rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, neg_neg])
    · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact Or.inl (h2.trans h1)
      · exact Or.inr (by rw [h2, h1])
      · exact Or.inr (by rw [h2, h1])
      · exact Or.inl (by rw [h2, h1, neg_neg])

/-- **Miyake, Lemma 4.1.5.** The correspondence `[[a, b], [c, d]] ↦ (c, d)` gives a bijection
between the right cosets `Γ_∞ \ Γ` (`Γ = SL₂(ℤ)`) and the coprime pairs modulo `±1`. -/
@[kb "miyake1989" "Lemma 4.1.5, p. 99"]
theorem exists_gammaInftyCosetsEquivCoprimePairs :
    ∃ e : Quotient (QuotientGroup.rightRel gammaInfty) ≃ Quotient coprimePairSetoid,
      ∀ g : SL(2, ℤ), ∃ h : IsCoprime (g 1 0) (g 1 1),
        e (Quotient.mk _ g) = Quotient.mk _ ⟨![g 1 0, g 1 1], h⟩ := by
  have hcop : ∀ g : SL(2, ℤ), IsCoprime (g 1 0) (g 1 1) := fun g => by
    have hdet := g.det_coe
    rw [Matrix.det_fin_two] at hdet
    exact ⟨-g 0 1, g 0 0, by linarith⟩
  let f : SL(2, ℤ) → CoprimePair := fun g => ⟨![g 1 0, g 1 1], by simpa using hcop g⟩
  -- the lower-left entry of `h g⁻¹`
  have hentry : ∀ g h : SL(2, ℤ), (h * g⁻¹) 1 0 = h 1 0 * g 1 1 - h 1 1 * g 1 0 := by
    intro g h
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two]
    ring
  have key : ∀ g h : SL(2, ℤ),
      QuotientGroup.rightRel gammaInfty g h ↔ coprimePairSetoid (f g) (f h) := by
    intro g h
    rw [QuotientGroup.rightRel_apply]
    change (h * g⁻¹) 1 0 = 0 ↔ (![h 1 0, h 1 1] = ![g 1 0, g 1 1] ∨
      ![h 1 0, h 1 1] = -![g 1 0, g 1 1])
    rw [hentry]
    constructor
    · intro h0
      -- `h = δ g` with `δ = h g⁻¹` upper triangular, `δ 1 1 = ±1`
      set δ := h * g⁻¹ with hδ
      have hδ10 : δ 1 0 = 0 := by rw [hδ, hentry]; exact h0
      have hdetδ := δ.det_coe
      rw [Matrix.det_fin_two, hδ10, mul_zero, sub_zero] at hdetδ
      have hhg : h = δ * g := by rw [hδ, inv_mul_cancel_right]
      have hrow : ∀ j, h 1 j = δ 1 1 * g 1 j := by
        intro j
        rw [hhg]
        simp [Matrix.mul_apply, Fin.sum_univ_two, hδ10]
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdetδ with ⟨-, h1⟩ | ⟨-, h1⟩
      · left; ext j; fin_cases j <;> simp [hrow, h1]
      · right; ext j; fin_cases j <;> simp [hrow, h1]
    · rintro (H | H)
      · have h1 := congrFun H 0
        have h2 := congrFun H 1
        simp at h1 h2
        rw [h1, h2]; ring
      · have h1 := congrFun H 0
        have h2 := congrFun H 1
        simp at h1 h2
        rw [h1, h2]; ring
  let F : Quotient (QuotientGroup.rightRel gammaInfty) → Quotient coprimePairSetoid :=
    Quotient.map f fun g h hgh => (key g h).1 hgh
  have hinj : Function.Injective F := by
    intro x y hxy
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    exact Quotient.sound ((key _ _).2 (Quotient.exact hxy))
  have hsurj : Function.Surjective F := by
    intro q
    induction q using Quotient.inductionOn with
    | h v =>
      obtain ⟨u, w, huw⟩ := v.2
      let g : SL(2, ℤ) := ⟨!![w, -u; v.1 0, v.1 1], by
        rw [Matrix.det_fin_two_of]; linarith⟩
      refine ⟨Quotient.mk _ g, Quotient.sound ?_⟩
      change v.1 = ![v.1 0, v.1 1] ∨ v.1 = -![v.1 0, v.1 1]
      left; ext j; fin_cases j <;> rfl
  refine ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun g => ⟨hcop g, rfl⟩⟩

/-- `{±1}`, the center of `SL₂(ℤ)`. -/
def plusMinusOne : Subgroup SL(2, ℤ) := Subgroup.zpowers (-1)

lemma mem_plusMinusOne_iff (g : SL(2, ℤ)) : g ∈ plusMinusOne ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    rcases Int.even_or_odd n with he | ho
    · left; exact he.neg_one_zpow
    · right; exact ho.neg_one_zpow
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

instance : plusMinusOne.Normal := by
  constructor
  intro n hn g
  rcases (mem_plusMinusOne_iff n).1 hn with rfl | rfl
  · simpa using Subgroup.one_mem plusMinusOne
  · rw [mul_neg, mul_one, neg_mul, mul_inv_cancel]
    exact Subgroup.mem_zpowers _

/-- **Miyake, Lemma 4.2.6.** Every elliptic element of a modular group has order `2` or `3` as
a transformation of `ℍ`, i.e. its image in `SL₂(ℤ) / {±1}` has order `2` or `3`. -/
@[kb "miyake1989" "Lemma 4.2.6, p. 107"]
theorem orderOf_isElliptic (γ : SL(2, ℤ)) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ).IsElliptic) :
    orderOf (QuotientGroup.mk γ : SL(2, ℤ) ⧸ plusMinusOne) = 2 ∨
      orderOf (QuotientGroup.mk γ : SL(2, ℤ) ⧸ plusMinusOne) = 3 := by
  set A := (γ : Matrix (Fin 2) (Fin 2) ℤ) with hAdef
  set t := A.trace with ht
  have hdet : A.det = 1 := γ.det_coe
  have hd : A.discr = t ^ 2 - 4 := by
    rw [Matrix.discr_fin_two, hdet, ← ht]; ring
  rw [Matrix.IsElliptic, hd] at hγ
  have ht1 : -1 ≤ t ∧ t ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (t - 2), sq_nonneg (t + 2)]
  -- Cayley–Hamilton: `γ² = t γ - 1`
  have hCH : A * A = t • A - 1 := by
    have hdet' := hdet
    rw [Matrix.det_fin_two] at hdet'
    rw [ht, Matrix.trace_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul] <;> norm_num <;> linarith
  -- `γ ≠ ±1`, since `±1` has trace `±2`
  have hne : (QuotientGroup.mk γ : SL(2, ℤ) ⧸ plusMinusOne) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, mem_plusMinusOne_iff]
    rintro (rfl | rfl)
    · simp [ht, hAdef] at ht1
    · simp [ht, hAdef, Matrix.trace_fin_two] at ht1
  have hmk : ∀ δ : SL(2, ℤ), (δ : Matrix (Fin 2) (Fin 2) ℤ) = 1 ∨
      (δ : Matrix (Fin 2) (Fin 2) ℤ) = -1 → (QuotientGroup.mk δ : SL(2, ℤ) ⧸ plusMinusOne) = 1 := by
    intro δ hδ
    rw [QuotientGroup.eq_one_iff, mem_plusMinusOne_iff]
    rcases hδ with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext (by simpa using h)
  obtain ⟨h1, h2⟩ := ht1
  have : t = -1 ∨ t = 0 ∨ t = 1 := by omega
  rcases this with h | h | h
  · -- `γ³ = 1`
    right
    apply orderOf_eq_prime _ hne
    rw [← QuotientGroup.mk_pow]
    apply hmk
    left
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_succ, sq, hCH, sub_mul, Matrix.smul_mul, hCH, h,
      Matrix.one_mul]
    module
  · -- `γ² = -1`
    left
    apply orderOf_eq_prime _ hne
    rw [← QuotientGroup.mk_pow]
    apply hmk
    right
    rw [Matrix.SpecialLinearGroup.coe_pow, sq, hCH, h]
    module
  · -- `γ³ = -1`
    right
    apply orderOf_eq_prime _ hne
    rw [← QuotientGroup.mk_pow]
    apply hmk
    right
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_succ, sq, hCH, sub_mul, Matrix.smul_mul, hCH, h,
      Matrix.one_mul]
    module

end ModularFormsKB.Miyake
