import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import ModularFormsKB.Citation
/-!
# Eisenstein's reduced matrices of determinant `ε`

Eisenstein, *Mathematische Abhandlungen* (1847), on the transformations of elliptic functions: every integer matrix of determinant `ε > 0` is a unimodular
matrix times one of the reduced matrices `(ϑ, 0; ξ, ϑ')`, `ϑ ϑ' = ε`, `0 ≤ ξ < ϑ'`; their number is
`σ(ε) = ∑_{d ∣ ε} d`, the number of essentially different transformations of degree `ε`.

Order of the factors. With the bound `0 ≤ ξ < ϑ'` the decomposition is unique when the reduced matrix stands on
the left, `A = T U` with `U ∈ SL₂(ℤ)` (right multiplication by `U` performs column operations, which change `ξ` by
multiples of `ϑ'`); in the other order, `A = U T`, the entry `ξ` is determined only modulo `ϑ` and the bound would
be `0 ≤ ξ < ϑ`. In Eisenstein's notation of composed substitutions the unimodular substitution is applied to the
result of the reduced one; the formal statement uses `A = T U`.
-/

noncomputable section

open Matrix
open scoped MatrixGroups ArithmeticFunction.sigma

namespace ModularFormsKB.Historical.Eisenstein

/-- Eisenstein's reduced matrices `(ϑ, 0; ξ, ϑ')` of determinant `ε`: `ϑ, ϑ' > 0`, `ϑ ϑ' = ε`, `0 ≤ ξ < ϑ'`. -/
def IsReducedMatrix (ε : ℤ) (T : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  T 0 1 = 0 ∧ 0 < T 0 0 ∧ 0 < T 1 1 ∧ T 0 0 * T 1 1 = ε ∧ 0 ≤ T 1 0 ∧ T 1 0 < T 1 1

/-- The finite set of reduced matrices of determinant `ε`. -/
def reducedMatrices (ε : ℕ) : Finset (Matrix (Fin 2) (Fin 2) ℤ) :=
  ε.divisorsAntidiagonal.biUnion fun ad ↦
    (Finset.range ad.2).image fun ξ : ℕ ↦ !![(ad.1 : ℤ), 0; (ξ : ℤ), (ad.2 : ℤ)]

/-- **Eisenstein's reduction of integer matrices** (1847): for `ε > 0`, every integer
matrix `A` with `det A = ε` is `T U` with `U ∈ SL₂(ℤ)` for exactly one reduced matrix `T`; the reduced matrices of
determinant `ε` are the elements of `reducedMatrices ε`, and there are `σ(ε)` of them. -/
@[kb "eisenstein1847" "Abhandlungen, transformation of elliptic functions"]
def EisensteinReduction : Prop :=
  ∀ ε : ℕ, 0 < ε →
    (∀ A : Matrix (Fin 2) (Fin 2) ℤ, A.det = ε →
      ∃! T : Matrix (Fin 2) (Fin 2) ℤ, IsReducedMatrix ε T ∧ ∃ U : SL(2, ℤ), A = T * (U : Matrix (Fin 2) (Fin 2) ℤ)) ∧
    (∀ T : Matrix (Fin 2) (Fin 2) ℤ, T ∈ reducedMatrices ε ↔ IsReducedMatrix ε T) ∧
    (reducedMatrices ε).card = σ 1 ε


lemma isReduced_of_mem {ε : ℕ} {T : Matrix (Fin 2) (Fin 2) ℤ} (h : T ∈ reducedMatrices ε) :
    IsReducedMatrix ε T := by
  simp only [reducedMatrices, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range,
    Nat.mem_divisorsAntidiagonal] at h
  obtain ⟨⟨a, d⟩, ⟨had, hε⟩, ξ, hξ, rfl⟩ := h
  have ha : 0 < a := Nat.pos_of_ne_zero (fun h0 ↦ hε (by simp [← had, h0]))
  have hd : 0 < d := Nat.pos_of_ne_zero (fun h0 ↦ hε (by simp [← had, h0]))
  simp only at hξ had
  refine ⟨by simp, by simpa using ha, by simpa using hd, by simp [← had], by simp, by simpa using hξ⟩

lemma mem_of_isReduced {ε : ℕ} {T : Matrix (Fin 2) (Fin 2) ℤ} (h : IsReducedMatrix ε T) :
    T ∈ reducedMatrices ε := by
  obtain ⟨h01, h00, h11, hdet, h10, h10'⟩ := h
  simp only [reducedMatrices, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range,
    Nat.mem_divisorsAntidiagonal]
  refine ⟨((T 0 0).toNat, (T 1 1).toNat), ⟨?_, ?_⟩, (T 1 0).toNat, ?_, ?_⟩
  · have : ((T 0 0).toNat * (T 1 1).toNat : ℕ) = (ε : ℤ) := by
      rw [← hdet]; push_cast; rw [Int.toNat_of_nonneg h00.le, Int.toNat_of_nonneg h11.le]
    exact_mod_cast this
  · intro h0
    have : ((T 0 0).toNat * (T 1 1).toNat : ℕ) = (ε : ℤ) := by
      rw [← hdet]; push_cast; rw [Int.toNat_of_nonneg h00.le, Int.toNat_of_nonneg h11.le]
    rw [h0] at this
    simp at this
    omega
  · simpa using (by omega : (T 1 0).toNat < (T 1 1).toNat)
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, Int.toNat_of_nonneg h00.le, Int.toNat_of_nonneg h11.le,
      Int.toNat_of_nonneg h10]

lemma exists_reduced {ε : ℕ} (hε : 0 < ε) (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det = ε) :
    ∃ T : Matrix (Fin 2) (Fin 2) ℤ, IsReducedMatrix ε T ∧
      ∃ U : SL(2, ℤ), A = T * (U : Matrix (Fin 2) (Fin 2) ℤ) := by
  set a := A 0 0 with ha
  set b := A 0 1 with hb
  set p := A 1 0 with hp
  set q := A 1 1 with hq
  have hdet : a * q - b * p = ε := by rw [← hA, Matrix.det_fin_two]
  set g : ℤ := (Int.gcd a b : ℤ) with hg
  obtain ⟨a', ha'⟩ : g ∣ a := Int.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ : g ∣ b := Int.gcd_dvd_right a b
  have hgpos : 0 < g := by
    rcases Nat.eq_zero_or_pos (Int.gcd a b) with h0 | h0
    · exfalso
      have h12 : a = 0 ∧ b = 0 := by simpa [Int.gcd_eq_zero_iff] using h0
      rw [h12.1, h12.2] at hdet
      have : (ε : ℤ) = 0 := by rw [← hdet]; ring
      omega
    · rw [hg]; exact_mod_cast h0
  set x := Int.gcdA a b
  set y := Int.gcdB a b
  have hbez : g * (x * a' + y * b') = g * 1 := by
    have := Int.gcd_eq_gcd_ab a b
    rw [← hg] at this
    calc g * (x * a' + y * b') = a * x + b * y := by rw [ha', hb'] at *; ring
      _ = g * 1 := by rw [this]; ring
  have hbez' : x * a' + y * b' = 1 := mul_left_cancel₀ hgpos.ne' hbez
  set d := a' * q - b' * p with hd
  have hgd : g * d = ε := by
    rw [← hdet, hd, ha', hb']; ring
  have hdpos : 0 < d := by
    by_contra hneg
    replace hneg := not_lt.mp hneg
    have : g * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hgpos.le hneg
    omega
  set c := p * x + q * y with hc
  set k := c / d with hk
  have hU : (!![a', b'; k * a' - y, k * b' + x] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hbez'
  refine ⟨!![g, 0; c % d, d], ⟨by simp, by simpa using hgpos, by simpa using hdpos, by simpa using hgd,
    by simpa using Int.emod_nonneg _ hdpos.ne', by simpa using Int.emod_lt_of_pos _ hdpos⟩,
    ⟨!![a', b'; k * a' - y, k * b' + x], hU⟩, ?_⟩
  have hmod : c % d = c - d * k := Int.emod_def c d
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hmod]
  · exact ha'
  · exact hb'
  · rw [hd, hc]; linear_combination (-p) * hbez'
  · rw [hd, hc]; linear_combination (-q) * hbez'

lemma reduced_unique {ε : ℕ} {T₁ T₂ : Matrix (Fin 2) (Fin 2) ℤ} (h₁ : IsReducedMatrix ε T₁)
    (h₂ : IsReducedMatrix ε T₂) (U₁ U₂ : SL(2, ℤ))
    (h : T₁ * (U₁ : Matrix (Fin 2) (Fin 2) ℤ) = T₂ * (U₂ : Matrix (Fin 2) (Fin 2) ℤ)) : T₁ = T₂ := by
  obtain ⟨h01, h00, h11, hdet, h10, h10'⟩ := h₁
  obtain ⟨g01, g00, g11, gdet, g10, g10'⟩ := h₂
  set W : SL(2, ℤ) := U₂ * U₁⁻¹ with hW
  have hT : T₁ = T₂ * (W : Matrix (Fin 2) (Fin 2) ℤ) := by
    have : (U₁ : Matrix (Fin 2) (Fin 2) ℤ) * ((U₁⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
    calc T₁ = T₁ * ((U₁ : Matrix (Fin 2) (Fin 2) ℤ) * ((U₁⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
          rw [this, Matrix.mul_one]
      _ = (T₁ * (U₁ : Matrix (Fin 2) (Fin 2) ℤ)) * ((U₁⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [Matrix.mul_assoc]
      _ = T₂ * (W : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [h, hW, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
  have hWdet : (W : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := W.2
  rw [Matrix.det_fin_two] at hWdet
  have e00 := congrFun (congrFun hT 0) 0
  have e01 := congrFun (congrFun hT 0) 1
  have e10 := congrFun (congrFun hT 1) 0
  have e11 := congrFun (congrFun hT 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, g01] at e00 e01 e10 e11
  rw [h01] at e01
  have hw01 : (W : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := by
    have : T₂ 0 0 * (W : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · omega
    · exact h0
  rw [hw01] at hWdet e11
  simp only [mul_zero, sub_zero, zero_mul, add_zero] at hWdet e00 e11 e10
  have hw00 : (W : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 := by
    have hpos : 0 < (W : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
      by_contra hn; replace hn := not_lt.mp hn
      have := mul_nonpos_of_nonneg_of_nonpos g00.le hn
      omega
    have h1 : (W : Matrix (Fin 2) (Fin 2) ℤ) 0 0 ∣ 1 := ⟨_, hWdet.symm⟩
    exact Int.eq_one_of_dvd_one hpos.le h1
  have hw11 : (W : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by
    rw [hw00] at hWdet; linarith
  rw [hw00] at e00 e10
  rw [hw11] at e11
  have hw10 : (W : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
    have hlt : T₂ 1 1 * (W : Matrix (Fin 2) (Fin 2) ℤ) 1 0 < T₂ 1 1 := by linarith
    have hge : 0 ≤ T₂ 1 1 * (W : Matrix (Fin 2) (Fin 2) ℤ) 1 0 + T₂ 1 0 := by linarith
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · nlinarith
    · nlinarith
  rw [hw10] at e10
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e11, e10, h01, g01]

lemma card_reducedMatrices {ε : ℕ} (hε : 0 < ε) : (reducedMatrices ε).card = σ 1 ε := by
  rw [reducedMatrices, Finset.card_biUnion]
  · have : ∀ ad ∈ ε.divisorsAntidiagonal, ((Finset.range ad.2).image fun ξ : ℕ ↦
        (!![(ad.1 : ℤ), 0; (ξ : ℤ), (ad.2 : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ)).card = ad.2 := by
      intro ad _
      rw [Finset.card_image_of_injective, Finset.card_range]
      intro m n h
      have := congrFun (congrFun h 1) 0
      simpa using this
    rw [Finset.sum_congr rfl this, ArithmeticFunction.sigma_one_apply,
      Nat.sum_divisorsAntidiagonal' (fun _ y ↦ y)]
  · intro x hx y hy hxy
    rw [Finset.mem_coe, Nat.mem_divisorsAntidiagonal] at hx hy
    have hne : x.1 ≠ y.1 := by
      intro h1
      apply hxy
      have h2 : x.2 = y.2 := by
        have : x.1 * x.2 = x.1 * y.2 := by rw [hx.1, h1, hy.1]
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (fun h0 ↦ hε.ne' (by rw [← hx.1, h0]; simp))) this
      exact Prod.ext h1 h2
    rw [Function.onFun, Finset.disjoint_left]
    intro M hM hM'
    simp only [Finset.mem_image] at hM hM'
    obtain ⟨m, _, rfl⟩ := hM
    obtain ⟨n, _, hn⟩ := hM'
    have := congrFun (congrFun hn 0) 0
    simp at this
    exact hne this.symm

/-- **Eisenstein's reduction of integer matrices**. Hermite normal form, by
Bezout (`Int.gcd_eq_gcd_ab`) and division with remainder (`Int.emod_def`); the count is
`Nat.sum_divisorsAntidiagonal'` with `ArithmeticFunction.sigma_one_apply`. -/
@[kb "eisenstein1847"
  "Abhandlungen, transformation of elliptic functions"]
theorem eisensteinReduction : EisensteinReduction := by
  intro ε hε
  refine ⟨fun A hA ↦ ?_, fun T ↦ ⟨isReduced_of_mem, mem_of_isReduced⟩, card_reducedMatrices hε⟩
  obtain ⟨T, hT, hU⟩ := exists_reduced hε A hA
  exact ⟨T, ⟨hT, hU⟩, fun T' ⟨hT', U', hU'⟩ ↦ by
    obtain ⟨U, hU⟩ := hU
    exact reduced_unique hT' hT U' U (hU'.symm.trans hU)⟩

end ModularFormsKB.Historical.Eisenstein
