import ModularFormsKB.Historical.Jacobi.TripleProduct
import ModularFormsKB.Historical.Jacobi.Section66Proofs
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import ModularFormsKB.Citation
/-!
# Smith's chain of expressions for `∏ (1 + qᵐ)`

H. J. S. Smith, *Report on the Theory of Numbers*, Part VI, art. 129 (*Collected Mathematical Papers* I, 1894, p. 318),
quoting Euler and Jacobi: for `‖q‖ < 1`,

`∏ (1 + qᵐ) = ∏ 1/(1 - q^{2m-1}) = ∏ (1 - q^{2m})/(1 - qᵐ)
  = ∑ (-1)ᵐ q^{3m²+m} / ∑ (-1)ᵐ q^{(3m²+m)/2}
  = ∏ (1 + q^{3m-2})(1 + q^{3m-1})(1 - q^{3m}) / ∏ (1 - q^{6m-3})² (1 - q^{6m})
  = ∑ q^{(3m²+m)/2} / ∑ (-1)ᵐ q^{3m²}`,

products over `m ≥ 1` (written with the index shifted to start at `0`), sums over `m ∈ ℤ`. The first two
equalities are Euler's (distinct parts and odd parts); the third is Euler's pentagonal theorem applied to `q` and
`q²`; the last two are the triple product (`Jacobi.triple_product`) for the nomes `q^{3/2}` and `q³`.
-/

noncomputable section

open Complex

namespace ModularFormsKB.Historical.Smith

/-- `E(q) = ∏_{m ≥ 1} (1 + qᵐ)`. -/
def distinctPartsProduct (q : ℂ) : ℂ := ∏' m : ℕ, (1 + q ^ (m + 1))

/-- **Smith, Report, art. 129** (*Collected Papers* I, p. 318):
the six expressions for `∏ (1 + qᵐ)`, `‖q‖ < 1`. The exponents `(3m² + m)/2`, `3m² + m`, `3m²` are
nonnegative integers for `m ∈ ℤ` and are written with `Int.toNat`. -/
@[kb "smith1894" "Report, art. 129, p. 318"]
def SmithEulerProducts : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 →
    distinctPartsProduct q = ∏' m : ℕ, (1 - q ^ (2 * m + 1))⁻¹ ∧
    distinctPartsProduct q = ∏' m : ℕ, (1 - q ^ (2 * m + 2)) / (1 - q ^ (m + 1)) ∧
    distinctPartsProduct q =
      (∑' m : ℤ, (-1 : ℂ) ^ m.natAbs * q ^ (3 * m ^ 2 + m).toNat) /
        (∑' m : ℤ, (-1 : ℂ) ^ m.natAbs * q ^ ((3 * m ^ 2 + m) / 2).toNat) ∧
    distinctPartsProduct q =
      (∏' m : ℕ, (1 + q ^ (3 * m + 1)) * (1 + q ^ (3 * m + 2)) * (1 - q ^ (3 * m + 3))) /
        (∏' m : ℕ, (1 - q ^ (6 * m + 3)) ^ 2 * (1 - q ^ (6 * m + 6))) ∧
    distinctPartsProduct q =
      (∑' m : ℤ, q ^ ((3 * m ^ 2 + m) / 2).toNat) /
        (∑' m : ℤ, (-1 : ℂ) ^ m.natAbs * q ^ (3 * m ^ 2).toNat)

open ModularFormsKB.Historical.Jacobi

section Proofs

variable {q : ℂ}

private lemma smith_eq1 (hq : ‖q‖ < 1) :
    distinctPartsProduct q = ∏' m : ℕ, (1 - q ^ (2 * m + 1))⁻¹ := by
  have h := E_mul_O hq
  have h2 := (multipliable_one : Multipliable (fun _ : ℕ ↦ (1 : ℂ))).tprod_div₀ (mO hq) (ne_O hq)
  have h3 : ∏' m : ℕ, (1 - q ^ (2 * m + 1))⁻¹ = (∏' m : ℕ, (1 - q ^ (2 * m + 1)))⁻¹ := by
    simpa [one_div] using h2
  rw [h3]
  exact eq_inv_of_mul_eq_one_left h

private lemma smith_A_ne (hq : ‖q‖ < 1) : (∏' n : ℕ, (1 - q ^ (n + 1))) ≠ 0 :=
  eulerProd_ne_zero hq

private lemma smith_eq2 (hq : ‖q‖ < 1) :
    distinctPartsProduct q = ∏' m : ℕ, (1 - q ^ (2 * m + 2)) / (1 - q ^ (m + 1)) := by
  rw [(mEv hq).tprod_div₀ (mA hq) (smith_A_ne hq), eq_div_iff (smith_A_ne hq)]
  rw [mul_comm]
  exact AE_eq hq

private lemma pent_exp (m : ℤ) : ((3 * m ^ 2 + m) / 2).toNat = pentagonal (-m) := by
  rw [pentagonal_neg]
  congr 2
  ring

private lemma pent_two (m : ℤ) : (3 * m ^ 2 + m).toNat = 2 * ((3 * m ^ 2 + m) / 2).toNat := by
  have h := two_mul_natCast_pentagonal_neg m
  have e : 3 * m ^ 2 + m = ((2 * pentagonal (-m) : ℕ) : ℤ) := by
    push_cast; linear_combination (-1 : ℤ) * h
  rw [pent_exp m, e, Int.toNat_natCast]

private lemma pent_hasSum {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun m : ℤ ↦ (-1 : ℂ) ^ m.natAbs * x ^ ((3 * m ^ 2 + m) / 2).toNat)
      (∏' n : ℕ, (1 - x ^ (n + 1))) := by
  have h := hasSum_eulerFunction_pentagonal hx
  rw [eulerFunction_eq_tprod hx] at h
  have h' := (Equiv.neg ℤ).hasSum_iff.mpr h
  convert h' using 1
  funext m
  simp [Function.comp, pent_exp]

private lemma smith_eq3 (hq : ‖q‖ < 1) :
    distinctPartsProduct q =
      (∑' m : ℤ, (-1 : ℂ) ^ m.natAbs * q ^ (3 * m ^ 2 + m).toNat) /
        (∑' m : ℤ, (-1 : ℂ) ^ m.natAbs * q ^ ((3 * m ^ 2 + m) / 2).toNat) := by
  have hN := pent_hasSum (norm_sq_lt_one hq)
  have hD := pent_hasSum hq
  have hN' : ∑' m : ℤ, (-1 : ℂ) ^ m.natAbs * q ^ (3 * m ^ 2 + m).toNat =
      ∏' n : ℕ, (1 - q ^ (2 * n + 2)) := by
    rw [← tprod_congr (fun n : ℕ ↦ show 1 - (q ^ 2) ^ (n + 1) = 1 - q ^ (2 * n + 2) by ring),
      ← hN.tsum_eq]
    refine tsum_congr fun m ↦ ?_
    rw [pent_two, pow_mul]
  rw [hN', hD.tsum_eq, smith_eq2 hq, (mEv hq).tprod_div₀ (mA hq) (smith_A_ne hq)]

open Filter in
private lemma tprod_three {f : ℕ → ℂ} (hf : Multipliable f)
    (hg : Multipliable fun m : ℕ ↦ f (3 * m) * f (3 * m + 1) * f (3 * m + 2)) :
    ∏' n, f n = ∏' m : ℕ, f (3 * m) * f (3 * m + 1) * f (3 * m + 2) := by
  have h1 := hf.hasProd.tendsto_prod_nat
  have h2 := hg.hasProd.tendsto_prod_nat
  have h3 : Tendsto (fun M : ℕ ↦ 3 * M) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ show n ≤ 3 * n by omega) tendsto_id
  have h1' := h1.comp h3
  have e : ∀ M : ℕ, ∏ i ∈ Finset.range (3 * M), f i =
      ∏ m ∈ Finset.range M, f (3 * m) * f (3 * m + 1) * f (3 * m + 2) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [show 3 * (M + 1) = 3 * M + 1 + 1 + 1 by ring, Finset.prod_range_succ,
        Finset.prod_range_succ, Finset.prod_range_succ, ih, Finset.prod_range_succ]
      ring
  refine tendsto_nhds_unique h1' ?_
  simpa [Function.comp_def, e] using h2

private lemma smith_r (hq : ‖q‖ < 1) : ‖q ^ 3‖ < 1 := by
  rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)

private lemma smith_E_split (hq : ‖q‖ < 1) :
    distinctPartsProduct q = (∏' m : ℕ, (1 + q ^ (3 * m + 1))) * (∏' m : ℕ, (1 + q ^ (3 * m + 2))) *
      ∏' m : ℕ, (1 + q ^ (3 * m + 3)) := by
  have hr := smith_r hq
  have ha : Multipliable fun m : ℕ ↦ 1 + q ^ (3 * m + 1) :=
    (multipliable_one_add_mul_pow q (q ^ 3) hr).congr fun n ↦ by ring
  have hb : Multipliable fun m : ℕ ↦ 1 + q ^ (3 * m + 2) :=
    (multipliable_one_add_mul_pow (q ^ 2) (q ^ 3) hr).congr fun n ↦ by ring
  have hc : Multipliable fun m : ℕ ↦ 1 + q ^ (3 * m + 3) :=
    (multipliable_one_add_mul_pow (q ^ 3) (q ^ 3) hr).congr fun n ↦ by ring
  have hg : Multipliable fun m : ℕ ↦ (fun n : ℕ ↦ 1 + q ^ (n + 1)) (3 * m) *
      (fun n : ℕ ↦ 1 + q ^ (n + 1)) (3 * m + 1) * (fun n : ℕ ↦ 1 + q ^ (n + 1)) (3 * m + 2) :=
    ((ha.mul hb).mul hc).congr fun m ↦ by ring
  unfold distinctPartsProduct
  rw [tprod_three (f := fun n : ℕ ↦ 1 + q ^ (n + 1)) (mE hq) hg, ← tprod_mul_three ha hb hc]

private lemma smith_eq4 (hq : ‖q‖ < 1) :
    distinctPartsProduct q =
      (∏' m : ℕ, (1 + q ^ (3 * m + 1)) * (1 + q ^ (3 * m + 2)) * (1 - q ^ (3 * m + 3))) /
        (∏' m : ℕ, (1 - q ^ (6 * m + 3)) ^ 2 * (1 - q ^ (6 * m + 6))) := by
  have hr := smith_r hq
  have ha : Multipliable fun m : ℕ ↦ 1 + q ^ (3 * m + 1) :=
    (multipliable_one_add_mul_pow q (q ^ 3) hr).congr fun n ↦ by ring
  have hb : Multipliable fun m : ℕ ↦ 1 + q ^ (3 * m + 2) :=
    (multipliable_one_add_mul_pow (q ^ 2) (q ^ 3) hr).congr fun n ↦ by ring
  have hd : Multipliable fun m : ℕ ↦ 1 - q ^ (3 * m + 3) :=
    (mA hr).congr fun n ↦ by ring
  have hU : (∏' m : ℕ, (1 - q ^ (6 * m + 3)) ^ 2 * (1 - q ^ (6 * m + 6))) =
      (∏' n : ℕ, (1 - (q ^ 3) ^ (2 * n + 1))) * (∏' n : ℕ, (1 - (q ^ 3) ^ (2 * n + 1))) *
        ∏' n : ℕ, (1 - (q ^ 3) ^ (2 * n + 2)) := by
    rw [← tprod_mul_three (mO hr) (mO hr) (mEv hr)]
    exact tprod_congr fun n ↦ by ring
  have hT : (∏' m : ℕ, (1 + q ^ (3 * m + 1)) * (1 + q ^ (3 * m + 2)) * (1 - q ^ (3 * m + 3))) =
      (∏' m : ℕ, (1 + q ^ (3 * m + 1))) * (∏' m : ℕ, (1 + q ^ (3 * m + 2))) *
        ∏' m : ℕ, (1 - q ^ (3 * m + 3)) := tprod_mul_three ha hb hd
  have hc : (∏' m : ℕ, (1 + q ^ (3 * m + 3))) = ∏' n : ℕ, (1 + (q ^ 3) ^ (n + 1)) :=
    tprod_congr fun n ↦ by ring
  have hd' : (∏' m : ℕ, (1 - q ^ (3 * m + 3))) = ∏' n : ℕ, (1 - (q ^ 3) ^ (n + 1)) :=
    tprod_congr fun n ↦ by ring
  have h1 := E_mul_O hr
  have h2 := A_eq hr
  have hne : (∏' m : ℕ, (1 - q ^ (6 * m + 3)) ^ 2 * (1 - q ^ (6 * m + 6))) ≠ 0 := by
    rw [hU]
    exact mul_ne_zero (mul_ne_zero (ne_O hr) (ne_O hr)) (ne_Ev hr)
  rw [eq_div_iff hne, smith_E_split hq, hT, hU, hc, hd']
  set Pa := ∏' m : ℕ, (1 + q ^ (3 * m + 1))
  set Pb := ∏' m : ℕ, (1 + q ^ (3 * m + 2))
  set Pc := ∏' n : ℕ, (1 + (q ^ 3) ^ (n + 1))
  set Pd := ∏' n : ℕ, (1 - (q ^ 3) ^ (n + 1))
  set O := ∏' n : ℕ, (1 - (q ^ 3) ^ (2 * n + 1))
  set Ev := ∏' n : ℕ, (1 - (q ^ 3) ^ (2 * n + 2))
  linear_combination (Pa * Pb * O * Ev) * h1 - Pa * Pb * h2

private lemma smith_D (hq : ‖q‖ < 1) :
    HasSum (fun m : ℤ ↦ (-1 : ℂ) ^ m.natAbs * q ^ (3 * m ^ 2).toNat)
      (∏' m : ℕ, (1 - q ^ (6 * m + 3)) ^ 2 * (1 - q ^ (6 * m + 6))) := by
  have h := triple_product (q := q ^ 3) (z := -1) (smith_r hq) (by norm_num)
  convert h using 1
  · funext m
    have e : (3 * m ^ 2).toNat = 3 * m.natAbs ^ 2 := by
      have : (3 * m ^ 2 : ℤ) = ((3 * m.natAbs ^ 2 : ℕ) : ℤ) := by
        push_cast; rw [sq_abs]
      rw [this, Int.toNat_natCast]
    rw [e, neg_one_zpow_eq, pow_mul]; ring
  · exact tprod_congr fun n ↦ by ring

private lemma smith_N (hq : ‖q‖ < 1) :
    HasSum (fun m : ℤ ↦ q ^ ((3 * m ^ 2 + m) / 2).toNat)
      (∏' m : ℕ, (1 + q ^ (3 * m + 1)) * (1 + q ^ (3 * m + 2)) * (1 - q ^ (3 * m + 3))) := by
  by_cases hq0 : q = 0
  · subst hq0
    have h1 : (∏' m : ℕ, (1 + (0 : ℂ) ^ (3 * m + 1)) * (1 + (0 : ℂ) ^ (3 * m + 2)) *
        (1 - (0 : ℂ) ^ (3 * m + 3))) = 1 := by simp
    rw [h1]
    have := hasSum_single (f := fun m : ℤ ↦ (0 : ℂ) ^ ((3 * m ^ 2 + m) / 2).toNat) 0
      (fun b hb ↦ by
        have : ((3 * b ^ 2 + b) / 2).toNat ≠ 0 := by
          rw [pent_exp]
          intro h
          have : pentagonal (-b) = pentagonal (-(0 : ℤ)) := by rw [h]; simp [pentagonal]
          exact hb (by simpa using pentagonal_injective this)
        simp [this])
    simpa using this
  · obtain ⟨s, rfl⟩ := IsAlgClosed.exists_pow_nat_eq q (by norm_num : 0 < 2)
    have hsn : ‖s‖ < 1 := by
      by_contra hc
      rw [not_lt] at hc
      rw [norm_pow] at hq
      nlinarith
    have hs0 : s ≠ 0 := fun h ↦ hq0 (by simp [h])
    have h := triple_product (q := s ^ 3) (z := s) (by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hsn (by norm_num)) hs0
    convert h using 1
    · funext n
      rw [pent_exp]
      have e : (2 * pentagonal (-n) : ℤ) = 3 * n ^ 2 + n := by
        rw [two_mul_natCast_pentagonal_neg]; ring
      have h1 : (s ^ 3) ^ (n.natAbs ^ 2) = s ^ (3 * n ^ 2) := by
        rw [← pow_mul, ← zpow_natCast]
        congr 1
        push_cast
        rw [sq_abs]
      rw [h1, ← zpow_add₀ hs0, ← e, ← pow_mul, ← zpow_natCast]
      congr 1
    · exact tprod_congr fun n ↦ by field_simp; ring

private lemma smith_eq5 (hq : ‖q‖ < 1) :
    distinctPartsProduct q =
      (∑' m : ℤ, q ^ ((3 * m ^ 2 + m) / 2).toNat) /
        (∑' m : ℤ, (-1 : ℂ) ^ m.natAbs * q ^ (3 * m ^ 2).toNat) := by
  rw [(smith_N hq).tsum_eq, (smith_D hq).tsum_eq]
  exact smith_eq4 hq

end Proofs

/-- **Smith, Report, art. 129** (*Collected Papers* I, p. 318):
the chain of five equalities for `∏ (1 + qᵐ)`, `‖q‖ < 1`: Euler's two product forms, the quotient of two
pentagonal series (Mathlib's `eulerFunction_eq_tprod` at `q` and `q²`), and the quotients of the triple-product
series and products for the nomes `q^{3/2}` and `q³` (`Jacobi.triple_product`). -/
@[kb "smith1894" "Report, art. 129, p. 318"]
theorem smithEulerProducts : SmithEulerProducts := fun _ hq ↦
  ⟨smith_eq1 hq, smith_eq2 hq, smith_eq3 hq, smith_eq4 hq, smith_eq5 hq⟩

end ModularFormsKB.Historical.Smith
