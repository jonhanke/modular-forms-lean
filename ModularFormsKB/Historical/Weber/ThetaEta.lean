import ModularFormsKB.Historical.WeberHeegnerStark.Defs
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import ModularFormsKB.Citation
/-!
# Weber: the theta constants as `η` times squares of Weber's functions

Weber, *Elliptische Functionen und algebraische Zahlen* (1891), § 21, (9)–(10), p. 63 (also the
pilot row WA-05, § 29, p. 87; *Lehrbuch der Algebra* III (1908), § 24, p. 85 and § 34, p. 114). With
`q = e^{πiω}`:

  `ϑ₀₀ = η f²`, `ϑ₀₁ = η f₁²`, `ϑ₁₀ = η f₂²`,

where `η(ω) = q^{1/12} ∏ (1 - q^{2ν})`, `f(ω) = q^{-1/24} ∏ (1 + q^{2ν-1})`, `f₁(ω) = q^{-1/24} ∏ (1 - q^{2ν-1})`,
`f₂(ω) = √2 q^{1/12} ∏ (1 + q^{2ν})`.

Weber obtains (9) from the product formulas § 21 (1)–(5): `ϑ₀₀(v) = Q ∏ (1 + q^{2ν-1} e^{2πiv})(1 + q^{2ν-1} e^{-2πiv})`
with `Q` independent of `v` (two functions with the same zeros and multipliers, § 17), and `Q = q^{-1/12} η(ω)`
(§ 21 (6)–(8), from Jacobi's `ϑ₁₁' = π ϑ₀₀ ϑ₀₁ ϑ₁₀`). Together these are **Jacobi's triple product identity**
(Jacobi, *Fundamenta nova* 1829, § 64), which is neither in Mathlib nor in Tau Ceti. It is the named input
`JacobiTripleProduct` here; Weber's (9) is proved from it (`weberTheta00_eq`, `weberTheta01_eq`,
`weberTheta10_eq`). Proving the triple product is the loose end.

`f` and `f₂` are the definitions `weberF`, `weberF₂` of the Weber–Heegner–Stark pilot (via Mathlib's `η`);
`f₁ = η(ω/2)/η(ω)` is new here.
-/

noncomputable section

open Complex
open scoped Real

namespace ModularFormsKB.Historical.Weber

open ModularFormsKB.WeberHeegnerStark (weberF weberF₂)

/-- Weber's `ϑ₀₀(ω) = ∑ q^{n²}`, `q = e^{πiω}` (Weber 1891, § 16): Mathlib's `jacobiTheta₂ 0 ω`. -/
def weberTheta00 (ω : ℂ) : ℂ := jacobiTheta₂ 0 ω

/-- Weber's `ϑ₀₁(ω) = ∑ (-1)ⁿ q^{n²}`: `jacobiTheta₂ (1/2) ω`. -/
def weberTheta01 (ω : ℂ) : ℂ := jacobiTheta₂ (1 / 2) ω

/-- Weber's `ϑ₁₀(ω) = ∑ q^{(n + 1/2)²}`: `e^{πiω/4} jacobiTheta₂ (ω/2) ω`. -/
def weberTheta10 (ω : ℂ) : ℂ := cexp (π * I * ω / 4) * jacobiTheta₂ (ω / 2) ω

/-- Weber's `f₁(ω) = q^{-1/24} ∏ (1 - q^{2ν-1}) = η(ω/2)/η(ω)` (Weber 1891, § 21 (10)). -/
@[kb "weber1891" "§ 21, (10), p. 63"]
def weberF₁ (ω : ℂ) : ℂ := ModularForm.eta (ω / 2) / ModularForm.eta ω

/-- **Jacobi's triple product identity** (Jacobi, *Fundamenta nova* 1829, § 64; Weber 1891, § 21 (1)–(8)),
as a named input: for `Im τ > 0`, `q = e^{πiτ}`,
`∑ q^{n²} e^{2πinz} = ∏_{n ≥ 1} (1 - q^{2n})(1 + q^{2n-1} e^{2πiz})(1 + q^{2n-1} e^{-2πiz})`. -/
structure JacobiTripleProduct : Prop where
  /-- The identity, with `n` shifted to start at `0`. -/
  eq : ∀ z τ : ℂ, 0 < τ.im → jacobiTheta₂ z τ =
    ∏' n : ℕ, (1 - cexp (2 * π * I * (n + 1) * τ)) * (1 + cexp (π * I * (2 * n + 1) * τ + 2 * π * I * z)) *
      (1 + cexp (π * I * (2 * n + 1) * τ - 2 * π * I * z))

section Products

/-- `∏ (1 + c rⁿ)` converges for `‖r‖ < 1`. -/
lemma multipliable_one_add_mul_pow (c r : ℂ) (hr : ‖r‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 + c * r ^ n := by
  apply multipliable_one_add_of_summable
  simpa [norm_mul, norm_pow] using (summable_geometric_of_lt_one (norm_nonneg r) hr).mul_left ‖c‖

lemma norm_sq_lt_one {q : ℂ} (hq : ‖q‖ < 1) : ‖q ^ 2‖ < 1 := by
  rw [norm_pow]; nlinarith [norm_nonneg q]

lemma multipliable_one_add_pow_succ {r : ℂ} (hr : ‖r‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 + r ^ (n + 1) :=
  (multipliable_one_add_mul_pow r r hr).congr fun n ↦ by ring

lemma multipliable_one_sub_pow_odd {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 - q ^ (2 * n + 1) :=
  (multipliable_one_add_mul_pow (-q) (q ^ 2) (norm_sq_lt_one hq)).congr fun n ↦ by ring

lemma multipliable_one_add_pow_odd {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 + q ^ (2 * n + 1) :=
  (multipliable_one_add_mul_pow q (q ^ 2) (norm_sq_lt_one hq)).congr fun n ↦ by ring

/-- The Euler product split into odd and even factors (adapted from Tau Ceti,
`tprod_one_sub_pow_eq_tprod_one_sub_pow_odd_mul`). -/
lemma tprod_one_sub_pow_split {q : ℂ} (hq : ‖q‖ < 1) :
    ∏' n : ℕ, (1 - q ^ (n + 1)) =
      (∏' n : ℕ, (1 - q ^ (2 * n + 1))) * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) := by
  have hP₂ : Multipliable fun n : ℕ ↦ 1 - (q ^ 2) ^ (n + 1) :=
    ModularForm.multipliable_one_sub_pow (norm_sq_lt_one hq)
  rw [← tprod_even_mul_odd (f := fun n ↦ 1 - q ^ (n + 1))
    (multipliable_one_sub_pow_odd hq) (by simpa [← pow_mul, mul_add] using hP₂)]
  simp [← pow_mul, mul_add]

/-- `∏ (1 - (-q)ⁿ) = ∏ (1 + q^{2n-1}) ∏ (1 - q^{2n})`. -/
lemma tprod_one_sub_neg_pow {q : ℂ} (hq : ‖q‖ < 1) :
    ∏' n : ℕ, (1 - (-q) ^ (n + 1)) =
      (∏' n : ℕ, (1 + q ^ (2 * n + 1))) * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) := by
  have h := tprod_one_sub_pow_split (q := -q) (by simpa using hq)
  rw [h]
  congr 1
  · refine tprod_congr fun n ↦ ?_
    rw [pow_succ, pow_mul, neg_sq, ← pow_mul]; ring
  · simp

lemma tprod_one_sub_mul_one_add {r : ℂ} (hr : ‖r‖ < 1) :
    (∏' n : ℕ, (1 - r ^ (n + 1))) * ∏' n : ℕ, (1 + r ^ (n + 1)) =
      ∏' n : ℕ, (1 - (r ^ 2) ^ (n + 1)) := by
  rw [← (ModularForm.multipliable_one_sub_pow hr).tprod_mul (multipliable_one_add_pow_succ hr)]
  exact tprod_congr fun n ↦ by ring

/-- `η z = e^{2πiz/24} ∏ (1 - e^{2πiz})ⁿ`. -/
lemma eta_eq_cexp (z : ℂ) :
    ModularForm.eta z = cexp (2 * π * I * z / 24) * ∏' n : ℕ, (1 - cexp (2 * π * I * z) ^ (n + 1)) := by
  have h : ∏' n : ℕ, (1 - ModularForm.eta_q n z) = ∏' n : ℕ, (1 - cexp (2 * π * I * z) ^ (n + 1)) :=
    tprod_congr fun n ↦ by rw [ModularForm.eta_q_eq_pow]
  unfold ModularForm.eta
  rw [h]
  simp [Function.Periodic.qParam]

lemma cexp_eq_pow (x ω : ℂ) (k : ℕ) (h : x = k * (π * I * ω)) :
    cexp x = cexp (π * I * ω) ^ k := by
  rw [h, Complex.exp_nat_mul]

/-- Everything in terms of `q = e^{πiω}` and `s = e^{πiω/24}`. -/
lemma eta_eq_q {ω q s : ℂ} (hq : q = cexp (π * I * ω)) (hs : s = cexp (π * I * ω / 24)) :
    ModularForm.eta ω = s ^ 2 * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) := by
  rw [eta_eq_cexp, cexp_eq_pow (2 * π * I * ω) ω 2 (by push_cast; ring), ← hq,
    show cexp (2 * π * I * ω / 24) = s ^ 2 by
      rw [hs, ← Complex.exp_nat_mul]; congr 1; push_cast; ring]

lemma eta_half_shift_eq_q {ω q : ℂ} (hq : q = cexp (π * I * ω)) :
    ModularForm.eta ((ω + 1) / 2) =
      cexp (2 * π * I * ((ω + 1) / 2) / 24) * ∏' n : ℕ, (1 - (-q) ^ (n + 1)) := by
  rw [eta_eq_cexp]
  congr 3
  rw [show 2 * π * I * ((ω + 1) / 2) = π * I * ω + π * I by ring, Complex.exp_add,
    Complex.exp_pi_mul_I, ← hq]; ring_nf

lemma eta_half_eq_q {ω q s : ℂ} (hq : q = cexp (π * I * ω)) (hs : s = cexp (π * I * ω / 24)) :
    ModularForm.eta (ω / 2) = s * ∏' n : ℕ, (1 - q ^ (n + 1)) := by
  rw [eta_eq_cexp, show 2 * π * I * (ω / 2) = π * I * ω by ring, ← hq, hs]

lemma eta_two_eq_q {ω q s : ℂ} (hq : q = cexp (π * I * ω)) (hs : s = cexp (π * I * ω / 24)) :
    ModularForm.eta (2 * ω) = s ^ 4 * ∏' n : ℕ, (1 - ((q ^ 2) ^ 2) ^ (n + 1)) := by
  rw [eta_eq_cexp, cexp_eq_pow (2 * π * I * (2 * ω)) ω 4 (by push_cast; ring), ← hq,
    show cexp (2 * π * I * (2 * ω) / 24) = s ^ 4 by
      rw [hs, ← Complex.exp_nat_mul]; congr 1; push_cast; ring]
  rw [← pow_mul]

lemma cexp_odd_eq {ω q : ℂ} (hq : q = cexp (π * I * ω)) (n : ℕ) :
    cexp (π * I * (2 * n + 1) * ω) = q ^ (2 * n + 1) := by
  rw [hq, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma cexp_even_eq {ω q : ℂ} (hq : q = cexp (π * I * ω)) (n : ℕ) :
    cexp (2 * π * I * (n + 1) * ω) = (q ^ 2) ^ (n + 1) := by
  rw [hq, ← pow_mul, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma tprod_mul_three {a b c : ℕ → ℂ} (ha : Multipliable a) (hb : Multipliable b)
    (hc : Multipliable c) :
    ∏' n, (a n * b n * c n) = (∏' n, a n) * (∏' n, b n) * ∏' n, c n := by
  rw [(ha.mul hb).tprod_mul hc, ha.tprod_mul hb]

lemma norm_cexp_pi_mul_lt_one {ω : ℂ} (hω : 0 < ω.im) : ‖cexp (π * I * ω)‖ < 1 := by
  rw [Complex.norm_exp]
  rw [Real.exp_lt_one_iff]
  have : (π * I * ω).re = -(π * ω.im) := by simp
  rw [this]
  have := Real.pi_pos
  nlinarith

lemma weberF_eq_q {ω q s : ℂ} (hω : 0 < ω.im) (hq : q = cexp (π * I * ω))
    (hs : s = cexp (π * I * ω / 24)) :
    weberF ω = (∏' n : ℕ, (1 + q ^ (2 * n + 1))) / s := by
  have hqn : ‖q‖ < 1 := hq ▸ norm_cexp_pi_mul_lt_one hω
  have hη := ModularForm.eta_ne_zero hω
  have he := eta_eq_q hq hs
  have hP : ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) ≠ 0 := by
    rw [he] at hη; exact right_ne_zero_of_mul hη
  have hs0 : s ≠ 0 := by rw [hs]; exact Complex.exp_ne_zero _
  have hc : cexp (-(π * I) / 24) * cexp (2 * π * I * ((ω + 1) / 2) / 24) = s := by
    rw [← Complex.exp_add, hs]; congr 1; ring
  unfold weberF
  rw [eta_half_shift_eq_q hq, tprod_one_sub_neg_pow hqn, he, ← mul_assoc _ (cexp _), hc]
  field_simp

lemma weberF₁_eq_q {ω q s : ℂ} (hω : 0 < ω.im) (hq : q = cexp (π * I * ω))
    (hs : s = cexp (π * I * ω / 24)) :
    weberF₁ ω = (∏' n : ℕ, (1 - q ^ (2 * n + 1))) / s := by
  have hqn : ‖q‖ < 1 := hq ▸ norm_cexp_pi_mul_lt_one hω
  have hη := ModularForm.eta_ne_zero hω
  have he := eta_eq_q hq hs
  have hP : ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) ≠ 0 := by
    rw [he] at hη; exact right_ne_zero_of_mul hη
  have hs0 : s ≠ 0 := by rw [hs]; exact Complex.exp_ne_zero _
  unfold weberF₁
  rw [eta_half_eq_q hq hs, tprod_one_sub_pow_split hqn, he]
  field_simp

lemma weberF₂_eq_q {ω q s : ℂ} (hω : 0 < ω.im) (hq : q = cexp (π * I * ω))
    (hs : s = cexp (π * I * ω / 24)) :
    weberF₂ ω = ((√2 : ℝ) : ℂ) * (s ^ 2 * ∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) := by
  have hqn : ‖q‖ < 1 := hq ▸ norm_cexp_pi_mul_lt_one hω
  have hη := ModularForm.eta_ne_zero hω
  have he := eta_eq_q hq hs
  have hP : ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) ≠ 0 := by
    rw [he] at hη; exact right_ne_zero_of_mul hη
  have hs0 : s ≠ 0 := by rw [hs]; exact Complex.exp_ne_zero _
  unfold weberF₂
  rw [eta_two_eq_q hq hs, ← tprod_one_sub_mul_one_add (norm_sq_lt_one hqn), he]
  field_simp

end Products

/-- **Weber § 21 (9), first formula**: `ϑ₀₀ = η f²`, from the triple product. -/
@[kb "weber1891" "§ 21, (9), p. 63"]
theorem weberTheta00_eq (hJ : JacobiTripleProduct) {ω : ℂ} (hω : 0 < ω.im) :
    weberTheta00 ω = ModularForm.eta ω * weberF ω ^ 2 := by
  obtain ⟨q, hq⟩ : ∃ q, q = cexp (π * I * ω) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = cexp (π * I * ω / 24) := ⟨_, rfl⟩
  have hqn : ‖q‖ < 1 := hq ▸ norm_cexp_pi_mul_lt_one hω
  have hs0 : s ≠ 0 := by rw [hs]; exact Complex.exp_ne_zero _
  have hmP := ModularForm.multipliable_one_sub_pow (norm_sq_lt_one hqn)
  have hmA := multipliable_one_add_pow_odd hqn
  have hterm : ∀ n : ℕ, (1 - cexp (2 * π * I * (n + 1) * ω)) *
      (1 + cexp (π * I * (2 * n + 1) * ω + 2 * π * I * 0)) *
      (1 + cexp (π * I * (2 * n + 1) * ω - 2 * π * I * 0)) =
      (1 - (q ^ 2) ^ (n + 1)) * (1 + q ^ (2 * n + 1)) * (1 + q ^ (2 * n + 1)) := fun n ↦ by
    rw [mul_zero, add_zero, sub_zero, cexp_even_eq hq n, cexp_odd_eq hq n]
  rw [weberTheta00, hJ.eq 0 ω hω, tprod_congr hterm, tprod_mul_three hmP hmA hmA,
    eta_eq_q hq hs, weberF_eq_q hω hq hs]
  field_simp

/-- **Weber § 21 (9), second formula**: `ϑ₀₁ = η f₁²`, from the triple product. -/
@[kb "weber1891" "§ 21, (9), p. 63"]
theorem weberTheta01_eq (hJ : JacobiTripleProduct) {ω : ℂ} (hω : 0 < ω.im) :
    weberTheta01 ω = ModularForm.eta ω * weberF₁ ω ^ 2 := by
  obtain ⟨q, hq⟩ : ∃ q, q = cexp (π * I * ω) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = cexp (π * I * ω / 24) := ⟨_, rfl⟩
  have hqn : ‖q‖ < 1 := hq ▸ norm_cexp_pi_mul_lt_one hω
  have hs0 : s ≠ 0 := by rw [hs]; exact Complex.exp_ne_zero _
  have hmP := ModularForm.multipliable_one_sub_pow (norm_sq_lt_one hqn)
  have hmB := multipliable_one_sub_pow_odd hqn
  have hterm : ∀ n : ℕ, (1 - cexp (2 * π * I * (n + 1) * ω)) *
      (1 + cexp (π * I * (2 * n + 1) * ω + 2 * π * I * (1 / 2))) *
      (1 + cexp (π * I * (2 * n + 1) * ω - 2 * π * I * (1 / 2))) =
      (1 - (q ^ 2) ^ (n + 1)) * (1 - q ^ (2 * n + 1)) * (1 - q ^ (2 * n + 1)) := fun n ↦ by
    rw [show 2 * π * I * (1 / 2 : ℂ) = π * I by ring, Complex.exp_add, Complex.exp_sub,
      Complex.exp_pi_mul_I, cexp_even_eq hq n, cexp_odd_eq hq n]
    ring
  rw [weberTheta01, hJ.eq (1 / 2) ω hω, tprod_congr hterm, tprod_mul_three hmP hmB hmB,
    eta_eq_q hq hs, weberF₁_eq_q hω hq hs]
  field_simp

/-- **Weber § 21 (9), third formula**: `ϑ₁₀ = η f₂²`, from the triple product. -/
@[kb "weber1891" "§ 21, (9), p. 63"]
theorem weberTheta10_eq (hJ : JacobiTripleProduct) {ω : ℂ} (hω : 0 < ω.im) :
    weberTheta10 ω = ModularForm.eta ω * weberF₂ ω ^ 2 := by
  obtain ⟨q, hq⟩ : ∃ q, q = cexp (π * I * ω) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = cexp (π * I * ω / 24) := ⟨_, rfl⟩
  have hqn : ‖q‖ < 1 := hq ▸ norm_cexp_pi_mul_lt_one hω
  have hq2 := norm_sq_lt_one hqn
  have hmP := ModularForm.multipliable_one_sub_pow hq2
  have hmC := multipliable_one_add_pow_succ hq2
  have hmD : Multipliable fun n : ℕ ↦ 1 + (q ^ 2) ^ n :=
    (multipliable_one_add_mul_pow 1 (q ^ 2) hq2).congr fun n ↦ by ring
  have hterm : ∀ n : ℕ, (1 - cexp (2 * π * I * (n + 1) * ω)) *
      (1 + cexp (π * I * (2 * n + 1) * ω + 2 * π * I * (ω / 2))) *
      (1 + cexp (π * I * (2 * n + 1) * ω - 2 * π * I * (ω / 2))) =
      (1 - (q ^ 2) ^ (n + 1)) * (1 + (q ^ 2) ^ (n + 1)) * (1 + (q ^ 2) ^ n) := fun n ↦ by
    rw [show π * I * (2 * n + 1) * ω + 2 * π * I * (ω / 2) = 2 * π * I * (n + 1) * ω by ring,
      show π * I * (2 * n + 1) * ω - 2 * π * I * (ω / 2) = π * I * (2 * n) * ω by ring,
      cexp_even_eq hq n, show cexp (π * I * (2 * n) * ω) = (q ^ 2) ^ n by
        rw [hq, ← pow_mul, ← Complex.exp_nat_mul]; congr 1; push_cast; ring]
  have hD : ∏' n : ℕ, (1 + (q ^ 2) ^ n) = 2 * ∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1)) := by
    rw [tprod_eq_zero_mul' (f := fun n : ℕ ↦ 1 + (q ^ 2) ^ n) hmC]
    norm_num
  have h6 : cexp (π * I * ω / 4) = s ^ 6 := by
    rw [hs, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have h2 : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow]; simp
  rw [weberTheta10, hJ.eq (ω / 2) ω hω, tprod_congr hterm, tprod_mul_three hmP hmC hmD, hD,
    eta_eq_q hq hs, weberF₂_eq_q hω hq hs, h6, mul_pow, mul_pow, h2]
  ring

end ModularFormsKB.Historical.Weber
