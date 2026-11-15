import ModularFormsKB.Historical.Jacobi.TripleProduct

/-!
# Eisenstein: Gauss's triangular-number identity and the quasi-periodicity of `χ`

Eisenstein, *Mathematische Abhandlungen* (1847), page numbers as in that volume:

* Paper 5 (*Theorema*), p. 175: Gauss's
  identity `1 + x + x³ + x⁶ + x¹⁰ + ⋯ = (1 - x²)/(1 - x) · (1 - x⁴)/(1 - x³) · (1 - x⁶)/(1 - x⁵) ⋯`, i.e.
  `∑_{n ≥ 0} x^{n(n+1)/2} = ∏_{n ≥ 1} (1 - x^{2n})/(1 - x^{2n-1})` for `|x| < 1` (`gauss_triangular`).
* *Beiträge* VI (Crelle 35), § 4, p. 277: for the theta-type product
  `χ(ζ) = (ζ - ζ⁻¹) ∏_{n ≥ 1} (1 - q^{2n} ζ²)(1 - q^{2n} ζ⁻²)` of formula (V.) and every integer `h`,
  `χ(q^h z) = (-1)^h q^{-h²} z^{-2h} χ(z)` (`eisensteinChi_qpow_mul`).

Both are proved here: Gauss's identity from Jacobi's triple product (`Historical.Jacobi.triple_product`),
`χ` directly from its product.
-/

noncomputable section

open Complex

namespace ModularFormsKB.Historical.Eisenstein

section GaussAux

lemma mult_one_add_pow_succ {r : ℂ} (hr : ‖r‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 + r ^ (n + 1) :=
  (Historical.Jacobi.multipliable_one_add_mul_pow r r hr).congr fun n ↦ by ring

lemma mult_one_add_pow {r : ℂ} (hr : ‖r‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 + r ^ n :=
  (Historical.Jacobi.multipliable_one_add_mul_pow 1 r hr).congr fun n ↦ by ring

lemma mult_one_sub_pow_odd {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 - q ^ (2 * n + 1) :=
  (Historical.Jacobi.multipliable_one_add_mul_pow (-q) (q ^ 2)
    (Historical.Jacobi.norm_sq_lt_one hq)).congr fun n ↦ by ring

lemma tprod_split_aux {q : ℂ} (hq : ‖q‖ < 1) :
    ∏' n : ℕ, (1 - q ^ (n + 1)) =
      (∏' n : ℕ, (1 - q ^ (2 * n + 1))) * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) := by
  have hP₂ : Multipliable fun n : ℕ ↦ 1 - (q ^ 2) ^ (n + 1) :=
    ModularForm.multipliable_one_sub_pow (Historical.Jacobi.norm_sq_lt_one hq)
  rw [← tprod_even_mul_odd (f := fun n ↦ 1 - q ^ (n + 1))
    (mult_one_sub_pow_odd hq) (by simpa [← pow_mul, mul_add] using hP₂)]
  simp [← pow_mul, mul_add]

lemma tprod_one_sub_mul_one_add_aux {r : ℂ} (hr : ‖r‖ < 1) :
    (∏' n : ℕ, (1 - r ^ (n + 1))) * ∏' n : ℕ, (1 + r ^ (n + 1)) =
      ∏' n : ℕ, (1 - (r ^ 2) ^ (n + 1)) := by
  rw [← (ModularForm.multipliable_one_sub_pow hr).tprod_mul (mult_one_add_pow_succ hr)]
  exact tprod_congr fun n ↦ by ring

lemma mult_gauss_quot {x : ℂ} (hx : ‖x‖ < 1) :
    Multipliable fun n : ℕ ↦ (1 - x ^ (2 * n + 2)) / (1 - x ^ (2 * n + 1)) := by
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hpos : 0 < 1 - ‖x‖ := by linarith
  have hden : ∀ n : ℕ, 1 - ‖x‖ ≤ ‖1 - x ^ (2 * n + 1)‖ := fun n ↦ by
    have h1 := abs_norm_sub_norm_le (1 : ℂ) (x ^ (2 * n + 1))
    rw [norm_one, norm_pow] at h1
    have h2 : ‖x‖ ^ (2 * n + 1) ≤ ‖x‖ := pow_le_of_le_one hx0 hx.le (by omega)
    have := le_abs_self (1 - ‖x‖ ^ (2 * n + 1))
    linarith
  have hne : ∀ n : ℕ, 1 - x ^ (2 * n + 1) ≠ 0 := fun n h ↦ by
    have := hden n
    rw [h, norm_zero] at this
    linarith
  have hd : ∀ n : ℕ, (1 - x ^ (2 * n + 2)) / (1 - x ^ (2 * n + 1)) =
      1 + (x ^ (2 * n + 1) * (1 - x)) / (1 - x ^ (2 * n + 1)) := fun n ↦ by
    have := hne n
    field_simp
    ring
  simp_rw [hd]
  apply multipliable_one_add_of_summable
  refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    ((summable_geometric_of_lt_one hx0 hx).mul_left (2 / (1 - ‖x‖)))
  rw [norm_div, norm_mul, norm_pow]
  have h1 : ‖x‖ ^ (2 * n + 1) ≤ ‖x‖ ^ n := pow_le_pow_of_le_one hx0 hx.le (by omega)
  have h2 : ‖1 - x‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) x
    rw [norm_one] at this
    linarith
  calc ‖x‖ ^ (2 * n + 1) * ‖1 - x‖ / ‖1 - x ^ (2 * n + 1)‖
      ≤ (‖x‖ ^ n * 2) / (1 - ‖x‖) :=
        div_le_div₀ (by positivity) (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) hpos (hden n)
    _ = _ := by ring

end GaussAux

/-- **Gauss's identity** (Eisenstein, *Abhandlungen* 1847, paper 5, p. 175): for
`|x| < 1`, `∑_{n ≥ 0} x^{n(n+1)/2} = ∏_{n ≥ 1} (1 - x^{2n})/(1 - x^{2n-1})` (product index shifted to start at
`0`). -/
@[kb "eisenstein1847" "paper 5 (Theorema), p. 175"]
theorem gauss_triangular {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ ↦ x ^ (n * (n + 1) / 2))
      (∏' n : ℕ, (1 - x ^ (2 * n + 2)) / (1 - x ^ (2 * n + 1))) := by
  by_cases hx0 : x = 0
  · subst hx0
    have h1 : ∏' n : ℕ, (1 - (0 : ℂ) ^ (2 * n + 2)) / (1 - (0 : ℂ) ^ (2 * n + 1)) = 1 := by
      simp
    rw [h1]
    have := hasSum_single (f := fun n : ℕ ↦ (0 : ℂ) ^ (n * (n + 1) / 2)) 0 (fun b hb ↦ by
      have : 0 < b * (b + 1) / 2 := Nat.div_pos (by nlinarith [Nat.pos_of_ne_zero hb]) (by norm_num)
      exact zero_pow this.ne')
    simpa using this
  obtain ⟨q, hq2⟩ : ∃ q : ℂ, q ^ 2 = x := ⟨x ^ ((2 : ℕ)⁻¹ : ℂ), Complex.cpow_nat_inv_pow x two_ne_zero⟩
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hx0
    rw [← hq2]; simp
  have hqn : ‖q‖ < 1 := by
    have : ‖q‖ ^ 2 < 1 := by rw [← norm_pow, hq2]; exact hx
    nlinarith [norm_nonneg q]
  have hJ := Historical.Jacobi.triple_product hqn hq0
  -- the sum side
  have hsum := hJ.summable
  have e : ∀ n : ℕ, x ^ (n * (n + 1) / 2) = q ^ (n * (n + 1)) := fun n ↦ by
    rw [← hq2, ← pow_mul, Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)]
  have hf0 : ∀ n : ℕ, q ^ ((n : ℤ).natAbs ^ 2) * q ^ (n : ℤ) = x ^ (n * (n + 1) / 2) := fun n ↦ by
    rw [e, Int.natAbs_natCast, zpow_natCast, ← pow_add]; congr 1; ring
  have hf1 : ∀ n : ℕ, q ^ ((-((n : ℤ) + 1)).natAbs ^ 2) * q ^ (-((n : ℤ) + 1)) =
      x ^ (n * (n + 1) / 2) := fun n ↦ by
    have : q ^ (n + 1) ≠ 0 := pow_ne_zero _ hq0
    rw [show (-((n : ℤ) + 1)).natAbs = n + 1 by omega, zpow_neg,
      show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, e]
    field_simp
    ring
  have hg : Summable fun n : ℕ ↦ x ^ (n * (n + 1) / 2) := by
    have := hsum.comp_injective (i := fun n : ℕ ↦ (n : ℤ)) Nat.cast_injective
    exact this.congr fun n ↦ hf0 n
  have htot : ∑' k : ℤ, q ^ (k.natAbs ^ 2) * q ^ k = 2 * ∑' n : ℕ, x ^ (n * (n + 1) / 2) := by
    rw [Historical.Jacobi.tsum_int_pair hsum, ← tsum_mul_left]
    refine tsum_congr fun n ↦ ?_
    rw [hf0, hf1]; ring
  have hP := hJ.tsum_eq
  rw [htot] at hP
  -- the product side
  have hx2 : ‖x ^ 2‖ < 1 := Historical.Jacobi.norm_sq_lt_one hx
  have hA : Multipliable fun n : ℕ ↦ 1 - x ^ (n + 1) := ModularForm.multipliable_one_sub_pow hx
  have hB := mult_one_add_pow_succ hx
  have hC := mult_one_add_pow hx
  have hterm : ∀ n : ℕ, (1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 1) * q) * (1 + q ^ (2 * n + 1) / q) =
      (1 - x ^ (n + 1)) * (1 + x ^ (n + 1)) * (1 + x ^ n) := fun n ↦ by
    rw [← hq2]
    have : q ^ (2 * n + 1) / q = (q ^ 2) ^ n := by field_simp; ring
    rw [this]; ring
  rw [tprod_congr hterm, Historical.Jacobi.tprod_mul_three hA hB hC] at hP
  have hC' : ∏' n : ℕ, (1 + x ^ n) = 2 * ∏' n : ℕ, (1 + x ^ (n + 1)) := by
    rw [tprod_eq_zero_mul' (f := fun n : ℕ ↦ 1 + x ^ n) hB]
    norm_num
  rw [hC'] at hP
  set A := ∏' n : ℕ, (1 - x ^ (n + 1)) with hAdef
  set B := ∏' n : ℕ, (1 + x ^ (n + 1)) with hBdef
  set O := ∏' n : ℕ, (1 - x ^ (2 * n + 1)) with hOdef
  set E := ∏' n : ℕ, (1 - (x ^ 2) ^ (n + 1)) with hEdef
  have hAB : A * B = E := tprod_one_sub_mul_one_add_aux hx
  have hAO : A = O * E := tprod_split_aux hx
  have hE0 : E ≠ 0 := Historical.Jacobi.eulerProd_ne_zero hx2
  have hOB : O * B = 1 := by
    apply mul_left_cancel₀ hE0
    linear_combination hAB - B * hAO
  have hO0 : O ≠ 0 := left_ne_zero_of_mul_eq_one hOB
  have hQ := mult_gauss_quot hx
  have hne : ∀ n : ℕ, 1 - x ^ (2 * n + 1) ≠ 0 := fun n h ↦ by
    have h1 : x ^ (2 * n + 1) = 1 := by linear_combination -h
    have h2 : ‖x‖ ^ (2 * n + 1) < 1 := pow_lt_one₀ (norm_nonneg _) hx (by omega)
    rw [← norm_pow, h1, norm_one] at h2
    exact lt_irrefl _ h2
  have hQO : (∏' n : ℕ, (1 - x ^ (2 * n + 2)) / (1 - x ^ (2 * n + 1))) * O = E := by
    rw [hOdef, ← hQ.tprod_mul (mult_one_sub_pow_odd hx)]
    exact tprod_congr fun n ↦ by rw [div_mul_cancel₀ _ (hne n)]; ring
  have hfinal : (∏' n : ℕ, (1 - x ^ (2 * n + 2)) / (1 - x ^ (2 * n + 1))) = E * B := by
    linear_combination (-(∏' n : ℕ, (1 - x ^ (2 * n + 2)) / (1 - x ^ (2 * n + 1)))) * hOB + B * hQO
  rw [hfinal]
  have : ∑' n : ℕ, x ^ (n * (n + 1) / 2) = E * B := by
    linear_combination (1 / 2 : ℂ) * hP + B * hAB
  rw [← this]
  exact hg.hasSum

/-- Eisenstein's theta-type product (formula (V.) of *Beiträge* VI, § 4):
`χ(ζ) = (ζ - ζ⁻¹) ∏_{n ≥ 1} (1 - q^{2n} ζ²)(1 - q^{2n} ζ⁻²)` (index shifted to start at `0`). -/
@[kb "eisenstein1847" "Beiträge VI, § 4, (V.), p. 275"]
def eisensteinChi (q ζ : ℂ) : ℂ :=
  (ζ - ζ⁻¹) * ∏' n : ℕ, (1 - q ^ (2 * n + 2) * ζ ^ 2) * (1 - q ^ (2 * n + 2) * ζ⁻¹ ^ 2)

/-- **The quasi-periodicity of `χ`** (Eisenstein, *Beiträge* VI, § 4, (VII.), p. 277): for `0 < |q| < 1`, `z ≠ 0` and every integer `h`,
`χ(q^h z) = (-1)^h q^{-h²} z^{-2h} χ(z)`. -/
@[kb "eisenstein1847" "Beiträge VI, § 4, (VII.), p. 277"]
theorem eisensteinChi_qpow_mul {q z : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hz : z ≠ 0) (h : ℤ) :
    eisensteinChi q (q ^ h * z) = (-1) ^ h * q ^ (-h ^ 2) * z ^ (-2 * h) * eisensteinChi q z := by
  have hq2 : ‖q‖ ^ 2 < 1 := by nlinarith [norm_nonneg q]
  have M : ∀ c : ℂ, Multipliable fun n : ℕ ↦ 1 - q ^ (2 * n) * c := fun c ↦
    (Historical.Jacobi.multipliable_one_add_mul_pow (-c) (q ^ 2)
      (Historical.Jacobi.norm_sq_lt_one hq)).congr fun n ↦ by ring
  -- the one-step relation
  have step : ∀ w : ℂ, w ≠ 0 →
      eisensteinChi q (q * w) = -q⁻¹ * w⁻¹ ^ 2 * eisensteinChi q w := by
    intro w hw
    have hA := M (q ^ 2 * w ^ 2)
    have hB := M (q ^ 2 * w⁻¹ ^ 2)
    have hW := M (w⁻¹ ^ 2)
    have hA1 : Multipliable fun n : ℕ ↦ 1 - q ^ (2 * (n + 1)) * (q ^ 2 * w ^ 2) :=
      (M (q ^ 4 * w ^ 2)).congr fun n ↦ by ring
    have hB1 : Multipliable fun n : ℕ ↦ 1 - q ^ (2 * (n + 1)) * (q ^ 2 * w⁻¹ ^ 2) :=
      (M (q ^ 4 * w⁻¹ ^ 2)).congr fun n ↦ by ring
    have hW1 : Multipliable fun n : ℕ ↦ 1 - q ^ (2 * (n + 1)) * w⁻¹ ^ 2 :=
      (M (q ^ 2 * w⁻¹ ^ 2)).congr fun n ↦ by ring
    have hP : ∏' n : ℕ, (1 - q ^ (2 * n + 2) * w ^ 2) * (1 - q ^ (2 * n + 2) * w⁻¹ ^ 2) =
        (∏' n : ℕ, (1 - q ^ (2 * n) * (q ^ 2 * w ^ 2))) *
          ∏' n : ℕ, (1 - q ^ (2 * n) * (q ^ 2 * w⁻¹ ^ 2)) := by
      rw [← hA.tprod_mul hB]
      exact tprod_congr fun n ↦ by ring
    have hc : ((q * w)⁻¹) ^ 2 * q ^ 2 = w⁻¹ ^ 2 := by
      rw [mul_inv]; field_simp
    have hPq : ∏' n : ℕ, (1 - q ^ (2 * n + 2) * (q * w) ^ 2) *
        (1 - q ^ (2 * n + 2) * (q * w)⁻¹ ^ 2) =
        (∏' n : ℕ, (1 - q ^ (2 * (n + 1)) * (q ^ 2 * w ^ 2))) *
          ∏' n : ℕ, (1 - q ^ (2 * n) * w⁻¹ ^ 2) := by
      rw [← hA1.tprod_mul hW]
      refine tprod_congr fun n ↦ ?_
      have : q ^ (2 * n + 2) * (q * w)⁻¹ ^ 2 = q ^ (2 * n) * w⁻¹ ^ 2 := by
        rw [← hc]; ring
      rw [this]; ring
    have hA0 := tprod_eq_zero_mul' (f := fun n : ℕ ↦ 1 - q ^ (2 * n) * (q ^ 2 * w ^ 2)) hA1
    have hW0 := tprod_eq_zero_mul' (f := fun n : ℕ ↦ 1 - q ^ (2 * n) * w⁻¹ ^ 2) hW1
    have hBW : ∏' n : ℕ, (1 - q ^ (2 * (n + 1)) * w⁻¹ ^ 2) =
        ∏' n : ℕ, (1 - q ^ (2 * n) * (q ^ 2 * w⁻¹ ^ 2)) :=
      tprod_congr fun n ↦ by ring
    unfold eisensteinChi
    rw [hP, hPq, hA0, hW0, hBW]
    simp only [mul_zero, pow_zero, one_mul]
    have : q ^ 2 ≠ 0 := pow_ne_zero _ hq0
    field_simp
    ring
  have zq : ∀ k : ℤ, ((q ^ k)⁻¹) ^ 2 = q ^ (-2 * k) := fun k ↦ by
    rw [← zpow_neg, ← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
  induction h using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have e : q ^ ((i : ℤ) + 1) * z = q * (q ^ (i : ℤ) * z) := by
      rw [zpow_add_one₀ hq0]; ring
    have hw : q ^ (i : ℤ) * z ≠ 0 := mul_ne_zero (zpow_ne_zero _ hq0) hz
    rw [e, step _ hw, ih, mul_inv, mul_pow, zq]
    have e1 : (-1 : ℂ) ^ ((i : ℤ) + 1) = (-1) ^ (i : ℤ) * (-1) := zpow_add_one₀ hm1 _
    have e2 : q ^ (-((i : ℤ) + 1) ^ 2) = q ^ (-(i : ℤ) ^ 2) * q ^ (-2 * (i : ℤ)) * q⁻¹ := by
      rw [← zpow_neg_one, ← zpow_add₀ hq0, ← zpow_add₀ hq0]; congr 1; ring
    have e3 : z ^ (-2 * ((i : ℤ) + 1)) = z ^ (-2 * (i : ℤ)) * z⁻¹ ^ 2 := by
      rw [← zpow_natCast, ← zpow_neg_one, ← zpow_mul, ← zpow_add₀ hz]; congr 1; push_cast; ring
    rw [e1, e2, e3]
    ring
  | pred i ih =>
    generalize -(i : ℤ) = h at ih ⊢
    have hk : q ^ (h - 1) * z ≠ 0 := mul_ne_zero (zpow_ne_zero _ hq0) hz
    have e0 : q ^ h = q ^ (h - 1) * q := by
      have := zpow_add_one₀ hq0 (h - 1)
      rwa [sub_add_cancel] at this
    have e : q * (q ^ (h - 1) * z) = q ^ h * z := by rw [e0]; ring
    have key : eisensteinChi q (q ^ (h - 1) * z) =
        -q * (q ^ (h - 1) * z) ^ 2 * eisensteinChi q (q * (q ^ (h - 1) * z)) := by
      rw [step _ hk]
      field_simp
    rw [key, e, ih]
    have e1 : (-1 : ℂ) ^ h = (-1) ^ (h - 1) * (-1) := by
      have := zpow_add_one₀ hm1 (h - 1)
      rwa [sub_add_cancel] at this
    have e2 : q ^ (-h ^ 2) = q ^ (-(h - 1) ^ 2) * q ^ (-2 * (h - 1)) * q⁻¹ := by
      rw [← zpow_neg_one, ← zpow_add₀ hq0, ← zpow_add₀ hq0]; congr 1; ring
    have e3 : z ^ (-2 * h) = z ^ (-2 * (h - 1)) * z⁻¹ ^ 2 := by
      rw [← zpow_natCast, ← zpow_neg_one, ← zpow_mul, ← zpow_add₀ hz]; congr 1; push_cast; ring
    have e4 : (q ^ (h - 1)) ^ 2 = q ^ (2 * (h - 1)) := by
      rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
    have hab : q ^ (2 * (h - 1)) * q ^ (-2 * (h - 1)) = 1 := by
      rw [← zpow_add₀ hq0]; simp
    have hq1 : q * q⁻¹ = 1 := mul_inv_cancel₀ hq0
    have hz1 : z ^ 2 * z⁻¹ ^ 2 = 1 := by field_simp
    rw [mul_pow, e4, e1, e2, e3]
    linear_combination
      ((-1 : ℂ) ^ (h - 1) * q ^ (-(h - 1) ^ 2) * z ^ (-2 * (h - 1)) * eisensteinChi q z) *
        (z ^ 2 * z⁻¹ ^ 2 * (q ^ (2 * (h - 1)) * q ^ (-2 * (h - 1))) * hq1 +
          (q ^ (2 * (h - 1)) * q ^ (-2 * (h - 1))) * hz1 + hab)

end ModularFormsKB.Historical.Eisenstein
