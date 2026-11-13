import ModularFormsKB.Historical.WeberHeegnerStark.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Numerical enclosure of `f₂(τ)²⁴` and the six singular values of `j`

With `q = e^{2πiτ}` and `A = |q|`, Weber's `f₂(τ)²⁴ = 4096 q ∏_{n ≥ 1} (1 + qⁿ)²⁴`; here it is
obtained from Mathlib's eta product as `4096 · q · (P(q²) / P(q))²⁴` with `P(w) = ∏ (1 - w^(n+1))`
(`norm_weberF₂_pow_24_eq`). The finite-product estimate `Finset.norm_prod_one_add_sub_one_le`
passes to the limit to give `|P(w) - 1| ≤ a / (1 - 2a)` for `|w| ≤ a` (`norm_etaProd_sub_one_le`),
hence the enclosure `4096 A L(α) ≤ |f₂²⁴| ≤ 4096 A U(α)` for `A ≤ α < 1/3`
(`le_norm_weberF₂_pow_24`, `norm_weberF₂_pow_24_le`).

Weber's cubic `(x + 16)³ = j x` (taken as a hypothesis) and `j = v³` then pin down `A = e^{-π√n}`
to within a few percent, by certified rational bounds on `π`, `e` and square roots. The closest call
is `n = 163` against `n = 162`.

## Main results

* `weberF₂_ne_zero`, `norm_weberF₂_pow_24_lt_one`.
* `mem_of_kleinJ_eq_pow_three`: if `Im τ = √n / 2` with `n ≥ 3`, Weber's cubic holds and
  `j(τ) = v³` with `v ∈ {0, -32, -96, -960, -5280, -640320}`, then `n ∈ {3, 11, 19, 43, 67, 163}`.

## References

* H. M. Stark, *On the "gap" in a theorem of Heegner*, J. Number Theory 1 (1969), 16–27.
* The enclosure argument is ported from Tau Ceti
  (`TauCeti/NumberTheory/ClassNumberOne/SingularValue.lean` and the Siegel-function bounds it uses,
  snapshot d2083f0f, Apache 2.0, The Tau Ceti contributors).
-/

noncomputable section

open ModularForm Complex
open UpperHalfPlane hiding I
open scoped Real

namespace ModularFormsKB.WeberHeegnerStark

/-- `q = e^{2πiz}`. -/
abbrev qOf (z : ℂ) : ℂ := cexp (2 * π * I * z)

/-- `P(w) = ∏_{n ≥ 1} (1 - wⁿ)`. -/
def etaProd (w : ℂ) : ℂ := ∏' n : ℕ, (1 - w ^ (n + 1))

private lemma tprod_eta_q_eq (z : ℂ) : (∏' n : ℕ, (1 - eta_q n z)) = etaProd (qOf z) := by
  unfold etaProd; simp only [eta_q_eq_pow]

private lemma eta_pow_24 (z : ℂ) :
    ModularForm.eta z ^ 24 = qOf z * etaProd (qOf z) ^ 24 := by
  have h2 : (Function.Periodic.qParam 24 z) ^ 24 = qOf z := by
    rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [ModularForm.eta, mul_pow, tprod_eta_q_eq, h2]

private lemma etaProd_ne_zero (τ : ℍ) : etaProd (qOf τ) ≠ 0 := by
  rw [← tprod_eta_q_eq]; exact eta_tprod_ne_zero τ.2

private lemma two_mul_mem (τ : ℍ) : (2 * (τ : ℂ)) ∈ upperHalfPlaneSet := by
  show 0 < (2 * (τ : ℂ)).im
  simpa using τ.im_pos

theorem weberF₂_ne_zero (τ : ℍ) : weberF₂ τ ≠ 0 := by
  unfold weberF₂
  exact div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by norm_num)).ne')
    (eta_ne_zero (two_mul_mem τ))) (eta_ne_zero τ.2)

/-- Exact formula for the norm of `f₂(τ)²⁴`. -/
theorem norm_weberF₂_pow_24_eq (τ : ℍ) :
    ‖weberF₂ τ ^ 24‖ = 4096 * ‖qOf τ‖ * (‖etaProd (qOf τ ^ 2)‖ / ‖etaProd (qOf τ)‖) ^ 24 := by
  have hq0 : ‖qOf (τ : ℂ)‖ ≠ 0 := norm_ne_zero_iff.2 (Complex.exp_ne_zero _)
  have hP : ‖etaProd (qOf (τ : ℂ))‖ ≠ 0 := norm_ne_zero_iff.2 (etaProd_ne_zero τ)
  have h2 : qOf (2 * (τ : ℂ)) = qOf τ ^ 2 := by
    unfold qOf; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hs : (((√2 : ℝ) : ℂ)) ^ 24 = 4096 := by
    rw [← Complex.ofReal_pow, show (24 : ℕ) = 2 * 12 from rfl, pow_mul, Real.sq_sqrt (by norm_num)]
    norm_num
  have h1 : weberF₂ τ ^ 24 =
      4096 * (qOf τ ^ 2 * etaProd (qOf τ ^ 2) ^ 24) / (qOf τ * etaProd (qOf τ) ^ 24) := by
    unfold weberF₂
    rw [div_pow, mul_pow, hs, eta_pow_24 (2 * (τ : ℂ)), eta_pow_24 (τ : ℂ), h2]
  have h4 : ‖(4096 : ℂ)‖ = 4096 := by norm_num
  rw [h1, norm_div, norm_mul, norm_mul, norm_mul]
  simp only [norm_pow]
  rw [h4, div_pow]
  field_simp

/-! ### The tail of the eta product -/

private lemma norm_etaProd_sub_one_le {w : ℂ} {a : ℝ} (hw : ‖w‖ ≤ a) (ha : 2 * a < 1) :
    ‖etaProd w - 1‖ ≤ a / (1 - 2 * a) := by
  have ha0 : 0 ≤ a := (norm_nonneg w).trans hw
  have ha1 : a < 1 := by linarith
  have hmult : Multipliable fun n : ℕ ↦ 1 - w ^ (n + 1) :=
    multipliable_one_sub_pow (hw.trans_lt ha1)
  have hs : HasSum (fun i : ℕ ↦ a ^ (i + 1)) (a / (1 - a)) := by
    have := (hasSum_geometric_of_lt_one ha0 ha1).mul_left a
    simpa [pow_succ, mul_comm, div_eq_mul_inv] using this
  have hs1 : a / (1 - a) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hfin : ∀ N : ℕ, ‖∏ i ∈ Finset.range N, (1 - w ^ (i + 1)) - 1‖ ≤ a / (1 - 2 * a) := by
    intro N
    have h := Finset.norm_prod_one_add_sub_one_le (Finset.range N) (fun i ↦ -w ^ (i + 1))
    simp only [← sub_eq_add_neg, norm_neg, norm_pow] at h
    refine h.trans ?_
    have h1 : ∑ i ∈ Finset.range N, ‖w‖ ^ (i + 1) ≤ a / (1 - a) :=
      (Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) hw _).trans
        (sum_le_hasSum _ (fun i _ ↦ by positivity) hs)
    have h2 := Real.exp_le_exp.2 h1
    have h3 : Real.exp (a / (1 - a)) ≤ 1 / (1 - a / (1 - a)) := by
      have e := Real.add_one_le_exp (-(a / (1 - a)))
      have e2 : Real.exp (a / (1 - a)) * Real.exp (-(a / (1 - a))) = 1 := by
        rw [← Real.exp_add]; simp
      rw [le_div_iff₀ (by linarith)]
      nlinarith [Real.exp_pos (a / (1 - a)), Real.exp_pos (-(a / (1 - a)))]
    have h4 : 1 / (1 - a / (1 - a)) - 1 = a / (1 - 2 * a) := by
      have n1 : (1 - a) ≠ 0 := by linarith
      have n2 : (1 - 2 * a) ≠ 0 := by linarith
      have e : 1 - a / (1 - a) = (1 - 2 * a) / (1 - a) := by field_simp; ring
      rw [e, one_div_div, div_sub_one n2]
      congr 1; ring
    linarith
  have ht := (hmult.hasProd.tendsto_prod_nat.sub_const 1).norm
  exact le_of_tendsto' ht hfin

private lemma norm_etaProd_bounds {w : ℂ} {a : ℝ} (hw : ‖w‖ ≤ a) (ha : 2 * a < 1) :
    1 - a / (1 - 2 * a) ≤ ‖etaProd w‖ ∧ ‖etaProd w‖ ≤ 1 + a / (1 - 2 * a) := by
  have h := (abs_norm_sub_norm_le (etaProd w) 1).trans (norm_etaProd_sub_one_le hw ha)
  rw [norm_one, abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-! ### The enclosure -/

private lemma small_aux {α : ℝ} (hα0 : 0 ≤ α) (hα : 3 * α < 1) :
    2 * α < 1 ∧ 2 * α ^ 2 < 1 ∧ α / (1 - 2 * α) < 1 ∧ α ^ 2 / (1 - 2 * α ^ 2) < 1 := by
  have h1 : 2 * α < 1 := by linarith
  have h2 : α ^ 2 < 1 / 9 := by nlinarith
  refine ⟨h1, by linarith, ?_, ?_⟩
  · rw [div_lt_one (by linarith)]; linarith
  · rw [div_lt_one (by nlinarith)]; nlinarith

/-- Upper enclosure of `|f₂(τ)²⁴|`. -/
theorem norm_weberF₂_pow_24_le {τ : ℍ} {α : ℝ} (hα : 3 * α < 1) (hq : ‖qOf τ‖ ≤ α) :
    ‖weberF₂ τ ^ 24‖ ≤
      4096 * ‖qOf τ‖ * ((1 + α ^ 2 / (1 - 2 * α ^ 2)) / (1 - α / (1 - 2 * α))) ^ 24 := by
  have hα0 : 0 ≤ α := (norm_nonneg _).trans hq
  obtain ⟨a1, a2, a3, a4⟩ := small_aux hα0 hα
  have hq2 : ‖qOf τ ^ 2‖ ≤ α ^ 2 := by rw [norm_pow]; gcongr
  have b1 := norm_etaProd_bounds hq a1
  have b2 := norm_etaProd_bounds hq2 a2
  rw [norm_weberF₂_pow_24_eq]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ 24) (by positivity)
  exact div_le_div₀ (by linarith [b2.2, norm_nonneg (etaProd (qOf τ ^ 2))]) b2.2 (by linarith)
    b1.1

/-- Lower enclosure of `|f₂(τ)²⁴|`. -/
theorem le_norm_weberF₂_pow_24 {τ : ℍ} {α : ℝ} (hα : 3 * α < 1) (hq : ‖qOf τ‖ ≤ α) :
    4096 * ‖qOf τ‖ * ((1 - α ^ 2 / (1 - 2 * α ^ 2)) / (1 + α / (1 - 2 * α))) ^ 24 ≤
      ‖weberF₂ τ ^ 24‖ := by
  have hα0 : 0 ≤ α := (norm_nonneg _).trans hq
  obtain ⟨a1, a2, a3, a4⟩ := small_aux hα0 hα
  have hq2 : ‖qOf τ ^ 2‖ ≤ α ^ 2 := by rw [norm_pow]; gcongr
  have b1 := norm_etaProd_bounds hq a1
  have b2 := norm_etaProd_bounds hq2 a2
  have hpos : 0 < ‖etaProd (qOf τ)‖ := norm_pos_iff.2 (etaProd_ne_zero τ)
  rw [norm_weberF₂_pow_24_eq]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg (by linarith) (by positivity))
    ?_ 24) (by positivity)
  exact div_le_div₀ (norm_nonneg _) b2.1 hpos b1.2

/-! ### Weber's cubic in norms -/

private theorem norm_cubic {τ : ℍ} {v : ℂ}
    (hW : (weberF₂ τ ^ 24 + 16) ^ 3 = kleinJ τ * weberF₂ τ ^ 24) (hj : kleinJ τ = v ^ 3) :
    ‖weberF₂ τ ^ 24 + 16‖ ^ 3 = ‖v‖ ^ 3 * ‖weberF₂ τ ^ 24‖ := by
  have h := congrArg norm hW
  rwa [hj, norm_pow, norm_mul, norm_pow] at h

private theorem false_of_norm_le {τ : ℍ} {v : ℂ}
    (hW : (weberF₂ τ ^ 24 + 16) ^ 3 = kleinJ τ * weberF₂ τ ^ 24) (hj : kleinJ τ = v ^ 3)
    {α U : ℝ} (hα : 3 * α < 1) (hq : ‖qOf τ‖ ≤ α)
    (hU : ((1 + α ^ 2 / (1 - 2 * α ^ 2)) / (1 - α / (1 - 2 * α))) ^ 24 ≤ U)
    (hcert : ‖v‖ ^ 3 * (4096 * α * U) < (16 - 4096 * α * U) ^ 3) : False := by
  have hA : 0 ≤ ‖qOf τ‖ := norm_nonneg _
  have hα0 : 0 ≤ α := hA.trans hq
  obtain ⟨a1, a2, a3, a4⟩ := small_aux hα0 hα
  have hU0 : 0 ≤ U := le_trans (by
    have : 0 ≤ 1 - α / (1 - 2 * α) := by linarith
    have : 0 ≤ 1 + α ^ 2 / (1 - 2 * α ^ 2) := by positivity
    positivity) hU
  have hx := (norm_weberF₂_pow_24_le hα hq).trans
    (by gcongr : 4096 * ‖qOf τ‖ * ((1 + α ^ 2 / (1 - 2 * α ^ 2)) / (1 - α / (1 - 2 * α))) ^ 24 ≤
      4096 * α * U)
  have hT : 4096 * α * U ≤ 16 := by
    by_contra h
    replace h := not_le.1 h
    have : (16 - 4096 * α * U) ^ 3 < 0 := Odd.pow_neg (by decide) (by linarith)
    have : 0 ≤ ‖v‖ ^ 3 * (4096 * α * U) := by positivity
    linarith
  set t := ‖weberF₂ τ ^ 24‖
  have hlow : 16 - t ≤ ‖weberF₂ τ ^ 24 + 16‖ := by
    have := norm_sub_norm_le (16 : ℂ) (-(weberF₂ τ ^ 24))
    rw [sub_neg_eq_add, add_comm, norm_neg, Complex.norm_ofNat] at this
    linarith
  have h := norm_cubic hW hj
  have h₁ : (16 - 4096 * α * U) ^ 3 ≤ (16 - t) ^ 3 := by gcongr
  have h₂ : (16 - t) ^ 3 ≤ ‖weberF₂ τ ^ 24 + 16‖ ^ 3 := by
    gcongr
    linarith
  have h₃ : ‖v‖ ^ 3 * t ≤ ‖v‖ ^ 3 * (4096 * α * U) := by gcongr
  linarith

private theorem false_of_le_norm {τ : ℍ} {v : ℂ}
    (hW : (weberF₂ τ ^ 24 + 16) ^ 3 = kleinJ τ * weberF₂ τ ^ 24) (hj : kleinJ τ = v ^ 3)
    {α β L U : ℝ} (hα : 3 * α < 1) (hq : ‖qOf τ‖ ≤ α) (hβ : β ≤ ‖qOf τ‖) (hβ₀ : 0 ≤ β)
    (hU : ((1 + α ^ 2 / (1 - 2 * α ^ 2)) / (1 - α / (1 - 2 * α))) ^ 24 ≤ U)
    (hL : L ≤ ((1 - α ^ 2 / (1 - 2 * α ^ 2)) / (1 + α / (1 - 2 * α))) ^ 24) (hL₀ : 0 ≤ L)
    (hcerta : (16 + 4096 * β * L) ^ 3 < ‖v‖ ^ 3 * (4096 * β * L))
    (hcertb : (16 + 4096 * α * U) ^ 3 < ‖v‖ ^ 3 * (4096 * α * U)) : False := by
  have hA : 0 ≤ ‖qOf τ‖ := norm_nonneg _
  have hα0 : 0 ≤ α := hA.trans hq
  obtain ⟨a1, a2, a3, a4⟩ := small_aux hα0 hα
  have hU0 : 0 ≤ U := le_trans (by
    have : 0 ≤ 1 - α / (1 - 2 * α) := by linarith
    have : 0 ≤ 1 + α ^ 2 / (1 - 2 * α ^ 2) := by positivity
    positivity) hU
  have hhi := (norm_weberF₂_pow_24_le hα hq).trans
    (by gcongr : 4096 * ‖qOf τ‖ * ((1 + α ^ 2 / (1 - 2 * α ^ 2)) / (1 - α / (1 - 2 * α))) ^ 24 ≤
      4096 * α * U)
  have hlo := (le_norm_weberF₂_pow_24 hα hq)
  have ha : 4096 * β * L ≤ ‖weberF₂ τ ^ 24‖ :=
    le_trans (by gcongr) hlo
  set t := ‖weberF₂ τ ^ 24‖
  have hf : ConvexOn ℝ (Set.Ici 0) fun t : ℝ ↦ (16 + t) ^ 3 - ‖v‖ ^ 3 * t := by
    refine ((((convexOn_pow 3).translate_right 16).subset (fun t ht ↦ ?_) (convex_Ici 0)).sub
      ((LinearMap.mul ℝ ℝ (‖v‖ ^ 3)).concaveOn (convex_Ici 0))).congr fun t _ ↦ ?_
    · rw [Set.mem_Ici] at ht
      rw [Set.mem_preimage, Set.mem_Ici]
      linarith
    · simp only [Pi.sub_apply, Function.comp_apply, LinearMap.mul_apply']
  have hmax := hf.le_max_of_mem_Icc (by positivity : (0 : ℝ) ≤ 4096 * β * L)
    (by positivity : (0 : ℝ) ≤ 4096 * α * U) ⟨ha, hhi⟩
  have hlt : (16 + t) ^ 3 < ‖v‖ ^ 3 * t := by
    rw [le_max_iff] at hmax
    rcases hmax with h | h <;> linarith
  have hup : ‖weberF₂ τ ^ 24 + 16‖ ≤ 16 + t := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_ofNat, add_comm]
  have h := norm_cubic hW hj
  have h₁ : ‖weberF₂ τ ^ 24 + 16‖ ^ 3 ≤ (16 + t) ^ 3 := by gcongr
  linarith

/-! ### Certified bounds for `e^{-π √m}` -/

private theorem exp_neg_le_of_le {x c : ℝ} (k : ℕ) (hc : 0 ≤ c) (hx : k + c ≤ x) :
    Real.exp (-x) ≤ (2.7182818283 ^ k * ∑ i ∈ Finset.range 6, c ^ i / i.factorial)⁻¹ := by
  have hS : 0 < ∑ i ∈ Finset.range 6, c ^ i / i.factorial := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    positivity
  calc Real.exp (-x) ≤ Real.exp (-(k + c)) := Real.exp_le_exp.2 (by linarith)
    _ = (Real.exp 1 ^ k * Real.exp c)⁻¹ := by
      rw [Real.exp_neg, Real.exp_add, ← Real.exp_nat_mul, mul_one]
    _ ≤ _ := inv_anti₀ (by positivity) (mul_le_mul (pow_le_pow_left₀ (by norm_num)
      Real.exp_one_gt_d9.le k) (Real.sum_le_exp_of_nonneg hc 6) hS.le (by positivity))

private theorem le_exp_neg_of_le {x d : ℝ} (k : ℕ) (hd : 0 ≤ d) (hx : x ≤ k - d) :
    (∑ i ∈ Finset.range 6, d ^ i / i.factorial) / 2.7182818286 ^ k ≤ Real.exp (-x) := by
  calc (∑ i ∈ Finset.range 6, d ^ i / i.factorial) / 2.7182818286 ^ k
      ≤ Real.exp d / Real.exp 1 ^ k := by
        gcongr
        · exact Real.sum_le_exp_of_nonneg hd 6
        · exact Real.exp_one_lt_d9.le
    _ = Real.exp (-(k - d)) := by
      rw [← Real.exp_nat_mul, mul_one, ← Real.exp_sub]
      ring_nf
    _ ≤ Real.exp (-x) := Real.exp_le_exp.2 (by linarith)

private theorem exp_neg_pi_mul_sqrt_le {m s c α : ℝ} (k : ℕ) (hs₀ : 0 ≤ s) (hs : s ^ 2 ≤ m)
    (hc : 0 ≤ c) (hk : k + c ≤ 3.141592 * s)
    (hα : (2.7182818283 ^ k * ∑ i ∈ Finset.range 6, c ^ i / i.factorial)⁻¹ ≤ α) :
    Real.exp (-(π * √m)) ≤ α := by
  have h₁ : s ≤ √m := by simpa [Real.sqrt_sq hs₀] using Real.sqrt_le_sqrt hs
  have h₂ : 3.141592 * s ≤ π * √m := mul_le_mul Real.pi_gt_d6.le h₁ hs₀ Real.pi_pos.le
  exact (exp_neg_le_of_le k hc (hk.trans h₂)).trans hα

private theorem le_exp_neg_pi_mul_sqrt {m s d β : ℝ} (k : ℕ) (hs₀ : 0 ≤ s) (hs : m ≤ s ^ 2)
    (hd : 0 ≤ d) (hk : 3.141593 * s ≤ k - d)
    (hβ : β ≤ (∑ i ∈ Finset.range 6, d ^ i / i.factorial) / 2.7182818286 ^ k) :
    β ≤ Real.exp (-(π * √m)) := by
  have h₁ : √m ≤ s := by simpa [Real.sqrt_sq hs₀] using Real.sqrt_le_sqrt hs
  have h₂ : π * √m ≤ 3.141593 * s :=
    mul_le_mul Real.pi_lt_d6.le h₁ (Real.sqrt_nonneg _) (by norm_num)
  exact hβ.trans (le_exp_neg_of_le k hd (h₂.trans hk))

/-! ### The imaginary part from the value of `j` -/

private theorem norm_qOf (τ : ℍ) : ‖qOf τ‖ = Real.exp (-(2 * π * τ.im)) := by
  unfold qOf; rw [Complex.norm_exp]; congr 1; simp [mul_assoc]

private theorem norm_qOf_le {τ : ℍ} {m : ℝ} (h : √m / 2 ≤ τ.im) :
    ‖qOf τ‖ ≤ Real.exp (-(π * √m)) := by
  rw [norm_qOf, Real.exp_le_exp]
  have := mul_le_mul_of_nonneg_left h Real.pi_pos.le
  linarith

private theorem le_norm_qOf {τ : ℍ} {m : ℝ} (h : τ.im ≤ √m / 2) :
    Real.exp (-(π * √m)) ≤ ‖qOf τ‖ := by
  rw [norm_qOf, Real.exp_le_exp]
  have := mul_le_mul_of_nonneg_left h Real.pi_pos.le
  linarith

/-- For `Im τ ≥ √3 / 2`, `|q| ≤ 0.00434`. -/
private theorem norm_qOf_le_of_three_le {τ : ℍ} {n : ℕ} (hτ : τ.im = √n / 2) (hn : 3 ≤ n) :
    ‖qOf τ‖ ≤ 0.00434 :=
  (norm_qOf_le (m := 3) (by rw [hτ]; gcongr; exact_mod_cast hn)).trans <|
    exp_neg_pi_mul_sqrt_le (s := 1.73205) (c := 0.4413) 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- For `Im τ ≥ √11 / 2`, `|q| ≤ 3.1e-5`. -/
private theorem norm_qOf_le_of_eleven_le {τ : ℍ} (hτ : √11 / 2 ≤ τ.im) : ‖qOf τ‖ ≤ 3.1e-5 :=
  (norm_qOf_le (m := 11) hτ).trans <|
    exp_neg_pi_mul_sqrt_le (s := 3.3166) (c := 0.41) 10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- For `Im τ ≥ √11 / 2` the number `f₂(τ)²⁴` is tiny. -/
theorem norm_weberF₂_pow_24_lt_one {τ : ℍ} (hτ : √11 / 2 ≤ τ.im) : ‖weberF₂ τ ^ 24‖ < 1 := by
  have hq := norm_qOf_le_of_eleven_le hτ
  have h := norm_weberF₂_pow_24_le (by norm_num) hq
  have hU : ((1 + (3.1e-5 : ℝ) ^ 2 / (1 - 2 * (3.1e-5 : ℝ) ^ 2)) /
      (1 - (3.1e-5 : ℝ) / (1 - 2 * (3.1e-5 : ℝ)))) ^ 24 ≤ 1.001 := by norm_num
  have hU0 : 0 ≤ ((1 + (3.1e-5 : ℝ) ^ 2 / (1 - 2 * (3.1e-5 : ℝ) ^ 2)) /
      (1 - (3.1e-5 : ℝ) / (1 - 2 * (3.1e-5 : ℝ)))) ^ 24 := by
    have : (0 : ℝ) ≤ 1 - (3.1e-5 : ℝ) / (1 - 2 * (3.1e-5 : ℝ)) := by norm_num
    positivity
  calc ‖weberF₂ τ ^ 24‖ ≤ _ := h
    _ ≤ 4096 * 3.1e-5 * 1.001 := by gcongr
    _ < 1 := by norm_num

private theorem le_of_kleinJ_eq {τ : ℍ} {n m m' : ℕ} {v : ℂ} (hτ : τ.im = √n / 2)
    (hW : (weberF₂ τ ^ 24 + 16) ^ 3 = kleinJ τ * weberF₂ τ ^ 24) (hj : kleinJ τ = v ^ 3)
    (hm : m + 1 = m') {α U : ℝ} (hα : Real.exp (-(π * √m')) ≤ α) (hα₀ : α ≤ 0.002)
    (hU : ((1 + α ^ 2 / (1 - 2 * α ^ 2)) / (1 - α / (1 - 2 * α))) ^ 24 ≤ U)
    (hcert : ‖v‖ ^ 3 * (4096 * α * U) < (16 - 4096 * α * U) ^ 3) : n ≤ m := by
  by_contra! h
  have hq := (norm_qOf_le (m := (m' : ℝ))
    (by rw [hτ]; gcongr; exact_mod_cast (by omega : m' ≤ n))).trans hα
  exact false_of_norm_le hW hj (by linarith) hq hU hcert

private theorem le_of_kleinJ_eq' {τ : ℍ} {n m m' : ℕ} {v : ℂ} (hτ : τ.im = √n / 2)
    (hn : 3 ≤ n) (hW : (weberF₂ τ ^ 24 + 16) ^ 3 = kleinJ τ * weberF₂ τ ^ 24)
    (hj : kleinJ τ = v ^ 3) (hm : m' + 1 = m) {β : ℝ}
    (hβ : β ≤ Real.exp (-(π * √m'))) (hβ₀ : 0 ≤ β)
    (hcerta : (16 + 4096 * β * 0.89) ^ 3 < ‖v‖ ^ 3 * (4096 * β * 0.89))
    (hcertb : (16 + 4096 * 0.00434 * 1.115) ^ 3 < ‖v‖ ^ 3 * (4096 * 0.00434 * 1.115)) :
    m ≤ n := by
  by_contra! h
  exact false_of_le_norm hW hj (by norm_num) (norm_qOf_le_of_three_le hτ hn)
    (hβ.trans (le_norm_qOf (m := (m' : ℝ))
      (by rw [hτ]; gcongr; exact_mod_cast (by omega : n ≤ m')))) hβ₀ (by norm_num)
    (by norm_num) (by norm_num) hcerta hcertb

/-- Recovering the discriminant from a singular value of `j` (port of Tau Ceti's
`mem_of_j_eq_intCast_pow_three`). -/
theorem mem_of_kleinJ_eq_pow_three {τ : ℍ} {n : ℕ} (hn : 3 ≤ n) (hτ : τ.im = √n / 2)
    (hW : (weberF₂ τ ^ 24 + 16) ^ 3 = kleinJ τ * weberF₂ τ ^ 24)
    {v : ℤ} (hv : v ∈ ({0, -32, -96, -960, -5280, -640320} : Finset ℤ))
    (hj : kleinJ τ = (v : ℂ) ^ 3) : n ∈ ({3, 11, 19, 43, 67, 163} : Finset ℕ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain rfl : n = 3 := by
      refine le_antisymm (le_of_kleinJ_eq (m := 3) (m' := 4) (α := 1.88e-3) (U := 1.05) hτ hW hj
        rfl (exp_neg_pi_mul_sqrt_le (s := 2) (c := 0.2831) 6 ?_ ?_ ?_ ?_ ?_) ?_ ?_ ?_) hn <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
    simp
  · obtain rfl : n = 11 := by
      refine le_antisymm (le_of_kleinJ_eq (m := 11) (m' := 12) (α := 1.89e-5) (U := 1.001) hτ hW hj
        rfl (exp_neg_pi_mul_sqrt_le (s := 3.464101) (c := 0.8827) 10 ?_ ?_ ?_ ?_ ?_) ?_ ?_ ?_)
        (le_of_kleinJ_eq' (m := 11) (m' := 10) (β := 4.84e-5) hτ hn hW hj rfl
          (le_exp_neg_pi_mul_sqrt (s := 3.162278) (d := 0.0654) 10 ?_ ?_ ?_ ?_ ?_) ?_ ?_ ?_) <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
    simp
  · obtain rfl : n = 19 := by
      refine le_antisymm (le_of_kleinJ_eq (m := 19) (m' := 20) (α := 7.92e-7) (U := 1.0001) hτ hW
        hj rfl (exp_neg_pi_mul_sqrt_le (s := 4.472135) (c := 0.0496) 14 ?_ ?_ ?_ ?_ ?_) ?_ ?_ ?_)
        (le_of_kleinJ_eq' (m := 19) (m' := 18) (β := 1.62e-6) hτ hn hW hj rfl
          (le_exp_neg_pi_mul_sqrt (s := 4.242641) (d := 0.6713) 14 ?_ ?_ ?_ ?_ ?_) ?_ ?_ ?_) <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
    simp
  · obtain rfl : n = 43 := by
      refine le_antisymm (le_of_kleinJ_eq (m := 43) (m' := 44) (α := 8.92e-10) (U := 1.000001) hτ
        hW hj rfl (exp_neg_pi_mul_sqrt_le (s := 6.633249) (c := 0.8389) 20 ?_ ?_ ?_ ?_ ?_) ?_ ?_ ?_)
        (le_of_kleinJ_eq' (m := 43) (m' := 42) (β := 1.43e-9) hτ hn hW hj rfl
          (le_exp_neg_pi_mul_sqrt (s := 6.480741) (d := 0.6401) 21 ?_ ?_ ?_ ?_ ?_) ?_ ?_ ?_) <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
    simp
  · obtain rfl : n = 67 := by
      refine le_antisymm (le_of_kleinJ_eq (m := 67) (m' := 68) (α := 5.62e-12) (U := 1.000001) hτ
        hW hj rfl (exp_neg_pi_mul_sqrt_le (s := 8.246211) (c := 0.9062) 25 ?_ ?_ ?_ ?_ ?_) ?_ ?_ ?_)
        (le_of_kleinJ_eq' (m := 67) (m' := 66) (β := 8.23e-12) hτ hn hW hj rfl
          (le_exp_neg_pi_mul_sqrt (s := 8.124039) (d := 0.4775) 26 ?_ ?_ ?_ ?_ ?_) ?_ ?_ ?_) <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
    simp
  · obtain rfl : n = 163 := by
      refine le_antisymm (le_of_kleinJ_eq (m := 163) (m' := 164) (α := 3.38e-18) (U := 1.000001)
        hτ hW hj rfl (exp_neg_pi_mul_sqrt_le (s := 12.806248) (c := 0.232) 40 ?_ ?_ ?_ ?_ ?_)
        ?_ ?_ ?_)
        (le_of_kleinJ_eq' (m := 163) (m' := 162) (β := 4.30e-18) hτ hn hW hj rfl
          (le_exp_neg_pi_mul_sqrt (s := 12.727923) (d := 0.014) 40 ?_ ?_ ?_ ?_ ?_) ?_ ?_ ?_) <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
    simp

end ModularFormsKB.WeberHeegnerStark
