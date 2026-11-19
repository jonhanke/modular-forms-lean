import ModularFormsKB.Historical.Weber.SecondOrder
import ModularFormsKB.Citation
/-!
# Ramanujan's class invariants `G_n`, `g_n` and their relations (No. 6, § 1)

Ramanujan, *Collected Papers*, No. 6 (*Modular equations and approximations to π*, Quart. J. Math. 45 (1914)),
§ 1, (1)–(7), p. 23: for `n > 0` and `q = e^{-π√n}`,

  `G_n = 2^{-1/4} q^{-1/24} ∏_{k ≥ 1} (1 + q^{2k-1})`,  `g_n = 2^{-1/4} q^{-1/24} ∏_{k ≥ 1} (1 - q^{2k-1})`,

so that `G_n = 2^{-1/4} f(√-n)` and `g_n = 2^{-1/4} f₁(√-n)` with Weber's `f`, `f₁` (`ramanujanG_eq`,
`ramanujanSmallG_eq`). Ramanujan's relations (5)–(7):

* (5) `g_{4n} = 2^{1/4} g_n G_n`;
* (6) `G_{1/n} = G_n` and `1/g_n = g_{4/n}`;
* (7) `(g_n G_n)⁸ (G_n⁸ - g_n⁸) = 1/4`.

**On (6).** A paraphrase of (6) that circulates reads `g_{1/n} = 1/g_n`; that is false (at `n = 1`, `g_1² = 2^{-1/4}`;
`not_ramanujanSmallG_inv`). The identity that holds, and the one Ramanujan uses, is `g_n g_{4/n} = 1`
(equivalently `g_{1/n} g_{4n} = 1`); it is the form stated here (loose end, erratum).

Ramanujan treats integral `n`; the relations are stated for all real `n > 0`.
-/

noncomputable section

open Complex
open scoped Real

namespace ModularFormsKB.Historical.Ramanujan

open ModularFormsKB.WeberHeegnerStark (weberF weberF₂)
open ModularFormsKB.Historical.Weber (weberF₁)

/-- **Ramanujan's `G_n`** (No. 6, § 1, (1), p. 23):
`G_n = 2^{-1/4} q^{-1/24} ∏_{k ≥ 1} (1 + q^{2k-1})`, `q = e^{-π√n}` (the product indexed from `k = 0` as `2k + 1`).
**Restriction:** the product converges for `n > 0` (so that `q = e^{-π√n} < 1`); for `n ≤ 0` Lean's `√n` is `0`, so
`q = 1` and the product is not multipliable. There the product is `1` by Lean's convention for a non-multipliable
`∏'`, so `ramanujanG n = 2^{-1/4}`, not the intended value. -/
@[kb "ramanujan1927" "No. 6, § 1, (1), p. 23"]
def ramanujanG (n : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (π * √n / 24) *
    ∏' k : ℕ, (1 + Real.exp (-(π * √n)) ^ (2 * k + 1))

/-- **Ramanujan's `g_n`** (No. 6, § 1, (1), p. 23):
`g_n = 2^{-1/4} q^{-1/24} ∏_{k ≥ 1} (1 - q^{2k-1})`, `q = e^{-π√n}`. -/
@[kb "ramanujan1927" "No. 6, § 1, (1), p. 23"]
def ramanujanSmallG (n : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.exp (π * √n / 24) *
    ∏' k : ℕ, (1 - Real.exp (-(π * √n)) ^ (2 * k + 1))

/-- **Ramanujan, No. 6, § 1, (5)–(7)** (p. 23), with (6) in the form
`1/g_n = g_{4/n}` (see the module docstring). -/
@[kb "ramanujan1927" "No. 6, § 1, (5)-(7), p. 23"]
def RamanujanClassInvariantRelations : Prop :=
  ∀ n : ℝ, 0 < n →
    ramanujanSmallG (4 * n) = (2 : ℝ) ^ (1 / 4 : ℝ) * ramanujanSmallG n * ramanujanG n ∧
    ramanujanG (1 / n) = ramanujanG n ∧
    1 / ramanujanSmallG n = ramanujanSmallG (4 / n) ∧
    (ramanujanSmallG n * ramanujanG n) ^ 8 * (ramanujanG n ^ 8 - ramanujanSmallG n ^ 8) = 1 / 4

section Proofs

open ModularFormsKB.Historical.Weber

/-! ### `G_n`, `g_n` as Weber's `f`, `f₁` -/

lemma ofReal_tprod' (b : ℕ → ℝ) : ((∏' k, b k : ℝ) : ℂ) = ∏' k, (b k : ℂ) :=
  Topology.IsClosedEmbedding.map_tprod (g := Complex.ofRealHom) b
    Complex.isUniformEmbedding_ofReal.isClosedEmbedding

lemma exp_mul_exp_neg (t : ℝ) :
    ((Real.exp (π * t / 24) : ℝ) : ℂ) * ((Real.exp (-(π * t) / 24) : ℝ) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, ← Real.exp_add, show π * t / 24 + -(π * t) / 24 = 0 by ring,
    Real.exp_zero]
  simp

lemma weberF_eq_real {t : ℝ} (ht : 0 < t) :
    weberF (I * (t : ℂ)) =
      ((Real.exp (π * t / 24) * ∏' k : ℕ, (1 + Real.exp (-(π * t)) ^ (2 * k + 1)) : ℝ) : ℂ) := by
  have hω : 0 < (I * (t : ℂ)).im := by simpa using ht
  rw [weberF_eq_q hω (q_real t).symm (s_real t).symm]
  have hP : (∏' k : ℕ, (1 + ((Real.exp (-(π * t)) : ℝ) : ℂ) ^ (2 * k + 1))) =
      ((∏' k : ℕ, (1 + Real.exp (-(π * t)) ^ (2 * k + 1)) : ℝ) : ℂ) := by
    rw [ofReal_tprod']; exact tprod_congr fun k ↦ by push_cast; ring
  rw [hP, Complex.ofReal_mul, div_eq_iff (by exact_mod_cast (Real.exp_pos _).ne')]
  generalize ((∏' k : ℕ, (1 + Real.exp (-(π * t)) ^ (2 * k + 1)) : ℝ) : ℂ) = P
  linear_combination (-P) * exp_mul_exp_neg t

lemma weberF₁_eq_real {t : ℝ} (ht : 0 < t) :
    weberF₁ (I * (t : ℂ)) =
      ((Real.exp (π * t / 24) * ∏' k : ℕ, (1 - Real.exp (-(π * t)) ^ (2 * k + 1)) : ℝ) : ℂ) := by
  have hω : 0 < (I * (t : ℂ)).im := by simpa using ht
  rw [weberF₁_eq_q hω (q_real t).symm (s_real t).symm]
  have hP : (∏' k : ℕ, (1 - ((Real.exp (-(π * t)) : ℝ) : ℂ) ^ (2 * k + 1))) =
      ((∏' k : ℕ, (1 - Real.exp (-(π * t)) ^ (2 * k + 1)) : ℝ) : ℂ) := by
    rw [ofReal_tprod']; exact tprod_congr fun k ↦ by push_cast; ring
  rw [hP, Complex.ofReal_mul, div_eq_iff (by exact_mod_cast (Real.exp_pos _).ne')]
  generalize ((∏' k : ℕ, (1 - Real.exp (-(π * t)) ^ (2 * k + 1)) : ℝ) : ℂ) = P
  linear_combination (-P) * exp_mul_exp_neg t

/-- `G_n = 2^{-1/4} f(√-n)` (No. 6, § 1, (1)–(2)). -/
theorem ramanujanG_eq (n : ℝ) (hn : 0 < n) :
    (ramanujanG n : ℂ) = (((2 : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * weberF (I * ((√n : ℝ) : ℂ)) := by
  rw [weberF_eq_real (Real.sqrt_pos.mpr hn), ← Complex.ofReal_mul]
  congr 1
  unfold ramanujanG
  ring

/-- `g_n = 2^{-1/4} f₁(√-n)` (No. 6, § 1, (1)–(2)). -/
theorem ramanujanSmallG_eq (n : ℝ) (hn : 0 < n) :
    (ramanujanSmallG n : ℂ) =
      (((2 : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * weberF₁ (I * ((√n : ℝ) : ℂ)) := by
  rw [weberF₁_eq_real (Real.sqrt_pos.mpr hn), ← Complex.ofReal_mul]
  congr 1
  unfold ramanujanSmallG
  ring

/-! ### Transformation laws of `f`, `f₁`, `f₂` -/

lemma weber_ne_zero {τ : ℂ} (hτ : 0 < τ.im) :
    weberF τ ≠ 0 ∧ weberF₁ τ ≠ 0 ∧ weberF₂ τ ≠ 0 := by
  have h := weber_triple hτ
  have h0 := sqrt2_ne
  refine ⟨?_, ?_, ?_⟩ <;> intro h' <;> rw [h'] at h <;> simp at h <;> exact h0 h.symm

/-- `f₁(-1/τ) = f₂(τ)`. -/
lemma weberF₁_neg_inv {τ : ℂ} (hτ : 0 < τ.im) : weberF₁ (-1 / τ) = weberF₂ τ := by
  have hτ0 : τ ≠ 0 := fun h ↦ by simp [h] at hτ
  have hz2 : 0 < (2 * τ).im := by simpa using hτ
  have h1 : ModularForm.eta (2 * τ) ≠ 0 := ModularForm.eta_ne_zero hz2
  have h2 : ModularForm.eta τ ≠ 0 := ModularForm.eta_ne_zero hτ
  have h3 := csqrt_ne_zero hτ0
  have h4 := csqrt_ne_zero Complex.I_ne_zero
  unfold weberF₁ weberF₂
  rw [show (-1 / τ) / 2 = -1 / (2 * τ) by field_simp, eta_S_eq hz2, eta_S_eq hτ,
    csqrt_two_mul hτ0]
  field_simp

/-- `f(-1/τ) = f(τ)`. -/
lemma weberF_neg_inv {τ : ℂ} (hτ : 0 < τ.im) : weberF (-1 / τ) = weberF τ := by
  have hτ0 : τ ≠ 0 := fun h ↦ by simp [h] at hτ
  have hS := im_neg_one_div_pos hτ
  have h1 := weberF₁_neg_inv hτ
  have h2 := weberF₁_neg_inv hS
  rw [show -1 / (-1 / τ) = τ by field_simp] at h2
  have hT := weber_triple hS
  rw [h1, ← h2] at hT
  have hT0 := weber_triple hτ
  obtain ⟨-, hf1, hf2⟩ := weber_ne_zero hτ
  apply mul_right_cancel₀ (mul_ne_zero hf1 hf2)
  linear_combination hT - hT0

/-- `f₁(2τ) = f(τ) f₁(τ)`. -/
lemma weberF₁_two_mul {τ : ℂ} (hτ : 0 < τ.im) : weberF₁ (2 * τ) = weberF τ * weberF₁ τ := by
  obtain ⟨-, -, hf2⟩ := weber_ne_zero hτ
  apply mul_right_cancel₀ hf2
  linear_combination weber_prod12 hτ - weber_triple hτ

/-! ### Constants -/

lemma const_facts :
    (2 : ℝ) ^ (-(1 / 4 : ℝ)) * (2 : ℝ) ^ (1 / 4 : ℝ) = 1 ∧
      ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = √2 ∧ ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ 8 = 4 := by
  obtain ⟨g, hg0, h14, -, h2⟩ := two_rpow_facts
  refine ⟨?_, ?_, ?_⟩
  · rw [← Real.rpow_add (by norm_num)]; norm_num
  · rw [h14, h2]; ring
  · rw [h14, show (g ^ 2) ^ 8 = (g ^ 4) ^ 4 by ring, ← h2,
      show √2 ^ 4 = (√2 ^ 2) ^ 2 by ring, Real.sq_sqrt (by norm_num)]
    norm_num

lemma sqrt_four_mul {n : ℝ} : ((√(4 * n) : ℝ) : ℂ) = 2 * ((√n : ℝ) : ℂ) := by
  have h4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [Real.sqrt_mul (by norm_num), h4]; push_cast; ring

/-! ### Ramanujan's relations -/

/-- **(5)** `g_{4n} = 2^{1/4} g_n G_n` (No. 6, § 1, (5), p. 23): from
`f₁(2τ) = f(τ) f₁(τ)`, i.e. `f₁(2τ) f₂(τ) = √2 = f f₁ f₂`. -/
@[kb "ramanujan1927" "No. 6, § 1, (5), p. 23"]
theorem ramanujanSmallG_four_mul (n : ℝ) (hn : 0 < n) :
    ramanujanSmallG (4 * n) =
      (2 : ℝ) ^ (1 / 4 : ℝ) * ramanujanSmallG n * ramanujanG n := by
  obtain ⟨hc, -, -⟩ := const_facts
  have hc' : (((2 : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * (((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hc
  have hτ : 0 < (I * ((√n : ℝ) : ℂ)).im := by simpa using Real.sqrt_pos.mpr hn
  apply Complex.ofReal_injective
  rw [ramanujanSmallG_eq (4 * n) (by positivity), Complex.ofReal_mul, Complex.ofReal_mul,
    ramanujanSmallG_eq n hn, ramanujanG_eq n hn, sqrt_four_mul,
    show I * (2 * ((√n : ℝ) : ℂ)) = 2 * (I * ((√n : ℝ) : ℂ)) by ring, weberF₁_two_mul hτ]
  linear_combination (-((((2 : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * weberF (I * ((√n : ℝ) : ℂ)) *
    weberF₁ (I * ((√n : ℝ) : ℂ)))) * hc'

/-- **(6a)** `G_{1/n} = G_n` (No. 6, § 1, (6), p. 23): `f(-1/τ) = f(τ)`
at `τ = i√n`. -/
@[kb "ramanujan1927" "No. 6, § 1, (6), p. 23"]
theorem ramanujanG_inv (n : ℝ) (hn : 0 < n) : ramanujanG (1 / n) = ramanujanG n := by
  have ht := Real.sqrt_pos.mpr hn
  have hτ : 0 < (I * ((√n : ℝ) : ℂ)).im := by simpa using ht
  have ht0 : ((√n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  apply Complex.ofReal_injective
  have this : I * ((√(1 / n) : ℝ) : ℂ) = -1 / (I * ((√n : ℝ) : ℂ)) := by
    rw [one_div, Real.sqrt_inv]; push_cast
    field_simp
    linear_combination (1 : ℂ) * Complex.I_sq
  rw [ramanujanG_eq (1 / n) (by positivity), ramanujanG_eq n hn, this, weberF_neg_inv hτ]

/-- **(6b)** `1/g_n = g_{4/n}` (No. 6, § 1, (6), p. 23): `f₁(-1/τ) = f₂(τ)` at
`τ = i√n/2` and `f₁(τ) f₂(τ/2) = √2`. -/
@[kb "ramanujan1927" "No. 6, § 1, (6), p. 23"]
theorem ramanujanSmallG_inv_four_div (n : ℝ) (hn : 0 < n) :
    1 / ramanujanSmallG n = ramanujanSmallG (4 / n) := by
  obtain ⟨hc, ha, -⟩ := const_facts
  have ht := Real.sqrt_pos.mpr hn
  have hτ : 0 < (I * ((√n : ℝ) : ℂ)).im := by simpa using ht
  have hτ2 : 0 < (I * ((√n : ℝ) : ℂ) / 2).im := by simpa using ht
  have ht0 : ((√n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hcs : (((2 : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) ^ 2 * ((√2 : ℝ) : ℂ) = 1 := by
    have hc' : (((2 : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * (((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) = 1 := by
      exact_mod_cast hc
    have ha' : (((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) ^ 2 = ((√2 : ℝ) : ℂ) := by exact_mod_cast ha
    rw [← ha']
    linear_combination (((2 : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) * ((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ) + 1 : ℂ) * hc'
  have key : ramanujanSmallG n * ramanujanSmallG (4 / n) = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul, ramanujanSmallG_eq n hn, ramanujanSmallG_eq (4 / n) (by positivity)]
    have h4 : I * ((√(4 / n) : ℝ) : ℂ) = -1 / (I * ((√n : ℝ) : ℂ) / 2) := by
      have : √(4 / n) = 2 / √n := by
        rw [Real.sqrt_div (by norm_num)]
        congr 1
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
      rw [this]; push_cast
      field_simp
      linear_combination (1 : ℂ) * Complex.I_sq
    rw [h4, weberF₁_neg_inv hτ2]
    have := weber_f₁_f₂_half hτ
    push_cast
    linear_combination (((2 : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) ^ 2 * this + hcs
  have hg0 : ramanujanSmallG n ≠ 0 := left_ne_zero_of_mul_eq_one key
  rw [div_eq_iff hg0]
  linarith [mul_comm (ramanujanSmallG n) (ramanujanSmallG (4 / n))]

/-- **(7)** `(g_n G_n)⁸ (G_n⁸ - g_n⁸) = 1/4` (No. 6, § 1, (7), p. 23), from
Weber's `f⁸ = f₁⁸ + f₂⁸` and `f f₁ f₂ = √2`. -/
@[kb "ramanujan1927" "No. 6, § 1, (7), p. 23"]
theorem ramanujan_seven (h : WeberEighthPowers) (n : ℝ) (hn : 0 < n) :
    (ramanujanSmallG n * ramanujanG n) ^ 8 * (ramanujanG n ^ 8 - ramanujanSmallG n ^ 8) = 1 / 4 := by
  obtain ⟨hc, -, ha8⟩ := const_facts
  have hτ : 0 < (I * ((√n : ℝ) : ℂ)).im := by simpa using Real.sqrt_pos.mpr hn
  have hc' : (((2 : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * (((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hc
  have ha' : (((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) ^ 8 = 4 := by exact_mod_cast ha8
  have hc8 : (((2 : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) ^ 8 = 1 / 4 := by
    have : ((((2 : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * (((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ)) ^ 8 = 1 := by
      rw [hc']; norm_num
    rw [mul_pow, ha'] at this
    linear_combination (1 / 4 : ℂ) * this
  have h8 := h _ hτ
  have hT := weber_triple hτ
  have hs8 : ((√2 : ℝ) : ℂ) ^ 8 = 16 := by
    rw [show ((√2 : ℝ) : ℂ) ^ 8 = (((√2 : ℝ) : ℂ) ^ 2) ^ 4 by ring, sqrt2_sq]; norm_num
  apply Complex.ofReal_injective
  push_cast
  rw [ramanujanSmallG_eq n hn, ramanujanG_eq n hn]
  generalize weberF (I * ((√n : ℝ) : ℂ)) = f at *
  generalize weberF₁ (I * ((√n : ℝ) : ℂ)) = g at *
  generalize weberF₂ (I * ((√n : ℝ) : ℂ)) = k at *
  generalize (((2 : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) = c at *
  have e1 : (c * g * (c * f)) ^ 8 * ((c * f) ^ 8 - (c * g) ^ 8) = (c ^ 8) ^ 3 * (f * g * k) ^ 8 := by
    have : f ^ 8 - g ^ 8 = k ^ 8 := by linear_combination h8
    linear_combination (c ^ 24 * (f * g) ^ 8) * this
  rw [e1, hc8, hT, hs8]
  norm_num

/-- **Ramanujan, No. 6, § 1, (5)–(7)** (p. 23): the relations between `G_n` and
`g_n`, for all real `n > 0`, given Weber's `f⁸ = f₁⁸ + f₂⁸` (needed only for (7)). Here (5), (6) are
unconditional (`ramanujanSmallG_four_mul`, `ramanujanG_inv`, `ramanujanSmallG_inv_four_div`). -/
@[kb "ramanujan1927" "No. 6, § 1, (5)-(7), p. 23"]
theorem ramanujanClassInvariantRelations (h : WeberEighthPowers) : RamanujanClassInvariantRelations :=
  fun n hn ↦ ⟨ramanujanSmallG_four_mul n hn, ramanujanG_inv n hn,
    ramanujanSmallG_inv_four_div n hn, ramanujan_seven h n hn⟩

/-- The circulating paraphrase `g_{1/n} = 1/g_n` of (6) is false: at `n = 1`, `g_1² = 2^{-1/4} ≠ 1`
(since `f₁(i) = f₂(i)` and `f(i) = 2^{1/4}`). See the module docstring. -/
theorem not_ramanujanSmallG_inv :
    ¬ ∀ n : ℝ, 0 < n → ramanujanSmallG (1 / n) = 1 / ramanujanSmallG n := by
  intro h
  obtain ⟨hc, ha, -⟩ := const_facts
  have hI : 0 < (I : ℂ).im := by simp
  have hc' : (((2 : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * (((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hc
  have ha' : (((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) ^ 2 = ((√2 : ℝ) : ℂ) := by exact_mod_cast ha
  have hF : weberF I = (((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) := by
    have := tableRow1
    unfold TableRow1 at this
    rwa [show sqrtNeg 1 = I by simp [sqrtNeg]] at this
  have hF1 : weberF₁ I = weberF₂ I := by
    have := weberF₁_neg_inv hI
    rwa [show (-1 : ℂ) / I = I by field_simp; linear_combination (-1 : ℂ) * Complex.I_sq] at this
  have hT := weber_triple hI
  rw [hF, hF1, ← ha'] at hT
  obtain ⟨-, -, hf2⟩ := weber_ne_zero hI
  have hsq : weberF₂ I ^ 2 = (((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) := by
    have ha0 : (((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < (2 : ℝ) ^ (1 / 4 : ℝ) := by positivity
      exact_mod_cast this.ne'
    apply mul_left_cancel₀ ha0
    linear_combination hT
  have h1 := h 1 one_pos
  have hg1 : (ramanujanSmallG 1 : ℂ) = (((2 : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * weberF₂ I := by
    rw [ramanujanSmallG_eq 1 one_pos, ← hF1]
    simp
  have hg2 : (ramanujanSmallG 1) ^ 2 = (2 : ℝ) ^ (-(1 / 4 : ℝ)) := by
    apply Complex.ofReal_injective
    push_cast
    rw [hg1, mul_pow, hsq]
    linear_combination (((2 : ℝ) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * hc'
  have hg0 : ramanujanSmallG 1 ≠ 0 := by
    intro h0
    rw [h0] at hg2
    have : (0 : ℝ) < (2 : ℝ) ^ (-(1 / 4 : ℝ)) := by positivity
    linarith [show (0 : ℝ) ^ 2 = 0 by norm_num]
  rw [div_one, eq_div_iff hg0] at h1
  have hc1 : (2 : ℝ) ^ (-(1 / 4 : ℝ)) = 1 := by rw [← hg2]; linear_combination h1
  have ha1 : (2 : ℝ) ^ (1 / 4 : ℝ) = 1 := by
    rw [hc1] at hc; linarith
  rw [ha1] at ha
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [← ha] at this
  norm_num at this

/-- **Ramanujan, No. 6, § 1, (5)–(7)**, unconditional: Weber's `f⁸ = f₁⁸ + f₂⁸` is
proved (`Weber.weberEighthPowers`, from the theta duplication formulas). -/
@[kb "ramanujan1927" "No. 6, § 1, (5)-(7), p. 23"]
theorem ramanujanClassInvariantRelations' : RamanujanClassInvariantRelations :=
  ramanujanClassInvariantRelations weberEighthPowers

end Proofs

end ModularFormsKB.Historical.Ramanujan
