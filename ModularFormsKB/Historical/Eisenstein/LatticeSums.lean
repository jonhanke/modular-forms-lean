import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import ModularFormsKB.Historical.Eisenstein.LatticeSumsAux
import ModularFormsKB.Citation
/-!
# Eisenstein: lattice sums, the order of summation, and the transformation law (1847)

Eisenstein, *Genaue Untersuchung der unendlichen Doppelproducte, aus welchen die elliptischen Functionen
als Quotienten zusammengesetzt sind*, Crelle 35 (1847), reprinted as *Beiträge zur Theorie der elliptischen
Functionen* VI in his *Mathematische Abhandlungen* (1847); page numbers are those of the *Abhandlungen*,.

For complex `α, β, γ` with `α/β` not real, Eisenstein studies the sums `∑ f(αm + βn + γ)` over all integers
`m, n`, in particular `∑ (αm + βn + γ)^{-g}`, summed in his order: first over `m`, then over `n`.

* `finite_lattice_points` (§ 1, p. 215): only finitely many `(m, n)` give
  `|αm + βn + γ| ≤ R`.
* `tsum_basis_change` (§ 3, p. 240): a sum converging independently of the order of its
  terms is unchanged by a unimodular change of basis `α' = λα + νβ`, `β' = μα + ρβ`, `λρ - μν = ±1`.
* `eisensteinOne_sub_tendsto` (§ 3, pp. 237–238): Eisenstein's weight-one sum
  `∑_n ∑_m (αm + βn + γ)^{-1}` is periodic with period `α` and grows by `δ · 2νπi/α` under `γ ↦ γ + νβ`.
* `eisensteinTwo_add` (§ 3, p. 239): the weight-two sum `∑_n ∑_m (αm + βn + γ)^{-2}` is
  doubly periodic.
* `eisenstein_cot_formula` (§ 4, p. 272): for `g ≥ 2`,
  `∑_n ∑_m (αm + βn + γ)^{-g} = (-1)^{g-1} π^g / ((g-1)! α^g) ∑_n cot^{(g-1)}(nη + ξ)`, `η = πβ/α`, `ξ = πγ/α`.
* `eisenstein_theoremB_of_three_le` (§ 4, Theorem B, p. 275): for `g ≥ 3` the series
  `∑_n cot^{(g-1)}(nπω + ξ)` is multiplied by `(λ + νω)^g` under `ω ↦ (μ + ρω)/(λ + νω)`, `ξ ↦ ξ/(λ + νω)`.
  The cases `g = 1, 2`, where Eisenstein's correction `Δ` appears, are the named propositions
  `EisensteinTheoremBOne`, `EisensteinTheoremBTwo`.
-/

noncomputable section

open Complex Filter Finset
open scoped Real Topology Nat

namespace ModularFormsKB.Historical.Eisenstein

/-! ### § 1: the lattice coset is discrete -/

/-- **Eisenstein, § 1, p. 215**: if `α/β` is not real, then for every bound `R`
only finitely many integer pairs `(m, n)` satisfy `|αm + βn + γ| ≤ R`. -/
@[kb "eisenstein1847" "Beiträge VI, § 1, p. 215"]
theorem finite_lattice_points {α β : ℂ} (h : (α / β).im ≠ 0) (γ : ℂ) (R : ℝ) :
    {p : ℤ × ℤ | ‖α * p.1 + β * p.2 + γ‖ ≤ R}.Finite := by
  have hβ : β ≠ 0 := by
    rintro rfl
    simp at h
  have hβn : 0 < ‖β‖ := norm_pos_iff.2 hβ
  have hc : 0 < |(α / β).im| := abs_pos.2 h
  set B : ℝ := R + ‖γ‖ with hB
  set M : ℝ := B / (‖β‖ * |(α / β).im|) with hM
  set N : ℝ := (B + ‖α‖ * M) / ‖β‖ with hN
  refine ((Set.finite_Icc (-⌈M⌉) ⌈M⌉).prod (Set.finite_Icc (-⌈N⌉) ⌈N⌉)).subset ?_
  rintro ⟨m, n⟩ hmn
  simp only [Set.mem_setOf_eq] at hmn
  have h1 : ‖α * m + β * n‖ ≤ B := by
    calc ‖α * m + β * n‖ = ‖(α * m + β * n + γ) - γ‖ := by ring_nf
      _ ≤ ‖α * m + β * n + γ‖ + ‖γ‖ := norm_sub_le _ _
      _ ≤ B := by rw [hB]; linarith
  have hαeq : α = (α / β) * β := by field_simp
  have h2 : α * m + β * n = β * ((α / β) * m + n) := by
    conv_lhs => rw [hαeq]
    ring
  have h3 : |(α / β).im| * |(m : ℝ)| ≤ ‖(α / β) * m + n‖ := by
    have := Complex.abs_im_le_norm ((α / β) * m + n)
    have e : (((α / β) * m + n).im) = (α / β).im * m := by simp
    rw [e, abs_mul] at this
    exact this
  have h4 : ‖β‖ * (|(α / β).im| * |(m : ℝ)|) ≤ B := by
    calc _ ≤ ‖β‖ * ‖(α / β) * m + n‖ := by gcongr
      _ = ‖α * m + β * n‖ := by rw [h2, norm_mul]
      _ ≤ B := h1
  have hm : |(m : ℝ)| ≤ M := by
    rw [hM, le_div_iff₀ (by positivity)]
    nlinarith
  have h5 : ‖β‖ * |(n : ℝ)| ≤ B + ‖α‖ * M := by
    have : ‖β * n‖ ≤ ‖α * m + β * n‖ + ‖α * m‖ := by
      calc ‖β * n‖ = ‖(α * m + β * n) - α * m‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    have h6 : ‖α * m‖ ≤ ‖α‖ * M := by
      rw [norm_mul]
      have : ‖(m : ℂ)‖ = |(m : ℝ)| := by simp
      rw [this]
      gcongr
    have h7 : ‖β * n‖ = ‖β‖ * |(n : ℝ)| := by
      rw [norm_mul]; simp
    linarith
  have hn : |(n : ℝ)| ≤ N := by
    rw [hN, le_div_iff₀ hβn]
    linarith
  simp only [Set.mem_prod, Set.mem_Icc]
  have hm' := abs_le.1 hm
  have hn' := abs_le.1 hn
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : (-(⌈M⌉ : ℝ)) ≤ m := by linarith [Int.le_ceil M]
    exact_mod_cast this
  · have : (m : ℝ) ≤ ⌈M⌉ := by linarith [Int.le_ceil M]
    exact_mod_cast this
  · have : (-(⌈N⌉ : ℝ)) ≤ n := by linarith [Int.le_ceil N]
    exact_mod_cast this
  · have : (n : ℝ) ≤ ⌈N⌉ := by linarith [Int.le_ceil N]
    exact_mod_cast this

/-! ### § 3: order-independent sums -/

/-- **Eisenstein, § 3, p. 240**: under the unimodular substitution
`m = λm' + μn'`, `n = νm' + ρn'`, `λρ - μν = ±1`, with `α' = λα + νβ`, `β' = μα + ρβ`, every sum
`∑ f(αm + βn + γ)` (an unordered sum over `ℤ²`, i.e. one converging independently of the order of its terms) is
unchanged when `(α, β)` is replaced by `(α', β')`. -/
@[kb "eisenstein1847" "Beiträge VI, § 3, pp. 240–241"]
theorem tsum_basis_change {E : Type*} [AddCommGroup E] [TopologicalSpace E] (f : ℂ → E)
    (α β γ : ℂ) (l μ ν ρ : ℤ) (hdet : l * ρ - μ * ν = 1 ∨ l * ρ - μ * ν = -1) :
    ∑' p : ℤ × ℤ, f ((l * α + ν * β) * p.1 + (μ * α + ρ * β) * p.2 + γ) =
      ∑' p : ℤ × ℤ, f (α * p.1 + β * p.2 + γ) := by
  have hdd : (l * ρ - μ * ν) * (l * ρ - μ * ν) = 1 := by
    rcases hdet with h | h <;> rw [h] <;> norm_num
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (l * p.1 + μ * p.2, ν * p.1 + ρ * p.2)
      invFun := fun q => ((l * ρ - μ * ν) * (ρ * q.1 - μ * q.2),
        (l * ρ - μ * ν) * (-ν * q.1 + l * q.2))
      left_inv := by
        intro p
        ext
        · simp only
          linear_combination p.1 * hdd
        · simp only
          linear_combination p.2 * hdd
      right_inv := by
        intro q
        ext
        · simp only
          linear_combination q.1 * hdd
        · simp only
          linear_combination q.2 * hdd }
  rw [← e.tsum_eq (fun q : ℤ × ℤ => f (α * q.1 + β * q.2 + γ))]
  refine tsum_congr fun p => ?_
  simp only [e, Equiv.coe_fn_mk]
  congr 1
  push_cast
  ring

/-! ### § 3: Eisenstein's order of summation in weights one and two -/

/-- The symmetric partial sums `∑_{m = -k}^{k} (αm + c)^{-1}`. -/
def symPartial (α c : ℂ) (k : ℕ) : ℂ := ∑ m ∈ Icc (-(k : ℤ)) k, 1 / (α * m + c)

/-- **The simple series** (Eisenstein, § 3, p. 237, from Euler): for `α ≠ 0` and `c ∉ αℤ`,
`∑_{m = -∞}^{∞} 1/(αm + c) = (π/α) cot(πc/α)` (symmetric partial sums). -/
@[kb "eisenstein1847" "Beiträge VI, § 3, p. 237"]
theorem tendsto_symPartial {α c : ℂ} (hα : α ≠ 0) (hc : ∀ m : ℤ, α * m + c ≠ 0) :
    Tendsto (symPartial α c) atTop (𝓝 (π / α * Complex.cot (π * c / α))) := by
  have hx : c / α ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    apply hc (-n)
    have : c = α * n := by rw [hn]; field_simp
    rw [this]; push_cast; ring
  have hcx : c = α * (c / α) := by field_simp
  set x := c / α with hxdef
  have key : ∀ k : ℕ, symPartial α c k = 1 / α * (1 / x + ∑ j ∈ range k, cotTerm x j) := by
    intro k
    have hsplit : ∀ f : ℤ → ℂ, ∀ k : ℕ, ∑ m ∈ Icc (-(k : ℤ)) k, f m =
        f 0 + ∑ j ∈ range k, (f ((j : ℤ) + 1) + f (-((j : ℤ) + 1))) := by
      intro f k
      induction k with
      | zero => simp
      | succ k ih =>
        have : Icc (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) =
            insert (-((k : ℤ) + 1)) (insert ((k : ℤ) + 1) (Icc (-(k : ℤ)) k)) := by
          ext m; simp only [mem_Icc, mem_insert]; push_cast; omega
        rw [this, sum_insert (by simp only [mem_insert, mem_Icc]; omega),
          sum_insert (by simp only [mem_Icc]; omega), ih, sum_range_succ]
        ring
    unfold symPartial
    rw [hsplit]
    rw [mul_add, mul_sum]
    congr 1
    · simp [hcx]
      ring
    · refine sum_congr rfl fun j _ => ?_
      simp only [cotTerm]
      rw [hcx]
      push_cast
      rw [show α * ((j : ℂ) + 1) + α * x = α * (x + (j + 1)) by ring,
        show α * (-((j : ℂ) + 1)) + α * x = α * (x - (j + 1)) by ring]
      simp only [one_div, mul_inv]
      ring
  have := ((tendsto_logDeriv_euler_cot_sub hx).const_add (1 / x)).const_mul (1 / α)
  have e : 1 / α * (1 / x + (↑π * Complex.cot (↑π * x) - 1 / x)) =
      π / α * Complex.cot (π * c / α) := by
    have : (π : ℂ) * c / α = π * x := by rw [hxdef]; ring
    rw [this]; ring
  rw [← e]
  exact this.congr' (Eventually.of_forall fun k => (key k).symm)

/-- Eisenstein's sign `δ`: `+1` if the coefficient of `i` in `α/β` is positive, `-1` otherwise. -/
def eisensteinDelta (α β : ℂ) : ℂ := if 0 < (α / β).im then 1 else -1

/-- The inner sums of Eisenstein's weight-one series: `∑_{m} 1/(αm + βn + γ)` (symmetric order), as a limit. -/
def innerOne (α β γ : ℂ) (n : ℤ) : ℂ := limUnder atTop (symPartial α (β * n + γ))

/-- The partial Eisenstein sums of weight one: `∑_{n = -l}^{l} ∑_{m = -∞}^{∞} 1/(αm + βn + γ)`. -/
def eisensteinOnePartial (α β γ : ℂ) (l : ℕ) : ℂ := ∑ n ∈ Icc (-(l : ℤ)) l, innerOne α β γ n

/-- The inner sum of the weight-one series, in closed form. -/
lemma innerOne_eq {α β : ℂ} (hα : α ≠ 0) (ξ : ℂ)
    (hξ : ∀ m n : ℤ, α * m + β * n + ξ ≠ 0) (n : ℤ) :
    innerOne α β ξ n = π / α * Complex.cot (π * (β * n + ξ) / α) :=
  (tendsto_symPartial hα (fun m ↦ by rw [← add_assoc]; exact hξ m n)).limUnder_eq

lemma im_div_swap {α β : ℂ} (h : (α / β).im ≠ 0) :
    (β / α).im = -(α / β).im / Complex.normSq (α / β) := by
  have : β / α = (α / β)⁻¹ := (inv_div α β).symm
  rw [this, Complex.inv_im]

lemma cot_direction (b a : ℂ) (hb : b.im ≠ 0) :
    Tendsto (fun l : ℕ ↦ Complex.cot ((l : ℂ) * b + a)) atTop
      (𝓝 (if b.im < 0 then I else -I)) := by
  have him : ∀ l : ℕ, (((l : ℂ) * b + a)).im = l * b.im + a.im := fun l ↦ by simp
  split_ifs with h
  · apply tendsto_cot_of_im_atBot
    simp_rw [him]
    exact tendsto_atBot_add_const_right _ _
      (by simpa [mul_comm] using tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg h)
  · apply tendsto_cot_of_im_atTop
    simp_rw [him]
    have : 0 < b.im := lt_of_le_of_ne (not_lt.1 h) (Ne.symm hb)
    exact tendsto_atTop_add_const_right _ _
      (by simpa [mul_comm] using tendsto_natCast_atTop_atTop.atTop_mul_const this)

/-- **Eisenstein, § 3, pp. 237–238**, the limits of the inner sums:
`lim_{l → ∞} ∑_m 1/(αm ± βl + ξ) = ±δ πi/α`. -/
@[kb "eisenstein1847" "Beiträge VI, § 3, pp. 237–238"]
theorem tendsto_innerOne {α β : ℂ} (hα : α ≠ 0) (h : (α / β).im ≠ 0) (ξ : ℂ)
    (hξ : ∀ m n : ℤ, α * m + β * n + ξ ≠ 0) :
    Tendsto (fun l : ℕ ↦ innerOne α β ξ l) atTop (𝓝 (eisensteinDelta α β * π * I / α)) ∧
      Tendsto (fun l : ℕ ↦ innerOne α β ξ (-(l : ℤ))) atTop (𝓝 (-(eisensteinDelta α β * π * I / α))) := by
  have hN : 0 < Complex.normSq (α / β) := by
    apply Complex.normSq_pos.2
    intro h0; apply h; rw [h0]; simp
  have hsw := im_div_swap h
  set b : ℂ := π * β / α with hb
  set a : ℂ := π * ξ / α with ha
  have hbim : b.im = π * (β / α).im := by
    rw [hb, mul_div_assoc]; simp
  have hlt : b.im < 0 ↔ 0 < (α / β).im := by
    rw [hbim, hsw]
    constructor
    · intro hh
      by_contra hc
      have : 0 ≤ -(α / β).im / Complex.normSq (α / β) := by
        apply div_nonneg _ hN.le
        linarith [not_lt.1 hc]
      nlinarith [Real.pi_pos]
    · intro hh
      have : -(α / β).im / Complex.normSq (α / β) < 0 :=
        div_neg_of_neg_of_pos (by linarith) hN
      nlinarith [Real.pi_pos]
  have hbne : b.im ≠ 0 := by
    intro h0
    rw [hbim] at h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact Real.pi_ne_zero h1
    · rw [hsw] at h1
      rcases div_eq_zero_iff.1 h1 with h2 | h2
      · exact h (by linarith)
      · exact hN.ne' h2
  have hz : ∀ l : ℕ, π * (β * ((l : ℕ) : ℤ) + ξ) / α = (l : ℂ) * b + a := fun l ↦ by
    rw [hb, ha]; push_cast; ring
  have hz' : ∀ l : ℕ, π * (β * ((-((l : ℕ) : ℤ) : ℤ) : ℂ) + ξ) / α = (l : ℂ) * (-b) + a := fun l ↦ by
    rw [hb, ha]; push_cast; ring
  have hbim' : (-b).im ≠ 0 := by simpa using hbne
  have hd : eisensteinDelta α β = if 0 < (α / β).im then 1 else -1 := rfl
  constructor
  · simp_rw [innerOne_eq hα ξ hξ, hz]
    have := (cot_direction b a hbne).const_mul (π / α)
    convert this using 2
    rw [hd]
    by_cases hp : 0 < (α / β).im
    · simp [hp, hlt.2 hp]; ring
    · have : ¬ b.im < 0 := fun hh ↦ hp (hlt.1 hh)
      simp [hp, this]; ring
  · simp_rw [innerOne_eq hα ξ hξ, hz']
    have := (cot_direction (-b) a hbim').const_mul (π / α)
    convert this using 2
    rw [hd]
    by_cases hp : 0 < (α / β).im
    · have hb1 : b.im < 0 := hlt.2 hp
      have hb1' : ¬ 0 < b.im := not_lt.2 hb1.le
      simp [hp, hb1, hb1']; ring
    · have hb2' : ¬ b.im < 0 := fun hh ↦ hp (hlt.1 hh)
      have hb2 : 0 < b.im := lt_of_le_of_ne (not_lt.1 hb2') (Ne.symm hbne)
      simp [hp, hb2, hb2']; ring

lemma cot_add_int_mul_pi (z : ℂ) (l : ℤ) : Complex.cot (z + l * π) = Complex.cot z := by
  have : Complex.exp (2 * I * (z + l * π)) = Complex.exp (2 * I * z) := by
    have h := Complex.exp_int_mul_two_pi_mul_I l
    rw [show 2 * I * (z + l * π) = 2 * I * z + l * (2 * π * I) by ring, Complex.exp_add, h, mul_one]
  rw [Complex.cot_eq_exp_ratio, Complex.cot_eq_exp_ratio, this]

lemma sum_Icc_shift_succ (c : ℤ → ℂ) (a b : ℤ) (h : a ≤ b + 1) :
    ∑ n ∈ Icc (a + 1) (b + 1), c n = ∑ n ∈ Icc a b, c n + c (b + 1) - c a := by
  have h1 : Icc a (b + 1) = insert (b + 1) (Icc a b) := by
    ext m; simp only [mem_Icc, mem_insert]; omega
  have h2 : Icc a (b + 1) = insert a (Icc (a + 1) (b + 1)) := by
    ext m; simp only [mem_Icc, mem_insert]; omega
  have e1 : ∑ n ∈ Icc a (b + 1), c n = c (b + 1) + ∑ n ∈ Icc a b, c n := by
    rw [h1, sum_insert (by simp)]
  have e2 : ∑ n ∈ Icc a (b + 1), c n = c a + ∑ n ∈ Icc (a + 1) (b + 1), c n := by
    rw [h2, sum_insert (by simp)]
  linear_combination e1 - e2

lemma telescope_tendsto (c : ℤ → ℂ) (A : ℂ)
    (hp : ∀ k : ℤ, Tendsto (fun L : ℕ ↦ c ((L : ℤ) + k)) atTop (𝓝 A))
    (hn : ∀ k : ℤ, Tendsto (fun L : ℕ ↦ c (-(L : ℤ) + k)) atTop (𝓝 (-A))) (ν : ℤ) :
    Tendsto (fun L : ℕ ↦ ∑ n ∈ Icc (-(L : ℤ) + ν) (L + ν), c n - ∑ n ∈ Icc (-(L : ℤ)) L, c n)
      atTop (𝓝 (2 * ν * A)) := by
  induction ν using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have key : ∀ L : ℕ, ∑ n ∈ Icc (-(L : ℤ) + (i + 1)) (L + (i + 1)), c n -
        ∑ n ∈ Icc (-(L : ℤ)) L, c n =
        (∑ n ∈ Icc (-(L : ℤ) + i) (L + i), c n - ∑ n ∈ Icc (-(L : ℤ)) L, c n)
          + c ((L : ℤ) + (i + 1)) - c (-(L : ℤ) + i) := by
      intro L
      rw [show -(L : ℤ) + (i + 1) = (-(L : ℤ) + i) + 1 by ring,
        show (L : ℤ) + (i + 1) = ((L : ℤ) + i) + 1 by ring,
        sum_Icc_shift_succ c _ _ (by omega)]
      ring
    simp_rw [key]
    have := (ih.add (hp (i + 1))).sub (hn i)
    convert this using 2
    push_cast; ring
  | pred i ih =>
    have key : ∀ L : ℕ, ∑ n ∈ Icc (-(L : ℤ) + (-i - 1)) (L + (-i - 1)), c n -
        ∑ n ∈ Icc (-(L : ℤ)) L, c n =
        (∑ n ∈ Icc (-(L : ℤ) + -i) (L + -i), c n - ∑ n ∈ Icc (-(L : ℤ)) L, c n)
          - c ((L : ℤ) + -i) + c (-(L : ℤ) + (-i - 1)) := by
      intro L
      have := sum_Icc_shift_succ c (-(L : ℤ) + (-i - 1)) ((L : ℤ) + (-i - 1)) (by omega)
      rw [show -(L : ℤ) + (-i - 1) + 1 = -(L : ℤ) + -i by ring,
        show (L : ℤ) + (-i - 1) + 1 = (L : ℤ) + -i by ring] at this
      linear_combination -this
    simp_rw [key]
    have := (ih.sub (hp (-i))).add (hn (-i - 1))
    convert this using 2
    push_cast; ring

/-- **Eisenstein's weight-one sum is only quasi-periodic** (§ 3, pp. 237–238):
for integers `λ, ν`, the partial Eisenstein sums satisfy
`∑_{|n| ≤ l} ∑_m 1/(αm + βn + γ + λα + νβ) - ∑_{|n| ≤ l} ∑_m 1/(αm + βn + γ) → δ · 2νπi/α`. In particular, where
Eisenstein's sum `φ(γ) = ∑_n ∑_m (αm + βn + γ)^{-1}` converges, `φ(γ + α) = φ(γ)` and
`φ(γ + νβ) = φ(γ) + δ · 2νπi/α` (`eisensteinOne_add`). -/
@[kb "eisenstein1847" "Beiträge VI, § 3, pp. 237–238"]
theorem eisensteinOne_sub_tendsto {α β : ℂ} (hα : α ≠ 0) (h : (α / β).im ≠ 0) (γ : ℂ)
    (hγ : ∀ m n : ℤ, α * m + β * n + γ ≠ 0) (l ν : ℤ) :
    Tendsto (fun L : ℕ ↦ eisensteinOnePartial α β (γ + l * α + ν * β) L - eisensteinOnePartial α β γ L)
      atTop (𝓝 (eisensteinDelta α β * 2 * ν * π * I / α)) := by
  set c : ℤ → ℂ := innerOne α β γ with hc
  have hγ' : ∀ k : ℤ, ∀ m n : ℤ, α * m + β * n + (γ + k * β) ≠ 0 := by
    intro k m n
    have := hγ m (n + k)
    push_cast at this
    intro h0; apply this; linear_combination h0
  have hshift : ∀ k n : ℤ, c (n + k) = innerOne α β (γ + k * β) n := by
    intro k n
    rw [hc]
    rw [innerOne_eq hα γ hγ, innerOne_eq hα (γ + k * β) (hγ' k)]
    congr 3
    push_cast; ring
  have hp : ∀ k : ℤ, Tendsto (fun L : ℕ ↦ c ((L : ℤ) + k)) atTop
      (𝓝 (eisensteinDelta α β * π * I / α)) := fun k ↦ by
    simp_rw [hshift]
    exact (tendsto_innerOne hα h (γ + k * β) (hγ' k)).1
  have hn : ∀ k : ℤ, Tendsto (fun L : ℕ ↦ c (-(L : ℤ) + k)) atTop
      (𝓝 (-(eisensteinDelta α β * π * I / α))) := fun k ↦ by
    simp_rw [hshift]
    exact (tendsto_innerOne hα h (γ + k * β) (hγ' k)).2
  have hT := telescope_tendsto c _ hp hn ν
  have hper : ∀ n : ℤ, innerOne α β (γ + l * α + ν * β) n = c (n + ν) := by
    intro n
    have hh : ∀ m n : ℤ, α * m + β * n + (γ + l * α + ν * β) ≠ 0 := by
      intro m n
      have := hγ (m + l) (n + ν)
      push_cast at this
      intro h0; apply this; linear_combination h0
    rw [hc]
    rw [innerOne_eq hα _ hh, innerOne_eq hα γ hγ]
    have : π * (β * (n : ℂ) + (γ + l * α + ν * β)) / α =
        π * (β * ((n + ν : ℤ) : ℂ) + γ) / α + l * π := by
      push_cast; field_simp; ring
    rw [this, cot_add_int_mul_pi]
  have hpart : ∀ L : ℕ, eisensteinOnePartial α β (γ + l * α + ν * β) L - eisensteinOnePartial α β γ L =
      ∑ n ∈ Icc (-(L : ℤ) + ν) (L + ν), c n - ∑ n ∈ Icc (-(L : ℤ)) L, c n := by
    intro L
    unfold eisensteinOnePartial
    simp_rw [hper]
    rw [← Finset.map_add_right_Icc, Finset.sum_map]
    rfl
  simp_rw [hpart]
  convert hT using 2
  ring

/-- The same, for the limits: if Eisenstein's weight-one sum converges at `γ` to `φ`, it converges at
`γ + λα + νβ` to `φ + δ · 2νπi/α`. -/
@[kb "eisenstein1847" "Beiträge VI, § 3, pp. 237–239"]
theorem eisensteinOne_add {α β : ℂ} (hα : α ≠ 0) (h : (α / β).im ≠ 0) (γ : ℂ)
    (hγ : ∀ m n : ℤ, α * m + β * n + γ ≠ 0) (l ν : ℤ) {S : ℂ}
    (hS : Tendsto (eisensteinOnePartial α β γ) atTop (𝓝 S)) :
    Tendsto (eisensteinOnePartial α β (γ + l * α + ν * β)) atTop
      (𝓝 (S + eisensteinDelta α β * 2 * ν * π * I / α)) := by
  simpa using hS.add (eisensteinOne_sub_tendsto hα h γ hγ l ν)

/-- Eisenstein's weight-two sum `∑_n ∑_m (αm + βn + γ)^{-2}` (inner sums absolutely convergent). -/
def eisensteinTwo (α β γ : ℂ) : ℂ := ∑' n : ℤ, ∑' m : ℤ, 1 / (α * m + β * n + γ) ^ 2

/-- **Eisenstein's weight-two sum is doubly periodic** (§ 3, p. 239): its change
under `γ ↦ γ + λα + νβ` is `0`. -/
@[kb "eisenstein1847" "Beiträge VI, § 3, p. 239"]
theorem eisensteinTwo_add (α β γ : ℂ) (l ν : ℤ) :
    eisensteinTwo α β (γ + l * α + ν * β) = eisensteinTwo α β γ := by
  unfold eisensteinTwo
  have h1 : ∀ n : ℤ, ∑' m : ℤ, 1 / (α * m + β * n + (γ + l * α + ν * β)) ^ 2 =
      ∑' m : ℤ, 1 / (α * m + β * ((n + ν : ℤ) : ℂ) + γ) ^ 2 := by
    intro n
    rw [← (Equiv.addRight l).tsum_eq (fun m : ℤ => 1 / (α * m + β * ((n + ν : ℤ) : ℂ) + γ) ^ 2)]
    refine tsum_congr fun m => ?_
    simp only [Equiv.coe_addRight]
    push_cast
    ring_nf
  simp_rw [h1]
  exact (Equiv.addRight ν).tsum_eq
    (fun n : ℤ => ∑' m : ℤ, 1 / (α * m + β * (n : ℂ) + γ) ^ 2)

/-- The outer series of `eisensteinTwo` converges (absolutely), so the periodicity is a statement about a
genuine sum: `∑_m (αm + βn + γ)^{-2} = (π/α)² / sin²(π(βn + γ)/α)` decays exponentially in `|n|`. -/
@[kb "eisenstein1847" "Beiträge VI, § 3, p. 239"]
theorem summable_eisensteinTwo {α β : ℂ} (hα : α ≠ 0) (h : (α / β).im ≠ 0) (γ : ℂ)
    (hγ : ∀ m n : ℤ, α * m + β * n + γ ≠ 0) :
    Summable fun n : ℤ ↦ ∑' m : ℤ, 1 / (α * m + β * n + γ) ^ 2 := by
  have hN : 0 < Complex.normSq (α / β) := by
    apply Complex.normSq_pos.2
    intro h0; apply h; rw [h0]; simp
  have hβα : (β / α).im ≠ 0 := by
    rw [im_div_swap h]; exact div_ne_zero (neg_ne_zero.2 h) hN.ne'
  set a : ℝ := π * (β / α).im with ha_def
  set b : ℝ := π * (γ / α).im with hb_def
  have ha : a ≠ 0 := mul_ne_zero Real.pi_ne_zero hβα
  have hapos : 0 < |a| := abs_pos.2 ha
  have hzim : ∀ n : ℤ, (π * (β * n + γ) / α : ℂ).im = a * n + b := by
    intro n
    have : (π : ℂ) * (β * n + γ) / α = π * ((n : ℂ) * (β / α) + γ / α) := by ring
    rw [this, Complex.im_ofReal_mul, Complex.add_im]
    simp [ha_def, hb_def]
    ring
  have hsin : ∀ n : ℤ, Complex.sin (π * (β * n + γ) / α) ≠ 0 := by
    intro n
    have hx : ((β * n + γ) / α) ∈ Complex.integerComplement := by
      rintro ⟨j, hj⟩
      apply hγ (-j) n
      have : β * n + γ = α * j := by rw [hj]; field_simp
      push_cast
      linear_combination this
    rw [mul_div_assoc]
    exact sin_pi_mul_ne_zero hx
  have hin : ∀ n : ℤ, ‖∑' m : ℤ, 1 / (α * m + β * n + γ) ^ 2‖ =
      π ^ 2 / ‖α‖ ^ 2 * (1 / ‖Complex.sin (π * (β * n + γ) / α)‖ ^ 2) := by
    intro n
    have hc : ∀ m : ℤ, α * m + (β * n + γ) ≠ 0 := fun m ↦ by
      rw [← add_assoc]; exact hγ m n
    have := inner_tsum_eq_cot hα hc (k := 1) le_rfl
    have e : ∀ m : ℤ, α * m + β * n + γ = α * m + (β * n + γ) := fun m ↦ add_assoc _ _ _
    simp_rw [e]
    rw [this, iteratedDeriv_one, deriv_cot_eq (hsin n)]
    simp [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.pi_pos.le, abs_of_pos Real.pi_pos]
  have hbound : ∀ n : ℤ, 1 ≤ |a * n + b| → ‖∑' m : ℤ, 1 / (α * m + β * n + γ) ^ 2‖ ≤
      π ^ 2 / ‖α‖ ^ 2 * 16 * Real.exp (2 * |b|) * Real.exp (-2 * |a|) ^ n.natAbs := by
    intro n hn
    rw [hin n]
    set y := a * n + b with hy
    have hs := norm_sin_lower (π * (β * n + γ) / α) (by rw [hzim n]; exact hn)
    rw [hzim n] at hs
    have hpos : 0 < Real.exp |y| / 4 := by positivity
    have h1 : 1 / ‖Complex.sin (π * (β * n + γ) / α)‖ ^ 2 ≤ 1 / (Real.exp |y| / 4) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hpos.le hs 2)
    have h2 : 1 / (Real.exp |y| / 4) ^ 2 = 16 * Real.exp (-2 * |y|) := by
      have e2 : Real.exp (-2 * |y|) = ((Real.exp |y|) ^ 2)⁻¹ := by
        rw [show -2 * |y| = -(2 * |y|) by ring, Real.exp_neg, two_mul, Real.exp_add, sq]
      rw [e2]; field_simp; ring
    have h3 : Real.exp (-2 * |y|) ≤ Real.exp (2 * |b|) * Real.exp (-2 * |a|) ^ n.natAbs := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have h4 : |a| * |(n : ℝ)| - |b| ≤ |y| := by
        have h := abs_add_le (a * n + b) (-b)
        rw [show a * n + b + -b = a * n by ring, abs_neg, abs_mul] at h
        rw [hy]; linarith
      have h5 : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [h5]
      nlinarith
    have hK : 0 ≤ π ^ 2 / ‖α‖ ^ 2 := by positivity
    calc π ^ 2 / ‖α‖ ^ 2 * (1 / ‖Complex.sin (π * (β * n + γ) / α)‖ ^ 2)
        ≤ π ^ 2 / ‖α‖ ^ 2 * (16 * Real.exp (-2 * |y|)) := by gcongr; exact h1.trans h2.le
      _ ≤ π ^ 2 / ‖α‖ ^ 2 * (16 * (Real.exp (2 * |b|) * Real.exp (-2 * |a|) ^ n.natAbs)) := by
          gcongr
      _ = _ := by ring
  have hr : Real.exp (-2 * |a|) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  refine Summable.of_norm_bounded_eventually (g := fun n : ℤ ↦
    π ^ 2 / ‖α‖ ^ 2 * 16 * Real.exp (2 * |b|) * Real.exp (-2 * |a|) ^ n.natAbs)
    ((summable_geom_int (Real.exp_pos _).le hr).mul_left _) ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_Icc (-⌈(1 + |b|) / |a|⌉) ⌈(1 + |b|) / |a|⌉).subset ?_
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  have hlt : |a * n + b| < 1 := by
    by_contra hc; exact hn (hbound n (not_lt.1 hc))
  have h6 : |a| * |(n : ℝ)| < 1 + |b| := by
    have h := abs_add_le (a * n + b) (-b)
    rw [show a * n + b + -b = a * n by ring, abs_neg, abs_mul] at h
    linarith
  have h7 : |(n : ℝ)| ≤ (1 + |b|) / |a| := by
    rw [le_div_iff₀ hapos]; nlinarith
  have h8 := abs_le.1 h7
  simp only [Set.mem_Icc]
  constructor
  · have : (-(⌈(1 + |b|) / |a|⌉ : ℝ)) ≤ n := by linarith [Int.le_ceil ((1 + |b|) / |a|)]
    exact_mod_cast this
  · have : (n : ℝ) ≤ ⌈(1 + |b|) / |a|⌉ := by linarith [Int.le_ceil ((1 + |b|) / |a|)]
    exact_mod_cast this

/-! ### § 4: the cotangent form and Theorem B -/

/-- **Eisenstein's cotangent formula** (§ 4, p. 272): for `α ≠ 0`, `β/α` not
real, `γ` off the lattice and `g ≥ 2`, summing over `m` first,
`∑_n ∑_m 1/(αm + βn + γ)^g = (-1)^{g-1} π^g / ((g-1)! α^g) · ∑_n cot^{(g-1)}(nη + ξ)`, `η = πβ/α`, `ξ = πγ/α`. -/
@[kb "eisenstein1847" "Beiträge VI, § 4, p. 272"]
theorem eisenstein_cot_formula {α β γ : ℂ} (hα : α ≠ 0) (h : (β / α).im ≠ 0)
    (hγ : ∀ m n : ℤ, α * m + β * n + γ ≠ 0) {g : ℕ} (hg : 2 ≤ g) :
    ∑' n : ℤ, ∑' m : ℤ, 1 / (α * m + β * n + γ) ^ g =
      (-1) ^ (g - 1) * π ^ g / ((g - 1)! * α ^ g) *
        ∑' n : ℤ, iteratedDeriv (g - 1) Complex.cot (n * (π * β / α) + π * γ / α) := by
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  simp only [Nat.add_sub_cancel]
  rw [← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  have hx : ((β * n + γ) / α) ∈ Complex.integerComplement := by
    rintro ⟨j, hj⟩
    apply hγ (-j) n
    have : β * n + γ = α * j := by rw [hj]; field_simp
    push_cast
    linear_combination this
  have h1 := tsum_inv_pow_eq_iteratedDeriv_cot hk hx
  have h2 : ∀ m : ℤ, 1 / (α * m + β * n + γ) ^ (k + 1) =
      (1 / α ^ (k + 1)) * (1 / ((β * n + γ) / α + m) ^ (k + 1)) := by
    intro m
    have : α * m + β * n + γ = α * ((β * n + γ) / α + m) := by field_simp; ring
    rw [this, mul_pow, one_div, one_div, one_div, mul_inv]
  simp_rw [h2]
  rw [tsum_mul_left, h1]
  have e : (π : ℂ) * ((β * n + γ) / α) = n * (π * β / α) + π * γ / α := by field_simp
  rw [e]
  have hf : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

/-- Eisenstein's series `F_g(ω, ξ) = ∑_n ∂^{g-1}/∂ξ^{g-1} cot(nπω + ξ)` (§ 4, p. 273).
**Restriction:** the series converges absolutely for `Im ω ≠ 0` and `g ≥ 2` (the derivatives of `cot` decay
exponentially in `n`); for `Im ω ≠ 0` and `g ≤ 1` it diverges (the terms tend to `∓i`). Elsewhere the value is `0` by
Lean's convention for a non-summable `∑'`, not an analytic continuation or the intended value. -/
def eisensteinF (g : ℕ) (ω ξ : ℂ) : ℂ := ∑' n : ℤ, iteratedDeriv (g - 1) Complex.cot (n * π * ω + ξ)

/-- Absolute summability of the shifted lattice sum of weight `g ≥ 3`. -/
lemma summable_shifted_lattice {g : ℕ} (hg : 3 ≤ g) {ω : ℂ} (hω : ω.im ≠ 0) (ξ : ℂ) :
    Summable fun p : ℤ × ℤ ↦ 1 / ((π : ℂ) * ω * p.1 + π * p.2 + ξ) ^ g := by
  have hfin : {p : ℤ × ℤ | ‖(π : ℂ) * ω * p.1 + π * p.2 + 0‖ ≤ 2 * ‖ξ‖}.Finite := by
    refine finite_lattice_points (α := (π : ℂ) * ω) (β := π) ?_ 0 _
    have : ((π : ℂ) * ω / π) = ω := mul_div_cancel_left₀ _ (by exact_mod_cast Real.pi_ne_zero)
    rw [this]; exact hω
  refine Summable.of_norm_bounded_eventually (g := fun p : ℤ × ℤ ↦
    2 ^ g * ‖1 / ((π : ℂ) * ω * p.1 + π * p.2) ^ g‖)
    ((summable_norm_lattice hg hω).mul_left _) ?_
  rw [Filter.eventually_cofinite]
  refine hfin.subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  rw [add_zero]
  by_contra hc
  apply hp
  set x : ℂ := (π : ℂ) * ω * p.1 + π * p.2 with hx
  have hc' : 2 * ‖ξ‖ < ‖x‖ := not_le.1 hc
  have hxpos : 0 < ‖x‖ := by have := norm_nonneg ξ; linarith
  have h1 : ‖x‖ / 2 ≤ ‖x + ξ‖ := by
    have := norm_sub_le x (-ξ)
    have h2 : ‖x‖ ≤ ‖x + ξ‖ + ‖ξ‖ := by
      calc ‖x‖ = ‖(x + ξ) - ξ‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith
  have h3 : (‖x‖ / 2) ^ g ≤ ‖x + ξ‖ ^ g := pow_le_pow_left₀ (by positivity) h1 g
  simp only [norm_div, norm_one, norm_pow]
  calc 1 / ‖x + ξ‖ ^ g ≤ 1 / (‖x‖ / 2) ^ g :=
        one_div_le_one_div_of_le (by positivity) h3
    _ = 2 ^ g * (1 / ‖x‖ ^ g) := by rw [div_pow]; field_simp

/-- The iterated sum of Eisenstein's `F_g` equals the unordered lattice sum. -/
lemma eisensteinF_const_mul {ω ξ : ℂ} (hω : ω.im ≠ 0)
    (hξ : ∀ m n : ℤ, π * m + π * ω * n ≠ ξ) {g : ℕ} (hg : 3 ≤ g) :
    ((-1) ^ (g - 1) * (π : ℂ) ^ g / ((g - 1)! * (π : ℂ) ^ g)) * eisensteinF g ω ξ =
      ∑' p : ℤ × ℤ, 1 / ((π : ℂ) * ω * p.1 + π * p.2 + ξ) ^ g := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hγ : ∀ m n : ℤ, (π : ℂ) * m + (π * ω) * n + ξ ≠ 0 := by
    intro m n h0
    apply hξ (-m) (-n)
    push_cast
    linear_combination (-1 : ℂ) * h0
  have h := eisenstein_cot_formula (α := (π : ℂ)) (β := π * ω) (γ := ξ) hπ
    (by rw [mul_div_cancel_left₀ _ hπ]; exact hω) hγ (by omega : 2 ≤ g)
  have e : ∀ n : ℤ, (n : ℂ) * (π * (π * ω) / π) + π * ξ / π = n * π * ω + ξ := by
    intro n; field_simp
  simp_rw [e] at h
  have hs := summable_shifted_lattice hg hω ξ
  rw [hs.tsum_prod' (fun n ↦ hs.prod_factor n), eisensteinF, ← h]
  refine tsum_congr fun n ↦ tsum_congr fun m ↦ ?_
  congr 2
  ring

/-- **Eisenstein's Theorem B for `g ≥ 3`** (§ 4, p. 275): for `ω` not real,
`ξ ∉ π(ℤ + ℤω)` and integers with `λρ - μν = ±1`, replacing `ω` by `(μ + ρω)/(λ + νω)` and `ξ` by
`ξ/(λ + νω)` multiplies `∑_n cot^{(g-1)}(nπω + ξ)` by `(λ + νω)^g` (Eisenstein's `Δ` is `0` for `g > 2`). -/
@[kb "eisenstein1847" "Beiträge VI, § 4, Theorem B, p. 275"]
theorem eisenstein_theoremB_of_three_le {ω : ℂ} (hω : ω.im ≠ 0) {ξ : ℂ}
    (hξ : ∀ m n : ℤ, π * m + π * ω * n ≠ ξ) (l μ ν ρ : ℤ)
    (hdet : l * ρ - μ * ν = 1 ∨ l * ρ - μ * ν = -1) {g : ℕ} (hg : 3 ≤ g) :
    eisensteinF g ((μ + ρ * ω) / (l + ν * ω)) (ξ / (l + ν * ω)) = (l + ν * ω) ^ g * eisensteinF g ω ξ := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hdetC : (l : ℂ) * ρ - μ * ν ≠ 0 := by
    have h0 : ((l * ρ - μ * ν : ℤ) : ℂ) ≠ 0 := by
      rcases hdet with h | h <;> rw [h] <;> norm_num
    simpa using h0
  have hc : (l : ℂ) + ν * ω ≠ 0 := by
    intro h0
    have him : (ν : ℝ) * ω.im = 0 := by simpa using congrArg Complex.im h0
    rcases mul_eq_zero.1 him with h1 | h1
    · have hν : ν = 0 := by exact_mod_cast h1
      subst hν
      apply hdetC
      simp at h0 ⊢
      rw [h0]; simp
    · exact hω h1
  set c : ℂ := l + ν * ω with hcdef
  have hω' : ((μ + ρ * ω) / c).im ≠ 0 := by
    have hcn : 0 < Complex.normSq c := Complex.normSq_pos.2 hc
    have : ((μ + ρ * ω) / c).im = ω.im * ((l : ℂ) * ρ - μ * ν).re / Complex.normSq c := by
      rw [Complex.div_im, hcdef]
      simp
      ring
    rw [this]
    have hre : ((l : ℂ) * ρ - μ * ν).re ≠ 0 := by
      intro h0; apply hdetC; apply Complex.ext
      · simpa using h0
      · simp
    exact div_ne_zero (mul_ne_zero hω hre) hcn.ne'
  have hξ' : ∀ m n : ℤ, π * m + π * ((μ + ρ * ω) / c) * n ≠ ξ / c := by
    intro m n h0
    apply hξ (l * m + μ * n) (ν * m + ρ * n)
    have : ((π : ℂ) * m + π * ((μ + ρ * ω) / c) * n) * c = ξ / c * c := by rw [h0]
    rw [div_mul_cancel₀ _ hc] at this
    have e : ((π : ℂ) * m + π * ((μ + ρ * ω) / c) * n) * c = π * m * c + π * (μ + ρ * ω) * n := by
      field_simp
    rw [e, hcdef] at this
    push_cast
    linear_combination this
  have h1 := eisensteinF_const_mul hω' hξ' hg
  have h2 := eisensteinF_const_mul hω hξ hg
  have hS : ∑' p : ℤ × ℤ, 1 / ((π : ℂ) * ((μ + ρ * ω) / c) * p.1 + π * p.2 + ξ / c) ^ g =
      c ^ g * ∑' p : ℤ × ℤ, 1 / ((π : ℂ) * ω * p.1 + π * p.2 + ξ) ^ g := by
    have hdet' : (ρ : ℤ) * l - ν * μ = 1 ∨ (ρ : ℤ) * l - ν * μ = -1 := by
      rcases hdet with h | h
      · left; linarith
      · right; linarith
    have hb := tsum_basis_change (fun z : ℂ ↦ 1 / z ^ g) ((π : ℂ) * ω) π ξ ρ ν μ l hdet'
    rw [← hb, ← tsum_mul_left]
    refine tsum_congr fun p ↦ ?_
    have : (π : ℂ) * ((μ + ρ * ω) / c) * p.1 + π * p.2 + ξ / c =
        (((ρ : ℂ) * (π * ω) + μ * π) * p.1 + (ν * (π * ω) + l * π) * p.2 + ξ) / c := by
      field_simp; rw [hcdef]; ring
    rw [this, div_pow]
    field_simp
  have hk : ((-1) ^ (g - 1) * (π : ℂ) ^ g / ((g - 1)! * (π : ℂ) ^ g)) ≠ 0 := by
    have hf : (((g - 1)! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (pow_ne_zero _ hπ))
      (mul_ne_zero hf (pow_ne_zero _ hπ))
  apply mul_left_cancel₀ hk
  rw [h1, hS, ← h2]
  ring

/-- Eisenstein's sign in Theorem B: `-δ` is the sign of the coefficient of `i` in `ω`. -/
def thmBDelta (ω : ℂ) : ℂ := if 0 < ω.im then -1 else 1

/-- **Theorem B for `g = 2`** (§ 4, p. 275), as a proposition: the series is multiplied by `(λ + νω)²` and
increased by `Δ = -(2δνi/π)(λ + νω)`. Not proved here (loose end): it contains the transformation law of
Eisenstein's `G₂`. -/
def EisensteinTheoremBTwo : Prop :=
  ∀ (ω ξ : ℂ) (l μ ν ρ : ℤ), ω.im ≠ 0 → (∀ m n : ℤ, π * m + π * ω * n ≠ ξ) →
    (l * ρ - μ * ν = 1 ∨ l * ρ - μ * ν = -1) →
    eisensteinF 2 ((μ + ρ * ω) / (l + ν * ω)) (ξ / (l + ν * ω)) =
      (l + ν * ω) ^ 2 * eisensteinF 2 ω ξ - 2 * thmBDelta ω * ν * I / π * (l + ν * ω)

/-- The weight-one series of Theorem B, with Eisenstein's pairing of `±n`:
`cot ξ + ∑_{n ≥ 1} (cot(nπω + ξ) + cot(-nπω + ξ))`. -/
def eisensteinFOne (ω ξ : ℂ) : ℂ :=
  Complex.cot ξ + ∑' n : ℕ, (Complex.cot ((n + 1) * π * ω + ξ) + Complex.cot (-((n + 1) * π * ω) + ξ))

/-- **Theorem B for `g = 1`** (§ 4, p. 275), as a proposition: the series (`±n` paired) is multiplied by
`λ + νω` and increased by `Δ = -(2δνi/π) ξ`. Not proved here (loose end). -/
def EisensteinTheoremBOne : Prop :=
  ∀ (ω ξ : ℂ) (l μ ν ρ : ℤ), ω.im ≠ 0 → (∀ m n : ℤ, π * m + π * ω * n ≠ ξ) →
    (l * ρ - μ * ν = 1 ∨ l * ρ - μ * ν = -1) →
    eisensteinFOne ((μ + ρ * ω) / (l + ν * ω)) (ξ / (l + ν * ω)) =
      (l + ν * ω) * eisensteinFOne ω ξ - 2 * thmBDelta ω * ν * I / π * ξ

end ModularFormsKB.Historical.Eisenstein
