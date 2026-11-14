import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import ModularFormsKB.Citation
/-!
# Kronecker's series `Ser_ρ` and its general transformation law

Kronecker, *Zur Theorie der elliptischen Functionen* (Werke 5, ed. Hensel, 1930, I, art. XXI), § 3, (D),
p. 111: for `u₀ = σ₀ v + τ₀ w` with real `σ₀, τ₀ ∉ ℤ`, `v/w ∉ ℝ`, an integer `ρ ≥ 0` and `u + mv + nw ≠ 0`,

  `Ser_ρ(u₀, u, v, w) = lim_{M → ∞} ∑_{m = -M}^{M} ∑_{n = -M}^{M} e^{(nσ₀ - mτ₀)2πi} / (u + mv + nw)^{1+ρ}`.

§ 7, (E), p. 118:
for integers `α, α', β, β', γ, γ', γ₀, γ₀'` with `αβ' - α'β = 1`, writing `u = σv + τw` and

  `σ₀' = ασ₀ + βτ₀ + γ₀`, `τ₀' = α'σ₀ + β'τ₀ + γ₀'`, `σ' = ασ + βτ + γ`, `τ' = α'σ + β'τ + γ'`,
  `v' = β'v - α'w`, `w' = -βv + αw`, `u' = σ'v' + τ'w'`,

  `Ser_ρ(u₀, u, v, w) = e^{((αγ' - α'γ)σ₀ + (βγ' - β'γ)τ₀)2πi} Ser_ρ(u₀', u', v', w')`.

## What is formalized

`ser ρ σ₀ τ₀ u v w` is Kronecker's square limit (D), with `u₀` given by its coordinates `σ₀, τ₀`.

* `ser_transformation_of_two_le`: the law (E) for `ρ ≥ 2`, where the series converges absolutely (Kronecker
  remarks this himself, p. 111) and (E) is a rearrangement. **Proved.**
* `SerTransformationLaw ρ`: the law (E) for a given `ρ`, as a named proposition. For `ρ = 0, 1` the series
  converges only conditionally and Kronecker's proof (the bound (B), the vanishing of the boundary sums (C),
  and continuity in `σ₀, τ₀`, §§ 2–5) is not formalized; the cases `ρ = 0, 1` are the loose end.

The numerical check `Ser₄` with `(α, β, α', β') = (2, 1, 3, 2)` and nonzero shifts agrees to `5·10⁻⁷`
(truncation `|m|, |n| ≤ 50`).
-/

noncomputable section

open Complex Filter Finset
open scoped Real

namespace ModularFormsKB.Historical.Kronecker

/-- The summand of Kronecker's `Ser_ρ`: `e^{(nσ₀ - mτ₀)2πi} / (u + mv + nw)^{1+ρ}`. -/
def serTerm (ρ : ℕ) (σ₀ τ₀ : ℝ) (u v w : ℂ) (m n : ℤ) : ℂ :=
  cexp ((n * σ₀ - m * τ₀ : ℝ) * (2 * π * I)) / (u + m * v + n * w) ^ (1 + ρ)

/-- **Kronecker's series** `Ser_ρ(σ₀v + τ₀w, u, v, w)` (Werke 5, I art. XXI, § 3, (D), p. 111): the limit of
the square partial sums `∑_{|m| ≤ M} ∑_{|n| ≤ M}` of `serTerm`. (Kronecker proves that the limit exists under
his hypotheses; `limUnder` returns a junk value otherwise.) -/
@[kb "kronecker1930" "I, art. XXI, § 3, (D), p. 111"]
def ser (ρ : ℕ) (σ₀ τ₀ : ℝ) (u v w : ℂ) : ℂ :=
  limUnder atTop fun M : ℕ ↦
    ∑ m ∈ Icc (-(M : ℤ)) M, ∑ n ∈ Icc (-(M : ℤ)) M, serTerm ρ σ₀ τ₀ u v w m n

/-- **Kronecker's general transformation law (E)** for a given `ρ` (Werke 5, I art. XXI, § 7, (E), p. 118),
as a proposition: under Kronecker's hypotheses (`v/w ∉ ℝ`, no integer among `σ₀, τ₀, σ₀', τ₀'`, `u` and `u'`
off the lattices), `Ser_ρ(u₀, u, v, w) = e^{((αγ' - α'γ)σ₀ + (βγ' - β'γ)τ₀)2πi} Ser_ρ(u₀', u', v', w')`. -/
def SerTransformationLaw (ρ : ℕ) : Prop :=
  ∀ (σ₀ τ₀ σ τ : ℝ) (v w : ℂ) (α α' β β' γ γ' γ₀ γ₀' : ℤ),
    (v / w).im ≠ 0 → α * β' - α' * β = 1 →
    (∀ k : ℤ, σ₀ ≠ k ∧ τ₀ ≠ k ∧ α * σ₀ + β * τ₀ + γ₀ ≠ k ∧ α' * σ₀ + β' * τ₀ + γ₀' ≠ k) →
    (∀ m n : ℤ, (σ * v + τ * w) + m * v + n * w ≠ 0) →
    ser ρ σ₀ τ₀ (σ * v + τ * w) v w =
      cexp (((α * γ' - α' * γ : ℤ) * σ₀ + (β * γ' - β' * γ : ℤ) * τ₀ : ℝ) * (2 * π * I)) *
        ser ρ (α * σ₀ + β * τ₀ + γ₀) (α' * σ₀ + β' * τ₀ + γ₀')
          ((α * σ + β * τ + γ : ℝ) * (β' * v - α' * w) + (α' * σ + β' * τ + γ' : ℝ) * (-β * v + α * w))
          (β' * v - α' * w) (-β * v + α * w)

/-! ### Absolute convergence for `ρ ≥ 2` -/

open EisensteinSeries in
private lemma summable_core (z : UpperHalfPlane) (c : ℂ) {k : ℝ} (hk : 2 < k) :
    Summable fun x : Fin 2 → ℤ ↦ ‖(x 0 : ℂ) * (z : ℂ) + x 1 + c‖ ^ (-k) := by
  have hr := r_pos z
  have ht : Filter.Tendsto (norm ∘ (id : (Fin 2 → ℤ) → (Fin 2 → ℤ))) Filter.cofinite
      Filter.atTop :=
    tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Topology.IsClosedEmbedding.id
  have hev : ∀ᶠ x : Fin 2 → ℤ in Filter.cofinite, ‖c‖ ≤ r z / 2 * ‖x‖ := by
    filter_upwards [ht.eventually_ge_atTop (2 * ‖c‖ / r z)] with x hx
    have hx' : 2 * ‖c‖ / r z ≤ ‖x‖ := hx
    rw [div_le_iff₀ hr] at hx'
    linarith
  refine Summable.of_norm_bounded_eventually
    ((summable_one_div_norm_rpow hk).mul_left ((r z / 2) ^ (-k))) ?_
  filter_upwards [hev] with x hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  by_cases hx0 : x = 0
  · subst hx0
    have : ‖c‖ ≤ 0 := by simpa using hx
    have hc : c = 0 := norm_le_zero_iff.mp this
    subst hc
    have hk0 : -k ≠ 0 := by linarith
    simp [Real.zero_rpow hk0]
  · have h1 := r_mul_max_le z hx0
    have h2 : ‖(x 0 : ℂ) * (z : ℂ) + x 1‖ ≤ ‖(x 0 : ℂ) * (z : ℂ) + x 1 + c‖ + ‖c‖ := by
      calc _ = ‖((x 0 : ℂ) * (z : ℂ) + x 1 + c) - c‖ := by rw [add_sub_cancel_right]
        _ ≤ _ := norm_sub_le _ _
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have h3 : r z / 2 * ‖x‖ ≤ ‖(x 0 : ℂ) * (z : ℂ) + x 1 + c‖ := by linarith
    rw [← Real.mul_rpow (by positivity) hxpos.le]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) h3 (by linarith)

private lemma summable_core' {z : ℂ} (hz : z.im ≠ 0) (c : ℂ) {k : ℝ} (hk : 2 < k) :
    Summable fun x : Fin 2 → ℤ ↦ ‖(x 0 : ℂ) * z + x 1 + c‖ ^ (-k) := by
  rcases lt_or_gt_of_ne hz with h | h
  · refine (summable_core ⟨starRingEnd ℂ z, by simpa using h⟩ (starRingEnd ℂ c) hk).congr
      fun x ↦ ?_
    have : (x 0 : ℂ) * starRingEnd ℂ z + x 1 + starRingEnd ℂ c =
        starRingEnd ℂ ((x 0 : ℂ) * z + x 1 + c) := by simp
    show ‖(x 0 : ℂ) * starRingEnd ℂ z + x 1 + starRingEnd ℂ c‖ ^ (-k) = _
    rw [this, Complex.norm_conj]
  · exact summable_core ⟨z, h⟩ c hk

private lemma summable_norm_rpow_lattice (u v w : ℂ) (hvw : (v / w).im ≠ 0) {k : ℝ} (hk : 2 < k) :
    Summable fun p : ℤ × ℤ ↦ ‖u + p.1 * v + p.2 * w‖ ^ (-k) := by
  have hw : w ≠ 0 := by rintro rfl; simp at hvw
  have h := summable_core' hvw (u / w) hk
  have h2 := ((finTwoArrowEquiv ℤ).symm.summable_iff
    (f := fun x : Fin 2 → ℤ ↦ ‖(x 0 : ℂ) * (v / w) + x 1 + u / w‖ ^ (-k))).mpr h
  refine (h2.mul_left (‖w‖ ^ (-k))).congr fun p ↦ ?_
  have key : u + p.1 * v + p.2 * w = w * (p.1 * (v / w) + p.2 + u / w) := by
    field_simp
    ring
  simp only [Function.comp, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [key, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

private lemma norm_cexp_real_mul (r : ℝ) : ‖cexp (r * (2 * π * I))‖ = 1 := by
  have : (r : ℂ) * (2 * π * I) = ((r * (2 * π) : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

private lemma norm_serTerm (ρ : ℕ) (σ₀ τ₀ : ℝ) (u v w : ℂ) (m n : ℤ) :
    ‖serTerm ρ σ₀ τ₀ u v w m n‖ = ‖u + m * v + n * w‖ ^ (-((1 + ρ : ℕ) : ℝ)) := by
  unfold serTerm
  rw [norm_div, norm_pow, norm_cexp_real_mul, Real.rpow_neg (norm_nonneg _), Real.rpow_natCast,
    one_div]

private lemma summable_norm_serTerm {ρ : ℕ} (hρ : 2 ≤ ρ) (σ₀ τ₀ : ℝ) (u v w : ℂ)
    (hvw : (v / w).im ≠ 0) :
    Summable fun p : ℤ × ℤ ↦ ‖serTerm ρ σ₀ τ₀ u v w p.1 p.2‖ := by
  have hk : (2 : ℝ) < ((1 + ρ : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 < 1 + ρ)
  exact (summable_norm_rpow_lattice u v w hvw hk).congr fun p ↦ (norm_serTerm ..).symm

private lemma exp_shift (A B Y : ℂ) (k : ℤ) (h : A = B + Y - k * (2 * π * I)) :
    cexp A = cexp B * cexp Y := by
  rw [h, Complex.exp_sub, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, div_one]

private lemma ser_eq_tsum {ρ : ℕ} {σ₀ τ₀ : ℝ} {u v w : ℂ}
    (hs : Summable fun p : ℤ × ℤ ↦ serTerm ρ σ₀ τ₀ u v w p.1 p.2) :
    ser ρ σ₀ τ₀ u v w = ∑' p : ℤ × ℤ, serTerm ρ σ₀ τ₀ u v w p.1 p.2 := by
  unfold ser
  apply Filter.Tendsto.limUnder_eq
  have h : Filter.Tendsto (fun s : Finset (ℤ × ℤ) ↦ ∑ p ∈ s, serTerm ρ σ₀ τ₀ u v w p.1 p.2)
      Filter.atTop (nhds (∑' p : ℤ × ℤ, serTerm ρ σ₀ τ₀ u v w p.1 p.2)) := hs.hasSum
  have hsq : Filter.Tendsto
      (fun M : ℕ ↦ (Finset.Icc (-(M : ℤ)) M) ×ˢ (Finset.Icc (-(M : ℤ)) M))
      Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro s
    refine ⟨s.sup fun p ↦ max p.1.natAbs p.2.natAbs, fun M hM p hp ↦ ?_⟩
    have h1 : max p.1.natAbs p.2.natAbs ≤ M :=
      (Finset.le_sup (f := fun p : ℤ × ℤ ↦ max p.1.natAbs p.2.natAbs) hp).trans hM
    have h2 : p.1.natAbs ≤ M := (le_max_left _ _).trans h1
    have h3 : p.2.natAbs ≤ M := (le_max_right _ _).trans h1
    simp only [Finset.mem_product, Finset.mem_Icc]
    omega
  refine (h.comp hsq).congr fun M ↦ ?_
  simp [Finset.sum_product]

/-- **Kronecker's transformation law (E) for `ρ ≥ 2`** (Werke 5, I art. XXI, § 7, (E), p. 118), in the absolutely convergent range. -/
@[kb "kronecker1930" "I, art. XXI, § 7, (E), p. 118"]
theorem ser_transformation_of_two_le {ρ : ℕ} (hρ : 2 ≤ ρ) : SerTransformationLaw ρ := by
  intro σ₀ τ₀ σ τ v w α α' β β' γ γ' γ₀ γ₀' hvw hdet _ _
  have hdetC : (α : ℂ) * β' - α' * β = 1 := by exact_mod_cast hdet
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p ↦ (β' * p.1 - β * p.2 + (β' * γ - β * γ'),
        -α' * p.1 + α * p.2 + (α * γ' - α' * γ))
      invFun := fun q ↦ (α * (q.1 - (β' * γ - β * γ')) + β * (q.2 - (α * γ' - α' * γ)),
        α' * (q.1 - (β' * γ - β * γ')) + β' * (q.2 - (α * γ' - α' * γ)))
      left_inv := fun p ↦ by
        ext
        · simp only; linear_combination p.1 * hdet
        · simp only; linear_combination p.2 * hdet
      right_inv := fun q ↦ by
        ext
        · simp only; linear_combination (q.1 - (β' * γ - β * γ')) * hdet
        · simp only; linear_combination (q.2 - (α * γ' - α' * γ)) * hdet }
  have hD : ∀ p : ℤ × ℤ,
      ((α * σ + β * τ + γ : ℝ) : ℂ) * (β' * v - α' * w) +
        ((α' * σ + β' * τ + γ' : ℝ) : ℂ) * (-β * v + α * w) +
        (p.1 : ℂ) * (β' * v - α' * w) + (p.2 : ℂ) * (-β * v + α * w) =
      ((σ : ℂ) * v + τ * w) + ((e p).1 : ℂ) * v + ((e p).2 : ℂ) * w := by
    intro p
    simp only [e, Equiv.coe_fn_mk]
    push_cast
    linear_combination ((σ : ℂ) * v + τ * w) * hdetC
  have hk : (2 : ℝ) < ((1 + ρ : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 < 1 + ρ)
  have hs := summable_norm_serTerm hρ σ₀ τ₀ ((σ : ℂ) * v + τ * w) v w hvw
  have hs0 : Summable fun p : ℤ × ℤ ↦ serTerm ρ σ₀ τ₀ ((σ : ℂ) * v + τ * w) v w p.1 p.2 :=
    Summable.of_norm hs
  rw [ser_eq_tsum hs0, ser_eq_tsum]
  · rw [← tsum_mul_left,
      ← e.tsum_eq (fun p : ℤ × ℤ ↦ serTerm ρ σ₀ τ₀ ((σ : ℂ) * v + τ * w) v w p.1 p.2)]
    refine tsum_congr fun p ↦ ?_
    unfold serTerm
    rw [hD p, ← mul_div_assoc]
    congr 1
    refine exp_shift _ _ _ (γ₀ * p.2 - γ₀' * p.1) ?_
    simp only [e, Equiv.coe_fn_mk]
    push_cast
    ring
  · refine Summable.of_norm ?_
    have hn := (e.summable_iff
      (f := fun p : ℤ × ℤ ↦ ‖serTerm ρ σ₀ τ₀ ((σ : ℂ) * v + τ * w) v w p.1 p.2‖)).mpr hs
    refine hn.congr fun p ↦ ?_
    simp only [Function.comp]
    rw [norm_serTerm, norm_serTerm, hD p]

/-- **Kronecker's invariance (E₀)** (Werke 5, I art. XXI, § 7, (E₀), p. 118): for `γ = γ' = 0` the value of
`Ser_ρ(σ₀v + τ₀w, σv + τw, v, w)` is invariant under the equivalence; here for `ρ ≥ 2`. -/
@[kb "kronecker1930" "I, art. XXI, § 7, (E₀), p. 118"]
theorem ser_invariant_of_two_le {ρ : ℕ} (hρ : 2 ≤ ρ) (σ₀ τ₀ σ τ : ℝ) (v w : ℂ) (α α' β β' γ₀ γ₀' : ℤ)
    (hvw : (v / w).im ≠ 0) (hdet : α * β' - α' * β = 1)
    (hint : ∀ k : ℤ, σ₀ ≠ k ∧ τ₀ ≠ k ∧ α * σ₀ + β * τ₀ + γ₀ ≠ k ∧ α' * σ₀ + β' * τ₀ + γ₀' ≠ k)
    (hu : ∀ m n : ℤ, (σ * v + τ * w) + m * v + n * w ≠ 0) :
    ser ρ σ₀ τ₀ (σ * v + τ * w) v w =
      ser ρ (α * σ₀ + β * τ₀ + γ₀) (α' * σ₀ + β' * τ₀ + γ₀')
        ((α * σ + β * τ : ℝ) * (β' * v - α' * w) + (α' * σ + β' * τ : ℝ) * (-β * v + α * w))
        (β' * v - α' * w) (-β * v + α * w) := by
  have h := ser_transformation_of_two_le hρ σ₀ τ₀ σ τ v w α α' β β' 0 0 γ₀ γ₀' hvw hdet hint hu
  simpa using h

end ModularFormsKB.Historical.Kronecker
