import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ModularFormsKB.Citation
/-!
# Miyake §1.7: the quotient $\Gamma\backslash\mathbb H^*$

Miyake, *Modular Forms* (Springer 1989), §1.7, pp. 23–28. Here: Lemma 1.7.3, the lower-left
entry bound for a Fuchsian group with a cusp at $\infty$ (a form of Shimizu's lemma), used by
Miyake to separate cusp neighborhoods.

## Conventions
* A Fuchsian group is a discrete subgroup $\Gamma$ of $\mathrm{SL}_2(\mathbb R)$: a
  `Subgroup SL(2, ℝ)` with `DiscreteTopology Γ`, where `SL(2, ℝ)` carries the subspace topology of
  $2\times 2$ real matrices.
* Matrix entries are 0-based: Miyake's $c$ is `γ 1 0`.
* $\tau_h = \begin{pmatrix} 1 & h \\ 0 & 1\end{pmatrix}$ is `translationSL h`.
-/

open Matrix
open scoped MatrixGroups

namespace ModularFormsKB.Miyake

/-- The translation $\tau_h = \begin{pmatrix} 1 & h \\ 0 & 1\end{pmatrix} \in \mathrm{SL}_2(\mathbb R)$,
acting on $\mathbb H$ by $z \mapsto z + h$. -/
def translationSL (h : ℝ) : SL(2, ℝ) :=
  ⟨!![1, h; 0, 1], by simp [Matrix.det_fin_two_of]⟩


/-- Iterated conjugation of `σ` by `γ`: `γ₀ = γ`, `γₙ₊₁ = γₙ σ γₙ⁻¹`. -/
def conjSeq (σ γ : SL(2, ℝ)) : ℕ → SL(2, ℝ)
  | 0 => γ
  | n + 1 => conjSeq σ γ n * σ * (conjSeq σ γ n)⁻¹

/-- The iterates `conjSeq σ γ n` stay in a subgroup containing `σ` and `γ`. -/
lemma conjSeq_mem (Γ : Subgroup SL(2, ℝ)) {σ γ : SL(2, ℝ)} (hσ : σ ∈ Γ) (hγ : γ ∈ Γ) (n : ℕ) :
    conjSeq σ γ n ∈ Γ := by
  induction n with
  | zero => exact hγ
  | succ n ih => exact Γ.mul_mem (Γ.mul_mem ih hσ) (Γ.inv_mem ih)

/-- Entries of `x σ x⁻¹` for `σ = ε · τ_h`. -/
lemma conj_entries (x σ : SL(2, ℝ)) (ε h : ℝ) (h00 : σ 0 0 = ε) (h01 : σ 0 1 = ε * h)
    (h10 : σ 1 0 = 0) (h11 : σ 1 1 = ε) :
    (x * σ * x⁻¹) 0 0 = ε * (1 - x 0 0 * x 1 0 * h) ∧
    (x * σ * x⁻¹) 0 1 = ε * (x 0 0 ^ 2 * h) ∧
    (x * σ * x⁻¹) 1 0 = -ε * h * x 1 0 ^ 2 ∧
    (x * σ * x⁻¹) 1 1 = ε * (1 + x 0 0 * x 1 0 * h) := by
  have hd : x 0 0 * x 1 1 - x 0 1 * x 1 0 = 1 := by
    have := x.2
    rw [Matrix.det_fin_two] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, h00, h01, h10, h11]
    first | ring1 | linear_combination ε * hd

/-- Isolation of points of a discrete subgroup. -/
lemma exists_isolating (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ] {x : SL(2, ℝ)} (hx : x ∈ Γ) :
    ∃ U : Set SL(2, ℝ), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ Γ, y ∈ U → y = x := by
  have h1 : IsOpen ({⟨x, hx⟩} : Set Γ) := isOpen_discrete _
  rw [isOpen_induced_iff] at h1
  obtain ⟨U, hU, hU'⟩ := h1
  refine ⟨U, hU, ?_, ?_⟩
  · have : (⟨x, hx⟩ : Γ) ∈ Subtype.val ⁻¹' U := by rw [hU']; rfl
    exact this
  · intro y hy hyU
    have : (⟨y, hy⟩ : Γ) ∈ Subtype.val ⁻¹' U := hyU
    rw [hU'] at this
    exact congrArg Subtype.val this

/-- **Miyake, Lemma 1.7.3.** Let $\Gamma \subset \mathrm{SL}_2(\mathbb R)$ be discrete and $h > 0$ with
$\tau_h \in \Gamma\{\pm 1\}$ (Miyake assumes $\infty$ is a cusp and
$\Gamma_\infty\{\pm1\} = \{\pm\tau_h^m : m \in \mathbb Z\}$; only $\pm\tau_h \in \Gamma$ is used). If
$\gamma = \begin{pmatrix} a & b \\ c & d\end{pmatrix} \in \Gamma$ satisfies $|ch| < 1$, then $c = 0$, i.e.
$\gamma \in \Gamma_\infty$. Generalization (weaker hypothesis on $\Gamma_\infty$). -/
@[kb "miyake1989" "Lemma 1.7.3, p. 26"]
theorem lower_left_eq_zero_of_abs_lt (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ] {h : ℝ}
    (hh : 0 < h) (hτ : translationSL h ∈ Γ ∨ -translationSL h ∈ Γ) {γ : SL(2, ℝ)} (hγ : γ ∈ Γ)
    (hc : |γ 1 0 * h| < 1) : γ 1 0 = 0 := by
  -- choose σ = ε τ_h ∈ Γ
  obtain ⟨σ, ε, hσ, hε, h00, h01, h10, h11⟩ : ∃ (σ : SL(2, ℝ)) (ε : ℝ), σ ∈ Γ ∧ (ε = 1 ∨ ε = -1) ∧
      σ 0 0 = ε ∧ σ 0 1 = ε * h ∧ σ 1 0 = 0 ∧ σ 1 1 = ε := by
    rcases hτ with H | H
    · exact ⟨_, 1, H, Or.inl rfl, by simp [translationSL], by simp [translationSL],
        by simp [translationSL], by simp [translationSL]⟩
    · refine ⟨_, -1, H, Or.inr rfl, ?_, ?_, ?_, ?_⟩
      · exact (show (-translationSL h) 0 0 = -1 from rfl)
      · rw [show (-translationSL h) 0 1 = -h from rfl]; ring
      · exact (show (-translationSL h) 1 0 = 0 by
          show -(0:ℝ) = 0; simp)
      · exact (show (-translationSL h) 1 1 = -1 from rfl)
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hεabs : |ε| = 1 := by rcases hε with rfl | rfl <;> simp
  set g := conjSeq σ γ with hg
  have hmem : ∀ n, g n ∈ Γ := conjSeq_mem Γ hσ hγ
  have hstep : ∀ n, (g (n+1)) 0 0 = ε * (1 - g n 0 0 * g n 1 0 * h) ∧
      (g (n+1)) 0 1 = ε * (g n 0 0 ^ 2 * h) ∧ (g (n+1)) 1 0 = -ε * h * g n 1 0 ^ 2 ∧
      (g (n+1)) 1 1 = ε * (1 + g n 0 0 * g n 1 0 * h) := fun n =>
    conj_entries (g n) σ ε h h00 h01 h10 h11
  -- the sequence u n = |c_n h|
  set r := |γ 1 0 * h| with hr
  have hr0 : 0 ≤ r := abs_nonneg _
  have hu : ∀ n, |g n 1 0 * h| = r ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => simp [hg, conjSeq, hr]
    | succ n ih =>
      have : g (n+1) 1 0 * h = -ε * (g n 1 0 * h) ^ 2 := by rw [(hstep n).2.2.1]; ring
      rw [this, abs_mul, abs_neg, hεabs, one_mul, abs_pow, ih, ← pow_mul, pow_succ]
  have hu1 : ∀ n, |g n 1 0 * h| ≤ 1 := fun n => by
    rw [hu]; exact pow_le_one₀ hr0 hc.le
  have hun : ∀ n, |g n 1 0 * h| ≤ r ^ n := fun n => by
    rw [hu]; exact pow_le_pow_of_le_one hr0 hc.le (Nat.lt_two_pow_self).le
  have ha : ∀ n : ℕ, |g n 0 0| ≤ |γ 0 0| + n := by
    intro n
    induction n with
    | zero => simp [hg, conjSeq]
    | succ n ih =>
      rw [(hstep n).1]
      have e : ε * (1 - g n 0 0 * g n 1 0 * h) = ε - ε * (g n 0 0 * (g n 1 0 * h)) := by ring
      rw [e]
      calc |ε - ε * (g n 0 0 * (g n 1 0 * h))| ≤ |ε| + |ε * (g n 0 0 * (g n 1 0 * h))| :=
            abs_sub _ _
        _ ≤ 1 + |g n 0 0| * 1 := by
            rw [hεabs, abs_mul, hεabs, abs_mul, one_mul]
            gcongr
            · exact hu1 n
        _ ≤ |γ 0 0| + ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hbd : ∀ n, |g (n+1) 0 0 - ε| ≤ (|γ 0 0| + n) * r ^ n ∧ |g (n+1) 1 1 - ε| ≤ (|γ 0 0| + n) * r ^ n := by
    intro n
    have h1 : |g n 0 0 * g n 1 0 * h| ≤ (|γ 0 0| + n) * r ^ n := by
      rw [mul_assoc, abs_mul]
      exact mul_le_mul (ha n) (hun n) (abs_nonneg _) (by positivity)
    constructor
    · have : g (n+1) 0 0 - ε = -(ε * (g n 0 0 * g n 1 0 * h)) := by rw [(hstep n).1]; ring
      rw [this, abs_neg, abs_mul, hεabs, one_mul]; exact h1
    · have : g (n+1) 1 1 - ε = ε * (g n 0 0 * g n 1 0 * h) := by rw [(hstep n).2.2.2]; ring
      rw [this, abs_mul, hεabs, one_mul]; exact h1
  have hlim : Filter.Tendsto (fun n : ℕ => (|γ 0 0| + n) * r ^ n) Filter.atTop (nhds 0) := by
    have h2 := (tendsto_self_mul_const_pow_of_lt_one hr0 hc)
    have h3 := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hc).const_mul |γ 0 0|
    have := h3.add h2
    simp only [mul_zero, add_zero] at this
    refine this.congr (fun n => ?_)
    ring
  have hA : Filter.Tendsto (fun n => g (n+1) 0 0) Filter.atTop (nhds ε) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => by rw [Real.dist_eq]; exact (hbd n).1) hlim
  have hD : Filter.Tendsto (fun n => g (n+1) 1 1) Filter.atTop (nhds ε) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => by rw [Real.dist_eq]; exact (hbd n).2) hlim
  have hC : Filter.Tendsto (fun n => g (n+1) 1 0) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun n => |g n 1 0 * h|) Filter.atTop (nhds 0) :=
      squeeze_zero (fun _ => abs_nonneg _) hun (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hc)
    have h4 := ((Filter.tendsto_add_atTop_iff_nat 1).2 this)
    have h5 : Filter.Tendsto (fun n => g (n+1) 1 0 * h) Filter.atTop (nhds 0) :=
      (tendsto_zero_iff_abs_tendsto_zero _).2 h4
    simpa [hh.ne'] using h5.div_const h
  have hB : Filter.Tendsto (fun n => g (n+2) 0 1) Filter.atTop (nhds (ε * h)) := by
    have h6 : Filter.Tendsto (fun n => ε * (g (n+1) 0 0 ^ 2 * h)) Filter.atTop
        (nhds (ε * (ε ^ 2 * h))) := (hA.pow 2).mul_const h |>.const_mul ε
    have e : ε * (ε ^ 2 * h) = ε * h := by rcases hε with rfl | rfl <;> ring
    rw [e] at h6
    exact h6.congr (fun n => ((hstep (n+1)).2.1).symm)
  have hA2 := (Filter.tendsto_add_atTop_iff_nat 1).2 hA
  have hD2 := (Filter.tendsto_add_atTop_iff_nat 1).2 hD
  have hC2 := (Filter.tendsto_add_atTop_iff_nat 1).2 hC
  have hT : Filter.Tendsto (fun n => g (n+2)) Filter.atTop (nhds σ) := by
    apply tendsto_subtype_rng.2
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    fin_cases i <;> fin_cases j
    · simpa [h00] using hA2
    · simpa [h01] using hB
    · simpa [h10] using hC2
    · simpa [h11] using hD2
  obtain ⟨U, hU, hσU, hUΓ⟩ := exists_isolating Γ hσ
  have hev := (hT.eventually (hU.mem_nhds hσU)).exists
  obtain ⟨n, hn⟩ := hev
  have hgn : g (n+2) = σ := hUΓ _ (hmem _) hn
  by_contra hne
  have hall : ∀ m, g m 1 0 ≠ 0 := by
    intro m
    induction m with
    | zero => exact hne
    | succ m ih =>
      rw [(hstep m).2.2.1]
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 hε0) hh.ne') (pow_ne_zero 2 ih)
  have := hall (n+2)
  rw [hgn, h10] at this
  exact this rfl

end ModularFormsKB.Miyake
