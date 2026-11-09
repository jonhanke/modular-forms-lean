import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import ModularFormsKB.Citation
/-!
# Miyake §1.1: the upper half plane and the unit disc

Miyake, *Modular Forms* (Springer 1989), §1.1, pp. 1–4. Here: Lemma 1.1.2, the complex analytic
isomorphism $\rho(z) = (z - i)/(z + i)$ of the upper half plane $\mathbb H$ onto the unit disc
$K = \{w \in \mathbb C : |w| < 1\}$ (Mathlib's `Complex.UnitDisc`, notation `𝔻`), with inverse
$w \mapsto i(1 + w)/(1 - w)$.

"Complex analytically isomorphic" is encoded as: a bijection $\mathbb H \to K$ given by
$\rho$, whose inverse is $w \mapsto i(1+w)/(1-w)$, with both formulas complex differentiable
(hence analytic) on the respective open subsets of $\mathbb C$.
-/

open Complex
open scoped Complex.UnitDisc

namespace ModularFormsKB.Miyake

/-- `z + i ≠ 0` on the upper half plane. -/
lemma add_I_ne_zero {z : ℂ} (hz : 0 < z.im) : z + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- The Cayley map sends the upper half plane into the unit disc. -/
lemma cayley_norm_lt {z : ℂ} (hz : 0 < z.im) : ‖(z - I) / (z + I)‖ < 1 := by
  have h := add_I_ne_zero hz
  rw [norm_div, div_lt_one (norm_pos_iff.mpr h)]
  apply lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _)
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp
  nlinarith

/-- `1 - w ≠ 0` on the unit disc. -/
lemma one_sub_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h
  have : w = 1 := by linear_combination -h
  rw [this] at hw
  simp at hw

/-- The inverse Cayley map sends the unit disc into the upper half plane. -/
lemma cayley_inv_im_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (I * (1 + w) / (1 - w)).im := by
  have h := one_sub_ne_zero hw
  have hn : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr h
  have h2 : Complex.normSq w < 1 := by
    have := Complex.sq_norm w
    nlinarith [norm_nonneg w]
  rw [Complex.div_im]
  have : 0 < (1 - Complex.normSq w) / Complex.normSq (1 - w) := div_pos (by linarith) hn
  convert this using 1
  simp only [Complex.normSq_apply] at *
  simp
  field_simp
  ring

/-- The Cayley map $\rho : \mathbb H \to K$, $\rho(z) = (z - i)/(z + i)$ (Miyake, proof of
Theorem 1.1.3, p. 3), as a bijection onto the unit disc with inverse $w \mapsto i(1 + w)/(1 - w)$. -/
noncomputable def cayleyEquiv : UpperHalfPlane ≃ 𝔻 where
  toFun z := UnitDisc.mk ((z - I) / (z + I)) (cayley_norm_lt z.im_pos)
  invFun w := UpperHalfPlane.mk (I * (1 + w) / (1 - w)) (cayley_inv_im_pos w.norm_lt_one)
  left_inv z := by
    have h := add_I_ne_zero z.im_pos
    apply UpperHalfPlane.ext
    simp only [UnitDisc.coe_mk]
    have h1 : 1 - (z - I) / (z + I) = 2 * I / (z + I) := by field_simp; ring
    have h2 : (2 * I / (z + I)) ≠ 0 := div_ne_zero (by simp) h
    rw [h1]
    field_simp
    ring
  right_inv w := by
    have h := one_sub_ne_zero w.norm_lt_one
    ext
    simp only [UnitDisc.coe_mk]
    have h3 : I * (1 + (w:ℂ)) / (1 - w) + I ≠ 0 := by
      have : I * (1 + (w:ℂ)) / (1 - w) + I = 2 * I / (1 - w) := by field_simp; ring
      rw [this]; exact div_ne_zero (by simp) h
    field_simp
    ring

/-- The Cayley map is $z \mapsto (z - i)/(z + i)$. -/
theorem cayleyEquiv_apply (z : UpperHalfPlane) : (cayleyEquiv z : ℂ) = (z - I) / (z + I) := rfl

/-- The inverse of the Cayley map is $w \mapsto i(1 + w)/(1 - w)$. -/
theorem cayleyEquiv_symm_apply (w : 𝔻) :
    ((cayleyEquiv.symm w : UpperHalfPlane) : ℂ) = I * (1 + w) / (1 - w) := rfl

/-- **Miyake, Lemma 1.1.2.** The upper half plane $\mathbb H$ and the unit disc $K$ are complex
analytically isomorphic: the Cayley map $\rho(z) = (z-i)/(z+i)$ is a bijection $\mathbb H \to K$
(`cayleyEquiv`, `cayleyEquiv_apply`, `cayleyEquiv_symm_apply`), and $\rho$ and its inverse
$w \mapsto i(1+w)/(1-w)$ are complex differentiable on $\mathbb H$ and on $K$ respectively. -/
@[kb "miyake1989" "Lemma 1.1.2, p. 2"]
theorem cayley_biholomorphic :
    DifferentiableOn ℂ (fun z : ℂ ↦ (z - I) / (z + I)) {z | 0 < z.im} ∧
      DifferentiableOn ℂ (fun w : ℂ ↦ I * (1 + w) / (1 - w)) (Metric.ball 0 1) ∧
      (∀ z : UpperHalfPlane, (cayleyEquiv z : ℂ) = (z - I) / (z + I)) ∧
      ∀ w : 𝔻, ((cayleyEquiv.symm w : UpperHalfPlane) : ℂ) = I * (1 + w) / (1 - w) := by
  refine ⟨?_, ?_, cayleyEquiv_apply, cayleyEquiv_symm_apply⟩
  · intro z hz
    have h := add_I_ne_zero (show 0 < z.im from hz)
    exact (((differentiableAt_id.sub_const I).div (differentiableAt_id.add_const I) h)).differentiableWithinAt
  · intro w hw
    have h := one_sub_ne_zero (show ‖w‖ < 1 by simpa using hw)
    exact ((((differentiableAt_id.const_add 1).const_mul I).div
      (differentiableAt_id.const_sub 1) h)).differentiableWithinAt

open OnePoint
open scoped Pointwise

/-! ### Lemma 1.1.1 -/

/-- The value of the Hermitian form $A|z|^2 + 2\operatorname{Re}(\bar B z) + C$ at a point of the
Riemann sphere $\mathbb P^1(\mathbb C) = \mathbb C \cup \{\infty\}$ (`OnePoint ℂ`), homogenized: at
$\infty$ (homogeneous coordinates $(1, 0)$) the value is $A$. -/
noncomputable def circleForm (A C : ℝ) (B : ℂ) : OnePoint ℂ → ℝ
  | ∞ => A
  | (z : ℂ) => A * Complex.normSq z + 2 * (starRingEnd ℂ B * z).re + C

/-- A *generalized circle* in $\mathbb P^1(\mathbb C)$: the zero set of
$A|z|^2 + 2\operatorname{Re}(\bar B z) + C$ with $A, C \in \mathbb R$, $B \in \mathbb C$ and
$|B|^2 > AC$. For $A \ne 0$ it is the circle with center $-B/A$ and radius $\sqrt{|B|^2 - AC}/|A|$;
for $A = 0$ it is the line $2\operatorname{Re}(\bar B z) + C = 0$ ($B \ne 0$) together with $\infty$
(`isGenCircle_sphere`, `isGenCircle_line`). -/
def IsGenCircle (S : Set (OnePoint ℂ)) : Prop :=
  ∃ (A C : ℝ) (B : ℂ), A * C < Complex.normSq B ∧ S = {x | circleForm A C B x = 0}

/-- Homogeneous Hermitian form $A|v_0|^2 + 2\operatorname{Re}(\bar B v_0 \bar v_1) + C|v_1|^2$. -/
noncomputable def circleHermForm (A C : ℝ) (B : ℂ) (v0 v1 : ℂ) : ℝ :=
  A * Complex.normSq v0 + 2 * (starRingEnd ℂ B * v0 * starRingEnd ℂ v1).re + C * Complex.normSq v1

/-- Transformed coefficient `A'`. -/
noncomputable def circleCoeffA (A C : ℝ) (B a c : ℂ) : ℝ := circleHermForm A C B a c
/-- Transformed coefficient `C'`. -/
noncomputable def circleCoeffC (A C : ℝ) (B b d : ℂ) : ℝ := circleHermForm A C B b d
/-- Transformed coefficient `B'`. -/
noncomputable def circleCoeffB (A C : ℝ) (B a b c d : ℂ) : ℂ :=
  A * (starRingEnd ℂ a * b) + C * (starRingEnd ℂ c * d) + B * (starRingEnd ℂ a * d)
    + starRingEnd ℂ B * (starRingEnd ℂ c * b)

/-- The form transforms covariantly. -/
lemma circleHermForm_trans (A C : ℝ) (B a b c d v0 v1 : ℂ) :
    circleHermForm A C B (a * v0 + b * v1) (c * v0 + d * v1) =
      circleHermForm (circleCoeffA A C B a c) (circleCoeffC A C B b d) (circleCoeffB A C B a b c d) v0 v1 := by
  simp only [circleHermForm, circleCoeffA, circleCoeffC, circleCoeffB, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- The discriminant transforms by $|\det|^2$. -/
lemma disc_trans (A C : ℝ) (B a b c d : ℂ) :
    Complex.normSq (circleCoeffB A C B a b c d) - circleCoeffA A C B a c * circleCoeffC A C B b d =
      Complex.normSq (a * d - b * c) * (Complex.normSq B - A * C) := by
  simp only [circleHermForm, circleCoeffA, circleCoeffC, circleCoeffB, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma circleForm_infty (A C : ℝ) (B : ℂ) : circleForm A C B ∞ = A := rfl

lemma circleForm_coe_eq (A C : ℝ) (B z : ℂ) :
    circleForm A C B (z : OnePoint ℂ) = circleHermForm A C B z 1 := by
  simp [circleForm, circleHermForm]

lemma circleForm_div (A C : ℝ) (B v0 v1 : ℂ) (h : v1 ≠ 0) :
    circleForm A C B ((v0 / v1 : ℂ) : OnePoint ℂ) * Complex.normSq v1 = circleHermForm A C B v0 v1 := by
  rw [circleForm_coe_eq]
  have h1 : Complex.normSq v1 ≠ 0 := by simpa using h
  have : circleHermForm A C B (v0 / v1) 1 * Complex.normSq v1 = circleHermForm A C B v0 v1 := by
    have e : v0 = (v0 / v1) * v1 := by field_simp
    have e2 : v1 = 1 * v1 := by simp
    conv_rhs => rw [e]
    simp only [circleHermForm, map_one, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im]
    simp only [Complex.one_re, Complex.one_im]
    ring
  exact this

/-- The determinant of an element of `GL₂(ℂ)` in terms of its entries is nonzero. -/
lemma gl_det_ne (h : GL (Fin 2) ℂ) : h 0 0 * h 1 1 - h 0 1 * h 1 0 ≠ 0 := by
  have := (Matrix.GeneralLinearGroup.det h).ne_zero
  rwa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at this

/-- Pointwise transformation law for the zero set of the form. -/
lemma circleForm_smul_iff (A C : ℝ) (B : ℂ) (h : GL (Fin 2) ℂ) (x : OnePoint ℂ) :
    circleForm A C B (h • x) = 0 ↔
      circleForm (circleCoeffA A C B (h 0 0) (h 1 0)) (circleCoeffC A C B (h 0 1) (h 1 1))
        (circleCoeffB A C B (h 0 0) (h 0 1) (h 1 0) (h 1 1)) x = 0 := by
  have hd := gl_det_ne h
  cases x with
  | infty =>
    rw [OnePoint.smul_infty_eq_ite]
    by_cases hc : h 1 0 = 0
    · rw [ite_eq_left hc]
      have ha : h 0 0 ≠ 0 := by
        intro ha; apply hd; simp [ha, hc]
      have e : circleCoeffA A C B (h 0 0) (h 1 0) = A * Complex.normSq (h 0 0) := by
        simp [circleCoeffA, circleHermForm, hc]
      show A = 0 ↔ circleCoeffA A C B (h 0 0) (h 1 0) = 0
      rw [e, mul_eq_zero, Complex.normSq_eq_zero]
      exact ⟨fun h0 => Or.inl h0, fun h0 => h0.resolve_right ha⟩
    · rw [ite_eq_right hc]
      have h1 : Complex.normSq (h 1 0) ≠ 0 := by simpa using hc
      have := circleForm_div A C B (h 0 0) (h 1 0) hc
      have e : circleHermForm A C B (h 0 0) (h 1 0) = circleCoeffA A C B (h 0 0) (h 1 0) := rfl
      rw [e] at this
      show _ ↔ circleCoeffA A C B (h 0 0) (h 1 0) = 0
      rw [← this]
      simp [h1]
  | coe z =>
    rw [OnePoint.smul_some_eq_ite]
    by_cases hc : h 1 0 * z + h 1 1 = 0
    · rw [ite_eq_left hc]
      have hz : h 0 0 * z + h 0 1 ≠ 0 := by
        intro hz; apply hd
        have e1 : h 0 1 = - (h 0 0 * z) := by linear_combination hz
        have e2 : h 1 1 = - (h 1 0 * z) := by linear_combination hc
        rw [e1, e2]; ring
      have key := circleHermForm_trans A C B (h 0 0) (h 0 1) (h 1 0) (h 1 1) z 1
      rw [mul_one, mul_one, hc] at key
      rw [circleForm_coe_eq, circleForm_infty, ← key]
      simp [circleHermForm, hz]
    · rw [ite_eq_right hc]
      have hh := circleForm_coe_eq (circleCoeffA A C B (h 0 0) (h 1 0)) (circleCoeffC A C B (h 0 1) (h 1 1))
        (circleCoeffB A C B (h 0 0) (h 0 1) (h 1 0) (h 1 1)) z
      rw [hh]
      have key := circleHermForm_trans A C B (h 0 0) (h 0 1) (h 1 0) (h 1 1) z 1
      rw [mul_one, mul_one] at key
      have h1 : Complex.normSq (h 1 0 * z + h 1 1) ≠ 0 := by simpa using hc
      have := circleForm_div A C B (h 0 0 * z + h 0 1) (h 1 0 * z + h 1 1) hc
      rw [key] at this
      rw [← this]
      simp [h1]

/-- Circles are generalized circles: the image in $\mathbb P^1(\mathbb C)$ of the circle
$|z - c| = r$, $r > 0$. -/
theorem isGenCircle_sphere (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsGenCircle (((↑) : ℂ → OnePoint ℂ) '' Metric.sphere c r) := by
  refine ⟨1, Complex.normSq c - r ^ 2, -c, ?_, ?_⟩
  · rw [Complex.normSq_neg]; nlinarith
  · ext x
    cases x with
    | infty => simp [circleForm]
    | coe z =>
      simp only [Set.mem_image, Set.mem_ofPred_eq, circleForm, OnePoint.coe_eq_coe,
        exists_eq_right, Metric.mem_sphere, dist_eq_norm]
      have h1 : ‖z - c‖ = r ↔ Complex.normSq (z - c) = r ^ 2 := by
        rw [Complex.normSq_eq_norm_sq]
        constructor
        · intro h; rw [h]
        · intro h; exact (sq_eq_sq₀ (norm_nonneg _) hr.le).1 h
      rw [h1]
      simp only [Complex.normSq_apply, Complex.mul_re, Complex.sub_re, Complex.sub_im,
        Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
      constructor <;> intro h <;> linarith


/-- Lines are generalized circles: the line $\{z : \operatorname{Re}(\bar B z) = t\}$ ($B \ne 0$)
together with $\infty$. -/
theorem isGenCircle_line {B : ℂ} (hB : B ≠ 0) (t : ℝ) :
    IsGenCircle (insert ∞ (((↑) : ℂ → OnePoint ℂ) '' {z | (starRingEnd ℂ B * z).re = t})) := by
  refine ⟨0, -2 * t, B, ?_, ?_⟩
  · simpa using Complex.normSq_pos.2 hB
  · ext x
    cases x with
    | infty => simp [circleForm]
    | coe z =>
      simp only [Set.mem_insert_iff, Set.mem_image, Set.mem_ofPred_eq, circleForm,
        OnePoint.coe_eq_coe, exists_eq_right]
      simp only [OnePoint.coe_ne_infty, false_or, zero_mul]
      constructor <;> intro h <;> linarith


/-- **Miyake, Lemma 1.1.1.** A linear fractional transformation maps circles and lines to circles or
lines: for every $g \in \mathrm{GL}_2(\mathbb C)$ acting on $\mathbb P^1(\mathbb C)$ by
$z \mapsto (az+b)/(cz+d)$ (Mathlib's `OnePoint.instGLAction`), the image $g S$ of a generalized circle
$S$ is a generalized circle. Lines are taken with the point $\infty$, as is necessary for the
statement to hold exactly. -/
@[kb "miyake1989" "Lemma 1.1.1, p. 2"]
theorem IsGenCircle.smul {S : Set (OnePoint ℂ)} (hS : IsGenCircle S) (g : GL (Fin 2) ℂ) :
    IsGenCircle (g • S) := by
  obtain ⟨A, C, B, hlt, rfl⟩ := hS
  refine ⟨circleCoeffA A C B ((g⁻¹ : GL (Fin 2) ℂ) 0 0) ((g⁻¹ : GL (Fin 2) ℂ) 1 0),
    circleCoeffC A C B ((g⁻¹ : GL (Fin 2) ℂ) 0 1) ((g⁻¹ : GL (Fin 2) ℂ) 1 1),
    circleCoeffB A C B ((g⁻¹ : GL (Fin 2) ℂ) 0 0) ((g⁻¹ : GL (Fin 2) ℂ) 0 1) ((g⁻¹ : GL (Fin 2) ℂ) 1 0)
      ((g⁻¹ : GL (Fin 2) ℂ) 1 1), ?_, ?_⟩
  · have hd := gl_det_ne g⁻¹
    have hp : 0 < Complex.normSq ((g⁻¹ : GL (Fin 2) ℂ) 0 0 * (g⁻¹ : GL (Fin 2) ℂ) 1 1
        - (g⁻¹ : GL (Fin 2) ℂ) 0 1 * (g⁻¹ : GL (Fin 2) ℂ) 1 0) := Complex.normSq_pos.2 hd
    have := disc_trans A C B ((g⁻¹ : GL (Fin 2) ℂ) 0 0) ((g⁻¹ : GL (Fin 2) ℂ) 0 1)
      ((g⁻¹ : GL (Fin 2) ℂ) 1 0) ((g⁻¹ : GL (Fin 2) ℂ) 1 1)
    have h2 : 0 < Complex.normSq B - A * C := by linarith
    have := mul_pos hp h2
    linarith
  · ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    exact circleForm_smul_iff A C B g⁻¹ x


end ModularFormsKB.Miyake
