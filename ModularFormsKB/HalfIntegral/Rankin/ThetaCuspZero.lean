/-
# The twisted theta series at the cusp 0: the Gauss-sum inversion (Miyake Corollary 4.9.7 (2))

Loose ends LE-MF-0056 and LE-MF-0256.

For $\psi$ primitive modulo $r \ge 1$, $\theta_\psi(z) = \sum_n\overline\psi(n)n^\nu e(n^2z)$ (`thetaTwist ψ 1`) and
$w \in \mathbb H$, with $\tau(\psi) = \sum_{a=0}^{r-1}\psi(a)e(a/r)$ (`gaussAt r ψ 1`) and the principal square root:
$$\theta_\psi\Big(\frac{-1}{4r^2w}\Big) = \frac{r}{\tau(\psi)}(-2iw)^{1/2}\,\theta_{\overline\psi}(w)\quad(\psi\text{ even}),\qquad
  \theta_\psi\Big(\frac{-1}{4r^2w}\Big) = \frac{r}{\tau(\psi)}(-2iw)^{1/2}(2rw)\,\theta_{\overline\psi}(w)\quad(\psi\text{ odd}).$$
Checked numerically. Source: Miyake 1989 `miyake1989`,
Corollary 4.9.7 (2) [unverified as to the normalization; the formula here is the one checked].

Proof route: $\overline\psi(n) = \tau(\psi)^{-1}\sum_b\psi(b)e(bn/r)$ for primitive $\psi$
(`GaussImprimitive.gaussAt_of_isPrimitive`), then Mathlib's `jacobiTheta₂_functional_equation` (and
`jacobiTheta₂'_functional_equation` for $\nu = 1$) at $z = b/r$, and the reindexing $n = rm - b$.
-/
import ModularFormsKB.HalfIntegral.Rankin.GaussImprimitive
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import ModularFormsKB.HalfIntegral.Theta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

namespace ModularFormsKB.HalfIntegral

open Complex

namespace ThetaCuspZero

open scoped Real

/-- `T = 2 * (-1/(4 r^2 w))` has positive imaginary part. -/
lemma im_T_pos {r : ℕ} [NeZero r] {w : ℂ} (hw : 0 < w.im) :
    0 < (2 * (-1 / (4 * (r : ℂ) ^ 2 * w))).im := by
  have hr : (r : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne r
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw0
  have : (2 * (-1 / (4 * (r : ℂ) ^ 2 * w))).im = w.im / (2 * (r : ℝ) ^ 2 * Complex.normSq w) := by
    rw [show (2 * (-1 / (4 * (r : ℂ) ^ 2 * w))) = -(1 / (2 * (r : ℂ) ^ 2)) * w⁻¹ by
      field_simp; ring]
    have : (-(1 / (2 * (r : ℂ) ^ 2)) : ℂ) = ((-(1 / (2 * (r : ℝ) ^ 2)) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.im_ofReal_mul, Complex.inv_im]
    field_simp
  rw [this]
  positivity

/-- `(-I T)^{-1/2} = r (-2 I w)^{1/2}`. -/
lemma inv_sqrt_T {r : ℕ} [NeZero r] {w : ℂ} (hw : 0 < w.im) :
    1 / (-I * (2 * (-1 / (4 * (r : ℂ) ^ 2 * w)))) ^ (1 / 2 : ℂ) = (r : ℂ) * (-2 * I * w) ^ (1 / 2 : ℂ) := by
  have hr : (r : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne r
  have hrR : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hre1 : 0 < (-I * (2 * (-1 / (4 * (r : ℂ) ^ 2 * w)))).re := by
    have := im_T_pos (r := r) hw
    simpa using this
  have hre2 : 0 < (-2 * I * w).re := by simpa using hw
  have hprod : (-I * (2 * (-1 / (4 * (r : ℂ) ^ 2 * w)))) * (-2 * I * w) = (((1 / (r : ℝ) ^ 2 : ℝ)) : ℂ) := by
    push_cast
    field_simp
    ring_nf
    simp [Complex.I_sq]
  have h := ModularFormsKB.HalfIntegral.sqrt_mul_of_re_pos hre1 hre2
  rw [hprod] at h
  have h2 : (((1 / (r : ℝ) ^ 2 : ℝ)) : ℂ) ^ (1 / 2 : ℂ) = ((1 / (r : ℝ) : ℝ) : ℂ) := by
    have := Complex.ofReal_cpow (x := 1 / (r : ℝ) ^ 2) (by positivity) (1 / 2 : ℝ)
    have e : (((1 / 2 : ℝ)) : ℂ) = 1 / 2 := by push_cast; rfl
    rw [e] at this
    rw [← this, ← Real.sqrt_eq_rpow]
    congr 1
    rw [show (1 / (r : ℝ) ^ 2) = (1 / (r : ℝ)) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [h2] at h
  have hs : (-2 * I * w) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    simp [hw0]
  have hu : (-I * (2 * (-1 / (4 * (r : ℂ) ^ 2 * w)))) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    intro hh
    have := hre1
    rw [hh.1] at this
    simp at this
  generalize (-I * (2 * (-1 / (4 * (r : ℂ) ^ 2 * w)))) ^ (1 / 2 : ℂ) = u at *
  generalize (-2 * I * w) ^ (1 / 2 : ℂ) = s at *
  rw [show (((1 / (r : ℝ) : ℝ)) : ℂ) = 1 / (r : ℂ) by push_cast; rfl] at h
  field_simp
  field_simp at h
  linear_combination (-1) * h


/-- `gaussAt r ψ 1` is the Gauss sum for the standard additive character. -/
lemma gaussAt_one_eq {r : ℕ} [NeZero r] (ψ : DirichletCharacter ℂ r) :
    gaussAt r ψ 1 = gaussSum ψ (ZMod.stdAddChar : AddChar (ZMod r) ℂ) := by
  unfold gaussAt gaussSum
  refine Finset.sum_nbij' (fun a ↦ (a : ZMod r)) (fun x ↦ x.val) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro x _; exact Finset.mem_range.2 (ZMod.val_lt x)
  · intro a ha
    exact ZMod.val_cast_of_lt (Finset.mem_range.1 ha)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro a ha
    have := ZMod.stdAddChar_coe (N := r) (a : ℤ)
    push_cast at this
    rw [this]
    push_cast
    ring_nf

lemma gaussAt_one_ne_zero {r : ℕ} [NeZero r] {ψ : DirichletCharacter ℂ r} (hψ : ψ.IsPrimitive) :
    gaussAt r ψ 1 ≠ 0 := by
  rw [gaussAt_one_eq]
  intro h
  have := DirichletCharacter.norm_gaussSum_stdAddChar hψ
  rw [h, norm_zero] at this
  have hpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  have := Real.sqrt_pos.mpr hpos
  simp_all

/-- Reindexing `ℤ` by residues modulo `r`. -/
lemma sum_reindex {r : ℕ} [NeZero r] (h : ℤ → ℂ) (hh : Summable h) :
    ∑ b ∈ Finset.range r, ∑' m : ℤ, h (m * r + b) = ∑' n : ℤ, h n := by
  set e := Int.divModEquiv r
  have h1 : Summable (fun p : ℤ × Fin r => h (e.symm p)) := e.symm.summable_iff.mpr hh
  have h2 : ∑' p : ℤ × Fin r, h (e.symm p) = ∑' n, h n := e.symm.tsum_eq h
  have h3 : ∑' p : ℤ × Fin r, h (e.symm p) = ∑' (m : ℤ) (b : Fin r), h (m * r + b) := by
    rw [h1.tsum_prod]
    simp [e, Int.divModEquiv_symm_apply]
  have h4 : Summable (Function.uncurry fun (m : ℤ) (b : Fin r) => h (m * r + b)) := by
    have : Summable (fun p : ℤ × Fin r => h (p.1 * r + p.2)) := by
      simpa [e, Int.divModEquiv_symm_apply] using h1
    exact this
  rw [← h2, h3, ← h4.tsum_comm]
  simp only [tsum_fintype]
  rw [← Fin.sum_univ_eq_sum_range (fun b => ∑' m : ℤ, h (m * r + b))]

lemma term_id {r : ℕ} [NeZero r] {w T : ℂ} (hw0 : w ≠ 0)
    (hTd : T = 2 * (-1 / (4 * (r : ℂ) ^ 2 * w))) (b m : ℤ) :
    cexp (2 * π * I * ((r : ℂ) * m - b) ^ 2 * w) =
      cexp (-π * I * ((b : ℂ) / r) ^ 2 / T) *
        cexp (2 * π * I * m * (((b : ℂ) / r) / T) + π * I * m ^ 2 * (-1 / T)) := by
  have hr : (r : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne r
  rw [← Complex.exp_add]
  congr 1
  subst hTd
  field_simp
  ring

lemma hasSum_dual_core {r : ℕ} [NeZero r] {w T : ℂ} (hw : 0 < w.im)
    (hTd : T = 2 * (-1 / (4 * (r : ℂ) ^ 2 * w))) (b : ℤ) :
    HasSum (fun m : ℤ => (r : ℂ) * (-2 * I * w) ^ (1 / 2 : ℂ) *
        cexp (2 * π * I * ((r : ℂ) * m - b) ^ 2 * w)) (jacobiTheta₂ ((b : ℂ) / r) T) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hT : 0 < T.im := hTd ▸ im_T_pos (r := r) hw
  have hT0 : T ≠ 0 := fun h => by simp [h] at hT
  have hT' : 0 < (-1 / T).im := by
    rw [div_eq_mul_inv, neg_one_mul, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos hT (Complex.normSq_pos.mpr hT0)
  have hs := hasSum_jacobiTheta₂_term (((b : ℂ) / r) / T) hT'
  have hFE := jacobiTheta₂_functional_equation ((b : ℂ) / r) T
  have hq : 1 / (-I * T) ^ (1 / 2 : ℂ) = (r : ℂ) * (-2 * I * w) ^ (1 / 2 : ℂ) := by
    subst hTd; exact inv_sqrt_T hw
  rw [hFE, hq]
  have e : (fun m : ℤ => (r : ℂ) * (-2 * I * w) ^ (1 / 2 : ℂ) *
        cexp (2 * π * I * ((r : ℂ) * m - b) ^ 2 * w)) =
      fun m : ℤ => (r : ℂ) * (-2 * I * w) ^ (1 / 2 : ℂ) * cexp (-π * I * ((b : ℂ) / r) ^ 2 / T) *
        jacobiTheta₂_term m (((b : ℂ) / r) / T) (-1 / T) := by
    funext m
    rw [term_id hw0 hTd b m, jacobiTheta₂_term]
    ring
  rw [e]
  exact hs.mul_left _

/-- The Poisson-dual series for `jacobiTheta₂ (b/r) T`. -/
lemma hasSum_dual {r : ℕ} [NeZero r] {w : ℂ} (hw : 0 < w.im) (b : ℤ) :
    HasSum (fun m : ℤ => (r : ℂ) * (-2 * I * w) ^ (1 / 2 : ℂ) *
        cexp (2 * π * I * ((r : ℂ) * m - b) ^ 2 * w))
      (jacobiTheta₂ ((b : ℂ) / r) (2 * (-1 / (4 * (r : ℂ) ^ 2 * w)))) :=
  hasSum_dual_core hw rfl b

lemma hasSum_dual'_core {r : ℕ} [NeZero r] {w T : ℂ} (hw : 0 < w.im)
    (hTd : T = 2 * (-1 / (4 * (r : ℂ) ^ 2 * w))) (b : ℤ) :
    HasSum (fun m : ℤ => 2 * π * I * ((r : ℂ) * (-2 * I * w) ^ (1 / 2 : ℂ) * (-2 * r * w)) *
        (((r : ℂ) * m - b) * cexp (2 * π * I * ((r : ℂ) * m - b) ^ 2 * w)))
      (jacobiTheta₂' ((b : ℂ) / r) T) := by
  have hr : (r : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne r
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hT : 0 < T.im := hTd ▸ im_T_pos (r := r) hw
  have hT0 : T ≠ 0 := fun h => by simp [h] at hT
  have hT' : 0 < (-1 / T).im := by
    rw [div_eq_mul_inv, neg_one_mul, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos hT (Complex.normSq_pos.mpr hT0)
  have hs := hasSum_jacobiTheta₂'_term (((b : ℂ) / r) / T) hT'
  have hs0 := hasSum_jacobiTheta₂_term (((b : ℂ) / r) / T) hT'
  have hFE := jacobiTheta₂'_functional_equation ((b : ℂ) / r) T
  have hq : 1 / (-I * T) ^ (1 / 2 : ℂ) = (r : ℂ) * (-2 * I * w) ^ (1 / 2 : ℂ) := by
    subst hTd; exact inv_sqrt_T hw
  rw [hFE, hq]
  have e : (fun m : ℤ => 2 * π * I * ((r : ℂ) * (-2 * I * w) ^ (1 / 2 : ℂ) * (-2 * r * w)) *
        (((r : ℂ) * m - b) * cexp (2 * π * I * ((r : ℂ) * m - b) ^ 2 * w))) =
      fun m : ℤ => (r : ℂ) * (-2 * I * w) ^ (1 / 2 : ℂ) * cexp (-π * I * ((b : ℂ) / r) ^ 2 / T) / T *
        (jacobiTheta₂'_term m (((b : ℂ) / r) / T) (-1 / T) -
          2 * π * I * ((b : ℂ) / r) * jacobiTheta₂_term m (((b : ℂ) / r) / T) (-1 / T)) := by
    funext m
    have hh := term_id hw0 hTd b m
    simp only [jacobiTheta₂'_term, jacobiTheta₂_term]
    rw [hh]
    subst hTd
    field_simp
    ring
  rw [e]
  exact (hs.sub (hs0.mul_left _)).mul_left _

/-- The Poisson-dual series for `jacobiTheta₂' (b/r) T`. -/
lemma hasSum_dual' {r : ℕ} [NeZero r] {w : ℂ} (hw : 0 < w.im) (b : ℤ) :
    HasSum (fun m : ℤ => 2 * π * I * ((r : ℂ) * (-2 * I * w) ^ (1 / 2 : ℂ) * (-2 * r * w)) *
        (((r : ℂ) * m - b) * cexp (2 * π * I * ((r : ℂ) * m - b) ^ 2 * w)))
      (jacobiTheta₂' ((b : ℂ) / r) (2 * (-1 / (4 * (r : ℂ) ^ 2 * w)))) :=
  hasSum_dual'_core hw rfl b

lemma psi_inv_expand {r : ℕ} [NeZero r] {ψ : DirichletCharacter ℂ r} (hψ : ψ.IsPrimitive) (n : ℤ) :
    ψ⁻¹ (n : ZMod r) = (gaussAt r ψ 1)⁻¹ *
      ∑ b ∈ Finset.range r, ψ (b : ZMod r) * cexp (2 * π * I * b * n / r) := by
  have h := GaussImprimitive.gaussAt_of_isPrimitive hψ n
  have hτ := gaussAt_one_ne_zero hψ
  show ψ⁻¹ (n : ZMod r) = (gaussAt r ψ 1)⁻¹ * gaussAt r ψ n
  rw [h]
  field_simp

lemma psi_cast {r : ℕ} (ψ : DirichletCharacter ℂ r) (m : ℤ) (b : ℕ) :
    ψ (((m * r + (b : ℤ) : ℤ)) : ZMod r) = ψ (b : ZMod r) := by
  congr 1
  simp

lemma summable_h0 {r : ℕ} (ψ : DirichletCharacter ℂ r) {w : ℂ} (hw : 0 < w.im) :
    Summable (fun n : ℤ => ψ (n : ZMod r) * cexp (2 * π * I * (n : ℂ) ^ 2 * w)) := by
  have hs := ((summable_jacobiTheta₂_term_iff 0 (2 * w)).mpr (by simpa using hw)).norm
  refine Summable.of_norm_bounded hs fun n => ?_
  rw [norm_mul]
  have h1 : ‖ψ (n : ZMod r)‖ ≤ 1 := ψ.norm_le_one _
  have h2 : ‖cexp (2 * π * I * (n : ℂ) ^ 2 * w)‖ = ‖jacobiTheta₂_term n 0 (2 * w)‖ := by
    unfold jacobiTheta₂_term
    congr 2
    ring
  rw [h2]
  exact mul_le_of_le_one_left (norm_nonneg _) h1

lemma summable_h1 {r : ℕ} (ψ : DirichletCharacter ℂ r) {w : ℂ} (hw : 0 < w.im) :
    Summable (fun n : ℤ => ψ (n : ZMod r) * ((n : ℂ) * cexp (2 * π * I * (n : ℂ) ^ 2 * w))) := by
  have hs := ((summable_jacobiTheta₂'_term_iff 0 (2 * w)).mpr (by simpa using hw)).norm.div_const (2 * π)
  refine Summable.of_norm_bounded hs fun n => ?_
  rw [norm_mul]
  have h1 : ‖ψ (n : ZMod r)‖ ≤ 1 := ψ.norm_le_one _
  have h2 : ‖(n : ℂ) * cexp (2 * π * I * (n : ℂ) ^ 2 * w)‖ =
      ‖jacobiTheta₂'_term n 0 (2 * w)‖ / (2 * π) := by
    unfold jacobiTheta₂'_term jacobiTheta₂_term
    have : (2 * (π : ℂ) * I * n * cexp (2 * π * I * n * 0 + π * I * n ^ 2 * (2 * w))) =
        (2 * π * I) * ((n : ℂ) * cexp (2 * π * I * (n : ℂ) ^ 2 * w)) := by
      rw [mul_zero, zero_add]
      ring_nf
    have hn : ‖(2 * (π : ℂ) * I)‖ = 2 * π := by
      simp [abs_of_pos Real.pi_pos]
    rw [this, norm_mul (2 * (π : ℂ) * I), hn]
    field_simp [Real.pi_pos.ne']
  rw [h2]
  exact mul_le_of_le_one_left (by positivity) h1

lemma tsum_dual {r : ℕ} [NeZero r] {w : ℂ} (hw : 0 < w.im) (b : ℕ) :
    jacobiTheta₂ ((b : ℂ) / r) (2 * (-1 / (4 * (r : ℂ) ^ 2 * w))) =
      ∑' m : ℤ, (r : ℂ) * (-2 * I * w) ^ (1 / 2 : ℂ) *
        cexp (2 * π * I * (((m * r + (b : ℤ) : ℤ) : ℂ)) ^ 2 * w) := by
  have h := (hasSum_dual (r := r) hw (-(b : ℤ))).tsum_eq
  rw [show ((b : ℂ) / r) = -(((-(b : ℤ) : ℤ) : ℂ) / r) by push_cast; ring, jacobiTheta₂_neg_left, ← h]
  refine tsum_congr fun m => ?_
  congr 3
  push_cast
  ring

lemma tsum_dual' {r : ℕ} [NeZero r] {w : ℂ} (hw : 0 < w.im) (b : ℕ) :
    jacobiTheta₂' ((b : ℂ) / r) (2 * (-1 / (4 * (r : ℂ) ^ 2 * w))) =
      ∑' m : ℤ, 2 * π * I * ((r : ℂ) * (-2 * I * w) ^ (1 / 2 : ℂ) * (2 * r * w)) *
        ((((m * r + (b : ℤ) : ℤ) : ℂ)) * cexp (2 * π * I * (((m * r + (b : ℤ) : ℤ) : ℂ)) ^ 2 * w)) := by
  have h := (hasSum_dual' (r := r) hw (-(b : ℤ))).tsum_eq
  have h2 := jacobiTheta₂'_neg_left ((b : ℂ) / r) (2 * (-1 / (4 * (r : ℂ) ^ 2 * w)))
  rw [show -((b : ℂ) / r) = ((-(b : ℤ) : ℤ) : ℂ) / r by push_cast; ring] at h2
  rw [← h] at h2
  rw [neg_eq_iff_eq_neg.mp h2.symm, ← tsum_neg]
  refine tsum_congr fun m => ?_
  push_cast
  ring_nf

/-- **The even twisted theta series at the cusp 0** (Miyake 1989 `miyake1989`, Corollary 4.9.7 (2), weight $1/2$):
$\theta_\psi(-1/(4r^2w)) = r\,\tau(\psi)^{-1}(-2iw)^{1/2}\,\theta_{\overline\psi}(w)$ for $\psi$ primitive and even. -/
@[kb "miyake1989" "Cor. 4.9.7 (2): the twisted theta series of weight 1/2 under z -> -1/(4 r^2 z), Gauss-sum constant"]
theorem thetaTwist_inversion_even {r : ℕ} [NeZero r] {ψ : DirichletCharacter ℂ r} (hψ : ψ.IsPrimitive)
    (hev : ψ (-1) = 1) {w : ℂ} (hw : 0 < w.im) :
    thetaTwist ψ 1 (-1 / (4 * (r : ℂ) ^ 2 * w)) =
      (r : ℂ) / gaussAt r ψ 1 * (-2 * I * w) ^ (1 / 2 : ℂ) * thetaTwist ψ⁻¹ 1 w := by
  have hτ := gaussAt_one_ne_zero hψ
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hpar : charParity ψ = 0 := by simp [charParity, hev]
  have hpar' : charParity ψ⁻¹ = 0 := by simp [charParity, MulChar.inv_apply_eq_inv', hev]
  have hT := im_T_pos (r := r) hw
  have hA : HasSum (fun n : ℤ => ψ⁻¹ (n : ZMod r) * (n : ℂ) ^ charParity ψ *
      cexp (2 * π * I * ((1 : ℕ) : ℂ) * (n : ℂ) ^ 2 * (-1 / (4 * (r : ℂ) ^ 2 * w))))
      ((gaussAt r ψ 1)⁻¹ * ∑ b ∈ Finset.range r,
        ψ (b : ZMod r) * jacobiTheta₂ ((b : ℂ) / r) (2 * (-1 / (4 * (r : ℂ) ^ 2 * w)))) := by
    have := hasSum_sum (s := Finset.range r)
      (f := fun (b : ℕ) (n : ℤ) => ((gaussAt r ψ 1)⁻¹ * ψ (b : ZMod r)) *
        jacobiTheta₂_term n ((b : ℂ) / r) (2 * (-1 / (4 * (r : ℂ) ^ 2 * w))))
      (a := fun b => ((gaussAt r ψ 1)⁻¹ * ψ (b : ZMod r)) *
        jacobiTheta₂ ((b : ℂ) / r) (2 * (-1 / (4 * (r : ℂ) ^ 2 * w))))
      (fun b _ => (hasSum_jacobiTheta₂_term _ hT).mul_left _)
    rw [Finset.mul_sum]
    convert this using 1
    · funext n
      rw [psi_inv_expand hψ n, hpar, pow_zero, mul_one, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [jacobiTheta₂_term]
      rw [mul_assoc, mul_assoc, ← Complex.exp_add]
      rw [← mul_assoc]
      congr 2
      push_cast
      ring
    · refine Finset.sum_congr rfl fun b _ => ?_
      ring
  unfold thetaTwist
  rw [hA.tsum_eq]
  have hB : ∑ b ∈ Finset.range r,
      ψ (b : ZMod r) * jacobiTheta₂ ((b : ℂ) / r) (2 * (-1 / (4 * (r : ℂ) ^ 2 * w))) =
      (r : ℂ) * (-2 * I * w) ^ (1 / 2 : ℂ) * ∑ b ∈ Finset.range r, ∑' m : ℤ,
        (fun n : ℤ => ψ (n : ZMod r) * cexp (2 * π * I * (n : ℂ) ^ 2 * w)) (m * r + (b : ℤ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [tsum_dual hw b, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    simp only [psi_cast]
    ring
  rw [hB, sum_reindex _ (summable_h0 ψ hw)]
  have hC : ∑' n : ℤ, ψ⁻¹⁻¹ (n : ZMod r) * (n : ℂ) ^ charParity ψ⁻¹ *
      cexp (2 * π * I * ((1 : ℕ) : ℂ) * (n : ℂ) ^ 2 * w) =
      ∑' n : ℤ, ψ (n : ZMod r) * cexp (2 * π * I * (n : ℂ) ^ 2 * w) := by
    refine tsum_congr fun n => ?_
    rw [inv_inv, hpar']
    simp
  rw [hC]
  ring

/-- **The odd twisted theta series at the cusp 0** (Miyake 1989 `miyake1989`, Corollary 4.9.7 (2), weight $3/2$):
$\theta_\psi(-1/(4r^2w)) = r\,\tau(\psi)^{-1}(-2iw)^{1/2}(2rw)\,\theta_{\overline\psi}(w)$ for $\psi$ primitive and odd. -/
@[kb "miyake1989" "Cor. 4.9.7 (2): the twisted theta series of weight 3/2 under z -> -1/(4 r^2 z), Gauss-sum constant"]
theorem thetaTwist_inversion_odd {r : ℕ} [NeZero r] {ψ : DirichletCharacter ℂ r} (hψ : ψ.IsPrimitive)
    (hodd : ψ (-1) = -1) {w : ℂ} (hw : 0 < w.im) :
    thetaTwist ψ 1 (-1 / (4 * (r : ℂ) ^ 2 * w)) =
      (r : ℂ) / gaussAt r ψ 1 * (-2 * I * w) ^ (1 / 2 : ℂ) * (2 * r * w) * thetaTwist ψ⁻¹ 1 w := by
  have hτ := gaussAt_one_ne_zero hψ
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hm1 : (-1 : ℂ) ≠ 1 := by norm_num
  have hpar : charParity ψ = 1 := by simp [charParity, hodd, hm1]
  have hpar' : charParity ψ⁻¹ = 1 := by simp [charParity, MulChar.inv_apply_eq_inv', hodd, hm1]
  have hT := im_T_pos (r := r) hw
  have h2pi : (2 * (π : ℂ) * I) ≠ 0 := by
    have := Real.pi_pos.ne'
    simp [this]
  have hA : HasSum (fun n : ℤ => ψ⁻¹ (n : ZMod r) * (n : ℂ) ^ charParity ψ *
      cexp (2 * π * I * ((1 : ℕ) : ℂ) * (n : ℂ) ^ 2 * (-1 / (4 * (r : ℂ) ^ 2 * w))))
      ((gaussAt r ψ 1)⁻¹ / (2 * π * I) * ∑ b ∈ Finset.range r,
        ψ (b : ZMod r) * jacobiTheta₂' ((b : ℂ) / r) (2 * (-1 / (4 * (r : ℂ) ^ 2 * w)))) := by
    have := hasSum_sum (s := Finset.range r)
      (f := fun (b : ℕ) (n : ℤ) => ((gaussAt r ψ 1)⁻¹ / (2 * π * I) * ψ (b : ZMod r)) *
        jacobiTheta₂'_term n ((b : ℂ) / r) (2 * (-1 / (4 * (r : ℂ) ^ 2 * w))))
      (a := fun b => ((gaussAt r ψ 1)⁻¹ / (2 * π * I) * ψ (b : ZMod r)) *
        jacobiTheta₂' ((b : ℂ) / r) (2 * (-1 / (4 * (r : ℂ) ^ 2 * w))))
      (fun b _ => (hasSum_jacobiTheta₂'_term _ hT).mul_left _)
    rw [Finset.mul_sum]
    convert this using 1
    · funext n
      rw [psi_inv_expand hψ n, hpar, pow_one, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [jacobiTheta₂'_term, jacobiTheta₂_term]
      have : cexp (2 * π * I * b * n / r + 2 * π * I * ((1 : ℕ) : ℂ) * (n : ℂ) ^ 2 *
          (-1 / (4 * (r : ℂ) ^ 2 * w))) =
          cexp (2 * π * I * n * (b / r) + π * I * n ^ 2 * (2 * (-1 / (4 * r ^ 2 * w)))) := by
        congr 1
        push_cast
        ring
      rw [← this]
      rw [Complex.exp_add]
      field_simp
    · refine Finset.sum_congr rfl fun b _ => ?_
      ring
  unfold thetaTwist
  rw [hA.tsum_eq]
  have hB : ∑ b ∈ Finset.range r,
      ψ (b : ZMod r) * jacobiTheta₂' ((b : ℂ) / r) (2 * (-1 / (4 * (r : ℂ) ^ 2 * w))) =
      (r : ℂ) * (-2 * I * w) ^ (1 / 2 : ℂ) * (2 * r * w) * (2 * π * I) * ∑ b ∈ Finset.range r, ∑' m : ℤ,
        (fun n : ℤ => ψ (n : ZMod r) * ((n : ℂ) * cexp (2 * π * I * (n : ℂ) ^ 2 * w))) (m * r + (b : ℤ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [tsum_dual' hw b, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    simp only [psi_cast]
    ring
  rw [hB, sum_reindex _ (summable_h1 ψ hw)]
  have hC : ∑' n : ℤ, ψ⁻¹⁻¹ (n : ZMod r) * (n : ℂ) ^ charParity ψ⁻¹ *
      cexp (2 * π * I * ((1 : ℕ) : ℂ) * (n : ℂ) ^ 2 * w) =
      ∑' n : ℤ, ψ (n : ZMod r) * ((n : ℂ) * cexp (2 * π * I * (n : ℂ) ^ 2 * w)) := by
    refine tsum_congr fun n => ?_
    rw [inv_inv, hpar']
    simp
    ring
  rw [hC]
  field_simp

end ThetaCuspZero

end ModularFormsKB.HalfIntegral
