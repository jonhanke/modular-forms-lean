import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import ModularFormsKB.Citation
/-!
# Miyake §1.3: stabilizers and centralizers in $\mathrm{GL}_2(\mathbb R)$

Miyake, *Modular Forms* (Springer 1989), §1.3, pp. 7–10.

## Conventions
* $\mathrm{GL}_2(\mathbb R)$ acts on $\mathbb H$ by Mathlib's `UpperHalfPlane.glAction` (for
  $\det > 0$ this is $z \mapsto (az+b)/(cz+d)$) and on $\mathbb R \cup \{\infty\}$ = `OnePoint ℝ`
  by `OnePoint.instGLAction` (Möbius transformations on the projective line).
* Matrix entries are 0-based: Miyake's $\begin{pmatrix} a & b \\ c & d \end{pmatrix}$ is
  `g 0 0, g 0 1, g 1 0, g 1 1`.
* Miyake's classes: a non-scalar $\alpha$ is elliptic, parabolic, hyperbolic when
  $\operatorname{tr}(\alpha)^2 < , = , > 4\det(\alpha)$; these are Mathlib's `Matrix.IsElliptic`,
  `Matrix.IsParabolic`, `Matrix.IsHyperbolic` (discriminant $\operatorname{tr}^2 - 4\det$).
* $\mathrm{GL}_2^+(\mathbb R)^{(x)}$ (Miyake (1.3.1)) is the set of $\alpha \in \mathrm{GL}_2^+(\mathbb R)$
  fixing $x$ that are parabolic or scalar.
-/

open Matrix UpperHalfPlane OnePoint

namespace ModularFormsKB.Miyake

/-- Fixed points of an element of positive determinant, in real coordinates. -/
lemma smul_eq_self_iff_of_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (z : ℍ) :
    g • z = z ↔ g 1 0 * (z.re ^ 2 - z.im ^ 2) + (g 1 1 - g 0 0) * z.re - g 0 1 = 0 ∧
      (2 * g 1 0 * z.re + g 1 1 - g 0 0) * z.im = 0 := by
  have h : g • z = z ↔ (z : ℂ) * denom g z = num g z := by
    rw [UpperHalfPlane.ext_iff, coe_smul_of_det_pos hg, div_eq_iff (denom_ne_zero g z), mul_comm]
    exact eq_comm
  rw [h, Complex.ext_iff]
  simp only [num, denom, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith

/-- Commutation of two elements of `GL₂`, in entries. -/
lemma commute_iff_entries (α β : GL (Fin 2) ℝ) :
    Commute α β ↔ (α 0 0 * β 0 0 + α 0 1 * β 1 0 = β 0 0 * α 0 0 + β 0 1 * α 1 0) ∧
      (α 0 0 * β 0 1 + α 0 1 * β 1 1 = β 0 0 * α 0 1 + β 0 1 * α 1 1) ∧
      (α 1 0 * β 0 0 + α 1 1 * β 1 0 = β 1 0 * α 0 0 + β 1 1 * α 1 0) ∧
      (α 1 0 * β 0 1 + α 1 1 * β 1 1 = β 1 0 * α 0 1 + β 1 1 * α 1 1) := by
  rw [commute_iff_eq, Units.ext_iff, Units.val_mul, Units.val_mul]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
    exact ⟨h00, h01, h10, h11⟩
  · rintro ⟨h00, h01, h10, h11⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> assumption

/-- $\det g = ad - bc$ for $g \in \mathrm{GL}_2(\mathbb R)$. -/
lemma det_eq' (g : GL (Fin 2) ℝ) : g.det.val = g 0 0 * g 1 1 - g 0 1 * g 1 0 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

/-- If `c = 0`, then `g` fixes `0` iff `b = 0`. -/
lemma smul_zero_eq_self_iff_of_c (g : GL (Fin 2) ℝ) (h : g 1 0 = 0) :
    g • ((0 : ℝ) : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ) ↔ g 0 1 = 0 := by
  have hd : g 1 1 ≠ 0 := by
    intro hd
    have h0 : g.det.val ≠ 0 := g.det.ne_zero
    rw [det_eq', h, hd] at h0
    simp at h0
  rw [OnePoint.smul_some_eq_ite]
  split_ifs with hc
  · exact absurd hc (by simpa [h] using hd)
  · simp [h, hd]

/-- A $2 \times 2$ matrix is scalar iff $b = c = 0$ and $a = d$. -/
lemma scalar_mem_iff (m : Matrix (Fin 2) (Fin 2) ℝ) :
    m ∈ Set.range (scalar (Fin 2)) ↔ m 0 1 = 0 ∧ m 1 0 = 0 ∧ m 0 0 = m 1 1 := by
  constructor
  · rintro ⟨r, rfl⟩
    simp
  · rintro ⟨h1, h2, h3⟩
    refine ⟨m 1 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]

/-- **Miyake, Lemma 1.3.2 (1)**, first equality: for $\alpha \in \mathrm{GL}_2(\mathbb R)$ with
$\det\alpha > 0$, $\alpha i = i$ if and only if $\alpha = \begin{pmatrix} a & b \\ -b & a\end{pmatrix}$,
i.e. $\mathrm{GL}_2^+(\mathbb R)_i = \mathbb R^\times \cdot \mathrm{SO}_2(\mathbb R)$. -/
@[kb "miyake1989" "Lemma 1.3.2 (1), p. 8"]
theorem glPos_smul_I_eq_I_iff (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) :
    g • I = I ↔ g 1 1 = g 0 0 ∧ g 1 0 = -g 0 1 := by
  rw [smul_eq_self_iff_of_pos hg]
  simp only [UpperHalfPlane.I_re, UpperHalfPlane.I_im]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith

/-- **Miyake, Lemma 1.3.2 (1)**, second equality: $\mathrm{GL}_2^+(\mathbb R)^{(\infty)} =
\left\{\begin{pmatrix} a & b \\ 0 & a\end{pmatrix} : a \in \mathbb R^\times, b \in \mathbb R\right\}$:
an element of positive determinant fixes $\infty$ and is parabolic or scalar if and only if
$c = 0$ and $a = d$. -/
@[kb "miyake1989" "Lemma 1.3.2 (1), p. 8"]
theorem glPos_fix_infty_parabolic_iff (g : GL (Fin 2) ℝ) (_hg : 0 < g.det.val) :
    (g • (∞ : OnePoint ℝ) = ∞ ∧
        ((g : Matrix (Fin 2) (Fin 2) ℝ).IsParabolic ∨
          (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.range (scalar (Fin 2)))) ↔
      g 1 0 = 0 ∧ g 0 0 = g 1 1 := by
  rw [OnePoint.smul_infty_eq_self_iff]
  constructor
  · rintro ⟨h, hp | hs⟩
    · have := (Matrix.isParabolic_iff_of_upperTriangular (m := (g : Matrix (Fin 2) (Fin 2) ℝ)) h).1 hp
      exact ⟨h, this.1⟩
    · exact ⟨h, ((scalar_mem_iff _).1 hs).2.2⟩
  · rintro ⟨h, h2⟩
    refine ⟨h, ?_⟩
    by_cases hb : g 0 1 = 0
    · right
      exact (scalar_mem_iff _).2 ⟨hb, h, h2⟩
    · left
      exact (Matrix.isParabolic_iff_of_upperTriangular (m := (g : Matrix (Fin 2) (Fin 2) ℝ)) h).2
        ⟨h2, hb⟩

/-- **Miyake, Lemma 1.3.2 (1)**, third equality: $\mathrm{GL}_2^+(\mathbb R)_{\infty,0} =
\left\{\begin{pmatrix} a & 0 \\ 0 & d\end{pmatrix} : ad > 0\right\}$. -/
@[kb "miyake1989" "Lemma 1.3.2 (1), p. 8"]
theorem glPos_fix_infty_zero_iff (g : GL (Fin 2) ℝ) (_hg : 0 < g.det.val) :
    (g • (∞ : OnePoint ℝ) = ∞ ∧ g • ((0 : ℝ) : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ)) ↔
      g 1 0 = 0 ∧ g 0 1 = 0 := by
  rw [OnePoint.smul_infty_eq_self_iff]
  constructor
  · rintro ⟨h, h0⟩
    exact ⟨h, (smul_zero_eq_self_iff_of_c g h).1 h0⟩
  · rintro ⟨h, h1⟩
    exact ⟨h, (smul_zero_eq_self_iff_of_c g h).2 h1⟩

/-- **Miyake, Lemma 1.3.3 (1).** Let $\alpha \in \mathrm{GL}_2^+(\mathbb R)$ be non-scalar with a
fixed point $z \in \mathbb H$. Then the centralizer of $\alpha$ in $\mathrm{GL}_2(\mathbb R)$ is
$\mathrm{GL}_2^+(\mathbb R)_z$: $\beta$ commutes with $\alpha$ iff $\det\beta > 0$ and $\beta z = z$.
(In particular $Z(\alpha) = Z(\alpha) \cap \mathrm{GL}_2^+(\mathbb R)$.) -/
@[kb "miyake1989" "Lemma 1.3.3 (1), p. 9"]
theorem commute_iff_of_smul_eq_self {α : GL (Fin 2) ℝ} (hα : 0 < α.det.val)
    (hns : (α : Matrix (Fin 2) (Fin 2) ℝ) ∉ Set.range (scalar (Fin 2))) {z : ℍ} (hz : α • z = z)
    (β : GL (Fin 2) ℝ) :
    Commute α β ↔ 0 < β.det.val ∧ β • z = z := by
  obtain ⟨h1, h2⟩ := (smul_eq_self_iff_of_pos hα z).1 hz
  have hy := z.im_pos
  have h2' : 2 * α 1 0 * z.re + α 1 1 - α 0 0 = 0 := (mul_eq_zero.1 h2).resolve_right hy.ne'
  have hd : α 1 1 = α 0 0 - 2 * α 1 0 * z.re := by linarith
  have hb : α 0 1 = -α 1 0 * (z.re ^ 2 + z.im ^ 2) := by
    rw [hd] at h1; nlinarith
  have hc : α 1 0 ≠ 0 := by
    intro hc
    apply hns
    rw [scalar_mem_iff]
    rw [hc] at hd hb
    refine ⟨?_, hc, ?_⟩ <;> simp [hb, hd]
  rw [commute_iff_entries]
  constructor
  · rintro ⟨E1, E2, E3, E4⟩
    have hq : β 0 1 = -β 1 0 * (z.re ^ 2 + z.im ^ 2) := by
      apply mul_left_cancel₀ hc
      rw [hb] at E1; nlinarith
    have hs : β 1 1 = β 0 0 - 2 * β 1 0 * z.re := by
      apply mul_left_cancel₀ hc
      rw [hd] at E3; nlinarith
    have hdet : 0 < β.det.val := by
      have hne : β.det.val ≠ 0 := β.det.ne_zero
      have : 0 ≤ β.det.val := by
        rw [det_eq', hq, hs]
        nlinarith [sq_nonneg (β 0 0 - β 1 0 * z.re), sq_nonneg (β 1 0 * z.im)]
      exact lt_of_le_of_ne this (Ne.symm hne)
    refine ⟨hdet, (smul_eq_self_iff_of_pos hdet z).2 ⟨?_, ?_⟩⟩
    · rw [hq, hs]; ring
    · rw [hs]; ring
  · rintro ⟨hdet, hβ⟩
    obtain ⟨g1, g2⟩ := (smul_eq_self_iff_of_pos hdet z).1 hβ
    have g2' : 2 * β 1 0 * z.re + β 1 1 - β 0 0 = 0 := (mul_eq_zero.1 g2).resolve_right hy.ne'
    have hs : β 1 1 = β 0 0 - 2 * β 1 0 * z.re := by linarith
    have hq : β 0 1 = -β 1 0 * (z.re ^ 2 + z.im ^ 2) := by
      rw [hs] at g1; nlinarith
    simp only [hb, hd, hq, hs]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- **Miyake, Lemma 1.3.3 (2)**, at the cusp $\infty$: for a parabolic $\alpha$ fixing $\infty$, the
centralizer of $\alpha$ in $\mathrm{GL}_2(\mathbb R)$ is $\mathrm{GL}_2^+(\mathbb R)^{(\infty)}$, the
matrices $\begin{pmatrix} a & b \\ 0 & a\end{pmatrix}$. Miyake states it at any $x \in \mathbb R \cup
\{\infty\}$, which follows by conjugation (Lemma 1.3.2 (2)); special case. -/
@[kb "miyake1989" "Lemma 1.3.3 (2), p. 9"]
theorem commute_iff_of_isParabolic_infty {α : GL (Fin 2) ℝ}
    (hpar : (α : Matrix (Fin 2) (Fin 2) ℝ).IsParabolic) (hα : α • (∞ : OnePoint ℝ) = ∞)
    (β : GL (Fin 2) ℝ) :
    Commute α β ↔ β 1 0 = 0 ∧ β 0 0 = β 1 1 := by
  have hc := OnePoint.smul_infty_eq_self_iff.1 hα
  obtain ⟨had, hb⟩ := (Matrix.isParabolic_iff_of_upperTriangular
    (m := (α : Matrix (Fin 2) (Fin 2) ℝ)) hc).1 hpar
  rw [commute_iff_entries]
  constructor
  · rintro ⟨E1, E2, E3, E4⟩
    have hr : β 1 0 = 0 := by
      have : α 0 1 * β 1 0 = 0 := by rw [hc] at E1; linarith
      exact (mul_eq_zero.1 this).resolve_left hb
    refine ⟨hr, ?_⟩
    have : α 0 1 * (β 1 1 - β 0 0) = 0 := by
      rw [← had] at E2; linarith
    have := (mul_eq_zero.1 this).resolve_left hb
    linarith
  · rintro ⟨hr, hp⟩
    simp only [hc, ← had, hr, ← hp]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- **Miyake, Lemma 1.3.3 (3)**, at the pair $\{\infty, 0\}$: for a hyperbolic $\alpha$ fixing $\infty$
and $0$ (a non-scalar diagonal matrix), $\beta$ commutes with $\alpha$ iff $\beta$ is diagonal; the
centralizer meets $\mathrm{GL}_2^+(\mathbb R)$ in $\mathrm{GL}_2^+(\mathbb R)_{\infty,0}$ and contains
$\operatorname{diag}(1,-1)$ of negative determinant, so the index is 2. Miyake states it for any pair
$x \ne x'$, which follows by conjugation; special case. -/
@[kb "miyake1989" "Lemma 1.3.3 (3), p. 9"]
theorem commute_iff_of_isHyperbolic_infty_zero {α : GL (Fin 2) ℝ}
    (hhyp : (α : Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic) (hα : α • (∞ : OnePoint ℝ) = ∞)
    (hα0 : α • ((0 : ℝ) : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ)) (β : GL (Fin 2) ℝ) :
    Commute α β ↔ β 1 0 = 0 ∧ β 0 1 = 0 := by
  have hc := OnePoint.smul_infty_eq_self_iff.1 hα
  have hb := (smul_zero_eq_self_iff_of_c α hc).1 hα0
  have hne : α 0 0 - α 1 1 ≠ 0 := by
    intro h
    have : (α : Matrix (Fin 2) (Fin 2) ℝ).discr = 0 := by
      rw [discr_fin_two, trace_fin_two, det_fin_two]
      simp only [hc, hb]
      have : α 0 0 = α 1 1 := by linarith
      rw [this]; ring
    exact absurd hhyp (by rw [Matrix.IsHyperbolic, this]; exact lt_irrefl _)
  rw [commute_iff_entries]
  constructor
  · rintro ⟨E1, E2, E3, E4⟩
    simp only [hc, hb] at E2 E3
    constructor
    · have : (α 0 0 - α 1 1) * β 1 0 = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    · have : (α 0 0 - α 1 1) * β 0 1 = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
  · rintro ⟨hr, hq⟩
    simp only [hc, hb, hr, hq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- **Miyake, Lemma 1.3.3 (3)**, index statement at $\{\infty, 0\}$: for $\alpha$ as in
`commute_iff_of_isHyperbolic_infty_zero`, $[Z(\alpha) : Z(\alpha) \cap \mathrm{GL}_2^+(\mathbb R)] = 2$. -/
@[kb "miyake1989" "Lemma 1.3.3 (3), p. 9"]
theorem index_centralizer_glPos_of_isHyperbolic {α : GL (Fin 2) ℝ}
    (hhyp : (α : Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic) (hα : α • (∞ : OnePoint ℝ) = ∞)
    (hα0 : α • ((0 : ℝ) : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ)) :
    (GLPos (Fin 2) ℝ).relIndex (Subgroup.centralizer {α}) = 2 := by
  have hmem : ∀ b : GL (Fin 2) ℝ, b ∈ Subgroup.centralizer {α} ↔ b 1 0 = 0 ∧ b 0 1 = 0 := by
    intro b
    rw [Subgroup.mem_centralizer_singleton_iff,
      ← commute_iff_of_isHyperbolic_infty_zero hhyp hα hα0 b]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hJ : J ∈ Subgroup.centralizer {α} := by
    rw [hmem]; simp [J]
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨J, hJ, fun b _ => ?_⟩
  have hne : (b.det : ℝ) ≠ 0 := b.det.ne_zero
  have hJd : ((J.det : ℝˣ) : ℝ) = -1 := by rw [det_J]; simp
  simp only [Matrix.mem_glpos, map_mul, Units.val_mul, hJd]
  rcases lt_or_gt_of_ne hne with h | h
  · left; constructor <;> linarith
  · right; constructor <;> linarith

/-! ### Lemma 1.3.4: normalizers -/
/-- Entries of a product in `GL₂(ℝ)`. -/
lemma mul_apply' (g h : GL (Fin 2) ℝ) (i j : Fin 2) :
    (g * h) i j = g i 0 * h 0 j + g i 1 * h 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Entries of the inverse in `GL₂(ℝ)`: `g⁻¹ = D⁻¹ [[d, -b], [-c, a]]`. -/
lemma inv_entries (g : GL (Fin 2) ℝ) :
    (g⁻¹) 0 0 = g 1 1 / g.det.val ∧ (g⁻¹) 0 1 = -g 0 1 / g.det.val ∧
    (g⁻¹) 1 0 = -g 1 0 / g.det.val ∧ (g⁻¹) 1 1 = g 0 0 / g.det.val := by
  have hD : g.det.val ≠ 0 := g.det.ne_zero
  have hD' : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by rwa [det_eq'] at hD
  have h1 : (g * g⁻¹) 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by rw [mul_inv_cancel]; rfl
  have h2 : (g * g⁻¹) 0 1 = (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := by rw [mul_inv_cancel]; rfl
  have h3 : (g * g⁻¹) 1 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by rw [mul_inv_cancel]; rfl
  have h4 : (g * g⁻¹) 1 1 = (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by rw [mul_inv_cancel]; rfl
  simp only [mul_apply', Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h1 h2 h3 h4
  rw [det_eq']
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [eq_div_iff hD']
  · linear_combination g 1 1 * h1 - g 0 1 * h3
  · linear_combination g 1 1 * h2 - g 0 1 * h4
  · linear_combination g 0 0 * h3 - g 1 0 * h1
  · linear_combination g 0 0 * h4 - g 1 0 * h2

/-- A `GL₂(ℝ)` element from explicit entries. -/
noncomputable def mk' (a b c d : ℝ) (h : a * d - b * c ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by simpa [Matrix.det_fin_two] using h)

@[simp] lemma mk'_00 (a b c d : ℝ) (h : a * d - b * c ≠ 0) : mk' a b c d h 0 0 = a := by
  simp [mk', Matrix.GeneralLinearGroup.mkOfDetNeZero]

@[simp] lemma mk'_01 (a b c d : ℝ) (h : a * d - b * c ≠ 0) : mk' a b c d h 0 1 = b := by
  simp [mk', Matrix.GeneralLinearGroup.mkOfDetNeZero]

@[simp] lemma mk'_10 (a b c d : ℝ) (h : a * d - b * c ≠ 0) : mk' a b c d h 1 0 = c := by
  simp [mk', Matrix.GeneralLinearGroup.mkOfDetNeZero]

@[simp] lemma mk'_11 (a b c d : ℝ) (h : a * d - b * c ≠ 0) : mk' a b c d h 1 1 = d := by
  simp [mk', Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- Determinant of a product in `GL₂(ℝ)`. -/
lemma det_mul' (g h : GL (Fin 2) ℝ) : (g * h).det.val = g.det.val * h.det.val := by
  simp [Matrix.GeneralLinearGroup.val_det_apply]

/-- Determinant of `mk'`. -/
lemma mk'_det (a b c d : ℝ) (h : a * d - b * c ≠ 0) : (mk' a b c d h).det.val = a * d - b * c := by
  rw [det_eq']; simp

/-- A positive-determinant element is in `GLPos`. -/
lemma mem_glPos_iff (g : GL (Fin 2) ℝ) : g ∈ GLPos (Fin 2) ℝ ↔ 0 < g.det.val :=
  Matrix.mem_glpos g

/-- $\mathrm{GL}_2^+(\mathbb R)_i$: elements of positive determinant fixing $i \in \mathbb H$
(Miyake (1.3.2); equal to $\mathbb R^\times\mathrm{SO}_2(\mathbb R)$ by `glPos_smul_I_eq_I_iff`). -/
noncomputable def glPosStabI : Subgroup (GL (Fin 2) ℝ) :=
  GLPos (Fin 2) ℝ ⊓ MulAction.stabilizer (GL (Fin 2) ℝ) I

/-- $\mathrm{GL}_2^+(\mathbb R)^{(\infty)}$: the matrices $\begin{pmatrix} a & b \\ 0 & a\end{pmatrix}$,
$a \ne 0$ (Miyake (1.3.1); the parabolic-or-scalar elements of positive determinant fixing $\infty$, by
`glPos_fix_infty_parabolic_iff`). -/
def glPosParabolicInfty : Subgroup (GL (Fin 2) ℝ) where
  carrier := {g | g 1 0 = 0 ∧ g 0 0 = g 1 1}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩ <;> simp only [mul_apply', ha1, hb1, ha2, hb2] <;> ring
  one_mem' := by
    refine ⟨?_, ?_⟩ <;> rfl
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    obtain ⟨h00, -, h10, h11⟩ := inv_entries a
    refine ⟨?_, ?_⟩
    · rw [h10, ha1]; simp
    · rw [h00, h11, ha2]

/-- $\mathrm{GL}_2^+(\mathbb R)_{\infty,0}$: elements of positive determinant fixing $\infty$ and $0$
(Miyake (1.3.2); the diagonal matrices with $ad > 0$, by `glPos_fix_infty_zero_iff`). -/
noncomputable def glPosStabInftyZero : Subgroup (GL (Fin 2) ℝ) :=
  GLPos (Fin 2) ℝ ⊓ MulAction.stabilizer (GL (Fin 2) ℝ) (∞ : OnePoint ℝ) ⊓
    MulAction.stabilizer (GL (Fin 2) ℝ) ((0 : ℝ) : OnePoint ℝ)

/-- Membership in `glPosStabI`, in entries. -/
lemma mem_stabI_iff (g : GL (Fin 2) ℝ) :
    g ∈ glPosStabI ↔ 0 < g.det.val ∧ g 1 1 = g 0 0 ∧ g 1 0 = -g 0 1 := by
  unfold glPosStabI
  rw [Subgroup.mem_inf, mem_glPos_iff, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, (glPos_smul_I_eq_I_iff g h).1 h'⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, (glPos_smul_I_eq_I_iff g h).2 h'⟩

/-- Membership in `glPosStabInftyZero`, in entries. -/
lemma mem_stabInftyZero_iff (g : GL (Fin 2) ℝ) :
    g ∈ glPosStabInftyZero ↔ 0 < g.det.val ∧ g 1 0 = 0 ∧ g 0 1 = 0 := by
  unfold glPosStabInftyZero
  rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_glPos_iff, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨⟨h, h1⟩, h2⟩
    exact ⟨h, (glPos_fix_infty_zero_iff g h).1 ⟨h1, h2⟩⟩
  · rintro ⟨h, h'⟩
    exact ⟨⟨h, ((glPos_fix_infty_zero_iff g h).2 h').1⟩, ((glPos_fix_infty_zero_iff g h).2 h').2⟩

/-- Membership in `glPosParabolicInfty`, in entries. -/
lemma mem_parabolicInfty_iff (g : GL (Fin 2) ℝ) :
    g ∈ glPosParabolicInfty ↔ g 1 0 = 0 ∧ g 0 0 = g 1 1 := Iff.rfl

/-- Normalizer criterion without inverses. -/
lemma mem_normalizer_iff_mul (S : Subgroup (GL (Fin 2) ℝ)) (g : GL (Fin 2) ℝ) :
    g ∈ Subgroup.normalizer (S : Set (GL (Fin 2) ℝ)) ↔ ∀ n, n * g ∈ S ↔ g * n ∈ S := by
  rw [Subgroup.mem_set_normalizer_iff']
  simp only [SetLike.mem_coe]

/-- If `N` contains an element of negative determinant, then `GL₂⁺` has index 2 in `N`. -/
lemma relIndex_glPos_eq_two_of_neg_det (N : Subgroup (GL (Fin 2) ℝ)) (s : GL (Fin 2) ℝ)
    (hs : s ∈ N) (hd : s.det.val < 0) : (GLPos (Fin 2) ℝ).relIndex N = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨s, hs⟩, fun b => ?_⟩
  have hb : b.1.det.val ≠ 0 := b.1.det.ne_zero
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, mem_glPos_iff, det_mul']
  rcases lt_or_gt_of_ne hb with h | h
  · exact Or.inl ⟨by nlinarith, by linarith⟩
  · exact Or.inr ⟨h, by nlinarith⟩

/-- The reflection `diag(-1, 1)`. -/
noncomputable def sRefl : GL (Fin 2) ℝ := mk' (-1) 0 0 1 (by norm_num)

/-- The rotation `[[0, 1], [-1, 0]]`. -/
noncomputable def wRot : GL (Fin 2) ℝ := mk' 0 1 (-1) 0 (by norm_num)

/-- `det (diag(-1, 1)) = -1`. -/
lemma sRefl_det : sRefl.det.val = -1 := by
  unfold sRefl; rw [mk'_det]; norm_num

/-- `det w = 1` for `w = [[0, 1], [-1, 0]]`. -/
lemma wRot_det : wRot.det.val = 1 := by
  unfold wRot; rw [mk'_det]; norm_num

/-- Entries of `sRefl`. -/
lemma sRefl_entries : sRefl 0 0 = -1 ∧ sRefl 0 1 = 0 ∧ sRefl 1 0 = 0 ∧ sRefl 1 1 = 1 := by
  simp [sRefl]

/-- Entries of `wRot`. -/
lemma wRot_entries : wRot 0 0 = 0 ∧ wRot 0 1 = 1 ∧ wRot 1 0 = -1 ∧ wRot 1 1 = 0 := by
  simp [wRot]

/-- `diag(-1, 1)` normalizes `glPosStabI`. -/
lemma sRefl_mem_normalizer_stabI :
    sRefl ∈ Subgroup.normalizer (glPosStabI : Set (GL (Fin 2) ℝ)) := by
  obtain ⟨a, b, c, d⟩ := sRefl_entries
  rw [mem_normalizer_iff_mul]
  intro n
  rw [mem_stabI_iff, mem_stabI_iff]
  simp only [det_mul', mul_apply', a, b, c, d, sRefl_det]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- `diag(-1, 1)` normalizes `glPosParabolicInfty`. -/
lemma sRefl_mem_normalizer_parabolic :
    sRefl ∈ Subgroup.normalizer (glPosParabolicInfty : Set (GL (Fin 2) ℝ)) := by
  obtain ⟨a, b, c, d⟩ := sRefl_entries
  rw [mem_normalizer_iff_mul]
  intro n
  rw [mem_parabolicInfty_iff, mem_parabolicInfty_iff]
  simp only [mul_apply', a, b, c, d]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, ?_⟩ <;> linarith

/-- `diag(-1, 1)` normalizes `glPosStabInftyZero`. -/
lemma sRefl_mem_normalizer_stabInftyZero :
    sRefl ∈ Subgroup.normalizer (glPosStabInftyZero : Set (GL (Fin 2) ℝ)) := by
  obtain ⟨a, b, c, d⟩ := sRefl_entries
  rw [mem_normalizer_iff_mul]
  intro n
  rw [mem_stabInftyZero_iff, mem_stabInftyZero_iff]
  simp only [det_mul', mul_apply', a, b, c, d, sRefl_det]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- `w` normalizes `glPosStabInftyZero` (it swaps the diagonal entries). -/
lemma wRot_mem_normalizer_stabInftyZero :
    wRot ∈ Subgroup.normalizer (glPosStabInftyZero : Set (GL (Fin 2) ℝ)) := by
  obtain ⟨a, b, c, d⟩ := wRot_entries
  rw [mem_normalizer_iff_mul]
  intro n
  rw [mem_stabInftyZero_iff, mem_stabInftyZero_iff]
  simp only [det_mul', mul_apply', a, b, c, d, wRot_det]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- An element of `GL₂⁺` normalizing `glPosStabI` lies in `glPosStabI`. -/
lemma mem_stabI_of_mem_normalizer (g : GL (Fin 2) ℝ)
    (hn : g ∈ Subgroup.normalizer (glPosStabI : Set (GL (Fin 2) ℝ))) (hd : 0 < g.det.val) :
    g ∈ glPosStabI := by
  have hD := det_eq' g
  have hne : (-g 1 0) * g 0 1 - g 0 0 * (-g 1 1) ≠ 0 := by
    have := g.det.ne_zero
    intro h; apply this; rw [hD]; linarith
  set n : GL (Fin 2) ℝ := mk' (-g 1 0) (g 0 0) (-g 1 1) (g 0 1) hne with hn_def
  have hn_det : n.det.val = g.det.val := by
    rw [hn_def, mk'_det, hD]; ring
  have e00 : n 0 0 = -g 1 0 := by simp [hn_def]
  have e01 : n 0 1 = g 0 0 := by simp [hn_def]
  have e10 : n 1 0 = -g 1 1 := by simp [hn_def]
  have e11 : n 1 1 = g 0 1 := by simp [hn_def]
  have h1 : n * g ∈ glPosStabI := by
    rw [mem_stabI_iff, det_mul', hn_det]
    refine ⟨mul_pos hd hd, ?_, ?_⟩ <;> simp only [mul_apply', e00, e01, e10, e11] <;> ring
  have h2 := ((mem_normalizer_iff_mul _ g).1 hn n).1 h1
  rw [mem_stabI_iff] at h2
  obtain ⟨-, h2a, h2b⟩ := h2
  simp only [mul_apply', e00, e01, e10, e11] at h2a h2b
  rw [mem_stabI_iff]
  refine ⟨hd, ?_⟩
  have hsq : (g 0 0 * g 1 1 - g 0 1 * g 1 0) ^ 2 = (g 0 0 ^ 2 + g 0 1 ^ 2) ^ 2 := by
    have : (g 0 0 * g 1 1 - g 0 1 * g 1 0) ^ 2 =
        (g 0 0 ^ 2 + g 0 1 ^ 2) * (g 1 0 ^ 2 + g 1 1 ^ 2) -
          (g 0 0 * g 1 0 + g 0 1 * g 1 1) ^ 2 := by ring
    rw [this]
    have e1 : g 0 0 * g 1 0 + g 0 1 * g 1 1 = 0 := by linarith
    have e2 : g 1 0 ^ 2 + g 1 1 ^ 2 = g 0 0 ^ 2 + g 0 1 ^ 2 := by nlinarith
    rw [e1, e2]; ring
  have hDu : g 0 0 * g 1 1 - g 0 1 * g 1 0 = g 0 0 ^ 2 + g 0 1 ^ 2 := by
    rw [hD] at hd
    exact (sq_eq_sq₀ hd.le (by positivity)).1 hsq
  have e1 : g 0 0 * g 1 0 + g 0 1 * g 1 1 = 0 := by linarith
  have e2 : g 1 0 ^ 2 + g 1 1 ^ 2 = g 0 0 ^ 2 + g 0 1 ^ 2 := by nlinarith
  have hz : (g 1 1 - g 0 0) ^ 2 + (g 1 0 + g 0 1) ^ 2 = 0 := by
    linear_combination e2 - 2 * hDu
  have s1 := sq_nonneg (g 1 1 - g 0 0)
  have s2 := sq_nonneg (g 1 0 + g 0 1)
  have hz1 : (g 1 1 - g 0 0) ^ 2 = 0 := by linarith
  have hz2 : (g 1 0 + g 0 1) ^ 2 = 0 := by linarith
  have hz1' := pow_eq_zero_iff (two_ne_zero) |>.1 hz1
  have hz2' := pow_eq_zero_iff (two_ne_zero) |>.1 hz2
  exact ⟨by linarith, by linarith⟩

/-- An element normalizing `glPosParabolicInfty` has `c = 0`. -/
lemma c_eq_zero_of_mem_normalizer_parabolic (g : GL (Fin 2) ℝ)
    (hn : g ∈ Subgroup.normalizer (glPosParabolicInfty : Set (GL (Fin 2) ℝ))) : g 1 0 = 0 := by
  have hD := det_eq' g
  have hne : (g 1 1 - g 1 0) * g 0 0 - (g 0 0 - g 0 1) * (-g 1 0) ≠ 0 := by
    have := g.det.ne_zero
    intro h; apply this; rw [hD]; linarith
  set n : GL (Fin 2) ℝ := mk' (g 1 1 - g 1 0) (g 0 0 - g 0 1) (-g 1 0) (g 0 0) hne with hn_def
  have e00 : n 0 0 = g 1 1 - g 1 0 := by simp [hn_def]
  have e01 : n 0 1 = g 0 0 - g 0 1 := by simp [hn_def]
  have e10 : n 1 0 = -g 1 0 := by simp [hn_def]
  have e11 : n 1 1 = g 0 0 := by simp [hn_def]
  have h1 : n * g ∈ glPosParabolicInfty := by
    rw [mem_parabolicInfty_iff]
    refine ⟨?_, ?_⟩ <;> simp only [mul_apply', e00, e01, e10, e11] <;> ring
  have h2 := ((mem_normalizer_iff_mul _ g).1 hn n).1 h1
  rw [mem_parabolicInfty_iff] at h2
  obtain ⟨h2a, -⟩ := h2
  simp only [mul_apply', e00, e10] at h2a
  have : g 1 0 ^ 2 = 0 := by nlinarith
  exact pow_eq_zero_iff (two_ne_zero) |>.1 this

/-- An element with `c = 0` normalizes `glPosParabolicInfty`. -/
lemma mem_normalizer_parabolic_of_c_eq_zero (g : GL (Fin 2) ℝ) (hr : g 1 0 = 0) :
    g ∈ Subgroup.normalizer (glPosParabolicInfty : Set (GL (Fin 2) ℝ)) := by
  have hD := det_eq' g
  have hD0 := g.det.ne_zero
  rw [hD, hr] at hD0
  have hp : g 0 0 ≠ 0 := fun h => hD0 (by rw [h]; ring)
  have hs : g 1 1 ≠ 0 := fun h => hD0 (by rw [h]; ring)
  rw [mem_normalizer_iff_mul]
  intro n
  rw [mem_parabolicInfty_iff, mem_parabolicInfty_iff]
  simp only [mul_apply', hr]
  constructor
  · rintro ⟨h1, h2⟩
    have hc : n 1 0 = 0 := by
      have h1' : n 1 0 * g 0 0 = 0 := by linarith
      exact (mul_eq_zero.1 h1').resolve_right hp
    simp only [hc] at h2 ⊢
    refine ⟨by ring, by linarith⟩
  · rintro ⟨h1, h2⟩
    have hc : n 1 0 = 0 := by
      have h1' : g 1 1 * n 1 0 = 0 := by linarith
      exact (mul_eq_zero.1 h1').resolve_left hs
    simp only [hc] at h2 ⊢
    refine ⟨by ring, by linarith⟩

/-- An element of positive determinant normalizing `glPosStabInftyZero` is diagonal or
antidiagonal. -/
lemma diag_or_anti_of_mem_normalizer (g : GL (Fin 2) ℝ)
    (hn : g ∈ Subgroup.normalizer (glPosStabInftyZero : Set (GL (Fin 2) ℝ)))
    (hd : 0 < g.det.val) :
    (g 0 1 = 0 ∧ g 1 0 = 0) ∨ (g 0 0 = 0 ∧ g 1 1 = 0) := by
  have hD := det_eq' g
  have hne : (2 * g 1 1) * g 0 0 - (-2 * g 0 1) * (-g 1 0) ≠ 0 := by
    intro h; rw [hD] at hd; linarith
  set n : GL (Fin 2) ℝ := mk' (2 * g 1 1) (-2 * g 0 1) (-g 1 0) (g 0 0) hne with hn_def
  have hn_det : n.det.val = 2 * g.det.val := by
    rw [hn_def, mk'_det, hD]; ring
  have e00 : n 0 0 = 2 * g 1 1 := by simp [hn_def]
  have e01 : n 0 1 = -2 * g 0 1 := by simp [hn_def]
  have e10 : n 1 0 = -g 1 0 := by simp [hn_def]
  have e11 : n 1 1 = g 0 0 := by simp [hn_def]
  have h1 : n * g ∈ glPosStabInftyZero := by
    rw [mem_stabInftyZero_iff, det_mul', hn_det]
    refine ⟨by nlinarith, ?_, ?_⟩ <;> simp only [mul_apply', e00, e01, e10, e11] <;> ring
  have h2 := ((mem_normalizer_iff_mul _ g).1 hn n).1 h1
  rw [mem_stabInftyZero_iff] at h2
  obtain ⟨-, h2a, h2b⟩ := h2
  simp only [mul_apply', e00, e01, e10, e11] at h2a h2b
  have hrs : g 1 0 * g 1 1 = 0 := by linarith
  have hpq : g 0 0 * g 0 1 = 0 := by linarith
  rw [hD] at hd
  by_cases hp : g 0 0 = 0
  · right
    have hr : g 1 0 ≠ 0 := fun h => by rw [hp, h] at hd; simp at hd
    exact ⟨hp, (mul_eq_zero.1 hrs).resolve_left hr⟩
  · left
    have hq := (mul_eq_zero.1 hpq).resolve_left hp
    have hs : g 1 1 ≠ 0 := fun h => by rw [hq, h] at hd; simp at hd
    exact ⟨hq, (mul_eq_zero.1 hrs).resolve_right hs⟩

/-- **Miyake, Lemma 1.3.4**, first assertion, for $G = \mathrm{GL}_2^+(\mathbb R)_i$:
$[N(G) : N(G) \cap \mathrm{GL}_2^+(\mathbb R)] = 2$, with $N(G)$ the normalizer in $\mathrm{GL}_2(\mathbb R)$. -/
@[kb "miyake1989" "Lemma 1.3.4, p. 9"]
theorem relIndex_glPos_normalizer_stabI :
    (GLPos (Fin 2) ℝ).relIndex
      (Subgroup.normalizer (glPosStabI : Set (GL (Fin 2) ℝ))) = 2 :=
  relIndex_glPos_eq_two_of_neg_det _ sRefl sRefl_mem_normalizer_stabI
    (by rw [sRefl_det]; norm_num)

/-- **Miyake, Lemma 1.3.4 (1)** at $z = i$: $N(G) \cap \mathrm{GL}_2^+(\mathbb R) = G$ for
$G = \mathrm{GL}_2^+(\mathbb R)_i$. Miyake states it at any $z \in \mathbb H$ (conjugate); special case. -/
@[kb "miyake1989" "Lemma 1.3.4 (1), p. 9"]
theorem normalizer_stabI_inf_glPos :
    Subgroup.normalizer (glPosStabI : Set (GL (Fin 2) ℝ)) ⊓ GLPos (Fin 2) ℝ = glPosStabI := by
  ext g
  rw [Subgroup.mem_inf, mem_glPos_iff]
  constructor
  · rintro ⟨hn, hd⟩
    exact mem_stabI_of_mem_normalizer g hn hd
  · intro hg
    exact ⟨Subgroup.le_normalizer hg, ((mem_stabI_iff g).1 hg).1⟩

/-- **Miyake, Lemma 1.3.4**, first assertion, for $G = \mathrm{GL}_2^+(\mathbb R)^{(\infty)}$. -/
@[kb "miyake1989" "Lemma 1.3.4, p. 9"]
theorem relIndex_glPos_normalizer_parabolicInfty :
    (GLPos (Fin 2) ℝ).relIndex
      (Subgroup.normalizer (glPosParabolicInfty : Set (GL (Fin 2) ℝ))) = 2 :=
  relIndex_glPos_eq_two_of_neg_det _ sRefl sRefl_mem_normalizer_parabolic
    (by rw [sRefl_det]; norm_num)

/-- **Miyake, Lemma 1.3.4 (2)** at $x = \infty$: for $G = \mathrm{GL}_2^+(\mathbb R)^{(\infty)}$,
$N(G) \cap \mathrm{GL}_2^+(\mathbb R) = \mathrm{GL}_2^+(\mathbb R)_\infty$ (positive determinant, $c = 0$).
Special case of Miyake's statement at any $x \in \mathbb R \cup \{\infty\}$. -/
@[kb "miyake1989" "Lemma 1.3.4 (2), p. 9"]
theorem normalizer_parabolicInfty_inf_glPos :
    Subgroup.normalizer (glPosParabolicInfty : Set (GL (Fin 2) ℝ)) ⊓ GLPos (Fin 2) ℝ =
      GLPos (Fin 2) ℝ ⊓ MulAction.stabilizer (GL (Fin 2) ℝ) (∞ : OnePoint ℝ) := by
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_glPos_iff, MulAction.mem_stabilizer_iff,
    OnePoint.smul_infty_eq_self_iff]
  constructor
  · rintro ⟨hn, hd⟩
    exact ⟨hd, c_eq_zero_of_mem_normalizer_parabolic g hn⟩
  · rintro ⟨hd, hr⟩
    exact ⟨mem_normalizer_parabolic_of_c_eq_zero g hr, hd⟩

/-- **Miyake, Lemma 1.3.4**, first assertion, for $G = \mathrm{GL}_2^+(\mathbb R)_{\infty,0}$. -/
@[kb "miyake1989" "Lemma 1.3.4, p. 9"]
theorem relIndex_glPos_normalizer_stabInftyZero :
    (GLPos (Fin 2) ℝ).relIndex
      (Subgroup.normalizer (glPosStabInftyZero : Set (GL (Fin 2) ℝ))) = 2 :=
  relIndex_glPos_eq_two_of_neg_det _ sRefl sRefl_mem_normalizer_stabInftyZero
    (by rw [sRefl_det]; norm_num)

/-- **Miyake, Lemma 1.3.4 (3)** at $\{x, x'\} = \{\infty, 0\}$: for $G = \mathrm{GL}_2^+(\mathbb R)_{\infty,0}$,
$[N(G) \cap \mathrm{GL}_2^+(\mathbb R) : G] = 2$. Special case of Miyake's statement for any $x \ne x'$. -/
@[kb "miyake1989" "Lemma 1.3.4 (3), p. 9"]
theorem relIndex_stabInftyZero_normalizer_inf_glPos :
    glPosStabInftyZero.relIndex
      (Subgroup.normalizer (glPosStabInftyZero : Set (GL (Fin 2) ℝ)) ⊓ GLPos (Fin 2) ℝ) = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨wRot, Subgroup.mem_inf.2 ⟨wRot_mem_normalizer_stabInftyZero,
    (mem_glPos_iff _).2 (by rw [wRot_det]; norm_num)⟩⟩, fun b => ?_⟩
  obtain ⟨hbN, hbP⟩ := Subgroup.mem_inf.1 b.2
  have hd := (mem_glPos_iff _).1 hbP
  obtain ⟨a0, b0, c0, d0⟩ := wRot_entries
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  rw [mem_stabInftyZero_iff, mem_stabInftyZero_iff]
  simp only [det_mul', mul_apply', a0, b0, c0, d0, wRot_det]
  have hD := det_eq' (b : GL (Fin 2) ℝ)
  rcases diag_or_anti_of_mem_normalizer _ hbN hd with ⟨hq, hr⟩ | ⟨hp, hs⟩
  · have hs : (b : GL (Fin 2) ℝ) 1 1 ≠ 0 := fun h => by rw [hD, hq, h] at hd; simp at hd
    refine Or.inr ⟨⟨hd, hr, hq⟩, ?_⟩
    rintro ⟨-, h2, -⟩
    apply hs; linarith
  · have hr : (b : GL (Fin 2) ℝ) 1 0 ≠ 0 := fun h => by rw [hD, hp, h] at hd; simp at hd
    refine Or.inl ⟨⟨by linarith, by linarith, by linarith⟩, ?_⟩
    rintro ⟨-, h2, -⟩
    exact hr h2

end ModularFormsKB.Miyake
