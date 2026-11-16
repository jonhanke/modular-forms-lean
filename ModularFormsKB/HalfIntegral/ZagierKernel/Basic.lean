/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
-/
import ModularFormsKB.HalfIntegral.Abstract.ShintaniInvariance

/-!
# Zagier's kernel $f_{k,\Delta}$ and its genus-character twist

For $k \ge 2$ and $\Delta > 0$ a discriminant, Zagier 1975 `zagier1975` [unverified] defines
$$ f_{k,\Delta}(z) = \sum_{b^2 - 4ac = \Delta} \frac{1}{(az^2 + bz + c)^k}, $$
the sum over all integral binary quadratic forms $[a, b, c]$ of discriminant $\Delta$ (`zagierKernel`). Kohnen–Zagier
1981 `kohnenzagier1981` (§II [unverified]) twist it by the genus character: for $D$ a fundamental discriminant and
$\Delta = DD'$ with $D'$ a discriminant,
$$ f_{k,D,\Delta}(z) = \sum_{b^2 - 4ac = \Delta} \frac{\chi_D([a,b,c])}{(az^2 + bz + c)^k} $$
(`zagierKernelChi`; $\chi_D$ is `BinQF.genusChar`, `Abstract/Shintani.lean`). Both are values of `tsum` over
`BinQF.OfDisc Δ`.

**Proved here** (no convergence needed):
- `BinQF.evalC_ne_zero`: $Q(z, 1) \ne 0$ on $\mathbb H$ when $\operatorname{disc} Q > 0$ (the roots are real);
- `BinQF.normSq_evalC`: $|Q(z,1)|^2 = (a|z|^2 + bx + c)^2 + \Delta y^2$, the identity behind the convergence;
- `zagierKernel_smul`, `zagierKernelChi_smul`: $f(\gamma z) = (cz + d)^{2k} f(z)$ for $\gamma \in \mathrm{SL}_2(\mathbb Z)$, by
  reindexing the sum along $Q \mapsto Q \circ \gamma$ (a bijection of the forms of discriminant $\Delta$); the twisted
  kernel needs the named input `GenusCharacterWellDefined` for the class invariance of $\chi_D$.

**Named input** `ZagierKernelCuspForm` (Zagier 1975, §5, and Kohnen–Zagier 1981, §II [unverified]): the series
converges absolutely and $f_{k,D,\Delta}$ is a cusp form of weight $2k$ for $\mathrm{SL}_2(\mathbb Z)$. Loose end
LE-MF-0309 (absolute convergence for $k \ge 2$ needs the count of forms of discriminant $\Delta$ in a ball of the
majorant, which `normSq_evalC` sets up; holomorphy by local uniform convergence; cuspidality).

**Index shift.** Matrix entries are 0-based: $c = \gamma_{1,0}$, $d = \gamma_{1,1}$.
-/

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups ModularForm

local notation "ℍ" => UpperHalfPlane

namespace BinQF

private theorem normSq_evalC_aux (Q : BinQF) (z : ℂ) :
    Complex.normSq (Q.evalC z) =
      ((Q.a : ℝ) * Complex.normSq z + Q.b * z.re + Q.c) ^ 2 + (Q.disc : ℝ) * z.im ^ 2 := by
  simp only [Complex.normSq_apply, evalC, disc, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, pow_two, Complex.intCast_re, Complex.intCast_im]
  push_cast
  ring

/-- **$Q(z, 1) \ne 0$ on $\mathbb H$ for $\operatorname{disc} Q > 0$**: the roots of $Q(z, 1)$ are real (or $Q(z,1)$ is a
nonzero linear or constant polynomial with real coefficients). -/
theorem evalC_ne_zero (Q : BinQF) (hΔ : 0 < Q.disc) (z : ℍ) : Q.evalC (z : ℂ) ≠ 0 := by
  intro h
  have h1 := normSq_evalC_aux Q (z : ℂ)
  rw [h, map_zero] at h1
  have hy : (0 : ℝ) < ((z : ℂ)).im := z.im_pos
  have hd : (0 : ℝ) < (Q.disc : ℝ) := by exact_mod_cast hΔ
  have : 0 < (Q.disc : ℝ) * ((z : ℂ)).im ^ 2 := by positivity
  nlinarith [sq_nonneg ((Q.a : ℝ) * Complex.normSq (z : ℂ) + Q.b * ((z : ℂ)).re + Q.c)]

/-- **The norm identity** $|Q(z,1)|^2 = (a|z|^2 + b\operatorname{Re}z + c)^2 + \operatorname{disc}(Q)(\operatorname{Im}z)^2$. -/
theorem normSq_evalC (Q : BinQF) (z : ℂ) :
    Complex.normSq (Q.evalC z) =
      ((Q.a : ℝ) * Complex.normSq z + Q.b * z.re + Q.c) ^ 2 + (Q.disc : ℝ) * z.im ^ 2 :=
  normSq_evalC_aux Q z

/-- The forms of discriminant $\Delta$ are permuted by $Q \mapsto Q \circ \gamma$, $\gamma \in \mathrm{SL}_2(\mathbb Z)$. -/
def compEquiv (Δ : ℤ) (γ : SL(2, ℤ)) : OfDisc Δ ≃ OfDisc Δ where
  toFun Q := ⟨Q.1.comp γ, by rw [disc_comp_SL]; exact Q.2⟩
  invFun Q := ⟨Q.1.comp (γ⁻¹ : SL(2, ℤ)), by rw [disc_comp_SL]; exact Q.2⟩
  left_inv Q := by
    apply Subtype.ext
    show (Q.1.comp (γ : Matrix (Fin 2) (Fin 2) ℤ)).comp ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = Q.1
    rw [← comp_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
      comp_one]
  right_inv Q := by
    apply Subtype.ext
    show (Q.1.comp ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).comp (γ : Matrix (Fin 2) (Fin 2) ℤ) = Q.1
    rw [← comp_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
      comp_one]

end BinQF

/-- **Zagier's kernel** $f_{k,\Delta}(z) = \sum_{b^2-4ac=\Delta}(az^2+bz+c)^{-k}$ (Zagier 1975 `zagier1975` [unverified]),
as the value of `tsum`. -/
noncomputable def zagierKernel (k : ℕ) (Δ : ℤ) (z : ℍ) : ℂ :=
  ∑' Q : BinQF.OfDisc Δ, (Q.1.evalC (z : ℂ) ^ k)⁻¹

/-- **The twisted kernel** $f_{k,D,\Delta}(z) = \sum_{b^2-4ac=\Delta}\chi_D([a,b,c])\,(az^2+bz+c)^{-k}$
(Kohnen–Zagier 1981 `kohnenzagier1981`, §II [unverified]), as the value of `tsum`. -/
noncomputable def zagierKernelChi (k : ℕ) (D Δ : ℤ) (z : ℍ) : ℂ :=
  ∑' Q : BinQF.OfDisc Δ, (BinQF.genusChar D Q.1 : ℂ) * (Q.1.evalC (z : ℂ) ^ k)⁻¹

/-- **Modularity of Zagier's kernel, formally**: $f_{k,\Delta}(\gamma z) = (cz+d)^{2k} f_{k,\Delta}(z)$ for
$\gamma \in \mathrm{SL}_2(\mathbb Z)$, by reindexing the sum (no convergence is used: both sides are values of
`tsum`, and reindexing along a bijection and multiplying by a constant commute with `tsum`). -/
theorem zagierKernel_smul (k : ℕ) {Δ : ℤ} (γ : SL(2, ℤ)) (z : ℍ) :
    zagierKernel k Δ (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ (2 * k) * zagierKernel k Δ z := by
  have hd := BinQF.denom_ne_zero_SL γ z
  unfold zagierKernel
  rw [← tsum_mul_left]
  refine Eq.trans (tsum_congr fun Q => ?_)
    ((BinQF.compEquiv Δ γ).tsum_eq
      (fun Q : BinQF.OfDisc Δ => ((γ 1 0 : ℂ) * z + γ 1 1) ^ (2 * k) * (Q.1.evalC (z : ℂ) ^ k)⁻¹))
  show _ = ((γ 1 0 : ℂ) * z + γ 1 1) ^ (2 * k) * ((Q.1.comp (γ : Matrix (Fin 2) (Fin 2) ℤ)).evalC (z : ℂ) ^ k)⁻¹
  rw [BinQF.coe_smul_SL, BinQF.evalC_smul Q.1 (γ : Matrix (Fin 2) (Fin 2) ℤ) hd, div_pow, ← pow_mul, inv_div,
    div_eq_mul_inv, mul_comm]

/-- **Modularity of the twisted kernel, formally** (as `zagierKernel_smul`), for $D$ fundamental and $\Delta = DD'$ with
$D' \equiv 0, 1 \bmod 4$, given the class invariance of the genus character (`GenusCharacterWellDefined`). -/
theorem zagierKernelChi_smul (k : ℕ) {D D' Δ : ℤ} (hW : GenusCharacterWellDefined D)
    (hD : IsFundamentalDiscriminant D) (hΔ : Δ = D * D') (hD' : D' % 4 = 0 ∨ D' % 4 = 1)
    (γ : SL(2, ℤ)) (z : ℍ) :
    zagierKernelChi k D Δ (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ (2 * k) * zagierKernelChi k D Δ z := by
  have hd := BinQF.denom_ne_zero_SL γ z
  unfold zagierKernelChi
  rw [← tsum_mul_left]
  refine Eq.trans (tsum_congr fun Q => ?_)
    ((BinQF.compEquiv Δ γ).tsum_eq
      (fun Q : BinQF.OfDisc Δ => ((γ 1 0 : ℂ) * z + γ 1 1) ^ (2 * k) *
        ((BinQF.genusChar D Q.1 : ℂ) * (Q.1.evalC (z : ℂ) ^ k)⁻¹)))
  have hQ : Q.1.disc = D * D' := by rw [Q.2, hΔ]
  have hg := BinQF.genusChar_comp hW hD hQ hD' γ
  show _ = ((γ 1 0 : ℂ) * z + γ 1 1) ^ (2 * k) *
    ((BinQF.genusChar D (Q.1.comp (γ : Matrix (Fin 2) (Fin 2) ℤ)) : ℂ) *
      ((Q.1.comp (γ : Matrix (Fin 2) (Fin 2) ℤ)).evalC (z : ℂ) ^ k)⁻¹)
  rw [hg, BinQF.coe_smul_SL, BinQF.evalC_smul Q.1 (γ : Matrix (Fin 2) (Fin 2) ℤ) hd, div_pow, ← pow_mul, inv_div,
    div_eq_mul_inv]
  ring

/-- **Zagier's kernel is an absolutely convergent cusp form** (Zagier 1975 `zagier1975`, §5; Kohnen–Zagier 1981
`kohnenzagier1981`, §II [unverified]): for $k \ge 2$, $D$ a fundamental discriminant and $\Delta = DD' > 0$ with $D'$ a
discriminant, the series of `zagierKernelChi` converges absolutely at every point of $\mathbb H$, and its sum is a cusp
form of weight $2k$ for $\mathrm{SL}_2(\mathbb Z)$. Loose end LE-MF-0309. -/
@[kb "zagier1975" "§5 and Kohnen–Zagier 1981 §II: f_{k,D,Δ} converges absolutely and lies in S_{2k}(SL₂(ℤ)) for k ≥ 2 [unverified]"]
structure ZagierKernelCuspForm (k : ℕ) : Prop where
  summable : 2 ≤ k → ∀ D D' : ℤ, IsFundamentalDiscriminant D → (D' % 4 = 0 ∨ D' % 4 = 1) → 0 < D * D' →
    ∀ z : ℍ, Summable fun Q : BinQF.OfDisc (D * D') ↦ ‖(BinQF.genusChar D Q.1 : ℂ) * (Q.1.evalC (z : ℂ) ^ k)⁻¹‖
  cuspForm : 2 ≤ k → ∀ D D' : ℤ, IsFundamentalDiscriminant D → (D' % 4 = 0 ∨ D' % 4 = 1) → 0 < D * D' →
    ∃ F : CuspForm 𝒮ℒ (2 * k : ℕ), ⇑F = zagierKernelChi k D (D * D')

end ModularFormsKB.HalfIntegral
