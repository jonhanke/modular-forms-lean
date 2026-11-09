import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Calculus.Deriv.Inv
import ModularFormsKB.Citation
/-!
# Miyake §1.4: the invariant metric on $\mathbb H$

Miyake, *Modular Forms* (Springer 1989), §1.4, pp. 10–16. Here: Lemma 1.4.3 (1), the
transformation of the 1-form $y^{-1}\,dz$ under $\alpha \in \mathrm{SL}_2(\mathbb R)$.

## Conventions
* $z = x + iy \in \mathbb H$; $j(\alpha, z) = cz + d$ is Mathlib's `UpperHalfPlane.denom α z`, and
  $\alpha z = (az+b)/(cz+d)$ is `num α z / denom α z` (Mathlib's `UpperHalfPlane.num`).
* A 1-form $f\,dz$ with holomorphic-direction coefficient only is identified with its coefficient $f$.
  The pullback of $y^{-1}dz$ by $z \mapsto \alpha z$ is $\operatorname{Im}(\alpha z)^{-1}\,
  \tfrac{d(\alpha z)}{dz}\,dz$, and $d[\log j(\alpha, z)] = \tfrac{c}{cz+d}\,dz$ for every branch of the
  logarithm, so Miyake's identity (1) is an identity of $dz$-coefficients.
-/

open Complex UpperHalfPlane

namespace ModularFormsKB.Miyake

/-- **Miyake, Lemma 1.4.3 (1).** For $\alpha = \begin{pmatrix} a & b \\ c & d\end{pmatrix} \in
\mathrm{SL}_2(\mathbb R)$ and $z \in \mathbb H$,
$$(y^{-1}dz)\circ\alpha - y^{-1}dz = -2i\, d[\log j(\alpha, z)],$$
stated for the $dz$-coefficients:
$\operatorname{Im}(\alpha z)^{-1}\,\frac{d(\alpha z)}{dz} - \operatorname{Im}(z)^{-1} = -2i\,\frac{c}{cz+d}$.
Part (2) (the real part, with $d[\arg j(\alpha,z)]$) is not formalized. -/
@[kb "miyake1989" "Lemma 1.4.3 (1), p. 13"]
theorem pullback_inv_im_dz (g : GL (Fin 2) ℝ) (hg : g.det.val = 1) (z : ℍ) :
    ((g • z).im : ℂ)⁻¹ * deriv (fun w : ℂ ↦ num g w / denom g w) z - (z.im : ℂ)⁻¹ =
      -2 * Complex.I * (g 1 0 / denom g z) := by
  have hj : denom g z ≠ 0 := denom_ne_zero g z
  have hdet : (g 0 0 * g 1 1 - g 0 1 * g 1 0 : ℝ) = 1 := by
    have := hg
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at this
    exact this
  have hdetC : (g 0 0 : ℂ) * g 1 1 - g 0 1 * g 1 0 = 1 := by exact_mod_cast hdet
  have hd : HasDerivAt (fun w : ℂ ↦ num g w / denom g w)
      (((g 0 0 : ℂ) * denom g z - num g z * g 1 0) / denom g z ^ 2) z := by
    have h1 : HasDerivAt (fun w : ℂ ↦ num g w) (g 0 0 : ℂ) z := by
      unfold num
      have := ((hasDerivAt_id (z : ℂ)).const_mul (g 0 0 : ℂ)).add_const (g 0 1 : ℂ)
      rw [mul_one] at this
      exact this
    have h2 : HasDerivAt (fun w : ℂ ↦ denom g w) (g 1 0 : ℂ) z := by
      unfold denom
      have := ((hasDerivAt_id (z : ℂ)).const_mul (g 1 0 : ℂ)).add_const (g 1 1 : ℂ)
      rw [mul_one] at this
      exact this
    exact h1.div h2 hj
  rw [hd.deriv, UpperHalfPlane.im_smul_eq_div_normSq, hg]
  have hy : (z.im : ℂ) ≠ 0 := by exact_mod_cast z.im_ne_zero
  have hn : (Complex.normSq (denom g z) : ℂ) = (starRingEnd ℂ) (denom g z) * denom g z :=
    Complex.normSq_eq_conj_mul_self
  have hnum : (g 0 0 : ℂ) * denom g z - num g z * g 1 0 = 1 := by
    unfold num denom; linear_combination hdetC
  have hcj : (starRingEnd ℂ) (denom g z) - denom g z = -2 * Complex.I * (g 1 0 * z.im) := by
    unfold denom
    simp only [map_add, map_mul, Complex.conj_ofReal]
    have : (starRingEnd ℂ) (z : ℂ) = (z : ℂ) - 2 * Complex.I * z.im := by
      apply Complex.ext <;> simp; ring
    rw [this]; ring
  rw [hnum]
  simp only [abs_one, one_mul, Complex.ofReal_div]
  rw [hn]
  have hcj0 : (starRingEnd ℂ) (denom g z) = denom g z + -2 * Complex.I * (g 1 0 * z.im) := by
    rw [← hcj]; ring
  rw [hcj0]
  field_simp
  ring

end ModularFormsKB.Miyake
