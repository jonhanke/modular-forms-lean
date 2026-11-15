/-
# Shimura's $T(p^2)$ on functions: the explicit coset sum

For a prime $p \nmid 4N$ (so $p$ odd), the double coset
$\Gamma_0(4N)\,\xi\,\Gamma_0(4N)$ with $\xi = (\mathrm{diag}(1, p^2), p^{1/2})$ in the metaplectic cover has the $p^2 + p$ right
cosets of $\begin{pmatrix}1&b\\0&p^2\end{pmatrix}$ ($0 \le b < p^2$), $\begin{pmatrix}p&4i\\0&p\end{pmatrix}$ ($1 \le i < p$) and
$\begin{pmatrix}p^2&0\\0&1\end{pmatrix}$ (Shimura 1973 `shimura1973`, §1 [unverified]). Evaluated with the theta multiplier,
the coset action of $T(p^2)$ is
$$ (T(p^2)f)(\tau) = p^{-2}\Big(\sum_{b=0}^{p^2-1} f\big(\tfrac{\tau+b}{p^2}\big)
  + \chi(p)\big(\varepsilon_p^{-1}\sqrt p\big)^{2k+1}\sum_{i=0}^{p-1}\Big(\frac ip\Big) f\big(\tau + \tfrac{4i}{p}\big)
  + \chi(p)^2 p^{2k+1} f(p^2\tau)\Big) $$
(`heckeFun`; the multiplier computation is in `ModularFormsKB/HalfIntegral/HeckeMult.lean`). Its $q$-expansion is Shimura's
coefficient formula `heckeT` once the quadratic Gauss sum $G_p = \sum_{x=0}^{p-1}\big(\frac xp\big)e(x/p)$ (`gaussQ`) is known
to equal $\varepsilon_p\sqrt p$ (Gauss's sign; the named input `QuadGaussSumSign`, since Mathlib only has
$G_p^2 = \big(\frac{-1}{p}\big)p$).

The point $(A\tau + B)/D$ of $\mathbb H$ for positive integers $A, D$ is `affPt A D B τ`.
-/
import ModularFormsKB.HalfIntegral.Abstract.ThetaInstance
import ModularFormsKB.HalfIntegral.Abstract.Shimura

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- **The point $(A\tau + B)/D$ of $\mathbb H$**, for positive integers $A, D$ and an integer $B$. -/
noncomputable def affPt (A D : ℕ+) (B : ℤ) (τ : ℍ) : ℍ :=
  ⟨((A : ℂ) * τ + B) / D, by
    have h : (((A : ℂ) * τ + B) / D).im = (A : ℝ) * τ.im / D := by
      simp [Complex.div_im, Complex.normSq_ofReal]
      field_simp
    rw [h]
    have := τ.im_pos
    positivity⟩

@[simp] lemma coe_affPt (A D : ℕ+) (B : ℤ) (τ : ℍ) :
    (affPt A D B τ : ℂ) = ((A : ℂ) * τ + B) / D := rfl

lemma im_affPt (A D : ℕ+) (B : ℤ) (τ : ℍ) : (affPt A D B τ).im = (A : ℝ) * τ.im / D := by
  change (((A : ℂ) * τ + B) / D).im = _
  simp [Complex.div_im, Complex.normSq_ofReal]
  field_simp

/-- **The quadratic Gauss sum** $G_p = \sum_{x=0}^{p-1}\big(\frac xp\big)e^{2\pi i x/p}$. -/
noncomputable def gaussQ (p : ℕ) : ℂ :=
  ∑ x ∈ Finset.range p, (jacobiSym x p : ℂ) * cexp (2 * π * I * x / p)

/-- **Gauss's sign of the quadratic Gauss sum** (Lidl–Niederreiter `lidl1997`, Thm. 5.15 [unverified]; Gauss 1811): for an
odd prime $p$, $G_p = \sqrt p$ if $p \equiv 1 \bmod 4$ and $G_p = i\sqrt p$ if $p \equiv 3 \bmod 4$, that is
$G_p = \varepsilon_p\sqrt p$ with $\varepsilon_p$ = `epsD p`. Mathlib proves only $G_p^2 = \big(\frac{-1}{p}\big)p$. -/
@[kb "lidl1997" "Thm. 5.15: the quadratic Gauss sum over F_p is √p or i√p according as p ≡ 1 or 3 mod 4 [unverified]"]
structure QuadGaussSumSign : Prop where
  sign : ∀ p : ℕ, p.Prime → p ≠ 2 → gaussQ p = epsD p * (Real.sqrt p : ℂ)

/-- **Shimura's $T(p^2)$ on functions**, as the explicit coset sum (see the module docstring). Meant for $p \nmid 4N$ prime;
the $i = 0$ term has coefficient $\big(\frac 0p\big) = 0$. -/
noncomputable def heckeFun (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (p : ℕ+) (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  ((p : ℕ) : ℂ) ^ (-2 : ℤ) * ((∑ b ∈ Finset.range ((p : ℕ) ^ 2), f (affPt 1 (p ^ 2) b τ)) +
    χ (p : ℕ) * ((epsD (p : ℕ))⁻¹ * (Real.sqrt (p : ℕ) : ℂ)) ^ (2 * k + 1) *
      (∑ i ∈ Finset.range p, (jacobiSym i p : ℂ) * f (affPt p p (4 * i) τ)) +
    χ (p : ℕ) ^ 2 * ((p : ℕ) : ℂ) ^ (2 * k + 1) * f (affPt (p ^ 2) 1 0 τ))

/-- $f_\alpha(\tau) = f(\tau/p^2)$, the translate of $f$ by $\alpha = \mathrm{diag}(1, p^2)$. -/
noncomputable def fAlpha (p : ℕ+) (f : ℍ → ℂ) (τ : ℍ) : ℂ := f (affPt 1 (p ^ 2) 0 τ)

end ModularFormsKB.HalfIntegral
