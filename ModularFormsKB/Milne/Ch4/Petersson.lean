import TauCeti.NumberTheory.ModularForms.Petersson.FiniteIndex
import ModularFormsKB.Citation
/-!
# Milne, Chapter 4: the Petersson inner product

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 4, pdf pp. 62–64.

Milne's $\langle f, g\rangle = \iint_D f(z)\overline{g(z)}\,y^{2k-2}\,dx\,dy$, $D$ a fundamental domain for $\Gamma$, is
linear in $f$. Writing $\mathrm{SL}_2(\mathbb Z) = \bigsqcup_q (\pm\Gamma)\,q$, the domain $D$ is
$\bigcup_q q^{-1}\mathcal F$ with $\mathcal F$ the standard fundamental domain of $\Gamma(1)$, and
$y^{2k-2}dx\,dy = y^{2k}\,d\mu$ with $d\mu = dx\,dy/y^2$ the invariant measure (Mathlib's `volume` on $\mathbb H$). So
$\langle f, g\rangle = \sum_q\int_{\mathcal F}(f|_{2k}q^{-1})\overline{(g|_{2k}q^{-1})}\,y^{2k}\,d\mu$ (`milnePetersson`).
Tau Ceti's `CuspForm.peterssonInnerCosets` is the same sum with the conjugate on the first argument
(`milnePetersson_eq_peterssonInnerCosets`).

## Items
- Lemma 4.30 (`petersson_smul_invariant`; the measure $dx\,dy/y^2$ is invariant by Mathlib's
  `UpperHalfPlane.instSMulInvariantMeasure…`, see `volume_smul_invariant`).
- Lemma 4.32 (`integrableOn_milnePetersson`).
- The Petersson inner product, p. 64 (`milnePetersson`), its properties: linear in the first variable
  (`milnePetersson_add_left`, `milnePetersson_smul_left`), Hermitian (`milnePetersson_conj_symm`), positive definite on
  $S_k(\Gamma)$ (`milnePetersson_self_pos`).
-/

open UpperHalfPlane Complex MeasureTheory ModularForm ModularGroup
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ComplexConjugate

noncomputable section

namespace ModularFormsKB.Milne

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- **The Petersson inner product** (p. 64), Milne's normalization (linear in the first variable), for modular forms
$f, g$ of weight $2k$ for $\Gamma$ (defined for all functions; it converges when one of $f$, $g$ is a cusp form,
Lemma 4.32). -/
@[kb "milne2017mf" "Section 4, the Petersson inner product (pdf p. 64)"]
def milnePetersson (k : ℤ) (f g : ℍ → ℂ) : ℂ :=
  ∑ q : SL(2, ℤ) ⧸ Γ.withCenter, peterssonInner (2 * k) fd (g ∣[2 * k] (q.out)⁻¹) (f ∣[2 * k] (q.out)⁻¹)

/-- Comparison with Tau Ceti: on cusp forms, Milne's product is `CuspForm.peterssonInnerCosets` with the arguments
swapped. -/
theorem milnePetersson_eq_peterssonInnerCosets (k : ℤ) (f g : CuspForm (Γ.map (mapGL ℝ)) (2 * k)) :
    milnePetersson Γ k f g = CuspForm.peterssonInnerCosets g f := rfl

omit [Γ.FiniteIndex] in
/-- **Lemma 4.30**: for modular forms $f, g$ of weight $2k$ for $\Gamma$, the function $f\bar g\,y^{2k}$ is invariant
under $\Gamma$; with the invariance of $dx\,dy/y^2$ (`volume_smul_invariant`) this is the invariance of the
differential $f(z)\overline{g(z)}y^{2k-2}dx\,dy$. (Mathlib's `SlashInvariantFormClass.petersson_smul`.) -/
@[kb "milne2017mf" "Section 4, Lemma 4.30 (pdf p. 63)"]
theorem petersson_smul_invariant (k : ℤ) (f g : ModularForm (Γ.map (mapGL ℝ)) (2 * k)) (γ : Γ) (τ : ℍ) :
    petersson (2 * k) g f ((γ : SL(2, ℤ)) • τ) = petersson (2 * k) g f τ :=
  UpperHalfPlane.petersson_smul_of_mem (2 * k) g f γ.2 τ

/-- **Lemma 4.30**, the measure: $dx\,dy/y^2$ is invariant under $\mathrm{SL}_2(\mathbb R)$ (here under
$\mathrm{GL}_2(\mathbb R)$, Mathlib). -/
@[kb "milne2017mf" "Section 4, invariance of dx dy / y^2 (pdf p. 62); Lemma 4.30 (pdf p. 63)"]
theorem volume_smul_invariant (g : GL (Fin 2) ℝ) (s : Set ℍ) :
    volume ((fun τ : ℍ ↦ g • τ) ⁻¹' s) = volume s :=
  MeasureTheory.measure_preimage_smul volume g s

/-- **Lemma 4.32**: if $f$ is a cusp form and $g$ a modular form of weight $2k$ for $\Gamma$, the integrand of
$\langle f, g\rangle$ is integrable on each translate of the fundamental domain, so the integral over $D$ converges;
likewise with the roles of $f$ and $g$ exchanged. -/
@[kb "milne2017mf" "Section 4, Lemma 4.32 (pdf p. 63)"]
theorem integrableOn_milnePetersson (k : ℤ) (f : CuspForm (Γ.map (mapGL ℝ)) (2 * k))
    (g : ModularForm (Γ.map (mapGL ℝ)) (2 * k)) (δ : SL(2, ℤ)) :
    IntegrableOn (fun τ ↦ petersson (2 * k) (⇑g ∣[2 * k] δ) (⇑f ∣[2 * k] δ) τ) fd ∧
      IntegrableOn (fun τ ↦ petersson (2 * k) (⇑f ∣[2 * k] δ) (⇑g ∣[2 * k] δ) τ) fd :=
  ⟨integrableOn_petersson_slash_right (2 * k) _ g f δ, integrableOn_petersson_slash_left (2 * k) _ f g δ⟩

/-- The Petersson product is linear in the first variable (p. 64): additivity, for cusp forms. -/
@[kb "milne2017mf" "Section 4, properties of the Petersson inner product (pdf p. 64)"]
theorem milnePetersson_add_left (k : ℤ) (f₁ f₂ g : CuspForm (Γ.map (mapGL ℝ)) (2 * k)) :
    milnePetersson Γ k ⇑(f₁ + f₂) g = milnePetersson Γ k f₁ g + milnePetersson Γ k f₂ g := by
  have h := fun a b => milnePetersson_eq_peterssonInnerCosets Γ k a b
  rw [h, h, h]
  exact CuspForm.peterssonInnerCosets_add_right _ _ _

/-- The Petersson product is linear in the first variable (p. 64): scalars. -/
@[kb "milne2017mf" "Section 4, properties of the Petersson inner product (pdf p. 64)"]
theorem milnePetersson_smul_left (k : ℤ) (c : ℂ) (f g : ℍ → ℂ) :
    milnePetersson Γ k (c • f) g = c * milnePetersson Γ k f g := by
  simp only [milnePetersson, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [ModularForm.SL_smul_slash]
  exact UpperHalfPlane.peterssonInner_smul_right _ _ c _ _

/-- $\langle f, g\rangle = \overline{\langle g, f\rangle}$ (p. 64). -/
@[kb "milne2017mf" "Section 4, properties of the Petersson inner product (pdf p. 64)"]
theorem milnePetersson_conj_symm (k : ℤ) (f g : ℍ → ℂ) :
    milnePetersson Γ k f g = conj (milnePetersson Γ k g f) := by
  simp only [milnePetersson, map_sum, UpperHalfPlane.peterssonInner_conj_symm]

/-- $\langle f, f\rangle > 0$ for every nonzero cusp form $f$ (p. 64): positive definite on $S_k(\Gamma)$. -/
@[kb "milne2017mf" "Section 4, properties of the Petersson inner product (pdf p. 64)"]
theorem milnePetersson_self_pos (k : ℤ) (f : CuspForm (Γ.map (mapGL ℝ)) (2 * k)) (hf : f ≠ 0) :
    (milnePetersson Γ k f f).im = 0 ∧ 0 < (milnePetersson Γ k f f).re := by
  rw [milnePetersson_eq_peterssonInnerCosets]
  refine ⟨CuspForm.peterssonInnerCosets_self_im f, ?_⟩
  refine lt_of_le_of_ne (CuspForm.peterssonInnerCosets_self_re_nonneg f) fun h0 => hf ?_
  rw [← CuspForm.peterssonInnerCosets_self_eq_zero]
  apply Complex.ext
  · simp [← h0]
  · simp

end ModularFormsKB.Milne
