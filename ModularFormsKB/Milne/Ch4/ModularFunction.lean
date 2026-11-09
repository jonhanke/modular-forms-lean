import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Sphere
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Meromorphic
import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
import TauCeti.Analysis.Complex.UpperHalfPlane.Meromorphic
import ModularFormsKB.Milne.Ch4.LevelOne
import ModularFormsKB.Citation
/-!
# Milne, Chapter 4: modular functions and meromorphic modular forms

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 4, pdf pp. 48–49.

Milne's $\Gamma$ is a subgroup of finite index of $\Gamma(1) = \mathrm{SL}_2(\mathbb Z)$. A **meromorphic modular form of
weight $2k$** for $\Gamma$ (p. 49) is a function $f$ on $\mathbb H$ with (a) $f(\gamma z) = (cz+d)^{2k}f(z)$ for
$\gamma \in \Gamma$, (b) $f$ meromorphic on $\mathbb H$, (c) $f$ meromorphic at the cusps; a **modular function** is a
meromorphic modular form of weight $0$ (p. 48). Condition (c) at the cusp $\gamma(i\infty)$, $\gamma \in \Gamma(1)$:
$f|_{2k}\gamma$ is invariant under $z \mapsto z + h$, $h$ the width of the cusp (Mathlib's `Subgroup.widthInfty` of
$\gamma^{-1}\Gamma\gamma$), so $f|_{2k}\gamma(z) = f^*(q)$, $q = e^{2\pi i z/h}$, and $f^*$ must be meromorphic at
$q = 0$; here $f^*$ is Mathlib's `Function.Periodic.cuspFunction h`. The order of $f$ at that cusp is the order of
$f^*$ at $0$ (`cuspOrder`).

## Items
- Definition of modular function, p. 48 (`IsModularFunction`), and of meromorphic modular form, p. 49
  (`IsMeromorphicModularForm`); width of a cusp (`cuspWidth`).
- Example 4.1 (`isModularFunction_one_iff_generators`, `IsModularFunction.laurent_expansion`).
- Proposition 4.3 (`existsUnique_J`).
- Remark 4.4 (`jFun_isModularFunction`, `jFun_holomorphic`, `cuspOrder_jFun`, `jFun_bijective`,
  `jFun_eq_smul_J`, `exists_jFun_biholomorph`).
- Definition 4.5 (modular form, cusp form, "weakly modular") is Mathlib's `ModularForm`, `CuspForm`,
  `SlashInvariantForm` at weight `2 * k`; the spaces $M_k(\Gamma)$, $S_k(\Gamma)$ and the graded ring
  $M(\Gamma) = \bigoplus_k M_k(\Gamma)$ (p. 51) are `ModularForm Γ (2 * k)`, `CuspForm Γ (2 * k)` and Mathlib's
  `ModularForm.instGCommRing`; the divisor sums $\sigma_k(n)$ (p. 56) are Mathlib's `ArithmeticFunction.sigma`.
- Remark 4.17 is a pointer: "We have verified all the assertions in (4.3)", i.e. Proposition 4.3 and Remark 4.4.
-/

open UpperHalfPlane Complex Filter Topology ModularForm Function
open scoped MatrixGroups Manifold Real ContDiff

noncomputable section

namespace ModularFormsKB.Milne

/-- The conjugate $\gamma^{-1}\Gamma\gamma$ of a subgroup of $\mathrm{SL}_2(\mathbb Z)$. -/
def conjSubgroup (Γ : Subgroup SL(2, ℤ)) (γ : SL(2, ℤ)) : Subgroup SL(2, ℤ) :=
  Γ.map (MulAut.conj γ⁻¹).toMonoidHom

/-- **The width of the cusp $\gamma(i\infty)$** for $\Gamma$ (p. 48): the least $h > 0$ with
$\pm\begin{pmatrix}1&h\\0&1\end{pmatrix} \in \gamma^{-1}\Gamma\gamma$ (Mathlib's `widthInfty`). -/
@[kb "milne2017mf" "Section 4, the width of a cusp (pdf p. 48)"]
def cuspWidth (Γ : Subgroup SL(2, ℤ)) (γ : SL(2, ℤ)) : ℝ :=
  ((conjSubgroup Γ γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).widthInfty

/-- **Meromorphic modular form of weight $2k$** for $\Gamma$ (p. 49): conditions 4.5(a,b,c) with "holomorphic"
replaced by "meromorphic". -/
@[kb "milne2017mf" "Section 4, meromorphic modular form, after Definition 4.5 (pdf p. 49)"]
structure IsMeromorphicModularForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ) : Prop where
  /-- (a) $f(\gamma z) = (cz+d)^{2k}f(z)$ for $\gamma \in \Gamma$. -/
  slash : ∀ γ ∈ Γ, f ∣[2 * k] γ = f
  /-- (b) $f$ is meromorphic on $\mathbb H$. -/
  meromorphic : ∀ z : ℍ, MeromorphicAt (f ∘ ofComplex) (z : ℂ)
  /-- (c) $f$ is meromorphic at every cusp $\gamma(i\infty)$. -/
  meromorphic_cusp : ∀ γ : SL(2, ℤ), MeromorphicAt (Periodic.cuspFunction (cuspWidth Γ γ) ((f ∣[2 * k] γ) ∘ ofComplex)) 0

/-- **Modular function** for $\Gamma$ (p. 48): (a) $f(\gamma z) = f(z)$ for $\gamma \in \Gamma$, (b) $f$ meromorphic on
$\mathbb H$, (c) $f$ meromorphic at the cusps. -/
@[kb "milne2017mf" "Section 4, modular function (pdf p. 48)"]
def IsModularFunction (Γ : Subgroup SL(2, ℤ)) (f : ℍ → ℂ) : Prop := IsMeromorphicModularForm Γ 0 f

/-- **The order of $f$ at the cusp $\gamma(i\infty)$**: the order at $q = 0$ of $f^*(q) = (f|_{2k}\gamma)(z)$,
$q = e^{2\pi i z/h}$. -/
@[kb "milne2017mf" "Section 4, order at a cusp, proof of Lemma 4.11 (pdf p. 52)"]
def cuspOrder (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) : WithTop ℤ :=
  meromorphicOrderAt (Periodic.cuspFunction (cuspWidth Γ γ) ((f ∣[2 * k] γ) ∘ ofComplex)) 0

/-- Helper: the conjugate of the full group is the full group. -/
theorem conjSubgroup_top (γ : SL(2, ℤ)) : conjSubgroup ⊤ γ = ⊤ := by
  unfold conjSubgroup
  exact Subgroup.map_top_of_surjective _ (MulAut.conj γ⁻¹).surjective

/-- Helper: every cusp of $\Gamma(1)$ has width $1$. -/
theorem cuspWidth_top (γ : SL(2, ℤ)) : cuspWidth ⊤ γ = 1 := by
  unfold cuspWidth
  rw [conjSubgroup_top]
  unfold Subgroup.widthInfty
  have h : ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).adjoinNegOne =
      ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
    rw [Subgroup.adjoinNegOne_eq_self_iff]
    refine ⟨-1, Subgroup.mem_top _, ?_⟩
    ext i j
    simp
  rw [h]
  exact Subgroup.strictWidthInfty_eq_one_of_T_mem (Subgroup.mem_top _)

/-- Helper: a modular function is invariant under the group. -/
theorem IsModularFunction.invariant {Γ : Subgroup SL(2, ℤ)} {f : ℍ → ℂ} (hf : IsModularFunction Γ f) :
    ∀ γ ∈ Γ, ∀ z : ℍ, f (γ • z) = f z := by
  intro γ hγ z
  have hf' : IsMeromorphicModularForm Γ 0 f := hf
  have h := congrFun (hf'.slash γ hγ) z
  rw [SL_slash_apply] at h
  simpa using h


/-- Helper: `mapGL` of an integral matrix is `±` a translation iff its projective image is that translation. -/
theorem mapGL_eq_pm_upperRightHom_iff (h : SL(2, ℤ)) (x : ℝ) :
    (Matrix.SpecialLinearGroup.mapGL ℝ h = Matrix.GeneralLinearGroup.upperRightHom x ∨
      Matrix.SpecialLinearGroup.mapGL ℝ h = -Matrix.GeneralLinearGroup.upperRightHom x) ↔
    sl2zToPSL2R h = Matrix.ProjectiveSpecialLinearGroup.upperRightHom x := by
  have e1 : ((Matrix.SpecialLinearGroup.transvection (zero_ne_one' (Fin 2)) x :
      SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, x; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.transvection_coe]
  rw [sl2zToPSL2R_apply, Matrix.ProjectiveSpecialLinearGroup.upperRightHom_apply,
    Matrix.ProjectiveSpecialLinearGroup.mk_eq_mk_iff]
  simp only [Units.ext_iff, Matrix.SpecialLinearGroup.ext_iff, Matrix.SpecialLinearGroup.coe_neg, e1,
    Matrix.SpecialLinearGroup.map_apply_coe]
  simp only [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Fin.forall_fin_two]
  simp [← Matrix.ext_iff, Fin.forall_fin_two]
  constructor <;> rintro (⟨⟨h1, h2⟩, h3, h4⟩ | ⟨⟨h1, h2⟩, h3, h4⟩) <;> simp_all <;>
    first | done | (left; exact ⟨by exact_mod_cast h4.symm, by exact_mod_cast h3.symm, by exact_mod_cast h4.symm⟩)

/-- Helper: membership in the `GL(2, ℝ)`-image of a subgroup of `SL(2, ℤ)`. -/
theorem mem_coe_GL_iff (C : Subgroup SL(2, ℤ)) (g : GL (Fin 2) ℝ) :
    g ∈ (C : Subgroup (GL (Fin 2) ℝ)) ↔ ∃ h ∈ C, Matrix.SpecialLinearGroup.mapGL ℝ h = g :=
  Subgroup.mem_map

/-- Helper: the periods of the conjugate group, read in `PSL(2, ℝ)`. -/
theorem mem_periods_conj_iff (Γ : Subgroup SL(2, ℤ)) (γ : SL(2, ℤ)) (x : ℝ) :
    x ∈ ((conjSubgroup Γ γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).adjoinNegOne.strictPeriods ↔
      sl2zToPSL2R γ * Matrix.ProjectiveSpecialLinearGroup.upperRightHom x * (sl2zToPSL2R γ)⁻¹ ∈
        Γ.map sl2zToPSL2R := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_adjoinNegOne_iff, mem_coe_GL_iff, mem_coe_GL_iff]
  have step : ((∃ h ∈ conjSubgroup Γ γ, Matrix.SpecialLinearGroup.mapGL ℝ h =
      Matrix.GeneralLinearGroup.upperRightHom x) ∨
      (∃ h ∈ conjSubgroup Γ γ, Matrix.SpecialLinearGroup.mapGL ℝ h =
      -Matrix.GeneralLinearGroup.upperRightHom x)) ↔
      ∃ h ∈ conjSubgroup Γ γ, sl2zToPSL2R h = Matrix.ProjectiveSpecialLinearGroup.upperRightHom x := by
    constructor
    · rintro (⟨h, hh, e⟩ | ⟨h, hh, e⟩)
      · exact ⟨h, hh, (mapGL_eq_pm_upperRightHom_iff h x).1 (Or.inl e)⟩
      · exact ⟨h, hh, (mapGL_eq_pm_upperRightHom_iff h x).1 (Or.inr e)⟩
    · rintro ⟨h, hh, e⟩
      rcases (mapGL_eq_pm_upperRightHom_iff h x).2 e with e | e
      · exact Or.inl ⟨h, hh, e⟩
      · exact Or.inr ⟨h, hh, by rw [e]⟩
  have hneg : ∀ h : SL(2, ℤ), (-Matrix.SpecialLinearGroup.mapGL ℝ h = Matrix.GeneralLinearGroup.upperRightHom x) ↔
      Matrix.SpecialLinearGroup.mapGL ℝ h = -Matrix.GeneralLinearGroup.upperRightHom x := by
    intro h
    rw [neg_eq_iff_eq_neg]
  rw [step]
  unfold conjSubgroup
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨h, ⟨g, hg, rfl⟩, e⟩
    refine ⟨g, hg, ?_⟩
    have hc : (MulAut.conj γ⁻¹).toMonoidHom g = γ⁻¹ * g * γ := by simp
    rw [hc, map_mul, map_mul, map_inv] at e
    rw [← e]
    group
  · rintro ⟨g, hg, e⟩
    refine ⟨γ⁻¹ * g * γ, ⟨g, hg, by simp⟩, ?_⟩
    rw [map_mul, map_mul, map_inv, e]
    group

/-- Helper: the width of a cusp datum at `γ • ∞` with scaling `γ⁻¹` is Mathlib's `cuspWidth`. -/
theorem cuspDatum_width_eq (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (γ : SL(2, ℤ))
    (D : (Γ.map sl2zToPSL2R).CuspDatum) (hc : D.cusp = sl2zToPSL2R γ • (OnePoint.infty : OnePoint ℝ))
    (hs : D.scaling = (sl2zToPSL2R γ)⁻¹) : D.width = cuspWidth Γ γ := by
  set P := sl2zToPSL2R γ with hP
  have hgen : P⁻¹ * (D.generator : PSL(2, ℝ)) * P = Matrix.ProjectiveSpecialLinearGroup.upperRightHom D.width := by
    have := D.scaling_mul_generator_mul_inv
    rwa [hs, inv_inv] at this
  have hper : ((conjSubgroup Γ γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).adjoinNegOne.strictPeriods =
      AddSubgroup.zmultiples D.width := by
    ext x
    rw [mem_periods_conj_iff, AddSubgroup.mem_zmultiples_iff]
    constructor
    · intro hx
      have hmem : (⟨P * Matrix.ProjectiveSpecialLinearGroup.upperRightHom x * P⁻¹, hx⟩ :
          Γ.map sl2zToPSL2R) ∈ MulAction.stabilizer (Γ.map sl2zToPSL2R) D.cusp := by
        rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
        show (P * Matrix.ProjectiveSpecialLinearGroup.upperRightHom x * P⁻¹) • D.cusp = D.cusp
        rw [hc, mul_smul, mul_smul, inv_smul_smul,
          Matrix.ProjectiveSpecialLinearGroup.upperRightHom_smul_infty]
      obtain ⟨n, hn⟩ := D.mem_stabilizer_iff_conj.1 hmem
      rw [hs] at hn
      have h2 : Matrix.ProjectiveSpecialLinearGroup.upperRightHom x =
          Matrix.ProjectiveSpecialLinearGroup.upperRightHom (n * D.width) := by
        rw [← hn]
        simp only [inv_inv]
        group
      exact ⟨n, by rw [zsmul_eq_mul]; exact (Matrix.ProjectiveSpecialLinearGroup.upperRightHom_injective h2).symm⟩
    · rintro ⟨n, rfl⟩
      rw [zsmul_eq_mul]
      have h1 := Matrix.ProjectiveSpecialLinearGroup.mul_zpow_mul_inv_eq_upperRightHom
        (σ := P⁻¹) (γ := (D.generator : PSL(2, ℝ))) (w := D.width) (by
          simpa only [inv_inv] using hgen) n
      have h2 : P * Matrix.ProjectiveSpecialLinearGroup.upperRightHom (n * D.width) * P⁻¹ =
          (D.generator : PSL(2, ℝ)) ^ n := by
        rw [← h1]
        group
      rw [h2]
      exact (D.generator ^ n).2
  have hdisc : DiscreteTopology
      ((conjSubgroup Γ γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).adjoinNegOne.strictPeriods := by
    rw [hper]
    infer_instance
  rw [Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty, eq_comm,
    AddSubgroup.zmultiples_eq_zmultiples_iff
      (not_isOfFinAddOrder_of_isAddTorsionFree D.width_pos.ne')] at hper
  have := D.width_pos
  have h0 := Subgroup.strictWidthInfty_nonneg
    ((conjSubgroup Γ γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).adjoinNegOne
  unfold cuspWidth Subgroup.widthInfty
  grind

/-- Helper: a cusp datum of the image of $\Gamma$ at $\gamma\cdot\infty$ with scaling $\gamma^{-1}$ exists, with
width `cuspWidth Γ γ`. -/
theorem exists_cuspDatum_of_sl2z (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (γ : SL(2, ℤ)) :
    ∃ D : (Γ.map sl2zToPSL2R).CuspDatum, D.cuspOrbit = Γ.cuspOrbitOfSL2Z γ ∧
      D.scaling⁻¹ = sl2zToPSL2R γ ∧ D.width = cuspWidth Γ γ := by
  obtain ⟨D, hD1, hD2⟩ := (Γ.isCuspPoint_map_sl2zToPSL2R_smul_infty γ).exists_cuspDatum
    (σ := (sl2zToPSL2R γ)⁻¹) (by rw [inv_smul_smul])
  refine ⟨D, Subtype.ext ?_, by rw [hD2, inv_inv], cuspDatum_width_eq Γ γ D hD1 hD2⟩
  rw [Subgroup.CuspDatum.cuspOrbit_val, Subgroup.cuspOrbitOfSL2Z_val, hD1]

/-- Helper: Tau Ceti's cusp extension is the cusp function used in `IsMeromorphicModularForm`. -/
theorem cuspExtension_eq (Γ : Subgroup SL(2, ℤ)) (γ : SL(2, ℤ)) (D : (Γ.map sl2zToPSL2R).CuspDatum)
    (hs : D.scaling⁻¹ = sl2zToPSL2R γ) (hw : D.width = cuspWidth Γ γ) (f : ℍ → ℂ) :
    TauCeti.Subgroup.CuspDatum.cuspExtension D f =
      Periodic.cuspFunction (cuspWidth Γ γ) ((f ∣[(2 * 0 : ℤ)] γ) ∘ ofComplex) := by
  rw [TauCeti.Subgroup.CuspDatum.cuspExtension_def, hw]
  unfold UpperHalfPlane.cuspFunction
  congr 2
  funext z
  rw [SL_slash_apply, hs, sl2zToPSL2R_smul]
  simp

/-- **Milne's first definition** (p. 48): a modular function for $\Gamma$ is a meromorphic function on the compact
Riemann surface $\Gamma\backslash\mathbb H^*$ (Tau Ceti's `CompactifiedQuotient` of the image of $\Gamma$ in
$\mathrm{PSL}_2(\mathbb R)$). Comparison: $f$ is a modular function iff it is the pullback $F \circ p$ of a meromorphic
function $F$ on $\Gamma\backslash\mathbb H^*$ along $p : \mathbb H \to \Gamma\backslash\mathbb H^*$ (pointwise equality,
which also fixes the junk values at poles; agreement only off a discrete set would not control $f$ near the cusps). -/
@[kb "milne2017mf" "Section 4, modular function as a meromorphic function on X(Gamma) (pdf p. 48)"]
theorem isModularFunction_iff_compactifiedQuotient (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (f : ℍ → ℂ) :
    IsModularFunction Γ f ↔
      (∀ γ ∈ Γ, ∀ z : ℍ, f (γ • z) = f z) ∧ (∀ z : ℍ, MeromorphicAt (f ∘ ofComplex) (z : ℂ)) ∧
      ∃ F : (Γ.map sl2zToPSL2R).CompactifiedQuotient → ℂ,
        (∀ x, TauCeti.RiemannSurface.MeromorphicAt F x) ∧
        ∀ z : ℍ, f z = F (Subgroup.CompactifiedQuotient.ofQuotient (Quotient.mk _ z)) := by
  constructor
  · intro hf
    have hf' : IsMeromorphicModularForm Γ 0 f := hf
    refine ⟨hf.invariant, hf'.meromorphic, ?_⟩
    have hinv : ∀ a b : ℍ, MulAction.orbitRel (Γ.map sl2zToPSL2R) ℍ a b → f a = f b := by
      intro a b hab
      obtain ⟨⟨_, γ0, hγ0, rfl⟩, hg⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hab)
      rw [← hg]
      show f (sl2zToPSL2R γ0 • b) = f b
      rw [sl2zToPSL2R_smul]
      exact hf.invariant γ0 hγ0 b
    let F : (Γ.map sl2zToPSL2R).CompactifiedQuotient → ℂ := fun x ↦
      match x with
      | .ofQuotient p => Quotient.lift f hinv p
      | .ofCusp _ => 0
    refine ⟨F, ?_, fun z ↦ rfl⟩
    intro x
    cases x with
    | ofQuotient p =>
      induction p using Quotient.inductionOn with
      | h z =>
        rw [Subgroup.CompactifiedQuotient.meromorphicAt_ofQuotient_mk_iff]
        show TauCeti.RiemannSurface.MeromorphicAt f z
        rw [TauCeti.UpperHalfPlane.meromorphicAt_iff_meromorphicAt_comp_ofComplex]
        exact hf'.meromorphic z
    | ofCusp C =>
      obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
      obtain ⟨D, hD, hs, hw⟩ := exists_cuspDatum_of_sl2z Γ γ
      rw [← hD, Subgroup.CompactifiedQuotient.meromorphicAt_ofCusp_iff D (f := f) (fun z ↦ rfl),
        cuspExtension_eq Γ γ D hs hw]
      exact hf'.meromorphic_cusp γ
  · rintro ⟨hinv, hmero, F, hFm, hF⟩
    refine ⟨fun γ hγ ↦ ?_, hmero, fun γ ↦ ?_⟩
    · funext z
      rw [SL_slash_apply]
      simpa using hinv γ hγ z
    · obtain ⟨D, hD, hs, hw⟩ := exists_cuspDatum_of_sl2z Γ γ
      have h := (Subgroup.CompactifiedQuotient.meromorphicAt_ofCusp_iff D (f := f)
        (fun z ↦ (hF z).symm)).1 (hFm _)
      rwa [cuspExtension_eq Γ γ D hs hw] at h

/-- Helper: a modular function for $\Gamma(1)$ is $1$-periodic. -/
theorem IsModularFunction.periodic_top {f : ℍ → ℂ} (hf : IsModularFunction ⊤ f) :
    Function.Periodic (f ∘ ofComplex) 1 :=
  UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ by
    rw [← modular_T_smul]
    exact hf.invariant _ (Subgroup.mem_top _) τ

/-- **Example 4.1**, generators: for $\Gamma(1)$, condition (a) for a modular function need only be checked for $S$ and
$T$: $f(-1/z) = f(z)$ and $f(z+1) = f(z)$. -/
@[kb "milne2017mf" "Section 4, Example 4.1 (pdf p. 48)"]
theorem invariant_one_iff_generators (f : ℍ → ℂ) :
    (∀ γ : SL(2, ℤ), ∀ z : ℍ, f (γ • z) = f z) ↔
      (∀ z : ℍ, f (ModularGroup.S • z) = f z) ∧ ∀ z : ℍ, f (ModularGroup.T • z) = f z := by
  refine ⟨fun h ↦ ⟨fun z ↦ h _ z, fun z ↦ h _ z⟩, fun ⟨hS, hT⟩ γ z ↦ ?_⟩
  have key : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f := by
    refine SlashInvariantForm.slash_action_generators_SL2Z ?_ ?_
    · funext z
      rw [SL_slash_apply]
      simpa using hS z
    · funext z
      rw [SL_slash_apply]
      simpa using hT z
  have h := congrFun (key γ) z
  rw [SL_slash_apply] at h
  simpa using h

/-- **Example 4.1**, Laurent expansion: a modular function for $\Gamma(1)$ is $f(z) = f^*(q) = \sum_{n\ge -N}a_nq^n$,
$q = e^{2\pi i z}$, for $\operatorname{Im} z$ large. -/
@[kb "milne2017mf" "Section 4, Example 4.1 (pdf p. 48)"]
theorem IsModularFunction.laurent_expansion {f : ℍ → ℂ} (hf : IsModularFunction ⊤ f) :
    ∃ N : ℕ, ∃ a : ℕ → ℂ, ∃ A : ℝ, ∀ z : ℍ, A < z.im →
      HasSum (fun n : ℕ ↦ a n * cexp (2 * π * Complex.I * z) ^ n)
        (cexp (2 * π * Complex.I * z) ^ N * f z) := by
  have hf' : IsMeromorphicModularForm ⊤ 0 f := hf
  have h1 := hf'.meromorphic_cusp 1
  rw [cuspWidth_top, SlashAction.slash_one] at h1
  obtain ⟨N, hN⟩ := h1
  obtain ⟨p, r, hr⟩ := hN
  have hper := hf.periodic_top
  have hev := (UpperHalfPlane.qParam_tendsto_atImInfty one_pos).eventually
    (Metric.isOpen_eball.mem_nhds (Metric.mem_eball_self hr.r_pos))
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).1 hev
  refine ⟨N, fun n ↦ p.coeff n, A, fun z hz ↦ ?_⟩
  have hq : Function.Periodic.qParam 1 (z : ℂ) ∈ Metric.eball (0 : ℂ) r := hA z hz.le
  have hs := hr.hasSum (y := Function.Periodic.qParam 1 (z : ℂ)) (by simpa using hq)
  have hqe : Function.Periodic.qParam 1 (z : ℂ) = cexp (2 * π * Complex.I * z) := by
    simp [Function.Periodic.qParam]
  have hF : Function.Periodic.cuspFunction 1 (f ∘ ofComplex) (Function.Periodic.qParam 1 (z : ℂ)) =
      f z := UpperHalfPlane.eq_cuspFunction z one_ne_zero hper
  rw [zero_add, hF, hqe] at hs
  convert hs using 1
  · funext n
    rw [p.apply_eq_pow_smul_coeff]
    simp [mul_comm]
  · simp

/-- Helper: $j$ is invariant under $\mathrm{SL}_2(\mathbb Z)$ (with the `SL(2, ℤ)` action). -/
theorem jFun_smul (γ : SL(2, ℤ)) (z : ℍ) : jFun (γ • z) = jFun z := by
  rw [jFun_eq]
  have hAction : (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) • z = γ • z := by
    rw [MulAction.compHom_smul_def, MulAction.compHom_smul_def]
    have hMap : Matrix.SpecialLinearGroup.mapGL ℝ (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) =
        Matrix.SpecialLinearGroup.mapGL ℝ γ := by
      ext i j
      simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    exact congrArg (· • z) hMap
  rw [← hAction]
  exact TauCeti.ModularForm.j_smul γ z

/-- Helper: $j|_0\gamma = j$. -/
theorem jFun_slash (γ : SL(2, ℤ)) : jFun ∣[(2 * 0 : ℤ)] γ = jFun := by
  funext z
  rw [SL_slash_apply, jFun_smul]
  simp

/-- Helper: $j$ is holomorphic in the sense of `AnalyticAt`. -/
theorem jFun_analyticAt (z : ℍ) : AnalyticAt ℂ (jFun ∘ ofComplex) (z : ℂ) := by
  rw [jFun_eq]
  exact TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex TauCeti.ModularForm.j_mdifferentiable z.im_pos

/-- Helper: the values of Tau Ceti's `jBiholomorph` on points of $\mathbb H$ are those of $j$. -/
theorem jBiholomorph_apply_mk (z : ℍ) :
    TauCeti.ModularGroup.jBiholomorph (Subgroup.CompactifiedQuotient.ofQuotient (Quotient.mk _ z)) =
      (jFun z : OnePoint ℂ) := by
  rw [TauCeti.ModularGroup.jBiholomorph_ofQuotient, TauCeti.ModularGroup.jQuotient_mk, jFun_eq]

/-- Helper: an invariant holomorphic function bounded at $i\infty$ is constant. -/
theorem exists_const_of_invariant {d : ℍ → ℂ} (hinv : ∀ (γ : SL(2, ℤ)) (z : ℍ), d (γ • z) = d z)
    (hd : MDiff d) (hb : IsBoundedAtImInfty d) : ∃ c : ℂ, ∀ z, d z = c := by
  have hslash : ∀ γ : SL(2, ℤ), d ∣[(0 : ℤ)] γ = d := by
    intro γ
    funext z
    rw [SL_slash_apply]
    simpa using hinv γ z
  let F : ModularForm 𝒮ℒ 0 :=
    { toFun := d
      slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hslash γ
      holo' := hd
      bdd_at_cusps' := fun {c} hc ↦ by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        rw [hslash γ]
        exact hb }
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const F
  exact ⟨c, fun z ↦ congrFun hc z⟩

/-- Helper: $J_0 = j/1728$ near the cusp is a constant multiple of $j$'s cusp function. -/
theorem cuspFunction_J0_eventuallyEq :
    Periodic.cuspFunction 1 ((fun z ↦ jFun z / 1728) ∘ ofComplex) =ᶠ[𝓝[≠] 0]
      (1 / 1728 : ℂ) • Periodic.cuspFunction 1 (jFun ∘ ofComplex) := by
  filter_upwards [self_mem_nhdsWithin] with q hq
  rw [Periodic.cuspFunction_eq_of_nonzero _ _ hq, Pi.smul_apply,
    Periodic.cuspFunction_eq_of_nonzero _ _ hq]
  simp [div_eq_inv_mul]

/-- Helper: $j/1728$ is a modular function. -/
theorem J0_isModularFunction : IsModularFunction ⊤ (fun z ↦ jFun z / 1728) := by
  have hsl : ∀ γ : SL(2, ℤ), (fun z ↦ jFun z / 1728) ∣[(2 * 0 : ℤ)] γ = fun z ↦ jFun z / 1728 := by
    intro γ
    funext z
    rw [SL_slash_apply]
    show jFun (γ • z) / 1728 * _ = _
    rw [jFun_smul]
    simp
  refine ⟨fun γ _ ↦ hsl γ, fun z ↦ ?_, fun γ ↦ ?_⟩
  · exact ((jFun_analyticAt z).fun_mul (analyticAt_const (v := (1 / 1728 : ℂ)))).meromorphicAt.congr
      (Filter.Eventually.of_forall fun w ↦ by simp [div_eq_mul_inv, mul_comm])
  · rw [hsl, cuspWidth_top]
    have h : MeromorphicAt (Periodic.cuspFunction 1 (jFun ∘ ofComplex)) 0 := by
      rw [jFun_eq]
      exact TauCeti.ModularForm.meromorphicAt_cuspFunction_j
    exact ((h.const_smul (1 / 1728 : ℂ))).congr cuspFunction_J0_eventuallyEq.symm

/-- Helper: $j/1728$ has a simple pole at the cusp. -/
theorem J0_cuspOrder : cuspOrder ⊤ 0 (fun z ↦ jFun z / 1728) 1 = -1 := by
  have hsl : ((fun z ↦ jFun z / 1728) ∣[(2 * 0 : ℤ)] (1 : SL(2, ℤ))) = fun z ↦ jFun z / 1728 :=
    SlashAction.slash_one _ _
  unfold cuspOrder
  rw [hsl, cuspWidth_top, meromorphicOrderAt_congr cuspFunction_J0_eventuallyEq,
    meromorphicOrderAt_const_smul_eq_meromorphicOrderAt (by norm_num)]
  rw [jFun_eq]
  exact TauCeti.ModularForm.meromorphicOrderAt_cuspFunction_j

/-- Helper: the conditions of Proposition 4.3 force $J = j/1728$. -/
theorem J_eq_of_conditions {J : ℍ → ℂ}
    (hJ : IsModularFunction ⊤ J ∧ (∀ z : ℍ, AnalyticAt ℂ (J ∘ ofComplex) (z : ℂ)) ∧
      cuspOrder ⊤ 0 J 1 = -1 ∧ J UpperHalfPlane.I = 1 ∧ J UpperHalfPlane.ρ = 0) :
    ∀ z, J z = jFun z / 1728 := by
  obtain ⟨hmod, hana, hord, hI, hρ⟩ := hJ
  have hper := hmod.periodic_top
  have hmer : MeromorphicAt (Periodic.cuspFunction 1 (J ∘ ofComplex)) 0 := by
    have h1 := (show IsMeromorphicModularForm ⊤ 0 J from hmod).meromorphic_cusp 1
    rwa [cuspWidth_top, SlashAction.slash_one] at h1
  have hord' : meromorphicOrderAt (Periodic.cuspFunction 1 (J ∘ ofComplex)) 0 =
      ((-1 : ℤ) : WithTop ℤ) := by
    unfold cuspOrder at hord
    rw [cuspWidth_top, SlashAction.slash_one] at hord
    exact_mod_cast hord
  obtain ⟨h, hh, -, hev⟩ := (meromorphicOrderAt_eq_int_iff hmer).1 hord'
  have hjan := TauCeti.ModularForm.analyticAt_cuspFunction_qParam_mul_j
  have hjev := TauCeti.ModularForm.cuspFunction_j_eventuallyEq
  have hj0 := TauCeti.ModularForm.cuspFunction_qParam_mul_j_zero
  set hj := cuspFunction 1 (fun τ : ℍ ↦ Periodic.qParam 1 (τ : ℂ) * TauCeti.ModularForm.j τ) with hhj
  set c := h 0 with hc
  have hG : AnalyticAt ℂ (fun q ↦ h q - c * hj q) 0 := hh.sub (analyticAt_const.mul hjan)
  have hG0 : (fun q ↦ h q - c * hj q) 0 = 0 := by simp [c, hj0]
  have hslope := hasDerivAt_iff_tendsto_slope.1 hG.differentiableAt.hasDerivAt
  have hq : Tendsto (fun z : ℍ ↦ Periodic.qParam 1 (z : ℂ)) atImInfty (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨UpperHalfPlane.qParam_tendsto_atImInfty one_pos,
      Filter.Eventually.of_forall fun z ↦ Periodic.qParam_ne_zero _⟩
  have htend := hslope.comp hq
  have ev1 := hq.eventually hev
  have ev2 := hq.eventually hjev
  have hbd : IsBoundedAtImInfty (fun z ↦ J z - c * jFun z) := by
    refine (Tendsto.isBigO_one ℝ (c := (deriv (fun q ↦ h q - c * hj q) 0)) (htend.congr' ?_))
    filter_upwards [ev1, ev2] with z h1 h2
    have e1 : J z = Periodic.cuspFunction 1 (J ∘ ofComplex) (Periodic.qParam 1 (z : ℂ)) :=
      (UpperHalfPlane.eq_cuspFunction z one_ne_zero hper).symm
    have e2 : jFun z = cuspFunction 1 TauCeti.ModularForm.j (Periodic.qParam 1 (z : ℂ)) := by
      rw [jFun_eq]
      exact (UpperHalfPlane.eq_cuspFunction z one_ne_zero
        TauCeti.ModularForm.periodic_j_comp_ofComplex).symm
    have hq0 : Periodic.qParam 1 (z : ℂ) ≠ 0 := Periodic.qParam_ne_zero _
    show slope (fun q ↦ h q - c * hj q) 0 (Periodic.qParam 1 (z : ℂ)) = J z - c * jFun z
    rw [e1, e2, h1, h2, slope_def_field]
    simp only [zpow_neg, zpow_one, smul_eq_mul, sub_zero, hG0]
    field_simp
  have hJmd : MDiff J := fun z ↦ UpperHalfPlane.mdifferentiableAt_iff.2 (hana z).differentiableAt
  have hjmd : MDiff jFun := by
    rw [jFun_eq]
    exact TauCeti.ModularForm.j_mdifferentiable
  obtain ⟨b, hb⟩ := exists_const_of_invariant (d := fun z ↦ J z - c * jFun z)
    (fun γ z ↦ by
      show J (γ • z) - c * jFun (γ • z) = J z - c * jFun z
      rw [hmod.invariant γ (Subgroup.mem_top _) z, jFun_smul])
    (hJmd.sub (mdifferentiable_const.mul hjmd)) hbd
  have hjρ : jFun UpperHalfPlane.ρ = 0 := by rw [jFun_eq]; exact TauCeti.ModularForm.j_ρ
  have hjI : jFun UpperHalfPlane.I = 1728 := by rw [jFun_eq]; exact TauCeti.ModularForm.j_I
  have hb0 : b = 0 := by
    have := hb UpperHalfPlane.ρ
    rw [hρ, hjρ] at this
    simpa using this.symm
  have hc' : c = 1 / 1728 := by
    have := hb UpperHalfPlane.I
    rw [hI, hjI, hb0] at this
    field_simp
    linear_combination -this
  intro z
  have := hb z
  rw [hb0, hc'] at this
  linear_combination this

/-- **Proposition 4.3**: there is a unique modular function $J$ for $\Gamma(1)$ that is holomorphic on $\mathbb H$, has a
simple pole at $i\infty$, and takes the values $J(i) = 1$, $J(\rho) = 0$, $\rho = e^{2\pi i/3}$. -/
@[kb "milne2017mf" "Section 4, Proposition 4.3 (pdf p. 49)"]
theorem existsUnique_J :
    ∃! J : ℍ → ℂ, IsModularFunction ⊤ J ∧ (∀ z : ℍ, AnalyticAt ℂ (J ∘ ofComplex) (z : ℂ)) ∧
      cuspOrder ⊤ 0 J 1 = -1 ∧ J UpperHalfPlane.I = 1 ∧ J UpperHalfPlane.ρ = 0 := by
  refine ⟨fun z ↦ jFun z / 1728, ⟨J0_isModularFunction, fun z ↦ ?_, J0_cuspOrder, ?_, ?_⟩, ?_⟩
  · exact ((jFun_analyticAt z).fun_mul (analyticAt_const (v := (1 / 1728 : ℂ)))).congr
      (Filter.Eventually.of_forall fun w ↦ by simp [div_eq_mul_inv, mul_comm])
  · rw [jFun_eq]
    simp [TauCeti.ModularForm.j_I]
  · rw [jFun_eq]
    simp [TauCeti.ModularForm.j_ρ]
  · intro J hJ
    funext z
    exact J_eq_of_conditions hJ z

/-- **Remark 4.4**: $j$ is invariant under $\Gamma(1)$ (a modular function). -/
@[kb "milne2017mf" "Section 4, Remark 4.4 (pdf p. 49)"]
theorem jFun_isModularFunction : IsModularFunction ⊤ jFun := by
  refine ⟨fun γ _ ↦ jFun_slash γ, fun z ↦ (jFun_analyticAt z).meromorphicAt, fun γ ↦ ?_⟩
  rw [jFun_slash, cuspWidth_top, jFun_eq]
  exact TauCeti.ModularForm.meromorphicAt_cuspFunction_j

/-- **Remark 4.4**: $j$ is holomorphic on $\mathbb H$. -/
@[kb "milne2017mf" "Section 4, Remark 4.4 (pdf p. 49)"]
theorem jFun_holomorphic (z : ℍ) : AnalyticAt ℂ (jFun ∘ ofComplex) (z : ℂ) :=
  jFun_analyticAt z

/-- **Remark 4.4**: $j$ has a simple pole at $i\infty$. -/
@[kb "milne2017mf" "Section 4, Remark 4.4 (pdf p. 49)"]
theorem cuspOrder_jFun : cuspOrder ⊤ 0 jFun 1 = -1 := by
  unfold cuspOrder
  rw [jFun_slash, cuspWidth_top, jFun_eq]
  exact TauCeti.ModularForm.meromorphicOrderAt_cuspFunction_j

/-- **Remark 4.4**: $j$ defines a bijection $\Gamma(1)\backslash\mathbb H \to \mathbb C$. -/
@[kb "milne2017mf" "Section 4, Remark 4.4 (pdf p. 49)"]
theorem jFun_bijective :
    (∀ c : ℂ, ∃ z : ℍ, jFun z = c) ∧ ∀ z w : ℍ, jFun z = jFun w → ∃ γ : SL(2, ℤ), γ • w = z := by
  constructor
  · intro c
    have h := TauCeti.ModularGroup.jBiholomorph.apply_symm_apply (c : OnePoint ℂ)
    generalize TauCeti.ModularGroup.jBiholomorph.symm (c : OnePoint ℂ) = x at h
    cases x with
    | ofQuotient p =>
      obtain ⟨z, rfl⟩ := Quotient.exists_rep p
      rw [jBiholomorph_apply_mk] at h
      exact ⟨z, OnePoint.coe_injective h⟩
    | ofCusp C =>
      rw [TauCeti.ModularGroup.jBiholomorph_ofCusp] at h
      exact absurd h (by simp)
  · intro z w hzw
    have h1 : TauCeti.ModularGroup.jBiholomorph (Subgroup.CompactifiedQuotient.ofQuotient
        (Quotient.mk _ z)) = TauCeti.ModularGroup.jBiholomorph (Subgroup.CompactifiedQuotient.ofQuotient
        (Quotient.mk _ w)) := by
      rw [jBiholomorph_apply_mk, jBiholomorph_apply_mk, hzw]
    have h2 := Subgroup.CompactifiedQuotient.ofQuotient_injective
      (TauCeti.ModularGroup.jBiholomorph.injective h1)
    have h3 : MulAction.orbitRel psl2zToPSL2R.range ℍ z w := Quotient.exact h2
    rw [TauCeti.ModularGroup.orbitRel_psl2zToPSL2RRange_iff_orbitRel_sl] at h3
    simpa only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] using h3

/-- **Remark 4.4**: $j$ defines an isomorphism of Riemann surfaces from $\Gamma(1)\backslash\mathbb H^*$ onto the
Riemann sphere (Tau Ceti's `TauCeti.ModularGroup.jBiholomorph`). -/
@[kb "milne2017mf" "Section 4, Remark 4.4 (pdf p. 49)"]
theorem exists_jFun_biholomorph :
    ∃ e : (psl2zToPSL2R.range).CompactifiedQuotient ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ OnePoint ℂ,
      ∀ z : ℍ, e (Subgroup.CompactifiedQuotient.ofQuotient (Quotient.mk _ z)) = (jFun z : OnePoint ℂ) :=
  ⟨TauCeti.ModularGroup.jBiholomorph, jBiholomorph_apply_mk⟩

/-- **Remark 4.4**: $j = 1728J$, for the function $J$ of Proposition 4.3. -/
@[kb "milne2017mf" "Section 4, Remark 4.4 (pdf p. 49)"]
theorem jFun_eq_smul_J {J : ℍ → ℂ} (hJ : IsModularFunction ⊤ J ∧ (∀ z : ℍ, AnalyticAt ℂ (J ∘ ofComplex) (z : ℂ)) ∧
      cuspOrder ⊤ 0 J 1 = -1 ∧ J UpperHalfPlane.I = 1 ∧ J UpperHalfPlane.ρ = 0) :
    jFun = fun z ↦ 1728 * J z := by
  funext z
  rw [J_eq_of_conditions hJ z]
  ring

end ModularFormsKB.Milne
