import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Group
import TauCeti.Analysis.Complex.UpperHalfPlane.Rotation
import TauCeti.Analysis.SpecialFunctions.Trigonometric.MatrixFinTwo
import ModularFormsKB.Milne.Ch1.GroupActions
import ModularFormsKB.Citation
/-!
# Milne, Chapter 2: automorphisms of `ℍ` and of the unit disk

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §2, pdf pp. 25–26.

* `SO2R`: the special orthogonal group of rotation matrices `!![cos θ, sin θ; -sin θ, cos θ]` (p. 25, D038), built
  on Tau Ceti's `Matrix.SpecialLinearGroup.rotation`.
* Proposition 2.1: (a) transitivity is Mathlib's `UpperHalfPlane.isPretransitiveSL2R`; (b) `SL₂(ℝ)/{±I} ≅ Aut(ℍ)`;
  (c) the stabilizer of `i` is `SO₂(ℝ)`; (d) `SL₂(ℝ)/SO₂(ℝ) ≃ₜ ℍ`.
* Lemma 2.2: the automorphisms of the disk fixing `0` are the rotations (Tau Ceti
  `TauCeti.stabilizer_zero_eq_unitDiscRotation_subgroupOf`, restated in the book's form).
* Exercise 2.3: `SU(1,1)`, its action on the disk, and the Cayley transform.

`Aut(ℍ)` is the group of biholomorphic automorphisms: permutations of `ℍ` that are holomorphic (Mathlib's
`MDifferentiable` for the complex manifold `ℍ`) with holomorphic inverse. `Aut(D)` is Tau Ceti's `unitDiscAut`.
`{±I}` is written as the centre of `SL₂(ℝ)` (resp. of `SU(1,1)`), which is `{±I}`.
-/

open Matrix MatrixGroups UpperHalfPlane Complex ComplexConjugate
open scoped Manifold ContDiff

namespace ModularFormsKB.Milne

/-! ### `SO₂(ℝ)` and Proposition 2.1 -/

/-- **The special orthogonal group** (Milne, p. 25): the rotation matrices `!![cos θ, sin θ; -sin θ, cos θ]` in
`SL₂(ℝ)`. -/
@[kb "milne2017mf" "§2, definition of SO_2(R), pdf p. 25"]
noncomputable def SO2R : Subgroup SL(2, ℝ) where
  carrier := Set.range Matrix.SpecialLinearGroup.rotation
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, Matrix.SpecialLinearGroup.rotation_add a b⟩
  one_mem' := ⟨0, Matrix.SpecialLinearGroup.rotation_zero⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, (Matrix.SpecialLinearGroup.rotation_inv a).symm⟩

/-- **Biholomorphic automorphisms of `ℍ`** (Milne, p. 25): permutations of `ℍ` that are holomorphic with holomorphic
inverse. -/
@[kb "milne2017mf" "§2, Aut(H), pdf p. 25"]
def autUpperHalfPlane : Subgroup (Equiv.Perm ℍ) where
  carrier := {e | MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e.symm}
  mul_mem' := by
    rintro e₁ e₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
    exact ⟨h₁.comp h₂, h₂'.comp h₁'⟩
  one_mem' := ⟨mdifferentiable_id, mdifferentiable_id⟩
  inv_mem' := by
    rintro e ⟨h, h'⟩
    exact ⟨h', h⟩

/-- The centre of `SL₂(ℝ)` is `{±I}`, the subgroup appearing in Proposition 2.1 (b). -/
@[kb "milne2017mf" "Proposition 2.1 (b), proof: only ±I act trivially, pdf p. 25"]
theorem mem_center_SL2R_iff (g : SL(2, ℝ)) : g ∈ Subgroup.center SL(2, ℝ) ↔ g = 1 ∨ g = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hg⟩
    rw [Fintype.card_fin] at hr
    have : (r - 1) * (r + 1) = 0 := by linear_combination hr
    rcases mul_eq_zero.1 this with h | h
    · left; have : r = 1 := by linarith
      subst this
      ext i j; rw [← hg]; fin_cases i <;> fin_cases j <;> simp
    · right; have : r = -1 := by linarith
      subst this
      ext i j; rw [← hg]; fin_cases i <;> fin_cases j <;> simp
  · rintro (rfl | rfl)
    · exact ⟨1, by simp, by simp⟩
    · refine ⟨-1, by simp, ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp

/-! ### Lemma 2.2 -/

/-- **Milne, Lemma 2.2.** The automorphisms of the open unit disk fixing `0` are the maps `z ↦ ζ z` with `|ζ| = 1`.
Tau Ceti: `TauCeti.stabilizer_zero_eq_unitDiscRotation_subgroupOf`. -/
@[kb "milne2017mf" "Lemma 2.2, pdf p. 26"]
theorem unitDiscAut_fix_zero_iff (e : Equiv.Perm Complex.UnitDisc) :
    (e ∈ TauCeti.unitDiscAut ∧ e 0 = 0) ↔ ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∀ z : Complex.UnitDisc, (e z : ℂ) = ζ * z := by
  constructor
  · rintro ⟨he, h0⟩
    obtain ⟨u, a, rfl⟩ := TauCeti.mem_unitDiscAut_iff.1 he
    have ha : (0 : Complex.UnitDisc) = a :=
      (TauCeti.unitDiscStandardAutomorphismEquiv u a).injective
        (h0.trans (TauCeti.unitDiscStandardAutomorphismEquiv_self u a).symm)
    subst ha
    refine ⟨u, by simp, fun z => ?_⟩
    simp [TauCeti.coe_unitDiscStandardAutomorphismEquiv_apply]
  · rintro ⟨ζ, hζ, h⟩
    let u : Circle := ⟨ζ, mem_sphere_zero_iff_norm.2 hζ⟩
    have hu : e = TauCeti.unitDiscStandardAutomorphismEquiv u 0 := by
      refine Equiv.ext fun z => Complex.UnitDisc.coe_injective ?_
      rw [h z, TauCeti.coe_unitDiscStandardAutomorphismEquiv_apply]
      simp [u]
    refine ⟨hu ▸ TauCeti.unitDiscStandardAutomorphismEquiv_mem_unitDiscAut u 0, ?_⟩
    apply Complex.UnitDisc.coe_injective
    rw [h]; simp

/-- **Milne, Exercise 2.3 (c).** Under the isomorphism `z ↦ (z - i)/(z + i)` of `ℍ` onto `D`, the action of
`!![cos θ, sin θ; -sin θ, cos θ]` on `ℍ` corresponds to the action of `!![e^{iθ}, 0; 0, e^{-iθ}]` on `D`, i.e. to
`w ↦ e^{2iθ} w`. -/
@[kb "milne2017mf" "Exercise 2.3 (c), pdf p. 26"]
theorem cayley_rotation_smul (θ : ℝ) (z : ℍ) :
    (((Matrix.SpecialLinearGroup.rotation θ • z : ℍ) : ℂ) - Complex.I) /
        (((Matrix.SpecialLinearGroup.rotation θ • z : ℍ) : ℂ) + Complex.I) =
      (exp (θ * Complex.I) * (((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)) + 0) /
        (0 * (((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)) + exp (-(θ * Complex.I))) := by
  have hz : (z : ℂ) + Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith [z.im_pos]
  have hD : ((-Real.sin θ : ℝ) : ℂ) * z + (Real.cos θ : ℝ) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero
      (Matrix.SpecialLinearGroup.mapGL ℝ (Matrix.SpecialLinearGroup.rotation θ)) z
    simpa [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.mapGL_coe_matrix] using this
  rw [UpperHalfPlane.specialLinearGroup_apply]
  simp only [Matrix.SpecialLinearGroup.coe_rotation]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Algebra.algebraMap_self_apply]
  have e1 : exp (θ * Complex.I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have e2 : exp (-(θ * Complex.I)) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    rw [show -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  have hne := Complex.exp_ne_zero (-(θ * Complex.I))
  rw [e1, e2]
  rw [e2] at hne
  simp only [Complex.ofReal_neg] at hD ⊢
  generalize (Real.cos θ : ℂ) = c at *
  generalize (Real.sin θ : ℂ) = s at *
  have hN : (c * z + s) + Complex.I * (-s * z + c) ≠ 0 := by
    have : (c * z + s) + Complex.I * (-s * z + c) = (c - s * Complex.I) * (z + Complex.I) := by
      ring_nf; simp [Complex.I_sq]
    rw [this]; exact mul_ne_zero hne hz
  generalize hd : (-s * (z : ℂ) + c) = d at *
  rw [div_add' _ _ _ hD, div_sub' hD, div_div_div_cancel_right₀ hD,
    div_eq_div_iff hN (by simpa using hne)]
  field_simp
  subst hd
  ring_nf
  simp [Complex.I_sq]

namespace AutAux

theorem zI (z : ℍ) : (z : ℂ) + Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith [z.im_pos]

theorem norm_cay_lt (z : ℍ) : ‖((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)‖ < 1 := by
  rw [norm_div, div_lt_one (norm_pos_iff.mpr (zI z)), ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.I_re, Complex.I_im]
  nlinarith [show 0 < (z : ℂ).im from z.im_pos]

/-- The Cayley transform `ℍ → D`. -/
noncomputable def cay (z : ℍ) : Complex.UnitDisc :=
  Complex.UnitDisc.mk (((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)) (norm_cay_lt z)

theorem one_sub_ne {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h
  have : w = 1 := (sub_eq_zero.1 h).symm
  rw [this] at hw
  simp at hw

theorem uncay_im_pos {w : ℂ} (hw : ‖w‖ < 1) :
    0 < (Complex.I * (1 + w) / (1 - w)).im := by
  have h1 := one_sub_ne hw
  have hN : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.2 h1
  have hw2 : w.re ^ 2 + w.im ^ 2 < 1 := by
    have := Complex.sq_norm w
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg w]
  rw [Complex.div_im]
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re,
    Complex.add_im, Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im]
  rw [Complex.normSq_apply] at hN ⊢
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at hN ⊢
  rw [← sub_div]
  exact div_pos (by nlinarith) (by nlinarith)

theorem uncay_mem (w : Complex.UnitDisc) :
    0 < (Complex.I * (1 + (w : ℂ)) / (1 - (w : ℂ))).im :=
  uncay_im_pos w.norm_lt_one

/-- The inverse Cayley transform `D → ℍ`. -/
noncomputable def uncay (w : Complex.UnitDisc) : ℍ :=
  ⟨Complex.I * (1 + (w : ℂ)) / (1 - (w : ℂ)), uncay_mem w⟩

theorem uncay_cay (z : ℍ) : uncay (cay z) = z := by
  apply UpperHalfPlane.ext
  simp only [uncay, cay, Complex.UnitDisc.coe_mk]
  have hz := zI z
  field_simp
  ring

theorem cay_uncay (w : Complex.UnitDisc) : cay (uncay w) = w := by
  apply Complex.UnitDisc.coe_injective
  simp only [uncay, cay, Complex.UnitDisc.coe_mk]
  have h1 := one_sub_ne w.norm_lt_one
  have hden : Complex.I * (1 + (w : ℂ)) / (1 - w) + Complex.I = 2 * Complex.I / (1 - w) := by
    field_simp
    ring
  have hnum : Complex.I * (1 + (w : ℂ)) / (1 - w) - Complex.I = 2 * Complex.I * w / (1 - w) := by
    field_simp
    ring
  have h2I : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  rw [hden, hnum]
  field_simp

/-- The Cayley equivalence `ℍ ≃ D`. -/
noncomputable def cayE : ℍ ≃ Complex.UnitDisc where
  toFun := cay
  invFun := uncay
  left_inv := uncay_cay
  right_inv := cay_uncay

/-- Conjugate a permutation of `ℍ` to one of the disc. -/
noncomputable def conjD (f : Equiv.Perm ℍ) : Equiv.Perm Complex.UnitDisc :=
  cayE.symm.trans (f.trans cayE)

theorem conjD_apply (f : Equiv.Perm ℍ) (w : Complex.UnitDisc) :
    conjD f w = cay (f (uncay w)) := rfl

theorem conjD_symm (f : Equiv.Perm ℍ) : (conjD f).symm = conjD f.symm := rfl

theorem isHol_conjD {f : Equiv.Perm ℍ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    TauCeti.IsHolomorphicUnitDiscPerm (conjD f) := by
  set F1 : ℂ → ℂ := (fun z : ℍ => (f z : ℂ)) ∘ ofComplex with hF1
  have hd : DifferentiableOn ℂ F1 {z | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.1 (UpperHalfPlane.mdifferentiable_coe.comp hf)
  refine ⟨fun w => (F1 (Complex.I * (1 + w) / (1 - w)) - Complex.I) /
      (F1 (Complex.I * (1 + w) / (1 - w)) + Complex.I), ?_, ?_⟩
  · intro w hw
    have hw' : ‖w‖ < 1 := by simpa using hw
    have hw1 : 1 - w ≠ 0 := one_sub_ne hw'
    have hu : 0 < (Complex.I * (1 + w) / (1 - w)).im := uncay_im_pos hw'
    have hF : DifferentiableAt ℂ F1 (Complex.I * (1 + w) / (1 - w)) :=
      (hd _ hu).differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hu)
    have hu' : DifferentiableAt ℂ (fun w : ℂ => Complex.I * (1 + w) / (1 - w)) w :=
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => Complex.I * (1 + w)) w).div
        (by fun_prop) hw1
    have hc := DifferentiableAt.comp (g := F1) w hF hu'
    have hne : F1 (Complex.I * (1 + w) / (1 - w)) + Complex.I ≠ 0 := by
      have : F1 (Complex.I * (1 + w) / (1 - w)) = (f ⟨_, hu⟩ : ℂ) := by
        simp [hF1, UpperHalfPlane.ofComplex_apply_of_im_pos hu]
      rw [this]; exact zI _
    exact ((hc.sub_const _).div (hc.add_const _) hne).differentiableWithinAt
  · intro w
    rw [conjD_apply]
    have : F1 (Complex.I * (1 + (w : ℂ)) / (1 - (w : ℂ))) = (f (uncay w) : ℂ) := by
      simp only [hF1, Function.comp_apply]
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos (uncay_mem w)]
      rfl
    beta_reduce
    rw [this]
    rfl

theorem isHol_conjD_mem {f : Equiv.Perm ℍ} (hf : f ∈ autUpperHalfPlane) :
    conjD f ∈ TauCeti.unitDiscAut :=
  ⟨isHol_conjD hf.1, by rw [conjD_symm]; exact isHol_conjD hf.2⟩

/-- Action of `SL₂(ℝ)` is holomorphic. -/
theorem mdiff_smul (g : SL(2, ℝ)) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : ℍ => g • z) := by
  have h : ∀ z : ℍ, g • z = Matrix.SpecialLinearGroup.toGL g • z := fun z =>
    (Matrix.SpecialLinearGroup.toGL_smul g z).symm
  simp only [h]
  apply UpperHalfPlane.mdifferentiable_smul
  simp [Matrix.SpecialLinearGroup.toGL]

/-- `SL₂(ℝ) → Aut(ℍ)`. -/
noncomputable def hom : SL(2, ℝ) →* autUpperHalfPlane where
  toFun g := ⟨MulAction.toPermHom SL(2, ℝ) ℍ g, mdiff_smul g, by
    have : (MulAction.toPermHom SL(2, ℝ) ℍ g).symm = MulAction.toPermHom SL(2, ℝ) ℍ g⁻¹ := by
      rw [map_inv]; rfl
    rw [this]; exact mdiff_smul g⁻¹⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)

theorem hom_apply (g : SL(2, ℝ)) (z : ℍ) : (hom g : Equiv.Perm ℍ) z = g • z := rfl

theorem eq_pm_of_smul_eq (g : SL(2, ℝ)) (h : ∀ z : ℍ, g • z = z) : g = 1 ∨ g = -1 := by
  have key : ∀ z : ℍ, (g 0 0 : ℂ) * z + g 0 1 = z * ((g 1 0 : ℂ) * z + g 1 1) := by
    intro z
    have h1 := UpperHalfPlane.coe_specialLinearGroup_apply g z
    rw [h z] at h1
    simp only [Algebra.algebraMap_self_apply] at h1
    have hd : ((g 1 0 : ℂ) * z + g 1 1) ≠ 0 := by
      have := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ g) z
      simpa [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.mapGL_coe_matrix] using this
    rw [eq_div_iff hd] at h1
    linear_combination -h1
  have k1 := key UpperHalfPlane.I
  have k2 := key ⟨2 * Complex.I, by simp⟩
  simp only [UpperHalfPlane.coe_I] at k1
  simp only at k2
  have r1 := congrArg Complex.re k1
  have i1 := congrArg Complex.im k1
  have r2 := congrArg Complex.re k2
  have i2 := congrArg Complex.im k2
  simp at r1 i1 r2 i2
  have hc : g 1 0 = 0 := by linarith
  have hb : g 0 1 = 0 := by linarith
  have hd : g 1 1 = g 0 0 := by linarith
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  have h3 : (g 0 0 - 1) * (g 0 0 + 1) = 0 := by
    rw [hc, hb, hd] at hdet; linear_combination hdet
  rcases mul_eq_zero.1 h3 with h4 | h4
  · left
    have h5 : g 0 0 = 1 := by linarith
    ext i j; fin_cases i <;> fin_cases j <;> simp [hb, hc, hd, h5]
  · right
    have h5 : g 0 0 = -1 := by linarith
    ext i j; fin_cases i <;> fin_cases j <;> simp [hb, hc, hd, h5]

theorem hom_eq_one_iff (g : SL(2, ℝ)) : hom g = 1 ↔ g ∈ Subgroup.center SL(2, ℝ) := by
  rw [mem_center_SL2R_iff]
  constructor
  · intro h
    exact eq_pm_of_smul_eq g fun z => by
      rw [← hom_apply, h]; rfl
  · rintro (rfl | rfl)
    · exact map_one _
    · refine Subtype.ext (Equiv.ext fun z => ?_)
      rw [hom_apply]
      change (-1 : SL(2, ℝ)) • z = z
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      simp

/-- An automorphism of `ℍ` fixing `i` is a rotation. -/
theorem fix_I_rotation {f : Equiv.Perm ℍ} (hf : f ∈ autUpperHalfPlane) (hI : f UpperHalfPlane.I = UpperHalfPlane.I) :
    ∃ θ : ℝ, ∀ z : ℍ, f z = Matrix.SpecialLinearGroup.rotation θ • z := by
  have hd := isHol_conjD_mem hf
  have h0 : conjD f 0 = 0 := by
    have : uncay (0 : Complex.UnitDisc) = UpperHalfPlane.I := by
      apply UpperHalfPlane.ext
      simp [uncay]
    apply Complex.UnitDisc.coe_injective
    rw [conjD_apply, this, hI]
    simp [cay]
  obtain ⟨ζ, hζ, hz⟩ := (unitDiscAut_fix_zero_iff (conjD f)).1 ⟨hd, h0⟩
  refine ⟨Complex.arg ζ / 2, fun z => ?_⟩
  have e1 : (cay (f z) : ℂ) = ζ * (cay z : ℂ) := by
    have := hz (cay z)
    rwa [conjD_apply, uncay_cay] at this
  have e2 : (cay (Matrix.SpecialLinearGroup.rotation (Complex.arg ζ / 2) • z) : ℂ) = ζ * (cay z : ℂ) := by
    simp only [cay, Complex.UnitDisc.coe_mk]
    rw [cayley_rotation_smul]
    have h2 : Complex.exp (((Complex.arg ζ / 2 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((Complex.arg ζ / 2 : ℝ) : ℂ) * Complex.I) = ζ := by
      rw [← Complex.exp_add]
      have := Complex.norm_mul_exp_arg_mul_I ζ
      rw [hζ, Complex.ofReal_one, one_mul] at this
      have e : ((Complex.arg ζ / 2 : ℝ) : ℂ) * Complex.I + ((Complex.arg ζ / 2 : ℝ) : ℂ) * Complex.I =
          (Complex.arg ζ : ℂ) * Complex.I := by push_cast; ring
      rw [e]; exact this
    have h1 : Complex.exp (((Complex.arg ζ / 2 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-(((Complex.arg ζ / 2 : ℝ) : ℂ) * Complex.I)) = 1 := by
      rw [← Complex.exp_add]; simp
    have hE' := Complex.exp_ne_zero (-(((Complex.arg ζ / 2 : ℝ) : ℂ) * Complex.I))
    rw [zero_mul, zero_add, add_zero, div_eq_iff hE']
    linear_combination (-(Complex.exp (((Complex.arg ζ / 2 : ℝ) : ℂ) * Complex.I) *
      (((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)))) * h1 +
      ((((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)) *
        Complex.exp (-(((Complex.arg ζ / 2 : ℝ) : ℂ) * Complex.I))) * h2
  have e3 : cay (f z) = cay (Matrix.SpecialLinearGroup.rotation (Complex.arg ζ / 2) • z) :=
    Complex.UnitDisc.coe_injective (e1.trans e2.symm)
  calc f z = uncay (cay (f z)) := (uncay_cay _).symm
    _ = _ := by rw [e3, uncay_cay]

end AutAux

/-- **Milne, Proposition 2.1 (b).** The action of `SL₂(ℝ)` on `ℍ` induces an isomorphism
`SL₂(ℝ)/{±I} ≅ Aut(ℍ)`. -/
@[kb "milne2017mf" "Proposition 2.1 (b), pdf p. 25"]
theorem exists_mulEquiv_autUpperHalfPlane :
    ∃ φ : SL(2, ℝ) ⧸ Subgroup.center SL(2, ℝ) ≃* autUpperHalfPlane,
      ∀ (g : SL(2, ℝ)) (z : ℍ), (φ (g : SL(2, ℝ) ⧸ Subgroup.center SL(2, ℝ)) : Equiv.Perm ℍ) z = g • z := by
  have hker : Subgroup.center SL(2, ℝ) = AutAux.hom.ker := by
    ext g
    rw [MonoidHom.mem_ker, AutAux.hom_eq_one_iff]
  have hsurj : Function.Surjective AutAux.hom := by
    intro e
    obtain ⟨g0, hg0⟩ := MulAction.exists_smul_eq SL(2, ℝ) UpperHalfPlane.I (e.1 UpperHalfPlane.I)
    set f' : autUpperHalfPlane := (AutAux.hom g0)⁻¹ * e with hf'
    have hI : (f' : Equiv.Perm ℍ) UpperHalfPlane.I = UpperHalfPlane.I := by
      rw [hf']
      show (AutAux.hom g0 : Equiv.Perm ℍ).symm (e.1 UpperHalfPlane.I) = UpperHalfPlane.I
      rw [Equiv.symm_apply_eq]
      exact hg0.symm
    obtain ⟨θ, hθ⟩ := AutAux.fix_I_rotation f'.2 hI
    refine ⟨g0 * Matrix.SpecialLinearGroup.rotation θ, ?_⟩
    have : AutAux.hom (Matrix.SpecialLinearGroup.rotation θ) = f' :=
      Subtype.ext (Equiv.ext fun z => (hθ z).symm)
    rw [map_mul, this, hf', mul_inv_cancel_left]
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj), ?_⟩
  intro g z
  rfl

/-- **Milne, Proposition 2.1 (c).** The stabilizer of `i` in `SL₂(ℝ)` is `SO₂(ℝ)`. -/
@[kb "milne2017mf" "Proposition 2.1 (c), pdf p. 25"]
theorem stabilizer_I_eq_SO2R : MulAction.stabilizer SL(2, ℝ) UpperHalfPlane.I = SO2R := by
  ext k
  rw [MulAction.mem_stabilizer_iff]
  have hmem : k ∈ SO2R ↔ ∃ θ, Matrix.SpecialLinearGroup.rotation θ = k := by
    unfold SO2R
    exact Iff.rfl
  rw [hmem]
  constructor
  · intro hk
    have h1 := Matrix.SpecialLinearGroup.sq_add_sq_eq_one_of_smul_I_eq_I hk
    obtain ⟨h11, h10⟩ := (Matrix.SpecialLinearGroup.smul_I_eq_I_iff k).1 hk
    set w : ℂ := ⟨k 0 0, k 0 1⟩ with hw
    have hn : ‖w‖ = 1 := by
      rw [Complex.norm_def, Complex.normSq_apply]
      simp [hw]
      nlinarith
    refine ⟨Complex.arg w, ?_⟩
    have hc : Real.cos (Complex.arg w) = k 0 0 := by
      rw [Complex.cos_arg (by intro h; rw [h] at hn; simp at hn), hn]; simp [hw]
    have hs : Real.sin (Complex.arg w) = k 0 1 := by
      rw [Complex.sin_arg, hn]; simp [hw]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc, hs, h11, h10]
  · rintro ⟨θ, rfl⟩
    exact TauCeti.UpperHalfPlane.rotation_smul_I θ

/-- `SL₂(ℝ)` is locally compact (a closed subset of the matrices). -/
instance instLocallyCompactSpaceSL2R : LocallyCompactSpace SL(2, ℝ) := by
  have hcl : IsClosed {A : Matrix (Fin 2) (Fin 2) ℝ | A.det = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  exact (hcl.isClosedEmbedding_subtypeVal).locallyCompactSpace

/-- `SL₂(ℝ)` is second countable (a subspace of the matrices). -/
instance instSecondCountableTopologySL2R : SecondCountableTopology SL(2, ℝ) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

/-- **Milne, Proposition 2.1 (d).** The map `SL₂(ℝ)/SO₂(ℝ) → ℍ`, `α SO₂(ℝ) ↦ α(i)`, is a homeomorphism. -/
@[kb "milne2017mf" "Proposition 2.1 (d), pdf p. 25"]
theorem exists_homeomorph_quotient_SO2R :
    ∃ e : SL(2, ℝ) ⧸ SO2R ≃ₜ ℍ, ∀ g : SL(2, ℝ), e (g : SL(2, ℝ) ⧸ SO2R) = g • UpperHalfPlane.I := by
  have h := exists_homeomorph_quotient_stabilizer (G := SL(2, ℝ)) (X := ℍ) UpperHalfPlane.I
  rw [stabilizer_I_eq_SO2R] at h
  exact h

/-! ### Exercise 2.3 -/

/-- The hermitian form `ψ((z₁, z₂), (w₁, w₂)) = z̄₁ w₁ - z̄₂ w₂` on `ℂ²` (Milne, Exercise 2.3). -/
@[kb "milne2017mf" "Exercise 2.3, the hermitian form psi, pdf p. 26"]
def herm11 (z w : Fin 2 → ℂ) : ℂ := conj (z 0) * w 0 - conj (z 1) * w 1

/-- **`SU(1,1)`** (Milne, Exercise 2.3): the elements `α ∈ SL₂(ℂ)` with `ψ(αz, αw) = ψ(z, w)`. -/
@[kb "milne2017mf" "Exercise 2.3, definition of SU(1,1), pdf p. 26"]
def SU11 : Subgroup SL(2, ℂ) where
  carrier := {α | ∀ z w : Fin 2 → ℂ,
    herm11 ((α : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ z) ((α : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ w) = herm11 z w}
  mul_mem' := by
    intro a b ha hb z w
    simp only [Set.mem_ofPred_eq] at *
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, hb]
  one_mem' := by intro z w; simp
  inv_mem' := by
    intro a ha z w
    simp only [Set.mem_ofPred_eq] at *
    have h := ha ((a⁻¹ : SL(2, ℂ)) *ᵥ z) ((a⁻¹ : SL(2, ℂ)) *ᵥ w)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, Matrix.one_mulVec] at h
    exact h.symm

/-- **Milne, Exercise 2.3 (a).** `SU(1,1) = { !![u, v; v̄, ū] | |u|² - |v|² = 1 }`. -/
@[kb "milne2017mf" "Exercise 2.3 (a), pdf p. 26"]
theorem mem_SU11_iff (α : SL(2, ℂ)) :
    α ∈ SU11 ↔ ∃ u v : ℂ, normSq u - normSq v = 1 ∧
      (α : Matrix (Fin 2) (Fin 2) ℂ) = !![u, v; conj v, conj u] := by
  constructor
  · intro h
    have hdet := α.2
    rw [Matrix.det_fin_two] at hdet
    have e00 := h ![1, 0] ![1, 0]
    have e11 := h ![0, 1] ![0, 1]
    have e01 := h ![1, 0] ![0, 1]
    simp [herm11, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e00 e11 e01
    have hα : (α : Matrix (Fin 2) (Fin 2) ℂ) = !![(α : Matrix (Fin 2) (Fin 2) ℂ) 0 0,
        (α : Matrix (Fin 2) (Fin 2) ℂ) 0 1; (α : Matrix (Fin 2) (Fin 2) ℂ) 1 0,
        (α : Matrix (Fin 2) (Fin 2) ℂ) 1 1] := (Matrix.eta_fin_two _)
    generalize (α : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = a at *
    generalize (α : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = b at *
    generalize (α : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = c at *
    generalize (α : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = d at *
    have e01' := congrArg conj e01
    simp only [map_sub, map_mul, Complex.conj_conj, map_zero] at e01'
    have hd : conj a = d := by
      linear_combination (-(conj a)) * hdet + d * e00 - c * e01
    have hc : conj b = c := by
      linear_combination (-(conj b)) * hdet + d * e01' - c * e11
    subst hd
    subst hc
    simp only [Complex.conj_conj] at e11
    refine ⟨a, b, ?_, hα⟩
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_sub, Complex.normSq_eq_conj_mul_self, Complex.ofReal_one]
    linear_combination -e11
  · rintro ⟨u, v, huv, hα⟩ z w
    have hu : (normSq u : ℂ) - normSq v = 1 := by exact_mod_cast huv
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self] at hu
    simp only [herm11, hα, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, map_add, map_mul, Complex.conj_conj]
    linear_combination (conj (z 0) * w 0 - conj (z 1) * w 1) * hu

namespace SU11Aux

/-- entries of an `SU(1,1)` element -/
theorem su11_spec (α : SU11) :
    normSq ((α : Matrix (Fin 2) (Fin 2) ℂ) 0 0) - normSq ((α : Matrix (Fin 2) (Fin 2) ℂ) 0 1) = 1 ∧
    (α : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = conj ((α : Matrix (Fin 2) (Fin 2) ℂ) 0 1) ∧
    (α : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = conj ((α : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
  obtain ⟨u, v, huv, hα⟩ := (mem_SU11_iff _).1 α.2
  have h00 := congrFun (congrFun hα 0) 0
  have h01 := congrFun (congrFun hα 0) 1
  have h10 := congrFun (congrFun hα 1) 0
  have h11 := congrFun (congrFun hα 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h01 h10 h11
  rw [h00, h01, h10, h11]
  exact ⟨huv, rfl, rfl⟩

/-- Build an element of `SU(1,1)` from `u, v`. -/
noncomputable def su11Mk (u v : ℂ) (h : normSq u - normSq v = 1) : SU11 :=
  ⟨⟨!![u, v; conj v, conj u], by
    rw [Matrix.det_fin_two_of]
    have := congrArg (fun r : ℝ => (r : ℂ)) h
    simp only [Complex.normSq_eq_conj_mul_self, Complex.ofReal_sub, Complex.ofReal_one] at this
    linear_combination this⟩, (mem_SU11_iff _).2 ⟨u, v, h, rfl⟩⟩

theorem norm_lt_of_normSq {u v : ℂ} (h : normSq u - normSq v = 1) : ‖v‖ < ‖u‖ := by
  have h1 : ‖v‖ ^ 2 < ‖u‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]; linarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1

theorem ne_zero_of_normSq {u v : ℂ} (h : normSq u - normSq v = 1) : u ≠ 0 := by
  intro hu
  rw [hu] at h
  simp at h
  linarith [normSq_nonneg v]

theorem den_ne_zero {u v : ℂ} (h : normSq u - normSq v = 1) (z : Complex.UnitDisc) :
    conj v * (z : ℂ) + conj u ≠ 0 := by
  intro h0
  have h1 : ‖conj u‖ = ‖conj v * (z : ℂ)‖ := by
    rw [← neg_eq_of_add_eq_zero_right h0, norm_neg]
  rw [Complex.norm_conj, norm_mul, Complex.norm_conj] at h1
  have := norm_lt_of_normSq h
  have hz := z.norm_lt_one
  nlinarith [norm_nonneg v, norm_nonneg (z : ℂ)]

/-- A circle element from a norm-one complex number. -/
def circOf (w : ℂ) (hw : ‖w‖ = 1) : Circle := ⟨w, mem_sphere_zero_iff_norm.2 hw⟩

@[simp] theorem coe_circOf (w : ℂ) (hw : ‖w‖ = 1) : (circOf w hw : ℂ) = w := rfl

/-- The disc automorphism of `!![u, v; v̄, ū]`. -/
noncomputable def su11Std (u v : ℂ) (h : normSq u - normSq v = 1) : Equiv.Perm Complex.UnitDisc :=
  TauCeti.unitDiscStandardAutomorphismEquiv
    (circOf (u / conj u) (by
      have := ne_zero_of_normSq h
      rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 this)]))
    (Complex.UnitDisc.mk (-v / u) (by
      have := ne_zero_of_normSq h
      rw [norm_div, norm_neg, div_lt_one (norm_pos_iff.2 this)]
      exact norm_lt_of_normSq h))

theorem su11Std_apply (u v : ℂ) (h : normSq u - normSq v = 1) (z : Complex.UnitDisc) :
    (su11Std u v h z : ℂ) = (u * z + v) / (conj v * z + conj u) := by
  have hu := ne_zero_of_normSq h
  have hu' : conj u ≠ 0 := by simpa using hu
  have hden := den_ne_zero h z
  unfold su11Std
  rw [TauCeti.coe_unitDiscStandardAutomorphismEquiv_apply]
  simp only [Complex.UnitDisc.coe_mk, map_neg, map_div₀, coe_circOf]
  have h2 : 1 - -conj v / conj u * (z : ℂ) ≠ 0 := by
    intro h3
    apply hden
    field_simp at h3
    linear_combination h3
  field_simp
  ring

noncomputable def su11Perm (α : SU11) : Equiv.Perm Complex.UnitDisc :=
  su11Std _ _ (su11_spec α).1

theorem su11Perm_apply (α : SU11) (z : Complex.UnitDisc) :
    (su11Perm α z : ℂ) =
      ((α : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * z + (α : Matrix (Fin 2) (Fin 2) ℂ) 0 1) /
        ((α : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * z + (α : Matrix (Fin 2) (Fin 2) ℂ) 1 1) := by
  obtain ⟨-, h10, h11⟩ := su11_spec α
  rw [h10, h11]
  exact su11Std_apply _ _ _ z

theorem den_ne (α : SU11) (z : Complex.UnitDisc) :
    (α : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * z + (α : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := by
  obtain ⟨h, h10, h11⟩ := su11_spec α
  rw [h10, h11]
  exact den_ne_zero h z

theorem moeb_comp (a b c d a' b' c' d' z : ℂ) (h1 : c' * z + d' ≠ 0)
    (h3 : (c * a' + d * c') * z + (c * b' + d * d') ≠ 0) :
    ((a * a' + b * c') * z + (a * b' + b * d')) / ((c * a' + d * c') * z + (c * b' + d * d')) =
      (a * ((a' * z + b') / (c' * z + d')) + b) / (c * ((a' * z + b') / (c' * z + d')) + d) := by
  have h2 : c * ((a' * z + b') / (c' * z + d')) + d =
      ((c * a' + d * c') * z + (c * b' + d * d')) / (c' * z + d') := by
    have : (a' * z + b') / (c' * z + d') * (c' * z + d') = a' * z + b' := div_mul_cancel₀ _ h1
    rw [eq_div_iff h1]
    linear_combination c * this
  rw [h2]
  field_simp
  ring

theorem su11Perm_mul (α β : SU11) : su11Perm (α * β) = su11Perm α * su11Perm β := by
  refine Equiv.ext fun z => Complex.UnitDisc.coe_injective ?_
  rw [Equiv.Perm.mul_apply, su11Perm_apply (α * β) z, su11Perm_apply α (su11Perm β z),
    su11Perm_apply β z]
  have h3 := den_ne (α * β) z
  simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two] at h3 ⊢
  exact moeb_comp _ _ _ _ _ _ _ _ _ (den_ne β z) h3

theorem su11Perm_one : su11Perm 1 = 1 := by
  refine Equiv.ext fun z => Complex.UnitDisc.coe_injective ?_
  rw [su11Perm_apply]
  simp

theorem comm_entry (α β : SU11) (h : β * α = α * β) (i j : Fin 2) :
    ∑ k, (β : Matrix (Fin 2) (Fin 2) ℂ) i k * (α : Matrix (Fin 2) (Fin 2) ℂ) k j =
      ∑ k, (α : Matrix (Fin 2) (Fin 2) ℂ) i k * (β : Matrix (Fin 2) (Fin 2) ℂ) k j := by
  have := congrArg (fun γ : SU11 => ((γ : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) i j) h
  simp only [Subgroup.coe_mul] at this
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at this
  simpa only [Matrix.mul_apply] using this

theorem su11_pm (α : SU11) (hb : (α : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0)
    (hd : (α : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = (α : Matrix (Fin 2) (Fin 2) ℂ) 0 0) :
    (α : SL(2, ℂ)) = 1 ∨ (α : SL(2, ℂ)) = -1 := by
  obtain ⟨hn, h10, h11⟩ := su11_spec α
  have hc : (α : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by rw [h10, hb]; simp
  have h1 : (normSq ((α : Matrix (Fin 2) (Fin 2) ℂ) 0 0) : ℂ) = 1 := by
    rw [hb] at hn; simpa using hn
  rw [Complex.normSq_eq_conj_mul_self] at h1
  have hca : conj ((α : Matrix (Fin 2) (Fin 2) ℂ) 0 0) = (α : Matrix (Fin 2) (Fin 2) ℂ) 0 0 :=
    h11.symm.trans hd
  rw [hca] at h1
  have h3 : ((α : Matrix (Fin 2) (Fin 2) ℂ) 0 0 - 1) *
      ((α : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + 1) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 h3 with h4 | h4
  · left
    have h5 : (α : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 1 := by linear_combination h4
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, hd, h5]
  · right
    have h5 : (α : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = -1 := by linear_combination h4
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, hd, h5]

theorem su11_center_iff (α : SU11) :
    α ∈ Subgroup.center SU11 ↔ (α : SL(2, ℂ)) = 1 ∨ (α : SL(2, ℂ)) = -1 := by
  constructor
  · intro h
    rw [Subgroup.mem_center_iff] at h
    obtain ⟨hn, h10, h11⟩ := su11_spec α
    have hb : (α : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
      have := comm_entry α (su11Mk Complex.I 0 (by simp)) (h _) 0 1
      simp [su11Mk, Fin.sum_univ_two] at this
      have h2 : (2 * Complex.I) * (α : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
        linear_combination this
      exact (mul_eq_zero.1 h2).resolve_left (by simp)
    have hd : (α : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = (α : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
      have h2 := comm_entry α (su11Mk (5 / 3) (4 / 3) (by
        simp [Complex.normSq_apply]; norm_num)) (h _) 0 1
      simp [su11Mk, Fin.sum_univ_two, hb] at h2
      linear_combination (3 / 4) * h2
    exact su11_pm α hb hd
  · rintro (h | h)
    · rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, h]
      simp
    · rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, h]
      simp

/-- The homomorphism `SU(1,1) → Aut(D)`. -/
noncomputable def su11Hom : SU11 →* TauCeti.unitDiscAut where
  toFun α := ⟨su11Perm α, TauCeti.unitDiscStandardAutomorphismEquiv_mem_unitDiscAut _ _⟩
  map_one' := Subtype.ext su11Perm_one
  map_mul' α β := Subtype.ext (su11Perm_mul α β)

theorem su11Hom_apply (α : SU11) : (su11Hom α : Equiv.Perm Complex.UnitDisc) = su11Perm α := rfl

theorem su11Hom_eq_one_iff (α : SU11) : su11Hom α = 1 ↔ α ∈ Subgroup.center SU11 := by
  rw [su11_center_iff]
  have hz : su11Hom α = 1 ↔ su11Perm α = 1 :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [hz]
  constructor
  · intro hp
    have hf : ∀ z : Complex.UnitDisc,
        (α : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * z + (α : Matrix (Fin 2) (Fin 2) ℂ) 0 1 =
          z * ((α : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * z + (α : Matrix (Fin 2) (Fin 2) ℂ) 1 1) := by
      intro z
      have := su11Perm_apply α z
      rw [hp, Equiv.Perm.one_apply, eq_div_iff (den_ne α z)] at this
      linear_combination -this
    have hb : (α : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
      simpa using hf 0
    obtain ⟨hn, h10, h11⟩ := su11_spec α
    have hc : (α : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by rw [h10, hb]; simp
    have h2 := hf (Complex.UnitDisc.mk (1 / 2) (by simp; norm_num))
    simp only [Complex.UnitDisc.coe_mk, hb, hc] at h2
    have hd : (α : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = (α : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
      linear_combination -2 * h2
    exact su11_pm α hb hd
  · rintro (h | h)
    · refine Equiv.ext fun z => Complex.UnitDisc.coe_injective ?_
      rw [su11Perm_apply, h]
      simp
    · refine Equiv.ext fun z => Complex.UnitDisc.coe_injective ?_
      rw [su11Perm_apply, h]
      simp

theorem su11Hom_surjective : Function.Surjective su11Hom := by
  rintro ⟨e, he⟩
  obtain ⟨u, a, rfl⟩ := TauCeti.mem_unitDiscAut_iff.1 he
  have ha := a.norm_lt_one
  have hδ : 0 < 1 - normSq (a : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (a : ℂ)]
  set δ := 1 - normSq (a : ℂ) with hδdef
  set r : ℝ := (Real.sqrt δ)⁻¹ with hr
  have hr2 : r ^ 2 = δ⁻¹ := by
    rw [hr, inv_pow, Real.sq_sqrt hδ.le]
  set s : ℂ := Complex.exp (((Complex.arg (u : ℂ) / 2 : ℝ) : ℂ) * Complex.I) with hs
  have hsn : ‖s‖ = 1 := by
    rw [hs, Complex.norm_exp_ofReal_mul_I]
  have hsc : conj s = s⁻¹ := by
    rw [hs, ← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [← Complex.exp_neg]
    congr 1
    ring
  have hss : s / conj s = (u : ℂ) := by
    rw [hsc, div_inv_eq_mul, hs, ← Complex.exp_add, ← two_mul]
    have h1 : (2 * (((Complex.arg (u : ℂ) / 2 : ℝ) : ℂ) * Complex.I)) =
        (Complex.arg (u : ℂ) : ℂ) * Complex.I := by push_cast; ring
    rw [h1]
    have := Complex.norm_mul_exp_arg_mul_I (u : ℂ)
    rwa [Circle.norm_coe, Complex.ofReal_one, one_mul] at this
  have hs0 : s ≠ 0 := norm_ne_zero_iff.1 (by rw [hsn]; exact one_ne_zero)
  have hr0 : (r : ℂ) ≠ 0 := by
    have : 0 < r := inv_pos.2 (Real.sqrt_pos.2 hδ)
    exact_mod_cast this.ne'
  have hnorm : normSq (s * r) - normSq (-(a : ℂ) * (s * r)) = 1 := by
    have hn : normSq s = 1 := by rw [Complex.normSq_eq_norm_sq, hsn]; norm_num
    have hn1 : normSq (s * r) = r * r := by
      rw [map_mul, hn, Complex.normSq_ofReal, one_mul]
    have hn2 : normSq (-(a : ℂ) * (s * r)) = normSq (a : ℂ) * (r * r) := by
      rw [map_mul, Complex.normSq_neg, hn1]
    rw [hn1, hn2]
    have h3 : r * r = δ⁻¹ := by rw [← sq]; exact hr2
    have : (r * r - normSq (a : ℂ) * (r * r)) = δ * (r * r) := by rw [hδdef]; ring
    rw [this, h3]; field_simp
  refine ⟨su11Mk _ _ hnorm, Subtype.ext ?_⟩
  show su11Perm _ = _
  unfold su11Perm su11Std
  congr 1
  · apply Subtype.ext
    simp only [su11Mk, coe_circOf, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [map_mul, Complex.conj_ofReal, mul_div_mul_right _ _ hr0, hss]
  · apply Complex.UnitDisc.coe_injective
    simp only [su11Mk, Complex.UnitDisc.coe_mk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    field_simp

end SU11Aux

/-- **Milne, Exercise 2.3 (b).** `!![u, v; v̄, ū] · z = (uz + v)/(v̄z + ū)` defines an action of `SU(1,1)` on the
unit disk inducing an isomorphism `SU(1,1)/{±I} ≅ Aut(D)`. -/
@[kb "milne2017mf" "Exercise 2.3 (b), pdf p. 26"]
theorem exists_mulEquiv_unitDiscAut :
    ∃ φ : SU11 ⧸ Subgroup.center SU11 ≃* TauCeti.unitDiscAut,
      ∀ (α : SU11) (z : Complex.UnitDisc),
        ((φ (α : SU11 ⧸ Subgroup.center SU11) : Equiv.Perm Complex.UnitDisc) z : ℂ) =
          ((α : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * z + (α : Matrix (Fin 2) (Fin 2) ℂ) 0 1) /
            ((α : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * z + (α : Matrix (Fin 2) (Fin 2) ℂ) 1 1) := by
  have hker : Subgroup.center SU11 = SU11Aux.su11Hom.ker := by
    ext α
    rw [MonoidHom.mem_ker, SU11Aux.su11Hom_eq_one_iff]
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ SU11Aux.su11Hom_surjective), ?_⟩
  intro α z
  exact SU11Aux.su11Perm_apply α z

/-- The centre of `SU(1,1)` is `{±I}`, the subgroup appearing in Exercise 2.3 (b). -/
@[kb "milne2017mf" "Exercise 2.3 (b): the kernel {±I}, pdf p. 26"]
theorem mem_center_SU11_iff (α : SU11) :
    α ∈ Subgroup.center SU11 ↔ (α : SL(2, ℂ)) = 1 ∨ (α : SL(2, ℂ)) = -1 :=
  SU11Aux.su11_center_iff α

end ModularFormsKB.Milne
