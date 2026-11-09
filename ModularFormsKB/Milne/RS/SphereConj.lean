import ModularFormsKB.Milne.RiemannSurface.Results
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Complex conjugation on the Riemann sphere

Complex conjugation `σ` of `OnePoint ℂ` is a homeomorphism that is anti-holomorphic. Conjugating a holomorphic
self-map of the sphere by `σ` gives a holomorphic map again, so `g ↦ σ ∘ g ∘ σ` is a ring automorphism `conjAut`
of the field of meromorphic functions on the sphere. It is not `ℂ`-linear.

Finally `no_conj_algHom` shows that no `ℂ`-algebra endomorphism of `M(ℙ¹)` can carry functions holomorphic at
`σ x` to functions holomorphic at `x`: such a map would force `ψ coordinate` to be `z ↦ conj z` on `ℂ`, which is
not holomorphic.

This file supports a counterexample to the named statement
`ModularFormsKB.RiemannSurfaceAlgebraicStructure (OnePoint ℂ)` (Milne, Theorem 7.5), whose uniqueness clause does
not require the field isomorphism to be `ℂ`-linear.
-/

open TauCeti.RiemannSurface OnePoint ComplexConjugate
open scoped Manifold

namespace ModularFormsKB.Milne.RS

/-- Complex conjugation on the Riemann sphere. -/
noncomputable def sphereConj (x : OnePoint ℂ) : OnePoint ℂ := OnePoint.map (starRingEnd ℂ) x

@[simp] theorem sphereConj_coe (z : ℂ) : sphereConj (z : OnePoint ℂ) = ((conj z : ℂ) : OnePoint ℂ) := rfl

@[simp] theorem sphereConj_infty : sphereConj ∞ = ∞ := rfl

@[simp] theorem sphereConj_sphereConj (x : OnePoint ℂ) : sphereConj (sphereConj x) = x := by
  induction x using OnePoint.rec <;> simp

theorem continuous_sphereConj : Continuous sphereConj :=
  (Homeomorph.onePointCongr Complex.conjCLE.toHomeomorph).continuous

/-- Complex conjugation on the Riemann sphere, as an equivalence. -/
noncomputable def sphereConjEquiv : OnePoint ℂ ≃ OnePoint ℂ where
  toFun := sphereConj
  invFun := sphereConj
  left_inv := sphereConj_sphereConj
  right_inv := sphereConj_sphereConj

/-! ### Charts and conjugation -/

theorem chartAt_sphereConj (y : OnePoint ℂ) : chartAt ℂ (sphereConj y) = chartAt ℂ y := by
  induction y using OnePoint.rec <;> simp

theorem chartAt_apply_sphereConj (y w : OnePoint ℂ) :
    chartAt ℂ y (sphereConj w) = conj (chartAt ℂ y w) := by
  induction y using OnePoint.rec <;> induction w using OnePoint.rec <;> simp [map_inv₀]

theorem chartAt_symm_conj (y : OnePoint ℂ) (v : ℂ) :
    (chartAt ℂ y).symm (conj v) = sphereConj ((chartAt ℂ y).symm v) := by
  induction y using OnePoint.rec with
  | infty =>
    by_cases hv : v = 0
    · simp [hv]
    · have : conj v ≠ 0 := by simpa using hv
      simp [hv, this, map_inv₀]
  | coe z => simp

/-- Conjugating a holomorphic self-map of the sphere by `σ` gives a holomorphic map. -/
theorem mdifferentiable_sphereConj_comp {g : OnePoint ℂ → OnePoint ℂ}
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x ↦ sphereConj (g (sphereConj x))) := by
  intro x
  rw [mdifferentiableAt_iff]
  refine ⟨continuous_sphereConj.continuousAt.comp
    ((hg.continuous.comp continuous_sphereConj).continuousAt), ?_⟩
  have h := ((mdifferentiableAt_iff _ _).1 (hg (sphereConj x))).2
  simp only [modelWithCornersSelf_coe, differentiableWithinAt_univ,
    mfld_simps] at h ⊢
  have h2 := DifferentiableAt.conj_conj h
  have e1 : (chartAt ℂ x x) = conj (chartAt ℂ (sphereConj x) (sphereConj x)) := by
    rw [chartAt_sphereConj, ← chartAt_apply_sphereConj]; simp
  have e2 : (fun v ↦ chartAt ℂ (sphereConj (g (sphereConj x)))
      (sphereConj (g (sphereConj ((chartAt ℂ x).symm v))))) =
      conj ∘ (fun v ↦ chartAt ℂ (g (sphereConj x)) (g ((chartAt ℂ (sphereConj x)).symm v))) ∘ conj := by
    funext v
    simp only [Function.comp_apply, chartAt_sphereConj, chartAt_apply_sphereConj]
    rw [chartAt_symm_conj, ← chartAt_sphereConj x, chartAt_sphereConj]
  have e3 : (↑(chartAt ℂ (sphereConj (g (sphereConj x)))) ∘ (fun x => sphereConj (g (sphereConj x))) ∘
      ↑(chartAt ℂ x).symm : ℂ → ℂ) = _ := e2
  rw [e3, e1]
  exact h2

/-! ### The conjugation automorphism of the function field -/

theorem sphereConj_eq_infty_iff {x : OnePoint ℂ} : sphereConj x = ∞ ↔ x = ∞ := by
  induction x using OnePoint.rec <;> simp

/-- The underlying meromorphic function of `σ ∘ g ∘ σ`. -/
noncomputable def conjFun (g : MeromorphicFunction (OnePoint ℂ)) : MeromorphicFunction (OnePoint ℂ) where
  toFun x := sphereConj (g (sphereConj x))
  mdifferentiable' := mdifferentiable_sphereConj_comp g.mdifferentiable
  ne_infty' h := by
    refine g.ne_infty' (funext fun y ↦ ?_)
    have := congrFun h (sphereConj y)
    change g y = ∞
    simpa [sphereConj_eq_infty_iff] using this

@[simp] theorem conjFun_apply (g : MeromorphicFunction (OnePoint ℂ)) (x : OnePoint ℂ) :
    conjFun g x = sphereConj (g (sphereConj x)) := rfl

theorem conjFun_conjFun (g : MeromorphicFunction (OnePoint ℂ)) : conjFun (conjFun g) = g := by
  ext x; simp

theorem conjFun_finitePart {g : MeromorphicFunction (OnePoint ℂ)} {x : OnePoint ℂ}
    (h : g (sphereConj x) ≠ ∞) : (conjFun g).finitePart x = conj (g.finitePart (sphereConj x)) := by
  apply MeromorphicFunction.finitePart_of_eq_coe
  rw [conjFun_apply, ← MeromorphicFunction.coe_finitePart h]
  rfl

theorem conjFun_add (f g : MeromorphicFunction (OnePoint ℂ)) :
    conjFun (f + g) = conjFun f + conjFun g := by
  rw [MeromorphicFunction.eq_add_iff]
  intro x hf hg
  have hf' : f (sphereConj x) ≠ ∞ := fun h ↦ hf (by simp [h])
  have hg' : g (sphereConj x) ≠ ∞ := fun h ↦ hg (by simp [h])
  rw [conjFun_finitePart hf', conjFun_finitePart hg', conjFun_apply,
    MeromorphicFunction.add_apply hf' hg']
  simp

theorem conjFun_mul (f g : MeromorphicFunction (OnePoint ℂ)) :
    conjFun (f * g) = conjFun f * conjFun g := by
  rw [MeromorphicFunction.eq_mul_iff]
  intro x hf hg
  have hf' : f (sphereConj x) ≠ ∞ := fun h ↦ hf (by simp [h])
  have hg' : g (sphereConj x) ≠ ∞ := fun h ↦ hg (by simp [h])
  rw [conjFun_finitePart hf', conjFun_finitePart hg', conjFun_apply,
    MeromorphicFunction.mul_apply hf' hg']
  simp

/-- The conjugation automorphism `g ↦ σ ∘ g ∘ σ` of the field of meromorphic functions on the sphere
(a ring automorphism, not ℂ-linear). -/
noncomputable def conjAut : MeromorphicFunction (OnePoint ℂ) ≃+* MeromorphicFunction (OnePoint ℂ) where
  toFun := conjFun
  invFun := conjFun
  left_inv := conjFun_conjFun
  right_inv := conjFun_conjFun
  map_mul' := conjFun_mul
  map_add' := conjFun_add

theorem conjAut_apply (g : MeromorphicFunction (OnePoint ℂ)) (x : OnePoint ℂ) :
    conjAut g x = sphereConj (g (sphereConj x)) := rfl

/-! ### No `ℂ`-algebra endomorphism is conjugation-compatible -/

/-- Complex conjugation is not complex differentiable. -/
theorem not_differentiableAt_conj : ¬ DifferentiableAt ℂ (starRingEnd ℂ) 0 := by
  intro h
  have h1 : HasFDerivAt (starRingEnd ℂ) (fderiv ℂ (starRingEnd ℂ) 0) 0 := h.hasFDerivAt
  have h2 := h1.restrictScalars ℝ
  have h3 : HasFDerivAt (starRingEnd ℂ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) 0 :=
    Complex.conjCLE.hasFDerivAt
  have h4 := h2.unique h3
  set L := fderiv ℂ (starRingEnd ℂ) 0
  have e1 : L 1 = 1 := by
    have := congrArg (fun T : ℂ →L[ℝ] ℂ ↦ T 1) h4
    simpa using this
  have e2 : L Complex.I = -Complex.I := by
    have := congrArg (fun T : ℂ →L[ℝ] ℂ ↦ T Complex.I) h4
    simpa using this
  have e3 : L Complex.I = Complex.I := by
    have : L (Complex.I • (1 : ℂ)) = Complex.I • L 1 := L.map_smul Complex.I 1
    simpa [e1] using this
  have : Complex.I = -Complex.I := e3.symm.trans e2
  have h5 : (2 : ℂ) * Complex.I = 0 := by linear_combination this
  simp at h5

/-- No ℂ-algebra endomorphism of `M(ℙ¹)` carries functions holomorphic at `σ x` to functions holomorphic
at `x`. -/
theorem no_conj_algHom (ψ : MeromorphicFunction (OnePoint ℂ) →ₐ[ℂ] MeromorphicFunction (OnePoint ℂ))
    (hψ : ∀ (g : MeromorphicFunction (OnePoint ℂ)) (x : OnePoint ℂ), g (sphereConj x) ≠ ∞ →
      ψ g x ≠ ∞) : False := by
  set c := (MeromorphicFunction.coordinate : MeromorphicFunction (OnePoint ℂ)) with hc
  have hcv : ∀ x : ℂ, c (sphereConj (x : OnePoint ℂ)) = ((conj x : ℂ) : OnePoint ℂ) := by
    intro x; simp [hc]
  -- Step 1: `ψ c` is conjugation on `ℂ`.
  have step1 : ∀ x : ℂ, ψ c (x : OnePoint ℂ) = ((conj x : ℂ) : OnePoint ℂ) := by
    intro x
    have hfin : ψ c (x : OnePoint ℂ) ≠ ∞ :=
      hψ c _ (by rw [hcv]; exact OnePoint.coe_ne_infty _)
    obtain ⟨a, ha⟩ := OnePoint.ne_infty_iff_exists.1 hfin
    by_contra hne
    have hax : a ≠ conj x := fun h ↦ hne (by rw [← ha, h])
    set u : MeromorphicFunction (OnePoint ℂ) := c - algebraMap ℂ _ a with hu
    have hu_val : u (sphereConj (x : OnePoint ℂ)) = ((conj x - a : ℂ) : OnePoint ℂ) := by
      rw [hu]
      exact MeromorphicFunction.sub_apply_of_eq_coe (hcv x) (by simp)
    have hsub : conj x - a ≠ 0 := sub_ne_zero.2 (Ne.symm hax)
    have hu0 : u ≠ 0 := by
      intro h0
      have := hu_val
      rw [h0] at this
      simp only [MeromorphicFunction.coe_zero] at this
      exact hsub (OnePoint.coe_injective this).symm
    have hinv : (u⁻¹) (sphereConj (x : OnePoint ℂ)) ≠ ∞ := by
      rw [MeromorphicFunction.inv_apply_of_eq_coe hu_val hsub]
      exact OnePoint.coe_ne_infty _
    have h1 := hψ _ _ hinv
    have hψu : ψ u = ψ c - algebraMap ℂ _ a := by
      rw [hu, map_sub, AlgHom.commutes]
    have hψu_ne : ψ u ≠ 0 := (map_ne_zero ψ).2 hu0
    have hψu_val : (ψ u) (x : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) := by
      rw [hψu]
      have := MeromorphicFunction.sub_apply_of_eq_coe (f := ψ c) (g := algebraMap ℂ _ a) (a := a) (b := a)
        (x := (x : OnePoint ℂ)) ha.symm (by simp)
      simpa using this
    rw [map_inv₀] at h1
    have hprod := congrArg (fun k : MeromorphicFunction (OnePoint ℂ) ↦ k (x : OnePoint ℂ))
      (mul_inv_cancel₀ hψu_ne)
    obtain ⟨b, hb⟩ := OnePoint.ne_infty_iff_exists.1 h1
    rw [MeromorphicFunction.mul_apply_of_eq_coe hψu_val hb.symm] at hprod
    simp at hprod
  -- Step 2: contradiction with non-differentiability of conjugation.
  have hne : (ψ c) ((0 : ℂ) : OnePoint ℂ) ≠ ∞ := by
    rw [step1]; exact OnePoint.coe_ne_infty _
  have hd := (OnePoint.mdifferentiableAt_iff_of_ne_infty hne).1 ((ψ c).mdifferentiable _) |>.2
  have hd2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (OnePoint.affineChart ∘ (ψ c) ∘ ((↑) : ℂ → OnePoint ℂ)) 0 :=
    MDifferentiableAt.comp (I' := 𝓘(ℂ)) (f := ((↑) : ℂ → OnePoint ℂ)) (g := OnePoint.affineChart ∘ (ψ c)) 0 hd
      ((OnePoint.contMDiff_coe.mdifferentiable (by simp)) 0)
  have hfun : (OnePoint.affineChart ∘ (ψ c) ∘ ((↑) : ℂ → OnePoint ℂ) : ℂ → ℂ) = starRingEnd ℂ := by
    funext z; simp [step1]
  rw [hfun, mdifferentiableAt_iff_differentiableAt] at hd2
  exact not_differentiableAt_conj hd2

end ModularFormsKB.Milne.RS
