import ModularFormsKB.Milne.Ch0.Introduction

/-!
# Milne, Proposition 0.4: the points of a nonsingular affine plane curve form a Riemann surface

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Proposition 0.4, pdf p. 8.

Let `C : f(X, Y) = 0` be a nonsingular affine plane curve over `ℂ`. At a point `P` of `C(ℂ)` with
`(∂f/∂Y)(P) ≠ 0` the map `Φ(x, y) = (x, f(x, y))` has invertible derivative, so by the inverse function theorem
(Mathlib's `HasStrictFDerivAt.toOpenPartialHomeomorph`) it is a local homeomorphism `Ψ` near `P`, with smooth
inverse (`OpenPartialHomeomorph.contDiffAt_symm`) once restricted to the open set where `∂f/∂Y ≠ 0`. Then
`Q ↦ Q.1` is a chart of `C(ℂ)` near `P`, with inverse `x ↦ Ψ⁻¹(x, 0)`. At a point with `(∂f/∂Y)(P) = 0` the
nonsingularity gives `(∂f/∂X)(P) ≠ 0`, and `Φ(x, y) = (y, f(x, y))` and the chart `Q ↦ Q.2` are used instead. A
transition map is `x ↦ π'(Ψ⁻¹(x, 0))` with `π'` a coordinate projection, which is smooth: this is the holomorphic
implicit function theorem in the form used by the book.

Main result: `planeCurveRiemannSurfaceStatement`, the named statement `PlaneCurveRiemannSurfaceStatement`.

Indices: `pderiv 0` is `∂/∂X`, `pderiv 1` is `∂/∂Y`.
-/

open MvPolynomial Set Topology Filter
open scoped Manifold

namespace ModularFormsKB.Milne.RS

/-! ### Polynomial functions on `ℂ²` -/

/-- The polynomial function `q ↦ p(q.1, q.2)` on `ℂ²`. -/
noncomputable def ev (p : MvPolynomial (Fin 2) ℂ) (q : ℂ × ℂ) : ℂ := aeval ![q.1, q.2] p

/-- The derivative of `ev p` at `q`: `(u, v) ↦ (∂p/∂X)(q) u + (∂p/∂Y)(q) v`. -/
noncomputable def evDeriv (p : MvPolynomial (Fin 2) ℂ) (q : ℂ × ℂ) : (ℂ × ℂ) →L[ℂ] ℂ :=
  ev (pderiv 0 p) q • ContinuousLinearMap.fst ℂ ℂ ℂ + ev (pderiv 1 p) q • ContinuousLinearMap.snd ℂ ℂ ℂ

theorem ev_C (a : ℂ) (q : ℂ × ℂ) : ev (C a) q = a := by simp [ev]

theorem ev_add (p r : MvPolynomial (Fin 2) ℂ) (q : ℂ × ℂ) : ev (p + r) q = ev p q + ev r q := by
  simp [ev]

theorem ev_mul_X (p : MvPolynomial (Fin 2) ℂ) (i : Fin 2) (q : ℂ × ℂ) :
    ev (p * X i) q = ev p q * ![q.1, q.2] i := by
  simp [ev]

@[simp] theorem ev_zero (q : ℂ × ℂ) : ev 0 q = 0 := by simp [ev]
@[simp] theorem ev_one (q : ℂ × ℂ) : ev 1 q = 1 := by simp [ev]
@[simp] theorem ev_mul (p r : MvPolynomial (Fin 2) ℂ) (q : ℂ × ℂ) : ev (p * r) q = ev p q * ev r q := by
  simp [ev]
@[simp] theorem ev_X0 (q : ℂ × ℂ) : ev (X 0) q = q.1 := by simp [ev]
@[simp] theorem ev_X1 (q : ℂ × ℂ) : ev (X 1) q = q.2 := by simp [ev]

@[simp] theorem evDeriv_apply (p : MvPolynomial (Fin 2) ℂ) (q x : ℂ × ℂ) :
    evDeriv p q x = ev (pderiv 0 p) q * x.1 + ev (pderiv 1 p) q * x.2 := by
  simp [evDeriv]

theorem ev_coord_fst : (fun q : ℂ × ℂ ↦ ![q.1, q.2] 0) = Prod.fst := rfl
theorem ev_coord_snd : (fun q : ℂ × ℂ ↦ ![q.1, q.2] 1) = Prod.snd := rfl

theorem contDiff_ev (p : MvPolynomial (Fin 2) ℂ) : ContDiff ℂ ⊤ (ev p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have : ev (C a) = fun _ ↦ a := funext (ev_C a)
    rw [this]; exact contDiff_const
  | add p r hp hr =>
    have : ev (p + r) = fun q ↦ ev p q + ev r q := funext (ev_add p r)
    rw [this]; exact hp.add hr
  | mul_X p i hp =>
    have : ev (p * X i) = fun q ↦ ev p q * ![q.1, q.2] i := funext (ev_mul_X p i)
    rw [this]
    refine hp.mul ?_
    fin_cases i
    · exact contDiff_fst
    · exact contDiff_snd

theorem continuous_ev (p : MvPolynomial (Fin 2) ℂ) : Continuous (ev p) := (contDiff_ev p).continuous

theorem hasFDerivAt_ev (p : MvPolynomial (Fin 2) ℂ) (q : ℂ × ℂ) : HasFDerivAt (ev p) (evDeriv p q) q := by
  induction p using MvPolynomial.induction_on generalizing q with
  | C a =>
    have h1 : ev (C a) = fun _ ↦ a := funext (ev_C a)
    have h2 : evDeriv (C a) q = 0 := ContinuousLinearMap.ext fun x ↦ by simp
    rw [h1, h2]; exact hasFDerivAt_const _ _
  | add p r hp hr =>
    have h1 : ev (p + r) = fun q ↦ ev p q + ev r q := funext (ev_add p r)
    have h2 : evDeriv (p + r) q = evDeriv p q + evDeriv r q := by
      refine ContinuousLinearMap.ext fun x ↦ ?_
      simp only [evDeriv_apply, map_add, ev_add, ContinuousLinearMap.add_apply]; ring
    rw [h1, h2]; exact (hp q).add (hr q)
  | mul_X p i hp =>
    have h1 : ev (p * X i) = fun q ↦ ev p q * ![q.1, q.2] i := funext (ev_mul_X p i)
    rw [h1]
    fin_cases i
    · have := (hp q).mul (ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt
      refine this.congr_fderiv (ContinuousLinearMap.ext fun x ↦ ?_)
      simp [Derivation.leibniz, pderiv_X, Pi.single_apply, ev_add]
      ring
    · have := (hp q).mul (ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt
      refine this.congr_fderiv (ContinuousLinearMap.ext fun x ↦ ?_)
      simp [Derivation.leibniz, pderiv_X, Pi.single_apply, ev_add]
      ring

/-! ### Nonsingularity over `ℂ` -/

theorem ev_algebraMap (g : MvPolynomial (Fin 2) ℂ) (q : ℂ × ℂ) :
    aeval ![algebraMap ℂ (AlgebraicClosure ℂ) q.1, algebraMap ℂ (AlgebraicClosure ℂ) q.2] g =
      algebraMap ℂ (AlgebraicClosure ℂ) (ev g q) := by
  have : ![algebraMap ℂ (AlgebraicClosure ℂ) q.1, algebraMap ℂ (AlgebraicClosure ℂ) q.2] =
      algebraMap ℂ (AlgebraicClosure ℂ) ∘ ![q.1, q.2] := by
    funext i; fin_cases i <;> rfl
  rw [this, aeval_algebraMap_apply]
  rfl

/-- At a point of a nonsingular curve, `∂f/∂X` or `∂f/∂Y` is nonzero. -/
theorem pderiv_ne_zero_of_isNonsingular {C : AffinePlaneCurve ℂ} (hC : C.IsNonsingular) {q : ℂ × ℂ}
    (hq : ev C.f q = 0) : ev (pderiv 0 C.f) q ≠ 0 ∨ ev (pderiv 1 C.f) q ≠ 0 := by
  by_contra h
  push_neg at h
  apply hC (algebraMap ℂ _ q.1, algebraMap ℂ _ q.2)
  refine ⟨?_, ?_, ?_⟩ <;> simp only [ev_algebraMap, hq, h.1, h.2, map_zero]

/-! ### The local homeomorphisms `Φ` -/

section Local

variable (f : MvPolynomial (Fin 2) ℂ)

/-- The coordinate used by the chart: `x` (`k = true`) or `y` (`k = false`). -/
noncomputable def coordL (k : Bool) : (ℂ × ℂ) →L[ℂ] ℂ :=
  bif k then ContinuousLinearMap.fst ℂ ℂ ℂ else ContinuousLinearMap.snd ℂ ℂ ℂ

/-- The other partial derivative, which must not vanish: `∂f/∂Y` for `k = true`, `∂f/∂X` for `k = false`. -/
noncomputable def other (k : Bool) (q : ℂ × ℂ) : ℂ :=
  bif k then ev (pderiv 1 f) q else ev (pderiv 0 f) q

theorem continuous_other (k : Bool) : Continuous (other f k) := by
  cases k
  · exact continuous_ev _
  · exact continuous_ev _

theorem isOpen_good (k : Bool) : IsOpen {q | other f k q ≠ 0} :=
  isOpen_ne_fun (continuous_other f k) continuous_const

/-- `Φ(q) = (coord q, f(q))`. -/
noncomputable def Phi (k : Bool) (q : ℂ × ℂ) : ℂ × ℂ := (coordL k q, ev f q)

/-- The derivative of `Φ`. -/
noncomputable def PhiDeriv (k : Bool) (q : ℂ × ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (coordL k).prod (evDeriv f q)

theorem hasFDerivAt_Phi (k : Bool) (q : ℂ × ℂ) : HasFDerivAt (Phi f k) (PhiDeriv f k q) q :=
  (coordL k).hasFDerivAt.prodMk (hasFDerivAt_ev f q)

theorem contDiff_Phi (k : Bool) : ContDiff ℂ ⊤ (Phi f k) :=
  (coordL k).contDiff.prodMk (contDiff_ev f)

theorem injective_PhiDeriv {k : Bool} {q : ℂ × ℂ} (hq : other f k q ≠ 0) :
    Function.Injective (PhiDeriv f k q) := by
  refine (injective_iff_map_eq_zero (PhiDeriv f k q)).2 ?_
  rintro ⟨u, v⟩ h
  cases k
  · simp only [PhiDeriv, coordL, other, cond_false, evDeriv] at h hq
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, ContinuousLinearMap.coe_fst', smul_eq_mul, Prod.mk_eq_zero] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    simp only [mul_zero, add_zero, mul_eq_zero, hq, false_or] at h2
    simp [h2]
  · simp only [PhiDeriv, coordL, other, cond_true, evDeriv] at h hq
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, ContinuousLinearMap.coe_snd', smul_eq_mul, Prod.mk_eq_zero] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    simp only [mul_zero, zero_add, mul_eq_zero, hq, false_or] at h2
    simp [h2]

/-- The derivative of `Φ` as a linear equivalence where the relevant partial derivative is nonzero. -/
noncomputable def PhiEquiv {k : Bool} {q : ℂ × ℂ} (hq : other f k q ≠ 0) : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
  (LinearEquiv.ofInjectiveEndo _ (injective_PhiDeriv f hq)).toContinuousLinearEquiv

theorem coe_PhiEquiv {k : Bool} {q : ℂ × ℂ} (hq : other f k q ≠ 0) :
    (PhiEquiv f hq : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) = PhiDeriv f k q := by
  ext x <;> rfl

/-- The local homeomorphism `Ψ` given by the inverse function theorem, restricted to the open set where the relevant
partial derivative is nonzero. -/
noncomputable def Psi {k : Bool} {P : ℂ × ℂ} (hP : other f k P ≠ 0) : OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ) :=
  (HasStrictFDerivAt.toOpenPartialHomeomorph (Phi f k)
    (((contDiff_Phi f k).contDiffAt).hasStrictFDerivAt' (f' := (PhiEquiv f hP : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)))
      (by rw [coe_PhiEquiv]; exact hasFDerivAt_Phi f k P) (by simp))).restrOpen _ (isOpen_good f k)

variable {f} {k : Bool} {P : ℂ × ℂ} (hP : other f k P ≠ 0)
include hP

theorem coe_Psi : (Psi f hP : ℂ × ℂ → ℂ × ℂ) = Phi f k := rfl

theorem mem_Psi_source : P ∈ (Psi f hP).source :=
  ⟨HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _, hP⟩

theorem good_of_mem_Psi_source {q : ℂ × ℂ} (hq : q ∈ (Psi f hP).source) : other f k q ≠ 0 := hq.2

theorem contDiffAt_Psi_symm {b : ℂ × ℂ} (hb : b ∈ (Psi f hP).target) : ContDiffAt ℂ 1 (Psi f hP).symm b := by
  have hs := (Psi f hP).map_target hb
  have hg := good_of_mem_Psi_source hP hs
  refine (Psi f hP).contDiffAt_symm hb (f₀' := PhiEquiv f hg) ?_ ?_
  · rw [coe_PhiEquiv, coe_Psi]; exact hasFDerivAt_Phi f k _
  · rw [coe_Psi]; exact (contDiff_Phi f k).contDiffAt.of_le (by simp)

theorem Psi_symm_spec {x : ℂ} (hx : (x, 0) ∈ (Psi f hP).target) :
    coordL k ((Psi f hP).symm (x, 0)) = x ∧ ev f ((Psi f hP).symm (x, 0)) = 0 := by
  have h := (Psi f hP).right_inv hx
  rw [coe_Psi] at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

end Local

/-! ### The charts -/

section Charts

variable {C : AffinePlaneCurve ℂ}

/-- The points `C(ℂ)`. -/
abbrev Pts (C : AffinePlaneCurve ℂ) : Type := C.points ℂ

theorem ev_eq_zero (Q : Pts C) : ev C.f Q = 0 := Q.2

open Classical in
/-- The chart of `C(ℂ)` near `P` given by the coordinate `coordL k`, where the other partial derivative is
nonzero. -/
noncomputable def chart (k : Bool) (P : Pts C) (hP : other C.f k P ≠ 0) : OpenPartialHomeomorph (Pts C) ℂ where
  toFun Q := coordL k Q
  invFun x := if hx : (x, 0) ∈ (Psi C.f hP).target then ⟨(Psi C.f hP).symm (x, 0), (Psi_symm_spec hP hx).2⟩ else P
  source := {Q | (Q : ℂ × ℂ) ∈ (Psi C.f hP).source}
  target := {x | (x, 0) ∈ (Psi C.f hP).target}
  map_source' := by
    intro Q hQ
    have h := (Psi C.f hP).map_source hQ
    simp only [coe_Psi, Phi, ev_eq_zero] at h
    exact h
  map_target' := by
    intro x hx
    simp only [mem_setOf_eq] at hx
    simp only [mem_setOf_eq, dif_pos hx]
    exact (Psi C.f hP).map_target hx
  left_inv' := by
    intro Q hQ
    have h : ((coordL k Q, 0) : ℂ × ℂ) = Psi C.f hP Q := by
      simp only [coe_Psi, Phi, ev_eq_zero]
    have hx : ((coordL k Q, 0) : ℂ × ℂ) ∈ (Psi C.f hP).target := h ▸ (Psi C.f hP).map_source hQ
    simp only [dif_pos hx]
    apply Subtype.ext
    simp only
    rw [h, (Psi C.f hP).left_inv hQ]
  right_inv' := by
    intro x hx
    simp only [mem_setOf_eq] at hx
    simp only [dif_pos hx]
    exact (Psi_symm_spec hP hx).1
  open_source := (Psi C.f hP).open_source.preimage continuous_subtype_val
  open_target := (Psi C.f hP).open_target.preimage (Continuous.prodMk continuous_id continuous_const)
  continuousOn_toFun := ((coordL k).continuous.comp continuous_subtype_val).continuousOn
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    have h1 : ContinuousOn (fun x : ℂ ↦ (Psi C.f hP).symm (x, 0)) {x | (x, 0) ∈ (Psi C.f hP).target} :=
      (Psi C.f hP).continuousOn_symm.comp (Continuous.prodMk continuous_id continuous_const).continuousOn
        fun x hx ↦ hx
    refine h1.congr fun x hx ↦ ?_
    simp only [mem_setOf_eq] at hx
    simp only [Function.comp_apply, dif_pos hx]

theorem chart_apply (k : Bool) (P : Pts C) (hP : other C.f k P ≠ 0) (Q : Pts C) :
    chart k P hP Q = coordL k Q := rfl

theorem mem_chart_source (k : Bool) (P : Pts C) (hP : other C.f k P ≠ 0) : P ∈ (chart k P hP).source :=
  mem_Psi_source hP

theorem chart_symm_eqOn (k : Bool) (P : Pts C) (hP : other C.f k P ≠ 0) :
    EqOn (fun x ↦ ((chart k P hP).symm x : ℂ × ℂ)) (fun x ↦ (Psi C.f hP).symm (x, 0)) (chart k P hP).target := by
  classical
  intro x hx
  exact congrArg Subtype.val (dif_pos hx)

theorem other_ne_zero_of_not (hC : C.IsNonsingular) (P : Pts C) (h : ¬ ev (pderiv 1 C.f) P ≠ 0) :
    other C.f false P ≠ 0 := by
  rcases pderiv_ne_zero_of_isNonsingular hC (ev_eq_zero P) with h' | h'
  · exact h'
  · exact absurd h' h

/-- The charted space structure on `C(ℂ)` (for nonsingular `C`). -/
noncomputable def chartedSpace (hC : C.IsNonsingular) : ChartedSpace ℂ (Pts C) where
  atlas := {e | ∃ (k : Bool) (P : Pts C) (hP : other C.f k P ≠ 0), e = chart k P hP}
  chartAt P := if h : ev (pderiv 1 C.f) P ≠ 0 then chart true P h else chart false P (other_ne_zero_of_not hC P h)
  mem_chart_source P := by
    by_cases h : ev (pderiv 1 C.f) P ≠ 0
    · rw [dif_pos h]; exact mem_chart_source _ _ _
    · rw [dif_neg h]; exact mem_chart_source _ _ _
  chart_mem_atlas P := by
    by_cases h : ev (pderiv 1 C.f) P ≠ 0
    · rw [dif_pos h]; exact ⟨_, _, _, rfl⟩
    · rw [dif_neg h]; exact ⟨_, _, _, rfl⟩

theorem chartAt_of_ne (hC : C.IsNonsingular) (P : Pts C) (h : ev (pderiv 1 C.f) P ≠ 0) :
    (chartedSpace hC).chartAt P = chart true P h := dif_pos h

theorem chartAt_of_eq (hC : C.IsNonsingular) (P : Pts C) (h : ev (pderiv 1 C.f) P = 0) :
    (chartedSpace hC).chartAt P = chart false P (other_ne_zero_of_not hC P (not_not.2 h)) :=
  dif_neg (not_not.2 h)

theorem contDiffOn_transition (k k' : Bool) (P P' : Pts C) (hP : other C.f k P ≠ 0)
    (hP' : other C.f k' P' ≠ 0) :
    ContDiffOn ℂ 1 ((chart k P hP).symm ≫ₕ chart k' P' hP') ((chart k P hP).symm ≫ₕ chart k' P' hP').source := by
  intro x hx
  rw [OpenPartialHomeomorph.trans_source] at hx
  have hxT : x ∈ (chart k P hP).target := hx.1
  have hsm : ContDiffAt ℂ 1 (fun y : ℂ ↦ coordL k' ((Psi C.f hP).symm (y, 0))) x :=
    (coordL k').contDiff.contDiffAt.comp x
      ((contDiffAt_Psi_symm hP hxT).comp x (contDiffAt_id.prodMk contDiffAt_const))
  refine (hsm.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [(chart k P hP).open_target.mem_nhds hxT] with y hy
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, chart_apply]
  exact congrArg (coordL k') (chart_symm_eqOn k P hP hy)

theorem isManifold (hC : C.IsNonsingular) :
    letI := chartedSpace hC
    IsManifold 𝓘(ℂ) 1 (Pts C) := by
  letI := chartedSpace hC
  apply isManifold_of_contDiffOn
  rintro e e' ⟨k, P, hP, rfl⟩ ⟨k', P', hP', rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    preimage_id_eq, id_eq, range_id, inter_univ]
  exact contDiffOn_transition k k' P P' hP hP'

end Charts

/-- **Milne, Proposition 0.4.** The points `C(ℂ)` of a nonsingular affine plane curve over `ℂ` form a Riemann
surface, with charts the restrictions of the projection `(x, y) ↦ x` near points where `∂f/∂Y ≠ 0`, and of
`(x, y) ↦ y` near the other points (where `∂f/∂X ≠ 0`). -/
@[kb "milne2017mf" "Proposition 0.4, pdf p. 8"]
theorem planeCurveRiemannSurfaceStatement : PlaneCurveRiemannSurfaceStatement := by
  refine ⟨fun C hC ↦ ⟨chartedSpace hC, isManifold hC, fun P ↦ ⟨fun h Q _ ↦ ?_, fun h Q _ ↦ ?_⟩⟩⟩
  · exact congrArg (fun e : OpenPartialHomeomorph (Pts C) ℂ ↦ e Q) (chartAt_of_ne hC P h)
  · exact congrArg (fun e : OpenPartialHomeomorph (Pts C) ℂ ↦ e Q) (chartAt_of_eq hC P h)

end ModularFormsKB.Milne.RS
