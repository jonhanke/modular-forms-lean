import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import ModularFormsKB.Citation
/-!
# Milne, Section 11: degree, separability and pure inseparability of a morphism of curves (D111, D112)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 11, pdf p. 106.

A nonconstant morphism $\alpha \colon C \to C'$ of complete nonsingular curves over $k$ is the same as a
$k$-embedding of function fields $\alpha^* \colon k(C') \to k(C)$ (the category of such curves with nonconstant
morphisms is anti-equivalent to that of function fields of one variable over $k$; Hartshorne I.6.12 [unverified]).
Neither Mathlib nor Tau Ceti has morphisms of curves, so the definitions are stated for the embedding
$\varphi = \alpha^*$:

- **D111** `curveMorphismDegree`: $\deg\alpha = [k(C) : \alpha^*k(C')]$;
- **D112** `IsSeparableCurveMorphism`, `IsPurelyInseparableCurveMorphism`: $k(C)$ is separable, respectively purely
  inseparable, over $\alpha^*k(C')$.
-/

namespace ModularFormsKB.Milne

variable {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']

/-- **D111** (Milne): the degree of a nonconstant morphism $\alpha \colon C \to C'$, given by its pullback
$\varphi = \alpha^* \colon k(C') \to k(C)$ on function fields: $[k(C) : \alpha^*k(C')]$. -/
@[kb "milne2017mf" "Section 11, degree of a morphism of curves (pdf p. 106)"]
noncomputable def curveMorphismDegree (φ : F' →ₐ[k] F) : ℕ :=
  Module.finrank φ.fieldRange F

/-- **D112** (Milne): a nonconstant morphism of curves is separable if $k(C)$ is separable over $\alpha^*k(C')$. -/
@[kb "milne2017mf" "Section 11, separable morphism of curves (pdf p. 106)"]
def IsSeparableCurveMorphism (φ : F' →ₐ[k] F) : Prop :=
  Algebra.IsSeparable φ.fieldRange F

/-- **D112** (Milne): a nonconstant morphism of curves is purely inseparable if $k(C)$ is purely inseparable over
$\alpha^*k(C')$. -/
@[kb "milne2017mf" "Section 11, purely inseparable morphism of curves (pdf p. 106)"]
def IsPurelyInseparableCurveMorphism (φ : F' →ₐ[k] F) : Prop :=
  IsPurelyInseparable φ.fieldRange F

/-- The identity morphism has degree $1$. -/
theorem curveMorphismDegree_id : curveMorphismDegree (AlgHom.id k F) = 1 := by
  unfold curveMorphismDegree
  rw [AlgHom.fieldRange_eq_top.mpr Function.surjective_id]
  exact IntermediateField.finrank_top

/-- A morphism of degree $1$ is both separable and purely inseparable. -/
theorem isSeparable_and_isPurelyInseparable_of_degree_eq_one (φ : F' →ₐ[k] F)
    (h : curveMorphismDegree φ = 1) :
    IsSeparableCurveMorphism φ ∧ IsPurelyInseparableCurveMorphism φ := by
  have htop : (⊤ : IntermediateField φ.fieldRange F) = ⊥ :=
    IntermediateField.finrank_eq_one_iff.mp (by rw [IntermediateField.finrank_top']; exact h)
  have hmem : ∀ x : F, ∃ y, algebraMap φ.fieldRange F y = x := fun x => by
    have hx : x ∈ (⊥ : IntermediateField φ.fieldRange F) := htop ▸ IntermediateField.mem_top
    exact IntermediateField.mem_bot.mp hx
  refine ⟨⟨fun x => ?_⟩, ⟨⟨fun x => ?_⟩, fun x _ => ?_⟩⟩
  · obtain ⟨y, rfl⟩ := hmem x
    exact isSeparable_algebraMap y
  · obtain ⟨y, rfl⟩ := hmem x
    exact isIntegral_algebraMap
  · obtain ⟨y, rfl⟩ := hmem x
    exact ⟨y, rfl⟩

end ModularFormsKB.Milne
