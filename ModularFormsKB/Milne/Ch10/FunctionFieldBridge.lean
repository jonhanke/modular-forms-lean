import ModularFormsKB.Milne.Ch7.Curves
import TauCeti.FieldTheory.FunctionField.Basic
import TauCeti.AlgebraicGeometry.Scheme.FunctionField

/-!
# The function field of a curve is an algebraic function field in Tau Ceti's sense

For an integral curve $X$ over a field $k$ (Milne's `IsCurve`: a variety of dimension one), the function field
$k(X)$ is an algebraic function field of one variable over $k$ in the sense of Tau Ceti
(`TauCeti.IsFunctionField`: there is a transcendental $x$ with $k(X)/k(x)$ finite). Proof: a variety is locally of
finite type (`IsVariety.locallyOfFiniteType`), so a nonempty affine open $\operatorname{Spec} A$ has $A$ finitely
generated over $k$ and $k(X) = \operatorname{Frac} A$ is a finitely generated field extension; its transcendence
degree is one (`dimension`), so a transcendence basis $\{x\}$ makes $k(X)$ algebraic and finitely generated, hence
finite, over $k(x)$. This is used for the degree of the Frobenius map in Proposition 10.2.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace ModularFormsKB.Milne

variable (k : Type u) [Field k]

/-- **The function field of a curve is an algebraic function field.** -/
theorem isFunctionField_functionField {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k))
    (hf : IsCurve k f) :
    letI := (functionFieldAlgebraMap k f).toAlgebra
    TauCeti.IsFunctionField k X.functionField := by
  let : X.Over (Spec (CommRingCat.of k)) := ⟨f⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := hf.1.locallyOfFiniteType
  have h : functionFieldAlgebraMap k f = Scheme.baseRingToFunctionField k X := by
    ext c
    rfl
  rw [h]
  have := TauCeti.AlgebraicGeometry.essFiniteType_functionField k (X := X)
  rw [TauCeti.isFunctionField_iff_trdeg_eq_one]
  exact hf.2

end ModularFormsKB.Milne
