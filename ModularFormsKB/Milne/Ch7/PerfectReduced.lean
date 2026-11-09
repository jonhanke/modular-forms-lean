import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.FieldTheory.Perfect

/-!
# Fields over a perfect field are geometrically reduced

For a perfect field $k$ and any field $K \supseteq k$, $\bar k \otimes_k K$ is reduced
(`isReduced_algebraicClosure_tensor_of_perfectField`). By `IsReduced.tensorProduct_of_flat_of_forall_fg` it suffices
that $K \otimes_k B$ is reduced for every finitely generated $k$-subalgebra $B \subseteq \bar k$; such a $B$ is a finite
field extension, separable because $k$ is perfect, hence unramified over $k$; so $K \otimes_k B$ is unramified over the
field $K$, hence reduced (Mathlib's `Algebra.FormallyUnramified.isReduced_of_field`). Used for the corrected Theorem 7.2
(the function field of a curve over a perfect field is geometrically reduced).
-/

universe u

open TensorProduct

namespace ModularFormsKB.Milne

variable (k : Type u) [Field k] [PerfectField k] (K : Type u) [Field K] [Algebra k K]

/-- **Over a perfect field, every field extension is geometrically reduced.** -/
theorem isReduced_algebraicClosure_tensor_of_perfectField : IsReduced (AlgebraicClosure k ⊗[k] K) := by
  have hKB : IsReduced (K ⊗[k] AlgebraicClosure k) := by
    refine IsReduced.tensorProduct_of_flat_of_forall_fg fun B hB ↦ ?_
    let : Field B := (Subalgebra.isField_of_algebraic B).toField
    have : Algebra.FiniteType k B := (Subalgebra.fg_iff_finiteType B).mp hB
    have : Algebra.IsAlgebraic k B := Algebra.IsAlgebraic.of_injective (Subalgebra.val B) Subtype.val_injective
    have : Algebra.IsSeparable k B := Algebra.IsAlgebraic.isSeparable_of_perfectField
    have : Algebra.FormallyUnramified k B := Algebra.FormallyUnramified.of_isSeparable k B
    have : Algebra.Unramified k B := ⟨inferInstance, inferInstance⟩
    have : Algebra.Unramified K (K ⊗[k] B) := inferInstance
    have : Algebra.FormallyUnramified K (K ⊗[k] B) := Algebra.Unramified.formallyUnramified
    have : Algebra.FiniteType K (K ⊗[k] B) := Algebra.Unramified.finiteType
    exact Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[k] B)
  exact isReduced_of_injective (Algebra.TensorProduct.comm k (AlgebraicClosure k) K).toRingHom
    (Algebra.TensorProduct.comm k (AlgebraicClosure k) K).injective

end ModularFormsKB.Milne
