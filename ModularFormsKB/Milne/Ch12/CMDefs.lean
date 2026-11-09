import TauCeti.Analysis.SpecialFunctions.Elliptic.Uniformization
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.PotentialGoodReduction
import TauCeti.NumberTheory.NumberField.Global.Orders.Picard
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import ModularFormsKB.Citation
/-!
# Milne, Section 12: definitions for complex multiplication

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, pdf pp. 123–124.
**D125** `HasComplexMultiplication`, **D129** `HasCMBy`, **D126** `EllCM` ($\mathrm{Ell}(R)$), `latticeEnd`,
`idealLattice`, and the named statement `ComplexUniformization`; see `ModularFormsKB.Milne.Ch12.ComplexMultiplication`
for the conventions and the results.
-/

open NumberField TauCeti TauCeti.Isogeny TauCeti.GlobalNumberFields UpperHalfPlane
open scoped WeierstrassCurve

namespace ModularFormsKB.Milne

/-! ### Definitions -/

section Defs

variable {k : Type*} [Field k] (W : WeierstrassCurve k) [W.IsElliptic]

/-- **D125** (Milne): $E$ has complex multiplication if $\mathrm{End}(E) \ne \mathbb Z$, i.e. some endomorphism is not
multiplication by an integer. -/
@[kb "milne2017mf" "Section 12, complex multiplication (pdf p. 123)"]
def HasComplexMultiplication : Prop :=
  ∃ f : Hom W.toAffine W.toAffine, ∀ n : ℤ, f ≠ n • (1 : Hom W.toAffine W.toAffine)

/-- **D129** (Milne): $E$ has complex multiplication by the order $R$ of a quadratic imaginary field $K$ (defined over
$k$): there is an isomorphism $R \to \mathrm{End}(E)$. -/
@[kb "milne2017mf" "Section 12, complex multiplication by R over k (pdf p. 124)"]
def HasCMBy {K : Type*} [Field K] [NumberField K] (O : NumberFieldOrder K) : Prop :=
  Module.finrank ℚ K = 2 ∧ IsTotallyComplex K ∧ Nonempty (O.toSubalgebra ≃+* Hom W.toAffine W.toAffine)

end Defs

/-- **D126** (Milne): $\mathrm{Ell}(R)$, the isomorphism classes of elliptic curves over $\mathbb C$ with complex
multiplication by $R$, recorded by their $j$-invariants. -/
@[kb "milne2017mf" "Section 12, Ell(R) (pdf p. 123)"]
def EllCM {K : Type*} [Field K] [NumberField K] (O : NumberFieldOrder K) : Set ℂ :=
  {x | ∃ (W : WeierstrassCurve ℂ) (_ : W.IsElliptic), HasCMBy W O ∧ W.j = x}

/-- The ring $\{\alpha \in \mathbb C \mid \alpha\Lambda \subseteq \Lambda\}$ of a subgroup $\Lambda \subseteq \mathbb C$
(for a lattice: the endomorphism ring of $\mathbb C/\Lambda$). -/
def latticeEnd (Λ : Submodule ℤ ℂ) : Subring ℂ where
  carrier := {α | ∀ x ∈ Λ, α * x ∈ Λ}
  mul_mem' ha hb x hx := by simpa [mul_assoc] using ha _ (hb x hx)
  one_mem' x hx := by simpa using hx
  add_mem' ha hb x hx := by simpa [add_mul] using Λ.add_mem (ha x hx) (hb x hx)
  zero_mem' x _ := by simp
  neg_mem' ha x hx := by simpa [neg_mul] using Λ.neg_mem (ha x hx)

/-- **The analytic theory of elliptic curves over $\mathbb C$** (Milne, Section 12, pdf p. 123, citing the
Weierstrass theory: Silverman, *The Arithmetic of Elliptic Curves*, VI.3, VI.4, VI.5), as a named statement:
(1) every elliptic curve over $\mathbb C$ is isomorphic to $E(\Lambda)$ for a lattice $\Lambda$; (2) the
endomorphisms of $E(\Lambda)$ are the maps $[z] \mapsto [\alpha z]$ for $\alpha\Lambda \subseteq \Lambda$; (3)
$E(\Lambda) \cong E(\Lambda')$ exactly when $\Lambda' = \alpha\Lambda$ for some $\alpha \in \mathbb C^\times$. -/
@[kb "milne2017mf" "Section 12, elliptic curves over C (pdf p. 123)"]
structure ComplexUniformization : Prop where
  exists_lattice : ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic], ∃ L : PeriodPair,
    ∃ C : WeierstrassCurve.VariableChange ℂ, C • W = L.weierstrassCurve
  endRingEquiv : ∀ L : PeriodPair, ∃ e : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine ≃+*
      latticeEnd L.lattice, ∀ f z, f.pointMap (L.weierstrassPoint z) = L.weierstrassPoint ((e f : ℂ) * z)
  j_eq_iff : ∀ L L' : PeriodPair, L.weierstrassCurve.j = L'.weierstrassCurve.j ↔
    ∃ α : ℂ, α ≠ 0 ∧ L'.lattice = L.lattice.map (LinearMap.mulLeft ℤ α)

section Ideals

variable {K : Type*} [Field K] [NumberField K] (ι : K →+* ℂ) (O : NumberFieldOrder K)

/-- The image $\iota(\mathfrak a) \subseteq \mathbb C$ of a fractional ideal of an order. -/
def idealLattice (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) : Submodule ℤ ℂ :=
  ((I : Submodule O.toSubalgebra K).restrictScalars ℤ).map ι.toIntAlgHom.toLinearMap

end Ideals

end ModularFormsKB.Milne
