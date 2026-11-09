import ModularFormsKB.Milne.Ch7.Varieties
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Birational.Dominant
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField

/-!
# Milne, Chapter 7: curves and Riemann surfaces (Theorem 7.2, Corollary 7.3, Example 7.4, Theorem 7.5)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 7, pdf pp. 94–95.

Varieties, curves, regularity and completeness are those of `ModularFormsKB.Milne.Ch7.Varieties`. A morphism of
curves over $k_0$ that is nonconstant is dominant, and a dominant morphism $\varphi : X \to Y$ of integral schemes
induces $\varphi^* : k_0(Y) \to k_0(X)$ (`functionFieldMap`, the stalk map at the generic point).

All four results are deep; they are stated as **named statements** (Prop structures carrying a source tag), not
proved:

- **Theorem 7.2**: `CurveFunctionFieldEquivalence` (complete regular irreducible curves over $k_0$ and function fields
  in one variable over $k_0$; geometric irreducibility and the field of constants).
- **Corollary 7.3**: `RegularCurveCompletion`.
- **Example 7.4**: `PlaneCurveNonsingularLocus`.
- **Theorem 7.5**: `RiemannSurfaceAlgebraicStructure` (Riemann's existence theorem), for compact connected Riemann
  surfaces in Tau Ceti's sense, with Tau Ceti's field of meromorphic functions
  `TauCeti.RiemannSurface.MeromorphicFunction`.

Remark 7.6 is commentary (not a result).
-/

universe u

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace ModularFormsKB.Milne

variable (k₀ : Type u) [Field k₀]

/-- The image of the generic point under a dominant morphism specializes to the generic point of the target. -/
theorem specializes_genericPoint_of_isDominant {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (φ : X ⟶ Y) [IsDominant φ] : φ (genericPoint X) ⤳ genericPoint Y := by
  have h := (genericPoint_spec X).image (f := φ.base) φ.base.hom.continuous
  rw [Set.image_univ, φ.denseRange.closure_range] at h
  exact h.specializes (Set.mem_univ _)

/-- **The map of function fields** $\varphi^* : k_0(Y) \to k_0(X)$ of a dominant morphism of irreducible schemes
(Milne, Section 10, pdf p. 106: "a nonconstant morphism $\alpha : C \to C'$ of curves defines an inclusion
$\alpha^* : k(C') \hookrightarrow k(C)$"): the stalk map at the generic point. -/
def functionFieldMap {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y] (φ : X ⟶ Y)
    [IsDominant φ] : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes (specializes_genericPoint_of_isDominant φ) ≫ φ.stalkMap (genericPoint X)

/-- The map from the local ring $\mathcal O_{X,x}$ to the function field $k_0(X)$ of an irreducible scheme. -/
def stalkToFunctionField {X : Scheme.{u}} [IrreducibleSpace X] (x : X) :
    X.presheaf.stalk x ⟶ X.functionField :=
  X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ x))

/-- A complete regular irreducible curve over $k_0$ (the objects of Theorem 7.2). -/
def IsCompleteRegularCurve {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k₀)) : Prop :=
  IsCurve k₀ f ∧ IsRegularVariety k₀ f ∧ IsComplete k₀ f

/-- **Milne, Theorem 7.2** (named statement): the map $X \mapsto k_0(X)$ is an equivalence from the category of
complete regular irreducible algebraic curves over $k_0$ (with nonconstant, i.e. dominant, morphisms over $k_0$) to the
category of function fields in one variable over $k_0$ (with $k_0$-embeddings), and the curve is geometrically
irreducible if and only if $k_0$ is the field of constants of $k_0(X)$. Fields:

- `functionField_isFunctionFieldIn`: the functor is well defined;
- `essSurj`: every function field in one variable is $k_0$-isomorphic to $k_0(X)$ for such a curve;
- `faithful`, `full`: dominant $k_0$-morphisms $X \to Y$ correspond bijectively to $k_0$-embeddings
  $k_0(Y) \to k_0(X)$, via $\varphi \mapsto \varphi^*$;
- `geometricallyIrreducible_iff`: geometric irreducibility versus the field of constants.

Proof in the book: only the construction of the curve from $K$ (its points are the discrete valuation rings of $K$
containing $k_0$). -/
@[kb "milne2017mf" "Section 7, Theorem 7.2 (pdf p. 94)"]
structure CurveFunctionFieldEquivalence : Prop where
  functionField_isFunctionFieldIn : ∀ {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k₀)),
    IsCompleteRegularCurve k₀ f →
      letI := (functionFieldAlgebraMap k₀ f).toAlgebra
      IsFunctionFieldIn k₀ 1 X.functionField
  essSurj : ∀ (K : Type u) [Field K] [Algebra k₀ K], IsFunctionFieldIn k₀ 1 K →
    ∃ (X : Scheme.{u}) (_ : IsIntegral X) (f : X ⟶ Spec (CommRingCat.of k₀)), IsCompleteRegularCurve k₀ f ∧
      ∃ e : K ≃+* X.functionField, ∀ c : k₀, e (algebraMap k₀ K c) = functionFieldAlgebraMap k₀ f c
  faithful : ∀ {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Spec (CommRingCat.of k₀))
    (g : Y ⟶ Spec (CommRingCat.of k₀)), IsCompleteRegularCurve k₀ f → IsCompleteRegularCurve k₀ g →
    ∀ (φ ψ : X ⟶ Y) [IsDominant φ] [IsDominant ψ], φ ≫ g = f → ψ ≫ g = f →
      functionFieldMap φ = functionFieldMap ψ → φ = ψ
  full : ∀ {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Spec (CommRingCat.of k₀))
    (g : Y ⟶ Spec (CommRingCat.of k₀)), IsCompleteRegularCurve k₀ f → IsCompleteRegularCurve k₀ g →
    ∀ σ : Y.functionField ⟶ X.functionField,
      (∀ c : k₀, σ.hom (functionFieldAlgebraMap k₀ g c) = functionFieldAlgebraMap k₀ f c) →
      ∃ (φ : X ⟶ Y) (_ : IsDominant φ), φ ≫ g = f ∧ functionFieldMap φ = σ
  geometricallyIrreducible_iff : ∀ {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k₀)),
    IsCompleteRegularCurve k₀ f →
      (GeometricallyIrreducible f ↔
        letI := (functionFieldAlgebraMap k₀ f).toAlgebra
        fieldOfConstants k₀ X.functionField = ⊥)

/-- A regular (irreducible) curve over $k_0$. -/
def IsRegularCurve {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k₀)) : Prop :=
  IsCurve k₀ f ∧ IsRegularVariety k₀ f

/-- **Milne, Corollary 7.3** (named statement): a regular curve $U$ embeds (as an open subscheme, over $k_0$) into a
complete regular curve $\bar U$, and $U \hookrightarrow \bar U$ is universal among maps from $U$ into complete
regular curves: every $k_0$-morphism $U \to C$ to a complete regular curve extends uniquely to $\bar U$. -/
@[kb "milne2017mf" "Section 7, Corollary 7.3 (pdf p. 94)"]
structure RegularCurveCompletion : Prop where
  completion : ∀ {U : Scheme.{u}} [IsIntegral U] (f : U ⟶ Spec (CommRingCat.of k₀)), IsRegularCurve k₀ f →
    ∃ (Ubar : Scheme.{u}) (_ : IsIntegral Ubar) (g : Ubar ⟶ Spec (CommRingCat.of k₀)) (ι : U ⟶ Ubar)
      (_ : IsOpenImmersion ι), IsCompleteRegularCurve k₀ g ∧ ι ≫ g = f ∧
      ∀ {C : Scheme.{u}} [IsIntegral C] (h : C ⟶ Spec (CommRingCat.of k₀)), IsCompleteRegularCurve k₀ h →
        ∀ φ : U ⟶ C, φ ≫ h = f → ∃! φbar : Ubar ⟶ C, φbar ≫ h = g ∧ ι ≫ φbar = φ

/-- The open subset $C^{\mathrm{ns}}$ of $C = \operatorname{Spec} k_0[X, Y]/(F)$ (Example 7.4): the complement of
the maximal (prime) ideals containing $(\partial F/\partial X, \partial F/\partial Y) \bmod F$. -/
def nonsingularLocus (F : MvPolynomial (Fin 2) k₀) :
    (Spec (CommRingCat.of (MvPolynomial (Fin 2) k₀ ⧸ Ideal.span {F}))).Opens :=
  ⟨(PrimeSpectrum.zeroLocus ({Ideal.Quotient.mk _ (MvPolynomial.pderiv 0 F),
    Ideal.Quotient.mk _ (MvPolynomial.pderiv 1 F)} : Set (MvPolynomial (Fin 2) k₀ ⧸ Ideal.span {F})))ᶜ,
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- **Milne, Example 7.4** (named statement): let $F(X, Y) \in k_0[X, Y]$ be absolutely irreducible (irreducible in
$k[X, Y]$, $k$ an algebraic closure of $k_0$), $A = k_0[X, Y]/(F)$, $C = \operatorname{Spec} A$. Then $A$ is an affine
$k_0$-algebra, $C^{\mathrm{ns}}$ is a nonsingular curve (smooth of relative dimension $1$ over $k_0$), and hence it
embeds as an open subscheme into a complete regular curve. -/
@[kb "milne2017mf" "Section 7, Example 7.4 (pdf p. 94)"]
structure PlaneCurveNonsingularLocus : Prop where
  statement : ∀ F : MvPolynomial (Fin 2) k₀,
    Irreducible (MvPolynomial.map (algebraMap k₀ (AlgebraicClosure k₀)) F) →
    IsAffineAlgebra k₀ (MvPolynomial (Fin 2) k₀ ⧸ Ideal.span {F}) ∧
      SmoothOfRelativeDimension 1 ((nonsingularLocus k₀ F).ι ≫ specStructure k₀ _) ∧
      ∃ (Cbar : Scheme.{u}) (_ : IsIntegral Cbar) (g : Cbar ⟶ Spec (CommRingCat.of k₀))
        (ι : (nonsingularLocus k₀ F).toScheme ⟶ Cbar) (_ : IsOpenImmersion ι),
        IsCompleteRegularCurve k₀ g ∧ ι ≫ g = (nonsingularLocus k₀ F).ι ≫ specStructure k₀ _

open TauCeti.RiemannSurface in
/-- **Milne, Theorem 7.5** (named statement; Riemann's existence theorem): every compact (connected) Riemann surface
$X$ has a unique structure of a complete nonsingular algebraic curve. Milne's construction: the underlying set is $X$,
the open sets are those with finite complement, and the regular functions on $U$ are the meromorphic functions on $X$
that are holomorphic on $U$. Formally: there are a complete regular curve $C$ over $\mathbb C$, a bijection $e$ of $X$
with the closed points of $C$, and a $\mathbb C$-isomorphism $\Phi$ of the field $\mathcal M(X)$ of meromorphic
functions (Tau Ceti's `MeromorphicFunction X`) with $\mathbb C(C)$, such that a meromorphic function is holomorphic at
$x$ exactly when $\Phi(g)$ is regular at $e(x)$ (lies in the image of $\mathcal O_{C, e(x)}$); and any two such
structures are isomorphic by a unique isomorphism over $\mathbb C$ compatible with the bijections. -/
@[kb "milne2017mf" "Section 7, Theorem 7.5 (pdf p. 95)"]
structure RiemannSurfaceAlgebraicStructure (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [ConnectedSpace X] [CompactSpace X] [T2Space X] : Prop where
  exists_structure : ∃ (C : Scheme.{0}) (_ : IsIntegral C) (f : C ⟶ Spec (CommRingCat.of ℂ)),
    IsCompleteRegularCurve ℂ f ∧
    ∃ (e : X ≃ {c : C // IsClosed ({c} : Set C)}) (Φ : MeromorphicFunction X ≃+* C.functionField),
      (∀ z : ℂ, Φ (algebraMap ℂ (MeromorphicFunction X) z) = functionFieldAlgebraMap ℂ f z) ∧
      ∀ (x : X) (g : MeromorphicFunction X),
        (g x ≠ OnePoint.infty ↔ ∃ s, (stalkToFunctionField (e x).1).hom s = Φ g)
  unique : ∀ (C C' : Scheme.{0}) [IsIntegral C] [IsIntegral C'] (f : C ⟶ Spec (CommRingCat.of ℂ))
    (f' : C' ⟶ Spec (CommRingCat.of ℂ)),
    IsCompleteRegularCurve ℂ f → IsCompleteRegularCurve ℂ f' →
    ∀ (e : X ≃ {c : C // IsClosed ({c} : Set C)}) (e' : X ≃ {c : C' // IsClosed ({c} : Set C')})
      (Φ : MeromorphicFunction X ≃+* C.functionField) (Φ' : MeromorphicFunction X ≃+* C'.functionField),
      (∀ (x : X) (g : MeromorphicFunction X),
        (g x ≠ OnePoint.infty ↔ ∃ s, (stalkToFunctionField (e x).1).hom s = Φ g)) →
      (∀ (x : X) (g : MeromorphicFunction X),
        (g x ≠ OnePoint.infty ↔ ∃ s, (stalkToFunctionField (e' x).1).hom s = Φ' g)) →
      ∃! i : C ≅ C', i.hom ≫ f' = f ∧ ∀ x : X, i.hom (e x).1 = (e' x).1

end ModularFormsKB.Milne
