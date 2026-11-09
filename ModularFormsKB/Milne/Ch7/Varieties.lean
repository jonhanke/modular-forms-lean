import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Topology
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.MvPolynomial.Basic
import ModularFormsKB.Citation
/-!
# Milne, Chapter 7: brief review of algebraic geometry (varieties, points, function fields)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 7, pdf pp. 91–94.

## Varieties as schemes

Milne works with *varieties in the sense of his notes on algebraic geometry*: an affine variety over $k_0$ is the
ringed space $\operatorname{Specm}(A) = (\operatorname{specm}(A), \mathcal O)$ of maximal ideals of an *affine
$k_0$-algebra* $A$ (finitely generated, with $k \otimes_{k_0} A$ reduced for an algebraic closure $k$), with the sheaf
satisfying $\mathcal O(D(f)) = A_f$; a prevariety is a ringed space with a finite cover by affine varieties, and a
variety is a separated prevariety. Mathlib has schemes, not $\operatorname{Specm}$-ringed spaces. We model Milne's
affine variety $\operatorname{Specm}(A)$ by the affine scheme $\operatorname{Spec}(A)$ over $\operatorname{Spec}(k_0)$:
for a finitely generated $k_0$-algebra the maximal ideals are the closed points of $\operatorname{Spec}(A)$ (a Jacobson
ring), and the two categories are equivalent (this is the standard dictionary; it is not formalized here). With this
dictionary Milne's definitions become:

- an *affine $k_0$-algebra* (`IsAffineAlgebra`) and the value $f(v) \in \kappa(v) = A/\mathfrak m_v$ of $f \in A$ at a
  point $v \in \operatorname{specm}(A)$ (D086, `valueAt`), with the zero set $V(f) = \operatorname{specm}(A) \smallsetminus
  D(f)$ (`valueAt_eq_zero_iff`);
- *affine variety*, *prevariety*, *variety* over $k_0$ (D087, `IsAffineVariety`, `IsPrevariety`, `IsVariety`);
- *points with coordinates in a $k_0$-algebra $R$* (D088 to D090, `Points`), with $X(R) = \operatorname{Hom}_{k_0}(A, R)$
  for $X = \operatorname{Spec} A$ (`pointsSpecEquiv`) and the description of $k_0$-points of $k_0[X_1, \dots, X_n]/I$
  as the common zeros of $I$ (`algHomQuotientEquiv`);
- the residue field $\kappa(v)$ of a point (D091, Mathlib's `AlgebraicGeometry.Scheme.residueField`) and the *degree* of
  a point (D092, `pointDegree`), with $X(k_0) = $ the points of degree $1$ (`pointsEquivDegreeOne`);
- the *dimension* of an irreducible variety, the transcendence degree of its function field (D093, `dimension`), and
  *algebraic curves*;
- *regular* varieties: all local rings at the points of $\operatorname{specm}$, i.e. at the closed points, are regular
  (D094, `IsRegularVariety`);
- *function fields in $n$ variables* and the *field of constants* (D095, `IsFunctionFieldIn`, `fieldOfConstants`).

Definition 7.1 (presheaves, sheaves, ringed spaces) is in Mathlib: `TopCat.Presheaf`, `TopCat.Presheaf.IsSheaf`,
`TopCat.Sheaf`, `AlgebraicGeometry.SheafedSpace` (a ringed space is a sheafed space valued in commutative rings).
-/

universe u

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace ModularFormsKB.Milne

variable (k₀ : Type u) [Field k₀]

/-! ### Affine algebras and the value of a function at a point -/

/-- **Affine $k_0$-algebra** (Milne, Section 7, pdf p. 91): a finitely generated $k_0$-algebra $A$ such that
$k \otimes_{k_0} A$ is reduced, $k$ an algebraic closure of $k_0$ (Mathlib's `AlgebraicClosure k₀`). -/
@[kb "milne2017mf" "Section 7, affine k0-algebra (pdf p. 91)"]
def IsAffineAlgebra (A : Type u) [CommRing A] [Algebra k₀ A] : Prop :=
  Algebra.FiniteType k₀ A ∧ IsReduced (TensorProduct k₀ (AlgebraicClosure k₀) A)

/-- **The value of a function at a point** (Milne, Section 7, pdf p. 92; D086): for $f \in A$ and a point
$v \in \operatorname{specm}(A)$ (a maximal ideal $\mathfrak m_v$; Mathlib's `MaximalSpectrum A`, with the topology
whose basic opens are $D(f) = \{\mathfrak m \mid f \notin \mathfrak m\}$), $f(v)$ is the image of $f$ in the residue
field $\kappa(v) = A/\mathfrak m_v$. -/
@[kb "milne2017mf" "Section 7, value f(v) of f at a point v of specm A (pdf p. 92)"]
def valueAt {A : Type u} [CommRing A] (f : A) (v : MaximalSpectrum A) : A ⧸ v.asIdeal :=
  Ideal.Quotient.mk v.asIdeal f

/-- The zero set $V(f) = \{v \mid f(v) = 0\}$ is the complement of $D(f)$ (Milne, Section 7, pdf p. 92). -/
@[kb "milne2017mf" "Section 7, the zero set V(f) is the complement of D(f) (pdf p. 92)"]
theorem valueAt_eq_zero_iff {A : Type u} [CommRing A] (f : A) (v : MaximalSpectrum A) :
    valueAt f v = 0 ↔ f ∈ v.asIdeal :=
  Ideal.Quotient.eq_zero_iff_mem

/-! ### Varieties -/

/-- The structure morphism of `Spec A` over `Spec k₀` for a $k_0$-algebra $A$. -/
abbrev specStructure (A : Type u) [CommRing A] [Algebra k₀ A] :
    Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k₀) :=
  Spec.map (CommRingCat.ofHom (algebraMap k₀ A))

/-- **Affine variety over $k_0$** (Milne, Section 7, pdf p. 92; D087): a $k_0$-scheme isomorphic over $k_0$ to
$\operatorname{Spec}(A)$ for an affine $k_0$-algebra $A$ (Milne: the ringed space $\operatorname{Specm}(A)$ and every
ringed space isomorphic to it; see the module docstring for the dictionary). -/
@[kb "milne2017mf" "Section 7, affine variety over k0 (pdf p. 92)"]
def IsAffineVariety {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k₀)) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : Algebra k₀ A), IsAffineAlgebra k₀ A ∧
    ∃ e : X ≅ Spec (CommRingCat.of A), e.hom ≫ specStructure k₀ A = f

/-- **Prevariety over $k_0$** (Milne, Section 7, pdf p. 92): a $k_0$-scheme with a finite covering by open subsets
each of which is an affine variety over $k_0$. -/
@[kb "milne2017mf" "Section 7, prevariety over k0 (pdf p. 92)"]
def IsPrevariety {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k₀)) : Prop :=
  ∃ (n : ℕ) (U : Fin n → X.Opens), (⨆ i, U i) = ⊤ ∧ ∀ i, IsAffineVariety k₀ ((U i).ι ≫ f)

/-- **Variety over $k_0$** (Milne, Section 7, pdf p. 92): a separated prevariety. Milne's separatedness ("for all
pairs of regular maps $Z \rightrightarrows X$ the set where they agree is closed in $Z$") is Mathlib's `IsSeparated`
(the diagonal is a closed immersion) under the dictionary of the module docstring. -/
@[kb "milne2017mf" "Section 7, variety over k0 (separated prevariety) (pdf p. 92)"]
def IsVariety {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k₀)) : Prop :=
  IsPrevariety k₀ f ∧ IsSeparated f

/-- $k_0$ itself is an affine $k_0$-algebra. -/
theorem isAffineAlgebra_self : IsAffineAlgebra k₀ k₀ := by
  refine ⟨inferInstance, ?_⟩
  exact isReduced_of_injective (Algebra.TensorProduct.rid k₀ (AlgebraicClosure k₀) (AlgebraicClosure k₀)).toRingEquiv.toRingHom
    (Algebra.TensorProduct.rid k₀ (AlgebraicClosure k₀) (AlgebraicClosure k₀)).injective

/-- The polynomial ring $k_0[X]$ (the coordinate ring of the affine line) is an affine $k_0$-algebra. -/
theorem isAffineAlgebra_polynomial : IsAffineAlgebra k₀ (Polynomial k₀) := by
  refine ⟨inferInstance, ?_⟩
  exact isReduced_of_injective (polyEquivTensor k₀ (AlgebraicClosure k₀)).symm.toRingEquiv.toRingHom
    (polyEquivTensor k₀ (AlgebraicClosure k₀)).symm.injective

/-- An affine $k_0$-algebra is reduced (it embeds in $k \otimes_{k_0} A$). -/
private lemma IsAffineAlgebra.isReduced' {A : Type u} [CommRing A] [Algebra k₀ A]
    (h : IsAffineAlgebra k₀ A) : _root_.IsReduced A := by
  have := h.2
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[k₀] TensorProduct k₀ (AlgebraicClosure k₀) A)
    (Algebra.TensorProduct.includeRight_injective (algebraMap k₀ (AlgebraicClosure k₀)).injective)

/-- Basic properties of an affine variety: reduced, finite type, compact, separated. -/
private lemma IsAffineVariety.facts {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k₀)}
    (h : IsAffineVariety k₀ f) :
    AlgebraicGeometry.IsReduced X ∧ LocallyOfFiniteType f ∧ CompactSpace X ∧ IsSeparated f := by
  obtain ⟨A, _, _, hA, e, rfl⟩ := h
  have := hA.isReduced'
  have : LocallyOfFiniteType (specStructure k₀ A) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr hA.1)
  refine ⟨isReduced_of_isOpenImmersion e.hom, inferInstance, ?_, inferInstance⟩
  have : CompactSpace (Spec (CommRingCat.of A)) := inferInstance
  have h1 : IsCompact (Set.range e.inv) := isCompact_range e.inv.continuous
  have h2 : Set.range e.inv = Set.univ := by
    refine Set.range_eq_univ.mpr fun x => ⟨e.hom x, ?_⟩
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
    rfl
  rw [h2] at h1
  exact isCompact_univ_iff.mp h1

/-- $\operatorname{Spec} A$ is an affine variety for an affine $k_0$-algebra $A$. -/
theorem isAffineVariety_spec {A : Type u} [CommRing A] [Algebra k₀ A] (hA : IsAffineAlgebra k₀ A) :
    IsAffineVariety k₀ (specStructure k₀ A) :=
  ⟨A, inferInstance, inferInstance, hA, Iso.refl _, Category.id_comp _⟩

/-- An affine variety is a variety (affine schemes are separated). -/
theorem IsAffineVariety.isVariety {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k₀)}
    (h : IsAffineVariety k₀ f) : IsVariety k₀ f := by
  refine ⟨⟨1, fun _ => ⊤, by simp, fun _ => ?_⟩, h.facts.2.2.2⟩
  obtain ⟨A, _, _, hA, e, he⟩ := h
  exact ⟨A, inferInstance, inferInstance, hA, (Scheme.topIso X) ≪≫ e, by subst he; simp⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- A variety is reduced: the affine algebras $A$ of an affine cover embed in the reduced rings $k \otimes A$. -/
theorem IsVariety.isReduced {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k₀)} (h : IsVariety k₀ f) :
    IsReduced X := by
  obtain ⟨⟨n, U, hU, hA⟩, _⟩ := h
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (show x ∈ ⨆ i, U i by rw [hU]; trivial)
    have := (hA i).facts.1
    exact isReduced_of_injective _
      (asIso <| (U i).ι.stalkMap ⟨x, hi⟩).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

set_option backward.isDefEq.respectTransparency.types false in
/-- A variety is of finite type over $k_0$ (locally of finite type and quasi-compact). -/
theorem IsVariety.locallyOfFiniteType {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k₀)}
    (h : IsVariety k₀ f) : LocallyOfFiniteType f := by
  obtain ⟨⟨n, U, hU, hA⟩, _⟩ := h
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyOfFiniteType) U hU
    fun i => (hA i).facts.2.1

/-- A variety is quasi-compact over $k_0$ (finitely many affine opens). -/
theorem IsVariety.quasiCompact {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k₀)} (h : IsVariety k₀ f) :
    QuasiCompact f := by
  obtain ⟨⟨n, U, hU, hA⟩, _⟩ := h
  refine (quasiCompact_iff_compactSpace f).mpr ?_
  refine isCompact_univ_iff.mp ?_
  have hc : ∀ i, IsCompact (Set.range (U i).ι) := fun i => by
    have := (hA i).facts.2.2.1
    exact isCompact_range (U i).ι.continuous
  convert isCompact_iUnion hc using 1
  ext x
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (show x ∈ ⨆ i, U i by rw [hU]; trivial)
  simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
  exact ⟨i, ⟨x, hi⟩, rfl⟩

/-! ### Points with coordinates in an algebra -/

/-- **Points with coordinates in a $k_0$-algebra $R$** (Milne, Section 7, pdf p. 93; D088 to D090): $X(R)$ is the
set of morphisms $\operatorname{Spec} R \to X$ over $k_0$. For $R = k_0$ these are the points with coordinates in
$k_0$ (Milne: morphisms $\operatorname{Specm} k_0 \to X$). -/
@[kb "milne2017mf" "Section 7, points X(R) with coordinates in a k0-algebra R, and X(k0) (pdf p. 93)"]
def Points {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k₀)) (R : Type u) [CommRing R] [Algebra k₀ R] :
    Type u :=
  {p : Spec (CommRingCat.of R) ⟶ X // p ≫ f = specStructure k₀ R}

/-- For $X = \operatorname{Spec} A$, $X(R) = \operatorname{Hom}_{k_0\text{-alg}}(A, R)$ (Milne, Section 7, pdf p. 93). -/
@[kb "milne2017mf" "Section 7, X(R) = Hom(A, R) for X = Specm A (pdf p. 93)"]
def pointsSpecEquiv (A R : Type u) [CommRing A] [Algebra k₀ A] [CommRing R] [Algebra k₀ R] :
    Points k₀ (specStructure k₀ A) R ≃ (A →ₐ[k₀] R) :=
  Spec.homEquivAlgHom (R := k₀) (A := A) (B := R)

/-- For $A = k_0[X_1, \dots, X_n]/I$, a $k_0$-homomorphism $A \to R$ is the same as an $n$-tuple $(a_1, \dots, a_n)$
in $R$ with $f(a_1, \dots, a_n) = 0$ for every $f \in I$ (Milne, Section 7, pdf p. 93, for $R = k_0$ and
$I = (f_1, \dots, f_m)$: "a point of $X$ with coordinates in $k_0$ is exactly what you expect it to be"). -/
@[kb "milne2017mf" "Section 7, k0-points of k0[X1,...,Xn]/(f1,...,fm) are common zeros (pdf p. 93)"]
def algHomQuotientEquiv (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k₀)) (R : Type u) [CommRing R]
    [Algebra k₀ R] :
    (MvPolynomial (Fin n) k₀ ⧸ I →ₐ[k₀] R) ≃ {a : Fin n → R // ∀ g ∈ I, MvPolynomial.aeval a g = 0} where
  toFun φ := ⟨fun i => φ (Ideal.Quotient.mk I (MvPolynomial.X i)), fun g hg => by
    have h1 := congrArg (fun ψ : MvPolynomial (Fin n) k₀ →ₐ[k₀] R => ψ g)
      (MvPolynomial.aeval_unique (φ.comp (Ideal.Quotient.mkₐ k₀ I)))
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Function.comp_def] at h1
    rw [← h1, (Ideal.Quotient.eq_zero_iff_mem).mpr hg, map_zero]⟩
  invFun a := Ideal.Quotient.liftₐ I (MvPolynomial.aeval a.1) a.2
  left_inv φ := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    refine (Ideal.Quotient.lift_mk I _ _).trans (MvPolynomial.aeval_X _ _)
  right_inv a := by
    apply Subtype.ext
    funext i
    exact (Ideal.Quotient.lift_mk I _ _).trans (by simp)

/-! ### Residue fields and degrees of points -/

/-- The $k_0$-algebra structure of the residue field $\kappa(x)$ of a point of a $k_0$-scheme. -/
def residueAlgebraMap {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k₀)) (x : X) :
    k₀ →+* X.residueField x :=
  ((Scheme.ΓSpecIso (CommRingCat.of k₀)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom

/-- **Degree of a point** (Milne, Section 7, pdf p. 93; D092): the degree $[\kappa(v) : k_0]$ of the residue field
(Mathlib's `Scheme.residueField`, D091) over $k_0$; it is $0$ when the extension is infinite (Mathlib's `finrank`
convention; for varieties every point of $\operatorname{specm}$ has finite degree). -/
@[kb "milne2017mf" "Section 7, degree of a point (pdf p. 93)"]
def pointDegree {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k₀)) (x : X) : ℕ :=
  letI := (residueAlgebraMap k₀ f x).toAlgebra
  Module.finrank k₀ (X.residueField x)

/-- `κ(x) → X → Spec k₀` is `Spec` of the structure map `k₀ → κ(x)`. -/
lemma fromSpecResidueField_comp_eq {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k₀)) (x : X) :
    X.fromSpecResidueField x ≫ f = Spec.map (CommRingCat.ofHom (residueAlgebraMap k₀ f x)) := by
  have h : X.fromSpecResidueField x ≫ f = Spec.map (Spec.preimage (X.fromSpecResidueField x ≫ f)) :=
    (Spec.map_preimage _).symm
  rw [h]
  congr 1
  have h2 := Scheme.ΓSpecIso_naturality (Spec.preimage (X.fromSpecResidueField x ≫ f))
  rw [Spec.map_preimage] at h2
  rw [← Iso.inv_comp_eq] at h2
  rw [← h2]
  simp only [Scheme.Hom.comp_appTop, Scheme.fromSpecResidueField, Category.assoc]
  rw [Scheme.fromSpecStalk_appTop]
  simp [residueAlgebraMap]

/-- A ring map `q : κ(x) → k₀` is a retraction of the structure map iff `Spec q` followed by the canonical map is a
`k₀`-point. -/
lemma comp_eq_iff {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k₀)) (x : X)
    (q : X.residueField x ⟶ CommRingCat.of k₀) :
    (Spec.map q ≫ X.fromSpecResidueField x) ≫ f = specStructure k₀ k₀ ↔
      ∀ c, q.hom (residueAlgebraMap k₀ f x c) = c := by
  rw [Category.assoc, fromSpecResidueField_comp_eq, ← Spec.map_comp]
  unfold specStructure
  rw [Spec.map_inj]
  constructor
  · intro h c
    exact congrArg (fun g : CommRingCat.of k₀ ⟶ CommRingCat.of k₀ => g.hom c) h
  · intro h
    ext c
    exact h c

/-- If `q` retracts the structure map then `κ(x)` has degree one. -/
lemma degree_one_of_retraction {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k₀)) (x : X)
    (q : X.residueField x ⟶ CommRingCat.of k₀) (h : ∀ c, q.hom (residueAlgebraMap k₀ f x c) = c) :
    pointDegree k₀ f x = 1 := by
  letI := (residueAlgebraMap k₀ f x).toAlgebra
  have hsurj : Function.Surjective (algebraMap k₀ (X.residueField x)) := by
    intro y
    refine ⟨q.hom y, q.hom.injective ?_⟩
    exact h _
  have hbij : Function.Bijective (algebraMap k₀ (X.residueField x)) :=
    ⟨(algebraMap k₀ (X.residueField x)).injective, hsurj⟩
  have := (AlgEquiv.ofBijective (Algebra.ofId k₀ (X.residueField x)) hbij).toLinearEquiv.finrank_eq
  unfold pointDegree
  rw [← this]
  exact Module.finrank_self k₀

/-- In degree one the structure map is bijective. -/
lemma bijective_of_degree_one {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k₀)) (x : X)
    (h : pointDegree k₀ f x = 1) : Function.Bijective (residueAlgebraMap k₀ f x) := by
  letI := (residueAlgebraMap k₀ f x).toAlgebra
  refine ⟨(residueAlgebraMap k₀ f x).injective, fun y => ?_⟩
  have h1 : Module.finrank k₀ (X.residueField x) = 1 := h
  have := Subalgebra.bot_eq_top_of_finrank_eq_one (F := k₀) (E := X.residueField x) h1
  have hy : y ∈ (⊤ : Subalgebra k₀ (X.residueField x)) := trivial
  rw [← this, Algebra.mem_bot] at hy
  obtain ⟨c, hc⟩ := hy
  exact ⟨c, hc⟩

/-- Any two retractions of a surjective structure map agree. -/
lemma retraction_unique {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k₀)) (x : X)
    (hs : Function.Surjective (residueAlgebraMap k₀ f x))
    (q₁ q₂ : X.residueField x ⟶ CommRingCat.of k₀)
    (h₁ : ∀ c, q₁.hom (residueAlgebraMap k₀ f x c) = c)
    (h₂ : ∀ c, q₂.hom (residueAlgebraMap k₀ f x c) = c) : q₁ = q₂ := by
  ext y
  obtain ⟨c, rfl⟩ := hs y
  rw [h₁, h₂]

/-- The canonical retraction in degree one. -/
def retractionOfDegreeOne {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k₀)) (x : X)
    (h : pointDegree k₀ f x = 1) : X.residueField x ⟶ CommRingCat.of k₀ :=
  CommRingCat.ofHom (RingEquiv.ofBijective _ (bijective_of_degree_one k₀ f x h)).symm.toRingHom

/-- The canonical retraction retracts the structure map. -/
lemma retractionOfDegreeOne_spec {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k₀)) (x : X)
    (h : pointDegree k₀ f x = 1) (c : k₀) :
    (retractionOfDegreeOne k₀ f x h).hom (residueAlgebraMap k₀ f x c) = c :=
  (RingEquiv.ofBijective _ (bijective_of_degree_one k₀ f x h)).symm_apply_apply c

/-- **$X(k_0)$ is the set of points of degree $1$** (Milne, Section 7, pdf p. 93): a point with coordinates in $k_0$
is determined by its image $v$, which has $\kappa(v) = k_0$; conversely each point of degree $1$ is the image of
exactly one $k_0$-point. -/
@[kb "milne2017mf" "Section 7, X(k0) is identified with the points of degree 1 (pdf p. 93)"]
def pointsEquivDegreeOne {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k₀)) :
    Points k₀ f k₀ ≃ {x : X // pointDegree k₀ f x = 1} := by
  have valid : ∀ p : Points k₀ f k₀, ∀ c,
      ((Scheme.SpecToEquivOfField k₀ X p.1).2).hom
        (residueAlgebraMap k₀ f (Scheme.SpecToEquivOfField k₀ X p.1).1 c) = c := by
    intro p
    have e : p.1 = Spec.map (Scheme.SpecToEquivOfField k₀ X p.1).2 ≫
        X.fromSpecResidueField (Scheme.SpecToEquivOfField k₀ X p.1).1 :=
      ((Scheme.SpecToEquivOfField k₀ X).symm_apply_apply p.1).symm
    have := p.2
    rw [e] at this
    exact (comp_eq_iff k₀ f _ _).mp this
  refine
    { toFun := fun p => ⟨(Scheme.SpecToEquivOfField k₀ X p.1).1,
        degree_one_of_retraction k₀ f _ _ (valid p)⟩
      invFun := fun xh => ⟨Spec.map (retractionOfDegreeOne k₀ f xh.1 xh.2) ≫ X.fromSpecResidueField xh.1,
        (comp_eq_iff k₀ f _ _).mpr (retractionOfDegreeOne_spec k₀ f xh.1 xh.2)⟩
      left_inv := fun p => ?_
      right_inv := fun xh => ?_ }
  · apply Subtype.ext
    have e : p.1 = Spec.map (Scheme.SpecToEquivOfField k₀ X p.1).2 ≫
        X.fromSpecResidueField (Scheme.SpecToEquivOfField k₀ X p.1).1 :=
      ((Scheme.SpecToEquivOfField k₀ X).symm_apply_apply p.1).symm
    have hd := degree_one_of_retraction k₀ f _ _ (valid p)
    have key : retractionOfDegreeOne k₀ f _ hd = (Scheme.SpecToEquivOfField k₀ X p.1).2 :=
      retraction_unique k₀ f _ (bijective_of_degree_one k₀ f _ hd).2 _ _
        (retractionOfDegreeOne_spec k₀ f _ hd) (valid p)
    refine Eq.trans ?_ e.symm
    dsimp only
    rw [key]
  · apply Subtype.ext
    exact congrArg Sigma.fst ((Scheme.SpecToEquivOfField k₀ X).apply_symm_apply
      ⟨xh.1, retractionOfDegreeOne k₀ f xh.1 xh.2⟩)

/-! ### Function fields, dimension, regularity, completeness -/

/-- The $k_0$-algebra structure on the function field $k_0(X)$ of an integral $k_0$-scheme. -/
def functionFieldAlgebraMap {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k₀)) :
    k₀ →+* X.functionField :=
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  ((Scheme.ΓSpecIso (CommRingCat.of k₀)).inv ≫ f.appTop ≫ X.germToFunctionField ⊤).hom

/-- **Dimension of a variety** (Milne, Section 7, pdf p. 94; D093): the transcendence degree of the function field
$k_0(X)$ over $k_0$. Milne speaks of a connected variety with function field the field of fractions of any open
affine; that requires $X$ irreducible, and we take $X$ integral (reduced and irreducible). -/
@[kb "milne2017mf" "Section 7, dimension of a variety (pdf p. 94)"]
def dimension {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k₀)) : Cardinal.{u} :=
  letI := (functionFieldAlgebraMap k₀ f).toAlgebra
  Algebra.trdeg k₀ X.functionField

/-- **Algebraic curve** (Milne, Section 7, pdf p. 94): an (irreducible) algebraic variety of dimension $1$. -/
@[kb "milne2017mf" "Section 7, algebraic curve (pdf p. 94)"]
def IsCurve {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k₀)) : Prop :=
  IsVariety k₀ f ∧ dimension k₀ f = 1

/-- **Regular variety** (Milne, Section 7, pdf p. 94; D094): all the local rings $\mathcal O_v$, $v$ a point of
$\operatorname{specm}$, are regular local rings (Mathlib's `IsRegularLocalRing`). The points of Milne's varieties are
the closed points of the scheme. -/
@[kb "milne2017mf" "Section 7, regular variety (pdf p. 94)"]
def IsRegularVariety {X : Scheme.{u}} (_f : X ⟶ Spec (CommRingCat.of k₀)) : Prop :=
  ∀ x : X, IsClosed ({x} : Set X) → IsRegularLocalRing (X.presheaf.stalk x)

/-- **Complete variety** (Milne, Section 7, pdf p. 94, and Milne's *Algebraic Geometry*): a variety $X$ is complete
if $X \times Y \to Y$ is closed for every variety $Y$; in scheme language the structure morphism is universally closed
(with separated and of finite type, proper). For regular curves Milne characterizes completeness by the discrete
valuation rings of $k_0(X)$ (that characterization is part of the named statement `CurveFunctionFieldEquivalence`). -/
@[kb "milne2017mf" "Section 7, complete variety (pdf p. 94)"]
def IsComplete {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k₀)) : Prop :=
  UniversallyClosed f

/-- **Function field in $n$ variables over $k_0$** (Milne, Section 7, pdf p. 94; D095): a field $K \supseteq k_0$
that is finitely generated (as a field) and of transcendence degree $n$ over $k_0$. -/
@[kb "milne2017mf" "Section 7, function field in n variables over k0 (pdf p. 94)"]
def IsFunctionFieldIn (n : ℕ) (K : Type u) [Field K] [Algebra k₀ K] : Prop :=
  (⊤ : IntermediateField k₀ K).FG ∧ Algebra.trdeg k₀ K = n

/-- **Field of constants** (Milne, Section 7, pdf p. 94; D095): the algebraic closure of $k_0$ in $K$. -/
@[kb "milne2017mf" "Section 7, field of constants of a function field (pdf p. 94)"]
abbrev fieldOfConstants (K : Type u) [Field K] [Algebra k₀ K] : IntermediateField k₀ K :=
  algebraicClosure k₀ K

end ModularFormsKB.Milne
