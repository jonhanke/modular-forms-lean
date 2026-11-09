import Mathlib
import TauCeti.FieldTheory.FunctionField.Basic
import TauCeti.FieldTheory.FunctionField.Place.Basic
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Order
import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
import ModularFormsKB.Citation
/-!
# Milne, Introduction ("Chapter 0"): Riemann surfaces and plane algebraic curves

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Introduction, pdf pp. 5–9.

* Definitions in running text (p. 8): affine plane algebraic curves (D006) with their points `C(K)`, ring of regular
  functions `k[C] = k[X, Y]/(f)` and field of rational functions; nonsingular plane curves (D008); projective plane
  curves (D010) with their points in `ℙ²(K)`, homogeneous coordinate ring and nonsingularity.
* Theorem 0.1 (uniformization): named statement; the part proved in the book (the three surfaces are pairwise
  non-isomorphic) is a named statement too, see `UniformizationStatement`.
* Proposition 0.4: the complex structure on the points of a nonsingular affine plane curve over `ℂ` (named statement:
  the book's proof uses the holomorphic implicit function theorem, and building the atlas is not done here).
* Theorem 0.5 (named statement, in the function-field form; see the docstring for the deviation).

Riemann surfaces are types with `[ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]`; the Riemann sphere is `OnePoint ℂ` (with
Tau Ceti's complex structure), the open unit disk is the open subset `Metric.ball (0 : ℂ) 1` of `ℂ`. Isomorphisms of
Riemann surfaces are bijections, holomorphic with holomorphic inverse (Milne, p. 16).

Indices: the variables `X, Y` (resp. `X, Y, Z`) of the book are `MvPolynomial.X 0, X 1` (resp. `X 0, X 1, X 2`).
-/

open MvPolynomial
open scoped LinearAlgebra.Projectivization
open scoped Manifold

namespace ModularFormsKB.Milne

/-! ### Isomorphisms of Riemann surfaces -/

/-- **Isomorphic Riemann surfaces** (Milne, p. 16): there is a bijection `X → Y`, holomorphic with holomorphic
inverse. -/
@[kb "milne2017mf" "§1, isomorphism of Riemann surfaces, pdf p. 16"]
def RiemannSurfaceIso (X Y : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
    [ChartedSpace ℂ Y] : Prop :=
  ∃ e : X ≃ Y, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e.symm

/-- The open unit disk `D = {z ∈ ℂ | |z| < 1}` as an open subset of `ℂ` (a Riemann surface with one chart). -/
noncomputable def unitDiskOpens : TopologicalSpace.Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

/-! ### Theorem 0.1 -/

/-- **Milne, Theorem 0.1 (uniformization)** (named statement): every simply connected Riemann surface is isomorphic to
exactly one of the Riemann sphere, `ℂ`, and the open unit disk. The book refers to the literature (Forster,
Farkas–Kra) for the existence part; its proof that the three are pairwise non-isomorphic is
`riemannSurfaceIso_distinct`. -/
@[kb "milne2017mf" "Theorem 0.1 (uniformization), pdf p. 5"]
structure UniformizationStatement : Prop where
  out : ∀ (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X], SimplyConnectedSpace X →
    RiemannSurfaceIso X (OnePoint ℂ) ∨ RiemannSurfaceIso X ℂ ∨ RiemannSurfaceIso X unitDiskOpens

theorem RiemannSurfaceIso.symm' {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
    [ChartedSpace ℂ Y] (h : RiemannSurfaceIso X Y) : RiemannSurfaceIso Y X := by
  obtain ⟨e, h1, h2⟩ := h
  exact ⟨e.symm, h2, by simpa using h1⟩

theorem RiemannSurfaceIso.trans' {X Y Z : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
    [ChartedSpace ℂ Y] [TopologicalSpace Z] [ChartedSpace ℂ Z] (h : RiemannSurfaceIso X Y)
    (h' : RiemannSurfaceIso Y Z) : RiemannSurfaceIso X Z := by
  obtain ⟨e, h1, h2⟩ := h
  obtain ⟨e', h1', h2'⟩ := h'
  exact ⟨e.trans e', h1'.comp h1, by simpa using h2.comp h2'⟩

theorem RiemannSurfaceIso.compact_iff {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
    [ChartedSpace ℂ Y] (h : RiemannSurfaceIso X Y) : CompactSpace X ↔ CompactSpace Y := by
  obtain ⟨e, h1, h2⟩ := h
  let E : X ≃ₜ Y := ⟨e, h1.continuous, h2.continuous⟩
  exact ⟨fun hX => by have := hX; exact E.compactSpace,
    fun hY => by have := hY; exact E.symm.compactSpace⟩

theorem not_compact_disk : ¬ CompactSpace unitDiskOpens := by
  intro h
  have hc : IsCompact (Set.range (Subtype.val : unitDiskOpens → ℂ)) :=
    isCompact_range continuous_subtype_val
  have : Set.range (Subtype.val : unitDiskOpens → ℂ) = Metric.ball 0 1 := by
    ext z; simp [unitDiskOpens]
  rw [this] at hc
  have hcl := hc.isClosed
  have : closure (Metric.ball (0:ℂ) 1) = Metric.closedBall 0 1 := closure_ball _ one_ne_zero
  rw [hcl.closure_eq] at this
  have h1 : (1 : ℂ) ∈ Metric.closedBall (0:ℂ) 1 := by simp
  rw [← this] at h1
  simp at h1

theorem not_iso_complex_disk : ¬ RiemannSurfaceIso ℂ unitDiskOpens := by
  rintro ⟨e, h1, h2⟩
  have hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : ℂ => (e z : ℂ)) :=
    ((contMDiff_subtype_val (I := 𝓘(ℂ)) (n := 1) (U := unitDiskOpens)).mdifferentiable
      (by simp)).comp h1
  have hd : Differentiable ℂ (fun z : ℂ => (e z : ℂ)) := mdifferentiable_iff_differentiable.mp hf
  have hb : Bornology.IsBounded (Set.range (fun z : ℂ => (e z : ℂ))) := by
    refine (Metric.isBounded_ball (x := (0:ℂ)) (r := 1)).subset ?_
    rintro _ ⟨z, rfl⟩
    exact (e z).2
  have := hd.apply_eq_apply_of_bounded hb 0 1
  have := e.injective (Subtype.ext this)
  simp at this

/-- **Milne, Theorem 0.1** (the part proved in the book): the Riemann sphere, `ℂ` and the open unit disk are pairwise
non-isomorphic. Only the sphere is compact; an isomorphism `ℂ → D` would be a bounded entire function, hence
constant (Liouville). -/
@[kb "milne2017mf" "Theorem 0.1, proof: the three surfaces are distinct, pdf p. 5"]
theorem riemannSurfaceIso_distinct :
    ¬ RiemannSurfaceIso (OnePoint ℂ) ℂ ∧ ¬ RiemannSurfaceIso (OnePoint ℂ) unitDiskOpens ∧
      ¬ RiemannSurfaceIso ℂ unitDiskOpens := by
  refine ⟨fun h => ?_, fun h => ?_, not_iso_complex_disk⟩
  · have := h.compact_iff.mp inferInstance
    exact not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℂ) this
  · exact not_compact_disk (h.compact_iff.mp inferInstance)

/-- **Milne, Theorem 0.1**, from the named existence statement: every simply connected Riemann surface is isomorphic
to exactly one of the three. -/
@[kb "milne2017mf" "Theorem 0.1 (uniformization), pdf p. 5"]
theorem uniformization_exactly_one (h : UniformizationStatement) (X : Type) [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] (hX : SimplyConnectedSpace X) :
    (RiemannSurfaceIso X (OnePoint ℂ) ∧ ¬ RiemannSurfaceIso X ℂ ∧ ¬ RiemannSurfaceIso X unitDiskOpens) ∨
    (¬ RiemannSurfaceIso X (OnePoint ℂ) ∧ RiemannSurfaceIso X ℂ ∧ ¬ RiemannSurfaceIso X unitDiskOpens) ∨
    (¬ RiemannSurfaceIso X (OnePoint ℂ) ∧ ¬ RiemannSurfaceIso X ℂ ∧ RiemannSurfaceIso X unitDiskOpens) := by
  obtain ⟨d1, d2, d3⟩ := riemannSurfaceIso_distinct
  have n1 : RiemannSurfaceIso X (OnePoint ℂ) → ¬ RiemannSurfaceIso X ℂ := fun a b =>
    d1 (a.symm'.trans' b)
  have n2 : RiemannSurfaceIso X (OnePoint ℂ) → ¬ RiemannSurfaceIso X unitDiskOpens := fun a b =>
    d2 (a.symm'.trans' b)
  have n3 : RiemannSurfaceIso X ℂ → ¬ RiemannSurfaceIso X unitDiskOpens := fun a b =>
    d3 (a.symm'.trans' b)
  rcases h.out X hX with a | a | a
  · exact Or.inl ⟨a, n1 a, n2 a⟩
  · exact Or.inr (Or.inl ⟨fun b => n1 b a, a, n3 a⟩)
  · exact Or.inr (Or.inr ⟨fun b => n2 b a, fun b => n3 b a, a⟩)

/-! ### Affine plane curves (D006, D008) -/

section Affine

variable {k : Type*} [Field k]

/-- **Affine plane algebraic curve** (Milne, p. 8): a curve `C` over `k` is given by a nonzero polynomial
`f(X, Y) ∈ k[X, Y]`. -/
@[kb "milne2017mf" "Introduction: affine plane algebraic curve, pdf p. 8"]
structure AffinePlaneCurve (k : Type*) [Field k] where
  /-- The defining polynomial `f(X, Y)`. -/
  f : MvPolynomial (Fin 2) k
  ne_zero : f ≠ 0

namespace AffinePlaneCurve

/-- The points `C(K)` of `C` with coordinates in a field `K ⊇ k`: the zeros of `f` in `K × K`. -/
@[kb "milne2017mf" "Introduction: the points C(K) of an affine plane curve, pdf p. 8"]
def points (C : AffinePlaneCurve k) (K : Type*) [Field K] [Algebra k K] : Set (K × K) :=
  {p | aeval ![p.1, p.2] C.f = 0}

/-- The ring of regular functions `k[C] = k[X, Y]/(f(X, Y))` (Milne, p. 8). -/
@[kb "milne2017mf" "Introduction: ring of regular functions k[C], pdf p. 8"]
abbrev coordinateRing (C : AffinePlaneCurve k) : Type _ :=
  MvPolynomial (Fin 2) k ⧸ Ideal.span {C.f}

/-- For irreducible `f`, the ring of regular functions is an integral domain. -/
theorem isDomain_coordinateRing (C : AffinePlaneCurve k) (hf : Irreducible C.f) :
    IsDomain C.coordinateRing :=
  (Ideal.Quotient.isDomain_iff_prime _).2 ((Ideal.span_singleton_prime C.ne_zero).2 hf.prime)

/-- The field of rational functions `k(C)`, the field of fractions of `k[C]` for irreducible `f` (Milne, p. 8). -/
@[kb "milne2017mf" "Introduction: field of rational functions k(C), pdf p. 8"]
abbrev functionField (C : AffinePlaneCurve k) (hf : Irreducible C.f) : Type _ :=
  letI := C.isDomain_coordinateRing hf
  FractionRing C.coordinateRing

/-- A **singular point** of `C` over `K` (Milne, p. 8): a point where `f`, `∂f/∂X` and `∂f/∂Y` all vanish. -/
@[kb "milne2017mf" "Introduction: singular point of a plane curve, pdf p. 8"]
def IsSingularPoint (C : AffinePlaneCurve k) {K : Type*} [Field K] [Algebra k K] (p : K × K) : Prop :=
  aeval ![p.1, p.2] C.f = 0 ∧ aeval ![p.1, p.2] (pderiv 0 C.f) = 0 ∧ aeval ![p.1, p.2] (pderiv 1 C.f) = 0

/-- **Nonsingular** affine plane curve (Milne, p. 8, D008): `f`, `∂f/∂X`, `∂f/∂Y` have no common zero in the
algebraic closure of `k`. -/
@[kb "milne2017mf" "Introduction: nonsingular affine plane curve, pdf p. 8"]
def IsNonsingular (C : AffinePlaneCurve k) : Prop :=
  ∀ p : AlgebraicClosure k × AlgebraicClosure k, ¬ C.IsSingularPoint p

end AffinePlaneCurve

end Affine

/-! ### Proposition 0.4 -/

/-- **Milne, Proposition 0.4** (named statement): for a nonsingular affine plane curve `C` over `ℂ`, the set `C(ℂ)`
(with the topology from `ℂ²`) has a natural structure of Riemann surface: near a point `P` with `(∂f/∂Y)(P) ≠ 0` the
projection `(x, y) ↦ x` is a chart, and near a point with `(∂f/∂X)(P) ≠ 0` the projection `(x, y) ↦ y` is a chart.
Recorded as: there is a complex structure on `C(ℂ)` such that, at every point, the chart is the restriction of one of
the two projections, the first one whenever `∂f/∂Y ≠ 0` there. (Over `ℂ` the algebraic closure is `ℂ` itself, so
nonsingularity is used through `AlgebraicClosure ℂ ≃ ℂ`.) -/
@[kb "milne2017mf" "Proposition 0.4, pdf p. 8"]
structure PlaneCurveRiemannSurfaceStatement : Prop where
  out : ∀ C : AffinePlaneCurve ℂ, C.IsNonsingular →
    ∃ (_ : ChartedSpace ℂ (C.points ℂ)), IsManifold 𝓘(ℂ) 1 (C.points ℂ) ∧
      ∀ P : C.points ℂ, (aeval ![P.1.1, P.1.2] (pderiv 1 C.f) ≠ 0 →
          Set.EqOn (chartAt ℂ P) (fun Q ↦ Q.1.1) (chartAt ℂ P).source) ∧
        (aeval ![P.1.1, P.1.2] (pderiv 1 C.f) = 0 →
          Set.EqOn (chartAt ℂ P) (fun Q ↦ Q.1.2) (chartAt ℂ P).source)

/-! ### Projective plane curves (D010) -/

section Projective

variable {k : Type*} [Field k]

/-- **Projective plane curve** (Milne, p. 8): given by a nonconstant homogeneous polynomial `F(X, Y, Z)`. -/
@[kb "milne2017mf" "Introduction: projective plane curve, pdf p. 8"]
structure ProjectivePlaneCurve (k : Type*) [Field k] where
  /-- The defining polynomial `F(X, Y, Z)`. -/
  F : MvPolynomial (Fin 3) k
  /-- Its degree `m ≥ 1`. -/
  m : ℕ
  isHomogeneous : F.IsHomogeneous m
  ne_zero : F ≠ 0
  pos : 0 < m

namespace ProjectivePlaneCurve

/-- `F(cx, cy, cz) = c^m F(x, y, z)` (Milne, p. 8), so the vanishing of `F` at a point of `ℙ²` is well defined. -/
theorem aeval_smul (C : ProjectivePlaneCurve k) {K : Type*} [Field K] [Algebra k K] (c : K) (v : Fin 3 → K) :
    aeval (c • v) C.F = c ^ C.m * aeval v C.F := by
  have hF := C.isHomogeneous
  conv_lhs => rw [C.F.as_sum]
  conv_rhs => rw [C.F.as_sum]
  simp only [map_sum, Finset.mul_sum, aeval_monomial]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdm : ∑ i, d i = C.m := by
    have := hF (mem_support_iff.mp hd)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at this
    simpa using this
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, hdm]
  ring

/-- The points `C(K) ⊆ ℙ²(K)` of `C` with coordinates in `K ⊇ k` (Milne, p. 8). -/
@[kb "milne2017mf" "Introduction: the points C(K) of a projective plane curve, pdf p. 8"]
def points (C : ProjectivePlaneCurve k) (K : Type*) [Field K] [Algebra k K] :
    Set (ℙ K (Fin 3 → K)) :=
  {p | aeval p.rep C.F = 0}

/-- A point `[v]` lies on `C` if and only if `F(v) = 0`, for any representative `v`. -/
theorem mk_mem_points_iff (C : ProjectivePlaneCurve k) {K : Type*} [Field K] [Algebra k K] (v : Fin 3 → K)
    (hv : v ≠ 0) : Projectivization.mk K v hv ∈ C.points K ↔ aeval v C.F = 0 := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  simp only [points, Set.mem_ofPred_eq]
  rw [← hc, show (c • v) = ((c : K) • v) from rfl, aeval_smul]
  simp [c.ne_zero]

/-- The homogeneous coordinate ring `k[C] = k[X, Y, Z]/(F)` (Milne, p. 8). -/
@[kb "milne2017mf" "Introduction: homogeneous coordinate ring of a projective plane curve, pdf p. 8"]
abbrev homogeneousCoordinateRing (C : ProjectivePlaneCurve k) : Type _ :=
  MvPolynomial (Fin 3) k ⧸ Ideal.span {C.F}

/-- The field of rational functions `k(C)` of an irreducible projective plane curve (Milne, p. 8): the quotients
`G/H` of homogeneous polynomials of the same degree with `F ∤ H`, as a subfield of the field of fractions of
`k[C]`. -/
@[kb "milne2017mf" "Introduction: field of rational functions of a projective plane curve, pdf p. 8"]
noncomputable def functionField (C : ProjectivePlaneCurve k) (hF : Irreducible C.F) :
    letI : IsDomain C.homogeneousCoordinateRing :=
      (Ideal.Quotient.isDomain_iff_prime _).2 ((Ideal.span_singleton_prime C.ne_zero).2 hF.prime)
    Subfield (FractionRing C.homogeneousCoordinateRing) :=
  letI : IsDomain C.homogeneousCoordinateRing :=
    (Ideal.Quotient.isDomain_iff_prime _).2 ((Ideal.span_singleton_prime C.ne_zero).2 hF.prime)
  Subfield.closure {x | ∃ (d : ℕ) (G H : MvPolynomial (Fin 3) k), G.IsHomogeneous d ∧ H.IsHomogeneous d ∧
    (Ideal.Quotient.mk (Ideal.span {C.F}) H : C.homogeneousCoordinateRing) ≠ 0 ∧
    x = algebraMap C.homogeneousCoordinateRing _ (Ideal.Quotient.mk (Ideal.span {C.F}) G) /
      algebraMap C.homogeneousCoordinateRing _ (Ideal.Quotient.mk (Ideal.span {C.F}) H)}

/-- The three affine pieces `C_X, C_Y, C_Z` given by `F(1, Y, Z)`, `F(X, 1, Z)`, `F(X, Y, 1)` (Milne, p. 9),
as polynomials in the two remaining variables (in their order). -/
noncomputable def affinePiece (C : ProjectivePlaneCurve k) (i : Fin 3) : MvPolynomial (Fin 2) k :=
  aeval (![![1, X 0, X 1], ![X 0, 1, X 1], ![X 0, X 1, 1]] i : Fin 3 → MvPolynomial (Fin 2) k) C.F

/-- **Nonsingular** projective plane curve (Milne, p. 9): `F`, `∂F/∂X`, `∂F/∂Y`, `∂F/∂Z` have no common nonzero
zero in the algebraic closure of `k`. (The book defines it as nonsingularity of the three affine pieces and states
the equivalence with this criterion.) -/
@[kb "milne2017mf" "Introduction: nonsingular projective plane curve, pdf p. 9"]
def IsNonsingular (C : ProjectivePlaneCurve k) : Prop :=
  ∀ v : Fin 3 → AlgebraicClosure k, v ≠ 0 →
    ¬ (aeval v C.F = 0 ∧ ∀ i, aeval v (pderiv i C.F) = 0)

end ProjectivePlaneCurve

end Projective

/-! ### Theorem 0.5 -/

/-- **Milne, Theorem 0.5** (named statement, function-field form). Every compact Riemann surface `S` is `C(ℂ)` for a
nonsingular projective curve `C` over `ℂ`, unique up to isomorphism, with `ℂ(C)` the field of meromorphic functions
on `S`. Deviation: Mathlib has no analytic space `C(ℂ)` of a complex projective variety, so the theorem is recorded
through its equivalent algebraic content (the curve `C` being determined by its function field, Milne §0 and the
discussion after Theorem 1.17): (a) the meromorphic functions `M(S)` form an algebraic function field of one variable
over `ℂ` (Tau Ceti's `TauCeti.IsFunctionField`); (b) the points of `S` correspond bijectively to the places of
`M(S)/ℂ` (the points of `C`), by `x ↦ ord_x`; (c) two compact Riemann surfaces are isomorphic if and only if their
fields of meromorphic functions are `ℂ`-isomorphic (uniqueness of `C`). -/
@[kb "milne2017mf" "Theorem 0.5, pdf p. 9"]
structure CompactRiemannSurfaceAlgebraicStatement : Prop where
  isFunctionField : ∀ (S : Type) [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) 1 S] [CompactSpace S]
    [ConnectedSpace S] [T2Space S], TauCeti.IsFunctionField ℂ (TauCeti.RiemannSurface.MeromorphicFunction S)
  places : ∀ (S : Type) [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) 1 S] [CompactSpace S]
    [ConnectedSpace S] [T2Space S],
    (∀ x : S, ∃ P : TauCeti.Place ℂ (TauCeti.RiemannSurface.MeromorphicFunction S), ∀ f, f ≠ 0 →
      P.valuation f = WithZero.exp (-(TauCeti.RiemannSurface.MeromorphicFunction.order x f).untop₀)) ∧
    ∀ P : TauCeti.Place ℂ (TauCeti.RiemannSurface.MeromorphicFunction S), ∃! x : S, ∀ f, f ≠ 0 →
      P.valuation f = WithZero.exp (-(TauCeti.RiemannSurface.MeromorphicFunction.order x f).untop₀)
  iso_iff : ∀ (S S' : Type) [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) 1 S] [CompactSpace S]
    [ConnectedSpace S] [T2Space S] [TopologicalSpace S'] [ChartedSpace ℂ S'] [IsManifold 𝓘(ℂ) 1 S']
    [CompactSpace S'] [ConnectedSpace S'] [T2Space S'],
    RiemannSurfaceIso S S' ↔ Nonempty (TauCeti.RiemannSurface.MeromorphicFunction S ≃ₐ[ℂ]
      TauCeti.RiemannSurface.MeromorphicFunction S')

end ModularFormsKB.Milne
