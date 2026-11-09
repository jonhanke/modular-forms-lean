import ModularFormsKB.Milne.Ch8.EllipticModuli

/-!
# Milne, Chapter 8: the j-line, condition (a) of Theorem 8.4

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 8, Theorem 8.4, proof of
condition (a) (pdf p. 98).

For a variety $T$ over $k$ and a family of elliptic curves $E$ over $T$, the $j$-invariant $j(E)$ is a regular function
on $T$ (Tau Ceti's `EllipticCurveGeom.j`), hence defines a regular map $\varphi : T \to \mathbb A^1$, and it is
compatible with base change (`EllipticCurveGeom.j_baseChange`). So for $t \in T(k)$ the point $t \circ \varphi$ of
$\mathbb A^1$ has coordinate $j(E_t)$.

## Items

- `Scheme.hom_ext_spec`: morphisms to an affine scheme are determined by their effect on global sections.
- `mapToAffineLine`: the morphism $T \to \mathbb A^1$ attached to a global function.
- **Theorem 8.4, condition (a)**: `ellipticFunctor_regular`.
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite TauCeti.AlgebraicGeometry

noncomputable section

namespace ModularFormsKB.Milne

/-- Morphisms into an affine scheme $\operatorname{Spec} R$ are determined by their maps on global sections. -/
theorem Scheme.hom_ext_spec {X : Scheme.{u}} {R : CommRingCat.{u}} {f g : X ⟶ Spec R}
    (h : f.appTop = g.appTop) : f = g := by
  have : IsIso (Spec R).toSpecΓ := inferInstance
  rw [← cancel_mono (Spec R).toSpecΓ, Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, h]

variable {k : Type u} [Field k]

/-- The ring homomorphism $k[X] \to \Gamma(T, \top)$ sending $X$ to a given global function $j$ and constants through
the $k$-structure of $T$. -/
def lineRingHom (T : Variety k) (j : Γ(T.obj.left, ⊤)) :
    CommRingCat.of (Polynomial k) ⟶ Γ(T.obj.left, ⊤) :=
  CommRingCat.ofHom (Polynomial.eval₂RingHom
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ T.obj.hom.appTop).hom) j)

/-- The morphism of schemes $T \to \operatorname{Spec} k[X]$ with coordinate a global function $j$. -/
def lineMap (T : Variety k) (j : Γ(T.obj.left, ⊤)) : T.obj.left ⟶ Spec (CommRingCat.of (Polynomial k)) :=
  ΓSpec.adjunction.homEquiv T.obj.left (op (CommRingCat.of (Polynomial k))) (lineRingHom T j).op

theorem lineMap_appTop (T : Variety k) (j : Γ(T.obj.left, ⊤)) :
    (lineMap T j).appTop = (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).hom ≫ lineRingHom T j :=
  ΓSpec_adjunction_homEquiv_eq _

theorem lineMap_over (T : Variety k) (j : Γ(T.obj.left, ⊤)) :
    lineMap T j ≫ specStructure k (Polynomial k) = T.obj.hom := by
  apply Scheme.hom_ext_spec
  rw [Scheme.Hom.comp_appTop, lineMap_appTop, specStructure]
  have h : CommRingCat.ofHom (algebraMap k (Polynomial k)) ≫ lineRingHom T j =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ T.obj.hom.appTop := by
    ext x
    simp [lineRingHom]
  rw [Scheme.ΓSpecIso_naturality_assoc, h, Iso.hom_inv_id_assoc]

/-- The morphism $T \to \mathbb A^1$ with coordinate a global function $j$. -/
def mapToAffineLine (T : Variety k) (j : Γ(T.obj.left, ⊤)) : T ⟶ affineLine k :=
  ObjectProperty.homMk (Over.homMk (lineMap T j) (lineMap_over T j))

theorem mapToAffineLine_coordinate (T : Variety k) (j : Γ(T.obj.left, ⊤)) :
    (mapToAffineLine T j).hom.left.appTop (affineLineCoordinate k) = j := by
  change (lineMap T j).appTop (affineLineCoordinate k) = j
  rw [lineMap_appTop]
  simp [affineLineCoordinate, lineRingHom]

/-- For a moduli problem $\mathcal P$, every class in $(\text{levelFunctor } \mathcal P)(T)$ has a regular map
$T \to \mathbb A^1$ given by its $j$-invariant, compatible with $k$-points. -/
theorem levelFunctor_regular (P : ModuliProblem (Spec (CommRingCat.of k))) (T : Variety k)
    (f : (levelFunctor P).obj (op T)) :
    ∃ φ : T ⟶ affineLine k, ∀ t : Variety.point k ⟶ T,
      (t ≫ φ).hom.left.appTop (affineLineCoordinate k) = jClass ((levelFunctor P).map t.op f) := by
  induction f using Quotient.inductionOn with
  | h x =>
  refine ⟨mapToAffineLine T x.1.j, fun t => ?_⟩
  have h1 : (t ≫ mapToAffineLine T x.1.j).hom.left.appTop (affineLineCoordinate k) =
      t.hom.left.appTop ((mapToAffineLine T x.1.j).hom.left.appTop (affineLineCoordinate k)) := by
    rfl
  rw [h1, mapToAffineLine_coordinate]
  change _ = (x.1.baseChange t.hom.left).j
  rw [EllipticCurveGeom.j_baseChange]

/-- **Milne, Theorem 8.4, condition (a)** (pdf p. 98): for every variety $T$ and every family
$f \in \mathcal E(T)$ of elliptic curves over $T$ there is a regular map $\varphi : T \to \mathbb A^1$ whose value at
each $t \in T(k)$ is the point with coordinate $j(E_t)$, $E_t$ the fibre of $f$ at $t$. -/
@[kb "milne2017mf" "Section 8, Theorem 8.4, proof of condition (a) (pdf p. 98)"]
theorem ellipticFunctor_regular (T : Variety k) (f : (ellipticFunctor k).obj (Opposite.op T)) :
    ∃ φ : T ⟶ affineLine k, ∀ t : Variety.point k ⟶ T,
      (t ≫ φ).hom.left.appTop (affineLineCoordinate k) = jClass ((ellipticFunctor k).map t.op f) :=
  levelFunctor_regular _ T f

end ModularFormsKB.Milne
