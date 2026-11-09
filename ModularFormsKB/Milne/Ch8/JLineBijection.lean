import ModularFormsKB.Milne.Ch8.JLine
import ModularFormsKB.Milne.Ch8.LegendreCounterexample
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ

/-!
# Milne, Chapter 8: the bijection $\mathcal E(k) \to \mathbb A^1(k)$ of Theorem 8.4

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 8, Theorem 8.4 and its proof
(pdf p. 98).

Over an algebraically closed field $k$, an elliptic curve over $\operatorname{Spec} k$ is the curve of a Weierstrass
equation (Tau Ceti's `EllipticCurveGeom.exists_iso_toEllipticCurveGeom`, over a local ring), two Weierstrass curves
with the same $j$-invariant differ by a change of variables (Mathlib's
`WeierstrassCurve.exists_variableChange_of_j_eq`), and every $j \in k$ occurs (Mathlib's `WeierstrassCurve.ofJ`). So
$E \mapsto j(E)$ is a bijection from isomorphism classes to $k = \mathbb A^1(k)$.

## Items

- `linePoint c`: the point of $\mathbb A^1$ with coordinate $c$; `pointCoord`; `point_ext` (points of $\mathbb A^1$
  are determined by their coordinate).
- `jPoint`: the class of $E$ goes to the point with coordinate $j(E)$; `jPoint_bijective`; `jEquiv`.
- `jEquiv_map`: for a family $f$ over $T$ and $t \in T(k)$, $\alpha(f_t) = t \circ \varphi_f$, $\varphi_f$ the
  $j$-map of the family (condition (a) of Definition 8.1 for $(\mathbb A^1, \alpha)$: `jEquiv_regular`).
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite TauCeti.AlgebraicGeometry MonoidalCategory

noncomputable section

namespace ModularFormsKB.Milne

variable {k : Type u} [Field k]

/-- The point of $\mathbb A^1$ with coordinate $c$. -/
def linePoint (c : k) : Variety.point k ⟶ affineLine k :=
  mapToAffineLine (Variety.point k) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)

/-- The coordinate of a point of $\mathbb A^1$. -/
def pointCoord (v : Variety.point k ⟶ affineLine k) : k :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).hom (v.hom.left.appTop (affineLineCoordinate k))

theorem appTop_linePoint (c : k) :
    (linePoint c).hom.left.appTop (affineLineCoordinate k) = (Scheme.ΓSpecIso (CommRingCat.of k)).inv c :=
  mapToAffineLine_coordinate _ _

@[simp]
theorem pointCoord_linePoint (c : k) : pointCoord (linePoint c) = c := by
  rw [pointCoord, appTop_linePoint]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of k)).inv_hom_id c

/-- Points of $\mathbb A^1$ are determined by the image of the coordinate. -/
theorem spec_line_ext {X : Scheme.{u}} {s : X ⟶ Spec (CommRingCat.of k)}
    {f g : X ⟶ Spec (CommRingCat.of (Polynomial k))}
    (hf : f ≫ specStructure k (Polynomial k) = s) (hg : g ≫ specStructure k (Polynomial k) = s)
    (h : f.appTop (affineLineCoordinate k) = g.appTop (affineLineCoordinate k)) : f = g := by
  refine Scheme.hom_ext_spec ?_
  rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv]
  ext1
  refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
  · have e1 := congrArg Scheme.Hom.appTop hf
    have e2 := congrArg Scheme.Hom.appTop hg
    rw [Scheme.Hom.comp_appTop] at e1 e2
    have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (Polynomial k)))
    have n' : (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv (algebraMap k (Polynomial k) a) =
        (specStructure k (Polynomial k)).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a) :=
      ConcreteCategory.congr_hom n a
    change f.appTop ((Scheme.ΓSpecIso _).inv (Polynomial.C a)) =
      g.appTop ((Scheme.ΓSpecIso _).inv (Polynomial.C a))
    rw [show Polynomial.C a = algebraMap k (Polynomial k) a from rfl, n']
    change ((specStructure k (Polynomial k)).appTop ≫ f.appTop) _ =
      ((specStructure k (Polynomial k)).appTop ≫ g.appTop) _
    rw [e1, e2]
  · exact h

theorem point_ext {v w : Variety.point k ⟶ affineLine k}
    (h : v.hom.left.appTop (affineLineCoordinate k) = w.hom.left.appTop (affineLineCoordinate k)) : v = w :=
  InducedCategory.hom_ext (Over.OverMorphism.ext
    (spec_line_ext (s := 𝟙 _) (Over.w v.hom) (Over.w w.hom) h))

theorem point_ext_coord {v w : Variety.point k ⟶ affineLine k} (h : pointCoord v = pointCoord w) : v = w := by
  exact point_ext ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.injective h)

/-- **The map $\alpha$ of Theorem 8.4**: the class of $E$ goes to the point of $\mathbb A^1$ with coordinate
$j(E)$. -/
def jPoint (x : (ellipticFunctor k).obj (op (Variety.point k))) : Variety.point k ⟶ affineLine k :=
  mapToAffineLine (Variety.point k) (jClass x)

theorem appTop_jPoint (x : (ellipticFunctor k).obj (op (Variety.point k))) :
    (jPoint x).hom.left.appTop (affineLineCoordinate k) = jClass x :=
  mapToAffineLine_coordinate _ _

/-- The class of the curve of an elliptic Weierstrass curve over $k$. -/
def weierstrassClass (W : WeierstrassCurve k) [W.IsElliptic] : (ellipticFunctor k).obj (op (Variety.point k)) :=
  Quotient.mk _ (⟨W.toEllipticCurveGeom, PUnit.unit⟩ : LevelPair _ (Variety.point k))

theorem jClass_weierstrassClass (W : WeierstrassCurve k) [W.IsElliptic] :
    jClass (weierstrassClass W) = (Scheme.ΓSpecIso (CommRingCat.of k)).inv W.j :=
  WeierstrassCurve.j_toEllipticCurveGeom W

/-- Every class over $\operatorname{Spec} k$ is the class of a Weierstrass curve. -/
theorem exists_weierstrassClass (x : (ellipticFunctor k).obj (op (Variety.point k))) :
    ∃ (W : WeierstrassCurve k) (_ : W.IsElliptic), weierstrassClass W = x := by
  induction x using Quotient.inductionOn with
  | h x =>
  obtain ⟨W, hW, e, he, h0⟩ := EllipticCurveGeom.exists_iso_toEllipticCurveGeom x.1
  refine ⟨W, hW, Quotient.sound ⟨Ch8Counterexample.isoHom (𝟙 _) e he h0, rfl, rfl⟩⟩

/-- Weierstrass curves with the same $j$-invariant have the same class. -/
theorem weierstrassClass_eq_of_j_eq [IsAlgClosed k] {W W' : WeierstrassCurve k} [W.IsElliptic] [W'.IsElliptic]
    (h : W.j = W'.j) : weierstrassClass W = weierstrassClass W' := by
  obtain ⟨C, rfl⟩ := WeierstrassCurve.exists_variableChange_of_j_eq W W' h
  refine (?_ : weierstrassClass (C • W) = weierstrassClass W).symm
  exact Quotient.sound ⟨Ch8Counterexample.vcHom (𝟙 _) W C, rfl, rfl⟩

theorem jPoint_injective [IsAlgClosed k] : Function.Injective (jPoint (k := k)) := by
  intro x y hxy
  obtain ⟨W, hW, rfl⟩ := exists_weierstrassClass x
  obtain ⟨W', hW', rfl⟩ := exists_weierstrassClass y
  apply weierstrassClass_eq_of_j_eq
  have := congrArg (fun v : Variety.point k ⟶ affineLine k ↦ v.hom.left.appTop (affineLineCoordinate k)) hxy
  simp only [appTop_jPoint, jClass_weierstrassClass] at this
  exact (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.injective this

theorem jPoint_weierstrassClass (W : WeierstrassCurve k) [W.IsElliptic] :
    jPoint (weierstrassClass W) = linePoint W.j := by
  apply point_ext
  rw [appTop_jPoint, appTop_linePoint, jClass_weierstrassClass]

theorem jPoint_surjective : Function.Surjective (jPoint (k := k)) := by
  classical
  intro v
  refine ⟨weierstrassClass (WeierstrassCurve.ofJ (pointCoord v)), ?_⟩
  rw [jPoint_weierstrassClass, WeierstrassCurve.ofJ_j]
  exact point_ext_coord (pointCoord_linePoint _)

/-- **The bijection $\alpha : \mathcal E(k) \to \mathbb A^1(k)$ of Theorem 8.4**, $E \mapsto j(E)$. -/
def jEquiv [IsAlgClosed k] : (ellipticFunctor k).obj (op (Variety.point k)) ≃ (Variety.point k ⟶ affineLine k) :=
  Equiv.ofBijective jPoint ⟨jPoint_injective, jPoint_surjective⟩

theorem jEquiv_apply [IsAlgClosed k] (x : (ellipticFunctor k).obj (op (Variety.point k))) :
    jEquiv x = jPoint x := rfl

theorem jEquiv_coordinate [IsAlgClosed k] (x : (ellipticFunctor k).obj (op (Variety.point k))) :
    (jEquiv x).hom.left.appTop (affineLineCoordinate k) = jClass x :=
  appTop_jPoint x

/-- For a family $f$ over $T$ and a point $t \in T(k)$, $\alpha(f_t)$ is $t$ followed by the $j$-map of $f$. -/
theorem jEquiv_map [IsAlgClosed k] (T : Variety k) (f : (ellipticFunctor k).obj (op T))
    (t : Variety.point k ⟶ T) :
    jEquiv ((ellipticFunctor k).map t.op f) = t ≫ mapToAffineLine T (jClass f) := by
  apply point_ext
  rw [jEquiv_coordinate]
  induction f using Quotient.inductionOn with
  | h x =>
  change (x.1.baseChange t.hom.left).j = t.hom.left.appTop ((mapToAffineLine T x.1.j).hom.left.appTop _)
  rw [mapToAffineLine_coordinate, EllipticCurveGeom.j_baseChange]

/-- **Theorem 8.4, condition (a)** for $(\mathbb A^1, \alpha)$. -/
theorem jEquiv_regular [IsAlgClosed k] (T : Variety k) (f : (ellipticFunctor k).obj (op T)) :
    ∃ φ : T ⟶ affineLine k, ∀ t : Variety.point k ⟶ T, t ≫ φ = jEquiv ((ellipticFunctor k).map t.op f) :=
  ⟨mapToAffineLine T (jClass f), fun t ↦ (jEquiv_map T f t).symm⟩

end ModularFormsKB.Milne
