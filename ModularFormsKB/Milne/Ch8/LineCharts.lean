import ModularFormsKB.Milne.Ch8.JLineBijection
import ModularFormsKB.Milne.Ch8.LineDescentAlgebra
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import TauCeti.AlgebraicGeometry.Birational.RationalMap

/-!
# Milne, Chapter 8: regular maps on the affine line from charts (for Theorem 8.4)

Used in the proof of the universal property in Milne's Theorem 8.4 (`milne2017mf`, Section 8, pdf p. 98). Let $Z$ be
a variety over an algebraically closed field $k$ and $b : k \to Z(k)$ a map. A *chart* for $b$ is a basic open
$D(s) = \operatorname{Spec} k[X]_s$ of $\mathbb A^1$ ($s \ne 0$) with a regular map $D(s) \to Z$ whose value at every
$w \in D(s)(k)$ is $b(w)$ (`LineChart`). If every point lies in a chart, $b$ is regular
(`exists_hom_of_charts`): two charts agree on $D(s s')$ (they agree on $k$-points, and morphisms of varieties are
determined by their values on $k$-points), so they define one rational map $\mathbb A^1 \dashrightarrow Z$, defined at
every point; its representative is a regular map with values $b$.

## Items

- `domVariety`, `algPoint`, `lineVariety`, `linePt`: affine varieties of finitely generated domains, their $k$-points,
  and the basic opens of $\mathbb A^1$.
- `algPoint_eq`: $k$-points of $\operatorname{Spec} R$ are $k$-algebra maps $R \to k$.
- `LineChart`, `exists_hom_of_charts`.
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite Polynomial

noncomputable section

namespace ModularFormsKB.Milne

variable {k : Type u} [Field k] [IsAlgClosed k]

/-! ### Affine varieties of finitely generated domains -/

/-- $\operatorname{Spec} R$ as a variety, for a finitely generated $k$-domain $R$. -/
abbrev domVariety (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R] : Variety k :=
  Ch8Counterexample.specVariety R (isAffineAlgebra_of_isDomain R)

theorem specMap_comp_specStructure {R : Type u} [CommRing R] [Algebra k R] (φ : R →ₐ[k] k) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ specStructure k R = 𝟙 _ := by
  rw [specStructure, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext c
  exact φ.commutes c

/-- The $k$-point of $\operatorname{Spec} R$ of a $k$-algebra map $R \to k$. -/
def algPoint {R : Type u} [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R] (φ : R →ₐ[k] k) :
    Variety.point k ⟶ domVariety (k := k) R :=
  ⟨Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (specMap_comp_specStructure φ)⟩

theorem algPoint_left {R : Type u} [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (φ : R →ₐ[k] k) : (algPoint φ).hom.left = Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl

/-- Every $k$-point of $\operatorname{Spec} R$ is `algPoint φ`. -/
theorem algPoint_surjective {R : Type u} [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (t : Variety.point k ⟶ domVariety (k := k) R) : ∃ φ : R →ₐ[k] k, t = algPoint φ := by
  obtain ⟨φ, hφ⟩ := Ch8Counterexample.exists_algHom_of_point _ t
  exact ⟨φ, InducedCategory.hom_ext (Over.OverMorphism.ext hφ)⟩

/-- The regular map $\operatorname{Spec} R' \to \operatorname{Spec} R$ of a $k$-algebra map $R \to R'$. -/
abbrev domHom {R R' : Type u} [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    [CommRing R'] [IsDomain R'] [Algebra k R'] [Algebra.FiniteType k R'] (φ : R →ₐ[k] R') :
    domVariety (k := k) R' ⟶ domVariety R :=
  Ch8Counterexample.specHom _ _ φ

theorem algPoint_domHom {R R' : Type u} [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    [CommRing R'] [IsDomain R'] [Algebra k R'] [Algebra.FiniteType k R'] (φ : R →ₐ[k] R') (ψ : R' →ₐ[k] k) :
    algPoint ψ ≫ domHom φ = algPoint (ψ.comp φ) := by
  refine InducedCategory.hom_ext (Over.OverMorphism.ext ?_)
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-! ### Basic opens of the affine line -/

variable (k) in
/-- The localization $k[X]_s$ is a finitely generated domain for $s \ne 0$. -/
theorem isDomain_away {s : k[X]} (hs : s ≠ 0) : IsDomain (Localization.Away s) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hs)

instance finiteType_away (s : k[X]) : Algebra.FiniteType k (Localization.Away s) :=
  Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance

/-- The basic open $D(s) = \operatorname{Spec} k[X]_s$ of $\mathbb A^1$, as a variety. -/
abbrev lineVariety (s : k[X]) (hs : s ≠ 0) : Variety k :=
  have := isDomain_away k hs
  domVariety (Localization.Away s)

/-- Evaluation $k[X]_s \to k$ at $w$ with $s(w) \ne 0$, as a $k$-algebra map. -/
def evalAwayAlg (s : k[X]) (w : k) (hw : s.eval w ≠ 0) : Localization.Away s →ₐ[k] k where
  __ := LineDescent.evalAway s w hw
  commutes' c := by
    change LineDescent.evalAway s w hw (algebraMap k[X] (Localization.Away s) (Polynomial.C c)) = c
    rw [LineDescent.evalAway, IsLocalization.Away.lift_eq]
    simp

theorem evalAwayAlg_algebraMap (s : k[X]) (w : k) (hw : s.eval w ≠ 0) (p : k[X]) :
    evalAwayAlg s w hw (algebraMap k[X] _ p) = p.eval w := by
  change LineDescent.evalAway s w hw _ = _
  rw [LineDescent.evalAway, IsLocalization.Away.lift_eq]
  rfl

/-- $k$-algebra maps out of $k[X]_s$ are determined by the image of $X$. -/
theorem algHom_away_ext {s : k[X]} {A : Type*} [CommRing A] [Algebra k A] {φ ψ : Localization.Away s →ₐ[k] A}
    (h : φ (algebraMap k[X] _ X) = ψ (algebraMap k[X] _ X)) : φ = ψ := by
  have h2 : φ.comp (IsScalarTower.toAlgHom k k[X] (Localization.Away s)) =
      ψ.comp (IsScalarTower.toAlgHom k k[X] (Localization.Away s)) := Polynomial.algHom_ext h
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers s)
  ext p
  · exact congrArg (fun f : k[X] →ₐ[k] A ↦ f (Polynomial.C p)) h2
  · exact h

theorem evalAwayAlg_unique {s : k[X]} (φ : Localization.Away s →ₐ[k] k) :
    ∃ hw : s.eval (φ (algebraMap k[X] _ X)) ≠ 0, φ = evalAwayAlg s _ hw := by
  have key : ∀ p : k[X], φ (algebraMap k[X] _ p) = p.eval (φ (algebraMap k[X] _ X)) := by
    intro p
    have : φ.comp (IsScalarTower.toAlgHom k k[X] (Localization.Away s)) = Polynomial.aeval (φ (algebraMap k[X] _ X)) :=
      Polynomial.algHom_ext (by simp)
    have := congrArg (fun f : k[X] →ₐ[k] k ↦ f p) this
    simpa using this
  have hw : s.eval (φ (algebraMap k[X] _ X)) ≠ 0 := by
    rw [← key]
    exact ((IsLocalization.Away.algebraMap_isUnit s).map φ).ne_zero
  exact ⟨hw, algHom_away_ext (by rw [evalAwayAlg_algebraMap, eval_X])⟩

/-- The $k$-point $w$ of $D(s)$, for $s(w) \ne 0$. -/
abbrev linePt (s : k[X]) (hs : s ≠ 0) (w : k) (hw : s.eval w ≠ 0) : Variety.point k ⟶ lineVariety s hs :=
  have := isDomain_away k hs
  algPoint (evalAwayAlg s w hw)

/-! ### Charts -/

/-- **A chart** for a map $b : k \to Z(k)$: a basic open $D(s)$ of $\mathbb A^1$ with a regular map $D(s) \to Z$ whose
value at every $w$ with $s(w) \ne 0$ is $b(w)$. -/
structure LineChart (Z : Variety k) (b : k → (Variety.point k ⟶ Z)) where
  s : k[X]
  hs : s ≠ 0
  m : lineVariety s hs ⟶ Z
  val : ∀ (w : k) (hw : s.eval w ≠ 0), linePt s hs w hw ≫ m = b w

/-! ### Gluing charts -/

section Glue

variable {Z : Variety k} {b : k → (Variety.point k ⟶ Z)}

/-- The open immersion $D(s) \to \mathbb A^1$ of schemes. -/
abbrev lineι (s : k[X]) : Spec (CommRingCat.of (Localization.Away s)) ⟶ Spec (CommRingCat.of k[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap k[X] (Localization.Away s)))

theorem nonempty_spec_away {s : k[X]} (hs : s ≠ 0) : Nonempty (Spec (CommRingCat.of (Localization.Away s))) := by
  have := isDomain_away k hs
  infer_instance

theorem dense_range_lineι {s : k[X]} (hs : s ≠ 0) : Dense (Set.range (lineι (k := k) s)) := by
  obtain ⟨x⟩ := nonempty_spec_away (k := k) hs
  exact (lineι s).isOpenEmbedding.isOpen_range.dense ⟨_, x, rfl⟩

/-- The morphism of schemes of a chart. -/
def LineChart.mor (c : LineChart Z b) : Spec (CommRingCat.of (Localization.Away c.s)) ⟶ Z.obj.left :=
  c.m.hom.left

/-- The partial map $\mathbb A^1 \dashrightarrow Z$ of a chart. -/
def LineChart.pm (c : LineChart Z b) : (Spec (CommRingCat.of k[X])).PartialMap Z.obj.left where
  domain := (lineι c.s).opensRange
  dense_domain := dense_range_lineι c.hs
  hom := (lineι c.s).isoOpensRange.inv ≫ c.mor

theorem isUnit_algebraMap_of_dvd {s s' : k[X]} (h : s ∣ s') (n : ℕ) :
    IsUnit (algebraMap k[X] (Localization.Away s') (s ^ n)) := by
  rw [map_pow]
  exact (isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit s')).pow n

/-- The $k$-algebra map $k[X]_s \to k[X]_{s s'}$. -/
def awayLeft (s s' : k[X]) : Localization.Away s →ₐ[k] Localization.Away (s * s') :=
  IsLocalization.liftAlgHom (M := Submonoid.powers s) (f := IsScalarTower.toAlgHom k k[X] _) (by
    rintro ⟨_, n, rfl⟩
    exact isUnit_algebraMap_of_dvd (dvd_mul_right s s') n)

/-- The $k$-algebra map $k[X]_{s'} \to k[X]_{s s'}$. -/
def awayRight (s s' : k[X]) : Localization.Away s' →ₐ[k] Localization.Away (s * s') :=
  IsLocalization.liftAlgHom (M := Submonoid.powers s') (f := IsScalarTower.toAlgHom k k[X] _) (by
    rintro ⟨_, n, rfl⟩
    exact isUnit_algebraMap_of_dvd (dvd_mul_left s' s) n)

theorem awayLeft_algebraMap (s s' : k[X]) (p : k[X]) :
    awayLeft s s' (algebraMap k[X] _ p) = algebraMap k[X] _ p :=
  IsLocalization.lift_eq _ _

theorem awayRight_algebraMap (s s' : k[X]) (p : k[X]) :
    awayRight s s' (algebraMap k[X] _ p) = algebraMap k[X] _ p :=
  IsLocalization.lift_eq _ _

theorem lineι_mul_left (s s' : k[X]) :
    lineι (k := k) (s * s') = Spec.map (CommRingCat.ofHom (awayLeft s s').toRingHom) ≫ lineι s := by
  rw [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun p ↦ (awayLeft_algebraMap s s' p).symm))

theorem lineι_mul_right (s s' : k[X]) :
    lineι (k := k) (s * s') = Spec.map (CommRingCat.ofHom (awayRight s s').toRingHom) ≫ lineι s' := by
  rw [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun p ↦ (awayRight_algebraMap s s' p).symm))

/-- Every $k$-point of $D(s)$ is `linePt s w`. -/
theorem exists_linePt {s : k[X]} (hs : s ≠ 0) (t : Variety.point k ⟶ lineVariety s hs) :
    ∃ (w : k) (hw : s.eval w ≠ 0), t = linePt s hs w hw := by
  have := isDomain_away k hs
  obtain ⟨φ, rfl⟩ := algPoint_surjective t
  obtain ⟨hw, h⟩ := evalAwayAlg_unique φ
  exact ⟨_, hw, congrArg algPoint h⟩

theorem linePt_awayLeft {s s' : k[X]} (hs : s ≠ 0) (hs' : s' ≠ 0) (w : k) (hw : (s * s').eval w ≠ 0) :
    haveI := isDomain_away k hs; haveI := isDomain_away k (mul_ne_zero hs hs')
    linePt (s * s') (mul_ne_zero hs hs') w hw ≫ domHom (awayLeft s s') =
      linePt s hs w (left_ne_zero_of_mul (by simpa using hw)) := by
  haveI := isDomain_away k hs; haveI := isDomain_away k (mul_ne_zero hs hs')
  rw [algPoint_domHom]
  congr 1
  apply algHom_away_ext
  simp [awayLeft_algebraMap, evalAwayAlg_algebraMap]

theorem linePt_awayRight {s s' : k[X]} (hs : s ≠ 0) (hs' : s' ≠ 0) (w : k) (hw : (s * s').eval w ≠ 0) :
    haveI := isDomain_away k hs'; haveI := isDomain_away k (mul_ne_zero hs hs')
    linePt (s * s') (mul_ne_zero hs hs') w hw ≫ domHom (awayRight s s') =
      linePt s' hs' w (right_ne_zero_of_mul (by simpa using hw)) := by
  haveI := isDomain_away k hs'; haveI := isDomain_away k (mul_ne_zero hs hs')
  rw [algPoint_domHom]
  congr 1
  apply algHom_away_ext
  simp [awayRight_algebraMap, evalAwayAlg_algebraMap]

/-- Two charts agree on $D(s s')$. -/
theorem LineChart.agree (c c' : LineChart Z b) :
    Spec.map (CommRingCat.ofHom (awayLeft c.s c'.s).toRingHom) ≫ c.mor =
      Spec.map (CommRingCat.ofHom (awayRight c.s c'.s).toRingHom) ≫ c'.mor := by
  haveI := isDomain_away k c.hs; haveI := isDomain_away k c'.hs
  haveI := isDomain_away k (mul_ne_zero c.hs c'.hs)
  have : (domHom (awayLeft c.s c'.s) ≫ c.m : lineVariety (c.s * c'.s) (mul_ne_zero c.hs c'.hs) ⟶ Z) =
      domHom (awayRight c.s c'.s) ≫ c'.m := by
    apply Variety.hom_ext_of_points
    intro t
    obtain ⟨w, hw, rfl⟩ := exists_linePt _ t
    rw [← Category.assoc, ← Category.assoc, linePt_awayLeft c.hs c'.hs, linePt_awayRight c.hs c'.hs, c.val,
      c'.val]
  exact congrArg (fun φ ↦ φ.hom.left) this

theorem isoOpensRange_hom_homOfLE {u t : k[X]} (h : (lineι (k := k) u).opensRange ≤ (lineι t).opensRange)
    (r : Spec (CommRingCat.of (Localization.Away u)) ⟶ Spec (CommRingCat.of (Localization.Away t)))
    (hr : lineι (k := k) u = r ≫ lineι t) :
    (lineι u).isoOpensRange.hom ≫ (Spec (CommRingCat.of k[X])).homOfLE h ≫
      (lineι t).isoOpensRange.inv = r := by
  rw [← cancel_mono (lineι (k := k) t)]
  have e : (lineι (k := k) t).isoOpensRange.inv ≫ lineι t = (lineι t).opensRange.ι := by
    rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
  rw [Category.assoc, Category.assoc, e, Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι, hr]

theorem opensRange_le_of_eq {X Y W : Scheme.{u}} {f : X ⟶ W} {g : Y ⟶ W} [IsOpenImmersion f] [IsOpenImmersion g]
    (r : X ⟶ Y) (h : f = r ≫ g) : f.opensRange ≤ g.opensRange := by
  rintro _ ⟨x, rfl⟩
  exact ⟨r x, by rw [h]; rfl⟩

/-- Two charts give equivalent partial maps. -/
theorem LineChart.pm_equiv (c c' : LineChart Z b) : c.pm.equiv c'.pm := by
  have hl := opensRange_le_of_eq _ (lineι_mul_left (k := k) c.s c'.s)
  have hr := opensRange_le_of_eq _ (lineι_mul_right (k := k) c.s c'.s)
  refine ⟨(lineι (c.s * c'.s)).opensRange, dense_range_lineι (mul_ne_zero c.hs c'.hs), hl, hr, ?_⟩
  change (Spec (CommRingCat.of k[X])).homOfLE hl ≫ (lineι c.s).isoOpensRange.inv ≫ c.mor =
    (Spec (CommRingCat.of k[X])).homOfLE hr ≫ (lineι c'.s).isoOpensRange.inv ≫ c'.mor
  rw [← cancel_epi (lineι (c.s * c'.s)).isoOpensRange.hom,
    reassoc_of% (isoOpensRange_hom_homOfLE hl _ (lineι_mul_left c.s c'.s)),
    reassoc_of% (isoOpensRange_hom_homOfLE hr _ (lineι_mul_right c.s c'.s))]
  exact c.agree c'

theorem appTop_specMap_inv {R S : CommRingCat.{u}} (f : R ⟶ S) (x : R) :
    (Spec.map f).appTop ((Scheme.ΓSpecIso R).inv x) = (Scheme.ΓSpecIso S).inv (f x) :=
  (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality f) x).symm

theorem lineι_specStructure (s : k[X]) :
    lineι (k := k) s ≫ specStructure k k[X] = specStructure k (Localization.Away s) := by
  rw [specStructure, specStructure, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x ↦
    (IsScalarTower.algebraMap_apply k k[X] (Localization.Away s) x).symm))

variable (k) in
/-- The closed point of $\operatorname{Spec} k$. -/
def pt0 : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k

/-- The point $w$ of $D(s)$ as a morphism of schemes. -/
def linePtMor (s : k[X]) (w : k) (hw : s.eval w ≠ 0) :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away s)) :=
  Spec.map (CommRingCat.ofHom (evalAwayAlg s w hw).toRingHom)

theorem linePt_left {s : k[X]} (hs : s ≠ 0) (w : k) (hw : s.eval w ≠ 0) :
    (linePt s hs w hw).hom.left = linePtMor s w hw := rfl

/-- The point $w$ of $\mathbb A^1$ as a morphism of schemes. -/
def linePointMor (w : k) : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k[X]) := (linePoint w).hom.left

/-- The point $w$ of $D(s)$ maps to the point $w$ of $\mathbb A^1$. -/
theorem linePt_lineι (s : k[X]) (w : k) (hw : s.eval w ≠ 0) :
    linePtMor s w hw ≫ lineι s = linePointMor w := by
  refine spec_line_ext (s := 𝟙 _) ?_ (Over.w (linePoint w).hom) ?_
  · rw [Category.assoc, lineι_specStructure, linePtMor]
    exact specMap_comp_specStructure _
  · refine (?_ : _ = (Scheme.ΓSpecIso (CommRingCat.of k)).inv w).trans (appTop_linePoint w).symm
    change (linePtMor s w hw ≫ lineι s).appTop ((Scheme.ΓSpecIso (CommRingCat.of k[X])).inv X) = _
    rw [Scheme.Hom.comp_appTop, linePtMor, CommRingCat.comp_apply, appTop_specMap_inv, appTop_specMap_inv]
    congr 1
    change evalAwayAlg s w hw (algebraMap k[X] _ X) = w
    rw [evalAwayAlg_algebraMap, eval_X]

theorem LineChart.mem_domain (c : LineChart Z b) (w : k) (hw : c.s.eval w ≠ 0) :
    linePointMor w (pt0 k) ∈ c.pm.domain :=
  ⟨linePtMor c.s w hw (pt0 k), by
    rw [← Scheme.Hom.comp_apply, linePt_lineι]⟩

/-- Every closed point of $\mathbb A^1$ is the point of some $w \in k$. -/
theorem exists_eq_linePoint (x : Spec (CommRingCat.of k[X])) (hx : IsClosed {x}) :
    ∃ w : k, linePointMor w (pt0 k) = x := by
  have hV : IsVariety k (affineLine k).obj.hom := (affineLine k).property
  haveI : LocallyOfFiniteType (affineLine k).obj.hom := hV.locallyOfFiniteType
  let p : Variety.point k ⟶ affineLine k := ⟨Over.homMk (pointOfClosedPoint (affineLine k).obj.hom x hx)
    (pointOfClosedPoint_comp (affineLine k).obj.hom x hx)⟩
  refine ⟨pointCoord p, ?_⟩
  rw [linePointMor, show linePoint (pointCoord p) = p from point_ext_coord (pointCoord_linePoint _)]
  exact pointOfClosedPoint_apply (affineLine k).obj.hom x hx _

/-- **Gluing charts.** If every point of $\mathbb A^1$ lies in a chart for $b$, then $b$ is the map on $k$-points of a
regular map $\mathbb A^1 \to Z$. -/
theorem exists_hom_of_charts (hcov : ∀ w : k, ∃ c : LineChart Z b, c.s.eval w ≠ 0) :
    ∃ ψ : affineLine k ⟶ Z, ∀ w : k, linePoint w ≫ ψ = b w := by
  have hZ : IsVariety k Z.obj.hom := Z.property
  haveI : IsSeparated Z.obj.hom := hZ.2
  haveI : Z.obj.left.IsSeparated := Scheme.IsSeparated.of_isSeparated Z.obj.hom
  obtain ⟨c₀, -⟩ := hcov 0
  let f := c₀.pm.toRationalMap
  have hmem : ∀ (c : LineChart Z b) (w : k), c.s.eval w ≠ 0 →
      linePointMor w (pt0 k) ∈ f.domain := by
    intro c w hw
    have hc : c.pm.toRationalMap = f := Scheme.PartialMap.toRationalMap_eq_iff.mpr (c.pm_equiv c₀)
    rw [← hc]
    exact c.pm.le_domain_toRationalMap (c.mem_domain w hw)
  have hf : f.domain = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    by_contra hx
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Z := (f.domain : Set (Spec (CommRingCat.of k[X])))ᶜ)
      ⟨x, hx⟩ f.domain.2.isClosed_compl.isLocallyClosed
    obtain ⟨w, rfl⟩ := exists_eq_linePoint y (mem_closedPoints_iff.mp hyc)
    obtain ⟨c, hc⟩ := hcov w
    exact hy (hmem c w hc)
  let ψ₀ := Scheme.RationalMap.toHom f hf
  have hmor : ∀ c : LineChart Z b, c.mor = lineι c.s ≫ ψ₀ := by
    intro c
    have hc : c.pm.toRationalMap = f := Scheme.PartialMap.toRationalMap_eq_iff.mpr (c.pm_equiv c₀)
    have hψ : ψ₀.toRationalMap = f := Scheme.RationalMap.toRationalMap_toHom f hf
    have heq : c.pm.equiv ψ₀.toPartialMap := Scheme.PartialMap.toRationalMap_eq_iff.mp (hc.trans hψ.symm)
    have h := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp heq
    have h2 := congrArg ((lineι c.s).isoOpensRange.hom ≫ ·) h
    simp only [LineChart.pm, Iso.hom_inv_id_assoc] at h2
    rw [h2, ← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  have hover : ψ₀ ≫ Z.obj.hom = specStructure k k[X] := by
    haveI : IsDominant (lineι (k := k) c₀.s) := ⟨dense_range_lineι c₀.hs⟩
    refine ext_of_isDominant_of_isSeparated (Limits.terminal.from _) (Limits.terminal.hom_ext _ _)
      (lineι c₀.s) ?_
    rw [← Category.assoc, ← hmor, lineι_specStructure]
    exact Over.w c₀.m.hom
  refine ⟨⟨Over.homMk ψ₀ hover⟩, fun w ↦ ?_⟩
  obtain ⟨c, hc⟩ := hcov w
  refine InducedCategory.hom_ext (Over.OverMorphism.ext ?_)
  change linePointMor w ≫ ψ₀ = (b w).hom.left
  rw [← linePt_lineι c.s w hc, Category.assoc, ← hmor, ← c.val w hc]
  rfl

end Glue

end ModularFormsKB.Milne
