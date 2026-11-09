import ModularFormsKB.Milne.Ch8.CyclicThreeDescent
import ModularFormsKB.Milne.Ch8.CyclicTwoModuli

/-!
# Milne, Theorem 8.6 for $N = 3$: the line $\mathbb A^1 \smallsetminus \{27\}$ solves $\mathcal E_{0,3}$

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 8, Theorem 8.6 (pdf p. 100).

Over an algebraically closed field $k$ with $3 \ne 0$, the moduli problem $\mathcal E_{0,3}$ of elliptic curves with a
cyclic subgroup of order three is solved by $M = \mathbb A^1 \smallsetminus \{27\} =
\operatorname{Spec} k[t, (t-27)^{-1}]$, with $\alpha(E, I)$ the invariant $t = a_1^3/a_3$ of the normal form
$y^2 + a_1xy + a_3y = x^3$ in which a generator of $I$ is $(0, 0)$ (`cyclicModuliSolution_three`). The proof follows
the case $N = 2$ (`CyclicTwoModuli`):

- (a) For a pair $(E, I)$ over a variety $V$ the invariant morphism `cycMor` is the descended map
  `CyclicThree.cycMap` of `CyclicThreeDescent`; it is invariant under isomorphism and natural (`cycMor_rel`,
  `cycMor_pull`).
- $\alpha$ is bijective (`alpha_bijective`): every pair over $k$ is isomorphic to the pair of $(0, 0)$ on
  $y^2 + sxy + y = x^3$, $s^3 = t$ (`exists_rel_normal`: move the generator to $(0, 0)$, its tangent to $y = 0$; then
  $\Psi_3(0) = a_2a_3^2$ forces $a_2 = 0$; scale $a_3$ to $1$), and $s$ and $\zeta s$, $\zeta^3 = 1$, give isomorphic
  pairs (`rel_normal_mul`).
- (b) Universality: the family $y^2 + txy + t^2y = x^3$ over $D(t(t - 27))$ gives a chart of $\beta \circ \alpha^{-1}$
  away from $t = 0$; the family $y^2 + sxy + y = x^3$ over $D(s^3 - 27)$, with invariant $s^3$, gives charts around
  every point by the descent lemma `exists_chart_at` of Theorem 8.4; the charts glue (`exists_hom_of_charts_away`).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite WeierstrassCurve TauCeti.AlgebraicGeometry MonoidalCategory
  ModularFormsKB.Milne.LevelTwoChart ModularFormsKB.Milne.CyclicThree MonObj TauCeti Polynomial

noncomputable section

namespace ModularFormsKB.Milne.CyclicThreeModuli

open Ch8Counterexample LevelTwoModuli CyclicTwoModuli

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The polynomial $t - 27$. -/
abbrev tPoly : k[X] := X - C 27

theorem tPoly_ne_zero : (tPoly : k[X]) ≠ 0 := X_sub_C_ne_zero 27

variable (k) in
/-- **The moduli variety** $M = \mathbb A^1 \smallsetminus \{27\} = D(t - 27)$. -/
abbrev tLine : Variety k := lineVariety (tPoly (k := k)) tPoly_ne_zero

/-- Pairs $(E, I)$, $I$ a cyclic subgroup of order three. -/
abbrev Pair (V : Variety k) := LevelPair (ModuliProblem.gammaZero (Spec (CommRingCat.of k)) 3) V

/-- The cyclic subgroup of a pair. -/
abbrev sub {V : Variety k} (x : Pair V) := ModuliProblem.gammaZeroEquiv _ x.2

/-- **The pair of a point of exact order three.** -/
def pairOf (V : Variety k) (E : EllipticCurveGeom V.obj.left) (P : 𝟙_ (Over V.obj.left) ⟶ Over.mk E.structureMap)
    (hP : E.IsOfExactOrder P 3) : Pair V :=
  ⟨E, (ModuliProblem.gammaZeroEquiv _).symm ⟨E.multiplesDivisor P 3, hP.isCyclicSubgroup_multiplesDivisor⟩⟩

theorem pairOf_congr (V : Variety k) (E : EllipticCurveGeom V.obj.left)
    {P P' : 𝟙_ (Over V.obj.left) ⟶ Over.mk E.structureMap} (hP : E.IsOfExactOrder P 3)
    (hP' : E.IsOfExactOrder P' 3) (h : P = P') : pairOf V E P hP = pairOf V E P' hP' := by
  subst h; rfl

theorem map_pairOf {V V' : Variety k} {E : EllipticCurveGeom V.obj.left} {E' : EllipticCurveGeom V'.obj.left}
    (f : V'.ellObj E' ⟶ V.ellObj E) (P : 𝟙_ (Over V.obj.left) ⟶ Over.mk E.structureMap)
    (hP : E.IsOfExactOrder P 3) :
    (ModuliProblem.gammaZero _ 3).map f.op (pairOf V E P hP).2 =
      (pairOf V' E' (EllipticCurveGeom.pointsPullback f.isPullback f.zero_total P)
        (hP.pointsPullback _ _)).2 := by
  apply (ModuliProblem.gammaZeroEquiv _).injective
  apply Subtype.ext
  exact (EllipticCurveGeom.multiplesDivisor_pointsPullback f.isPullback f.zero_total P 3).symm

theorem rel_pairOf_hom {V : Variety k} {E E' : EllipticCurveGeom V.obj.left}
    (f : V.ellObj E' ⟶ V.ellObj E) (hf : f.base = 𝟙 _) (P : 𝟙_ (Over V.obj.left) ⟶ Over.mk E.structureMap)
    (hP : E.IsOfExactOrder P 3) :
    LevelPair.Rel (pairOf V E' (EllipticCurveGeom.pointsPullback f.isPullback f.zero_total P)
      (hP.pointsPullback _ _)) (pairOf V E P hP) :=
  ⟨f, hf, map_pairOf f P hP⟩

/-! ### The invariant morphism -/

variable (h3 : ((3 : ℕ) : k) ≠ 0)
include h3

/-- **The invariant morphism** $V \to M$ of a pair. -/
def cycMor {V : Variety k} (x : Pair V) : V ⟶ tLine k :=
  ⟨Over.homMk (cycMap h3 V.obj.hom (sub x).2) (cycMap_specStructure h3 V.obj.hom (sub x).2)⟩

theorem cycMor_left {V : Variety k} (x : Pair V) :
    (cycMor h3 x).hom.left = cycMap h3 V.obj.hom (sub x).2 := rfl

theorem cycMap_hom {V V' : Variety k} (x : Pair V) (E' : EllipticCurveGeom V'.obj.left)
    (f : V'.ellObj E' ⟶ V.ellObj x.1) :
    cycMap h3 V'.obj.hom (sub (⟨E', (ModuliProblem.gammaZero _ 3).map f.op x.2⟩ : Pair V')).2 =
      f.base ≫ cycMap h3 V.obj.hom (sub x).2 :=
  cycMap_comp h3 V.obj.hom V'.obj.hom (I := (sub x).1) f.isPullback f.zero_total
    f.base_structureMap (sub x).2 _

theorem cycMor_rel {V : Variety k} {x y : Pair V} (h : LevelPair.Rel x y) : cycMor h3 x = cycMor h3 y := by
  obtain ⟨f, hf, hfy⟩ := h
  have hx : x = ⟨x.1, (ModuliProblem.gammaZero _ 3).map f.op y.2⟩ := Sigma.ext rfl (heq_of_eq hfy.symm)
  rw [hx]
  apply InducedCategory.hom_ext
  apply Over.OverMorphism.ext
  rw [cycMor_left, cycMor_left]
  have := cycMap_hom h3 y x.1 f
  rw [hf, Category.id_comp] at this
  exact this

theorem cycMor_pull {V W : Variety k} (φ : W ⟶ V) (x : Pair V) :
    cycMor h3 (LevelPair.pull φ x) = φ ≫ cycMor h3 x := by
  apply InducedCategory.hom_ext
  apply Over.OverMorphism.ext
  rw [cycMor_left]
  exact cycMap_hom h3 x _ (LevelPair.pullHom φ x.1)

omit h3 in
theorem ne_zero_of_order_three {S : Scheme.{u}} (q : S ⟶ Spec (CommRingCat.of k)) (h3 : ((3 : ℕ) : k) ≠ 0)
    {E : EllipticCurveGeom S} {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} (hP : E.IsOfExactOrder P 3) (s : S) :
    P.left s ≠ E.zero s :=
  ne_zero_one (natCast_ne_zero_residue h3 q) hP s

/-- The invariant morphism of `pairOf` is the invariant map `tMap` of the point. -/
theorem cycMor_pairOf_left {V : Variety k} (E : EllipticCurveGeom V.obj.left)
    (P : 𝟙_ (Over V.obj.left) ⟶ Over.mk E.structureMap) (hP : E.IsOfExactOrder P 3) :
    (cycMor h3 (pairOf V E P hP)).hom.left = tMap V.obj.hom hP.pow_eq_one
      (ne_zero_of_order_three V.obj.hom h3 hP) := by
  rw [cycMor_left]
  let G : Gen (sub (pairOf V E P hP)).1 (𝟙 V.obj.left) :=
    ⟨E, 𝟙 _, CyclicTwo.isPullback_id E, (Category.comp_id _).trans (Category.id_comp _).symm, P, hP,
      Scheme.IdealSheafData.comap_id _⟩
  have := cycMap_spec h3 V.obj.hom (sub (pairOf V E P hP)).2 (𝟙 _) G
  rw [Category.id_comp] at this
  rw [this]
  change tMap _ _ _ = tMap _ _ _
  congr 1

/-- $\alpha$: the invariant of a class of pairs over $k$. -/
def alpha : (cyclicFunctor k 3).obj (op (Variety.point k)) → (Variety.point k ⟶ tLine k) :=
  Quotient.lift (cycMor h3) fun _ _ h ↦ cycMor_rel h3 h

/-! ### Weierstrass pairs -/

omit [IsAlgClosed k] h3 in
/-- A point $(x, y)$ with $\Psi_3(x) = 0$ is killed by three. -/
theorem affinePointHom_pow_three {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] {x y : R}
    (h : W.toAffine.Equation x y) (h3x : psi3 W x = 0) : affinePointHom W h ^ 3 = 1 := by
  have hm : (toEllipticCurveGeomIso W).inv ≫ (W.toEllipticCurveGeom.mulBy 3).left =
      W.projModelMulBy 3 ≫ (toEllipticCurveGeomIso W).inv := by
    rw [projModelMulBy_eq]; simp
  have h3' := (projModelAffinePoint_projModelMulBy_three_eq_projModelZero_iff h).mpr (by rw [← psi3_eq]; exact h3x)
  have := (EllipticCurveGeom.zpow_eq_one_iff_left_comp_mulBy_left _ (affinePointHom W h) 3).mpr (by
    rw [affinePointHom_left, Category.assoc, hm, ← Category.assoc, h3', ← zero_toEllipticCurveGeomIso_hom,
      Category.assoc, Iso.hom_inv_id, Category.comp_id])
  exact_mod_cast this

omit [IsAlgClosed k] h3 in
theorem inv_left_ne_zero {S : Scheme.{u}} {E : EllipticCurveGeom S} {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
    (hP : ∀ s, P.left s ≠ E.zero s) (s : S) : P⁻¹.left s ≠ E.zero s := by
  intro hs
  apply hP s
  have := congrArg E.neg hs
  rw [EllipticCurveGeom.hom_inv_left, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Category.assoc,
    EllipticCurveGeom.neg_neg, EllipticCurveGeom.zero_neg] at this
  simpa using this

/-- **A point $(x, y)$ with $\Psi_3(x) = 0$ has exact order three.** -/
theorem isOfExactOrder_affine {R : Type u} [CommRing R] [Algebra k R] (W : WeierstrassCurve R) [W.IsElliptic]
    {x y : R} (h : W.toAffine.Equation x y) (h3x : psi3 W x = 0) :
    W.toEllipticCurveGeom.IsOfExactOrder (affinePointHom W h) 3 := by
  have hres := natCast_ne_zero_residue h3 (specStructure k R)
  have hcube := affinePointHom_pow_three W h h3x
  let φ := (zmodMonoidHomEquiv 3 _).symm ⟨affinePointHom W h, hcube⟩
  have hφ1 : φ (.ofAdd 1) = affinePointHom W h := zmodMonoidHomEquiv_symm_apply_ofAdd_one _
  have hφ : W.toEllipticCurveGeom.IsFiberwiseInjective φ := by
    refine EllipticCurveGeom.isFiberwiseInjective_zmod_iff.mpr fun j hj hj3 s ↦ ?_
    rw [hφ1]
    interval_cases j
    · rw [pow_one]
      exact affinePointHom_ne_zero h s
    · have hinv : affinePointHom W h ^ 2 = (affinePointHom W h)⁻¹ :=
        eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hcube])
      rw [hinv]
      exact inv_left_ne_zero (affinePointHom_ne_zero h) s
  have := EllipticCurveGeom.isFiberwiseInjective_iff_isOfNaiveExactOrder.mp hφ
  rw [hφ1] at this
  exact this.isOfExactOrder hres

/-- The pair of a Weierstrass family over a finitely generated domain with a point of order three. -/
abbrev wPair (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (W : WeierstrassCurve R) [W.IsElliptic] {x y : R} (h : W.toAffine.Equation x y) (h3x : psi3 W x = 0) :
    Pair (domVariety (k := k) R) :=
  pairOf (domVariety R) W.toEllipticCurveGeom (affinePointHom W h) (isOfExactOrder_affine h3 W h h3x)

/-- The pair of a Weierstrass curve over $k$ with a point of order three. -/
abbrev kPair (W : WeierstrassCurve k) [W.IsElliptic] {x y : k} (h : W.toAffine.Equation x y)
    (h3x : psi3 W x = 0) : Pair (Variety.point k) :=
  pairOf (Variety.point k) W.toEllipticCurveGeom (affinePointHom W h) (isOfExactOrder_affine h3 W h h3x)

omit h3 in
theorem eval_tPoly_ne_zero {l : k} (hl : IsUnit (l - 27)) : (tPoly (k := k)).eval l ≠ 0 := by
  simpa using hl.ne_zero

omit h3 in
theorem spec_tLift_eq (l : k) (hl : IsUnit (l - 27)) :
    Spec.map (CommRingCat.ofHom (tLift (algebraMap k k) l hl)) =
      (linePt (tPoly (k := k)) tPoly_ne_zero l (eval_tPoly_ne_zero hl)).hom.left := by
  change _ = Spec.map (CommRingCat.ofHom (evalAwayAlg _ l _).toRingHom)
  congr 2

/-- **The invariant of a Weierstrass family.** -/
theorem cycMor_wPair_left (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (W : WeierstrassCurve R) [W.IsElliptic] {x y : R} (h : W.toAffine.Equation x y) (h3x : psi3 W x = 0) :
    (cycMor h3 (wPair h3 R W h h3x)).hom.left = Spec.map (CommRingCat.ofHom
      (tLift (algebraMap k R) (inv3 W (isUnit_coeffC_of_psi3 h h3x)) (isUnit_inv_weierstrass_sub W h h3x))) :=
  (cycMor_pairOf_left h3 _ _ _).trans (tMap_weierstrass W h h3x _ _)

/-- **The invariant of a Weierstrass curve over $k$.** -/
theorem cycMor_kPair_left (W : WeierstrassCurve k) [W.IsElliptic] {x y : k} (h : W.toAffine.Equation x y)
    (h3x : psi3 W x = 0) :
    cycMor h3 (kPair h3 W h h3x) = linePt (tPoly (k := k)) tPoly_ne_zero
      (inv3 W (isUnit_coeffC_of_psi3 h h3x)) (eval_tPoly_ne_zero (isUnit_inv_weierstrass_sub W h h3x)) := by
  apply InducedCategory.hom_ext
  apply Over.OverMorphism.ext
  refine (cycMor_pairOf_left h3 _ _ _).trans ?_
  rw [← spec_tLift_eq _ (isUnit_inv_weierstrass_sub W h h3x)]
  have := tMap_weierstrass (k := k) W h h3x (isOfExactOrder_affine h3 W h h3x).pow_eq_one
    (ne_zero_of_order_three (specStructure k k) h3 (isOfExactOrder_affine h3 W h h3x))
  rw [← this]
  change tMap _ _ _ = tMap _ _ _
  congr 1
  exact specStructure_self.symm

/-- **The invariant at a $k$-point of a Weierstrass family.** -/
theorem cycMor_pull_wPair (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (W : WeierstrassCurve R) [W.IsElliptic] {x y : R} (h : W.toAffine.Equation x y) (h3x : psi3 W x = 0)
    (τ : R →ₐ[k] k) :
    cycMor h3 (LevelPair.pull (algPoint τ) (wPair h3 R W h h3x)) = linePt (tPoly (k := k)) tPoly_ne_zero
      (τ (inv3 W (isUnit_coeffC_of_psi3 h h3x)))
      (eval_tPoly_ne_zero (by
        have := (isUnit_inv_weierstrass_sub W h h3x).map τ
        rwa [map_sub, map_ofNat] at this)) := by
  have hl' : IsUnit (τ (inv3 W (isUnit_coeffC_of_psi3 h h3x)) - 27) := by
    have := (isUnit_inv_weierstrass_sub W h h3x).map τ
    rwa [map_sub, map_ofNat] at this
  rw [cycMor_pull]
  apply InducedCategory.hom_ext
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ (cycMor h3 (wPair h3 R W h h3x)).hom.left = _
  rw [cycMor_wPair_left, ← spec_tLift_eq _ hl']
  refine (Spec.map_comp _ _).symm.trans ?_
  rw [← CommRingCat.ofHom_comp]
  congr 2
  apply tLift_ext
  · intro a
    have e1 := RingHom.congr_fun (tLift_algebraMap_k (algebraMap k R) _ (isUnit_inv_weierstrass_sub W h h3x)) a
    have e2 := RingHom.congr_fun (tLift_algebraMap_k (algebraMap k k) _ hl') a
    simp only [RingHom.comp_apply] at e1 e2 ⊢
    rw [e1, e2]
    exact τ.commutes a
  · rw [RingHom.comp_apply, tLift_algebraMap, Polynomial.eval₂_X, tLift_algebraMap, Polynomial.eval₂_X]
    rfl

end ModularFormsKB.Milne.CyclicThreeModuli
