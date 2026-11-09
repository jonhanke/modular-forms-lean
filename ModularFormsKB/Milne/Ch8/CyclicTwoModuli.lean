import ModularFormsKB.Milne.Ch8.CyclicTwoDescent
import ModularFormsKB.Milne.Ch8.LineChartsAway
import ModularFormsKB.Milne.Ch8.LevelTwoModuli

/-!
# Milne, Theorem 8.6 for $N = 2$: the line $\mathbb A^1 \smallsetminus \{4\}$ solves $\mathcal E_{0,2}$

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 8, Theorem 8.6 (pdf p. 100).

Over an algebraically closed field $k$ with $2 \ne 0$, the moduli problem $\mathcal E_{0,2}$ of elliptic curves with a
cyclic subgroup of order two is solved by $M = \mathbb A^1 \smallsetminus \{4\} = \operatorname{Spec} k[t, (t-4)^{-1}]$,
with $\alpha(E, I)$ the invariant $t = a^2/b$ of the normal form $y^2 = x(x^2 + ax + b)$ in which the generator of $I$ is
$(0, 0)$ (`cyclicModuliSolution_two`).

- (a) For a pair $(E, I)$ over a variety $V$ the invariant map `cycMor` is the glued map `CyclicTwo.cycMap` of
  `CyclicTwoDescent` (fppf descent of the invariants of local generators); it is invariant under isomorphism and
  natural under base change (`cycMor_rel`, `cycMor_pull`).
- $\alpha$ is bijective (`alpha_bijective`): over $k$ every cyclic subgroup of order two has a generator
  (`CyclicTwo.nonempty_gen_spec`), every pair is isomorphic to the pair of $(0, 0)$ on $y^2 = x(x^2 + sx + 1)$, $s^2 = t$
  (`exists_rel_normal`), and $s$ and $-s$ give isomorphic pairs (`rel_normal_neg`).
- (b) Universality: the family $y^2 = x(x^2 + tx + t)$ over $D(t(t - 4))$ gives a chart of $\beta \circ \alpha^{-1}$ away
  from $t = 0$; the family $y^2 = x(x^2 + sx + 1)$ over $D(s^2 - 4)$, whose invariant is $s^2$, gives charts around every
  point by the descent lemma `exists_chart_at` of Theorem 8.4; the charts glue on $D(t - 4)$
  (`exists_hom_of_charts_away`).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite WeierstrassCurve TauCeti.AlgebraicGeometry MonoidalCategory
  ModularFormsKB.Milne.LevelTwoChart ModularFormsKB.Milne.CyclicTwo MonObj TauCeti Polynomial

noncomputable section

namespace ModularFormsKB.Milne.CyclicTwoModuli

open Ch8Counterexample LevelTwoModuli

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The polynomial $t - 4$. -/
abbrev tPoly : k[X] := X - C 4

theorem tPoly_ne_zero : (tPoly : k[X]) ≠ 0 := X_sub_C_ne_zero 4

variable (k) in
/-- **The moduli variety** $M = \mathbb A^1 \smallsetminus \{4\} = D(t - 4)$. -/
abbrev tLine : Variety k := lineVariety (tPoly (k := k)) tPoly_ne_zero

/-- Pairs $(E, I)$, $I$ a cyclic subgroup of order two. -/
abbrev Pair (V : Variety k) := LevelPair (ModuliProblem.gammaZero (Spec (CommRingCat.of k)) 2) V

/-- The cyclic subgroup of a pair. -/
abbrev sub {V : Variety k} (x : Pair V) := ModuliProblem.gammaZeroEquiv _ x.2

/-- **The pair of a point of exact order two.** -/
def pairOf (V : Variety k) (E : EllipticCurveGeom V.obj.left) (P : 𝟙_ (Over V.obj.left) ⟶ Over.mk E.structureMap)
    (hP : E.IsOfExactOrder P 2) : Pair V :=
  ⟨E, (ModuliProblem.gammaZeroEquiv _).symm ⟨E.multiplesDivisor P 2, hP.isCyclicSubgroup_multiplesDivisor⟩⟩

theorem pairOf_congr (V : Variety k) (E : EllipticCurveGeom V.obj.left)
    {P P' : 𝟙_ (Over V.obj.left) ⟶ Over.mk E.structureMap} (hP : E.IsOfExactOrder P 2)
    (hP' : E.IsOfExactOrder P' 2) (h : P = P') : pairOf V E P hP = pairOf V E P' hP' := by
  subst h; rfl

/-- Pulling the structure of `pairOf` back along an arrow of `Ell/k`. -/
theorem map_pairOf {V V' : Variety k} {E : EllipticCurveGeom V.obj.left} {E' : EllipticCurveGeom V'.obj.left}
    (f : V'.ellObj E' ⟶ V.ellObj E) (P : 𝟙_ (Over V.obj.left) ⟶ Over.mk E.structureMap)
    (hP : E.IsOfExactOrder P 2) :
    (ModuliProblem.gammaZero _ 2).map f.op (pairOf V E P hP).2 =
      (pairOf V' E' (EllipticCurveGeom.pointsPullback f.isPullback f.zero_total P)
        (hP.pointsPullback _ _)).2 := by
  apply (ModuliProblem.gammaZeroEquiv _).injective
  apply Subtype.ext
  exact (EllipticCurveGeom.multiplesDivisor_pointsPullback f.isPullback f.zero_total P 2).symm

/-- An isomorphism over the identity carrying the points to each other gives isomorphic pairs. -/
theorem rel_pairOf_hom {V : Variety k} {E E' : EllipticCurveGeom V.obj.left}
    (f : V.ellObj E' ⟶ V.ellObj E) (hf : f.base = 𝟙 _) (P : 𝟙_ (Over V.obj.left) ⟶ Over.mk E.structureMap)
    (hP : E.IsOfExactOrder P 2) :
    LevelPair.Rel (pairOf V E' (EllipticCurveGeom.pointsPullback f.isPullback f.zero_total P)
      (hP.pointsPullback _ _)) (pairOf V E P hP) :=
  ⟨f, hf, map_pairOf f P hP⟩

/-! ### The invariant morphism -/

variable (h2 : ((2 : ℕ) : k) ≠ 0)
include h2

/-- **The invariant morphism** $V \to M$ of a pair. -/
def cycMor {V : Variety k} (x : Pair V) : V ⟶ tLine k :=
  ⟨Over.homMk (cycMap (two_ne_zero' h2) V.obj.hom (sub x).2)
    (cycMap_specStructure (two_ne_zero' h2) V.obj.hom (sub x).2)⟩

theorem cycMor_left {V : Variety k} (x : Pair V) :
    (cycMor h2 x).hom.left = cycMap (two_ne_zero' h2) V.obj.hom (sub x).2 := rfl

theorem cycMap_hom {V V' : Variety k} (x : Pair V) (E' : EllipticCurveGeom V'.obj.left)
    (f : V'.ellObj E' ⟶ V.ellObj x.1) :
    cycMap (two_ne_zero' h2) V'.obj.hom (sub (⟨E', (ModuliProblem.gammaZero _ 2).map f.op x.2⟩ : Pair V')).2 =
      f.base ≫ cycMap (two_ne_zero' h2) V.obj.hom (sub x).2 :=
  cycMap_comp (two_ne_zero' h2) V.obj.hom V'.obj.hom (I := (sub x).1) f.isPullback f.zero_total
    f.base_structureMap (sub x).2 _

theorem cycMor_rel {V : Variety k} {x y : Pair V} (h : LevelPair.Rel x y) : cycMor h2 x = cycMor h2 y := by
  obtain ⟨f, hf, hfy⟩ := h
  have hx : x = ⟨x.1, (ModuliProblem.gammaZero _ 2).map f.op y.2⟩ := Sigma.ext rfl (heq_of_eq hfy.symm)
  rw [hx]
  apply InducedCategory.hom_ext
  apply Over.OverMorphism.ext
  rw [cycMor_left, cycMor_left]
  have := cycMap_hom h2 y x.1 f
  rw [hf, Category.id_comp] at this
  exact this

theorem cycMor_pull {V W : Variety k} (φ : W ⟶ V) (x : Pair V) :
    cycMor h2 (LevelPair.pull φ x) = φ ≫ cycMor h2 x := by
  apply InducedCategory.hom_ext
  apply Over.OverMorphism.ext
  rw [cycMor_left]
  exact cycMap_hom h2 x _ (LevelPair.pullHom φ x.1)

omit h2 in
theorem ne_zero_of_order_two {S : Scheme.{u}} (q : S ⟶ Spec (CommRingCat.of k)) (h2 : ((2 : ℕ) : k) ≠ 0)
    {E : EllipticCurveGeom S} {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} (hP : E.IsOfExactOrder P 2) (s : S) :
    P.left s ≠ E.zero s := by
  have := hP.pow_left_apply_ne_zero (two_ne_zero_residue (two_ne_zero' h2) q s) (k := 1) one_pos one_lt_two
  simpa using this

/-- The invariant morphism of `pairOf` is the invariant map `tMap` of the point. -/
theorem cycMor_pairOf_left {V : Variety k} (E : EllipticCurveGeom V.obj.left)
    (P : 𝟙_ (Over V.obj.left) ⟶ Over.mk E.structureMap) (hP : E.IsOfExactOrder P 2) :
    (cycMor h2 (pairOf V E P hP)).hom.left = tMap (two_ne_zero' h2) V.obj.hom hP.pow_eq_one
      (ne_zero_of_order_two V.obj.hom h2 hP) := by
  rw [cycMor_left]
  let G : Gen (sub (pairOf V E P hP)).1 (𝟙 V.obj.left) :=
    ⟨E, 𝟙 _, isPullback_id E, (Category.comp_id _).trans (Category.id_comp _).symm, P, hP,
      Scheme.IdealSheafData.comap_id _⟩
  have := cycMap_spec (two_ne_zero' h2) V.obj.hom (sub (pairOf V E P hP)).2 (𝟙 _) G
  rw [Category.id_comp] at this
  rw [this]
  change tMap _ _ _ _ = tMap _ _ _ _
  congr 1

/-- $\alpha$: the invariant of a class of pairs over $k$. -/
def alpha : (cyclicFunctor k 2).obj (op (Variety.point k)) → (Variety.point k ⟶ tLine k) :=
  Quotient.lift (cycMor h2) fun _ _ h ↦ cycMor_rel h2 h

/-! ### Weierstrass pairs -/

omit h2 in
theorem specStructure_self : specStructure k k = 𝟙 (Spec (CommRingCat.of k)) := by
  simp only [specStructure]
  convert Spec.map_id (CommRingCat.of k)

/-- **A point $(x, y)$ with $2y + a_1 x + a_3 = 0$ has exact order two.** -/
theorem isOfExactOrder_affine {R : Type u} [CommRing R] [Algebra k R] (W : WeierstrassCurve R) [W.IsElliptic]
    {x y : R} (h : W.toAffine.Equation x y) (hy : 2 * y + W.a₁ * x + W.a₃ = 0) :
    W.toEllipticCurveGeom.IsOfExactOrder (affinePointHom W h) 2 := by
  have hres := two_ne_zero_of_over h2 (specStructure k R)
  have hsq : affinePointHom W h ^ 2 = 1 := by
    have hneg : W.toAffine.negY x y = y := by simp only [Affine.negY]; linear_combination -hy
    have hinv : (affinePointHom W h)⁻¹ = affinePointHom W h :=
      (affinePointHom_inv' h).trans (affinePointHom_congr W _ h rfl hneg)
    rw [sq]
    nth_rewrite 1 [← hinv]
    exact inv_mul_cancel _
  let φ := (zmodMonoidHomEquiv 2 _).symm ⟨affinePointHom W h, hsq⟩
  have hφ1 : φ (.ofAdd 1) = affinePointHom W h := zmodMonoidHomEquiv_symm_apply_ofAdd_one _
  have hφ : W.toEllipticCurveGeom.IsFiberwiseInjective φ := by
    refine EllipticCurveGeom.isFiberwiseInjective_zmod_iff.mpr fun j hj hj2 s ↦ ?_
    obtain rfl : j = 1 := by omega
    rw [pow_one, hφ1]
    exact affinePointHom_ne_zero h s
  have := EllipticCurveGeom.isFiberwiseInjective_iff_isOfNaiveExactOrder.mp hφ
  rw [hφ1] at this
  exact this.isOfExactOrder hres

/-- The pair of a Weierstrass family over a finitely generated domain with a point of order two. -/
abbrev wPair (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (W : WeierstrassCurve R) [W.IsElliptic] {x y : R} (h : W.toAffine.Equation x y)
    (hy : 2 * y + W.a₁ * x + W.a₃ = 0) : Pair (domVariety (k := k) R) :=
  pairOf (domVariety R) W.toEllipticCurveGeom (affinePointHom W h) (isOfExactOrder_affine h2 W h hy)

/-- The pair of a Weierstrass curve over $k$ with a point of order two. -/
abbrev kPair (W : WeierstrassCurve k) [W.IsElliptic] {x y : k} (h : W.toAffine.Equation x y)
    (hy : 2 * y + W.a₁ * x + W.a₃ = 0) : Pair (Variety.point k) :=
  pairOf (Variety.point k) W.toEllipticCurveGeom (affinePointHom W h) (isOfExactOrder_affine h2 W h hy)

omit h2 in
theorem eval_tPoly_ne_zero {l : k} (hl : IsUnit (l - 4)) : (tPoly (k := k)).eval l ≠ 0 := by
  simpa using hl.ne_zero

omit h2 in
/-- The point of $M$ with coordinate $l$ is $\operatorname{Spec}$ of $t \mapsto l$. -/
theorem spec_tLift_eq (l : k) (hl : IsUnit (l - 4)) :
    Spec.map (CommRingCat.ofHom (tLift (algebraMap k k) l hl)) =
      (linePt (tPoly (k := k)) tPoly_ne_zero l (eval_tPoly_ne_zero hl)).hom.left := by
  change _ = Spec.map (CommRingCat.ofHom (evalAwayAlg _ l _).toRingHom)
  congr 2

/-- **The invariant of a Weierstrass family.** -/
theorem cycMor_wPair_left (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (W : WeierstrassCurve R) [W.IsElliptic] {x y : R} (h : W.toAffine.Equation x y)
    (hy : 2 * y + W.a₁ * x + W.a₃ = 0) :
    (cycMor h2 (wPair h2 R W h hy)).hom.left = Spec.map (CommRingCat.ofHom
      (tLift (algebraMap k R) (inv W (isUnit_coeffB_weierstrass (two_ne_zero' h2) W h hy))
        (isUnit_inv_weierstrass_sub_four (two_ne_zero' h2) W h hy))) := by
  exact (cycMor_pairOf_left h2 _ _ _).trans (tMap_weierstrass (two_ne_zero' h2) W h hy _ _)

/-- **The invariant of a Weierstrass curve over $k$.** -/
theorem cycMor_kPair_left (W : WeierstrassCurve k) [W.IsElliptic] {x y : k} (h : W.toAffine.Equation x y)
    (hy : 2 * y + W.a₁ * x + W.a₃ = 0) :
    cycMor h2 (kPair h2 W h hy) = linePt (tPoly (k := k)) tPoly_ne_zero
      (inv W (isUnit_coeffB_weierstrass (two_ne_zero' h2) W h hy))
      (eval_tPoly_ne_zero (isUnit_inv_weierstrass_sub_four (two_ne_zero' h2) W h hy)) := by
  apply InducedCategory.hom_ext
  apply Over.OverMorphism.ext
  refine (cycMor_pairOf_left h2 _ _ _).trans ?_
  rw [← spec_tLift_eq _ (isUnit_inv_weierstrass_sub_four (two_ne_zero' h2) W h hy)]
  have := tMap_weierstrass (two_ne_zero' h2) W h hy
    (isOfExactOrder_affine h2 W h hy).pow_eq_one
    (ne_zero_of_order_two (specStructure k k) h2 (isOfExactOrder_affine h2 W h hy))
  rw [← this]
  change tMap _ _ _ _ = tMap _ _ _ _
  congr 1
  exact specStructure_self.symm

/-- **The invariant at a $k$-point of a Weierstrass family.** -/
theorem cycMor_pull_wPair (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (W : WeierstrassCurve R) [W.IsElliptic] {x y : R} (h : W.toAffine.Equation x y)
    (hy : 2 * y + W.a₁ * x + W.a₃ = 0) (τ : R →ₐ[k] k) :
    cycMor h2 (LevelPair.pull (algPoint τ) (wPair h2 R W h hy)) = linePt (tPoly (k := k)) tPoly_ne_zero
      (τ (inv W (isUnit_coeffB_weierstrass (two_ne_zero' h2) W h hy)))
      (eval_tPoly_ne_zero (by
        have := (isUnit_inv_weierstrass_sub_four (two_ne_zero' h2) W h hy).map τ
        rwa [map_sub, map_ofNat] at this)) := by
  have hl' : IsUnit (τ (inv W (isUnit_coeffB_weierstrass (two_ne_zero' h2) W h hy)) - 4) := by
    have := (isUnit_inv_weierstrass_sub_four (two_ne_zero' h2) W h hy).map τ
    rwa [map_sub, map_ofNat] at this
  rw [cycMor_pull]
  apply InducedCategory.hom_ext
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ (cycMor h2 (wPair h2 R W h hy)).hom.left = _
  rw [cycMor_wPair_left, ← spec_tLift_eq _ hl']
  refine (Spec.map_comp _ _).symm.trans ?_
  rw [← CommRingCat.ofHom_comp]
  congr 2
  apply tLift_ext
  · intro a
    have e1 := RingHom.congr_fun (tLift_algebraMap_k (algebraMap k R) _
      (isUnit_inv_weierstrass_sub_four (two_ne_zero' h2) W h hy)) a
    have e2 := RingHom.congr_fun (tLift_algebraMap_k (algebraMap k k) _ hl') a
    simp only [RingHom.comp_apply] at e1 e2 ⊢
    rw [e1, e2]
    exact τ.commutes a
  · rw [RingHom.comp_apply, tLift_algebraMap, Polynomial.eval₂_X, tLift_algebraMap, Polynomial.eval₂_X]
    rfl

/-! ### Normal forms over $k$ -/

omit h2 in
/-- The Weierstrass curve $y^2 = x(x^2 + ax + b)$. -/
abbrev wc {R : Type u} [CommRing R] (a b : R) : WeierstrassCurve R := ⟨0, a, 0, b, 0⟩

omit h2 in
theorem wc_Δ {R : Type u} [CommRing R] (a b : R) : (wc a b).Δ = 16 * b ^ 2 * (a ^ 2 - 4 * b) := by
  simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]
  ring

omit h2 in
theorem wc_equation {R : Type u} [CommRing R] (a b : R) : (wc a b).toAffine.Equation 0 0 := by
  rw [Affine.equation_iff]
  simp

omit h2 in
theorem wc_hy {R : Type u} [CommRing R] (a b : R) : 2 * (0 : R) + (wc a b).a₁ * 0 + (wc a b).a₃ = 0 := by
  simp

omit h2 in
theorem inv_wc {R : Type u} [CommRing R] (a b : R) (hB : IsUnit (8 * coeffB (wc a b) 0)) (l : R)
    (hl : l * (16 * b) = 16 * a ^ 2) : inv (wc a b) hB = l := by
  rw [inv_eq_iff]
  simp only [coeffA, coeffB, b₂, b₄]
  linear_combination hl

omit h2 in
theorem linePt_congr {l l' : k} (h : l = l') (hl : (tPoly (k := k)).eval l ≠ 0)
    (hl' : (tPoly (k := k)).eval l' ≠ 0) :
    linePt (tPoly (k := k)) tPoly_ne_zero l hl = linePt tPoly tPoly_ne_zero l' hl' := by
  subst h; rfl

omit h2 in
theorem linePt_inj {l l' : k} {hl : (tPoly (k := k)).eval l ≠ 0} {hl' : (tPoly (k := k)).eval l' ≠ 0}
    (h : linePt (tPoly (k := k)) tPoly_ne_zero l hl = linePt tPoly tPoly_ne_zero l' hl') : l = l' := by
  have h1 := congrArg (fun v ↦ v.hom.left) h
  change Spec.map (CommRingCat.ofHom (evalAwayAlg _ l hl).toRingHom) =
    Spec.map (CommRingCat.ofHom (evalAwayAlg _ l' hl').toRingHom) at h1
  have h3 := congrArg (fun φ : CommRingCat.of (TRing k) ⟶ CommRingCat.of k ↦ φ.hom (algebraMap k[X] _ X))
    (Spec.map_injective h1)
  simpa [evalAwayAlg_algebraMap] using h3

theorem kPair_congr_pt (W : WeierstrassCurve k) [W.IsElliptic] {x y x' y' : k}
    (h : W.toAffine.Equation x y) (h' : W.toAffine.Equation x' y') (hy : 2 * y + W.a₁ * x + W.a₃ = 0)
    (hy' : 2 * y' + W.a₁ * x' + W.a₃ = 0) (hx : x = x') (hyy : y = y') :
    kPair h2 W h hy = kPair h2 W h' hy' := by
  subst hx hyy; rfl

/-- Equal curves with the same point give isomorphic pairs. -/
theorem rel_kPair_congr {W W' : WeierstrassCurve k} (hW : W = W') [W.IsElliptic] [W'.IsElliptic] {x y : k}
    (h : W.toAffine.Equation x y) (h' : W'.toAffine.Equation x y) (hy : 2 * y + W.a₁ * x + W.a₃ = 0)
    (hy' : 2 * y + W'.a₁ * x + W'.a₃ = 0) : LevelPair.Rel (kPair h2 W h hy) (kPair h2 W' h' hy') := by
  subst hW
  exact LevelPair.rel_refl _

/-- **A change of variables gives isomorphic pairs.** -/
theorem rel_vc (W : WeierstrassCurve k) [W.IsElliptic] (C : VariableChange k) {x y : k}
    (h' : (C • W).toAffine.Equation x y) (hy' : 2 * y + (C • W).a₁ * x + (C • W).a₃ = 0)
    (hy : 2 * ((C.u : k) ^ 3 * y + (C.u : k) ^ 2 * C.s * x + C.t) + W.a₁ * ((C.u : k) ^ 2 * x + C.r) +
      W.a₃ = 0) :
    LevelPair.Rel (kPair h2 (C • W) h' hy')
      (kPair h2 W ((Affine.variableChange_equation W C x y).mpr h') hy) := by
  let vc : (Variety.point k).ellObj (C • W).toEllipticCurveGeom ⟶ (Variety.point k).ellObj W.toEllipticCurveGeom :=
    vcHom (𝟙 (Spec (CommRingCat.of k))) W C
  have hP := isOfExactOrder_affine h2 W ((Affine.variableChange_equation W C x y).mpr h') hy
  have hb : vc.base = 𝟙 _ := rfl
  have r := rel_pairOf_hom vc hb (affinePointHom W ((Affine.variableChange_equation W C x y).mpr h')) hP
  have e := pairOf_congr (Variety.point k) (C • W).toEllipticCurveGeom (hP.pointsPullback vc.isPullback vc.zero_total)
    (isOfExactOrder_affine h2 (C • W) h' hy') (pointsPullback_vcHom _ W C h')
  rw [e] at r
  exact r

omit h2 in
/-- A pair over $k$ is isomorphic to the pair of a generator. -/
theorem exists_rel_gen (x : Pair (Variety.point k)) :
    ∃ (E : EllipticCurveGeom (Spec (CommRingCat.of k))) (P : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶
      Over.mk E.structureMap) (hP : E.IsOfExactOrder P 2),
      LevelPair.Rel x (pairOf (Variety.point k) E P hP) := by
  obtain ⟨G⟩ := nonempty_gen_spec (sub x).2
  let f : (Variety.point k).ellObj G.E' ⟶ (Variety.point k).ellObj x.1 :=
    { base := 𝟙 (Spec (CommRingCat.of k))
      base_structureMap := Category.id_comp (𝟙 (Spec (CommRingCat.of k)))
      total := G.g
      isPullback := G.hg
      zero_total := G.h0 }
  refine ⟨G.E', G.P, G.hP, LevelPair.rel_symm ⟨f, rfl, ?_⟩⟩
  apply (ModuliProblem.gammaZeroEquiv _).injective
  apply Subtype.ext
  exact G.hI

/-- A pair of a generator over $k$ is isomorphic to the pair of an affine point of a Weierstrass curve. -/
theorem exists_rel_weierstrass (E : EllipticCurveGeom (Spec (CommRingCat.of k)))
    (P : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Over.mk E.structureMap) (hP : E.IsOfExactOrder P 2) :
    ∃ (W : WeierstrassCurve k) (_ : W.IsElliptic) (x y : k) (h : W.toAffine.Equation x y)
      (hy : 2 * y + W.a₁ * x + W.a₃ = 0),
      LevelPair.Rel (pairOf (Variety.point k) E P hP) (kPair h2 W h hy) := by
  obtain ⟨W, hW, e0, he0, hz⟩ := E.exists_iso_toEllipticCurveGeom
  let a : (Variety.point k).ellObj W.toEllipticCurveGeom ⟶ (Variety.point k).ellObj E := isoHom _ e0 he0 hz
  have hb : a.base = 𝟙 _ := rfl
  have r := rel_pairOf_hom a hb P hP
  have hP' := hP.pointsPullback a.isPullback a.zero_total
  obtain ⟨x, y, h, hxy⟩ := exists_affinePointHom _ (ne_zero_of_order_two (𝟙 _) h2 hP')
  have hy : 2 * y + W.a₁ * x + W.a₃ = 0 := by
    apply two_torsion_of_left_neg h
    rw [← hxy]
    exact left_neg_self hP'.pow_eq_one
  refine ⟨W, hW, x, y, h, hy, LevelPair.rel_symm ?_⟩
  have e := pairOf_congr (Variety.point k) W.toEllipticCurveGeom hP' (isOfExactOrder_affine h2 W h hy) hxy
  rw [e] at r
  exact r

omit h2 in
theorem sixteen_ne_zero (h2 : ((2 : ℕ) : k) ≠ 0) : (16 : k) ≠ 0 := by
  have : (16 : k) = ((2 : ℕ) : k) ^ 4 := by norm_num
  rw [this]
  exact pow_ne_zero _ h2

omit h2 in
theorem isElliptic_wc {s : k} (h2 : ((2 : ℕ) : k) ≠ 0) (hs : s ^ 2 - 4 ≠ 0) : (wc s 1).IsElliptic := by
  refine ⟨?_⟩
  rw [wc_Δ]
  refine IsUnit.mk0 _ ?_
  simpa [sixteen_ne_zero h2] using hs

/-- **Normal form**: every pair over $k$ is isomorphic to the pair of $(0, 0)$ on $y^2 = x(x^2 + sx + 1)$. -/
theorem exists_rel_normal (x : Pair (Variety.point k)) :
    ∃ (s : k) (hs : s ^ 2 - 4 ≠ 0), LevelPair.Rel x
      (haveI := isElliptic_wc h2 hs; kPair h2 (wc s 1) (wc_equation s 1) (wc_hy s 1)) := by
  have h2' := two_ne_zero' h2
  obtain ⟨E, P, hP, r1⟩ := exists_rel_gen x
  obtain ⟨W, hW, x₀, y₀, h, hy, r2⟩ := exists_rel_weierstrass h2 E P hP
  -- move the point to `(0, 0)` and make `a₁ = a₃ = 0`
  let C₀ : VariableChange k := ⟨1, x₀, -W.a₁ * 2⁻¹, y₀⟩
  have hh : (2 : k) * 2⁻¹ = 1 := mul_inv_cancel₀ h2'
  have h0 : (C₀ • W).toAffine.Equation 0 0 := by
    rw [← Affine.variableChange_equation]
    convert h using 2 <;> simp [C₀]
  have ha₁ : (C₀ • W).a₁ = 0 := by
    rw [variableChange_a₁]
    simp only [C₀, inv_one, Units.val_one, one_mul]
    linear_combination (-W.a₁) * hh
  have ha₃ : (C₀ • W).a₃ = 0 := by
    rw [variableChange_a₃]
    simp only [C₀, inv_one, Units.val_one, one_pow, one_mul]
    linear_combination hy
  have ha₆ : (C₀ • W).a₆ = 0 := by
    have := h0
    rw [Affine.equation_iff] at this
    linear_combination -this
  have hW₀ : C₀ • W = wc (C₀ • W).a₂ (C₀ • W).a₄ := by
    ext
    exacts [ha₁, rfl, ha₃, rfl, ha₆]
  have hb : (C₀ • W).a₄ ≠ 0 := by
    intro hb
    have hΔ := (C₀ • W).isUnit_Δ
    rw [hW₀, wc_Δ, hb] at hΔ
    simp at hΔ
  have hy0 : 2 * (0 : k) + (C₀ • W).a₁ * 0 + (C₀ • W).a₃ = 0 := by rw [ha₁, ha₃]; ring
  have r3 := rel_vc h2 W C₀ h0 hy0 (by simp only [C₀, Units.val_one]; linear_combination hy)
  rw [kPair_congr_pt h2 W _ h _ hy (by simp [C₀]) (by simp [C₀])] at r3
  -- scale so that `a₄ = 1`
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (C₀ • W).a₄ (by norm_num : 0 < 4)
  have hu0 : u ≠ 0 := by rintro rfl; exact hb (by rw [← hu]; ring)
  let C₁ : VariableChange k := ⟨Units.mk0 u hu0, 0, 0, 0⟩
  set s := ((Units.mk0 u hu0)⁻¹ : kˣ) ^ 2 * (C₀ • W).a₂ with hsdef
  have hW₁ : C₁ • (C₀ • W) = wc s 1 := by
    ext
    · rw [variableChange_a₁, ha₁]; simp [C₁]
    · rw [variableChange_a₂, ha₁]; simp [C₁, hsdef]
    · rw [variableChange_a₃, ha₁, ha₃]; simp [C₁]
    · rw [variableChange_a₄, ha₁, ha₃]
      simp only [C₁, mul_zero, sub_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]
      rw [← hu, Units.val_inv_eq_inv_val, Units.val_mk0]
      field_simp
    · rw [variableChange_a₆, ha₁, ha₃, ha₆]; simp [C₁]
  have h1 : (C₁ • (C₀ • W)).toAffine.Equation 0 0 := by rw [hW₁]; exact wc_equation s 1
  have hy1 : 2 * (0 : k) + (C₁ • (C₀ • W)).a₁ * 0 + (C₁ • (C₀ • W)).a₃ = 0 := by
    rw [hW₁]; exact wc_hy s 1
  have r4 := rel_vc h2 (C₀ • W) C₁ h1 hy1 (by simp only [C₁]; rw [ha₁, ha₃]; ring)
  rw [kPair_congr_pt h2 (C₀ • W) _ h0 _ hy0 (by simp [C₁]) (by simp [C₁])] at r4
  have hs : s ^ 2 - 4 ≠ 0 := by
    intro hs
    have hΔ := (C₁ • (C₀ • W)).isUnit_Δ
    rw [hW₁, wc_Δ] at hΔ
    simp [hs] at hΔ
  haveI := isElliptic_wc h2 hs
  have r5 := rel_kPair_congr h2 hW₁ h1 (wc_equation s 1) hy1 (wc_hy s 1)
  refine ⟨s, hs, ?_⟩
  exact LevelPair.rel_trans r1 (LevelPair.rel_trans r2 (LevelPair.rel_trans (LevelPair.rel_symm r3)
    (LevelPair.rel_trans (LevelPair.rel_symm r4) r5)))

/-! ### Bijectivity of $\alpha$ -/

theorem eval_tPoly_sq_ne_zero {s : k} (hs : s ^ 2 - 4 ≠ 0) : (tPoly (k := k)).eval (s ^ 2) ≠ 0 := by
  simpa using hs

theorem alpha_kPair_wc {s : k} (hs : s ^ 2 - 4 ≠ 0) :
    haveI := isElliptic_wc h2 hs
    alpha h2 ⟦kPair h2 (wc s 1) (wc_equation s 1) (wc_hy s 1)⟧ =
      linePt (tPoly (k := k)) tPoly_ne_zero (s ^ 2) (eval_tPoly_sq_ne_zero h2 hs) := by
  haveI := isElliptic_wc h2 hs
  exact (cycMor_kPair_left h2 (wc s 1) (wc_equation s 1) (wc_hy s 1)).trans
    (linePt_congr (inv_wc _ _ _ _ (by ring)) _ _)

/-- **The normal forms of $s$ and $-s$ are isomorphic** (the change of variables $x \mapsto -x$). -/
theorem rel_normal_neg {s : k} (hs : s ^ 2 - 4 ≠ 0) (hs' : (-s) ^ 2 - 4 ≠ 0) :
    haveI := isElliptic_wc h2 hs; haveI := isElliptic_wc h2 hs'
    LevelPair.Rel (kPair h2 (wc (-s) 1) (wc_equation (-s) 1) (wc_hy (-s) 1))
      (kPair h2 (wc s 1) (wc_equation s 1) (wc_hy s 1)) := by
  haveI := isElliptic_wc h2 hs; haveI := isElliptic_wc h2 hs'
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : k) two_pos
  have hi0 : i ≠ 0 := by rintro rfl; simp at hi
  let C : VariableChange k := ⟨Units.mk0 i hi0, 0, 0, 0⟩
  have hi4 : i ^ 4 = 1 := by rw [show i ^ 4 = (i ^ 2) ^ 2 by ring, hi]; ring
  have hW : C • wc s 1 = wc (-s) 1 := by
    ext
    · rw [variableChange_a₁]; simp [C]
    · rw [variableChange_a₂]
      simp only [C, Units.val_inv_eq_inv_val, Units.val_mk0, mul_zero, sub_zero, add_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      rw [inv_pow, hi]
      simp
    · rw [variableChange_a₃]; simp [C]
    · rw [variableChange_a₄]
      simp only [C, Units.val_inv_eq_inv_val, Units.val_mk0, mul_zero, sub_zero, add_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      rw [inv_pow, hi4]
      simp
    · rw [variableChange_a₆]; simp [C]
  have h1 : (C • wc s 1).toAffine.Equation 0 0 := by rw [hW]; exact wc_equation (-s) 1
  have hy1 : 2 * (0 : k) + (C • wc s 1).a₁ * 0 + (C • wc s 1).a₃ = 0 := by rw [hW]; exact wc_hy (-s) 1
  have r := rel_vc h2 (wc s 1) C h1 hy1 (by simp [C])
  rw [kPair_congr_pt h2 (wc s 1) _ (wc_equation s 1) _ (wc_hy s 1) (by simp [C]) (by simp [C])] at r
  exact LevelPair.rel_trans (LevelPair.rel_symm (rel_kPair_congr h2 hW h1 (wc_equation (-s) 1) hy1
    (wc_hy (-s) 1))) r

theorem alpha_bijective : Function.Bijective (alpha h2) := by
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h x =>
    induction b using Quotient.inductionOn with
    | h y =>
    obtain ⟨s, hs, r1⟩ := exists_rel_normal h2 x
    obtain ⟨s', hs', r2⟩ := exists_rel_normal h2 y
    have e1 : alpha h2 ⟦x⟧ = _ := (cycMor_rel h2 r1).trans (alpha_kPair_wc h2 hs)
    have e2 : alpha h2 ⟦y⟧ = _ := (cycMor_rel h2 r2).trans (alpha_kPair_wc h2 hs')
    have hss := linePt_inj (e1.symm.trans (hab.trans e2))
    apply Quotient.sound
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hss with h | h
    · subst h
      exact LevelPair.rel_trans r1 (LevelPair.rel_symm r2)
    · subst h
      haveI := isElliptic_wc h2 hs'
      exact LevelPair.rel_trans r1 (LevelPair.rel_trans (rel_normal_neg h2 hs' hs) (LevelPair.rel_symm r2))
  · intro v
    obtain ⟨w, hw, rfl⟩ := exists_linePt tPoly_ne_zero v
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq w two_pos
    have hs : r ^ 2 - 4 ≠ 0 := by rw [hr]; simpa using hw
    haveI := isElliptic_wc h2 hs
    exact ⟨⟦kPair h2 (wc r 1) (wc_equation r 1) (wc_hy r 1)⟧,
      (alpha_kPair_wc h2 hs).trans (linePt_congr hr _ _)⟩

/-! ### Universality -/

section Universal

variable {Z : Variety k} (β : (cyclicFunctor k 2).obj (op (Variety.point k)) → (Variety.point k ⟶ Z))
  (hβ : ∀ (T : Variety k) (f : (cyclicFunctor k 2).obj (op T)),
    ∃ φ : T ⟶ Z, ∀ t : Variety.point k ⟶ T, t ≫ φ = β ((cyclicFunctor k 2).map t.op f))

omit [IsAlgClosed k] h2 in
theorem eval_tPoly_zero_ne_zero (h2 : ((2 : ℕ) : k) ≠ 0) : (tPoly (k := k)).eval 0 ≠ 0 := by
  have : (4 : k) = ((2 : ℕ) : k) * ((2 : ℕ) : k) := by norm_num
  simp only [eval_sub, eval_X, eval_C, zero_sub, ne_eq, neg_eq_zero, this, mul_self_eq_zero]
  exact h2

open Classical in
/-- $\beta \circ \alpha^{-1}$ as a function of the coordinate. -/
def bfun (w : k) : Variety.point k ⟶ Z :=
  if hw : (tPoly (k := k)).eval w ≠ 0 then
    β ((Equiv.ofBijective _ (alpha_bijective h2)).symm (linePt tPoly tPoly_ne_zero w hw))
  else β ((Equiv.ofBijective _ (alpha_bijective h2)).symm
    (linePt tPoly tPoly_ne_zero 0 (eval_tPoly_zero_ne_zero h2)))

include hβ in
/-- A Weierstrass family gives a regular map with the values of $\beta \circ \alpha^{-1}$ at its invariants. -/
theorem exists_hom_wPair (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (W : WeierstrassCurve R) [W.IsElliptic] {x y : R} (h : W.toAffine.Equation x y)
    (hy : 2 * y + W.a₁ * x + W.a₃ = 0) :
    ∃ hh : domVariety (k := k) R ⟶ Z, ∀ τ : R →ₐ[k] k,
      algPoint τ ≫ hh = bfun h2 β (τ (inv W (isUnit_coeffB_weierstrass (two_ne_zero' h2) W h hy))) := by
  obtain ⟨φ, hφ⟩ := hβ _ ⟦wPair h2 R W h hy⟧
  refine ⟨φ, fun τ ↦ (hφ (algPoint τ)).trans ?_⟩
  have e := cycMor_pull_wPair h2 R W h hy τ
  rw [bfun, dif_pos (eval_tPoly_ne_zero (by
    have := (isUnit_inv_weierstrass_sub_four (two_ne_zero' h2) W h hy).map τ
    rwa [map_sub, map_ofNat] at this))]
  congr 1
  rw [Equiv.eq_symm_apply]
  exact e

/-- The polynomial $t(t - 4)$ of the seed chart. -/
abbrev seed1 : k[X] := X * (X - C 4)

omit [IsAlgClosed k] h2 in
theorem seed1_ne_zero : (seed1 : k[X]) ≠ 0 := mul_ne_zero X_ne_zero (X_sub_C_ne_zero 4)

/-- The polynomial $s^2 - 4$. -/
abbrev seed2 : k[X] := X ^ 2 - C 4

omit [IsAlgClosed k] h2 in
theorem seed2_ne_zero : (seed2 : k[X]) ≠ 0 := by
  intro h
  have := congrArg (Polynomial.natDegree) h
  rw [natDegree_sub_C, natDegree_X_pow] at this
  simp at this

omit h2 in
theorem isUnit_two_away (h2 : ((2 : ℕ) : k) ≠ 0) (s : k[X]) : IsUnit (2 : Localization.Away s) := by
  rw [← map_ofNat (algebraMap k (Localization.Away s)) 2]
  exact (IsUnit.mk0 (2 : k) (two_ne_zero' h2)).map _

include hβ in
/-- **The seed chart**: the family $y^2 = x(x^2 + tx + t)$ over $D(t(t - 4))$. -/
theorem nonempty_seed : Nonempty (LineChart Z (bfun h2 β)) := by
  haveI := isDomain_away k (seed1_ne_zero (k := k))
  set t : Localization.Away (seed1 : k[X]) := algebraMap k[X] _ X
  have ht : IsUnit t := by
    have := isUnit_algebraMap_of_dvd (k := k) (dvd_mul_right X (X - C 4)) 1
    rwa [pow_one] at this
  have ht4 : IsUnit (t - 4) := by
    have := isUnit_algebraMap_of_dvd (k := k) (dvd_mul_left (X - C 4) X) 1
    rwa [pow_one, map_sub, show (C 4 : k[X]) = 4 from map_ofNat C 4, map_ofNat] at this
  have h16 : IsUnit (16 : Localization.Away (seed1 : k[X])) := by
    have := (isUnit_two_away h2 (seed1 : k[X])).pow 4
    norm_num at this
    exact this
  haveI : (wc t t).IsElliptic := ⟨by
    rw [wc_Δ, show t ^ 2 - 4 * t = t * (t - 4) by ring]
    exact (h16.mul (ht.pow 2)).mul (ht.mul ht4)⟩
  obtain ⟨hh, hhv⟩ := exists_hom_wPair h2 β hβ _ (wc t t) (wc_equation t t) (wc_hy t t)
  refine ⟨⟨seed1, seed1_ne_zero, hh, fun w hw ↦ ?_⟩⟩
  have := hhv (evalAwayAlg _ w hw)
  rw [inv_wc _ _ _ t (by ring), evalAwayAlg_algebraMap, eval_X] at this
  exact this

include hβ in
/-- **Theorem 8.6 ($N = 2$), condition (b).** -/
theorem alpha_universal :
    ∃ ψ : tLine k ⟶ Z, ∀ v : Variety.point k ⟶ tLine k,
      v ≫ ψ = β ((Equiv.ofBijective _ (alpha_bijective h2)).symm v) := by
  classical
  obtain ⟨c₁⟩ := nonempty_seed h2 β hβ
  haveI := isDomain_away k (seed2_ne_zero (k := k))
  set σ : Localization.Away (seed2 : k[X]) := algebraMap k[X] _ X
  have hσ4 : IsUnit (σ ^ 2 - 4) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (seed2 : k[X])) (seed2 : k[X])
    rwa [map_sub, map_pow, show (C 4 : k[X]) = 4 from map_ofNat C 4, map_ofNat] at this
  have h16 : IsUnit (16 : Localization.Away (seed2 : k[X])) := by
    have := (isUnit_two_away h2 (seed2 : k[X])).pow 4
    norm_num at this
    exact this
  haveI : (wc σ 1).IsElliptic := ⟨by
    rw [wc_Δ]
    convert h16.mul hσ4 using 1
    ring⟩
  obtain ⟨hh, hhv⟩ := exists_hom_wPair h2 β hβ _ (wc σ 1) (wc_equation σ 1) (wc_hy σ 1)
  let π : k[X] →ₐ[k] Localization.Away (seed2 : k[X]) := Polynomial.aeval (σ ^ 2)
  have hπX : π X = σ ^ 2 := aeval_X _
  have hπ : Function.Injective π := by
    have hπ' : π = (IsScalarTower.toAlgHom k k[X] (Localization.Away (seed2 : k[X]))).comp (expand k 2) := by
      apply Polynomial.algHom_ext
      simp [π, σ]
    rw [hπ']
    exact (IsLocalization.injective (Localization.Away (seed2 : k[X]))
      (powers_le_nonZeroDivisors_of_noZeroDivisors seed2_ne_zero)).comp (expand_injective two_pos)
  have hhv' : ∀ τ : Localization.Away (seed2 : k[X]) →ₐ[k] k, algPoint τ ≫ hh = bfun h2 β (τ (π X)) := by
    intro τ
    rw [hhv, hπX, inv_wc _ _ _ (σ ^ 2) (by ring)]
  have hcov : ∀ v : k, (tPoly (k := k)).eval v ≠ 0 → ∃ c : LineChart Z (bfun h2 β), c.s.eval v ≠ 0 := by
    intro v hv
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq v two_pos
    have hr4 : (seed2 : k[X]).eval r ≠ 0 := by simpa [hr] using hv
    refine exists_chart_at π hπ hh hhv' c₁ v (evalAwayAlg _ r hr4) ?_
    rw [hπX, map_pow, evalAwayAlg_algebraMap, eval_X, hr]
  obtain ⟨ψ, hψ⟩ := exists_hom_of_charts_away tPoly_ne_zero hcov
  refine ⟨ψ, fun v ↦ ?_⟩
  obtain ⟨w, hw, rfl⟩ := exists_linePt tPoly_ne_zero v
  rw [hψ, bfun, dif_pos hw]

end Universal

/-- **The line $\mathbb A^1 \smallsetminus \{4\}$ solves the moduli problem $\mathcal E_{0,2}$.** -/
theorem isModuliSolution_two :
    IsModuliSolution (cyclicFunctor k 2) (tLine k) (Equiv.ofBijective _ (alpha_bijective h2)) := by
  refine ⟨fun T f ↦ ?_, fun Z β hβ ↦ alpha_universal h2 β hβ⟩
  induction f using Quotient.inductionOn with
  | h x => exact ⟨cycMor h2 x, fun t ↦ (cycMor_pull h2 t x).symm⟩

end ModularFormsKB.Milne.CyclicTwoModuli

namespace ModularFormsKB.Milne

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Milne, Theorem 8.6 for $N = 2$**, unconditionally: over an algebraically closed field with $2 \ne 0$, the line
$\mathbb A^1 \smallsetminus \{4\}$ with the invariant $t = a^2/b$ of $y^2 = x(x^2 + ax + b)$ solves $\mathcal E_{0,2}$. -/
@[kb "milne2017mf" "Section 8, Theorem 8.6 for N = 2 (pdf p. 100)"]
theorem cyclicModuliSolution_two : CyclicModuliSolution k 2 :=
  ⟨fun hN ↦ ⟨CyclicTwoModuli.tLine k, _, CyclicTwoModuli.isModuliSolution_two hN⟩⟩

end ModularFormsKB.Milne
