import ModularFormsKB.Milne.Ch8.YOneDescent
import ModularFormsKB.Milne.Ch8.CyclicTwoModuli

/-!
# Theorem 8.6 for $N \ge 4$: the invariant morphism and the bijection $\alpha$

For a pair $(E, I)$ over a variety $V$ ($I$ cyclic of order $N$), the invariant morphism $V \to M$ is the descended
map `cycMap` (`cycMor`, invariant under isomorphism and natural: `cycMor_rel`, `cycMor_pull`). The universal pair
over $Y_1(N)$ (`xu`) has invariant $q : Y_1(N) \to M$ (`cycMor_xu`), and every pair over $k$ is the pullback of the
universal pair along its classifying point (`rel_pull_xu`). The map $\alpha$ from pairs over $k$ to $M(k)$ is bijective
(`alpha_bijective`): two pairs with the same invariant have classifying points in the same orbit of
$(\mathbb Z/N)^\times$ (Tau Ceti's `exists_comp_specComap_eq`), hence are isomorphic (a unit multiple of a generator
generates the same subgroup, `multiplesDivisor_pow_unit`); every $k$-point of $M$ lifts to $Y_1(N)$.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TauCeti.AlgebraicGeometry MonoidalCategory MonObj
  TauCeti.AffineInvariantQuotient ModularFormsKB.Milne.LevelTwoChart

noncomputable section

namespace ModularFormsKB.Milne.YOneModuli

open CyclicN CyclicThree CyclicTwo

variable {k : Type u} [Field k] [IsAlgClosed k] {N : ℕ} [NeZero N] [hNf : Fact (((N : ℕ) : k) ≠ 0)]
  [h4f : Fact (4 ≤ N)]

instance instIsAffineY : IsAffine (Y k N).base := isAffine_Y hNf.out

variable (N) in
/-- Pairs $(E, I)$, $I$ a cyclic subgroup of order $N$. -/
abbrev Pair (V : Variety k) := LevelPair (ModuliProblem.gammaZero (B k) N) V

/-- The cyclic subgroup of a pair. -/
abbrev sub {V : Variety k} (x : Pair N V) := ModuliProblem.gammaZeroEquiv _ x.2

variable (k N) in
/-- $Y_1(N)$ as a variety. -/
abbrev yV : Variety k := yVar (k := k) (N := N) hNf.out h4f.out

/-- **The invariant morphism** $V \to M$ of a pair. -/
def cycMor {V : Variety k} (x : Pair N V) : V ⟶ mVar k N :=
  ⟨Over.homMk (cycMap V.obj.hom (sub x).2) (cycMap_specStructure V.obj.hom (sub x).2)⟩

theorem cycMor_left {V : Variety k} (x : Pair N V) : (cycMor x).hom.left = cycMap V.obj.hom (sub x).2 := rfl

theorem cycMap_hom {V V' : Variety k} (x : Pair N V) (E' : EllipticCurveGeom V'.obj.left)
    (f : V'.ellObj E' ⟶ V.ellObj x.1) :
    cycMap V'.obj.hom (sub (⟨E', (ModuliProblem.gammaZero _ N).map f.op x.2⟩ : Pair N V')).2 =
      f.base ≫ cycMap V.obj.hom (sub x).2 :=
  cycMap_comp V.obj.hom V'.obj.hom (I := (sub x).1) f.isPullback f.zero_total f.base_structureMap (sub x).2 _

theorem cycMor_rel {V : Variety k} {x y : Pair N V} (h : LevelPair.Rel x y) : cycMor x = cycMor y := by
  obtain ⟨f, hf, hfy⟩ := h
  have hx : x = ⟨x.1, (ModuliProblem.gammaZero _ N).map f.op y.2⟩ := Sigma.ext rfl (heq_of_eq hfy.symm)
  rw [hx]
  apply InducedCategory.hom_ext
  apply Over.OverMorphism.ext
  rw [cycMor_left, cycMor_left]
  have := cycMap_hom y x.1 f
  rw [hf, Category.id_comp] at this
  exact this

theorem cycMor_pull {V W : Variety k} (φ : W ⟶ V) (x : Pair N V) :
    cycMor (LevelPair.pull φ x) = φ ≫ cycMor x := by
  apply InducedCategory.hom_ext
  apply Over.OverMorphism.ext
  rw [cycMor_left]
  exact cycMap_hom x _ (LevelPair.pullHom φ x.1)

/-- The pair of a $[\Gamma_1(N)]$-structure. -/
def zPair (V : Variety k) (E : EllipticCurveGeom V.obj.left)
    (α : (ModuliProblem.gammaOne (B k) N).obj (op (V.ellObj E))) : Pair N V :=
  ⟨E, (ModuliProblem.gammaOneToGammaZero (B k) N).app _ α⟩

/-- The invariant of the pair of a structure is `tStr`. -/
theorem cycMor_zPair_left (V : Variety k) (E : EllipticCurveGeom V.obj.left)
    (α : (ModuliProblem.gammaOne (B k) N).obj (op (V.ellObj E))) :
    (cycMor (zPair V E α)).hom.left = tStr α := by
  rw [cycMor_left]
  let G : Gen N (sub (zPair V E α)).1 (𝟙 V.obj.left) :=
    ⟨E, 𝟙 _, CyclicTwo.isPullback_id E, (Category.comp_id _).trans (Category.id_comp _).symm,
      (ModuliProblem.gammaOneEquiv _ α).1, (ModuliProblem.gammaOneEquiv _ α).2,
      Scheme.IdealSheafData.comap_id _⟩
  have := cycMap_spec V.obj.hom (sub (zPair V E α)).2 (𝟙 _) G
  rw [Category.id_comp] at this
  rw [this]
  change tStr _ = tStr _
  congr 1

/-- The structure of the universal subgroup on $Y_1(N)$. -/
def sU : (ModuliProblem.gammaZero (B k) N).obj (op (Y k N)) :=
  (ModuliProblem.gammaOneToGammaZero (B k) N).app _ (univ hNf.out h4f.out)

theorem map_cls_sU {X : EllObj (B k)} (α : (ModuliProblem.gammaOne (B k) N).obj (op X)) :
    (ModuliProblem.gammaZero (B k) N).map (cls hNf.out h4f.out α).op sU =
      (ModuliProblem.gammaOneToGammaZero (B k) N).app _ α := by
  rw [sU, ← NatTrans.naturality_apply (ModuliProblem.gammaOneToGammaZero (B k) N), map_cls_univ]

/-- A unit multiple of a structure gives the same subgroup. -/
theorem gammaOneToGammaZero_powStr {X : EllObj (B k)} (g : (ZMod N)ˣ)
    (α : (ModuliProblem.gammaOne (B k) N).obj (op X)) :
    (ModuliProblem.gammaOneToGammaZero (B k) N).app _ (powStr hNf.out g α) =
      (ModuliProblem.gammaOneToGammaZero (B k) N).app _ α := by
  apply (ModuliProblem.gammaZeroEquiv _).injective
  apply Subtype.ext
  rw [ModuliProblem.gammaZeroEquiv_gammaOneToGammaZero_app, ModuliProblem.gammaZeroEquiv_gammaOneToGammaZero_app,
    powStr_point]
  exact multiplesDivisor_pow_unit (by have := h4f.out; omega) (ModuliProblem.gammaOneEquiv X α).2.pow_eq_one g

variable (k N) in
/-- **The universal pair** over $Y_1(N)$. -/
def xu : Pair N (yV k N) := ⟨(Y k N).curve, sU⟩

/-- The invariant of the universal pair is the quotient map. -/
theorem cycMor_xu : (cycMor (xu k N)).hom.left = qmap := by
  have := cycMor_zPair_left (yV k N) (Y k N).curve (univ hNf.out h4f.out)
  have h2 : tStr (univ hNf.out h4f.out) = (qmap : (Y k N).base ⟶ _) := by
    unfold tStr
    rw [cls_univ]
    exact Category.id_comp _
  exact this.trans h2

/-- The variety morphism of a morphism of schemes into $Y_1(N)$ over $k$. -/
def toYV {V : Variety k} (f : V.obj.left ⟶ (Y k N).base) (hf : f ≫ (Y k N).structureMap = V.obj.hom) :
    V ⟶ yV k N :=
  ⟨Over.homMk f hf⟩

/-- **Every pair given by a structure is a pullback of the universal pair** along its classifying map. -/
theorem rel_pull_xu {V : Variety k} (E : EllipticCurveGeom V.obj.left)
    (α : (ModuliProblem.gammaOne (B k) N).obj (op (V.ellObj E))) :
    LevelPair.Rel (zPair V E α)
      (LevelPair.pull (toYV (cls hNf.out h4f.out α).base (cls hNf.out h4f.out α).base_structureMap) (xu k N)) := by
  have := LevelPair.rel_of_arrows (P := ModuliProblem.gammaZero (B k) N) (V := V) sU (cls hNf.out h4f.out α)
    (LevelPair.pullHom (toYV (cls hNf.out h4f.out α).base (cls hNf.out h4f.out α).base_structureMap)
      (Y k N).curve) rfl
  rw [map_cls_sU] at this
  exact this


/-! ### Bijectivity of $\alpha$ -/

/-- $\alpha$: the invariant of a class of pairs over $k$. -/
def alpha : (cyclicFunctor k N).obj (op (Variety.point k)) → (Variety.point k ⟶ mVar k N) :=
  Quotient.lift cycMor fun _ _ h ↦ cycMor_rel h

/-- A pair over $k$ is isomorphic to the pair of a structure (a generator of its subgroup). -/
theorem exists_rel_zPair (x : Pair N (Variety.point k)) :
    ∃ (E : EllipticCurveGeom (Variety.point k).obj.left)
      (α : (ModuliProblem.gammaOne (B k) N).obj (op ((Variety.point k).ellObj E))),
      LevelPair.Rel x (zPair (Variety.point k) E α) := by
  obtain ⟨G⟩ := nonempty_gen_spec (sub x).2
  let f : (Variety.point k).ellObj G.E' ⟶ (Variety.point k).ellObj x.1 :=
    { base := 𝟙 (Spec (CommRingCat.of k))
      base_structureMap := Category.id_comp (𝟙 (Spec (CommRingCat.of k)))
      total := G.g
      isPullback := G.hg
      zero_total := G.h0 }
  let α : (ModuliProblem.gammaOne (B k) N).obj (op ((Variety.point k).ellObj G.E')) :=
    (ModuliProblem.gammaOneEquiv ((Variety.point k).ellObj G.E')).symm ⟨G.P, G.hP⟩
  have key : (ModuliProblem.gammaZero (B k) N).map f.op x.2 =
      (ModuliProblem.gammaOneToGammaZero (B k) N).app _ α := by
    apply (ModuliProblem.gammaZeroEquiv ((Variety.point k).ellObj G.E')).injective
    apply Subtype.ext
    rw [ModuliProblem.gammaZeroEquiv_gammaOneToGammaZero_app]
    exact G.hI
  exact ⟨G.E', α, LevelPair.rel_symm ⟨f, rfl, key⟩⟩

theorem toYV_congr {V : Variety k} {f f' : V.obj.left ⟶ (Y k N).base} (h : f = f')
    (hf : f ≫ (Y k N).structureMap = V.obj.hom) (hf' : f' ≫ (Y k N).structureMap = V.obj.hom) :
    toYV f hf = toYV f' hf' := by
  subst h; rfl

theorem zPair_powStr (V : Variety k) (E : EllipticCurveGeom V.obj.left) (g : (ZMod N)ˣ)
    (α : (ModuliProblem.gammaOne (B k) N).obj (op (V.ellObj E))) :
    zPair V E (powStr hNf.out g α) = zPair V E α := by
  rw [zPair, zPair, gammaOneToGammaZero_powStr]

/-- **Pairs over $k$ with the same invariant are isomorphic.** -/
theorem rel_of_cycMor_eq {E E' : EllipticCurveGeom (Variety.point k).obj.left}
    {α : (ModuliProblem.gammaOne (B k) N).obj (op ((Variety.point k).ellObj E))}
    {α' : (ModuliProblem.gammaOne (B k) N).obj (op ((Variety.point k).ellObj E'))}
    (h : cycMor (zPair (Variety.point k) E α) = cycMor (zPair (Variety.point k) E' α')) :
    LevelPair.Rel (zPair (Variety.point k) E α) (zPair (Variety.point k) E' α') := by
  have := isAffine_Y (k := k) (N := N) hNf.out
  have h1 := congrArg (fun φ : Variety.point k ⟶ mVar k N ↦ φ.hom.left) h
  rw [cycMor_zPair_left, cycMor_zPair_left] at h1
  unfold tStr qmap at h1
  obtain ⟨g, hg⟩ := exists_comp_specComap_eq (R k N) (ZMod N)ˣ (K := k) (x₁ := (cls hNf.out h4f.out α).base ≫ (Y k N).base.toSpecΓ)
    (x₂ := (cls hNf.out h4f.out α').base ≫ (Y k N).base.toSpecΓ) (by
      have h1' := h1
      rw [← Category.assoc, ← Category.assoc] at h1'
      exact h1')
  rw [specComap_eq] at hg
  have hg' : ((cls hNf.out h4f.out α).base ≫ (sigma hNf.out h4f.out g).base) ≫ (Y k N).base.toSpecΓ =
      (cls hNf.out h4f.out α').base ≫ (Y k N).base.toSpecΓ := by
    rw [Category.assoc, Scheme.toSpecΓ_naturality, ← Category.assoc]
    exact hg
  have hb : (cls hNf.out h4f.out (powStr hNf.out g α)).base = (cls hNf.out h4f.out α').base := by
    rw [cls_powStr, EllObj.comp_base]
    exact (cancel_mono _).mp hg'
  have r1 := rel_pull_xu E (powStr hNf.out g α)
  have r2 := rel_pull_xu E' α'
  rw [zPair_powStr] at r1
  rw [toYV_congr hb _ (cls hNf.out h4f.out α').base_structureMap] at r1
  exact LevelPair.rel_trans r1 (LevelPair.rel_symm r2)

theorem projection_specStructure :
    projection (R k N) (ZMod N)ˣ ≫ specStructure k (RG k N) = specStructure k (R k N) := by
  rw [projection_def, specStructure, Spec.algebraMap, ← Spec.map_comp]
  rfl

theorem isoSpec_inv_structureMap :
    (Y k N).base.isoSpec.inv ≫ (Y k N).structureMap = specStructure k (R k N) := by
  have := isAffine_Y (k := k) (N := N) hNf.out
  rw [← toSpecΓ_specMap_gammaAlgHom (Y k N).structureMap, ← Scheme.isoSpec_hom, Iso.inv_hom_id_assoc]

/-- **Every $k$-point of $M$ lifts to $Y_1(N)$.** -/
theorem exists_point_lift (m : Variety.point k ⟶ mVar k N) :
    ∃ t : Variety.point k ⟶ yV k N, t.hom.left ≫ qmap = m.hom.left := by
  have := isAffine_Y (k := k) (N := N) hNf.out
  have hlft : LocallyOfFiniteType (specStructure k (RG k N)) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hlftR : LocallyOfFiniteType (specStructure k (R k N)) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hm : m.hom.left ≫ specStructure k (RG k N) = 𝟙 _ := Over.w m.hom
  set z := m.hom.left (IsLocalRing.closedPoint k)
  have hz : IsClosed {z} := (pointEquivClosedPoint (specStructure k (RG k N)) ⟨m.hom.left, hm⟩).2
  obtain ⟨x, hx⟩ := (inferInstance : Surjective (projection (R k N) (ZMod N)ˣ)).surj z
  have hzmax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal z).mp hz
  have hxmax : x.asIdeal.IsMaximal := by
    have := x.isPrime
    have : Algebra.IsIntegral (RG k N) (R k N) := Algebra.IsInvariant.isIntegral _ _ (ZMod N)ˣ
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := RG k N) x.asIdeal ?_
    have hcomap : z.asIdeal = x.asIdeal.comap (algebraMap (RG k N) (R k N)) := by
      rw [← hx]
      exact congrArg PrimeSpectrum.asIdeal (projection_base_apply (R k N) (ZMod N)ˣ x)
    rw [hcomap] at hzmax
    exact hzmax
  have hxc : IsClosed {x} := (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mpr hxmax
  let σ := pointOfClosedPoint (specStructure k (R k N)) x hxc
  have hσ : σ ≫ specStructure k (R k N) = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  have e : σ ≫ (Y k N).base.isoSpec.inv ≫ (Y k N).structureMap = 𝟙 _ := by
    rw [isoSpec_inv_structureMap, hσ]
  refine ⟨toYV (V := Variety.point k) (σ ≫ (Y k N).base.isoSpec.inv) ((Category.assoc _ _ _).trans e), ?_⟩
  change (σ ≫ (Y k N).base.isoSpec.inv) ≫ (Y k N).base.toSpecΓ ≫ projection (R k N) (ZMod N)ˣ = _
  rw [← Scheme.isoSpec_hom, Category.assoc, Iso.inv_hom_id_assoc]
  refine ext_of_apply_closedPoint_eq (specStructure k (RG k N)) ?_ hm ?_
  · rw [Category.assoc, projection_specStructure, hσ]
  · change (projection (R k N) (ZMod N)ˣ) (σ (IsLocalRing.closedPoint k)) = z
    rw [show σ (IsLocalRing.closedPoint k) = x from pointOfClosedPoint_apply _ _ _ _, hx]

theorem alpha_bijective : Function.Bijective (alpha (k := k) (N := N)) := by
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h x =>
    induction b using Quotient.inductionOn with
    | h y =>
    obtain ⟨E, α, r1⟩ := exists_rel_zPair x
    obtain ⟨E', α', r2⟩ := exists_rel_zPair y
    have e : cycMor (zPair (Variety.point k) E α) = cycMor (zPair (Variety.point k) E' α') :=
      (cycMor_rel r1).symm.trans (hab.trans (cycMor_rel r2))
    exact Quotient.sound (LevelPair.rel_trans r1 (LevelPair.rel_trans (rel_of_cycMor_eq e)
      (LevelPair.rel_symm r2)))
  · intro m
    obtain ⟨t, ht⟩ := exists_point_lift m
    refine ⟨⟦LevelPair.pull t (xu k N)⟧, ?_⟩
    change cycMor _ = m
    rw [cycMor_pull]
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    change t.hom.left ≫ (cycMor (xu k N)).hom.left = m.hom.left
    rw [cycMor_xu]
    exact ht

end ModularFormsKB.Milne.YOneModuli
