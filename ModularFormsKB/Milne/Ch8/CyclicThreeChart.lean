import ModularFormsKB.Milne.Ch8.CyclicThreeInvariant
import ModularFormsKB.Milne.Ch8.CyclicTwoChart
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.MulBy.ThreeTorsion
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Coprimality

/-!
# The invariant map of an elliptic curve with a point of order three, over a scheme

Let $E$ be an elliptic curve over a scheme $S$ over $\operatorname{Spec} k$, and let $P$ be a point with $P^3 = 1$
missing the zero section. On every pointed Weierstrass chart $c$ of $E$, $P$ is an affine point $(x_0, y_0)$ with
$\Psi_3(x_0) = 0$ (`psi3_x₀`, through Tau Ceti's `projModelAffinePoint_projModelMulBy_three_eq_projModelZero_iff`),
$C = (2y_0 + a_1x_0 + a_3)^2$ is a unit (Tau Ceti's `isUnit_evalEval_ψ₂_of_eval_Ψ₃_eq_zero`), and the invariant
$t_c = AB/C$ of `CyclicThreeInvariant` is defined (`chartInv`), with $t_c - 27$ a unit. As for points of order two
(`CyclicTwoChart`), it is compatible along cartesian morphisms carrying the points to each other, and the chart values
glue to the **invariant map** $S \to \operatorname{Spec} k[t, (t - 27)^{-1}]$ (`tMap`), over $\operatorname{Spec} k$
(`tMap_specStructure`), natural (`tMap_comp`), with the expected value on a Weierstrass family (`tMap_weierstrass`).
No hypothesis on the characteristic is needed here.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve TauCeti.AlgebraicGeometry MonoidalCategory
  ModularFormsKB.Milne.LevelTwoLambda ModularFormsKB.Milne.LevelTwoChart MonObj

noncomputable section

namespace ModularFormsKB.Milne.CyclicThree

open CyclicTwo

variable (k : Type u) [Field k]

/-- The coordinate ring $k[t, (t - 27)^{-1}]$ of $\mathbb A^1 \smallsetminus \{27\}$. -/
abbrev TRing : Type u := Localization.Away (Polynomial.X - Polynomial.C 27 : Polynomial k)

variable {k}

/-- The ring map $k[t, (t - 27)^{-1}] \to R$, $t \mapsto l$, for $l - 27$ a unit. -/
def tLift {R : Type u} [CommRing R] (f : k →+* R) (l : R) (hl : IsUnit (l - 27)) : TRing k →+* R :=
  IsLocalization.Away.lift (Polynomial.X - Polynomial.C 27 : Polynomial k)
    (g := Polynomial.eval₂RingHom f l) (by
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, map_ofNat]
      exact hl)

theorem tLift_algebraMap {R : Type u} [CommRing R] (f : k →+* R) (l : R) (hl : IsUnit (l - 27))
    (q : Polynomial k) : tLift f l hl (algebraMap (Polynomial k) (TRing k) q) = Polynomial.eval₂ f l q :=
  IsLocalization.Away.lift_eq _ _ q

theorem tLift_ext {R : Type u} [CommRing R] {ρ ρ' : TRing k →+* R}
    (hC : ∀ a : k, ρ (algebraMap k _ a) = ρ' (algebraMap k _ a))
    (hX : ρ (algebraMap (Polynomial k) _ Polynomial.X) = ρ' (algebraMap (Polynomial k) _ Polynomial.X)) :
    ρ = ρ' := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X - Polynomial.C 27 : Polynomial k))
  apply Polynomial.ringHom_ext
  · intro a
    have := hC a
    rwa [IsScalarTower.algebraMap_apply k (Polynomial k) (TRing k)] at this
  · exact hX

theorem tLift_algebraMap_k {R : Type u} [CommRing R] (f : k →+* R) (l : R) (hl : IsUnit (l - 27)) :
    (tLift f l hl).comp (algebraMap k (TRing k)) = f := by
  ext a
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k (Polynomial k) (TRing k), tLift_algebraMap,
    Polynomial.algebraMap_eq, Polynomial.eval₂_C]

theorem inv3_congr {R : Type u} [CommRing R] {W W' : WeierstrassCurve R} (hW : W = W') {x x' : R} (hx : x = x')
    (hC : IsUnit (coeffC W x)) (hC' : IsUnit (coeffC W' x')) : inv3 W hC = inv3 W' hC' := by
  subst hW hx; rfl

/-! ### Points of order three in Weierstrass coordinates -/

section Affine

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} [W.IsElliptic] {x y : R}
  (h : W.toAffine.Equation x y)

include h in
theorem psi3_of_mulBy (h3 : W.projModelAffinePoint h ≫ W.projModelMulBy 3 = W.projModelZero) :
    psi3 W x = 0 := by
  rw [psi3_eq]
  exact (projModelAffinePoint_projModelMulBy_three_eq_projModelZero_iff h).mp h3

include h in
theorem isUnit_coeffC_of_psi3 (h3 : psi3 W x = 0) : IsUnit (coeffC W x) := by
  rw [coeffC_eq h]
  have hu := isUnit_evalEval_ψ₂_of_eval_Ψ₃_eq_zero h (by rw [← psi3_eq]; exact h3)
  rw [ψ₂, Affine.evalEval_polynomialY] at hu
  exact hu.pow 2

end Affine

/-! ### The point on a chart -/

section Chart

variable {S : Scheme.{u}} {E : EllipticCurveGeom S} {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
  (hP3 : P ^ 3 = 1) (hP0 : ∀ s, P.left s ≠ E.zero s) (c : PointedWeierstrassChart E.structureMap E.zero)

include hP3 in
/-- On every chart, the model point of `P` is killed by multiplication by three. -/
theorem modelPoint_projModelMulBy_three :
    c.modelPoint (hPs P) ≫ c.equation.projModelMulBy 3 = c.equation.projModelZero := by
  have hn : P.left ≫ (E.mulBy 3).left = E.zero :=
    (EllipticCurveGeom.zpow_eq_one_iff_left_comp_mulBy_left E P 3).mp (by exact_mod_cast hP3)
  exact c.isPullback_modelIso_inv_toTotal.hom_ext
    (by rw [Category.assoc, c.equation.projModelMulBy_comp_of_isPullback
      c.isPullback_modelIso_inv_toTotal c.projModelZero_modelIso_inv_toTotal, ← Category.assoc,
      c.modelPoint_modelIso_inv_toTotal, Category.assoc, hn,
      c.projModelZero_modelIso_inv_toTotal])
    (by
      rw [Category.assoc, projModelMulBy_projModelOver, c.modelPoint_projModelOver,
        projModelZero_projModelOver]
      rfl)

include hP3 in
theorem psi3_x₀ : psi3 c.equation (x₀ hP0 c) = 0 := by
  refine psi3_of_mulBy (coords₀_equation hP0 c) ?_
  rw [← modelPoint_coords₀]
  exact modelPoint_projModelMulBy_three hP3 c

include hP3 in
theorem isUnit_coeffC_chart : IsUnit (coeffC c.equation (x₀ hP0 c)) :=
  isUnit_coeffC_of_psi3 (coords₀_equation hP0 c) (psi3_x₀ hP3 hP0 c)

end Chart

/-! ### The invariant map, glued along the charts -/

section Glue

variable {S : Scheme.{u}} (p : S ⟶ Spec (CommRingCat.of k))
  {E : EllipticCurveGeom S} {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
  (hP3 : P ^ 3 = 1) (hP0 : ∀ s, P.left s ≠ E.zero s)

include hP3 in
/-- **The invariant of a chart.** -/
def chartInv (c : PointedWeierstrassChart E.structureMap E.zero) : c.ring :=
  inv3 c.equation (isUnit_coeffC_chart hP3 hP0 c)

include hP3 hP0 in
theorem isUnit_chartInv_sub (c : PointedWeierstrassChart E.structureMap E.zero) :
    IsUnit (chartInv hP3 hP0 c - 27) :=
  isUnit_inv3_sub _ (psi3_x₀ hP3 hP0 c) c.equation.isUnit_Δ

include p hP3 hP0 in
/-- **The chart ring map** $k[t, (t - 27)^{-1}] \to \Gamma(\text{base of } c)$, $t \mapsto t_c$. -/
def chartRhoT (c : PointedWeierstrassChart E.structureMap E.zero) : TRing k →+* c.ring :=
  tLift (chartAlg p c).hom (chartInv hP3 hP0 c) (isUnit_chartInv_sub hP3 hP0 c)

end Glue

/-! ### Transport along cartesian morphisms -/

section Over

variable {S S' : Scheme.{u}} (p : S ⟶ Spec (CommRingCat.of k)) (p' : S' ⟶ Spec (CommRingCat.of k))
  {E : EllipticCurveGeom S} {E' : EllipticCurveGeom S'}
  {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {P' : 𝟙_ (Over S') ⟶ Over.mk E'.structureMap}
  (hP3 : P ^ 3 = 1) (hP0 : ∀ s, P.left s ≠ E.zero s) (hP3' : P' ^ 3 = 1) (hP0' : ∀ s, P'.left s ≠ E'.zero s)
  {g : E'.carrier ⟶ E.carrier} {b : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap b)
  {c : PointedWeierstrassChart E.structureMap E.zero} {c' : PointedWeierstrassChart E'.structureMap E'.zero}
  {h : c'.base ⟶ c.base} (hh : h ≫ c.baseMap = c'.baseMap ≫ b)
  (h0 : E'.zero ≫ g = b ≫ E.zero) (hpt : P'.left ≫ g = b ≫ P.left) (hp : b ≫ p = p')

include hg hh h0 hpt in
theorem chartInv_over :
    chartInv hP3' hP0' c' = (ringMapOver h).hom (chartInv hP3 hP0 c) := by
  set ψ := (ringMapOver h).hom
  have hF := isPullback_modelMapOver hg hh
  have hF0 := projModelZero_modelMapOver hg hh h0
  rw [← CommRingCat.ofHom_hom (ringMapOver h)] at hF hF0
  obtain ⟨C, hC, hx⟩ := exists_variableChange_of_isPullback c.equation c'.equation ψ _ hF hF0
  have he : ψ (x₀ hP0 c) = (C.u : c'.ring) ^ 2 * x₀ hP0' c' + C.r := by
    refine hx (coords₀_equation hP0 c) (coords₀_equation hP0' c') ?_
    rw [← modelPoint_coords₀, ← modelPoint_coords₀, CommRingCat.ofHom_hom]
    exact modelPoint_modelMapOver hg hh _ _ hpt
  have hB1 : IsUnit (coeffC (C • c.equation.map ψ) (x₀ hP0' c')) := by
    rw [hC]; exact isUnit_coeffC_chart hP3' hP0' c'
  have hB3 : IsUnit (coeffC (c.equation.map ψ) (ψ (x₀ hP0 c))) := by
    convert (isUnit_coeffC_chart hP3 hP0 c).map ψ using 1
    simp only [coeffC, map_b₂, map_b₄, map_b₆, map_mul, map_add, map_pow, map_ofNat]
  have hB2 : IsUnit (coeffC (c.equation.map ψ) ((C.u : c'.ring) ^ 2 * x₀ hP0' c' + C.r)) := by
    rwa [← he]
  calc chartInv hP3' hP0' c' = inv3 (C • c.equation.map ψ) hB1 := inv3_congr hC.symm rfl _ _
    _ = inv3 (c.equation.map ψ) hB2 := inv3_variableChange C hB1 hB2
    _ = inv3 (c.equation.map ψ) hB3 := inv3_congr rfl he.symm _ _
    _ = ψ (chartInv hP3 hP0 c) := inv3_map ψ _ hB3

include hg hh h0 hpt hp in
theorem chartRhoT_over :
    (ringMapOver h).hom.comp (chartRhoT p hP3 hP0 c) = chartRhoT p' hP3' hP0' c' := by
  apply tLift_ext
  · intro a
    rw [RingHom.comp_apply, ← RingHom.comp_apply (chartRhoT p hP3 hP0 c), chartRhoT, tLift_algebraMap_k,
      ← RingHom.comp_apply (chartRhoT p' hP3' hP0' c'), chartRhoT, tLift_algebraMap_k,
      ← chartAlg_ringMapOver p p' hh hp]
    rfl
  · simp only [RingHom.comp_apply, chartRhoT, tLift_algebraMap, Polynomial.eval₂_X]
    exact (chartInv_over hP3 hP0 hP3' hP0' hg hh h0 hpt).symm

include hg hh h0 hpt hp in
theorem spec_chartRhoT_over :
    c'.baseIso.hom ≫ Spec.map (CommRingCat.ofHom (chartRhoT p' hP3' hP0' c')) =
      h ≫ c.baseIso.hom ≫ Spec.map (CommRingCat.ofHom (chartRhoT p hP3 hP0 c)) := by
  rw [← chartRhoT_over p p' hP3 hP0 hP3' hP0' hg hh h0 hpt hp, CommRingCat.ofHom_comp, Spec.map_comp,
    CommRingCat.ofHom_hom, spec_ringMapOver]
  simp

end Over

/-! ### Gluing and naturality -/

section Map

variable {S : Scheme.{u}} (p : S ⟶ Spec (CommRingCat.of k))
  {E : EllipticCurveGeom S} {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
  (hP3 : P ^ 3 = 1) (hP0 : ∀ s, P.left s ≠ E.zero s)

/-- The invariant map on the part of $S$ over the base of a chart. -/
def pieceT (c : PointedWeierstrassChart E.structureMap E.zero) :
    pullback (𝟙 S) c.baseMap ⟶ Spec (CommRingCat.of (TRing k)) :=
  pullback.snd (𝟙 S) c.baseMap ≫ c.baseIso.hom ≫ Spec.map (CommRingCat.ofHom (chartRhoT p hP3 hP0 c))

theorem map_pieceT {c k' : PointedWeierstrassChart E.structureMap E.zero} {h : k'.base ⟶ c.base}
    (hh : h ≫ c.baseMap = k'.baseMap) :
    pullback.map (𝟙 S) k'.baseMap (𝟙 S) c.baseMap (𝟙 _) h (𝟙 _) (by simp) (by simp [hh]) ≫
      pieceT p hP3 hP0 c = pieceT p hP3 hP0 k' := by
  rw [pieceT, pieceT, pullback.lift_snd_assoc, Category.assoc,
    ← spec_chartRhoT_over p p hP3 hP0 hP3 hP0 (isPullback_id E) (c := c) (c' := k') (h := h)
      (by rw [hh, Category.comp_id]) (by simp) (by simp) (Category.id_comp _)]

/-- **The invariant map** $S \to \mathbb A^1 \smallsetminus \{27\}$ of a curve with a point of order three. -/
def tMap : S ⟶ Spec (CommRingCat.of (TRing k)) :=
  EllipticCurveGeom.glueMorphisms (q := 𝟙 S) (pieceT p hP3 hP0) (map_pieceT p hP3 hP0)

theorem baseMap_tMap (c : PointedWeierstrassChart E.structureMap E.zero) :
    c.baseMap ≫ tMap p hP3 hP0 =
      c.baseIso.hom ≫ Spec.map (CommRingCat.ofHom (chartRhoT p hP3 hP0 c)) := by
  have := pullback.lift c.baseMap (𝟙 c.base) (by simp) ≫=
    EllipticCurveGeom.fst_glueMorphisms (q := 𝟙 S) (pieceT p hP3 hP0) (map_pieceT p hP3 hP0) c
  simpa [tMap, pieceT, -EllipticCurveGeom.fst_glueMorphisms, -EllipticCurveGeom.fst_glueMorphisms_assoc] using this

theorem tMap_specStructure : tMap p hP3 hP0 ≫ specStructure k (TRing k) = p := by
  obtain ⟨A⟩ := E.localModel
  refine A.hom_ext (𝟙 S) _ _ fun i ↦ ?_
  have hc : pullback.fst (𝟙 S) (A.chart i).baseMap = pullback.snd _ _ ≫ (A.chart i).baseMap := by
    simpa using pullback.condition (f := 𝟙 S) (g := (A.chart i).baseMap)
  rw [hc, Category.assoc, Category.assoc, reassoc_of% baseMap_tMap p hP3 hP0 (A.chart i)]
  congr 1
  rw [specStructure, ← Spec.map_comp, ← CommRingCat.ofHom_comp, chartRhoT, tLift_algebraMap_k,
    CommRingCat.ofHom_hom, spec_chartAlg, Iso.hom_inv_id_assoc]

end Map

section Naturality

variable {S S' : Scheme.{u}} (p : S ⟶ Spec (CommRingCat.of k)) (p' : S' ⟶ Spec (CommRingCat.of k))
  {E : EllipticCurveGeom S} {E' : EllipticCurveGeom S'}
  {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {P' : 𝟙_ (Over S') ⟶ Over.mk E'.structureMap}
  (hP3 : P ^ 3 = 1) (hP0 : ∀ s, P.left s ≠ E.zero s) (hP3' : P' ^ 3 = 1) (hP0' : ∀ s, P'.left s ≠ E'.zero s)
  {g : E'.carrier ⟶ E.carrier} {b : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap b)
  (h0 : E'.zero ≫ g = b ≫ E.zero) (hpt : P'.left ≫ g = b ≫ P.left) (hp : b ≫ p = p')

include hg h0 hpt hp in
/-- **Naturality of the invariant map.** -/
theorem tMap_comp : tMap p' hP3' hP0' = b ≫ tMap p hP3 hP0 := by
  obtain ⟨A'⟩ := E'.localModel
  obtain ⟨A⟩ := E.localModel
  refine A'.hom_ext (𝟙 S') _ _ fun i ↦ ?_
  set c' := A'.chart i
  have hc : pullback.fst (𝟙 S') c'.baseMap = pullback.snd _ _ ≫ c'.baseMap := by
    simpa using pullback.condition (f := 𝟙 S') (g := c'.baseMap)
  rw [hc, Category.assoc, Category.assoc]
  congr 1
  rw [baseMap_tMap]
  refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
  obtain ⟨j, y, hy⟩ := A.covers (b (c'.baseMap x))
  have hx : x ∈ (c'.baseMap ≫ b) ⁻¹ᵁ (A.chart j).baseMap.opensRange :=
    ⟨y, by rw [Scheme.Hom.comp_apply]; exact hy⟩
  set c := A.chart j
  obtain ⟨V, hV, hxV, hVc⟩ := exists_isAffineOpen_mem_and_subset hx
  let V' : c'.base.affineOpens := ⟨V, hV⟩
  set c'' := c'.restrict V'
  have hrange : Set.range (c''.baseMap ≫ b) ⊆ Set.range c.baseMap := by
    rintro _ ⟨z, rfl⟩
    rw [← PointedWeierstrassChart.restrictι_baseMap, Category.assoc, Scheme.Hom.comp_apply]
    exact hVc ((c'.range_restrictι V').subset ⟨z, rfl⟩)
  let h : c''.base ⟶ c.base := IsOpenImmersion.lift c.baseMap (c''.baseMap ≫ b) hrange
  have hh : h ≫ c.baseMap = c''.baseMap ≫ b := IsOpenImmersion.lift_fac _ _ _
  have hU : Set.range V.ι ⊆ Set.range (c'.restrictι V') := by
    rw [PointedWeierstrassChart.range_restrictι, Scheme.Opens.range_ι]
  let ℓ : (V : Scheme) ⟶ c''.base := IsOpenImmersion.lift (c'.restrictι V') V.ι hU
  have hℓ : ℓ ≫ c'.restrictι V' = V.ι := IsOpenImmersion.lift_fac _ _ _
  refine ⟨V, hxV, ?_⟩
  rw [← hℓ, Category.assoc, Category.assoc]
  congr 1
  have e1 := spec_chartRhoT_over p' p' hP3' hP0' hP3' hP0' (isPullback_id E')
    (by rw [PointedWeierstrassChart.restrictι_baseMap, Category.comp_id]) (by simp) (by simp)
    (Category.id_comp _) (c := c') (c' := c'') (h := c'.restrictι V')
  have e2 := spec_chartRhoT_over p p' hP3 hP0 hP3' hP0' hg hh h0 hpt hp
  rw [← e1, e2, ← Category.assoc, ← Category.assoc, PointedWeierstrassChart.restrictι_baseMap]
  change _ = c''.baseMap ≫ b ≫ tMap p hP3 hP0
  rw [← Category.assoc c''.baseMap, ← hh, Category.assoc h c.baseMap, baseMap_tMap, Category.assoc]

end Naturality

/-! ### The invariant map of a Weierstrass family -/

section Weierstrass

variable {R : Type u} [CommRing R] [Algebra k R] (W : WeierstrassCurve R) [W.IsElliptic]
  {x y : R} (h : W.toAffine.Equation x y) (h3 : psi3 W x = 0)

include h3 in
theorem isUnit_inv_weierstrass_sub : IsUnit (inv3 W (isUnit_coeffC_of_psi3 h h3) - 27) :=
  isUnit_inv3_sub _ h3 W.isUnit_Δ

variable (hP3 : Ch8Counterexample.affinePointHom W h ^ 3 = 1)
  (hP0 : ∀ s, (Ch8Counterexample.affinePointHom W h).left s ≠ W.toEllipticCurveGeom.zero s)

/-- **The invariant map of a Weierstrass family with a point of order three** is $\operatorname{Spec}$ of
$t \mapsto t(W; x_0)$. -/
theorem tMap_weierstrass :
    tMap (specStructure k R) hP3 hP0 = Spec.map (CommRingCat.ofHom
      (tLift (algebraMap k R) (inv3 W (isUnit_coeffC_of_psi3 h h3)) (isUnit_inv_weierstrass_sub W h h3))) := by
  obtain ⟨A⟩ := W.toEllipticCurveGeom.localModel
  refine A.hom_ext (𝟙 _) _ _ fun i ↦ ?_
  set c := A.chart i
  have hc : pullback.fst (𝟙 _) c.baseMap = pullback.snd _ _ ≫ c.baseMap := by
    simpa using pullback.condition (f := 𝟙 (Spec (.of R))) (g := c.baseMap)
  rw [hc, Category.assoc, Category.assoc]
  congr 1
  rw [baseMap_tMap]
  set ψ : CommRingCat.of R ⟶ c.ring := Spec.preimage (c.baseIso.inv ≫ c.baseMap) with hψdef
  have hψ : Spec.map ψ = c.baseIso.inv ≫ c.baseMap := Spec.map_preimage _
  set F : c.equation.projModel ⟶ W.projModel :=
    c.modelIso.inv ≫ c.toTotal ≫ (toEllipticCurveGeomIso W).hom
  have hF : IsPullback F c.equation.projModelOver W.projModelOver (Spec.map (CommRingCat.ofHom ψ.hom)) := by
    rw [CommRingCat.ofHom_hom, hψ]
    refine (c.isPullback_modelIso_inv_toTotal).of_iso (.refl _) (toEllipticCurveGeomIso W) (.refl _) (.refl _)
      (by simp [F]) (by simp) (by simp [toEllipticCurveGeomIso_hom_projModelOver]) (by simp)
  have hpt' (Q : Spec (.of R) ⟶ W.toEllipticCurveGeom.carrier)
      (hQ : Q ≫ W.toEllipticCurveGeom.structureMap = 𝟙 _) :
      c.modelPoint hQ ≫ F = Spec.map (CommRingCat.ofHom ψ.hom) ≫ Q ≫ (toEllipticCurveGeomIso W).hom := by
    rw [CommRingCat.ofHom_hom, hψ]
    simp [F, PointedWeierstrassChart.modelPoint_modelIso_inv_toTotal_assoc]
  have hF0 : c.equation.projModelZero ≫ F = Spec.map (CommRingCat.ofHom ψ.hom) ≫ W.projModelZero := by
    have := hpt' _ W.toEllipticCurveGeom.zero_comp
    rwa [PointedWeierstrassChart.modelPoint_zero, zero_toEllipticCurveGeomIso_hom] at this
  obtain ⟨C, hC, hxf⟩ := exists_variableChange_of_isPullback W c.equation ψ.hom F hF hF0
  have he : ψ.hom x = (C.u : c.ring) ^ 2 * x₀ hP0 c + C.r := by
    refine hxf h (coords₀_equation hP0 c) ?_
    rw [← modelPoint_coords₀, hpt', Ch8Counterexample.affinePointHom_left, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hinv : chartInv hP3 hP0 c = ψ.hom (inv3 W (isUnit_coeffC_of_psi3 h h3)) := by
    have hB1 : IsUnit (coeffC (C • W.map ψ.hom) (x₀ hP0 c)) := by
      rw [hC]; exact isUnit_coeffC_chart hP3 hP0 c
    have hB3 : IsUnit (coeffC (W.map ψ.hom) (ψ.hom x)) := by
      convert (isUnit_coeffC_of_psi3 h h3).map ψ.hom using 1
      simp only [coeffC, map_b₂, map_b₄, map_b₆, map_mul, map_add, map_pow, map_ofNat]
    have hB2 : IsUnit (coeffC (W.map ψ.hom) ((C.u : c.ring) ^ 2 * x₀ hP0 c + C.r)) := by
      rwa [← he]
    calc chartInv hP3 hP0 c = inv3 (C • W.map ψ.hom) hB1 := inv3_congr hC.symm rfl _ _
      _ = inv3 (W.map ψ.hom) hB2 := inv3_variableChange C hB1 hB2
      _ = inv3 (W.map ψ.hom) hB3 := inv3_congr rfl he.symm _ _
      _ = ψ.hom (inv3 W _) := inv3_map ψ.hom _ hB3
  have hρ : chartRhoT (specStructure k R) hP3 hP0 c =
      ψ.hom.comp (tLift (algebraMap k R) (inv3 W (isUnit_coeffC_of_psi3 h h3))
        (isUnit_inv_weierstrass_sub W h h3)) := by
    apply tLift_ext
    · intro a
      rw [← RingHom.comp_apply (chartRhoT _ hP3 hP0 c), chartRhoT, tLift_algebraMap_k, RingHom.comp_apply,
        ← RingHom.comp_apply (tLift _ _ _), tLift_algebraMap_k]
      have : chartAlg (specStructure k R) c = CommRingCat.ofHom (algebraMap k R) ≫ ψ := by
        apply Spec.map_injective
        rw [spec_chartAlg, Spec.map_comp, hψ]
        simp [specStructure]
      rw [this]
      rfl
    · rw [chartRhoT, tLift_algebraMap, RingHom.comp_apply, tLift_algebraMap, Polynomial.eval₂_X,
        Polynomial.eval₂_X]
      exact hinv
  rw [hρ, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, hψ]
  simp

end Weierstrass

end ModularFormsKB.Milne.CyclicThree
