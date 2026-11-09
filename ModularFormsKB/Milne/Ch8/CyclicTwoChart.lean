import ModularFormsKB.Milne.Ch8.CyclicTwoInvariant
import ModularFormsKB.Milne.Ch8.CyclicTwoGenerator
import ModularFormsKB.Milne.Ch8.LevelTwoMap

/-!
# The invariant map of an elliptic curve with a point of order two, over a scheme

Let $E$ be an elliptic curve over a scheme $S$ over $\operatorname{Spec} k$, $2 \ne 0$ in $k$, and let $P$ be a point
with $P^2 = 1$ missing the zero section. On every pointed Weierstrass chart $c$ of $E$, $P$ is an affine point
$(x_0, y_0)$ of order two, and the invariant $t_c = A^2/(8B)$ of `CyclicTwoInvariant` is defined (`chartInv`), with
$t_c - 4$ a unit. It is compatible along cartesian morphisms of elliptic curves carrying the points to each other
(`chartInv_eq_of_hom`, through `LevelTwoChart.exists_variableChange_of_isPullback`), and the chart values glue to the
**invariant map** $S \to \operatorname{Spec} k[t, (t - 4)^{-1}]$ (`tMap`), over $\operatorname{Spec} k$
(`tMap_specStructure`), natural (`tMap_comp`).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve TauCeti.AlgebraicGeometry MonoidalCategory
  ModularFormsKB.Milne.LevelTwoLambda ModularFormsKB.Milne.LevelTwoChart MonObj

noncomputable section

namespace ModularFormsKB.Milne.CyclicTwo

variable (k : Type u) [Field k]

/-- The coordinate ring $k[t, (t - 4)^{-1}]$ of $\mathbb A^1 \smallsetminus \{4\}$. -/
abbrev TRing : Type u := Localization.Away (Polynomial.X - Polynomial.C 4 : Polynomial k)

variable {k}

/-- The ring map $k[t, (t - 4)^{-1}] \to R$, $t \mapsto l$, for $l - 4$ a unit. -/
def tLift {R : Type u} [CommRing R] (f : k →+* R) (l : R) (hl : IsUnit (l - 4)) : TRing k →+* R :=
  IsLocalization.Away.lift (Polynomial.X - Polynomial.C 4 : Polynomial k)
    (g := Polynomial.eval₂RingHom f l) (by
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, map_ofNat]
      exact hl)

theorem tLift_algebraMap {R : Type u} [CommRing R] (f : k →+* R) (l : R) (hl : IsUnit (l - 4)) (q : Polynomial k) :
    tLift f l hl (algebraMap (Polynomial k) (TRing k) q) = Polynomial.eval₂ f l q :=
  IsLocalization.Away.lift_eq _ _ q

theorem tLift_ext {R : Type u} [CommRing R] {ρ ρ' : TRing k →+* R}
    (hC : ∀ a : k, ρ (algebraMap k _ a) = ρ' (algebraMap k _ a))
    (hX : ρ (algebraMap (Polynomial k) _ Polynomial.X) = ρ' (algebraMap (Polynomial k) _ Polynomial.X)) :
    ρ = ρ' := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X - Polynomial.C 4 : Polynomial k))
  apply Polynomial.ringHom_ext
  · intro a
    have := hC a
    rwa [IsScalarTower.algebraMap_apply k (Polynomial k) (TRing k)] at this
  · exact hX

theorem tLift_algebraMap_k {R : Type u} [CommRing R] (f : k →+* R) (l : R) (hl : IsUnit (l - 4)) :
    (tLift f l hl).comp (algebraMap k (TRing k)) = f := by
  ext a
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k (Polynomial k) (TRing k), tLift_algebraMap,
    Polynomial.algebraMap_eq, Polynomial.eval₂_C]

theorem inv_congr {R : Type u} [CommRing R] {W W' : WeierstrassCurve R} (hW : W = W') {x x' : R} (hx : x = x')
    (hB : IsUnit (8 * coeffB W x)) (hB' : IsUnit (8 * coeffB W' x')) : inv W hB = inv W' hB' := by
  subst hW hx; rfl

/-! ### The point on a chart -/

section Chart

variable {S : Scheme.{u}} {E : EllipticCurveGeom S} {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
  (hP2 : P ^ 2 = 1) (hP0 : ∀ s, P.left s ≠ E.zero s) (c : PointedWeierstrassChart E.structureMap E.zero)

theorem hPs (P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) : P.left ≫ E.structureMap = 𝟙 S :=
  EllipticCurveGeom.left_comp_structureMap _

include hP2 in
theorem left_neg_self : P.left ≫ E.neg = P.left := by
  have : P⁻¹ = P := inv_eq_of_mul_eq_one_right (by rw [← sq, hP2])
  rw [← EllipticCurveGeom.hom_inv_left, this]

include hP0 in
theorem exists_coords₀ :
    ∃ (x y : c.ring) (h : c.equation.toAffine.Equation x y),
      c.modelPoint (hPs P) = c.equation.projModelAffinePoint h :=
  c.equation.exists_eq_projModelAffinePoint (c.modelPoint_projModelOver (hPs P)) (c.modelPoint_apply_ne (hPs P) hP0)

/-- The $x$-coordinate of `P` on a chart. -/
def x₀ : c.ring := (exists_coords₀ hP0 c).choose

theorem coords₀_equation : c.equation.toAffine.Equation (x₀ hP0 c) (exists_coords₀ hP0 c).choose_spec.choose :=
  (exists_coords₀ hP0 c).choose_spec.choose_spec.choose

theorem modelPoint_coords₀ : c.modelPoint (hPs P) = c.equation.projModelAffinePoint (coords₀_equation hP0 c) :=
  (exists_coords₀ hP0 c).choose_spec.choose_spec.choose_spec

include hP2 in
theorem cubic_x₀ :
    4 * x₀ hP0 c ^ 3 + c.equation.b₂ * x₀ hP0 c ^ 2 + 2 * c.equation.b₄ * x₀ hP0 c + c.equation.b₆ = 0 := by
  refine cubic_eq_zero (coords₀_equation hP0 c) ?_
  have h1 : c.modelPoint (hPs P) ≫ c.equation.projModelNeg = c.modelPoint (hPs P) := by
    rw [← EllipticCurveGeom.modelPoint_neg]
    congr 1
    exact left_neg_self hP2
  rw [modelPoint_coords₀ hP0 c, projModelAffinePoint_projModelNeg, projModelAffinePoint_inj] at h1
  have h2 := h1.2
  simp only [Affine.negY] at h2
  linear_combination -h2

end Chart

/-! ### The invariant map, glued along the charts -/

section Glue

variable (h2 : (2 : k) ≠ 0) {S : Scheme.{u}} (p : S ⟶ Spec (CommRingCat.of k))
  {E : EllipticCurveGeom S} {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
  (hP2 : P ^ 2 = 1) (hP0 : ∀ s, P.left s ≠ E.zero s)

include h2 p in
theorem isUnit_two_chart (c : PointedWeierstrassChart E.structureMap E.zero) : IsUnit (2 : c.ring) := by
  rw [← map_ofNat (chartAlg p c).hom 2]
  exact (IsUnit.mk0 (2 : k) h2).map _

include h2 p hP2 in
theorem isUnit_coeffB_chart (c : PointedWeierstrassChart E.structureMap E.zero) :
    IsUnit (8 * coeffB c.equation (x₀ hP0 c)) :=
  isUnit_coeffB (cubic_x₀ hP2 hP0 c) (isUnit_two_chart h2 p c) c.equation.isUnit_Δ

include h2 p hP2 in
/-- **The invariant of a chart.** -/
def chartInv (c : PointedWeierstrassChart E.structureMap E.zero) : c.ring :=
  inv c.equation (isUnit_coeffB_chart h2 p hP2 hP0 c)

include h2 p hP2 hP0 in
theorem isUnit_chartInv_sub_four (c : PointedWeierstrassChart E.structureMap E.zero) :
    IsUnit (chartInv h2 p hP2 hP0 c - 4) :=
  isUnit_inv_sub_four (cubic_x₀ hP2 hP0 c) (isUnit_two_chart h2 p c) c.equation.isUnit_Δ

include h2 p hP2 hP0 in
/-- **The chart ring map** $k[t, (t - 4)^{-1}] \to \Gamma(\text{base of } c)$, $t \mapsto t_c$. -/
def chartRhoT (c : PointedWeierstrassChart E.structureMap E.zero) : TRing k →+* c.ring :=
  tLift (chartAlg p c).hom (chartInv h2 p hP2 hP0 c) (isUnit_chartInv_sub_four h2 p hP2 hP0 c)

end Glue

/-! ### Transport along cartesian morphisms -/

section Over

variable (h2 : (2 : k) ≠ 0)
  {S S' : Scheme.{u}} (p : S ⟶ Spec (CommRingCat.of k)) (p' : S' ⟶ Spec (CommRingCat.of k))
  {E : EllipticCurveGeom S} {E' : EllipticCurveGeom S'}
  {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {P' : 𝟙_ (Over S') ⟶ Over.mk E'.structureMap}
  (hP2 : P ^ 2 = 1) (hP0 : ∀ s, P.left s ≠ E.zero s) (hP2' : P' ^ 2 = 1) (hP0' : ∀ s, P'.left s ≠ E'.zero s)
  {g : E'.carrier ⟶ E.carrier} {b : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap b)
  {c : PointedWeierstrassChart E.structureMap E.zero} {c' : PointedWeierstrassChart E'.structureMap E'.zero}
  {h : c'.base ⟶ c.base} (hh : h ≫ c.baseMap = c'.baseMap ≫ b)
  (h0 : E'.zero ≫ g = b ≫ E.zero) (hpt : P'.left ≫ g = b ≫ P.left) (hp : b ≫ p = p')

include hg hh h0 hpt hp in
theorem chartInv_over :
    chartInv h2 p' hP2' hP0' c' = (ringMapOver h).hom (chartInv h2 p hP2 hP0 c) := by
  set ψ := (ringMapOver h).hom
  have hF := isPullback_modelMapOver hg hh
  have hF0 := projModelZero_modelMapOver hg hh h0
  rw [← CommRingCat.ofHom_hom (ringMapOver h)] at hF hF0
  obtain ⟨C, hC, hx⟩ := exists_variableChange_of_isPullback c.equation c'.equation ψ _ hF hF0
  have he : ψ (x₀ hP0 c) = (C.u : c'.ring) ^ 2 * x₀ hP0' c' + C.r := by
    refine hx (coords₀_equation hP0 c) (coords₀_equation hP0' c') ?_
    rw [← modelPoint_coords₀, ← modelPoint_coords₀, CommRingCat.ofHom_hom]
    exact modelPoint_modelMapOver hg hh _ _ hpt
  have hB1 : IsUnit (8 * coeffB (C • c.equation.map ψ) (x₀ hP0' c')) := by
    rw [hC]; exact isUnit_coeffB_chart h2 p' hP2' hP0' c'
  have hB2 : IsUnit (8 * coeffB (c.equation.map ψ) ((C.u : c'.ring) ^ 2 * x₀ hP0' c' + C.r)) := by
    rw [← he]
    convert (isUnit_coeffB_chart h2 p hP2 hP0 c).map ψ using 1
    simp only [coeffB, map_b₂, map_b₄, map_mul, map_add, map_pow]
    rw [show ψ 8 = 8 from map_ofNat ψ 8, show ψ 6 = 6 from map_ofNat ψ 6]
  have hB3 : IsUnit (8 * coeffB (c.equation.map ψ) (ψ (x₀ hP0 c))) := by rwa [he]
  calc chartInv h2 p' hP2' hP0' c' = inv (C • c.equation.map ψ) hB1 := inv_congr hC.symm rfl _ _
    _ = inv (c.equation.map ψ) hB2 := inv_variableChange C hB1 hB2
    _ = inv (c.equation.map ψ) hB3 := inv_congr rfl he.symm _ _
    _ = ψ (chartInv h2 p hP2 hP0 c) := inv_map ψ _ hB3

include hg hh h0 hpt hp in
theorem chartRhoT_over :
    (ringMapOver h).hom.comp (chartRhoT h2 p hP2 hP0 c) = chartRhoT h2 p' hP2' hP0' c' := by
  apply tLift_ext
  · intro a
    rw [RingHom.comp_apply, ← RingHom.comp_apply (chartRhoT h2 p hP2 hP0 c), chartRhoT, tLift_algebraMap_k,
      ← RingHom.comp_apply (chartRhoT h2 p' hP2' hP0' c'), chartRhoT, tLift_algebraMap_k,
      ← chartAlg_ringMapOver p p' hh hp]
    rfl
  · simp only [RingHom.comp_apply, chartRhoT, tLift_algebraMap, Polynomial.eval₂_X]
    exact (chartInv_over h2 p p' hP2 hP0 hP2' hP0' hg hh h0 hpt hp).symm

include hg hh h0 hpt hp in
theorem spec_chartRhoT_over :
    c'.baseIso.hom ≫ Spec.map (CommRingCat.ofHom (chartRhoT h2 p' hP2' hP0' c')) =
      h ≫ c.baseIso.hom ≫ Spec.map (CommRingCat.ofHom (chartRhoT h2 p hP2 hP0 c)) := by
  rw [← chartRhoT_over h2 p p' hP2 hP0 hP2' hP0' hg hh h0 hpt hp, CommRingCat.ofHom_comp, Spec.map_comp,
    CommRingCat.ofHom_hom, spec_ringMapOver]
  simp

end Over

/-! ### Gluing and naturality -/

section Map

variable (h2 : (2 : k) ≠ 0) {S : Scheme.{u}} (p : S ⟶ Spec (CommRingCat.of k))
  {E : EllipticCurveGeom S} {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
  (hP2 : P ^ 2 = 1) (hP0 : ∀ s, P.left s ≠ E.zero s)

/-- The invariant map on the part of $S$ over the base of a chart. -/
def pieceT (c : PointedWeierstrassChart E.structureMap E.zero) :
    pullback (𝟙 S) c.baseMap ⟶ Spec (CommRingCat.of (TRing k)) :=
  pullback.snd (𝟙 S) c.baseMap ≫ c.baseIso.hom ≫ Spec.map (CommRingCat.ofHom (chartRhoT h2 p hP2 hP0 c))

theorem isPullback_id (E : EllipticCurveGeom S) :
    IsPullback (𝟙 E.carrier) E.structureMap E.structureMap (𝟙 S) :=
  IsPullback.of_horiz_isIso ⟨by simp⟩

theorem map_pieceT {c k' : PointedWeierstrassChart E.structureMap E.zero} {h : k'.base ⟶ c.base}
    (hh : h ≫ c.baseMap = k'.baseMap) :
    pullback.map (𝟙 S) k'.baseMap (𝟙 S) c.baseMap (𝟙 _) h (𝟙 _) (by simp) (by simp [hh]) ≫
      pieceT h2 p hP2 hP0 c = pieceT h2 p hP2 hP0 k' := by
  rw [pieceT, pieceT, pullback.lift_snd_assoc, Category.assoc,
    ← spec_chartRhoT_over h2 p p hP2 hP0 hP2 hP0 (isPullback_id E) (c := c) (c' := k') (h := h)
      (by rw [hh, Category.comp_id]) (by simp) (by simp) (Category.id_comp _)]

/-- **The invariant map** $S \to \mathbb A^1 \smallsetminus \{4\}$ of a curve with a point of order two. -/
def tMap : S ⟶ Spec (CommRingCat.of (TRing k)) :=
  EllipticCurveGeom.glueMorphisms (q := 𝟙 S) (pieceT h2 p hP2 hP0) (map_pieceT h2 p hP2 hP0)

theorem baseMap_tMap (c : PointedWeierstrassChart E.structureMap E.zero) :
    c.baseMap ≫ tMap h2 p hP2 hP0 =
      c.baseIso.hom ≫ Spec.map (CommRingCat.ofHom (chartRhoT h2 p hP2 hP0 c)) := by
  have := pullback.lift c.baseMap (𝟙 c.base) (by simp) ≫=
    EllipticCurveGeom.fst_glueMorphisms (q := 𝟙 S) (pieceT h2 p hP2 hP0) (map_pieceT h2 p hP2 hP0) c
  simpa [tMap, pieceT, -EllipticCurveGeom.fst_glueMorphisms, -EllipticCurveGeom.fst_glueMorphisms_assoc] using this

theorem tMap_specStructure : tMap h2 p hP2 hP0 ≫ specStructure k (TRing k) = p := by
  obtain ⟨A⟩ := E.localModel
  refine A.hom_ext (𝟙 S) _ _ fun i ↦ ?_
  have hc : pullback.fst (𝟙 S) (A.chart i).baseMap = pullback.snd _ _ ≫ (A.chart i).baseMap := by
    simpa using pullback.condition (f := 𝟙 S) (g := (A.chart i).baseMap)
  rw [hc, Category.assoc, Category.assoc, reassoc_of% baseMap_tMap h2 p hP2 hP0 (A.chart i)]
  congr 1
  rw [specStructure, ← Spec.map_comp, ← CommRingCat.ofHom_comp, chartRhoT, tLift_algebraMap_k,
    CommRingCat.ofHom_hom, spec_chartAlg, Iso.hom_inv_id_assoc]

end Map

section Naturality

variable (h2 : (2 : k) ≠ 0)
  {S S' : Scheme.{u}} (p : S ⟶ Spec (CommRingCat.of k)) (p' : S' ⟶ Spec (CommRingCat.of k))
  {E : EllipticCurveGeom S} {E' : EllipticCurveGeom S'}
  {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {P' : 𝟙_ (Over S') ⟶ Over.mk E'.structureMap}
  (hP2 : P ^ 2 = 1) (hP0 : ∀ s, P.left s ≠ E.zero s) (hP2' : P' ^ 2 = 1) (hP0' : ∀ s, P'.left s ≠ E'.zero s)
  {g : E'.carrier ⟶ E.carrier} {b : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap b)
  (h0 : E'.zero ≫ g = b ≫ E.zero) (hpt : P'.left ≫ g = b ≫ P.left) (hp : b ≫ p = p')

include hg h0 hpt hp in
/-- **Naturality of the invariant map.** -/
theorem tMap_comp : tMap h2 p' hP2' hP0' = b ≫ tMap h2 p hP2 hP0 := by
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
  have e1 := spec_chartRhoT_over h2 p' p' hP2' hP0' hP2' hP0' (isPullback_id E')
    (by rw [PointedWeierstrassChart.restrictι_baseMap, Category.comp_id]) (by simp) (by simp)
    (Category.id_comp _) (c := c') (c' := c'') (h := c'.restrictι V')
  have e2 := spec_chartRhoT_over h2 p p' hP2 hP0 hP2' hP0' hg hh h0 hpt hp
  rw [← e1, e2, ← Category.assoc, ← Category.assoc, PointedWeierstrassChart.restrictι_baseMap]
  change _ = c''.baseMap ≫ b ≫ tMap h2 p hP2 hP0
  rw [← Category.assoc c''.baseMap, ← hh, Category.assoc h c.baseMap, baseMap_tMap, Category.assoc]

end Naturality

/-! ### The invariant map of a Weierstrass family -/

section Weierstrass

variable (h2 : (2 : k) ≠ 0) {R : Type u} [CommRing R] [Algebra k R] (W : WeierstrassCurve R) [W.IsElliptic]
  {x y : R} (h : W.toAffine.Equation x y) (hy : 2 * y + W.a₁ * x + W.a₃ = 0)

include h2 in
theorem isUnit_two_alg : IsUnit (2 : R) := by
  rw [← map_ofNat (algebraMap k R) 2]
  exact (IsUnit.mk0 (2 : k) h2).map _

include h2 h hy in
theorem isUnit_coeffB_weierstrass : IsUnit (8 * coeffB W x) :=
  isUnit_coeffB (cubic_eq_zero h hy) (isUnit_two_alg h2) W.isUnit_Δ

include h2 h hy in
theorem isUnit_inv_weierstrass_sub_four : IsUnit (inv W (isUnit_coeffB_weierstrass h2 W h hy) - 4) :=
  isUnit_inv_sub_four (cubic_eq_zero h hy) (isUnit_two_alg h2) W.isUnit_Δ

variable (hP2 : Ch8Counterexample.affinePointHom W h ^ 2 = 1)
  (hP0 : ∀ s, (Ch8Counterexample.affinePointHom W h).left s ≠ W.toEllipticCurveGeom.zero s)

/-- **The invariant map of a Weierstrass family with a point of order two** is $\operatorname{Spec}$ of
$t \mapsto t(W; x_0)$. -/
theorem tMap_weierstrass :
    tMap h2 (specStructure k R) hP2 hP0 = Spec.map (CommRingCat.ofHom
      (tLift (algebraMap k R) (inv W (isUnit_coeffB_weierstrass h2 W h hy))
        (isUnit_inv_weierstrass_sub_four h2 W h hy))) := by
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
  -- the invariant of the chart is the image of that of `W`
  have hinv : chartInv h2 (specStructure k R) hP2 hP0 c = ψ.hom (inv W (isUnit_coeffB_weierstrass h2 W h hy)) := by
    have hB1 : IsUnit (8 * coeffB (C • W.map ψ.hom) (x₀ hP0 c)) := by
      rw [hC]; exact isUnit_coeffB_chart h2 (specStructure k R) hP2 hP0 c
    have hB2 : IsUnit (8 * coeffB (W.map ψ.hom) ((C.u : c.ring) ^ 2 * x₀ hP0 c + C.r)) := by
      rw [← he]
      convert (isUnit_coeffB_weierstrass h2 W h hy).map ψ.hom using 1
      simp only [coeffB, map_b₂, map_b₄, map_mul, map_add, map_pow]
      rw [show ψ.hom 8 = 8 from map_ofNat ψ.hom 8, show ψ.hom 6 = 6 from map_ofNat ψ.hom 6]
    have hB3 : IsUnit (8 * coeffB (W.map ψ.hom) (ψ.hom x)) := by rwa [he]
    calc chartInv h2 (specStructure k R) hP2 hP0 c = inv (C • W.map ψ.hom) hB1 := inv_congr hC.symm rfl _ _
      _ = inv (W.map ψ.hom) hB2 := inv_variableChange C hB1 hB2
      _ = inv (W.map ψ.hom) hB3 := inv_congr rfl he.symm _ _
      _ = ψ.hom (inv W _) := inv_map ψ.hom _ hB3
  have hρ : chartRhoT h2 (specStructure k R) hP2 hP0 c =
      ψ.hom.comp (tLift (algebraMap k R) (inv W (isUnit_coeffB_weierstrass h2 W h hy))
        (isUnit_inv_weierstrass_sub_four h2 W h hy)) := by
    apply tLift_ext
    · intro a
      rw [← RingHom.comp_apply (chartRhoT h2 _ hP2 hP0 c), chartRhoT, tLift_algebraMap_k, RingHom.comp_apply,
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

end ModularFormsKB.Milne.CyclicTwo
