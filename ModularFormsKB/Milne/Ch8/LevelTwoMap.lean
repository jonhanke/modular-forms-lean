import ModularFormsKB.Milne.Ch8.LevelTwoChart
import ModularFormsKB.Milne.Ch8.LegendreCounterexample

/-!
# The $\lambda$-map of a level-two family: Weierstrass families and base change

Continuing `LevelTwoChart`:

- `chartLam_eq_of_hom`: if the model of a chart maps to the projective model of a Weierstrass curve $W$ over $R$ by a
  cartesian pointed morphism over $\operatorname{Spec}\psi$ carrying the basis points to affine points $(x_j, y_j)$
  of $W$, then $\lambda_c = \psi(\lambda(W; x_1, x_2))$.
- `lamMap_weierstrass`: for the elliptic curve of a Weierstrass curve $W$ over $\operatorname{Spec} R$ whose basis
  points are the affine points $(x_j, y_j)$, the $\lambda$-map is $\operatorname{Spec}$ of
  $\lambda \mapsto \lambda(W; x_1, x_2)$.
- `lamMap_comp`: the $\lambda$-map is natural for cartesian morphisms of elliptic curves carrying the basis points to
  the basis points.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve TauCeti.AlgebraicGeometry MonoidalCategory
  ModularFormsKB.Milne.LevelTwoLambda MonObj

noncomputable section

namespace ModularFormsKB.Milne.LevelTwoChart

section General

variable {S : Scheme.{u}} {E : EllipticCurveGeom S}
  {φ : Multiplicative (ZMod 2 × ZMod 2) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}
  (hφ : E.IsFiberwiseInjective φ) (c : PointedWeierstrassChart E.structureMap E.zero)

/-- **The Legendre parameter of a chart mapping to a Weierstrass model.** -/
theorem chartLam_eq_of_hom {R : Type u} [CommRing R] (W : WeierstrassCurve R) (ψ : R →+* c.ring)
    (F : c.equation.projModel ⟶ W.projModel)
    (hF : IsPullback F c.equation.projModelOver W.projModelOver (Spec.map (CommRingCat.ofHom ψ)))
    (hF0 : c.equation.projModelZero ≫ F = Spec.map (CommRingCat.ofHom ψ) ≫ W.projModelZero)
    {x₁ y₁ x₂ y₂ : R} (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hpt₁ : c.modelPoint (hP φ e₁) ≫ F = Spec.map (CommRingCat.ofHom ψ) ≫ W.projModelAffinePoint h₁)
    (hpt₂ : c.modelPoint (hP φ e₂) ≫ F = Spec.map (CommRingCat.ofHom ψ) ≫ W.projModelAffinePoint h₂)
    {i₂ : R} (hi : 2 * i₂ = 1) {i₂' : c.ring} (hi' : 2 * i₂' = 1) (hx : IsUnit (x₂ - x₁)) :
    chartLam hφ c i₂' = ψ (lam W i₂ hx) := by
  obtain ⟨C, hC, hxf⟩ := exists_variableChange_of_isPullback W c.equation ψ F hF hF0
  exact lam_transport W c.equation ψ C hC hi hi' hx (isUnit_coords_sub hφ c)
    (hxf h₁ (coords_equation hφ c _) (by rw [← modelPoint_coords]; exact hpt₁))
    (hxf h₂ (coords_equation hφ c _) (by rw [← modelPoint_coords]; exact hpt₂))

end General

section Maps

variable {k : Type u} [Field k] (h2 : (2 : k) ≠ 0)

/-- The ring map $k[\lambda, (\lambda(\lambda - 1))^{-1}] \to R$, $\lambda \mapsto l$, for $l, l - 1$ units. -/
def legendreLift {R : Type u} [CommRing R] (f : k →+* R) (l : R) (hl : IsUnit (l * (l - 1))) :
    LegendreRing k →+* R :=
  IsLocalization.Away.lift (Polynomial.X * (Polynomial.X - 1) : Polynomial k)
    (g := Polynomial.eval₂RingHom f l) (by simpa using hl)

theorem legendreLift_algebraMap {R : Type u} [CommRing R] (f : k →+* R) (l : R) (hl : IsUnit (l * (l - 1)))
    (q : Polynomial k) :
    legendreLift f l hl (algebraMap (Polynomial k) (LegendreRing k) q) = Polynomial.eval₂ f l q :=
  IsLocalization.Away.lift_eq _ _ q

theorem legendreLift_ext {R : Type u} [CommRing R] {ρ ρ' : LegendreRing k →+* R}
    (hC : ∀ a : k, ρ (algebraMap k _ a) = ρ' (algebraMap k _ a))
    (hX : ρ (algebraMap (Polynomial k) _ Polynomial.X) = ρ' (algebraMap (Polynomial k) _ Polynomial.X)) :
    ρ = ρ' := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X * (Polynomial.X - 1) : Polynomial k))
  apply Polynomial.ringHom_ext
  · intro a
    have := hC a
    rwa [IsScalarTower.algebraMap_apply k (Polynomial k) (LegendreRing k)] at this
  · exact hX

end Maps

/-! ### Transport of the chart data along a cartesian morphism of elliptic curves -/

section Over

variable {k : Type u} [Field k] (h2 : (2 : k) ≠ 0)
  {S S' : Scheme.{u}} (p : S ⟶ Spec (CommRingCat.of k)) (p' : S' ⟶ Spec (CommRingCat.of k))
  {E : EllipticCurveGeom S} {E' : EllipticCurveGeom S'}
  {φ : Multiplicative (ZMod 2 × ZMod 2) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}
  {φ' : Multiplicative (ZMod 2 × ZMod 2) →* (𝟙_ (Over S') ⟶ Over.mk E'.structureMap)}
  (hφ : E.IsFiberwiseInjective φ) (hφ' : E'.IsFiberwiseInjective φ')
  {g : E'.carrier ⟶ E.carrier} {b : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap b)
  {c : PointedWeierstrassChart E.structureMap E.zero} {c' : PointedWeierstrassChart E'.structureMap E'.zero}
  {h : c'.base ⟶ c.base} (hh : h ≫ c.baseMap = c'.baseMap ≫ b)

/-- The morphism of restrictions of the curves over chart bases induced by `g`. -/
def carrierMapOver : c'.pullbackCarrier ⟶ c.pullbackCarrier :=
  c.isPullback.lift (c'.toTotal ≫ g) (c'.toBase ≫ h) (by
    rw [Category.assoc, hg.w, ← Category.assoc, c'.isPullback.w, Category.assoc, Category.assoc, hh])

@[reassoc (attr := simp)]
theorem carrierMapOver_toTotal : carrierMapOver hg hh ≫ c.toTotal = c'.toTotal ≫ g :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
theorem carrierMapOver_toBase : carrierMapOver hg hh ≫ c.toBase = c'.toBase ≫ h :=
  IsPullback.lift_snd _ _ _ _

theorem isPullback_carrierMapOver : IsPullback (carrierMapOver hg hh) c'.toBase c.toBase h := by
  refine IsPullback.of_right ?_ (carrierMapOver_toBase hg hh) c.isPullback
  rw [carrierMapOver_toTotal, hh]
  exact c'.isPullback.paste_horiz hg

theorem chartPoint_carrierMapOver {P : S ⟶ E.carrier} (hP : P ≫ E.structureMap = 𝟙 S) {P' : S' ⟶ E'.carrier}
    (hP' : P' ≫ E'.structureMap = 𝟙 S') (hPP : P' ≫ g = b ≫ P) :
    c'.chartPoint hP' ≫ carrierMapOver hg hh = h ≫ c.chartPoint hP := by
  apply c.isPullback.hom_ext
  · simp [hPP, reassoc_of% hh]
  · simp

/-- The ring map of the morphism `h` of chart bases. -/
def ringMapOver (h : c'.base ⟶ c.base) : c.ring ⟶ c'.ring :=
  Spec.preimage (c'.baseIso.inv ≫ h ≫ c.baseIso.hom)

theorem spec_ringMapOver (h : c'.base ⟶ c.base) :
    Spec.map (ringMapOver h) = c'.baseIso.inv ≫ h ≫ c.baseIso.hom :=
  Spec.map_preimage _

/-- The morphism of projective models of the two charts induced by `g`. -/
def modelMapOver : c'.equation.projModel ⟶ c.equation.projModel :=
  c'.modelIso.inv ≫ carrierMapOver hg hh ≫ c.modelIso.hom

theorem isPullback_modelMapOver :
    IsPullback (modelMapOver hg hh) c'.equation.projModelOver c.equation.projModelOver
      (Spec.map (ringMapOver h)) := by
  rw [spec_ringMapOver]
  exact (isPullback_carrierMapOver hg hh).of_iso c'.modelIso c.modelIso c'.baseIso c.baseIso
    (by simp [modelMapOver]) c'.modelIso_over.symm c.modelIso_over.symm (by simp)

theorem modelPoint_modelMapOver {P : S ⟶ E.carrier} (hP : P ≫ E.structureMap = 𝟙 S) {P' : S' ⟶ E'.carrier}
    (hP' : P' ≫ E'.structureMap = 𝟙 S') (hPP : P' ≫ g = b ≫ P) :
    c'.modelPoint hP' ≫ modelMapOver hg hh = Spec.map (ringMapOver h) ≫ c.modelPoint hP := by
  rw [spec_ringMapOver, PointedWeierstrassChart.modelPoint_def, PointedWeierstrassChart.modelPoint_def,
    modelMapOver]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% chartPoint_carrierMapOver hg hh hP hP' hPP]

variable (h0 : E'.zero ≫ g = b ≫ E.zero) (hpts : ∀ a, (φ' a).left ≫ g = b ≫ (φ a).left) (hp : b ≫ p = p')

include h0 in
theorem projModelZero_modelMapOver :
    c'.equation.projModelZero ≫ modelMapOver hg hh = Spec.map (ringMapOver h) ≫ c.equation.projModelZero := by
  have := modelPoint_modelMapOver hg hh E.zero_comp E'.zero_comp h0
  simpa using this

include hp hh in
theorem chartAlg_ringMapOver : chartAlg p c ≫ ringMapOver h = chartAlg p' c' := by
  apply Spec.map_injective
  rw [Spec.map_comp, spec_ringMapOver, spec_chartAlg, spec_chartAlg, ← hp]
  simp [reassoc_of% hh]

include hg hh h0 hpts hp in
/-- **The chart ring maps are compatible along `g`.** -/
theorem chartRho_ringMapOver :
    (ringMapOver h).hom.comp (chartRho h2 p hφ c) = chartRho h2 p' hφ' c' := by
  apply legendreLift_ext
  · intro a
    rw [RingHom.comp_apply, ← RingHom.comp_apply (chartRho h2 p hφ c), chartRho_algebraMap_k,
      ← RingHom.comp_apply (chartRho h2 p' hφ' c'), chartRho_algebraMap_k, ← chartAlg_ringMapOver p p' hh hp]
    rfl
  · simp only [RingHom.comp_apply, chartRho_algebraMap, Polynomial.eval₂_X, lamC, chartLam]
    symm
    exact chartLam_eq_of_hom hφ' c' c.equation (ringMapOver h).hom (modelMapOver hg hh)
      (isPullback_modelMapOver hg hh) (projModelZero_modelMapOver hg hh h0)
      (coords_equation hφ c e₁_ne_one) (coords_equation hφ c e₂_ne_one)
      (by rw [← modelPoint_coords]; exact modelPoint_modelMapOver hg hh _ _ (hpts _))
      (by rw [← modelPoint_coords]; exact modelPoint_modelMapOver hg hh _ _ (hpts _))
      (two_mul_chartHalf h2 p c) (two_mul_chartHalf h2 p' c') (isUnit_coords_sub hφ c)

include hg hh h0 hpts hp in
theorem spec_chartRho_over :
    c'.baseIso.hom ≫ Spec.map (CommRingCat.ofHom (chartRho h2 p' hφ' c')) =
      h ≫ c.baseIso.hom ≫ Spec.map (CommRingCat.ofHom (chartRho h2 p hφ c)) := by
  rw [← chartRho_ringMapOver h2 p p' hφ hφ' hg hh h0 hpts hp, CommRingCat.ofHom_comp, Spec.map_comp,
    CommRingCat.ofHom_hom, spec_ringMapOver]
  simp

end Over

/-! ### Naturality of the $\lambda$-map -/

section Naturality

variable {k : Type u} [Field k] (h2 : (2 : k) ≠ 0)
  {S S' : Scheme.{u}} (p : S ⟶ Spec (CommRingCat.of k)) (p' : S' ⟶ Spec (CommRingCat.of k))
  {E : EllipticCurveGeom S} {E' : EllipticCurveGeom S'}
  {φ : Multiplicative (ZMod 2 × ZMod 2) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}
  {φ' : Multiplicative (ZMod 2 × ZMod 2) →* (𝟙_ (Over S') ⟶ Over.mk E'.structureMap)}
  (hφ : E.IsFiberwiseInjective φ) (hφ' : E'.IsFiberwiseInjective φ')
  {g : E'.carrier ⟶ E.carrier} {b : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap b)
  (h0 : E'.zero ≫ g = b ≫ E.zero) (hpts : ∀ a, (φ' a).left ≫ g = b ≫ (φ a).left) (hp : b ≫ p = p')

include hg h0 hpts hp in
/-- **Naturality of the $\lambda$-map** along a cartesian morphism of elliptic curves carrying the basis to the
basis. -/
theorem lamMap_comp : lamMap h2 p' hφ' = b ≫ lamMap h2 p hφ := by
  obtain ⟨A'⟩ := E'.localModel
  obtain ⟨A⟩ := E.localModel
  refine A'.hom_ext (𝟙 S') _ _ fun i ↦ ?_
  set c' := A'.chart i
  have hc : pullback.fst (𝟙 S') c'.baseMap = pullback.snd _ _ ≫ c'.baseMap := by
    simpa using pullback.condition (f := 𝟙 S') (g := c'.baseMap)
  rw [hc, Category.assoc, Category.assoc]
  congr 1
  rw [baseMap_lamMap]
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
  -- on the restricted chart `c''`, both sides are the chart map of `c''`
  have e1 := spec_chartRho h2 p' hφ' (PointedWeierstrassChart.restrictι_baseMap c' V')
  have e2 := spec_chartRho_over h2 p p' hφ hφ' hg hh h0 hpts hp
  rw [e1, e2, ← Category.assoc, ← Category.assoc, PointedWeierstrassChart.restrictι_baseMap]
  change _ = c''.baseMap ≫ b ≫ lamMap h2 p hφ
  rw [← Category.assoc c''.baseMap, ← hh, Category.assoc h c.baseMap, baseMap_lamMap, Category.assoc]

end Naturality

/-! ### The $\lambda$-map of a Weierstrass family -/

section Weierstrass

variable {k : Type u} [Field k] (h2 : (2 : k) ≠ 0) {R : Type u} [CommRing R] [Algebra k R]
  (W : WeierstrassCurve R) [W.IsElliptic]
  {φ : Multiplicative (ZMod 2 × ZMod 2) →* (𝟙_ (Over (Spec (.of R))) ⟶ Over.mk W.toEllipticCurveGeom.structureMap)}
  (hφ : W.toEllipticCurveGeom.IsFiberwiseInjective φ)
  {x₁ y₁ x₂ y₂ : R} (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
  (hφ₁ : φ e₁ = Ch8Counterexample.affinePointHom W h₁) (hφ₂ : φ e₂ = Ch8Counterexample.affinePointHom W h₂)
  (hy₁ : 2 * y₁ + W.a₁ * x₁ + W.a₃ = 0) (hy₂ : 2 * y₂ + W.a₁ * x₂ + W.a₃ = 0) (hx : IsUnit (x₂ - x₁))

/-- $1/2$ in a $k$-algebra. -/
def half (R : Type u) [CommRing R] [Algebra k R] : R := algebraMap k R (2 : k)⁻¹

include h2 in
theorem two_mul_half : 2 * half (k := k) R = 1 := by
  rw [half, ← map_ofNat (algebraMap k R) 2, ← map_mul, mul_inv_cancel₀ h2, map_one]

include h2 h₁ h₂ hy₁ hy₂ in
theorem isUnit_lam_weierstrass : IsUnit (lam W (half (k := k) R) hx * (lam W (half (k := k) R) hx - 1)) :=
  (isUnit_lam (two_mul_half h2) (cubic_eq_zero h₁ hy₁) (cubic_eq_zero h₂ hy₂) hx W.isUnit_Δ).mul
    (isUnit_lam_sub_one (two_mul_half h2) (cubic_eq_zero h₁ hy₁) (cubic_eq_zero h₂ hy₂) hx W.isUnit_Δ)

include hφ₁ hφ₂ in
/-- **The $\lambda$-map of a Weierstrass family** is $\operatorname{Spec}$ of $\lambda \mapsto \lambda(W; x_1, x_2)$. -/
theorem lamMap_weierstrass :
    lamMap h2 (specStructure k R) hφ = Spec.map (CommRingCat.ofHom
      (legendreLift (algebraMap k R) (lam W (half (k := k) R) hx) (isUnit_lam_weierstrass h2 W h₁ h₂ hy₁ hy₂ hx))) := by
  obtain ⟨A⟩ := W.toEllipticCurveGeom.localModel
  refine A.hom_ext (𝟙 _) _ _ fun i ↦ ?_
  set c := A.chart i
  have hc : pullback.fst (𝟙 _) c.baseMap = pullback.snd _ _ ≫ c.baseMap := by
    simpa using pullback.condition (f := 𝟙 (Spec (.of R))) (g := c.baseMap)
  rw [hc, Category.assoc, Category.assoc]
  congr 1
  rw [baseMap_lamMap]
  set ψ : CommRingCat.of R ⟶ c.ring := Spec.preimage (c.baseIso.inv ≫ c.baseMap) with hψdef
  have hψ : Spec.map ψ = c.baseIso.inv ≫ c.baseMap := Spec.map_preimage _
  -- the model of `c` maps to the model of `W`
  set F : c.equation.projModel ⟶ W.projModel :=
    c.modelIso.inv ≫ c.toTotal ≫ (toEllipticCurveGeomIso W).hom
  have hF : IsPullback F c.equation.projModelOver W.projModelOver (Spec.map (CommRingCat.ofHom ψ.hom)) := by
    rw [CommRingCat.ofHom_hom, hψ]
    refine (c.isPullback_modelIso_inv_toTotal).of_iso (.refl _) (toEllipticCurveGeomIso W) (.refl _) (.refl _)
      (by simp [F]) (by simp) (by simp [toEllipticCurveGeomIso_hom_projModelOver]) (by simp)
  have hpt (P : Spec (.of R) ⟶ W.toEllipticCurveGeom.carrier)
      (hP : P ≫ W.toEllipticCurveGeom.structureMap = 𝟙 _) :
      c.modelPoint hP ≫ F = Spec.map (CommRingCat.ofHom ψ.hom) ≫ P ≫ (toEllipticCurveGeomIso W).hom := by
    rw [CommRingCat.ofHom_hom, hψ]
    simp [F, PointedWeierstrassChart.modelPoint_modelIso_inv_toTotal_assoc]
  have hF0 : c.equation.projModelZero ≫ F = Spec.map (CommRingCat.ofHom ψ.hom) ≫ W.projModelZero := by
    have := hpt _ W.toEllipticCurveGeom.zero_comp
    rwa [PointedWeierstrassChart.modelPoint_zero, zero_toEllipticCurveGeomIso_hom] at this
  have hpt₁ : c.modelPoint (hP φ e₁) ≫ F = Spec.map (CommRingCat.ofHom ψ.hom) ≫ W.projModelAffinePoint h₁ := by
    rw [hpt, hφ₁, Ch8Counterexample.affinePointHom_left, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hpt₂ : c.modelPoint (hP φ e₂) ≫ F = Spec.map (CommRingCat.ofHom ψ.hom) ≫ W.projModelAffinePoint h₂ := by
    rw [hpt, hφ₂, Ch8Counterexample.affinePointHom_left, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hlam := chartLam_eq_of_hom hφ c W ψ.hom F hF hF0 h₁ h₂ hpt₁ hpt₂ (two_mul_half h2)
    (two_mul_chartHalf h2 (specStructure k R) c) hx
  have hρ : chartRho h2 (specStructure k R) hφ c =
      ψ.hom.comp (legendreLift (algebraMap k R) (lam W (half (k := k) R) hx)
        (isUnit_lam_weierstrass h2 W h₁ h₂ hy₁ hy₂ hx)) := by
    apply legendreLift_ext
    · intro a
      rw [← RingHom.comp_apply (chartRho h2 _ hφ c), chartRho_algebraMap_k, RingHom.comp_apply,
        IsScalarTower.algebraMap_apply k (Polynomial k) (LegendreRing k), legendreLift_algebraMap,
        Polynomial.algebraMap_eq, Polynomial.eval₂_C]
      have : chartAlg (specStructure k R) c = CommRingCat.ofHom (algebraMap k R) ≫ ψ := by
        apply Spec.map_injective
        rw [spec_chartAlg, Spec.map_comp, hψ]
        simp [specStructure]
      rw [this]
      rfl
    · rw [chartRho_algebraMap, RingHom.comp_apply, legendreLift_algebraMap, Polynomial.eval₂_X,
        Polynomial.eval₂_X]
      exact hlam
  rw [hρ, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, hψ]
  simp

end Weierstrass

end ModularFormsKB.Milne.LevelTwoChart
