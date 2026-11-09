import ModularFormsKB.Milne.Ch8.LevelTwoLambda
import ModularFormsKB.Milne.Ch8.EllipticModuli
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Glue
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Neg
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Neg
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ZeroSection
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.VariableChange.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.NaiveLevel

/-!
# The Legendre parameter of an elliptic curve with a level-two structure, over a scheme

Let $E$ be an elliptic curve over a scheme $S$ over $\operatorname{Spec} k$, $2 \ne 0$ in $k$, and let
$\varphi : (\mathbb Z/2)^2 \to E(S)$ be injective on every fibre. On every pointed Weierstrass chart $c$ of $E$ the
sections $P = \varphi(1, 0)$, $Q = \varphi(0, 1)$ are affine points $(x_1, y_1), (x_2, y_2)$ of order two with
$x_2 - x_1$ a unit (`isUnit_sub`), so the Legendre parameter $\lambda_c$ of `LevelTwoLambda` is defined
(`chartLam`). It is compatible with the morphisms of chart bases (`chartLam_map`): two charts differ by a change of
variables (`exists_variableChange_of_isPullback`, through Tau Ceti's
`existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom`), and $\lambda$ is invariant under changes of
variables. Gluing along the charts (Tau Ceti's `EllipticCurveGeom.glueMorphisms`) gives the **$\lambda$-map**
$S \to \Lambda = \operatorname{Spec} k[\lambda, (\lambda(\lambda - 1))^{-1}]$ (`lamMap`), over $\operatorname{Spec} k$
(`lamMap_specStructure`) and equal to $\lambda_c$ on the base of every chart (`baseMap_lamMap`).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve TauCeti.AlgebraicGeometry MonoidalCategory
  ModularFormsKB.Milne.LevelTwoLambda MonObj

noncomputable section

namespace ModularFormsKB.Milne.LevelTwoChart

/-! ### Transport of the Legendre parameter along cartesian pointed morphisms of models -/

section Transport

theorem lam_congr {R : Type u} [CommRing R] {W W' : WeierstrassCurve R} (hW : W = W') {i i' : R}
    (hi : 2 * i = 1) (hi' : 2 * i' = 1) {x₁ x₂ x₁' x₂' : R} (e₁ : x₁ = x₁') (e₂ : x₂ = x₂')
    (hx : IsUnit (x₂ - x₁)) (hx' : IsUnit (x₂' - x₁')) : lam W i hx = lam W' i' hx' := by
  subst hW e₁ e₂
  have : i = i' := by linear_combination i' * hi - i * hi'
  subst this
  rfl

variable {R R' : Type u} [CommRing R] [CommRing R'] (W : WeierstrassCurve R) (W' : WeierstrassCurve R')
  (ψ : R →+* R')

/-- **A cartesian pointed morphism of projective models is a change of variables after base change**, and it moves
the $x$-coordinates of affine points by $x \mapsto u^2 x + r$. -/
theorem exists_variableChange_of_isPullback (F : W'.projModel ⟶ W.projModel)
    (hF : IsPullback F W'.projModelOver W.projModelOver (Spec.map (CommRingCat.ofHom ψ)))
    (hF0 : W'.projModelZero ≫ F = Spec.map (CommRingCat.ofHom ψ) ≫ W.projModelZero) :
    ∃ C : VariableChange R', C • W.map ψ = W' ∧ ∀ {x y : R} {x' y' : R'} (h : W.toAffine.Equation x y)
      (h' : W'.toAffine.Equation x' y'),
      W'.projModelAffinePoint h' ≫ F = Spec.map (CommRingCat.ofHom ψ) ≫ W.projModelAffinePoint h →
        ψ x = (C.u : R') ^ 2 * x' + C.r := by
  have base := W.isPullback_projModelBaseChange ψ
  let e := hF.isoIsPullback _ _ base
  have he1 : e.hom ≫ W.projModelBaseChange ψ = F := hF.isoIsPullback_hom_fst _ _ base
  have he2 : e.hom ≫ (W.map ψ).projModelOver = W'.projModelOver := hF.isoIsPullback_hom_snd _ _ base
  have h0 : W'.projModelZero ≫ e.hom = (W.map ψ).projModelZero := by
    apply base.hom_ext
    · rw [Category.assoc, he1, hF0, projModelZero_projModelBaseChange]
    · rw [Category.assoc, he2, projModelZero_projModelOver, projModelZero_projModelOver]
  obtain ⟨C, ⟨hC, hCe⟩, -⟩ := existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e he2 h0
  refine ⟨C, hC, fun {x y x' y'} h h' hpt ↦ ?_⟩
  have hp : W'.projModelAffinePoint h' ≫ e.hom = (W.map ψ).projModelAffinePoint (h.map ψ) := by
    apply base.hom_ext
    · rw [Category.assoc, he1, hpt, projModelAffinePoint_projModelBaseChange]
    · rw [Category.assoc, he2, projModelAffinePoint_projModelOver, projModelAffinePoint_projModelOver]
  rw [hCe, projModelAffinePoint_eqToHom_assoc h' hC.symm, projModelAffinePoint_projModelVariableChangeIso_hom,
    projModelAffinePoint_inj] at hp
  exact hp.1.symm

/-- **Transport of the Legendre parameter**: if the models are related by a change of variables after base change
along $\psi$, moving $\psi(x_j)$ to $u^2 x_j' + r$, then $\lambda' = \psi(\lambda)$. -/
theorem lam_transport (C : VariableChange R') (hC : C • W.map ψ = W') {i₂ : R} {i₂' : R'} (hi : 2 * i₂ = 1)
    (hi' : 2 * i₂' = 1) {x₁ x₂ : R} {x₁' x₂' : R'} (hu : IsUnit (x₂ - x₁)) (hu' : IsUnit (x₂' - x₁'))
    (e₁ : ψ x₁ = (C.u : R') ^ 2 * x₁' + C.r) (e₂ : ψ x₂ = (C.u : R') ^ 2 * x₂' + C.r) :
    lam W' i₂' hu' = ψ (lam W i₂ hu) := by
  have hw : IsUnit (ψ x₂ - ψ x₁) := by rw [← map_sub]; exact hu.map ψ
  have hv : IsUnit (((C.u : R') ^ 2 * x₂' + C.r) - ((C.u : R') ^ 2 * x₁' + C.r)) := by rwa [← e₁, ← e₂]
  have hψi : 2 * ψ i₂ = 1 := by rw [← map_ofNat ψ 2, ← map_mul, hi, map_one]
  calc lam W' i₂' hu' = lam (C • W.map ψ) i₂' hu' := lam_congr hC.symm hi' hi' rfl rfl _ _
    _ = lam (W.map ψ) i₂' hv := lam_variableChange C i₂' hi' hu' hv
    _ = lam (W.map ψ) (ψ i₂) hw := lam_congr rfl hi' hψi e₁.symm e₂.symm hv hw
    _ = ψ (lam W i₂ hu) := lam_map ψ i₂ hu hw

end Transport

/-! ### The two basis points on a chart -/

section Chart

variable {S : Scheme.{u}} {E : EllipticCurveGeom S}
  (φ : Multiplicative (ZMod 2 × ZMod 2) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap))

/-- The first basis vector $(1, 0)$. -/
abbrev e₁ : Multiplicative (ZMod 2 × ZMod 2) := .ofAdd (1, 0)

/-- The second basis vector $(0, 1)$. -/
abbrev e₂ : Multiplicative (ZMod 2 × ZMod 2) := .ofAdd (0, 1)

theorem e₁_ne_one : e₁ ≠ 1 := by decide

theorem e₂_ne_one : e₂ ≠ 1 := by decide

theorem e₂_ne_e₁ : e₂ ≠ e₁ := by decide

theorem inv_eq_self (a : Multiplicative (ZMod 2 × ZMod 2)) : a⁻¹ = a := by
  revert a; decide

theorem hP (a : Multiplicative (ZMod 2 × ZMod 2)) : (φ a).left ≫ E.structureMap = 𝟙 S :=
  EllipticCurveGeom.left_comp_structureMap _

/-- A point of a level-two family is its own negative. -/
theorem left_neg (a : Multiplicative (ZMod 2 × ZMod 2)) : (φ a).left ≫ E.neg = (φ a).left := by
  rw [← EllipticCurveGeom.hom_inv_left, ← map_inv, inv_eq_self]

variable {φ} (hφ : E.IsFiberwiseInjective φ) (c : PointedWeierstrassChart E.structureMap E.zero)

include hφ in
theorem exists_coords {a : Multiplicative (ZMod 2 × ZMod 2)} (ha : a ≠ 1) :
    ∃ (x y : c.ring) (h : c.equation.toAffine.Equation x y),
      c.modelPoint (hP φ a) = c.equation.projModelAffinePoint h :=
  c.equation.exists_eq_projModelAffinePoint (c.modelPoint_projModelOver (hP φ a))
    (c.modelPoint_apply_ne (hP φ a) (EllipticCurveGeom.isFiberwiseInjective_iff.mp hφ a ha))

theorem modelPoint_neg_eq (a : Multiplicative (ZMod 2 × ZMod 2)) :
    c.modelPoint (hP φ a) ≫ c.equation.projModelNeg = c.modelPoint (hP φ a) := by
  rw [← EllipticCurveGeom.modelPoint_neg]
  congr 1
  exact left_neg φ a

/-- **The model points are points of order two**: $2y + a_1x + a_3 = 0$. -/
theorem two_torsion (a : Multiplicative (ZMod 2 × ZMod 2)) {x y : c.ring} (h : c.equation.toAffine.Equation x y)
    (hpt : c.modelPoint (hP φ a) = c.equation.projModelAffinePoint h) :
    2 * y + c.equation.a₁ * x + c.equation.a₃ = 0 := by
  have h1 := modelPoint_neg_eq (φ := φ) c a
  rw [hpt, projModelAffinePoint_projModelNeg, projModelAffinePoint_inj] at h1
  have h2 := h1.2
  simp only [Affine.negY] at h2
  linear_combination -h2

include hφ in
/-- **The $x$-coordinates of the two basis points differ by a unit.** -/
theorem isUnit_sub {a b : Multiplicative (ZMod 2 × ZMod 2)} (hab : a ≠ b) {x y x' y' : c.ring}
    (h : c.equation.toAffine.Equation x y) (h' : c.equation.toAffine.Equation x' y')
    (hpa : c.modelPoint (hP φ a) = c.equation.projModelAffinePoint h)
    (hpb : c.modelPoint (hP φ b) = c.equation.projModelAffinePoint h') : IsUnit (x' - x) := by
  by_contra hx
  obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hx
  let s : Spec c.ring := ⟨m, hm.isPrime⟩
  have hs := (c.equation.projModelAffinePoint_apply_eq_or_eq_projModelNeg_iff h h' s).mpr hxm
  have hneg : c.equation.projModelAffinePoint h ≫ c.equation.projModelNeg = c.equation.projModelAffinePoint h := by
    rw [← hpa]; exact modelPoint_neg_eq c a
  rw [hneg, or_self] at hs
  refine c.modelPoint_apply_ne_modelPoint (hP φ a) (hP φ b) (fun t ht ↦ hab ?_) s (by rw [hpa, hpb]; exact hs)
  exact (hφ.left_apply_injective t ht).symm

/-- The coordinates of the basis point $\varphi(a)$ on a chart. -/
def coords {a : Multiplicative (ZMod 2 × ZMod 2)} (ha : a ≠ 1) : c.ring × c.ring :=
  ((exists_coords hφ c ha).choose, (exists_coords hφ c ha).choose_spec.choose)

theorem coords_equation {a : Multiplicative (ZMod 2 × ZMod 2)} (ha : a ≠ 1) :
    c.equation.toAffine.Equation (coords hφ c ha).1 (coords hφ c ha).2 :=
  (exists_coords hφ c ha).choose_spec.choose_spec.choose

theorem modelPoint_coords {a : Multiplicative (ZMod 2 × ZMod 2)} (ha : a ≠ 1) :
    c.modelPoint (hP φ a) = c.equation.projModelAffinePoint (coords_equation hφ c ha) :=
  (exists_coords hφ c ha).choose_spec.choose_spec.choose_spec

theorem isUnit_coords_sub : IsUnit ((coords hφ c e₂_ne_one).1 - (coords hφ c e₁_ne_one).1) :=
  isUnit_sub hφ c e₂_ne_e₁.symm (coords_equation hφ c e₁_ne_one) (coords_equation hφ c e₂_ne_one)
    (modelPoint_coords hφ c e₁_ne_one) (modelPoint_coords hφ c e₂_ne_one)

/-- **The Legendre parameter of a chart.** -/
def chartLam (i₂ : c.ring) : c.ring :=
  lam c.equation i₂ (isUnit_coords_sub hφ c)

theorem cubic_coords {a : Multiplicative (ZMod 2 × ZMod 2)} (ha : a ≠ 1) :
    4 * (coords hφ c ha).1 ^ 3 + c.equation.b₂ * (coords hφ c ha).1 ^ 2 +
      2 * c.equation.b₄ * (coords hφ c ha).1 + c.equation.b₆ = 0 :=
  cubic_eq_zero (coords_equation hφ c ha) (two_torsion c a _ (modelPoint_coords hφ c ha))

theorem isUnit_chartLam {i₂ : c.ring} (hi : 2 * i₂ = 1) : IsUnit (chartLam hφ c i₂) :=
  isUnit_lam hi (cubic_coords hφ c _) (cubic_coords hφ c _) _ c.equation.isUnit_Δ

theorem isUnit_chartLam_sub_one {i₂ : c.ring} (hi : 2 * i₂ = 1) : IsUnit (chartLam hφ c i₂ - 1) :=
  isUnit_lam_sub_one hi (cubic_coords hφ c _) (cubic_coords hφ c _) _ c.equation.isUnit_Δ

/-- The ring map $\Gamma(\text{base of } c) \to \Gamma(\text{base of } k)$ of a morphism of chart bases. -/
def chartRingMap {c k : PointedWeierstrassChart E.structureMap E.zero} (h : k.base ⟶ c.base) : c.ring ⟶ k.ring :=
  Spec.preimage (k.baseIso.inv ≫ h ≫ c.baseIso.hom)

theorem spec_chartRingMap {c k : PointedWeierstrassChart E.structureMap E.zero} (h : k.base ⟶ c.base) :
    Spec.map (chartRingMap h) = k.baseIso.inv ≫ h ≫ c.baseIso.hom :=
  Spec.map_preimage _

/-- **The Legendre parameters of two charts are compatible.** -/
theorem chartLam_map {c k : PointedWeierstrassChart E.structureMap E.zero} {h : k.base ⟶ c.base}
    (hh : h ≫ c.baseMap = k.baseMap) {i₂ : c.ring} {i₂' : k.ring} (hi : 2 * i₂ = 1) (hi' : 2 * i₂' = 1) :
    chartLam hφ k i₂' = (chartRingMap h).hom (chartLam hφ c i₂) := by
  set ψ := (chartRingMap h).hom
  have hψ : Spec.map (CommRingCat.ofHom ψ) = k.baseIso.inv ≫ h ≫ c.baseIso.hom := by
    rw [← spec_chartRingMap h]; rfl
  have hF := PointedWeierstrassChart.isPullback_projModelMap hh
  have hF0 := PointedWeierstrassChart.projModelZero_projModelMap hh
  rw [← hψ] at hF hF0
  obtain ⟨C, hC, hx⟩ := exists_variableChange_of_isPullback c.equation k.equation ψ _ hF hF0
  have hpt (a : Multiplicative (ZMod 2 × ZMod 2)) (ha : a ≠ 1) :
      ψ (coords hφ c ha).1 = (C.u : k.ring) ^ 2 * (coords hφ k ha).1 + C.r := by
    refine hx (coords_equation hφ c ha) (coords_equation hφ k ha) ?_
    rw [← modelPoint_coords, ← modelPoint_coords, PointedWeierstrassChart.modelPoint_projModelMap, hψ]
  exact lam_transport c.equation k.equation ψ C hC hi hi' _ _ (hpt _ _) (hpt _ _)

end Chart

/-! ### The $\lambda$-map, glued along the charts -/

section Glue

variable {k : Type u} [Field k] (h2 : (2 : k) ≠ 0) {S : Scheme.{u}} (p : S ⟶ Spec (CommRingCat.of k))
  {E : EllipticCurveGeom S} {φ : Multiplicative (ZMod 2 × ZMod 2) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)}
  (hφ : E.IsFiberwiseInjective φ)

/-- The $k$-algebra structure of the coefficient ring of a chart. -/
def chartAlg (c : PointedWeierstrassChart E.structureMap E.zero) : CommRingCat.of k ⟶ c.ring :=
  Spec.preimage (c.baseIso.inv ≫ c.baseMap ≫ p)

theorem spec_chartAlg (c : PointedWeierstrassChart E.structureMap E.zero) :
    Spec.map (chartAlg p c) = c.baseIso.inv ≫ c.baseMap ≫ p :=
  Spec.map_preimage _

theorem chartAlg_comp {c k' : PointedWeierstrassChart E.structureMap E.zero} {h : k'.base ⟶ c.base}
    (hh : h ≫ c.baseMap = k'.baseMap) : chartAlg p c ≫ chartRingMap h = chartAlg p k' := by
  apply Spec.map_injective
  rw [Spec.map_comp, spec_chartRingMap, spec_chartAlg, spec_chartAlg]
  simp [reassoc_of% hh]

/-- The inverse of $2$ in the coefficient ring of a chart. -/
def chartHalf (c : PointedWeierstrassChart E.structureMap E.zero) : c.ring :=
  (chartAlg p c).hom (2 : k)⁻¹

include h2 in
theorem two_mul_chartHalf (c : PointedWeierstrassChart E.structureMap E.zero) : 2 * chartHalf p c = 1 := by
  rw [chartHalf, ← map_ofNat (chartAlg p c).hom 2, ← map_mul, mul_inv_cancel₀ h2, map_one]

/-- The Legendre parameter of a chart, with $1/2$ from $k$. -/
def lamC (c : PointedWeierstrassChart E.structureMap E.zero) : c.ring := chartLam hφ c (chartHalf p c)

include h2 in
theorem isUnit_lamC_mul (c : PointedWeierstrassChart E.structureMap E.zero) :
    IsUnit (lamC p hφ c * (lamC p hφ c - 1)) :=
  (isUnit_chartLam hφ c (two_mul_chartHalf h2 p c)).mul (isUnit_chartLam_sub_one hφ c (two_mul_chartHalf h2 p c))

/-- **The chart ring map** $k[\lambda, (\lambda(\lambda - 1))^{-1}] \to \Gamma(\text{base of } c)$,
$\lambda \mapsto \lambda_c$. -/
def chartRho (c : PointedWeierstrassChart E.structureMap E.zero) : LegendreRing k →+* c.ring :=
  IsLocalization.Away.lift (Polynomial.X * (Polynomial.X - 1) : Polynomial k)
    (g := Polynomial.eval₂RingHom (chartAlg p c).hom (lamC p hφ c)) (by
      simpa using isUnit_lamC_mul h2 p hφ c)

theorem chartRho_algebraMap (c : PointedWeierstrassChart E.structureMap E.zero) (q : Polynomial k) :
    chartRho h2 p hφ c (algebraMap (Polynomial k) (LegendreRing k) q) =
      Polynomial.eval₂ (chartAlg p c).hom (lamC p hφ c) q :=
  IsLocalization.Away.lift_eq _ _ q

theorem chartRho_comp {c k' : PointedWeierstrassChart E.structureMap E.zero} {h : k'.base ⟶ c.base}
    (hh : h ≫ c.baseMap = k'.baseMap) :
    (chartRingMap h).hom.comp (chartRho h2 p hφ c) = chartRho h2 p hφ k' := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X * (Polynomial.X - 1) : Polynomial k))
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, chartRho_algebraMap, Polynomial.eval₂_C]
    rw [← chartAlg_comp p hh]
    rfl
  · simp only [RingHom.comp_apply, chartRho_algebraMap, Polynomial.eval₂_X, lamC]
    exact (chartLam_map hφ hh (two_mul_chartHalf h2 p c) (two_mul_chartHalf h2 p k')).symm

theorem chartRho_algebraMap_k (c : PointedWeierstrassChart E.structureMap E.zero) :
    (chartRho h2 p hφ c).comp (algebraMap k (LegendreRing k)) = (chartAlg p c).hom := by
  ext a
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k (Polynomial k) (LegendreRing k), chartRho_algebraMap]
  simp

/-- The $\lambda$-map on the part of $S$ over the base of a chart. -/
def piece (c : PointedWeierstrassChart E.structureMap E.zero) :
    pullback (𝟙 S) c.baseMap ⟶ Spec (CommRingCat.of (LegendreRing k)) :=
  pullback.snd (𝟙 S) c.baseMap ≫ c.baseIso.hom ≫ Spec.map (CommRingCat.ofHom (chartRho h2 p hφ c))

theorem spec_chartRho {c k' : PointedWeierstrassChart E.structureMap E.zero} {h : k'.base ⟶ c.base}
    (hh : h ≫ c.baseMap = k'.baseMap) :
    h ≫ c.baseIso.hom ≫ Spec.map (CommRingCat.ofHom (chartRho h2 p hφ c)) =
      k'.baseIso.hom ≫ Spec.map (CommRingCat.ofHom (chartRho h2 p hφ k')) := by
  rw [← chartRho_comp h2 p hφ hh, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, spec_chartRingMap]
  simp

theorem map_piece {c k' : PointedWeierstrassChart E.structureMap E.zero} {h : k'.base ⟶ c.base}
    (hh : h ≫ c.baseMap = k'.baseMap) :
    pullback.map (𝟙 S) k'.baseMap (𝟙 S) c.baseMap (𝟙 _) h (𝟙 _) (by simp) (by simp [hh]) ≫ piece h2 p hφ c =
      piece h2 p hφ k' := by
  rw [piece, piece, pullback.lift_snd_assoc, Category.assoc, spec_chartRho h2 p hφ hh]

/-- **The $\lambda$-map** $S \to \Lambda$ of a level-two family. -/
def lamMap : S ⟶ Spec (CommRingCat.of (LegendreRing k)) :=
  EllipticCurveGeom.glueMorphisms (q := 𝟙 S) (piece h2 p hφ) (map_piece h2 p hφ)

/-- On the base of a chart, the $\lambda$-map is $\operatorname{Spec}$ of the chart ring map. -/
theorem baseMap_lamMap (c : PointedWeierstrassChart E.structureMap E.zero) :
    c.baseMap ≫ lamMap h2 p hφ = c.baseIso.hom ≫ Spec.map (CommRingCat.ofHom (chartRho h2 p hφ c)) := by
  have := pullback.lift c.baseMap (𝟙 c.base) (by simp) ≫=
    EllipticCurveGeom.fst_glueMorphisms (q := 𝟙 S) (piece h2 p hφ) (map_piece h2 p hφ) c
  simpa [lamMap, piece, -EllipticCurveGeom.fst_glueMorphisms, -EllipticCurveGeom.fst_glueMorphisms_assoc] using this

/-- **The $\lambda$-map lies over $\operatorname{Spec} k$.** -/
theorem lamMap_specStructure : lamMap h2 p hφ ≫ specStructure k (LegendreRing k) = p := by
  obtain ⟨A⟩ := E.localModel
  refine A.hom_ext (𝟙 S) _ _ fun i ↦ ?_
  have hc : pullback.fst (𝟙 S) (A.chart i).baseMap = pullback.snd _ _ ≫ (A.chart i).baseMap := by
    simpa using pullback.condition (f := 𝟙 S) (g := (A.chart i).baseMap)
  rw [hc, Category.assoc, Category.assoc, reassoc_of% baseMap_lamMap h2 p hφ (A.chart i)]
  congr 1
  rw [specStructure, ← Spec.map_comp, ← CommRingCat.ofHom_comp, chartRho_algebraMap_k, CommRingCat.ofHom_hom,
    spec_chartAlg, Iso.hom_inv_id_assoc]

end Glue

end ModularFormsKB.Milne.LevelTwoChart
