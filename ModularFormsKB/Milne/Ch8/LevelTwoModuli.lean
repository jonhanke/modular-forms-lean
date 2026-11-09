import ModularFormsKB.Milne.Ch8.LevelTwoMap
import ModularFormsKB.Milne.Ch8.LevelOne

/-!
# Milne, Theorem 8.8 for $N = 2$: the $\lambda$-line is a (coarse) solution

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 8, Theorem 8.8 and
Example 8.9 (pdf p. 100).

Over an algebraically closed field $k$ with $2 \ne 0$, the moduli problem $\mathcal E_2$ is solved by the Legendre line
$\Lambda = \operatorname{Spec} k[\lambda, (\lambda(\lambda - 1))^{-1}]$ with $\alpha(E, t) = \lambda(E, t)$, the
Legendre parameter of the basis $t$ of $E[2]$ (`levelModuliSolution_two`). The solution is coarse, not fine
(`Ch8Counterexample.not_exists_isFineModuliSolution`).

- For a pair $x = (E, t)$ over a variety $V$, `lamMor x : V ⟶ Λ` is the $\lambda$-map of `LevelTwoChart.lamMap`. It
  is invariant under isomorphism and natural under base change (`lamMor_rel`, `lamMor_pull`, from
  `LevelTwoChart.lamMap_comp`), which gives condition (a) of Definition 8.1.
- On the Legendre pair $L$ over $\Lambda$ (the curve $y^2 = x(x - 1)(x - \lambda)$ with the basis $(0, 0), (1, 0)$),
  `lamMor L` is the identity (`lamMor_legendre`, from `LevelTwoChart.lamMap_weierstrass`): so $\alpha$ is surjective
  and condition (b) holds, with the regular map $\Lambda \to Z$ of the family $L$.
- Injectivity of $\alpha$ (`rel_pull_legendre`): every pair over $k$ is isomorphic to the pullback of $L$ along its
  $\lambda$, by the change of variables $u^2 = x_2 - x_1$, $r = x_1$, $s = -a_1/2$, $t = y_1$ to Legendre form.
- The Weil pairing condition is automatic at level two (`Ch8Counterexample.hasWeilPairing_two`), so
  $\mathcal E_2$ is the problem of all pairs with a level-two structure (`levelNFunctorIsoOfForall`).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite WeierstrassCurve TauCeti.AlgebraicGeometry MonoidalCategory
  ModularFormsKB.Milne.LevelTwoLambda ModularFormsKB.Milne.LevelTwoChart MonObj TauCeti

noncomputable section

namespace ModularFormsKB.Milne.LevelTwoModuli

open Ch8Counterexample

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Residue fields of a scheme over $k$ have $2 \ne 0$ when $2 \ne 0$ in $k$. -/
theorem two_ne_zero_of_over (h2 : ((2 : ℕ) : k) ≠ 0) {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) (s : X) :
    ((2 : ℕ) : X.residueField s) ≠ 0 := by
  intro h
  apply two_ne_zero_residueField (k := k) h2 (p s)
  apply (p.residueFieldMap s).hom.injective
  rw [map_natCast, h, map_zero]

/-- The Legendre line as a variety. -/
abbrev lamLine (k : Type u) [Field k] [IsAlgClosed k] : Variety k :=
  specVariety (LegendreRing k) isAffineAlgebra_legendreRing

/-- The level-two family of a pair. -/
abbrev fam {V : Variety k} (x : LevelPair (ModuliProblem.gamma (Spec (CommRingCat.of k)) 2) V) :
    Multiplicative (ZMod 2 × ZMod 2) →* (𝟙_ (Over V.obj.left) ⟶ Over.mk x.1.structureMap) :=
  (ModuliProblem.gammaEquiv _ x.2).1

variable (h2 : ((2 : ℕ) : k) ≠ 0)
include h2

theorem two_ne_zero' : (2 : k) ≠ 0 := by simpa using h2

theorem fam_injective {V : Variety k} (x : LevelPair (ModuliProblem.gamma (Spec (CommRingCat.of k)) 2) V) :
    x.1.IsFiberwiseInjective (fam x) :=
  (ModuliProblem.gammaEquiv _ x.2).2.isFiberwiseInjective (two_ne_zero_of_over h2 V.obj.hom)

/-- **The $\lambda$-map of a pair**, as a regular map $V \to \Lambda$. -/
def lamMor {V : Variety k} (x : LevelPair (ModuliProblem.gamma (Spec (CommRingCat.of k)) 2) V) :
    V ⟶ lamLine k :=
  ⟨Over.homMk (lamMap (two_ne_zero' h2) V.obj.hom (fam_injective h2 x))
    (lamMap_specStructure (two_ne_zero' h2) V.obj.hom (fam_injective h2 x))⟩

theorem lamMor_left {V : Variety k} (x : LevelPair (ModuliProblem.gamma (Spec (CommRingCat.of k)) 2) V) :
    (lamMor h2 x).hom.left = lamMap (two_ne_zero' h2) V.obj.hom (fam_injective h2 x) := rfl

/-- **The $\lambda$-map along an arrow of `Ell/k`.** -/
theorem lamMap_hom {V V' : Variety k} (x : LevelPair (ModuliProblem.gamma (Spec (CommRingCat.of k)) 2) V)
    (E' : EllipticCurveGeom V'.obj.left) (f : V'.ellObj E' ⟶ V.ellObj x.1) :
    lamMap (two_ne_zero' h2) V'.obj.hom (fam_injective h2 ⟨E', (ModuliProblem.gamma _ 2).map f.op x.2⟩) =
      f.base ≫ lamMap (two_ne_zero' h2) V.obj.hom (fam_injective h2 x) := by
  refine lamMap_comp (two_ne_zero' h2) V.obj.hom V'.obj.hom (fam_injective h2 x) _ f.isPullback f.zero_total
    (fun a ↦ ?_) f.base_structureMap
  change ((ModuliProblem.gammaEquiv _ ((ModuliProblem.gamma _ 2).map f.op x.2)).1 a).left ≫ f.total = _
  rw [ModuliProblem.gammaEquiv_map, MonoidHom.comp_apply, EllipticCurveGeom.pointsPullback_left_comp]

theorem lamMor_rel {V : Variety k} {x y : LevelPair (ModuliProblem.gamma (Spec (CommRingCat.of k)) 2) V}
    (h : LevelPair.Rel x y) : lamMor h2 x = lamMor h2 y := by
  obtain ⟨f, hf, hfy⟩ := h
  apply InducedCategory.hom_ext
  apply Over.OverMorphism.ext
  rw [lamMor_left, lamMor_left]
  have := lamMap_hom h2 y x.1 f
  rw [hf, Category.id_comp] at this
  rw [← this]
  congr 2
  exact Sigma.ext rfl (heq_of_eq hfy.symm)

theorem lamMor_pull {V W : Variety k} (φ : W ⟶ V)
    (x : LevelPair (ModuliProblem.gamma (Spec (CommRingCat.of k)) 2) V) :
    lamMor h2 (LevelPair.pull φ x) = φ ≫ lamMor h2 x := by
  apply InducedCategory.hom_ext
  apply Over.OverMorphism.ext
  rw [lamMor_left]
  exact lamMap_hom h2 x _ (LevelPair.pullHom φ x.1)

/-! ### The Legendre pair -/

theorem isUnit_two_legendreRing' : IsUnit (2 : LegendreRing k) := by
  rw [← map_ofNat (algebraMap k (LegendreRing k)) 2]
  exact (IsUnit.mk0 (2 : k) (two_ne_zero' h2)).map _

theorem isElliptic_legendreCurve : (legendreCurve k).IsElliptic := by
  rw [isElliptic_freyCurve_iff]
  refine ⟨isUnit_two_legendreRing' h2, isUnit_one, isUnit_legendreLambda.neg, ?_⟩
  have : (1 : LegendreRing k) + -legendreLambda k = -(legendreLambda k - 1) := by ring
  rw [this]
  exact isUnit_legendreLambda_sub_one.neg

/-- The Legendre pair over $\Lambda$. -/
abbrev legPair : LevelPair (ModuliProblem.gamma (Spec (CommRingCat.of k)) 2) (lamLine k) :=
  haveI := isElliptic_legendreCurve h2
  pairOf k _ (legendreCurve k) rfl rfl legendre_eq_zero legendre_eq_one (by simp)

theorem fam_legPair_one [(legendreCurve k).IsElliptic] :
    fam (legPair h2) e₁ = affinePointHom (legendreCurve k) legendre_eq_zero :=
  (congrArg (fun f ↦ f e₁) (gammaEquiv_pairOf (k := k) isAffineAlgebra_legendreRing (legendreCurve k) rfl rfl
    legendre_eq_zero legendre_eq_one (by simp))).trans (level2_one_zero _ _ _ _)

theorem fam_legPair_two [(legendreCurve k).IsElliptic] :
    fam (legPair h2) e₂ = affinePointHom (legendreCurve k) legendre_eq_one :=
  (congrArg (fun f ↦ f e₂) (gammaEquiv_pairOf (k := k) isAffineAlgebra_legendreRing (legendreCurve k) rfl rfl
    legendre_eq_zero legendre_eq_one (by simp))).trans (level2_zero_one _ _ _ _)

theorem lam_legendre :
    lam (legendreCurve k) (half (k := k) (LegendreRing k)) (x₁ := 0) (x₂ := 1) (by simp) = legendreLambda k := by
  rw [lam_eq_iff]
  have hh := two_mul_half (k := k) (R := LegendreRing k) (two_ne_zero' h2)
  simp only [thirdRoot, b₂, freyCurve]
  linear_combination (-(legendreLambda k + 1) * (2 * half (k := k) (LegendreRing k) + 1)) * hh

/-- **The $\lambda$-map of the Legendre pair is the identity.** -/
theorem lamMor_legendre : lamMor h2 (legPair h2) = 𝟙 (lamLine k) := by
  haveI := isElliptic_legendreCurve h2
  apply InducedCategory.hom_ext
  apply Over.OverMorphism.ext
  rw [lamMor_left]
  have hφ₁ : fam (legPair h2) e₁ = affinePointHom (legendreCurve k) legendre_eq_zero :=
    (congrArg (fun f ↦ f e₁) (gammaEquiv_pairOf (k := k) isAffineAlgebra_legendreRing (legendreCurve k) rfl rfl
      legendre_eq_zero legendre_eq_one (by simp))).trans (level2_one_zero _ _ _ _)
  have hφ₂ : fam (legPair h2) e₂ = affinePointHom (legendreCurve k) legendre_eq_one :=
    (congrArg (fun f ↦ f e₂) (gammaEquiv_pairOf (k := k) isAffineAlgebra_legendreRing (legendreCurve k) rfl rfl
      legendre_eq_zero legendre_eq_one (by simp))).trans (level2_zero_one _ _ _ _)
  have key := lamMap_weierstrass (two_ne_zero' h2) (legendreCurve k) (fam_injective h2 (legPair h2))
    legendre_eq_zero legendre_eq_one hφ₁ hφ₂ (by simp [freyCurve]) (by simp [freyCurve]) (by simp)
  refine key.trans ?_
  have hid : legendreLift (algebraMap k (LegendreRing k)) (lam (legendreCurve k) (half (LegendreRing k)) _)
      (isUnit_lam_weierstrass (two_ne_zero' h2) (legendreCurve k) legendre_eq_zero legendre_eq_one
        (by simp [freyCurve]) (by simp [freyCurve]) (by simp)) = RingHom.id _ := by
    apply legendreLift_ext
    · intro a
      rw [IsScalarTower.algebraMap_apply k (Polynomial k) (LegendreRing k), legendreLift_algebraMap]
      rw [Polynomial.algebraMap_eq, Polynomial.eval₂_C]; rfl
    · rw [legendreLift_algebraMap, Polynomial.eval₂_X, lam_legendre h2]
      rfl
  rw [hid]
  exact Spec.map_id _

theorem lamMor_pull_legendre (t : Variety.point k ⟶ lamLine k) : lamMor h2 (LevelPair.pull t (legPair h2)) = t := by
  rw [lamMor_pull, lamMor_legendre, Category.comp_id]

/-! ### Every pair over $k$ is a pullback of the Legendre pair -/

omit h2 in
/-- A point of the elliptic curve of a Weierstrass curve over $k$ missing the zero section is affine. -/
theorem exists_affinePointHom {W : WeierstrassCurve k} [W.IsElliptic]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ Over.mk W.toEllipticCurveGeom.structureMap)
    (hP : ∀ s, P.left s ≠ W.toEllipticCurveGeom.zero s) :
    ∃ (x y : k) (h : W.toAffine.Equation x y), P = affinePointHom W h := by
  have hP1 : (P.left ≫ (toEllipticCurveGeomIso W).hom) ≫ W.projModelOver = 𝟙 _ := by
    rw [Category.assoc, toEllipticCurveGeomIso_hom_projModelOver]
    exact EllipticCurveGeom.left_comp_structureMap P
  have hP0 : ∀ s, (P.left ≫ (toEllipticCurveGeomIso W).hom) s ≠ W.projModelZero s := by
    intro s hs
    apply hP s
    have := congrArg (fun z ↦ (toEllipticCurveGeomIso W).inv z) hs
    simp only [← Scheme.Hom.comp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      ← zero_toEllipticCurveGeomIso_hom] at this
    exact this
  obtain ⟨x, y, h, he⟩ := W.exists_eq_projModelAffinePoint hP1 hP0
  refine ⟨x, y, h, Over.OverMorphism.ext ?_⟩
  rw [affinePointHom_left, ← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]

omit h2 [IsAlgClosed k] in
theorem affinePointHom_inv' {R : Type u} [CommRing R] {W : WeierstrassCurve R} [W.IsElliptic] {x y : R}
    (h : W.toAffine.Equation x y) :
    (affinePointHom W h)⁻¹ = affinePointHom W ((W.toAffine.equation_neg x y).mpr h) := by
  apply Over.OverMorphism.ext
  rw [EllipticCurveGeom.hom_inv_left, affinePointHom_left, affinePointHom_left, Category.assoc,
    ← cancel_mono (toEllipticCurveGeomIso W).hom, Category.assoc, Category.assoc,
    neg_toEllipticCurveGeomIso_hom, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    projModelAffinePoint_projModelNeg]

omit h2 [IsAlgClosed k] in
theorem affinePointHom_inj {R : Type u} [CommRing R] {W : WeierstrassCurve R} [W.IsElliptic] {x y x' y' : R}
    {h : W.toAffine.Equation x y} {h' : W.toAffine.Equation x' y'}
    (he : affinePointHom W h = affinePointHom W h') : x = x' ∧ y = y' := by
  have := congrArg (fun P ↦ P.left ≫ (toEllipticCurveGeomIso W).hom) he
  simp only [affinePointHom_left, Category.assoc, Iso.inv_hom_id, Category.comp_id] at this
  rwa [projModelAffinePoint_inj] at this

omit h2 [IsAlgClosed k] in
/-- A point of the elliptic curve of a Weierstrass curve that is its own negative has order two. -/
theorem two_torsion_of_left_neg {R : Type u} [CommRing R] {W : WeierstrassCurve R} [W.IsElliptic] {x y : R}
    (h : W.toAffine.Equation x y)
    (hneg : (affinePointHom W h).left ≫ W.toEllipticCurveGeom.neg = (affinePointHom W h).left) :
    2 * y + W.a₁ * x + W.a₃ = 0 := by
  have h1 := congrArg (· ≫ (toEllipticCurveGeomIso W).hom) hneg
  simp only [affinePointHom_left, Category.assoc, neg_toEllipticCurveGeomIso_hom, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id, projModelAffinePoint_projModelNeg] at h1
  rw [projModelAffinePoint_inj] at h1
  have hy := h1.2
  simp only [Affine.negY] at hy
  linear_combination -hy

/-- **Every pair over $k$ is isomorphic to the pullback of the Legendre pair along its $\lambda$.** -/
theorem rel_pull_legendre (x : LevelPair (ModuliProblem.gamma (Spec (CommRingCat.of k)) 2) (Variety.point k)) :
    LevelPair.Rel x (LevelPair.pull (lamMor h2 x) (legPair h2)) := by
  haveI := isElliptic_legendreCurve h2
  obtain ⟨W, hW, e0, he0, hz⟩ := x.1.exists_iso_toEllipticCurveGeom
  let a : (Variety.point k).ellObj W.toEllipticCurveGeom ⟶ (Variety.point k).ellObj x.1 := isoHom _ e0 he0 hz
  let xW : LevelPair (ModuliProblem.gamma (Spec (CommRingCat.of k)) 2) (Variety.point k) :=
    ⟨W.toEllipticCurveGeom, (ModuliProblem.gamma _ 2).map a.op x.2⟩
  have r1 : LevelPair.Rel xW x := ⟨a, rfl, rfl⟩
  have hlam : lamMor h2 xW = lamMor h2 x := lamMor_rel h2 r1
  have hinj := fam_injective h2 xW
  obtain ⟨x₁, y₁, h₁, hφ₁⟩ := exists_affinePointHom (fam xW e₁)
    (EllipticCurveGeom.isFiberwiseInjective_iff.mp hinj _ e₁_ne_one)
  obtain ⟨x₂, y₂, h₂, hφ₂⟩ := exists_affinePointHom (fam xW e₂)
    (EllipticCurveGeom.isFiberwiseInjective_iff.mp hinj _ e₂_ne_one)
  have hy (b : Multiplicative (ZMod 2 × ZMod 2)) {x y : k} (h : W.toAffine.Equation x y)
      (hφ : fam xW b = affinePointHom W h) : 2 * y + W.a₁ * x + W.a₃ = 0 := by
    have h1 := LevelTwoChart.left_neg (fam xW) b
    rw [hφ] at h1
    exact two_torsion_of_left_neg h h1
  have hy₁ := hy e₁ h₁ hφ₁
  have hy₂ := hy e₂ h₂ hφ₂
  have hx : x₂ - x₁ ≠ 0 := by
    intro hx0
    have hX : x₂ = x₁ := sub_eq_zero.mp hx0
    have hY : y₂ = y₁ := by
      rcases Affine.Y_eq_of_X_eq h₂ h₁ hX with hY | hY
      · exact hY
      · rw [hY, Affine.negY]; linear_combination -hy₁
    have hfe : fam xW e₂ = fam xW e₁ := by
      rw [hφ₁, hφ₂]; exact affinePointHom_congr W h₂ h₁ hX hY
    haveI : Nonempty (Variety.point k).obj.left := inferInstanceAs (Nonempty (Spec (CommRingCat.of k)))
    exact e₂_ne_e₁ (hinj.injective hfe)
  have hxu : IsUnit (x₂ - x₁) := IsUnit.mk0 _ hx
  have hh := two_mul_half (k := k) (R := k) (two_ne_zero' h2)
  set i := half (k := k) k
  have hk := lamMap_weierstrass (R := k) (two_ne_zero' h2) W hinj h₁ h₂ hφ₁ hφ₂ hy₁ hy₂ hxu
  set l := lam W i hxu with hl
  set ev := legendreLift (algebraMap k k) l (isUnit_lam_weierstrass (two_ne_zero' h2) W h₁ h₂ hy₁ hy₂ hxu)
  have hs : specStructure k k = 𝟙 (Spec (CommRingCat.of k)) := by
    simp only [specStructure]
    convert Spec.map_id (CommRingCat.of k)
  rw [hs] at hk
  have hpt : (lamMor h2 x).hom.left = Spec.map (CommRingCat.ofHom ev) := by
    rw [← hlam, lamMor_left]
    exact hk
  have hevl : ev (legendreLambda k) = l := by
    rw [legendreLift_algebraMap, Polynomial.eval₂_X]
  -- the change of variables to Legendre form
  obtain ⟨u0, hu0⟩ := IsAlgClosed.exists_pow_nat_eq (x₂ - x₁) two_pos
  have hu0ne : u0 ≠ 0 := by
    rintro rfl
    exact hx (by rw [← hu0]; ring)
  let C : VariableChange k := ⟨Units.mk0 u0 hu0ne, x₁, -W.a₁ * i, y₁⟩
  have hCu : ((C.u : kˣ) : k) = u0 := rfl
  have hC0 : (C • W).toAffine.Equation 0 0 := by
    rw [← Affine.variableChange_equation]
    convert h₁ using 2 <;> simp [C]
  have hC1 : (C • W).toAffine.Equation 1 0 := by
    rw [← Affine.variableChange_equation]
    convert h₂ using 2
    · simp only [C, Units.val_mk0, _root_.mul_one]; rw [hu0]; ring
    · simp only [C, Units.val_mk0, mul_zero, _root_.mul_one, zero_add]
      linear_combination (-W.a₁ * i) * hu0 + i * hy₁ - i * hy₂ - (y₁ - y₂) * hh
  have ha₁ : (C • W).a₁ = 0 := by
    rw [variableChange_a₁]
    simp only [C]
    linear_combination -(↑(Units.mk0 u0 hu0ne)⁻¹ * W.a₁) * hh
  have ha₃ : (C • W).a₃ = 0 := by
    rw [variableChange_a₃]
    simp only [C]
    linear_combination (↑(Units.mk0 u0 hu0ne)⁻¹ ^ 3) * hy₁
  have ha₆ : (C • W).a₆ = 0 := by
    have := hC0
    rw [Affine.equation_iff] at this
    linear_combination -this
  have h1eq := hC1
  rw [Affine.equation_iff] at h1eq
  -- the Legendre parameter of `C • W` at `0, 1`
  have hlamC : lam (C • W) i (x₁ := 0) (x₂ := 1) (by simp) = l := by
    have hv : IsUnit (((C.u : k) ^ 2 * 1 + C.r) - ((C.u : k) ^ 2 * 0 + C.r)) := by
      rw [hCu]; simp only [_root_.mul_one, mul_zero, zero_add, add_sub_cancel_right]
      exact (IsUnit.mk0 u0 hu0ne).pow 2
    rw [lam_variableChange C i hh _ hv]
    exact lam_congr rfl hh hh (by simp [C]) (by rw [hCu]; simp [C]; rw [hu0]; ring) _ _
  have ha₂ : (C • W).a₂ = -l - 1 := by
    rw [← hlamC]
    have := lam_mul (W := C • W) i (x₁ := 0) (x₂ := 1) (by simp)
    simp only [thirdRoot, b₂, ha₁, sub_zero] at this
    linear_combination this + (-(C • W).a₂ * (2 * i + 1)) * hh
  have ha₄ : (C • W).a₄ = l := by
    rw [ha₂, ha₆, ha₁, ha₃] at h1eq
    linear_combination -h1eq
  have hCW : C • W = (legendreCurve k).map ev := by
    ext
    · rw [ha₁]; simp [freyCurve]
    · rw [ha₂]; simp [freyCurve, hevl]
    · rw [ha₃]; simp [freyCurve]
    · rw [ha₄]; simp [freyCurve, hevl]
    · rw [ha₆]; simp [freyCurve]
  -- the arrows
  let vc := vcHom (𝟙 (Spec (CommRingCat.of k))) W C
  let xC : LevelPair (ModuliProblem.gamma (Spec (CommRingCat.of k)) 2) (Variety.point k) :=
    ⟨(C • W).toEllipticCurveGeom, (ModuliProblem.gamma _ 2).map vc.op xW.2⟩
  have r2 : LevelPair.Rel xC xW := ⟨vc, rfl, rfl⟩
  have hg : Spec.map (CommRingCat.ofHom ev) ≫ specStructure k (LegendreRing k) = 𝟙 _ := by
    rw [specStructure, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : ev.comp (algebraMap k (LegendreRing k)) = RingHom.id k := by
      ext c
      rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k (Polynomial k) (LegendreRing k),
        legendreLift_algebraMap, Polynomial.algebraMap_eq, Polynomial.eval₂_C]
      rfl
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  let bc := bcHom (specStructure k (LegendreRing k)) (legendreCurve k) ev (𝟙 _) hg
  have hab : bc.base = (LevelPair.pullHom (lamMor h2 x) (legPair h2).1).base := by
    rw [bcHom_base, LevelPair.pullHom_base, hpt]
  have r3 := LevelPair.rel_of_arrows (V := Variety.point k) (P := ModuliProblem.gamma (Spec (CommRingCat.of k)) 2)
    (X := (lamLine k).ellObj (legPair h2).1) (legPair h2).2 bc (LevelPair.pullHom (lamMor h2 x) (legPair h2).1) hab
  -- the structures on `C • W = (legendreCurve k).map ev` agree
  have key : ∀ (W₁ : WeierstrassCurve k) [W₁.IsElliptic] (_ : W₁ = (legendreCurve k).map ev)
      (s₁ : (ModuliProblem.gamma (Spec (CommRingCat.of k)) 2).obj
        (op ((Variety.point k).ellObj W₁.toEllipticCurveGeom)))
      (h0₁ : W₁.toAffine.Equation 0 0) (h1₁ : W₁.toAffine.Equation 1 0)
      (_ : (ModuliProblem.gammaEquiv _ s₁).1 e₁ = affinePointHom W₁ h0₁)
      (_ : (ModuliProblem.gammaEquiv _ s₁).1 e₂ = affinePointHom W₁ h1₁),
      LevelPair.Rel (P := ModuliProblem.gamma (Spec (CommRingCat.of k)) 2) (V := Variety.point k)
        ⟨W₁.toEllipticCurveGeom, s₁⟩
        ⟨((legendreCurve k).map ev).toEllipticCurveGeom, (ModuliProblem.gamma _ 2).map bc.op (legPair h2).2⟩ := by
    intro W₁ _ hW₁ s₁ h0₁ h1₁ hs₁ hs₂
    subst hW₁
    refine ⟨𝟙 _, rfl, ?_⟩
    rw [op_id, Functor.map_id_apply]
    apply (ModuliProblem.gammaEquiv _).injective
    apply Subtype.ext
    refine (ModuliProblem.gammaEquiv_map (N := 2) bc (legPair h2).2).trans ?_
    apply hom_ext_two
    · refine Eq.trans ?_ hs₁.symm
      exact (congrArg (EllipticCurveGeom.pointsPullback bc.isPullback bc.zero_total) (fam_legPair_one h2)).trans
        ((pointsPullback_bcHom _ (legendreCurve k) ev _ hg legendre_eq_zero).trans
          (affinePointHom_congr _ _ _ (map_zero ev) (map_zero ev)))
    · refine Eq.trans ?_ hs₂.symm
      exact (congrArg (EllipticCurveGeom.pointsPullback bc.isPullback bc.zero_total) (fam_legPair_two h2)).trans
        ((pointsPullback_bcHom _ (legendreCurve k) ev _ hg legendre_eq_one).trans
          (affinePointHom_congr _ _ _ (map_one ev) (map_zero ev)))
  have hW0 : W.toAffine.Equation ((C.u : k) ^ 2 * 0 + C.r) ((C.u : k) ^ 3 * 0 + (C.u : k) ^ 2 * C.s * 0 + C.t) :=
    (Affine.variableChange_equation W C 0 0).mpr hC0
  have hW1 : W.toAffine.Equation ((C.u : k) ^ 2 * 1 + C.r) ((C.u : k) ^ 3 * 0 + (C.u : k) ^ 2 * C.s * 1 + C.t) :=
    (Affine.variableChange_equation W C 1 0).mpr hC1
  have hxC₁ : (ModuliProblem.gammaEquiv _ xC.2).1 e₁ = affinePointHom (C • W) hC0 := by
    refine (congrArg (fun f ↦ f e₁) (ModuliProblem.gammaEquiv_map (N := 2) vc xW.2)).trans ?_
    rw [MonoidHom.comp_apply]
    change EllipticCurveGeom.pointsPullback _ _ (fam xW e₁) = _
    rw [hφ₁, affinePointHom_congr W h₁ hW0 (by simp [C]) (by simp [C])]
    exact pointsPullback_vcHom _ W C hC0
  have hxC₂ : (ModuliProblem.gammaEquiv _ xC.2).1 e₂ = affinePointHom (C • W) hC1 := by
    refine (congrArg (fun f ↦ f e₂) (ModuliProblem.gammaEquiv_map (N := 2) vc xW.2)).trans ?_
    rw [MonoidHom.comp_apply]
    change EllipticCurveGeom.pointsPullback _ _ (fam xW e₂) = _
    rw [hφ₂, affinePointHom_congr W h₂ hW1 (by simp only [C, Units.val_mk0, _root_.mul_one]; rw [hu0]; ring)
      (by simp only [C, Units.val_mk0, mul_zero, _root_.mul_one, zero_add]
          linear_combination -((-W.a₁ * i) * hu0 + i * hy₁ - i * hy₂ - (y₁ - y₂) * hh))]
    exact pointsPullback_vcHom _ W C hC1
  have r4 := key (C • W) hCW xC.2 hC0 hC1 hxC₁ hxC₂
  exact LevelPair.rel_trans (LevelPair.rel_symm r1) (LevelPair.rel_trans (LevelPair.rel_symm r2)
    (LevelPair.rel_trans r4 r3))

/-! ### The solution -/

/-- $\alpha$: the $\lambda$ of a class of pairs over $k$. -/
def alpha : (levelFunctor (ModuliProblem.gamma (Spec (CommRingCat.of k)) 2)).obj (op (Variety.point k)) →
    (Variety.point k ⟶ lamLine k) :=
  Quotient.lift (lamMor h2) fun _ _ h ↦ lamMor_rel h2 h

theorem alpha_bijective : Function.Bijective (alpha h2) := by
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h x =>
    induction b using Quotient.inductionOn with
    | h y =>
    change lamMor h2 x = lamMor h2 y at hab
    apply Quotient.sound
    have r1 := rel_pull_legendre h2 x
    have r2 := rel_pull_legendre h2 y
    rw [hab] at r1
    exact LevelPair.rel_trans r1 (LevelPair.rel_symm r2)
  · intro t
    exact ⟨⟦LevelPair.pull t (legPair h2)⟧, lamMor_pull_legendre h2 t⟩

/-- **The Legendre line solves the moduli problem of elliptic curves with a level-two structure.** -/
theorem isModuliSolution_two :
    IsModuliSolution (levelFunctor (ModuliProblem.gamma (Spec (CommRingCat.of k)) 2)) (lamLine k)
      (Equiv.ofBijective _ (alpha_bijective h2)) := by
  refine ⟨fun T f ↦ ?_, fun Z β hβ ↦ ?_⟩
  · induction f using Quotient.inductionOn with
    | h x => exact ⟨lamMor h2 x, fun t ↦ (lamMor_pull h2 t x).symm⟩
  · obtain ⟨ψ, hψ⟩ := hβ (lamLine k) ⟦legPair h2⟧
    refine ⟨ψ, fun v ↦ ?_⟩
    rw [hψ v]
    congr 1
    rw [Equiv.eq_symm_apply]
    exact lamMor_pull_legendre h2 v

end ModularFormsKB.Milne.LevelTwoModuli

namespace ModularFormsKB.Milne

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Milne, Theorem 8.8 for $N = 2$**, unconditionally: the Legendre line
$\mathbb A^1 \smallsetminus \{0, 1\}$ with $\alpha(E, t) = \lambda$ solves $\mathcal E_2$ (a coarse solution:
`Ch8Counterexample.not_exists_isFineModuliSolution`). -/
theorem levelModuliSolution_two : LevelModuliSolution k 2 := by
  refine ⟨fun hN ζ hζ ↦ ?_⟩
  have hζ' : ζ = -1 := hζ.eq_neg_one_of_two_right
  subst hζ'
  exact ⟨LevelTwoModuli.lamLine k, _, isModuliSolution_of_natIso
    (levelNFunctorIsoOfForall hN (-1) (fun _ x ↦ Ch8Counterexample.hasWeilPairing_two hN x))
    (LevelTwoModuli.isModuliSolution_two hN)⟩

/-- **Milne, Example 8.9 as corrected** (`LegendreCoarseModuli`), unconditionally: the Legendre line is a (coarse)
solution of $\mathcal E_2$ over an algebraically closed field of characteristic $0$. -/
theorem legendreCoarseModuli [CharZero k] : LegendreCoarseModuli k := by
  have h2 : ((2 : ℕ) : k) ≠ 0 := by norm_num
  exact ⟨⟨LevelTwoModuli.lamLine k, Iso.refl _, Category.id_comp _, _, isModuliSolution_of_natIso
    (levelNFunctorIsoOfForall h2 (-1) (fun _ x ↦ Ch8Counterexample.hasWeilPairing_two h2 x))
    (LevelTwoModuli.isModuliSolution_two h2)⟩⟩

end ModularFormsKB.Milne
