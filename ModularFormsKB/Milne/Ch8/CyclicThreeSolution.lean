import ModularFormsKB.Milne.Ch8.CyclicThreeModuli

/-!
# Milne, Theorem 8.6 for $N = 3$: normal forms, bijectivity and universality

Continuation of `CyclicThreeModuli`: every pair over $k$ is isomorphic to the pair of $(0, 0)$ on the normal form
$y^2 + sxy + y = x^3$ (`exists_rel_normal`), whose invariant is $s^3$ (`alpha_kPair_wc3`); $s$ and $s'$ with
$s^3 = s'^3$ give isomorphic pairs (`rel_normal_mul`), so $\alpha$ is bijective (`alpha_bijective`). Universality
(`alpha_universal`) and the final statement `cyclicModuliSolution_three` follow as for $N = 2$.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite WeierstrassCurve TauCeti.AlgebraicGeometry MonoidalCategory
  ModularFormsKB.Milne.LevelTwoChart ModularFormsKB.Milne.CyclicThree MonObj TauCeti Polynomial

noncomputable section

namespace ModularFormsKB.Milne.CyclicThreeModuli

open Ch8Counterexample LevelTwoModuli CyclicTwoModuli

variable {k : Type u} [Field k] [IsAlgClosed k]

/-! ### Algebra of the normal form -/

omit [IsAlgClosed k] in
/-- **The $3$-division polynomial under a change of variables**: $u^8 \Psi_3^{C \cdot W}(x) = \Psi_3^W(u^2x + r)$. -/
theorem psi3_variableChange {R : Type u} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R) (x : R) :
    (C.u : R) ^ 8 * psi3 (C • W) x = psi3 W ((C.u : R) ^ 2 * x + C.r) := by
  set v : R := ((C.u⁻¹ : Rˣ) : R)
  set u : R := (C.u : R)
  have hv : v * u = 1 := by simp [v, u]
  have h2 : u ^ 2 * v ^ 2 = 1 := by linear_combination (v * u + 1) * hv
  have h4 : u ^ 4 * v ^ 4 = 1 := by linear_combination ((v * u) ^ 2 + 1) * h2
  have h6 : u ^ 6 * v ^ 6 = 1 := by linear_combination ((v * u) ^ 4 + (v * u) ^ 2 + 1) * h2
  have h8 : u ^ 8 * v ^ 8 = 1 := by linear_combination ((v * u) ^ 4 + 1) * h4
  simp only [psi3, variableChange_b₂, variableChange_b₄, variableChange_b₆, variableChange_b₈]
  linear_combination u ^ 6 * x ^ 3 * (W.b₂ + 12 * C.r) * h2 +
    3 * u ^ 4 * x ^ 2 * (W.b₄ + C.r * W.b₂ + 6 * C.r ^ 2) * h4 +
    3 * u ^ 2 * x * (W.b₆ + 2 * C.r * W.b₄ + C.r ^ 2 * W.b₂ + 4 * C.r ^ 3) * h6 +
    (W.b₈ + 3 * C.r * W.b₆ + 3 * C.r ^ 2 * W.b₄ + C.r ^ 3 * W.b₂ + 3 * C.r ^ 4) * h8

omit [IsAlgClosed k] in
theorem psi3_variableChange_eq_zero {R : Type u} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)
    {x : R} (h : psi3 W ((C.u : R) ^ 2 * x + C.r) = 0) : psi3 (C • W) x = 0 := by
  have e := psi3_variableChange W C x
  rw [h] at e
  exact ((Units.isUnit C.u).pow 8).mul_right_eq_zero.mp e

omit [IsAlgClosed k] in
/-- A point of exact order three, read on the Weierstrass curve: $\Psi_3(x) = 0$. -/
theorem psi3_of_pow_three {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] {x y : R}
    (h : W.toAffine.Equation x y) (hP : affinePointHom W h ^ 3 = 1) : psi3 W x = 0 := by
  have hm : (toEllipticCurveGeomIso W).inv ≫ (W.toEllipticCurveGeom.mulBy 3).left =
      W.projModelMulBy 3 ≫ (toEllipticCurveGeomIso W).inv := by
    rw [projModelMulBy_eq]; simp
  have h1 := (EllipticCurveGeom.zpow_eq_one_iff_left_comp_mulBy_left _ (affinePointHom W h) 3).mp
    (by exact_mod_cast hP)
  rw [affinePointHom_left, Category.assoc, hm] at h1
  have h2 := congrArg (· ≫ (toEllipticCurveGeomIso W).hom) h1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_toEllipticCurveGeomIso_hom] at h2
  exact psi3_of_mulBy h h2

omit [IsAlgClosed k] in
/-- The Weierstrass curve $y^2 + a_1xy + a_3y = x^3$. -/
abbrev wc3 {R : Type u} [CommRing R] (a₁ a₃ : R) : WeierstrassCurve R := ⟨a₁, 0, a₃, 0, 0⟩

omit [IsAlgClosed k] in
theorem wc3_Δ {R : Type u} [CommRing R] (a₁ a₃ : R) : (wc3 a₁ a₃).Δ = a₃ ^ 3 * (a₁ ^ 3 - 27 * a₃) := by
  simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]
  ring

omit [IsAlgClosed k] in
theorem wc3_equation {R : Type u} [CommRing R] (a₁ a₃ : R) : (wc3 a₁ a₃).toAffine.Equation 0 0 := by
  rw [Affine.equation_iff]
  simp

omit [IsAlgClosed k] in
theorem wc3_psi3 {R : Type u} [CommRing R] (a₁ a₃ : R) : psi3 (wc3 a₁ a₃) 0 = 0 := by
  simp only [psi3, b₂, b₄, b₆, b₈]
  ring

omit [IsAlgClosed k] in
theorem inv3_wc3 {R : Type u} [CommRing R] (a₁ a₃ : R) (hC : IsUnit (coeffC (wc3 a₁ a₃) 0)) (l : R)
    (hl : l * a₃ ^ 2 = a₁ ^ 3 * a₃) : inv3 (wc3 a₁ a₃) hC = l := by
  rw [inv3_eq_iff]
  simp only [CyclicTwo.coeffA, CyclicTwo.coeffB, coeffC, b₂, b₄, b₆]
  linear_combination hl

omit [IsAlgClosed k] in
theorem isElliptic_wc3 {s : k} (hs : s ^ 3 - 27 ≠ 0) : (wc3 s 1).IsElliptic := by
  refine ⟨?_⟩
  rw [wc3_Δ]
  refine IsUnit.mk0 _ ?_
  simpa using hs

theorem linePt_congr {l l' : k} (h : l = l') (hl : (tPoly (k := k)).eval l ≠ 0)
    (hl' : (tPoly (k := k)).eval l' ≠ 0) :
    linePt (tPoly (k := k)) tPoly_ne_zero l hl = linePt tPoly tPoly_ne_zero l' hl' := by
  subst h; rfl

theorem linePt_inj {l l' : k} {hl : (tPoly (k := k)).eval l ≠ 0} {hl' : (tPoly (k := k)).eval l' ≠ 0}
    (h : linePt (tPoly (k := k)) tPoly_ne_zero l hl = linePt tPoly tPoly_ne_zero l' hl') : l = l' := by
  have h1 := congrArg (fun v ↦ v.hom.left) h
  change Spec.map (CommRingCat.ofHom (evalAwayAlg _ l hl).toRingHom) =
    Spec.map (CommRingCat.ofHom (evalAwayAlg _ l' hl').toRingHom) at h1
  have h3 := congrArg (fun φ : CommRingCat.of (TRing k) ⟶ CommRingCat.of k ↦ φ.hom (algebraMap k[X] _ X))
    (Spec.map_injective h1)
  simpa [evalAwayAlg_algebraMap] using h3

variable (h3 : ((3 : ℕ) : k) ≠ 0)
include h3

/-! ### Isomorphisms of Weierstrass pairs -/

theorem kPair_congr_pt (W : WeierstrassCurve k) [W.IsElliptic] {x y x' y' : k}
    (h : W.toAffine.Equation x y) (h' : W.toAffine.Equation x' y') (h3x : psi3 W x = 0)
    (h3x' : psi3 W x' = 0) (hx : x = x') (hyy : y = y') :
    kPair h3 W h h3x = kPair h3 W h' h3x' := by
  subst hx hyy; rfl

theorem rel_kPair_congr {W W' : WeierstrassCurve k} (hW : W = W') [W.IsElliptic] [W'.IsElliptic] {x y : k}
    (h : W.toAffine.Equation x y) (h' : W'.toAffine.Equation x y) (h3x : psi3 W x = 0)
    (h3x' : psi3 W' x = 0) : LevelPair.Rel (kPair h3 W h h3x) (kPair h3 W' h' h3x') := by
  subst hW
  exact LevelPair.rel_refl _

/-- **A change of variables gives isomorphic pairs.** -/
theorem rel_vc (W : WeierstrassCurve k) [W.IsElliptic] (C : VariableChange k) {x y : k}
    (h' : (C • W).toAffine.Equation x y) (h3x' : psi3 (C • W) x = 0)
    (h3x : psi3 W ((C.u : k) ^ 2 * x + C.r) = 0) :
    LevelPair.Rel (kPair h3 (C • W) h' h3x')
      (kPair h3 W ((Affine.variableChange_equation W C x y).mpr h') h3x) := by
  let vc : (Variety.point k).ellObj (C • W).toEllipticCurveGeom ⟶ (Variety.point k).ellObj W.toEllipticCurveGeom :=
    vcHom (𝟙 (Spec (CommRingCat.of k))) W C
  have hP := isOfExactOrder_affine h3 W ((Affine.variableChange_equation W C x y).mpr h') h3x
  have hb : vc.base = 𝟙 _ := rfl
  have r := rel_pairOf_hom vc hb (affinePointHom W ((Affine.variableChange_equation W C x y).mpr h')) hP
  have e := pairOf_congr (Variety.point k) (C • W).toEllipticCurveGeom (hP.pointsPullback vc.isPullback vc.zero_total)
    (isOfExactOrder_affine h3 (C • W) h' h3x') (pointsPullback_vcHom _ W C h')
  rw [e] at r
  exact r

omit h3 in
/-- A pair over $k$ is isomorphic to the pair of a generator. -/
theorem exists_rel_gen (x : Pair (Variety.point k)) :
    ∃ (E : EllipticCurveGeom (Spec (CommRingCat.of k))) (P : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶
      Over.mk E.structureMap) (hP : E.IsOfExactOrder P 3),
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
    (P : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Over.mk E.structureMap) (hP : E.IsOfExactOrder P 3) :
    ∃ (W : WeierstrassCurve k) (_ : W.IsElliptic) (x y : k) (h : W.toAffine.Equation x y)
      (h3x : psi3 W x = 0), LevelPair.Rel (pairOf (Variety.point k) E P hP) (kPair h3 W h h3x) := by
  obtain ⟨W, hW, e0, he0, hz⟩ := E.exists_iso_toEllipticCurveGeom
  let a : (Variety.point k).ellObj W.toEllipticCurveGeom ⟶ (Variety.point k).ellObj E := isoHom _ e0 he0 hz
  have hb : a.base = 𝟙 _ := rfl
  have r := rel_pairOf_hom a hb P hP
  have hP' := hP.pointsPullback a.isPullback a.zero_total
  obtain ⟨x, y, h, hxy⟩ := exists_affinePointHom _ (ne_zero_of_order_three (𝟙 _) h3 hP')
  have h3x : psi3 W x = 0 := psi3_of_pow_three W h (by rw [← hxy]; exact hP'.pow_eq_one)
  refine ⟨W, hW, x, y, h, h3x, LevelPair.rel_symm ?_⟩
  have e := pairOf_congr (Variety.point k) W.toEllipticCurveGeom hP' (isOfExactOrder_affine h3 W h h3x) hxy
  rw [e] at r
  exact r

/-- **Moving the point to $(0, 0)$ and its tangent to $y = 0$.** -/
theorem exists_rel_wc3 (W : WeierstrassCurve k) [W.IsElliptic] {x₀ y₀ : k} (h : W.toAffine.Equation x₀ y₀)
    (h3x : psi3 W x₀ = 0) :
    ∃ (a₁ a₃ : k) (_ : (wc3 a₁ a₃).IsElliptic), LevelPair.Rel (kPair h3 W h h3x)
      (kPair h3 (wc3 a₁ a₃) (wc3_equation a₁ a₃) (wc3_psi3 a₁ a₃)) := by
  -- move the point to `(0, 0)`
  let C₀ : VariableChange k := ⟨1, x₀, 0, y₀⟩
  have h0 : (C₀ • W).toAffine.Equation 0 0 := by
    rw [← Affine.variableChange_equation]
    convert h using 2 <;> simp [C₀]
  have hp0 : psi3 (C₀ • W) 0 = 0 := psi3_variableChange_eq_zero W C₀ (by simpa [C₀] using h3x)
  have r3 := rel_vc h3 W C₀ h0 hp0 (by simpa [C₀] using h3x)
  rw [kPair_congr_pt h3 W _ h _ h3x (by simp [C₀]) (by simp [C₀])] at r3
  set W₁ := C₀ • W with hW₁
  have ha₆ : W₁.a₆ = 0 := by
    have := h0
    rw [Affine.equation_iff] at this
    linear_combination -this
  have ha₃ : W₁.a₃ ≠ 0 := by
    intro ha
    have hC := isUnit_coeffC_of_psi3 h0 hp0
    simp only [coeffC, b₂, b₄, b₆, ha, ha₆] at hC
    simp at hC
  -- make the tangent `y = 0`
  let C₁ : VariableChange k := ⟨1, 0, W₁.a₄ / W₁.a₃, 0⟩
  have h1 : (C₁ • W₁).toAffine.Equation 0 0 := by
    rw [← Affine.variableChange_equation]
    convert h0 using 2 <;> simp [C₁]
  have hp1 : psi3 (C₁ • W₁) 0 = 0 := psi3_variableChange_eq_zero W₁ C₁ (by simpa [C₁] using hp0)
  have r4 := rel_vc h3 W₁ C₁ h1 hp1 (by simpa [C₁] using hp0)
  rw [kPair_congr_pt h3 W₁ _ h0 _ hp0 (by simp [C₁]) (by simp [C₁])] at r4
  set W₂ := C₁ • W₁ with hW₂
  have hb₃ : W₂.a₃ = W₁.a₃ := by
    rw [hW₂, variableChange_a₃]; simp [C₁]
  have hb₄ : W₂.a₄ = 0 := by
    rw [hW₂, variableChange_a₄]
    simp only [C₁, inv_one, Units.val_one, one_pow, _root_.one_mul, mul_zero, zero_mul, add_zero, sub_zero]
    field_simp
    ring
  have hb₆ : W₂.a₆ = 0 := by
    rw [hW₂, variableChange_a₆]; simp [C₁, ha₆]
  have hb₂ : W₂.a₂ = 0 := by
    have e := hp1
    simp only [psi3, b₂, b₄, b₆, b₈, hb₄, hb₆] at e
    have e' : W₂.a₂ * W₂.a₃ ^ 2 = 0 := by linear_combination e
    rw [hb₃] at e'
    exact (mul_eq_zero.mp e').resolve_right (pow_ne_zero 2 ha₃)
  have hW₂eq : W₂ = wc3 W₂.a₁ W₂.a₃ := by
    ext
    exacts [rfl, hb₂, rfl, hb₄, hb₆]
  haveI : (wc3 W₂.a₁ W₂.a₃).IsElliptic := by rw [← hW₂eq]; infer_instance
  refine ⟨W₂.a₁, W₂.a₃, inferInstance, ?_⟩
  have r5 := rel_kPair_congr h3 hW₂eq h1 (wc3_equation _ _) hp1 (wc3_psi3 _ _)
  exact LevelPair.rel_trans (LevelPair.rel_symm r3) (LevelPair.rel_trans (LevelPair.rel_symm r4) r5)

/-- **Scaling** $a_3$ to $1$. -/
theorem exists_rel_wc3_one {a₁ a₃ : k} [(wc3 a₁ a₃).IsElliptic] :
    ∃ (s : k) (hs : s ^ 3 - 27 ≠ 0), LevelPair.Rel
      (kPair h3 (wc3 a₁ a₃) (wc3_equation a₁ a₃) (wc3_psi3 a₁ a₃))
      (haveI := isElliptic_wc3 hs; kPair h3 (wc3 s 1) (wc3_equation s 1) (wc3_psi3 s 1)) := by
  have ha₃ : a₃ ≠ 0 := by
    intro ha
    have hΔ := (wc3 a₁ a₃).isUnit_Δ
    rw [wc3_Δ, ha] at hΔ
    simp at hΔ
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq a₃ (by norm_num : 0 < 3)
  have hu0 : u ≠ 0 := by rintro rfl; exact ha₃ (by rw [← hu]; ring)
  let C : VariableChange k := ⟨Units.mk0 u hu0, 0, 0, 0⟩
  set s := u⁻¹ * a₁ with hsdef
  have hW : C • wc3 a₁ a₃ = wc3 s 1 := by
    ext
    · rw [variableChange_a₁]; simp [C, hsdef]
    · rw [variableChange_a₂]; simp [C]
    · rw [variableChange_a₃]
      simp only [C, Units.val_inv_eq_inv_val, Units.val_mk0, mul_zero, zero_mul, add_zero]
      rw [← hu, inv_pow]
      field_simp
    · rw [variableChange_a₄]; simp [C]
    · rw [variableChange_a₆]; simp [C]
  have hs : s ^ 3 - 27 ≠ 0 := by
    intro hs
    have hΔ := (C • wc3 a₁ a₃).isUnit_Δ
    rw [hW, wc3_Δ] at hΔ
    simp [hs] at hΔ
  haveI := isElliptic_wc3 hs
  have h1 : (C • wc3 a₁ a₃).toAffine.Equation 0 0 := by rw [hW]; exact wc3_equation s 1
  have hp1 : psi3 (C • wc3 a₁ a₃) 0 = 0 := by rw [hW]; exact wc3_psi3 s 1
  have r := rel_vc h3 (wc3 a₁ a₃) C h1 hp1 (by simpa [C] using wc3_psi3 a₁ a₃)
  rw [kPair_congr_pt h3 (wc3 a₁ a₃) _ (wc3_equation a₁ a₃) _ (wc3_psi3 a₁ a₃) (by simp [C]) (by simp [C])] at r
  refine ⟨s, hs, LevelPair.rel_trans (LevelPair.rel_symm r) ?_⟩
  exact rel_kPair_congr h3 hW h1 (wc3_equation s 1) hp1 (wc3_psi3 s 1)

/-- **Normal form**: every pair over $k$ is isomorphic to the pair of $(0, 0)$ on $y^2 + sxy + y = x^3$. -/
theorem exists_rel_normal (x : Pair (Variety.point k)) :
    ∃ (s : k) (hs : s ^ 3 - 27 ≠ 0), LevelPair.Rel x
      (haveI := isElliptic_wc3 hs; kPair h3 (wc3 s 1) (wc3_equation s 1) (wc3_psi3 s 1)) := by
  obtain ⟨E, P, hP, r1⟩ := exists_rel_gen x
  obtain ⟨W, hW, x₀, y₀, h, h3x, r2⟩ := exists_rel_weierstrass h3 E P hP
  obtain ⟨a₁, a₃, ha, r3⟩ := exists_rel_wc3 h3 W h h3x
  obtain ⟨s, hs, r4⟩ := exists_rel_wc3_one h3 (a₁ := a₁) (a₃ := a₃)
  exact ⟨s, hs, LevelPair.rel_trans r1 (LevelPair.rel_trans r2 (LevelPair.rel_trans r3 r4))⟩

/-! ### Bijectivity of $\alpha$ -/

omit h3 in
theorem eval_tPoly_cube_ne_zero {s : k} (hs : s ^ 3 - 27 ≠ 0) : (tPoly (k := k)).eval (s ^ 3) ≠ 0 := by
  simpa using hs

theorem alpha_kPair_wc3 {s : k} (hs : s ^ 3 - 27 ≠ 0) :
    haveI := isElliptic_wc3 hs
    alpha h3 ⟦kPair h3 (wc3 s 1) (wc3_equation s 1) (wc3_psi3 s 1)⟧ =
      linePt (tPoly (k := k)) tPoly_ne_zero (s ^ 3) (eval_tPoly_cube_ne_zero hs) := by
  haveI := isElliptic_wc3 hs
  exact (cycMor_kPair_left h3 (wc3 s 1) (wc3_equation s 1) (wc3_psi3 s 1)).trans
    (linePt_congr (inv3_wc3 _ _ _ _ (by ring)) _ _)

/-- **The normal forms of $s$ and $s'$ with $s^3 = s'^3$ are isomorphic.** -/
theorem rel_normal_mul {s s' : k} (hs : s ^ 3 - 27 ≠ 0) (hs' : s' ^ 3 - 27 ≠ 0) (hss : s' ^ 3 = s ^ 3) :
    haveI := isElliptic_wc3 hs; haveI := isElliptic_wc3 hs'
    LevelPair.Rel (kPair h3 (wc3 s' 1) (wc3_equation s' 1) (wc3_psi3 s' 1))
      (kPair h3 (wc3 s 1) (wc3_equation s 1) (wc3_psi3 s 1)) := by
  haveI := isElliptic_wc3 hs; haveI := isElliptic_wc3 hs'
  by_cases hs0 : s = 0
  · have hs'0 : s' = 0 := by subst hs0; simpa using hss
    subst hs0 hs'0
    exact LevelPair.rel_refl _
  have hs'0 : s' ≠ 0 := by rintro rfl; apply hs0; simpa using hss.symm
  set u := s / s' with hudef
  have hu0 : u ≠ 0 := div_ne_zero hs0 hs'0
  have hu3 : u ^ 3 = 1 := by rw [hudef, div_pow, ← hss, div_self (pow_ne_zero 3 hs'0)]
  let C : VariableChange k := ⟨Units.mk0 u hu0, 0, 0, 0⟩
  have hW : C • wc3 s 1 = wc3 s' 1 := by
    ext
    · rw [variableChange_a₁]
      simp only [C, Units.val_inv_eq_inv_val, Units.val_mk0, mul_zero, add_zero, hudef]
      field_simp
    · rw [variableChange_a₂]; simp [C]
    · rw [variableChange_a₃]
      simp only [C, Units.val_inv_eq_inv_val, Units.val_mk0, mul_zero, zero_mul, add_zero, inv_pow, hu3]
      simp
    · rw [variableChange_a₄]; simp [C]
    · rw [variableChange_a₆]; simp [C]
  have h1 : (C • wc3 s 1).toAffine.Equation 0 0 := by rw [hW]; exact wc3_equation s' 1
  have hp1 : psi3 (C • wc3 s 1) 0 = 0 := by rw [hW]; exact wc3_psi3 s' 1
  have r := rel_vc h3 (wc3 s 1) C h1 hp1 (by simpa [C] using wc3_psi3 s 1)
  rw [kPair_congr_pt h3 (wc3 s 1) _ (wc3_equation s 1) _ (wc3_psi3 s 1) (by simp [C]) (by simp [C])] at r
  exact LevelPair.rel_trans (LevelPair.rel_symm (rel_kPair_congr h3 hW h1 (wc3_equation s' 1) hp1
    (wc3_psi3 s' 1))) r

theorem alpha_bijective : Function.Bijective (alpha h3) := by
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h x =>
    induction b using Quotient.inductionOn with
    | h y =>
    obtain ⟨s, hs, r1⟩ := exists_rel_normal h3 x
    obtain ⟨s', hs', r2⟩ := exists_rel_normal h3 y
    have e1 : alpha h3 ⟦x⟧ = _ := (cycMor_rel h3 r1).trans (alpha_kPair_wc3 h3 hs)
    have e2 : alpha h3 ⟦y⟧ = _ := (cycMor_rel h3 r2).trans (alpha_kPair_wc3 h3 hs')
    have hss := linePt_inj (e1.symm.trans (hab.trans e2))
    apply Quotient.sound
    exact LevelPair.rel_trans r1 (LevelPair.rel_trans (rel_normal_mul h3 hs' hs hss) (LevelPair.rel_symm r2))
  · intro v
    obtain ⟨w, hw, rfl⟩ := exists_linePt tPoly_ne_zero v
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq w (by norm_num : 0 < 3)
    have hs : r ^ 3 - 27 ≠ 0 := by rw [hr]; simpa using hw
    haveI := isElliptic_wc3 hs
    exact ⟨⟦kPair h3 (wc3 r 1) (wc3_equation r 1) (wc3_psi3 r 1)⟧,
      (alpha_kPair_wc3 h3 hs).trans (linePt_congr hr _ _)⟩

/-! ### Universality -/

section Universal

variable {Z : Variety k} (β : (cyclicFunctor k 3).obj (op (Variety.point k)) → (Variety.point k ⟶ Z))
  (hβ : ∀ (T : Variety k) (f : (cyclicFunctor k 3).obj (op T)),
    ∃ φ : T ⟶ Z, ∀ t : Variety.point k ⟶ T, t ≫ φ = β ((cyclicFunctor k 3).map t.op f))

omit [IsAlgClosed k] in
theorem eval_tPoly_zero_ne_zero : (tPoly (k := k)).eval 0 ≠ 0 := by
  have : (27 : k) = ((3 : ℕ) : k) ^ 3 := by norm_num
  simp only [eval_sub, eval_X, eval_C, zero_sub, ne_eq, neg_eq_zero, this]
  exact pow_ne_zero 3 h3

open Classical in
/-- $\beta \circ \alpha^{-1}$ as a function of the coordinate. -/
def bfun (w : k) : Variety.point k ⟶ Z :=
  if hw : (tPoly (k := k)).eval w ≠ 0 then
    β ((Equiv.ofBijective _ (alpha_bijective h3)).symm (linePt tPoly tPoly_ne_zero w hw))
  else β ((Equiv.ofBijective _ (alpha_bijective h3)).symm
    (linePt tPoly tPoly_ne_zero 0 (eval_tPoly_zero_ne_zero h3)))

include hβ in
/-- A Weierstrass family gives a regular map with the values of $\beta \circ \alpha^{-1}$ at its invariants. -/
theorem exists_hom_wPair (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (W : WeierstrassCurve R) [W.IsElliptic] {x y : R} (h : W.toAffine.Equation x y) (h3x : psi3 W x = 0) :
    ∃ hh : domVariety (k := k) R ⟶ Z, ∀ τ : R →ₐ[k] k,
      algPoint τ ≫ hh = bfun h3 β (τ (inv3 W (isUnit_coeffC_of_psi3 h h3x))) := by
  obtain ⟨φ, hφ⟩ := hβ _ ⟦wPair h3 R W h h3x⟧
  refine ⟨φ, fun τ ↦ (hφ (algPoint τ)).trans ?_⟩
  have e := cycMor_pull_wPair h3 R W h h3x τ
  rw [bfun, dif_pos (eval_tPoly_ne_zero (by
    have := (isUnit_inv_weierstrass_sub W h h3x).map τ
    rwa [map_sub, map_ofNat] at this))]
  congr 1
  rw [Equiv.eq_symm_apply]
  exact e

/-- The polynomial $t(t - 27)$ of the seed chart. -/
abbrev seed1 : k[X] := X * (X - C 27)

omit [IsAlgClosed k] h3 in
theorem seed1_ne_zero : (seed1 : k[X]) ≠ 0 := mul_ne_zero X_ne_zero (X_sub_C_ne_zero 27)

/-- The polynomial $s^3 - 27$. -/
abbrev seed2 : k[X] := X ^ 3 - C 27

omit [IsAlgClosed k] h3 in
theorem seed2_ne_zero : (seed2 : k[X]) ≠ 0 := by
  intro h
  have := congrArg (Polynomial.natDegree) h
  rw [natDegree_sub_C, natDegree_X_pow] at this
  simp at this

include hβ in
/-- **The seed chart**: the family $y^2 + txy + t^2y = x^3$ over $D(t(t - 27))$. -/
theorem nonempty_seed : Nonempty (LineChart Z (bfun h3 β)) := by
  haveI := isDomain_away k (seed1_ne_zero (k := k))
  set t : Localization.Away (seed1 : k[X]) := algebraMap k[X] _ X
  have ht : IsUnit t := by
    have := isUnit_algebraMap_of_dvd (k := k) (dvd_mul_right X (X - C 27)) 1
    rwa [pow_one] at this
  have ht27 : IsUnit (t - 27) := by
    have := isUnit_algebraMap_of_dvd (k := k) (dvd_mul_left (X - C 27) X) 1
    rwa [pow_one, map_sub, show (C 27 : k[X]) = 27 from map_ofNat C 27, map_ofNat] at this
  haveI : (wc3 t (t ^ 2)).IsElliptic := ⟨by
    rw [wc3_Δ, show (t ^ 2) ^ 3 * (t ^ 3 - 27 * t ^ 2) = t ^ 8 * (t - 27) by ring]
    exact (ht.pow 8).mul ht27⟩
  obtain ⟨hh, hhv⟩ := exists_hom_wPair h3 β hβ _ (wc3 t (t ^ 2)) (wc3_equation t (t ^ 2)) (wc3_psi3 t (t ^ 2))
  refine ⟨⟨seed1, seed1_ne_zero, hh, fun w hw ↦ ?_⟩⟩
  have := hhv (evalAwayAlg _ w hw)
  rw [inv3_wc3 _ _ _ t (by ring), evalAwayAlg_algebraMap, eval_X] at this
  exact this

include hβ in
/-- **Theorem 8.6 ($N = 3$), condition (b).** -/
theorem alpha_universal :
    ∃ ψ : tLine k ⟶ Z, ∀ v : Variety.point k ⟶ tLine k,
      v ≫ ψ = β ((Equiv.ofBijective _ (alpha_bijective h3)).symm v) := by
  classical
  obtain ⟨c₁⟩ := nonempty_seed h3 β hβ
  haveI := isDomain_away k (seed2_ne_zero (k := k))
  set σ : Localization.Away (seed2 : k[X]) := algebraMap k[X] _ X
  have hσ27 : IsUnit (σ ^ 3 - 27) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (seed2 : k[X])) (seed2 : k[X])
    rwa [map_sub, map_pow, show (C 27 : k[X]) = 27 from map_ofNat C 27, map_ofNat] at this
  haveI : (wc3 σ 1).IsElliptic := ⟨by
    rw [wc3_Δ]
    convert hσ27 using 1
    ring⟩
  obtain ⟨hh, hhv⟩ := exists_hom_wPair h3 β hβ _ (wc3 σ 1) (wc3_equation σ 1) (wc3_psi3 σ 1)
  let π : k[X] →ₐ[k] Localization.Away (seed2 : k[X]) := Polynomial.aeval (σ ^ 3)
  have hπX : π X = σ ^ 3 := aeval_X _
  have hπ : Function.Injective π := by
    have hπ' : π = (IsScalarTower.toAlgHom k k[X] (Localization.Away (seed2 : k[X]))).comp (expand k 3) := by
      apply Polynomial.algHom_ext
      simp [π, σ]
    rw [hπ']
    exact (IsLocalization.injective (Localization.Away (seed2 : k[X]))
      (powers_le_nonZeroDivisors_of_noZeroDivisors seed2_ne_zero)).comp (expand_injective (by norm_num))
  have hhv' : ∀ τ : Localization.Away (seed2 : k[X]) →ₐ[k] k, algPoint τ ≫ hh = bfun h3 β (τ (π X)) := by
    intro τ
    rw [hhv, hπX, inv3_wc3 _ _ _ (σ ^ 3) (by ring)]
  have hcov : ∀ v : k, (tPoly (k := k)).eval v ≠ 0 → ∃ c : LineChart Z (bfun h3 β), c.s.eval v ≠ 0 := by
    intro v hv
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq v (by norm_num : 0 < 3)
    have hr27 : (seed2 : k[X]).eval r ≠ 0 := by simpa [hr] using hv
    refine exists_chart_at π hπ hh hhv' c₁ v (evalAwayAlg _ r hr27) ?_
    rw [hπX, map_pow, evalAwayAlg_algebraMap, eval_X, hr]
  obtain ⟨ψ, hψ⟩ := exists_hom_of_charts_away tPoly_ne_zero hcov
  refine ⟨ψ, fun v ↦ ?_⟩
  obtain ⟨w, hw, rfl⟩ := exists_linePt tPoly_ne_zero v
  rw [hψ, bfun, dif_pos hw]

end Universal

/-- **The line $\mathbb A^1 \smallsetminus \{27\}$ solves the moduli problem $\mathcal E_{0,3}$.** -/
theorem isModuliSolution_three :
    IsModuliSolution (cyclicFunctor k 3) (tLine k) (Equiv.ofBijective _ (alpha_bijective h3)) := by
  refine ⟨fun T f ↦ ?_, fun Z β hβ ↦ alpha_universal h3 β hβ⟩
  induction f using Quotient.inductionOn with
  | h x => exact ⟨cycMor h3 x, fun t ↦ (cycMor_pull h3 t x).symm⟩

end ModularFormsKB.Milne.CyclicThreeModuli

namespace ModularFormsKB.Milne

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Milne, Theorem 8.6 for $N = 3$**, unconditionally: over an algebraically closed field with $3 \ne 0$, the line
$\mathbb A^1 \smallsetminus \{27\}$ with the invariant $t = a_1^3/a_3$ of $y^2 + a_1xy + a_3y = x^3$ solves
$\mathcal E_{0,3}$. -/
@[kb "milne2017mf" "Section 8, Theorem 8.6 for N = 3 (pdf p. 100)"]
theorem cyclicModuliSolution_three : CyclicModuliSolution k 3 :=
  ⟨fun hN ↦ ⟨CyclicThreeModuli.tLine k, _, CyclicThreeModuli.isModuliSolution_three hN⟩⟩

end ModularFormsKB.Milne
