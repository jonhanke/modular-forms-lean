import ModularFormsKB.Milne.Ch8.LineChartDescent

/-!
# Milne, Chapter 8: Theorem 8.4 (the $j$-line is the solution of the moduli problem of elliptic curves)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 8, Theorem 8.4 (pdf p. 98).

Over an algebraically closed field $k$ of any characteristic, $(\mathbb A^1, \alpha)$ with $\alpha(E) = j(E)$
(`jEquiv`) is a solution of the moduli problem $\mathcal E$ (`ellipticModuliSolution`).

- Condition (a): the $j$-invariant of a family is a regular function (`jEquiv_regular`).
- Condition (b): let $\beta : \mathcal E(k) \to Z(k)$ be regular on families and put $b(w) = \beta(\alpha^{-1}(w))$.
  The family $y^2 + xy = x^3 - \frac{36}{j - 1728}x - \frac{1}{j - 1728}$ over
  $D(j(j - 1728)) \subseteq \mathbb A^1$ (Mathlib's `WeierstrassCurve.ofJNe0Or1728`) has $j$-invariant $j$, so $b$ is
  regular on $D(j(j - 1728))$ (`seedChart`). The universal Weierstrass family over
  $T = \operatorname{Spec} k[a_1, a_2, a_3, a_4, a_6][\Delta^{-1}]$ has a $k$-point over every $v \in k$
  (Mathlib's `WeierstrassCurve.ofJ`), and its $j$-map $k[X] \to \mathcal O(T)$ is injective; by descent along it
  (`exists_chart_at`) $b$ is regular around every point, hence on $\mathbb A^1$ (`exists_hom_of_charts`).
  Milne's own argument instead uses the Legendre family and the quotient by the anharmonic group, which fails in
  characteristic $2$; the descent used here works in every characteristic.
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite Polynomial TauCeti.AlgebraicGeometry

noncomputable section

namespace ModularFormsKB.Milne

variable {k : Type u} [Field k] [IsAlgClosed k]

/-! ### Families of Weierstrass curves over affine varieties -/

section Families

variable {R : Type u} [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]

/-- The class of the curve of an elliptic Weierstrass curve over a finitely generated domain $R$, as a family over
$\operatorname{Spec} R$. -/
def weierstrassFamily (W : WeierstrassCurve R) [W.IsElliptic] :
    (ellipticFunctor k).obj (op (domVariety (k := k) R)) :=
  Quotient.mk _ (⟨W.toEllipticCurveGeom, PUnit.unit⟩ : LevelPair _ (domVariety R))

theorem jEquiv_map_weierstrassFamily (W : WeierstrassCurve R) [W.IsElliptic] (τ : R →ₐ[k] k) :
    jEquiv ((ellipticFunctor k).map (algPoint τ).op (weierstrassFamily W)) = linePoint (τ W.j) := by
  rw [jEquiv_map]
  apply point_ext
  rw [appTop_linePoint]
  change (algPoint τ).hom.left.appTop ((mapToAffineLine _ (jClass (weierstrassFamily W))).hom.left.appTop
    (affineLineCoordinate k)) = _
  rw [mapToAffineLine_coordinate]
  change (Spec.map (CommRingCat.ofHom τ.toRingHom)).appTop W.toEllipticCurveGeom.j = _
  rw [WeierstrassCurve.j_toEllipticCurveGeom, appTop_specMap_inv]
  rfl

/-- A map $\beta$ regular on families is regular on the family of a Weierstrass curve, with value
$b(\tau(j))$ at $\tau$. -/
theorem exists_hom_weierstrassFamily {Z : Variety k} (β : (ellipticFunctor k).obj (op (Variety.point k)) →
      (Variety.point k ⟶ Z))
    (hβ : ∀ (T : Variety k) (f : (ellipticFunctor k).obj (op T)),
      ∃ φ : T ⟶ Z, ∀ t : Variety.point k ⟶ T, t ≫ φ = β ((ellipticFunctor k).map t.op f))
    (W : WeierstrassCurve R) [W.IsElliptic] :
    ∃ h : domVariety (k := k) R ⟶ Z, ∀ τ : R →ₐ[k] k,
      algPoint τ ≫ h = β (jEquiv.symm (linePoint (τ W.j))) := by
  obtain ⟨φ, hφ⟩ := hβ _ (weierstrassFamily W)
  refine ⟨φ, fun τ ↦ ?_⟩
  rw [hφ, ← jEquiv_map_weierstrassFamily W τ, Equiv.symm_apply_apply]

end Families

/-! ### The seed chart -/

/-- The polynomial $X (X - 1728)$. -/
abbrev seedPoly : k[X] := X * (X - Polynomial.C 1728)

theorem seedPoly_ne_zero : (seedPoly : k[X]) ≠ 0 := mul_ne_zero X_ne_zero (X_sub_C_ne_zero _)

/-- The coordinate on $D(X (X - 1728))$. -/
abbrev seedJ : Localization.Away (seedPoly : k[X]) := algebraMap k[X] _ X

instance fact_isUnit_seedJ : Fact (IsUnit (seedJ (k := k))) :=
  ⟨by
    have := isUnit_algebraMap_of_dvd (k := k) (dvd_mul_right X (X - Polynomial.C 1728)) 1
    rwa [pow_one] at this⟩

instance fact_isUnit_seedJ_sub : Fact (IsUnit (seedJ (k := k) - 1728)) :=
  ⟨by
    have := isUnit_algebraMap_of_dvd (k := k) (dvd_mul_left (X - Polynomial.C 1728) X) 1
    rw [pow_one, map_sub, show (Polynomial.C 1728 : k[X]) = 1728 from map_ofNat Polynomial.C 1728,
      map_ofNat] at this
    exact this⟩

/-- **The seed chart**: $b$ is regular on $D(X (X - 1728))$, through the family
$y^2 + xy = x^3 - \frac{36}{j - 1728}x - \frac{1}{j - 1728}$ with $j$-invariant $j$. -/
theorem nonempty_seedChart {Z : Variety k}
    (β : (ellipticFunctor k).obj (op (Variety.point k)) → (Variety.point k ⟶ Z))
    (hβ : ∀ (T : Variety k) (f : (ellipticFunctor k).obj (op T)),
      ∃ φ : T ⟶ Z, ∀ t : Variety.point k ⟶ T, t ≫ φ = β ((ellipticFunctor k).map t.op f)) :
    Nonempty (LineChart Z (fun w ↦ β (jEquiv.symm (linePoint w)))) := by
  haveI := isDomain_away k (seedPoly_ne_zero (k := k))
  obtain ⟨h, hh⟩ := exists_hom_weierstrassFamily β hβ (WeierstrassCurve.ofJNe0Or1728 (seedJ (k := k)))
  refine ⟨⟨seedPoly, seedPoly_ne_zero, h, fun w hw ↦ ?_⟩⟩
  have := hh (evalAwayAlg _ w hw)
  rw [WeierstrassCurve.ofJNe0Or1728_j, evalAwayAlg_algebraMap, eval_X] at this
  exact this

/-! ### The universal Weierstrass family -/

section Universal

variable (k) in
/-- The Weierstrass curve with indeterminate coefficients over $k[a_1, a_2, a_3, a_4, a_6]$. -/
abbrev univCurve0 : WeierstrassCurve (MvPolynomial (Fin 5) k) :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4⟩

variable (k) in
/-- The coordinate ring $k[a_1, a_2, a_3, a_4, a_6][\Delta^{-1}]$ of the base of the universal Weierstrass family. -/
abbrev UnivRing : Type u := Localization.Away (univCurve0 k).Δ

variable (k) in
/-- The universal elliptic Weierstrass curve over `UnivRing k`. -/
abbrev univCurve : WeierstrassCurve (UnivRing k) := (univCurve0 k).map (algebraMap _ (UnivRing k))

instance : (univCurve k).IsElliptic :=
  ⟨by rw [WeierstrassCurve.map_Δ]; exact IsLocalization.Away.algebraMap_isUnit _⟩

/-- Specialization of the coefficients to those of a Weierstrass curve over $k$. -/
def coeffAlg (W : WeierstrassCurve k) : MvPolynomial (Fin 5) k →ₐ[k] k :=
  MvPolynomial.aeval ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

theorem map_coeffAlg (W : WeierstrassCurve k) : (univCurve0 k).map (coeffAlg W).toRingHom = W := by
  ext <;> simp [coeffAlg]

theorem coeffAlg_Δ (W : WeierstrassCurve k) : coeffAlg W (univCurve0 k).Δ = W.Δ := by
  have := WeierstrassCurve.map_Δ (univCurve0 k) (coeffAlg W).toRingHom
  rw [map_coeffAlg] at this
  exact this.symm

theorem j_congr {W₁ W₂ : WeierstrassCurve k} [W₁.IsElliptic] [W₂.IsElliptic] (h : W₁ = W₂) : W₁.j = W₂.j := by
  subst h
  rfl

/-- The $k$-point of the base of the universal family of an elliptic Weierstrass curve over $k$. -/
def univPoint (W : WeierstrassCurve k) [W.IsElliptic] : UnivRing k →ₐ[k] k :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (univCurve0 k).Δ) (f := coeffAlg W) (by
    rintro ⟨_, n, rfl⟩
    rw [map_pow, coeffAlg_Δ]
    exact (WeierstrassCurve.IsElliptic.isUnit (W := W)).pow n)

theorem univPoint_j (W : WeierstrassCurve k) [W.IsElliptic] : univPoint W (univCurve k).j = W.j := by
  have h1 : (univPoint W).toRingHom.comp (algebraMap _ (UnivRing k)) = (coeffAlg W).toRingHom :=
    RingHom.ext fun x ↦ IsLocalization.lift_eq _ _
  have : (univCurve k).map (univPoint W).toRingHom = W := by
    rw [WeierstrassCurve.map_map, h1, map_coeffAlg]
  rw [← j_congr this, WeierstrassCurve.map_j (univCurve k)]
  rfl

theorem univCurve0_Δ_ne_zero : (univCurve0 k).Δ ≠ 0 := by
  classical
  intro h
  have := coeffAlg_Δ (WeierstrassCurve.ofJ (0 : k))
  rw [h, map_zero] at this
  exact (WeierstrassCurve.IsElliptic.isUnit (W := WeierstrassCurve.ofJ (0 : k))).ne_zero this.symm

instance : IsDomain (UnivRing k) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors univCurve0_Δ_ne_zero)

instance : Algebra.FiniteType k (UnivRing k) :=
  Algebra.FiniteType.trans (S := MvPolynomial (Fin 5) k) inferInstance inferInstance

variable (k) in
/-- The $j$-map $k[X] \to k[a_1, \dots, a_6][\Delta^{-1}]$ of the universal family. -/
def univJ : k[X] →ₐ[k] UnivRing k := Polynomial.aeval (univCurve k).j

theorem univPoint_univJ (W : WeierstrassCurve k) [W.IsElliptic] : univPoint W (univJ k X) = W.j := by
  rw [univJ, aeval_X, univPoint_j]

theorem univJ_injective : Function.Injective (univJ k) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro q hq
  refine Polynomial.funext fun v ↦ ?_
  have h := LineDescent.eval_of_algHom (univJ k) (univPoint (WeierstrassCurve.ofJ v))
    (by rw [univPoint_univJ, WeierstrassCurve.ofJ_j]) q
  rw [hq, map_zero] at h
  rw [← h, eval_zero]

end Universal

/-! ### Theorem 8.4 -/

/-- **Theorem 8.4, condition (b)** for $(\mathbb A^1, \alpha)$. -/
theorem jEquiv_universal (Z : Variety k)
    (β : (ellipticFunctor k).obj (op (Variety.point k)) → (Variety.point k ⟶ Z))
    (hβ : ∀ (T : Variety k) (f : (ellipticFunctor k).obj (op T)),
      ∃ φ : T ⟶ Z, ∀ t : Variety.point k ⟶ T, t ≫ φ = β ((ellipticFunctor k).map t.op f)) :
    ∃ ψ : affineLine k ⟶ Z, ∀ v : Variety.point k ⟶ affineLine k, v ≫ ψ = β (jEquiv.symm v) := by
  classical
  obtain ⟨c₀⟩ := nonempty_seedChart β hβ
  obtain ⟨h, hh⟩ := exists_hom_weierstrassFamily β hβ (univCurve k)
  have hh' : ∀ τ : UnivRing k →ₐ[k] k, algPoint τ ≫ h = β (jEquiv.symm (linePoint (τ (univJ k X)))) := by
    intro τ
    rw [hh, univJ, aeval_X]
  obtain ⟨ψ, hψ⟩ := exists_hom_of_charts (b := fun w ↦ β (jEquiv.symm (linePoint w))) fun v ↦
    exists_chart_at (univJ k) univJ_injective h hh' c₀ v (univPoint (WeierstrassCurve.ofJ v))
      (by rw [univPoint_univJ, WeierstrassCurve.ofJ_j])
  refine ⟨ψ, fun v ↦ ?_⟩
  have hv : linePoint (pointCoord v) = v := point_ext_coord (pointCoord_linePoint _)
  rw [← hv]
  exact hψ _

variable (k) in
/-- **Milne, Theorem 8.4**: over an algebraically closed field $k$ (of any characteristic), $(\mathbb A^1, j)$ is a
solution of the moduli problem $\mathcal E$ of elliptic curves. -/
@[kb "milne2017mf" "Section 8, Theorem 8.4 (pdf p. 98)"]
theorem ellipticModuliSolution : EllipticModuliSolution k :=
  ⟨⟨jEquiv, jEquiv_coordinate, ⟨jEquiv_regular, jEquiv_universal⟩⟩⟩

end ModularFormsKB.Milne
