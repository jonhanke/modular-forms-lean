import ModularFormsKB.Milne.Ch8.EllipticModuli
import ModularFormsKB.Milne.Ch8.LegendreAlgebra
import TauCeti.AlgebraicGeometry.EllipticCurve.Legendre
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Neg
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.VariableChange.OverScheme
import TauCeti.AlgebraicGeometry.ModularCurve.Comparison
import TauCeti.Data.ZMod.MonoidHomEquiv
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.RootsOfUnity
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Bilinear
import TauCeti.LinearAlgebra.BilinearForm.Basic

/-!
# Milne, Example 8.9: the moduli problem $\mathcal E_2$ has no fine moduli variety

Level-$2$ structures are not rigid: $[-1]$ fixes every point of order $2$. Over the Legendre line
$T = \operatorname{Spec} k[\lambda, (\lambda(\lambda - 1))^{-1}]$, the Legendre curve $y^2 = x(x - 1)(x - \lambda)$ with the
basis $(0, 0), (1, 0)$ of its $2$-torsion and its quadratic twist $y^2 = x(x - \lambda)(x - \lambda^2)$ with the basis
$(0, 0), (\lambda, 0)$ become isomorphic, with their level structures, over the double cover $T' \to T$,
$\lambda = s^2$, which is surjective on $k$-points. If $\mathcal E_2 \cong h_V$, the two classes over $T$ would have the
same image in $V(T)$ (their images agree after composing with $T' \to T$, hence on $k$-points), so they would be equal:
the two curves would be isomorphic over $T$. A pointed isomorphism of Weierstrass models over $T$ is a change of
variables (Tau Ceti, `existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom`), which multiplies the discriminant
by $u^{-12}$; the discriminants differ by $\lambda^6$, so $\lambda^3 = \pm u^6$ would be a square in
$k[\lambda, (\lambda(\lambda - 1))^{-1}]$, which it is not.

This refutes `LegendreFineModuli` (`not_legendreFineModuli`); see `docs/updates-and-errata.md`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory TauCeti TauCeti.AlgebraicGeometry
  WeierstrassCurve MonObj

noncomputable section

namespace ModularFormsKB.Milne.Ch8Counterexample

/-! ### Naive level-two structures -/

/-- A homomorphism out of $(\mathbb Z/2)^2$ is injective iff the images of $(1, 0)$, $(0, 1)$ are nontrivial and
distinct. -/
theorem injective_zmod_two_prod_iff {G : Type*} [Group G] (ψ : Multiplicative (ZMod 2 × ZMod 2) →* G) :
    Function.Injective ψ ↔ ψ (.ofAdd (1, 0)) ≠ 1 ∧ ψ (.ofAdd (0, 1)) ≠ 1 ∧
      ψ (.ofAdd (0, 1)) ≠ ψ (.ofAdd (1, 0)) := by
  have hadd : (.ofAdd (1, 1) : Multiplicative (ZMod 2 × ZMod 2)) = .ofAdd (0, 1) / .ofAdd (1, 0) := by decide
  rw [injective_iff_map_eq_one]
  refine ⟨fun h ↦ ⟨fun e ↦ absurd (h _ e) (by decide), fun e ↦ absurd (h _ e) (by decide),
    fun e ↦ absurd (h (.ofAdd (1, 1)) (by rw [hadd, map_div, e, div_self'])) (by decide)⟩,
    fun ⟨h₁, h₂, h₃⟩ z hz ↦ ?_⟩
  have hp : ∀ p : ZMod 2 × ZMod 2, p = 0 ∨ p = (1, 0) ∨ p = (0, 1) ∨ p = (1, 1) := by decide
  obtain ⟨p, rfl⟩ : ∃ p, Multiplicative.ofAdd p = z := ⟨z.toAdd, rfl⟩
  rcases hp p with rfl | rfl | rfl | rfl
  · exact ofAdd_zero
  · exact absurd hz h₁
  · exact absurd hz h₂
  · rw [hadd, map_div, div_eq_one] at hz
    exact absurd hz h₃

variable {S : Scheme.{u}} {E : EllipticCurveGeom S}

/-- **The naive `[Γ(2)]` condition.** A homomorphism `φ : (ℤ/2ℤ)² →* E(S)` is injective on every fibre exactly
when `P = φ (1, 0)` and `Q = φ (0, 1)` miss the zero section and `Q ≠ P` over every point of `S`. -/
theorem isFiberwiseInjective_zmod_two_prod_iff
    {φ : Multiplicative (ZMod 2 × ZMod 2) →* (𝟙_ (Over S) ⟶ Over.mk E.structureMap)} :
    E.IsFiberwiseInjective φ ↔
      (∀ s, (φ (.ofAdd (1, 0))).left s ≠ E.zero s) ∧ (∀ s, (φ (.ofAdd (0, 1))).left s ≠ E.zero s) ∧
        ∀ s, (φ (.ofAdd (0, 1))).left s ≠ (φ (.ofAdd (1, 0))).left s := by
  rw [EllipticCurveGeom.isFiberwiseInjective_iff_forall_residueField]
  simp only [← forall_and]
  refine forall_congr' fun s ↦ ?_
  set ψ := (EllipticCurveGeom.pointsPullback (E.isPullback_baseChange (S.fromSpecResidueField s))
    (by simp)).comp φ
  have hψ (a b) : ψ a = ψ b ↔ (φ a).left s = (φ b).left s :=
    EllipticCurveGeom.pointsPullback_fromSpecResidueField_eq_iff _ _ s
  rw [injective_zmod_two_prod_iff, ne_eq, ne_eq, ne_eq, ← map_one ψ, hψ, hψ, hψ]
  simp only [map_one]
  rfl

/-! ### Points of order two on a Weierstrass curve over a ring -/

section Weierstrass

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]

/-- The point $[x : y : 1]$ of a Weierstrass curve over $R$, as an $R$-point of the elliptic curve
`W.toEllipticCurveGeom`. -/
def affinePointHom {x y : R} (h : W.toAffine.Equation x y) :
    𝟙_ (Over (Spec (.of R))) ⟶ Over.mk W.toEllipticCurveGeom.structureMap :=
  Over.homMk (W.projModelAffinePoint h ≫ (toEllipticCurveGeomIso W).inv) <| by
    simp [← toEllipticCurveGeomIso_hom_projModelOver]

theorem affinePointHom_left {x y : R} (h : W.toAffine.Equation x y) :
    (affinePointHom W h).left = W.projModelAffinePoint h ≫ (toEllipticCurveGeomIso W).inv :=
  rfl

variable {W}

/-- A point $(x, 0)$ of a curve with $a_1 = a_3 = 0$ is its own negative. -/
theorem affinePointHom_inv (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) {x : R} (h : W.toAffine.Equation x 0) :
    (affinePointHom W h)⁻¹ = affinePointHom W h := by
  apply Over.OverMorphism.ext
  rw [EllipticCurveGeom.hom_inv_left, affinePointHom_left, Category.assoc,
    ← cancel_mono (toEllipticCurveGeomIso W).hom, Category.assoc, Category.assoc,
    neg_toEllipticCurveGeomIso_hom, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    projModelAffinePoint_projModelNeg, projModelAffinePoint_inj]
  refine ⟨rfl, ?_⟩
  simp [Affine.negY, ha₁, ha₃]

/-- A point $(x, 0)$ of a curve with $a_1 = a_3 = 0$ has order dividing $2$. -/
theorem affinePointHom_sq (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) {x : R} (h : W.toAffine.Equation x 0) :
    affinePointHom W h ^ 2 = 1 := by
  rw [sq]
  nth_rewrite 1 [← affinePointHom_inv ha₁ ha₃ h]
  exact inv_mul_cancel _

/-- An affine point misses the zero section everywhere. -/
theorem affinePointHom_ne_zero {x y : R} (h : W.toAffine.Equation x y) (s : Spec (.of R)) :
    (affinePointHom W h).left s ≠ W.toEllipticCurveGeom.zero s := by
  intro hs
  have h' := congrArg (toEllipticCurveGeomIso W).hom hs
  rw [affinePointHom_left, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, zero_toEllipticCurveGeomIso_hom] at h'
  exact (ne_projModelZero_iff_mem_basicOpen (projModelAffinePoint_projModelOver h) s).mpr
    (projModelAffinePoint_mem_basicOpen h s) h'

/-- Two affine points whose $x$-coordinates differ by a unit are distinct everywhere. -/
theorem affinePointHom_ne {x₁ y₁ x₂ y₂ : R} (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hx : IsUnit (x₂ - x₁)) (s : Spec (.of R)) :
    (affinePointHom W h₂).left s ≠ (affinePointHom W h₁).left s := by
  intro hs
  have h' := congrArg (toEllipticCurveGeomIso W).hom hs
  rw [affinePointHom_left, affinePointHom_left, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.comp_id,
    projModelAffinePoint_apply_eq_iff] at h'
  exact s.isPrime.ne_top ((Ideal.eq_top_of_isUnit_mem _ h'.1 hx))

variable (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) {x₁ x₂ : R} (h₁ : W.toAffine.Equation x₁ 0)
  (h₂ : W.toAffine.Equation x₂ 0)

/-- **The naive level-two structure** $(1, 0) \mapsto (x_1, 0)$, $(0, 1) \mapsto (x_2, 0)$. -/
def level2 : Multiplicative (ZMod 2 × ZMod 2) →* (𝟙_ (Over (Spec (.of R))) ⟶
    Over.mk W.toEllipticCurveGeom.structureMap) :=
  (zmodProdMonoidHomEquiv 2 _).symm
    (⟨affinePointHom W h₁, affinePointHom_sq ha₁ ha₃ h₁⟩, ⟨affinePointHom W h₂, affinePointHom_sq ha₁ ha₃ h₂⟩)

theorem level2_one_zero : level2 ha₁ ha₃ h₁ h₂ (.ofAdd (1, 0)) = affinePointHom W h₁ := by
  rw [← coe_zmodProdMonoidHomEquiv_apply_fst, level2, Equiv.apply_symm_apply]

theorem level2_zero_one : level2 ha₁ ha₃ h₁ h₂ (.ofAdd (0, 1)) = affinePointHom W h₂ := by
  rw [← coe_zmodProdMonoidHomEquiv_apply_snd, level2, Equiv.apply_symm_apply]

theorem isFiberwiseInjective_level2 (hx : IsUnit (x₂ - x₁)) :
    W.toEllipticCurveGeom.IsFiberwiseInjective (level2 ha₁ ha₃ h₁ h₂) := by
  rw [isFiberwiseInjective_zmod_two_prod_iff, level2_one_zero, level2_zero_one]
  exact ⟨affinePointHom_ne_zero h₁, affinePointHom_ne_zero h₂, affinePointHom_ne h₁ h₂ hx⟩

end Weierstrass

/-! ### The Weil pairing of a basis of the `2`-torsion is `-1` -/

section WeilPairingTwo

variable {F : Type*} [Field F] [DecidableEq F] [IsSepClosed F] (W : WeierstrassCurve F) [W.IsElliptic]
  (hF : ((2 : ℕ) : F) ≠ 0)

/-- **$e_2(S, T) = -1$** for two distinct nonzero points $S, T$ of order dividing $2$, over a separably closed field
of characteristic $\ne 2$. -/
theorem weilPairing_two_eq_neg_one (S T : AddSubgroup.torsionBy W.toAffine.Point ((2 : ℕ) : ℤ))
    (hS : S ≠ 0) (hT : T ≠ 0) (hST : S ≠ T) :
    (((TauCeti.Isogeny.weilPairing W 2 hF S T).toMul : Fˣ) : F) = -1 := by
  obtain ⟨b⟩ := nonempty_basis_torsionBy W 2 hF
  -- `S, T` are linearly independent over `ZMod 2`
  have hli : LinearIndependent (ZMod 2) ![S, T] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 : ∀ x : AddSubgroup.torsionBy W.toAffine.Point ((2 : ℕ) : ℤ), x + x = 0 := by
      intro x
      have : (2 : ℤ) • (x : W.toAffine.Point) = 0 := x.2
      rw [two_smul] at this
      exact Subtype.ext this
    have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hcases s with rfl | rfl <;> rcases hcases t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · simp only [one_smul, zero_smul, zero_add] at hst; exact absurd hst hT
    · simp only [one_smul, zero_smul, add_zero] at hst; exact absurd hst hS
    · exfalso; apply hST
      simp only [one_smul] at hst
      have := congrArg (· + T) hst
      simp only [zero_add, add_assoc, h2, add_zero] at this
      exact this
  have hcard : Fintype.card (Fin 2) = Module.finrank (ZMod 2)
      (AddSubgroup.torsionBy W.toAffine.Point ((2 : ℕ) : ℤ)) := by
    rw [Module.finrank_eq_card_basis b]
  let c := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hc0 : c 0 = S := by simp [c]
  have hc1 : c 1 = T := by simp [c]
  have hprim : IsPrimitiveRoot (((TauCeti.Isogeny.weilPairing W 2 hF (c 0) (c 1)).toMul : Fˣ) : F) 2 := by
    refine IsPrimitiveRoot.coe_units_iff.2 <| IsPrimitiveRoot.coe_submonoidClass_iff.2
      ⟨by rw [← toMul_nsmul, nsmul_additive_rootsOfUnity_eq_zero, toMul_zero],
      fun l hl ↦ (ZMod.natCast_eq_zero_iff l 2).1 <|
        (TauCeti.Isogeny.isAlt_weilPairingBilin W 2 hF).eq_zero_of_smul_apply_basis_eq_zero c
          (TauCeti.Isogeny.separatingLeft_weilPairingBilin W 2 hF) ?_⟩
    rw [TauCeti.Isogeny.weilPairingBilin_apply, Nat.cast_smul_eq_nsmul]
    exact Additive.toMul.injective (by simpa [toMul_nsmul] using hl)
  rw [hc0, hc1] at hprim
  exact hprim.eq_neg_one_of_two_right

end WeilPairingTwo

/-! ### Every level-two structure has Weil pairing `-1` -/

section HasWeilPairingTwo

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The residue fields of $\operatorname{Spec} k$ have $2 \ne 0$ when $2 \ne 0$ in $k$. -/
theorem two_ne_zero_residueField (hk : ((2 : ℕ) : k) ≠ 0) (s : Spec (.of k)) :
    ((2 : ℕ) : (Spec (.of k)).residueField s) ≠ 0 := by
  let f : k →+* (Spec (.of k)).residueField s :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Spec (.of k)).evaluation ⊤ s trivial).hom
  intro h
  apply hk
  apply f.injective
  rw [map_natCast, h, map_zero]

/-- An isomorphism of elliptic curves over the same base, as an arrow of `Ell/B` over the identity. -/
def isoHom {B T : Scheme.{u}} (g : T ⟶ B) {E E' : EllipticCurveGeom T} (e : E.carrier ≅ E'.carrier)
    (he : e.hom ≫ E'.structureMap = E.structureMap) (h0 : E.zero ≫ e.hom = E'.zero) :
    (⟨T, g, E⟩ : EllObj B) ⟶ ⟨T, g, E'⟩ where
  base := 𝟙 _
  base_structureMap := Category.id_comp _
  total := e.hom
  isPullback := IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩
  zero_total := by rw [h0, Category.id_comp]

theorem isoHom_base {B T : Scheme.{u}} (g : T ⟶ B) {E E' : EllipticCurveGeom T} (e : E.carrier ≅ E'.carrier)
    (he : e.hom ≫ E'.structureMap = E.structureMap) (h0 : E.zero ≫ e.hom = E'.zero) :
    (isoHom g e he h0).base = 𝟙 _ := rfl

/-- **The Weil pairing condition is automatic for level two**: over an algebraically closed field with $2 \ne 0$,
every pair $(E, t)$ of an elliptic curve over a variety with a `[Γ(2)]`-structure has $e_2(t_1, t_2) = -1$ in every
fibre. -/
theorem hasWeilPairing_two (hk : ((2 : ℕ) : k) ≠ 0) {V : Variety k}
    (x : LevelPair (ModuliProblem.gamma (Spec (CommRingCat.of k)) 2) V) : HasWeilPairing 2 hk (-1) x := by
  intro v
  set Ef := x.1.baseChange v.hom.left
  obtain ⟨W, hW, e0, he0, hz⟩ := Ef.exists_iso_toEllipticCurveGeom
  let a : (Variety.point k).ellObj W.toEllipticCurveGeom ⟶ (Variety.point k).ellObj Ef :=
    isoHom _ e0 he0 hz
  refine ⟨W, hW, a ≫ LevelPair.pullHom v x.1, ?_, ?_⟩
  · rw [EllObj.comp_base]
    change 𝟙 _ ≫ (LevelPair.pullHom v x.1).base = _
    rw [Category.id_comp, LevelPair.pullHom_base]
  · classical
    set s := (ModuliProblem.gamma _ 2).map (a ≫ LevelPair.pullHom v x.1).op x.2
    set φ := (ModuliProblem.gammaEquiv _ s).1
    have hinj : Function.Injective φ := by
      have h := ((ModuliProblem.gammaEquiv _ s).2).isFiberwiseInjective
        (two_ne_zero_residueField (k := k) hk)
      exact (EllipticCurveGeom.isFiberwiseInjective_iff_injective _ φ).mp h
    have hne : ∀ p q : Multiplicative (ZMod 2 × ZMod 2), p ≠ q →
        (W.toEllipticCurveGeomPointsMulEquiv (φ p)).toAdd ≠ (W.toEllipticCurveGeomPointsMulEquiv (φ q)).toAdd :=
      fun p q hpq h ↦ hpq (hinj (W.toEllipticCurveGeomPointsMulEquiv.injective (Multiplicative.toAdd.injective h)))
    have h0 : ∀ p : Multiplicative (ZMod 2 × ZMod 2), p ≠ 1 →
        (W.toEllipticCurveGeomPointsMulEquiv (φ p)).toAdd ≠ 0 := by
      intro p hp h
      have := hne p 1 hp
      simp only [map_one] at this
      exact this (h.trans (congrArg Multiplicative.toAdd (map_one W.toEllipticCurveGeomPointsMulEquiv)).symm)
    intro S T hS hT
    refine weilPairing_two_eq_neg_one W hk S T ?_ ?_ ?_
    · intro h; apply h0 (.ofAdd (1, 0)) (by decide); rw [← hS, h]; rfl
    · intro h; apply h0 (.ofAdd (0, 1)) (by decide); rw [← hT, h]; rfl
    · intro h; apply hne (.ofAdd (1, 0)) (.ofAdd (0, 1)) (by decide); rw [← hS, ← hT, h]

end HasWeilPairingTwo

/-! ### Arrows of `Ell/B` from base change and from changes of variables -/

section Arrows

variable {R : Type u} [CommRing R] {B : Scheme.{u}} (g : Spec (.of R) ⟶ B)

/-- **Base change of a Weierstrass curve along a ring map**, as an arrow of `Ell/B`. -/
def bcHom (W : WeierstrassCurve R) [W.IsElliptic] {R' : Type u} [CommRing R'] (φ : R →+* R')
    (g' : Spec (.of R') ⟶ B) (hg : Spec.map (CommRingCat.ofHom φ) ≫ g = g') :
    (⟨Spec (.of R'), g', (W.map φ).toEllipticCurveGeom⟩ : EllObj B) ⟶
      ⟨Spec (.of R), g, W.toEllipticCurveGeom⟩ where
  base := Spec.map (CommRingCat.ofHom φ)
  base_structureMap := hg
  total := (toEllipticCurveGeomIso (W.map φ)).hom ≫ W.projModelBaseChange φ ≫ (toEllipticCurveGeomIso W).inv
  isPullback := (W.isPullback_projModelBaseChange φ).of_iso (toEllipticCurveGeomIso (W.map φ)).symm
    (toEllipticCurveGeomIso W).symm (.refl _) (.refl _) (by simp) (by simp [← toEllipticCurveGeomIso_hom_projModelOver])
    (by simp [← toEllipticCurveGeomIso_hom_projModelOver]) (by simp)
  zero_total := by
    rw [← Category.assoc, zero_toEllipticCurveGeomIso_hom, ← Category.assoc, projModelZero_projModelBaseChange,
      Category.assoc, ← zero_toEllipticCurveGeomIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem bcHom_base (W : WeierstrassCurve R) [W.IsElliptic] {R' : Type u} [CommRing R'] (φ : R →+* R')
    (g' : Spec (.of R') ⟶ B) (hg : Spec.map (CommRingCat.ofHom φ) ≫ g = g') :
    (bcHom g W φ g' hg).base = Spec.map (CommRingCat.ofHom φ) := rfl

theorem pointsPullback_bcHom (W : WeierstrassCurve R) [W.IsElliptic] {R' : Type u} [CommRing R'] (φ : R →+* R')
    (g' : Spec (.of R') ⟶ B) (hg : Spec.map (CommRingCat.ofHom φ) ≫ g = g')
    {x y : R} (h : W.toAffine.Equation x y) :
    EllipticCurveGeom.pointsPullback (bcHom g W φ g' hg).isPullback (bcHom g W φ g' hg).zero_total
      (affinePointHom W h) =
      affinePointHom (W.map φ) (h.map φ) := by
  symm
  rw [EllipticCurveGeom.eq_pointsPullback_iff]
  simp only [bcHom, affinePointHom_left, Category.assoc, Iso.inv_hom_id_assoc]
  rw [projModelAffinePoint_projModelBaseChange_assoc]

/-- **A change of variables** $W = C \cdot W'$, as an arrow of `Ell/B` over the identity. -/
def vcHom (W' : WeierstrassCurve R) [W'.IsElliptic] (C : VariableChange R) :
    (⟨Spec (.of R), g, (C • W').toEllipticCurveGeom⟩ : EllObj B) ⟶ ⟨Spec (.of R), g, W'.toEllipticCurveGeom⟩ :=
  isoHom g (toEllipticCurveGeomIso (C • W') ≪≫ W'.projModelVariableChangeIso C ≪≫ (toEllipticCurveGeomIso W').symm)
    (by
      rw [← toEllipticCurveGeomIso_hom_projModelOver W', ← toEllipticCurveGeomIso_hom_projModelOver (C • W')]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
        projModelVariableChangeIso_hom_projModelOver])
    (by
      simp only [Iso.trans_hom, Iso.symm_hom]
      rw [reassoc_of% (zero_toEllipticCurveGeomIso_hom (C • W')), projModelZero_projModelVariableChangeIso_hom_assoc,
        ← zero_toEllipticCurveGeomIso_hom W', Category.assoc, Iso.hom_inv_id, Category.comp_id])

theorem vcHom_base (W' : WeierstrassCurve R) [W'.IsElliptic] (C : VariableChange R) :
    (vcHom g W' C).base = 𝟙 _ := rfl

theorem pointsPullback_vcHom (W' : WeierstrassCurve R) [W'.IsElliptic] (C : VariableChange R) {x y : R}
    (h : (C • W').toAffine.Equation x y) :
    EllipticCurveGeom.pointsPullback (vcHom g W' C).isPullback (vcHom g W' C).zero_total
        (affinePointHom W' ((Affine.variableChange_equation W' C x y).mpr h)) =
      affinePointHom (C • W') h := by
  symm
  rw [EllipticCurveGeom.eq_pointsPullback_iff]
  simp only [vcHom, isoHom, affinePointHom_left, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Category.id_comp]
  rw [projModelAffinePoint_projModelVariableChangeIso_hom_assoc]

end Arrows

/-! ### An arrow of `Ell/B` over the identity gives a pointed isomorphism of Weierstrass models -/

section PointedIso

variable {R : Type u} [CommRing R] {B : Scheme.{u}} (g : Spec (.of R) ⟶ B) {W W' : WeierstrassCurve R}
  [W.IsElliptic] [W'.IsElliptic]

theorem exists_pointedIso_of_hom
    (f : (⟨Spec (.of R), g, W.toEllipticCurveGeom⟩ : EllObj B) ⟶ ⟨Spec (.of R), g, W'.toEllipticCurveGeom⟩)
    (hf : f.base = 𝟙 _) :
    ∃ e : W.projModel ≅ W'.projModel, e.hom ≫ W'.projModelOver = W.projModelOver ∧
      W.projModelZero ≫ e.hom = W'.projModelZero := by
  have hpb := f.isPullback
  rw [hf] at hpb
  have : IsIso f.total := hpb.isIso_fst_of_isIso
  refine ⟨(toEllipticCurveGeomIso W).symm ≪≫ asIso f.total ≪≫ toEllipticCurveGeomIso W', ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, toEllipticCurveGeomIso_hom_projModelOver]
    have h1 := f.total_structureMap
    rw [hf, Category.comp_id] at h1
    rw [show f.total ≫ (W'.toEllipticCurveGeom).structureMap = W.toEllipticCurveGeom.structureMap from h1,
      ← toEllipticCurveGeomIso_hom_projModelOver, Iso.inv_hom_id_assoc]
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom]
    have h0 := f.zero_total
    rw [hf, Category.id_comp] at h0
    rw [← zero_toEllipticCurveGeomIso_hom, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc,
      show W.toEllipticCurveGeom.zero ≫ f.total = W'.toEllipticCurveGeom.zero from h0,
      zero_toEllipticCurveGeomIso_hom]

end PointedIso

/-! ### The Legendre curve and its twist over the Legendre line are not isomorphic -/

section Twist

variable {k : Type u} [Field k]

theorem isUnit_legendreLambda : IsUnit (legendreLambda k) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := LegendreRing k) (Polynomial.X * (Polynomial.X - 1) :
    Polynomial k)
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_left h

theorem isUnit_legendreLambda_sub_one : IsUnit (legendreLambda k - 1) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := LegendreRing k) (Polynomial.X * (Polynomial.X - 1) :
    Polynomial k)
  rw [map_mul, map_sub, map_one] at h
  exact isUnit_of_mul_isUnit_right h

instance : IsDomain (LegendreRing k) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors
    (mul_ne_zero Polynomial.X_ne_zero (Polynomial.X_sub_C_ne_zero 1)))

variable (k)

/-- The Legendre curve $y^2 = x(x - 1)(x - \lambda)$ over $k[\lambda, (\lambda(\lambda - 1))^{-1}]$. -/
abbrev legendreCurve : WeierstrassCurve (LegendreRing k) := freyCurve 1 (-legendreLambda k)

/-- Its quadratic twist by $\lambda$: $y^2 = x(x - \lambda)(x - \lambda^2)$. -/
abbrev twistCurve : WeierstrassCurve (LegendreRing k) := freyCurve (legendreLambda k) (-legendreLambda k ^ 2)

variable [CharZero k]

theorem isUnit_two_legendreRing : IsUnit (2 : LegendreRing k) := by
  rw [← map_ofNat (algebraMap k (LegendreRing k)) 2]
  exact (IsUnit.mk0 (2 : k) two_ne_zero).map _

instance : (legendreCurve k).IsElliptic := by
  rw [isElliptic_freyCurve_iff]
  refine ⟨isUnit_two_legendreRing k, isUnit_one, isUnit_legendreLambda.neg, ?_⟩
  have : (1 : LegendreRing k) + -legendreLambda k = -(legendreLambda k - 1) := by ring
  rw [this]
  exact isUnit_legendreLambda_sub_one.neg

instance : (twistCurve k).IsElliptic := by
  rw [isElliptic_freyCurve_iff]
  refine ⟨isUnit_two_legendreRing k, isUnit_legendreLambda, (isUnit_legendreLambda.pow 2).neg, ?_⟩
  have : legendreLambda k + -legendreLambda k ^ 2 = -(legendreLambda k * (legendreLambda k - 1)) := by ring
  rw [this]
  exact (isUnit_legendreLambda.mul isUnit_legendreLambda_sub_one).neg

variable [IsAlgClosed k]

/-- **The Legendre curve and its twist are not isomorphic over the Legendre line**: there is no pointed isomorphism
of their Weierstrass models over $k[\lambda, (\lambda(\lambda - 1))^{-1}]$. -/
theorem not_exists_pointedIso :
    ¬ ∃ e : (legendreCurve k).projModel ≅ (twistCurve k).projModel,
      e.hom ≫ (twistCurve k).projModelOver = (legendreCurve k).projModelOver ∧
        (legendreCurve k).projModelZero ≫ e.hom = (twistCurve k).projModelZero := by
  rintro ⟨e, he, h0⟩
  obtain ⟨C, ⟨hC, -⟩, -⟩ := existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e he h0
  have hΔ := congrArg WeierstrassCurve.Δ hC
  rw [variableChange_Δ, freyCurve_Δ, freyCurve_Δ] at hΔ
  set l := legendreLambda k
  set u : LegendreRing k := (C.u : LegendreRing k)
  have hD : IsUnit (16 * l ^ 2 * (1 - l) ^ 2 : LegendreRing k) := by
    have h16 : IsUnit (16 : LegendreRing k) := by
      have : (16 : LegendreRing k) = 2 ^ 4 := by norm_num
      rw [this]; exact (isUnit_two_legendreRing k).pow 4
    have h1 : IsUnit (1 - l) := by
      have : (1 : LegendreRing k) - l = -(l - 1) := by ring
      rw [this]; exact isUnit_legendreLambda_sub_one.neg
    exact (h16.mul (isUnit_legendreLambda.pow 2)).mul (h1.pow 2)
  -- `u⁻¹² l⁶ D = D`, so `l⁶ = u¹²`
  have h6 : l ^ 6 = u ^ 12 := by
    set v : LegendreRing k := ((C.u⁻¹ : (LegendreRing k)ˣ) : LegendreRing k) with hv
    have hu : v * u = 1 := by simp [u, v]
    have : v ^ 12 * l ^ 6 * (16 * l ^ 2 * (1 - l) ^ 2) = 16 * l ^ 2 * (1 - l) ^ 2 := by
      linear_combination hΔ
    have h' : l ^ 6 * (16 * l ^ 2 * (1 - l) ^ 2) = u ^ 12 * (16 * l ^ 2 * (1 - l) ^ 2) := by
      calc l ^ 6 * (16 * l ^ 2 * (1 - l) ^ 2)
          = (v * u) ^ 12 * l ^ 6 * (16 * l ^ 2 * (1 - l) ^ 2) := by rw [hu]; ring
        _ = u ^ 12 * (v ^ 12 * l ^ 6 * (16 * l ^ 2 * (1 - l) ^ 2)) := by ring
        _ = u ^ 12 * (16 * l ^ 2 * (1 - l) ^ 2) := by rw [this]
    exact hD.mul_left_injective h'
  -- hence `l³ = ± u⁶`, a square
  apply not_exists_sq_eq_legendreLambda_pow_three (k := k)
  have hfac : (l ^ 3 - u ^ 6) * (l ^ 3 + u ^ 6) = 0 := by linear_combination h6
  rcases mul_eq_zero.mp hfac with h | h
  · exact ⟨u ^ 3, by linear_combination -h⟩
  · obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : k) two_pos
    refine ⟨algebraMap k (LegendreRing k) i * u ^ 3, ?_⟩
    have hi' : (algebraMap k (LegendreRing k) i) ^ 2 = -1 := by rw [← map_pow, hi, map_neg, map_one]
    linear_combination (u ^ 6) * hi' - h

end Twist

/-! ### Affine varieties with level-two pairs -/

section Pairs

variable {k : Type u} [Field k]

/-- $\operatorname{Spec} A$ as a variety, for an affine $k$-algebra $A$. -/
def specVariety (A : Type u) [CommRing A] [Algebra k A] (hA : IsAffineAlgebra k A) : Variety k :=
  ⟨Over.mk (specStructure k A), (isAffineVariety_spec k hA).isVariety⟩

/-- The regular map $\operatorname{Spec} A' \to \operatorname{Spec} A$ of a $k$-algebra map $A \to A'$. -/
def specHom {A A' : Type u} [CommRing A] [Algebra k A] [CommRing A'] [Algebra k A'] (hA : IsAffineAlgebra k A)
    (hA' : IsAffineAlgebra k A') (φ : A →ₐ[k] A') : specVariety A' hA' ⟶ specVariety A hA :=
  ⟨Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact φ.commutes c)⟩

theorem specHom_left {A A' : Type u} [CommRing A] [Algebra k A] [CommRing A'] [Algebra k A']
    (hA : IsAffineAlgebra k A) (hA' : IsAffineAlgebra k A') (φ : A →ₐ[k] A') :
    (specHom hA hA' φ).hom.left = Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl

/-- $k$-points of $\operatorname{Spec} A$ are $k$-algebra maps $A \to k$. -/
theorem exists_algHom_of_point {A : Type u} [CommRing A] [Algebra k A] (hA : IsAffineAlgebra k A)
    (t : Variety.point k ⟶ specVariety A hA) :
    ∃ φ : A →ₐ[k] k, t.hom.left = Spec.map (CommRingCat.ofHom φ.toRingHom) := by
  let f : Spec (.of k) ⟶ Spec (.of A) := t.hom.left
  let φ0 := Spec.preimage f
  have hφ0 : Spec.map φ0 = f := Spec.map_preimage f
  have hw : f ≫ specStructure k A = 𝟙 _ := Over.w t.hom
  have hc : CommRingCat.ofHom (algebraMap k A) ≫ φ0 = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ0, Spec.map_id]
    exact hw
  have hcomm : ∀ c : k, φ0.hom (algebraMap k A c) = algebraMap k k c := fun c ↦ by
    have := congrArg (fun h ↦ h.hom c) hc
    simpa using this
  exact ⟨{ φ0.hom with commutes' := hcomm }, hφ0.symm⟩

variable (k)

/-- **A level-two pair over $\operatorname{Spec} A$**: a Weierstrass curve with $a_1 = a_3 = 0$ and two points
$(x_1, 0), (x_2, 0)$ with $x_2 - x_1$ a unit. -/
def pairOf {A : Type u} [CommRing A] [Algebra k A] (hA : IsAffineAlgebra k A) (W : WeierstrassCurve A)
    [W.IsElliptic] (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) {x₁ x₂ : A} (h₁ : W.toAffine.Equation x₁ 0)
    (h₂ : W.toAffine.Equation x₂ 0) (hx : IsUnit (x₂ - x₁)) :
    LevelPair (ModuliProblem.gamma (Spec (CommRingCat.of k)) 2) (specVariety A hA) :=
  ⟨W.toEllipticCurveGeom, (ModuliProblem.gammaEquiv _).symm
    ⟨level2 ha₁ ha₃ h₁ h₂, (isFiberwiseInjective_level2 ha₁ ha₃ h₁ h₂ hx).isDrinfeldBasis⟩⟩

variable {k}

/-- Homomorphisms out of $(\mathbb Z/2)^2$ into a commutative group agree if they agree on $(1, 0)$ and $(0, 1)$. -/
theorem hom_ext_two {G : Type*} [CommGroup G] {φ ψ : Multiplicative (ZMod 2 × ZMod 2) →* G}
    (h₁ : φ (.ofAdd (1, 0)) = ψ (.ofAdd (1, 0))) (h₂ : φ (.ofAdd (0, 1)) = ψ (.ofAdd (0, 1))) : φ = ψ := by
  apply (zmodProdMonoidHomEquiv 2 G).injective
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [coe_zmodProdMonoidHomEquiv_apply_fst, coe_zmodProdMonoidHomEquiv_apply_fst, h₁]
  · rw [coe_zmodProdMonoidHomEquiv_apply_snd, coe_zmodProdMonoidHomEquiv_apply_snd, h₂]

theorem affinePointHom_congr {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] {x y x' y' : R}
    (h : W.toAffine.Equation x y) (h' : W.toAffine.Equation x' y') (hx : x = x') (hy : y = y') :
    affinePointHom W h = affinePointHom W h' := by
  subst hx hy; rfl

/-- **Pulling back a pair along $\operatorname{Spec} A' \to \operatorname{Spec} A$** gives the pair of the base
changed Weierstrass curve. -/
theorem gammaEquiv_pairOf {A : Type u} [CommRing A] [Algebra k A] (hA : IsAffineAlgebra k A)
    (W : WeierstrassCurve A) [W.IsElliptic] (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) {x₁ x₂ : A}
    (h₁ : W.toAffine.Equation x₁ 0) (h₂ : W.toAffine.Equation x₂ 0) (hx : IsUnit (x₂ - x₁)) :
    (ModuliProblem.gammaEquiv _ (pairOf k hA W ha₁ ha₃ h₁ h₂ hx).2).1 = level2 ha₁ ha₃ h₁ h₂ :=
  congrArg Subtype.val ((ModuliProblem.gammaEquiv _).apply_symm_apply _)

theorem rel_pull_pairOf {A A' : Type u} [CommRing A] [Algebra k A] [CommRing A'] [Algebra k A']
    (hA : IsAffineAlgebra k A) (hA' : IsAffineAlgebra k A') (φ : A →ₐ[k] A') (W : WeierstrassCurve A)
    [W.IsElliptic] (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) {x₁ x₂ : A} (h₁ : W.toAffine.Equation x₁ 0)
    (h₂ : W.toAffine.Equation x₂ 0) (hx : IsUnit (x₂ - x₁)) (ha₁' : (W.map φ.toRingHom).a₁ = 0)
    (ha₃' : (W.map φ.toRingHom).a₃ = 0) (h₁' : (W.map φ.toRingHom).toAffine.Equation (φ x₁) 0)
    (h₂' : (W.map φ.toRingHom).toAffine.Equation (φ x₂) 0) (hx' : IsUnit (φ x₂ - φ x₁)) :
    LevelPair.Rel (LevelPair.pull (specHom hA hA' φ) (pairOf k hA W ha₁ ha₃ h₁ h₂ hx))
      (pairOf k hA' (W.map φ.toRingHom) ha₁' ha₃' h₁' h₂' hx') := by
  let b := bcHom (specStructure k A) W φ.toRingHom (specStructure k A') (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact φ.commutes c)
  have h := LevelPair.rel_of_arrows (pairOf k hA W ha₁ ha₃ h₁ h₂ hx).2
    (LevelPair.pullHom (specHom hA hA' φ) W.toEllipticCurveGeom) b rfl
  have key : (ModuliProblem.gamma _ 2).map b.op (pairOf k hA W ha₁ ha₃ h₁ h₂ hx).2 =
      (pairOf k hA' (W.map φ.toRingHom) ha₁' ha₃' h₁' h₂' hx').2 := by
    apply (ModuliProblem.gammaEquiv _).injective
    apply Subtype.ext
    refine (ModuliProblem.gammaEquiv_map (N := 2) b (pairOf k hA W ha₁ ha₃ h₁ h₂ hx).2).trans ?_
    refine (congrArg (fun ψ ↦ (EllipticCurveGeom.pointsPullback b.isPullback b.zero_total).comp ψ)
      (gammaEquiv_pairOf hA W ha₁ ha₃ h₁ h₂ hx)).trans
      (Eq.trans ?_ (gammaEquiv_pairOf hA' (W.map φ.toRingHom) ha₁' ha₃' h₁' h₂' hx').symm)
    apply hom_ext_two
    · rw [MonoidHom.comp_apply, level2_one_zero, level2_one_zero]
      exact pointsPullback_bcHom _ W φ.toRingHom _ _ h₁ |>.trans (affinePointHom_congr _ _ _ rfl (by simp))
    · rw [MonoidHom.comp_apply, level2_zero_one, level2_zero_one]
      exact pointsPullback_bcHom _ W φ.toRingHom _ _ h₂ |>.trans (affinePointHom_congr _ _ _ rfl (by simp))
  have e : (⟨(W.map φ.toRingHom).toEllipticCurveGeom, (ModuliProblem.gamma _ 2).map b.op
      (pairOf k hA W ha₁ ha₃ h₁ h₂ hx).2⟩ : LevelPair _ (specVariety A' hA')) =
        pairOf k hA' (W.map φ.toRingHom) ha₁' ha₃' h₁' h₂' hx' :=
    Sigma.ext rfl (heq_of_eq key)
  rw [← e]
  exact h

/-- Pairs built from equal data are isomorphic. -/
theorem rel_pairOf_of_eq {A : Type u} [CommRing A] [Algebra k A] (hA : IsAffineAlgebra k A)
    {W W' : WeierstrassCurve A} [W.IsElliptic] [W'.IsElliptic] (hW : W = W')
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (ha₁' : W'.a₁ = 0) (ha₃' : W'.a₃ = 0) {x₁ x₂ x₁' x₂' : A}
    (h₁ : W.toAffine.Equation x₁ 0) (h₂ : W.toAffine.Equation x₂ 0) (hx : IsUnit (x₂ - x₁))
    (h₁' : W'.toAffine.Equation x₁' 0) (h₂' : W'.toAffine.Equation x₂' 0) (hx' : IsUnit (x₂' - x₁'))
    (e₁ : x₁ = x₁') (e₂ : x₂ = x₂') :
    LevelPair.Rel (pairOf k hA W ha₁ ha₃ h₁ h₂ hx) (pairOf k hA W' ha₁' ha₃' h₁' h₂' hx') := by
  subst hW e₁ e₂
  have : ‹W.IsElliptic› = ‹W.IsElliptic› := rfl
  exact LevelPair.rel_refl _

/-- **Pairs related by a change of variables** $W = C \cdot W'$ with $s = t = 0$, carrying $(x, 0)$ to
$(u^2 x + r, 0)$, are isomorphic. -/
theorem rel_pairOf_vc {A : Type u} [CommRing A] [Algebra k A] (hA : IsAffineAlgebra k A)
    (W' : WeierstrassCurve A) [W'.IsElliptic] (C : VariableChange A) (hs : C.s = 0) (ht : C.t = 0)
    (ha₁ : (C • W').a₁ = 0) (ha₃ : (C • W').a₃ = 0) (ha₁' : W'.a₁ = 0) (ha₃' : W'.a₃ = 0) {x₁ x₂ : A}
    (h₁ : (C • W').toAffine.Equation x₁ 0) (h₂ : (C • W').toAffine.Equation x₂ 0) (hx : IsUnit (x₂ - x₁))
    (h₁' : W'.toAffine.Equation ((C.u : A) ^ 2 * x₁ + C.r) 0) (h₂' : W'.toAffine.Equation ((C.u : A) ^ 2 * x₂ + C.r) 0)
    (hx' : IsUnit (((C.u : A) ^ 2 * x₂ + C.r) - ((C.u : A) ^ 2 * x₁ + C.r))) :
    LevelPair.Rel (pairOf k hA (C • W') ha₁ ha₃ h₁ h₂ hx) (pairOf k hA W' ha₁' ha₃' h₁' h₂' hx') := by
  refine ⟨vcHom (specStructure k A) W' C, rfl, ?_⟩
  have hy (x : A) : (0 : A) = (C.u : A) ^ 3 * 0 + (C.u : A) ^ 2 * C.s * x + C.t := by simp [hs, ht]
  apply (ModuliProblem.gammaEquiv _).injective
  apply Subtype.ext
  refine (ModuliProblem.gammaEquiv_map (N := 2) (vcHom (specStructure k A) W' C)
    (pairOf k hA W' ha₁' ha₃' h₁' h₂' hx').2).trans ?_
  refine (congrArg (fun φ ↦ (EllipticCurveGeom.pointsPullback (vcHom (specStructure k A) W' C).isPullback
    (vcHom (specStructure k A) W' C).zero_total).comp φ) (gammaEquiv_pairOf hA W' ha₁' ha₃' h₁' h₂' hx')).trans
    (Eq.trans ?_ (gammaEquiv_pairOf hA (C • W') ha₁ ha₃ h₁ h₂ hx).symm)
  apply hom_ext_two
  · rw [MonoidHom.comp_apply, level2_one_zero, level2_one_zero,
      affinePointHom_congr W' h₁' ((Affine.variableChange_equation W' C x₁ 0).mpr h₁) rfl (hy x₁)]
    exact pointsPullback_vcHom _ W' C h₁
  · rw [MonoidHom.comp_apply, level2_zero_one, level2_zero_one,
      affinePointHom_congr W' h₂' ((Affine.variableChange_equation W' C x₂ 0).mpr h₂) rfl (hy x₂)]
    exact pointsPullback_vcHom _ W' C h₂

end Pairs

/-! ### The refutation -/

section Final

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]

/-- The Legendre line $T = \operatorname{Spec} k[\lambda, (\lambda(\lambda - 1))^{-1}]$. -/
abbrev legendreLine : Variety k := specVariety (LegendreRing k) isAffineAlgebra_legendreRing

/-- Its double cover $T' = \operatorname{Spec} k[s, (s(s^2 - 1))^{-1}]$, $\lambda = s^2$. -/
abbrev sqrtLine : Variety k := specVariety (LegendreSqrtRing k) isAffineAlgebra_legendreSqrtRing

/-- The double cover $T' \to T$. -/
abbrev sqrtCover : sqrtLine k ⟶ legendreLine k := specHom _ _ (legendreSqrtMap k)

variable {k}

omit [CharZero k] in
theorem exists_lift_sqrtCover (t : Variety.point k ⟶ legendreLine k) :
    ∃ t' : Variety.point k ⟶ sqrtLine k, t' ≫ sqrtCover k = t := by
  obtain ⟨φ, hφ⟩ := exists_algHom_of_point _ t
  obtain ⟨ψ, hψ⟩ := exists_algHom_comp_legendreSqrtMap φ
  refine ⟨⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom)) ?_⟩, ?_⟩
  · change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext c
    exact ψ.commutes c
  · apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map _ = _
    rw [hφ, ← Spec.map_comp, ← hψ]
    rfl

omit [IsAlgClosed k] [CharZero k] in
theorem isUnit_legendreSqrt' : IsUnit (legendreSqrt k) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := LegendreSqrtRing k)
    (Polynomial.X * (Polynomial.X ^ 2 - 1) : Polynomial k)
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_left h

omit [IsAlgClosed k] [CharZero k] in
theorem legendre_eq_zero : (legendreCurve k).toAffine.Equation 0 0 := by
  rw [Affine.equation_iff]; simp

omit [IsAlgClosed k] [CharZero k] in
theorem legendre_eq_one : (legendreCurve k).toAffine.Equation 1 0 := by
  rw [Affine.equation_iff]; simp [freyCurve]

omit [IsAlgClosed k] [CharZero k] in
theorem twist_eq_zero : (twistCurve k).toAffine.Equation 0 0 := by
  rw [Affine.equation_iff]; simp

omit [IsAlgClosed k] [CharZero k] in
theorem twist_eq_lambda : (twistCurve k).toAffine.Equation (legendreLambda k) 0 := by
  rw [Affine.equation_iff]; simp [freyCurve]; ring

/-- The Legendre curve with the basis $(0, 0), (1, 0)$ of its $2$-torsion, over $T$. -/
abbrev legendrePair : LevelPair (ModuliProblem.gamma (Spec (CommRingCat.of k)) 2) (legendreLine k) :=
  pairOf k _ (legendreCurve k) rfl rfl legendre_eq_zero legendre_eq_one (by simp)

/-- The twist with the basis $(0, 0), (\lambda, 0)$, over $T$. -/
abbrev twistPair : LevelPair (ModuliProblem.gamma (Spec (CommRingCat.of k)) 2) (legendreLine k) :=
  pairOf k _ (twistCurve k) rfl rfl twist_eq_zero twist_eq_lambda (by simpa using isUnit_legendreLambda)

/-- **The two pairs become isomorphic on the double cover.** -/
theorem rel_pull_legendre_twist :
    LevelPair.Rel (LevelPair.pull (sqrtCover k) legendrePair) (LevelPair.pull (sqrtCover k) twistPair) := by
  set φ := legendreSqrtMap k
  set σ := legendreSqrt k
  have hl : φ (legendreLambda k) = σ ^ 2 := legendreSqrtMap_lambda
  have hσ := isUnit_legendreSqrt' (k := k)
  set C : VariableChange (LegendreSqrtRing k) := ⟨hσ.unit, 0, 0, 0⟩
  set v : LegendreSqrtRing k := ((hσ.unit⁻¹ : (LegendreSqrtRing k)ˣ) : LegendreSqrtRing k)
  have hv : v * σ = 1 := by simp [v, σ]
  have hW : (legendreCurve k).map φ.toRingHom = C • (twistCurve k).map φ.toRingHom := by
    ext
    · simp [C, variableChange_a₁]
    · simp only [C, variableChange_a₂, map_a₂, freyCurve_a₂, map_a₁, freyCurve_a₁]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_neg, map_one, map_pow, hl]
      linear_combination ((v * σ + 1) * (σ ^ 2 + 1)) * hv
    · simp [C, variableChange_a₃]
    · simp only [C, variableChange_a₄, map_a₄, freyCurve_a₄, map_a₁, map_a₂, map_a₃, freyCurve_a₁, freyCurve_a₂,
        freyCurve_a₃]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_neg, map_one, map_pow, map_mul, hl,
        map_zero]
      linear_combination (-(σ ^ 2 * (v * σ + 1) * (v ^ 2 * σ ^ 2 + 1))) * hv
    · simp [C, variableChange_a₆]
  have hL0 : ((legendreCurve k).map φ.toRingHom).toAffine.Equation (φ 0) 0 := by
    simp
  have hL1 : ((legendreCurve k).map φ.toRingHom).toAffine.Equation (φ 1) 0 := by
    simpa using legendre_eq_one.map φ.toRingHom
  have hT0 : ((twistCurve k).map φ.toRingHom).toAffine.Equation (φ 0) 0 := by
    simp
  have hTl : ((twistCurve k).map φ.toRingHom).toAffine.Equation (φ (legendreLambda k)) 0 := by
    simpa using twist_eq_lambda.map φ.toRingHom
  have r1 := rel_pull_pairOf isAffineAlgebra_legendreRing isAffineAlgebra_legendreSqrtRing φ (legendreCurve k)
    rfl rfl legendre_eq_zero legendre_eq_one (by simp) (by simp) (by simp) hL0 hL1 (by simp)
  have r2 := rel_pull_pairOf isAffineAlgebra_legendreRing isAffineAlgebra_legendreSqrtRing φ (twistCurve k)
    rfl rfl twist_eq_zero twist_eq_lambda
    (by simpa using isUnit_legendreLambda) (by simp) (by simp) hT0 hTl
    (by simpa [hl] using hσ.pow 2)
  have hC0 : (C • (twistCurve k).map φ.toRingHom).toAffine.Equation 0 0 := by
    rw [← hW]; simp
  have hC1 : (C • (twistCurve k).map φ.toRingHom).toAffine.Equation 1 0 := by
    rw [← hW]; simpa using hL1
  have hCa₁ : (C • (twistCurve k).map φ.toRingHom).a₁ = 0 := by rw [← hW]; simp
  have hCa₃ : (C • (twistCurve k).map φ.toRingHom).a₃ = 0 := by rw [← hW]; simp
  have hT0' : ((twistCurve k).map φ.toRingHom).toAffine.Equation ((C.u : LegendreSqrtRing k) ^ 2 * 0 + C.r) 0 := by
    simp [C]
  have hT1' : ((twistCurve k).map φ.toRingHom).toAffine.Equation ((C.u : LegendreSqrtRing k) ^ 2 * 1 + C.r) 0 := by
    simpa [C, σ, hl] using hTl
  have r3 := rel_pairOf_of_eq isAffineAlgebra_legendreSqrtRing hW (by simp) (by simp) hCa₁ hCa₃ hL0 hL1
    (by simp) hC0 hC1 (by simp) (by simp) (by simp)
  have r4 := rel_pairOf_vc isAffineAlgebra_legendreSqrtRing ((twistCurve k).map φ.toRingHom) C rfl rfl hCa₁ hCa₃
    (by simp) (by simp) hC0 hC1
    (by simp) hT0' hT1' (by simpa [C] using hσ.pow 2)
  have r5 := rel_pairOf_of_eq isAffineAlgebra_legendreSqrtRing rfl (by simp) (by simp) (by simp) (by simp) hT0' hT1'
    (by simpa [C] using hσ.pow 2) hT0 hTl (by simpa [hl] using hσ.pow 2) (by simp [C]) (by simp [C, σ, hl])
  exact LevelPair.rel_trans r1 (LevelPair.rel_trans r3 (LevelPair.rel_trans r4
    (LevelPair.rel_trans r5 (LevelPair.rel_symm r2))))

omit [IsAlgClosed k] [CharZero k] in
theorem levelNFunctor_map_mk [IsSepClosed k] {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) (ζ : k) {V W : Variety k}
    (φ : W ⟶ V) (p : {x : LevelPair (ModuliProblem.gamma (Spec (CommRingCat.of k)) N) V //
      HasWeilPairing N hN ζ x}) :
    (levelNFunctor hN ζ).map φ.op (⟦p⟧ : Quotient (LevelNPair.setoid hN ζ V)) =
      (⟦⟨LevelPair.pull φ p.1, hasWeilPairing_pull φ p.2⟩⟧ : Quotient (LevelNPair.setoid hN ζ W)) :=
  rfl

theorem map_sqrtCover_legendre_twist (h2 : ((2 : ℕ) : k) ≠ 0) :
    (levelNFunctor (N := 2) h2 (-1 : k)).map (sqrtCover k).op
        (⟦⟨legendrePair, hasWeilPairing_two h2 legendrePair⟩⟧ : Quotient (LevelNPair.setoid h2 (-1 : k) _)) =
      (levelNFunctor (N := 2) h2 (-1 : k)).map (sqrtCover k).op
        (⟦⟨twistPair, hasWeilPairing_two h2 twistPair⟩⟧ : Quotient (LevelNPair.setoid h2 (-1 : k) _)) := by
  rw [levelNFunctor_map_mk, levelNFunctor_map_mk]
  apply Quotient.sound
  change LevelPair.Rel _ _
  exact rel_pull_legendre_twist

/-- **The moduli problem $\mathcal E_2$ has no fine moduli variety** (over an algebraically closed field of
characteristic $0$, with $\zeta = -1$). -/
theorem not_exists_isFineModuliSolution (h2 : ((2 : ℕ) : k) ≠ 0) :
    ¬ ∃ (V : Variety k) (α : (levelNFunctor (N := 2) h2 (-1 : k)).obj (op (Variety.point k)) ≃
      (Variety.point k ⟶ V)), IsFineModuliSolution.{u, u + 1} (levelNFunctor (N := 2) h2 (-1 : k)) V α := by
  rintro ⟨V, α, -, eta, -⟩
  set F := levelNFunctor (N := 2) h2 (-1 : k)
  let a : F.obj (op (legendreLine k)) := ⟦⟨legendrePair, hasWeilPairing_two h2 legendrePair⟩⟧
  let a' : F.obj (op (legendreLine k)) := ⟦⟨twistPair, hasWeilPairing_two h2 twistPair⟩⟧
  have hpull : F.map (sqrtCover k).op a = F.map (sqrtCover k).op a' := map_sqrtCover_legendre_twist h2
  have hnat : ∀ b, (eta.hom.app (op (sqrtLine k)) (F.map (sqrtCover k).op b)).down =
      sqrtCover k ≫ (eta.hom.app (op (legendreLine k)) b).down := fun b ↦ by
    have := congrArg ULift.down (ConcreteCategory.congr_hom (eta.hom.naturality (sqrtCover k).op) b)
    exact this
  have heq : (eta.hom.app (op (legendreLine k)) a).down = (eta.hom.app (op (legendreLine k)) a').down := by
    apply Variety.hom_ext_of_points
    intro t
    obtain ⟨t', rfl⟩ := exists_lift_sqrtCover t
    rw [Category.assoc, Category.assoc, ← hnat, ← hnat, hpull]
  have haa : a = a' := by
    have h := congrArg (eta.inv.app (op (legendreLine k))) (ULift.ext_iff.mpr heq)
    simpa using h
  obtain ⟨f, hf, -⟩ := Quotient.exact haa
  exact not_exists_pointedIso k (exists_pointedIso_of_hom (W := legendreCurve k) (W' := twistCurve k) _ f hf)

end Final

/-- **Milne, Example 8.9 (as corrected) is false**: over an algebraically closed field of characteristic $0$ the
moduli problem $\mathcal E_2$ has no fine moduli variety at all, in particular not the Legendre line. Level-two
structures are not rigid, and the Legendre curve and its quadratic twist by $\lambda$ are a counterexample to
representability (see the module docstring). -/
@[kb "milne2017mf" "Section 8, Example 8.9 (pdf p. 100): refuted (no fine moduli variety for N = 2)"]
theorem not_legendreFineModuli (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] :
    ¬ LegendreFineModuli k := by
  rintro ⟨V, e, -, α, hα⟩
  exact not_exists_isFineModuliSolution (k := k) (by norm_num) ⟨V, α, hα⟩

end ModularFormsKB.Milne.Ch8Counterexample

namespace ModularFormsKB.Milne

/-- **Milne, Example 8.9, corrected** (named statement): over an algebraically closed field of characteristic $0$,
the moduli problem $\mathcal E_2$ ($\zeta = -1$) has a solution (a coarse moduli variety, Definition 8.1) isomorphic over
$k$ to the Legendre line $\mathbb A^1 \smallsetminus \{0, 1\} = \operatorname{Spec} k[\lambda, (\lambda(\lambda - 1))^{-1}]$.
It is not a fine moduli variety: `Ch8Counterexample.not_legendreFineModuli` (level-two structures are not rigid). -/
@[kb "milne2017mf" "Section 8, Example 8.9 (pdf p. 100), corrected: coarse moduli variety"]
structure LegendreCoarseModuli (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] : Prop where
  coarse : ∃ (V : Variety k) (e : V.obj.left ≅ Spec (CommRingCat.of (LegendreRing k))),
    e.hom ≫ specStructure k (LegendreRing k) = V.obj.hom ∧ ∃
    (α : (levelNFunctor (N := 2) (by norm_num) (-1 : k)).obj (op (Variety.point k)) ≃ (Variety.point k ⟶ V)),
    IsModuliSolution (levelNFunctor (N := 2) (by norm_num) (-1 : k)) V α

end ModularFormsKB.Milne
