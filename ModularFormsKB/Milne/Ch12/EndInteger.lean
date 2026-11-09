import ModularFormsKB.Milne.Ch12.GaloisCM
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Differential
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Kernel
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Differential
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.FixedField
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Genus
import ModularFormsKB.Citation
/-!
# Milne, Section 12: elliptic curves over $\mathbb R$ have no complex multiplication over $\mathbb R$

Used to refute the named statement `SerreTateFreeTateModule` as formalized (see `docs/updates-and-errata.md`).

## Items

- `exists_pullbackDifferential_eq_smul` (Silverman, *The Arithmetic of Elliptic Curves*, III.5.2): over an
  algebraically closed field, every endomorphism pulls the invariant differential back to a constant multiple of it.
  Proof: $f^*\omega = h\omega$ with $h$ in the function field; $\omega$ is translation invariant and
  $\tau_P^* f^* = f^* \tau_{f(P)}^*$, so $h$ is fixed by every translation. A non-constant $h$ would make the function
  field finite over $k(h)$, with finitely many automorphisms, while the translations by the infinitely many points
  are pairwise distinct automorphisms fixing $k(h)$.
-/

open TauCeti TauCeti.Isogeny WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve Classical IntermediateField

namespace ModularFormsKB.Milne

namespace EndInteger

section AlgClosed

variable {F : Type*} [Field F] [IsAlgClosed F]

/-- Over an algebraically closed field an elliptic curve has infinitely many points: every `x` is the
`x`-coordinate of a point. -/
theorem infinite_point (W : WeierstrassCurve.Affine F) [W.IsElliptic] : Infinite W.Point := by
  have hy : ∀ x : F, ∃ y : F, W.Equation x y := by
    intro x
    set p : Polynomial F := Polynomial.C 1 * Polynomial.X ^ 2 + Polynomial.C (W.a₁ * x + W.a₃) * Polynomial.X +
      Polynomial.C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) with hp
    have hdeg : p.degree ≠ 0 := by
      rw [hp, Polynomial.degree_quadratic one_ne_zero]
      decide
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root p hdeg
    refine ⟨y, ?_⟩
    rw [WeierstrassCurve.Affine.equation_iff]
    have : p.eval y = 0 := hy
    rw [hp] at this
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X] at this
    linear_combination this
  choose y hy using hy
  have hns : ∀ x, W.Nonsingular x (y x) := fun x => (W.equation_iff_nonsingular).mp (hy x)
  refine Infinite.of_injective (fun x => Point.some x (y x) (hns x)) fun x x' h => ?_
  simp only [Point.some.injEq] at h
  exact h.1

variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]

open scoped RatFunc in
/-- **A function fixed by every translation is constant.** -/
theorem mem_range_of_forall_translation {h : W.FunctionField}
    (hfix : ∀ P : (W⁄F).toAffine.Point, translation W P h = h) :
    h ∈ Set.range (algebraMap F W.FunctionField) := by
  by_contra hn
  have htr : Transcendental F h := by
    intro halg
    exact hn ((isIntegrallyClosedIn_functionField W).isIntegral_iff.mp halg.isIntegral)
  have : FiniteDimensional F⟮h⟯ W.FunctionField := FunctionField.finiteDimensional_of_adjoin_transcendental htr
  have hmem : ∀ P : (W⁄F).toAffine.Point, translation W P ∈ (F⟮h⟯).fixingSubgroup := by
    intro P
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    have hle : F⟮h⟯ ≤ IntermediateField.fixedField (Subgroup.zpowers (translation W P)) := by
      rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
      intro σ hσ
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
      have : translation W P ^ n = translation W (n • P) := by
        exact ((translationHom W).map_zpow (Multiplicative.ofAdd P) n).symm
      rw [this]
      exact hfix _
    exact (IntermediateField.mem_fixedField_iff _ _).mp (hle hz) _ (Subgroup.mem_zpowers _)
  let g : (W⁄F).toAffine.Point → (W.FunctionField ≃ₐ[F⟮h⟯] W.FunctionField) := fun P =>
    IntermediateField.fixingSubgroupEquiv F⟮h⟯ ⟨translation W P, hmem P⟩
  have hg : Function.Injective g := by
    intro P Q hPQ
    apply translation_injective W
    have := congrArg Subtype.val ((IntermediateField.fixingSubgroupEquiv F⟮h⟯).injective hPQ)
    exact this
  have := infinite_point (W⁄F).toAffine
  have := Finite.of_injective g hg
  exact not_finite (W⁄F).toAffine.Point

/-- For a separable isogeny over an algebraically closed field the pullback of the invariant differential is a constant
multiple of it. -/
theorem exists_pullbackDifferential_eq_smul_of_isogeny (φ : Isogeny W W)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField] :
    ∃ c : F, φ.pullbackDifferential (invariantDifferential W) = c • invariantDifferential W := by
  obtain ⟨h, hh, -⟩ := existsUnique_smul_invariantDifferential W (φ.pullbackDifferential (invariantDifferential W))
  have hfix : ∀ P : W.Point, translation W (Point.equivBaseChangeSelf W P) h = h := by
    intro P
    set τ := translation W (Point.equivBaseChangeSelf W P)
    set ρ := translation W (Point.equivBaseChangeSelf W (φ.toPointHom P))
    have hcomm : τ.toAlgHom.comp φ.fieldPullback = φ.fieldPullback.comp ρ.toAlgHom :=
      AlgHom.ext fun z => φ.translation_fieldPullback P z
    have key : KaehlerDifferential.mapSemilinear τ.toAlgHom (φ.pullbackDifferential (invariantDifferential W)) =
        φ.pullbackDifferential (invariantDifferential W) := by
      rw [pullbackDifferential_apply, ← KaehlerDifferential.mapSemilinear_comp_apply, hcomm,
        KaehlerDifferential.mapSemilinear_comp_apply, mapSemilinear_translation_invariantDifferential]
    rw [← hh, KaehlerDifferential.mapSemilinear_smul, mapSemilinear_translation_invariantDifferential] at key
    exact smul_left_injective _ (invariantDifferential_ne_zero W) key
  have hfix' : ∀ P : (W⁄F).toAffine.Point, translation W P h = h := by
    intro P
    obtain ⟨Q, rfl⟩ := (Point.equivBaseChangeSelf W).surjective P
    exact hfix Q
  obtain ⟨c, rfl⟩ := mem_range_of_forall_translation W hfix'
  exact ⟨c, by rw [← hh, algebraMap_smul]⟩

/-- **Silverman III.5.2**: over an algebraically closed field every endomorphism pulls the invariant differential back
to a constant multiple of it. -/
theorem exists_pullbackDifferential_eq_smul (f : Hom W W) :
    ∃ c : F, f.pullbackDifferential (invariantDifferential W) = c • invariantDifferential W := by
  rcases f.eq_zero_or_exists_ofIsogeny with rfl | ⟨φ, rfl⟩
  · exact ⟨0, by simp⟩
  rw [Hom.pullbackDifferential_ofIsogeny]
  by_cases h0 : φ.pullbackDifferential (invariantDifferential W) = 0
  · exact ⟨0, by rw [h0, zero_smul]⟩
  have : Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField :=
    (isSeparable_iff_pullbackDifferential_ne_zero φ).mpr h0
  exact exists_pullbackDifferential_eq_smul_of_isogeny W φ

end AlgClosed

section Real

variable (W : WeierstrassCurve.Affine ℝ) [W.IsElliptic]

/-- Over $\mathbb R$ the pullback of the invariant differential along an endomorphism is a **real** multiple of it:
over $\mathbb C$ it is a constant multiple, and a function of $\mathbb R(E)$ that becomes constant over $\mathbb C$ is
algebraic over $\mathbb R$, hence constant ($\mathbb R$ is the exact field of constants). -/
theorem exists_real_pullbackDifferential (f : Hom W W) :
    ∃ r : ℝ, f.pullbackDifferential (invariantDifferential W) = r • invariantDifferential W := by
  obtain ⟨h, hh, -⟩ := existsUnique_smul_invariantDifferential W (f.pullbackDifferential (invariantDifferential W))
  obtain ⟨c, hc⟩ := exists_pullbackDifferential_eq_smul (W.map (algebraMap ℝ ℂ)) (f.map (algebraMap ℝ ℂ))
  have hmap : FunctionField.mapDifferential W (algebraMap ℝ ℂ) (f.pullbackDifferential (invariantDifferential W)) =
      (f.map (algebraMap ℝ ℂ)).pullbackDifferential (invariantDifferential (W.map (algebraMap ℝ ℂ))) := by
    rcases f.eq_zero_or_exists_ofIsogeny with rfl | ⟨φ, rfl⟩
    · simp [Hom.zero_map]
    · rw [Hom.ofIsogeny_map, Hom.pullbackDifferential_ofIsogeny, Hom.pullbackDifferential_ofIsogeny]
      exact mapDifferential_pullback_invariantDifferential φ _
  rw [← hh, (FunctionField.mapDifferential W _).map_smulₛₗ, FunctionField.mapDifferential_invariantDifferential, hc,
    ← algebraMap_smul (W.map (algebraMap ℝ ℂ)).FunctionField c] at hmap
  have hM : FunctionField.map W (algebraMap ℝ ℂ) h = algebraMap ℂ _ c :=
    smul_left_injective _ (invariantDifferential_ne_zero _) hmap
  have hcomp : (FunctionField.map W (algebraMap ℝ ℂ) : W.FunctionField →+* _).comp
      (algebraMap ℝ W.FunctionField) = (algebraMap ℂ (W.map (algebraMap ℝ ℂ)).FunctionField).comp
        (algebraMap ℝ ℂ) :=
    RingHom.ext fun a => FunctionField.map_algebraMap W (algebraMap ℝ ℂ) a
  have hint : IsIntegral ℝ h := by
    obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := ℝ) c
    refine ⟨p, hpm, (FunctionField.map W (algebraMap ℝ ℂ)).injective ?_⟩
    rw [map_zero, Polynomial.hom_eval₂, hcomp, hM, ← Polynomial.hom_eval₂, hp, map_zero]
  obtain ⟨r, hr⟩ := (isIntegrallyClosedIn_functionField W).isIntegral_iff.mp hint
  exact ⟨r, by rw [← hh, ← hr, algebraMap_smul]⟩

/-- An anti-self-dual endomorphism of an elliptic curve over $\mathbb R$ is zero: it squares to $-\deg$, while it
acts on the invariant differential by a real number $r$, so $r^2 = -\deg \le 0$. -/
theorem eq_zero_of_dual_eq_neg {x : Hom W W} (hx : x.dual = -x) : x = 0 := by
  obtain ⟨r, hr⟩ := exists_real_pullbackDifferential W x
  have h1 : (x * x).pullbackDifferential (invariantDifferential W) = (r * r) • invariantDifferential W := by
    rw [Hom.mul_def, Hom.pullbackDifferential_comp, LinearMap.comp_apply, hr, LinearMap.map_smul, hr, smul_smul]
  have h2 : (x * x).pullbackDifferential (invariantDifferential W) =
      (-(x.degree : ℤ)) • invariantDifferential W := by
    rw [Hom.mul_self_eq_neg_degree_of_dual_eq_neg hx, Hom.one_def, ← neg_smul,
      Hom.pullbackDifferential_zsmul_id_invariantDifferential]
  rw [h1, ← Int.cast_smul_eq_zsmul ℝ] at h2
  have h3 : (r * r + (x.degree : ℝ)) • invariantDifferential W = 0 := by
    rw [add_smul, h2, ← add_smul]
    push_cast
    simp
  rcases smul_eq_zero.mp h3 with h | h
  · have hd : (x.degree : ℝ) = 0 := by nlinarith [mul_self_nonneg r, (Nat.cast_nonneg x.degree : (0 : ℝ) ≤ _)]
    exact (Hom.degree_eq_zero_iff x).mp (by exact_mod_cast hd)
  · exact absurd h (invariantDifferential_ne_zero W)

/-- **Every endomorphism of an elliptic curve over $\mathbb R$ is multiplication by an integer.** -/
theorem mem_range_intCast (f : Hom W W) : f ∈ Set.range (Int.castRingHom (Hom W W)) := by
  set t := QuadraticMap.polar (fun h : Hom W W ↦ (h.degree : ℤ)) f 1
  have hx := eq_zero_of_dual_eq_neg W (Hom.dual_two_nsmul_sub_polar_smul_one f)
  refine Hom.mem_range_of_zsmul_mem_range (R := ℤ) (Int.cast_injective) (N := 2) two_ne_zero ⟨t, ?_⟩
  rw [sub_eq_zero] at hx
  rw [eq_intCast, ← zsmul_one, ← hx, ofNat_zsmul]

/-- The endomorphism ring of an elliptic curve over $\mathbb R$ is $\mathbb Z$. -/
noncomputable def endRingEquivInt : ℤ ≃+* Hom W W :=
  RingEquiv.ofBijective (Int.castRingHom (Hom W W)) ⟨Int.cast_injective, fun f => mem_range_intCast W f⟩

end Real

end EndInteger

open EndInteger

/-- The curve $y^2 = x^3 - x$ over $\mathbb R$. -/
def curveXCubeSubX : WeierstrassCurve ℝ := ⟨0, 0, 0, -1, 0⟩

instance : curveXCubeSubX.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  simp [curveXCubeSubX, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]

/-- **`SerreTateFreeTateModule` is false as stated** (see `docs/updates-and-errata.md`): for $K = \mathbb Q$ the order
is $R = \mathbb Z$, which is $\mathrm{End}_{\mathbb R}(E)$ for $E\colon y^2 = x^3 - x$; with $\omega = 1$ the vectors
$t$ and $\omega t = t$ are never linearly independent. -/
@[kb "milne2017mf" "Section 12, Rem. 12.12 (pdf p. 125), as formalized: refuted for K = Q"]
theorem not_serreTateFreeTateModule : ¬ SerreTateFreeTateModule := by
  intro h
  let O := TauCeti.GlobalNumberFields.maximalNumberFieldOrder ℚ
  let e : O.toSubalgebra ≃+* ℤ := Rat.ringOfIntegersEquiv
  let i : O.toSubalgebra ≃+* Hom curveXCubeSubX.toAffine curveXCubeSubX.toAffine :=
    e.trans (endRingEquivInt curveXCubeSubX.toAffine)
  have hω : ∀ x : O.toSubalgebra, ∃ a b : ℤ, x = a + b * 1 := fun x =>
    ⟨e x, 0, by
      rw [Int.cast_zero, zero_mul, add_zero]
      exact (e.symm_apply_apply x).symm.trans (eq_intCast e.symm.toRingHom (e x))⟩
  obtain ⟨t, hli, -⟩ := h.free ℝ curveXCubeSubX ℂ 2 (by norm_num) ℚ O i 1 hω
  have h1 : cmAction curveXCubeSubX ℂ 2 i 1 t = t := by
    refine TateModule.ext fun n => Subtype.ext ?_
    rw [cmAction, map_one, Hom.map_one]
    show (1 : Hom (curveXCubeSubX⁄ℂ).toAffine (curveXCubeSubX⁄ℂ).toAffine).pointMap _ = _
    rw [Hom.one_def, Hom.id_pointMap]
    rfl
  rw [h1] at hli
  exact zero_ne_one (hli.injective (by simp) : (0 : Fin 2) = 1)

end ModularFormsKB.Milne
