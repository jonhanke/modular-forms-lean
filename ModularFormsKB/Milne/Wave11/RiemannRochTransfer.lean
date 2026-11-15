import ModularFormsKB.Milne.Wave11.Bijection
import ModularFormsKB.Milne.RS.HurwitzOrder
import ModularFormsKB.Milne.Wave4A.CanonicalClass
import ModularFormsKB.Milne.RiemannSurface.Examples
import TauCeti.FieldTheory.FunctionField.Differential.Comparison
import TauCeti.FieldTheory.FunctionField.Different.Tame
import TauCeti.FieldTheory.FunctionField.RiemannRoch.Uniqueness

/-!
# Riemann–Roch on a compact Riemann surface from the degree of one meromorphic function

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Theorem 1.20 (Riemann–Roch, pdf p. 21).

Let `X` be a compact connected Riemann surface with a nonconstant meromorphic function `f` of valence `n` such that
`[M(X) : ℂ(f)] = n`. The bijection `x ↦ P_x` of `X` with the places of `M(X)/ℂ`, which identifies the analytic
orders with the orders of the places (`Wave11.Bijection`), carries:

* divisors on `X` to divisors of `M(X)/ℂ`, preserving degrees (all places have degree one), `L(D)` to the
  Riemann–Roch space of Tau Ceti (`ell_eq_dim`), and principal divisors to principal divisors;
* the divisor of the differential `df` to `-2 (f)_∞ + Diff(M(X)/ℂ(f))`, the divisor of the Weil differential `df`
  (Tau Ceti `TauCeti.weilDifferentialDivisor_weilDifferentialOfSeparating`, Stichtenoth 4.3.7 (c)): at a point `y`
  with local multiplicity `m`, `ord_y(df) = m - 1` (or `-m - 1` at a pole), and the different exponent is `e - 1 = m - 1`
  (tame ramification in characteristic zero, Tau Ceti `TauCeti.Place.isTame_of_charZero`).

So the divisor of every nonzero differential form is a Riemann–Roch divisor of `M(X)/ℂ` (Tau Ceti
`TauCeti.isRiemannRochDivisor_weilDifferentialDivisor`, Stichtenoth 1.5.15, transported along linear equivalence), and
`RiemannRochStatement X` follows (`riemannRoch_of_finrank_eq`).
-/

open TauCeti TauCeti.RiemannSurface ModularFormsKB.Milne.RiemannSurface ModularFormsKB.Milne.RS MeromorphicFunction
open TauCeti.AlgebraicGeometry
open scoped Manifold IntermediateField

noncomputable section

namespace ModularFormsKB.Milne.Wave11

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [ConnectedSpace X] [T2Space X]

/-- `ℂ` is integrally closed in every field extension: an element integral over `ℂ` is a root of a linear polynomial. -/
theorem isIntegrallyClosedIn_complex (K : Type*) [Field K] [Algebra ℂ K] : IsIntegrallyClosedIn ℂ K :=
  isIntegrallyClosedIn_iff.mpr ⟨(algebraMap ℂ K).injective, fun {x} hx ↦ by
    have hdeg := IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible hx)
    exact minpoly.mem_range_of_degree_eq_one ℂ x hdeg⟩

/-- A nonconstant meromorphic function is transcendental over `ℂ`. -/
theorem transcendental_of_isNonconstant {f : MeromorphicFunction X} (hf : IsNonconstant f) :
    Transcendental ℂ f := by
  intro halg
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible halg.isIntegral)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one ℂ f hdeg
  exact not_isNonconstant_algebraMap c (hc ▸ hf)

section Transfer

variable (hF : IsFunctionField ℂ (MeromorphicFunction X)) {f : MeromorphicFunction X} (hf : IsNonconstant f)
  [Algebra (RatFunc ℂ) (MeromorphicFunction X)] [IsScalarTower ℂ (RatFunc ℂ) (MeromorphicFunction X)]
  (hX : algebraMap (RatFunc ℂ) (MeromorphicFunction X) RatFunc.X = f)
  [FiniteDimensional (RatFunc ℂ) (MeromorphicFunction X)]
  (hdeg : Module.finrank (RatFunc ℂ) (MeromorphicFunction X) = degree (toFiniteHolomorphicMap f hf))

/-- The bijection `X ≃ {places of M(X)/ℂ}`. -/
def pointPlaceEquiv : X ≃ Place ℂ (MeromorphicFunction X) :=
  Equiv.ofBijective (pointPlace hF hf) (pointPlace_bijective hF hf hX hdeg)

/-- Divisors on `X` as divisors of `M(X)/ℂ`. -/
def pushDivisor : WeilDivisor X →+ Divisor ℂ (MeromorphicFunction X) :=
  Finsupp.mapDomain.addMonoidHom (pointPlaceEquiv hF hf hX hdeg)

theorem pushDivisor_apply (D : WeilDivisor X) (y : X) :
    pushDivisor hF hf hX hdeg D (pointPlace hF hf y) = D y := by
  show Finsupp.mapDomain (pointPlaceEquiv hF hf hX hdeg) D (pointPlaceEquiv hF hf hX hdeg y) = D y
  rw [Finsupp.mapDomain_equiv_apply, Equiv.symm_apply_apply]

theorem coeff_pushDivisor (D : WeilDivisor X) (y : X) :
    (pushDivisor hF hf hX hdeg D).coeff (pointPlace hF hf y) = D y :=
  pushDivisor_apply hF hf hX hdeg D y

include hX hdeg in
theorem pushDivisor_ext {A B : Divisor ℂ (MeromorphicFunction X)}
    (h : ∀ y, A.coeff (pointPlace hF hf y) = B.coeff (pointPlace hF hf y)) : A = B := by
  refine Finsupp.ext fun P ↦ ?_
  obtain ⟨y, rfl⟩ := (pointPlace_bijective hF hf hX hdeg).2 P
  exact h y

/-- Degrees are preserved (every place of `M(X)/ℂ` has degree one). -/
theorem degree_pushDivisor (D : WeilDivisor X) :
    Divisor.degree (pushDivisor hF hf hX hdeg D) = WeilDivisor.degree D := by
  have h : (Divisor.degree).comp (pushDivisor hF hf hX hdeg) = (WeilDivisor.degree : WeilDivisor X →+ ℤ) := by
    refine Finsupp.addHom_ext fun y n ↦ ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, pushDivisor, Finsupp.mapDomain.addMonoidHom_apply,
      Finsupp.mapDomain_single]
    rw [Divisor.degree_single, (pointPlaceEquiv hF hf hX hdeg y).degree_eq_one_of_isAlgClosed_of_isFunctionField hF,
      Nat.cast_one, mul_one]
    simp [WeilDivisor.degree, Finsupp.degree_single]
  exact DFunLike.congr_fun h D

include hX hdeg in
theorem ordAt_eq_ord (y : X) {g : MeromorphicFunction X} (hg : g ≠ 0) :
    ordAt y g = (pointPlace hF hf y).ord g :=
  ordAt_eq_ord_pointPlace hF hf hX hdeg y g hg

/-- `L(D)` on `X` is the Riemann–Roch space of the pushed divisor. -/
theorem rrSpace_eq (D : WeilDivisor X) :
    rrSpace X D = (riemannRochSpace (pushDivisor hF hf hX hdeg D) : Submodule ℂ (MeromorphicFunction X)) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp only [Submodule.zero_mem]
  rw [mem_riemannRochSpace_iff_neg_le_ord hg]
  constructor
  · intro h P
    obtain ⟨y, rfl⟩ := (pointPlace_bijective hF hf hX hdeg).2 P
    rw [coeff_pushDivisor, ← ordAt_eq_ord hF hf hX hdeg y hg]
    have := h y
    rw [← coe_ordAt hg] at this
    exact_mod_cast this
  · intro h y
    have := h (pointPlace hF hf y)
    rw [coeff_pushDivisor, ← ordAt_eq_ord hF hf hX hdeg y hg] at this
    rw [← coe_ordAt hg]
    exact_mod_cast this

theorem ell_eq_dim (D : WeilDivisor X) : ell X D = Divisor.dim (pushDivisor hF hf hX hdeg D) := by
  rw [ell, Divisor.dim_def, rrSpace_eq hF hf hX hdeg]

theorem principalDivisor_apply_eq_ordAt {g : MeromorphicFunction X} (hg : g ≠ 0) (y : X) :
    principalDivisor X g y = ordAt y g := by
  have h := coe_principalDivisor_apply hg y
  rw [← coe_ordAt hg] at h
  exact_mod_cast h

/-- Principal divisors go to principal divisors. -/
theorem pushDivisor_principal {g : MeromorphicFunction X} (hg : g ≠ 0) :
    pushDivisor hF hf hX hdeg (principalDivisor X g) = Divisor.principal hF (Units.mk0 g hg) := by
  refine pushDivisor_ext hF hf hX hdeg fun y ↦ ?_
  rw [coeff_pushDivisor, Divisor.coeff_principal, Units.val_mk0, principalDivisor_apply_eq_ordAt hg,
    ordAt_eq_ord hF hf hX hdeg y hg]

end Transfer

/-! ### The canonical divisor -/

section Canonical

variable (hF : IsFunctionField ℂ (MeromorphicFunction X)) {f : MeromorphicFunction X} (hf : IsNonconstant f)

open scoped Classical in
/-- The order of `df` at `y`: `m - 1` where `f` is finite, `-m - 1` at a pole, `m` the local multiplicity. -/
theorem ordZ_differential (y : X) :
    (differential f).ordZ y =
      if f y = OnePoint.infty then -(localMultiplicity (toFiniteHolomorphicMap f hf) y : ℤ) - 1
      else (localMultiplicity (toFiniteHolomorphicMap f hf) y : ℤ) - 1 := by
  set β := toFiniteHolomorphicMap f hf
  have hpull : pullbackFun β coordinate = f := comap_coordinate hf
  have h := ord_differential_pullbackFun β coordinate y
  rw [hpull] at h
  have hz := coe_ordZ (differential_not_isZero hf) y
  rw [h] at hz
  have hβ : (β : X → OnePoint ℂ) y = f y := rfl
  rw [hβ] at hz
  split_ifs with hy
  · rw [hy, ord_differential_coordinate_infty] at hz
    have h2 : ((differential f).ordZ y : WithTop ℤ) =
        (((-2) * (localMultiplicity β y : ℤ) + ((localMultiplicity β y : ℤ) - 1) : ℤ) : WithTop ℤ) := by
      rw [hz]; norm_cast
    have h3 := WithTop.coe_injective h2
    linarith
  · obtain ⟨z, hz'⟩ := OnePoint.ne_infty_iff_exists.1 hy
    rw [← hz', ord_differential_coordinate_coe, zero_mul, zero_add] at hz
    exact_mod_cast hz

variable [Algebra (RatFunc ℂ) (MeromorphicFunction X)] [IsScalarTower ℂ (RatFunc ℂ) (MeromorphicFunction X)]
  (hX : algebraMap (RatFunc ℂ) (MeromorphicFunction X) RatFunc.X = f)
  [FiniteDimensional (RatFunc ℂ) (MeromorphicFunction X)] [Algebra.IsSeparable (RatFunc ℂ) (MeromorphicFunction X)]
  (hdeg : Module.finrank (RatFunc ℂ) (MeromorphicFunction X) = degree (toFiniteHolomorphicMap f hf))

include hX hdeg in
/-- The ramification index of `P_y` over `ℂ(t)` is the local multiplicity of `f` at `y`. -/
theorem ramificationIdx_pointPlace (y : X) :
    (Place.ramificationIdx (RatFunc ℂ) (pointPlace hF hf y) : ℤ) =
      localMultiplicity (toFiniteHolomorphicMap f hf) y := by
  have hm := ordAt_unifAt hf hX y
  have hne : algebraMap (RatFunc ℂ) (MeromorphicFunction X) (unifAt (f y)) ≠ 0 := by
    intro h0; rw [h0] at hm; simp [ordAt] at hm
    exact (localMultiplicity_pos (toFiniteHolomorphicMap f hf) y).ne' (by exact_mod_cast hm.symm)
  rw [← hm, ordAt_eq_ord_pointPlace hF hf hX hdeg y _ hne, Place.ord_algebraMap_restrict ℂ (RatFunc ℂ),
    restrict_pointPlace hF hf hX y, ord_placeAt_unifAt, mul_one]

include hX hdeg in
/-- **The divisor of `df` is `-2 (f)_∞ + Diff(M(X)/ℂ(f))`.** -/
theorem pushDivisor_differential :
    pushDivisor hF hf hX hdeg (differential f).divisor =
      (-2 : ℤ) • Divisor.poles hF (Units.mk0 f (transcendental_of_isNonconstant hf).ne_zero) +
        Divisor.different ℂ (MeromorphicFunction X) (IsFunctionField.ratFunc ℂ) := by
  refine pushDivisor_ext hF hf hX hdeg fun y ↦ ?_
  have hf0 : f ≠ 0 := (transcendental_of_isNonconstant hf).ne_zero
  rw [coeff_pushDivisor, divisor_apply_of_not_isZero (differential_not_isZero hf), ordZ_differential hf,
    WeilDivisor.coeff_add, WeilDivisor.coeff_zsmul, Divisor.coeff_poles, Units.val_mk0]
  have htame := (Divisor.coeff_different_add_one_eq_ramificationIdx_iff (k := ℂ) (F := RatFunc ℂ)
    (k' := ℂ) (F' := MeromorphicFunction X) (IsFunctionField.ratFunc ℂ) (pointPlace hF hf y)).2
    (Place.isTame_of_charZero ℂ (RatFunc ℂ) (pointPlace hF hf y))
  rw [ramificationIdx_pointPlace hF hf hX hdeg y] at htame
  have hord := ordAt_eq_ord_pointPlace hF hf hX hdeg y f hf0
  set m := (localMultiplicity (toFiniteHolomorphicMap f hf) y : ℤ)
  split_ifs with hy
  · have hpd := principalDivisor_apply_infty hf y hy
    rw [principalDivisor_apply_eq_ordAt hf0, hord] at hpd
    have : -(pointPlace hF hf y).ord f ⊔ 0 = m := by rw [hpd]; simp [m]; rfl
    rw [this]
    linarith
  · have hnn : 0 ≤ (pointPlace hF hf y).ord f := by
      rw [← hord, ordAt_nonneg_iff hf0, order_nonneg_iff]; exact hy
    have : -(pointPlace hF hf y).ord f ⊔ 0 = 0 := by omega
    rw [this]
    linarith

end Canonical

/-! ### Riemann–Roch -/

/-- **Milne, Theorem 1.20 (Riemann–Roch), for a compact Riemann surface with a function of full degree.** If a
nonconstant meromorphic function `f` on the compact connected Riemann surface `X` satisfies `[M(X) : ℂ(f)] = valence f`
(which holds as soon as the points of one unbranched fibre of `f` are separated by meromorphic functions), then
`RiemannRochStatement X` holds, with `g` the genus of the function field `M(X)/ℂ`. -/
@[kb "milne2017mf" "Theorem 1.20 (Riemann-Roch), pdf p. 21, for X with [M(X) : C(f)] = valence f"]
theorem riemannRoch_of_finrank_eq {f : MeromorphicFunction X} (hf : IsNonconstant f)
    (hdeg : Module.finrank ℂ⟮f⟯ (MeromorphicFunction X) = valence f) : RiemannRochStatement X := by
  classical
  have hF := (isFunctionField_of_exists_nonconstant ⟨⟨f, hf⟩⟩).1
  have hx := transcendental_of_isNonconstant hf
  have hex := isIntegrallyClosedIn_complex (MeromorphicFunction X)
  haveI : FiniteDimensional ℂ⟮f⟯ (MeromorphicFunction X) := hF.finiteDimensional_adjoin hx
  haveI : Algebra.IsSeparable ℂ⟮f⟯ (MeromorphicFunction X) := inferInstance
  letI := ratFuncAlgebraOfTranscendental hx
  haveI := isScalarTower_ratFuncAlgebraOfTranscendental hx
  haveI := finiteDimensional_ratFuncAlgebraOfTranscendental hx
  haveI := isSeparable_ratFuncAlgebraOfTranscendental hx
  have hX : algebraMap (RatFunc ℂ) (MeromorphicFunction X) RatFunc.X = f :=
    algebraMap_ratFuncAlgebraOfTranscendental_X hx
  have hdeg' : Module.finrank (RatFunc ℂ) (MeromorphicFunction X) = degree (toFiniteHolomorphicMap f hf) := by
    have hv : valence f = degree (toFiniteHolomorphicMap f hf) := by
      simp only [valence, if_pos hf]; rfl
    rw [← hv, ← hdeg]
    refine Algebra.finrank_eq_of_equiv_equiv (RatFunc.algEquivOfTranscendental f hx).toRingEquiv
      (RingEquiv.refl _) ?_
    ext r
    rw [RingHom.comp_apply, RingHom.comp_apply, algebraMap_ratFuncAlgebraOfTranscendental_apply]
    rfl
  -- the Weil differential `df` and its divisor
  set ω₀ := weilDifferentialOfSeparating hF hx
  have hω₀ : (ω₀ : Module.Dual ℂ ↥(repartitionSpace ℂ (MeromorphicFunction X))) ≠ 0 := by
    simpa using weilDifferentialOfSeparating_ne_zero hF hx
  have hRR₀ := isRiemannRochDivisor_weilDifferentialDivisor hF hex ω₀.2 hω₀
  have hW₀ : weilDifferentialDivisor hF hex ω₀.2 hω₀ =
      pushDivisor hF hf hX hdeg' (differential f).divisor := by
    rw [pushDivisor_differential hF hf hX hdeg']
    exact weilDifferentialDivisor_weilDifferentialOfSeparating hF hex hx
  refine ⟨fun D ↦ ?_, ⟨genus ℂ (MeromorphicFunction X), fun ω hω D ↦ ?_⟩⟩
  · rw [rrSpace_eq hF hf hX hdeg']
    exact finiteDimensional_riemannRochSpace hF _
  -- the divisor of `ω` is linearly equivalent to that of `df`
  have hdf := differential_not_isZero hf
  have hq := diffQuot_ne_zero hω hdf
  have hsplit := divisor_eq_principalDivisor_diffQuot_add hω hdf
  have hRR : (pushDivisor hF hf hX hdeg' ω.divisor).IsRiemannRochDivisor (genus ℂ (MeromorphicFunction X)) := by
    refine Divisor.IsRiemannRochDivisor.of_linearlyEquivalent hF hRR₀ ?_
    rw [Divisor.linearlyEquivalent_iff]
    refine ⟨(Units.mk0 (diffQuot ω (differential f)) hq)⁻¹, ?_⟩
    rw [hW₀, hsplit, map_add, pushDivisor_principal hF hf hX hdeg' hq]
    rw [show Divisor.principal hF (Units.mk0 (diffQuot ω (differential f)) hq)⁻¹ =
        -Divisor.principal hF (Units.mk0 (diffQuot ω (differential f)) hq) from by
      rw [Divisor.principal, Divisor.principal, ofMul_inv, map_neg]]
    abel
  have h := hRR (pushDivisor hF hf hX hdeg' D)
  rw [← map_sub, ← ell_eq_dim, ← ell_eq_dim, degree_pushDivisor] at h
  exact h

end ModularFormsKB.Milne.Wave11
