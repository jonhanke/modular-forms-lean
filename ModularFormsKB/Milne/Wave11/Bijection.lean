import ModularFormsKB.Milne.Wave11.Surjective
import TauCeti.FieldTheory.FunctionField.Place.Extension.Fundamental
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.FieldTheory.RatFunc.Automorphism

/-!
# Points of `X` and places of `M(X)`: the bijection

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §1 (pdf pp. 18–22).

Let `X` be a compact connected Riemann surface and `f` a nonconstant meromorphic function of valence `n` such that
`[M(X) : ℂ(f)] = n` (for the `ℂ(t)`-algebra structure `t ↦ f`). Then `x ↦ P_x` is a bijection from `X` onto the
places of `M(X)/ℂ`, and `ord_{P_x} = ord_x` (`pointPlace_bijective`, `ordAt_eq_ord_pointPlace`).

Proof. Fix a value `c` of `f` on the sphere and let `p_c` be the corresponding place of `ℂ(t)`, with uniformizer
`u_c = t - c` (or `1/t` for `c = ∞`). The places of `M(X)` over `p_c` are exactly the `P_y` with `f(y) = c`
(surjectivity, `Wave11.Surjective`); writing `ord_y = e_y · ord_{P_y}` and `m_y = ord_y(u_c(f))` for the local
multiplicity,
`n = ∑_{Q ∣ p_c} e(Q ∣ p_c) ≤ ∑_{f(y) = c} e(P_y ∣ p_c) ≤ ∑_{f(y) = c} e_y · e(P_y ∣ p_c) = ∑_{f(y) = c} m_y = n`
(the fundamental identity, Tau Ceti `TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isFunctionField`,
with all relative degrees `1`; and `∑ m_y = deg f`). So both inequalities are equalities: `y ↦ P_y` is injective on
the fibre and every `e_y = 1`.

The hypothesis `[M(X) : ℂ(f)] = n` holds as soon as the points of one unbranched fibre of `f` are separated by
meromorphic functions (Tau Ceti `TauCeti.RiemannSurface.MeromorphicFunction.finrank_ratFunc_eq_degree_of_pairwise_separated_fiber`),
and on `X₀(N)` for `f = j` (Milne, proof of Theorem 6.1).
-/

open TauCeti TauCeti.RiemannSurface ModularFormsKB.Milne.RiemannSurface MeromorphicFunction Polynomial
open scoped Manifold

noncomputable section

namespace ModularFormsKB.Milne.Wave11

/-! ### The places of `ℂ(t)` attached to the points of the sphere -/

/-- The uniformizer `t - c` (or `1/t` at `∞`) of the place of `ℂ(t)` at a point of the sphere. -/
def unifAt : OnePoint ℂ → RatFunc ℂ
  | (c : ℂ) => RatFunc.X - RatFunc.C c
  | OnePoint.infty => (RatFunc.X)⁻¹

/-- The place of `ℂ(t)` at a point of the sphere. -/
def placeAt : OnePoint ℂ → Place ℂ (RatFunc ℂ)
  | (c : ℂ) => Place.adicOfIrreducible (Polynomial.irreducible_X_sub_C c)
  | OnePoint.infty => Place.infty ℂ

theorem ord_placeAt_unifAt (c : OnePoint ℂ) : (placeAt c).ord (unifAt c) = 1 := by
  induction c using OnePoint.rec with
  | infty => exact Place.ord_infty_inv_X
  | coe c => exact Place.ord_adicOfIrreducible_X_sub_C_self c

theorem eq_placeAt_of_ord_pos {c : OnePoint ℂ} {P : Place ℂ (RatFunc ℂ)} (h : 0 < P.ord (unifAt c)) :
    P = placeAt c := by
  induction c using OnePoint.rec with
  | infty =>
    show P = Place.infty ℂ
    refine Place.one_lt_valuation_X_iff_eq_infty.1 ?_
    have hX0 : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
    have hv : P.valuation (RatFunc.X : RatFunc ℂ)⁻¹ < 1 :=
      (P.valuation_lt_one_iff_ord_pos (inv_ne_zero hX0)).2 h
    rw [map_inv₀] at hv
    have hpos : 0 < P.valuation (RatFunc.X : RatFunc ℂ) := by
      rw [zero_lt_iff, ne_eq, map_eq_zero]; exact hX0
    exact (inv_lt_one₀ hpos).1 hv
  | coe c => exact Place.ord_X_sub_C_pos_iff.1 h

/-- The meromorphic function on the sphere of the uniformizer at `c`. -/
theorem order_ratFuncEquiv_unifAt (c : OnePoint ℂ) : order c (ratFuncEquiv (unifAt c)) = 1 := by
  induction c using OnePoint.rec with
  | infty =>
    show order OnePoint.infty (ratFuncEquiv (RatFunc.X)⁻¹) = 1
    rw [map_inv₀, ratFuncEquiv_X, AddValuation.map_inv, order_coordinate_infty]
    rfl
  | coe c =>
    show order (c : OnePoint ℂ) (ratFuncEquiv (RatFunc.X - RatFunc.C c)) = 1
    have h1 : ratFuncEquiv (RatFunc.X - RatFunc.C c) = coordinate - algebraMap ℂ _ c := by
      rw [map_sub, ratFuncEquiv_X, ← RatFunc.algebraMap_C, ratFuncEquiv_algebraMap, aeval_C]
    rw [h1, order_apply, TauCeti.RiemannSurface.meromorphicOrderAt_def, OnePoint.chartAt_coe]
    have h : ((coordinate - algebraMap ℂ (MeromorphicFunction (OnePoint ℂ)) c).finitePart ∘
        (OnePoint.affineChart (𝕜 := ℂ)).symm) = fun z : ℂ ↦ z - c := by
      funext z
      simp only [Function.comp_apply, OnePoint.affineChart_symm_apply]
      exact finitePart_of_eq_coe (sub_apply_of_eq_coe (coordinate_apply _) (by simp [coe_algebraMap]))
    rw [h, OnePoint.affineChart_coe]
    exact meromorphicOrderAt_id_sub_const

/-- The uniformizer at `c` vanishes only at `c`. -/
theorem eq_of_order_ratFuncEquiv_unifAt_pos {c z : OnePoint ℂ} (h : 0 < order z (ratFuncEquiv (unifAt c))) :
    z = c := by
  rw [order_pos_iff] at h
  induction c using OnePoint.rec with
  | infty =>
    change ratFuncEquiv (RatFunc.X)⁻¹ z = _ at h
    rw [map_inv₀, ratFuncEquiv_X] at h
    induction z using OnePoint.rec with
    | infty => rfl
    | coe w =>
      exfalso
      by_cases hw : w = 0
      · subst hw
        have hneg : order ((0 : ℂ) : OnePoint ℂ) coordinate⁻¹ < 0 := by
          rw [AddValuation.map_inv, order_coordinate_zero]
          exact WithTop.coe_lt_coe.2 (by norm_num : (-1 : ℤ) < 0)
        rw [order_neg_iff, h] at hneg
        exact OnePoint.coe_ne_infty _ hneg
      · rw [inv_apply_of_eq_coe (coordinate_apply _) hw] at h
        exact hw (inv_eq_zero.1 (OnePoint.coe_injective h))
  | coe c =>
    change ratFuncEquiv (RatFunc.X - RatFunc.C c) z = _ at h
    have h1 : ratFuncEquiv (RatFunc.X - RatFunc.C c) = coordinate - algebraMap ℂ _ c := by
      rw [map_sub, ratFuncEquiv_X, ← RatFunc.algebraMap_C, ratFuncEquiv_algebraMap, aeval_C]
    rw [h1] at h
    induction z using OnePoint.rec with
    | infty =>
      exfalso
      have hlt : order OnePoint.infty coordinate < order OnePoint.infty (algebraMap ℂ (MeromorphicFunction (OnePoint ℂ)) c) := by
        rcases eq_or_ne c 0 with rfl | hc
        · simp only [map_zero, AddValuation.map_zero, order_coordinate_infty]
          exact WithTop.coe_lt_top _
        · rw [order_algebraMap hc, order_coordinate_infty]; decide
      have := AddValuation.map_sub_eq_of_lt_left (order OnePoint.infty) hlt
      rw [order_coordinate_infty] at this
      have hneg : order OnePoint.infty (coordinate - algebraMap ℂ (MeromorphicFunction _) c) < 0 := by
        rw [this]; decide
      rw [order_neg_iff, h] at hneg
      exact OnePoint.coe_ne_infty _ hneg
    | coe w =>
      rw [sub_apply_of_eq_coe (coordinate_apply _)
        (show (algebraMap ℂ (MeromorphicFunction (OnePoint ℂ)) c) (w : OnePoint ℂ) = (c : OnePoint ℂ) by
          simp [coe_algebraMap])] at h
      exact congrArg _ (sub_eq_zero.1 (OnePoint.coe_injective h))

/-! ### The counting argument -/

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [ConnectedSpace X] [T2Space X]
  (hF : IsFunctionField ℂ (MeromorphicFunction X)) {f : MeromorphicFunction X} (hf : IsNonconstant f)
  [Algebra (RatFunc ℂ) (MeromorphicFunction X)] [IsScalarTower ℂ (RatFunc ℂ) (MeromorphicFunction X)]
  (hX : algebraMap (RatFunc ℂ) (MeromorphicFunction X) RatFunc.X = f)

include hX in
/-- The `ℂ(t)`-algebra structure `t ↦ f` is pullback of rational functions along `f`. -/
theorem algebraMap_eq_comap :
    algebraMap (RatFunc ℂ) (MeromorphicFunction X) =
      ((comapₐ (toFiniteHolomorphicMap f hf) (toFiniteHolomorphicMap f hf).holomorphic
        (toFiniteHolomorphicMap f hf).nonconstant).comp ratFuncEquiv.toAlgHom).toRingHom := by
  have : (IsScalarTower.toAlgHom ℂ (RatFunc ℂ) (MeromorphicFunction X)) =
      ((comapₐ (toFiniteHolomorphicMap f hf) (toFiniteHolomorphicMap f hf).holomorphic
        (toFiniteHolomorphicMap f hf).nonconstant).comp ratFuncEquiv.toAlgHom) := by
    refine RatFunc.algHom_ext ?_
    rw [IsScalarTower.coe_toAlgHom', hX, AlgHom.comp_apply]
    change f = comap (toFiniteHolomorphicMap f hf) (toFiniteHolomorphicMap f hf).holomorphic
      (toFiniteHolomorphicMap f hf).nonconstant (ratFuncEquiv RatFunc.X)
    rw [ratFuncEquiv_X, comap_coordinate]
  rw [← this]
  rfl

include hX in
theorem algebraMap_eq_comap_apply (r : RatFunc ℂ) :
    algebraMap (RatFunc ℂ) (MeromorphicFunction X) r =
      comap (toFiniteHolomorphicMap f hf) (toFiniteHolomorphicMap f hf).holomorphic
        (toFiniteHolomorphicMap f hf).nonconstant (ratFuncEquiv r) := by
  rw [algebraMap_eq_comap hf hX]
  rfl

include hX in
/-- The order at `y` of `u_c(f)` is the local multiplicity of `f` at `y`, for `c = f(y)`. -/
theorem ordAt_unifAt (y : X) :
    ordAt y (algebraMap (RatFunc ℂ) (MeromorphicFunction X) (unifAt (f y))) =
      localMultiplicity (toFiniteHolomorphicMap f hf) y := by
  set β := toFiniteHolomorphicMap f hf
  have hne : algebraMap (RatFunc ℂ) (MeromorphicFunction X) (unifAt (f y)) ≠ 0 := by
    rw [_root_.map_ne_zero]
    intro h0
    have := order_ratFuncEquiv_unifAt (f y)
    rw [h0, map_zero, AddValuation.map_zero] at this
    exact WithTop.top_ne_coe this
  have h := meromorphicOrderAt_finitePart_comap (⇑β) β.holomorphic β.nonconstant (ratFuncEquiv (unifAt (f y))) y
  rw [← order_apply, ← order_apply] at h
  change _ = order (f y) (ratFuncEquiv (unifAt (f y))) * _ at h
  rw [order_ratFuncEquiv_unifAt, one_mul, ← algebraMap_eq_comap_apply hf hX, ← coe_ordAt hne] at h
  exact_mod_cast h

variable [FiniteDimensional (RatFunc ℂ) (MeromorphicFunction X)]

include hX in
/-- A point lies over `placeAt (f y)`. -/
theorem restrict_pointPlace (y : X) :
    (pointPlace hF hf y).restrict ℂ (RatFunc ℂ) = placeAt (f y) := by
  refine eq_placeAt_of_ord_pos ?_
  rw [← Place.ord_algebraMap_pos_iff ℂ (RatFunc ℂ)]
  have hm := ordAt_unifAt hf hX y
  have hne : algebraMap (RatFunc ℂ) (MeromorphicFunction X) (unifAt (f y)) ≠ 0 := by
    intro h0; rw [h0] at hm; simp [ordAt] at hm
    exact (localMultiplicity_pos (toFiniteHolomorphicMap f hf) y).ne' (by exact_mod_cast hm.symm)
  rw [ord_pointPlace_pos_iff hF hf y hne, hm]
  exact_mod_cast localMultiplicity_pos (toFiniteHolomorphicMap f hf) y

include hX in
/-- A point whose place lies over `placeAt c` lies over `c`. -/
theorem apply_eq_of_restrict_pointPlace {y : X} {c : OnePoint ℂ}
    (h : (pointPlace hF hf y).restrict ℂ (RatFunc ℂ) = placeAt c) : f y = c := by
  rw [restrict_pointPlace hF hf hX y] at h
  set β := toFiniteHolomorphicMap f hf
  have hP : 0 < (pointPlace hF hf y).ord (algebraMap (RatFunc ℂ) (MeromorphicFunction X) (unifAt c)) := by
    have := Place.ramificationIdx_pos (RatFunc ℂ) (pointPlace hF hf y)
    rw [Place.ord_algebraMap_restrict ℂ (RatFunc ℂ), restrict_pointPlace hF hf hX y, h, ord_placeAt_unifAt,
      mul_one]
    exact_mod_cast this
  have hne : algebraMap (RatFunc ℂ) (MeromorphicFunction X) (unifAt c) ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hP; exact lt_irrefl _ hP
  have hpos := (ord_pointPlace_pos_iff hF hf y hne).1 hP
  have hu0 : unifAt c ≠ 0 := by
    intro h0; have := ord_placeAt_unifAt c; rw [h0, Place.ord_zero] at this; exact zero_ne_one this
  have hr0 : ratFuncEquiv (unifAt c) ≠ 0 := by
    intro h0; exact hu0 (ratFuncEquiv.injective (h0.trans (map_zero _).symm))
  have hord := meromorphicOrderAt_finitePart_comap (⇑β) β.holomorphic β.nonconstant (ratFuncEquiv (unifAt c)) y
  rw [← order_apply, ← order_apply, ← algebraMap_eq_comap_apply hf hX, ← coe_ordAt hne] at hord
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 ((order (β y)).ne_top_iff.2 hr0)
  rw [← hk, ← WithTop.coe_natCast, ← WithTop.coe_mul] at hord
  have hkm := WithTop.coe_injective hord
  have hm : (0 : ℤ) < localMultiplicity β y := by exact_mod_cast localMultiplicity_pos β y
  have hk0 : 0 < k := by
    by_contra hk0
    push Not at hk0
    nlinarith
  have hz : 0 < order (β y) (ratFuncEquiv (unifAt c)) := by
    rw [← hk]; exact_mod_cast hk0
  exact eq_of_order_ratFuncEquiv_unifAt_pos hz

variable (hdeg : Module.finrank (RatFunc ℂ) (MeromorphicFunction X) = degree (toFiniteHolomorphicMap f hf))

include hX hdeg in
/-- **The counting argument** over the value `c = f(y₀)`: on the fibre of `f` over `c`, the map `y ↦ P_y` is
injective and every `e_y` is `1`. -/
theorem fiber_count (c : OnePoint ℂ) :
    Set.InjOn (pointPlace hF hf) ((toFiniteHolomorphicMap f hf) ⁻¹' {c}) ∧
      ∀ y ∈ (toFiniteHolomorphicMap f hf) ⁻¹' {c}, ∀ g : MeromorphicFunction X, g ≠ 0 →
        ordAt y g = (pointPlace hF hf y).ord g := by
  classical
  set β := toFiniteHolomorphicMap f hf
  set P := pointPlace hF hf
  set S := (β.finite_fiber c).toFinset
  set T := (Place.finite_setOf_restrict_eq (k' := ℂ) (F' := MeromorphicFunction X) ℂ (RatFunc ℂ)
    (placeAt c)).toFinset
  have hβ : ∀ y, (β : X → OnePoint ℂ) y = f y := fun _ ↦ rfl
  have hmemS : ∀ y, y ∈ S ↔ f y = c := fun y ↦ by simp [S, hβ]
  have hmemT : ∀ Q, Q ∈ T ↔ Q.restrict ℂ (RatFunc ℂ) = placeAt c := fun Q ↦ by simp [T]
  -- ramification indices `e(P_y ∣ p_c)` and the factors `e_y`
  have hram : ∀ y ∈ S, (P y).ord (algebraMap (RatFunc ℂ) (MeromorphicFunction X) (unifAt c)) =
      Place.ramificationIdx (RatFunc ℂ) (P y) := by
    intro y hy
    rw [Place.ord_algebraMap_restrict ℂ (RatFunc ℂ), restrict_pointPlace hF hf hX y, (hmemS y).1 hy, ord_placeAt_unifAt, mul_one]
  choose e he hord using exists_order_eq_mul_ord hF hf
  have hmult : ∀ y ∈ S, (localMultiplicity β y : ℤ) = e y * Place.ramificationIdx (RatFunc ℂ) (P y) := by
    intro y hy
    have hc : f y = c := (hmemS y).1 hy
    have hm := ordAt_unifAt hf hX y
    rw [hc] at hm
    have hne : algebraMap (RatFunc ℂ) (MeromorphicFunction X) (unifAt c) ≠ 0 := by
      intro h0; rw [h0] at hm; simp [ordAt] at hm
      exact (localMultiplicity_pos β y).ne' (by exact_mod_cast hm.symm)
    rw [← hm, hord y _ hne, hram y hy]
  -- the fundamental identity, with all relative degrees `1`
  have hrel : ∀ Q : Place ℂ (MeromorphicFunction X), Place.relativeDegree ℂ (RatFunc ℂ) Q = 1 := by
    intro Q
    have h := Place.finrank_mul_degree_eq_relativeDegree_mul_degree_restrict (k := ℂ) (k' := ℂ) (F := RatFunc ℂ) Q
    rw [Module.finrank_self, one_mul, Q.degree_eq_one_of_isAlgClosed_of_isFunctionField hF,
      (Q.restrict ℂ (RatFunc ℂ)).degree_eq_one_of_isAlgClosed_of_isFunctionField (IsFunctionField.ratFunc ℂ),
      mul_one] at h
    exact h.symm
  have hfund : ∑ Q ∈ T, Place.ramificationIdx (RatFunc ℂ) Q = degree β := by
    have h := Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isFunctionField (k' := ℂ)
      (F' := MeromorphicFunction X) ℂ (RatFunc ℂ) (IsFunctionField.ratFunc ℂ) (placeAt c) (s := T) hmemT
    simp only [hrel, mul_one] at h
    rw [h, hdeg]
  have hfib : ∑ y ∈ S, (localMultiplicity β y : ℤ) = degree β := by
    rw [degree_eq_fiber_sum β c]; push_cast; rfl
  -- `P` maps `S` onto `T`
  have hmaps : ∀ y ∈ S, P y ∈ T := fun y hy ↦ by
    rw [hmemT, restrict_pointPlace hF hf hX y, (hmemS y).1 hy]
  have honto : ∀ Q ∈ T, ∃ y ∈ S, P y = Q := by
    intro Q hQ
    obtain ⟨y, hy⟩ := exists_pointPlace_eq hF hf Q
    refine ⟨y, (hmemS y).2 (apply_eq_of_restrict_pointPlace hF hf hX ?_), hy⟩
    rw [hy]; exact (hmemT Q).1 hQ
  -- the two inequalities
  set w : Place ℂ (MeromorphicFunction X) → ℤ := fun Q ↦ Place.ramificationIdx (RatFunc ℂ) Q
  have hw1 : ∀ Q, 1 ≤ w Q := fun Q ↦ by
    have := Place.ramificationIdx_pos (RatFunc ℂ) Q; simp only [w]; omega
  have hfiber : ∑ y ∈ S, w (P y) = ∑ Q ∈ T, ((S.filter fun y ↦ P y = Q).card : ℤ) * w Q := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun Q _ ↦ ?_
    rw [Finset.sum_congr rfl fun y hy ↦ by rw [(Finset.mem_filter.1 hy).2], Finset.sum_const, nsmul_eq_mul]
  have hcard1 : ∀ Q ∈ T, 1 ≤ ((S.filter fun y ↦ P y = Q).card : ℤ) := by
    intro Q hQ
    obtain ⟨y, hy, hyQ⟩ := honto Q hQ
    have : 0 < (S.filter fun y ↦ P y = Q).card := Finset.card_pos.2 ⟨y, Finset.mem_filter.2 ⟨hy, hyQ⟩⟩
    omega
  have he1 : ∀ y ∈ S, 1 ≤ e y := fun y _ ↦ by have := he y; omega
  have hA : ∑ Q ∈ T, w Q ≤ ∑ Q ∈ T, ((S.filter fun y ↦ P y = Q).card : ℤ) * w Q :=
    Finset.sum_le_sum fun Q hQ ↦ le_mul_of_one_le_left (by linarith [hw1 Q]) (hcard1 Q hQ)
  have hB : ∑ y ∈ S, w (P y) ≤ ∑ y ∈ S, e y * w (P y) :=
    Finset.sum_le_sum fun y hy ↦ le_mul_of_one_le_left (by linarith [hw1 (P y)]) (he1 y hy)
  have hT : ∑ Q ∈ T, w Q = degree β := by simp only [w]; exact_mod_cast hfund
  have hS : ∑ y ∈ S, e y * w (P y) = degree β := by
    rw [← hfib]; exact Finset.sum_congr rfl fun y hy ↦ (hmult y hy).symm
  -- so both are equalities
  have hA' : ∀ Q ∈ T, ((S.filter fun y ↦ P y = Q).card : ℤ) = 1 := by
    have heq : ∑ Q ∈ T, w Q = ∑ Q ∈ T, ((S.filter fun y ↦ P y = Q).card : ℤ) * w Q := by
      linarith [hA, hB, hT, hS, hfiber]
    intro Q hQ
    have := (Finset.sum_eq_sum_iff_of_le fun Q hQ ↦
      le_mul_of_one_le_left (by linarith [hw1 Q]) (hcard1 Q hQ)).1 heq Q hQ
    have hwQ := hw1 Q
    nlinarith
  have hB' : ∀ y ∈ S, e y = 1 := by
    have heq : ∑ y ∈ S, w (P y) = ∑ y ∈ S, e y * w (P y) := by linarith [hA, hB, hT, hS, hfiber]
    intro y hy
    have := (Finset.sum_eq_sum_iff_of_le fun y hy ↦
      le_mul_of_one_le_left (by linarith [hw1 (P y)]) (he1 y hy)).1 heq y hy
    have hwy := hw1 (P y)
    nlinarith
  refine ⟨fun y hy y' hy' hyy' ↦ ?_, fun y hy g hg ↦ ?_⟩
  · have hyS : y ∈ S := (β.finite_fiber c).mem_toFinset.2 hy
    have hy'S : y' ∈ S := (β.finite_fiber c).mem_toFinset.2 hy'
    have h1 := hA' (P y) (hmaps y hyS)
    rw [Nat.cast_eq_one, Finset.card_eq_one] at h1
    obtain ⟨a, ha⟩ := h1
    have hya : y ∈ S.filter fun z ↦ P z = P y := Finset.mem_filter.2 ⟨hyS, rfl⟩
    have hy'a : y' ∈ S.filter fun z ↦ P z = P y := Finset.mem_filter.2 ⟨hy'S, hyy'.symm⟩
    rw [ha, Finset.mem_singleton] at hya hy'a
    rw [hya, hy'a]
  · rw [hord y g hg, hB' y ((β.finite_fiber c).mem_toFinset.2 hy), one_mul]

include hX hdeg in
/-- **`x ↦ P_x` is a bijection from `X` onto the places of `M(X)/ℂ`.** -/
theorem pointPlace_bijective : Function.Bijective (pointPlace hF hf) := by
  refine ⟨fun y y' h ↦ ?_, fun Q ↦ exists_pointPlace_eq hF hf Q⟩
  have hc : f y' = f y := apply_eq_of_restrict_pointPlace hF hf hX (by rw [← h]; exact restrict_pointPlace hF hf hX y)
  exact (fiber_count hF hf hX hdeg (f y)).1 rfl hc h

include hX hdeg in
/-- **The order of `P_x` is the analytic order at `x`.** -/
theorem ordAt_eq_ord_pointPlace (y : X) (g : MeromorphicFunction X) (hg : g ≠ 0) :
    ordAt y g = (pointPlace hF hf y).ord g :=
  (fiber_count hF hf hX hdeg (f y)).2 y rfl g hg

end ModularFormsKB.Milne.Wave11
