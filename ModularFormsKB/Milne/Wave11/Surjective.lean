import ModularFormsKB.Milne.Wave11.PointPlace
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Degree
import TauCeti.FieldTheory.FunctionField.Place.Approximation
import TauCeti.FieldTheory.FunctionField.Place.Degree
import TauCeti.RingTheory.Polynomial.Monic.OfCoeff

/-!
# Every place of `M(X)/ℂ` is the place of a point

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §1 (pdf pp. 18–22).

Let `X` be a compact connected Riemann surface and `g` a nonconstant meromorphic function on `X`. For every place `Q`
of the field `M(X)/ℂ` there is a point `y` of `X` with `Q = P_y` (`exists_pointPlace_eq`). The proof is the classical
one: if `Q` had no centre, let `c` be the residue of `g` at `Q` (finite, after replacing `g` by `1/g`) and choose, by
the approximation theorem (Tau Ceti `TauCeti.Place.exists_forall_mem_ord_sub_eq`), a function `G` with
`ord_Q(G) = 1` and `G = 1` at the points of the fibre `g⁻¹(c)`. The polynomial `∏ (T - G(x))` over the fibres of
`g` (Forster, Theorem 8.2) has coefficients `a_i` that are rational functions of `g`, finite at `c`, and annihilates
`G`; reducing `∑ a_i(g) G^i = 0` modulo the maximal ideal of `Q` gives `a_0(c) = 0`, while `a_0(c) = ± ∏ G(x) = ±1`.

The fibre polynomial with its coefficient values is rebuilt here (`exists_fiberPoly`) following Tau Ceti's proof of
`TauCeti.RiemannSurface.MeromorphicFunction.exists_monic_natDegree_eq_degree_eval₂_eq_zero`, whose statement does not
record the coefficients.
-/

open TauCeti TauCeti.RiemannSurface ModularFormsKB.Milne.RiemannSurface MeromorphicFunction Polynomial
open Filter Topology
open scoped Manifold

noncomputable section

namespace ModularFormsKB.Milne.Wave11

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [ConnectedSpace X] [T2Space X]

section FiberPoly

variable (β : FiniteHolomorphicMap X (OnePoint ℂ)) (G : MeromorphicFunction X)

/-- The polynomial `∏ (T - G(x))` over the fibre of `β` over `y`, counted with multiplicity. -/
def fiberPoly (y : OnePoint ℂ) : ℂ[X] :=
  (((fiberMultiset β y).map G.finitePart).map fun v ↦ Polynomial.X - C v).prod

omit [ConnectedSpace X] in
/-- Over a point whose fibre carries no pole of `G`, the elementary symmetric functions of the values of `G` along
the fibres are continuous (Tau Ceti's private `continuousAt_esymm`). -/
theorem continuousAt_esymm_fiber {y₀ : OnePoint ℂ} (hy₀ : ∀ x ∈ β ⁻¹' {y₀}, G x ≠ OnePoint.infty) (k : ℕ) :
    ContinuousAt (fun y ↦ ((fiberMultiset β y).map G.finitePart).esymm k) y₀ := by
  have han : AnalyticAt ℂ ((fun y ↦ ((fiberMultiset β y).map G.finitePart).esymm k) ∘
      (chartAt ℂ y₀).symm) (chartAt ℂ y₀ y₀) :=
    analyticAt_esymm_map_fiberMultiset β.holomorphic β.not_eventuallyConst
      (IsManifold.chart_mem_maximalAtlas y₀) (mem_chart_source ℂ y₀) (fun x hx ↦ by
        filter_upwards [G.continuous.continuousAt.eventually (isOpen_ne.mem_nhds (hy₀ x hx))]
          with x' hx'
        exact mdifferentiableAt_finitePart hx') k
  refine (han.continuousAt.comp ((chartAt ℂ y₀).continuousAt (mem_chart_source ℂ y₀))).congr ?_
  filter_upwards [(chartAt ℂ y₀).open_source.mem_nhds (mem_chart_source ℂ y₀)] with y hy
  simp only [Function.comp_apply, (chartAt ℂ y₀).left_inv hy]

/-- **The fibre polynomial of `G` with its coefficients.** A monic polynomial of degree `deg β` over `M(ℙ¹)` which,
pulled back along `β`, annihilates `G`, and whose coefficients take, over each point `y₀` whose fibre carries no pole
of `G`, the values of the coefficients of `∏ (T - G(x))` over that fibre. -/
theorem exists_fiberPoly :
    ∃ p : (MeromorphicFunction (OnePoint ℂ))[X], p.Monic ∧ p.natDegree = degree β ∧
      p.eval₂ (comapₐ β β.holomorphic β.nonconstant).toRingHom G = 0 ∧
      ∀ y₀ : OnePoint ℂ, (∀ x ∈ β ⁻¹' {y₀}, G x ≠ OnePoint.infty) → ∀ i ≤ degree β,
        p.coeff i y₀ = ↑((fiberPoly β G y₀).coeff i) := by
  set n := degree β
  set Q : OnePoint ℂ → ℂ[X] := fiberPoly β G
  have hcard (y : OnePoint ℂ) : Multiset.card ((fiberMultiset β y).map G.finitePart) = n := by
    rw [Multiset.card_map, β.card_fiberMultiset]
  have hQ (i : ℕ) (hi : i ≤ n) : (fun y ↦ (Q y).coeff i) = fun y ↦
      (-1) ^ (n - i) * ((fiberMultiset β y).map G.finitePart).esymm (n - i) := by
    funext y
    simp only [Q, fiberPoly]
    rw [Multiset.prod_X_sub_C_coeff _ (hcard y ▸ hi), hcard]
  have hmero (i : Fin n) (y : OnePoint ℂ) : MeromorphicAt (fun y ↦ (Q y).coeff i) y := by
    rw [hQ i i.2.le]
    exact (meromorphicAt_const _ y).mul (meromorphicAt_esymm_map_finitePart_fiberMultiset β G _ y)
  set A : Fin n → MeromorphicFunction (OnePoint ℂ) := fun i ↦ ofMeromorphic (hmero i)
  have hcoeffval (y₀ : OnePoint ℂ) (hy₀ : ∀ x ∈ β ⁻¹' {y₀}, G x ≠ OnePoint.infty) (i : ℕ) (hi' : i ≤ n) :
      (TauCeti.Polynomial.monicOfCoeff A).coeff i y₀ = ↑((Q y₀).coeff i) := by
    rcases hi'.lt_or_eq with hin | rfl
    · have hA := TauCeti.Polynomial.coeff_monicOfCoeff A ⟨i, hin⟩
      rw [Fin.val_mk] at hA
      rw [hA]
      refine ofMeromorphic_apply_of_continuousAt _ ?_
      rw [hQ i hi']
      exact continuousAt_const.mul (continuousAt_esymm_fiber β G hy₀ _)
    · rw [TauCeti.Polynomial.coeff_monicOfCoeff_self, MeromorphicFunction.coe_one,
        congrFun (hQ n le_rfl) y₀, Nat.sub_self, pow_zero, Multiset.esymm_zero, one_mul]
  refine ⟨TauCeti.Polynomial.monicOfCoeff A, TauCeti.Polynomial.monic_monicOfCoeff A,
    TauCeti.Polynomial.natDegree_monicOfCoeff A, ?_, hcoeffval⟩
  refine eq_of_forall_apply_eq (p := fun x ↦ ∀ x' ∈ β ⁻¹' {β x}, G x' ≠ OnePoint.infty) (fun x₀ ↦ ?_)
    fun x hx ↦ ?_
  · have hB : (β ⁻¹' (β '' {x | G x = OnePoint.infty})).Finite :=
      (G.finite_setOf_eq_infty.image β).preimage' fun y _ ↦ β.finite_fiber y
    filter_upwards [mem_codiscrete_iff_forall_mem_nhdsNE.1 hB.compl_mem_codiscrete x₀]
      with x hx x' hx' hfx'
    exact hx ⟨x', hfx', hx'⟩
  have hcoeff (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      (comapₐ β β.holomorphic β.nonconstant).toRingHom
          ((TauCeti.Polynomial.monicOfCoeff A).coeff i) x = ↑((Q (β x)).coeff i) := by
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, comapₐ_apply, comap_apply]
    exact hcoeffval (β x) hx i hi'
  rw [eval₂_eq_sum_range, TauCeti.Polynomial.natDegree_monicOfCoeff, MeromorphicFunction.coe_zero,
    sum_apply_of_eq_coe fun i hi ↦ mul_apply_of_eq_coe (hcoeff i hi)
      (pow_apply_of_eq_coe (coe_finitePart (hx x rfl)).symm i)]
  rw [← eval_eq_sum_range' (by
      simp only [Q, fiberPoly]
      rw [natDegree_multiset_prod_X_sub_C_eq_card, hcard]
      omega)]
  simp only [Q, fiberPoly]
  rw [eval_multiset_prod, Multiset.map_map]
  refine congrArg _ (Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨G.finitePart x, ?_, by simp⟩))
  exact Multiset.mem_map_of_mem _ ((mem_fiberMultiset (β.finite_fiber (β x))).2
    ⟨rfl, localMultiplicity_pos β x⟩)

/-- If `G = 1` on the fibre over `y₀`, the constant coefficient of the fibre polynomial there is `(-1)^n`. -/
theorem fiberPoly_coeff_zero_of_eq_one {y₀ : OnePoint ℂ}
    (h1 : ∀ x ∈ β ⁻¹' {y₀}, G x = ((1 : ℂ) : OnePoint ℂ)) :
    (fiberPoly β G y₀).coeff 0 = (-1) ^ degree β := by
  rw [coeff_zero_eq_eval_zero, fiberPoly, eval_multiset_prod, Multiset.map_map]
  have hmap : (fiberMultiset β y₀).map ((fun p ↦ eval 0 p) ∘ (fun v ↦ Polynomial.X - C v) ∘ G.finitePart) =
      (fiberMultiset β y₀).map fun _ ↦ (-1 : ℂ) := by
    refine Multiset.map_congr rfl fun x hx ↦ ?_
    have hβx : β x = y₀ := ((mem_fiberMultiset (β.finite_fiber y₀)).1 hx).1
    simp [finitePart_of_eq_coe (h1 x hβx)]
  rw [Multiset.map_map]
  refine (congrArg Multiset.prod hmap).trans ?_
  rw [Multiset.map_const', Multiset.prod_replicate, β.card_fiberMultiset]

end FiberPoly

section Valuation

variable {F : Type*} [Field F] [Algebra ℂ F] (Q : Place ℂ F)

/-- A polynomial in an integral element `g` with `g ≡ c` is congruent to its value at `c`. -/
theorem valuation_aeval_sub_lt_one {g : F} {c : ℂ} (hg : Q.valuation g ≤ 1)
    (hgc : Q.valuation (g - algebraMap ℂ F c) < 1) (p : ℂ[X]) :
    Q.valuation (aeval g p - algebraMap ℂ F (p.eval c)) < 1 := by
  have hint : ∀ q : ℂ[X], Q.valuation (aeval g q) ≤ 1 := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add]
      exact (Q.valuation.map_add _ _).trans (max_le hp hq)
    | monomial n a =>
      rw [aeval_monomial, map_mul, map_pow]
      rcases eq_or_ne a 0 with rfl | ha
      · simp
      · rw [Q.isTrivialOn.eq_one a ha, one_mul]
        exact pow_le_one₀ zero_le hg
  obtain ⟨q, hq⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := c) (p := p)
  have h : aeval g p - algebraMap ℂ F (p.eval c) = (g - algebraMap ℂ F c) * aeval g q := by
    have := congrArg (aeval g) hq
    simpa [map_sub, aeval_C] using this
  rw [h, map_mul]
  calc Q.valuation (g - algebraMap ℂ F c) * Q.valuation (aeval g q)
      ≤ Q.valuation (g - algebraMap ℂ F c) * 1 := by gcongr; exact hint q
    _ < 1 := by rwa [mul_one]

/-- A function congruent to a nonzero constant is a unit at `Q`. -/
theorem valuation_eq_one_of_sub_lt_one {u : F} {a : ℂ} (ha : a ≠ 0) (h : Q.valuation (u - algebraMap ℂ F a) < 1) :
    Q.valuation u = 1 := by
  have h1 : Q.valuation (algebraMap ℂ F a) = 1 := Q.isTrivialOn.eq_one a ha
  have : u = (u - algebraMap ℂ F a) + algebraMap ℂ F a := by ring
  rw [this, Valuation.map_add_eq_of_lt_right _ (by rwa [h1]), h1]

end Valuation

section Comap

variable {g : MeromorphicFunction X} (hg : IsNonconstant g)

/-- Pulling back the coordinate along `g` gives `g`. -/
theorem comap_coordinate :
    comap (toFiniteHolomorphicMap g hg) (toFiniteHolomorphicMap g hg).holomorphic
      (toFiniteHolomorphicMap g hg).nonconstant coordinate = g :=
  MeromorphicFunction.ext fun x ↦ by simp [comap_apply, coordinate_apply, toFiniteHolomorphicMap]; rfl

theorem comap_aeval_coordinate (p : ℂ[X]) :
    comap (toFiniteHolomorphicMap g hg) (toFiniteHolomorphicMap g hg).holomorphic
      (toFiniteHolomorphicMap g hg).nonconstant (aeval coordinate p) = aeval g p := by
  rw [← comapₐ_apply, ← Polynomial.aeval_algHom_apply, comapₐ_apply, comap_coordinate]

variable (Q : Place ℂ (MeromorphicFunction X)) {c : ℂ}
  (hgQ : Q.valuation g ≤ 1) (hgc : Q.valuation (g - algebraMap ℂ _ c) < 1)
include hgQ hgc

/-- **A rational function of `g` finite at `c` is integral at `Q` and congruent to its value at `c`**, when `g ≡ c`
at `Q`: write it `num(g)/denom(g)` with `denom(c) ≠ 0`. -/
theorem valuation_comap_sub_lt_one (a : MeromorphicFunction (OnePoint ℂ)) (hac : a c ≠ OnePoint.infty) :
    Q.valuation (comap (toFiniteHolomorphicMap g hg) (toFiniteHolomorphicMap g hg).holomorphic
      (toFiniteHolomorphicMap g hg).nonconstant a - algebraMap ℂ _ (a.finitePart c)) < 1 := by
  set β := toFiniteHolomorphicMap g hg
  set r := ratFuncEquiv.symm a
  have har : a = ratFuncEquiv r := (ratFuncEquiv.apply_symm_apply a).symm
  have hsplit : r = algebraMap ℂ[X] (RatFunc ℂ) r.num / algebraMap ℂ[X] (RatFunc ℂ) r.denom :=
    (RatFunc.num_div_denom r).symm
  have hA : a = aeval coordinate r.num / aeval coordinate r.denom := by
    rw [har]
    nth_rewrite 1 [hsplit]
    rw [map_div₀, ratFuncEquiv_algebraMap, ratFuncEquiv_algebraMap]
  -- the denominator does not vanish at `c`
  have hden : r.denom.eval c ≠ 0 := by
    intro h0
    have hnum : r.num.eval c ≠ 0 := by
      intro h1
      obtain ⟨u, v, huv⟩ := RatFunc.isCoprime_num_denom r
      have := congrArg (eval c) huv
      simp [h0, h1] at this
    have hrel : a * aeval coordinate r.denom = aeval coordinate r.num := by
      have hd : aeval coordinate r.denom ≠ 0 := by
        intro hz
        have := congrArg (ratFuncEquiv.symm) hz
        rw [← ratFuncEquiv_algebraMap, AlgEquiv.symm_apply_apply, map_zero] at this
        exact r.denom_ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).1 this)
      rw [hA, div_mul_cancel₀ _ hd]
    have hv := congrArg (· (c : OnePoint ℂ)) hrel
    rw [mul_apply_of_eq_coe (coe_finitePart hac).symm (aeval_coordinate_apply_coe _ c), h0, mul_zero,
      aeval_coordinate_apply_coe] at hv
    exact hnum (OnePoint.coe_injective hv).symm
  -- the value at `c`
  have hval : a.finitePart c = r.num.eval c / r.denom.eval c := by
    refine finitePart_of_eq_coe ?_
    rw [har, ratFuncEquiv_apply_coe r hden]
    simp [RatFunc.eval, eval₂_id]
  have hcomap : comap β β.holomorphic β.nonconstant a = aeval g r.num / aeval g r.denom := by
    rw [hA, ← comapₐ_apply, map_div₀, comapₐ_apply, comapₐ_apply, comap_aeval_coordinate,
      comap_aeval_coordinate]
  have hd1 : Q.valuation (aeval g r.denom) = 1 :=
    valuation_eq_one_of_sub_lt_one Q hden (valuation_aeval_sub_lt_one Q hgQ hgc r.denom)
  have hd0 : aeval g r.denom ≠ 0 := fun h ↦ by simp [h] at hd1
  set a₀ := a.finitePart c
  have hp : (r.num - C a₀ * r.denom).eval c = 0 := by
    rw [eval_sub, eval_mul, eval_C, hval, div_mul_cancel₀ _ hden, sub_self]
  have h1 := valuation_aeval_sub_lt_one Q hgQ hgc (r.num - C a₀ * r.denom)
  rw [hp, map_zero, sub_zero, map_sub, map_mul, aeval_C] at h1
  rw [hcomap]
  have : aeval g r.num / aeval g r.denom - algebraMap ℂ _ a₀ =
      (aeval g r.num - algebraMap ℂ _ a₀ * aeval g r.denom) / aeval g r.denom := by
    field_simp
  rw [this, map_div₀, hd1, div_one]
  exact h1

theorem valuation_comap_le_one (a : MeromorphicFunction (OnePoint ℂ)) (hac : a c ≠ OnePoint.infty) :
    Q.valuation (comap (toFiniteHolomorphicMap g hg) (toFiniteHolomorphicMap g hg).holomorphic
      (toFiniteHolomorphicMap g hg).nonconstant a) ≤ 1 := by
  have h := valuation_comap_sub_lt_one hg Q hgQ hgc a hac
  set u := comap (toFiniteHolomorphicMap g hg) (toFiniteHolomorphicMap g hg).holomorphic
      (toFiniteHolomorphicMap g hg).nonconstant a
  have : u = (u - algebraMap ℂ _ (a.finitePart c)) + algebraMap ℂ _ (a.finitePart c) := by ring
  rw [this]
  refine (Q.valuation.map_add _ _).trans (max_le h.le ?_)
  rcases eq_or_ne (a.finitePart c) 0 with h0 | h0
  · simp [h0]
  · exact (Q.isTrivialOn.eq_one _ h0).le

end Comap

omit [CompactSpace X] [T2Space X] in
/-- A meromorphic function that is not nonconstant is a constant. -/
theorem eq_algebraMap_of_not_isNonconstant {g : MeromorphicFunction X} (h : ¬ IsNonconstant g) :
    ∃ c : ℂ, g = algebraMap ℂ _ c := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  simp only [IsNonconstant, not_exists, not_not] at h
  by_cases hv : g x₀ = OnePoint.infty
  · exact absurd (funext fun x ↦ (h x x₀).trans hv) g.coe_ne_infty
  obtain ⟨c, hc⟩ := OnePoint.ne_infty_iff_exists.1 hv
  exact ⟨c, MeromorphicFunction.ext fun x ↦ by rw [h x x₀, ← hc, coe_algebraMap]⟩

omit [CompactSpace X] [T2Space X] in
theorem not_isNonconstant_algebraMap (c : ℂ) : ¬ IsNonconstant (algebraMap ℂ (MeromorphicFunction X) c) := by
  rintro ⟨a, b, hab⟩
  exact hab (by simp [coe_algebraMap])

omit [CompactSpace X] [T2Space X] in
theorem isNonconstant_inv {g : MeromorphicFunction X} (hg : IsNonconstant g) : IsNonconstant g⁻¹ := by
  by_contra h
  obtain ⟨c, hc⟩ := eq_algebraMap_of_not_isNonconstant h
  have : g = algebraMap ℂ _ c⁻¹ := by rw [← inv_inv g, hc, map_inv₀]
  exact not_isNonconstant_algebraMap c⁻¹ (this ▸ hg)

variable (hF : IsFunctionField ℂ (MeromorphicFunction X)) {f₀ : MeromorphicFunction X} (hf₀ : IsNonconstant f₀)

/-- `0 < ord_{P_y}` exactly when `0 < ord_y`. -/
theorem ord_pointPlace_pos_iff (y : X) {G : MeromorphicFunction X} (hG : G ≠ 0) :
    0 < (pointPlace hF hf₀ y).ord G ↔ 0 < ordAt y G := by
  obtain ⟨e, he, hord⟩ := exists_order_eq_mul_ord hF hf₀ y
  rw [hord G hG]
  constructor
  · intro h; positivity
  · intro h
    by_contra h'
    push Not at h'
    nlinarith

theorem apply_eq_zero_of_ordAt_pos {y : X} {G : MeromorphicFunction X} (hG : G ≠ 0) (h : 0 < ordAt y G) :
    G y = ((0 : ℂ) : OnePoint ℂ) := by
  rw [← order_pos_iff, ← coe_ordAt hG]
  exact_mod_cast h

/-- **Surjectivity onto places (finite residue).** If `ord_Q(g) ≥ 0` for a nonconstant `g`, then `Q = P_y` for some
point `y` of the fibre of `g` over the residue of `g` at `Q`. -/
theorem exists_pointPlace_eq_of_valuation_le_one {g : MeromorphicFunction X} (hg : IsNonconstant g)
    (Q : Place ℂ (MeromorphicFunction X)) (hgQ : Q.valuation g ≤ 1) :
    ∃ y, pointPlace hF hf₀ y = Q := by
  classical
  obtain ⟨c, hgc⟩ := (Q.degree_eq_one_iff_forall_exists_valuation_sub_lt_one).1
    (Q.degree_eq_one_of_isAlgClosed_of_isFunctionField hF) g hgQ
  set β := toFiniteHolomorphicMap g hg
  set S := (β.finite_fiber (c : OnePoint ℂ)).toFinset
  by_contra hne
  push Not at hne
  -- approximation: `ord_Q(G) = 1`, `ord_{P_y}(G - 1) = 1` on the fibre
  set s : Finset (Place ℂ (MeromorphicFunction X)) := insert Q (S.image (pointPlace hF hf₀))
  obtain ⟨G, hG⟩ := Place.exists_forall_mem_ord_sub_eq s (fun P ↦ if P = Q then 0 else 1) (fun _ ↦ 1)
  have hGQ : Q.ord G = 1 := by simpa using hG Q (Finset.mem_insert_self _ _)
  have hG0 : G ≠ 0 := by rintro rfl; simp at hGQ
  have hGQv : Q.valuation G < 1 := (Q.valuation_lt_one_iff_ord_pos hG0).2 (by rw [hGQ]; exact one_pos)
  have hG1 : ∀ x ∈ β ⁻¹' {(c : OnePoint ℂ)}, G x = ((1 : ℂ) : OnePoint ℂ) := by
    intro x hx
    have hxS : x ∈ S := (β.finite_fiber _).mem_toFinset.2 hx
    have h := hG (pointPlace hF hf₀ x) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hxS))
    rw [if_neg (hne x)] at h
    have hsub0 : G - 1 ≠ 0 := by rintro h0; rw [h0, Place.ord_zero] at h; exact zero_ne_one h
    have hpos := (ord_pointPlace_pos_iff hF hf₀ x hsub0).1 (by rw [h]; exact one_pos)
    have h0 := apply_eq_zero_of_ordAt_pos hsub0 hpos
    have : G = (G - 1) + 1 := by ring
    rw [this, add_apply_of_eq_coe h0 (show (1 : MeromorphicFunction X) x = ((1 : ℂ) : OnePoint ℂ) by simp [MeromorphicFunction.coe_one]),
      zero_add]
  have hGfin : ∀ x ∈ β ⁻¹' {(c : OnePoint ℂ)}, G x ≠ OnePoint.infty := fun x hx ↦ by
    rw [hG1 x hx]; exact OnePoint.coe_ne_infty _
  obtain ⟨p, hpm, hpdeg, hpG, hpval⟩ := exists_fiberPoly β G
  have hval := hpval _ hGfin
  -- every coefficient is finite at `c`, the constant one with value `(-1)^n`
  have hcfin : ∀ i, p.coeff i (c : OnePoint ℂ) ≠ OnePoint.infty := by
    intro i
    by_cases hi : i ≤ degree β
    · rw [hval i hi]; exact OnePoint.coe_ne_infty _
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), MeromorphicFunction.coe_zero]; exact OnePoint.coe_ne_infty _
  have hc0 : (p.coeff 0).finitePart c = (-1) ^ degree β := by
    rw [finitePart_of_eq_coe (hval 0 (Nat.zero_le _)), fiberPoly_coeff_zero_of_eq_one β G hG1]
  set φ := (comapₐ β β.holomorphic β.nonconstant).toRingHom
  have hφ : ∀ a, φ a = comap β β.holomorphic β.nonconstant a := fun a ↦ rfl
  -- the terms of positive degree lie in the maximal ideal of `Q`
  have htail : Q.valuation (∑ i ∈ Finset.range p.natDegree, φ (p.coeff (i + 1)) * G ^ (i + 1)) < 1 := by
    refine (Valuation.map_sum_lt _ (by simp) fun i _ ↦ ?_)
    rw [map_mul, map_pow]
    calc Q.valuation (φ (p.coeff (i + 1))) * Q.valuation G ^ (i + 1)
        ≤ 1 * Q.valuation G ^ (i + 1) := by
          gcongr; rw [hφ]; exact valuation_comap_le_one hg Q hgQ hgc _ (hcfin _)
      _ < 1 := by rw [one_mul]; exact pow_lt_one₀ zero_le hGQv (Nat.succ_ne_zero i)
  have heq : φ (p.coeff 0) = -∑ i ∈ Finset.range p.natDegree, φ (p.coeff (i + 1)) * G ^ (i + 1) := by
    have h := hpG
    rw [eval₂_eq_sum_range, Finset.sum_range_succ'] at h
    simp only [pow_zero, mul_one] at h
    exact eq_neg_of_add_eq_zero_right h
  have hlt : Q.valuation (φ (p.coeff 0)) < 1 := by rw [heq, Valuation.map_neg]; exact htail
  have hone : Q.valuation (φ (p.coeff 0)) = 1 := by
    refine valuation_eq_one_of_sub_lt_one Q (a := (p.coeff 0).finitePart c) ?_ ?_
    · rw [hc0]; exact pow_ne_zero _ (by norm_num)
    · rw [hφ]; exact valuation_comap_sub_lt_one hg Q hgQ hgc _ (hcfin 0)
  rw [hone] at hlt
  exact lt_irrefl _ hlt

/-- **Every place of `M(X)/ℂ` is the place of a point.** -/
theorem exists_pointPlace_eq (Q : Place ℂ (MeromorphicFunction X)) : ∃ y, pointPlace hF hf₀ y = Q := by
  by_cases h : Q.valuation f₀ ≤ 1
  · exact exists_pointPlace_eq_of_valuation_le_one hF hf₀ hf₀ Q h
  · have hinv : IsNonconstant f₀⁻¹ := isNonconstant_inv hf₀
    refine exists_pointPlace_eq_of_valuation_le_one hF hf₀ hinv Q ?_
    rw [map_inv₀]
    push Not at h
    exact inv_le_one_of_one_le₀ h.le

end ModularFormsKB.Milne.Wave11
