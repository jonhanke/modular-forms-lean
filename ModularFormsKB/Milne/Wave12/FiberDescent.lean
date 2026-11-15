import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Degree
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Separation

/-!
# Separation of points descends along finite holomorphic maps

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Theorems 1.17 and 1.20 (pdf pp. 20–21), used for
the modular curves in `ModularFormsKB.Milne.Wave12.ScalarRiemannRoch`.

Let `π : X → Y` be a finite holomorphic map of compact connected Riemann surfaces and `h` a meromorphic function on
`X`. The elementary symmetric functions of the values of `h` along the fibres of `π`, counted with multiplicity,

  `c_k(y) = e_k (h(x) : x ∈ π⁻¹(y))`,

are meromorphic on `Y` (`meromorphicAt_fiberEsymm`; the norm and trace of `h` are among them). Tau Ceti proves this
for maps to the sphere (`TauCeti.RiemannSurface.MeromorphicFunction.meromorphicAt_esymm_map_finitePart_fiberMultiset`);
the proof there needs only a function on the target vanishing at a given point, which every compact surface carrying a
nonconstant meromorphic function has (`exists_ne_zero_apply_eq_zero_of_isNonconstant`). The holomorphy of the
symmetric functions away from the poles is Tau Ceti's general `TauCeti.RiemannSurface.analyticAt_esymm_map_fiberMultiset`.

Consequence (**`exists_ne_of_pairwise_separated`**): if the points of `π⁻¹(y) ∪ π⁻¹(y')` are pairwise separated by
meromorphic functions on `X`, then `y ≠ y'` are separated by a meromorphic function on `Y`. Choose `h` finite and
injective on the two fibres (Tau Ceti `exists_forall_ne_infty_and_injOn`); the polynomials `∏ (T - h(x))` over the two
fibres have disjoint root sets, so some coefficient `c_k` differs.
-/

open Filter Function OnePoint Polynomial Set Topology TauCeti.RiemannSurface MeromorphicFunction
open scoped Manifold

noncomputable section

namespace ModularFormsKB.Milne.Wave12

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [ConnectedSpace X] [T2Space X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
  [CompactSpace Y] [ConnectedSpace Y] [T2Space Y]

omit [CompactSpace Y] [T2Space Y] in
/-- Every point of a compact connected Riemann surface with a nonconstant meromorphic function `g` is a zero of a
nonzero meromorphic function (`g - g(y₀)`, or `1/g` at a pole). -/
theorem exists_ne_zero_apply_eq_zero_of_nonconstant {g : MeromorphicFunction Y} (hg : ∃ a b, g a ≠ g b)
    (y₀ : Y) : ∃ u : MeromorphicFunction Y, u ≠ 0 ∧ u y₀ = ((0 : ℂ) : OnePoint ℂ) := by
  by_cases h : g y₀ = ∞
  · refine ⟨g⁻¹, fun h0 ↦ ?_, inv_apply_of_eq_infty h⟩
    have : g = 0 := inv_eq_zero.1 h0
    obtain ⟨a, b, hab⟩ := hg
    exact hab (by rw [this, MeromorphicFunction.coe_zero])
  · refine ⟨g - algebraMap ℂ _ (g.finitePart y₀), fun h0 ↦ ?_, ?_⟩
    · have hc : g = algebraMap ℂ _ (g.finitePart y₀) := sub_eq_zero.1 h0
      obtain ⟨a, b, hab⟩ := hg
      exact hab (by rw [hc, coe_algebraMap])
    · rw [sub_apply h (by simp)]
      simp

variable (π : FiniteHolomorphicMap X Y) (f : MeromorphicFunction X)

/-- The `k`-th elementary symmetric function of the values of `f` along the fibre of `π` over `y`, counted with
multiplicity. -/
def fiberEsymm (k : ℕ) (y : Y) : ℂ := ((fiberMultiset π y).map f.finitePart).esymm k

omit [ConnectedSpace X] [ConnectedSpace Y] [CompactSpace Y] in
theorem analyticAt_fiberEsymm {y₀ : Y} (hy₀ : ∀ x ∈ π ⁻¹' {y₀}, f x ≠ ∞) (k : ℕ) :
    AnalyticAt ℂ (fiberEsymm π f k ∘ (chartAt ℂ y₀).symm) (chartAt ℂ y₀ y₀) :=
  analyticAt_esymm_map_fiberMultiset π.holomorphic π.not_eventuallyConst
    (IsManifold.chart_mem_maximalAtlas y₀) (mem_chart_source ℂ y₀) (fun x hx ↦ by
      filter_upwards [f.continuous.continuousAt.eventually (isOpen_ne.mem_nhds (hy₀ x hx))]
        with x' hx'
      exact mdifferentiableAt_finitePart hx') k

omit [ConnectedSpace X] [ConnectedSpace Y] [CompactSpace Y] in
theorem continuousAt_fiberEsymm {y₀ : Y} (hy₀ : ∀ x ∈ π ⁻¹' {y₀}, f x ≠ ∞) (k : ℕ) :
    ContinuousAt (fiberEsymm π f k) y₀ := by
  refine ((analyticAt_fiberEsymm π f hy₀ k).continuousAt.comp
    ((chartAt ℂ y₀).continuousAt (mem_chart_source ℂ y₀))).congr ?_
  filter_upwards [(chartAt ℂ y₀).open_source.mem_nhds (mem_chart_source ℂ y₀)] with y hy
  simp only [Function.comp_apply, (chartAt ℂ y₀).left_inv hy]

omit [CompactSpace Y] [CompactSpace X] [T2Space X] [T2Space Y] in
/-- Multiplying `f` by a high power of the pullback of a function vanishing at `y₀` removes the poles of `f` over
`y₀`. -/
theorem exists_mul_comap_pow_ne_infty' {u : MeromorphicFunction Y} {y₀ : Y}
    (hu₀ : u y₀ = ((0 : ℂ) : OnePoint ℂ)) :
    ∃ N : ℕ, ∀ x ∈ π ⁻¹' {y₀}, (f * comap π π.holomorphic π.nonconstant (u ^ N)) x ≠ ∞ := by
  have hev (x : X) (hx : x ∈ π ⁻¹' {y₀}) : ∀ᶠ N in atTop,
      (f * comap π π.holomorphic π.nonconstant (u ^ N)) x ≠ ∞ := by
    have hπx : π x = y₀ := hx
    have hpos : 0 < order x (comap π π.holomorphic π.nonconstant u) := by
      rw [order_pos_iff, comap_apply, hπx, hu₀]
    refine Eventually.mono ?_ fun N (hN : 0 ≤ order x f +
        N • order x (comap π π.holomorphic π.nonconstant u)) ↦ by
      rwa [← order_nonneg_iff, (order x).map_mul, comap_pow, (order x).map_pow]
    revert hpos
    induction order x f using WithTop.recTopCoe with
    | top => exact fun _ ↦ .of_forall fun N ↦ by simp
    | coe a =>
      induction order x (comap π π.holomorphic π.nonconstant u) using WithTop.recTopCoe with
      | top =>
        refine fun _ ↦ (eventually_ge_atTop 1).mono fun N hN ↦ ?_
        obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
        rw [succ_nsmul, WithTop.add_top, WithTop.add_top]
        exact le_top
      | coe b =>
        refine fun hpos ↦ (eventually_ge_atTop a.natAbs).mono fun N hN ↦ ?_
        have hb : (1 : ℤ) ≤ b := by
          have := WithTop.coe_pos.1 hpos
          omega
        rw [← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_nonneg, nsmul_eq_mul]
        have ha : -(a.natAbs : ℤ) ≤ a := by omega
        have hN' : (a.natAbs : ℤ) ≤ N := by exact_mod_cast hN
        have hN₀ : (0 : ℤ) ≤ N := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hb hN₀]
  obtain ⟨N, hN⟩ := ((π.finite_fiber y₀).eventually_all.2 hev).exists
  exact ⟨N, hN⟩

omit [CompactSpace Y] in
/-- **The elementary symmetric functions of the values along the fibres of `π` are meromorphic on `Y`**, given a
nonzero function on `Y` vanishing at each point. -/
theorem meromorphicAt_fiberEsymm
    (hu : ∀ y₀ : Y, ∃ u : MeromorphicFunction Y, u ≠ 0 ∧ u y₀ = ((0 : ℂ) : OnePoint ℂ)) (k : ℕ) (y₀ : Y) :
    TauCeti.RiemannSurface.MeromorphicAt (fiberEsymm π f k) y₀ := by
  obtain ⟨u, hu, hu₀⟩ := hu y₀
  obtain ⟨N, hN⟩ := exists_mul_comap_pow_ne_infty' π f hu₀
  set g := f * comap π π.holomorphic π.nonconstant (u ^ N)
  have hg : TauCeti.RiemannSurface.MeromorphicAt (fiberEsymm π g k) y₀ := by
    rw [meromorphicAt_def]
    exact (analyticAt_fiberEsymm π g hN k).meromorphicAt
  have hpoles : (π '' {x | f x = ∞}).Finite := f.finite_setOf_eq_infty.image π
  refine (hg.mul ((u.meromorphicAt_finitePart y₀).pow (N * k)).inv).congr ?_
  filter_upwards [u.eventually_ne_infty y₀, eventually_finitePart_ne_zero hu y₀,
    mem_codiscrete_iff_forall_mem_nhdsNE.1 hpoles.compl_mem_codiscrete y₀] with y hyu hyu₀ hyf
  have hfib : (fiberMultiset π y).map g.finitePart =
      ((fiberMultiset π y).map f.finitePart).map (u.finitePart y ^ N • ·) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun x hx ↦ ?_
    have hπx : π x = y := ((mem_fiberMultiset (π.finite_fiber y)).1 hx).1
    have hfx : f x ≠ ∞ := fun h ↦ hyf ⟨x, h, hπx⟩
    refine finitePart_of_eq_coe ?_
    rw [mul_apply_of_eq_coe (coe_finitePart hfx).symm
      (by rw [comap_apply, hπx, pow_apply hyu]), Function.comp_apply, smul_eq_mul, mul_comm]
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, fiberEsymm]
  rw [hfib, ← Multiset.pow_smul_esymm, smul_eq_mul, ← pow_mul, mul_right_comm,
    mul_inv_cancel₀ (pow_ne_zero _ hyu₀), one_mul]

/-- Multisets of the same cardinality with the same elementary symmetric functions are equal. -/
theorem multiset_eq_of_esymm_eq {A B : Multiset ℂ} (hc : Multiset.card A = Multiset.card B)
    (he : ∀ k, A.esymm k = B.esymm k) : A = B := by
  have hA := Multiset.prod_X_sub_X_eq_sum_esymm A
  have hB := Multiset.prod_X_sub_X_eq_sum_esymm B
  have hp : (A.map fun t ↦ X - C t).prod = (B.map fun t ↦ X - C t).prod := by
    rw [hA, hB, hc]
    simp only [he]
  rw [← Polynomial.roots_multiset_prod_X_sub_C A, ← Polynomial.roots_multiset_prod_X_sub_C B, hp]

omit [CompactSpace Y] in
/-- **Separation descends along `π`**: if the points of the two fibres of `π` over `y ≠ y'` are pairwise separated
by meromorphic functions on `X`, some meromorphic function on `Y` separates `y` and `y'`. -/
theorem exists_ne_of_pairwise_separated
    (hu : ∀ y₀ : Y, ∃ u : MeromorphicFunction Y, u ≠ 0 ∧ u y₀ = ((0 : ℂ) : OnePoint ℂ)) {y y' : Y} (hyy : y ≠ y')
    (hsep : (π ⁻¹' {y} ∪ π ⁻¹' {y'}).Pairwise fun x x' ↦ ∃ g : MeromorphicFunction X, g x ≠ g x') :
    ∃ g : MeromorphicFunction Y, g y ≠ g y' := by
  obtain ⟨h, hfin, hinj⟩ :=
    exists_forall_ne_infty_and_injOn ((π.finite_fiber y).union (π.finite_fiber y')) hsep
  by_contra hall
  push Not at hall
  have hval : ∀ k, fiberEsymm π h k y = fiberEsymm π h k y' := by
    intro k
    set c := ofMeromorphic (meromorphicAt_fiberEsymm π h hu k)
    have h1 : c y = (fiberEsymm π h k y : OnePoint ℂ) :=
      ofMeromorphic_apply_of_continuousAt _ (continuousAt_fiberEsymm π h (fun x hx ↦ hfin x (Or.inl hx)) k)
    have h2 : c y' = (fiberEsymm π h k y' : OnePoint ℂ) :=
      ofMeromorphic_apply_of_continuousAt _ (continuousAt_fiberEsymm π h (fun x hx ↦ hfin x (Or.inr hx)) k)
    have := hall c
    rw [h1, h2] at this
    exact OnePoint.coe_injective this
  have hAB : (fiberMultiset π y).map h.finitePart = (fiberMultiset π y').map h.finitePart :=
    multiset_eq_of_esymm_eq (by simp) hval
  have hpos : 0 < Multiset.card (fiberMultiset π y) := by
    rw [FiniteHolomorphicMap.card_fiberMultiset]; exact degree_pos π
  obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.1 hpos
  have hxA : h.finitePart x ∈ (fiberMultiset π y').map h.finitePart := by
    rw [← hAB]; exact Multiset.mem_map_of_mem _ hx
  obtain ⟨x', hx', hxx'⟩ := Multiset.mem_map.1 hxA
  have hπx : π x = y := ((mem_fiberMultiset (π.finite_fiber y)).1 hx).1
  have hπx' : π x' = y' := ((mem_fiberMultiset (π.finite_fiber y')).1 hx').1
  have hmx : x ∈ π ⁻¹' {y} ∪ π ⁻¹' {y'} := Or.inl hπx
  have hmx' : x' ∈ π ⁻¹' {y} ∪ π ⁻¹' {y'} := Or.inr hπx'
  have heq : h x' = h x := by
    rw [← coe_finitePart (hfin x' hmx'), ← coe_finitePart (hfin x hmx), hxx']
  exact hyy (by rw [← hπx, ← hπx', hinj hmx' hmx heq])

end ModularFormsKB.Milne.Wave12
