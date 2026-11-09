import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import ModularFormsKB.Milne.RiemannSurface.Results

/-!
# Milne, Theorem 1.17: the named statement is false without compactness and the Hausdorff axiom

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Theorem 1.17, pdf p. 20.

The named statement `ModularFormsKB.Milne.RiemannSurface.ExistsNonconstantStatement X` is stated for a connected
charted space `X` with an `IsManifold 𝓘(ℂ) 1` structure, but without `[CompactSpace X]` and `[T2Space X]`, which are
part of Milne's hypotheses (compact Riemann surfaces are Hausdorff). It is therefore false for the following
non-Hausdorff (and noncompact) connected complex manifold `PeriodGluedPlane`: the plane `ℂ` with the upper half-plane
identified along translations by `ℤ` and the lower half-plane identified along translations by `ℤ √2`.

* Every holomorphic map `f : PeriodGluedPlane → OnePoint ℂ` pulls back to a holomorphic map `g` on `ℂ` which is
  `1`-periodic and `√2`-periodic on the real line (by continuity from above and below respectively). The group
  `ℤ + ℤ √2` is dense in `ℝ`, so `g` is constant on `ℝ`, hence constant near `0` by the identity theorem, hence
  constant by the identity theorem for Riemann surfaces.
* `PeriodGluedPlane` is not Hausdorff (`PeriodGluedPlane.not_t2Space`), so the hypothesis of the book is violated.
-/

open Set Topology Filter
open scoped Manifold

namespace ModularFormsKB.Milne.RS

/-- The identification relation on `ℂ`: equal points, or points of the upper half-plane differing by an integer, or
points of the lower half-plane differing by an integer multiple of `√2`. -/
def periodRel (z w : ℂ) : Prop :=
  z = w ∨ (0 < z.im ∧ 0 < w.im ∧ ∃ n : ℤ, w = z + n) ∨
    (z.im < 0 ∧ w.im < 0 ∧ ∃ m : ℤ, w = z + m * (Real.sqrt 2 : ℂ))

/-- `periodRel` is an equivalence relation. -/
def periodSetoid : Setoid ℂ where
  r := periodRel
  iseqv := by
    refine ⟨fun z ↦ Or.inl rfl, ?_, ?_⟩
    · rintro z w (rfl | ⟨hz, hw, n, rfl⟩ | ⟨hz, hw, m, rfl⟩)
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨hw, hz, -n, ?_⟩)
        push_cast; ring
      · refine Or.inr (Or.inr ⟨hw, hz, -m, ?_⟩)
        push_cast; ring
    · rintro z w u (rfl | ⟨hz, hw, n, rfl⟩ | ⟨hz, hw, m, rfl⟩) h2
      · exact h2
      · rcases h2 with rfl | ⟨-, hu, n', rfl⟩ | ⟨hw', -, -⟩
        · exact Or.inr (Or.inl ⟨hz, hw, n, rfl⟩)
        · exact Or.inr (Or.inl ⟨hz, hu, n + n', by push_cast; ring⟩)
        · exact absurd hw' (not_lt.2 hw.le)
      · rcases h2 with rfl | ⟨hw', -, -⟩ | ⟨-, hu, m', rfl⟩
        · exact Or.inr (Or.inr ⟨hz, hw, m, rfl⟩)
        · exact absurd hw' (not_lt.2 hw.le)
        · exact Or.inr (Or.inr ⟨hz, hu, m + m', by push_cast; ring⟩)

/-- **The period-glued plane**: `ℂ` modulo `periodRel`, with the quotient topology. The upper half-plane is wrapped
around a cylinder of circumference `1`, the lower half-plane around one of circumference `√2`, and the real axis is
left alone. -/
def PeriodGluedPlane : Type := Quotient periodSetoid

namespace PeriodGluedPlane

instance : TopologicalSpace PeriodGluedPlane := inferInstanceAs (TopologicalSpace (Quotient periodSetoid))

/-- The quotient map `ℂ → PeriodGluedPlane`. -/
def q : ℂ → PeriodGluedPlane := Quotient.mk periodSetoid

theorem q_eq {z w : ℂ} : q z = q w ↔ periodRel z w := Quotient.eq (r := periodSetoid)

theorem q_surjective : Function.Surjective q := Quotient.mk_surjective

theorem continuous_q : Continuous q := continuous_quot_mk

theorem periodRel_dist {z w : ℂ} (h : periodRel z w) : z = w ∨ 1 ≤ dist z w := by
  rcases h with h | ⟨-, -, n, hn⟩ | ⟨-, -, m, hm⟩
  · exact Or.inl h
  · by_cases hn0 : n = 0
    · left; rw [hn, hn0]; simp
    · right
      rw [dist_eq_norm, hn, show z - (z + n) = -(n : ℂ) by ring, norm_neg, Complex.norm_intCast]
      exact_mod_cast Int.one_le_abs hn0
  · by_cases hm0 : m = 0
    · left; rw [hm, hm0]; simp
    · right
      have hs : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by norm_num)
      rw [dist_eq_norm, hm, show z - (z + m * (Real.sqrt 2 : ℂ)) = -((m : ℂ) * (Real.sqrt 2 : ℂ)) by ring,
        norm_neg, norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg 2)]
      have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
      nlinarith

/-- The open ball of radius `1/2` about `p`; `q` is injective on it. -/
noncomputable def ball (p : ℂ) : Set ℂ := Metric.ball p (1 / 2)

theorem isOpen_ball (p : ℂ) : IsOpen (ball p) := Metric.isOpen_ball

theorem mem_ball_self (p : ℂ) : p ∈ ball p := Metric.mem_ball_self (by norm_num)

theorem injOn_ball (p : ℂ) : InjOn q (ball p) := by
  intro z hz w hw h
  rcases periodRel_dist (q_eq.1 h) with h | h
  · exact h
  · have h1 : dist z w ≤ dist z p + dist p w := dist_triangle _ _ _
    have h2 : dist z p < 1 / 2 := hz
    have h3 : dist p w < 1 / 2 := by rw [dist_comm]; exact hw
    linarith

theorem isOpenMap_q : IsOpenMap q := by
  intro U hU
  refine (isQuotientMap_quotient_mk' (s := periodSetoid)).isOpen_preimage.mp ?_
  change IsOpen (q ⁻¹' (q '' U))
  rw [isOpen_iff_forall_mem_open]
  rintro w ⟨z, hz, hzw⟩
  rcases q_eq.1 hzw with rfl | ⟨hz0, hw0, n, rfl⟩ | ⟨hz0, hw0, m, rfl⟩
  · exact ⟨U, fun u hu ↦ ⟨u, hu, rfl⟩, hU, hz⟩
  · refine ⟨(fun v ↦ v - n) ⁻¹' U ∩ {v | 0 < v.im}, ?_, ?_, ⟨by simpa using hz, hw0⟩⟩
    · rintro v ⟨hv, hv0⟩
      exact ⟨v - n, hv, q_eq.2 (Or.inr (Or.inl ⟨by simpa using hv0, hv0, n, by ring⟩))⟩
    · exact (hU.preimage (by fun_prop)).inter (isOpen_lt continuous_const Complex.continuous_im)
  · refine ⟨(fun v ↦ v - m * (Real.sqrt 2 : ℂ)) ⁻¹' U ∩ {v | v.im < 0}, ?_, ?_,
      ⟨by simpa using hz, hw0⟩⟩
    · rintro v ⟨hv, hv0⟩
      exact ⟨v - m * (Real.sqrt 2 : ℂ), hv,
        q_eq.2 (Or.inr (Or.inr ⟨by simpa using hv0, hv0, m, by ring⟩))⟩
    · exact (hU.preimage (by fun_prop)).inter (isOpen_lt Complex.continuous_im continuous_const)

/-- The partial equivalence `ball p → q '' ball p` given by `q`. -/
noncomputable def ballEquiv (p : ℂ) : PartialEquiv ℂ PeriodGluedPlane where
  toFun := q
  invFun := Function.invFunOn q (ball p)
  source := ball p
  target := q '' ball p
  map_source' := fun _ h ↦ mem_image_of_mem q h
  map_target' := fun _ h ↦ Function.invFunOn_mem h
  left_inv' := fun _ h ↦ (injOn_ball p).leftInvOn_invFunOn h
  right_inv' := fun _ h ↦ Function.invFunOn_eq h

/-- The chart at `p`: inverse of `q` restricted to the ball of radius `1/2` about `p`. -/
noncomputable def chartP (p : ℂ) : OpenPartialHomeomorph PeriodGluedPlane ℂ :=
  (OpenPartialHomeomorph.ofContinuousOpenRestrict (ballEquiv p) continuous_q.continuousOn
    (isOpenMap_q.domRestrict (isOpen_ball p)) (isOpen_ball p)).symm

theorem chartP_symm_apply (p w : ℂ) : (chartP p).symm w = q w := rfl

theorem chartP_source (p : ℂ) : (chartP p).source = q '' ball p := rfl

theorem chartP_target (p : ℂ) : (chartP p).target = ball p := rfl

theorem chartP_q {p w : ℂ} (h : w ∈ ball p) : chartP p (q w) = w :=
  (injOn_ball p).leftInvOn_invFunOn h

theorem eventually_periodRel {w w' : ℂ} (h : periodRel w w') :
    ∀ᶠ v in 𝓝 w, periodRel v (v + (w' - w)) := by
  rcases h with rfl | ⟨hw, hw', n, hn⟩ | ⟨hw, hw', m, hm⟩
  · exact Eventually.of_forall fun v ↦ Or.inl (by simp)
  · have hc : w' - w = n := by rw [hn]; ring
    have hO : IsOpen {v : ℂ | 0 < v.im} := isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hO.mem_nhds hw] with v hv
    rw [hc]
    exact Or.inr (Or.inl ⟨hv, by simpa using hv, n, rfl⟩)
  · have hc : w' - w = m * (Real.sqrt 2 : ℂ) := by rw [hm]; ring
    filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hw] with v hv
    rw [hc]
    exact Or.inr (Or.inr ⟨hv, by simpa using (show v.im < 0 from hv), m, rfl⟩)

/-- Local translation: near `w`, the chart at `p` (with `q w' = q w`, `w' ∈ ball p`) is the translation by `w' - w`. -/
theorem chartP_eventually {p w w' : ℂ} (hw' : w' ∈ ball p) (h : q w' = q w) :
    ∀ᶠ v in 𝓝 w, chartP p (q v) = v + (w' - w) := by
  have hrel := eventually_periodRel (q_eq.1 h.symm)
  have hc : ContinuousAt (fun v : ℂ ↦ v + (w' - w)) w := by fun_prop
  have hmem : ∀ᶠ v in 𝓝 w, v + (w' - w) ∈ ball p :=
    hc.eventually_mem (by simpa using (isOpen_ball p).mem_nhds hw')
  filter_upwards [hrel, hmem] with v hv hv'
  rw [q_eq.2 hv]
  exact chartP_q hv'

/-- A chosen representative of a point of `PeriodGluedPlane`. -/
noncomputable def rep (x : PeriodGluedPlane) : ℂ := Classical.choose (q_surjective x)

theorem q_rep (x : PeriodGluedPlane) : q (rep x) = x := Classical.choose_spec (q_surjective x)

noncomputable instance : ChartedSpace ℂ PeriodGluedPlane where
  atlas := range chartP
  chartAt x := chartP (rep x)
  mem_chart_source x := ⟨rep x, mem_ball_self _, q_rep x⟩
  chart_mem_atlas _ := mem_range_self _

instance : IsManifold 𝓘(ℂ) 1 PeriodGluedPlane := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨p, rfl⟩ ⟨p', rfl⟩
  intro w hw
  have hw1 : w ∈ ((chartP p).symm ≫ₕ chartP p').source := hw.1
  obtain ⟨w', hw'p', hq⟩ := hw1.2
  have hq' : q w' = q w := hq
  have hev := chartP_eventually hw'p' hq'
  have hd : ContDiffAt ℂ 1 (fun v : ℂ ↦ v + (w' - w)) w := contDiffAt_id.add contDiffAt_const
  refine ContDiffAt.contDiffWithinAt (hd.congr_of_eventuallyEq ?_)
  filter_upwards [hev] with v hv
  exact hv

theorem mdifferentiable_q : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) q := by
  intro w
  refine (mdifferentiableAt_iff_of_mem_source (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (mem_chart_source ℂ w)
    (mem_chart_source ℂ (q w))).2 ⟨continuous_q.continuousAt, ?_⟩
  have hev : ∀ᶠ v in 𝓝 w, chartAt ℂ (q w) (q v) = v + (rep (q w) - w) :=
    chartP_eventually (p := rep (q w)) (mem_ball_self _) (q_rep _)
  have hd : DifferentiableAt ℂ (fun v : ℂ ↦ v + (rep (q w) - w)) w :=
    differentiableAt_id.add_const _
  have : DifferentiableAt ℂ ((chartAt ℂ (q w)) ∘ q) w := hd.congr_of_eventuallyEq hev
  simpa [extChartAt, chartAt_self_eq] using this.differentiableWithinAt

instance : ConnectedSpace PeriodGluedPlane := q_surjective.connectedSpace continuous_q

theorem q_zero_ne_q_one : q 0 ≠ q 1 := by
  intro h
  rcases q_eq.1 h with h | ⟨h, -⟩ | ⟨h, -⟩ <;> simp at h

/-- `PeriodGluedPlane` is not Hausdorff: `q 0` and `q 1` cannot be separated. -/
theorem not_t2Space : ¬ T2Space PeriodGluedPlane := by
  intro hT
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation q_zero_ne_q_one
  have h1 : ∀ᶠ ε : ℝ in 𝓝 0, q ((0 : ℂ) + ε * Complex.I) ∈ U :=
    (continuous_q.comp (by fun_prop : Continuous fun ε : ℝ ↦ (0 : ℂ) + ε * Complex.I)).continuousAt.preimage_mem_nhds
      (by simpa using hU.mem_nhds hxU)
  have h2 : ∀ᶠ ε : ℝ in 𝓝 0, q ((1 : ℂ) + ε * Complex.I) ∈ V :=
    (continuous_q.comp (by fun_prop : Continuous fun ε : ℝ ↦ (1 : ℂ) + ε * Complex.I)).continuousAt.preimage_mem_nhds
      (by simpa using hV.mem_nhds hyV)
  have h3 : ∀ᶠ ε : ℝ in 𝓝[>] 0, (q ((0 : ℂ) + ε * Complex.I) ∈ U ∧ q ((1 : ℂ) + ε * Complex.I) ∈ V) ∧
      ε ∈ Ioi 0 :=
    ((h1.and h2).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨ε, ⟨hεU, hεV⟩, hε⟩ := h3.exists
  have heq : q ((0 : ℂ) + ε * Complex.I) = q ((1 : ℂ) + ε * Complex.I) :=
    q_eq.2 (Or.inr (Or.inl ⟨by simpa using hε, by simpa using hε, 1, by push_cast; ring⟩))
  exact hUV.ne_of_mem hεU (heq ▸ hεV) rfl

end PeriodGluedPlane

open PeriodGluedPlane TauCeti TauCeti.RiemannSurface

/-- A continuous function on `ℝ` with periods `1` and `√2` is constant (the group `ℤ + ℤ √2` is dense). -/
theorem real_const_of_periods {Y : Type*} [TopologicalSpace Y] [T2Space Y] (G : ℝ → Y) (hG : Continuous G)
    (h1 : ∀ c, G (c + 1) = G c) (h2 : ∀ c, G (c + Real.sqrt 2) = G c) : ∀ c, G c = G 0 := by
  have hper : ∀ s ∈ AddSubgroup.closure ({Real.sqrt 2, 1} : Set ℝ), ∀ c, G (c + s) = G c := by
    intro s hs
    refine AddSubgroup.closure_induction (p := fun s _ ↦ ∀ c, G (c + s) = G c) ?_ ?_ ?_ ?_ hs
    · intro x hx
      rcases hx with rfl | hx
      · exact h2
      · rw [mem_singleton_iff.1 hx]; exact h1
    · intro c; simp
    · intro x y _ _ hx hy c
      rw [← add_assoc, hy, hx]
    · intro x _ hx c
      simpa using (hx (c + -x)).symm
  have hd : Dense (AddSubgroup.closure ({Real.sqrt 2, 1} : Set ℝ) : Set ℝ) := by
    rw [dense_addSubgroupClosure_pair_iff]
    simpa using irrational_sqrt_two
  intro c
  have hcl : IsClosed {s : ℝ | G (0 + s) = G 0} :=
    isClosed_eq (hG.comp (by fun_prop)) continuous_const
  have hsub := hcl.closure_subset_iff.2 (fun s hs ↦ by simpa using hper s hs 0)
  have hc : c ∈ closure (AddSubgroup.closure ({Real.sqrt 2, 1} : Set ℝ) : Set ℝ) := by
    rw [hd.closure_eq]; exact mem_univ c
  simpa using hsub hc

theorem eq_of_eventually_im {Y : Type*} [TopologicalSpace Y] [T2Space Y] (g : ℂ → Y) (hg : Continuous g)
    (l : Filter ℝ) [l.NeBot] (hl : l ≤ 𝓝 0) (d c : ℂ)
    (h : ∀ᶠ ε : ℝ in l, g (d + (ε : ℂ) * Complex.I) = g (c + (ε : ℂ) * Complex.I)) : g d = g c := by
  have key : ∀ e : ℂ, Tendsto (fun ε : ℝ ↦ g (e + (ε : ℂ) * Complex.I)) l (𝓝 (g e)) := by
    intro e
    have hc : Continuous (fun ε : ℝ ↦ g (e + (ε : ℂ) * Complex.I)) := by fun_prop
    simpa using hc.continuousAt.tendsto.mono_left hl
  exact tendsto_nhds_unique_of_eventuallyEq (key d) (key c) h

theorem real_periodic {Y : Type*} [TopologicalSpace Y] [T2Space Y] (g : ℂ → Y) (hg : Continuous g)
    (hq : ∀ z w, periodRel z w → g z = g w) :
    (∀ c : ℝ, g ((c + 1 : ℝ) : ℂ) = g c) ∧ (∀ c : ℝ, g ((c + Real.sqrt 2 : ℝ) : ℂ) = g c) := by
  constructor
  · intro c
    refine eq_of_eventually_im g hg (𝓝[>] 0) nhdsWithin_le_nhds _ _ ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    refine (hq _ _ (Or.inr (Or.inl ⟨by simpa using hε, by simpa using hε, 1, ?_⟩))).symm
    push_cast; ring
  · intro c
    refine eq_of_eventually_im g hg (𝓝[<] 0) nhdsWithin_le_nhds _ _ ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    refine (hq _ _ (Or.inr (Or.inr ⟨by simpa using hε, by simpa using hε, 1, ?_⟩))).symm
    push_cast; ring

/-- Every holomorphic map from `PeriodGluedPlane` to the Riemann sphere is constant. -/
theorem meromorphic_const (f : MeromorphicFunction PeriodGluedPlane) (x x' : PeriodGluedPlane) :
    f x = f x' := by
  set g : ℂ → OnePoint ℂ := fun z ↦ f (q z) with hgdef
  have hgc : Continuous g := f.mdifferentiable'.continuous.comp continuous_q
  have hgm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := f.mdifferentiable'.comp mdifferentiable_q
  have hq : ∀ z w, periodRel z w → g z = g w := fun z w h ↦ by
    simp only [hgdef]; rw [q_eq.2 h]
  obtain ⟨hp1, hp2⟩ := real_periodic g hgc hq
  have hreal : ∀ c : ℝ, g c = g 0 := by
    have := real_const_of_periods (fun c : ℝ ↦ g c) (hgc.comp Complex.continuous_ofReal) hp1 hp2
    simpa using this
  have hana := analyticAt_chartAt_comp_comp_chartAt_symm (f := g) (x := (0 : ℂ))
    (.of_forall fun y ↦ hgm y)
  set F : ℂ → ℂ := fun z ↦ chartAt ℂ (g 0) (g z) with hFdef
  have hF : AnalyticAt ℂ F 0 := by simpa [hFdef, chartAt_self_eq] using hana
  have hFreal : ∀ x : ℝ, F x = F 0 := by
    intro x
    simp only [hFdef]
    rw [hreal x]
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), F z = F 0 := by
    have hne : Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using hx
    exact hne.frequently (Eventually.frequently (Eventually.of_forall hFreal))
  have hFev : ∀ᶠ z in 𝓝 (0 : ℂ), F z = F 0 :=
    (hF.frequently_eq_iff_eventually_eq analyticAt_const).1 hfreq
  have hgev : ∀ᶠ z in 𝓝 (0 : ℂ), g z = g 0 := by
    filter_upwards [hFev, hgc.continuousAt.eventually_mem
      ((chartAt ℂ (g 0)).open_source.mem_nhds (mem_chart_source ℂ (g 0)))] with z hz hzs
    have h1 := (chartAt ℂ (g 0)).left_inv hzs
    have h0 := (chartAt ℂ (g 0)).left_inv (mem_chart_source ℂ (g 0))
    calc g z = (chartAt ℂ (g 0)).symm (F z) := h1.symm
      _ = (chartAt ℂ (g 0)).symm (F 0) := by rw [hz]
      _ = g 0 := h0
  have hconst : EventuallyConst g (𝓝 (0 : ℂ)) := eventuallyConst_iff_exists_eventuallyEq.2 ⟨g 0, hgev⟩
  have hall := apply_eq_of_eventuallyConst hgm hconst
  obtain ⟨z, rfl⟩ := q_surjective x
  obtain ⟨z', rfl⟩ := q_surjective x'
  exact (hall z).trans (hall z').symm

/-- **Milne, Theorem 1.17, first statement, as recorded, is false**: the connected complex manifold
`PeriodGluedPlane` (not Hausdorff, not compact) has no nonconstant meromorphic function. -/
@[kb "milne2017mf" "Theorem 1.17, pdf p. 20: the named statement needs compactness and the Hausdorff axiom"]
theorem not_existsNonconstantStatement :
    ¬ ModularFormsKB.Milne.RiemannSurface.ExistsNonconstantStatement PeriodGluedPlane := by
  rintro ⟨⟨f, x, x', hne⟩⟩
  exact hne (meromorphic_const f x x')

end ModularFormsKB.Milne.RS
