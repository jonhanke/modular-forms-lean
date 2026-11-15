import ModularFormsKB.Milne.Wave15.Cochains

/-!
# A disc system adapted to a point

For a point `a` of a compact Riemann surface there is a disc system `D` with a disc centred at `a` (index `i₀`) such
that no other disc of radius `S/4` meets the closed coordinate disc `z₀⁻¹(B̄(z₀(a), S₀/16))`
(`exists_adapted`). On such a system the principal parts `(z₀ - z₀(a))⁻ᵏ` define bounded cocycles
(`MittagLeffler.lean`).
-/

open Set Metric Topology TopologicalSpace

universe u

noncomputable section

namespace ModularFormsKB.Milne.Wave15

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [CompactSpace X] [T2Space X]

/-- Every point of a chart target is the centre of a closed disc inside any open neighbourhood. -/
theorem exists_closedBall_subset {s : Set ℂ} (hs : IsOpen s) {c : ℂ} (hc : c ∈ s) :
    ∃ S > 0, closedBall c S ⊆ s := by
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 hs c hc
  exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεs⟩

/-- **A disc system adapted to `a`.** -/
theorem exists_adapted (a : X) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (D : DiscSystem X ι) (i₀ : ι), D.pt i₀ = a ∧
      ∀ j, j ≠ i₀ → ∀ x ∈ D.V (1 / 4) j, x ∈ (D.e i₀).source → D.S i₀ / 16 < ‖D.e i₀ x - D.c i₀‖ := by
  classical
  set e₀ := chartAt ℂ a
  obtain ⟨S₀, hS₀, hS₀t⟩ := exists_closedBall_subset e₀.open_target (mem_chart_target ℂ a)
  -- the closed disc `A` around `a`
  set A : Set X := e₀.symm '' closedBall (e₀ a) (S₀ / 16) with hA
  have hAt : closedBall (e₀ a) (S₀ / 16) ⊆ e₀.target :=
    (closedBall_subset_closedBall (by linarith)).trans hS₀t
  have hAc : IsClosed A :=
    ((isCompact_closedBall _ _).image_of_continuousOn (e₀.continuousOn_symm.mono hAt)).isClosed
  -- the small disc around `a`
  set V₀ : Set X := e₀.source ∩ e₀ ⁻¹' ball (e₀ a) (S₀ / 8)
  have hV₀ : IsOpen V₀ := e₀.continuousOn.isOpen_inter_preimage e₀.open_source isOpen_ball
  have hAV₀ : A ⊆ V₀ := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨e₀.map_target (hAt hw), ?_⟩
    rw [mem_preimage, e₀.right_inv (hAt hw), mem_ball]
    exact (mem_closedBall.1 hw).trans_lt (by linarith)
  -- discs around points off `A`
  have hdisc : ∀ y : {y : X // y ∉ A}, ∃ S > 0, closedBall (chartAt ℂ (y : X) y) S ⊆
      (chartAt ℂ (y : X)).target ∩ (chartAt ℂ (y : X)).symm ⁻¹' Aᶜ := fun y ↦ by
    refine exists_closedBall_subset ((chartAt ℂ (y : X)).continuousOn_symm.isOpen_inter_preimage
      (chartAt ℂ (y : X)).open_target hAc.isOpen_compl) ⟨mem_chart_target ℂ (y : X), ?_⟩
    rw [mem_preimage, (chartAt ℂ (y : X)).left_inv (mem_chart_source ℂ (y : X))]
    exact y.2
  choose Sy hSy hSyt using hdisc
  set U : {y : X // y ∉ A} → Set X := fun y ↦ (chartAt ℂ (y : X)).source ∩
    chartAt ℂ (y : X) ⁻¹' ball (chartAt ℂ (y : X) y) (Sy y / 8)
  have hUo : ∀ y, IsOpen (U y) := fun y ↦
    (chartAt ℂ (y : X)).continuousOn.isOpen_inter_preimage (chartAt ℂ (y : X)).open_source isOpen_ball
  have hcov : V₀ᶜ ⊆ ⋃ y, U y := fun x hx ↦ by
    have hxA : x ∉ A := fun h ↦ hx (hAV₀ h)
    refine mem_iUnion.2 ⟨⟨x, hxA⟩, mem_chart_source ℂ x, ?_⟩
    simp only [mem_preimage, mem_ball, dist_self]
    have := hSy ⟨x, hxA⟩
    positivity
  obtain ⟨t, ht⟩ := (hV₀.isClosed_compl.isCompact).elim_finite_subcover U hUo hcov
  -- the disc system indexed by `Option t`
  let pt : Option t → X := fun o ↦ o.elim a fun y ↦ ((y : {y : X // y ∉ A}) : X)
  let S : Option t → ℝ := fun o ↦ o.elim S₀ fun y ↦ Sy y
  have hSyt' : ∀ y : {y : X // y ∉ A}, closedBall (chartAt ℂ (y : X) y) (Sy y) ⊆
      (chartAt ℂ (y : X)).target := fun y ↦ (hSyt y).trans inter_subset_left
  let D : DiscSystem X (Option t) :=
    { pt := pt
      S := S
      S_pos := fun o ↦ by cases o <;> simp [S, hS₀, hSy]
      closedBall_subset := fun o ↦ by
        cases o with
        | none => exact hS₀t
        | some y => exact hSyt' y
      cover := fun x ↦ by
        by_cases hx : x ∈ V₀
        · exact ⟨none, hx.1, hx.2⟩
        · obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht hx)
          exact ⟨some ⟨y, hy⟩, hxy.1, hxy.2⟩ }
  refine ⟨Option t, inferInstance, inferInstance, D, none, rfl, ?_⟩
  intro j hj x hx hx₀
  obtain ⟨y, rfl⟩ := Option.ne_none_iff_exists'.1 hj
  -- `x` lies in the disc around `y`, hence off `A`
  have hxA : x ∉ A := by
    have hxs : x ∈ (D.e (some y)).source := hx.1
    have h2 : D.e (some y) x ∈ ball (D.c (some y)) (1 / 4 * D.S (some y)) := hx.2
    have hb : D.e (some y) x ∈ closedBall (D.c (some y)) (D.S (some y)) := by
      refine mem_closedBall.2 ((mem_ball.1 h2).le.trans ?_)
      change 1 / 4 * Sy y ≤ Sy y
      linarith [hSy (y : {y : X // y ∉ A})]
    have h3 := (hSyt y hb).2
    have h4 : (D.e (some y)).symm (D.e (some y) x) ∈ Aᶜ := h3
    rwa [(D.e (some y)).left_inv hxs] at h4
  by_contra hle
  refine hxA ⟨e₀ x, mem_closedBall.2 ?_, e₀.left_inv hx₀⟩
  rw [dist_eq_norm]
  exact not_lt.1 hle

end ModularFormsKB.Milne.Wave15
