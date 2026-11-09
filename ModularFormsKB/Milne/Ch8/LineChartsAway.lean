import ModularFormsKB.Milne.Ch8.LineChartDescent

/-!
# Regular maps on a basic open of the affine line from charts

A variant of `exists_hom_of_charts` (`Ch8/LineCharts.lean`) for a basic open $D(s_0) \subseteq \mathbb A^1$: if every
$k$-point $w$ with $s_0(w) \ne 0$ lies in a chart for $b$, then $b$ is the map on $k$-points of a regular map
$D(s_0) \to Z$ (`exists_hom_of_charts_away`). The charts define one rational map $\mathbb A^1 \dashrightarrow Z$; its
domain of definition contains $D(s_0)$ (an open subset of $\mathbb A^1$ containing all closed points of $D(s_0)$), and
the regular map is its representative restricted to $D(s_0)$. Used for Theorem 8.6 with $N = 2$, where the moduli
variety is $\mathbb A^1 \smallsetminus \{4\}$.
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite Polynomial

noncomputable section

namespace ModularFormsKB.Milne

variable {k : Type u} [Field k] [IsAlgClosed k] {Z : Variety k} {b : k → (Variety.point k ⟶ Z)}

theorem mem_range_lineι_iff (s : k[X]) (w : k) :
    linePointMor w (pt0 k) ∈ Set.range (lineι (k := k) s) ↔ s.eval w ≠ 0 := by
  rw [← mem_basicOpen_linePointMor w s]
  have := PrimeSpectrum.localization_away_comap_range (Localization.Away s) s
  exact Set.ext_iff.mp this _

/-- **Gluing charts on a basic open.** -/
theorem exists_hom_of_charts_away {s₀ : k[X]} (hs₀ : s₀ ≠ 0)
    (hcov : ∀ w : k, s₀.eval w ≠ 0 → ∃ c : LineChart Z b, c.s.eval w ≠ 0) :
    ∃ ψ : lineVariety s₀ hs₀ ⟶ Z, ∀ (w : k) (hw : s₀.eval w ≠ 0), linePt s₀ hs₀ w hw ≫ ψ = b w := by
  classical
  have hZ : IsVariety k Z.obj.hom := Z.property
  have : IsSeparated Z.obj.hom := hZ.2
  have : Z.obj.left.IsSeparated := Scheme.IsSeparated.of_isSeparated Z.obj.hom
  have := isDomain_away k hs₀
  -- a first chart
  obtain ⟨w₀, hw₀⟩ : ∃ w : k, s₀.eval w ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (s₀.roots.toFinset)
    exact hw (by simpa [Multiset.mem_toFinset, mem_roots hs₀] using h w)
  obtain ⟨c₀, -⟩ := hcov w₀ hw₀
  let f := c₀.pm.toRationalMap
  have hpm : ∀ c : LineChart Z b, c.pm.toRationalMap = f := fun c ↦
    Scheme.PartialMap.toRationalMap_eq_iff.mpr (c.pm_equiv c₀)
  have hmem : ∀ (c : LineChart Z b) (w : k), c.s.eval w ≠ 0 → linePointMor w (pt0 k) ∈ f.domain := by
    intro c w hw
    rw [← hpm c]
    exact c.pm.le_domain_toRationalMap (c.mem_domain w hw)
  -- the domain of definition contains `D(s₀)`
  have hdom : (lineι (k := k) s₀).opensRange ≤ f.domain := by
    intro x hx
    by_contra hxf
    have hlc := ((lineι (k := k) s₀).opensRange.2.isLocallyClosed).inter
      f.domain.2.isClosed_compl.isLocallyClosed
    obtain ⟨y, ⟨hy1, hy2⟩, hyc⟩ := nonempty_inter_closedPoints (⟨x, hx, hxf⟩ : Set.Nonempty
      (((lineι (k := k) s₀).opensRange : Set _) ∩ (f.domain : Set _)ᶜ)) hlc
    obtain ⟨w, rfl⟩ := exists_eq_linePoint y (mem_closedPoints_iff.mp hyc)
    have hw : s₀.eval w ≠ 0 := (mem_range_lineι_iff s₀ w).mp hy1
    obtain ⟨c, hc⟩ := hcov w hw
    exact hy2 (hmem c w hc)
  have hF : f.toPartialMap.toRationalMap = f := Scheme.RationalMap.toRationalMap_toPartialMap f
  have hdom' : (lineι (k := k) s₀).opensRange ≤ f.toPartialMap.domain := hdom
  let ψ₀ : Spec (CommRingCat.of (Localization.Away s₀)) ⟶ Z.obj.left :=
    (lineι s₀).isoOpensRange.hom ≫ (Spec (CommRingCat.of k[X])).homOfLE hdom' ≫ f.toPartialMap.hom
  -- every chart agrees with `ψ₀` on `D(c.s * s₀)`
  have hmor : ∀ c : LineChart Z b, Spec.map (CommRingCat.ofHom (awayLeft c.s s₀).toRingHom) ≫ c.mor =
      Spec.map (CommRingCat.ofHom (awayRight c.s s₀).toRingHom) ≫ ψ₀ := by
    intro c
    have heq : c.pm.equiv f.toPartialMap :=
      Scheme.PartialMap.toRationalMap_eq_iff.mp ((hpm c).trans hF.symm)
    have hl := opensRange_le_of_eq _ (lineι_mul_left (k := k) c.s s₀)
    have hr := opensRange_le_of_eq _ (lineι_mul_right (k := k) c.s s₀)
    have h := (Scheme.PartialMap.equiv_iff_of_isSeparated_of_le (S := Limits.terminal Scheme)
      (dense_range_lineι (mul_ne_zero c.hs hs₀)) hl (hr.trans hdom')).mp heq
    have h2 := congrArg ((lineι (c.s * s₀)).isoOpensRange.hom ≫ ·) h
    change (lineι (c.s * s₀)).isoOpensRange.hom ≫ (Spec (CommRingCat.of k[X])).homOfLE hl ≫
      (lineι c.s).isoOpensRange.inv ≫ c.mor = (lineι (c.s * s₀)).isoOpensRange.hom ≫
      (Spec (CommRingCat.of k[X])).homOfLE (hr.trans hdom') ≫ f.toPartialMap.hom at h2
    rw [reassoc_of% (isoOpensRange_hom_homOfLE hl _ (lineι_mul_left c.s s₀))] at h2
    rw [h2, ← isoOpensRange_hom_homOfLE hr _ (lineι_mul_right c.s s₀)]
    simp only [ψ₀, Category.assoc, Iso.inv_hom_id_assoc]
    rw [Scheme.homOfLE_homOfLE_assoc]
  have hval : ∀ (w : k) (hw : s₀.eval w ≠ 0), linePtMor s₀ w hw ≫ ψ₀ = (b w).hom.left := by
    intro w hw
    obtain ⟨c, hc⟩ := hcov w hw
    have := isDomain_away k c.hs
    have := isDomain_away k (mul_ne_zero c.hs hs₀)
    have hcw : (c.s * s₀).eval w ≠ 0 := by rw [eval_mul]; exact mul_ne_zero hc hw
    have eR := congrArg (fun φ ↦ φ.hom.left) (linePt_awayRight c.hs hs₀ w hcw)
    have eL := congrArg (fun φ ↦ φ.hom.left) (linePt_awayLeft c.hs hs₀ w hcw)
    change linePtMor _ w hcw ≫ Spec.map (CommRingCat.ofHom (awayRight c.s s₀).toRingHom) =
      linePtMor s₀ w hw at eR
    change linePtMor _ w hcw ≫ Spec.map (CommRingCat.ofHom (awayLeft c.s s₀).toRingHom) =
      linePtMor c.s w hc at eL
    rw [← eR, Category.assoc, ← hmor, ← Category.assoc, eL, ← c.val w hc]
    rfl
  -- `ψ₀` lies over `k`
  have hover : ψ₀ ≫ Z.obj.hom = specStructure k (Localization.Away s₀) := by
    have := isDomain_away k (mul_ne_zero c₀.hs hs₀)
    let ι' := Spec.map (CommRingCat.ofHom (awayRight c₀.s s₀).toRingHom)
    have : IsOpenImmersion ι' := by
      have h1 : IsOpenImmersion (ι' ≫ lineι s₀) := by
        rw [← lineι_mul_right]; infer_instance
      exact IsOpenImmersion.of_comp ι' (lineι s₀)
    have : IsDominant ι' := by
      obtain ⟨y⟩ := nonempty_spec_away (k := k) (mul_ne_zero c₀.hs hs₀)
      exact ⟨ι'.isOpenEmbedding.isOpen_range.dense ⟨_, y, rfl⟩⟩
    refine ext_of_isDominant_of_isSeparated (Limits.terminal.from _) (Limits.terminal.hom_ext _ _) ι' ?_
    have hc0 : c₀.mor ≫ Z.obj.hom = specStructure k (Localization.Away c₀.s) := Over.w c₀.m.hom
    rw [← Category.assoc, ← hmor, Category.assoc, hc0]
    rw [specStructure, specStructure, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    change awayLeft c₀.s s₀ (algebraMap k _ a) = awayRight c₀.s s₀ (algebraMap k _ a)
    rw [AlgHom.commutes, AlgHom.commutes]
  refine ⟨⟨Over.homMk ψ₀ hover⟩, fun w hw ↦ ?_⟩
  refine InducedCategory.hom_ext (Over.OverMorphism.ext ?_)
  exact hval w hw

end ModularFormsKB.Milne
