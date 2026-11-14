import ModularFormsKB.Milne.Wave4A.GenusZero

/-!
# Milne, Example 4.13: the valence formula for meromorphic modular forms of level one

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 4, Example 4.13, pdf p. 54.

For a nonzero meromorphic modular form `f` of weight `2k` for `Γ(1)`,
`ord_{i∞}(f) + ½ ord_i(f) + ⅓ ord_ρ(f) + Σ_Q ord_Q(f) = k/6`, the sum over the points `Q` of `Γ(1)\ℍ` other than
the classes of `i` and `ρ`. The holomorphic case is Tau Ceti's `TauCeti.ModularForm.valence_formula`
(`valence_formula_one`); here the meromorphic case is read off from Proposition 4.12 for `Γ(1)`
(`valenceFormula_top`): `X(1)` has genus `0` and one cusp, `i` and `ρ` are the only elliptic points up to
equivalence, with stabilizers of orders `2` and `3` in `PSL₂(ℤ)`.
-/

open UpperHalfPlane Complex Filter Topology ModularForm MulAction
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.Wave6


open ModularFormsKB.Milne TauCeti.ModularGroup in
/-- The `SL(2, ℤ)`-orbit of `z` meets `(mk z).out` (orbit representatives are related by `SL(2, ℤ)`). -/
theorem exists_smul_out (z : ℍ) :
    ∃ γ : SL(2, ℤ), γ • z = (Quotient.mk (orbitRel ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R) ℍ) z).out := by
  have h : orbitRel ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R) ℍ
      (Quotient.mk (orbitRel ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R) ℍ) z).out z := Quotient.mk_out z
  obtain ⟨a, hg⟩ := mem_orbit_iff.1 (orbitRel_apply.1 h)
  obtain ⟨g, -, hgx⟩ := Subgroup.mem_map.1 a.2
  refine ⟨g, ?_⟩
  have hg' : (a : PSL(2, ℝ)) • z = _ := hg
  rw [← hgx, sl2zToPSL2R_smul] at hg'
  exact hg'

open ModularFormsKB.Milne in
theorem orbitRel_top_iff (z w : ℍ) :
    orbitRel ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R) ℍ z w ↔ orbitRel SL(2, ℤ) ℍ z w := by
  simp only [orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨a, h⟩
    obtain ⟨g, -, hgx⟩ := Subgroup.mem_map.1 a.2
    refine ⟨g, ?_⟩
    have h' : (a : PSL(2, ℝ)) • w = _ := h
    rw [← hgx, sl2zToPSL2R_smul] at h'
    exact h'
  · rintro ⟨a, h⟩
    exact ⟨⟨sl2zToPSL2R a, a, Subgroup.mem_top _, rfl⟩,
      by simpa [Subgroup.smul_def, sl2zToPSL2R_smul] using h⟩

open ModularFormsKB.Milne in
/-- Orbit classes for `⊤.map sl2zToPSL2R` and for `SL(2, ℤ)` agree. -/
theorem mk_eq_iff (z w : ℍ) :
    Quotient.mk (orbitRel ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R) ℍ) z = Quotient.mk _ w ↔
      (Quotient.mk'' z : orbitRel.Quotient SL(2, ℤ) ℍ) = Quotient.mk'' w :=
  by rw [Quotient.eq, Quotient.eq'']; exact orbitRel_top_iff z w

open ModularFormsKB.Milne in
/-- `stabOrder ⊤` of an orbit representative: `2` on the orbit of `i`, `3` on that of `ρ`, `1` elsewhere. -/
theorem stabOrder_top_I (γ : SL(2, ℤ)) : stabOrder ⊤ (γ • UpperHalfPlane.I) = 2 := by
  unfold stabOrder
  rw [Subgroup.card_stabilizer_map_smul_I]
  simp

open ModularFormsKB.Milne in
theorem stabOrder_top_ρ (γ : SL(2, ℤ)) : stabOrder ⊤ (γ • UpperHalfPlane.ρ) = 3 := by
  unfold stabOrder
  rw [Subgroup.card_stabilizer_map_smul_ρ]
  simp

open ModularFormsKB.Milne in
theorem stabOrder_top_eq_one {z : ℍ}
    (hI : Quotient.mk (orbitRel ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R) ℍ) z ≠ Quotient.mk _ UpperHalfPlane.I)
    (hρ : Quotient.mk (orbitRel ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R) ℍ) z ≠ Quotient.mk _ UpperHalfPlane.ρ) :
    stabOrder ⊤ z = 1 :=
  Subgroup.card_stabilizer_map_eq_one_of_orbit_ne _ (fun h ↦ hI ((mk_eq_iff _ _).2 h)) (fun h ↦ hρ ((mk_eq_iff _ _).2 h))

/-- The order at `γ • z` of a modular form for `Γ(1)` equals the order at `z`. -/
theorem order_smul {k : ℤ} {f : ℍ → ℂ} (hf : IsMeromorphicModularForm ⊤ k f) (γ : SL(2, ℤ)) (z : ℍ) :
    (meromorphicOrderAt (f ∘ ofComplex) ((γ • z : ℍ) : ℂ)).untopD 0 =
      (meromorphicOrderAt (f ∘ ofComplex) (z : ℂ)).untopD 0 := by
  have h := TauCeti.orderOfVanishingAt_slash (k := 2 * k) f (γ := Matrix.SpecialLinearGroup.mapGL ℝ γ)
    (by
      have := (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ).det_coe
      simpa using this.symm ▸ one_pos) z
  have hs : f ∣[2 * k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) = f := hf.slash γ (Subgroup.mem_top _)
  rw [hs] at h
  have hsm : Matrix.SpecialLinearGroup.mapGL ℝ γ • z = γ • z := rfl
  rw [hsm] at h
  exact h.symm

open ModularFormsKB.Milne TauCeti.RiemannSurface MeromorphicFunction UncondDiff UncondValence in
/-- The interior terms `ord_{p.out}/e_p - k(1 - 1/e_p)` of the valence sum have finite support (they are the
orders `M` of the differential `ω = F (dJ)^k` on `X(Γ)`, as in `valenceFormula_of_canonicalDegree`). -/
theorem finite_support_interior (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {k : ℤ} {f : ℍ → ℂ}
    (hf : IsMeromorphicModularForm Γ k f) (hnz : ∃ z : ℍ, ¬ (f ∘ ofComplex) =ᶠ[𝓝[≠] (z : ℂ)] 0) :
    (Function.support fun p : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ =>
      ((((_root_.meromorphicOrderAt (f ∘ ofComplex) (p.out : ℂ)).untopD 0 : ℤ) : ℚ) / stabOrder Γ p.out -
        k * (1 - 1 / (stabOrder Γ p.out : ℚ)))).Finite := by
  obtain ⟨Fc, hFm, hF⟩ := exists_descent (quotJ_isModularFunction hf)
  obtain ⟨Jc, hJm, hJ⟩ := exists_descent (jFun_isModularFunction' Γ)
  set dJ := dOf Jc hJm
  have hΦ := Fc_ne_zero hFm hJm hF hJ hnz
  have hFfin := meromorphicOrderAt_ne_top hFm hΦ
  have hdfin := dOf_ord_ne_top hJm (Jc_nonconst hJm hJ)
  set M : modularCurve Γ → ℤ := fun x ↦ (meromorphicOrderAt Fc x).untop₀ + k * dJ.ordZ x
  have hM : ∀ x, (kDiff Fc Jc hFm hJm k).order x = (M x : WithTop ℤ) := by
    intro x
    rw [order_kDiff]
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 (hFfin x)
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 (hdfin x)
    simp only [M, RiemannSurface.MeromorphicDifferential.ordZ, ← ha, WithTop.untop₀_coe]
    change ((a : WithTop ℤ) + (k : WithTop ℤ) * (dOf Jc hJm).ord x) = ((a + k * ((dOf Jc hJm).ord x).untop₀ : ℤ) : WithTop ℤ)
    rw [← hb, WithTop.untop₀_coe]
    norm_cast
  have hdJ0 : ¬ dJ.IsZero := fun h ↦ hdfin (Classical.arbitrary _) (h _)
  have hsF : (Function.support fun x ↦ (meromorphicOrderAt Fc x).untop₀).Finite := by
    refine (RiemannSurface.principalDivisor (modularCurve Γ) (ofMeromorphic hFm)).support.finite_toSet.subset ?_
    intro x hx
    have := RiemannSurface.coe_principalDivisor_apply hΦ x
    rw [order_ofMeromorphic hFm x] at this
    simp only [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    apply hx
    simp only
    rw [← this, h0]
    rfl
  have hsD : (Function.support dJ.ordZ).Finite := RiemannSurface.MeromorphicDifferential.finite_support_ordZ hdJ0
  have hsDk : (Function.support fun x ↦ k * dJ.ordZ x).Finite :=
    hsD.subset (Function.support_mul_subset_right _ _)
  have hsM : (Function.support M).Finite := (hsF.union hsDk).subset (Function.support_add _ _)
  have hint : ∀ p : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ,
      ((((_root_.meromorphicOrderAt (f ∘ ofComplex) (p.out : ℂ)).untopD 0 : ℤ) : ℚ) / stabOrder Γ p.out -
        k * (1 - 1 / (stabOrder Γ p.out : ℚ))) =
        (M (Subgroup.CompactifiedQuotient.ofQuotient p) : ℚ) := by
    intro p
    have hp : modularCurve.proj Γ p.out = Subgroup.CompactifiedQuotient.ofQuotient p := by
      unfold modularCurve.proj
      rw [Quotient.out_eq]
    rw [interior_term hFm hJm hF hJ p.out (M (modularCurve.proj Γ p.out)) (hM _), hp]
  refine (hsM.preimage (Subgroup.CompactifiedQuotient.ofQuotient_injective.injOn)).subset ?_
  intro p hp
  simp only [Function.mem_support, hint] at hp
  simpa using hp

open ModularFormsKB.Milne in
/-- `Γ(1)` has a unique cusp orbit. -/
@[instance_reducible]
def uniqueCuspOrbits_top : Unique (CuspOrbits ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) := by
  have hrange : ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R) = psl2zToPSL2R.range := by
    rw [← TauCeti.range_sl2zToPSL2R_eq_range_psl2zToPSL2R, MonoidHom.range_eq_map]
  letI : Unique ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R).CuspOrbit := by
    rw [hrange]; infer_instance
  exact (Equiv.ofBijective _ (bijective_cuspOrbitOfSL2Z_cuspRep ⊤)).unique

open ModularFormsKB.Milne in
/-- The cusp term of the valence sum for `Γ(1)` is `ord_{i∞}`, and there is one cusp. -/
theorem cusp_sum_top {k : ℤ} {f : ℍ → ℂ} (hf : IsMeromorphicModularForm ⊤ k f) :
    (∑ᶠ c : CuspOrbits ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      (((cuspOrder ⊤ k f (cuspRep ⊤ c)).untopD 0 : ℤ) : ℚ)) = (((cuspOrder ⊤ k f 1).untopD 0 : ℤ) : ℚ) ∧
    cuspCount ⊤ = 1 := by
  let _ := uniqueCuspOrbits_top
  have hc : ∀ γ : SL(2, ℤ), cuspOrder ⊤ k f γ = cuspOrder ⊤ k f 1 := by
    intro γ
    unfold cuspOrder
    rw [cuspWidth_top, cuspWidth_top, hf.slash γ (Subgroup.mem_top _), hf.slash 1 (Subgroup.mem_top _)]
  refine ⟨?_, by simp [cuspCount]⟩
  rw [finsum_unique]
  simp only [hc]

/-- **Milne, Example 4.13**, meromorphic forms: for a nonzero meromorphic modular form `f` of weight `2k` for
`Γ(1)`, `ord_{i∞}(f) + ½ ord_i(f) + ⅓ ord_ρ(f) + Σ_Q ord_Q(f) = k/6`, the sum over the classes `Q` of points of
`ℍ` with trivial stabilizer in `PSL₂(ℤ)` (that is, not equivalent to `i` or `ρ`). -/
@[kb "milne2017mf" "Section 4, Example 4.13 (pdf p. 54)"]
theorem example_4_13 (k : ℤ) (f : ℍ → ℂ) (hf : IsMeromorphicModularForm ⊤ k f)
    (h0 : ∃ z : ℍ, ¬ (f ∘ ofComplex) =ᶠ[𝓝[≠] (z : ℂ)] 0) :
    (((cuspOrder ⊤ k f 1).untopD 0 : ℤ) : ℚ)
      + 1 / 2 * (((meromorphicOrderAt (f ∘ ofComplex) (UpperHalfPlane.I : ℂ)).untopD 0 : ℤ) : ℚ)
      + 1 / 3 * (((meromorphicOrderAt (f ∘ ofComplex) (UpperHalfPlane.ρ : ℂ)).untopD 0 : ℤ) : ℚ)
      + ∑ᶠ p : orbitRel.Quotient ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R) ℍ,
          (if stabOrder ⊤ p.out = 1 then
            (((meromorphicOrderAt (f ∘ ofComplex) (p.out : ℂ)).untopD 0 : ℤ) : ℚ) else 0)
      = k / 6 := by
  classical
  have hv := (valenceFormula_top).formula k f hf h0
  have hfin := finite_support_interior ⊤ hf h0
  obtain ⟨hcs, hcc⟩ := cusp_sum_top hf
  unfold valenceSum at hv
  rw [hcs, hcc] at hv
  have hg0 : genus (modularCurve ⊤) = 0 := genus_and_canonicalDegree_top.1
  rw [hg0] at hv
  let pI : orbitRel.Quotient ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R) ℍ := Quotient.mk _ UpperHalfPlane.I
  let pρ : orbitRel.Quotient ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R) ℍ := Quotient.mk _ UpperHalfPlane.ρ
  have hne : pI ≠ pρ := fun h ↦ TauCeti.ModularGroup.orbit_mk_I_ne_orbit_mk_ρ ((mk_eq_iff _ _).1 h)
  have hIout : stabOrder ⊤ pI.out = 2 ∧
      (meromorphicOrderAt (f ∘ ofComplex) (pI.out : ℂ)).untopD 0 =
        (meromorphicOrderAt (f ∘ ofComplex) (UpperHalfPlane.I : ℂ)).untopD 0 := by
    obtain ⟨γ, hγ⟩ := exists_smul_out UpperHalfPlane.I
    change stabOrder ⊤ (Quotient.mk _ UpperHalfPlane.I).out = 2 ∧ _
    rw [← hγ]
    exact ⟨stabOrder_top_I γ, order_smul hf γ _⟩
  have hρout : stabOrder ⊤ pρ.out = 3 ∧
      (meromorphicOrderAt (f ∘ ofComplex) (pρ.out : ℂ)).untopD 0 =
        (meromorphicOrderAt (f ∘ ofComplex) (UpperHalfPlane.ρ : ℂ)).untopD 0 := by
    obtain ⟨γ, hγ⟩ := exists_smul_out UpperHalfPlane.ρ
    change stabOrder ⊤ (Quotient.mk _ UpperHalfPlane.ρ).out = 3 ∧ _
    rw [← hγ]
    exact ⟨stabOrder_top_ρ γ, order_smul hf γ _⟩
  have hone : ∀ p : orbitRel.Quotient ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R) ℍ,
      p ≠ pI → p ≠ pρ → stabOrder ⊤ p.out = 1 := by
    intro p h1 h2
    apply stabOrder_top_eq_one
    · rwa [Quotient.out_eq]
    · rwa [Quotient.out_eq]
  set oI : ℚ := (((meromorphicOrderAt (f ∘ ofComplex) (UpperHalfPlane.I : ℂ)).untopD 0 : ℤ) : ℚ) with hoI
  set oρ : ℚ := (((meromorphicOrderAt (f ∘ ofComplex) (UpperHalfPlane.ρ : ℂ)).untopD 0 : ℤ) : ℚ) with hoρ
  have hpt : ∀ p : orbitRel.Quotient ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R) ℍ,
      ((((meromorphicOrderAt (f ∘ ofComplex) (p.out : ℂ)).untopD 0 : ℤ) : ℚ) / stabOrder ⊤ p.out -
        k * (1 - 1 / (stabOrder ⊤ p.out : ℚ))) =
      (if stabOrder ⊤ p.out = 1 then
            (((meromorphicOrderAt (f ∘ ofComplex) (p.out : ℂ)).untopD 0 : ℤ) : ℚ) else 0) +
        ((if p = pI then oI / 2 - k / 2 else 0) + (if p = pρ then oρ / 3 - 2 * k / 3 else 0)) := by
    intro p
    by_cases h1 : p = pI
    · subst h1
      rw [hIout.1, hIout.2]
      simp [hne, hoI]
      ring
    by_cases h2 : p = pρ
    · subst h2
      rw [hρout.1, hρout.2]
      simp [hne.symm, hoρ]
      ring
    · rw [hone p h1 h2]
      simp [h1, h2]
  have hsupp : (Function.support fun p : orbitRel.Quotient ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R) ℍ =>
      (if stabOrder ⊤ p.out = 1 then
            (((meromorphicOrderAt (f ∘ ofComplex) (p.out : ℂ)).untopD 0 : ℤ) : ℚ) else 0)).Finite := by
    refine (hfin.union (Set.toFinite {pI, pρ})).subset ?_
    intro p hp
    by_contra hcon
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, not_or, Function.mem_support,
      ne_eq, not_not] at hcon hp
    obtain ⟨hg, h1, h2⟩ := hcon
    have := hpt p
    rw [hg] at this
    by_cases he : stabOrder ⊤ p.out = 1
    · simp only [he, h1, h2, ↓reduceIte, add_zero] at this
      refine hp ?_
      simp only [he, ↓reduceIte]
      exact this.symm
    · exact hp (by simp [he])
  have hab : (Function.support fun p : orbitRel.Quotient ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R) ℍ =>
      ((if p = pI then oI / 2 - k / 2 else 0) + (if p = pρ then oρ / 3 - 2 * k / 3 else 0))).Finite := by
    refine (Set.toFinite {pI, pρ}).subset ?_
    intro p hp
    by_contra hcon
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcon
    simp [hcon.1, hcon.2] at hp
  have ha : (Function.support fun p : orbitRel.Quotient ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R) ℍ =>
      (if p = pI then oI / 2 - k / 2 else 0)).Finite :=
    (Set.toFinite {pI}).subset (fun p hp ↦ by
      by_contra hc
      exact hp (if_neg (by simpa using hc)))
  have hb : (Function.support fun p : orbitRel.Quotient ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R) ℍ =>
      (if p = pρ then oρ / 3 - 2 * k / 3 else 0)).Finite :=
    (Set.toFinite {pρ}).subset (fun p hp ↦ by
      by_contra hc
      exact hp (if_neg (by simpa using hc)))
  have hsI : ∑ᶠ p : orbitRel.Quotient ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R) ℍ,
      (if p = pI then oI / 2 - k / 2 else 0) = oI / 2 - k / 2 := by
    rw [finsum_eq_single _ pI (fun p hp ↦ if_neg hp)]
    simp
  have hsρ : ∑ᶠ p : orbitRel.Quotient ((⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R) ℍ,
      (if p = pρ then oρ / 3 - 2 * k / 3 else 0) = oρ / 3 - 2 * k / 3 := by
    rw [finsum_eq_single _ pρ (fun p hp ↦ if_neg hp)]
    simp
  rw [finsum_congr hpt, finsum_add_distrib hsupp hab, finsum_add_distrib ha hb, hsI, hsρ] at hv
  push_cast at hv
  linarith

end ModularFormsKB.Milne.Wave6
