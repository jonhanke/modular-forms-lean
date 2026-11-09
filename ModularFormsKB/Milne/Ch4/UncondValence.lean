import ModularFormsKB.Milne.Ch4.UncondDifferential
import ModularFormsKB.Milne.RiemannSurface.Results
import ModularFormsKB.Milne.RiemannSurface.Differential

/-!
# Milne, Proposition 4.12, from the degree of a canonical divisor

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Section 4, Proposition 4.12 (pdf p. 53).

Milne derives the valence formula from Lemma 4.11 (proved unconditionally in
`ModularFormsKB.Milne.UncondDiff.modularFormDifferential`) and Corollary 1.21, $\deg\operatorname{div}(\omega) =
2g - 2$ for a nonzero meromorphic differential $\omega$ on $X(\Gamma)$. On main, Corollary 1.21 is
`ModularFormsKB.Milne.RiemannSurface.degree_canonical_and_ell_canonical`, conditional on Riemann–Roch with an
unnamed integer `g`; its identification with `genus` is the remaining analytic input. The degree statement for
`genus` is recorded here as the named statement `CanonicalDegreeStatement X`.

## Reduction
For $\omega = F\,(dJ)^k$ (Lemma 4.11), $\mathrm{ord}_P(\omega) = \mathrm{ord}_P(F) + k\,\mathrm{ord}_P(dJ)$, so
$\sum_P \mathrm{ord}_P(\omega) = \deg\operatorname{div}(F) + k\deg\operatorname{div}(dJ) = k(2g-2)$, and Lemma 4.11
turns the left side into the valence sum minus $k\epsilon_\infty$.
-/

open UpperHalfPlane Complex Filter Topology ModularForm MulAction Function
open scoped MatrixGroups Manifold Real ContDiff

noncomputable section

namespace ModularFormsKB.Milne

/-- The genus of Section 4 (`ModularFormsKB.Milne.genus`) is the genus of Section 1
(`ModularFormsKB.Milne.RiemannSurface.genus`): the two spaces of holomorphic differentials have the same definition. -/
theorem genus_eq_riemannSurface_genus (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] :
    genus X = RiemannSurface.genus X := rfl

/-- **Corollary 1.21, degree part, for the genus** (named statement): on the Riemann surface `X`, the divisor of
every nonzero meromorphic differential form has degree $2g - 2$, $g$ the genus. It follows from Riemann–Roch
(`RiemannSurface.RiemannRochStatement X`) by `RiemannSurface.degree_canonical_and_ell_canonical` once the integer of
Riemann–Roch is identified with the genus ($\ell(K) = g$). -/
@[kb "milne2017mf" "Corollary 1.21, pdf p. 21"]
structure CanonicalDegreeStatement (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop where
  out : ∀ θ : RiemannSurface.MeromorphicDifferential X, ¬ θ.IsZero →
    TauCeti.AlgebraicGeometry.WeilDivisor.degree θ.divisor = 2 * (RiemannSurface.genus X : ℤ) - 2

/-- An element of `SL(2, ℤ)` with vanishing lower-left entry preserves imaginary parts. -/
theorem im_smul_of_entry_eq_zero (t : SL(2, ℤ)) (h : t 1 0 = 0) (w : ℍ) :
    (t • w).im = w.im := by
  have hdet := Matrix.SpecialLinearGroup.det_coe t
  rw [Matrix.det_fin_two, h] at hdet
  have h1 : ((t 1 1 : ℤ) : ℝ) ^ 2 = 1 := by
    simp only [mul_zero, sub_zero] at hdet
    rcases Int.eq_one_or_neg_one_of_mul_eq_one (u := t 1 1) (v := t 0 0)
      (by rw [mul_comm]; exact hdet) with h | h <;> simp [h]
  have key := UpperHalfPlane.im_smul_eq_div_normSq (t : GL (Fin 2) ℝ) w
  have hd : Complex.normSq (UpperHalfPlane.denom (t : GL (Fin 2) ℝ) w) = 1 := by
    simp [UpperHalfPlane.denom, Complex.normSq_apply, h]
    rw [← sq]; exact h1
  rw [hd] at key
  simpa using key

/-- The modular curve of a finite-index subgroup of `SL(2, ℤ)` is compact. -/
theorem compactSpace_modularCurve (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    CompactSpace (modularCurve Γ) := by
  classical
  have hmk : ∀ γ ∈ Γ, ∀ x : ℍ, Quotient.mk (orbitRel (Γ.map sl2zToPSL2R) ℍ) (γ • x) =
      Quotient.mk (orbitRel (Γ.map sl2zToPSL2R) ℍ) x := by
    intro γ hγ x
    have h := orbitRel.Quotient.quotient_smul_eq
      (g := (⟨sl2zToPSL2R γ, Subgroup.mem_map_of_mem _ hγ⟩ : Γ.map sl2zToPSL2R)) (a := x)
    simpa only [MulAction.subgroup_smul_def, UpperHalfPlane.sl2zToPSL2R_smul] using h
  choose g hgC using fun C : (Γ.map sl2zToPSL2R).CuspOrbit => Γ.cuspOrbitOfSL2Z_surjective C
  choose D hD1 hD2 hD3 using fun C => exists_cuspDatum_of_sl2z Γ (g C)
  have hDC : ∀ C, (D C).cuspOrbit = C := fun C => (hD1 C).trans (hgC C)
  have : Finite (SL(2, ℤ) ⧸ Γ) := Subgroup.finite_quotient_of_finiteIndex
  have hR : (Set.range fun q : SL(2, ℤ) ⧸ Γ => (q.out)⁻¹).Finite := Set.finite_range _
  apply Subgroup.CompactifiedQuotient.compactSpace_of_compact_truncations D hDC
  intro A
  obtain ⟨T, hT⟩ := (Set.finite_range A).bddAbove
  refine ⟨⋃ r ∈ Set.range (fun q : SL(2, ℤ) ⧸ Γ => (q.out)⁻¹),
    (fun x => r • x) '' _root_.ModularGroup.truncatedFundamentalDomain T,
    hR.isCompact_biUnion fun r _ => (_root_.ModularGroup.isCompact_truncatedFundamentalDomain T).image
      (by
        have : (fun x : ℍ => r • x) = fun x => sl2zToPSL2R r • x := by
          funext x; exact (UpperHalfPlane.sl2zToPSL2R_smul r x).symm
        rw [this]; exact continuous_const_smul _), ?_⟩
  intro q
  induction q using Quotient.inductionOn with
  | h z =>
    obtain ⟨g0, hg0⟩ := _root_.ModularGroup.exists_smul_mem_fd z
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Γ g0
    have hprod : (h : SL(2, ℤ)) * ((QuotientGroup.mk g0 : SL(2, ℤ) ⧸ Γ).out)⁻¹ = g0⁻¹ := by
      rw [hh]; group
    have hz : z = ((h : SL(2, ℤ)) * ((QuotientGroup.mk g0 : SL(2, ℤ) ⧸ Γ).out)⁻¹) • (g0 • z) := by
      rw [hprod, inv_smul_smul]
    have hq : Quotient.mk (orbitRel (Γ.map sl2zToPSL2R) ℍ) z =
        Quotient.mk (orbitRel (Γ.map sl2zToPSL2R) ℍ)
          (((QuotientGroup.mk g0 : SL(2, ℤ) ⧸ Γ).out)⁻¹ • (g0 • z)) := by
      conv_lhs => rw [hz, mul_smul]
      exact hmk h h.2 _
    by_cases hy : (g0 • z).im ≤ T
    · left
      refine ⟨_, Set.mem_iUnion₂.mpr ⟨_, ⟨_, rfl⟩, g0 • z, ⟨hg0, hy⟩, rfl⟩, hq.symm⟩
    · right
      set r := ((QuotientGroup.mk g0 : SL(2, ℤ) ⧸ Γ).out)⁻¹ with hr
      set w := g0 • z with hw
      obtain ⟨h2, hh2, h2e⟩ := (Γ.cuspOrbitOfSL2Z_eq_iff (g (Γ.cuspOrbitOfSL2Z r)) r).mp
        (hgC (Γ.cuspOrbitOfSL2Z r))
      have hs : (D (Γ.cuspOrbitOfSL2Z r)).scaling =
          (sl2zToPSL2R (g (Γ.cuspOrbitOfSL2Z r)))⁻¹ := by
        rw [← hD2, inv_inv]
      have hsm : (D (Γ.cuspOrbitOfSL2Z r)).scaling • (h2 • r • w) =
          ((g (Γ.cuspOrbitOfSL2Z r))⁻¹ * h2 * r) • w := by
        rw [hs, ← map_inv, UpperHalfPlane.sl2zToPSL2R_smul, mul_smul, mul_smul]
      refine ⟨Γ.cuspOrbitOfSL2Z r, h2 • r • w, ?_, (hmk h2 hh2 _).trans hq.symm⟩
      rw [TauCeti.Subgroup.CuspDatum.mem_horodisc, hsm, im_smul_of_entry_eq_zero _ h2e]
      exact lt_of_le_of_lt (hT ⟨_, rfl⟩) (lt_of_not_ge hy)

/-- A finitely supported sum over the compactified quotient splits into the points of the coarse quotient and the
cusps. -/
theorem finsum_compactifiedQuotient {Γ : Subgroup PSL(2, ℝ)} {M : Type*} [AddCommMonoid M]
    (g : Γ.CompactifiedQuotient → M) (hg : (Function.support g).Finite) :
    ∑ᶠ x, g x = (∑ᶠ p, g (Subgroup.CompactifiedQuotient.ofQuotient p)) +
      ∑ᶠ C, g (Subgroup.CompactifiedQuotient.ofCusp C) := by
  open Subgroup.CompactifiedQuotient in
  have hq : Function.Injective (ofQuotient (Γ := Γ)) := fun a b h => by cases h; rfl
  have hc : Function.Injective (ofCusp (Γ := Γ)) := fun a b h => by cases h; rfl
  have hU : (Set.univ : Set Γ.CompactifiedQuotient) =
      Set.range (Subgroup.CompactifiedQuotient.ofQuotient (Γ := Γ)) ∪
        Set.range (Subgroup.CompactifiedQuotient.ofCusp (Γ := Γ)) := by
    ext x; cases x <;> simp
  have hD : Disjoint (Set.range (Subgroup.CompactifiedQuotient.ofQuotient (Γ := Γ)))
      (Set.range (Subgroup.CompactifiedQuotient.ofCusp (Γ := Γ))) := by
    rw [Set.disjoint_left]; rintro _ ⟨a, rfl⟩ ⟨b, h⟩; cases h
  rw [← finsum_mem_univ, hU, finsum_mem_union' hD (hg.subset Set.inter_subset_right)
    (hg.subset Set.inter_subset_right), finsum_mem_range hq, finsum_mem_range hc]

/-- Mathlib's cusp orbits of `γ⁻¹ ∞`-type cosets agree iff Tau Ceti's criterion holds. -/
theorem mathlib_cusp_eq_iff (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (γ γ' : SL(2, ℤ)) :
    cosetToCuspOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) ⟦γ⁻¹⟧ = cosetToCuspOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) ⟦γ'⁻¹⟧ ↔
      ∃ h ∈ Γ, (γ⁻¹ * h * γ') 1 0 = 0 := by
  rw [cosetToCuspOrbit_apply_mk, cosetToCuspOrbit_apply_mk]
  simp only [inv_inv]
  rw [Quotient.eq]
  have key (h : SL(2, ℤ)) : Matrix.SpecialLinearGroup.mapGL ℝ h • Matrix.SpecialLinearGroup.mapGL ℝ γ' • (OnePoint.infty : OnePoint ℝ) = Matrix.SpecialLinearGroup.mapGL ℝ γ • OnePoint.infty ↔
      (γ⁻¹ * h * γ') 1 0 = 0 := by
    have e (x : SL(2, ℤ)) : Matrix.SpecialLinearGroup.mapGL ℝ x • (OnePoint.infty : OnePoint ℝ) = OnePoint.infty ↔
        x 1 0 = 0 := by
      rw [OnePoint.smul_infty_eq_self_iff]
      simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    rw [← e]
    simp only [map_mul, map_inv, mul_smul]
    rw [inv_smul_eq_iff]
  constructor
  · rintro ⟨⟨g, hg⟩, hgx⟩
    obtain ⟨h, hh, rfl⟩ := hg
    have := congrArg Subtype.val hgx
    exact ⟨h, hh, (key h).mp this⟩
  · rintro ⟨h, hh, hx⟩
    exact ⟨⟨Matrix.SpecialLinearGroup.mapGL ℝ h, h, hh, rfl⟩, Subtype.ext ((key h).mpr hx)⟩

/-- Mathlib's cusp orbits of `Γ` (used by `cuspRep`, `cuspCount`, `valenceSum`) correspond to Tau Ceti's cusp orbits
of the image of `Γ` in `PSL(2, ℝ)`, the cusps of `modularCurve Γ`. -/
theorem bijective_cuspOrbitOfSL2Z_cuspRep (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    Function.Bijective (fun c : CuspOrbits (Γ : Subgroup (GL (Fin 2) ℝ)) ↦ Γ.cuspOrbitOfSL2Z (cuspRep Γ c)) := by
  have spec (c : CuspOrbits (Γ : Subgroup (GL (Fin 2) ℝ))) :
      cosetToCuspOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) ⟦(cuspRep Γ c)⁻¹⟧ = c := by
    have := (surjective_cosetToCuspOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) c).choose_spec
    simpa [cuspRep] using this
  constructor
  · intro c c' h
    rw [Subgroup.cuspOrbitOfSL2Z_eq_iff, ← mathlib_cusp_eq_iff, spec, spec] at h
    exact h
  · intro C
    obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
    refine ⟨cosetToCuspOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) ⟦γ⁻¹⟧, ?_⟩
    simp only
    rw [Subgroup.cuspOrbitOfSL2Z_eq_iff, ← mathlib_cusp_eq_iff, spec]

namespace UncondValence

section DJ

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The differential $dJ$ of a meromorphic function `J`, as a meromorphic differential form. -/
def dOf (J : X → ℂ) (hJ : ∀ y, TauCeti.RiemannSurface.MeromorphicAt J y) :
    RiemannSurface.MeromorphicDifferential X where
  coeff x u := deriv (J ∘ (chartAt ℂ x).symm) u
  meromorphicAt x u hu := (UncondDiff.meromorphicAt_comp_chartAt_symm hJ x hu).deriv
  compat x y u hu huy := by
    have h := (UncondDiff.kDiff (fun _ ↦ (1 : ℂ)) J (fun _ ↦ TauCeti.RiemannSurface.meromorphicAt_const 1 _)
      hJ 1).compat x y u hu huy
    have e : UncondDiff.kDiffOf (fun _ ↦ (1 : ℂ)) J 1 x = fun u ↦ deriv (J ∘ (chartAt ℂ x).symm) u := by
      funext u; simp [UncondDiff.kDiffOf]
    simp only [UncondDiff.kDiff, e, UncondDiff.kDiffOf, one_mul, zpow_one] at h
    exact h

end DJ

section Orders

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

open TauCeti.RiemannSurface in
/-- $\mathrm{ord}_x(F\,(dJ)^k) = \mathrm{ord}_x(F) + k\,\mathrm{ord}_x(dJ)$. -/
theorem order_kDiff (F J : X → ℂ) (hF : ∀ y, MeromorphicAt F y) (hJ : ∀ y, MeromorphicAt J y) (k : ℤ) (x : X) :
    (UncondDiff.kDiff F J hF hJ k).order x = meromorphicOrderAt F x + k * (dOf J hJ).ord x := by
  change _root_.meromorphicOrderAt ((F ∘ (chartAt ℂ x).symm) * deriv (J ∘ (chartAt ℂ x).symm) ^ k)
    (chartAt ℂ x x) = _
  rw [_root_.meromorphicOrderAt_mul (hF x) ((hJ x).deriv.zpow k), _root_.meromorphicOrderAt_zpow (hJ x).deriv]
  rfl

variable [ConnectedSpace X]

open TauCeti.RiemannSurface MeromorphicFunction in
theorem order_ofMeromorphic {F : X → ℂ} (hF : ∀ y, MeromorphicAt F y) (x : X) :
    order x (ofMeromorphic hF) = meromorphicOrderAt F x := by
  rw [order_apply]
  exact meromorphicOrderAt_congr (finitePart_ofMeromorphic_eventuallyEq hF x)

open TauCeti.RiemannSurface MeromorphicFunction in
theorem meromorphicOrderAt_ne_top {F : X → ℂ} (hF : ∀ y, MeromorphicAt F y) (h0 : ofMeromorphic hF ≠ 0)
    (x : X) : meromorphicOrderAt F x ≠ ⊤ := by
  rw [← order_ofMeromorphic hF x]
  exact fun h ↦ h0 ((AddValuation.top_iff _).1 h)

open TauCeti.RiemannSurface MeromorphicFunction in
/-- If `J` is not constant, $dJ$ has finite order everywhere. -/
theorem dOf_ord_ne_top {J : X → ℂ} (hJ : ∀ y, MeromorphicAt J y)
    (hnc : ∀ c : ℂ, ofMeromorphic hJ ≠ algebraMap ℂ (MeromorphicFunction X) c) (x : X) :
    (dOf J hJ).ord x ≠ ⊤ := by
  set g := J ∘ (chartAt ℂ x).symm
  set u := chartAt ℂ x x
  have hg : _root_.MeromorphicAt g u := hJ x
  change _root_.meromorphicOrderAt (deriv g) u ≠ ⊤
  have hne : _root_.meromorphicOrderAt g u ≠ ⊤ := by
    have := meromorphicOrderAt_ne_top hJ (by simpa using hnc 0) x
    exact this
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
  by_cases hn0 : n = 0
  · subst hn0
    obtain ⟨h, hha, hh0, hgh⟩ := (_root_.meromorphicOrderAt_eq_int_iff hg).1 (by rw [← hn])
    set c := h u
    have hJc : ∀ y, MeromorphicAt (fun y ↦ J y - c) y := fun y ↦ (hJ y).sub (meromorphicAt_const c y)
    -- `g - c` has positive finite order at `u`
    have hgc : (fun v ↦ g v - c) =ᶠ[𝓝[≠] u] fun v ↦ h v - c := by
      filter_upwards [hgh] with v hv
      simp [hv]
    have hpos : 0 < _root_.meromorphicOrderAt (fun v ↦ g v - c) u := by
      rw [_root_.meromorphicOrderAt_congr hgc]
      have hha' : AnalyticAt ℂ (fun v ↦ h v - c) u := hha.sub analyticAt_const
      have hcont : Tendsto (fun v ↦ h v - c) (𝓝[≠] u) (𝓝 0) := by
        have := hha'.continuousAt.tendsto
        simp only [sub_self, c] at this
        exact this.mono_left nhdsWithin_le_nhds
      exact (tendsto_zero_iff_meromorphicOrderAt_pos hha'.meromorphicAt).1 hcont
    have hfin : _root_.meromorphicOrderAt (fun v ↦ g v - c) u ≠ ⊤ := by
      have h1 := meromorphicOrderAt_ne_top hJc (fun h0 ↦ hnc c ?_) x
      · exact h1
      rw [ofMeromorphic_sub hJ (fun y ↦ meromorphicAt_const c y), ofMeromorphic_const, sub_eq_zero] at h0
      exact h0
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hfin
    have hm0 : (m : ℂ) ≠ 0 := by
      have : (0 : WithTop ℤ) < m := by rw [hm]; exact hpos
      exact_mod_cast (show m ≠ 0 by exact_mod_cast this.ne')
    have hd := _root_.meromorphicOrderAt_deriv_eq_sub_one hm0 hm.symm
    have hdd : deriv (fun v ↦ g v - c) = deriv g := funext fun v ↦ deriv_sub_const _
    rw [hdd] at hd
    rw [hd]
    exact WithTop.coe_ne_top
  · have hd := _root_.meromorphicOrderAt_deriv_eq_sub_one (by exact_mod_cast hn0) hn.symm
    rw [hd]
    exact WithTop.coe_ne_top

end Orders

section Degrees

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [CompactSpace X] [ConnectedSpace X] [T2Space X]

open TauCeti.RiemannSurface MeromorphicFunction in
/-- **Proposition 1.12 (a)** for a function `X → ℂ`: $\sum_x \mathrm{ord}_x(F) = 0$. -/
theorem finsum_order_eq_zero {F : X → ℂ} (hF : ∀ y, MeromorphicAt F y) (h0 : ofMeromorphic hF ≠ 0) :
    ∑ᶠ x, (meromorphicOrderAt F x).untop₀ = 0 := by
  set D := RiemannSurface.principalDivisor X (ofMeromorphic hF)
  have hD : ∀ x, D x = (meromorphicOrderAt F x).untop₀ := by
    intro x
    have := RiemannSurface.coe_principalDivisor_apply h0 x
    rw [order_ofMeromorphic hF x] at this
    rw [← this, WithTop.untop₀_coe]
  have hdeg := RiemannSurface.degree_principalDivisor (ofMeromorphic hF)
  rw [TauCeti.AlgebraicGeometry.WeilDivisor.degree_apply] at hdeg
  rw [← hdeg, ← finsum_congr hD, finsum_eq_sum_of_support_subset _ (s := D.support)]
  intro x hx
  simpa using hx

/-- The degree of the divisor of a nonzero differential form is the finite sum of its orders. -/
theorem degree_divisor_eq_finsum {θ : RiemannSurface.MeromorphicDifferential X} (hθ : ¬ θ.IsZero) :
    TauCeti.AlgebraicGeometry.WeilDivisor.degree θ.divisor = ∑ᶠ x, θ.ordZ x := by
  have hfin := RiemannSurface.MeromorphicDifferential.finite_support_ordZ hθ
  unfold RiemannSurface.MeromorphicDifferential.divisor
  rw [dite_eq_left_of_eq_true (eq_true hfin), TauCeti.AlgebraicGeometry.WeilDivisor.degree_apply,
    finsum_eq_sum_of_support_subset _ (s := (Finsupp.ofSupportFinite θ.ordZ hfin).support)]
  · rfl
  · intro x hx
    simpa [Finsupp.ofSupportFinite_coe] using hx

end Degrees

section Modular

open TauCeti.RiemannSurface MeromorphicFunction UncondDiff

instance instCompactSpace (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : CompactSpace (modularCurve Γ) :=
  compactSpace_modularCurve Γ

instance instNonempty (Γ : Subgroup SL(2, ℤ)) : Nonempty (modularCurve Γ) :=
  ⟨modularCurve.proj Γ UpperHalfPlane.I⟩

instance instConnectedSpace (Γ : Subgroup SL(2, ℤ)) : ConnectedSpace (modularCurve Γ) :=
  { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

/-- $J$ has a pole of order $h$ at a cusp of width $h$. -/
theorem order_Jc_cusp {Jc : modularCurve Γ → ℂ} (hJ : ∀ z, jFun z = Jc (modularCurve.proj Γ z))
    (γ : SL(2, ℤ)) {n : ℕ} (hn : 0 < n) (hw : cuspWidth Γ γ = n) :
    meromorphicOrderAt Jc (Subgroup.CompactifiedQuotient.ofCusp (Γ.cuspOrbitOfSL2Z γ)) =
      ((-(n : ℤ) : ℤ) : WithTop ℤ) := by
  rw [order_descent_cusp hJ γ]
  unfold cuspOrder
  rw [jFun_slash, hw, order_cuspFunction_jFun hn]

/-- $J$ is not constant. -/
theorem Jc_nonconst {Jc : modularCurve Γ → ℂ} (hJm : ∀ y, MeromorphicAt Jc y)
    (hJ : ∀ z, jFun z = Jc (modularCurve.proj Γ z)) (c : ℂ) :
    ofMeromorphic hJm ≠ algebraMap ℂ (MeromorphicFunction (modularCurve Γ)) c := by
  intro hc
  obtain ⟨n, hn, hw⟩ := exists_nat_cuspWidth Γ 1
  have h1 := order_Jc_cusp hJ 1 hn hw
  rw [← order_ofMeromorphic hJm, hc] at h1
  by_cases hc0 : c = 0
  · subst hc0
    rw [map_zero, AddValuation.map_zero] at h1
    exact WithTop.top_ne_coe h1
  · rw [order_algebraMap hc0] at h1
    have : (0 : ℤ) = -n := by exact_mod_cast h1
    omega

variable {k : ℤ} {f : ℍ → ℂ}

omit [Γ.FiniteIndex] in
/-- A modular form that is somewhere not locally zero gives a nonzero function $F = f/(j')^k$ on $X(\Gamma)$. -/
theorem Fc_ne_zero {Fc Jc : modularCurve Γ → ℂ} (hFm : ∀ y, MeromorphicAt Fc y) (hJm : ∀ y, MeromorphicAt Jc y)
    (hF : ∀ z, quotJ f k z = Fc (modularCurve.proj Γ z)) (hJ : ∀ z, jFun z = Jc (modularCurve.proj Γ z))
    (hnz : ∃ z : ℍ, ¬ (f ∘ ofComplex) =ᶠ[𝓝[≠] (z : ℂ)] 0) : ofMeromorphic hFm ≠ 0 := by
  intro h0
  obtain ⟨z, hz⟩ := hnz
  apply hz
  have hF0 : meromorphicOrderAt Fc (modularCurve.proj Γ z) = ⊤ := by
    rw [← order_ofMeromorphic hFm, h0, AddValuation.map_zero]
  have h := order_interior_gen (k := k) (f := f) hFm hJm hF hJ z
  rw [order_kDiff, hF0, WithTop.top_add,
    WithTop.top_mul (by exact_mod_cast stabOrder_ne_zero z), WithTop.top_add] at h
  exact meromorphicOrderAt_eq_top_iff.1 h

omit [Γ.FiniteIndex] in
/-- The interior term of the valence sum is $\mathrm{ord}_P(\omega)$. -/
theorem interior_term {Fc Jc : modularCurve Γ → ℂ} (hFm : ∀ y, MeromorphicAt Fc y)
    (hJm : ∀ y, MeromorphicAt Jc y)
    (hF : ∀ z, quotJ f k z = Fc (modularCurve.proj Γ z)) (hJ : ∀ z, jFun z = Jc (modularCurve.proj Γ z))
    (z : ℍ) (m : ℤ) (hm : (kDiff Fc Jc hFm hJm k).order (modularCurve.proj Γ z) = m) :
    ((((_root_.meromorphicOrderAt (f ∘ ofComplex) (z : ℂ)).untopD 0 : ℤ) : ℚ) / stabOrder Γ z -
      k * (1 - 1 / (stabOrder Γ z : ℚ))) = m := by
  rw [order_interior_gen hFm hJm hF hJ z, hm]
  have he : (stabOrder Γ z : ℚ) ≠ 0 := by exact_mod_cast stabOrder_ne_zero z
  have hc : ((m : WithTop ℤ) * ((stabOrder Γ z : ℤ) : WithTop ℤ) +
      ((k * ((stabOrder Γ z : ℤ) - 1) : ℤ) : WithTop ℤ)) =
      ((m * stabOrder Γ z + k * ((stabOrder Γ z : ℤ) - 1) : ℤ) : WithTop ℤ) := by norm_cast
  rw [show ((stabOrder Γ z : WithTop ℤ)) = ((stabOrder Γ z : ℤ) : WithTop ℤ) from rfl, hc,
    WithTop.untopD_coe]
  push_cast
  field_simp
  ring

/-- The cusp term of the valence sum is $\mathrm{ord}_P(\omega) + k$. -/
theorem cusp_term (hf : IsMeromorphicModularForm Γ k f) {Fc Jc : modularCurve Γ → ℂ}
    (hFm : ∀ y, MeromorphicAt Fc y) (hJm : ∀ y, MeromorphicAt Jc y)
    (hF : ∀ z, quotJ f k z = Fc (modularCurve.proj Γ z)) (hJ : ∀ z, jFun z = Jc (modularCurve.proj Γ z))
    (γ : SL(2, ℤ)) (m : ℤ)
    (hm : (kDiff Fc Jc hFm hJm k).order (Subgroup.CompactifiedQuotient.ofCusp (Γ.cuspOrbitOfSL2Z γ)) = m) :
    (((cuspOrder Γ k f γ).untopD 0 : ℤ) : ℚ) = m + k := by
  rw [order_cusp hf hFm hJm hF hJ γ m hm, WithTop.untopD_coe]
  push_cast
  ring

end Modular

end UncondValence

open TauCeti.RiemannSurface MeromorphicFunction UncondDiff UncondValence in
/-- **Proposition 4.12** (the valence formula), from Corollary 1.21 on $X(\Gamma)$: for every subgroup $\Gamma$ of
finite index in $\mathrm{SL}_2(\mathbb Z)$, `CanonicalDegreeStatement (modularCurve Γ)` implies
`ValenceFormula Γ`. Lemma 4.11 is used in the unconditional form `UncondDiff.modularFormDifferential`. -/
@[kb "milne2017mf" "Section 4, Proposition 4.12 (pdf p. 53)"]
theorem valenceFormula_of_canonicalDegree (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hC : CanonicalDegreeStatement (modularCurve Γ)) : ValenceFormula Γ where
  formula k f hf hnz := by
    obtain ⟨Fc, hFm, hF⟩ := exists_descent (quotJ_isModularFunction hf)
    obtain ⟨Jc, hJm, hJ⟩ := exists_descent (jFun_isModularFunction' Γ)
    set dJ := dOf Jc hJm
    have hΦ := Fc_ne_zero hFm hJm hF hJ hnz
    have hFfin := meromorphicOrderAt_ne_top hFm hΦ
    have hdfin := dOf_ord_ne_top hJm (Jc_nonconst hJm hJ)
    -- the integer orders of `ω = F (dJ)^k`
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
    have hsum : ∑ᶠ x, M x = k * (2 * (RiemannSurface.genus (modularCurve Γ) : ℤ) - 2) := by
      rw [finsum_add_distrib hsF hsDk, finsum_order_eq_zero hFm hΦ, ← mul_finsum,
        ← degree_divisor_eq_finsum hdJ0, hC.out dJ hdJ0, zero_add]
    -- the valence sum, term by term
    unfold valenceSum
    have hint : ∀ p : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ,
        ((((_root_.meromorphicOrderAt (f ∘ ofComplex) (p.out : ℂ)).untopD 0 : ℤ) : ℚ) / stabOrder Γ p.out -
          k * (1 - 1 / (stabOrder Γ p.out : ℚ))) =
          (M (Subgroup.CompactifiedQuotient.ofQuotient p) : ℚ) := by
      intro p
      have hp : modularCurve.proj Γ p.out = Subgroup.CompactifiedQuotient.ofQuotient p := by
        unfold modularCurve.proj
        rw [Quotient.out_eq]
      rw [interior_term hFm hJm hF hJ p.out (M (modularCurve.proj Γ p.out)) (hM _), hp]
    have hcusp : ∀ c : CuspOrbits (Γ : Subgroup (GL (Fin 2) ℝ)),
        (((cuspOrder Γ k f (cuspRep Γ c)).untopD 0 : ℤ) : ℚ) =
          (M (Subgroup.CompactifiedQuotient.ofCusp (Γ.cuspOrbitOfSL2Z (cuspRep Γ c))) : ℚ) + k :=
      fun c ↦ cusp_term hf hFm hJm hF hJ (cuspRep Γ c) _ (hM _)
    have hce : ∑ᶠ c : CuspOrbits (Γ : Subgroup (GL (Fin 2) ℝ)),
        (M (Subgroup.CompactifiedQuotient.ofCusp (Γ.cuspOrbitOfSL2Z (cuspRep Γ c))) : ℚ) =
          ∑ᶠ C, (M (Subgroup.CompactifiedQuotient.ofCusp C) : ℚ) :=
      finsum_comp_equiv (Equiv.ofBijective _ (bijective_cuspOrbitOfSL2Z_cuspRep Γ))
        (f := fun C ↦ (M (Subgroup.CompactifiedQuotient.ofCusp C) : ℚ))
    have hk : ∑ᶠ _ : CuspOrbits (Γ : Subgroup (GL (Fin 2) ℝ)), (k : ℚ) = cuspCount Γ * k := by
      have := Fintype.ofFinite (CuspOrbits (Γ : Subgroup (GL (Fin 2) ℝ)))
      rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, cuspCount, Nat.card_eq_fintype_card,
        nsmul_eq_mul]
    rw [finsum_congr hint, finsum_congr hcusp,
      finsum_add_distrib (Set.toFinite _) (Set.toFinite _), hce, hk, ← add_assoc,
      ← finsum_compactifiedQuotient (fun x ↦ (M x : ℚ)) (hsM.subset (fun x hx ↦ by simpa using hx))]
    have hcast : ∑ᶠ x, (M x : ℚ) = ((∑ᶠ x, M x : ℤ) : ℚ) :=
      (map_finsum (Int.castAddHom ℚ) hsM).symm
    rw [hcast, hsum, genus_eq_riemannSurface_genus]
    push_cast
    ring

end ModularFormsKB.Milne
