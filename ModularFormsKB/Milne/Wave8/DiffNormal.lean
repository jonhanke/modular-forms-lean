import ModularFormsKB.Milne.Wave7.CMComplex
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InvariantDifferential

/-!
# Milne wave 8: a morphism lifting `z ↦ αz` pulls the invariant differential back to `α ω`

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, pdf p. 126 (the
normalization of `i : R ≅ End(E)` through the action on the tangent space, used in Proposition 12.21), with
Proposition 3.3 (pdf p. 42).

For a lattice `Λ`, the curve `E(Λ) : y² = x³ - (g₂/4)x - g₃/4` carries the point `P(z) = (℘(z), ℘'(z)/2)` and the
invariant differential `ω = dx / 2y`, which is `dz` along `P`. A morphism `f : E(Λ) → E(Λ')` is `[z] ↦ [αz]`
(`Wave7.exists_mul_of_hom`); this file proves `f^*ω' = α ω` in Tau Ceti's Kähler differentials of the function
field (`pullbackDifferential_eq_smul_of_lift`).

**Proof.** Tau Ceti gives `f^*ω' = c ω` for a constant `c`
(`Hom.existsUnique_pullbackDifferential_invariantDifferential_eq_smul`). Write `x ∘ f = r(x)` with `r = N/D`
(`Isogeny.xRatFunc`) and `y ∘ f = y s(x)` (`Wave5.exists_fieldPullback_genericY_eq`). Then
`f^*ω' = d(r(x)) / (2 y s(x)) = r'(x) / s(x) · ω` (derivation rules for `d`), so
`(D N' - N D')·s_den = c · s_num · D²` as polynomials. Along `P`: `℘_{Λ'}(αz) = r(℘(z))` and `℘'_{Λ'}(αz)/2 =
℘'(z)/2 · s(℘(z))`; differentiating the first identity, `α ℘'_{Λ'}(αz) = r'(℘(z)) ℘'(z)`, so `α s(x₀) = r'(x₀) =
c s(x₀)` at a generic `x₀ = ℘(z₀)`, whence `α = c`.
-/

open Complex PeriodPair TauCeti TauCeti.Isogeny Polynomial Filter Topology WeierstrassCurve.Affine
open ModularFormsKB.Milne.Wave5 ModularFormsKB.Milne.Wave7
open scoped RatFunc

namespace ModularFormsKB.Milne.Wave8

variable {L L' : PeriodPair}

/-- A nonzero polynomial does not vanish at the generic `x`. -/
theorem aeval_genericX_ne_zero (W : WeierstrassCurve.Affine ℂ) [W.IsElliptic] {p : ℂ[X]} (hp : p ≠ 0) :
    aeval (genericX W) p ≠ 0 :=
  fun h ↦ transcendental_genericX W ⟨p, hp, h⟩

/-- The denominator `2y + a₁x + a₃` of the invariant differential of `E(Λ)` is `2y`. -/
theorem invariantDifferentialDenom_eq (M : PeriodPair) :
    invariantDifferentialDenom M.weierstrassCurve.toAffine = 2 * genericY M.weierstrassCurve.toAffine := by
  rw [invariantDifferentialDenom_def]
  have h1 : M.weierstrassCurve.toAffine.a₁ = 0 := M.weierstrassCurve_a₁
  have h3 : M.weierstrassCurve.toAffine.a₃ = 0 := M.weierstrassCurve_a₃
  rw [h1, h3, map_zero, zero_mul, add_zero, add_zero]

/-- The function field identity behind the normalization: for an isogeny `φ : E(Λ) → E(Λ')` with `φ^*ω' = c ω`,
`x ∘ φ = N(x)/D(x)` and `y ∘ φ = y s(x)`, the polynomial identity `(D N' - N D') s_den = c s_num D²` holds. -/
theorem polynomial_identity_of_pullback (φ : Isogeny L.weierstrassCurve.toAffine L'.weierstrassCurve.toAffine)
    {s : RatFunc ℂ} (hs0 : s ≠ 0)
    (hs : φ.fieldPullback (genericY L'.weierstrassCurve.toAffine) =
      genericY L.weierstrassCurve.toAffine * algebraMap (RatFunc ℂ) _ s)
    {c : ℂ} (hc : φ.pullbackDifferential (invariantDifferential L'.weierstrassCurve.toAffine) =
      c • invariantDifferential L.weierstrassCurve.toAffine) :
    (φ.xRatFunc.denom * derivative φ.xRatFunc.num - φ.xRatFunc.num * derivative φ.xRatFunc.denom) * s.denom =
      C c * s.num * φ.xRatFunc.denom ^ 2 := by
  let W := L.weierstrassCurve.toAffine
  let K := W.FunctionField
  set x := genericX W with hx
  set y := genericY W with hy'
  set N := φ.xRatFunc.num
  set Dn := φ.xRatFunc.denom
  let D := KaehlerDifferential.D ℂ K
  have hy : y ≠ 0 := genericY_ne_zero_of_a₁_a₃ L.weierstrassCurve_a₁ L.weierstrassCurve_a₃
  have hdx : D x ≠ 0 := TauCeti.D_ne_zero_of_separating (transcendental_genericX W)
  have hDn : aeval x Dn ≠ 0 := aeval_genericX_ne_zero W φ.xRatFunc.denom_ne_zero
  have hsn : aeval x s.num ≠ 0 := aeval_genericX_ne_zero W (by rwa [Ne, RatFunc.num_eq_zero_iff])
  have hsd : aeval x s.denom ≠ 0 := aeval_genericX_ne_zero W s.denom_ne_zero
  have hS : algebraMap (RatFunc ℂ) K s = aeval x s.num / aeval x s.denom := by
    nth_rewrite 1 [← RatFunc.num_div_denom s]
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      algebraMap_eq_aeval_genericX, algebraMap_eq_aeval_genericX]
  -- the left side of `hc` as a multiple of `dx`
  have hL : φ.pullbackDifferential (invariantDifferential L'.weierstrassCurve.toAffine) =
      ((2 * (y * (aeval x s.num / aeval x s.denom)))⁻¹ * ((aeval x Dn)⁻¹ ^ 2 *
        (aeval x Dn * aeval x (derivative N) - aeval x N * aeval x (derivative Dn)))) • D x := by
    rw [invariantDifferential_def, pullbackDifferential_smul, pullbackDifferential_D, map_inv₀,
      invariantDifferentialDenom_eq, map_mul, map_ofNat, hs, hS, fieldPullback_genericX_eq_aeval_div]
    change _ • D (aeval x N / aeval x Dn) = _
    rw [Derivation.leibniz_div, Derivation.map_aeval, Derivation.map_aeval]
    simp only [smul_smul, ← sub_smul]
  have hR : c • invariantDifferential W = (algebraMap ℂ K c * (2 * y)⁻¹) • D x := by
    rw [invariantDifferential_def, invariantDifferentialDenom_eq, ← algebraMap_smul K c, smul_smul]
  rw [hL, hR] at hc
  have hk := smul_left_injective K hdx hc
  by_contra hne
  apply aeval_genericX_ne_zero W (sub_ne_zero.mpr hne)
  simp only [map_sub, map_mul, map_pow, aeval_C]
  field_simp at hk
  have h2 : (2 : K) ≠ 0 := by
    have := (map_ne_zero (algebraMap ℂ K)).2 (two_ne_zero : (2 : ℂ) ≠ 0)
    rwa [map_ofNat] at this
  rw [div_left_inj' h2] at hk
  linear_combination hk

/-- A morphism `E(Λ) → E(Λ')` lifting `z ↦ αz` with `α = 0` is zero, and conversely. -/
theorem eq_zero_of_lift_zero {f : Hom L.weierstrassCurve.toAffine L'.weierstrassCurve.toAffine}
    (hf : ∀ z, f.pointMap (L.weierstrassPoint z) = L'.weierstrassPoint (0 * z)) : f = 0 :=
  hom_ext_of_weierstrassPoint' fun z ↦ by rw [hf, zero_mul, Hom.zero_pointMap, L'.weierstrassPoint_eq_zero_iff]; exact zero_mem _

/-- If the zero morphism lifts `z ↦ αz`, then `α = 0`. -/
theorem eq_zero_of_zero_lift {α : ℂ}
    (hf : ∀ z, (0 : Hom L.weierstrassCurve.toAffine L'.weierstrassCurve.toAffine).pointMap (L.weierstrassPoint z) =
      L'.weierstrassPoint (α * z)) : α = 0 := by
  by_contra hα
  obtain ⟨w, hw⟩ := exists_notMem_lattice L'
  have := hf (α⁻¹ * w)
  rw [Hom.zero_pointMap, eq_comm, L'.weierstrassPoint_eq_zero_iff, ← mul_assoc, mul_inv_cancel₀ hα, one_mul] at this
  exact hw this

/-- **Normalization of a lift** (Milne, Section 12, pdf p. 126, with Proposition 3.3): a morphism
`f : E(Λ) → E(Λ')` with `f(P(z)) = P'(αz)` for all `z` pulls the invariant differential of `E(Λ')` back to `α` times
that of `E(Λ)`: on tangent spaces at `0`, `f` is multiplication by `α`. -/
@[kb "milne2017mf" "Section 12, normalized action on the tangent space (pdf p. 126)"]
theorem pullbackDifferential_eq_smul_of_lift (f : Hom L.weierstrassCurve.toAffine L'.weierstrassCurve.toAffine)
    {α : ℂ} (hf : ∀ z, f.pointMap (L.weierstrassPoint z) = L'.weierstrassPoint (α * z)) :
    f.pullbackDifferential (invariantDifferential L'.weierstrassCurve.toAffine) =
      α • invariantDifferential L.weierstrassCurve.toAffine := by
  classical
  obtain ⟨c, hc, -⟩ := Hom.existsUnique_pullbackDifferential_invariantDifferential_eq_smul f
  suffices hcα : c = α by rw [hc, hcα]
  rcases Hom.eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · rw [eq_zero_of_zero_lift hf]
    rw [Hom.pullbackDifferential_zero, LinearMap.zero_apply, eq_comm] at hc
    exact (smul_eq_zero.1 hc).resolve_right (invariantDifferential_ne_zero _)
  rw [Hom.pullbackDifferential_ofIsogeny] at hc
  obtain ⟨s, hs⟩ := exists_fieldPullback_genericY_eq φ L.weierstrassCurve_a₁ L.weierstrassCurve_a₃
    L'.weierstrassCurve_a₁ L'.weierstrassCurve_a₃
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero] at hs
    exact genericY_ne_zero_of_a₁_a₃ L'.weierstrassCurve_a₁ L'.weierstrassCurve_a₃
      ((map_eq_zero_iff _ φ.fieldPullback.toRingHom.injective).1 hs)
  have hsn : s.num ≠ 0 := by rwa [Ne, RatFunc.num_eq_zero_iff]
  have hpoly := polynomial_identity_of_pullback φ hs0 hs hc
  set r := φ.xRatFunc
  set B : ℂ[X] := r.denom * s.denom * s.num * cubicPoly L
  have hB : B ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero r.denom_ne_zero s.denom_ne_zero) hsn)
    (cubicPoly_ne_zero L)
  obtain ⟨x₀, hx₀⟩ := Infinite.exists_notMem_finset B.roots.toFinset
  have hBx : B.eval x₀ ≠ 0 := fun h ↦ hx₀ (Multiset.mem_toFinset.2 ((mem_roots hB).2 h))
  simp only [B, eval_mul, mul_ne_zero_iff] at hBx
  obtain ⟨⟨⟨hrd, hsd⟩, hsnx⟩, hcub⟩ := hBx
  obtain ⟨z₀, hz₀, hxz₀⟩ := L.exists_weierstrassP_eq x₀
  set R : ℂ → ℂ := fun t ↦ r.num.eval t / r.denom.eval t
  set S : ℂ → ℂ := fun t ↦ s.num.eval t / s.denom.eval t
  -- the action of `φ` on points, by the rational functions, compared with `z ↦ αz`
  have hformula : ∀ z, z ∉ L.lattice → r.denom.eval (℘[L] z) ≠ 0 → s.denom.eval (℘[L] z) ≠ 0 →
      α * z ∉ L'.lattice ∧ ℘[L'] (α * z) = R (℘[L] z) ∧ ℘'[L'] (α * z) / 2 = ℘'[L] z / 2 * S (℘[L] z) := by
    intro z hz hr' hs'
    have h1 := hf z
    rw [L.weierstrassPoint_of_notMem hz] at h1
    obtain ⟨h', hP⟩ := pointMap_ofIsogeny_some_eq φ hs _ hr' hs'
    rw [hP] at h1
    have hαz : α * z ∉ L'.lattice := fun h ↦ by
      rw [L'.weierstrassPoint_of_mem h] at h1
      exact Point.some_ne_zero _ h1
    rw [L'.weierstrassPoint_of_notMem hαz, Point.some.injEq] at h1
    exact ⟨hαz, h1.1.symm, h1.2.symm⟩
  obtain ⟨hαz₀, -, hy₀⟩ := hformula z₀ hz₀ (by rwa [hxz₀]) (by rwa [hxz₀])
  -- derivatives at `z₀`
  have hwpz : HasDerivAt ℘[L] (℘'[L] z₀) z₀ := by
    have := (L.analyticOnNhd_weierstrassP z₀ hz₀).differentiableAt.hasDerivAt
    rwa [L.deriv_weierstrassP] at this
  have hwpz' : HasDerivAt ℘[L'] (℘'[L'] (α * z₀)) (α * z₀) := by
    have := (L'.analyticOnNhd_weierstrassP _ hαz₀).differentiableAt.hasDerivAt
    rwa [L'.deriv_weierstrassP] at this
  have hd1 : HasDerivAt (fun z ↦ ℘[L'] (α * z)) (℘'[L'] (α * z₀) * (α * 1)) z₀ :=
    hwpz'.comp z₀ ((hasDerivAt_id z₀).const_mul α)
  have hrd' : r.denom.eval (℘[L] z₀) ≠ 0 := by rwa [hxz₀]
  have hd2 : HasDerivAt (fun z ↦ R (℘[L] z))
      (((derivative r.num).eval (℘[L] z₀) * r.denom.eval (℘[L] z₀) -
        r.num.eval (℘[L] z₀) * (derivative r.denom).eval (℘[L] z₀)) / r.denom.eval (℘[L] z₀) ^ 2 *
        ℘'[L] z₀) z₀ :=
    ((r.num.hasDerivAt _).div (r.denom.hasDerivAt _) hrd').comp z₀ hwpz
  have hev : (fun z ↦ R (℘[L] z)) =ᶠ[𝓝 z₀] fun z ↦ ℘[L'] (α * z) := by
    have e1 : ∀ᶠ z in 𝓝 z₀, z ∉ L.lattice := L.isClosed_lattice.isOpen_compl.mem_nhds hz₀
    have e2 : ∀ᶠ z in 𝓝 z₀, r.denom.eval (℘[L] z) ≠ 0 :=
      ((r.denom.continuous.continuousAt).comp hwpz.continuousAt).eventually_ne hrd'
    have e3 : ∀ᶠ z in 𝓝 z₀, s.denom.eval (℘[L] z) ≠ 0 :=
      ((s.denom.continuous.continuousAt).comp hwpz.continuousAt).eventually_ne (by simpa [hxz₀] using hsd)
    filter_upwards [e1, e2, e3] with z h1 h2 h3
    exact (hformula z h1 h2 h3).2.1.symm
  have hderiv := (hd1.congr_of_eventuallyEq hev).unique hd2
  -- conclude
  have hp0 : ℘'[L] z₀ ≠ 0 := by
    intro h
    have := sq_eq_cubicPoly L (L.equation_weierstrassP hz₀)
    rw [h, hxz₀] at this
    exact hcub (by simpa using this.symm)
  have hpx := congrArg (eval x₀) hpoly
  simp only [eval_mul, eval_sub, eval_pow, eval_C] at hpx
  rw [hxz₀] at hderiv hy₀
  have hy₀' : ℘'[L'] (α * z₀) = ℘'[L] z₀ * S x₀ := by linear_combination 2 * hy₀
  rw [hy₀'] at hderiv
  simp only [S] at hderiv
  field_simp at hderiv
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hp0 hsnx) (pow_ne_zero 2 hrd))
  linear_combination (-℘'[L] z₀) * hderiv - ℘'[L] z₀ * hpx

end ModularFormsKB.Milne.Wave8
