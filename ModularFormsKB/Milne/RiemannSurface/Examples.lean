import ModularFormsKB.Milne.RiemannSurface.Differential
import ModularFormsKB.Milne.RiemannSurface.Results
import TauCeti.Geometry.Manifold.Algebra.Quotient
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Milne, Chapter 1: the Riemann sphere and `ℂ/ℤ`

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §1, pdf pp. 15–22.

* Example 1.5: the unit sphere with the two stereographic projections is the Riemann sphere. **Erratum**: with the
  book's formula `(x + iy)/(1 + z)` for the projection from the south pole, the transition map is `w ↦ 1/w̄`, which is
  not holomorphic; the second chart must be `(x - iy)/(1 + z)` (`stereoSouth_book_eq`, `stereoSouth_mul_stereoNorth`).
  Recorded in `docs/updates-and-errata.md`.
* Example 1.10: `ℂ/ℤ` (Tau Ceti's complex Lie group structure on quotients by discrete submodules), its holomorphic
  functions, and the isomorphism `q = e^{2πiz} : ℂ/ℤ → ℂˣ` of Riemann surfaces and of groups.
* Example 1.11: the Riemann sphere `OnePoint ℂ` is `ℙ¹(ℂ)` (Mathlib's `OnePoint.equivProjectivization`), its two
  charts are `x₀/x₁` and `x₁/x₀`, with transition map `z ↦ 1/z`.
* Proposition 1.14: `M(S) = ℂ(z)` (Tau Ceti `TauCeti.RiemannSurface.MeromorphicFunction.ratFuncEquiv`, restated).
* Example 1.18: `M(S) = ℂ(f)` for `f` of valence one.
* Example 1.23: `ℓ(m P_∞) = m + 1`, `div(dz) = -2 P_∞`, `g = 0` (Exercise 1.24, the Riemann–Roch theorem for the
  sphere, is in `Wave4A/SphereRiemannRoch.lean`).
-/

open Filter Topology Set Complex
open scoped Manifold Real

namespace ModularFormsKB.Milne

open TauCeti.RiemannSurface TauCeti.AlgebraicGeometry MeromorphicFunction RiemannSurface

/-! ### Example 1.5: stereographic projection -/

section Stereographic

/-- The unit sphere `x² + y² + z² = 1` in `ℝ³`. -/
abbrev UnitSphere : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The north pole `(0, 0, 1)`. -/
noncomputable def northPole : UnitSphere := ⟨EuclideanSpace.single 2 1, by simp⟩

/-- The south pole `(0, 0, -1)`. -/
noncomputable def southPole : UnitSphere := ⟨EuclideanSpace.single 2 (-1), by simp⟩

/-- Stereographic projection from the north pole (Milne, Example 1.5): `(x, y, z) ↦ (x + iy)/(1 - z)`. -/
@[kb "milne2017mf" "Example 1.5: stereographic projection from the north pole, pdf p. 16"]
noncomputable def stereoNorth (p : UnitSphere) : ℂ :=
  ((p.1 0 : ℂ) + (p.1 1 : ℂ) * I) / (1 - (p.1 2 : ℂ))

/-- Stereographic projection from the south pole, oriented so that the transition map is holomorphic:
`(x, y, z) ↦ (x - iy)/(1 + z)`. -/
@[kb "milne2017mf" "Example 1.5: stereographic projection from the south pole (corrected), pdf p. 16"]
noncomputable def stereoSouth (p : UnitSphere) : ℂ :=
  ((p.1 0 : ℂ) - (p.1 1 : ℂ) * I) / (1 + (p.1 2 : ℂ))

/-- The projection from the south pole as the book's formula reads, `(x, y, z) ↦ (x + iy)/(1 + z)`. -/
noncomputable def stereoSouthBook (p : UnitSphere) : ℂ :=
  ((p.1 0 : ℂ) + (p.1 1 : ℂ) * I) / (1 + (p.1 2 : ℂ))

theorem UnitSphere.sum_sq (p : UnitSphere) : p.1 0 ^ 2 + p.1 1 ^ 2 + p.1 2 ^ 2 = 1 := by
  have h := p.2
  rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_three] at h
  simpa using h

theorem UnitSphere.eq_northPole_iff (p : UnitSphere) : p = northPole ↔ p.1 2 = 1 := by
  constructor
  · rintro rfl; simp [northPole]
  · intro h
    have := p.sum_sq
    have h0 : p.1 0 = 0 := by rw [h] at this; nlinarith [sq_nonneg (p.1 0), sq_nonneg (p.1 1)]
    have h1 : p.1 1 = 0 := by rw [h] at this; nlinarith [sq_nonneg (p.1 0), sq_nonneg (p.1 1)]
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [northPole, h0, h1, h]

theorem UnitSphere.eq_southPole_iff (p : UnitSphere) : p = southPole ↔ p.1 2 = -1 := by
  constructor
  · rintro rfl; simp [southPole]
  · intro h
    have := p.sum_sq
    have h0 : p.1 0 = 0 := by rw [h] at this; nlinarith [sq_nonneg (p.1 0), sq_nonneg (p.1 1)]
    have h1 : p.1 1 = 0 := by rw [h] at this; nlinarith [sq_nonneg (p.1 0), sq_nonneg (p.1 1)]
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [southPole, h0, h1, h]

theorem UnitSphere.sum_sq_complex (p : UnitSphere) :
    (p.1 0 : ℂ) ^ 2 + (p.1 1 : ℂ) ^ 2 + (p.1 2 : ℂ) ^ 2 = 1 := by
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) p.sum_sq

theorem UnitSphere.one_sub_ne {p : UnitSphere} (hN : p ≠ northPole) : (1 - (p.1 2 : ℂ)) ≠ 0 := by
  intro h
  apply hN
  rw [UnitSphere.eq_northPole_iff]
  have : (p.1 2 : ℂ) = 1 := by linear_combination -h
  exact_mod_cast this

theorem UnitSphere.one_add_ne {p : UnitSphere} (hS : p ≠ southPole) : (1 + (p.1 2 : ℂ)) ≠ 0 := by
  intro h
  apply hS
  rw [UnitSphere.eq_southPole_iff]
  have : (p.1 2 : ℂ) = -1 := by linear_combination h
  exact_mod_cast this

/-- **Milne, Example 1.5** (the transition map): on the sphere minus the two poles, `σ_S = 1/σ_N`, so the transition
map `w ↦ 1/w` between the two charts is holomorphic. -/
@[kb "milne2017mf" "Example 1.5: the transition map between the stereographic charts, pdf p. 16"]
theorem stereoSouth_mul_stereoNorth {p : UnitSphere} (hN : p ≠ northPole) (hS : p ≠ southPole) :
    stereoSouth p * stereoNorth p = 1 := by
  have h1 := UnitSphere.one_sub_ne hN
  have h2 := UnitSphere.one_add_ne hS
  have hs := p.sum_sq_complex
  unfold stereoSouth stereoNorth
  field_simp
  linear_combination hs - (p.1 1 : ℂ) ^ 2 * Complex.I_sq

/-- **Erratum to Milne, Example 1.5**: with the book's formula for the projection from the south pole, the transition
map is `w ↦ 1/w̄`, antiholomorphic. -/
@[kb "milne2017mf" "Example 1.5: erratum, the book's south chart is antiholomorphic to the north chart, pdf p. 16"]
theorem stereoSouth_book_eq {p : UnitSphere} (hN : p ≠ northPole) (hS : p ≠ southPole) :
    stereoSouthBook p = (starRingEnd ℂ (stereoNorth p))⁻¹ := by
  have h1 := UnitSphere.one_sub_ne hN
  have h2 := UnitSphere.one_add_ne hS
  have hs := p.sum_sq_complex
  have hx : (p.1 0 : ℂ) - (p.1 1 : ℂ) * I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp at hre him
    have : p.1 2 = 1 ∨ p.1 2 = -1 := by
      have := p.sum_sq
      rw [hre, him] at this
      have : (p.1 2 - 1) * (p.1 2 + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    rcases this with h | h
    · exact hN ((UnitSphere.eq_northPole_iff p).2 h)
    · exact hS ((UnitSphere.eq_southPole_iff p).2 h)
  unfold stereoSouthBook stereoNorth
  simp only [map_div₀, map_add, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, map_one]
  field_simp
  have hx' : (p.1 0 : ℂ) + -((p.1 1 : ℂ) * I) ≠ 0 := by simpa [sub_eq_add_neg] using hx
  rw [eq_div_iff hx']
  linear_combination hs - (p.1 1 : ℂ) ^ 2 * Complex.I_sq

theorem normSq_add_one_pos (z : ℂ) : 0 < Complex.normSq z + 1 := by
  have := Complex.normSq_nonneg z
  linarith

/-- The inverse of the stereographic projection from the north pole, as a map `ℂ → ℝ³`. -/
noncomputable def stereoInvFun (z : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[2 * z.re / (Complex.normSq z + 1), 2 * z.im / (Complex.normSq z + 1),
    (Complex.normSq z - 1) / (Complex.normSq z + 1)]

theorem norm_stereoInvFun (z : ℂ) : ‖stereoInvFun z‖ = 1 := by
  have hs : 0 < Complex.normSq z + 1 := normSq_add_one_pos z
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_three]
  simp only [stereoInvFun, Real.norm_eq_abs, sq_abs]
  simp
  field_simp
  rw [Complex.normSq_apply]
  ring

/-- The inverse of the stereographic projection from the north pole on the Riemann sphere. -/
noncomputable def stereoInv (w : OnePoint ℂ) : UnitSphere :=
  w.elim northPole fun z => ⟨stereoInvFun z, by simpa using norm_stereoInvFun z⟩

/-- Auxiliary map used for continuity at infinity: `stereoInvFun z = stereoInvAux z⁻¹`. -/
noncomputable def stereoInvAux (w : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[2 * w.re / (Complex.normSq w + 1), -(2 * w.im) / (Complex.normSq w + 1),
    (1 - Complex.normSq w) / (Complex.normSq w + 1)]

theorem stereoInvFun_eq_aux {z : ℂ} (hz : z ≠ 0) : stereoInvFun z = stereoInvAux z⁻¹ := by
  have hn : 0 < Complex.normSq z := Complex.normSq_pos.2 hz
  have hs : 0 < Complex.normSq z + 1 := normSq_add_one_pos z
  have h1 : Complex.normSq z * Complex.normSq z⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hz, map_one]
  have hr : (z⁻¹).re = z.re / Complex.normSq z := by simp [Complex.inv_re]
  have hi : (z⁻¹).im = -z.im / Complex.normSq z := by simp [Complex.inv_im]
  have hq : Complex.normSq z⁻¹ = (Complex.normSq z)⁻¹ := map_inv₀ _ _
  ext i
  fin_cases i <;> simp [stereoInvFun, stereoInvAux, hr, hi, hq] <;> field_simp <;> ring

theorem continuous_stereoInvAux : Continuous stereoInvAux := by
  have hc : Continuous fun w : ℂ => Complex.normSq w + 1 := Complex.continuous_normSq.add continuous_const
  have hne : ∀ w : ℂ, Complex.normSq w + 1 ≠ 0 := fun w => (normSq_add_one_pos w).ne'
  unfold stereoInvAux
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i
  · exact (continuous_const.mul Complex.continuous_re).div hc hne
  · exact (continuous_const.mul Complex.continuous_im).neg.div hc hne
  · exact (continuous_const.sub Complex.continuous_normSq).div hc hne

theorem continuous_stereoInvFun : Continuous stereoInvFun := by
  have hc : Continuous fun w : ℂ => Complex.normSq w + 1 := Complex.continuous_normSq.add continuous_const
  have hne : ∀ w : ℂ, Complex.normSq w + 1 ≠ 0 := fun w => (normSq_add_one_pos w).ne'
  unfold stereoInvFun
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i
  · exact (continuous_const.mul Complex.continuous_re).div hc hne
  · exact (continuous_const.mul Complex.continuous_im).div hc hne
  · exact (Complex.continuous_normSq.sub continuous_const).div hc hne

theorem stereoNorth_stereoInv (z : ℂ) : stereoNorth (stereoInv z) = z := by
  have hs : 0 < Complex.normSq z + 1 := normSq_add_one_pos z
  have h2 : (Complex.normSq z : ℂ) + 1 ≠ 0 := by exact_mod_cast hs.ne'
  simp only [stereoNorth, stereoInv, OnePoint.elim_some, stereoInvFun]
  simp
  have h3 : (1 : ℂ) - ((Complex.normSq z : ℂ) - 1) / ((Complex.normSq z : ℂ) + 1) =
      2 / ((Complex.normSq z : ℂ) + 1) := by
    field_simp; ring
  rw [h3]
  conv_rhs => rw [← Complex.re_add_im z]
  field_simp

theorem stereoNorth_eq {p : UnitSphere} (hN : p ≠ northPole) :
    stereoNorth p = ((p.1 0 / (1 - p.1 2) : ℝ) : ℂ) + ((p.1 1 / (1 - p.1 2) : ℝ) : ℂ) * I := by
  have h : (1 - p.1 2) ≠ 0 := fun h => hN ((UnitSphere.eq_northPole_iff p).2 (by linarith))
  have h' : (1 - (p.1 2 : ℂ)) ≠ 0 := UnitSphere.one_sub_ne hN
  unfold stereoNorth
  push_cast
  field_simp

theorem stereoInv_stereoNorth {p : UnitSphere} (hN : p ≠ northPole) :
    stereoInv (stereoNorth p : ℂ) = p := by
  have h : (1 - p.1 2) ≠ 0 := fun h => hN ((UnitSphere.eq_northPole_iff p).2 (by linarith))
  have hs := p.sum_sq
  set x := p.1 0
  set y := p.1 1
  set c := p.1 2
  have hre : (stereoNorth p).re = x / (1 - c) := by
    rw [stereoNorth_eq hN]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  have him : (stereoNorth p).im = y / (1 - c) := by
    rw [stereoNorth_eq hN]
    simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  have hnorm : Complex.normSq (stereoNorth p) = (1 + c) / (1 - c) := by
    rw [Complex.normSq_apply, hre, him]
    field_simp
    nlinarith
  have hc1 : (1 + c) / (1 - c) + 1 = 2 / (1 - c) := by field_simp; ring
  apply Subtype.ext
  simp only [stereoInv, OnePoint.elim_some, stereoInvFun, hre, him, hnorm, hc1]
  ext i
  fin_cases i <;> simp <;> field_simp <;> ring

theorem stereoInv_injective : Function.Injective stereoInv := by
  have key : ∀ z : ℂ, stereoInv z ≠ northPole := by
    intro z h
    have := (UnitSphere.eq_northPole_iff _).1 h
    simp only [stereoInv, OnePoint.elim_some, stereoInvFun] at this
    have hs : 0 < Complex.normSq z + 1 := normSq_add_one_pos z
    simp at this
    rw [div_eq_one_iff_eq hs.ne'] at this
    linarith
  intro a b hab
  induction a using OnePoint.rec <;> induction b using OnePoint.rec
  · rfl
  · exact absurd hab.symm (key _)
  · exact absurd hab (key _)
  · congr 1
    have := congrArg stereoNorth hab
    rwa [stereoNorth_stereoInv, stereoNorth_stereoInv] at this

theorem stereoInv_surjective : Function.Surjective stereoInv := by
  intro p
  by_cases hN : p = northPole
  · exact ⟨OnePoint.infty, by simp [stereoInv, hN]⟩
  · exact ⟨((stereoNorth p : ℂ) : OnePoint ℂ), stereoInv_stereoNorth hN⟩

theorem continuous_stereoInv : Continuous stereoInv := by
  rw [OnePoint.continuous_iff]
  constructor
  · rw [tendsto_subtype_rng]
    have hn : stereoInv OnePoint.infty = northPole := rfl
    rw [hn, coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    have h0 : Tendsto (fun z : ℂ => stereoInvAux z⁻¹) (Bornology.cobounded ℂ)
        (𝓝 (stereoInvAux 0)) :=
      ((continuous_stereoInvAux.tendsto 0).comp tendsto_inv₀_cobounded)
    have h00 : stereoInvAux 0 = (northPole : UnitSphere).1 := by
      ext i; fin_cases i <;> simp [stereoInvAux, northPole]
    rw [h00] at h0
    refine h0.congr' ?_
    filter_upwards [Bornology.eventually_ne_cobounded (0 : ℂ)] with z hz
    simp [stereoInv, stereoInvFun_eq_aux hz]
  · exact continuous_induced_rng.2 continuous_stereoInvFun

/-- **Milne, Example 1.5.** The two stereographic projections define a complex structure on the unit sphere, and the
resulting Riemann surface is the Riemann sphere: there is a homeomorphism `Φ` of the unit sphere onto `OnePoint ℂ`
under which the two charts of `OnePoint ℂ` (Tau Ceti's `affineChart` and `invChart`) become the stereographic
projections from the north and the south pole. -/
@[kb "milne2017mf" "Example 1.5: the Riemann sphere, pdf p. 16"]
theorem exists_homeomorph_onePoint :
    ∃ Φ : UnitSphere ≃ₜ OnePoint ℂ, Φ northPole = OnePoint.infty ∧ Φ southPole = ((0 : ℂ) : OnePoint ℂ) ∧
      (∀ p, p ≠ northPole → chartAt ℂ ((0 : ℂ) : OnePoint ℂ) (Φ p) = stereoNorth p) ∧
      (∀ p, p ≠ southPole → chartAt ℂ (OnePoint.infty : OnePoint ℂ) (Φ p) = stereoSouth p) := by
  let E : OnePoint ℂ ≃ UnitSphere := Equiv.ofBijective stereoInv ⟨stereoInv_injective, stereoInv_surjective⟩
  let H : OnePoint ℂ ≃ₜ UnitSphere := Continuous.homeoOfEquivCompactToT2 (f := E) continuous_stereoInv
  have hH : ∀ w, H w = stereoInv w := fun w => rfl
  have key : ∀ p, p ≠ northPole → H.symm p = ((stereoNorth p : ℂ) : OnePoint ℂ) := by
    intro p hp
    apply H.injective
    rw [H.apply_symm_apply, hH, stereoInv_stereoNorth hp]
  have hnorth : H.symm northPole = OnePoint.infty := by
    apply H.injective
    rw [H.apply_symm_apply, hH]; rfl
  have hsouth : H.symm southPole = ((0 : ℂ) : OnePoint ℂ) := by
    apply H.injective
    rw [H.apply_symm_apply, hH]
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [stereoInv, stereoInvFun, southPole]
  refine ⟨H.symm, hnorth, hsouth, fun p hp => ?_, fun p hp => ?_⟩
  · rw [key p hp]; simp
  · by_cases hN : p = northPole
    · subst hN
      rw [hnorth]
      simp [stereoSouth, northPole]
    · rw [key p hN]
      simp only [OnePoint.chartAt_infty, OnePoint.invChart_coe]
      have := stereoSouth_mul_stereoNorth hN hp
      exact (eq_inv_of_mul_eq_one_left this).symm

end Stereographic

/-! ### Example 1.10: `ℂ/ℤ` -/

section Cylinder

/-- The subgroup `ℤ ⊆ ℂ`. -/
noncomputable abbrev intLattice : Submodule ℤ ℂ := Submodule.span ℤ {(1 : ℂ)}

theorem intLattice_eq : (intLattice : Set ℂ) = Set.range (Int.cast : ℤ → ℂ) := by
  ext z
  simp only [SetLike.mem_coe, intLattice, Submodule.mem_span_singleton, Set.mem_range]
  constructor
  · rintro ⟨n, rfl⟩; exact ⟨n, by simp⟩
  · rintro ⟨n, rfl⟩; exact ⟨n, by simp⟩

instance : DiscreteTopology intLattice := by
  have hemb : Topology.IsEmbedding (Int.cast : ℤ → ℂ) := by
    have := Complex.isometry_ofReal.isEmbedding.comp Int.isClosedEmbedding_coe_real.isEmbedding
    convert this using 1
    ext n; simp
  have h2 : DiscreteTopology (Set.range (Int.cast : ℤ → ℂ)) :=
    hemb.toHomeomorph.discreteTopology
  rw [← intLattice_eq] at h2
  exact h2

/-- `ℂ/ℤ`, with the complex structure for which the quotient map is a local isomorphism (Milne, Example 1.10;
Tau Ceti's quotient manifold structure). -/
@[kb "milne2017mf" "Example 1.10: the Riemann surface C/Z, pdf p. 17"]
abbrev Cylinder : Type := AddAction.orbitRel.Quotient intLattice ℂ

/-- The quotient map `p : ℂ → ℂ/ℤ`. -/
noncomputable def Cylinder.mk (z : ℂ) : Cylinder := Quotient.mk _ z

/-- `ℂˣ = ℂ ∖ {0}` as an open subset of `ℂ`. -/
def puncturedPlane : TopologicalSpace.Opens ℂ := ⟨{0}ᶜ, isOpen_compl_singleton⟩

theorem Cylinder.isLocalDiffeomorph_mk : IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) 1 Cylinder.mk :=
  TauCeti.isLocalDiffeomorph_addQuotientMk (G := intLattice) (M := ℂ) (I := 𝓘(ℂ)) (n := 1)

theorem Cylinder.mdifferentiable_mk : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Cylinder.mk :=
  Cylinder.isLocalDiffeomorph_mk.mdifferentiable one_ne_zero

theorem Cylinder.continuous_mk : Continuous Cylinder.mk :=
  Cylinder.mdifferentiable_mk.continuous

/-- **Milne, Example 1.10** (holomorphic functions on `ℂ/ℤ`): a function `f` on an open subset `U` of `ℂ/ℤ` is
holomorphic if and only if `f ∘ p` is holomorphic on `p⁻¹(U)`. -/
@[kb "milne2017mf" "Example 1.10: holomorphic functions on C/Z, pdf p. 17"]
theorem mdifferentiableOn_cylinder_iff (f : Cylinder → ℂ) (U : Set Cylinder) (hU : IsOpen U) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f U ↔ DifferentiableOn ℂ (f ∘ Cylinder.mk) (Cylinder.mk ⁻¹' U) := by
  rw [← mdifferentiableOn_iff_differentiableOn]
  constructor
  · intro h
    exact h.comp Cylinder.mdifferentiable_mk.mdifferentiableOn (fun _ hx => hx)
  · intro h x hx
    obtain ⟨z, rfl⟩ : ∃ z, Cylinder.mk z = x := Quotient.mk_surjective x
    have hloc := Cylinder.isLocalDiffeomorph_mk z
    have hopen : IsOpen (Cylinder.mk ⁻¹' U) := hU.preimage Cylinder.continuous_mk
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (f ∘ Cylinder.mk) z :=
      MDifferentiableWithinAt.mdifferentiableAt (h z hx) (hopen.mem_nhds hx)
    have hL : hloc.localInverse (Cylinder.mk z) = z :=
      hloc.localInverse_left_inv hloc.localInverse_mem_target
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) hloc.localInverse (Cylinder.mk z) :=
      hloc.mdifferentiableAt_localInverse one_ne_zero
    have h3 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ((f ∘ Cylinder.mk) ∘ hloc.localInverse) (Cylinder.mk z) := by
      refine MDifferentiableAt.comp (Cylinder.mk z) ?_ h2
      rw [hL]; exact h1
    refine (h3.congr_of_eventuallyEq ?_).mdifferentiableWithinAt
    filter_upwards [hloc.localInverse_eventuallyEq_right] with y hy
    simpa [Function.comp_def] using congrArg f hy.symm

theorem mem_intLattice_iff {z : ℂ} : z ∈ intLattice ↔ ∃ n : ℤ, z = n := by
  have : z ∈ (intLattice : Set ℂ) ↔ z ∈ Set.range (Int.cast : ℤ → ℂ) := by rw [intLattice_eq]
  simpa [eq_comm] using this

theorem exp_two_pi_I_eq_iff (z w : ℂ) :
    exp (2 * π * I * z) = exp (2 * π * I * w) ↔ z - w ∈ intLattice := by
  rw [Complex.exp_eq_exp_iff_exists_int, mem_intLattice_iff]
  have hne : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply mul_left_cancel₀ hne
    linear_combination hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have : z = w + n := by linear_combination hn
    rw [this]; ring

/-- `z ↦ e^{2πiz}` as a map to `ℂˣ`. -/
noncomputable def cylQ (z : ℂ) : puncturedPlane := ⟨exp (2 * π * I * z), Complex.exp_ne_zero _⟩

/-- `q : ℂ/ℤ → ℂˣ`. -/
noncomputable def cylE : Cylinder → puncturedPlane :=
  Quotient.lift cylQ fun a b h => by
    have : a - b ∈ intLattice := (Submodule.orbitRel_apply_iff_sub_mem _).1 h
    exact Subtype.ext ((exp_two_pi_I_eq_iff a b).2 this)

theorem cylE_bijective : Function.Bijective cylE := by
  have hne : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  constructor
  · intro x y h
    obtain ⟨a, rfl⟩ : ∃ a, Cylinder.mk a = x := Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ : ∃ b, Cylinder.mk b = y := Quotient.mk_surjective y
    have := (exp_two_pi_I_eq_iff a b).1 (congrArg Subtype.val h)
    exact Quotient.sound ((Submodule.orbitRel_apply_iff_sub_mem _).2 this)
  · intro w
    refine ⟨Cylinder.mk (Complex.log w / (2 * π * I)), Subtype.ext ?_⟩
    show exp (2 * π * I * (Complex.log w / (2 * π * I))) = w
    rw [mul_div_cancel₀ _ hne, Complex.exp_log w.2]

theorem mdifferentiable_cylE_val : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x => (cylE x : ℂ)) := by
  have := (mdifferentiableOn_cylinder_iff (fun x => (cylE x : ℂ)) Set.univ isOpen_univ).2 ?_
  · exact mdifferentiableOn_univ.1 this
  · rw [Set.preimage_univ]
    change DifferentiableOn ℂ (fun z : ℂ => exp (2 * π * I * z)) _
    exact differentiableOn_univ.2 (by fun_prop)

theorem mdifferentiable_cylE : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) cylE := fun x =>
  (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff cylE Set.univ x).1 (mdifferentiable_cylE_val x)

theorem exists_mul_mem_slitPlane {w : ℂ} (hw : w ≠ 0) : ∃ c : ℂ, c ≠ 0 ∧ c * w ∈ slitPlane := by
  by_cases h : w ∈ slitPlane
  · exact ⟨1, one_ne_zero, by simpa using h⟩
  · refine ⟨-1, by simp, ?_⟩
    rw [Complex.mem_slitPlane_iff] at h ⊢
    push Not at h
    obtain ⟨h1, h2⟩ := h
    left
    have : w.re ≠ 0 := by
      intro h0
      apply hw
      exact Complex.ext h0 h2
    simp only [neg_mul, one_mul, Complex.neg_re]
    exact neg_pos.2 (lt_of_le_of_ne h1 this)

theorem mdifferentiable_cylE_symm :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Equiv.ofBijective cylE cylE_bijective).symm := by
  intro w0
  obtain ⟨c, hc0, hc⟩ := exists_mul_mem_slitPlane w0.2
  set b : ℂ → ℂ := fun w => (Complex.log (c * w) - Complex.log c) / (2 * π * I) with hb
  have hne : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hV : IsOpen {w : puncturedPlane | c * (w : ℂ) ∈ slitPlane} :=
    Complex.isOpen_slitPlane.preimage (by fun_prop)
  have hbd : DifferentiableAt ℂ b (w0 : ℂ) := by
    refine DifferentiableAt.div_const (DifferentiableAt.sub ?_ (differentiableAt_const _)) _
    exact DifferentiableAt.clog (by fun_prop) hc
  have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun w : puncturedPlane => Cylinder.mk (b (w : ℂ))) w0 := by
    refine (Cylinder.mdifferentiable_mk (b w0)).comp w0 ?_
    exact hbd.mdifferentiableAt.comp w0
      ((contMDiff_subtype_val (I := 𝓘(ℂ)) (n := 1) (U := puncturedPlane)).mdifferentiable
        (by simp) w0)
  refine (h1.congr_of_eventuallyEq ?_).mdifferentiableWithinAt
  filter_upwards [hV.mem_nhds hc] with w hw
  rw [Equiv.symm_apply_eq]
  apply Subtype.ext
  show (w : ℂ) = exp (2 * π * I * b w)
  simp only [hb]
  rw [mul_div_cancel₀ _ hne, Complex.exp_sub, Complex.exp_log (slitPlane_ne_zero hw),
    Complex.exp_log hc0]
  field_simp

/-- **Milne, Example 1.10.** `q(z) = e^{2πiz}` defines an isomorphism `ℂ/ℤ → ℂˣ`, both of Riemann surfaces
(holomorphic with holomorphic inverse) and of topological groups (a homeomorphism carrying `+` to `·`). -/
@[kb "milne2017mf" "Example 1.10: q = exp(2 pi i z) gives C/Z = C^x, pdf p. 17"]
theorem exists_cylinder_equiv_puncturedPlane :
    ∃ e : Cylinder ≃ₜ puncturedPlane, (∀ z, (e (Cylinder.mk z) : ℂ) = exp (2 * π * I * z)) ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e.symm ∧
      ∀ x y, (e (x + y) : ℂ) = e x * e y := by
  let e : Cylinder ≃ₜ puncturedPlane :=
    { Equiv.ofBijective cylE cylE_bijective with
      continuous_toFun := mdifferentiable_cylE.continuous
      continuous_invFun := mdifferentiable_cylE_symm.continuous }
  refine ⟨e, fun z => rfl, mdifferentiable_cylE, mdifferentiable_cylE_symm, fun x y => ?_⟩
  obtain ⟨a, rfl⟩ : ∃ a, Cylinder.mk a = x := Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ : ∃ b, Cylinder.mk b = y := Quotient.mk_surjective y
  change (cylE (Quotient.mk _ a + Quotient.mk _ b) : ℂ) = (cylE (Quotient.mk _ a) : ℂ) * cylE (Quotient.mk _ b)
  rw [← Submodule.orbitRelQuotient_mk_add]
  change exp (2 * π * I * (a + b)) = exp (2 * π * I * a) * exp (2 * π * I * b)
  rw [mul_add, Complex.exp_add]

end Cylinder

/-! ### Example 1.11 and Proposition 1.14: the Riemann sphere -/

section Sphere

open scoped LinearAlgebra.Projectivization

open Classical in
/-- **Milne, Example 1.11.** The Riemann sphere is `ℙ¹(ℂ)` (Mathlib's `OnePoint.equivProjectivization`, `t ↦ (t : 1)`,
`∞ ↦ (1 : 0)`), and its two charts are `(x₀ : x₁) ↦ x₀/x₁` on `x₁ ≠ 0` and `(x₀ : x₁) ↦ x₁/x₀` on `x₀ ≠ 0`; the
transition map is `z ↦ 1/z` on `ℂ ∖ {0}`. (Mathlib numbers the coordinates so that `x₁ = 0` is `∞`; the book's
`U₀`, `z₀` are this `U₁`, `z₁` and vice versa.) -/
@[kb "milne2017mf" "Example 1.11, pdf p. 18"]
theorem chartAt_onePoint_projectivization (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    (v 1 ≠ 0 → chartAt ℂ ((0 : ℂ) : OnePoint ℂ) ((OnePoint.equivProjectivization ℂ).symm
        (Projectivization.mk ℂ v hv)) = v 0 / v 1) ∧
      (v 0 ≠ 0 → chartAt ℂ (OnePoint.infty : OnePoint ℂ) ((OnePoint.equivProjectivization ℂ).symm
        (Projectivization.mk ℂ v hv)) = v 1 / v 0) := by
  refine ⟨fun h1 => ?_, fun h0 => ?_⟩
  · simp [h1, div_eq_inv_mul]
  · by_cases h1 : v 1 = 0
    · simp [h1]
    · simp [h1, div_eq_inv_mul, mul_comm]

/-- **Milne, Example 1.11** (the transition map): `z₁ = z₀⁻¹` on the overlap of the two charts. -/
@[kb "milne2017mf" "Example 1.11: the transition map z -> 1/z, pdf p. 18"]
theorem chartAt_infty_symm_chartAt_zero {z : ℂ} (hz : z ≠ 0) :
    chartAt ℂ (OnePoint.infty : OnePoint ℂ) ((chartAt ℂ ((0 : ℂ) : OnePoint ℂ)).symm z) = z⁻¹ := by
  simp

/-- **Milne, Proposition 1.14.** The field of meromorphic functions on the Riemann sphere is `ℂ(z)`: there is a
`ℂ`-algebra isomorphism `ℂ(X) ≃ M(S)` sending `X` to the coordinate `z`. Tau Ceti:
`TauCeti.RiemannSurface.MeromorphicFunction.ratFuncEquiv`. -/
@[kb "milne2017mf" "Proposition 1.14, pdf p. 19"]
theorem exists_ratFunc_algEquiv :
    ∃ e : RatFunc ℂ ≃ₐ[ℂ] MeromorphicFunction (OnePoint ℂ), e RatFunc.X = coordinate :=
  ⟨ratFuncEquiv, ratFuncEquiv_X⟩

/-- **Milne, Example 1.18.** For a meromorphic function `f` of valence one on the Riemann sphere, `M(S) = ℂ(f)`. -/
@[kb "milne2017mf" "Example 1.18, pdf p. 20"]
theorem adjoin_eq_top_of_valence_eq_one {f : MeromorphicFunction (OnePoint ℂ)} (hf : valence f = 1) :
    IntermediateField.adjoin ℂ {f} = ⊤ := by
  have hnc : IsNonconstant f := by
    by_contra h
    simp [valence, h] at hf
  set β := toFiniteHolomorphicMap f hnc
  set φ := comapₐ β β.holomorphic β.nonconstant with hφ
  have hφX : φ coordinate = f := by
    rw [hφ, comapₐ_apply]
    exact MeromorphicFunction.ext fun x => by simp [comap_apply, β, toFiniteHolomorphicMap]; rfl
  set ψ : RatFunc ℂ →ₐ[ℂ] MeromorphicFunction (OnePoint ℂ) := φ.comp ratFuncEquiv.toAlgHom with hψ
  have hψX : ψ RatFunc.X = f := by simp [hψ, hφX]
  have hψp : ∀ p : Polynomial ℂ, ψ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) = Polynomial.aeval f p := by
    intro p
    have : ψ.comp (IsScalarTower.toAlgHom ℂ (Polynomial ℂ) (RatFunc ℂ)) = Polynomial.aeval f := by
      apply Polynomial.algHom_ext
      simpa using hψX
    simpa using congrArg (fun h => h p) this
  have hmem : ∀ r : RatFunc ℂ, ψ r ∈ IntermediateField.adjoin ℂ {f} := by
    intro r
    have hr := RatFunc.num_div_denom r
    rw [← hr, map_div₀, hψp, hψp]
    refine div_mem ?_ ?_
    · exact IntermediateField.algebra_adjoin_le_adjoin ℂ {f} (Polynomial.aeval_mem_adjoin_singleton ℂ f)
    · exact IntermediateField.algebra_adjoin_le_adjoin ℂ {f} (Polynomial.aeval_mem_adjoin_singleton ℂ f)
  rw [eq_top_iff]
  intro g _
  obtain ⟨p, hpm, hpd, hpg⟩ := exists_monic_natDegree_le_valence hnc g
  have hpd' : p.natDegree ≤ 1 := hpd.trans hf.le
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hpd' with h0 | h1
  · rw [Polynomial.Monic.natDegree_eq_zero hpm] at h0
    rw [h0, Polynomial.eval₂_one] at hpg
    exact absurd hpg one_ne_zero
  · rw [hpm.eq_X_add_C h1] at hpg
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C] at hpg
    obtain ⟨r, hr⟩ := ratFuncEquiv.surjective (-(p.coeff 0))
    have : g = ψ r := by
      have h2 : g = -(φ (p.coeff 0)) := eq_neg_of_add_eq_zero_left hpg
      rw [h2, hψ]
      simp [hr]
    rw [this]
    exact hmem r

/-- The point at infinity as a divisor `P_∞`. -/
noncomputable def divisorInfty : WeilDivisor (OnePoint ℂ) := Finsupp.single OnePoint.infty 1

open Classical in
theorem divisorInfty_nsmul_apply (m : ℕ) (x : OnePoint ℂ) :
    (m • divisorInfty) x = if x = OnePoint.infty then (m : ℤ) else 0 := by
  by_cases h : x = OnePoint.infty
  · subst h; simp [divisorInfty]
  · simp [divisorInfty, Finsupp.single_apply, Ne.symm h, h]

theorem mem_rrSpace_nsmul_iff (m : ℕ) (f : MeromorphicFunction (OnePoint ℂ)) :
    f ∈ rrSpace (OnePoint ℂ) (m • divisorInfty) ↔
      (∀ z : ℂ, f z ≠ OnePoint.infty) ∧ (((-(m : ℤ) : ℤ)) : WithTop ℤ) ≤ order OnePoint.infty f := by
  constructor
  · intro h
    refine ⟨fun z => ?_, ?_⟩
    · have := h z
      rw [divisorInfty_nsmul_apply, if_neg (OnePoint.coe_ne_infty z)] at this
      rw [← order_nonneg_iff]; simpa using this
    · have := h OnePoint.infty
      rwa [divisorInfty_nsmul_apply, if_pos rfl] at this
  · rintro ⟨h1, h2⟩ x
    induction x using OnePoint.rec with
    | infty => rw [divisorInfty_nsmul_apply, if_pos rfl]; exact h2
    | coe z =>
      rw [divisorInfty_nsmul_apply, if_neg (OnePoint.coe_ne_infty z)]
      simpa using (order_nonneg_iff.2 (h1 z))

theorem coordinate_pow_mem (m i : ℕ) (hi : i ≤ m) :
    (coordinate : MeromorphicFunction (OnePoint ℂ)) ^ i ∈ rrSpace (OnePoint ℂ) (m • divisorInfty) := by
  rw [mem_rrSpace_nsmul_iff]
  refine ⟨fun z => ?_, ?_⟩
  · rw [← order_nonneg_iff, (order (z : OnePoint ℂ)).map_pow]
    have : (0 : WithTop ℤ) ≤ order (z : OnePoint ℂ) coordinate := by
      rw [order_nonneg_iff, coordinate_apply]; exact OnePoint.coe_ne_infty z
    exact nsmul_nonneg this i
  · rw [(order OnePoint.infty).map_pow, order_coordinate_infty]
    have : i • (-1 : WithTop ℤ) = (((-(i : ℤ)) : ℤ) : WithTop ℤ) := by
      rw [show (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) from rfl, ← WithTop.coe_nsmul]
      congr 1
      simp
    rw [this]
    exact_mod_cast (by omega : -(m : ℤ) ≤ -(i : ℤ))

theorem aeval_coordinate_injective' :
    Function.Injective (Polynomial.aeval (R := ℂ) (coordinate : MeromorphicFunction (OnePoint ℂ))) := by
  refine (injective_iff_map_eq_zero _).2 fun p hp => Polynomial.funext fun z => ?_
  have h := aeval_coordinate_apply_coe p z
  rw [hp, coe_zero] at h
  simpa using (OnePoint.coe_injective h).symm


theorem map_aeval_le_rrSpace (m : ℕ) :
    Submodule.map (Polynomial.aeval (R := ℂ) (coordinate : MeromorphicFunction (OnePoint ℂ))).toLinearMap
      (Polynomial.degreeLT ℂ (m + 1)) ≤ rrSpace (OnePoint ℂ) (m • divisorInfty) := by
  rintro _ ⟨p, hp, rfl⟩
  have hlt : p.natDegree < m + 1 := by
    by_cases h0 : p = 0
    · simp [h0]
    · have := Polynomial.mem_degreeLT.1 hp
      exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 this
  have hsum := Polynomial.as_sum_range' p (m + 1) hlt
  show Polynomial.aeval coordinate p ∈ _
  rw [hsum, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Polynomial.aeval_monomial]
  have := Submodule.smul_mem (rrSpace (OnePoint ℂ) (m • divisorInfty)) (p.coeff i)
    (coordinate_pow_mem m i (by omega))
  simpa [Algebra.smul_def] using this

theorem rrSpace_le_map_aeval (m : ℕ) :
    rrSpace (OnePoint ℂ) (m • divisorInfty) ≤
    Submodule.map (Polynomial.aeval (R := ℂ) (coordinate : MeromorphicFunction (OnePoint ℂ))).toLinearMap
      (Polynomial.degreeLT ℂ (m + 1)) := by
  induction m with
  | zero =>
    intro f hf
    rw [mem_rrSpace_nsmul_iff] at hf
    have hinf : ∀ x, f x ≠ OnePoint.infty := by
      intro x
      induction x using OnePoint.rec with
      | infty =>
        rw [← order_nonneg_iff]
        simpa using hf.2
      | coe z => exact hf.1 z
    obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_forall_ne_infty hinf
    refine ⟨Polynomial.C c, Polynomial.mem_degreeLT.2 ?_, ?_⟩
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
    · simp [← hc]
  | succ m ih =>
    intro f hf
    have hf' := (mem_rrSpace_nsmul_iff _ _).1 hf
    have hZ0 : (coordinate : MeromorphicFunction (OnePoint ℂ)) ≠ 0 := by
      intro h
      have := congrArg (fun g : MeromorphicFunction (OnePoint ℂ) => g OnePoint.infty) h
      simp at this
    have hZn : (coordinate : MeromorphicFunction (OnePoint ℂ)) ^ (m + 1) ≠ 0 := pow_ne_zero _ hZ0
    set Z : MeromorphicFunction (OnePoint ℂ) := coordinate with hZ
    set g := f * (Z ^ (m + 1))⁻¹ with hg
    have hgZ : g * Z ^ (m + 1) = f := by rw [hg, mul_assoc, inv_mul_cancel₀ hZn, mul_one]
    have hordZ : order OnePoint.infty (Z ^ (m + 1)) = (((-((m + 1 : ℕ) : ℤ)) : ℤ) : WithTop ℤ) := by
      rw [(order OnePoint.infty).map_pow, hZ, order_coordinate_infty,
        show (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) from rfl, ← WithTop.coe_nsmul]
      congr 1
      simp
    have hordg : order OnePoint.infty f = order OnePoint.infty g + (((-((m + 1 : ℕ) : ℤ)) : ℤ) : WithTop ℤ) := by
      rw [← hordZ, ← (order OnePoint.infty).map_mul, hgZ]
    have hg0 : 0 ≤ order OnePoint.infty g := by
      have h2 := hf'.2
      rw [hordg] at h2
      generalize order OnePoint.infty g = a at h2 ⊢
      induction a using WithTop.recTopCoe with
      | top => simp
      | coe k =>
        have : -((m + 1 : ℕ) : ℤ) ≤ k + (-((m + 1 : ℕ) : ℤ)) := by exact_mod_cast h2
        have : (0 : ℤ) ≤ k := by omega
        exact_mod_cast this
    obtain ⟨c, hc⟩ := OnePoint.ne_infty_iff_exists.1 (order_nonneg_iff.1 hg0)
    have hgc : 0 < order OnePoint.infty (g - algebraMap ℂ _ c) := by
      rw [order_pos_iff]
      have := sub_apply_of_eq_coe (f := g) (g := algebraMap ℂ (MeromorphicFunction (OnePoint ℂ)) c)
        (x := OnePoint.infty) hc.symm (congrFun (coe_algebraMap c) _)
      rw [this, sub_self]
    set f' := f - algebraMap ℂ _ c * Z ^ (m + 1) with hf'def
    have hf'eq : f' = Z ^ (m + 1) * (g - algebraMap ℂ _ c) := by
      rw [hf'def, mul_sub, mul_comm (Z ^ (m + 1)) g, hgZ, mul_comm]
    have hmono : algebraMap ℂ (MeromorphicFunction (OnePoint ℂ)) c * Z ^ (m + 1) ∈
        rrSpace (OnePoint ℂ) ((m + 1) • divisorInfty) := by
      have := Submodule.smul_mem (rrSpace (OnePoint ℂ) ((m + 1) • divisorInfty)) c
        (coordinate_pow_mem (m + 1) (m + 1) le_rfl)
      simpa [Algebra.smul_def] using this
    have hf'mem : f' ∈ rrSpace (OnePoint ℂ) (m • divisorInfty) := by
      have h1 : f' ∈ rrSpace (OnePoint ℂ) ((m + 1) • divisorInfty) := Submodule.sub_mem _ hf hmono
      rw [mem_rrSpace_nsmul_iff] at h1 ⊢
      refine ⟨h1.1, ?_⟩
      rw [hf'eq, (order OnePoint.infty).map_mul, hordZ]
      generalize order OnePoint.infty (g - algebraMap ℂ _ c) = a at hgc ⊢
      induction a using WithTop.recTopCoe with
      | top => simp
      | coe k =>
        have : (0 : ℤ) < k := by exact_mod_cast hgc
        have : (((-(m : ℤ)) : ℤ) : WithTop ℤ) ≤ ((-((m + 1 : ℕ) : ℤ) + k : ℤ) : WithTop ℤ) := by
          exact_mod_cast (by push_cast; omega)
        exact_mod_cast this
    obtain ⟨p', hp', hp'eq⟩ := ih hf'mem
    refine ⟨p' + Polynomial.C c * Polynomial.X ^ (m + 1), ?_, ?_⟩
    · refine Submodule.add_mem _ (Polynomial.degreeLT_mono (by omega) hp') ?_
      rw [Polynomial.mem_degreeLT]
      exact (Polynomial.degree_C_mul_X_pow_le (m + 1) c).trans_lt (by exact_mod_cast Nat.lt_succ_self _)
    · have : f = f' + algebraMap ℂ _ c * Z ^ (m + 1) := by rw [hf'def]; ring
      rw [this, ← hp'eq]
      simp [hZ, Algebra.algebraMap_eq_smul_one]



theorem degree_divisorInfty : WeilDivisor.degree divisorInfty = 1 := by
  simp [WeilDivisor.degree, divisorInfty, Finsupp.degree_single]

/-- **Milne, Example 1.23** (first part): `ℓ(m P_∞) = m + 1` for `m ≥ 0` (the polynomials of degree `≤ m`). -/
@[kb "milne2017mf" "Example 1.23: l(m P_infty) = m + 1, pdf p. 22"]
theorem ell_nsmul_divisorInfty (m : ℕ) : ell (OnePoint ℂ) (m • divisorInfty) = m + 1 := by
  have h : rrSpace (OnePoint ℂ) (m • divisorInfty) =
      Submodule.map (Polynomial.aeval (R := ℂ) (coordinate : MeromorphicFunction (OnePoint ℂ))).toLinearMap
        (Polynomial.degreeLT ℂ (m + 1)) :=
    le_antisymm (rrSpace_le_map_aeval m) (map_aeval_le_rrSpace m)
  unfold ell
  rw [h]
  rw [← (Submodule.equivMapOfInjective _ aeval_coordinate_injective' _).finrank_eq]
  rw [(Polynomial.degreeLTEquiv ℂ (m + 1)).finrank_eq]
  simp


theorem ord_differential_coordinate_coe (z : ℂ) :
    (differential (coordinate : MeromorphicFunction (OnePoint ℂ))).ord (z : OnePoint ℂ) = 0 := by
  classical
  have h : (differential (coordinate : MeromorphicFunction (OnePoint ℂ))).coeff (z : OnePoint ℂ) =
      fun _ => 1 := by
    show deriv (coordinate.finitePart ∘ (chartAt ℂ (z : OnePoint ℂ)).symm) = _
    have : (coordinate.finitePart ∘ (chartAt ℂ (z : OnePoint ℂ)).symm) = id := by
      funext v
      simp only [OnePoint.chartAt_coe, OnePoint.affineChart_symm_apply, Function.comp_apply, id_eq]
      exact finitePart_of_eq_coe (coordinate_apply _)
    rw [this]
    funext v
    simp
  unfold MeromorphicDifferential.ord
  rw [h, _root_.meromorphicOrderAt_const]
  simp

theorem ord_differential_coordinate_infty :
    (differential (coordinate : MeromorphicFunction (OnePoint ℂ))).ord OnePoint.infty = -2 := by
  have h : (differential (coordinate : MeromorphicFunction (OnePoint ℂ))).coeff OnePoint.infty =
      fun u => -(u ^ 2)⁻¹ := by
    show deriv (coordinate.finitePart ∘ (chartAt ℂ OnePoint.infty).symm) = _
    have : (coordinate.finitePart ∘ (chartAt ℂ (OnePoint.infty : OnePoint ℂ)).symm) =
        fun u : ℂ => u⁻¹ := by
      funext u
      simp only [OnePoint.chartAt_infty, Function.comp_apply]
      by_cases hu : u = 0
      · subst hu
        simp only [OnePoint.invChart_symm_zero, inv_zero]
        exact finitePart_of_eq_infty (coordinate_apply _)
      · rw [OnePoint.invChart_symm_of_ne_zero hu]
        exact finitePart_of_eq_coe (coordinate_apply _)
    rw [this, deriv_inv']
  unfold MeromorphicDifferential.ord
  rw [h]
  simp only [OnePoint.chartAt_infty, OnePoint.invChart_infty]
  have hm : _root_.MeromorphicAt (fun u : ℂ => -(u ^ 2)⁻¹) 0 := by
    have : _root_.MeromorphicAt (fun u : ℂ => u) 0 := _root_.MeromorphicAt.id 0
    exact ((this.pow 2).inv).neg
  rw [show (-2 : WithTop ℤ) = ((-2 : ℤ) : WithTop ℤ) from rfl, _root_.meromorphicOrderAt_eq_int_iff hm]
  refine ⟨fun _ => -1, analyticAt_const, by norm_num, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with u hu
  simp [zpow_neg]


/-- **Milne, Example 1.23** (second part): `dz` has a pole of order 2 at `∞` and no other zeros or poles:
`div(dz) = -2 P_∞`. -/
@[kb "milne2017mf" "Example 1.23: div(dz) = -2 P_infty, pdf p. 22"]
theorem divisor_differential_coordinate :
    (differential (coordinate : MeromorphicFunction (OnePoint ℂ))).divisor = -2 • divisorInfty := by
  classical
  set ω := differential (coordinate : MeromorphicFunction (OnePoint ℂ)) with hω
  have hord : ∀ x, ω.ordZ x = if x = OnePoint.infty then -2 else 0 := by
    intro x
    induction x using OnePoint.rec with
    | infty =>
      rw [if_pos rfl]
      unfold MeromorphicDifferential.ordZ
      rw [hω, ord_differential_coordinate_infty]
      rfl
    | coe z =>
      rw [if_neg (OnePoint.coe_ne_infty z)]
      unfold MeromorphicDifferential.ordZ
      rw [hω, ord_differential_coordinate_coe]
      rfl
  have hfin : (Function.support ω.ordZ).Finite := by
    refine (Set.finite_singleton OnePoint.infty).subset fun x hx => ?_
    by_contra h
    have h' : x ≠ OnePoint.infty := h
    exact hx (by rw [hord, if_neg h'])
  unfold MeromorphicDifferential.divisor
  rw [dif_pos hfin]
  refine Finsupp.ext fun x => ?_
  rw [Finsupp.ofSupportFinite_coe, hord]
  by_cases hx : x = OnePoint.infty
  · subst hx; simp [divisorInfty]
  · simp [divisorInfty, Finsupp.single_apply, Ne.symm hx, hx]


/-- **Milne, Example 1.23** (conclusion): the Riemann–Roch theorem forces `g = 0` on the sphere: any `g` satisfying
the Riemann–Roch formula is `0`. -/
@[kb "milne2017mf" "Example 1.23: the Riemann sphere has genus 0, pdf p. 22"]
theorem genus_eq_zero_of_riemannRoch {g : ℕ}
    (hg : ∀ ω : MeromorphicDifferential (OnePoint ℂ), ¬ ω.IsZero → ∀ D : WeilDivisor (OnePoint ℂ),
      (ell (OnePoint ℂ) D : ℤ) = WeilDivisor.degree D + 1 - g + ell (OnePoint ℂ) (ω.divisor - D)) :
    g = 0 := by
  have hω : ¬ (differential (coordinate : MeromorphicFunction (OnePoint ℂ))).IsZero := by
    intro h
    have := h ((0 : ℂ) : OnePoint ℂ)
    rw [ord_differential_coordinate_coe] at this
    exact absurd this (by simp)
  have h2 := (degree_canonical_and_ell_canonical hg hω).1
  rw [divisor_differential_coordinate, map_zsmul, degree_divisorInfty] at h2
  simp only [smul_eq_mul] at h2
  omega

-- Exercise 1.24 (the Riemann–Roch theorem for the sphere) is `ModularFormsKB.Milne.riemannRoch_sphere` in
-- `ModularFormsKB/Milne/Wave4A/SphereRiemannRoch.lean`.

end Sphere

end ModularFormsKB.Milne
