import TauCeti.Analysis.Contour.Residue.Theorem
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Analysis.Analytic.Polynomial

/-!
# The residue theorem for rational functions on the Riemann sphere

This file supports the residue theorem on the Riemann sphere (Milne, *Modular Functions and Modular
Forms*, Proposition 1.12 (b)): for a rational function `r ∈ ℂ(X)`, the sum of the residues of
`r(z) dz` over all points of `ℂ ∪ {∞}` vanishes.

Residues at finite points are Tau Ceti's `TauCeti.Contour.residue`. The residue at `∞` is the residue
at `0` of the pullback of `r(z) dz` under `u = 1/z`, namely `r(1/u) · (-u⁻²) du`.

## Proof strategy

Contour integrals. For a radius `R` larger than the moduli of all poles,
`classicalResidueTheorem_circle` expresses `∮_{C(0,R)} r` through the finite residues. The
substitution `u = 1/w` identifies `∮_{C(0,R)} F(w) dw` with `-∮_{C(0,1/R)} F(1/u)(-u⁻²) du`
(`circleIntegral_inv_comp`), and the latter is computed by the residue theorem again, the only
possible pole inside `C(0,1/R)` being `0`.

## Main results

* `ModularFormsKB.Milne.RS.meromorphicAt_ratEval`
* `ModularFormsKB.Milne.RS.residue_ratEval_eq_zero`
* `ModularFormsKB.Milne.RS.sum_residue_ratEval_add_residue_infty_of_subset`: for any finite set `S`
  containing the zeros of the denominator.
* `ModularFormsKB.Milne.RS.sum_residue_ratEval_add_residue_infty`: the case `S` = the roots.
-/

open Filter Topology Complex Metric
open scoped Real

namespace ModularFormsKB.Milne.RS

/-- The rational function `r` as a function on `ℂ` (junk at the poles). -/
noncomputable def ratEval (r : RatFunc ℂ) (z : ℂ) : ℂ := r.eval (RingHom.id ℂ) z

theorem ratEval_eq (r : RatFunc ℂ) :
    ratEval r = fun z ↦ r.num.eval z / r.denom.eval z := by
  funext z
  simp [ratEval, RatFunc.eval, Polynomial.eval₂_id]

private theorem analyticAt_poly (p : Polynomial ℂ) (c : ℂ) :
    AnalyticAt ℂ (fun z ↦ p.eval z) c :=
  AnalyticOnNhd.eval_polynomial p c (Set.mem_univ c)

/-- `ratEval r` is meromorphic at every point of `ℂ`. -/
theorem meromorphicAt_ratEval (r : RatFunc ℂ) (c : ℂ) : MeromorphicAt (ratEval r) c := by
  rw [ratEval_eq]
  exact (analyticAt_poly _ c).meromorphicAt.div (analyticAt_poly _ c).meromorphicAt

/-- `ratEval r` is analytic away from the zeros of the denominator. -/
theorem analyticAt_ratEval (r : RatFunc ℂ) {c : ℂ} (hc : r.denom.eval c ≠ 0) :
    AnalyticAt ℂ (ratEval r) c := by
  rw [ratEval_eq]
  exact (analyticAt_poly _ c).div (analyticAt_poly _ c) hc

/-- The residue of `ratEval r` vanishes at points where the denominator does not. -/
theorem residue_ratEval_eq_zero (r : RatFunc ℂ) {c : ℂ} (hc : r.denom.eval c ≠ 0) :
    TauCeti.Contour.residue (ratEval r) c = 0 :=
  TauCeti.Contour.residue_eq_zero_of_analyticAt (analyticAt_ratEval r hc)

private theorem meromorphicAt_poly_inv (p : Polynomial ℂ) :
    MeromorphicAt (fun u : ℂ ↦ p.eval u⁻¹) 0 := by
  have : (fun u : ℂ ↦ p.eval u⁻¹) =
      fun u ↦ ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (u⁻¹) ^ i := by
    funext u
    exact Polynomial.eval_eq_sum_range _
  rw [this]
  refine MeromorphicAt.fun_sum fun i _ ↦ ?_
  exact (MeromorphicAt.const _ _).mul (((MeromorphicAt.id 0).inv).pow i)

/-- The substitution `u = 1/w` in a circle integral: with the pullback `F(1/u)(-u⁻²) du`, one gets
`∮_{C(0,R⁻¹)} F(1/u)(-u⁻²) du = -∮_{C(0,R)} F(w) dw` (the circle is traversed in the opposite
direction). -/
theorem circleIntegral_inv_comp (F : ℂ → ℂ) {R : ℝ} (hR : 0 < R) :
    circleIntegral (fun u ↦ F u⁻¹ * -(u ^ 2)⁻¹) 0 R⁻¹ = -circleIntegral F 0 R := by
  set h : ℝ → ℂ := fun θ ↦ (R * exp (θ * I)) * I * F (R * exp (θ * I)) with hh
  have hper : Function.Periodic h (2 * π) := by
    intro θ
    simp only [hh]
    have : exp (((θ + 2 * π : ℝ) : ℂ) * I) = exp (θ * I) := by
      rw [show (((θ + 2 * π : ℝ) : ℂ) * I) = θ * I + 2 * π * I by push_cast; ring,
        Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    rw [this]
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have key : ∀ θ : ℝ, (circleMap 0 R⁻¹ θ * I) • (F (circleMap 0 R⁻¹ θ)⁻¹ *
      -(circleMap 0 R⁻¹ θ ^ 2)⁻¹) = -h (-θ) := by
    intro θ
    have he : exp (θ * I) ≠ 0 := Complex.exp_ne_zero _
    simp only [hh, circleMap_zero, smul_eq_mul]
    push_cast
    rw [show (-(θ : ℂ)) * I = -((θ : ℂ) * I) by ring, Complex.exp_neg]
    rw [show ((R : ℂ)⁻¹ * exp (θ * I))⁻¹ = R * (exp (θ * I))⁻¹ by
      rw [mul_inv, inv_inv]]
    field_simp
  unfold circleIntegral
  simp only [deriv_circleMap]
  simp_rw [key]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg (fun θ ↦ h θ)]
  have h2 : ∫ x in (-(2 * π))..(-0), h x = ∫ x in (0:ℝ)..(0 + 2 * π), h x := by
    rw [neg_zero, zero_add]
    have := hper.intervalIntegral_add_eq (-(2 * π)) 0
    rw [show -(2 * π) + 2 * π = 0 by ring, zero_add] at this
    exact this
  rw [h2, zero_add]
  simp only [hh, circleMap_zero, smul_eq_mul]

/-- **Residue theorem on the Riemann sphere** for a rational function, for any finite set `S`
containing the zeros of the denominator. -/
theorem sum_residue_ratEval_add_residue_infty_of_subset (r : RatFunc ℂ) (S : Finset ℂ)
    (hS : ∀ c, r.denom.eval c = 0 → c ∈ S) :
    ∑ c ∈ S, TauCeti.Contour.residue (ratEval r) c +
      TauCeti.Contour.residue (fun u ↦ ratEval r u⁻¹ * -(u ^ 2)⁻¹) 0 = 0 := by
  set R : ℝ := 1 + ∑ s ∈ S, ‖s‖ with hRdef
  have hsum : 0 ≤ ∑ s ∈ S, ‖s‖ := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hR : 0 < R := by rw [hRdef]; linarith
  have hlt : ∀ s ∈ S, ‖s‖ < R := fun s hs ↦ by
    have := Finset.single_le_sum (f := fun s : ℂ ↦ ‖s‖) (fun _ _ ↦ norm_nonneg _) hs
    rw [hRdef]; linarith
  -- the circle of radius `R`
  have hcirc := TauCeti.Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg
    (f := ratEval r) (c := 0) hR S (fun z _ ↦ meromorphicAt_ratEval r z)
    (fun s hs ↦ by simpa using hlt s hs)
    (fun z _ hz ↦ by
      by_contra hzS
      have hd : r.denom.eval z ≠ 0 := fun h ↦ hzS (hS z h)
      exact absurd (analyticAt_ratEval r hd).meromorphicOrderAt_nonneg (not_le.2 hz))
  -- the circle of radius `R⁻¹` in the coordinate `u`
  set g : ℂ → ℂ := fun u ↦ ratEval r u⁻¹ * -(u ^ 2)⁻¹ with hg
  have hRi : 0 < R⁻¹ := inv_pos.2 hR
  have hgan : ∀ u : ℂ, u ≠ 0 → ‖u‖ ≤ R⁻¹ → AnalyticAt ℂ g u := by
    intro u hu hur
    have hd : r.denom.eval u⁻¹ ≠ 0 := by
      intro h
      have h1 := hlt _ (hS _ h)
      rw [norm_inv] at h1
      have hupos : 0 < ‖u‖ := norm_pos_iff.2 hu
      have : R ≤ ‖u‖⁻¹ := by
        rw [le_inv_comm₀ hR hupos]; exact hur
      linarith
    refine AnalyticAt.mul ?_ ?_
    · exact (analyticAt_ratEval r hd).comp (analyticAt_inv hu)
    · exact ((analyticAt_id.pow 2).inv (pow_ne_zero 2 hu)).neg
  have hg0 : MeromorphicAt g 0 := by
    have : g = fun u ↦ (r.num.eval u⁻¹ / r.denom.eval u⁻¹) * -(u ^ 2)⁻¹ := by
      funext u; simp only [hg, ratEval_eq]
    rw [this]
    refine ((meromorphicAt_poly_inv _).div (meromorphicAt_poly_inv _)).mul ?_
    exact ((MeromorphicAt.id 0).pow 2).inv.neg
  have hcirc2 := TauCeti.Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg
    (f := g) (c := 0) hRi {0}
    (fun u hu ↦ by
      by_cases h0 : u = 0
      · subst h0; exact hg0
      · exact (hgan u h0 (by simpa using hu)).meromorphicAt)
    (by simpa using hRi)
    (fun z hz hlt0 ↦ by
      by_contra hz0
      have hz0' : z ≠ 0 := by simpa using hz0
      exact absurd (hgan z hz0' (by simpa using hz)).meromorphicOrderAt_nonneg (not_le.2 hlt0))
  have hint := circleIntegral_inv_comp (ratEval r) hR
  rw [← hg, hcirc2, hcirc] at hint
  simp only [Finset.sum_singleton] at hint
  have hne : (2 * (π : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : 2 * (π : ℂ) * I * (TauCeti.Contour.residue g 0 +
      ∑ s ∈ S, TauCeti.Contour.residue (ratEval r) s) = 0 := by
    rw [mul_add]; linear_combination hint
  have := (mul_eq_zero.1 this).resolve_left hne
  rw [add_comm]; exact this

/-- **Residue theorem on the Riemann sphere** for a rational function `r`: the residues at the finite
poles plus the residue at `∞`, computed in the coordinate `u = 1/z` (where
`r(z) dz = -r(1/u) u⁻² du`), sum to zero (Milne, Proposition 1.12 (b)). -/
theorem sum_residue_ratEval_add_residue_infty (r : RatFunc ℂ) :
    ∑ c ∈ r.denom.roots.toFinset, TauCeti.Contour.residue (ratEval r) c +
      TauCeti.Contour.residue (fun u ↦ ratEval r u⁻¹ * -(u ^ 2)⁻¹) 0 = 0 := by
  refine sum_residue_ratEval_add_residue_infty_of_subset r _ fun c hc ↦ ?_
  have hd : r.denom ≠ 0 := RatFunc.denom_ne_zero r
  simpa [Multiset.mem_toFinset, Polynomial.mem_roots hd] using hc

end ModularFormsKB.Milne.RS
