/-
# The geodesic as a flow

For an integral binary quadratic form $Q$ of discriminant
$\Delta > 0$, the arc-length parametrization `BinQF.geodesic` of `Abstract/Shintani.lean` is the flow of
$\dot z = Q(z,1)/\sqrt\Delta$.

Proved:
- `BinQF.hasDerivAt_geodesic`: $\frac{d}{ds}z_Q(s) = Q(z_Q(s), 1)/\sqrt\Delta$, i.e. $dz/Q(z,1) = ds/\sqrt\Delta$;
- `BinQF.continuous_geodesic`: the geodesic is continuous;
- `BinQF.evalC_geodesic_ne_zero`: $Q(z_Q(s), 1) \ne 0$.
-/
import ModularFormsKB.HalfIntegral.Abstract.Shintani

namespace ModularFormsKB.HalfIntegral

namespace BinQF

open Complex

private theorem hasDerivAt_geodesic_zero (Q : BinQF) (ha : Q.a = 0) (hQ : 0 < Q.disc) (s : ℝ) :
    HasDerivAt Q.geodesic (Q.evalC (Q.geodesic s) / ((√(Q.disc : ℝ) : ℝ) : ℂ)) s := by
  have hb : Q.b ≠ 0 := by
    intro h; simp [disc, ha, h] at hQ
  have hR : √(Q.disc : ℝ) = |(Q.b : ℝ)| := by
    rw [← Real.sqrt_sq_eq_abs]; congr 1; simp [disc, ha]
  have hb' : (Q.b : ℝ) ≠ 0 := by exact_mod_cast hb
  have key : ∀ σ : ℝ, σ * Q.b = |(Q.b : ℝ)| → σ ^ 2 = 1 → (SignType.sign (Q.b : ℝ) : ℝ) = σ →
      HasDerivAt Q.geodesic (Q.evalC (Q.geodesic s) / ((√(Q.disc : ℝ) : ℝ) : ℂ)) s := by
    intro σ hσ hσ2 hsg
    have hg : Q.geodesic = fun s => ((-(Q.c : ℝ) / Q.b : ℝ) : ℂ) + I * (Real.exp (σ * s) : ℝ) := by
      funext t; simp only [geodesic, ha, ↓reduceIte, hsg]
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (σ * s)) (Real.exp (σ * s) * σ) s := by
      simpa using ((hasDerivAt_id s).const_mul σ).exp
    have h2 := (h1.ofReal_comp).const_mul I |>.const_add ((-(Q.c : ℝ) / Q.b : ℝ) : ℂ)
    rw [hg]
    convert h2 using 1
    have hR' : ((√(Q.disc : ℝ) : ℝ) : ℂ) = ((|(Q.b : ℝ)| : ℝ) : ℂ) := by rw [hR]
    rw [hR', ← hσ]
    have hb'' : (Q.b : ℂ) ≠ 0 := by exact_mod_cast hb
    have hσ2c : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ2
    have hσc : (σ : ℂ) ≠ 0 := by
      intro h0; rw [h0] at hσ2c; norm_num at hσ2c
    simp only [evalC, ha]
    push_cast
    field_simp
    linear_combination (-((Q.b : ℂ) ^ 3 * I * cexp (↑σ * ↑s))) * hσ2c
  rcases lt_or_gt_of_ne hb' with h | h
  · refine key (-1) (by rw [abs_of_neg h]; ring) (by norm_num) ?_
    simp [h]
  · refine key 1 (by rw [abs_of_pos h]; ring) (by norm_num) ?_
    simp [h]

private theorem hasDerivAt_geodesic_ne (Q : BinQF) (ha : Q.a ≠ 0) (hQ : 0 < Q.disc) (s : ℝ) :
    HasDerivAt Q.geodesic (Q.evalC (Q.geodesic s) / ((√(Q.disc : ℝ) : ℝ) : ℂ)) s := by
  set R : ℝ := √(Q.disc : ℝ) with hRdef
  have hRpos : 0 < R := Real.sqrt_pos.2 (by exact_mod_cast hQ)
  have hR2 : R ^ 2 = (Q.b : ℝ) ^ 2 - 4 * Q.a * Q.c := by
    rw [hRdef, Real.sq_sqrt (by exact_mod_cast hQ.le)]; simp [disc]
  have ha' : (Q.a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hC : 0 < Real.cosh s := Real.cosh_pos s
  have hCS : Real.cosh s ^ 2 = Real.sinh s ^ 2 + 1 := Real.cosh_sq s
  have hx : HasDerivAt (fun s : ℝ => (-(Q.b : ℝ) - R * (Real.sinh s / Real.cosh s)) / (2 * Q.a))
      ((-(R * ((Real.cosh s * Real.cosh s - Real.sinh s * Real.sinh s) / Real.cosh s ^ 2)))
        / (2 * Q.a)) s := by
    have := (((Real.hasDerivAt_sinh s).div (Real.hasDerivAt_cosh s) hC.ne').const_mul R).const_sub
      (-(Q.b : ℝ)) |>.div_const (2 * (Q.a : ℝ))
    simpa using this
  have hy : HasDerivAt (fun s : ℝ => R / (2 * |(Q.a : ℝ)| * Real.cosh s))
      (-(R * (2 * |(Q.a : ℝ)| * Real.sinh s)) / (2 * |(Q.a : ℝ)| * Real.cosh s) ^ 2) s := by
    have h := (((Real.hasDerivAt_cosh s).const_mul (2 * |(Q.a : ℝ)|)).fun_inv
      (mul_pos (by positivity) hC).ne').const_mul R
    convert h using 1
    · funext t; simp [div_eq_mul_inv]
    · simp only [div_eq_mul_inv]; ring
  have h2 := (hx.ofReal_comp.add (hy.ofReal_comp.const_mul I))
  have hg : Q.geodesic = fun s => ((((-(Q.b : ℝ) - R * (Real.sinh s / Real.cosh s)) / (2 * Q.a) : ℝ) : ℂ)
      + I * ((R / (2 * |(Q.a : ℝ)| * Real.cosh s) : ℝ) : ℂ)) := by
    funext t; simp [geodesic, ha, hRdef, Real.tanh_eq_sinh_div_cosh]
  rw [hg]
  convert h2 using 1
  have hCc : (Real.cosh s : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
  have hac : (Q.a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hR2c : (R : ℂ) ^ 2 = (Q.b : ℂ) ^ 2 - 4 * Q.a * Q.c := by exact_mod_cast hR2
  have hCSc : (Real.cosh s : ℂ) ^ 2 = (Real.sinh s : ℂ) ^ 2 + 1 := by exact_mod_cast hCS
  beta_reduce
  generalize Real.sinh s = S at hCSc ⊢
  generalize Real.cosh s = C at hCc hCSc ⊢
  rcases lt_or_gt_of_ne ha' with h | h
  · rw [abs_of_neg h]
    simp only [evalC]
    push_cast
    field_simp
    linear_combination (R : ℂ) ^ 2 * hCSc + (R : ℂ) ^ 2 * Complex.I_sq + (C : ℂ) ^ 2 * hR2c
  · rw [abs_of_pos h]
    simp only [evalC]
    push_cast
    field_simp
    linear_combination (R : ℂ) ^ 2 * hCSc + (R : ℂ) ^ 2 * Complex.I_sq + (C : ℂ) ^ 2 * hR2c

/-- **The geodesic is the flow of $\dot z = Q(z,1)/\sqrt\Delta$**, i.e. $dz/Q(z,1) = ds/\sqrt\Delta$ along it. -/
theorem hasDerivAt_geodesic (Q : BinQF) (hQ : 0 < Q.disc) (s : ℝ) :
    HasDerivAt Q.geodesic (Q.evalC (Q.geodesic s) / ((√(Q.disc : ℝ) : ℝ) : ℂ)) s := by
  by_cases ha : Q.a = 0
  · exact hasDerivAt_geodesic_zero Q ha hQ s
  · exact hasDerivAt_geodesic_ne Q ha hQ s

/-- The geodesic is continuous. -/
theorem continuous_geodesic (Q : BinQF) (hQ : 0 < Q.disc) : Continuous Q.geodesic :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_geodesic Q hQ s).continuousAt

/-- For $\Delta > 0$, $Q(z, 1) \ne 0$ for every $z$ in the upper half plane. -/
private theorem evalC_ne_zero_of_im_pos (Q : BinQF) (hQ : 0 < Q.disc) (z : ℂ) (hz : 0 < z.im) :
    Q.evalC z ≠ 0 := by
  intro h0
  by_cases ha : Q.a = 0
  · have hb : Q.b ≠ 0 := by
      intro h; simp [disc, ha, h] at hQ
    have := congrArg Complex.im h0
    simp [evalC, ha] at this
    rcases this with h | h
    · exact hb h
    · exact hz.ne' h
  · have hD : (0 : ℝ) < Q.disc := by exact_mod_cast hQ
    have hsq : (2 * (Q.a : ℂ) * z + Q.b) ^ 2 = ((√(Q.disc : ℝ) : ℝ) : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hD.le]
      have : Q.a * (4 * Q.evalC z) = 0 := by rw [h0]; ring
      simp only [evalC, disc] at this ⊢
      push_cast
      linear_combination this
    have him : (2 * (Q.a : ℂ) * z + Q.b).im ≠ 0 := by
      have e : (2 * (Q.a : ℂ) * z + Q.b).im = 2 * Q.a * z.im := by
        simp [mul_im]
      have : (Q.a : ℝ) ≠ 0 := by exact_mod_cast ha
      rw [e]
      exact mul_ne_zero (mul_ne_zero two_ne_zero this) hz.ne'
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h <;>
      exact him (by rw [h]; simp)

/-- The geodesic avoids the zeros of $Q(z, 1)$. -/
theorem evalC_geodesic_ne_zero (Q : BinQF) (hQ : 0 < Q.disc) (s : ℝ) :
    Q.evalC (Q.geodesic s) ≠ 0 :=
  evalC_ne_zero_of_im_pos Q hQ _ (geodesic_im_pos Q hQ s)

end BinQF

end ModularFormsKB.HalfIntegral
