import ModularFormsKB.Milne.Wave5.EndomorphismLift
import ModularFormsKB.Milne.Ch3.AbelJacobi

/-!
# Milne wave 5: evaluating functions of `E(Λ)` along `z ↦ (℘(z), ℘'(z)/2)`

A class of the coordinate ring `ℂ[x, y]/(y² - x³ + (g₂/4)x + g₃/4)` of `E(Λ)` is determined by the function
`z ↦ A(℘(z), ℘'(z)/2)` on `ℂ`: if that function vanishes off a discrete set, the class is zero
(`mk_eq_zero_of_eventually`). Reducing `A` to `a(x) + b(x) y`, the norm `a² - b² (x³ - (g₂/4)x - g₃/4)` vanishes at
`℘(z)` off a discrete set, hence everywhere (identity theorem on the connected set `ℂ ∖ Λ`, and `℘` takes every
value), hence is the zero polynomial; comparing degrees (even against odd) gives `a = b = 0`.

This is how analytic identities between elliptic functions are transported to the function field of `E(Λ)`, for the
construction of the endomorphism `[z] ↦ [αz]` (`ModularFormsKB.Milne.Wave5.MultiplicationIsogeny`).
-/

open Complex PeriodPair TauCeti TauCeti.Isogeny Polynomial Filter Topology WeierstrassCurve.Affine

namespace ModularFormsKB.Milne.Wave5

variable (L : PeriodPair)

/-- The value of a bivariate polynomial at `(℘(z), ℘'(z)/2)`. -/
noncomputable def evWP (A : ℂ[X][X]) (z : ℂ) : ℂ := A.evalEval (℘[L] z) (℘'[L] z / 2)

@[simp] theorem evWP_add (A B : ℂ[X][X]) (z : ℂ) : evWP L (A + B) z = evWP L A z + evWP L B z := by
  simp [evWP]
@[simp] theorem evWP_sub (A B : ℂ[X][X]) (z : ℂ) : evWP L (A - B) z = evWP L A z - evWP L B z := by
  simp [evWP]
@[simp] theorem evWP_mul (A B : ℂ[X][X]) (z : ℂ) : evWP L (A * B) z = evWP L A z * evWP L B z := by
  simp [evWP]
@[simp] theorem evWP_pow (A : ℂ[X][X]) (n : ℕ) (z : ℂ) : evWP L (A ^ n) z = evWP L A z ^ n := by
  simp [evWP]
@[simp] theorem evWP_C (a : ℂ[X]) (z : ℂ) : evWP L (C a) z = a.eval (℘[L] z) := by
  simp [evWP, evalEval_C]

/-- Classes equal in the coordinate ring take equal values along `(℘, ℘'/2)` off the lattice. -/
theorem evWP_eq_of_mk_eq {A B : ℂ[X][X]}
    (h : CoordinateRing.mk L.weierstrassCurve.toAffine A = CoordinateRing.mk L.weierstrassCurve.toAffine B)
    {z : ℂ} (hz : z ∉ L.lattice) : evWP L A z = evWP L B z :=
  WeierstrassCurve.evalEval_eq_of_mk_eq _ (L.equation_weierstrassP hz) h

theorem eventually_notMem_lattice_codiscrete : ∀ᶠ z in codiscrete ℂ, z ∉ L.lattice := by
  rw [eventually_codiscrete_iff_forall_eventually_nhdsNE]
  intro z
  exact L.eventually_notMem_lattice z

/-- `a(℘) + b(℘) ℘'/2 = 0` off a discrete set forces `a = b = 0`. -/
theorem eq_zero_of_eventually_add_mul {a b : ℂ[X]}
    (h : ∀ᶠ z in codiscrete ℂ, a.eval (℘[L] z) + b.eval (℘[L] z) * (℘'[L] z / 2) = 0) : a = 0 ∧ b = 0 := by
  set N : ℂ[X] := a ^ 2 - b ^ 2 * cubicPoly L
  have hN : ∀ᶠ z in codiscrete ℂ, N.eval (℘[L] z) = 0 := by
    filter_upwards [h, eventually_notMem_lattice_codiscrete L] with z hz hzL
    have hsq := sq_eq_cubicPoly L (L.equation_weierstrassP hzL)
    simp only [N, eval_sub, eval_pow, eval_mul]
    rw [← hsq]
    linear_combination (a.eval (℘[L] z) - b.eval (℘[L] z) * (℘'[L] z / 2)) * hz
  have hU : IsPreconnected (L.lattice : Set ℂ)ᶜ :=
    (L.countable_lattice.isPathConnected_compl_of_one_lt_rank
      (by rw [rank_real_complex]; norm_num)).isConnected.isPreconnected
  have han : AnalyticOnNhd ℂ (fun z ↦ N.eval (℘[L] z)) (L.lattice : Set ℂ)ᶜ :=
    fun z hz ↦ ((N.differentiable.analyticAt (℘[L] z)).comp (L.analyticOnNhd_weierstrassP z hz) :)
  obtain ⟨z₁, hz₁⟩ := L.exists_weierstrassP_eq 0
  have hfreq : ∃ᶠ z in 𝓝[≠] z₁, N.eval (℘[L] z) = 0 :=
    (hN.filter_mono (nhdsNE_le_codiscrete z₁)).frequently
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hz₁.1 hfreq
  have hN0 : N = 0 := by
    refine Polynomial.funext fun x ↦ ?_
    obtain ⟨z, hz, rfl⟩ := L.exists_weierstrassP_eq x
    simpa using hzero hz
  have hcub : (cubicPoly L).natDegree = 3 := by
    unfold cubicPoly; compute_degree!
  have heq : a ^ 2 = b ^ 2 * cubicPoly L := sub_eq_zero.1 hN0
  by_cases hb : b = 0
  · subst hb
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      pow_eq_zero_iff] at heq
    exact ⟨heq, rfl⟩
  · exfalso
    have hd := congrArg natDegree heq
    rw [natDegree_mul (pow_ne_zero 2 hb) (cubicPoly_ne_zero L), natDegree_pow, natDegree_pow, hcub] at hd
    omega

/-- **A class of the coordinate ring vanishing along `(℘, ℘'/2)` off a discrete set is zero.** -/
theorem mk_eq_zero_of_eventually (A : ℂ[X][X]) (h : ∀ᶠ z in codiscrete ℂ, evWP L A z = 0) :
    CoordinateRing.mk L.weierstrassCurve.toAffine A = 0 := by
  have hmon := L.weierstrassCurve.toAffine.monic_polynomial
  obtain ⟨R, hR_def⟩ : ∃ R, R = A %ₘ L.weierstrassCurve.toAffine.polynomial := ⟨_, rfl⟩
  have hdeg : R.degree ≤ 1 := by
    have := degree_modByMonic_lt A hmon
    rw [degree_eq_natDegree hmon.ne_zero, L.weierstrassCurve.toAffine.natDegree_polynomial] at this
    rw [hR_def]
    exact Order.le_of_lt_succ this
  have hAR : A = L.weierstrassCurve.toAffine.polynomial * (A /ₘ L.weierstrassCurve.toAffine.polynomial) + R := by
    rw [hR_def, add_comm]; exact (modByMonic_add_div A _).symm
  have hR := eq_X_add_C_of_degree_le_one hdeg
  have hval : ∀ᶠ z in codiscrete ℂ,
      (R.coeff 0).eval (℘[L] z) + (R.coeff 1).eval (℘[L] z) * (℘'[L] z / 2) = 0 := by
    filter_upwards [h, eventually_notMem_lattice_codiscrete L] with z hz hzL
    have hpoly : L.weierstrassCurve.toAffine.polynomial.evalEval (℘[L] z) (℘'[L] z / 2) = 0 :=
      L.equation_weierstrassP hzL
    unfold evWP at hz
    rw [hAR, evalEval_add, evalEval_mul, hpoly, zero_mul, zero_add] at hz
    rw [← hz]
    conv_rhs => rw [hR]
    simp only [evalEval, eval_add, eval_mul, eval_C, eval_X]
    ring
  obtain ⟨h0, h1⟩ := eq_zero_of_eventually_add_mul L hval
  have hR0 : R = 0 := by rw [hR, h0, h1]; simp
  rw [hAR, map_add, map_mul, hR0, map_zero, add_zero]
  simp [CoordinateRing.mk, AdjoinRoot.mk_self]

/-- **The evaluation of a two-variable polynomial in `℘, ℘'` as a polynomial in `x, y = ℘'/2`.** -/
noncomputable def toXY (P : MvPolynomial (Fin 2) ℂ) : ℂ[X][X] :=
  MvPolynomial.aeval ![C X, C (C 2) * X] P

theorem evalEval_toXY (P : MvPolynomial (Fin 2) ℂ) (x y : ℂ) :
    (toXY P).evalEval x y = MvPolynomial.eval ![x, 2 * y] P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [toXY, evalEval]
  | add p q hp hq =>
    rw [show toXY (p + q) = toXY p + toXY q from map_add _ _ _, evalEval_add, hp, hq, map_add]
  | mul_X p i hp =>
    simp only [toXY, map_mul, MvPolynomial.aeval_X, evalEval_mul] at hp ⊢
    rw [hp]
    fin_cases i <;> simp [evalEval]

theorem evWP_toXY (P : MvPolynomial (Fin 2) ℂ) (z : ℂ) :
    evWP L (toXY P) z = MvPolynomial.eval ![℘[L] z, ℘'[L] z] P := by
  rw [evWP, evalEval_toXY]
  congr 2
  simp [mul_div_cancel₀]

end ModularFormsKB.Milne.Wave5
