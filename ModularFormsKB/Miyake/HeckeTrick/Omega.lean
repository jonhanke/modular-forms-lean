import ModularFormsKB.Miyake.HeckeTrick.Sigma
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Miyake §7.2: the function $\omega(z;\alpha,\beta)$ (Theorem 7.2.4, Lemma 7.2.6, Theorem 7.2.7)

Miyake, *Modular Forms*, §7.2, pp. 279–282. On $\mathbf H' \times \mathbb C \times \mathbf H'$ Miyake puts
$$\omega(z;\alpha,\beta) = \Gamma(\beta)^{-1}z^{\beta}\sigma(z;\alpha,\beta) \qquad (7.2.31)$$
and continues it to $\mathbf H' \times \mathbb C \times \mathbb C$ (Theorem 7.2.4).

**Route of the continuation.** The book continues $\omega$ by the symmetry 7.2.4 (1) and the derivative
formula 7.2.4 (2). We continue it instead by the recurrence (7.2.39),
$\omega(z;\alpha,\beta) = \omega(z;\alpha,\beta+1) + (1-\alpha)z^{-1}\omega(z;\alpha-1,\beta+1)$, which the book
proves for $z = y > 0$ on p. 282 (and which holds on $\mathbf H'$ by (7.2.38)): `omegaAux n` is the $n$-fold
application of the recurrence to (7.2.31), defined and holomorphic on $\operatorname{Re}\beta > -n$, and the
`omegaAux n` agree where both are defined. The continuation is unique (identity theorem), so this is the
book's $\omega$; the statements 7.2.4 (1), (2) are then proved for the continued function.

Off $\mathbf H'$ (`0 < z.re` fails) the Lean function has no meaning.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace ModularFormsKB.Miyake.HeckeTrick

/-- **Miyake (7.2.31)** on its domain of definition $\mathbf H' \times \mathbb C \times \mathbf H'$:
$\omega_0(z;\alpha,\beta) = \Gamma(\beta)^{-1}z^{\beta}\sigma(z;\alpha,\beta)$. -/
@[kb "miyake1989" "(7.2.31), p. 279"]
def omega0 (z α β : ℂ) : ℂ := (Gamma β)⁻¹ * z ^ β * sigma z α β

/-- The $n$-fold application of the recurrence (7.2.39) to `omega0`; it represents $\omega$ on
$\operatorname{Re}\beta > -n$. -/
def omegaAux : ℕ → ℂ → ℂ → ℂ → ℂ
  | 0 => omega0
  | n + 1 => fun z α β ↦ omegaAux n z α (β + 1) + (1 - α) * z⁻¹ * omegaAux n z (α - 1) (β + 1)

/-- **Miyake (7.2.31) and Theorem 7.2.4.** The function $\omega(z;\alpha,\beta)$ on $\mathbf H' \times \mathbb C
\times \mathbb C$: `omegaAux n` with $n = \lfloor -\operatorname{Re}\beta \rfloor_+ + 1 > -\operatorname{Re}\beta$. -/
@[kb "miyake1989" "(7.2.31) and Theorem 7.2.4, pp. 279-280"]
def omega (z α β : ℂ) : ℂ := omegaAux (⌊-β.re⌋₊ + 1) z α β

/-- **Miyake (7.2.39)** for `omega0`, on $\mathbf H' \times \mathbb C \times \mathbf H'$ (from (7.2.38)). -/
theorem omega0_rec {z α β : ℂ} (hz : 0 < z.re) (hβ : 0 < β.re) :
    omega0 z α β = omega0 z α (β + 1) + (1 - α) * z⁻¹ * omega0 z (α - 1) (β + 1) := by
  have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz
  have hβ0 : β ≠ 0 := fun h ↦ by simp [h] at hβ
  have hΓ : Gamma β ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hβ
  simp only [omega0]
  rw [sigma_succ hz hβ, Complex.cpow_add _ _ hz0, Complex.cpow_one, Complex.Gamma_add_one _ hβ0]
  field_simp
  ring

/-- The representatives agree: `omegaAux (n + 1) = omegaAux n` on $\operatorname{Re}\beta > -n$. -/
theorem omegaAux_succ {n : ℕ} {z : ℂ} (hz : 0 < z.re) {α β : ℂ} (hβ : -(n : ℝ) < β.re) :
    omegaAux (n + 1) z α β = omegaAux n z α β := by
  induction n generalizing α β with
  | zero =>
    simp only [omegaAux]
    exact (omega0_rec hz (by simpa using hβ)).symm
  | succ n ih =>
    have h1 : -(n : ℝ) < (β + 1).re := by simp; push_cast at hβ; linarith
    change omegaAux (n + 1) z α (β + 1) + (1 - α) * z⁻¹ * omegaAux (n + 1) z (α - 1) (β + 1) =
      omegaAux n z α (β + 1) + (1 - α) * z⁻¹ * omegaAux n z (α - 1) (β + 1)
    rw [ih h1, ih h1]

/-- The representatives agree: `omegaAux m = omegaAux n` on $\operatorname{Re}\beta > -n$ for $m \ge n$. -/
theorem omegaAux_eq_of_le {n m : ℕ} (hnm : n ≤ m) {z : ℂ} (hz : 0 < z.re) {α β : ℂ}
    (hβ : -(n : ℝ) < β.re) : omegaAux m z α β = omegaAux n z α β := by
  induction hnm with
  | refl => rfl
  | step h ih =>
    rename_i m
    have : -(m : ℝ) < β.re := lt_of_le_of_lt (by simpa using (Nat.cast_le (α := ℝ)).mpr h) hβ
    rw [omegaAux_succ hz this, ih]

lemma neg_floor_lt (β : ℂ) : -((⌊-β.re⌋₊ + 1 : ℕ) : ℝ) < β.re := by
  have := Nat.lt_floor_add_one (-β.re)
  push_cast
  linarith

/-- $\omega$ is represented by `omegaAux n` on $\operatorname{Re}\beta > -n$. -/
theorem omega_eq_omegaAux {n : ℕ} {z : ℂ} (hz : 0 < z.re) {α β : ℂ} (hβ : -(n : ℝ) < β.re) :
    omega z α β = omegaAux n z α β := by
  unfold omega
  rw [← omegaAux_eq_of_le (le_max_left (⌊-β.re⌋₊ + 1) n) hz (neg_floor_lt β),
    omegaAux_eq_of_le (le_max_right (⌊-β.re⌋₊ + 1) n) hz hβ]

/-- On its original domain $\omega$ is (7.2.31). -/
@[kb "miyake1989" "(7.2.31), p. 279"]
theorem omega_eq_omega0 {z α β : ℂ} (hz : 0 < z.re) (hβ : 0 < β.re) :
    omega z α β = (Gamma β)⁻¹ * z ^ β * sigma z α β :=
  omega_eq_omegaAux (n := 0) hz (by simpa using hβ)

/-- **Miyake (7.2.39)**, on all of $\mathbf H' \times \mathbb C \times \mathbb C$:
$\omega(z;\alpha,\beta) = \omega(z;\alpha,\beta+1) + (1-\alpha)z^{-1}\omega(z;\alpha-1,\beta+1)$. -/
@[kb "miyake1989" "(7.2.39), p. 282"]
theorem omega_rec {z : ℂ} (hz : 0 < z.re) (α β : ℂ) :
    omega z α β = omega z α (β + 1) + (1 - α) * z⁻¹ * omega z (α - 1) (β + 1) := by
  set n := ⌊-β.re⌋₊ + 1 with hn_def
  have hn : -(n : ℝ) < β.re := neg_floor_lt β
  have hn1 : -((n + 1 : ℕ) : ℝ) < β.re := by push_cast; linarith
  have hn' : -(n : ℝ) < (β + 1).re := by simp; linarith
  rw [omega_eq_omegaAux hz hn1, omega_eq_omegaAux hz hn', omega_eq_omegaAux hz hn']
  rfl

/-- `omegaAux n` is holomorphic (jointly in $(z,\alpha,\beta)$) on $\mathbf H' \times \mathbb C \times
\{\operatorname{Re}\beta > -n\}$. -/
theorem differentiableOn_omegaAux (n : ℕ) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ ↦ omegaAux n p.1 p.2.1 p.2.2)
      {p | 0 < p.1.re ∧ -(n : ℝ) < p.2.2.re} := by
  induction n with
  | zero =>
    simp only [omegaAux, omega0, Nat.cast_zero, neg_zero]
    intro p hp
    have hslit : p.1 ∈ Complex.slitPlane := Or.inl hp.1
    exact ((((Complex.differentiable_one_div_Gamma _).comp p differentiableAt_snd.snd).mul
      (differentiableAt_fst.cpow differentiableAt_snd.snd hslit)).differentiableWithinAt).mul
      (differentiableOn_sigma p hp)
  | succ n ih =>
    have hU : ∀ c : ℂ, Set.MapsTo (fun p : ℂ × ℂ × ℂ ↦ (p.1, p.2.1 + c, p.2.2 + 1))
        {p | 0 < p.1.re ∧ -((n + 1 : ℕ) : ℝ) < p.2.2.re} {p | 0 < p.1.re ∧ -(n : ℝ) < p.2.2.re} := by
      intro c p hp
      refine ⟨hp.1, ?_⟩
      have := hp.2
      simp only [Complex.add_re, Complex.one_re]
      push_cast at this
      linarith
    have hd : ∀ c : ℂ, DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ ↦ omegaAux n p.1 (p.2.1 + c) (p.2.2 + 1))
        {p | 0 < p.1.re ∧ -((n + 1 : ℕ) : ℝ) < p.2.2.re} := fun c ↦
      ih.comp (by fun_prop) (hU c)
    have h1 := hd 0
    have h2 := hd (-1)
    simp only [add_zero] at h1
    simp only [← sub_eq_add_neg] at h2
    change DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ ↦ omegaAux n p.1 p.2.1 (p.2.2 + 1) +
      (1 - p.2.1) * p.1⁻¹ * omegaAux n p.1 (p.2.1 - 1) (p.2.2 + 1)) _
    refine h1.add (DifferentiableOn.mul (DifferentiableOn.mul (by fun_prop) ?_) h2)
    intro p hp
    have : p.1 ≠ 0 := fun h ↦ by have := hp.1; simp [h] at this
    exact (differentiableAt_fst.inv this).differentiableWithinAt

/-- **Miyake, Theorem 7.2.4 (holomorphy).** $\omega(z;\alpha,\beta)$ is holomorphic on
$\mathbf H' \times \mathbb C \times \mathbb C$ (jointly in the three variables). -/
@[kb "miyake1989" "Theorem 7.2.4, p. 279"]
theorem differentiableOn_omega :
    DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ ↦ omega p.1 p.2.1 p.2.2) {p | 0 < p.1.re} := by
  intro p hp
  set n := ⌊-p.2.2.re⌋₊ + 1
  set U : Set (ℂ × ℂ × ℂ) := {q | 0 < q.1.re ∧ -(n : ℝ) < q.2.2.re}
  have hUo : IsOpen U := by
    show IsOpen ({q : ℂ × ℂ × ℂ | 0 < q.1.re} ∩ {q | -(n : ℝ) < q.2.2.re})
    exact (isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt continuous_const (by fun_prop))
  have hpU : p ∈ U := ⟨hp, neg_floor_lt p.2.2⟩
  have hd := (differentiableOn_omegaAux n).differentiableAt (hUo.mem_nhds hpU)
  refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hUo.mem_nhds hpU] with q hq
  exact omega_eq_omegaAux hq.1 hq.2

/-! ### The symmetry (Theorem 7.2.4 (1)) -/

/-- The integrand of the double integral in the proof of Theorem 7.2.4 (1) (Miyake p. 279):
$e^{-x(u+w+uw)}u^{a-1}w^{b-1}$. -/
def symmIntegrand (x : ℝ) (a b : ℂ) (u w : ℝ) : ℂ :=
  cexp (-(x : ℂ) * ((u : ℂ) + w + u * w)) * (u : ℂ) ^ (a - 1) * (w : ℂ) ^ (b - 1)

theorem ofReal_inv_cpow {p : ℝ} (hp : 0 < p) (s : ℂ) :
    (((p⁻¹ : ℝ)) : ℂ) ^ s = ((p : ℂ) ^ s)⁻¹ := by
  rw [Complex.ofReal_inv]
  exact Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hp.le]; exact Real.pi_pos.ne)

/-- The inner integral: $\int_0^\infty e^{-x(u+w+uw)}w^{b-1}dw = e^{-xu}\Gamma(b)(x(u+1))^{-b}$. -/
theorem integral_symmIntegrand_inner {x : ℝ} (hx : 0 < x) {a b : ℂ} (hb : 0 < b.re) {u : ℝ}
    (hu : 0 < u) : ∫ w in Ioi (0 : ℝ), symmIntegrand x a b u w =
      cexp (-(x : ℂ) * u) * (u : ℂ) ^ (a - 1) * ((1 / ((x * (u + 1) : ℝ) : ℂ)) ^ b * Gamma b) := by
  have hr : 0 < x * (u + 1) := by positivity
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hb hr
  rw [← h, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun w _ ↦ ?_)
  simp only [symmIntegrand]
  have : cexp (-(x : ℂ) * ((u : ℂ) + w + u * w)) =
      cexp (-(x : ℂ) * u) * cexp (-(((x * (u + 1) : ℝ) : ℂ) * (w : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [this]; ring

/-- $\Gamma(b)\sigma(x;1-b,a) = x^b\int_0^\infty\int_0^\infty e^{-x(u+w+uw)}u^{a-1}w^{b-1}\,dw\,du$
(Miyake p. 279; $\operatorname{Re} b > 0$). -/
theorem Gamma_mul_sigma_symm {x : ℝ} (hx : 0 < x) {a b : ℂ} (hb : 0 < b.re) :
    Gamma b * sigma x (1 - b) a =
      (x : ℂ) ^ b * ∫ u in Ioi (0 : ℝ), ∫ w in Ioi (0 : ℝ), symmIntegrand x a b u w := by
  rw [sigma, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u hu ↦ ?_)
  have hu0 : (0 : ℝ) < u := hu
  rw [integral_symmIntegrand_inner hx hb hu0]
  simp only [sigmaIntegrand]
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hu1 : ((u : ℂ) + 1) ≠ 0 := by exact_mod_cast (by positivity : u + 1 ≠ 0)
  have e1 : (1 / ((x * (u + 1) : ℝ) : ℂ)) ^ b = ((x : ℂ) ^ b)⁻¹ * (((u + 1 : ℝ) : ℂ) ^ b)⁻¹ := by
    have : (1 / ((x * (u + 1) : ℝ) : ℂ)) = ((x⁻¹ : ℝ) : ℂ) * (((u + 1)⁻¹ : ℝ) : ℂ) := by
      push_cast; field_simp
    rw [this, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
      ofReal_inv_cpow hx, ofReal_inv_cpow (by positivity)]
  have hxb : (x : ℂ) ^ b ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; simp [hx0]
  have hub : ((u + 1 : ℝ) : ℂ) ^ b ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push_cast; simp [hu1]
  rw [e1, show 1 - b - 1 = -b by ring, Complex.cpow_neg]
  field_simp

theorem integrable_symmIntegrand {x : ℝ} (hx : 0 < x) {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Integrable (Function.uncurry (symmIntegrand x a b))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hI : ∀ c : ℂ, 0 < c.re →
      IntegrableOn (fun u : ℝ ↦ Real.exp (-x * u) * u ^ (c.re - 1)) (Ioi 0) := by
    intro c hc
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := c.re - 1) (b := x)
      (by linarith) one_pos hx
    refine this.congr_fun (fun u _ ↦ ?_) measurableSet_Ioi
    simp [mul_comm]
  have hprod := (hI a ha).mul_prod (hI b hb)
  rw [Measure.prod_restrict] at hprod ⊢
  refine hprod.mono' ?_ ((ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)).mpr
    (Eventually.of_forall fun q hq ↦ ?_))
  · refine Measurable.aestronglyMeasurable ?_
    unfold Function.uncurry symmIntegrand
    fun_prop
  · obtain ⟨hu, hw⟩ := hq
    have hu0 : (0 : ℝ) < q.1 := hu
    have hw0 : (0 : ℝ) < q.2 := hw
    simp only [Function.uncurry, symmIntegrand]
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hu0,
      Complex.norm_cpow_eq_rpow_re_of_pos hw0]
    have e : (-(x : ℂ) * ((q.1 : ℂ) + q.2 + q.1 * q.2)).re = -(x * (q.1 + q.2 + q.1 * q.2)) := by
      simp
    rw [e]
    simp only [Complex.sub_re, Complex.one_re]
    have : Real.exp (-(x * (q.1 + q.2 + q.1 * q.2))) ≤
        Real.exp (-x * q.1) * Real.exp (-x * q.2) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [mul_pos hx (mul_pos hu0 hw0)]
    have p1 : 0 ≤ q.1 ^ (a.re - 1) := (Real.rpow_pos_of_pos hu0 _).le
    have p2 : 0 ≤ q.2 ^ (b.re - 1) := (Real.rpow_pos_of_pos hw0 _).le
    calc Real.exp (-(x * (q.1 + q.2 + q.1 * q.2))) * q.1 ^ (a.re - 1) * q.2 ^ (b.re - 1)
        ≤ (Real.exp (-x * q.1) * Real.exp (-x * q.2)) * q.1 ^ (a.re - 1) * q.2 ^ (b.re - 1) := by
          gcongr
      _ = _ := by ring

/-- Fubini: $\int\int e^{-x(u+w+uw)}u^{a-1}w^{b-1}$ is symmetric in $(a,b)$. -/
theorem symmS_swap {x : ℝ} (hx : 0 < x) {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    ∫ u in Ioi (0 : ℝ), ∫ w in Ioi (0 : ℝ), symmIntegrand x a b u w =
      ∫ u in Ioi (0 : ℝ), ∫ w in Ioi (0 : ℝ), symmIntegrand x b a u w := by
  rw [integral_integral_swap (integrable_symmIntegrand hx ha hb)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun w _ ↦
    setIntegral_congr_fun measurableSet_Ioi (fun u _ ↦ ?_))
  simp only [symmIntegrand]
  rw [show ((u : ℂ) + w + u * w) = w + u + w * u by ring]
  ring

/-- The symmetry for $\omega_0$ at a positive real point: $\omega_0(x;1-b,a) = \omega_0(x;1-a,b)$
for $\operatorname{Re} a, \operatorname{Re} b > 0$ (Miyake pp. 279-280). -/
theorem omega0_symm_real {x : ℝ} (hx : 0 < x) {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    omega0 x (1 - b) a = omega0 x (1 - a) b := by
  have h1 := Gamma_mul_sigma_symm hx (a := a) hb
  have h2 := Gamma_mul_sigma_symm hx (a := b) ha
  rw [symmS_swap hx ha hb] at h1
  set S := ∫ u in Ioi (0 : ℝ), ∫ w in Ioi (0 : ℝ), symmIntegrand x b a u w
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hΓa : Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha
  have hΓb : Gamma b ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hb
  have e1 : sigma x (1 - b) a = ((x : ℂ) ^ b * S) * (Gamma b)⁻¹ := by
    rw [← h1]; field_simp
  have e2 : sigma x (1 - a) b = ((x : ℂ) ^ a * S) * (Gamma a)⁻¹ := by
    rw [← h2]; field_simp
  simp only [omega0]
  rw [e1, e2]
  ring

/-- Theorem 7.2.4 (1) at a positive real point, for $\operatorname{Re}\alpha < 1$, $\operatorname{Re}\beta > 0$. -/
theorem omega_symm_real {x : ℝ} (hx : 0 < x) {α β : ℂ} (hα : α.re < 1) (hβ : 0 < β.re) :
    omega x (1 - β) (1 - α) = omega x α β := by
  have hxr : 0 < (x : ℂ).re := by simpa using hx
  have ha : 0 < (1 - α).re := by simp; linarith
  rw [omega_eq_omega0 hxr ha, omega_eq_omega0 hxr hβ]
  have := omega0_symm_real hx ha hβ
  rw [sub_sub_cancel] at this
  exact this

theorem differentiable_omega_beta {z : ℂ} (hz : 0 < z.re) (α : ℂ) :
    Differentiable ℂ (fun β : ℂ ↦ omega z α β) := by
  have h := differentiableOn_omega.comp (f := fun β : ℂ ↦ (z, α, β))
    (by fun_prop : Differentiable ℂ _).differentiableOn (s := Set.univ) (fun β _ ↦ hz)
  exact differentiableOn_univ.mp h

theorem differentiable_omega_alpha {z : ℂ} (hz : 0 < z.re) (β : ℂ) :
    Differentiable ℂ (fun α : ℂ ↦ omega z α β) := by
  have h := differentiableOn_omega.comp (f := fun α : ℂ ↦ (z, α, β))
    (by fun_prop : Differentiable ℂ _).differentiableOn (s := Set.univ) (fun α _ ↦ hz)
  exact differentiableOn_univ.mp h

theorem differentiableOn_omega_z (α β : ℂ) :
    DifferentiableOn ℂ (fun w : ℂ ↦ omega w α β) {w | 0 < w.re} :=
  differentiableOn_omega.comp (f := fun w : ℂ ↦ (w, α, β))
    (by fun_prop : Differentiable ℂ _).differentiableOn (fun _ hw ↦ hw)

/-- Identity theorem for entire functions agreeing near a point. -/
theorem eq_of_eventuallyEq_entire {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {c : ℂ} (h : f =ᶠ[𝓝 c] g) (z : ℂ) : f z = g z :=
  AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (U := Set.univ)
    (fun w _ ↦ hf.analyticAt w) (fun w _ ↦ hg.analyticAt w) isPreconnected_univ
    (Set.mem_univ c) h (Set.mem_univ z)

/-- Extension of the symmetry in $z$ from $z > 0$ to $\operatorname{Re} z > 0$. -/
theorem omega_symm_pos_re {z α β : ℂ} (hz : 0 < z.re) (hα : α.re < 1) (hβ : 0 < β.re) :
    omega z (1 - β) (1 - α) = omega z α β := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf := (differentiableOn_omega_z (1 - β) (1 - α)).analyticOnNhd hU
  have hg := (differentiableOn_omega_z α β).analyticOnNhd hU
  refine hf.eqOn_of_preconnected_of_frequently_eq hg (convex_halfSpace_re_gt 0).isPreconnected
    (z₀ := 1) (by simp) ?_ hz
  rw [Filter.frequently_iff]
  intro V hV
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhdsWithin_iff.mp hV
  refine ⟨((1 + ε / 2 : ℝ) : ℂ), hεV ⟨?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    have : (((1 + ε / 2 : ℝ) : ℂ) - 1) = ((ε / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  · intro h
    have h' : (((1 + ε / 2 : ℝ) : ℂ)) = 1 := h
    have := congrArg Complex.re h'
    simp at this
    linarith
  · exact omega_symm_real (x := 1 + ε / 2) (by positivity) hα hβ

/-- Extension of the symmetry to all $\beta \in \mathbb C$ (for $\operatorname{Re}\alpha < 1$). -/
theorem omega_symm_re_lt {z : ℂ} (hz : 0 < z.re) {α : ℂ} (hα : α.re < 1) (β : ℂ) :
    omega z (1 - β) (1 - α) = omega z α β := by
  refine eq_of_eventuallyEq_entire (c := 1)
    ((differentiable_omega_alpha hz (1 - α)).comp (differentiable_const _ |>.sub differentiable_id))
    (differentiable_omega_beta hz α) ?_ β
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hU.mem_nhds (by simp : (1 : ℂ) ∈ {w : ℂ | 0 < w.re})] with w hw
  exact omega_symm_pos_re hz hα hw

/-- **Miyake, Theorem 7.2.4 (1).** $\omega(z;1-\beta,1-\alpha) = \omega(z;\alpha,\beta)$ on
$\mathbf H' \times \mathbb C \times \mathbb C$. -/
@[kb "miyake1989" "Theorem 7.2.4 (1), p. 279"]
theorem omega_symm {z : ℂ} (hz : 0 < z.re) (α β : ℂ) : omega z (1 - β) (1 - α) = omega z α β := by
  refine eq_of_eventuallyEq_entire (c := 0)
    (f := fun α' ↦ omega z (1 - β) (1 - α'))
    (g := fun α' ↦ omega z α' β)
    ((differentiable_omega_beta hz (1 - β)).comp (differentiable_const _ |>.sub differentiable_id))
    (differentiable_omega_alpha hz β) ?_ α
  have hU : IsOpen {w : ℂ | w.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  filter_upwards [hU.mem_nhds (by simp : (0 : ℂ) ∈ {w : ℂ | w.re < 1})] with w hw
  exact omega_symm_re_lt hz hw β

/-- $w^{-\beta} = w \cdot w^{-(\beta+1)}$ for $w \ne 0$. -/
theorem cpow_neg_eq_mul {w : ℂ} (hw : w ≠ 0) (β : ℂ) : w ^ (-β) = w * w ^ (-(β + 1)) := by
  conv_lhs => rw [show -β = -(β + 1) + 1 by ring, Complex.cpow_add _ _ hw, Complex.cpow_one]
  ring

/-- The derivative formula for $\operatorname{Re}\beta > 0$. -/
theorem hasDerivAt_exp_omega_pos {z : ℂ} (hz : 0 < z.re) (α : ℂ) {β : ℂ} (hβ : 0 < β.re) :
    HasDerivAt (fun w ↦ cexp (-w) * w ^ (-β) * omega w α β)
      (-(cexp (-z) * z ^ (-β) * omega z (α + 1) β)) z := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hΓ : Gamma β ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hβ
  have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz
  have hs := hasDerivAt_sigma_z hz hβ (α := α)
  have hs2 : HasDerivAt (fun w ↦ (Gamma β)⁻¹ * (cexp (-w) * sigma w α β))
      ((Gamma β)⁻¹ * (cexp (-z) * -1 * sigma z α β + cexp (-z) * (-sigma z α (β + 1)))) z :=
    (((hasDerivAt_id z).neg.cexp).mul hs).const_mul _
  have heq : (fun w ↦ cexp (-w) * w ^ (-β) * omega w α β) =ᶠ[𝓝 z]
      fun w ↦ (Gamma β)⁻¹ * (cexp (-w) * sigma w α β) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hw0 : w ≠ 0 := fun h ↦ by simp [h] at hw
    have hw' : 0 < w.re := hw
    have hwβ : w ^ β ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; simp [hw0]
    rw [omega_eq_omega0 hw' hβ, Complex.cpow_neg]
    field_simp
  refine (hs2.congr_of_eventuallyEq heq).congr_deriv ?_
  have hzβ : z ^ β ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; simp [hz0]
  rw [omega_eq_omega0 hz (by simpa using hβ : 0 < β.re), Complex.cpow_neg,
    ← sigma_add_sigma_succ hz hβ]
  field_simp
  ring

/-- The case $n = 1$ of (7.2.36): $\frac{d}{dz}\big(e^{-z}z^{-\beta}\omega(z;\alpha,\beta)\big) =
-e^{-z}z^{-\beta}\omega(z;\alpha+1,\beta)$ on $\mathbf H'$, for all $\alpha, \beta$. -/
theorem hasDerivAt_exp_omega {z : ℂ} (hz : 0 < z.re) (α β : ℂ) :
    HasDerivAt (fun w ↦ cexp (-w) * w ^ (-β) * omega w α β)
      (-(cexp (-z) * z ^ (-β) * omega z (α + 1) β)) z := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have key : ∀ n : ℕ, ∀ (α β : ℂ), -(n : ℝ) < β.re →
      HasDerivAt (fun w ↦ cexp (-w) * w ^ (-β) * omega w α β)
        (-(cexp (-z) * z ^ (-β) * omega z (α + 1) β)) z := by
    intro n
    induction n with
    | zero => intro α β hβ; exact hasDerivAt_exp_omega_pos hz α (by simpa using hβ)
    | succ n ih =>
      intro α β hβ
      have hβ1 : -(n : ℝ) < (β + 1).re := by simp; push_cast at hβ; linarith
      have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz
      set G : ℂ → ℂ → ℂ := fun a w ↦ cexp (-w) * w ^ (-(β + 1)) * omega w a (β + 1) with hG
      have hG' : ∀ a, HasDerivAt (G a) (-G (a + 1) z) z := fun a ↦ by
        have := ih a (β + 1) hβ1
        simpa [hG] using this
      have h1 : HasDerivAt (fun w ↦ w * G α w + (1 - α) * G (α - 1) w)
          (G α z + z * (-G (α + 1) z) + (1 - α) * (-G α z)) z := by
        have := ((hasDerivAt_id' z).mul (hG' α)).add ((hG' (α - 1)).const_mul (1 - α))
        exact this.congr_deriv (by simp)
      have heq : (fun w ↦ cexp (-w) * w ^ (-β) * omega w α β) =ᶠ[𝓝 z]
          fun w ↦ w * G α w + (1 - α) * G (α - 1) w := by
        filter_upwards [hU.mem_nhds hz] with w hw
        have hw0 : w ≠ 0 := fun h ↦ by simp [h] at hw
        have hw' : 0 < w.re := hw
        simp only [hG]
        rw [omega_rec hw' α β, cpow_neg_eq_mul hw0 β]
        field_simp
      refine (h1.congr_of_eventuallyEq heq).congr_deriv ?_
      have e1 := omega_rec hz (α + 1) β
      rw [e1, cpow_neg_eq_mul hz0 β]
      simp only [hG, add_sub_cancel_right]
      field_simp
      ring
  exact key (⌊-β.re⌋₊ + 1) α β (neg_floor_lt β)

/-- **Miyake, Theorem 7.2.4 (2).** For $n \in \mathbb N$ and $z \in \mathbf H'$,
$\omega(z;\alpha,\beta) = (-1)^n e^{z}z^{\beta}\frac{\partial^n}{\partial z^n}
\big(e^{-z}z^{-\beta}\omega(z;\alpha-n,\beta)\big)$. -/
@[kb "miyake1989" "Theorem 7.2.4 (2), p. 279"]
theorem omega_eq_iteratedDeriv (n : ℕ) {z : ℂ} (hz : 0 < z.re) (α β : ℂ) :
    omega z α β = (-1) ^ n * cexp z * z ^ β *
      iteratedDeriv n (fun w ↦ cexp (-w) * w ^ (-β) * omega w (α - n) β) z := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have key : ∀ n : ℕ, ∀ (a : ℂ) (z : ℂ), 0 < z.re →
      iteratedDeriv n (fun w ↦ cexp (-w) * w ^ (-β) * omega w a β) z =
        (-1) ^ n * (cexp (-z) * z ^ (-β) * omega z (a + n) β) := by
    intro n
    induction n with
    | zero => intro a z hz; simp
    | succ n ih =>
      intro a z hz
      rw [iteratedDeriv_succ']
      have hev : deriv (fun w ↦ cexp (-w) * w ^ (-β) * omega w a β) =ᶠ[𝓝 z]
          fun w ↦ -(cexp (-w) * w ^ (-β) * omega w (a + 1) β) := by
        filter_upwards [hU.mem_nhds hz] with w hw
        exact (hasDerivAt_exp_omega hw a β).deriv
      rw [hev.iteratedDeriv_eq, iteratedDeriv_fun_neg, ih (a + 1) z hz]
      push_cast
      rw [show a + 1 + n = a + (n + 1) by ring]
      ring
  rw [key n _ z hz, sub_add_cancel]
  have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz
  have h1 : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by rw [← mul_pow]; simp
  have h2 : cexp z * cexp (-z) = 1 := by rw [← Complex.exp_add]; simp
  have h3 : z ^ β * z ^ (-β) = 1 := by rw [← Complex.cpow_add _ _ hz0]; simp
  calc omega z α β = ((-1 : ℂ) ^ n * (-1) ^ n) * (cexp z * cexp (-z)) * (z ^ β * z ^ (-β)) *
        omega z α β := by rw [h1, h2, h3]; ring
    _ = _ := by ring

/-- **Miyake, Lemma 7.2.6.** $\omega(z;\alpha,0) = 1$ for $(z,\alpha) \in \mathbf H' \times \mathbb C$. -/
@[kb "miyake1989" "Lemma 7.2.6, p. 281"]
theorem omega_zero {z : ℂ} (hz : 0 < z.re) (α : ℂ) : omega z α 0 = 1 := by
  have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz
  rw [omega_rec hz, zero_add, omega_eq_omega0 hz (by simp), omega_eq_omega0 hz (by simp)]
  simp only [Complex.Gamma_one, inv_one, one_mul, Complex.cpow_one]
  have h := mul_sigma_one hz α
  have : (1 - α) * z⁻¹ * (z * sigma z (α - 1) 1) = (1 - α) * sigma z (α - 1) 1 := by
    field_simp
  rw [this, h]
  ring

/-! ### The bound (Theorem 7.2.7) -/

theorem rpow_succ_le {A u : ℝ} (hA : 0 ≤ A) (hu : 0 < u) : (u + 1) ^ A ≤ 2 ^ A * (1 + u ^ A) := by
  have h2 : (0 : ℝ) ≤ 2 ^ A := by positivity
  have hp : 0 ≤ u ^ A := (Real.rpow_pos_of_pos hu _).le
  rcases le_total u 1 with h | h
  · calc (u + 1) ^ A ≤ 2 ^ A := Real.rpow_le_rpow (by linarith) (by linarith) hA
      _ = 2 ^ A * 1 := (mul_one _).symm
      _ ≤ 2 ^ A * (1 + u ^ A) := mul_le_mul_of_nonneg_left (by linarith) h2
  · calc (u + 1) ^ A ≤ (2 * u) ^ A := Real.rpow_le_rpow (by linarith) (by linarith) hA
      _ = 2 ^ A * u ^ A := Real.mul_rpow (by norm_num) hu.le
      _ ≤ 2 ^ A * (1 + u ^ A) := mul_le_mul_of_nonneg_left (by linarith) h2

theorem rpow_neg_le_one_add {y A B : ℝ} (hy : 0 < y) (hA : 0 ≤ A) (hAB : A ≤ B) :
    y ^ (-A) ≤ 1 + y ^ (-B) := by
  have hp : 0 ≤ y ^ (-B) := (Real.rpow_pos_of_pos hy _).le
  rcases le_total y 1 with h | h
  · have : y ^ (-A) ≤ y ^ (-B) := Real.rpow_le_rpow_of_exponent_ge hy h (by linarith)
    linarith
  · have : y ^ (-A) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
    linarith

theorem integrableOn_rpow_mul_exp {y : ℝ} (hy : 0 < y) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ ↦ u ^ (c - 1) * Real.exp (-(y * u))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := c - 1) (b := y)
    (by linarith) one_pos hy
  refine this.congr_fun (fun u _ ↦ ?_) measurableSet_Ioi
  simp [neg_mul]

/-- A bound for $|\sigma(y;\alpha,\beta)|$ by Gamma values (Miyake p. 281). -/
theorem norm_sigma_le {y : ℝ} (hy : 0 < y) {α β : ℂ} (hβ : 0 < β.re) {A : ℝ} (hA : 0 ≤ A)
    (hα : α.re - 1 ≤ A) :
    ‖sigma y α β‖ ≤ 2 ^ A * (Real.Gamma β.re * y ^ (-β.re) +
      Real.Gamma (β.re + A) * y ^ (-(β.re + A))) := by
  have hb1 := integrableOn_rpow_mul_exp hy hβ
  have hb2 := integrableOn_rpow_mul_exp hy (by linarith : 0 < β.re + A)
  have hint : IntegrableOn (fun u : ℝ ↦ 2 ^ A * (u ^ (β.re - 1) * Real.exp (-(y * u)) +
      u ^ (β.re + A - 1) * Real.exp (-(y * u)))) (Ioi 0) := (hb1.add hb2).const_mul _
  have hI1 := Real.integral_rpow_mul_exp_neg_mul_Ioi hβ hy
  have hI2 := Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : 0 < β.re + A) hy
  have hy1 : ∀ c : ℝ, (1 / y) ^ c = y ^ (-c) := fun c ↦ by
    rw [one_div, Real.inv_rpow hy.le, Real.rpow_neg hy.le]
  calc ‖sigma y α β‖ ≤ ∫ u in Ioi (0 : ℝ), ‖sigmaIntegrand y α β u‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioi (0 : ℝ), 2 ^ A * (u ^ (β.re - 1) * Real.exp (-(y * u)) +
        u ^ (β.re + A - 1) * Real.exp (-(y * u))) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun u ↦ norm_nonneg _) hint ?_
        refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu ↦ ?_)
        have hu0 : (0 : ℝ) < u := hu
        have hn : ‖sigmaIntegrand y α β u‖ =
            Real.exp (-y * u) * (u + 1) ^ (α.re - 1) * u ^ (β.re - 1) := by
          rw [norm_sigmaIntegrand hu0]; simp
        beta_reduce
        rw [hn]
        have e1 : (u + 1) ^ (α.re - 1) ≤ 2 ^ A * (1 + u ^ A) :=
          (Real.rpow_le_rpow_of_exponent_le (by linarith) hα).trans (rpow_succ_le hA hu0)
        have e2 : u ^ (β.re + A - 1) = u ^ (β.re - 1) * u ^ A := by
          rw [← Real.rpow_add hu0]; ring_nf
        have p1 : 0 ≤ Real.exp (-y * u) := (Real.exp_pos _).le
        have p2 : 0 ≤ u ^ (β.re - 1) := (Real.rpow_pos_of_pos hu0 _).le
        have e3 : Real.exp (-y * u) = Real.exp (-(y * u)) := by ring_nf
        rw [e2, ← e3]
        calc Real.exp (-y * u) * (u + 1) ^ (α.re - 1) * u ^ (β.re - 1)
            ≤ Real.exp (-y * u) * (2 ^ A * (1 + u ^ A)) * u ^ (β.re - 1) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e1 p1) p2
          _ = _ := by ring
    _ = 2 ^ A * ((1 / y) ^ β.re * Real.Gamma β.re + (1 / y) ^ (β.re + A) * Real.Gamma (β.re + A)) := by
        rw [integral_const_mul, integral_add hb1 hb2, hI1, hI2]
    _ = _ := by rw [hy1, hy1]; ring

/-- Continuity of the constant in the bound. -/
theorem continuousAt_boundConst {A : ℝ} (hA : 0 ≤ A) {p : ℂ × ℂ} (hp : 0 < p.2.re) :
    ContinuousAt (fun p : ℂ × ℂ ↦ ‖Gamma p.2‖⁻¹ * 2 ^ A *
      (Real.Gamma p.2.re + Real.Gamma (p.2.re + A))) p := by
  have hne : ∀ s : ℝ, 0 < s → ∀ m : ℕ, s ≠ -m := fun s hs m h ↦ by
    have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hG : ContinuousAt (fun p : ℂ × ℂ ↦ Gamma p.2) p :=
    (Complex.continuousAt_Gamma _ (fun m h ↦ by
      have := congrArg Complex.re h
      have h2 := Nat.cast_nonneg (α := ℝ) m
      simp at this; linarith)).comp (f := fun p : ℂ × ℂ ↦ p.2) continuous_snd.continuousAt
  have hnz : ‖Gamma p.2‖ ≠ 0 := norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hp)
  have hre : ContinuousAt (fun p : ℂ × ℂ ↦ p.2.re) p :=
    (Complex.continuous_re.comp continuous_snd).continuousAt
  have hR1 : ContinuousAt (fun p : ℂ × ℂ ↦ Real.Gamma p.2.re) p :=
    (Real.differentiableAt_Gamma (hne _ hp)).continuousAt.comp (f := fun p : ℂ × ℂ ↦ p.2.re) hre
  have hR2 : ContinuousAt (fun p : ℂ × ℂ ↦ Real.Gamma (p.2.re + A)) p :=
    (Real.differentiableAt_Gamma (hne _ (by linarith) : ∀ m : ℕ, p.2.re + A ≠ -m)).continuousAt.comp
      (f := fun p : ℂ × ℂ ↦ p.2.re + A) (hre.add continuousAt_const)
  exact ((hG.norm.inv₀ hnz).mul continuousAt_const).mul (hR1.add hR2)

/-- **Theorem 7.2.7** for $\operatorname{Re}\beta > 0$ on $T$ (Miyake p. 281). -/
theorem omega_bound_pos {T : Set (ℂ × ℂ)} (hT : IsCompact T) (hTβ : ∀ p ∈ T, 0 < p.2.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, 0 < y → ∀ p ∈ T,
      ‖omega y p.1 p.2‖ ≤ C * (1 + y ^ (-B)) := by
  obtain ⟨M, hM⟩ := (hT.image (Complex.continuous_re.comp continuous_fst)).bddAbove
  set A : ℝ := max 0 (M - 1) with hAdef
  have hA : 0 ≤ A := le_max_left _ _
  have hK : ContinuousOn (fun p : ℂ × ℂ ↦ ‖Gamma p.2‖⁻¹ * 2 ^ A *
      (Real.Gamma p.2.re + Real.Gamma (p.2.re + A))) T := fun p hp ↦
    (continuousAt_boundConst hA (hTβ p hp)).continuousWithinAt
  obtain ⟨C0, hC0⟩ := hT.exists_bound_of_continuousOn hK
  refine ⟨max C0 0, le_max_right _ _, A, hA, fun y hy p hp ↦ ?_⟩
  have hβ := hTβ p hp
  have hyr : 0 < (y : ℂ).re := by simpa using hy
  have hαA : p.1.re - 1 ≤ A := by
    have : p.1.re ≤ M := hM ⟨p, hp, rfl⟩
    have := le_max_right 0 (M - 1)
    linarith
  rw [omega_eq_omega0 hyr hβ, norm_mul, norm_mul, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hσ := norm_sigma_le hy hβ hA hαA
  have hΓ : 0 < ‖Gamma p.2‖ := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hβ)
  have hg1 : 0 < Real.Gamma p.2.re := Real.Gamma_pos_of_pos hβ
  have hg2 : 0 < Real.Gamma (p.2.re + A) := Real.Gamma_pos_of_pos (by linarith)
  have hyb : 0 < y ^ p.2.re := Real.rpow_pos_of_pos hy _
  have hKp : ‖Gamma p.2‖⁻¹ * 2 ^ A * (Real.Gamma p.2.re + Real.Gamma (p.2.re + A)) ≤ max C0 0 :=
    (le_abs_self _).trans ((by simpa [Real.norm_eq_abs] using hC0 p hp : _ ≤ C0).trans (le_max_left _ _))
  have e1 : y ^ p.2.re * y ^ (-p.2.re) = 1 := by
    rw [← Real.rpow_add hy]; simp
  have e2 : y ^ p.2.re * y ^ (-(p.2.re + A)) = y ^ (-A) := by
    rw [← Real.rpow_add hy]; ring_nf
  have hyA : 0 ≤ y ^ (-A) := (Real.rpow_pos_of_pos hy _).le
  have h2A : (0 : ℝ) < 2 ^ A := by positivity
  calc ‖Gamma p.2‖⁻¹ * y ^ p.2.re * ‖sigma y p.1 p.2‖
      ≤ ‖Gamma p.2‖⁻¹ * y ^ p.2.re * (2 ^ A * (Real.Gamma p.2.re * y ^ (-p.2.re) +
        Real.Gamma (p.2.re + A) * y ^ (-(p.2.re + A)))) :=
        mul_le_mul_of_nonneg_left hσ (by positivity)
    _ = ‖Gamma p.2‖⁻¹ * 2 ^ A * (Real.Gamma p.2.re * (y ^ p.2.re * y ^ (-p.2.re)) +
        Real.Gamma (p.2.re + A) * (y ^ p.2.re * y ^ (-(p.2.re + A)))) := by ring
    _ = ‖Gamma p.2‖⁻¹ * 2 ^ A * (Real.Gamma p.2.re + Real.Gamma (p.2.re + A) * y ^ (-A)) := by
        rw [e1, e2]; ring
    _ ≤ ‖Gamma p.2‖⁻¹ * 2 ^ A * ((Real.Gamma p.2.re + Real.Gamma (p.2.re + A)) * (1 + y ^ (-A))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith [mul_nonneg hg1.le hyA]
    _ = (‖Gamma p.2‖⁻¹ * 2 ^ A * (Real.Gamma p.2.re + Real.Gamma (p.2.re + A))) * (1 + y ^ (-A)) := by
        ring
    _ ≤ max C0 0 * (1 + y ^ (-A)) := mul_le_mul_of_nonneg_right hKp (by linarith)

/-- **Theorem 7.2.7** for $\operatorname{Re}\beta > -m$ on $T$, by induction on $m$ via (7.2.39). -/
theorem omega_bound_aux (m : ℕ) : ∀ {T : Set (ℂ × ℂ)}, IsCompact T → (∀ p ∈ T, -(m : ℝ) < p.2.re) →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, 0 < y → ∀ p ∈ T,
      ‖omega y p.1 p.2‖ ≤ C * (1 + y ^ (-B)) := by
  induction m with
  | zero => intro T hT h; exact omega_bound_pos hT (by simpa using h)
  | succ m ih =>
    intro T hT hTβ
    have hc1 : Continuous (fun p : ℂ × ℂ ↦ (p.1, p.2 + 1)) := by fun_prop
    have hc2 : Continuous (fun p : ℂ × ℂ ↦ (p.1 - 1, p.2 + 1)) := by fun_prop
    obtain ⟨C₁, hC₁, B₁, hB₁, h₁⟩ := ih (hT.image hc1) (by
      rintro _ ⟨p, hp, rfl⟩
      have := hTβ p hp
      simp only [Complex.add_re, Complex.one_re]
      push_cast at this; linarith)
    obtain ⟨C₂, hC₂, B₂, hB₂, h₂⟩ := ih (hT.image hc2) (by
      rintro _ ⟨p, hp, rfl⟩
      have := hTβ p hp
      simp only [Complex.add_re, Complex.one_re]
      push_cast at this; linarith)
    obtain ⟨D, hD⟩ := hT.exists_bound_of_continuousOn
      (f := fun p : ℂ × ℂ ↦ 1 - p.1) (by fun_prop : Continuous _).continuousOn
    set B' : ℝ := max B₁ (B₂ + 1) with hB'
    have hB1 : B₁ ≤ B' := le_max_left _ _
    have hB2 : B₂ + 1 ≤ B' := le_max_right _ _
    have hD0 : 0 ≤ max D 0 := le_max_right _ _
    refine ⟨2 * C₁ + 2 * (max D 0 * C₂), by positivity, B', by linarith [le_max_left B₁ (B₂ + 1)], ?_⟩
    intro y hy p hp
    have hyr : 0 < (y : ℂ).re := by simpa using hy
    have h1 : ‖omega y p.1 (p.2 + 1)‖ ≤ C₁ * (1 + y ^ (-B₁)) := h₁ y hy (p.1, p.2 + 1) ⟨p, hp, rfl⟩
    have h2 : ‖omega y (p.1 - 1) (p.2 + 1)‖ ≤ C₂ * (1 + y ^ (-B₂)) := h₂ y hy (p.1 - 1, p.2 + 1) ⟨p, hp, rfl⟩
    have hDp : ‖1 - p.1‖ ≤ max D 0 := (hD p hp).trans (le_max_left _ _)
    have hyn : ‖(y : ℂ)⁻¹‖ = y⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
    have ha : y ^ (-B₁) ≤ 1 + y ^ (-B') := rpow_neg_le_one_add hy hB₁ hB1
    have hb : y ^ (-(B₂ + 1)) ≤ 1 + y ^ (-B') := rpow_neg_le_one_add hy (by linarith) hB2
    have hc : y ^ (-(1 : ℝ)) ≤ 1 + y ^ (-B') := rpow_neg_le_one_add hy zero_le_one (by linarith)
    have hyi : y⁻¹ = y ^ (-(1 : ℝ)) := (Real.rpow_neg_one y).symm
    have hyi2 : y⁻¹ * y ^ (-B₂) = y ^ (-(B₂ + 1)) := by
      rw [hyi, ← Real.rpow_add hy]; ring_nf
    have ht : 0 ≤ y ^ (-B') := (Real.rpow_pos_of_pos hy _).le
    have hyi0 : 0 ≤ y⁻¹ := by positivity
    rw [omega_rec hyr]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hyn]
    calc ‖omega y p.1 (p.2 + 1)‖ + ‖1 - p.1‖ * y⁻¹ * ‖omega y (p.1 - 1) (p.2 + 1)‖
        ≤ C₁ * (1 + y ^ (-B₁)) + max D 0 * y⁻¹ * (C₂ * (1 + y ^ (-B₂))) := by
          refine add_le_add h1 (mul_le_mul (mul_le_mul_of_nonneg_right hDp hyi0) h2
            (norm_nonneg _) (by positivity))
      _ = C₁ * (1 + y ^ (-B₁)) + max D 0 * C₂ * (y⁻¹ + y ^ (-(B₂ + 1))) := by
          rw [← hyi2]; ring
      _ ≤ C₁ * (1 + (1 + y ^ (-B'))) + max D 0 * C₂ * ((1 + y ^ (-B')) + (1 + y ^ (-B'))) := by
          refine add_le_add (mul_le_mul_of_nonneg_left (by linarith) hC₁)
            (mul_le_mul_of_nonneg_left ?_ (by positivity))
          rw [hyi]; linarith
      _ ≤ _ := by nlinarith [mul_nonneg hC₁ ht, mul_nonneg (mul_nonneg hD0 hC₂) ht]

/-- **Miyake, Theorem 7.2.7.** For every compact $T \subset \mathbb C \times \mathbb C$ there are $A, B > 0$ with
$|\omega(y;\alpha,\beta)| \le A(1 + y^{-B})$ for all $y > 0$ and $(\alpha,\beta) \in T$. -/
@[kb "miyake1989" "Theorem 7.2.7, p. 281"]
theorem omega_bound {T : Set (ℂ × ℂ)} (hT : IsCompact T) :
    ∃ A > (0 : ℝ), ∃ B > (0 : ℝ), ∀ y : ℝ, 0 < y → ∀ p ∈ T,
      ‖omega y p.1 p.2‖ ≤ A * (1 + y ^ (-B)) := by
  obtain ⟨L, hL⟩ := (hT.image (Complex.continuous_re.comp continuous_snd)).bddBelow
  obtain ⟨m, hm⟩ := exists_nat_gt (-L)
  obtain ⟨C, hC, B, hB, h⟩ := omega_bound_aux m hT (fun p hp ↦ by
    have : L ≤ p.2.re := hL ⟨p, hp, rfl⟩
    linarith)
  refine ⟨2 * C + 1, by positivity, B + 1, by linarith, fun y hy p hp ↦ ?_⟩
  have h1 := h y hy p hp
  have h2 : y ^ (-B) ≤ 1 + y ^ (-(B + 1)) := rpow_neg_le_one_add hy hB (by linarith)
  have ht : 0 ≤ y ^ (-(B + 1)) := (Real.rpow_pos_of_pos hy _).le
  nlinarith [mul_nonneg hC ht]

end ModularFormsKB.Miyake.HeckeTrick
