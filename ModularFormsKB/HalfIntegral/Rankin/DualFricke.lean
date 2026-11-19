/-
# The dual Eisenstein series under the Fricke involution

Loose end LE-MF-0256.

The dual Eisenstein series $\check E(z,s) = y^s\sum_{(m,n)}G(\omega,-m)(mz+n)^\lambda|mz+n|^{-\lambda-2s}$
(`eisensteinDual`) is the Eisenstein series of $\Gamma_0(L)$ "at the cusp $0$". Under $W_L z = -1/(Lz)$ it becomes a
series at $\infty$ with the Gauss sums on the second coordinate,
$$\check E(W_Lz,s) = L^s\Big(\frac{|z|}{z}\Big)^\lambda E^G(z,s),\qquad
  E^G(z,s) = y^s\sum_{(c,d)}G(\omega,d)\,(Lcz+d)^\lambda|Lcz+d|^{-\lambda-2s}$$
(`eisensteinDual_fricke`; the reindexing $(m,n)\mapsto(n,-m)$, no convergence needed). With the Gauss sum of the
imprimitive character (`GaussImprimitive.gaussAt_eq_sum_primitive`), for $\operatorname{Re}s > 1$, $f$ the conductor,
$\omega^*$ the primitive character and $g_0 = L/f$,
$$E^G(z,s) = \tau(\omega^*)\sum_{e\mid g_0}e^{1-2s}(g_0/e)^{-s}\mu(g_0/e)\,\omega^*(g_0/e)\,
  E_{f,\overline{\omega^*}}\big((g_0/e)z,s\big)$$
(`eisensteinGauss_eq_sum`), $E_{f,\cdot}$ = `eisensteinLattice f λ`: a finite combination of Eisenstein series at
$\infty$ of level $f$ with the primitive character $\overline{\omega^*}$, evaluated at $(g_0/e)z$.

**Index shift.** Matrix entries are 0-based.
-/
import ModularFormsKB.HalfIntegral.Rankin.GaussImprimitive
import ModularFormsKB.HalfIntegral.Rankin.DualReps
import TauCeti.NumberTheory.ModularForms.Fricke.Operator

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup MeasureTheory Set
open scoped Real

local notation "ℍ" => UpperHalfPlane

namespace DualFricke

/-- **The Eisenstein series at $\infty$ with Gauss-sum coefficients**
$E^G(z,s) = y^s\sum_{(c,d)\in\mathbb Z^2}G(\omega,d)\,(Lcz+d)^\lambda|Lcz+d|^{-\lambda-2s}$.
**Restriction:** the lattice sum converges absolutely for $\operatorname{Re} s > 1$ (the terms have size $|Lcz +
d|^{-2\operatorname{Re} s}$ and the Gauss-sum coefficients are bounded). Elsewhere the value is $0$ by Lean's
convention for a non-summable `∑'`, not an analytic continuation or the intended value. -/
noncomputable def eisensteinGauss (L lam : ℕ) (ω : DirichletCharacter ℂ L) (z : ℍ) (s : ℂ) : ℂ :=
  ((z.im : ℂ) ^ s) * ∑' p : ℤ × ℤ, gaussAt L ω p.2 * eisTerm lam s ((L : ℂ) * p.1 * z + p.2)

/-- The point $rz$ of $\mathbb H$ for a positive integer $r$ (the action of the positive reals; $r = 0$ is replaced
by $1$). -/
noncomputable def scalePt (r : ℕ) (z : ℍ) : ℍ :=
  (⟨((max r 1 : ℕ) : ℝ), by positivity⟩ : {x : ℝ // 0 < x}) • z

lemma coe_scalePt {r : ℕ} (hr : 1 ≤ r) (z : ℍ) : ((scalePt r z : ℍ) : ℂ) = (r : ℂ) * z := by
  unfold scalePt
  rw [UpperHalfPlane.coe_pos_real_smul]
  simp [Nat.max_eq_left hr]

lemma summable_norm_eisTerm {L : ℕ} (hL : 1 ≤ L) (lam : ℕ) (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : ℤ × ℤ ↦ ‖eisTerm lam s ((L : ℂ) * p.1 * z + p.2)‖) := by
  have hk : 2 < 2 * s.re := by linarith
  let e : ℤ × ℤ → (Fin 2 → ℤ) := fun p ↦ ![(L : ℤ) * p.1, p.2]
  have he : Function.Injective e := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    simp [e] at h0 h1
    have hL0 : (L : ℤ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
    rcases h0 with h0 | h0
    · simp [h0, h1]
    · exact absurd h0 (by omega)
  have hS := ((EisensteinSeries.summable_one_div_norm_rpow hk).comp_injective he).mul_left
    ((EisensteinSeries.r z) ^ (-(2 * s.re)))
  refine Summable.of_norm_bounded hS fun p ↦ ?_
  have h1 := RankinUnfold.norm_eisTerm_le lam hs ((L : ℂ) * p.1 * z + p.2)
  have h2 := EisensteinSeries.summand_bound z (k := 2 * s.re) (by linarith) (e p)
  have h3 : ((e p 0 : ℤ) : ℂ) * z + ((e p 1 : ℤ) : ℂ) = (L : ℂ) * p.1 * z + p.2 := by simp [e]
  rw [h3] at h2
  rw [norm_norm]
  simp only [Function.comp_apply]
  exact h1.trans h2

lemma eisTerm_natCast_mul {lam : ℕ} (hlam : 1 ≤ lam) (s : ℂ) {e : ℕ} (he : 1 ≤ e) (v : ℂ) :
    eisTerm lam s ((e : ℂ) * v) = (e : ℂ) ^ (-2 * s) * eisTerm lam s v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [eisTerm, zero_pow (show lam ≠ 0 by omega)]
  have he0 : (e : ℂ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have ha : 0 < ‖v‖ := norm_pos_iff.2 hv
  unfold eisTerm
  rw [norm_mul, Complex.norm_natCast, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg heR.le ha.le,
    show (-(lam : ℂ) - 2 * s) = -(lam : ℂ) + (-2 * s) by ring, Complex.cpow_add _ _ (by exact_mod_cast heR.ne'),
    Complex.cpow_neg, Complex.cpow_natCast]
  have h1 : ((e : ℝ) : ℂ) = (e : ℂ) := by simp
  rw [h1, mul_pow]
  have h2 : (e : ℂ) ^ lam ≠ 0 := pow_ne_zero _ he0
  field_simp

lemma tsum_dvd_reindex {L : ℕ} (lam : ℕ) (s : ℂ) (z : ℍ) {f : ℕ} (ψ : DirichletCharacter ℂ f) {e : ℕ}
    (he : 1 ≤ e) :
    ∑' p : ℤ × ℤ, (if (e : ℤ) ∣ p.2 then ψ ((p.2 / e : ℤ) : ZMod f) * eisTerm lam s ((L : ℂ) * p.1 * z + p.2) else 0) =
      ∑' q : ℤ × ℤ, ψ (q.2 : ZMod f) * eisTerm lam s ((L : ℂ) * q.1 * z + (e : ℤ) * q.2) := by
  have he0 : (e : ℤ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
  have hinj : Function.Injective (fun q : ℤ × ℤ ↦ (q.1, (e : ℤ) * q.2)) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have := mul_left_cancel₀ he0 h2
    simp [h1, this]
  rw [← hinj.tsum_eq]
  · refine tsum_congr fun q ↦ ?_
    simp [Int.mul_ediv_cancel_left _ he0]
  · intro p hp
    by_cases h : (e : ℤ) ∣ p.2
    · obtain ⟨d, hd⟩ := h
      exact ⟨(p.1, d), Prod.ext rfl hd.symm⟩
    · exact absurd (by simp [h]) hp

lemma per_e {L f e k : ℕ} (hf : f * (e * k) = L) (he : 1 ≤ e) (hk : 1 ≤ k) {lam : ℕ} (hlam : 1 ≤ lam)
    (ψ : DirichletCharacter ℂ f) (z : ℍ) (s : ℂ) :
    (z.im : ℂ) ^ s * ∑' q : ℤ × ℤ, ψ (q.2 : ZMod f) * eisTerm lam s ((L : ℂ) * q.1 * z + (e : ℤ) * q.2) =
      (e : ℂ) ^ (-2 * s) * (k : ℂ) ^ (-s) * eisensteinLattice f lam ψ (scalePt k z) s := by
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hy := z.im_pos
  have hpt : ∀ q : ℤ × ℤ, eisTerm lam s ((L : ℂ) * q.1 * z + (e : ℤ) * q.2) =
      (e : ℂ) ^ (-2 * s) * eisTerm lam s ((f : ℂ) * q.1 * ((scalePt k z : ℍ) : ℂ) + q.2) := by
    intro q
    rw [← eisTerm_natCast_mul hlam s he, coe_scalePt hk, ← hf]
    congr 1
    push_cast
    ring
  have him : ((scalePt k z).im : ℂ) = (k : ℂ) * z.im := by
    have : (scalePt k z).im = k * z.im := by
      rw [UpperHalfPlane.im, coe_scalePt hk]; simp
    rw [this]; push_cast; ring
  unfold eisensteinLattice
  simp_rw [hpt, ← mul_assoc, mul_comm (ψ _) ((e : ℂ) ^ (-2 * s)), mul_assoc]
  rw [tsum_mul_left]
  have h1 : (((scalePt k z).im : ℝ) : ℂ) ^ s = (k : ℂ) ^ s * (z.im : ℂ) ^ s := by
    rw [UpperHalfPlane.im, coe_scalePt hk]
    have : (((k : ℂ) * z).im) = k * z.im := by simp
    rw [this, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hkR.le hy.le]
    simp
  rw [h1]
  have h2 : (k : ℂ) ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  rw [Complex.cpow_neg]
  field_simp
  refine congrArg (_ * ·) (tsum_congr fun p ↦ ?_)
  rw [mul_right_comm (f : ℂ) (p.1 : ℂ)]

lemma coe_fricke_smul {L : ℕ} [NeZero L] (z : ℍ) :
    ((TauCeti.frickeGL ℝ L • z : ℍ) : ℂ) = -1 / ((L : ℂ) * z) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos TauCeti.val_det_frickeGL_pos]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom]

/-- **The dual Eisenstein series under the Fricke involution:** for $\lambda \ge 1$,
$\check E(W_Lz,s) = L^s(|z|/z)^\lambda E^G(z,s)$. -/
theorem eisensteinDual_fricke {L lam : ℕ} [NeZero L] (hlam : 1 ≤ lam) (ω : DirichletCharacter ℂ L) (z : ℍ)
    (s : ℂ) :
    eisensteinDual L lam ω (TauCeti.frickeGL ℝ L • z) s =
      (L : ℂ) ^ s * (((‖(z : ℂ)‖ : ℝ) : ℂ) / z) ^ lam * eisensteinGauss L lam ω z s := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
  have hz0 : (z : ℂ) ≠ 0 := z.ne_zero
  set j : ℂ := (L : ℂ) * z with hjdef
  have hj : j ≠ 0 := mul_ne_zero hLc hz0
  have hnz : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr hz0
  have hnj : ‖j‖ = L * ‖(z : ℂ)‖ := by
    rw [hjdef, norm_mul]; simp
  have hy := z.im_pos
  have him : (TauCeti.frickeGL ℝ L • z).im = z.im / (L * ‖(z : ℂ)‖ ^ 2) := by
    have h1 : (TauCeti.frickeGL ℝ L • z).im = ((-1 / j : ℂ)).im := by
      rw [UpperHalfPlane.im, coe_fricke_smul]
    rw [h1, div_eq_mul_inv, Complex.mul_im, Complex.inv_re, Complex.inv_im]
    have : j.re = L * (z : ℂ).re := by simp [hjdef]
    have h2 : j.im = L * z.im := by simp [hjdef]
    have h3 : Complex.normSq j = L ^ 2 * ‖(z : ℂ)‖ ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, hnj]; ring
    simp only [neg_re, one_re, neg_im, one_im, h3, h2]
    have : ‖(z : ℂ)‖ ^ 2 = Complex.normSq z := by rw [Complex.normSq_eq_norm_sq]
    field_simp
    simp
  set a : ℂ := ((L : ℝ) : ℂ) ^ s with ha
  set b : ℂ := ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ s with hb
  have hLarg : ((L : ℝ) : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hL.le]; exact Real.pi_ne_zero.symm
  have hzarg : ((‖(z : ℂ)‖ : ℝ) : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hnz.le]; exact Real.pi_ne_zero.symm
  have hjs : ((‖j‖ : ℝ) : ℂ) ^ s = a * b := by
    rw [hnj, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hL.le hnz.le]
  have e1 : (((TauCeti.frickeGL ℝ L • z).im : ℝ) : ℂ) ^ s = ((z.im : ℂ) ^ s) * (a * b ^ 2)⁻¹ := by
    rw [him, div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hy.le (by positivity),
      Complex.ofReal_inv, Complex.inv_cpow _ _ (by
        rw [Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_ne_zero.symm)]
    congr 2
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hL.le (by positivity),
      sq ‖(z : ℂ)‖, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hnz.le hnz.le]
    rw [sq]
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p ↦ (p.2, -p.1)
      invFun := fun q ↦ (-q.2, q.1)
      left_inv := fun p ↦ by simp
      right_inv := fun q ↦ by simp }
  have hpt : ∀ p : ℤ × ℤ, (p.1 : ℂ) * ((TauCeti.frickeGL ℝ L • z : ℍ) : ℂ) + p.2 =
      (((L : ℂ) * (e p).1 * z + (e p).2)) / j := by
    intro p
    rw [coe_fricke_smul, ← hjdef]
    simp only [e, Equiv.coe_fn_mk]
    push_cast
    field_simp
    rw [hjdef]; ring
  have hterm : ∀ p : ℤ × ℤ, gaussAt L ω (-p.1) * eisTerm lam s ((p.1 : ℂ) * ((TauCeti.frickeGL ℝ L • z : ℍ) : ℂ) + p.2) =
      ((‖j‖ : ℂ) ^ lam / j ^ lam) * ((‖j‖ : ℂ) ^ s) ^ 2 *
        (gaussAt L ω (e p).2 * eisTerm lam s ((L : ℂ) * (e p).1 * z + (e p).2)) := by
    intro p
    rw [hpt p, DualReps.eisTerm_div hlam s _ hj]
    simp only [e, Equiv.coe_fn_mk]
    ring
  unfold eisensteinDual eisensteinGauss
  have key : ∑' p : ℤ × ℤ, gaussAt L ω (-p.1) * eisTerm lam s ((p.1 : ℂ) * ((TauCeti.frickeGL ℝ L • z : ℍ) : ℂ) + p.2) =
      ((‖j‖ : ℂ) ^ lam / j ^ lam) * ((‖j‖ : ℂ) ^ s) ^ 2 *
        ∑' q : ℤ × ℤ, gaussAt L ω q.2 * eisTerm lam s ((L : ℂ) * q.1 * z + q.2) := by
    rw [← tsum_mul_left]
    simp_rw [hterm]
    exact e.tsum_eq (fun q ↦ ((‖j‖ : ℂ) ^ lam / j ^ lam) * ((‖j‖ : ℂ) ^ s) ^ 2 *
      (gaussAt L ω q.2 * eisTerm lam s ((L : ℂ) * q.1 * z + q.2)))
  rw [e1, mul_assoc, key]
  have hnj' : ((‖j‖ : ℝ) : ℂ) = (L : ℂ) * ((‖(z : ℂ)‖ : ℝ) : ℂ) := by rw [hnj]; push_cast; ring
  have hLa : a ≠ 0 := by
    rw [ha, Ne, Complex.cpow_eq_zero_iff]; exact fun h ↦ hLc (by exact_mod_cast h.1)
  have hbb : b ≠ 0 := by
    rw [hb, Ne, Complex.cpow_eq_zero_iff]; exact fun h ↦ hnz.ne' (by exact_mod_cast h.1)
  have hnzc : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnz.ne'
  rw [hjs, hnj', hjdef]
  simp only [mul_pow, div_pow]
  rw [show (L : ℂ) ^ s = a by rw [ha]; simp]
  generalize ((z.im : ℝ) : ℂ) ^ s = Y
  have hzl : (z : ℂ) ^ lam ≠ 0 := pow_ne_zero _ hz0
  have hLl : (L : ℂ) ^ lam ≠ 0 := pow_ne_zero _ hLc
  generalize (L : ℂ) ^ lam = P at hLl ⊢
  generalize (((‖(z : ℂ)‖ : ℝ) : ℂ)) ^ lam = Q
  generalize (z : ℂ) ^ lam = R at hzl ⊢
  generalize (∑' q : ℤ × ℤ, gaussAt L ω q.2 * eisTerm lam s ((L : ℂ) * q.1 * z + q.2)) = T
  field_simp

/-- **The combination of Eisenstein series at $\infty$ with the primitive character:** with $f$ the conductor of
$\omega$, $\omega^*$ its primitive character and $g_0 = L/f$,
$\tau(\omega^*)\sum_{e\mid g_0}e^{1-2s}(g_0/e)^{-s}\mu(g_0/e)\,\omega^*(g_0/e)\,E_{f,\overline{\omega^*}}((g_0/e)z,s)$. -/
noncomputable def eisensteinPrimSum (L lam : ℕ) (ω : DirichletCharacter ℂ L) (z : ℍ) (s : ℂ) : ℂ :=
  gaussAt ω.conductor ω.primitiveCharacter 1 *
      ∑ e ∈ (L / ω.conductor).divisors,
        (e : ℂ) ^ (1 - 2 * s) * (((L / ω.conductor / e : ℕ) : ℂ) ^ (-s)) *
          (ArithmeticFunction.moebius (L / ω.conductor / e) : ℂ) *
          ω.primitiveCharacter ((L / ω.conductor / e : ℕ) : ZMod ω.conductor) *
          eisensteinLattice ω.conductor lam ω.primitiveCharacter⁻¹ (scalePt (L / ω.conductor / e) z) s

/-- **$E^G$ as a combination of Eisenstein series at $\infty$ with the primitive character** (for
$\operatorname{Re}s > 1$, $\lambda \ge 1$): $E^G(z,s) = \tau(\omega^*)\sum_{e\mid g_0}e^{1-2s}(g_0/e)^{-s}\mu(g_0/e)\,
\omega^*(g_0/e)\,E_{f,\overline{\omega^*}}((g_0/e)z,s)$ (`eisensteinPrimSum`). -/
theorem eisensteinGauss_eq_sum {L lam : ℕ} [NeZero L] (hlam : 1 ≤ lam) (ω : DirichletCharacter ℂ L) (z : ℍ)
    {s : ℂ} (hs : 1 < s.re) :
    eisensteinGauss L lam ω z s = eisensteinPrimSum L lam ω z s := by
  unfold eisensteinGauss eisensteinPrimSum
  have hL1 : 1 ≤ L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hfL : ω.conductor ∣ L := DirichletCharacter.conductor_dvd_level ω
  have hLf : ω.conductor * (L / ω.conductor) = L := Nat.mul_div_cancel' hfL
  have hg0 : ∀ e ∈ (L / ω.conductor).divisors, e ≠ 0 ∧ 1 ≤ L / ω.conductor / e ∧
      ω.conductor * (e * (L / ω.conductor / e)) = L := by
    intro e he
    rw [Nat.mem_divisors] at he
    obtain ⟨hd, h0⟩ := he
    have hepos : 0 < e := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero h0)
    refine ⟨hepos.ne', Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd) hepos, ?_⟩
    rw [Nat.mul_div_cancel' hd]; exact hLf
  have hsumΦ : ∀ e : ℕ, Summable (fun p : ℤ × ℤ ↦ (if (e : ℤ) ∣ p.2 then
      ω.primitiveCharacter⁻¹ ((p.2 / e : ℤ) : ZMod ω.conductor) *
        eisTerm lam s ((L : ℂ) * p.1 * z + p.2) else 0)) := by
    intro e
    refine Summable.of_norm_bounded (summable_norm_eisTerm hL1 lam z hs) fun p ↦ ?_
    split_ifs
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)
    · rw [norm_zero]; exact norm_nonneg _
  have hdec : ∀ p : ℤ × ℤ, gaussAt L ω p.2 * eisTerm lam s ((L : ℂ) * p.1 * z + p.2) =
      gaussAt ω.conductor ω.primitiveCharacter 1 * ∑ e ∈ (L / ω.conductor).divisors,
        ((e : ℂ) * (ArithmeticFunction.moebius (L / ω.conductor / e) : ℂ) *
          ω.primitiveCharacter ((L / ω.conductor / e : ℕ) : ZMod ω.conductor)) *
        (if (e : ℤ) ∣ p.2 then ω.primitiveCharacter⁻¹ ((p.2 / e : ℤ) : ZMod ω.conductor) *
          eisTerm lam s ((L : ℂ) * p.1 * z + p.2) else 0) := by
    intro p
    rw [GaussImprimitive.gaussAt_eq_sum_primitive, Finset.sum_filter, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    split_ifs <;> ring
  simp_rw [hdec]
  rw [tsum_mul_left, Summable.tsum_finsetSum (fun e _ ↦ (hsumΦ e).mul_left _), mul_left_comm,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun e he ↦ ?_
  obtain ⟨he0, hk, hf⟩ := hg0 e he
  have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.2 he0
  rw [tsum_mul_left, tsum_dvd_reindex lam s z _ he1, mul_left_comm, per_e hf he1 hk hlam _ z s]
  have hec : (e : ℂ) ≠ 0 := by exact_mod_cast he0
  have : (e : ℂ) ^ (1 - 2 * s) = e * (e : ℂ) ^ (-2 * s) := by
    rw [show (1 - 2 * s) = 1 + (-2 * s) by ring, Complex.cpow_add _ _ hec, Complex.cpow_one]
  rw [this]
  ring

/-- The same statement with the definition unfolded. -/
theorem eisensteinGauss_eq_sum' {L lam : ℕ} [NeZero L] (hlam : 1 ≤ lam) (ω : DirichletCharacter ℂ L) (z : ℍ)
    {s : ℂ} (hs : 1 < s.re) :
    eisensteinGauss L lam ω z s = gaussAt ω.conductor ω.primitiveCharacter 1 *
      ∑ e ∈ (L / ω.conductor).divisors,
        (e : ℂ) ^ (1 - 2 * s) * (((L / ω.conductor / e : ℕ) : ℂ) ^ (-s)) *
          (ArithmeticFunction.moebius (L / ω.conductor / e) : ℂ) *
          ω.primitiveCharacter ((L / ω.conductor / e : ℕ) : ZMod ω.conductor) *
          eisensteinLattice ω.conductor lam ω.primitiveCharacter⁻¹ (scalePt (L / ω.conductor / e) z) s :=
  eisensteinGauss_eq_sum hlam ω z hs

end DualFricke

end ModularFormsKB.HalfIntegral
