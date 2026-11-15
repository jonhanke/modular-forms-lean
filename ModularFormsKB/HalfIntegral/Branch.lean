/-
# Principal square roots of products, and the multiplier under $U$

For $w^{1/2}$ the principal branch (Mathlib's `cpow` with exponent $1/2$),
$a^{1/2} b^{1/2} = (ab)^{1/2}$ when $-\pi < \arg a + \arg b \le \pi$, and $a^{1/2}b^{1/2} = -(ab)^{1/2}$ when
$\arg a + \arg b > \pi$.

Consequence, with $U = \begin{pmatrix}1&0\\4&1\end{pmatrix}$ and $Uz = z/(4z+1)$: the bottom row of $\gamma U$ is
$(c + 4d, d)$ and
$$j(\gamma U, z) = j(\gamma, Uz)\,(4z+1)^{1/2} \qquad (z \in \mathbb H)$$
(`thetaMultCD_U`). The sign of $(ab)^{1/2}$ versus $a^{1/2}b^{1/2}$, with $a = c\,Uz + d$ and $b = 4z+1$, is exactly compensated
by Shimura's sign in $\big(\frac{c+4d}{d}\big)$ versus $\big(\frac cd\big)$.
-/
import ModularFormsKB.HalfIntegral.Theta

namespace ModularFormsKB.HalfIntegral

open Complex
open scoped Real

/-- $a^{1/2}b^{1/2} = (ab)^{1/2}$ when $-\pi < \arg a + \arg b \le \pi$. -/
theorem cpow_half_mul_of_arg {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : -π < a.arg + b.arg) (h2 : a.arg + b.arg ≤ π) :
    a ^ (1 / 2 : ℂ) * b ^ (1 / 2 : ℂ) = (a * b) ^ (1 / 2 : ℂ) := by
  have hl : Complex.log (a * b) = Complex.log a + Complex.log b :=
    (Complex.log_mul_eq_add_log_iff ha hb).mpr ⟨h1, h2⟩
  rw [cpow_def_of_ne_zero ha, cpow_def_of_ne_zero hb, cpow_def_of_ne_zero (mul_ne_zero ha hb),
    ← Complex.exp_add, hl]
  congr 1
  ring

/-- $a^{1/2}b^{1/2} = -(ab)^{1/2}$ when $\arg a + \arg b > \pi$. -/
theorem cpow_half_mul_of_pi_lt_arg {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (h : π < a.arg + b.arg) :
    a ^ (1 / 2 : ℂ) * b ^ (1 / 2 : ℂ) = -(a * b) ^ (1 / 2 : ℂ) := by
  have hab := mul_ne_zero ha hb
  have hang := Complex.arg_mul_coe_angle ha hb
  obtain ⟨k, hk⟩ := (Real.Angle.angle_eq_iff_two_pi_dvd_sub).mp hang
  have hb1 := Complex.arg_le_pi a
  have hb2 := Complex.arg_le_pi b
  have hc1 := Complex.neg_pi_lt_arg (a * b)
  have hc2 := Complex.arg_le_pi (a * b)
  have hpi := Real.pi_pos
  have hk1 : (k : ℝ) < 0 := by nlinarith
  have hk2 : (-2 : ℝ) < k := by nlinarith
  have hk3 : k = -1 := by
    have : k < 0 := by exact_mod_cast hk1
    have : -2 < k := by exact_mod_cast hk2
    omega
  subst hk3
  have hl : Complex.log (a * b) = Complex.log a + Complex.log b - 2 * π * I := by
    apply Complex.ext
    · simp [Complex.log_re, norm_mul, Real.log_mul, norm_ne_zero_iff.mpr ha, norm_ne_zero_iff.mpr hb]
    · simp [Complex.log_im]
      push_cast at hk
      linarith
  rw [cpow_def_of_ne_zero ha, cpow_def_of_ne_zero hb, cpow_def_of_ne_zero hab, hl,
    ← Complex.exp_add]
  have : (Complex.log a * (1 / 2) + Complex.log b * (1 / 2)) =
      (Complex.log a + Complex.log b - 2 * π * I) * (1 / 2) + π * I := by ring
  rw [this, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

private lemma arg_mem_of_im_pos {w : ℂ} (h : 0 < w.im) : 0 < w.arg ∧ w.arg < π := by
  refine ⟨?_, ?_⟩
  · refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr h.le) (fun h0 => ?_)
    have := (Complex.arg_eq_zero_iff.mp h0.symm).2
    linarith
  · exact Complex.arg_lt_pi_iff.mpr (Or.inr h.ne')

private lemma arg_mem_of_im_neg {w : ℂ} (h : w.im < 0) : -π < w.arg ∧ w.arg < 0 :=
  ⟨Complex.neg_pi_lt_arg w, Complex.arg_neg_iff.mpr h⟩

private lemma arg_mul_of_pi_lt {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (h : π < a.arg + b.arg) :
    (a * b).arg = a.arg + b.arg - 2 * π := by
  have hang := Complex.arg_mul_coe_angle ha hb
  obtain ⟨k, hk⟩ := (Real.Angle.angle_eq_iff_two_pi_dvd_sub).mp hang
  have hb1 := Complex.arg_le_pi a
  have hb2 := Complex.arg_le_pi b
  have hc1 := Complex.neg_pi_lt_arg (a * b)
  have hc2 := Complex.arg_le_pi (a * b)
  have hpi := Real.pi_pos
  have hk1 : (k : ℝ) < 0 := by nlinarith
  have hk2 : (-2 : ℝ) < k := by nlinarith
  have hk3 : k = -1 := by
    have : k < 0 := by exact_mod_cast hk1
    have : -2 < k := by exact_mod_cast hk2
    omega
  subst hk3
  push_cast at hk
  linarith

private lemma jac_shift (c d : ℤ) :
    jacobiSym (c + 4 * d) d.natAbs = jacobiSym c d.natAbs := by
  apply jacobiSym.mod_left'
  have : ((d.natAbs : ℕ) : ℤ) ∣ 4 * d := Dvd.dvd.mul_left (Int.natAbs_dvd.mpr dvd_rfl) 4
  obtain ⟨k, hk⟩ := this
  rw [hk, Int.add_mul_emod_self_left]

/-- **The multiplier under $U$:** $j(\gamma U, z) = j(\gamma, Uz)\,(4z+1)^{1/2}$ for $z \in \mathbb H$, where $(c+4d, d)$ is the
bottom row of $\gamma U$. -/
theorem thetaMultCD_U {c d : ℤ} (hd : Odd d) (z : ℂ) (hz : 0 < z.im) :
    thetaMultCD (c + 4 * d) d z = thetaMultCD c d (z / (4 * z + 1)) * (4 * z + 1) ^ (1 / 2 : ℂ) := by
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd
  have hbim : (4 * z + 1).im = 4 * z.im := by simp
  have hbim' : 0 < (4 * z + 1).im := by rw [hbim]; linarith
  have hb0 : (4 * z + 1) ≠ 0 := fun h => by rw [h] at hbim'; simp at hbim'
  have hwim : 0 < (z / (4 * z + 1)).im := by
    have : (z / (4 * z + 1)).im = z.im / Complex.normSq (4 * z + 1) := by
      rw [Complex.div_im]
      have : Complex.normSq (4 * z + 1) ≠ 0 := (Complex.normSq_pos.mpr hb0).ne'
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] at *
      simp
      field_simp
      ring
    rw [this]
    have := Complex.normSq_pos.mpr hb0
    positivity
  set b : ℂ := 4 * z + 1 with hb
  set w : ℂ := z / b with hw
  set a : ℂ := (c : ℂ) * w + d with ha
  have hab : (((c + 4 * d : ℤ) : ℂ)) * z + d = a * b := by
    rw [ha, hw]; push_cast; field_simp; ring
  have haim : a.im = c * w.im := by simp [ha]
  have habim : (a * b).im = (c + 4 * d : ℤ) * z.im := by
    rw [← hab]; simp
  have hJ := jac_shift c d
  have hbarg := arg_mem_of_im_pos hbim'
  have key : (a ^ (1 / 2 : ℂ) * b ^ (1 / 2 : ℂ) = (a * b) ^ (1 / 2 : ℂ) ∧
        shimuraSym (c + 4 * d) d = shimuraSym c d) ∨
      (a ^ (1 / 2 : ℂ) * b ^ (1 / 2 : ℂ) = -(a * b) ^ (1 / 2 : ℂ) ∧
        shimuraSym (c + 4 * d) d = - shimuraSym c d) := by
    rcases lt_trichotomy c 0 with hc | hc | hc
    · have hai : a.im < 0 := by
        rw [haim]; have : (c : ℝ) < 0 := by exact_mod_cast hc
        nlinarith
      have haa := arg_mem_of_im_neg hai
      have ha0 : a ≠ 0 := fun h => by rw [h] at hai; simp at hai
      left
      refine ⟨cpow_half_mul_of_arg ha0 hb0 (by linarith) (by linarith), ?_⟩
      unfold shimuraSym
      rcases lt_or_gt_of_ne hd0 with hdn | hdp
      · have : c + 4 * d < 0 := by omega
        simp [hc, hdn, this, hJ]
      · simp [not_lt.mpr hdp.le, hJ]
    · subst hc
      have hae : a = d := by simp [ha]
      rcases lt_or_gt_of_ne hd0 with hdn | hdp
      · right
        have ha0 : a ≠ 0 := by rw [hae]; exact_mod_cast hd0
        have hpa : a.arg = π := Complex.arg_eq_pi_iff.mpr
          ⟨by rw [hae]; simpa using hdn, by rw [hae]; simp⟩
        refine ⟨cpow_half_mul_of_pi_lt_arg ha0 hb0 (by linarith [hbarg.1]), ?_⟩
        unfold shimuraSym
        have : 4 * d < 0 := by omega
        have hJ' : jacobiSym (4 * d) d.natAbs = jacobiSym 0 d.natAbs := by simpa using hJ
        simp [this, hdn, hJ']
      · left
        have ha0 : a ≠ 0 := by rw [hae]; exact_mod_cast hd0
        have hpa : a.arg = 0 := Complex.arg_eq_zero_iff.mpr
          ⟨by rw [hae]; simpa using hdp.le, by rw [hae]; simp⟩
        refine ⟨cpow_half_mul_of_arg ha0 hb0 (by linarith [hbarg.1]) (by linarith [hbarg.2]), ?_⟩
        unfold shimuraSym
        have : ¬ (4 * d < 0) := by omega
        have hJ' : jacobiSym (4 * d) d.natAbs = jacobiSym 0 d.natAbs := by simpa using hJ
        simp [this, not_lt.mpr hdp.le, hJ']
    · have hai : 0 < a.im := by
        rw [haim]; have : (0 : ℝ) < c := by exact_mod_cast hc
        positivity
      have haa := arg_mem_of_im_pos hai
      have ha0 : a ≠ 0 := fun h => by rw [h] at hai; simp at hai
      by_cases hs : 0 ≤ c + 4 * d
      · left
        have hle : a.arg + b.arg ≤ π := by
          by_contra hn
          have h2 := arg_mul_of_pi_lt ha0 hb0 (not_le.mp hn)
          have h3 : (a * b).arg < 0 := by linarith
          have h4 := Complex.arg_neg_iff.mp h3
          rw [habim] at h4
          have : (0 : ℝ) ≤ ((c + 4 * d : ℤ) : ℝ) := by exact_mod_cast hs
          nlinarith
        refine ⟨cpow_half_mul_of_arg ha0 hb0 (by linarith) hle, ?_⟩
        unfold shimuraSym
        simp [not_lt.mpr hs, not_lt.mpr hc.le, hJ]
      · right
        push Not at hs
        have hdn : d < 0 := by omega
        have hgt : π < a.arg + b.arg := by
          by_contra hn
          push Not at hn
          have h2 := Complex.arg_mul ha0 hb0 ⟨by linarith, hn⟩
          have h3 : 0 < (a * b).arg := by linarith
          have h4 := Complex.arg_nonneg_iff.mp h3.le
          rw [habim] at h4
          have : ((c + 4 * d : ℤ) : ℝ) < 0 := by exact_mod_cast hs
          nlinarith
        refine ⟨cpow_half_mul_of_pi_lt_arg ha0 hb0 hgt, ?_⟩
        unfold shimuraSym
        simp [hs, hdn, not_lt.mpr hc.le, hJ]
  unfold thetaMultCD
  rw [hab]
  rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
  · rw [k2, ← k1]; ring
  · rw [k2]; push_cast
    have : (a * b) ^ (1 / 2 : ℂ) = -(a ^ (1 / 2 : ℂ) * b ^ (1 / 2 : ℂ)) := by rw [k1]; ring
    rw [this]; ring

end ModularFormsKB.HalfIntegral
