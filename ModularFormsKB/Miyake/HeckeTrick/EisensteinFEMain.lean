import ModularFormsKB.Miyake.HeckeTrick.EisensteinFE

/-!
# `EisensteinFE` from `LatticeThetaInversion`: the assembly

With $\sigma = s + \lambda/2$, Hecke's completed Eisenstein series is
$E^*(z,s) = L^sy^s\pi^{\lambda/2}\,\mathcal M\Theta(z,\cdot)(s+\lambda/2)$, where $\mathcal M$ is the Mellin transform.
For $\operatorname{Re}s > 1$ the Mellin transform is $\Gamma(\sigma)\pi^{-\sigma}\sum_p\omega(d)v^\lambda|v|^{-2\sigma}$
(`mellin_genTheta`); for $\operatorname{Re}s < 0$ the functional equation of the Mellin transforms
(`mellin_latticeTheta_feq`, at $\sigma' = 1 - s + \lambda/2$) gives the dual series. All powers below have positive real
bases, and the constants are matched through $r^w = e^{w\log r}$.
-/

open MeasureTheory Set Filter Topology Complex
open scoped UpperHalfPlane
open scoped Real

noncomputable section

namespace ModularFormsKB.Miyake.HeckeTrick

open ModularFormsKB.HalfIntegral

/-- Hecke's completed Eisenstein series $E^*(z,s) = L^sy^s\pi^{\lambda/2}\mathcal M\Theta(z,\cdot)(s+\lambda/2)$. -/
def eisensteinCompleted (L lam : ℕ) (ω : DirichletCharacter ℂ L) (z : ℍ) (s : ℂ) : ℂ :=
  (L : ℂ) ^ s * (z.im : ℂ) ^ s * (π : ℂ) ^ ((lam : ℂ) / 2) *
    mellin (latticeTheta L lam ω z) (s + (lam : ℂ) / 2)

/-- $r^w = e^{w\log r}$ for $r > 0$. -/
theorem ofReal_cpow_eq_exp {r : ℝ} (hr : 0 < r) (w : ℂ) : (r : ℂ) ^ w = cexp (Real.log r * w) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), ← Complex.ofReal_log hr.le]

/-- $y^t \le y^A + y^{-A}$ for $y > 0$ and $|t| \le A$. -/
theorem rpow_le_rpow_add_rpow_neg {y t A : ℝ} (hy : 0 < y) (ht : |t| ≤ A) :
    y ^ t ≤ y ^ A + y ^ (-A) := by
  rcases le_or_gt 1 y with h1 | h1
  · have : y ^ t ≤ y ^ A := Real.rpow_le_rpow_of_exponent_le h1 ((le_abs_self t).trans ht)
    linarith [Real.rpow_nonneg hy.le (-A)]
  · have : y ^ t ≤ y ^ (-A) :=
      Real.rpow_le_rpow_of_exponent_ge hy h1.le (by linarith [neg_abs_le t])
    linarith [Real.rpow_nonneg hy.le A]

/-- $(y^a + y^{-a})(y^b + y^{-b}) \le 3(y^{a+b} + y^{-(a+b)})$ for $a, b \ge 0$. -/
theorem rpow_add_mul_le {y a b : ℝ} (hy : 0 < y) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (y ^ a + y ^ (-a)) * (y ^ b + y ^ (-b)) ≤ 3 * (y ^ (a + b) + y ^ (-(a + b))) := by
  have e1 : (y ^ a + y ^ (-a)) * (y ^ b + y ^ (-b)) =
      y ^ (a + b) + y ^ (-(a + b)) + (y ^ (a - b) + y ^ (b - a)) := by
    rw [add_mul, mul_add, mul_add, ← Real.rpow_add hy, ← Real.rpow_add hy, ← Real.rpow_add hy,
      ← Real.rpow_add hy]
    have : -a + -b = -(a + b) := by ring
    rw [this, show a + -b = a - b by ring, show -a + b = b - a by ring]
    ring
  have h1 := rpow_le_rpow_add_rpow_neg hy (t := a - b) (A := a + b)
    (by rw [abs_le]; constructor <;> linarith)
  have h2 := rpow_le_rpow_add_rpow_neg hy (t := b - a) (A := a + b)
    (by rw [abs_le]; constructor <;> linarith)
  rw [e1]
  have hp : 0 ≤ y ^ (a + b) + y ^ (-(a + b)) := by positivity
  linarith [h1, h2, hp]

theorem norm_gaussAt_le (L : ℕ) (ω : DirichletCharacter ℂ L) (m : ℤ) : ‖gaussAt L ω m‖ ≤ L := by
  unfold gaussAt
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a ∈ Finset.range L, ‖ω a * cexp (2 * π * I * a * m / L)‖
      ≤ ∑ _a ∈ Finset.range L, (1 : ℝ) := by
        refine Finset.sum_le_sum fun a _ ↦ ?_
        rw [norm_mul]
        have h1 : ‖ω a‖ ≤ 1 := DirichletCharacter.norm_le_one ω _
        have h2 : ‖cexp (2 * π * I * a * m / L)‖ = 1 := by
          rw [Complex.norm_exp]
          have : (2 * π * I * a * m / L : ℂ).re = 0 := by
            simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
          rw [this, Real.exp_zero]
        rw [h2, mul_one]; exact h1
    _ = L := by simp

/-- $(r:\mathbb C) = e^{\log r}$ for $r > 0$. -/
theorem ofReal_eq_exp_log {r : ℝ} (hr : 0 < r) : (r : ℂ) = cexp (Real.log r) := by
  rw [← Complex.ofReal_exp, Real.exp_log hr]

/-- The constant of the second formula: $L^sy^s\pi^{\lambda/2}\varepsilon(L^2y^2)^{\sigma'}\pi^{-\sigma'} =
L^{-s}\pi^{-(1-s)}y^{1-s}$ for $\sigma' = 1 - s + \lambda/2$. -/
theorem const_second {L lam : ℕ} (hL : 1 ≤ L) (z : ℍ) (s : ℂ) :
    (L : ℂ) ^ s * (z.im : ℂ) ^ s * (π : ℂ) ^ ((lam : ℂ) / 2) * thetaEps L lam z *
        (((L : ℝ) ^ 2 * z.im ^ 2 : ℝ) : ℂ) ^ (1 - s + (lam : ℂ) / 2) * (π : ℂ) ^ (-(1 - s + (lam : ℂ) / 2)) =
      (L : ℂ) ^ (-s) * (π : ℂ) ^ (-(1 - s)) * (z.im : ℂ) ^ (1 - s) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hy := z.im_pos
  have hLc : (L : ℂ) = ((L : ℝ) : ℂ) := by norm_cast
  have hε : thetaEps L lam z =
      cexp (-(2 * Real.log L + Real.log z.im) - lam * (Real.log L + Real.log z.im)) := by
    unfold thetaEps
    rw [ofReal_eq_exp_log (by positivity)]
    congr 1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_inv, Real.log_pow, Real.log_inv,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
    push_cast
    ring
  have hLL : Real.log ((L : ℝ) ^ 2 * z.im ^ 2) = 2 * Real.log L + 2 * Real.log z.im := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [hε, hLc, ofReal_cpow_eq_exp hL0, ofReal_cpow_eq_exp hL0, ofReal_cpow_eq_exp hy,
    ofReal_cpow_eq_exp hy, ofReal_cpow_eq_exp Real.pi_pos, ofReal_cpow_eq_exp Real.pi_pos,
    ofReal_cpow_eq_exp Real.pi_pos, ofReal_cpow_eq_exp (by positivity), hLL]
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem mellin_latticeTheta_eq {L lam : ℕ} (hL : 1 ≤ L) (hlam : 1 ≤ lam) (ω : DirichletCharacter ℂ L)
    (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    mellin (latticeTheta L lam ω z) (s + (lam : ℂ) / 2) = Gamma (s + (lam : ℂ) / 2) *
      (π : ℂ) ^ (-(s + (lam : ℂ) / 2)) *
        ∑' p : ℤ × ℤ, ω (p.2 : ZMod L) * eisTerm lam s ((L : ℂ) * p.1 * z + p.2) := by
  have hσ : 1 + (lam : ℝ) / 2 < (s + (lam : ℂ) / 2).re := by
    have : (s + (lam : ℂ) / 2).re = s.re + (lam : ℝ) / 2 := by simp
    rw [this]; linarith
  rw [show latticeTheta L lam ω z = genTheta L lam (fun p ↦ ω (p.2 : ZMod L)) z from
    funext (latticeTheta_eq_genTheta L lam ω z)]
  rw [mellin_genTheta hL hlam (C := 1) (fun p ↦ DirichletCharacter.norm_le_one ω _) z hσ]
  congr 1
  unfold genSeries eisTerm genVec
  refine tsum_congr fun p ↦ ?_
  rw [mul_assoc, mul_assoc]
  congr 3
  ring

theorem mellin_dualTheta_eq {L lam : ℕ} (hlam : 1 ≤ lam) (ω : DirichletCharacter ℂ L) (z : ℍ)
    {s : ℂ} (hs : s.re < 0) :
    mellin (dualTheta L lam ω z) (1 - s + (lam : ℂ) / 2) = Gamma (1 - s + (lam : ℂ) / 2) *
      (π : ℂ) ^ (-(1 - s + (lam : ℂ) / 2)) *
        ∑' p : ℤ × ℤ, gaussAt L ω (-p.1) * eisTerm lam (1 - s) ((p.1 : ℂ) * z + p.2) := by
  have hσ : 1 + (lam : ℝ) / 2 < (1 - s + (lam : ℂ) / 2).re := by
    have : (1 - s + (lam : ℂ) / 2).re = 1 - s.re + (lam : ℝ) / 2 := by simp
    rw [this]; linarith
  rw [show dualTheta L lam ω z = genTheta 1 lam (fun p ↦ gaussAt L ω (-p.1)) z from
    funext (dualTheta_eq_genTheta L lam ω z)]
  rw [mellin_genTheta le_rfl hlam (C := L) (fun p ↦ norm_gaussAt_le L ω _) z hσ]
  congr 1
  unfold genSeries eisTerm genVec
  refine tsum_congr fun p ↦ ?_
  simp only [Nat.cast_one, one_mul]
  rw [show (-2 * (1 - s + (lam : ℂ) / 2)) = -(lam : ℂ) - 2 * (1 - s) by ring]
  ring

/-- **Hecke's functional equation of the Eisenstein series, from the theta inversion.** `EisensteinFE` holds
if `LatticeThetaInversion` does. -/
@[kb "hecke1927" "functional equation of the lattice Eisenstein series, from the theta inversion formula"]
theorem eisensteinFE_of_latticeThetaInversion (h : LatticeThetaInversion) : EisensteinFE := by
  refine ⟨fun L lam ω hL hlam _ ↦ ?_⟩
  have hL1 : 1 ≤ L := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
  refine ⟨eisensteinCompleted L lam ω, fun z ↦ ?_, fun s ↦ ?_, fun z s hs ↦ ?_, fun z s hs ↦ ?_,
    fun σ₁ σ₂ ↦ ?_⟩
  · -- entire in `s`
    have hy : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast z.im_pos.ne'
    unfold eisensteinCompleted
    exact (((differentiable_id.const_cpow (Or.inl hLc)).mul
      (differentiable_id.const_cpow (Or.inl hy))).mul (differentiable_const _)).mul
      ((differentiable_mellin_latticeTheta h ω hL1 hlam z).comp (differentiable_id.add_const _))
  · -- continuous in `z`
    unfold eisensteinCompleted
    have hc : Continuous fun z : ℍ ↦ ((z.im : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im
    have hcp : Continuous fun z : ℍ ↦ ((z.im : ℝ) : ℂ) ^ s :=
      hc.cpow continuous_const fun z ↦ Or.inl (by simpa using z.im_pos)
    exact ((continuous_const.mul hcp).mul continuous_const).mul
      (continuous_mellin_latticeTheta h ω hL1 hlam _)
  · -- `Re s > 1`
    unfold eisensteinCompleted eisensteinLattice
    rw [mellin_latticeTheta_eq hL1 hlam ω z hs]
    have hπ : (π : ℂ) ^ ((lam : ℂ) / 2) * (π : ℂ) ^ (-(s + (lam : ℂ) / 2)) = (π : ℂ) ^ (-s) := by
      rw [← Complex.cpow_add _ _ (by exact_mod_cast Real.pi_pos.ne')]
      congr 1; ring
    calc _ = (L : ℂ) ^ s * ((π : ℂ) ^ ((lam : ℂ) / 2) * (π : ℂ) ^ (-(s + (lam : ℂ) / 2))) *
          Gamma (s + (lam : ℂ) / 2) * ((z.im : ℂ) ^ s *
            ∑' p : ℤ × ℤ, ω (p.2 : ZMod L) * eisTerm lam s ((L : ℂ) * p.1 * z + p.2)) := by ring
      _ = _ := by rw [hπ]
  · -- `Re s < 0`
    unfold eisensteinCompleted eisensteinDual
    rw [show s + (lam : ℂ) / 2 = (lam : ℂ) + 1 - (1 - s + (lam : ℂ) / 2) by ring]
    have hσ : 1 + (lam : ℝ) / 2 < (1 - s + (lam : ℂ) / 2).re := by
      have : (1 - s + (lam : ℂ) / 2).re = 1 - s.re + (lam : ℝ) / 2 := by simp
      rw [this]; linarith
    rw [mellin_latticeTheta_feq h ω hL1 hlam z hσ, mellin_dualTheta_eq hlam ω z hs]
    have hc := const_second (lam := lam) hL1 z s
    calc _ = ((L : ℂ) ^ s * (z.im : ℂ) ^ s * (π : ℂ) ^ ((lam : ℂ) / 2) * thetaEps L lam z *
          (((L : ℝ) ^ 2 * z.im ^ 2 : ℝ) : ℂ) ^ (1 - s + (lam : ℂ) / 2) *
            (π : ℂ) ^ (-(1 - s + (lam : ℂ) / 2))) * Gamma (1 - s + (lam : ℂ) / 2) *
          ∑' p : ℤ × ℤ, gaussAt L ω (-p.1) * eisTerm lam (1 - s) ((p.1 : ℂ) * z + p.2) := by ring
      _ = _ := by rw [hc]; ring
  · -- bound on vertical strips
    obtain ⟨A, B, hAB⟩ := norm_mellin_latticeTheta_le h ω hL1 hlam (σ₁ + lam / 2) (σ₂ + lam / 2)
    set A' : ℝ := max |σ₁| |σ₂| with hA'
    refine ⟨A' + |A|, 3 * (L : ℝ) ^ A' * π ^ ((lam : ℝ) / 2) * |B|, fun z s h1 h2 ↦ ?_⟩
    have hy := z.im_pos
    have hsA : |s.re| ≤ A' := by
      rw [abs_le]; constructor
      · have := neg_abs_le σ₁; have := le_max_left |σ₁| |σ₂|; linarith
      · have := le_abs_self σ₂; have := le_max_right |σ₁| |σ₂|; linarith
    have hA0 : 0 ≤ A' := (abs_nonneg _).trans (le_max_left _ _)
    have hm := hAB z (s + (lam : ℂ) / 2) (by simp; linarith) (by simp; linarith)
    have hsym : z.im ^ A + z.im ^ (-A) = z.im ^ |A| + z.im ^ (-|A|) := by
      rcases le_total 0 A with hA | hA
      · rw [abs_of_nonneg hA]
      · rw [abs_of_nonpos hA, neg_neg]; ring
    have hpos : 0 ≤ z.im ^ |A| + z.im ^ (-|A|) := by positivity
    have hm' : ‖mellin (latticeTheta L lam ω z) (s + (lam : ℂ) / 2)‖ ≤
        |B| * (z.im ^ |A| + z.im ^ (-|A|)) := by
      rw [← hsym]
      exact hm.trans (mul_le_mul_of_nonneg_right (le_abs_self B) (by rw [hsym]; exact hpos))
    have hLs : ‖(L : ℂ) ^ s‖ ≤ (L : ℝ) ^ A' := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hL1) ((le_abs_self _).trans hsA)
    have hys : ‖(z.im : ℂ) ^ s‖ ≤ z.im ^ A' + z.im ^ (-A') := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
      exact rpow_le_rpow_add_rpow_neg hy hsA
    have hπ : ‖(π : ℂ) ^ ((lam : ℂ) / 2)‖ = π ^ ((lam : ℝ) / 2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]; simp
    have hprod := rpow_add_mul_le hy hA0 (abs_nonneg A)
    unfold eisensteinCompleted
    rw [norm_mul, norm_mul, norm_mul, hπ]
    calc _ ≤ (L : ℝ) ^ A' * (z.im ^ A' + z.im ^ (-A')) * π ^ ((lam : ℝ) / 2) *
          (|B| * (z.im ^ |A| + z.im ^ (-|A|))) := by gcongr
      _ = (L : ℝ) ^ A' * π ^ ((lam : ℝ) / 2) * |B| *
          ((z.im ^ A' + z.im ^ (-A')) * (z.im ^ |A| + z.im ^ (-|A|))) := by ring
      _ ≤ (L : ℝ) ^ A' * π ^ ((lam : ℝ) / 2) * |B| *
          (3 * (z.im ^ (A' + |A|) + z.im ^ (-(A' + |A|)))) := by gcongr
      _ = _ := by ring

end ModularFormsKB.Miyake.HeckeTrick
