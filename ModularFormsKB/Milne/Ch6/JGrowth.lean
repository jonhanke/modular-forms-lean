import ModularFormsKB.Milne.Ch6.HermiteNormalForm
import ModularFormsKB.Milne.Ch6.LevelTwoVanishing

/-!
# Growth of $j(N\gamma z)$ at $i\infty$, and the stabilizer of $j(Nz)$

For $\gamma \in \mathrm{SL}_2(\mathbb Z)$ write $\begin{pmatrix}N&0\\0&1\end{pmatrix}\gamma = \delta
\begin{pmatrix}a&b\\0&d\end{pmatrix}$ (Hermite normal form, `ModularFormsKB.Milne.HNF.exists_SL2Z_mul_upper`), so
$j(N\gamma z) = j((az+b)/d)$. Hence (Milne, Section 6, proof of Theorem 6.1, pdf p. 88):

- `norm_j_scale_smul_le`: $|j(N\gamma z)| \le 2e^{2\pi N \operatorname{Im} z}$ for $\operatorname{Im} z$ large;
- `mem_Gamma0_of_j_scale_smul`: if $j(N\gamma z) = j(Nz)$ for all $z$ then $\gamma \in \Gamma_0(N)$
  (compare the growth $|j(w)| \sim e^{2\pi\operatorname{Im} w}$ along $z = it$, $t \to \infty$).
-/

open UpperHalfPlane CongruenceSubgroup Matrix Filter Topology
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.LevelTwo

open TauCeti.ModularForm

/-- The point $(az+b)/d$ of $\mathbb H$, $a, d > 0$. -/
def affineH (a b d : ℤ) (ha : 0 < a) (hd : 0 < d) (z : ℍ) : ℍ :=
  ⟨((a : ℂ) * z + b) / d, by
    have : (((a : ℂ) * z + b) / d).im = a * z.im / d := by
      simp
    rw [this]
    exact div_pos (mul_pos (by exact_mod_cast ha) z.im_pos) (by exact_mod_cast hd)⟩

/-- Two-sided growth of $|j(w)|$ for $\operatorname{Im} w$ large (from $qj \to 1$). -/
theorem norm_j_bounds : ∃ A : ℝ, ∀ w : ℍ, A ≤ w.im →
    Real.exp (2 * Real.pi * w.im) / 2 ≤ ‖j w‖ ∧ ‖j w‖ ≤ 2 * Real.exp (2 * Real.pi * w.im) := by
  have h := (tendsto_qParam_mul_j_atImInfty).norm
  have h1 : ∀ᶠ w : ℍ in atImInfty, ‖(1 : ℂ)‖ - 1 / 2 < ‖Function.Periodic.qParam 1 (w : ℂ) * j w‖ :=
    h.eventually (lt_mem_nhds (by norm_num))
  have h2 : ∀ᶠ w : ℍ in atImInfty, ‖Function.Periodic.qParam 1 (w : ℂ) * j w‖ < ‖(1 : ℂ)‖ + 1 :=
    h.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).1 (h1.and h2)
  refine ⟨A, fun w hw => ?_⟩
  obtain ⟨hl, hu⟩ := hA w hw
  rw [norm_mul, Function.Periodic.norm_qParam] at hl hu
  simp only [norm_one] at hl hu
  have hpos := Real.exp_pos (2 * Real.pi * w.im)
  have e : Real.exp (-(2 * Real.pi * w.im)) * Real.exp (2 * Real.pi * w.im) = 1 := by
    rw [← Real.exp_add]; simp
  have e2 : ‖j w‖ = (Real.exp (-(2 * Real.pi * w.im)) * ‖j w‖) * Real.exp (2 * Real.pi * w.im) := by
    rw [mul_right_comm, e, one_mul]
  have hq : Real.exp (-(2 * Real.pi * w.im)) = Real.exp (-(2 * Real.pi * w.im)) := rfl
  constructor
  · rw [e2]; norm_num at hl; nlinarith
  · rw [e2]; norm_num at hu; nlinarith

/-- $|j(w)| \le 2 e^{2\pi \operatorname{Im} w}$ for $\operatorname{Im} w$ large (from $qj \to 1$). -/
theorem norm_j_le : ∃ A : ℝ, ∀ w : ℍ, A ≤ w.im → ‖j w‖ ≤ 2 * Real.exp (2 * Real.pi * w.im) := by
  obtain ⟨A, hA⟩ := norm_j_bounds
  exact ⟨A, fun w hw => (hA w hw).2⟩

/-- If $\begin{pmatrix}N&0\\0&1\end{pmatrix}\gamma = \delta\begin{pmatrix}a&b\\0&d\end{pmatrix}$ then
$N(\gamma z) = \delta((az+b)/d)$. -/
theorem scaleH_smul_eq {N : ℕ} (hN : 0 < N) (γ δ : SL(2, ℤ)) (a b d : ℤ) (ha : 0 < a) (hd : 0 < d)
    (h : !![(N : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (δ : Matrix (Fin 2) (Fin 2) ℤ) * !![a, b; 0, d])
    (z : ℍ) : scaleH N hN (γ • z) = δ • affineH a b d ha hd z := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have c00 : (N : ℂ) * (γ 0 0 : ℂ) = (δ 0 0 : ℂ) * a := by exact_mod_cast e00
  have c01 : (N : ℂ) * (γ 0 1 : ℂ) = (δ 0 0 : ℂ) * b + (δ 0 1 : ℂ) * d := by exact_mod_cast e01
  have c10 : (γ 1 0 : ℂ) = (δ 1 0 : ℂ) * a := by exact_mod_cast e10
  have c11 : (γ 1 1 : ℂ) = (δ 1 0 : ℂ) * b + (δ 1 1 : ℂ) * d := by exact_mod_cast e11
  have hz : ((γ 1 0 : ℝ) : ℂ) * (z : ℂ) + ((γ 1 1 : ℤ) : ℝ) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) z
    exact this
  have hz' : (γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ) ≠ 0 := by
    simpa using hz
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hden : (δ 1 0 : ℂ) * (((a : ℂ) * z + b) / d) + (δ 1 1 : ℂ) =
      ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) / d := by
    rw [c10, c11]; field_simp; ring
  have hz'' : (z : ℂ) * (γ 1 0 : ℂ) + (γ 1 1 : ℂ) ≠ 0 := by rwa [mul_comm]
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  show (N : ℂ) * ((γ • z : ℍ) : ℂ) = _
  rw [coe_specialLinearGroup_apply γ z]
  simp only [affineH, algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
  rw [hden]
  field_simp
  linear_combination (z : ℂ) * c00 + c01

/-- **Growth of $j(N\gamma z)$.** -/
theorem norm_j_scale_smul_le {N : ℕ} (hN : 0 < N) (γ : SL(2, ℤ)) :
    ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im →
      ‖j (scaleH N hN (γ • z))‖ ≤ 2 * Real.exp (2 * Real.pi * N * z.im) := by
  have hdet : 0 < (!![(N : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ)).det := by
    rw [Matrix.det_mul, γ.det_coe]; simp [Matrix.det_fin_two_of]; exact hN
  obtain ⟨δ, a, b, d, ha, hd, hb0, hbd, hM⟩ := ModularFormsKB.Milne.HNF.exists_SL2Z_mul_upper _ hdet
  have hadet : a * d = N := by
    have := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_mul, γ.det_coe, δ.det_coe] at this
    simpa [Matrix.det_fin_two_of] using this.symm
  obtain ⟨A₀, hA₀⟩ := norm_j_le
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hadR : (a : ℝ) * d = N := by exact_mod_cast hadet
  refine ⟨max 0 (A₀ * d / a), fun z hz => ?_⟩
  have hz0 : 0 ≤ z.im := le_trans (le_max_left _ _) hz
  have hz1 : A₀ * d / a ≤ z.im := le_trans (le_max_right _ _) hz
  rw [scaleH_smul_eq hN γ δ a b d ha hd hM z, jSL]
  have hw : (affineH a b d ha hd z).im = a * z.im / d := by simp [affineH]
  have hA : A₀ ≤ (affineH a b d ha hd z).im := by
    rw [hw, le_div_iff₀ hdR]
    rw [div_le_iff₀ haR] at hz1
    linarith
  refine le_trans (hA₀ _ hA) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  · exact Real.exp_le_exp.2 (by
      rw [hw]
      have : (a : ℝ) * z.im / d ≤ N * z.im := by
        rw [div_le_iff₀ hdR, ← hadR]
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        have haz : 0 ≤ (a : ℝ) * z.im := mul_nonneg haR.le hz0
        have hdd : (1 : ℝ) ≤ d * d := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hdd haz]
      nlinarith [Real.pi_pos])

/-- **The stabilizer of $j(Nz)$ is $\Gamma_0(N)$.** -/
theorem mem_Gamma0_of_j_scale_smul {N : ℕ} (hN : 0 < N) (γ : SL(2, ℤ))
    (h : ∀ z : ℍ, j (scaleH N hN (γ • z)) = j (scaleH N hN z)) : γ ∈ Gamma0 N := by
  have hdet : 0 < (!![(N : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ)).det := by
    rw [Matrix.det_mul, γ.det_coe]; simp [Matrix.det_fin_two_of]; exact hN
  obtain ⟨δ, a, b, d, ha, hd, hb0, hbd, hM⟩ := ModularFormsKB.Milne.HNF.exists_SL2Z_mul_upper _ hdet
  have hadet : a * d = N := by
    have := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_mul, γ.det_coe, δ.det_coe] at this
    simpa [Matrix.det_fin_two_of] using this.symm
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hadR : (a : ℝ) * d = N := by exact_mod_cast hadet
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨A, hA⟩ := norm_j_bounds
  -- key inequality N * d ≤ a
  have key : (N : ℝ) ≤ a / d := by
    by_contra hlt
    rw [not_le] at hlt
    have hp := Real.pi_pos
    set ε : ℝ := (N : ℝ) - a / d with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    set t : ℝ := max (max 1 (A * d / a + 1)) (max A (4 / (2 * Real.pi * ε))) with ht
    have hε4 : 4 ≤ 2 * Real.pi * ε * t := by
      have h1 : 4 / (2 * Real.pi * ε) ≤ t := by rw [ht]; exact le_trans (le_max_right _ _) (le_max_right _ _)
      rw [div_le_iff₀ (by positivity)] at h1
      linarith
    have ht3 : A ≤ t := by rw [ht]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have ht1 : 1 ≤ t := by rw [ht]; exact le_trans (le_max_left _ _) (le_max_left _ _)
    have ht2 : A * d / a + 1 ≤ t := by rw [ht]; exact le_trans (le_max_right _ _) (le_max_left _ _)
    have htpos : 0 < t := by linarith
    let z : ℍ := ⟨(⟨0, t⟩ : ℂ), htpos⟩
    have hzim : z.im = t := rfl
    have hNge : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hjeq : j (affineH a b d ha hd z) = j (scaleH N hN z) := by
      rw [← h z, scaleH_smul_eq hN γ δ a b d ha hd hM z, jSL]
    have hw : (affineH a b d ha hd z).im = a * t / d := by simp [affineH, hzim]
    have hv : (scaleH N hN z).im = N * t := by simp [scaleH, hzim]
    have hA1 : A ≤ (affineH a b d ha hd z).im := by
      rw [hw, le_div_iff₀ hdR]
      have : A * d / a ≤ t := by linarith
      rw [div_le_iff₀ haR] at this
      linarith
    have hA2 : A ≤ (scaleH N hN z).im := by
      rw [hv]; nlinarith
    have b1 := (hA _ hA1).2
    have b2 := (hA _ hA2).1
    rw [hjeq, hw] at b1
    rw [hv] at b2
    have hexp : Real.exp (2 * Real.pi * (N * t)) =
        Real.exp (2 * Real.pi * (a * t / d)) * Real.exp (2 * Real.pi * ε * t) := by
      rw [← Real.exp_add]; congr 1; rw [hε]; field_simp; ring
    have h5 : 5 ≤ Real.exp (2 * Real.pi * ε * t) := by
      have := Real.add_one_le_exp (2 * Real.pi * ε * t); linarith
    have hpos := Real.exp_pos (2 * Real.pi * (a * t / d))
    rw [hexp] at b2
    nlinarith
  have hd1 : d = 1 := by
    have h1 : (N : ℝ) * d ≤ a := by rwa [le_div_iff₀ hdR] at key
    have h2 : (N : ℤ) * d ≤ a := by exact_mod_cast h1
    have : (N : ℤ) * d * d ≤ a * d := mul_le_mul_of_nonneg_right h2 hd.le
    rw [hadet] at this
    nlinarith
  subst hd1
  have hb : b = 0 := by omega
  subst hb
  have ha' : a = N := by simpa using hadet
  subst ha'
  rw [mem_Gamma0_iff_conj hN]
  refine ⟨δ, ?_⟩
  rw [conj_eq hN]
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  have e11 := congrFun (congrFun hM 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have q00 : (N : ℚ) * (γ 0 0 : ℚ) = (δ 0 0 : ℚ) * N := by exact_mod_cast e00
  have q01 : (N : ℚ) * (γ 0 1 : ℚ) = (δ 0 1 : ℚ) := by exact_mod_cast e01
  have q10 : (γ 1 0 : ℚ) = (δ 1 0 : ℚ) * N := by exact_mod_cast e10
  have q11 : (γ 1 1 : ℚ) = (δ 1 1 : ℚ) := by exact_mod_cast e11
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
    exact mul_right_cancel₀ hN0 (by linarith)
  · linarith
  · rw [q10]; field_simp
  · linarith

end ModularFormsKB.Milne.LevelTwo
