/-
# $W(4)$ and $U(4)$ preserve $S_{k+1/2}(4)$ for the theta multiplier

This supplies the field `maps` of `KohnenPlusEigen`.

For the theta multiplier $j(\gamma,\tau) = \varepsilon_d^{-1}\left(\frac cd\right)(c\tau+d)^{1/2}$ (`thetaMult`), level $4$,
trivial character:
- `kohnenW4_kohnenW4`: $W(4)$ is an involution, $(g|W(4))|W(4) = g$ (`kohnenW4`; principal branches, both factors
  have positive real part);
- `kohnenW4_mem_cuspForms`: $W(4)$ maps $S_{k+1/2}(4)$ to itself. For $\gamma \in \Gamma_0(4)$ put
  $\gamma^* = W\gamma W^{-1} \in \Gamma_0(4)$, $W = \begin{pmatrix}0&-1\\4&0\end{pmatrix}$; the factor identity
  $j(\gamma^*, W\tau)(-2i\tau)^{1/2} = (-2i\gamma\tau)^{1/2}j(\gamma,\tau)$ follows from the Fricke law of $\theta$
  (`theta_fricke`) and the transformation law (`theta_transformationLaw`) where $\theta(\tau) \ne 0$, and everywhere by
  the identity theorem;
- `kohnenU4_mem_cuspForms`: $U(4)$ maps $S_{k+1/2}(4)$ to itself. With $A_j = \begin{pmatrix}1&j\\0&4\end{pmatrix}$ and
  $\gamma \in \Gamma_0(4)$ one has $A_j\gamma = \gamma_j A_{\sigma(j)}$ with $\gamma_j \in \Gamma_0(16)$ of bottom row
  $(4c, d - c\sigma(j))$, $\sigma$ a permutation of $\{0,1,2,3\}$, and $j(\gamma_j, A_{\sigma(j)}\tau) = j(\gamma,\tau)$
  (`shimuraSym_add_right`, `epsD_add_right`, $(4c/d') = (c/d')$);
- `kohnenL_mem_cuspForms`: hence $L = W(4)U(4)$ preserves $S_{k+1/2}(4)$, the field `maps` of `KohnenPlusEigen`.
-/
import ModularFormsKB.HalfIntegral.KohnenU4
import ModularFormsKB.HalfIntegral.KohnenTheta
import ModularFormsKB.HalfIntegral.Abstract.ThetaInstance
import ModularFormsKB.HalfIntegral.HeckeCusp
import ModularFormsKB.HalfIntegral.Symbol
import ModularFormsKB.HalfIntegral.Law

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup
open scoped Manifold

local notation "ℍ" => UpperHalfPlane

theorem frickePt_frickePt (τ : ℍ) : frickePt (frickePt τ) = τ := by
  apply UpperHalfPlane.ext
  have h : (τ : ℂ) ≠ 0 := τ.ne_zero
  simp only [coe_frickePt]
  field_simp

theorem re_pos_aux (w : ℍ) : 0 < (-2 * I * (w : ℂ)).re := by
  have := w.im_pos
  have e : (-2 * I * (w : ℂ)).re = 2 * (w : ℂ).im := by simp
  rw [e]; have : (w : ℂ).im = w.im := rfl
  rw [this]; positivity

theorem W4_factor_mul (s : ℂ) (τ : ℍ) :
    (-2 * I * (τ : ℂ)) ^ (-s) * (-2 * I * ((frickePt τ : ℍ) : ℂ)) ^ (-s) = 1 := by
  have h : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hre1 := re_pos_aux τ
  have hre2 := re_pos_aux (frickePt τ)
  have ha0 : (-2 * I * (τ : ℂ)) ≠ 0 := fun h => by rw [h] at hre1; simp at hre1
  have hb0 : (-2 * I * ((frickePt τ : ℍ) : ℂ)) ≠ 0 := fun h => by rw [h] at hre2; simp at hre2
  have h1 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre1)
  have h2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre2)
  rw [abs_lt] at h1 h2
  have hl : Complex.log ((-2 * I * (τ : ℂ)) * (-2 * I * ((frickePt τ : ℍ) : ℂ))) =
      Complex.log (-2 * I * (τ : ℂ)) + Complex.log (-2 * I * ((frickePt τ : ℍ) : ℂ)) :=
    (Complex.log_mul_eq_add_log_iff ha0 hb0).mpr ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
  have hprod : (-2 * I * (τ : ℂ)) * (-2 * I * ((frickePt τ : ℍ) : ℂ)) = 1 := by
    simp only [coe_frickePt]
    field_simp
    ring_nf
    simp [Complex.I_sq]
  rw [hprod, Complex.log_one] at hl
  rw [cpow_def_of_ne_zero ha0, cpow_def_of_ne_zero hb0, ← Complex.exp_add, ← add_mul, ← hl]
  simp

/-- **$W(4)$ is an involution.** -/
theorem kohnenW4_kohnenW4 (k : ℕ) (g : ℍ → ℂ) : kohnenW4 k (kohnenW4 k g) = g := by
  funext τ
  simp only [kohnenW4]
  rw [frickePt_frickePt, ← mul_assoc, W4_factor_mul, one_mul]

/-! ### $U(4)$ -/

lemma shimuraSym_four_mul (c d : ℤ) (hd : Odd d) : shimuraSym (4 * c) d = shimuraSym c d := by
  have hJ : jacobiSym (4 * c) d.natAbs = jacobiSym c d.natAbs := by
    rw [jacobiSym.mul_left, jacobiSym.at_four (Int.natAbs_odd.mpr hd), one_mul]
  unfold shimuraSym
  rw [hJ]
  have : (4 * c < 0) ↔ (c < 0) := by omega
  simp only [this]

lemma shimuraSym_sub_mul {c d : ℤ} (hc : 4 ∣ c) (hd : Odd d) (m : ℤ) :
    shimuraSym c (d - c * m) = shimuraSym c d := by
  have hcev : Even c := (even_iff_two_dvd).2 (dvd_trans (by norm_num) hc)
  have hodd : ∀ n : ℤ, Odd (d - c * n) := fun n ↦ Odd.sub_even hd (Even.mul_right hcev n)
  induction m using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have h := shimuraSym_add_right hc (hodd (i + 1))
    have e : d - c * ((i : ℤ) + 1) + c = d - c * i := by ring
    rw [e] at h
    rw [← h]
    exact ih
  | pred i ih =>
    have h := shimuraSym_add_right hc (hodd (-i))
    have e : d - c * (-(i : ℤ)) + c = d - c * (-(i : ℤ) - 1) := by ring
    rw [e] at h
    rw [h]
    exact ih

lemma int_aux (a b c0 d j : ℤ) (hdet : a * d - b * (4 * c0) = 1) :
    ∃ β : ℤ, b + j * d - (a + j * (4 * c0)) * ((a * (b + j * d)) % 4) = 4 * β := by
  have hodd : Odd (a * d) := ⟨2 * (b * c0), by linarith⟩
  obtain ⟨t, ht⟩ := (Int.odd_mul.mp hodd).1
  set X := b + j * d with hX
  set q := (a * X) / 4 with hq
  have hM : (a * X) % 4 = a * X - 4 * q := Int.emod_def _ _
  refine ⟨-t * (t + 1) * X + a * q - j * c0 * ((a * X) % 4), ?_⟩
  rw [hM, ht]
  rw [ht] at hM
  ring

lemma exists_gamma_j {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (j : ℕ) :
    ∃ (γ' : SL(2, ℤ)) (m : ℕ), m < 4 ∧ γ' ∈ Gamma0 4 ∧ γ' 1 0 = 4 * γ 1 0 ∧
      γ' 1 1 = γ 1 1 - γ 1 0 * m ∧ (γ 0 0 * m) % 4 = (γ 0 1 + j * γ 1 1) % 4 ∧
      ∀ τ : ℍ, quarterPt j (γ • τ) = γ' • quarterPt m τ := by
  obtain ⟨c0, hc0⟩ := Gamma0_four_dvd hγ
  have hdet := det_entries γ
  rw [hc0] at hdet
  obtain ⟨β, hβ⟩ := int_aux (γ 0 0) (γ 0 1) c0 (γ 1 1) j hdet
  set a := γ 0 0 with ha
  set b := γ 0 1 with hb
  set d := γ 1 1 with hd
  set M : ℤ := (a * (b + j * d)) % 4 with hMdef
  have hM0 : 0 ≤ M := Int.emod_nonneg _ (by norm_num)
  have hM4 : M < 4 := Int.emod_lt_of_pos _ (by norm_num)
  have hmM : ((M.toNat : ℕ) : ℤ) = M := Int.toNat_of_nonneg hM0
  have hdet' : (a + j * (4 * c0)) * (d - 4 * c0 * M) - β * (4 * (4 * c0)) = 1 := by
    linear_combination hdet + (4 * c0) * hβ
  let γ' : SL(2, ℤ) := ⟨!![a + j * (4 * c0), β; 4 * (4 * c0), d - 4 * c0 * M], by
    simp [Matrix.det_fin_two]; linarith⟩
  refine ⟨γ', M.toNat, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Gamma0_mem]
    rw [show γ' 1 0 = 4 * (4 * c0) by simp [γ']]
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr (by exact ⟨4 * c0, rfl⟩)
  · simp [γ', hc0]
  · simp [γ', hc0, hmM]
  · rw [hmM]
    have : a * M = (b + j * d) - 4 * (β + j * c0 * M) := by linear_combination (-1 : ℤ) * hβ
    rw [this]
    omega
  · intro τ
    have hs := cd_ne_zero γ τ
    ext
    show (((γ • τ : ℍ) : ℂ) + j) / 4 = ((γ' • quarterPt M.toNat τ : ℍ) : ℂ)
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [eq_intCast, Complex.ofReal_intCast]
    have e1 : (γ' 0 0 : ℤ) = a + j * (4 * c0) := by simp [γ']
    have e2 : (γ' 0 1 : ℤ) = β := by simp [γ']
    have e3 : (γ' 1 0 : ℤ) = 4 * (4 * c0) := by simp [γ']
    have e4 : (γ' 1 1 : ℤ) = d - 4 * c0 * M := by simp [γ']
    have hmC : ((M.toNat : ℕ) : ℂ) = (M : ℂ) := by exact_mod_cast hmM
    have hq : ((quarterPt M.toNat τ : ℍ) : ℂ) = ((τ : ℂ) + (M : ℂ)) / 4 := by
      show ((τ : ℂ) + ((M.toNat : ℕ) : ℂ)) / 4 = _
      rw [hmC]
    rw [e1, e2, e3, e4, hq, ← ha, ← hb, ← hd, hc0]
    rw [← hd, hc0] at hs
    have hβC : (b : ℂ) + j * d - (a + j * (4 * c0)) * M = 4 * β := by exact_mod_cast hβ
    have hden : ((4 * (4 * c0) : ℤ) : ℂ) * (((τ : ℂ) + (M : ℂ)) / 4) + ((d - 4 * c0 * M : ℤ) : ℂ)
        = 4 * c0 * τ + d := by push_cast; ring
    rw [hden]
    push_cast at hs ⊢
    have hs' : (τ : ℂ) * c0 * 4 + d ≠ 0 := by intro h; apply hs; linear_combination h
    have hs'' : (τ : ℂ) * 4 * c0 + d ≠ 0 := by intro h; apply hs; linear_combination h
    field_simp
    linear_combination hβC

lemma thetaMult_gamma_j {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (m : ℕ) (τ : ℍ)
    (h10 : γ' 1 0 = 4 * γ 1 0) (h11 : γ' 1 1 = γ 1 1 - γ 1 0 * m) :
    thetaMult γ' ((quarterPt m τ : ℍ) : ℂ) = thetaMult γ (τ : ℂ) := by
  have hc4 := Gamma0_four_dvd hγ
  have hodd := Gamma0_four_odd hγ
  have hcev : Even (γ 1 0) := (even_iff_two_dvd).2 (dvd_trans (by norm_num) hc4)
  have hodd' : Odd (γ 1 1 - γ 1 0 * m) := Odd.sub_even hodd (Even.mul_right hcev _)
  have he : epsD (γ 1 1 - γ 1 0 * m) = epsD (γ 1 1) := by
    have := epsD_add_right (c := -(γ 1 0 * (m : ℤ))) (d := γ 1 1) (dvd_neg.2 (dvd_mul_of_dvd_left hc4 _))
    rwa [← sub_eq_add_neg] at this
  have hsy : shimuraSym (4 * γ 1 0) (γ 1 1 - γ 1 0 * m) = shimuraSym (γ 1 0) (γ 1 1) := by
    rw [shimuraSym_four_mul _ _ hodd', shimuraSym_sub_mul hc4 hodd]
  have hz : ((4 * γ 1 0 : ℤ) : ℂ) * (((quarterPt m τ : ℍ) : ℂ)) + ((γ 1 1 - γ 1 0 * m : ℤ) : ℂ)
      = (γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ) := by
    show ((4 * γ 1 0 : ℤ) : ℂ) * (((τ : ℂ) + (m : ℂ)) / 4) + _ = _
    push_cast; ring
  unfold thetaMult thetaMultCD
  rw [h10, h11, he, hsy, hz]

lemma transforms_iff_simple (k : ℕ) (f : ℍ → ℂ) :
    thetaMultiplierSystem.Transforms k 1 1 f ↔
      ∀ γ ∈ Gamma0 4, ∀ τ : ℍ, f (γ • τ) = thetaMult γ (τ : ℂ) ^ (2 * k + 1) * f τ := by
  refine forall₂_congr fun γ hγ ↦ forall_congr' fun τ ↦ ?_
  have hu : IsUnit ((γ 1 1 : ℤ) : ZMod (4 * 1)) := by
    have hc : ((γ 1 0 : ℤ) : ZMod (4 * 1)) = 0 := by rwa [Gamma0_mem] at hγ
    have hdet := γ.det_coe
    rw [Matrix.det_fin_two] at hdet
    have h1 : ((γ 0 0 : ℤ) : ZMod (4 * 1)) * (γ 1 1 : ℤ) = 1 := by
      have := congrArg (fun x : ℤ ↦ (x : ZMod (4 * 1))) hdet
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at this
      rw [hc] at this
      simpa using this
    exact IsUnit.of_mul_eq_one ((γ 0 0 : ℤ) : ZMod (4 * 1)) (by rw [← h1]; ring)
  rw [MulChar.one_apply hu, one_mul]
  rfl

lemma quarterPt_eq_affPt (j : ℕ) (τ : ℍ) : quarterPt j τ = affPt 1 4 (j : ℤ) τ := by
  ext
  simp [quarterPt]

lemma kohnenU4_transforms (k : ℕ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ Gamma0 4, ∀ τ : ℍ, f (γ • τ) = thetaMult γ (τ : ℂ) ^ (2 * k + 1) * f τ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (τ : ℍ) :
    kohnenU4 f (γ • τ) = thetaMult γ (τ : ℂ) ^ (2 * k + 1) * kohnenU4 f τ := by
  choose! G m hm4 hG hG10 hG11 hmod hpt using fun j : ℕ ↦ exists_gamma_j hγ j
  have hterm : ∀ j ∈ Finset.range 4, f (quarterPt j (γ • τ)) =
      thetaMult γ (τ : ℂ) ^ (2 * k + 1) * f (quarterPt (m j) τ) := by
    intro j _
    rw [hpt j τ, hf _ (hG j) _, thetaMult_gamma_j hγ (m j) τ (hG10 j) (hG11 j)]
  have hinj : Set.InjOn m (Finset.range 4 : Set ℕ) := by
    intro j hj j' hj' hjj
    have hjlt : j < 4 := by simpa using hj
    have hjlt' : j' < 4 := by simpa using hj'
    have h1 := hmod j
    have h2 := hmod j'
    rw [hjj] at h1
    have h3 : ((γ 0 1 : ℤ) + j * γ 1 1) % 4 = ((γ 0 1 : ℤ) + j' * γ 1 1) % 4 := by rw [← h1, ← h2]
    have hodd := Gamma0_four_odd hγ
    have hd4 : γ 1 1 % 4 = 1 ∨ γ 1 1 % 4 = 3 := by
      obtain ⟨t, ht⟩ := hodd; omega
    interval_cases j <;> interval_cases j' <;> omega
  have himg : (Finset.range 4).image m = Finset.range 4 := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      simpa using hm4 j
    · rw [Finset.card_image_of_injOn hinj]
  have hsum : ∑ j ∈ Finset.range 4, f (quarterPt (m j) τ) = ∑ j ∈ Finset.range 4, f (quarterPt j τ) := by
    rw [← Finset.sum_image (f := fun x ↦ f (quarterPt x τ)) hinj, himg]
  unfold kohnenU4
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum]
  ring

lemma kohnenU4_mdiff {f : ℍ → ℂ} (hf : MDiff f) : MDiff (kohnenU4 f) := by
  have h1 : MDiff (fun τ ↦ ∑ j ∈ Finset.range 4, f (quarterPt j τ)) :=
    mdiff_finset_sum _ (fun (j : ℕ) τ ↦ f (quarterPt j τ))
      (fun j _ ↦ by
        simp_rw [quarterPt_eq_affPt]
        exact mdiff_comp_affPt hf _ _ _)
  exact h1.const_smul (1 / 4 : ℂ)

lemma kohnenU4_cuspNorm_le (k : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    Abstract.cuspNorm k (kohnenU4 f) γ τ ≤ (1 / 4 : ℝ) * ∑ j ∈ Finset.range 4,
      Abstract.cuspNorm k (fun τ ↦ f (affPt 1 4 (j : ℤ) τ)) γ τ := by
  have key : ‖kohnenU4 f (γ • τ)‖ ≤ 1 / 4 * ∑ j ∈ Finset.range 4, ‖f (quarterPt j (γ • τ))‖ := by
    unfold kohnenU4
    rw [norm_mul]
    have hn : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
    rw [hn]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
  unfold Abstract.cuspNorm
  simp only [← quarterPt_eq_affPt]
  have hnn : 0 ≤ ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-((k : ℝ) + 1 / 2)) := by positivity
  calc _ ≤ ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-((k : ℝ) + 1 / 2)) *
        (1 / 4 * ∑ j ∈ Finset.range 4, ‖f (quarterPt j (γ • τ))‖) :=
        mul_le_mul_of_nonneg_left key hnn
    _ = _ := by
        simp only [← Finset.mul_sum]
        ring

lemma kohnenU4_zero (k : ℕ) {f : ℍ → ℂ}
    (hf : ∀ γ : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty (Abstract.cuspNorm k f γ)) (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty (Abstract.cuspNorm k (kohnenU4 f) γ) := by
  have hz : ∀ j ∈ Finset.range 4, Filter.Tendsto
      (Abstract.cuspNorm k (fun τ ↦ f (affPt 1 4 (j : ℤ) τ)) γ) UpperHalfPlane.atImInfty (nhds 0) :=
    fun j _ ↦ cuspNorm_affPt_zero k hf 1 4 (j : ℤ) γ
  have ht := (tendsto_finsetSum (Finset.range 4) hz).const_mul (1 / 4 : ℝ)
  rw [Finset.sum_const_zero, mul_zero] at ht
  refine squeeze_zero (fun τ ↦ ?_) (fun τ ↦ kohnenU4_cuspNorm_le k f γ τ) ?_
  · unfold Abstract.cuspNorm; positivity
  · simpa using ht

/-! ### $W(4)$ -/

lemma mdiff_frickePt : MDiff frickePt := by
  have hdet : (!![(0 : ℝ), -1; 4, 0]).det ≠ 0 := by simp [Matrix.det_fin_two]
  have hg : 0 < (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet).det.val := by
    simp [Matrix.det_fin_two]
  have : frickePt = fun τ : ℍ ↦ Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet • τ := by
    funext τ
    ext
    rw [UpperHalfPlane.coe_smul_of_det_pos (by simp [Matrix.det_fin_two])]
    simp [UpperHalfPlane.num, UpperHalfPlane.denom]
  rw [this]
  exact UpperHalfPlane.mdifferentiable_smul hg

lemma mdiff_cpow_fricke (e : ℂ) : MDiff (fun τ : ℍ ↦ (-2 * I * (τ : ℂ)) ^ e) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h : DifferentiableOn ℂ (fun z : ℂ ↦ (-2 * I * z) ^ e) {z : ℂ | 0 < z.im} := by
    apply DifferentiableOn.cpow (by fun_prop) (differentiableOn_const _)
    intro z hz
    rw [Complex.mem_slitPlane_iff]
    left
    simpa using hz
  refine h.congr fun z hz ↦ ?_
  simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

lemma eq_zero_of_mdiff_of_im_gt {F : ℍ → ℂ} (hF : MDiff F) (h : ∀ τ : ℍ, 1 < τ.im → F τ = 0) :
    ∀ τ : ℍ, F τ = 0 := by
  have hhol : DifferentiableOn ℂ (F ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hF
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hana := hhol.analyticOnNhd hU
  have hconn : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  have hz0 : (2 * Complex.I) ∈ {z : ℂ | 0 < z.im} := by simp
  have hev : (F ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds (2 * Complex.I)] 0 := by
    have : {z : ℂ | 1 < z.im} ∈ nhds (2 * Complex.I) :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by simp)
    filter_upwards [this] with z hz
    have hz' : 0 < z.im := lt_trans one_pos hz
    simp only [Function.comp_apply, Pi.zero_apply]
    exact h (UpperHalfPlane.ofComplex z) (by rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz']; simpa using hz)
  have h0 := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz0 hev
  intro τ
  have := h0 τ.im_pos
  simpa using this

lemma exists_gamma_star {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma0 4 ∧ γ' 1 0 = -(4 * γ 0 1) ∧ γ' 1 1 = γ 0 0 ∧
      ∀ τ : ℍ, frickePt (γ • τ) = γ' • frickePt τ := by
  obtain ⟨c0, hc0⟩ := Gamma0_four_dvd hγ
  have hdet := det_entries γ
  rw [hc0] at hdet
  let γ' : SL(2, ℤ) := ⟨!![γ 1 1, -c0; -(4 * γ 0 1), γ 0 0], by
    simp [Matrix.det_fin_two]; linear_combination hdet⟩
  refine ⟨γ', ?_, by simp [γ'], by simp [γ'], ?_⟩
  · rw [Gamma0_mem]
    rw [show γ' 1 0 = -(4 * γ 0 1) by simp [γ']]
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr (by exact ⟨-(γ 0 1), by ring⟩)
  · intro τ
    have hs := cd_ne_zero γ τ
    have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
    have hP : ((γ • τ : ℍ) : ℂ) ≠ 0 := (γ • τ).ne_zero
    ext
    rw [coe_frickePt, UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply,
      coe_frickePt]
    simp only [eq_intCast, Complex.ofReal_intCast]
    have e1 : (γ' 0 0 : ℤ) = γ 1 1 := by simp [γ']
    have e2 : (γ' 0 1 : ℤ) = -c0 := by simp [γ']
    have e3 : (γ' 1 0 : ℤ) = -(4 * γ 0 1) := by simp [γ']
    have e4 : (γ' 1 1 : ℤ) = γ 0 0 := by simp [γ']
    rw [e1, e2, e3, e4]
    have hP' := hP
    rw [UpperHalfPlane.coe_specialLinearGroup_apply] at hP'
    simp only [eq_intCast, Complex.ofReal_intCast] at hP'
    have hnum : (γ 0 0 : ℂ) * τ + γ 0 1 ≠ 0 := fun h0 ↦ hP' (by rw [h0, zero_div])
    have hc : ((γ 1 0 : ℤ) : ℂ) = 4 * c0 := by exact_mod_cast hc0
    have hden : ((-(4 * γ 0 1) : ℤ) : ℂ) * (-1 / (4 * (τ : ℂ))) + ((γ 0 0 : ℤ) : ℂ) =
        ((γ 0 0 : ℂ) * τ + γ 0 1) / τ := by
      push_cast; field_simp; ring
    rw [hden, hc]
    rw [hc] at hs
    push_cast
    field_simp
    ring

lemma thetaMult_fricke_factor {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (hγ' : γ' ∈ Gamma0 4)
    (hpt : ∀ τ : ℍ, frickePt (γ • τ) = γ' • frickePt τ) (τ : ℍ) :
    thetaMult γ' ((frickePt τ : ℍ) : ℂ) * (-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ) =
      (-2 * I * ((γ • τ : ℍ) : ℂ)) ^ (1 / 2 : ℂ) * thetaMult γ (τ : ℂ) := by
  have h1 : MDiff (fun τ : ℍ ↦ thetaMult γ' ((frickePt τ : ℍ) : ℂ)) :=
    (thetaMultiplierSystem.holo γ' hγ').comp mdiff_frickePt
  have h2 := mdiff_cpow_fricke (1 / 2 : ℂ)
  have h3 : MDiff (fun τ : ℍ ↦ (-2 * I * ((γ • τ : ℍ) : ℂ)) ^ (1 / 2 : ℂ)) :=
    (mdiff_cpow_fricke (1 / 2 : ℂ)).comp (UpperHalfPlane.mdifferentiable_smul (g := (γ : GL (Fin 2) ℝ)) (by simp))
  have h4 : MDiff (fun τ : ℍ ↦ thetaMult γ (τ : ℂ)) := thetaMultiplierSystem.holo γ hγ
  have hF := eq_zero_of_mdiff_of_im_gt
    (F := fun τ : ℍ ↦ thetaMult γ' ((frickePt τ : ℍ) : ℂ) * (-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ) -
      (-2 * I * ((γ • τ : ℍ) : ℂ)) ^ (1 / 2 : ℂ) * thetaMult γ (τ : ℂ)) ((h1.mul h2).sub (h3.mul h4)) ?_ τ
  · exact sub_eq_zero.mp hF
  intro σ hσ
  have e1 := theta_transformationLaw γ' hγ' (frickePt σ)
  rw [← hpt σ] at e1
  have e2 := theta_fricke ((γ • σ : ℍ) : ℂ) (γ • σ).im_pos
  have e3 := theta_fricke (σ : ℂ) σ.im_pos
  have e4 := theta_transformationLaw γ hγ σ
  have hne : theta (σ : ℂ) ≠ 0 := theta_ne_zero_of_one_lt_im hσ
  rw [← coe_frickePt] at e2 e3
  rw [e2, e4] at e1
  rw [e3] at e1
  show _ - _ = 0
  rw [sub_eq_zero]
  apply mul_right_cancel₀ hne
  linear_combination -e1

lemma cpow_neg_half_pow (k : ℕ) (x : ℂ) :
    x ^ (-((k : ℂ) + 1 / 2)) = ((x ^ (1 / 2 : ℂ)) ^ (2 * k + 1))⁻¹ := by
  rw [← Complex.cpow_nat_mul, ← Complex.cpow_neg]
  congr 1
  push_cast
  ring

lemma cpow_half_fricke_ne_zero (w : ℍ) : (-2 * I * (w : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
  intro h
  rw [Complex.cpow_eq_zero_iff] at h
  have := re_pos_aux w
  rw [h.1] at this
  simp at this

lemma kohnenW4_transforms (k : ℕ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ Gamma0 4, ∀ τ : ℍ, f (γ • τ) = thetaMult γ (τ : ℂ) ^ (2 * k + 1) * f τ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (τ : ℍ) :
    kohnenW4 k f (γ • τ) = thetaMult γ (τ : ℂ) ^ (2 * k + 1) * kohnenW4 k f τ := by
  obtain ⟨γ', hγ', h10, h11, hpt⟩ := exists_gamma_star hγ
  have key := thetaMult_fricke_factor hγ hγ' hpt τ
  have ha := cpow_half_fricke_ne_zero τ
  have hP := cpow_half_fricke_ne_zero (γ • τ)
  unfold kohnenW4
  rw [hpt τ, hf γ' hγ' (frickePt τ), cpow_neg_half_pow, cpow_neg_half_pow]
  have hk := congrArg (fun x : ℂ ↦ x ^ (2 * k + 1)) key
  simp only [mul_pow] at hk
  generalize thetaMult γ' ((frickePt τ : ℍ) : ℂ) = J at *
  generalize thetaMult γ (τ : ℂ) = j at *
  generalize (-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ) = a at *
  generalize (-2 * I * ((γ • τ : ℍ) : ℂ)) ^ (1 / 2 : ℂ) = P at *
  generalize f (frickePt τ) = fW
  field_simp
  linear_combination fW * hk

lemma kohnenW4_mdiff (k : ℕ) {f : ℍ → ℂ} (hf : MDiff f) : MDiff (kohnenW4 k f) :=
  (mdiff_cpow_fricke (-((k : ℂ) + 1 / 2))).mul (hf.comp mdiff_frickePt)

lemma frickePt_eq_S (w : ℍ) : frickePt w = ModularGroup.S • affPt 4 1 0 w := by
  have hw : (w : ℂ) ≠ 0 := w.ne_zero
  ext
  rw [UpperHalfPlane.modular_S_smul, coe_frickePt]
  simp only [coe_affPt]
  push_cast
  field_simp
  ring

lemma norm_cpow_fricke (k : ℕ) (P : ℂ) (hP : P ≠ 0) :
    ‖(-2 * I * P) ^ (-((k : ℂ) + 1 / 2))‖ = (2 * ‖P‖) ^ (-((k : ℝ) + 1 / 2)) := by
  have h0 : (-2 * I * P) ≠ 0 := mul_ne_zero (by simp) hP
  rw [Complex.norm_cpow_of_ne_zero h0]
  have : (-((k : ℂ) + 1 / 2)).im = 0 := by simp
  rw [this]
  simp only [mul_zero, Real.exp_zero, div_one]
  congr 1
  · simp
  · simp

lemma W4_cuspNorm_eq (k : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) :
    ∃ (ρ : SL(2, ℤ)) (A' D' : ℕ+) (B' : ℤ) (C : ℝ), 0 < C ∧ ∀ τ : ℍ,
      Abstract.cuspNorm k (kohnenW4 k f) γ τ = C * Abstract.cuspNorm k f ρ (affPt A' D' B' τ) := by
  obtain ⟨η, A', D', B', hsm, hden⟩ := affPt_decomp 4 1 0 γ
  refine ⟨ModularGroup.S * η, A', D', B', (((D' : ℕ) : ℝ) / 2) ^ (-((k : ℝ) + 1 / 2)), by positivity,
    fun τ ↦ ?_⟩
  set x := affPt A' D' B' τ with hx
  have hρ : (ModularGroup.S * η) • x = frickePt (γ • τ) := by
    rw [mul_smul, hx, ← hsm τ, frickePt_eq_S]
  have hs := cd_ne_zero γ τ
  have hη := cd_ne_zero η x
  have hPne : ((γ • τ : ℍ) : ℂ) ≠ 0 := (γ • τ).ne_zero
  have hD' : (0 : ℝ) < ((D' : ℕ) : ℝ) := by exact_mod_cast D'.pos
  have hb0' : ((ModularGroup.S * η) 1 0 : ℤ) = η 0 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [ModularGroup.S, Matrix.mul_apply, Fin.sum_univ_two]
  have hb1' : ((ModularGroup.S * η) 1 1 : ℤ) = η 0 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp [ModularGroup.S, Matrix.mul_apply, Fin.sum_univ_two]
  have hb0 : (((ModularGroup.S * η) 1 0 : ℤ) : ℂ) = η 0 0 := by rw [hb0']
  have hb1 : (((ModularGroup.S * η) 1 1 : ℤ) : ℂ) = η 0 1 := by rw [hb1']
  have hηx : ((η • x : ℍ) : ℂ) = 4 * ((γ • τ : ℍ) : ℂ) := by
    rw [← hsm τ]
    simp
  have hηx' : ((η • x : ℍ) : ℂ) = ((η 0 0 : ℂ) * x + η 0 1) / ((η 1 0 : ℂ) * x + η 1 1) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [eq_intCast, Complex.ofReal_intCast]
  have hnum : (η 0 0 : ℂ) * x + η 0 1 = 4 * ((γ • τ : ℍ) : ℂ) * ((η 1 0 : ℂ) * x + η 1 1) := by
    rw [hηx] at hηx'
    rw [eq_div_iff hη] at hηx'
    exact hηx'.symm
  have hN1 : ‖((ModularGroup.S * η) 1 0 : ℂ) * x + (ModularGroup.S * η) 1 1‖ =
      4 * ‖((γ • τ : ℍ) : ℂ)‖ * ‖(η 1 0 : ℂ) * x + η 1 1‖ := by
    rw [hb0, hb1, hnum, norm_mul, norm_mul]
    simp
  have hN2 : ((D' : ℕ) : ℝ) * ‖(η 1 0 : ℂ) * x + η 1 1‖ = ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ := by
    have h := hden τ
    rw [← hx] at h
    have := congrArg norm h
    simpa [norm_mul] using this
  have hv : 0 < ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ := norm_pos_iff.mpr hs
  have hu : 0 < ‖((γ • τ : ℍ) : ℂ)‖ := norm_pos_iff.mpr hPne
  have hw : 0 < ‖(η 1 0 : ℂ) * x + η 1 1‖ := norm_pos_iff.mpr hη
  unfold Abstract.cuspNorm
  show _ * ‖(-2 * I * ((γ • τ : ℍ) : ℂ)) ^ (-((k : ℂ) + 1 / 2)) * f (frickePt (γ • τ))‖ = _
  rw [hρ, hN1, norm_mul, norm_cpow_fricke k _ hPne]
  have hrw : (2 * ‖((γ • τ : ℍ) : ℂ)‖) ^ (-((k : ℝ) + 1 / 2)) * ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-((k : ℝ) + 1 / 2)) =
      (((D' : ℕ) : ℝ) / 2) ^ (-((k : ℝ) + 1 / 2)) *
        (4 * ‖((γ • τ : ℍ) : ℂ)‖ * ‖(η 1 0 : ℂ) * x + η 1 1‖) ^ (-((k : ℝ) + 1 / 2)) := by
    rw [← Real.mul_rpow (by positivity) (by positivity), ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [← hN2]
    field_simp
    ring
  calc _ = ((2 * ‖((γ • τ : ℍ) : ℂ)‖) ^ (-((k : ℝ) + 1 / 2)) *
        ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-((k : ℝ) + 1 / 2))) * ‖f (frickePt (γ • τ))‖ := by ring
    _ = _ := by rw [hrw]; ring

lemma zero_of_comp_W {u w : ℍ → ℝ} (C : ℝ) (hC : 0 < C) (A' D' : ℕ+) (B' : ℤ)
    (hu : UpperHalfPlane.IsZeroAtImInfty u) (hu0 : ∀ τ, 0 ≤ u τ)
    (hw : ∀ τ, w τ = C * u (affPt A' D' B' τ)) :
    UpperHalfPlane.IsZeroAtImInfty w := by
  rw [UpperHalfPlane.isZeroAtImInfty_iff] at *
  have hA' : (0 : ℝ) < ((A' : ℕ) : ℝ) := by exact_mod_cast A'.pos
  have hD' : (0 : ℝ) < ((D' : ℕ) : ℝ) := by exact_mod_cast D'.pos
  intro ε hε
  obtain ⟨A0, h⟩ := hu (ε / C) (by positivity)
  refine ⟨A0 * D' / A', fun z hz ↦ ?_⟩
  have him : A0 ≤ (affPt A' D' B' z).im := by
    rw [im_affPt, le_div_iff₀ hD']
    rw [div_le_iff₀ hA'] at hz
    linarith
  have := h _ him
  rw [Real.norm_of_nonneg (hu0 _)] at this
  rw [hw z, Real.norm_of_nonneg (mul_nonneg hC.le (hu0 _))]
  calc C * u (affPt A' D' B' z) ≤ C * (ε / C) := mul_le_mul_of_nonneg_left this hC.le
    _ = ε := by field_simp

lemma kohnenW4_zero (k : ℕ) {f : ℍ → ℂ}
    (hf : ∀ γ : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty (Abstract.cuspNorm k f γ)) (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty (Abstract.cuspNorm k (kohnenW4 k f) γ) := by
  obtain ⟨ρ, A', D', B', C, hC, h⟩ := W4_cuspNorm_eq k f γ
  exact zero_of_comp_W C hC A' D' B' (hf ρ) (fun τ ↦ by unfold Abstract.cuspNorm; positivity) h

/-- **$U(4)$ preserves $S_{k+1/2}(4)$** for the theta multiplier. -/
theorem kohnenU4_mem_cuspForms (k : ℕ) {f : ℍ → ℂ} (hf : f ∈ thetaMultiplierSystem.cuspForms k 1 1) :
    kohnenU4 f ∈ thetaMultiplierSystem.cuspForms k 1 1 :=
  ⟨kohnenU4_mdiff hf.holo,
    (transforms_iff_simple k _).2 fun _ hγ τ ↦
      kohnenU4_transforms k ((transforms_iff_simple k f).1 hf.transforms) hγ τ,
    kohnenU4_zero k hf.zero_at_cusps⟩

/-- **$W(4)$ preserves $S_{k+1/2}(4)$** for the theta multiplier. -/
theorem kohnenW4_mem_cuspForms (k : ℕ) {f : ℍ → ℂ} (hf : f ∈ thetaMultiplierSystem.cuspForms k 1 1) :
    kohnenW4 k f ∈ thetaMultiplierSystem.cuspForms k 1 1 :=
  ⟨kohnenW4_mdiff k hf.holo,
    (transforms_iff_simple k _).2 fun _ hγ τ ↦
      kohnenW4_transforms k ((transforms_iff_simple k f).1 hf.transforms) hγ τ,
    kohnenW4_zero k hf.zero_at_cusps⟩


/-- **$L = W(4)U(4)$ preserves $S_{k+1/2}(4)$** for the theta multiplier (the field `maps` of `KohnenPlusEigen`). -/
theorem kohnenL_mem_cuspForms (k : ℕ) {f : ℍ → ℂ} (hf : f ∈ thetaMultiplierSystem.cuspForms k 1 1) :
    kohnenL k f ∈ thetaMultiplierSystem.cuspForms k 1 1 :=
  kohnenW4_mem_cuspForms k (kohnenU4_mem_cuspForms k hf)

end ModularFormsKB.HalfIntegral
