/-
# The Fricke eigenvalue of $f_{32}$ and its character form

* `coeffGrowth_f32C`, `isCuspFormChar_f32`: $f_{32}$ is in Miyake's $S_2(32, 1)$ (from `f32Modular`).
* `fricke_f32`: in Miyake's normalization the Fricke involution $\omega_{32}$ acts on $f_{32}$ by $-1$.

**Proof of `fricke_f32`.** `thetaSph_S_smul_of_finrank_eq` for $\theta_{\gamma+L}(-1/(32z))$, with $L^\vee = (\tfrac14\mathbb Z)^2$,
gives $(\sqrt{32}z)^{-2}\theta(-1/(32z)) = \tfrac i2 S(z)$ where
$S = \sum_{(j,l) \in \mathbb Z^2} i^{j-l}(j + il)\,q^{j^2+l^2}$ (`theta_S_tau`). Splitting $\mathbb Z^2$ by the classes of
$(j,l)$ modulo the rotation group $\{1, i, -1, -i\}$ (`decomp`): the terms with $j + l$ even cancel under
$(j,l) \mapsto (-j,-l)$ (`Fterm_neg`), and the four classes with $j + l$ odd are the rotations of the primary
class (`piece0` to `piece3`), each a multiple ($i$, $1$, $i$, $1$) of the series of `Gterm`, so
$S = (2 + 2i) f_{32}$ (`hasSum_split`). Hence $\omega_{32}$ acts on $f_{32} = \tfrac{1+i}2\theta$ by
$\tfrac{1+i}{2}\cdot\tfrac i2 (2+2i) = -1$.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.F32Theta
import ModularFormsKB.Miyake.Sec4_3.Twist

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
open Complex MatrixGroups CongruenceSubgroup ModularForm
open scoped Real
open ModularFormsKB.Miyake.Sec4_9
local notation "ℍ" => UpperHalfPlane

/-- `f₃₂`'s coefficients as complex numbers. -/
noncomputable def f32C (m : ℕ) : ℂ := (f32Coeff m : ℂ)

theorem qSeries_f32C (τ : ℍ) : Miyake.qSeries f32C τ = f32 τ := rfl

theorem coeffGrowth_f32C : Miyake.CoeffGrowth f32C := by
  refine ⟨1, Asymptotics.IsBigO.of_bound 6 (Filter.Eventually.of_forall fun m ↦ ?_)⟩
  have hb := abs_f32Coeff_le m
  rw [f32C, Complex.norm_intCast, Real.rpow_one, Real.norm_natCast]
  exact_mod_cast hb

theorem isCuspFormChar_f32 :
    Miyake.IsCuspFormChar 2 32 1 (fun τ : ℍ ↦ Miyake.qSeries f32C τ) := by
  obtain ⟨F, hF⟩ := f32Modular.exists_cuspForm
  have hfun : (fun τ : ℍ ↦ Miyake.qSeries f32C τ) = f32 := funext qSeries_f32C
  have hmem : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 32 → (F : ℍ → ℂ) ∣[(2 : ℤ)] γ = F := by
    intro γ hγ
    have := F.slash_action_eq' (Matrix.SpecialLinearGroup.mapGL ℝ γ) ⟨γ, hγ, rfl⟩
    rwa [← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← ModularForm.SL_slash] at this
  refine ⟨⟨CuspForm.restrict (Subgroup.map_mono (Gamma1_in_Gamma0 32)) F, ?_⟩, ?_⟩
  · rw [hfun, ← hF]; rfl
  · intro γ hγ
    have hu : IsUnit ((γ 1 1 : ℤ) : ZMod 32) := by
      have hdet := γ.det_coe
      rw [Matrix.det_fin_two] at hdet
      rw [Gamma0_mem] at hγ
      refine isUnit_iff_exists_inv.mpr ⟨((γ 0 0 : ℤ) : ZMod 32), ?_⟩
      have := congrArg (fun x : ℤ ↦ (x : ZMod 32)) hdet
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hγ, mul_zero, sub_zero] at this
      rw [mul_comm]; exact this
    rw [hfun, ← hF, hmem γ hγ, MulChar.one_apply hu, one_smul]

/-! ### Powers of `I` -/

theorem I_zpow_congr {m n : ℤ} (h : m % 4 = n % 4) : I ^ m = I ^ n := by
  obtain ⟨t, rfl⟩ : ∃ t, m = n + 4 * t := ⟨(m - n) / 4, by omega⟩
  rw [zpow_add₀ I_ne_zero, zpow_mul]
  have : I ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by rfl, zpow_natCast, I_pow_four]
  rw [this, one_zpow, mul_one]

theorem I_zpow_one {n : ℤ} (h : n % 4 = 1) : I ^ n = I := by
  rw [I_zpow_congr (n := 1) (by simpa using h)]; simp

theorem I_zpow_three {n : ℤ} (h : n % 4 = 3) : I ^ n = -I := by
  rw [I_zpow_congr (n := 3) (by simpa using h)]
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast, pow_succ, I_sq]; ring

theorem exp_quarter (n : ℤ) : cexp (2 * π * I * (((n : ℝ) / 4 : ℝ) : ℂ)) = I ^ n := by
  have : (2 * π * I * (((n : ℝ) / 4 : ℝ) : ℂ)) = (n : ℂ) * (π / 2 * I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul, Complex.exp_pi_div_two_mul_I]

/-! ### The Fricke series -/

/-- `I^{j - l} (j + i l) e(2πi (j² + l²) z)`. -/
noncomputable def Fterm (z : ℍ) (p : ℤ × ℤ) : ℂ :=
  I ^ (p.1 - p.2) * ((p.1 : ℂ) + I * p.2) * cexp (2 * π * I * ((p.1 ^ 2 + p.2 ^ 2 : ℤ) : ℂ) * z)

/-- The four rotations. -/
def r1 (p : ℤ × ℤ) : ℤ × ℤ := (p.2, -p.1)
def r2 (p : ℤ × ℤ) : ℤ × ℤ := (-p.1, -p.2)
def r3 (p : ℤ × ℤ) : ℤ × ℤ := (-p.2, p.1)

theorem r1_bij : Function.Bijective r1 := by
  constructor
  · intro p q h; simp only [r1, Prod.mk.injEq] at h; ext <;> omega
  · intro p; exact ⟨(-p.2, p.1), by simp [r1]⟩
theorem r2_bij : Function.Bijective r2 := by
  constructor
  · intro p q h; simp only [r2, Prod.mk.injEq] at h; ext <;> omega
  · intro p; exact ⟨(-p.1, -p.2), by simp [r2]⟩
theorem r3_bij : Function.Bijective r3 := by
  constructor
  · intro p q h; simp only [r3, Prod.mk.injEq] at h; ext <;> omega
  · intro p; exact ⟨(p.2, -p.1), by simp [r3]⟩

theorem hasSum_comp_bij {r : ℤ × ℤ → ℤ × ℤ} (hr : Function.Bijective r) {G : ℤ × ℤ → ℂ} {a : ℂ}
    (h : HasSum G a) : HasSum (G ∘ r) a :=
  (Equiv.ofBijective r hr).hasSum_iff.mpr h

theorem piece0 (z : ℍ) (p : ℤ × ℤ) :
    {p : ℤ × ℤ | p ∈ Sset}.indicator (Fterm z) p = I * Gterm z p := by
  by_cases h : p ∈ Sset
  · rw [Set.indicator_of_mem (by exact h), Gterm, Set.indicator_of_mem h, Fterm]
    have h' := h
    simp only [Sset, Set.mem_ofPred_eq] at h'
    rw [I_zpow_one (by omega)]
    ring
  · rw [Set.indicator_of_notMem (by exact h), Gterm, Set.indicator_of_notMem h]; simp

theorem piece1 (z : ℍ) (p : ℤ × ℤ) :
    {p : ℤ × ℤ | r1 p ∈ Sset}.indicator (Fterm z) p = 1 * Gterm z (r1 p) := by
  by_cases h : r1 p ∈ Sset
  · rw [Set.indicator_of_mem (by exact h), Gterm, Set.indicator_of_mem h, Fterm]
    have h' := h
    simp only [r1, Sset, Set.mem_ofPred_eq] at h'
    rw [I_zpow_three (by omega)]
    have hN : (r1 p).1 ^ 2 + (r1 p).2 ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by simp only [r1]; ring
    rw [hN]
    generalize cexp (2 * π * I * ((p.1 ^ 2 + p.2 ^ 2 : ℤ) : ℂ) * z) = E
    simp only [r1]
    push_cast
    linear_combination (-(p.2 : ℂ) * E) * Complex.I_sq
  · rw [Set.indicator_of_notMem (by exact h), Gterm, Set.indicator_of_notMem h]; simp

theorem piece2 (z : ℍ) (p : ℤ × ℤ) :
    {p : ℤ × ℤ | r2 p ∈ Sset}.indicator (Fterm z) p = I * Gterm z (r2 p) := by
  by_cases h : r2 p ∈ Sset
  · rw [Set.indicator_of_mem (by exact h), Gterm, Set.indicator_of_mem h, Fterm]
    have h' := h
    simp only [r2, Sset, Set.mem_ofPred_eq] at h'
    rw [I_zpow_three (by omega)]
    have hN : (r2 p).1 ^ 2 + (r2 p).2 ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by simp only [r2]; ring
    rw [hN]
    simp only [r2]
    push_cast
    ring
  · rw [Set.indicator_of_notMem (by exact h), Gterm, Set.indicator_of_notMem h]; simp

theorem piece3 (z : ℍ) (p : ℤ × ℤ) :
    {p : ℤ × ℤ | r3 p ∈ Sset}.indicator (Fterm z) p = 1 * Gterm z (r3 p) := by
  by_cases h : r3 p ∈ Sset
  · rw [Set.indicator_of_mem (by exact h), Gterm, Set.indicator_of_mem h, Fterm]
    have h' := h
    simp only [r3, Sset, Set.mem_ofPred_eq] at h'
    rw [I_zpow_one (by omega)]
    have hN : (r3 p).1 ^ 2 + (r3 p).2 ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by simp only [r3]; ring
    rw [hN]
    generalize cexp (2 * π * I * ((p.1 ^ 2 + p.2 ^ 2 : ℤ) : ℂ) * z) = E
    simp only [r3]
    push_cast
    linear_combination ((p.2 : ℂ) * E) * Complex.I_sq
  · rw [Set.indicator_of_notMem (by exact h), Gterm, Set.indicator_of_notMem h]; simp

theorem Fterm_neg (z : ℍ) {p : ℤ × ℤ} (h : (p.1 + p.2) % 2 = 0) : Fterm z (-p) = -Fterm z p := by
  rw [Fterm, Fterm]
  simp only [Prod.fst_neg, Prod.snd_neg]
  rw [I_zpow_congr (m := -p.1 - -p.2) (n := p.1 - p.2) (by omega)]
  have : (-p.1) ^ 2 + (-p.2) ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by ring
  rw [this]
  push_cast
  ring

theorem Eneg (z : ℍ) (p : ℤ × ℤ) :
    {p : ℤ × ℤ | (p.1 + p.2) % 2 = 0}.indicator (Fterm z) (-p) =
      -({p : ℤ × ℤ | (p.1 + p.2) % 2 = 0}.indicator (Fterm z) p) := by
  by_cases hp : (p.1 + p.2) % 2 = 0
  · rw [Set.indicator_of_mem (show -p ∈ {p : ℤ × ℤ | (p.1 + p.2) % 2 = 0} by
      simp only [Set.mem_ofPred_eq, Prod.fst_neg, Prod.snd_neg]; omega),
      Set.indicator_of_mem (show p ∈ {p : ℤ × ℤ | (p.1 + p.2) % 2 = 0} from hp), Fterm_neg z hp]
  · rw [Set.indicator_of_notMem (show -p ∉ {p : ℤ × ℤ | (p.1 + p.2) % 2 = 0} by
      simp only [Set.mem_ofPred_eq, Prod.fst_neg, Prod.snd_neg]; omega),
      Set.indicator_of_notMem (show p ∉ {p : ℤ × ℤ | (p.1 + p.2) % 2 = 0} from hp)]
    simp

theorem decomp (z : ℍ) (p : ℤ × ℤ) :
    Fterm z p = {p : ℤ × ℤ | (p.1 + p.2) % 2 = 0}.indicator (Fterm z) p +
      {p : ℤ × ℤ | p ∈ Sset}.indicator (Fterm z) p +
      {p : ℤ × ℤ | r1 p ∈ Sset}.indicator (Fterm z) p +
      {p : ℤ × ℤ | r2 p ∈ Sset}.indicator (Fterm z) p +
      {p : ℤ × ℤ | r3 p ∈ Sset}.indicator (Fterm z) p := by
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Sset, r1, r2, r3]
  split_ifs <;> first | (exfalso; omega) | simp

theorem hasSum_split (z : ℍ) {S0 : ℂ} (hF : HasSum (Fterm z) S0) :
    S0 = (2 * I + 2) * ((1 + I) / 2 * thetaSph L32 1 u1 w1 γ32 z) := by
  set a := (1 + I) / 2 * thetaSph L32 1 u1 w1 γ32 z with ha
  have hG : HasSum (Gterm z) a := hasSum_Gterm z
  have h0 : HasSum (fun p ↦ {p : ℤ × ℤ | p ∈ Sset}.indicator (Fterm z) p) (I * a) := by
    simp_rw [piece0]; exact hG.mul_left I
  have h1 : HasSum (fun p ↦ {p : ℤ × ℤ | r1 p ∈ Sset}.indicator (Fterm z) p) (1 * a) := by
    simp_rw [piece1]; exact (hasSum_comp_bij r1_bij hG).mul_left 1
  have h2 : HasSum (fun p ↦ {p : ℤ × ℤ | r2 p ∈ Sset}.indicator (Fterm z) p) (I * a) := by
    simp_rw [piece2]; exact (hasSum_comp_bij r2_bij hG).mul_left I
  have h3 : HasSum (fun p ↦ {p : ℤ × ℤ | r3 p ∈ Sset}.indicator (Fterm z) p) (1 * a) := by
    simp_rw [piece3]; exact (hasSum_comp_bij r3_bij hG).mul_left 1
  have hE := hF.sub (((h0.add h1).add h2).add h3)
  have hE' : HasSum (fun p ↦ {p : ℤ × ℤ | (p.1 + p.2) % 2 = 0}.indicator (Fterm z) p)
      (S0 - (I * a + 1 * a + I * a + 1 * a)) := by
    convert hE using 1
    funext p
    linear_combination (-1 : ℂ) * decomp z p
  -- antisymmetry
  have hneg : HasSum (fun p ↦ -({p : ℤ × ℤ | (p.1 + p.2) % 2 = 0}.indicator (Fterm z) p))
      (S0 - (I * a + 1 * a + I * a + 1 * a)) := by
    have := (Equiv.neg (ℤ × ℤ)).hasSum_iff.mpr hE'
    convert this using 1
    funext p
    simp only [Function.comp_apply, Equiv.neg_apply]
    exact (Eneg z p).symm
  have h4 := hE'.neg
  have h5 := hneg.unique h4
  have : S0 - (I * a + 1 * a + I * a + 1 * a) = 0 := by
    linear_combination (1 / 2 : ℂ) * h5
  linear_combination this


/-! ### The dual lattice -/

/-- The parametrisation `ℤ² → (¼ℤ)²` of the dual lattice of `4ℤ ⊕ 4ℤ`. -/
noncomputable def jD (p : ℤ × ℤ) : ZLattice.dual L32 :=
  ⟨WithLp.toLp 2 (((p.1 : ℝ) / 4), ((p.2 : ℝ) / 4)),
    mem_dual_L32.mpr ⟨p.1, p.2, by simp, by simp⟩⟩

theorem jD_bijective : Function.Bijective jD := by
  constructor
  · intro p q h
    have h1 := congrArg (fun v : ZLattice.dual L32 ↦ (v : E2).fst) h
    have h2 := congrArg (fun v : ZLattice.dual L32 ↦ (v : E2).snd) h
    simp [jD] at h1 h2
    ext <;> assumption_mod_cast
  · intro v
    obtain ⟨m, n, h1, h2⟩ := mem_dual_L32.mp v.2
    refine ⟨(m, n), ?_⟩
    apply Subtype.ext
    apply WithLp.ofLp_injective
    ext
    · simp only [jD]; simp; linarith
    · simp only [jD]; simp; linarith

/-- `τ = 32 z`. -/
noncomputable def tau32 (z : ℍ) : ℍ := ⟨32 * (z : ℂ), by
  have := z.im_pos
  simp [this]⟩

theorem coe_tau32 (z : ℍ) : (tau32 z : ℂ) = 32 * z := rfl

theorem dual_term (z : ℍ) (p : ℤ × ℤ) :
    isoForm u1 w1 (jD p : E2) ^ 1 * cexp (2 * π * I * (((inner ℝ γ32 (jD p : E2)) : ℝ) : ℂ)) *
      cexp (π * I * (‖(jD p : E2)‖ ^ 2 : ℝ) * (tau32 z : ℂ)) = (1 / 4) * Fterm z p := by
  have hin : (inner ℝ γ32 (jD p : E2)) = ((p.1 - p.2 : ℤ) : ℝ) / 4 := by
    simp [γ32, jD, WithLp.prod_inner_apply]; ring
  have hx : (jD p : E2).fst = (p.1 : ℝ) / 4 := by simp [jD]
  have hy : (jD p : E2).snd = (p.2 : ℝ) / 4 := by simp [jD]
  rw [hin, exp_quarter, isoForm_u1_w1, norm_sq_E2, hx, hy, Fterm, coe_tau32, pow_one]
  have : cexp (π * I * (((p.1 : ℝ) / 4) ^ 2 + ((p.2 : ℝ) / 4) ^ 2 : ℝ) * (32 * z : ℂ)) =
      cexp (2 * π * I * ((p.1 ^ 2 + p.2 ^ 2 : ℤ) : ℂ) * z) := by
    congr 1; push_cast; ring
  rw [this]
  push_cast
  ring

theorem summable_Fterm (z : ℍ) : Summable (Fterm z) := by
  have h := summable_norm_thetaW (ZLattice.dual L32) (polyBounded_isoForm_pow u1 w1 1) 0 (tau32 z)
  have h1 := (Equiv.ofBijective jD jD_bijective).summable_iff.mpr h
  have h2 : Summable (fun p ↦ ‖Fterm z p‖) := by
    convert h1.mul_left 4 using 1
    funext p
    have := dual_term z p
    have hn := congrArg norm this
    rw [norm_mul, norm_mul, norm_mul] at hn
    have hph : ‖cexp (2 * π * I * (((inner ℝ γ32 (jD p : E2)) : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [hph, mul_one] at hn
    simp only [Function.comp_apply, Equiv.ofBijective_apply, zero_add]
    have h4 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
    rw [h4] at hn
    rw [norm_mul]
    linarith
  exact h2.of_norm


theorem theta_S_tau (z : ℍ) :
    thetaSph L32 1 u1 w1 γ32 (ModularGroup.S • tau32 z) =
      (16 : ℂ)⁻¹ * ((-(tau32 z : ℂ)) * ((-I) * (tau32 z : ℂ))) * ((1 / 4) * ∑' p, Fterm z p) := by
  rw [thetaSph_S_smul_of_finrank_eq L32 finrank_E2 isSph_u1_w1 γ32 (tau32 z), covolume_L32]
  have h := (Equiv.ofBijective jD jD_bijective).tsum_eq
    (fun m : ZLattice.dual L32 ↦ isoForm u1 w1 (m : E2) ^ 1 *
      cexp (2 * π * I * ((inner ℝ γ32 (m : E2) : ℝ) : ℂ)) *
      cexp (π * I * (‖(m : E2)‖ ^ 2 : ℝ) * (tau32 z : ℂ)))
  rw [← h]
  simp only [Equiv.ofBijective_apply, dual_term]
  rw [tsum_mul_left]
  push_cast
  ring

theorem fricke_f32 (z : ℂ) (hz : 0 < z.im) :
    Miyake.fricke 2 32 (Miyake.qSeries f32C) z = Miyake.qSeries (fun m ↦ -f32C m) z := by
  set zz : ℍ := ⟨z, hz⟩ with hzz
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hS : ((ModularGroup.S • tau32 zz : ℍ) : ℂ) = -1 / (((32 : ℝ) : ℂ) * z) := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [coe_tau32, hzz, neg_div]
  have hneg : Miyake.qSeries (fun m ↦ -f32C m) z = -f32 zz := by
    simp only [Miyake.qSeries, neg_mul]
    rw [tsum_neg]; rfl
  have hsum := summable_Fterm zz
  have hS0 := hasSum_split zz hsum.hasSum
  have hθ := theta_S_tau zz
  have hfa : f32 zz = (1 + I) / 2 * thetaSph L32 1 u1 w1 γ32 zz := f32_eq_theta zz
  have hf2 : f32 (ModularGroup.S • tau32 zz) =
      (1 + I) / 2 * thetaSph L32 1 u1 w1 γ32 (ModularGroup.S • tau32 zz) := f32_eq_theta _
  have hq : Miyake.qSeries f32C (-1 / (((32 : ℝ) : ℂ) * z)) =
      f32 (ModularGroup.S • tau32 zz) := by
    rw [← hS]; rfl
  have hsq : ((√(32 : ℝ) : ℂ) * z) ^ (-(2 : ℤ)) = (32 * z ^ 2)⁻¹ := by
    rw [zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, mul_pow, ← Complex.ofReal_pow,
      Real.sq_sqrt (by norm_num)]
    push_cast; rfl
  have hzc : (zz : ℂ) = z := rfl
  have hI3 : I ^ 3 = -I := by rw [pow_succ, Complex.I_sq]; ring
  rw [Miyake.fricke, hq, hf2, hθ, hneg, hfa, hsq, hS0, coe_tau32, hzc]
  field_simp
  ring_nf
  simp only [hI3, Complex.I_sq, Complex.I_pow_four]
  ring

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
