/-
# The Fricke eigenvalue of $f_{64}$

* `fricke_f64`: in Miyake's normalization the Fricke involution $\omega_{64}$ acts on $f_{64}$ by $-1$.

**Proof.** `thetaSph_S_smul_of_finrank_eq` for $\theta_{\gamma+L}(-1/(64z))$, with
$L^\vee = \frac{1}{4\sqrt2}\mathbb Z \oplus \frac{1}{2\sqrt2}\mathbb Z$, expresses it through the series
$S = \sum_{(m, n) \in \mathbb Z^2} i^m (m + 2in)\,q^{m^2 + 4n^2}$ (`theta_S_tau64`): for
$y = (m/(4\sqrt2), n/(2\sqrt2))$ one has $\langle\gamma, y\rangle = m/4$, the spherical weight is
$(m + 2in)/(4\sqrt2)$ and $\|y\|^2/2 = (m^2 + 4n^2)/64$. Splitting by the residue of $m$ modulo $4$ (`decomp64`):
the terms with $m$ even cancel under $(m, n) \mapsto (-m, -n)$ (`Fterm64_neg`), and the terms with $m \equiv 3 \bmod 4$
are, after $(m, n) \mapsto (-m, -n)$, those with $m \equiv 1 \bmod 4$; both have factor $i$ in front of the series
of `Gterm64`. Hence $S = 2i f_{64}$ (`hasSum_split64`), and with $\tau = 64z$ the eigenvalue is
$(\sqrt2)^{-1}\cdot\tfrac1{16}\cdot i\cdot\tfrac{1}{4\sqrt2}\cdot 2i\cdot 64^2/64 \cdot \tfrac1{64}\cdot 64 = -1$.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.F32Fricke
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.F64Theta

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
open Complex MatrixGroups CongruenceSubgroup ModularForm
open scoped Real
open ModularFormsKB.Miyake.Sec4_9
local notation "ℍ" => UpperHalfPlane

/-! ### The Fricke series -/

/-- `I^m (m + 2 i n) e(2πi (m² + 4n²) z)`. -/
noncomputable def Fterm64 (z : ℍ) (p : ℤ × ℤ) : ℂ :=
  I ^ p.1 * ((p.1 : ℂ) + 2 * I * p.2) * cexp (2 * π * I * ((p.1 ^ 2 + 4 * p.2 ^ 2 : ℤ) : ℂ) * z)

theorem piece0_64 (z : ℍ) (p : ℤ × ℤ) :
    {p : ℤ × ℤ | p.1 % 4 = 1}.indicator (Fterm64 z) p = I * Gterm64 z p := by
  by_cases h : p.1 % 4 = 1
  · rw [Set.indicator_of_mem (by exact h), Gterm64, Set.indicator_of_mem (by exact h), Fterm64,
      I_zpow_one h]
    ring
  · rw [Set.indicator_of_notMem (by exact h), Gterm64, Set.indicator_of_notMem (by exact h)]; simp

theorem piece2_64 (z : ℍ) (p : ℤ × ℤ) :
    {p : ℤ × ℤ | (-p.1) % 4 = 1}.indicator (Fterm64 z) p = I * Gterm64 z (-p) := by
  by_cases h : (-p.1) % 4 = 1
  · have h' : (-p).1 % 4 = 1 := h
    rw [Set.indicator_of_mem (by exact h), Gterm64, Set.indicator_of_mem (by exact h'), Fterm64,
      I_zpow_three (by omega)]
    have hN : (-p).1 ^ 2 + 4 * (-p).2 ^ 2 = p.1 ^ 2 + 4 * p.2 ^ 2 := by simp only [Prod.fst_neg, Prod.snd_neg]; ring
    rw [hN]
    simp only [Prod.fst_neg, Prod.snd_neg]
    push_cast
    ring
  · have h' : ¬ (-p).1 % 4 = 1 := h
    rw [Set.indicator_of_notMem (by exact h), Gterm64, Set.indicator_of_notMem (by exact h')]; simp

theorem Fterm64_neg (z : ℍ) {p : ℤ × ℤ} (h : p.1 % 2 = 0) : Fterm64 z (-p) = -Fterm64 z p := by
  rw [Fterm64, Fterm64]
  simp only [Prod.fst_neg, Prod.snd_neg]
  rw [I_zpow_congr (m := -p.1) (n := p.1) (by omega)]
  have : (-p.1) ^ 2 + 4 * (-p.2) ^ 2 = p.1 ^ 2 + 4 * p.2 ^ 2 := by ring
  rw [this]
  push_cast
  ring

theorem Eneg64 (z : ℍ) (p : ℤ × ℤ) :
    {p : ℤ × ℤ | p.1 % 2 = 0}.indicator (Fterm64 z) (-p) =
      -({p : ℤ × ℤ | p.1 % 2 = 0}.indicator (Fterm64 z) p) := by
  by_cases hp : p.1 % 2 = 0
  · rw [Set.indicator_of_mem (show -p ∈ {p : ℤ × ℤ | p.1 % 2 = 0} by
      simp only [Set.mem_ofPred_eq, Prod.fst_neg]; omega),
      Set.indicator_of_mem (show p ∈ {p : ℤ × ℤ | p.1 % 2 = 0} from hp), Fterm64_neg z hp]
  · rw [Set.indicator_of_notMem (show -p ∉ {p : ℤ × ℤ | p.1 % 2 = 0} by
      simp only [Set.mem_ofPred_eq, Prod.fst_neg]; omega),
      Set.indicator_of_notMem (show p ∉ {p : ℤ × ℤ | p.1 % 2 = 0} from hp)]
    simp

theorem decomp64 (z : ℍ) (p : ℤ × ℤ) :
    Fterm64 z p = {p : ℤ × ℤ | p.1 % 2 = 0}.indicator (Fterm64 z) p +
      {p : ℤ × ℤ | p.1 % 4 = 1}.indicator (Fterm64 z) p +
      {p : ℤ × ℤ | (-p.1) % 4 = 1}.indicator (Fterm64 z) p := by
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs <;> first | (exfalso; omega) | simp

theorem hasSum_split64 (z : ℍ) {S0 a : ℂ} (hF : HasSum (Fterm64 z) S0) (hG : HasSum (Gterm64 z) a) :
    S0 = 2 * I * a := by
  have h0 : HasSum (fun p ↦ {p : ℤ × ℤ | p.1 % 4 = 1}.indicator (Fterm64 z) p) (I * a) := by
    simp_rw [piece0_64]; exact hG.mul_left I
  have h2 : HasSum (fun p ↦ {p : ℤ × ℤ | (-p.1) % 4 = 1}.indicator (Fterm64 z) p) (I * a) := by
    simp_rw [piece2_64]; exact ((Equiv.neg (ℤ × ℤ)).hasSum_iff.mpr hG).mul_left I
  have hE := hF.sub (h0.add h2)
  have hE' : HasSum (fun p ↦ {p : ℤ × ℤ | p.1 % 2 = 0}.indicator (Fterm64 z) p)
      (S0 - (I * a + I * a)) := by
    convert hE using 1
    funext p
    linear_combination (-1 : ℂ) * decomp64 z p
  have hneg : HasSum (fun p ↦ -({p : ℤ × ℤ | p.1 % 2 = 0}.indicator (Fterm64 z) p))
      (S0 - (I * a + I * a)) := by
    have := (Equiv.neg (ℤ × ℤ)).hasSum_iff.mpr hE'
    convert this using 1
    funext p
    simp only [Function.comp_apply, Equiv.neg_apply]
    exact (Eneg64 z p).symm
  have h4 := hE'.neg
  have h5 := hneg.unique h4
  have : S0 - (I * a + I * a) = 0 := by
    linear_combination (1 / 2 : ℂ) * h5
  linear_combination this

/-! ### The dual lattice -/

/-- The parametrisation `ℤ² → L^∨`. -/
noncomputable def jD64 (p : ℤ × ℤ) : ZLattice.dual L64 :=
  ⟨WithLp.toLp 2 ((p.1 : ℝ) / (4 * √2), (p.2 : ℝ) / (2 * √2)),
    mem_dual_L64.mpr ⟨p.1, p.2, div_mul_cancel₀ _ (by positivity), div_mul_cancel₀ _ (by positivity)⟩⟩

theorem jD64_bijective : Function.Bijective jD64 := by
  constructor
  · intro p q h
    have h1 := congrArg (fun v : ZLattice.dual L64 ↦ (v : E2).fst) h
    have h2 := congrArg (fun v : ZLattice.dual L64 ↦ (v : E2).snd) h
    simp only [jD64] at h1 h2
    have e1 : (p.1 : ℝ) = q.1 := by
      have hh := congrArg (· * (4 * √2)) h1
      simpa [div_mul_cancel₀, show (4 * √2 : ℝ) ≠ 0 by positivity] using hh
    have e2 : (p.2 : ℝ) = q.2 := by
      have hh := congrArg (· * (2 * √2)) h2
      simpa [div_mul_cancel₀, show (2 * √2 : ℝ) ≠ 0 by positivity] using hh
    ext <;> assumption_mod_cast
  · intro v
    obtain ⟨m, n, h1, h2⟩ := mem_dual_L64.mp v.2
    refine ⟨(m, n), ?_⟩
    apply Subtype.ext
    apply WithLp.ofLp_injective
    ext
    · simp only [jD64]; rw [← h1]; field_simp; rfl
    · simp only [jD64]; rw [← h2]; field_simp; rfl

/-- `τ = 64 z`. -/
noncomputable def tau64 (z : ℍ) : ℍ := ⟨64 * (z : ℂ), by
  have := z.im_pos
  simp [this]⟩

theorem coe_tau64 (z : ℍ) : (tau64 z : ℂ) = 64 * z := rfl

theorem dual_term64 (z : ℍ) (p : ℤ × ℤ) :
    isoForm u1 w1 (jD64 p : E2) ^ 1 * cexp (2 * π * I * (((inner ℝ γ64 (jD64 p : E2)) : ℝ) : ℂ)) *
      cexp (π * I * (‖(jD64 p : E2)‖ ^ 2 : ℝ) * (tau64 z : ℂ)) =
      ((4 * √2 : ℝ) : ℂ)⁻¹ * Fterm64 z p := by
  have hs : (√2 : ℝ) ≠ 0 := by positivity
  have hin : (inner ℝ γ64 (jD64 p : E2)) = ((p.1 : ℤ) : ℝ) / 4 := by
    simp [γ64, jD64, WithLp.prod_inner_apply]
    field_simp
  have hx : (jD64 p : E2).fst = (p.1 : ℝ) / (4 * √2) := by simp [jD64]
  have hy : (jD64 p : E2).snd = (p.2 : ℝ) / (2 * √2) := by simp [jD64]
  have hn : (jD64 p : E2).fst ^ 2 + (jD64 p : E2).snd ^ 2 =
      ((p.1 : ℝ) ^ 2 + 4 * (p.2 : ℝ) ^ 2) / 32 := by
    rw [hx, hy, div_pow, div_pow, mul_pow, mul_pow, sqrt_two_sq]
    field_simp
    ring
  rw [hin, exp_quarter, isoForm_u1_w1, norm_sq_E2, hn, hx, hy, Fterm64, coe_tau64, pow_one]
  have : cexp (π * I * (((p.1 : ℝ) ^ 2 + 4 * (p.2 : ℝ) ^ 2) / 32 : ℝ) * (64 * z : ℂ)) =
      cexp (2 * π * I * ((p.1 ^ 2 + 4 * p.2 ^ 2 : ℤ) : ℂ) * z) := by
    congr 1; push_cast; ring
  rw [this]
  have hsC : (√2 : ℂ) ≠ 0 := by rw [Ne, Complex.ofReal_eq_zero]; exact hs
  push_cast
  field_simp
  ring

theorem summable_Fterm64 (z : ℍ) : Summable (Fterm64 z) := by
  have h := summable_norm_thetaW (ZLattice.dual L64) (polyBounded_isoForm_pow u1 w1 1) 0 (tau64 z)
  have h1 := (Equiv.ofBijective jD64 jD64_bijective).summable_iff.mpr h
  have h2 : Summable (fun p ↦ ‖Fterm64 z p‖) := by
    convert h1.mul_left (4 * √2) using 1
    funext p
    have := dual_term64 z p
    have hn := congrArg norm this
    have hph : ‖cexp (2 * π * I * (((inner ℝ γ64 (jD64 p : E2)) : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    simp only [norm_mul, hph, mul_one] at hn
    simp only [Function.comp_apply, Equiv.ofBijective_apply, zero_add]
    have h4 : ‖((4 * √2 : ℝ) : ℂ)⁻¹‖ = (4 * √2)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [h4] at hn
    have hs : (0 : ℝ) < 4 * √2 := by positivity
    rw [norm_mul]
    field_simp at hn ⊢
    linarith
  exact h2.of_norm

theorem theta_S_tau64 (z : ℍ) :
    thetaSph L64 1 u1 w1 γ64 (ModularGroup.S • tau64 z) =
      (16 : ℂ)⁻¹ * ((-(tau64 z : ℂ)) * ((-I) * (tau64 z : ℂ))) *
        (((4 * √2 : ℝ) : ℂ)⁻¹ * ∑' p, Fterm64 z p) := by
  rw [thetaSph_S_smul_of_finrank_eq L64 finrank_E2 isSph_u1_w1 γ64 (tau64 z), covolume_L64]
  have h := (Equiv.ofBijective jD64 jD64_bijective).tsum_eq
    (fun m : ZLattice.dual L64 ↦ isoForm u1 w1 (m : E2) ^ 1 *
      cexp (2 * π * I * ((inner ℝ γ64 (m : E2) : ℝ) : ℂ)) *
      cexp (π * I * (‖(m : E2)‖ ^ 2 : ℝ) * (tau64 z : ℂ)))
  rw [← h]
  simp only [Equiv.ofBijective_apply, dual_term64]
  rw [tsum_mul_left]
  push_cast
  ring

theorem fricke_f64 (z : ℂ) (hz : 0 < z.im) :
    Miyake.fricke 2 64 (Miyake.qSeries f64C) z = Miyake.qSeries (fun m ↦ -f64C m) z := by
  set zz : ℍ := ⟨z, hz⟩ with hzz
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hS : ((ModularGroup.S • tau64 zz : ℍ) : ℂ) = -1 / (((64 : ℝ) : ℂ) * z) := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [coe_tau64, hzz, neg_div]
  have hsum := summable_Fterm64 zz
  have hG : HasSum (Gterm64 zz) (Miyake.qSeries f64C zz) := by
    rw [f64_eq_theta]; exact hasSum_Gterm64 zz
  have hS0 := hasSum_split64 zz hsum.hasSum hG
  have hneg : Miyake.qSeries (fun m ↦ -f64C m) z = -Miyake.qSeries f64C zz := by
    simp only [Miyake.qSeries, neg_mul]
    rw [tsum_neg]
  have hθ := theta_S_tau64 zz
  have hf2 : Miyake.qSeries f64C ((ModularGroup.S • tau64 zz : ℍ) : ℂ) =
      (√2 : ℂ)⁻¹ * thetaSph L64 1 u1 w1 γ64 (ModularGroup.S • tau64 zz) := f64_eq_theta _
  have hq : Miyake.qSeries f64C (-1 / (((64 : ℝ) : ℂ) * z)) =
      Miyake.qSeries f64C ((ModularGroup.S • tau64 zz : ℍ) : ℂ) := by
    rw [← hS]
  have hsq : ((√(64 : ℝ) : ℂ) * z) ^ (-(2 : ℤ)) = (64 * z ^ 2)⁻¹ := by
    rw [zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, mul_pow, ← Complex.ofReal_pow,
      Real.sq_sqrt (by norm_num)]
    push_cast; rfl
  have hs2 : (√2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, sqrt_two_sq]; push_cast; rfl
  have hsC : (√2 : ℂ) ≠ 0 := by
    intro h; rw [h] at hs2; norm_num at hs2
  have hzc : (zz : ℂ) = z := rfl
  rw [Miyake.fricke, hq, hf2, hθ, hneg, hsq, hS0, coe_tau64, hzc]
  push_cast
  field_simp
  ring_nf
  rw [hs2]
  simp only [Complex.I_sq]
  ring

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
