import ModularFormsKB.Miyake.HeckeTrick.FourierRows

/-!
# Miyake §7.2, proof of Theorem 7.2.9: collecting the Fourier terms

Miyake, *Modular Forms*, §7.2, pp. 284–285. Summing the row formula `heckeRow_pos` over $c \ge 1$: the terms
$m = 0$ give $D(s)y^{1-k-2s}$, the terms $m \ge 1$ give $A(s)y^{-s}\sum_n(\dots)$ and the terms $m \le -1$ give
$B(s)y^{-k-s}\sum_n(\dots)$ (grouping $(c,m)$ by $n = cm$); with the row $0$ (`heckeRow_zero`) this is Theorem 7.2.9.
-/

open MeasureTheory Set Filter Topology Complex
open scoped UpperHalfPlane
open scoped Real

noncomputable section

namespace ModularFormsKB.Miyake.HeckeTrick

open ModularFormsKB.Miyake.Wave2B

variable {L M : ℕ}

/-- Regrouping a double sum over `ℕ+ × ℕ+` by the product. -/
theorem hasSum_regroup {P : ℕ → ℕ → ℂ} (hP : Summable fun p : ℕ+ × ℕ+ ↦ P p.1 p.2) :
    HasSum (fun c : ℕ+ ↦ ∑' m : ℕ+, P c m)
      (∑' n : ℕ+, ∑ x ∈ (n : ℕ).divisorsAntidiagonal, P x.1 x.2) := by
  have h1 := hP.hasSum.sum_divisorsAntidiagonal
  rw [h1.tsum_eq, hP.tsum_prod]
  exact hP.prod.hasSum

/-- `m^a (cm)^b ≤ (cm)^(a⁺ + b⁺)`. -/
theorem rpow_mul_rpow_le (a b : ℝ) (c m : ℕ+) :
    ((m : ℕ) : ℝ) ^ a * (((c : ℕ) * (m : ℕ) : ℕ) : ℝ) ^ b ≤
      (((c : ℕ) * (m : ℕ) : ℕ) : ℝ) ^ (max a 0 + max b 0) := by
  have hm : (1 : ℝ) ≤ ((m : ℕ) : ℝ) := by exact_mod_cast m.pos
  have hn : (1 : ℝ) ≤ (((c : ℕ) * (m : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero c.ne_zero m.ne_zero)
  have hmn : ((m : ℕ) : ℝ) ≤ (((c : ℕ) * (m : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_left _ c.pos
  rw [Real.rpow_add (by linarith)]
  gcongr
  · calc ((m : ℕ) : ℝ) ^ a ≤ ((m : ℕ) : ℝ) ^ (max a 0) :=
        Real.rpow_le_rpow_of_exponent_le hm (le_max_left _ _)
      _ ≤ _ := Real.rpow_le_rpow (by linarith) hmn (le_max_right _ _)
  · exact le_max_left _ _

/-- Summability over `ℕ+ × ℕ+` of `m^a (cm)^b ρ^{cm}`. -/
theorem summable_rpow_geom (a b : ℝ) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable fun p : ℕ+ × ℕ+ ↦ ((p.2 : ℕ) : ℝ) ^ a * (((p.1 : ℕ) * (p.2 : ℕ) : ℕ) : ℝ) ^ b *
      ρ ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
  set K : ℕ := ⌈max a 0 + max b 0⌉₊ with hK
  have hs : Summable fun n : ℕ ↦ (n : ℝ) ^ K * (Real.sqrt ρ) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one K (by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (Real.sqrt_lt' one_pos).mpr (by simpa using h1))
  obtain ⟨B, hB⟩ := (hs.tendsto_atTop_zero.bddAbove_range)
  have hB' : ∀ n : ℕ, (n : ℝ) ^ K * (Real.sqrt ρ) ^ n ≤ B := fun n ↦ hB ⟨n, rfl⟩
  have hsq : Real.sqrt ρ < 1 := (Real.sqrt_lt' one_pos).mpr (by simpa using h1)
  refine ((summable_prod_mul_pow (𝕜 := ℝ) 0 (r := Real.sqrt ρ)
    (by rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]; exact hsq)).mul_left
      B).of_nonneg_of_le (fun p ↦ by positivity) fun p ↦ ?_
  have hn : (1 : ℝ) ≤ (((p.1 : ℕ) * (p.2 : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero p.1.ne_zero p.2.ne_zero)
  have e1 := rpow_mul_rpow_le a b p.1 p.2
  have e2 : (((p.1 : ℕ) * (p.2 : ℕ) : ℕ) : ℝ) ^ (max a 0 + max b 0) ≤
      (((p.1 : ℕ) * (p.2 : ℕ) : ℕ) : ℝ) ^ K := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hn (Nat.le_ceil _)
  have e3 := hB' ((p.1 : ℕ) * (p.2 : ℕ))
  have hρn : ρ ^ ((p.1 : ℕ) * (p.2 : ℕ)) = (Real.sqrt ρ) ^ ((p.1 : ℕ) * (p.2 : ℕ)) *
      (Real.sqrt ρ) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
    rw [← mul_pow, Real.mul_self_sqrt h0]
  have hq1 : (Real.sqrt ρ) ^ ((p.1 : ℕ) * (p.2 : ℕ)) ≤ 1 := pow_le_one₀ (Real.sqrt_nonneg _) hsq.le
  have hq0 : 0 ≤ (Real.sqrt ρ) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by positivity
  simp only [pow_zero, Nat.cast_one, one_mul]
  rw [hρn]
  calc _ ≤ ((((p.1 : ℕ) * (p.2 : ℕ) : ℕ) : ℝ) ^ K) * ((Real.sqrt ρ) ^ ((p.1 : ℕ) * (p.2 : ℕ)) *
      (Real.sqrt ρ) ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by gcongr; exact e1.trans e2
    _ = ((((p.1 : ℕ) * (p.2 : ℕ) : ℕ) : ℝ) ^ K * (Real.sqrt ρ) ^ ((p.1 : ℕ) * (p.2 : ℕ))) *
        (Real.sqrt ρ) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by ring
    _ ≤ B * (Real.sqrt ρ) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by gcongr

theorem ofReal_cpow_exp {a : ℝ} (ha : 0 < a) (w : ℂ) :
    (a : ℂ) ^ w = cexp (w * (Real.log a : ℝ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne'), Complex.ofReal_log ha.le,
    mul_comm]

theorem two_eq_exp : (2 : ℂ) = cexp ((Real.log 2 : ℝ)) := by
  rw [← Complex.ofReal_exp, Real.exp_log two_pos]; simp

theorem two_cpow (w : ℂ) : (2 : ℂ) ^ w = cexp (w * (Real.log 2 : ℝ)) := by
  have := ofReal_cpow_exp two_pos w
  simpa using this

theorem two_mul_exp (X : ℂ) : 2 * X = cexp ((Real.log 2 : ℝ)) * X := by
  rw [← two_eq_exp]

/-- The constants in the positive Fourier terms. -/
theorem scalar_pos (k : ℤ) (s : ℂ) {M y c m : ℝ} (hM : 0 < M) (hy : 0 < y) (hc : 0 < c) (hm : 0 < m) :
    2 * ((M : ℂ) ^ (-(k : ℂ) - 2 * s) *
      (((2 * π : ℝ) : ℂ) ^ ((k : ℂ) + s) * (((2 * (c * y / M) : ℝ) : ℂ) ^ (-s) *
        (m : ℂ) ^ ((k : ℂ) + s - 1)))) =
    (2 : ℂ) ^ (k + 1) * (((π / M : ℝ) : ℂ) ^ (s + k) * ((y : ℂ) ^ (-s) *
      ((m : ℂ) ^ ((k : ℂ) + 2 * s - 1) * ((c * m : ℝ) : ℂ) ^ (-s)))) := by
  have hπ := Real.pi_pos
  refine (two_mul_exp _).trans ?_
  rw [← Complex.cpow_intCast, ofReal_cpow_exp hM, ofReal_cpow_exp (by positivity : 0 < 2 * π),
    ofReal_cpow_exp (by positivity : 0 < 2 * (c * y / M)), ofReal_cpow_exp hm,
    ofReal_cpow_exp (by positivity : 0 < π / M), ofReal_cpow_exp hy, ofReal_cpow_exp hm,
    ofReal_cpow_exp (by positivity : 0 < c * m)]
  rw [show (2 : ℂ) ^ ((k + 1 : ℤ) : ℂ) = cexp (((k + 1 : ℤ) : ℂ) * (Real.log 2 : ℝ)) by
    rw [← Complex.ofReal_ofNat, ofReal_cpow_exp two_pos]]
  simp only [← Complex.exp_add]
  congr 1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) hM.ne',
    Real.log_mul hc.ne' hy.ne', Real.log_mul hc.ne' hm.ne']
  push_cast
  ring

theorem scalar_neg (k : ℤ) (s : ℂ) {M y c m : ℝ} (hM : 0 < M) (hy : 0 < y) (hc : 0 < c) (hm : 0 < m) :
    2 * ((M : ℂ) ^ (-(k : ℂ) - 2 * s) *
      (((2 * π : ℝ) : ℂ) ^ s * (((2 * (c * y / M) : ℝ) : ℂ) ^ (-((k : ℂ) + s)) *
        (m : ℂ) ^ (s - 1)))) =
    (2 : ℂ) ^ (1 - k) * (((π / M : ℝ) : ℂ) ^ s * ((y : ℂ) ^ (-(k : ℂ) - s) *
      ((m : ℂ) ^ ((k : ℂ) + 2 * s - 1) * ((c * m : ℝ) : ℂ) ^ (-s - k)))) := by
  have hπ := Real.pi_pos
  refine (two_mul_exp _).trans ?_
  rw [← Complex.cpow_intCast, ofReal_cpow_exp hM, ofReal_cpow_exp (by positivity : 0 < 2 * π),
    ofReal_cpow_exp (by positivity : 0 < 2 * (c * y / M)), ofReal_cpow_exp hm,
    ofReal_cpow_exp (by positivity : 0 < π / M), ofReal_cpow_exp hy, ofReal_cpow_exp hm,
    ofReal_cpow_exp (by positivity : 0 < c * m)]
  rw [show (2 : ℂ) ^ ((1 - k : ℤ) : ℂ) = cexp (((1 - k : ℤ) : ℂ) * (Real.log 2 : ℝ)) by
    rw [← Complex.ofReal_ofNat, ofReal_cpow_exp two_pos]]
  simp only [← Complex.exp_add]
  congr 1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) hM.ne',
    Real.log_mul hc.ne' hy.ne', Real.log_mul hc.ne' hm.ne']
  push_cast
  ring

theorem ofReal_eq_exp {a : ℝ} (ha : 0 < a) : (a : ℂ) = cexp ((Real.log a : ℝ)) := by
  rw [← Complex.ofReal_exp, Real.exp_log ha]

theorem scalar_const (k : ℤ) (s : ℂ) {M y c : ℝ} (hM : 0 < M) (hy : 0 < y) (hc : 0 < c) :
    (M : ℂ) ^ (-(k : ℂ) - 2 * s) * ((M : ℂ) * (((2 * π : ℝ) : ℂ) ^ ((k : ℂ) + s + s) *
      ((4 * π * (c * y / M) : ℝ) : ℂ) ^ (1 - ((k : ℂ) + s) - s))) =
    (π : ℂ) * ((2 : ℂ) ^ (2 - 2 * s - k) * ((c : ℂ) ^ (1 - (k : ℂ) - 2 * s) *
      (y : ℂ) ^ (1 - (k : ℂ) - 2 * s))) := by
  have hπ := Real.pi_pos
  rw [ofReal_cpow_exp hM, ofReal_cpow_exp (by positivity : 0 < 2 * π),
    ofReal_cpow_exp (by positivity : 0 < 4 * π * (c * y / M)), ofReal_cpow_exp hc,
    ofReal_cpow_exp hy, two_cpow, ofReal_eq_exp hM, ofReal_eq_exp hπ]
  simp only [← Complex.exp_add]
  congr 1
  have h4 : Real.log (4 * π * (c * y / M)) = 2 * Real.log 2 + Real.log π + (Real.log c + Real.log y - Real.log M) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_div (by positivity) hM.ne', Real.log_mul hc.ne' hy.ne']
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow]; push_cast; ring
  rw [Real.log_mul (by positivity) (by positivity), h4]
  push_cast
  ring

theorem hasSum_pnat_L [NeZero L] {s : ℂ} (hs : 1 < s.re) (χ : DirichletCharacter ℂ L) :
    HasSum (fun c : ℕ+ ↦ χ ((c : ℕ) : ZMod L) * ((c : ℕ) : ℂ) ^ (-s))
      (DirichletCharacter.LFunction χ s) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have h := (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs).hasSum
  have h2 : HasSum ((LSeries.term (fun n : ℕ ↦ χ n) s) ∘ ((↑) : ℕ+ → ℕ)) (LSeries (fun n : ℕ ↦ χ n) s) := by
    rw [Function.Injective.hasSum_iff PNat.coe_injective]
    · exact h
    · intro n hn
      have : n = 0 := by
        by_contra h0
        exact hn ⟨⟨n, Nat.pos_of_ne_zero h0⟩, rfl⟩
      simp [this]
  convert h2 using 1
  funext c
  simp only [Function.comp]
  rw [LSeries.term_of_ne_zero c.ne_zero, div_eq_mul_inv, Complex.cpow_neg]

theorem tsum_heckeRow_constTerm' {k : ℤ} {s : ℂ} (hs : 2 < (k : ℝ) + 2 * s.re) [NeZero L] [NeZero M]
    (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (z : ℍ) :
    HasSum (fun c : ℕ+ ↦ 2 * (χ ((c : ℕ) : ZMod L) * (M : ℂ) ^ (-(k : ℂ) - 2 * s) *
        (charFourier ψ 0 * xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s 0)))
      (heckeD k χ ψ s * (z.im : ℂ) ^ (1 - k - 2 * s)) := by
  classical
  by_cases hψ : ψ = 1
  swap
  · have h0 := charFourier_zero ψ
    simp only [hψ, if_false] at h0
    simp only [h0, heckeD, hψ, if_false, mul_zero, zero_mul]
    exact hasSum_zero
  subst hψ
  have h0 : charFourier (1 : DirichletCharacter ℂ M) 0 =
      (M : ℂ) * ∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹) := by
    rw [charFourier_zero]; simp
  have hy : 0 < z.im := z.im_pos
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hre : 1 < (2 * s + k - 1).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.intCast_re, Complex.one_re]
    linarith
  have hL := hasSum_pnat_L hre χ
  have hdup : Gamma ((2 * s + k - 1) / 2) * Gamma ((2 * s + k) / 2) =
      Gamma ((k : ℂ) + s + s - 1) * (2 : ℂ) ^ (2 - 2 * s - k) * (Real.sqrt π : ℂ) := by
    have := Complex.Gamma_mul_Gamma_add_half ((2 * s + k - 1) / 2)
    rw [show (2 * s + k - 1) / 2 + 1 / 2 = (2 * s + k) / 2 by ring,
      show 1 - 2 * ((2 * s + k - 1) / 2) = 2 - 2 * s - k by ring,
      show 2 * ((2 * s + k - 1) / 2) = (k : ℂ) + s + s - 1 by ring] at this
    exact this
  have hsq : ((Real.sqrt π : ℝ) : ℂ) * ((Real.sqrt π : ℝ) : ℂ) = (π : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have eI : (I : ℂ) ^ (s - ((k : ℂ) + s)) = I ^ (-k) := by
    rw [show s - ((k : ℂ) + s) = ((-k : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
  have hγ : Gamma (s + k) = Gamma ((k : ℂ) + s) := by rw [add_comm]
  set Pi : ℂ := ∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹) with hPi
  set K0 : ℂ := 2 * Pi * I ^ (-k) * (Gamma ((k : ℂ) + s))⁻¹ * (Gamma s)⁻¹ * Gamma ((k : ℂ) + s + s - 1) *
    (π : ℂ) * (2 : ℂ) ^ (2 - 2 * s - k) * (z.im : ℂ) ^ (1 - (k : ℂ) - 2 * s) with hK0
  convert hL.mul_left K0 using 1
  · funext c
    have hc : (0 : ℝ) < ((c : ℕ) : ℝ) := by exact_mod_cast c.pos
    have sc := scalar_const k s hM hy hc
    simp only [Complex.ofReal_natCast] at sc
    rw [h0, xiCont, if_neg (lt_irrefl _), if_pos rfl, eI,
      show -(2 * s + k - 1) = 1 - (k : ℂ) - 2 * s by ring]
    linear_combination (2 * χ ((c : ℕ) : ZMod L) * Pi * (Gamma ((k : ℂ) + s))⁻¹ * (Gamma s)⁻¹ *
      Gamma ((k : ℂ) + s + s - 1) * I ^ (-k)) * sc
  · rw [heckeD, if_pos rfl, hγ]
    linear_combination ((2 * (Real.sqrt π : ℂ) * I ^ (-k) * Pi * (Gamma s)⁻¹ * (Gamma ((k : ℂ) + s))⁻¹ *
      DirichletCharacter.LFunction χ (2 * s + k - 1) * (z.im : ℂ) ^ (1 - (k : ℂ) - 2 * s))) * hdup
      + (2 * I ^ (-k) * Pi * (Gamma ((k : ℂ) + s))⁻¹ * (Gamma s)⁻¹ * Gamma ((k : ℂ) + s + s - 1) *
        (2 : ℂ) ^ (2 - 2 * s - k) * (z.im : ℂ) ^ (1 - (k : ℂ) - 2 * s) *
        DirichletCharacter.LFunction χ (2 * s + k - 1)) * hsq

theorem summable_generic {χ' g : ℕ → ℂ} {G : ℝ} (hχ : ∀ c, ‖χ' c‖ ≤ 1) (hg : ∀ m, ‖g m‖ ≤ G)
    (u v : ℂ) {q : ℕ → ℂ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hq : ∀ n, ‖q n‖ ≤ ρ ^ n)
    (α β : ℂ) {y M : ℝ} (hy : 0 < y) (hM : 0 < M) :
    Summable fun p : ℕ+ × ℕ+ ↦ (χ' p.1 * ((p.2 : ℕ) : ℂ) ^ u * g p.2) *
      ((((p.1 : ℕ) * (p.2 : ℕ) : ℕ) : ℂ) ^ v * q ((p.1 : ℕ) * (p.2 : ℕ)) *
        omega (4 * π * y * (((p.1 : ℕ) * (p.2 : ℕ) : ℕ) : ℝ) / M : ℝ) α β) := by
  obtain ⟨A, hA, B, hB, hω⟩ := omega_bound (T := {((α, β) : ℂ × ℂ)}) isCompact_singleton
  set Y0 : ℝ := 4 * π * y / M with hY0
  have hπ := Real.pi_pos
  have hY0pos : 0 < Y0 := by positivity
  have hG : 0 ≤ G := (norm_nonneg _).trans (hg 0)
  refine ((summable_rpow_geom u.re v.re hρ0 hρ1).mul_left
    (G * (A * (1 + Y0 ^ (-B))))).of_norm_bounded fun p ↦ ?_
  have hmpos : 0 < (p.2 : ℕ) := p.2.pos
  have hcm : 0 < (p.1 : ℕ) * (p.2 : ℕ) := Nat.mul_pos p.1.pos p.2.pos
  have hcmR : (1 : ℝ) ≤ (((p.1 : ℕ) * (p.2 : ℕ) : ℕ) : ℝ) := by exact_mod_cast hcm
  have hω' := hω (4 * π * y * (((p.1 : ℕ) * (p.2 : ℕ) : ℕ) : ℝ) / M) (by positivity) (α, β) rfl
  have hle : Y0 ≤ 4 * π * y * (((p.1 : ℕ) * (p.2 : ℕ) : ℕ) : ℝ) / M := by
    have : 4 * π * y ≤ 4 * π * y * (((p.1 : ℕ) * (p.2 : ℕ) : ℕ) : ℝ) :=
      le_mul_of_one_le_right (by positivity) hcmR
    rw [hY0]
    exact div_le_div_of_nonneg_right this hM.le
  have hω2 : ‖omega (4 * π * y * (((p.1 : ℕ) * (p.2 : ℕ) : ℕ) : ℝ) / M : ℝ) α β‖ ≤
      A * (1 + Y0 ^ (-B)) := by
    refine hω'.trans ?_
    have := Real.rpow_le_rpow_of_nonpos hY0pos hle (neg_nonpos.mpr hB.le)
    exact mul_le_mul_of_nonneg_left (by linarith) hA.le
  have hA0 : 0 ≤ A * (1 + Y0 ^ (-B)) := by positivity
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
    Complex.norm_natCast_cpow_of_pos hmpos, Complex.norm_natCast_cpow_of_pos hcm]
  have e1 : ‖χ' p.1‖ * ((p.2 : ℕ) : ℝ) ^ u.re * ‖g p.2‖ ≤ 1 * ((p.2 : ℕ) : ℝ) ^ u.re * G := by
    gcongr
    · exact hχ _
    · exact hg _
  have e2 := hq ((p.1 : ℕ) * (p.2 : ℕ))
  calc _ ≤ (1 * ((p.2 : ℕ) : ℝ) ^ u.re * G) * ((((p.1 : ℕ) * (p.2 : ℕ) : ℕ) : ℝ) ^ v.re *
        ρ ^ ((p.1 : ℕ) * (p.2 : ℕ)) * (A * (1 + Y0 ^ (-B)))) := by
        gcongr
    _ = _ := by ring

theorem norm_gaussCoeff_le {m : ℕ} (χ₀ : DirichletCharacter ℂ m) {l : ℕ} (hl : l ≠ 0) (n : ℕ) :
    ‖gaussCoeff χ₀ l n‖ ≤ ∑ d ∈ l.divisors, (d : ℝ) := by
  unfold gaussCoeff
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun d hd ↦ ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd hl (Nat.gcd_dvd_left l n))
      (fun _ _ _ ↦ Nat.cast_nonneg _))
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast]
  have h1 : ‖((ArithmeticFunction.moebius (l / d) : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have h2 := DirichletCharacter.norm_le_one χ₀ ((l / d : ℕ) : ZMod m)
  have h3 : ‖(starRingEnd ℂ) (χ₀ ((n / d : ℕ) : ZMod m))‖ ≤ 1 := by
    rw [RCLike.norm_conj]; exact DirichletCharacter.norm_le_one _ _
  calc (d : ℝ) * ‖((ArithmeticFunction.moebius (l / d) : ℤ) : ℂ)‖ * ‖χ₀ ((l / d : ℕ) : ZMod m)‖ *
        ‖(starRingEnd ℂ) (χ₀ ((n / d : ℕ) : ZMod m))‖ ≤ d * 1 * 1 * 1 := by gcongr
    _ = d := by ring

/-- `‖e^{2πi n z/M}‖ = ρ^n` with `ρ = e^{-2π y/M}`. -/
theorem norm_cexp_q (z : ℍ) (n : ℕ) (M : ℕ) :
    ‖cexp (2 * π * I * (n : ℂ) * (z : ℂ) / M)‖ = (Real.exp (-(2 * π * z.im / M))) ^ n := by
  rw [Complex.norm_exp]
  have : 2 * π * I * (n : ℂ) * (z : ℂ) / M = ((2 * π * n / M : ℝ) : ℂ) * (I * (z : ℂ)) := by
    push_cast; ring
  rw [this, Complex.re_ofReal_mul, ← Real.exp_nat_mul]
  congr 1
  simp
  ring

theorem norm_cexp_qbar (z : ℍ) (n : ℕ) (M : ℕ) :
    ‖cexp (-2 * π * I * (n : ℂ) * (starRingEnd ℂ) (z : ℂ) / M)‖ = (Real.exp (-(2 * π * z.im / M))) ^ n := by
  rw [Complex.norm_exp]
  have : -2 * π * I * (n : ℂ) * (starRingEnd ℂ) (z : ℂ) / M =
      ((-2 * π * n / M : ℝ) : ℂ) * (I * (starRingEnd ℂ) (z : ℂ)) := by
    push_cast; ring
  rw [this, Complex.re_ofReal_mul, ← Real.exp_nat_mul]
  congr 1
  simp
  ring

/-- The `(c, m)` term of the first series. -/
def posP (k : ℤ) (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (z : ℍ) (s : ℂ)
    (c m : ℕ) : ℂ :=
  (χ (c : ZMod L) * (m : ℂ) ^ ((k : ℂ) + 2 * s - 1) *
      gaussCoeff ψ.primitiveCharacter (M / ψ.conductor) m) *
    (((c * m : ℕ) : ℂ) ^ (-s) * cexp (2 * π * I * ((c * m : ℕ) : ℂ) * z / M) *
      omega (4 * π * z.im * ((c * m : ℕ) : ℝ) / M : ℝ) ((k : ℂ) + s) s)

/-- The `(c, m)` term of the second series. -/
def negP (k : ℤ) (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (z : ℍ) (s : ℂ)
    (c m : ℕ) : ℂ :=
  (χ (c : ZMod L) * (m : ℂ) ^ ((k : ℂ) + 2 * s - 1) *
      gaussCoeff ψ.primitiveCharacter (M / ψ.conductor) m) *
    (((c * m : ℕ) : ℂ) ^ (-s - k) *
      cexp (-2 * π * I * ((c * m : ℕ) : ℂ) * (starRingEnd ℂ) (z : ℂ) / M) *
      omega (4 * π * z.im * ((c * m : ℕ) : ℝ) / M : ℝ) s ((k : ℂ) + s))

theorem exists_gauss_bound [NeZero M] (ψ : DirichletCharacter ℂ M) :
    ∃ G : ℝ, ∀ m : ℕ, ‖gaussCoeff ψ.primitiveCharacter (M / ψ.conductor) m‖ ≤ G := by
  have hl : M / ψ.conductor ≠ 0 := by
    have h1 : ψ.conductor ≤ M := Nat.le_of_dvd (NeZero.pos M) ψ.conductor_dvd_level
    exact (Nat.div_pos h1 (Nat.pos_of_ne_zero ψ.conductor_ne_zero)).ne'
  exact ⟨_, fun m ↦ norm_gaussCoeff_le _ hl m⟩

theorem rho_bounds [NeZero M] (z : ℍ) :
    0 ≤ Real.exp (-(2 * π * z.im / M)) ∧ Real.exp (-(2 * π * z.im / M)) < 1 := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hy := z.im_pos
  have hπ := Real.pi_pos
  refine ⟨(Real.exp_pos _).le, ?_⟩
  have : 0 < 2 * π * z.im / M := by positivity
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by linarith)

theorem summable_posP [NeZero M] (k : ℤ) (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (z : ℍ) (s : ℂ) : Summable fun p : ℕ+ × ℕ+ ↦ posP k χ ψ z s p.1 p.2 := by
  obtain ⟨G, hG⟩ := exists_gauss_bound ψ
  obtain ⟨h0, h1⟩ := rho_bounds (M := M) z
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  exact summable_generic (χ' := fun c ↦ χ (c : ZMod L)) (fun c ↦ DirichletCharacter.norm_le_one _ _) hG
    ((k : ℂ) + 2 * s - 1) (-s) (q := fun n ↦ cexp (2 * π * I * (n : ℂ) * z / M)) h0 h1
    (fun n ↦ (norm_cexp_q z n M).le) ((k : ℂ) + s) s z.im_pos hM

theorem summable_negP [NeZero M] (k : ℤ) (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (z : ℍ) (s : ℂ) : Summable fun p : ℕ+ × ℕ+ ↦ negP k χ ψ z s p.1 p.2 := by
  obtain ⟨G, hG⟩ := exists_gauss_bound ψ
  obtain ⟨h0, h1⟩ := rho_bounds (M := M) z
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  exact summable_generic (χ' := fun c ↦ χ (c : ZMod L)) (fun c ↦ DirichletCharacter.norm_le_one _ _) hG
    ((k : ℂ) + 2 * s - 1) (-s - k)
    (q := fun n ↦ cexp (-2 * π * I * (n : ℂ) * (starRingEnd ℂ) (z : ℂ) / M)) h0 h1
    (fun n ↦ (norm_cexp_qbar z n M).le) s ((k : ℂ) + s) z.im_pos hM

theorem antidiag_posP (k : ℤ) (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (z : ℍ) (s : ℂ) (n : ℕ+) :
    ∑ x ∈ (n : ℕ).divisorsAntidiagonal, posP k χ ψ z s x.1 x.2 = heckeTermA k χ ψ z s n := by
  have h1 : ∑ x ∈ (n : ℕ).divisorsAntidiagonal, posP k χ ψ z s x.1 x.2 =
      (∑ x ∈ (n : ℕ).divisorsAntidiagonal, χ (x.1 : ZMod L) * (x.2 : ℂ) ^ ((k : ℂ) + 2 * s - 1) *
        gaussCoeff ψ.primitiveCharacter (M / ψ.conductor) x.2) *
      (((n : ℕ) : ℂ) ^ (-s) * cexp (2 * π * I * ((n : ℕ) : ℂ) * z / M) *
        omega (4 * π * z.im * ((n : ℕ) : ℝ) / M : ℝ) ((k : ℂ) + s) s) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    simp only [posP]
    rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
  rw [h1, Nat.sum_divisorsAntidiagonal' (f := fun a b ↦ χ (a : ZMod L) * (b : ℂ) ^ ((k : ℂ) + 2 * s - 1) *
        gaussCoeff ψ.primitiveCharacter (M / ψ.conductor) b)]
  simp only [heckeTermA, heckeCoeff]
  ring

theorem antidiag_negP (k : ℤ) (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (z : ℍ) (s : ℂ) (n : ℕ+) :
    ∑ x ∈ (n : ℕ).divisorsAntidiagonal, negP k χ ψ z s x.1 x.2 = heckeTermB k χ ψ z s n := by
  have h1 : ∑ x ∈ (n : ℕ).divisorsAntidiagonal, negP k χ ψ z s x.1 x.2 =
      (∑ x ∈ (n : ℕ).divisorsAntidiagonal, χ (x.1 : ZMod L) * (x.2 : ℂ) ^ ((k : ℂ) + 2 * s - 1) *
        gaussCoeff ψ.primitiveCharacter (M / ψ.conductor) x.2) *
      (((n : ℕ) : ℂ) ^ (-s - k) *
        cexp (-2 * π * I * ((n : ℕ) : ℂ) * (starRingEnd ℂ) (z : ℂ) / M) *
        omega (4 * π * z.im * ((n : ℕ) : ℝ) / M : ℝ) s ((k : ℂ) + s)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    simp only [negP]
    rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
  rw [h1, Nat.sum_divisorsAntidiagonal' (f := fun a b ↦ χ (a : ZMod L) * (b : ℂ) ^ ((k : ℂ) + 2 * s - 1) *
        gaussCoeff ψ.primitiveCharacter (M / ψ.conductor) b)]
  simp only [heckeTermB, heckeCoeff]
  ring

theorem pos_term [NeZero M] (k : ℤ) (s : ℂ) (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (z : ℍ) (c m : ℕ+) :
    2 * (χ ((c : ℕ) : ZMod L) * (M : ℂ) ^ (-(k : ℂ) - 2 * s) *
      (cexp (2 * π * I * ((m : ℕ) : ℤ) * (c : ℕ) * z.re / M) * charFourier ψ ((m : ℕ) : ℤ) *
        xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s ((m : ℕ) : ℤ))) =
      heckeA k ψ s * (z.im : ℂ) ^ (-s) * posP k χ ψ z s c m := by
  haveI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  have hy := z.im_pos
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hcR : (0 : ℝ) < ((c : ℕ) : ℝ) := by exact_mod_cast c.pos
  have hmR : (0 : ℝ) < ((m : ℕ) : ℝ) := by exact_mod_cast m.pos
  have hπ := Real.pi_pos
  have hcF := charFourier_natCast ψ (m : ℕ)
  simp only [Int.cast_natCast] at hcF ⊢
  rw [xiCont, if_pos (by exact_mod_cast hmR), hcF]
  have hE : cexp (2 * π * I * (((c : ℕ) * (m : ℕ) : ℕ) : ℂ) * z / M) =
      cexp (2 * π * I * ((m : ℕ) : ℂ) * (c : ℕ) * z.re / M) *
        ((Real.exp (-2 * π * (((c : ℕ) : ℝ) * z.im / M) * ((m : ℕ) : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    have hz : (z : ℂ) = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im _).symm
    rw [hz]
    push_cast
    linear_combination (2 * π * ((m : ℕ) : ℂ) * ((c : ℕ) : ℂ) * (z.im : ℂ) / M) * Complex.I_sq
  have eω : (4 * π * (((c : ℕ) : ℝ) * z.im / M) * ((m : ℕ) : ℝ) : ℝ) =
      4 * π * z.im * (((c : ℕ) * (m : ℕ) : ℕ) : ℝ) / M := by
    push_cast; ring
  have eI : (I : ℂ) ^ (s - ((k : ℂ) + s)) = I ^ (-k) := by
    rw [show s - ((k : ℂ) + s) = ((-k : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
  have hγ : Gamma (s + k) = Gamma ((k : ℂ) + s) := by rw [add_comm]
  have sc := scalar_pos k s hM hy hcR hmR
  have ecm : (((c : ℕ) : ℝ) * ((m : ℕ) : ℝ) : ℝ) = (((c : ℕ) * (m : ℕ) : ℕ) : ℝ) := by push_cast; ring
  rw [ecm] at sc
  simp only [Complex.ofReal_natCast] at sc
  rw [eω, eI]
  simp only [posP, heckeA, hγ, hE]
  simp only [Complex.ofReal_natCast]
  linear_combination (χ ((c : ℕ) : ZMod L) * gaussSum ψ.primitiveCharacter ZMod.stdAddChar *
    gaussCoeff ψ.primitiveCharacter (M / ψ.conductor) (m : ℕ) * I ^ (-k) * (Gamma ((k : ℂ) + s))⁻¹ *
    cexp (2 * π * I * ((m : ℕ) : ℂ) * (c : ℕ) * z.re / M) *
    ((Real.exp (-2 * π * (((c : ℕ) : ℝ) * z.im / M) * ((m : ℕ) : ℝ)) : ℝ) : ℂ) *
    omega (4 * π * z.im * (((c : ℕ) * (m : ℕ) : ℕ) : ℝ) / M : ℝ) ((k : ℂ) + s) s) * sc

theorem neg_term [NeZero M] (k : ℤ) (s : ℂ) (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (z : ℍ) (c m : ℕ+) :
    2 * (χ ((c : ℕ) : ZMod L) * (M : ℂ) ^ (-(k : ℂ) - 2 * s) *
      (cexp (2 * π * I * (-((m : ℕ) : ℤ)) * (c : ℕ) * z.re / M) * charFourier ψ (-((m : ℕ) : ℤ)) *
        xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s (-((m : ℕ) : ℤ)))) =
      heckeB k ψ s * (z.im : ℂ) ^ (-k - s) * negP k χ ψ z s c m := by
  haveI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  have hy := z.im_pos
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hcR : (0 : ℝ) < ((c : ℕ) : ℝ) := by exact_mod_cast c.pos
  have hmR : (0 : ℝ) < ((m : ℕ) : ℝ) := by exact_mod_cast m.pos
  have hπ := Real.pi_pos
  have hcF := charFourier_natCast ψ (m : ℕ)
  rw [charFourier_neg, hcF]
  simp only [Int.cast_natCast, Int.cast_neg]
  rw [xiCont, if_neg (by linarith), if_neg (by linarith), abs_neg, abs_of_pos hmR]
  have hE : cexp (-2 * π * I * (((c : ℕ) * (m : ℕ) : ℕ) : ℂ) * (starRingEnd ℂ) (z : ℂ) / M) =
      cexp (2 * π * I * (-((m : ℕ) : ℂ)) * (c : ℕ) * z.re / M) *
        ((Real.exp (-2 * π * (((c : ℕ) : ℝ) * z.im / M) * ((m : ℕ) : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    have hz : (starRingEnd ℂ) (z : ℂ) = (z.re : ℂ) - (z.im : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [hz]
    push_cast
    linear_combination (2 * π * ((m : ℕ) : ℂ) * ((c : ℕ) : ℂ) * (z.im : ℂ) / M) * Complex.I_sq
  have eω : (4 * π * (((c : ℕ) : ℝ) * z.im / M) * ((m : ℕ) : ℝ) : ℝ) =
      4 * π * z.im * (((c : ℕ) * (m : ℕ) : ℕ) : ℝ) / M := by
    push_cast; ring
  have eI : (I : ℂ) ^ (s - ((k : ℂ) + s)) = I ^ (-k) := by
    rw [show s - ((k : ℂ) + s) = ((-k : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
  have sc := scalar_neg k s hM hy hcR hmR
  have ecm : (((c : ℕ) : ℝ) * ((m : ℕ) : ℝ) : ℝ) = (((c : ℕ) * (m : ℕ) : ℕ) : ℝ) := by push_cast; ring
  rw [ecm] at sc
  simp only [Complex.ofReal_natCast] at sc
  rw [eω, eI]
  simp only [negP, heckeB, hE]
  simp only [Complex.ofReal_natCast]
  linear_combination (χ ((c : ℕ) : ZMod L) * ψ (-1) * gaussSum ψ.primitiveCharacter ZMod.stdAddChar *
    gaussCoeff ψ.primitiveCharacter (M / ψ.conductor) (m : ℕ) * I ^ (-k) * (Gamma s)⁻¹ *
    cexp (2 * π * I * (-((m : ℕ) : ℂ)) * (c : ℕ) * z.re / M) *
    ((Real.exp (-2 * π * (((c : ℕ) : ℝ) * z.im / M) * ((m : ℕ) : ℝ)) : ℝ) : ℂ) *
    omega (4 * π * z.im * (((c : ℕ) * (m : ℕ) : ℕ) : ℝ) / M : ℝ) s ((k : ℂ) + s)) * sc

theorem tsum_heckeRow_posTerm' {k : ℤ} {s : ℂ} (hs : 2 < (k : ℝ) + 2 * s.re) [NeZero L] [NeZero M]
    (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (z : ℍ) :
    HasSum (fun c : ℕ+ ↦ 2 * (χ ((c : ℕ) : ZMod L) * (M : ℂ) ^ (-(k : ℂ) - 2 * s) *
        ∑' m : ℕ+, cexp (2 * π * I * ((m : ℕ) : ℤ) * (c : ℕ) * z.re / M) * charFourier ψ ((m : ℕ) : ℤ) *
            xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s ((m : ℕ) : ℤ)))
      (heckeA k ψ s * (z.im : ℂ) ^ (-s) * ∑' n : ℕ+, heckeTermA k χ ψ z s n) := by
  have hR := (hasSum_regroup (P := posP k χ ψ z s) (summable_posP k χ ψ z s)).mul_left
    (heckeA k ψ s * (z.im : ℂ) ^ (-s))
  rw [tsum_congr (antidiag_posP k χ ψ z s)] at hR
  convert hR using 1
  funext c
  simp only [← tsum_mul_left]
  exact tsum_congr fun m ↦ pos_term k s χ ψ z c m

theorem tsum_heckeRow_negTerm' {k : ℤ} {s : ℂ} (hs : 2 < (k : ℝ) + 2 * s.re) [NeZero L] [NeZero M]
    (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (z : ℍ) :
    HasSum (fun c : ℕ+ ↦ 2 * (χ ((c : ℕ) : ZMod L) * (M : ℂ) ^ (-(k : ℂ) - 2 * s) *
        ∑' m : ℕ+, cexp (2 * π * I * (-((m : ℕ) : ℤ)) * (c : ℕ) * z.re / M) *
          charFourier ψ (-((m : ℕ) : ℤ)) *
            xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s (-((m : ℕ) : ℤ))))
      (heckeB k ψ s * (z.im : ℂ) ^ (-k - s) * ∑' n : ℕ+, heckeTermB k χ ψ z s n) := by
  have hR := (hasSum_regroup (P := negP k χ ψ z s) (summable_negP k χ ψ z s)).mul_left
    (heckeB k ψ s * (z.im : ℂ) ^ (-k - s))
  rw [tsum_congr (antidiag_negP k χ ψ z s)] at hR
  convert hR using 1
  funext c
  simp only [← tsum_mul_left]
  exact tsum_congr fun m ↦ neg_term k s χ ψ z c m

theorem cpow_M_ne_zero [NeZero M] (w : ℂ) : (M : ℂ) ^ w ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne M))]
  exact Complex.exp_ne_zero _

theorem summable_pos_slice [NeZero M] (k : ℤ) (s : ℂ) (ψ : DirichletCharacter ℂ M) (z : ℍ) (c : ℕ+) :
    Summable fun m : ℕ+ ↦ cexp (2 * π * I * ((m : ℕ) : ℤ) * (c : ℕ) * z.re / M) *
      charFourier ψ ((m : ℕ) : ℤ) * xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s ((m : ℕ) : ℤ) := by
  have h := (summable_posP k (1 : DirichletCharacter ℂ 1) ψ z s).prod_factor c
  refine (h.mul_left (heckeA k ψ s * (z.im : ℂ) ^ (-s) / (2 * (M : ℂ) ^ (-(k : ℂ) - 2 * s)))).congr
    fun m ↦ ?_
  have := pos_term k s (1 : DirichletCharacter ℂ 1) ψ z c m
  have hMe := cpow_M_ne_zero (M := M) (-(k : ℂ) - 2 * s)
  have h1 : (1 : DirichletCharacter ℂ 1) (((c : ℕ) : ℕ) : ZMod 1) = 1 := by
    rw [show (((c : ℕ) : ℕ) : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
  rw [h1, one_mul] at this
  rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero two_ne_zero hMe)]
  linear_combination (-1 : ℂ) * this

theorem summable_neg_slice [NeZero M] (k : ℤ) (s : ℂ) (ψ : DirichletCharacter ℂ M) (z : ℍ) (c : ℕ+) :
    Summable fun m : ℕ+ ↦ cexp (2 * π * I * (-((m : ℕ) : ℤ)) * (c : ℕ) * z.re / M) *
      charFourier ψ (-((m : ℕ) : ℤ)) * xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s (-((m : ℕ) : ℤ)) := by
  have h := (summable_negP k (1 : DirichletCharacter ℂ 1) ψ z s).prod_factor c
  refine (h.mul_left (heckeB k ψ s * (z.im : ℂ) ^ (-k - s) / (2 * (M : ℂ) ^ (-(k : ℂ) - 2 * s)))).congr
    fun m ↦ ?_
  have := neg_term k s (1 : DirichletCharacter ℂ 1) ψ z c m
  have hMe := cpow_M_ne_zero (M := M) (-(k : ℂ) - 2 * s)
  have h1 : (1 : DirichletCharacter ℂ 1) (((c : ℕ) : ℕ) : ZMod 1) = 1 := by
    rw [show (((c : ℕ) : ℕ) : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
  rw [h1, one_mul] at this
  rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero two_ne_zero hMe)]
  linear_combination (-1 : ℂ) * this

theorem tsum_row_split [NeZero M] (k : ℤ) (s : ℂ) (ψ : DirichletCharacter ℂ M) (z : ℍ) (c : ℕ+) :
    (∑' m : ℤ, if m = 0 then (0 : ℂ) else
          cexp (2 * π * I * m * (c : ℕ) * z.re / M) * charFourier ψ m *
            xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s m) =
      (∑' m : ℕ+, cexp (2 * π * I * ((m : ℕ) : ℤ) * (c : ℕ) * z.re / M) * charFourier ψ ((m : ℕ) : ℤ) *
            xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s ((m : ℕ) : ℤ)) +
        ∑' m : ℕ+, cexp (2 * π * I * (-((m : ℕ) : ℤ)) * (c : ℕ) * z.re / M) *
          charFourier ψ (-((m : ℕ) : ℤ)) *
            xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s (-((m : ℕ) : ℤ)) := by
  set g : ℤ → ℂ := fun m ↦ if m = 0 then (0 : ℂ) else
          cexp (2 * π * I * m * (c : ℕ) * z.re / M) * charFourier ψ m *
            xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s m with hg
  have hpos : ∀ m : ℕ+, g ((m : ℕ) : ℤ) = cexp (2 * π * I * ((m : ℕ) : ℤ) * (c : ℕ) * z.re / M) *
      charFourier ψ ((m : ℕ) : ℤ) * xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s ((m : ℕ) : ℤ) := by
    intro m
    have : ((m : ℕ) : ℤ) ≠ 0 := by exact_mod_cast m.ne_zero
    simp only [hg, this, if_false]
  have hneg : ∀ m : ℕ+, g (-((m : ℕ) : ℤ)) = cexp (2 * π * I * (-((m : ℕ) : ℤ)) * (c : ℕ) * z.re / M) *
      charFourier ψ (-((m : ℕ) : ℤ)) * xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s (-((m : ℕ) : ℤ)) := by
    intro m
    have : -((m : ℕ) : ℤ) ≠ 0 := by simpa using m.ne_zero
    simp only [hg, this, if_false, Int.cast_neg, Int.cast_natCast]
  have h1 : Summable fun n : ℕ+ ↦ g ((n : ℕ) : ℤ) :=
    (summable_pos_slice k s ψ z c).congr fun m ↦ (hpos m).symm
  have h2 : Summable fun n : ℕ+ ↦ g (-((n : ℕ) : ℤ)) :=
    (summable_neg_slice k s ψ z c).congr fun m ↦ (hneg m).symm
  have hsum : Summable g := by
    rw [summable_int_iff_summable_nat_and_neg]
    constructor
    · exact (summable_pnat_iff_summable_nat (f := fun n : ℕ ↦ g (n : ℤ))).mp h1
    · exact (summable_pnat_iff_summable_nat (f := fun n : ℕ ↦ g (-(n : ℤ)))).mp h2
  rw [tsum_int_eq_zero_add_tsum_pnat hsum]
  simp only [hg, if_true, zero_add]
  exact congrArg₂ _ (tsum_congr hpos) (tsum_congr hneg)

/-- **Miyake, p. 284.** The terms $m = 0$ of the rows give $D(s)y^{1-k-2s}$
(with Legendre's duplication formula for $\Gamma(k+2s-1)$). -/
theorem tsum_heckeRow_constTerm {k : ℤ} {s : ℂ} (hs : 2 < (k : ℝ) + 2 * s.re) [NeZero L] [NeZero M]
    (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (z : ℍ) :
    HasSum (fun c : ℕ+ ↦ 2 * (χ ((c : ℕ) : ZMod L) * (M : ℂ) ^ (-(k : ℂ) - 2 * s) *
        (charFourier ψ 0 * xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s 0)))
      (heckeD k χ ψ s * (z.im : ℂ) ^ (1 - k - 2 * s)) :=
  tsum_heckeRow_constTerm' hs χ ψ z

/-- **Miyake, p. 285.** The terms $m \ge 1$ of the rows give $A(s)y^{-s}\sum_n(\dots)$. -/
theorem tsum_heckeRow_posTerm {k : ℤ} {s : ℂ} (hs : 2 < (k : ℝ) + 2 * s.re) [NeZero L] [NeZero M]
    (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (z : ℍ) :
    HasSum (fun c : ℕ+ ↦ 2 * (χ ((c : ℕ) : ZMod L) * (M : ℂ) ^ (-(k : ℂ) - 2 * s) *
        ∑' m : ℕ+, cexp (2 * π * I * ((m : ℕ) : ℤ) * (c : ℕ) * z.re / M) * charFourier ψ ((m : ℕ) : ℤ) *
            xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s ((m : ℕ) : ℤ)))
      (heckeA k ψ s * (z.im : ℂ) ^ (-s) * ∑' n : ℕ+, heckeTermA k χ ψ z s n) :=
  tsum_heckeRow_posTerm' hs χ ψ z

/-- **Miyake, p. 285.** The terms $m \le -1$ of the rows give $B(s)y^{-k-s}\sum_n(\dots)$. -/
theorem tsum_heckeRow_negTerm {k : ℤ} {s : ℂ} (hs : 2 < (k : ℝ) + 2 * s.re) [NeZero L] [NeZero M]
    (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (z : ℍ) :
    HasSum (fun c : ℕ+ ↦ 2 * (χ ((c : ℕ) : ZMod L) * (M : ℂ) ^ (-(k : ℂ) - 2 * s) *
        ∑' m : ℕ+, cexp (2 * π * I * (-((m : ℕ) : ℤ)) * (c : ℕ) * z.re / M) *
          charFourier ψ (-((m : ℕ) : ℤ)) *
            xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s (-((m : ℕ) : ℤ))))
      (heckeB k ψ s * (z.im : ℂ) ^ (-k - s) * ∑' n : ℕ+, heckeTermB k χ ψ z s n) :=
  tsum_heckeRow_negTerm' hs χ ψ z

/-- **Miyake, Theorem 7.2.9 (the Fourier expansion).** If $\chi(-1)\psi(-1) = (-1)^k$ and
$k + 2\operatorname{Re}s > 2$, then $E_k(z,s;\chi,\psi)$ equals `eisensteinCharSCont`. -/
@[kb "miyake1989" "Theorem 7.2.9, p. 284"]
theorem eisensteinCharS_eq_cont (k : ℤ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (hpar : χ (-1) * ψ (-1) = (-1) ^ k) (z : ℍ) {s : ℂ}
    (hs : 2 < (k : ℝ) + 2 * s.re) :
    eisensteinCharS k s χ ψ z = eisensteinCharSCont k χ ψ z s := by
  rw [eisensteinCharS_eq_tsum_heckeRow hs χ ψ z,
    tsum_int_eq_zero_add_two_mul_tsum_pnat (fun c ↦ heckeRow_neg s χ ψ hpar z c)
      (summable_heckeRow hs χ ψ z),
    heckeRow_zero hs χ ψ hpar z, eisensteinCharSCont]
  have hc := tsum_heckeRow_constTerm' hs χ ψ z
  have hp := tsum_heckeRow_posTerm' hs χ ψ z
  have hn := tsum_heckeRow_negTerm' hs χ ψ z
  have hall := (hc.add hp).add hn
  have hrow : ∀ c : ℕ+, 2 * heckeRow k s χ ψ z ((c : ℕ) : ℤ) =
      2 * (χ ((c : ℕ) : ZMod L) * (M : ℂ) ^ (-(k : ℂ) - 2 * s) *
        (charFourier ψ 0 * xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s 0)) +
      2 * (χ ((c : ℕ) : ZMod L) * (M : ℂ) ^ (-(k : ℂ) - 2 * s) *
        ∑' m : ℕ+, cexp (2 * π * I * ((m : ℕ) : ℤ) * (c : ℕ) * z.re / M) * charFourier ψ ((m : ℕ) : ℤ) *
            xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s ((m : ℕ) : ℤ)) +
      2 * (χ ((c : ℕ) : ZMod L) * (M : ℂ) ^ (-(k : ℂ) - 2 * s) *
        ∑' m : ℕ+, cexp (2 * π * I * (-((m : ℕ) : ℤ)) * (c : ℕ) * z.re / M) *
          charFourier ψ (-((m : ℕ) : ℤ)) *
            xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s (-((m : ℕ) : ℤ))) := by
    intro c
    rw [heckeRow_pos hs χ ψ z c, tsum_row_split k s ψ z c]
    ring
  have key := (tsum_congr hrow).trans hall.tsum_eq
  rw [tsum_mul_left] at key
  rw [nsmul_eq_mul, Nat.cast_ofNat, key]
  ring

/-- **Miyake, Theorem 7.2.9.** For $\chi(-1)\psi(-1) = (-1)^k$, $E_k(z,s;\chi,\psi)$ continues to a meromorphic
function on the whole $s$-plane, given by the Fourier expansion `eisensteinCharSCont`. -/
@[kb "miyake1989" "Theorem 7.2.9, p. 284"]
theorem miyake_7_2_9 (k : ℤ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (hpar : χ (-1) * ψ (-1) = (-1) ^ k) (z : ℍ) :
    MeromorphicOn (eisensteinCharSCont k χ ψ z) univ ∧
      ∀ s : ℂ, 2 < (k : ℝ) + 2 * s.re → eisensteinCharS k s χ ψ z = eisensteinCharSCont k χ ψ z s :=
  ⟨meromorphicOn_eisensteinCharSCont k χ ψ z, fun _ hs ↦ eisensteinCharS_eq_cont k χ ψ hpar z hs⟩

end ModularFormsKB.Miyake.HeckeTrick
