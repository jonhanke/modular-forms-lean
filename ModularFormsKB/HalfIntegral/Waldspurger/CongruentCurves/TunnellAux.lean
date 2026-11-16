/-
# Lemmas for Tunnell's theorem with the true $L$-function

- The characters of Tunnell's forms at level $128 = 4 \cdot 32$: the trivial character `tunnellChi0` and
  `tunnellChi2` $= \left(\frac 2\cdot\right)$ (Mathlib's `ZMod.χ₈` lifted to level $128$).
- The twisted coefficients of the Shimura lifts are those of Mathlib's $L(E_n, s)$:
  $\chi_0(d)\left(\frac{-n}d\right)b(d) = \left(\frac nd\right)b(d)$ and
  $\chi_2(d)\left(\frac{-m}d\right)b(d) = \left(\frac{2m}d\right)b(d)$ (because $b(d) \ne 0$ forces $d \equiv 1 \bmod 4$).
- Square classes at $2$: odd $u \equiv 1 \bmod 8$ is a square in $\mathbb Q_2$, so odd $n_0, n$ with
  $n_0 n \equiv 1 \bmod 8$ are in one square class for level $128$.
- Tunnell's counts vanish on the classes of root number $-1$: $A(n) = B(n) = 0$ for $n \equiv 5, 7 \bmod 8$, and
  $C(2m) = D(2m) = 0$ for $m \equiv 3, 7 \bmod 8$.
- $q$-expansions of Tunnell's forms; their first coefficients.
- $\beta = \int_1^\infty dx/\sqrt{x^3 - x} > 0$.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.F32Basic
import ModularFormsKB.HalfIntegral.Waldspurger.Coefficients
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import ModularFormsKB.HalfIntegral.QExpUnique
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open Complex Tunnell
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- The trivial character modulo $128 = 4 \cdot 32$ (character of Tunnell's odd form). -/
noncomputable abbrev tunnellChi0 : DirichletCharacter ℂ (4 * 32) := 1

/-- $\left(\frac 2\cdot\right)$ modulo $128$ (character of Tunnell's even form): Mathlib's `ZMod.χ₈` lifted. -/
noncomputable def tunnellChi2 : DirichletCharacter ℂ (4 * 32) :=
  DirichletCharacter.changeLevel (by norm_num : 8 ∣ 4 * 32) (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ))

theorem coprime_mul_of_odd_aux {d : ℕ} (hd : Odd d) : Nat.Coprime d (4 * 32) := by
  have h2 : Nat.Coprime d 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    exact fun h => (Nat.not_even_iff_odd.2 hd) (even_iff_two_dvd.2 h)
  have := Nat.Coprime.pow_right 7 h2
  simpa using this

theorem tunnellChi2_apply_odd {d : ℕ} (hd : Odd d) : tunnellChi2 (d : ZMod (4 * 32)) = (jacobiSym 2 d : ℂ) := by
  have hc : IsCoprime (d : ℤ) ((4 * 32 : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (coprime_mul_of_odd_aux hd)
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd' (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ))
    (by norm_num : 8 ∣ 4 * 32) hc
  rw [Int.cast_natCast, Int.cast_natCast] at this
  rw [tunnellChi2, this, jacobiSym.at_two hd]
  simp

theorem tunnellChi2_sq : tunnellChi2 ^ 2 = 1 := by
  ext a
  simp only [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  have hu : IsUnit ((a : ZMod (4 * 32)).val : ZMod (4 * 32)) := by
    rw [ZMod.natCast_zmod_val]; exact a.isUnit
  have hc := (ZMod.isUnit_iff_coprime _ _).1 hu
  have hodd : Odd (a : ZMod (4 * 32)).val := by
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    have h2 : 2 ∣ Nat.gcd (a : ZMod (4 * 32)).val (4 * 32) :=
      Nat.dvd_gcd (even_iff_two_dvd.1 hne) (by norm_num)
    rw [hc] at h2
    omega
  have := tunnellChi2_apply_odd hodd
  rw [ZMod.natCast_zmod_val] at this
  rw [this, ← Int.cast_pow]
  generalize (a : ZMod (4 * 32)).val = n at hodd this ⊢
  have hg : Int.gcd 2 (n : ℤ) = 1 := by
    have h2 : Nat.Coprime 2 n := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      exact fun h => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
    simpa [Int.gcd] using h2
  rcases jacobiSym.eq_one_or_neg_one hg with h | h
  · rw [h]; simp
  · rw [h]; simp

/-- $\beta = \int_1^\infty dx/\sqrt{x^3 - x}$, the integral in Tunnell's formula ($\Omega(E_1) = 2\beta$). -/
noncomputable def tunnellBeta : ℝ := ∫ x in Set.Ioi (1 : ℝ), 1 / Real.sqrt (x ^ 3 - x)

open MeasureTheory Set in
theorem tunnellBeta_integrableOn_aux :
    IntegrableOn (fun x : ℝ ↦ 1 / Real.sqrt (x ^ 3 - x)) (Ioi 1) := by
  have hmeas : Measurable (fun x : ℝ ↦ 1 / Real.sqrt (x ^ 3 - x)) := by fun_prop
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (1 : ℝ) ≤ 2)]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntervalIntegrable (fun x : ℝ ↦ (x - 1) ^ (-(1 / 2) : ℝ)) volume (0 + 1) (1 + 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by norm_num)).comp_sub_right 1
    have h2 : IntegrableOn (fun x : ℝ ↦ (x - 1) ^ (-(1 / 2) : ℝ)) (Ioc 1 2) := by
      have := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) + 1 ≤ 1 + 1)).1 h1
      norm_num at this
      exact this
    refine Integrable.mono' h2 hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have hx1 : 1 < x := hx.1
    have hpos : 0 < x - 1 := by linarith
    have hle : x - 1 ≤ x ^ 3 - x := by nlinarith [mul_pos hpos hpos]
    rw [Real.rpow_neg hpos.le, ← Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [one_div]
    apply inv_anti₀ (Real.sqrt_pos.2 hpos)
    exact Real.sqrt_le_sqrt hle
  · have h2 : IntegrableOn (fun x : ℝ ↦ 2 * x ^ (-(3 / 2) : ℝ)) (Ioi 2) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul 2
    refine Integrable.mono' h2 hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have hx2 : 2 < x := hx
    have hx0 : 0 < x := by linarith
    have hs : (x ^ (3 / 2 : ℝ)) ^ 2 = x ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    have hp : 0 < x ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have hle : x ^ (3 / 2 : ℝ) / 2 ≤ Real.sqrt (x ^ 3 - x) := by
      apply Real.le_sqrt_of_sq_le
      rw [div_pow, hs]
      nlinarith [sq_nonneg x]
    rw [Real.rpow_neg hx0.le, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc 1 / Real.sqrt (x ^ 3 - x) ≤ 1 / (x ^ (3 / 2 : ℝ) / 2) :=
          one_div_le_one_div_of_le (by positivity) hle
      _ = 2 * (x ^ (3 / 2 : ℝ))⁻¹ := by field_simp

open MeasureTheory Set in
/-- $\beta > 0$ (the integrand is positive and integrable: $\sim (2(x-1))^{-1/2}$ at $1$, $\sim x^{-3/2}$ at $\infty$). -/
theorem tunnellBeta_pos : 0 < tunnellBeta := by
  unfold tunnellBeta
  have hint := tunnellBeta_integrableOn_aux
  have hpos : ∀ x ∈ Ioi (1 : ℝ), 0 < 1 / Real.sqrt (x ^ 3 - x) := by
    intro x hx
    have hx1 : 1 < x := hx
    have : 0 < x ^ 3 - x := by nlinarith [mul_pos (by linarith : (0:ℝ) < x - 1) (by linarith : (0:ℝ) < x), sq_nonneg x]
    positivity
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => (hpos x hx).le)) hint]
  refine lt_of_lt_of_le ?_ (measure_mono (t := Function.support (fun x : ℝ ↦ 1 / Real.sqrt (x ^ 3 - x)) ∩ Ioi 1)
    (fun x hx => ⟨(hpos x hx).ne', hx⟩))
  simp

theorem shimuraTwistCoeff_chi0 (n d : ℕ) :
    shimuraTwistCoeff 1 32 tunnellChi0 n (fun m ↦ (f32Coeff m : ℂ)) d = (congruentCoeff n d : ℂ) := by
  unfold shimuraTwistCoeff shimuraChar congruentCoeff
  by_cases h : f32Coeff d = 0
  · simp [h]
  · have h4 := mod_four_eq_one_of_f32Coeff_ne_zero h
    have hodd : Odd d := by rw [Nat.odd_iff]; omega
    have hunit : IsUnit (d : ZMod (4 * 32)) :=
      (ZMod.isUnit_iff_coprime _ _).2 (coprime_mul_of_odd_aux hodd)
    have e1 : jacobiSym ((-1) ^ 1 * (n : ℤ)) d = jacobiSym n d := by
      rw [jacobiSym.mul_left, pow_one, jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_one_mod_four h4]
      simp
    rw [MulChar.one_apply hunit, e1]
    push_cast
    ring

theorem shimuraTwistCoeff_chi2 (m d : ℕ) :
    shimuraTwistCoeff 1 32 tunnellChi2 m (fun m ↦ (f32Coeff m : ℂ)) d = (congruentCoeff (2 * m) d : ℂ) := by
  unfold shimuraTwistCoeff shimuraChar congruentCoeff
  by_cases h : f32Coeff d = 0
  · simp [h]
  · have h4 := mod_four_eq_one_of_f32Coeff_ne_zero h
    have hodd : Odd d := by rw [Nat.odd_iff]; omega
    have e1 : jacobiSym ((2 : ℤ) * (m : ℤ)) d = jacobiSym 2 d * jacobiSym ((-1) ^ 1 * (m : ℤ)) d := by
      rw [jacobiSym.mul_left, jacobiSym.mul_left, pow_one, jacobiSym.at_neg_one hodd,
        ZMod.χ₄_nat_one_mod_four h4]
      simp
    rw [tunnellChi2_apply_odd hodd]
    push_cast
    rw [e1]
    push_cast
    ring

/-- An odd $u \equiv 1 \bmod 8$ is a square in $\mathbb Q_2$ (Hensel). -/
theorem isSquare_padic_two_of_mod_eight {u : ℕ} (hu : u % 8 = 1) : IsSquare ((u : ℚ_[2])) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F : Polynomial ℤ_[2] := Polynomial.X ^ 2 - Polynomial.C (u : ℤ_[2])
  have hF1 : F.aeval (1 : ℤ_[2]) = -((u - 1 : ℤ) : ℤ_[2]) := by
    simp [F]
  have hF2 : F.derivative.aeval (1 : ℤ_[2]) = 2 := by
    simp [F]; norm_num
  have h8 : ‖((u - 1 : ℤ) : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-(3 : ℤ)) := by
    have : ((2 : ℕ) : ℤ) ^ 3 ∣ ((u : ℤ) - 1) := by
      have : (u : ℤ) % 8 = 1 := by omega
      omega
    have := (PadicInt.norm_int_le_pow_iff_dvd (p := 2) (k := (u : ℤ) - 1) (n := 3)).2 this
    simpa using this
  have h2 : ‖(2 : ℤ_[2])‖ = 1 / 2 := by
    have := PadicInt.norm_p (p := 2)
    simpa using this
  have hnorm : ‖F.aeval (1 : ℤ_[2])‖ < ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hF1, hF2, norm_neg, h2]
    refine lt_of_le_of_lt h8 ?_
    norm_num
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  refine ⟨(z : ℚ_[2]), ?_⟩
  have : z ^ 2 = (u : ℤ_[2]) := by
    simpa [F, sub_eq_zero] using hz
  have h3 : ((z ^ 2 : ℤ_[2]) : ℚ_[2]) = ((u : ℤ_[2]) : ℚ_[2]) := by rw [this]
  simpa [sq] using h3.symm

/-- Odd $n_0, n$ with $n_0n \equiv 1 \bmod 8$ lie in one square class at level $128$. -/
theorem sameSquareClass_of_mod_eight {n₀ n : ℕ} (h : n₀ * n % 8 = 1) : SameSquareClass 32 n₀ n := by
  intro p hp hdvd
  have h2 : p ∣ 2 ^ 7 := by
    have : (4 * 32 : ℕ) = 2 ^ 7 := by norm_num
    rwa [this] at hdvd
  have hp2 : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow h2)
  subst hp2
  exact isSquare_padic_two_of_mod_eight h

theorem sq_mod_eight_aux (x : ℤ) : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have h : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by
    omega
  rcases h with h | h | h | h | h | h | h | h <;> simp [pow_two, Int.mul_emod, h]

theorem repCount_eq_zero_aux {α β m : ℕ} (hβ : 8 ∣ β)
    (H : ∀ a b : ℤ, (a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 4) → (b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 4) →
      (a + α * b) % 8 ≠ (m : ℤ) % 8) : Tunnell.repCount α β m = 0 := by
  unfold Tunnell.repCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v _ h
  obtain ⟨k, hk⟩ := hβ
  have hz : (β : ℤ) * v.2.2 ^ 2 = 8 * (k * v.2.2 ^ 2) := by rw [hk]; push_cast; ring
  apply H (v.1 ^ 2) (v.2.1 ^ 2) (sq_mod_eight_aux _) (sq_mod_eight_aux _)
  rw [← h, hz, Int.add_mul_emod_self_left]

theorem tunnellA_eq_zero {n : ℕ} (h : n % 8 = 5 ∨ n % 8 = 7) : tunnellA n = 0 := by
  apply repCount_eq_zero_aux (by norm_num)
  intro a b ha hb
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> omega

theorem tunnellB_eq_zero {n : ℕ} (h : n % 8 = 5 ∨ n % 8 = 7) : tunnellB n = 0 := by
  apply repCount_eq_zero_aux (by norm_num)
  intro a b ha hb
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> omega

theorem tunnellC_eq_zero {m : ℕ} (h : m % 8 = 3 ∨ m % 8 = 7) : tunnellC (2 * m) = 0 := by
  unfold tunnellC
  rw [show 2 * m / 2 = m by omega]
  apply repCount_eq_zero_aux (by norm_num)
  intro a b ha hb
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> omega

theorem tunnellD_eq_zero {m : ℕ} (h : m % 8 = 3 ∨ m % 8 = 7) : tunnellD (2 * m) = 0 := by
  unfold tunnellD
  rw [show 2 * m / 2 = m by omega]
  apply repCount_eq_zero_aux (by norm_num)
  intro a b ha hb
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> omega

theorem repCount_le_aux (α β m : ℕ) : Tunnell.repCount α β m ≤ (2 * m + 1) ^ 3 := by
  unfold Tunnell.repCount
  refine (Finset.card_filter_le _ _).trans ?_
  simp only [Finset.card_product, Int.card_Icc]
  have : ((m : ℤ) + 1 - -(m : ℤ)).toNat = 2 * m + 1 := by omega
  rw [this]
  ring_nf
  rfl

theorem hasQExp_of_bound_aux (c : ℕ → ℂ) (hc : ∀ m, ‖c m‖ ≤ 2 * ((2 * m + 1) ^ 3 : ℕ)) :
    Abstract.HasQExp (fun τ ↦ ∑' m : ℕ, c m * cexp (2 * π * I * m * τ)) c := by
  intro τ
  refine Summable.hasSum ?_
  set q : ℂ := cexp (2 * π * I * τ) with hq
  have hqn : ‖q‖ < 1 := by
    rw [hq, Complex.norm_exp]
    have : (2 * π * I * (τ : ℂ)).re = -(2 * π * (τ : ℂ).im) := by
      simp [Complex.mul_re]
    rw [this]
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.2
    have h3 : 0 < (τ : ℂ).im := τ.im_pos
    nlinarith [mul_pos Real.pi_pos h3]
  have hterm : ∀ m : ℕ, cexp (2 * π * I * m * τ) = q ^ m := by
    intro m
    rw [hq, ← Complex.exp_nat_mul]
    congr 1
    ring
  have hs : Summable (fun m : ℕ ↦ 2 * (((2 * m + 1) ^ 3 : ℕ) : ℝ) * ‖q‖ ^ m) := by
    have h3 := summable_pow_mul_geometric_of_norm_lt_one 3 (r := ‖q‖) (by simpa using hqn)
    have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 (r := ‖q‖) (by simpa using hqn)
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := ‖q‖) (by simpa using hqn)
    have h0 := summable_geometric_of_lt_one (norm_nonneg q) hqn
    have := (((h3.mul_left 16).add (h2.mul_left 24)).add (h1.mul_left 12)).add (h0.mul_left 2)
    refine this.congr ?_
    intro m
    push_cast
    ring
  refine Summable.of_norm_bounded hs ?_
  intro m
  rw [hterm, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (by simpa using hc m) (by positivity)

theorem hasQExp_tunnellOdd : Abstract.HasQExp tunnellOdd tunnellOddCoeff := by
  refine hasQExp_of_bound_aux tunnellOddCoeff ?_
  intro m
  unfold tunnellOddCoeff
  have hA := repCount_le_aux 2 8 m
  have hB := repCount_le_aux 2 32 m
  split_ifs
  · calc ‖(tunnellB m : ℂ) - (tunnellA m : ℂ) / 2‖ ≤ ‖(tunnellB m : ℂ)‖ + ‖(tunnellA m : ℂ) / 2‖ :=
          norm_sub_le _ _
      _ ≤ 2 * (((2 * m + 1) ^ 3 : ℕ) : ℝ) := by
          rw [norm_div]
          simp only [Complex.norm_natCast]
          have hA' : (tunnellA m : ℝ) ≤ ((2 * m + 1) ^ 3 : ℕ) := by exact_mod_cast hA
          have hB' : (tunnellB m : ℝ) ≤ ((2 * m + 1) ^ 3 : ℕ) := by exact_mod_cast hB
          simp only [Complex.norm_ofNat]
          linarith
  · simp only [norm_zero]; positivity

theorem hasQExp_tunnellEven : Abstract.HasQExp tunnellEven tunnellEvenCoeff := by
  refine hasQExp_of_bound_aux tunnellEvenCoeff ?_
  intro m
  unfold tunnellEvenCoeff
  have hA : tunnellC (2 * m) ≤ (2 * m + 1) ^ 3 := by
    unfold tunnellC; rw [show 2 * m / 2 = m by omega]; exact repCount_le_aux 4 8 m
  have hB : tunnellD (2 * m) ≤ (2 * m + 1) ^ 3 := by
    unfold tunnellD; rw [show 2 * m / 2 = m by omega]; exact repCount_le_aux 4 32 m
  split_ifs
  · calc ‖(tunnellD (2 * m) : ℂ) - (tunnellC (2 * m) : ℂ) / 2‖
          ≤ ‖(tunnellD (2 * m) : ℂ)‖ + ‖(tunnellC (2 * m) : ℂ) / 2‖ := norm_sub_le _ _
      _ ≤ 2 * (((2 * m + 1) ^ 3 : ℕ) : ℝ) := by
          rw [norm_div]
          simp only [Complex.norm_natCast]
          have hA' : (tunnellC (2 * m) : ℝ) ≤ ((2 * m + 1) ^ 3 : ℕ) := by exact_mod_cast hA
          have hB' : (tunnellD (2 * m) : ℝ) ≤ ((2 * m + 1) ^ 3 : ℕ) := by exact_mod_cast hB
          simp only [Complex.norm_ofNat]
          linarith
  · simp only [norm_zero]; positivity

theorem tunnellOddCoeff_one : tunnellOddCoeff 1 = 1 := by
  unfold tunnellOddCoeff
  rw [if_pos odd_one, tunnellA_one, tunnellB_one]
  norm_num

theorem tunnellOddCoeff_three : tunnellOddCoeff 3 = 2 := by
  unfold tunnellOddCoeff
  rw [if_pos (by decide), tunnellA_three, tunnellB_three]
  norm_num

theorem tunnellEvenCoeff_one : tunnellEvenCoeff 1 = 1 := by
  unfold tunnellEvenCoeff
  rw [if_pos odd_one]
  have h1 : tunnellC (2 * 1) = 2 := tunnellC_two
  have h2 : tunnellD (2 * 1) = 2 := tunnellD_two
  rw [h1, h2]
  norm_num

theorem tunnellD_ten : tunnellD (2 * 5) = 4 := by
  unfold tunnellD; decide +kernel

theorem tunnellC_ten : tunnellC (2 * 5) = 4 := by
  unfold tunnellC; decide +kernel

theorem tunnellEvenCoeff_five : tunnellEvenCoeff 5 = 2 := by
  unfold tunnellEvenCoeff
  rw [if_pos (by decide), tunnellC_ten, tunnellD_ten]
  norm_num

theorem tunnellOdd_ne_zero : tunnellOdd ≠ 0 := by
  intro h
  have h1 : Abstract.HasQExp tunnellOdd tunnellOddCoeff := hasQExp_tunnellOdd
  have h2 : Abstract.HasQExp tunnellOdd (fun _ ↦ 0) := by
    intro τ; rw [h]; simpa using hasSum_zero
  have := congrFun (Abstract.hasQExp_unique h1 h2) 1
  rw [tunnellOddCoeff_one] at this
  exact one_ne_zero this

theorem tunnellEven_ne_zero : tunnellEven ≠ 0 := by
  intro h
  have h1 : Abstract.HasQExp tunnellEven tunnellEvenCoeff := hasQExp_tunnellEven
  have h2 : Abstract.HasQExp tunnellEven (fun _ ↦ 0) := by
    intro τ; rw [h]; simpa using hasSum_zero
  have := congrFun (Abstract.hasQExp_unique h1 h2) 1
  rw [tunnellEvenCoeff_one] at this
  exact one_ne_zero this

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
