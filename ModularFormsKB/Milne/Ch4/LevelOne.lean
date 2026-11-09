import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import TauCeti.Analysis.Complex.ModularForms.LevelOne.JInputs
import TauCeti.NumberTheory.ModularForms.LevelOne.DiscriminantEigenform
import ModularFormsKB.Citation
/-!
# Milne, Chapter 4: Eisenstein series, $\Delta$, $j$ and $\tau$ for $\Gamma(1)$

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 4, pdf pp. 48–58.

**Weight convention.** Milne writes weight $2k$; Mathlib's `ModularForm 𝒮ℒ w` has weight $w$, so Milne's $k$ is
Mathlib's $w/2$. Milne's $G_k$ is the full lattice sum $\sum_{(m,n)\neq(0,0)}(mz+n)^{-2k}$ (`G`), of Mathlib weight
$2k$; Mathlib's normalized series is `ModularForm.E`, with $G_k = 2\zeta(2k)E_{2k}$ (`G_eq`). Milne's $g_2 = 60G_2$,
$g_3 = 140G_3$, $\Delta = g_2^3 - 27g_3^2$ (`disc`) is $(2\pi)^{12}$ times Mathlib's `ModularForm.discriminant`
(`disc_eq`), and Milne's $j = 1728g_2^3/\Delta$ (`jFun`) is Tau Ceti's `TauCeti.ModularForm.j` $= E_4^3/\Delta$
(`jFun_eq`).

**Milne's Bernoulli numbers** are $B_k = |b_{2k}|$ for Mathlib's `bernoulli` $b$ ($B_1 = 1/6$, $B_2 = 1/30$):
see `milneBernoulli`.

## Items
- Proposition 4.7 (`G_isModularForm`, `tendsto_G_atImInfty`); proof of 4.7 (`G`).
- Proposition 4.18 (`riemannZeta_two_mul_eq_milneBernoulli`).
- Proposition 4.20 (`G_qExpansion`).
- Theorem 4.21, Jacobi's product (`disc_eq_prod`).
- The Ramanujan $\tau$-function, p. 58 (`ramanujanTau`, `ramanujanTau_isInt`, `ramanujanTau_one`,
  `ramanujanTau_two`, `hasSum_ramanujanTau`).
- Theorem 4.22, the $q$-expansion of $j$ with integral coefficients (`jFun_qExpansion`).
-/

open UpperHalfPlane ModularForm EisensteinSeries Complex Filter Topology
open scoped MatrixGroups Real ArithmeticFunction.sigma

noncomputable section

namespace ModularFormsKB.Milne

/-- **Milne's Eisenstein series** $G_k(z) = \sum_{(m,n)\neq(0,0)} (mz+n)^{-2k}$ (weight $2k$ in Milne's convention).
The term with $(m,n) = (0,0)$ is $0^{-2k} = 0$ in Lean, so the sum over all pairs is the sum over nonzero pairs. -/
@[kb "milne2017mf" "Section 4, proof of Proposition 4.7, the series G_k(z) (pdf p. 50)"]
def G (k : ℕ) (z : ℍ) : ℂ := ∑' v : Fin 2 → ℤ, eisSummand (2 * k : ℕ) v z

/-- Comparison with Mathlib: $G_k = 2\zeta(2k)\,E_{2k}$ for $k \ge 2$. -/
theorem G_eq {k : ℕ} (hk : 3 ≤ 2 * k) (z : ℍ) : G k z = 2 * riemannZeta (2 * k : ℕ) * E hk z := by
  have h := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk z
  have hE : E hk z = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 (2 * k : ℕ) z := by
    rw [show E hk z = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 (2 * k : ℕ) z from rfl,
      eisensteinSeriesSIF_apply 0 _ z, smul_eq_mul]
  unfold G
  rw [h, hE]
  ring

/-- **Proposition 4.7**, modularity: for $k > 1$, $G_k$ is a modular form of weight $2k$ for $\Gamma(1)$. -/
@[kb "milne2017mf" "Section 4, Proposition 4.7 (pdf p. 50)"]
theorem G_isModularForm {k : ℕ} (hk : 1 < k) : ∃ F : ModularForm 𝒮ℒ (2 * k : ℕ), ⇑F = G k := by
  have hk3 : 3 ≤ 2 * k := by omega
  refine ⟨(2 * riemannZeta (2 * k : ℕ)) • E hk3, ?_⟩
  funext z
  rw [G_eq hk3 z]
  rfl

/-- **Proposition 4.7**, value at infinity: for $k > 1$, $G_k(z) \to 2\zeta(2k)$ as $z \to i\infty$. -/
@[kb "milne2017mf" "Section 4, Proposition 4.7 (pdf p. 50)"]
theorem tendsto_G_atImInfty {k : ℕ} (hk : 1 < k) :
    Tendsto (G k) atImInfty (𝓝 (2 * riemannZeta (2 * k : ℕ))) := by
  have hk3 : 3 ≤ 2 * k := by omega
  have h := (tendsto_E_atImInfty hk3 (even_two_mul k)).const_mul (2 * riemannZeta (2 * k : ℕ))
  rw [mul_one] at h
  refine h.congr fun z ↦ ?_
  rw [G_eq hk3 z]

/-- **Milne's Bernoulli numbers** (p. 55): $\frac{x}{e^x-1} = 1 - \frac x2 + \sum_{k\ge1}(-1)^{k+1}B_k\frac{x^{2k}}{(2k)!}$,
so $B_k = (-1)^{k+1}b_{2k} = |b_{2k}|$ for Mathlib's `bernoulli` $b$ (`milneBernoulli_eq`). -/
@[kb "milne2017mf" "Section 4, the Bernoulli numbers B_k (pdf p. 55)"]
def milneBernoulli (k : ℕ) : ℚ := |bernoulli (2 * k)|

/-- Helper: $(-1)^{k+1} b_{2k} > 0$ for $k \ge 1$, from $\zeta(2k) \ge 1$. -/
theorem sign_bernoulli_pos {k : ℕ} (hk : 1 ≤ k) : 0 < (-1 : ℚ) ^ (k + 1) * bernoulli (2 * k) := by
  have hk0 : k ≠ 0 := by omega
  have h1 := le_hasSum (hasSum_zeta_nat hk0) 1 (fun j _ ↦ by positivity)
  by_contra hneg
  rw [not_lt] at hneg
  have hneg' : (-1 : ℝ) ^ (k + 1) * (bernoulli (2 * k) : ℝ) ≤ 0 := by exact_mod_cast hneg
  have h2 : (-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) * (bernoulli (2 * k) : ℝ) /
      (2 * k).factorial ≤ 0 := by
    have : (-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) * (bernoulli (2 * k) : ℝ) /
      (2 * k).factorial = ((2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) / (2 * k).factorial) *
        ((-1 : ℝ) ^ (k + 1) * (bernoulli (2 * k) : ℝ)) := by ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg'
  norm_num at h1
  linarith

/-- Milne's sign convention: $(-1)^{k+1}B_k = b_{2k}$ for $k \ge 1$. -/
theorem milneBernoulli_eq {k : ℕ} (hk : 1 ≤ k) : (-1) ^ (k + 1) * milneBernoulli k = bernoulli (2 * k) := by
  have h := sign_bernoulli_pos hk
  unfold milneBernoulli
  rcases neg_one_pow_eq_or ℚ (k + 1) with h1 | h1
  · rw [h1] at h ⊢
    rw [abs_of_pos (by simpa using h)]
    simp
  · rw [h1] at h ⊢
    rw [abs_of_neg (by simpa using h)]
    simp

/-- **Proposition 4.18**: $\zeta(2k) = \frac{2^{2k-1}}{(2k)!}B_k\pi^{2k}$ for all $k \ge 1$. -/
@[kb "milne2017mf" "Section 4, Proposition 4.18 (pdf p. 55)"]
theorem riemannZeta_two_mul_eq_milneBernoulli {k : ℕ} (hk : 1 ≤ k) :
    riemannZeta (2 * k : ℕ) = (2 : ℂ) ^ (2 * k - 1) / (2 * k).factorial * (milneBernoulli k : ℂ) * (π : ℂ) ^ (2 * k) := by
  have hk0 : k ≠ 0 := by omega
  rw [Nat.cast_mul, Nat.cast_ofNat, riemannZeta_two_mul_nat hk0, ← milneBernoulli_eq hk]
  push_cast
  have h : ((-1 : ℂ) ^ (k + 1)) * (-1) ^ (k + 1) = 1 := by rw [← mul_pow]; simp
  generalize (-1 : ℂ) ^ (k + 1) = s at h ⊢
  calc s * (2 : ℂ) ^ (2 * k - 1) * (π : ℂ) ^ (2 * k) * (s * (milneBernoulli k : ℂ)) /
        ((2 * k).factorial : ℂ)
      = (s * s) * ((2 : ℂ) ^ (2 * k - 1) * (π : ℂ) ^ (2 * k) * (milneBernoulli k : ℂ) /
        ((2 * k).factorial : ℂ)) := by ring
    _ = _ := by rw [h]; ring

/-- **Proposition 4.20**: for every $k \ge 2$,
$G_k(z) = 2\zeta(2k) + \frac{2(2\pi i)^{2k}}{(2k-1)!}\sum_{n\ge1}\sigma_{2k-1}(n)q^n$, $q = e^{2\pi i z}$. -/
@[kb "milne2017mf" "Section 4, Proposition 4.20 (pdf p. 56)"]
theorem G_qExpansion {k : ℕ} (hk : 2 ≤ k) (z : ℍ) :
    G k z = 2 * riemannZeta (2 * k : ℕ) + 2 * (2 * π * Complex.I) ^ (2 * k) / (2 * k - 1).factorial *
      ∑' n : ℕ+, (σ (2 * k - 1) n : ℂ) * cexp (2 * π * Complex.I * z) ^ (n : ℕ) := by
  have hk3 : 3 ≤ 2 * k := by omega
  have h := tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow hk3 (even_two_mul k) z
  have hn : (-2 * π * Complex.I) ^ (2 * k) = (2 * π * Complex.I) ^ (2 * k) := by
    rw [show (-2 * π * Complex.I : ℂ) = -(2 * π * Complex.I) by ring]
    exact Even.neg_pow (even_two_mul k) _
  rw [hn] at h
  unfold G
  rw [h]
  ring

/-- Helper: $G_2 = \frac{\pi^4}{45}E_4$. -/
theorem G_two (z : ℍ) : G 2 z = (π : ℂ) ^ 4 / 45 * E₄ z := by
  rw [G_eq (k := 2) (by norm_num) z]
  have hz : riemannZeta ((2 * 2 : ℕ) : ℂ) = (π : ℂ) ^ 4 / 90 := by
    norm_num [riemannZeta_four]
  rw [hz]
  change 2 * ((π : ℂ) ^ 4 / 90) * E₄ z = _
  ring

/-- Helper: $G_3 = \frac{2\pi^6}{945}E_6$. -/
theorem G_three (z : ℍ) : G 3 z = 2 * (π : ℂ) ^ 6 / 945 * E₆ z := by
  rw [G_eq (k := 3) (by norm_num) z]
  have hz : riemannZeta ((2 * 3 : ℕ) : ℂ) = (π : ℂ) ^ 6 / 945 := by
    have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
    have hb : bernoulli (2 * 3) = 1 / 42 := by decide +kernel
    rw [hb] at h
    have e : ((2 * 3 : ℕ) : ℂ) = 2 * ((3 : ℕ) : ℂ) := by push_cast; ring
    rw [e, h]
    norm_num [Nat.factorial]
    ring
  rw [hz]
  change 2 * ((π : ℂ) ^ 6 / 945) * E₆ z = _
  ring

/-- Milne's $g_2 = 60G_2$ (p. 57). -/
@[kb "milne2017mf" "Section 4, g_2 = 60 G_2 (pdf p. 58)"]
def g₂ (z : ℍ) : ℂ := 60 * G 2 z

/-- Milne's $g_3 = 140G_3$ (p. 57). -/
@[kb "milne2017mf" "Section 4, g_3 = 140 G_3 (pdf p. 58)"]
def g₃ (z : ℍ) : ℂ := 140 * G 3 z

/-- Helper: Jacobi's product for Mathlib's discriminant in terms of `cexp`. -/
theorem discriminant_eq_cexp_prod (z : ℍ) : ModularForm.discriminant z =
    cexp (2 * π * Complex.I * z) * ∏' n : ℕ, (1 - cexp (2 * π * Complex.I * z) ^ (n + 1)) ^ 24 := by
  have hq : Function.Periodic.qParam 1 (z : ℂ) = cexp (2 * π * Complex.I * z) := by
    simp [Function.Periodic.qParam]
  rw [ModularForm.discriminant_eq_q_prod, hq]
  simp only [eta_q_eq_pow]

/-- **Milne's discriminant** $\Delta = g_2^3 - 27g_3^2$ (p. 57). -/
@[kb "milne2017mf" "Section 4, the discriminant Delta = g_2^3 - 27 g_3^2 (pdf p. 57)"]
def disc (z : ℍ) : ℂ := g₂ z ^ 3 - 27 * g₃ z ^ 2

/-- Comparison with Mathlib: Milne's $\Delta$ is $(2\pi)^{12}$ times Mathlib's `ModularForm.discriminant`
($=\eta^{24}$). -/
theorem disc_eq (z : ℍ) : disc z = (2 * π : ℂ) ^ 12 * ModularForm.discriminant z := by
  unfold disc g₂ g₃
  rw [G_two, G_three, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  ring

/-- **Theorem 4.21 (Jacobi)**: $\Delta(z) = (2\pi)^{12}\,q\prod_{n\ge1}(1-q^n)^{24}$, $q = e^{2\pi i z}$. -/
@[kb "milne2017mf" "Section 4, Theorem 4.21 (pdf p. 57)"]
theorem disc_eq_prod (z : ℍ) :
    disc z = (2 * π : ℂ) ^ 12 * cexp (2 * π * Complex.I * z) * ∏' n : ℕ, (1 - cexp (2 * π * Complex.I * z) ^ (n + 1)) ^ 24 := by
  rw [disc_eq, discriminant_eq_cexp_prod]
  ring

/-- **The Ramanujan $\tau$-function** (p. 58): $q\prod_{n\ge1}(1-q^n)^{24} = \sum_{n\ge1}\tau(n)q^n$, i.e. $\tau(n)$ is
the $n$-th $q$-expansion coefficient of Mathlib's `ModularForm.discriminant`. Defined with complex values;
`ramanujanTau_isInt` shows the values are integers. -/
@[kb "milne2017mf" "Section 4, the Ramanujan tau-function (pdf p. 58)"]
def ramanujanTau (n : ℕ) : ℂ := (qExpansion 1 ModularForm.discriminant).coeff n

/-- The defining expansion of $\tau$: $\sum_{n\ge 0}\tau(n)q^n = q\prod_{n\ge1}(1-q^n)^{24}$ (and $\tau(0) = 0$). -/
@[kb "milne2017mf" "Section 4, the Ramanujan tau-function (pdf p. 58)"]
theorem hasSum_ramanujanTau (z : ℍ) :
    HasSum (fun n : ℕ ↦ ramanujanTau n * cexp (2 * π * Complex.I * z) ^ n)
      (cexp (2 * π * Complex.I * z) * ∏' n : ℕ, (1 - cexp (2 * π * Complex.I * z) ^ (n + 1)) ^ 24) := by
  have h := ModularForm.hasSum_qExpansion (f := CuspForm.discriminant) (h := 1) one_pos
    one_mem_strictPeriods_SL z
  have hq : Function.Periodic.qParam 1 (z : ℂ) = cexp (2 * π * Complex.I * z) := by
    simp [Function.Periodic.qParam]
  rw [hq] at h
  rw [← discriminant_eq_cexp_prod]
  exact h

/-- Helper: the integer power series $\sum_n \sigma_k(n) q^n$. -/
def sigmaSeries (k : ℕ) : PowerSeries ℤ := PowerSeries.mk fun n => ((σ k n : ℕ) : ℤ)

/-- Helper: $E_4$ has the integral $q$-expansion $1 + 240\sum\sigma_3(n)q^n$. -/
theorem map_E₄ : PowerSeries.map (Int.castRingHom ℂ) (1 + 240 * sigmaSeries 3) =
    qExpansion 1 E₄ := by
  ext m
  have h : (qExpansion 1 E₄).coeff m = _ := E_qExpansion_coeff (k := 4) (by norm_num) ⟨2, rfl⟩ m
  rw [h, PowerSeries.coeff_map]
  have hb : bernoulli 4 = -1 / 30 := by decide +kernel
  rcases m with _ | m
  · simp [sigmaSeries]
  · simp [sigmaSeries, hb]
    norm_num

/-- Helper: $E_6$ has the integral $q$-expansion $1 - 504\sum\sigma_5(n)q^n$. -/
theorem map_E₆ : PowerSeries.map (Int.castRingHom ℂ) (1 - 504 * sigmaSeries 5) =
    qExpansion 1 E₆ := by
  ext m
  have h : (qExpansion 1 E₆).coeff m = _ := E_qExpansion_coeff (k := 6) (by norm_num) ⟨3, rfl⟩ m
  rw [h, PowerSeries.coeff_map]
  have hb : bernoulli 6 = 1 / 42 := by decide +kernel
  rcases m with _ | m
  · simp [sigmaSeries]
  · simp [sigmaSeries, hb]
    norm_num

/-- Helper: $12 \mid 5\sigma_3(n) + 7\sigma_5(n)$. -/
theorem twelve_dvd_sigma (n : ℕ) : (12 : ℤ) ∣ 5 * ((σ 3 n : ℕ) : ℤ) + 7 * ((σ 5 n : ℕ) : ℤ) := by
  rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.dvd_sum fun d _ => ?_
  have h : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
  have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) 12).1
    (by push_cast; exact h _)
  exact_mod_cast h2

/-- Helper: the $q$-expansion of the discriminant has integer coefficients (as a power series). -/
theorem exists_int_discriminant : ∃ C : PowerSeries ℤ,
    PowerSeries.map (Int.castRingHom ℂ) C = qExpansion 1 ModularForm.discriminant := by
  set a := sigmaSeries 3 with ha
  set b := sigmaSeries 5 with hb
  set e : PowerSeries ℤ := PowerSeries.mk fun n => (5 * ((σ 3 n : ℕ) : ℤ) + 7 * ((σ 5 n : ℕ) : ℤ)) / 12
    with he
  have key : 12 * e = 5 * a + 7 * b := by
    ext n
    simp only [he, ha, hb, sigmaSeries, PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_mk,
      map_add]
    exact Int.mul_ediv_cancel' (twelve_dvd_sigma n)
  have key2 : (1 + 240 * a) ^ 3 - (1 - 504 * b) ^ 2 =
      1728 * (e + 100 * a ^ 2 + 8000 * a ^ 3 - 147 * b ^ 2) := by
    linear_combination (-144 : PowerSeries ℤ) * key
  refine ⟨e + 100 * a ^ 2 + 8000 * a ^ 3 - 147 * b ^ 2, ?_⟩
  generalize e + 100 * a ^ 2 + 8000 * a ^ 3 - 147 * b ^ 2 = Cz at key2 ⊢
  have h1 : PowerSeries.map (Int.castRingHom ℂ) (1728 * Cz) =
      (1728 : ℂ) • PowerSeries.map (Int.castRingHom ℂ) Cz := by
    ext n
    rw [map_mul, map_ofNat]
    simp
  rw [TauCeti.ModularForm.qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq, ← map_E₄, ← map_E₆,
    ← map_pow, ← map_pow, ← map_sub, key2, h1, smul_smul]
  norm_num

/-- "Evidently each $\tau(n) \in \mathbb Z$" (p. 58). -/
@[kb "milne2017mf" "Section 4, tau(n) is an integer (pdf p. 58)"]
theorem ramanujanTau_isInt (n : ℕ) : ∃ m : ℤ, ramanujanTau n = m := by
  obtain ⟨C, hC⟩ := exists_int_discriminant
  refine ⟨C.coeff n, ?_⟩
  unfold ramanujanTau
  rw [← hC, PowerSeries.coeff_map]
  simp

@[kb "milne2017mf" "Section 4, tau(1) = 1 (pdf p. 58)"]
theorem ramanujanTau_one : ramanujanTau 1 = 1 := ModularForm.discriminant_qExpansion_coeff_one

/-- $\tau(2) = -24$ (the minus sign is lost in some text extractions of the pdf). -/
@[kb "milne2017mf" "Section 4, tau(2) = -24 (pdf p. 58)"]
theorem ramanujanTau_two : ramanujanTau 2 = -24 :=
  TauCeti.ModularForm.discriminant_qExpansion_coeff_two

/-- Helper: $\tau(3) = 252$. -/
theorem ramanujanTau_three : ramanujanTau 3 = 252 :=
  TauCeti.ModularForm.discriminant_qExpansion_coeff_three

/-- Helper: $\tau(4) = \tau(2)^2 - 2^{11} = -1472$. -/
theorem ramanujanTau_four : ramanujanTau 4 = -1472 := by
  have h : ramanujanTau 4 = ramanujanTau 2 * ramanujanTau 2 - 2 ^ 11 * ramanujanTau 1 := by
    simpa [ramanujanTau] using
      TauCeti.ModularForm.discriminant_qExpansion_coeff_prime_pow_add_two Nat.prime_two 0
  rw [h, ramanujanTau_two, ramanujanTau_one]
  norm_num

/-- $\tau(12) = -370944$ (p. 58). -/
@[kb "milne2017mf" "Section 4, tau(12) = -370944 (pdf p. 58)"]
theorem ramanujanTau_twelve : ramanujanTau 12 = -370944 := by
  have h : ramanujanTau 12 = ramanujanTau 3 * ramanujanTau 4 := by
    simpa [ramanujanTau] using
      TauCeti.ModularForm.discriminant_qExpansion_coeff_mul (m := 3) (n := 4) (by norm_num)
  rw [h, ramanujanTau_three, ramanujanTau_four]
  norm_num

/-- **Milne's $j$-function** $j = 1728g_2^3/\Delta$ (p. 58). -/
@[kb "milne2017mf" "Section 4, j = 1728 g_2^3 / Delta (pdf p. 58); Remark 4.4 (pdf p. 49)"]
def jFun (z : ℍ) : ℂ := 1728 * g₂ z ^ 3 / disc z

/-- Comparison with Tau Ceti: Milne's $j$ is `TauCeti.ModularForm.j` $= E_4^3/\Delta$. -/
theorem jFun_eq : jFun = TauCeti.ModularForm.j := by
  funext z
  have hΔ := ModularForm.discriminant_ne_zero z
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold jFun g₂
  rw [TauCeti.ModularForm.j_apply, G_two, disc_eq, div_eq_div_iff
    (mul_ne_zero (pow_ne_zero _ (mul_ne_zero two_ne_zero hπ)) hΔ) hΔ]
  ring

/-- Helper: the $q$-expansion series of $qj$ is an integral power series. -/
theorem exists_int_qParam_mul_j : ∃ JZ : PowerSeries ℤ, PowerSeries.map (Int.castRingHom ℂ) JZ =
    qExpansion 1 (fun τ : ℍ ↦ Function.Periodic.qParam 1 (τ : ℂ) * TauCeti.ModularForm.j τ) := by
  obtain ⟨C, hC⟩ := exists_int_discriminant
  have hJD := TauCeti.ModularForm.qExpansion_qParam_mul_j_mul_qExpansion_discriminant
  have hC0 : C.coeff 0 = 0 := by
    have h := TauCeti.ModularForm.discriminant_qExpansion_coeff_zero
    rw [← hC, PowerSeries.coeff_map] at h
    simpa using h
  have hC1 : C.coeff 1 = 1 := by
    have h : (qExpansion 1 ModularForm.discriminant).coeff 1 = 1 := ramanujanTau_one
    rw [← hC, PowerSeries.coeff_map] at h
    simpa using h
  set C' : PowerSeries ℤ := PowerSeries.mk fun n => C.coeff (n + 1) with hC'
  have hCX : C = PowerSeries.X * C' := by
    ext n
    rcases n with _ | n
    · simp [hC0]
    · simp [hC', PowerSeries.coeff_succ_X_mul]
  have hc : PowerSeries.constantCoeff C' = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simpa [hC'] using hC1
  set AZ : PowerSeries ℤ := 1 + 240 * sigmaSeries 3 with hAZ
  refine ⟨AZ ^ 3 * PowerSeries.invOfUnit C' 1, ?_⟩
  have hmul : AZ ^ 3 * PowerSeries.invOfUnit C' 1 * C' = AZ ^ 3 := by
    rw [mul_assoc, mul_comm (PowerSeries.invOfUnit C' 1) C',
      PowerSeries.mul_invOfUnit C' 1 (by simpa using hc), mul_one]
  set J := qExpansion 1 (fun τ : ℍ ↦ Function.Periodic.qParam 1 (τ : ℂ) * TauCeti.ModularForm.j τ)
    with hJ
  set M := PowerSeries.map (Int.castRingHom ℂ) C' with hM
  have hCM : qExpansion 1 ModularForm.discriminant = PowerSeries.X * M := by
    rw [← hC, hCX, map_mul, PowerSeries.map_X]
  have hM0 : M ≠ 0 := by
    intro h0
    have : PowerSeries.constantCoeff M = 1 := by
      rw [hM, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hc]
      simp
    rw [h0] at this
    simp at this
  have h1 : J * M = PowerSeries.map (Int.castRingHom ℂ) AZ ^ 3 := by
    have hA : PowerSeries.map (Int.castRingHom ℂ) AZ = qExpansion 1 E₄ := map_E₄
    have h2 : PowerSeries.X * (J * M) = PowerSeries.X * qExpansion 1 E₄ ^ 3 := by
      rw [← hJD, hCM]; ring
    rw [hA]
    exact mul_left_cancel₀ PowerSeries.X_ne_zero h2
  apply mul_right_cancel₀ hM0
  rw [h1, hM, ← map_mul, ← map_pow, hmul]

/-- Helper: the coefficient of $q^3$ in $qj$ is $21493760$. -/
theorem qParam_mul_j_coeff_three :
    (qExpansion 1 (fun τ : ℍ ↦ Function.Periodic.qParam 1 (τ : ℂ) *
      TauCeti.ModularForm.j τ)).coeff 3 = 21493760 := by
  have h := congrArg (PowerSeries.coeff (3 + 1))
    TauCeti.ModularForm.qExpansion_qParam_mul_j_mul_qExpansion_discriminant
  rw [PowerSeries.coeff_succ_X_mul] at h
  have e1 : (qExpansion 1 ModularForm.discriminant).coeff 1 = 1 := ramanujanTau_one
  have e2 : (qExpansion 1 ModularForm.discriminant).coeff 2 = -24 := ramanujanTau_two
  have e3 : (qExpansion 1 ModularForm.discriminant).coeff 3 = 252 := ramanujanTau_three
  have e4 : (qExpansion 1 ModularForm.discriminant).coeff 4 = -1472 := ramanujanTau_four
  have e0 := TauCeti.ModularForm.discriminant_qExpansion_coeff_zero
  have j0 := TauCeti.ModularForm.qExpansion_qParam_mul_j_coeff_zero
  have j1 := TauCeti.ModularForm.qExpansion_qParam_mul_j_coeff_one
  have j2 := TauCeti.ModularForm.qExpansion_qParam_mul_j_coeff_two
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, e0, e1, e2, e3, e4, j0, j1, j2,
    E₄_qExpansion_coeff_one, TauCeti.ModularForm.E₄_qExpansion_coeff_two,
    TauCeti.ModularForm.E₄_qExpansion_coeff_three,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩] at h
  linear_combination h

/-- **Theorem 4.22**: $j(z) = q^{-1} + 744 + 196884q + 21493760q^2 + \sum_{n\ge3}c(n)q^n$, $q = e^{2\pi i z}$,
with $c(n) \in \mathbb Z$ for all $n$. Stated as: there are integers $c(0), c(1), \dots$ with $c(0) = 744$,
$c(1) = 196884$, $c(2) = 21493760$ and $\sum_{n\ge0}c(n)q^n = j(z) - q^{-1}$ for every $z \in \mathbb H$. -/
@[kb "milne2017mf" "Section 4, Theorem 4.22 (pdf p. 58)"]
theorem jFun_qExpansion :
    ∃ c : ℕ → ℤ, c 0 = 744 ∧ c 1 = 196884 ∧ c 2 = 21493760 ∧
      ∀ z : ℍ, HasSum (fun n : ℕ ↦ (c n : ℂ) * cexp (2 * π * Complex.I * z) ^ n) (jFun z - (cexp (2 * π * Complex.I * z))⁻¹) := by
  obtain ⟨JZ, hJZ⟩ := exists_int_qParam_mul_j
  have hcoef : ∀ n : ℕ, (qExpansion 1 (fun τ : ℍ ↦ Function.Periodic.qParam 1 (τ : ℂ) *
      TauCeti.ModularForm.j τ)).coeff n = ((JZ.coeff n : ℤ) : ℂ) := by
    intro n
    rw [← hJZ, PowerSeries.coeff_map]
    simp
  refine ⟨fun n => JZ.coeff (n + 1), ?_, ?_, ?_, ?_⟩
  · have h := hcoef 1
    rw [TauCeti.ModularForm.qExpansion_qParam_mul_j_coeff_one] at h
    exact_mod_cast h.symm
  · have h := hcoef 2
    rw [TauCeti.ModularForm.qExpansion_qParam_mul_j_coeff_two] at h
    exact_mod_cast h.symm
  · have h := hcoef 3
    rw [qParam_mul_j_coeff_three] at h
    exact_mod_cast h.symm
  · intro z
    have h := TauCeti.ModularForm.hasSum_j_sub_inv_qParam z
    have hq : Function.Periodic.qParam 1 (z : ℂ) = cexp (2 * π * Complex.I * z) := by
      simp [Function.Periodic.qParam]
    rw [hq] at h
    rw [jFun_eq]
    simp only [hcoef] at h
    convert h using 2

end ModularFormsKB.Milne
