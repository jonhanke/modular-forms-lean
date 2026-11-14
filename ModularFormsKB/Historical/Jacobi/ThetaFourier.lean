import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import ModularFormsKB.Citation
/-!
# The Fourier series of Jacobi's `Θ` and `H`

Jacobi, *Fundamenta nova theoriae functionum ellipticarum* (1829), §§ 61–63, pp. 176–180: with
`q = e^{-πK'/K}`,

  `Θ(2Kx/π) ∝ 1 - 2q cos 2x + 2q⁴ cos 4x - 2q⁹ cos 6x + …`,
  `H(2Kx/π) ∝ 2 q^{1/4} sin x - 2 q^{9/4} sin 3x + 2 q^{25/4} sin 5x - …`. Jacobi obtains
the coefficients by comparing coefficients in the shift relations
`Θ(u + 2K) = Θ(u)`, `Θ(u + 2iK') = -e^{π(K' - iu)/K} Θ(u)`.

## What is formalized

Mathlib's `jacobiTheta₂ z τ = ∑_{n ∈ ℤ} e^{2πinz + πin²τ}`. Put `q = e^{πiτ}` (Jacobi's `q` for `τ = iK'/K`)
and, for complex `x`,

* `jacobiΘ x τ = jacobiTheta₂ (x/π + 1/2) τ = ∑ (-1)ⁿ q^{n²} e^{2inx}` (the series `ϑ₄`),
* `jacobiH x τ = -i e^{ix + πiτ/4} jacobiTheta₂ (x/π + 1/2 + τ/2) τ = ∑ (-1)ⁿ q^{(n+1/2)²} e^{(2n+1)ix} / i`
  (the series `ϑ₁`).

Proved: the cosine and sine forms of these series (`jacobiΘ_eq_cos_series`, `jacobiH_eq_sin_series`), which
are Jacobi's displayed Fourier series, and the shift relations (`jacobiΘ_add_pi`,
`jacobiΘ_add_pi_mul_tau`).

Not formalized: Jacobi defines `Θ` and `H` from the elliptic functions (`Θ(u) = Θ(0) exp ∫₀ᵘ Z(u) du`, with `Z`
from the integral of the second kind, and `H(u) = √k sn u · Θ(u)` up to a constant). The identification of
those analytically defined functions with the series, i.e. that Jacobi's `Θ(2Kx/π)` is a constant multiple of
`jacobiΘ x (iK'/K)`, needs Jacobi's elliptic functions and the complete integrals `K`, `K'`, which Mathlib
lacks; it is the loose end of this file.
-/

noncomputable section

open Complex
open scoped Real

namespace ModularFormsKB.Historical.Jacobi

/-- The theta series `ϑ₄` in Jacobi's variable: `Θ(x, τ) = ∑_{n ∈ ℤ} (-1)ⁿ q^{n²} e^{2inx}`, `q = e^{πiτ}`. -/
def jacobiΘ (x τ : ℂ) : ℂ := jacobiTheta₂ (x / π + 1 / 2) τ

/-- The theta series `ϑ₁` in Jacobi's variable:
`H(x, τ) = -i ∑_{n ∈ ℤ} (-1)ⁿ q^{(n + 1/2)²} e^{(2n+1)ix}`, `q = e^{πiτ}`. -/
def jacobiH (x τ : ℂ) : ℂ :=
  -I * cexp (I * x + π * I * τ / 4) * jacobiTheta₂ (x / π + 1 / 2 + τ / 2) τ

private lemma theta_term_nat (k : ℕ) (x τ : ℂ) :
    jacobiTheta₂_term k (x / π + 1 / 2) τ =
      (-1) ^ k * cexp (π * I * (k : ℂ) ^ 2 * τ) * cexp (2 * k * x * I) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have e : 2 * π * I * (k : ℂ) * (x / π + 1 / 2) + π * I * (k : ℂ) ^ 2 * τ =
      (k : ℂ) * (π * I) + π * I * (k : ℂ) ^ 2 * τ + 2 * k * x * I := by
    field_simp; ring
  simp only [jacobiTheta₂_term, Int.cast_natCast]
  rw [e, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

private lemma theta_term_neg (k : ℕ) (x τ : ℂ) :
    jacobiTheta₂_term (-(k : ℤ)) (x / π + 1 / 2) τ =
      (-1) ^ k * cexp (π * I * (k : ℂ) ^ 2 * τ) * cexp (-(2 * k * x) * I) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have e : 2 * π * I * (-(k : ℂ)) * (x / π + 1 / 2) + π * I * (-(k : ℂ)) ^ 2 * τ =
      (k : ℂ) * (-(π * I)) + π * I * (k : ℂ) ^ 2 * τ + -(2 * k * x) * I := by
    field_simp; ring
  have h : cexp (-(π * I)) = -1 := by rw [Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  simp only [jacobiTheta₂_term, Int.cast_neg, Int.cast_natCast]
  rw [e, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul, h]

private lemma theta_pair (k : ℕ) (x τ : ℂ) :
    jacobiTheta₂_term k (x / π + 1 / 2) τ + jacobiTheta₂_term (-(k : ℤ)) (x / π + 1 / 2) τ =
      2 * ((-1) ^ k * cexp (π * I * (k : ℂ) ^ 2 * τ) * Complex.cos (2 * k * x)) := by
  rw [theta_term_nat, theta_term_neg]
  have := Complex.two_cos (2 * k * x)
  linear_combination ((-1) ^ k * cexp (π * I * (k : ℂ) ^ 2 * τ)) * -this

private lemma H_pair (n : ℕ) (x τ : ℂ) :
    cexp (I * x + π * I * τ / 4) *
      (jacobiTheta₂_term n (x / π + 1 / 2 + τ / 2) τ +
        jacobiTheta₂_term (-((n : ℤ) + 1)) (x / π + 1 / 2 + τ / 2) τ) =
      (-1) ^ n * cexp (π * I * ((n : ℂ) + 1 / 2) ^ 2 * τ) * (2 * I * Complex.sin ((2 * n + 1) * x)) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have e1 : I * x + π * I * τ / 4 + (2 * π * I * (n : ℂ) * (x / π + 1 / 2 + τ / 2) + π * I * (n : ℂ) ^ 2 * τ) =
      (n : ℂ) * (π * I) + (π * I * ((n : ℂ) + 1 / 2) ^ 2 * τ + (2 * n + 1) * x * I) := by
    field_simp; ring
  have e2 : I * x + π * I * τ / 4 + (2 * π * I * (-((n : ℂ) + 1)) * (x / π + 1 / 2 + τ / 2) +
      π * I * (-((n : ℂ) + 1)) ^ 2 * τ) =
      ((n + 1 : ℕ) : ℂ) * (-(π * I)) + (π * I * ((n : ℂ) + 1 / 2) ^ 2 * τ + (-((2 * n + 1) * x)) * I) := by
    push_cast; field_simp; ring
  have h : cexp (-(π * I)) = -1 := by rw [Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  simp only [jacobiTheta₂_term, Int.cast_neg, Int.cast_natCast, Int.cast_add, Int.cast_one]
  rw [mul_add, ← Complex.exp_add, ← Complex.exp_add, e1, e2, Complex.exp_add, Complex.exp_add,
    Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_nat_mul, h,
    Complex.exp_pi_mul_I]
  have h2 := Complex.two_sin ((2 * n + 1) * x)
  have h3 : 2 * I * Complex.sin ((2 * n + 1) * x) =
      cexp ((2 * n + 1) * x * I) - cexp (-((2 * n + 1) * x) * I) := by
    linear_combination I * h2 + (cexp (-((2 * n + 1) * x) * I) - cexp ((2 * n + 1) * x * I)) * Complex.I_sq
  rw [h3]
  ring

/-- **Fourier series of `Θ`** (Jacobi, *Fundamenta nova* § 62, p. 176):
`Θ(x) = 1 - 2q cos 2x + 2q⁴ cos 4x - … = 1 + 2 ∑_{n ≥ 1} (-1)ⁿ q^{n²} cos 2nx`, with `q^{n²} = e^{πin²τ}`. -/
@[kb "jacobi1829" "§ 62, p. 176"]
theorem jacobiΘ_eq_cos_series (x : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiΘ x τ = 1 + 2 * ∑' n : ℕ+,
      (-1 : ℂ) ^ (n : ℕ) * cexp (π * I * (n : ℂ) ^ 2 * τ) * Complex.cos (2 * n * x) := by
  have hs := (summable_jacobiTheta₂_term_iff (x / π + 1 / 2) τ).mpr hτ
  have h3 : Summable fun n : ℕ+ ↦ jacobiTheta₂_term ((n : ℕ) : ℤ) (x / π + 1 / 2) τ :=
    hs.comp_injective (i := fun n : ℕ+ ↦ ((n : ℕ) : ℤ))
      (fun a b h ↦ PNat.coe_injective (Nat.cast_injective (R := ℤ) h))
  have h4 : Summable fun n : ℕ+ ↦ jacobiTheta₂_term (-((n : ℕ) : ℤ)) (x / π + 1 / 2) τ :=
    hs.comp_injective (i := fun n : ℕ+ ↦ -((n : ℕ) : ℤ))
      (fun a b h ↦ PNat.coe_injective (by simpa using h))
  unfold jacobiΘ jacobiTheta₂
  rw [tsum_int_eq_zero_add_tsum_pnat hs, add_assoc, ← h3.tsum_add h4]
  have h0 : jacobiTheta₂_term 0 (x / π + 1 / 2) τ = 1 := by simp [jacobiTheta₂_term]
  rw [h0, ← tsum_mul_left]
  refine congrArg (1 + ·) (tsum_congr fun n ↦ ?_)
  have := theta_pair (n : ℕ) x τ
  simpa using this

/-- **Fourier series of `H`** (Jacobi, *Fundamenta nova* § 62, pp. 177–178):
`H(x) = 2 q^{1/4} sin x - 2 q^{9/4} sin 3x + … = 2 ∑_{n ≥ 0} (-1)ⁿ q^{(n + 1/2)²} sin (2n+1)x`, with
`q^{(n+1/2)²} = e^{πi(n+1/2)²τ}`. -/
@[kb "jacobi1829" "§ 62, pp. 177–178"]
theorem jacobiH_eq_sin_series (x : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiH x τ = 2 * ∑' n : ℕ,
      (-1 : ℂ) ^ n * cexp (π * I * ((n : ℂ) + 1 / 2) ^ 2 * τ) * Complex.sin ((2 * n + 1) * x) := by
  have hs := (summable_jacobiTheta₂_term_iff (x / π + 1 / 2 + τ / 2) τ).mpr hτ
  have hs1 : Summable fun n : ℕ ↦ jacobiTheta₂_term (n : ℤ) (x / π + 1 / 2 + τ / 2) τ :=
    hs.comp_injective (i := fun n : ℕ ↦ (n : ℤ)) Nat.cast_injective
  have hs2 : Summable fun n : ℕ ↦
      jacobiTheta₂_term (-((n : ℤ) + 1)) (x / π + 1 / 2 + τ / 2) τ :=
    hs.comp_injective (i := fun n : ℕ ↦ -((n : ℤ) + 1)) (fun a b h ↦ by simpa using h)
  have hsplit := tsum_of_nat_of_neg_add_one
    (f := fun n : ℤ ↦ jacobiTheta₂_term n (x / π + 1 / 2 + τ / 2) τ) hs1 hs2
  rw [← hs1.tsum_add hs2] at hsplit
  unfold jacobiH jacobiTheta₂
  rw [hsplit, mul_assoc, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  have := H_pair n x τ
  linear_combination (-I) * this + (-2 * (-1) ^ n * cexp (π * I * ((n : ℂ) + 1 / 2) ^ 2 * τ) *
    Complex.sin ((2 * n + 1) * x)) * Complex.I_sq

/-- Shift relation `Θ(u + 2K) = Θ(u)`, i.e. `Θ(x + π) = Θ(x)` (Jacobi, *Fundamenta nova* §§ 61–62). -/
@[kb "jacobi1829" "§ 62, shift relations, p. 176"]
theorem jacobiΘ_add_pi (x τ : ℂ) : jacobiΘ (x + π) τ = jacobiΘ x τ := by
  unfold jacobiΘ
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (x + π) / π + 1 / 2 = (x / π + 1 / 2) + 1 by field_simp; ring]
  exact jacobiTheta₂_add_left _ _

/-- Shift relation `Θ(u + 2iK') = -e^{π(K' - iu)/K} Θ(u)`, i.e. `Θ(x + πτ) = -q⁻¹ e^{-2ix} Θ(x)` with
`q = e^{πiτ}` (Jacobi, *Fundamenta nova* §§ 61–62). -/
@[kb "jacobi1829" "§ 62, shift relations, p. 176"]
theorem jacobiΘ_add_pi_mul_tau (x τ : ℂ) :
    jacobiΘ (x + π * τ) τ = -cexp (-(π * I * τ)) * cexp (-(2 * I * x)) * jacobiΘ x τ := by
  unfold jacobiΘ
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h : cexp (-(π * I)) = -1 := by rw [Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  have e : cexp (-π * I * (τ + 2 * (x / π + 1 / 2))) =
      cexp (-(π * I * τ)) * cexp (-(2 * I * x)) * cexp (-(π * I)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    field_simp; ring
  rw [show (x + π * τ) / π + 1 / 2 = (x / π + 1 / 2) + τ by field_simp; ring,
    jacobiTheta₂_add_left', e, h]
  ring

end ModularFormsKB.Historical.Jacobi
