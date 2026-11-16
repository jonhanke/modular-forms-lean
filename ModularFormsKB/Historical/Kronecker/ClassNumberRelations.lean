import ModularFormsKB.Hurwitz.Relations
import ModularFormsKB.Citation
/-!
# Kronecker's weighted class numbers `G`, `F`, `E` and their elementary relations

Kronecker, *Werke* 4 (ed. Hensel, 1929), XXIII, p. 247,
and *Werke* 2 (1897), XVII (*Bilineare Formen mit vier Variabeln*), § 22, p. 484, the arithmetic proofs of the
relations of Crelle 57.

Kronecker counts classes of positive definite forms `ax² + 2bxy + cy²` with `ac - b² = n` (Gauss's convention,
discriminant `-4n`), the classes of the types `(1, 0, 1)` and `(1, 1, 1)` weighted `1/2` and `1/3`:

* `G(n)`: all classes;
* `F(n)`: the classes with `a` or `c` odd;
* `H(n) = G(n) - F(n)`: the classes with `a` and `c` both even (Kronecker's `H`);
* `E(n) = 2F(n) - G(n)`.

**Definitions used here.** `G(n)` is the weighted count of the forms of discriminant `-4n`, which is Tau Ceti's
Hurwitz class number `H(4n)` (`TauCeti.hurwitzClassNumber`, with the same weights; `hurwitzClassNumber_eq_classCount`
in `ModularFormsKB.Hurwitz.ClassNumber`). A form with `a = 2a'`, `c = 2c'` even has `4a'c' - b² = n`, so it is the
form `a'x² + bxy + c'y²` of discriminant `-n` read in Gauss's convention: Kronecker's `H(n)` is the Hurwitz class
number `H(n)`. So we *define* `F(n) = H(4n) - H(n)` (`kroneckerF`). The bijection behind this identification
(classes of determinant `n` with both outer coefficients even ↔ classes of discriminant `-n`) is not formalized
(loose end LE-MF-0261). At `n = 0` the definitions give `G(0) = -1/12`, `F(0) = 0`, `E(0) = 1/12`, Kronecker's
values in *Werke* 2.

The core library's `ModularFormsKB.Hurwitz.Relations` is imported (a wrapper, not a re-proof). Kronecker's
weighted counts used here are Tau Ceti's Hurwitz class numbers; this is a restriction recorded as LE-MF-0261.

## What is formalized
Werke 4, XXIII, p. 247:
* `kroneckerG_four_mul`: `G(4n) = F(4n) + G(n)` (immediate from the definitions above);
* `kroneckerG_eq_F_of_mod_four`: `G(n) = F(n)` for `n ≡ 1, 2 (mod 4)`. **Proved** (Tau Ceti's
  `hurwitzClassNumber_eq_zero_of_mod_four_eq_one_or_two`);
* `kroneckerG_eq_two_F_of_mod_eight`: `G(n) = 2F(n)` for `n ≡ 7 (mod 8)`, from the three-squares formula
  `ThreeSquaresClassNumber` of the core library (Gauss; proved there from Zagier's theorem and two named inputs);
* `KroneckerThreeModEight`: `3G(n) = 4F(n)` for `n ≡ 3 (mod 8)`. **Stated** (named proposition), checked by the
  kernel for the first values (`kroneckerThreeModEight_check`);
* `twelve_kroneckerE_eq_r3`: `12E(n) = r₃(n)`, from `ThreeSquaresClassNumber` (Gauss's theorem in Kronecker's form).

Werke 2, XVII, § 22, p. 484:
* `kroneckerE_four_mul` (`E(4n) = E(n)`) and `kroneckerE_eq_zero_of_mod_eight` (`E(n) = 0`, `n ≡ 7 mod 8`), from
  `ThreeSquaresClassNumber`; `kroneckerE_eq_F_of_mod_four` (`E(n) = F(n)`, `n ≡ 1, 2 mod 4`), proved;
  `kroneckerE_eq_two_thirds_F` (`E(n) = 2F(n)/3`, `n ≡ 3 mod 8`), from `KroneckerThreeModEight`;
* `three_sum_kroneckerE`: `3 ∑_{h² ≤ n} E(n - h²) = 2(2 + (-1)ⁿ) λ(n)`, `λ(n)` the sum of the odd divisors of `n`,
  from `ThreeSquaresClassNumber` and Jacobi's four-square theorem `JacobiFourSquares` (named input; Smith's Report
  art. 127) through `r4_eq_sum_r3`, the splitting of a four-square representation by its last
  coordinate (proved).
-/

noncomputable section

open Finset
open ModularFormsKB.Hurwitz

namespace ModularFormsKB.Historical.Kronecker

/-- Kronecker's `G(n)`: the weighted number of classes of positive definite forms `ax² + 2bxy + cy²` with
`ac - b² = n`; it is the Hurwitz class number `H(4n)` (see the module docstring). `G(0) = -1/12`. -/
def kroneckerG (n : ℕ) : ℚ := TauCeti.hurwitzClassNumber (4 * n)

/-- Kronecker's `F(n)`: the weighted number of those classes with an odd outer coefficient, `G(n) - H(n)`
(see the module docstring for the identification with Hurwitz class numbers). `F(0) = 0`. -/
def kroneckerF (n : ℕ) : ℚ := TauCeti.hurwitzClassNumber (4 * n) - TauCeti.hurwitzClassNumber n

/-- Kronecker's `E(n) = 2F(n) - G(n)`; `E(0) = 1/12`. -/
def kroneckerE (n : ℕ) : ℚ := 2 * kroneckerF n - kroneckerG n

theorem kroneckerE_eq (n : ℕ) :
    kroneckerE n = TauCeti.hurwitzClassNumber (4 * n) - 2 * TauCeti.hurwitzClassNumber n := by
  unfold kroneckerE kroneckerF kroneckerG; ring

/-! ### Werke 4, XXIII -/

/-- **`G(4n) = F(4n) + G(n)`** (Kronecker, Werke 4, XXIII, p. 247). -/
@[kb "kronecker1929" "XXIII, p. 247: G(4n) = F(4n) + G(n)"]
theorem kroneckerG_four_mul (n : ℕ) : kroneckerG (4 * n) = kroneckerF (4 * n) + kroneckerG n := by
  unfold kroneckerG kroneckerF; ring

/-- **`G(n) = F(n)` for `n ≡ 1, 2 (mod 4)`** (Kronecker, Werke 4, XXIII, p. 247: `G(4n+1) = F(4n+1)`,
`G(4n+2) = F(4n+2)`). -/
@[kb "kronecker1929" "XXIII, p. 247: G(4n+1) = F(4n+1), G(4n+2) = F(4n+2)"]
theorem kroneckerG_eq_F_of_mod_four {n : ℕ} (hn : n % 4 = 1 ∨ n % 4 = 2) : kroneckerG n = kroneckerF n := by
  unfold kroneckerG kroneckerF
  rw [TauCeti.hurwitzClassNumber_eq_zero_of_mod_four_eq_one_or_two hn]; ring

/-- **`G(n) = 2F(n)` for `n ≡ 7 (mod 8)`** (Kronecker, Werke 4, XXIII, p. 247: `G(8n+7) = 2F(8n+7)`),
from the three-squares formula `ThreeSquaresClassNumber`. -/
@[kb "kronecker1929" "XXIII, p. 247: G(8n+7) = 2 F(8n+7)"]
theorem kroneckerG_eq_two_F_of_mod_eight (h : ThreeSquaresClassNumber) {n : ℕ} (hn : n % 8 = 7) :
    kroneckerG n = 2 * kroneckerF n := by
  unfold kroneckerG kroneckerF
  rw [hurwitz_four_mul_of_mod_eight h hn]; ring

/-- **Kronecker's relation `3G(n) = 4F(n)` for `n ≡ 3 (mod 8)`** (Werke 4, XXIII, p. 247:
`3G(8n+3) = 4F(8n+3)`), stated as a named proposition. In Hurwitz class numbers it says `H(4n) = 4H(n)` for
`n ≡ 3 (mod 8)`, the case `(-n/2) = -1` of the class number formula for orders; not formalized (LE-MF-0262). -/
@[kb "kronecker1929" "XXIII, p. 247: 3 G(8n+3) = 4 F(8n+3) (stated)"]
def KroneckerThreeModEight : Prop := ∀ n : ℕ, n % 8 = 3 → 3 * kroneckerG n = 4 * kroneckerF n

/-- `KroneckerThreeModEight` holds for `n = 3, 11, …, 59` (checked by the kernel). -/
theorem kroneckerThreeModEight_check :
    ∀ k ∈ range 8, 3 * kroneckerG (8 * k + 3) = 4 * kroneckerF (8 * k + 3) := by
  unfold kroneckerG kroneckerF
  decide +kernel

/-- **`12E(n) = r₃(n)`** (Kronecker, Werke 4, XXIII, p. 247): Gauss's three-squares theorem in
Kronecker's form, from `ThreeSquaresClassNumber`. -/
@[kb "kronecker1929" "XXIII, p. 247: 12 E(n) = r_3(n)"]
theorem twelve_kroneckerE_eq_r3 (h : ThreeSquaresClassNumber) (n : ℕ) : 12 * kroneckerE n = r3 n := by
  rw [kroneckerE_eq, h.r3_eq]

/-! ### Werke 2, XVII -/

/-- **`E(4n) = E(n)`** (Kronecker, Werke 2, XVII, § 22, p. 484), from `ThreeSquaresClassNumber` and
`r₃(4n) = r₃(n)`. -/
@[kb "kronecker1897" "XVII, § 22, p. 484: E(4n) = E(n)"]
theorem kroneckerE_four_mul (h : ThreeSquaresClassNumber) (n : ℕ) : kroneckerE (4 * n) = kroneckerE n := by
  have h1 := twelve_kroneckerE_eq_r3 h (4 * n)
  have h2 := twelve_kroneckerE_eq_r3 h n
  rw [r3_four_mul] at h1
  linarith

/-- **`E(n) = F(n)` for `n ≡ 1, 2 (mod 4)`** (Kronecker, Werke 2, XVII, § 22, p. 484). -/
@[kb "kronecker1897" "XVII, § 22, p. 484: E(n) = F(n) for n = 1, 2 mod 4"]
theorem kroneckerE_eq_F_of_mod_four {n : ℕ} (hn : n % 4 = 1 ∨ n % 4 = 2) : kroneckerE n = kroneckerF n := by
  unfold kroneckerE
  rw [kroneckerG_eq_F_of_mod_four hn]; ring

/-- **`E(n) = 2F(n)/3` for `n ≡ 3 (mod 8)`** (Kronecker, Werke 2, XVII, § 22, p. 484), from
`KroneckerThreeModEight`. -/
@[kb "kronecker1897" "XVII, § 22, p. 484: E(n) = 2F(n)/3 for n = 3 mod 8"]
theorem kroneckerE_eq_two_thirds_F (hK : KroneckerThreeModEight) {n : ℕ} (hn : n % 8 = 3) :
    kroneckerE n = 2 / 3 * kroneckerF n := by
  have := hK n hn
  unfold kroneckerE
  linarith

/-- **`E(n) = 0` for `n ≡ 7 (mod 8)`** (Kronecker, Werke 2, XVII, § 22, p. 484), from
`ThreeSquaresClassNumber` and `r₃(n) = 0`. -/
@[kb "kronecker1897" "XVII, § 22, p. 484: E(n) = 0 for n = 7 mod 8"]
theorem kroneckerE_eq_zero_of_mod_eight (h : ThreeSquaresClassNumber) {n : ℕ} (hn : n % 8 = 7) :
    kroneckerE n = 0 := by
  have := twelve_kroneckerE_eq_r3 h n
  rw [r3_eq_zero_of_mod_eight hn] at this
  push_cast at this
  linarith

/-! ### Four squares -/

/-- The representations of `n` as `x² + y² + z² + w²` with `|x|, |y|, |z|, |w| ≤ √n`. -/
def fourSquareReps (n : ℕ) : Finset (ℤ × ℤ × ℤ × ℤ) :=
  {v ∈ Icc (-(n.sqrt : ℤ)) n.sqrt ×ˢ Icc (-(n.sqrt : ℤ)) n.sqrt ×ˢ Icc (-(n.sqrt : ℤ)) n.sqrt ×ˢ
      Icc (-(n.sqrt : ℤ)) n.sqrt | v.1 ^ 2 + v.2.1 ^ 2 + v.2.2.1 ^ 2 + v.2.2.2 ^ 2 = n}

/-- **`r₄(n)`**, the number of `(x, y, z, w) ∈ ℤ⁴` with `x² + y² + z² + w² = n`. -/
def r4 (n : ℕ) : ℕ := #(fourSquareReps n)

/-- `λ(n)`: the sum of the odd divisors of `n` (Kronecker's `λ` in Werke 2, Smith's `σ_odd`). -/
def oddDivisorSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors with Odd d, d

/-- **Input: Jacobi's four-square theorem** (Jacobi, *Fundamenta nova* 1829, § 40–42; in the form of Smith's
*Report on the Theory of Numbers*, art. 127, pp. 306–307:`ϑ₃(q)⁴ = 1 + 8 ∑ (2 + (-1)ⁿ) σ_odd(n) qⁿ`):
`r₄(n) = 8 (2 + (-1)ⁿ) λ(n)` for `n ≥ 1`. -/
@[kb "smith1894" "Report on the Theory of Numbers, art. 127, p. 306: theta_3^4 = 1 + 8 sum (2 + (-1)^n) sigma_odd(n) q^n"]
structure JacobiFourSquares : Prop where
  r4_eq : ∀ n : ℕ, 0 < n → (r4 n : ℤ) = 8 * (2 + (-1) ^ n) * oddDivisorSum n

/-- `JacobiFourSquares` holds for `1 ≤ n ≤ 12` (checked by the kernel). -/
theorem jacobiFourSquares_check :
    ∀ n ∈ Icc 1 12, (r4 n : ℤ) = 8 * (2 + (-1) ^ n) * oddDivisorSum n := by
  decide +kernel

/-- **A four-square representation split by its first coordinate**: `r₄(n) = ∑_{|h| ≤ √n} r₃(n - h²)`. -/
theorem r4_eq_sum_r3 (n : ℕ) :
    r4 n = ∑ h ∈ Icc (-(n.sqrt : ℤ)) n.sqrt, r3 (n - h.natAbs ^ 2) := by
  unfold r4
  have hmaps : ∀ v ∈ fourSquareReps n, v.1 ∈ Icc (-(n.sqrt : ℤ)) n.sqrt := fun v hv ↦
    (mem_product.1 (mem_filter.1 hv).1).1
  rw [card_eq_sum_card_fiberwise hmaps]
  refine sum_congr rfl fun h _ ↦ ?_
  unfold r3
  refine card_nbij' (fun v ↦ v.2) (fun w ↦ (h, w)) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [coe_filter, fourSquareReps, mem_filter, mem_product, Set.mem_ofPred_eq] at hv
    obtain ⟨⟨⟨_, _, _, _⟩, hsum⟩, rfl⟩ := hv
    have hle : v.1.natAbs ^ 2 ≤ n := by
      have : (v.1.natAbs : ℤ) ^ 2 ≤ n := by
        rw [Int.natAbs_sq]; nlinarith [sq_nonneg v.2.1, sq_nonneg v.2.2.1, sq_nonneg v.2.2.2]
      exact_mod_cast this
    have hcast : ((n - v.1.natAbs ^ 2 : ℕ) : ℤ) = n - v.1 ^ 2 := by
      rw [Nat.cast_sub hle]; push_cast; rw [sq_abs]
    simp only [coe_filter, threeSquareReps, mem_product, Set.mem_ofPred_eq]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · apply mem_Icc_sqrt_of_sq_le; rw [hcast]
      nlinarith [sq_nonneg v.2.2.1, sq_nonneg v.2.2.2]
    · apply mem_Icc_sqrt_of_sq_le; rw [hcast]
      nlinarith [sq_nonneg v.2.1, sq_nonneg v.2.2.2]
    · apply mem_Icc_sqrt_of_sq_le; rw [hcast]
      nlinarith [sq_nonneg v.2.1, sq_nonneg v.2.2.1]
    · rw [hcast]; linarith
  · intro w hw
    simp only [coe_filter, threeSquareReps, mem_product, Set.mem_ofPred_eq] at hw
    obtain ⟨_, hsum⟩ := hw
    have hh : h ∈ Icc (-(n.sqrt : ℤ)) n.sqrt := by assumption
    have hle : h.natAbs ^ 2 ≤ n := by
      have h1 : h.natAbs ≤ n.sqrt := by
        rw [mem_Icc] at hh; omega
      calc h.natAbs ^ 2 ≤ n.sqrt ^ 2 := Nat.pow_le_pow_left h1 2
        _ ≤ n := Nat.sqrt_le' n
    have hcast : ((n - h.natAbs ^ 2 : ℕ) : ℤ) = n - h ^ 2 := by
      rw [Nat.cast_sub hle]; push_cast; rw [sq_abs]
    rw [hcast] at hsum
    simp only [coe_filter, fourSquareReps, mem_filter, mem_product, Set.mem_ofPred_eq]
    refine ⟨⟨⟨hh, ?_, ?_, ?_⟩, by linarith⟩, trivial⟩
    · apply mem_Icc_sqrt_of_sq_le
      nlinarith [sq_nonneg h, sq_nonneg w.2.1, sq_nonneg w.2.2]
    · apply mem_Icc_sqrt_of_sq_le
      nlinarith [sq_nonneg h, sq_nonneg w.1, sq_nonneg w.2.2]
    · apply mem_Icc_sqrt_of_sq_le
      nlinarith [sq_nonneg h, sq_nonneg w.1, sq_nonneg w.2.1]
  · intro v hv
    simp only [coe_filter, Set.mem_ofPred_eq] at hv
    simp [hv.2.symm]
  · intro w _
    rfl

/-- **Kronecker's consequence of the three- and four-square theorems** (Werke 2, XVII, § 22, p. 484):
for `n ≥ 1`, `3 ∑_{h² ≤ n} E(n - h²) = 2 (2 + (-1)ⁿ) λ(n)`, from `ThreeSquaresClassNumber` and `JacobiFourSquares`. -/
@[kb "kronecker1897" "XVII, § 22, p. 484: 3 sum_h E(n - h^2) = 2(2 + (-1)^n) lambda(n)"]
theorem three_sum_kroneckerE (h : ThreeSquaresClassNumber) (hJ : JacobiFourSquares) {n : ℕ} (hn : 0 < n) :
    3 * ∑ k ∈ Icc (-(n.sqrt : ℤ)) n.sqrt, kroneckerE (n - k.natAbs ^ 2) =
      2 * (2 + (-1) ^ n) * oddDivisorSum n := by
  have hE : ∀ m, kroneckerE m = (r3 m : ℚ) / 12 := fun m ↦ by
    have := twelve_kroneckerE_eq_r3 h m
    linarith
  simp_rw [hE]
  rw [← Finset.sum_div, ← Nat.cast_sum, ← r4_eq_sum_r3]
  have h' : (r4 n : ℚ) = 8 * (2 + (-1) ^ n) * oddDivisorSum n := by exact_mod_cast hJ.r4_eq n hn
  rw [h']
  ring

end ModularFormsKB.Historical.Kronecker
