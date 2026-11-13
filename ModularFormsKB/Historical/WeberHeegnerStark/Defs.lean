import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Weber's functions, the modular invariant and the form class number

The objects of the Weber–Heegner–Stark proof of the class number one theorem, built from Mathlib only.

* `kleinJ τ = E₄(τ)³ / Δ(τ)`: the modular invariant, normalized so that `j(i) = 1728`
  (Weber writes `j`; Tau Ceti's `TauCeti.ModularForm.j` is the same quotient).
* `gammaTwo τ = E₄(τ) / η(τ)⁸`: Weber's `γ₂`, a cube root of `j` (`gammaTwo_pow_three`).
* `weberF τ = e^{-πi/24} η((τ+1)/2) / η(τ)` and `weberF₂ τ = √2 η(2τ) / η(τ)`: Weber's `f` and `f₂`
  (Weber 1891, § 34; with `q = e^{πiτ}`, `f = q^{-1/24} ∏ (1 + q^{2n-1})` and
  `f₂ = √2 q^{1/12} ∏ (1 + q^{2n})`).
* `IsReducedForm D a b c` and `formClassNumber D`: Gauss's reduced primitive positive definite forms
  `a x² + b x y + c y²` of discriminant `D = b² - 4ac < 0`, and their number `h(D)`. Weber writes forms as
  `(a, 2b, c)` with determinant `b² - ac`; we use the modern discriminant.

The functions `weberF`, `weberF₂` take a complex argument, since Mathlib's `η` does; they are only used
on the upper half-plane.
-/

noncomputable section

open ModularForm Complex
open UpperHalfPlane hiding I
open scoped Real

namespace ModularFormsKB.WeberHeegnerStark

/-- The modular invariant `j = E₄³ / Δ`. -/
def kleinJ (τ : ℍ) : ℂ := E₄ τ ^ 3 / discriminant τ

/-- Weber's `γ₂ = E₄ / η⁸` (Weber 1891, § 92; Cox, *Primes of the form x² + ny²*, § 12). -/
def gammaTwo (τ : ℍ) : ℂ := E₄ τ / ModularForm.eta τ ^ 8

/-- Weber's `f(τ) = e^{-πi/24} η((τ+1)/2) / η(τ)` (Weber 1891, § 34). -/
def weberF (τ : ℂ) : ℂ := cexp (-(π * I) / 24) * ModularForm.eta ((τ + 1) / 2) / ModularForm.eta τ

/-- Weber's `f₂(τ) = √2 η(2τ) / η(τ)` (Weber 1891, § 34). -/
def weberF₂ (τ : ℂ) : ℂ := ((√2 : ℝ) : ℂ) * ModularForm.eta (2 * τ) / ModularForm.eta τ

theorem gammaTwo_pow_three (τ : ℍ) : gammaTwo τ ^ 3 = kleinJ τ := by
  rw [gammaTwo, kleinJ, discriminant, div_pow, ← pow_mul]

/-! ### Binary quadratic forms -/

/-- The form `a x² + b x y + c y²` is primitive: `gcd(a, b, c) = 1`. -/
def IsPrimitiveForm (a b c : ℤ) : Prop := Int.gcd (Int.gcd a b) c = 1

/-- `a x² + b x y + c y²` is a reduced primitive positive definite form of discriminant `D`:
`b² - 4ac = D`, `|b| ≤ a ≤ c`, `b ≥ 0` if `|b| = a` or `a = c`, and `gcd(a, b, c) = 1`.
For `D < 0` every class of primitive positive definite forms contains exactly one reduced form
(Gauss, *Disquisitiones* § 171–172; Cox, Theorem 2.8). -/
def IsReducedForm (D a b c : ℤ) : Prop :=
  b ^ 2 - 4 * a * c = D ∧ 0 < a ∧ |b| ≤ a ∧ a ≤ c ∧ ((|b| = a ∨ a = c) → 0 ≤ b) ∧
    IsPrimitiveForm a b c

instance (D a b c : ℤ) : Decidable (IsReducedForm D a b c) := by
  unfold IsReducedForm IsPrimitiveForm; infer_instance

/-- The finite set of reduced primitive positive definite forms of discriminant `D`, as triples
`(a, b, c)`. A reduced form has `3a² ≤ |D|`, so `a ≤ √|D|` and `|b| ≤ a`; `c` is determined. -/
def reducedForms (D : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  let N : ℤ := Nat.sqrt D.natAbs
  ((Finset.Icc 1 N ×ˢ Finset.Icc (-N) N).image fun ab ↦
      (ab.1, ab.2, (ab.2 ^ 2 - D) / (4 * ab.1))).filter
    fun t ↦ IsReducedForm D t.1 t.2.1 t.2.2

/-- The form class number `h(D)`: the number of classes of primitive positive definite forms of
discriminant `D < 0`, counted by reduced forms. -/
def formClassNumber (D : ℤ) : ℕ := (reducedForms D).card

/-- `τ` is the root in the upper half-plane of the positive definite form `a x² + b x y + c y²`:
`a > 0`, `D = b² - 4ac < 0` and `τ = (-b + i √|D|) / (2a)`. -/
def IsFormRoot (a b c : ℤ) (τ : ℍ) : Prop :=
  0 < a ∧ b ^ 2 - 4 * a * c < 0 ∧
    (τ : ℂ) = (-(b : ℂ) + (Real.sqrt ((-(b ^ 2 - 4 * a * c) : ℤ) : ℝ) : ℂ) * I) / (2 * a)

end ModularFormsKB.WeberHeegnerStark
