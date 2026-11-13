import ModularFormsKB.Historical.WeberHeegnerStark.Defs
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.FundamentalDiscriminant

/-!
# The named inputs of the Heegner–Stark theorem

Heegner's proof (1952), as completed by Stark (1969) and Deuring (1968), uses the theory of complex
multiplication only through a handful of classical theorems, most of them in Weber's
*Elliptische Functionen und algebraische Zahlen* (1891). We do not prove them here. Following this
repository's inputs rule, each is a field of the structure `WeberHeegnerStarkInputs`, with its source;
the theorem `ModularFormsKB.WeberHeegnerStark.heegnerStark_classNumber_eq_one_iff` takes the structure as a
hypothesis. None of the fields mentions class number one, the nine discriminants or Heegner's
Diophantine equation.

| Field | Classical theorem | Source | Status elsewhere |
|---|---|---|---|
| `isIntegral_kleinJ` | singular moduli are algebraic integers | Weber § 87 | not formalized |
| `finrank_kleinJ` | `[ℚ(j(τ)) : ℚ] = h(D)` (degree of the class equation) | Weber § 88; first main theorem of complex multiplication | not formalized |
| `imaginaryQuadratic` | `d_K` is a fundamental discriminant and `h_K = h(d_K)` | Dirichlet, Dedekind; Cox, Theorem 5.30 | Tau Ceti (form–ideal correspondence) |
| `classNumber_four_mul` | `h(-4m) = 3 h(-m)` for `m ≡ 3 mod 8`, `m > 3` | Weber § 89; Dirichlet's class number formula for orders | not formalized |
| `gammaTwo_mem` | `γ₂(τ)` is a class invariant | Weber § 92 | not formalized |
| `weberF_pow_eight_mem` | Weber's Theorem I: `f(√-m)⁸` is a class invariant | Weber § 94 | not formalized |
| `weberF_pow_three_mem` | Weber's Theorem VI: `f(√-m)³` is a class invariant, `m ≡ 3 mod 8` | Weber § 94, stated by Weber without proof; proved by Birch 1969 [from memory; to check] | not formalized |
| `weber_cubic` | `-f₂²⁴` is a root of `(u - 16)³ - j u` | Weber § 93 (1) | Tau Ceti: `siegelFunction_zero_half_pow_twelve_add_sixteen_pow_three` |

Section numbers are those of Weber's *Elliptische Functionen und algebraische Zahlen* (1891); the second
edition (*Lehrbuch der Algebra*, volume III, 1908) has not been compared.

Two fields are deliberately weaker than Weber's statements: `weberF_pow_three_mem` adds `3 ∤ m`
(Weber's Theorem VI has no such condition), and both Theorem I and Theorem VI are stated only at the
point `√-m`, the root of the principal form `x² + m y²`. A weaker hypothesis makes the conditional
theorem stronger.

The numerical consistency of the Weber fields beyond class number one was checked by an integer relation
search (`f(√-m)` has degree `3 h(-m)` for `m = 11, 35, 59`), so the structure is not vacuous for a
trivial reason.
-/

open NumberField Module IntermediateField
open UpperHalfPlane hiding I

namespace ModularFormsKB.WeberHeegnerStark

/-- **The named inputs of Heegner's proof.** Each field is a classical theorem, cited in its docstring;
see the module docstring for the table of sources. -/
structure WeberHeegnerStarkInputs : Prop where
  /-- **Singular moduli are algebraic integers** (Weber 1891, § 87, from the leading coefficient of
  the modular equation `F_n(u, u)`; Deuring; Cox, Theorem 11.1). If `τ` in the upper half-plane is
  imaginary quadratic, `j(τ)` is integral over `ℤ`. -/
  isIntegral_kleinJ : ∀ (τ : ℍ) (a b c : ℤ), a ≠ 0 →
    (a : ℂ) * (τ : ℂ) ^ 2 + b * τ + c = 0 → IsIntegral ℤ (kleinJ τ)
  /-- **The degree of a singular modulus is the class number** (Weber 1891, § 88: the class equation
  has degree `h`; in modern terms the first main theorem of complex multiplication, Cox,
  Theorem 11.1 and Proposition 13.2). If `τ` is the root of a primitive positive definite form of
  discriminant `D`, then `[ℚ(j(τ)) : ℚ] = h(D)`. -/
  finrank_kleinJ : ∀ (a b c : ℤ) (τ : ℍ), IsPrimitiveForm a b c → IsFormRoot a b c τ →
    finrank ℚ ℚ⟮kleinJ τ⟯ = formClassNumber (b ^ 2 - 4 * a * c)
  /-- **Dirichlet–Dedekind** (Cox, *Primes of the form x² + ny²*, §§ 5 and 7 [theorem numbers from memory]): the discriminant
  of an imaginary quadratic field is a fundamental discriminant, and the class number of the field
  equals the number of classes of primitive positive definite forms of that discriminant. -/
  imaginaryQuadratic : ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → discr K < 0 →
    Int.IsFundamentalDiscr (discr K) ∧ classNumber K = formClassNumber (discr K)
  /-- **Weber § 89**: for `m ≡ 3 mod 8` and `m > 3`, the order `ℤ[√-m]` has three times as
  many classes as `ℤ[(1 + √-m)/2]` (Dirichlet's class number formula for orders; Cox,
  Theorem 7.24 and Corollary 7.28). -/
  classNumber_four_mul : ∀ m : ℕ, m % 8 = 3 → 3 < m →
    formClassNumber (-4 * m) = 3 * formClassNumber (-m)
  /-- **`γ₂` is a class invariant** (Weber 1891, § 92; Cox, Theorem 12.2): if `τ` is the root
  of a primitive positive definite form `(a, b, c)` with `3 ∤ D`, `3 ∤ a` and `3 ∣ b`, then
  `γ₂(τ) ∈ ℚ(j(τ))`. -/
  gammaTwo_mem : ∀ (a b c : ℤ) (τ : ℍ), IsPrimitiveForm a b c → IsFormRoot a b c τ →
    ¬ (3 : ℤ) ∣ b ^ 2 - 4 * a * c → ¬ (3 : ℤ) ∣ a → (3 : ℤ) ∣ b → gammaTwo τ ∈ ℚ⟮kleinJ τ⟯
  /-- **Weber's Theorem I** (Weber 1891, § 94), at the root `√-m` of the principal form: for
  odd `m` with `3 ∤ m`, `f(√-m)⁸ ∈ ℚ(j(√-m))`. -/
  weberF_pow_eight_mem : ∀ (m : ℕ) (τ : ℍ), Odd m → ¬ 3 ∣ m →
    (τ : ℂ) = ((√(m : ℝ) : ℝ) : ℂ) * Complex.I → weberF τ ^ 8 ∈ ℚ⟮kleinJ τ⟯
  /-- **Weber's Theorem VI** (Weber 1891, § 94, p. 365), at the root `√-m` of the principal
  form: for `m ≡ 3 mod 8` (and, here, `3 ∤ m`), `f(√-m)³ ∈ ℚ(j(√-m))`. Weber states it as confirmed by
  all known examples, with the general proof missing; this is the "gap" in Heegner's proof. -/
  weberF_pow_three_mem : ∀ (m : ℕ) (τ : ℍ), m % 8 = 3 → ¬ 3 ∣ m →
    (τ : ℂ) = ((√(m : ℝ) : ℝ) : ℂ) * Complex.I → weberF τ ^ 3 ∈ ℚ⟮kleinJ τ⟯
  /-- **Weber's cubic** (Weber 1891, § 93 (1)): `f²⁴`, `-f₁²⁴`, `-f₂²⁴` are the roots of
  `(u - 16)³ - j u`; here the root `-f₂²⁴`. Proved in Tau Ceti as
  `TauCeti.ModularForm.siegelFunction_zero_half_pow_twelve_add_sixteen_pow_three`
  (`g_{(0,1/2)}¹² = f₂²⁴`). -/
  weber_cubic : ∀ τ : ℍ, (weberF₂ τ ^ 24 + 16) ^ 3 = kleinJ τ * weberF₂ τ ^ 24

/-- **The discriminant of `ℚ(√m)`** (Dedekind; textbook algebraic number theory, e.g. Marcus, *Number
Fields*, Chapter 2 [chapter from memory]). It is used only to restate the class number one theorem with
`K = ℚ(√-d)` instead of the discriminant: if a quadratic field `K` contains a square root of a squarefree
integer `m ≠ 1`, then `d_K = m` for `m ≡ 1 mod 4` and `d_K = 4m` otherwise. Not a statement about complex
multiplication, so it is kept apart from `WeberHeegnerStarkInputs`. -/
structure QuadraticDiscriminantInput : Prop where
  /-- `d_K = m` or `4m` for `K = ℚ(√m)`. -/
  discr_eq : ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → ∀ m : ℤ, Squarefree m →
    m ≠ 1 → IsSquare (m : K) → discr K = if m % 4 = 1 then m else 4 * m

end ModularFormsKB.WeberHeegnerStark
