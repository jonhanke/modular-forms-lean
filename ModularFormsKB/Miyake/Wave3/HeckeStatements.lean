import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.PrimePower
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators
import TauCeti.NumberTheory.ModularForms.DiamondOperators
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.MvPolynomial.Basic
import ModularFormsKB.Citation
/-!
# Miyake §4.5: statements of Theorems 4.5.9, 4.5.17 and 4.5.19 (not proved here)

Miyake, *Modular Forms* (Springer 1989), §4.5, pp. 142, 150 and 152.

These three theorems are stated as named propositions; none is proved in this repository.

* **Theorem 4.5.9** (`HeckeAlgebraPolynomialStatement N`): the Hecke algebra
  `ℛ(N) = ℛ(Γ₀(N), Δ₀(N))` over `ℤ` is the polynomial ring in `T(p)`, `T(p, p)` (`p ∤ N`) and
  `T(q)` (`q ∣ N`), all primes. Miyake's `Δ₀(N)` is Tau Ceti's `HeckeRing.GL2.Delta0 N`; `T(p)`
  is `HeckeRing.GL2.heckeTGeneratorGamma0 N p` (`Γ₀(N) diag(1, p) Γ₀(N)`) and `T(p, p)` is
  `HeckeRing.GL2.heckeTScalarGamma0 N p` (`Γ₀(N) diag(p, p) Γ₀(N)`). Tau Ceti has the
  multiplication table of these elements and the commutativity of `ℛ(N)`, but not the
  algebraic independence. Missing piece: the algebraic independence of the generators (Miyake
  derives it from Lemmas 4.5.7–4.5.8, the degrees of the double cosets).
* **Theorem 4.5.17** (Ramanujan–Petersson, Deligne; `RamanujanPeterssonStatement`). Miyake: "We
  do not prove this theorem in this book." **Erratum:** the book prints
  `a(n) = O(n^{(k-1)/2})` for every `f ∈ 𝒮_k(N, χ)` and `(n, N) = 1`. Deligne's theorem gives
  `|a(n)| ≤ d(n) n^{(k-1)/2}` for normalized eigenforms (from (4.5.41) at each prime), hence
  `O(n^{(k-1)/2 + ε})` for every `ε > 0`; the printed exponent without `ε` is too strong: for
  `Δ`, `limsup |τ(n)| n^{-11/2} = ∞` (Rankin) [unverified]. The statement below carries the `ε`.
* **Theorem 4.5.19** (Shimura, Theorems 3.48 and 3.52; `IntegralBasisStatement`) for
  `Γ = Γ₁(N)`, `k ≥ 2`: `𝒮_k(Γ₁(N))` has a basis whose Fourier coefficients at `∞` are rational
  integers, and whose `ℤ`-span is stable under every Hecke operator `T(n)` (so `ℛ(N)` acts by
  integral matrices). Miyake allows every `Γ` with `Γ₁(N) ⊆ Γ ⊆ Γ₀(N)`; only `Γ₁(N)` is stated
  here, with Tau Ceti's Hecke operators `heckeTCuspNat` (for `n` prime to `N`, and at all `n`
  through Tau Ceti's definition). Tau Ceti proves the integrality of the Hecke action on forms
  with integral coefficients at all cusps (`heckeTNat_mem_integralAtCusps`), not the existence of
  an integral basis. Missing piece: an integral structure on `𝒮_k` (Shimura's proof uses the
  `q`-expansion principle or Eichler–Shimura).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Filter Asymptotics Matrix.SpecialLinearGroup
open scoped MatrixGroups HeckeCosetModule

noncomputable section

namespace ModularFormsKB.Miyake

/-- The index set of the generators of `ℛ(N)` in Theorem 4.5.9: `T(p)` and `T(p, p)` for primes
`p ∤ N`, and `T(q)` for primes `q ∣ N`. -/
abbrev HeckeGenerators (N : ℕ) : Type :=
  {p : ℕ // p.Prime ∧ ¬ p ∣ N} ⊕ {p : ℕ // p.Prime ∧ ¬ p ∣ N} ⊕ {q : ℕ // q.Prime ∧ q ∣ N}

/-- The generators of Theorem 4.5.9 as elements of `ℛ(N) = 𝕋(Δ₀(N), Γ₀(N))` over `ℤ`. -/
def heckeGenerator (N : ℕ) [NeZero N] :
    HeckeGenerators N → 𝕋 (HeckeRing.GL2.Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ
  | .inl p => HeckeRing.GL2.heckeTGeneratorGamma0 N p.1
  | .inr (.inl p) => HeckeRing.GL2.heckeTScalarGamma0 N p.1
  | .inr (.inr q) => HeckeRing.GL2.heckeTGeneratorGamma0 N q.1

/-- **Miyake, Theorem 4.5.9** (statement, not proved here): `ℛ(N)` is the polynomial ring over
`ℤ` in `T(p)`, `T(p, p)` (`p ∤ N`) and `T(q)` (`q ∣ N`): there is a ring isomorphism from the
polynomial ring on these symbols onto `ℛ(N)` sending each variable to its generator. -/
@[kb "miyake1989" "Theorem 4.5.9, p. 142 (statement)"]
structure HeckeAlgebraPolynomialStatement (N : ℕ) [NeZero N] : Prop where
  exists_equiv : ∃ e : MvPolynomial (HeckeGenerators N) ℤ ≃+*
      𝕋 (HeckeRing.GL2.Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ,
    ∀ i, e (MvPolynomial.X i) = heckeGenerator N i

/-- **Miyake, Theorem 4.5.17** (Ramanujan–Petersson conjecture, proved by Deligne; statement,
corrected by `ε`, see the module docstring): for `f = Σ a(n) qⁿ ∈ 𝒮_k(N, χ)` and every `ε > 0`,
`a(n) = O(n^{(k-1)/2 + ε})` along the `n` prime to `N`. -/
@[kb "miyake1989" "Theorem 4.5.17, p. 150 (statement, with epsilon)"]
structure RamanujanPeterssonStatement : Prop where
  isBigO : ∀ (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k), f ∈ TauCeti.cuspFormCharSpace k χ →
    ∀ ε : ℝ, 0 < ε →
      (fun n : ℕ ↦ if n.Coprime N then (qExpansion 1 f).coeff n else 0)
        =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (((k : ℝ) - 1) / 2 + ε)

/-- **Miyake, Theorem 4.5.19** for `Γ = Γ₁(N)` (statement, not proved here): for `k ≥ 2`,
`𝒮_k(Γ₁(N))` has a basis whose Fourier coefficients at `∞` are rational integers (2), and the
`ℤ`-span of that basis is stable under every Hecke operator `T(n)` (1). -/
@[kb "miyake1989" "Theorem 4.5.19, p. 152 (statement, Gamma = Gamma1(N))"]
structure IntegralBasisStatement (N : ℕ) [NeZero N] (k : ℤ) : Prop where
  exists_basis : 2 ≤ k → ∃ (ι : Type) (b : Module.Basis ι ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)),
    (∀ i n, ∃ a : ℤ, (qExpansion 1 (b i)).coeff n = a) ∧
    ∀ (n : ℕ) [NeZero n] i, HeckeRing.GL2.heckeTCuspNat (N := N) k n (b i) ∈
      Submodule.span ℤ (Set.range b)

end ModularFormsKB.Miyake
