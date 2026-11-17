/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import ModularFormsKB.HalfIntegral.KohnenLUFourProof
import ModularFormsKB.HalfIntegral.PlusHeckeAdjoint
import ModularFormsKB.HalfIntegral.ZagierKernel.KohnenKernelSquare
import ModularFormsKB.HalfIntegral.KohnenTraceReduction

/-!
# Headline statements of modular-forms-lean 0.5.1: Kohnen's plus space and the Kohnen–Zagier formula

A topic, not a book: Kohnen's plus space `S⁺_{k+1/2}(4)` of cusp forms of weight `k + 1/2` on `Γ₀(4)` (W. Kohnen,
*Modular forms of half-integral weight on Γ₀(4)*, Math. Ann. 248 (1980)), Kohnen's isomorphism with
`S_{2k}(SL₂(ℤ))`, the Kohnen–Zagier formula for the squares of the Fourier coefficients and Waldspurger's theorem on
the plus space (W. Kohnen and D. Zagier, *Values of L-series of modular forms at the center of the critical strip*,
Invent. Math. 64 (1981)), the latter two through Zagier's kernel function. New in 0.5.0.

The main results of the library for this topic, one theorem each, with every proof a deliberate `sorry`: to check
what is claimed, read this file. `Solution_KohnenPlusSpace.lean` proves the same statements from the library, and
`lake comparator` (configured by `comparator/KohnenPlusSpace.json`) checks that each proved statement is exactly the
one here and uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied, except that a named statement in the conclusion is unfolded. The
statements were not yet reviewed by a human (see the README).

**Unconditional theorems**: `plus_heckeT_selfAdjoint`, the self-adjointness of Shimura's `T(p²)`, `p` odd, on the
plus space for the Petersson product (a former named input); and, new in 0.5.1, `kohnen_plus_eigenbasis`, a basis of
`S⁺_{k+1/2}(4)` of eigenforms of all `T(p²)`, `p` odd (a former named input, `KohnenPlusEigenbasis`).

Two former named inputs of the conditional theorems are proved in the library and are no longer hypotheses: Kohnen's
`U(4)` identity on the plus space (`KohnenLUFour`, `kohnenLUFour_theta`) and the cycle integrals at square
discriminants (`KohnenSquareCycle`, `kohnenSquareCycle`).

**Conditional theorems.** Each has the form *(named inputs) → statement*: its hypotheses include named `Prop`
structures whose fields are classical theorems that the library does not prove, each with its source. The inputs are
hypotheses, not axioms, so `#print axioms` shows only the standard axioms. All locators below are unverified: the
papers were not checked.

## Named inputs (assumed, not proved here)

* `ModularFormsKB.HalfIntegral.KohnenTraceIdentity k` (Kohnen 1980, §§ 2–4): for `k ≥ 1`, the traces of every finite
  product of Hecke operators agree on `S⁺_{k+1/2}(4)` and on `S_{2k}(SL₂(ℤ))`, with `T(p²) ↔ T(p)` for odd primes `p`
  and, including `p = 2`, `T⁺(4) ↔ T(2)` for Kohnen's operator `T⁺(4)` given by its coefficient formula.
* `ModularFormsKB.HalfIntegral.KohnenKernelModular k` (Kohnen–Zagier 1981, § II): for `k ≥ 2`, a fundamental
  discriminant `D` with `(-1)^k D > 0` and `G ∈ S_{2k}(SL₂(ℤ))`, the `q`-series with the coefficients of Zagier's
  kernel (`kohnenKernelCoeff k D G`) is a form `g ∈ S⁺_{k+1/2}(4)`, and `g` is the value at `G` of the adjoint of the
  `D`-th Shimura lift for the Petersson products.
* `ModularFormsKB.HalfIntegral.ZagierKernelUnfolding k` (Kohnen–Zagier 1981, § II, Proposition): for `k ≥ 2`, the
  Petersson product of Zagier's function `f_{k,D,|D|m}` with `G ∈ S_{2k}(SL₂(ℤ))` is an explicit constant times the
  cycle integral `r_{k,D}(G; m)` (the sum over the binary quadratic forms of discriminant `D|D|m` of the integrals of
  `G` along their closed geodesics, weighted by the genus character of `D`).

New in 0.5.1, the three inputs of `kohnen_isomorphism_of_inputs`, each a consequence of `KohnenTraceIdentity` (the
library proves the three implications), and together equivalent to it:

* `ModularFormsKB.HalfIntegral.KohnenDLift thetaMultiplierSystem k D` (Kohnen 1980, Theorem 1), for every fundamental
  discriminant `D` with `(-1)^k D > 0` (`KohnenDisc k D`): for `k ≥ 1` and every `g ∈ S⁺_{k+1/2}(4)` with coefficients
  `a`, the `q`-series with the coefficients of the `D`-th lift (`kohnenLiftCoeff k D a`) is a cusp form of weight `2k`
  on `SL₂(ℤ)`;
* `ModularFormsKB.HalfIntegral.KohnenDimensionLe thetaMultiplierSystem k` (Kohnen 1980, §§ 2–3): for `k ≥ 1`,
  `dim S_{2k}(SL₂(ℤ)) ≤ dim S⁺_{k+1/2}(4)` (proved in the library for `k ≤ 5` and `k = 7`, where the left side is `0`);
* `ModularFormsKB.HalfIntegral.KohnenPlusMultOne thetaMultiplierSystem k` (Kohnen 1980, Theorem 1 and its corollary):
  for `k ≥ 1`, two eigenforms in `S⁺_{k+1/2}(4)` with the same eigenvalues of `T(p²)` at all odd primes `p`, the first
  nonzero, are proportional.

## Definitions used

Besides Mathlib (`CuspForm`, `LSeries`, `jacobiSym`) and the theta multiplier system of this library
(`ModularFormsKB.HalfIntegral.thetaMultiplierSystem`, the automorphy factor of `θ(τ) = Σ_{n ∈ ℤ} e^{2πi n² τ}`), the
statements use these definitions of the library:

* `M.plusCuspForms k 1 1` (for `M = thetaMultiplierSystem`): Kohnen's plus space `S⁺_{k+1/2}(4)`, the cusp forms of
  weight `k + 1/2` on `Γ₀(4)` whose coefficients `c(n)` vanish unless `(-1)^k n ≡ 0, 1 (mod 4)`;
* `ModularFormsKB.HalfIntegral.Abstract.HasQExp f a`: `f(τ) = Σ_{n ≥ 0} a(n) e^{2πinτ}` for every `τ`;
* `ModularFormsKB.HalfIntegral.heckeT k 1 1 p`: Shimura's `T(p²)` on coefficient sequences, weight `k + 1/2`, level 4,
  trivial character; `ModularFormsKB.HalfIntegral.heckeTInt w 1 1 p`: the Hecke operator `T(p)` of weight `w` and level
  one on coefficient sequences, `b ↦ (n ↦ b(pn) + p^{w-1} b(n/p))`;
* `ModularFormsKB.HalfIntegral.peterssonFour k f g = (1/6) ∫_{Γ₀(4)\ℍ} conj(f) g v^{k+1/2} dμ`,
  `peterssonNormSqFour k g = peterssonFour k g g`, and `peterssonNormSqOne k F = ∫_{SL₂(ℤ)\ℍ} |F|² v^{2k} dμ`
  (Kohnen and Zagier's normalizations);
* `ModularFormsKB.HalfIntegral.Corresponds M k g c F b`: `g ∈ S⁺_{k+1/2}(4)` is nonzero with coefficients `c`, `F` is
  a normalized Hecke eigenform of weight `2k` and level one with coefficients `b`, and `T(p²) c = b(p) c` for every odd
  prime `p`;
* `ModularFormsKB.HalfIntegral.IsFundamentalDiscriminant D`, `ModularFormsKB.HalfIntegral.kroneckerDisc D n` (the
  Kronecker symbol `(D/n)`), and `ModularFormsKB.HalfIntegral.IsEntireLSeries b σ L` (`L` is entire and equals the
  L-series of `b` on `Re s > σ`);
* (0.5.1) `ModularFormsKB.HalfIntegral.IsPlusEigenform M k g μ`: `g ∈ S⁺_{k+1/2}(4)` has coefficients `c` with
  `T(p²) c = μ(p) c` for every odd prime `p`; and, in the inputs, `ModularFormsKB.HalfIntegral.KohnenDisc k D`
  (`D` fundamental, `(-1)^k D > 0`) and `ModularFormsKB.HalfIntegral.kohnenLiftCoeff k D a` (the coefficients
  `∑_{d ∣ n} (D/d) d^{k-1} a(|D| n²/d²)` of the `D`-th lift).
-/

namespace ModularFormsKB.Headlines

section KohnenPlusSpace

open Complex MatrixGroups CongruenceSubgroup ModularForm
open scoped Real UpperHalfPlane
open ModularFormsKB.HalfIntegral

/-- **`T(p²)` is self-adjoint on Kohnen's plus space** (Shimura 1973, § 1; Kohnen 1980, § 1), unconditional: for an
odd prime `p` and `g₁, g₂ ∈ S⁺_{k+1/2}(4)` with coefficients `c₁, c₂`, if `g₁', g₂' ∈ S⁺_{k+1/2}(4)` have the
coefficients `T(p²)c₁`, `T(p²)c₂`, then `⟨g₁', g₂⟩ = ⟨g₁, g₂'⟩`. -/
theorem plus_heckeT_selfAdjoint (k : ℕ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (g₁ g₂ g₁' g₂' : ℍ → ℂ)
    (c₁ c₂ : ℕ → ℂ) (h₁ : g₁ ∈ thetaMultiplierSystem.plusCuspForms k 1 1)
    (h₂ : g₂ ∈ thetaMultiplierSystem.plusCuspForms k 1 1)
    (h₁' : g₁' ∈ thetaMultiplierSystem.plusCuspForms k 1 1)
    (h₂' : g₂' ∈ thetaMultiplierSystem.plusCuspForms k 1 1)
    (hc₁ : Abstract.HasQExp g₁ c₁) (hc₂ : Abstract.HasQExp g₂ c₂)
    (hc₁' : Abstract.HasQExp g₁' (heckeT k 1 1 p c₁)) (hc₂' : Abstract.HasQExp g₂' (heckeT k 1 1 p c₂)) :
    peterssonFour k g₁' g₂ = peterssonFour k g₁ g₂' := by
  sorry

/-- **Kohnen's isomorphism, conditional on Kohnen's trace identity** (Kohnen 1980, Theorem 1; named input
`KohnenTraceIdentity`): for `k ≥ 1` there is a `ℂ`-linear isomorphism
`Φ : S⁺_{k+1/2}(4) ≅ S_{2k}(SL₂(ℤ))` with `Φ ∘ T(p²) = T(p) ∘ Φ` on `q`-expansions for every odd prime `p`. -/
theorem kohnen_isomorphism (k : ℕ) (h : KohnenTraceIdentity k) :
    1 ≤ k → ∃ Φ : thetaMultiplierSystem.plusCuspForms k 1 1 ≃ₗ[ℂ] CuspForm 𝒮ℒ (2 * k : ℕ),
      ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ f f' : thetaMultiplierSystem.plusCuspForms k 1 1, ∀ a b : ℕ → ℂ,
        Abstract.HasQExp f a → Abstract.HasQExp f' (heckeT k 1 1 p a) → Abstract.HasQExp (Φ f) b →
          Abstract.HasQExp (Φ f') (heckeTInt (2 * k) 1 1 p b) := by
  sorry

/-- **The Kohnen–Zagier formula, conditional on named inputs** (Kohnen–Zagier 1981, Theorem 1, through Zagier's
kernel; named inputs `KohnenTraceIdentity`, `KohnenKernelModular`, `ZagierKernelUnfolding`): if `g ∈ S⁺_{k+1/2}(4)` (coefficients `c`) corresponds to the normalized eigenform
`F ∈ S_{2k}(SL₂(ℤ))` (coefficients `b`) and `D` is a fundamental discriminant with `(-1)^k D > 0`, then
`|c(|D|)|² / ⟨g, g⟩ = (k-1)!/π^k · |D|^{k-1/2} · L(F, D, k) / ⟨F, F⟩` for every entire continuation `L` of
`Σ (D/n) b(n) n^{-s}`. -/
theorem kohnen_zagier (k : ℕ) (h : KohnenTraceIdentity k)
    (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k) :
    1 ≤ k → ∀ (g : ℍ → ℂ) (c : ℕ → ℂ) (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ),
      Corresponds thetaMultiplierSystem k g c F b → ∀ D : ℤ, IsFundamentalDiscriminant D → 0 < (-1) ^ k * D →
        ∀ L : ℂ → ℂ, IsEntireLSeries (fun n ↦ (kroneckerDisc D n : ℂ) * b n) ((k : ℝ) + 1) L →
          ((‖c D.natAbs‖ ^ 2 : ℝ) : ℂ) / peterssonNormSqFour k g =
            ((k - 1).factorial / (π : ℂ) ^ k) * ((D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) *
              L k / peterssonNormSqOne k F := by
  sorry

/-- **Waldspurger's theorem on the plus space, conditional on named inputs** (Waldspurger 1981, in Kohnen and Zagier's
form, 1981; the named inputs of `kohnen_zagier`): if `g` and `F` correspond and `D₁, D₂` are fundamental
discriminants with `(-1)^k Dᵢ > 0`, then `c(|D₁|)² |D₂|^{k-1/2} L(F, D₂, k) = c(|D₂|)² |D₁|^{k-1/2} L(F, D₁, k)`. -/
theorem waldspurger_plus (k : ℕ) (h : KohnenTraceIdentity k)
    (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k) :
    1 ≤ k → ∀ (g : ℍ → ℂ) (c : ℕ → ℂ) (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ),
      Corresponds thetaMultiplierSystem k g c F b → ∀ D₁ D₂ : ℤ, IsFundamentalDiscriminant D₁ →
        IsFundamentalDiscriminant D₂ → 0 < (-1) ^ k * D₁ → 0 < (-1) ^ k * D₂ →
        ∀ L₁ L₂ : ℂ → ℂ, IsEntireLSeries (fun n ↦ (kroneckerDisc D₁ n : ℂ) * b n) ((k : ℝ) + 1) L₁ →
          IsEntireLSeries (fun n ↦ (kroneckerDisc D₂ n : ℂ) * b n) ((k : ℝ) + 1) L₂ →
          c D₁.natAbs ^ 2 * ((D₂.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) * L₂ k =
            c D₂.natAbs ^ 2 * ((D₁.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) * L₁ k := by
  sorry

/-- **The central twisted L-values are nonnegative, conditional on named inputs** (Kohnen–Zagier 1981, Corollary 1;
the named inputs of `kohnen_zagier`): for a normalized Hecke eigenform `F ∈ S_{2k}(SL₂(ℤ))`, `k ≥ 1`, with
coefficients `b` and a fundamental discriminant `D` with `(-1)^k D > 0`, every entire continuation `L` of
`L(F, D, s) = Σ (D/n) b(n) n^{-s}` has `L(k)` real and `≥ 0`. -/
theorem kohnen_zagier_twistedL_nonneg (k : ℕ) (hk : 1 ≤ k) (h : KohnenTraceIdentity k)
    (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k)
    (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ) (hb : Abstract.HasQExp F b) (h1 : b 1 = 1)
    (heig : ∀ p : ℕ, p.Prime → heckeTInt (2 * k) 1 1 p b = b p • b) {D : ℤ} (hD : IsFundamentalDiscriminant D)
    (hsign : 0 < (-1) ^ k * D) {L : ℂ → ℂ}
    (hL' : IsEntireLSeries (fun n ↦ (kroneckerDisc D n : ℂ) * b n) ((k : ℝ) + 1) L) :
    (L k).im = 0 ∧ 0 ≤ (L k).re := by
  sorry

/-- **`S⁺_{k+1/2}(4)` has a basis of Hecke eigenforms** (Kohnen 1980, § 1), unconditional, new in 0.5.1 (a former
named input): for `k ≥ 1` there are finitely many linearly independent `g₁, …, g_r ∈ S⁺_{k+1/2}(4)`, each an
eigenform of `T(p²)` for every odd prime `p` (with eigenvalues `μᵢ(p)`), spanning the plus space. The library proves
it from the self-adjointness of the `T(p²)` (`plus_heckeT_selfAdjoint`): commuting symmetric operators on a finite
dimensional inner product space are simultaneously diagonalizable. -/
theorem kohnen_plus_eigenbasis (k : ℕ) :
    1 ≤ k → ∃ (r : ℕ) (g : Fin r → ℍ → ℂ) (μ : Fin r → ℕ → ℂ),
      (∀ i, IsPlusEigenform thetaMultiplierSystem k (g i) (μ i)) ∧ LinearIndependent ℂ g ∧
        thetaMultiplierSystem.plusCuspForms k 1 1 ≤ Submodule.span ℂ (Set.range g) := by
  sorry

/-- **Kohnen's isomorphism, conditional on three of Kohnen's lemmas** (Kohnen 1980, Theorem 1; new in 0.5.1; named
inputs `KohnenDLift` for every admissible `D`, `KohnenDimensionLe`, `KohnenPlusMultOne`, which together are equivalent
to the `KohnenTraceIdentity` of `kohnen_isomorphism`): for `k ≥ 1` there is a `ℂ`-linear isomorphism
`Φ : S⁺_{k+1/2}(4) ≅ S_{2k}(SL₂(ℤ))` with `Φ ∘ T(p²) = T(p) ∘ Φ` on `q`-expansions for every odd prime `p`. -/
theorem kohnen_isomorphism_of_inputs (k : ℕ)
    (hL : ∀ D, KohnenDisc k D → KohnenDLift thetaMultiplierSystem k D)
    (hdim : KohnenDimensionLe thetaMultiplierSystem k) (h1 : KohnenPlusMultOne thetaMultiplierSystem k) :
    1 ≤ k → ∃ Φ : thetaMultiplierSystem.plusCuspForms k 1 1 ≃ₗ[ℂ] CuspForm 𝒮ℒ (2 * k : ℕ),
      ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ f f' : thetaMultiplierSystem.plusCuspForms k 1 1, ∀ a b : ℕ → ℂ,
        Abstract.HasQExp f a → Abstract.HasQExp f' (heckeT k 1 1 p a) → Abstract.HasQExp (Φ f) b →
          Abstract.HasQExp (Φ f') (heckeTInt (2 * k) 1 1 p b) := by
  sorry

end KohnenPlusSpace

end ModularFormsKB.Headlines
