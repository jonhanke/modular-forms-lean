/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import ModularFormsKB.ThetaGenus.Gram
import ModularFormsKB.ThetaGenus.Gross

/-!
# Headline statements of modular-forms-lean 0.5.1: theta series of quadratic forms in one genus

A topic, not a book: theta series of positive definite integral quadratic forms in one genus differ by a cusp form
(the classical consequence of Siegel's main theorem, C. L. Siegel, *Über die analytische Theorie der quadratischen
Formen*, Ann. of Math. 36 (1935); here proved directly, by comparing the constant terms at every cusp, which are
local Gauss sums and so depend only on the genus), in every rank: integral weight `n/2` on `Γ₁(N)` for even rank `n`,
and half-integral weight in Shimura's space `S_{k+1/2}(4N, χ)` for odd rank `n = 2k + 1`. As an instance, Gross's form
of weight 3/2 for the prime 11 (B. H. Gross, *Heights and the special values of L-series*, 1987) lies in Kohnen's
plus space of level 44. New in 0.5.0.

The main results of the library for this topic, one theorem each, with every proof a deliberate `sorry`: to check
what is claimed, read this file. `Solution_ThetaGenus.lean` proves the same statements from the library, and
`lake comparator` (configured by `comparator/ThetaGenus.json`) checks that each proved statement is exactly the one
here and uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).
All theorems are unconditional.

The forms are given by their Hessians `H` (Gram matrices of the bilinear form `xᵀHy`, so `Q(x) = xᵀHx/2`), as
integer matrices acting on column vectors. Indices are 0-based (`Fin n`).

## Definitions used

Besides Mathlib (`CuspForm`, `CongruenceSubgroup.Gamma1`, `Matrix.PosDef`, `jacobiSym`, `DirichletCharacter`), the
statements use these definitions of the library:

* `ModularFormsKB.ThetaGenus.IsEvenGram H`: `H` is symmetric, has even diagonal and is positive definite;
* `ModularFormsKB.ThetaGenus.thetaGram H τ = ∑_{x ∈ ℤⁿ} exp(π i xᵀHx τ)`;
* `ModularFormsKB.ThetaGenus.IsGramLevel H N`: `H H' = N · 1` for an integer matrix `H'` with even diagonal (that is,
  `N H⁻¹` is an even integral matrix);
* `ModularFormsKB.ThetaGenus.GramSameGenus H H'`: `det H = det H'` and, for every `c ≥ 1`, an integer matrix `U`
  invertible modulo `c` with `(Ux)ᵀH'(Ux) ≡ xᵀHx (mod 2c)` for all `x` (the forms are isometric modulo every `c`);
* `ModularFormsKB.HalfIntegral.halfIntCuspForms k N χ`: Shimura's cusp forms of weight `k + 1/2` on `Γ₀(4N)` with
  character `χ`, for the theta multiplier (holomorphic, with the transformation law of `θ^{2k+1}` twisted by `χ` on
  `Γ₀(4N)`, and vanishing at every cusp);
* `ModularFormsKB.HalfIntegral.thetaMultiplierSystem.plusCuspForms k N χ`: the cusp forms of weight `k + 1/2` on
  `Γ₀(4N)` for the theta multiplier whose `q`-expansion coefficients `c(n)` vanish unless `(-1)^k n ≡ 0, 1 (mod 4)`
  (Kohnen's plus space);
* `ModularFormsKB.ThetaGenus.Gross.grossH₁`, `grossH₂`: the Hessians `[[8, 0, 4], [0, 22, 0], [4, 0, 24]]` and
  `[[6, 0, 4], [0, 88, 44], [4, 44, 32]]` of Gross's two ternary forms of discriminant 11.
-/

namespace ModularFormsKB.Headlines

section ThetaGenus

open Complex Module Filter Topology
open scoped Real RealInnerProductSpace ModularForm UpperHalfPlane MatrixGroups Matrix
open ModularFormsKB.ThetaGenus

/-- **Theta series in one genus differ by a cusp form, even rank** (Siegel 1935; Gram-matrix form). Let `H`, `H'` be
Hessians of positive definite even integral forms of rank `n = 2k` in one genus, and `N` an admissible level for
both. Then `θ_H - θ_{H'}` is a cusp form of weight `k` on `Γ₁(N)`. -/
theorem thetaGenus_sub_cuspForm_even {n : ℕ} {H H' : Matrix (Fin n) (Fin n) ℤ} (hH : IsEvenGram H)
    (hH' : IsEvenGram H') {k : ℕ} (hn : n = 2 * k) (h : GramSameGenus H H') {N : ℕ}
    (hN : IsGramLevel H N) (hN' : IsGramLevel H' N) :
    ∃ f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k,
      ⇑f = thetaGram H - thetaGram H' := by
  sorry

/-- **Theta series in one genus differ by a cusp form, odd rank** (Siegel 1935; Gram-matrix form). Let `H`, `H'` be
Hessians of positive definite even integral forms of rank `n = 2k + 1` in one genus, with `4N` an admissible level
for both. Then `θ_H - θ_{H'}` lies in Shimura's `S_{k+1/2}(4N, χ)` for the character `χ(d) = (2 det H / d)`. -/
theorem thetaGenus_sub_cuspForm_odd {n : ℕ} {H H' : Matrix (Fin n) (Fin n) ℤ} (hH : IsEvenGram H)
    (hH' : IsEvenGram H') {k : ℕ} (hn : n = 2 * k + 1) (h : GramSameGenus H H')
    {N : ℕ} [NeZero N] (hN : IsGramLevel H (4 * N)) (hN' : IsGramLevel H' (4 * N)) :
    ∃ χ : DirichletCharacter ℂ (4 * N),
      (∀ d : ℕ, d.Coprime (4 * N) → χ d = (jacobiSym (2 * H.det) d : ℂ)) ∧
      (fun τ ↦ thetaGram H τ - thetaGram H' τ) ∈ HalfIntegral.halfIntCuspForms k N χ := by
  sorry

/-- **Gross's form is a cusp form in Kohnen's plus space of level 44** (Gross 1987, for the prime 11): for Gross's two
ternary forms of discriminant 11, which lie in one genus, `(θ₁ - θ₂)/2` is a cusp form of weight 3/2 on `Γ₀(44)`
for the theta multiplier and the trivial character, and lies in the plus space. -/
theorem gross_form_mem_plusCuspForms :
    (fun τ ↦ (thetaGram Gross.grossH₁ τ - thetaGram Gross.grossH₂ τ) / 2) ∈
      HalfIntegral.thetaMultiplierSystem.plusCuspForms 1 11 1 := by
  sorry

end ThetaGenus

end ModularFormsKB.Headlines
