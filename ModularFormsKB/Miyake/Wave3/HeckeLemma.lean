import TauCeti.NumberTheory.ModularForms.DiamondOperators
import ModularFormsKB.Citation
/-!
# Miyake, Lemma 4.6.3 (Hecke's lemma): statement

Miyake, *Modular Forms* (Springer 1989), §4.6, p. 155, Lemma 4.6.3.

Miyake's `𝒢_k(N, χ)` is Tau Ceti's `modFormCharSpace k χ`, the forms in
`M_k(Γ₁(N))` on which every diamond operator `⟨d⟩` acts by `χ(d)` (`χ` a character of
`(ℤ/N)ˣ`). Miyake's `Δ₀(N)` is the monoid of integer matrices `[a b; c d]` with `det > 0`,
`N ∣ c` and `gcd(a, N) = 1`. An integer matrix `α` acts through any `g ∈ GL₂(ℝ)` with the same
entries; Mathlib's slash operator `f ∣[k] g = det(g)^{k-1} (cz + d)^{-k} f(gz)` differs from
Miyake's `det(α)^{k/2} (cz+d)^{-k} f(αz)` by a nonzero constant, which does not affect the
hypothesis `f ∣[k] α ∈ 𝒢_k(N, χ)`.

**Status: stated, not proved.** The lemma is the named proposition `HeckeLemmaStatement N k χ`.
Tau Ceti has no counterpart (its newform theory goes around Hecke's lemma, see
`TauCeti.exists_cuspForm_mem_cuspFormCharSpace_or_eq_zero`). Miyake's proof uses Lemma 4.5.2
(elementary divisors in `Γ₀(N)`; the primitive case is Tau Ceti's
`HeckeRing.GL2.mem_doubleCoset_natDiagGL_of_primitive`, Shimura 3.33), the existence of
`γ ∈ Γ₀(N)` with `αγα⁻¹ ∉ Γ₀(N)`, and a comparison of `q`-expansion coefficients
`a(n) = C^{-t} a(n/h^t)`. Missing piece: the passage from `f ∣ α ∈ 𝒢_k(N, χ)` to the relation
`C f(z) = f(z/h)` with `h > 1` (the matrix computation of the proof, in Mathlib's slash
conventions). Miyake's `k` is positive (the proof ends "since `k > 0`, `f = 0`"); for `k = 0`
constants are counterexamples.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace ModularFormsKB.Miyake

/-- **Miyake, Lemma 4.6.3 (Hecke)**, statement (not proved here). Let `k > 0`,
`f ∈ 𝒢_k(N, χ)`, and `α = [a b; c d]` an integer matrix in `Δ₀(N)` with `det α > 1` prime to
`N` and `gcd(a, b, c, d) = 1`. If `f ∣[k] α ∈ 𝒢_k(N, χ)`, then `f = 0`. -/
@[kb "miyake1989" "Lemma 4.6.3, p. 155 (statement)"]
def HeckeLemmaStatement (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) : Prop :=
  0 < k → ∀ f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k, f ∈ TauCeti.modFormCharSpace k χ →
    ∀ α : Matrix (Fin 2) (Fin 2) ℤ, (N : ℤ) ∣ α 1 0 → IsCoprime (α 0 0) N → 1 < α.det →
      IsCoprime α.det N → (∀ m : ℤ, (∀ i j, m ∣ α i j) → IsUnit m) →
      ∀ g : GL (Fin 2) ℝ, (g : Matrix (Fin 2) (Fin 2) ℝ) = α.map (Int.cast) →
      (∃ F ∈ TauCeti.modFormCharSpace k χ, ⇑F = ⇑f ∣[k] g) → f = 0

end ModularFormsKB.Miyake
