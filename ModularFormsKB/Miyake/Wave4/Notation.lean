import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.CoefficientFormula
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Scalar
import ModularFormsKB.Citation
/-!
# Miyake §4.5: notation for the spaces `𝒢_k(N, χ)`, `𝒮_k(N, χ)` and the operators `T(n)`

Miyake, *Modular Forms* (Springer 1989), §4.3 (p. 115) and §4.5 (pp. 132–142).

This file introduces no new mathematics: it names, in Miyake's terms, objects that the pinned
dependency Tau Ceti (revision 4908b03) defines, so that the statements of wave 4 read as in the
book.

* Miyake's character `χ` is a Dirichlet character modulo `N` (`DirichletCharacter ℂ N`), extended
  by `0` at residues not prime to `N`. Tau Ceti indexes its spaces by the unit homomorphism
  `χ.toUnitHom : (ℤ/N)ˣ →* ℂˣ`.
* `cuspSpace k χ` is Miyake's `𝒮_k(N, χ)` (p. 115): the cusp forms `f` on `Γ₁(N)` with
  `f ∣_k γ = χ(d) f` for every `γ = [a b; c d] ∈ Γ₀(N)` (Tau Ceti's `cuspFormCharSpace`, see
  `TauCeti.mem_cuspFormCharSpace_iff_nebentypus`; `Gamma0Map N γ = d mod N`). `modSpace k χ` is
  `𝒢_k(N, χ)`. Miyake takes `k` a positive integer; here `k : ℤ`.
* `heckeT k χ n` is Miyake's Hecke operator `T(n)` on `𝒮_k(N, χ)` (p. 136, (4.5.26)), for
  `n ≥ 1`. Tau Ceti builds the Hecke-ring element `heckeTCompositeGamma0 N n` as the product over
  the primes `p ∣ n` of the terms of the recurrence `T(p^{e+2}) = T(p) T(p^{e+1}) − p T(p, p) T(p^e)`
  (with `T(p, p) = 0` when `p ∣ N`), starting from the double coset `T(p) = Γ₀(N) diag(1, p) Γ₀(N)`.
  Miyake *defines* `T(n)` as the sum of all double cosets of `Δ₀(N)` of determinant `n` and
  derives that recurrence (Lemma 4.5.7) and multiplicativity (Lemma 4.5.8). The two agree once
  Lemma 4.5.7 is known; see `MiyakeHecke.lean` (`miyakeHeckeT`) for Miyake's definition and the
  comparison.
* `heckeTT k χ l m` is the action of Miyake's `T(l, m) = Γ₀(N) diag(l, m) Γ₀(N)` (p. 133;
  Tau Ceti's `diagElemGamma0 N ![l, m]`, which is `0` when `gcd(l, N) ≠ 1` or `l m = 0`).

The normalisation agrees with Miyake's: Tau Ceti's operator is `f ↦ n^{k/2-1} Σ f ∣_k α_v`
in Miyake's slash convention, so `T(n, n)` acts on `𝒮_k(N, χ)` by `χ(n) n^{k-2}`
(`heckeTT_self`, Miyake (4.5.25)), and the coefficient formula of Lemma 4.5.14 holds verbatim.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave4

variable {N : ℕ} [NeZero N]

/-- Miyake's `𝒮_k(N, χ)` (p. 115) for a Dirichlet character `χ` modulo `N`: Tau Ceti's
`cuspFormCharSpace k χ.toUnitHom`, a subspace of the cusp forms on `Γ₁(N)`. -/
abbrev cuspSpace (k : ℤ) (χ : DirichletCharacter ℂ N) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  TauCeti.cuspFormCharSpace k χ.toUnitHom

/-- Miyake's `𝒢_k(N, χ)` (p. 115): Tau Ceti's `modFormCharSpace k χ.toUnitHom`. -/
abbrev modSpace (k : ℤ) (χ : DirichletCharacter ℂ N) :
    Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  TauCeti.modFormCharSpace k χ.toUnitHom

/-- Miyake's Hecke operator `T(n)` on `𝒮_k(N, χ)` (p. 136), through Tau Ceti's composite element
`heckeTCompositeGamma0 N n` of the Hecke ring `ℛ(Γ₀(N), Δ₀(N))`. -/
abbrev heckeT (k : ℤ) (χ : DirichletCharacter ℂ N) (n : ℕ) : Module.End ℂ (cuspSpace k χ) :=
  HeckeRing.GL2.heckeRingHomCuspCharSpace k χ.toUnitHom (HeckeRing.GL2.heckeTCompositeGamma0 N n)

/-- Miyake's `T(n)` on `𝒢_k(N, χ)`. -/
abbrev heckeTMod (k : ℤ) (χ : DirichletCharacter ℂ N) (n : ℕ) : Module.End ℂ (modSpace k χ) :=
  HeckeRing.GL2.heckeRingHomCharSpace k χ.toUnitHom (HeckeRing.GL2.heckeTCompositeGamma0 N n)

/-- The action on `𝒮_k(N, χ)` of Miyake's `T(l, m) = Γ₀(N) diag(l, m) Γ₀(N)` (p. 133). -/
abbrev heckeTT (k : ℤ) (χ : DirichletCharacter ℂ N) (l m : ℕ) : Module.End ℂ (cuspSpace k χ) :=
  HeckeRing.GL2.heckeRingHomCuspCharSpace k χ.toUnitHom (HeckeRing.GL2.diagElemGamma0 N ![l, m])

/-- The `n`-th Fourier coefficient at `∞` of an element of `𝒮_k(N, χ)` (width `1`). -/
abbrev coeff {k : ℤ} {χ : DirichletCharacter ℂ N} (f : cuspSpace k χ) (n : ℕ) : ℂ :=
  (qExpansion 1 (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n

/-- The `n`-th Fourier coefficient at `∞` of an element of `𝒢_k(N, χ)`. -/
abbrev coeffMod {k : ℤ} {χ : DirichletCharacter ℂ N} (f : modSpace k χ) (n : ℕ) : ℂ :=
  (qExpansion 1 (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n

/-- Tau Ceti writes the character in its formulas as `MulChar.ofUnitHom χ.toUnitHom`; this is
`χ` itself. -/
theorem ofUnitHom_toUnitHom (χ : DirichletCharacter ℂ N) :
    (MulChar.ofUnitHom χ.toUnitHom : DirichletCharacter ℂ N) = χ := by
  rw [MulChar.ofUnitHom_eq, MulChar.toUnitHom_eq, Equiv.symm_apply_apply]

/-- **Miyake (4.5.25)**: `T(n, n)` acts on `𝒮_k(N, χ)` as the scalar `χ(n) n^{k-2}`, for `n ≥ 1`
(for `gcd(n, N) ≠ 1` both sides are `0`). -/
@[kb "miyake1989" "(4.5.25), p. 136"]
theorem heckeTT_self (k : ℤ) (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : 0 < n) :
    heckeTT k χ n n = (χ n * (n : ℂ) ^ (k - 2)) • 1 := by
  rw [heckeTT, ← HeckeRing.GL2.heckeTScalarGamma0_def]
  by_cases hnN : n.Coprime N
  · rw [HeckeRing.GL2.heckeRingHomCuspCharSpace_heckeTScalarGamma0 k χ.toUnitHom n hn hnN,
      MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime]
  · have hunit : ¬ IsUnit (n : ZMod N) := fun h ↦ hnN ((ZMod.isUnit_iff_coprime n N).mp h)
    rw [HeckeRing.GL2.heckeTScalarGamma0_of_not_coprime N hnN, map_zero,
      MulChar.map_nonunit _ hunit, zero_mul, zero_smul]

end ModularFormsKB.Miyake.Wave4
