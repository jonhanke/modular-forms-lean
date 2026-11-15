/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import ModularFormsKB.Miyake.Sec4_3.Hecke
import ModularFormsKB.Miyake.Sec4_3.WeilTheorem
import ModularFormsKB.Miyake.Wave6.HeckeIndependence
import ModularFormsKB.Miyake.Wave8.GeneralAdjoint
import ModularFormsKB.Miyake.Sec4_9.Spherical.Forms
import ModularFormsKB.Miyake.Sec4_9.Spherical.Odd
import ModularFormsKB.Miyake.Sec4_9.Spherical.UnaryLaw
import ModularFormsKB.Miyake.HeckeTrick.FourierTerms
import ModularFormsKB.Miyake.HeckeTrick.HeckeLimit
import ModularFormsKB.Miyake.Sec4_6.HeckeLemma

/-!
# Headline statements of modular-forms-lean 0.4.0: Miyake, *Modular Forms*, proved

The statements of `Challenge_Miyake.lean`, each proved by appeal to the library theorem. `lake comparator`
(configured by `comparator/Miyake.json`) checks that each statement here is exactly the one in
`Challenge_Miyake.lean` and that its proof uses only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.

Each statement is the library's statement, copied, except that a named statement in the conclusion (a `Prop`
structure of the library) is unfolded into its field. The statements were not yet reviewed by a human (see the
README).

## Definitions used

Besides Mathlib and Tau Ceti, the statements use these definitions of the library; a reader checking a statement
should check these too:

* `Miyake.CoeffGrowth`, `Miyake.qSeries`, `Miyake.completedL`, `Miyake.BoundedOnVerticalStrips`,
  `Miyake.HeckeCondition`, `Miyake.fricke`, `Miyake.twist`, `Miyake.twistedCompletedL`,
  `Miyake.TwistedHeckeCondition`, `Miyake.gaussW`, `Miyake.weilConstant`, `Miyake.IsModularFormChar`,
  `Miyake.IsCuspFormChar`, `Miyake.IsOddPrimeOrFour`, `Miyake.IsWeilSet` (converse theorems)
* (0.3.1) `ModularFormsKB.Miyake.HeckeGenerators`, `ModularFormsKB.Miyake.heckeGenerator` (the generators `T(p)`,
  `T(p, p)` for `p ∤ N` and `T(q)` for `q ∣ N` of the Hecke ring of `Γ₀(N)`, Tau Ceti's double cosets); the
  space `ModularFormsKB.Miyake.Wave4.cuspSpace` (Tau Ceti's `𝒮_k(N, χ)`), `ModularFormsKB.Miyake.Wave4.heckeT`
  (Tau Ceti's `T(n)`), `ModularFormsKB.Miyake.Wave7.heckeTStar` and `ModularFormsKB.Miyake.Wave7.heckeTStarN`
  (Miyake's `T*(m, l)`, the double coset `Γ₀(N) diag(m, l) Γ₀(N)` acting with the weight `conj χ(d)`, and
  `T*(n) = Σ T*(m, l)` over `l m = n`, `l ∣ m`, (4.5.16)), `ModularFormsKB.Miyake.Wave7.pet` (Tau Ceti's Petersson
  product on `Γ₁(N)`) (Theorem 4.5.4)
* (0.4.0) `ModularFormsKB.Miyake.Sec4_9.thetaSph` (the theta series `∑_{v ∈ L} P(v) e^{πi‖v‖²τ}` of a lattice with
  the spherical weight `P(x) = (⟪u, x⟫ + i⟪w, x⟫)^ν`), `ModularFormsKB.Miyake.Sec4_9.IsSphericalDatum` (`ν ≤ 1` or
  `u + iw` isotropic, so that `P` is harmonic), `ModularFormsKB.Miyake.Sec4_9.oddThetaChar` (the character of the
  odd-rank theta series), with Tau Ceti's `ZLattice.IsEven`, `ZLattice.level` and `ZLattice.IsEven.thetaCharacter`
  and the half-integral weight spaces `ModularFormsKB.HalfIntegral.halfIntModularForms`,
  `ModularFormsKB.HalfIntegral.halfIntCuspForms` (Shimura's `M_{k+1/2}(4N, χ)`, `S_{k+1/2}(4N, χ)`) (Corollary 4.9.4);
  `ModularFormsKB.HalfIntegral.thetaTwist` (`∑_{n ∈ ℤ} ψ(n) n^ν e^{2πitn²z}`), `ModularFormsKB.HalfIntegral.charParity`,
  `ModularFormsKB.HalfIntegral.thetaMult` (the theta multiplier `j(γ, z)`) (Corollary 4.9.7);
  `ModularFormsKB.Miyake.HeckeTrick.eisensteinCharS` (`E_k(z, s; χ, ψ)` as a series), its continuation
  `ModularFormsKB.Miyake.HeckeTrick.eisensteinCharSCont` (the Fourier expansion of Theorem 7.2.9),
  `ModularFormsKB.Miyake.Wave2B.IsHeckeLimit` (Hecke's limit `lim_{s → 0} E_k(z, s; χ, ψ)`),
  `ModularFormsKB.Miyake.Wave2B.eisensteinCharA`, `.eisensteinCharCoeff`, `.eisensteinCharConst` (the constants and
  coefficients of (7.2.12)) (Theorems 7.2.9, 7.2.12, 7.2.13)
-/

namespace ModularFormsKB.Headlines

section Converse

open Complex Filter Asymptotics CongruenceSubgroup _root_.Miyake
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm

/-- **Hecke's theorem with the Fricke involution** (Miyake, Theorem 4.3.6). For positive integers `k`, `N` and
coefficients `a_n`, `b_n` of polynomial growth, with `f = ∑ a_n e^{2πinz}` and `g = ∑ b_n e^{2πinz}`:
`g = f|_k ω_N` on `ℍ` if and only if `Λ_N(s; f)` and `Λ_N(s; g)` continue to the whole plane with
`Λ_N(s; f) = i^k Λ_N(k - s; g)` and `Λ_N(s; f) + a_0/s + i^k b_0/(k - s)` entire and bounded on vertical strips. -/
theorem hecke_converse {k N : ℕ} (hk : 0 < k) (hN : 0 < N) {a b : ℕ → ℂ}
    (ha : CoeffGrowth a) (hb : CoeffGrowth b) :
    (∀ z : ℂ, 0 < z.im → qSeries b z = fricke k N (qSeries a) z) ↔
      HeckeCondition k N (I ^ k) a b := by
  exact _root_.Miyake.hecke_fricke hk hN ha hb

/-- **Hecke's converse theorem at level one** (Miyake, Theorem 4.3.8). For even `k ≥ 2` and coefficients `a_n` of
polynomial growth, `∑ a_n e^{2πinz}` is a modular form of weight `k` for `SL₂(ℤ)` if and only if
`Λ(s) = (2π)^{-s} Γ(s) L(s)` continues to the whole plane with `Λ(s) = (-1)^{k/2} Λ(k - s)` and
`Λ(s) + a_0/s + (-1)^{k/2} a_0/(k - s)` entire and bounded on vertical strips. -/
theorem hecke_converse_levelOne {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) {a : ℕ → ℂ} (ha : CoeffGrowth a) :
    (∃ F : ModularForm 𝒮ℒ k, ∀ τ : ℍ, F τ = qSeries a τ) ↔
      HeckeCondition k 1 ((-1) ^ (k / 2)) a a := by
  exact _root_.Miyake.levelOne_converse hk hk2 ha

/-- **Weil's converse theorem** (Miyake, Theorem 4.3.15). Let `k`, `N` be positive integers, `χ` a Dirichlet
character modulo `N` with `χ(-1) = (-1)^k`, `a_n`, `b_n` of polynomial growth, `f = ∑ a_n e^{2πinz}`,
`g = ∑ b_n e^{2πinz}`, and `𝓜` a set of odd primes and `4`, prime to `N`, meeting every arithmetic progression of
coprime positive integers. If `Λ_N(s; f)`, `Λ_N(s; g)` satisfy Hecke's condition with root number `i^k`, and for
every primitive character `ψ` of conductor in `𝓜` the twisted functions satisfy the twisted condition with Weil's
constant `χ(m_ψ) ψ(-N) W(ψ)/W(ψ̄)`, then `f ∈ M_k(N, χ)`, `g ∈ M_k(N, χ̄)` and `g = f|_k ω_N`. -/
theorem weil_converse {k N : ℕ} (hk : 0 < k) (hN : 0 < N) (χ : DirichletCharacter ℂ N)
    (hχ : χ (-1) = (-1) ^ k) {a b : ℕ → ℂ} (ha : CoeffGrowth a) (hb : CoeffGrowth b)
    {M : Set ℕ} (hM : IsWeilSet N M) (h1 : HeckeCondition k N (I ^ k) a b)
    (h2 : ∀ (m : ℕ) [NeZero m], m ∈ M → ∀ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive →
      TwistedHeckeCondition k N ψ (weilConstant χ ψ) a b) :
    IsModularFormChar k N χ (fun τ : ℍ ↦ qSeries a τ) ∧
      IsModularFormChar k N χ⁻¹ (fun τ : ℍ ↦ qSeries b τ) ∧
      ∀ z : ℂ, 0 < z.im → qSeries b z = fricke k N (qSeries a) z := by
  exact _root_.Miyake.weil hk hN χ hχ ha hb hM h1 h2

/-- **Weil's converse theorem for cusp forms** (Miyake, Theorem 4.3.15, last sentence): under the hypotheses of
`weil_converse`, if moreover `L(s; f)` converges absolutely at `s = k - δ` for some `δ > 0`, then `f` and `g` are
cusp forms. -/
theorem weil_converse_cusp {k N : ℕ} (hk : 0 < k) (hN : 0 < N) (χ : DirichletCharacter ℂ N)
    (hχ : χ (-1) = (-1) ^ k) {a b : ℕ → ℂ} (ha : CoeffGrowth a) (hb : CoeffGrowth b)
    {M : Set ℕ} (hM : IsWeilSet N M) (h1 : HeckeCondition k N (I ^ k) a b)
    (h2 : ∀ (m : ℕ) [NeZero m], m ∈ M → ∀ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive →
      TwistedHeckeCondition k N ψ (weilConstant χ ψ) a b)
    {δ : ℝ} (hδ : 0 < δ) (hL : LSeriesSummable a (k - δ)) :
    IsCuspFormChar k N χ (fun τ : ℍ ↦ qSeries a τ) ∧
      IsCuspFormChar k N χ⁻¹ (fun τ : ℍ ↦ qSeries b τ) := by
  exact _root_.Miyake.weil_cusp hk hN χ hχ ha hb hM h1 h2 hδ hL

end Converse

section HeckeAlgebra

open CongruenceSubgroup Matrix.SpecialLinearGroup ModularFormsKB.Miyake
open scoped MatrixGroups HeckeCosetModule

/-- **The Hecke ring of `Γ₀(N)` is a polynomial ring** (Miyake, Theorem 4.5.9). For `N ≥ 1`, the Hecke ring
`ℛ(N) = ℛ(Γ₀(N), Δ₀(N))` over `ℤ` is the polynomial ring over `ℤ` in `T(p)`, `T(p, p)` (`p` prime, `p ∤ N`) and
`T(q)` (`q` prime, `q ∣ N`): there is a ring isomorphism from the polynomial ring on these symbols onto `ℛ(N)`
sending each variable to its generator. Tau Ceti has the local polynomial-ring theorem at level one (Shimura,
Theorem 3.20), not this one at level `N`. -/
theorem heckeRing_gamma0_polynomial (N : ℕ) [NeZero N] :
    ∃ e : MvPolynomial (HeckeGenerators N) ℤ ≃+*
        𝕋 (HeckeRing.GL2.Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ,
      ∀ i, e (MvPolynomial.X i) = heckeGenerator N i := by
  exact (ModularFormsKB.Miyake.Wave6.heckeAlgebraPolynomial N).exists_equiv

end HeckeAlgebra

section Adjoint

open ModularFormsKB.Miyake.Wave4 ModularFormsKB.Miyake.Wave7

/-- **`T(n)` and `T*(n)` are adjoint for every `n`** (Miyake, Theorem 4.5.4 (2)). For a Dirichlet character `χ`
modulo `N`, an integer weight `k` and every `n ≥ 1` (with no condition on `(n, N)`), the operators `T(n)` and `T*(n)`
on `𝒮_k(N, χ)` are mutually adjoint for the Petersson product: `⟨f | T(n), g⟩ = ⟨f, g | T*(n)⟩` and
`⟨f | T*(n), g⟩ = ⟨f, g | T(n)⟩`. Tau Ceti has the case `(n, N) = 1`. -/
theorem hecke_adjoint_heckeTStar {N : ℕ} [NeZero N] (k : ℤ) (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : 0 < n)
    (f g : cuspSpace k χ) :
    pet (heckeT k χ n f) g = pet f (heckeTStarN k χ n g) ∧
      pet (heckeTStarN k χ n f) g = pet f (heckeT k χ n g) := by
  exact ⟨ModularFormsKB.Miyake.Wave8.pet_heckeT_left_all k χ hn f g, ModularFormsKB.Miyake.Wave8.pet_heckeTStarN_left_all k χ hn f g⟩

end Adjoint

section SphericalTheta

open Module ModularFormsKB.Miyake.Sec4_9 Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- **Theta series with a spherical function, even rank** (Miyake, Theorem 4.9.3 and Corollary 4.9.4, in lattice
form). Let `L` be an even lattice of rank `2k` in a Euclidean space, of level `N`, and `P(x) = (⟪u, x⟫ + i⟪w, x⟫)^ν`
a spherical function of degree `ν` (`ν ≤ 1`, or `u + iw` isotropic). Then `θ_L(τ; P) = ∑_{v ∈ L} P(v) e^{πi‖v‖²τ}`
is a modular form of weight `k + ν` on `Γ₁(N)` lying in the character space of the theta character `χ_L`
(so in `M_{k+ν}(Γ₀(N), χ_L)`), and a cusp form when `ν ≥ 1`. Tau Ceti main has the case `P = 1`. -/
theorem thetaSpherical_even {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {k : ℕ} (hL : ZLattice.IsEven L)
    (hk : finrank ℝ E = 2 * k) {ν : ℕ} {u w : E} (hsph : IsSphericalDatum ν u w) :
    (∃ f : ModularForm ((CongruenceSubgroup.Gamma1 (ZLattice.level L)).map (mapGL ℝ)) (k + ν : ℕ),
        f ∈ TauCeti.modFormCharSpace (k + ν : ℕ) (MulChar.equivToUnitHom (hL.thetaCharacter ⟨k, by omega⟩)) ∧
          ⇑f = thetaSph L ν u w 0) ∧
      (1 ≤ ν → ∃ f : CuspForm ((CongruenceSubgroup.Gamma1 (ZLattice.level L)).map (mapGL ℝ)) (k + ν : ℕ),
        ⇑f = thetaSph L ν u w 0) := by
  exact ⟨⟨ModularFormsKB.Miyake.Sec4_9.thetaSphForm hL hk hsph, ModularFormsKB.Miyake.Sec4_9.thetaSphForm_mem_modFormCharSpace hL hk hsph, rfl⟩, fun hν ↦ ⟨ModularFormsKB.Miyake.Sec4_9.thetaSphCuspForm hL hk hν hsph, rfl⟩⟩

/-- **Theta series with a spherical function, odd rank** (Miyake, Theorem 4.9.3 and Corollary 4.9.4 for odd `r`, in
lattice form). Let `L` be an even lattice of rank `2k + 1`, of level `N`, and `P` a spherical function of degree
`ν` as above. Then `θ_L(τ; P)` lies in Shimura's space `M_{k+ν+1/2}(4N, χ)` of half-integral weight (theta
multiplier), `χ = oddThetaChar`, and in the cusp forms `S_{k+ν+1/2}(4N, χ)` when `ν ≥ 1`. -/
theorem thetaSpherical_odd {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {k : ℕ} (hL : ZLattice.IsEven L)
    (hk : finrank ℝ E = 2 * k + 1) {ν : ℕ} {u w : E} (hsph : IsSphericalDatum ν u w) :
    (fun τ : UpperHalfPlane ↦ thetaSph L ν u w 0 τ) ∈
        ModularFormsKB.HalfIntegral.halfIntModularForms (k + ν) (ZLattice.level L) (oddThetaChar hL hk ν) ∧
      (1 ≤ ν → (fun τ : UpperHalfPlane ↦ thetaSph L ν u w 0 τ) ∈
        ModularFormsKB.HalfIntegral.halfIntCuspForms (k + ν) (ZLattice.level L) (oddThetaChar hL hk ν)) := by
  exact ⟨ModularFormsKB.Miyake.Sec4_9.thetaSph_mem_halfIntModularForms hL hk hsph, fun hν ↦ ModularFormsKB.Miyake.Sec4_9.thetaSph_mem_halfIntCuspForms hL hk hν hsph⟩

end SphericalTheta

section TwistedTheta

open ModularFormsKB.HalfIntegral
open scoped MatrixGroups

/-- **Shimura's transformation law of the twisted theta series, for every character** (Miyake, Corollary 4.9.7 (1);
Shimura 1973, Proposition 2.2). For a Dirichlet character `ψ` modulo `r ≥ 1` (primitive or not) of parity `ν`
(`ψ(-1) = (-1)^ν`), `t ≥ 1`, and `γ = [a b; c d] ∈ Γ₀(4tr²)`, the series `θ_{ψ,t}(z) = ∑_{n ∈ ℤ} ψ(n) n^ν e^{2πitn²z}`
satisfies `θ_{ψ,t}(γz) = ψ̄(d) (t/|d|) (cz + d)^ν j(γ, z) θ_{ψ,t}(z)`, with `(t/|d|)` the Jacobi symbol and `j` the
theta multiplier. -/
theorem thetaTwist_transformation {r : ℕ} (ψ : DirichletCharacter ℂ r) (hr : 1 ≤ r) {t : ℕ} (ht : 1 ≤ t)
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 (4 * t * r ^ 2)) (τ : UpperHalfPlane) :
    thetaTwist ψ t ((γ • τ : UpperHalfPlane) : ℂ) = ψ⁻¹ (γ 1 1 : ZMod r) * (jacobiSym t (γ 1 1).natAbs : ℂ) *
      ((γ 1 0 : ℂ) * τ + γ 1 1) ^ charParity ψ * thetaMult γ τ * thetaTwist ψ t τ := by
  exact ModularFormsKB.HalfIntegral.thetaTwist_law ψ hr ht hγ τ

end TwistedTheta

section HeckeTrick

open Set Complex ModularFormsKB.Miyake.HeckeTrick ModularFormsKB.Miyake.Wave2B
open scoped Real UpperHalfPlane

/-- **Hecke's continuation of the Eisenstein series in `s`** (Miyake, Theorem 7.2.9). For Dirichlet characters `χ`
modulo `L` and `ψ` modulo `M` and an integer `k` with `χ(-1)ψ(-1) = (-1)^k`, and every `z ∈ ℍ`, the function
`s ↦ E_k(z, s; χ, ψ)`, defined by its series for `k + 2 Re s > 2`, continues to a meromorphic function on the whole
`s`-plane, given by its Fourier expansion `eisensteinCharSCont`. -/
theorem heckeEisenstein_continuation {L M : ℕ} (k : ℤ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (hpar : χ (-1) * ψ (-1) = (-1) ^ k) (z : ℍ) :
    MeromorphicOn (eisensteinCharSCont k χ ψ z) univ ∧
      ∀ s : ℂ, 2 < (k : ℝ) + 2 * s.re → eisensteinCharS k s χ ψ z = eisensteinCharSCont k χ ψ z s := by
  exact ModularFormsKB.Miyake.HeckeTrick.miyake_7_2_9 k χ ψ hpar z

/-- **Hecke's limit in weight two** (Miyake, Theorem 7.2.12). If `χ(-1)ψ(-1) = 1`, then for every `z ∈ ℍ` the limit
`E₂(z; χ, ψ) = lim_{s → 0} E₂(z, s; χ, ψ)` exists and equals `C + A ∑_{n ≥ 1} a_n e^{2πinz/M}` plus, when `χ` and `ψ`
are both trivial, the non-holomorphic term `-π ∏_{p ∣ M}(1 - p⁻¹) ∏_{p ∣ L}(1 - p⁻¹) / Im z`. -/
theorem heckeLimit_weightTwo (L M : ℕ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (hχψ : χ (-1) * ψ (-1) = 1) (z : ℍ) :
    ∃ w : ℂ, IsHeckeLimit 2 χ ψ z w ∧
      HasSum (fun n : ℕ+ ↦ eisensteinCharA 2 ψ * eisensteinCharCoeff 2 χ ψ n *
          cexp (2 * π * Complex.I * (n : ℕ) * z / M))
        (w - eisensteinCharConst 2 (L := L) ψ -
          (if χ = 1 ∧ ψ = 1 then -π * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹)) *
            ∏ p ∈ L.primeFactors, (1 - (p : ℂ)⁻¹) else 0) / (z.im : ℂ)) := by
  exact by convert ModularFormsKB.Miyake.HeckeTrick.miyakeTheorem7_2_12 L M χ ψ hχψ z

/-- **Hecke's limit in weight one** (Miyake, Theorem 7.2.13). If `χ(-1)ψ(-1) = -1`, then for every `z ∈ ℍ` the limit
`E₁(z; χ, ψ) = lim_{s → 0} E₁(z, s; χ, ψ)` exists and equals `C + D + A ∑_{n ≥ 1} a_n e^{2πinz/M}`, with
`C = 2 L(1, ψ)` if `L = 1` (else `0`) and `D = -2πi ∏_{p ∣ M}(1 - p⁻¹) L(0, χ)` if `ψ` is trivial (else `0`). -/
theorem heckeLimit_weightOne (L M : ℕ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (hχψ : χ (-1) * ψ (-1) = -1) (z : ℍ) :
    ∃ w : ℂ, IsHeckeLimit 1 χ ψ z w ∧
      HasSum (fun n : ℕ+ ↦ eisensteinCharA 1 ψ * eisensteinCharCoeff 1 χ ψ n *
          cexp (2 * π * Complex.I * (n : ℕ) * z / M))
        (w - (if L = 1 then 2 * DirichletCharacter.LFunction ψ 1 else 0) -
          (if ψ = 1 then -2 * π * Complex.I * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹)) *
            DirichletCharacter.LFunction χ 0 else 0)) := by
  exact by convert ModularFormsKB.Miyake.HeckeTrick.miyakeTheorem7_2_13 L M χ ψ hχψ z

end HeckeTrick

section HeckeLemma

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

/-- **Hecke's lemma** (Miyake, Lemma 4.6.3). Let `k > 0`, `f ∈ 𝒢_k(N, χ)` (Tau Ceti's `modFormCharSpace`), and
`α = [a b; c d]` a primitive integer matrix with `N ∣ c`, `gcd(a, N) = 1` and `det α > 1` prime to `N`. If
`f |_k α ∈ 𝒢_k(N, χ)`, then `f = 0`. (Mathlib's slash operator differs from Miyake's by a nonzero constant.) Tau
Ceti's newform theory goes around this lemma. -/
theorem hecke_lemma (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (hk : 0 < k)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ TauCeti.modFormCharSpace k χ)
    (α : Matrix (Fin 2) (Fin 2) ℤ) (hN : (N : ℤ) ∣ α 1 0) (hco : IsCoprime (α 0 0) N) (hdet1 : 1 < α.det)
    (hdetco : IsCoprime α.det N) (hprim : ∀ m : ℤ, (∀ i j, m ∣ α i j) → IsUnit m) (g : GL (Fin 2) ℝ)
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = α.map (Int.cast))
    (hF : ∃ F ∈ TauCeti.modFormCharSpace k χ, ⇑F = ⇑f ∣[k] g) : f = 0 := by
  exact ModularFormsKB.Miyake.Sec4_6.heckeLemma N k χ hk f hf α hN hco hdet1 hdetco hprim g hg hF

end HeckeLemma

end ModularFormsKB.Headlines
