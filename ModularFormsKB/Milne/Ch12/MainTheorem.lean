import ModularFormsKB.Milne.Ch12.CMDefs
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import ModularFormsKB.Citation
/-!
# Milne, Section 12: the main theorem of complex multiplication (12.18, 12.25, 12.26)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, pdf pp. 126–129.

Neither Mathlib nor Tau Ceti has the Hilbert class field, ring class fields or the Artin map of a quadratic imaginary
field, so these results are **named statements**, phrased with the automorphisms of $\mathbb C$:

- $K$ is a quadratic imaginary field with an embedding $\iota\colon K \to \mathbb C$; "an automorphism over $K$" is a
  ring automorphism $\tau$ of $\mathbb C$ fixing $\iota(K)$.
- **Frobenius elements.** Let $\overline{\mathbb Z} \subseteq \mathbb C$ be the ring of all algebraic integers
  (`integralClosure ℤ ℂ`). For a prime $\mathfrak p$ of $K$ and a prime $\mathfrak P$ of $\overline{\mathbb Z}$ above
  $\iota(\mathfrak p)$, a Frobenius element at $\mathfrak P$ is an automorphism $\tau$ over $K$ with $\tau(x) \equiv
  x^{N\mathfrak p} \pmod{\mathfrak P}$ for every algebraic integer $x$ (`IsFrobeniusAt`). It restricts to the
  Frobenius $\mathrm{Frob}(\mathfrak p)$ of every finite extension of $K$ in which $\mathfrak p$ is unramified.
- $j(\mathfrak a) = j(\mathbb C/\iota\mathfrak a)$ (`IsJOfIdeal`): the $j$-invariant of `L.weierstrassCurve` for any
  period pair `L` with lattice $\iota(\mathfrak a)$.

## Items

- **Theorem 12.18** `MainTheoremCM` (named): (a) $K[j(E)]$ is the Hilbert class field: it has degree $h_K$ over $K$
  and a prime $\mathfrak p$ of $K$ splits in it (its Frobenius elements fix $j(E)$) exactly when $\mathfrak p$ is
  principal (by Bauer's theorem this characterizes the Hilbert class field among the extensions of $K$ in
  $\mathbb C$); (b) the automorphisms over $K$ permute $\mathrm{Ell}(\mathcal O_K)$ transitively; (c)
  $\mathrm{Frob}(\mathfrak p)(j(\mathfrak a)) = j(\mathfrak a\mathfrak p^{-1})$.
- **Lemma 12.25** `FrobeniusClassLemma` (named): Milne's $\varphi(\mathrm{Frob}_{\mathfrak p}) = \mathrm{Cl}(\mathfrak p)$
  for a set of primes of density one: the primes of degree one outside a finite set (Milne's set $S$: conditions
  (i), (ii) exclude finitely many primes).
- **Theorem 12.26** `GaloisKabOverKstar` (named): $\mathrm{Gal}(K^{\mathrm{ab}}/K^*)$ is a product of groups of order $2$,
  where $K^* = \mathbb Q^{\mathrm{cyc}}\cdot K'$ and $K'$ is generated over $K$ by the $j(\tau)$, $\tau \in K \cap
  \mathbb H$; here: every automorphism of $\mathbb C$ fixing $K^*$ has order dividing $2$ on $K^{\mathrm{ab}}$.
- **Theorem 12.27** is not stated: it needs ray class fields and the Weber function (none available).
-/

open NumberField TauCeti TauCeti.GlobalNumberFields UpperHalfPlane

namespace ModularFormsKB.Milne

variable {K : Type*} [Field K] [NumberField K] (ι : K →+* ℂ)

/-- The fractional ideals of the ring of integers, as Tau Ceti's maximal order. -/
abbrev MaxOrderIdeal (K : Type*) [Field K] [NumberField K] :=
  FractionalIdeal (nonZeroDivisors (maximalNumberFieldOrder K).toSubalgebra) K

/-- $x = j(\mathbb C/\iota\mathfrak a)$: $x$ is the $j$-invariant of the curve of every period pair whose lattice is
$\iota(\mathfrak a)$. -/
def IsJOfIdeal (I : MaxOrderIdeal K) (x : ℂ) : Prop :=
  ∀ L : PeriodPair, L.lattice = idealLattice ι (maximalNumberFieldOrder K) I → L.weierstrassCurve.j = x

/-- $\tau$ is an automorphism of $\mathbb C$ over $K$ (fixing $\iota(K)$). -/
def IsAutOver (τ : ℂ ≃+* ℂ) : Prop := ∀ x : K, τ (ι x) = ι x

/-- $\tau$ is a Frobenius element at a prime $\mathfrak P$ of the algebraic integers lying over $\iota(\mathfrak p)$:
$\tau$ is an automorphism over $K$ with $\tau(x) - x^{N\mathfrak p} \in \mathfrak P$ for every algebraic integer
$x$. -/
def IsFrobeniusAt (𝔭 : Ideal (𝓞 K)) (τ : ℂ ≃+* ℂ) : Prop :=
  IsAutOver ι τ ∧ ∃ P : Ideal (integralClosure ℤ ℂ), P.IsMaximal ∧
    (∀ x : 𝓞 K, (⟨ι x, (x.2.map ι.toIntAlgHom)⟩ : integralClosure ℤ ℂ) ∈ P ↔ x ∈ 𝔭) ∧
    ∀ x : integralClosure ℤ ℂ, ∃ y : integralClosure ℤ ℂ, (y : ℂ) = τ x ∧ y - x ^ Ideal.absNorm 𝔭 ∈ P

/-- The prime $\mathfrak p$ of $\mathcal O_K$ as a fractional ideal of the maximal order. -/
noncomputable def primeAsIdeal (𝔭 : Ideal (𝓞 K)) : MaxOrderIdeal K :=
  ((𝔭 : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)

/-- **Theorem 12.18** (Milne; the first main theorem of complex multiplication: Weber, Hasse, Deuring
[unverified]), as a named statement in the form explained in the module docstring. -/
@[kb "milne2017mf" "Section 12, Thm. 12.18 (pdf p. 126)"]
structure MainTheoremCM : Prop where
  /-- (a), degree: $[K(j(E)) : K] = h_K$. -/
  degree : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ), Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ x ∈ EllCM (maximalNumberFieldOrder K),
      Module.finrank ℚ (IntermediateField.adjoin ℚ (Set.range ι ∪ {x})) = 2 * Nat.card (ClassGroup (𝓞 K))
  /-- (a), splitting: the Frobenius elements at $\mathfrak p$ fix $j(E)$ iff $\mathfrak p$ is principal. -/
  splits_iff : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ), Module.finrank ℚ K = 2 →
    IsTotallyComplex K → ∀ x ∈ EllCM (maximalNumberFieldOrder K), ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsMaximal → 𝔭 ≠ ⊥ →
      ((∀ τ, IsFrobeniusAt ι 𝔭 τ → τ x = x) ↔ Submodule.IsPrincipal 𝔭)
  /-- (b): the automorphisms over $K$ permute $\mathrm{Ell}(\mathcal O_K)$ transitively. -/
  stable : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ), Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ τ : ℂ ≃+* ℂ, IsAutOver ι τ → ∀ x ∈ EllCM (maximalNumberFieldOrder K), τ x ∈ EllCM (maximalNumberFieldOrder K)
  transitive : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ), Module.finrank ℚ K = 2 →
    IsTotallyComplex K → ∀ x ∈ EllCM (maximalNumberFieldOrder K), ∀ y ∈ EllCM (maximalNumberFieldOrder K),
      ∃ τ : ℂ ≃+* ℂ, IsAutOver ι τ ∧ τ x = y
  /-- (c): $\mathrm{Frob}(\mathfrak p)(j(\mathfrak a)) = j(\mathfrak a\mathfrak p^{-1})$. -/
  frobenius : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ), Module.finrank ℚ K = 2 →
    IsTotallyComplex K → ∀ (I : MaxOrderIdeal K), I ≠ 0 → ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsMaximal → 𝔭 ≠ ⊥ →
      ∀ τ, IsFrobeniusAt ι 𝔭 τ → ∀ x y : ℂ, IsJOfIdeal ι I x → IsJOfIdeal ι (I * (primeAsIdeal 𝔭)⁻¹) y →
        τ x = y

/-- **Lemma 12.25** (Milne), as a named statement: let $x_0 = j(\mathfrak a_0) \in \mathrm{Ell}(\mathcal O_K)$. For all
primes $\mathfrak p$ of $K$ of degree one ($N\mathfrak p$ prime) outside a finite set, every Frobenius element
$\tau$ at $\mathfrak p$ satisfies $\tau(x_0) = \mathrm{Cl}(\mathfrak p)^{-1} * x_0$, i.e. $\varphi(\mathrm{Frob}_
{\mathfrak p}) = \mathrm{Cl}(\mathfrak p)$ for Milne's $\varphi$ ($x_0^\sigma = x_0 * \varphi(\sigma)$, with the class
group acting through $\mathfrak a * \mathbb C/\Lambda = \mathbb C/\Lambda\mathfrak a^{-1}$). -/
@[kb "milne2017mf" "Section 12, Lemma 12.25 (pdf p. 128)"]
structure FrobeniusClassLemma : Prop where
  frob : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ), Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ (I : MaxOrderIdeal K), I ≠ 0 → ∃ T : Set (Ideal (𝓞 K)), T.Finite ∧
      ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsMaximal → 𝔭 ∉ T → (Ideal.absNorm 𝔭).Prime →
        ∀ τ, IsFrobeniusAt ι 𝔭 τ → ∀ x y : ℂ, IsJOfIdeal ι I x →
          IsJOfIdeal ι (I * (primeAsIdeal 𝔭)⁻¹) y → τ x = y

/-- $\iota(K)$ as a subfield of $\mathbb C$. -/
noncomputable def embField : IntermediateField ℚ ℂ := ι.toRatAlgHom.fieldRange

/-- $K^{\mathrm{ab}} \subseteq \mathbb C$: the compositum of the finite Galois extensions of $\iota(K)$ in
$\mathbb C$ with abelian Galois group. -/
noncomputable def embAb : IntermediateField (embField ι) ℂ :=
  ⨆ L : {L : IntermediateField (embField ι) ℂ // FiniteDimensional (embField ι) L ∧ IsGalois (embField ι) L ∧
      ∀ σ τ : L ≃ₐ[embField ι] L, σ * τ = τ * σ}, L.1

/-- $K^* = \mathbb Q^{\mathrm{cyc}} \cdot K'$: $\iota(K)$ with all roots of unity and all $j(\tau)$, $\tau \in \mathbb H
\cap \iota(K)$. -/
noncomputable def embKStar : IntermediateField (embField ι) ℂ :=
  IntermediateField.adjoin (embField ι)
    ({x | ∃ n : ℕ, 0 < n ∧ x ^ n = 1} ∪ {x | ∃ z : ℍ, (z : ℂ) ∈ Set.range ι ∧ x = TauCeti.ModularForm.j z})

/-- **Theorem 12.26** (Milne), as a named statement: $K^* \subseteq K^{\mathrm{ab}}$ and $\mathrm{Gal}(K^{\mathrm{ab}}/
K^*)$ is a product of groups of order $2$: every automorphism of $\mathbb C$ fixing $K^*$ acts on $K^{\mathrm{ab}}$
with square the identity. -/
@[kb "milne2017mf" "Section 12, Thm. 12.26 (pdf p. 129)"]
structure GaloisKabOverKstar : Prop where
  le : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ), Module.finrank ℚ K = 2 → IsTotallyComplex K →
    embKStar ι ≤ embAb ι
  sq_eq_one : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ), Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ σ : ℂ ≃ₐ[embField ι] ℂ, (∀ x ∈ embKStar ι, σ x = x) → ∀ x ∈ embAb ι, σ (σ x) = x

end ModularFormsKB.Milne
