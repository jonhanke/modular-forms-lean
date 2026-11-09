import ModularFormsKB.Milne.Ch12.GaloisCM
import ModularFormsKB.Milne.Ch12.Isogenies
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Differential
import ModularFormsKB.Citation
/-!
# Milne, Section 12: corrected forms of Remark 12.12 and Proposition 12.21

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, pdf pp. 125–126.

The named statements `SerreTateFreeTateModule` and `ClassGroupActionPrincipal` are false as formalized (see
`docs/updates-and-errata.md`; the first is refuted in Lean, `not_serreTateFreeTateModule`). This file states the
corrected forms, which are what Milne means, as named statements; neither is proved here.

## Items

- `SerreTateFreeTateModuleQuadratic`: Remark 12.12 with Milne's standing hypothesis $[K:\mathbb Q] = 2$.
- `ClassGroupActionPrincipalNormalized`: Proposition 12.21 with the compatibility clause restricted to normalized
  $i\colon R \cong \mathrm{End}(E)$, those for which $i(a)$ acts on the invariant differential by $\iota(a)$ for a fixed
  embedding $\iota\colon K \to k$ (Milne normalizes $i$ through the action on the tangent space).
-/

open NumberField TauCeti TauCeti.Isogeny TauCeti.GlobalNumberFields WeierstrassCurve.Affine
open scoped WeierstrassCurve Classical

namespace ModularFormsKB.Milne

/-- **Remark 12.12, corrected** (Milne; Serre–Tate, *Good reduction of abelian varieties*, Ann. of Math. 88 (1968),
p. 502 [unverified]): for an order $R = \mathbb Z + \mathbb Z\omega$ of a **quadratic** field $K$ with
$i\colon R \cong \mathrm{End}(E)$, some $t \in T_\ell E$ makes $t, \omega t$ a $\mathbb Z_\ell$-basis. Named statement;
`SerreTateFreeTateModule` without the hypothesis $[K:\mathbb Q] = 2$ is false (`not_serreTateFreeTateModule`). -/
@[kb "milne2017mf" "Section 12, Rem. 12.12 (pdf p. 125), corrected"]
structure SerreTateFreeTateModuleQuadratic : Prop where
  free : ∀ (k : Type) [Field k] (W : WeierstrassCurve k) [W.IsElliptic] (Ks : Type) [Field Ks] [IsSepClosed Ks]
    [Algebra k Ks] (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : Ks) ≠ 0 →
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (O : NumberFieldOrder K)
      (i : O.toSubalgebra ≃+* Hom W.toAffine W.toAffine) (ω : O.toSubalgebra),
      (∀ x : O.toSubalgebra, ∃ a b : ℤ, x = a + b * ω) →
      ∃ t : TateModule ℓ (W⁄Ks).toAffine.Point,
        LinearIndependent ℤ_[ℓ] ![t, cmAction W Ks ℓ i ω t] ∧
          Submodule.span ℤ_[ℓ] {t, cmAction W Ks ℓ i ω t} = ⊤

/-- The corrected statement implies the original one for quadratic fields (the only case in which Milne uses it). -/
theorem SerreTateFreeTateModuleQuadratic.free_of_finrank (h : SerreTateFreeTateModuleQuadratic)
    {k : Type} [Field k] (W : WeierstrassCurve k) [W.IsElliptic] (Ks : Type) [Field Ks] [IsSepClosed Ks]
    [Algebra k Ks] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : Ks) ≠ 0) {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (O : NumberFieldOrder K) (i : O.toSubalgebra ≃+* Hom W.toAffine W.toAffine)
    (ω : O.toSubalgebra) (hω : ∀ x : O.toSubalgebra, ∃ a b : ℤ, x = a + b * ω) :
    ∃ t : TateModule ℓ (W⁄Ks).toAffine.Point,
      LinearIndependent ℤ_[ℓ] ![t, cmAction W Ks ℓ i ω t] ∧
        Submodule.span ℤ_[ℓ] {t, cmAction W Ks ℓ i ω t} = ⊤ :=
  h.free k W Ks ℓ hℓ K hK O i ω hω

/-- $i\colon R \cong \mathrm{End}(E)$ is **normalized** with respect to an embedding $\iota\colon K \to k$: each $i(a)$
pulls the invariant differential back to $\iota(a)$ times itself. -/
def IsNormalizedCM {k : Type*} [Field k] {W : WeierstrassCurve.Affine k} [W.IsElliptic] {K : Type*} [Field K]
    [NumberField K] {O : NumberFieldOrder K} (ι : K →+* k) (i : O.toSubalgebra ≃+* Hom W W) : Prop :=
  ∀ a : O.toSubalgebra, (i a).pullbackDifferential (invariantDifferential W) = ι a • invariantDifferential W

/-- **Proposition 12.21, corrected** (Milne; proof omitted in the book): for $k$ algebraically closed of
characteristic zero and a fixed embedding $\iota\colon K \to k$, $\mathrm{Cl}(R)$ acts simply transitively on
$\mathrm{Ell}_k(R)$, the action characterized by $[\mathfrak a] \cdot j(E) = j(E')$ for every $\mathfrak a$-isogeny
$E \to E'$ with respect to a **normalized** $i$. Named statement; without the normalization the compatibility clause
forces $[\mathfrak a]^2 = 1$ (see `docs/updates-and-errata.md`). -/
@[kb "milne2017mf" "Section 12, Prop. 12.21 (pdf p. 126), corrected"]
structure ClassGroupActionPrincipalNormalized : Prop where
  principal : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (K : Type) [Field K] [NumberField K]
    (O : NumberFieldOrder K), Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ ι : K →+* k,
    ∃ act : Pic O → EllCMOver k O → EllCMOver k O,
      (∀ (W W' : WeierstrassCurve.Affine k) [W.IsElliptic] [W'.IsElliptic] (i : O.toSubalgebra ≃+* Hom W W),
          IsNormalizedCM ι i →
          ∀ (I : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ) (J : Ideal O.toSubalgebra),
          ((J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) = I) →
          (hW : W.j ∈ EllCMOver k O) → (hW' : W'.j ∈ EllCMOver k O) → (φ : Hom W W') → IsAIsogeny i J φ →
            act (ClassGroup.mk (K := K) I) ⟨W.j, hW⟩ = ⟨W'.j, hW'⟩) ∧
      ∀ x₀, Function.Bijective fun c ↦ act c x₀

end ModularFormsKB.Milne
