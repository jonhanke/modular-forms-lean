import ModularFormsKB.Milne.Wave4A.DegreeOneTransfer
import ModularFormsKB.Milne.Wave4A.GenusFormula
import ModularFormsKB.Milne.Wave4A.SphereRiemannRoch
import ModularFormsKB.Milne.RS.CanonicalGenus
import ModularFormsKB.Citation
/-!
# Miyake §2.2, §2.5 and §4.2: Riemann–Roch, dimension and genus formulas (modular groups)

Miyake, *Modular Forms* (Springer 1989): §2.2, p. 48 (Theorem 2.2.1, Corollary 2.2.2); §2.5,
pp. 60–61 (Theorem 2.5.2); §4.2, p. 113 (Theorem 4.2.11).

These rows rest on the Riemann–Roch theorem for compact Riemann surfaces, which is in neither
Mathlib nor Tau Ceti. This repository already carries the material in Milne's numbering
(`ModularFormsKB/Milne/`): the named input `RiemannRochStatement X`, proved for the Riemann
sphere and for `X(1)`; the reduction of the dimension formula and of the genus formula to
Riemann–Roch and Riemann–Hurwitz; and the unconditional ramification count of `X(Γ) → X(1)`.
This file restates those results in Miyake's terms and under Miyake's numbering.

Conventions.
* The genus of a compact Riemann surface is the dimension of the space of holomorphic
  differentials: `ModularFormsKB.Milne.RiemannSurface.genus X` (used in Corollary 2.2.2 and
  Theorem 4.2.11) or, in Milne's dimension formula, `ModularFormsKB.Milne.genus` of the
  quotient `modularCurve Γ` (two parallel definitions of this repository, each used as the
  underlying Milne theorem uses it). Miyake defines the genus topologically
  (§1.8) and identifies it with `l(div ω)` in Corollary 2.2.2; here that identification is the
  definition, and `ℓ(div ω) = g` is `ell_div_eq_genus` below.
* A modular group `Γ` is a subgroup of finite index of `SL₂(ℤ)`; `X(Γ) = Γ\ℍ*`
  (`ModularFormsKB.Milne.ModularCurveX Γ`, Tau Ceti's compactified quotient). Miyake's `μ`,
  `ν₂`, `ν₃`, `ν∞` are `genusIndex Γ`, `nuTwo Γ`, `nuThree Γ`, `nuInfty Γ`.
* Miyake's weight `k` (even) is `2k` here, as in Milne.

Status.
* Theorem 2.2.1 (Riemann–Roch): the statement is the named input
  `ModularFormsKB.Milne.RiemannSurface.RiemannRochStatement X`; proved for `ℙ¹(ℂ)`
  (`riemannRoch_onePoint`) and for `X(SL₂(ℤ))` (`riemannRoch_modularCurveX_top`).
* Corollary 2.2.2, `l(div ω) = g`: proved for every compact Riemann surface
  (`ell_div_eq_genus`); `deg div ω = 2g - 2` is the named input
  `ModularFormsKB.Milne.CanonicalDegreeStatement`.
* Theorem 2.5.2 for modular groups, `dim 𝒢_k(Γ)` for even `k ≥ 2`: conditional on Riemann–Roch
  and the canonical degree on `X(Γ)` (`finrank_modularForm_of_riemannRoch`); unconditional for
  `SL₂(ℤ)` (`finrank_modularForm_top`). The cusp-form part for `SL₂(ℤ)` is in
  `Wave3/LevelOneDimension.lean`.
* Theorem 4.2.11 (the genus of `X(Γ)`): conditional on the Riemann–Hurwitz formula
  (`genus_modularCurveX_eq`); the ramification count (4.2.13)–(4.2.15) of its proof is
  unconditional (`ramificationDegree_modularCurveX_eq`).
-/

open Set
open scoped MatrixGroups Manifold

noncomputable section

namespace ModularFormsKB.Miyake

open ModularFormsKB.Milne ModularFormsKB.Milne.RiemannSurface TauCeti.RiemannSurface

/-! ### §2.2: Riemann–Roch -/

/-- **Miyake, Theorem 2.2.1** (Riemann–Roch) for the Riemann sphere `ℙ¹(ℂ) = OnePoint ℂ`:
`l(a) = deg a - g + 1 + l(div ω - a)` for every divisor `a` and nonzero differential `ω`. -/
@[kb "miyake1989" "Theorem 2.2.1, p. 48 (for the Riemann sphere)"]
theorem riemannRoch_onePoint : RiemannRochStatement (OnePoint ℂ) :=
  riemannRoch_sphere

/-- **Miyake, Theorem 2.2.1** (Riemann–Roch) for `X(1) = SL₂(ℤ)\ℍ*`. -/
@[kb "miyake1989" "Theorem 2.2.1, p. 48 (for X(1))"]
theorem riemannRoch_modularCurveX_top : RiemannRochStatement (ModularCurveX ⊤) :=
  riemannRochStatement_modularCurveX_top

/-- **Miyake, Corollary 2.2.2**, `l(div ω) = g`: on a compact Riemann surface, for every nonzero
meromorphic differential `ω`, the space `L(div ω)` has dimension the genus. -/
@[kb "miyake1989" "Corollary 2.2.2, p. 48: l(div omega) = g"]
theorem ell_div_eq_genus {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X] [CompactSpace X] [T2Space X]
    {ω : MeromorphicDifferential X} (hω : ¬ ω.IsZero) :
    ell X ω.divisor = RiemannSurface.genus X :=
  RS.ell_divisor_eq_genus hω

/-! ### §2.5: the dimension formula for modular groups -/

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- **Miyake, Theorem 2.5.2** (the dimension of `𝒢_K(Γ)` for even `K = 2k ≥ 2`), for a modular
group `Γ`, conditional on Riemann–Roch and `deg div ω = 2g - 2` on `X(Γ)`:
`dim 𝒢_{2k}(Γ) = (2k - 1)(g - 1) + Σ_μ [k(1 - 1/e_μ)] + k t`, `t` the number of cusps. In
Miyake's form, with `K = 2k`: `(K - 1)(g - 1) + Σ_μ [K/2 (1 - 1/e_μ)] + (K/2 - 1) t + t` for
`K ≥ 4`, and `g + t - 1` for `K = 2` (every modular group has a cusp). -/
@[kb "miyake1989" "Theorem 2.5.2, pp. 60-61 (modular groups, conditional on Riemann-Roch)"]
theorem finrank_modularForm_of_riemannRoch
    (hRR : RiemannRochStatement (modularCurve Γ)) (hC : CanonicalDegreeStatement (modularCurve Γ))
    (k : ℕ) (hk : 1 ≤ k) :
    (Module.finrank ℂ (ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * k : ℕ)) : ℤ) =
      (2 * k - 1) * ((Milne.genus (modularCurve Γ) : ℤ) - 1) + cuspCount Γ * k + ellipticTerm Γ k :=
  (dimensionFormula_of_riemannRoch Γ hRR hC).formula k hk

/-- **Miyake, Theorem 2.5.2** for `Γ = SL₂(ℤ)`, `𝒢` part, unconditional (Milne's Theorem 4.9 for
`Γ(1)`, from Riemann–Roch on `X(1)`). -/
@[kb "miyake1989" "Theorem 2.5.2, pp. 60-61 (for SL2(Z))"]
theorem finrank_modularForm_top (k : ℕ) (hk : 1 ≤ k) :
    (Module.finrank ℂ (ModularForm ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
        (2 * k : ℕ)) : ℤ) =
      (2 * k - 1) * ((Milne.genus (modularCurve ⊤) : ℤ) - 1) + cuspCount ⊤ * k + ellipticTerm ⊤ k :=
  dimensionFormula_top.formula k hk

/-! ### §4.2: the genus of `X(Γ)` -/

/-- **Miyake, Theorem 4.2.11**, conditional on the Riemann–Hurwitz formula (Miyake's (1.8.8)) for
`X(Γ)` over the Riemann sphere: for a modular group `Γ`,
`g = 1 + μ/12 - ν₂/4 - ν₃/3 - ν∞/2`. -/
@[kb "miyake1989" "Theorem 4.2.11, p. 113 (conditional on the Hurwitz formula)"]
theorem genus_modularCurveX_eq
    (hRH : RiemannHurwitzStatement (ModularCurveX Γ) (OnePoint ℂ)) :
    (RiemannSurface.genus (ModularCurveX Γ) : ℚ) =
      1 + (genusIndex Γ : ℚ) / 12 - (nuTwo Γ : ℚ) / 4 - (nuThree Γ : ℚ) / 3 -
        (nuInfty Γ : ℚ) / 2 :=
  genus_modularCurveX Γ hRH

/-- **Miyake, proof of Theorem 4.2.11**, (4.2.13)–(4.2.15), unconditional: the total
ramification of `F : X(Γ) → X(1)` is
`Σ (e_b - 1) = (μ - ν₂)/2 + 2(μ - ν₃)/3 + (μ - ν∞)`. -/
@[kb "miyake1989" "Theorem 4.2.11, proof, (4.2.13)-(4.2.15), p. 113"]
theorem ramificationDegree_modularCurveX_eq :
    (ramificationDegree (modularCurveXMap Γ) : ℝ) =
      ((genusIndex Γ : ℝ) - nuTwo Γ) / 2 + 2 * ((genusIndex Γ : ℝ) - nuThree Γ) / 3 +
        ((genusIndex Γ : ℝ) - nuInfty Γ) :=
  ramificationDegree_modularCurveX Γ

end ModularFormsKB.Miyake
