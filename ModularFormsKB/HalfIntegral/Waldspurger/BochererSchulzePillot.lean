/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.GrossFormula

/-!
# Böcherer–Schulze-Pillot: central values through ternary theta series of quaternion orders

Böcherer–Schulze-Pillot 1991 `bochererschulzepillot1991` [unverified] extend Gross's formula to newforms of squarefree
level $N$ and weight $2k$: the theta series of the ternary lattices of an Eichler order of level $N$ in a definite
quaternion algebra, weighted by the Brandt eigenvector of $f$ (with harmonic polynomials when $k > 1$), give a form of
weight $k + 1/2$ whose $|D|$-th coefficient squared is proportional to $L(f, k)\,L(f, D, k)\,|D|^{k-1/2}$, for $D$ with the
local conditions of the algebra at the primes dividing $N$.

`BochererSchulzePillot N n B` states the case used here: weight $2$ ($k = 1$), $N$ squarefree with an odd number of
prime factors, $B$ the Brandt module of the maximal orders of the algebra ramified exactly at the primes dividing $N$ and
at $\infty$, and $D$ with every prime $\ell \mid N$ inert in $\mathbb Q(\sqrt D)$ (loose end LE-MF-0314: Eichler orders,
weight $2k$ and the other local conditions are not stated). The Brandt module is data, as in `GrossFormula.lean`.

**Proved.** `grossFormula_of_bochererSchulzePillot`: at prime level the statement is `GrossFormula`.

**Relation to the other statements.** The ternary theta series here are the cuspidal parts of genus theta series
(`HalfIntegral/TernaryDecomposition.lean`: the decomposition of a theta series into its unary-theta and orthogonal
parts); `WaldspurgerSquareClassFull` gives the ratio $c(n_1)^2L(f, D_2, 1)\sqrt{n_2} = c(n_2)^2L(f,D_1,1)\sqrt{n_1}$ on one
square class, which the formula below implies on its classes (as `grossRatio_of_grossFormula` does at $N = 11$), and
in addition fixes the constant through $L(f, 1)$. Material on the quadratic forms themselves is not part of this library.
-/

namespace ModularFormsKB.HalfIntegral.Waldspurger.Gross

open Complex MatrixGroups CongruenceSubgroup ModularForm

local notation "ℍ" => UpperHalfPlane

/-- **Böcherer–Schulze-Pillot's formula in weight 2, for maximal orders** (Böcherer–Schulze-Pillot 1991
`bochererschulzepillot1991`, Thm. and Cor. [unverified]): for $N$ squarefree with an odd number of prime factors, a
Brandt module $B$ of level $N$, $e \ne 0$ with $\sum e_i = 0$, and $F \in S_2(\Gamma_0(N))$ with coefficients $a$,
$a(1) = 1$, and $B(m)^{\mathsf T}e = a(m)e$ for $(m, N) = 1$, there is $\kappa > 0$ with
$L_0(1)\,L(1)\,\sqrt{|D|} = \kappa\,c_e(|D|)^2$ for every fundamental $D < 0$ such that every prime $\ell \mid N$ is inert in
$\mathbb Q(\sqrt D)$. -/
@[kb "bochererschulzepillot1991" "L(f,1) L(f,D,1) √|D| proportional to the square of the |D|-th coefficient of Σ e_i θ_i, squarefree level, weight 2, maximal orders [unverified]"]
structure BochererSchulzePillot (N n : ℕ) (B : BrandtModule N n) : Prop where
  formula : Squarefree N → Odd N.primeFactors.card → ∀ e : Fin n → ℤ, e ≠ 0 → ∑ i, e i = 0 →
    ∀ (F : CuspForm ((Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2) (a : ℕ → ℂ),
      Abstract.HasQExp F a → a 1 = 1 →
      (∀ m, 1 ≤ m → m.Coprime N → ∀ i, (((B.B m).transpose.mulVec e i : ℤ) : ℂ) = a m * e i) →
      ∃ κ : ℝ, 0 < κ ∧ ∀ L₀ : ℂ → ℂ, IsEntireLSeries a 2 L₀ →
        ∀ D : ℤ, IsFundamentalDiscriminant D → D < 0 → (∀ ℓ ∈ N.primeFactors, jacobiSym D ℓ = -1) →
          ∀ L : ℂ → ℂ, IsEntireLSeries (fun n ↦ (kroneckerDisc D n : ℂ) * a n) 2 L →
            L₀ 1 * L 1 * (Real.sqrt D.natAbs : ℂ) = ((κ * grossCoeffOf B e D.natAbs ^ 2 : ℝ) : ℂ)

/-- **At prime level, Böcherer–Schulze-Pillot is Gross's formula.** -/
theorem grossFormula_of_bochererSchulzePillot {p n : ℕ} (B : BrandtModule p n)
    (h : BochererSchulzePillot p n B) : GrossFormula p n B := by
  refine ⟨fun hp e he hsum F a hF h1 heig ↦ ?_⟩
  have hodd : Odd p.primeFactors.card := by rw [hp.primeFactors, Finset.card_singleton]; exact odd_one
  obtain ⟨κ, hκ, hf⟩ := h.formula hp.squarefree hodd e he hsum F a hF h1 heig
  refine ⟨κ, hκ, fun L₀ hL₀ D hD hD0 hDp L hL ↦ hf L₀ hL₀ D hD hD0 (fun ℓ hℓ ↦ ?_) L hL⟩
  rw [hp.primeFactors, Finset.mem_singleton] at hℓ
  rw [hℓ]
  exact hDp

end ModularFormsKB.HalfIntegral.Waldspurger.Gross
