/-
# Waldspurger's theorem on Fourier coefficients: named input (level 4, plus space)

Waldspurger 1981 `waldspurger1981` (Corollaire 2 [unverified]) proves, for a Hecke
eigenform $g$ of weight $k+\tfrac12$ corresponding to $F$ under the Shimura lift, that $c(n)^2$ is proportional to
$n^{k-1/2}L(F, \chi_{D}, k)$ on each square class of $n$ (with a local condition at the primes dividing the level). We state the
special case of Kohnen's plus space of level $4$ and trivial character, in the ratio form, where it is the consequence of the
Kohnen–Zagier formula recorded in the introduction of Kohnen–Zagier 1981 `kohnenzagier1981`:
$$ c(|D_1|)^2\,|D_2|^{k-1/2}\,L(F, D_2, k) = c(|D_2|)^2\,|D_1|^{k-1/2}\,L(F, D_1, k) $$
for fundamental discriminants $D_1, D_2$ with $(-1)^k D_i > 0$. Unlike the Kohnen–Zagier formula, this does not involve the
Petersson norms. The general level $4N$ statement with character (and the local square-class condition) is not yet
stated; its normalization needs checking against the source.
-/
import ModularFormsKB.HalfIntegral.Abstract.Kohnen

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup ModularForm
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- **Waldspurger's theorem, level 4 plus space, ratio form** (Waldspurger 1981 `waldspurger1981`, Corollaire 2, as
specialized in Kohnen–Zagier 1981 `kohnenzagier1981`, introduction [unverified]). -/
@[kb "waldspurger1981" "Cor. 2, ratio form, specialized to the level 4 plus space [unverified]"]
structure WaldspurgerPlus (M : MultiplierSystem) (k : ℕ) : Prop where
  ratio : 1 ≤ k → ∀ (g : ℍ → ℂ) (c : ℕ → ℂ) (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ),
    Corresponds M k g c F b → ∀ D₁ D₂ : ℤ, IsFundamentalDiscriminant D₁ → IsFundamentalDiscriminant D₂ →
      0 < (-1) ^ k * D₁ → 0 < (-1) ^ k * D₂ →
      ∀ L₁ L₂ : ℂ → ℂ, IsEntireLSeries (fun n ↦ (kroneckerDisc D₁ n : ℂ) * b n) ((k : ℝ) + 1) L₁ →
        IsEntireLSeries (fun n ↦ (kroneckerDisc D₂ n : ℂ) * b n) ((k : ℝ) + 1) L₂ →
        c D₁.natAbs ^ 2 * ((D₂.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) * L₂ k =
          c D₂.natAbs ^ 2 * ((D₁.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) * L₁ k

end ModularFormsKB.HalfIntegral
