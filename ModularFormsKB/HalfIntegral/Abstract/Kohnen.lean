/-
# Kohnen's isomorphism and the Kohnen–Zagier formula: named inputs

Level $4$, trivial character, relative to an abstract multiplier system `M`
(`ModularFormsKB/HalfIntegral/Abstract/Multiplier.lean`), meant to be the theta multiplier. Integral weight forms of level one are
Mathlib's `CuspForm 𝒮ℒ (2 * k)`; their coefficients are read through `Abstract.HasQExp`.

**Normalizations** (Kohnen–Zagier 1981 `kohnenzagier1981`, Thm. 1 [unverified]):
- $\langle g, g\rangle = \tfrac16\int_{\Gamma_0(4)\backslash\mathbb H}|g|^2 v^{k+1/2}\,du\,dv/v^2$ (`peterssonNormSqFour`), computed with
  the six coset representatives `gamma0FourReps` on Mathlib's fundamental domain `ModularGroup.fd`;
- $\langle F, F\rangle = \int_{\mathrm{SL}_2(\mathbb Z)\backslash\mathbb H}|F|^2 v^{2k}\,du\,dv/v^2$ (`peterssonNormSqOne`);
- $L(F, D, s) = \sum_{n\ge1}\left(\frac Dn\right) b(n) n^{-s}$, where $\left(\frac Dn\right)$ is the Kronecker symbol (`kroneckerDisc`)
  and $b$ the coefficients of $F$; at $s = k$ (the centre) it is the value of the entire continuation (`IsEntireLSeries`).

**Kronecker symbol.** Mathlib has the Jacobi symbol only. For a discriminant $D$ we set
$\left(\frac D2\right) = 0$ if $D$ is even, $1$ if $D \equiv \pm1 \bmod 8$, $-1$ if $D \equiv \pm 3 \bmod 8$, and extend
multiplicatively: $\left(\frac D{2^e m}\right) = \left(\frac D2\right)^e\left(\frac Dm\right)$ for odd $m$.
-/
import ModularFormsKB.HalfIntegral.Abstract.Shimura
import Mathlib.NumberTheory.ModularForms.Basic

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup ModularForm
open scoped Real
open scoped Manifold

local notation "ℍ" => UpperHalfPlane

/-- The Kronecker symbol $\left(\frac D2\right)$. -/
def kroneckerTwo (D : ℤ) : ℤ :=
  if 2 ∣ D then 0 else if D % 8 = 1 ∨ D % 8 = 7 then 1 else -1

/-- **The Kronecker symbol** $\left(\frac Dn\right)$ for $n \ge 1$: $\left(\frac D2\right)^{e}\left(\frac Dm\right)$ for $n = 2^e m$,
$m$ odd (Jacobi symbol). Only used for discriminants $D \equiv 0, 1 \bmod 4$. -/
def kroneckerDisc (D : ℤ) (n : ℕ) : ℤ :=
  kroneckerTwo D ^ n.factorization 2 * jacobiSym D (n / 2 ^ n.factorization 2)

/-- **Fundamental discriminant:** $D \equiv 1 \bmod 4$ squarefree, or $D = 4m$ with $m \equiv 2, 3 \bmod 4$ squarefree. -/
def IsFundamentalDiscriminant (D : ℤ) : Prop :=
  (D % 4 = 1 ∧ Squarefree D) ∨ ∃ m : ℤ, D = 4 * m ∧ (m % 4 = 2 ∨ m % 4 = 3) ∧ Squarefree m

/-- **$L$ is an entire continuation of $\sum b(n)n^{-s}$:** $L$ is entire and equals the Dirichlet series for
$\operatorname{Re} s > \sigma_0$. By the identity theorem such an $L$ is unique. -/
def IsEntireLSeries (b : ℕ → ℂ) (σ₀ : ℝ) (L : ℂ → ℂ) : Prop :=
  Differentiable ℂ L ∧ ∀ s : ℂ, σ₀ < s.re → L s = LSeries b s

/-- $\langle g, g\rangle = \tfrac16\int_{\Gamma_0(4)\backslash\mathbb H}|g|^2 v^{k+1/2}\,d\mu$ (Kohnen–Zagier's normalization). -/
noncomputable def peterssonNormSqFour (k : ℕ) (g : ℍ → ℂ) : ℂ :=
  (1 / 6 : ℂ) * peterssonReps gamma0FourReps ((k : ℝ) + 1 / 2) g g

/-- $\langle F, F\rangle = \int_{\mathrm{SL}_2(\mathbb Z)\backslash\mathbb H}|F|^2 v^{2k}\,d\mu$. -/
noncomputable def peterssonNormSqOne (k : ℕ) (F : ℍ → ℂ) : ℂ :=
  peterssonReps [1] (2 * k) F F

/-- **Kohnen's isomorphism** (Kohnen 1980 `kohnen1980`, Thm. 1 [unverified]): for $k \ge 1$ there is a $\mathbb C$-linear
isomorphism $\Phi : S^+_{k+1/2}(4) \cong S_{2k}(\mathrm{SL}_2(\mathbb Z))$ compatible with the Hecke operators: for every odd
prime $p$, if $f, f' \in S^+_{k+1/2}(4)$ have coefficients $a$ and $T(p^2)a$, then $\Phi f'$ has the coefficients $T(p)$ of
those of $\Phi f$. (At $p = 2$ Kohnen's operator is the projection $T^+(4)$ of $U(4)$ to the plus space; not stated.) -/
@[kb "kohnen1980" "Thm. 1: S⁺_{k+1/2}(4) ≅ S_{2k}(1) as Hecke modules [unverified]"]
structure KohnenIsomorphism (M : MultiplierSystem) (k : ℕ) : Prop where
  iso : 1 ≤ k → ∃ Φ : M.plusCuspForms k 1 1 ≃ₗ[ℂ] CuspForm 𝒮ℒ (2 * k : ℕ),
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ f f' : M.plusCuspForms k 1 1, ∀ a b : ℕ → ℂ,
      Abstract.HasQExp f a → Abstract.HasQExp f' (heckeT k 1 1 p a) → Abstract.HasQExp (Φ f) b →
        Abstract.HasQExp (Φ f') (heckeTInt (2 * k) 1 1 p b)

/-- **$g \in S^+_{k+1/2}(4)$ and $F \in S_{2k}(1)$ correspond:** $F$ is a normalized Hecke eigenform with coefficients $b$
($b(1) = 1$, $T(p)b = b(p)\,b$ for all primes $p$), and $g \ne 0$ has coefficients $c$ with $T(p^2)c = b(p)\,c$ for all odd
primes $p$. -/
structure Corresponds (M : MultiplierSystem) (k : ℕ) (g : ℍ → ℂ) (c : ℕ → ℂ) (F : CuspForm 𝒮ℒ (2 * k : ℕ))
    (b : ℕ → ℂ) : Prop where
  plus : g ∈ M.plusCuspForms k 1 1
  ne_zero : g ≠ 0
  coeff_g : Abstract.HasQExp g c
  coeff_F : Abstract.HasQExp F b
  normalized : b 1 = 1
  eigen_F : ∀ p : ℕ, p.Prime → heckeTInt (2 * k) 1 1 p b = b p • b
  eigen_g : ∀ p : ℕ, p.Prime → p ≠ 2 → heckeT k 1 1 p c = b p • c

/-- **The Kohnen–Zagier formula** (Kohnen–Zagier 1981 `kohnenzagier1981`, Thm. 1 [unverified]): if $g$ and $F$ correspond
and $D$ is a fundamental discriminant with $(-1)^k D > 0$, then
$$\frac{|c(|D|)|^2}{\langle g, g\rangle} = \frac{(k-1)!}{\pi^k}\,|D|^{k-1/2}\,\frac{L(F, D, k)}{\langle F, F\rangle}.$$
$L(F, D, \cdot)$ is any entire continuation of $\sum (D/n) b(n) n^{-s}$ from $\operatorname{Re}s > k+1$. -/
@[kb "kohnenzagier1981" "Thm. 1: |c(|D|)|²/⟨g,g⟩ = (k-1)!/π^k |D|^{k-1/2} L(F,D,k)/⟨F,F⟩ [unverified]"]
structure KohnenZagier (M : MultiplierSystem) (k : ℕ) : Prop where
  formula : 1 ≤ k → ∀ (g : ℍ → ℂ) (c : ℕ → ℂ) (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ),
    Corresponds M k g c F b → ∀ D : ℤ, IsFundamentalDiscriminant D → 0 < (-1) ^ k * D →
      ∀ L : ℂ → ℂ, IsEntireLSeries (fun n ↦ (kroneckerDisc D n : ℂ) * b n) ((k : ℝ) + 1) L →
        ((‖c D.natAbs‖ ^ 2 : ℝ) : ℂ) / peterssonNormSqFour k g =
          ((k - 1).factorial / (π : ℂ) ^ k) * ((D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) *
            L k / peterssonNormSqOne k F

end ModularFormsKB.HalfIntegral
