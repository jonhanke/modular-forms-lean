/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.Restated
import ModularFormsKB.HalfIntegral.SerreStark
import ModularFormsKB.HalfIntegral.Abstract.Waldspurger
import ModularFormsKB.HalfIntegral.Abstract.PeterssonDefinite
import ModularFormsKB.HalfIntegral.Abstract.ThetaInstance
import ModularFormsKB.HalfIntegral.Abstract.KohnenZagierReduction

/-!
# Shimura's theorem in weight $3/2$, and cross-checks of the Waldspurger statements

**Shimura's theorem in weight $3/2$.** `ShimuraTheorem` (Shimura 1973) is stated for $k \ge 2$. In weight $3/2$ ($k = 1$) the lift of a cusp form
is a cusp form only on the orthogonal complement of the unary theta series $\theta_{\psi,t}$ of weight $3/2$ (Shimura
1973 `shimura1973`, Main Theorem for $\lambda = 1$; the level by Cipra 1983 `cipra1983` [unverified]).
`ShimuraTheoremThreeHalves` states this, with orthogonality for `peterssonLevel`. Consistency:
- `ShimuraTheoremThreeHalves.liftsTo_char`: for quadratic $\chi$ the lift has trivial character, as `LiftsTo` (the
  hypothesis of `WaldspurgerSquareClassFull` at $k = 1$) requires;
- Tunnell's forms are of level $128 = 4\cdot 32$, $k = 1$, so `ShimuraTheoremThreeHalves thetaMultiplierSystem 32 χ` is
  the statement that their lifts are weight 2 cusp forms of level $128$; `TunnellEigenforms` names the lifts directly
  (`Waldspurger/CongruentCurves/Criterion.lean`), so no theorem here depends on row 36.

**Row 39.** Kohnen's formula for odd squarefree level (`KohnenSquarefree`, Kohnen 1985) at $N = 1$ is the
Kohnen–Zagier formula with $\kappa = \langle g,g\rangle/\langle F,F\rangle$. Proved:
- `kohnenSquarefree_one_of_kohnenZagier`: `KohnenZagier` implies `KohnenSquarefree k 1` for every corresponding pair,
  with $2^{\nu(1)} = 1$ and the same constant $\frac{(k-1)!}{\pi^k}|D|^{k-1/2}$: the two statements agree at $N = 1$;
- `KohnenSquarefree.ratio_one`: `KohnenSquarefree k 1` gives the ratio form of `WaldspurgerPlus` with $|c|^2$ in
  place of $c^2$ (equal for real coefficients, `plusRealCoefficients_theta`).

The cross-check of `WaldspurgerSquareClassFull` at level $4$ against `WaldspurgerPlus` is reduced to the statement
`LevelFourCrossCheck` (loose end LE-MF-0313): `WaldspurgerSquareClassFull` uses the twist by $\chi'_n(d) = \chi(d)\left(\frac{(-1)^kn}d\right)$,
which vanishes at even $d$, while `WaldspurgerPlus` uses the Kronecker symbol $\left(\frac Dd\right)$, $D = (-1)^kn$. The two
$L$-functions differ by the Euler factor at $2$, which depends on $D \bmod 8$; on one $2$-adic square class it is the
same for $n_1$ and $n_2$, so the two ratios agree. Not proved here: the Euler factor identity for the continuations,
the $2$-adic square class of odd $n_1 n_2$ as $n_1 \equiv n_2 \bmod 8$, and the passage between level one forms and
`LiftsTo` at level $4$.
-/

namespace ModularFormsKB.HalfIntegral.Waldspurger

open Complex MatrixGroups CongruenceSubgroup ModularForm
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-! ## Row 36 -/

/-- **Shimura's theorem in weight $3/2$** (Shimura 1973 `shimura1973`, Main Theorem for $\lambda = 1$; Cipra 1983
`cipra1983` for the level [unverified]): for squarefree $t \ge 1$ and $f \in S_{3/2}(4N, \chi)$ with $q$-expansion $a$,
orthogonal (for `peterssonLevel`) to every unary theta series $\theta_{\psi,t'}$ of weight $3/2$ in the space
($(\psi, t') \in \Omega_1(4N, \chi)$, `unaryIndex 1 N χ`), there is a cusp form $F \in S_2(4N, \chi^2)$ with $n$-th
coefficient $A_t(n)$ = `shimuraCoeff 1 N χ t a n` for $n \ge 1$. Loose end LE-MF-0258 (now a statement). -/
@[kb "shimura1973" "Main Theorem, λ = 1: the t-th lift of f ∈ S_{3/2}(4N, χ) orthogonal to the unary theta series is a weight 2 cusp form [unverified]"]
structure ShimuraTheoremThreeHalves (M : MultiplierSystem) (N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop where
  lift : ∀ t : ℕ, 1 ≤ t → Squarefree t → ∀ f ∈ M.cuspForms 1 N χ,
    (∀ p ∈ unaryIndex 1 N χ, peterssonLevel 1 N (unaryThetaOf p) f = 0) → ∀ a : ℕ → ℂ, Abstract.HasQExp f a →
      ∃ F : ℍ → ℂ, IsIntCuspForm 2 (4 * N) (χ ^ 2) F ∧
        ∃ c : ℕ → ℂ, Abstract.HasQExp F c ∧ ∀ n, 1 ≤ n → c n = shimuraCoeff 1 N χ t a n

/-- **For quadratic $\chi$ the weight $3/2$ lift has trivial character**, the form of `LiftsTo` at $k = 1$. -/
theorem ShimuraTheoremThreeHalves.liftsTo_char {M : MultiplierSystem} {N : ℕ} {χ : DirichletCharacter ℂ (4 * N)}
    (h : ShimuraTheoremThreeHalves M N χ) (hχ : χ ^ 2 = 1) {t : ℕ} (ht : 1 ≤ t) (hts : Squarefree t)
    {f : ℍ → ℂ} (hf : f ∈ M.cuspForms 1 N χ)
    (horth : ∀ p ∈ unaryIndex 1 N χ, peterssonLevel 1 N (unaryThetaOf p) f = 0) {a : ℕ → ℂ}
    (ha : Abstract.HasQExp f a) :
    ∃ F : ℍ → ℂ, IsIntCuspForm (2 * 1) (4 * N) 1 F ∧
      ∃ c : ℕ → ℂ, Abstract.HasQExp F c ∧ ∀ n, 1 ≤ n → c n = shimuraCoeff 1 N χ t a n := by
  obtain ⟨F, hF, c, hc, hcn⟩ := h.lift t ht hts f hf horth a ha
  exact ⟨F, by simpa [hχ] using hF, c, hc, hcn⟩

/-! ## Row 39 -/

/-- The prime factors of $1$: there are none, so `KohnenSquarefree k 1` has no local conditions. -/
theorem primeFactors_one_isEmpty : IsEmpty ((1 : ℕ).primeFactors) :=
  ⟨fun ⟨x, hx⟩ ↦ by simp at hx⟩

/-- **`KohnenZagier` implies `KohnenSquarefree` at $N = 1$**, with $\kappa = \langle g, g\rangle/\langle F, F\rangle$: the
constants $2^{\nu(N)}\frac{(k-1)!}{\pi^k}|D|^{k-1/2}$ of Kohnen 1985 at $N = 1$ are those of Kohnen–Zagier 1981. -/
theorem kohnenSquarefree_one_of_kohnenZagier {k : ℕ} (hk : 1 ≤ k)
    (hKZ : KohnenZagier thetaMultiplierSystem k) {g : ℍ → ℂ} {c : ℕ → ℂ} {F : CuspForm 𝒮ℒ (2 * k : ℕ)}
    {b : ℕ → ℂ} (hgF : Corresponds thetaMultiplierSystem k g c F b) (w : (1 : ℕ).primeFactors → ℤˣ)
    (L : ℤ → ℂ → ℂ) (hL : ∀ D, IsEntireLSeries (fun n ↦ (kroneckerDisc D n : ℂ) * b n) ((k : ℝ) + 1) (L D)) :
    KohnenSquarefree k 1 w c b L := by
  have hNg := (peterssonDefinite thetaMultiplierSystem k).four g hgF.plus hgF.ne_zero
  have hNF := (peterssonDefinite thetaMultiplierSystem k).one F
    (cuspForm_ne_zero_of_coeff_one F hgF.coeff_F hgF.normalized)
  obtain ⟨hg0, hgim⟩ := peterssonNormSqFour_nonneg k g
  obtain ⟨hF0, hFim⟩ := peterssonNormSqOne_nonneg k F
  set ng := (peterssonNormSqFour k g).re
  set nf := (peterssonNormSqOne k F).re
  have hng : peterssonNormSqFour k g = (ng : ℂ) := Complex.ext (by simp [ng]) (by simp [hgim])
  have hnf : peterssonNormSqOne k F = (nf : ℂ) := Complex.ext (by simp [nf]) (by simp [hFim])
  have hng0 : ng ≠ 0 := fun h ↦ hNg (by rw [hng, h, ofReal_zero])
  have hnf0 : nf ≠ 0 := fun h ↦ hNF (by rw [hnf, h, ofReal_zero])
  refine ⟨hL, ⟨ng / nf, div_pos (lt_of_le_of_ne hg0 (Ne.symm hng0)) (lt_of_le_of_ne hF0 (Ne.symm hnf0)),
    fun D hD hs _ ↦ ?_⟩, fun D _ _ ⟨ℓ, _⟩ ↦ (primeFactors_one_isEmpty.false ℓ).elim⟩
  have key := hKZ.formula hk g c F b hgF D hD hs (L D) (hL D)
  rw [hng, hnf] at key
  have hng0' : (ng : ℂ) ≠ 0 := ofReal_ne_zero.2 hng0
  have hnf0' : (nf : ℂ) ≠ 0 := ofReal_ne_zero.2 hnf0
  rw [div_eq_div_iff hng0' hnf0'] at key
  simp only [Nat.primeFactors_one, Finset.card_empty, pow_zero, mul_one, Complex.ofReal_div]
  calc ((‖c D.natAbs‖ ^ 2 : ℝ) : ℂ) = ((‖c D.natAbs‖ ^ 2 : ℝ) : ℂ) * nf / nf :=
        (mul_div_cancel_right₀ _ hnf0').symm
    _ = _ := by rw [key]; ring

/-- **`KohnenSquarefree` at $N = 1$ gives the ratio form of `WaldspurgerPlus`**, with $|c|^2$ for $c^2$. -/
theorem KohnenSquarefree.ratio_one {k : ℕ} {w : (1 : ℕ).primeFactors → ℤˣ} {c b : ℕ → ℂ} {L : ℤ → ℂ → ℂ}
    (h : KohnenSquarefree k 1 w c b L) {D₁ D₂ : ℤ} (hD₁ : IsFundamentalDiscriminant D₁)
    (hD₂ : IsFundamentalDiscriminant D₂) (hs₁ : 0 < (-1) ^ k * D₁) (hs₂ : 0 < (-1) ^ k * D₂) :
    ((‖c D₁.natAbs‖ ^ 2 : ℝ) : ℂ) * ((D₂.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) * L D₂ k =
      ((‖c D₂.natAbs‖ ^ 2 : ℝ) : ℂ) * ((D₁.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) * L D₁ k := by
  obtain ⟨κ, -, hf⟩ := h.formula
  have none : ∀ ℓ : (1 : ℕ).primeFactors, ∀ D : ℤ, kroneckerDisc D ℓ = w ℓ :=
    fun ℓ ↦ (primeFactors_one_isEmpty.false ℓ).elim
  rw [hf D₁ hD₁ hs₁ (fun ℓ ↦ none ℓ D₁), hf D₂ hD₂ hs₂ (fun ℓ ↦ none ℓ D₂)]
  ring

/-- **The level-four cross-check** (row 39, reduced; loose end LE-MF-0313): `WaldspurgerPlus` for the theta multiplier
implies `WaldspurgerSquareClassFull`'s ratio for corresponding level one pairs and odd squarefree $n_1, n_2$ with
$(-1)^kn_i \equiv 1 \bmod 4$ in one $2$-adic square class. A statement to be proved, not an input: the module docstring
lists what is missing. -/
def LevelFourCrossCheck (k : ℕ) : Prop :=
  WaldspurgerPlus thetaMultiplierSystem k → 1 ≤ k →
    ∀ (g : ℍ → ℂ) (c : ℕ → ℂ) (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ),
      Corresponds thetaMultiplierSystem k g c F b →
      ∀ n₁ n₂ : ℕ, Odd n₁ → Odd n₂ → Squarefree n₁ → Squarefree n₂ →
        ((-1) ^ k * n₁ : ℤ) % 4 = 1 → ((-1) ^ k * n₂ : ℤ) % 4 = 1 → SameSquareClass 1 n₁ n₂ →
        ∀ L₁ L₂ : ℂ → ℂ, IsEntireLSeries (shimuraTwistCoeff k 1 1 n₁ b) ((k : ℝ) + 1) L₁ →
          IsEntireLSeries (shimuraTwistCoeff k 1 1 n₂ b) ((k : ℝ) + 1) L₂ →
          c n₁ ^ 2 * L₂ k * squareClassFactor 1 1 n₁ n₂ * ((n₂ : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) =
            c n₂ ^ 2 * L₁ k * ((n₁ : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ)

end ModularFormsKB.HalfIntegral.Waldspurger
