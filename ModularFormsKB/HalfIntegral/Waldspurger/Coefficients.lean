/-
# Waldspurger 1981 on square classes, Kohnen 1985 for odd squarefree level, and the fibre dimension

Sources: Waldspurger 1981 `waldspurger1981`, Kohnen 1985 `kohnen1985`, Waldspurger 1991 `waldspurger1991` (locators
[unverified]: the papers were not checked).

**Square classes.** Squarefree $n_1, n_2 \ge 1$ are in the same class for the level $4N$ if $n_1/n_2 \in (\mathbb Q_p^\times)^2$
for every $p \mid 4N$ (`SameSquareClass`, stated as: $n_1n_2$ is a $p$-adic square).

**Waldspurger's theorem (1981, Corollaire 2 [unverified]).** For a $T(p^2)$-eigenform $g = \sum c(n)q^n \in S_{k+1/2}(4N,\chi)$,
$\chi$ quadratic, whose Shimura lift is the normalized eigen cusp form $F = \sum b(n)q^n$ of weight $2k$, and $n_1, n_2$
squarefree in one class,
$$ c(n_1)^2\,L(F,\chi_{n_2}', k)\,n_2^{k-1/2} = c(n_2)^2\,L(F,\chi_{n_1}', k)\,n_1^{k-1/2},\qquad
\chi'_n(d) = \chi(d)\Big(\frac{(-1)^kn}{d}\Big),$$
the character of the $n$-th Shimura lift (`shimuraChar`). (Waldspurger's factor $\chi(n_2/n_1)$ is $1$ here because $\chi$ is
quadratic and $n_1, n_2$ are taken prime to $4N$; this restriction makes the named input weaker than the source.)
`WaldspurgerSquareClass`. Proved: on a square class with one nonvanishing central value, $c(n)^2 = A\,L(F,\chi'_n,k)\,
n^{k-1/2}$ with one constant $A$ (`WaldspurgerSquareClass.exists_constant`), and $c(n) = 0 \iff L(F,\chi'_n,k) = 0$ once
some $c(n_0) \ne 0$ (`WaldspurgerSquareClass.coeff_eq_zero_iff`).

**Kohnen's formula (1985, Thm. 1 [unverified]).** For $N$ odd squarefree, a newform $f$ of level $N$ with Atkin–Lehner
eigenvalues $w_\ell$, and the corresponding $g$ in Kohnen's plus space of level $4N$: for fundamental $D$ with $(-1)^kD > 0$,
$$\Big(\tfrac D\ell\Big) = w_\ell\ \forall \ell\mid N:\quad \frac{|c(|D|)|^2}{\langle g,g\rangle} = 2^{\nu(N)}\frac{(k-1)!}{\pi^k}|D|^{k-1/2}
\frac{L(f,D,k)}{\langle f,f\rangle};\qquad \Big(\tfrac D\ell\Big) = -w_\ell \text{ for some } \ell:\quad c(|D|) = 0.$$
The Petersson product of level $4N$ is not yet constructed in the library, so `KohnenSquarefree` states the formula with
$\langle g,g\rangle/\langle f,f\rangle$ replaced by an unspecified positive constant $\kappa$. Proved: the ratio form on
Kohnen's discriminants (`KohnenSquarefree.ratio`) and **nonnegativity of the central values**
$L(f, D, k) \ge 0$ (`KohnenSquarefree.central_nonneg`), a famous consequence of these formulas.

**The fibre** (Waldspurger 1991). `shimuraFibre M k N χ b` is the space of $g \in S_{k+1/2}(4N,\chi)$ all of whose $t$-th
lifts ($t$ squarefree) are multiples of $b$; `WaldspurgerFibreDimension` (named) identifies the dimension of
$S \cap \mathrm{fibre}$, for a subspace $S$ (the full space, or the plus space), with `LocalData.fibreDim` of
`Packets.lean`. Proved: under Kohnen's local data the plus fibre is a line (`finrank_plusFibre_eq_one`).
-/
import ModularFormsKB.HalfIntegral.Abstract.Shimura
import ModularFormsKB.HalfIntegral.Abstract.Kohnen
import ModularFormsKB.HalfIntegral.Waldspurger.Packets
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes

namespace ModularFormsKB.HalfIntegral.Waldspurger

open Complex MatrixGroups CongruenceSubgroup
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- **Same square class at level $4N$:** $n_1 n_2$ is a square in $\mathbb Q_p$ for every prime $p \mid 4N$. -/
def SameSquareClass (N n₁ n₂ : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ∣ 4 * N → IsSquare (((n₁ * n₂ : ℕ) : ℚ_[p]))

/-- The coefficients $\chi'_n(d)\,b(d)$ of the twist $L(F, \chi'_n, s)$, $\chi'_n$ the character of the $n$-th Shimura lift. -/
noncomputable def shimuraTwistCoeff (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (n : ℕ) (b : ℕ → ℂ) (d : ℕ) : ℂ :=
  shimuraChar k N χ n d * b d

/-- **$g$ is a Hecke eigenform whose Shimura lift is the normalized eigen cusp form $F$:** $g \in S_{k+1/2}(4N,\chi)$ is
nonzero with coefficients $c$, $F$ is a weight $2k$ cusp form on $\Gamma_0(4N)$ (trivial character) with coefficients
$b$, $b(1) = 1$, $T(p)b = b(p)b$ and $T(p^2)c = b(p)c$ for $p \nmid 4N$. -/
structure LiftsTo (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (g : ℍ → ℂ) (c : ℕ → ℂ)
    (F : ℍ → ℂ) (b : ℕ → ℂ) : Prop where
  mem : g ∈ M.cuspForms k N χ
  ne_zero : g ≠ 0
  coeff_g : Abstract.HasQExp g c
  cusp_F : IsIntCuspForm (2 * k) (4 * N) 1 F
  coeff_F : Abstract.HasQExp F b
  normalized : b 1 = 1
  eigen_F : ∀ p : ℕ, p.Prime → ¬ p ∣ 4 * N → heckeTInt (2 * k) (4 * N) 1 p b = b p • b
  eigen_g : ∀ p : ℕ, p.Prime → ¬ p ∣ 4 * N → heckeT k N χ p c = b p • c

/-- **Waldspurger's theorem on square classes** (Waldspurger 1981 `waldspurger1981`, Corollaire 2 [unverified]), for
quadratic $\chi$ and $n_i$ prime to $4N$:
$c(n_1)^2 L(F,\chi'_{n_2},k)\,n_2^{k-1/2} = c(n_2)^2 L(F,\chi'_{n_1},k)\,n_1^{k-1/2}$, $L(F,\chi'_n,\cdot)$ any entire
continuation of $\sum \chi'_n(d)b(d)d^{-s}$ from $\operatorname{Re}s > k+1$. -/
@[kb "waldspurger1981" "Cor. 2: c(n₁)² L(F,χ'_{n₂},k) n₂^{k-1/2} = c(n₂)² L(F,χ'_{n₁},k) n₁^{k-1/2} on a square class [unverified]"]
structure WaldspurgerSquareClass (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop where
  ratio : 1 ≤ k → χ ^ 2 = 1 → ∀ (g : ℍ → ℂ) (c : ℕ → ℂ) (F : ℍ → ℂ) (b : ℕ → ℂ), LiftsTo M k N χ g c F b →
    ∀ n₁ n₂ : ℕ, 1 ≤ n₁ → 1 ≤ n₂ → Squarefree n₁ → Squarefree n₂ → Nat.Coprime n₁ (4 * N) →
      Nat.Coprime n₂ (4 * N) → SameSquareClass N n₁ n₂ →
      ∀ L₁ L₂ : ℂ → ℂ, IsEntireLSeries (shimuraTwistCoeff k N χ n₁ b) ((k : ℝ) + 1) L₁ →
        IsEntireLSeries (shimuraTwistCoeff k N χ n₂ b) ((k : ℝ) + 1) L₂ →
        c n₁ ^ 2 * L₂ k * ((n₂ : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) = c n₂ ^ 2 * L₁ k * ((n₁ : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ)

namespace WaldspurgerSquareClass

variable {M : MultiplierSystem} {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)}

/-- **One constant per square class:** if $L(F,\chi'_{n_0},k) \ne 0$ for one $n_0$ in the class, then
$c(n)^2 = A\,L(F,\chi'_n,k)\,n^{k-1/2}$ for all $n$ in the class, with $A = c(n_0)^2/(L(F,\chi'_{n_0},k)\,n_0^{k-1/2})$. -/
theorem exists_constant (hW : WaldspurgerSquareClass M k N χ) (hk : 1 ≤ k) (hχ : χ ^ 2 = 1)
    {g : ℍ → ℂ} {c : ℕ → ℂ} {F : ℍ → ℂ} {b : ℕ → ℂ} (hg : LiftsTo M k N χ g c F b)
    (L : ℕ → ℂ → ℂ) (hL : ∀ n, IsEntireLSeries (shimuraTwistCoeff k N χ n b) ((k : ℝ) + 1) (L n))
    {n₀ : ℕ} (h₀ : 1 ≤ n₀) (hsq₀ : Squarefree n₀) (hcop₀ : Nat.Coprime n₀ (4 * N)) (hL₀ : L n₀ k ≠ 0) :
    ∃ A : ℂ, ∀ n : ℕ, 1 ≤ n → Squarefree n → Nat.Coprime n (4 * N) → SameSquareClass N n₀ n →
      c n ^ 2 = A * L n k * ((n : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) := by
  have hP : (((n₀ : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (n₀ : ℝ) ^ ((k : ℝ) - 1 / 2) :=
      Real.rpow_pos_of_pos (by exact_mod_cast h₀) _
    exact_mod_cast this.ne'
  refine ⟨c n₀ ^ 2 / (L n₀ k * (((n₀ : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) : ℂ)), fun n hn hsq hcop hcl ↦ ?_⟩
  have h := hW.ratio hk hχ g c F b hg n₀ n h₀ hn hsq₀ hsq hcop₀ hcop hcl (L n₀) (L n) (hL n₀) (hL n)
  generalize (((n₀ : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) : ℂ) = P₀ at *
  generalize (((n : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) : ℂ) = P at *
  field_simp
  linear_combination -h

/-- **Vanishing of coefficients detects vanishing of central values** on a square class containing some $n_0$ with
$c(n_0) \ne 0$. -/
theorem coeff_eq_zero_iff (hW : WaldspurgerSquareClass M k N χ) (hk : 1 ≤ k) (hχ : χ ^ 2 = 1)
    {g : ℍ → ℂ} {c : ℕ → ℂ} {F : ℍ → ℂ} {b : ℕ → ℂ} (hg : LiftsTo M k N χ g c F b)
    (L : ℕ → ℂ → ℂ) (hL : ∀ n, IsEntireLSeries (shimuraTwistCoeff k N χ n b) ((k : ℝ) + 1) (L n))
    {n₀ : ℕ} (h₀ : 1 ≤ n₀) (hsq₀ : Squarefree n₀) (hcop₀ : Nat.Coprime n₀ (4 * N)) (hc₀ : c n₀ ≠ 0)
    (hL₀ : L n₀ k ≠ 0) {n : ℕ} (hn : 1 ≤ n) (hsq : Squarefree n) (hcop : Nat.Coprime n (4 * N))
    (hcl : SameSquareClass N n₀ n) : c n = 0 ↔ L n k = 0 := by
  have h := hW.ratio hk hχ g c F b hg n₀ n h₀ hn hsq₀ hsq hcop₀ hcop hcl (L n₀) (L n) (hL n₀) (hL n)
  have hP : (((n : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) ^ ((k : ℝ) - 1 / 2) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    exact_mod_cast this.ne'
  have hP₀ : (((n₀ : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (n₀ : ℝ) ^ ((k : ℝ) - 1 / 2) :=
      Real.rpow_pos_of_pos (by exact_mod_cast h₀) _
    exact_mod_cast this.ne'
  generalize (((n : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) : ℂ) = P at *
  generalize (((n₀ : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) : ℂ) = P₀ at *
  constructor
  · intro h0
    rw [h0] at h
    have h4 : c n₀ ^ 2 * L n k * P = 0 := by rw [h]; ring
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact (mul_eq_zero.mp h5).resolve_left (pow_ne_zero 2 hc₀)
    · exact absurd h5 hP
  · intro h0
    rw [h0] at h
    have h4 : c n ^ 2 * L n₀ k * P₀ = 0 := by rw [← h]; ring
    rcases mul_eq_zero.mp h4 with h5 | h5
    · rcases mul_eq_zero.mp h5 with h6 | h6
      · exact pow_eq_zero_iff two_ne_zero |>.mp h6
      · exact absurd h6 hL₀
    · exact absurd h5 hP₀

end WaldspurgerSquareClass

/-! ## Kohnen 1985: odd squarefree level -/

/-- **Kohnen's formula for odd squarefree level** (Kohnen 1985 `kohnen1985`, Thm. 1 and its corollary [unverified]),
with the Petersson quotient $\langle g, g\rangle/\langle f,f\rangle$ abstracted to a positive constant $\kappa$ (the level $4N$
Petersson product is not yet constructed). `w ℓ` is the Atkin–Lehner eigenvalue of $f$ at $\ell \mid N$, `c` the
coefficients of $g$, and `L D` an entire continuation of $L(f, D, s) = \sum (D/n)b(n)n^{-s}$. -/
@[kb "kohnen1985" "Thm. 1: |c(|D|)|²/⟨g,g⟩ = 2^ν(N) (k-1)!/π^k |D|^{k-1/2} L(f,D,k)/⟨f,f⟩ if (D/ℓ) = w_ℓ ∀ℓ|N; c(|D|) = 0 if (D/ℓ) = -w_ℓ for some ℓ [unverified]"]
structure KohnenSquarefree (k N : ℕ) (w : N.primeFactors → ℤˣ) (c : ℕ → ℂ) (b : ℕ → ℂ) (L : ℤ → ℂ → ℂ) : Prop where
  entire : ∀ D : ℤ, IsEntireLSeries (fun n ↦ (kroneckerDisc D n : ℂ) * b n) ((k : ℝ) + 1) (L D)
  formula : ∃ κ : ℝ, 0 < κ ∧ ∀ D : ℤ, IsFundamentalDiscriminant D → 0 < (-1) ^ k * D →
    (∀ ℓ : N.primeFactors, kroneckerDisc D ℓ = w ℓ) →
      ((‖c D.natAbs‖ ^ 2 : ℝ) : ℂ) = (κ : ℂ) * 2 ^ N.primeFactors.card * ((k - 1).factorial / (π : ℂ) ^ k) *
        ((D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) * L D k
  vanish : ∀ D : ℤ, IsFundamentalDiscriminant D → 0 < (-1) ^ k * D →
    (∃ ℓ : N.primeFactors, kroneckerDisc D ℓ = -(w ℓ : ℤ)) → c D.natAbs = 0

namespace KohnenSquarefree

variable {k N : ℕ} {w : N.primeFactors → ℤˣ} {c b : ℕ → ℂ} {L : ℤ → ℂ → ℂ}

/-- Kohnen's formula with the constants collected: `‖c‖² = κ' |D|^(k-1/2) L`, `κ' > 0` real. -/
private theorem formula_aux (h : KohnenSquarefree k N w c b L) :
    ∃ κ' : ℝ, 0 < κ' ∧ ∀ D : ℤ, IsFundamentalDiscriminant D → 0 < (-1) ^ k * D →
      (∀ ℓ : N.primeFactors, kroneckerDisc D ℓ = w ℓ) →
      ((‖c D.natAbs‖ ^ 2 : ℝ) : ℂ) = (κ' : ℂ) * ((D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) * L D k := by
  obtain ⟨κ, hκ, hf⟩ := h.formula
  refine ⟨κ * 2 ^ N.primeFactors.card * (((k - 1).factorial : ℝ) / π ^ k), by positivity, ?_⟩
  intro D hD hs hw
  rw [hf D hD hs hw]
  push_cast
  ring

/-- **Nonnegativity of central values:** $L(f, D, k)$ is real and $\ge 0$ for every fundamental $D$ satisfying Kohnen's
condition. -/
theorem central_nonneg (h : KohnenSquarefree k N w c b L) {D : ℤ} (hD : IsFundamentalDiscriminant D)
    (hsign : 0 < (-1) ^ k * D) (hw : ∀ ℓ : N.primeFactors, kroneckerDisc D ℓ = w ℓ) :
    (L D k).im = 0 ∧ 0 ≤ (L D k).re := by
  obtain ⟨κ', hκ', hf⟩ := formula_aux h
  have hP : (0 : ℝ) < (D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) := by
    refine Real.rpow_pos_of_pos ?_ _
    exact_mod_cast Int.natAbs_pos.mpr (fun h0 ↦ by simp [h0] at hsign)
  have key : L D k = (((‖c D.natAbs‖ ^ 2) / (κ' * (D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2)) : ℝ) : ℂ) := by
    have h1 := hf D hD hsign hw
    have h2 : (κ' * (D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) ≠ 0 := by positivity
    have h3 : ((κ' * (D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2
    rw [Complex.ofReal_div, Complex.ofReal_mul, eq_div_iff (by rw [Complex.ofReal_mul] at h3; exact h3), h1]
    ring
  rw [key]
  constructor
  · exact Complex.ofReal_im _
  · rw [Complex.ofReal_re]; positivity

/-- **Ratio form** on Kohnen's discriminants: $|c(|D_1|)|^2|D_2|^{k-1/2}L(f,D_2,k) = |c(|D_2|)|^2|D_1|^{k-1/2}L(f,D_1,k)$. -/
theorem ratio (h : KohnenSquarefree k N w c b L) {D₁ D₂ : ℤ} (hD₁ : IsFundamentalDiscriminant D₁)
    (hD₂ : IsFundamentalDiscriminant D₂) (hs₁ : 0 < (-1) ^ k * D₁) (hs₂ : 0 < (-1) ^ k * D₂)
    (hw₁ : ∀ ℓ : N.primeFactors, kroneckerDisc D₁ ℓ = w ℓ) (hw₂ : ∀ ℓ : N.primeFactors, kroneckerDisc D₂ ℓ = w ℓ) :
    ((‖c D₁.natAbs‖ ^ 2 : ℝ) : ℂ) * ((D₂.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) * L D₂ k =
      ((‖c D₂.natAbs‖ ^ 2 : ℝ) : ℂ) * ((D₁.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) * L D₁ k := by
  obtain ⟨κ', -, hf⟩ := formula_aux h
  rw [hf D₁ hD₁ hs₁ hw₁, hf D₂ hD₂ hs₂ hw₂]
  ring

/-- **Nonvanishing criterion:** for $D$ satisfying Kohnen's condition, $c(|D|) \ne 0 \iff L(f, D, k) \ne 0$. -/
theorem coeff_ne_zero_iff (h : KohnenSquarefree k N w c b L) (hk : 1 ≤ k) {D : ℤ} (hD : IsFundamentalDiscriminant D)
    (hsign : 0 < (-1) ^ k * D) (hw : ∀ ℓ : N.primeFactors, kroneckerDisc D ℓ = w ℓ) :
    c D.natAbs ≠ 0 ↔ L D k ≠ 0 := by
  obtain ⟨κ', hκ', hf⟩ := formula_aux h
  have hP : (0 : ℝ) < (D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) := by
    refine Real.rpow_pos_of_pos ?_ _
    exact_mod_cast Int.natAbs_pos.mpr (fun h0 ↦ by simp [h0] at hsign)
  have h1 := hf D hD hsign hw
  have h3 : (κ' : ℂ) * (((D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hκ'.ne') (by exact_mod_cast hP.ne')
  constructor
  · intro hc hL
    rw [hL, mul_zero] at h1
    have : ‖c D.natAbs‖ = 0 := by
      have : (‖c D.natAbs‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h1
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    exact hc (norm_eq_zero.mp this)
  · intro hL hc
    have h4 : ((κ' : ℂ) * (((D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) : ℂ)) * L D k = 0 := by
      rw [← h1, hc]; simp
    exact (mul_eq_zero.mp h4).elim h3 hL

end KohnenSquarefree

/-! ## The fibre of the Shimura correspondence -/

private theorem shimuraCoeff_add (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ) (a a' : ℕ → ℂ) (n : ℕ) :
    shimuraCoeff k N χ t (a + a') n = shimuraCoeff k N χ t a n + shimuraCoeff k N χ t a' n := by
  simp only [shimuraCoeff, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

private theorem shimuraCoeff_smul' (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ) (α : ℂ) (a : ℕ → ℂ)
    (n : ℕ) : shimuraCoeff k N χ t (α • a) n = α * shimuraCoeff k N χ t a n := by
  simp only [shimuraCoeff, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **The fibre over $b$:** forms $g \in S_{k+1/2}(4N,\chi)$ with a $q$-expansion $c$ such that every $t$-th Shimura lift
($t$ squarefree) is a multiple of $b$ on $n \ge 1$. -/
def shimuraFibre (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (b : ℕ → ℂ) :
    Submodule ℂ (ℍ → ℂ) where
  carrier := {g | g ∈ M.cuspForms k N χ ∧ ∃ c : ℕ → ℂ, Abstract.HasQExp g c ∧
    ∀ t : ℕ, Squarefree t → ∃ α : ℂ, ∀ n, 1 ≤ n → shimuraCoeff k N χ t c n = α * b n}
  add_mem' := by
    rintro f g ⟨hf, c, hc, hα⟩ ⟨hg, c', hc', hα'⟩
    refine ⟨add_mem hf hg, c + c', fun τ ↦ ?_, fun t ht ↦ ?_⟩
    · simpa [add_mul] using (hc τ).add (hc' τ)
    · obtain ⟨α, hα1⟩ := hα t ht
      obtain ⟨α', hα1'⟩ := hα' t ht
      refine ⟨α + α', fun n hn ↦ ?_⟩
      rw [shimuraCoeff_add, hα1 n hn, hα1' n hn]
      ring
  zero_mem' := by
    refine ⟨zero_mem _, 0, fun τ ↦ ?_, fun t ht ↦ ⟨0, fun n hn ↦ ?_⟩⟩
    · simpa using hasSum_zero
    · simp [shimuraCoeff]
  smul_mem' := by
    rintro a f ⟨hf, c, hc, hα⟩
    refine ⟨Submodule.smul_mem _ a hf, a • c, fun τ ↦ ?_, fun t ht ↦ ?_⟩
    · simpa [mul_assoc] using (hc τ).mul_left a
    · obtain ⟨α, hα1⟩ := hα t ht
      refine ⟨a * α, fun n hn ↦ ?_⟩
      rw [shimuraCoeff_smul', hα1 n hn]
      ring

/-- **Waldspurger's dimension formula for the fibre** (Waldspurger 1991 `waldspurger1991` [unverified]; local
multiplicity one and the local fixed-vector dimensions enter through the local data `D`): the forms in the subspace $S$
(the full space, or Kohnen's plus space) whose Shimura lifts are multiples of $b$ form a space of dimension
$\sum_{\varepsilon\ \mathrm{admissible}}\prod_v d_v(\varepsilon_v)$. -/
@[kb "waldspurger1991" "dimension of the forms with Shimura lift f = Σ over admissible sign patterns of local fixed-vector dimensions [unverified]"]
structure WaldspurgerFibreDimension {ι : Type*} [Fintype ι] [DecidableEq ι] (M : MultiplierSystem) (k N : ℕ)
    (χ : DirichletCharacter ℂ (4 * N)) (b : ℕ → ℂ) (S : Submodule ℂ (ℍ → ℂ)) (D : LocalData ι) : Prop where
  finrank_eq : Module.finrank ℂ ↥(shimuraFibre M k N χ b ⊓ S) = D.fibreDim

/-- **The plus fibre is a line** (Kohnen 1985's multiplicity one in the plus space, recovered from Waldspurger's formula
with Kohnen's local data: a line in $\sigma_\ell^{w_\ell}$, nothing in $\sigma_\ell^{-w_\ell}$). -/
theorem finrank_plusFibre_eq_one {M : MultiplierSystem} {k N : ℕ} {b : ℕ → ℂ} {w : N.primeFactors → ℤˣ}
    (h : WaldspurgerFibreDimension M k N 1 b (M.plusCuspForms k N 1)
      (classicalLocal k N w (fun p ε ↦ if ε = w p then 1 else 0))) :
    Module.finrank ℂ ↥(shimuraFibre M k N 1 b ⊓ M.plusCuspForms k N 1) = 1 := by
  rw [h.finrank_eq, kohnen_fibreDim]

end ModularFormsKB.HalfIntegral.Waldspurger
