/-
# Coefficient bounds beyond Hecke's: named statements

Hecke's bound $a(n) = O(n^{(2k+1)/4})$ for $f \in S_{k+1/2}(4N,\chi)$ is the named input
`HeckeCoeffBound` (`Abstract/ShimuraWeil.lean`), **proved** for $N \ge 1$ (`heckeCoeffBound`, `HeckeBound.lean`). This file
records the stronger bounds as **named statements only**. They are neither proved nor assumed anywhere in the knowledge
base (a design decision: Deligne's bound is not used and these are not proved).

1. `DeligneBound` (integral weight, Deligne 1974 `deligne1974`): $|a(p)| \le 2p^{(w-1)/2}$ for $p \nmid L$, and
   $a(n) = O(n^{(w-1)/2+\varepsilon})$, for normalized eigenforms of weight $w \ge 2$ on $\Gamma_0(L)$ with character.
2. `HalfIntRamanujan` (half-integral weight, conjectural): $a(t) = O(t^{k/2-1/4+\varepsilon})$ for squarefree $t$.
3. `IwaniecCoeffBound` ($k \ge 2$, Iwaniec 1987 `iwaniec1987`) and `DukeCoeffBound` ($k = 1$, Duke 1988 `duke1988`):
   $a(t) = O(t^{k/2-1/28+\varepsilon})$ for squarefree $t$ (convexity breaking).

**Exponents.** With $w = k + \tfrac12$: Hecke's bound is $n^{w/2} = n^{k/2+1/4}$; the Petersson formula with Weil's bound
for the Salié sums gives $t^{w/2-1/4+\varepsilon} = t^{k/2+\varepsilon}$ on squarefree $t$ (the convexity bound for the
twisted $L$-values through Waldspurger's formula); Iwaniec and Duke gain $1/28$ over it, $t^{w/2-2/7+\varepsilon} =
t^{k/2-1/28+\varepsilon}$; the conjecture is $t^{(w-1)/2+\varepsilon} = t^{k/2-1/4+\varepsilon}$. So
$k/2 - 1/4 < k/2 - 1/28 < k/2 + 1/4$, and the proved implications below are
`HalfIntRamanujan` $\Rightarrow$ `IwaniecCoeffBound`, `DukeCoeffBound` $\Rightarrow$ Hecke's bound on squarefree $t$.

**Proved here** (sanity checks): `iwaniecCoeffBound_of_ramanujan`, `dukeCoeffBound_of_ramanujan`,
`heckeCoeffBoundSqfree_of_iwaniec`, `heckeCoeffBoundSqfree_of_duke`, `heckeCoeffBoundSqfree_of_heckeCoeffBound`.

All half-integral statements are relative to an abstract multiplier system `M`; they are meant for the theta multiplier.
-/
import ModularFormsKB.HalfIntegral.Abstract.ShimuraWeil

namespace ModularFormsKB.HalfIntegral

open Complex

local notation "ℍ" => UpperHalfPlane

/-! ## Integral weight: Deligne -/

/-- **Normalized Hecke eigenform of integral weight $w$ on $\Gamma_0(L)$ with character $\psi$.**

Fields:
- `cusp`: $F \in S_w(\Gamma_0(L),\psi)$ (`IsIntCuspForm`);
- `qexp`: $F = \sum_{n\ge0}c(n)q^n$;
- `one`: $c(1) = 1$;
- `eigen`: for every prime $p$ the coefficients are an eigenvector of $T(p)$ in Shimura's coefficient form
  (`heckeTInt`: $c(pn) + \psi(p)p^{w-1}c(n/p)$), with eigenvalue $c(p)$ (forced by $c(1) = 1$). For $p \mid L$,
  $\psi(p) = 0$ and this is $U(p)$.

Mathlib has no theory of newforms, so "newform" (the hypothesis of the sources) is replaced by this predicate; every
normalized newform of level $L$ satisfies it. It also admits some oldforms (eigenvectors of every $U(p)$, $p \mid L$, in
the old space, e.g. $g(\tau) - a_g(p)g(p\tau) + \psi(p)p^{w-1}g(p^2\tau)$); for them `DeligneBound` still holds, since their
$T(p)$-eigenvalues, $p \nmid L$, are those of a newform and their $U(p)$-eigenvalues have absolute value at most
$p^{(w-1)/2}$ (Atkin–Lehner 1970, Li 1975 [unverified]). -/
structure IsNormalizedIntEigenform (w L : ℕ) (ψ : DirichletCharacter ℂ L) (F : ℍ → ℂ) (c : ℕ → ℂ) : Prop where
  cusp : IsIntCuspForm w L ψ F
  qexp : Abstract.HasQExp F c
  one : c 1 = 1
  eigen : ∀ p : ℕ, p.Prime → ∀ n : ℕ, 1 ≤ n → heckeTInt w L ψ p c n = c p * c n

/-- **Deligne's bound (the Ramanujan–Petersson conjecture in integral weight)** (Deligne 1974 `deligne1974`, Thm. 8.2
[unverified]; Ramanujan's $\tau(n)$ is $w = 12$, $L = 1$). For $w \ge 2$ and a normalized eigenform
$F = \sum c(n)q^n \in S_w(\Gamma_0(L),\psi)$ (`IsNormalizedIntEigenform`):

Fields:
- `prime`: $|c(p)| \le 2p^{(w-1)/2}$ for every prime $p \nmid L$;
- `growth`: for every $\varepsilon > 0$ there is $C$ with $|c(n)| \le Cn^{(w-1)/2+\varepsilon}$ for all $n \ge 1$ (from the
  sharper $|c(n)| \le d(n)n^{(w-1)/2}$, $d$ the number of divisors, and $d(n) = O(n^{\varepsilon})$).

**Named statement only; not proved and not used in this knowledge base.**

**Relation to a decomposition statement for weight $2$.** A companion statement (outside this library) is a
different statement: weight $2$, Mathlib's `CuspForm (Gamma1 N) 2` with character, and a *decomposition* of every cusp
form into normalized forms with $|b_i(m)| \le d(m)m^{1/2}$. It combines Deligne's bound (for $w = 2$ already
Eichler–Shimura–Igusa) with the newform decomposition (Atkin–Lehner, Li), and neither statement implies the other
without newform theory, so it is not reused here. -/
@[kb "deligne1974" "Thm. 8.2: |a(p)| ≤ 2p^{(k-1)/2} for normalized newforms of weight k ≥ 2, p ∤ N [unverified]"]
structure DeligneBound (w L : ℕ) (ψ : DirichletCharacter ℂ L) : Prop where
  prime : 2 ≤ w → ∀ F : ℍ → ℂ, ∀ c : ℕ → ℂ, IsNormalizedIntEigenform w L ψ F c →
    ∀ p : ℕ, p.Prime → ¬ p ∣ L → ‖c p‖ ≤ 2 * (p : ℝ) ^ (((w : ℝ) - 1) / 2)
  growth : 2 ≤ w → ∀ F : ℍ → ℂ, ∀ c : ℕ → ℂ, IsNormalizedIntEigenform w L ψ F c →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ‖c n‖ ≤ C * (n : ℝ) ^ (((w : ℝ) - 1) / 2 + ε)

/-! ## Half-integral weight, on squarefree indices -/

/-- **A coefficient bound with exponent $e$ on squarefree indices:** every $f = \sum a(n)q^n \in S_{k+1/2}(4N,\chi)$ satisfies,
for every $\varepsilon > 0$, $|a(t)| \le Ct^{e+\varepsilon}$ for all squarefree $t \ge 1$, with $C$ depending on
$f$ and $\varepsilon$. -/
def SqfreeCoeffBound (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (e : ℝ) : Prop :=
  ∀ f ∈ M.cuspForms k N χ, ∀ a : ℕ → ℂ, Abstract.HasQExp f a →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℕ, 1 ≤ t → Squarefree t → ‖a t‖ ≤ C * (t : ℝ) ^ (e + ε)

/-- A squarefree bound with exponent $e$ gives one with every larger exponent $e'$. -/
theorem SqfreeCoeffBound.mono {M : MultiplierSystem} {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)} {e e' : ℝ}
    (h : SqfreeCoeffBound M k N χ e) (hee : e ≤ e') : SqfreeCoeffBound M k N χ e' := by
  intro f hf a ha ε hε
  obtain ⟨C, hC⟩ := h f hf a ha ε hε
  refine ⟨max C 0, fun t ht hsq ↦ (hC t ht hsq).trans ?_⟩
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  exact mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith))
    (by positivity) (le_max_right _ _)

/-- **The Ramanujan-type conjecture in half-integral weight** (open; Iwaniec 1997 `iwaniec1997`, §5 [unverified];
Kohnen–Zagier 1981 `kohnenzagier1981` [unverified]): for $k \ge 1$, every $f \in S_{k+1/2}(4N,\chi)$ satisfies
$a(t) = O(t^{k/2-1/4+\varepsilon})$ for every $\varepsilon > 0$ on squarefree $t$ (`SqfreeCoeffBound` with
$e = k/2 - 1/4 = (w-1)/2$, $w = k+\tfrac12$). Through Waldspurger's formula $a(t)^2 \sim L(\tfrac12, F\otimes\chi_t)\,
t^{k-1/2}$ it is equivalent to the Lindelöf hypothesis for the twisted $L$-values in the $t$-aspect.

Field: `bound`: for $k \ge 1$, `SqfreeCoeffBound M k N χ (k/2 - 1/4)`.

*Why squarefree $t$ only.* Along a square class $n = tm^2$ the coefficients are governed by the Shimura lift
(`shimuraCoeff`), not by the conjecture: for a $T(p^2)$-eigenform and $m$ prime to $4N$,
$a(tm^2) = a(t)\sum_{d\mid m}\mu(d)\chi_t(d)d^{k-1}A(m/d)$ with $A$ the eigenvalues of the weight $2k$ lift, so the growth in
$m$ is that of an integral weight $2k$ form, $m^{k-1/2+o(1)}$ by Deligne, and the content of the conjecture is the
$t$-aspect, $a(t)$. For general $n$ the bound can fail: in weight $3/2$ the unary theta series
$\sum_m\psi(m)m\,q^{tm^2}$ is a cusp form with $|a(tm^2)| = m = t^{-1/2}(tm^2)^{1/2}$, exponent $1/2 > k/2 - 1/4 = 1/4$ in
$n = tm^2$.

*Weight $3/2$ ($k = 1$).* For this reason the conjecture for general $n$ is stated on the orthogonal complement of the unary
theta series. On squarefree indices no restriction is needed: such a series has at most one nonzero squarefree coefficient
(at $t$, if $t$ is squarefree), and a finite sum of them has finitely many, so it satisfies every bound of this shape. -/
@[kb "iwaniec1997" "§5: conjectured bound a(t) ≪ t^{(w-1)/2+ε} for squarefree t, weight w = k + 1/2 [unverified]"]
structure HalfIntRamanujan (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop where
  bound : 1 ≤ k → SqfreeCoeffBound M k N χ ((k : ℝ) / 2 - 1 / 4)

/-- **Iwaniec's convexity-breaking bound** (Iwaniec 1987 `iwaniec1987`, Theorem 1 [unverified]): for $k \ge 2$ (weight
$w = k + \tfrac12 \ge \tfrac52$), every $f \in S_{k+1/2}(4N,\chi)$ satisfies $a(t) = O(t^{k/2-1/28+\varepsilon})$ on
squarefree $t$, i.e. $t^{w/2-2/7+\varepsilon}$ in Iwaniec's normalization (weight $w$): a saving of $1/28$ over the
convexity exponent $w/2 - 1/4 = k/2$.

Field: `bound`: for $k \ge 2$, `SqfreeCoeffBound M k N χ (k/2 - 1/28)`.

**Named statement only; not proved and not used.** *Note:* an earlier draft gave the exponent as
$k/2 - 1/4 - 1/28$, which is below the conjectured $k/2 - 1/4$; the exponent here is $w/2 - 2/7$ as recalled from the paper
(locator [unverified], the paper was not available on the machine that wrote this). -/
@[kb "iwaniec1987" "Theorem 1: a(n) ≪ n^{w/2-2/7+ε} for squarefree n, weight w ≥ 5/2 [unverified]"]
structure IwaniecCoeffBound (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop where
  bound : 2 ≤ k → SqfreeCoeffBound M k N χ ((k : ℝ) / 2 - 1 / 28)

/-- **Duke's convexity-breaking bound in weight $3/2$** (Duke 1988 `duke1988`, Theorem 5 [unverified]; extending
Iwaniec 1987 to weight $3/2$): for $k = 1$, every $f \in S_{3/2}(4N,\chi)$ satisfies $a(t) = O(t^{1/2-1/28+\varepsilon})
= O(t^{13/28+\varepsilon})$ on squarefree $t$ (exponent $w/2 - 2/7$, $w = 3/2$).

Field: `bound`: for $k = 1$, `SqfreeCoeffBound M k N χ (k/2 - 1/28)`.

**Named statement only; not proved and not used.** On squarefree $t$ no orthogonality to unary theta series is needed (see
`HalfIntRamanujan`). -/
@[kb "duke1988" "Theorem 5: a(n) ≪ n^{3/4-2/7+ε} = n^{13/28+ε} for squarefree n, weight 3/2 [unverified]"]
structure DukeCoeffBound (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop where
  bound : k = 1 → SqfreeCoeffBound M k N χ ((k : ℝ) / 2 - 1 / 28)

/-- **Hecke's bound on squarefree indices:** the squarefree case of `HeckeCoeffBound`, exponent $(2k+1)/4 = k/2 + 1/4$. -/
def HeckeCoeffBoundSqfree (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop :=
  ∀ f ∈ M.cuspForms k N χ, ∀ a : ℕ → ℂ, Abstract.HasQExp f a →
    ∃ C : ℝ, ∀ t : ℕ, 1 ≤ t → Squarefree t → ‖a t‖ ≤ C * (t : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 4)

/-- `HeckeCoeffBound` restricts to squarefree indices. -/
theorem heckeCoeffBoundSqfree_of_heckeCoeffBound {M : MultiplierSystem} {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)}
    (h : HeckeCoeffBound M k N χ) : HeckeCoeffBoundSqfree M k N χ := by
  intro f hf a ha
  obtain ⟨C, hC⟩ := h.bound f hf a ha
  exact ⟨C, fun t ht _ ↦ hC t ht⟩

/-- A squarefree bound with exponent $e < k/2 + 1/4$ implies Hecke's bound on squarefree indices. -/
theorem heckeCoeffBoundSqfree_of_sqfreeCoeffBound {M : MultiplierSystem} {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)}
    {e : ℝ} (h : SqfreeCoeffBound M k N χ e) (he : e < (k : ℝ) / 2 + 1 / 4) : HeckeCoeffBoundSqfree M k N χ := by
  intro f hf a ha
  obtain ⟨C, hC⟩ := h f hf a ha ((k : ℝ) / 2 + 1 / 4 - e) (by linarith)
  refine ⟨C, fun t ht hsq ↦ ?_⟩
  have hexp : e + ((k : ℝ) / 2 + 1 / 4 - e) = ((2 * k + 1 : ℕ) : ℝ) / 4 := by push_cast; ring
  simpa only [hexp] using hC t ht hsq

/-- **The conjecture implies Iwaniec's bound** ($k \ge 2$): $k/2 - 1/4 \le k/2 - 1/28$. -/
theorem iwaniecCoeffBound_of_ramanujan {M : MultiplierSystem} {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)}
    (h : HalfIntRamanujan M k N χ) : IwaniecCoeffBound M k N χ :=
  ⟨fun hk ↦ (h.bound (by omega)).mono (by linarith)⟩

/-- **The conjecture implies Duke's bound** ($k = 1$): $k/2 - 1/4 \le k/2 - 1/28$. -/
theorem dukeCoeffBound_of_ramanujan {M : MultiplierSystem} {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)}
    (h : HalfIntRamanujan M k N χ) : DukeCoeffBound M k N χ :=
  ⟨fun hk ↦ (h.bound (by omega)).mono (by linarith)⟩

/-- **Iwaniec's bound implies Hecke's bound on squarefree indices** ($k \ge 2$): $k/2 - 1/28 < k/2 + 1/4$. -/
theorem heckeCoeffBoundSqfree_of_iwaniec {M : MultiplierSystem} {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)}
    (h : IwaniecCoeffBound M k N χ) (hk : 2 ≤ k) : HeckeCoeffBoundSqfree M k N χ :=
  heckeCoeffBoundSqfree_of_sqfreeCoeffBound (h.bound hk) (by linarith)

/-- **Duke's bound implies Hecke's bound on squarefree indices** ($k = 1$): $k/2 - 1/28 < k/2 + 1/4$. -/
theorem heckeCoeffBoundSqfree_of_duke {M : MultiplierSystem} {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)}
    (h : DukeCoeffBound M k N χ) (hk : k = 1) : HeckeCoeffBoundSqfree M k N χ :=
  heckeCoeffBoundSqfree_of_sqfreeCoeffBound (h.bound hk) (by linarith)

end ModularFormsKB.HalfIntegral
