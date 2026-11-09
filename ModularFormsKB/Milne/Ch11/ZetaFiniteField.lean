import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Zeta
import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus
import ModularFormsKB.Citation
/-!
# Milne, Section 11: the zeta function of a curve over a finite field (Theorem 11.4)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 11, pdf p. 110.

**Theorem 11.4.** Let $C$ be a complete nonsingular curve of genus $g$ over $\mathbb F_q$ and $N_n$ the number of
points of $C$ with coordinates in $\mathbb F_{q^n}$. There are algebraic integers $\alpha_1,\dots,\alpha_{2g}$ with
$N_n = 1 + q^n - \sum_i\alpha_i^n$ for all $n \ge 1$; the $q/\alpha_i$ are a permutation of the $\alpha_i$, and
$|\alpha_i| = q^{1/2}$ (Weil's Riemann hypothesis for curves).

## Items

- `WeilCurveTheorem`: Theorem 11.4 for every genus, as a **named statement** (Weil 1948). Neither Mathlib nor
  Tau Ceti has curves over finite fields with their points over extensions, so it is stated for the function field
  $F = \mathbb F_q(C)$ (Tau Ceti's places, place degrees and genus): the points of $C$ over $\mathbb F_{q^n}$ are the
  Galois orbits of closed points, so $N_n = \sum_{d \mid n} d\,B_d$ with $B_d$ the number of places of degree $d$
  (Stichtenoth, *Algebraic Function Fields and Codes*, 5.1). "Curve over $\mathbb F_q$" includes geometric
  irreducibility, which is the hypothesis that $\mathbb F_q$ is algebraically closed in $F$.
- `weil_elliptic`: Theorem 11.4 for elliptic curves ($g = 1$), **proved** from Tau Ceti's zeta function of an
  elliptic curve (rationality, point counts over extensions, Riemann hypothesis). Here $N_n$ is the number of
  points of the projective Weierstrass model over a finite extension $E/F$ of degree $n$.
- `zeta_elliptic`: the formula $Z(C,t) = \prod(1-\alpha_it)/((1-t)(1-qt))$ in the elliptic case (Tau Ceti).
-/

open TauCeti PowerSeries Polynomial

namespace ModularFormsKB.Milne

universe u v

/-- The number of points of the curve with function field $F/k$ over the extension of $k$ of degree $n$:
$N_n = \sum_{d\mid n} d\,B_d$, where $B_d$ is the number of places of $F/k$ of degree $d$. -/
noncomputable def curvePointCount (k : Type u) (F : Type v) [Field k] [Field F] [Algebra k F] (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d * Nat.card {P : Place k F // P.degree = d}

/-- **Theorem 11.4** (Milne; Weil's theorem, the Riemann hypothesis for curves over finite fields), as a named
statement, in the function field form explained in the module docstring: for a function field $F$ of one variable
over a finite field $k$ with $q$ elements, $k$ algebraically closed in $F$, of genus $g$, there are algebraic
integers $\alpha_1,\dots,\alpha_{2g}$ with $N_n = 1 + q^n - \sum\alpha_i^n$ for all $n\ge1$, such that
$i\mapsto q/\alpha_i$ permutes the $\alpha_i$ and $|\alpha_i| = q^{1/2}$. -/
@[kb "milne2017mf" "Section 11, Thm. 11.4 (pdf p. 110), function field form"]
structure WeilCurveTheorem : Prop where
  weil : ∀ (k : Type u) (F : Type v) [Field k] [Finite k] [Field F] [Algebra k F],
    IsFunctionField k F → IsIntegrallyClosedIn k F →
    ∃ α : Fin (2 * genus k F) → ℂ, (∀ i, IsIntegral ℤ (α i)) ∧
      (∀ n : ℕ, 1 ≤ n → (curvePointCount k F n : ℂ) =
        1 + (Nat.card k : ℂ) ^ n - ∑ i, α i ^ n) ∧
      (∃ σ : Equiv.Perm (Fin (2 * genus k F)), ∀ i, (Nat.card k : ℂ) / α i = α (σ i)) ∧
      (∀ i, ‖α i‖ = Real.sqrt (Nat.card k))

section Elliptic

variable {F : Type u} [Field F] [Finite F] (W : WeierstrassCurve F) [W.IsElliptic]

/-- A complex root of a monic integer quadratic is an algebraic integer. -/
lemma isIntegral_of_quadratic_root (a q : ℤ) (α : ℂ) (h : α ^ 2 - a * α + q = 0) :
    IsIntegral ℤ α := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + Polynomial.C q, ?_, ?_⟩
  · monicity!
  · rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_C]
    simpa using h

/-- Power sums of the roots of `X^2 - a X + q` satisfy the recurrence, hence equal any integer
sequence with the same recurrence and initial values. -/
lemma powSum_eq (a q : ℂ) (α₁ α₂ : ℂ) (h₁ : α₁ ^ 2 = a * α₁ - q) (h₂ : α₂ ^ 2 = a * α₂ - q)
    (hs : α₁ + α₂ = a) (t : ℕ → ℤ) (t0 : t 0 = 2) (t1 : (t 1 : ℂ) = a)
    (hr : ∀ n, (t (n + 2) : ℂ) = a * t (n + 1) - q * t n) (n : ℕ) :
    α₁ ^ n + α₂ ^ n = (t n : ℂ) := by
  have key : ∀ n, α₁ ^ n + α₂ ^ n = (t n : ℂ) ∧ α₁ ^ (n + 1) + α₂ ^ (n + 1) = (t (n + 1) : ℂ) := by
    intro n
    induction n with
    | zero => simp [t0, t1, hs]; norm_num
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [hr, ← ih.1, ← ih.2]
      have e : ∀ x : ℂ, ∀ k : ℕ, x ^ (k + 2) = x ^ k * x ^ 2 := fun x k => by ring
      have e1 := e α₁ n
      have e2 := e α₂ n
      rw [show n + 1 + 1 = n + 2 by ring, e1, e2, h₁, h₂]
      ring
  exact (key n).1

open WeierstrassCurve in
/-- **Theorem 11.4 for elliptic curves** (Milne, Section 11; $g = 1$): for an elliptic curve $W$ over a finite field
$F$ with $q$ elements there are algebraic integers $\alpha_1,\alpha_2$ with
$N_n = \#W(E) = 1 + q^n - \alpha_1^n - \alpha_2^n$ for every finite extension $E/F$ of degree $n$, with
$q/\alpha_1 = \alpha_2$, $q/\alpha_2 = \alpha_1$ and $|\alpha_1| = |\alpha_2| = q^{1/2}$. The $\alpha_i$ are the
roots of $X^2 - a_qX + q$, $a_q$ the Frobenius trace. -/
@[kb "milne2017mf" "Section 11, Thm. 11.4 (pdf p. 110), case g = 1"]
theorem weil_elliptic : ∃ α₁ α₂ : ℂ, IsIntegral ℤ α₁ ∧ IsIntegral ℤ α₂ ∧
    (∀ (E : Type u) [Field E] [Finite E] [Algebra F E],
      ((W⁄E).pointCount : ℂ) = 1 + (Nat.card F : ℂ) ^ Module.finrank F E -
        α₁ ^ Module.finrank F E - α₂ ^ Module.finrank F E) ∧
    (Nat.card F : ℂ) / α₁ = α₂ ∧ (Nat.card F : ℂ) / α₂ = α₁ ∧
    ‖α₁‖ = Real.sqrt (Nat.card F) ∧ ‖α₂‖ = Real.sqrt (Nat.card F) := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq
    (((W.frobeniusTrace : ℂ)) ^ 2 - 4 * (Nat.card F : ℂ)) (two_pos)
  set a : ℂ := (W.frobeniusTrace : ℂ) with ha
  set q : ℂ := (Nat.card F : ℂ) with hq
  have hq0 : q ≠ 0 := by
    rw [hq]; exact_mod_cast (Nat.card_pos (α := F)).ne'
  have h₁ : ((a + s) / 2) ^ 2 = a * ((a + s) / 2) - q := by
    linear_combination (1 / 4 : ℂ) * hs
  have h₂ : ((a - s) / 2) ^ 2 = a * ((a - s) / 2) - q := by
    linear_combination (1 / 4 : ℂ) * hs
  have hsum : (a + s) / 2 + (a - s) / 2 = a := by ring
  have hprod : (a + s) / 2 * ((a - s) / 2) = q := by
    linear_combination (-1 / 4 : ℂ) * hs
  have hne₁ : (a + s) / 2 ≠ 0 := fun h => hq0 (by rw [← hprod, h]; ring)
  have hne₂ : (a - s) / 2 ≠ 0 := fun h => hq0 (by rw [← hprod, h]; ring)
  have hnorm : ∀ α : ℂ, α ≠ 0 → α ^ 2 = a * α - q → ‖α‖ = Real.sqrt (Nat.card F) := by
    intro α hα h
    have hz : 1 - W.frobeniusTrace * α⁻¹ + Nat.card F * (α⁻¹) ^ 2 = 0 := by
      have : (1 : ℂ) - a * α⁻¹ + q * (α⁻¹) ^ 2 = (α ^ 2 - a * α + q) / α ^ 2 := by
        field_simp
      rw [show (1 : ℂ) - W.frobeniusTrace * α⁻¹ + Nat.card F * (α⁻¹) ^ 2
          = 1 - a * α⁻¹ + q * (α⁻¹) ^ 2 from rfl, this]
      rw [show α ^ 2 - a * α + q = 0 by linear_combination h]
      simp
    have := W.norm_eq_inv_sqrt_card_of_one_sub_frobeniusTrace_mul_add_card_mul_sq_eq_zero hz
    rw [norm_inv] at this
    have h2 := congrArg (·⁻¹) this
    simpa using h2
  refine ⟨(a + s) / 2, (a - s) / 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine isIntegral_of_quadratic_root W.frobeniusTrace (Nat.card F) _ ?_
    push_cast
    linear_combination h₁
  · refine isIntegral_of_quadratic_root W.frobeniusTrace (Nat.card F) _ ?_
    push_cast
    linear_combination h₂
  · intro E _ _ _
    have hp := powSum_eq a q _ _ h₁ h₂ hsum (fun n => W.frobeniusPowTrace n)
      W.frobeniusPowTrace_zero (by simp [ha])
      (fun n => by rw [W.frobeniusPowTrace_add_two]; push_cast; rfl)
      (Module.finrank F E)
    have h3 : ((W.frobeniusPowTrace (Module.finrank F E) : ℤ) : ℂ) =
        q ^ Module.finrank F E + 1 - (W⁄E).pointCount := by
      rw [W.frobeniusPowTrace_finrank E, WeierstrassCurve.frobeniusTrace_def,
        Module.natCard_eq_pow_finrank (K := F) (V := E)]
      push_cast
      ring
    linear_combination hp + h3
  · rw [div_eq_iff hne₁]; linear_combination -hprod
  · rw [div_eq_iff hne₂]; linear_combination -hprod
  · exact hnorm _ hne₁ h₁
  · exact hnorm _ hne₂ h₂

end Elliptic

end ModularFormsKB.Milne
