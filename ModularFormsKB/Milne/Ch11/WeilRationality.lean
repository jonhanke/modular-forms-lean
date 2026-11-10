import ModularFormsKB.Milne.Ch11.WeilCount
import ModularFormsKB.Milne.Ch11.WeilLSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, Section 11: rationality and functional equation of the zeta function

H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed. (`stichtenoth2009`), Theorem 5.1.15 (a), (b).

The named statement `ZetaLPolynomial` follows from Riemann–Roch (Tau Ceti, `TauCeti.exists_isRiemannRochDivisor`),
the finiteness of $\mathrm{Cl}^0(F)$ (Tau Ceti, `TauCeti.Divisor.finite_ker_degreeClass`), the count of effective
divisors in a class (`card_effective_linearlyEquivalent`) and **F. K. Schmidt's theorem** that there is a divisor of
degree one (`SchmidtDegreeOne`, named statement; Stichtenoth, Corollary 5.1.11). With $D_1$ of degree $1$ and
representatives $R_c$ of the classes $c \in \mathrm{Cl}^0(F)$, put $a_m = \sum_c q^{\ell(mD_1 + R_c)}$; then
$a_m = h$ for $m < 0$, Riemann–Roch gives $a_m = q^{m+1-g}a_{2g-2-m}$ (the canonical class $W$ sends the class of
$mD_1 + R_c$ to that of $(2g-2-m)D_1 + R_{c'}$, $c' = [W - (2g-2)D_1] - c$), and $(q - 1)A_n = a_n - h$; the algebra
is `exists_lpoly_of_classSums`.
-/

open Finset TauCeti TauCeti.AlgebraicGeometry

namespace ModularFormsKB.Milne

universe u v

/-- **F. K. Schmidt's theorem** (Schmidt 1931; Stichtenoth, Corollary 5.1.11), as a named statement: a function
field over a finite field $k$, with $k$ algebraically closed in it, has a divisor of degree $1$. -/
@[kb "stichtenoth2009" "Corollary 5.1.11 (F. K. Schmidt)"]
structure SchmidtDegreeOne : Prop where
  exists_degree_one : ∀ (k : Type u) (F : Type v) [Field k] [Finite k] [Field F] [Algebra k F],
    IsFunctionField k F → IsIntegrallyClosedIn k F → ∃ D : Divisor k F, Divisor.degree D = 1

section Glue

variable {k : Type u} {F : Type v} [Field k] [Finite k] [Field F] [Algebra k F]

/-- There is exactly one effective divisor of degree $0$. -/
lemma effectiveDivisorCount_zero (hF : IsFunctionField k F) : effectiveDivisorCount k F 0 = 1 := by
  unfold effectiveDivisorCount
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨0, ⟨le_rfl, by simp⟩⟩, ?_⟩
  rintro ⟨D, hE, hd⟩
  have hD0 : 0 ≤ D := hE
  have := (Divisor.degree_eq_zero_iff hF hD0).mp (by exact_mod_cast hd)
  subst this
  rfl

end Glue

/-- **`ZetaLPolynomial` from F. K. Schmidt's theorem** (Stichtenoth, Theorem 5.1.15 (a), (b)). -/
theorem zetaLPolynomial_of_schmidt (hS : SchmidtDegreeOne.{u, v}) : ZetaLPolynomial.{u, v} := by
  refine ⟨fun k F _ _ _ _ hF hex => ?_⟩
  classical
  obtain ⟨D₁, hD₁⟩ := hS.exists_degree_one k F hF hex
  obtain ⟨W, hW⟩ := exists_isRiemannRochDivisor hF hex
  haveI : Finite (Divisor.degreeClass hF).ker := Divisor.finite_ker_degreeClass hF
  letI : Fintype (Divisor.degreeClass hF).ker := Fintype.ofFinite _
  set S := Place.orderSystem hF with hSdef
  let R : (Divisor.degreeClass hF).ker → Divisor k F := fun c =>
    (QuotientAddGroup.mk'_surjective S.principalSubgroup (c : S.ClassGroup)).choose
  have hR : ∀ c, S.divisorClass (R c) = c := fun c => by
    rw [S.divisorClass_eq_mk']
    exact (QuotientAddGroup.mk'_surjective S.principalSubgroup (c : S.ClassGroup)).choose_spec
  have hRdeg : ∀ c, Divisor.degree (R c) = 0 := fun c => by
    rw [← Divisor.degreeClass_divisorClass hF, hR c]
    exact c.2
  set q : ℕ := Nat.card k with hq
  set g : ℕ := genus k F with hg
  set h : ℕ := Fintype.card (Divisor.degreeClass hF).ker with hh
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  let a : ℤ → ℚ := fun m => ∑ c, (q : ℚ) ^ Divisor.dim (m • D₁ + R c)
  have hdeg : ∀ (m : ℤ) c, Divisor.degree (m • D₁ + R c) = m := fun m c => by
    rw [Divisor.degree_add, Divisor.degree_zsmul, hD₁, hRdeg]; ring
  have hneg : ∀ m : ℤ, m < 0 → a m = h := by
    intro m hm
    simp only [a]
    rw [show (h : ℚ) = ∑ _c : (Divisor.degreeClass hF).ker, (1 : ℚ) by simp [hh]]
    refine sum_congr rfl fun c _ => ?_
    rw [Divisor.dim_eq_zero_of_degree_neg hF (by rw [hdeg]; exact hm), pow_zero]
  -- the class of `W - (2g-2) D₁`
  have hWdeg := hW.degree_eq hF hex
  let κ : (Divisor.degreeClass hF).ker :=
    ⟨S.divisorClass (W - ((2 * g - 2 : ℤ)) • D₁), by
      rw [AddMonoidHom.mem_ker, Divisor.degreeClass_divisorClass, Divisor.degree_sub,
        Divisor.degree_zsmul, hD₁, hWdeg]; ring⟩
  have hdual : ∀ m : ℤ, a m = (q : ℚ) ^ (m + 1 - g) * a (2 * g - 2 - m) := by
    intro m
    simp only [a]
    rw [mul_sum]
    rw [← Fintype.sum_equiv (Equiv.subLeft κ)
      (fun c => (q : ℚ) ^ (m + 1 - g) * (q : ℚ) ^ Divisor.dim ((2 * g - 2 - m) • D₁ + R (κ - c)))
      (fun c => (q : ℚ) ^ (m + 1 - g) * (q : ℚ) ^ Divisor.dim ((2 * g - 2 - m) • D₁ + R c))
      (fun c => rfl)]
    refine sum_congr rfl fun c _ => ?_
    -- Riemann–Roch at `m D₁ + R c`
    have hRR := hW (m • D₁ + R c)
    have hlin : S.LinearlyEquivalent (W - (m • D₁ + R c)) ((2 * g - 2 - m) • D₁ + R (κ - c)) := by
      rw [← S.divisorClass_eq_iff]
      simp only [map_add, map_sub, hR, κ, AddSubgroup.coe_sub, map_zsmul, sub_smul]
      abel
    rw [Divisor.dim_eq_of_linearlyEquivalent hF hlin, hdeg] at hRR
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq0]
    congr 1
  have hA : ∀ n : ℕ, ((q : ℚ) - 1) * ((effectiveDivisorCount k F n : ℤ) : ℚ) = a n - h := by
    intro n
    have h1 := effectiveDivisorCount_mul_eq_sum hF hex D₁ hD₁ R hR n
    have h2 : ((q : ℚ) - 1) * ((effectiveDivisorCount k F n : ℤ) : ℚ) =
        ∑ c, ((q : ℚ) ^ Divisor.dim (n • D₁ + R c) - 1) := by exact_mod_cast h1
    rw [h2, sum_sub_distrib]
    simp only [a, natCast_zsmul, sum_const, card_univ, ← hh]
    simp
  exact exists_lpoly_of_classSums q g h hq2 (fun n => (effectiveDivisorCount k F n : ℤ)) a hneg hdual hA
    (by simp [effectiveDivisorCount_zero hF])

end ModularFormsKB.Milne
