import ModularFormsKB.Milne.Ch11.WeilCount

/-!
# F. K. Schmidt's theorem: counting in degrees divisible by the gcd

Let $F/k$ be a function field over a finite field with $q$ elements, $k$ algebraically closed in $F$, and let
$\delta$ divide the degree of every place (Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed.,
Lemma 5.1.9 – Corollary 5.1.11).

- `effectiveDivisorCount_mul_eq_sum_of_degree`: for a divisor $D$ of degree $\delta$ and representatives $R_c$ of
  $\mathrm{Cl}^0(F)$, $(q-1)A_{\delta m} = \sum_c (q^{\ell(mD + R_c)} - 1)$ (as `effectiveDivisorCount_mul_eq_sum`, with
  $D$ in place of a divisor of degree one).
- `effectiveDivisorCount_eq_zero_of_not_dvd`, `curvePointCount_eq_zero_of_not_dvd`: $A_n = N_n = 0$ for $\delta \nmid n$.
- `curvePointCount_constantCompositum`: $N_m(F\cdot k') = N_{[k':k]m}(F)$, from `card_degree_one_constantCompositum` in
  the tower $F \subseteq F\cdot k' \subseteq F\cdot k''$, $[k'':k'] = m$.
- `zeta_constantCompositum_eq_pow`: for $[k':k] = \delta$, $Z_{F\cdot k'}(u) = Y(u)^\delta$ with
  $Y(u) = \sum_m A_{\delta m}(F)u^m$ (both sides have constant term $1$ and the same logarithmic derivative
  $\sum_m N_m(F\cdot k')u^m = \sum_m N_{\delta m}(F)u^m$; Newton recursion, `effectiveDivisorCount_newton`).
-/

open Finset TauCeti TauCeti.AlgebraicGeometry

namespace ModularFormsKB.Milne

universe u u' v v'

section Count

variable {k : Type u} {F : Type v} [Field k] [Finite k] [Field F] [Algebra k F]

/-- $(q - 1) A_{\delta m} = \sum_{c \in \mathrm{Cl}^0(F)} (q^{\ell(mD + R_c)} - 1)$ for $\deg D = \delta$. -/
theorem effectiveDivisorCount_mul_eq_sum_of_degree (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) [Fintype (Divisor.degreeClass hF).ker] (D : Divisor k F) (δ : ℕ)
    (hD : Divisor.degree D = δ) (R : (Divisor.degreeClass hF).ker → Divisor k F)
    (hR : ∀ c, (Place.orderSystem hF).divisorClass (R c) = c) (m : ℕ) :
    ((Nat.card k : ℤ) - 1) * effectiveDivisorCount k F (δ * m) =
      ∑ c, ((Nat.card k : ℤ) ^ Divisor.dim (m • D + R c) - 1) := by
  classical
  have hdegR : ∀ c, Divisor.degree (R c) = 0 := fun c => by
    rw [← Divisor.degreeClass_divisorClass hF, hR c]
    exact (AddMonoidHom.mem_ker).mp c.2
  have hdegN : Divisor.degree (m • D) = ((δ * m : ℕ) : ℤ) := by
    simp [hD]; ring
  have hdegS : ∀ c, Divisor.degree (m • D + R c) = ((δ * m : ℕ) : ℤ) := fun c => by
    rw [Divisor.degree_add, hdegN, hdegR, add_zero]
  let P := {E : Divisor k F // 0 ≤ E ∧ Divisor.degree E = ((δ * m : ℕ) : ℤ)}
  have hPfin : Finite P :=
    (Set.Finite.subset (Divisor.finite_setOf_nonneg_degree_le hF (δ * m))
      (t := {E : Divisor k F | 0 ≤ E ∧ Divisor.degree E = ((δ * m : ℕ) : ℤ)})
      (fun E (hE : 0 ≤ E ∧ Divisor.degree E = ((δ * m : ℕ) : ℤ)) => ⟨hE.1, hE.2.le⟩)).to_subtype
  let ψ : P → (Divisor.degreeClass hF).ker := fun E =>
    ⟨(Place.orderSystem hF).divisorClass E.1 - (Place.orderSystem hF).divisorClass (m • D), by
      rw [AddMonoidHom.mem_ker, map_sub, Divisor.degreeClass_divisorClass,
        Divisor.degreeClass_divisorClass, E.2.2, hdegN, sub_self]⟩
  have hfib : ∀ c, Nat.card {E : P // ψ E = c} =
      Nat.card {E : Divisor k F // 0 ≤ E ∧
          (Place.orderSystem hF).LinearlyEquivalent E (m • D + R c)} := by
    intro c
    have key : ∀ E : Divisor k F, (Place.orderSystem hF).divisorClass E -
        (Place.orderSystem hF).divisorClass (m • D) = c ↔
        (Place.orderSystem hF).LinearlyEquivalent E (m • D + R c) := by
      intro E
      rw [← (Place.orderSystem hF).divisorClass_eq_iff, map_add, hR c, sub_eq_iff_eq_add, add_comm]
    refine Nat.card_congr
      { toFun := fun E => ⟨E.1.1, E.1.2.1, (key E.1.1).mp (congrArg Subtype.val E.2)⟩
        invFun := fun E => ⟨⟨E.1, E.2.1, by
          have := Divisor.degreeClass_divisorClass hF E.1
          rw [(Place.orderSystem hF).divisorClass_eq_iff.mpr E.2.2,
            Divisor.degreeClass_divisorClass, hdegS] at this
          exact this.symm⟩, Subtype.ext ((key E.1).mpr E.2.2)⟩
        left_inv := fun E => by ext; rfl
        right_inv := fun E => by ext; rfl }
  haveI := Fintype.ofFinite P
  have hA : effectiveDivisorCount k F (δ * m) = ∑ c, Nat.card {E : P // ψ E = c} := by
    unfold effectiveDivisorCount
    change Nat.card P = _
    rw [Nat.card_eq_fintype_card, ← Fintype.card_congr (Equiv.sigmaFiberEquiv ψ), Fintype.card_sigma]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Nat.card_eq_fintype_card]
  rw [hA]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hfib c, card_effective_linearlyEquivalent hF hex]

/-- $A_n = 0$ when $\delta \nmid n$ and $\delta$ divides every place degree. -/
theorem effectiveDivisorCount_eq_zero_of_not_dvd (δ : ℕ) (hδ : ∀ P : Place k F, δ ∣ P.degree) (n : ℕ)
    (hn : ¬ δ ∣ n) : effectiveDivisorCount k F n = 0 := by
  unfold effectiveDivisorCount
  haveI : IsEmpty {D : Divisor k F // 0 ≤ D ∧ Divisor.degree D = n} := by
    refine ⟨fun ⟨D, _, hD⟩ => hn ?_⟩
    have h : (δ : ℤ) ∣ Divisor.degree D := by
      rw [Divisor.degree_apply, Finsupp.sum]
      exact Finset.dvd_sum fun P _ => Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr (hδ P)) _
    rw [hD] at h
    exact Int.natCast_dvd_natCast.mp h
  exact Nat.card_of_isEmpty

/-- $N_n = 0$ when $\delta \nmid n$ and $\delta$ divides every place degree. -/
theorem curvePointCount_eq_zero_of_not_dvd (δ : ℕ) (hδ : ∀ P : Place k F, δ ∣ P.degree) (n : ℕ)
    (hn : ¬ δ ∣ n) : curvePointCount k F n = 0 := by
  unfold curvePointCount
  refine Finset.sum_eq_zero fun d hd => ?_
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  haveI : IsEmpty {P : Place k F // P.degree = d} := by
    refine ⟨fun ⟨P, hP⟩ => hn ?_⟩
    have := hδ P
    rw [hP] at this
    exact this.trans hdn
  simp

end Count

end ModularFormsKB.Milne
