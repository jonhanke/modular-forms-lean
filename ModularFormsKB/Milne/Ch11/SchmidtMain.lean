import ModularFormsKB.Milne.Ch11.SchmidtAlgebra
import ModularFormsKB.Milne.Ch11.SchmidtExtension
import ModularFormsKB.Milne.Ch11.WeilRationality
import ModularFormsKB.Milne.Ch11.BombieriUpper

/-!
# F. K. Schmidt's theorem

**Theorem** (F. K. Schmidt 1931; Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Corollary 5.1.11): a
function field $F$ over a finite field $k$, $k$ algebraically closed in $F$, has a divisor of degree one.

Proof (Stichtenoth's pole-order argument, made polynomial). Let $\delta$ be the least positive degree of a divisor;
it divides every place degree. With a divisor $D$ of degree $\delta$, the class sums give
$(1-u)(1-Qu)Y_F(u) = P(u)$ with $Y_F(u) = \sum_m A_{\delta m}(F)u^m$, $Q = q^\delta$, $P(1) \ne 0$
(`exists_gcd_poly`). For the constant field extension $F' = F\cdot\mathbb F_{q^\delta}$, with its own $\delta'$,
$(1-u^{\delta'})(1-Q^{\delta'}u^{\delta'})Z_{F'}(u) = P'(u)$ with $P'(1) \ne 0$, and $Z_{F'} = Y_F^\delta$
(`zeta_constantCompositum_eq_pow`). Hence $P'\,((1-u)(1-Qu))^\delta = P^\delta(1-u^{\delta'})(1-Q^{\delta'}u^{\delta'})$,
and comparing the multiplicity of the root $u = 1$ gives $\delta = 1$ (`eq_one_of_rootMultiplicity`).

Consequently Theorem 11.4 depends only on the even-degree lower bound: `weilCurveTheorem_of_lowerBound`.
-/

open Finset TauCeti TauCeti.AlgebraicGeometry Polynomial

namespace ModularFormsKB.Milne

universe u v

/-- The gcd of the degrees, its divisor, and the two polynomials. -/
theorem exists_gcd_poly (k : Type u) (F : Type v) [Field k] [Finite k] [Field F] [Algebra k F]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) :
    ∃ δ : ℕ, 1 ≤ δ ∧ (∃ D : Divisor k F, Divisor.degree D = δ) ∧ (∀ P : Place k F, δ ∣ P.degree) ∧
      (∃ P : ℤ[X], (1 - PowerSeries.X) * (1 - PowerSeries.C ((Nat.card k : ℤ) ^ δ) * PowerSeries.X) *
          PowerSeries.mk (fun m => (effectiveDivisorCount k F (δ * m) : ℤ)) = (P : PowerSeries ℤ) ∧
        P.eval 1 ≠ 0) ∧
      (∃ P : ℤ[X], (1 - PowerSeries.X ^ δ) *
          (1 - PowerSeries.C ((Nat.card k : ℤ) ^ δ) * PowerSeries.X ^ δ) *
          PowerSeries.mk (fun n => (effectiveDivisorCount k F n : ℤ)) = (P : PowerSeries ℤ) ∧
        P.eval 1 ≠ 0) := by
  classical
  set q : ℕ := Nat.card k with hq
  have hq2 : 2 ≤ q := Finite.one_lt_card
  -- `δ`, the least positive degree of a divisor
  have hex0 : ∃ n : ℕ, 0 < n ∧ ∃ D : Divisor k F, Divisor.degree D = n := by
    obtain ⟨P⟩ := Place.nonempty hF
    exact ⟨P.degree, Place.one_le_degree_of_isFunctionField P hF, WeilDivisor.ofPoint P,
      Divisor.degree_ofPoint P⟩
  set δ := Nat.find hex0 with hδdef
  have hδspec := Nat.find_spec hex0
  obtain ⟨D, hD⟩ := hδspec.2
  have hδ1 : 1 ≤ δ := hδspec.1
  have hdvd : ∀ P : Place k F, δ ∣ P.degree := by
    intro P
    by_contra hnd
    have hr : 0 < P.degree % δ := Nat.pos_of_ne_zero fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    have hrlt : P.degree % δ < δ := Nat.mod_lt _ hδspec.1
    refine Nat.find_min hex0 hrlt ⟨hr, WeilDivisor.ofPoint P - ((P.degree / δ : ℕ) : ℤ) • D, ?_⟩
    rw [Divisor.degree_sub, Divisor.degree_zsmul, Divisor.degree_ofPoint, hD]
    have h1 := Nat.mod_add_div P.degree δ
    have h2 : ((P.degree % δ : ℕ) : ℤ) + (δ : ℤ) * ((P.degree / δ : ℕ) : ℤ) = P.degree := by
      exact_mod_cast h1
    linarith
  refine ⟨δ, hδ1, ⟨D, hD⟩, hdvd, ?_⟩
  -- class sums
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
  set h : ℕ := Fintype.card (Divisor.degreeClass hF).ker with hh
  have hh1 : 1 ≤ h := Fintype.card_pos
  set g : ℕ := genus k F with hg
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  obtain ⟨W, hW⟩ := exists_isRiemannRochDivisor hF hex
  have hWdeg := hW.degree_eq hF hex
  let a : ℕ → ℚ := fun m => ∑ c, (q : ℚ) ^ Divisor.dim (m • D + R c)
  have hA : ∀ m, ((q : ℚ) - 1) * ((effectiveDivisorCount k F (δ * m) : ℤ) : ℚ) = a m - h := by
    intro m
    have h1 := effectiveDivisorCount_mul_eq_sum_of_degree hF hex D δ hD R hR m
    have h2 : ((q : ℚ) - 1) * ((effectiveDivisorCount k F (δ * m) : ℤ) : ℚ) =
        ∑ c, ((q : ℚ) ^ Divisor.dim (m • D + R c) - 1) := by exact_mod_cast h1
    rw [h2, sum_sub_distrib]
    simp [a, hh]
  have hbig : ∀ m, 2 * g ≤ m →
      a m = h * (q : ℚ) ^ ((1 : ℤ) - g) * ((q ^ δ : ℕ) : ℚ) ^ m := by
    intro m hm
    have hdim : ∀ c, (Divisor.dim (m • D + R c) : ℤ) = δ * m + 1 - g := by
      intro c
      have hRR := hW (m • D + R c)
      have hdegc : Divisor.degree (m • D + R c) = δ * m := by
        rw [Divisor.degree_add, map_nsmul, hRdeg, hD, nsmul_eq_mul]; push_cast; ring
      have h0 : Divisor.dim (W - (m • D + R c)) = 0 := by
        apply Divisor.dim_eq_zero_of_degree_neg hF
        rw [Divisor.degree_sub, hWdeg, hdegc]
        have : (m : ℤ) ≤ δ * m := by nlinarith
        push_cast; omega
      rw [h0, hdegc] at hRR
      push_cast at hRR
      linarith
    simp only [a]
    rw [show (h : ℚ) * (q : ℚ) ^ ((1 : ℤ) - g) * ((q ^ δ : ℕ) : ℚ) ^ m =
        ∑ _c : (Divisor.degreeClass hF).ker, (q : ℚ) ^ ((1 : ℤ) - g) * ((q ^ δ : ℕ) : ℚ) ^ m by
      simp [hh]; ring]
    refine sum_congr rfl fun c _ => ?_
    rw [← zpow_natCast, hdim c]
    push_cast
    rw [← pow_mul, ← zpow_natCast (q : ℚ) (δ * m), ← zpow_add₀ hq0]
    congr 1
    push_cast; ring
  have hqδ : 2 ≤ q ^ δ := le_trans hq2 (Nat.le_self_pow (by omega) q)
  refine ⟨?_, ?_⟩
  · obtain ⟨P, hP, hP1⟩ := exists_poly_of_eventually_geometric q (q ^ δ) h 1 hq2 hqδ hh1 le_rfl
      ((q : ℚ) ^ ((1 : ℤ) - g)) (fun m => (effectiveDivisorCount k F (δ * m) : ℤ))
      (fun n hn => absurd (one_dvd n) hn) a (fun m => by simpa using hA m) (2 * g) hbig
    refine ⟨P, ?_, hP1⟩
    rw [← hP]
    simp only [pow_one]
    push_cast
    rfl
  · obtain ⟨P, hP, hP1⟩ := exists_poly_of_eventually_geometric q (q ^ δ) h δ hq2 hqδ hh1 hδ1
      ((q : ℚ) ^ ((1 : ℤ) - g)) (fun n => (effectiveDivisorCount k F n : ℤ))
      (fun n hn => by simp [effectiveDivisorCount_eq_zero_of_not_dvd δ hdvd n hn]) a hA (2 * g) hbig
    refine ⟨P, ?_, hP1⟩
    rw [← hP]
    push_cast
    rfl

/-- **F. K. Schmidt's theorem.** -/
theorem schmidtDegreeOne : SchmidtDegreeOne.{u, v} := by
  refine ⟨fun k F _ _ _ _ hF hex => ?_⟩
  obtain ⟨δ, hδ1, ⟨D, hD⟩, hdvd, ⟨P, hP, hP1⟩, -⟩ := exists_gcd_poly k F hF hex
  set q : ℕ := Nat.card k with hq
  have hq2 : 2 ≤ q := Finite.one_lt_card
  obtain ⟨F', k', hfd, hdeg, hc⟩ := exists_constantCompositum_finrank_eq (k := k) (F := F) δ hδ1
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top hc
  have hex' : IsIntegrallyClosedIn k' F' := IsIntegrallyClosedIn.of_constantCompositum_eq_top hex hc
  have : Finite k' := Module.finite_of_finite k
  have hcard : Nat.card k' = q ^ δ := by
    rw [Module.natCard_eq_pow_finrank (K := k), hdeg]
  obtain ⟨δ', hδ'1, -, -, -, ⟨P', hP', hP'1⟩⟩ := exists_gcd_poly k' F' hF' hex'
  have hZ := zeta_constantCompositum_eq_pow hF hex hc δ hdeg hdvd
  rw [hcard] at hP'
  -- the polynomial identity
  have hid : P' * ((1 - X) * (1 - C ((q : ℤ) ^ δ) * X)) ^ δ =
      P ^ δ * ((1 - X ^ δ') * (1 - C (((q : ℤ) ^ δ) ^ δ') * X ^ δ')) := by
    apply Polynomial.coe_injective
    push_cast
    rw [← hP', ← hP, hZ]
    simp only [mul_pow, Nat.cast_pow, map_pow]
    ring
  have hQ : 2 ≤ q ^ δ := le_trans hq2 (Nat.le_self_pow (by omega) q)
  have h1 := eq_one_of_rootMultiplicity P P' δ δ' (q ^ δ) hδ1 hδ'1 hQ hP1 hP'1 (by
    convert hid using 3 <;> push_cast <;> ring)
  exact ⟨D, by rw [hD, h1]; rfl⟩

/-- **Theorem 11.4** (Milne; Weil's Riemann hypothesis for curves over finite fields) from the even-degree lower
bound alone: Bombieri's upper bound and F. K. Schmidt's theorem are proved. -/
theorem weilCurveTheorem_of_lowerBound (hL : HasseWeilLowerBoundEven.{u, v}) : WeilCurveTheorem.{u, v} :=
  weilCurveTheorem_of_schmidt_of_lowerBound schmidtDegreeOne hL

end ModularFormsKB.Milne
