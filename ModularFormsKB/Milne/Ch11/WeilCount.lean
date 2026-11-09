import ModularFormsKB.Milne.Ch11.WeilZeta

/-!
# Counting effective divisors by divisor classes

For a function field $F$ over a finite field $k$ with $q$ elements, $k$ algebraically closed in $F$
(Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Lemma 5.1.4 and Proposition 5.1.8 [unverified
numbering]):

- `card_effective_linearlyEquivalent`: the effective divisors linearly equivalent to $D$ are the
  $D + (f)$, $f \in \mathcal L(D) \setminus 0$, and $f$, $f'$ give the same divisor exactly when $f'/f \in k^\times$;
  so $(q - 1)\cdot\#\{E \ge 0 : E \sim D\} = q^{\ell(D)} - 1$.
- `effectiveDivisorCount_mul_eq_sum`: given a divisor $D_1$ of degree $1$ and representatives $R_c$ of the
  classes $c \in \mathrm{Cl}^0(F)$, $(q - 1) A_n = \sum_{c} (q^{\ell(nD_1 + R_c)} - 1)$.
-/

open Finset TauCeti TauCeti.AlgebraicGeometry

namespace ModularFormsKB.Milne

universe u v

variable {k : Type u} {F : Type v} [Field k] [Finite k] [Field F] [Algebra k F]

/-- $(q - 1)\cdot\#\{E \ge 0 : E \sim D\} = q^{\ell(D)} - 1$. -/
theorem card_effective_linearlyEquivalent (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (D : Divisor k F) :
    ((Nat.card k : ℤ) - 1) *
        Nat.card {E : Divisor k F // 0 ≤ E ∧
          (Place.orderSystem hF).LinearlyEquivalent E D} =
      (Nat.card k : ℤ) ^ Divisor.dim D - 1 := by
  classical
  haveI := finiteDimensional_riemannRochSpace hF D
  haveI : Finite (riemannRochSpace D) := Module.finite_of_finite k
  have hV : Nat.card (riemannRochSpace D) = Nat.card k ^ Divisor.dim D :=
    Module.natCard_eq_pow_finrank (K := k)
  -- the units of `L(D)`
  let T := {u : Fˣ // (u : F) ∈ riemannRochSpace D}
  let S := {E : Divisor k F // 0 ≤ E ∧
          (Place.orderSystem hF).LinearlyEquivalent E D}
  let eT : T ≃ {v : riemannRochSpace D // v ≠ 0} :=
    { toFun := fun u => ⟨⟨u.1, u.2⟩, fun h => u.1.ne_zero (congrArg Subtype.val h)⟩
      invFun := fun v => ⟨Units.mk0 v.1.1 (fun h => v.2 (Subtype.ext h)), by simpa using v.1.2⟩
      left_inv := fun u => by ext; simp
      right_inv := fun v => by ext; simp }
  haveI : Finite T := Finite.of_equiv _ eT.symm
  haveI : Finite {v : riemannRochSpace D // v ≠ 0} := inferInstance
  have hT : Nat.card T + 1 = Nat.card (riemannRochSpace D) := by
    rw [Nat.card_congr eT, ← Nat.card_congr (Equiv.optionSubtypeNe (0 : riemannRochSpace D))]
    haveI := Fintype.ofFinite {v : riemannRochSpace D // v ≠ 0}
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_option]
  let φ : T → S := fun u => ⟨D + Divisor.principal hF u.1, by
    have h := (mem_riemannRochSpace_units_iff hF).mp u.2
    refine ⟨?_, ?_⟩
    · rwa [add_comm]
    · rw [Divisor.linearlyEquivalent_iff hF]
      exact ⟨u.1, by simp⟩⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨E, hE, hl⟩
    obtain ⟨z, hz⟩ := (Divisor.linearlyEquivalent_iff hF).mp hl
    refine ⟨⟨z, ?_⟩, ?_⟩
    · rw [mem_riemannRochSpace_units_iff hF, hz, sub_add_cancel]; exact hE
    · apply Subtype.ext; simp [φ, hz]
  have hfib : ∀ E : S, Nat.card {u : T // φ u = E} = Nat.card k - 1 := by
    intro E
    obtain ⟨u0, hu0⟩ := hsurj E
    have hprin : ∀ c : kˣ, Divisor.principal hF (Units.map (algebraMap k F : k →* F) c) = 0 :=
      fun c => (Divisor.principal_eq_zero_iff hF hex _).mpr ⟨c, rfl⟩
    let g : kˣ → {u : T // φ u = E} := fun c =>
      ⟨⟨u0.1 * Units.map (algebraMap k F : k →* F) c, by
        have h : (algebraMap k F c) * (u0.1 : F) ∈ riemannRochSpace D := by
          rw [← Algebra.smul_def]; exact (riemannRochSpace D).smul_mem _ u0.2
        simpa [mul_comm] using h⟩, by
        rw [← hu0]; apply Subtype.ext
        simp [φ, Divisor.principal_mul, hprin]⟩
    have hg : Function.Bijective g := by
      constructor
      · intro c c' h
        have h1 : u0.1 * Units.map (algebraMap k F : k →* F) c =
            u0.1 * Units.map (algebraMap k F : k →* F) c' := congrArg (fun x => x.1.1) h
        have h2 := mul_left_cancel h1
        ext
        exact (algebraMap k F).injective (congrArg Units.val h2)
      · rintro ⟨u, hu⟩
        have h0 : Divisor.principal hF (u.1 / u0.1) = 0 := by
          rw [Divisor.principal_div]
          have := congrArg Subtype.val (hu.trans hu0.symm)
          simp only [φ] at this
          rw [add_right_inj] at this
          rw [this, sub_self]
        obtain ⟨c, hc⟩ := (Divisor.principal_eq_zero_iff hF hex _).mp h0
        have hc0 : c ≠ 0 := by
          rintro rfl
          have : ((u.1 / u0.1 : Fˣ) : F) ≠ 0 := Units.ne_zero _
          exact this (by rw [← hc]; simp)
        refine ⟨Units.mk0 c hc0, ?_⟩
        have hu' : (u.1 : F) = algebraMap k F c * u0.1 := by
          rw [Units.val_div_eq_div_val] at hc
          rw [hc]; field_simp [u0.1.ne_zero]
        apply Subtype.ext; apply Subtype.ext; apply Units.ext
        show (u0.1 : F) * algebraMap k F c = u.1
        rw [hu', mul_comm]
    rw [← Nat.card_units (α := k)]
    exact (Nat.card_eq_of_bijective g hg).symm
  haveI : Finite S := Finite.of_surjective φ hsurj
  haveI := Fintype.ofFinite T
  haveI := Fintype.ofFinite S
  have hcard : Nat.card T = Nat.card S * (Nat.card k - 1) := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_congr (Equiv.sigmaFiberEquiv φ), Fintype.card_sigma]
    have hE : ∀ E : S, Fintype.card {x // φ x = E} = Nat.card k - 1 := fun E => by
      rw [← Nat.card_eq_fintype_card]; exact hfib E
    simp only [hE]
    simp [Nat.card_eq_fintype_card]
  have hq : 1 ≤ Nat.card k := Nat.card_pos
  have h1 : (Nat.card T : ℤ) + 1 = (Nat.card k : ℤ) ^ Divisor.dim D := by
    have := hT; rw [hV] at this; exact_mod_cast this
  rw [hcard] at h1
  push_cast [Nat.cast_sub hq] at h1
  linarith

/-- $(q - 1) A_n = \sum_{c \in \mathrm{Cl}^0(F)} (q^{\ell(nD_1 + R_c)} - 1)$. -/
theorem effectiveDivisorCount_mul_eq_sum (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    [Fintype (Divisor.degreeClass hF).ker] (D₁ : Divisor k F) (hD₁ : Divisor.degree D₁ = 1)
    (R : (Divisor.degreeClass hF).ker → Divisor k F)
    (hR : ∀ c, (Place.orderSystem hF).divisorClass (R c) = c) (n : ℕ) :
    ((Nat.card k : ℤ) - 1) * effectiveDivisorCount k F n =
      ∑ c, ((Nat.card k : ℤ) ^ Divisor.dim (n • D₁ + R c) - 1) := by
  classical
  have hdegR : ∀ c, Divisor.degree (R c) = 0 := fun c => by
    rw [← Divisor.degreeClass_divisorClass hF, hR c]
    exact (AddMonoidHom.mem_ker).mp c.2
  have hdegN : Divisor.degree (n • D₁) = n := by simp [hD₁]
  have hdegS : ∀ c, Divisor.degree (n • D₁ + R c) = n := fun c => by
    rw [Divisor.degree_add, hdegN, hdegR, add_zero]
  let P := {E : Divisor k F // 0 ≤ E ∧ Divisor.degree E = n}
  have hPfin : Finite P :=
    (Set.Finite.subset (Divisor.finite_setOf_nonneg_degree_le hF n)
      (t := {E : Divisor k F | 0 ≤ E ∧ Divisor.degree E = n})
      (fun E (hE : 0 ≤ E ∧ Divisor.degree E = n) => ⟨hE.1, hE.2.le⟩)).to_subtype
  let ψ : P → (Divisor.degreeClass hF).ker := fun E =>
    ⟨(Place.orderSystem hF).divisorClass E.1 - (Place.orderSystem hF).divisorClass (n • D₁), by
      rw [AddMonoidHom.mem_ker, map_sub, Divisor.degreeClass_divisorClass,
        Divisor.degreeClass_divisorClass, E.2.2, hdegN, sub_self]⟩
  have hfib : ∀ c, Nat.card {E : P // ψ E = c} =
      Nat.card {E : Divisor k F // 0 ≤ E ∧
          (Place.orderSystem hF).LinearlyEquivalent E (n • D₁ + R c)} := by
    intro c
    have key : ∀ E : Divisor k F, (Place.orderSystem hF).divisorClass E -
        (Place.orderSystem hF).divisorClass (n • D₁) = c ↔
        (Place.orderSystem hF).LinearlyEquivalent E (n • D₁ + R c) := by
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
  have hA : effectiveDivisorCount k F n = ∑ c, Nat.card {E : P // ψ E = c} := by
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

end ModularFormsKB.Milne
