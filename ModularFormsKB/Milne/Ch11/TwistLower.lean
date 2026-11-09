import ModularFormsKB.Milne.Ch11.WeilMultiple
import ModularFormsKB.Milne.Ch11.TwistCount
import ModularFormsKB.Milne.Ch11.WeilConstantExtensionExists

/-!
# The lower bound for a fixed field of a group of automorphisms (one constant field)

Let $F/k$ be a function field over a finite field with $q$ elements, $k$ exact, of genus $g$, and
$H \le \Gamma$ finite groups of $k$-automorphisms of $F$ such that $F^\Gamma$ has genus $0$. If $q$ is a square and
$q > (g+1)^4$, then (`card_degree_one_fixedField_ge`)
$$N_1(F^H) \ge q + 1 - (|\Gamma| - 1)(2g+1)\sqrt q.$$

Proof (Bombieri; Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., proof of Theorem 5.2.3
[unverified numbering]): take $F' = F \cdot k'$ with $[k':k] = |\Gamma|$ and the twists $F_\tau$ by
$\tau \otimes \mathrm{Frobenius}$. Each $F_\tau$ is a function field of genus $g$ over $k$, so Bombieri's upper bound
(`bombieriUpperBound`) gives $N_1(F_\tau) \le q + 1 + (2g+1)\sqrt q$. The twisting identity
(`sum_card_degree_one_twistField`) for $\Gamma$ and $N_1(F^\Gamma) = q+1$ (genus $0$) give
$\sum_{\tau\in\Gamma} N_1(F_\tau) = |\Gamma|(q+1)$, hence $N_1(F_\tau) \ge q + 1 - (|\Gamma|-1)(2g+1)\sqrt q$ for every
$\tau$; the identity for $H$ gives $|H| N_1(F^H) = \sum_{\tau \in H} N_1(F_\tau)$.
-/

open TauCeti Module IntermediateField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ModularFormsKB.Milne

universe u v

/-- An intermediate field of an exact extension is exact. -/
theorem isIntegrallyClosedIn_intermediateField {k E : Type*} [Field k] [Field E] [Algebra k E]
    (hex : IsIntegrallyClosedIn k E) (M : IntermediateField k E) : IsIntegrallyClosedIn k M := by
  refine isIntegrallyClosedIn_iff.mpr ⟨(algebraMap k M).injective, fun {x} hx => ?_⟩
  have hxE : IsIntegral k (x : E) := by
    have := hx.map (IsScalarTower.toAlgHom k M E)
    simpa using this
  obtain ⟨c, hc⟩ := (isIntegrallyClosedIn_iff.mp hex).2 hxE
  exact ⟨c, Subtype.ext (by rw [← hc]; rfl)⟩

/-- A function field of genus $0$ with exact constants has $q + 1$ rational places. -/
theorem card_degree_one_of_genus_eq_zero {k : Type u} {L : Type v} [Field k] [Finite k] [Field L]
    [Algebra k L] (hL : IsFunctionField k L) (hex : IsIntegrallyClosedIn k L) (hg : genus k L = 0) :
    (Nat.card {P : Place k L // P.degree = 1} : ℝ) = Nat.card k + 1 := by
  obtain ⟨α, -, -, hN, -⟩ := (weilZetaRationality_of_zetaLPolynomial
    (zetaLPolynomial_of_schmidt schmidtDegreeOne) zetaNewtonIdentity).rational k L hL hex
  have h1 := hN 1 le_rfl
  have hempty : IsEmpty (Fin (2 * genus k L)) := by rw [hg, mul_zero]; infer_instance
  rw [Finset.univ_eq_empty, Finset.sum_empty, sub_zero, pow_one] at h1
  have hc : curvePointCount k L 1 = Nat.card {P : Place k L // P.degree = 1} := by
    simp [curvePointCount]
  rw [hc] at h1
  have h2 : ((Nat.card {P : Place k L // P.degree = 1} : ℝ) : ℂ) = ((Nat.card k + 1 : ℝ) : ℂ) := by
    push_cast; rw [h1]; ring
  exact_mod_cast Complex.ofReal_injective h2

/-- The rational places of isomorphic function fields correspond. -/
theorem card_degree_one_congr {k L L' : Type*} [Field k] [Field L] [Field L'] [Algebra k L] [Algebra k L']
    (e : L ≃ₐ[k] L') :
    Nat.card {P : Place k L // P.degree = 1} = Nat.card {P : Place k L' // P.degree = 1} :=
  Nat.card_congr ((Place.mapEquiv e).subtypeEquiv fun P => by
    rw [Place.mapEquiv_apply, Place.degree_map])

section Twists

variable {k : Type u} {F : Type v} {k' F' : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
  [Field k'] [Field F'] [Algebra k k'] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Finite k'] [Algebra.IsSeparable k k']
  (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (hc : constantCompositum F k' F' = ⊤)
  {ρ : k' ≃ₐ[k] k'} (hρq : ∀ c, ρ c = c ^ Nat.card k)

include hF hρq in
/-- Bombieri's upper bound for each twist. -/
theorem card_degree_one_twistField_le (hq : IsSquare (Nat.card k))
    (hbig : (genus k F + 1) ^ 4 < Nat.card k) {τ : F ≃ₐ[k] F}
    (hgm : twistAut hex hc τ ρ ^ finrank k k' = 1) :
    (Nat.card {R : Place k (twistField (twistAut hex hc τ ρ)) // R.degree = 1} : ℝ) ≤
      Nat.card k + 1 + (2 * genus k F + 1) * Real.sqrt (Nat.card k) := by
  have hρ := orderOf_of_forall hρq
  have hF'k' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top hc
  have hex' : IsIntegrallyClosedIn k' F' := IsIntegrallyClosedIn.of_constantCompositum_eq_top hex hc
  have hgF' : genus k' F' = genus k F := genus_eq_genus_of_constantCompositum_eq_top hF hex hc
  have hgρ := twistAut_algebraMap_right hex hc τ ρ
  have hT := isFunctionField_twistField _ hgm hF'k'
  have hexT := isIntegrallyClosedIn_twistField _ ρ hgρ hρ hex'
  have hgT : genus k (twistField (twistAut hex hc τ ρ)) = genus k F := by
    rw [genus_twistField _ ρ hgρ hρ hgm hF'k' hex', hgF']
  have := bombieriUpperBound.bound k (twistField (twistAut hex hc τ ρ)) hT hexT hq
    (by rw [hgT]; exact hbig)
  rw [hgT] at this
  exact this

include hF hρq in
/-- The combinatorial core: an upper bound $U$ for every twist gives
$N_1(F^H) \ge |\Gamma| N_1(F^\Gamma) - (|\Gamma| - 1) U$. -/
theorem card_degree_one_fixedField_ge_aux (Γ : Subgroup (F ≃ₐ[k] F)) [Fintype Γ]
    (H : Subgroup (F ≃ₐ[k] F)) [Fintype H] (hH : H ≤ Γ) (hdeg : finrank k k' = Nat.card Γ) (U : ℝ)
    (hupper : ∀ τ ∈ Γ,
      (Nat.card {R : Place k (twistField (twistAut hex hc τ ρ)) // R.degree = 1} : ℝ) ≤ U) :
    (Nat.card Γ : ℝ) * Nat.card {P : Place k (twistBase hex hc Γ) // P.degree = 1} -
        (Nat.card Γ - 1) * U ≤ Nat.card {P : Place k (twistBase hex hc H) // P.degree = 1} := by
  classical
  have hm1 : 1 ≤ Nat.card Γ := Nat.card_pos
  have hsumΓ := sum_card_degree_one_twistField hF hex hc Γ hρq (by rw [hdeg])
  have hsumH := sum_card_degree_one_twistField hF hex hc H hρq
    (by rw [hdeg]; exact Subgroup.card_dvd_of_le hH)
  have hlower : ∀ σ ∈ Γ, (Nat.card Γ : ℝ) * Nat.card {P : Place k (twistBase hex hc Γ) // P.degree = 1} -
      (Nat.card Γ - 1) * U ≤
      Nat.card {R : Place k (twistField (twistAut hex hc σ ρ)) // R.degree = 1} := by
    intro σ hσ
    have hsum := congrArg (fun n : ℕ => (n : ℝ)) hsumΓ
    simp only [Nat.cast_sum, Nat.cast_mul] at hsum
    have hsplit := Finset.add_sum_erase (Finset.univ : Finset Γ)
      (fun τ : Γ => (Nat.card {R : Place k (twistField (twistAut hex hc τ ρ)) // R.degree = 1} : ℝ))
      (Finset.mem_univ ⟨σ, hσ⟩)
    have hrest : ∑ τ ∈ Finset.univ.erase (⟨σ, hσ⟩ : Γ),
        (Nat.card {R : Place k (twistField (twistAut hex hc τ ρ)) // R.degree = 1} : ℝ) ≤
        (Nat.card Γ - 1) * U := by
      calc _ ≤ ∑ τ ∈ Finset.univ.erase (⟨σ, hσ⟩ : Γ), U := Finset.sum_le_sum fun τ _ => hupper τ τ.2
        _ = (Nat.card Γ - 1) * U := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
              nsmul_eq_mul, ← Nat.card_eq_fintype_card, Nat.cast_sub hm1, Nat.cast_one]
    linarith
  have hHsum := congrArg (fun n : ℕ => (n : ℝ)) hsumH
  simp only [Nat.cast_sum, Nat.cast_mul] at hHsum
  have hHlow : (Nat.card H : ℝ) * ((Nat.card Γ : ℝ) *
      Nat.card {P : Place k (twistBase hex hc Γ) // P.degree = 1} - (Nat.card Γ - 1) * U) ≤
      ∑ τ : H, (Nat.card {R : Place k (twistField (twistAut hex hc τ ρ)) // R.degree = 1} : ℝ) := by
    calc _ = ∑ _τ : H, ((Nat.card Γ : ℝ) *
          Nat.card {P : Place k (twistBase hex hc Γ) // P.degree = 1} - (Nat.card Γ - 1) * U) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
      _ ≤ _ := Finset.sum_le_sum fun τ _ => hlower τ (hH τ.2)
  rw [hHsum] at hHlow
  have hHpos : (0 : ℝ) < Nat.card H := by exact_mod_cast Nat.card_pos
  exact le_of_mul_le_mul_left hHlow hHpos

end Twists

/-- **The lower bound for a fixed field, over one constant field.** -/
theorem card_degree_one_fixedField_ge {k : Type u} {F : Type v} [Field k] [Finite k] [Field F]
    [Algebra k F] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (Γ : Subgroup (F ≃ₐ[k] F)) [Finite Γ] (H : Subgroup (F ≃ₐ[k] F)) (hH : H ≤ Γ)
    (hK : genus k (fixedField Γ) = 0) (hq : IsSquare (Nat.card k))
    (hbig : (genus k F + 1) ^ 4 < Nat.card k) :
    (Nat.card k : ℝ) + 1 - (Nat.card Γ - 1) * (2 * genus k F + 1) * Real.sqrt (Nat.card k) ≤
      Nat.card {P : Place k (fixedField H) // P.degree = 1} := by
  classical
  letI := Fintype.ofFinite Γ
  have hHfin : Finite H :=
    Finite.of_injective (Subgroup.inclusion hH) (Subgroup.inclusion_injective hH)
  letI := Fintype.ofFinite H
  have hm1 : 1 ≤ Nat.card Γ := Nat.card_pos
  obtain ⟨F', k', hfd, hdeg, hc⟩ := exists_constantCompositum_finrank_eq (k := k) (F := F) _ hm1
  have : Finite k' := Module.finite_of_finite k
  letI := Fintype.ofFinite k
  obtain ⟨ρ, hρq⟩ : ∃ ρ : k' ≃ₐ[k] k', ∀ c, ρ c = c ^ Nat.card k :=
    ⟨FiniteField.frobeniusAlgEquivOfAlgebraic k k', fun c => by
      rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Nat.card_eq_fintype_card]⟩
  have hiso : ∀ M : Subgroup (F ≃ₐ[k] F), [Finite M] → Nonempty
      (fixedField M ≃ₐ[k] twistBase hex hc M) := fun M _ =>
    ⟨((fixedField M).equivMap (IsScalarTower.toAlgHom k F F')).trans
      (IntermediateField.equivOfEq (fixedField_twistGroup_top hex hc M))⟩
  have hKcount : (Nat.card {P : Place k (twistBase hex hc Γ) // P.degree = 1} : ℝ) =
      Nat.card k + 1 := by
    obtain ⟨e⟩ := hiso Γ
    have hKF : IsFunctionField k (fixedField Γ) := hF.fixedField Γ
    rw [← card_degree_one_congr e]
    exact card_degree_one_of_genus_eq_zero hKF (isIntegrallyClosedIn_intermediateField hex _) hK
  have hHcount : Nat.card {P : Place k (twistBase hex hc H) // P.degree = 1} =
      Nat.card {P : Place k (fixedField H) // P.degree = 1} := by
    obtain ⟨e⟩ := hiso H
    exact (card_degree_one_congr e).symm
  have key := card_degree_one_fixedField_ge_aux hF hex hc hρq Γ H hH hdeg _
    (fun τ hτ => card_degree_one_twistField_le hF hex hc hρq hq hbig
      (pow_eq_one_of_dvd hex hc (by rw [hdeg]) hτ ρ))
  rw [hKcount, hHcount] at key
  linarith

end ModularFormsKB.Milne
