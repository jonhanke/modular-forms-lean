import TauCeti.FieldTheory.FunctionField.ConstantExtension.Fibre
import ModularFormsKB.Milne.Ch11.ZetaFiniteField

/-!
# Rational places of a constant field extension

For a function field $F$ over a finite field $k$, $k$ algebraically closed in $F$, and a constant field extension
$F' = F\cdot k'$ with $[k' : k] = r$, the rational places of $F'/k'$ are counted by
$N_1(F') = N_r(F) = \sum_{d \mid r} d\,B_d(F)$ (Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., proof of
Lemma 5.1.9 [unverified numbering]): a place $P$ of $F$ of degree $d$ has a rational place of $F'$ above it only
if its residue field $\mathbb F_{q^d}$ embeds in $k' = \mathbb F_{q^r}$, i.e. $d \mid r$, and then it has exactly
$d$ places above it, all rational (Tau Ceti, `ncard_setOf_restrict_eq_eq_degree_of_constantCompositum_eq_top`,
`degree_eq_one_of_constantCompositum_eq_top`). This is how a bound for degree-one places, applied to $F\cdot k'$
(same genus, Tau Ceti `genus_eq_genus_of_constantCompositum_eq_top`), becomes a bound for $N_r(F)$.
-/

open TauCeti

namespace ModularFormsKB.Milne

universe u u' v v'

/-- $N_1(F \cdot k') = N_{[k':k]}(F)$. -/
theorem card_degree_one_constantCompositum {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
    [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
    [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [Finite k] [FiniteDimensional k k']
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) :
    Nat.card {P' : Place k' F' // P'.degree = 1} = curvePointCount k F (Module.finrank k k') := by
  classical
  have : FiniteDimensional F F' := TauCeti.finiteDimensional_of_constantCompositum_eq_top (k := k) h
  have : Algebra.IsIntegral F F' := inferInstance
  have : Finite k' := Module.finite_of_finite k
  have : Algebra.IsAlgebraic k k' := inferInstance
  have : Normal k k' := inferInstance
  have : Algebra.IsSeparable k k' := inferInstance
  set r := Module.finrank k k' with hr
  have hrpos : 0 < r := Module.finrank_pos
  -- rational places lie over places of degree dividing `r`
  have key1 : ∀ P' : Place k' F', P'.degree = 1 → (P'.restrict k F).degree ∣ r := by
    intro P' hP'
    have := Place.finrank_mul_degree_eq_relativeDegree_mul_degree_restrict k F P'
    rw [hP', mul_one] at this
    exact ⟨Place.relativeDegree k F P', by rw [hr, this, mul_comm]⟩
  have key2 : ∀ P : Place k F, P.degree ∣ r → Nonempty (P.ResidueField →ₐ[k] k') := by
    intro P hP
    have := P.finiteDimensional_residueField hF
    refine FiniteField.nonempty_algHom_of_finrank_dvd ?_
    rw [← Place.degree_eq_finrank]
    exact hP
  have hfibfin : ∀ P : Place k F, {P' : Place k' F' | P'.restrict k F = P}.Finite :=
    fun P => Place.finite_setOf_restrict_eq_of_constantCompositum_eq_top hF h P
  have key3 : ∀ P : Place k F, P.degree ∣ r →
      {P' : Place k' F' | P'.restrict k F = P}.ncard = P.degree := by
    intro P hP
    obtain ⟨φ⟩ := key2 P hP
    exact Place.ncard_setOf_restrict_eq_eq_degree_of_constantCompositum_eq_top hF hex h P φ
  have key4 : ∀ P' : Place k' F', (P'.restrict k F).degree ∣ r → P'.degree = 1 := by
    intro P' hP'
    obtain ⟨φ⟩ := key2 _ hP'
    exact Place.degree_eq_one_of_constantCompositum_eq_top hF hex h P' φ
  -- the finite set of places below
  have hTfin : {P : Place k F | P.degree ∈ r.divisors}.Finite :=
    (Place.finite_setOf_degree_le hF r).subset fun P hP =>
      Nat.divisor_le (Finset.mem_coe.mp hP)
  set T := hTfin.toFinset with hT
  have hmemT : ∀ P, P ∈ T ↔ P.degree ∈ r.divisors := fun P => by simp [hT]
  have hAfin : {P' : Place k' F' | P'.degree = 1}.Finite := by
    refine (hTfin.biUnion fun P _ => hfibfin P).subset fun P' hP' => ?_
    refine Set.mem_biUnion (x := P'.restrict k F) ?_ rfl
    have := key1 P' hP'
    simpa [Nat.mem_divisors, hrpos.ne'] using this
  set A := hAfin.toFinset with hA
  have hmemA : ∀ P', P' ∈ A ↔ P'.degree = 1 := fun P' => by simp [hA]
  have hcardA : Nat.card {P' : Place k' F' // P'.degree = 1} = A.card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun P' => (hmemA P').symm)
  have hmaps : ∀ P' ∈ A, P'.restrict k F ∈ T := by
    intro P' hP'
    rw [hmemT, Nat.mem_divisors]
    exact ⟨key1 P' ((hmemA _).mp hP'), hrpos.ne'⟩
  have hfib : ∀ P ∈ T, (A.filter fun P' => P'.restrict k F = P).card = P.degree := by
    intro P hP
    have hd : P.degree ∣ r := (Nat.mem_divisors.mp ((hmemT P).mp hP)).1
    rw [← key3 P hd, Set.ncard_eq_toFinset_card _ (hfibfin P)]
    congr 1
    ext P'
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hmemA]
    constructor
    · exact fun h => h.2
    · intro h'
      exact ⟨key4 P' (h' ▸ hd), h'⟩
  rw [hcardA, Finset.card_eq_sum_card_fiberwise hmaps,
    Finset.sum_congr rfl hfib]
  unfold curvePointCount
  rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := r.divisors) (g := Place.degree)
    (fun P hP => (hmemT P).mp hP)]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.sum_congr rfl (g := fun _ => d) (fun P hP => (Finset.mem_filter.mp hP).2),
    Finset.sum_const, smul_eq_mul, mul_comm]
  congr 1
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun P => by
    rw [Finset.mem_filter, hmemT]
    constructor
    · rintro ⟨_, h2⟩; exact h2
    · intro h2; exact ⟨by rw [h2]; exact hd, h2⟩)

end ModularFormsKB.Milne
