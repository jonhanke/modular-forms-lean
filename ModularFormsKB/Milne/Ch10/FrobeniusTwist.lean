import ModularFormsKB.Milne.Ch10.Correspondences
import TauCeti.AlgebraicGeometry.Frobenius.Perfect
import TauCeti.AlgebraicGeometry.Frobenius.UniversalHomeomorphism

/-!
# Milne, Proposition 10.2: the Frobenius twist over a perfect field

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 10, pdf p. 106.

Over a perfect field $k$ of characteristic $p$ the iterated Frobenius of $\operatorname{Spec} k$ is an isomorphism, so
the base change $C^{(q)} = C \times_{k, F^n} k$ maps isomorphically onto $C$ by the first projection
(`isIso_frobeniusTwist_fst`), and $\Pi_q$ followed by this projection is the $n$-fold absolute Frobenius of $C$
(`frobeniusMap_fst`). Consequences proved here:

- $C^{(q)}$ is integral when $C$ is (`isIntegral_frobeniusTwist`);
- $\Pi_q$ is surjective, hence dominant (`isDominant_frobeniusMap`);
- $C^{(q)} \to \operatorname{Spec} k$ is universally closed when $C \to \operatorname{Spec} k$ is
  (`universallyClosed_frobeniusTwistStructure`).

`frobeniusFactorization_of` reduces `FrobeniusFactorization` to two named statements that carry the remaining
content: `FrobeniusTwistCurveProperties` (the twist is a complete regular curve and $\Pi_q$ is purely inseparable of
degree $q$) and `PurelyInseparableFactorization` (the factorization of a purely inseparable map of degree $q$, which
needs Theorem 7.2, `CurveFunctionFieldEquivalence`).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace ModularFormsKB.Milne

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
  (hk : (p : Γ(Spec (CommRingCat.of k), ⊤)) = 0)

include hk in
/-- The characteristic of $k$ is $p$. -/
theorem charP_of_natCast_eq_zero : CharP k p := by
  have h : ((p : ℕ) : k) = 0 := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom hk
    simpa using this
  exact (CharP.charP_iff_prime_eq_zero (Fact.out)).mpr h

/-- Over a perfect field the iterated Frobenius of $\operatorname{Spec} k$ is an isomorphism. -/
theorem isIso_iterateFrobenius_spec [PerfectField k] (n : ℕ) :
    IsIso ((Spec (CommRingCat.of k)).iterateFrobenius p hk n) := by
  haveI := charP_of_natCast_eq_zero k p hk
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  haveI : IsIso ((Spec (CommRingCat.of k)).frobenius p hk) :=
    (Scheme.isPerfect_iff_isIso hk).mp inferInstance
  induction n with
  | zero => rw [Scheme.iterateFrobenius_zero]; infer_instance
  | succ n ih => rw [Scheme.iterateFrobenius_succ]; infer_instance

variable {C : Scheme.{u}} (f : C ⟶ Spec (CommRingCat.of k))

/-- **$C^{(q)} \cong C$ as schemes**: the first projection is an isomorphism over a perfect field. -/
theorem isIso_frobeniusTwist_fst [PerfectField k] (n : ℕ) :
    IsIso (pullback.fst f ((Spec (CommRingCat.of k)).iterateFrobenius p hk n)) := by
  haveI := isIso_iterateFrobenius_spec k p hk n
  infer_instance

/-- $\Pi_q$ followed by the projection $C^{(q)} \to C$ is the $n$-fold absolute Frobenius of $C$. -/
theorem frobeniusMap_fst (n : ℕ) :
    frobeniusMap k p hk f n ≫ pullback.fst _ _ =
      C.iterateFrobenius p (Scheme.natCast_eq_zero_of_hom f hk) n :=
  Scheme.Hom.iterateRelativeFrobenius_fst f p hk n

/-- **$C^{(q)}$ is integral** when $C$ is and $k$ is perfect. -/
theorem isIntegral_frobeniusTwist [PerfectField k] [IsIntegral C] (n : ℕ) :
    IsIntegral (frobeniusTwist k p hk f n) := by
  haveI := isIso_frobeniusTwist_fst k p hk f n
  haveI : Nonempty (frobeniusTwist k p hk f n) :=
    ⟨(inv (pullback.fst f ((Spec (CommRingCat.of k)).iterateFrobenius p hk n))) (Nonempty.some inferInstance)⟩
  exact isIntegral_of_isOpenImmersion (pullback.fst f _)

/-- **$\Pi_q$ is surjective**, hence dominant. -/
theorem surjective_frobeniusMap [PerfectField k] (n : ℕ) : Surjective (frobeniusMap k p hk f n) := by
  haveI := isIso_frobeniusTwist_fst k p hk f n
  have h : frobeniusMap k p hk f n =
      C.iterateFrobenius p (Scheme.natCast_eq_zero_of_hom f hk) n ≫
        inv (pullback.fst f ((Spec (CommRingCat.of k)).iterateFrobenius p hk n)) := by
    exact (IsIso.eq_comp_inv _).mpr (frobeniusMap_fst k p hk f n)
  rw [h]
  infer_instance

/-- **$\Pi_q$ is dominant.** -/
theorem isDominant_frobeniusMap [PerfectField k] (n : ℕ) : IsDominant (frobeniusMap k p hk f n) := by
  haveI := surjective_frobeniusMap k p hk f n
  infer_instance

/-- **$C^{(q)} \to \operatorname{Spec} k$ is universally closed** when $C \to \operatorname{Spec} k$ is. -/
theorem universallyClosed_frobeniusTwistStructure [PerfectField k] [UniversallyClosed f] (n : ℕ) :
    UniversallyClosed (frobeniusTwistStructure k p hk f n) := by
  haveI := isIso_iterateFrobenius_spec k p hk n
  haveI := isIso_frobeniusTwist_fst k p hk f n
  have h : frobeniusTwistStructure k p hk f n =
      pullback.fst f ((Spec (CommRingCat.of k)).iterateFrobenius p hk n) ≫ f ≫
        inv ((Spec (CommRingCat.of k)).iterateFrobenius p hk n) := by
    rw [← Category.assoc, pullback.condition, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

/-- **The twist is a complete regular curve and $\Pi_q$ is purely inseparable of degree $q$** (the remaining content
of the first half of Proposition 10.2), as a named statement. -/
@[kb "milne2017mf" "Section 10, Proposition 10.2 (pdf p. 106), properties of C^(q) and Π_q"]
structure FrobeniusTwistCurveProperties [IsAlgClosed k] : Prop where
  curve : ∀ {C : Scheme.{u}} [IsIntegral C] (f : C ⟶ Spec (CommRingCat.of k)), IsCompleteRegularCurve k f →
    ∀ (n : ℕ) [IsIntegral (frobeniusTwist k p hk f n)] [IsDominant (frobeniusMap k p hk f n)],
      IsCompleteRegularCurve k (frobeniusTwistStructure k p hk f n) ∧
      IsPurelyInseparableMorphism (frobeniusMap k p hk f n) ∧ morphismDegree (frobeniusMap k p hk f n) = p ^ n

/-- **Factorization of purely inseparable maps through the Frobenius** (the second half of Proposition 10.2), as a
named statement; Milne's proof identifies $k(C')$ with $k(C)^q$ and uses Theorem 7.2. -/
@[kb "milne2017mf" "Section 10, Proposition 10.2 (pdf p. 106), factorization"]
structure PurelyInseparableFactorization [IsAlgClosed k] : Prop where
  factors : ∀ {C C' : Scheme.{u}} [IsIntegral C] [IsIntegral C'] (f : C ⟶ Spec (CommRingCat.of k))
    (f' : C' ⟶ Spec (CommRingCat.of k)), IsCompleteRegularCurve k f → IsCompleteRegularCurve k f' →
    ∀ (φ : C ⟶ C') [IsDominant φ], φ ≫ f' = f → IsPurelyInseparableMorphism φ →
    ∀ n : ℕ, morphismDegree φ = p ^ n →
      ∃ e : frobeniusTwist k p hk f n ≅ C', e.hom ≫ f' = frobeniusTwistStructure k p hk f n ∧
        frobeniusMap k p hk f n ≫ e.hom = φ

/-- **Proposition 10.2 from the two named statements**: integrality of $C^{(q)}$ and dominance of $\Pi_q$ are proved
here. -/
theorem frobeniusFactorization_of [IsAlgClosed k] (h₁ : FrobeniusTwistCurveProperties k p hk)
    (h₂ : PurelyInseparableFactorization k p hk) : FrobeniusFactorization k p hk where
  frobenius := by
    intro C _ f hf n
    haveI := isIntegral_frobeniusTwist k p hk f n
    haveI := isDominant_frobeniusMap k p hk f n
    exact ⟨inferInstance, inferInstance, h₁.curve f hf n⟩
  factors := h₂.factors

end ModularFormsKB.Milne
