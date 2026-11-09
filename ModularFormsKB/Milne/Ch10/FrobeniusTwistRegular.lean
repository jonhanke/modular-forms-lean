import ModularFormsKB.Milne.Ch10.FrobeniusTwist

/-!
# Milne, Proposition 10.2: regularity and separatedness of the Frobenius twist

Over a perfect field the projection $C^{(q)} \to C$ is an isomorphism of schemes
(`isIso_frobeniusTwist_fst`), so the local rings of $C^{(q)}$ at closed points are those of $C$
(`isRegularVariety_frobeniusTwistStructure`), and the structure morphism $C^{(q)} \to \operatorname{Spec} k$ is the
composite of that isomorphism, $C \to \operatorname{Spec} k$ and the inverse of the Frobenius of
$\operatorname{Spec} k$, hence separated when $C \to \operatorname{Spec} k$ is (`isSeparated_frobeniusTwistStructure`).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace ModularFormsKB.Milne

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
  (hk : (p : Γ(Spec (CommRingCat.of k), ⊤)) = 0) {C : Scheme.{u}} (f : C ⟶ Spec (CommRingCat.of k))

/-- **The twist is regular** when $C$ is. -/
theorem isRegularVariety_frobeniusTwistStructure [PerfectField k] (hf : IsRegularVariety k f) (n : ℕ) :
    IsRegularVariety k (frobeniusTwistStructure k p hk f n) := by
  have := isIso_frobeniusTwist_fst k p hk f n
  intro x hx
  set e := pullback.fst f ((Spec (CommRingCat.of k)).iterateFrobenius p hk n) with he
  have hcl : IsClosed ({e x} : Set C) := by
    have : ({e x} : Set C) = e '' {x} := by simp
    rw [this]
    exact (Scheme.homeoOfIso (asIso e)).isClosed_image.mpr hx
  have h1 := hf (e x) hcl
  have : IsIso (e.stalkMap x) := inferInstance
  have := h1
  exact IsRegularLocalRing.of_ringEquiv (asIso (e.stalkMap x)).commRingCatIsoToRingEquiv

/-- **The twist is separated over $k$** when $C$ is. -/
theorem isSeparated_frobeniusTwistStructure [PerfectField k] [IsSeparated f] (n : ℕ) :
    IsSeparated (frobeniusTwistStructure k p hk f n) := by
  have := isIso_iterateFrobenius_spec k p hk n
  have := isIso_frobeniusTwist_fst k p hk f n
  have h : frobeniusTwistStructure k p hk f n =
      pullback.fst f ((Spec (CommRingCat.of k)).iterateFrobenius p hk n) ≫ f ≫
        inv ((Spec (CommRingCat.of k)).iterateFrobenius p hk n) := by
    rw [← Category.assoc, pullback.condition, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

/-- **The twist is a curve and $\Pi_q$ is purely inseparable of degree $q$** (what remains of
`FrobeniusTwistCurveProperties` once regularity and completeness are proved), as a named statement. -/
@[kb "milne2017mf" "Section 10, Proposition 10.2 (pdf p. 106), C^(q) is a curve and Π_q has degree q"]
structure FrobeniusTwistCurveDegree [IsAlgClosed k] : Prop where
  curve : ∀ {C : Scheme.{u}} [IsIntegral C] (f : C ⟶ Spec (CommRingCat.of k)), IsCompleteRegularCurve k f →
    ∀ (n : ℕ) [IsIntegral (frobeniusTwist k p hk f n)] [IsDominant (frobeniusMap k p hk f n)],
      IsCurve k (frobeniusTwistStructure k p hk f n) ∧
      IsPurelyInseparableMorphism (frobeniusMap k p hk f n) ∧ morphismDegree (frobeniusMap k p hk f n) = p ^ n

/-- `FrobeniusTwistCurveProperties` from `FrobeniusTwistCurveDegree`: regularity and completeness of the twist are
proved. -/
theorem frobeniusTwistCurveProperties_of [IsAlgClosed k] (h : FrobeniusTwistCurveDegree k p hk) :
    FrobeniusTwistCurveProperties k p hk where
  curve := by
    intro C _ f hf n _ _
    obtain ⟨hc, hpi, hdeg⟩ := h.curve f hf n
    have : UniversallyClosed f := hf.2.2
    exact ⟨⟨hc, isRegularVariety_frobeniusTwistStructure k p hk f hf.2.1 n,
      universallyClosed_frobeniusTwistStructure k p hk f n⟩, hpi, hdeg⟩

/-- **Proposition 10.2** from `FrobeniusTwistCurveDegree` and `PurelyInseparableFactorization`. -/
theorem frobeniusFactorization_of_curveDegree [IsAlgClosed k] (h₁ : FrobeniusTwistCurveDegree k p hk)
    (h₂ : PurelyInseparableFactorization k p hk) : FrobeniusFactorization k p hk :=
  frobeniusFactorization_of k p hk (frobeniusTwistCurveProperties_of k p hk h₁) h₂

end ModularFormsKB.Milne
