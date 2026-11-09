import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Baire.LocallyCompactRegular
import ModularFormsKB.Citation
/-!
# Milne, Chapter 1: continuous group actions

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §1 "Continuous group actions", pdf pp. 13–15.

* Lemma 1.1: `G ⧸ H` is Hausdorff if and only if `H` is closed. Mathlib has the direction "closed implies
  Hausdorff" (`QuotientGroup.instT2Space` style instances); here both directions.
* Proposition 1.2: for a continuous transitive action of a locally compact group with a countable base on a locally
  compact space, `G ⧸ Stab(x) → X`, `[g] ↦ g x`, is a homeomorphism. Mathlib has the open mapping theorem
  `isOpenMap_smul_of_sigmaCompact`; here the homeomorphism statement in the book's form.
* Lemma 1.3 (Baire): the book's form of Mathlib's Baire category theorem.

Following Bourbaki (as Milne says on p. 13), locally compact spaces are Hausdorff: the hypotheses carry `T2Space`.
-/

open Topology

namespace ModularFormsKB.Milne

section Lemma1_1

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Milne, Lemma 1.1.** For a subgroup `H` of a topological group `G`, the coset space `G ⧸ H` is Hausdorff if and
only if `H` is closed in `G`. -/
@[kb "milne2017mf" "Lemma 1.1, pdf p. 14"]
theorem quotient_t2Space_iff_isClosed (H : Subgroup G) :
    T2Space (G ⧸ H) ↔ IsClosed (H : Set G) := by
  constructor
  · intro h
    have := (QuotientGroup.t1Space_iff (N := H)).1 inferInstance
    exact this
  · intro h
    have : IsClosed (H : Set G) := h
    infer_instance

end Lemma1_1

section Prop1_2

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X : Type*} [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

/-- **Milne, Proposition 1.2.** Let `G` act continuously and transitively on `X`, with `G` and `X` locally compact
(hence Hausdorff, following Bourbaki) and `G` with a countable base. Then for every `x : X` the map
`G ⧸ Stab(x) → X`, `[g] ↦ g • x`, is a homeomorphism. -/
@[kb "milne2017mf" "Proposition 1.2, pdf p. 14"]
theorem exists_homeomorph_quotient_stabilizer [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [LocallyCompactSpace X] [T2Space X] [MulAction.IsPretransitive G X]
    (x : X) :
    ∃ e : G ⧸ MulAction.stabilizer G x ≃ₜ X, ∀ g : G, e (g : G ⧸ MulAction.stabilizer G x) = g • x := by
  let H := MulAction.stabilizer G x
  let f : G ⧸ H → X := Quotient.lift (fun g : G => g • x) (by
    intro a b hab
    have h : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.1 hab
    have h2 : (a⁻¹ * b) • x = x := h
    calc a • x = a • ((a⁻¹ * b) • x) := by rw [h2]
      _ = b • x := by rw [smul_smul, mul_inv_cancel_left])
  have hf : ∀ g : G, f (g : G ⧸ H) = g • x := fun g => rfl
  have hcont : Continuous f := by
    refine (QuotientGroup.isQuotientMap_mk H).continuous_iff.2 ?_
    exact (continuous_id.smul continuous_const : Continuous fun g : G => g • x)
  have hinj : Function.Injective f := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | _ a => ?_
    induction b using QuotientGroup.induction_on with | _ b => ?_
    rw [hf, hf] at hab
    apply QuotientGroup.eq.2
    show (a⁻¹ * b) • x = x
    rw [mul_smul, ← hab, inv_smul_smul]
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
    exact ⟨g, by rw [hf, hg]⟩
  have hopen : IsOpenMap f := by
    intro U hU
    have h1 : IsOpenMap (fun g : G => g • x) := isOpenMap_smul_of_sigmaCompact x
    have := h1 _ (QuotientGroup.isQuotientMap_mk H |>.continuous.isOpen_preimage _ hU)
    have e : (fun g : G => g • x) '' (((↑) : G → G ⧸ H) ⁻¹' U) = f '' U := by
      rw [show (fun g : G => g • x) = f ∘ ((↑) : G → G ⧸ H) from rfl, Set.image_comp,
        Set.image_preimage_eq _ QuotientGroup.mk_surjective]
    rwa [e] at this
  exact ⟨(Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopen,
    fun g => rfl⟩

end Prop1_2

/-- **Milne, Lemma 1.3 (Baire's theorem).** If a nonempty locally compact (Hausdorff) space is a countable union of
closed subsets, at least one of them has an interior point. Mathlib: `BaireSpace.of_t2Space_locallyCompactSpace`
and `nonempty_interior_of_iUnion_of_closed`. -/
@[kb "milne2017mf" "Lemma 1.3, pdf p. 15"]
theorem exists_nonempty_interior_of_iUnion_eq_univ {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [Nonempty X] (V : ℕ → Set X) (hV : ∀ n, IsClosed (V n))
    (hU : ⋃ n, V n = Set.univ) : ∃ n, (interior (V n)).Nonempty := by
  have := BaireSpace.of_t2Space_locallyCompactSpace (X := X)
  exact nonempty_interior_of_iUnion_of_closed hV hU

end ModularFormsKB.Milne
