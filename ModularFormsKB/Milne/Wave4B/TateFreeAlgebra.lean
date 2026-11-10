import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Nakayama
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Finite.Basic

/-!
# Linear algebra for Remark 12.12 (Milne): cyclic vectors and Nakayama over `ℤ_ℓ`

Two algebraic lemmas used in `ModularFormsKB.Milne.Wave4B.TateModuleFree` (the corrected Remark 12.12 of
J. S. Milne, *Modular Functions and Modular Forms*, `milne2017mf`, Section 12, pdf p. 125):

* `exists_cyclic_of_ne_smul`: on a group `A` killed by a prime `ℓ` with `ℓ²` elements, an additive endomorphism
  `g` that is not multiplication by an integer has a cyclic vector: some `P` with `A = ℤ P + ℤ g(P)`.
* `basis_of_forall_mod`: in a free `ℤ_ℓ`-module `T` of rank 2, if `t, u` span `T` modulo `ℓ T`, then `t, u` are a
  basis (Nakayama, then a surjection between free modules of the same finite rank is injective).
-/

namespace ModularFormsKB.Milne.Wave4B

/-- On a two-dimensional vector space, an endomorphism without a cyclic vector is a scalar. -/
theorem exists_eq_smul_of_forall_not_cyclic {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (hfin : Module.finrank K V = 2) (G : V →ₗ[K] V)
    (hno : ∀ v : V, ∃ x : V, ∀ a b : K, a • v + b • G v ≠ x) : ∃ c : K, G = c • 1 := by
  have key : ∀ v : V, ¬ LinearIndependent K ![v, G v] := fun v hv ↦ by
    have hfd : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hfin
    obtain ⟨x, hx⟩ := hno v
    have hspan : Submodule.span K (Set.range ![v, G v]) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card hv]
      simp [hfin]
    have hxm : x ∈ Submodule.span K {v, G v} := by
      rw [Matrix.range_cons_cons_empty] at hspan
      rw [hspan]; trivial
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 hxm
    exact hx a b hab
  exact LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent key

/-- **Cyclic vectors.** Let `A` be an abelian group with `ℓ • a = 0` for all `a`, having exactly `ℓ ^ 2` elements
(`ℓ` prime), and `g : A →+ A` not of the form `a ↦ c • a` for an integer `c`. Then some `P` generates `A` together
with `g P`. -/
theorem exists_cyclic_of_ne_smul {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A] [Finite A]
    (hA : ∀ a : A, ℓ • a = 0) (hcard : Nat.card A = ℓ ^ 2) (g : A →+ A)
    (hg : ∀ c : ℤ, ∃ a : A, g a ≠ c • a) :
    ∃ P : A, ∀ x : A, ∃ a b : ℤ, x = a • P + b • g P := by
  letI : Module (ZMod ℓ) A := AddCommGroup.zmodModule hA
  have hz : ∀ (c : ZMod ℓ) (x : A), c • x = ((c.val : ℤ)) • x := by
    intro c x
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (ZMod ℓ), ZMod.natCast_zmod_val]
  have hfin : Module.finrank (ZMod ℓ) A = 2 := by
    have := Fintype.ofFinite A
    have := Module.card_eq_pow_finrank (K := ZMod ℓ) (V := A)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard, Nat.card_zmod] at this
    exact (Nat.pow_right_injective hℓ.out.two_le this).symm
  by_contra hno
  push_neg at hno
  obtain ⟨c, hc⟩ := exists_eq_smul_of_forall_not_cyclic hfin (g.toZModLinearMap ℓ) fun v ↦ by
    obtain ⟨x, hx⟩ := hno v
    refine ⟨x, fun a b hab ↦ hx a.val b.val ?_⟩
    rw [← hab, hz a, hz b]
    rfl
  obtain ⟨a, ha⟩ := hg (c.val : ℤ)
  apply ha
  have := LinearMap.congr_fun hc a
  change g a = _ at this
  rw [this, LinearMap.smul_apply, Module.End.one_apply, hz]

/-- **Nakayama over `ℤ_ℓ` in rank 2.** In a free `ℤ_ℓ`-module of rank 2, two elements that span modulo `ℓ` form a
basis. -/
theorem basis_of_forall_mod {ℓ : ℕ} [Fact ℓ.Prime] {T : Type*} [AddCommGroup T] [Module ℤ_[ℓ] T]
    [Module.Free ℤ_[ℓ] T] [Module.Finite ℤ_[ℓ] T] (hr : Module.finrank ℤ_[ℓ] T = 2) (t u : T)
    (h : ∀ x : T, ∃ (a b : ℤ) (y : T), x = a • t + b • u + ℓ • y) :
    LinearIndependent ℤ_[ℓ] ![t, u] ∧ Submodule.span ℤ_[ℓ] {t, u} = ⊤ := by
  have hspan : Submodule.span ℤ_[ℓ] {t, u} = ⊤ := by
    have hle : (⊤ : Submodule ℤ_[ℓ] T) ≤ Submodule.span ℤ_[ℓ] {t, u} ⊔
        (IsLocalRing.maximalIdeal ℤ_[ℓ]) • (⊤ : Submodule ℤ_[ℓ] T) := by
      intro x _
      obtain ⟨a, b, y, rfl⟩ := h x
      refine Submodule.add_mem_sup ?_ ?_
      · refine Submodule.add_mem _ ?_ ?_
        · rw [← Int.cast_smul_eq_zsmul ℤ_[ℓ]]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
        · rw [← Int.cast_smul_eq_zsmul ℤ_[ℓ]]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · rw [← Nat.cast_smul_eq_nsmul ℤ_[ℓ]]
        refine Submodule.smul_mem_smul ?_ trivial
        rw [PadicInt.maximalIdeal_eq_span_p]
        exact Ideal.subset_span rfl
    have := Submodule.le_of_le_smul_of_le_jacobson (Module.Finite.fg_top)
      (by rw [← Ideal.jacobson_bot, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) hle
    exact top_le_iff.1 this
  refine ⟨?_, hspan⟩
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · rw [Matrix.range_cons_cons_empty, hspan]
  · simp [hr]

end ModularFormsKB.Milne.Wave4B
