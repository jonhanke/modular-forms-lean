import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import ModularFormsKB.Citation
/-!
# Andrianov–Zhuravlev, Chapter 4, Lemma 1.10: a common eigenvector of commuting operators

A. N. Andrianov and V. G. Zhuravlev, *Modular Forms and Hecke Operators* (`andrianovzhuravlev1995`), Chapter 4,
Lemma 1.10 (pdf p. 244): a nonzero finite-dimensional vector space over an algebraically closed field has a nonzero
common eigenvector for any finite family of pairwise commuting linear operators. The book's proof is induction on
the number of operators, passing to an eigenspace of the first one; we run the same induction inside an invariant
subspace (`exists_common_eigenvector_mem`).
-/

namespace ModularFormsKB.Andrianov

variable {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The induction behind Lemma 1.10: a nonzero subspace `W` invariant under pairwise commuting operators
`S_1, …, S_d` contains a nonzero common eigenvector. -/
theorem exists_common_eigenvector_mem : ∀ (d : ℕ) (S : Fin d → Module.End K V),
    (∀ i j, Commute (S i) (S j)) → ∀ W : Submodule K V, W ≠ ⊥ → (∀ i, ∀ w ∈ W, S i w ∈ W) →
    ∃ v ∈ W, v ≠ 0 ∧ ∀ i, ∃ c : K, S i v = c • v
  | 0, _, _, W, hW, _ => by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    exact ⟨v, hv, hv0, fun i => i.elim0⟩
  | d + 1, S, hS, W, hW, hinv => by
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW
    let T : Module.End K W := (S 0).restrict (hinv 0)
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    let W' : Submodule K V := W ⊓ LinearMap.ker (S 0 - c • (1 : Module.End K V))
    have hmem' : ∀ v, v ∈ W' ↔ v ∈ W ∧ S 0 v = c • v := by
      intro v
      simp only [W', Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, sub_eq_zero]
    have hW' : W' ≠ ⊥ := by
      intro h
      have hwv : (w : V) ∈ W' := by
        rw [hmem']
        refine ⟨w.2, ?_⟩
        have := hw.apply_eq_smul
        exact congrArg Subtype.val this
      rw [h, Submodule.mem_bot] at hwv
      exact hw.2 (Subtype.ext hwv)
    have hinv' : ∀ i : Fin d, ∀ v ∈ W', S i.succ v ∈ W' := by
      intro i v hv
      rw [hmem'] at hv ⊢
      refine ⟨hinv _ v hv.1, ?_⟩
      have hcomm : S 0 (S i.succ v) = S i.succ (S 0 v) := by
        rw [← Module.End.mul_apply, (hS 0 i.succ).eq, Module.End.mul_apply]
      rw [hcomm, hv.2, map_smul]
    obtain ⟨v, hv, hv0, hev⟩ := exists_common_eigenvector_mem d (fun i => S i.succ)
      (fun i j => hS _ _) W' hW' hinv'
    refine ⟨v, ((hmem' v).1 hv).1, hv0, fun i => ?_⟩
    refine Fin.cases ⟨c, ((hmem' v).1 hv).2⟩ (fun j => hev j) i

/-- **Andrianov–Zhuravlev, Chapter 4, Lemma 1.10.** Let `V` be a nonzero finite-dimensional vector space over an
algebraically closed field and `S_1, …, S_d` pairwise commuting linear operators on `V`. Then `V` contains a nonzero
common eigenvector of `S_1, …, S_d`. -/
@[kb "andrianovzhuravlev1995" "Chapter 4, Lemma 1.10, p. 244"]
theorem exists_common_eigenvector [Nontrivial V] {d : ℕ} (S : Fin d → Module.End K V)
    (hS : ∀ i j, Commute (S i) (S j)) : ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ c : K, S i v = c • v := by
  obtain ⟨v, -, hv0, hev⟩ := exists_common_eigenvector_mem d S hS ⊤ top_ne_bot
    (fun _ _ _ => Submodule.mem_top)
  exact ⟨v, hv0, hev⟩

end ModularFormsKB.Andrianov
