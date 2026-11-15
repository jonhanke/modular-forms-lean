/-
# Joint eigenvectors with distinct eigenvalue systems are linearly independent

A linear algebra lemma used for Kohnen's isomorphism: nonzero vectors that are eigenvectors of a family of
operators, with pairwise distinct systems of eigenvalues, are linearly independent.
-/
import Mathlib.LinearAlgebra.LinearIndependent.Basic

namespace ModularFormsKB.HalfIntegral

/-- **Joint eigenvectors for distinct eigenvalue systems are linearly independent:** if $T_p v_i = \mu_i(p) v_i$ for
all $p$, each $v_i \neq 0$, and for $i \neq j$ some $p$ has $\mu_i(p) \neq \mu_j(p)$, then $(v_i)$ is linearly
independent. -/
theorem linearIndependent_of_jointEigen {ι P K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : P → V →ₗ[K] V) (μ : ι → P → K) (v : ι → V) (hv : ∀ i, v i ≠ 0)
    (hT : ∀ i p, T p (v i) = μ i p • v i) (hsep : ∀ i j, i ≠ j → ∃ p, μ i p ≠ μ j p) :
    LinearIndependent K v := by
  classical
  have key : ∀ n : ℕ, ∀ s : Finset ι, s.card = n → ∀ g : ι → K,
      ∑ i ∈ s, g i • v i = 0 → ∀ i ∈ s, g i = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hs g hg i hi
      by_cases hex : ∃ j ∈ s, j ≠ i
      · obtain ⟨j, hj, hji⟩ := hex
        obtain ⟨p, hp⟩ := hsep i j hji.symm
        have h0 : ∑ x ∈ s, (g x * (μ x p - μ j p)) • v x = 0 := by
          have e : ∑ x ∈ s, (g x * (μ x p - μ j p)) • v x
              = T p (∑ x ∈ s, g x • v x) - μ j p • ∑ x ∈ s, g x • v x := by
            rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [map_smul, hT, smul_smul, smul_smul, mul_sub, sub_smul, mul_comm (g x) (μ x p),
              mul_comm (μ j p) (g x)]
          rw [e, hg]; simp
        have h1 : ∑ x ∈ s.erase j, (g x * (μ x p - μ j p)) • v x = 0 := by
          rw [Finset.sum_erase _ (by simp)]; exact h0
        have hlt : (s.erase j).card < n := by
          rw [Finset.card_erase_of_mem hj, ← hs]
          have : 0 < s.card := Finset.card_pos.mpr ⟨j, hj⟩
          omega
        have hi' : i ∈ s.erase j := Finset.mem_erase.mpr ⟨hji.symm, hi⟩
        have hgi := ih _ hlt (s.erase j) rfl _ h1 i hi'
        have hne : μ i p - μ j p ≠ 0 := sub_ne_zero.mpr hp
        have hgi0 : g i = 0 := by
          rcases mul_eq_zero.mp hgi with h | h
          · exact h
          · exact absurd h hne
        exact hgi0
      · simp only [not_exists, not_and, not_not] at hex
        have hsub : s = {i} := by
          ext x; simp only [Finset.mem_singleton]
          exact ⟨fun hx => hex x hx, fun hx => hx ▸ hi⟩
        subst hsub
        simp only [Finset.sum_singleton] at hg
        by_contra h
        apply hv i
        have := congrArg (fun w => (g i)⁻¹ • w) hg
        simpa [smul_smul, inv_mul_cancel₀ h] using this
  rw [linearIndependent_iff']
  intro s g hg i hi
  exact key _ s rfl g hg i hi

end ModularFormsKB.HalfIntegral
