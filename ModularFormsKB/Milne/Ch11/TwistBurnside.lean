import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# A fixed-point count over a coset

Let a finite group $\Omega$ act transitively on a finite nonempty set $X$, let $N \trianglelefteq \Omega$ and
$\varphi \in \Omega$ with $\Omega = \langle\varphi\rangle N$, and suppose every stabilizer meets the coset
$\varphi N$. Then $\sum_{n \in N} \#\mathrm{Fix}(\varphi n) = |N|$.

This is the group theory behind the twisting argument for the lower bound in Weil's theorem: $\Omega$ is the Galois
group $\Gamma \times \mathrm{Gal}(k'/k)$ of $E \cdot k'$ over the fixed field, $X$ the places over a rational place,
$N = \Gamma$ and $\varphi$ the Frobenius; a stabilizer (decomposition group) meets $\varphi N$ because it maps onto
the Galois group of the residue extension.

Proof: for each $x$ the $n$ with $\varphi n x = x$ form a translate of $\mathrm{Stab}_N(x)$; $N$ is transitive
(because $\varphi \in \mathrm{Stab}(x) N$), so $|\mathrm{Stab}_N(x)| \cdot |X| = |N|$.
-/

open Finset

namespace ModularFormsKB.Milne

variable {Ω X : Type*} [Group Ω] [MulAction Ω X]

theorem exists_mem_mul_pow_of_smul_eq (N : Subgroup Ω) [N.Normal] {φ s : Ω} (n₀ : Ω) (hn₀ : n₀ ∈ N)
    (hs : s = φ * n₀) (j : ℕ) : ∃ m ∈ N, φ ^ j = m * s ^ j := by
  have hφ : φ = (s * n₀⁻¹ * s⁻¹) * s := by rw [hs]; group
  have hm₁ : s * n₀⁻¹ * s⁻¹ ∈ N := ‹N.Normal›.conj_mem _ (N.inv_mem hn₀) s
  induction j with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ j ih =>
    obtain ⟨m, hm, hj⟩ := ih
    refine ⟨m * (s ^ j * (s * n₀⁻¹ * s⁻¹) * (s ^ j)⁻¹), N.mul_mem hm (‹N.Normal›.conj_mem _ hm₁ _), ?_⟩
    rw [pow_succ, hj]
    conv_lhs => rw [hφ]
    group

/-- **The fixed-point count over a coset.** -/
theorem sum_card_fixed_coset [Finite X] [Nonempty X] (N : Subgroup Ω) [N.Normal] [Fintype N] (φ : Ω)
    (hgen : ∀ ω : Ω, ∃ j : ℕ, ∃ n ∈ N, ω = φ ^ j * n)
    (htrans : ∀ x y : X, ∃ ω : Ω, ω • x = y)
    (hstab : ∀ x : X, ∃ n ∈ N, (φ * n) • x = x) :
    ∑ n : N, Nat.card {x : X // (φ * n) • x = x} = Nat.card N := by
  classical
  have := Fintype.ofFinite X
  -- `N` is transitive
  have hNtrans : ∀ x y : X, ∃ n : N, n • x = y := by
    intro x y
    obtain ⟨ω, rfl⟩ := htrans x y
    obtain ⟨j, n, hn, rfl⟩ := hgen ω
    obtain ⟨n₀, hn₀, hfix⟩ := hstab x
    set s := φ * n₀ with hsdef
    obtain ⟨m, hm, hφj⟩ := exists_mem_mul_pow_of_smul_eq N n₀ hn₀ hsdef j
    have hsx : ∀ i : ℕ, s ^ i • x = x := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ, mul_smul, hfix, ih]
    have hmem : m * (s ^ j * n * (s ^ j)⁻¹) ∈ N := N.mul_mem hm (‹N.Normal›.conj_mem _ hn _)
    refine ⟨⟨_, hmem⟩, ?_⟩
    have hinv : (s ^ j)⁻¹ • x = x := by rw [inv_smul_eq_iff, hsx j]
    change (m * (s ^ j * n * (s ^ j)⁻¹)) • x = (φ ^ j * n) • x
    rw [hφj, mul_smul, mul_smul, mul_smul, hinv, mul_smul, mul_smul]
  -- for each `x`, the solutions `n` of `φ n x = x` are a translate of `Stab_N(x)`
  have hcount : ∀ x : X, Nat.card {n : N // (φ * (n : Ω)) • x = x} = Nat.card {n : N // n • x = x} := by
    intro x
    obtain ⟨n₀, hn₀, hfix⟩ := hstab x
    have key : ∀ n : Ω, (φ * n) • x = x ↔ (n₀⁻¹ * n) • x = x := by
      intro n
      have : (φ * n) = (φ * n₀) * (n₀⁻¹ * n) := by group
      rw [this, mul_smul]
      constructor
      · intro h
        have h' := congrArg (fun y => (φ * n₀)⁻¹ • y) h
        simp only [inv_smul_smul] at h'
        rw [h', inv_smul_eq_iff, hfix]
      · intro h; rw [h, hfix]
    refine Nat.card_congr
      { toFun := fun n => ⟨⟨n₀⁻¹ * n.1, N.mul_mem (N.inv_mem hn₀) n.1.2⟩, (key n.1).mp n.2⟩
        invFun := fun n => ⟨⟨n₀ * n.1, N.mul_mem hn₀ n.1.2⟩, (key _).mpr (by rw [← mul_assoc, inv_mul_cancel, one_mul]; exact n.2)⟩
        left_inv := fun n => by ext; simp
        right_inv := fun n => by ext; simp }
  -- orbit--stabilizer with a transitive action
  have horbit : ∀ x : X, Nat.card {n : N // n • x = x} * Nat.card X = Nat.card N := by
    intro x
    have h1 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group N x
    simp only [← Nat.card_eq_fintype_card] at h1
    have h2 : MulAction.orbit N x = Set.univ := Set.eq_univ_of_forall fun y => hNtrans x y
    have h3 : Nat.card (MulAction.orbit N x) = Nat.card X := by rw [h2, Nat.card_univ]
    have h4 : Nat.card {n : N // n • x = x} = Nat.card (MulAction.stabilizer N x) := rfl
    rw [h4, mul_comm, ← h3, h1]
  -- double counting
  have hswap : ∑ n : N, Nat.card {x : X // (φ * n) • x = x} =
      ∑ x : X, Nat.card {n : N // (φ * (n : Ω)) • x = x} := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]
  simp_rw [hcount]
  have hpos : 0 < Nat.card X := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [Finset.sum_mul]
  simp_rw [horbit]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card (α := X), mul_comm]

end ModularFormsKB.Milne
