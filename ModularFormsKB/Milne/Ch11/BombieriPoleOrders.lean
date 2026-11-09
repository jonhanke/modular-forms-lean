import ModularFormsKB.Milne.Ch11.ZetaFiniteField

/-!
# Bombieri's argument, I: functions with distinct pole orders at a rational place

For a rational place $P_0$ of a function field $F/k$ and $m \ge 0$, the quotients
$\mathcal L(jP_0)/\mathcal L((j-1)P_0)$ have dimension at most one, so there are $\ell(mP_0)$ indices
$j \in [0, m]$ at which $\ell$ jumps, and for each such $j$ a function with a pole of order exactly $j$ at $P_0$ and no
other poles. With Riemann's inequality $\ell(mP_0) \ge m + 1 - g$ this gives at least $m + 1 - g$ functions in
$\mathcal L(mP_0)$ with pairwise distinct orders at $P_0$ (Stichtenoth, *Algebraic Function Fields and Codes*,
2nd ed., Section 5.2 [unverified]).
-/

open TauCeti TauCeti.AlgebraicGeometry

namespace ModularFormsKB.Milne

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

section
variable (P₀ : Place k F)

/-- The divisor `(n - 1) P₀`, indexed by `n : ℕ`. -/
private noncomputable def pdiv (n : ℕ) : Divisor k F := ((n : ℤ) - 1) • WeilDivisor.ofPoint P₀

private lemma pdiv_succ (n : ℕ) : pdiv P₀ (n + 1) = pdiv P₀ n + WeilDivisor.ofPoint P₀ := by
  unfold pdiv; push_cast; rw [show ((n : ℤ) + 1 - 1) = n by ring,
    sub_smul, one_smul]; abel

private lemma pdiv_le_succ (n : ℕ) : pdiv P₀ n ≤ pdiv P₀ (n + 1) := by
  rw [pdiv_succ]
  refine le_add_of_nonneg_right ?_
  intro Q
  by_cases h : Q = P₀
  · subst h
    have := WeilDivisor.coeff_ofPoint_self Q
    simp only [WeilDivisor.coeff] at this
    simp [this]
  · have := WeilDivisor.coeff_ofPoint_of_ne h
    simp only [WeilDivisor.coeff] at this
    simp [this]

private lemma pdiv_dim_zero (hF : IsFunctionField k F) (hP₀ : P₀.degree = 1) :
    Divisor.dim (pdiv P₀ 0) = 0 := by
  apply Divisor.dim_eq_zero_of_degree_neg hF
  unfold pdiv
  rw [Divisor.degree_zsmul, Divisor.degree_ofPoint, hP₀]; norm_num

private lemma pdiv_dim_succ_le (hF : IsFunctionField k F) (hP₀ : P₀.degree = 1) (n : ℕ) :
    Divisor.dim (pdiv P₀ (n + 1)) ≤ Divisor.dim (pdiv P₀ n) + 1 := by
  have := finrank_riemannRochSpace_add_ofPoint_le hF (pdiv P₀ n) P₀
    (finiteDimensional_riemannRochSpace hF _)
  rw [← pdiv_succ, hP₀] at this
  exact this

private lemma card_filter_eq (hF : IsFunctionField k F) (hP₀ : P₀.degree = 1) (n : ℕ) :
    Divisor.dim (pdiv P₀ n) =
      ((Finset.range n).filter fun j => Divisor.dim (pdiv P₀ (j + 1)) =
        Divisor.dim (pdiv P₀ j) + 1).card := by
  classical
  induction n with
  | zero => simpa using pdiv_dim_zero P₀ hF hP₀
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    have h1 := pdiv_dim_succ_le P₀ hF hP₀ n
    have h2 : Divisor.dim (pdiv P₀ n) ≤ Divisor.dim (pdiv P₀ (n + 1)) :=
      Divisor.dim_mono hF (pdiv_le_succ P₀ n)
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]; omega
    · omega

private lemma pdiv_eq (j : ℕ) : pdiv P₀ (j + 1) = (j : ℤ) • WeilDivisor.ofPoint P₀ := by
  unfold pdiv; push_cast; simp

private lemma exists_jump (hF : IsFunctionField k F) (j : ℕ)
    (h : Divisor.dim (pdiv P₀ (j + 1)) = Divisor.dim (pdiv P₀ j) + 1) :
    ∃ f : F, f ≠ 0 ∧ P₀.ord f = -(j : ℤ) ∧ (∀ Q : Place k F, Q ≠ P₀ → 0 ≤ Q.ord f) := by
  have hfd := finiteDimensional_riemannRochSpace hF (pdiv P₀ (j + 1))
  have hfd' := finiteDimensional_riemannRochSpace hF (pdiv P₀ j)
  have : ¬ riemannRochSpace (pdiv P₀ (j + 1)) ≤ riemannRochSpace (pdiv P₀ j) := by
    intro hle
    have := Submodule.finrank_mono hle
    rw [← Divisor.dim_def, ← Divisor.dim_def] at this
    omega
  rw [SetLike.le_def] at this
  push_neg at this
  obtain ⟨f, hf1, hf2⟩ := this
  have hf0 : f ≠ 0 := by rintro rfl; exact hf2 (Submodule.zero_mem _)
  rw [pdiv_eq, mem_riemannRochSpace_zsmul_ofPoint_iff hf0] at hf1
  have hj : pdiv P₀ j = ((j : ℤ) - 1) • WeilDivisor.ofPoint P₀ := rfl
  rw [hj, mem_riemannRochSpace_zsmul_ofPoint_iff hf0] at hf2
  have : ¬ (-((j : ℤ) - 1) ≤ P₀.ord f) := fun h' => hf2 ⟨h', hf1.2⟩
  refine ⟨f, hf0, ?_, hf1.2⟩
  omega

end

/-- **At least $m + 1 - g$ functions in $\mathcal L(mP_0)$ with pairwise distinct orders at $P_0$.** -/
theorem exists_injective_ord_mem_riemannRochSpace (hF : IsFunctionField k F) (P₀ : Place k F)
    (hP₀ : P₀.degree = 1) (m : ℕ) :
    ∃ (s : ℕ) (f : Fin s → F), (m : ℤ) + 1 - genus k F ≤ s ∧
      (∀ i, f i ∈ riemannRochSpace ((m : ℤ) • WeilDivisor.ofPoint P₀)) ∧ (∀ i, f i ≠ 0) ∧
      Function.Injective (fun i => P₀.ord (f i)) ∧ (∀ i, P₀.ord (f i) ≤ 0) := by
  classical
  set J := (Finset.range (m + 1)).filter fun j => Divisor.dim (pdiv P₀ (j + 1)) =
        Divisor.dim (pdiv P₀ j) + 1 with hJ
  have hcard : Divisor.dim ((m : ℤ) • WeilDivisor.ofPoint P₀) = J.card := by
    rw [← pdiv_eq]; exact card_filter_eq P₀ hF hP₀ (m + 1)
  have hR := Divisor.degree_add_one_sub_genus_le_dim hF ((m : ℤ) • WeilDivisor.ofPoint P₀)
  rw [hcard, Divisor.degree_zsmul, Divisor.degree_ofPoint, hP₀] at hR
  have hex : ∀ j ∈ J, ∃ f : F, f ≠ 0 ∧ P₀.ord f = -(j : ℤ) ∧
      (∀ Q : Place k F, Q ≠ P₀ → 0 ≤ Q.ord f) := fun j hj =>
    exists_jump P₀ hF j (Finset.mem_filter.1 hj).2
  choose! pick hp using hex
  let g : Fin J.card ↪o ℕ := J.orderEmbOfFin rfl
  have hg : ∀ i, g i ∈ J := fun i => J.orderEmbOfFin_mem rfl i
  refine ⟨J.card, fun i => pick (g i), by push_cast at hR ⊢; linarith, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨h0, h1, h2⟩ := hp _ (hg i)
    have hlt : g i < m + 1 := Finset.mem_range.1 (Finset.mem_filter.1 (hg i)).1
    show pick (g i) ∈ _
    rw [mem_riemannRochSpace_zsmul_ofPoint_iff h0]
    refine ⟨?_, h2⟩
    rw [h1]
    have : ((g i : ℕ) : ℤ) ≤ m := by omega
    omega
  · intro i; exact (hp _ (hg i)).1
  · intro i i' h
    have := (hp _ (hg i)).2.1
    have := (hp _ (hg i')).2.1
    simp only at h
    have : g i = g i' := by omega
    exact g.injective this
  · intro i
    have := (hp _ (hg i)).2.1
    show P₀.ord (pick (g i)) ≤ 0
    omega

end ModularFormsKB.Milne
