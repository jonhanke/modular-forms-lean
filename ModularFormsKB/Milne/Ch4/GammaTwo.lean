import ModularFormsKB.Miyake.CongruenceModularGroups
import ModularFormsKB.Citation
/-!
# Milne, Chapter 4: Example 4.2, the group $\Gamma(2)$

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 4, Example 4.2, pdf p. 48.

Milne's $\Gamma(1)$ is $\mathrm{SL}_2(\mathbb Z)$. Example 4.2 says: $\Gamma(2)$ has index 6 in $\Gamma(1)$; it has three
inequivalent cusps $i\infty$, $0$, $1$; and the stabilizer of $i\infty$ in $\Gamma(2)$ is generated (up to $\pm1$) by
$\begin{pmatrix}1&2\\0&1\end{pmatrix}$, so the width of $i\infty$ is $2$ and the local parameter is $e^{2\pi i z/2}$.

The index and the cusp count come from `ModularFormsKB.Miyake.index_Gamma` and
`ModularFormsKB.Miyake.card_cuspOrbits_Gamma_two` (Miyake, Theorems 4.2.5 and 4.2.10).
-/

open Matrix CongruenceSubgroup ModularGroup
open scoped MatrixGroups

namespace ModularFormsKB.Milne

/-- **Example 4.2**, index: $[\Gamma(1) : \Gamma(2)] = 6$. -/
@[kb "milne2017mf" "Section 4, Example 4.2 (pdf p. 48)"]
theorem index_Gamma_two : (Gamma 2).index = 6 := by
  have h2 := Miyake.card_SL2_ZMod 2
  rw [Nat.Prime.primeFactors Nat.prime_two] at h2
  norm_num at h2
  rw [Miyake.index_Gamma, Nat.card_eq_fintype_card]
  exact_mod_cast h2

/-- **Example 4.2**, cusps: $\Gamma(2)$ has three inequivalent cusps. -/
@[kb "milne2017mf" "Section 4, Example 4.2 (pdf p. 48)"]
theorem card_cuspOrbits_Gamma_two : Nat.card (CuspOrbits (Gamma 2 : Subgroup (GL (Fin 2) ℝ))) = 3 :=
  Miyake.card_cuspOrbits_Gamma_two

/-- Parity of the entries of an element of `Gamma 2`. -/
private theorem Gamma_two_parity {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma 2) :
    γ 0 0 % 2 = 1 ∧ γ 0 1 % 2 = 0 ∧ γ 1 0 % 2 = 0 ∧ γ 1 1 % 2 = 1 := by
  rw [Gamma_mem] at hγ
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  have e1 := (ZMod.intCast_eq_intCast_iff' (γ 0 0) 1 2).1 (by simpa using h1)
  have e2 := (ZMod.intCast_eq_intCast_iff' (γ 0 1) 0 2).1 (by simpa using h2)
  have e3 := (ZMod.intCast_eq_intCast_iff' (γ 1 0) 0 2).1 (by simpa using h3)
  have e4 := (ZMod.intCast_eq_intCast_iff' (γ 1 1) 1 2).1 (by simpa using h4)
  omega

/-- **Example 4.2**, the three cusps are $i\infty$, $0 = S(i\infty)$ and $1 = TS(i\infty)$: no element of $\Gamma(2)$
maps one of them to another. With `card_cuspOrbits_Gamma_two` they represent all three cusp orbits. -/
@[kb "milne2017mf" "Section 4, Example 4.2 (pdf p. 48)"]
theorem cusps_Gamma_two_distinct :
    ∀ c ∈ ({OnePoint.infty, ((0 : ℝ) : OnePoint ℝ), ((1 : ℝ) : OnePoint ℝ)} : Set (OnePoint ℝ)),
    ∀ c' ∈ ({OnePoint.infty, ((0 : ℝ) : OnePoint ℝ), ((1 : ℝ) : OnePoint ℝ)} : Set (OnePoint ℝ)),
      c ≠ c' → ∀ γ ∈ Gamma 2, Matrix.SpecialLinearGroup.mapGL ℝ γ • c ≠ c' := by
  intro c hc c' hc' hne γ hγ
  obtain ⟨p1, p2, p3, p4⟩ := Gamma_two_parity hγ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc hc'
  intro heq
  have e10 : ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) 1 0) = ((γ 1 0 : ℤ) : ℝ) := by simp
  have e00 : ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) 0 0) = ((γ 0 0 : ℤ) : ℝ) := by simp
  have e01 : ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) 0 1) = ((γ 0 1 : ℤ) : ℝ) := by simp
  have e11 : ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) 1 1) = ((γ 1 1 : ℤ) : ℝ) := by simp
  rcases hc with rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl <;>
    try exact absurd rfl hne
  all_goals
    simp only [OnePoint.smul_infty_eq_ite, OnePoint.smul_some_eq_ite, e10, e00, e01, e11] at heq
    split_ifs at heq with h
    all_goals
      try simp only [mul_one, mul_zero, zero_add] at h
      first
      | (simp at heq; done)
      | (simp at heq
         first
         | (rcases heq with h1 | h1
            all_goals first
              | exact h h1
              | (norm_cast at h1 h; omega))
         | (rw [div_eq_one_iff_eq (by simpa using h)] at heq
            norm_cast at heq
            omega)
         | (norm_cast at h; omega))

/-- **Example 4.2**, stabilizer of $i\infty$: an element of $\Gamma(2)$ fixing $i\infty$ (lower left entry $0$) is
$\pm\begin{pmatrix}1&2m\\0&1\end{pmatrix}$, i.e. $\pm T^{2m}$. -/
@[kb "milne2017mf" "Section 4, Example 4.2 (pdf p. 48)"]
theorem stabilizer_infty_Gamma_two {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma 2) (hc : γ 1 0 = 0) :
    ∃ m : ℤ, γ = T ^ (2 * m) ∨ γ = -T ^ (2 * m) := by
  obtain ⟨p1, p2, p3, p4⟩ := Gamma_two_parity hγ
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two, hc] at hdet
  have hm : γ 0 0 * γ 1 1 = 1 := by linarith
  obtain ⟨m, hm2⟩ : ∃ m : ℤ, γ 0 1 = 2 * m := ⟨γ 0 1 / 2, by omega⟩
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hm with h | h
  · have hd : γ 1 1 = 1 := by rw [h] at hm; linarith
    refine ⟨m, Or.inl ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, h, hd, hc, hm2]
  · have hd : γ 1 1 = -1 := by rw [h] at hm; linarith
    refine ⟨-m, Or.inr ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, h, hd, hc, hm2, mul_neg]

/-- **Example 4.2**, width: the width of the cusp $i\infty$ for $\Gamma(2)$ is $2$ (Mathlib's
`CongruenceSubgroup.strictWidthInfty_Gamma`). -/
@[kb "milne2017mf" "Section 4, Example 4.2 (pdf p. 48)"]
theorem strictWidthInfty_Gamma_two : (Gamma 2 : Subgroup (GL (Fin 2) ℝ)).strictWidthInfty = 2 := by
  simp

end ModularFormsKB.Milne
