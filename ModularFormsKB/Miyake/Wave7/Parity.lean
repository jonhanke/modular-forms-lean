import ModularFormsKB.Miyake.Wave4.Notation
import TauCeti.NumberTheory.ModularForms.Parity
import TauCeti.NumberTheory.ModularForms.Conjugate

/-!
# Miyake, Lemma 4.3.2 (1), (3) on `𝒢_k(N, χ)`, `𝒮_k(N, χ)`

Miyake, *Modular Forms* (Springer 1989), §4.3, p. 115.

* (1) If `χ(-1) ≠ (-1)^k`, then `𝒢_k(N, χ) = {0}` (and so `𝒮_k(N, χ) = {0}`).
* (3) If `f(z) = Σ a_n e^{2πinz} ∈ 𝒢_k(N, χ)` (resp. `𝒮_k(N, χ)`), then
  `f_ρ(z) = Σ conj(a_n) e^{2πinz}` (4.3.3) satisfies `f_ρ(z) = conj(f(-conj z))` and belongs to
  `𝒢_k(N, conj χ)` (resp. `𝒮_k(N, conj χ)`).

Both are restatements, in wave 4's notation `modSpace`, `cuspSpace`, of Tau Ceti's parity lemma
(`TauCeti.modFormCharSpace_eq_bot_of_char_neg_one_ne`) and conjugate form
(`ModularForm.conj`, `ModularForm.qExpansion_conj`, `conj_mem_modFormCharSpace`). Part (2) is
`Sec4_3.fricke_isModularFormChar` and Tau Ceti's `frickeCharEquiv`.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

noncomputable section

namespace ModularFormsKB.Miyake.Wave7

open ModularFormsKB.Miyake.Wave4

variable {N : ℕ}

/-- For a Dirichlet character `χ`, the unit homomorphism of `χ⁻¹` is the inverse of that of `χ`. -/
theorem toUnitHom_inv_eq_inv (χ : DirichletCharacter ℂ N) : (χ⁻¹).toUnitHom = χ.toUnitHom⁻¹ := by
  ext u
  simp [MulChar.inv_apply_eq_inv']

/-- The point `-conj z` of `ℍ`. -/
def negConj (τ : ℍ) : ℍ := ⟨-(starRingEnd ℂ) (τ : ℂ), by simpa using τ.im_pos⟩

/-- **Miyake, Lemma 4.3.2 (1)**: if `χ(-1) ≠ (-1)^k`, then `𝒢_k(N, χ) = {0}`. -/
@[kb "miyake1989" "Lemma 4.3.2 (1), p. 115"]
theorem modSpace_eq_bot_of_parity (k : ℤ) (χ : DirichletCharacter ℂ N)
    (h : χ (-1) ≠ (-1 : ℂ) ^ k) : modSpace k χ = ⊥ := by
  refine TauCeti.modFormCharSpace_eq_bot_of_char_neg_one_ne ?_
  simpa [MulChar.coe_toUnitHom] using h

/-- **Miyake, Lemma 4.3.2 (1)** for cusp forms: if `χ(-1) ≠ (-1)^k`, then `𝒮_k(N, χ) = {0}`. -/
@[kb "miyake1989" "Lemma 4.3.2 (1), p. 115"]
theorem cuspSpace_eq_bot_of_parity (k : ℤ) (χ : DirichletCharacter ℂ N)
    (h : χ (-1) ≠ (-1 : ℂ) ^ k) : cuspSpace k χ = ⊥ := by
  refine TauCeti.cuspFormCharSpace_eq_bot_of_char_neg_one_ne ?_
  simpa [MulChar.coe_toUnitHom] using h

/-- **Miyake, Lemma 4.3.2 (3)**: for `f ∈ 𝒢_k(N, χ)` the form `f_ρ` with conjugate Fourier
coefficients (4.3.3) exists in `𝒢_k(N, conj χ)` and `f_ρ(z) = conj(f(-conj z))`. -/
@[kb "miyake1989" "Lemma 4.3.2 (3), p. 115"]
theorem exists_modSpace_conj (k : ℤ) (χ : DirichletCharacter ℂ N) (f : modSpace k χ) :
    ∃ g : modSpace k χ⁻¹,
      (∀ n, coeffMod g n = starRingEnd ℂ (coeffMod f n)) ∧
        ∀ τ : ℍ, (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) τ =
          starRingEnd ℂ ((f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (negConj τ)) := by
  have hJ := TauCeti.Gamma1_map_le_conjAct_inv_J N
  refine ⟨⟨ModularForm.conj hJ (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k), ?_⟩, ?_, ?_⟩
  · change _ ∈ TauCeti.modFormCharSpace k _
    rw [toUnitHom_inv_eq_inv]
    exact ModularForm.conj_mem_modFormCharSpace f.2
  · intro n
    simp only [coeffMod]
    rw [ModularForm.qExpansion_conj one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N) hJ,
      PowerSeries.coeff_map]
  · intro τ
    rw [ModularForm.conj_apply, UpperHalfPlane.J_smul,
      UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using τ.im_pos)]
    rfl

/-- **Miyake, Lemma 4.3.2 (3)** for cusp forms. -/
@[kb "miyake1989" "Lemma 4.3.2 (3), p. 115"]
theorem exists_cuspSpace_conj (k : ℤ) (χ : DirichletCharacter ℂ N) (f : cuspSpace k χ) :
    ∃ g : cuspSpace k χ⁻¹,
      (∀ n, coeff g n = starRingEnd ℂ (coeff f n)) ∧
        ∀ τ : ℍ, (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) τ =
          starRingEnd ℂ ((f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (negConj τ)) := by
  have hJ := TauCeti.Gamma1_map_le_conjAct_inv_J N
  refine ⟨⟨CuspForm.conj hJ (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k), ?_⟩, ?_, ?_⟩
  · change _ ∈ TauCeti.cuspFormCharSpace k _
    rw [toUnitHom_inv_eq_inv]
    exact CuspForm.conj_mem_cuspFormCharSpace f.2
  · intro n
    simp only [coeff]
    rw [CuspForm.qExpansion_conj one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N) hJ,
      PowerSeries.coeff_map]
  · intro τ
    rw [CuspForm.conj_apply, UpperHalfPlane.J_smul,
      UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using τ.im_pos)]
    rfl

end ModularFormsKB.Miyake.Wave7
