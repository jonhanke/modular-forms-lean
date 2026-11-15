import ModularFormsKB.Miyake.Wave10.LowWeight
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.ConstantTerm

/-!
# Miyake, Theorem 4.7.1 for k = 1 with the constant term a₀

Miyake, *Modular Forms* (Springer 1989), p. 177. For `k = 1` Miyake's `a₀` is `0` if both `χ₁` and
`χ₂` are non-trivial and `-B_{1,χ}/2` otherwise (`χ = χ₁χ₂`; when `χ₂` is trivial `χ = χ₁`, when
`χ₁` is trivial `χ = χ₂`).

Proof: Tau Ceti's constant term of the normalized weight-one series
(`TauCeti.EisensteinSeries.qExpansion_normalizedCharE1MFRaise_coeff_zero`). The weight-two constant
terms (`-(1 - M)/24` in case (i), `-B_{2, χ₂}/4` or `0` in case (ii)) are not covered here (the
`k = 2` part of wave 10's LE-MF-0228 stays open).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup DirichletCharacter
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave11

open ModularFormsKB.Miyake.Wave4 ModularFormsKB.Miyake.Wave10 TauCeti.EisensteinSeries

/-- **Miyake, Theorem 4.7.1**, `k = 1`, with the constant term: for primitive `χ₁ mod M₁`,
`χ₂ mod M₂` with `χ₁(-1) χ₂(-1) = -1` there is `f ∈ 𝒢₁(M₁ M₂, χ₁ χ₂)` with
`aₙ(f) = Σ_{d ∣ n} χ₁(n/d) χ₂(d)` for `n ≥ 1` and `a₀(f) = 0` if `χ₁`, `χ₂` are both non-trivial,
`a₀(f) = -B_{1, χ₁}/2` if `χ₂` is trivial (`M₂ = 1`), `a₀(f) = -B_{1, χ₂}/2` if `χ₁` is trivial
(`M₁ = 1`). -/
@[kb "miyake1989" "Theorem 4.7.1, p. 177 (k = 1, with a_0)"]
theorem exists_modSpace_coeff_eq_weightOne_constTerm {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂]
    [NeZero (M₁ * M₂)]
    (χ₁ : DirichletCharacter ℂ M₁) (χ₂ : DirichletCharacter ℂ M₂) (h₁ : χ₁.IsPrimitive)
    (h₂ : χ₂.IsPrimitive) (hpar : χ₁ (-1) * χ₂ (-1) = -1) :
    ∃ f : modSpace (N := M₁ * M₂) 1
        (χ₁.changeLevel (dvd_mul_right M₁ M₂) * χ₂.changeLevel (dvd_mul_left M₂ M₁)),
      (∀ n : ℕ, n ≠ 0 → coeffMod f n = ∑ d ∈ n.divisors, χ₁ (n / d : ℕ) * χ₂ d) ∧
      coeffMod f 0 = -((if M₂ = 1 then χ₁.generalizedBernoulli 1 else 0) +
        (if M₁ = 1 then χ₂.generalizedBernoulli 1 else 0)) / 2 := by
  let a : CharIndex (M₁ * M₂) 1 := ⟨M₁, M₂, 1, χ₁, χ₂, h₁, h₂, by simpa using hpar, by simp⟩
  have ha : a.nebentypus = (χ₁.changeLevel (dvd_mul_right M₁ M₂) *
      χ₂.changeLevel (dvd_mul_left M₂ M₁)).toUnitHom := (nebentypus_eq_iff a _).2 rfl
  refine ⟨a.weightOneInCharSpace ha, fun n hn ↦ ?_, ?_⟩
  · show (qExpansion 1 a.weightOneForm).coeff n = _
    rw [CharIndex.qExpansion_weightOneForm_coeff _ hn]
    simp only [a, one_dvd, ↓reduceIte, Nat.div_one, twistedDivisorSum_apply, pow_zero, mul_one]
  · show (qExpansion 1 a.weightOneForm).coeff 0 = _
    rw [CharIndex.weightOneForm_def]
    exact qExpansion_normalizedCharE1MFRaise_coeff_zero χ₁ χ₂ _ hpar h₂

/-- In Miyake's terms: for `k = 1`, `a₀ = 0` when `χ₁` and `χ₂` are both non-trivial. -/
@[kb "miyake1989" "Theorem 4.7.1, p. 177 (k = 1, a_0 = 0 for non-trivial characters)"]
theorem exists_modSpace_weightOne_constTerm_eq_zero {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂]
    [NeZero (M₁ * M₂)]
    (χ₁ : DirichletCharacter ℂ M₁) (χ₂ : DirichletCharacter ℂ M₂) (h₁ : χ₁.IsPrimitive)
    (h₂ : χ₂.IsPrimitive) (hpar : χ₁ (-1) * χ₂ (-1) = -1) (hne₁ : χ₁ ≠ 1) (hne₂ : χ₂ ≠ 1) :
    ∃ f : modSpace (N := M₁ * M₂) 1
        (χ₁.changeLevel (dvd_mul_right M₁ M₂) * χ₂.changeLevel (dvd_mul_left M₂ M₁)),
      (∀ n : ℕ, n ≠ 0 → coeffMod f n = ∑ d ∈ n.divisors, χ₁ (n / d : ℕ) * χ₂ d) ∧
      coeffMod f 0 = 0 := by
  obtain ⟨f, hf, h0⟩ := exists_modSpace_coeff_eq_weightOne_constTerm χ₁ χ₂ h₁ h₂ hpar
  have hM₁ : M₁ ≠ 1 := by
    rintro rfl
    exact hne₁ (Subsingleton.elim _ _)
  have hM₂ : M₂ ≠ 1 := by
    rintro rfl
    exact hne₂ (Subsingleton.elim _ _)
  exact ⟨f, hf, by simp [h0, hM₁, hM₂]⟩

end ModularFormsKB.Miyake.Wave11
