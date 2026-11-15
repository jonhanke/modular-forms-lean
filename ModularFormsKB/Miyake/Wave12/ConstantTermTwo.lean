import ModularFormsKB.Miyake.Wave10.LowWeight

/-!
# Miyake, Theorem 4.7.1 for k = 2 with the constant term a₀

Miyake, *Modular Forms* (Springer 1989), Theorem 4.7.1, p. 177. For `k = 2` Miyake's constant
term is

* `a₀ = -(1 - M)/24` when `χ₁` and `χ₂` are both trivial (case (i) of (4.7.2): `M₁ = 1`,
  `M = M₂ = p` prime);
* `a₀ = 0` when `χ₁` is non-trivial;
* `a₀ = -B_{2,χ}/4` otherwise, that is `χ₁` trivial (`M₁ = 1`) and `χ₂` non-trivial, where
  `χ = χ₁ χ₂ = χ₂`.

The coefficients `aₙ`, `n ≥ 1`, are wave 10's (`exists_modSpace_coeff_eq_weightTwo`,
`exists_modSpace_coeff_eq_weightTwo_trivial`); this file adds `a₀` for the same forms.

Proofs: Tau Ceti's constant terms `qExpansion_coeff_correctedE2` (`E₂(z) - t E₂(tz)` has constant
term `1 - t`) and `qExpansion_normalizedCharG2MFRaise_coeff_zero` (`E₂^{ψ,φ,t}` has constant term
`-B_{2,φ}/4` if `u = 1`, else `0`).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup DirichletCharacter
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave12

open ModularFormsKB.Miyake.Wave4 ModularFormsKB.Miyake.Wave10 TauCeti.EisensteinSeries

variable {N : ℕ} [NeZero N]

/-- The constant term of `E₂(z) - t E₂(tz)` in `𝒢₂(N, 1)` is `1 - t`. -/
lemma coeffMod_weightTwoTriv_zero (t : ℕ) (ht : t ∣ N) :
    coeffMod (weightTwoTriv t ht) 0 = 1 - (t : ℂ) := by
  have : NeZero (trivIndex t ht).t := NeZero.of_dvd (trivIndex t ht).t_dvd
  show (qExpansion 1 (trivIndex t ht).weightTwoForm).coeff 0 = _
  rw [CharIndex.weightTwoForm_of_eq_one _ ⟨rfl, rfl⟩]
  simpa only [ModularForm.coe_restrict, ite_true, show (trivIndex t ht).t = t from rfl] using
    qExpansion_coeff_correctedE2 (trivIndex t ht).t 0

/-- The constant term of Miyake's `f₂(lz; 1, 1_p)` (`trivGen l p`) is `(p - 1)/24`. -/
lemma coeffMod_trivGen_zero {l p : ℕ} (h : l * p ∣ N) :
    coeffMod (trivGen l p h) 0 = -(1 - (p : ℂ)) / 24 := by
  have hl : l ≠ 0 := by
    rintro rfl
    exact NeZero.ne N (Nat.eq_zero_of_zero_dvd (by simpa using h))
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  rw [trivGen, coeffMod_smul, coeffMod_sub, coeffMod_weightTwoTriv_zero,
    coeffMod_weightTwoTriv_zero]
  push_cast
  field_simp
  ring

/-- **Miyake, Theorem 4.7.1**, `k = 2`, case (i) of (4.7.2), with the constant term: for a prime
`p` there is `f ∈ 𝒢₂(p, 1)` with `aₙ(f) = Σ_{d ∣ n} 1_p(d) d` for `n ≥ 1` (so
`L(s; f) = ζ(s) L(s - 1, 1_p)`) and `a₀(f) = -(1 - M)/24`, `M = p`. -/
@[kb "miyake1989" "Theorem 4.7.1, p. 177 (k = 2, case (i), with a_0)"]
theorem exists_modSpace_coeff_eq_weightTwo_trivial_constTerm {p : ℕ} (hp : p.Prime) [NeZero p] :
    ∃ f : modSpace (N := p) 2 1,
      (∀ n : ℕ, n ≠ 0 →
        coeffMod f n = ∑ d ∈ n.divisors, (1 : DirichletCharacter ℂ p) d * (d : ℂ)) ∧
      coeffMod f 0 = -(1 - (p : ℂ)) / 24 := by
  refine ⟨trivGen 1 p (by simp), fun n hn ↦ ?_, coeffMod_trivGen_zero _⟩
  rw [coeffMod_trivGen hp (by simp) (Nat.pos_of_ne_zero hn), eisCoeff]
  simp only [one_dvd, ↓reduceIte, Nat.div_one]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [show ((1 : DirichletCharacter ℂ 1) ((n / d : ℕ) : ZMod 1)) = 1 from
    MulChar.one_apply (isUnit_of_subsingleton _)]
  simp

/-- **Miyake, Theorem 4.7.1**, `k = 2`, case (ii) of (4.7.2), with the constant term: for
primitive `χ₁ mod M₁`, `χ₂ mod M₂`, not both trivial, with `χ₁(-1) χ₂(-1) = 1`, there is
`f ∈ 𝒢₂(M₁ M₂, χ₁ χ₂)` with `aₙ(f) = Σ_{d ∣ n} χ₁(n/d) χ₂(d) d` for `n ≥ 1`, and
`a₀(f) = -B_{2, χ₂}/4` if `χ₁` is trivial (`M₁ = 1`, so `χ = χ₂`), `a₀(f) = 0` otherwise. -/
@[kb "miyake1989" "Theorem 4.7.1, p. 177 (k = 2, case (ii), with a_0)"]
theorem exists_modSpace_coeff_eq_weightTwo_constTerm {M₁ M₂ : ℕ} [NeZero M₂]
    [NeZero (M₁ * M₂)]
    (χ₁ : DirichletCharacter ℂ M₁) (χ₂ : DirichletCharacter ℂ M₂) (h₁ : χ₁.IsPrimitive)
    (h₂ : χ₂.IsPrimitive) (hne : ¬ (χ₁ = 1 ∧ χ₂ = 1)) (hpar : χ₁ (-1) * χ₂ (-1) = 1) :
    ∃ f : modSpace (N := M₁ * M₂) 2
        (χ₁.changeLevel (dvd_mul_right M₁ M₂) * χ₂.changeLevel (dvd_mul_left M₂ M₁)),
      (∀ n : ℕ, n ≠ 0 → coeffMod f n = ∑ d ∈ n.divisors, χ₁ (n / d : ℕ) * χ₂ d * (d : ℂ)) ∧
      coeffMod f 0 = if M₁ = 1 then -χ₂.generalizedBernoulli 2 / 4 else 0 := by
  let a : CharIndex (M₁ * M₂) 2 := ⟨M₁, M₂, 1, χ₁, χ₂, h₁, h₂, by simpa using hpar, by simp⟩
  have ha : a.nebentypus = (χ₁.changeLevel (dvd_mul_right M₁ M₂) *
      χ₂.changeLevel (dvd_mul_left M₂ M₁)).toUnitHom := (nebentypus_eq_iff a _).2 rfl
  have hne' : a.psi ≠ 1 ∨ a.phi ≠ 1 := not_and_or.mp hne
  refine ⟨a.weightTwoInCharSpace ha, fun n hn ↦ ?_, ?_⟩
  · show (qExpansion 1 a.weightTwoForm).coeff n = _
    rw [CharIndex.qExpansion_weightTwoForm_coeff_of_ne_one a hne' hn]
    simp only [a, one_dvd, ↓reduceIte, Nat.div_one, twistedDivisorSum_apply, pow_one]
  · show (qExpansion 1 a.weightTwoForm).coeff 0 = _
    rw [CharIndex.weightTwoForm_of_ne_one a hne']
    exact qExpansion_normalizedCharG2MFRaise_coeff_zero χ₁ χ₂ (t := 1) _ hne' h₂

/-- In Miyake's terms: for `k = 2`, `a₀ = 0` when `χ₁` is non-trivial. -/
@[kb "miyake1989" "Theorem 4.7.1, p. 177 (k = 2, a_0 = 0 for non-trivial chi_1)"]
theorem exists_modSpace_weightTwo_constTerm_eq_zero {M₁ M₂ : ℕ} [NeZero M₂]
    [NeZero (M₁ * M₂)]
    (χ₁ : DirichletCharacter ℂ M₁) (χ₂ : DirichletCharacter ℂ M₂) (h₁ : χ₁.IsPrimitive)
    (h₂ : χ₂.IsPrimitive) (hpar : χ₁ (-1) * χ₂ (-1) = 1) (hne₁ : χ₁ ≠ 1) :
    ∃ f : modSpace (N := M₁ * M₂) 2
        (χ₁.changeLevel (dvd_mul_right M₁ M₂) * χ₂.changeLevel (dvd_mul_left M₂ M₁)),
      (∀ n : ℕ, n ≠ 0 → coeffMod f n = ∑ d ∈ n.divisors, χ₁ (n / d : ℕ) * χ₂ d * (d : ℂ)) ∧
      coeffMod f 0 = 0 := by
  obtain ⟨f, hf, h0⟩ := exists_modSpace_coeff_eq_weightTwo_constTerm χ₁ χ₂ h₁ h₂
    (fun h ↦ hne₁ h.1) hpar
  have hM₁ : M₁ ≠ 1 := by
    rintro rfl
    exact hne₁ (Subsingleton.elim _ _)
  exact ⟨f, hf, by simp [h0, hM₁]⟩

end ModularFormsKB.Miyake.Wave12
