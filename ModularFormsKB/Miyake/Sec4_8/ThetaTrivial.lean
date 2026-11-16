import ModularFormsKB.Miyake.Sec4_8.ThetaStatementFix
import ModularFormsKB.Citation
/-!
# Miyake, Theorem 4.8.2 for the trivial character (the Eisenstein case)

Miyake, *Modular Forms* (Springer 1989), Theorem 4.8.2, p. 183, in the corrected form
`ModularFormsKB.Miyake.Sec4_8.ImaginaryQuadraticThetaStatement'`.

**Proved here.** `imaginaryQuadraticTheta'_trivial`: for every imaginary quadratic field `K` of
discriminant `d`, the conclusion of the corrected statement holds for the modulus `𝔫 = 𝓞_K`,
`u = 0` and the trivial Hecke character `ξ = 1`: `χ = χ_d` is a Dirichlet character modulo
`|d| = |d| N_K(𝓞_K)` with `χ(m) = χ_d(m) ξ((m))`, and `f(z; 1) = Σ_𝔞 e(N(𝔞) z)` (the coefficient
of `e(nz)` is the number of ideals of norm `n`) is, after adding its constant term, the
normalized weight-one Eisenstein series `E_1(1, χ_d)` of Tau Ceti, a modular form of weight one
and character `χ_d`. The cusp-form and primitivity clauses are void in this case, because the
trivial character is induced from the trivial Dirichlet character through the norm.

The proof is the first half of the refutation `not_imaginaryQuadraticThetaStatement`: the coefficients are `Σ_{m ∣ n} χ_d(m)` by Theorem 3.3.3
(`Sec3_3.theorem_3_3_3_coeff`), which are those of `E_1(1, χ_d)`
(`TauCeti.EisensteinSeries.qExpansion_normalizedCharE1MF_coeff`).

The general case (every modulus `𝔫`, every `u`, every `ξ`) is open, loose end LE-MF-0229.
-/

open NumberField TauCeti.Multiquadratic

noncomputable section

namespace ModularFormsKB.Miyake.Sec4_8

open Wave11 Wave4 Matrix.SpecialLinearGroup

variable {K : Type*} [Field K] [NumberField K]

/-- The trivial Hecke character is induced from the trivial Dirichlet character modulo `1`. -/
lemma trivialIdealHeckeChar_isInducedFromDirichlet :
    (trivialIdealHeckeChar : IdealHeckeChar (⊤ : Ideal (𝓞 K))).IsInducedFromDirichlet := by
  refine ⟨1, 1, fun 𝔞 h𝔞 _ _ ↦ ?_⟩
  rw [trivialIdealHeckeChar_apply, if_neg h𝔞]
  exact (MulChar.one_apply (isUnit_of_subsingleton _)).symm

/-- The principal ideal of a nonzero rational integer is nonzero. -/
lemma span_intCast_eq_bot_iff (m : ℤ) : Ideal.span {(m : 𝓞 K)} = ⊥ ↔ m = 0 := by
  rw [Ideal.span_singleton_eq_bot]
  exact_mod_cast Int.cast_eq_zero

/-- **Miyake, Theorem 4.8.2, Eisenstein case `𝔫 = 𝓞_K`, `u = 0`, `ξ = 1`**: the conclusion of the
corrected statement `ImaginaryQuadraticThetaStatement'` for the trivial Hecke character. The
character is `χ_d`, and the form is the normalized weight-one Eisenstein series of `χ_d`, whose
coefficients `n ≥ 1` are the numbers of ideals of norm `n`. -/
@[kb "miyake1989" "Theorem 4.8.2, p. 183 (trivial character, modulus O_K)"]
theorem imaginaryQuadraticTheta'_trivial (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K]
    (σ : K →+* ℂ) :
    haveI : NeZero ((discr K).natAbs * Ideal.absNorm (⊤ : Ideal (𝓞 K))) :=
      ⟨level_ne_zero top_ne_bot⟩
    ∃ χ : DirichletCharacter ℂ ((discr K).natAbs * Ideal.absNorm (⊤ : Ideal (𝓞 K))),
      (∀ m : ℤ, χ m = (TauCeti.kroneckerSym (discr K) m : ℂ) *
        (trivialIdealHeckeChar : IdealHeckeChar (⊤ : Ideal (𝓞 K))) (Ideal.span {(m : 𝓞 K)}) *
          (Int.sign m : ℂ) ^ 0) ∧
      ∃ f : modSpace ((0 + 1 : ℕ) : ℤ) χ, (∀ n : ℕ, n ≠ 0 →
          coeffMod f n = thetaCoeff (trivialIdealHeckeChar : IdealHeckeChar (⊤ : Ideal (𝓞 K))) 0 n) ∧
        (¬ (0 = 0 ∧
            (trivialIdealHeckeChar : IdealHeckeChar (⊤ : Ideal (𝓞 K))).IsInducedFromDirichlet) →
          f ∈ LinearMap.range (TauCeti.cuspToModFormCharSpace ((0 + 1 : ℕ) : ℤ) χ.toUnitHom) ∧
          ((trivialIdealHeckeChar : IdealHeckeChar (⊤ : Ideal (𝓞 K))).IsPrimitive
              (fun a ↦ (σ a / (‖σ a‖ : ℂ)) ^ 0) →
            ∃ g : cuspSpace ((0 + 1 : ℕ) : ℤ) χ, Wave4.IsPrimitive g ∧
              TauCeti.cuspToModFormCharSpace ((0 + 1 : ℕ) : ℤ) χ.toUnitHom g = f)) := by
  set M := (discr K).natAbs * Ideal.absNorm (⊤ : Ideal (𝓞 K)) with hM
  haveI : NeZero M := ⟨level_ne_zero top_ne_bot⟩
  have hD := isFundamentalDiscr_discr hK
  haveI : NeZero (discr K).natAbs := ⟨Int.natAbs_ne_zero.2 (discr_ne_zero K)⟩
  set φ := fundamentalDiscriminantCharCast ℂ (discr K) hD with hφdef
  have huv : 1 * (discr K).natAbs ∣ M := by rw [one_mul]; exact Dvd.intro _ rfl
  have hdM : (discr K).natAbs ∣ M := Dvd.intro _ rfl
  set E := TauCeti.EisensteinSeries.normalizedCharE1MF (1 : DirichletCharacter ℂ 1) φ huv
  have h1 : ∀ x : ZMod 1, (1 : DirichletCharacter ℂ 1) x = 1 :=
    fun x ↦ MulChar.one_apply (isUnit_of_subsingleton x)
  have hφneg : φ (-1) = -1 := by
    rw [hφdef, fundamentalDiscriminantCharCast, MulChar.ringHomComp_apply,
      fundamentalDiscriminantChar_neg_one, discr_sign_eq_neg_one hK]
    simp
  have hpar : (1 : DirichletCharacter ℂ 1) (-1) * φ (-1) = -1 := by rw [h1, hφneg, one_mul]
  have hφ : φ.IsPrimitive := isPrimitive_fundamentalDiscriminantCharCast hD
  -- the character
  set χ : DirichletCharacter ℂ M := φ.changeLevel hdM with hχ
  have hχ' : (1 : DirichletCharacter ℂ 1).changeLevel (dvd_of_mul_right_dvd huv) *
      φ.changeLevel (dvd_of_mul_left_dvd huv) = χ := by
    rw [map_one, one_mul]
  have hφint : ∀ m : ℤ, φ m = (TauCeti.kroneckerSym (discr K) m : ℂ) := by
    intro m
    rw [hφdef, fundamentalDiscriminantCharCast, MulChar.ringHomComp_apply,
      fundamentalDiscriminantChar_intCast]
    simp
  have hdisc1 : (discr K).natAbs ≠ 1 := by
    intro h
    have := hD.emod_four_eq_zero_or_one
    have hneg : discr K < 0 := by
      have := discr_sign_eq_neg_one hK (K := K)
      exact Int.sign_eq_neg_one_iff_neg.mp this
    omega
  refine ⟨χ, fun m ↦ ?_, ⟨E, ?_⟩, fun n hn ↦ ?_, fun h ↦ absurd ⟨rfl,
    trivialIdealHeckeChar_isInducedFromDirichlet⟩ h⟩
  · -- the values of the character
    have hM1 : M = (discr K).natAbs := by rw [hM, Ideal.absNorm_top, mul_one]
    rw [trivialIdealHeckeChar_apply, pow_zero, mul_one]
    by_cases hcop : IsCoprime m (M : ℤ)
    · rw [hχ, DirichletCharacter.changeLevel_eq_cast_of_dvd' φ hdM hcop, hφint]
      have hm : m ≠ 0 := by
        rintro rfl
        rw [isCoprime_zero_left, Int.isUnit_iff, hM1] at hcop
        omega
      rw [if_neg ((span_intCast_eq_bot_iff m).not.mpr hm), mul_one]
    · have h0 : TauCeti.kroneckerSym (discr K) m = 0 := by
        rw [TauCeti.kroneckerSym_eq_zero_iff]
        intro h
        apply hcop
        rw [hM1, Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
        simpa [Int.gcd, Int.natAbs_natCast, Int.natAbs_abs] using h
      rw [h0, Int.cast_zero, zero_mul]
      apply MulChar.map_nonunit
      rw [ZMod.isUnit_intCast_iff_isCoprime, isCoprime_comm]
      exact hcop
  · -- membership in the character space
    have hmem := TauCeti.EisensteinSeries.normalizedCharE1MF_mem_modFormCharSpace
      (1 : DirichletCharacter ℂ 1) φ huv
    rw [hχ'] at hmem
    exact hmem
  · -- the coefficients `n ≥ 1`
    simp only [coeffMod]
    change (UpperHalfPlane.qExpansion 1 ⇑E).coeff n = _
    rw [thetaCoeff_trivial hn,
      TauCeti.EisensteinSeries.qExpansion_normalizedCharE1MF_coeff _ φ huv hpar hφ hn,
      DirichletCharacter.twistedDivisorSum_apply]
    have h33 := Sec3_3.theorem_3_3_3_coeff hK hn
    have h33' := congrArg (Int.cast : ℤ → ℂ) h33
    push_cast at h33'
    rw [h33']
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [h1, one_mul, pow_zero, mul_one, hφdef, fundamentalDiscriminantCharCast,
      MulChar.ringHomComp_apply]
    simp

end ModularFormsKB.Miyake.Sec4_8
