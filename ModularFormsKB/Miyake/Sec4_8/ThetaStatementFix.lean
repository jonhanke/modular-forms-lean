import ModularFormsKB.Miyake.Wave11.QuadraticTheta
import ModularFormsKB.Miyake.Sec3_3.DedekindZeta
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.ConstantTerm
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.Normalized
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Realization
import TauCeti.NumberTheory.ModularForms.QExpansion.Positive
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import ModularFormsKB.Citation
/-!
# Miyake, Theorem 4.8.2: the constant term in the Eisenstein case

Miyake, *Modular Forms* (Springer 1989), Theorem 4.8.2, p. 183.

The statement `ModularFormsKB.Miyake.Wave11.ImaginaryQuadraticThetaStatement` (job mf-miyake-w11)
asks for a form `f ∈ 𝒢_{u+1}(N, χ)` all of whose coefficients, **including the constant one**,
are those of `Σ_𝔞 ξ(𝔞) N(𝔞)^{u/2} e(N(𝔞) z)` (the sum over the nonzero integral ideals, so the
constant coefficient is `0`); and, for `ξ` primitive, that `f` is a primitive form (a cusp form).
Both requirements fail in the Eisenstein case `u = 0`, `ξ` induced from a Dirichlet character
through the norm, which Miyake's theorem singles out: there `f(z; ξ)` is an Eisenstein series and
carries a nonzero constant term.

**Proved here.** `not_imaginaryQuadraticThetaStatement`: for every imaginary quadratic field `K`
the wave 11 statement is false. Take `𝔫 = 𝓞_K`, `u = 0` and `ξ` the trivial character. The
statement would give `f ∈ 𝒢_1(|d|, χ)` with constant coefficient `0` and `n`-th coefficient the
number of ideals of norm `n`, which is `Σ_{m ∣ n} χ_d(m)` (Theorem 3.3.3, `theorem_3_3_3_coeff`).
Tau Ceti's normalized weight-one Eisenstein series `E = normalizedCharE1MF 1 χ_d` has the same
positive coefficients (`qExpansion_normalizedCharE1MF_coeff`), so `f = E` (a form of nonzero
weight is determined by its positive coefficients, `eq_of_forall_pos_qExpansion_coeff_eq`); but
the constant coefficient of `E` is `-B_{1, χ_d}/2 ≠ 0`
(`qExpansion_normalizedCharE1MF_coeff_zero_ne_zero_iff`). (For `K = ℚ(i)` this is
`Σ_{n ≥ 1} r₂(n)/4 qⁿ = (θ(z)² - 1)/4`, which is not modular.)

**Corrected statement.** `ImaginaryQuadraticThetaStatement'` asks only for the coefficients
`n ≥ 1` (the constant term is then determined, and is `0` whenever `f` is a cusp form), and asks
for primitivity only outside the Eisenstein case. It is stated, not proved (loose end
LE-MF-0229); the error in the wave 11 statement is loose end LE-MF-0245. Whether Miyake's printed
statement itself shows the constant term could not be checked against the page.
-/

open NumberField TauCeti.Multiquadratic

noncomputable section

namespace ModularFormsKB.Miyake.Sec4_8

open Wave11 Wave4 Matrix.SpecialLinearGroup

variable {K : Type*} [Field K] [NumberField K]

/-- The trivial Hecke character mod `𝓞_K`: `1` on the nonzero ideals, `0` on `⊥`. -/
def trivialIdealHeckeChar : IdealHeckeChar (⊤ : Ideal (𝓞 K)) where
  toFun 𝔞 := if 𝔞 = ⊥ then 0 else 1
  map_top := by simp
  map_mul 𝔞 𝔟 := by
    by_cases ha : 𝔞 = ⊥ <;> by_cases hb : 𝔟 = ⊥ <;> simp [ha, hb, Ideal.mul_eq_bot]
  norm_eq_one 𝔞 h _ := by simp [h]
  eq_zero_of_not_isCoprime 𝔞 h := by
    exact absurd (by rw [Ideal.isCoprime_iff_sup_eq, sup_top_eq]) h
  map_bot := by simp

lemma trivialIdealHeckeChar_apply (𝔞 : Ideal (𝓞 K)) :
    (trivialIdealHeckeChar : IdealHeckeChar (⊤ : Ideal (𝓞 K))) 𝔞 = if 𝔞 = ⊥ then 0 else 1 := rfl

/-- The trivial character has the infinity type `(a/|a|)^0 = 1` for the modulus `𝓞_K`. -/
lemma trivialIdealHeckeChar_satisfiesInfinityType (σ : K →+* ℂ) :
    (trivialIdealHeckeChar : IdealHeckeChar (⊤ : Ideal (𝓞 K))).SatisfiesInfinityType
      (fun a ↦ (σ a / (‖σ a‖ : ℂ)) ^ 0) ⊤ := by
  intro a ha _ _
  rw [trivialIdealHeckeChar_apply, if_neg (by simpa [Ideal.span_singleton_eq_bot] using ha)]
  simp

/-- The coefficients of `f(z; 1)` (`u = 0`): the number of ideals of norm `n`. -/
lemma thetaCoeff_trivial {n : ℕ} (hn : n ≠ 0) :
    thetaCoeff (trivialIdealHeckeChar : IdealHeckeChar (⊤ : Ideal (𝓞 K))) 0 n =
      (TauCeti.dedekindZetaCoeff K n : ℂ) := by
  rw [thetaCoeff, if_neg hn]
  have h1 : ∀ 𝔞 ∈ (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 K) n).toFinset,
      (trivialIdealHeckeChar : IdealHeckeChar (⊤ : Ideal (𝓞 K))) 𝔞 *
        (Real.sqrt n : ℂ) ^ 0 = 1 := by
    intro 𝔞 h𝔞
    have hN : Ideal.absNorm 𝔞 = n := by simpa using h𝔞
    have h0 : 𝔞 ≠ ⊥ := fun h ↦ hn (by rw [← hN, h, Ideal.absNorm_bot])
    rw [trivialIdealHeckeChar_apply, if_neg h0, pow_zero, mul_one]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one, TauCeti.dedekindZetaCoeff]
  congr 1
  rw [← Set.ncard_eq_toFinset_card _ (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 K) n)]
  exact (Nat.card_coe_set_eq _).symm

/-- An imaginary quadratic field has negative discriminant. -/
lemma discr_sign_eq_neg_one (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] :
    (discr K).sign = -1 := by
  have h := IsTotallyComplex.finrank (K := K)
  have hc : InfinitePlace.nrComplexPlaces K = 1 := by omega
  rw [sign_discr, hc, pow_one]

/-- **The wave 11 statement of Miyake's Theorem 4.8.2 is false** for every imaginary quadratic
field: with `𝔫 = 𝓞_K`, `u = 0` and `ξ = 1` it would give a modular form of weight one with
constant coefficient `0` and the coefficients of the weight-one Eisenstein series, whose
constant coefficient is not `0`. -/
@[kb "miyake1989" "Theorem 4.8.2, p. 183 (the wave 11 statement fails in the Eisenstein case)"]
theorem not_imaginaryQuadraticThetaStatement (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] :
    ¬ ImaginaryQuadraticThetaStatement K := by
  intro h
  let σ : K →+* ℂ := (IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom
  have htop : (⊤ : Ideal (𝓞 K)) ≠ ⊥ := top_ne_bot
  obtain ⟨χ, -, f, hf, -, -⟩ := h hK inferInstance σ ⊤ htop 0 trivialIdealHeckeChar
    (trivialIdealHeckeChar_satisfiesInfinityType σ)
  set M := (discr K).natAbs * Ideal.absNorm (⊤ : Ideal (𝓞 K)) with hM
  haveI : NeZero M := ⟨level_ne_zero htop⟩
  have hD := isFundamentalDiscr_discr hK
  haveI : NeZero (discr K).natAbs := ⟨Int.natAbs_ne_zero.2 (discr_ne_zero K)⟩
  set φ := fundamentalDiscriminantCharCast ℂ (discr K) hD with hφdef
  have huv : 1 * (discr K).natAbs ∣ M := by rw [one_mul]; exact Dvd.intro _ rfl
  set E := TauCeti.EisensteinSeries.normalizedCharE1MF (1 : DirichletCharacter ℂ 1) φ huv
  have h1 : ∀ x : ZMod 1, (1 : DirichletCharacter ℂ 1) x = 1 :=
    fun x ↦ MulChar.one_apply (isUnit_of_subsingleton x)
  have hφneg : φ (-1) = -1 := by
    rw [hφdef, fundamentalDiscriminantCharCast, MulChar.ringHomComp_apply,
      fundamentalDiscriminantChar_neg_one, discr_sign_eq_neg_one hK]
    simp
  have hpar : (1 : DirichletCharacter ℂ 1) (-1) * φ (-1) = -1 := by rw [h1, hφneg, one_mul]
  have hφ : φ.IsPrimitive := isPrimitive_fundamentalDiscriminantCharCast hD
  have hfE : (f : ModularForm ((CongruenceSubgroup.Gamma1 M).map (mapGL ℝ)) 1) = E := by
    refine TauCeti.ModularForm.eq_of_forall_pos_qExpansion_coeff_eq one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map M) one_ne_zero fun n hn ↦ ?_
    have hfn := hf n
    simp only [coeffMod] at hfn
    rw [hfn, thetaCoeff_trivial hn.ne',
      TauCeti.EisensteinSeries.qExpansion_normalizedCharE1MF_coeff _ φ huv hpar hφ hn.ne',
      DirichletCharacter.twistedDivisorSum_apply]
    have h33 := Sec3_3.theorem_3_3_3_coeff hK hn.ne'
    have h33' := congrArg (Int.cast : ℤ → ℂ) h33
    push_cast at h33'
    rw [h33']
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [h1, one_mul, pow_zero, mul_one, hφdef, fundamentalDiscriminantCharCast,
      MulChar.ringHomComp_apply]
    simp
  have h0 := hf 0
  simp only [coeffMod, thetaCoeff, if_pos rfl] at h0
  have hE0 := (TauCeti.EisensteinSeries.qExpansion_normalizedCharE1MF_coeff_zero_ne_zero_iff
    (1 : DirichletCharacter ℂ 1) φ huv hpar DirichletCharacter.isPrimitive_one_level_one hφ).2
    (Or.inl rfl)
  have h0' : (UpperHalfPlane.qExpansion 1
      ⇑(f : ModularForm ((CongruenceSubgroup.Gamma1 M).map (mapGL ℝ)) 1)).coeff 0 = 0 := h0
  rw [hfE] at h0'
  exact hE0 h0'

/-- **Miyake, Theorem 4.8.2** (corrected statement; stated, not proved). Let `K` be an imaginary
quadratic field of discriminant `d`, embedded in `ℂ` by `σ`, and `ξ` a Hecke character mod `𝔫`
with `ξ((a)) = (a/|a|)^u` for `a ≡ 1 mod 𝔫` (`u ≥ 0`). Put `N = |d| N_K(𝔫)`. Then
`χ(m) = χ_d(m) ξ((m)) sgn(m)^u` is a Dirichlet character modulo `N`, and there is
`f ∈ 𝒢_{u+1}(N, χ)` whose `n`-th coefficient is `Σ_{N(𝔞) = n} ξ(𝔞) n^{u/2}` for every `n ≥ 1`
(the constant coefficient is not prescribed; it vanishes when `f` is a cusp form); `f` is a cusp
form unless `u = 0` and `ξ` is induced from a Dirichlet character through `N_K`, and in that
case, if `ξ` is primitive, `f` is a primitive form. Differs from
`Wave11.ImaginaryQuadraticThetaStatement` (false, `not_imaginaryQuadraticThetaStatement`) only
in the constant coefficient and in the Eisenstein case of the primitivity clause. -/
@[kb "miyake1989" "Theorem 4.8.2, p. 183 (corrected statement)"]
def ImaginaryQuadraticThetaStatement' (K : Type*) [Field K] [NumberField K] : Prop :=
  Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (σ : K →+* ℂ) (𝔫 : Ideal (𝓞 K)) (h𝔫 : 𝔫 ≠ ⊥) (u : ℕ) (ξ : IdealHeckeChar 𝔫),
    ξ.SatisfiesInfinityType (fun a ↦ (σ a / (‖σ a‖ : ℂ)) ^ u) 𝔫 →
    haveI : NeZero ((discr K).natAbs * Ideal.absNorm 𝔫) := ⟨level_ne_zero h𝔫⟩
    ∃ χ : DirichletCharacter ℂ ((discr K).natAbs * Ideal.absNorm 𝔫),
      (∀ m : ℤ, χ m = (TauCeti.kroneckerSym (discr K) m : ℂ) * ξ (Ideal.span {(m : 𝓞 K)}) *
        (Int.sign m : ℂ) ^ u) ∧
      ∃ f : modSpace ((u + 1 : ℕ) : ℤ) χ, (∀ n : ℕ, n ≠ 0 → coeffMod f n = thetaCoeff ξ u n) ∧
        (¬ (u = 0 ∧ ξ.IsInducedFromDirichlet) →
          f ∈ LinearMap.range (TauCeti.cuspToModFormCharSpace ((u + 1 : ℕ) : ℤ) χ.toUnitHom) ∧
          (ξ.IsPrimitive (fun a ↦ (σ a / (‖σ a‖ : ℂ)) ^ u) →
            ∃ g : cuspSpace ((u + 1 : ℕ) : ℤ) χ, Wave4.IsPrimitive g ∧
              TauCeti.cuspToModFormCharSpace ((u + 1 : ℕ) : ℤ) χ.toUnitHom g = f))

end ModularFormsKB.Miyake.Sec4_8
