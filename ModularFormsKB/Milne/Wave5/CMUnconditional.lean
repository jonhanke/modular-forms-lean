import ModularFormsKB.Milne.Wave5.MultiplicationIsogeny

/-!
# Milne wave 5: the complex-multiplication results of Section 12, unconditionally

With `ComplexUniformization` now proved (`ModularFormsKB.Milne.Wave5.complexUniformization`, from
`endomorphismLiftStatement` and `multiplicationIsogenyStatement`), the results of Milne's Section 12 that the library
had proved from it become unconditional:

* **Proposition 12.6** (`exists_equiv_pic_ellCM`): `Pic(R) ≅ Ell(R)`, `[𝔞] ↦ j(ℂ/𝔞)`;
* **Corollary 12.7** (`card_ellCM`): `#Ell(R) = h(R)`;
* **Theorem 12.8** (`isAlgebraic_j_of_hasComplexMultiplication`): `j(E)` is algebraic for `E` over `ℂ` with complex
  multiplication;
* **Corollary 12.9** (`isAlgebraic_j_of_quadratic`): `j(z)` is algebraic when `ℚ[z]` is imaginary quadratic;
* **Corollary 12.16** (`jIntegralAtCM`, previously only stated as `JIntegralAtCM`): `j(z)` is an algebraic integer
  when `ℚ[z]` is imaginary quadratic (from `isIntegral_j_of_hasComplexMultiplication`, the complex form of 12.15).

Theorem 12.14 and Corollary 12.15 over number fields are in `Wave5/EndomorphismLift.lean`.
-/

open NumberField TauCeti TauCeti.Isogeny TauCeti.GlobalNumberFields UpperHalfPlane

namespace ModularFormsKB.Milne.Wave5

section Ideals

variable {K : Type*} [Field K] [NumberField K] (ι : K →+* ℂ) (O : NumberFieldOrder K)

/-- **Milne, Proposition 12.6** (unconditional): for an order `R` of an imaginary quadratic field, `[𝔞] ↦ j(ℂ/𝔞)` is a
bijection `Pic(R) ≅ Ell(R)`. -/
@[kb "milne2017mf" "Section 12, Prop. 12.6 (pdf p. 123)"]
theorem exists_equiv_pic_ellCM' (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] :
    ∃ φ : Pic O ≃ EllCM O, ∀ (I : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ)
      (L : PeriodPair), L.lattice = idealLattice ι O I →
        (φ (ClassGroup.mk (K := K) I : Pic O) : ℂ) = L.weierstrassCurve.j :=
  exists_equiv_pic_ellCM ι O complexUniformization hK

/-- **Milne, Corollary 12.7** (unconditional): there are exactly `h(R)` isomorphism classes of complex elliptic curves
with complex multiplication by `R`. -/
@[kb "milne2017mf" "Section 12, Cor. 12.7 (pdf p. 123)"]
theorem card_ellCM' (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] :
    Nat.card (EllCM O) = Nat.card (Pic O) :=
  card_ellCM O complexUniformization hK

end Ideals

/-- **Milne, Theorem 12.8** (unconditional): an elliptic curve over `ℂ` with complex multiplication has algebraic
`j`-invariant. -/
@[kb "milne2017mf" "Section 12, Thm. 12.8 (pdf p. 124)"]
theorem isAlgebraic_j_of_hasComplexMultiplication' (W : WeierstrassCurve ℂ) [W.IsElliptic]
    (hW : HasComplexMultiplication W) : IsAlgebraic ℚ W.j :=
  isAlgebraic_j_of_hasComplexMultiplication complexUniformization W hW

/-- **Milne, Corollary 12.9** (unconditional): if `z ∈ ℍ` generates an imaginary quadratic field, `j(z)` is
algebraic. -/
@[kb "milne2017mf" "Section 12, Cor. 12.9 (pdf p. 124)"]
theorem isAlgebraic_j_of_quadratic' (z : ℍ) (hz : IsIntegral ℚ (z : ℂ))
    (hz2 : (minpoly ℚ (z : ℂ)).natDegree = 2) : IsAlgebraic ℚ (TauCeti.ModularForm.j z) :=
  isAlgebraic_j_of_quadratic complexUniformization z hz hz2

/-- The curve `E(ℤz + ℤ)` has complex multiplication when `z` is quadratic: `d z` with `d` a common denominator of
the minimal polynomial maps the lattice into itself (the argument of `isAlgebraic_j_of_quadratic`). -/
theorem hasComplexMultiplication_of_quadratic (z : ℍ) (hz : IsIntegral ℚ (z : ℂ))
    (hz2 : (minpoly ℚ (z : ℂ)).natDegree = 2) : HasComplexMultiplication z.periodPair.weierstrassCurve := by
  obtain ⟨e, -⟩ := complexUniformization.endRingEquiv z.periodPair
  have hmonic := minpoly.monic hz
  have hroot := minpoly.aeval ℚ (z : ℂ)
  set p := minpoly ℚ (z : ℂ) with hpdef
  have hc2 : p.coeff 2 = 1 := by
    have := hmonic.coeff_natDegree
    rwa [hz2] at this
  rw [Polynomial.aeval_eq_sum_range, hz2] at hroot
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc2, zero_add] at hroot
  set b := p.coeff 1
  set c := p.coeff 0
  have hq : (z : ℂ) ^ 2 + (b : ℂ) * z + (c : ℂ) = 0 := by
    simpa [Rat.smul_def, add_comm, add_left_comm, add_assoc] using hroot
  set d : ℕ := b.den * c.den with hd
  have hdpos : 0 < d := Nat.mul_pos b.den_pos c.den_pos
  have hB : (d : ℂ) * b = ((b.num * c.den : ℤ) : ℂ) := by
    have : (d : ℚ) * b = ((b.num * c.den : ℤ) : ℚ) := by
      have h := Rat.mul_den_eq_num b
      push_cast [hd]
      linear_combination (c.den : ℚ) * h
    exact_mod_cast congrArg (fun q : ℚ => (q : ℂ)) this
  have hC : (d : ℂ) * c = ((c.num * b.den : ℤ) : ℂ) := by
    have : (d : ℚ) * c = ((c.num * b.den : ℤ) : ℚ) := by
      have h := Rat.mul_den_eq_num c
      push_cast [hd]
      linear_combination (b.den : ℚ) * h
    exact_mod_cast congrArg (fun q : ℚ => (q : ℂ)) this
  set B : ℤ := b.num * c.den
  set C : ℤ := c.num * b.den
  have hw : (d : ℂ) * z ∈ latticeEnd z.periodPair.lattice := by
    intro x hx
    obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 hx
    refine PeriodPair.mem_lattice.2 ⟨-m * B + n * d, -m * C, ?_⟩
    simp only [periodPair_ω₁, periodPair_ω₂]
    push_cast
    linear_combination (-((m : ℂ) * d)) * hq + ((m : ℂ) * z) * hB + (m : ℂ) * hC
  refine ⟨e.symm ⟨(d : ℂ) * z, hw⟩, fun n hf => ?_⟩
  have h1 := congrArg e hf
  rw [e.apply_symm_apply, map_zsmul, map_one] at h1
  have h2 := congrArg (fun x : latticeEnd z.periodPair.lattice => (x : ℂ)) h1
  simp at h2
  have h3 := congrArg Complex.im h2
  simp at h3
  rcases h3 with h3 | h3
  · omega
  · exact absurd h3 z.im_ne_zero

/-- **Milne, Corollary 12.16** (unconditional): if `z ∈ ℍ` generates an imaginary quadratic field, `j(z)` is an
algebraic integer. Milne deduces it from Corollary 12.15 over a number field; here it follows from the complex form
of 12.15 (`isIntegral_j_of_hasComplexMultiplication`, itself from the number-field form and a descent of the curve). -/
@[kb "milne2017mf" "Section 12, Cor. 12.16 (pdf p. 125)"]
theorem jIntegralAtCM : JIntegralAtCM := by
  refine ⟨fun z hz hz2 ↦ ?_⟩
  have := isIntegral_j_of_hasComplexMultiplication complexUniformization _
    (hasComplexMultiplication_of_quadratic z hz hz2)
  rwa [weierstrassCurve_j_periodPair] at this

end ModularFormsKB.Milne.Wave5
