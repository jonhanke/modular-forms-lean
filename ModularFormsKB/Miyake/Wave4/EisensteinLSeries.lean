import ModularFormsKB.Miyake.Wave4.Notation
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.ConstantTerm
import TauCeti.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Miyake, Theorem 4.7.1: the modular form with `L(s; f) = L(s, χ₁) L(s - k + 1, χ₂)`

Miyake, *Modular Forms* (Springer 1989), §4.7, p. 177.

Let `χ₁`, `χ₂` be Dirichlet characters modulo `M₁`, `M₂` satisfying (4.7.2), `M = M₁ M₂`,
`χ = χ₁ χ₂` (as characters modulo `M`), and `k ≥ 1` with `χ(-1) = (-1)^k`. Then there is
`f = Σ aₙ qⁿ ∈ 𝒢_k(M, χ)` with `L(s; f) = L(s, χ₁) L(s - k + 1, χ₂)`, i.e.
`aₙ = Σ_{0 < d ∣ n} χ₁(n/d) χ₂(d) d^{k-1}` for `n ≥ 1`, and an explicit constant term.

**Covered here:** case (ii) of (4.7.2) (both characters primitive) with `k ≥ 3`: the
coefficients `aₙ`, `n ≥ 1` (`exists_modSpace_coeff_eq`), the vanishing of `a₀` when `χ₁` is
non-trivial (`M₁ ≠ 1`), and the identity of `L`-series for `Re s > k` (`exists_modSpace_LSeries_eq`).
**Not covered:** `k ≤ 2` (including case (i), `k = 2` with both characters trivial), and the value
`a₀ = -B_{k, χ₂}/(2k)` when `χ₁` is trivial.

Proof: Tau Ceti's Eisenstein series with characters `G_k^{χ₁, χ₂}`
(`TauCeti.EisensteinSeries.charEisensteinSeriesMF`), whose coefficients for primitive `χ₂` are a
nonzero constant (a Gauss sum of `χ₂⁻¹` times `2(-2πi)^k/((k-1)! M₂^k)`) times the twisted divisor
sum (`qExpansion_charEisensteinSeriesMF_coeff_of_isPrimitive`), rescaled. Miyake's own proof goes
through Weil's converse theorem (Theorem 4.3.15, `Sec4_3/WeilTheorem.lean`); the Eisenstein series
route is Miyake's §7.1.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups LSeries.notation

noncomputable section

namespace ModularFormsKB.Miyake.Wave4

private lemma term_twist {M : ℕ} (χ : DirichletCharacter ℂ M) {k : ℕ} (hk : 1 ≤ k) (s : ℂ) :
    LSeries.term (fun n : ℕ ↦ χ n * (n : ℂ) ^ (k - 1)) s =
      LSeries.term (fun n : ℕ ↦ χ n) (s - k + 1) := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  have h : s - k + 1 = s - ((k - 1 : ℕ) : ℂ) := by
    rw [Nat.cast_sub hk]; push_cast; ring
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [h, Complex.cpow_sub _ _ hn', Complex.cpow_natCast]
  field_simp

/-- **Miyake, Theorem 4.7.1**, case (ii) of (4.7.2), `k ≥ 3`, coefficient form: for primitive
Dirichlet characters `χ₁ mod M₁`, `χ₂ mod M₂` with `χ₁(-1) χ₂(-1) = (-1)^k`, there is
`f ∈ 𝒢_k(M₁ M₂, χ₁ χ₂)` with `aₙ(f) = Σ_{d ∣ n} χ₁(n/d) χ₂(d) d^{k-1}` for `n ≥ 1`, and
`a₀(f) = 0` when `χ₁` is non-trivial. (Miyake's hypothesis that `χ₁` is primitive is kept; the
proof does not use it.) -/
@[kb "miyake1989" "Theorem 4.7.1, p. 177 (case (ii), k >= 3, coefficients)"]
theorem exists_modSpace_coeff_eq {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂] {k : ℕ} (hk : 3 ≤ k)
    (χ₁ : DirichletCharacter ℂ M₁) (χ₂ : DirichletCharacter ℂ M₂) (_h₁ : χ₁.IsPrimitive)
    (h₂ : χ₂.IsPrimitive) (hpar : χ₁ (-1) * χ₂ (-1) = (-1) ^ k) :
    ∃ f : modSpace (N := M₁ * M₂) (k : ℤ)
        (χ₁.changeLevel (dvd_mul_right M₁ M₂) * χ₂.changeLevel (dvd_mul_left M₂ M₁)),
      (∀ n : ℕ, n ≠ 0 →
        coeffMod f n = ∑ d ∈ n.divisors, χ₁ (n / d : ℕ) * χ₂ d * (d : ℂ) ^ (k - 1)) ∧
      (M₁ ≠ 1 → coeffMod f 0 = 0) := by
  have hk' : (3 : ℤ) ≤ k := by exact_mod_cast hk
  have huv : M₁ * M₂ ∣ M₁ * M₂ := dvd_rfl
  set G := TauCeti.EisensteinSeries.charEisensteinSeriesMF (N := M₁ * M₂) χ₁ χ₂ hk' huv with hG
  have hmem : G ∈ modSpace (N := M₁ * M₂) (k : ℤ)
      (χ₁.changeLevel (dvd_mul_right M₁ M₂) * χ₂.changeLevel (dvd_mul_left M₂ M₁)) :=
    TauCeti.EisensteinSeries.charEisensteinSeriesMF_mem_modFormCharSpace χ₁ χ₂ hk' huv
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℂ, C ≠ 0 ∧ ∀ n : ℕ, n ≠ 0 →
      (qExpansion 1 G).coeff n = C * DirichletCharacter.twistedDivisorSum (k - 1) χ₁ χ₂ n := by
    refine ⟨_, ?_, fun n hn ↦
      TauCeti.EisensteinSeries.qExpansion_charEisensteinSeriesMF_coeff_of_isPrimitive χ₁ χ₂ hk'
        huv (by simpa using hpar) h₂ hn⟩
    have hg : gaussSum χ₂⁻¹ ZMod.stdAddChar ≠ 0 :=
      DirichletCharacter.gaussSum_inv_ne_zero_of_isPrimitive (by exact_mod_cast NeZero.ne M₂) h₂
        (ZMod.isPrimitive_stdAddChar M₂)
    have hM : (M₂ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M₂
    refine mul_ne_zero (div_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ ?_))
      (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _) (pow_ne_zero _ hM))) hg
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨⟨C⁻¹ • G, Submodule.smul_mem _ _ hmem⟩, ?_, ?_⟩
  · intro n hn
    show (qExpansion 1 (C⁻¹ • G)).coeff n = _
    rw [ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _)]
    simp only [map_smul, smul_eq_mul]
    rw [hC n hn, DirichletCharacter.twistedDivisorSum_apply, ← mul_assoc, inv_mul_cancel₀ hC0,
      one_mul]
  · intro hM1
    show (qExpansion 1 (C⁻¹ • G)).coeff 0 = 0
    rw [ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _)]
    have h0 : (qExpansion 1 G).coeff 0 = 0 := by
      have h := TauCeti.EisensteinSeries.constantTermAt_charEisensteinSeriesMF
        (N := M₁ * M₂) χ₁ χ₂ hk' huv 1
      rw [constantTermAt_eq_coeff_zero_qExpansionAt, qExpansionAt_one,
        strictWidthInfty_Gamma1] at h
      have := ZMod.nontrivial_iff.mpr hM1
      have h00 : χ₁ 0 = 0 := MulChar.map_nonunit χ₁ not_isUnit_zero
      simp only [show ((M₂ : ℤ) ∣ (1 : SL(2, ℤ)) 1 0) by simp, ↓reduceIte] at h
      simpa [hG, h00] using h
    simp [h0]

/-- **Miyake, Theorem 4.7.1**, case (ii) of (4.7.2), `k ≥ 3`, `L`-series form: the form `f` of
`exists_modSpace_coeff_eq` satisfies `L(s; f) = L(s, χ₁) L(s - k + 1, χ₂)` for `Re s > k`. -/
@[kb "miyake1989" "Theorem 4.7.1, p. 177 (case (ii), k >= 3, L-series)"]
theorem exists_modSpace_LSeries_eq {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂] {k : ℕ} (hk : 3 ≤ k)
    (χ₁ : DirichletCharacter ℂ M₁) (χ₂ : DirichletCharacter ℂ M₂) (h₁ : χ₁.IsPrimitive)
    (h₂ : χ₂.IsPrimitive) (hpar : χ₁ (-1) * χ₂ (-1) = (-1) ^ k) :
    ∃ f : modSpace (N := M₁ * M₂) (k : ℤ)
        (χ₁.changeLevel (dvd_mul_right M₁ M₂) * χ₂.changeLevel (dvd_mul_left M₂ M₁)),
      ∀ s : ℂ, (k : ℝ) < s.re →
        LSeries (fun n ↦ coeffMod f n) s =
          LSeries (fun n ↦ χ₁ n) s * LSeries (fun n ↦ χ₂ n) (s - k + 1) := by
  obtain ⟨f, hf1, -⟩ := exists_modSpace_coeff_eq hk χ₁ χ₂ h₁ h₂ hpar
  refine ⟨f, fun s hs ↦ ?_⟩
  have hs1 : 1 < s.re := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hs2 : 1 < (s - k + 1).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re, Complex.one_re]
    linarith
  have hk1 : 1 ≤ k := by omega
  have hsum2 : LSeriesSummable (fun n : ℕ ↦ χ₂ n * (n : ℂ) ^ (k - 1)) s := by
    have := DirichletCharacter.LSeriesSummable_of_one_lt_re χ₂ hs2
    unfold LSeriesSummable at this ⊢
    rwa [term_twist χ₂ hk1 s]
  have hL2 : LSeries (fun n : ℕ ↦ χ₂ n * (n : ℂ) ^ (k - 1)) s =
      LSeries (fun n ↦ χ₂ n) (s - k + 1) := by
    unfold LSeries
    rw [term_twist χ₂ hk1 s]
  rw [LSeries_congr (g := (fun n : ℕ ↦ χ₁ n) ⍟ (fun n : ℕ ↦ χ₂ n * (n : ℂ) ^ (k - 1)))
    (fun {n} hn ↦ ?_) s]
  · rw [LSeries_convolution' (DirichletCharacter.LSeriesSummable_of_one_lt_re χ₁ hs1) hsum2, hL2]
  · rw [hf1 n hn]
    simp only [LSeries.convolution_def]
    rw [Nat.sum_divisorsAntidiagonal'
      (fun a b ↦ χ₁ (a : ZMod M₁) * (χ₂ (b : ZMod M₂) * (b : ℂ) ^ (k - 1)))]
    exact Finset.sum_congr rfl fun d _ ↦ by ring

end ModularFormsKB.Miyake.Wave4
