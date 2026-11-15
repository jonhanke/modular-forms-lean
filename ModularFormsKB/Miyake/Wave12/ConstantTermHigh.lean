import ModularFormsKB.Miyake.Wave12.ConstantTermTwo
import ModularFormsKB.Miyake.Wave11.ConstantTerm
import ModularFormsKB.Miyake.Wave4.EisensteinLSeries
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Bernoulli

/-!
# Miyake, Theorem 4.7.1: the constant term for `k ≥ 3` and the `L`-series in weights one and two

Miyake, *Modular Forms* (Springer 1989), Theorem 4.7.1, p. 177.

* `exists_modSpace_coeff_eq_constTerm`: for `k ≥ 3` (case (ii) of (4.7.2), both characters
  primitive), the form `f` with `aₙ = Σ_{d ∣ n} χ₁(n/d) χ₂(d) d^{k-1}` (`n ≥ 1`) has
  `a₀ = -B_{k, χ₂}/(2k)` if `χ₁` is trivial (`M₁ = 1`, so `χ = χ₂`) and `a₀ = 0` otherwise,
  Miyake's constant term. Wave 4 (`ModularFormsKB.Miyake.Wave4.exists_modSpace_coeff_eq`) had
  the coefficients and the vanishing of `a₀` for non-trivial `χ₁`.
* `LSeries_eq_of_coeff`: the coefficient identity gives
  `L(s; f) = L(s, χ₁) L(s - k + 1, χ₂)` for `Re s > k`, in every weight `k ≥ 1` (wave 4's argument
  for `k ≥ 3`, with the weight left free); `exists_modSpace_LSeries_eq_weightOne`,
  `exists_modSpace_LSeries_eq_weightTwo`, `exists_modSpace_LSeries_eq_weightTwo_trivial` are
  Miyake's `L`-series statement in weights one and two.

Together with waves 4, 10, 11 and `ConstantTermTwo.lean`, every weight and both cases of (4.7.2)
of Theorem 4.7.1 are covered, with `a₀` and the `L`-series.

Proofs: Tau Ceti's normalized Eisenstein series with characters
(`normalizedCharEisensteinSeriesMF`) and its constant term
`qExpansion_normalizedCharEisensteinSeriesMF_coeff_zero`.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups LSeries.notation

noncomputable section

namespace ModularFormsKB.Miyake.Wave12

open ModularFormsKB.Miyake.Wave4 ModularFormsKB.Miyake.Wave10 ModularFormsKB.Miyake.Wave11
  TauCeti.EisensteinSeries

/-- **Miyake, Theorem 4.7.1**, `k ≥ 3` (case (ii) of (4.7.2)), with the constant term: for
primitive `χ₁ mod M₁`, `χ₂ mod M₂` with `χ₁(-1) χ₂(-1) = (-1)^k`, there is
`f ∈ 𝒢_k(M₁ M₂, χ₁ χ₂)` with `aₙ(f) = Σ_{d ∣ n} χ₁(n/d) χ₂(d) d^{k-1}` for `n ≥ 1`, and
`a₀(f) = -B_{k, χ₂}/(2k)` if `χ₁` is trivial (`M₁ = 1`), `a₀(f) = 0` otherwise. -/
@[kb "miyake1989" "Theorem 4.7.1, p. 177 (k >= 3, with a_0)"]
theorem exists_modSpace_coeff_eq_constTerm {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂] {k : ℕ}
    (hk : 3 ≤ k) (χ₁ : DirichletCharacter ℂ M₁) (χ₂ : DirichletCharacter ℂ M₂)
    (_h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (hpar : χ₁ (-1) * χ₂ (-1) = (-1) ^ k) :
    ∃ f : modSpace (N := M₁ * M₂) (k : ℤ)
        (χ₁.changeLevel (dvd_mul_right M₁ M₂) * χ₂.changeLevel (dvd_mul_left M₂ M₁)),
      (∀ n : ℕ, n ≠ 0 →
        coeffMod f n = ∑ d ∈ n.divisors, χ₁ (n / d : ℕ) * χ₂ d * (d : ℂ) ^ (k - 1)) ∧
      coeffMod f 0 = if M₁ = 1 then -χ₂.generalizedBernoulli k / (2 * (k : ℂ)) else 0 := by
  have hk' : (3 : ℤ) ≤ k := by exact_mod_cast hk
  have huv : M₁ * M₂ ∣ M₁ * M₂ := dvd_rfl
  have hpar' : χ₁ (-1) * χ₂ (-1) = (-1) ^ (k : ℤ) := by simpa using hpar
  set F := normalizedCharEisensteinSeriesMF (N := M₁ * M₂) χ₁ χ₂ hk' huv with hF
  have hmem : F ∈ modSpace (N := M₁ * M₂) (k : ℤ)
      (χ₁.changeLevel (dvd_mul_right M₁ M₂) * χ₂.changeLevel (dvd_mul_left M₂ M₁)) :=
    normalizedCharEisensteinSeriesMF_mem_modFormCharSpace χ₁ χ₂ hk' huv
  refine ⟨⟨F, hmem⟩, fun n hn ↦ ?_, ?_⟩
  · show (qExpansion 1 F).coeff n = _
    rw [hF, qExpansion_normalizedCharEisensteinSeriesMF_coeff χ₁ χ₂ hk' huv hpar' h₂ hn,
      DirichletCharacter.twistedDivisorSum_apply]
  · show (qExpansion 1 F).coeff 0 = _
    rw [hF]
    exact qExpansion_normalizedCharEisensteinSeriesMF_coeff_zero χ₁ χ₂ hk' huv hpar' h₂

/-! ### The `L`-series in every weight -/

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

/-- **Miyake, Theorem 4.7.1**, the `L`-series from the coefficients, in every weight `k ≥ 1`: if
`aₙ = Σ_{d ∣ n} χ₁(n/d) χ₂(d) d^{k-1}` for `n ≥ 1`, then
`L(s; f) = L(s, χ₁) L(s - k + 1, χ₂)` for `Re s > k`. -/
theorem LSeries_eq_of_coeff {M₁ M₂ : ℕ} {k : ℕ} (hk : 1 ≤ k) (χ₁ : DirichletCharacter ℂ M₁)
    (χ₂ : DirichletCharacter ℂ M₂) (a : ℕ → ℂ)
    (ha : ∀ n : ℕ, n ≠ 0 → a n = ∑ d ∈ n.divisors, χ₁ (n / d : ℕ) * χ₂ d * (d : ℂ) ^ (k - 1))
    (s : ℂ) (hs : (k : ℝ) < s.re) :
    LSeries a s = LSeries (fun n ↦ χ₁ n) s * LSeries (fun n ↦ χ₂ n) (s - k + 1) := by
  have hs1 : 1 < s.re := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hs2 : 1 < (s - k + 1).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re, Complex.one_re]
    linarith
  have hsum2 : LSeriesSummable (fun n : ℕ ↦ χ₂ n * (n : ℂ) ^ (k - 1)) s := by
    have := DirichletCharacter.LSeriesSummable_of_one_lt_re χ₂ hs2
    unfold LSeriesSummable at this ⊢
    rwa [term_twist χ₂ hk s]
  have hL2 : LSeries (fun n : ℕ ↦ χ₂ n * (n : ℂ) ^ (k - 1)) s =
      LSeries (fun n ↦ χ₂ n) (s - k + 1) := by
    unfold LSeries
    rw [term_twist χ₂ hk s]
  rw [LSeries_congr (g := (fun n : ℕ ↦ χ₁ n) ⍟ (fun n : ℕ ↦ χ₂ n * (n : ℂ) ^ (k - 1)))
    (fun {n} hn ↦ ?_) s]
  · rw [LSeries_convolution' (DirichletCharacter.LSeriesSummable_of_one_lt_re χ₁ hs1) hsum2, hL2]
  · rw [ha n hn]
    simp only [LSeries.convolution_def]
    rw [Nat.sum_divisorsAntidiagonal'
      (fun a b ↦ χ₁ (a : ZMod M₁) * (χ₂ (b : ZMod M₂) * (b : ℂ) ^ (k - 1)))]
    exact Finset.sum_congr rfl fun d _ ↦ by ring

/-- **Miyake, Theorem 4.7.1**, `k = 1`, `L`-series form (with the constant term of wave 11):
for primitive `χ₁ mod M₁`, `χ₂ mod M₂` with `χ₁(-1) χ₂(-1) = -1`, there is
`f ∈ 𝒢₁(M₁ M₂, χ₁ χ₂)` with `L(s; f) = L(s, χ₁) L(s, χ₂)` for `Re s > 1`. -/
@[kb "miyake1989" "Theorem 4.7.1, p. 177 (k = 1, L-series)"]
theorem exists_modSpace_LSeries_eq_weightOne {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂]
    [NeZero (M₁ * M₂)]
    (χ₁ : DirichletCharacter ℂ M₁) (χ₂ : DirichletCharacter ℂ M₂) (h₁ : χ₁.IsPrimitive)
    (h₂ : χ₂.IsPrimitive) (hpar : χ₁ (-1) * χ₂ (-1) = -1) :
    ∃ f : modSpace (N := M₁ * M₂) 1
        (χ₁.changeLevel (dvd_mul_right M₁ M₂) * χ₂.changeLevel (dvd_mul_left M₂ M₁)),
      coeffMod f 0 = -((if M₂ = 1 then χ₁.generalizedBernoulli 1 else 0) +
        (if M₁ = 1 then χ₂.generalizedBernoulli 1 else 0)) / 2 ∧
      ∀ s : ℂ, 1 < s.re →
        LSeries (fun n ↦ coeffMod f n) s =
          LSeries (fun n ↦ χ₁ n) s * LSeries (fun n ↦ χ₂ n) s := by
  obtain ⟨f, hf, h0⟩ := exists_modSpace_coeff_eq_weightOne_constTerm χ₁ χ₂ h₁ h₂ hpar
  refine ⟨f, h0, fun s hs ↦ ?_⟩
  have := LSeries_eq_of_coeff (k := 1) le_rfl χ₁ χ₂ (fun n ↦ coeffMod f n)
    (fun n hn ↦ by rw [hf n hn]; simp) s (by simpa using hs)
  simpa using this

/-- **Miyake, Theorem 4.7.1**, `k = 2`, case (ii), `L`-series form: there is
`f ∈ 𝒢₂(M₁ M₂, χ₁ χ₂)` with Miyake's constant term and `L(s; f) = L(s, χ₁) L(s - 1, χ₂)` for
`Re s > 2`. -/
@[kb "miyake1989" "Theorem 4.7.1, p. 177 (k = 2, case (ii), L-series)"]
theorem exists_modSpace_LSeries_eq_weightTwo {M₁ M₂ : ℕ} [NeZero M₂] [NeZero (M₁ * M₂)]
    (χ₁ : DirichletCharacter ℂ M₁) (χ₂ : DirichletCharacter ℂ M₂) (h₁ : χ₁.IsPrimitive)
    (h₂ : χ₂.IsPrimitive) (hne : ¬ (χ₁ = 1 ∧ χ₂ = 1)) (hpar : χ₁ (-1) * χ₂ (-1) = 1) :
    ∃ f : modSpace (N := M₁ * M₂) 2
        (χ₁.changeLevel (dvd_mul_right M₁ M₂) * χ₂.changeLevel (dvd_mul_left M₂ M₁)),
      coeffMod f 0 = (if M₁ = 1 then -χ₂.generalizedBernoulli 2 / 4 else 0) ∧
      ∀ s : ℂ, 2 < s.re →
        LSeries (fun n ↦ coeffMod f n) s =
          LSeries (fun n ↦ χ₁ n) s * LSeries (fun n ↦ χ₂ n) (s - 1) := by
  obtain ⟨f, hf, h0⟩ := exists_modSpace_coeff_eq_weightTwo_constTerm χ₁ χ₂ h₁ h₂ hne hpar
  refine ⟨f, h0, fun s hs ↦ ?_⟩
  have := LSeries_eq_of_coeff (k := 2) (by norm_num) χ₁ χ₂ (fun n ↦ coeffMod f n)
    (fun n hn ↦ by rw [hf n hn]; simp) s (by simpa using hs)
  rw [this, show s - ((2 : ℕ) : ℂ) + 1 = s - 1 by push_cast; ring]

/-- **Miyake, Theorem 4.7.1**, `k = 2`, case (i), `L`-series form: for a prime `p` there is
`f ∈ 𝒢₂(p, 1)` with `a₀ = -(1 - p)/24` and `L(s; f) = ζ(s) L(s - 1, 1_p)` for `Re s > 2`
(`ζ(s)` written as the `L`-series of the trivial character modulo `1`). -/
@[kb "miyake1989" "Theorem 4.7.1, p. 177 (k = 2, case (i), L-series)"]
theorem exists_modSpace_LSeries_eq_weightTwo_trivial {p : ℕ} (hp : p.Prime) [NeZero p] :
    ∃ f : modSpace (N := p) 2 1,
      coeffMod f 0 = -(1 - (p : ℂ)) / 24 ∧
      ∀ s : ℂ, 2 < s.re →
        LSeries (fun n ↦ coeffMod f n) s =
          LSeries (fun n ↦ (1 : DirichletCharacter ℂ 1) n) s *
            LSeries (fun n ↦ (1 : DirichletCharacter ℂ p) n) (s - 1) := by
  obtain ⟨f, hf, h0⟩ := exists_modSpace_coeff_eq_weightTwo_trivial_constTerm hp
  refine ⟨f, h0, fun s hs ↦ ?_⟩
  have := LSeries_eq_of_coeff (k := 2) (by norm_num) (1 : DirichletCharacter ℂ 1)
    (1 : DirichletCharacter ℂ p) (fun n ↦ coeffMod f n) (fun n hn ↦ by
      rw [hf n hn]
      refine Finset.sum_congr rfl fun d _ ↦ ?_
      rw [show ((1 : DirichletCharacter ℂ 1) ((n / d : ℕ) : ZMod 1)) = 1 from
        MulChar.one_apply (isUnit_of_subsingleton _)]
      simp) s (by simpa using hs)
  rw [this, show s - ((2 : ℕ) : ℂ) + 1 = s - 1 by push_cast; ring]

end ModularFormsKB.Miyake.Wave12
