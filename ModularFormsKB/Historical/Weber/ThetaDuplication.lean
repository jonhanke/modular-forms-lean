import ModularFormsKB.Historical.Weber.ClassInvariantTable
import ModularFormsKB.Citation
/-!
# The duplication formulas of the theta constants and Jacobi's quartic identity

With Weber's theta constants `ϑ₀₀(ω) = ∑ q^{n²}`, `ϑ₀₁(ω) = ∑ (-1)ⁿ q^{n²}`, `ϑ₁₀(ω) = ∑ q^{(n+1/2)²}`
(`q = e^{πiω}`; `weberTheta00`, `weberTheta01`, `weberTheta10` of `ThetaEta.lean`), the duplication formulas
(Gauss; Jacobi, *Fundamenta nova* (1829), § 36 [unverified]; Weber 1891, § 23 [unverified]) are

  `ϑ₀₀(ω)² + ϑ₀₁(ω)² = 2 ϑ₀₀(2ω)²`,  `ϑ₀₀(ω) ϑ₀₁(ω) = ϑ₀₁(2ω)²`,  `ϑ₀₀(ω)² - ϑ₀₁(ω)² = 2 ϑ₁₀(2ω)²`.

Each is the rotation `(a, b) ↦ (a + b, a - b)` of the lattice `ℤ²` (with `m² + n² = 2(a² + b²)`), applied to the
double series of the left side. Eliminating `ϑ₀₀(ω)`, `ϑ₀₁(ω)` gives **Jacobi's quartic identity**
`ϑ₀₀⁴ = ϑ₀₁⁴ + ϑ₁₀⁴` at `2ω`, hence everywhere; with `ϑ₀₀ = η f²`, `ϑ₀₁ = η f₁²`, `ϑ₁₀ = η f₂²` (`ThetaEta.lean`) it is
Weber's `f⁸ = f₁⁸ + f₂⁸` (Weber 1891, § 34 [unverified]).

Neither the duplication formulas nor the quartic identity is in Mathlib or Tau Ceti (searched 2026-11-16:
`jacobiTheta₂` lemmas in Mathlib, `TauCeti/NumberTheory/ModularForms/JacobiTheta`).
-/

noncomputable section

open Complex
open scoped Real

namespace ModularFormsKB.Historical.Weber

open ModularFormsKB.WeberHeegnerStark (weberF weberF₂)

/-- The three duplication formulas of the theta constants. -/
def ThetaDuplication : Prop :=
  ∀ ω : ℂ, 0 < ω.im →
    weberTheta00 ω ^ 2 + weberTheta01 ω ^ 2 = 2 * weberTheta00 (2 * ω) ^ 2 ∧
    weberTheta00 ω * weberTheta01 ω = weberTheta01 (2 * ω) ^ 2 ∧
    weberTheta00 ω ^ 2 - weberTheta01 ω ^ 2 = 2 * weberTheta10 (2 * ω) ^ 2

/-- **Jacobi's quartic identity** `ϑ₀₀⁴ = ϑ₀₁⁴ + ϑ₁₀⁴` (Jacobi, *Fundamenta nova* (1829), § 36 [unverified]). -/
def JacobiQuartic : Prop :=
  ∀ ω : ℂ, 0 < ω.im → weberTheta00 ω ^ 4 = weberTheta01 ω ^ 4 + weberTheta10 ω ^ 4

/-- **Weber's `f⁸ = f₁⁸ + f₂⁸`** (Weber 1891, § 34 [unverified]). -/
def WeberEighthPowers : Prop :=
  ∀ ω : ℂ, 0 < ω.im → weberF ω ^ 8 = weberF₁ ω ^ 8 + weberF₂ ω ^ 8

section Duplication

/-- `(-1)^m` for `m : ℤ`. -/
def dupSgn (m : ℤ) : ℂ := (-1 : ℂ) ^ m

lemma dupSgn_add (m n : ℤ) : dupSgn (m + n) = dupSgn m * dupSgn n := zpow_add₀ (by norm_num) _ _

lemma dupSgn_even {m : ℤ} (h : Even m) : dupSgn m = 1 := Even.neg_one_zpow h

lemma dupSgn_odd {m : ℤ} (h : Odd m) : dupSgn m = -1 := Odd.neg_one_zpow h

lemma norm_dupSgn (m : ℤ) : ‖dupSgn m‖ = 1 := by simp [dupSgn]

lemma dupSgn_zero_of_odd {m n : ℤ} (h : Odd (m + n)) : dupSgn m + dupSgn n = 0 := by
  have h' : ¬ Even (m + n) := Int.not_even_iff_odd.mpr h
  rw [Int.even_add] at h'
  rcases Int.even_or_odd m with hm | hm <;> rcases Int.even_or_odd n with hn | hn
  · exact absurd ⟨fun _ ↦ hn, fun _ ↦ hm⟩ h'
  · rw [dupSgn_even hm, dupSgn_odd hn]; norm_num
  · rw [dupSgn_odd hm, dupSgn_even hn]; norm_num
  · exact absurd ⟨fun h1 ↦ absurd h1 (Int.not_even_iff_odd.mpr hm),
      fun h1 ↦ absurd h1 (Int.not_even_iff_odd.mpr hn)⟩ h'

/-- The terms `q^{m²}` of `ϑ₀₀`, `q = e^{πiω}`. -/
def tt (ω : ℂ) (m : ℤ) : ℂ := jacobiTheta₂_term m 0 ω

lemma summable_norm_term (z ω : ℂ) (hω : 0 < ω.im) :
    Summable fun m : ℤ ↦ ‖jacobiTheta₂_term m z ω‖ :=
  summable_norm_iff.mpr ((summable_jacobiTheta₂_term_iff z ω).2 hω)

lemma summable_norm_tt {ω : ℂ} (hω : 0 < ω.im) : Summable fun m ↦ ‖tt ω m‖ :=
  summable_norm_term 0 ω hω

lemma summable_norm_sgn_tt {ω : ℂ} (hω : 0 < ω.im) : Summable fun m ↦ ‖dupSgn m * tt ω m‖ :=
  (summable_norm_tt hω).congr fun m ↦ by rw [norm_mul, norm_dupSgn, one_mul]

lemma term_half (m : ℤ) (ω : ℂ) : jacobiTheta₂_term m (1 / 2) ω = dupSgn m * tt ω m := by
  unfold tt jacobiTheta₂_term dupSgn
  rw [mul_zero, zero_add]
  have : cexp (2 * π * I * m * (1 / 2) + π * I * m ^ 2 * ω) =
      cexp (m * (π * I)) * cexp (π * I * m ^ 2 * ω) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [this, Complex.exp_int_mul, Complex.exp_pi_mul_I]

lemma theta01_eq_tsum (ω : ℂ) : weberTheta01 ω = ∑' m : ℤ, dupSgn m * tt ω m := by
  unfold weberTheta01 jacobiTheta₂
  exact tsum_congr fun m ↦ term_half m ω

lemma theta00_eq_tsum (ω : ℂ) : weberTheta00 ω = ∑' m : ℤ, tt ω m := rfl

lemma tt_two_mul (ω : ℂ) (a b : ℤ) :
    tt (2 * ω) a * tt (2 * ω) b = tt ω (a + b) * tt ω (a - b) := by
  unfold tt jacobiTheta₂_term
  rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring

lemma tt_shift (ω : ℂ) (a b : ℤ) :
    tt ω (a + b + 1) * tt ω (a - b) = cexp (π * I * (2 * ω) / 2) *
      (jacobiTheta₂_term a (2 * ω / 2) (2 * ω) * jacobiTheta₂_term b (2 * ω / 2) (2 * ω)) := by
  unfold tt jacobiTheta₂_term
  simp only [← Complex.exp_add]
  congr 1; push_cast; ring

lemma theta10_sq {τ : ℂ} (hτ : 0 < τ.im) :
    weberTheta10 τ ^ 2 = ∑' p : ℤ × ℤ, cexp (π * I * τ / 2) *
      (jacobiTheta₂_term p.1 (τ / 2) τ * jacobiTheta₂_term p.2 (τ / 2) τ) := by
  have hn := summable_norm_term (τ / 2) τ hτ
  rw [tsum_mul_left, ← tsum_mul_tsum_of_summable_norm hn hn, weberTheta10, mul_pow, sq (jacobiTheta₂ _ _),
    jacobiTheta₂]
  congr 1
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma sq_tsum_two {f g : ℤ → ℂ} (hf : Summable fun m ↦ ‖f m‖) (hg : Summable fun m ↦ ‖g m‖) :
    (∑' m, f m) * (∑' m, g m) = ∑' p : ℤ × ℤ, f p.1 * g p.2 :=
  tsum_mul_tsum_of_summable_norm hf hg

/-- **The duplication formulas** (Gauss; Jacobi, *Fundamenta nova* (1829), § 36 [unverified]), proved: each
is a rotation of the lattice `ℤ²` applied to the double series of the left side. The sums
`ϑ₀₀² ± ϑ₀₁²` and `ϑ₀₀ ϑ₀₁ = ½ ∑ ((-1)^m + (-1)^n) q^{m²+n²}` are supported on `m + n` even resp. odd, which is
the range of `(a, b) ↦ (a + b, a - b)` resp. `(a, b) ↦ (a + b + 1, a - b)` (`Function.Injective.tsum_eq`),
and `m² + n² = 2(a² + b²)` resp. `2((a + ½)² + (b + ½)²)` there. -/
theorem thetaDuplication : ThetaDuplication := by
  intro ω hω
  have hω2 : 0 < (2 * ω).im := by simpa using hω
  have hA := summable_norm_tt hω
  have hB := summable_norm_sgn_tt hω
  have hA2 := summable_norm_tt hω2
  have hB2 := summable_norm_sgn_tt hω2
  have s1 := summable_mul_of_summable_norm hA hA
  have s2 := summable_mul_of_summable_norm hB hB
  have s3 := summable_mul_of_summable_norm hA hB
  have s3' : Summable fun p : ℤ × ℤ ↦ tt ω p.2 * (dupSgn p.1 * tt ω p.1) :=
    (Equiv.summable_iff (Equiv.prodComm ℤ ℤ)).mpr s3
  have e00 : weberTheta00 ω ^ 2 = ∑' p : ℤ × ℤ, tt ω p.1 * tt ω p.2 := by
    rw [sq, theta00_eq_tsum, sq_tsum_two hA hA]
  have e01 : weberTheta01 ω ^ 2 =
      ∑' p : ℤ × ℤ, (dupSgn p.1 * tt ω p.1) * (dupSgn p.2 * tt ω p.2) := by
    rw [sq, theta01_eq_tsum, sq_tsum_two hB hB]
  have e0001 : weberTheta00 ω * weberTheta01 ω =
      ∑' p : ℤ × ℤ, tt ω p.1 * (dupSgn p.2 * tt ω p.2) := by
    rw [theta00_eq_tsum, theta01_eq_tsum, sq_tsum_two hA hB]
  have f00 : weberTheta00 (2 * ω) ^ 2 = ∑' p : ℤ × ℤ, tt (2 * ω) p.1 * tt (2 * ω) p.2 := by
    rw [sq, theta00_eq_tsum, sq_tsum_two hA2 hA2]
  have f01 : weberTheta01 (2 * ω) ^ 2 =
      ∑' p : ℤ × ℤ, (dupSgn p.1 * tt (2 * ω) p.1) * (dupSgn p.2 * tt (2 * ω) p.2) := by
    rw [sq, theta01_eq_tsum, sq_tsum_two hB2 hB2]
  have g1_inj : Function.Injective (fun c : ℤ × ℤ ↦ (c.1 + c.2, c.1 - c.2)) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    omega
  have g2_inj : Function.Injective (fun c : ℤ × ℤ ↦ (c.1 + c.2 + 1, c.1 - c.2)) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    omega
  have hE : ∀ c : ℤ × ℤ, dupSgn (c.1 + c.2) * dupSgn (c.1 - c.2) = 1 := fun c ↦ by
    rw [← dupSgn_add]; exact dupSgn_even ⟨c.1, by ring⟩
  have hO : ∀ c : ℤ × ℤ, dupSgn (c.1 + c.2 + 1) * dupSgn (c.1 - c.2) = -1 := fun c ↦ by
    rw [← dupSgn_add]; exact dupSgn_odd ⟨c.1, by ring⟩
  refine ⟨?_, ?_, ?_⟩
  · -- ϑ₀₀² + ϑ₀₁² = 2 ϑ₀₀(2ω)²
    rw [e00, e01, f00, ← s1.tsum_add s2, ← tsum_mul_left]
    set F : ℤ × ℤ → ℂ := fun p ↦ tt ω p.1 * tt ω p.2 +
      (dupSgn p.1 * tt ω p.1) * (dupSgn p.2 * tt ω p.2) with hF
    have hsupp : Function.support F ⊆ Set.range (fun c : ℤ × ℤ ↦ (c.1 + c.2, c.1 - c.2)) := by
      intro p hp
      rw [Function.mem_support] at hp
      have hev : Even (p.1 + p.2) := by
        by_contra hne
        apply hp
        have h1 := dupSgn_add p.1 p.2
        rw [dupSgn_odd (Int.not_even_iff_odd.mp hne)] at h1
        simp only [hF]
        linear_combination (-(tt ω p.1 * tt ω p.2)) * h1
      obtain ⟨k, hk⟩ := hev
      exact ⟨(k, p.1 - k), Prod.ext (by simp only; omega) (by simp only; omega)⟩
    rw [← g1_inj.tsum_eq hsupp]
    refine tsum_congr fun c ↦ ?_
    simp only [hF]
    have h2 := tt_two_mul ω c.1 c.2
    linear_combination (tt ω (c.1 + c.2) * tt ω (c.1 - c.2)) * hE c - 2 * h2
  · -- ϑ₀₀ ϑ₀₁ = ϑ₀₁(2ω)²
    set L : ℤ × ℤ → ℂ := fun p ↦ tt ω p.1 * (dupSgn p.2 * tt ω p.2) with hL
    have hsw : ∑' p : ℤ × ℤ, L p = ∑' p : ℤ × ℤ, tt ω p.2 * (dupSgn p.1 * tt ω p.1) :=
      ((Equiv.prodComm ℤ ℤ).tsum_eq L).symm
    set F : ℤ × ℤ → ℂ := fun p ↦ L p + tt ω p.2 * (dupSgn p.1 * tt ω p.1) with hF
    have hsum : ∑' p, F p = 2 * ∑' p, L p := by
      rw [hF, s3.tsum_add s3', ← hsw]; ring
    have hsupp : Function.support F ⊆ Set.range (fun c : ℤ × ℤ ↦ (c.1 + c.2, c.1 - c.2)) := by
      intro p hp
      rw [Function.mem_support] at hp
      have hev : Even (p.1 + p.2) := by
        by_contra hne
        apply hp
        have h1 := dupSgn_zero_of_odd (Int.not_even_iff_odd.mp hne)
        simp only [hF, hL]
        linear_combination (tt ω p.1 * tt ω p.2) * h1
      obtain ⟨k, hk⟩ := hev
      exact ⟨(k, p.1 - k), Prod.ext (by simp only; omega) (by simp only; omega)⟩
    have hre : ∑' p, F p = 2 * ∑' c : ℤ × ℤ,
        (dupSgn c.1 * tt (2 * ω) c.1) * (dupSgn c.2 * tt (2 * ω) c.2) := by
      rw [← tsum_mul_left, ← g1_inj.tsum_eq hsupp]
      refine tsum_congr fun c ↦ ?_
      simp only [hF, hL]
      have h2 := tt_two_mul ω c.1 c.2
      have h3 : dupSgn (c.1 - c.2) = dupSgn (c.1 + c.2) := by
        rw [show c.1 + c.2 = (c.1 - c.2) + (c.2 + c.2) by ring, dupSgn_add,
          dupSgn_even ⟨c.2, rfl⟩, mul_one]
      have h4 := dupSgn_add c.1 c.2
      rw [h3]
      linear_combination (2 * tt ω (c.1 + c.2) * tt ω (c.1 - c.2)) * h4 -
        (2 * dupSgn c.1 * dupSgn c.2) * h2
    have key := mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0) (hsum.symm.trans hre)
    rw [e0001, f01]
    exact key
  · -- ϑ₀₀² - ϑ₀₁² = 2 ϑ₁₀(2ω)²
    rw [e00, e01, theta10_sq hω2, ← s1.tsum_sub s2, ← tsum_mul_left]
    set F : ℤ × ℤ → ℂ := fun p ↦ tt ω p.1 * tt ω p.2 -
      (dupSgn p.1 * tt ω p.1) * (dupSgn p.2 * tt ω p.2) with hF
    have hsupp : Function.support F ⊆ Set.range (fun c : ℤ × ℤ ↦ (c.1 + c.2 + 1, c.1 - c.2)) := by
      intro p hp
      rw [Function.mem_support] at hp
      have hodd : Odd (p.1 + p.2) := by
        by_contra hne
        apply hp
        have h1 := dupSgn_add p.1 p.2
        rw [dupSgn_even (Int.not_odd_iff_even.mp hne)] at h1
        simp only [hF]
        linear_combination (tt ω p.1 * tt ω p.2) * h1
      obtain ⟨k, hk⟩ := hodd
      exact ⟨(k, p.1 - k - 1), Prod.ext (by simp only; omega) (by simp only; omega)⟩
    rw [← g2_inj.tsum_eq hsupp]
    refine tsum_congr fun c ↦ ?_
    simp only [hF]
    have h2 := tt_shift ω c.1 c.2
    have h3 := hO c
    linear_combination 2 * h2 - (tt ω (c.1 + c.2 + 1) * tt ω (c.1 - c.2)) * h3

end Duplication

/-- **The duplication formulas imply Jacobi's quartic identity** (Jacobi, *Fundamenta nova* (1829), § 36
[unverified]): apply them at `ω/2`; with `A = ϑ₀₀(ω/2)²`, `B = ϑ₀₁(ω/2)²` one gets `ϑ₀₀(ω)² = (A + B)/2`,
`ϑ₁₀(ω)² = (A - B)/2`, `ϑ₀₁(ω)² = ϑ₀₀(ω/2) ϑ₀₁(ω/2)`, and `((A+B)/2)² = AB + ((A-B)/2)²`. -/
theorem jacobiQuartic_of_duplication (h : ThetaDuplication) : JacobiQuartic := by
  intro ω hω
  obtain ⟨h1, h2, h3⟩ := h (ω / 2) (by simpa using hω)
  rw [show 2 * (ω / 2) = ω by ring] at h1 h2 h3
  have hP : weberTheta00 ω ^ 2 = (weberTheta00 (ω / 2) ^ 2 + weberTheta01 (ω / 2) ^ 2) / 2 := by
    linear_combination (-1 / 2 : ℂ) * h1
  have hQ : weberTheta01 ω ^ 2 = weberTheta00 (ω / 2) * weberTheta01 (ω / 2) := h2.symm
  have hR : weberTheta10 ω ^ 2 = (weberTheta00 (ω / 2) ^ 2 - weberTheta01 (ω / 2) ^ 2) / 2 := by
    linear_combination (-1 / 2 : ℂ) * h3
  rw [show weberTheta00 ω ^ 4 = (weberTheta00 ω ^ 2) ^ 2 by ring,
    show weberTheta01 ω ^ 4 = (weberTheta01 ω ^ 2) ^ 2 by ring,
    show weberTheta10 ω ^ 4 = (weberTheta10 ω ^ 2) ^ 2 by ring, hP, hQ, hR]
  ring

/-- **Jacobi's quartic identity implies Weber's `f⁸ = f₁⁸ + f₂⁸`** (Weber 1891, § 34 [unverified]): with
`ϑ₀₀ = η f²`, `ϑ₀₁ = η f₁²`, `ϑ₁₀ = η f₂²` (`weberTheta00_eq` etc.) the quartic reads
`η⁴ (f⁸ - f₁⁸ - f₂⁸) = 0`, and `η ≠ 0`. -/
theorem weberEighthPowers_of_quartic (h : JacobiQuartic) : WeberEighthPowers := by
  intro ω hω
  have h4 := h ω hω
  rw [weberTheta00_eq hω, weberTheta01_eq hω, weberTheta10_eq hω] at h4
  have hη : ModularForm.eta ω ≠ 0 := ModularForm.eta_ne_zero hω
  have h5 : ModularForm.eta ω ^ 4 * (weberF ω ^ 8 - (weberF₁ ω ^ 8 + weberF₂ ω ^ 8)) = 0 := by
    linear_combination h4
  rcases mul_eq_zero.mp h5 with h6 | h6
  · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h6) hη
  · exact sub_eq_zero.mp h6

/-- **Jacobi's quartic identity** `ϑ₀₀⁴ = ϑ₀₁⁴ + ϑ₁₀⁴`, unconditional. -/
theorem jacobiQuartic : JacobiQuartic := jacobiQuartic_of_duplication thetaDuplication

/-- **Weber's `f⁸ = f₁⁸ + f₂⁸`**, unconditional (Weber 1891, § 34 [unverified]). -/
theorem weberEighthPowers : WeberEighthPowers := weberEighthPowers_of_quartic jacobiQuartic

end ModularFormsKB.Historical.Weber
