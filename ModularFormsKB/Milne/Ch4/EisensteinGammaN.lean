import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Weighted
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Primitive
import ModularFormsKB.Milne.Ch4.Petersson
import ModularFormsKB.Citation
/-!
# Milne, Chapter 4: Eisenstein series for $\Gamma(N)$

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 4, pdf pp. 64–66.

Milne's **restricted** Eisenstein series $G(z; c_0, d_0; N) = \sum (cz+d)^{-2k}$ over coprime $(c, d) \equiv
(c_0, d_0) \bmod N$ (Definition 4.36(a)) is Mathlib's `eisensteinSeries a (2k)` with `a = (c₀, d₀) mod N`; Mathlib's
`EisensteinSeries.eisensteinSeriesMF` makes it a modular form of weight $2k \ge 3$ for $\Gamma(N)$. The **general**
series (Definition 4.36(b)), over all $(c, d) \ne (0, 0)$ with $(c, d) \equiv (c_0, d_0)$, is `generalEisenstein`,
Tau Ceti's weighted Eisenstein series with the indicator weight of the class.

## Items
- Definition 4.36 (`generalEisenstein`; (a) is Mathlib's `eisensteinSeries`).
- Proposition 4.37 (`span_generalEisenstein`), proof omitted in the book.
- Remark 4.38 (b): orthogonality of cusp forms and Eisenstein series, stated as `EisensteinCuspOrthogonal` and proved in `Unfolding.lean` (`eisensteinCuspOrthogonal`); the
  consequence that the Eisenstein series span the orthogonal complement of $S_k(\Gamma(N))$ in $M_k(\Gamma(N))$
  (`orthogonal_cuspForms_iff_mem_eisenstein`).
-/

open UpperHalfPlane Complex ModularForm EisensteinSeries CongruenceSubgroup
open Matrix.SpecialLinearGroup
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne

/-- **Definition 4.36 (b)**: the general Eisenstein series of weight $k$ for $\Gamma(N)$,
$G(z; c_0, d_0; N) = \sum_{(c,d) \equiv (c_0,d_0),\ (c,d) \ne (0,0)} (cz+d)^{-k}$ (Milne's weight $2k$ is `k = 2 * k`). -/
@[kb "milne2017mf" "Section 4, Definition 4.36 (b) (pdf p. 66)"]
def generalEisenstein (N : ℕ) (k : ℤ) (a : Fin 2 → ZMod N) (z : ℍ) : ℂ :=
  TauCeti.EisensteinSeries.weightedEisensteinSeries (fun b ↦ if b = a then 1 else 0) k z

/-- **Definition 4.36 (a)** (Mathlib): the restricted Eisenstein series is the sum over coprime $(c, d) \equiv a$. -/
@[kb "milne2017mf" "Section 4, Definition 4.36 (a) (pdf p. 66)"]
theorem restrictedEisenstein_eq (N : ℕ) (k : ℤ) (a : Fin 2 → ZMod N) (z : ℍ) :
    eisensteinSeries a k z = ∑' v : gammaSet N 1 a, eisSummand k v z := rfl

/-- The series `∑ r^(-K)` over positive integers has summable norms for `K ≥ 3`. -/
private lemma summable_norm_inv_zpow_nat {K : ℤ} (hK : 3 ≤ K) :
    Summable fun r : ℕ ↦ ‖((r : ℂ) ^ K)⁻¹‖ := by
  have hk' : -(K : ℝ) < -1 := by exact_mod_cast (by omega : -K < -1)
  simpa only [norm_inv, norm_zpow, Complex.norm_natCast, ← zpow_neg,
    ← Real.rpow_intCast, Int.cast_neg] using (Real.summable_nat_rpow.mpr hk')

/-- The coefficient of the restricted series `E_c` in the general series `G_a`. -/
private def genCoeff (N : ℕ) (K : ℤ) (a c : Fin 2 → ZMod N) : ℂ :=
  ∑' r : ℕ, ((r : ℂ) ^ K)⁻¹ * (if r • c = a then 1 else 0)

/-- The coefficient of the general series `G_b` in the Möbius-inverted expression of `E_a`. -/
private def mobCoeff (N : ℕ) (K : ℤ) (a b : Fin 2 → ZMod N) : ℂ :=
  ∑' s : ℕ, (((ArithmeticFunction.moebius s : ℤ) : ℂ) * ((s : ℂ) ^ K)⁻¹) * (if s • b = a then 1 else 0)

/-- The general series is a finite combination of restricted series (Tau Ceti's decomposition by gcd). -/
private lemma generalEisenstein_eq_sum (N : ℕ) [NeZero N] {K : ℤ} (hK : 3 ≤ K)
    (a : Fin 2 → ZMod N) (z : ℍ) :
    generalEisenstein N K a z = ∑ c, genCoeff N K a c * eisensteinSeries c K z := by
  classical
  set W : (Fin 2 → ZMod N) → ℂ := fun b ↦ if b = a then (1 : ℂ) else 0 with hW
  have hscoeff (c : Fin 2 → ZMod N) :
      Summable fun r : ℕ ↦ ((r : ℂ) ^ K)⁻¹ * W (r • c) := by
    refine Summable.of_norm ((summable_norm_inv_zpow_nat hK).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun r ↦ ?_)
    rw [norm_mul]
    have h1 : ‖W (r • c)‖ ≤ 1 := by simp only [hW]; split_ifs <;> simp
    calc ‖((r : ℂ) ^ K)⁻¹‖ * ‖W (r • c)‖ ≤ ‖((r : ℂ) ^ K)⁻¹‖ * 1 :=
          mul_le_mul le_rfl h1 (norm_nonneg _) (norm_nonneg _)
      _ = _ := mul_one _
  have key := TauCeti.EisensteinSeries.weightedEisensteinSeries_eq_tsum_eisensteinSeries W hK z
  unfold generalEisenstein
  rw [key]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Summable.tsum_finsetSum]
  · refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [genCoeff, ← tsum_mul_right]
  · intro c _
    exact (hscoeff c).mul_right _

/-- A residue class with no primitive lift has vanishing restricted series. -/
private lemma eisensteinSeries_eq_zero_of_not_primitive (N : ℕ) (K : ℤ) (a : Fin 2 → ZMod N)
    (h : ¬ ∃ c d : ZMod N, c * a 0 + d * a 1 = 1) (z : ℍ) : eisensteinSeries a K z = 0 := by
  have hE : IsEmpty (gammaSet N 1 a) := by
    refine ⟨fun ⟨v, hv1, hv2⟩ ↦ h ?_⟩
    obtain ⟨c, d, hcd⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hv2
    refine ⟨(c : ZMod N), (d : ZMod N), ?_⟩
    have h0 : a 0 = ((v 0 : ℤ) : ZMod N) := (congrFun hv1 0).symm
    have h1 : a 1 = ((v 1 : ℤ) : ZMod N) := (congrFun hv1 1).symm
    rw [h0, h1]
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) hcd
  simp [eisensteinSeries, tsum_empty]

/-- Sum of the Möbius function over divisors. -/
private lemma sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun F : ArithmeticFunction ℤ ↦ F n) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

/-- Möbius inversion for a doubly indexed series. -/
private lemma tsum_moebius_mul {K : ℤ} (hK : 3 ≤ K) (u : ℕ → ℂ) (hu : u 0 = 0)
    (hb : ∀ n, ‖u n‖ ≤ ‖((n : ℂ) ^ K)⁻¹‖) :
    ∑' p : ℕ × ℕ, ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ) * u (p.1 * p.2) = u 1 := by
  have hS := summable_norm_inv_zpow_nat hK
  have h2 : Summable fun p : ℕ × ℕ ↦ ‖((p.1 : ℂ) ^ K)⁻¹‖ * ‖((p.2 : ℂ) ^ K)⁻¹‖ :=
    summable_mul_of_summable_norm (R := ℝ) (f := fun r : ℕ ↦ ‖((r : ℂ) ^ K)⁻¹‖)
      (g := fun r : ℕ ↦ ‖((r : ℂ) ^ K)⁻¹‖) (by simpa using hS) (by simpa using hS)
  have hsum : Summable fun p : ℕ × ℕ ↦ ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ) * u (p.1 * p.2) := by
    refine Summable.of_norm_bounded h2 fun p ↦ ?_
    rw [norm_mul]
    have hm : ‖((ArithmeticFunction.moebius p.1 : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    calc ‖((ArithmeticFunction.moebius p.1 : ℤ) : ℂ)‖ * ‖u (p.1 * p.2)‖
        ≤ 1 * ‖((((p.1 * p.2 : ℕ)) : ℂ) ^ K)⁻¹‖ :=
          mul_le_mul hm (hb _) (norm_nonneg _) zero_le_one
      _ = ‖((p.1 : ℂ) ^ K)⁻¹‖ * ‖((p.2 : ℂ) ^ K)⁻¹‖ := by
          rw [one_mul, ← norm_mul, Nat.cast_mul, mul_zpow, mul_inv]
  have hF := hsum.hasSum.tsum_fiberwise (fun p : ℕ × ℕ ↦ p.1 * p.2)
  have hfib (n : ℕ) : ∑' b : (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {n},
      ((ArithmeticFunction.moebius b.1.1 : ℤ) : ℂ) * u (b.1.1 * b.1.2) = if n = 1 then u 1 else 0 := by
    rcases eq_or_ne n 0 with rfl | hn
    · have : ∀ b : (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {0},
          ((ArithmeticFunction.moebius b.1.1 : ℤ) : ℂ) * u (b.1.1 * b.1.2) = 0 := by
        rintro ⟨⟨s, r⟩, hb⟩
        have h0 : s * r = 0 := hb
        simp [h0, hu]
      simp [this]
    · rw [show (fun p : ℕ × ℕ ↦ p.1 * p.2) ⁻¹' {n} = n.divisorsAntidiagonal by ext; simp [hn],
        Finset.tsum_subtype' n.divisorsAntidiagonal fun p ↦
          ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ) * u (p.1 * p.2)]
      have : ∑ p ∈ n.divisorsAntidiagonal, ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ) * u (p.1 * p.2)
          = ∑ p ∈ n.divisorsAntidiagonal, ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ) * u n :=
        Finset.sum_congr rfl fun p hp ↦ by rw [(Nat.mem_divisorsAntidiagonal.1 hp).1]
      rw [this, ← Finset.sum_mul,
        Nat.sum_divisorsAntidiagonal (fun i _ ↦ ((ArithmeticFunction.moebius i : ℤ) : ℂ))]
      have hm := sum_moebius_divisors n
      have hm' : ∑ i ∈ n.divisors, ((ArithmeticFunction.moebius i : ℤ) : ℂ) = if n = 1 then 1 else 0 := by
        have := congrArg (Int.cast : ℤ → ℂ) hm
        push_cast at this
        exact this
      rw [hm']
      split_ifs with h1
      · subst h1; simp
      · simp
  have hF' : HasSum (fun n : ℕ ↦ if n = 1 then u 1 else 0)
      (∑' p : ℕ × ℕ, ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ) * u (p.1 * p.2)) := by
    convert hF using 1
    funext n
    exact (hfib n).symm
  exact hF'.unique (hasSum_ite_eq 1 (u 1))

/-- The Möbius-inverted coefficients invert the general-to-restricted coefficient matrix. -/
private lemma mob_mul_gen (N : ℕ) [NeZero N] {K : ℤ} (hK : 3 ≤ K) (a c : Fin 2 → ZMod N) :
    ∑ b, mobCoeff N K a b * genCoeff N K b c = if c = a then 1 else 0 := by
  classical
  have hS := summable_norm_inv_zpow_nat hK
  let A : (Fin 2 → ZMod N) → ℕ → ℂ := fun b s ↦
    (((ArithmeticFunction.moebius s : ℤ) : ℂ) * ((s : ℂ) ^ K)⁻¹) * (if s • b = a then 1 else 0)
  let B : (Fin 2 → ZMod N) → ℕ → ℂ := fun b r ↦
    ((r : ℂ) ^ K)⁻¹ * (if r • c = b then 1 else 0)
  have hm : ∀ s : ℕ, ‖((ArithmeticFunction.moebius s : ℤ) : ℂ)‖ ≤ 1 := fun s ↦ by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hA : ∀ b, Summable fun s ↦ ‖A b s‖ := fun b ↦ by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun s ↦ ?_) hS
    simp only [A, norm_mul]
    have h1 : ‖(if s • b = a then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
    calc ‖((ArithmeticFunction.moebius s : ℤ) : ℂ)‖ * ‖((s : ℂ) ^ K)⁻¹‖ *
          ‖(if s • b = a then (1 : ℂ) else 0)‖
        ≤ 1 * ‖((s : ℂ) ^ K)⁻¹‖ * 1 :=
          mul_le_mul (mul_le_mul (hm s) le_rfl (norm_nonneg _) zero_le_one) h1 (norm_nonneg _)
            (by positivity)
      _ = _ := by ring
  have hB : ∀ b, Summable fun r ↦ ‖B b r‖ := fun b ↦ by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun r ↦ ?_) hS
    simp only [B, norm_mul]
    have h1 : ‖(if r • c = b then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
    calc ‖((r : ℂ) ^ K)⁻¹‖ * ‖(if r • c = b then (1 : ℂ) else 0)‖ ≤ ‖((r : ℂ) ^ K)⁻¹‖ * 1 :=
          mul_le_mul le_rfl h1 (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  have hprod : ∀ b, mobCoeff N K a b * genCoeff N K b c = ∑' p : ℕ × ℕ, A b p.1 * B b p.2 :=
    fun b ↦ tsum_mul_tsum_of_summable_norm (hA b) (hB b)
  have hsumm : ∀ b, Summable fun p : ℕ × ℕ ↦ A b p.1 * B b p.2 :=
    fun b ↦ summable_mul_of_summable_norm (hA b) (hB b)
  let u : ℕ → ℂ := fun n ↦ ((n : ℂ) ^ K)⁻¹ * (if n • c = a then 1 else 0)
  have hK0 : K ≠ 0 := by omega
  have hu0 : u 0 = 0 := by simp [u, zero_zpow _ hK0]
  have hub : ∀ n, ‖u n‖ ≤ ‖((n : ℂ) ^ K)⁻¹‖ := fun n ↦ by
    simp only [u, norm_mul]
    have h1 : ‖(if n • c = a then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
    calc ‖((n : ℂ) ^ K)⁻¹‖ * ‖(if n • c = a then (1 : ℂ) else 0)‖ ≤ ‖((n : ℂ) ^ K)⁻¹‖ * 1 :=
          mul_le_mul le_rfl h1 (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  have hterm : ∀ p : ℕ × ℕ, ∑ b, A b p.1 * B b p.2 =
      ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ) * u (p.1 * p.2) := by
    rintro ⟨s, r⟩
    simp only
    have hmul : (s * r) • c = s • r • c := mul_smul s r c
    rw [Finset.sum_eq_single (r • c)]
    · simp only [A, B, u, hmul]
      by_cases h : s • r • c = a
      · simp only [h, ite_true]
        simp only [Nat.cast_mul, mul_zpow, mul_inv]
        ring
      · simp only [h, ite_false, ite_true]
        ring
    · intro b _ hb
      have : ¬ r • c = b := fun h ↦ hb h.symm
      simp only [A, B, this, mul_zero, ite_false]
    · simp
  calc ∑ b, mobCoeff N K a b * genCoeff N K b c = ∑ b, ∑' p : ℕ × ℕ, A b p.1 * B b p.2 :=
        Finset.sum_congr rfl fun b _ ↦ hprod b
    _ = ∑' p : ℕ × ℕ, ∑ b, A b p.1 * B b p.2 :=
        (Summable.tsum_finsetSum fun b _ ↦ hsumm b).symm
    _ = ∑' p : ℕ × ℕ, ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ) * u (p.1 * p.2) :=
        tsum_congr hterm
    _ = u 1 := tsum_moebius_mul hK u hu0 hub
    _ = if c = a then 1 else 0 := by simp [u]

/-- Each restricted series is a finite combination of general series (Möbius inversion). -/
private lemma eisensteinSeries_eq_sum_general (N : ℕ) [NeZero N] {K : ℤ} (hK : 3 ≤ K)
    (a : Fin 2 → ZMod N) :
    eisensteinSeries a K = ∑ b, mobCoeff N K a b • generalEisenstein N K b := by
  funext z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [generalEisenstein_eq_sum N hK, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ c, ∑ b, mobCoeff N K a b * (genCoeff N K b c * eisensteinSeries c K z) =
      (if c = a then 1 else 0) * eisensteinSeries c K z := fun c ↦ by
    rw [← mob_mul_gen N hK a c, Finset.sum_mul]
    simp_rw [mul_assoc]
  simp_rw [this]
  simp

/-- The Petersson product is additive in the second variable on modular forms (first variable a cusp form). -/
private lemma milnePetersson_add_right' (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ)
    (f : CuspForm (Γ.map (mapGL ℝ)) (2 * k)) (g₁ g₂ : ModularForm (Γ.map (mapGL ℝ)) (2 * k)) :
    milnePetersson Γ k f ⇑(g₁ + g₂) = milnePetersson Γ k f g₁ + milnePetersson Γ k f g₂ := by
  simp only [milnePetersson, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have h : ⇑(g₁ + g₂) = ⇑g₁ + ⇑g₂ := rfl
  rw [h, SlashAction.add_slash]
  exact UpperHalfPlane.peterssonInner_add_left _ _ _ _ _
    (integrableOn_petersson_slash_right (2 * k) _ g₁ f _)
    (integrableOn_petersson_slash_right (2 * k) _ g₂ f _)

/-- Conjugate-homogeneity of the Petersson product in the second variable. -/
private lemma milnePetersson_smul_right' (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) (c : ℂ)
    (f g : ℍ → ℂ) :
    milnePetersson Γ k f (c • g) = (starRingEnd ℂ) c * milnePetersson Γ k f g := by
  simp only [milnePetersson, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [ModularForm.SL_smul_slash]
  exact UpperHalfPlane.peterssonInner_smul_left _ _ c _ _

/-- The Petersson product of a cusp form against a finite linear combination of modular forms. -/
private lemma milnePetersson_sum_right' (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ)
    (f : CuspForm (Γ.map (mapGL ℝ)) (2 * k)) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (G : ι → ModularForm (Γ.map (mapGL ℝ)) (2 * k)) :
    milnePetersson Γ k f ⇑(∑ i ∈ s, c i • G i) =
      ∑ i ∈ s, (starRingEnd ℂ) (c i) * milnePetersson Γ k f (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := milnePetersson_smul_right' Γ k 0 f 0
    simp only [Finset.sum_empty]
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, milnePetersson_add_right', ih]
    have h : ⇑(c a • G a) = c a • ⇑(G a) := rfl
    rw [h, milnePetersson_smul_right']

/-- **Proposition 4.37**: for weight $2k > 2$, the general Eisenstein series for $\Gamma(N)$ span the same space as the
restricted ones (those with $\gcd(c_0, d_0, N) = 1$): each is a linear combination of the others. -/
@[kb "milne2017mf" "Section 4, Proposition 4.37 (pdf p. 66)"]
theorem span_generalEisenstein (N : ℕ) [NeZero N] {k : ℕ} (hk : 2 ≤ k) :
    Submodule.span ℂ (Set.range fun a : Fin 2 → ZMod N ↦ generalEisenstein N (2 * k) a) =
      Submodule.span ℂ (Set.range fun a : {a : Fin 2 → ZMod N // ∃ c d : ZMod N, c * a 0 + d * a 1 = 1} ↦
        eisensteinSeries a.1 (2 * k : ℤ)) := by
  have hK : (3 : ℤ) ≤ 2 * (k : ℤ) := by omega
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    have h : generalEisenstein N (2 * k) a = ∑ c, genCoeff N (2 * k) a c • eisensteinSeries c (2 * k : ℤ) := by
      funext z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact generalEisenstein_eq_sum N hK a z
    change generalEisenstein N (2 * k) a ∈ Submodule.span ℂ _
    rw [h]
    refine Submodule.sum_mem _ fun c _ ↦ Submodule.smul_mem _ _ ?_
    by_cases hc : ∃ c' d : ZMod N, c' * c 0 + d * c 1 = 1
    · exact Submodule.subset_span ⟨⟨c, hc⟩, rfl⟩
    · have : eisensteinSeries c (2 * k : ℤ) = 0 :=
        funext fun z ↦ eisensteinSeries_eq_zero_of_not_primitive N _ c hc z
      rw [this]
      exact Submodule.zero_mem _
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    change eisensteinSeries a.1 (2 * k : ℤ) ∈ Submodule.span ℂ _
    rw [eisensteinSeries_eq_sum_general N hK a.1]
    exact Submodule.sum_mem _ fun b _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

/-- **Remark 4.38 (b)** (statement; proved as `eisensteinCuspOrthogonal` in `Unfolding.lean`): $\langle f, g\rangle = 0$ for every cusp form $f$ and every restricted
Eisenstein series $g$ of weight $2k > 2$ for $\Gamma(N)$ ("$\varphi_0$ gives the zeroth coefficient"). -/
@[kb "milne2017mf" "Section 4, Remark 4.38 (b) (pdf p. 66)"]
structure EisensteinCuspOrthogonal (N : ℕ) [NeZero N] (k : ℕ) : Prop where
  orth : ∀ (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (2 * k : ℤ)) (a : Fin 2 → ZMod N),
    milnePetersson (CongruenceSubgroup.Gamma N) k f (eisensteinSeries a (2 * k : ℤ)) = 0

/-- **Remark 4.38 (b)**: "the space of Eisenstein series is the orthogonal complement of $S_k(\Gamma)$ in
$M_k(\Gamma)$", proved from `EisensteinCuspOrthogonal`, Tau Ceti's decomposition $M_k = \mathcal E_k \oplus S_k$
(`TauCeti.EisensteinSeries.isCompl_primitiveEisensteinSubspace_cuspFormSubmodule`) and the definiteness of the
Petersson product. -/
@[kb "milne2017mf" "Section 4, Remark 4.38 (b) (pdf p. 66)"]
theorem orthogonal_cuspForms_iff_mem_eisenstein (N : ℕ) [NeZero N] {k : ℕ} (hk : 2 ≤ k)
    (horth : EisensteinCuspOrthogonal N k) (g : ModularForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (2 * k : ℤ)) :
    (∀ f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (2 * k : ℤ), milnePetersson (CongruenceSubgroup.Gamma N) k f g = 0) ↔
      ⇑g ∈ Submodule.span ℂ (Set.range fun a : Fin 2 → ZMod N ↦ eisensteinSeries a (2 * k : ℤ)) := by
  have hK : (3 : ℤ) ≤ 2 * (k : ℤ) := by omega
  have hmem : ⇑g ∈ Submodule.span ℂ (Set.range fun a : Fin 2 → ZMod N ↦ eisensteinSeries a (2 * k : ℤ)) ↔
      g ∈ TauCeti.EisensteinSeries.primitiveEisensteinSubspace N hK := by
    rw [TauCeti.EisensteinSeries.mem_primitiveEisensteinSubspace_iff,
      Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, DFunLike.coe_injective ?_⟩
      rw [← hc]
      ext z
      simp
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← hc]
      ext z
      simp
  have hback : ∀ (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (2 * k : ℤ))
      (e : ModularForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (2 * k : ℤ)),
      e ∈ TauCeti.EisensteinSeries.primitiveEisensteinSubspace N hK →
        milnePetersson (CongruenceSubgroup.Gamma N) k f e = 0 := by
    intro f e he
    obtain ⟨c, rfl⟩ := (TauCeti.EisensteinSeries.mem_primitiveEisensteinSubspace_iff hK e).mp he
    rw [milnePetersson_sum_right']
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    have h0 := horth.orth f a
    have h1 : ⇑(eisensteinSeriesMF hK a) =
        eisensteinSeries a (2 * k : ℤ) := rfl
    rw [h1, h0, mul_zero]
  rw [hmem]
  constructor
  · intro h
    have htop := TauCeti.EisensteinSeries.sup_primitiveEisensteinSubspace_cuspFormSubmodule_eq_top
      (N := N) hK
    have hg : g ∈ TauCeti.EisensteinSeries.primitiveEisensteinSubspace N hK ⊔
        ModularForm.cuspFormSubmodule _ _ := by
      rw [htop]; trivial
    obtain ⟨e, he, s, ⟨s', hs'⟩, hes⟩ := Submodule.mem_sup.mp hg
    have hsf : ⇑s = ⇑s' := by rw [← hs']; rfl
    have h1 : milnePetersson (CongruenceSubgroup.Gamma N) k s' ⇑g = 0 := h s'
    rw [← hes, milnePetersson_add_right', hback s' e he] at h1
    have h2 : milnePetersson (CongruenceSubgroup.Gamma N) k s' s' = 0 := by
      rw [zero_add, hsf] at h1
      exact h1
    have hs0 : s' = 0 := by
      by_contra hne
      have := (milnePetersson_self_pos (CongruenceSubgroup.Gamma N) k s' hne).2
      rw [h2] at this
      simp at this
    have hs0' : s = 0 := by rw [← hs', hs0]; simp
    rw [← hes, hs0', add_zero]
    exact he
  · intro hg f
    exact hback f g hg

end ModularFormsKB.Milne
