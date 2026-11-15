import ModularFormsKB.Milne.Wave12.ScalarRiemannRoch
import ModularFormsKB.Milne.Wave10.RiemannRochInputs

/-!
# Riemann–Roch on `X(Γ)` for every `Γ ⊇ Γ(pᵏ)`; Theorems 1.27, 2.22, 4.9 and Proposition 4.12 for these `Γ`

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Theorem 1.20 (pdf p. 21), Theorem 1.27 (p. 22),
Theorem 2.22 (p. 37), Theorem 4.9 (p. 51), Proposition 4.12 (p. 53).

If `l² ≡ 1 (mod 2pᵏ)` for a prime `p`, then `l ≡ ±1 (mod pᵏ)` (`dvd_sub_one_or_dvd_add_one`). Hence a matrix scalar
modulo `2pᵏ` is `±1` modulo `pᵏ`, and the image of `Γ_sc(2pᵏ)` in `PSL₂(ℝ)` lies in that of every `Γ ⊇ Γ(pᵏ)`
(`barGammaSc_le_of_Gamma_le`). So `riemannRoch_of_GammaSc_le` applies:

* **`riemannRoch_of_Gamma_primePow_le`**: Theorem 1.20 on `X(Γ)` for every `Γ ⊇ Γ(pᵏ)` (in particular `X(pᵏ)` and
  `X₁(pᵏ)`, `riemannRoch_Gamma_primePow`, `riemannRoch_Gamma1_primePow`);
* `dimensionFormula_of_Gamma_primePow_le`, `valenceFormula_of_Gamma_primePow_le`, `genus_of_Gamma_primePow_le`,
  `riemannHurwitz_of_Gamma_primePow_le`: Theorem 4.9, Proposition 4.12, Theorem 2.22, Theorem 1.27 for these `Γ`,
  through the reductions of waves 10 (`Wave10.dimensionFormula_of_riemannRoch'` and the others).
-/

open UpperHalfPlane CongruenceSubgroup Matrix TauCeti.RiemannSurface ModularFormsKB.Milne.RiemannSurface
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.Wave12

/-- If `2pᵏ ∣ l² - 1` for a prime `p`, then `pᵏ ∣ l - 1` or `pᵏ ∣ l + 1`. -/
theorem dvd_sub_one_or_dvd_add_one {p k : ℕ} (hp : p.Prime) {l : ℤ}
    (h : (2 * (p : ℤ) ^ k) ∣ l ^ 2 - 1) : ((p : ℤ) ^ k) ∣ l - 1 ∨ ((p : ℤ) ^ k) ∣ l + 1 := by
  have hfac : l ^ 2 - 1 = (l - 1) * (l + 1) := by ring
  rw [hfac] at h
  have hpk : ((p : ℤ) ^ k) ∣ (l - 1) * (l + 1) := dvd_trans (Dvd.intro_left 2 rfl) h
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  by_cases h2 : p = 2
  · subst h2
    rcases k with _ | k
    · simp
    have h2d : (2 : ℤ) ∣ (l - 1) * (l + 1) := dvd_trans (Dvd.intro _ rfl) h
    obtain ⟨u, hu⟩ : (2 : ℤ) ∣ l - 1 := by
      rcases Int.prime_two.dvd_or_dvd h2d with h' | ⟨t, ht⟩
      · exact h'
      · exact ⟨t - 1, by linarith⟩
    have hv : l + 1 = 2 * (u + 1) := by linarith
    rw [hu, hv] at h
    have h4 : (4 * (2 : ℤ) ^ k) ∣ 4 * (u * (u + 1)) := by
      have : (2 * (2 : ℤ) ^ (k + 1)) = 4 * 2 ^ k := by ring
      rw [← this]
      convert h using 1
      ring
    have hk : ((2 : ℤ) ^ k) ∣ u * (u + 1) := (mul_dvd_mul_iff_left (by norm_num)).1 h4
    rcases Int.even_or_odd u with he | ho
    · have hc : IsCoprime ((2 : ℤ) ^ k) (u + 1) := by
        apply IsCoprime.pow_left
        rw [Prime.coprime_iff_not_dvd Int.prime_two]
        rw [← even_iff_two_dvd, Int.not_even_iff_odd]
        exact he.add_one
      left
      rw [hu]; push_cast; rw [pow_succ, mul_comm ((2 : ℤ) ^ k) 2]
      exact mul_dvd_mul_left 2 (hc.dvd_of_dvd_mul_right hk)
    · have hc : IsCoprime ((2 : ℤ) ^ k) u := by
        apply IsCoprime.pow_left
        rw [Prime.coprime_iff_not_dvd Int.prime_two, ← even_iff_two_dvd, Int.not_even_iff_odd]
        exact ho
      right
      rw [hv]; push_cast; rw [pow_succ, mul_comm ((2 : ℤ) ^ k) 2]
      exact mul_dvd_mul_left 2 (hc.dvd_of_dvd_mul_left hk)
  · have hnot : ¬ ((p : ℤ) ∣ l - 1 ∧ (p : ℤ) ∣ l + 1) := by
      rintro ⟨h1, h1'⟩
      have h2' : (p : ℤ) ∣ 2 := by
        have := dvd_sub h1' h1
        simpa using this
      have : p ∣ 2 := by exact_mod_cast h2'
      exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    by_cases h1 : (p : ℤ) ∣ l - 1
    · have hc : IsCoprime ((p : ℤ) ^ k) (l - 1 + 2) := by
        apply IsCoprime.pow_left
        rw [Prime.coprime_iff_not_dvd hpZ]
        intro h3
        exact hnot ⟨h1, by convert h3 using 1; ring⟩
      have hc' : IsCoprime ((p : ℤ) ^ k) (l + 1) := by convert hc using 1; ring
      left
      exact hc'.dvd_of_dvd_mul_right hpk
    · have hc : IsCoprime ((p : ℤ) ^ k) (l - 1) :=
        IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hpZ).2 h1)
      right
      exact hc.dvd_of_dvd_mul_left hpk

/-- A matrix scalar modulo `2pᵏ` is `±1` modulo `pᵏ`: the image of `Γ_sc(2pᵏ)` in `PSL₂(ℝ)` lies in the image of every
`Γ ⊇ Γ(pᵏ)`. -/
theorem barGammaSc_le_of_Gamma_le {p k : ℕ} (hp : p.Prime) {Γ : Subgroup SL(2, ℤ)} (hΓ : Gamma (p ^ k) ≤ Γ) :
    barGamma (GammaSc (2 * p ^ k)) ≤ barGamma Γ := by
  rintro _ ⟨γ, hγ, rfl⟩
  obtain ⟨r, hr2, hr⟩ := mem_GammaSc_iff.1 hγ
  have e00 := congrFun (congrFun hr 0) 0
  have e01 := congrFun (congrFun hr 0) 1
  have e10 := congrFun (congrFun hr 1) 0
  have e11 := congrFun (congrFun hr 1) 1
  simp only [scalar_apply, diagonal_apply_eq, ne_eq, zero_ne_one, not_false_eq_true, diagonal_apply_ne,
    one_ne_zero, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, map_apply, eq_intCast] at e00 e01 e10 e11
  set M := 2 * p ^ k
  have hdvd : ∀ a : ℤ, ((a : ZMod M) = 0) → ((p : ℤ) ^ k) ∣ a := fun a ha ↦ by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd a M).1 ha
    exact dvd_trans (Dvd.intro_left 2 (by simp [M])) this
  have hl : ((γ 0 0 : ℤ) : ZMod M) ^ 2 - 1 = 0 := by rw [← e00, hr2, sub_self]
  have hl' : (2 * (p : ℤ) ^ k) ∣ (γ 0 0) ^ 2 - 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((γ 0 0) ^ 2 - 1) M).1 (by push_cast; exact hl)
    simpa [M] using this
  have hb := hdvd _ e01.symm
  have hc := hdvd _ e10.symm
  have hd : ((p : ℤ) ^ k) ∣ γ 1 1 - γ 0 0 := hdvd _ (by push_cast; rw [← e00, ← e11, sub_self])
  have hcast : ∀ a : ℤ, ((p : ℤ) ^ k) ∣ a → ((a : ZMod (p ^ k)) = 0) := fun a ha ↦
    (ZMod.intCast_zmod_eq_zero_iff_dvd a (p ^ k)).2 (by exact_mod_cast ha)
  rcases dvd_sub_one_or_dvd_add_one hp hl' with h | h
  · refine ⟨γ, hΓ ?_, rfl⟩
    have h11 : ((p : ℤ) ^ k) ∣ γ 1 1 - 1 := by
      have := dvd_add hd h; convert this using 1; ring
    rw [Gamma_mem]
    refine ⟨?_, hcast _ hb, hcast _ hc, ?_⟩
    · have := hcast _ h; push_cast at this; exact sub_eq_zero.1 this
    · have := hcast _ h11; push_cast at this; exact sub_eq_zero.1 this
  · refine ⟨-γ, hΓ ?_, sl2zToPSL2R_neg γ⟩
    have h11 : ((p : ℤ) ^ k) ∣ γ 1 1 + 1 := by
      have := dvd_add hd h; convert this using 1; ring
    rw [Gamma_mem]
    simp only [SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
    refine ⟨?_, by rw [hcast _ hb, neg_zero], by rw [hcast _ hc, neg_zero], ?_⟩
    · have := hcast _ h; push_cast at this; linear_combination -this
    · have := hcast _ h11; push_cast at this; linear_combination -this

theorem Gamma_le_Gamma1 (N : ℕ) : Gamma N ≤ Gamma1 N := by
  intro γ hγ
  rw [Gamma_mem] at hγ
  rw [Gamma1_mem]
  exact ⟨hγ.1, hγ.2.2.2, hγ.2.2.1⟩

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {p k : ℕ} (hp : p.Prime) (hΓ : Gamma (p ^ k) ≤ Γ)
include hp hΓ

/-- **Milne, Theorem 1.20 (Riemann–Roch) on `X(Γ)` for every `Γ ⊇ Γ(pᵏ)`**, `p` prime. -/
@[kb "milne2017mf" "Theorem 1.20 (Riemann-Roch), pdf p. 21, for X(Gamma), Gamma containing Gamma(p^k)"]
theorem riemannRoch_of_Gamma_primePow_le : RiemannRochStatement (ModularCurveX Γ) :=
  haveI : NeZero (2 * p ^ k) := ⟨by have := hp.pos; positivity⟩
  riemannRoch_of_GammaSc_le (2 * p ^ k) (barGammaSc_le_of_Gamma_le hp hΓ)

/-- **Milne, Theorem 4.9 (the dimension formula) for every `Γ ⊇ Γ(pᵏ)`**, unconditional. -/
@[kb "milne2017mf" "Section 4, Theorem 4.9 (pdf p. 51), for Gamma containing Gamma(p^k)"]
theorem dimensionFormula_of_Gamma_primePow_le : DimensionFormula Γ :=
  Wave10.dimensionFormula_of_riemannRoch' Γ (riemannRoch_of_Gamma_primePow_le hp hΓ)

/-- **Milne, Proposition 4.12 (the valence formula) for every `Γ ⊇ Γ(pᵏ)`**, unconditional. -/
@[kb "milne2017mf" "Section 4, Proposition 4.12 (pdf p. 53), for Gamma containing Gamma(p^k)"]
theorem valenceFormula_of_Gamma_primePow_le : ValenceFormula Γ :=
  Wave10.valenceFormula_of_riemannRoch Γ (riemannRoch_of_Gamma_primePow_le hp hΓ)

/-- **Milne, Theorem 1.27 (Riemann–Hurwitz) for maps `X(Γ) → ℙ¹`, `Γ ⊇ Γ(pᵏ)`**, unconditional. -/
@[kb "milne2017mf" "Theorem 1.27 (Riemann-Hurwitz), pdf p. 22, for X(Gamma) -> P^1, Gamma containing Gamma(p^k)"]
theorem riemannHurwitz_of_Gamma_primePow_le : RiemannHurwitzStatement (ModularCurveX Γ) (OnePoint ℂ) :=
  Wave10.riemannHurwitz_modularCurveX Γ (riemannRoch_of_Gamma_primePow_le hp hΓ)

/-- **Milne, Theorem 2.22 (the genus formula) for `X(Γ)`, `Γ ⊇ Γ(pᵏ)`**, unconditional: the analytic genus is
`1 + m/12 - ν₂/4 - ν₃/3 - ν∞/2`. -/
@[kb "milne2017mf" "Theorem 2.22, pdf p. 37, for Gamma containing Gamma(p^k)"]
theorem genus_of_Gamma_primePow_le :
    (genus (ModularCurveX Γ) : ℚ) =
      1 + (genusIndex Γ : ℚ) / 12 - (nuTwo Γ : ℚ) / 4 - (nuThree Γ : ℚ) / 3 - (nuInfty Γ : ℚ) / 2 :=
  Wave10.genus_modularCurveX_of_riemannRoch Γ (riemannRoch_of_Gamma_primePow_le hp hΓ)

omit [Γ.FiniteIndex] hΓ in
/-- **Theorem 1.20 on `X(pᵏ)`.** -/
@[kb "milne2017mf" "Theorem 1.20 (Riemann-Roch), pdf p. 21, for X(p^k)"]
theorem riemannRoch_Gamma_primePow : RiemannRochStatement (ModularCurveX (Gamma (p ^ k))) :=
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  riemannRoch_of_Gamma_primePow_le hp le_rfl

omit [Γ.FiniteIndex] hΓ in
/-- **Theorem 1.20 on `X₁(pᵏ)`.** -/
@[kb "milne2017mf" "Theorem 1.20 (Riemann-Roch), pdf p. 21, for X_1(p^k)"]
theorem riemannRoch_Gamma1_primePow : RiemannRochStatement (ModularCurveX (Gamma1 (p ^ k))) :=
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  riemannRoch_of_Gamma_primePow_le hp (Gamma_le_Gamma1 _)

end ModularFormsKB.Milne.Wave12
