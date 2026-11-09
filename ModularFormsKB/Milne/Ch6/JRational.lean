import ModularFormsKB.Milne.Ch6.JCoefficients

/-!
# The $q$-expansion of $j$ has rational coefficients

All $q$-expansion coefficients of $qj = qE_4^3/\Delta$ are rational: those of $E_4$ and $E_6$ are $240\sigma_3(n)$ and
$-504\sigma_5(n)$ (Mathlib's `EisensteinSeries.E_qExpansion_coeff`), $\Delta = (E_4^3 - E_6^2)/1728$
(`TauCeti.ModularForm.qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq`) has $\Delta_0 = 0$, $\Delta_1 = 1$, and
$qj \cdot \Delta = qE_4^3$ (`TauCeti.ModularForm.qExpansion_qParam_mul_j_mul_qExpansion_discriminant`) determines the
coefficients of $qj$ recursively. Used for the rationality of the modular polynomial (Milne, Section 6, proof of
Theorem 6.1, pdf p. 88).
-/

open UpperHalfPlane ModularForm EisensteinSeries Filter Topology
open scoped ArithmeticFunction.sigma MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.JCoefficients

open TauCeti.ModularForm

local notation "𝕢" => Function.Periodic.qParam

/-- Power series over `ℂ` all of whose coefficients are rational: the range of `ℚ⟦X⟧ → ℂ⟦X⟧`. -/
theorem mem_range_iff (f : PowerSeries ℂ) :
    f ∈ (PowerSeries.map (Rat.castHom ℂ)).range ↔ ∀ n, ∃ r : ℚ, (r : ℂ) = f.coeff n := by
  constructor
  · rintro ⟨g, rfl⟩ n
    exact ⟨g.coeff n, by simp⟩
  · intro h
    choose g hg using h
    exact ⟨PowerSeries.mk g, by ext n; simp [hg]⟩

private theorem eis_coeff_isRat {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (n : ℕ) :
    ∃ r : ℚ, (r : ℂ) = (qExpansion 1 (E hk)).coeff n := by
  rw [E_qExpansion_coeff hk hk2]
  by_cases h : n = 0
  · exact ⟨1, by simp [h]⟩
  · exact ⟨-(2 * k / bernoulli k) * (σ (k - 1) n : ℕ), by simp [h]⟩

theorem E₄_coeff_isRat (n : ℕ) : ∃ r : ℚ, (r : ℂ) = (qExpansion 1 E₄).coeff n :=
  eis_coeff_isRat (by norm_num) ⟨2, rfl⟩ n

theorem E₆_coeff_isRat (n : ℕ) : ∃ r : ℚ, (r : ℂ) = (qExpansion 1 E₆).coeff n :=
  eis_coeff_isRat (by norm_num) ⟨3, rfl⟩ n

theorem E₄_mem : qExpansion 1 E₄ ∈ (PowerSeries.map (Rat.castHom ℂ)).range :=
  (mem_range_iff _).2 E₄_coeff_isRat

theorem E₆_mem : qExpansion 1 E₆ ∈ (PowerSeries.map (Rat.castHom ℂ)).range :=
  (mem_range_iff _).2 E₆_coeff_isRat

theorem discriminant_mem :
    qExpansion 1 discriminant ∈ (PowerSeries.map (Rat.castHom ℂ)).range := by
  rw [qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq]
  have h : ((1728 : ℂ)⁻¹ : ℂ) • (qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2) =
      PowerSeries.C ((1728 : ℂ)⁻¹) * (qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2) := by
    simp [PowerSeries.smul_eq_C_mul]
  rw [h]
  refine Subring.mul_mem _ ?_ (Subring.sub_mem _ (Subring.pow_mem _ E₄_mem _)
    (Subring.pow_mem _ E₆_mem _))
  exact ⟨PowerSeries.C ((1728 : ℚ)⁻¹), by simp⟩

theorem discriminant_coeff_isRat (n : ℕ) : ∃ r : ℚ, (r : ℂ) = (qExpansion 1 discriminant).coeff n :=
  (mem_range_iff _).1 discriminant_mem n

/-- **The coefficients of $qj$ are rational.** -/
theorem j_coeff_isRat (n : ℕ) : ∃ r : ℚ, (r : ℂ) = (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)).coeff n := by
  refine (mem_range_iff _).1 ?_ n
  obtain ⟨D, hD⟩ : PowerSeries.X ∣ qExpansion 1 discriminant :=
    PowerSeries.X_dvd_iff.2 (by simpa using discriminant_qExpansion_coeff_zero)
  have hDc : ∀ m, D.coeff m = (qExpansion 1 discriminant).coeff (m + 1) := fun m => by
    rw [hD, PowerSeries.coeff_succ_X_mul]
  have hD0 : PowerSeries.constantCoeff D = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hDc]
    simpa using discriminant_qExpansion_coeff_one
  obtain ⟨g, hg⟩ := (mem_range_iff D).2 fun m => by
    obtain ⟨r, hr⟩ := discriminant_coeff_isRat (m + 1)
    exact ⟨r, by rw [hDc, hr]⟩
  obtain ⟨h, hh⟩ : (qExpansion 1 E₄ ^ 3) ∈ (PowerSeries.map (Rat.castHom ℂ)).range :=
    Subring.pow_mem _ E₄_mem _
  have hg0 : PowerSeries.constantCoeff g ≠ 0 := by
    intro h0
    have : ((PowerSeries.constantCoeff g : ℚ) : ℂ) = 1 := by
      rw [← hD0, ← hg]; rfl
    simp [h0] at this
  have hmul : qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ) * D = qExpansion 1 E₄ ^ 3 := by
    have := qExpansion_qParam_mul_j_mul_qExpansion_discriminant
    rw [hD] at this
    refine mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ℂ)) ?_
    rw [← this]; ring
  have key : qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ) =
      PowerSeries.map (Rat.castHom ℂ) (h * g⁻¹) := by
    have hinv : g * g⁻¹ = 1 := PowerSeries.mul_inv_cancel g hg0
    calc qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)
        = qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ) * (D * PowerSeries.map (Rat.castHom ℂ) g⁻¹) := by
          rw [← hg, ← map_mul, hinv]; simp
      _ = _ := by
          rw [← mul_assoc, hmul, ← hh, map_mul]
  rw [key]
  exact ⟨_, rfl⟩

end ModularFormsKB.Milne.JCoefficients
