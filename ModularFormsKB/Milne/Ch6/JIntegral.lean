import ModularFormsKB.Milne.Ch6.JRational

/-!
# The $q$-expansion of $j$ has integer coefficients

With $E_4 = 1 + 240A$, $E_6 = 1 - 504B$ ($A = \sum\sigma_3(n)q^n$, $B = \sum\sigma_5(n)q^n$),
$$\Delta = \frac{E_4^3 - E_6^2}{1728} = \frac{5A + 7B}{12} + 100A^2 - 147B^2 + 8000A^3,$$
and $12 \mid 5d^3 + 7d^5$ for every $d$, so $\Delta$ has integer coefficients; $\Delta = q + O(q^2)$, so
$\Delta/q$ is a unit of $\mathbb Z[[q]]$ and $qj = E_4^3 \cdot (\Delta/q)^{-1}$ has integer coefficients. Used for the
integrality of the modular polynomial (Milne, Section 6, proof of Theorem 6.1, pdf p. 88).
-/

open UpperHalfPlane ModularForm EisensteinSeries Filter Topology
open scoped ArithmeticFunction.sigma MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.JCoefficients

open TauCeti.ModularForm

local notation "𝕢" => Function.Periodic.qParam

/-- Power series over `ℂ` all of whose coefficients are integers: the range of `ℤ⟦X⟧ → ℂ⟦X⟧`. -/
theorem mem_range_int_iff (f : PowerSeries ℂ) :
    f ∈ (PowerSeries.map (Int.castRingHom ℂ)).range ↔ ∀ n, ∃ r : ℤ, (r : ℂ) = f.coeff n := by
  constructor
  · rintro ⟨g, rfl⟩ n
    exact ⟨g.coeff n, by simp⟩
  · intro h
    choose g hg using h
    exact ⟨PowerSeries.mk g, by ext n; simp [hg]⟩

private theorem bernoulli_four' : bernoulli 4 = -1 / 30 := by decide +kernel
private theorem bernoulli_six' : bernoulli 6 = 1 / 42 := by decide +kernel

private theorem twelve_dvd (d : ℕ) : (12 : ℤ) ∣ 5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5 := by
  have h : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
  have := h (d : ZMod 12)
  have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) 12).1 (by
    push_cast; exact this)
  exact_mod_cast h2

private theorem twelve_dvd_sum (n : ℕ) : (12 : ℤ) ∣ 5 * ((σ 3 n : ℕ) : ℤ) + 7 * ((σ 5 n : ℕ) : ℤ) := by
  simp only [ArithmeticFunction.sigma_apply, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.dvd_sum fun d _ => by push_cast; exact twelve_dvd d

/-- `A = ∑ σ₃(n) qⁿ` over `ℤ`. -/
private def serA : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 0 else ((σ 3 n : ℕ) : ℤ)
private def serB : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 0 else ((σ 5 n : ℕ) : ℤ)
private def serC : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (5 * ((σ 3 n : ℕ) : ℤ) + 7 * ((σ 5 n : ℕ) : ℤ)) / 12

private theorem serC_spec : 12 * serC = 5 * serA + 7 * serB := by
  ext n
  have : (12 : PowerSeries ℤ) = PowerSeries.C 12 := by simp
  have h5 : (5 : PowerSeries ℤ) = PowerSeries.C 5 := by simp
  have h7 : (7 : PowerSeries ℤ) = PowerSeries.C 7 := by simp
  rw [this, h5, h7]
  simp only [serC, serA, serB, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · exact Int.mul_ediv_cancel' (twelve_dvd_sum n)

private theorem E₄_eq : qExpansion 1 E₄ = PowerSeries.map (Int.castRingHom ℂ) (1 + PowerSeries.C 240 * serA) := by
  ext n
  have := E_qExpansion_coeff (k := 4) (by norm_num) ⟨2, rfl⟩ n
  change (qExpansion 1 (E (k := 4) (by norm_num))).coeff n = _
  rw [this]
  simp only [PowerSeries.coeff_map, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_one,
    serA, PowerSeries.coeff_mk]
  by_cases h : n = 0
  · subst h; simp
  · simp [h, bernoulli_four']
    norm_num

private theorem E₆_eq : qExpansion 1 E₆ = PowerSeries.map (Int.castRingHom ℂ) (1 - PowerSeries.C 504 * serB) := by
  ext n
  have := E_qExpansion_coeff (k := 6) (by norm_num) ⟨3, rfl⟩ n
  change (qExpansion 1 (E (k := 6) (by norm_num))).coeff n = _
  rw [this]
  simp only [PowerSeries.coeff_map, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_one,
    serB, PowerSeries.coeff_mk]
  by_cases h : n = 0
  · subst h; simp
  · simp [h, bernoulli_six']
    norm_num

private def serD : PowerSeries ℤ := serC + 100 * serA ^ 2 - 147 * serB ^ 2 + 8000 * serA ^ 3

private theorem serD_spec :
    1728 * serD = (1 + 240 * serA) ^ 3 - (1 - 504 * serB) ^ 2 := by
  unfold serD
  linear_combination 144 * serC_spec

private theorem discriminant_eq_map :
    qExpansion 1 discriminant = PowerSeries.map (Int.castRingHom ℂ) serD := by
  have h240 : (PowerSeries.C 240 : PowerSeries ℤ) = 240 := by simp
  have h504 : (PowerSeries.C 504 : PowerSeries ℤ) = 504 := by simp
  rw [qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq, E₄_eq, E₆_eq, h240, h504]
  have h : ((1728 : ℂ)⁻¹ : ℂ) • (PowerSeries.map (Int.castRingHom ℂ) (1 + 240 * serA) ^ 3 -
      PowerSeries.map (Int.castRingHom ℂ) (1 - 504 * serB) ^ 2) =
      PowerSeries.C ((1728 : ℂ)⁻¹) * PowerSeries.map (Int.castRingHom ℂ)
        ((1 + 240 * serA) ^ 3 - (1 - 504 * serB) ^ 2) := by
    simp [PowerSeries.smul_eq_C_mul]
  rw [h, ← serD_spec, map_mul]
  have : PowerSeries.map (Int.castRingHom ℂ) (1728 : PowerSeries ℤ) = PowerSeries.C (1728 : ℂ) := by
    have : (1728 : PowerSeries ℤ) = PowerSeries.C 1728 := by simp
    rw [this, PowerSeries.map_C]; simp
  rw [this, ← mul_assoc, ← map_mul]
  simp

/-- **The coefficients of $qj$ are integers.** -/
theorem j_coeff_isInt (n : ℕ) :
    ∃ r : ℤ, (r : ℂ) = (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)).coeff n := by
  refine (mem_range_int_iff _).1 ?_ n
  obtain ⟨D, hD⟩ : PowerSeries.X ∣ qExpansion 1 discriminant :=
    PowerSeries.X_dvd_iff.2 (by simpa using discriminant_qExpansion_coeff_zero)
  have hDc : ∀ m, D.coeff m = (qExpansion 1 discriminant).coeff (m + 1) := fun m => by
    rw [hD, PowerSeries.coeff_succ_X_mul]
  have hD0 : PowerSeries.constantCoeff D = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hDc]
    simpa using discriminant_qExpansion_coeff_one
  obtain ⟨g, hg⟩ := (mem_range_int_iff D).2 fun m => by
    refine ⟨serD.coeff (m + 1), ?_⟩
    rw [hDc, discriminant_eq_map]; simp
  obtain ⟨h, hh⟩ : (qExpansion 1 E₄ ^ 3) ∈ (PowerSeries.map (Int.castRingHom ℂ)).range := by
    rw [E₄_eq]; exact ⟨(1 + PowerSeries.C 240 * serA) ^ 3, by simp⟩
  have hg0 : PowerSeries.constantCoeff g = 1 := by
    have : ((PowerSeries.constantCoeff g : ℤ) : ℂ) = 1 := by
      rw [← hD0, ← hg]; rfl
    exact_mod_cast this
  have hu : IsUnit g := (PowerSeries.isUnit_iff_constantCoeff).2 (by rw [hg0]; exact isUnit_one)
  obtain ⟨u, hu⟩ := hu
  have hmul : qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ) * D = qExpansion 1 E₄ ^ 3 := by
    have := qExpansion_qParam_mul_j_mul_qExpansion_discriminant
    rw [hD] at this
    refine mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ℂ)) ?_
    rw [← this]; ring
  have key : qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ) =
      PowerSeries.map (Int.castRingHom ℂ) (h * ↑u⁻¹) := by
    have hinv : g * ↑u⁻¹ = 1 := by rw [← hu]; exact u.mul_inv
    calc qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)
        = qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ) * (D * PowerSeries.map (Int.castRingHom ℂ) ↑u⁻¹) := by
          rw [← hg, ← map_mul, hinv]; simp
      _ = _ := by
          rw [← mul_assoc, hmul, ← hh, map_mul]
  rw [key]
  exact ⟨_, rfl⟩

end ModularFormsKB.Milne.JCoefficients
