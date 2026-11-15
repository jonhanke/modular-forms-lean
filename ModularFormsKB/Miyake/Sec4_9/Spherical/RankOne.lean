import ModularFormsKB.Miyake.Sec4_9.Spherical.Odd

/-!
# Rank-one lattices `x ℤ ⊆ ℝ`

Helper file for Miyake's Corollary 4.9.7: the lattice `x ℤ`
(`x ≠ 0`) as the span of a basis (so that it carries Mathlib's lattice instances), its covolume
`|x|`, its dual `x⁻¹ ℤ`, and, for the lattice `√(2t) r ℤ` of the twisted theta series, evenness,
the level (dividing `4 t r²`) and the signed discriminant of its sum with `√2 ℤ`.
-/

open Complex Module
open scoped Real RealInnerProductSpace Pointwise

set_option linter.unusedSectionVars false

namespace ModularFormsKB.Miyake.Sec4_9

/-- The basis `(x)` of `ℝ`, `x ≠ 0`. -/
noncomputable def rankOneBasis {x : ℝ} (hx : x ≠ 0) : Module.Basis (Fin 1) ℝ ℝ :=
  (Module.Basis.singleton (Fin 1) ℝ).unitsSMul fun _ ↦ Units.mk0 x hx

/-- The lattice `x ℤ ⊆ ℝ`. -/
noncomputable abbrev rankOneLattice {x : ℝ} (hx : x ≠ 0) : Submodule ℤ ℝ :=
  Submodule.span ℤ (Set.range (rankOneBasis hx))

theorem rankOneLattice_eq {x : ℝ} (hx : x ≠ 0) : rankOneLattice hx = Submodule.span ℤ {x} := by
  rw [rankOneLattice, Set.range_unique]
  congr 2
  simp [rankOneBasis, Module.Basis.unitsSMul_apply]

theorem mem_rankOneLattice {x : ℝ} (hx : x ≠ 0) {y : ℝ} :
    y ∈ rankOneLattice hx ↔ ∃ m : ℤ, m * x = y := by
  rw [rankOneLattice_eq, Submodule.mem_span_singleton]
  simp [zsmul_eq_mul]

theorem mem_dual_rankOneLattice {x : ℝ} (hx : x ≠ 0) {y : ℝ} :
    y ∈ ZLattice.dual (rankOneLattice hx) ↔ ∃ m : ℤ, y * x = m := by
  rw [rankOneLattice_eq, ZLattice.dual_span_singleton hx, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, by rw [zsmul_eq_mul, mul_assoc, inv_mul_cancel₀ hx, mul_one]⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [zsmul_eq_mul, ← hm]; field_simp⟩

/-- The covolume of `x ℤ` is `|x|`. -/
theorem covolume_rankOneLattice {x : ℝ} (hx : x ≠ 0) :
    ZLattice.covolume (rankOneLattice hx) = |x| := by
  have h1 : rankOneLattice hx = x • rankOneLattice one_ne_zero := by
    rw [rankOneLattice_eq, rankOneLattice_eq, Submodule.smul_span, Set.smul_set_singleton,
      smul_eq_mul, mul_one]
  have h := ZLattice.covolume_smul (L := rankOneLattice one_ne_zero) (c := x)
  rw [Module.finrank_self, pow_one, rankOneLattice_eq] at h
  simp only [ZLattice.isUnimodular_span_one.covolume_eq_one, mul_one] at h
  rw [← h]
  congr 1
  rw [h1, rankOneLattice_eq]

/-! ### The lattice `√(2t) r ℤ` -/

/-- The generator `√(2t) r` of the lattice of the twisted theta series. -/
noncomputable def twistGen (t r : ℕ) : ℝ := √(2 * t) * r

theorem twistGen_pos {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r) : 0 < twistGen t r := by
  unfold twistGen
  have : (0 : ℝ) < 2 * t := by positivity
  positivity

theorem twistGen_ne_zero {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r) : twistGen t r ≠ 0 :=
  (twistGen_pos ht hr).ne'

theorem twistGen_sq (t r : ℕ) : twistGen t r ^ 2 = 2 * t * r ^ 2 := by
  unfold twistGen
  rw [mul_pow, Real.sq_sqrt (by positivity)]

/-- The lattice `√(2t) r ℤ`. -/
noncomputable abbrev twistLattice {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r) : Submodule ℤ ℝ :=
  rankOneLattice (twistGen_ne_zero ht hr)

theorem isEven_twistLattice {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r) :
    ZLattice.IsEven (twistLattice ht hr) := by
  rw [twistLattice, rankOneLattice_eq]
  exact ZLattice.isEven_span_singleton_iff.mpr ⟨t * r ^ 2, by
    rw [Real.norm_eq_abs, sq_abs, twistGen_sq]; push_cast; ring⟩

/-- The coset vector `√(2t) a`; it lies in the dual of `√(2t) r ℤ`. -/
noncomputable def twistVec (t : ℕ) (a : ℤ) : ℝ := √(2 * t) * a

theorem twistVec_mem_dual {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r) (a : ℤ) :
    twistVec t a ∈ ZLattice.dual (twistLattice ht hr) := by
  rw [mem_dual_rankOneLattice]
  refine ⟨2 * t * a * r, ?_⟩
  unfold twistVec twistGen
  rw [show √(2 * (t : ℝ)) * a * (√(2 * t) * r) = (√(2 * t)) ^ 2 * a * r by ring,
    Real.sq_sqrt (by positivity)]
  push_cast; ring

theorem norm_twistVec_sq (t : ℕ) (a : ℤ) : ‖twistVec t a‖ ^ 2 = 2 * t * a ^ 2 := by
  rw [Real.norm_eq_abs, sq_abs, twistVec, mul_pow, Real.sq_sqrt (by positivity)]

/-- The level of `√(2t) r ℤ` divides `4 t r²`. -/
theorem level_twistLattice_dvd {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r) :
    ZLattice.level (twistLattice ht hr) ∣ 4 * t * r ^ 2 := by
  refine ZLattice.level_dvd_iff.mpr fun y hy ↦ ?_
  obtain ⟨m, hm⟩ := (mem_dual_rankOneLattice _).mp hy
  have hx := twistGen_ne_zero ht hr
  have hy' : y = m / twistGen t r := by rw [← hm]; field_simp
  refine ⟨m ^ 2, ?_⟩
  rw [hy', Real.norm_eq_abs, sq_abs, div_pow, twistGen_sq]
  push_cast
  field_simp
  ring

/-- The doubled lattice `√(2t) r ℤ ⊕ √2 ℤ`. -/
noncomputable abbrev twistLattice₂ {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r) :
    Submodule ℤ (WithLp 2 (ℝ × ℝ)) :=
  ZLattice.orthSum (twistLattice ht hr) sqrtTwoLattice

theorem level_twistLattice₂_dvd {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r) :
    ZLattice.level (twistLattice₂ ht hr) ∣ 4 * t * r ^ 2 := by
  rw [ZLattice.level_orthSum, level_sqrtTwoLattice]
  exact Nat.lcm_dvd (level_twistLattice_dvd ht hr) ⟨t * r ^ 2, by ring⟩

theorem four_dvd_level_twistLattice₂ {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r) :
    4 ∣ ZLattice.level (twistLattice₂ ht hr) := four_dvd_level_orthSum

theorem finrank_twist₂ : finrank ℝ (WithLp 2 (ℝ × ℝ)) = 2 * 1 := by
  rw [finrank_withLp_prod_real, Module.finrank_self]

/-- The signed discriminant of `√(2t) r ℤ ⊕ √2 ℤ` is `-4 t r²`. -/
theorem signedDiscr_twistLattice₂ {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r) :
    ZLattice.signedDiscr (twistLattice₂ ht hr) = -(4 * t * r ^ 2 : ℤ) := by
  have hL := isEven_orthSum_sqrtTwo (isEven_twistLattice ht hr)
  rw [ZLattice.signedDiscr_of_finrank_eq _ finrank_twist₂]
  have hcard : (Nat.card (ZLattice.DiscriminantGroup (twistLattice₂ ht hr)) : ℝ) =
      4 * t * r ^ 2 := by
    have h2 : sqrtTwoLattice = rankOneLattice (Real.sqrt_ne_zero'.mpr two_pos) := rfl
    rw [← hL.isIntegral.det_eq_card_discriminantGroup, ZLattice.det_def,
      ZLattice.covolume_orthSum, covolume_rankOneLattice, h2, covolume_rankOneLattice, mul_pow,
      sq_abs, sq_abs, twistGen_sq, Real.sq_sqrt zero_le_two]
    ring
  have : (Nat.card (ZLattice.DiscriminantGroup (twistLattice₂ ht hr)) : ℤ) = 4 * t * r ^ 2 := by
    exact_mod_cast hcard
  rw [this]; ring

end ModularFormsKB.Miyake.Sec4_9
