import ModularFormsKB.Miyake.Sec4_9.Spherical.RankOne
import ModularFormsKB.HalfIntegral.Abstract.ShimuraRankin

/-!
# The twisted theta series as a combination of coset theta series (Miyake, Corollary 4.9.7)

For a Dirichlet character `ψ` modulo `r ≥ 1` of parity `ν`
(`HalfIntegral.charParity`) and `t ≥ 1`, Shimura's twisted theta series is
`θ_{ψ,t}(z) = ∑_{n ∈ ℤ} ψ̄(n) n^ν e(t n² z)` (`HalfIntegral.thetaTwist`). Splitting `n` by its
class `a` modulo `r` and writing `√(2t) n = √(2t) a + m √(2t) r`,

`θ_{ψ,t} = (√(2t))^{-ν} ∑_{a=0}^{r-1} ψ̄(a) θ_{√(2t)a + √(2t)rℤ}(·; x^ν)`

(`thetaTwist_eq_sum`), a combination of coset theta series of the even rank-one lattice
`√(2t) r ℤ` with the spherical weight `x ↦ x^ν` (`ν ≤ 1`, no isotropy needed).
-/

open Complex Module
open scoped Real RealInnerProductSpace UpperHalfPlane

set_option linter.unusedSectionVars false

namespace ModularFormsKB.Miyake.Sec4_9

open HalfIntegral

theorem charParity_le_one {r : ℕ} (ψ : DirichletCharacter ℂ r) : charParity ψ ≤ 1 := by
  unfold charParity; split_ifs <;> omega

theorem isSphericalDatum_one_zero {r : ℕ} (ψ : DirichletCharacter ℂ r) :
    IsSphericalDatum (charParity ψ) (1 : ℝ) 0 := Or.inl (charParity_le_one ψ)

theorem isoForm_one_zero (x : ℝ) : isoForm (1 : ℝ) 0 x = x := by
  simp [isoForm]

/-- The lattice combination `∑_{a < r} ψ̄(a) θ_{√(2t)a + √(2t)rℤ}(·; x^ν)`. -/
noncomputable def thetaLat {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r)
    (τ : ℍ) : ℂ :=
  ∑ a ∈ Finset.range r, ψ⁻¹ (a : ZMod r) *
    thetaSph (twistLattice ht hr) (charParity ψ) 1 0 (twistVec t a) τ

/-- The coset theta series over `√(2t) a + √(2t) r ℤ` as a series over `m ∈ ℤ`. -/
theorem hasSum_thetaSph_twist {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r) (ν : ℕ) (a : ℤ) (τ : ℍ) :
    HasSum (fun m : ℤ ↦ ((√(2 * t) : ℝ) : ℂ) ^ ν * (((a + r * m : ℤ) : ℂ) ^ ν *
        cexp (2 * π * I * t * ((a + r * m : ℤ) : ℂ) ^ 2 * τ)))
      (thetaSph (twistLattice ht hr) ν 1 0 (twistVec t a) τ) := by
  have hx := twistGen_ne_zero ht hr
  have hs : HasSum (fun v : twistLattice ht hr ↦ isoForm 1 0 (twistVec t a + v) ^ ν *
      cexp (π * I * (‖twistVec t a + (v : ℝ)‖ ^ 2 : ℝ) * τ))
      (thetaSph (twistLattice ht hr) ν 1 0 (twistVec t a) τ) :=
    (summable_thetaW (twistLattice ht hr) (polyBounded_isoForm_pow 1 0 ν) (twistVec t a) τ).hasSum
  set he : ℤ ≃ twistLattice ht hr :=
    (LinearEquiv.toSpanNonzeroSingleton ℤ ℝ (twistGen t r) hx).toEquiv.trans
      (LinearEquiv.ofEq _ _ (rankOneLattice_eq hx).symm).toEquiv with hhe
  have hev (m : ℤ) : ((he m : twistLattice ht hr) : ℝ) = m * twistGen t r := by
    simp [hhe, zsmul_eq_mul]
  rw [← he.hasSum_iff] at hs
  convert hs using 1
  funext m
  simp only [Function.comp_apply, hev, isoForm_one_zero]
  have hv : twistVec t a + m * twistGen t r = √(2 * t) * ((a + r * m : ℤ) : ℝ) := by
    unfold twistVec twistGen; push_cast; ring
  rw [hv, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (by positivity)]
  push_cast
  simp only [mul_pow]
  ring_nf

/-- **The twisted theta series as a lattice combination.** -/
theorem thetaTwist_eq_sum {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r)
    (τ : ℍ) : thetaTwist ψ t τ = (((√(2 * t) : ℝ) : ℂ) ^ charParity ψ)⁻¹ * thetaLat ψ ht hr τ := by
  have : NeZero r := ⟨by omega⟩
  set ν := charParity ψ
  set c : ℂ := ((√(2 * t) : ℝ) : ℂ) ^ ν
  have hc : c ≠ 0 := pow_ne_zero _ (ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity)))
  set term : ℤ → ℂ := fun n ↦ ψ⁻¹ (n : ZMod r) * (n : ℂ) ^ ν * cexp (2 * π * I * t * (n : ℂ) ^ 2 * τ)
  -- the pieces of the residue classes
  set h : ℕ → ℤ → ℂ := fun a n ↦ if (n : ZMod r) = (a : ZMod r) then term n else 0
  have hpiece (a : ℕ) : HasSum (h a) (c⁻¹ * (ψ⁻¹ (a : ZMod r) *
      thetaSph (twistLattice ht hr) ν 1 0 (twistVec t a) τ)) := by
    have hinj : Function.Injective fun m : ℤ ↦ (a : ℤ) + r * m := fun m₁ m₂ hm ↦ by
      have : (r : ℤ) * m₁ = r * m₂ := by linarith
      exact mul_left_cancel₀ (by exact_mod_cast (show r ≠ 0 by omega)) this
    rw [← hinj.hasSum_iff]
    · have h1 := (hasSum_thetaSph_twist ht hr ν a τ).mul_left (c⁻¹ * ψ⁻¹ (a : ZMod r))
      convert h1 using 1
      · funext m
        simp only [Function.comp_apply, h, term]
        have hmod : (((a : ℤ) + r * m : ℤ) : ZMod r) = (a : ZMod r) := by simp
        rw [if_pos hmod, hmod]
        field_simp
        push_cast
        ring
      · ring
    · intro n hn
      simp only [h]
      rw [if_neg]
      intro hna
      apply hn
      have : ((n - a : ℤ) : ZMod r) = 0 := by push_cast; rw [hna]; simp
      obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
      exact ⟨m, by linarith⟩
  have htot := hasSum_sum (s := Finset.range r) fun a _ ↦ hpiece a
  have hsum : (fun n ↦ ∑ a ∈ Finset.range r, h a n) = term := by
    funext n
    rw [Finset.sum_eq_single (n % r).toNat]
    · simp only [h]
      rw [if_pos]
      have : (((n % r).toNat : ℕ) : ℤ) = n % r := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
      rw [show (((n % r).toNat : ℕ) : ZMod r) = (((n % r).toNat : ℕ) : ℤ) by push_cast; rfl, this]
      simp
    · intro b hb hne
      simp only [h]
      rw [if_neg]
      intro hnb
      apply hne
      have hb' : b < r := Finset.mem_range.mp hb
      have h2 : n % r = (b : ℤ) % r := (ZMod.intCast_eq_intCast_iff' n b r).mp (by exact_mod_cast hnb)
      rw [Int.emod_eq_of_lt (a := (b : ℤ)) (by positivity) (by exact_mod_cast hb')] at h2
      rw [h2]
      simp
    · intro h'
      exact absurd (Finset.mem_range.mpr (by
        have := Int.emod_lt_of_pos n (show (0 : ℤ) < r by omega)
        omega)) h'
  rw [hsum] at htot
  rw [thetaTwist, htot.tsum_eq, thetaLat, Finset.mul_sum]

/-! ### The character identity `(-4tr² / d) χ_{-4}(d) = (t / |d|)` -/

theorem chi4_int_sq {n : ℤ} (h : n % 2 = 1) : (ZMod.χ₄ (n : ZMod 4)) ^ 2 = 1 := by
  rw [ZMod.χ₄_int_eq_if_mod_four]
  split_ifs <;> simp_all

theorem chi4_int_neg {n : ℤ} (h : n % 2 = 1) :
    ZMod.χ₄ ((-n : ℤ) : ZMod 4) = -ZMod.χ₄ (n : ZMod 4) := by
  rw [ZMod.χ₄_int_eq_if_mod_four, ZMod.χ₄_int_eq_if_mod_four]
  split_ifs <;> omega

theorem chi4_neg (x : ZMod 4) : ZMod.χ₄ (-x) = -ZMod.χ₄ x := by
  rw [show -x = -1 * x by ring, map_mul, show ZMod.χ₄ (-1) = -1 by decide, neg_one_mul]

theorem kronecker_twist_mul_chi4 {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r) {d : ℤ}
    (hd : IsCoprime d (4 * t * r ^ 2 : ℕ)) :
    (TauCeti.kroneckerSym (-(4 * t * r ^ 2 : ℤ)) d : ℂ) * (ZMod.χ₄ (d : ZMod 4) : ℂ) =
      (jacobiSym t d.natAbs : ℂ) := by
  have h2 : IsCoprime d 2 := hd.of_isCoprime_of_dvd_right (by push_cast; exact ⟨2 * t * r ^ 2, by ring⟩)
  have hodd : Odd d := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    intro h
    have hu := h2.isUnit_of_dvd' h (dvd_refl 2)
    rcases Int.isUnit_iff.mp hu with h | h <;> norm_num at h
  have hd2 : d % 2 = 1 := Int.odd_iff.mp hodd
  set m := d.natAbs with hm
  have hnodd : Odd m := Int.natAbs_odd.mpr hodd
  have hgcd : ((2 * r : ℕ) : ℤ).gcd (m : ℤ) = 1 := by
    have : IsCoprime ((2 * r : ℕ) : ℤ) d :=
      (hd.symm.of_isCoprime_of_dvd_left (by push_cast; exact ⟨2 * t * r, by ring⟩))
    have h := Int.isCoprime_iff_gcd_eq_one.mp this
    rw [Int.gcd, Int.natAbs_natCast]
    rw [Int.gcd] at h
    exact h
  have hJ : jacobiSym (-(4 * t * r ^ 2 : ℤ)) m = ZMod.χ₄ (m : ZMod 4) * jacobiSym t m := by
    rw [show -(4 * t * r ^ 2 : ℤ) = -1 * (((2 * r : ℕ) : ℤ) ^ 2 * t) by push_cast; ring,
      jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.at_neg_one hnodd, jacobiSym.sq_one' hgcd,
      one_mul]
  have hsq : ((ZMod.χ₄ (m : ZMod 4) : ℤ) : ℂ) ^ 2 = 1 := by
    have h := chi4_int_sq (n := (m : ℤ)) (by omega)
    have h' : ZMod.χ₄ (m : ZMod 4) ^ 2 = 1 := by exact_mod_cast h
    exact_mod_cast h'
  have hm0 : m ≠ 0 := by intro h0; rw [hm, Int.natAbs_eq_zero] at h0; subst h0; simp at hd2
  rw [TauCeti.kroneckerSym_of_odd _ hodd, hJ]
  have hmpos : 0 < (d.natAbs : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
  rcases Int.natAbs_eq d with hd' | hd'
  · rw [if_neg (by omega)]
    have : (d : ZMod 4) = (m : ZMod 4) := by
      conv_lhs => rw [hd']
      exact Int.cast_natCast _
    rw [this]
    push_cast
    linear_combination (jacobiSym t m : ℂ) * hsq
  · have htr : (0 : ℤ) < 4 * t * r ^ 2 := by
      have : (0 : ℤ) < t := by exact_mod_cast ht
      have : (0 : ℤ) < r := by exact_mod_cast hr
      positivity
    rw [if_pos ⟨by omega, by omega⟩]
    have : (d : ZMod 4) = -(m : ZMod 4) := by
      conv_lhs => rw [hd']
      rw [Int.cast_neg, Int.cast_natCast]
    rw [this, chi4_neg]
    push_cast
    linear_combination (jacobiSym t m : ℂ) * hsq

end ModularFormsKB.Miyake.Sec4_9
