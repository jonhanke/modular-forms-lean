/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
-/
import ModularFormsKB.HalfIntegral.ZagierKernel.SquareCycle.SquareRep
import ModularFormsKB.HalfIntegral.ZagierKernel.SquareCycle.GaussSum
import ModularFormsKB.HalfIntegral.ZagierKernel.Unfolding
import TauCeti.NumberTheory.ModularForms.LFunction.Period
import TauCeti.NumberTheory.ModularForms.Twist.Basic
import TauCeti.NumberTheory.ModularForms.ModularSymbols.Period.Integral
import TauCeti.NumberTheory.ModularForms.LFunction.Basic
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import ModularFormsKB.HalfIntegral.Abstract.TwistContinuationProof

/-!
# The cycle integrals of discriminant $D^2$ give $L(G, D, k)$ (`KohnenSquareCycle`)

For $D$ fundamental with $(-1)^kD > 0$ and $n = |D|$:
1. (`shintaniCoeff_natAbs_eq_sum`, `ClassSum.lean`) the classes of discriminant $n^2$ are those of $[0, n, c]$, $0 \le c < n$
   (`Classes.lean`), the genus character of the class of $[0,n,c]$ is $\left(\frac Dc\right)$, and the cycle integral is a class
   invariant (`CuspIntegral.lean`), so
   $r_{k,D}(G; n) = \sum_{0\le c<n}\left(\frac Dc\right)\int_{C_{[0,n,c]}}G(z)\,(nz + c)^{k-1}dz$;
2. (`cycleIntegral_squareRep`) the geodesic of $[0, n, c]$ is the vertical line from $-c/n$ to $i\infty$, so
   $\int_{C_{[0,n,c]}} = n^{k-1}i^k\int_0^\infty G(-c/n + it)\,t^{k-1}dt$;
3. (`sum_kroneckerSym_cycleIntegral`) by `KroneckerGaussSum`, $\sum_c\left(\frac Dc\right)G(\tau - c/n) = \operatorname{sgn}(D)\sqrt D\,(G\otimes\chi_D)(\tau)$,
   where $G \otimes \chi_D$ is the twist (Tau Ceti `CuspForm.twist`), and the period
   $\int_0^\infty (G\otimes\chi_D)(it)\,t^{k-1}dt = (k-1)!\,(2\pi)^{-k}L(G, D, k)$ (Tau Ceti
   `cuspIntegral_mul_pow_zero_infty_eq_L`). Since $i^k\operatorname{sgn}(D)\sqrt D = (-1)^{\lfloor k/2\rfloor}\sqrt{|D|}$ when
   $(-1)^kD > 0$, the sum is `squareCycleConst k D * L k`.

**Headline** (`SquareCycle.lean`): `kohnenSquareCycle_of_gaussSum`: `KroneckerGaussSum → KohnenSquareCycle k`.
-/

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups ModularForm CongruenceSubgroup
open scoped Real

open BinQF

local notation "ℍ" => UpperHalfPlane

/-- Change of variables $t = e^s$. -/
theorem integral_Ioi_eq_integral_exp (f : ℝ → ℂ) :
    ∫ t in Set.Ioi (0 : ℝ), f t = ∫ s : ℝ, (Real.exp s : ℂ) * f (Real.exp s) := by
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := (Set.univ : Set ℝ))
    (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn f
  rw [Set.image_univ, Real.range_exp, MeasureTheory.Measure.restrict_univ] at h
  rw [h]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s ↦ ?_)
  simp [abs_of_pos (Real.exp_pos s), Complex.real_smul]

theorem squareRep_geodesic {n : ℕ} (hn : 0 < n) (c : ℤ) (s : ℝ) :
    (BinQF.squareRep n c).geodesic s = -(c : ℂ) / n + I * (Real.exp s : ℝ) := by
  have h1 : SignType.sign ((n : ℤ) : ℝ) = 1 := sign_pos (by exact_mod_cast hn)
  have h2 : SignType.sign (n : ℝ) = 1 := sign_pos (by exact_mod_cast hn)
  simp [BinQF.geodesic, BinQF.squareRep, h2]

theorem squareRep_evalC {n : ℕ} (hn : 0 < n) (c : ℤ) (s : ℝ) :
    (BinQF.squareRep n c).evalC ((BinQF.squareRep n c).geodesic s) = n * I * (Real.exp s : ℝ) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [squareRep_geodesic hn]
  simp [BinQF.evalC, BinQF.squareRep]
  field_simp
  ring

/-- **The cycle integral of $[0, n, c]$**: $\int_{C_{[0,n,c]}}G(z)(nz+c)^{k-1}dz = n^{k-1}i^k\int_0^\infty G(-c/n+it)\,t^{k-1}dt$. -/
theorem cycleIntegral_squareRep {k : ℕ} (hk : 1 ≤ k) (G : ℍ → ℂ) {n : ℕ} (hn : 0 < n) (c : ℤ) :
    cycleIntegral k G (BinQF.squareRep n c) =
      (n : ℂ) ^ (k - 1) * I ^ k *
        ∫ t in Set.Ioi (0 : ℝ), G (UpperHalfPlane.ofComplex (-(c : ℂ) / n + I * t)) * (t : ℂ) ^ (k - 1) := by
  have hd : (BinQF.squareRep n c).disc = (n : ℤ) ^ 2 := BinQF.disc_squareRep n c
  have hpos : 0 < (BinQF.squareRep n c).disc := by rw [hd]; positivity
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsq : √(((BinQF.squareRep n c).disc : ℤ) : ℝ) = n := by
    rw [hd]; push_cast; exact Real.sqrt_sq (by positivity)
  unfold BinQF.cycleIntegral
  rw [dif_pos hpos, if_pos (by rw [hd]; exact ⟨n, sq _⟩), hsq]
  have hint : ∀ s : ℝ, G ((BinQF.squareRep n c).geodesicH hpos s) *
      (BinQF.squareRep n c).evalC ((BinQF.squareRep n c).geodesic s) ^ k =
      ((n : ℂ) ^ k * I ^ k) * ((Real.exp s : ℝ) *
        (G (UpperHalfPlane.ofComplex (-(c : ℂ) / n + I * ((Real.exp s : ℝ) : ℂ))) *
          ((Real.exp s : ℝ) : ℂ) ^ (k - 1))) := by
    intro s
    have him : 0 < (-(c : ℂ) / n + I * ((Real.exp s : ℝ) : ℂ)).im := by
      have := Real.exp_pos s
      simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.div_natCast_im, Complex.neg_im, Complex.intCast_im]
      simpa using this
    have h1 : (BinQF.squareRep n c).geodesicH hpos s =
        UpperHalfPlane.ofComplex (-(c : ℂ) / n + I * ((Real.exp s : ℝ) : ℂ)) := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
      apply UpperHalfPlane.ext
      simp [BinQF.geodesicH, squareRep_geodesic hn]
    rw [h1, squareRep_evalC hn, mul_pow, mul_pow]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    ring
  simp_rw [hint]
  rw [MeasureTheory.integral_const_mul, ← integral_Ioi_eq_integral_exp
    (fun t : ℝ ↦ G (UpperHalfPlane.ofComplex (-(c : ℂ) / n + I * (t : ℂ))) * (t : ℂ) ^ (k - 1))]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  rw [Complex.ofReal_natCast]
  field_simp

/-! ### Sums over `ZMod M` and periodicity -/

theorem sum_zmod_eq_sum_range {M : ℕ} [NeZero M] (F : ZMod M → ℂ) :
    ∑ j : ZMod M, F j = ∑ c ∈ Finset.range M, F (c : ZMod M) := by
  refine Finset.sum_bij' (fun j _ ↦ j.val) (fun c _ ↦ (c : ZMod M)) ?_ ?_ ?_ ?_ ?_
  · intro j _; exact Finset.mem_range.2 (ZMod.val_lt j)
  · intro c _; exact Finset.mem_univ _
  · intro j _; simp
  · intro c hc; exact ZMod.val_cast_of_lt (Finset.mem_range.1 hc)
  · intro j _; simp

theorem cusp_periodic (w : ℤ) (G : CuspForm 𝒮ℒ w) (τ : ℍ) (m : ℤ) :
    G ((m : ℝ) +ᵥ τ) = G τ := by
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex (Γ := 𝒮ℒ) (h := 1) G
    one_mem_strictPeriods_SL
  have := (hper.int_mul m) (τ : ℂ)
  have him : 0 < ((τ : ℂ) + (m : ℂ) * ((1 : ℝ) : ℂ)).im := by simpa using τ.im_pos
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] at this
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos him] at this
  convert this using 2
  ext
  simp [add_comm]

/-! ### The twist -/

/-- The twist of a level one cusp form by the Kronecker character of `D`. -/
noncomputable def twistForm {D : ℤ} (hD4 : D ≡ 0 [ZMOD 4] ∨ D ≡ 1 [ZMOD 4]) (hD0 : D ≠ 0) {w : ℤ}
    (G : CuspForm 𝒮ℒ w) :
    CuspForm ((Gamma1 (D.natAbs * D.natAbs)).map (Matrix.SpecialLinearGroup.mapGL ℝ)) w :=
  haveI : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD0⟩
  CuspForm.twist (M := D.natAbs) (N := 1) (L := D.natAbs * D.natAbs)
    (fun x ↦ TauCeti.kroneckerChar ℂ D hD4 hD0 x) (by simp) dvd_rfl
    (CuspForm.restrict (TauCeti.Gamma1_one_map_eq_SL).le G)

theorem dft_kronecker (hGauss : KroneckerGaussSum) {D : ℤ} (hDf : IsFundamentalDiscriminant D)
    (hD4 : D ≡ 0 [ZMOD 4] ∨ D ≡ 1 [ZMOD 4]) (hD0 : D ≠ 0) [NeZero D.natAbs] (x : ZMod D.natAbs) :
    ZMod.dft (fun y : ZMod D.natAbs ↦ (TauCeti.kroneckerChar ℂ D hD4 hD0 y)) (-x) =
      (TauCeti.kroneckerSym D x.val : ℂ) * sqrtDisc D := by
  rw [ZMod.dft_apply, sum_zmod_eq_sum_range, ← hGauss.eq D hDf (x.val : ℤ)]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  have h : -((c : ZMod D.natAbs) * -x) = (((c : ℤ) * (x.val : ℤ) : ℤ) : ZMod D.natAbs) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    ring
  rw [h, ZMod.stdAddChar_coe, TauCeti.kroneckerChar_natCast, smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

/-- **The twist as a sum of translates.** -/
theorem twistForm_apply (hGauss : KroneckerGaussSum) {D : ℤ} (hDf : IsFundamentalDiscriminant D)
    (hD4 : D ≡ 0 [ZMOD 4] ∨ D ≡ 1 [ZMOD 4]) (hD0 : D ≠ 0) {w : ℤ} (G : CuspForm 𝒮ℒ w) (τ : ℍ) :
    twistForm hD4 hD0 G τ = (D.natAbs : ℂ)⁻¹ * sqrtDisc D *
      ∑ c ∈ Finset.range D.natAbs, (TauCeti.kroneckerSym D c : ℂ) *
        G ((-(c : ℝ) / D.natAbs) +ᵥ τ) := by
  haveI : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD0⟩
  unfold twistForm
  rw [CuspForm.twist_apply, mul_assoc]
  congr 1
  rw [← Equiv.sum_comp (Equiv.neg (ZMod D.natAbs))]
  simp only [Equiv.neg_apply]
  have hM : (0 : ℝ) < D.natAbs := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
  have step : ∀ x : ZMod D.natAbs, ZMod.dft (fun x ↦ (TauCeti.kroneckerChar ℂ D hD4 hD0) x) (-x) *
        (CuspForm.restrict (TauCeti.Gamma1_one_map_eq_SL).le G) (((-x).val : ℝ) / D.natAbs +ᵥ τ) =
      sqrtDisc D * ((TauCeti.kroneckerSym D x.val : ℂ) * G ((-(x.val : ℝ) / D.natAbs) +ᵥ τ)) := by
    intro x
    rw [dft_kronecker hGauss hDf hD4 hD0 x]
    have hG : (CuspForm.restrict (TauCeti.Gamma1_one_map_eq_SL).le G) (((-x).val : ℝ) / D.natAbs +ᵥ τ)
        = G ((-(x.val : ℝ) / D.natAbs) +ᵥ τ) := by
      change G _ = G _
      by_cases hx : x = 0
      · subst hx; simp
      · haveI : NeZero x := ⟨hx⟩
        rw [ZMod.val_neg_of_ne_zero,Nat.cast_sub (ZMod.val_lt x).le]
        have : ((D.natAbs : ℝ) - x.val) / D.natAbs = ((1 : ℤ) : ℝ) + (-(x.val : ℝ) / D.natAbs) := by
          push_cast
          field_simp
          ring
        rw [this, add_vadd]
        exact cusp_periodic w G _ 1
    rw [hG]
    ring
  rw [Finset.mul_sum]
  refine (Finset.sum_congr rfl fun x _ ↦ step x).trans ?_
  rw [sum_zmod_eq_sum_range (fun x : ZMod D.natAbs ↦ sqrtDisc D *
    ((TauCeti.kroneckerSym D x.val : ℂ) * G ((-(x.val : ℝ) / D.natAbs) +ᵥ τ)))]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  rw [ZMod.val_cast_of_lt (Finset.mem_range.1 hc)]

theorem twistForm_coeff {D : ℤ} (hD4 : D ≡ 0 [ZMOD 4] ∨ D ≡ 1 [ZMOD 4]) (hD0 : D ≠ 0) {w : ℤ}
    (G : CuspForm 𝒮ℒ w) (b : ℕ → ℂ) (hb : Abstract.HasQExp G b) {n : ℕ} (hn : n ≠ 0) :
    (UpperHalfPlane.qExpansion 1 (twistForm hD4 hD0 G)).coeff n = twistCoeff D b n := by
  haveI : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD0⟩
  unfold twistForm
  rw [CuspForm.qExpansion_twist_coeff]
  rw [TauCeti.kroneckerChar_natCast, ← kroneckerDisc_eq_kroneckerSym D hn, twistCoeff,
    hasQExp_coeff_eq_qExpansion G hb n]
  rfl

/-- **The Mellin transform of the twist.** -/
theorem integral_twistForm {k : ℕ} (hk : 2 ≤ k) {D : ℤ}
    (hD4 : D ≡ 0 [ZMOD 4] ∨ D ≡ 1 [ZMOD 4]) (hD0 : D ≠ 0)
    (G : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ) (hb : Abstract.HasQExp G b)
    (L : ℂ → ℂ) (hL : IsEntireLSeries (twistCoeff D b) ((k : ℝ) + 1) L) :
    ∫ t in Set.Ioi (0 : ℝ), twistForm hD4 hD0 G (UpperHalfPlane.ofComplex (I * t)) * (t : ℂ) ^ (k - 1) =
      ((k - 1).factorial : ℂ) / (2 * π) ^ k * L k := by
  haveI : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD0⟩
  set T := twistForm hD4 hD0 G with hT
  have hkpos : (0 : ℤ) < ((2 * k : ℕ) : ℤ) := by omega
  have hwidth : ((Gamma1 (D.natAbs * D.natAbs)).map (Matrix.SpecialLinearGroup.mapGL ℝ)).strictWidthInfty = 1 := by
    simp
  have hLeq : L = fun s ↦ ((1 : ℝ) : ℂ) ^ (-s) * ModularForm.L hkpos T s := by
    have := CuspForm.eq_strictWidthInfty_cpow_mul_L T hkpos hL.1 (fun {s} hs ↦ ?_)
    · rw [hwidth] at this
      exact this
    · rw [hL.2 s (by simpa using (by push_cast at hs; linarith : (k : ℝ) + 1 < s.re))]
      rw [hwidth]
      exact LSeries_congr (fun {n} hn ↦ (twistForm_coeff hD4 hD0 G b hb hn).symm) s
  have hLk : L k = ModularForm.L hkpos T ((k - 1 : ℕ) + 1) := by
    rw [hLeq]
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]
    congr 1
    push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
    ring
  have hΛ := ModularForm.Λ_natCast_add_one hkpos T (k - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hΛ
  have hm := congrFun (CuspForm.Λ_eq_mellin hkpos T) (((k - 1 : ℕ) : ℂ) + 1)
  rw [mellin] at hm
  have hk1 : (((k - 1 : ℕ) : ℂ) + 1) = (k : ℂ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]; push_cast; ring
  rw [hk1] at hLk hΛ hm
  rw [hLk, ← hΛ, hm]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  have : ((k : ℂ) - 1) = ((k - 1 : ℕ) : ℂ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]; simp
  simp only [this, Complex.cpow_natCast, smul_eq_mul]
  ring

/-! ### Integrability along vertical lines -/

theorem integrableOn_translate {j : ℕ} (G : CuspForm 𝒮ℒ ((2 * (j + 1) : ℕ) : ℤ)) (x : ℚ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦ G (UpperHalfPlane.ofComplex ((x : ℂ) + I * t)) * (t : ℂ) ^ j)
      (Set.Ioi (0 : ℝ)) := by
  have hP : (MvPolynomial.X 0 - MvPolynomial.C (x : ℂ) * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) ^ j *
      MvPolynomial.X 1 ^ j ∈ MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (2 * j) := by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    have h1 : (MvPolynomial.X 0 - MvPolynomial.C (x : ℂ) * MvPolynomial.X 1 :
        MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 :=
      (MvPolynomial.isHomogeneous_X ℂ 0).sub (MvPolynomial.isHomogeneous_C_mul_X _ _)
    have := (h1.pow j).mul ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).pow j)
    convert this using 1
    ring
  let P : MvPolynomial.homogeneousSubmodule (Fin 2) ℂ (2 * j) := ⟨_, hP⟩
  let g : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.upperRightHom x
  have hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det := by
    simp [g, Matrix.GeneralLinearGroup.upperRightHom_apply]
  have h := TauCeti.ModularSymbols.integrableOn_resToImagAxis_periodIntegrand_slash (Γ := 𝒮ℒ)
    G (by push_cast; ring) P hg
  have hmap : Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g =
      Matrix.GeneralLinearGroup.upperRightHom (x : ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [g, Matrix.GeneralLinearGroup.upperRightHom_apply]
  have hslash : ∀ τ : ℍ, (⇑G ∣[((2 * (j + 1) : ℕ) : ℤ)] g) τ = G ((x : ℝ) +ᵥ τ) := by
    intro τ
    rw [ModularForm.rat_slash, hmap]
    exact TauCeti.ModularForm.slash_upperRightHom_apply _ _ _ _
  refine MeasureTheory.IntegrableOn.congr_fun (h.const_mul ((I : ℂ) ^ j)⁻¹) (fun t ht ↦ ?_)
    measurableSet_Ioi
  have ht' : (0 : ℝ) < t := ht
  rw [UpperHalfPlane.resToImagAxis_of_pos _ ht',
    TauCeti.ModularSymbols.periodIntegrand_slash_apply (k := ((2 * (j + 1) : ℕ) : ℤ)) (by push_cast; ring) G P hg, hslash, hmap]
  have hdet : ((g : Matrix (Fin 2) (Fin 2) ℚ).det) = 1 := by
    simp [g, Matrix.GeneralLinearGroup.upperRightHom_apply]
  have hpt : ∀ τ : ℍ, (τ : ℂ) = I * t → G ((x : ℝ) +ᵥ τ) = G (UpperHalfPlane.ofComplex ((x : ℂ) + I * t)) := by
    intro τ hτ
    congr 1
    ext
    rw [UpperHalfPlane.coe_vadd, UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa [hτ] using ht')]
    simp [hτ, add_comm]
  rw [hpt _ rfl, hdet]
  simp [P, UpperHalfPlane.num, UpperHalfPlane.denom, Matrix.GeneralLinearGroup.upperRightHom_apply,
    mul_pow]
  have : (I : ℂ) ^ j ≠ 0 := pow_ne_zero _ I_ne_zero
  field_simp

/-! ### The constant -/

theorem rpow_const_eq {k : ℕ} (hk : 1 ≤ k) (M : ℕ) (hM : 0 < M) :
    ((M : ℝ) ^ (k - 1)) * √(M : ℝ) = (M : ℝ) ^ ((k : ℝ) - 1 / 2) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hM']
  congr 1
  rw [Nat.cast_sub hk]
  push_cast
  ring

theorem const_eq {k : ℕ} (hk : 1 ≤ k) {D : ℤ} (hD : 0 < (-1) ^ k * D) :
    (D.natAbs : ℂ) ^ (k - 1) * I ^ k * ((D.natAbs : ℂ) * (sqrtDisc D)⁻¹) =
      (((-1 : ℝ) ^ (k / 2) * (D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) : ℂ) := by
  have hD0 : D ≠ 0 := by rintro rfl; simp at hD
  have hM : 0 < D.natAbs := Int.natAbs_pos.2 hD0
  have hM' : (0 : ℝ) < D.natAbs := by exact_mod_cast hM
  rw [← rpow_const_eq hk _ hM]
  set r : ℝ := √(D.natAbs : ℝ) with hr
  have hr0 : r ≠ 0 := (Real.sqrt_pos.2 hM').ne'
  have hrr : r ^ 2 = D.natAbs := Real.sq_sqrt hM'.le
  have hrc : ((D.natAbs : ℕ) : ℂ) = (r : ℂ) ^ 2 := by exact_mod_cast hrr.symm
  rcases lt_or_gt_of_ne hD0 with hneg | hpos
  · -- D < 0, k odd
    have hodd : Odd k := by
      by_contra h
      rw [Nat.not_odd_iff_even] at h
      rw [h.neg_one_pow] at hD
      omega
    obtain ⟨m, hm⟩ := hodd
    have hs : sqrtDisc D = I * (r : ℂ) := by
      rw [sqrtDisc, if_neg (by omega)]
      congr 2
      rw [hr]
      congr 1
      have : (D.natAbs : ℝ) = -(D : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hneg)]
      rw [this]
    have hk2 : k / 2 = m := by omega
    have hI : (I : ℂ) ^ k = (-1) ^ m * I := by
      rw [hm, pow_succ, pow_mul, I_sq]
    have hkey : (D.natAbs : ℂ) * (sqrtDisc D)⁻¹ = -(I * r) := by
      have : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
      rw [hs, hrc]
      field_simp
      linear_combination I_sq
    rw [hkey, hI, hk2]
    push_cast
    linear_combination (-((D.natAbs : ℂ) ^ (k - 1) * (-1) ^ m * r)) * I_sq
  · -- D > 0, k even
    have heven : Even k := by
      by_contra h
      rw [Nat.not_even_iff_odd] at h
      rw [h.neg_one_pow] at hD
      omega
    obtain ⟨m, hm⟩ := heven
    have hs : sqrtDisc D = (r : ℂ) := by
      rw [sqrtDisc, if_pos (by omega)]
      congr 2
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hpos)]
    have hk2 : k / 2 = m := by omega
    have hI : (I : ℂ) ^ k = (-1) ^ m := by
      rw [hm, ← two_mul, pow_mul, I_sq]
    have hkey : (D.natAbs : ℂ) * (sqrtDisc D)⁻¹ = r := by
      have : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
      rw [hs, hrc]
      field_simp
    rw [hkey, hI, hk2]
    push_cast
    ring

/-- **Step 3: the twisted sum of cycle integrals is $L(G, D, k)$**, given the Gauss sum. -/
theorem sum_kroneckerSym_cycleIntegral (hGauss : KroneckerGaussSum) {k : ℕ} (hk : 2 ≤ k) {D : ℤ}
    (hD : KohnenDisc k D) (G : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ) (hb : Abstract.HasQExp G b)
    (L : ℂ → ℂ) (hL : IsEntireLSeries (twistCoeff D b) ((k : ℝ) + 1) L) :
    ∑ c ∈ Finset.range D.natAbs,
        (TauCeti.kroneckerSym D c : ℂ) * cycleIntegral k G (BinQF.squareRep D.natAbs c) =
      (squareCycleConst k D : ℂ) * L k := by
  obtain ⟨hDf, hDpos⟩ := hD
  have hD0 : D ≠ 0 := by rintro rfl; simp at hDpos
  have hD4 : D ≡ 0 [ZMOD 4] ∨ D ≡ 1 [ZMOD 4] := by
    rcases hDf with ⟨h4, -⟩ | ⟨m, rfl, -, -⟩
    · right; simpa [Int.ModEq] using h4
    · left; exact Int.modEq_zero_iff_dvd.mpr ⟨m, rfl⟩
  have hMpos : 0 < D.natAbs := Int.natAbs_pos.2 hD0
  haveI : NeZero D.natAbs := ⟨hMpos.ne'⟩
  have hDpos' : 0 < (-1) ^ k * D := hDpos
  have hconst := const_eq (by omega : 1 ≤ k) hDpos'
  have hmell := integral_twistForm hk hD4 hD0 G b hb L hL
  have hs0 : sqrtDisc D ≠ 0 := by
    rw [sqrtDisc]
    split_ifs with h
    · have : (0 : ℝ) < D := by exact_mod_cast lt_of_le_of_ne h (Ne.symm hD0)
      exact_mod_cast (Real.sqrt_pos.2 this).ne'
    · have : (0 : ℝ) < -D := by exact_mod_cast (by omega : 0 < -D)
      exact mul_ne_zero I_ne_zero (by exact_mod_cast (Real.sqrt_pos.2 this).ne')
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hmell hconst
  have hint : ∀ c ∈ Finset.range D.natAbs, MeasureTheory.Integrable
      (fun t : ℝ ↦ (TauCeti.kroneckerSym D c : ℂ) *
        (G (UpperHalfPlane.ofComplex (-(c : ℂ) / D.natAbs + I * t)) * (t : ℂ) ^ j))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro c _
    have := integrableOn_translate G (-(c : ℚ) / D.natAbs)
    have e : ((-(c : ℚ) / D.natAbs : ℚ) : ℂ) = -(c : ℂ) / D.natAbs := by push_cast; ring
    rw [e] at this
    exact this.const_mul _
  have h1 : ∀ c ∈ Finset.range D.natAbs,
      (TauCeti.kroneckerSym D c : ℂ) * cycleIntegral (j + 1) G (BinQF.squareRep D.natAbs c) =
      (D.natAbs : ℂ) ^ j * I ^ (j + 1) * ∫ t in Set.Ioi (0 : ℝ), (TauCeti.kroneckerSym D c : ℂ) *
        (G (UpperHalfPlane.ofComplex (-(c : ℂ) / D.natAbs + I * t)) * (t : ℂ) ^ j) := by
    intro c _
    rw [cycleIntegral_squareRep (by omega) G hMpos c, MeasureTheory.integral_const_mul]
    simp only [Nat.add_sub_cancel, Int.cast_natCast]
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, ← MeasureTheory.integral_finsetSum _ hint]
  have h2 : ∫ t in Set.Ioi (0 : ℝ), ∑ c ∈ Finset.range D.natAbs, (TauCeti.kroneckerSym D c : ℂ) *
        (G (UpperHalfPlane.ofComplex (-(c : ℂ) / D.natAbs + I * t)) * (t : ℂ) ^ j) =
      ((D.natAbs : ℂ) * (sqrtDisc D)⁻¹) * ∫ t in Set.Ioi (0 : ℝ),
        twistForm hD4 hD0 G (UpperHalfPlane.ofComplex (I * t)) * (t : ℂ) ^ j := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    have ht' : (0 : ℝ) < t := ht
    have him : 0 < (I * (t : ℂ)).im := by simpa using ht'
    rw [twistForm_apply hGauss hDf hD4 hD0 G]
    have hpt : ∀ c : ℕ, G ((-(c : ℝ) / D.natAbs) +ᵥ UpperHalfPlane.ofComplex (I * t)) =
        G (UpperHalfPlane.ofComplex (-(c : ℂ) / D.natAbs + I * t)) := by
      intro c
      congr 1
      have him2 : 0 < (-(c : ℂ) / D.natAbs + I * t).im := by
        simpa [Complex.div_natCast_im] using ht'
      ext
      rw [UpperHalfPlane.coe_vadd, UpperHalfPlane.ofComplex_apply_of_im_pos him,
        UpperHalfPlane.ofComplex_apply_of_im_pos him2]
      push_cast
      simp [add_comm]
    simp only [hpt]
    have hM : (D.natAbs : ℂ) ≠ 0 := by exact_mod_cast hMpos.ne'
    field_simp
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  rw [h2, hmell]
  calc (D.natAbs : ℂ) ^ j * I ^ (j + 1) * ((D.natAbs : ℂ) * (sqrtDisc D)⁻¹ *
        (((j).factorial : ℂ) / (2 * π) ^ (j + 1) * L ((j + 1 : ℕ) : ℂ)))
      = ((D.natAbs : ℂ) ^ j * I ^ (j + 1) * ((D.natAbs : ℂ) * (sqrtDisc D)⁻¹)) *
        (((j).factorial : ℂ) / (2 * π) ^ (j + 1) * L ((j + 1 : ℕ) : ℂ)) := by ring
    _ = _ := by
      rw [hconst]
      unfold squareCycleConst
      push_cast
      ring

end ModularFormsKB.HalfIntegral
