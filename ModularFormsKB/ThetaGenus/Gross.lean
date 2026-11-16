import ModularFormsKB.ThetaGenus.Gram
import ModularFormsKB.HalfIntegral.Waldspurger.Gross
import ModularFormsKB.HalfIntegral.Abstract.ThetaInstance

/-!
# Gross's weight 3/2 form is a cusp form in Kohnen's plus space of level 44 (an instance of the genus theorem)

Part of loose end LE-MF-0175.

`HalfIntegral.Waldspurger.Gross` (`Gross.lean`) records Gross's ternary forms
`Q₁ = 4x₀² + 4x₀x₂ + 11x₁² + 12x₂²` and `Q₂ = 3x₀² + 4x₀x₂ + 44x₁² + 44x₁x₂ + 16x₂²` and the
coefficients `grossCoeff n = (r_{Q₁}(n) - r_{Q₂}(n)) / 2` of `g = (θ₁ - θ₂)/2`, but not that `g` is a
modular form. Here, with the Gram convention of `Gram.lean` (Hessians `grossH₁`, `grossH₂`,
`xᵀ H_i x = 2 Q_i(x)`):

* both Hessians have determinant `3872 = 2⁵ · 11²` and admissible level `44` (`44 H_i⁻¹` is an even
  integer matrix; `isGramLevel_grossH₁`, `isGramLevel_grossH₂`);
* they are in one genus (`gramSameGenus_gross`): they have common sublattices of index `3`
  (`U₁ᵀ H₁ U₁ = U₂ᵀ H₂ U₂`, `det U₁ = det U₂ = 3`) and of index `5` (`det V₁ = 5`, `det V₂ = -5`),
  found by a computer search and checked here by `decide`;
* hence (headline H5, odd rank `3`, `N = 11`) `θ₁ - θ₂ ∈ S_{3/2}(44, χ)`. The character is trivial:
  `χ(d) = (2 · 3872 / d) = (88² / d) = 1` (`grossForm_mem_plusCuspForms`);
* `g = (θ₁ - θ₂)/2` has `q`-expansion `∑ grossCoeff n qⁿ` and satisfies Kohnen's plus condition
  (`grossCoeff_eq_zero_of_mod_four`), so `g ∈ S⁺_{3/2}(44)` for the theta multiplier.
-/

open Complex Module Filter Topology
open scoped Real ModularForm UpperHalfPlane MatrixGroups Matrix

set_option linter.unusedSectionVars false

namespace ModularFormsKB.ThetaGenus.Gross

open ModularFormsKB.HalfIntegral.Waldspurger.Gross

/-- The Hessian of `Q₁`. -/
def grossH₁ : Matrix (Fin 3) (Fin 3) ℤ := !![8, 0, 4; 0, 22, 0; 4, 0, 24]

/-- The Hessian of `Q₂`. -/
def grossH₂ : Matrix (Fin 3) (Fin 3) ℤ := !![6, 0, 4; 0, 88, 44; 4, 44, 32]

theorem gramNorm_grossH₁ (x : Fin 3 → ℤ) : gramNorm grossH₁ x = 2 * grossQ₁ (x 0, x 1, x 2) := by
  simp [gramNorm, dotProduct, Matrix.mulVec, Fin.sum_univ_three, grossH₁, grossQ₁]
  ring

theorem gramNorm_grossH₂ (x : Fin 3 → ℤ) : gramNorm grossH₂ x = 2 * grossQ₂ (x 0, x 1, x 2) := by
  simp [gramNorm, dotProduct, Matrix.mulVec, Fin.sum_univ_three, grossH₂, grossQ₂]
  ring

theorem posDef_grossH₁ : (grossH₁.map (Int.cast : ℤ → ℝ)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [grossH₁]
  · intro x hx
    simp only [star_trivial]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, grossH₁]
    by_contra hneg
    apply hx
    have h1 : x 1 = 0 := by nlinarith [sq_nonneg (2 * x 0 + x 2), sq_nonneg (x 2), sq_nonneg (x 1)]
    have h2 : x 2 = 0 := by nlinarith [sq_nonneg (2 * x 0 + x 2), sq_nonneg (x 2), sq_nonneg (x 1)]
    have h0 : x 0 = 0 := by nlinarith [sq_nonneg (2 * x 0 + x 2), sq_nonneg (x 2), sq_nonneg (x 1)]
    ext i; fin_cases i <;> simp [h0, h1, h2]

theorem posDef_grossH₂ : (grossH₂.map (Int.cast : ℤ → ℝ)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [grossH₂]
  · intro x hx
    simp only [star_trivial]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, grossH₂]
    by_contra hneg
    apply hx
    have h2 : x 2 = 0 := by
      nlinarith [sq_nonneg (3 * x 0 + 2 * x 2), sq_nonneg (2 * x 1 + x 2), sq_nonneg (x 2)]
    have h1 : x 1 = 0 := by
      nlinarith [sq_nonneg (3 * x 0 + 2 * x 2), sq_nonneg (2 * x 1 + x 2), sq_nonneg (x 2)]
    have h0 : x 0 = 0 := by
      nlinarith [sq_nonneg (3 * x 0 + 2 * x 2), sq_nonneg (2 * x 1 + x 2), sq_nonneg (x 2)]
    ext i; fin_cases i <;> simp [h0, h1, h2]

theorem isEvenGram_grossH₁ : IsEvenGram grossH₁ := by
  refine ⟨by decide +kernel, fun i ↦ by fin_cases i <;> decide, ?_⟩
  exact posDef_grossH₁

theorem isEvenGram_grossH₂ : IsEvenGram grossH₂ := by
  refine ⟨by decide +kernel, fun i ↦ by fin_cases i <;> decide, ?_⟩
  exact posDef_grossH₂

theorem isGramLevel_grossH₁ : IsGramLevel grossH₁ (4 * 11) := by
  refine ⟨!![6, 0, -1; 0, 2, 0; -1, 0, 2], by unfold grossH₁; decide +kernel,
    fun i ↦ by fin_cases i <;> decide⟩

theorem isGramLevel_grossH₂ : IsGramLevel grossH₂ (4 * 11) := by
  refine ⟨!![10, 2, -4; 2, 2, -3; -4, -3, 6], by unfold grossH₂; decide +kernel,
    fun i ↦ by fin_cases i <;> decide⟩

theorem det_grossH₁ : grossH₁.det = 3872 := by
  simp [grossH₁, Matrix.det_fin_three]

theorem det_grossH₂ : grossH₂.det = 3872 := by
  simp [grossH₂, Matrix.det_fin_three]

/-- **Gross's two forms are in one genus**, from common sublattices of indices `3` and `5`. -/
theorem gramSameGenus_gross : GramSameGenus grossH₁ grossH₂ := by
  have hU : (!![3, 2, 1; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ).transpose * grossH₁ *
      !![3, 2, 1; 0, 1, 0; 0, 0, 1] =
      (!![-4, -3, -2; -1, 0, -1; 2, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ).transpose * grossH₂ *
      !![-4, -3, -2; -1, 0, -1; 2, 0, 1] := by
    unfold grossH₁ grossH₂; decide +kernel
  have hV : (!![5, 4, 2; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ).transpose * grossH₁ *
      !![5, 4, 2; 0, 1, 0; 0, 0, 1] =
      (!![4, 5, 2; -1, 0, -1; 2, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ).transpose * grossH₂ *
      !![4, 5, 2; -1, 0, -1; 2, 0, 1] := by
    unfold grossH₁ grossH₂; decide +kernel
  have d1 : (!![3, 2, 1; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ).det = 3 := by
    simp [Matrix.det_fin_three]
  have d2 : (!![-4, -3, -2; -1, 0, -1; 2, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ).det = 3 := by
    simp [Matrix.det_fin_three]
  have d3 : (!![5, 4, 2; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ).det = 5 := by
    simp [Matrix.det_fin_three]
  have d4 : (!![4, 5, 2; -1, 0, -1; 2, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ).det = -5 := by
    simp [Matrix.det_fin_three]
  refine gramSameGenus_of_common_sublattices (isEvenGram_grossH₁.symm)
    isEvenGram_grossH₁.even_diag isEvenGram_grossH₂.symm isEvenGram_grossH₂.even_diag
    (by rw [det_grossH₁, det_grossH₂]) hU hV ?_
  rw [d1, d2, d3, d4]
  exact ⟨14, 5, by norm_num⟩

/-- Generic `q`-expansion of `θ_H` for a ternary Hessian `H` with `xᵀHx = 2Q(x)` and solutions of
`Q = n` in the box `[-n, n]³`. -/
theorem hasQExp_thetaGram_of {H : Matrix (Fin 3) (Fin 3) ℤ} (hH : IsEvenGram H)
    (Q : ℤ × ℤ × ℤ → ℤ) (hQ : ∀ x : Fin 3 → ℤ, gramNorm H x = 2 * Q (x 0, x 1, x 2))
    (hbox : ∀ (n : ℕ) (y : ℤ × ℤ × ℤ), Q y = n → y ∈ box n) :
    HalfIntegral.Abstract.HasQExp (fun τ ↦ thetaGram H τ)
      (fun n ↦ (thetaCount Q n : ℂ)) := by
  intro τ
  have hnn : ∀ x : Fin 3 → ℤ, 0 ≤ Q (x 0, x 1, x 2) := by
    intro x
    have h1 := norm_sq_gramEquiv hH x
    have h2 : (0 : ℝ) ≤ (gramNorm H x : ℝ) := by rw [← h1]; positivity
    have h3 : 0 ≤ gramNorm H x := by exact_mod_cast h2
    rw [hQ] at h3
    omega
  have hsum : Summable fun x : Fin 3 → ℤ ↦ cexp (π * I * (gramNorm H x : ℂ) * τ) := by
    have := ZLattice.summable_thetaSeries (gramLattice hH) τ
    rw [← (gramEquiv hH).toEquiv.summable_iff] at this
    refine this.congr fun x ↦ ?_
    simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, norm_sq_gramEquiv]
    push_cast
    rfl
  have hfib := hsum.hasSum.tsum_fiberwise (fun x : Fin 3 → ℤ ↦ (Q (x 0, x 1, x 2)).toNat)
  have hcard : ∀ m : ℕ, Nat.card ((fun x : Fin 3 → ℤ ↦ (Q (x 0, x 1, x 2)).toNat) ⁻¹' {m}) =
      thetaCount Q m := by
    intro m
    unfold thetaCount
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr
      { toFun := fun b ↦ ⟨(b.1 0, b.1 1, b.1 2), ?_⟩
        invFun := fun y ↦ ⟨![y.1.1, y.1.2.1, y.1.2.2], ?_⟩
        left_inv := fun b ↦ ?_
        right_inv := fun y ↦ ?_ }
    · have hb : (Q (b.1 0, b.1 1, b.1 2)).toNat = m := b.2
      have := hnn b.1
      have hq : Q (b.1 0, b.1 1, b.1 2) = m := by omega
      exact Finset.mem_filter.mpr ⟨hbox m _ hq, hq⟩
    · have hy := (Finset.mem_filter.mp y.2).2
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [hy]; simp
    · apply Subtype.ext
      funext i
      fin_cases i <;> rfl
    · apply Subtype.ext
      rfl
  have key : ∀ m : ℕ, ∑' b : ((fun x : Fin 3 → ℤ ↦ (Q (x 0, x 1, x 2)).toNat) ⁻¹' {m}),
      cexp (π * I * (gramNorm H b.1 : ℂ) * τ) =
        (thetaCount Q m : ℂ) * cexp (2 * π * I * m * τ) := by
    intro m
    have hconst : ∀ b : ((fun x : Fin 3 → ℤ ↦ (Q (x 0, x 1, x 2)).toNat) ⁻¹' {m}),
        cexp (π * I * (gramNorm H b.1 : ℂ) * τ) = cexp (2 * π * I * m * τ) := by
      intro b
      have hb : (Q (b.1 0, b.1 1, b.1 2)).toNat = m := b.2
      have := hnn b.1
      have hq : Q (b.1 0, b.1 1, b.1 2) = m := by omega
      have hg : gramNorm H b.1 = 2 * m := by rw [hQ, hq]
      rw [hg]
      congr 1
      push_cast
      ring
    rw [tsum_congr hconst, tsum_const, hcard, nsmul_eq_mul]
  have h2 := hfib
  simp only [key] at h2
  exact h2

/-- The `q`-expansion of `θ_{H_i}`: the coefficient of `qⁿ` is `r_{Q_i}(n)` (counted in the box
`[-n, n]³`, `thetaCount`). -/
theorem hasQExp_thetaGram_grossH₁ :
    HalfIntegral.Abstract.HasQExp (fun τ ↦ thetaGram grossH₁ τ)
      (fun n ↦ (thetaCount grossQ₁ n : ℂ)) :=
  hasQExp_thetaGram_of isEvenGram_grossH₁ grossQ₁ gramNorm_grossH₁
    (fun _ _ h ↦ mem_box_of_grossQ₁ h)

theorem hasQExp_thetaGram_grossH₂ :
    HalfIntegral.Abstract.HasQExp (fun τ ↦ thetaGram grossH₂ τ)
      (fun n ↦ (thetaCount grossQ₂ n : ℂ)) :=
  hasQExp_thetaGram_of isEvenGram_grossH₂ grossQ₂ gramNorm_grossH₂
    (fun _ _ h ↦ mem_box_of_grossQ₂ h)

theorem thetaCount_even (Q : ℤ × ℤ × ℤ → ℤ) (hQneg : ∀ x, Q (-x) = Q x) (hQ0 : Q 0 = 0)
    {n : ℕ} (hn : 1 ≤ n) : Even (thetaCount Q n) := by
  unfold thetaCount
  have hmem : ∀ x ∈ (box n).filter (fun x ↦ Q x = n), -x ∈ (box n).filter (fun x ↦ Q x = n) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨?_, by rw [hQneg]; exact hx2⟩
    obtain ⟨a, b, c⟩ := x
    simp only [box, Finset.mem_product, Finset.mem_Icc, Prod.neg_mk] at hx1 ⊢
    omega
  have h := Finset.sum_involution (s := (box n).filter (fun x ↦ Q x = n))
    (f := fun _ ↦ (1 : ZMod 2)) (fun x _ ↦ -x)
    (fun a _ ↦ by decide)
    (fun a ha _ ↦ by
      have hne : a ≠ 0 := by
        rintro rfl
        have := (Finset.mem_filter.mp ha).2
        rw [hQ0] at this
        omega
      obtain ⟨x, y, z⟩ := a
      intro h
      apply hne
      simp only [Prod.neg_mk, Prod.mk.injEq, Prod.mk_eq_zero] at h ⊢
      omega)
    (fun a ha ↦ hmem a ha) (fun a _ ↦ neg_neg a)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact (ZMod.natCast_eq_zero_iff_even).mp h

theorem thetaCount_zero (Q : ℤ × ℤ × ℤ → ℤ) (hQ0 : Q 0 = 0)
    (hbox : ∀ (n : ℕ) (y : ℤ × ℤ × ℤ), Q y = n → y ∈ box n) : thetaCount Q 0 = 1 := by
  unfold thetaCount
  rw [Finset.card_eq_one]
  refine ⟨0, ?_⟩
  ext y
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hy⟩
    have := hbox 0 y (by simpa using hy)
    obtain ⟨a, b, c⟩ := y
    simp only [box, Finset.mem_product, Finset.mem_Icc] at this
    simp only [Prod.mk_eq_zero]
    push_cast at this
    omega
  · rintro rfl
    refine ⟨?_, by simpa using hQ0⟩
    simp [box]
    rfl

theorem grossCoeff_cast (n : ℕ) :
    (grossCoeff n : ℂ) = ((thetaCount grossQ₁ n : ℂ) - (thetaCount grossQ₂ n : ℂ)) / 2 := by
  have hQ0₁ : grossQ₁ 0 = 0 := by simp [grossQ₁]
  have hQ0₂ : grossQ₂ 0 = 0 := by simp [grossQ₂]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have e1 := thetaCount_zero _ hQ0₁ (fun _ _ h ↦ mem_box_of_grossQ₁ h)
    have e2 := thetaCount_zero _ hQ0₂ (fun _ _ h ↦ mem_box_of_grossQ₂ h)
    simp [grossCoeff, e1, e2]
  · obtain ⟨a, ha⟩ := thetaCount_even grossQ₁ (fun x ↦ by simp [grossQ₁]) hQ0₁ hn
    obtain ⟨b, hb⟩ := thetaCount_even grossQ₂ (fun x ↦ by simp [grossQ₂]) hQ0₂ hn
    have h : grossCoeff n = (a : ℤ) - b := by
      unfold grossCoeff
      rw [ha, hb]
      push_cast
      omega
    rw [h, ha, hb]
    push_cast
    ring

/-- **`g = (θ₁ - θ₂)/2` has `q`-expansion `∑ grossCoeff n qⁿ`** (both counts are even for `n ≥ 1`,
since `x ↦ -x` has no fixed point on `Q_i = n`, and equal to `1` for `n = 0`). -/
theorem hasQExp_grossForm :
    HalfIntegral.Abstract.HasQExp (fun τ ↦ (thetaGram grossH₁ τ - thetaGram grossH₂ τ) / 2)
      (fun n ↦ (grossCoeff n : ℂ)) := by
  intro τ
  have h := ((hasQExp_thetaGram_grossH₁ τ).sub (hasQExp_thetaGram_grossH₂ τ)).div_const 2
  have hfun : (fun n : ℕ ↦ (grossCoeff n : ℂ) * cexp (2 * π * I * n * τ)) =
      fun n : ℕ ↦ ((thetaCount grossQ₁ n : ℂ) * cexp (2 * π * I * n * τ) -
        (thetaCount grossQ₂ n : ℂ) * cexp (2 * π * I * n * τ)) / 2 := by
    funext n
    rw [grossCoeff_cast]
    ring
  rw [hfun]
  exact h

theorem chi_eq_one (χ : DirichletCharacter ℂ (4 * 11))
    (hχ : ∀ d : ℕ, d.Coprime (4 * 11) → χ d = (jacobiSym (2 * grossH₁.det) d : ℂ)) : χ = 1 := by
  refine MulChar.ext fun a ↦ ?_
  have hc := ZMod.val_coe_unit_coprime a
  have hc2 : Nat.Coprime (a : ZMod (4 * 11)).val 2 :=
    Nat.Coprime.coprime_dvd_right (by norm_num) hc
  have hc88 : ((88 : ℤ)).gcd ((a : ZMod (4 * 11)).val : ℕ) = 1 := by
    have : Nat.Coprime (a : ZMod (4 * 11)).val (4 * 11 * 2) := Nat.Coprime.mul_right hc hc2
    rw [Int.gcd_eq_natAbs]
    simpa [Nat.coprime_comm] using this.symm
  have h1 := hχ _ hc
  rw [ZMod.natCast_zmod_val, det_grossH₁] at h1
  rw [h1, MulChar.one_apply a.isUnit]
  have : (2 * 3872 : ℤ) = 88 ^ 2 := by norm_num
  rw [this, jacobiSym.sq_one' hc88]
  simp

/-- **H5 instance: Gross's form is a cusp form of weight `3/2` in Kohnen's plus space of level `44`**
(trivial character, theta multiplier). -/
@[kb "gross1987" "Gross's weight 3/2 form (theta_1 - theta_2)/2 of level 11 lies in S^+_{3/2}(Gamma0(44)): same genus implies cuspidal"]
theorem grossForm_mem_plusCuspForms :
    (fun τ ↦ (thetaGram grossH₁ τ - thetaGram grossH₂ τ) / 2) ∈
      HalfIntegral.thetaMultiplierSystem.plusCuspForms 1 11 1 := by
  obtain ⟨χ, hχ, hmem⟩ := gramSameGenus_thetaGram_sub_mem_halfIntCuspForms (k := 1) (N := 11)
    isEvenGram_grossH₁ isEvenGram_grossH₂ (by norm_num) gramSameGenus_gross isGramLevel_grossH₁
    isGramLevel_grossH₂
  have hχ1 := chi_eq_one χ hχ
  subst hχ1
  have hcusp : (fun τ ↦ (thetaGram grossH₁ τ - thetaGram grossH₂ τ) / 2) ∈
      HalfIntegral.thetaMultiplierSystem.cuspForms 1 11 1 := by
    rw [HalfIntegral.thetaMultiplierSystem_cuspForms]
    have := Submodule.smul_mem _ (1 / 2 : ℂ) hmem
    convert this using 1
    funext τ
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨hcusp, fun n ↦ (grossCoeff n : ℂ), hasQExp_grossForm, ?_⟩
  intro n hn
  have : n % 4 = 1 ∨ n % 4 = 2 := by
    simp only [pow_one] at hn
    omega
  simp [grossCoeff_eq_zero_of_mod_four this]

end ModularFormsKB.ThetaGenus.Gross
