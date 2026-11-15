import ModularFormsKB.Miyake.HeckeTrick.Poles

/-!
# Miyake §7.2: Hecke's limit in weights two and one (Theorems 7.2.12, 7.2.13)

Miyake, *Modular Forms*, §7.2, p. 288. Miyake defines $E_2(z;\chi,\psi)$ and $E_1(z;\chi,\psi)$ as the value at
$s = 0$ of the continuation of $E_k(z,s;\chi,\psi)$ (Theorem 7.2.9). We prove the statements recorded in wave 2B,
`MiyakeTheorem7_2_12` and `MiyakeTheorem7_2_13` (`Miyake/Wave2B/HeckeTrick.lean`), from the Fourier expansion
`eisensteinCharSCont` of Theorem 7.2.9 (wave 3):

* at $s = 0$ the factor $B(s)$ has the zero $\Gamma(0)^{-1}$, so the antiholomorphic series drops out;
* $\omega(x;\alpha,0) = 1$ (Lemma 7.2.6, `omega_zero`), so the first series is the $q$-series of the theorem;
* the term $D(s)y^{1-k-2s}$ needs care where Lean's formula has a removable singularity at $s = 0$:
  for $k = 2$ and $\chi$ trivial, $\Gamma(s)^{-1}L_L(2s+1,\chi) = \Gamma(s+1)^{-1}\,\tfrac12(2s)L_L(2s+1,\chi)$ tends
  to $\tfrac12\prod_{p\mid L}(1-p^{-1})$; for $k = 1$ the factor $\Gamma(s)^{-1}\Gamma(s)$ is $1$.

So the continuation used for `IsHeckeLimit` is written with these cancellations made (`heckeLimitFun`); it agrees
with the series (7.2.1) on $k + 2\operatorname{Re}s > 2$ and is holomorphic on $\operatorname{Re}s > -1/2$.
-/

open MeasureTheory Set Filter Topology Complex
open scoped UpperHalfPlane
open scoped Real

noncomputable section

namespace ModularFormsKB.Miyake.HeckeTrick

open ModularFormsKB.Miyake.Wave2B

variable {L M : ℕ}

open scoped Classical

lemma trivChar_apply_neg_one {N : ℕ} [NeZero N] : (1 : DirichletCharacter ℂ N) (-1) = 1 :=
  MulChar.one_apply isUnit_one.neg

lemma heckeB_zero (k : ℤ) [NeZero M] (ψ : DirichletCharacter ℂ M) : heckeB k ψ 0 = 0 := by
  simp [heckeB, Complex.Gamma_zero]

lemma omega_arg_re_pos [NeZero M] (z : ℍ) (n : ℕ+) :
    0 < (((4 * π * z.im * (n : ℕ) / M : ℝ)) : ℂ).re := by
  have hM : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  rw [Complex.ofReal_re]
  have := z.im_pos
  positivity

lemma heckeTermA_zero (k : ℤ) [NeZero M] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (z : ℍ) (n : ℕ+) :
    heckeTermA k χ ψ z 0 n = heckeCoeff k χ ψ 0 n * cexp (2 * π * I * (n : ℕ) * z / M) := by
  unfold heckeTermA
  rw [omega_zero (omega_arg_re_pos z n)]
  simp

/-- At $s = 0$ the two Fourier series parts reduce to $A(0)\sum_n a_n(0)e^{2\pi inz/M}$. -/
lemma heckeRest_zero (k : ℤ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (z : ℍ) :
    heckeRest k χ ψ z 0 =
      heckeA k ψ 0 * ∑' n : ℕ+, heckeCoeff k χ ψ 0 n * cexp (2 * π * I * (n : ℕ) * z / M) := by
  unfold heckeRest
  rw [heckeB_zero]
  simp only [neg_zero, Complex.cpow_zero, mul_one, zero_mul, add_zero]
  congr 1
  exact tsum_congr fun n ↦ heckeTermA_zero k χ ψ z n

lemma summable_heckeTermA_zero (k : ℤ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (z : ℍ) :
    Summable fun n : ℕ+ ↦ heckeCoeff k χ ψ 0 n * cexp (2 * π * I * (n : ℕ) * z / M) := by
  obtain ⟨u, hu, hb⟩ := heckeTerm_uniform k χ ψ z (isCompact_singleton (x := (0 : ℂ)))
  refine hu.of_norm_bounded fun n ↦ ?_
  rw [← heckeTermA_zero]
  exact (hb 0 rfl n).1

lemma heckeCoeff_two_zero (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (n : ℕ) :
    heckeCoeff 2 χ ψ 0 n = eisensteinCharCoeff 2 χ ψ n := by
  unfold heckeCoeff eisensteinCharCoeff
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  congr 2
  rw [show ((2 : ℤ) : ℂ) + 2 * 0 - 1 = ((1 : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast]

lemma heckeCoeff_one_zero (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (n : ℕ) :
    heckeCoeff 1 χ ψ 0 n = eisensteinCharCoeff 1 χ ψ n := by
  unfold heckeCoeff eisensteinCharCoeff
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  congr 2
  rw [show ((1 : ℤ) : ℂ) + 2 * 0 - 1 = ((0 : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast]

lemma Gamma_one_half_eq_sqrt : Gamma (1 / 2) = (Real.sqrt π : ℂ) := by
  have := Complex.Gamma_ofReal (1 / 2 : ℝ)
  rw [Real.Gamma_one_half_eq] at this
  push_cast at this
  exact this

lemma Gamma_inv_two_eq_sqrt : Gamma 2⁻¹ = (Real.sqrt π : ℂ) := by
  rw [← Gamma_one_half_eq_sqrt, one_div]

lemma Gamma_two' : Gamma 2 = 1 := by
  rw [show (2 : ℂ) = 1 + 1 by norm_num, Complex.Gamma_add_one _ one_ne_zero, Complex.Gamma_one, mul_one]

lemma heckeA_two_zero [NeZero M] (ψ : DirichletCharacter ℂ M) : heckeA 2 ψ 0 = eisensteinCharA 2 ψ := by
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  unfold heckeA eisensteinCharA
  rw [show (0 : ℂ) + ((2 : ℤ) : ℂ) = ((2 : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast,
    show ((2 : ℕ) : ℂ) = 1 + 1 by norm_num, Complex.Gamma_add_one _ one_ne_zero, Complex.Gamma_one]
  push_cast
  simp only [zpow_neg, zpow_ofNat]
  field_simp
  have hI4 : I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, I_sq]; norm_num
  rw [hI4]
  simp

lemma heckeA_one_zero [NeZero M] (ψ : DirichletCharacter ℂ M) : heckeA 1 ψ 0 = eisensteinCharA 1 ψ := by
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  unfold heckeA eisensteinCharA
  rw [show (0 : ℂ) + ((1 : ℤ) : ℂ) = 1 by push_cast; ring, Complex.cpow_one, Complex.Gamma_one]
  push_cast
  simp only [zpow_neg, zpow_one, Nat.factorial, Nat.cast_one, pow_one]
  rw [Complex.inv_I]
  field_simp

/-! ### Weight two -/

/-- The factor $D^\ast(s)$ of weight two: $D(s)$ of Theorem 7.2.9 with $\Gamma(s)^{-1}L_L(2s+1,\chi)$ replaced by
$\Gamma(s+1)^{-1}\cdot\tfrac12(2s)L_L(2s+1,\chi)$ when $\chi$ is trivial (the same value for $\operatorname{Re}s > 0$). -/
def heckeDTwo [NeZero L] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (s : ℂ) : ℂ :=
  if ψ = 1 then
    2 * (Real.sqrt π : ℂ) * I ^ (-(2 : ℤ)) * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹)) *
      (Gamma (s + 2))⁻¹ * Gamma ((2 * s + 1) / 2) * Gamma (s + 1) *
      (if χ = 1 then (Gamma (s + 1))⁻¹ * DirichletCharacter.LFunctionTrivChar₁ L (2 * s + 1) / 2
        else (Gamma s)⁻¹ * DirichletCharacter.LFunction χ (2 * s + 1))
  else 0

/-- The continuation of $E_2(z,s;\chi,\psi)$ with the removable singularity at $s = 0$ cancelled:
$C(s) + D^\ast(s)y^{-1-2s} + (\text{Fourier series})$. -/
def heckeLimitTwo [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (z : ℍ)
    (s : ℂ) : ℂ :=
  heckeC 2 L ψ s + heckeDTwo χ ψ s * (z.im : ℂ) ^ (-1 - 2 * s) + heckeRest 2 χ ψ z s

lemma differentiableAt_heckeDTwo [NeZero L] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) {s : ℂ}
    (hs : -1 / 2 < s.re) : DifferentiableAt ℂ (heckeDTwo χ ψ) s := by
  have g1 : DifferentiableAt ℂ (fun s : ℂ ↦ Gamma ((2 * s + 1) / 2)) s :=
    diffAt_comp' (w := fun s ↦ (2 * s + 1) / 2)
      (differentiableAt_gamma_of_re_pos (by simp [Complex.div_ofNat_re]; linarith)) (by fun_prop)
  have g2 : DifferentiableAt ℂ (fun s : ℂ ↦ Gamma (s + 1)) s :=
    diffAt_comp' (w := fun s ↦ s + 1) (differentiableAt_gamma_of_re_pos (by simp; linarith))
      (by fun_prop)
  have g3 : DifferentiableAt ℂ (fun s : ℂ ↦ (Gamma (s + 2))⁻¹) s :=
    (Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const (2 : ℂ))) s
  have g4 : DifferentiableAt ℂ (fun s : ℂ ↦ (Gamma (s + 1))⁻¹) s :=
    (Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const (1 : ℂ))) s
  unfold heckeDTwo
  by_cases hψ : ψ = 1
  · simp only [hψ, ite_true]
    by_cases hχ : χ = 1
    · simp only [hχ, ite_true]
      exact ((((differentiableAt_const _).mul g3).mul g1).mul g2).mul
        ((g4.mul (((DirichletCharacter.differentiable_LFunctionTrivChar₁ L).comp
          (by fun_prop : Differentiable ℂ fun s : ℂ ↦ 2 * s + 1)) s)).div_const 2)
    · simp only [hχ, ite_false]
      exact ((((differentiableAt_const _).mul g3).mul g1).mul g2).mul
        ((Complex.differentiable_one_div_Gamma s).mul
          (((DirichletCharacter.differentiable_LFunction hχ).comp
            (by fun_prop : Differentiable ℂ fun s : ℂ ↦ 2 * s + 1)) s))
  · simp only [hψ, ite_false]
    exact differentiableAt_const _

lemma differentiableOn_heckeLimitTwo [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (z : ℍ) :
    DifferentiableOn ℂ (heckeLimitTwo χ ψ z) {s | -1 / 2 < s.re} := by
  intro s hs
  have hs' : -1 / 2 < s.re := hs
  refine DifferentiableAt.differentiableWithinAt ?_
  have gC : DifferentiableAt ℂ (heckeC 2 L ψ) s := by
    refine differentiableAt_heckeC 2 L ψ (Or.inl fun h ↦ ?_)
    have := congrArg Complex.re h
    simp at this
    linarith
  have g5 : DifferentiableAt ℂ (fun s : ℂ ↦ (z.im : ℂ) ^ (-1 - 2 * s)) s :=
    (differentiable_cpow_im z (fun s ↦ -1 - 2 * s) (by fun_prop)) s
  exact (gC.add ((differentiableAt_heckeDTwo χ ψ hs').mul g5)).add (differentiable_heckeRest 2 χ ψ z s)

lemma heckeD_two_eq [NeZero L] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) {s : ℂ}
    (hre : 0 < s.re) : heckeD 2 χ ψ s = heckeDTwo χ ψ s := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hre
  unfold heckeD heckeDTwo
  by_cases hψ : ψ = 1
  · simp only [hψ, ite_true]
    have h1 : (2 * s + ((2 : ℤ) : ℂ) - 1) / 2 = (2 * s + 1) / 2 := by push_cast; ring
    have h2 : (2 * s + ((2 : ℤ) : ℂ)) / 2 = s + 1 := by push_cast; ring
    have h3 : 2 * s + ((2 : ℤ) : ℂ) - 1 = 2 * s + 1 := by push_cast; ring
    have h4 : s + ((2 : ℤ) : ℂ) = s + 2 := by push_cast; ring
    rw [h1, h2, h3, h4]
    by_cases hχ : χ = 1
    · simp only [hχ, ite_true]
      have hw : (2 * s + 1 : ℂ) ≠ 1 := by
        intro h; apply hs0; linear_combination h / 2
      have hup : DirichletCharacter.LFunctionTrivChar₁ L (2 * s + 1) =
          (2 * s + 1 - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ L) (2 * s + 1) := by
        simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hw,
          DirichletCharacter.LFunctionTrivChar]
      rw [hup, Complex.Gamma_add_one s hs0]
      have hG : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre
      field_simp
      ring
    · simp only [hχ, ite_false]
      ring
  · simp [hψ]

lemma heckeLimitTwo_eq [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (hpar : χ (-1) * ψ (-1) = 1) (z : ℍ) {s : ℂ} (hs : 2 < ((2 : ℤ) : ℝ) + 2 * s.re) :
    heckeLimitTwo χ ψ z s = eisensteinCharS 2 s χ ψ z := by
  have hpar' : χ (-1) * ψ (-1) = (-1) ^ (2 : ℤ) := by rw [hpar]; norm_num
  have hre : 0 < s.re := by push_cast at hs; linarith
  have hexp : (1 : ℂ) - ((2 : ℤ) : ℂ) - 2 * s = -1 - 2 * s := by push_cast; ring
  rw [eisensteinCharS_eq_cont 2 χ ψ hpar' z hs, eisensteinCharSCont_eq, heckeLimitTwo,
    heckeD_two_eq χ ψ hre, hexp]

lemma heckeC_two_zero [NeZero M] (ψ : DirichletCharacter ℂ M) :
    heckeC 2 L ψ 0 = eisensteinCharConst 2 (L := L) ψ := by
  unfold heckeC eisensteinCharConst
  split_ifs with hL
  · congr 1
    have := (hasSum_pnat_L (L := M) (s := 2) (by norm_num) ψ).tsum_eq
    rw [show (2 : ℂ) * 0 + ((2 : ℤ) : ℂ) = 2 by push_cast; ring, ← this]
    refine tsum_congr fun n ↦ ?_
    congr 1
    rw [show (-(2 : ℂ)) = (((-(2 : ℤ)) : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
    norm_num
  · rfl

lemma heckeDTwo_zero [NeZero L] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) :
    heckeDTwo χ ψ 0 = if χ = 1 ∧ ψ = 1 then -π * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹)) *
        ∏ p ∈ L.primeFactors, (1 - (p : ℂ)⁻¹) else 0 := by
  unfold heckeDTwo
  by_cases hψ : ψ = 1
  · by_cases hχ : χ = 1
    · simp only [hψ, hχ, and_self, ite_true]
      have hsq : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = (π : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
      simp only [mul_zero, zero_add, Complex.Gamma_one, inv_one, one_mul, mul_one, Gamma_two',
        Gamma_one_half_eq_sqrt]
      simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_self]
      simp only [zpow_neg, zpow_ofNat, I_sq]
      linear_combination (-(∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹)) *
        ∏ p ∈ L.primeFactors, (1 - (p : ℂ)⁻¹)) * hsq
    · simp [hψ, hχ, Complex.Gamma_zero]
  · simp [hψ]

lemma heckeLimitTwo_zero [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (z : ℍ) :
    heckeLimitTwo χ ψ z 0 = eisensteinCharConst 2 (L := L) ψ +
      (if χ = 1 ∧ ψ = 1 then -π * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹)) *
        ∏ p ∈ L.primeFactors, (1 - (p : ℂ)⁻¹) else 0) / (z.im : ℂ) +
      eisensteinCharA 2 ψ * ∑' n : ℕ+, eisensteinCharCoeff 2 χ ψ n *
        cexp (2 * π * I * (n : ℕ) * z / M) := by
  have hexp : (z.im : ℂ) ^ (-1 - 2 * (0 : ℂ)) = (z.im : ℂ)⁻¹ := by
    rw [show (-1 - 2 * (0 : ℂ)) = -1 by ring, Complex.cpow_neg_one]
  rw [heckeLimitTwo, heckeRest_zero, heckeA_two_zero, heckeC_two_zero, heckeDTwo_zero, hexp,
    div_eq_mul_inv]
  simp_rw [heckeCoeff_two_zero]

open scoped Classical in
/-- **Miyake, Theorem 7.2.12.** If $\chi(-1)\psi(-1) = 1$, Hecke's limit $E_2(z;\chi,\psi)$ exists and equals
$C + Dy^{-1} + A\sum_{n\ge1}a_ne^{2\pi inz/M}$, with $D = -\pi\prod_{p\mid M}(1-p^{-1})\prod_{p\mid L}(1-p^{-1})$ when
$\chi$ and $\psi$ are both principal and $D = 0$ otherwise. -/
@[kb "miyake1989" "Theorem 7.2.12, p. 288"]
theorem miyakeTheorem7_2_12 : MiyakeTheorem7_2_12 := by
  intro L M _ _ χ ψ hpar z
  refine ⟨heckeLimitTwo χ ψ z 0, ⟨1 / 2, by norm_num, heckeLimitTwo χ ψ z,
    (differentiableOn_heckeLimitTwo χ ψ z).mono ?_, fun s hs ↦ heckeLimitTwo_eq χ ψ hpar z hs, rfl⟩, ?_⟩
  · rintro s (hs | hs)
    · have h2 : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
      rw [Metric.mem_ball, dist_zero_right] at hs
      show -1 / 2 < s.re
      linarith [neg_abs_le s.re]
    · show -1 / 2 < s.re
      have : 0 < s.re := hs
      linarith
  · rw [heckeLimitTwo_zero]
    have h := (summable_heckeTermA_zero 2 χ ψ z).hasSum.mul_left (eisensteinCharA 2 ψ)
    simp_rw [heckeCoeff_two_zero] at h
    convert h using 1
    · funext n; ring
    · ring

/-! ### Weight one -/

/-- The factor $D^\ast(s)$ of weight one: $D(s)$ of Theorem 7.2.9 with $\Gamma(s)^{-1}\Gamma(s)$ cancelled. -/
def heckeDOne [NeZero L] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (s : ℂ) : ℂ :=
  if ψ = 1 then
    2 * (Real.sqrt π : ℂ) * I ^ (-(1 : ℤ)) * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹)) *
      (Gamma (s + 1))⁻¹ * Gamma ((2 * s + 1) / 2) * DirichletCharacter.LFunction χ (2 * s)
  else 0

/-- The continuation of $E_1(z,s;\chi,\psi)$ with the factor $\Gamma(s)^{-1}\Gamma(s)$ of $D(s)$ cancelled. -/
def heckeLimitOne [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (z : ℍ)
    (s : ℂ) : ℂ :=
  heckeC 1 L ψ s + heckeDOne χ ψ s * (z.im : ℂ) ^ (-2 * s) + heckeRest 1 χ ψ z s

lemma differentiableOn_heckeLimitOne [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (hpar : χ (-1) * ψ (-1) = -1) (z : ℍ) :
    DifferentiableOn ℂ (heckeLimitOne χ ψ z) {s | -1 / 2 < s.re} := by
  intro s hs
  have hs' : -1 / 2 < s.re := hs
  refine DifferentiableAt.differentiableWithinAt ?_
  have gC : DifferentiableAt ℂ (heckeC 1 L ψ) s := by
    by_cases hψ : ψ = 1
    · refine differentiableAt_heckeC 1 L ψ (Or.inr (Or.inr ?_))
      rintro rfl
      have h2 : χ (-1) = 1 := by
        have : (-1 : ZMod 1) = 1 := Subsingleton.elim _ _
        rw [this, map_one]
      rw [h2, hψ, trivChar_apply_neg_one] at hpar
      norm_num at hpar
    · exact differentiableAt_heckeC 1 L ψ (Or.inr (Or.inl hψ))
  have g1 : DifferentiableAt ℂ (fun s : ℂ ↦ Gamma ((2 * s + 1) / 2)) s :=
    diffAt_comp' (w := fun s ↦ (2 * s + 1) / 2)
      (differentiableAt_gamma_of_re_pos (by simp [Complex.div_ofNat_re]; linarith)) (by fun_prop)
  have g4 : DifferentiableAt ℂ (fun s : ℂ ↦ (Gamma (s + 1))⁻¹) s :=
    (Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const (1 : ℂ))) s
  have g5 : DifferentiableAt ℂ (fun s : ℂ ↦ (z.im : ℂ) ^ (-2 * s)) s :=
    (differentiable_cpow_im z (fun s ↦ -2 * s) (by fun_prop)) s
  have gD : DifferentiableAt ℂ (heckeDOne χ ψ) s := by
    unfold heckeDOne
    by_cases hψ : ψ = 1
    · simp only [hψ, ite_true]
      have hχ : χ ≠ 1 := by
        rintro rfl
        rw [hψ, trivChar_apply_neg_one, trivChar_apply_neg_one] at hpar
        norm_num at hpar
      exact ((((differentiableAt_const _).mul g4).mul g1).mul
        (((DirichletCharacter.differentiable_LFunction hχ).comp
          (by fun_prop : Differentiable ℂ fun s : ℂ ↦ 2 * s)) s))
    · simp only [hψ, ite_false]
      exact differentiableAt_const _
  exact (gC.add (gD.mul g5)).add (differentiable_heckeRest 1 χ ψ z s)

lemma heckeD_one_eq' [NeZero L] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) {s : ℂ}
    (hre : 0 < s.re) : heckeD 1 χ ψ s = heckeDOne χ ψ s := by
  unfold heckeD heckeDOne
  by_cases hψ : ψ = 1
  · simp only [hψ, ite_true]
    have h1 : (2 * s + ((1 : ℤ) : ℂ) - 1) / 2 = s := by push_cast; ring
    have h2 : (2 * s + ((1 : ℤ) : ℂ)) / 2 = (2 * s + 1) / 2 := by push_cast; ring
    have h3 : 2 * s + ((1 : ℤ) : ℂ) - 1 = 2 * s := by push_cast; ring
    have h4 : s + ((1 : ℤ) : ℂ) = s + 1 := by push_cast; ring
    rw [h1, h2, h3, h4]
    have hG : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre
    field_simp
  · simp [hψ]

lemma heckeLimitOne_eq [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (hpar : χ (-1) * ψ (-1) = -1) (z : ℍ) {s : ℂ} (hs : 2 < ((1 : ℤ) : ℝ) + 2 * s.re) :
    heckeLimitOne χ ψ z s = eisensteinCharS 1 s χ ψ z := by
  have hpar' : χ (-1) * ψ (-1) = (-1) ^ (1 : ℤ) := by rw [hpar]; norm_num
  have hre : 0 < s.re := by push_cast at hs; linarith
  have hexp : (1 : ℂ) - ((1 : ℤ) : ℂ) - 2 * s = -2 * s := by push_cast; ring
  rw [eisensteinCharS_eq_cont 1 χ ψ hpar' z hs, eisensteinCharSCont_eq, heckeLimitOne,
    heckeD_one_eq' χ ψ hre, hexp]

lemma heckeDOne_zero [NeZero L] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) :
    heckeDOne χ ψ 0 = if ψ = 1 then -2 * π * I * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹)) *
        DirichletCharacter.LFunction χ 0 else 0 := by
  unfold heckeDOne
  by_cases hψ : ψ = 1
  · simp only [hψ, ite_true]
    have hsq : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = (π : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
    rw [show (0 : ℂ) + 1 = 1 by ring, Complex.Gamma_one, show (2 * (0 : ℂ) + 1) / 2 = 1 / 2 by ring,
      Gamma_one_half_eq_sqrt, show (2 : ℂ) * 0 = 0 by ring]
    simp only [zpow_neg, zpow_one, Complex.inv_I, inv_one]
    linear_combination (-(2 : ℂ) * I * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹)) *
      DirichletCharacter.LFunction χ 0) * hsq
  · simp [hψ]

lemma heckeLimitOne_zero [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (z : ℍ) :
    heckeLimitOne χ ψ z 0 = (if L = 1 then 2 * DirichletCharacter.LFunction ψ 1 else 0) +
      (if ψ = 1 then -2 * π * I * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹)) *
        DirichletCharacter.LFunction χ 0 else 0) +
      eisensteinCharA 1 ψ * ∑' n : ℕ+, eisensteinCharCoeff 1 χ ψ n *
        cexp (2 * π * I * (n : ℕ) * z / M) := by
  have hC : heckeC 1 L ψ 0 = if L = 1 then 2 * DirichletCharacter.LFunction ψ 1 else 0 := by
    unfold heckeC
    rw [show (2 : ℂ) * 0 + ((1 : ℤ) : ℂ) = 1 by push_cast; ring]
  rw [heckeLimitOne, heckeRest_zero, heckeA_one_zero, hC, heckeDOne_zero,
    show (-2 : ℂ) * 0 = 0 by ring, Complex.cpow_zero, mul_one]
  simp_rw [heckeCoeff_one_zero]

open scoped Classical in
/-- **Miyake, Theorem 7.2.13.** If $\chi(-1)\psi(-1) = -1$, Hecke's limit $E_1(z;\chi,\psi)$ exists and equals
$C + D + A\sum_{n\ge1}a_ne^{2\pi inz/M}$, with $C = 2L_M(1,\psi)$ if $\chi$ is the principal character mod $1$,
$D = -2\pi i\prod_{p\mid M}(1-p^{-1})L_L(0,\chi)$ if $\psi$ is principal (each $0$ otherwise). -/
@[kb "miyake1989" "Theorem 7.2.13, p. 288"]
theorem miyakeTheorem7_2_13 : MiyakeTheorem7_2_13 := by
  intro L M _ _ χ ψ hpar z
  refine ⟨heckeLimitOne χ ψ z 0, ⟨1 / 2, by norm_num, heckeLimitOne χ ψ z,
    (differentiableOn_heckeLimitOne χ ψ hpar z).mono ?_, fun s hs ↦ heckeLimitOne_eq χ ψ hpar z hs,
    rfl⟩, ?_⟩
  · rintro s (hs | hs)
    · have h2 : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
      rw [Metric.mem_ball, dist_zero_right] at hs
      show -1 / 2 < s.re
      linarith [neg_abs_le s.re]
    · show -1 / 2 < s.re
      have : 0 < s.re := hs
      linarith
  · rw [heckeLimitOne_zero]
    have h := (summable_heckeTermA_zero 1 χ ψ z).hasSum.mul_left (eisensteinCharA 1 ψ)
    simp_rw [heckeCoeff_one_zero] at h
    convert h using 1
    · funext n; ring
    · ring

end ModularFormsKB.Miyake.HeckeTrick
