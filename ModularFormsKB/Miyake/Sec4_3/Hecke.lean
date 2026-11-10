import ModularFormsKB.Miyake.Sec4_3.QSeries
import ModularFormsKB.Miyake.Sec4_3.Strip
import ModularFormsKB.Miyake.Sec4_3.HeckeCore
import ModularFormsKB.Miyake.Sec4_3.ModularQ
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# Miyake §4.3: Hecke's converse theorem

* `Miyake.hecke` (Theorem 4.3.5): for real $k, N > 0$,
  $g(z) = (-i\sqrt N z)^{-k} f(-1/(Nz))$ holds iff condition (B) holds.
* `Miyake.hecke_fricke` (Theorem 4.3.6): the same with $g = f|_k\omega_N$ and root number $i^k$.
* `Miyake.levelOne_converse`, `Miyake.levelOne_converse_cusp` (Theorem 4.3.8): level one.
-/

open Complex Filter Asymptotics CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm

noncomputable section

namespace Miyake

/-- **Hecke's theorem** (Miyake Theorem 4.3.5). Let $f(z) = \sum a_n e^{2\pi i n z}$ and
$g(z) = \sum b_n e^{2\pi i n z}$ with $a_n, b_n = O(n^\nu)$ (condition (4.3.7)), and let $k, N > 0$ be
real. Then
$$\text{(A)}\quad g(z) = (-i\sqrt N z)^{-k} f(-1/(Nz)) \quad (z \in \mathbb H)$$
holds if and only if (B): $\Lambda_N(s;f)$ and $\Lambda_N(s;g)$ continue to the whole plane, satisfy
$\Lambda_N(s;f) = \Lambda_N(k-s;g)$, and $\Lambda_N(s;f) + a_0/s + b_0/(k-s)$ is entire and bounded on
vertical strips (`Miyake.HeckeCondition` with $C = 1$). The power is the principal branch
($-i\sqrt N z$ has positive real part). Relation: same. -/
@[kb "miyake1989" "§4.3, Theorem 4.3.5 (Hecke), p. 119"]
theorem hecke {k N : ℝ} (hk : 0 < k) (hN : 0 < N) {a b : ℕ → ℂ}
    (ha : CoeffGrowth a) (hb : CoeffGrowth b) :
    (∀ z : ℂ, 0 < z.im →
      qSeries b z = (-I * (√N : ℂ) * z) ^ (-(k : ℂ)) * qSeries a (-1 / (N * z))) ↔
    HeckeCondition k N 1 a b :=
  ⟨hecke_B_of_A hk hN ha hb, hecke_A_of_B hk hN ha hb⟩

lemma qSeries_const_mul (C : ℂ) (b : ℕ → ℂ) (z : ℂ) :
    qSeries (fun n ↦ C * b n) z = C * qSeries b z := by
  simp only [qSeries, mul_assoc, tsum_mul_left]

lemma completedL_const_mul (N : ℝ) (C : ℂ) (b : ℕ → ℂ) (s : ℂ) :
    completedL N (fun n ↦ C * b n) s = C * completedL N b s := by
  have : (fun n ↦ C * b n) = C • b := rfl
  simp only [completedL, this, LSeries_smul]
  ring

/-- A root number can be absorbed into the second coefficient sequence. -/
lemma heckeCondition_iff_one (k N : ℝ) (C : ℂ) (a b : ℕ → ℂ) :
    HeckeCondition k N C a b ↔ HeckeCondition k N 1 a (fun n ↦ C * b n) := by
  simp only [HeckeCondition, completedL_const_mul, one_mul]

/-- $(-iw)^{-k} = i^k w^{-k}$ for a natural number $k$. -/
lemma neg_I_mul_cpow_neg_nat (k : ℕ) (w : ℂ) :
    (-I * w) ^ (-(k : ℂ)) = I ^ k * w ^ (-(k : ℤ)) := by
  rw [cpow_neg, cpow_natCast, mul_pow, mul_inv, zpow_neg, zpow_natCast]
  congr 1
  exact inv_eq_of_mul_eq_one_right (by rw [← mul_pow, neg_mul, I_mul_I, neg_neg, one_pow])

/-- **Hecke's theorem, slash form** (Miyake Theorem 4.3.6). For positive integers $k, N$ and
$f, g$ as in Theorem 4.3.5: $g = f|_k\omega_N$, i.e. $g(z) = (\sqrt N z)^{-k} f(-1/(Nz))$, holds iff
$\Lambda_N(s;f)$, $\Lambda_N(s;g)$ continue to the whole plane with
$\Lambda_N(s;f) = i^k\Lambda_N(k-s;g)$ and $\Lambda_N(s;f) + a_0/s + i^k b_0/(k-s)$ entire and bounded
on vertical strips (`Miyake.HeckeCondition` with $C = i^k$). Relation: same. -/
@[kb "miyake1989" "§4.3, Theorem 4.3.6, p. 122"]
theorem hecke_fricke {k N : ℕ} (hk : 0 < k) (hN : 0 < N) {a b : ℕ → ℂ}
    (ha : CoeffGrowth a) (hb : CoeffGrowth b) :
    (∀ z : ℂ, 0 < z.im → qSeries b z = fricke k N (qSeries a) z) ↔
    HeckeCondition k N (I ^ k) a b := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [heckeCondition_iff_one, ← hecke hk' hN' ha (hb.const_mul _)]
  have hIk : (I : ℂ) ^ k ≠ 0 := pow_ne_zero _ I_ne_zero
  refine forall_congr' fun z ↦ imp_congr_right fun _ ↦ ?_
  rw [qSeries_const_mul, mul_assoc, ofReal_natCast, neg_I_mul_cpow_neg_nat, mul_assoc, fricke]
  push_cast
  exact (mul_right_inj' hIk).symm

/-- $j(\gamma, w) = cw + d$ for $\gamma \in \mathrm{SL}_2(\mathbb Z)$ acting through $\mathrm{GL}_2(\mathbb R)$. -/
lemma denom_SL_eq (γ : SL(2, ℤ)) (w : ℂ) :
    denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map
      (Int.castRingHom ℝ)) γ)) w = ((γ 1 0 : ℤ) : ℂ) * w + ((γ 1 1 : ℤ) : ℂ) := by
  simp [denom]

/-- For a $q$-series, the Fricke relation in level one, $f(z) = z^{-k} f(-1/z)$, is invariance
under $S$. -/
lemma fricke_one_iff_slash_S (k : ℕ) (a : ℕ → ℂ) :
    (∀ z : ℂ, 0 < z.im → qSeries a z = fricke k 1 (qSeries a) z) ↔
      (fun τ : ℍ ↦ qSeries a τ) ∣[(k : ℤ)] ModularGroup.S = fun τ : ℍ ↦ qSeries a τ := by
  constructor
  · intro h
    ext τ
    rw [SlashInvariantForm.slash_S_apply, h τ τ.im_pos, fricke]
    simp only [Real.sqrt_one, ofReal_one, one_mul, neg_div, one_div, inv_neg]
    ring
  · intro h z hz
    have := congrFun h ⟨z, hz⟩
    rw [SlashInvariantForm.slash_S_apply] at this
    rw [fricke, ← this]
    simp only [Real.sqrt_one, ofReal_one, one_mul, neg_div, one_div, inv_neg]
    ring

/-- A $q$-series with coefficients of polynomial growth that is invariant under $S$ is a modular
form for $\mathrm{SL}_2(\mathbb Z)$ (cusp form if $a_0 = 0$). -/
lemma slash_SL2Z_of_slash_S {k : ℤ} {a : ℕ → ℂ}
    (hS : (fun τ : ℍ ↦ qSeries a τ) ∣[k] ModularGroup.S = fun τ : ℍ ↦ qSeries a τ) :
    ∀ γ : SL(2, ℤ), (fun τ : ℍ ↦ qSeries a τ) ∣[k] γ = fun τ : ℍ ↦ qSeries a τ := by
  refine SlashInvariantForm.slash_action_generators_SL2Z hS ?_
  ext τ
  have hden : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map
      (Int.castRingHom ℝ)) ModularGroup.T)) (τ : ℂ) = 1 := by
    rw [denom_SL_eq]; simp [ModularGroup.T]
  rw [ModularForm.SL_slash_apply, hden, modular_T_smul]
  simp [qSeries_add_one, add_comm]

lemma exists_modularForm_levelOne {k : ℤ} {a : ℕ → ℂ} (ha : CoeffGrowth a)
    (hS : (fun τ : ℍ ↦ qSeries a τ) ∣[k] ModularGroup.S = fun τ : ℍ ↦ qSeries a τ) :
    ∃ F : ModularForm 𝒮ℒ k, ∀ τ : ℍ, F τ = qSeries a τ := by
  have hall := slash_SL2Z_of_slash_S hS
  refine ⟨{ toFun := fun τ : ℍ ↦ qSeries a τ
            slash_action_eq' := fun γ hγ ↦ ?_
            holo' := mdifferentiable_qSeries ha
            bdd_at_cusps' := fun hc ↦ ?_ }, fun τ ↦ rfl⟩
  · obtain ⟨g, rfl⟩ := hγ
    exact hall g
  · refine (OnePoint.isBoundedAt_iff_forall_SL2Z hc).2 fun γ _ ↦ ?_
    rw [hall γ]
    exact isBoundedAtImInfty_qSeries ha

lemma exists_cuspForm_levelOne {k : ℤ} {a : ℕ → ℂ} (ha : CoeffGrowth a) (h0 : a 0 = 0)
    (hS : (fun τ : ℍ ↦ qSeries a τ) ∣[k] ModularGroup.S = fun τ : ℍ ↦ qSeries a τ) :
    ∃ F : CuspForm 𝒮ℒ k, ∀ τ : ℍ, F τ = qSeries a τ := by
  have hall := slash_SL2Z_of_slash_S hS
  refine ⟨{ toFun := fun τ : ℍ ↦ qSeries a τ
            slash_action_eq' := fun γ hγ ↦ ?_
            holo' := mdifferentiable_qSeries ha
            zero_at_cusps' := fun hc ↦ ?_ }, fun τ ↦ rfl⟩
  · obtain ⟨g, rfl⟩ := hγ
    exact hall g
  · refine (OnePoint.isZeroAt_iff_forall_SL2Z hc).2 fun γ _ ↦ ?_
    rw [hall γ]
    exact isZeroAtImInfty_qSeries ha h0

lemma I_pow_even {k : ℕ} (hk : Even k) : (I : ℂ) ^ k = (-1) ^ (k / 2) := by
  obtain ⟨m, rfl⟩ := hk
  rw [← two_mul, pow_mul, I_sq, Nat.mul_div_cancel_left _ two_pos]

/-- **Hecke's converse theorem in level one** (Miyake Theorem 4.3.8). Let $k \ge 2$ be even and
$f(z) = \sum a_n e^{2\pi i n z}$ with $a_n = O(n^\nu)$. Then $f \in M_k(\mathrm{SL}_2(\mathbb Z))$ iff
$\Lambda(s;f) = (2\pi)^{-s}\Gamma(s)L(s;f)$ continues to the whole plane,
$\Lambda(s;f) + a_0/s + (-1)^{k/2}a_0/(k-s)$ is entire and bounded on vertical strips, and
$\Lambda(s;f) = (-1)^{k/2}\Lambda(k-s;f)$ (`Miyake.HeckeCondition` with $N = 1$, $g = f$,
$C = (-1)^{k/2}$). Relation: same. -/
@[kb "miyake1989" "§4.3, Theorem 4.3.8, p. 122"]
theorem levelOne_converse {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) {a : ℕ → ℂ} (ha : CoeffGrowth a) :
    (∃ F : ModularForm 𝒮ℒ k, ∀ τ : ℍ, F τ = qSeries a τ) ↔
    HeckeCondition k 1 ((-1) ^ (k / 2)) a a := by
  have H := hecke_fricke (k := k) (N := 1) (by omega) one_pos ha ha
  rw [Nat.cast_one] at H
  rw [← I_pow_even hk, ← H]
  rw [fricke_one_iff_slash_S]
  constructor
  · rintro ⟨F, hF⟩
    have hfun : (fun τ : ℍ ↦ qSeries a τ) = ⇑F := funext fun τ ↦ (hF τ).symm
    rw [hfun]
    exact SlashInvariantForm.slash_action_eqn F _ ⟨ModularGroup.S, rfl⟩
  · exact exists_modularForm_levelOne ha

/-- **Miyake Theorem 4.3.8, last sentence**: under the conditions of the theorem, if moreover
$a_0 = 0$ then $f$ is a cusp form. Relation: same. -/
@[kb "miyake1989" "§4.3, Theorem 4.3.8, p. 123"]
theorem levelOne_converse_cusp {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) {a : ℕ → ℂ}
    (ha : CoeffGrowth a) (h0 : a 0 = 0) (hB : HeckeCondition k 1 ((-1) ^ (k / 2)) a a) :
    ∃ F : CuspForm 𝒮ℒ k, ∀ τ : ℍ, F τ = qSeries a τ := by
  have H := hecke_fricke (k := k) (N := 1) (by omega) one_pos ha ha
  rw [Nat.cast_one] at H
  rw [← I_pow_even hk, ← H] at hB
  rw [fricke_one_iff_slash_S] at hB
  exact exists_cuspForm_levelOne ha h0 hB

end Miyake
