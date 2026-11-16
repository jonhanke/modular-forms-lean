/-
# The root number of $E_{2m}$: `heckeCharacterRootNumber`

Proves the structure `HeckeCharacterRootNumber` of `RootNumber.lean`, i.e. the functional equation of $L(E_{2m}, s)$
for odd squarefree $m$ with conductor $64m^2$ and sign `congruentSign (2 * m)`, without Hecke characters, by repeating
the odd case (`congruentFE_odd`) for the newform $f_{64} = f_{32} \otimes \left(\frac 2\cdot\right)$ of level $64$:

* $f_{64}$ is a cusp form in $S_2(64, 1)$ (`isCuspFormChar_f64`, a theta series with a spherical weight, `F64Theta`);
* its Fricke eigenvalue is $-1$ (`fricke_f64`, `F64Fricke`);
* for odd squarefree $m$ the twist of $f_{64}$ by $\left(\frac\cdot m\right)$ has the coefficients of $L(E_{2m}, s)$,
  since $\left(\frac{2m}{d}\right) b(d) = \left(\frac 2d\right)\left(\frac md\right)b(d)$ and on the support of $b$
  ($d \equiv 1 \bmod 4$) $\left(\frac md\right) = \left(\frac dm\right)$ (`twist_jacobiChar_f64C`);
* Weil's constant of the twist at level $64$ is $\left(\frac{-64}{m}\right) = \left(\frac{-1}{m}\right)$, which is
  `congruentSign (2 * m)` (`weilConstant_jacobiChar64`);
* Miyake's Theorem 4.3.12 (`Miyake.twisted_completedL_cuspForm`) then gives the functional equation.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.RootNumber
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.F64Fricke

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open Complex
open scoped Real

theorem twist_jacobiChar_f64C {m : ℕ} [NeZero m] (hm : Odd m) (hsq : Squarefree (2 * m)) :
    Miyake.twist (jacobiChar m) f64C = lCoeff (2 * m) := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  rw [lCoeff_eq hsq]
  funext d
  simp only [Miyake.twist, f64C, congruentCoeff]
  by_cases hb : f32Coeff d = 0
  · simp [hb]
  have h4 := mod_four_eq_one_of_f32Coeff_ne_zero hb
  rw [jacobiChar_natCast hm, jacobiSym.quadratic_reciprocity_one_mod_four h4 hm]
  have e : jacobiSym ((2 * m : ℕ) : ℤ) d = jacobiSym 2 d * jacobiSym m d := by
    push_cast
    exact jacobiSym.mul_left 2 m d
  rw [e]
  push_cast
  ring

/-- $\left(\frac{-64}{m}\right) = \left(\frac{-1}{m}\right)$ is the predicted sign for $E_{2m}$, $m$ odd. -/
theorem jacobiSym_neg_sixtyFour {m : ℕ} (hm : Odd m) :
    (jacobiSym (-64) m : ℂ) = congruentSign (2 * m) := by
  have h64 : jacobiSym 64 m = 1 := by
    have : (64 : ℤ) = 8 ^ 2 := by norm_num
    rw [this]
    refine jacobiSym.sq_one' ?_
    have h2 : Nat.Coprime 8 m := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
      exact (Nat.coprime_two_right.mpr hm).symm.pow_left 3
    have h3 : Int.gcd ((8 : ℕ) : ℤ) ((m : ℕ) : ℤ) = 1 := by rw [Int.gcd_natCast_natCast]; exact h2
    exact_mod_cast h3
  have : (-64 : ℤ) = -1 * 64 := by norm_num
  rw [this, jacobiSym.mul_left, h64, mul_one, jacobiSym.at_neg_one hm, ZMod.χ₄_nat_eq_if_mod_four]
  have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h | h
  · have h8 : (2 * m) % 8 = 2 := by omega
    simp [congruentSign, h, h8, hm2]
  · have h8 : (2 * m) % 8 = 6 := by omega
    simp [congruentSign, h, h8, hm2]

/-- **Weil's constant of the twist by $\left(\frac\cdot m\right)$** at level $64$ is `congruentSign (2 * m)`. -/
theorem weilConstant_jacobiChar64 {m : ℕ} [NeZero m] (hm : Odd m) (hsq : Squarefree m) :
    Miyake.weilConstant (1 : DirichletCharacter ℂ 64) (jacobiChar m) = congruentSign (2 * m) := by
  have hW : Miyake.gaussW (jacobiChar m) ≠ 0 := Miyake.gaussW_ne_zero (isPrimitive_jacobiChar hm hsq)
  have hu : IsUnit ((m : ℕ) : ZMod 64) := by
    rw [ZMod.isUnit_iff_coprime, show (64 : ℕ) = 2 ^ 6 by norm_num]
    exact (Nat.coprime_two_right.mpr hm).pow_right 6
  unfold Miyake.weilConstant
  rw [jacobiChar_inv hm, MulChar.one_apply hu, one_mul, mul_div_assoc, div_self hW, mul_one,
    ← jacobiSym_neg_sixtyFour hm, ← jacobiChar_intCast hm]
  push_cast
  ring_nf

/-- $\sqrt{64 m^2} = m\sqrt{64}$. -/
theorem sqrt_sixtyFour_mul_sq (n : ℕ) : √((64 * n ^ 2 : ℕ) : ℝ) = n * √(64 : ℕ) := by
  push_cast
  rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity), mul_comm]

/-- **The functional equation of $L(E_{2m}, s)$, $m$ odd squarefree**, with conductor $64m^2$ and sign
$\left(\frac{-1}m\right)$ (Miyake Theorem 4.3.12 with the Fricke eigenvalue $-1$ of $f_{64}$). -/
theorem congruentFE_even {m : ℕ} [NeZero m] (hm : Odd m) (hsq : Squarefree m) :
    CongruentFE (2 * m) ((64 * m ^ 2 : ℕ) : ℝ) (congruentSign (2 * m)) := by
  have hψ := isPrimitive_jacobiChar hm hsq
  have hsq2 : Squarefree (2 * m) := by
    rw [Nat.squarefree_mul_iff]
    exact ⟨(Nat.coprime_two_left.mpr hm), Nat.prime_two.squarefree, hsq⟩
  have hcop : m.Coprime 64 := by
    rw [show (64 : ℕ) = 2 ^ 6 by norm_num]
    exact (Nat.coprime_two_right.mpr hm).pow_right 6
  have hb : Miyake.CoeffGrowth (fun k ↦ -f64C k) := by
    obtain ⟨ν, hν⟩ := coeffGrowth_f64C
    exact ⟨ν, hν.neg_left⟩
  obtain ⟨Φ, hΦd, -, σ₀, h1, h2⟩ := Miyake.twisted_completedL_cuspForm (k := 2) (N := 64) (m := m)
    two_pos (by norm_num) 1 (jacobiChar m) hψ hcop coeffGrowth_f64C hb isCuspFormChar_f64
    (fun z hz ↦ by simpa using fricke_f64 z hz)
  rw [jacobiChar_inv hm, weilConstant_jacobiChar64 hm hsq] at h2
  have htw : ∀ s : ℂ, Miyake.twistedCompletedL (64 : ℕ) (jacobiChar m) f64C s =
      Miyake.completedL ((64 * m ^ 2 : ℕ) : ℝ) (lCoeff (2 * m)) s := by
    intro s
    rw [Miyake.twistedCompletedL, Miyake.completedL, twist_jacobiChar_f64C hm hsq2,
      sqrt_sixtyFour_mul_sq]
  have htwneg : ∀ s : ℂ, Miyake.twistedCompletedL (64 : ℕ) (jacobiChar m) (fun k ↦ -f64C k) s =
      -Miyake.twistedCompletedL (64 : ℕ) (jacobiChar m) f64C s := by
    intro s
    have : Miyake.twist (jacobiChar m) (fun k ↦ -f64C k) = -Miyake.twist (jacobiChar m) f64C := by
      funext k; simp [Miyake.twist]
    rw [Miyake.twistedCompletedL, Miyake.twistedCompletedL, this, LSeries_neg]
    ring
  refine ⟨Φ, hΦd, ⟨σ₀, fun s hs ↦ by rw [h1 s (by exact_mod_cast hs), htw]⟩, fun s ↦ ?_⟩
  have hA : AnalyticOnNhd ℂ (fun s ↦ Φ (2 - s)) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (hΦd.comp (differentiable_const _ |>.sub differentiable_id))
  have hB : AnalyticOnNhd ℂ (fun s ↦ congruentSign (2 * m) * Φ s) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr ((differentiable_const _).mul hΦd)
  have heq : (fun s ↦ Φ (2 - s)) = fun s ↦ congruentSign (2 * m) * Φ s := by
    refine hA.eq_of_eventuallyEq hB (z₀ := ((σ₀ + 1 : ℝ) : ℂ)) ?_
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨{z : ℂ | σ₀ < z.re},
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp), fun z hz ↦ ?_⟩
    have hz' : (σ₀ : ℝ) < ((2 : ℕ) : ℝ) - (2 - z).re := by simp; exact hz
    simp only
    rw [h2 (2 - z) hz', show ((2 : ℕ) : ℂ) - (2 - z) = z by push_cast; ring, htwneg,
      h1 z (by exact_mod_cast hz)]
    simp [I_sq]
  exact congrFun heq s

/-- **The root number of $E_{2m}$** (Birch–Stephens, here proved): the named input `HeckeCharacterRootNumber` of
`RootNumber.lean` holds, by the twist of the level-$64$ newform $f_{64}$ (`congruentFE_even`). -/
theorem heckeCharacterRootNumber : HeckeCharacterRootNumber where
  fe m hm hsq := by
    have : NeZero m := ⟨hm.pos.ne'⟩
    have := congruentFE_even hm hsq
    push_cast at this
    exact this

/-- **`CongruentRootNumber` unconditionally**: $L(E_n, 1) = 0$ for squarefree $n \equiv 5, 6, 7 \bmod 8$. -/
theorem congruentRootNumber_proved : CongruentRootNumber :=
  congruentRootNumber heckeCharacterRootNumber

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
