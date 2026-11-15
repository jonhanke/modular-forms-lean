import ModularFormsKB.Miyake.GeneralizedBernoulli
import TauCeti.NumberTheory.DirichletCharacter.LValues

/-!
# Miyake, Theorem 3.3.4 for $k = 1$: $L(0,\chi) = -B_{1,\chi}$

Miyake, *Modular Forms* (Springer 1989), Theorem 3.3.4, p. 95. `LFunction_one_sub_nat` proves
$L(1-k,\chi) = -B_{k,\chi}/k$ for $k \ge 2$ from Mathlib's values of the Hurwitz zeta function at negative
integers; Mathlib lacks $\zeta(0, x) = \tfrac12 - x$, so $k = 1$ was open (LE-MF-0046, LE-MF-0161).

Here $k = 1$ is proved for every character in the case of the theorem, $k \equiv \delta_\chi \pmod 2$, i.e. $\chi$
odd and primitive (Miyake's hypothesis), and also for every even character (where both sides are $0$, except
$L(0,\chi_0) = -\tfrac12 = -B_{1,\chi_0}$ for the character mod $1$):

* `LFunction_zero_of_odd`: for primitive odd $\chi$ mod $m$, $L(0,\chi) = -B_{1,\chi}$, by Mathlib's functional
  equation `DirichletCharacter.IsPrimitive.completedLFunction_one_sub` (relating $L(0,\chi)$ to $L(1,\chi^{-1})$)
  and Tau Ceti's cotangent evaluation of $L(1,\chi^{-1})$ (`two_mul_LFunction_one_eq_sum_mul_cot`,
  `IsPrimitive.sum_inv_mul_pi_mul_cot`);
* `LFunction_zero_of_even`: for even $\chi$, $L(0,\chi) = -B_{1,\chi}$ (Mathlib's
  `ZMod.LFunction_apply_zero_of_even` and Tau Ceti's vanishing of $B_{1,\chi}$);
* `generalizedBernoulli_eq_tauCeti`: our $B_{n,\chi}$ is Tau Ceti's `DirichletCharacter.generalizedBernoulli`.
-/

open Complex
open scoped Real

namespace ModularFormsKB.Miyake

/-- Our $B_{n,\chi}$ (`generalizedBernoulli`, residues $1, \dots, m$) is Tau Ceti's
`DirichletCharacter.generalizedBernoulli` (residue classes mod $m$, with $0$ represented by $m$). -/
theorem generalizedBernoulli_eq_tauCeti {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (n : ℕ) :
    generalizedBernoulli χ n = χ.generalizedBernoulli n := by
  rw [DirichletCharacter.generalizedBernoulli_def, generalizedBernoulli]
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  congr 1
  · simp
  · symm
    refine Finset.sum_bij' (fun a _ ↦ if a = 0 then m else a.val) (fun a _ ↦ (a : ZMod m))
      (fun a _ ↦ ?_) (fun _ _ ↦ Finset.mem_univ _) (fun a _ ↦ ?_) (fun a ha ↦ ?_) (fun a _ ↦ ?_)
    · rw [Finset.mem_Icc]
      split_ifs with h
      · exact ⟨Nat.pos_of_ne_zero (NeZero.ne m), le_rfl⟩
      · exact ⟨Nat.pos_of_ne_zero fun h' ↦ h ((ZMod.val_eq_zero a).mp h'), (ZMod.val_lt a).le⟩
    · split_ifs with h
      · simp [h]
      · simp
    · rw [Finset.mem_Icc] at ha
      rcases Nat.lt_or_ge a m with h1 | h1
      · have h0 : (a : ZMod m) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          exact fun h ↦ absurd (Nat.le_of_dvd (by omega) h) (by omega)
        rw [ite_eq_right_iff.mpr (fun h ↦ absurd h h0), ZMod.val_natCast, Nat.mod_eq_of_lt h1]
      · have : a = m := by omega
        subst this
        simp
    · split_ifs with h
      · subst h
        rw [ZMod.natCast_self, div_self hm, Polynomial.eval_map, Polynomial.eval₂_at_one,
          div_self (Nat.cast_ne_zero.mpr (NeZero.ne m) : (m : ℚ) ≠ 0)]
      · rw [ZMod.natCast_zmod_val, Polynomial.eval_map,
          show ((a.val : ℂ) / m) = algebraMap ℚ ℂ ((a.val : ℚ) / m) by
            rw [map_div₀, map_natCast, map_natCast],
          Polynomial.eval₂_at_apply]

/-- $L(1,\chi^{-1}) = \frac{\pi i}{m}\,W(\chi^{-1})\,B_{1,\chi}$ for primitive odd $\chi$ mod $m$ (Tau Ceti's
cotangent formula). -/
theorem LFunction_inv_one_eq {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m} (hχ : χ.IsPrimitive)
    (hodd : χ.Odd) :
    χ⁻¹.LFunction 1 = π * I / m * gaussSum χ⁻¹ ZMod.stdAddChar * χ.generalizedBernoulli 1 := by
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    have h := hodd
    rw [DirichletCharacter.Odd, MulChar.one_apply isUnit_one.neg] at h
    norm_num at h
  have hinv : χ⁻¹.Odd := by
    rw [DirichletCharacter.Odd, MulChar.inv_apply_eq_inv', hodd, inv_neg, inv_one]
  have hL := χ⁻¹.two_mul_LFunction_one_eq_sum_mul_cot hinv
  have hsum := hχ.sum_inv_mul_pi_mul_cot (dvd_refl m) hχ1
  simp only [ZMod.natCast_zmod_val] at hsum
  simp_rw [div_mul_eq_mul_div] at hL
  rw [← Finset.sum_div, hsum] at hL
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  field_simp at hL ⊢
  linear_combination hL

/-- **Miyake, Theorem 3.3.4 (1)**, $k = 1$: for a primitive odd character $\chi$, $L(0,\chi) = -B_{1,\chi}$. -/
@[kb "miyake1989" "Theorem 3.3.4 (1), p. 95 (k = 1)"]
theorem LFunction_zero_of_odd {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m} (hχ : χ.IsPrimitive)
    (hodd : χ.Odd) :
    DirichletCharacter.LFunction χ 0 = -generalizedBernoulli χ 1 := by
  have hm1 : m ≠ 1 := by
    rintro rfl
    have := hodd
    rw [DirichletCharacter.Odd, show (-1 : ZMod 1) = 1 from Subsingleton.elim _ _, map_one] at this
    norm_num at this
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [generalizedBernoulli_eq_tauCeti]
  -- `L(0, χ) = Λ(0, χ)` and `Λ(1, χ⁻¹) = L(1, χ⁻¹) / π`
  have h0 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ 0 (Or.inr hm1)
  rw [hodd.gammaFactor_def, zero_add, Complex.Gammaℝ_one, div_one] at h0
  have hinvodd : χ⁻¹.Odd := by
    rw [DirichletCharacter.Odd, MulChar.inv_apply_eq_inv', hodd, inv_neg, inv_one]
  have h1 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ 1 (Or.inl one_ne_zero)
  rw [hinvodd.gammaFactor_def] at h1
  have hG2 : Gammaℝ (1 + 1) = (π : ℂ)⁻¹ := by
    rw [show (1 : ℂ) + 1 = 2 by norm_num, Complex.Gammaℝ_def]
    simp [Complex.cpow_neg_one]
  rw [hG2] at h1
  have hFE := hχ.completedLFunction_one_sub 1
  rw [sub_self] at hFE
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΛ1 : χ⁻¹.completedLFunction 1 = χ⁻¹.LFunction 1 / π := by
    rw [h1]; field_simp
  rw [h0, hFE, hΛ1, LFunction_inv_one_eq hχ hodd, DirichletCharacter.rootNumber]
  have hodd' : ¬ χ.Even := hodd.not_even
  simp only [hodd', ite_false, pow_one]
  have hprod := DirichletCharacter.gaussSum_mul_gaussSum_inv_eq_neg_one_mul_card_of_isPrimitive hχ
    (ZMod.isPrimitive_stdAddChar m)
  rw [ZMod.card, hodd] at hprod
  have hsq0 : (m : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]
  set r := (m : ℂ) ^ (1 / 2 : ℂ)
  have hI : I ≠ 0 := I_ne_zero
  calc r * (gaussSum χ ZMod.stdAddChar / I / r) *
        (π * I / m * gaussSum χ⁻¹ ZMod.stdAddChar * χ.generalizedBernoulli 1 / π)
      = (gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar) * χ.generalizedBernoulli 1 / m := by
        field_simp
    _ = -χ.generalizedBernoulli 1 := by
        rw [hprod]; field_simp

/-- **Miyake, Theorem 3.3.4**, $k = 1$, even characters: $L(0,\chi) = -B_{1,\chi}$ (both sides are $0$ unless
$\chi$ is the character mod $1$, where both are $-\tfrac12$). -/
@[kb "miyake1989" "Theorem 3.3.4, p. 95 (k = 1, even chi)"]
theorem LFunction_zero_of_even {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m} (heven : χ.Even) :
    DirichletCharacter.LFunction χ 0 = -generalizedBernoulli χ 1 := by
  rw [generalizedBernoulli_eq_tauCeti, DirichletCharacter.LFunction,
    ZMod.LFunction_apply_zero_of_even (by exact heven.to_fun)]
  rcases eq_or_ne m 1 with rfl | hm1
  · rw [DirichletCharacter.generalizedBernoulli_modOne]
    simp [Subsingleton.elim (0 : ZMod 1) 1]
    norm_num
  · rw [DirichletCharacter.generalizedBernoulli_eq_zero_of_apply_neg_one_eq_neg (Or.inr hm1)
      (by rw [heven]; norm_num), χ.map_zero' hm1]
    simp

/-- **Miyake, Theorem 3.3.4 (1)**, $k = 1$, in the book's form: for a primitive character $\chi$,
$L(0,\chi) = -B_{1,\chi}$ (for $\chi$ even and $m > 1$ both sides vanish, which is part (2); for the character mod
$1$ both are $-\tfrac12$, Miyake's $B_1 = 1/2$). Together with `LFunction_one_sub_nat` this is Theorem 3.3.4 (1)
for every $k \ge 1$. -/
@[kb "miyake1989" "Theorem 3.3.4 (1), p. 95 (k = 1)"]
theorem LFunction_zero {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m} (hχ : χ.IsPrimitive) :
    DirichletCharacter.LFunction χ 0 = -generalizedBernoulli χ 1 := by
  rcases χ.even_or_odd with h | h
  · exact LFunction_zero_of_even h
  · exact LFunction_zero_of_odd hχ h

end ModularFormsKB.Miyake
