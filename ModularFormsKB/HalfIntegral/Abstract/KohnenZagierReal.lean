/-
# The theta multiplier is compatible with complex conjugation

The identity below is correct, including the case $c = 0$, $d = -1$ where the principal square root does not commute
with conjugation.

Let $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \Gamma_0(4)$, $\gamma^* = \begin{pmatrix}a&-b\\-c&d\end{pmatrix}$
(Tau Ceti `Matrix.SpecialLinearGroup.conjJ`) and $\tau^* = -\bar\tau$ (Mathlib `J • τ`). Then
$$j(\gamma^*, \tau^*) = \overline{j(\gamma, \tau)}\qquad(\text{`thetaMult_conjJ`}),$$
for the theta multiplier $j(\gamma, \tau) = \varepsilon_d^{-1}\left(\tfrac cd\right)(c\tau+d)^{1/2}$.

**Proof.** For $c \ne 0$: $(-c)(-\bar\tau) + d = \overline{c\tau+d}$ is not a negative real, so the principal square root commutes
with conjugation (`Complex.conj_cpow`); $\overline{\varepsilon_d^{-1}} = \varepsilon_d$; and $\left(\tfrac{-c}d\right) = \varepsilon_d^2\left(\tfrac cd\right)$
by `jacobiSym.neg` and the sign convention of `shimuraSym`. For $c = 0$ both sides are $1$ ($d = \pm1$).
-/
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import ModularFormsKB.HalfIntegral.Abstract.ThetaInstance
import TauCeti.NumberTheory.ModularForms.Conjugate

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup UpperHalfPlane
open scoped ComplexConjugate

/-- **The Jacobi symbol identity** $\left(\tfrac{-c}{d}\right) = \varepsilon_d^2\left(\tfrac cd\right)$ in Shimura's convention. -/
theorem shimuraSym_neg {c d : ℤ} (hc : c ≠ 0) (hd : Odd d) :
    shimuraSym (-c) d = (if d % 4 = 1 then 1 else -1) * shimuraSym c d := by
  have hn : Odd d.natAbs := Int.natAbs_odd.2 hd
  have h := jacobiSym.neg c hn
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd
  have hmod : d % 4 = 1 ∨ d % 4 = 3 := by rcases hd with ⟨m, rfl⟩; omega
  have hv1 : d % 4 = 1 → (d > 0 → ZMod.χ₄ (d.natAbs : ZMod 4) = 1) ∧ (d < 0 → ZMod.χ₄ (d.natAbs : ZMod 4) = -1) := by
    intro h1
    exact ⟨fun hp ↦ ZMod.χ₄_nat_one_mod_four (by omega), fun hn' ↦ ZMod.χ₄_nat_three_mod_four (by omega)⟩
  have hv3 : d % 4 = 3 → (d > 0 → ZMod.χ₄ (d.natAbs : ZMod 4) = -1) ∧ (d < 0 → ZMod.χ₄ (d.natAbs : ZMod 4) = 1) := by
    intro h3
    exact ⟨fun hp ↦ ZMod.χ₄_nat_three_mod_four (by omega), fun hn' ↦ ZMod.χ₄_nat_one_mod_four (by omega)⟩
  unfold shimuraSym
  rw [h]
  rcases lt_or_gt_of_ne hd0 with hdn | hdp
  · rcases hmod with h1 | h3
    · rw [(hv1 h1).2 hdn]
      split_ifs <;> first | (exfalso; omega) | ring
    · rw [(hv3 h3).2 hdn]
      split_ifs <;> first | (exfalso; omega) | ring
  · rcases hmod with h1 | h3
    · rw [(hv1 h1).1 hdp]
      split_ifs <;> first | (exfalso; omega) | ring
    · rw [(hv3 h3).1 hdp]
      split_ifs <;> first | (exfalso; omega) | ring

/-- **The multiplier formula commutes with the reflection** for $c \ne 0$. -/
theorem thetaMultCD_reflect {c d : ℤ} (hc : c ≠ 0) (hd : Odd d) {z : ℂ} (hz : 0 < z.im) :
    thetaMultCD (-c) d (-conj z) = conj (thetaMultCD c d z) := by
  unfold thetaMultCD
  have hw : (((-c : ℤ) : ℂ)) * (-conj z) + (d : ℂ) = conj ((c : ℂ) * z + d) := by
    simp only [Int.cast_neg, map_add, map_mul, map_intCast]; ring
  have harg : ((c : ℂ) * z + d).arg ≠ Real.pi := by
    rw [Ne, Complex.arg_eq_pi_iff]
    rintro ⟨_, h⟩
    simp at h
    rcases h with h | h
    · exact hc h
    · exact hz.ne' h
  rw [hw, Complex.conj_cpow _ _ harg]
  have hhalf : conj (1 / 2 : ℂ) = 1 / 2 := by simp [map_ofNat]
  rw [hhalf, map_mul, map_mul]
  have hs : (shimuraSym (-c) d : ℂ) = (if d % 4 = 1 then 1 else -1) * shimuraSym c d := by
    have := shimuraSym_neg hc hd
    exact_mod_cast congrArg (fun x : ℤ ↦ (x : ℂ)) this
  have hconj_eps : conj ((epsD d)⁻¹) = epsD d := by unfold epsD; split_ifs <;> simp
  have hconj_s : conj (shimuraSym c d : ℂ) = shimuraSym c d := by simp
  rw [hconj_eps, hconj_s, hs]
  unfold epsD
  split_ifs <;> simp [Complex.inv_I] <;> ring

/-- **Compatibility of the theta multiplier with complex conjugation:** $j(\gamma^*, -\bar\tau) = \overline{j(\gamma, \tau)}$
for $\gamma \in \Gamma_0(4)$, $\gamma^* = $ `conjJ γ` (the sign of $b$ and $c$ reversed). -/
theorem thetaMult_conjJ {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (τ : ℍ) :
    thetaMult (Matrix.SpecialLinearGroup.conjJ γ) ((J • τ : ℍ) : ℂ) = conj (thetaMult γ τ) := by
  have hd : Odd (γ 1 1) := by
    have h4 : (4 : ℤ) ∣ γ 1 0 := by
      have := hγ
      rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      exact_mod_cast this
    have hdet := γ.det_coe
    rw [Matrix.det_fin_two] at hdet
    obtain ⟨m, hm⟩ := h4
    have h1 : γ 1 1 * γ 0 0 = 1 + 4 * (γ 0 1 * m) := by rw [hm] at hdet; linarith
    have h2 : Odd (γ 1 1 * γ 0 0) := by rw [h1]; exact ⟨2 * (γ 0 1 * m), by ring⟩
    exact (Int.odd_mul.1 h2).1
  have e10 : (Matrix.SpecialLinearGroup.conjJ γ) 1 0 = -γ 1 0 := rfl
  have e11 : (Matrix.SpecialLinearGroup.conjJ γ) 1 1 = γ 1 1 := rfl
  unfold thetaMult
  rw [e10, e11, coe_J_smul]
  by_cases hc : γ 1 0 = 0
  · have hdet := γ.det_coe
    rw [Matrix.det_fin_two, hc] at hdet
    have hd1 : γ 1 1 = 1 ∨ γ 1 1 = -1 := by
      have : γ 0 0 * γ 1 1 = 1 := by linarith
      exact Int.eq_one_or_neg_one_of_mul_eq_one' this |>.imp (fun h ↦ h.2) (fun h ↦ h.2)
    rw [hc, neg_zero]
    rcases hd1 with h | h <;> rw [h]
    · simp [thetaMultCD_zero_one]
    · simp [thetaMultCD_zero_neg_one]
  · exact thetaMultCD_reflect hc hd τ.im_pos

end ModularFormsKB.HalfIntegral
