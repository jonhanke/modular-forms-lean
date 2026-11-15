import ModularFormsKB.Miyake.Wave9.EtaHecke
import TauCeti.NumberTheory.ModularForms.Twist.Basic
import TauCeti.NumberTheory.ModularForms.Degeneracy
import TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.Ramified
import ModularFormsKB.Citation
open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm TauCeti.ExactDivisor

/-!
# Miyake §4.6: Corollary 4.6.18 (1), the Gauss-sum value of the constant in `f | η_q = c g_q`

Miyake, *Modular Forms* (Springer 1989), Corollary 4.6.18 (1), p. 172, case `N_q = q` prime and
`χ_q` primitive modulo `q`. Notation as in `Wave9/EtaOperator.lean` (an exact divisor `q ∥ N`,
`χ = ψ φ`, an `η`-matrix `η = γ diag(q, 1)` for `q`, Mathlib's slash).

## Result
* `corollary_4_6_18_one`: for a primitive form `f = Σ a_n e(nz)` of `𝒮_k^0(N, ψ φ)` with `ψ`
  primitive modulo `q`, `f | η = c g` with `g` primitive of `𝒮_k^0(N, ψ⁻¹ φ)` and
  `c = q⁻¹ ψ(-1) W(ψ) conj(a_q)`, where `W(ψ) = Σ_u ψ(u) e(u/q)` is `gaussSum ψ stdAddChar`.
  In Miyake's normalization of the slash (`det^{k/2}` instead of `det^{k-1}`) this is
  `c = N_q^{-k/2} W(χ_q) χ_q(-1) conj(a_q)`; the two differ by the factor `q^{1-k/2}`.
* `pseudo_core`: the equivalent form `q^{2-k} a_q ψ(-1) c = W(ψ)`, i.e.
  `c = ψ(-1) W(ψ) q^{k-2} / a_q`, valid for every `ψ` (primitivity is only used to know that
  `|a_q|² = q^{k-1}`).

## Proof
Put `D = diag(q, 1)`, `η = γ D`, `S_a = f | [1 a/q; 0 1]`, `Z = Σ_a ψ(a) S_a`. For a unit `a`,
`[1 u/q; 0 1] D⁻¹ η = γ_u [1 t/q; 0 1]` with `γ_u ∈ Γ₀(N)`, lower-right entry `≡ a⁻¹ mod q`,
`≡ 1 mod N/q`, and `t ≡ -a⁻¹` (`slash_coset`). Hence `Z | D⁻¹ η = Σ_v S_v - f`
(`sum_slash_coset`), and `Σ_v S_v = q a_q f(q ·)` (`sum_tr_eq`, from `U_q f = a_q f` via the
twist by `δ₀` and the level raise). Undoing `D⁻¹ η` with `f | η = c g`, `f | η² = E f` and
`f | γ² = ψ(-1) f` gives `Z = α g - β g(q ·)` (`Z_eq`). Comparing the first `q`-expansion
coefficients of `Z / q` (the twist of `f` by the inverse discrete Fourier transform of `ψ`, whose
first coefficient is `q⁻¹ W(ψ)`; `exists_twist_psi`) and of `α g - β g(q ·)`
(`coeff_one_of_eq`) gives `α = W(ψ)`.

Inputs from Tau Ceti: the twist (`CuspForm.twist`), the level raise, the `U_q`-eigenvalue
relation `a_{qm} = a_q a_m`, and Li's `|a_q|² = q^{k-1}` when the nebentypus is not defined
modulo `N/q` (`Newform.norm_qExpansion_coeff_prime_sq_of_not_exists_eq_comp`).
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace ModularFormsKB.Miyake.Sec4_6

open ModularFormsKB.Miyake.Wave4 ModularFormsKB.Miyake.Wave9

section Matrices

variable {q : ℕ} [NeZero q]

lemma coe_scaleGL_inv :
    (((TauCeti.scaleGL q)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(q : ℝ)⁻¹, 0; 0, 1] := by
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  rw [Matrix.GeneralLinearGroup.coe_inv, TauCeti.coe_scaleGL]
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hq]

/-- `η = γ diag(q, 1)` in `GL₂(ℝ)`. -/
lemma etaGL_eq_mul {N : ℕ} [NeZero N] {M : Matrix (Fin 2) (Fin 2) ℤ} (hQ : q ∥ N)
    (hM : IsEtaMatrix N q M) {γ : SL(2, ℤ)}
    (h : M = (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) :
    etaGL hQ hM = mapGL ℝ γ * TauCeti.scaleGL q := by
  refine Units.ext ?_
  rw [Units.val_mul, TauCeti.coe_atkinLehnerGL, TauCeti.coe_scaleGL]
  subst h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.mapGL_coe_matrix]

/-- The coset identity: `U(u/q) D⁻¹ γ D = γ_u U(t/q)`. -/
lemma coset_identity (γ γu : SL(2, ℤ)) (u t : ℤ)
    (h00 : γu 0 0 = γ 0 0 + u * γ 1 0) (h10 : γu 1 0 = q * γ 1 0)
    (h11 : γu 1 1 = γ 1 1 - γ 1 0 * t)
    (h01 : (q : ℤ) * γu 0 1 = γ 0 1 + u * γ 1 1 - (γ 0 0 + u * γ 1 0) * t) :
    Matrix.GeneralLinearGroup.upperRightHom ((u : ℝ) / q) * (TauCeti.scaleGL q)⁻¹ *
        (mapGL ℝ γ * TauCeti.scaleGL q) =
      mapGL ℝ γu * Matrix.GeneralLinearGroup.upperRightHom ((t : ℝ) / q) := by
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  refine Units.ext ?_
  simp only [Units.val_mul, coe_scaleGL_inv, TauCeti.coe_scaleGL,
    Matrix.GeneralLinearGroup.upperRightHom_apply]
  have h00' : (γu 0 0 : ℝ) = γ 0 0 + u * γ 1 0 := by exact_mod_cast h00
  have h10' : (γu 1 0 : ℝ) = q * γ 1 0 := by exact_mod_cast h10
  have h11' : (γu 1 1 : ℝ) = γ 1 1 - γ 1 0 * t := by exact_mod_cast h11
  have h01' : (q : ℝ) * γu 0 1 = γ 0 1 + u * γ 1 1 - (γ 0 0 + u * γ 1 0) * t := by
    exact_mod_cast h01
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      h00', h10', h11'] <;> field_simp
  · linear_combination (-1 : ℝ) * h01'
  · ring

end Matrices

section Coset

variable {N : ℕ} [NeZero N] {q : ℕ} [Fact q.Prime] [NeZero q]

lemma exists_gamma_u (γ : SL(2, ℤ)) (u t : ℤ)
    (ht : (q : ℤ) ∣ (γ 0 1 + u * γ 1 1) - (γ 0 0 + u * γ 1 0) * t) :
    ∃ γu : SL(2, ℤ), γu 0 0 = γ 0 0 + u * γ 1 0 ∧ γu 1 0 = q * γ 1 0 ∧
      γu 1 1 = γ 1 1 - γ 1 0 * t ∧
      (q : ℤ) * γu 0 1 = γ 0 1 + u * γ 1 1 - (γ 0 0 + u * γ 1 0) * t := by
  obtain ⟨B', hB'⟩ := ht
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 :=
    Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
  refine ⟨⟨!![γ 0 0 + u * γ 1 0, B'; q * γ 1 0, γ 1 1 - γ 1 0 * t], ?_⟩, by simp, by simp, by simp,
    ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (γ 1 0) * hB'
  · show (q : ℤ) * B' = _
    linear_combination (-1 : ℤ) * hB'

lemma cond_dvd (γ : SL(2, ℤ)) (hA : ((γ 0 0 : ℤ) : ZMod q) = 0)
    (hB : ((γ 0 1 : ℤ) : ZMod q) = -1) (hC : ((γ 1 0 : ℤ) : ZMod q) = 1)
    (hD : ((γ 1 1 : ℤ) : ZMod q) = 0) (u t : ℤ) (hu : (u : ZMod q) ≠ 0)
    (ht : (t : ZMod q) = -(u : ZMod q)⁻¹) :
    (q : ℤ) ∣ (γ 0 1 + u * γ 1 1) - (γ 0 0 + u * γ 1 0) * t := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [hA, hB, hC, hD, ht]
  field_simp
  ring

/-- The value of `ψ φ` at the diamond label of `γ ∈ Γ₀(N)`: `ψ(d) φ(d)`. -/
lemma splitChar_label (hQ : q ∥ N) (ψ : DirichletCharacter ℂ q)
    (φ : DirichletCharacter ℂ (N / q)) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    (((splitChar hQ ψ φ).toUnitHom ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩) : ℂˣ) : ℂ) =
      ψ ((γ 1 1 : ℤ) : ZMod q) * φ ((γ 1 1 : ℤ) : ZMod (N / q)) := by
  rw [MulChar.coe_toUnitHom, MonoidHom.coe_toHomUnits, Gamma0Map_apply]
  have hcop : IsCoprime (γ 1 1) (N : ℤ) := by
    obtain ⟨c, hc⟩ := mem_Gamma0_iff_dvd.mp hγ
    have hdet := Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
    exact ⟨γ 0 0, -(γ 0 1 * c), by rw [hc] at hdet; linear_combination hdet⟩
  simp only [splitChar, MulChar.coeToFun_mul, Pi.mul_apply,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop]

lemma slash_coset (k : ℤ) (hQ : q ∥ N) (ψ : DirichletCharacter ℂ q)
    (φ : DirichletCharacter ℂ (N / q)) {F : ℍ → ℂ}
    (hF : ∀ γ' : SL(2, ℤ), γ' ∈ Gamma0 N → F ∣[k] mapGL ℝ γ' =
      (ψ ((γ' 1 1 : ℤ) : ZMod q) * φ ((γ' 1 1 : ℤ) : ZMod (N / q))) • F)
    {γ : SL(2, ℤ)} (hA : (q : ℤ) ∣ γ 0 0) (hB : (q : ℤ) ∣ γ 0 1 + 1) (hC : (q : ℤ) ∣ γ 1 0 - 1)
    (hD : (q : ℤ) ∣ γ 1 1) (hC' : ((N / q : ℕ) : ℤ) ∣ γ 1 0) (hD' : ((N / q : ℕ) : ℤ) ∣ γ 1 1 - 1)
    (a : ZMod q) (ha : a ≠ 0) :
    (F ∣[k] Matrix.GeneralLinearGroup.upperRightHom ((a.val : ℝ) / q)) ∣[k]
        ((TauCeti.scaleGL q)⁻¹ * (mapGL ℝ γ * TauCeti.scaleGL q)) =
      ψ a⁻¹ • (F ∣[k] Matrix.GeneralLinearGroup.upperRightHom (((-a⁻¹).val : ℝ) / q)) := by
  have hN : N = q * (N / q) := (Nat.mul_div_cancel' hQ.dvd).symm
  set u : ℤ := (a.val : ℤ) with hu_def
  set t : ℤ := ((-a⁻¹).val : ℤ) with ht_def
  have hu : (u : ZMod q) = a := by simp [u]
  have ht : (t : ZMod q) = -a⁻¹ := by simp [t]
  have hA0 : ((γ 0 0 : ℤ) : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hA
  have hB0 : ((γ 0 1 : ℤ) : ZMod q) = -1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hB
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have hC0 : ((γ 1 0 : ℤ) : ZMod q) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hC
    push_cast at this
    exact sub_eq_zero.mp this
  have hD0 : ((γ 1 1 : ℤ) : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hD
  obtain ⟨γu, h00, h10, h11, h01⟩ := exists_gamma_u γ u t
    (cond_dvd γ hA0 hB0 hC0 hD0 u t (by rwa [hu]) (by rw [ht, hu]))
  have hγu : γu ∈ Gamma0 N := by
    rw [Gamma0_mem, h10]
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_
    rw [hN]
    push_cast
    exact mul_dvd_mul_left _ hC'
  have hψ : ((γu 1 1 : ℤ) : ZMod q) = a⁻¹ := by
    rw [h11]; push_cast; rw [hD0, hC0, ht]; ring
  have hφ : ((γu 1 1 : ℤ) : ZMod (N / q)) = 1 := by
    rw [h11]
    have e1 : ((γ 1 1 : ℤ) : ZMod (N / q)) = 1 :=
      sub_eq_zero.mp (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hD')
    have e2 : ((γ 1 0 : ℤ) : ZMod (N / q)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hC'
    push_cast
    rw [e1, e2]; ring
  have e1 : ((a.val : ℝ) / q) = ((u : ℝ) / q) := by simp [u]
  have e2 : (((-a⁻¹).val : ℝ) / q) = ((t : ℝ) / q) := by simp [t]
  rw [e1, e2, ← SlashAction.slash_mul, ← mul_assoc, coset_identity γ γu u t h00 h10 h11 h01,
    SlashAction.slash_mul, hF γu hγu, hψ, hφ, MulChar.map_one, mul_one,
    ModularForm.smul_slash_of_det_pos k (by simp [Matrix.GeneralLinearGroup.upperRightHom_apply])]

lemma det_R_pos (γ : SL(2, ℤ)) :
    0 < ((((TauCeti.scaleGL q)⁻¹ * (mapGL ℝ γ * TauCeti.scaleGL q) : GL (Fin 2) ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  have h : Matrix.GeneralLinearGroup.det
      ((TauCeti.scaleGL q)⁻¹ * (mapGL ℝ γ * TauCeti.scaleGL q) : GL (Fin 2) ℝ) = 1 := by
    rw [map_mul, map_mul, map_inv, Matrix.SpecialLinearGroup.det_mapGL]
    simp
  rw [h]; simp

/-- The translate `S a = F ∣ [1 a/q; 0 1]`. -/
abbrev tr (k : ℤ) (q : ℕ) (F : ℍ → ℂ) (a : ZMod q) : ℍ → ℂ :=
  F ∣[k] Matrix.GeneralLinearGroup.upperRightHom ((a.val : ℝ) / q)

lemma sum_slash_coset (k : ℤ) (hQ : q ∥ N) (ψ : DirichletCharacter ℂ q)
    (φ : DirichletCharacter ℂ (N / q)) {F : ℍ → ℂ}
    (hF : ∀ γ' : SL(2, ℤ), γ' ∈ Gamma0 N → F ∣[k] mapGL ℝ γ' =
      (ψ ((γ' 1 1 : ℤ) : ZMod q) * φ ((γ' 1 1 : ℤ) : ZMod (N / q))) • F)
    {γ : SL(2, ℤ)} (hA : (q : ℤ) ∣ γ 0 0) (hB : (q : ℤ) ∣ γ 0 1 + 1) (hC : (q : ℤ) ∣ γ 1 0 - 1)
    (hD : (q : ℤ) ∣ γ 1 1) (hC' : ((N / q : ℕ) : ℤ) ∣ γ 1 0) (hD' : ((N / q : ℕ) : ℤ) ∣ γ 1 1 - 1) :
    (∑ a : ZMod q, ψ a • tr k q F a) ∣[k]
        ((TauCeti.scaleGL q)⁻¹ * (mapGL ℝ γ * TauCeti.scaleGL q)) =
      (∑ v : ZMod q, tr k q F v) - F := by
  have hF0 : tr k q F 0 = F := by
    simp [tr]
  have key : ∀ a : ZMod q, ψ a • (tr k q F a ∣[k]
      ((TauCeti.scaleGL q)⁻¹ * (mapGL ℝ γ * TauCeti.scaleGL q))) =
      tr k q F (-a⁻¹) - (if a = 0 then tr k q F 0 else 0) := by
    intro a
    by_cases ha : a = 0
    · subst ha
      rw [MulChar.map_nonunit ψ not_isUnit_zero]
      simp
    · rw [show (if a = 0 then tr k q F 0 else 0) = 0 by simp [ha], sub_zero, slash_coset k hQ ψ φ hF hA hB hC hD hC' hD' a ha, smul_smul,
        ← map_mul, mul_inv_cancel₀ ha, MulChar.map_one, one_smul]
  rw [SlashAction.sum_slash]
  simp_rw [ModularForm.smul_slash_of_det_pos k (det_R_pos γ), key]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have e : ∑ a : ZMod q, tr k q F (-a⁻¹) = ∑ v : ZMod q, tr k q F v :=
    Equiv.sum_comp ((Function.Involutive.toPerm (fun a : ZMod q => a⁻¹) inv_inv).trans
      (Equiv.neg _)) (tr k q F)
  rw [e, hF0]

end Coset

section UOperator

lemma funext_of_coeff {L : ℕ} [NeZero L] {k : ℤ} (f g : CuspForm ((Gamma1 L).map (mapGL ℝ)) k)
    (c : ℂ) (h : ∀ m, (qExpansion 1 ⇑f).coeff m = c * (qExpansion 1 ⇑g).coeff m) :
    ⇑f = c • ⇑g := by
  have : Fact (IsCusp OnePoint.infty ((Gamma1 L).map (mapGL ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map L)⟩
  funext τ
  have h1 := ModularForm.hasSum_qExpansion (f := f) one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map L) τ
  have h2 := (ModularForm.hasSum_qExpansion (f := g) one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map L) τ).mul_left c
  simp only [h, mul_assoc] at h1
  exact h1.unique h2

variable {N : ℕ} [NeZero N] {q : ℕ} [Fact q.Prime] [NeZero q]

lemma sum_tr_eq (k : ℤ) (hqN : q ∣ N) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (a : ℂ)
    (hU : ∀ m, (qExpansion 1 ⇑f).coeff (q * m) = a * (qExpansion 1 ⇑f).coeff m) :
    ∑ v : ZMod q, tr k q ⇑f v = ((q : ℂ) * a) • (fun τ ↦ f (TauCeti.scaleGL q • τ)) := by
  have hNL : N * q ∣ q * N := by rw [mul_comm]
  have hML : q * q ∣ q * N := mul_dvd_mul_left q hqN
  set Φ : ZMod q → ℂ := Pi.single 0 1 with hΦ
  have hcoeff : ∀ m, (qExpansion 1 ⇑(CuspForm.twist Φ hNL hML f)).coeff m =
      a * (qExpansion 1 ⇑(TauCeti.CuspForm.levelRaise q
        (TauCeti.Gamma1_map_le_conjAct_scaleGL N q) f)).coeff m := by
    intro m
    rw [CuspForm.qExpansion_twist_coeff, TauCeti.CuspForm.qExpansion_levelRaise_coeff_Gamma1]
    by_cases hd : q ∣ m
    · obtain ⟨j, rfl⟩ := hd
      simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ (Fact.out : q.Prime).pos, hU j]
      simp [hΦ]
    · have : (m : ZMod q) ≠ 0 := fun h ↦ hd ((ZMod.natCast_eq_zero_iff m q).mp h)
      simp [hΦ, hd, this]
  have h := funext_of_coeff _ _ a hcoeff
  funext τ
  have h1 := congrFun h τ
  rw [CuspForm.twist_apply, Pi.smul_apply, TauCeti.CuspForm.levelRaise_apply] at h1
  have hF : ∀ b : ZMod q, ZMod.dft Φ b = 1 := by
    intro b
    rw [ZMod.dft_apply]
    simp [hΦ, Pi.single_apply]
  simp only [hF, one_mul, smul_eq_mul] at h1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, tr,
    TauCeti.ModularForm.slash_upperRightHom_apply]
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  rw [mul_assoc]
  have h2 : ∑ x : ZMod q, (⇑f) (((x.val : ℝ) / q) +ᵥ τ) = (q : ℂ) * (a * f (TauCeti.scaleGL q • τ)) := by
    rw [← h1]; field_simp
  rw [← h2]

end UOperator

section FirstCoeff

variable {N : ℕ} [NeZero N] {q : ℕ} [Fact q.Prime] [NeZero q]

/-- If a form `T` of level `Γ₁(qN)` is `α g(τ) + β g(qτ)`, its first coefficient is `α b₁`. -/
lemma coeff_one_of_eq (k : ℤ) (T : CuspForm ((Gamma1 (q * N)).map (mapGL ℝ)) k)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (α β : ℂ)
    (h : ∀ τ : ℍ, T τ = α * g τ + β * g (TauCeti.scaleGL q • τ)) :
    (qExpansion 1 ⇑T).coeff 1 = α * (qExpansion 1 ⇑g).coeff 1 := by
  have : Fact (IsCusp OnePoint.infty ((Gamma1 N).map (mapGL ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N)⟩
  have : Fact (IsCusp OnePoint.infty ((Gamma1 (q * N)).map (mapGL ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map (q * N))⟩
  set V := TauCeti.CuspForm.levelRaise q (TauCeti.Gamma1_map_le_conjAct_scaleGL N q) g with hV
  have hVc : ∀ m, (qExpansion 1 ⇑V).coeff m =
      if q ∣ m then (qExpansion 1 ⇑g).coeff (m / q) else 0 :=
    TauCeti.CuspForm.qExpansion_levelRaise_coeff_Gamma1 N g
  set c : ℕ → ℂ := fun m ↦ α * (qExpansion 1 ⇑g).coeff m + β * (qExpansion 1 ⇑V).coeff m with hc
  have hsum : ∀ τ : ℍ, HasSum (fun m ↦ c m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) (T τ) := by
    intro τ
    have h1 := (ModularForm.hasSum_qExpansion (f := g) one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map N) τ).mul_left α
    have h2 := (ModularForm.hasSum_qExpansion (f := V) one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map (q * N)) τ).mul_left β
    rw [h τ, ← TauCeti.CuspForm.levelRaise_apply (TauCeti.Gamma1_map_le_conjAct_scaleGL N q) g τ]
    convert h1.add h2 using 1
    funext m
    simp only [hc, smul_eq_mul]
    ring
  have := ModularFormClass.qExpansion_coeff_unique one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map (q * N)) (f := T) hsum 1
  rw [← this, hc]
  simp only [hVc]
  have : ¬ q ∣ 1 := fun h1 ↦ (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h1)
  simp [this]

end FirstCoeff

section Algebra

variable {N : ℕ} [NeZero N] {q : ℕ} [Fact q.Prime] [NeZero q]

lemma slash_cancel (k : ℤ) (g : GL (Fin 2) ℝ) (H : ℍ → ℂ) : (H ∣[k] g) ∣[k] g⁻¹ = H := by
  rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

lemma slash_cancel' (k : ℤ) (g : GL (Fin 2) ℝ) (H : ℍ → ℂ) : (H ∣[k] g⁻¹) ∣[k] g = H := by
  rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]

/-- Positive determinant. -/
def PD (g : GL (Fin 2) ℝ) : Prop := 0 < ((g : Matrix (Fin 2) (Fin 2) ℝ)).det

lemma PD.inv {g : GL (Fin 2) ℝ} (h : PD g) : PD g⁻¹ := by
  unfold PD at *
  rw [← Matrix.GeneralLinearGroup.val_det_apply] at *
  rw [map_inv, Units.val_inv_eq_inv_val]
  exact inv_pos.mpr h

lemma PD.mul {g h : GL (Fin 2) ℝ} (hg : PD g) (hh : PD h) : PD (g * h) := by
  unfold PD at *
  rw [← Matrix.GeneralLinearGroup.val_det_apply] at *
  rw [map_mul, Units.val_mul]
  exact mul_pos hg hh

lemma PD.scaleGL : PD (TauCeti.scaleGL q) := TauCeti.val_det_scaleGL_pos

lemma PD.mapGL (γ : SL(2, ℤ)) : PD (mapGL ℝ γ) := by
  unfold PD
  rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.det_mapGL]
  simp

lemma smul_slash_PD (k : ℤ) {g : GL (Fin 2) ℝ} (h : PD g) (H : ℍ → ℂ) (c : ℂ) :
    (c • H) ∣[k] g = c • (H ∣[k] g) :=
  ModularForm.smul_slash_of_det_pos k h H c

end Algebra

section ZEq

variable {N : ℕ} [NeZero N] {q : ℕ} [Fact q.Prime] [NeZero q]

lemma slash_gamma_sq (k : ℤ) (hQ : q ∥ N) (ψ : DirichletCharacter ℂ q)
    (φ : DirichletCharacter ℂ (N / q)) {F : ℍ → ℂ}
    (hF : ∀ γ' : SL(2, ℤ), γ' ∈ Gamma0 N → F ∣[k] mapGL ℝ γ' =
      (ψ ((γ' 1 1 : ℤ) : ZMod q) * φ ((γ' 1 1 : ℤ) : ZMod (N / q))) • F)
    {γ : SL(2, ℤ)} (hA : (q : ℤ) ∣ γ 0 0) (hB : (q : ℤ) ∣ γ 0 1 + 1) (hC : (q : ℤ) ∣ γ 1 0 - 1)
    (hD : (q : ℤ) ∣ γ 1 1) (hC' : ((N / q : ℕ) : ℤ) ∣ γ 1 0) (hD' : ((N / q : ℕ) : ℤ) ∣ γ 1 1 - 1) :
    (F ∣[k] mapGL ℝ γ) ∣[k] mapGL ℝ γ = ψ (-1) • F := by
  have hN : N = q * (N / q) := (Nat.mul_div_cancel' hQ.dvd).symm
  have e10 : ((γ * γ : SL(2, ℤ)) 1 0 : ℤ) = γ 1 0 * (γ 0 0 + γ 1 1) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  have e11 : ((γ * γ : SL(2, ℤ)) 1 1 : ℤ) = γ 1 0 * γ 0 1 + γ 1 1 * γ 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hmem : γ * γ ∈ Gamma0 N := by
    rw [Gamma0_mem, e10]
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_
    rw [hN]; push_cast
    rw [mul_comm (γ 1 0)]
    exact mul_dvd_mul (dvd_add hA hD) hC'
  have hB0 : ((γ 0 1 : ℤ) : ZMod q) = -1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hB
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have hC0 : ((γ 1 0 : ℤ) : ZMod q) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hC
    push_cast at this
    exact sub_eq_zero.mp this
  have hD0 : ((γ 1 1 : ℤ) : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hD
  have e1 : ((γ 1 1 : ℤ) : ZMod (N / q)) = 1 :=
    sub_eq_zero.mp (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hD')
  have e2 : ((γ 1 0 : ℤ) : ZMod (N / q)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hC'
  rw [← SlashAction.slash_mul, ← map_mul, hF _ hmem, e11]
  push_cast
  rw [hC0, hB0, hD0, e1, e2]
  simp

lemma Z_eq (k : ℤ) (hQ : q ∥ N) (ψ : DirichletCharacter ℂ q)
    (φ : DirichletCharacter ℂ (N / q)) {F G₀ : ℍ → ℂ}
    (hF : ∀ γ' : SL(2, ℤ), γ' ∈ Gamma0 N → F ∣[k] mapGL ℝ γ' =
      (ψ ((γ' 1 1 : ℤ) : ZMod q) * φ ((γ' 1 1 : ℤ) : ZMod (N / q))) • F)
    {γ : SL(2, ℤ)} (hA : (q : ℤ) ∣ γ 0 0) (hB : (q : ℤ) ∣ γ 0 1 + 1) (hC : (q : ℤ) ∣ γ 1 0 - 1)
    (hD : (q : ℤ) ∣ γ 1 1) (hC' : ((N / q : ℕ) : ℤ) ∣ γ 1 0) (hD' : ((N / q : ℕ) : ℤ) ∣ γ 1 1 - 1)
    (c₀ E aq : ℂ) (hE0 : E ≠ 0)
    (hfg : F ∣[k] (mapGL ℝ γ * TauCeti.scaleGL q) = c₀ • G₀)
    (hE : (F ∣[k] (mapGL ℝ γ * TauCeti.scaleGL q)) ∣[k] (mapGL ℝ γ * TauCeti.scaleGL q) = E • F)
    (hsum : ∑ v : ZMod q, tr k q F v = ((q : ℂ) * aq) • (fun τ ↦ F (TauCeti.scaleGL q • τ))) :
    ∑ a : ZMod q, ψ a • tr k q F a =
      ((q : ℂ) * aq * (q : ℂ) ^ (1 - k) * ψ (-1) * c₀) • G₀ -
        (E⁻¹ * c₀) • (G₀ ∣[k] TauCeti.scaleGL q) := by
  set D := TauCeti.scaleGL q with hD_def
  set g : GL (Fin 2) ℝ := mapGL ℝ γ with hg_def
  have hPDD : PD D := PD.scaleGL
  have hPDg : PD g := PD.mapGL γ
  have hεε : ψ (-1) * ψ (-1) = 1 := by
    rw [← map_mul]; simp
  have h1 : (∑ a : ZMod q, ψ a • tr k q F a) ∣[k] (D⁻¹ * (g * D)) =
      (∑ v : ZMod q, tr k q F v) - F := sum_slash_coset k hQ ψ φ hF hA hB hC hD hC' hD'
  have hFD : (fun τ ↦ F (D • τ)) = (q : ℂ) ^ (1 - k) • (F ∣[k] D) :=
    (TauCeti.smul_slash_scaleGL_eq k F).symm
  rw [hsum, hFD, smul_smul] at h1
  set κ : ℂ := (q : ℂ) * aq * (q : ℂ) ^ (1 - k) with hκ
  have hη : (mapGL ℝ γ * TauCeti.scaleGL q) = g * D := rfl
  have hFγ : F ∣[k] g = c₀ • (G₀ ∣[k] D⁻¹) := by
    have : (F ∣[k] g) ∣[k] D = c₀ • G₀ := by rw [← SlashAction.slash_mul]; exact hfg
    calc F ∣[k] g = ((F ∣[k] g) ∣[k] D) ∣[k] D⁻¹ := (slash_cancel k D _).symm
      _ = _ := by rw [this, smul_slash_PD k hPDD.inv]
  have hγinv : F ∣[k] g⁻¹ = ψ (-1) • (F ∣[k] g) := by
    have hsq := slash_gamma_sq k hQ ψ φ hF hA hB hC hD hC' hD'
    have h' : F ∣[k] g = ψ (-1) • (F ∣[k] g⁻¹) := by
      calc F ∣[k] g = ((F ∣[k] g) ∣[k] g) ∣[k] g⁻¹ := (slash_cancel k g _).symm
        _ = _ := by rw [hsq, smul_slash_PD k hPDg.inv]
    rw [h', smul_smul, hεε, one_smul]
  have hηinv : F ∣[k] (g * D)⁻¹ = (E⁻¹ * c₀) • G₀ := by
    have hPDη : PD (g * D) := hPDg.mul hPDD
    have h' : F ∣[k] (g * D) = E • (F ∣[k] (g * D)⁻¹) := by
      calc F ∣[k] (g * D) = ((F ∣[k] (g * D)) ∣[k] (g * D)) ∣[k] (g * D)⁻¹ :=
            (slash_cancel k (g * D) _).symm
        _ = _ := by rw [hE, smul_slash_PD k hPDη.inv]
    rw [hη] at hfg
    rw [hfg] at h'
    calc F ∣[k] (g * D)⁻¹ = E⁻¹ • (E • (F ∣[k] (g * D)⁻¹)) := by
          rw [smul_smul, inv_mul_cancel₀ hE0, one_smul]
      _ = _ := by rw [← h', smul_smul]
  have hDη : D * (g * D)⁻¹ = g⁻¹ := by
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  have hR : (D⁻¹ * (g * D))⁻¹ = (g * D)⁻¹ * D := by rw [mul_inv_rev, inv_inv]
  have hPDR : PD ((g * D)⁻¹ * D) := (hPDg.mul hPDD).inv.mul hPDD
  have hZ : ∑ a : ZMod q, ψ a • tr k q F a =
      ((∑ a : ZMod q, ψ a • tr k q F a) ∣[k] (D⁻¹ * (g * D))) ∣[k] (D⁻¹ * (g * D))⁻¹ :=
    (slash_cancel k _ _).symm
  refine hZ.trans ?_
  rw [h1, hR, SlashAction.sub_slash, smul_slash_PD k hPDR, SlashAction.slash_mul,
    SlashAction.slash_mul, ← SlashAction.slash_mul k D, hDη, hγinv, hFγ, hηinv]
  simp only [smul_slash_PD k hPDD, slash_cancel' k D, smul_smul]
  congr 2
  ring

end ZEq

section Gauss

variable {N : ℕ} [NeZero N] {q : ℕ} [Fact q.Prime] [NeZero q]

lemma exists_twist_psi (k : ℤ) (hqN : q ∣ N) (ψ : DirichletCharacter ℂ q)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∃ T : CuspForm ((Gamma1 (q * N)).map (mapGL ℝ)) k,
      (∀ τ : ℍ, T τ = (q : ℂ)⁻¹ * (∑ a : ZMod q, ψ a • tr k q ⇑f a) τ) ∧
      (qExpansion 1 ⇑T).coeff 1 =
        (q : ℂ)⁻¹ * gaussSum ψ ZMod.stdAddChar * (qExpansion 1 ⇑f).coeff 1 := by
  have hNL : N * q ∣ q * N := by rw [mul_comm]
  have hML : q * q ∣ q * N := mul_dvd_mul_left q hqN
  set Φ : ZMod q → ℂ := ZMod.dft.symm (fun a ↦ ψ a) with hΦ
  have hF : ZMod.dft Φ = fun a ↦ ψ a := LinearEquiv.apply_symm_apply _ _
  refine ⟨CuspForm.twist Φ hNL hML f, ?_, ?_⟩
  · intro τ
    rw [CuspForm.twist_apply, hF]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, tr,
      TauCeti.ModularForm.slash_upperRightHom_apply]
  · rw [CuspForm.qExpansion_twist_coeff]
    have h1 : Φ ((1 : ℕ) : ZMod q) = (q : ℂ)⁻¹ * gaussSum ψ ZMod.stdAddChar := by
      rw [hΦ, ZMod.invDFT_apply]
      simp [gaussSum, mul_comm]
    rw [h1]

end Gauss

section Primitive

variable {N : ℕ} [NeZero N] {q : ℕ} [Fact q.Prime] [NeZero q]

lemma exists_unit_crt (hQ : q ∥ N) (v : (ZMod q)ˣ) :
    ∃ x : (ZMod N)ˣ, ZMod.unitsMap hQ.dvd x = v ∧
      ZMod.unitsMap (Nat.div_dvd_of_dvd hQ.dvd) x = 1 := by
  obtain ⟨m, hm1, hm2⟩ := Nat.chineseRemainder hQ.coprime ((v : ZMod q).val) 1
  have hmq : (m : ZMod q) = v := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hm1]; exact ZMod.natCast_zmod_val _
  have hmN' : (m : ZMod (N / q)) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff m 1 (N / q)).mpr hm2
    simpa using this
  have hc1 : m.Coprime q := (ZMod.isUnit_iff_coprime m q).mp (hmq ▸ v.isUnit)
  have hc2 : m.Coprime (N / q) := (ZMod.isUnit_iff_coprime m (N / q)).mp (hmN' ▸ isUnit_one)
  have hN : N = q * (N / q) := (Nat.mul_div_cancel' hQ.dvd).symm
  have hcop : m.Coprime N := by
    rw [hN]; exact Nat.Coprime.mul_right hc1 hc2
  refine ⟨ZMod.unitOfCoprime m hcop, Units.ext ?_, Units.ext ?_⟩
  · rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime]
    simp only [ZMod.cast_natCast hQ.dvd, hmq]
  · rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime]
    simp only [ZMod.cast_natCast (Nat.div_dvd_of_dvd hQ.dvd), hmN',
      Units.val_one]

lemma not_exists_comp (hQ : q ∥ N) (ψ : DirichletCharacter ℂ q)
    (φ : DirichletCharacter ℂ (N / q)) (hψ : ψ.IsPrimitive) :
    ¬ ∃ χ₀ : (ZMod (N / q))ˣ →* ℂˣ, (splitChar hQ ψ φ).toUnitHom =
      χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hQ.dvd)) := by
  rintro ⟨χ₀, h⟩
  have hone : ψ = 1 := by
    ext v
    obtain ⟨x, hx1, hx2⟩ := exists_unit_crt hQ v
    have := congrArg (fun χ : (ZMod N)ˣ →* ℂˣ ↦ ((χ x : ℂˣ) : ℂ)) h
    simp only [toUnitHom_splitChar, MonoidHom.mul_apply, MonoidHom.comp_apply, hx1, hx2,
      map_one, Units.val_one, mul_one] at this
    simpa using this
  apply (Fact.out : q.Prime).one_lt.ne'
  have := hψ
  rw [DirichletCharacter.IsPrimitive, hone, DirichletCharacter.conductor_one] at this
  exact this.symm

end Primitive

section Core

variable {N : ℕ} [NeZero N] {q : ℕ} [Fact q.Prime] [NeZero q] {M : Matrix (Fin 2) (Fin 2) ℤ}

lemma prim_facts (k : ℤ) (hQ : q ∥ N) (ψ : DirichletCharacter ℂ q)
    (φ : DirichletCharacter ℂ (N / q)) (hψ : ψ.IsPrimitive)
    {f : cuspSpace k (splitChar hQ ψ φ)} (hf : IsPrimitive f) :
    (∀ m, coeff f (q * m) = coeff f q * coeff f m) ∧
      coeff f q * starRingEnd ℂ (coeff f q) = (q : ℂ) ^ (k - 1) := by
  obtain ⟨F, hχ, hF⟩ := (isPrimitive_iff_exists_newform f).mp hf
  have hq : q.Prime := Fact.out
  have hqN : q ∣ N := hQ.dvd
  have hU := F.heckeUCuspNat_eq_qExpansion_coeff_smul hq hqN
  have hU' := (HeckeRing.GL2.heckeUCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul k hq hqN
    _).mp hU
  rw [hF] at hU'
  refine ⟨hU', ?_⟩
  have hχ' : ¬ ∃ χ₀ : (ZMod (N / q))ˣ →* ℂˣ,
      F.χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hqN)) := by
    rw [hχ]; exact not_exists_comp hQ ψ φ hψ
  have hn := F.norm_qExpansion_coeff_prime_sq_of_not_exists_eq_comp hq hqN hχ'
  rw [hF] at hn
  change (qExpansion 1 (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff q *
    starRingEnd ℂ ((qExpansion 1 (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff q) = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn,
    Complex.ofReal_zpow, Complex.ofReal_natCast]

lemma pseudo_core (k : ℤ) (hQ : q ∥ N) (hM : IsEtaMatrix N q M) (ψ : DirichletCharacter ℂ q)
    (φ : DirichletCharacter ℂ (N / q)) (f : cuspSpace k (splitChar hQ ψ φ))
    (g : cuspSpace k (splitChar hQ ψ⁻¹ φ)) (c₀ : ℂ)
    (hfg : ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] etaGL hQ hM =
      c₀ • ⇑(g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hf1 : coeff f 1 = 1) (hg1 : coeff g 1 = 1)
    (hU : ∀ m, coeff f (q * m) = coeff f q * coeff f m) :
    (q : ℂ) * coeff f q * (q : ℂ) ^ (1 - k) * ψ (-1) * c₀ = gaussSum ψ ZMod.stdAddChar := by
  have hqN : q ∣ N := hQ.dvd
  obtain ⟨γ, hMeq, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hM.exists_entries
  have sq1 : ∀ x : ℤ, ((q ^ 2 : ℕ) : ℤ) ∣ x → (q : ℤ) ∣ x := fun x hx ↦
    (Dvd.intro_left (q : ℤ) (by push_cast; ring)).trans hx
  have sq2 : ∀ x : ℤ, (((N / q) ^ 2 : ℕ) : ℤ) ∣ x → ((N / q : ℕ) : ℤ) ∣ x := fun x hx ↦
    (Dvd.intro_left ((N / q : ℕ) : ℤ) (by push_cast; ring)).trans hx
  have hGL := etaGL_eq_mul hQ hM hMeq
  rw [hGL] at hfg
  have hF : ∀ γ' : SL(2, ℤ), γ' ∈ Gamma0 N → ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k]
      mapGL ℝ γ' = (ψ ((γ' 1 1 : ℤ) : ZMod q) * φ ((γ' 1 1 : ℤ) : ZMod (N / q))) •
        ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := fun γ' h ↦ by
    rw [(TauCeti.mem_cuspFormCharSpace_iff_nebentypus k _ _).mp f.2 ⟨γ', h⟩,
      splitChar_label hQ ψ φ h]
  have hE := eta_slash_eta k hQ hM ψ φ f
  rw [hGL] at hE
  have hE0 := etaSqConst_ne_zero k hQ ψ φ
  have hsum := sum_tr_eq k hqN (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (coeff f q) hU
  have hZ := Z_eq k hQ ψ φ hF (sq1 _ h1) (sq1 _ h2) (sq1 _ h3) (sq1 _ h4) (sq2 _ h7) (sq2 _ h8)
    c₀ _ (coeff f q) hE0 hfg hE hsum
  obtain ⟨T, hT1, hT2⟩ := exists_twist_psi k hqN ψ (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hcoef := coeff_one_of_eq k T
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    ((q : ℂ)⁻¹ * ((q : ℂ) * coeff f q * (q : ℂ) ^ (1 - k) * ψ (-1) * c₀))
    ((q : ℂ)⁻¹ * (-(etaSqConst k ψ φ)⁻¹ * c₀ * (q : ℂ) ^ (k - 1))) (fun τ ↦ by
      rw [hT1, congrFun hZ τ]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, TauCeti.slash_scaleGL_apply]
      ring)
  rw [hT2, show (qExpansion 1 ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 = 1
    from hf1, show (qExpansion 1 ⇑(g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 = 1
    from hg1] at hcoef
  have := mul_left_cancel₀ (inv_ne_zero hq0) (by simpa using hcoef.symm)
  exact this

end Core

section Main

variable {N : ℕ} [NeZero N] {M : Matrix (Fin 2) (Fin 2) ℤ}

/-- **Miyake, Corollary 4.6.18 (1)** (`N_q = q`, `χ_q` primitive modulo `q`): for a primitive form
`f = Σ a_n e(nz)` of `𝒮_k^0(N, χ_q χ'_q)`, `f | η_q = c g_q` with
`c = q⁻¹ χ_q(-1) W(χ_q) conj(a_q)` in Mathlib's normalization of the slash
(`W(ψ) = Σ_u ψ(u) e(u/q)` is `gaussSum ψ stdAddChar`); in Miyake's normalization this is
`c = N_q^{-k/2} W(χ_q) χ_q(-1) conj(a_q)`. -/
@[kb "miyake1989" "Corollary 4.6.18 (1), p. 172 (N_q = q)"]
theorem corollary_4_6_18_one (k : ℤ) {q : ℕ} [NeZero q] (hq : q.Prime) (hQ : q ∥ N)
    (hM : IsEtaMatrix N q M) (ψ : DirichletCharacter ℂ q) (hψ : ψ.IsPrimitive)
    (φ : DirichletCharacter ℂ (N / q))
    {f : cuspSpace k (splitChar hQ ψ φ)} (hf : IsPrimitive f) :
    ∃ g : cuspSpace k (splitChar hQ ψ⁻¹ φ), IsPrimitive g ∧
      ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] etaGL hQ hM =
        ((q : ℂ)⁻¹ * ψ (-1) * gaussSum ψ (ZMod.stdAddChar) * starRingEnd ℂ (coeff f q)) •
          ⇑(g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨g, hg, ⟨c₀, -, hfg⟩, -⟩ := exists_isPrimitive_eta_all k hQ hM ψ φ hf
  obtain ⟨hU, hnorm⟩ := prim_facts k hQ ψ φ hψ hf
  have hcore := pseudo_core k hQ hM ψ φ f g c₀ hfg hf.2.2 hg.2.2 hU
  refine ⟨g, hg, ?_⟩
  rw [hfg]
  congr 1
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hεε : ψ (-1) * ψ (-1) = 1 := by rw [← map_mul]; simp
  have hpow : (q : ℂ) ^ (1 - k) * (q : ℂ) ^ (k - 1) = 1 := by
    rw [← zpow_add₀ hq0]; simp
  rw [← hcore]
  have : (q : ℂ)⁻¹ * ψ (-1) * ((q : ℂ) * coeff f q * (q : ℂ) ^ (1 - k) * ψ (-1) * c₀) *
      starRingEnd ℂ (coeff f q) = ((q : ℂ)⁻¹ * q) * (ψ (-1) * ψ (-1)) *
        ((q : ℂ) ^ (1 - k) * (coeff f q * starRingEnd ℂ (coeff f q))) * c₀ := by ring
  rw [this, inv_mul_cancel₀ hq0, hεε, hnorm, hpow]
  ring

end Main

end ModularFormsKB.Miyake.Sec4_6
