import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.ModularForms.Petersson
import ModularFormsKB.Citation
/-!
# Miyake §2.1: the boundedness criterion for cusp forms

Miyake, *Modular Forms* (Springer 1989), §2.1, pp. 42–43, Theorem 2.1.5 and Corollary 2.1.6.

We work with Mathlib's `ModularForm Γ k` and `CuspForm Γ k` for an arithmetic subgroup `Γ` of
`GL₂(ℝ)` (Miyake's `𝒢_k(Γ)` and `𝒮_k(Γ)` for a modular group, integral weight `k`).

* Theorem 2.1.5: a holomorphic `Γ`-invariant function `f` of weight `k > 0` is a cusp form if and
  only if `|f(z)| Im(z)^{k/2}` is bounded on `ℍ`
  (`ModularFormsKB.Miyake.exists_cuspForm_iff_bounded`). The direction "cusp form ⇒ bounded" is
  Mathlib's `CuspFormClass.exists_bound`; the converse is new here and holds at every point of
  `ℙ¹(ℝ)` for every `k > 0` (`ModularFormsKB.Miyake.isZeroAt_of_bounded`), with no hypothesis on
  `Γ`. Miyake states the theorem for `f ∈ Ω_k(Γ)` (meromorphic); boundedness forces holomorphy,
  and the meromorphic case is not covered (Mathlib has no meromorphic modular forms). Miyake's
  `k` is implicitly positive: for `k = 0` a nonzero constant is a counterexample.
* Corollary 2.1.6: Hecke's bound `a_n = O(n^{k/2})` for the Fourier coefficients of a cusp form at
  any cusp `x₀ = g ∞`, `g ∈ SL₂(ℤ)` (`ModularFormsKB.Miyake.qExpansion_slash_isBigO`), from
  Mathlib's bound at `∞` (`CuspFormClass.qExpansion_isBigO`) applied to the translate `f ∣[k] g`.
-/

open UpperHalfPlane ModularForm OnePoint Filter Asymptotics ConjAct Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Manifold Pointwise

namespace ModularFormsKB.Miyake

/-- The converse half of **Miyake, Theorem 2.1.5**, pointwise at a cusp: if `k > 0` and
`|f(z)| Im(z)^{k/2}` is bounded on `ℍ`, then `f` vanishes at every `c ∈ ℙ¹(ℝ)`, i.e.
`f ∣[k] g → 0` at `i∞` for every `g ∈ GL₂(ℝ)` with `g ∞ = c`. -/
@[kb "miyake1989" "Theorem 2.1.5, p. 42"]
theorem isZeroAt_of_bounded {k : ℤ} (hk : 0 < k) {f : ℍ → ℂ}
    (hf : ∃ C, ∀ τ : ℍ, ‖f τ‖ * τ.im ^ ((k : ℝ) / 2) ≤ C) (c : OnePoint ℝ) :
    c.IsZeroAt f k := by
  intro g _
  obtain ⟨C, hC⟩ := hf
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set D := |g.det.val| ^ (k - 2) * C' ^ 2 with hD
  have key : ∀ τ : ℍ, ‖(f ∣[k] g) τ‖ ^ 2 * τ.im ^ (k : ℤ) ≤ D := by
    intro τ
    have h1 := congrArg norm (UpperHalfPlane.petersson_slash k f f g τ)
    have hp : ∀ (F : ℍ → ℂ) (σ : ℍ), ‖petersson k F F σ‖ = ‖F σ‖ ^ 2 * σ.im ^ k := by
      intro F σ
      simp [petersson, sq, abs_of_pos σ.im_pos]
    have h2 := hp (f ∣[k] g) τ
    rw [h1, norm_mul, norm_σ, hp f] at h2
    have h3 : ‖f (g • τ)‖ ^ 2 * (g • τ).im ^ k ≤ C' ^ 2 := by
      have h4 : ‖f (g • τ)‖ * (g • τ).im ^ ((k : ℝ) / 2) ≤ C' := (hC _).trans (le_max_left _ _)
      have h5 : 0 ≤ ‖f (g • τ)‖ * (g • τ).im ^ ((k : ℝ) / 2) := by
        have := (g • τ).im_pos; positivity
      have h6 := pow_le_pow_left₀ h5 h4 2
      have h7 : ((g • τ).im ^ ((k : ℝ) / 2)) ^ 2 = (g • τ).im ^ k := by
        rw [← Real.rpow_mul_natCast (g • τ).im_pos.le]
        simp
      rw [mul_pow, h7] at h6
      exact h6
    rw [← h2]
    refine (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)).trans (le_of_eq ?_)
    rw [hD]
    simp
  have bound : ∀ τ : ℍ, ‖(f ∣[k] g) τ‖ ≤ √D / τ.im ^ ((k : ℝ) / 2) := by
    intro τ
    rw [le_div_iff₀ (by have := τ.im_pos; positivity)]
    refine Real.le_sqrt_of_sq_le ?_
    have h7 : ((τ.im) ^ ((k : ℝ) / 2)) ^ 2 = τ.im ^ k := by
      rw [← Real.rpow_mul_natCast τ.im_pos.le]
      simp
    rw [mul_pow, h7]
    exact key τ
  rw [IsZeroAtImInfty, ZeroAtFilter, tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun τ : ℍ ↦ √D / τ.im ^ ((k : ℝ) / 2)) atImInfty (nhds 0) := by
    have := (tendsto_rpow_atTop (show 0 < (k : ℝ) / 2 by have : (0 : ℝ) < k := by exact_mod_cast hk
                                                         linarith)).comp (Filter.tendsto_comap : Tendsto UpperHalfPlane.im (comap UpperHalfPlane.im atTop) atTop)
    exact (this.const_div_atTop _ )
  exact squeeze_zero (fun _ ↦ norm_nonneg _) bound hlim

/-- **Miyake, Theorem 2.1.5.** Let `Γ` be an arithmetic subgroup of `GL₂(ℝ)`, `k > 0`, and `f`
a holomorphic function on `ℍ` invariant under `∣[k] γ` for `γ ∈ Γ`. Then `f` is a cusp form for
`Γ` if and only if `|f(z)| Im(z)^{k/2}` is bounded on `ℍ`. -/
@[kb "miyake1989" "Theorem 2.1.5, p. 42"]
theorem exists_cuspForm_iff_bounded {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    (hk : 0 < k) (f : SlashInvariantForm Γ k) (hf : MDiff (f : ℍ → ℂ)) :
    (∃ F : CuspForm Γ k, ⇑F = ⇑f) ↔ ∃ C, ∀ τ : ℍ, ‖f τ‖ * τ.im ^ ((k : ℝ) / 2) ≤ C := by
  constructor
  · rintro ⟨F, hF⟩
    obtain ⟨C, hC⟩ := CuspFormClass.exists_bound F
    refine ⟨C, fun τ ↦ ?_⟩
    have hpos : 0 < τ.im ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos τ.im_pos _
    have := hC τ
    rw [le_div_iff₀ (by simpa using hpos)] at this
    have e : f τ = F τ := by rw [← SlashInvariantForm.toFun_eq_coe]; exact (congrFun hF τ).symm
    rw [e]
    simpa using this
  · intro hb
    refine ⟨{ toSlashInvariantForm := f, holo' := hf,
              zero_at_cusps' := fun {c} _ ↦ isZeroAt_of_bounded hk hb c }, rfl⟩

/-- **Miyake, Corollary 2.1.6.** Let `Γ` be an arithmetic subgroup of `GL₂(ℝ)`, `f` a cusp form
of weight `k` for `Γ`, `x₀ = g ∞` a cusp with `g ∈ SL₂(ℤ)` (Miyake's `σ = g⁻¹`, `σ x₀ = ∞`). Then there is a period
`h > 0` of `f ∣[k] g` (the width of the cusp: the generator of the strict periods of `g⁻¹ Γ g`)
such that the coefficients `a_n` of the Fourier expansion `(f ∣[k] g)(z) = Σ a_n e^{2πinz/h}`
satisfy `a_n = O(n^{k/2})`. -/
@[kb "miyake1989" "Corollary 2.1.6, p. 43"]
theorem qExpansion_slash_isBigO {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    (f : CuspForm Γ k) (g : SL(2, ℤ)) :
    ∃ h : ℝ, 0 < h ∧ (∀ τ : ℍ, (⇑f ∣[k] g) (h +ᵥ τ) = (⇑f ∣[k] g) τ) ∧
      (fun n ↦ (UpperHalfPlane.qExpansion h (⇑f ∣[k] g)).coeff n)
        =O[atTop] fun n ↦ (n : ℝ) ^ ((k : ℝ) / 2) := by
  classical
  have hI : ((ConjAct.toConjAct ((g : GL (Fin 2) ℝ))⁻¹) • Γ).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
      using! Subgroup.IsArithmetic.conj Γ (mapGL ℚ g)⁻¹
  let F := CuspForm.translate f (g : GL (Fin 2) ℝ)
  have hh : 0 < (ConjAct.toConjAct ((g : GL (Fin 2) ℝ))⁻¹ • Γ).strictWidthInfty :=
    Subgroup.strictWidthInfty_pos_iff.mpr Fact.out
  have hF : (⇑F) = ⇑f ∣[k] g := by
    rw [ModularForm.SL_slash]; rfl
  refine ⟨_, hh, fun τ ↦ ?_, ?_⟩
  · rw [← hF]
    exact SlashInvariantForm.vAdd_apply_of_mem_strictPeriods F τ
      (Subgroup.strictWidthInfty_mem_strictPeriods _)
  · rw [← hF]
    exact CuspFormClass.qExpansion_isBigO F

end ModularFormsKB.Miyake
