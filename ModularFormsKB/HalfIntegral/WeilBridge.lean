/-
# The named input `WeilConverse` from the proved Weil converse theorem

In an earlier version of this library, Weil's converse theorem was the named input `WeilConverse`
(`Abstract/ShimuraWeil.lean`), with auxiliary definitions reconstructed from Miyake §4.3 because the Miyake
development could not be imported there. Here it is proved from `Miyake.weil_cusp` (Miyake 1989 `miyake1989`,
Thm. 4.3.15) and the Weil set `Miyake.exists_weilSet`. The comparison of the definitions:

* `CoeffGrowth`, `qSeries`: identical to `Miyake.CoeffGrowth`, `Miyake.qSeries`.
* `HeckeCondition k N C a b` (two entire functions $E_a, E_b$, bounded on vertical strips, with $E_a(k-s) = CE_b(s)$)
  implies `Miyake.HeckeCondition k N C a b` (one entire function $\Phi$ with both expansions) when $C \ne 0$: take
  $\Phi = E_a$ (`heckeCondition_miyake`). The gamma factors agree (`gammaFactor N s * LSeries a s = Miyake.completedL`).
* `TwistedHeckeCondition k N ψ C a b` (Hecke's condition at level $Nm^2$ for the twisted sequences, constant $i^kC$)
  implies `Miyake.TwistedHeckeCondition k N ψ C a b` for $m > 1$, since then $\psi(0) = 0$ kills the constant terms and
  $\sqrt{Nm^2} = m\sqrt N$ (`twistedHeckeCondition_miyake`).
* `gaussW` (a sum over $u < m$) equals `Miyake.gaussW` (Mathlib's `gaussSum` with `ZMod.stdAddChar`), so the Weil
  constants agree (`gaussW_eq_miyake`, `weilConstant_eq_miyake`).
* `Miyake.IsCuspFormChar k N χ f` implies `IsIntCuspForm k N χ f` (`isIntCuspForm_of_isCuspFormChar`).
* The Weil set of `WeilConverse` is $\{m : m \text{ an odd prime}, (m, N) = 1\}$, the set of `Miyake.exists_weilSet`.

So the hypotheses of `WeilConverse` are at least as strong as Miyake's and its conclusion is weaker: `weilConverse` proves the
structure. Consequence: Shimura's theorem needs only the twisted functional equations (`shimuraTheorem_of_twistedFE`).
-/
import ModularFormsKB.HalfIntegral.HeckeBound
import ModularFormsKB.Miyake.Sec4_3.WeilTheorem

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup
open scoped Real ModularForm

local notation "ℍ" => UpperHalfPlane

private lemma gammaFactor_mul_eq (N : ℕ) (a : ℕ → ℂ) (s : ℂ) :
    gammaFactor N s * LSeries a s = Miyake.completedL (N : ℝ) a s := by
  rfl

private lemma gammaFactor_twist_eq {N m : ℕ} (ψ : DirichletCharacter ℂ m) (a : ℕ → ℂ) (s : ℂ) :
    gammaFactor (N * m ^ 2) s * LSeries (twist ψ a) s = Miyake.twistedCompletedL (N : ℝ) ψ a s := by
  have hsq : Real.sqrt ((N * m ^ 2 : ℕ) : ℝ) = (m : ℝ) * Real.sqrt N := by
    push_cast
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    ring
  unfold gammaFactor Miyake.twistedCompletedL
  rw [hsq]
  try rfl

/-- The Hecke condition here (two entire functions) gives Miyake's condition (B) (one entire function), for a
nonzero constant. -/
theorem heckeCondition_miyake {k N : ℕ} {C : ℂ} (hC : C ≠ 0) {a b : ℕ → ℂ} (h : HeckeCondition k N C a b) :
    Miyake.HeckeCondition k N C a b := by
  obtain ⟨Ea, Eb, hEa, hEb, hBa, hBb, ⟨σ, hσ⟩, hfe⟩ := h
  refine ⟨Ea, hEa, hBa, σ, ?_, ?_⟩
  · intro s hs
    rw [(hσ s hs).1, gammaFactor_mul_eq]
    simp only [Complex.ofReal_natCast]
  · intro s hs
    have ht : σ < ((k : ℂ) - s).re := by
      simp only [Complex.sub_re, Complex.natCast_re]
      simpa using hs
    have h1 := (hσ _ ht).2
    have h2 := hfe ((k : ℂ) - s)
    have h3 : (k : ℂ) - ((k : ℂ) - s) = s := by ring
    rw [h3] at h2
    rw [h3] at h1
    rw [h2, h1, ← gammaFactor_mul_eq]
    simp only [Complex.ofReal_natCast]
    field_simp
    ring

/-- The twisted Hecke condition here (Hecke's condition at level $Nm^2$ for the twisted sequences) gives Miyake's
condition $(B_\psi)$ of Lemma 4.3.9, for a character of modulus $m > 1$. -/
theorem twistedHeckeCondition_miyake {k N m : ℕ} (hm : 1 < m) (ψ : DirichletCharacter ℂ m) {C : ℂ} {a b : ℕ → ℂ}
    (h : TwistedHeckeCondition k N ψ C a b) : Miyake.TwistedHeckeCondition k N ψ C a b := by
  obtain ⟨Ea, Eb, hEa, hEb, hBa, hBb, ⟨σ, hσ⟩, hfe⟩ := h
  have : Fact (1 < m) := ⟨hm⟩
  have ha0 : twist ψ a 0 = 0 := by simp [twist, MulChar.map_zero]
  have hb0 : twist ψ⁻¹ b 0 = 0 := by simp [twist, MulChar.map_zero]
  refine ⟨Ea, hEa, hBa, σ, ?_, ?_⟩
  · intro s hs
    rw [(hσ s hs).1, ha0, hb0]
    simp only [zero_div, mul_zero, add_zero]
    exact gammaFactor_twist_eq ψ a s
  · intro s hs
    have ht : σ < ((k : ℂ) - s).re := by
      simp only [Complex.sub_re, Complex.natCast_re]
      exact hs
    have h1 := (hσ _ ht).2
    have h2 := hfe ((k : ℂ) - s)
    have h3 : (k : ℂ) - ((k : ℂ) - s) = s := by ring
    rw [h3] at h2
    rw [h2, h1, ha0, hb0]
    simp only [zero_div, mul_zero, add_zero]
    rw [gammaFactor_twist_eq ψ⁻¹ b]

/-- The two Gauss sums agree: $\sum_{u<m}\psi(u)e^{2\pi iu/m}$ is Mathlib's `gaussSum ψ ZMod.stdAddChar`. -/
theorem gaussW_eq_miyake {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) : gaussW ψ = Miyake.gaussW ψ := by
  unfold gaussW Miyake.gaussW gaussSum
  refine Finset.sum_nbij' (fun u : ℕ ↦ (u : ZMod m)) (fun a : ZMod m ↦ a.val) ?_ ?_ ?_ ?_ ?_
  · intro u _; exact Finset.mem_univ _
  · intro a _; exact Finset.mem_range.2 (ZMod.val_lt a)
  · intro u hu; exact ZMod.val_cast_of_lt (Finset.mem_range.1 hu)
  · intro a _; exact ZMod.natCast_zmod_val a
  · intro u _
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast]

/-- The two Weil constants agree. -/
theorem weilConstant_eq_miyake {N m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ m) :
    weilConstant χ ψ = Miyake.weilConstant χ ψ := by
  unfold weilConstant Miyake.weilConstant
  rw [gaussW_eq_miyake ψ, gaussW_eq_miyake ψ⁻¹]

/-- A cusp form in Miyake's sense (`Miyake.IsCuspFormChar`, built on Mathlib's `CuspForm` for $\Gamma_1(N)$) is a cusp
form in the sense of `IsIntCuspForm`, for $N \ge 1$. (For $N = 0$, $\Gamma_1(0)$ has infinite index, Mathlib's
`CuspForm` only asks vanishing at $\infty$, and the implication fails.) -/
theorem isIntCuspForm_of_isCuspFormChar {k N : ℕ} (hN : 0 < N) (χ : DirichletCharacter ℂ N) {f : ℍ → ℂ}
    (h : Miyake.IsCuspFormChar k N χ f) : IsIntCuspForm k N χ f := by
  obtain ⟨⟨F, rfl⟩, hs⟩ := h
  have hd : ∀ (γ : SL(2, ℤ)) (τ : ℍ),
      UpperHalfPlane.denom γ τ = (γ 1 0 : ℂ) * τ + γ 1 1 := fun γ τ ↦ ModularGroup.denom_apply γ τ
  refine ⟨CuspFormClass.holo F, ?_, ?_⟩
  · intro γ hγ τ
    have h1 := congrFun (hs γ hγ) τ
    rw [ModularForm.SL_slash_apply] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    have hne := UpperHalfPlane.denom_ne_zero γ τ
    rw [hd] at h1 hne
    have h2 : F (γ • τ) = F (γ • τ) * ((γ 1 0 : ℂ) * τ + γ 1 1) ^ (-(k : ℤ)) *
        ((γ 1 0 : ℂ) * τ + γ 1 1) ^ k := by
      rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hne]
      simp
    rw [h2, h1]
    ring
  · intro γ
    have : NeZero N := ⟨hN.ne'⟩
    have h := CuspFormClass.zero_at_infty_slash F γ
    rw [UpperHalfPlane.IsZeroAtImInfty, Filter.ZeroAtFilter, tendsto_zero_iff_norm_tendsto_zero] at h ⊢
    refine h.congr (fun τ ↦ ?_)
    rw [Real.norm_of_nonneg (by positivity), ModularForm.SL_slash_apply, norm_mul, norm_zpow, hd,
      Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, zpow_neg, zpow_natCast, mul_comm]

/-- **Weil's converse theorem, cusp-form part, as `WeilConverse` states it** (Weil 1967 `weil1967`; Miyake 1989
`miyake1989`, Thm. 4.3.15): the named input `WeilConverse` holds, by `Miyake.weil_cusp` with the Weil set of
`Miyake.exists_weilSet`. -/
@[kb "miyake1989" "Thm. 4.3.15: Weil's converse theorem, cusp-form part, in the formulation of WeilConverse; from weil_cusp"]
theorem weilConverse : WeilConverse := by
  refine ⟨fun k N hk hN χ hχ a b ha hb hH hTw δ hδ hL ↦ ?_⟩
  have hL' : LSeriesSummable a ((k : ℂ) - (δ : ℂ)) := by
    have : (((k : ℝ) - δ : ℝ) : ℂ) = (k : ℂ) - (δ : ℂ) := by push_cast; ring
    rwa [this] at hL
  obtain ⟨h1, h2⟩ := Miyake.weil_cusp hk hN χ hχ ha hb (Miyake.exists_weilSet hN)
    (heckeCondition_miyake (pow_ne_zero _ I_ne_zero) hH)
    (fun m _ hm ψ hψ ↦ by
      rw [← weilConstant_eq_miyake]
      exact twistedHeckeCondition_miyake hm.1.one_lt ψ (hTw m hm.1 hm.2.1 hm.2.2 ψ hψ))
    hδ hL'
  exact ⟨isIntCuspForm_of_isCuspFormChar hN χ h1, isIntCuspForm_of_isCuspFormChar hN χ⁻¹ h2⟩

/-- **Shimura's theorem from the twisted functional equations alone** (Shimura 1973 `shimura1973`, Main Theorem
[unverified]): `shimuraTheorem_of_weil_fe` with `WeilConverse` discharged by `weilConverse`. -/
@[kb "shimura1973" "Main Theorem, reduced to the twisted functional equations (Weil's theorem and Hecke's bound proved) [unverified]"]
theorem shimuraTheorem_of_twistedFE (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (hN : 0 < N)
    (hFE : ShimuraTwistedFE M k N χ) : ShimuraTheorem M k N χ :=
  shimuraTheorem_of_weil_fe M k N χ hN weilConverse hFE

end ModularFormsKB.HalfIntegral
