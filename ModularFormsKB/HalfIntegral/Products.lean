/-
# Products and powers of half-integral weight forms

If $f \in M_{k+1/2}(4N, \chi)$ and $g \in M_{l+1/2}(4N, \psi)$ then by `thetaMult_sq`
$$(fg)(\gamma\tau) = \chi\psi(d)\,\chi_{-4}(d)^{k+l+1}\,(c\tau+d)^{k+l+1}\,(fg)(\tau) \qquad (\gamma \in \Gamma_0(4N))$$
(`HalfIntTransforms.mul`), and $|c\tau+d|^{-(k+l+1)}|(fg)(\gamma\tau)|$ is the product of the two cusp quantities. On
$\Gamma_1(4N)$ all three characters are trivial ($d \equiv 1 \bmod 4N$), so $fg$ is a modular form of weight $k+l+1$ on
$\Gamma_1(4N)$ in Mathlib's sense (`halfIntMul`). Mathlib's `ModularForm` carries no character; the character
$\chi\psi\chi_{-4}^{k+l+1}$ on $\Gamma_0(4N)$ is recorded separately by `HalfIntTransforms.mul`.

For odd powers of a weight-½ form with trivial character: $f \in M_{1/2}(4N, 1) \Rightarrow f^{2k+1} \in M_{k+1/2}(4N, 1)$
(`IsHalfIntModularForm.pow_odd`). (In Shimura's normalization, with $j^{2k+1}$ in the law, $\theta^{2k+1}$ has trivial
character; the character $\chi_{-4}^{\,m}$ appears for even powers $\theta^{2m}$, of integral weight $m$.)
-/
import ModularFormsKB.HalfIntegral.Law
import ModularFormsKB.HalfIntegral.Forms

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup UpperHalfPlane
open scoped Manifold ModularForm

/-- The bottom-right entry of $\gamma \in \Gamma_0(M)$ is a unit mod $M$. -/
lemma isUnit_d_of_mem_Gamma0 {M : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : IsUnit ((γ 1 1 : ℤ) : ZMod M) := by
  have h0 : ((γ 1 0 : ℤ) : ZMod M) = 0 := (Gamma0_mem).mp hγ
  refine IsUnit.of_mul_eq_one ((γ 0 0 : ℤ) : ZMod M) ?_
  have : (((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ)) : ZMod M) = 1 := by rw [det_entries]; simp
  push_cast at this
  rw [h0] at this
  simpa [mul_comm] using this

lemma Gamma0_mul_le (N : ℕ) : Gamma0 (4 * N) ≤ Gamma0 4 := by
  intro γ hγ
  rw [Gamma0_mem] at hγ ⊢
  have h' : ((γ 1 0 : ℤ) : ZMod (4 * N)) = 0 := hγ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h' ⊢
  exact dvd_trans (by exact_mod_cast Dvd.intro N rfl) h'

/-- $\|c\tau+d\|^{-(k+1/2)} \cdot \|c\tau+d\|^{-(l+1/2)} = \|c\tau+d\|^{-(k+l+1)}$. -/
lemma rpow_half_mul_rpow_half {x : ℝ} (hx : 0 < x) (k l : ℕ) :
    x ^ (-((k : ℝ) + 1 / 2)) * x ^ (-((l : ℝ) + 1 / 2)) = (x ^ (k + l + 1))⁻¹ := by
  rw [← Real.rpow_add hx, ← Real.rpow_natCast, ← Real.rpow_neg hx.le]
  congr 1; push_cast; ring

lemma norm_mul_slash (k l : ℕ) (f g : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    ‖((f * g) ∣[((k + l + 1 : ℕ) : ℤ)] γ) τ‖ = cuspNorm k f γ τ * cuspNorm l g γ τ := by
  rw [ModularForm.SL_slash_apply]
  have hD : denom γ τ = (γ 1 0 : ℂ) * τ + γ 1 1 := by simp [UpperHalfPlane.denom]
  have hpos : 0 < ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ := by
    rw [← hD]; exact norm_pos_iff.mpr (denom_ne_zero γ τ)
  unfold cuspNorm
  rw [norm_mul, Pi.mul_apply, norm_mul, norm_zpow, hD, zpow_neg, zpow_natCast]
  rw [show ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-((k : ℝ) + 1 / 2)) * ‖f (γ • τ)‖ *
      (‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-((l : ℝ) + 1 / 2)) * ‖g (γ • τ)‖) =
      (‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-((k : ℝ) + 1 / 2)) * ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-((l : ℝ) + 1 / 2))) *
      (‖f (γ • τ)‖ * ‖g (γ • τ)‖) by ring, rpow_half_mul_rpow_half hpos]
  ring

lemma isBounded_mul_of_nonneg {a b : ℍ → ℝ} (ha : IsBoundedAtImInfty a) (hb : IsBoundedAtImInfty b)
    (_ha0 : ∀ τ, 0 ≤ a τ) (_hb0 : ∀ τ, 0 ≤ b τ) : IsBoundedAtImInfty (fun τ ↦ a τ * b τ) := by
  rw [isBoundedAtImInfty_iff] at *
  obtain ⟨M, A, hA⟩ := ha
  obtain ⟨M', A', hA'⟩ := hb
  refine ⟨M * M', max A A', fun z hz => ?_⟩
  have h1 := hA z (le_trans (le_max_left _ _) hz)
  have h2 := hA' z (le_trans (le_max_right _ _) hz)
  rw [Real.norm_eq_abs] at *
  rw [abs_mul] at *
  exact mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)

/-- **The product of two half-integral weight forms is a modular form of weight $k+l+1$ on $\Gamma_1(4N)$**
(Mathlib's `ModularForm`): for $f \in M_{k+1/2}(4N,\chi)$ and $g \in M_{l+1/2}(4N,\psi)$. -/
noncomputable def halfIntMul {k l N : ℕ} {χ ψ : DirichletCharacter ℂ (4 * N)} {f g : ℍ → ℂ}
    (hf : IsHalfIntModularForm k N χ f) (hg : IsHalfIntModularForm l N ψ g) :
    ModularForm (Gamma1 (4 * N)) ((k + l + 1 : ℕ) : ℤ) where
  toFun := f * g
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hA
    have hγ0 : γ ∈ Gamma0 (4 * N) := Gamma1_in_Gamma0 _ hγ
    have hd1 : ((γ 1 1 : ℤ) : ZMod (4 * N)) = 1 := ((Gamma1_mem _ γ).mp hγ).2.1
    have hd4 : ((γ 1 1 : ℤ) : ZMod 4) = 1 := by
      have := congrArg (ZMod.castHom (Dvd.intro N rfl : 4 ∣ 4 * N) (ZMod 4)) hd1
      simpa using this
    change (f * g) ∣[((k + l + 1 : ℕ) : ℤ)] γ = f * g
    funext τ
    rw [ModularForm.slash_action_eq'_iff]
    have h := HalfIntTransforms.mul hf.transforms hg.transforms γ hγ0 τ
    simp only [Pi.mul_apply]
    rw [h, hd1, hd4]
    simp only [map_one, one_mul, Int.cast_one, one_pow, zpow_natCast]
  holo' := hf.holo.mul hg.holo
  bdd_at_cusps' {c} hc := by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z (hc.mono (by
      intro x hx
      obtain ⟨γ, -, rfl⟩ := Subgroup.mem_map.mp hx
      exact ⟨γ, rfl⟩))]
    intro γ _
    have hb := isBounded_mul_of_nonneg (hf.bdd_at_cusps γ) (hg.bdd_at_cusps γ)
      (cuspNorm_nonneg k f γ) (cuspNorm_nonneg l g γ)
    rw [isBoundedAtImInfty_iff] at hb ⊢
    obtain ⟨M, A, hA⟩ := hb
    refine ⟨M, A, fun τ hτ => ?_⟩
    have := hA τ hτ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (cuspNorm_nonneg k f γ τ)
      (cuspNorm_nonneg l g γ τ))] at this
    convert this using 1
    exact norm_mul_slash k l f g γ τ

@[simp]
lemma coe_halfIntMul {k l N : ℕ} {χ ψ : DirichletCharacter ℂ (4 * N)} {f g : ℍ → ℂ}
    (hf : IsHalfIntModularForm k N χ f) (hg : IsHalfIntModularForm l N ψ g) :
    (halfIntMul hf hg : ℍ → ℂ) = f * g := rfl

/-- **Odd powers:** $f \in M_{1/2}(4N, 1) \Rightarrow f^{2k+1} \in M_{k+1/2}(4N, 1)$. -/
theorem IsHalfIntModularForm.pow_odd {N : ℕ} {f : ℍ → ℂ} (hf : IsHalfIntModularForm 0 N 1 f) (k : ℕ) :
    IsHalfIntModularForm k N 1 (f ^ (2 * k + 1)) := by
  refine ⟨hf.holo.pow _, fun γ hγ τ => ?_, fun γ => ?_⟩
  · have h := hf.transforms γ hγ τ
    rw [MulChar.one_apply (isUnit_d_of_mem_Gamma0 hγ)] at h ⊢
    simp only [Pi.pow_apply, h, Nat.mul_zero, Nat.zero_add, pow_one, one_mul]
    rw [mul_pow]
  · have hb := hf.bdd_at_cusps γ
    rw [isBoundedAtImInfty_iff] at hb ⊢
    obtain ⟨M, A, hA⟩ := hb
    refine ⟨M ^ (2 * k + 1), A, fun τ hτ => ?_⟩
    have h1 := hA τ hτ
    have e : cuspNorm k (f ^ (2 * k + 1)) γ τ = cuspNorm 0 f γ τ ^ (2 * k + 1) := by
      unfold cuspNorm
      rw [Pi.pow_apply, norm_pow, mul_pow, ← Real.rpow_natCast (_ ^ _), ← Real.rpow_mul (norm_nonneg _)]
      congr 2; push_cast; ring
    rw [Real.norm_eq_abs, abs_of_nonneg (cuspNorm_nonneg _ _ _ _), e]
    rw [Real.norm_eq_abs, abs_of_nonneg (cuspNorm_nonneg _ _ _ _)] at h1
    exact pow_le_pow_left₀ (cuspNorm_nonneg _ _ _ _) h1 _

end ModularFormsKB.HalfIntegral
