/-
# Invariance of the cycle-integral integrand

For $G$ of weight $2k$ on $\mathrm{SL}_2(\mathbb Z)$ and a binary quadratic form $Q$, the
integrand $G(z)\,Q(z,1)^k$ of the cycle integral (`BinQF.cycleIntegral`, `Abstract/Shintani.lean`) satisfies
$$ G(\gamma z)\,Q(\gamma z, 1)^k = G(z)\,(Q\circ\gamma)(z, 1)^k \qquad (\gamma \in \mathrm{SL}_2(\mathbb Z)), $$
(`BinQF.integrand_smul`), so it is invariant under the automorphs of $Q$ (`BinQF.integrand_automorph`), and the integrand of
$Q\circ\gamma$ at $z$ is that of $Q$ at $\gamma z$. These are the pointwise identities behind the base-point and class
invariance of the cycle integrals. Level-one cusp forms satisfy the hypothesis (`BinQF.cuspForm_transform`).

**Index shift.** Matrix entries are 0-based: $c = \gamma_{1,0}$, $d = \gamma_{1,1}$.
-/
import ModularFormsKB.HalfIntegral.Abstract.Shintani

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups ModularForm

local notation "ℍ" => UpperHalfPlane

namespace BinQF

/-- $\gamma z = \frac{g_{0,0}z + g_{0,1}}{g_{1,0}z + g_{1,1}}$ in $\mathbb C$, with the casts of `BinQF.evalC_comp`. -/
theorem coe_smul_SL (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ • τ : ℍ) : ℂ) = ((γ 0 0 : ℂ) * τ + γ 0 1) / ((γ 1 0 : ℂ) * τ + γ 1 1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

/-- $g_{1,0}\tau + g_{1,1} \ne 0$ on $\mathbb H$. -/
theorem denom_ne_zero_SL (γ : SL(2, ℤ)) (τ : ℍ) : (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := by
  intro h
  have hc : (γ 1 0 : ℝ) = 0 := by
    have := congrArg Complex.im h
    simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero, UpperHalfPlane.coe_im,
      zero_im] at this
    exact (mul_eq_zero.1 this).resolve_right (UpperHalfPlane.im_ne_zero τ)
  have hd : (γ 1 1 : ℝ) = 0 := by
    have := congrArg Complex.re h
    simp only [add_re, mul_re, intCast_re, intCast_im, zero_mul, sub_zero, zero_re, hc,
      UpperHalfPlane.coe_re] at this
    simpa using this
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hc' : γ 1 0 = 0 := by exact_mod_cast hc
  have hd' : γ 1 1 = 0 := by exact_mod_cast hd
  rw [hc', hd'] at hdet
  simp at hdet

/-- **Transformation of the integrand:** if $G(\gamma\tau) = (c\tau+d)^{2k}G(\tau)$, then
$G(\gamma\tau)\,Q(\gamma\tau,1)^k = G(\tau)\,(Q\circ\gamma)(\tau,1)^k$. -/
theorem integrand_smul (Q : BinQF) (k : ℕ) {G : ℍ → ℂ} (γ : SL(2, ℤ)) (τ : ℍ)
    (hG : G (γ • τ) = ((γ 1 0 : ℂ) * τ + γ 1 1) ^ (2 * k) * G τ) :
    G (γ • τ) * Q.evalC (γ • τ : ℍ) ^ k = G τ * (Q.comp γ).evalC τ ^ k := by
  have hd := denom_ne_zero_SL γ τ
  rw [hG, coe_smul_SL, evalC_smul Q (γ : Matrix (Fin 2) (Fin 2) ℤ) hd, div_pow, pow_mul]
  field_simp

/-- **Invariance under automorphs:** for $t^2 - \Delta u^2 = 4$ and $g$ the automorph,
$G(g\tau)\,Q(g\tau,1)^k = G(\tau)\,Q(\tau,1)^k$. -/
theorem integrand_automorph (Q : BinQF) (k : ℕ) {G : ℍ → ℂ} {t u : ℤ} (h : t ^ 2 - Q.disc * u ^ 2 = 4) (τ : ℍ)
    (hG : G (Q.automorphSL h • τ) =
      (((Q.automorphSL h) 1 0 : ℂ) * τ + (Q.automorphSL h) 1 1) ^ (2 * k) * G τ) :
    G (Q.automorphSL h • τ) * Q.evalC (Q.automorphSL h • τ : ℍ) ^ k = G τ * Q.evalC τ ^ k := by
  rw [integrand_smul Q k _ τ hG, comp_automorphSL]

/-- **Level-one cusp forms of weight $2k$** satisfy $G(\gamma\tau) = (c\tau+d)^{2k}G(\tau)$ for all $\gamma \in \mathrm{SL}_2(\mathbb Z)$. -/
theorem cuspForm_transform {k : ℕ} (G : CuspForm 𝒮ℒ (2 * k : ℕ)) (γ : SL(2, ℤ)) (τ : ℍ) :
    G (γ • τ) = ((γ 1 0 : ℂ) * τ + γ 1 1) ^ (2 * k) * G τ := by
  have h := SlashInvariantForm.slash_action_eqn'' G
    (γ := Matrix.SpecialLinearGroup.mapGL ℝ γ) (MonoidHom.mem_range.2 ⟨γ, rfl⟩) τ
  rw [show γ • τ = (Matrix.SpecialLinearGroup.mapGL ℝ γ) • τ from rfl, h, zpow_natCast]
  simp [UpperHalfPlane.denom]

end BinQF

end ModularFormsKB.HalfIntegral
