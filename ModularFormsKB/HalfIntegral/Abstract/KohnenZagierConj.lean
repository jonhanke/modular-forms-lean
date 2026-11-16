/-
# The conjugate form $\hat g(\tau) = \overline{g(-\bar\tau)}$ on Kohnen's plus space

For the theta multiplier and $g \in S_{k+1/2}(4)$:
- `conjForm g` $:= \tau \mapsto \overline{g(J\tau)}$ with $J\tau = -\bar\tau$ is again a cusp form
  (`conjForm_mem_cuspForms`): holomorphic (Mathlib `MDifferentiable.slash` for the matrix $J$), it satisfies the
  transformation law because $J\gamma\tau = \gamma^*J\tau$ and $j(\gamma^*, J\tau) = \overline{j(\gamma, \tau)}$
  (`thetaMult_conjJ`), and the cusp conditions transfer because $\operatorname{Im}J\tau = \operatorname{Im}\tau$;
- $q$-expansion: $g = \sum a(n)q^n$ gives $\hat g = \sum \overline{a(n)}q^n$ (`hasQExp_conjForm`);
- the plus space is preserved (`conjForm_mem_plus`), since the plus condition only looks at indices.
-/
import ModularFormsKB.HalfIntegral.Abstract.KohnenZagierReal
import ModularFormsKB.HalfIntegral.Abstract.KohnenReduction

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup UpperHalfPlane TauCeti TauCeti.UpperHalfPlane
open scoped ComplexConjugate Real ModularForm

/-- **The conjugate function** $\hat g(\tau) = \overline{g(-\bar\tau)}$. -/
noncomputable def conjForm (g : ℍ → ℂ) : ℍ → ℂ := fun τ ↦ conj (g (J • τ))

theorem conjForm_conjForm (g : ℍ → ℂ) : conjForm (conjForm g) = g := by
  funext τ
  have : J • J • τ = τ := by rw [smul_smul, ← sq, J_sq, one_smul]
  simp only [conjForm, Complex.conj_conj, this]

theorem conjForm_eq_slash (g : ℍ → ℂ) : conjForm g = g ∣[(0 : ℤ)] J := by
  funext τ
  exact (slash_J_apply 0 g τ).symm

/-- $J$ intertwines $\gamma$ and $\gamma^*$ on $\mathbb H$. -/
theorem J_smul_sl (γ : SL(2, ℤ)) (τ : ℍ) :
    J • (γ • τ) = Matrix.SpecialLinearGroup.conjJ γ • (J • τ) := by
  have h := Matrix.SpecialLinearGroup.J_mul_mapGL γ
  calc J • (γ • τ) = J • (Matrix.SpecialLinearGroup.mapGL ℝ γ • τ) := by
        rfl
    _ = (J * Matrix.SpecialLinearGroup.mapGL ℝ γ) • τ := (mul_smul _ _ _).symm
    _ = (Matrix.SpecialLinearGroup.mapGL ℝ (Matrix.SpecialLinearGroup.conjJ γ) * J) • τ := by rw [h]
    _ = Matrix.SpecialLinearGroup.conjJ γ • (J • τ) := by
        rw [mul_smul]; rfl

theorem conj_one_dirichlet {n : ℕ} (x : ZMod n) : conj ((1 : DirichletCharacter ℂ n) x) = (1 : DirichletCharacter ℂ n) x := by
  by_cases hx : IsUnit x
  · simp [MulChar.one_apply hx]
  · simp [MulChar.map_nonunit _ hx]

theorem hasQExp_conjForm {g : ℍ → ℂ} {a : ℕ → ℂ} (h : Abstract.HasQExp g a) :
    Abstract.HasQExp (conjForm g) (fun n ↦ conj (a n)) := fun τ ↦ by
  have h1 := Complex.hasSum_conj'.2 (h (J • τ))
  have hf : (fun n : ℕ ↦ conj (a n) * cexp (2 * π * Complex.I * n * τ)) =
      fun n ↦ conj (a n * cexp (2 * π * Complex.I * n * ((J • τ : ℍ) : ℂ))) := by
    funext n
    rw [map_mul, ← Complex.exp_conj]
    congr 2
    rw [coe_J_smul]
    simp only [map_mul, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast, Complex.conj_conj]
    ring
  show HasSum (fun n : ℕ ↦ conj (a n) * cexp (2 * π * Complex.I * n * τ)) (conj (g (J • τ)))
  rw [hf]
  exact h1

theorem conjForm_isCuspForm {k : ℕ} {g : ℍ → ℂ} (hg : thetaMultiplierSystem.IsCuspForm k 1 1 g) :
    thetaMultiplierSystem.IsCuspForm k 1 1 (conjForm g) where
  holo := by
    rw [conjForm_eq_slash]
    exact MDifferentiable.slash hg.holo 0 J
  transforms γ hγ τ := by
    have hγ' : Matrix.SpecialLinearGroup.conjJ γ ∈ Gamma0 (4 * 1) := TauCeti.conjJ_mem_Gamma0 hγ
    have e := hg.transforms _ hγ' (J • τ)
    have hj : thetaMultiplierSystem.j (Matrix.SpecialLinearGroup.conjJ γ) (J • τ) =
        conj (thetaMultiplierSystem.j γ τ) := by
      simpa using thetaMult_conjJ (by simpa using hγ) τ
    show conj (g (J • (γ • τ))) = _
    rw [J_smul_sl, e, hj, map_mul, map_mul, map_pow, Complex.conj_conj]
    have : (Matrix.SpecialLinearGroup.conjJ γ) 1 1 = γ 1 1 := rfl
    rw [this, conj_one_dirichlet]
    rfl
  zero_at_cusps γ := by
    have hz := hg.zero_at_cusps (Matrix.SpecialLinearGroup.conjJ γ)
    have hden : ∀ τ : ℍ, ‖(((Matrix.SpecialLinearGroup.conjJ γ) 1 0 : ℤ) : ℂ) * ((J • τ : ℍ) : ℂ) +
        (((Matrix.SpecialLinearGroup.conjJ γ) 1 1 : ℤ) : ℂ)‖ = ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ := by
      intro τ
      have e10 : (Matrix.SpecialLinearGroup.conjJ γ) 1 0 = -γ 1 0 := rfl
      have e11 : (Matrix.SpecialLinearGroup.conjJ γ) 1 1 = γ 1 1 := rfl
      have : ((-γ 1 0 : ℤ) : ℂ) * (-conj (τ : ℂ)) + (γ 1 1 : ℂ) = conj ((γ 1 0 : ℂ) * τ + γ 1 1) := by
        simp only [Int.cast_neg, map_add, map_mul, map_intCast]; ring
      rw [e10, e11, coe_J_smul, this]
      exact RCLike.norm_conj _
    have heq : ∀ τ : ℍ, Abstract.cuspNorm k (conjForm g) γ τ =
        Abstract.cuspNorm k g (Matrix.SpecialLinearGroup.conjJ γ) (J • τ) := by
      intro τ
      simp only [Abstract.cuspNorm, conjForm, J_smul_sl, hden]
      rw [RCLike.norm_conj]
    rw [isZeroAtImInfty_iff] at hz ⊢
    intro ε hε
    obtain ⟨A, hA⟩ := hz ε hε
    refine ⟨A, fun τ hτ ↦ ?_⟩
    rw [heq]
    exact hA (J • τ) (by rwa [J_smul_im])

/-- **The plus space is preserved by conjugation.** -/
theorem conjForm_mem_plus {k : ℕ} {g : ℍ → ℂ} (hg : g ∈ thetaMultiplierSystem.plusCuspForms k 1 1) :
    conjForm g ∈ thetaMultiplierSystem.plusCuspForms k 1 1 := by
  obtain ⟨hc, a, ha, hpl⟩ := hg
  refine ⟨conjForm_isCuspForm hc, fun n ↦ conj (a n), hasQExp_conjForm ha, fun n hn ↦ ?_⟩
  show conj (a n) = 0
  rw [hpl n hn, map_zero]

end ModularFormsKB.HalfIntegral
