import ModularFormsKB.Milne.Ch6.LevelTwoCusp
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp

/-!
# Milne, Example 6.2: $F_2(j(z), j(2z)) = 0$ on $\mathbb H$

Let $G(z) = F_2(j(z), j(2z))$ (`ModularFormsKB.Milne.LevelTwo.F2`). Its three "conjugates"
$$f_1(z) = F_2(j(z), j(2z)),\quad f_2(z) = F_2(j(z), j(z/2)),\quad f_3(z) = F_2(j(z), j((z+1)/2))$$
are permuted by $z \mapsto z + 1$ and $z \mapsto -1/z$ (the cosets of $\Gamma_0(2)$ in $\Gamma(1)$), so their
elementary symmetric functions are holomorphic functions on $\mathbb H$ invariant under $\mathrm{SL}_2(\mathbb Z)$.
Since $F_2$ is symmetric, $f_2(z) = G(z/2)$ and $f_3(z) = G((z+1)/2)$, so all three tend to $0$ at $i\infty$
(`ModularFormsKB.Milne.LevelTwo.tendsto_F2_j_j2`). A level-one modular form of weight $0$ is constant
(Mathlib's `ModularFormClass.levelOne_weight_zero_const`), so the symmetric functions vanish, and $f_1 = 0$.

This proves the identity $F_2(j(z), j(2z)) = 0$ of Milne, Example 6.2 (pdf p. 90) without the Riemann surface
$X_0(2)$ (`F2_j_two_eq_zero`).
-/

open UpperHalfPlane ModularForm Filter Topology Matrix ModularGroup
open scoped MatrixGroups Manifold

noncomputable section

namespace ModularFormsKB.Milne.LevelTwo

open TauCeti.ModularForm

/-- `j` is invariant under `SL₂(ℤ)`, for its action on `ℍ`. -/
theorem jSL (γ : SL(2, ℤ)) (z : ℍ) : j (γ • z) = j z :=
  j_smul γ z

/-- `j` is invariant under $\begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(\mathbb Z)$, stated for a point
given by its coordinate. -/
theorem j_eq_of_coe {w z : ℍ} (a b c d : ℤ) (hdet : a * d - b * c = 1)
    (h : (w : ℂ) = ((a : ℂ) * z + b) / ((c : ℂ) * z + d)) : j w = j z := by
  let γ : SL(2, ℤ) := ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact hdet⟩
  have : w = γ • z := by
    ext
    rw [coe_specialLinearGroup_apply]
    simpa [γ] using h
  rw [this, jSL]

/-- The point $z/2$. -/
def half (τ : ℍ) : ℍ :=
  ⟨(τ : ℂ) / 2, by simpa using τ.im_pos⟩

/-- The point $(z+1)/2$. -/
def halfT (τ : ℍ) : ℍ :=
  ⟨((τ : ℂ) + 1) / 2, by simpa using τ.im_pos⟩

@[simp] theorem coe_half (τ : ℍ) : (half τ : ℂ) = τ / 2 := rfl

@[simp] theorem coe_halfT (τ : ℍ) : (halfT τ : ℂ) = (τ + 1) / 2 := rfl

@[simp] theorem coe_two (τ : ℍ) : (two τ : ℂ) = 2 * τ := by
  simp [two, scaleH]

/-- $G(z) = F_2(j(z), j(2z))$. -/
def G (τ : ℍ) : ℂ := F2 (j τ) (j (two τ))

/-- $f_2(z) = F_2(j(z), j(z/2))$. -/
def f2 (τ : ℍ) : ℂ := F2 (j τ) (j (half τ))

/-- $f_3(z) = F_2(j(z), j((z+1)/2))$. -/
def f3 (τ : ℍ) : ℂ := F2 (j τ) (j (halfT τ))

theorem coe_T_smul (τ : ℍ) : ((T • τ : ℍ) : ℂ) = τ + 1 := by
  rw [coe_specialLinearGroup_apply]
  simp [ModularGroup.coe_T]

theorem coe_S_smul (τ : ℍ) : ((S • τ : ℍ) : ℂ) = -1 / τ := by
  rw [coe_specialLinearGroup_apply]
  simp [ModularGroup.coe_S]

theorem G_T (τ : ℍ) : G (T • τ) = G τ := by
  unfold G
  rw [jSL]
  refine congrArg (F2 (j τ)) ?_
  apply j_eq_of_coe 1 2 0 1 (by norm_num)
  rw [coe_two, coe_two, coe_T_smul]
  push_cast
  ring

theorem f2_T (τ : ℍ) : f2 (T • τ) = f3 τ := by
  unfold f2 f3
  rw [jSL]
  congr 2
  ext
  rw [coe_half, coe_halfT, coe_T_smul]

theorem f3_T (τ : ℍ) : f3 (T • τ) = f2 τ := by
  unfold f2 f3
  rw [jSL]
  refine congrArg (F2 (j τ)) ?_
  apply j_eq_of_coe 1 1 0 1 (by norm_num)
  rw [coe_half, coe_halfT, coe_T_smul]
  push_cast
  ring

theorem G_S (τ : ℍ) : G (S • τ) = f2 τ := by
  unfold G f2
  rw [jSL]
  refine congrArg (F2 (j τ)) ?_
  apply j_eq_of_coe 0 (-1) 1 0 (by norm_num)
  have : (τ : ℂ) ≠ 0 := τ.ne_zero
  rw [coe_two, coe_half, coe_S_smul]
  push_cast
  simp only [zero_mul, zero_add, add_zero, one_mul]
  field_simp

theorem f2_S (τ : ℍ) : f2 (S • τ) = G τ := by
  unfold G f2
  rw [jSL]
  refine congrArg (F2 (j τ)) ?_
  apply j_eq_of_coe 0 (-1) 1 0 (by norm_num)
  have : (τ : ℂ) ≠ 0 := τ.ne_zero
  rw [coe_two, coe_half, coe_S_smul]
  push_cast
  simp only [zero_mul, zero_add, add_zero, one_mul]
  field_simp

theorem f3_S (τ : ℍ) : f3 (S • τ) = f3 τ := by
  unfold f3
  rw [jSL]
  refine congrArg (F2 (j τ)) ?_
  apply j_eq_of_coe 1 (-1) 2 (-1) (by norm_num)
  have : (τ : ℂ) ≠ 0 := τ.ne_zero
  rw [coe_halfT, coe_halfT, coe_S_smul]
  have hden : ((2 : ℤ) : ℂ) * (((τ : ℂ) + 1) / 2) + ((-1 : ℤ) : ℂ) = τ := by push_cast; ring
  rw [hden]
  push_cast
  field_simp
  ring

/-- $f_2(z) = G(z/2)$, by the symmetry of $F_2$. -/
theorem f2_eq (τ : ℍ) : f2 τ = G (half τ) := by
  unfold f2 G
  rw [F2_comm]
  congr 2
  ext
  simp only [coe_half, coe_two]
  ring

/-- $f_3(z) = G((z+1)/2)$, by the symmetry of $F_2$. -/
theorem f3_eq (τ : ℍ) : f3 τ = G (halfT τ) := by
  unfold f3 G
  rw [F2_comm]
  refine congrArg (F2 _) ?_
  rw [← jSL T τ]
  congr 1
  ext
  rw [coe_two, coe_halfT, coe_T_smul]
  ring

theorem tendsto_half : Tendsto half atImInfty atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  have : (UpperHalfPlane.im ∘ half) = fun τ ↦ τ.im / 2 := by
    funext τ
    change ((τ : ℂ) / 2).im = τ.im / 2
    simp
  rw [this]
  exact tendsto_comap.atTop_div_const two_pos

theorem tendsto_halfT : Tendsto halfT atImInfty atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  have : (UpperHalfPlane.im ∘ halfT) = fun τ ↦ τ.im / 2 := by
    funext τ
    change (((τ : ℂ) + 1) / 2).im = τ.im / 2
    simp
  rw [this]
  exact tendsto_comap.atTop_div_const two_pos

theorem tendsto_G : Tendsto G atImInfty (𝓝 0) := tendsto_F2_j_j2

theorem tendsto_f2 : Tendsto f2 atImInfty (𝓝 0) := by
  rw [show f2 = G ∘ half from funext f2_eq]
  exact tendsto_G.comp tendsto_half

theorem tendsto_f3 : Tendsto f3 atImInfty (𝓝 0) := by
  rw [show f3 = G ∘ halfT from funext f3_eq]
  exact tendsto_G.comp tendsto_halfT

/-! ### Holomorphy -/

/-- The element $\begin{pmatrix}a&b\\0&d\end{pmatrix}$ of $\mathrm{GL}_2(\mathbb R)$, $a, d > 0$. -/
def upper (a b d : ℝ) (ha : 0 < a) (hd : 0 < d) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d] (by simp [Matrix.det_fin_two_of, ha.ne', hd.ne'])

theorem upper_det_pos (a b d : ℝ) (ha : 0 < a) (hd : 0 < d) : 0 < (upper a b d ha hd).det.val := by
  simp [upper, Matrix.det_fin_two]; positivity

theorem coe_upper_smul (a b d : ℝ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    ((upper a b d ha hd • τ : ℍ) : ℂ) = (a * τ + b) / d := by
  rw [coe_smul_of_det_pos (upper_det_pos a b d ha hd)]
  simp [upper, num, denom]

theorem mdiff_j_comp {φ : ℍ → ℍ} (a b d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hφ : ∀ τ, (φ τ : ℂ) = (a * τ + b) / d) : MDiff (fun τ ↦ j (φ τ)) := by
  have : φ = fun τ ↦ upper a b d ha hd • τ := by
    funext τ
    ext
    rw [coe_upper_smul, hφ]
  rw [this]
  exact j_mdifferentiable.comp (mdifferentiable_smul (upper_det_pos a b d ha hd))

theorem mdiff_F2 {a b : ℍ → ℂ} (ha : MDiff a) (hb : MDiff b) : MDiff (fun τ ↦ F2 (a τ) (b τ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at ha hb ⊢
  have hF : Differentiable ℂ (fun p : ℂ × ℂ ↦ F2 p.1 p.2) := by
    unfold F2
    fun_prop
  have := hF.comp_differentiableOn (ha.prodMk hb)
  simpa only [Function.comp_def] using this

theorem mdiff_G : MDiff G :=
  mdiff_F2 j_mdifferentiable (mdiff_j_comp 2 0 1 two_pos one_pos fun τ ↦ by simp)

theorem mdiff_f2 : MDiff f2 :=
  mdiff_F2 j_mdifferentiable (mdiff_j_comp 1 0 2 one_pos two_pos fun τ ↦ by simp)

theorem mdiff_f3 : MDiff f3 :=
  mdiff_F2 j_mdifferentiable (mdiff_j_comp 1 1 2 one_pos two_pos fun τ ↦ by simp)

/-! ### The symmetric functions are constant -/

/-- A holomorphic function on $\mathbb H$ invariant under $z \mapsto z+1$ and $z \mapsto -1/z$ and tending to $0$ at
$i\infty$ vanishes identically. -/
theorem eq_zero_of_invariant {e : ℍ → ℂ} (hT : ∀ τ, e (T • τ) = e τ) (hS : ∀ τ, e (S • τ) = e τ)
    (hmd : MDiff e) (hlim : Tendsto e atImInfty (𝓝 0)) (τ : ℍ) : e τ = 0 := by
  have hinv : ∀ γ : SL(2, ℤ), e ∣[(0 : ℤ)] γ = e := by
    refine SlashInvariantForm.slash_action_generators_SL2Z ?_ ?_
    · funext τ; simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one]; exact hS τ
    · funext τ; simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one]; exact hT τ
  let F : ModularForm 𝒮ℒ 0 :=
    { toFun := e
      slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hinv γ
      holo' := hmd
      bdd_at_cusps' := fun hc ↦ (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun γ _ ↦
        (hinv γ).symm ▸ hlim.isBigO_one ℝ }
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const F
  have he : e = Function.const _ c := hc
  rw [he] at hlim
  have : c = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  simp [he, this]

/-- **$F_2(j(z), j(2z)) = 0$ for all $z \in \mathbb H$** (Milne, Example 6.2, pdf p. 90). -/
theorem F2_j_two_eq_zero (τ : ℍ) : F2 (j τ) (j (two τ)) = 0 := by
  have h2 : Tendsto (fun τ ↦ G τ * f2 τ + G τ * f3 τ + f2 τ * f3 τ) atImInfty (𝓝 0) := by
    simpa using ((tendsto_G.mul tendsto_f2).add (tendsto_G.mul tendsto_f3)).add (tendsto_f2.mul tendsto_f3)
  have e1 := eq_zero_of_invariant (e := fun τ ↦ G τ + f2 τ + f3 τ)
    (fun τ ↦ by simp only [G_T, f2_T, f3_T]; ring) (fun τ ↦ by simp only [G_S, f2_S, f3_S]; ring)
    ((mdiff_G.add mdiff_f2).add mdiff_f3) (by simpa using (tendsto_G.add tendsto_f2).add tendsto_f3) τ
  have e2 := eq_zero_of_invariant (e := fun τ ↦ G τ * f2 τ + G τ * f3 τ + f2 τ * f3 τ)
    (fun τ ↦ by simp only [G_T, f2_T, f3_T]; ring) (fun τ ↦ by simp only [G_S, f2_S, f3_S]; ring)
    (((mdiff_G.mul mdiff_f2).add (mdiff_G.mul mdiff_f3)).add (mdiff_f2.mul mdiff_f3))
    h2 τ
  have e3 := eq_zero_of_invariant (e := fun τ ↦ G τ * f2 τ * f3 τ)
    (fun τ ↦ by simp only [G_T, f2_T, f3_T]; ring) (fun τ ↦ by simp only [G_S, f2_S, f3_S]; ring)
    ((mdiff_G.mul mdiff_f2).mul mdiff_f3) (by simpa using (tendsto_G.mul tendsto_f2).mul tendsto_f3) τ
  have h : G τ ^ 3 = 0 := by
    linear_combination (G τ ^ 2) * e1 - G τ * e2 + e3
  exact pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h

end ModularFormsKB.Milne.LevelTwo
