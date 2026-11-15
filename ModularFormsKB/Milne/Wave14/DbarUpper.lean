import ModularFormsKB.Milne.Wave14.HalfPlaneTriv
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley

/-!
# The equation $\bar\partial u = \alpha$ on the upper half-plane

Part of the proof of Milne, Remark 4.26. Every smooth $\alpha$ on $\{\operatorname{Im} z > 0\}$ is
$\bar\partial u$ for a smooth $u$ (`exists_dbar_upperSet`): transport the equation to the unit disc by the inverse
Cayley transform $\varphi(w) = i(1 + w)/(1 - w)$, solve it there with Tau Ceti's Dolbeault lemma on a disc
(`TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_ball`, no support condition), and pull back by the
Cayley transform $c(z) = (z - i)/(z + i)$, using the chain rule
$\bar\partial(v \circ c) = \overline{c'} \cdot (\bar\partial v) \circ c$ for holomorphic $c$
(`conjWirtingerDeriv_comp_holomorphic`).
-/

open Set Topology Filter Metric Complex
open scoped ContDiff ComplexConjugate

noncomputable section

namespace ModularFormsKB.Milne.Wave14

/-- **Chain rule, holomorphic inner map**: `∂̄(v ∘ c)(z) = conj (c'(z)) · ∂̄v(c z)`. -/
theorem conjWirtingerDeriv_comp_holomorphic {v c : ℂ → ℂ} {z : ℂ} (hv : DifferentiableAt ℝ v (c z))
    (hc : DifferentiableAt ℂ c z) :
    TauCeti.conjWirtingerDeriv (v ∘ c) z 1 = conj (deriv c z) * TauCeti.conjWirtingerDeriv v (c z) 1 := by
  have hcR : HasFDerivAt c ((fderiv ℂ c z).restrictScalars ℝ) z :=
    hc.hasFDerivAt.restrictScalars ℝ
  have hfd : fderiv ℝ (v ∘ c) z = (fderiv ℝ v (c z)).comp ((fderiv ℂ c z).restrictScalars ℝ) :=
    (hv.hasFDerivAt.comp z hcR).fderiv
  have hlin : ∀ w : ℂ, ((fderiv ℂ c z).restrictScalars ℝ) w = w * deriv c z := by
    intro w
    simp only [ContinuousLinearMap.coe_restrictScalars']
    calc fderiv ℂ _ _ w = fderiv ℂ _ _ (w • (1 : ℂ)) := by rw [smul_eq_mul, mul_one]
      _ = _ := by rw [map_smul, fderiv_apply_one_eq_deriv, smul_eq_mul]
  rw [← smul_eq_mul, ← TauCeti.conjWirtingerDeriv_apply_eq_conj_smul_apply_one,
    TauCeti.conjWirtingerDeriv_apply, TauCeti.conjWirtingerDeriv_apply, hfd]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hlin, smul_eq_mul, one_mul]
  congr 3
  ring_nf

/-- **Chain rule, holomorphic outer map**: `∂̄(F ∘ g)(x) = F'(g x) · ∂̄g(x)`. -/
theorem conjWirtingerDeriv_holomorphic_comp {F g : ℂ → ℂ} {x : ℂ} (hF : DifferentiableAt ℂ F (g x))
    (hg : DifferentiableAt ℝ g x) :
    TauCeti.conjWirtingerDeriv (F ∘ g) x 1 = deriv F (g x) * TauCeti.conjWirtingerDeriv g x 1 := by
  have hFR : HasFDerivAt F ((fderiv ℂ F (g x)).restrictScalars ℝ) (g x) :=
    hF.hasFDerivAt.restrictScalars ℝ
  have hfd : fderiv ℝ (F ∘ g) x = ((fderiv ℂ F (g x)).restrictScalars ℝ).comp (fderiv ℝ g x) :=
    (hFR.comp x hg.hasFDerivAt).fderiv
  have hlin : ∀ w : ℂ, ((fderiv ℂ F (g x)).restrictScalars ℝ) w = w * deriv F (g x) := by
    intro w
    simp only [ContinuousLinearMap.coe_restrictScalars']
    calc fderiv ℂ _ _ w = fderiv ℂ _ _ (w • (1 : ℂ)) := by rw [smul_eq_mul, mul_one]
      _ = _ := by rw [map_smul, fderiv_apply_one_eq_deriv, smul_eq_mul]
  rw [TauCeti.conjWirtingerDeriv_apply, TauCeti.conjWirtingerDeriv_apply, hfd]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hlin, smul_eq_mul]
  ring

/-- The inverse Cayley transform. -/
def invCayley (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

/-- The Cayley transform. -/
def cayley (z : ℂ) : ℂ := (z - I) / (z + I)

theorem upperSet_eq : upperSet = UpperHalfPlane.upperHalfPlaneSet := rfl

theorem cayley_mapsTo : MapsTo cayley upperSet (ball 0 1) :=
  TauCeti.bijOn_sub_I_div_add_I_upperHalfPlaneSet.mapsTo

theorem invCayley_mapsTo : MapsTo invCayley (ball 0 1) upperSet :=
  TauCeti.bijOn_I_mul_one_add_div_one_sub_ball.mapsTo

theorem ne_one_of_mem_ball {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : w ≠ 1 := by
  rintro rfl; simp at hw

theorem add_I_ne_zero_of_mem {z : ℂ} (hz : z ∈ upperSet) : z + I ≠ 0 :=
  TauCeti.add_I_ne_zero_of_im_nonneg (le_of_lt hz)

theorem invCayley_cayley {z : ℂ} (hz : z ∈ upperSet) : invCayley (cayley z) = z :=
  TauCeti.I_mul_one_add_sub_I_div_add_I_div_one_sub (add_I_ne_zero_of_mem hz)

theorem differentiableAt_cayley {z : ℂ} (hz : z ∈ upperSet) : DifferentiableAt ℂ cayley z :=
  (TauCeti.differentiableOn_sub_I_div_add_I.differentiableAt
    ((isOpen_ne.preimage (continuous_id.add continuous_const)).mem_nhds (add_I_ne_zero_of_mem hz)))

theorem differentiableAt_invCayley {w : ℂ} (hw : w ≠ 1) : DifferentiableAt ℂ invCayley w :=
  (TauCeti.hasDerivAt_I_mul_one_add_div_one_sub hw).differentiableAt

/-- `invCayley' (cayley z) · cayley' z = 1`. -/
theorem deriv_invCayley_mul_deriv_cayley {z : ℂ} (hz : z ∈ upperSet) :
    deriv invCayley (cayley z) * deriv cayley z = 1 := by
  have hcz : cayley z ≠ 1 := ne_one_of_mem_ball (cayley_mapsTo hz)
  have h1 : HasDerivAt (invCayley ∘ cayley) (deriv invCayley (cayley z) * deriv cayley z) z :=
    (differentiableAt_invCayley hcz).hasDerivAt.comp z (differentiableAt_cayley hz).hasDerivAt
  have hev : invCayley ∘ cayley =ᶠ[𝓝 z] id := by
    filter_upwards [isOpen_upperSet.mem_nhds hz] with y hy
    exact invCayley_cayley hy
  exact h1.unique ((hasDerivAt_id z).congr_of_eventuallyEq hev)

theorem contDiffOn_invCayley : ContDiffOn ℝ ∞ invCayley (ball 0 1) := by
  have h : DifferentiableOn ℂ invCayley ({1}ᶜ : Set ℂ) := fun w hw ↦
    (differentiableAt_invCayley hw).differentiableWithinAt
  exact ((h.contDiffOn isOpen_compl_singleton).restrict_scalars ℝ).mono fun w hw ↦
    ne_one_of_mem_ball hw

theorem contDiffOn_cayley : ContDiffOn ℝ ∞ cayley upperSet := by
  have h : DifferentiableOn ℂ cayley upperSet := fun z hz ↦
    (differentiableAt_cayley hz).differentiableWithinAt
  exact (h.contDiffOn isOpen_upperSet).restrict_scalars ℝ

/-- **`∂̄u = α` on the upper half-plane.** -/
theorem exists_dbar_upperSet {α : ℂ → ℂ} (hα : ContDiffOn ℝ ∞ α upperSet) :
    ∃ u : ℂ → ℂ, ContDiffOn ℝ ∞ u upperSet ∧
      ∀ z ∈ upperSet, TauCeti.conjWirtingerDeriv u z 1 = α z := by
  let β : ℂ → ℂ := fun w ↦ α (invCayley w) * conj (deriv invCayley w)
  have hderiv : ∀ w : ℂ, w ≠ 1 → deriv invCayley w = 2 * I / (1 - w) ^ 2 := fun w hw ↦
    (TauCeti.hasDerivAt_I_mul_one_add_div_one_sub hw).deriv
  have hβ : ContDiffOn ℝ ∞ β (ball 0 1) := by
    refine (hα.comp contDiffOn_invCayley invCayley_mapsTo).mul ?_
    have hd : ContDiffOn ℝ ∞ (fun w : ℂ ↦ 2 * I / (1 - w) ^ 2) (ball 0 1) := by
      refine contDiffOn_div' contDiffOn_const ((contDiffOn_const.sub contDiffOn_id).pow 2) ?_
      intro w hw
      exact pow_ne_zero _ (sub_ne_zero.2 (ne_one_of_mem_ball hw).symm)
    refine (Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn hd).congr ?_
    intro w hw
    simp [hderiv w (ne_one_of_mem_ball hw)]
  obtain ⟨v, hv, hvβ⟩ := TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_ball
    (n := ⊤) (c := 0) (R := 1) le_top hβ
  refine ⟨v ∘ cayley, hv.comp contDiffOn_cayley cayley_mapsTo, fun z hz ↦ ?_⟩
  have hcz := cayley_mapsTo hz
  have hvd : DifferentiableAt ℝ v (cayley z) :=
    ((hv (cayley z) hcz).contDiffAt (isOpen_ball.mem_nhds hcz)).differentiableAt (by simp)
  rw [conjWirtingerDeriv_comp_holomorphic hvd (differentiableAt_cayley hz), hvβ _ hcz]
  simp only [β, invCayley_cayley hz]
  have h1 := deriv_invCayley_mul_deriv_cayley hz
  calc conj (deriv cayley z) * (α z * conj (deriv invCayley (cayley z)))
      = α z * conj (deriv invCayley (cayley z) * deriv cayley z) := by rw [map_mul]; ring
    _ = α z := by rw [h1, map_one, mul_one]

end ModularFormsKB.Milne.Wave14
