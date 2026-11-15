import ModularFormsKB.Milne.Wave14.DbarUpper
import ModularFormsKB.Milne.Ch4.UncondLineBundle
import TauCeti.Geometry.Manifold.Complex.Analytic

/-!
# Milne, Remark 4.26: every holomorphic line bundle on $\mathbb H$ is trivial

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Section 4, Remark 4.26 (pdf p. 59).

**The multiplicative Cousin problem on $\mathbb H$** (`multiplicativeCousinStatement`, the library's named input
`MultiplicativeCousinStatement`, now proved): every holomorphic nowhere-vanishing cocycle $g_{ij}$ on an open cover
of $\mathbb H$ is $h_i / h_j$ with $h_i$ holomorphic and nowhere zero. Hence **Remark 4.26**
(`lineBundlesOnHTrivial`) unconditionally, through the library's reduction `lineBundlesOnHTrivial_of_cousin`.

Proof (`exists_holomorphic_triv`), for a holomorphic cocycle $G_{ij}$ on an open cover of
$\{\operatorname{Im} z > 0\} \subseteq \mathbb C$:
1. $G$ is smoothly trivial, $G_{ij} = s_i/s_j$ (`smoothTriv_upperHalfPlane`, gluing along chains of rectangles).
2. $\bar\partial s_i / s_i = \bar\partial s_j / s_j$ on overlaps, since $\bar\partial G_{ij} = 0$; so these glue to a
   smooth $\alpha$ on the half-plane.
3. Solve $\bar\partial v = \alpha$ (`exists_dbar_upperSet`); then $h_i = s_i e^{-v}$ has
   $\bar\partial h_i = e^{-v}(\bar\partial s_i - s_i \alpha) = 0$, so it is holomorphic, and $h_i/h_j = G_{ij}$.

Milne gives no proof (he cites the vanishing of $H^1(\mathbb H, \mathcal O^\times)$); this is the standard
exponential-sequence argument (Forster, *Lectures on Riemann Surfaces*, §30) with the topological step done by
hand.
-/

open Set Topology Filter Metric Complex
open scoped ContDiff Manifold

noncomputable section

namespace ModularFormsKB.Milne.Wave14

variable {ι : Type*} {U : ι → Set ℂ} {G : ι → ι → ℂ → ℂ}

theorem contDiffAt_of_contDiffOn_open {f : ℂ → ℂ} {s : Set ℂ} (hf : ContDiffOn ℝ ∞ f s) (hs : IsOpen s)
    {z : ℂ} (hz : z ∈ s) : ContDiffAt ℝ ∞ f z :=
  hf.contDiffAt (hs.mem_nhds hz)

theorem differentiableAt_of_contDiffOn_open {f : ℂ → ℂ} {s : Set ℂ} (hf : ContDiffOn ℝ ∞ f s)
    (hs : IsOpen s) {z : ℂ} (hz : z ∈ s) : DifferentiableAt ℝ f z :=
  (contDiffAt_of_contDiffOn_open hf hs hz).differentiableAt (by simp)

/-- **The holomorphic multiplicative Cousin problem on the upper half-plane** (in `ℂ`). -/
theorem exists_holomorphic_triv (hU : ∀ i, IsOpen (U i)) (hcov : ∀ z ∈ upperSet, ∃ i, z ∈ U i)
    (hG : ∀ i j, DifferentiableOn ℂ (G i j) (U i ∩ U j)) (hG0 : ∀ i j, ∀ x ∈ U i ∩ U j, G i j x ≠ 0)
    (hGm : ∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k, G i k x = G i j x * G j k x) :
    ∃ H : ι → ℂ → ℂ, (∀ i, DifferentiableOn ℂ (H i) (U i ∩ upperSet)) ∧
      (∀ i, ∀ x ∈ U i ∩ upperSet, H i x ≠ 0) ∧
      ∀ i j, ∀ x ∈ U i ∩ U j ∩ upperSet, G i j x = H i x / H j x := by
  have hGs : IsSmoothCocycle U G :=
    ⟨hU, fun i j ↦ ((hG i j).contDiffOn ((hU i).inter (hU j))).restrict_scalars ℝ, hG0, hGm⟩
  obtain ⟨s, hs1, hs2, hs3⟩ := smoothTriv_upperHalfPlane hGs hcov
  have hUo : ∀ i, IsOpen (U i ∩ upperSet) := fun i ↦ (hU i).inter isOpen_upperSet
  -- step 2: the logarithmic `∂̄`-derivatives glue
  let A : ι → ℂ → ℂ := fun i z ↦ TauCeti.conjWirtingerDeriv (s i) z 1 / s i z
  have hAeq : ∀ i j, ∀ z ∈ U i ∩ U j ∩ upperSet, A i z = A j z := by
    intro i j z hz
    have hzo : U i ∩ U j ∩ upperSet ∈ 𝓝 z := (((hU i).inter (hU j)).inter isOpen_upperSet).mem_nhds hz
    have hev : s i =ᶠ[𝓝 z] fun y ↦ G i j y * s j y := by
      filter_upwards [hzo] with y hy
      have := hs3 i j y hy
      rw [this, div_mul_cancel₀ _ (hs2 j y ⟨hy.1.2, hy.2⟩)]
    have hGd : DifferentiableAt ℂ (G i j) z :=
      (hG i j).differentiableAt (((hU i).inter (hU j)).mem_nhds hz.1)
    have hsj : DifferentiableAt ℝ (s j) z :=
      differentiableAt_of_contDiffOn_open (hs1 j) (hUo j) ⟨hz.1.2, hz.2⟩
    have hd : TauCeti.conjWirtingerDeriv (s i) z 1 = G i j z * TauCeti.conjWirtingerDeriv (s j) z 1 := by
      rw [hev.conjWirtingerDeriv_eq, TauCeti.conjWirtingerDeriv_fun_mul (hGd.restrictScalars ℝ) hsj,
        hGd.conjWirtingerDeriv_eq_zero]
      simp
    simp only [A, hd, hs3 i j z hz]
    have h1 := hs2 j z ⟨hz.1.2, hz.2⟩
    have h2 := hG0 i j z hz.1
    have h3 := hs2 i z ⟨hz.1.1, hz.2⟩
    field_simp
  classical
  let α : ℂ → ℂ := fun z ↦ if h : ∃ i, z ∈ U i then A h.choose z else 0
  have hαA : ∀ i, ∀ z ∈ U i ∩ upperSet, α z = A i z := by
    intro i z hz
    have h : ∃ i, z ∈ U i := ⟨i, hz.1⟩
    simp only [α, dif_pos h]
    exact hAeq _ _ z ⟨⟨h.choose_spec, hz.1⟩, hz.2⟩
  have hAs : ∀ i, ContDiffOn ℝ ∞ (A i) (U i ∩ upperSet) := by
    intro i z hz
    refine ContDiffAt.contDiffWithinAt ?_
    have hsz := contDiffAt_of_contDiffOn_open (hs1 i) (hUo i) hz
    exact contDiffAt_div' (hsz.conjWirtingerDeriv_apply (m := ∞) (by simp) 1) hsz (hs2 i z hz)
  have hα : ContDiffOn ℝ ∞ α upperSet := by
    refine contDiffOn_of_locally_contDiffOn fun z hz ↦ ?_
    obtain ⟨i, hi⟩ := hcov z hz
    refine ⟨U i, hU i, hi, ?_⟩
    rw [inter_comm]
    exact (hAs i).congr (hαA i)
  -- step 3
  obtain ⟨v, hv, hvα⟩ := exists_dbar_upperSet hα
  let H : ι → ℂ → ℂ := fun i z ↦ s i z * Complex.exp (-v z)
  refine ⟨H, fun i z hz ↦ ?_, fun i z hz ↦ mul_ne_zero (hs2 i z hz) (Complex.exp_ne_zero _),
    fun i j z hz ↦ ?_⟩
  · have hvz : DifferentiableAt ℝ v z := differentiableAt_of_contDiffOn_open hv isOpen_upperSet hz.2
    have hsz : DifferentiableAt ℝ (s i) z := differentiableAt_of_contDiffOn_open (hs1 i) (hUo i) hz
    let F : ℂ → ℂ := fun t ↦ Complex.exp (-t)
    have hF : ∀ t, DifferentiableAt ℂ F t := fun t ↦ (differentiable_exp.comp differentiable_neg) t
    have hFd : ∀ t, deriv F t = -Complex.exp (-t) := fun t ↦ by
      have := ((hasDerivAt_neg t).cexp)
      simpa [F] using this.deriv
    have hEd : DifferentiableAt ℝ (F ∘ v) z := ((hF (v z)).restrictScalars ℝ).comp z hvz
    have hHd : DifferentiableAt ℝ (H i) z := hsz.mul hEd
    refine ((TauCeti.differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero hHd).2 ?_).differentiableWithinAt
    have hHeq : H i = fun y ↦ s i y * (F ∘ v) y := rfl
    rw [hHeq, TauCeti.conjWirtingerDeriv_fun_mul hsz hEd]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    rw [conjWirtingerDeriv_holomorphic_comp (hF (v z)) hvz, hFd, hvα z hz.2, hαA i z hz]
    simp only [A, Function.comp_apply, F]
    have h0 := hs2 i z hz
    field_simp
    ring
  · simp only [H]
    rw [mul_div_mul_right _ _ (Complex.exp_ne_zero _)]
    exact hs3 i j z hz

open UpperHalfPlane in
/-- **The multiplicative Cousin problem on `ℍ`** (`MultiplicativeCousinStatement`), proved. -/
@[kb "forster1981" "Section 30, Theorem 30.3 (H^1(X, O^*) = 0), for X = the upper half-plane"]
theorem multiplicativeCousinStatement : MultiplicativeCousinStatement where
  out ι U hU hcov g hg hg0 hgm := by
    -- transport to `ℂ`
    let U' : ι → Set ℂ := fun i ↦ (↑) '' U i
    let G : ι → ι → ℂ → ℂ := fun i j z ↦ g i j (ofComplex z)
    have hU' : ∀ i, IsOpen (U' i) := fun i ↦ isOpenEmbedding_coe.isOpenMap _ (hU i)
    have hmem : ∀ i (τ : ℍ), (τ : ℂ) ∈ U' i ↔ τ ∈ U i := fun i τ ↦
      ⟨fun ⟨σ, hσ, he⟩ ↦ by rwa [UpperHalfPlane.ext he] at hσ, fun h ↦ ⟨τ, h, rfl⟩⟩
    have hsub : ∀ i, U' i ⊆ upperSet := fun i ↦ by
      rintro _ ⟨τ, -, rfl⟩; exact τ.im_pos
    have hofc : ∀ z ∈ upperSet, ((ofComplex z : ℍ) : ℂ) = z := fun z hz ↦ by
      rw [ofComplex_apply_of_im_pos hz]
    have hmem' : ∀ i, ∀ z ∈ upperSet, z ∈ U' i ↔ ofComplex z ∈ U i := fun i z hz ↦ by
      rw [← hmem, hofc z hz]
    have hcov' : ∀ z ∈ upperSet, ∃ i, z ∈ U' i := fun z hz ↦ by
      obtain ⟨i, hi⟩ := hcov (ofComplex z)
      exact ⟨i, (hmem' i z hz).2 hi⟩
    have hGd : ∀ i j, DifferentiableOn ℂ (G i j) (U' i ∩ U' j) := by
      intro i j z hz
      have hz' : z ∈ upperSet := hsub i hz.1
      have hτ : ofComplex z ∈ U i ∩ U j := ⟨(hmem' i z hz').1 hz.1, (hmem' j z hz').1 hz.2⟩
      have hmd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (g i j) (ofComplex z) :=
        ((hg i j).contMDiffAt (((hU i).inter (hU j)).mem_nhds hτ)).mdifferentiableAt (by simp)
      rw [UpperHalfPlane.mdifferentiableAt_iff, hofc z hz'] at hmd
      exact hmd.differentiableWithinAt
    have hG0 : ∀ i j, ∀ x ∈ U' i ∩ U' j, G i j x ≠ 0 := fun i j x hx ↦ by
      have hx' := hsub i hx.1
      exact hg0 i j _ ⟨(hmem' i x hx').1 hx.1, (hmem' j x hx').1 hx.2⟩
    have hGm : ∀ i j k, ∀ x ∈ U' i ∩ U' j ∩ U' k, G i k x = G i j x * G j k x := fun i j k x hx ↦ by
      have hx' := hsub i hx.1.1
      exact hgm i j k _ ⟨⟨(hmem' i x hx').1 hx.1.1, (hmem' j x hx').1 hx.1.2⟩, (hmem' k x hx').1 hx.2⟩
    obtain ⟨H, hHd, hH0, hHG⟩ := exists_holomorphic_triv hU' hcov' hGd hG0 hGm
    refine ⟨fun i τ ↦ H i τ, fun i ↦ ?_, fun i τ hτ ↦ hH0 i τ ⟨(hmem i τ).2 hτ, τ.im_pos⟩,
      fun i j τ hτ ↦ ?_⟩
    · rw [TauCeti.contMDiffOn_iff_mdifferentiableOn (by simp) (hU i)]
      intro τ hτ
      refine MDifferentiableAt.mdifferentiableWithinAt ?_
      rw [UpperHalfPlane.mdifferentiableAt_iff]
      have hτ' : (τ : ℂ) ∈ U' i ∩ upperSet := ⟨(hmem i τ).2 hτ, τ.im_pos⟩
      have hd : DifferentiableAt ℂ (H i) τ := (hHd i).differentiableAt (((hU' i).inter isOpen_upperSet).mem_nhds hτ')
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_upperSet.mem_nhds τ.im_pos] with z hz
      simp only [Function.comp_apply, hofc z hz]
    · have := hHG i j τ ⟨⟨(hmem i τ).2 hτ.1, (hmem j τ).2 hτ.2⟩, τ.im_pos⟩
      simpa [G, ofComplex_apply] using this

/-- **Milne, Remark 4.26**, unconditionally: every holomorphic line bundle on `ℍ` has a nowhere-vanishing
holomorphic section. -/
@[kb "milne2017mf" "Section 4, Remark 4.26 (pdf p. 59)"]
theorem lineBundlesOnHTrivial : LineBundlesOnHTrivial :=
  lineBundlesOnHTrivial_of_cousin multiplicativeCousinStatement

end ModularFormsKB.Milne.Wave14
