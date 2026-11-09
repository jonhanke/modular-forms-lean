import ModularFormsKB.Milne.Ch4.Automorphy

/-!
# Milne, Remark 4.26: line bundles on $\mathbb H$, reduced to the multiplicative Cousin problem

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Section 4, Remark 4.26 (pdf p. 59).

The named statement `ModularFormsKB.Milne.LineBundlesOnHTrivial` (every holomorphic line bundle on $\mathbb H$ has a
nowhere-vanishing holomorphic section) is derived here from the vanishing of the first Čech cohomology of the sheaf
$\mathcal O^\times$ of nowhere-vanishing holomorphic functions on $\mathbb H$, for every open cover
(`MultiplicativeCousinStatement`, the multiplicative Cousin problem on $\mathbb H$): `lineBundlesOnHTrivial_of_cousin`.

The cited input is a standard theorem of complex analysis: $H^1(\mathbb H, \mathcal O) = 0$ (Dolbeault–Grothendieck
lemma and the solution of $\bar\partial u = g$ on a planar domain, Hörmander, *An Introduction to Complex Analysis
in Several Variables*, Theorem 1.4.4) and $H^2(\mathbb H, \mathbb Z) = 0$ give $H^1(\mathbb H, \mathcal O^\times) = 0$
through the exponential sequence (Forster, *Lectures on Riemann Surfaces*, §30, Theorem 30.3 for noncompact
Riemann surfaces), and Čech $H^1$ of any open cover injects into sheaf $H^1$. Not available in Mathlib or Tau Ceti:
Tau Ceti has the Cauchy–Pompeiu formula (`TauCeti.Analysis.Complex.Pompeiu`, compactly supported data) but not the
exhaustion argument or the exponential sequence.

## Proof of the reduction
Let $e_x$ be the trivialization at $x$ with base set $U_x$, and $g_{xy}(b) = (e_x \circ e_y^{-1})_b(1)$ the coordinate
change, a holomorphic nowhere-vanishing cocycle. If $g_{xy} = h_x/h_y$, then $s(b) = e_b^{-1}(h_b(b))$ satisfies
$e_x(s(b)) = h_x(b)$ on $U_x$, so $s$ is holomorphic and nowhere zero.
-/

open Bundle Set Topology
open scoped Manifold ContDiff

noncomputable section

namespace ModularFormsKB.Milne

/-- **The multiplicative Cousin problem on $\mathbb H$** (named statement; $\check H^1(\mathbb H, \mathcal
O^\times) = 0$ for every open cover): every holomorphic nowhere-vanishing cocycle $g_{ij}$ on an open cover
$\{U_i\}$ of $\mathbb H$ is a coboundary $g_{ij} = h_i/h_j$ with $h_i$ holomorphic and nowhere zero on $U_i$. -/
@[kb "forster1981" "Section 30, Theorem 30.3 (H^1(X, O^*) = 0 for noncompact simply connected Riemann surfaces)"]
structure MultiplicativeCousinStatement : Prop where
  out : ∀ (ι : Type) (U : ι → Set UpperHalfPlane), (∀ i, IsOpen (U i)) → (∀ x, ∃ i, x ∈ U i) →
    ∀ g : ι → ι → UpperHalfPlane → ℂ,
      (∀ i j, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (g i j) (U i ∩ U j)) →
      (∀ i j, ∀ x ∈ U i ∩ U j, g i j x ≠ 0) →
      (∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k, g i k x = g i j x * g j k x) →
      ∃ h : ι → UpperHalfPlane → ℂ, (∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (h i) (U i)) ∧
        (∀ i, ∀ x ∈ U i, h i x ≠ 0) ∧ ∀ i j, ∀ x ∈ U i ∩ U j, g i j x = h i x / h j x

namespace UncondLineBundle

variable (E : UpperHalfPlane → Type) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace ℂ E)] [FiberBundle ℂ E] [VectorBundle ℂ ℂ E]

/-- The coordinate change $g_{xy}(b) = (e_x \circ e_y^{-1})_b(1)$ between the trivializations at `y` and `x`. -/
def cocycle (x y : UpperHalfPlane) (b : UpperHalfPlane) : ℂ :=
  (trivializationAt ℂ E y).coordChangeL ℂ (trivializationAt ℂ E x) b 1

omit [FiberBundle ℂ E] [VectorBundle ℂ ℂ E] in
/-- A coordinate change of a line bundle is multiplication by its value at `1`. -/
theorem coordChangeL_eq_mul (e e' : Trivialization ℂ (π ℂ E)) [e.IsLinear ℂ] [e'.IsLinear ℂ]
    (b : UpperHalfPlane) (v : ℂ) : e.coordChangeL ℂ e' b v = v * e.coordChangeL ℂ e' b 1 := by
  conv_lhs => rw [← mul_one v, ← smul_eq_mul, map_smul, smul_eq_mul]

theorem cocycle_mul {x y z b : UpperHalfPlane}
    (hb : b ∈ (trivializationAt ℂ E x).baseSet ∩ (trivializationAt ℂ E y).baseSet ∩
      (trivializationAt ℂ E z).baseSet) :
    cocycle E x z b = cocycle E x y b * cocycle E y z b := by
  obtain ⟨⟨hx, hy⟩, hz⟩ := hb
  simp only [cocycle]
  have h : (trivializationAt ℂ E z).coordChangeL ℂ (trivializationAt ℂ E x) b 1 =
      (trivializationAt ℂ E y).coordChangeL ℂ (trivializationAt ℂ E x) b
        ((trivializationAt ℂ E z).coordChangeL ℂ (trivializationAt ℂ E y) b 1) := by
    rw [Trivialization.coordChangeL_apply _ _ ⟨hz, hx⟩, Trivialization.coordChangeL_apply _ _ ⟨hz, hy⟩,
      Trivialization.coordChangeL_apply _ _ ⟨hy, hx⟩, Trivialization.symm_apply_apply_mk _ hy]
  rw [h, coordChangeL_eq_mul E _ _ b, mul_comm]

theorem cocycle_ne_zero {x y b : UpperHalfPlane}
    (_hb : b ∈ (trivializationAt ℂ E x).baseSet ∩ (trivializationAt ℂ E y).baseSet) :
    cocycle E x y b ≠ 0 := by
  intro h0
  have h := congrArg ((trivializationAt ℂ E y).coordChangeL ℂ (trivializationAt ℂ E x) b).symm h0
  simp only [cocycle, ContinuousLinearEquiv.symm_apply_apply, map_zero] at h
  exact one_ne_zero h

variable [ContMDiffVectorBundle ω ℂ E 𝓘(ℂ)]

theorem cocycle_contMDiffOn (x y : UpperHalfPlane) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (cocycle E x y)
      ((trivializationAt ℂ E x).baseSet ∩ (trivializationAt ℂ E y).baseSet) := by
  rw [inter_comm]
  exact (contMDiffOn_coordChangeL (IB := 𝓘(ℂ)) (n := ω) (trivializationAt ℂ E y)
    (trivializationAt ℂ E x)).clm_apply contMDiffOn_const

end UncondLineBundle

open UncondLineBundle in
/-- **Remark 4.26** from the multiplicative Cousin problem on $\mathbb H$: every holomorphic line bundle on
$\mathbb H$ has a nowhere-vanishing holomorphic section. -/
@[kb "milne2017mf" "Section 4, Remark 4.26 (pdf p. 59)"]
theorem lineBundlesOnHTrivial_of_cousin (hC : MultiplicativeCousinStatement) : LineBundlesOnHTrivial where
  trivial E _ _ _ _ _ _ := by
    obtain ⟨h, hsm, hne, hgh⟩ := hC.out UpperHalfPlane (fun x ↦ (trivializationAt ℂ E x).baseSet)
      (fun x ↦ (trivializationAt ℂ E x).open_baseSet) (fun x ↦ ⟨x, mem_baseSet_trivializationAt ℂ E x⟩)
      (cocycle E) (cocycle_contMDiffOn E) (fun x y b hb ↦ cocycle_ne_zero E hb)
      (fun x y z b hb ↦ cocycle_mul E hb)
    let s : (b : UpperHalfPlane) → E b := fun b ↦ (trivializationAt ℂ E b).symm b (h b b)
    have hb : ∀ b, b ∈ (trivializationAt ℂ E b).baseSet := fun b ↦ mem_baseSet_trivializationAt ℂ E b
    -- the section read in the trivialization at `x` is `h x`
    have hread : ∀ x b, b ∈ (trivializationAt ℂ E x).baseSet →
        ((trivializationAt ℂ E x) ⟨b, s b⟩).2 = h x b := by
      intro x b hbx
      have h1 := Trivialization.coordChangeL_apply (R := ℂ) (trivializationAt ℂ E b)
        (trivializationAt ℂ E x) ⟨hb b, hbx⟩ (h b b)
      rw [← h1, coordChangeL_eq_mul E]
      have h2 := hgh x b b ⟨hbx, hb b⟩
      simp only [cocycle] at h2
      rw [h2, mul_div_cancel₀ _ (hne b b (hb b))]
    refine ⟨s, fun x ↦ ?_, fun b hs0 ↦ ?_⟩
    · rw [contMDiffAt_section]
      have hU := (trivializationAt ℂ E x).open_baseSet.mem_nhds (hb x)
      refine ((hsm x).contMDiffAt hU).congr_of_eventuallyEq ?_
      filter_upwards [hU] with b hbx
      exact hread x b hbx
    · have := hread b b (hb b)
      have h0 := congrFun ((trivializationAt ℂ E b).coe_linearMapAt_of_mem (R := ℂ) (hb b)) 0
      rw [map_zero] at h0
      rw [hs0, ← h0] at this
      exact hne b b (hb b) this.symm

end ModularFormsKB.Milne
