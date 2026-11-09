import ModularFormsKB.Milne.Ch4.Dimension

/-!
# Milne, Lemma 4.11, unconditionally

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Section 4, Lemma 4.11 (pdf p. 52).

The named statement `ModularFormsKB.Milne.ModularFormDifferential Γ` is proved here for every subgroup `Γ` of finite
index in $\mathrm{SL}_2(\mathbb Z)$ (`modularFormDifferential`).

## Construction
On a Riemann surface `X`, two meromorphic functions `F` and `J` give the meromorphic $k$-fold differential
$F\,(dJ)^k$, with coefficient $u \mapsto F(z_x^{-1}u)\,\bigl((J\circ z_x^{-1})'(u)\bigr)^k$ in the chart $z_x$ at `x`
(`kDiffOf`). For a meromorphic modular form $f$ of weight $2k$ for $\Gamma$, take $J$ the function on $X(\Gamma)$
induced by $j$, and $F$ the function induced by the modular function $f/(j')^k$, where $j' = dj/dz$ is a meromorphic
(in fact holomorphic) modular form of weight $2$ for $\Gamma(1)$. Pulled back to $\mathbb H$ the differential is
$f/(j')^k\,(j'\,dz)^k = f\,(dz)^k$, which is Milne's $\omega$.

The order formulas: at $z \in \mathbb H$, with $\varphi = z_P \circ p$ the chart expression of the projection, of local
degree $e_z$, $f = (\omega_P\circ\varphi)\,(\varphi')^k$ gives (a). At a cusp, $J$ has a pole of order $h$ (the width)
and $j'$ has $q$-order $-h$ as well, so $\mathrm{ord}(f) = \mathrm{ord}(F) - kh$ and
$\mathrm{ord}_P(\omega) = \mathrm{ord}_P(F) + k(-h - 1)$, which gives (b).
-/

open UpperHalfPlane Complex Filter Topology ModularForm MulAction Function
open scoped MatrixGroups Manifold Real ContDiff

noncomputable section

namespace ModularFormsKB.Milne

namespace UncondDiff

section Generic

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The coefficients of the $k$-fold differential $F\,(dJ)^k$ in the charts of `X`. -/
def kDiffOf (F J : X → ℂ) (k : ℤ) (x : X) (u : ℂ) : ℂ :=
  F ((chartAt ℂ x).symm u) * deriv (J ∘ (chartAt ℂ x).symm) u ^ k

/-- A meromorphic function on `X`, read in the chart at `x`, is meromorphic at every point of the chart target. -/
theorem meromorphicAt_comp_chartAt_symm {G : X → ℂ} (hG : ∀ y, TauCeti.RiemannSurface.MeromorphicAt G y)
    (x : X) {u : ℂ} (hu : u ∈ (chartAt ℂ x).target) :
    MeromorphicAt (G ∘ (chartAt ℂ x).symm) u := by
  have h := (TauCeti.RiemannSurface.meromorphicAt_iff_of_mem_maximalAtlas
    (f := G) (IsManifold.chart_mem_maximalAtlas (n := 1) x) ((chartAt ℂ x).map_target hu)).1
    (hG ((chartAt ℂ x).symm u))
  rwa [(chartAt ℂ x).right_inv hu] at h

/-- The $k$-fold differential $F\,(dJ)^k$ of two meromorphic functions. -/
def kDiff (F J : X → ℂ) (hF : ∀ y, TauCeti.RiemannSurface.MeromorphicAt F y)
    (hJ : ∀ y, TauCeti.RiemannSurface.MeromorphicAt J y) (k : ℤ) : KDifferential X k where
  coeff := kDiffOf F J k
  meromorphic x u hu :=
    (meromorphicAt_comp_chartAt_symm hF x hu).mul ((meromorphicAt_comp_chartAt_symm hJ x hu).deriv.zpow k)
  compat x y u hu huy := by
    have hmx := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) (M := X) x
    have hmy := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) (M := X) y
    set cx := chartAt ℂ x
    set cy := chartAt ℂ y
    -- the open overlap `W` around `u`
    have hW : ∀ᶠ v in 𝓝 u, v ∈ cx.target ∧ cx.symm v ∈ cy.source :=
      (cx.isOpen_inter_preimage_symm cy.open_source).mem_nhds ⟨hu, huy⟩
    have hsrc : ∀ {v}, v ∈ cx.target → cx.symm v ∈ cy.source → cy.symm (transition X x y v) = cx.symm v :=
      fun _ hv' ↦ cy.left_inv hv'
    have han : ∀ {v}, v ∈ cx.target → cx.symm v ∈ cy.source → AnalyticAt ℂ (transition X x y) v := by
      intro v hv hv'
      have := TauCeti.analyticAt_symm_trans hmx hmy (cx.map_target hv) hv'
      rwa [cx.right_inv hv] at this
    have hd : deriv (transition X x y) u ≠ 0 := by
      have := TauCeti.deriv_symm_trans_ne_zero hmx hmy (cx.map_target hu) huy
      rwa [cx.right_inv hu] at this
    have hnc : ¬ EventuallyConst (transition X x y) (𝓝 u) := by
      intro hc
      obtain ⟨c, hc⟩ := eventuallyConst_iff_exists_eventuallyEq.1 hc
      exact hd (by rw [hc.deriv_eq]; simp)
    have hτ : Tendsto (transition X x y) (𝓝[≠] u) (𝓝[≠] (transition X x y u)) :=
      (han hu huy).map_nhdsNE hnc
    have hJy : MeromorphicAt (J ∘ cy.symm) (transition X x y u) :=
      meromorphicAt_comp_chartAt_symm hJ y (cy.map_source huy)
    have hdiff : ∀ᶠ v in 𝓝[≠] u, AnalyticAt ℂ (J ∘ cy.symm) (transition X x y v) :=
      hτ.eventually hJy.eventually_analyticAt
    filter_upwards [hdiff, nhdsWithin_le_nhds hW, nhdsWithin_le_nhds hW.eventually_nhds] with v hv hvW hvW'
    obtain ⟨hv1, hv2⟩ := hvW
    have heq : J ∘ cx.symm =ᶠ[𝓝 v] (J ∘ cy.symm) ∘ transition X x y := by
      filter_upwards [hvW'] with w hw
      simp only [Function.comp_apply, hsrc hw.1 hw.2]
    simp only [kDiffOf]
    rw [hsrc hv1 hv2, heq.deriv_eq, deriv_comp _ hv.differentiableAt (han hv1 hv2).differentiableAt, mul_zpow,
      mul_assoc]

end Generic


section Cusp

open Function

/-- At a width `n ∈ ℕ`, the cusp function of a `1`-periodic function is that of width `1` composed with `q ↦ q^n`. -/
theorem cuspFunction_nat_eventuallyEq {φ : ℂ → ℂ} (hφ : Periodic φ 1) {n : ℕ} (hn : 0 < n) :
    Periodic.cuspFunction n φ =ᶠ[𝓝[≠] 0] fun q ↦ Periodic.cuspFunction 1 φ (q ^ n) := by
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq0 : q ≠ 0 := hq
  rw [Periodic.cuspFunction_eq_of_nonzero _ _ hq0]
  set z := Periodic.invQParam (n : ℝ) q with hz
  have h1 : Periodic.qParam (n : ℝ) z = q := Periodic.qParam_right_inv (by positivity) hq0
  have h2 : Periodic.qParam 1 z = q ^ n := by
    rw [← h1, Periodic.qParam, Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp
  rw [← h2, Periodic.eq_cuspFunction one_ne_zero hφ z]

/-- The cusp function of the normalized derivative: if `g ∘ ofComplex` is `h`-periodic with cusp function `G`
meromorphic at `0`, then near `q = 0` the cusp function of `D g = (2πi)⁻¹ g'` is `q ↦ h⁻¹ q G'(q)`. -/
theorem cuspFunction_normalizedDeriv_eventuallyEq {g : ℍ → ℂ} {h : ℝ} (hh : 0 < h)
    (hper : Periodic (g ∘ ofComplex) h) (hmero : MeromorphicAt (Periodic.cuspFunction h (g ∘ ofComplex)) 0) :
    Periodic.cuspFunction h (Derivative.normalizedDerivOfComplex g ∘ ofComplex) =ᶠ[𝓝[≠] 0]
      fun q ↦ (h : ℂ)⁻¹ * q * deriv (Periodic.cuspFunction h (g ∘ ofComplex)) q := by
  have hA := hmero.eventually_analyticAt
  have hB : ∀ᶠ q : ℂ in 𝓝[≠] 0, ‖q‖ < 1 :=
    eventually_nhdsWithin_of_eventually_nhds
      (by
        have := Metric.ball_mem_nhds (0:ℂ) one_pos
        filter_upwards [this] with x hx using by simpa using hx)
  filter_upwards [hA, hB, self_mem_nhdsWithin] with q hqA hq1 hq
  have hq0 : q ≠ 0 := hq
  set G := Periodic.cuspFunction h (g ∘ ofComplex) with hG
  set z := Periodic.invQParam h q with hz
  have hzpos : 0 < z.im := Periodic.im_invQParam_pos_of_norm_lt_one hh hq1 hq0
  have h1 : Periodic.qParam h z = q := Periodic.qParam_right_inv hh.ne' hq0
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [Periodic.cuspFunction_eq_of_nonzero _ _ hq0]
  have hfun : (g ∘ ofComplex) = G ∘ Periodic.qParam h := by
    funext w
    simp [hG, Periodic.eq_cuspFunction hh.ne' hper w]
  have hq' : HasDerivAt (Periodic.qParam h) (Periodic.qParam h z * (2 * π * Complex.I / h)) z := by
    unfold Periodic.qParam
    have : HasDerivAt (fun w : ℂ => 2 * π * Complex.I * w / h) (2 * π * Complex.I / h) z := by
      simpa using ((hasDerivAt_id z).const_mul (2 * π * Complex.I)).div_const (h : ℂ)
    exact this.cexp
  have hGd : HasDerivAt G (deriv G q) (Periodic.qParam h z) := by
    rw [h1]; exact hqA.differentiableAt.hasDerivAt
  have hcomp := hGd.comp z hq'
  have hd : deriv (g ∘ ofComplex) z = deriv G q * (q * (2 * π * Complex.I / h)) := by
    rw [hfun, hcomp.deriv, h1]
  simp only [Derivative.normalizedDerivOfComplex, Function.comp_apply]
  rw [ofComplex_apply_of_im_pos hzpos]
  have : ((⟨z, hzpos⟩ : ℍ) : ℂ) = z := rfl
  rw [this, hd]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- The width of a cusp of a finite-index subgroup of `SL(2, ℤ)` is a positive integer. -/
theorem exists_nat_cuspWidth (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (γ : SL(2, ℤ)) :
    ∃ n : ℕ, 0 < n ∧ cuspWidth Γ γ = n := by
  obtain ⟨D, -, -, hD⟩ := exists_cuspDatum_of_sl2z Γ γ
  have hpos : 0 < cuspWidth Γ γ := hD ▸ D.width_pos
  have hmem : cuspWidth Γ γ ∈ ((conjSubgroup Γ γ : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).periods := Subgroup.widthInfty_mem_periods _
  unfold Subgroup.periods at hmem
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_adjoinNegOne_iff, mem_coe_GL_iff,
    mem_coe_GL_iff] at hmem
  have fin : ∀ z : ℤ, ((z : ℝ) = cuspWidth Γ γ ∨ (z : ℝ) = -cuspWidth Γ γ) →
      ∃ n : ℕ, 0 < n ∧ cuspWidth Γ γ = n := by
    intro z hz
    refine ⟨z.natAbs, ?_, ?_⟩
    · rcases hz with hz | hz
      · have : (0 : ℝ) < z := hz ▸ hpos
        have : 0 < z := by exact_mod_cast this
        omega
      · have : (z : ℝ) < 0 := by rw [hz]; linarith
        have : z < 0 := by exact_mod_cast this
        omega
    · rcases hz with hz | hz
      · have : (0 : ℝ) < z := hz ▸ hpos
        have : 0 < z := by exact_mod_cast this
        rw [← hz, Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast this)]
      · have : (z : ℝ) < 0 := by rw [hz]; linarith
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg this, hz]; ring
  rcases hmem with ⟨h, -, he⟩ | ⟨h, -, he⟩
  · apply fin (h 0 1)
    left
    have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1) he
    simpa [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.GeneralLinearGroup.upperRightHom] using this
  · apply fin (h 0 1)
    right
    have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1) he
    simpa [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.GeneralLinearGroup.upperRightHom] using this

end Cusp

section JFunction

/-- $j' = dj/dz$, as $2\pi i$ times Mathlib's normalized derivative $\frac{1}{2\pi i}\frac{d}{dz}$. -/
def jD : ℍ → ℂ := (2 * π * Complex.I : ℂ) • Derivative.normalizedDerivOfComplex jFun

theorem jFun_mdifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jFun := by
  rw [jFun_eq]; exact TauCeti.ModularForm.j_mdifferentiable

theorem jD_apply (z : ℍ) : jD z = deriv (jFun ∘ ofComplex) z := by
  have h : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  simp only [jD, Pi.smul_apply, smul_eq_mul, Derivative.normalizedDerivOfComplex]
  rw [← mul_assoc, mul_inv_cancel₀ h, one_mul]

theorem jD_mdifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jD :=
  (Derivative.normalizedDerivOfComplex_mdifferentiable jFun_mdifferentiable).const_smul _

theorem jD_analyticAt (z : ℍ) : AnalyticAt ℂ (jD ∘ ofComplex) (z : ℂ) :=
  TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex jD_mdifferentiable z.im_pos

/-- $j'$ is a modular form of weight $2$ for $\Gamma(1)$: $j'|_2\gamma = j'$. -/
theorem jD_slash (γ : SL(2, ℤ)) : jD ∣[(2 : ℤ)] γ = jD := by
  have h := Derivative.normalizedDerivOfComplex_SL_slash (k := 0) jFun_mdifferentiable (γ := γ)
  have hj : jFun ∣[(0 : ℤ)] γ = jFun := by simpa using jFun_slash γ
  rw [hj] at h
  simp only [Int.cast_zero, zero_mul, zero_add] at h
  have h' : Derivative.normalizedDerivOfComplex jFun ∣[(2 : ℤ)] γ = Derivative.normalizedDerivOfComplex jFun := by
    conv_rhs => rw [h]
    funext z; simp
  rw [jD, SL_smul_slash, h']

theorem jD_smul (γ : SL(2, ℤ)) (z : ℍ) : jD (γ • z) = denom γ z ^ 2 * jD z := by
  have h := congrFun (jD_slash γ) z
  rw [SL_slash_apply] at h
  have hd : denom γ z ≠ 0 := denom_ne_zero _ _
  rw [← h, zpow_neg, ← mul_assoc, mul_comm (denom γ z ^ 2), mul_assoc, zpow_two, ← sq,
    mul_inv_cancel₀ (pow_ne_zero 2 hd), mul_one]

/-- $j'$ does not vanish identically near any point of $\mathbb H$. -/
theorem jD_eventually_ne_zero (z : ℍ) : ∀ᶠ w in 𝓝[≠] (z : ℂ), jD (ofComplex w) ≠ 0 := by
  rcases (jD_analyticAt z).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hU : IsOpen {w : ℂ | 0 < w.im} := isOpen_upperHalfPlaneSet
    have hzU : (z : ℂ) ∈ {w : ℂ | 0 < w.im} := z.im_pos
    have h2 : ∀ᶠ w in 𝓝 (z : ℂ), w ∈ {w : ℂ | 0 < w.im} ∧ (jD ∘ ofComplex) w = 0 :=
      Filter.Eventually.and (hU.mem_nhds hzU) h
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 h2
    set B := Metric.ball (z : ℂ) ε with hB
    have hder : ∀ w ∈ B, deriv (jFun ∘ ofComplex) w = 0 := by
      intro w hw
      obtain ⟨hw1, hw2⟩ := hball (Metric.mem_ball.1 hw)
      have hw1' : 0 < w.im := hw1
      have := jD_apply ⟨w, hw1'⟩
      simp only [Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hw1'] at hw2 this
      rw [← this]; exact hw2
    have hdiff : DifferentiableOn ℂ (jFun ∘ ofComplex) B := fun w hw => by
      obtain ⟨hw1, -⟩ := hball (Metric.mem_ball.1 hw)
      exact (jFun_analyticAt ⟨w, hw1⟩).differentiableAt.differentiableWithinAt
    have hconst : ∀ x ∈ B, (jFun ∘ ofComplex) x = (jFun ∘ ofComplex) (z : ℂ) := fun x hx =>
      Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected hdiff
        (fun w hw => hder w hw) hx (Metric.mem_ball_self hε)
    have hev : (jFun ∘ ofComplex) =ᶠ[𝓝 (z : ℂ)] fun _ => (jFun ∘ ofComplex) (z : ℂ) :=
      Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds _ hε) hconst
    have hconn : IsPreconnected {w : ℂ | 0 < w.im} :=
      (convex_halfSpace_im_gt 0).isPreconnected
    have han : AnalyticOnNhd ℂ (jFun ∘ ofComplex) {w : ℂ | 0 < w.im} := fun w hw =>
      jFun_analyticAt ⟨w, hw⟩
    have heq := han.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hconn hzU hev
    obtain ⟨y, hy⟩ := jFun_bijective.1 (jFun z + 1)
    have := heq (show (y : ℂ) ∈ {w : ℂ | 0 < w.im} from y.im_pos)
    simp only [Function.comp, UpperHalfPlane.ofComplex_apply] at this
    rw [hy] at this
    simp at this
  · filter_upwards [h] with w hw using hw

/-- At width `n`, the cusp function of $j$ has a pole of order `n`. -/
theorem order_cuspFunction_jFun {n : ℕ} (hn : 0 < n) :
    meromorphicOrderAt (Periodic.cuspFunction (n : ℝ) (jFun ∘ ofComplex)) 0 = ((-(n : ℤ) : ℤ) : WithTop ℤ) := by
  have hper : Periodic (jFun ∘ ofComplex) 1 := IsModularFunction.periodic_top jFun_isModularFunction
  have h1 : meromorphicOrderAt (Periodic.cuspFunction 1 (jFun ∘ ofComplex)) 0 = ((-1 : ℤ) : WithTop ℤ) := by
    have := cuspOrder_jFun
    unfold cuspOrder at this
    rw [jFun_slash, cuspWidth_top] at this
    exact_mod_cast this
  have hm : MeromorphicAt (Periodic.cuspFunction 1 (jFun ∘ ofComplex)) 0 :=
    meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [h1]; decide)
  rw [meromorphicOrderAt_congr (cuspFunction_nat_eventuallyEq hper hn),
    meromorphicOrderAt_comp_pow hm hn (-1) h1]
  congr 1
  ring

/-- At width `n`, the cusp function of $j'$ also has a pole of order `n`. -/
theorem order_cuspFunction_jD {n : ℕ} (hn : 0 < n) :
    meromorphicOrderAt (Periodic.cuspFunction (n : ℝ) (jD ∘ ofComplex)) 0 = ((-(n : ℤ) : ℤ) : WithTop ℤ) := by
  have hper1 : Periodic (jFun ∘ ofComplex) 1 := IsModularFunction.periodic_top jFun_isModularFunction
  have hper : Periodic (jFun ∘ ofComplex) (n : ℝ) := by simpa using hper1.nat_mul n
  set G := Periodic.cuspFunction (n : ℝ) (jFun ∘ ofComplex)
  have hG : meromorphicOrderAt G 0 = ((-(n : ℤ) : ℤ) : WithTop ℤ) := order_cuspFunction_jFun hn
  have hm : MeromorphicAt G 0 := meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [hG]; simp; omega)
  have hD := cuspFunction_normalizedDeriv_eventuallyEq (by exact_mod_cast hn : (0 : ℝ) < n) hper hm
  have hE : Periodic.cuspFunction (n : ℝ) (jD ∘ ofComplex) =ᶠ[𝓝[≠] 0]
      (fun _ ↦ (2 * π * Complex.I) * ((n : ℝ) : ℂ)⁻¹) * ((fun q ↦ q) * deriv G) := by
    filter_upwards [hD, self_mem_nhdsWithin] with q hq hq0
    rw [Periodic.cuspFunction_eq_of_nonzero _ _ hq0]
    rw [Periodic.cuspFunction_eq_of_nonzero _ _ hq0] at hq
    simp only [jD, Function.comp_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply] at hq ⊢
    rw [hq]
    ring
  have hd := meromorphicOrderAt_deriv_eq_sub_one (n := -(n : ℤ)) (by simp; omega) hG
  have hc : (2 * π * Complex.I) * ((n : ℝ) : ℂ)⁻¹ ≠ 0 := by
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
  rw [meromorphicOrderAt_congr hE, meromorphicOrderAt_mul (by fun_prop) (by fun_prop),
    meromorphicOrderAt_mul (by fun_prop) hm.deriv, hd, meromorphicOrderAt_const, ite_eq_right_iff.2 (fun h ↦ absurd h hc)]
  have hid : meromorphicOrderAt (fun q : ℂ ↦ q) 0 = 1 := meromorphicOrderAt_id
  rw [hid]
  norm_cast
  ring_nf

/-- $j$ is a modular function for every subgroup of finite index. -/
theorem jFun_isModularFunction' (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : IsModularFunction Γ jFun := by
  refine ⟨fun γ _ ↦ jFun_slash γ, fun z ↦ (jFun_analyticAt z).meromorphicAt, fun γ ↦ ?_⟩
  obtain ⟨n, hn, hw⟩ := exists_nat_cuspWidth Γ γ
  rw [jFun_slash, hw]
  exact meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [order_cuspFunction_jFun hn]; simp; omega)

end JFunction

section Quotient

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {f : ℍ → ℂ}

/-- The modular function $f/(j')^k$ attached to a meromorphic modular form $f$ of weight $2k$. -/
def quotJ (f : ℍ → ℂ) (k : ℤ) : ℍ → ℂ := fun z ↦ f z / jD z ^ k

theorem meromorphicAt_cuspFunction_jD {n : ℕ} (hn : 0 < n) :
    MeromorphicAt (Periodic.cuspFunction (n : ℝ) (jD ∘ ofComplex)) 0 :=
  meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [order_cuspFunction_jD hn]; simp; omega)

theorem quotJ_slash_apply (γ : SL(2, ℤ)) (z : ℍ) :
    (quotJ f k ∣[(2 * 0 : ℤ)] γ) z = (f ∣[2 * k] γ) z / jD z ^ k := by
  rw [SL_slash_apply, SL_slash_apply, quotJ, jD_smul]
  have h : (denom γ z ^ 2) ^ k = denom γ z ^ (2 * k) := by
    rw [zpow_mul]; norm_cast
  rw [mul_zpow, h]
  simp only [mul_zero, zpow_zero, zpow_neg]
  ring

theorem quotJ_isModularFunction (hf : IsMeromorphicModularForm Γ k f) : IsModularFunction Γ (quotJ f k) := by
  refine ⟨fun γ hγ ↦ ?_, fun z ↦ ?_, fun γ ↦ ?_⟩
  · funext z
    rw [quotJ_slash_apply, hf.slash γ hγ]
    rfl
  · exact (hf.meromorphic z).div ((jD_analyticAt z).meromorphicAt.zpow k)
  · obtain ⟨n, hn, hw⟩ := exists_nat_cuspWidth Γ γ
    have hc := hf.meromorphic_cusp γ
    rw [hw] at hc ⊢
    have hE : Periodic.cuspFunction (n : ℝ) ((quotJ f k ∣[(2 * 0 : ℤ)] γ) ∘ ofComplex) =ᶠ[𝓝[≠] 0]
        Periodic.cuspFunction (n : ℝ) ((f ∣[2 * k] γ) ∘ ofComplex) /
          Periodic.cuspFunction (n : ℝ) (jD ∘ ofComplex) ^ k := by
      filter_upwards [self_mem_nhdsWithin] with q hq
      simp only [Periodic.cuspFunction_eq_of_nonzero _ _ hq, Pi.div_apply, Pi.pow_apply, comp_apply,
        quotJ_slash_apply]
    exact (hc.div ((meromorphicAt_cuspFunction_jD hn).zpow k)).congr hE.symm

/-- $\mathrm{ord}(f) = \mathrm{ord}(f/(j')^k) + k\,\mathrm{ord}(j') = \mathrm{ord}(f/(j')^k) - kh$ at a cusp of
width $h$. -/
theorem cuspOrder_eq_quotJ (hf : IsMeromorphicModularForm Γ k f) (γ : SL(2, ℤ)) {n : ℕ} (hn : 0 < n)
    (hw : cuspWidth Γ γ = n) :
    cuspOrder Γ k f γ = cuspOrder Γ 0 (quotJ f k) γ + ((k * -(n : ℤ) : ℤ) : WithTop ℤ) := by
  have hq := (quotJ_isModularFunction hf).meromorphic_cusp γ
  unfold cuspOrder
  rw [hw] at hq ⊢
  have hjD := meromorphicAt_cuspFunction_jD hn
  have hne := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hjD).1
    (by rw [order_cuspFunction_jD hn]; simp)
  have hE : Periodic.cuspFunction (n : ℝ) ((f ∣[2 * k] γ) ∘ ofComplex) =ᶠ[𝓝[≠] 0]
      Periodic.cuspFunction (n : ℝ) ((quotJ f k ∣[(2 * 0 : ℤ)] γ) ∘ ofComplex) *
        Periodic.cuspFunction (n : ℝ) (jD ∘ ofComplex) ^ k := by
    filter_upwards [self_mem_nhdsWithin, hne] with q hq hq'
    simp only [Pi.mul_apply, Pi.pow_apply]
    simp only [Periodic.cuspFunction_eq_of_nonzero _ _ hq, comp_apply] at hq' ⊢
    rw [quotJ_slash_apply, div_mul_cancel₀ _ (zpow_ne_zero _ hq')]
  rw [meromorphicOrderAt_congr hE, meromorphicOrderAt_mul hq (hjD.zpow k), meromorphicOrderAt_zpow hjD,
    order_cuspFunction_jD hn]
  norm_cast

/-- Descent of a modular function to $X(\Gamma)$ (from `isModularFunction_iff_compactifiedQuotient`). -/
theorem exists_descent {g : ℍ → ℂ} (hg : IsModularFunction Γ g) :
    ∃ G : modularCurve Γ → ℂ, (∀ x, TauCeti.RiemannSurface.MeromorphicAt G x) ∧
      ∀ z, g z = G (modularCurve.proj Γ z) :=
  ((isModularFunction_iff_compactifiedQuotient Γ g).1 hg).2.2

/-- The order of a descended modular function at the cusp $\gamma(i\infty)$ is its order there. -/
theorem order_descent_cusp {g : ℍ → ℂ} {G : modularCurve Γ → ℂ} (hG : ∀ z, g z = G (modularCurve.proj Γ z))
    (γ : SL(2, ℤ)) :
    TauCeti.RiemannSurface.meromorphicOrderAt G (Subgroup.CompactifiedQuotient.ofCusp (Γ.cuspOrbitOfSL2Z γ)) =
      cuspOrder Γ 0 g γ := by
  obtain ⟨D, hD, hs, hw⟩ := exists_cuspDatum_of_sl2z Γ γ
  rw [← hD, Subgroup.CompactifiedQuotient.meromorphicOrderAt_ofCusp D (f := g) (fun z ↦ (hG z).symm),
    cuspExtension_eq Γ γ D hs hw]
  rfl

end Quotient

section Interior

variable {Γ : Subgroup SL(2, ℤ)}

theorem mdifferentiable_proj : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (modularCurve.proj Γ) :=
  Subgroup.CompactifiedQuotient.mdifferentiable_ofQuotient.comp
    (Subgroup.mdifferentiable_quotientMk (Γ.map sl2zToPSL2R))

theorem continuousAt_proj_ofComplex (z : ℍ) : ContinuousAt (modularCurve.proj Γ ∘ ofComplex) (z : ℂ) := by
  have h1 : ContinuousAt ofComplex (z : ℂ) := (mdifferentiableAt_ofComplex z.im_pos).continuousAt
  have h2 : ContinuousAt (modularCurve.proj Γ) (ofComplex (z : ℂ)) := (mdifferentiable_proj _).continuousAt
  exact h2.comp h1

/-- The chart expression $\varphi = z_x \circ p$ of the projection is differentiable wherever $p(w)$ lies in the
chart domain. -/
theorem differentiableAt_chart_proj (x : modularCurve Γ) {w : ℂ} (hw : 0 < w.im)
    (hx : modularCurve.proj Γ (ofComplex w) ∈ (chartAt ℂ x).source) :
    DifferentiableAt ℂ (chartAt ℂ x ∘ modularCurve.proj Γ ∘ ofComplex) w := by
  have h : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x ∘ modularCurve.proj Γ) (ofComplex w) :=
    (mdifferentiableAt_atlas (chart_mem_atlas ℂ x) hx).comp _ (mdifferentiable_proj _)
  have := UpperHalfPlane.mdifferentiableAt_iff.1 h
  rwa [ofComplex_apply_of_im_pos hw] at this

/-- A function on $X(\Gamma)$ whose pullback to $\mathbb H$ is holomorphic is holomorphic at the points of
$\Gamma\backslash\mathbb H$. -/
theorem mdifferentiableAt_of_pullback {G : modularCurve Γ → ℂ} {g : ℍ → ℂ}
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hG : ∀ z, g z = G (modularCurve.proj Γ z)) (z : ℍ) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) G (modularCurve.proj Γ z) := by
  have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (G ∘ Subgroup.CompactifiedQuotient.ofQuotient) := by
    rw [Subgroup.mdifferentiable_iff_comp_quotientMk]
    have : (G ∘ Subgroup.CompactifiedQuotient.ofQuotient) ∘ Quotient.mk _ = g := funext fun z ↦ (hG z).symm
    rw [this]; exact hg
  exact Subgroup.CompactifiedQuotient.mdifferentiableAt_comp_ofQuotient_iff.1 (h1 _)

variable {k : ℤ} {f : ℍ → ℂ}

/-- **Lemma 4.11, pullback**: near $z \in \mathbb H$, $f = (\omega_P \circ \varphi)\,(\varphi')^k$ in the chart at
$P = p(z)$, with $\varphi = z_P \circ p$. -/
theorem interior_eq {Fc Jc : modularCurve Γ → ℂ} (hF : ∀ z, quotJ f k z = Fc (modularCurve.proj Γ z))
    (hJ : ∀ z, jFun z = Jc (modularCurve.proj Γ z)) (z : ℍ) :
    (f ∘ ofComplex) =ᶠ[𝓝[≠] (z : ℂ)] fun w ↦
      kDiffOf Fc Jc k (modularCurve.proj Γ z)
          (chartAt ℂ (modularCurve.proj Γ z) (modularCurve.proj Γ (ofComplex w))) *
        deriv (chartAt ℂ (modularCurve.proj Γ z) ∘ modularCurve.proj Γ ∘ ofComplex) w ^ k := by
  set x := modularCurve.proj Γ z
  set φ := chartAt ℂ x ∘ modularCurve.proj Γ ∘ ofComplex
  have hS : ∀ᶠ w in 𝓝 (z : ℂ), 0 < w.im ∧ modularCurve.proj Γ (ofComplex w) ∈ (chartAt ℂ x).source :=
    (show ∀ᶠ w in 𝓝 (z : ℂ), 0 < w.im from isOpen_upperHalfPlaneSet.mem_nhds z.im_pos).and
      ((continuousAt_proj_ofComplex z).preimage_mem_nhds
        ((chartAt ℂ x).open_source.mem_nhds (by
          simp [x, ofComplex_apply])))
  have hJd := mdifferentiableAt_of_pullback jFun_mdifferentiable hJ
  filter_upwards [nhdsWithin_le_nhds hS, nhdsWithin_le_nhds hS.eventually_nhds, jD_eventually_ne_zero z]
    with w hw hw' hjD
  obtain ⟨hw1, hw2⟩ := hw
  have hcs : (chartAt ℂ x).symm (φ w) = modularCurve.proj Γ (ofComplex w) := (chartAt ℂ x).left_inv hw2
  -- the chain rule for $j = (J \circ z_x^{-1}) \circ \varphi$
  have heq : jFun ∘ ofComplex =ᶠ[𝓝 w] (Jc ∘ (chartAt ℂ x).symm) ∘ φ := by
    filter_upwards [hw'] with w' hw''
    simp only [Function.comp_apply, φ, (chartAt ℂ x).left_inv hw''.2, hJ]
  have hJdiff : DifferentiableAt ℂ (Jc ∘ (chartAt ℂ x).symm) (φ w) := by
    have hm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Jc ∘ (chartAt ℂ x).symm) (φ w) := by
      refine MDifferentiableAt.comp _ ?_ (mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ x)
        ((chartAt ℂ x).map_source hw2))
      rw [hcs, ofComplex_apply_of_im_pos hw1]
      exact hJd _
    exact mdifferentiableAt_iff_differentiableAt.1 hm
  have hchain : deriv (jFun ∘ ofComplex) w = deriv (Jc ∘ (chartAt ℂ x).symm) (φ w) * deriv φ w := by
    rw [heq.deriv_eq, deriv_comp _ hJdiff (differentiableAt_chart_proj x hw1 hw2)]
  have hjw : jD (ofComplex w) = deriv (jFun ∘ ofComplex) w := by
    rw [jD_apply, ofComplex_apply_of_im_pos hw1]
  simp only [kDiffOf, Function.comp_apply]
  rw [show (chartAt ℂ x) (modularCurve.proj Γ (ofComplex w)) = φ w from rfl, hcs, ← hF,
    mul_assoc, ← mul_zpow, ← hchain, ← hjw, quotJ, div_mul_cancel₀ _ (zpow_ne_zero _ hjD)]

end Interior

section Orders

variable {Γ : Subgroup SL(2, ℤ)}

theorem eventually_chart_source (z : ℍ) :
    ∀ᶠ w in 𝓝 (z : ℂ), 0 < w.im ∧
      modularCurve.proj Γ (ofComplex w) ∈ (chartAt ℂ (modularCurve.proj Γ z)).source :=
  (show ∀ᶠ w in 𝓝 (z : ℂ), 0 < w.im from isOpen_upperHalfPlaneSet.mem_nhds z.im_pos).and
    ((continuousAt_proj_ofComplex z).preimage_mem_nhds
      ((chartAt ℂ _).open_source.mem_nhds (by simp [ofComplex_apply])))

/-- The local degree of $\varphi = z_P \circ p$ at $z$ is $e_z$ (Tau Ceti's elliptic order formula). -/
theorem order_phi (z : ℍ) :
    meromorphicOrderAt (fun w ↦ chartAt ℂ (modularCurve.proj Γ z) (modularCurve.proj Γ (ofComplex w)) -
      chartAt ℂ (modularCurve.proj Γ z) (modularCurve.proj Γ z)) (z : ℂ) = (stabOrder Γ z : WithTop ℤ) := by
  set x := modularCurve.proj Γ z
  set G : modularCurve Γ → ℂ := fun y ↦ chartAt ℂ x y - chartAt ℂ x x
  have h := Subgroup.CompactifiedQuotient.meromorphicOrderAt_comp_ofQuotient_mk G z
  rw [TauCeti.UpperHalfPlane.meromorphicOrderAt_eq_meromorphicOrderAt_comp_ofComplex] at h
  have h1 : TauCeti.RiemannSurface.meromorphicOrderAt G x = 1 := by
    rw [TauCeti.RiemannSurface.meromorphicOrderAt_def]
    have : G ∘ (chartAt ℂ x).symm =ᶠ[𝓝 (chartAt ℂ x x)] (· - chartAt ℂ x x) := by
      filter_upwards [(chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source (mem_chart_source ℂ x))]
        with u hu
      simp [G, (chartAt ℂ x).right_inv hu]
    rw [meromorphicOrderAt_congr (this.filter_mono nhdsWithin_le_nhds)]
    exact meromorphicOrderAt_id_sub_const
  have h1' : TauCeti.RiemannSurface.meromorphicOrderAt G
      (Subgroup.CompactifiedQuotient.ofQuotient (Quotient.mk _ z)) = 1 := h1
  rw [h1', mul_one] at h
  exact h

variable {k : ℤ} {f : ℍ → ℂ}

/-- $e_z \ne 0$. -/
theorem stabOrder_ne_zero (z : ℍ) : stabOrder Γ z ≠ 0 := by
  set x := modularCurve.proj Γ z
  set φ := chartAt ℂ x ∘ modularCurve.proj Γ ∘ ofComplex
  have hφ : AnalyticAt ℂ φ z := Complex.analyticAt_iff_eventually_differentiableAt.2
    ((eventually_chart_source z).mono fun w hw ↦ differentiableAt_chart_proj x hw.1 hw.2)
  have hφz : φ z = chartAt ℂ x x := by simp [φ, x, ofComplex_apply]
  have hord : meromorphicOrderAt (fun w ↦ φ w - φ z) z = (stabOrder Γ z : WithTop ℤ) := by
    rw [hφz]; exact order_phi z
  have hφa : AnalyticAt ℂ (fun w ↦ φ w - φ z) z := hφ.sub analyticAt_const
  intro he0
  have hcont : Tendsto (fun w ↦ φ w - φ z) (𝓝[≠] (z : ℂ)) (𝓝 0) := by
    have := hφa.continuousAt.tendsto
    simp only [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have := (tendsto_zero_iff_meromorphicOrderAt_pos hφa.meromorphicAt).1 hcont
  rw [hord, he0] at this
  simp at this

/-- **Lemma 4.11 (a)**, in `WithTop ℤ`: $\mathrm{ord}_z(f) = e\,\mathrm{ord}_P(\omega) + k(e - 1)$. -/
theorem order_interior_gen {Fc Jc : modularCurve Γ → ℂ} (hFm : ∀ y, TauCeti.RiemannSurface.MeromorphicAt Fc y)
    (hJm : ∀ y, TauCeti.RiemannSurface.MeromorphicAt Jc y)
    (hF : ∀ z, quotJ f k z = Fc (modularCurve.proj Γ z)) (hJ : ∀ z, jFun z = Jc (modularCurve.proj Γ z))
    (z : ℍ) :
    meromorphicOrderAt (f ∘ ofComplex) (z : ℂ) =
      (kDiff Fc Jc hFm hJm k).order (modularCurve.proj Γ z) * (stabOrder Γ z : WithTop ℤ) +
        ((k * ((stabOrder Γ z : ℤ) - 1) : ℤ) : WithTop ℤ) := by
  set x := modularCurve.proj Γ z
  set φ := chartAt ℂ x ∘ modularCurve.proj Γ ∘ ofComplex
  set e := stabOrder Γ z
  set c := kDiffOf Fc Jc k x
  have hφ : AnalyticAt ℂ φ z := Complex.analyticAt_iff_eventually_differentiableAt.2
    ((eventually_chart_source z).mono fun w hw ↦ differentiableAt_chart_proj x hw.1 hw.2)
  have hφz : φ z = chartAt ℂ x x := by simp [φ, x, ofComplex_apply]
  have hord : meromorphicOrderAt (fun w ↦ φ w - φ z) z = (e : WithTop ℤ) := by
    rw [hφz]; exact order_phi z
  have hφa : AnalyticAt ℂ (fun w ↦ φ w - φ z) z := hφ.sub analyticAt_const
  have he : e ≠ 0 := stabOrder_ne_zero z
  have hana : analyticOrderAt (fun w ↦ φ w - φ z) z = e := by
    have := hφa.meromorphicOrderAt_eq
    rw [hord] at this
    cases h : analyticOrderAt (fun w ↦ φ w - φ z) (z : ℂ) with
    | top => rw [h] at this; simp at this
    | coe a =>
      rw [h] at this
      simp only [ENat.map_natCast] at this
      exact_mod_cast this.symm
  have hnc : ¬ EventuallyConst φ (𝓝 (z : ℂ)) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hana]; simp
  have hcm : MeromorphicAt c (φ z) := by
    rw [hφz]
    exact (kDiff Fc Jc hFm hJm k).meromorphic x _ ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
  have h1 : meromorphicOrderAt (c ∘ φ) z = (kDiff Fc Jc hFm hJm k).order x * (e : WithTop ℤ) := by
    rw [hcm.meromorphicOrderAt_comp hφ hnc, hana, hφz]
    rfl
  have h2 : meromorphicOrderAt (deriv φ) z = (((e : ℤ) - 1 : ℤ) : WithTop ℤ) := by
    have := meromorphicOrderAt_deriv_eq_sub_one (n := (e : ℤ)) (by exact_mod_cast he) hord
    have hd : deriv (fun w ↦ φ w - φ z) = deriv φ := funext fun w ↦ deriv_sub_const _
    rwa [hd] at this
  rw [meromorphicOrderAt_congr (interior_eq hF hJ z)]
  change meromorphicOrderAt ((c ∘ φ) * (deriv φ) ^ k) z = _
  rw [meromorphicOrderAt_mul (hcm.comp_analyticAt hφ) (hφ.deriv.meromorphicAt.zpow k),
    meromorphicOrderAt_zpow hφ.deriv.meromorphicAt, h1, h2]
  rfl

/-- **Lemma 4.11 (a)**: $\mathrm{ord}_z(f) = e\,\mathrm{ord}_P(\omega) + k(e - 1)$. -/
theorem order_interior {Fc Jc : modularCurve Γ → ℂ} (hFm : ∀ y, TauCeti.RiemannSurface.MeromorphicAt Fc y)
    (hJm : ∀ y, TauCeti.RiemannSurface.MeromorphicAt Jc y)
    (hF : ∀ z, quotJ f k z = Fc (modularCurve.proj Γ z)) (hJ : ∀ z, jFun z = Jc (modularCurve.proj Γ z))
    (z : ℍ) (m : ℤ) (hm : (kDiff Fc Jc hFm hJm k).order (modularCurve.proj Γ z) = m) :
    meromorphicOrderAt (f ∘ ofComplex) (z : ℂ) =
      ((stabOrder Γ z * m + k * (stabOrder Γ z - 1 : ℕ) : ℤ) : WithTop ℤ) := by
  rw [order_interior_gen hFm hJm hF hJ z, hm, Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (stabOrder_ne_zero z))]
  norm_cast
  ring_nf

end Orders

section Cusps

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {f : ℍ → ℂ}

/-- **Lemma 4.11 (b)**, in `WithTop ℤ`: at the cusp $\gamma(i\infty)$, $\mathrm{ord}(f) = \mathrm{ord}_P(\omega) + k$. -/
theorem order_cusp_gen (hf : IsMeromorphicModularForm Γ k f) {Fc Jc : modularCurve Γ → ℂ}
    (hFm : ∀ y, TauCeti.RiemannSurface.MeromorphicAt Fc y) (hJm : ∀ y, TauCeti.RiemannSurface.MeromorphicAt Jc y)
    (hF : ∀ z, quotJ f k z = Fc (modularCurve.proj Γ z)) (hJ : ∀ z, jFun z = Jc (modularCurve.proj Γ z))
    (γ : SL(2, ℤ)) :
    cuspOrder Γ k f γ =
      (kDiff Fc Jc hFm hJm k).order (Subgroup.CompactifiedQuotient.ofCusp (Γ.cuspOrbitOfSL2Z γ)) + (k : WithTop ℤ) := by
  obtain ⟨n, hn, hw⟩ := exists_nat_cuspWidth Γ γ
  set y : modularCurve Γ := Subgroup.CompactifiedQuotient.ofCusp (Γ.cuspOrbitOfSL2Z γ)
  set u := chartAt ℂ y y
  -- the orders of `F` and `J` at the cusp
  have hFo : TauCeti.RiemannSurface.meromorphicOrderAt Fc y = cuspOrder Γ 0 (quotJ f k) γ :=
    order_descent_cusp hF γ
  have hJo : meromorphicOrderAt (Jc ∘ (chartAt ℂ y).symm) u = ((-(n : ℤ) : ℤ) : WithTop ℤ) := by
    have := order_descent_cusp hJ γ
    rw [TauCeti.RiemannSurface.meromorphicOrderAt_def] at this
    rw [this]
    unfold cuspOrder
    rw [jFun_slash, hw, order_cuspFunction_jFun hn]
  have hdJ : meromorphicOrderAt (deriv (Jc ∘ (chartAt ℂ y).symm)) u = ((-(n : ℤ) - 1 : ℤ) : WithTop ℤ) :=
    meromorphicOrderAt_deriv_eq_sub_one (by simp; omega) hJo
  have hFm' : MeromorphicAt (Fc ∘ (chartAt ℂ y).symm) u := hFm y
  have hJm' : MeromorphicAt (Jc ∘ (chartAt ℂ y).symm) u := hJm y
  have hord : (kDiff Fc Jc hFm hJm k).order y =
      cuspOrder Γ 0 (quotJ f k) γ + (k : WithTop ℤ) * ((-(n : ℤ) - 1 : ℤ) : WithTop ℤ) := by
    change meromorphicOrderAt ((Fc ∘ (chartAt ℂ y).symm) * deriv (Jc ∘ (chartAt ℂ y).symm) ^ k) u = _
    rw [meromorphicOrderAt_mul hFm' (hJm'.deriv.zpow _), meromorphicOrderAt_zpow hJm'.deriv, hdJ, ← hFo]
    rfl
  rw [cuspOrder_eq_quotJ hf γ hn hw, hord]
  cases cuspOrder Γ 0 (quotJ f k) γ with
  | top => simp
  | coe a =>
    norm_cast
    ring_nf

/-- **Lemma 4.11 (b)**: at the cusp $\gamma(i\infty)$, $\mathrm{ord}(f) = \mathrm{ord}_P(\omega) + k$. -/
theorem order_cusp (hf : IsMeromorphicModularForm Γ k f) {Fc Jc : modularCurve Γ → ℂ}
    (hFm : ∀ y, TauCeti.RiemannSurface.MeromorphicAt Fc y) (hJm : ∀ y, TauCeti.RiemannSurface.MeromorphicAt Jc y)
    (hF : ∀ z, quotJ f k z = Fc (modularCurve.proj Γ z)) (hJ : ∀ z, jFun z = Jc (modularCurve.proj Γ z))
    (γ : SL(2, ℤ)) (m : ℤ)
    (hm : (kDiff Fc Jc hFm hJm k).order (Subgroup.CompactifiedQuotient.ofCusp (Γ.cuspOrbitOfSL2Z γ)) = m) :
    cuspOrder Γ k f γ = ((m + k : ℤ) : WithTop ℤ) := by
  rw [order_cusp_gen hf hFm hJm hF hJ γ, hm]
  norm_cast

end Cusps

/-- **Lemma 4.11** (Milne, p. 52), unconditionally: for every subgroup $\Gamma$ of finite index in
$\mathrm{SL}_2(\mathbb Z)$, a meromorphic modular form of weight $2k$ defines a meromorphic $k$-fold differential on
$X(\Gamma)$ with the order relations (a), (b). -/
@[kb "milne2017mf" "Section 4, Lemma 4.11 (pdf p. 52)"]
theorem modularFormDifferential (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : ModularFormDifferential Γ where
  exists_diff k f hf := by
    obtain ⟨Fc, hFm, hF⟩ := exists_descent (quotJ_isModularFunction hf)
    obtain ⟨Jc, hJm, hJ⟩ := exists_descent (jFun_isModularFunction' Γ)
    refine ⟨kDiff Fc Jc hFm hJm k, fun z ↦ (interior_eq hF hJ z).trans
      (Eventually.of_forall fun w ↦ by simp only [zpow_natCast]; rfl), fun z m hm ↦ order_interior hFm hJm hF hJ z m hm,
      fun C γ hC m hm ↦ ?_⟩
    have hC' : C = Γ.cuspOrbitOfSL2Z γ := Subtype.ext (by rw [hC, Subgroup.cuspOrbitOfSL2Z_val])
    subst hC'
    exact order_cusp hf hFm hJm hF hJ γ m hm

end UncondDiff

end ModularFormsKB.Milne
