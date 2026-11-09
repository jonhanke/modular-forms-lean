import ModularFormsKB.Milne.Ch4.UncondValence
import ModularFormsKB.Milne.Ch4.UncondDimensionNF
import ModularFormsKB.Milne.RiemannSurface.Results

/-!
# Milne, Theorem 4.9 (dimension formula) from Riemann–Roch on $X(\Gamma)$

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Section 4, Theorem 4.9 (pdf p. 51).

For a subgroup $\Gamma$ of finite index in $\mathrm{SL}_2(\mathbb Z)$ and $k \ge 1$, Milne identifies
$M_{2k}(\Gamma)$ with $L(D_k)$ on $X(\Gamma)$ via Lemma 4.11 and applies Corollary 1.22. Here
$\omega = F\,(dJ)^k$ with $F$ the function on $X(\Gamma)$ induced by $f/(j')^k$ (`UncondDiff`), so the space is
$L(D_k)$ for the divisor
$D_k = k\,\operatorname{div}(dJ) + \sum_P \lfloor k(1 - 1/e_P)\rfloor P + k\sum_{\text{cusps}} Q$.

## Main results
* `UncondDim.equivRRSpace`: $M_{2k}(\Gamma) \cong L(D_k)$, $f \mapsto F$.
* `UncondDim.degree_divisorK`: $\deg D_k = k(2g - 2) + \sum_P\lfloor k(1-1/e_P)\rfloor + k\epsilon_\infty$.
* `dimensionFormula_of_riemannRoch`: `RiemannRochStatement (modularCurve Γ)` and
  `CanonicalDegreeStatement (modularCurve Γ)` imply `DimensionFormula Γ`.
-/

open UpperHalfPlane Complex Filter Topology ModularForm MulAction
open scoped MatrixGroups Manifold Real ContDiff

noncomputable section

namespace ModularFormsKB.Milne

namespace UncondDim

open TauCeti.RiemannSurface MeromorphicFunction UncondDiff UncondValence

section Basic

variable {Γ : Subgroup SL(2, ℤ)}

/-- $e_z$ depends only on the orbit of $z$. -/
theorem stabOrder_eq_of_proj_eq {z w : ℍ} (h : modularCurve.proj Γ z = modularCurve.proj Γ w) :
    stabOrder Γ z = stabOrder Γ w := by
  have h' := Quotient.exact (Subgroup.CompactifiedQuotient.ofQuotient_injective h)
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h')
  unfold stabOrder
  rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact (Subgroup.card_map_of_injective (MulAut.conj g).injective)

/-- Pulling back to $\mathbb H$ and the order formula $\mathrm{ord}_z(F \circ p) = e_z\,\mathrm{ord}_{p(z)}(F)$. -/
theorem order_pullback (F : modularCurve Γ → ℂ) (z : ℍ) :
    _root_.meromorphicOrderAt (F ∘ modularCurve.proj Γ ∘ ofComplex) (z : ℂ) =
      stabOrder Γ z * TauCeti.RiemannSurface.meromorphicOrderAt F (modularCurve.proj Γ z) := by
  have h := Subgroup.CompactifiedQuotient.meromorphicOrderAt_comp_ofQuotient_mk F z
  rw [TauCeti.UpperHalfPlane.meromorphicOrderAt_eq_meromorphicOrderAt_comp_ofComplex] at h
  exact h

/-- **Equality of meromorphic functions on $X(\Gamma)$ from one point of $\mathbb H$.** If the pullbacks of `F₁`
and `F₂` agree on a punctured neighbourhood of a single point of $\mathbb H$, the meromorphic functions they define
are equal (the difference has order $\top$ at one point). -/
theorem ofMeromorphic_eq_of_pullback {F₁ F₂ : modularCurve Γ → ℂ} (h₁ : ∀ y, MeromorphicAt F₁ y)
    (h₂ : ∀ y, MeromorphicAt F₂ y) (z : ℍ)
    (h : (F₁ ∘ modularCurve.proj Γ ∘ ofComplex) =ᶠ[𝓝[≠] (z : ℂ)] (F₂ ∘ modularCurve.proj Γ ∘ ofComplex)) :
    ofMeromorphic h₁ = ofMeromorphic h₂ := by
  have hm : ∀ y, MeromorphicAt (fun x ↦ F₁ x - F₂ x) y := fun y ↦ (h₁ y).sub (h₂ y)
  have h0 : (fun x ↦ F₁ x - F₂ x) ∘ modularCurve.proj Γ ∘ ofComplex =ᶠ[𝓝[≠] (z : ℂ)] 0 := by
    filter_upwards [h] with w hw
    simp only [Function.comp_apply, Pi.zero_apply] at hw ⊢
    rw [hw, sub_self]
  have ho := order_pullback (Γ := Γ) (fun x ↦ F₁ x - F₂ x) z
  rw [_root_.meromorphicOrderAt_eq_top_iff.2 h0] at ho
  have hx : TauCeti.RiemannSurface.meromorphicOrderAt (fun x ↦ F₁ x - F₂ x) (modularCurve.proj Γ z) = ⊤ := by
    by_contra hne
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hne
    rw [← ha] at ho
    have : ((stabOrder Γ z : ℤ) : WithTop ℤ) * (a : WithTop ℤ) = ((stabOrder Γ z * a : ℤ) : WithTop ℤ) := by
      norm_cast
    exact WithTop.top_ne_coe (ho.trans this)
  rw [← order_ofMeromorphic hm, AddValuation.top_iff, ofMeromorphic_sub h₁ h₂, sub_eq_zero] at hx
  exact hx

end Basic

section Periodic

open Matrix

theorem slash_upperRight (G : ℍ → ℂ) (k : ℤ) (w : ℝ) (z : ℍ) :
    (G ∣[2 * k] GeneralLinearGroup.upperRightHom w) z = G (w +ᵥ z) := by
  have : GeneralLinearGroup.upperRightHom w • z = w +ᵥ z := by
    ext
    simp [σ, num, denom, coe_vadd, UpperHalfPlane.coe_smul, add_comm]
  simp_rw [slash_def, this]
  simp [σ, denom, GeneralLinearGroup.val_det_apply]

theorem slash_neg_upperRight (G : ℍ → ℂ) (k : ℤ) (w : ℝ) (z : ℍ) :
    (G ∣[2 * k] (-GeneralLinearGroup.upperRightHom w)) z = G (w +ᵥ z) := by
  have : (-GeneralLinearGroup.upperRightHom w) • z = w +ᵥ z := by
    ext
    simp [σ, num, denom, coe_vadd, UpperHalfPlane.coe_smul, add_comm]
  simp_rw [slash_def, this]
  simp [σ, denom, GeneralLinearGroup.val_det_apply, _root_.zpow_mul]

variable {Γ : Subgroup SL(2, ℤ)}

/-- A function of even weight $2k$ invariant under $\Gamma$, slashed by $\gamma$, is periodic of period the width of
the cusp $\gamma(i\infty)$ (an element $\pm T^h$ of $\gamma^{-1}\Gamma\gamma$ acts by $z \mapsto z + h$ in even
weight). -/
theorem periodic_slash {F : ℍ → ℂ} {k : ℤ} (hF : ∀ δ ∈ Γ, F ∣[2 * k] δ = F) (γ : SL(2, ℤ)) :
    Function.Periodic ((F ∣[2 * k] γ) ∘ ofComplex) (cuspWidth Γ γ) := by
  have hmem : cuspWidth Γ γ ∈ ((conjSubgroup Γ γ : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).periods := Subgroup.widthInfty_mem_periods _
  unfold Subgroup.periods at hmem
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_adjoinNegOne_iff, mem_coe_GL_iff,
    mem_coe_GL_iff] at hmem
  -- the slash by an element of the conjugate group fixes `F ∣ γ`
  have hinv : ∀ h ∈ conjSubgroup Γ γ, (F ∣[2 * k] γ) ∣[2 * k] h = F ∣[2 * k] γ := by
    intro h hh
    obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.1 hh
    rw [← SlashAction.slash_mul]
    have : γ * (MulAut.conj γ⁻¹).toMonoidHom δ = δ * γ := by
      simp [mul_assoc]
    rw [this, SlashAction.slash_mul, hF δ hδ]
  apply UpperHalfPlane.periodic_comp_ofComplex
  intro z
  rcases hmem with ⟨h, hh, he⟩ | ⟨h, hh, he⟩
  · have := congrFun (hinv h hh) z
    rw [SL_slash] at this
    have he' : SpecialLinearGroup.toGL (SpecialLinearGroup.map (Int.castRingHom ℝ) h) =
        GeneralLinearGroup.upperRightHom (cuspWidth Γ γ) := he
    rw [he', slash_upperRight] at this
    exact this
  · have := congrFun (hinv h hh) z
    rw [SL_slash] at this
    have he' : SpecialLinearGroup.toGL (SpecialLinearGroup.map (Int.castRingHom ℝ) h) =
        -GeneralLinearGroup.upperRightHom (cuspWidth Γ γ) := he
    rw [he', slash_neg_upperRight] at this
    exact this

end Periodic

section Forms

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}

omit [Γ.FiniteIndex] in
theorem slash_eq_of_mem (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * k)) {δ : SL(2, ℤ)} (hδ : δ ∈ Γ) :
    (f : ℍ → ℂ) ∣[2 * k] δ = f := by
  rw [SL_slash]
  exact SlashInvariantForm.slash_action_eqn f _ ((mem_coe_GL_iff _ _).2 ⟨δ, hδ, rfl⟩)

theorem analyticAt_of_mdifferentiable {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (z : ℍ) :
    AnalyticAt ℂ (g ∘ ofComplex) (z : ℂ) := by
  refine Complex.analyticAt_iff_eventually_differentiableAt.2 ?_
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  have := UpperHalfPlane.mdifferentiableAt_iff.1 (hg ⟨w, hw⟩)
  simpa using this

/-- The cusp function of a modular form slashed by $\gamma \in \mathrm{SL}_2(\mathbb Z)$ is analytic at $q = 0$. -/
theorem analyticAt_cuspFunction (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * k)) (γ : SL(2, ℤ)) :
    AnalyticAt ℂ (Function.Periodic.cuspFunction (cuspWidth Γ γ) (((f : ℍ → ℂ) ∣[2 * k] γ) ∘ ofComplex)) 0 := by
  obtain ⟨n, hn, hw⟩ := exists_nat_cuspWidth Γ γ
  have hpos : 0 < cuspWidth Γ γ := by rw [hw]; exact_mod_cast hn
  have hc : IsCusp (Matrix.SpecialLinearGroup.mapGL ℝ γ • (OnePoint.infty : OnePoint ℝ))
      (Γ : Subgroup (GL (Fin 2) ℝ)) := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff']
    exact ⟨γ, rfl⟩
  have hb : IsBoundedAtImInfty ((f : ℍ → ℂ) ∣[2 * k] γ) := by
    have := f.bdd_at_cusps' hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z (by
      rw [isCusp_SL2Z_iff']; exact ⟨γ, rfl⟩)] at this
    exact this γ rfl
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((f : ℍ → ℂ) ∣[2 * k] γ) := by
    rw [SL_slash]; exact f.holo'.slash _ _
  exact UpperHalfPlane.analyticAt_cuspFunction_zero hpos (periodic_slash (fun δ hδ ↦ slash_eq_of_mem f hδ) γ) hhol hb

/-- A modular form of weight $2k$ is a meromorphic modular form. -/
theorem isMeromorphicModularForm (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * k)) :
    IsMeromorphicModularForm Γ k f where
  slash _ hδ := slash_eq_of_mem f hδ
  meromorphic z := (analyticAt_of_mdifferentiable f.holo' z).meromorphicAt
  meromorphic_cusp γ := (analyticAt_cuspFunction f γ).meromorphicAt

omit [Γ.FiniteIndex] in
theorem order_nonneg (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * k)) (z : ℍ) :
    0 ≤ _root_.meromorphicOrderAt ((f : ℍ → ℂ) ∘ ofComplex) (z : ℂ) :=
  (analyticAt_of_mdifferentiable f.holo' z).meromorphicOrderAt_nonneg

theorem cuspOrder_nonneg (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * k)) (γ : SL(2, ℤ)) :
    0 ≤ cuspOrder Γ k f γ :=
  (analyticAt_cuspFunction f γ).meromorphicOrderAt_nonneg

end Forms

section Divisor

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- The function $J$ on $X(\Gamma)$ induced by $j$. -/
def Jc : modularCurve Γ → ℂ := (exists_descent (jFun_isModularFunction' Γ)).choose

theorem Jc_meromorphic : ∀ y, MeromorphicAt (Jc Γ) y := (exists_descent (jFun_isModularFunction' Γ)).choose_spec.1

theorem Jc_spec : ∀ z, jFun z = Jc Γ (modularCurve.proj Γ z) :=
  (exists_descent (jFun_isModularFunction' Γ)).choose_spec.2

/-- The differential $dJ$ on $X(\Gamma)$. -/
def dJ : RiemannSurface.MeromorphicDifferential (modularCurve Γ) := dOf (Jc Γ) (Jc_meromorphic Γ)

theorem dJ_ord_ne_top (x : modularCurve Γ) : (dJ Γ).ord x ≠ ⊤ :=
  dOf_ord_ne_top _ (Jc_nonconst (Jc_meromorphic Γ) (Jc_spec Γ)) x

theorem dJ_ord_eq (x : modularCurve Γ) : (dJ Γ).ord x = ((dJ Γ).ordZ x : WithTop ℤ) := by
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 (dJ_ord_ne_top Γ x)
  unfold RiemannSurface.MeromorphicDifferential.ordZ
  rw [← hb, WithTop.untop₀_coe]

theorem dJ_ne_zero : ¬ (dJ Γ).IsZero := fun h ↦ dJ_ord_ne_top Γ (Classical.arbitrary _) (h _)

/-- The correction term of $D_k$: $\lfloor k(1 - 1/e_P)\rfloor$ at $P \in \Gamma\backslash\mathbb H$, $k$ at the
cusps. -/
def corr (k : ℕ) : modularCurve Γ → ℤ
  | .ofQuotient p => ⌊(k : ℚ) * (1 - 1 / (stabOrder Γ p.out : ℚ))⌋
  | .ofCusp _ => k

omit [Γ.FiniteIndex] in
/-- $e_z = 1$ off the elliptic orbits. -/
theorem stabOrder_out_eq_one {p : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ}
    (hp : p ∉ (Γ.map sl2zToPSL2R).ellipticOrbits) : stabOrder Γ p.out = 1 := by
  rw [← Quotient.out_eq p, Subgroup.quotientMk_mem_ellipticOrbits_iff, not_not, TauCeti.mem_freeLocus] at hp
  unfold stabOrder
  rw [hp]
  exact Subgroup.card_bot

theorem finite_support_corr (k : ℕ) : (Function.support (corr Γ k)).Finite := by
  have hE := (Γ.map sl2zToPSL2R).finite_ellipticOrbits
  refine ((hE.image Subgroup.CompactifiedQuotient.ofQuotient).union
    (Set.finite_range (Subgroup.CompactifiedQuotient.ofCusp (Γ := Γ.map sl2zToPSL2R)))).subset ?_
  intro x hx
  cases x with
  | ofQuotient p =>
    left
    refine ⟨p, ?_, rfl⟩
    by_contra hp
    apply hx
    simp [corr, stabOrder_out_eq_one Γ hp]
  | ofCusp C => exact Or.inr ⟨C, rfl⟩

theorem finite_support_divK (k : ℕ) :
    (Function.support fun x ↦ (k : ℤ) * (dJ Γ).ordZ x + corr Γ k x).Finite :=
  (((RiemannSurface.MeromorphicDifferential.finite_support_ordZ (dJ_ne_zero Γ)).subset
    (Function.support_mul_subset_right _ _)).union (finite_support_corr Γ k)).subset
    (Function.support_add _ _)

/-- **The divisor $D_k$** with $M_{2k}(\Gamma) \cong L(D_k)$:
$D_k = k\operatorname{div}(dJ) + \sum_P\lfloor k(1-1/e_P)\rfloor P + k\sum_Q Q$. -/
def divK (k : ℕ) : TauCeti.AlgebraicGeometry.WeilDivisor (modularCurve Γ) :=
  Finsupp.ofSupportFinite _ (finite_support_divK Γ k)

theorem divK_apply (k : ℕ) (x : modularCurve Γ) : divK Γ k x = k * (dJ Γ).ordZ x + corr Γ k x := rfl

end Divisor

section Ineq

/-- Interior inequality: $e\,m + k(e-1) \ge 0 \iff m \ge -\lfloor k(1 - 1/e)\rfloor$, with
$m = \mathrm{ord}(F) + k\,\mathrm{ord}(dJ)$. -/
theorem interior_iff {A : WithTop ℤ} {b : ℤ} {e k : ℕ} (he : 0 < e) :
    0 ≤ (A + ((k : ℤ) : WithTop ℤ) * (b : WithTop ℤ)) * ((e : ℤ) : WithTop ℤ) + ((k * ((e : ℤ) - 1) : ℤ) : WithTop ℤ) ↔
      ((-((k : ℤ) * b + ⌊(k : ℚ) * (1 - 1 / (e : ℚ))⌋) : ℤ) : WithTop ℤ) ≤ A := by
  cases A with
  | top =>
    have : ((e : ℤ) : WithTop ℤ) ≠ 0 := by exact_mod_cast he.ne'
    rw [WithTop.top_add, WithTop.top_mul this, WithTop.top_add]
    simp
  | coe a =>
    have hc : ((a : WithTop ℤ) + ((k : ℤ) : WithTop ℤ) * (b : WithTop ℤ)) * ((e : ℤ) : WithTop ℤ) +
        ((k * ((e : ℤ) - 1) : ℤ) : WithTop ℤ) = (((a + k * b) * e + k * ((e : ℤ) - 1) : ℤ) : WithTop ℤ) := by
      norm_cast
    rw [hc, WithTop.coe_le_coe, WithTop.coe_nonneg]
    have heq : (0 : ℚ) < e := by exact_mod_cast he
    constructor
    · intro h
      have : (-(a + k * b) : ℤ) ≤ ⌊(k : ℚ) * (1 - 1 / (e : ℚ))⌋ := by
        rw [Int.le_floor]
        have h' : (0 : ℚ) ≤ ((a + k * b) * e + k * ((e : ℤ) - 1) : ℤ) := by exact_mod_cast h
        push_cast at h' ⊢
        have hk : (k : ℚ) * (1 - 1 / (e : ℚ)) = (k * e - k) / e := by field_simp
        rw [hk, le_div_iff₀ heq]
        nlinarith
      linarith
    · intro h
      have h1 : (-(a + k * b) : ℤ) ≤ ⌊(k : ℚ) * (1 - 1 / (e : ℚ))⌋ := by linarith
      rw [Int.le_floor] at h1
      have : (0 : ℚ) ≤ ((a + k * b) * e + k * ((e : ℤ) - 1) : ℤ) := by
        push_cast at h1 ⊢
        have h2 : (-((a : ℚ) + k * b)) * e ≤ k * (1 - 1 / (e : ℚ)) * e := mul_le_mul_of_nonneg_right h1 heq.le
        have h3 : (k : ℚ) * (1 - 1 / (e : ℚ)) * e = k * (e - 1) := by field_simp
        nlinarith
      exact_mod_cast this

/-- Cusp inequality: $m + k \ge 0 \iff \mathrm{ord}(F) \ge -(kb + k)$. -/
theorem cusp_iff {A : WithTop ℤ} {b : ℤ} {k : ℕ} :
    0 ≤ A + ((k : ℤ) : WithTop ℤ) * (b : WithTop ℤ) + ((k : ℤ) : WithTop ℤ) ↔
      ((-((k : ℤ) * b + k) : ℤ) : WithTop ℤ) ≤ A := by
  cases A with
  | top => simp
  | coe a =>
    have hc : (a : WithTop ℤ) + ((k : ℤ) : WithTop ℤ) * (b : WithTop ℤ) + ((k : ℤ) : WithTop ℤ) =
        ((a + k * b + k : ℤ) : WithTop ℤ) := by norm_cast
    rw [hc, WithTop.coe_le_coe, WithTop.coe_nonneg]
    omega

end Ineq

section Forward

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℕ}

/-- The function $F = f/(j')^k$ on $X(\Gamma)$ attached to $f \in M_{2k}(\Gamma)$. -/
def Fc (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * (k : ℤ))) : modularCurve Γ → ℂ :=
  (exists_descent (quotJ_isModularFunction (isMeromorphicModularForm f))).choose

theorem Fc_meromorphic (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * (k : ℤ))) :
    ∀ y, MeromorphicAt (Fc f) y :=
  (exists_descent (quotJ_isModularFunction (isMeromorphicModularForm f))).choose_spec.1

theorem Fc_spec (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * (k : ℤ))) :
    ∀ z, quotJ f k z = Fc f (modularCurve.proj Γ z) :=
  (exists_descent (quotJ_isModularFunction (isMeromorphicModularForm f))).choose_spec.2

omit [Γ.FiniteIndex] in
theorem proj_out (p : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    modularCurve.proj Γ p.out = Subgroup.CompactifiedQuotient.ofQuotient p := by
  unfold modularCurve.proj
  rw [Quotient.out_eq]

omit [Γ.FiniteIndex] in
theorem corr_proj (z : ℍ) :
    corr Γ k (modularCurve.proj Γ z) = ⌊(k : ℚ) * (1 - 1 / (stabOrder Γ z : ℚ))⌋ := by
  have h : stabOrder Γ (Quotient.out (Quotient.mk (orbitRel (Γ.map sl2zToPSL2R) ℍ) z)) = stabOrder Γ z :=
    stabOrder_eq_of_proj_eq (by rw [proj_out]; rfl)
  change ⌊(k : ℚ) * (1 - 1 / (stabOrder Γ (Quotient.out (Quotient.mk _ z)) : ℚ))⌋ = _
  rw [h]

/-- **Lemma 4.11 for $L(D_k)$, interior points**: for a meromorphic modular form $f$ with descended $F$,
$\mathrm{ord}_z(f) \ge 0$ at a representative $z$ of $P$ iff $\mathrm{ord}_P(F) \ge -D_k(P)$. -/
theorem order_nonneg_iff_interior {f : ℍ → ℂ} (hf : IsMeromorphicModularForm Γ k f) {F : modularCurve Γ → ℂ}
    (hFm : ∀ y, MeromorphicAt F y) (hF : ∀ z, quotJ f k z = F (modularCurve.proj Γ z)) (z : ℍ) :
    0 ≤ _root_.meromorphicOrderAt (f ∘ ofComplex) (z : ℂ) ↔
      ((-(divK Γ k (modularCurve.proj Γ z)) : ℤ) : WithTop ℤ) ≤
        TauCeti.RiemannSurface.meromorphicOrderAt F (modularCurve.proj Γ z) := by
  have _ := hf
  rw [order_interior_gen hFm (Jc_meromorphic Γ) hF (Jc_spec Γ) z, order_kDiff,
    show (dOf (Jc Γ) (Jc_meromorphic Γ)) = dJ Γ from rfl, dJ_ord_eq, divK_apply, corr_proj]
  exact interior_iff (Nat.pos_of_ne_zero (stabOrder_ne_zero z))

/-- **Lemma 4.11 for $L(D_k)$, cusps**: $\mathrm{ord}_\gamma(f) \ge 0$ iff $\mathrm{ord}_Q(F) \ge -D_k(Q)$. -/
theorem order_nonneg_iff_cusp {f : ℍ → ℂ} (hf : IsMeromorphicModularForm Γ k f) {F : modularCurve Γ → ℂ}
    (hFm : ∀ y, MeromorphicAt F y) (hF : ∀ z, quotJ f k z = F (modularCurve.proj Γ z)) (γ : SL(2, ℤ)) :
    0 ≤ cuspOrder Γ k f γ ↔
      ((-(divK Γ k (Subgroup.CompactifiedQuotient.ofCusp (Γ.cuspOrbitOfSL2Z γ))) : ℤ) : WithTop ℤ) ≤
        TauCeti.RiemannSurface.meromorphicOrderAt F (Subgroup.CompactifiedQuotient.ofCusp (Γ.cuspOrbitOfSL2Z γ)) := by
  rw [order_cusp_gen hf hFm (Jc_meromorphic Γ) hF (Jc_spec Γ) γ, order_kDiff,
    show (dOf (Jc Γ) (Jc_meromorphic Γ)) = dJ Γ from rfl, dJ_ord_eq, divK_apply]
  exact cusp_iff

theorem ofMeromorphic_Fc_mem (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * (k : ℤ))) :
    ofMeromorphic (Fc_meromorphic f) ∈ RiemannSurface.rrSpace (modularCurve Γ) (divK Γ k) := by
  intro x
  rw [order_ofMeromorphic]
  cases x with
  | ofQuotient p =>
    have := (order_nonneg_iff_interior (isMeromorphicModularForm f) (Fc_meromorphic f) (Fc_spec f) p.out).1
      (order_nonneg f p.out)
    rwa [proj_out] at this
  | ofCusp C =>
    obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
    exact (order_nonneg_iff_cusp (isMeromorphicModularForm f) (Fc_meromorphic f) (Fc_spec f) γ).1
      (cuspOrder_nonneg f γ)

variable (Γ k) in
/-- **The map $M_{2k}(\Gamma) \to L(D_k)$**, $f \mapsto F = f/(j')^k$ (Milne, proof of Theorem 4.9). -/
def toRR : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * (k : ℤ)) →ₗ[ℂ]
    RiemannSurface.rrSpace (modularCurve Γ) (divK Γ k) where
  toFun f := ⟨ofMeromorphic (Fc_meromorphic f), ofMeromorphic_Fc_mem f⟩
  map_add' f g := by
    apply Subtype.ext
    simp only [Submodule.coe_add]
    rw [← ofMeromorphic_add]
    apply ofMeromorphic_eq_of_pullback _ _ UpperHalfPlane.I
    refine Eventually.of_forall fun w ↦ ?_
    simp only [Function.comp_apply]
    rw [← Fc_spec, Pi.add_apply, ← Fc_spec, ← Fc_spec]
    simp [quotJ, add_div]
  map_smul' c f := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply]
    rw [Algebra.smul_def, ← ofMeromorphic_const, ← ofMeromorphic_mul]
    apply ofMeromorphic_eq_of_pullback _ _ UpperHalfPlane.I
    refine Eventually.of_forall fun w ↦ ?_
    simp only [Function.comp_apply]
    rw [← Fc_spec, Pi.mul_apply, ← Fc_spec]
    simp [quotJ, mul_div_assoc]

theorem coe_toRR (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * (k : ℤ))) :
    (toRR Γ k f : MeromorphicFunction (modularCurve Γ)) = ofMeromorphic (Fc_meromorphic f) := rfl

/-- A function analytic at `z` that vanishes on a punctured neighbourhood of `z` vanishes at `z`. -/
theorem eq_zero_of_eventually {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z) (h : g =ᶠ[𝓝[≠] z] 0) : g z = 0 :=
  tendsto_nhds_unique (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' h.symm)

theorem toRR_injective : Function.Injective (toRR Γ k) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have h0 : ofMeromorphic (Fc_meromorphic f) = 0 := congrArg Subtype.val hf
  ext z
  have hx : TauCeti.RiemannSurface.meromorphicOrderAt (Fc f) (modularCurve.proj Γ z) = ⊤ := by
    rw [← order_ofMeromorphic (Fc_meromorphic f), h0, AddValuation.map_zero]
  have h := order_interior_gen (Fc_meromorphic f) (Jc_meromorphic Γ) (Fc_spec f) (Jc_spec Γ) z
  rw [order_kDiff _ _ (Fc_meromorphic f) (Jc_meromorphic Γ), hx, WithTop.top_add,
    WithTop.top_mul (by exact_mod_cast stabOrder_ne_zero z), WithTop.top_add] at h
  have := eq_zero_of_eventually (analyticAt_of_mdifferentiable f.holo' z) (meromorphicOrderAt_eq_top_iff.1 h)
  simpa [ofComplex_apply] using this

end Forward

section Backward

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℕ}

omit [Γ.FiniteIndex] in
theorem proj_smul {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (z : ℍ) : modularCurve.proj Γ (γ • z) = modularCurve.proj Γ z := by
  unfold modularCurve.proj
  congr 1
  apply Quotient.sound
  exact ⟨⟨sl2zToPSL2R γ, Subgroup.mem_map_of_mem _ hγ⟩, UpperHalfPlane.sl2zToPSL2R_smul γ z⟩

/-- The pullback of a meromorphic function on $X(\Gamma)$ is a modular function. -/
theorem isModularFunction_pullback {F : modularCurve Γ → ℂ} (hF : ∀ y, MeromorphicAt F y) :
    IsModularFunction Γ (fun z ↦ F (modularCurve.proj Γ z)) := by
  refine (isModularFunction_iff_compactifiedQuotient Γ _).2 ⟨fun γ hγ z ↦ by simp only [proj_smul hγ],
    fun z ↦ ?_, F, hF, fun z ↦ rfl⟩
  have h := Subgroup.CompactifiedQuotient.meromorphicAt_ofQuotient_mk_iff.1 (hF (modularCurve.proj Γ z))
  exact TauCeti.UpperHalfPlane.meromorphicAt_iff_meromorphicAt_comp_ofComplex.1 h

/-- The meromorphic modular form $g = (\Phi \circ p)\,(j')^k$ attached to $\Phi \in \mathcal M(X(\Gamma))$. -/
def gOf (Φ : MeromorphicFunction (modularCurve Γ)) (k : ℕ) : ℍ → ℂ :=
  fun z ↦ Φ.finitePart (modularCurve.proj Γ z) * jD z ^ (k : ℤ)

omit [Γ.FiniteIndex] in
theorem gOf_slash_apply (Φ : MeromorphicFunction (modularCurve Γ)) (γ : SL(2, ℤ)) (z : ℍ) :
    (gOf Φ k ∣[2 * (k : ℤ)] γ) z = Φ.finitePart (modularCurve.proj Γ (γ • z)) * jD z ^ (k : ℤ) := by
  rw [SL_slash_apply, gOf, jD_smul]
  have hd : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have h : (denom γ z ^ 2) ^ (k : ℤ) = denom γ z ^ (2 * (k : ℤ)) := by
    rw [zpow_mul]; norm_cast
  rw [mul_zpow, h, mul_assoc, mul_comm (denom γ z ^ (2 * (k : ℤ))), mul_assoc, ← zpow_add₀ hd]
  simp

theorem isMeromorphicModularForm_gOf (Φ : MeromorphicFunction (modularCurve Γ)) :
    IsMeromorphicModularForm Γ k (gOf Φ k) := by
  have hh := isModularFunction_pullback (Γ := Γ) Φ.meromorphicAt_finitePart
  have hh' : IsMeromorphicModularForm Γ 0 _ := hh
  refine ⟨fun γ hγ ↦ ?_, fun z ↦ ?_, fun γ ↦ ?_⟩
  · funext z
    rw [gOf_slash_apply, proj_smul hγ]
    rfl
  · exact (hh'.meromorphic z).mul ((jD_analyticAt z).meromorphicAt.zpow k)
  · obtain ⟨n, hn, hw⟩ := exists_nat_cuspWidth Γ γ
    have hc := hh'.meromorphic_cusp γ
    rw [hw] at hc ⊢
    have hE : Function.Periodic.cuspFunction (n : ℝ) ((gOf Φ k ∣[2 * (k : ℤ)] γ) ∘ ofComplex) =ᶠ[𝓝[≠] 0]
        Function.Periodic.cuspFunction (n : ℝ)
            (((fun z ↦ Φ.finitePart (modularCurve.proj Γ z)) ∣[(2 * 0 : ℤ)] γ) ∘ ofComplex) *
          Function.Periodic.cuspFunction (n : ℝ) (jD ∘ ofComplex) ^ (k : ℤ) := by
      filter_upwards [self_mem_nhdsWithin] with q hq
      simp only [Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq, Pi.mul_apply, Pi.pow_apply,
        Function.comp_apply]
      rw [gOf_slash_apply, SL_slash_apply]
      simp
    exact (hc.mul ((meromorphicAt_cuspFunction_jD hn).zpow k)).congr hE.symm

omit [Γ.FiniteIndex] in
/-- The function on $X(\Gamma)$ induced by $g/(j')^k$ is $\Phi$. -/
theorem ofMeromorphic_eq_of_gOf (Φ : MeromorphicFunction (modularCurve Γ)) {G : modularCurve Γ → ℂ}
    (hGm : ∀ y, MeromorphicAt G y) (hG : ∀ z, quotJ (gOf Φ k) k z = G (modularCurve.proj Γ z)) :
    ofMeromorphic hGm = Φ := by
  conv_rhs => rw [← ofMeromorphic_finitePart Φ]
  apply ofMeromorphic_eq_of_pullback _ _ UpperHalfPlane.I
  filter_upwards [jD_eventually_ne_zero UpperHalfPlane.I] with w hw
  simp only [Function.comp_apply, ← hG, quotJ, gOf]
  rw [mul_div_assoc, div_self (zpow_ne_zero _ hw), mul_one]

theorem order_gOf_nonneg {Φ : MeromorphicFunction (modularCurve Γ)}
    (hΦ : Φ ∈ RiemannSurface.rrSpace (modularCurve Γ) (divK Γ k)) (z : ℍ) :
    0 ≤ _root_.meromorphicOrderAt (gOf Φ k ∘ ofComplex) (z : ℂ) := by
  obtain ⟨G, hGm, hG⟩ := exists_descent (quotJ_isModularFunction (isMeromorphicModularForm_gOf (k := k) Φ))
  rw [order_nonneg_iff_interior (isMeromorphicModularForm_gOf Φ) hGm hG z, ← order_ofMeromorphic hGm,
    ofMeromorphic_eq_of_gOf Φ hGm hG]
  exact hΦ _

theorem cuspOrder_gOf_nonneg {Φ : MeromorphicFunction (modularCurve Γ)}
    (hΦ : Φ ∈ RiemannSurface.rrSpace (modularCurve Γ) (divK Γ k)) (γ : SL(2, ℤ)) :
    0 ≤ cuspOrder Γ k (gOf Φ k) γ := by
  obtain ⟨G, hGm, hG⟩ := exists_descent (quotJ_isModularFunction (isMeromorphicModularForm_gOf (k := k) Φ))
  rw [order_nonneg_iff_cusp (isMeromorphicModularForm_gOf Φ) hGm hG γ, ← order_ofMeromorphic hGm,
    ofMeromorphic_eq_of_gOf Φ hGm hG]
  exact hΦ _

theorem nf_gOf_slash (Φ : RiemannSurface.rrSpace (modularCurve Γ) (divK Γ k)) {δ : SL(2, ℤ)} (hδ : δ ∈ Γ) :
    UncondDimNF.nf (gOf (Φ : MeromorphicFunction (modularCurve Γ)) k) ∣[2 * (k : ℤ)] δ =
      UncondDimNF.nf (gOf (Φ : MeromorphicFunction (modularCurve Γ)) k) := by
  have hg := isMeromorphicModularForm_gOf (k := k) (Φ : MeromorphicFunction (modularCurve Γ))
  have h1 := hg.slash δ hδ
  have h2 := order_gOf_nonneg Φ.2
  exact UncondDimNF.nf_slash hg.meromorphic h2 h1

variable (k) in
/-- The slash-invariant form underlying the inverse map. -/
def ofRRSIF (Φ : RiemannSurface.rrSpace (modularCurve Γ) (divK Γ k)) :
    SlashInvariantForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * (k : ℤ)) where
  toFun := UncondDimNF.nf (gOf (Φ : MeromorphicFunction (modularCurve Γ)) k)
  slash_action_eq' γ hγ := by
    obtain ⟨δ, hδ, rfl⟩ := (mem_coe_GL_iff _ _).1 hγ
    have h := nf_gOf_slash Φ hδ
    rw [SL_slash] at h
    exact h

theorem coe_ofRRSIF (Φ : RiemannSurface.rrSpace (modularCurve Γ) (divK Γ k)) :
    (ofRRSIF k Φ : ℍ → ℂ) = UncondDimNF.nf (gOf (Φ : MeromorphicFunction (modularCurve Γ)) k) := rfl

variable (k) in
/-- **The inverse map $L(D_k) \to M_{2k}(\Gamma)$**: $\Phi \mapsto (\Phi \circ p)(j')^k$, with its removable
singularities filled in. -/
def ofRR (Φ : RiemannSurface.rrSpace (modularCurve Γ) (divK Γ k)) :
    ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * (k : ℤ)) where
  toSlashInvariantForm := ofRRSIF k Φ
  holo' := by
    rw [coe_ofRRSIF]
    have hg := isMeromorphicModularForm_gOf (k := k) (Φ : MeromorphicFunction (modularCurve Γ))
    have h2 := order_gOf_nonneg Φ.2
    exact UncondDimNF.nf_mdifferentiable hg.meromorphic h2
  bdd_at_cusps' {c} hc := by
    have hc' : IsCusp c 𝒮ℒ := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).1 hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc']
    intro γ _
    have hg := isMeromorphicModularForm_gOf (k := k) (Φ : MeromorphicFunction (modularCurve Γ))
    obtain ⟨n, hn, hw⟩ := exists_nat_cuspWidth Γ γ
    have hpos : 0 < cuspWidth Γ γ := by rw [hw]; exact_mod_cast hn
    change IsBoundedAtImInfty (UncondDimNF.nf (gOf (Φ : MeromorphicFunction (modularCurve Γ)) k) ∣[2 * (k : ℤ)] γ)
    have h2 := order_gOf_nonneg Φ.2
    have h3 := cuspOrder_gOf_nonneg Φ.2 γ
    exact UncondDimNF.nf_isBoundedAtImInfty hg.meromorphic h2 hpos (periodic_slash hg.slash γ)
      (hg.meromorphic_cusp γ) h3

theorem coe_ofRR (Φ : RiemannSurface.rrSpace (modularCurve Γ) (divK Γ k)) :
    (ofRR k Φ : ℍ → ℂ) = UncondDimNF.nf (gOf (Φ : MeromorphicFunction (modularCurve Γ)) k) := rfl

theorem toRR_ofRR (Φ : RiemannSurface.rrSpace (modularCurve Γ) (divK Γ k)) : toRR Γ k (ofRR k Φ) = Φ := by
  apply Subtype.ext
  rw [coe_toRR]
  conv_rhs => rw [← ofMeromorphic_finitePart (Φ : MeromorphicFunction (modularCurve Γ))]
  apply ofMeromorphic_eq_of_pullback _ _ UpperHalfPlane.I
  have hg := isMeromorphicModularForm_gOf (k := k) (Φ : MeromorphicFunction (modularCurve Γ))
  filter_upwards [jD_eventually_ne_zero UpperHalfPlane.I, UncondDimNF.nf_eventuallyEq hg.meromorphic UpperHalfPlane.I]
    with w hw hn
  simp only [Function.comp_apply] at hn ⊢
  rw [← Fc_spec, quotJ]
  rw [coe_ofRR, hn, gOf, mul_div_assoc, div_self (zpow_ne_zero _ hw), mul_one]

theorem toRR_surjective : Function.Surjective (toRR Γ k) := fun Φ ↦ ⟨ofRR k Φ, toRR_ofRR Φ⟩

variable (Γ k) in
/-- **$M_{2k}(\Gamma) \cong L(D_k)$** (Milne, proof of Theorem 4.9), for every $k \ge 0$. -/
def equivRRSpace : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * (k : ℤ)) ≃ₗ[ℂ]
    RiemannSurface.rrSpace (modularCurve Γ) (divK Γ k) :=
  LinearEquiv.ofBijective (toRR Γ k) ⟨toRR_injective, toRR_surjective⟩

theorem finrank_eq_ell :
    Module.finrank ℂ (ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * (k : ℤ))) =
      RiemannSurface.ell (modularCurve Γ) (divK Γ k) :=
  (equivRRSpace Γ k).finrank_eq

end Backward

section Degree

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

open TauCeti.AlgebraicGeometry

theorem finite_ellipticOrbits : (Γ.map sl2zToPSL2R).ellipticOrbits.Finite :=
  (Γ.map sl2zToPSL2R).finite_ellipticOrbits

/-- A sum over the orbits of $\Gamma$ on $\mathbb H$ of a function vanishing off the elliptic orbits is a sum over
the elliptic orbits. -/
theorem finsum_eq_sum_elliptic {M : Type*} [AddCommMonoid M] (f : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ → M)
    (hf : ∀ p, p ∉ (Γ.map sl2zToPSL2R).ellipticOrbits → f p = 0) :
    ∑ᶠ p, f p = ∑ p ∈ (finite_ellipticOrbits Γ).toFinset, f p := by
  refine finsum_eq_sum_of_support_subset f fun p hp ↦ ?_
  rw [Set.Finite.coe_toFinset]
  by_contra h
  exact hp (hf p h)

theorem ellipticTerm_eq (k : ℕ) :
    ellipticTerm Γ k = ∑ p ∈ (finite_ellipticOrbits Γ).toFinset,
      ⌊(k : ℚ) * (1 - 1 / (stabOrder Γ p.out : ℚ))⌋ :=
  finsum_mem_eq_finite_toFinset_sum _ _

theorem cuspCount_eq : cuspCount Γ = Nat.card (Γ.map sl2zToPSL2R).CuspOrbit :=
  Nat.card_eq_of_bijective _ (bijective_cuspOrbitOfSL2Z_cuspRep Γ)

theorem cuspCount_pos : 0 < cuspCount Γ := by
  rw [cuspCount_eq]
  have : Nonempty (Γ.map sl2zToPSL2R).CuspOrbit := ⟨Γ.cuspOrbitOfSL2Z 1⟩
  exact Nat.card_pos

/-- **The degree of $D_k$**: $\deg D_k = k(2g - 2) + \sum_P\lfloor k(1-1/e_P)\rfloor + k\epsilon_\infty$. -/
theorem degree_divK (hC : CanonicalDegreeStatement (modularCurve Γ)) (k : ℕ) :
    WeilDivisor.degree (divK Γ k) =
      k * (2 * (RiemannSurface.genus (modularCurve Γ) : ℤ) - 2) + ellipticTerm Γ k + k * cuspCount Γ := by
  have h1 : WeilDivisor.degree (divK Γ k) = ∑ᶠ x, divK Γ k x := by
    rw [WeilDivisor.degree_apply, finsum_eq_sum_of_support_subset _ (s := (divK Γ k).support)]
    intro x hx
    simpa using hx
  have hs1 : (Function.support fun x ↦ (k : ℤ) * (dJ Γ).ordZ x).Finite :=
    (RiemannSurface.MeromorphicDifferential.finite_support_ordZ (dJ_ne_zero Γ)).subset
      (Function.support_mul_subset_right _ _)
  rw [h1, finsum_congr (divK_apply Γ k), finsum_add_distrib hs1 (finite_support_corr Γ k), ← mul_finsum,
    ← UncondValence.degree_divisor_eq_finsum (dJ_ne_zero Γ), hC.out _ (dJ_ne_zero Γ),
    finsum_compactifiedQuotient (corr Γ k) (finite_support_corr Γ k)]
  have he : ∑ᶠ p, corr Γ k (Subgroup.CompactifiedQuotient.ofQuotient p) = ellipticTerm Γ k := by
    rw [ellipticTerm_eq, finsum_eq_sum_elliptic Γ]
    · rfl
    · intro p hp
      simp [corr, stabOrder_out_eq_one Γ hp]
  have hc : ∑ᶠ C, corr Γ k (Subgroup.CompactifiedQuotient.ofCusp C) = k * cuspCount Γ := by
    have := Fintype.ofFinite (Γ.map sl2zToPSL2R).CuspOrbit
    simp only [corr]
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, cuspCount_eq, Nat.card_eq_fintype_card,
      nsmul_eq_mul, mul_comm]
  rw [he, hc]
  ring

/-- $\lfloor k(1 - 1/e)\rfloor \ge (k-1)(1 - 1/e)$ for integers $e \ge 1$. -/
theorem floor_ge (k e : ℕ) (he : 0 < e) :
    ((k : ℚ) - 1) * (1 - 1 / (e : ℚ)) ≤ ⌊(k : ℚ) * (1 - 1 / (e : ℚ))⌋ := by
  have heq : (0 : ℚ) < e := by exact_mod_cast he
  set x := (k : ℚ) * (1 - 1 / (e : ℚ))
  have hx : (e : ℚ) * x = ((k * ((e : ℤ) - 1) : ℤ) : ℚ) := by
    simp only [x]; push_cast; field_simp
  have h1 : x - 1 < ⌊x⌋ := Int.sub_one_lt_floor x
  have h2 : ((k * ((e : ℤ) - 1) - e : ℤ) : ℚ) < ((e * ⌊x⌋ : ℤ) : ℚ) := by
    push_cast
    have := mul_lt_mul_of_pos_left h1 heq
    push_cast at hx
    nlinarith
  have h3 : k * ((e : ℤ) - 1) - e + 1 ≤ e * ⌊x⌋ := by
    have := (Int.cast_lt (R := ℚ)).1 h2
    omega
  have h4 : ((k * ((e : ℤ) - 1) - e + 1 : ℤ) : ℚ) ≤ ((e * ⌊x⌋ : ℤ) : ℚ) := by exact_mod_cast h3
  push_cast at h4
  have h5 : ((k : ℚ) - 1) * (1 - 1 / (e : ℚ)) * e = k * (e - 1) - e + 1 := by field_simp; ring
  have h6 : ((k : ℚ) - 1) * (1 - 1 / (e : ℚ)) * e ≤ ⌊x⌋ * e := by rw [h5]; linarith
  exact le_of_mul_le_mul_right h6 heq

/-- The discriminant as a modular form for $\Gamma$, of weight $2 \cdot 6$. -/
def discForm : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * (6 : ℕ)) :=
  ModularForm.restrict (Subgroup.map_le_range _ _) (CuspForm.toModularFormₗ CuspForm.discriminant)

/-- $2g - 2 + \epsilon_\infty + \sum_P (1 - 1/e_P) \ge 0$, from the valence formula for $\Delta$. -/
theorem euler_nonneg_of (hC : CanonicalDegreeStatement (modularCurve Γ))
    (Δf : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * ((6 : ℕ) : ℤ))) (hΔ : ∀ z : ℍ, Δf z ≠ 0) :
    0 ≤ 2 * (RiemannSurface.genus (modularCurve Γ) : ℚ) - 2 + cuspCount Γ +
      ∑ p ∈ (finite_ellipticOrbits Γ).toFinset, (1 - 1 / (stabOrder Γ p.out : ℚ)) := by
  have hmm := isMeromorphicModularForm (k := ((6 : ℕ) : ℤ)) Δf
  have hnz : ∃ z : ℍ, ¬ ((Δf : ℍ → ℂ) ∘ ofComplex) =ᶠ[𝓝[≠] (z : ℂ)] 0 := by
    refine ⟨UpperHalfPlane.I, fun h ↦ hΔ UpperHalfPlane.I ?_⟩
    have := eq_zero_of_eventually (analyticAt_of_mdifferentiable Δf.holo' UpperHalfPlane.I) h
    rw [Function.comp_apply, ofComplex_apply] at this
    exact this
  have hv := (valenceFormula_of_canonicalDegree Γ hC).formula ((6 : ℕ) : ℤ) (Δf : ℍ → ℂ) hmm hnz
  unfold valenceSum at hv
  -- interior orders vanish
  have hint : ∀ p : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ,
      ((((_root_.meromorphicOrderAt ((Δf : ℍ → ℂ) ∘ ofComplex) (p.out : ℂ)).untopD 0 : ℤ) : ℚ) /
        stabOrder Γ p.out - ((6 : ℕ) : ℤ) * (1 - 1 / (stabOrder Γ p.out : ℚ))) =
        -6 * (1 - 1 / (stabOrder Γ p.out : ℚ)) := by
    intro p
    have ha : AnalyticAt ℂ ((Δf : ℍ → ℂ) ∘ ofComplex) (p.out : ℂ) := analyticAt_of_mdifferentiable Δf.holo' p.out
    have h0 : _root_.meromorphicOrderAt ((Δf : ℍ → ℂ) ∘ ofComplex) (p.out : ℂ) = 0 := by
      rw [ha.meromorphicOrderAt_eq]
      have : analyticOrderAt ((Δf : ℍ → ℂ) ∘ ofComplex) (p.out : ℂ) = 0 :=
        ha.analyticOrderAt_eq_zero.2 (by simpa [ofComplex_apply] using hΔ p.out)
      simp [this]
    rw [h0]
    simp
  have hcusp : 0 ≤ ∑ᶠ c : CuspOrbits (Γ : Subgroup (GL (Fin 2) ℝ)),
      (((cuspOrder Γ ((6 : ℕ) : ℤ) Δf (cuspRep Γ c)).untopD 0 : ℤ) : ℚ) := by
    refine finsum_nonneg fun c ↦ ?_
    have := cuspOrder_nonneg Δf (cuspRep Γ c)
    cases h : cuspOrder Γ ((6 : ℕ) : ℤ) Δf (cuspRep Γ c) with
    | top => simp
    | coe a =>
      rw [h] at this
      simp only [WithTop.untopD_coe]
      exact_mod_cast WithTop.coe_nonneg.1 this
  rw [finsum_congr hint, finsum_eq_sum_elliptic Γ] at hv
  · rw [← Finset.mul_sum, genus_eq_riemannSurface_genus] at hv
    push_cast at hv hcusp
    linarith
  · intro p hp
    simp [stabOrder_out_eq_one Γ hp]

theorem euler_nonneg (hC : CanonicalDegreeStatement (modularCurve Γ)) :
    0 ≤ 2 * (RiemannSurface.genus (modularCurve Γ) : ℚ) - 2 + cuspCount Γ +
      ∑ p ∈ (finite_ellipticOrbits Γ).toFinset, (1 - 1 / (stabOrder Γ p.out : ℚ)) :=
  euler_nonneg_of Γ hC (discForm Γ) fun z ↦ ModularForm.discriminant_ne_zero z

/-- $\deg D_k > 2g - 2$ for $k \ge 1$. -/
theorem degree_divK_gt (hC : CanonicalDegreeStatement (modularCurve Γ)) {k : ℕ} (hk : 1 ≤ k) :
    2 * (RiemannSurface.genus (modularCurve Γ) : ℤ) - 2 < WeilDivisor.degree (divK Γ k) := by
  rw [degree_divK Γ hC k, ellipticTerm_eq]
  have hE := euler_nonneg Γ hC
  have hfl : ∑ p ∈ (finite_ellipticOrbits Γ).toFinset, ((k : ℚ) - 1) * (1 - 1 / (stabOrder Γ p.out : ℚ)) ≤
      ∑ p ∈ (finite_ellipticOrbits Γ).toFinset, ((⌊(k : ℚ) * (1 - 1 / (stabOrder Γ p.out : ℚ))⌋ : ℤ) : ℚ) :=
    Finset.sum_le_sum fun p _ ↦ floor_ge k _ (Nat.pos_of_ne_zero (stabOrder_ne_zero p.out))
  rw [← Finset.mul_sum] at hfl
  have hcp : (1 : ℚ) ≤ cuspCount Γ := by exact_mod_cast cuspCount_pos Γ
  have hk' : (0 : ℚ) ≤ (k : ℚ) - 1 := by
    have : (1 : ℚ) ≤ k := by exact_mod_cast hk
    linarith
  have key : (2 * (RiemannSurface.genus (modularCurve Γ) : ℚ) - 2) <
      k * (2 * (RiemannSurface.genus (modularCurve Γ) : ℚ) - 2) +
        ∑ p ∈ (finite_ellipticOrbits Γ).toFinset, ((⌊(k : ℚ) * (1 - 1 / (stabOrder Γ p.out : ℚ))⌋ : ℤ) : ℚ) +
          k * cuspCount Γ := by
    nlinarith [mul_nonneg hk' hE]
  exact_mod_cast key

end Degree

end UncondDim

open UncondDim in
/-- **Theorem 4.9** (the dimension formula), from Riemann–Roch on $X(\Gamma)$: for every subgroup $\Gamma$ of finite
index in $\mathrm{SL}_2(\mathbb Z)$, `RiemannRochStatement (modularCurve Γ)` (Theorem 1.20) and
`CanonicalDegreeStatement (modularCurve Γ)` (Corollary 1.21 with the genus) imply `DimensionFormula Γ`. Lemma 4.11
is used unconditionally (`UncondDim.equivRRSpace`: $M_{2k}(\Gamma) \cong L(D_k)$). -/
@[kb "milne2017mf" "Section 4, Theorem 4.9 (pdf p. 51)"]
theorem dimensionFormula_of_riemannRoch (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hRR : RiemannSurface.RiemannRochStatement (modularCurve Γ))
    (hC : CanonicalDegreeStatement (modularCurve Γ)) : DimensionFormula Γ where
  formula k hk := by
    obtain ⟨g₀, hg₀⟩ := hRR.exists_genus
    have hK := (RiemannSurface.degree_canonical_and_ell_canonical hg₀ (dJ_ne_zero Γ)).1
    have hg : (g₀ : ℤ) = RiemannSurface.genus (modularCurve Γ) := by
      have := hC.out _ (dJ_ne_zero Γ)
      omega
    have hell := RiemannSurface.ell_eq_of_degree_gt hg₀ ⟨dJ Γ, dJ_ne_zero Γ⟩ (D := divK Γ k)
      (by rw [hg]; exact degree_divK_gt Γ hC hk)
    have hw : ((2 * k : ℕ) : ℤ) = 2 * (k : ℤ) := by push_cast; ring
    rw [hw, finrank_eq_ell, hell, degree_divK Γ hC, hg, genus_eq_riemannSurface_genus]
    ring

end ModularFormsKB.Milne
