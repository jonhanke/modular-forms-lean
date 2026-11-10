import ModularFormsKB.Milne.Ch4.UncondDimension
import ModularFormsKB.Milne.RS.CanonicalGenus
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule

/-!
# Milne, Lemma 11.10: cusp forms of weight 2 and holomorphic differentials

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 11, Lemma 11.10
(pdf p. 114).

**Lemma 11.10.** There is a natural one-to-one correspondence between the cusp forms of weight $2$ for
$\Gamma_0(N)$ and the holomorphic differential forms on $X_0(N)$.

Milne's proof: $f \mapsto f\,dz$ identifies meromorphic modular forms of weight 2 with meromorphic differentials on
$X_0(N)$ (Remark 4.8), and Lemma 4.11 shows that the cusp forms correspond to the holomorphic differentials. The proof
works for every subgroup $\Gamma$ of finite index in $\mathrm{SL}_2(\mathbb Z)$, and we prove it in that generality
(`cuspFormWeightTwoEquiv`), then specialize to $\Gamma_0(N)$ (`cuspFormGammaZeroEquiv`).

## Construction
The space $M_2(\Gamma)$ is identified with the Riemann–Roch space $L(D_1)$ on $X(\Gamma)$,
$D_1 = \operatorname{div}(dJ) + \sum_{\text{cusps}} Q$ (`UncondDim.equivRRSpace`, $f \mapsto F = f/j'$, so that
$f\,dz = F\,dJ$; the elliptic correction $\lfloor 1 - 1/e_P\rfloor$ vanishes in weight 2). By Lemma 4.11 (b) the
order of $f$ at a cusp $Q$ is $\mathrm{ord}_Q(F\,dJ) + 1$, so $f$ is a cusp form exactly when $F\,dJ$ is holomorphic
at the cusps, i.e. when $F \in L(\operatorname{div}(dJ))$ (`toRR_mem_iff`). Finally multiplication by $dJ$ is an
isomorphism $L(\operatorname{div}(dJ)) \cong \Omega^1(X(\Gamma))$ (`RS.rrSpaceEquivHolomorphicDifferentials`).
The composite sends $f$ to the holomorphic differential $F\,dJ$, whose pullback to $\mathbb H$ is $f(z)\,dz$.

## Main results
* `cuspFormWeightTwoEquiv`: $S_2(\Gamma) \cong \Omega^1(X(\Gamma))$ for $\Gamma$ of finite index.
* `cuspFormGammaZeroEquiv`: **Lemma 11.10**, $S_2(\Gamma_0(N)) \cong \Omega^1(X_0(N))$.
* `finrank_cuspForm_weight_two`: $\dim S_2(\Gamma) = g(X(\Gamma))$.
* `isCuspForm_iff_one_le_cuspOrder`: a modular form of weight 2 is a cusp form iff its order at every cusp is
  at least $1$.
-/

namespace ModularFormsKB.Milne.Wave4B

open Filter Topology in
/-- For $g$ analytic at $0$, the order of $g$ at $0$ is at least $1$ iff $g(0) = 0$. -/
theorem one_le_meromorphicOrderAt_iff {g : ℂ → ℂ} (ha : AnalyticAt ℂ g 0) :
    1 ≤ meromorphicOrderAt g 0 ↔ g 0 = 0 := by
  have h1 : 1 ≤ meromorphicOrderAt g 0 ↔ 0 < meromorphicOrderAt g 0 := by
    induction meromorphicOrderAt g 0 using WithTop.recTopCoe with
    | top => simp
    | coe a => norm_cast
  have h2 := tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt
  rw [h1, ← h2]
  constructor
  · intro h
    exact tendsto_nhds_unique (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) h
  · intro h
    have := ha.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
    rwa [h] at this

end ModularFormsKB.Milne.Wave4B

open UpperHalfPlane Complex Filter Topology ModularForm MulAction
open scoped MatrixGroups Manifold Real ContDiff

noncomputable section

namespace ModularFormsKB.Milne.Wave4B

open TauCeti.RiemannSurface MeromorphicFunction UncondDiff UncondValence UncondDim

section CuspOrder

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}

/-- For a modular form $f$ of weight $2k$, the order of $f$ at the cusp $\gamma(i\infty)$ is at least $1$ exactly when
$f|_{2k}\gamma$ vanishes at $i\infty$. -/
theorem one_le_cuspOrder_iff (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * k)) (γ : SL(2, ℤ)) :
    1 ≤ cuspOrder Γ k f γ ↔ IsZeroAtImInfty ((f : ℍ → ℂ) ∣[2 * k] γ) := by
  obtain ⟨n, hn, hw⟩ := exists_nat_cuspWidth Γ γ
  have hpos : 0 < cuspWidth Γ γ := by rw [hw]; exact_mod_cast hn
  have ha := analyticAt_cuspFunction f γ
  have hper := periodic_slash (fun δ hδ ↦ slash_eq_of_mem f hδ) γ
  have hord := one_le_meromorphicOrderAt_iff ha
  unfold cuspOrder
  rw [hord]
  constructor
  · intro h0
    change Tendsto _ atImInfty (𝓝 0)
    have ht := ha.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty hpos)
    rw [h0] at ht
    refine ht.congr fun τ ↦ ?_
    exact UpperHalfPlane.eq_cuspFunction τ hpos.ne' hper
  · intro hz
    exact hz.cuspFunction_apply_zero hpos

/-- `γ(i∞)` is a cusp of every finite-index subgroup. -/
theorem isCusp_smul_infty (γ : SL(2, ℤ)) :
    IsCusp (Matrix.SpecialLinearGroup.mapGL ℝ γ • (OnePoint.infty : OnePoint ℝ)) (Γ : Subgroup (GL (Fin 2) ℝ)) := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff']
  exact ⟨γ, rfl⟩

/-- **A modular form is a cusp form iff it has order at least $1$ at every cusp** (Milne, p. 49: $f$ is a cusp form
when it vanishes at the cusps). -/
theorem isCuspForm_iff_one_le_cuspOrder (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * k)) :
    IsCuspForm f ↔ ∀ γ : SL(2, ℤ), 1 ≤ cuspOrder Γ k f γ := by
  rw [isCuspForm_iff]
  constructor
  · intro h γ
    have hc := isCusp_smul_infty (Γ := Γ) γ
    have hz := h hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z (by rw [isCusp_SL2Z_iff']; exact ⟨γ, rfl⟩)] at hz
    exact (one_le_cuspOrder_iff f γ).2 (hz γ rfl)
  · intro h c hc
    have hc' : IsCusp c 𝒮ℒ := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).1 hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc']
    intro γ _
    exact (one_le_cuspOrder_iff f γ).1 (h γ)

end CuspOrder

section Divisor

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- In weight 2 the elliptic correction vanishes: $D_1(P) = \mathrm{ord}_P(dJ)$ at $P \in \Gamma\backslash\mathbb H$. -/
theorem divK_one_proj (z : ℍ) : divK Γ 1 (modularCurve.proj Γ z) = (dJ Γ).ordZ (modularCurve.proj Γ z) := by
  rw [divK_apply, corr_proj]
  have he : (1 : ℚ) ≤ stabOrder Γ z := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (stabOrder_ne_zero z)
  have hfl : ⌊((1 : ℕ) : ℚ) * (1 - 1 / (stabOrder Γ z : ℚ))⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    have h0 : (0 : ℚ) < stabOrder Γ z := by linarith
    have h1 : 0 < 1 / (stabOrder Γ z : ℚ) := by positivity
    have h2 : 1 / (stabOrder Γ z : ℚ) ≤ 1 := by rw [div_le_one h0]; exact he
    push_cast
    constructor <;> linarith
  rw [hfl]
  simp

/-- At a cusp, $D_1(Q) = \mathrm{ord}_Q(dJ) + 1$. -/
theorem divK_one_cusp (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    divK Γ 1 (Subgroup.CompactifiedQuotient.ofCusp C) =
      (dJ Γ).ordZ (Subgroup.CompactifiedQuotient.ofCusp C) + 1 := by
  rw [divK_apply]
  simp [corr]

/-- $\operatorname{div}(dJ) \le D_1$ pointwise. -/
theorem divisor_dJ_le_divK_one (x : modularCurve Γ) : (dJ Γ).divisor x ≤ divK Γ 1 x := by
  rw [RS.divisor_apply (dJ_ne_zero Γ)]
  cases x with
  | ofQuotient p =>
    have := divK_one_proj Γ p.out
    rw [proj_out] at this
    rw [this]
  | ofCusp C =>
    rw [divK_one_cusp]
    omega

/-- $L(\operatorname{div}(dJ)) \subseteq L(D_1)$. -/
theorem rrSpace_dJ_le : RiemannSurface.rrSpace (modularCurve Γ) (dJ Γ).divisor ≤
    RiemannSurface.rrSpace (modularCurve Γ) (divK Γ 1) := by
  intro Φ hΦ x
  refine le_trans ?_ (hΦ x)
  exact_mod_cast neg_le_neg (divisor_dJ_le_divK_one Γ x)

end Divisor

section Membership

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

/-- **Lemma 4.11 (b) in weight 2**: for $f \in M_2(\Gamma)$ with $F = f/j'$, the order of $f$ at the cusp
$\gamma(i\infty)$ is at least $1$ iff $\mathrm{ord}_Q(F) \ge -\mathrm{ord}_Q(dJ)$. -/
theorem one_le_cuspOrder_iff_order (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * ((1 : ℕ) : ℤ)))
    (γ : SL(2, ℤ)) :
    1 ≤ cuspOrder Γ ((1 : ℕ) : ℤ) f γ ↔
      ((-((dJ Γ).ordZ (Subgroup.CompactifiedQuotient.ofCusp (Γ.cuspOrbitOfSL2Z γ))) : ℤ) : WithTop ℤ) ≤
        TauCeti.RiemannSurface.meromorphicOrderAt (Fc f) (Subgroup.CompactifiedQuotient.ofCusp (Γ.cuspOrbitOfSL2Z γ)) := by
  rw [order_cusp_gen (isMeromorphicModularForm f) (Fc_meromorphic f) (Jc_meromorphic Γ) (Fc_spec f) (Jc_spec Γ) γ,
    order_kDiff, show (dOf (Jc Γ) (Jc_meromorphic Γ)) = dJ Γ from rfl, dJ_ord_eq]
  generalize TauCeti.RiemannSurface.meromorphicOrderAt (Fc f)
    (Subgroup.CompactifiedQuotient.ofCusp (Γ.cuspOrbitOfSL2Z γ)) = A
  generalize (dJ Γ).ordZ (Subgroup.CompactifiedQuotient.ofCusp (Γ.cuspOrbitOfSL2Z γ)) = b
  cases A with
  | top => simp
  | coe a =>
    have hc : (a : WithTop ℤ) + (((1 : ℕ) : ℤ) : WithTop ℤ) * (b : WithTop ℤ) + (((1 : ℕ) : ℤ) : WithTop ℤ) =
        ((a + b + 1 : ℤ) : WithTop ℤ) := by push_cast; norm_cast; ring_nf
    rw [hc]
    norm_cast
    omega

/-- **The cusp forms are the forms with $F = f/j' \in L(\operatorname{div}(dJ))$.** -/
theorem toRR_mem_iff (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * ((1 : ℕ) : ℤ))) :
    (toRR Γ 1 f : MeromorphicFunction (modularCurve Γ)) ∈
        RiemannSurface.rrSpace (modularCurve Γ) (dJ Γ).divisor ↔ IsCuspForm f := by
  rw [isCuspForm_iff_one_le_cuspOrder]
  change (∀ x, _) ↔ _
  simp only [coe_toRR, order_ofMeromorphic, RS.divisor_apply (dJ_ne_zero Γ)]
  constructor
  · intro h γ
    exact (one_le_cuspOrder_iff_order f γ).2 (h _)
  · intro h x
    cases x with
    | ofQuotient p =>
      have h1 := (toRR Γ 1 f).2 (Subgroup.CompactifiedQuotient.ofQuotient p)
      rw [coe_toRR, order_ofMeromorphic, ← proj_out, divK_one_proj] at h1
      rw [← proj_out]
      exact h1
    | ofCusp C =>
      obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
      exact (one_le_cuspOrder_iff_order f γ).1 (h γ)

end Membership

section Equiv

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- The map $S_2(\Gamma) \to L(\operatorname{div}(dJ))$, $f \mapsto f/j'$. -/
def cuspToRR : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * ((1 : ℕ) : ℤ)) →ₗ[ℂ]
    RiemannSurface.rrSpace (modularCurve Γ) (dJ Γ).divisor :=
  LinearMap.codRestrict _ ((RiemannSurface.rrSpace (modularCurve Γ) (divK Γ 1)).subtype ∘ₗ toRR Γ 1 ∘ₗ
    CuspForm.toModularFormₗ) fun f ↦ (toRR_mem_iff _).2 (CuspForm.isCuspForm_toModularFormₗ f)

theorem cuspToRR_injective : Function.Injective (cuspToRR Γ) := by
  intro f g h
  have h' := congrArg Subtype.val h
  change ((toRR Γ 1 (CuspForm.toModularFormₗ f) : RiemannSurface.rrSpace (modularCurve Γ) (divK Γ 1)) :
    MeromorphicFunction (modularCurve Γ)) = (toRR Γ 1 (CuspForm.toModularFormₗ g) : _) at h'
  exact CuspForm.toModularFormₗ_injective (toRR_injective (Subtype.ext h'))

theorem cuspToRR_surjective : Function.Surjective (cuspToRR Γ) := by
  rintro ⟨Φ, hΦ⟩
  have hmem := rrSpace_dJ_le Γ hΦ
  set g := ofRR 1 ⟨Φ, hmem⟩
  have hg : toRR Γ 1 g = ⟨Φ, hmem⟩ := toRR_ofRR _
  have hcusp : IsCuspForm g := by
    rw [← toRR_mem_iff, hg]
    exact hΦ
  obtain ⟨h, hh⟩ := hcusp
  refine ⟨h, Subtype.ext ?_⟩
  change ((toRR Γ 1 (CuspForm.toModularFormₗ h) : RiemannSurface.rrSpace (modularCurve Γ) (divK Γ 1)) :
    MeromorphicFunction (modularCurve Γ)) = Φ
  rw [hh, hg]

/-- **$S_2(\Gamma) \cong \Omega^1(X(\Gamma))$** for every subgroup $\Gamma$ of finite index in
$\mathrm{SL}_2(\mathbb Z)$: $f \mapsto F\,dJ$ with $F = f/j'$, the holomorphic differential whose pullback to
$\mathbb H$ is $f(z)\,dz$ (Milne, Lemma 11.10 and its proof, for general $\Gamma$). -/
@[kb "milne2017mf" "Section 11, Lemma 11.10 (pdf p. 114), for every subgroup of finite index"]
def cuspFormWeightTwoEquiv :
    CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2 ≃ₗ[ℂ] RiemannSurface.holomorphicDifferentials (modularCurve Γ) :=
  (LinearEquiv.ofBijective (cuspToRR Γ) ⟨cuspToRR_injective Γ, cuspToRR_surjective Γ⟩).trans
    (RS.rrSpaceEquivHolomorphicDifferentials (dJ_ne_zero Γ))

/-- **Lemma 11.10** (Milne, p. 114): the cusp forms of weight $2$ for $\Gamma_0(N)$ correspond one-to-one (as a
complex linear isomorphism) to the holomorphic differential forms on $X_0(N)$. -/
@[kb "milne2017mf" "Section 11, Lemma 11.10 (pdf p. 114)"]
def cuspFormGammaZeroEquiv (N : ℕ) [NeZero N] :
    CuspForm ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 2 ≃ₗ[ℂ]
      RiemannSurface.holomorphicDifferentials (modularCurve (CongruenceSubgroup.Gamma0 N)) :=
  cuspFormWeightTwoEquiv (CongruenceSubgroup.Gamma0 N)

/-- $\dim S_2(\Gamma) = g(X(\Gamma))$, the genus of the modular curve. -/
@[kb "milne2017mf" "Section 11, Lemma 11.10 (pdf p. 114): dim S_2 = genus"]
theorem finrank_cuspForm_weight_two :
    Module.finrank ℂ (CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2) = genus (modularCurve Γ) :=
  (cuspFormWeightTwoEquiv Γ).finrank_eq

end Equiv

end ModularFormsKB.Milne.Wave4B
