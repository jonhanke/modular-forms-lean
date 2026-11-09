import ModularFormsKB.Milne.Ch6.X0Functions
import ModularFormsKB.Milne.Ch2.ModularCurves
import TauCeti.Analysis.Complex.ModularForms.CongruenceSubgroups.Degree
import TauCeti.Analysis.Complex.Fuchsian.Compactification.FiniteHolomorphicMap
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Degree
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# $[\mathbb C(X_0(N)) : \mathbb C(j)] \le \psi$, and generation by $j$ and $j_N$

Milne, Section 6, proof of Theorem 6.1 (pdf p. 88). The function $j$ on $X_0(N)$ is the composite
$X_0(N) \to X(1) \xrightarrow{\ \sim\ } \mathbb P^1$ (`jXMap`), of degree $\psi = (\Gamma(1) : \Gamma_0(N))$ (Tau Ceti's
`CongruenceSubgroup.degree_compactifiedQuotientMap_Gamma0` and `TauCeti.RiemannSurface.degree_comp`). By Tau Ceti's
`exists_monic_natDegree_eq_degree_eval₂_eq_zero`, every meromorphic function on $X_0(N)$ is a root of a monic polynomial
of degree $\psi$ over $\mathbb C(j)$ (`natDegree_minpoly_le`). Hence if some $f_0$ has degree exactly $\psi$ over
$\mathbb C(j)$, then $\mathbb C(j, f_0) = \mathbb C(X_0(N))$ (primitive element theorem; `adjoin_eq_top`).
-/

open UpperHalfPlane CongruenceSubgroup Polynomial
open scoped MatrixGroups Manifold

noncomputable section

namespace ModularFormsKB.Milne

open TauCeti.RiemannSurface Subgroup.CompactifiedQuotient TauCeti.RiemannSurface.MeromorphicFunction

variable (N : ℕ) [NeZero N]

instance : CompactSpace (X0 N) := compactSpace_compactifiedQuotient_map_sl2zToPSL2R _

/-- $j : X_0(N) \to \mathbb P^1$ as a finite holomorphic map. -/
def jXMap : FiniteHolomorphicMap (X0 N) (OnePoint ℂ) :=
  TauCeti.ModularGroup.jFiniteHolomorphicMap.comp
    (TauCeti.Fuchsian.compactifiedQuotientFiniteHolomorphicMap (Gamma0_map_le_range N))

theorem coe_jXMap : ⇑(jXMap N) = ⇑(jX N) := by
  funext x
  simp [jXMap, jX, jXFun, TauCeti.ModularGroup.coe_jFiniteHolomorphicMap,
    TauCeti.ModularGroup.coe_jBiholomorph]

theorem degree_jXMap : degree (jXMap N) = (Gamma0 N).index := by
  unfold jXMap
  rw [TauCeti.RiemannSurface.degree_comp, TauCeti.ModularGroup.coe_jFiniteHolomorphicMap,
    TauCeti.ModularGroup.degree_jSphere, one_mul]
  exact CongruenceSubgroup.degree_compactifiedQuotientMap_Gamma0 N

/-- $j$ is transcendental over $\mathbb C$ in $\mathbb C(X_0(N))$. -/
theorem transcendental_jX : Transcendental ℂ (jX N) := by
  intro halg
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible halg.isIntegral)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one ℂ (jX N) hdeg
  have h1 := isJOnX0_jX N UpperHalfPlane.ρ
  have h2 := isJOnX0_jX N UpperHalfPlane.I
  rw [← hc, MeromorphicFunction.coe_algebraMap] at h1 h2
  rw [TauCeti.ModularForm.j_ρ] at h1
  rw [TauCeti.ModularForm.j_I] at h2
  have := h1.symm.trans h2
  norm_num [OnePoint.coe_eq_coe] at this

omit [NeZero N] in
/-- Algebra homomorphisms out of `ℂ(t)` are determined by the image of `t`. -/
theorem ratFunc_algHom_ext {M : Type*} [Field M] [Algebra ℂ M] (φ ψ : RatFunc ℂ →ₐ[ℂ] M)
    (h : φ RatFunc.X = ψ RatFunc.X) : φ = ψ := by
  have key : ∀ (χ : RatFunc ℂ →ₐ[ℂ] M) (p : ℂ[X]),
      χ (algebraMap ℂ[X] (RatFunc ℂ) p) = aeval (χ RatFunc.X) p := by
    intro χ p
    have hp : algebraMap ℂ[X] (RatFunc ℂ) p = aeval RatFunc.X p := by
      rw [← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
    rw [hp, Polynomial.aeval_algHom_apply]
  apply AlgHom.toRingHom_injective
  apply IsFractionRing.ringHom_ext (A := ℂ[X])
  intro p
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, key, h]

/-- Pulling back a rational function along $j$ lands in $\mathbb C(j)$. -/
theorem comap_jXMap_mem (g : MeromorphicFunction (OnePoint ℂ)) :
    comap (jXMap N) (jXMap N).holomorphic (jXMap N).nonconstant g ∈
      IntermediateField.adjoin ℂ {jX N} := by
  set K := IntermediateField.adjoin ℂ {jX N}
  let e := RatFunc.algEquivOfTranscendental (jX N) (transcendental_jX N)
  have hext : (comapₐ (jXMap N) (jXMap N).holomorphic (jXMap N).nonconstant).comp
      (ratFuncEquiv : RatFunc ℂ ≃ₐ[ℂ] MeromorphicFunction (OnePoint ℂ)).toAlgHom =
      K.val.comp e.toAlgHom := by
    apply ratFunc_algHom_ext
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, ratFuncEquiv_X,
      RatFunc.algEquivOfTranscendental_X, e]
    refine DFunLike.ext _ _ fun x ↦ ?_
    simp [comapₐ_apply, coe_jXMap]
  have := DFunLike.congr_fun hext (ratFuncEquiv.symm g)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply] at this
  rw [← comapₐ_apply, this]
  exact (e _).2

/-- **Every meromorphic function on $X_0(N)$ has degree at most $\psi$ over $\mathbb C(j)$.** -/
theorem natDegree_minpoly_le (f : MeromorphicFunction (X0 N)) :
    IsIntegral (IntermediateField.adjoin ℂ {jX N}) f ∧
      (minpoly (IntermediateField.adjoin ℂ {jX N}) f).natDegree ≤ (Gamma0 N).index := by
  set K := IntermediateField.adjoin ℂ {jX N}
  obtain ⟨p, hp, hdeg, hpf⟩ := exists_monic_natDegree_eq_degree_eval₂_eq_zero (jXMap N) f
  let φ : MeromorphicFunction (OnePoint ℂ) →+* K :=
    RingHom.codRestrict (comapₐ (jXMap N) (jXMap N).holomorphic (jXMap N).nonconstant).toRingHom K
      (comap_jXMap_mem N)
  have hq : (p.map φ).Monic := hp.map _
  have hqdeg : (p.map φ).natDegree = (Gamma0 N).index := by
    rw [hp.natDegree_map, hdeg, degree_jXMap]
  have hroot : aeval f (p.map φ) = 0 := by
    rw [aeval_def, eval₂_map]
    exact hpf
  have hint : IsIntegral K f := ⟨_, hq, hroot⟩
  refine ⟨hint, ?_⟩
  rw [← hqdeg]
  exact natDegree_le_natDegree (minpoly.min K f hq hroot)

/-- **Generation.** If $f_0$ has degree $\psi$ over $\mathbb C(j)$, then $\mathbb C(j, f_0) = \mathbb C(X_0(N))$. -/
theorem adjoin_eq_top (f₀ : MeromorphicFunction (X0 N))
    (h : (minpoly (IntermediateField.adjoin ℂ {jX N}) f₀).natDegree = (Gamma0 N).index) :
    IntermediateField.adjoin ℂ {jX N, f₀} = ⊤ := by
  set K := IntermediateField.adjoin ℂ {jX N}
  set E := IntermediateField.adjoin ℂ {jX N, f₀}
  rw [eq_top_iff]
  intro f _
  have hKE : K ≤ E := IntermediateField.adjoin.mono ℂ _ _ (by simp)
  let L : IntermediateField K (MeromorphicFunction (X0 N)) := IntermediateField.adjoin K {f₀}
  let M : IntermediateField K (MeromorphicFunction (X0 N)) := IntermediateField.adjoin K {f₀, f}
  have hint : ∀ x ∈ ({f₀, f} : Set (MeromorphicFunction (X0 N))), IsIntegral K x := by
    intro x hx
    rcases hx with rfl | rfl
    · exact (natDegree_minpoly_le N _).1
    · exact (natDegree_minpoly_le N _).1
  have : FiniteDimensional K M := IntermediateField.finiteDimensional_adjoin hint
  have hLM : L ≤ M := IntermediateField.adjoin.mono K _ _ (by simp)
  have hL : Module.finrank K L = (Gamma0 N).index := by
    rw [IntermediateField.adjoin.finrank (natDegree_minpoly_le N f₀).1, h]
  have hM : Module.finrank K M ≤ (Gamma0 N).index := by
    have hchar : CharZero K := charZero_of_injective_algebraMap (algebraMap ℂ K).injective
    have hI : Algebra.IsIntegral K M := Algebra.IsIntegral.of_finite K M
    have hS : Algebra.IsSeparable K M := Algebra.IsSeparable.of_integral K M
    obtain ⟨α, hα⟩ := Field.exists_primitive_element K M
    have hαint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
    have h1 : Module.finrank K M = (minpoly K α).natDegree := by
      rw [← IntermediateField.adjoin.finrank hαint, hα, IntermediateField.finrank_top']
    rw [h1]
    have h2 : minpoly K α = minpoly K (α : MeromorphicFunction (X0 N)) :=
      (minpoly.algebraMap_eq (A := K) (B := M) (B' := MeromorphicFunction (X0 N))
        (algebraMap M _).injective α).symm
    rw [h2]
    exact (natDegree_minpoly_le N _).2
  have hLM' : L = M := IntermediateField.eq_of_le_of_finrank_le hLM (hL ▸ hM)
  have hfM : f ∈ M := IntermediateField.subset_adjoin K _ (by simp)
  rw [← hLM'] at hfM
  let T : IntermediateField K (MeromorphicFunction (X0 N)) :=
    { E.toSubfield with algebraMap_mem' := fun k ↦ hKE k.2 }
  have hLE : L ≤ T := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact IntermediateField.subset_adjoin ℂ _ (by simp)
  exact hLE hfM

end ModularFormsKB.Milne
