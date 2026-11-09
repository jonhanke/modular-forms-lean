import ModularFormsKB.Milne.Ch7.Curves
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.EssentialFiniteness

/-!
# Milne, Theorem 7.2 fails over imperfect fields

Milne's varieties are *geometrically reduced*: an affine $k_0$-algebra $A$ has $k \otimes_{k_0} A$ reduced
(`IsAffineAlgebra`). The function field $k_0(X)$ of such a curve is therefore separable over $k_0$, and a function field
in one variable that is not separable over $k_0$ is not $k_0(X)$ for any curve $X$ in Milne's sense. So the essential
surjectivity in Theorem 7.2 (`CurveFunctionFieldEquivalence.essSurj`) is false when $k_0$ is not perfect.

**Counterexample.** $k_0 = \mathbb F_2(a)$ (`RatFunc (ZMod 2)`), $L = k_0(\sqrt a)$ (`AdjoinRoot (X^2 - a)`), and
$K = L(t)$ (`RatFunc L`), a function field in one variable over $k_0$. If $K \cong k_0(X)$, choose a nonempty open
$U \cong \operatorname{Spec} A$ of the prevariety $X$ with $A$ an affine $k_0$-algebra. Then $\sqrt a = p/q$ with
$p, q \in A$, $q \neq 0$, so $p^2 = a q^2$, and in $\bar k \otimes A$ (characteristic $2$, $\alpha^2 = a$)
$(1 \otimes p - \alpha \otimes q)^2 = 0$. Since $\bar k \otimes A$ is reduced, $1 \otimes p = \alpha \otimes q$; applying
a $k_0$-linear form $\varphi$ on $\bar k$ with $\varphi(1) = 0$, $\varphi(\alpha) = 1$ gives $q = 0$, a contradiction.

The corrected statement assumes $k_0$ perfect (`CurveFunctionFieldEquivalencePerfect`); see
`docs/updates-and-errata.md`.
-/

open AlgebraicGeometry CategoryTheory Polynomial

noncomputable section

namespace ModularFormsKB.Milne.Ch7Counterexample

open scoped TensorProduct

section Algebraic

variable {k₀ : Type*} [Field k₀] [CharP k₀ 2] {A : Type*} [CommRing A] [Algebra k₀ A]

omit [CharP k₀ 2] in
/-- A $k_0$-linear form $\varphi$ on $\bar k$ with $\varphi(1) = 0$ and $\varphi(\alpha) = 1$, for $\alpha \notin k_0$. -/
theorem exists_form {E : Type*} [Field E] [Algebra k₀ E] (α : E) (hα : α ∉ Set.range (algebraMap k₀ E)) :
    ∃ φ : E →ₗ[k₀] k₀, φ 1 = 0 ∧ φ α = 1 := by
  have hli : LinearIndependent k₀ ![(1 : E), α] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hα
      refine ⟨-s / t, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have ht' : algebraMap k₀ E t ≠ 0 := by simpa using ht
      rw [map_div₀, map_neg, div_eq_iff ht']
      linear_combination -hst
  let φ₀ : Submodule.span k₀ (Set.range ![(1 : E), α]) →ₗ[k₀] k₀ :=
    (Finsupp.lapply 1).comp hli.repr
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend φ₀
  have h1 : (1 : E) ∈ Submodule.span k₀ (Set.range ![(1 : E), α]) :=
    Submodule.subset_span ⟨0, rfl⟩
  have h2 : α ∈ Submodule.span k₀ (Set.range ![(1 : E), α]) :=
    Submodule.subset_span ⟨1, rfl⟩
  refine ⟨φ, ?_, ?_⟩
  · have := LinearMap.congr_fun hφ ⟨1, h1⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
    rw [this]
    simp only [φ₀, LinearMap.coe_comp, Function.comp_apply, Finsupp.lapply_apply]
    have := hli.repr_eq_single 0 ⟨1, h1⟩ rfl
    rw [this]
    simp
  · have := LinearMap.congr_fun hφ ⟨α, h2⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
    rw [this]
    simp only [φ₀, LinearMap.coe_comp, Function.comp_apply, Finsupp.lapply_apply]
    have := hli.repr_eq_single 1 ⟨α, h2⟩ rfl
    rw [this]
    simp

/-- **No geometrically reduced algebra contains a square root of a non-square** (characteristic $2$): if
$\bar k \otimes_{k_0} A$ is reduced and $p^2 = a q^2$ in $A$ with $a \in k_0$ not a square, then $q = 0$. -/
theorem eq_zero_of_sq_eq (hA : IsReduced (TensorProduct k₀ (AlgebraicClosure k₀) A)) {a : k₀}
    (ha : ¬ IsSquare a) {p q : A} (h : p ^ 2 = algebraMap k₀ A a * q ^ 2) : q = 0 := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap k₀ (AlgebraicClosure k₀) a) two_pos
  have hαk : α ∉ Set.range (algebraMap k₀ (AlgebraicClosure k₀)) := by
    rintro ⟨c, rfl⟩
    apply ha
    refine ⟨c, ?_⟩
    apply (algebraMap k₀ (AlgebraicClosure k₀)).injective
    rw [← hα, map_mul, sq]
  obtain ⟨φ, hφ1, hφα⟩ := exists_form α hαk
  set T := TensorProduct k₀ (AlgebraicClosure k₀) A
  have h2 : (2 : T) = 0 := by
    rw [← map_ofNat (algebraMap k₀ T) 2, CharTwo.two_eq_zero, map_zero]
  set x : T := (1 : AlgebraicClosure k₀) ⊗ₜ p - α ⊗ₜ q
  have hx : x ^ 2 = 0 := by
    have e1 : ((1 : AlgebraicClosure k₀) ⊗ₜ[k₀] p) ^ 2 = (1 : AlgebraicClosure k₀) ⊗ₜ (p ^ 2) := by
      rw [sq, sq, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have e2 : (α ⊗ₜ[k₀] q) ^ 2 = (1 : AlgebraicClosure k₀) ⊗ₜ (p ^ 2) := by
      rw [sq, Algebra.TensorProduct.tmul_mul_tmul, ← sq, ← sq, hα, h, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul, Algebra.smul_def]
    calc x ^ 2 = ((1 : AlgebraicClosure k₀) ⊗ₜ[k₀] p) ^ 2 + (α ⊗ₜ[k₀] q) ^ 2
          - 2 * (((1 : AlgebraicClosure k₀) ⊗ₜ[k₀] p) * (α ⊗ₜ[k₀] q)) := by ring
      _ = 2 * ((1 : AlgebraicClosure k₀) ⊗ₜ (p ^ 2) - ((1 : AlgebraicClosure k₀) ⊗ₜ[k₀] p) * (α ⊗ₜ[k₀] q)) := by
          rw [e1, e2]; ring
      _ = 0 := by rw [h2, zero_mul]
  have hx0 : x = 0 := (hA.eq_zero x ⟨2, hx⟩)
  have := congrArg (fun y => TensorProduct.lid k₀ A (LinearMap.rTensor A φ y)) hx0
  simp only [x, map_sub, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hφ1, hφα, zero_smul, one_smul,
    zero_sub, map_zero, neg_eq_zero] at this
  exact this

end Algebraic

section Geometric

universe u

variable {k₀ : Type u} [Field k₀]

/-- **An affine chart of an integral prevariety**: a nonempty open $U \cong \operatorname{Spec} A$, $A$ an affine
$k_0$-algebra, gives an injective $k_0$-algebra map $A \to k_0(X)$ whose image generates $k_0(X)$ as a field of
fractions. -/
theorem exists_affineAlgebra_functionField {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k₀))
    (hf : IsPrevariety k₀ f) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra k₀ A), IsAffineAlgebra k₀ A ∧
      ∃ ψ : A →+* X.functionField, Function.Injective ψ ∧
        (∀ c, ψ (algebraMap k₀ A c) = functionFieldAlgebraMap k₀ f c) ∧
        ∀ z : X.functionField, ∃ p q : A, q ≠ 0 ∧ z * ψ q = ψ p := by
  obtain ⟨n, U, hU, hUaff⟩ := hf
  have hgen : genericPoint X ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).1 hgen
  obtain ⟨A, _, _, hA, ei, hei⟩ := hUaff i
  have hne : Nonempty (U i) := ⟨⟨_, hi⟩⟩
  have haff : IsAffineOpen (U i) := IsAffine.of_isIso ei.hom
  -- the ring map `A → Γ(X, U) → k₀(X)`
  let g : Γ(X, U i) →+* X.functionField := (X.germToFunctionField (U i)).hom
  let θ : A ≃+* Γ(X, U i) :=
    ((Scheme.ΓSpecIso (CommRingCat.of A)).symm ≪≫ (Scheme.Γ.mapIso ei.op) ≪≫ (U i).topIso).commRingCatIsoToRingEquiv
  refine ⟨A, inferInstance, inferInstance, hA, g.comp θ.toRingHom, ?_, ?_, ?_⟩
  · exact (X.germToFunctionField_injective (U i)).comp θ.injective
  · intro c
    have h1 := congrArg (fun φ => φ.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k₀ A)))
    have h2 := congrArg (fun φ => (Scheme.Hom.appTop φ).hom ((Scheme.ΓSpecIso (CommRingCat.of k₀)).inv.hom c)) hei
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom] at h1 h2
    change (X.germToFunctionField (U i)).hom ((U i).topIso.hom.hom (ei.hom.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (algebraMap k₀ A c)))) = _
    rw [h1]
    change (X.germToFunctionField (U i)).hom ((U i).topIso.hom.hom (ei.hom.appTop.hom
      ((specStructure k₀ A).appTop.hom _))) = _
    rw [h2]
    simp only [functionFieldAlgebraMap, Scheme.Opens.topIso_hom, Scheme.Opens.ι_appTop,
      CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    erw [TopCat.Presheaf.germ_res_apply', TopCat.Presheaf.germ_res_apply']
  · intro z
    have := functionField_isFractionRing_of_isAffineOpen X (U i) haff
    obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors Γ(X, U i)) z
    refine ⟨θ.symm p, θ.symm q, ?_, ?_⟩
    · intro h0
      have : (q : Γ(X, U i)) = 0 := by simpa using congrArg θ h0
      exact nonZeroDivisors.coe_ne_zero q this
    · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        RingEquiv.apply_symm_apply]
      exact IsLocalization.mk'_spec X.functionField p q

end Geometric

/-- The imperfect field $k_0 = \mathbb F_2(a)$. -/
abbrev K0 : Type := RatFunc (ZMod 2)

/-- The element $a \in k_0$. -/
abbrev a : K0 := RatFunc.X

theorem not_isSquare_a : ¬ IsSquare a := by
  rintro ⟨r, hr⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact RatFunc.X_ne_zero (by simpa [a] using hr)
  have h := congrArg RatFunc.intDegree hr
  rw [RatFunc.intDegree_mul hr0 hr0, RatFunc.intDegree_X] at h
  omega

/-- The polynomial $X^2 - a$. -/
abbrev sqrtPoly : K0[X] := X ^ 2 - C a

theorem irreducible_sqrtPoly : Irreducible sqrtPoly := by
  have hdeg : sqrtPoly.natDegree = 2 := by
    simp only [sqrtPoly]
    compute_degree!
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [hdeg]; decide
  · intro r hr
    apply not_isSquare_a
    refine ⟨r, ?_⟩
    simp only [IsRoot, sqrtPoly, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hr
    rw [← hr, sq]

instance : Fact (Irreducible sqrtPoly) := ⟨irreducible_sqrtPoly⟩

/-- $L = k_0(\sqrt a)$. -/
abbrev L : Type := AdjoinRoot sqrtPoly

/-- $K = L(t)$. -/
abbrev K : Type := RatFunc L

instance : Module.Finite K0 L := (AdjoinRoot.powerBasis (irreducible_sqrtPoly.ne_zero)).finite

instance : Algebra.EssFiniteType K0 K := by
  have : Algebra.EssFiniteType L[X] K := Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors L[X])
  have : Algebra.EssFiniteType K0 L[X] := Algebra.EssFiniteType.comp K0 L L[X]
  exact Algebra.EssFiniteType.comp K0 L[X] K

theorem trdeg_L_K : Algebra.trdeg L K = 1 := by
  have h := trdeg_add_eq L L[X] (A := K)
  have h0 : Algebra.trdeg L[X] K = 0 := by
    have : Algebra.IsAlgebraic L[X] K := IsLocalization.isAlgebraic K (nonZeroDivisors L[X])
    exact trdeg_eq_zero
  rw [Polynomial.trdeg_of_isDomain, h0, add_zero] at h
  exact h.symm

theorem trdeg_K0_K : Algebra.trdeg K0 K = 1 := by
  have h := trdeg_add_eq K0 L (A := K)
  have h0 : Algebra.trdeg K0 L = 0 := trdeg_eq_zero
  rw [h0, zero_add, trdeg_L_K] at h
  exact h.symm

theorem isFunctionFieldIn_K : IsFunctionFieldIn K0 1 K :=
  ⟨IntermediateField.fg_top K0 K, by rw [trdeg_K0_K]; rfl⟩

theorem root_sq : (AdjoinRoot.root sqrtPoly : L) ^ 2 = algebraMap K0 L a := by
  have h := AdjoinRoot.eval₂_root sqrtPoly
  simp only [sqrtPoly, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
  rw [h, AdjoinRoot.algebraMap_eq]

/-- **Milne's Theorem 7.2 is false over the imperfect field $\mathbb F_2(a)$**: the function field
$K = \mathbb F_2(a)(\sqrt a)(t)$ in one variable is not the function field of a complete regular curve in Milne's
sense (a geometrically reduced variety). See the module docstring and `docs/updates-and-errata.md`. -/
@[kb "milne2017mf" "Section 7, Theorem 7.2 (pdf p. 94): refuted over imperfect fields"]
theorem not_curveFunctionFieldEquivalence : ¬ CurveFunctionFieldEquivalence K0 := by
  intro H
  obtain ⟨X, hX, f, hc, e, he⟩ := H.essSurj K isFunctionFieldIn_K
  obtain ⟨A, _, _, hA, ψ, hψ, hψk, hfrac⟩ := exists_affineAlgebra_functionField f hc.1.1.1
  set x := e (algebraMap L K (AdjoinRoot.root sqrtPoly))
  have hx : x ^ 2 = functionFieldAlgebraMap K0 f a := by
    rw [← he, ← map_pow, ← map_pow, root_sq, ← IsScalarTower.algebraMap_apply]
  obtain ⟨p, q, hq, hpq⟩ := hfrac x
  have hpq2 : p ^ 2 = algebraMap K0 A a * q ^ 2 := by
    apply hψ
    rw [map_pow, map_mul, map_pow, hψk, ← hx, ← hpq]
    ring
  exact hq (eq_zero_of_sq_eq hA.2 not_isSquare_a hpq2)

end ModularFormsKB.Milne.Ch7Counterexample

namespace ModularFormsKB.Milne

universe u

/-- **Milne, Theorem 7.2, corrected** (named statement): over a *perfect* field $k_0$ the map $X \mapsto k_0(X)$ is
an equivalence from complete regular irreducible curves over $k_0$ to function fields in one variable over $k_0$, as
in `CurveFunctionFieldEquivalence`. The hypothesis is needed: over the imperfect field $\mathbb F_2(a)$ the statement
fails (`Ch7Counterexample.not_curveFunctionFieldEquivalence`); Milne assumes $k_0$ perfect from Section 7 on
(pdf p. 93, "Assume $k_0$ is perfect") but not in the statement of Theorem 7.2. -/
@[kb "milne2017mf" "Section 7, Theorem 7.2 (pdf p. 94), corrected: k0 perfect"]
structure CurveFunctionFieldEquivalencePerfect (k₀ : Type u) [Field k₀] [PerfectField k₀] : Prop where
  statement : CurveFunctionFieldEquivalence k₀

end ModularFormsKB.Milne
