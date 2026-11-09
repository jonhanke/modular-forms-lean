import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Flat.Basic
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Adjoin.FGBaseChange
import Mathlib.Algebra.Polynomial.Lifts
import TauCeti.RingTheory.TensorProduct.IsDomain

/-!
# Geometric irreducibility of a field extension and its field of constants (algebra)

Let $k$ be a field, $\bar k$ an algebraic closure and $K \supseteq k$ a field.

- `isDomain_tensor_of_isLocalization`: $\bar k \otimes_k M^{-1}A$ is a domain when $\bar k \otimes_k A$ is.
- `eq_of_one_tmul_eq_tmul_one`: if $1 \otimes l = \alpha \otimes 1$ in $\bar k \otimes_k K$ then $l \in k$.
- `algebraicClosure_eq_bot_of_isDomain`: if $\bar k \otimes_k K$ is a domain, $k$ is algebraically closed in $K$: for
  $l$ algebraic with minimal polynomial $p = \prod (X - \alpha)$ over $\bar k$, $\prod (1 \otimes l - \alpha \otimes 1) =
  p(1 \otimes l) = 0$, so some factor vanishes.

Used for the last assertion of Theorem 7.2 (Milne, `milne2017mf`, Section 7, pdf p. 94).
-/

universe u

open TensorProduct Polynomial

noncomputable section

namespace ModularFormsKB.Milne.Constants

variable {k : Type u} [Field k]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- $\bar k \otimes_k M^{-1}A$ is a domain when $\bar k \otimes_k A$ is. -/
theorem isDomain_tensor_of_isLocalization {A B : Type u} [CommRing A] [IsDomain A] [Algebra k A] [CommRing B]
    [Algebra k B] [Algebra A B] [IsScalarTower k A B] (M : Submonoid A) (hM : M ≤ nonZeroDivisors A)
    [IsLocalization M B] (h : IsDomain (AlgebraicClosure k ⊗[k] A)) : IsDomain (AlgebraicClosure k ⊗[k] B) := by
  let φ : AlgebraicClosure k ⊗[k] A →ₐ[k] AlgebraicClosure k ⊗[k] B :=
    Algebra.TensorProduct.map (AlgHom.id k _) (IsScalarTower.toAlgHom k A B)
  let _ : Algebra (AlgebraicClosure k ⊗[k] A) (AlgebraicClosure k ⊗[k] B) := φ.toRingHom.toAlgebra
  have : IsScalarTower (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A) (AlgebraicClosure k ⊗[k] B) :=
    .of_algebraMap_eq' (by ext c; simp [φ, RingHom.algebraMap_toAlgebra])
  have hloc := IsLocalization.tensorProduct_tensorProduct_right k (AlgebraicClosure k) M B
    (by ext a; simp [φ, RingHom.algebraMap_toAlgebra])
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (R := AlgebraicClosure k ⊗[k] A)
    (M := M.map (Algebra.TensorProduct.includeRight (R := k) (A := AlgebraicClosure k)))
    (AlgebraicClosure k ⊗[k] B) ?_
  rintro _ ⟨s, hs, rfl⟩
  apply mem_nonZeroDivisors_of_ne_zero
  intro h0
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[k] AlgebraicClosure k ⊗[k] A) :=
    Algebra.TensorProduct.includeRight_injective (FaithfulSMul.algebraMap_injective k _)
  exact nonZeroDivisors.ne_zero (hM hs) (hinj (h0.trans (map_zero _).symm))

variable {K : Type u} [Field K] [Algebra k K]

/-- **If $1 \otimes l = \alpha \otimes 1$ in $\bar k \otimes_k K$, then $l \in k$.** -/
theorem mem_bot_of_one_tmul_eq_tmul_one {l : K} {α : AlgebraicClosure k}
    (h : (1 : AlgebraicClosure k) ⊗ₜ[k] l = α ⊗ₜ[k] (1 : K)) : l ∈ (⊥ : IntermediateField k K) := by
  by_contra hl
  have hl' : l ∉ Submodule.span k {(1 : K)} := by
    intro hs
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
    exact hl (by rw [Algebra.smul_def, mul_one]; exact IntermediateField.algebraMap_mem _ c)
  obtain ⟨φ, hφl, hφ1⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hl' inferInstance
  have h1 : φ 1 = 0 := by
    have : φ 1 ∈ (Submodule.span k {(1 : K)}).map φ := Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self 1)
    rw [hφ1] at this
    exact this
  have := congrArg (TensorProduct.rid k (AlgebraicClosure k) ∘ LinearMap.lTensor (AlgebraicClosure k) φ) h
  simp only [Function.comp_apply, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, h1, zero_smul] at this
  exact hφl (by simpa [Algebra.smul_def] using this)

/-- **If $\bar k \otimes_k K$ is a domain, then $k$ is algebraically closed in $K$.** -/
theorem algebraicClosure_eq_bot_of_isDomain (h : IsDomain (AlgebraicClosure k ⊗[k] K)) :
    algebraicClosure k K = ⊥ := by
  refine eq_bot_iff.mpr fun l hl ↦ ?_
  have hal : IsAlgebraic k l := mem_algebraicClosure_iff.mp hl
  have hint : IsIntegral k l := hal.isIntegral
  set p := minpoly k l
  set q := p.map (algebraMap k (AlgebraicClosure k))
  have hq : q.Monic := (minpoly.monic hint).map _
  have hsplit : (q.roots.map fun a ↦ X - C a).prod = q :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hq (IsAlgClosed.card_roots_eq_natDegree)
  set y : AlgebraicClosure k ⊗[k] K := (1 : AlgebraicClosure k) ⊗ₜ[k] l
  have hy : aeval y q = 0 := by
    rw [aeval_map_algebraMap]
    have : y = (Algebra.TensorProduct.includeRight : K →ₐ[k] AlgebraicClosure k ⊗[k] K) l := rfl
    rw [this, aeval_algHom_apply, minpoly.aeval, map_zero]
  rw [← hsplit, map_multiset_prod, Multiset.map_map] at hy
  obtain ⟨α, -, hα⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hy)
  simp only [Function.comp_apply, map_sub, aeval_X, aeval_C] at hα
  refine mem_bot_of_one_tmul_eq_tmul_one (α := α) ?_
  rw [sub_eq_zero] at hα
  exact hα

/-! ### The converse over a perfect field -/

section Converse

variable (hK : algebraicClosure k K = ⊥)
include hK

/-- The minimal polynomial over $K$ of an element algebraic over $k$ has the same degree as over $k$ when $k$ is
algebraically closed in $K$. -/
theorem natDegree_minpoly_eq {E : Type u} [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] {β : E}
    (hβ : IsIntegral k β) : (minpoly K β).natDegree = (minpoly k β).natDegree := by
  have hβK : IsIntegral K β := hβ.tower_top
  have hdvd : minpoly K β ∣ (minpoly k β).map (algebraMap k K) := minpoly.dvd_map_of_isScalarTower k K β
  have hlifts : minpoly K β ∈ lifts (algebraMap k K) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    have hint := isIntegral_coeff_of_dvd (minpoly k β) (minpoly K β) (minpoly.monic hβ) (minpoly.monic hβK)
      hdvd n
    have hmem : (minpoly K β).coeff n ∈ algebraicClosure k K :=
      mem_algebraicClosure_iff.mpr hint.isAlgebraic
    rw [hK, IntermediateField.mem_bot] at hmem
    exact hmem
  obtain ⟨q, hqmap, hqdeg, hqmon⟩ := lifts_and_natDegree_eq_and_monic hlifts (minpoly.monic hβK)
  have hq0 : aeval β q = 0 := by
    rw [← aeval_map_algebraMap K, hqmap, minpoly.aeval]
  apply le_antisymm
  · have hne : (minpoly k β).map (algebraMap k K) ≠ 0 := (minpoly.monic hβ).map _ |>.ne_zero
    calc (minpoly K β).natDegree ≤ ((minpoly k β).map (algebraMap k K)).natDegree :=
          natDegree_le_of_dvd hdvd hne
      _ = (minpoly k β).natDegree := natDegree_map _
  · rw [← hqdeg]
    exact natDegree_le_of_dvd (minpoly.dvd k β hq0) hqmon.ne_zero

/-- $k(\alpha) \otimes_k K$ is a domain for $\alpha \in \bar k$, when $k$ is algebraically closed in $K$. -/
theorem isDomain_adjoin_tensor (α : AlgebraicClosure k) :
    IsDomain (IntermediateField.adjoin k {α} ⊗[k] K) := by
  set E := AlgebraicClosure K
  have hα : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  set F := IntermediateField.adjoin k {α}
  let fF : F →ₐ[k] E := IsAlgClosed.lift
  set A := fF.fieldRange
  let eA : F ≃ₐ[k] A := AlgEquiv.ofInjectiveField fF
  let pb := IntermediateField.adjoin.powerBasis hα
  let b := pb.basis.map eA.toLinearEquiv
  set β : E := fF (IntermediateField.AdjoinSimple.gen k α)
  have hβ : IsIntegral k β := (Algebra.IsIntegral.isIntegral (IntermediateField.AdjoinSimple.gen k α)).map fF
  have hmin : minpoly k β = minpoly k α := by
    rw [minpoly.algHom_eq fF fF.injective, IntermediateField.minpoly_gen]
  have hdim : pb.dim = (minpoly K β).natDegree := by
    rw [natDegree_minpoly_eq hK hβ, hmin, IntermediateField.adjoin.powerBasis_dim]
  have hb : ∀ i, (A.val ∘ b) i = β ^ (i : ℕ) := by
    intro i
    simp only [Function.comp_apply, b, pb, Module.Basis.map_apply, PowerBasis.coe_basis,
      IntermediateField.adjoin.powerBasis_gen, AlgEquiv.toLinearEquiv_apply]
    change ((AlgEquiv.ofInjectiveField fF) _ : E) = _
    exact map_pow fF _ _
  have hli : LinearIndependent K (A.val ∘ b) := by
    have h := linearIndependent_pow (K := K) β
    rw [← hdim] at h
    convert h using 1
    funext i
    exact hb i
  have hLD : A.LinearDisjoint K := IntermediateField.LinearDisjoint.of_basis_left b hli
  have : IsDomain (A ⊗[k] K) := hLD.isDomain
  exact (Algebra.TensorProduct.congr eA AlgEquiv.refl).toMulEquiv.isDomain

/-- **If $k$ is perfect and algebraically closed in $K$, then $K \otimes_k \bar k$ is a domain.** -/
theorem isDomain_tensor_of_algebraicClosure_eq_bot [PerfectField k] : IsDomain (K ⊗[k] AlgebraicClosure k) := by
  classical
  have hinjL : Function.Injective (Algebra.TensorProduct.includeLeft : K →ₐ[k] K ⊗[k] AlgebraicClosure k) :=
    Algebra.TensorProduct.includeLeft_injective (FaithfulSMul.algebraMap_injective k _)
  have : Nontrivial (K ⊗[k] AlgebraicClosure k) := hinjL.nontrivial
  -- every pair of elements comes from `K ⊗ k(α)` for some `α`
  have key : ∀ a b : K ⊗[k] AlgebraicClosure k, ∃ α : AlgebraicClosure k,
      a ∈ (Algebra.TensorProduct.map (AlgHom.id K K) (IntermediateField.adjoin k {α}).val).range ∧
      b ∈ (Algebra.TensorProduct.map (AlgHom.id K K) (IntermediateField.adjoin k {α}).val).range := by
    intro a b
    obtain ⟨C₁, hC₁, ha⟩ := exists_fg_and_mem_baseChange a
    obtain ⟨C₂, hC₂, hb⟩ := exists_fg_and_mem_baseChange b
    obtain ⟨s, hs⟩ := hC₁.sup hC₂
    set M := IntermediateField.adjoin k (s : Set (AlgebraicClosure k))
    have : FiniteDimensional k M :=
      IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
    obtain ⟨γ, hγ⟩ := Field.exists_primitive_element k M
    have hM : M = IntermediateField.adjoin k {(γ : AlgebraicClosure k)} := by
      rw [← IntermediateField.lift_adjoin_simple, hγ, IntermediateField.lift_top]
    refine ⟨γ, ?_, ?_⟩
    all_goals
      have hle : ∀ C : Subalgebra k (AlgebraicClosure k), C ≤ C₁ ⊔ C₂ →
          C ≤ (IntermediateField.adjoin k {(γ : AlgebraicClosure k)}).toSubalgebra := fun C hC ↦ by
        rw [← hM]
        refine hC.trans ?_
        rw [← hs]
        exact Algebra.adjoin_le (IntermediateField.subset_adjoin k _)
    · obtain ⟨y, rfl⟩ := ha
      have h := hle C₁ le_sup_left
      refine ⟨Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.inclusion h) y, ?_⟩
      show (Algebra.TensorProduct.map (AlgHom.id K K) _) _ = (Algebra.TensorProduct.map (AlgHom.id K K) C₁.val) y
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
      rfl
    · obtain ⟨y, rfl⟩ := hb
      have h := hle C₂ le_sup_right
      refine ⟨Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.inclusion h) y, ?_⟩
      show (Algebra.TensorProduct.map (AlgHom.id K K) _) _ = (Algebra.TensorProduct.map (AlgHom.id K K) C₂.val) y
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
      rfl
  refine @NoZeroDivisors.to_isDomain _ _ this ⟨fun {a b} hab ↦ ?_⟩
  obtain ⟨α, ⟨x, hx⟩, ⟨y, hy⟩⟩ := key a b
  change (Algebra.TensorProduct.map (AlgHom.id K K) (IntermediateField.adjoin k {α}).val) x = a at hx
  change (Algebra.TensorProduct.map (AlgHom.id K K) (IntermediateField.adjoin k {α}).val) y = b at hy
  subst hx hy
  have := isDomain_adjoin_tensor hK α
  have : IsDomain (K ⊗[k] IntermediateField.adjoin k {α}) := (Algebra.TensorProduct.comm k K (IntermediateField.adjoin k {α})).toMulEquiv.isDomain
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K) (IntermediateField.adjoin k {α}).val) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K) (IntermediateField.adjoin k {α}).val.toLinearMap Subtype.val_injective
  rw [← map_mul] at hab
  have h0 : x * y = 0 := hinj (hab.trans (map_zero _).symm)
  rcases mul_eq_zero.mp h0 with h | h
  · left; rw [h, map_zero]
  · right; rw [h, map_zero]

end Converse

/-- **If $\bar k \otimes_k K$ is a domain, so is $M \otimes_k K$ for every field $M \supseteq k$**: embed $\bar k$ in an
algebraic closure $\bar M$; then $\bar M \otimes_k K = \bar M \otimes_{\bar k} (\bar k \otimes_k K)$ is a domain (a
tensor product of domains over an algebraically closed field, Tau Ceti), and $M \otimes_k K \subseteq \bar M \otimes_k K$.
-/
theorem isDomain_tensor_of_isDomain (h : IsDomain (AlgebraicClosure k ⊗[k] K)) (M : Type u) [Field M]
    [Algebra k M] : IsDomain (M ⊗[k] K) := by
  let ι : AlgebraicClosure k →ₐ[k] AlgebraicClosure M := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure k) (AlgebraicClosure M) := ι.toRingHom.toAlgebra
  have : IsScalarTower k (AlgebraicClosure k) (AlgebraicClosure M) :=
    .of_algebraMap_eq fun c ↦ (ι.commutes c).symm
  have : IsDomain (AlgebraicClosure M ⊗[AlgebraicClosure k] (AlgebraicClosure k ⊗[k] K)) :=
    TauCeti.isDomain_tensorProduct_of_isAlgClosed _ _
  have : IsDomain (AlgebraicClosure M ⊗[k] K) :=
    (Algebra.TensorProduct.cancelBaseChange k (AlgebraicClosure k) (AlgebraicClosure M)
      (AlgebraicClosure M) K).symm.toMulEquiv.isDomain
  have hinj : Function.Injective (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k M (AlgebraicClosure M))
      (AlgHom.id k K)) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := K)
      (IsScalarTower.toAlgHom k M (AlgebraicClosure M)).toLinearMap (RingHom.injective _)
  exact hinj.isDomain _

end ModularFormsKB.Milne.Constants
