/-
# Equal traces of commuting families force equal joint eigenvalue multiplicities

If two families of commuting operators on finite-dimensional complex spaces have equal traces on every finite product
(`A` on `V`, `B` on `W`), and the second family has a basis of joint eigenvectors with pairwise distinct eigenvalue
systems, then in the first space every joint eigenspace has dimension at most one, every eigenvalue system occurring in
the first space occurs in the second, and the first space is spanned by joint eigenvectors.

Proof sketch: equal traces of products pass to equal traces of products of shifted operators `A i - c`; decomposing `V`
into joint generalized eigenspaces `V_χ`, the trace of such a product is `∑_χ dim V_χ * ∏ (χ i - c)`; separating the
finitely many systems `χ` by suitable products gives `dim V_χ = 1` if `χ` occurs in `W` and `0` otherwise.
-/
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace ModularFormsKB.HalfIntegral

/-- `v` is a joint eigenvector of the family `A` with eigenvalue system `ν` (it may be `0`). -/
def IsJointEigenvector {ι V : Type*} [AddCommGroup V] [Module ℂ V] (A : ι → Module.End ℂ V) (ν : ι → ℂ) (v : V) :
    Prop :=
  ∀ i, A i v = ν i • v

section Aux

variable {ι V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The product of the shifted operators `A i - c` over a list of pairs `(i, c)`. -/
noncomputable def shiftProd (A : ι → Module.End ℂ V) (ℓ : List (ι × ℂ)) : Module.End ℂ V :=
  (ℓ.map fun p => A p.1 - algebraMap ℂ _ p.2).prod

/-- The corresponding scalar product `∏ (χ i - c)`. -/
def shiftScalar (ℓ : List (ι × ℂ)) (χ : ι → ℂ) : ℂ :=
  (ℓ.map fun p => χ p.1 - p.2).prod

@[simp] lemma shiftProd_nil (A : ι → Module.End ℂ V) : shiftProd A [] = 1 := rfl

lemma shiftProd_cons (A : ι → Module.End ℂ V) (p : ι × ℂ) (ℓ : List (ι × ℂ)) :
    shiftProd A (p :: ℓ) = (A p.1 - algebraMap ℂ _ p.2) * shiftProd A ℓ := by
  simp [shiftProd]

@[simp] lemma shiftScalar_nil (χ : ι → ℂ) : shiftScalar [] χ = 1 := rfl

lemma shiftScalar_cons (p : ι × ℂ) (ℓ : List (ι × ℂ)) (χ : ι → ℂ) :
    shiftScalar (p :: ℓ) χ = (χ p.1 - p.2) * shiftScalar ℓ χ := by
  simp [shiftScalar]

lemma trace_shiftProd_cons (A : ι → Module.End ℂ V) (p : ι × ℂ) (ℓ : List (ι × ℂ)) (m : List ι) :
    LinearMap.trace ℂ V (shiftProd A (p :: ℓ) * (m.map A).prod) =
      LinearMap.trace ℂ V (shiftProd A ℓ * ((m ++ [p.1]).map A).prod) -
        p.2 * LinearMap.trace ℂ V (shiftProd A ℓ * (m.map A).prod) := by
  have h : shiftProd A (p :: ℓ) * (m.map A).prod =
      A p.1 * (shiftProd A ℓ * (m.map A).prod) - p.2 • (shiftProd A ℓ * (m.map A).prod) := by
    rw [shiftProd_cons]
    simp [sub_mul, mul_assoc, Algebra.algebraMap_eq_smul_one]
  rw [h, map_sub, map_smul, LinearMap.trace_mul_comm, smul_eq_mul, mul_assoc]
  simp

lemma trace_shiftProd_eq {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A : ι → Module.End ℂ V) (B : ι → Module.End ℂ W)
    (htr : ∀ l : List ι, LinearMap.trace ℂ V (l.map A).prod = LinearMap.trace ℂ W (l.map B).prod) :
    ∀ (ℓ : List (ι × ℂ)) (m : List ι),
      LinearMap.trace ℂ V (shiftProd A ℓ * (m.map A).prod) =
        LinearMap.trace ℂ W (shiftProd B ℓ * (m.map B).prod) := by
  intro ℓ
  induction ℓ with
  | nil => intro m; simpa using htr m
  | cons p ℓ ih =>
    intro m
    rw [trace_shiftProd_cons, trace_shiftProd_cons, ih, ih]

end Aux

section Nilp

variable {ι U : Type*} [AddCommGroup U] [Module ℂ U]

lemma commute_shift (a : ι → Module.End ℂ U) (ha : ∀ i j, Commute (a i) (a j)) (j i : ι) (c c' : ℂ) :
    Commute (a j - algebraMap ℂ _ c) (a i - algebraMap ℂ _ c') :=
  ((ha j i).sub_right (Algebra.commute_algebraMap_right c' (a j))).sub_left
    (Algebra.commute_algebraMap_left c _)

lemma commute_shiftProd (a : ι → Module.End ℂ U) (ha : ∀ i j, Commute (a i) (a j)) (ℓ : List (ι × ℂ))
    (i : ι) (c : ℂ) : Commute (shiftProd a ℓ) (a i - algebraMap ℂ _ c) := by
  refine Commute.list_prod_left _ _ ?_
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨q, _, rfl⟩ := hx
  exact commute_shift a ha _ _ _ _

lemma trace_shiftProd_nilpotent [FiniteDimensional ℂ U] (a : ι → Module.End ℂ U)
    (ha : ∀ i j, Commute (a i) (a j)) (χ : ι → ℂ) (hn : ∀ i, IsNilpotent (a i - algebraMap ℂ _ (χ i)))
    (ℓ : List (ι × ℂ)) :
    LinearMap.trace ℂ U (shiftProd a ℓ) = shiftScalar ℓ χ * (Module.finrank ℂ U : ℂ) := by
  induction ℓ with
  | nil => simp [LinearMap.trace_one]
  | cons p ℓ ih =>
    have hc := commute_shiftProd a ha ℓ p.1 p.2
    have h2 := LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent (f := shiftProd a ℓ)
      (g := a p.1 - algebraMap ℂ _ p.2) (χ p.1 - p.2) hc (by
        have : a p.1 - algebraMap ℂ _ p.2 - algebraMap ℂ _ (χ p.1 - p.2) =
            a p.1 - algebraMap ℂ _ (χ p.1) := by simp [map_sub]
        rw [this]; exact hn p.1)
    rw [shiftProd_cons, ← hc.eq]
    change LinearMap.trace ℂ U (shiftProd a ℓ ∘ₗ (a p.1 - algebraMap ℂ _ p.2)) = _
    rw [h2, ih, shiftScalar_cons]; ring

end Nilp

section WSide

variable {ι W κ : Type*} [AddCommGroup W] [Module ℂ W]

lemma shiftProd_basis (B : ι → Module.End ℂ W) (b : Module.Basis κ ℂ W) (μ : κ → ι → ℂ)
    (hb : ∀ x i, B i (b x) = μ x i • b x) (ℓ : List (ι × ℂ)) (x : κ) :
    shiftProd B ℓ (b x) = shiftScalar ℓ (μ x) • b x := by
  induction ℓ with
  | nil => simp
  | cons p ℓ ih =>
    rw [shiftProd_cons, shiftScalar_cons, mul_apply_eq_comp, ih, map_smul]
    simp only [LinearMap.sub_apply, hb, Module.algebraMap_end_apply]
    module

lemma trace_shiftProd_basis [Fintype κ] (B : ι → Module.End ℂ W) (b : Module.Basis κ ℂ W)
    (μ : κ → ι → ℂ) (hb : ∀ x i, B i (b x) = μ x i • b x) (ℓ : List (ι × ℂ)) :
    LinearMap.trace ℂ W (shiftProd B ℓ) = ∑ x, shiftScalar ℓ (μ x) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [LinearMap.toMatrix_apply, shiftProd_basis B b μ hb]

end WSide

section VSide

open Set

variable {ι V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The joint generalized eigenspace of the family `A` for the eigenvalue system `χ`. -/
noncomputable def jointGen (A : ι → Module.End ℂ V) (χ : ι → ℂ) : Submodule ℂ V :=
  ⨅ i, (A i).maxGenEigenspace (χ i)

lemma mapsTo_jointGen (A : ι → Module.End ℂ V) (hA : ∀ i j, Commute (A i) (A j)) (χ : ι → ℂ) (j : ι) :
    MapsTo (A j) (jointGen A χ) (jointGen A χ) := by
  intro x hx
  simp only [jointGen, SetLike.mem_coe, Submodule.mem_iInf] at hx ⊢
  exact fun i => Module.End.mapsTo_maxGenEigenspace_of_comm (hA i j) (χ i) (hx i)

lemma iSupIndep_jointGen (A : ι → Module.End ℂ V) (hA : ∀ i j, Commute (A i) (A j)) :
    iSupIndep (jointGen A) :=
  Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo A
    fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hA j i) φ

lemma iSup_jointGen (A : ι → Module.End ℂ V) (hA : ∀ i j, Commute (A i) (A j)) :
    iSup (jointGen A) = ⊤ :=
  Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo A
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hA j i) φ)
    (fun i => Module.End.iSup_maxGenEigenspace_eq_top _)

lemma finite_jointGen (A : ι → Module.End ℂ V) (hA : ∀ i j, Commute (A i) (A j)) :
    {χ | jointGen A χ ≠ ⊥}.Finite :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep (iSupIndep_jointGen A hA)

lemma shiftProd_mem (A : ι → Module.End ℂ V) (p : Submodule ℂ V) (hp : ∀ i, MapsTo (A i) p p)
    (ℓ : List (ι × ℂ)) (x : V) (hx : x ∈ p) : shiftProd A ℓ x ∈ p := by
  induction ℓ with
  | nil => simpa using hx
  | cons q ℓ ih =>
    rw [shiftProd_cons, mul_apply_eq_comp]
    simp only [LinearMap.sub_apply, Module.algebraMap_end_apply]
    exact p.sub_mem (hp q.1 ih) (p.smul_mem _ ih)

lemma coe_shiftProd_restrict (A : ι → Module.End ℂ V) (p : Submodule ℂ V) (hp : ∀ i, MapsTo (A i) p p)
    (ℓ : List (ι × ℂ)) (x : p) :
    ((shiftProd (fun i => (A i).restrict (hp i)) ℓ x : p) : V) = shiftProd A ℓ x := by
  induction ℓ with
  | nil => simp
  | cons q ℓ ih =>
    rw [shiftProd_cons, shiftProd_cons, mul_apply_eq_comp, mul_apply_eq_comp]
    simp only [LinearMap.sub_apply, Module.algebraMap_end_apply, Submodule.coe_sub, SetLike.val_smul]
    show A q.1 ((shiftProd (fun i => (A i).restrict (hp i)) ℓ x : p) : V) - q.2 • _ = _
    rw [ih]

lemma trace_shiftProd_V (A : ι → Module.End ℂ V) (hA : ∀ i j, Commute (A i) (A j)) (ℓ : List (ι × ℂ)) :
    LinearMap.trace ℂ V (shiftProd A ℓ) =
      ∑ χ ∈ (finite_jointGen A hA).toFinset, shiftScalar ℓ χ * (Module.finrank ℂ (jointGen A χ) : ℂ) := by
  classical
  have hint : DirectSum.IsInternal (jointGen A) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_jointGen A hA) (iSup_jointGen A hA)
  have hmaps : ∀ χ, MapsTo (shiftProd A ℓ) (jointGen A χ) (jointGen A χ) :=
    fun χ x hx => shiftProd_mem A _ (mapsTo_jointGen A hA χ) ℓ x hx
  rw [LinearMap.trace_eq_sum_trace_restrict' hint (finite_jointGen A hA) hmaps]
  refine Finset.sum_congr rfl fun χ _ => ?_
  have hr : (shiftProd A ℓ).restrict (hmaps χ) =
      shiftProd (fun i => (A i).restrict (mapsTo_jointGen A hA χ i)) ℓ := by
    ext x
    exact (coe_shiftProd_restrict A _ (mapsTo_jointGen A hA χ) ℓ x).symm
  rw [hr]
  refine trace_shiftProd_nilpotent _ (fun i j => LinearMap.restrict_commute (hA i j) _ _) χ ?_ ℓ
  intro i
  have hh : MapsTo (A i - algebraMap ℂ (Module.End ℂ V) (χ i)) (jointGen A χ) (jointGen A χ) :=
    fun x hx => (mapsTo_jointGen A hA χ i hx |> fun h => by
      simp only [SetLike.mem_coe] at hx h ⊢
      exact (jointGen A χ).sub_mem h ((jointGen A χ).smul_mem _ hx))
  have heq : (fun i => (A i).restrict (mapsTo_jointGen A hA χ i)) i - algebraMap ℂ _ (χ i) =
      (A i - algebraMap ℂ (Module.End ℂ V) (χ i)).restrict hh := by
    ext x; simp only [LinearMap.sub_apply, Module.algebraMap_end_apply, Submodule.coe_sub, SetLike.val_smul]; rfl
  rw [heq]
  exact Module.End.isNilpotent_restrict_of_le (p := jointGen A χ)
    (q := (A i).maxGenEigenspace (χ i)) (iInf_le _ i)
    (Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (A i) (χ i))

end VSide

section Final

open Set

lemma separate {ι : Type*} (S : Finset (ι → ℂ)) (f g : (ι → ℂ) → ℂ)
    (h : ∀ ℓ : List (ι × ℂ), ∑ χ ∈ S, f χ * shiftScalar ℓ χ = ∑ χ ∈ S, g χ * shiftScalar ℓ χ) :
    ∀ ν ∈ S, f ν = g ν := by
  classical
  intro ν hν
  have hex : ∀ χ : {x // x ∈ S.erase ν}, ∃ i, χ.1 i ≠ ν i := fun χ =>
    Function.ne_iff.1 (Finset.mem_erase.1 χ.2).1
  choose idx hidx using hex
  let ℓ : List (ι × ℂ) := (S.erase ν).attach.toList.map fun χ => (idx χ, χ.1 (idx χ))
  have hℓ : ∀ χ', shiftScalar ℓ χ' = ∏ χ ∈ (S.erase ν).attach, (χ' (idx χ) - χ.1 (idx χ)) := by
    intro χ'
    simp only [shiftScalar, ℓ, List.map_map]
    exact Finset.prod_map_toList _ _
  have h0 : ∀ χ' ∈ S, χ' ≠ ν → shiftScalar ℓ χ' = 0 := by
    intro χ' hχ' hne
    rw [hℓ]
    exact Finset.prod_eq_zero (i := ⟨χ', Finset.mem_erase.2 ⟨hne, hχ'⟩⟩) (Finset.mem_attach _ _)
      (sub_self _)
  have h1 : shiftScalar ℓ ν ≠ 0 := by
    rw [hℓ]; exact Finset.prod_ne_zero_iff.2 fun χ _ => sub_ne_zero.2 (hidx χ).symm
  have key := h ℓ
  rw [Finset.sum_eq_single_of_mem ν hν (fun χ hχ hne => by rw [h0 χ hχ hne, mul_zero]),
      Finset.sum_eq_single_of_mem ν hν (fun χ hχ hne => by rw [h0 χ hχ hne, mul_zero])] at key
  exact mul_right_cancel₀ h1 key

lemma exists_smul_of_finrank_le_one {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (U : Submodule ℂ V) (hU : Module.finrank ℂ U ≤ 1) (v w : V) (hv : v ∈ U) (hw : w ∈ U) (hv0 : v ≠ 0) :
    ∃ t : ℂ, w = t • v := by
  have hx' : (⟨v, hv⟩ : U) ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have h1 : Module.finrank ℂ U = 1 :=
    le_antisymm hU (Nat.succ_le_of_lt (Module.finrank_pos_iff_exists_ne_zero.2 ⟨_, hx'⟩))
  obtain ⟨d, hd⟩ := (finrank_eq_one_iff_of_ne_zero' ⟨v, hv⟩ hx').1 h1 ⟨w, hw⟩
  exact ⟨d, (congrArg Subtype.val hd).symm⟩

lemma eq_zero_of_finrank_le_one {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (g : Module.End ℂ V) (U : Submodule ℂ V) (hg : MapsTo g U U) (hU : Module.finrank ℂ U ≤ 1)
    (x : V) (hx : x ∈ U) (hk : ∃ k : ℕ, (g ^ k) x = 0) : g x = 0 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨k, hk⟩ := hk
  obtain ⟨d, hgx⟩ := exists_smul_of_finrank_le_one U hU x (g x) hx (hg hx) hx0
  have hpow : ∀ n : ℕ, (g ^ n) x = d ^ n • x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, mul_apply_eq_comp, hgx, map_smul, ih, smul_smul, pow_succ, mul_comm]
  rw [hpow] at hk
  have hd : d ^ k = 0 := (smul_eq_zero.1 hk).resolve_right hx0
  have : d = 0 := by
    by_contra hd0
    exact pow_ne_zero k hd0 hd
  rw [hgx, this, zero_smul]

theorem jointEigen_of_trace_eq {ι V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : ι → Module.End ℂ V) (B : ι → Module.End ℂ W)
    (hA : ∀ i j, Commute (A i) (A j))
    (htr : ∀ l : List ι, LinearMap.trace ℂ V (l.map A).prod = LinearMap.trace ℂ W (l.map B).prod)
    {κ : Type*} (b : Module.Basis κ ℂ W) (μ : κ → ι → ℂ) (hb : ∀ x i, B i (b x) = μ x i • b x)
    (hμ : Function.Injective μ) :
    (∀ (ν : ι → ℂ) (v w : V), IsJointEigenvector A ν v → IsJointEigenvector A ν w → v ≠ 0 →
        ∃ t : ℂ, w = t • v) ∧
    (∀ (ν : ι → ℂ) (v : V), IsJointEigenvector A ν v → v ≠ 0 → ∃ x, μ x = ν) ∧
    Submodule.span ℂ {v : V | ∃ ν, IsJointEigenvector A ν v} = ⊤ := by
  classical
  have : Finite κ := Module.Finite.finite_basis b
  have : Fintype κ := Fintype.ofFinite κ
  set S : Finset (ι → ℂ) := (finite_jointGen A hA).toFinset ∪ Finset.univ.image μ with hS
  have hsub : (finite_jointGen A hA).toFinset ⊆ S := Finset.subset_union_left
  have hkey : ∀ χ ∈ S, (Module.finrank ℂ (jointGen A χ) : ℂ) = if χ ∈ Set.range μ then 1 else 0 := by
    refine separate S (fun χ => (Module.finrank ℂ (jointGen A χ) : ℂ))
      (fun χ => if χ ∈ Set.range μ then 1 else 0) ?_
    intro ℓ
    have e := trace_shiftProd_eq A B htr ℓ []
    simp only [List.map_nil, List.prod_nil, mul_one] at e
    rw [trace_shiftProd_V A hA ℓ, trace_shiftProd_basis B b μ hb ℓ] at e
    have hL : ∑ χ ∈ (finite_jointGen A hA).toFinset, shiftScalar ℓ χ * (Module.finrank ℂ (jointGen A χ) : ℂ) =
        ∑ χ ∈ S, (Module.finrank ℂ (jointGen A χ) : ℂ) * shiftScalar ℓ χ := by
      rw [Finset.sum_subset hsub]
      · exact Finset.sum_congr rfl fun χ _ => mul_comm _ _
      · intro χ _ hχ
        have : jointGen A χ = ⊥ := by simpa using hχ
        simp [this]
    have himg : Finset.univ.image μ = S.filter (· ∈ Set.range μ) := by
      ext χ
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, hS, Finset.mem_union,
        Set.mem_range]
      constructor
      · rintro ⟨x, rfl⟩; exact ⟨Or.inr ⟨x, rfl⟩, x, rfl⟩
      · rintro ⟨_, x, hx⟩; exact ⟨x, hx⟩
    have hR : ∑ χ ∈ S, (if χ ∈ Set.range μ then (1 : ℂ) else 0) * shiftScalar ℓ χ =
        ∑ x, shiftScalar ℓ (μ x) := by
      rw [← Finset.sum_image (f := fun χ => shiftScalar ℓ χ) (g := μ) (fun x _ y _ h => hμ h), himg,
        Finset.sum_filter]
      exact Finset.sum_congr rfl fun χ _ => by split_ifs <;> simp
    rw [← hL, e, hR]
  have hfr : ∀ χ, Module.finrank ℂ (jointGen A χ) ≤ 1 ∧ (jointGen A χ ≠ ⊥ → χ ∈ Set.range μ) := by
    intro χ
    by_cases hχ : χ ∈ (finite_jointGen A hA).toFinset
    · have h := hkey χ (hsub hχ)
      by_cases hr : χ ∈ Set.range μ
      · rw [if_pos hr] at h
        have : Module.finrank ℂ (jointGen A χ) = 1 := by exact_mod_cast h
        exact ⟨this.le, fun _ => hr⟩
      · rw [if_neg hr] at h
        have h0 : Module.finrank ℂ (jointGen A χ) = 0 := by exact_mod_cast h
        exact ⟨by omega, fun hne => absurd (Submodule.finrank_eq_zero.1 h0) hne⟩
    · have : jointGen A χ = ⊥ := by simpa using hχ
      have h0 : Module.finrank ℂ (jointGen A χ) = 0 := Submodule.finrank_eq_zero.2 this
      exact ⟨by omega, fun hne => absurd this hne⟩
  have hmem : ∀ ν v, IsJointEigenvector A ν v → v ∈ jointGen A ν := by
    intro ν v h
    simp only [jointGen, Submodule.mem_iInf]
    exact fun i => Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 (h i))
  have hdiag : ∀ χ, ∀ x ∈ jointGen A χ, IsJointEigenvector A χ x := by
    intro χ x hx i
    have hx' : x ∈ (A i).maxGenEigenspace (χ i) := by
      simp only [jointGen, Submodule.mem_iInf] at hx; exact hx i
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hx'
    have hg : MapsTo (A i - χ i • (1 : Module.End ℂ V)) (jointGen A χ) (jointGen A χ) := by
      intro y hy
      simp only [SetLike.mem_coe] at hy ⊢
      have := mapsTo_jointGen A hA χ i hy
      simp only [SetLike.mem_coe] at this
      simpa using (jointGen A χ).sub_mem this ((jointGen A χ).smul_mem (χ i) hy)
    have := eq_zero_of_finrank_le_one _ _ hg (hfr χ).1 x hx ⟨k, hk⟩
    simpa [sub_eq_zero] using this
  refine ⟨?_, ?_, ?_⟩
  · intro ν v w hv hw hv0
    exact exists_smul_of_finrank_le_one _ (hfr ν).1 v w (hmem ν v hv) (hmem ν w hw) hv0
  · intro ν v hv hv0
    refine (hfr ν).2 fun h => hv0 ?_
    have := hmem ν v hv
    rw [h] at this
    simpa using this
  · refine eq_top_iff.2 (le_of_eq_of_le (iSup_jointGen A hA).symm (iSup_le fun χ x hx => ?_))
    exact Submodule.subset_span ⟨χ, hdiag χ x hx⟩

end Final

end ModularFormsKB.HalfIntegral
