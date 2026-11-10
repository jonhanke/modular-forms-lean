import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Algebra.ProperAction.CompactlyGenerated
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.Data.ZMod.QuotientGroup
import ModularFormsKB.Citation
/-!
# Miyake §1.5: discrete subgroups and proper discontinuity

Miyake, *Modular Forms* (Springer 1989), §1.5, pp. 17–20.

* Theorem 1.5.2: let `G` and `X` be as in Theorem 1.2.1 (a locally compact group with a
  countable basis acting continuously and transitively on a nonempty locally compact Hausdorff
  space), and suppose all stabilizers `G_x` are compact. Then a subgroup `Γ` of `G` is discrete
  if and only if it acts properly discontinuously on `X`
  (`ModularFormsKB.Miyake.discreteTopology_iff_properlyDiscontinuousSMul`).
  "Properly discontinuous" is Mathlib's `ProperlyDiscontinuousSMul`, which is Miyake's
  second (compact-set) formulation: `#{γ ∈ Γ | γ A ∩ B ≠ ∅} < ∞` for compact `A, B`.
  The hypothesis that `X` is nonempty is implicit in Miyake (for empty `X` every subgroup acts
  properly discontinuously).
* Example 1.5.1: for `α ∈ SL₂(ℝ)` the cyclic group `⟨α⟩` is discrete if `α` is parabolic or
  hyperbolic; if `α` is elliptic, `⟨α⟩` is discrete only when `α` has finite order
  (`ModularFormsKB.Miyake.discreteTopology_zpowers_of_isParabolic_or_isHyperbolic`,
  `ModularFormsKB.Miyake.discreteTopology_zpowers_iff_of_isElliptic`).

## Proofs
Theorem 1.5.2 follows Miyake: (1) ⇒ (2) shows that `{g | g x ∈ A}` is compact for compact `A`
(it lies in finitely many compact sets `C_ν G_x`, using that the orbit map is open by
Theorem 1.2.1), so the action of `G` is proper and a discrete (hence closed) subgroup acts
properly discontinuously; (2) ⇒ (1) uses a neighbourhood `V` of `1` with compact closure:
`Γ ∩ V ⊆ {γ | γ x ∈ V x}` is finite.

Example 1.5.1 is stated without proof in Miyake. Here: for hyperbolic `α` the traces satisfy
`|tr αⁿ| ≥ |tr α| > 2` for `n ≠ 0`; for parabolic `α = s (1 + N)` with `s = ±1`, `N² = 0`,
`N ≠ 0`, so `αⁿ = sⁿ (1 + n N)`; for elliptic `α` the group `⟨α⟩` fixes the fixed point of `α`
in `ℍ`, whose stabilizer is compact.
-/

open MulAction Topology Matrix Filter
open scoped MatrixGroups Pointwise

namespace ModularFormsKB.Miyake

section General

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [MulAction G X] [ContinuousSMul G X] [IsPretransitive G X]

/-- In the setting of Theorem 1.2.1, if the stabilizer of `x` is compact then the orbit map
`g ↦ g x` is proper: `{g | g x ∈ A}` is compact for compact `A` (Miyake's proof of
Theorem 1.5.2, (1) ⇒ (2)). -/
theorem isProperMap_smul_of_isCompact_stabilizer (x : X)
    (hK : IsCompact (stabilizer G x : Set G)) : IsProperMap fun g : G => g • x := by
  have hcont : Continuous fun g : G => g • x := continuous_id.smul continuous_const
  refine isProperMap_iff_isCompact_preimage.2 ⟨hcont, fun A hA => ?_⟩
  have hopen : IsOpenMap fun g : G => g • x := isOpenMap_smul_of_sigmaCompact x
  choose C hCc hCg using fun g : G => exists_compact_mem_nhds g
  have hcover : A ⊆ ⋃ g : G, (fun h : G => h • x) '' interior (C g) := by
    intro a _
    obtain ⟨g, rfl⟩ := exists_smul_eq G x a
    exact Set.mem_iUnion.2 ⟨g, g, mem_interior_iff_mem_nhds.2 (hCg g), rfl⟩
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover _ (fun g => hopen _ isOpen_interior) hcover
  have hsub : (fun g : G => g • x) ⁻¹' A ⊆ ⋃ c ∈ t, C c * (stabilizer G x : Set G) := by
    intro g hg
    have hg' := ht hg
    simp only [Set.mem_iUnion, Set.mem_image] at hg'
    obtain ⟨c, hct, h, hh, hhx⟩ := hg'
    refine Set.mem_iUnion₂.2 ⟨c, hct, h, interior_subset hh, h⁻¹ * g, ?_, by simp⟩
    rw [SetLike.mem_coe, mem_stabilizer_iff, mul_smul, ← hhx, inv_smul_smul]
  exact (t.isCompact_biUnion fun c _ => (hCc c).mul hK).of_isClosed_subset
    (hA.isClosed.preimage hcont) hsub

/-- **Miyake, Theorem 1.5.2.** With `G` and `X` as in Theorem 1.2.1 (`X` nonempty) and all
stabilizers compact, a subgroup `Γ` of `G` is discrete if and only if it acts properly
discontinuously on `X`. -/
@[kb "miyake1989" "Theorem 1.5.2, p. 17"]
theorem discreteTopology_iff_properlyDiscontinuousSMul [T2Space G] [Nonempty X]
    (hstab : ∀ x : X, IsCompact (stabilizer G x : Set G)) (Γ : Subgroup G) :
    DiscreteTopology Γ ↔ ProperlyDiscontinuousSMul Γ X := by
  obtain ⟨x⟩ := ‹Nonempty X›
  constructor
  · intro hΓ
    haveI : ProperSMul G X :=
      MulAction.properSMul_of_proper_orbitMap (isProperMap_smul_of_isCompact_stabilizer x (hstab x))
    haveI : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discreteTopology
    rw [properlyDiscontinuousSMul_iff_properSMul]
    infer_instance
  · intro hpd
    obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
    have hcont : Continuous fun g : G => g • x := continuous_id.smul continuous_const
    have hfin := hpd.finite_disjoint_inter_image (isCompact_singleton (x := x)) (hVc.image hcont)
    have hfin' : Set.Finite {γ : Γ | (γ : G) ∈ V} := hfin.subset fun γ hγ =>
      ⟨γ • x, ⟨x, rfl, rfl⟩, γ, hγ, rfl⟩
    have hF : (((↑) : Γ → G) '' ({γ : Γ | (γ : G) ∈ V} \ {1})).Finite :=
      (hfin'.diff).image _
    apply discreteTopology_of_isOpen_singleton_one
    have : ({1} : Set Γ) =
        ((↑) : Γ → G) ⁻¹' (interior V \ ((↑) : Γ → G) '' ({γ : Γ | (γ : G) ∈ V} \ {1})) := by
      ext γ
      constructor
      · rintro rfl
        refine ⟨mem_interior_iff_mem_nhds.2 hV1, ?_⟩
        rintro ⟨γ', ⟨-, hγ'⟩, h⟩
        exact hγ' (Subtype.ext h)
      · rintro ⟨hi, hnF⟩
        by_contra hne
        exact hnF ⟨γ, ⟨(interior_subset (s := V) hi : (γ : G) ∈ V), hne⟩, rfl⟩
    rw [this]
    exact (isOpen_interior.sdiff hF.isClosed).preimage continuous_subtype_val

end General

/-! ### Example 1.5.1 -/

section Example

/-- A cyclic subgroup `⟨α⟩` is discrete as soon as some open neighbourhood of `1` contains no
power `αⁿ ≠ 1`. -/
lemma discreteTopology_zpowers_of_isOpen {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (α : G) (U : Set G) (hU : IsOpen U) (h1 : (1 : G) ∈ U)
    (h : ∀ n : ℤ, α ^ n ∈ U → α ^ n = 1) : DiscreteTopology (Subgroup.zpowers α) := by
  apply discreteTopology_of_isOpen_singleton_one
  have : ({1} : Set (Subgroup.zpowers α)) = ((↑) : Subgroup.zpowers α → G) ⁻¹' U := by
    ext ⟨γ, hγ⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hγ
    constructor
    · intro hγ1
      have : α ^ n = 1 := congrArg Subtype.val hγ1
      simpa [this] using h1
    · intro hU'
      exact Subtype.ext (h n hU')
  rw [this]
  exact hU.preimage continuous_subtype_val

/-- Cayley–Hamilton for `SL₂`: `α² = (tr α) α - 1`. -/
lemma sq_eq_trace_smul_sub_one (α : SL(2, ℝ)) :
    ((α : Matrix (Fin 2) (Fin 2) ℝ)) ^ 2 =
      (α : Matrix (Fin 2) (Fin 2) ℝ).trace • (α : Matrix (Fin 2) (Fin 2) ℝ) - 1 := by
  have hdet := α.det_coe
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;> linarith

/-- The trace of an inverse in `SL₂` is the trace. -/
lemma trace_inv (α : SL(2, ℝ)) :
    ((α⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace = (α : Matrix (Fin 2) (Fin 2) ℝ).trace := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.trace_fin_two,
    Matrix.trace_fin_two]
  simp [add_comm]

/-- Trace recursion `tr α^{n+2} = tr α · tr α^{n+1} - tr αⁿ`. -/
lemma trace_pow_add_two (α : SL(2, ℝ)) (n : ℕ) :
    ((α ^ (n + 2) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace =
      (α : Matrix (Fin 2) (Fin 2) ℝ).trace *
          ((α ^ (n + 1) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace -
        ((α ^ n : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace := by
  set A := (α : Matrix (Fin 2) (Fin 2) ℝ)
  have hA : ((α ^ (n + 2) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = A ^ n * A ^ 2 := by
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_add]
  have hA1 : ((α ^ (n + 1) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = A ^ n * A := by
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_succ]
  rw [hA, hA1, Matrix.SpecialLinearGroup.coe_pow, sq_eq_trace_smul_sub_one, Matrix.mul_sub,
    Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]

/-- For hyperbolic `α ∈ SL₂(ℝ)`, `|tr α| ≤ |tr αⁿ|` for every `n ≥ 1`. -/
lemma abs_trace_le_abs_trace_pow (α : SL(2, ℝ)) (ht : 2 ≤ |(α : Matrix (Fin 2) (Fin 2) ℝ).trace|)
    (n : ℕ) :
    |((α ^ n : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace| ≤
        |((α ^ (n + 1) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace| ∧
      |(α : Matrix (Fin 2) (Fin 2) ℝ).trace| ≤
        |((α ^ (n + 1) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace| := by
  set t := (α : Matrix (Fin 2) (Fin 2) ℝ).trace
  induction n with
  | zero =>
    simp only [pow_zero, Matrix.SpecialLinearGroup.coe_one, Matrix.trace_one, zero_add, pow_one,
      Fintype.card_fin]
    norm_num
    exact ⟨ht, le_rfl⟩
  | succ n ih =>
    have hrec := trace_pow_add_two α n
    set a := ((α ^ n : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace
    set b := ((α ^ (n + 1) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace
    set c := ((α ^ (n + 1 + 1) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace
    have hc : c = t * b - a := hrec
    have key : |b| ≤ |c| := by
      have h1 : |t * b| ≤ |c| + |a| := by
        calc |t * b| = |c + a| := by rw [hc]; ring_nf
          _ ≤ |c| + |a| := abs_add_le _ _
      rw [abs_mul] at h1
      nlinarith [abs_nonneg b, ih.1]
    exact ⟨key, ih.2.trans key⟩

/-- **Miyake, Example 1.5.1 (parabolic and hyperbolic case).** For `α ∈ SL₂(ℝ)` parabolic or
hyperbolic, the cyclic group `⟨α⟩` is a discrete subgroup of `SL₂(ℝ)`. -/
@[kb "miyake1989" "Example 1.5.1, p. 20"]
theorem discreteTopology_zpowers_of_isParabolic_or_isHyperbolic (α : SL(2, ℝ))
    (hα : (α : Matrix (Fin 2) (Fin 2) ℝ).IsParabolic ∨
      (α : Matrix (Fin 2) (Fin 2) ℝ).IsHyperbolic) :
    DiscreteTopology (Subgroup.zpowers α) := by
  set A := (α : Matrix (Fin 2) (Fin 2) ℝ) with hAdef
  set t := A.trace with htdef
  have hdet : A.det = 1 := α.det_coe
  have hdiscr : A.discr = t ^ 2 - 4 := by
    rw [Matrix.discr_fin_two, hdet, ← htdef]; ring
  have htr_cont : Continuous fun g : SL(2, ℝ) => (g : Matrix (Fin 2) (Fin 2) ℝ).trace := by
    unfold Matrix.trace Matrix.diag; fun_prop
  rcases hα with ⟨hns, hd0⟩ | hhyp
  · -- parabolic: `α = s (1 + N)`, `s = ±1`, `N² = 0`, `N ≠ 0`
    have ht2 : t ^ 2 = 4 := by rw [hdiscr] at hd0; linarith
    obtain ⟨s, hs, hts⟩ : ∃ s : ℝ, s ^ 2 = 1 ∧ t = 2 * s := by
      have : (t - 2) * (t + 2) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.1 this with h | h
      · exact ⟨1, by norm_num, by linarith⟩
      · exact ⟨-1, by norm_num, by linarith⟩
    set N : Matrix (Fin 2) (Fin 2) ℝ := s • A - 1 with hNdef
    have hA : A = s • (1 + N) := by
      rw [hNdef, add_sub_cancel, smul_smul, ← sq, hs, one_smul]
    have hN2 : N * N = 0 := by
      have hCH := sq_eq_trace_smul_sub_one α
      rw [← hAdef, ← htdef, hts] at hCH
      have e : N * N = s ^ 2 • (A * A) - (2 * s) • A + 1 := by
        rw [hNdef]
        simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
          Matrix.mul_one]
        module
      rw [e, ← sq A, hCH, hs, one_smul]
      module
    have hN0 : N ≠ 0 := by
      intro h0
      apply hns
      refine ⟨s, ?_⟩
      rw [hA, h0, add_zero]
      ext i j
      simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
    have htrN : N.trace = 0 := by
      rw [hNdef, Matrix.trace_sub, Matrix.trace_smul, ← htdef, hts, Matrix.trace_one]
      simp only [Fintype.card_fin, smul_eq_mul]
      norm_num
      linear_combination 2 * hs
    clear_value N
    -- powers: `αⁿ = sⁿ (1 + n N)`
    have hpow : ∀ n : ℤ, ((α ^ n : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
        (s ^ n) • (1 + (n : ℝ) • N) := by
      have hinv : ((α⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = s • (1 - N) := by
        have h1 : ((α⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) * A = 1 := by
          rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
            Matrix.SpecialLinearGroup.coe_one]
        have h2 : (s • (1 - N)) * A = 1 := by
          rw [hA, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← sq, hs, one_smul, sub_mul,
            Matrix.one_mul, mul_add, Matrix.mul_one, hN2]
          abel
        have hAinv : IsUnit A := by
          rw [Matrix.isUnit_iff_isUnit_det, hdet]; exact isUnit_one
        exact (hAinv.mul_left_inj).1 (h1.trans h2.symm)
      intro n
      induction n using Int.induction_on with
      | zero => simp
      | succ n ih =>
        rw [_root_.zpow_add_one, Matrix.SpecialLinearGroup.coe_mul, ih, ← hAdef, hA, zpow_add_one₀
          (by rintro rfl; norm_num at hs), Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        congr 1
        simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one,
          Matrix.smul_mul, Matrix.mul_smul, hN2, smul_zero]
        push_cast
        module
      | pred n ih =>
        rw [_root_.zpow_sub_one, Matrix.SpecialLinearGroup.coe_mul, ih, hinv, zpow_sub_one₀
          (by rintro rfl; norm_num at hs), Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        have hsinv : s⁻¹ = s := by
          have : s * s = 1 := by rw [← sq, hs]
          exact inv_eq_of_mul_eq_one_right this
        rw [hsinv]
        congr 1
        simp only [add_mul, mul_add, sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one,
          Matrix.smul_mul, Matrix.mul_smul, hN2, smul_zero]
        push_cast
        module
    -- an entry of `N` that is nonzero
    obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hN0 (Matrix.ext hcon)
    refine discreteTopology_zpowers_of_isOpen α
      {g | |(g : Matrix (Fin 2) (Fin 2) ℝ).trace - 2| < 2 ∧
        |(g : Matrix (Fin 2) (Fin 2) ℝ) i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| < |N i j|}
      ?_ ?_ ?_
    · have hent : Continuous fun g : SL(2, ℝ) => (g : Matrix (Fin 2) (Fin 2) ℝ) i j :=
        (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
      exact (isOpen_lt ((htr_cont.sub continuous_const).abs) continuous_const).inter
        (isOpen_lt ((hent.sub continuous_const).abs) continuous_const)
    · simp only [Set.mem_setOf_eq, Matrix.SpecialLinearGroup.coe_one, Matrix.trace_one,
        Fintype.card_fin, sub_self, abs_zero]
      exact ⟨by norm_num, abs_pos.2 hij⟩
    · intro n ⟨htn, hentn⟩
      rw [hpow n] at htn hentn
      have hsn : s ^ n = 1 ∨ s ^ n = -1 := by
        have hs' : (s - 1) * (s + 1) = 0 := by linear_combination hs
        rcases mul_eq_zero.1 hs' with h | h
        · left; rw [show s = 1 by linarith, _root_.one_zpow]
        · rw [show s = -1 by linarith]
          exact (Int.even_or_odd n).imp (fun he => he.neg_one_zpow) (fun ho => ho.neg_one_zpow)
      rcases hsn with h1 | h1
      · rw [h1, one_smul] at hentn
        have : n = 0 := by
          by_contra hn
          simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_sub_cancel_left,
            abs_mul] at hentn
          have : (1 : ℝ) ≤ |(n : ℝ)| := by
            rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
          nlinarith [abs_nonneg (N i j)]
        rw [this, zpow_zero]
      · exfalso
        rw [h1, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul, htrN, Matrix.trace_one]
          at htn
        simp only [Fintype.card_fin, smul_eq_mul] at htn
        norm_num at htn
  · -- hyperbolic: `|tr αⁿ| ≥ |tr α| > 2` for `n ≠ 0`
    have ht : 2 < |t| := by
      rw [Matrix.IsHyperbolic, hdiscr] at hhyp
      have : (2 : ℝ) ^ 2 < |t| ^ 2 := by rw [sq_abs]; linarith
      exact (pow_lt_pow_iff_left₀ (by norm_num) (abs_nonneg _) (by norm_num)).1 this
    refine discreteTopology_zpowers_of_isOpen α
      {g | |(g : Matrix (Fin 2) (Fin 2) ℝ).trace| < |t|} (isOpen_lt htr_cont.abs continuous_const)
      (by simpa using ht) ?_
    intro n hn
    by_contra hne
    have hn0 : n ≠ 0 := by rintro rfl; exact hne (zpow_zero α)
    have hn' : |((α ^ n : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace| < |t| := hn
    apply (lt_irrefl |t|)
    refine lt_of_le_of_lt ?_ hn'
    obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg n
    · subst hm
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
      rw [zpow_natCast]
      exact (abs_trace_le_abs_trace_pow α ht.le k).2
    · subst hm
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
      rw [_root_.zpow_neg, zpow_natCast, trace_inv]
      exact (abs_trace_le_abs_trace_pow α ht.le k).2

/-- **Miyake, Example 1.5.1 (elliptic case).** For `α ∈ SL₂(ℝ)` elliptic, the cyclic group
`⟨α⟩` is discrete if and only if `α` has finite order. -/
@[kb "miyake1989" "Example 1.5.1, p. 20"]
theorem discreteTopology_zpowers_iff_of_isElliptic (α : SL(2, ℝ))
    (hα : (α : Matrix (Fin 2) (Fin 2) ℝ).IsElliptic) :
    DiscreteTopology (Subgroup.zpowers α) ↔ IsOfFinOrder α := by
  constructor
  · intro hd
    -- `⟨α⟩` fixes the fixed point `z` of `α`, whose stabilizer is compact
    set g : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ α
    have hg : (g : Matrix (Fin 2) (Fin 2) ℝ).IsElliptic := hα
    set z : UpperHalfPlane := UpperHalfPlane.fixedPt g hg
    have hαz : α • z = z := by
      have : g • z = z :=
        (UpperHalfPlane.gl_smul_eq_self_iff_eq_fixedPt (by simp [g]) hg).2 rfl
      exact this
    have hcomp : IsCompact {γ : SL(2, ℝ) | (γ • ({z} : Set UpperHalfPlane) ∩ {z}).Nonempty} :=
      ProperSMul.isCompact_setOfPred_inter_nonempty isCompact_singleton isCompact_singleton
    have hsub : (Subgroup.zpowers α : Set SL(2, ℝ)) ⊆
        {γ : SL(2, ℝ) | (γ • ({z} : Set UpperHalfPlane) ∩ {z}).Nonempty} := by
      intro γ hγ
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hγ
      have : α ^ n • z = z := by
        rw [← MulAction.mem_stabilizer_iff]
        exact Subgroup.zpow_mem _ (MulAction.mem_stabilizer_iff.2 hαz) n
      exact ⟨z, ⟨z, rfl, this⟩, rfl⟩
    have hclosed : IsClosed (Subgroup.zpowers α : Set SL(2, ℝ)) :=
      Subgroup.isClosed_of_discreteTopology
    have hc : IsCompact (Subgroup.zpowers α : Set SL(2, ℝ)) := hcomp.of_isClosed_subset hclosed hsub
    haveI : CompactSpace (Subgroup.zpowers α) := isCompact_iff_compactSpace.1 hc
    haveI : Finite (Subgroup.zpowers α) := finite_of_compact_of_discrete
    exact finite_zpowers.1 inferInstance
  · intro hfin
    haveI : Finite (Subgroup.zpowers α) := finite_zpowers.2 hfin
    infer_instance

end Example

end ModularFormsKB.Miyake
