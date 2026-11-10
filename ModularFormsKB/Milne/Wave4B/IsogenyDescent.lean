import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Factorisation
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Kernel
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Differential
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing.Basis
import Mathlib.RingTheory.Localization.Integer

/-!
# Dividing an endomorphism by `ℓ`, with descent from the separable closure

Input for the corrected Remark 12.12 of J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`,
Section 12, pdf p. 125). The step in Serre–Tate's argument (and Silverman III.4.11) is: an endomorphism `φ` of an
elliptic curve `E` over a field `k` that kills `E[ℓ]` (over a separable closure, `ℓ` invertible in `k`) is `ℓ ψ` for an
endomorphism `ψ` **defined over `k`**.

Over the separable closure `kˢ` this is Tau Ceti's kernel form of the factorisation theorem
(`TauCeti.Isogeny.existsUnique_comp_eq_iff_ker_le`), for `φ` separable. The descent to `k` uses the subfield form
(`TauCeti.Isogeny.existsUnique_comp_eq_iff_fieldRange_le`): the inclusion of pulled-back function fields descends
along a field extension (`fieldRange_le_of_map`), because a basis of `k(E)` over `[ℓ]^* k(E)` stays linearly
independent over `[ℓ]^* kˢ(E)` (Tau Ceti's linear disjointness `WeierstrassCurve.Affine.FunctionField.linearIndependent_map`;
the argument is that of the private lemma `linearIndependent_functionFieldMap_basis` in Tau Ceti's
`Isogeny/BaseChange/Degree.lean`, reproduced here).

## Main results
* `fieldRange_le_of_map`: if `ψ_K^* K(W₃) ⊆ φ_K^* K(W₂)` after base change, then `ψ^* F(W₃) ⊆ φ^* F(W₂)`.
* `exists_eq_zsmul_of_torsion`: a separable endomorphism over `k` killing the `ℓ`-torsion over `kˢ` is `ℓ` times an
  endomorphism over `k`.
-/

open WeierstrassCurve.Affine
open scoped nonZeroDivisors

namespace ModularFormsKB.Milne.Wave4B

open TauCeti TauCeti.Isogeny

section Descent

variable {F K : Type*} [Field F] [Field K] {W₁ W₂ W₃ : WeierstrassCurve.Affine F}

/-- (Tau Ceti, `Isogeny/BaseChange/Degree.lean`, private there.) The pullback along `φ.map f` of a function of the
coordinate ring of `W₂⁄K`, in the monomial basis. -/
theorem fieldPullback_map_algebraMap' (φ : Isogeny W₁ W₂) (f : F →+* K)
    (z : (W₂.map f).CoordinateRing) :
    (φ.map f).fieldPullback (algebraMap _ _ z) =
      ((CoordinateRing.basisMonomials (W₂.map f)).repr z).sum fun j c ↦
        c • FunctionField.map W₁ f
          (φ.fieldPullback (algebraMap _ _ (CoordinateRing.basisMonomials W₂ j))) := by
  conv_lhs => rw [← (CoordinateRing.basisMonomials (W₂.map f)).linearCombination_repr z,
    Finsupp.linearCombination_apply]
  rw [Finsupp.sum, Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Algebra.smul_def, map_mul, map_mul, ← IsScalarTower.algebraMap_apply, AlgHom.commutes,
    Algebra.smul_def, ← CoordinateRing.map_basisMonomials,
    ← FunctionField.map_algebraMap_coordinateRing, map_fieldPullback_map]

/-- (Tau Ceti, private there.) The pulled-back monomials are linearly independent over `F`. -/
theorem linearIndependent_pulledBackMonomials' (φ : Isogeny W₁ W₂) :
    LinearIndependent F fun j : ℕ × Fin 2 ↦ (⟨φ.fieldPullback
      (algebraMap _ _ (CoordinateRing.basisMonomials W₂ j)), AlgHom.mem_fieldRange.2 ⟨_, rfl⟩⟩ :
        φ.fieldPullback.fieldRange) :=
  LinearIndependent.of_comp (φ.fieldPullback.fieldRange.val.toLinearMap) <|
    (CoordinateRing.basisMonomials W₂).linearIndependent.map' ((φ.fieldPullback.toLinearMap).comp
      (IsScalarTower.toAlgHom F W₂.CoordinateRing W₂.FunctionField).toLinearMap)
      (LinearMap.ker_eq_bot.2 (φ.fieldPullback.injective.comp
        (FaithfulSMul.algebraMap_injective _ _)))

/-- (Tau Ceti, `linearIndependent_functionFieldMap_basis`, private there.) The image of a basis of `F(W₁)` over
`φ^* F(W₂)` is linearly independent over `φ_K^* K(W₂)`. -/
theorem linearIndependent_functionFieldMap_basis' (φ : Isogeny W₁ W₂) (f : F →+* K)
    {ι : Type*} [Finite ι] (b : Module.Basis ι φ.fieldPullback.fieldRange W₁.FunctionField) :
    LinearIndependent (φ.map f).fieldPullback.fieldRange (FunctionField.map W₁ f ∘ b) := by
  classical
  have := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose h hh using fun i ↦ AlgHom.mem_fieldRange.1 (g i).2
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples (W₂.map f).CoordinateRing⁰
    Finset.univ h
  choose r hr using fun i ↦ hs i (Finset.mem_univ i)
  set B := CoordinateRing.basisMonomials W₂ with hB
  set B' := CoordinateRing.basisMonomials (W₂.map f) with hB'
  let m : ℕ × Fin 2 → φ.fieldPullback.fieldRange := fun j ↦
    ⟨φ.fieldPullback (algebraMap _ _ (B j)), AlgHom.mem_fieldRange.2 ⟨_, rfl⟩⟩
  have hK := FunctionField.linearIndependent_map W₁ f
    (linearIndependent_smul (linearIndependent_pulledBackMonomials' φ) b.linearIndependent)
  set T := Finset.univ.biUnion fun i ↦ (B'.repr (r i)).support
  have hT (i) : (B'.repr (r i)).support ⊆ T :=
    Finset.subset_biUnion_of_mem (fun i ↦ (B'.repr (r i)).support) (Finset.mem_univ i)
  have key : ∑ p ∈ T ×ˢ Finset.univ,
      B'.repr (r p.2) p.1 • FunctionField.map W₁ f (m p.1 • b p.2) = 0 := by
    have := congrArg
      ((φ.map f).fieldPullback (algebraMap _ _ (s : (W₂.map f).CoordinateRing)) * ·) hg
    simp only [mul_zero, Finset.mul_sum] at this
    rw [Finset.sum_product, Finset.sum_comm, ← this]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hgi : (φ.map f).fieldPullback (algebraMap _ _ (s : (W₂.map f).CoordinateRing)) *
        (g i : (W₁.map f).FunctionField) = (φ.map f).fieldPullback (algebraMap _ _ (r i)) := by
      rw [hr i, Algebra.smul_def, map_mul, hh]
    rw [Function.comp_apply, IntermediateField.smul_def, smul_eq_mul, ← mul_assoc, hgi,
      fieldPullback_map_algebraMap', ← hB, ← hB', Finsupp.sum_of_support_subset _ (hT i)
        (fun j c ↦ c • FunctionField.map W₁ f (m j)) (fun _ _ ↦ zero_smul _ _), Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [smul_mul_assoc, Algebra.smul_def (m j), map_mul, IntermediateField.algebraMap_apply]
  have hc := linearIndependent_iff'.1 hK _ _ key
  have hr0 : r i = 0 := by
    refine B'.repr.injective (Finsupp.ext fun j ↦ ?_)
    by_cases hj : j ∈ T
    · simpa using hc (j, i) (Finset.mk_mem_product hj (Finset.mem_univ i))
    · simpa using Finsupp.notMem_support_iff.1 fun h ↦ hj (hT i h)
  have hs0 : algebraMap (W₂.map f).CoordinateRing (W₂.map f).FunctionField s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hh0 : h i = 0 := by
    have := hr i
    rw [hr0, map_zero, Algebra.smul_def, eq_comm, mul_eq_zero] at this
    exact this.resolve_left hs0
  exact Subtype.ext (by rw [← hh, hh0, map_zero, ZeroMemClass.coe_zero])

/-- **Descent of the factorisation criterion.** If after a base change `f : F → K` the field pulled back along `ψ`
lies in the field pulled back along `φ`, then this already holds over `F`. -/
theorem fieldRange_le_of_map (φ : Isogeny W₁ W₂) (ψ : Isogeny W₁ W₃) (f : F →+* K)
    (h : (ψ.map f).fieldPullback.fieldRange ≤ (φ.map f).fieldPullback.fieldRange) :
    ψ.fieldPullback.fieldRange ≤ φ.fieldPullback.fieldRange := by
  classical
  set M := φ.fieldPullback.fieldRange
  set M' := (φ.map f).fieldPullback.fieldRange
  let b := Module.finBasis M W₁.FunctionField
  have hli := linearIndependent_functionFieldMap_basis' φ f b
  have hmapM : ∀ m : M, FunctionField.map W₁ f m ∈ M' := by
    rintro ⟨_, ⟨v, rfl⟩⟩
    exact ⟨FunctionField.map W₂ f v, map_fieldPullback_map φ f v⟩
  let mp : M → M' := fun m ↦ ⟨_, hmapM m⟩
  have hsum : ∀ x : W₁.FunctionField,
      FunctionField.map W₁ f x = ∑ i, (mp (b.repr x i) : (W₁.map f).FunctionField) *
        FunctionField.map W₁ f (b i) := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [IntermediateField.smul_def, smul_eq_mul, map_mul]
  rintro z ⟨w, rfl⟩
  have hZ : FunctionField.map W₁ f (ψ.fieldPullback w) ∈ M' :=
    h ⟨FunctionField.map W₃ f w, map_fieldPullback_map ψ f w⟩
  set Z : M' := ⟨_, hZ⟩
  set c := b.repr (ψ.fieldPullback w)
  set d := b.repr 1
  have hrel : ∑ i, (mp (c i) - Z * mp (d i)) • (FunctionField.map W₁ f ∘ b) i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, Function.comp_apply, IntermediateField.smul_def, smul_eq_mul]
    have h1 := hsum (ψ.fieldPullback w)
    have h2 := hsum 1
    rw [map_one] at h2
    simp only [IntermediateField.coe_mul, mul_assoc, ← Finset.mul_sum]
    rw [← h1, ← h2, mul_one, sub_self]
  have hcoef := (Fintype.linearIndependent_iff.1 hli) _ hrel
  -- some coordinate of `1` is nonzero
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra hne
    push_neg at hne
    have : (1 : W₁.FunctionField) = 0 := by
      rw [← b.sum_repr 1]
      simp [d, hne]
    exact one_ne_zero this
  have hci : FunctionField.map W₁ f (c i) = FunctionField.map W₁ f (ψ.fieldPullback w * d i) := by
    have h0 := hcoef i
    rw [sub_eq_zero] at h0
    have := congrArg Subtype.val h0
    rw [MulMemClass.coe_mul] at this
    rw [map_mul]
    exact this
  have hinj := (FunctionField.map W₁ f).injective hci
  have hdi : (d i : W₁.FunctionField) ≠ 0 := by exact_mod_cast hi
  have : ψ.fieldPullback w = (c i : W₁.FunctionField) / d i := by
    rw [hinj, mul_div_cancel_right₀ _ hdi]
  change ψ.fieldPullback w ∈ M
  rw [this]
  exact M.div_mem (c i).2 (d i).2

end Descent

section DivideByEll

variable {k Ks : Type*} [Field k] [Field Ks] [IsSepClosed Ks] [DecidableEq Ks] (f : k →+* Ks)
  {W : WeierstrassCurve.Affine k} [W.IsElliptic]

/-- `[n]` as an isogeny is `n` times the identity, also after base change. -/
theorem map_mulByIntIsogenyOfNeZero {n : ℤ} (hn : n ≠ 0) :
    (mulByIntIsogenyOfNeZero W hn).map f = mulByIntIsogenyOfNeZero (W.map f) hn :=
  Hom.ofIsogeny_injective <| by
    rw [← Hom.ofIsogeny_map, mulByIntIsogenyOfNeZero, mulByIntIsogenyOfNeZero, ofIsogeny_mulByIntIsogeny,
      ofIsogeny_mulByIntIsogeny, Hom.map_zsmul, Hom.id_map]

/-- **Dividing by `ℓ`** (Silverman III.4.11 with descent): let `φ` be an endomorphism of `E` over `k` that pulls the
invariant differential back to a nonzero differential (so `φ` is separable), and kills every `n`-torsion point of `E`
over the separably closed field `Ks ⊇ k`, where `n` is invertible in `Ks`. Then `φ = n • ψ` for an endomorphism `ψ`
of `E` over `k`. -/
theorem exists_eq_zsmul_of_torsion {n : ℤ} (hn : (n : Ks) ≠ 0) (φ : Hom W W)
    (hsep : φ.pullbackDifferential (invariantDifferential W) ≠ 0)
    (hφ : ∀ P : (W.map f).Point, n • P = 0 → (φ.map f).pointMap P = 0) :
    ∃ ψ : Hom W W, φ = n • ψ := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hφ0 : φ ≠ 0 := by rintro rfl; simp [Hom.pullbackDifferential_zero] at hsep
  set ψ := Hom.toIsogeny hφ0 with hψdef
  have hψ : Hom.ofIsogeny ψ = φ := Hom.ofIsogeny_toIsogeny hφ0
  set L := mulByIntIsogenyOfNeZero W hn0 with hL
  set LK := mulByIntIsogenyOfNeZero (W.map f) hn0 with hLK
  have hLmap : L.map f = LK := map_mulByIntIsogenyOfNeZero f hn0
  -- separability of `ψ` and of `[n]` over `Ks`
  have hsepψ : Algebra.IsSeparable ψ.fieldPullback.fieldRange W.FunctionField := by
    rw [isSeparable_iff_pullbackDifferential_ne_zero, ← Hom.pullbackDifferential_ofIsogeny, hψ]
    exact hsep
  have hsepψK : Algebra.IsSeparable (ψ.map f).fieldPullback.fieldRange (W.map f).FunctionField :=
    isSeparable_map ψ f
  have hsepL : Algebra.IsSeparable LK.fieldPullback.fieldRange (W.map f).FunctionField := by
    rw [isSeparable_iff_pullbackDifferential_ne_zero, ← Hom.pullbackDifferential_ofIsogeny, hLK,
      mulByIntIsogenyOfNeZero, ofIsogeny_mulByIntIsogeny, Hom.pullbackDifferential_zsmul_id_invariantDifferential]
    rw [Ne, zsmul_invariantDifferential_eq_zero_iff]
    exact hn
  -- `ker [n] ≤ ker ψ` over `Ks`
  have hker : LK.ker ≤ (ψ.map f).ker := by
    intro P hP
    obtain ⟨Q, rfl⟩ := (Point.equivBaseChangeSelf (W.map f)).surjective P
    rw [mem_ker_iff_toPointHom_eq_zero] at hP ⊢
    rw [← Hom.pointMap_ofIsogeny_eq_toPointHom] at hP
    rw [← Hom.pointMap_ofIsogeny_eq_toPointHom]
    rw [hLK, mulByIntIsogenyOfNeZero, ofIsogeny_mulByIntIsogeny, Hom.zsmul_pointMap, Hom.id_pointMap] at hP
    rw [← Hom.ofIsogeny_map, hψ]
    exact hφ Q hP
  have hcard : Nat.card LK.ker = LK.degree := card_ker_eq_degree LK
  obtain ⟨χK, hχK, -⟩ := (existsUnique_comp_eq_iff_ker_le hcard (ψ.map f)).2 hker
  have hleK : (ψ.map f).fieldPullback.fieldRange ≤ (L.map f).fieldPullback.fieldRange := by
    rw [hLmap]
    exact (existsUnique_comp_eq_iff_fieldRange_le LK (ψ.map f)).1 ⟨χK, hχK, fun χ' h' ↦
      comp_right_injective LK (h'.trans hχK.symm)⟩
  obtain ⟨χ, hχ, -⟩ := (existsUnique_comp_eq_iff_fieldRange_le L ψ).2 (fieldRange_le_of_map L ψ f hleK)
  refine ⟨Hom.ofIsogeny χ, ?_⟩
  rw [← hψ, ← hχ, ← Hom.ofIsogeny_comp_ofIsogeny, hL, mulByIntIsogenyOfNeZero, ofIsogeny_mulByIntIsogeny,
    Hom.comp_zsmul, Hom.comp_id]

end DivideByEll

end ModularFormsKB.Milne.Wave4B
