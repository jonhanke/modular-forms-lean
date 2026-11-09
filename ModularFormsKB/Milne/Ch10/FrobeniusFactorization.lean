import Mathlib.FieldTheory.PurelyInseparable.Exponent
import ModularFormsKB.Milne.Ch10.FrobeniusMain
import ModularFormsKB.Milne.Ch10.CurveFaithful

/-!
# Milne, Proposition 10.2: the factorization from Theorem 7.2

Let $\varphi : C \to C'$ be a purely inseparable morphism of degree $q = p^n$ of complete regular curves over an
algebraically closed field $k$. Then $\varphi^* k(C') \subseteq k(C)$ is an intermediate field over which $k(C)$ is
purely inseparable of degree $q$, so it contains $k(C)^q$ (every $x$ satisfies $x^{p^e} \in \varphi^*k(C')$ with
$p^e \le q$), and $[k(C) : k(C)^q] = q$ forces $\varphi^*k(C') = k(C)^q = \Pi_q^* k(C^{(q)})$. The resulting
$k$-isomorphism $k(C') \cong k(C^{(q)})$ compatible with $\varphi^*$ and $\Pi_q^*$ comes, by Theorem 7.2
(`CurveFunctionFieldEquivalence`: dominant $k$-morphisms of complete regular curves correspond to $k$-embeddings
of function fields), from an isomorphism $C^{(q)} \cong C'$ over $k$ with $\Pi_q \gg e = \varphi$.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace ModularFormsKB.Milne

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
  (hk : (p : Γ(Spec (CommRingCat.of k), ⊤)) = 0)

open Module
theorem pow_mem_range_of_finrank {F K : Type*} [Field F] [Field K] [Algebra F K] (p : ℕ) [Fact p.Prime]
    [ExpChar F p] [IsPurelyInseparable F K] (n : ℕ) (hn : Module.finrank F K = p ^ n) (x : K) :
    x ^ p ^ n ∈ (algebraMap F K).range := by
  haveI : FiniteDimensional F K := Module.finite_of_finrank_pos (by rw [hn]; exact pow_pos (Fact.out : p.Prime).pos _)
  have h1 := IsPurelyInseparable.minpoly_natDegree_eq' F p x
  have h2 : (minpoly F x).natDegree ≤ finrank F K := minpoly.natDegree_le x
  rw [h1, hn] at h2
  have he : IsPurelyInseparable.elemExponent F x ≤ n :=
    (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp h2
  have h3 := IsPurelyInseparable.elemExponent_def' (K := F) p x
  have : x ^ p ^ n = (x ^ p ^ IsPurelyInseparable.elemExponent F x) ^ p ^ (n - IsPurelyInseparable.elemExponent F x) := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' he]
  rw [this]
  exact Subring.pow_mem _ h3 _


theorem fieldRange_eq_iterateFrobenius {k F K : Type*} [Field k] [Field F] [Field K] [Algebra F K]
    [Algebra k K] [PerfectField k] (p : ℕ) [Fact p.Prime] [ExpChar K p] [ExpChar F p]
    (hF : TauCeti.IsFunctionField k K) [IsPurelyInseparable F K] (n : ℕ)
    (hn : Module.finrank F K = p ^ n) :
    (algebraMap F K).fieldRange = (iterateFrobenius K p n).fieldRange := by
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos _
  have hRL : (iterateFrobenius K p n).fieldRange ≤ (algebraMap F K).fieldRange := by
    rintro _ ⟨x, rfl⟩
    rw [iterateFrobenius_def]
    exact pow_mem_range_of_finrank p n hn x
  have hL : Module.finrank (algebraMap F K).fieldRange K = p ^ n := by
    rw [← hn]
    symm
    exact Algebra.finrank_eq_of_equiv_equiv (algebraMap F K).rangeRestrictFieldEquiv
      (RingEquiv.refl K) (by ext x; rfl)
  have hR := finrank_iterateFrobenius_fieldRange (k := k) p hF n
  let : Algebra (iterateFrobenius K p n).fieldRange (algebraMap F K).fieldRange :=
    (Subfield.inclusion hRL).toAlgebra
  have : IsScalarTower (iterateFrobenius K p n).fieldRange (algebraMap F K).fieldRange K :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  have h1 := Module.finrank_mul_finrank (iterateFrobenius K p n).fieldRange
    (algebraMap F K).fieldRange K
  rw [hL, hR] at h1
  have h2 : Module.finrank (iterateFrobenius K p n).fieldRange (algebraMap F K).fieldRange = 1 :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [one_mul]; exact h1)
  have h3 := (finrank_eq_one_iff_of_nonzero' (1 : (algebraMap F K).fieldRange)
    one_ne_zero).mp h2
  refine le_antisymm ?_ hRL
  intro l hl
  obtain ⟨c, hc⟩ := h3 ⟨l, hl⟩
  have : (c : K) = l := congrArg Subtype.val (by simpa [Algebra.smul_def] using hc)
  exact this ▸ c.2

theorem functionFieldMap_germ {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (φ : X ⟶ Y) [IsDominant φ]
    (s : Γ(Y, ⊤)) :
    (functionFieldMap φ).hom (Y.germToFunctionField ⊤ s) = X.germToFunctionField ⊤ (φ.appTop s) := by
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  haveI : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  unfold functionFieldMap
  rw [CommRingCat.comp_apply]
  have h1 : Y.presheaf.stalkSpecializes (specializes_genericPoint_of_isDominant φ)
      (Y.germToFunctionField ⊤ s) = Y.presheaf.germ ⊤ (φ (genericPoint X)) trivial s := by
    exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  rw [h1]
  exact Scheme.Hom.germ_stalkMap_apply φ ⊤ (genericPoint X) trivial s

theorem functionFieldMap_algebraMap (k : Type u) [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k)) (φ : X ⟶ Y) [IsDominant φ]
    (h : φ ≫ g = f) (c : k) :
    (functionFieldMap φ).hom (functionFieldAlgebraMap k g c) = functionFieldAlgebraMap k f c := by
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  haveI : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  subst h
  simp only [functionFieldAlgebraMap, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [functionFieldMap_germ]
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- **The factorization part of Proposition 10.2 from the full half of Theorem 7.2** (the faithful half is
`curveFunctionField_faithful`, proved). -/
theorem purelyInseparableFactorization_of_full [IsAlgClosed k] (hfull : CurveFunctionFieldFull.{u} k) :
    PurelyInseparableFactorization k p hk where
  factors := by
    intro C C' _ _ f f' hf hf' φ _ hφf hpi n hdeg
    haveI : CharP k p := charP_of_natCast_eq_zero k p hk
    haveI := isIntegral_frobeniusTwist k p hk f n
    haveI := isDominant_frobeniusMap k p hk f n
    obtain ⟨hTc, hTpi, hTdeg⟩ :=
      (frobeniusTwistCurveProperties_of k p hk (frobeniusTwistCurveDegree k p hk)).curve f hf n
    letI : Algebra k C.functionField := (functionFieldAlgebraMap k f).toAlgebra
    have hFun := isFunctionField_functionField k f hf.1
    haveI : ExpChar k p := ExpChar.prime Fact.out
    haveI : ExpChar C.functionField p :=
      expChar_of_injective_algebraMap (algebraMap k C.functionField).injective p
    -- ranges
    have hrφ : (functionFieldMap φ).hom.fieldRange = (iterateFrobenius C.functionField p n).fieldRange := by
      letI := functionFieldAlgebra φ
      haveI : IsPurelyInseparable C'.functionField C.functionField := hpi
      haveI : ExpChar C'.functionField p :=
        RingHom.expChar (algebraMap C'.functionField C.functionField)
          (algebraMap C'.functionField C.functionField).injective p
      exact fieldRange_eq_iterateFrobenius (k := k) p hFun n hdeg
    have hrP : (functionFieldMap (frobeniusMap k p hk f n)).hom.fieldRange =
        (iterateFrobenius C.functionField p n).fieldRange := by
      letI := functionFieldAlgebra (frobeniusMap k p hk f n)
      haveI : IsPurelyInseparable (frobeniusTwist k p hk f n).functionField C.functionField := hTpi
      haveI : ExpChar (frobeniusTwist k p hk f n).functionField p :=
        RingHom.expChar (algebraMap (frobeniusTwist k p hk f n).functionField C.functionField)
          (algebraMap (frobeniusTwist k p hk f n).functionField C.functionField).injective p
      exact fieldRange_eq_iterateFrobenius (k := k) p hFun n hTdeg
    have hrange := hrφ.trans hrP.symm
    let σ : C'.functionField ≃+* (frobeniusTwist k p hk f n).functionField :=
      (functionFieldMap φ).hom.rangeRestrictFieldEquiv.trans
        ((RingEquiv.subfieldCongr hrange).trans
          (functionFieldMap (frobeniusMap k p hk f n)).hom.rangeRestrictFieldEquiv.symm)
    have hσ : ∀ x, (functionFieldMap (frobeniusMap k p hk f n)).hom (σ x) = (functionFieldMap φ).hom x := by
      intro x
      have h := congrArg Subtype.val
        ((functionFieldMap (frobeniusMap k p hk f n)).hom.rangeRestrictFieldEquiv.apply_symm_apply
          (RingEquiv.subfieldCongr hrange ((functionFieldMap φ).hom.rangeRestrictFieldEquiv x)))
      rw [RingHom.rangeRestrictFieldEquiv_apply_coe] at h
      exact h
    have hcompat : ∀ c : k, σ (functionFieldAlgebraMap k f' c) =
        functionFieldAlgebraMap k (frobeniusTwistStructure k p hk f n) c := by
      intro c
      apply (functionFieldMap (frobeniusMap k p hk f n)).hom.injective
      rw [hσ, functionFieldMap_algebraMap k f f' φ hφf,
        functionFieldMap_algebraMap k f (frobeniusTwistStructure k p hk f n) _
          (frobeniusMap_comp k p hk f n)]
    have hcompat' : ∀ c : k, σ.symm (functionFieldAlgebraMap k (frobeniusTwistStructure k p hk f n) c) =
        functionFieldAlgebraMap k f' c := fun c => σ.symm_apply_eq.mpr (hcompat c).symm
    obtain ⟨e, he_dom, he_f, he_map⟩ := hfull.full (frobeniusTwistStructure k p hk f n) f' hTc hf'
      (CommRingCat.ofHom σ.toRingHom) hcompat
    obtain ⟨e', he'_dom, he'_f, he'_map⟩ := hfull.full f' (frobeniusTwistStructure k p hk f n) hf' hTc
      (CommRingCat.ofHom σ.symm.toRingHom) hcompat'
    haveI := he_dom
    haveI := he'_dom
    have hid : ∀ (X : Scheme.{u}) [IsIntegral X], functionFieldMap (𝟙 X) = 𝟙 _ := by
      intro X _
      ext y
      exact functionFieldMap_id X y
    have h1 : e ≫ e' = 𝟙 _ := by
      refine curveFunctionField_faithful k (frobeniusTwistStructure k p hk f n) (frobeniusTwistStructure k p hk f n) hTc hTc
        _ _ (by rw [Category.assoc, he'_f, he_f]) (by rw [Category.id_comp]) ?_
      rw [functionFieldMap_comp, hid, he_map, he'_map]
      ext y
      exact σ.apply_symm_apply y
    have h2 : e' ≫ e = 𝟙 _ := by
      refine curveFunctionField_faithful k f' f' hf' hf' _ _ (by rw [Category.assoc, he_f, he'_f]) (by rw [Category.id_comp]) ?_
      rw [functionFieldMap_comp, hid, he_map, he'_map]
      ext y
      exact σ.symm_apply_apply y
    refine ⟨⟨e, e', h1, h2⟩, he_f, ?_⟩
    refine curveFunctionField_faithful k f f' hf hf' _ _ (by rw [Category.assoc, he_f, frobeniusMap_comp]) hφf ?_
    rw [functionFieldMap_comp, he_map]
    ext y
    exact hσ y

/-- **The factorization part of Proposition 10.2 from Theorem 7.2.** -/
theorem purelyInseparableFactorization_of [IsAlgClosed k] (h72 : CurveFunctionFieldEquivalence.{u} k) :
    PurelyInseparableFactorization k p hk :=
  purelyInseparableFactorization_of_full k p hk (curveFunctionFieldFull_of_equivalence k h72)

/-- **Proposition 10.2 from the full half of Theorem 7.2** (`CurveFunctionFieldFull`, named statement): the only
input left. -/
theorem frobeniusFactorization_of_curveFunctionFieldFull [IsAlgClosed k]
    (hfull : CurveFunctionFieldFull.{u} k) : FrobeniusFactorization k p hk :=
  frobeniusFactorization_of_factorization k p hk (purelyInseparableFactorization_of_full k p hk hfull)

/-- **Proposition 10.2 from Theorem 7.2** (Milne; `CurveFunctionFieldEquivalence`, a Chapter 7 named statement). -/
theorem frobeniusFactorization_of_curveFunctionFieldEquivalence [IsAlgClosed k]
    (h72 : CurveFunctionFieldEquivalence.{u} k) : FrobeniusFactorization k p hk :=
  frobeniusFactorization_of_curveFunctionFieldFull k p hk (curveFunctionFieldFull_of_equivalence k h72)

end ModularFormsKB.Milne
