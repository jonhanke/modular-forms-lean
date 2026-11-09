import ModularFormsKB.Milne.Ch10.FrobeniusTwist
import ModularFormsKB.Milne.Ch10.FunctionFieldBridge
import TauCeti.FieldTheory.FunctionField.Frobenius

/-!
# Milne, Proposition 10.2: $\Pi_q$ is purely inseparable of degree $q$

Let $k$ be algebraically closed of characteristic $p$, $q = p^n$, and $C$ an integral curve over $k$ with function
field $K$. Composing $\Pi_q : C \to C^{(q)}$ with the isomorphism $C^{(q)} \cong C$ (`isIso_frobeniusTwist_fst`)
gives the $n$-fold absolute Frobenius of $C$ (`frobeniusMap_fst`), whose map on function fields is
$x \mapsto x^{q}$. Hence $\Pi_q^*$ identifies $k(C^{(q)})$ with $K^q$: the extension $K/\Pi_q^*k(C^{(q)})$ is
purely inseparable ($x^q$ lies in the image) of degree $[K : K^q] = q$ (Tau Ceti's
`TauCeti.IsFunctionField.finrank_fieldRange_frobenius` for $[K : K^p] = p$, iterated in the tower
$K \supseteq K^p \supseteq \dots \supseteq K^{p^n}$; $K$ is a Tau Ceti function field by
`isFunctionField_functionField`).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace ModularFormsKB.Milne

section FieldTheory

open Module


section
variable {k K : Type*} [Field k] [Field K] [Algebra k K] (p : ℕ) [ExpChar K p]

theorem fieldRange_succ_le (n : ℕ) :
    (iterateFrobenius K p (n + 1)).fieldRange ≤ (iterateFrobenius K p n).fieldRange := by
  rintro _ ⟨x, rfl⟩
  refine ⟨x ^ p, ?_⟩
  simp only [iterateFrobenius_def, ← pow_mul, pow_succ, mul_comm]

/-- The ring equivalence `R_1 ≃ R_{n+1}` given by `x ↦ x ^ p ^ n`. -/
noncomputable def powEquivRange (n : ℕ) :
    (iterateFrobenius K p 1).fieldRange ≃+* (iterateFrobenius K p (n + 1)).fieldRange := by
  refine RingEquiv.ofBijective
    (((iterateFrobenius K p n).comp (iterateFrobenius K p 1).fieldRange.subtype).codRestrict
      (iterateFrobenius K p (n + 1)).fieldRange ?_) ⟨?_, ?_⟩
  · rintro ⟨_, x, rfl⟩
    refine ⟨x, ?_⟩
    simp [iterateFrobenius_def, frobenius_def, ← pow_mul, pow_succ']
  · intro a b h
    apply Subtype.ext
    apply (iterateFrobenius K p n).injective
    exact congrArg Subtype.val h
  · rintro ⟨_, x, rfl⟩
    refine ⟨⟨x ^ p, x, by simp [frobenius_def]⟩, ?_⟩
    apply Subtype.ext
    simp [iterateFrobenius_def, ← pow_mul, pow_succ']

theorem finrank_iterateFrobenius_fieldRange [PerfectField k] (hF : TauCeti.IsFunctionField k K)
    (n : ℕ) : Module.finrank (iterateFrobenius K p n).fieldRange K = p ^ n := by
  induction n with
  | zero =>
    have h : Module.finrank (iterateFrobenius K p 0).fieldRange K = Module.finrank K K :=
      Algebra.finrank_eq_of_equiv_equiv
        (iterateFrobenius K p 0).rangeRestrictFieldEquiv.symm (RingEquiv.refl K) (by
          ext x
          have h := congrArg Subtype.val
            ((iterateFrobenius K p 0).rangeRestrictFieldEquiv.apply_symm_apply x)
          rw [RingHom.rangeRestrictFieldEquiv_apply_coe, iterateFrobenius_def] at h
          simp only [pow_zero, pow_one] at h
          exact h)
    rw [h, Module.finrank_self, pow_zero]
  | succ n ih =>
    let : Algebra (iterateFrobenius K p (n + 1)).fieldRange (iterateFrobenius K p n).fieldRange :=
      (Subfield.inclusion (fieldRange_succ_le p n)).toAlgebra
    have : IsScalarTower (iterateFrobenius K p (n + 1)).fieldRange
        (iterateFrobenius K p n).fieldRange K :=
      IsScalarTower.of_algebraMap_eq (fun x => rfl)
    have h1 := Module.finrank_mul_finrank (iterateFrobenius K p (n + 1)).fieldRange
      (iterateFrobenius K p n).fieldRange K
    have h2 : Module.finrank (iterateFrobenius K p (n + 1)).fieldRange
        (iterateFrobenius K p n).fieldRange = p := by
      have h3 : Module.finrank (iterateFrobenius K p 1).fieldRange K =
          Module.finrank (iterateFrobenius K p (n + 1)).fieldRange
            (iterateFrobenius K p n).fieldRange :=
        Algebra.finrank_eq_of_equiv_equiv (powEquivRange p n)
          (iterateFrobenius K p n).rangeRestrictFieldEquiv (by
            ext x
            rfl)
      rw [← h3, iterateFrobenius_one]
      exact hF.finrank_fieldRange_frobenius p
    rw [← h1, h2, ih, pow_succ, mul_comm]
end

end FieldTheory

section Geometry

theorem functionFieldMap_congr {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    {φ ψ : X ⟶ Y} [IsDominant φ] [IsDominant ψ] (h : φ = ψ) :
    functionFieldMap φ = functionFieldMap ψ := by
  subst h
  rfl

theorem functionFieldMap_comp {X Y Z : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    [IrreducibleSpace Z] (φ : X ⟶ Y) (ψ : Y ⟶ Z) [IsDominant φ] [IsDominant ψ]
    [IsDominant (φ ≫ ψ)] :
    functionFieldMap (φ ≫ ψ) = functionFieldMap ψ ≫ functionFieldMap φ := by
  unfold functionFieldMap
  rw [Scheme.Hom.stalkMap_comp]
  simp only [Category.assoc]
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_assoc ψ (φ (genericPoint X)) (genericPoint Y)
    (specializes_genericPoint_of_isDominant φ)]
  rw [TopCat.Presheaf.stalkSpecializes_comp_assoc]
  rfl

variable {p : ℕ} [Fact p.Prime] {C : Scheme.{u}} (hX : (p : Γ(C, ⊤)) = 0)

instance surjective_frobenius' : Surjective (C.frobenius p hX) :=
  ⟨fun x => ⟨x, Scheme.frobenius_apply hX x⟩⟩

instance surjective_iterateFrobenius' (n : ℕ) : Surjective (C.iterateFrobenius p hX n) :=
  ⟨fun x => ⟨x, Scheme.iterateFrobenius_apply hX n x⟩⟩


theorem functionFieldMap_frobenius [IrreducibleSpace C] (y : C.functionField) :
    (functionFieldMap (C.frobenius p hX)).hom y = y ^ p := by
  obtain ⟨U, hxU, s, rfl⟩ := C.presheaf.exists_germ_eq y
  unfold functionFieldMap
  rw [CommRingCat.comp_apply]
  have h1 : C.presheaf.stalkSpecializes (specializes_genericPoint_of_isDominant (C.frobenius p hX))
      = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
  rw [h1]
  show ((C.frobenius p hX).stalkMap (genericPoint C)).hom
    (C.presheaf.germ U (C.frobenius p hX (genericPoint C)) hxU s) = _
  refine (Scheme.Hom.germ_stalkMap_apply (C.frobenius p hX) U _ hxU s).trans ?_
  rw [Scheme.Hom.app_eq_appLE, Scheme.frobenius_appLE_apply, map_pow]
  congr 1
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _


theorem functionFieldMap_id (X : Scheme.{u}) [IrreducibleSpace X] (y : X.functionField) :
    (functionFieldMap (𝟙 X)).hom y = y := by
  unfold functionFieldMap
  rw [CommRingCat.comp_apply]
  have h1 : X.presheaf.stalkSpecializes (specializes_genericPoint_of_isDominant (𝟙 X)) = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl _ _
  rw [h1, Scheme.Hom.stalkMap_id]
  rfl

theorem functionFieldMap_iterateFrobenius [IrreducibleSpace C] (n : ℕ) (y : C.functionField) :
    (functionFieldMap (C.iterateFrobenius p hX n)).hom y = y ^ p ^ n := by
  induction n generalizing y with
  | zero =>
    rw [functionFieldMap_congr (Scheme.iterateFrobenius_zero hX), functionFieldMap_id, pow_zero,
      pow_one]
  | succ n ih =>
    rw [functionFieldMap_congr (Scheme.iterateFrobenius_succ hX n), functionFieldMap_comp,
      CommRingCat.comp_apply, ih, functionFieldMap_frobenius, ← pow_mul, pow_succ']

end Geometry

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
  (hk : (p : Γ(Spec (CommRingCat.of k), ⊤)) = 0) {C : Scheme.{u}} (f : C ⟶ Spec (CommRingCat.of k))

/-- **$\Pi_q$ is purely inseparable of degree $q = p^n$.** -/
theorem frobeniusMap_isPurelyInseparable_degree [IsAlgClosed k] [IsIntegral C] (hf : IsCurve k f) (n : ℕ)
    [IsIntegral (frobeniusTwist k p hk f n)] [IsDominant (frobeniusMap k p hk f n)] :
    IsPurelyInseparableMorphism (frobeniusMap k p hk f n) ∧
      morphismDegree (frobeniusMap k p hk f n) = p ^ n := by
  haveI : CharP k p := charP_of_natCast_eq_zero k p hk
  haveI := isIso_frobeniusTwist_fst k p hk f n
  let e : frobeniusTwist k p hk f n ⟶ C :=
    pullback.fst f ((Spec (CommRingCat.of k)).iterateFrobenius p hk n)
  have hkey : ∀ z : C.functionField,
      (functionFieldMap (frobeniusMap k p hk f n)).hom ((functionFieldMap e).hom z) = z ^ p ^ n := by
    intro z
    have h := functionFieldMap_congr (φ := frobeniusMap k p hk f n ≫ e)
      (ψ := C.iterateFrobenius p (Scheme.natCast_eq_zero_of_hom f hk) n) (frobeniusMap_fst k p hk f n)
    rw [functionFieldMap_comp] at h
    exact (congrArg (fun g => g.hom z) h).trans (functionFieldMap_iterateFrobenius _ n z)
  have hbij : Function.Bijective (functionFieldMap e).hom := by
    refine ⟨(functionFieldMap e).hom.injective, fun w => ⟨(functionFieldMap (inv e)).hom w, ?_⟩⟩
    have h := functionFieldMap_congr (φ := e ≫ inv e) (ψ := 𝟙 _) (IsIso.hom_inv_id e)
    rw [functionFieldMap_comp] at h
    have h2 := congrArg (fun g => g.hom w) h
    exact h2.trans (functionFieldMap_id _ w)
  let E : C.functionField ≃+* (frobeniusTwist k p hk f n).functionField :=
    RingEquiv.ofBijective (functionFieldMap e).hom hbij
  letI : Algebra k C.functionField := (functionFieldAlgebraMap k f).toAlgebra
  have hF := isFunctionField_functionField k f hf
  haveI : ExpChar k p := ExpChar.prime Fact.out
  haveI : ExpChar C.functionField p :=
    expChar_of_injective_algebraMap (algebraMap k C.functionField).injective p
  have hdeg := finrank_iterateFrobenius_fieldRange (k := k) p hF n
  letI := functionFieldAlgebra (frobeniusMap k p hk f n)
  refine ⟨show IsPurelyInseparable (frobeniusTwist k p hk f n).functionField C.functionField from ?_,
    show Module.finrank (frobeniusTwist k p hk f n).functionField C.functionField = p ^ n from ?_⟩
  · haveI : ExpChar (frobeniusTwist k p hk f n).functionField p :=
      RingHom.expChar
        (algebraMap (frobeniusTwist k p hk f n).functionField C.functionField)
        (algebraMap (frobeniusTwist k p hk f n).functionField C.functionField).injective p
    rw [isPurelyInseparable_iff_pow_mem _ p]
    intro x
    exact ⟨n, E x, hkey x⟩
  · rw [← hdeg]
    symm
    refine Algebra.finrank_eq_of_equiv_equiv
      ((iterateFrobenius C.functionField p n).rangeRestrictFieldEquiv.symm.trans E)
      (RingEquiv.refl _) ?_
    ext r
    have h := congrArg Subtype.val
      ((iterateFrobenius C.functionField p n).rangeRestrictFieldEquiv.apply_symm_apply r)
    rw [RingHom.rangeRestrictFieldEquiv_apply_coe] at h
    exact (hkey _).trans h

end ModularFormsKB.Milne
