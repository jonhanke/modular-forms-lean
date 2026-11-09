import ModularFormsKB.Milne.Ch11.TwistBaseChange
import TauCeti.FieldTheory.FunctionField.SeparablyGenerated
import TauCeti.FieldTheory.FunctionField.Consequences.GenusZero
import Mathlib.FieldTheory.Normal.Closure

/-!
# The lower bound along multiples of the degree of the constant field of a Galois closure

For a function field $F/k$ ($k$ finite with $q$ elements, $k$ exact) choose a separating element $x$
(Tau Ceti, `exists_transcendental_and_isSeparable_adjoin_of_perfectField`), let $E$ be the normal closure of
$F/k(x)$ in an algebraic closure, and $k_1 = \mathbb F_{q^d}$ the constant field of $E$. Over $k_1$, $E$ is a
function field with exact constants, $\Gamma = \mathrm{Gal}(E/k_1(x))$ and $H = \mathrm{Gal}(E/F k_1)$ are finite
groups of $k_1$-automorphisms with $E^\Gamma = k_1(x)$ (genus $0$) and $E^H = F \cdot k_1$
(`fixedField_fixingSubgroup_of_isGalois`). Hence $N_n(F \cdot k_1) = N_{dn}(F)$
(`curvePointCount_constantCompositum`) and the even-degree bound for $E^H$ (`lowerBound_fixedField`) gives
**`hasseWeilLowerBoundMultiple`**, the lower bound $N_n(F) \ge q^n + 1 - C q^{n/2}$ for all large multiples $n$ of
$2d$ (Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., proof of Theorem 5.2.3 [unverified numbering]).
-/

open TauCeti Module IntermediateField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ModularFormsKB.Milne

universe u v

section Galois

variable {K k₁ E : Type*} [Field K] [Field k₁] [Field E] [Algebra K E] [Algebra k₁ E]
  [FiniteDimensional K E] [IsGalois K E]

/-- An intermediate field $M$ of $E/k_1$ containing a subfield $K$ over which $E$ is finite Galois, viewed as an
intermediate field of $E/K$. -/
def intermediateFieldOfContains (M : IntermediateField k₁ E) (hKM : ∀ a : K, algebraMap K E a ∈ M) :
    IntermediateField K E :=
  { M.toSubfield with algebraMap_mem' := hKM }

/-- **Galois correspondence over an intermediate field.** If $E/K$ is finite Galois and $M$ is an intermediate
field of $E/k_1$ containing $K$, then the fixed field of the $k_1$-automorphisms fixing $M$ is $M$. -/
theorem fixedField_fixingSubgroup_of_isGalois (M : IntermediateField k₁ E)
    (hKM : ∀ a : K, algebraMap K E a ∈ M) : fixedField (fixingSubgroup M) = M := by
  refine le_antisymm (fun y hy => ?_) (fun y hy => (mem_fixedField_iff _ _).mpr fun σ hσ => hσ ⟨y, hy⟩)
  set T := intermediateFieldOfContains M hKM
  have hfix : ∀ τ : E ≃ₐ[T] E, τ y = y := by
    intro τ
    let τ' : E ≃ₐ[k₁] E := AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) fun c => by
      have hc : algebraMap k₁ E c ∈ T := M.algebraMap_mem c
      exact τ.commutes ⟨_, hc⟩
    have hτ' : τ' ∈ fixingSubgroup M := fun m => τ.commutes ⟨m.1, m.2⟩
    exact (mem_fixedField_iff _ _).mp hy τ' hτ'
  have hmem : y ∈ fixedField (⊤ : Subgroup (E ≃ₐ[T] E)) :=
    (mem_fixedField_iff _ _).mpr fun τ _ => hfix τ
  rw [IsGalois.fixedField_top, IntermediateField.mem_bot] at hmem
  obtain ⟨t, rfl⟩ := hmem
  exact t.2

/-- The $k_1$-automorphisms fixing such an $M$ form a finite group. -/
theorem finite_fixingSubgroup_of_isGalois (M : IntermediateField k₁ E)
    (hKM : ∀ a : K, algebraMap K E a ∈ M) : Finite (fixingSubgroup M) := by
  let f : fixingSubgroup M → (E ≃ₐ[K] E) := fun σ =>
    AlgEquiv.ofRingEquiv (f := (σ.1 : E ≃ₐ[k₁] E).toRingEquiv) fun a =>
      σ.2 ⟨algebraMap K E a, hKM a⟩
  refine Finite.of_injective f fun σ τ hστ => Subtype.ext (AlgEquiv.ext fun z => ?_)
  exact congrArg (fun φ : E ≃ₐ[K] E => φ z) hστ

end Galois

section Compositum

variable {k F k₁ E : Type*} [Field k] [Field F] [Field k₁] [Field E] [Algebra k F] [Algebra k k₁]
  [Algebra k E] [Algebra F E] [Algebra k₁ E] [IsScalarTower k F E] [IsScalarTower k k₁ E]

/-- The compositum $F \cdot k_1$ inside $E$, as an intermediate field of $E/k_1$. -/
noncomputable abbrev adjoinRange (k₁ F E : Type*) [Field k₁] [Field F] [Field E] [Algebra F E]
    [Algebra k₁ E] : IntermediateField k₁ E :=
  adjoin k₁ (Set.range (algebraMap F E))

noncomputable instance algebraAdjoinRange : Algebra F (adjoinRange k₁ F E) :=
  RingHom.toAlgebra
    { toFun := fun f => ⟨algebraMap F E f, subset_adjoin _ _ ⟨f, rfl⟩⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun f g => Subtype.ext (map_mul _ f g)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun f g => Subtype.ext (map_add _ f g) }

theorem coe_algebraMap_adjoinRange (f : F) :
    (algebraMap F (adjoinRange k₁ F E) f : E) = algebraMap F E f := rfl

instance isScalarTower_adjoinRange : IsScalarTower k F (adjoinRange k₁ F E) :=
  IsScalarTower.of_algebraMap_eq fun c => Subtype.ext (by
    rw [coe_algebraMap_adjoinRange, ← IsScalarTower.algebraMap_apply]
    exact (IsScalarTower.algebraMap_apply k (adjoinRange k₁ F E) E c).symm)

/-- $F \cdot k_1$ is the constant field extension of $F$ by $k_1$. -/
theorem constantCompositum_adjoinRange_eq_top :
    constantCompositum F k₁ (adjoinRange k₁ F E) = ⊤ := by
  set A := adjoinRange k₁ F E
  set C := constantCompositum F k₁ A
  let C' : IntermediateField k₁ E := Subfield.toIntermediateField (C.toSubfield.map A.val.toRingHom)
    fun c => ⟨algebraMap k₁ A c, algebraMap_mem_constantCompositum F k₁ A c, rfl⟩
  have hA : A ≤ C' := by
    refine (adjoin_le_iff).mpr ?_
    rintro _ ⟨f, rfl⟩
    exact ⟨algebraMap F A f, C.algebraMap_mem f, rfl⟩
  rw [eq_top_iff]
  intro z _
  obtain ⟨w, hw, hwz⟩ := hA z.2
  have : w = z := Subtype.ext hwz
  rw [← this]
  exact hw

/-- $N_n(F \cdot k_1) = N_{[k_1:k] n}(F)$. -/
theorem curvePointCount_adjoinRange [Finite k] [FiniteDimensional k k₁] (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (n : ℕ) (hn : 1 ≤ n) :
    curvePointCount k₁ (adjoinRange k₁ F E) n = curvePointCount k F (finrank k k₁ * n) :=
  curvePointCount_constantCompositum hF hex constantCompositum_adjoinRange_eq_top n hn

end Compositum

theorem sqrt_pow_eq (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : Real.sqrt (a ^ n) = Real.sqrt a ^ n := by
  rw [show a ^ n = (Real.sqrt a ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt ha]]
  exact Real.sqrt_sq (by positivity)

/-- The lower bound along the multiples $dn$, $n$ even, from a finite Galois extension $E$ of $k(x)$ containing
$F$, with $d$ the degree of the constant field of $E$. -/
theorem exists_lowerBound_of_galois {k : Type u} {F : Type v} {E : Type v} [Field k] [Finite k] [Field F]
    [Algebra k F] [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {x : F} (hxt : Transcendental k x)
    {K : Type*} [Field K] [Algebra K F] [Algebra K E] [IsScalarTower K F E] [FiniteDimensional K E]
    [IsGalois K E] (hKx : ∀ a : K, algebraMap K F a ∈ k⟮x⟯) [FiniteDimensional F E] :
    ∃ d : ℕ, 1 ≤ d ∧ ∃ C : ℝ, ∃ n₁ : ℕ, ∀ n, n₁ ≤ n → 2 ∣ n →
      (Nat.card k : ℝ) ^ (d * n) + 1 - C * Real.sqrt (Nat.card k) ^ (d * n) ≤
        curvePointCount k F (d * n) := by
  classical
  have hEk : IsFunctionField k E := hF.finite_extension
  let k₁ := algebraicClosure k E
  have : FiniteDimensional k k₁ := hEk.finiteDimensional_algebraicClosure
  have : Finite k₁ := Module.finite_of_finite k
  have hE₁ : IsFunctionField k₁ E := hEk.algebraicClosure
  have hex₁ : IsIntegrallyClosedIn k₁ E := inferInstance
  let y : E := algebraMap F E x
  have hyk : Transcendental k y :=
    (transcendental_algebraMap_iff (algebraMap F E).injective).mpr hxt
  have hyt : Transcendental k₁ y :=
    (Algebra.IsAlgebraic.transcendental_iff (R := k) (S := k₁)).mp hyk
  let MK : IntermediateField k₁ E := k₁⟮y⟯
  let MF : IntermediateField k₁ E := adjoinRange k₁ F E
  have hKMF : ∀ a : K, algebraMap K E a ∈ MF := fun a => by
    rw [IsScalarTower.algebraMap_apply K F E]
    exact subset_adjoin _ _ ⟨_, rfl⟩
  have hKMK : ∀ a : K, algebraMap K E a ∈ MK := by
    have hle : (k⟮x⟯).map (IsScalarTower.toAlgHom k F E) ≤ MK.restrictScalars k := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]
      exact IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self k₁ y)
    intro a
    rw [IsScalarTower.algebraMap_apply K F E]
    exact hle ⟨_, hKx a, rfl⟩
  have hMKF : MK ≤ MF := IntermediateField.adjoin_simple_le_iff.mpr (subset_adjoin _ _ ⟨x, rfl⟩)
  have : Finite (fixingSubgroup MK) := finite_fixingSubgroup_of_isGalois MK hKMK
  have hH : fixingSubgroup MF ≤ fixingSubgroup MK := IntermediateField.fixingSubgroup_le hMKF
  have hΓ : fixedField (fixingSubgroup MK) = MK := fixedField_fixingSubgroup_of_isGalois MK hKMK
  have hHf : fixedField (fixingSubgroup MF) = MF := fixedField_fixingSubgroup_of_isGalois MF hKMF
  have hK0 : genus k₁ (fixedField (fixingSubgroup MK)) = 0 := by
    rw [hΓ]; exact genus_adjoin_simple_eq_zero hyt
  have hcount : ∀ n, 1 ≤ n → curvePointCount k₁ (fixedField (fixingSubgroup MF)) n =
      curvePointCount k F (finrank k k₁ * n) := by
    intro n hn
    rw [hHf]
    exact curvePointCount_adjoinRange hF hex n hn
  have hcard : Nat.card k₁ = Nat.card k ^ finrank k k₁ := Module.natCard_eq_pow_finrank (K := k)
  refine ⟨finrank k k₁, Module.finrank_pos,
    (Nat.card (fixingSubgroup MK) - 1) * (2 * genus k₁ E + 1), 4 * (genus k₁ E + 1) + 1,
    fun n hn h2 => ?_⟩
  have hb := lowerBound_fixedField hE₁ hex₁ (fixingSubgroup MK) (fixingSubgroup MF) hH hK0 n hn h2
  rw [hcount n (by omega), hcard] at hb
  push_cast at hb
  rw [sqrt_pow_eq _ (by positivity), ← pow_mul, ← pow_mul] at hb
  linarith

/-- **The lower bound along the multiples $dn$, $n$ even**, from the Galois closure of $F/k(x)$ with constant
field $\mathbb F_{q^d}$. -/
theorem exists_lowerBound_galoisClosure {k : Type u} {F : Type v} [Field k] [Finite k] [Field F]
    [Algebra k F] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) :
    ∃ d : ℕ, 1 ≤ d ∧ ∃ C : ℝ, ∃ n₁ : ℕ, ∀ n, n₁ ≤ n → 2 ∣ n →
      (Nat.card k : ℝ) ^ (d * n) + 1 - C * Real.sqrt (Nat.card k) ^ (d * n) ≤
        curvePointCount k F (d * n) := by
  classical
  obtain ⟨x, hxt, hsep⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  have : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin hxt
  have : Algebra.IsAlgebraic k⟮x⟯ (AlgebraicClosure F) :=
    Algebra.IsAlgebraic.trans k⟮x⟯ F (AlgebraicClosure F)
  have : IsAlgClosure k⟮x⟯ (AlgebraicClosure F) := ⟨inferInstance, inferInstance⟩
  have : Normal k⟮x⟯ (AlgebraicClosure F) := IsAlgClosure.normal k⟮x⟯ (AlgebraicClosure F)
  let E := normalClosure k⟮x⟯ F (AlgebraicClosure F)
  have : IsGalois k⟮x⟯ E := { }
  have : FiniteDimensional F E := Module.Finite.right k⟮x⟯ F E
  have : IsScalarTower k F E := IsScalarTower.of_algebraMap_eq fun c => Subtype.ext
    (IsScalarTower.algebraMap_apply k F (AlgebraicClosure F) c)
  have : FiniteDimensional k⟮x⟯ E := normalClosure.is_finiteDimensional k⟮x⟯ F (AlgebraicClosure F)
  exact exists_lowerBound_of_galois (E := E) (K := k⟮x⟯) hF hex hxt fun a => a.2

/-- **The lower bound along the multiples of some degree** (`HasseWeilLowerBoundMultiple`), proved. -/
theorem hasseWeilLowerBoundMultiple : HasseWeilLowerBoundMultiple.{u, v} := by
  refine ⟨fun k F _ _ _ _ hF hex => ?_⟩
  obtain ⟨d, hd, C, n₁, hC⟩ := exists_lowerBound_galoisClosure hF hex
  refine ⟨C, 2 * d, d * n₁, by omega, fun n hn hdn => ?_⟩
  obtain ⟨j, rfl⟩ := hdn
  have h := hC (2 * j) (by
    by_contra hlt
    push Not at hlt
    have : d * (2 * j) < d * n₁ := Nat.mul_lt_mul_of_pos_left hlt (by omega)
    rw [show 2 * d * j = d * (2 * j) by ring] at hn
    omega) ⟨j, rfl⟩
  rw [show 2 * d * j = d * (2 * j) by ring]
  exact h

end ModularFormsKB.Milne
