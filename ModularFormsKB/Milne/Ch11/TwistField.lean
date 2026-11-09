import TauCeti.FieldTheory.FunctionField.ConstantExtension.Genus.Basic
import TauCeti.FieldTheory.FunctionField.ConstantExtension.Genus.Change
import TauCeti.FieldTheory.FunctionField.ConstantExtension.ResidueField
import TauCeti.FieldTheory.FunctionField.Automorphism.FixedField
import TauCeti.FieldTheory.FunctionField.Place.Equiv
import TauCeti.FieldTheory.Minpoly.IsIntegrallyClosedIn
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The twist of a function field by an automorphism over a Frobenius

Let $k'/k$ be an extension of finite fields of degree $m$, $E$ a function field over $k'$ with $k'$ algebraically
closed in $E$, and $g$ a $k$-automorphism of $E$ with $g^m = 1$ acting on $k'$ as an automorphism $\rho$ of order
$m$ (in the application $\rho$ is the Frobenius and $g = \tau \otimes \rho$, `twistAut`). Let
$T = E^{\langle g\rangle}$ be the fixed field. Then (Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed.,
proof of Theorem 5.2.3 [unverified numbering]):

- `isFunctionField_twistField`, `isIntegrallyClosedIn_twistField`: $T$ is a function field over $k$ with $k$
  algebraically closed in $T$;
- `constantCompositum_twistField_eq_top`: $E = T \cdot k'$, so `genus_twistField`: $g(T) = g(E)$;
- `card_degree_one_twistField`: the rational places of $T$ correspond to the rational places $Q$ of $E/k'$ with
  $g Q = Q$.
-/

open TauCeti Module IntermediateField

set_option linter.unusedSectionVars false

namespace ModularFormsKB.Milne

variable {k k' E : Type*} [Field k] [Field k'] [Field E] [Algebra k k'] [Algebra k' E] [Algebra k E]
  [IsScalarTower k k' E] [Finite k] [Finite k'] [Algebra.IsSeparable k k']

/-- The fixed field of an automorphism. -/
noncomputable abbrev twistField (g : E ≃ₐ[k] E) : IntermediateField k E :=
  fixedField (Subgroup.zpowers g)

/-- The elements of $k'$ fixed by an automorphism of order $[k':k]$ are those of $k$. -/
theorem mem_range_of_orderOf_eq {ρ : k' ≃ₐ[k] k'} (hρ : orderOf ρ = finrank k k') {c : k'}
    (hc : ρ c = c) : c ∈ Set.range (algebraMap k k') := by
  have := Fintype.ofFinite (Subgroup.zpowers ρ)
  have hfin := FixedPoints.finrank_eq_card (Subgroup.zpowers ρ) k'
  rw [← Nat.card_eq_fintype_card, Nat.card_zpowers, hρ] at hfin
  set M : IntermediateField k k' := fixedField (Subgroup.zpowers ρ)
  have hM : finrank k M = 1 := by
    have h1 := Module.finrank_mul_finrank k M k'
    have h2 : finrank M k' = finrank k k' := hfin
    have hpos : 0 < finrank k k' := Module.finrank_pos
    rw [h2] at h1
    exact (Nat.mul_eq_right hpos.ne').mp h1
  have hbot : M = ⊥ := IntermediateField.finrank_eq_one_iff.mp hM
  have hcM : c ∈ M := (mem_fixedField_iff _ _).mpr fun σ hσ => by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
    clear hσ
    have : (ρ ^ j) c = c := by
      induction j using Int.induction_on with
      | zero => simp
      | succ n ih => rw [zpow_add_one, AlgEquiv.mul_apply, hc, ih]
      | pred n ih =>
        rw [zpow_sub_one, AlgEquiv.mul_apply]
        have : ρ.symm c = c := by rw [AlgEquiv.symm_apply_eq, hc]
        rw [show (ρ⁻¹ : k' ≃ₐ[k] k') c = ρ.symm c from rfl, this, ih]
    exact this
  rw [hbot] at hcM
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hcM
  exact ⟨a, ha⟩

variable (g : E ≃ₐ[k] E) (ρ : k' ≃ₐ[k] k')
  (hgρ : ∀ c : k', g (algebraMap k' E c) = algebraMap k' E (ρ c))
  (hρ : orderOf ρ = finrank k k') (hgm : g ^ finrank k k' = 1)

include hgρ in
theorem twist_pow_algebraMap (n : ℕ) (c : k') :
    (g ^ n) (algebraMap k' E c) = algebraMap k' E ((ρ ^ n) c) := by
  induction n generalizing c with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, AlgEquiv.mul_apply, hgρ, ih, AlgEquiv.mul_apply]

include hgρ hρ hgm in
theorem orderOf_twist : orderOf g = finrank k k' := by
  have hpos : 0 < finrank k k' := Module.finrank_pos
  refine (orderOf_eq_iff hpos).mpr ⟨hgm, fun j hj hj0 hgj => ?_⟩
  have hρj : ρ ^ j = 1 := AlgEquiv.ext fun c => by
    apply (algebraMap k' E).injective
    rw [← twist_pow_algebraMap g ρ hgρ, hgj]; rfl
  have := orderOf_le_of_pow_eq_one hj0 hρj
  omega

include hgm in
theorem finite_zpowers_twist : Finite (Subgroup.zpowers g) := by
  have hpos : 0 < finrank k k' := Module.finrank_pos
  have : IsOfFinOrder g := isOfFinOrder_iff_pow_eq_one.mpr ⟨_, hpos, hgm⟩
  exact this.finite_zpowers

include hgρ hρ hgm in
/-- $[E : T] = m$. -/
theorem finrank_twistField : finrank (twistField g) E = finrank k k' := by
  have := finite_zpowers_twist g hgm
  have := Fintype.ofFinite (Subgroup.zpowers g)
  have h := FixedPoints.finrank_eq_card (Subgroup.zpowers g) E
  rw [← Nat.card_eq_fintype_card, Nat.card_zpowers, orderOf_twist g ρ hgρ hρ hgm] at h
  exact h

include hgρ in
theorem algebraMap_mem_twistField_iff (c : k') :
    algebraMap k' E c ∈ twistField g ↔ ρ c = c := by
  constructor
  · intro h
    have := (mem_fixedField_iff _ _).mp h g (Subgroup.mem_zpowers g)
    rw [hgρ] at this
    exact (algebraMap k' E).injective this
  · intro hc
    refine (mem_fixedField_iff _ _).mpr fun σ hσ => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
    have hg : g (algebraMap k' E c) = algebraMap k' E c := by rw [hgρ, hc]
    clear hσ
    induction j using Int.induction_on with
    | zero => simp
    | succ n ih => rw [zpow_add_one, AlgEquiv.mul_apply, hg, ih]
    | pred n ih =>
      rw [zpow_sub_one, AlgEquiv.mul_apply]
      have : g.symm (algebraMap k' E c) = algebraMap k' E c := by rw [AlgEquiv.symm_apply_eq, hg]
      rw [show (g⁻¹ : E ≃ₐ[k] E) (algebraMap k' E c) = g.symm (algebraMap k' E c) from rfl, this, ih]

include hgρ hρ in
/-- $k$ is algebraically closed in the twist. -/
theorem isIntegrallyClosedIn_twistField (hex : IsIntegrallyClosedIn k' E) :
    IsIntegrallyClosedIn k (twistField g) := by
  refine (isIntegrallyClosedIn_iff).mpr ⟨(algebraMap k (twistField g)).injective, fun {x} hx => ?_⟩
  have hxE : IsIntegral k (x : E) := by
    have := hx.map (IsScalarTower.toAlgHom k (twistField g) E)
    simpa using this
  have hxE' : IsIntegral k' (x : E) := hxE.tower_top
  obtain ⟨c, hc⟩ := (isIntegrallyClosedIn_iff.mp hex).2 hxE'
  have hρc : ρ c = c := (algebraMap_mem_twistField_iff g ρ hgρ c).mp (hc ▸ x.2)
  obtain ⟨a, rfl⟩ := mem_range_of_orderOf_eq hρ hρc
  refine ⟨a, Subtype.ext ?_⟩
  rw [← hc, ← IsScalarTower.algebraMap_apply k k' E]
  rfl

include hgρ hρ hgm in
/-- $E = T \cdot k'$. -/
theorem constantCompositum_twistField_eq_top (hex : IsIntegrallyClosedIn k' E) :
    constantCompositum (twistField g) k' E = ⊤ := by
  have hexT := isIntegrallyClosedIn_twistField g ρ hgρ hρ hex
  let b := Module.finBasis k k'
  have hli : LinearIndependent (twistField g) (algebraMap k' E ∘ b) :=
    linearIndependent_algebraMap_comp_of_isIntegrallyClosedIn hexT
      (fun i => Algebra.IsSeparable.isSeparable k (b i)) b.linearIndependent
  have hfr := finrank_twistField g ρ hgρ hρ hgm
  have : FiniteDimensional (twistField g) E :=
    Module.finite_of_finrank_pos (by rw [hfr]; exact Module.finrank_pos)
  have hspan : Submodule.span (twistField g) (Set.range (algebraMap k' E ∘ b)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [hfr]; simp)
  rw [eq_top_iff]
  intro y _
  have hy : y ∈ Submodule.span (twistField g) (Set.range (algebraMap k' E ∘ b)) := by
    rw [hspan]; trivial
  have hle : Submodule.span (twistField g) (Set.range (algebraMap k' E ∘ b)) ≤
      Subalgebra.toSubmodule (constantCompositum (twistField g) k' E).toSubalgebra :=
    Submodule.span_le.mpr (by
      rintro _ ⟨i, rfl⟩
      exact algebraMap_mem_constantCompositum _ _ _ (b i))
  exact hle hy

include hgm in
/-- The twist is a function field over $k$. -/
theorem isFunctionField_twistField (hE : IsFunctionField k' E) : IsFunctionField k (twistField g) := by
  have : FiniteDimensional k k' := Module.Finite.of_finite
  have := finite_zpowers_twist g hgm
  exact (hE.of_finiteDimensional (k := k)).fixedField _

include hgρ hρ hgm in
/-- The twist has the genus of $E$. -/
theorem genus_twistField (hE : IsFunctionField k' E) (hex : IsIntegrallyClosedIn k' E) :
    genus k (twistField g) = genus k' E :=
  (genus_eq_genus_of_constantCompositum_eq_top (isFunctionField_twistField g hgm hE)
    (isIntegrallyClosedIn_twistField g ρ hgρ hρ hex)
    (constantCompositum_twistField_eq_top g ρ hgρ hρ hgm hex)).symm

/-- The action of $g$ on the places of $E/k'$ (transport along the $\rho$-semilinear $g$). -/
noncomputable def twistPlace : Place k' E ≃ Place k' E :=
  Place.equivOfRingEquiv ρ.toRingEquiv g.toRingEquiv hgρ

theorem valuation_twistPlace_apply (Q : Place k' E) (x : E) :
    (twistPlace g ρ hgρ Q).valuation (g x) = Q.valuation x := by
  simp [twistPlace]

theorem twistField_symm_apply (z : twistField g) : g.symm (z : E) = z := by
  have : g (z : E) = z := (mem_fixedField_iff _ _).mp z.2 g (Subgroup.mem_zpowers g)
  rw [AlgEquiv.symm_apply_eq, this]

include hgρ hρ hgm in
theorem finiteDimensional_twistField : FiniteDimensional (twistField g) E :=
  Module.finite_of_finrank_pos (by rw [finrank_twistField g ρ hgρ hρ hgm]; exact Module.finrank_pos)

/-- $gQ$ and $Q$ lie over the same place of the twist. -/
theorem restrict_twistPlace [Algebra.IsIntegral (twistField g) E] (Q : Place k' E) :
    (twistPlace g ρ hgρ Q).restrict k (twistField g) = Q.restrict k (twistField g) := by
  have hcomap : (twistPlace g ρ hgρ Q).valuation.comap (algebraMap (twistField g) E) =
      Q.valuation.comap (algebraMap (twistField g) E) := by
    ext z
    simp only [Valuation.comap_apply, twistPlace, Place.valuation_equivOfRingEquiv]
    exact congrArg Q.valuation (twistField_symm_apply g z)
  ext1
  change (((twistPlace g ρ hgρ Q).valuation.comap (algebraMap (twistField g) E)).normalization) =
    ((Q.valuation.comap (algebraMap (twistField g) E)).normalization)
  rw [hcomap]

include hgρ hρ in
/-- If a rational place $Q$ of $E/k'$ is fixed by $g$, the place below it in any subfield fixed by $g$ is rational. -/
theorem degree_restrict_eq_one_of_twistPlace_eq' (M : IntermediateField k E) (hM : ∀ x ∈ M, g x = x)
    [Algebra.IsIntegral M E] {Q : Place k' E}
    (hQ : Q.degree = 1) (hfix : twistPlace g ρ hgρ Q = Q) : (Q.restrict k M).degree = 1 := by
  set R := Q.restrict k M
  refine (Place.degree_eq_one_iff_forall_exists_valuation_sub_lt_one R).mpr fun f hf => ?_
  have hfQ : algebraMap M E f ∈ Q.integers :=
    (Place.mem_integers_restrict_iff k _ Q f).mp hf
  obtain ⟨d, hd⟩ := (Place.degree_eq_one_iff_forall_exists_valuation_sub_lt_one Q).mp hQ _ hfQ
  have hgf : g (algebraMap M E f) = algebraMap M E f :=
    hM f f.2
  have hd' : Q.valuation (algebraMap M E f - algebraMap k' E (ρ d)) < 1 := by
    have := valuation_twistPlace_apply g ρ hgρ Q (algebraMap M E f - algebraMap k' E d)
    rw [map_sub, hgf, hgρ, hfix] at this
    rw [this]; exact hd
  have hρd : ρ d = d := Place.eq_of_valuation_sub_lt_one Q hd' hd
  obtain ⟨c, rfl⟩ := mem_range_of_orderOf_eq hρ hρd
  refine ⟨c, ?_⟩
  have hv := Place.valuation_algebraMap_restrict k M Q (f - algebraMap k M c)
  have heq : algebraMap M E (f - algebraMap k M c) =
      algebraMap M E f - algebraMap k' E (algebraMap k k' c) := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [heq] at hv
  rw [hv] at hd
  by_contra hge
  rw [not_lt] at hge
  exact absurd hd (not_lt.mpr (one_le_pow₀ hge))

include hgρ hρ in
/-- If a rational place $Q$ of $E/k'$ is fixed by $g$, the place of the twist below it is rational. -/
theorem degree_restrict_eq_one_of_twistPlace_eq [Algebra.IsIntegral (twistField g) E] {Q : Place k' E}
    (hQ : Q.degree = 1) (hfix : twistPlace g ρ hgρ Q = Q) : (Q.restrict k (twistField g)).degree = 1 :=
  degree_restrict_eq_one_of_twistPlace_eq' g ρ hgρ hρ (twistField g)
    (fun _x hx => (mem_fixedField_iff _ _).mp hx g (Subgroup.mem_zpowers g)) hQ hfix

include hgρ hρ hgm in
/-- **The rational places of the twist** correspond to the rational places of $E/k'$ fixed by $g$. -/
theorem card_degree_one_twistField (hE : IsFunctionField k' E) (hex : IsIntegrallyClosedIn k' E) :
    Nat.card {R : Place k (twistField g) // R.degree = 1} =
      Nat.card {Q : Place k' E // Q.degree = 1 ∧ twistPlace g ρ hgρ Q = Q} := by
  have := finiteDimensional_twistField g ρ hgρ hρ hgm
  have hT := isFunctionField_twistField g hgm hE
  have hexT := isIntegrallyClosedIn_twistField g ρ hgρ hρ hex
  have hc := constantCompositum_twistField_eq_top g ρ hgρ hρ hgm hex
  have huniq : ∀ R : Place k (twistField g), R.degree = 1 →
      ∃! Q : Place k' E, Q.restrict k (twistField g) = R := fun R hR =>
    Place.existsUnique_restrict_eq_of_degree_eq_one_of_constantCompositum_eq_top hT hc hR
  have hdeg : ∀ Q : Place k' E, (Q.restrict k (twistField g)).degree = 1 → Q.degree = 1 := by
    intro Q hQ
    exact Place.degree_eq_one_of_constantCompositum_eq_top hT hexT hc Q
      ((Algebra.ofId k k').comp (Place.residueFieldEquivOfDegreeEqOne _ hQ).symm.toAlgHom)
  symm
  refine Nat.card_congr
    { toFun := fun Q => ⟨Q.1.restrict k (twistField g),
        degree_restrict_eq_one_of_twistPlace_eq g ρ hgρ hρ Q.2.1 Q.2.2⟩
      invFun := fun R => ⟨(huniq R.1 R.2).choose,
        hdeg _ (by rw [(huniq R.1 R.2).choose_spec.1]; exact R.2),
        (huniq R.1 R.2).unique (by rw [restrict_twistPlace]; exact (huniq R.1 R.2).choose_spec.1)
          (huniq R.1 R.2).choose_spec.1⟩
      left_inv := by
        intro Q
        apply Subtype.ext
        have hR := degree_restrict_eq_one_of_twistPlace_eq g ρ hgρ hρ Q.2.1 Q.2.2
        exact (huniq _ hR).unique (huniq _ hR).choose_spec.1 rfl
      right_inv := fun R => Subtype.ext (huniq R.1 R.2).choose_spec.1 }

end ModularFormsKB.Milne
