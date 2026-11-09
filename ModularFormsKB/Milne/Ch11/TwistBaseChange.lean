import ModularFormsKB.Milne.Ch11.TwistLower

/-!
# Base change of a group of automorphisms to a constant field extension

Let $E/k$ be a function field with $k$ exact, $E' = E \cdot k'$ a finite separable constant field extension and
$M$ a group of $k$-automorphisms of $E$. Each $\tau \in M$ extends to the $k'$-automorphism $\tau \otimes 1$ of $E'$
(`baseChangeAut`), and the fixed field of $M \otimes 1$ is the constant field extension of $E^M$ by $k'$
(`constantCompositum_fixedField_baseChange_eq_top`): writing $b \in E'$ in the basis of constants, $b$ is fixed by
$M \otimes 1$ exactly when its coordinates are fixed by $M$.

Consequently, for $H \le \Gamma$ with $E^\Gamma$ of genus $0$, the lower bound over one constant field
(`card_degree_one_fixedField_ge`) applied over $k_n$ gives (`lowerBound_fixedField`)
$N_n(E^H) \ge q^n + 1 - C q^{n/2}$ for all even $n$ large enough, with $C = (|\Gamma|-1)(2g+1)$.
-/

open TauCeti Module IntermediateField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ModularFormsKB.Milne

universe u v

section BaseChange

variable {k k' E E' : Type*} [Field k] [Field k'] [Field E] [Field E']
  [Algebra k k'] [Algebra k E] [Algebra k E'] [Algebra k' E'] [Algebra E E']
  [IsScalarTower k k' E'] [IsScalarTower k E E'] [Algebra.IsSeparable k k']
  (hex : IsIntegrallyClosedIn k E) (h : constantCompositum E k' E' = ⊤)

/-- $\tau \otimes 1$, a $k'$-automorphism of $E'$. -/
noncomputable def baseChangeAut (τ : E ≃ₐ[k] E) : E' ≃ₐ[k'] E' :=
  AlgEquiv.ofRingEquiv (f := (twistAut hex h τ 1).toRingEquiv) fun c => by
    simp [twistAut_algebraMap_right]

@[simp]
theorem baseChangeAut_apply (τ : E ≃ₐ[k] E) (x : E') :
    baseChangeAut hex h τ x = twistAut hex h τ 1 x := rfl

/-- $\tau \mapsto \tau \otimes 1$ as a group homomorphism. -/
noncomputable def baseChangeHom : (E ≃ₐ[k] E) →* (E' ≃ₐ[k'] E') where
  toFun := baseChangeAut hex h
  map_one' := AlgEquiv.ext fun x => by simp
  map_mul' τ τ' := AlgEquiv.ext fun x => by
    simp only [baseChangeAut_apply, AlgEquiv.mul_apply]
    rw [← AlgEquiv.mul_apply, ← twistAut_mul, mul_one]

theorem baseChangeHom_apply (τ : E ≃ₐ[k] E) (x : E') : baseChangeHom hex h τ x = twistAut hex h τ 1 x :=
  rfl

theorem injective_baseChangeHom : Function.Injective (baseChangeHom hex h) := by
  intro τ τ' hττ'
  have : twistAutHom hex h (τ, 1) = twistAutHom hex h (τ', 1) :=
    AlgEquiv.ext fun x => congrArg (fun σ : E' ≃ₐ[k'] E' => σ x) hττ'
  exact congrArg Prod.fst (injective_twistAutHom hex h this)

variable (M : Subgroup (E ≃ₐ[k] E))

theorem algebraMap_mem_fixedField_baseChange (x : fixedField M) :
    algebraMap E E' (x : E) ∈ fixedField (M.map (baseChangeHom hex h)) := by
  refine (mem_fixedField_iff _ _).mpr fun σ hσ => ?_
  obtain ⟨τ, hτ, rfl⟩ := hσ
  rw [baseChangeHom_apply, twistAut_algebraMap_left, (mem_fixedField_iff _ _).mp x.2 τ hτ]

/-- The inclusion $E^M \to E'^{M \otimes 1}$. -/
noncomputable def fixedFieldBaseChangeHom :
    fixedField M →+* fixedField (M.map (baseChangeHom hex h)) where
  toFun x := ⟨algebraMap E E' (x : E), algebraMap_mem_fixedField_baseChange hex h M x⟩
  map_one' := Subtype.ext (map_one (algebraMap E E'))
  map_mul' x y := Subtype.ext (map_mul (algebraMap E E') (x : E) (y : E))
  map_zero' := Subtype.ext (map_zero (algebraMap E E'))
  map_add' x y := Subtype.ext (map_add (algebraMap E E') (x : E) (y : E))

noncomputable instance algebraFixedFieldBaseChange :
    Algebra (fixedField M) (fixedField (M.map (baseChangeHom hex h))) :=
  (fixedFieldBaseChangeHom hex h M).toAlgebra

theorem coe_algebraMap_fixedFieldBaseChange (x : fixedField M) :
    (algebraMap (fixedField M) (fixedField (M.map (baseChangeHom hex h))) x : E') =
      algebraMap E E' (x : E) := rfl

instance isScalarTower_fixedFieldBaseChange :
    IsScalarTower k (fixedField M) (fixedField (M.map (baseChangeHom hex h))) :=
  IsScalarTower.of_algebraMap_eq fun c => Subtype.ext (by
    change algebraMap k E' c = algebraMap E E' (algebraMap k E c)
    rw [← IsScalarTower.algebraMap_apply])

/-- **The fixed field of $M \otimes 1$ is $E^M \cdot k'$.** -/
theorem constantCompositum_fixedField_baseChange_eq_top [FiniteDimensional k k'] :
    constantCompositum (fixedField M) k' (fixedField (M.map (baseChangeHom hex h))) = ⊤ := by
  classical
  set B := fixedField (M.map (baseChangeHom hex h))
  let b := Module.finBasis k k'
  let bE := constantBasis hex h b
  rw [eq_top_iff]
  intro y _
  -- the coordinates of `y` are fixed by `M`
  have hcoord : ∀ i, bE.repr (y : E') i ∈ fixedField M := by
    intro i
    refine (mem_fixedField_iff _ _).mpr fun τ hτ => ?_
    have hy : twistAut hex h τ 1 (y : E') = y :=
      (mem_fixedField_iff _ _).mp y.2 _ ⟨τ, hτ, rfl⟩
    have hexp : (y : E') = ∑ j, algebraMap E E' (bE.repr (y : E') j) * algebraMap k' E' (b j) := by
      conv_lhs => rw [← bE.sum_repr (y : E')]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, constantBasis_apply]
    have himg : twistAut hex h τ 1 (y : E') =
        ∑ j, algebraMap E E' (τ (bE.repr (y : E') j)) * algebraMap k' E' (b j) := by
      conv_lhs => rw [hexp]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, twistAut_algebraMap_left, twistAut_algebraMap_right, AlgEquiv.one_apply]
    have hsum : (y : E') = ∑ j, τ (bE.repr (y : E') j) • bE j := by
      conv_lhs => rw [← hy, himg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, constantBasis_apply]
    have := congrArg (fun z => bE.repr z i) hsum
    simp only [Basis.repr_sum_self] at this
    exact this.symm
  -- hence `y` lies in the compositum
  have hy : y = ∑ i, algebraMap (fixedField M) B ⟨_, hcoord i⟩ * algebraMap k' B (b i) := by
    apply Subtype.ext
    simp only [IntermediateField.coe_sum, IntermediateField.coe_mul]
    conv_lhs => rw [← bE.sum_repr (y : E')]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, constantBasis_apply]
    rfl
  rw [hy]
  refine IntermediateField.sum_mem _ fun i _ => IntermediateField.mul_mem _ ?_ ?_
  · exact IntermediateField.algebraMap_mem _ _
  · exact algebraMap_mem_constantCompositum _ _ _ (b i)

end BaseChange

/-- **The lower bound for $E^H$ in even degrees**, when $E^\Gamma$ has genus $0$:
$N_n(E^H) \ge q^n + 1 - (|\Gamma|-1)(2g+1) q^{n/2}$ for even $n \ge 4(g+1)+1$. -/
theorem lowerBound_fixedField {k : Type u} {E : Type v} [Field k] [Finite k] [Field E] [Algebra k E]
    (hE : IsFunctionField k E) (hex : IsIntegrallyClosedIn k E) (Γ H : Subgroup (E ≃ₐ[k] E)) [Finite Γ]
    (hH : H ≤ Γ) (hK : genus k (fixedField Γ) = 0) (n : ℕ) (hn : 4 * (genus k E + 1) + 1 ≤ n)
    (h2 : 2 ∣ n) :
    (Nat.card k : ℝ) ^ n + 1 - (Nat.card Γ - 1) * (2 * genus k E + 1) * Real.sqrt (Nat.card k) ^ n ≤
      curvePointCount k (fixedField H) n := by
  set q : ℕ := Nat.card k with hq
  have hq2 : 2 ≤ q := Finite.one_lt_card
  obtain ⟨E', k', hfd, hdeg, hc⟩ := exists_constantCompositum_finrank_eq (k := k) (F := E) n (by omega)
  have : Finite k' := Module.finite_of_finite k
  have hE' : IsFunctionField k' E' := hE.of_constantCompositum_eq_top hc
  have hex' : IsIntegrallyClosedIn k' E' := IsIntegrallyClosedIn.of_constantCompositum_eq_top hex hc
  have hg : genus k' E' = genus k E := genus_eq_genus_of_constantCompositum_eq_top hE hex hc
  have hcard : Nat.card k' = q ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := k), hdeg]
  set Γ' := Γ.map (baseChangeHom hex hc)
  set H' := H.map (baseChangeHom hex hc)
  have hH' : H' ≤ Γ' := Subgroup.map_mono hH
  have : Finite Γ' := Finite.Set.finite_image _ _
  have hcardΓ : Nat.card Γ' = Nat.card Γ :=
    Subgroup.card_map_of_injective (injective_baseChangeHom hex hc)
  have hKF : IsFunctionField k (fixedField Γ) := hE.fixedField Γ
  have hK' : genus k' (fixedField Γ') = 0 := by
    rw [genus_eq_genus_of_constantCompositum_eq_top hKF (isIntegrallyClosedIn_intermediateField hex _)
      (constantCompositum_fixedField_baseChange_eq_top hex hc Γ), hK]
  have hHfin : Finite H :=
    Finite.of_injective (Subgroup.inclusion hH) (Subgroup.inclusion_injective hH)
  have hHF : IsFunctionField k (fixedField H) := hE.fixedField H
  have hHcount : Nat.card {P : Place k' (fixedField H') // P.degree = 1} =
      curvePointCount k (fixedField H) n := by
    rw [card_degree_one_constantCompositum hHF (isIntegrallyClosedIn_intermediateField hex _)
      (constantCompositum_fixedField_baseChange_eq_top hex hc H), hdeg]
  obtain ⟨m, rfl⟩ := h2
  have hsq : IsSquare (Nat.card k') := ⟨q ^ m, by rw [hcard]; ring⟩
  have hbig : (genus k' E' + 1) ^ 4 < Nat.card k' := by
    rw [hg, hcard]; exact pow_four_lt_pow _ _ _ hq2 (by omega)
  have hb := card_degree_one_fixedField_ge hE' hex' Γ' H' hH' hK' hsq hbig
  rw [hHcount, hcardΓ, hg, hcard] at hb
  have hsqrt : Real.sqrt ((q : ℝ) ^ (2 * m)) = Real.sqrt q ^ (2 * m) := by
    rw [show (q : ℝ) ^ (2 * m) = (Real.sqrt q ^ (2 * m)) ^ 2 by
      rw [← pow_mul, show 2 * m * 2 = 2 * (2 * m) by ring, pow_mul (Real.sqrt (q : ℝ)) 2,
        Real.sq_sqrt (by positivity)]]
    exact Real.sqrt_sq (by positivity)
  push_cast at hb
  rw [hsqrt] at hb
  exact hb

end ModularFormsKB.Milne
