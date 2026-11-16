import ModularFormsKB.ThetaGenus.ConstantTerm

/-!
# The genus in congruence form; Gauss sums are genus invariants

The arithmetic half of the statement that theta series of one genus differ by a cusp form.

**The genus, in congruence form.** Two lattices `L ⊆ E`, `M ⊆ F` are in one genus
(`ThetaGenus.SameGenus L M`) when they have the same covolume and, for every `c ≥ 1`, a `ℤ`-linear map
`φ : L → M` induces a bijection `L/cL → M/cM` with `‖φ x‖² ≡ ‖x‖² mod 2c`, i.e. `Q(φ x) ≡ Q(x) mod c`
for `Q = ‖·‖²/2` (`ModIsometry`). For positive definite lattices this is Siegel's description of the
genus: same determinant and equivalence modulo every integer, which by the Chinese remainder theorem
and compactness is the same as isometry over every `ℤ_p` [unverified: Cassels, *Rational Quadratic
Forms*, Ch. 9; Siegel 1935]. The equivalence with Tau Ceti's `TauCeti.IntegralLattice.SameGenus`
(signature and integral isometry at every prime) is not formalized here (loose end).

**Gauss sums.** For even lattices in one genus, `G_L(a, c) = G_M(a, c)` for every `a` and every `c ≥ 1`
(`SameGenus.gaussSum_eq`): `φ` induces a bijection of the index sets carrying each summand
`e(a ‖x‖² / (2c))` to itself.

**Orthogonal sums.** `L ⊕ M` and `L ⊕ M'` are in one genus when `M` and `M'` are
(`SameGenus.orthSum_left`, `SameGenus.orthSum_right`), and `θ_{L ⊕ M} = θ_L θ_M`
(`thetaSph_zero_orthSum`).
-/

open Complex Module Filter Topology
open scoped Real RealInnerProductSpace ModularForm UpperHalfPlane MatrixGroups Pointwise

set_option linter.unusedSectionVars false

namespace ModularFormsKB.ThetaGenus

open ModularFormsKB.Miyake.Sec4_9

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- **`φ` is an isometry modulo `c`**: `‖φ x‖² ≡ ‖x‖² mod 2c`, and `φ` induces a bijection
`L/cL → M/cM`. -/
structure ModIsometry (L : Submodule ℤ E) (M : Submodule ℤ F) (c : ℕ) (φ : L →ₗ[ℤ] M) : Prop where
  norm_sq : ∀ x : L, ∃ m : ℤ, ‖((φ x : M) : F)‖ ^ 2 - ‖(x : E)‖ ^ 2 = 2 * c * m
  surj : ∀ y : M, ∃ x : L, ∃ w : M, y = φ x + c • w
  inj : ∀ x : L, (∃ w : M, φ x = c • w) → ∃ v : L, x = c • v

/-- **Two lattices in one genus** (congruence form): equal covolumes, and an isometry modulo every
`c ≥ 1`. -/
structure SameGenus [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [MeasurableSpace E]
    [BorelSpace E] [MeasurableSpace F] [BorelSpace F] (L : Submodule ℤ E) (M : Submodule ℤ F) :
    Prop where
  covolume_eq : ZLattice.covolume L = ZLattice.covolume M
  modIso : ∀ c : ℕ, 0 < c → ∃ φ : L →ₗ[ℤ] M, ModIsometry L M c φ

/-! ### Gauss sums are genus invariants -/

section GaussSum

variable {L : Submodule ℤ E} {M : Submodule ℤ F}

theorem ModIsometry.le_comap {c : ℕ} {φ : L →ₗ[ℤ] M} :
    ((c : ℝ) • L).submoduleOf L ≤ (((c : ℝ) • M).submoduleOf M).comap φ := by
  intro x hx
  obtain ⟨w, rfl⟩ := ZLattice.mem_smul_submoduleOf_iff.mp hx
  rw [Submodule.mem_comap, map_nsmul]
  exact ZLattice.mem_smul_submoduleOf_iff.mpr ⟨φ w, rfl⟩

/-- The map `L/cL → M/cM` induced by `φ`. -/
noncomputable def ModIsometry.quotMap (c : ℕ) (φ : L →ₗ[ℤ] M) :
    L ⧸ ((c : ℝ) • L).submoduleOf L →ₗ[ℤ] M ⧸ ((c : ℝ) • M).submoduleOf M :=
  Submodule.mapQ _ _ φ ModIsometry.le_comap

theorem ModIsometry.bijective_quotMap {c : ℕ} {φ : L →ₗ[ℤ] M} (h : ModIsometry L M c φ) :
    Function.Bijective (ModIsometry.quotMap c φ) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with | H x
    rw [LinearMap.mem_ker, ModIsometry.quotMap, Submodule.mapQ_apply,
      Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨w, hw⟩ := ZLattice.mem_smul_submoduleOf_iff.mp hy
    obtain ⟨v, hv⟩ := h.inj x ⟨w, hw.symm⟩
    rw [Submodule.Quotient.mk_eq_zero]
    exact ZLattice.mem_smul_submoduleOf_iff.mpr ⟨v, hv.symm⟩
  · intro y
    induction y using Submodule.Quotient.induction_on with | H y
    obtain ⟨x, w, hw⟩ := h.surj y
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    rw [ModIsometry.quotMap, Submodule.mapQ_apply, Submodule.Quotient.eq]
    exact ZLattice.mem_smul_submoduleOf_iff.mpr ⟨-w, by rw [hw]; simp⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem ModIsometry.gaussTerm_quotMap {c : ℕ} {φ : L →ₗ[ℤ] M} (h : ModIsometry L M c φ)
    (hL : ZLattice.IsEven L) (hM : ZLattice.IsEven M) (a : ℤ) (y : L ⧸ ((c : ℝ) • L).submoduleOf L) :
    ZLattice.gaussTerm M hM a c 0 (ModIsometry.quotMap c φ y) = ZLattice.gaussTerm L hL a c 0 y := by
  induction y using Submodule.Quotient.induction_on with | H x
  rw [ModIsometry.quotMap, Submodule.mapQ_apply, ZLattice.gaussTerm_mk, ZLattice.gaussTerm_mk]
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hc' : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hc
  obtain ⟨m, hm⟩ := h.norm_sq x
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨a * m, ?_⟩
  simp only [ZeroMemClass.coe_zero, inner_zero_right, add_zero]
  have : ‖((φ x : M) : F)‖ ^ 2 = ‖(x : E)‖ ^ 2 + 2 * c * m := by linarith
  rw [this]
  push_cast
  field_simp

/-- **Gauss sums are genus invariants.** -/
theorem SameGenus.gaussSum_eq [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (h : SameGenus L M)
    (hL : ZLattice.IsEven L) (hM : ZLattice.IsEven M) (a : ℤ) (c : ℕ) [NeZero c]
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] [Fintype (M ⧸ ((c : ℝ) • M).submoduleOf M)] :
    ZLattice.gaussSum L hL a c = ZLattice.gaussSum M hM a c := by
  obtain ⟨φ, hφ⟩ := h.modIso c (Nat.pos_of_ne_zero (NeZero.ne c))
  rw [ZLattice.gaussSum_def, ZLattice.gaussSum_def]
  exact (Fintype.sum_bijective _ hφ.bijective_quotMap _ _
    fun y ↦ (hφ.gaussTerm_quotMap hL hM a y).symm)

end GaussSum

/-! ### Orthogonal sums -/

section OrthSum

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]

/-- The theta series of `L` is Tau Ceti's `ZLattice.thetaSeries`. -/
theorem thetaSph_zero_eq_thetaSeries (L : Submodule ℤ E) :
    thetaSph L 0 0 0 0 = ZLattice.thetaSeries L := by
  funext τ
  rw [thetaSph]
  simp only [pow_zero]
  rw [thetaW_one, ZLattice.thetaCoset_zero]

/-- `θ_{L ⊕ M} = θ_L θ_M`. -/
theorem thetaSph_zero_orthSum (L : Submodule ℤ E) [DiscreteTopology L] (M : Submodule ℤ F)
    [DiscreteTopology M] :
    thetaSph (ZLattice.orthSum L M) 0 0 0 0 = thetaSph L 0 0 0 0 * thetaSph M 0 0 0 0 := by
  rw [thetaSph_zero_eq_thetaSeries, thetaSph_zero_eq_thetaSeries, thetaSph_zero_eq_thetaSeries,
    ZLattice.thetaSeries_orthSum]

variable {L : Submodule ℤ E} {M : Submodule ℤ F} {M' : Submodule ℤ G}

/-- `id ⊕ φ : L ⊕ M → L ⊕ M'`. -/
noncomputable def orthSumMapRight (L : Submodule ℤ E) (φ : M →ₗ[ℤ] M') :
    ZLattice.orthSum L M →ₗ[ℤ] ZLattice.orthSum L M' :=
  (ZLattice.orthSumEquivProd L M').symm.toLinearMap ∘ₗ (LinearMap.prodMap LinearMap.id φ) ∘ₗ
    (ZLattice.orthSumEquivProd L M).toLinearMap

theorem coe_orthSumMapRight (φ : M →ₗ[ℤ] M') (z : ZLattice.orthSum L M) :
    ((orthSumMapRight L φ z : ZLattice.orthSum L M') : WithLp 2 (E × G)) =
      WithLp.toLp 2 ((z : WithLp 2 (E × F)).fst, ((φ (ZLattice.orthSumEquivProd L M z).2 : M') : G)) :=
  rfl

theorem orthSumEquivProd_orthSumMapRight (φ : M →ₗ[ℤ] M') (z : ZLattice.orthSum L M) :
    ZLattice.orthSumEquivProd L M' (orthSumMapRight L φ z) =
      ((ZLattice.orthSumEquivProd L M z).1, φ (ZLattice.orthSumEquivProd L M z).2) := by
  simp [orthSumMapRight]

theorem ModIsometry.mapRight {c : ℕ} {φ : M →ₗ[ℤ] M'} (h : ModIsometry M M' c φ) :
    ModIsometry (ZLattice.orthSum L M) (ZLattice.orthSum L M') c (orthSumMapRight L φ) where
  norm_sq z := by
    obtain ⟨m, hm⟩ := h.norm_sq (ZLattice.orthSumEquivProd L M z).2
    refine ⟨m, ?_⟩
    rw [coe_orthSumMapRight, WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd]
    rw [← hm, ZLattice.coe_orthSumEquivProd_apply_snd]
    ring
  surj y := by
    obtain ⟨x₂, w₂, hw⟩ := h.surj (ZLattice.orthSumEquivProd L M' y).2
    refine ⟨(ZLattice.orthSumEquivProd L M).symm ((ZLattice.orthSumEquivProd L M' y).1, x₂),
      (ZLattice.orthSumEquivProd L M').symm (0, w₂), ?_⟩
    apply (ZLattice.orthSumEquivProd L M').injective
    rw [map_add, map_nsmul]
    rw [orthSumEquivProd_orthSumMapRight, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    ext1
    · simp
    · simpa using hw
  inj x := by
    rintro ⟨w, hw⟩
    have hw' := congrArg (ZLattice.orthSumEquivProd L M') hw
    rw [orthSumEquivProd_orthSumMapRight, map_nsmul] at hw'
    obtain ⟨v₂, hv₂⟩ := h.inj _ ⟨_, (Prod.ext_iff.mp hw').2⟩
    refine ⟨(ZLattice.orthSumEquivProd L M).symm ((ZLattice.orthSumEquivProd L M' w).1, v₂), ?_⟩
    apply (ZLattice.orthSumEquivProd L M).injective
    rw [map_nsmul, LinearEquiv.apply_symm_apply]
    ext1
    · exact (Prod.ext_iff.mp hw').1
    · exact hv₂

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace G] [BorelSpace G] [DiscreteTopology M] [IsZLattice ℝ M]
  [DiscreteTopology M'] [IsZLattice ℝ M']

/-- **`L ⊕ M` and `L ⊕ M'` are in one genus when `M` and `M'` are.** -/
theorem SameGenus.orthSum_left (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (h : SameGenus M M') : SameGenus (ZLattice.orthSum L M) (ZLattice.orthSum L M') where
  covolume_eq := by rw [ZLattice.covolume_orthSum, ZLattice.covolume_orthSum, h.covolume_eq]
  modIso c hc := by
    obtain ⟨φ, hφ⟩ := h.modIso c hc
    exact ⟨orthSumMapRight L φ, hφ.mapRight⟩

end OrthSum

end ModularFormsKB.ThetaGenus
