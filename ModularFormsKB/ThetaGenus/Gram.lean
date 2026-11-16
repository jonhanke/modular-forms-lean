import ModularFormsKB.ThetaGenus.Cusp

/-!
# Miyake §4.9 and headline H5 in Gram-matrix form

Indices are 0-based (`Fin n`).

**Gram convention** (the Hessian convention of a companion library on quadratic forms; not yet reviewed). A positive definite integral quadratic form
is `Q(x) = ∑_{i ≤ j} c_{ij} x_i x_j`. Its **Hessian** `H = (∂²Q/∂x_i∂x_j)` is an even symmetric
integer matrix: `xᵀ H x = 2 Q(x)` (`gramNorm H x`).
The rational Gram matrix of the quadratic form is `F = H / 2`. The theta series is
`θ_H(τ) = ∑_{x ∈ ℤⁿ} q^{Q(x)} = ∑_x exp (π i xᵀHx τ)` (`thetaGram H`). **Level and character are
stated through `H`**: `N` is admissible when `N H⁻¹` is an even integer matrix (`IsGramLevel H N`;
the least such `N` is the level of `Q`), and the character is a Kronecker symbol of `det H`.

**Lattice bridge.** `IsEvenGram H` (symmetric, even diagonal, positive definite) gives a basis `b` of
`ℝⁿ` with `⟪b_i, b_j⟫ = H_ij` (`exists_gramBasis`), hence an even lattice `gramLattice hH` with
`θ_{gramLattice} = θ_H` (`thetaSph_gramLattice`), level dividing every admissible `N`
(`level_gramLattice_dvd`) and discriminant group of order `det H`
(`card_discriminantGroup_gramLattice`).

**Miyake, Theorem 4.9.3 and Corollary 4.9.4, Gram form.**
- `thetaGram_slash_of_mem_Gamma0`: `n = 2k`, `A ∈ Γ₀(N)`:
  `θ_H ∣[k] A = ((-1)^k det H / d) θ_H` (Kronecker symbol).
- `exists_modularForm_thetaGram`: `n = 2k`: `θ_H ∈ M_k(Γ₁(N))`.
- `exists_thetaGram_mem_halfIntModularForms`: `n = 2k + 1`, `4N` admissible:
  `θ_H ∈ M_{k+1/2}(4N, χ)` with `χ(d) = (2 det H / d)` for odd `d > 0` prime to `4N`.

**Headline H5, Gram form.** `GramSameGenus H H'` (same determinant; for every `c ≥ 1` an
integer matrix `U` invertible mod `c` with `Q'(Ux) ≡ Q(x) mod c`, i.e. `x ↦ Ux` is an isometry
`ℤⁿ/c → ℤⁿ/c`) implies `θ_H - θ_{H'}` is a cusp form: `gramSameGenus_exists_cuspForm` (even `n`),
`gramSameGenus_thetaGram_sub_mem_halfIntCuspForms` (odd `n`).
`gramSameGenus_of_common_sublattices` gives `GramSameGenus` from two common sublattices of coprime
indices (used for Gross's forms, `Gross.lean`).
-/

open Complex Module Filter Topology
open scoped Real RealInnerProductSpace ModularForm UpperHalfPlane MatrixGroups Matrix

set_option linter.unusedSectionVars false

namespace ModularFormsKB.ThetaGenus

open ModularFormsKB.Miyake.Sec4_9

variable {n : ℕ}

/-! ### Definitions in Gram-matrix form -/

/-- `xᵀ H x`, which is `2 Q(x)` for the Hessian `H` of `Q`. -/
def gramNorm (H : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) : ℤ := x ⬝ᵥ (H *ᵥ x)

/-- **`H` is the Hessian of a positive definite integral quadratic form**: symmetric, even diagonal,
positive definite. -/
structure IsEvenGram (H : Matrix (Fin n) (Fin n) ℤ) : Prop where
  symm : H.transpose = H
  even_diag : ∀ i, Even (H i i)
  posDef : (H.map (Int.cast : ℤ → ℝ)).PosDef

/-- **The theta series** `θ_H(τ) = ∑_{x ∈ ℤⁿ} exp (π i xᵀHx τ) = ∑_x q^{Q(x)}`. -/
noncomputable def thetaGram (H : Matrix (Fin n) (Fin n) ℤ) (τ : ℍ) : ℂ :=
  ∑' x : Fin n → ℤ, cexp (π * I * (gramNorm H x : ℂ) * τ)

/-- **`N` is an admissible level for `H`**: `N H⁻¹` is an even integer matrix, i.e. `H H' = N · 1`
for an integer matrix `H'` with even diagonal. -/
def IsGramLevel (H : Matrix (Fin n) (Fin n) ℤ) (N : ℕ) : Prop :=
  ∃ H' : Matrix (Fin n) (Fin n) ℤ, H * H' = (N : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) ∧
    ∀ i, Even (H' i i)

/-- **`H` and `H'` are in one genus** (congruence form): `det H = det H'`, and for every `c ≥ 1` an
integer matrix `U`, invertible mod `c`, with `xᵀ(UᵀH'U)x ≡ xᵀHx mod 2c` (i.e. `Q'(Ux) ≡ Q(x) mod c`). -/
def GramSameGenus (H H' : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  H.det = H'.det ∧ ∀ c : ℕ, 0 < c → ∃ U : Matrix (Fin n) (Fin n) ℤ,
    IsUnit ((U.det : ℤ) : ZMod c) ∧ ∀ x, gramNorm H' (U *ᵥ x) ≡ gramNorm H x [ZMOD 2 * c]

/-! ### The lattice bridge -/

variable {H : Matrix (Fin n) (Fin n) ℤ}

section RealGram

open scoped MatrixOrder

theorem exists_gramBasis_real (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) :
    ∃ b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)), ∀ i j, ⟪b i, b j⟫ = H i j := by
  classical
  have hs : H.PosSemidef := hH.posSemidef
  set S := CFC.sqrt H with hS
  have hSS : S * S = H := CFC.sqrt_mul_sqrt_self H hs.nonneg
  have hSh : S.IsHermitian := by simpa using (CFC.sqrt_nonneg H).1
  have hST : S.transpose = S := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hSh.eq
  have hdet : IsUnit S.det := by
    have h1 : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit
    rw [← hSS, Matrix.det_mul] at h1
    exact isUnit_of_mul_isUnit_left h1
  let e : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (Matrix.toLinearEquiv' S
      ((Matrix.isUnit_iff_isUnit_det _).mpr hdet).nonempty_invertible.some).trans
      (WithLp.linearEquiv 2 ℝ _).symm
  refine ⟨(Pi.basisFun ℝ (Fin n)).map e, fun i j => ?_⟩
  simp [e, EuclideanSpace.inner_eq_star_dotProduct]
  show (S *ᵥ Pi.single j 1) ⬝ᵥ (S *ᵥ Pi.single i 1) = H i j
  have hsy : ∀ a b, S a b = S b a := fun a b => by
    have := congrFun (congrFun hST b) a
    simpa using this
  rw [← hSS, Matrix.mul_apply]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hsy i k]
  ring

end RealGram

/-- A positive definite `H` is the Gram matrix of a basis of `ℝⁿ`. -/
theorem exists_gramBasis (hH : IsEvenGram H) :
    ∃ b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)), ∀ i j, ⟪b i, b j⟫ = (H i j : ℝ) :=
  exists_gramBasis_real _ hH.posDef

/-- A chosen basis with Gram matrix `H`. -/
noncomputable def gramBasis (hH : IsEvenGram H) : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  Classical.choose (exists_gramBasis hH)

theorem inner_gramBasis (hH : IsEvenGram H) (i j : Fin n) :
    ⟪gramBasis hH i, gramBasis hH j⟫ = (H i j : ℝ) :=
  Classical.choose_spec (exists_gramBasis hH) i j

/-- **The lattice of `H`**: the `ℤ`-span of `gramBasis hH`. -/
noncomputable abbrev gramLattice (hH : IsEvenGram H) : Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℤ (Set.range (gramBasis hH))

theorem sum_sum_even_of_symm (f : Fin n → Fin n → ℤ) (hf : ∀ i j, f i j = f j i)
    (hd : ∀ i, Even (f i i)) : Even (∑ i, ∑ j, f i j) := by
  have h1 : ∀ i, ∑ j, f i j =
      ∑ j, (if j < i then f i j else 0) + f i i + ∑ j, (if i < j then f i j else 0) := by
    intro i
    have : ∀ j, f i j = (if j < i then f i j else 0) + (if i = j then f i j else 0) +
        (if i < j then f i j else 0) := by
      intro j
      rcases lt_trichotomy i j with h | h | h
      · simp [h, h.ne, not_lt.mpr h.le]
      · subst h; simp
      · simp [h, h.ne', not_lt.mpr h.le]
    rw [Finset.sum_congr rfl (fun j _ ↦ this j), Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp
  have h2 : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    split_ifs
    · exact hf _ _
    · rfl
  have hD : Even (∑ i, f i i) := Finset.sum_induction _ Even (fun _ _ ↦ Even.add) ⟨0, rfl⟩
    (fun i _ ↦ hd i)
  rw [Finset.sum_congr rfl fun i _ ↦ h1 i, Finset.sum_add_distrib, Finset.sum_add_distrib, h2,
    add_right_comm]
  exact Even.add ⟨_, rfl⟩ hD

theorem even_gramNorm (hs : H.transpose = H) (he : ∀ i, Even (H i i)) (x : Fin n → ℤ) :
    Even (gramNorm H x) := by
  have : gramNorm H x = ∑ i, ∑ j, x i * H i j * x j := by
    simp [gramNorm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [this]
  refine sum_sum_even_of_symm _ (fun i j ↦ ?_) (fun i ↦ ?_)
  · have := congrFun (congrFun hs j) i
    simp only [Matrix.transpose_apply] at this
    rw [this]; ring
  · obtain ⟨m, hm⟩ := he i
    exact ⟨x i * m * x i, by rw [hm]; ring⟩

/-- The `ℤ`-basis of `gramLattice hH` induced by `gramBasis hH`. -/
noncomputable def gramZBasis (hH : IsEvenGram H) : Module.Basis (Fin n) ℤ (gramLattice hH) :=
  Module.Basis.span ((gramBasis hH).linearIndependent.restrict_scalars' ℤ)

/-- Coordinates: `ℤⁿ ≃ gramLattice hH`. -/
noncomputable def gramEquiv (hH : IsEvenGram H) : (Fin n → ℤ) ≃ₗ[ℤ] gramLattice hH :=
  (gramZBasis hH).equivFun.symm

theorem coe_gramEquiv (hH : IsEvenGram H) (x : Fin n → ℤ) :
    ((gramEquiv hH x : gramLattice hH) : EuclideanSpace ℝ (Fin n)) =
      ∑ i, (x i : ℝ) • gramBasis hH i := by
  simp [gramEquiv, gramZBasis, Module.Basis.equivFun_symm_apply,
    Int.cast_smul_eq_zsmul]

theorem norm_sq_gramEquiv (hH : IsEvenGram H) (x : Fin n → ℤ) :
    ‖((gramEquiv hH x : gramLattice hH) : EuclideanSpace ℝ (Fin n))‖ ^ 2 = (gramNorm H x : ℝ) := by
  rw [coe_gramEquiv, ← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, inner_gramBasis]
  simp [gramNorm, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  have hs : H j i = H i j := by simpa using congrFun (congrFun hH.symm i) j
  rw [hs]
  ring

theorem isEven_gramLattice (hH : IsEvenGram H) : ZLattice.IsEven (gramLattice hH) := by
  intro v hv
  obtain ⟨x, hx⟩ := (gramEquiv hH).surjective ⟨v, hv⟩
  obtain ⟨m, hm⟩ := even_gramNorm hH.symm hH.even_diag x
  refine ⟨m, ?_⟩
  have hv' : v = ((gramEquiv hH x : gramLattice hH) : EuclideanSpace ℝ (Fin n)) := by rw [hx]
  rw [hv', norm_sq_gramEquiv, hm]
  push_cast; ring

/-- **`θ` of the lattice of `H` is `θ_H`.** -/
theorem thetaSph_gramLattice (hH : IsEvenGram H) :
    thetaSph (gramLattice hH) 0 0 0 0 = thetaGram H := by
  funext τ
  rw [thetaSph, thetaW_apply, thetaGram, ← (gramEquiv hH).toEquiv.tsum_eq]
  refine tsum_congr fun x ↦ ?_
  simp only [LinearEquiv.coe_toEquiv, zero_add, pow_zero, one_mul, norm_sq_gramEquiv]
  push_cast
  rfl

theorem gram_gramZBasis (hH : IsEvenGram H) :
    Matrix.gram ℝ (fun i ↦ ((gramZBasis hH i : gramLattice hH) : EuclideanSpace ℝ (Fin n))) =
      H.map (Int.cast : ℤ → ℝ) := by
  ext i j
  simp [Matrix.gram_apply, gramZBasis, inner_gramBasis]

theorem level_gramLattice_dvd (hH : IsEvenGram H) {N : ℕ} (hN : IsGramLevel H N) :
    ZLattice.level (gramLattice hH) ∣ N := by
  obtain ⟨H', hHH', hev⟩ := hN
  rw [ZLattice.level_dvd_iff_gram (isEven_gramLattice hH).isIntegral (gramZBasis hH) N]
  refine ⟨H', hev, ?_⟩
  rw [gram_gramZBasis]
  have hdet : IsUnit (H.map (Int.cast : ℤ → ℝ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hH.posDef.isUnit
  have h1 : H.map (Int.cast : ℤ → ℝ) * H'.map (Int.cast : ℤ → ℝ) = (N : ℝ) • 1 := by
    ext i j
    have h2 := congrArg (Int.cast : ℤ → ℝ) (congrFun (congrFun hHH' i) j)
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply] at h2 ⊢
    push_cast at h2
    rw [h2]
    split_ifs <;> simp
  calc H'.map (Int.cast : ℤ → ℝ)
      = (H.map (Int.cast : ℤ → ℝ))⁻¹ * (H.map (Int.cast : ℤ → ℝ) * H'.map (Int.cast : ℤ → ℝ)) := by
        rw [← mul_assoc, Matrix.nonsing_inv_mul _ hdet, one_mul]
    _ = (N : ℝ) • (H.map (Int.cast : ℤ → ℝ))⁻¹ := by
        rw [h1, Matrix.mul_smul, mul_one]

theorem card_discriminantGroup_gramLattice (hH : IsEvenGram H) :
    (Nat.card (ZLattice.DiscriminantGroup (gramLattice hH)) : ℤ) = H.det := by
  have h1 := (isEven_gramLattice hH).isIntegral.det_eq_card_discriminantGroup
  rw [ZLattice.det_eq_det_gram _ (gramZBasis hH), gram_gramZBasis, ← Int.cast_det] at h1
  exact_mod_cast h1.symm

theorem det_gramLattice (hH : IsEvenGram H) : ZLattice.det (gramLattice hH) = (H.det : ℝ) := by
  rw [ZLattice.det_eq_det_gram _ (gramZBasis hH), gram_gramZBasis, ← Int.cast_det]

/-- An integer matrix invertible modulo `c` has an integer inverse modulo `c`. -/
theorem exists_inv_mod (U : Matrix (Fin n) (Fin n) ℤ) {c : ℕ}
    (hU : IsUnit ((U.det : ℤ) : ZMod c)) :
    ∃ (W : Matrix (Fin n) (Fin n) ℤ) (t : ℤ),
      U * W = (1 + (c : ℤ) * t) • (1 : Matrix (Fin n) (Fin n) ℤ) ∧
      W * U = (1 + (c : ℤ) * t) • (1 : Matrix (Fin n) (Fin n) ℤ) := by
  obtain ⟨u, v, huv⟩ := (ZMod.isUnit_intCast_iff_isCoprime _ _).mp hU
  have h1 : v * U.det = 1 + (c : ℤ) * (-u) := by linear_combination huv
  refine ⟨v • U.adjugate, -u, ?_, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, ← h1]
  · rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, ← h1]

theorem sameGenus_gramLattice {H' : Matrix (Fin n) (Fin n) ℤ} (hH : IsEvenGram H)
    (hH' : IsEvenGram H') (h : GramSameGenus H H') :
    SameGenus (gramLattice hH) (gramLattice hH') := by
  refine ⟨?_, fun c hc ↦ ?_⟩
  · have h1 : ZLattice.det (gramLattice hH) = ZLattice.det (gramLattice hH') := by
      rw [det_gramLattice, det_gramLattice, h.1]
    rw [ZLattice.det_def, ZLattice.det_def] at h1
    exact (sq_eq_sq₀ (ZLattice.covolume_pos _ _).le (ZLattice.covolume_pos _ _).le).mp h1
  obtain ⟨U, hU, hmod⟩ := h.2 c hc
  obtain ⟨W, t, hUW, hWU⟩ := exists_inv_mod U hU
  let φ : gramLattice hH →ₗ[ℤ] gramLattice hH' :=
    (gramEquiv hH').toLinearMap ∘ₗ Matrix.mulVecLin U ∘ₗ (gramEquiv hH).symm.toLinearMap
  have hφ : ∀ y, φ (gramEquiv hH y) = gramEquiv hH' (U *ᵥ y) := by
    intro y; simp [φ]
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨y, rfl⟩ := (gramEquiv hH).surjective x
    rw [hφ, norm_sq_gramEquiv, norm_sq_gramEquiv]
    obtain ⟨m, hm⟩ := Int.modEq_iff_dvd.mp (hmod y)
    refine ⟨-m, ?_⟩
    have : ((gramNorm H y : ℤ) : ℝ) - (gramNorm H' (U *ᵥ y) : ℤ) = 2 * c * m := by
      exact_mod_cast hm
    push_cast
    linarith
  · intro y
    obtain ⟨z, rfl⟩ := (gramEquiv hH').surjective y
    refine ⟨gramEquiv hH (W *ᵥ z), gramEquiv hH' (-t • z), ?_⟩
    rw [hφ, ← map_nsmul, ← map_add]
    congr 1
    rw [Matrix.mulVec_mulVec, hUW, Matrix.smul_mulVec, Matrix.one_mulVec, ← Nat.cast_smul_eq_nsmul ℤ]
    simp only [smul_smul, add_smul, one_smul, neg_smul, smul_neg]
    abel
  · intro x ⟨w, hw⟩
    obtain ⟨y, rfl⟩ := (gramEquiv hH).surjective x
    obtain ⟨w', rfl⟩ := (gramEquiv hH').surjective w
    rw [hφ, ← map_nsmul] at hw
    have hw' := (gramEquiv hH').injective hw
    refine ⟨gramEquiv hH (W *ᵥ w' - t • y), ?_⟩
    rw [← map_nsmul]
    congr 1
    have h2 : W *ᵥ (U *ᵥ y) = y + ((c : ℤ) * t) • y := by
      rw [Matrix.mulVec_mulVec, hWU, Matrix.smul_mulVec, Matrix.one_mulVec, add_smul, one_smul]
    rw [hw', Matrix.mulVec_smul] at h2
    ext i
    have h3 := congrFun h2 i
    simp at h3 ⊢
    linarith

theorem gramNorm_mulVec (H U : Matrix (Fin n) (Fin n) ℤ) (y : Fin n → ℤ) :
    gramNorm H (U *ᵥ y) = gramNorm (U.transpose * H * U) y := by
  unfold gramNorm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  conv_rhs => rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem gramNorm_mulVec_modEq (hs : H.transpose = H) (he : ∀ i, Even (H i i))
    {M N E : Matrix (Fin n) (Fin n) ℤ} {c : ℕ} (hME : M = N + (c : ℤ) • E) (x : Fin n → ℤ) :
    gramNorm H (M *ᵥ x) ≡ gramNorm H (N *ᵥ x) [ZMOD 2 * c] := by
  set y := N *ᵥ x
  set z := E *ᵥ x
  have hM : M *ᵥ x = y + (c : ℤ) • z := by
    rw [hME, Matrix.add_mulVec, Matrix.smul_mulVec]
  have hsym : z ⬝ᵥ (H *ᵥ y) = y ⬝ᵥ (H *ᵥ z) := by
    rw [Matrix.dotProduct_mulVec]
    conv_lhs => rw [← hs, Matrix.vecMul_transpose]
    exact dotProduct_comm _ _
  obtain ⟨m, hm⟩ := even_gramNorm hs he z
  have hexp : gramNorm H (y + (c : ℤ) • z) = gramNorm H y + 2 * c * (y ⬝ᵥ (H *ᵥ z)) +
      (c : ℤ) ^ 2 * gramNorm H z := by
    unfold gramNorm
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [hsym]
    ring
  rw [hM, hexp]
  refine (Int.modEq_iff_dvd.mpr ⟨(y ⬝ᵥ (H *ᵥ z)) + c * m, ?_⟩).symm
  rw [hm]
  ring

/-- The property "`H` and `H'` are isometric modulo `c`", as in `GramSameGenus`. -/
def GenusMod (H H' : Matrix (Fin n) (Fin n) ℤ) (c : ℕ) : Prop :=
  ∃ U : Matrix (Fin n) (Fin n) ℤ, IsUnit ((U.det : ℤ) : ZMod c) ∧
    ∀ x, gramNorm H' (U *ᵥ x) ≡ gramNorm H x [ZMOD 2 * c]

theorem genusMod_of_coprime {H' : Matrix (Fin n) (Fin n) ℤ}
    (hs : H.transpose = H) (he : ∀ i, Even (H i i))
    {U₁ U₂ : Matrix (Fin n) (Fin n) ℤ} (hU : U₁.transpose * H * U₁ = U₂.transpose * H' * U₂)
    {c : ℕ} (hc : IsCoprime (U₁.det * U₂.det) (c : ℤ)) : GenusMod H H' c := by
  have h1 : IsCoprime U₁.det (c : ℤ) := hc.of_mul_left_left
  have h2 : IsCoprime U₂.det (c : ℤ) := hc.of_mul_left_right
  obtain ⟨W, t, hUW, hWU⟩ := exists_inv_mod U₁ ((ZMod.isUnit_intCast_iff_isCoprime _ _).mpr h1.symm)
  refine ⟨U₂ * W, ?_, fun x ↦ ?_⟩
  · rw [ZMod.isUnit_intCast_iff_isCoprime, Matrix.det_mul]
    refine IsCoprime.mul_right h2.symm ?_
    have h3 : IsCoprime (1 + (c : ℤ) * t) (c : ℤ) := ⟨1, -t, by ring⟩
    have h4 : W.det * U₁.det = (1 + (c : ℤ) * t) ^ n := by
      rw [← Matrix.det_mul, hWU, Matrix.det_smul]; simp
    have h5 : IsCoprime (W.det * U₁.det) (c : ℤ) := h4 ▸ h3.pow_left
    exact h5.of_mul_left_left.symm
  · rw [← Matrix.mulVec_mulVec, gramNorm_mulVec, ← hU, ← gramNorm_mulVec, Matrix.mulVec_mulVec]
    have := gramNorm_mulVec_modEq hs he (M := U₁ * W) (N := 1) (E := t • 1) (c := c)
      (by rw [hUW, smul_smul, add_smul, one_smul, mul_comm]) x
    simpa using this

theorem det_cast_eq {c : ℕ} {U N E : Matrix (Fin n) (Fin n) ℤ} (h : U = N + (c : ℤ) • E) :
    ((U.det : ℤ) : ZMod c) = ((N.det : ℤ) : ZMod c) := by
  rw [Int.cast_det, Int.cast_det]
  congr 1
  ext i j
  simp only [Matrix.map_apply, h, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_add,
    Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]

theorem modEq_two_mul_mul {a b : ℤ} {c₁ c₂ : ℕ} (hc : IsCoprime (c₁ : ℤ) (c₂ : ℤ))
    (h1 : a ≡ b [ZMOD 2 * c₁]) (h2 : a ≡ b [ZMOD 2 * c₂]) : a ≡ b [ZMOD 2 * ((c₁ * c₂ : ℕ) : ℤ)] := by
  obtain ⟨k₁, hk₁⟩ := Int.modEq_iff_dvd.mp h1
  obtain ⟨k₂, hk₂⟩ := Int.modEq_iff_dvd.mp h2
  have hk : (c₁ : ℤ) * k₁ = c₂ * k₂ := by linarith
  have d1 : (c₁ : ℤ) ∣ c₂ * k₂ := ⟨k₁, hk.symm⟩
  have d2 : (c₁ : ℤ) ∣ k₂ := hc.dvd_of_dvd_mul_left d1
  obtain ⟨l, hl⟩ := d2
  refine Int.modEq_iff_dvd.mpr ⟨l, ?_⟩
  rw [hk₂, hl]; push_cast; ring

theorem genusMod_mul {H' : Matrix (Fin n) (Fin n) ℤ} (hs' : H'.transpose = H')
    (he' : ∀ i, Even (H' i i)) {c₁ c₂ : ℕ} (hc : IsCoprime (c₁ : ℤ) (c₂ : ℤ))
    (h₁ : GenusMod H H' c₁) (h₂ : GenusMod H H' c₂) : GenusMod H H' (c₁ * c₂) := by
  obtain ⟨Ua, hua, hna⟩ := h₁
  obtain ⟨Ub, hub, hnb⟩ := h₂
  obtain ⟨u, v, huv⟩ := id hc
  set U : Matrix (Fin n) (Fin n) ℤ := (v * c₂) • Ua + (u * c₁) • Ub with hUdef
  have e₁ : U = Ua + (c₁ : ℤ) • (u • (Ub - Ua)) := by
    rw [hUdef]; ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    linear_combination (Ua i j) * huv
  have e₂ : U = Ub + (c₂ : ℤ) • (v • (Ua - Ub)) := by
    rw [hUdef]; ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    linear_combination (Ub i j) * huv
  refine ⟨U, ?_, fun x ↦ ?_⟩
  · rw [ZMod.isUnit_intCast_iff_isCoprime]
    push_cast
    refine IsCoprime.mul_left ?_ ?_
    · rw [← ZMod.isUnit_intCast_iff_isCoprime, det_cast_eq e₁]; exact hua
    · rw [← ZMod.isUnit_intCast_iff_isCoprime, det_cast_eq e₂]; exact hub
  · have a1 : gramNorm H' (U *ᵥ x) ≡ gramNorm H x [ZMOD 2 * c₁] :=
      (gramNorm_mulVec_modEq hs' he' e₁ x).trans (hna x)
    have a2 : gramNorm H' (U *ᵥ x) ≡ gramNorm H x [ZMOD 2 * c₂] :=
      (gramNorm_mulVec_modEq hs' he' e₂ x).trans (hnb x)
    exact modEq_two_mul_mul hc a1 a2

theorem exists_split (a : ℕ) : ∀ c : ℕ, 0 < c → ∃ c₁ c₂ : ℕ, c₁ * c₂ = c ∧ Nat.Coprime c₁ a ∧
    ∀ p, p.Prime → p ∣ c₂ → p ∣ a := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hc
    by_cases h : Nat.Coprime c a
    · refine ⟨c, 1, by simp, h, fun p hp hd ↦ ?_⟩
      exact absurd (Nat.dvd_one.mp hd) hp.one_lt.ne'
    · obtain ⟨p, hp, hpc, hpa⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
      obtain ⟨c', rfl⟩ := hpc
      have hc' : 0 < c' := Nat.pos_of_mul_pos_left hc
      have hlt : c' < p * c' := lt_mul_left hc' hp.one_lt
      obtain ⟨c₁, c₂, h1, h2, h3⟩ := ih c' hlt hc'
      refine ⟨c₁, p * c₂, by rw [← mul_assoc, mul_comm c₁ p, mul_assoc, h1], h2,
        fun q hq hqd ↦ ?_⟩
      rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
      · rw [(Nat.prime_dvd_prime_iff_eq hq hp).mp h]; exact hpa
      · exact h3 q hq h

/-- **`GramSameGenus` from two common sublattices of coprime indices**: if
`U₁ᵀ H U₁ = U₂ᵀ H' U₂` and `V₁ᵀ H V₁ = V₂ᵀ H' V₂` with `det U₁ det U₂` prime to `det V₁ det V₂`,
`H`, `H'` symmetric with even diagonal and `det H = det H'`, then `H` and `H'` are in one genus.
(For `c` prime to `det U₁ det U₂`, `U = U₂ U₁⁻¹ mod c` works; a general `c` is the product of a part
prime to `det U₁ det U₂` and a part prime to `det V₁ det V₂`, and the Chinese remainder theorem
glues the two matrices.) -/
theorem gramSameGenus_of_common_sublattices {H' : Matrix (Fin n) (Fin n) ℤ}
    (hsymm : H.transpose = H) (heven : ∀ i, Even (H i i))
    (hsymm' : H'.transpose = H') (heven' : ∀ i, Even (H' i i)) (hdet : H.det = H'.det)
    {U₁ U₂ V₁ V₂ : Matrix (Fin n) (Fin n) ℤ}
    (hU : U₁.transpose * H * U₁ = U₂.transpose * H' * U₂)
    (hV : V₁.transpose * H * V₁ = V₂.transpose * H' * V₂)
    (hcop : IsCoprime (U₁.det * U₂.det) (V₁.det * V₂.det)) :
    GramSameGenus H H' := by
  refine ⟨hdet, fun c hc ↦ ?_⟩
  obtain ⟨c₁, c₂, hcc, hcop₁, hp⟩ := exists_split (U₁.det * U₂.det).natAbs c hc
  have hI₁ : IsCoprime (U₁.det * U₂.det) (c₁ : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
    simpa [Nat.coprime_comm] using hcop₁.symm
  have hcop₂ : Nat.Coprime c₂ (V₁.det * V₂.det).natAbs := by
    refine Nat.coprime_of_dvd fun p hp' hpc hpd ↦ ?_
    have h2 : (p : ℤ) ∣ U₁.det * U₂.det := Int.natCast_dvd.mpr (hp p hp' hpc)
    have h3 : (p : ℤ) ∣ V₁.det * V₂.det := Int.natCast_dvd.mpr hpd
    have h4 := hcop.isUnit_of_dvd' h2 h3
    have := Int.isUnit_iff_natAbs_eq.mp h4
    simp at this
    exact hp'.one_lt.ne' this
  have hI₂ : IsCoprime (V₁.det * V₂.det) (c₂ : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
    simpa using hcop₂.symm
  have hc12 : IsCoprime (c₁ : ℤ) (c₂ : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    refine Nat.coprime_of_dvd fun p hp' hp1 hp2 ↦ ?_
    exact hp'.one_lt.ne' ((Nat.Coprime.coprime_dvd_left hp1 hcop₁).eq_one_of_dvd (hp p hp' hp2))
  have := genusMod_mul hsymm' heven' hc12 (genusMod_of_coprime hsymm heven hU hI₁)
    (genusMod_of_coprime hsymm heven hV hI₂)
  rw [hcc] at this
  exact this

/-! ### Rows 37–38: Miyake §4.9 in Gram form -/

theorem finrank_euclideanSpace_fin' : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
  simp

/-- The odd-rank character of `gramLattice hH`, in Kronecker form `(2 det H / d)`. -/
theorem oddThetaCharOf_gram (hH : IsEvenGram H) {k : ℕ}
    (hk : finrank ℝ (EuclideanSpace ℝ (Fin n)) = 2 * k + 1) {N : ℕ}
    (hdvd : ZLattice.level (gramLattice hH) ∣ 4 * N)
    : ∀ d : ℕ, d.Coprime (4 * N) →
      oddThetaCharOf (isEven_gramLattice hH) hk 0 hdvd d = (jacobiSym (2 * H.det) d : ℂ) := by
  intro d hd
  rw [oddThetaCharOf_natCast _ _ _ _ hd, card_discriminantGroup_gramLattice]
  simp

/-- **Miyake, Theorem 4.9.3 (Gram form, even rank `n = 2k`)**: for `A ∈ Γ₀(N)`, `N` admissible,
`θ_H ∣[k] A = ((-1)^k det H / d) θ_H`. -/
@[kb "miyake1989" "Theorem 4.9.3 in Gram-matrix form: theta_H | A = ((-1)^k det H / d) theta_H on Gamma0(N), N H^-1 even integral"]
theorem thetaGram_slash_of_mem_Gamma0 (hH : IsEvenGram H) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN : IsGramLevel H N) {A : SL(2, ℤ)} (hA : A ∈ CongruenceSubgroup.Gamma0 N) :
    thetaGram H ∣[(k : ℤ)] A =
      (TauCeti.kroneckerSym ((-1) ^ k * H.det) (A 1 1) : ℂ) • thetaGram H := by
  have hL := isEven_gramLattice hH
  have hk : finrank ℝ (EuclideanSpace ℝ (Fin n)) = 2 * k := by rw [finrank_euclideanSpace_fin', hn]
  have hsph : IsSphericalDatum 0 (0 : EuclideanSpace ℝ (Fin n)) 0 := Or.inl zero_le_one
  have hdvd := level_gramLattice_dvd hH hN
  have hA' := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hA
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 (ZLattice.level (gramLattice hH)) := by
    rw [CongruenceSubgroup.mem_Gamma0_iff_dvd]
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hdvd) hA'
  have h := IsEvenSph.thetaSph_slash_of_mem_Gamma0 hL hk hsph hA0
  rw [thetaSph_gramLattice] at h
  have hcop : IsCoprime (A 1 1) (ZLattice.level (gramLattice hH) : ℤ) := by
    obtain ⟨s, hs⟩ := dvd_trans (Int.natCast_dvd_natCast.mpr hdvd) hA'
    have hdet := A.det_coe
    rw [Matrix.det_fin_two] at hdet
    exact ⟨A 0 0, -(A 0 1 * s), by linear_combination hdet + (A 0 1 : ℤ) * hs⟩
  have hc := hL.thetaCharacter_intCast (⟨k, by omega⟩ : Even (finrank ℝ (EuclideanSpace ℝ (Fin n))))
    hcop
  rw [hc, ZLattice.signedDiscr_of_finrank_eq _ hk, card_discriminantGroup_gramLattice] at h
  simpa using h

/-- **Miyake, Corollary 4.9.4 (Gram form, even rank)**: `θ_H ∈ M_k(Γ₁(N))`. -/
@[kb "miyake1989" "Corollary 4.9.4 in Gram-matrix form: theta_H is a modular form of weight n/2 on Gamma1(N)"]
theorem exists_modularForm_thetaGram (hH : IsEvenGram H) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN : IsGramLevel H N) :
    ∃ f : ModularForm ((CongruenceSubgroup.Gamma1 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k,
      ⇑f = thetaGram H := by
  have hL := isEven_gramLattice hH
  have hk : finrank ℝ (EuclideanSpace ℝ (Fin n)) = 2 * k := by rw [finrank_euclideanSpace_fin', hn]
  have hsph : IsSphericalDatum 0 (0 : EuclideanSpace ℝ (Fin n)) 0 := Or.inl zero_le_one
  have hdvd := level_gramLattice_dvd hH hN
  refine ⟨{ toFun := thetaSph (gramLattice hH) 0 0 0 0
            slash_action_eq' := ?_
            holo' := ?_
            bdd_at_cusps' := ?_ }, thetaSph_gramLattice hH⟩
  · intro A hA
    obtain ⟨A, hA, rfl⟩ := hA
    rw [← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← ModularForm.SL_slash,
      thetaSph_zero_slash_of_mem_Gamma1 hL hk hdvd hA]
  · exact mdifferentiable_thetaW _ (polyBounded_isoForm_pow 0 0 0) 0
  · intro c hc
    apply (OnePoint.isBoundedAt_iff_forall_SL2Z (hc.mono (Subgroup.map_le_range _ _))).mpr
    intro A _
    exact isBoundedAtImInfty_slash_thetaSph hL hk hsph A

/-- **Miyake, Theorem 4.9.3 (Gram form, odd rank `n = 2k + 1`)**: for `4N` admissible,
`θ_H ∈ M_{k+1/2}(4N, χ)` with `χ(d) = (2 det H / d)` (Jacobi symbol) on odd `d > 0` prime to `4N`. -/
@[kb "miyake1989" "Theorem 4.9.3 in Gram-matrix form, odd rank: theta_H in M_{n/2}(4N, chi), chi(d) = (2 det H / d)"]
theorem exists_thetaGram_mem_halfIntModularForms (hH : IsEvenGram H) {k : ℕ} (hn : n = 2 * k + 1)
    {N : ℕ} (hN : IsGramLevel H (4 * N)) :
    ∃ χ : DirichletCharacter ℂ (4 * N),
      (∀ d : ℕ, d.Coprime (4 * N) → χ d = (jacobiSym (2 * H.det) d : ℂ)) ∧
      (fun τ ↦ thetaGram H τ) ∈ HalfIntegral.halfIntModularForms k N χ := by
  have hL := isEven_gramLattice hH
  have hk : finrank ℝ (EuclideanSpace ℝ (Fin n)) = 2 * k + 1 := by
    rw [finrank_euclideanSpace_fin', hn]
  have hsph : IsSphericalDatum 0 (0 : EuclideanSpace ℝ (Fin n)) 0 := Or.inl zero_le_one
  have hdvd := level_gramLattice_dvd hH hN
  refine ⟨oddThetaCharOf hL hk 0 hdvd, oddThetaCharOf_gram hH hk hdvd, ?_⟩
  have h := thetaSph_mem_halfIntModularForms_of_dvd hL hk hsph hdvd
  rw [thetaSph_gramLattice] at h
  exact h

/-! ### Row 39: headline H5 in Gram form -/

/-- **Headline H5, Gram form, even rank `n = 2k`**: Hessians in one genus with a common admissible
level `N` have theta series differing by a cusp form of weight `k` on `Γ₁(N)`. -/
@[kb "siegel1935" "theta series of forms in one genus differ by a cusp form (Gram-matrix form, even rank)"]
theorem gramSameGenus_exists_cuspForm {H' : Matrix (Fin n) (Fin n) ℤ} (hH : IsEvenGram H)
    (hH' : IsEvenGram H') {k : ℕ} (hn : n = 2 * k) (h : GramSameGenus H H') {N : ℕ}
    (hN : IsGramLevel H N) (hN' : IsGramLevel H' N) :
    ∃ f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k,
      ⇑f = thetaGram H - thetaGram H' := by
  have hk : finrank ℝ (EuclideanSpace ℝ (Fin n)) = 2 * k := by rw [finrank_euclideanSpace_fin', hn]
  obtain ⟨f, hf⟩ := sameGenus_thetaSph_sub_cuspForm (sameGenus_gramLattice hH hH' h)
    (isEven_gramLattice hH) (isEven_gramLattice hH') hk hk (level_gramLattice_dvd hH hN)
    (level_gramLattice_dvd hH' hN')
  exact ⟨f, by rw [hf, thetaSph_gramLattice, thetaSph_gramLattice]⟩

/-- **Headline H5, Gram form, odd rank `n = 2k + 1`**: `θ_H - θ_{H'} ∈ S_{k+1/2}(4N, χ)`,
`χ(d) = (2 det H / d)`. -/
@[kb "siegel1935" "theta series of forms in one genus differ by a cusp form (Gram-matrix form, odd rank, half-integral weight)"]
theorem gramSameGenus_thetaGram_sub_mem_halfIntCuspForms {H' : Matrix (Fin n) (Fin n) ℤ}
    (hH : IsEvenGram H) (hH' : IsEvenGram H') {k : ℕ} (hn : n = 2 * k + 1) (h : GramSameGenus H H')
    {N : ℕ} [NeZero N] (hN : IsGramLevel H (4 * N)) (hN' : IsGramLevel H' (4 * N)) :
    ∃ χ : DirichletCharacter ℂ (4 * N),
      (∀ d : ℕ, d.Coprime (4 * N) → χ d = (jacobiSym (2 * H.det) d : ℂ)) ∧
      (fun τ ↦ thetaGram H τ - thetaGram H' τ) ∈ HalfIntegral.halfIntCuspForms k N χ := by
  have hk : finrank ℝ (EuclideanSpace ℝ (Fin n)) = 2 * k + 1 := by
    rw [finrank_euclideanSpace_fin', hn]
  have hdvd := level_gramLattice_dvd hH hN
  have h1 := sameGenus_thetaSph_sub_mem_halfIntCuspForms (sameGenus_gramLattice hH hH' h)
    (isEven_gramLattice hH) (isEven_gramLattice hH') hk hk hdvd (level_gramLattice_dvd hH' hN')
  refine ⟨oddThetaCharOf (isEven_gramLattice hH) hk 0 hdvd, oddThetaCharOf_gram hH hk hdvd, ?_⟩
  have e : (fun τ : ℍ ↦ thetaSph (gramLattice hH) 0 0 0 0 τ - thetaSph (gramLattice hH') 0 0 0 0 τ) =
      fun τ ↦ thetaGram H τ - thetaGram H' τ := by
    rw [thetaSph_gramLattice, thetaSph_gramLattice]
  rw [← e]
  exact h1

end ModularFormsKB.ThetaGenus
