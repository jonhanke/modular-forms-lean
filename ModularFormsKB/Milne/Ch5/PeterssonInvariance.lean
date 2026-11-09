import ModularFormsKB.Milne.Ch5.LevelOnePetersson
import ModularFormsKB.Milne.Ch5.Matrices
import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# Milne, Chapter 5: invariance of the Petersson product under $\mathrm{GL}_2(\mathbb Q)^+$ (Lemma 5.22)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf p. 76.

Milne states $\langle f|_k\alpha, g|_k\alpha\rangle = \langle f, g\rangle$ for cusp forms $f, g$ of weight $2k$ for
$\Gamma(1)$ and $\alpha \in \mathrm{GL}_2(\mathbb R)^+$, and explains that the left side is computed with respect to a
congruence subgroup $\Gamma'$ for which $f|_k\alpha$, $g|_k\alpha$ are modular, normalized by the index (the quotient of
the volumes of the fundamental domains). This needs $\Gamma(1) \cap \alpha^{-1}\Gamma(1)\alpha$ to have finite index,
which by Lemma 5.29 means that $\alpha$ is a scalar multiple of an integer matrix; Milne's $f|_k\alpha$ does not
change when $\alpha$ is multiplied by a scalar, so we take $\alpha$ integral. Here $\Gamma' = \Gamma(1) \cap
\alpha^{-1}\Gamma(1)\alpha$ (`translateLevel`), $f|_k\alpha = (\det\alpha)^{1-k}(f \mid_{2k} \alpha)$ is Mathlib's
`CuspForm.translate` rescaled (`milneTranslate`), and the normalized product is Tau Ceti's
`CuspForm.peterssonInnerCosets` divided by the index of $\Gamma'\cdot\{\pm 1\}$.

## Items
- Lemma 5.22 (`petersson_milneTranslate`).
- The consequence $\langle f|_k\alpha, g\rangle = \langle f, g|_k\alpha^{-1}\rangle$ is used through Tau Ceti's
  adjoint theory (`UpperHalfPlane.peterssonInner_slash_left_of_det_pos`) in Theorem 5.23.
-/

open UpperHalfPlane ModularForm Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped MatrixGroups ModularForm Pointwise

namespace ModularFormsKB.Milne

/-- $\Gamma(1) \cap \alpha^{-1}\Gamma(1)\alpha$, as a subgroup of $\mathrm{SL}_2(\mathbb Z)$. -/
noncomputable def translateLevel (α : GL (Fin 2) ℝ) : Subgroup SL(2, ℤ) :=
  (ConjAct.toConjAct α⁻¹ • 𝒮ℒ).comap (mapGL ℝ)

/-- Membership in `translateLevel`: $\alpha\gamma\alpha^{-1} \in \Gamma(1)$. -/
theorem mem_translateLevel (β : GL (Fin 2) ℝ) (γ : SL(2, ℤ)) :
    γ ∈ translateLevel β ↔ β * mapGL ℝ γ * β⁻¹ ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := by
  unfold translateLevel
  rw [Subgroup.mem_comap, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [ConjAct.toConjAct_smul]

/-- A matrix congruent to the identity mod `m` is `1 + m • N`. -/
theorem exists_eq_one_add_smul_of_mem_Gamma {m : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma m) :
    ∃ N : Matrix (Fin 2) (Fin 2) ℤ, (γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 + (m : ℤ) • N := by
  rw [Gamma_mem] at hγ
  obtain ⟨h00, h01, h10, h11⟩ := hγ
  have key : ∀ x y : ℤ, ((x : ZMod m) = (y : ZMod m)) → ∃ q, x = y + m * q := by
    intro x y h
    obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub y x m).mp h.symm
    exact ⟨q, by linarith⟩
  obtain ⟨q00, e00⟩ := key _ 1 (by simpa using h00)
  obtain ⟨q01, e01⟩ := key _ 0 (by simpa using h01)
  obtain ⟨q10, e10⟩ := key _ 0 (by simpa using h10)
  obtain ⟨q11, e11⟩ := key _ 1 (by simpa using h11)
  refine ⟨!![q00, q01; q10, q11], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]

/-- If `A` is an integer matrix of positive determinant `m` then `Γ(m)` lies in `translateLevel A`. -/
theorem Gamma_le_translateLevel {α : GL (Fin 2) ℝ} (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (α : Matrix (Fin 2) (Fin 2) ℝ) = A.map (Int.cast : ℤ → ℝ)) (hα : 0 < α.det.val) :
    Gamma (A.det.toNat) ≤ translateLevel α := by
  intro γ hγ
  obtain ⟨N, hN⟩ := exists_eq_one_add_smul_of_mem_Gamma hγ
  have hdetR : (α : Matrix (Fin 2) (Fin 2) ℝ).det = (A.det : ℝ) := by
    rw [hA]; exact (RingHom.map_det (Int.castRingHom ℝ) A).symm
  have hdpos : 0 < A.det := by
    have : (0 : ℝ) < (A.det : ℝ) := by rw [← hdetR]; exact hα
    exact_mod_cast this
  have hm : ((A.det.toNat : ℕ) : ℤ) = A.det := Int.toNat_of_nonneg hdpos.le
  rw [hm] at hN
  rw [mem_translateLevel]
  set X : Matrix (Fin 2) (Fin 2) ℤ := 1 + A * N * A.adjugate with hX
  have h1 : A * (γ : Matrix (Fin 2) (Fin 2) ℤ) = X * A := by
    rw [hN, hX, mul_add, add_mul, Matrix.mul_smul, Matrix.mul_assoc (A * N), Matrix.adjugate_mul,
      Matrix.mul_smul, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul]
  have hdetX : X.det = 1 := by
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul, γ.2] at h2
    have : A.det * (X.det - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · omega
    · linarith
  have hXR : (α : Matrix (Fin 2) (Fin 2) ℝ) * (mapGL ℝ γ : Matrix (Fin 2) (Fin 2) ℝ) *
      ((α⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = X.map (Int.cast : ℤ → ℝ) := by
    have h3 : (α : Matrix (Fin 2) (Fin 2) ℝ) * (mapGL ℝ γ : Matrix (Fin 2) (Fin 2) ℝ) =
        X.map (Int.cast : ℤ → ℝ) * (α : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [hA, mapGL_coe_matrix]
      have e := congrArg (RingHom.mapMatrix (Int.castRingHom ℝ)) h1
      rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_mul] at e
      exact e
    rw [h3, Matrix.mul_assoc]
    have : (α : Matrix (Fin 2) (Fin 2) ℝ) * ((α⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [this, Matrix.mul_one]
  let δ : SL(2, ℤ) := ⟨X, hdetX⟩
  refine ⟨δ, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hXR]
  exact (mapGL_coe_matrix δ).trans rfl

/-- For an integral $\alpha$ of positive determinant, $\Gamma(1) \cap \alpha^{-1}\Gamma(1)\alpha$ has finite index (it
contains $\Gamma(\det\alpha)$). -/
theorem translateLevel_finiteIndex {α : GL (Fin 2) ℝ} (hα : 0 < α.det.val)
    (hint : ∃ A : Matrix (Fin 2) (Fin 2) ℤ, (α : Matrix (Fin 2) (Fin 2) ℝ) = A.map (Int.cast : ℤ → ℝ)) :
    (translateLevel α).FiniteIndex := by
  obtain ⟨A, hA⟩ := hint
  have hdetR : (α : Matrix (Fin 2) (Fin 2) ℝ).det = (A.det : ℝ) := by
    rw [hA]; exact (RingHom.map_det (Int.castRingHom ℝ) A).symm
  have hdpos : 0 < A.det := by
    have : (0 : ℝ) < (A.det : ℝ) := by rw [← hdetR]; exact hα
    exact_mod_cast this
  have : NeZero (A.det.toNat) := ⟨by omega⟩
  exact Subgroup.finiteIndex_of_le (Gamma_le_translateLevel A hA hα)

theorem translateLevel_map_le (α : GL (Fin 2) ℝ) :
    (translateLevel α).map (mapGL ℝ) ≤ ConjAct.toConjAct α⁻¹ • 𝒮ℒ :=
  Subgroup.map_comap_le _ _

theorem mapGL_mem_range (u : SL(2, ℤ)) : mapGL ℝ u ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) :=
  MonoidHom.mem_range.mpr ⟨u, rfl⟩

/-- Left multiplication by an element of $\mathrm{SL}_2(\mathbb Z)$ does not change `translateLevel`. -/
theorem translateLevel_mapGL_mul (u : SL(2, ℤ)) (β : GL (Fin 2) ℝ) :
    translateLevel (mapGL ℝ u * β) = translateLevel β := by
  ext γ
  rw [mem_translateLevel, mem_translateLevel]
  have : mapGL ℝ u * β * mapGL ℝ γ * (mapGL ℝ u * β)⁻¹ =
      mapGL ℝ u * (β * mapGL ℝ γ * β⁻¹) * (mapGL ℝ u)⁻¹ := by group
  rw [this, Subgroup.mul_mem_cancel_right _ (Subgroup.inv_mem _ (mapGL_mem_range u)),
    Subgroup.mul_mem_cancel_left _ (mapGL_mem_range u)]

/-- Right multiplication by $v \in \mathrm{SL}_2(\mathbb Z)$ conjugates `translateLevel`, preserving the index. -/
theorem index_translateLevel_mul_mapGL (v : SL(2, ℤ)) (β : GL (Fin 2) ℝ) :
    (translateLevel (β * mapGL ℝ v)).index = (translateLevel β).index := by
  have h : translateLevel (β * mapGL ℝ v) = (translateLevel β).comap (MulAut.conj v).toMonoidHom := by
    ext γ
    rw [Subgroup.mem_comap, mem_translateLevel, mem_translateLevel]
    have : β * mapGL ℝ v * mapGL ℝ γ * (β * mapGL ℝ v)⁻¹ =
        β * mapGL ℝ (((MulAut.conj v).toMonoidHom) γ) * β⁻¹ := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, map_mul, map_inv]
      group
    rw [this]
  rw [h]
  exact Subgroup.index_comap_of_surjective _ (MulAut.conj v).surjective

/-- Multiplying by a central element does not change `translateLevel`. -/
theorem translateLevel_central_mul {z : GL (Fin 2) ℝ} (hz : z ∈ Subgroup.center (GL (Fin 2) ℝ))
    (β : GL (Fin 2) ℝ) : translateLevel (z * β) = translateLevel β := by
  ext γ
  rw [mem_translateLevel, mem_translateLevel]
  have h := Subgroup.mem_center_iff.mp hz
  have : z * β * mapGL ℝ γ * (z * β)⁻¹ = β * mapGL ℝ γ * β⁻¹ := by
    have e : z * β * mapGL ℝ γ * (z * β)⁻¹ = z * (β * mapGL ℝ γ * β⁻¹) * z⁻¹ := by group
    rw [e, mul_inv_eq_iff_eq_mul]
    exact (h _).symm
  rw [this]

/-- The diagonal element $\mathrm{diag}(a, d)$ of $\mathrm{GL}_2(\mathbb R)$. -/
noncomputable def diagGL (a d : ℝ) (ha : a ≠ 0) (hd : d ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![a, d])
    (by simp [ha, hd])

/-- Inverting a diagonal matrix does not change the index of `translateLevel` (conjugation by $S$ swaps the
entries, and scalars are central). -/
theorem index_translateLevel_diagGL_inv (a d : ℝ) (ha : a ≠ 0) (hd : d ≠ 0) :
    (translateLevel (diagGL a d ha hd)⁻¹).index = (translateLevel (diagGL a d ha hd)).index := by
  let w : SL(2, ℤ) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  let w' : SL(2, ℤ) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
  have hc : (a * d)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero ha hd)
  let z : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![(a * d)⁻¹, (a * d)⁻¹])
    (by simp [ha, hd])
  have hz : z ∈ Subgroup.center (GL (Fin 2) ℝ) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Units.ext
    have e : (Matrix.diagonal ![(a * d)⁻¹, (a * d)⁻¹] : Matrix (Fin 2) (Fin 2) ℝ) = (a * d)⁻¹ • 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    show (g : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.diagonal ![(a * d)⁻¹, (a * d)⁻¹] =
      Matrix.diagonal ![(a * d)⁻¹, (a * d)⁻¹] * (g : Matrix (Fin 2) (Fin 2) ℝ)
    rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  have key : (diagGL a d ha hd)⁻¹ = z * (mapGL ℝ w * diagGL a d ha hd * mapGL ℝ w') := by
    symm
    apply eq_inv_of_mul_eq_one_right
    apply Units.ext
    have e1 : ((diagGL a d ha hd : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, 0; 0, d] := by
      show Matrix.diagonal ![a, d] = _
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have e2 : ((z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(a * d)⁻¹, 0; 0, (a * d)⁻¹] := by
      show Matrix.diagonal ![(a * d)⁻¹, (a * d)⁻¹] = _
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have ew : ((mapGL ℝ w : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, 0] := by
      rw [mapGL_coe_matrix, map_apply_coe]; ext i j; fin_cases i <;> fin_cases j <;> simp [w]
    have ew' : ((mapGL ℝ w' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; -1, 0] := by
      rw [mapGL_coe_matrix, map_apply_coe]; ext i j; fin_cases i <;> fin_cases j <;> simp [w']
    simp only [Units.val_mul, Units.val_one, e1, e2, ew, ew', Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp
  rw [key, translateLevel_central_mul hz, index_translateLevel_mul_mapGL, translateLevel_mapGL_mul]

/-- **Key index equality.** For an integral $\alpha$ of positive determinant,
$[\Gamma(1) : \Gamma(1) \cap \alpha\Gamma(1)\alpha^{-1}] = [\Gamma(1) : \Gamma(1) \cap \alpha^{-1}\Gamma(1)\alpha]$
(Smith normal form, then conjugation by $S$). -/
theorem index_translateLevel_inv {α : GL (Fin 2) ℝ} (hα : 0 < α.det.val)
    (hint : ∃ A : Matrix (Fin 2) (Fin 2) ℤ, (α : Matrix (Fin 2) (Fin 2) ℝ) = A.map (Int.cast : ℤ → ℝ)) :
    (translateLevel α⁻¹).index = (translateLevel α).index := by
  obtain ⟨A, hA⟩ := hint
  have hdetR : (α : Matrix (Fin 2) (Fin 2) ℝ).det = (A.det : ℝ) := by
    rw [hA]; exact (RingHom.map_det (Int.castRingHom ℝ) A).symm
  have hdpos : 0 < A.det := by
    have : (0 : ℝ) < (A.det : ℝ) := by rw [← hdetR]; exact hα
    exact_mod_cast this
  have hn : 0 < A.det.toNat := by omega
  obtain ⟨⟨a, d⟩, ⟨-, hprod, U, V, hUV⟩, -⟩ :=
    exists_unique_elementaryDivisors hn A (Int.toNat_of_nonneg hdpos.le).symm
  simp only at hprod hUV
  have ha : a ≠ 0 := by rintro rfl; simp at hprod; omega
  have hd : d ≠ 0 := by rintro rfl; simp at hprod; omega
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have e1 : ((diagGL a d ha' hd' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.diagonal ![(a : ℝ), d] := rfl
  have hαeq : α = mapGL ℝ U * diagGL a d ha' hd' * mapGL ℝ V := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hA, hUV, mapGL_coe_matrix, mapGL_coe_matrix, map_apply_coe,
      map_apply_coe, e1]
    have e2 : (Matrix.diagonal ![(a : ℤ), (d : ℤ)]).map (Int.cast : ℤ → ℝ) =
        Matrix.diagonal ![(a : ℝ), d] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [← e2]
    show (Int.castRingHom ℝ).mapMatrix _ = (Int.castRingHom ℝ).mapMatrix _ * (Int.castRingHom ℝ).mapMatrix _ *
      (Int.castRingHom ℝ).mapMatrix _
    rw [← map_mul, ← map_mul]
  have h1 : (translateLevel α).index = (translateLevel (diagGL a d ha' hd')).index := by
    rw [hαeq, index_translateLevel_mul_mapGL, translateLevel_mapGL_mul]
  have h2 : (mapGL ℝ U * diagGL a d ha' hd' * mapGL ℝ V)⁻¹ =
      mapGL ℝ V⁻¹ * ((diagGL a d ha' hd')⁻¹ * mapGL ℝ U⁻¹) := by
    simp [mul_inv_rev, mul_assoc]
  rw [h1, hαeq, h2, translateLevel_mapGL_mul, index_translateLevel_mul_mapGL,
    index_translateLevel_diagGL_inv]

/-- `translateLevel` contains $-1$, so adjoining the centre changes nothing. -/
theorem withCenter_translateLevel (β : GL (Fin 2) ℝ) :
    (translateLevel β).withCenter = translateLevel β := by
  rw [Subgroup.withCenter_eq_self_iff]
  intro x hx
  have hneg : (-1 : SL(2, ℤ)) ∈ translateLevel β := by
    have h := mapGL_mem_range (-1 : SL(2, ℤ))
    rw [mapGL_neg_one] at h
    rw [mem_translateLevel, mapGL_neg_one, mul_neg_one, neg_mul, mul_inv_cancel]
    exact h
  rcases Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hx with rfl | rfl
  · exact Subgroup.one_mem _
  · exact hneg

/-- `Γ₁(1)` is everything. -/
theorem Gamma1_one_eq_top' : Gamma1 1 = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> exact Subsingleton.elim _ _

/-- The conjugation relation between `translateLevel α` and `translateLevel α⁻¹`. -/
theorem inv_conjAct_translateLevel_inv (α : GL (Fin 2) ℝ) :
    ConjAct.toConjAct α⁻¹ • (translateLevel α⁻¹).map (mapGL ℝ) = (translateLevel α).map (mapGL ℝ) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [map_inv, inv_inv, ConjAct.toConjAct_smul, Subgroup.mem_map,
    mem_translateLevel]
  constructor
  · rintro ⟨δ, ⟨γ, hγ⟩, h2⟩
    have hx : x = α⁻¹ * mapGL ℝ δ * α := by rw [h2]; group
    refine ⟨γ, ?_, hγ.trans hx.symm⟩
    rw [hγ]
    have : α * (α⁻¹ * mapGL ℝ δ * α) * α⁻¹ = mapGL ℝ δ := by group
    rw [this]
    exact mapGL_mem_range δ
  · rintro ⟨γ, ⟨δ, hδ⟩, rfl⟩
    refine ⟨δ, ?_, hδ⟩
    rw [hδ]
    have : α⁻¹ * (α * mapGL ℝ γ * α⁻¹) * α = mapGL ℝ γ := by group
    rw [this]
    exact mapGL_mem_range γ

/-- Milne's $f|_k\alpha = (\det\alpha)^{1-k}(f \mid_{2k}\alpha)$ (`milneSlash_eq`), as a cusp form for
$\Gamma(1) \cap \alpha^{-1}\Gamma(1)\alpha$. -/
noncomputable def milneTranslate (k : ℕ) (α : GL (Fin 2) ℝ) (f : CuspForm 𝒮ℒ (2 * k)) :
    CuspForm ((translateLevel α).map (mapGL ℝ)) (2 * k) :=
  (((α.det.val : ℝ) : ℂ) ^ (1 - k : ℤ)) • CuspForm.restrict (translateLevel_map_le α) (CuspForm.translate f α)

/-- **Milne, Lemma 5.22.** For cusp forms $f, g$ of weight $2k$ for $\Gamma(1)$ and an integer matrix $\alpha$ of positive
determinant, the Petersson product of $f|_k\alpha$ and $g|_k\alpha$ with respect to
$\Gamma' = \Gamma(1) \cap \alpha^{-1}\Gamma(1)\alpha$, normalized by the index, equals $\langle f, g\rangle$. -/
@[kb "milne2017mf" "Section 5, Lemma 5.22 (pdf p. 76)"]
theorem petersson_milneTranslate (k : ℕ) {α : GL (Fin 2) ℝ} (hα : 0 < α.det.val)
    (hint : ∃ A : Matrix (Fin 2) (Fin 2) ℤ, (α : Matrix (Fin 2) (Fin 2) ℝ) = A.map (Int.cast : ℤ → ℝ))
    (f g : CuspForm 𝒮ℒ (2 * k)) :
    haveI := translateLevel_finiteIndex hα hint
    CuspForm.peterssonInnerCosets (milneTranslate k α f) (milneTranslate k α g) /
        ((translateLevel α).withCenter.index : ℂ) = levelOnePetersson (2 * k) f g := by
  have hΓ₁ := translateLevel_finiteIndex hα hint
  have hidx := index_translateLevel_inv hα hint
  have hΓ₂ : (translateLevel α⁻¹).FiniteIndex := ⟨by rw [hidx]; exact hΓ₁.index_ne_zero⟩
  have hdet : (0 : ℝ) < (α : Matrix (Fin 2) (Fin 2) ℝ).det := hα
  have hle : (translateLevel α⁻¹).map (mapGL ℝ) ≤ (Gamma1 1).map (mapGL ℝ) :=
    Subgroup.map_mono (by rw [Gamma1_one_eq_top']; exact le_top)
  set f' := ((levelOneCuspEquiv (2 * (k : ℤ))).symm f : CuspForm ((Gamma1 1).map (mapGL ℝ)) (2 * k)) with hf'
  set g' := ((levelOneCuspEquiv (2 * (k : ℤ))).symm g : CuspForm ((Gamma1 1).map (mapGL ℝ)) (2 * k)) with hg'
  have h1 := TauCeti.CuspForm.peterssonInnerCosets_slash_of_inv_conjAct_eq (Γ := translateLevel α)
    (Γ' := translateLevel α⁻¹) hdet (inv_conjAct_translateLevel_inv α)
    (f := CuspForm.restrict hle f') (g := CuspForm.restrict hle g')
    (F := CuspForm.restrict (translateLevel_map_le α) (CuspForm.translate f α))
    (G := CuspForm.restrict (translateLevel_map_le α) (CuspForm.translate g α)) rfl rfl
  have h2 := CuspForm.peterssonInnerCosets_restrict_restrict hle f' g'
  have hwc1 := withCenter_translateLevel α
  have hwc2 := withCenter_translateLevel α⁻¹
  have hrel : (translateLevel α⁻¹).withCenter.relIndex (Gamma1 1).withCenter =
      (translateLevel α).withCenter.index := by
    have htop : (Gamma1 1).withCenter = ⊤ := by
      rw [Gamma1_one_eq_top']; exact top_le_iff.mp (Subgroup.le_withCenter ⊤)
    rw [htop, Subgroup.relIndex_top_right, hwc2, hwc1, hidx]
  have hne : ((translateLevel α).withCenter.index : ℂ) ≠ 0 := by
    rw [hwc1]; exact_mod_cast hΓ₁.index_ne_zero
  have hD : ((α.det.val : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hα.ne'
  have hDeq : ((α : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) = α.det.val := rfl
  rw [hDeq] at h1
  rw [hrel] at h2
  have hP : levelOnePetersson (2 * k) f g = CuspForm.peterssonInnerCosets f' g' := rfl
  have hconj : (starRingEnd ℂ) (((α.det.val : ℝ) : ℂ) ^ (1 - k : ℤ)) = ((α.det.val : ℝ) : ℂ) ^ (1 - k : ℤ) := by
    rw [map_zpow₀, Complex.conj_ofReal]
  have hz : ((α.det.val : ℝ) : ℂ) ^ (1 - k : ℤ) * ((α.det.val : ℝ) : ℂ) ^ (1 - k : ℤ) *
      ((α.det.val : ℝ) : ℂ) ^ (2 * (k : ℤ) - 2) = 1 := by
    rw [← zpow_add₀ hD, ← zpow_add₀ hD]
    have : (1 - (k : ℤ)) + (1 - k) + (2 * k - 2) = 0 := by ring
    rw [this, zpow_zero]
  unfold milneTranslate
  rw [CuspForm.peterssonInnerCosets_smul_left, CuspForm.peterssonInnerCosets_smul_right, hconj, h1, h2, hP]
  field_simp
  linear_combination (CuspForm.peterssonInnerCosets f' g') * hz

end ModularFormsKB.Milne
