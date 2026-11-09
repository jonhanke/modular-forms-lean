import ModularFormsKB.Milne.Ch6.ModularEquation
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Holomorphic
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Conj
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Sphere

/-!
# The functions $j(z)$ and $j(Nz)$ on $X_0(N)$

Milne, Section 6, proof of Theorem 6.1 (pdf p. 88): $j(z)$ and $j(Nz)$ are modular functions for $\Gamma_0(N)$. We
construct them as meromorphic functions on Tau Ceti's compactified quotient $X_0(N)$ (`ModularFormsKB.Milne.X0`):

- `jX N`: $X_0(N) \to X(1) \xrightarrow{j} \mathbb P^1$, Tau Ceti's `compactifiedQuotientMap` followed by
  `TauCeti.ModularGroup.jBiholomorph`; `isJOnX0_jX`.
-/

open UpperHalfPlane CongruenceSubgroup Matrix MulAction
open scoped MatrixGroups Manifold Pointwise

noncomputable section

namespace ModularFormsKB.Milne

open TauCeti.RiemannSurface Subgroup.CompactifiedQuotient

theorem Gamma0_map_le_range (N : ℕ) : (Gamma0 N).map sl2zToPSL2R ≤ psl2zToPSL2R.range := by
  rintro _ ⟨γ, -, rfl⟩
  exact ⟨γ, psl2zToPSL2R_mk γ⟩

/-- The map $X_0(N) \to \mathbb P^1$, $[z] \mapsto j(z)$. -/
def jXFun (N : ℕ) : X0 N → OnePoint ℂ :=
  TauCeti.ModularGroup.jBiholomorph ∘ Subgroup.compactifiedQuotientMap (Gamma0_map_le_range N)

theorem jXFun_ofQuotient (N : ℕ) (z : ℍ) :
    jXFun N (ofQuotient (Quotient.mk _ z)) = (TauCeti.ModularForm.j z : OnePoint ℂ) := by
  simp [jXFun]

/-- **$j$ as a meromorphic function on $X_0(N)$.** -/
def jX (N : ℕ) : MeromorphicFunction (X0 N) where
  toFun := jXFun N
  mdifferentiable' := (TauCeti.ModularGroup.jBiholomorph.mdifferentiable (by simp)).comp
    (Subgroup.CompactifiedQuotient.mdifferentiable_compactifiedQuotientMap (Gamma0_map_le_range N))
  ne_infty' := fun h ↦ by
    have := congrFun h (ofQuotient (Quotient.mk _ UpperHalfPlane.I))
    rw [jXFun_ofQuotient] at this
    exact OnePoint.coe_ne_infty _ this

theorem isJOnX0_jX (N : ℕ) : IsJOnX0 N (jX N) := fun z ↦ jXFun_ofQuotient N z

/-! ### $j(Nz)$ -/

/-- $\operatorname{diag}(\sqrt N, 1/\sqrt N) \in \mathrm{SL}_2(\mathbb R)$, acting by $z \mapsto Nz$. -/
def sqrtDiag (N : ℕ) (hN : 0 < N) : SL(2, ℝ) :=
  ⟨!![Real.sqrt N, 0; 0, (Real.sqrt N)⁻¹], by
    have : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 hN)).ne'
    rw [Matrix.det_fin_two_of]; field_simp; ring⟩

/-- Its image in $\mathrm{PSL}_2(\mathbb R)$. -/
def gN (N : ℕ) (hN : 0 < N) : PSL(2, ℝ) := (sqrtDiag N hN : PSL(2, ℝ))

theorem gN_smul (N : ℕ) (hN : 0 < N) (z : ℍ) : gN N hN • z = scaleH N hN z := by
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 hN)).ne'
  have hs2 : (Real.sqrt N : ℂ) ^ 2 = N := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N)]; simp
  ext
  rw [gN, UpperHalfPlane.pslMk_smul, coe_specialLinearGroup_apply]
  simp only [sqrtDiag, scaleH, UpperHalfPlane.coe_mk]
  simp
  have : (Real.sqrt N : ℂ) ≠ 0 := by exact_mod_cast hs
  field_simp
  rw [hs2]
  ring

/-- The conjugate $g\,\Gamma_0(N)\,g^{-1}$ in $\mathrm{PSL}_2(\mathbb R)$. -/
def Gamma0Conj (N : ℕ) (hN : 0 < N) : Subgroup PSL(2, ℝ) :=
  ConjAct.toConjAct (gN N hN) • (Gamma0 N).map sl2zToPSL2R

theorem sqrtDiag_mul {N : ℕ} (hN : 0 < N) (γ δ : SL(2, ℤ)) (h00 : δ 0 0 = γ 0 0)
    (h01 : δ 0 1 = N * γ 0 1) (h10 : (N : ℤ) * δ 1 0 = γ 1 0) (h11 : δ 1 1 = γ 1 1) :
    sqrtDiag N hN * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ =
      Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) δ * sqrtDiag N hN := by
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 hN)).ne'
  have hs2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
  have h10' : (N : ℝ) * (δ 1 0 : ℝ) = (γ 1 0 : ℝ) := by exact_mod_cast h10
  have h01' : (δ 0 1 : ℝ) = N * (γ 0 1 : ℝ) := by exact_mod_cast h01
  have h00' : (δ 0 0 : ℝ) = (γ 0 0 : ℝ) := by exact_mod_cast h00
  have h11' : (δ 1 1 : ℝ) = (γ 1 1 : ℝ) := by exact_mod_cast h11
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, sqrtDiag]
  · rw [h00']; ring
  · rw [h01']; field_simp; rw [hs2]; ring
  · rw [← h10']; field_simp; rw [hs2]
  · rw [h11']; ring

theorem sqrtDiag_conj {N : ℕ} (hN : 0 < N) (γ δ : SL(2, ℤ)) (h00 : δ 0 0 = γ 0 0)
    (h01 : δ 0 1 = N * γ 0 1) (h10 : (N : ℤ) * δ 1 0 = γ 1 0) (h11 : δ 1 1 = γ 1 1) :
    sqrtDiag N hN * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ * (sqrtDiag N hN)⁻¹ =
      Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) δ := by
  rw [sqrtDiag_mul hN γ δ h00 h01 h10 h11, mul_inv_cancel_right]

theorem Gamma0Conj_le_range (N : ℕ) (hN : 0 < N) : Gamma0Conj N hN ≤ psl2zToPSL2R.range := by
  intro x hx
  rw [Gamma0Conj, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
  obtain ⟨γ, hγ, hγx⟩ := hx
  obtain ⟨δ, h00, h01, h10, h11⟩ := exists_delta_of_mem_Gamma0 γ hγ
  refine ⟨(δ : PSL(2, ℤ)), ?_⟩
  rw [psl2zToPSL2R_mk, sl2zToPSL2R_apply, ← sqrtDiag_conj hN γ δ h00 h01 h10 h11]
  have : x = gN N hN * sl2zToPSL2R γ * (gN N hN)⁻¹ := by
    rw [hγx, ConjAct.smul_def]; simp [mul_assoc]
  rw [this, sl2zToPSL2R_apply, gN]
  simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem gN_conj (N : ℕ) (hN : 0 < N) :
    ConjAct.toConjAct (gN N hN) • (Gamma0 N).map sl2zToPSL2R = Gamma0Conj N hN := rfl

instance (N : ℕ) (hN : 0 < N) : DiscreteTopology (Gamma0Conj N hN) :=
  .of_subset (inferInstance : DiscreteTopology psl2zToPSL2R.range) (Gamma0Conj_le_range N hN)

/-- The map $X_0(N) \to \mathbb P^1$, $[z] \mapsto j(Nz)$. -/
def jNXFun (N : ℕ) (hN : 0 < N) : X0 N → OnePoint ℂ :=
  TauCeti.ModularGroup.jBiholomorph ∘ Subgroup.compactifiedQuotientMap (Gamma0Conj_le_range N hN) ∘
    Subgroup.compactifiedQuotientConj (gN_conj N hN)

theorem jNXFun_ofQuotient (N : ℕ) (hN : 0 < N) (z : ℍ) :
    jNXFun N hN (ofQuotient (Quotient.mk _ z)) =
      (TauCeti.ModularForm.j (scaleH N hN z) : OnePoint ℂ) := by
  simp only [jNXFun, Function.comp_apply]
  rw [Subgroup.compactifiedQuotientConj_ofQuotient, Subgroup.quotientConjHomeomorph_mk,
    Subgroup.compactifiedQuotientMap_ofQuotient]
  simp [gN_smul, TauCeti.ModularGroup.jQuotient_mk]

/-- **$j(Nz)$ as a meromorphic function on $X_0(N)$.** -/
def jNX (N : ℕ) (hN : 0 < N) : MeromorphicFunction (X0 N) where
  toFun := jNXFun N hN
  mdifferentiable' := by
    exact (TauCeti.ModularGroup.jBiholomorph.mdifferentiable (by simp)).comp
      ((Subgroup.CompactifiedQuotient.mdifferentiable_compactifiedQuotientMap
        (Gamma0Conj_le_range N hN)).comp (Subgroup.CompactifiedQuotient.mdifferentiable_compactifiedQuotientConj _))
  ne_infty' := fun h ↦ by
    have := congrFun h (ofQuotient (Quotient.mk _ UpperHalfPlane.I))
    rw [jNXFun_ofQuotient] at this
    exact OnePoint.coe_ne_infty _ this

theorem isJNOnX0_jNX (N : ℕ) (hN : 0 < N) : IsJNOnX0 N hN (jNX N hN) :=
  fun z ↦ jNXFun_ofQuotient N hN z

end ModularFormsKB.Milne
