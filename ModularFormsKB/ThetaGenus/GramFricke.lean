import ModularFormsKB.ThetaGenus.Gram
import ModularFormsKB.Miyake.Sec4_9.Spherical.Fricke

/-!
# Miyake, Corollary 4.9.5 in Gram-matrix form

Loose end LE-MF-0054. Gram convention of
`Gram.lean`. Let `A` be a symmetric positive definite integer matrix and `N > 0` with `N A⁻¹` integral
(`A * A' = N · 1`, `A'` integral). Miyake's `θ(z; A) = ∑_x e(xᵀAx z / 2)`; here `θ(2z; A) = θ_{2A}(z)`
and `θ(z; A) = θ_A(z)` when `A` has even diagonal.

* (1) `2A` is even and `4N` is admissible for it: `θ(2z; A) = θ_{2A}` has level dividing `4N`
  (`isGramLevel_two_smul`).
* (2) if `A` has even diagonal, `2N` is admissible for `A` (`isGramLevel_two_mul_of_even`).
* (3) if moreover `N A⁻¹` has even diagonal, `N` is admissible (`IsGramLevel` by definition), and
  the Fricke involution carries `θ_A` to `θ_{N A⁻¹}`:
  `θ_A(-1/(Nτ)) = (det A)^{-1/2} (Nτ/i)^{n/2} θ_{N A⁻¹}(τ)` (`thetaGram_fricke`).
-/

open Complex Module Filter Topology
open scoped Real RealInnerProductSpace ModularForm UpperHalfPlane MatrixGroups Matrix

set_option linter.unusedSectionVars false

namespace ModularFormsKB.ThetaGenus

open ModularFormsKB.Miyake.Sec4_9
open scoped Pointwise

variable {n : ℕ} {A A' : Matrix (Fin n) (Fin n) ℤ} {N : ℕ}

section Helpers

/-- Theta series of the `ℤ`-span of an `ℝ`-independent family with integral Gram matrix. -/
theorem thetaSph_span_gram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : Fin n → E) (hv : LinearIndependent ℝ v) (G : Matrix (Fin n) (Fin n) ℤ)
    (hG : ∀ i j, ⟪v i, v j⟫ = (G i j : ℝ)) (hs : G.transpose = G) :
    thetaSph (Submodule.span ℤ (Set.range v)) 0 0 0 0 = thetaGram G := by
  funext τ
  let B : Module.Basis (Fin n) ℤ (Submodule.span ℤ (Set.range v)) :=
    Module.Basis.span (hv.restrict_scalars' ℤ)
  have hB : ∀ x : Fin n → ℤ,
      ((B.equivFun.symm x : Submodule.span ℤ (Set.range v)) : E) = ∑ i, (x i : ℝ) • v i := by
    intro x
    simp [B, Module.Basis.equivFun_symm_apply, Int.cast_smul_eq_zsmul]
  have hn : ∀ x : Fin n → ℤ,
      ‖((B.equivFun.symm x : Submodule.span ℤ (Set.range v)) : E)‖ ^ 2 = (gramNorm G x : ℝ) := by
    intro x
    rw [hB, ← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, hG]
    simp [gramNorm, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    have hs' : G j i = G i j := by simpa using congrFun (congrFun hs i) j
    rw [hs']
    ring
  rw [thetaSph, thetaW_apply, thetaGram, ← B.equivFun.symm.toEquiv.tsum_eq]
  refine tsum_congr fun x ↦ ?_
  simp only [LinearEquiv.coe_toEquiv, zero_add, pow_zero, one_mul, hn]
  push_cast
  rfl

end Helpers

/-- **Miyake, Corollary 4.9.5 (1), Gram form**: if `A A' = N · 1`, then `(2A)(2A') = 4N · 1` and `2A'`
has even diagonal, so `4N` is admissible for `2A`. -/
theorem isGramLevel_two_smul (h : A * A' = (N : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) :
    IsGramLevel ((2 : ℤ) • A) (4 * N) := by
  refine ⟨(2 : ℤ) • A', ?_, fun i ↦ ⟨A' i i, by simp [two_mul]⟩⟩
  rw [Matrix.smul_mul, Matrix.mul_smul, h, smul_smul, smul_smul]
  push_cast
  ring_nf

/-- `2A` has even diagonal. -/
theorem even_diag_two_smul (i : Fin n) : Even (((2 : ℤ) • A) i i) := ⟨A i i, by simp [two_mul]⟩

/-- **Miyake, Corollary 4.9.5 (2), Gram form**: if `A A' = N · 1`, then `A (2A') = 2N · 1`, so `2N` is
admissible for `A` (meaningful when `A` has even diagonal). -/
theorem isGramLevel_two_mul_of_even (h : A * A' = (N : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) :
    IsGramLevel A (2 * N) := by
  refine ⟨(2 : ℤ) • A', ?_, fun i ↦ ⟨A' i i, by simp [two_mul]⟩⟩
  rw [Matrix.mul_smul, h, smul_smul]
  push_cast
  ring_nf

/-- **Miyake, Corollary 4.9.5 (3), Gram form: the Fricke transform.** For `A` even positive definite,
`A A' = N · 1` with `A'` even (so `A'` is also even positive definite, `hA'`):
`θ_A(-1/(Nτ)) = (det A)^{-1/2} (Nτ / i)^{n/2} θ_{A'}(τ)`. -/
@[kb "miyake1989" "Corollary 4.9.5 (3) in Gram-matrix form: theta_A(-1/(N tau)) = det(A)^(-1/2) (N tau/i)^(n/2) theta_{N A^-1}(tau)"]
theorem thetaGram_fricke (hA : IsEvenGram A) (hN : 0 < N)
    (h : A * A' = (N : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) (hA' : IsEvenGram A') (τ : ℍ) :
    thetaGram A (ModularGroup.S • ((⟨N, by exact_mod_cast hN⟩ : {r : ℝ // 0 < r}) • τ)) =
      ((Real.sqrt (A.det : ℝ) : ℂ))⁻¹ * (((N : ℂ) * τ) / I) ^ ((n : ℂ) / 2) * thetaGram A' τ := by
  classical
  have hs : (Real.sqrt (N : ℝ)) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hN)
  have hsq : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt (by positivity)
  set b := gramBasis hA with hb
  set d := LinearMap.BilinForm.dualBasis (innerₗ (EuclideanSpace ℝ (Fin n)))
    TauCeti.nondegenerate_inner b with hd
  -- the Gram matrix of the dual basis
  have hbd : ∀ j k, ⟪b j, d k⟫ = if j = k then (1 : ℝ) else 0 := by
    intro j k
    rw [real_inner_comm]
    have := LinearMap.BilinForm.apply_dualBasis_left (B := innerₗ (EuclideanSpace ℝ (Fin n)))
      TauCeti.nondegenerate_inner b k j
    simpa [eq_comm] using this
  have hexp : ∀ j, b j = ∑ l, (A j l : ℝ) • d l := by
    intro j
    conv_lhs => rw [← d.sum_repr (b j)]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [hd, LinearMap.BilinForm.dualBasis_repr_apply]
    simp [inner_gramBasis, hb]
  have hfact : ∀ j k, ∑ l, (A j l : ℝ) * ⟪d l, d k⟫ = if j = k then (1 : ℝ) else 0 := by
    intro j k
    rw [← hbd j k]
    conv_rhs => rw [hexp j]
    simp [sum_inner, real_inner_smul_left]
  have h1 : A.map (Int.cast : ℤ → ℝ) * A'.map (Int.cast : ℤ → ℝ) = (N : ℝ) • 1 := by
    ext i j
    have h2 := congrArg (Int.cast : ℤ → ℝ) (congrFun (congrFun h i) j)
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply] at h2 ⊢
    push_cast at h2
    rw [h2]
    split_ifs <;> simp
  have h1' : A'.map (Int.cast : ℤ → ℝ) * A.map (Int.cast : ℤ → ℝ) = (N : ℝ) • 1 := by
    have := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, ← Matrix.transpose_map, ← Matrix.transpose_map, hA.symm,
      hA'.symm] at this
    rw [this]
    ext i j
    simp [Matrix.transpose_apply, Matrix.one_apply, eq_comm]
  have hgram : ∀ i k, ⟪Real.sqrt (N : ℝ) • d i, Real.sqrt (N : ℝ) • d k⟫ = (A' i k : ℝ) := by
    intro i k
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← sq, hsq]
    set g : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i k ↦ ⟪d i, d k⟫ with hg
    have hAg : A.map (Int.cast : ℤ → ℝ) * g = 1 := by
      ext j k
      simp only [Matrix.mul_apply, Matrix.map_apply, hg, Matrix.of_apply, Matrix.one_apply]
      exact hfact j k
    have : A'.map (Int.cast : ℤ → ℝ) = (N : ℝ) • g := by
      calc A'.map (Int.cast : ℤ → ℝ)
          = A'.map (Int.cast : ℤ → ℝ) * (A.map (Int.cast : ℤ → ℝ) * g) := by rw [hAg, mul_one]
        _ = (N : ℝ) • g := by rw [← mul_assoc, h1', smul_mul_assoc, one_mul]
    have := congrFun (congrFun this i) k
    simpa [hg] using this.symm
  have hind : LinearIndependent ℝ (fun i ↦ Real.sqrt (N : ℝ) • d i) :=
    (d.linearIndependent).units_smul (fun _ ↦ Units.mk0 _ hs)
  have hdual : Real.sqrt (N : ℝ) • ZLattice.dual (gramLattice hA) =
      Submodule.span ℤ (Set.range fun i ↦ Real.sqrt (N : ℝ) • d i) := by
    rw [gramLattice, ZLattice.dual_span_basis, Submodule.smul_span]
    congr 1
    ext x
    simp [Set.mem_smul_set, hd, hb]
  have key := thetaSph_fricke (L := gramLattice hA) (ν := 0) (u := 0) (w := 0)
    (Or.inl zero_le_one) (N := (N : ℝ)) (by exact_mod_cast hN) τ
  rw [thetaSph_gramLattice hA, hdual,
    thetaSph_span_gram _ hind A' hgram hA'.symm] at key
  have hcov : ZLattice.covolume (gramLattice hA) = Real.sqrt (A.det : ℝ) := by
    have := ZLattice.inv_covolume_eq_inv_sqrt_det (gramLattice hA)
    rw [det_gramLattice hA] at this
    exact inv_injective this
  rw [key, hcov, finrank_euclideanSpace_fin']
  simp

end ModularFormsKB.ThetaGenus
