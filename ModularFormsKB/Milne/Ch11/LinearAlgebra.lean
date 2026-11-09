import Mathlib
import ModularFormsKB.Citation
/-!
# Milne, Section 11: two elementary results from linear algebra (Propositions 11.1, 11.2, Corollary 11.3)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 11, pdf pp. 109–110.

## Items

- **Proposition 11.1**: `card_ker_mapQ_baseChange` — for a free $\mathbb Z$-module $\Lambda$ of finite rank and
  $\alpha \colon \Lambda \to \Lambda$ with $\det\alpha \ne 0$, the kernel of the map
  $\tilde\alpha \colon (\Lambda\otimes\mathbb Q)/\Lambda \to (\Lambda\otimes\mathbb Q)/\Lambda$ induced by $\alpha$ has
  order $|\det\alpha|$. We write $\mathbb Q\otimes_{\mathbb Z}\Lambda$ (Mathlib's base change) for Milne's
  $\Lambda\otimes\mathbb Q$, and $\Lambda$ for its image $1\otimes\Lambda$.
-/

open TensorProduct

namespace ModularFormsKB.Milne

section Prop11_1

variable {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]

/-- The lattice $\Lambda$ inside $\mathbb Q \otimes_{\mathbb Z} \Lambda$, as the image of $\lambda \mapsto 1\otimes\lambda$. -/
noncomputable def latticeInRat (Λ : Type*) [AddCommGroup Λ] : Submodule ℤ (ℚ ⊗[ℤ] Λ) :=
  LinearMap.range (TensorProduct.mk ℤ ℚ Λ 1)

omit [Module.Free ℤ Λ] [Module.Finite ℤ Λ] in
/-- The map $\alpha\otimes 1$ on $\mathbb Q\otimes\Lambda$ preserves $\Lambda$. -/
theorem latticeInRat_le_comap (α : Λ →ₗ[ℤ] Λ) :
    latticeInRat Λ ≤ (latticeInRat Λ).comap ((α.baseChange ℚ).restrictScalars ℤ) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨α x, rfl⟩

/-- The map $\tilde\alpha$ on $(\Lambda\otimes\mathbb Q)/\Lambda$ induced by $\alpha$ (Milne, Proposition 11.1). -/
noncomputable def torsionMap (α : Λ →ₗ[ℤ] Λ) :
    (ℚ ⊗[ℤ] Λ) ⧸ latticeInRat Λ →ₗ[ℤ] (ℚ ⊗[ℤ] Λ) ⧸ latticeInRat Λ :=
  (latticeInRat Λ).mapQ (latticeInRat Λ) ((α.baseChange ℚ).restrictScalars ℤ) (latticeInRat_le_comap α)

/-- **Proposition 11.1** (Milne): for a free $\mathbb Z$-module $\Lambda$ of finite rank and a $\mathbb Z$-linear
$\alpha\colon\Lambda\to\Lambda$ with nonzero determinant, the kernel of
$\tilde\alpha\colon(\Lambda\otimes\mathbb Q)/\Lambda\to(\Lambda\otimes\mathbb Q)/\Lambda$ has order $|\det\alpha|$. -/
@[kb "milne2017mf" "Section 11, Prop. 11.1 (pdf p. 109)"]
theorem card_ker_torsionMap (α : Λ →ₗ[ℤ] Λ) (hα : LinearMap.det α ≠ 0) :
    Nat.card (LinearMap.ker (torsionMap α)) = (LinearMap.det α).natAbs := by
  classical
  have hinj : Function.Injective (TensorProduct.mk ℤ ℚ Λ 1) := by
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := Λ)
      (Algebra.linearMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
    have : (TensorProduct.mk ℤ ℚ Λ 1 : Λ → ℚ ⊗[ℤ] Λ) =
        (LinearMap.rTensor Λ (Algebra.linearMap ℤ ℚ)) ∘ (TensorProduct.lid ℤ Λ).symm := by
      funext x
      simp
    rw [this]
    exact h.comp (TensorProduct.lid ℤ Λ).symm.injective
  have hdet : IsUnit (LinearMap.det (α.baseChange ℚ)) := by
    rw [LinearMap.det_baseChange]
    simpa using hα
  have hbij : Function.Bijective (α.baseChange ℚ) :=
    (Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 hdet)
  let e := LinearEquiv.ofBijective (α.baseChange ℚ) hbij
  let L := latticeInRat Λ
  have hmem : ∀ μ : Λ, torsionMap α (L.mkQ (e.symm (TensorProduct.mk ℤ ℚ Λ 1 μ))) = 0 := by
    intro μ
    have : (α.baseChange ℚ) (e.symm (TensorProduct.mk ℤ ℚ Λ 1 μ)) = TensorProduct.mk ℤ ℚ Λ 1 μ :=
      e.apply_symm_apply _
    show L.mkQ ((α.baseChange ℚ) (e.symm (TensorProduct.mk ℤ ℚ Λ 1 μ))) = 0
    rw [this]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨μ, rfl⟩
  let g : Λ →ₗ[ℤ] LinearMap.ker (torsionMap α) :=
    LinearMap.codRestrict (LinearMap.ker (torsionMap α))
      (L.mkQ ∘ₗ ((e.symm : (ℚ ⊗[ℤ] Λ) →ₗ[ℚ] (ℚ ⊗[ℤ] Λ)).restrictScalars ℤ)
        ∘ₗ TensorProduct.mk ℤ ℚ Λ 1) (fun μ => hmem μ)
  have hg : Function.Surjective g := by
    rintro ⟨q, hq⟩
    induction q using Submodule.Quotient.induction_on with
    | H v =>
      have hq' : torsionMap α (L.mkQ v) = 0 := hq
      simp only [torsionMap] at hq'
      obtain ⟨μ, hμ⟩ := (Submodule.Quotient.mk_eq_zero _).1 hq'
      refine ⟨μ, Subtype.ext ?_⟩
      have h2 : e.symm (TensorProduct.mk ℤ ℚ Λ 1 μ) = v := by
        rw [e.symm_apply_eq]
        exact hμ
      show L.mkQ (e.symm (TensorProduct.mk ℤ ℚ Λ 1 μ)) = L.mkQ v
      rw [h2]
  have hker : LinearMap.ker g = LinearMap.range α := by
    ext μ
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro h
      have h1 : L.mkQ (e.symm (TensorProduct.mk ℤ ℚ Λ 1 μ)) = 0 := by
        exact congrArg Subtype.val h
      obtain ⟨l, hl⟩ := (Submodule.Quotient.mk_eq_zero _).1 h1
      refine ⟨l, hinj ?_⟩
      have h3 : TensorProduct.mk ℤ ℚ Λ 1 μ = e (TensorProduct.mk ℤ ℚ Λ 1 l) := by
        rw [show TensorProduct.mk ℤ ℚ Λ 1 l = e.symm (TensorProduct.mk ℤ ℚ Λ 1 μ) from hl]
        exact (e.apply_symm_apply _).symm
      rw [h3]
      simp [e]
    · rintro ⟨l, rfl⟩
      apply Subtype.ext
      have : e.symm (TensorProduct.mk ℤ ℚ Λ 1 (α l)) = TensorProduct.mk ℤ ℚ Λ 1 l := by
        apply e.injective
        simp [e]
      show L.mkQ (e.symm (TensorProduct.mk ℤ ℚ Λ 1 (α l))) = 0
      rw [this]
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨l, rfl⟩
  have e1 : Nat.card (LinearMap.ker (torsionMap α)) = Nat.card (Λ ⧸ LinearMap.range α) := by
    rw [← hker]
    exact (Nat.card_congr (LinearMap.quotKerEquivOfSurjective g hg).toEquiv).symm
  have hαinj : Function.Injective α := by
    intro x y hxy
    have h1 : Function.Injective (α.baseChange ℚ) := hbij.1
    have h2 : TensorProduct.mk ℤ ℚ Λ 1 (α x) = TensorProduct.mk ℤ ℚ Λ 1 (α y) := by rw [hxy]
    apply hinj
    apply h1
    simpa using h2
  rw [e1, ← Submodule.natAbs_det_equiv (LinearMap.range α) (LinearEquiv.ofInjective α hαinj)]
  rfl

end Prop11_1

section Prop11_2

/-! ### Proposition 11.2 and Corollary 11.3

Milne starts from a real vector space $V$ with an $\mathbb R$-linear $J$, $J^2 = -1$, and gives $V$ the complex
structure $(x+iy)v = xv + yJv$. We take the equivalent Mathlib form: $V$ is a complex vector space (so a real one by
restriction of scalars) and $J$ is multiplication by $i$ (`complexStructure`, with `complexStructure_sq`). The
complexification $\mathbb C\otimes_{\mathbb R}V$ is a complex vector space through the left factor, $J$ extends to
$1\otimes J$ (`complexStructure.baseChange ℂ`), and $V^{+}$, $V^{-}$ are its eigenspaces for $i$ and $-i$. -/

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The complex structure $J = (v \mapsto iv)$ on $V$, as an $\mathbb R$-linear map. -/
noncomputable def complexStructure (V : Type*) [AddCommGroup V] [Module ℂ V] : V →ₗ[ℝ] V :=
  (LinearMap.lsmul ℂ V Complex.I).restrictScalars ℝ

theorem complexStructure_sq : complexStructure V ∘ₗ complexStructure V = -LinearMap.id := by
  ext v
  simp [complexStructure, smul_smul]


private lemma J_tmul (z : ℂ) (v : V) :
    (complexStructure V).baseChange ℂ (z ⊗ₜ[ℝ] v) = z ⊗ₜ[ℝ] (Complex.I • v) := by
  simp [complexStructure]

private lemma J_J (w : ℂ ⊗[ℝ] V) :
    (complexStructure V).baseChange ℂ ((complexStructure V).baseChange ℂ w) = -w := by
  have h := congrArg (LinearMap.baseChange ℂ) (complexStructure_sq (V := V))
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_neg, LinearMap.baseChange_id] at h
  exact LinearMap.congr_fun h w

/-- $V^{+}$: the $+i$ eigenspace of $1\otimes J$ on $\mathbb C\otimes_{\mathbb R}V$. -/
noncomputable def plusSpace (V : Type*) [AddCommGroup V] [Module ℂ V] : Submodule ℂ (ℂ ⊗[ℝ] V) :=
  Module.End.eigenspace ((complexStructure V).baseChange ℂ) Complex.I

/-- $V^{-}$: the $-i$ eigenspace of $1\otimes J$ on $\mathbb C\otimes_{\mathbb R}V$. -/
noncomputable def minusSpace (V : Type*) [AddCommGroup V] [Module ℂ V] : Submodule ℂ (ℂ ⊗[ℝ] V) :=
  Module.End.eigenspace ((complexStructure V).baseChange ℂ) (-Complex.I)

private lemma mem_plusSpace_iff (w : ℂ ⊗[ℝ] V) :
    w ∈ plusSpace V ↔ (complexStructure V).baseChange ℂ w = Complex.I • w := by
  simp [plusSpace, Module.End.mem_eigenspace_iff]

private lemma mem_minusSpace_iff (w : ℂ ⊗[ℝ] V) :
    w ∈ minusSpace V ↔ (complexStructure V).baseChange ℂ w = (-Complex.I) • w := by
  simp [minusSpace, Module.End.mem_eigenspace_iff]

/-- The projection of $\mathbb C\otimes_{\mathbb R}V$ onto $V^{+}$ along $V^{-}$:
$w\mapsto \tfrac12\,(w - i\,(1\otimes J)w)$. -/
noncomputable def plusProj (V : Type*) [AddCommGroup V] [Module ℂ V] : ℂ ⊗[ℝ] V →ₗ[ℂ] ℂ ⊗[ℝ] V :=
  (1 / 2 : ℂ) • (LinearMap.id - Complex.I • (complexStructure V).baseChange ℂ)

private lemma plusProj_apply (w : ℂ ⊗[ℝ] V) :
    plusProj V w = (1 / 2 : ℂ) • (w - Complex.I • (complexStructure V).baseChange ℂ w) := rfl

theorem plusProj_mem (w : ℂ ⊗[ℝ] V) : plusProj V w ∈ plusSpace V := by
  rw [mem_plusSpace_iff, plusProj_apply]
  simp only [map_smul, map_sub, J_J, smul_sub, smul_smul, smul_neg]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem plusProj_eq_self (w : ℂ ⊗[ℝ] V) (hw : w ∈ plusSpace V) : plusProj V w = w := by
  rw [mem_plusSpace_iff] at hw
  rw [plusProj_apply, hw]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [smul_sub, smul_smul]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem plusProj_eq_zero (w : ℂ ⊗[ℝ] V) (hw : w ∈ minusSpace V) : plusProj V w = 0 := by
  rw [mem_minusSpace_iff] at hw
  rw [plusProj_apply, hw]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [smul_sub, smul_smul, smul_neg]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/-- The splitting $\mathbb C\otimes_{\mathbb R}V = V^{+}\oplus V^{-}$ (Milne, Section 11, pdf p. 109). -/
@[kb "milne2017mf" "Section 11, splitting before Prop. 11.2 (pdf p. 109)"]
theorem isCompl_plusSpace_minusSpace : IsCompl (plusSpace V) (minusSpace V) := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  constructor
  · rw [Submodule.disjoint_def]
    intro w h1 h2
    rw [mem_plusSpace_iff] at h1
    rw [mem_minusSpace_iff] at h2
    have h3 : Complex.I • w = (-Complex.I) • w := h1.symm.trans h2
    have h4 : (2 * Complex.I) • w = 0 := by
      rw [mul_smul, two_smul]
      calc Complex.I • w + Complex.I • w = Complex.I • w + (-Complex.I) • w := by rw [← h3]
        _ = 0 := by rw [← add_smul]; simp
    rcases smul_eq_zero.mp h4 with h | h
    · simp at h
    · exact h
  · rw [codisjoint_iff, eq_top_iff]
    intro w _
    have : w = plusProj V w + (1 / 2 : ℂ) • (w + Complex.I • (complexStructure V).baseChange ℂ w) := by
      rw [plusProj_apply]; module
    rw [this]
    refine Submodule.add_mem_sup (plusProj_mem w) ?_
    rw [mem_minusSpace_iff]
    simp only [map_smul, map_add, J_J, smul_add, smul_smul, smul_neg, neg_smul]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

private lemma plusProj_tmul_I (v : V) :
    plusProj V (1 ⊗ₜ[ℝ] (Complex.I • v)) = Complex.I • plusProj V (1 ⊗ₜ[ℝ] v) := by
  rw [plusProj_apply, plusProj_apply, J_tmul, J_tmul, smul_smul, Complex.I_mul_I, neg_one_smul, tmul_neg]
  simp only [smul_sub, smul_neg, smul_smul]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

private lemma plusProj_tmul_real (r : ℝ) (v : V) :
    plusProj V (1 ⊗ₜ[ℝ] (r • v)) = (r : ℂ) • plusProj V (1 ⊗ₜ[ℝ] v) := by
  have h : (1 : ℂ) ⊗ₜ[ℝ] (r • v) = (r : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] v) := by
    rw [smul_tmul', smul_eq_mul, mul_one, ← smul_tmul r (1 : ℂ) v]; simp
  rw [h, map_smul]

private lemma plusProj_tmul_smul (c : ℂ) (v : V) :
    plusProj V (1 ⊗ₜ[ℝ] (c • v)) = c • plusProj V (1 ⊗ₜ[ℝ] v) := by
  have h : c • v = c.re • v + c.im • (Complex.I • v) := by
    conv_lhs => rw [← Complex.re_add_im c]
    rw [add_smul, mul_smul]
    simp [Complex.coe_smul]
  rw [h, tmul_add, map_add, plusProj_tmul_real, plusProj_tmul_real, plusProj_tmul_I, smul_smul, ← add_smul,
    Complex.re_add_im]

/-- The map $(V,J)\to V^{+}$, $v\mapsto$ (projection of $1\otimes v$ onto $V^{+}$), which is complex linear for
the complex structure $J$ on $V$. -/
noncomputable def toPlusSpace (V : Type*) [AddCommGroup V] [Module ℂ V] : V →ₗ[ℂ] plusSpace V where
  toFun v := ⟨plusProj V (1 ⊗ₜ v), plusProj_mem _⟩
  map_add' v w := by ext; simp [TensorProduct.tmul_add]
  map_smul' c v := Subtype.ext (plusProj_tmul_smul c v)

/-- The multiplication map $\mathbb C\otimes_{\mathbb R}V\to V$, $z\otimes v\mapsto zv$. -/
private noncomputable def mulMap (V : Type*) [AddCommGroup V] [Module ℂ V] : ℂ ⊗[ℝ] V →ₗ[ℝ] V :=
  TensorProduct.lift
    (LinearMap.mk₂ ℝ (fun (z : ℂ) (v : V) => z • v) (fun _ _ _ => add_smul _ _ _)
      (fun r z v => smul_assoc r z v) (fun _ _ _ => smul_add _ _ _) (fun r z v => smul_comm z r v))

private lemma mulMap_tmul (z : ℂ) (v : V) : mulMap V (z ⊗ₜ[ℝ] v) = z • v := by
  simp [mulMap]

private lemma mulMap_smul (c : ℂ) (w : ℂ ⊗[ℝ] V) : mulMap V (c • w) = c • mulMap V w := by
  induction w using TensorProduct.inductionOn with
  | tmul z v => rw [smul_tmul', smul_eq_mul, mulMap_tmul, mulMap_tmul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

private lemma mulMap_plusProj (v : V) : mulMap V (plusProj V (1 ⊗ₜ[ℝ] v)) = v := by
  rw [plusProj_apply, mulMap_smul, map_sub, mulMap_smul, J_tmul, mulMap_tmul, mulMap_tmul]
  simp only [smul_sub, smul_smul]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

private lemma plusProj_mulMap (w : ℂ ⊗[ℝ] V) :
    plusProj V (1 ⊗ₜ[ℝ] (mulMap V w)) = plusProj V w := by
  induction w using TensorProduct.inductionOn with
  | tmul z v =>
    rw [mulMap_tmul, plusProj_tmul_smul, ← map_smul, smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => rw [map_add, tmul_add, map_add, hx, hy, map_add]

/-- **Proposition 11.2 (a)** (Milne): the map $(V,J)\to\mathbb C\otimes_{\mathbb R}V\to V^{+}$,
$v\mapsto 1\otimes v\mapsto$ its $V^{+}$-component, is an isomorphism of complex vector spaces. -/
@[kb "milne2017mf" "Section 11, Prop. 11.2(a) (pdf p. 109)"]
theorem bijective_toPlusSpace : Function.Bijective (toPlusSpace V) := by
  constructor
  · intro v v' h
    have h' := congrArg (fun x : plusSpace V => mulMap V (x : ℂ ⊗[ℝ] V)) h
    simpa [toPlusSpace, mulMap_plusProj] using h'
  · rintro ⟨w, hw⟩
    refine ⟨mulMap V w, Subtype.ext ?_⟩
    show plusProj V (1 ⊗ₜ[ℝ] (mulMap V w)) = w
    rw [plusProj_mulMap, plusProj_eq_self w hw]

/-- Complex conjugation on the first factor, $z\otimes v\mapsto\bar z\otimes v$, an $\mathbb R$-linear map of
$\mathbb C\otimes_{\mathbb R}V$ (Milne writes $V\otimes_{\mathbb R}\mathbb C$). -/
noncomputable def conjTensor (V : Type*) [AddCommGroup V] [Module ℂ V] : ℂ ⊗[ℝ] V →ₗ[ℝ] ℂ ⊗[ℝ] V :=
  TensorProduct.map Complex.conjAe.toLinearMap LinearMap.id

private lemma conjTensor_tmul (z : ℂ) (v : V) : conjTensor V (z ⊗ₜ[ℝ] v) = (starRingEnd ℂ z) ⊗ₜ[ℝ] v := by
  simp [conjTensor]

private lemma conjTensor_conjTensor (w : ℂ ⊗[ℝ] V) : conjTensor V (conjTensor V w) = w := by
  induction w using TensorProduct.inductionOn with
  | tmul z v => rw [conjTensor_tmul, conjTensor_tmul, Complex.conj_conj]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private lemma conjTensor_smul (c : ℂ) (w : ℂ ⊗[ℝ] V) :
    conjTensor V (c • w) = (starRingEnd ℂ c) • conjTensor V w := by
  induction w using TensorProduct.inductionOn with
  | tmul z v => rw [smul_tmul', smul_eq_mul, conjTensor_tmul, conjTensor_tmul, smul_tmul', smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

private lemma conjTensor_J (w : ℂ ⊗[ℝ] V) :
    conjTensor V ((complexStructure V).baseChange ℂ w) = (complexStructure V).baseChange ℂ (conjTensor V w) := by
  induction w using TensorProduct.inductionOn with
  | tmul z v => rw [J_tmul, conjTensor_tmul, conjTensor_tmul, J_tmul]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

private lemma conjTensor_mem_minus (w : ℂ ⊗[ℝ] V) (hw : w ∈ plusSpace V) : conjTensor V w ∈ minusSpace V := by
  rw [mem_plusSpace_iff] at hw
  rw [mem_minusSpace_iff, ← conjTensor_J, hw, conjTensor_smul, Complex.conj_I]

private lemma conjTensor_mem_plus (w : ℂ ⊗[ℝ] V) (hw : w ∈ minusSpace V) : conjTensor V w ∈ plusSpace V := by
  rw [mem_minusSpace_iff] at hw
  rw [mem_plusSpace_iff, ← conjTensor_J, hw, conjTensor_smul, map_neg, Complex.conj_I, neg_neg]

/-- **Proposition 11.2 (b)** (Milne): $z\otimes v\mapsto\bar z\otimes v$ is an $\mathbb R$-linear involution of
$\mathbb C\otimes_{\mathbb R}V$ interchanging $V^{+}$ and $V^{-}$. -/
@[kb "milne2017mf" "Section 11, Prop. 11.2(b) (pdf p. 109)"]
theorem conjTensor_involutive_and_swap :
    Function.Involutive (conjTensor V) ∧
      (plusSpace V).toAddSubgroup.map (conjTensor V).toAddMonoidHom = (minusSpace V).toAddSubgroup ∧
      (minusSpace V).toAddSubgroup.map (conjTensor V).toAddMonoidHom = (plusSpace V).toAddSubgroup := by
  refine ⟨conjTensor_conjTensor, ?_, ?_⟩
  · ext u
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact conjTensor_mem_minus w hw
    · intro hu
      exact ⟨conjTensor V u, conjTensor_mem_plus u hu, conjTensor_conjTensor u⟩
  · ext u
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact conjTensor_mem_plus w hw
    · intro hu
      exact ⟨conjTensor V u, conjTensor_mem_minus u hu, conjTensor_conjTensor u⟩

/-- The matrix `Q` with rows indexed by `ι ⊕ ι` and columns by `κ`: the coordinates `b.repr (c k)` and their
conjugates. -/
private noncomputable def coordMatrix {ι κ : Type*} [Fintype ι] (b : Module.Basis ι ℂ V)
    (c : Module.Basis κ ℝ V) : Matrix (ι ⊕ ι) κ ℂ :=
  Matrix.of fun a k => Sum.elim (fun i => b.repr (c k) i) (fun i => starRingEnd ℂ (b.repr (c k) i)) a

private lemma coord_apply {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι ℂ V) (c : Module.Basis κ ℝ V) (α : V →ₗ[ℂ] V) (j : κ) (i : ι) :
    ∑ k, b.repr (c k) i * ((LinearMap.toMatrix c c (α.restrictScalars ℝ) k j : ℝ) : ℂ) =
      ∑ l, LinearMap.toMatrix b b α i l * b.repr (c j) l := by
  have h1 : b.repr (α (c j)) i = ∑ l, LinearMap.toMatrix b b α i l * b.repr (c j) l := by
    rw [← LinearMap.toMatrix_mulVec_repr b b α (c j)]
    rfl
  rw [← h1]
  conv_rhs => rw [← c.sum_repr (α (c j))]
  rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.coe_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm, LinearMap.toMatrix_apply]
  rfl

private lemma coordMatrix_mul {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι ℂ V) (c : Module.Basis κ ℝ V) (α : V →ₗ[ℂ] V) :
    coordMatrix b c * (LinearMap.toMatrix c c (α.restrictScalars ℝ)).map (↑) =
      Matrix.fromBlocks (LinearMap.toMatrix b b α) 0 0 ((LinearMap.toMatrix b b α).map (starRingEnd ℂ)) *
        coordMatrix b c := by
  ext a j
  rcases a with i | i
  · simp only [Matrix.mul_apply, coordMatrix, Matrix.of_apply, Matrix.map_apply, Sum.elim_inl,
      Matrix.fromBlocks_apply₁₁, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero]
    exact coord_apply b c α j i
  · refine (Matrix.mul_apply (M := coordMatrix b c)).trans (Eq.trans ?_ (Matrix.mul_apply (M := Matrix.fromBlocks _ _ _ _)).symm)
    simp only [coordMatrix, Matrix.of_apply, Matrix.map_apply, Sum.elim_inr,
      Matrix.fromBlocks_apply₂₂, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply,
      zero_mul, Finset.sum_const_zero, zero_add]
    have := congrArg (starRingEnd ℂ) (coord_apply b c α j i)
    simp only [map_sum, map_mul, Complex.conj_ofReal] at this
    simpa [mul_comm] using this

private lemma coordMatrix_injective {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι ℂ V) (c : Module.Basis κ ℝ V) :
    Function.Injective (coordMatrix b c).mulVec := by
  have core : ∀ x : κ → ℂ, (coordMatrix b c).mulVec x = 0 → x = 0 := by
    intro x hx
    have h1 : ∀ i, ∑ k, x k * b.repr (c k) i = 0 := fun i => by
      have := congrFun hx (Sum.inl i)
      simpa [Matrix.mulVec, dotProduct, coordMatrix, mul_comm] using this
    have h2 : ∀ i, ∑ k, x k * starRingEnd ℂ (b.repr (c k) i) = 0 := fun i => by
      have := congrFun hx (Sum.inr i)
      simpa [Matrix.mulVec, dotProduct, coordMatrix, mul_comm] using this
    have hc : ∀ i, ∑ k, starRingEnd ℂ (x k) * b.repr (c k) i = 0 := fun i => by
      have := congrArg (starRingEnd ℂ) (h2 i)
      simpa [map_sum, Complex.conj_conj] using this
    have key : ∀ y : κ → ℝ, (∀ i, ∑ k, (y k : ℂ) * b.repr (c k) i = 0) → y = 0 := by
      intro y hy
      have hs : ∑ k, y k • c k = 0 := by
        apply b.repr.injective
        ext i
        simp only [map_sum, map_zero, Finsupp.finsetSum_apply, Finsupp.coe_zero, Pi.zero_apply]
        rw [← hy i]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Complex.coe_smul, map_smul]
        simp
      exact funext (Fintype.linearIndependent_iff.mp c.linearIndependent y hs)
    have hu := key (fun k => (x k).re) fun i => by
      have : ∀ k, (((x k).re : ℝ) : ℂ) * b.repr (c k) i =
          (x k * b.repr (c k) i + starRingEnd ℂ (x k) * b.repr (c k) i) / 2 := fun k => by
        rw [Complex.re_eq_add_conj]; ring
      simp_rw [this, ← Finset.sum_div, Finset.sum_add_distrib, h1, hc]
      simp
    have hw := key (fun k => (x k).im) fun i => by
      have : ∀ k, (((x k).im : ℝ) : ℂ) * b.repr (c k) i =
          (x k * b.repr (c k) i - starRingEnd ℂ (x k) * b.repr (c k) i) / (2 * Complex.I) := fun k => by
        rw [Complex.im_eq_sub_conj]; ring
      simp_rw [this, ← Finset.sum_div, Finset.sum_sub_distrib, h1, hc]
      simp
    funext k
    apply Complex.ext
    · simpa using congrFun hu k
    · simpa using congrFun hw k
  intro x y hxy
  have : (coordMatrix b c).mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (core _ this)

/-- **Corollary 11.3** (Milne): let $\alpha$ be a complex-linear endomorphism of a finite-dimensional complex vector
space $V$, $A$ its matrix as an $\mathbb R$-linear map (in any real basis $c$) and $A_1$ its matrix as a
$\mathbb C$-linear map (in any complex basis $b$). Then $A$ is similar (over $\mathbb C$) to
$\begin{pmatrix}A_1&0\\0&\bar A_1\end{pmatrix}$. The real basis is indexed by a type $\kappa$ with
$|\kappa| = 2|\iota|$; the similarity is stated after reindexing $\kappa$ as $\iota\oplus\iota$. -/
@[kb "milne2017mf" "Section 11, Cor. 11.3 (pdf p. 110)"]
theorem realMatrix_similar_fromBlocks [FiniteDimensional ℂ V] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (b : Module.Basis ι ℂ V) (c : Module.Basis κ ℝ V) (α : V →ₗ[ℂ] V) :
    ∃ (e : κ ≃ ι ⊕ ι) (P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ), IsUnit P ∧
      P * Matrix.reindex e e ((LinearMap.toMatrix c c (α.restrictScalars ℝ)).map (↑)) =
        Matrix.fromBlocks (LinearMap.toMatrix b b α) 0 0 ((LinearMap.toMatrix b b α).map (starRingEnd ℂ)) * P := by
  have hcard : Fintype.card κ = Fintype.card (ι ⊕ ι) := by
    have h1 := Module.finrank_eq_card_basis c
    have h2 := Module.finrank_eq_card_basis b
    have h3 := Module.finrank_mul_finrank ℝ ℂ V
    rw [Complex.finrank_real_complex] at h3
    rw [Fintype.card_sum]
    omega
  let e : κ ≃ ι ⊕ ι := Fintype.equivOfCardEq hcard
  refine ⟨e, (coordMatrix b c).submatrix id e.symm, ?_, ?_⟩
  · have hinj : Function.Injective ((coordMatrix b c).submatrix id e.symm).mulVec := by
      intro x y hxy
      have h : (coordMatrix b c).mulVec (x ∘ e) = (coordMatrix b c).mulVec (y ∘ e) := by
        ext a
        have := congrFun hxy a
        simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id] at this ⊢
        have s1 := Equiv.sum_comp e.symm (fun k => coordMatrix b c a k * (x ∘ e) k)
        have s2 := Equiv.sum_comp e.symm (fun k => coordMatrix b c a k * (y ∘ e) k)
        simp only [Function.comp, Equiv.apply_symm_apply] at s1 s2
        exact s1.symm.trans (this.trans s2)
      have := coordMatrix_injective b c h
      funext a
      simpa using congrFun this (e.symm a)
    exact (Matrix.mulVec_injective_iff_isUnit).mp hinj
  · have := coordMatrix_mul b c α
    ext a a'
    have h := congrFun (congrFun this a) (e.symm a')
    refine Eq.trans ?_ (h.trans ?_)
    · refine (Matrix.mul_apply (M := (coordMatrix b c).submatrix id e.symm)).trans ?_
      refine Eq.trans ?_ (Matrix.mul_apply (M := coordMatrix b c)).symm
      simp only [Matrix.submatrix_apply, Matrix.reindex_apply, id]
      exact Equiv.sum_comp e.symm (fun k => coordMatrix b c a k *
        ((LinearMap.toMatrix c c) (α.restrictScalars ℝ)).map Complex.ofReal k (e.symm a'))
    · refine Eq.trans (Matrix.mul_apply (M := Matrix.fromBlocks _ _ _ _)) ?_
      exact (Matrix.mul_apply (M := Matrix.fromBlocks _ _ _ _)).symm

end Prop11_2

end ModularFormsKB.Milne
