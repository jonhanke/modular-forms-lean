import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basis
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Automorphisms of a constant field extension

Let $F/k$ be a function field with $k$ algebraically closed in $F$, and $F' = F\cdot k'$ a constant field
extension by a separable algebraic extension $k'/k$. Then $F' \cong F \otimes_k k'$ (the multiplication map is an
isomorphism: it sends the $F$-basis $1 \otimes b_i$ to Tau Ceti's basis of constants `constantBasis`). Hence every
pair $(\tau, \rho)$ of a $k$-automorphism $\tau$ of $F$ and a $k$-automorphism $\rho$ of $k'$ gives a
$k$-automorphism `twistAut τ ρ` $= \tau \otimes \rho$ of $F'$, the unique one restricting to $\tau$ on $F$ and to
$\rho$ on $k'$. For $\rho$ the Frobenius this is the automorphism whose fixed field is the *twist* of $F$ by
$\tau$ (Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., proof of Theorem 5.2.3 [unverified numbering];
Bombieri, Séminaire Bourbaki 430, 1973).
-/

open TauCeti Module
open scoped TensorProduct

namespace ModularFormsKB.Milne

variable {k : Type*} {k' : Type*} {F : Type*} {F' : Type*}
  [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- The multiplication map $F \otimes_k k' \to F'$, an $F$-algebra homomorphism. -/
noncomputable def constantTensorHom : F ⊗[k] k' →ₐ[F] F' :=
  Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId F F') (IsScalarTower.toAlgHom k k' F')

@[simp]
theorem constantTensorHom_tmul (x : F) (c : k') :
    constantTensorHom (k := k) (x ⊗ₜ c : F ⊗[k] k') = algebraMap F F' x * algebraMap k' F' c := rfl

variable [Algebra.IsSeparable k k']

/-- The multiplication map $F \otimes_k k' \to F' = F \cdot k'$ is bijective when $k$ is exact in $F$. -/
theorem bijective_constantTensorHom (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) :
    Function.Bijective (constantTensorHom (k := k) (k' := k') (F := F) (F' := F')) := by
  let b := Basis.ofVectorSpace k k'
  let b1 := Algebra.TensorProduct.basis F b
  let b2 := constantBasis hex h b
  have hlin : (constantTensorHom (k := k) (k' := k') (F := F) (F' := F')).toLinearMap =
      (b1.equiv b2 (Equiv.refl _)).toLinearMap := by
    refine b1.ext fun i => ?_
    rw [LinearEquiv.coe_coe, Basis.equiv_apply]
    simp [b1, b2, Algebra.TensorProduct.basis_apply]
  have : ⇑(constantTensorHom (k := k) (k' := k') (F := F) (F' := F')) = ⇑(b1.equiv b2 (Equiv.refl _)) :=
    congrArg (⇑) hlin
  rw [this]
  exact (b1.equiv b2 (Equiv.refl _)).bijective

/-- $F \otimes_k k' \cong F'$. -/
noncomputable def constantTensorEquiv (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤) :
    F ⊗[k] k' ≃ₐ[F] F' :=
  AlgEquiv.ofBijective _ (bijective_constantTensorHom hex h)

@[simp]
theorem constantTensorEquiv_tmul (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    (x : F) (c : k') :
    constantTensorEquiv hex h (x ⊗ₜ c) = algebraMap F F' x * algebraMap k' F' c := rfl

/-- **The automorphism $\tau \otimes \rho$ of $F' = F \otimes_k k'$.** -/
noncomputable def twistAut (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
    (τ : F ≃ₐ[k] F) (ρ : k' ≃ₐ[k] k') : F' ≃ₐ[k] F' :=
  ((constantTensorEquiv hex h).restrictScalars k).symm.trans
    ((Algebra.TensorProduct.congr τ ρ).trans ((constantTensorEquiv hex h).restrictScalars k))

variable (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)

theorem twistAut_tmul (τ : F ≃ₐ[k] F) (ρ : k' ≃ₐ[k] k') (x : F) (c : k') :
    twistAut hex h τ ρ (algebraMap F F' x * algebraMap k' F' c) =
      algebraMap F F' (τ x) * algebraMap k' F' (ρ c) := by
  have hx : ((constantTensorEquiv hex h).restrictScalars k).symm
      (algebraMap F F' x * algebraMap k' F' c) = x ⊗ₜ c := by
    rw [AlgEquiv.symm_apply_eq]; rfl
  simp only [twistAut, AlgEquiv.trans_apply, hx, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  rfl

@[simp]
theorem twistAut_algebraMap_left (τ : F ≃ₐ[k] F) (ρ : k' ≃ₐ[k] k') (x : F) :
    twistAut hex h τ ρ (algebraMap F F' x) = algebraMap F F' (τ x) := by
  simpa using twistAut_tmul hex h τ ρ x 1

@[simp]
theorem twistAut_algebraMap_right (τ : F ≃ₐ[k] F) (ρ : k' ≃ₐ[k] k') (c : k') :
    twistAut hex h τ ρ (algebraMap k' F' c) = algebraMap k' F' (ρ c) := by
  simpa using twistAut_tmul hex h τ ρ 1 c

include hex h in
/-- Two $k$-algebra homomorphisms of $F'$ agreeing on $F$ and on $k'$ are equal. -/
theorem algHom_ext_constantCompositum {f g : F' →ₐ[k] F'}
    (hF : ∀ x : F, f (algebraMap F F' x) = g (algebraMap F F' x))
    (hk : ∀ c : k', f (algebraMap k' F' c) = g (algebraMap k' F' c)) : f = g := by
  have hcomp : f.comp ((constantTensorEquiv hex h).restrictScalars k).toAlgHom =
      g.comp ((constantTensorEquiv hex h).restrictScalars k).toAlgHom := by
    refine Algebra.TensorProduct.ext' fun x c => ?_
    change f (constantTensorEquiv hex h (x ⊗ₜ c)) = g (constantTensorEquiv hex h (x ⊗ₜ c))
    rw [constantTensorEquiv_tmul, map_mul, map_mul, hF, hk]
  ext y
  obtain ⟨z, rfl⟩ := (constantTensorEquiv hex h).surjective y
  exact congrArg (fun φ : F ⊗[k] k' →ₐ[k] F' => φ z) hcomp

include hex h in
theorem algEquiv_ext_constantCompositum {f g : F' ≃ₐ[k] F'}
    (hF : ∀ x : F, f (algebraMap F F' x) = g (algebraMap F F' x))
    (hk : ∀ c : k', f (algebraMap k' F' c) = g (algebraMap k' F' c)) : f = g :=
  AlgEquiv.coe_toAlgHom_injective (algHom_ext_constantCompositum hex h hF hk)

@[simp]
theorem twistAut_one : twistAut hex h (1 : F ≃ₐ[k] F) (1 : k' ≃ₐ[k] k') = 1 :=
  algEquiv_ext_constantCompositum hex h (by simp) (by simp)

theorem twistAut_mul (τ τ' : F ≃ₐ[k] F) (ρ ρ' : k' ≃ₐ[k] k') :
    twistAut hex h (τ * τ') (ρ * ρ') = twistAut hex h τ ρ * twistAut hex h τ' ρ' :=
  algEquiv_ext_constantCompositum hex h (by simp) (by simp)

/-- $(\tau, \rho) \mapsto \tau \otimes \rho$ as a group homomorphism. -/
noncomputable def twistAutHom : (F ≃ₐ[k] F) × (k' ≃ₐ[k] k') →* (F' ≃ₐ[k] F') where
  toFun p := twistAut hex h p.1 p.2
  map_one' := twistAut_one hex h
  map_mul' p p' := twistAut_mul hex h p.1 p'.1 p.2 p'.2

@[simp]
theorem twistAutHom_apply (p : (F ≃ₐ[k] F) × (k' ≃ₐ[k] k')) : twistAutHom hex h p = twistAut hex h p.1 p.2 :=
  rfl

theorem twistAut_pow (τ : F ≃ₐ[k] F) (ρ : k' ≃ₐ[k] k') (n : ℕ) :
    twistAut hex h τ ρ ^ n = twistAut hex h (τ ^ n) (ρ ^ n) := by
  have := map_pow (twistAutHom hex h) (τ, ρ) n
  simpa using this.symm

theorem injective_twistAutHom : Function.Injective (twistAutHom hex h) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨τ, ρ⟩ hp
  rw [MonoidHom.mem_ker, twistAutHom_apply] at hp
  refine Prod.ext (AlgEquiv.ext fun x => ?_) (AlgEquiv.ext fun c => ?_)
  · apply (algebraMap F F').injective
    have := congrArg (fun φ : F' ≃ₐ[k] F' => φ (algebraMap F F' x)) hp
    simpa using this
  · apply (algebraMap k' F').injective
    have := congrArg (fun φ : F' ≃ₐ[k] F' => φ (algebraMap k' F' c)) hp
    simpa using this

end ModularFormsKB.Milne
