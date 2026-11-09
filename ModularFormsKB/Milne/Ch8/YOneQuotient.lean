import ModularFormsKB.Milne.Ch8.YOneModuli
import TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.Affine
import TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.UniversalProperty
import TauCeti.RingTheory.Invariant.FiniteType

/-!
# The quotient $Y_1(N)/(\mathbb Z/N)^\times$ (towards Theorem 8.6 for $N \ge 4$)

The units $G = (\mathbb Z/N)^\times$ act on $R = \Gamma(Y_1(N))$ through the automorphisms $\sigma_g$ of
`YOneModuli` (`g • r = σ_g^* r`, `instMulSemiringAction`), $k$-linearly. The quotient $M = \operatorname{Spec} R^G$
(Tau Ceti's `Quotient.quotient`) is a Milne variety (`mVar`): $R^G$ is of finite type over $k$ (Noether's theorem,
Tau Ceti's `finiteType_subalgebra`) and reduced.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TauCeti.AlgebraicGeometry MonoidalCategory MonObj

noncomputable section

namespace ModularFormsKB.Milne.YOneModuli

open CyclicN CyclicThree

variable {k : Type u} [Field k] {N : ℕ} [NeZero N] [hNf : Fact (((N : ℕ) : k) ≠ 0)] [h4f : Fact (4 ≤ N)]

variable (k N) in
/-- The coordinate ring $R = \Gamma(Y_1(N))$. -/
abbrev R : Type u := Γ((Y k N).base, ⊤)

/-- The action of $g$ on $R$: pullback along $\sigma_g$. -/
def act (g : (ZMod N)ˣ) : R k N →+* R k N := (sigma hNf.out h4f.out g).base.appTop.hom

instance instMulSemiringAction : MulSemiringAction (ZMod N)ˣ (R k N) where
  smul g r := act g r
  one_smul r := by
    change act 1 r = r
    rw [act, sigma_one _ _ (by have := h4f.out; omega)]
    simp
  mul_smul g h r := by
    change act (g * h) r = act g (act h r)
    rw [act, act, act, sigma_mul, EllObj.comp_base, Scheme.Hom.comp_appTop]
    rfl
  smul_zero g := map_zero (act g)
  smul_add g := map_add (act g)
  smul_one g := map_one (act g)
  smul_mul g := map_mul (act g)

theorem smul_def (g : (ZMod N)ˣ) (r : R k N) : g • r = act g r := rfl

variable (k N) in
/-- The $k$-algebra structure of $R$, from the structure morphism of $Y_1(N)$. -/
instance instAlgebra : Algebra k (R k N) := (gammaAlgHom (Y k N).structureMap).toAlgebra

theorem algebraMap_R (c : k) : algebraMap k (R k N) c = gammaAlgHom (Y k N).structureMap c := rfl

/-- The action is $k$-linear. -/
theorem act_algebraMap (g : (ZMod N)ˣ) (c : k) : act g (algebraMap k (R k N) c) = algebraMap k (R k N) c := by
  rw [algebraMap_R, gammaAlgHom, act, ← CommRingCat.comp_apply, Category.assoc, ← Scheme.Hom.comp_appTop,
    EllObj.Hom.base_structureMap]

instance : SMulCommClass (ZMod N)ˣ k (R k N) where
  smul_comm g c r := by
    rw [smul_def, Algebra.smul_def, Algebra.smul_def, smul_def, map_mul, act_algebraMap]

variable (k N) in
/-- The invariants $R^G$. -/
abbrev RG : Type u := FixedPoints.subring (R k N) (ZMod N)ˣ

/-- The $k$-algebra structure of $R^G$. -/
instance instAlgebraRG : Algebra k (RG k N) :=
  ((algebraMap k (R k N)).codRestrict (FixedPoints.subring (R k N) (ZMod N)ˣ)
    fun c g ↦ act_algebraMap g c).toAlgebra

/-- $R^G$ as the fixed $k$-subalgebra. -/
def rgEquiv : FixedPoints.subalgebra k (R k N) (ZMod N)ˣ ≃ₐ[k] RG k N where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

instance finiteType_R : Algebra.FiniteType k (R k N) := by
  have := isAffine_Y (k := k) hNf.out
  have := smooth_Y (k := k) hNf.out h4f.out
  exact finiteType_gammaAlgHom _

instance isReduced_R : _root_.IsReduced (R k N) := by
  have := isAffine_Y (k := k) hNf.out
  have := smooth_Y (k := k) hNf.out h4f.out
  exact isReduced_gamma_of_smooth (Y k N).structureMap

instance finiteType_RG : Algebra.FiniteType k (RG k N) :=
  Algebra.FiniteType.equiv inferInstance rgEquiv

instance isReduced_RG : _root_.IsReduced (RG k N) :=
  isReduced_of_injective (FixedPoints.subring (R k N) (ZMod N)ˣ).subtype Subtype.val_injective

variable (k N) in
/-- **The moduli variety** $M = Y_1(N)/(\mathbb Z/N)^\times = \operatorname{Spec} R^G$. -/
def mVar [IsAlgClosed k] : Variety k :=
  ⟨Over.mk (specStructure k (RG k N)), (isAffineVariety_spec k (isAffineAlgebra_of_isReduced _)).isVariety⟩

end ModularFormsKB.Milne.YOneModuli
