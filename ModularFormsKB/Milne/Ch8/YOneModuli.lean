import ModularFormsKB.Milne.Ch8.CyclicGenerators
import ModularFormsKB.Milne.Ch8.SmoothVariety
import TauCeti.AlgebraicGeometry.ModularCurve.Comparison

/-!
# The fine moduli variety $Y_1(N)$ over an algebraically closed field (towards Theorem 8.6 for $N \ge 4$)

Let $k$ be algebraically closed and $N \ge 4$ invertible in $k$. Tau Ceti's $Y_1(N)$ over $B = \operatorname{Spec} k$
(`EllObj.yOne B N`) represents Drinfeld points of exact order $N$ (`ModuliProblem.gammaOneRepresentableBy`). Here:

- $Y_1(N)$ is a Milne variety (`yVar`): it is affine and smooth over $k$ (Tau Ceti), so `isAffineVariety_of_smooth`;
- the **classifying arrow** `cls α : X ⟶ Y₁(N)` of a structure $\alpha$, natural in $X$ (`cls_map`);
- for a unit $g$ of $\mathbb Z/N$, the structure $P \mapsto gP$ (`powStr`) and the automorphism $\sigma_g$ of
  $Y_1(N)$ classifying $g$ times the universal point (`sigma`), with `cls (powStr g α) = cls α ≫ sigma g`
  (`cls_powStr`), $\sigma_1 = 1$ and $\sigma_{gh} = \sigma_g \sigma_h$ (`sigma_one`, `sigma_mul`).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TauCeti.AlgebraicGeometry MonoidalCategory MonObj

noncomputable section

namespace ModularFormsKB.Milne.YOneModuli

open CyclicN CyclicThree

variable {k : Type u} [Field k] {N : ℕ} [NeZero N]

/-- The base scheme $B = \operatorname{Spec} k$. -/
abbrev B (k : Type u) [Field k] : Scheme.{u} := Spec (CommRingCat.of k)

variable (hN : ((N : ℕ) : k) ≠ 0) (h4 : 4 ≤ N)

include hN in
theorem hNB : ∀ b : B k, (N : (B k).residueField b) ≠ 0 := natCast_ne_zero_residue hN (𝟙 _)

variable (k N) in
/-- $Y_1(N)$ over $k$, with its universal curve. -/
abbrev Y : EllObj (B k) := EllObj.yOne (B k) N

/-- The representing equivalence of $Y_1(N)$. -/
def rep : (ModuliProblem.gammaOne (B k) N).RepresentableBy (Y k N) :=
  ModuliProblem.gammaOneRepresentableBy (hN := hNB hN) h4

/-! ### $Y_1(N)$ as a variety -/

include hN in
theorem isAffine_Y : IsAffine (Y k N).base := EllObj.isAffine_yOne_base _ N (hNB hN)

include hN h4 in
theorem smooth_Y : Smooth (Y k N).structureMap := EllObj.smooth_yOne_structureMap _ N (hNB hN) h4

include hN h4 in
theorem isAffineVariety_Y [IsAlgClosed k] : IsAffineVariety k (Y k N).structureMap := by
  have := isAffine_Y hN
  have := smooth_Y hN h4
  exact isAffineVariety_of_smooth _

/-- **$Y_1(N)$ as a variety over $k$.** -/
def yVar [IsAlgClosed k] : Variety k :=
  ⟨Over.mk (Y k N).structureMap, (isAffineVariety_Y hN h4).isVariety⟩

/-! ### Classifying arrows -/

/-- **The classifying arrow** of a $[\Gamma_1(N)]$-structure. -/
def cls {X : EllObj (B k)} (α : (ModuliProblem.gammaOne (B k) N).obj (op X)) : X ⟶ Y k N :=
  (rep hN h4).homEquiv.symm α

theorem homEquiv_cls {X : EllObj (B k)} (α : (ModuliProblem.gammaOne (B k) N).obj (op X)) :
    (rep hN h4).homEquiv (cls hN h4 α) = α :=
  (rep hN h4).homEquiv.apply_symm_apply α

/-- **Naturality of the classifying arrow.** -/
theorem cls_map {X X' : EllObj (B k)} (f : X' ⟶ X) (α : (ModuliProblem.gammaOne (B k) N).obj (op X)) :
    cls hN h4 ((ModuliProblem.gammaOne (B k) N).map f.op α) = f ≫ cls hN h4 α := by
  apply (rep hN h4).homEquiv.injective
  rw [homEquiv_cls, (rep hN h4).homEquiv_comp, homEquiv_cls]

/-- The universal structure on $Y_1(N)$. -/
def univ : (ModuliProblem.gammaOne (B k) N).obj (op (Y k N)) := (rep hN h4).homEquiv (𝟙 _)

theorem cls_univ : cls hN h4 (univ hN h4) = 𝟙 _ := (rep hN h4).homEquiv.symm_apply_apply _

theorem map_cls_univ {X : EllObj (B k)} (α : (ModuliProblem.gammaOne (B k) N).obj (op X)) :
    (ModuliProblem.gammaOne (B k) N).map (cls hN h4 α).op (univ hN h4) = α := by
  apply (rep hN h4).homEquiv.symm.injective
  change cls hN h4 _ = cls hN h4 _
  rw [cls_map, cls_univ, Category.comp_id]

/-! ### Unit multiples -/

/-- The structure $g \cdot \alpha$: the point $gP$, for a unit $g$ of $\mathbb Z/N$. -/
def powStr {X : EllObj (B k)} (g : (ZMod N)ˣ) (α : (ModuliProblem.gammaOne (B k) N).obj (op X)) :
    (ModuliProblem.gammaOne (B k) N).obj (op X) :=
  (ModuliProblem.gammaOneEquiv X).symm ⟨(ModuliProblem.gammaOneEquiv X α).1 ^ (g : ZMod N).val,
    isOfExactOrder_pow_of_coprime (fun s ↦ X.structureMap.natCast_residueField_ne_zero (hNB hN _))
      (ModuliProblem.gammaOneEquiv X α).2 (ZMod.val_coe_unit_coprime g)⟩

theorem powStr_point {X : EllObj (B k)} (g : (ZMod N)ˣ) (α : (ModuliProblem.gammaOne (B k) N).obj (op X)) :
    (ModuliProblem.gammaOneEquiv X (powStr hN g α)).1 = (ModuliProblem.gammaOneEquiv X α).1 ^ (g : ZMod N).val := by
  simp [powStr]

theorem map_powStr {X X' : EllObj (B k)} (f : X' ⟶ X) (g : (ZMod N)ˣ)
    (α : (ModuliProblem.gammaOne (B k) N).obj (op X)) :
    (ModuliProblem.gammaOne (B k) N).map f.op (powStr hN g α) =
      powStr hN g ((ModuliProblem.gammaOne (B k) N).map f.op α) := by
  apply (ModuliProblem.gammaOneEquiv X').injective
  apply Subtype.ext
  rw [ModuliProblem.gammaOneEquiv_map, powStr_point, powStr_point, ModuliProblem.gammaOneEquiv_map, map_pow]

/-- **The automorphism $\sigma_g$ of $Y_1(N)$**, classifying $g$ times the universal point. -/
def sigma (g : (ZMod N)ˣ) : Y k N ⟶ Y k N := cls hN h4 (powStr hN g (univ hN h4))

theorem cls_powStr {X : EllObj (B k)} (g : (ZMod N)ˣ) (α : (ModuliProblem.gammaOne (B k) N).obj (op X)) :
    cls hN h4 (powStr hN g α) = cls hN h4 α ≫ sigma hN h4 g := by
  conv_lhs => rw [← map_cls_univ hN h4 α, ← map_powStr, cls_map]
  rfl

theorem powStr_one {X : EllObj (B k)} (α : (ModuliProblem.gammaOne (B k) N).obj (op X)) (hN1 : 1 < N) :
    powStr hN 1 α = α := by
  apply (ModuliProblem.gammaOneEquiv X).injective
  apply Subtype.ext
  haveI : Fact (1 < N) := ⟨hN1⟩
  rw [powStr_point, Units.val_one, ZMod.val_one, pow_one]

theorem powStr_mul {X : EllObj (B k)} (g h : (ZMod N)ˣ) (α : (ModuliProblem.gammaOne (B k) N).obj (op X)) :
    powStr hN h (powStr hN g α) = powStr hN (g * h) α := by
  apply (ModuliProblem.gammaOneEquiv X).injective
  apply Subtype.ext
  rw [powStr_point, powStr_point, powStr_point, ← pow_mul]
  have hP := (ModuliProblem.gammaOneEquiv X α).2
  rw [pow_eq_pow_mod hP, pow_eq_pow_mod hP ((g * h : (ZMod N)ˣ) : ZMod N).val, Units.val_mul, ZMod.val_mul,
    Nat.mod_mod]

theorem sigma_one (hN1 : 1 < N) : sigma hN h4 (1 : (ZMod N)ˣ) = 𝟙 _ := by
  rw [sigma, powStr_one hN _ hN1, cls_univ]

theorem sigma_mul (g h : (ZMod N)ˣ) : sigma hN h4 (g * h) = sigma hN h4 g ≫ sigma hN h4 h := by
  rw [sigma, ← powStr_mul, cls_powStr]
  rfl

end ModularFormsKB.Milne.YOneModuli
