import ModularFormsKB.Milne.Ch8.YOneBijection
import ModularFormsKB.Milne.Ch8.CyclicThreeSolution
import ModularFormsKB.Milne.Ch8.CyclicOne

/-!
# Milne, Theorem 8.6 for every $N$: $\mathcal E_{0,N}$ has a solution

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 8, Theorem 8.6 (pdf p. 100).

For $N \ge 4$ invertible in the algebraically closed field $k$, the quotient $M = Y_1(N)/(\mathbb Z/N)^\times$ of Tau
Ceti's fine moduli variety $Y_1(N)$ solves $\mathcal E_{0,N}$ (`isModuliSolution_ge_four`):

- (a) the invariant morphism of a pair (`cycMor`, descended along fppf covers from the local generators);
- $\alpha$ is bijective (`alpha_bijective`, `YOneBijection`);
- (b) for $\beta$ as in Definition 8.1 (b), the regular map $\varphi : Y_1(N) \to Z$ of the universal pair is invariant
  under the automorphisms $\sigma_g$ (`phi_invariant`, checked on $k$-points: $\sigma_g$ pulls the universal subgroup
  back to itself), so it descends to $M$ (Tau Ceti's `descOfFinite`).

With $N = 1, 2, 3$ (`cyclicModuliSolution_one`, `_two`, `_three`) this gives **Theorem 8.6 for every $N$**
(`cyclicModuliSolution`).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TauCeti.AlgebraicGeometry MonoidalCategory MonObj
  TauCeti.AffineInvariantQuotient

noncomputable section

namespace ModularFormsKB.Milne.YOneModuli

open CyclicN CyclicThree CyclicTwo

variable {k : Type u} [Field k] [IsAlgClosed k] {N : ℕ} [NeZero N] [hNf : Fact (((N : ℕ) : k) ≠ 0)]
  [h4f : Fact (4 ≤ N)]

/-- $\sigma_g$ as a regular map of $Y_1(N)$. -/
def sigmaV (g : (ZMod N)ˣ) : yV k N ⟶ yV k N :=
  toYV (sigma hNf.out h4f.out g).base (sigma hNf.out h4f.out g).base_structureMap

/-- **$\sigma_g$ pulls the universal pair back to itself.** -/
theorem rel_pull_sigma (g : (ZMod N)ˣ) : LevelPair.Rel (LevelPair.pull (sigmaV g) (xu k N)) (xu k N) := by
  have := LevelPair.rel_of_arrows (P := ModuliProblem.gammaZero (B k) N) (V := yV k N) sU
    (LevelPair.pullHom (sigmaV g) (Y k N).curve) (sigma hNf.out h4f.out g) rfl
  have e : (ModuliProblem.gammaZero (B k) N).map (sigma hNf.out h4f.out g).op sU = sU := by
    rw [sigma, map_cls_sU, gammaOneToGammaZero_powStr]
    rfl
  refine LevelPair.rel_trans this ⟨𝟙 _, EllObj.id_base _, ?_⟩
  erw [op_id, Functor.map_id_apply]
  exact e.symm

section Universal

variable {Z : Variety k} (β : (cyclicFunctor k N).obj (op (Variety.point k)) → (Variety.point k ⟶ Z))

theorem phi_invariant (φ : yV k N ⟶ Z)
    (hφ : ∀ t : Variety.point k ⟶ yV k N, t ≫ φ = β ((cyclicFunctor k N).map t.op ⟦xu k N⟧))
    (g : (ZMod N)ˣ) : sigmaV g ≫ φ = φ := by
  apply Variety.hom_ext_of_points
  intro t
  have hx : (cyclicFunctor k N).map (sigmaV g).op ⟦xu k N⟧ = ⟦xu k N⟧ := Quotient.sound (rel_pull_sigma g)
  rw [← Category.assoc, hφ, hφ]
  congr 1
  erw [op_comp, Functor.map_comp_apply, hx]

theorem specMap_sigma_isoSpec_inv (g : (ZMod N)ˣ) :
    Spec.map (sigma hNf.out h4f.out g).base.appTop ≫ (Y k N).base.isoSpec.inv =
      (Y k N).base.isoSpec.inv ≫ (sigma hNf.out h4f.out g).base := by
  rw [Iso.comp_inv_eq, Category.assoc, Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality, ← Category.assoc,
    ← Scheme.isoSpec_hom, Iso.inv_hom_id, Category.id_comp]

variable (hβ : ∀ (T : Variety k) (f : (cyclicFunctor k N).obj (op T)),
    ∃ φ : T ⟶ Z, ∀ t : Variety.point k ⟶ T, t ≫ φ = β ((cyclicFunctor k N).map t.op f))

include hβ in
/-- **Theorem 8.6 ($N \ge 4$), condition (b).** -/
theorem alpha_universal :
    ∃ ψ : mVar k N ⟶ Z, ∀ v : Variety.point k ⟶ mVar k N,
      v ≫ ψ = β ((Equiv.ofBijective _ (alpha_bijective (k := k) (N := N))).symm v) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : yV k N ⟶ Z, ∀ t : Variety.point k ⟶ yV k N,
      t ≫ φ = β ((cyclicFunctor k N).map t.op ⟦xu k N⟧) := hβ _ ⟦xu k N⟧
  let f0 : Spec (CommRingCat.of (R k N)) ⟶ Z.obj.left := (Y k N).base.isoSpec.inv ≫ φ.hom.left
  have hf : ∀ g : (ZMod N)ˣ, specComap (R k N) (ZMod N)ˣ g ≫ f0 = f0 := by
    intro g
    have hinv := congrArg (fun χ : yV k N ⟶ Z ↦ χ.hom.left) (phi_invariant β φ hφ g)
    change (sigma hNf.out h4f.out g).base ≫ φ.hom.left = φ.hom.left at hinv
    change Spec.map (sigma hNf.out h4f.out g).base.appTop ≫ (Y k N).base.isoSpec.inv ≫ φ.hom.left =
      (Y k N).base.isoSpec.inv ≫ φ.hom.left
    calc Spec.map (sigma hNf.out h4f.out g).base.appTop ≫ (Y k N).base.isoSpec.inv ≫ φ.hom.left
        = (Spec.map (sigma hNf.out h4f.out g).base.appTop ≫ (Y k N).base.isoSpec.inv) ≫ φ.hom.left :=
          (Category.assoc _ _ _).symm
      _ = ((Y k N).base.isoSpec.inv ≫ (sigma hNf.out h4f.out g).base) ≫ φ.hom.left :=
          congrArg (· ≫ φ.hom.left) (specMap_sigma_isoSpec_inv g)
      _ = (Y k N).base.isoSpec.inv ≫ (sigma hNf.out h4f.out g).base ≫ φ.hom.left := Category.assoc _ _ _
      _ = (Y k N).base.isoSpec.inv ≫ φ.hom.left := congrArg ((Y k N).base.isoSpec.inv ≫ ·) hinv
  let ψ0 := descOfFinite f0 hf
  have hψ0 : projection (R k N) (ZMod N)ˣ ≫ ψ0 = f0 := projection_descOfFinite f0 hf
  have hover : ψ0 ≫ Z.obj.hom = specStructure k (RG k N) := by
    rw [← cancel_epi (projection (R k N) (ZMod N)ˣ), reassoc_of% hψ0, projection_specStructure]
    change (Y k N).base.isoSpec.inv ≫ φ.hom.left ≫ Z.obj.hom = _
    have hw : φ.hom.left ≫ Z.obj.hom = (Y k N).structureMap := Over.w φ.hom
    exact (congrArg ((Y k N).base.isoSpec.inv ≫ ·) hw).trans isoSpec_inv_structureMap
  let ψ : mVar k N ⟶ Z := ⟨Over.homMk ψ0 hover⟩
  have hxu : cycMor (xu k N) ≫ ψ = φ := by
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    change (cycMor (xu k N)).hom.left ≫ ψ0 = φ.hom.left
    rw [cycMor_xu]
    change (Y k N).base.toSpecΓ ≫ projection (R k N) (ZMod N)ˣ ≫ ψ0 = φ.hom.left
    rw [hψ0, ← Scheme.isoSpec_hom]
    exact Iso.hom_inv_id_assoc _ _
  refine ⟨ψ, fun v ↦ ?_⟩
  obtain ⟨x, rfl⟩ := (alpha_bijective (k := k) (N := N)).2 v
  rw [Equiv.ofBijective_symm_apply_apply]
  induction x using Quotient.inductionOn with
  | h y =>
  obtain ⟨E, α, r⟩ := exists_rel_zPair y
  have r' := LevelPair.rel_trans r (rel_pull_xu E α)
  change cycMor y ≫ ψ = _
  rw [cycMor_rel r', cycMor_pull, Category.assoc, hxu, hφ]
  exact congrArg β (Quotient.sound r').symm

end Universal

/-- **$M = Y_1(N)/(\mathbb Z/N)^\times$ solves the moduli problem $\mathcal E_{0,N}$** for $N \ge 4$. -/
theorem isModuliSolution_ge_four :
    IsModuliSolution (cyclicFunctor k N) (mVar k N) (Equiv.ofBijective _ (alpha_bijective (k := k) (N := N))) := by
  refine ⟨fun T f ↦ ?_, fun Z β hβ ↦ alpha_universal β hβ⟩
  induction f using Quotient.inductionOn with
  | h x => exact ⟨cycMor x, fun t ↦ (cycMor_pull t x).symm⟩

end ModularFormsKB.Milne.YOneModuli

namespace ModularFormsKB.Milne

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Milne, Theorem 8.6 for $N \ge 4$**, unconditionally: over an algebraically closed field with $N \ne 0$, the
quotient $Y_1(N)/(\mathbb Z/N)^\times$ of the fine moduli variety $Y_1(N)$ solves $\mathcal E_{0,N}$. -/
@[kb "milne2017mf" "Section 8, Theorem 8.6 for N >= 4 (pdf p. 100)"]
theorem cyclicModuliSolution_of_four_le {N : ℕ} (h4 : 4 ≤ N) : CyclicModuliSolution k N := by
  refine ⟨fun hN ↦ ?_⟩
  haveI : NeZero N := ⟨by omega⟩
  haveI : Fact (((N : ℕ) : k) ≠ 0) := ⟨hN⟩
  haveI : Fact (4 ≤ N) := ⟨h4⟩
  exact ⟨YOneModuli.mVar k N, _, YOneModuli.isModuliSolution_ge_four⟩

/-- **Milne, Theorem 8.6** (first assertion, over an algebraically closed field), unconditionally for every $N$: if
$N$ is not divisible by the characteristic of $k$, the moduli problem $\mathcal E_{0,N}$ has a solution. -/
@[kb "milne2017mf" "Section 8, Theorem 8.6 (pdf p. 100), over an algebraically closed field"]
theorem cyclicModuliSolution (N : ℕ) : CyclicModuliSolution k N := by
  rcases N with _ | _ | _ | _ | n
  · exact ⟨fun h ↦ absurd Nat.cast_zero h⟩
  · exact cyclicModuliSolution_one k
  · exact cyclicModuliSolution_two k
  · exact cyclicModuliSolution_three k
  · exact cyclicModuliSolution_of_four_le k (by omega)

end ModularFormsKB.Milne
