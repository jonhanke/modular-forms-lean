import ModularFormsKB.Milne.Ch8.LevelOne

/-!
# Milne, Chapter 8: Theorem 8.6 for $N = 1$

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 8, Theorem 8.6 (pdf p. 100).

A cyclic subgroup of order $1$ of an elliptic curve $E/S$ (Tau Ceti's `IsCyclicSubgroup I 1`) is the zero section
(`ker_zero_eq_of_isCyclicSubgroup_one`): it contains the zero section because it is a subgroup scheme whose inclusion
preserves the unit, and it is contained in it because multiplication by $1$ kills it. So an elliptic curve has exactly
one $[\Gamma_0(1)]$-structure, $[\Gamma_0(1)]$ is the trivial problem (`gammaZeroOneIso`), $\mathcal E_{0,1} \cong
\mathcal E$, and Theorem 8.4 gives `cyclicModuliSolution_one`.
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite TauCeti.AlgebraicGeometry MonoidalCategory

noncomputable section

namespace ModularFormsKB.Milne

/-- **A cyclic subgroup of order one is the zero section.** -/
theorem ker_zero_eq_of_isCyclicSubgroup_one {S : Scheme.{u}} {E : EllipticCurveGeom S}
    {I : E.carrier.IdealSheafData} (h : E.IsCyclicSubgroup I 1) : I = E.zero.ker := by
  apply le_antisymm
  · obtain ⟨grp, hi⟩ := h.exists_grpObj_isMonHom
    have h1 := congrArg CommaMorphism.left (IsMonHom.one_hom (Over.homMk I.subschemeι rfl :
      Over.mk (I.subschemeι ≫ E.structureMap) ⟶ Over.mk E.structureMap))
    simp only [Over.comp_left, Over.homMk_left, EllipticCurveGeom.one_left] at h1
    rw [← h1]
    calc I = I.subschemeι.ker := I.ker_subschemeι.symm
      _ ≤ _ := Scheme.Hom.le_ker_comp _ _
  · have h3 := h.subschemeι_comp_mulBy
    rw [Nat.cast_one, EllipticCurveGeom.mulBy_one, Over.id_left] at h3
    erw [Category.comp_id] at h3
    calc E.zero.ker ≤ ((I.subschemeι ≫ E.structureMap) ≫ E.zero).ker := Scheme.Hom.le_ker_comp _ _
      _ = I.subschemeι.ker := by rw [Category.assoc, ← h3]
      _ = I := I.ker_subschemeι

/-- Every object of `Ell/B` has exactly one $[\Gamma_0(1)]$-structure. -/
instance uniqueGammaZeroOne {B : Scheme.{u}} (X : (EllObj B)ᵒᵖ) : Unique ((ModuliProblem.gammaZero B 1).obj X) where
  default := (ModuliProblem.gammaOneToGammaZero B 1).app X default
  uniq α := (ModuliProblem.gammaZeroEquiv X.unop).injective <| Subtype.ext <|
    (ker_zero_eq_of_isCyclicSubgroup_one (ModuliProblem.gammaZeroEquiv X.unop α).2).trans
      (ker_zero_eq_of_isCyclicSubgroup_one (ModuliProblem.gammaZeroEquiv X.unop _).2).symm

/-- **$[\Gamma_0(1)]$ is the trivial moduli problem.** -/
def gammaZeroOneIso (B : Scheme.{u}) : ModuliProblem.gammaZero B 1 ≅ 𝟙_ (ModuliProblem B) :=
  ModuliProblem.isoTensorUnitOfUnique _

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **Milne, Theorem 8.6 for $N = 1$**, unconditionally: $\mathcal E_{0,1} \cong \mathcal E$, solved by the affine line
with the $j$-invariant. -/
theorem cyclicModuliSolution_one : CyclicModuliSolution k 1 := by
  refine ⟨fun _ ↦ ?_⟩
  obtain ⟨α, -, hα⟩ := (ellipticModuliSolution k).solution
  exact ⟨affineLine k, _, isModuliSolution_of_natIso (levelFunctorIso (gammaZeroOneIso _)) hα⟩

end ModularFormsKB.Milne
