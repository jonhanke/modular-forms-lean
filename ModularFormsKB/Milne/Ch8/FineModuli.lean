import ModularFormsKB.Milne.Ch8.Moduli

/-!
# Milne, Chapter 8: a representing variety is a fine solution (Remark 8.3 (b))

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 8, Remark 8.3 (b)
(pdf p. 98).

If a variety $V$ represents a moduli problem $F$, i.e. $F \cong h_V$, then $(V, \alpha)$ with $\alpha$ the bijection
$F(k) \cong V(k)$ is a solution of $F$ (`isModuliSolution_of_iso`), and in fact a fine one
(`isFineModuliSolution_of_iso`): condition (a) is the classifying map of a family, and condition (b) is the value of
$\beta$ on the universal family. This reduces Theorem 8.8 for $N \ge 3$ to the existence of a fine moduli variety.
-/

universe u w

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

namespace ModularFormsKB.Milne

variable {k : Type u} [Field k]

/-- The bijection $F(k) \cong V(k)$ of an isomorphism $F \cong h_V$. -/
def pointEquivOfIso {F : (Variety k)ᵒᵖ ⥤ Type (max u w)} {V : Variety k}
    (η : F ≅ yoneda.obj V ⋙ uliftFunctor.{w}) : F.obj (op (Variety.point k)) ≃ (Variety.point k ⟶ V) :=
  (η.app (op (Variety.point k))).toEquiv.trans Equiv.ulift

/-- **A representing variety is a solution** (Milne, Remark 8.3 (b)). -/
theorem isModuliSolution_of_iso {F : (Variety k)ᵒᵖ ⥤ Type (max u w)} {V : Variety k}
    (η : F ≅ yoneda.obj V ⋙ uliftFunctor.{w}) : IsModuliSolution F V (pointEquivOfIso η) := by
  have nat : ∀ {T T' : Variety k} (t : T' ⟶ T) (f : F.obj (op T)),
      (η.hom.app (op T') (F.map t.op f)).down = t ≫ (η.hom.app (op T) f).down := fun t f ↦
    congrArg ULift.down (ConcreteCategory.congr_hom (η.hom.naturality t.op) f)
  refine ⟨fun T f ↦ ⟨(η.hom.app (op T) f).down, fun t ↦ (nat t f).symm⟩, fun Z β hβ ↦ ?_⟩
  let e : (yoneda.obj V ⋙ uliftFunctor.{w}).obj (op V) := (show ULift.{w} (V ⟶ V) from ULift.up (𝟙 V))
  let u : F.obj (op V) := η.inv.app (op V) e
  obtain ⟨ψ, hψ⟩ := hβ V u
  refine ⟨ψ, fun v ↦ ?_⟩
  rw [hψ]
  congr 1
  apply (pointEquivOfIso η).injective
  rw [Equiv.apply_symm_apply]
  change (η.hom.app _ (F.map v.op u)).down = v
  rw [nat v u]
  have : (η.hom.app (op V) u).down = 𝟙 V :=
    congrArg ULift.down (ConcreteCategory.congr_hom (η.inv_hom_id_app (op V)) e)
  rw [this, Category.comp_id]

/-- **A representing variety is a fine solution** (Milne, Remark 8.3 (b)). -/
theorem isFineModuliSolution_of_iso {F : (Variety k)ᵒᵖ ⥤ Type (max u w)} {V : Variety k}
    (η : F ≅ yoneda.obj V ⋙ uliftFunctor.{w}) : IsFineModuliSolution.{u, w} F V (pointEquivOfIso η) :=
  ⟨isModuliSolution_of_iso η, η, fun _ ↦ rfl⟩

end ModularFormsKB.Milne
