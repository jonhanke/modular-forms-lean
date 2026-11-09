import ModularFormsKB.Milne.Ch7.Varieties
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Yoneda

/-!
# Milne, Chapter 8: the general notion of a moduli variety (Definition 8.1, Proposition 8.2, Remark 8.3)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 8, pdf pp. 97–98.

Fix an algebraically closed field $k$. Varieties over $k$ are those of Chapter 7 (`ModularFormsKB.Milne.IsVariety`),
here organized as the full subcategory `Variety k` of schemes over $\operatorname{Spec} k$; a morphism (regular map) of
varieties is a morphism over $\operatorname{Spec} k$. The point $\operatorname{Specm} k$ is `Variety.point k`, and for
a variety $V$ the set $V(k)$ of points with coordinates in $k$ is `Variety.point k ⟶ V`. A *moduli problem* is a
contravariant functor $F$ from varieties to sets, `(Variety k)ᵒᵖ ⥤ Type u`; $F(k)$ is `F.obj (op (Variety.point k))`
and a point $t \in T(k)$ gives $F(t) : F(T) \to F(k)$, `F.map t.op`.

A map $T(k) \to V(k)$ is *regular* when it is induced by a morphism $T \to V$ (Milne: "defined by a morphism of
algebraic varieties").

## Items

- **Definition 8.1** (solution of a moduli problem): `IsModuliSolution`; **moduli variety** (D100): `IsModuliVariety`.
- **Proposition 8.2** (uniqueness up to unique isomorphism): `moduliSolution_unique`. The proof needs that a morphism of
  varieties over an algebraically closed field is determined by its map on $k$-points (`Variety.hom_ext_of_points`,
  from Mathlib's `AlgebraicGeometry.ext_of_apply_eq`).
- **Remark 8.3 (a)** (solutions as universal natural transformations $F \to h_V$): `isModuliSolution_iff_natTrans`;
  **fine and coarse moduli varieties** (Remark 8.3 (b), D101): `IsFineModuliSolution`, `IsCoarseModuliSolution`.
-/

universe u w

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

namespace ModularFormsKB.Milne

variable (k : Type u) [Field k]

/-- The property of a scheme over $\operatorname{Spec} k$ of being a variety over $k$ (Chapter 7). -/
def varietyProperty : ObjectProperty (Over (Spec (CommRingCat.of k))) :=
  fun Y ↦ IsVariety k Y.hom

/-- **The category of varieties over $k$** (Milne, Section 8, pdf p. 97): varieties over $k$ (Chapter 7) with the
regular maps (morphisms of schemes over $\operatorname{Spec} k$). -/
@[kb "milne2017mf" "Section 8, the category of algebraic varieties over k (pdf p. 97)"]
abbrev Variety : Type (u + 1) :=
  (varietyProperty k).FullSubcategory

/-- $\operatorname{Spec} k$ is a variety over $k$. -/
theorem isVariety_point : IsVariety k (𝟙 (Spec (CommRingCat.of k))) := by
  have h := (isAffineVariety_spec k (isAffineAlgebra_self k)).isVariety
  have e : specStructure k k = 𝟙 (Spec (CommRingCat.of k)) := by
    simp only [specStructure]
    convert Spec.map_id (CommRingCat.of k)
  rwa [e] at h

/-- **The point** $\operatorname{Specm} k$ as a variety over $k$; `Variety.point k ⟶ V` is $V(k)$. -/
def Variety.point : Variety k :=
  ⟨Over.mk (𝟙 (Spec (CommRingCat.of k))), isVariety_point k⟩

variable {k}

/-- **Morphisms of varieties over an algebraically closed field are determined by their values on $k$-points**
(used in Milne's proof of Proposition 8.2): Mathlib's `AlgebraicGeometry.ext_of_apply_eq`. -/
theorem Variety.hom_ext_of_points [IsAlgClosed k] {T W : Variety k} {φ ψ : T ⟶ W}
    (h : ∀ t : Variety.point k ⟶ T, t ≫ φ = t ≫ ψ) : φ = ψ := by
  have hV : IsVariety k W.obj.hom := W.property
  have hT : IsVariety k T.obj.hom := T.property
  haveI : IsSeparated W.obj.hom := hV.2
  haveI : LocallyOfFiniteType W.obj.hom := hV.locallyOfFiniteType
  haveI : IsReduced T.obj.left := hT.isReduced
  haveI : LocallyOfFiniteType (φ.hom.left ≫ W.obj.hom) := by
    rw [Over.w φ.hom]; exact hT.locallyOfFiniteType
  have hmain : φ.hom.left = ψ.hom.left := by
    refine ext_of_apply_eq W.obj.hom Set.univ ?_ ?_ ?_ ?_
    · exact isOpen_univ.isLocallyClosed
    · exact dense_univ
    · intro x _ hx
      haveI : LocallyOfFiniteType T.obj.hom := hT.locallyOfFiniteType
      let t : Variety.point k ⟶ T := ⟨Over.homMk (pointOfClosedPoint T.obj.hom x hx)
        (pointOfClosedPoint_comp T.obj.hom x hx)⟩
      have h0 : t.hom ≫ φ.hom = t.hom ≫ ψ.hom := congrArg (fun g : Variety.point k ⟶ W => g.hom) (h t)
      have h1 : φ.hom.left (pointOfClosedPoint T.obj.hom x hx (IsLocalRing.closedPoint k)) =
          ψ.hom.left (pointOfClosedPoint T.obj.hom x hx (IsLocalRing.closedPoint k)) :=
        congrArg (fun g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ W.obj => g.left (IsLocalRing.closedPoint k)) h0
      have hp : ∀ a, pointOfClosedPoint T.obj.hom x hx a = x := pointOfClosedPoint_apply _ x hx
      erw [hp] at h1
      exact h1
    · rw [Over.w φ.hom, Over.w ψ.hom]
  exact InducedCategory.hom_ext (Over.OverMorphism.ext hmain)


/-- **Solution to a moduli problem** (Milne, Definition 8.1): a variety $V$ with a bijection
$\alpha : F(k) \to V(k)$ such that

(a) for every variety $T$ and $f \in F(T)$, the map $T(k) \to V(k)$, $t \mapsto \alpha(f_t)$, $f_t = F(t)(f)$, is
regular;

(b) (universality) for every variety $Z$ and map $\beta : F(k) \to Z(k)$ such that $t \mapsto \beta(f_t)$ is regular
for every pair $(T, f)$ as in (a), the map $\beta \circ \alpha^{-1} : V(k) \to Z(k)$ is regular. -/
@[kb "milne2017mf" "Section 8, Definition 8.1 (pdf p. 97)"]
structure IsModuliSolution (F : (Variety k)ᵒᵖ ⥤ Type w) (V : Variety k)
    (α : F.obj (op (Variety.point k)) ≃ (Variety.point k ⟶ V)) : Prop where
  regular : ∀ (T : Variety k) (f : F.obj (op T)),
    ∃ φ : T ⟶ V, ∀ t : Variety.point k ⟶ T, t ≫ φ = α (F.map t.op f)
  universal : ∀ (Z : Variety k) (β : F.obj (op (Variety.point k)) → (Variety.point k ⟶ Z)),
    (∀ (T : Variety k) (f : F.obj (op T)),
      ∃ φ : T ⟶ Z, ∀ t : Variety.point k ⟶ T, t ≫ φ = β (F.map t.op f)) →
    ∃ ψ : V ⟶ Z, ∀ v : Variety.point k ⟶ V, v ≫ ψ = β (α.symm v)

/-- **Moduli variety** (Milne, Section 8, pdf p. 97; D100): a variety that occurs as the solution of a moduli
problem. -/
@[kb "milne2017mf" "Section 8, moduli variety (pdf p. 97)"]
def IsModuliVariety (V : Variety k) : Prop :=
  ∃ (F : (Variety k)ᵒᵖ ⥤ Type w) (α : F.obj (op (Variety.point k)) ≃ (Variety.point k ⟶ V)),
    IsModuliSolution F V α

/-- **Milne, Proposition 8.2**: up to a unique isomorphism, there exists at most one solution to a moduli problem:
for two solutions $(V, \alpha)$, $(V', \alpha')$ there is exactly one isomorphism $V \to V'$ carrying $\alpha$ to
$\alpha'$ (on $k$-points, $\alpha' \circ \alpha^{-1}$). -/
@[kb "milne2017mf" "Section 8, Proposition 8.2 (pdf p. 97)"]
theorem moduliSolution_unique [IsAlgClosed k] {F : (Variety k)ᵒᵖ ⥤ Type w} {V V' : Variety k}
    {α : F.obj (op (Variety.point k)) ≃ (Variety.point k ⟶ V)}
    {α' : F.obj (op (Variety.point k)) ≃ (Variety.point k ⟶ V')}
    (h : IsModuliSolution F V α) (h' : IsModuliSolution F V' α') :
    ∃! e : V ≅ V', ∀ x : F.obj (op (Variety.point k)), α x ≫ e.hom = α' x := by
  obtain ⟨ψ, hψ⟩ := h.universal V' α' h'.regular
  obtain ⟨ψ', hψ'⟩ := h'.universal V α h.regular
  have h1 : ψ ≫ ψ' = 𝟙 V := by
    apply Variety.hom_ext_of_points
    intro v
    rw [← Category.assoc, hψ, hψ', Equiv.symm_apply_apply, Equiv.apply_symm_apply, Category.comp_id]
  have h2 : ψ' ≫ ψ = 𝟙 V' := by
    apply Variety.hom_ext_of_points
    intro v
    rw [← Category.assoc, hψ', hψ, Equiv.symm_apply_apply, Equiv.apply_symm_apply, Category.comp_id]
  refine ⟨⟨ψ, ψ', h1, h2⟩, fun x => ?_, fun e he => ?_⟩
  · have := hψ (α x)
    simpa using this
  · ext1
    apply Variety.hom_ext_of_points
    intro v
    have h3 := he (α.symm v)
    rw [Equiv.apply_symm_apply] at h3
    show v ≫ e.hom = v ≫ ψ
    rw [h3, hψ]

/-- Regular maps on `k`-points come from a natural transformation `F ⟶ h_Z` (for `k` algebraically closed). -/
lemma exists_natTrans_of_regular [IsAlgClosed k] (F : (Variety k)ᵒᵖ ⥤ Type u) (Z : Variety k)
    (β : F.obj (op (Variety.point k)) → (Variety.point k ⟶ Z))
    (hreg : ∀ (T : Variety k) (f : F.obj (op T)),
      ∃ φ : T ⟶ Z, ∀ t : Variety.point k ⟶ T, t ≫ φ = β (F.map t.op f)) :
    ∃ η : F ⟶ yoneda.obj Z, (∀ x, η.app (op (Variety.point k)) x = β x) ∧
      ∀ (T : Variety k) (f : F.obj (op T)) (t : Variety.point k ⟶ T),
        t ≫ η.app (op T) f = β (F.map t.op f) := by
  choose φ hφ using hreg
  have key : ∀ (T : Variety k) (f : F.obj (op T)) (t : Variety.point k ⟶ T),
      t ≫ φ T f = β (F.map t.op f) := hφ
  refine ⟨{ app := fun T => TypeCat.ofHom (fun f => φ T.unop f), naturality := ?_ }, ?_, ?_⟩
  · intro T' T g
    ext f
    apply Variety.hom_ext_of_points
    intro t
    show t ≫ φ T.unop (F.map g f) = t ≫ g.unop ≫ φ T'.unop f
    rw [key, ← Category.assoc, key]
    simp
  · intro x
    have := key (Variety.point k) x (𝟙 _)
    simpa using this
  · intro T f t
    exact key T f t

/-- **Milne, Remark 8.3 (a)**: with $h_V = \operatorname{Hom}(-, V)$ (`yoneda.obj V`), condition (a) of Definition 8.1
says that $\alpha$ extends to a natural transformation $\eta : F \to h_V$, and (b) says that $\eta$ is universal: every
natural transformation $F \to h_Z$ factors uniquely through $\eta$. -/
@[kb "milne2017mf" "Section 8, Remark 8.3 (a) (pdf p. 98)"]
theorem isModuliSolution_iff_natTrans [IsAlgClosed k] (F : (Variety k)ᵒᵖ ⥤ Type u) (V : Variety k)
    (α : F.obj (op (Variety.point k)) ≃ (Variety.point k ⟶ V)) :
    IsModuliSolution F V α ↔
      ∃ η : F ⟶ yoneda.obj V, (∀ x, η.app (op (Variety.point k)) x = α x) ∧
        ∀ (Z : Variety k) (η' : F ⟶ yoneda.obj Z), ∃! ψ : V ⟶ Z, η ≫ yoneda.map ψ = η' := by
  constructor
  · intro hs
    obtain ⟨η, hη0, hη1⟩ := exists_natTrans_of_regular F V (fun x => α x) hs.regular
    refine ⟨η, hη0, fun Z η' => ?_⟩
    obtain ⟨ψ, hψ⟩ := hs.universal Z (fun x => η'.app _ x) (fun T f => ⟨η'.app (op T) f, fun t => by
      have := ConcreteCategory.congr_hom (η'.naturality t.op) f
      exact this.symm⟩)
    refine ⟨ψ, ?_, fun ψ₂ hψ₂ => ?_⟩
    · ext T f
      apply Variety.hom_ext_of_points
      intro t
      show t ≫ η.app T f ≫ ψ = t ≫ η'.app T f
      rw [← Category.assoc, hη1 T.unop f t, hψ, Equiv.symm_apply_apply]
      exact ConcreteCategory.congr_hom (η'.naturality t.op) f
    · apply Variety.hom_ext_of_points
      intro v
      have h3 := ConcreteCategory.congr_hom (congr_app hψ₂ (op (Variety.point k))) (α.symm v)
      have h4 : η.app (op (Variety.point k)) (α.symm v) ≫ ψ₂ = η'.app (op (Variety.point k)) (α.symm v) := h3
      rw [hη0, Equiv.apply_symm_apply] at h4
      rw [h4, hψ]
      rfl
  · rintro ⟨η, hη0, huniv⟩
    refine ⟨fun T f => ⟨η.app (op T) f, fun t => ?_⟩, fun Z β hβ => ?_⟩
    · rw [← hη0]
      exact (ConcreteCategory.congr_hom (η.naturality t.op) f).symm
    · obtain ⟨η', hη'0, -⟩ := exists_natTrans_of_regular F Z β hβ
      obtain ⟨ψ, hψ, -⟩ := huniv Z η'
      refine ⟨ψ, fun v => ?_⟩
      have h3 := ConcreteCategory.congr_hom (congr_app hψ (op (Variety.point k))) (α.symm v)
      have h4 : η.app (op (Variety.point k)) (α.symm v) ≫ ψ = η'.app (op (Variety.point k)) (α.symm v) := h3
      rwa [hη0, hη'0, Equiv.apply_symm_apply] at h4

/-- **Fine moduli variety** (Milne, Remark 8.3 (b), pdf p. 98; D101): a solution $(V, \alpha)$ such that $V$ represents
the functor, i.e. $\alpha$ extends to an isomorphism of functors $F \cong h_V$ ($h_V$ lifted to the universe of $F$,
which for moduli of elliptic curves is one universe higher). -/
@[kb "milne2017mf" "Section 8, Remark 8.3 (b), fine moduli variety (pdf p. 98)"]
def IsFineModuliSolution (F : (Variety k)ᵒᵖ ⥤ Type (max u w)) (V : Variety k)
    (α : F.obj (op (Variety.point k)) ≃ (Variety.point k ⟶ V)) : Prop :=
  IsModuliSolution F V α ∧ ∃ η : F ≅ yoneda.obj V ⋙ uliftFunctor.{w},
    ∀ x, (η.hom.app (op (Variety.point k)) x).down = α x

/-- **Coarse moduli variety** (Milne, Remark 8.3 (b), pdf p. 98; D101): a solution that is not fine. -/
@[kb "milne2017mf" "Section 8, Remark 8.3 (b), coarse moduli variety (pdf p. 98)"]
def IsCoarseModuliSolution (F : (Variety k)ᵒᵖ ⥤ Type (max u w)) (V : Variety k)
    (α : F.obj (op (Variety.point k)) ≃ (Variety.point k ⟶ V)) : Prop :=
  IsModuliSolution F V α ∧ ¬ IsFineModuliSolution.{u, w} F V α

end ModularFormsKB.Milne
