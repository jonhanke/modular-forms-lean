import ModularFormsKB.Milne.Ch8.EllipticModuliProof
import ModularFormsKB.Milne.Ch8.LegendreCounterexample

/-!
# Milne, Chapter 8: transport of solutions, and Theorem 8.8 for $N = 1$

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 8 (pdf pp. 97–100).

- `isModuliSolution_of_natIso`: a solution of a moduli problem $F'$ is a solution of every problem $F \cong F'$.
- `levelFunctorIso`: an isomorphism of moduli problems $\mathcal P \cong \mathcal Q$ over `Ell/k` gives an isomorphism
  of the moduli problems `levelFunctor P ≅ levelFunctor Q` on varieties.
- `levelNFunctorIsoOfForall`: when every pair satisfies the Weil pairing condition, $\mathcal E_N$ is the moduli
  problem of all pairs with a level-$N$ structure.
- `levelModuliSolution_one`: **Theorem 8.8 for $N = 1$**. A level-one structure is unique (Tau Ceti's
  `gammaLevelOneIso`) and the Weil pairing $e_1$ takes values in the trivial group $\mu_1$, so $\mathcal E_1 \cong
  \mathcal E$ and Theorem 8.4 (`ellipticModuliSolution`) applies.
-/

universe u w

open AlgebraicGeometry CategoryTheory Opposite TauCeti.AlgebraicGeometry MonoidalCategory

noncomputable section

namespace ModularFormsKB.Milne

variable {k : Type u} [Field k]

/-- **Solutions transport along isomorphisms of moduli problems.** -/
theorem isModuliSolution_of_natIso {F F' : (Variety k)ᵒᵖ ⥤ Type w} (e : F ≅ F') {V : Variety k}
    {α' : F'.obj (op (Variety.point k)) ≃ (Variety.point k ⟶ V)} (h : IsModuliSolution F' V α') :
    IsModuliSolution F V ((e.app (op (Variety.point k))).toEquiv.trans α') := by
  have natH : ∀ {T : Variety k} (t : Variety.point k ⟶ T) (f : F.obj (op T)),
      e.hom.app (op (Variety.point k)) (F.map t.op f) = F'.map t.op (e.hom.app (op T) f) := fun t f ↦
    ConcreteCategory.congr_hom (e.hom.naturality t.op) f
  have natI : ∀ {T : Variety k} (t : Variety.point k ⟶ T) (f : F'.obj (op T)),
      e.inv.app (op (Variety.point k)) (F'.map t.op f) = F.map t.op (e.inv.app (op T) f) := fun t f ↦
    ConcreteCategory.congr_hom (e.inv.naturality t.op) f
  refine ⟨fun T f ↦ ?_, fun Z β hβ ↦ ?_⟩
  · obtain ⟨φ, hφ⟩ := h.regular T (e.hom.app (op T) f)
    refine ⟨φ, fun t ↦ ?_⟩
    rw [hφ]
    change _ = α' (e.hom.app _ (F.map t.op f))
    rw [natH]
  · obtain ⟨ψ, hψ⟩ := h.universal Z (fun x ↦ β (e.inv.app _ x)) (fun T f ↦ by
      obtain ⟨φ, hφ⟩ := hβ T (e.inv.app (op T) f)
      exact ⟨φ, fun t ↦ by rw [hφ, natI]⟩)
    exact ⟨ψ, fun v ↦ hψ v⟩

section LevelFunctorIso

variable {P Q : ModuliProblem (Spec (CommRingCat.of k))}

/-- The equivalence of pairs induced by an isomorphism of moduli problems. -/
def LevelPair.congr (e : P ≅ Q) (V : Variety k) : LevelPair P V ≃ LevelPair Q V :=
  Equiv.sigmaCongrRight fun E ↦ (e.app (op (V.ellObj E))).toEquiv

theorem LevelPair.rel_congr (e : P ≅ Q) {V : Variety k} (x y : LevelPair P V) :
    LevelPair.Rel x y ↔ LevelPair.Rel (LevelPair.congr e V x) (LevelPair.congr e V y) := by
  have nat : ∀ (f : V.ellObj x.1 ⟶ V.ellObj y.1),
      Q.map f.op (e.hom.app _ y.2) = e.hom.app _ (P.map f.op y.2) := fun f ↦
    (ConcreteCategory.congr_hom (e.hom.naturality f.op) y.2).symm
  constructor
  · rintro ⟨f, hf, hfy⟩
    refine ⟨f, hf, ?_⟩
    change Q.map f.op (e.hom.app _ y.2) = e.hom.app _ x.2
    rw [nat, hfy]
  · rintro ⟨f, hf, hfy⟩
    refine ⟨f, hf, ?_⟩
    exact (e.app _).toEquiv.injective ((nat f).symm.trans hfy)

theorem LevelPair.congr_pull (e : P ≅ Q) {V W : Variety k} (φ : W ⟶ V) (x : LevelPair P V) :
    LevelPair.congr e W (LevelPair.pull φ x) = LevelPair.pull φ (LevelPair.congr e V x) := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  exact ConcreteCategory.congr_hom (e.hom.naturality (LevelPair.pullHom φ x.1).op) x.2

/-- **An isomorphism of moduli problems over `Ell/k` gives an isomorphism of moduli problems on varieties.** -/
def levelFunctorIso (e : P ≅ Q) : levelFunctor P ≅ levelFunctor Q :=
  NatIso.ofComponents
    (fun V ↦ (Quotient.congr (LevelPair.congr e V.unop) (LevelPair.rel_congr e)).toIso)
    (fun {V W} φ ↦ by
      ext x
      induction x using Quotient.inductionOn with
      | h x =>
      change Quotient.mk _ (LevelPair.congr e W.unop (LevelPair.pull φ.unop x)) =
        Quotient.mk _ (LevelPair.pull φ.unop (LevelPair.congr e V.unop x))
      rw [LevelPair.congr_pull])

end LevelFunctorIso

section LevelN

variable [IsSepClosed k] {N : ℕ} [NeZero N]

/-- **When every pair has Weil pairing $\zeta$, $\mathcal E_N$ is the moduli problem of all pairs with a level-$N$
structure.** -/
def levelNFunctorIsoOfForall (hN : (N : k) ≠ 0) (ζ : k)
    (h : ∀ (V : Variety k) (x : LevelPair (ModuliProblem.gamma (Spec (CommRingCat.of k)) N) V),
      HasWeilPairing N hN ζ x) :
    levelNFunctor hN ζ ≅ levelFunctor (ModuliProblem.gamma (Spec (CommRingCat.of k)) N) :=
  NatIso.ofComponents
    (fun V ↦ (Quotient.congr (Equiv.subtypeUnivEquiv (h V.unop)) (fun _ _ ↦ Iff.rfl)).toIso)
    (fun {V W} φ ↦ by
      ext x
      induction x using Quotient.inductionOn with
      | h x => rfl)

end LevelN

section LevelOne

variable [IsAlgClosed k]

/-- **Every pair has Weil pairing $1$ at level one**: $e_1$ takes values in the trivial group $\mu_1$. -/
theorem hasWeilPairing_one (hk : ((1 : ℕ) : k) ≠ 0) {V : Variety k}
    (x : LevelPair (ModuliProblem.gamma (Spec (CommRingCat.of k)) 1) V) : HasWeilPairing 1 hk 1 x := by
  intro v
  set Ef := x.1.baseChange v.hom.left
  obtain ⟨W, hW, e0, he0, hz⟩ := Ef.exists_iso_toEllipticCurveGeom
  let a : (Variety.point k).ellObj W.toEllipticCurveGeom ⟶ (Variety.point k).ellObj Ef :=
    Ch8Counterexample.isoHom _ e0 he0 hz
  refine ⟨W, hW, a ≫ LevelPair.pullHom v x.1, ?_, ?_⟩
  · rw [EllObj.comp_base]
    change 𝟙 _ ≫ (LevelPair.pullHom v x.1).base = _
    rw [Category.id_comp, LevelPair.pullHom_base]
  · classical
    intro S T _ _
    set z := (TauCeti.Isogeny.weilPairing W 1 hk S T).toMul
    have hz1 : (z : kˣ) = 1 := by
      have := (mem_rootsOfUnity 1 (z : kˣ)).mp z.2
      rwa [pow_one] at this
    rw [hz1, Units.val_one]

/-- $\mathcal E_1 \cong \mathcal E$. -/
def levelNOneIso (hk : ((1 : ℕ) : k) ≠ 0) : levelNFunctor hk (1 : k) ≅ ellipticFunctor k :=
  levelNFunctorIsoOfForall hk 1 (fun _ ↦ hasWeilPairing_one hk) ≪≫
    levelFunctorIso (ModuliProblem.gammaLevelOneIso _)

variable (k) in
/-- **Milne, Theorem 8.8 for $N = 1$**, unconditionally: the affine line with the $j$-invariant. -/
theorem levelModuliSolution_one : LevelModuliSolution k 1 := by
  refine ⟨fun hN ζ hζ ↦ ?_⟩
  have hζ1 : ζ = 1 := by simpa using hζ.pow_eq_one
  subst hζ1
  obtain ⟨α, -, hα⟩ := (ellipticModuliSolution k).solution
  exact ⟨affineLine k, _, isModuliSolution_of_natIso (levelNOneIso hN) hα⟩

end LevelOne

end ModularFormsKB.Milne
