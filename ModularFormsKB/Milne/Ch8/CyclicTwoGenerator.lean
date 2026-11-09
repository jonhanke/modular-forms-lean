import ModularFormsKB.Milne.Ch8.CyclicOne

/-!
# Milne, Chapter 8 (towards Theorem 8.6 for $N = 2$): the generator of a cyclic subgroup of order two is unique

Let $E$ be an elliptic curve over a scheme $S$ with $2$ invertible in every residue field, and let $P, Q$ be points of
exact order $2$ (Tau Ceti's `IsOfExactOrder`). If the divisors $[P] + [2P]$ and $[Q] + [2Q]$ agree, then $P = Q$
(`eq_of_multiplesDivisor_two_eq`). Both divisors are $\ker P \cdot \ker 0$; away from the zero section the second factor
is the unit ideal, and $P, Q$ miss the zero section, so $\ker P = \ker Q$; two sections with the same kernel are equal.

This is the first step of the proof of Theorem 8.6 with $N = 2$: the generators of
a cyclic subgroup of order two over the members of an fppf cover agree on the overlaps.
-/

universe u

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry MonoidalCategory MonObj

noncomputable section

namespace ModularFormsKB.Milne.CyclicTwo

/-- An ideal sheaf is the unit ideal on every affine open disjoint from its support. -/
theorem ideal_eq_top_of_disjoint {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
    (h : Disjoint (U.1 : Set X) I.support) : I.ideal U = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have hx : U.2.fromSpec ⟨m, hm.isPrime⟩ ∈ X.zeroLocus (U := U.1) (I.ideal U) ∩ U.1 := by
    rw [← U.2.fromSpec_image_zeroLocus]
    exact ⟨⟨m, hm.isPrime⟩, show (I.ideal U : Set Γ(X, U.1)) ⊆ m from hle, rfl⟩
  have hs : U.2.fromSpec ⟨m, hm.isPrime⟩ ∈ I.support :=
    (Scheme.IdealSheafData.mem_support_iff_of_mem hx.2).mpr hx.1
  exact Set.disjoint_left.mp h hx.2 hs

/-- **Two sections of a morphism with the same kernel are equal.** -/
theorem eq_of_ker_eq {S X : Scheme.{u}} {π : X ⟶ S} {f g : S ⟶ X} (hf : f ≫ π = 𝟙 S) (hg : g ≫ π = 𝟙 S)
    [IsClosedImmersion f] [IsClosedImmersion g] (h : g.ker = f.ker) : f = g := by
  have hl := IsClosedImmersion.lift_fac g f h.le
  have : IsClosedImmersion.lift g f h.le = 𝟙 S :=
    calc IsClosedImmersion.lift g f h.le = IsClosedImmersion.lift g f h.le ≫ (g ≫ π) := by
          rw [hg, Category.comp_id]
      _ = f ≫ π := by rw [← Category.assoc, hl]
      _ = 𝟙 S := hf
  rw [← hl, this, Category.id_comp]

variable {S : Scheme.{u}} {E : EllipticCurveGeom S}

/-- The divisor $[P] + [2P]$ of a point of exact order two is $\ker P \cdot \ker 0$. -/
theorem multiplesDivisor_two {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} (hP : E.IsOfExactOrder P 2) :
    E.multiplesDivisor P 2 = Scheme.Hom.ker (Y := E.carrier) P.left * E.zero.ker := by
  have h2 : P ^ 2 = 1 := hP.pow_eq_one
  have htop : ∀ J : E.carrier.IdealSheafData, ⊤ * J = J := fun J ↦ by
    ext U : 2
    simp
  rw [EllipticCurveGeom.multiplesDivisor_succ, EllipticCurveGeom.multiplesDivisor_succ,
    EllipticCurveGeom.multiplesDivisor_zero, htop, zero_add, pow_one, show (1 + 1 : ℕ) = 2 from rfl, h2,
    EllipticCurveGeom.hom_one_left]
  congr 2

/-- A section misses the support of the kernel of the zero section when it misses the zero section. -/
theorem range_disjoint_zero {P : S ⟶ E.carrier} (hP : ∀ s, P s ≠ E.zero s) (hPπ : P ≫ E.structureMap = 𝟙 S) :
    Disjoint (Set.range P) (E.zero.ker.support : Set E.carrier) := by
  rw [Scheme.Hom.support_ker, IsClosed.closure_eq E.zero.isClosedEmbedding.isClosed_range]
  rintro A hA1 hA2 x hx
  obtain ⟨s, rfl⟩ := hA1 hx
  obtain ⟨t, ht⟩ := hA2 hx
  have hts : t = s := by
    have := congrArg E.structureMap ht
    simpa [← Scheme.Hom.comp_apply, hPπ] using this
  subst hts
  exact hP t ht.symm

/-- A section of an elliptic curve is a closed immersion. -/
theorem isClosedImmersion_section {P : S ⟶ E.carrier} (hPπ : P ≫ E.structureMap = 𝟙 S) : IsClosedImmersion P := by
  have : IsClosedImmersion (P ≫ E.structureMap) := by rw [hPπ]; infer_instance
  exact .of_comp P E.structureMap

theorem support_ker_section {P : S ⟶ E.carrier} (hPπ : P ≫ E.structureMap = 𝟙 S) :
    (P.ker.support : Set E.carrier) = Set.range P := by
  haveI := isClosedImmersion_section hPπ
  rw [Scheme.Hom.support_ker, IsClosed.closure_eq P.isClosedEmbedding.isClosed_range]

/-- **The generator of a cyclic subgroup of order two is unique**, where $2$ is invertible. -/
theorem eq_of_multiplesDivisor_two_eq (h2 : ∀ s : S, ((2 : ℕ) : S.residueField s) ≠ 0)
    {P Q : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} (hP : E.IsOfExactOrder P 2) (hQ : E.IsOfExactOrder Q 2)
    (h : E.multiplesDivisor P 2 = E.multiplesDivisor Q 2) : P = Q := by
  have hP0 : ∀ s, P.left s ≠ E.zero s := fun s ↦ by
    simpa using hP.pow_left_apply_ne_zero (h2 s) (k := 1) one_pos one_lt_two
  have hQ0 : ∀ s, Q.left s ≠ E.zero s := fun s ↦ by
    simpa using hQ.pow_left_apply_ne_zero (h2 s) (k := 1) one_pos one_lt_two
  have hPπ : P.left ≫ E.structureMap = 𝟙 S := EllipticCurveGeom.left_comp_structureMap P
  have hQπ : Q.left ≫ E.structureMap = 𝟙 S := EllipticCurveGeom.left_comp_structureMap Q
  haveI := isClosedImmersion_section hPπ
  haveI := isClosedImmersion_section hQπ
  rw [multiplesDivisor_two hP, multiplesDivisor_two hQ] at h
  have hz : (E.zero.ker.support : Set E.carrier) = Set.range E.zero := by
    rw [Scheme.Hom.support_ker, IsClosed.closure_eq E.zero.isClosedEmbedding.isClosed_range]
  have hsP := support_ker_section hPπ
  have hsQ := support_ker_section hQπ
  -- the two opens covering `E`
  have hdisP := range_disjoint_zero hP0 hPπ
  have hdisQ := range_disjoint_zero hQ0 hQπ
  rw [hz] at hdisP hdisQ
  have hcov : ∀ x : E.carrier, ∃ U : E.carrier.affineOpens, x ∈ U.1 ∧
      (Disjoint (U.1 : Set E.carrier) (Set.range E.zero) ∨
        Disjoint (U.1 : Set E.carrier) (Set.range P.left ∪ Set.range Q.left)) := by
    intro x
    by_cases hx : x ∈ Set.range E.zero
    · have hxPQ : x ∉ Set.range P.left ∪ Set.range Q.left := by
        rintro (h' | h')
        · exact Set.disjoint_left.mp hdisP h' hx
        · exact Set.disjoint_left.mp hdisQ h' hx
      have ho : IsOpen (Set.range P.left ∪ Set.range Q.left)ᶜ :=
        (P.left.isClosedEmbedding.isClosed_range.union Q.left.isClosedEmbedding.isClosed_range).isOpen_compl
      obtain ⟨V, hV, hxV, hVs⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨_, ho⟩) hxPQ
      exact ⟨⟨V, hV⟩, hxV, Or.inr (Set.disjoint_left.mpr fun y hy hy' ↦ hVs hy hy')⟩
    · have ho : IsOpen (Set.range E.zero)ᶜ := E.zero.isClosedEmbedding.isClosed_range.isOpen_compl
      obtain ⟨V, hV, hxV, hVs⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨_, ho⟩) hx
      exact ⟨⟨V, hV⟩, hxV, Or.inl (Set.disjoint_left.mpr fun y hy hy' ↦ hVs hy hy')⟩
  choose U hxU hU using hcov
  have hker : Scheme.Hom.ker (Y := E.carrier) P.left = Scheme.Hom.ker (Y := E.carrier) Q.left := by
    refine Scheme.IdealSheafData.ext_of_iSup_eq_top U ?_ fun x ↦ ?_
    · exact top_le_iff.mp fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hxU y⟩
    · rcases hU x with hd | hd
      · have h0 : E.zero.ker.ideal (U x) = ⊤ := ideal_eq_top_of_disjoint _ _ (by rwa [hz])
        have := congrArg (fun I ↦ Scheme.IdealSheafData.ideal I (U x)) h
        simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, h0, Ideal.mul_top] at this
        exact this
      · rw [ideal_eq_top_of_disjoint _ _ (by rw [hsP]; exact hd.mono_right Set.subset_union_left),
          ideal_eq_top_of_disjoint _ _ (by rw [hsQ]; exact hd.mono_right Set.subset_union_right)]
  exact Over.OverMorphism.ext (eq_of_ker_eq hPπ hQπ hker.symm)

end ModularFormsKB.Milne.CyclicTwo
