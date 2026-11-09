import ModularFormsKB.Milne.Ch8.CyclicThreeChart

/-!
# Milne, Chapter 8 (towards Theorem 8.6 for $N = 3$): the invariant does not depend on the generator

Let $E$ be an elliptic curve over a scheme $S$ with $3$ invertible in every residue field, and let $P, Q$ be points of
exact order three generating the same cyclic subgroup: $[P] + [2P] + [3P] = [Q] + [2Q] + [3Q]$. Then the invariant maps
of `CyclicThreeChart` agree: `tMap (Q) = tMap (P)` (`tMap_eq_of_multiplesDivisor_eq`).

Unlike the case of order two (`CyclicTwo.eq_of_multiplesDivisor_two_eq`), $Q$ need not equal $P$; but $S$ is covered by
the two open sets $U_1 = \{s : Q(s) \notin 2P(S)\}$ and $U_2 = \{s : Q(s) \notin P(S)\}$, with $Q = P$ over $U_1$ and
$Q = 2P = -P$ over $U_2$ (`eq_of_ker_mul_eq`: two sections with the same image whose kernels agree up to factors which
are the unit ideal near that image are equal). The invariant map is natural, so it is unchanged by the automorphism
$-1$ of $E$, which carries $P$ to $-P$ (`tMap_inv`).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits TauCeti.AlgebraicGeometry MonoidalCategory MonObj
  CartesianMonoidalCategory

noncomputable section

namespace ModularFormsKB.Milne.CyclicThree

open CyclicTwo

variable {S : Scheme.{u}} {E : EllipticCurveGeom S}

/-! ### Pointwise distinctness -/

theorem left_comp_translation (P R : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) :
    R.left ≫ (TauCeti.leftTranslation P).hom.left = (P * R).left := by
  rw [← Over.comp_left, TauCeti.comp_leftTranslation_hom, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

/-- Two points whose quotient misses the zero section are distinct at every point of the base. -/
theorem left_apply_ne {P Q : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} (h : ∀ s, (P⁻¹ * Q).left s ≠ E.zero s) (s : S) :
    P.left s ≠ Q.left s := by
  intro hs
  apply h s
  have e1 := left_comp_translation P⁻¹ Q
  have e2 := left_comp_translation P⁻¹ P
  rw [inv_mul_cancel, EllipticCurveGeom.hom_one_left] at e2
  rw [← e1, Scheme.Hom.comp_apply, ← hs, ← Scheme.Hom.comp_apply, e2]
  rfl

variable {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}

/-- A natural number nonzero in $k$ is nonzero in every residue field of a scheme over $k$. -/
theorem natCast_ne_zero_residue {X : Scheme.{u}} {k : Type u} [Field k] {n : ℕ} (hn : (n : k) ≠ 0)
    (q : X ⟶ Spec (CommRingCat.of k)) (s : X) : (n : X.residueField s) ≠ 0 := by
  let f : k →+* (Spec (.of k)).residueField (q s) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Spec (.of k)).evaluation ⊤ (q s) trivial).hom
  intro h
  apply hn
  apply f.injective
  apply (q.residueFieldMap s).hom.injective
  rw [map_natCast, map_natCast, h, map_zero, map_zero]

variable (h3 : ∀ s : S, ((3 : ℕ) : S.residueField s) ≠ 0)

include h3 in
theorem ne_zero_one (hP : E.IsOfExactOrder P 3) (s : S) : P.left s ≠ E.zero s := by
  simpa using hP.pow_left_apply_ne_zero (h3 s) (k := 1) one_pos (by norm_num)

include h3 in
theorem ne_zero_two (hP : E.IsOfExactOrder P 3) (s : S) : (P ^ 2).left s ≠ E.zero s :=
  hP.pow_left_apply_ne_zero (h3 s) (k := 2) two_pos (by norm_num)

include h3 in
theorem ne_sq (hP : E.IsOfExactOrder P 3) (s : S) : P.left s ≠ (P ^ 2).left s := by
  refine left_apply_ne (fun s ↦ ?_) s
  rw [sq, inv_mul_cancel_left]
  exact ne_zero_one h3 hP s

/-- The divisor $[P] + [2P] + [3P]$ of a point with $P^3 = 1$. -/
theorem multiplesDivisor_three (hP3 : P ^ 3 = 1) :
    E.multiplesDivisor P 3 =
      Scheme.Hom.ker (Y := E.carrier) P.left * Scheme.Hom.ker (Y := E.carrier) (P ^ 2).left * E.zero.ker := by
  have htop : ∀ J : E.carrier.IdealSheafData, ⊤ * J = J := fun J ↦ by
    ext U : 2
    simp
  rw [EllipticCurveGeom.multiplesDivisor_succ, EllipticCurveGeom.multiplesDivisor_succ,
    EllipticCurveGeom.multiplesDivisor_succ, EllipticCurveGeom.multiplesDivisor_zero, htop, zero_add, pow_one,
    show (1 + 1 : ℕ) = 2 from rfl, show (2 + 1 : ℕ) = 3 from rfl, hP3, EllipticCurveGeom.hom_one_left]
  congr 2

/-! ### Two sections with the same image and the same kernel up to local units -/

/-- **Two sections agreeing pointwise, whose kernels agree up to factors that are the unit ideal near their image,
are equal.** -/
theorem eq_of_ker_mul_eq {P Q : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {A B : E.carrier.IdealSheafData}
    (hPQ : ∀ s, P.left s = Q.left s)
    (hAB : ∀ s, ∃ U : E.carrier.affineOpens, P.left s ∈ U.1 ∧ A.ideal U = ⊤ ∧ B.ideal U = ⊤)
    (h : Scheme.Hom.ker (Y := E.carrier) P.left * A = Scheme.Hom.ker (Y := E.carrier) Q.left * B) : P = Q := by
  have hPπ : P.left ≫ E.structureMap = 𝟙 S := EllipticCurveGeom.left_comp_structureMap P
  have hQπ : Q.left ≫ E.structureMap = 𝟙 S := EllipticCurveGeom.left_comp_structureMap Q
  have := isClosedImmersion_section hPπ
  have := isClosedImmersion_section hQπ
  have hsP := support_ker_section hPπ
  have hsQ := support_ker_section hQπ
  have hrange : Set.range P.left = Set.range Q.left := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩; exact ⟨s, (hPQ s).symm⟩
    · rintro ⟨s, rfl⟩; exact ⟨s, hPQ s⟩
  have hcov : ∀ x : E.carrier, ∃ U : E.carrier.affineOpens, x ∈ U.1 ∧
      (Scheme.Hom.ker (Y := E.carrier) P.left).ideal U = (Scheme.Hom.ker (Y := E.carrier) Q.left).ideal U := by
    intro x
    by_cases hx : x ∈ Set.range P.left
    · obtain ⟨s, rfl⟩ := hx
      obtain ⟨U, hsU, hA, hB⟩ := hAB s
      refine ⟨U, hsU, ?_⟩
      have := congrArg (fun I ↦ Scheme.IdealSheafData.ideal I U) h
      simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, hA, hB, Ideal.mul_top] at this
      exact this
    · have ho : IsOpen (Set.range P.left)ᶜ := P.left.isClosedEmbedding.isClosed_range.isOpen_compl
      obtain ⟨V, hV, hxV, hVs⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨_, ho⟩) hx
      let V' : E.carrier.affineOpens := ⟨V, hV⟩
      have hd : Disjoint (V'.1 : Set E.carrier) (Set.range P.left) :=
        Set.disjoint_left.mpr fun y hy hy' ↦ hVs hy hy'
      refine ⟨V', hxV, ?_⟩
      rw [ideal_eq_top_of_disjoint _ _ (by rw [hsP]; exact hd),
        ideal_eq_top_of_disjoint _ _ (by rw [hsQ, ← hrange]; exact hd)]
  choose U hxU hU using hcov
  have hker : Scheme.Hom.ker (Y := E.carrier) P.left = Scheme.Hom.ker (Y := E.carrier) Q.left := by
    refine Scheme.IdealSheafData.ext_of_iSup_eq_top U ?_ fun x ↦ hU x
    exact top_le_iff.mp fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hxU y⟩
  exact Over.OverMorphism.ext (eq_of_ker_eq hPπ hQπ hker.symm)

end ModularFormsKB.Milne.CyclicThree
