import ModularFormsKB.Milne.Ch8.CyclicThreeGenerator
import ModularFormsKB.Milne.Ch8.CyclicTwoDescent

/-!
# Milne, Chapter 8 (towards Theorem 8.6 for $N = 3$): independence of the generator

For points $P, Q$ of exact order three with the same divisor $[P] + [2P] + [3P] = [Q] + [2Q] + [3Q]$, over a scheme
on which $3$ is invertible, $Q$ agrees pointwise with $P$ or with $2P$ (`eq_or_eq_sq`); on the open set where it agrees
with one of them it is equal to it (`eq_of_forall_eq`, from `eq_of_ker_mul_eq`); and the invariant map is unchanged
by $P \mapsto -P = 2P$ (`tMap_inv`). Hence `tMap (Q) = tMap (P)` (`tMap_eq_of_multiplesDivisor_eq`).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits TauCeti.AlgebraicGeometry MonoidalCategory MonObj
  CartesianMonoidalCategory

noncomputable section

namespace ModularFormsKB.Milne.CyclicThree

open CyclicTwo

variable {S : Scheme.{u}} {E : EllipticCurveGeom S} {P : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}

/-- Two sections of `E` through the same point lie over the same point of the base. -/
theorem base_eq {f g : S ⟶ E.carrier} (hf : f ≫ E.structureMap = 𝟙 S) (hg : g ≫ E.structureMap = 𝟙 S) {s t : S}
    (h : f t = g s) : t = s := by
  have := congrArg E.structureMap h
  rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hf, hg] at this

theorem natCast_ne_zero_of_hom {X Y : Scheme.{u}} (f : X ⟶ Y) {n : ℕ} (h : ∀ y, (n : Y.residueField y) ≠ 0)
    (x : X) : (n : X.residueField x) ≠ 0 := by
  intro hx
  apply h (f x)
  apply (f.residueFieldMap x).hom.injective
  rw [map_natCast, hx, map_zero]

variable (h3 : ∀ s : S, ((3 : ℕ) : S.residueField s) ≠ 0)

section Cases

variable {Q : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} (hP : E.IsOfExactOrder P 3) (hQ : E.IsOfExactOrder Q 3)
  (h : E.multiplesDivisor P 3 = E.multiplesDivisor Q 3)

include h3 hP hQ h in
/-- **The other generator agrees pointwise with $P$ or with $2P$.** -/
theorem eq_or_eq_sq (s : S) : Q.left s = P.left s ∨ Q.left s = (P ^ 2).left s := by
  have hmem : Q.left s ∈ ((E.multiplesDivisor Q 3).support : Set E.carrier) := by
    rw [EllipticCurveGeom.coe_support_multiplesDivisor]
    exact Set.mem_iUnion₂.mpr ⟨0, by norm_num, s, by rw [zero_add, pow_one]⟩
  rw [← h, EllipticCurveGeom.coe_support_multiplesDivisor] at hmem
  obtain ⟨a, ha, t, ht⟩ := Set.mem_iUnion₂.mp hmem
  have hts := base_eq (EllipticCurveGeom.left_comp_structureMap _) (EllipticCurveGeom.left_comp_structureMap _) ht
  subst hts
  interval_cases a
  · left; simpa using ht.symm
  · right; exact ht.symm
  · exfalso
    rw [show (2 + 1 : ℕ) = 3 from rfl, hP.pow_eq_one, EllipticCurveGeom.hom_one_left] at ht
    exact ne_zero_one h3 hQ t ht.symm

include h3 hQ h in
/-- **Where $Q$ agrees pointwise with one of $P$, $2P$, it is equal to it.** -/
theorem eq_of_forall_eq {R R' : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} (hRR' : ∀ s, R.left s ≠ R'.left s)
    (hdiv : E.multiplesDivisor P 3 = Scheme.Hom.ker (Y := E.carrier) R.left *
      (Scheme.Hom.ker (Y := E.carrier) R'.left * E.zero.ker))
    (hR : ∀ s, Q.left s = R.left s) : Q = R := by
  have hQπ := EllipticCurveGeom.left_comp_structureMap Q
  have hQ2π := EllipticCurveGeom.left_comp_structureMap (Q ^ 2)
  have hR'π := EllipticCurveGeom.left_comp_structureMap R'
  have hzπ : E.zero ≫ E.structureMap = 𝟙 S := E.zero_comp
  have := isClosedImmersion_section hQ2π
  have := isClosedImmersion_section hR'π
  refine eq_of_ker_mul_eq (A := Scheme.Hom.ker (Y := E.carrier) (Q ^ 2).left * E.zero.ker)
    (B := Scheme.Hom.ker (Y := E.carrier) R'.left * E.zero.ker) hR (fun s ↦ ?_) ?_
  · let Z : Set E.carrier := Set.range (Q ^ 2).left ∪ Set.range R'.left ∪ Set.range E.zero
    have hZ : IsClosed Z :=
      ((Q ^ 2).left.isClosedEmbedding.isClosed_range.union R'.left.isClosedEmbedding.isClosed_range).union
        E.zero.isClosedEmbedding.isClosed_range
    have hs : Q.left s ∉ Z := by
      rintro ((⟨t, ht⟩ | ⟨t, ht⟩) | ⟨t, ht⟩)
      · obtain rfl := base_eq hQ2π hQπ ht
        exact ne_sq h3 hQ t ht.symm
      · obtain rfl := base_eq hR'π hQπ ht
        exact hRR' t ((hR t).symm.trans ht.symm)
      · obtain rfl := base_eq hzπ hQπ ht
        exact ne_zero_one h3 hQ t ht.symm
    obtain ⟨V, hV, hsV, hVZ⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨_, hZ.isOpen_compl⟩) hs
    let V' : E.carrier.affineOpens := ⟨V, hV⟩
    have hd : ∀ {T : Set E.carrier}, T ⊆ Z → Disjoint (V'.1 : Set E.carrier) T := fun hT ↦
      Set.disjoint_left.mpr fun y hy hy' ↦ hVZ hy (hT hy')
    have h1 := ideal_eq_top_of_disjoint (Scheme.Hom.ker (Y := E.carrier) (Q ^ 2).left) V'
      (by rw [support_ker_section hQ2π]; exact hd (fun y hy ↦ Or.inl (Or.inl hy)))
    have h2 := ideal_eq_top_of_disjoint (Scheme.Hom.ker (Y := E.carrier) R'.left) V'
      (by rw [support_ker_section hR'π]; exact hd (fun y hy ↦ Or.inl (Or.inr hy)))
    have h0 := ideal_eq_top_of_disjoint E.zero.ker V'
      (by rw [support_ker_section hzπ]; exact hd (fun y hy ↦ Or.inr hy))
    refine ⟨V', hsV, ?_, ?_⟩
    · rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, h1, h0, Ideal.top_mul]
    · rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, h2, h0, Ideal.top_mul]
  · rw [← hdiv, h, multiplesDivisor_three hQ.pow_eq_one, _root_.mul_assoc]

end Cases

/-! ### The invariant map of a cyclic subgroup of order three -/

section Invariant

variable {k : Type u} [Field k] (p : S ⟶ Spec (CommRingCat.of k))

theorem tMap_congr {P Q : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} (h : P = Q) (hP3 : P ^ 3 = 1)
    (hP0 : ∀ s, P.left s ≠ E.zero s) (hQ3 : Q ^ 3 = 1) (hQ0 : ∀ s, Q.left s ≠ E.zero s) :
    tMap p hP3 hP0 = tMap p hQ3 hQ0 := by
  subst h; rfl

theorem isPullback_neg (E : EllipticCurveGeom S) : IsPullback E.neg E.structureMap E.structureMap (𝟙 S) :=
  IsPullback.of_horiz_isIso ⟨by rw [EllipticCurveGeom.neg_structureMap, Category.comp_id]⟩

/-- **The invariant map is unchanged by** $P \mapsto -P$ (naturality along the automorphism $-1$). -/
theorem tMap_inv (hP3 : P ^ 3 = 1) (hP0 : ∀ s, P.left s ≠ E.zero s) (hP3' : P⁻¹ ^ 3 = 1)
    (hP0' : ∀ s, P⁻¹.left s ≠ E.zero s) : tMap p hP3' hP0' = tMap p hP3 hP0 := by
  have := tMap_comp p p hP3 hP0 hP3' hP0' (isPullback_neg E)
    (by rw [EllipticCurveGeom.zero_neg, Category.id_comp])
    (by rw [EllipticCurveGeom.hom_inv_left, Category.assoc, EllipticCurveGeom.neg_neg]; simp)
    (Category.id_comp p)
  rwa [Category.id_comp] at this

variable {Q : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} (hP : E.IsOfExactOrder P 3) (hQ : E.IsOfExactOrder Q 3)
  (h : E.multiplesDivisor P 3 = E.multiplesDivisor Q 3)

include h3 hP hQ h in
/-- The two invariant maps agree on an open set where $Q$ agrees pointwise with $P$ or with $2P$. -/
theorem tMap_restrict_eq (U : S.Opens) (R R' : 𝟙_ (Over S) ⟶ Over.mk E.structureMap)
    (hRR : (R = P ∧ R' = P ^ 2) ∨ (R = P ^ 2 ∧ R' = P)) (hRU : ∀ u : U, Q.left (U.ι u) = R.left (U.ι u)) :
    U.ι ≫ tMap p hQ.pow_eq_one (ne_zero_one h3 hQ) = U.ι ≫ tMap p hP.pow_eq_one (ne_zero_one h3 hP) := by
  set c := U.ι
  let E' := E.baseChange c
  let g := CyclicTwo.Gen.bcg E c
  have hg : IsPullback g E'.structureMap E.structureMap c := E.isPullback_baseChange c
  have h0 : E'.zero ≫ g = c ≫ E.zero := CyclicTwo.Gen.bcg_zero E c
  let pb := EllipticCurveGeom.pointsPullback hg h0
  have h3' := natCast_ne_zero_of_hom c h3
  have hP' : E'.IsOfExactOrder (pb P) 3 := hP.pointsPullback _ _
  have hQ' : E'.IsOfExactOrder (pb Q) 3 := hQ.pointsPullback _ _
  have hdiv : E'.multiplesDivisor (pb P) 3 = E'.multiplesDivisor (pb Q) 3 := by
    rw [EllipticCurveGeom.multiplesDivisor_pointsPullback, EllipticCurveGeom.multiplesDivisor_pointsPullback, h]
  have hginj : Function.Injective g := g.isOpenEmbedding.injective
  have hpt : ∀ X : 𝟙_ (Over S) ⟶ Over.mk E.structureMap, (pb X).left ≫ g = c ≫ X.left :=
    EllipticCurveGeom.pointsPullback_left_comp hg h0
  have hval : ∀ (X : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) (u : U), g ((pb X).left u) = X.left (c u) := by
    intro X u
    have e := congrArg (fun f ↦ f u) (hpt X)
    exact e
  have hRU' : ∀ u, (pb Q).left u = (pb R).left u := fun u ↦ hginj ((hval Q u).trans ((hRU u).trans (hval R u).symm))
  have hP'3 := multiplesDivisor_three (E := E') hP'.pow_eq_one
  have eQ := tMap_comp p (c ≫ p) hQ.pow_eq_one (ne_zero_one h3 hQ) hQ'.pow_eq_one (ne_zero_one h3' hQ')
    hg h0 (hpt Q) rfl
  have eP := tMap_comp p (c ≫ p) hP.pow_eq_one (ne_zero_one h3 hP) hP'.pow_eq_one (ne_zero_one h3' hP')
    hg h0 (hpt P) rfl
  rw [← eQ, ← eP]
  rcases hRR with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hQR : pb Q = pb R := by
      refine eq_of_forall_eq h3' hQ' hdiv (R' := pb (R ^ 2)) (fun u ↦ ?_) ?_ hRU'
      · rw [map_pow]; exact ne_sq h3' hP' u
      · rw [hP'3, map_pow, _root_.mul_assoc]
    exact tMap_congr _ hQR _ _ _ _
  · have hQR : pb Q = pb (R' ^ 2) := by
      refine eq_of_forall_eq h3' hQ' hdiv (R' := pb R') (fun u ↦ ?_) ?_ hRU'
      · rw [map_pow]; exact (ne_sq h3' hP' u).symm
      · rw [hP'3, map_pow, mul_left_comm, ← _root_.mul_assoc]
    have hinv : pb R' ^ 2 = (pb R')⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hP'.pow_eq_one])
    rw [map_pow] at hQR
    rw [tMap_congr _ (hQR.trans hinv) _ _ (by rw [inv_pow, hP'.pow_eq_one, inv_one])
      (fun u ↦ by rw [← hinv]; exact ne_zero_two h3' hP' u)]
    exact tMap_inv _ _ _ _ _

include h3 hP hQ h in
/-- **The invariant map does not depend on the generator** of a cyclic subgroup of order three. -/
theorem tMap_eq_of_multiplesDivisor_eq :
    tMap p hQ.pow_eq_one (ne_zero_one h3 hQ) = tMap p hP.pow_eq_one (ne_zero_one h3 hP) := by
  refine Scheme.hom_ext_of_forall _ _ fun s ↦ ?_
  have hPπ := EllipticCurveGeom.left_comp_structureMap P
  have hP2π := EllipticCurveGeom.left_comp_structureMap (P ^ 2)
  have hQπ := EllipticCurveGeom.left_comp_structureMap Q
  have := isClosedImmersion_section hPπ
  have := isClosedImmersion_section hP2π
  rcases eq_or_eq_sq h3 hP hQ h s with hs | hs
  · let U : S.Opens := ⟨(Q.left ⁻¹' Set.range (P ^ 2).left)ᶜ,
      ((P ^ 2).left.isClosedEmbedding.isClosed_range.preimage Q.left.continuous).isOpen_compl⟩
    refine ⟨U, ?_, tMap_restrict_eq h3 p hP hQ h U P (P ^ 2) (Or.inl ⟨rfl, rfl⟩) fun u ↦ ?_⟩
    · rintro ⟨t, ht⟩
      obtain rfl := base_eq hP2π hQπ ht
      exact ne_sq h3 hP t (hs.symm.trans ht.symm)
    · rcases eq_or_eq_sq h3 hP hQ h (U.ι u) with hu | hu
      · exact hu
      · exact absurd ⟨_, hu.symm⟩ u.2
  · let U : S.Opens := ⟨(Q.left ⁻¹' Set.range P.left)ᶜ,
      (P.left.isClosedEmbedding.isClosed_range.preimage Q.left.continuous).isOpen_compl⟩
    refine ⟨U, ?_, tMap_restrict_eq h3 p hP hQ h U (P ^ 2) P (Or.inr ⟨rfl, rfl⟩) fun u ↦ ?_⟩
    · rintro ⟨t, ht⟩
      obtain rfl := base_eq hPπ hQπ ht
      exact ne_sq h3 hP t (ht.trans hs)
    · rcases eq_or_eq_sq h3 hP hQ h (U.ι u) with hu | hu
      · exact absurd ⟨_, hu.symm⟩ u.2
      · exact hu

end Invariant

end ModularFormsKB.Milne.CyclicThree
