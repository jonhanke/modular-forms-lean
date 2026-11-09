import ModularFormsKB.Milne.Ch8.CyclicThreeIndependence

/-!
# Generators of a cyclic subgroup of order $N$ (towards Theorem 8.6 for general $N$)

Let $E$ be an elliptic curve over a scheme $S$ with $N$ invertible in every residue field, and $P, Q$ points of exact
order $N$ with the same divisor $[P] + \dots + [NP] = [Q] + \dots + [NQ]$.

- Equality of values at a point of $S$ is a congruence for the group law (`mul_apply_congr`, `pow_apply_congr`): it is
  transported by translations.
- At every point $s$, $Q(s) = (bP)(s)$ for some $b$ prime to $N$ (`exists_coprime_apply_eq`).
- Where $Q$ agrees pointwise with $bP$, it equals $bP$ (`eq_pow_of_forall_apply_eq`, from `eq_of_ker_mul_eq`).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits TauCeti.AlgebraicGeometry MonoidalCategory MonObj
  CartesianMonoidalCategory

noncomputable section

namespace ModularFormsKB.Milne.CyclicN

open CyclicTwo CyclicThree

variable {S : Scheme.{u}} {E : EllipticCurveGeom S}

/-! ### Pointwise equality is a congruence -/

theorem mul_left_apply_congr (A : 𝟙_ (Over S) ⟶ Over.mk E.structureMap) {B B' : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
    {s : S} (h : B.left s = B'.left s) : (A * B).left s = (A * B').left s := by
  rw [← left_comp_translation A B, ← left_comp_translation A B', Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h]

theorem mul_apply_congr {A A' B B' : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {s : S} (hA : A.left s = A'.left s)
    (hB : B.left s = B'.left s) : (A * B).left s = (A' * B').left s :=
  calc (A * B).left s = (A * B').left s := mul_left_apply_congr A hB
    _ = (B' * A).left s := by rw [mul_comm]
    _ = (B' * A').left s := mul_left_apply_congr B' hA
    _ = (A' * B').left s := by rw [mul_comm]

theorem pow_apply_congr {A A' : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} {s : S} (h : A.left s = A'.left s) (n : ℕ) :
    (A ^ n).left s = (A' ^ n).left s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ]; exact mul_apply_congr ih h

theorem one_left_apply (s : S) : (1 : 𝟙_ (Over S) ⟶ Over.mk E.structureMap).left s = E.zero s := by
  rw [EllipticCurveGeom.hom_one_left]; rfl

/-! ### The other generators -/

variable {N : ℕ} (hN : ∀ s : S, (N : S.residueField s) ≠ 0) {P Q : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
  (hP : E.IsOfExactOrder P N) (hQ : E.IsOfExactOrder Q N)

include hN hP in
/-- The multiples $P, 2P, \dots, NP$ take distinct values at every point. -/
theorem pow_apply_ne_pow {a b : ℕ} (ha : a < N) (hb : b < N) (hab : a ≠ b) (s : S) :
    (P ^ a).left s ≠ (P ^ b).left s := by
  wlog hlt : a < b generalizing a b
  · exact fun h ↦ this hb ha (Ne.symm hab) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab)) h.symm
  intro h
  have h' : ((P ^ a)⁻¹ * P ^ b).left s = ((P ^ a)⁻¹ * P ^ a).left s := mul_left_apply_congr _ h.symm
  rw [inv_mul_cancel, one_left_apply, mul_comm, ← pow_sub P hlt.le] at h'
  exact hP.pow_left_apply_ne_zero (hN s) (Nat.sub_pos_of_lt hlt) (by omega) h'

include hP in
theorem pow_eq_pow_mod (m : ℕ) : P ^ m = P ^ (m % N) := by
  conv_lhs => rw [← Nat.mod_add_div m N, pow_add, pow_mul, hP.pow_eq_one, one_pow, _root_.mul_one]

include hN hP in
/-- The values of $P^{a+1}$ and $P^{c+1}$, $a \ne c < N$, are distinct at every point. -/
theorem pow_succ_apply_ne {a c : ℕ} (ha : a < N) (hc : c < N) (hac : a ≠ c) (s : S) :
    (P ^ (a + 1)).left s ≠ (P ^ (c + 1)).left s := by
  rw [pow_eq_pow_mod hP (a + 1), pow_eq_pow_mod hP (c + 1)]
  have hN0 : N ≠ 0 := by rintro rfl; exact hN s (by simp)
  refine pow_apply_ne_pow hN hP (Nat.mod_lt _ (Nat.pos_of_ne_zero hN0)) (Nat.mod_lt _ (Nat.pos_of_ne_zero hN0))
    ?_ s
  intro h
  apply hac
  have h1 : (a + 1) % N = if a + 1 = N then 0 else a + 1 := by
    split_ifs with h' <;> [rw [h', Nat.mod_self]; exact Nat.mod_eq_of_lt (by omega)]
  have h2 : (c + 1) % N = if c + 1 = N then 0 else c + 1 := by
    split_ifs with h' <;> [rw [h', Nat.mod_self]; exact Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2] at h
  split_ifs at h <;> omega

include hN hP hQ in
/-- **At every point, $Q$ agrees with $bP$ for some $b$ prime to $N$.** -/
theorem exists_coprime_apply_eq (h : E.multiplesDivisor P N = E.multiplesDivisor Q N) (s : S) :
    ∃ a < N, (a + 1).Coprime N ∧ Q.left s = (P ^ (a + 1)).left s := by
  have hN0 : N ≠ 0 := by rintro rfl; exact hN s (by simp)
  have hmem : Q.left s ∈ ((E.multiplesDivisor Q N).support : Set E.carrier) := by
    rw [EllipticCurveGeom.coe_support_multiplesDivisor]
    exact Set.mem_iUnion₂.mpr ⟨0, Nat.pos_of_ne_zero hN0, s, by rw [zero_add, pow_one]⟩
  rw [← h, EllipticCurveGeom.coe_support_multiplesDivisor] at hmem
  obtain ⟨a, ha, t, ht⟩ := Set.mem_iUnion₂.mp hmem
  have hts := base_eq (EllipticCurveGeom.left_comp_structureMap _) (EllipticCurveGeom.left_comp_structureMap _) ht
  rw [hts] at ht
  refine ⟨a, ha, ?_, ht.symm⟩
  by_contra hcop
  set g := Nat.gcd (a + 1) N
  have hg1 : 1 < g := by
    have hg0 : g ≠ 0 := Nat.gcd_ne_zero_right hN0
    have : g ≠ 1 := hcop
    omega
  set m := N / g
  have hgN : g ∣ N := Nat.gcd_dvd_right _ _
  have hga : g ∣ a + 1 := Nat.gcd_dvd_left _ _
  have hm0 : 0 < m := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hgN) (by omega)
  have hmN : m < N := Nat.div_lt_self (Nat.pos_of_ne_zero hN0) hg1
  have hQm := pow_apply_congr ht.symm m
  rw [← pow_mul] at hQm
  have hdiv : (a + 1) * m = ((a + 1) / g) * N := by
    obtain ⟨c, hc⟩ := hga
    obtain ⟨d, hd⟩ := hgN
    have hgpos : 0 < g := by omega
    have hm' : m = d := by simp only [m]; rw [hd, Nat.mul_div_cancel_left _ hgpos]
    have hc' : (a + 1) / g = c := by rw [hc, Nat.mul_div_cancel_left _ hgpos]
    rw [hm', hc', hc, hd]
    ring
  rw [hdiv, pow_mul', hP.pow_eq_one, one_pow, one_left_apply] at hQm
  exact hQ.pow_left_apply_ne_zero (hN s) hm0 hmN hQm

/-- An ideal sheaf which is a finite product of ideal sheaves that are the unit ideal on `V` is the unit ideal on
`V`. -/
theorem ideal_prod_eq_top {X : Scheme.{u}} {α : Type*} (t : Finset α) (I : α → X.IdealSheafData)
    (V : X.affineOpens) (h : ∀ i ∈ t, (I i).ideal V = ⊤) : (∏ i ∈ t, I i).ideal V = ⊤ := by
  refine Finset.prod_induction I (fun J ↦ J.ideal V = ⊤) (fun J J' hJ hJ' ↦ ?_) ?_ h
  · rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, hJ, hJ', Ideal.top_mul]
  · rfl

include hN hP hQ in
/-- **Where $Q$ agrees pointwise with $(a + 1)P$, it equals $(a + 1)P$.** -/
theorem eq_pow_of_forall_apply_eq (h : E.multiplesDivisor P N = E.multiplesDivisor Q N) {a : ℕ} (ha : a < N)
    (hR : ∀ s, Q.left s = (P ^ (a + 1)).left s) : Q = P ^ (a + 1) := by
  have h0N : 0 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  have haN : a ∈ Finset.range N := Finset.mem_range.mpr ha
  set A := ∏ c ∈ (Finset.range N).erase 0, Scheme.Hom.ker (Y := E.carrier) (Q ^ (c + 1)).left
  set B := ∏ c ∈ (Finset.range N).erase a, Scheme.Hom.ker (Y := E.carrier) (P ^ (c + 1)).left
  have hQd : E.multiplesDivisor Q N = Scheme.Hom.ker (Y := E.carrier) Q.left * A := by
    rw [EllipticCurveGeom.multiplesDivisor, ← Finset.mul_prod_erase _ _ h0N, zero_add, pow_one]
  have hPd : E.multiplesDivisor P N = Scheme.Hom.ker (Y := E.carrier) (P ^ (a + 1)).left * B := by
    rw [EllipticCurveGeom.multiplesDivisor, ← Finset.mul_prod_erase _ _ haN]
  refine eq_of_ker_mul_eq (A := A) (B := B) hR (fun s ↦ ?_) (by rw [← hQd, ← h, hPd])
  have hcl : ∀ R : 𝟙_ (Over S) ⟶ Over.mk E.structureMap, IsClosed (Set.range R.left) := fun R ↦ by
    have := isClosedImmersion_section (EllipticCurveGeom.left_comp_structureMap R)
    exact R.left.isClosedEmbedding.isClosed_range
  let Z : Set E.carrier := (⋃ c ∈ (Finset.range N).erase 0, Set.range (Q ^ (c + 1)).left) ∪
    ⋃ c ∈ (Finset.range N).erase a, Set.range (P ^ (c + 1)).left
  have hZ : IsClosed Z :=
    ((Finset.finite_toSet ((Finset.range N).erase 0)).isClosed_biUnion fun c _ ↦ hcl _).union
      ((Finset.finite_toSet ((Finset.range N).erase a)).isClosed_biUnion fun c _ ↦ hcl _)
  have hs : Q.left s ∉ Z := by
    rintro (hz | hz)
    · obtain ⟨c, hc, t, ht⟩ := Set.mem_iUnion₂.mp hz
      have hts := base_eq (EllipticCurveGeom.left_comp_structureMap _)
        (EllipticCurveGeom.left_comp_structureMap _) ht
      rw [hts] at ht
      obtain ⟨hc0, hcN⟩ := Finset.mem_erase.mp hc
      exact pow_succ_apply_ne hN hQ (Finset.mem_range.mp hcN) (by omega) hc0 s
        (ht.trans (by rw [zero_add, pow_one]))
    · obtain ⟨c, hc, t, ht⟩ := Set.mem_iUnion₂.mp hz
      have hts := base_eq (EllipticCurveGeom.left_comp_structureMap _)
        (EllipticCurveGeom.left_comp_structureMap _) ht
      rw [hts] at ht
      obtain ⟨hca, hcN⟩ := Finset.mem_erase.mp hc
      exact pow_succ_apply_ne hN hP (Finset.mem_range.mp hcN) ha hca s (ht.trans (hR s))
  obtain ⟨V, hV, hsV, hVZ⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨_, hZ.isOpen_compl⟩) hs
  let V' : E.carrier.affineOpens := ⟨V, hV⟩
  refine ⟨V', hsV, ideal_prod_eq_top _ _ _ fun c hc ↦ ?_, ideal_prod_eq_top _ _ _ fun c hc ↦ ?_⟩
  · refine ideal_eq_top_of_disjoint _ _ ?_
    rw [support_ker_section (EllipticCurveGeom.left_comp_structureMap _)]
    exact Set.disjoint_left.mpr fun y hy hy' ↦ hVZ hy (Or.inl (Set.mem_iUnion₂.mpr ⟨c, hc, hy'⟩))
  · refine ideal_eq_top_of_disjoint _ _ ?_
    rw [support_ker_section (EllipticCurveGeom.left_comp_structureMap _)]
    exact Set.disjoint_left.mpr fun y hy hy' ↦ hVZ hy (Or.inr (Set.mem_iUnion₂.mpr ⟨c, hc, hy'⟩))

include hN hP in
/-- **$aP$ has exact order $N$ for $a$ prime to $N$.** -/
theorem isOfExactOrder_pow_of_coprime [NeZero N] {a : ℕ} (ha : a.Coprime N) : E.IsOfExactOrder (P ^ a) N := by
  have hcube : (P ^ a) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hP.pow_eq_one, one_pow]
  let φ := (TauCeti.zmodMonoidHomEquiv N _).symm ⟨P ^ a, hcube⟩
  have hφ1 : φ (.ofAdd 1) = P ^ a := TauCeti.zmodMonoidHomEquiv_symm_apply_ofAdd_one _
  have hφ : E.IsFiberwiseInjective φ := by
    refine EllipticCurveGeom.isFiberwiseInjective_zmod_iff.mpr fun j hj hjN s ↦ ?_
    rw [hφ1, ← pow_mul, pow_eq_pow_mod hP]
    have hmod : (a * j) % N ≠ 0 := by
      intro h0
      have hdvd : N ∣ a * j := Nat.dvd_of_mod_eq_zero h0
      have : N ∣ j := (Nat.Coprime.dvd_of_dvd_mul_left ha.symm hdvd)
      exact absurd (Nat.le_of_dvd hj this) (not_le.mpr hjN)
    exact hP.pow_left_apply_ne_zero (hN s) (Nat.pos_of_ne_zero hmod) (Nat.mod_lt _ (NeZero.pos N))
  have := EllipticCurveGeom.isFiberwiseInjective_iff_isOfNaiveExactOrder.mp hφ
  rw [hφ1] at this
  exact this.isOfExactOrder hN

theorem pow_eq_pow_mod' {X : 𝟙_ (Over S) ⟶ Over.mk E.structureMap} (hX : X ^ N = 1) (m : ℕ) :
    X ^ m = X ^ (m % N) := by
  conv_lhs => rw [← Nat.mod_add_div m N, pow_add, pow_mul, hX, one_pow, _root_.mul_one]

/-- The divisor $[P] + \dots + [NP]$ indexed by $\mathbb Z/N$. -/
theorem multiplesDivisor_eq_zmod [NeZero N] (h1 : 1 < N) {X : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
    (hX : X ^ N = 1) : E.multiplesDivisor X N = E.pointsDivisor fun a : ZMod N ↦ X ^ a.val := by
  rw [EllipticCurveGeom.multiplesDivisor_eq_pointsDivisor]
  have hinj : Function.Injective fun i : Fin N ↦ (((i.val + 1 : ℕ)) : ZMod N) := by
    intro i j hij
    have := congrArg ZMod.val hij
    simp only [ZMod.val_natCast] at this
    have hi := i.isLt
    have hj := j.isLt
    apply Fin.ext
    rcases Nat.lt_or_ge (i.val + 1) N with h | h <;> rcases Nat.lt_or_ge (j.val + 1) N with h' | h'
    · rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt h'] at this; omega
    · rw [Nat.mod_eq_of_lt h, show j.val + 1 = N by omega, Nat.mod_self] at this; omega
    · rw [show i.val + 1 = N by omega, Nat.mod_self, Nat.mod_eq_of_lt h'] at this; omega
    · omega
  let e : Fin N ≃ ZMod N := Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, by rw [Fintype.card_fin, ZMod.card]⟩)
  rw [← EllipticCurveGeom.pointsDivisor_comp_equiv _ e]
  congr 1
  funext i
  simp only [Function.comp_apply, e, Equiv.ofBijective_apply, ZMod.val_natCast]
  exact pow_eq_pow_mod' hX _

/-- **A unit multiple of $P$ has the same divisor** $[P] + \dots + [NP]$. -/
theorem multiplesDivisor_pow_unit [NeZero N] (h1 : 1 < N) {X : 𝟙_ (Over S) ⟶ Over.mk E.structureMap}
    (hX : X ^ N = 1) (u : (ZMod N)ˣ) : E.multiplesDivisor (X ^ (u : ZMod N).val) N = E.multiplesDivisor X N := by
  have hXu : (X ^ (u : ZMod N).val) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hX, one_pow]
  rw [multiplesDivisor_eq_zmod h1 hXu, multiplesDivisor_eq_zmod h1 hX]
  rw [← EllipticCurveGeom.pointsDivisor_comp_equiv (fun a : ZMod N ↦ X ^ a.val) (Units.mulLeft u)]
  congr 1
  funext a
  simp only [Function.comp_apply, Units.mulLeft_apply]
  rw [← pow_mul, pow_eq_pow_mod' hX, ZMod.val_mul]

end ModularFormsKB.Milne.CyclicN
