import Mathlib
import ModularFormsKB.Citation
/-!
# Milne, Chapter 2: discrete subgroups of `SL₂(ℝ)` acting on `ℍ`

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §2, pdf pp. 26–39.

* Definitions in running text: discontinuous action (footnote 6, D039), Fuchsian group (D041), elliptic point
  of a discrete subgroup (D047), fundamental domain (p. 32).
* Proposition 2.4 (both directions, for a general locally compact `G` acting on `X ≃ G/K`, `K` compact).
* Exercise 2.8 (c): commensurability and compactness of `Γ\ℍ`.
* Proposition 2.10: the stabilizer of an elliptic point is finite cyclic.
* Lemma 2.13: finitely many `(c, d)` with `|cz + d| ≤ N`.
* Proposition 2.16 (fundamental domain of a finite-index subgroup) and Proposition 2.17 (connected fundamental
  domain; the book omits the proof: a named statement here).
* Exercise 2.24: orbits of a normal subgroup of finite index on a transitive set.

`SL(2, ℝ)` acts on `ℍ` through Mathlib's action; `Γ\ℍ` is `MulAction.orbitRel.Quotient Γ ℍ`.
-/

open Matrix MatrixGroups UpperHalfPlane Filter Topology Pointwise Polynomial

namespace ModularFormsKB.Milne

/-! ### Definitions -/

/-- **Discontinuous action** (Milne, §2, footnote 6, p. 26): a continuous action of `Γ` on `X` is discontinuous if for
every `x : X` and every sequence `γ i` of distinct elements of `Γ`, the sequence `γ i • x` has no cluster point.
The book says "the set `{γ_i x}` has no cluster point"; we read it, as in Lee's *Introduction to Topological
Manifolds* (which the book cites), as a statement about the sequence. -/
@[kb "milne2017mf" "§2, footnote 6: discontinuous action, pdf p. 26"]
def IsDiscontinuousAction (Γ X : Type*) [Group Γ] [MulAction Γ X] [TopologicalSpace X] : Prop :=
  ∀ (x : X) (γ : ℕ → Γ), Function.Injective γ → ∀ y : X, ¬ MapClusterPt y atTop (fun i ↦ γ i • x)

/-- **Fuchsian group** (Milne, p. 28): a discrete subgroup of `PSL₂(ℝ)`. -/
@[kb "milne2017mf" "§2, definition of Fuchsian group, pdf p. 28"]
def IsFuchsianGroup (Γ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℝ)) : Prop :=
  DiscreteTopology Γ

/-- **Elliptic point** (Milne, p. 31): for a discrete subgroup `Γ` of `SL₂(ℝ)`, a point `z ∈ ℍ` is an elliptic point
if it is the fixed point of an elliptic element of `Γ`. Elliptic is Mathlib's `Matrix.IsElliptic` (negative
discriminant, i.e. `|tr γ| < 2` for `det γ = 1`), which is the book's trace criterion on p. 30; it excludes `±I`. -/
@[kb "milne2017mf" "§2, definition of elliptic point, pdf p. 31"]
def IsEllipticPoint (Γ : Subgroup SL(2, ℝ)) (z : ℍ) : Prop :=
  ∃ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) ℝ).IsElliptic ∧ γ • z = z

/-- The open-set notion of fundamental set used in Milne's Proposition 2.16 (p. 32 without connectedness, which
2.16 explicitly drops): `D` is open, no two points of `D` are `Γ`-equivalent, and every point of `ℍ` is
`Γ`-equivalent to a point of the closure of `D`. -/
@[kb "milne2017mf" "§2, definition of fundamental domain (without connectedness), pdf p. 32"]
def IsFundamentalSet (Γ : Subgroup SL(2, ℝ)) (D : Set ℍ) : Prop :=
  IsOpen D ∧ (∀ z ∈ D, ∀ w ∈ D, ∀ γ ∈ Γ, γ • z = w → z = w) ∧ ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ closure D

/-- **Fundamental domain** (Milne, p. 32): a connected open subset `D` of `ℍ` such that no two points of `D` are
equivalent under `Γ` and `ℍ = ⋃ γ D̄`. -/
@[kb "milne2017mf" "§2, definition of fundamental domain, pdf p. 32"]
def IsFundamentalDomain (Γ : Subgroup SL(2, ℝ)) (D : Set ℍ) : Prop :=
  IsConnected D ∧ IsFundamentalSet Γ D

/-! ### Proposition 2.4 -/

/-- **Milne, Proposition 2.4.** Let `G` be a locally compact group acting continuously on `X` such that the
stabilizer `K` of `x₀` is compact and `gK ↦ g x₀ : G/K → X` is a homeomorphism. For a subgroup `Γ` of `G` the
following are equivalent: (a) for all compact `A, B ⊆ X`, `{γ ∈ Γ | γA ∩ B ≠ ∅}` is finite; (b) `Γ` is discrete. -/
@[kb "milne2017mf" "Proposition 2.4, pdf p. 26"]
theorem finite_meets_iff_discreteTopology {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    (x₀ : X) (hK : IsCompact (MulAction.stabilizer G x₀ : Set G))
    (hX : ∃ e : G ⧸ MulAction.stabilizer G x₀ ≃ₜ X,
      ∀ g : G, e (g : G ⧸ MulAction.stabilizer G x₀) = g • x₀)
    (Γ : Subgroup G) :
    (∀ A B : Set X, IsCompact A → IsCompact B → {γ : Γ | ((γ : G) • A ∩ B).Nonempty}.Finite) ↔
      DiscreteTopology Γ := by
  obtain ⟨e, he⟩ := hX
  have hClosedK : IsClosed (MulAction.stabilizer G x₀ : Set G) := hK.isClosed
  have hmk : IsProperMap (QuotientGroup.mk : G → G ⧸ MulAction.stabilizer G x₀) := by
    rw [isProperMap_iff_isClosedMap_and_compact_fibers]
    refine ⟨QuotientGroup.continuous_mk, QuotientGroup.isClosedMap_coe hK, ?_⟩
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have : (QuotientGroup.mk : G → G ⧸ MulAction.stabilizer G x₀) ⁻¹' {(g : G ⧸ MulAction.stabilizer G x₀)}
        = (fun k => g * k) '' (MulAction.stabilizer G x₀ : Set G) := by
      ext g'
      simp only [Set.mem_preimage, Set.mem_singleton_iff, QuotientGroup.eq, Set.mem_image]
      constructor
      · intro h
        exact ⟨g⁻¹ * g', by simpa using (MulAction.stabilizer G x₀).inv_mem h, by group⟩
      · rintro ⟨k, hk, rfl⟩
        simpa using (MulAction.stabilizer G x₀).inv_mem hk
    rw [this]
    exact hK.image (continuous_const_mul g)
  have horb : IsProperMap (fun g : G => g • x₀) := by
    have : (fun g : G => g • x₀) = e ∘ (QuotientGroup.mk : G → G ⧸ MulAction.stabilizer G x₀) := by
      funext g; simp [he]
    rw [this]
    exact e.isProperMap.comp hmk
  have htrans : MulAction.IsPretransitive G X := by
    have hs : ∀ x : X, ∃ g : G, g • x₀ = x := by
      intro x
      obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e.symm x)
      exact ⟨g, by rw [← he, hg]; simp⟩
    refine ⟨fun x y => ?_⟩
    obtain ⟨g, rfl⟩ := hs x
    obtain ⟨h, rfl⟩ := hs y
    exact ⟨h * g⁻¹, by simp [mul_smul]⟩
  have hproper : ProperSMul G X := MulAction.properSMul_of_proper_orbitMap horb
  constructor
  · intro hfin
    obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds (1 : G)
    have hB : IsCompact ((fun g : G => g • x₀) '' V) := hVc.image (by fun_prop)
    have hS := hfin {x₀} _ isCompact_singleton hB
    set F : Set G := (Subtype.val '' {γ : Γ | ((γ : G) • ({x₀} : Set X) ∩ (fun g : G => g • x₀) '' V).Nonempty}) \ {1} with hF
    have hFfin : F.Finite := (hS.image _).sdiff
    have hU : IsOpen (interior V ∩ Fᶜ) := isOpen_interior.inter hFfin.isClosed.isOpen_compl
    have h1 : (1 : G) ∈ interior V ∩ Fᶜ := ⟨mem_interior_iff_mem_nhds.mpr hV, by simp [hF]⟩
    apply discreteTopology_of_isOpen_singleton_one
    have : ({1} : Set Γ) = Subtype.val ⁻¹' (interior V ∩ Fᶜ) := by
      ext γ
      simp only [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_inter_iff, Set.mem_compl_iff]
      constructor
      · rintro rfl; simpa using h1
      · rintro ⟨hv, hnF⟩
        by_contra hne
        apply hnF
        have hmem : γ ∈ {γ : Γ | ((γ : G) • ({x₀} : Set X) ∩ (fun g : G => g • x₀) '' V).Nonempty} :=
          ⟨(γ : G) • x₀, Set.smul_mem_smul_set rfl, (γ : G), interior_subset hv, rfl⟩
        refine ⟨⟨γ, hmem, rfl⟩, ?_⟩
        exact fun h => hne (Subtype.ext h)
    rw [this]
    exact hU.preimage continuous_subtype_val
  · intro hdisc
    intro A B hA hB
    have hcl : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discreteTopology
    have hemb : IsClosedEmbedding ((↑) : Γ → G) := hcl.isClosedEmbedding_subtypeVal
    have hT := ProperSMul.isCompact_setOfPred_inter_nonempty (G := G) hA hB
    exact (hemb.isCompact_preimage hT).finite_of_discrete

/-! ### Exercise 2.8 (c) -/

private theorem exists_compact_cover (Γ : Subgroup SL(2, ℝ))
    [CompactSpace (MulAction.orbitRel.Quotient Γ ℍ)] :
    ∃ C : Set ℍ, IsCompact C ∧ ∀ z : ℍ, ∃ γ ∈ Γ, ∃ c ∈ C, γ • c = z := by
  have hq := MulAction.isOpenQuotientMap_quotientMk (Γ := Γ) (T := ℍ)
  choose K hKc hKn using fun x : ℍ => exists_compact_mem_nhds x
  obtain ⟨t, ht⟩ := (isCompact_univ (X := MulAction.orbitRel.Quotient Γ ℍ)).elim_finite_subcover
    (fun x : ℍ => Quotient.mk (MulAction.orbitRel Γ ℍ) '' interior (K x))
    (fun x => hq.isOpenMap _ isOpen_interior)
    (by
      intro q _
      obtain ⟨z, rfl⟩ := Quotient.mk_surjective q
      exact Set.mem_iUnion.mpr ⟨z, z, mem_interior_iff_mem_nhds.mpr (hKn z), rfl⟩)
  refine ⟨⋃ x ∈ t, K x, t.isCompact_biUnion fun x _ => hKc x, ?_⟩
  intro z
  have := ht (Set.mem_univ (Quotient.mk (MulAction.orbitRel Γ ℍ) z))
  simp only [Set.mem_iUnion] at this
  obtain ⟨x, hx, c, hc, hcz⟩ := this
  have h3 : (MulAction.orbitRel Γ ℍ) c z := Quotient.exact hcz
  rw [MulAction.orbitRel_apply] at h3
  obtain ⟨γ, hγ⟩ := h3
  have hγ' : (γ : Γ) • z = c := hγ
  exact ⟨(γ⁻¹ : Γ), (γ⁻¹ : Γ).2, c, Set.mem_biUnion hx (interior_subset hc),
    (inv_smul_eq_iff.mpr hγ'.symm : (γ⁻¹ : Γ) • c = z)⟩

/-- **Milne, Exercise 2.8 (c).** If `Γ` and `Γ'` are commensurable subgroups of `SL₂(ℝ)` and `Γ\ℍ` is compact, then
so is `Γ'\ℍ`. -/
@[kb "milne2017mf" "Exercise 2.8 (c), pdf p. 29"]
theorem compactSpace_quotient_of_commensurable {Γ Γ' : Subgroup SL(2, ℝ)} (h : Γ.Commensurable Γ')
    [CompactSpace (MulAction.orbitRel.Quotient Γ ℍ)] :
    CompactSpace (MulAction.orbitRel.Quotient Γ' ℍ) := by
  obtain ⟨C, hC, hcov⟩ := exists_compact_cover Γ
  have hfi : (Γ'.subgroupOf Γ).FiniteIndex := ⟨h.2.relIndex_ne_zero⟩
  have : Finite (Γ ⧸ Γ'.subgroupOf Γ) := inferInstance
  let r : (Γ ⧸ Γ'.subgroupOf Γ) → Γ := fun q => Quotient.out q
  let C' : Set ℍ := ⋃ q, ((r q : SL(2, ℝ))⁻¹) • C
  have hC' : IsCompact C' := isCompact_iUnion fun q => by
    rw [← Set.image_smul]
    exact hC.image (continuous_const_smul _)
  have hsurj : Set.univ ⊆ Quotient.mk (MulAction.orbitRel Γ' ℍ) '' C' := by
    intro p _
    obtain ⟨z, rfl⟩ := Quotient.mk_surjective p
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov z
    set g : Γ := ⟨γ, hγ⟩ with hg
    set q : Γ ⧸ Γ'.subgroupOf Γ := (QuotientGroup.mk g⁻¹ : Γ ⧸ Γ'.subgroupOf Γ) with hqdef
    have hq : (r q)⁻¹ * g⁻¹ ∈ Γ'.subgroupOf Γ := by
      have : (QuotientGroup.mk (r q) : Γ ⧸ Γ'.subgroupOf Γ) = q := QuotientGroup.out_eq' q
      exact QuotientGroup.eq.mp this
    have hδ : (((r q)⁻¹ * g⁻¹ : Γ) : SL(2, ℝ)) ∈ Γ' := hq
    refine ⟨((r q : SL(2, ℝ))⁻¹) • c, Set.mem_iUnion.mpr ⟨q, Set.smul_mem_smul_set hc⟩, ?_⟩
    apply Quotient.sound
    change (MulAction.orbitRel Γ' ℍ) _ _
    rw [MulAction.orbitRel_apply]
    refine ⟨⟨(((r q)⁻¹ * g⁻¹ : Γ) : SL(2, ℝ)), hδ⟩, ?_⟩
    show (((r q)⁻¹ * g⁻¹ : Γ) : SL(2, ℝ)) • (γ • c) = ((r q : SL(2, ℝ))⁻¹) • c
    rw [← mul_smul]
    congr 1
    simp [hg, mul_assoc]
  exact ⟨by
    have := hC'.image (MulAction.isOpenQuotientMap_quotientMk (Γ := Γ') (T := ℍ)).continuous
    rwa [Set.eq_univ_of_univ_subset hsurj] at this⟩

/-! ### Proposition 2.10 -/

private theorem aux_scalar {g : SL(2, ℝ)} {z : ℍ} {e : ℝ}
    (hz : g • z = z)
    (hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ g) (z : ℂ) = (e : ℂ)) :
    (g : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.scalar (Fin 2) e := by
  have hdet : (0 : ℝ) < (Matrix.SpecialLinearGroup.mapGL ℝ g).det.val := by simp
  have hne : (e : ℂ) ≠ 0 := hd ▸ denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ g) z
  have hn : num (Matrix.SpecialLinearGroup.mapGL ℝ g) (z : ℂ) = (e : ℂ) * (z : ℂ) := by
    have h1 : ((Matrix.SpecialLinearGroup.mapGL ℝ g) • z : ℍ) = z := hz
    have h2 := coe_smul_of_det_pos hdet z
    rw [h1, hd, eq_div_iff hne] at h2
    rw [← h2]
    ring
  have hm : ∀ i j, ((Matrix.SpecialLinearGroup.map (RingHom.id ℝ) g : SL(2, ℝ)) i j) = g i j :=
    fun _ _ => rfl
  simp only [num, denom, Matrix.SpecialLinearGroup.mapGL_coe_matrix, hm,
    Algebra.algebraMap_self, Complex.ext_iff, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero] at hd hn
  have him : (z : ℂ).im ≠ 0 := z.im_ne_zero
  have h10 : g 1 0 = 0 := (mul_eq_zero.mp hd.2).resolve_right him
  have h00 : g 0 0 = e := mul_right_cancel₀ him hn.2
  have h11 : g 1 1 = e := by
    have h := hd.1
    rw [h10] at h
    linarith
  have h01 : g 0 1 = 0 := by
    have h := hn.1
    rw [h00] at h
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h00, h01, h10, h11]

/-- **Milne, Proposition 2.10.** If `z` is an elliptic point of a discrete subgroup `Γ` of `SL₂(ℝ)`, then
`{γ ∈ Γ | γ z = z}` is a finite cyclic group. -/
@[kb "milne2017mf" "Proposition 2.10, pdf p. 31"]
theorem finite_and_isCyclic_stabilizer {Γ : Subgroup SL(2, ℝ)} [DiscreteTopology Γ] {z : ℍ}
    (hz : IsEllipticPoint Γ z) :
    Finite (MulAction.stabilizer Γ z) ∧ IsCyclic (MulAction.stabilizer Γ z) := by
  have hfin : Finite (MulAction.stabilizer Γ z) := by
    have hcl : IsClosed (Γ : Set SL(2, ℝ)) := Subgroup.isClosed_of_discreteTopology
    have : Topology.IsClosedEmbedding ((↑) : Γ → SL(2, ℝ)) := hcl.isClosedEmbedding_subtypeVal
    have : ProperSMul Γ ℍ := inferInstance
    have hK : IsCompact ((fun p : Γ × ℍ => (p.1 • p.2, p.2)) ⁻¹' {(z, z)}) :=
      (ProperSMul.isProperMap_smul_pair (G := Γ) (X := ℍ)).isCompact_preimage isCompact_singleton
    have hK2 := hK.image continuous_fst
    have hfin := hK2.finite_of_discrete
    refine (hfin.subset ?_).to_subtype
    intro g hg
    exact ⟨(g, z), by simpa using hg, rfl⟩
  refine ⟨hfin, ?_⟩
  let φ : (MulAction.stabilizer Γ z) →* ℂ :=
    { toFun := fun g => denom (Matrix.SpecialLinearGroup.mapGL ℝ ((g : Γ) : SL(2, ℝ))) (z : ℂ)
      map_one' := by simp
      map_mul' := fun a b => by
        have h := denom_cocycle' (Matrix.SpecialLinearGroup.mapGL ℝ ((a : Γ) : SL(2, ℝ)))
          (Matrix.SpecialLinearGroup.mapGL ℝ ((b : Γ) : SL(2, ℝ))) z
        have hb : smulAux (Matrix.SpecialLinearGroup.mapGL ℝ ((b : Γ) : SL(2, ℝ))) z = z := b.2
        have hσ : ∀ w, σ (Matrix.SpecialLinearGroup.mapGL ℝ ((b : Γ) : SL(2, ℝ))) w = w := by
          intro w; simp [σ]
        rw [hb, hσ] at h
        simpa using h }
  refine isCyclic_of_injective_ringHom φ ?_
  rw [injective_iff_map_eq_one]
  intro g hg
  have hg' : denom (Matrix.SpecialLinearGroup.mapGL ℝ ((g : Γ) : SL(2, ℝ))) (z : ℂ)
      = ((1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_one]; exact hg
  have hsc := aux_scalar (g.2 : ((g : Γ) : SL(2, ℝ)) • z = z) hg'
  refine Subtype.ext (Subtype.ext (Subtype.ext ?_))
  simpa using hsc

/-! ### Lemma 2.13 -/

/-- **Milne, Lemma 2.13.** For fixed `z ∈ ℍ` and `N`, only finitely many pairs of integers `(c, d)` satisfy
`|cz + d| ≤ N`. (The book takes `N ∈ ℕ`; any real `N` is allowed here.) -/
@[kb "milne2017mf" "Lemma 2.13, pdf p. 33"]
theorem finite_setOf_norm_mul_add_le (z : ℍ) (N : ℝ) :
    {p : ℤ × ℤ | ‖(p.1 : ℂ) * (z : ℂ) + p.2‖ ≤ N}.Finite := by
  have hy : 0 < (z : ℂ).im := z.im_pos
  set y := (z : ℂ).im
  set x := (z : ℂ).re
  apply ((Set.finite_Icc (-⌈N / y⌉ : ℤ) ⌈N / y⌉).prod
    (Set.finite_Icc (-⌈N + (N / y) * |x|⌉ : ℤ) ⌈N + (N / y) * |x|⌉)).subset
  rintro ⟨c, d⟩ h
  simp only [Set.mem_setOf_eq] at h
  have h1 : |(c : ℝ) * y| ≤ N := by
    refine le_trans ?_ h
    have := Complex.abs_im_le_norm ((c : ℂ) * (z : ℂ) + d)
    simpa [y] using this
  have h2 : |(c : ℝ) * x + d| ≤ N := by
    refine le_trans ?_ h
    have := Complex.abs_re_le_norm ((c : ℂ) * (z : ℂ) + d)
    simpa [x] using this
  have hc : |(c : ℝ)| ≤ N / y := by
    rw [le_div_iff₀ hy]; rwa [abs_mul, abs_of_pos hy] at h1
  have hd : |(d : ℝ)| ≤ N + (N / y) * |x| := by
    have : |(d : ℝ)| ≤ |(c : ℝ) * x + d| + |(c : ℝ) * x| := by
      have := abs_sub (((c : ℝ) * x + d)) ((c : ℝ) * x)
      simpa using this
    rw [abs_mul] at this
    nlinarith [abs_nonneg x, mul_le_mul_of_nonneg_right hc (abs_nonneg x)]
  have hc' := (abs_le.mp hc)
  have hd' := (abs_le.mp hd)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : (-(⌈N / y⌉ : ℤ) : ℝ) ≤ c := by linarith [hc'.1, Int.le_ceil (N / y)]
    exact_mod_cast this
  · have : (c : ℝ) ≤ ⌈N / y⌉ := by linarith [Int.le_ceil (N / y), hc'.2]
    exact_mod_cast this
  · have : (-(⌈N + (N / y) * |x|⌉ : ℤ) : ℝ) ≤ d := by
      linarith [hd'.1, Int.le_ceil (N + (N / y) * |x|)]
    exact_mod_cast this
  · have : (d : ℝ) ≤ ⌈N + (N / y) * |x|⌉ := by linarith [Int.le_ceil (N + (N / y) * |x|), hd'.2]
    exact_mod_cast this

/-! ### Propositions 2.16 and 2.17 -/

private theorem aux_infinite (V : Set ℂ) (hV : IsOpen V) (h : V.Nonempty) : V.Infinite := by
  intro hf
  obtain ⟨x, hx⟩ := h
  have h1 : (V \ {x}).Finite := hf.subset Set.sdiff_subset
  have hW : (V \ {x})ᶜ ∈ 𝓝 x := h1.isClosed.compl_mem_nhds (by simp)
  have hV' : V ∈ 𝓝 x := hV.mem_nhds hx
  have hA : (V ∩ (V \ {x})ᶜ) ∩ {x}ᶜ ∈ 𝓝[≠] x :=
    Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (Filter.inter_mem hV' hW)) self_mem_nhdsWithin
  obtain ⟨y, hy1, hy2⟩ := (Filter.nonempty_of_mem hA)
  exact hy1.2 ⟨hy1.1, hy2⟩

private theorem aux_fixed_open (g : SL(2, ℝ)) (U : Set ℍ) (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ w ∈ U, g • w = w) : g = 1 ∨ g = -1 := by
  have key : ∀ w ∈ U, (g 1 0 : ℂ) * (w : ℂ) ^ 2 + ((g 1 1 : ℂ) - g 0 0) * (w : ℂ) - g 0 1 = 0 := by
    intro w hw
    have h1 := congrArg (fun x : ℍ => (x : ℂ)) (h w hw)
    simp only [coe_specialLinearGroup_apply, Algebra.algebraMap_self, RingHom.id_apply] at h1
    have hden : (g 1 0 : ℂ) * (w : ℂ) + g 1 1 ≠ 0 := by
      have := denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ g) w
      simpa [UpperHalfPlane.denom] using this
    rw [div_eq_iff hden] at h1
    linear_combination -h1
  set P : ℂ[X] := C (g 1 0 : ℂ) * X ^ 2 + C ((g 1 1 : ℂ) - g 0 0) * X - C (g 0 1 : ℂ) with hP
  have hP0 : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinf := aux_infinite _ (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ hU)
      (hne.image _)
    refine hinf.mono ?_
    rintro _ ⟨w, hw, rfl⟩
    have := key w hw
    simpa [hP, Polynomial.IsRoot] using this
  have c2 := congrArg (fun p => p.coeff 2) hP0
  have c1 := congrArg (fun p => p.coeff 1) hP0
  have c0 := congrArg (fun p => p.coeff 0) hP0
  simp [hP, Polynomial.coeff_X, Polynomial.coeff_C] at c2 c1 c0
  have hc : g 1 0 = 0 := by exact_mod_cast c2
  have hb : g 0 1 = 0 := by exact_mod_cast c0
  have hda : g 1 1 = g 0 0 := by
    have : (g 1 1 : ℂ) = g 0 0 := by linear_combination c1
    exact_mod_cast this
  have hdet := g.det_coe
  rw [Matrix.det_fin_two, hc, hb, hda] at hdet
  have ha : g 0 0 = 1 ∨ g 0 0 = -1 := by
    have : (g 0 0 - 1) * (g 0 0 + 1) = 0 := by linarith [hdet]
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  rcases ha with ha | ha
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hda]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hda]

private theorem neg_smul' (g : SL(2, ℝ)) (z : ℍ) : (-g) • z = g • z := by
  ext
  simp only [coe_specialLinearGroup_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Complex.ofReal_neg]
  rw [← neg_div_neg_eq]
  congr 1 <;> ring

/-- **Milne, Proposition 2.16.** Let `Γ` be a discrete subgroup of `SL₂(ℝ)` with fundamental domain `D`, and let
`γ₁, …, γₘ ∈ Γ` be representatives of the cosets of the image of `Γ'` in `Γ/{±I}`, i.e. every `γ ∈ Γ` is
`± γ' γᵢ` with `γ' ∈ Γ'` for exactly one `i`. Then `D' = ⋃ γᵢ D` is a (possibly disconnected) fundamental domain
for `Γ'`. -/
@[kb "milne2017mf" "Proposition 2.16, pdf p. 34"]
theorem isFundamentalSet_iUnion {Γ Γ' : Subgroup SL(2, ℝ)} [DiscreteTopology Γ] (hΓ' : Γ' ≤ Γ) {D : Set ℍ}
    (hD : IsFundamentalDomain Γ D) {m : ℕ} (γs : Fin m → SL(2, ℝ)) (hγs : ∀ i, γs i ∈ Γ)
    (hcos : ∀ γ ∈ Γ, ∃! i : Fin m, ∃ γ' ∈ Γ', γ = γ' * γs i ∨ γ = -(γ' * γs i)) :
    IsFundamentalSet Γ' (⋃ i, γs i • D) := by
  obtain ⟨-, hDopen, hDinj, hDcov⟩ := hD
  have stab : ∀ u ∈ D, ∀ γ ∈ Γ, γ • u = u → γ = 1 ∨ γ = -1 := by
    intro u hu γ hγ hfix
    refine aux_fixed_open γ (D ∩ (fun x => γ • x) ⁻¹' D)
      (hDopen.inter (hDopen.preimage (continuous_const_smul γ))) ⟨u, hu, by simpa [hfix] using hu⟩ ?_
    intro w hw
    exact (hDinj w hw.1 (γ • w) hw.2 γ hγ rfl).symm
  refine ⟨isOpen_iUnion fun i => hDopen.smul (γs i), ?_, ?_⟩
  · intro z hz w hw γ' hγ' hzw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hw
    obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hi
    obtain ⟨v, hv, rfl⟩ := Set.mem_smul_set.mp hj
    have hδ : (γs j)⁻¹ * γ' * γs i ∈ Γ :=
      Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (hγs j)) (hΓ' hγ')) (hγs i)
    have hδu : ((γs j)⁻¹ * γ' * γs i) • u = v := by
      rw [mul_smul, mul_smul, hzw, inv_smul_smul]
    have huv : u = v := hDinj u hu v hv _ hδ hδu
    subst huv
    have hfix := stab u hu _ hδ hδu
    have hij : i = j := by
      have heq : γ' * γs i = γs j * ((γs j)⁻¹ * γ' * γs i) := by group
      obtain ⟨k, -, hk⟩ := hcos (γs i) (hγs i)
      have h1 : i = k := hk i ⟨1, Γ'.one_mem, Or.inl (by simp)⟩
      have h2 : j = k := by
        refine hk j ⟨γ'⁻¹, Γ'.inv_mem hγ', ?_⟩
        rcases hfix with h | h
        · left
          rw [h, mul_one] at heq
          rw [← heq]; group
        · right
          rw [h, mul_neg, mul_one] at heq
          have : γs i = γ'⁻¹ * -(γs j) := by
            rw [← heq]; group
          rw [this, mul_neg]
      rw [h1, h2]
    subst hij
    rfl
  · intro z
    obtain ⟨γ, hγ, hz⟩ := hDcov z
    obtain ⟨i, ⟨γ'', hγ'', hrep⟩, -⟩ := hcos γ⁻¹ (Γ.inv_mem hγ)
    refine ⟨γ''⁻¹, Γ'.inv_mem hγ'', ?_⟩
    have hz' : γ''⁻¹ • z = γs i • (γ • z) := by
      have hzz : z = γ⁻¹ • (γ • z) := by simp
      have : γ''⁻¹ • z = γ''⁻¹ • (γ⁻¹ • (γ • z)) := by rw [← hzz]
      rw [this]
      rcases hrep with h | h
      · rw [h, ← mul_smul]; congr 1; group
      · rw [h, neg_smul', ← mul_smul]; congr 1; group
    rw [hz']
    have hm : γs i • (γ • z) ∈ closure (⋃ j, γs j • D) :=
      map_mem_closure (continuous_const_smul (γs i)) hz fun u hu =>
        Set.mem_iUnion.mpr ⟨i, Set.smul_mem_smul_set hu⟩
    exact hm

/-- **Milne, Proposition 2.17** (proof omitted in the book): in the situation of Proposition 2.16 the
representatives `γᵢ` can be chosen so that the closure of `D' = ⋃ γᵢ D` is connected; the interior of that closure is
then a connected fundamental domain for `Γ'`. Recorded as a named statement. -/
@[kb "milne2017mf" "Proposition 2.17, pdf p. 35"]
structure ConnectedFundamentalDomainStatement : Prop where
  out : ∀ {Γ Γ' : Subgroup SL(2, ℝ)} [DiscreteTopology Γ], Γ' ≤ Γ → ∀ {D : Set ℍ}, IsFundamentalDomain Γ D →
    ∀ {m : ℕ}, (∃ γs : Fin m → SL(2, ℝ), (∀ i, γs i ∈ Γ) ∧
      ∀ γ ∈ Γ, ∃! i : Fin m, ∃ γ' ∈ Γ', γ = γ' * γs i ∨ γ = -(γ' * γs i)) →
    ∃ γs : Fin m → SL(2, ℝ), (∀ i, γs i ∈ Γ) ∧
      (∀ γ ∈ Γ, ∃! i : Fin m, ∃ γ' ∈ Γ', γ = γ' * γs i ∨ γ = -(γ' * γs i)) ∧
      IsConnected (closure (⋃ i, γs i • D)) ∧
      IsFundamentalDomain Γ' (interior (closure (⋃ i, γs i • D)))

/-! ### Exercise 2.24 -/

/-- **Milne, Exercise 2.24.** Let `G` act transitively on `X`, let `H` be a normal subgroup of finite index, `G₀` the
stabilizer of `x₀` and `H₀ = H ∩ G₀`. Then the number of `H`-orbits on `X` is `(G : H) / (G₀ : H₀)`; stated here
multiplied out. -/
@[kb "milne2017mf" "Exercise 2.24, pdf p. 39"]
theorem card_orbits_mul_relIndex_eq_index {G X : Type*} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] (H : Subgroup G) [H.Normal] [H.FiniteIndex] (x₀ : X) :
    Nat.card (MulAction.orbitRel.Quotient H X) * H.relIndex (MulAction.stabilizer G x₀) = H.index := by
  set G₀ := MulAction.stabilizer G x₀
  choose g hg using fun x : X => MulAction.exists_smul_eq G x₀ x
  let f : X → G ⧸ (H ⊔ G₀) := fun x => (g x : G ⧸ (H ⊔ G₀))
  have hrel : ∀ x y : X, (MulAction.orbitRel H X) x y ↔ f x = f y := by
    intro x y
    rw [MulAction.orbitRel_apply]
    simp only [f, QuotientGroup.eq]
    constructor
    · rintro ⟨h, hh⟩
      have hh' : (h : G) • y = x := hh
      have hs : (g x)⁻¹ * (h : G) * g y ∈ G₀ := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hg y, hh', inv_smul_eq_iff, hg x]
      have : (g x)⁻¹ * g y = ((g x)⁻¹ * (h : G)⁻¹ * g x) * ((g x)⁻¹ * h * g y) := by group
      rw [this]
      refine Subgroup.mul_mem_sup ?_ hs
      have := (inferInstance : H.Normal).conj_mem (h : G)⁻¹ (H.inv_mem h.2) (g x)⁻¹
      simpa [mul_assoc] using this
    · intro hmem
      obtain ⟨h, hh, s, hs, hhs⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
      have hy : g y = g x * h * s := by rw [mul_assoc, hhs]; group
      have hs' : s • x₀ = x₀ := hs
      have hyy : y = g x • h • x₀ := by
        rw [← hg y, hy, mul_smul, mul_smul, hs']
      refine ⟨⟨g x * h⁻¹ * (g x)⁻¹, ?_⟩, ?_⟩
      · have := (inferInstance : H.Normal).conj_mem h⁻¹ (H.inv_mem hh) (g x)
        simpa [mul_assoc] using this
      · show (g x * h⁻¹ * (g x)⁻¹) • y = x
        rw [hyy, ← mul_smul, ← mul_smul, mul_assoc (g x * h⁻¹ * (g x)⁻¹) (g x) h]
        have : g x * h⁻¹ * (g x)⁻¹ * (g x * h) = g x := by group
        rw [this, hg]
  have hbij : Function.Bijective (Quotient.lift f (fun x y h => (hrel x y).mp h) :
      MulAction.orbitRel.Quotient H X → G ⧸ (H ⊔ G₀)) := by
    constructor
    · intro a b
      induction a using Quotient.inductionOn
      induction b using Quotient.inductionOn
      intro h
      exact Quotient.sound ((hrel _ _).mpr h)
    · intro q
      induction q using Quotient.inductionOn with
      | _ a =>
        refine ⟨Quotient.mk _ (a • x₀), ?_⟩
        show f (a • x₀) = _
        simp only [f, QuotientGroup.eq]
        apply Subgroup.mem_sup_right
        show ((g (a • x₀))⁻¹ * a) • x₀ = x₀
        rw [mul_smul, inv_smul_eq_iff, hg]
  have e : H.relIndex (H ⊔ G₀) = H.relIndex G₀ := by rw [Subgroup.relIndex_sup_left]
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), ← Subgroup.index_eq_card, mul_comm, ← e]
  exact Subgroup.relIndex_mul_index le_sup_left

end ModularFormsKB.Milne
