import ModularFormsKB.Milne.Wave9.HomDescent
import ModularFormsKB.Milne.Wave8.ClassGroupActionField
import ModularFormsKB.Milne.Ch12.AutComplex
import ModularFormsKB.Milne.Ch12.VariableChangeEnd
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ

/-!
# Milne wave 9: Proposition 12.21 (corrected form) over every algebraically closed field embeddable in `ℂ`

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, Proposition 12.21,
pdf p. 126 (proof omitted in the book).

Wave 8 proved the corrected named statement `ClassGroupActionPrincipalNormalized` over `ℂ` and every field isomorphic
to `ℂ`. Here it is descended along an embedding `τ : F → ℂ` of an algebraically closed field `F` of characteristic
zero (the Lefschetz principle in the form Milne uses it):

* base change identifies `End_F(E)` with `End_ℂ(E ⊗ ℂ)` (`endMapRingEquiv`, from the rigidity of
  `Wave9/HomDescent.lean`), so `E` has complex multiplication by `R` over `F` exactly when `E ⊗ ℂ` does;
* `Ell_F(R) → Ell_ℂ(R)`, `j ↦ τ(j)`, is a bijection (`ellCMOverEquiv`): a `j`-invariant with complex multiplication
  is algebraic (it has finitely many conjugates under `Aut(ℂ)`, Theorem 12.8), hence lies in `τ(F)`;
* the kernel of an `𝔞`-isogeny is torsion, and torsion points are defined over `F`, so kernels on points over `F`
  and over `ℂ` determine each other (`pointMap_eq_zero_iff_baseChange`).

Every algebraically closed field of characteristic zero of cardinality at most that of `ℂ` embeds in `ℂ`
(`nonempty_ringHom_complex`: it lies in an algebraically closed field of the cardinality of `ℂ`, isomorphic to `ℂ` by
Steinitz). This covers `ℚ̄` and all countable fields, the case left open by wave 8 (LE-MF-0210).
-/

open NumberField TauCeti TauCeti.Isogeny TauCeti.GlobalNumberFields WeierstrassCurve.Affine Cardinal
open scoped WeierstrassCurve

namespace ModularFormsKB.Milne.Wave9

section Descent

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [IsAlgClosed F] [CharZero F] [IsAlgClosed L]
  [DecidableEq F] [DecidableEq L]

/-- **Base change is an isomorphism of endomorphism rings** for `F ⊆ L` algebraically closed of characteristic
zero. -/
noncomputable def endMapRingEquiv (W : WeierstrassCurve F) [W.IsElliptic] :
    Hom W.toAffine W.toAffine ≃+* Hom (W⁄L).toAffine (W⁄L).toAffine :=
  RingEquiv.ofBijective (Hom.mapRingHom (W₁ := W.toAffine) (algebraMap F L)) (hom_map_bijective W W)

theorem endMapRingEquiv_apply (W : WeierstrassCurve F) [W.IsElliptic] (f : Hom W.toAffine W.toAffine) :
    (endMapRingEquiv W f : Hom (W⁄L).toAffine (W⁄L).toAffine) = f.map (algebraMap F L) :=
  rfl

variable {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K}

/-- Complex multiplication by `O` is invariant under algebraically closed base change. -/
theorem hasCMBy_baseChange_iff (W : WeierstrassCurve F) [W.IsElliptic] :
    HasCMBy (W⁄L) O ↔ HasCMBy W O := by
  constructor
  · rintro ⟨h1, h2, ⟨e⟩⟩
    exact ⟨h1, h2, ⟨e.trans (endMapRingEquiv (L := L) W).symm⟩⟩
  · rintro ⟨h1, h2, ⟨e⟩⟩
    exact ⟨h1, h2, ⟨e.trans (endMapRingEquiv W)⟩⟩

/-- `Ell_F(R)` maps into `Ell_L(R)`. -/
theorem algebraMap_mem_ellCMOver {x : F} (hx : x ∈ EllCMOver F O) : algebraMap F L x ∈ EllCMOver L O := by
  obtain ⟨W, hW, hcm, rfl⟩ := hx
  exact ⟨W⁄L, inferInstance, (hasCMBy_baseChange_iff W).mpr hcm, WeierstrassCurve.map_j W _⟩

/-- A point of `W ⊗ L` killed by a nonzero morphism is defined over `F`. -/
theorem exists_mapAlong_eq_of_pointMap_eq_zero {W V : WeierstrassCurve F} [W.IsElliptic] [V.IsElliptic]
    {g : Hom W.toAffine V.toAffine} (hg : g ≠ 0) {Q : (W⁄L).toAffine.Point}
    (hQ : (g.map (algebraMap F L)).pointMap Q = 0) :
    ∃ P : W.toAffine.Point, P.mapAlong (algebraMap F L) (algebraMap F L).injective = Q := by
  have hgL : g.map (algebraMap F L) ≠ 0 := by rwa [Ne, Hom.map_eq_zero_iff]
  set H := (g.map (algebraMap F L)).pointMapHom.ker
  have hfin : (SetLike.coe H).Finite := by
    refine (Hom.finite_setOf_pointMap_eq hgL 0).subset fun P hP ↦ ?_
    exact (Hom.mem_ker_pointMapHom_iff _ P).mp hP
  have : Finite H := hfin.to_subtype
  have hQH : Q ∈ H := (Hom.mem_ker_pointMapHom_iff _ Q).mpr hQ
  have hord := isOfFinAddOrder_of_finite (⟨Q, hQH⟩ : H)
  have hpos : 0 < addOrderOf Q := by
    have h := hord.addOrderOf_pos
    rwa [← AddSubgroup.addOrderOf_coe] at h
  refine exists_mapAlong_eq_of_zsmul_eq_zero W (n := (addOrderOf Q : ℤ)) (by exact_mod_cast hpos.ne') ?_
  rw [natCast_zsmul, addOrderOf_nsmul_eq_zero]

/-- **Kernels on points under algebraically closed base change**: for `J ≠ 0`, the kernel condition of an
`𝔞`-isogeny on the points over `F` gives it on the points over `L`. -/
theorem pointMap_eq_zero_iff_baseChange {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
    (i : O.toSubalgebra ≃+* Hom W.toAffine W.toAffine) (J : Ideal O.toSubalgebra) (hJ : J ≠ ⊥)
    (φ : Hom W.toAffine W'.toAffine)
    (h : ∀ P : W.toAffine.Point, φ.pointMap P = 0 ↔ ∀ a ∈ J, (i a).pointMap P = 0)
    (Q : (W⁄L).toAffine.Point) :
    (φ.map (algebraMap F L)).pointMap Q = 0 ↔
      ∀ a ∈ J, ((i a).map (algebraMap F L)).pointMap Q = 0 := by
  obtain ⟨a₀, ha₀, ha₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hi₀ : i a₀ ≠ 0 := by
    rw [Ne, ← map_zero i]
    exact fun h0 ↦ ha₀0 (i.injective h0)
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    apply hi₀
    refine Hom.ext_pointMap fun P ↦ ?_
    rw [Hom.zero_pointMap]
    exact (h P).mp (Hom.zero_pointMap P) a₀ ha₀
  have key : ∀ {V : WeierstrassCurve F} [V.IsElliptic] (g : Hom W.toAffine V.toAffine) (P : W.toAffine.Point),
      (g.map (algebraMap F L)).pointMap (P.mapAlong (algebraMap F L) (algebraMap F L).injective) = 0 ↔
        g.pointMap P = 0 := by
    intro V _ g P
    rw [Hom.pointMap_map, ← Point.mapAlong_zero (algebraMap F L) (algebraMap F L).injective,
      (Point.mapAlong_injective (algebraMap F L) (algebraMap F L).injective).eq_iff]
  constructor
  · intro hQ
    obtain ⟨P, rfl⟩ := exists_mapAlong_eq_of_pointMap_eq_zero hφ0 hQ
    intro a ha
    exact (key (i a) P).mpr ((h P).mp ((key φ P).mp hQ) a ha)
  · intro hQ
    obtain ⟨P, rfl⟩ := exists_mapAlong_eq_of_pointMap_eq_zero hi₀ (hQ a₀ ha₀)
    exact (key φ P).mpr ((h P).mpr fun a ha ↦ (key (i a) P).mp (hQ a ha))

end Descent

section Complex

variable {F : Type*} [Field F] [IsAlgClosed F] [CharZero F] [Algebra F ℂ]
variable {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K}

/-- **`Ell_ℂ(R)` comes from `F`**: every `j`-invariant of a complex curve with complex multiplication by `O` is the
image of an element of `Ell_F(R)` (it is algebraic, Theorem 12.8, and `F` is algebraically closed). -/
theorem exists_algebraMap_eq_of_mem_ellCMOver (hK : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) {y : ℂ}
    (hy : y ∈ EllCMOver ℂ O) : ∃ x ∈ EllCMOver F O, algebraMap F ℂ x = y := by
  classical
  have := hTC
  have hfin : Finite (EllCM O) := by
    obtain ⟨ι⟩ : Nonempty (K →+* ℂ) := inferInstance
    obtain ⟨φ, -⟩ := exists_equiv_pic_ellCM ι O Wave5.complexUniformization hK
    exact Finite.of_equiv _ φ
  have halg : IsAlgebraic ℚ y :=
    isAlgebraic_of_finite_range_ringEquiv y
      ((Set.toFinite (EllCM O)).subset (by rintro _ ⟨σ, rfl⟩; exact j_map_mem_ellCM σ hy))
  have halgF : IsAlgebraic F y := halg.tower_top F
  obtain ⟨x, hx⟩ := minpoly.mem_range_of_degree_eq_one F y
    (IsAlgClosed.degree_eq_one_of_irreducible F (minpoly.irreducible halgF.isIntegral))
  refine ⟨x, ?_, hx⟩
  obtain ⟨W'', hW'', hcm, rfl⟩ := hy
  let W₀ : WeierstrassCurve F := WeierstrassCurve.ofJ x
  have hj : (W₀⁄ℂ).j = W''.j :=
    (WeierstrassCurve.map_j W₀ (algebraMap F ℂ)).trans (by rw [WeierstrassCurve.ofJ_j]; exact hx)
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq W'' (W₀⁄ℂ) hj.symm
  obtain ⟨h1, h2, ⟨e⟩⟩ := hcm
  have hcm₀ : HasCMBy (W₀⁄ℂ) O := ⟨h1, h2, ⟨e.trans (endRingEquivOfVariableChange hC)⟩⟩
  exact ⟨W₀, inferInstance, (hasCMBy_baseChange_iff W₀).mp hcm₀, WeierstrassCurve.ofJ_j x⟩

/-- **`Ell_F(R) ≅ Ell_ℂ(R)`**, `j ↦ τ(j)`, for an algebraically closed field `F` of characteristic zero embedded in
`ℂ`. -/
noncomputable def ellCMOverEquiv (hK : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) :
    EllCMOver F O ≃ EllCMOver ℂ O :=
  haveI := Classical.decEq F
  Equiv.ofBijective (fun x ↦ ⟨algebraMap F ℂ (x : F), algebraMap_mem_ellCMOver x.2⟩)
    ⟨fun x y hxy ↦ Subtype.ext ((algebraMap F ℂ).injective (congrArg Subtype.val hxy)),
      fun y ↦ by
        obtain ⟨x, hx, hxy⟩ := exists_algebraMap_eq_of_mem_ellCMOver (F := F) hK hTC y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

theorem ellCMOverEquiv_apply (hK : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) (x : EllCMOver F O) :
    (ellCMOverEquiv hK hTC x : ℂ) = algebraMap F ℂ (x : F) :=
  rfl

end Complex

open scoped Classical in
/-- **Proposition 12.21, corrected, over an algebraically closed field embedded in `ℂ`**, with the kernel of an
`𝔞`-isogeny read on the points over `F`. -/
theorem exists_act_of_ringHom (F : Type) [Field F] [IsAlgClosed F] [CharZero F]
    (τ : F →+* ℂ) (K : Type) [Field K] [NumberField K] (O : NumberFieldOrder K) (hK : Module.finrank ℚ K = 2)
    (hTC : IsTotallyComplex K) (ι : K →+* F) :
    ∃ act : Pic O → EllCMOver F O → EllCMOver F O,
      (∀ (W W' : WeierstrassCurve.Affine F) [W.IsElliptic] [W'.IsElliptic] (i : O.toSubalgebra ≃+* Hom W W),
          IsNormalizedCM ι i →
          ∀ (I : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ) (J : Ideal O.toSubalgebra),
          ((J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) = I) →
          (hW : W.j ∈ EllCMOver F O) → (hW' : W'.j ∈ EllCMOver F O) → (φ : Hom W W') →
          (∀ P : W.Point, φ.pointMap P = 0 ↔ ∀ a ∈ J, (i a).pointMap P = 0) →
            act (ClassGroup.mk (K := K) I) ⟨W.j, hW⟩ = ⟨W'.j, hW'⟩) ∧
      ∀ x₀, Function.Bijective fun c ↦ act c x₀ := by
  classical
  let _ : Algebra F ℂ := τ.toAlgebra
  obtain ⟨actC, hC, hbij⟩ := Wave8.exists_act_complex K O hK hTC ((algebraMap F ℂ).comp ι)
  set e := ellCMOverEquiv (F := F) (O := O) hK hTC
  refine ⟨fun c x ↦ e.symm (actC c (e x)), ?_, fun x₀ ↦ e.symm.bijective.comp (hbij (e x₀))⟩
  intro W W' _ _ i hi I J hJI hW hW' φ hφ
  have hJ : J ≠ ⊥ := by
    rintro rfl
    apply I.ne_zero
    rw [← hJI]
    simp
  have hnorm : IsNormalizedCM ((algebraMap F ℂ).comp ι) (i.trans (endMapRingEquiv W)) := fun a ↦
    Wave8.hom_map_pullbackDifferential (i a) (algebraMap F ℂ) (hi a)
  have hWC : (W⁄ℂ).j ∈ EllCMOver ℂ O := by
    convert algebraMap_mem_ellCMOver (L := ℂ) hW using 1; exact WeierstrassCurve.map_j W _
  have hWC' : (W'⁄ℂ).j ∈ EllCMOver ℂ O := by
    convert algebraMap_mem_ellCMOver (L := ℂ) hW' using 1; exact WeierstrassCurve.map_j W' _
  have h := hC (W⁄ℂ) (W'⁄ℂ) (i.trans (endMapRingEquiv W)) hnorm I J hJI hWC hWC' (φ.map (algebraMap F ℂ))
    (pointMap_eq_zero_iff_baseChange i J hJ φ hφ)
  have e1 : e ⟨W.j, hW⟩ = ⟨(W⁄ℂ).j, hWC⟩ := Subtype.ext (WeierstrassCurve.map_j W (algebraMap F ℂ)).symm
  simp only
  rw [e1, h, Equiv.symm_apply_eq]
  exact Subtype.ext (WeierstrassCurve.map_j W' (algebraMap F ℂ))

/-- **Proposition 12.21, corrected, over an algebraically closed field embedded in `ℂ`**: the body of the named
statement `ClassGroupActionPrincipalNormalized` for an algebraically closed field `F` of characteristic zero with a
field embedding `τ : F → ℂ`. -/
theorem classGroupActionPrincipalNormalized_of_ringHom (F : Type) [Field F] [IsAlgClosed F] [CharZero F]
    (τ : F →+* ℂ) (K : Type) [Field K] [NumberField K] (O : NumberFieldOrder K) (hK : Module.finrank ℚ K = 2)
    (hTC : IsTotallyComplex K) (ι : K →+* F) :
    ∃ act : Pic O → EllCMOver F O → EllCMOver F O,
      (∀ (W W' : WeierstrassCurve.Affine F) [W.IsElliptic] [W'.IsElliptic] (i : O.toSubalgebra ≃+* Hom W W),
          IsNormalizedCM ι i →
          ∀ (I : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ) (J : Ideal O.toSubalgebra),
          ((J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) = I) →
          (hW : W.j ∈ EllCMOver F O) → (hW' : W'.j ∈ EllCMOver F O) → (φ : Hom W W') → IsAIsogeny i J φ →
            act (ClassGroup.mk (K := K) I) ⟨W.j, hW⟩ = ⟨W'.j, hW'⟩) ∧
      ∀ x₀, Function.Bijective fun c ↦ act c x₀ := by
  obtain ⟨act, hact, hbij⟩ := exists_act_of_ringHom F τ K O hK hTC ι
  exact ⟨act, fun W W' _ _ i hi I J hJI hW hW' φ hφ ↦
    hact W W' i hi I J hJI hW hW' φ (Wave8.pointMap_eq_zero_iff_of_isAIsogeny O i J φ hφ), hbij⟩

/-- Every algebraically closed field of characteristic zero of cardinality at most that of `ℂ` embeds in `ℂ`: it lies
in the algebraic closure `L` of `F(T_z : z ∈ ℂ)`, of the cardinality of `ℂ`, and `L ≅ ℂ` (Steinitz, Mathlib
`IsAlgClosed.ringEquiv_of_equiv_of_charZero`). -/
theorem nonempty_ringHom_complex (F : Type) [Field F] [CharZero F] (hF : #F ≤ #ℂ) : Nonempty (F →+* ℂ) := by
  let R := MvPolynomial ℂ F
  let Q := FractionRing R
  let L := AlgebraicClosure Q
  have hC : ℵ₀ < #ℂ := by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have hR : #R ≤ #ℂ := by
    refine (MvPolynomial.cardinalMk_le_max).trans ?_
    exact max_le (max_le hF le_rfl) hC.le
  have hQ : #Q ≤ #ℂ := by
    have hsurj : Function.Surjective fun p : R × R ↦ (algebraMap R Q p.1 / algebraMap R Q p.2 : Q) := by
      intro z
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) z
      exact ⟨(a, b), rfl⟩
    refine (Cardinal.mk_le_of_surjective hsurj).trans ?_
    rw [Cardinal.mk_prod, Cardinal.lift_id]
    exact (Cardinal.mul_le_max _ _).trans (max_le (max_le hR hR) hC.le)
  have hL : #L ≤ #ℂ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max Q L).trans (max_le hQ hC.le)
  let g : ℂ → L := fun z ↦ algebraMap Q L (algebraMap R Q (MvPolynomial.X z))
  have hg : Function.Injective g := by
    intro z w hzw
    have h1 := (algebraMap Q L).injective hzw
    have h2 := IsFractionRing.injective R Q h1
    exact MvPolynomial.X_injective h2
  have hCL : #ℂ ≤ #L := Cardinal.mk_le_of_injective hg
  let f : F →+* L := (algebraMap Q L).comp ((algebraMap R Q).comp MvPolynomial.C)
  have hf : Function.Injective f := f.injective
  have : CharZero L := charZero_of_injective_ringHom hf
  · have hLc : ℵ₀ < #L := hC.trans_le hCL
    obtain ⟨σ⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ) hLc
      (Cardinal.eq.mp (le_antisymm hL hCL))
    exact ⟨(σ : L →+* ℂ).comp f⟩

/-- **Proposition 12.21, corrected** (Milne; proof omitted in the book), for every algebraically closed field `F` of
characteristic zero of cardinality at most that of `ℂ` (for example `ℚ̄`, every countable algebraically closed field of
characteristic zero, and `ℂ`): `Cl(R)` acts simply transitively on `Ell_F(R)`, compatibly with `𝔞`-isogenies for
normalized complex multiplication. -/
@[kb "milne2017mf" "Section 12, Prop. 12.21 (pdf p. 126), corrected, fields of cardinality at most that of C"]
theorem classGroupActionPrincipalNormalized_of_mk_le (F : Type) [Field F] [IsAlgClosed F] [CharZero F]
    (hF : #F ≤ #ℂ) (K : Type) [Field K] [NumberField K] (O : NumberFieldOrder K) (hK : Module.finrank ℚ K = 2)
    (hTC : IsTotallyComplex K) (ι : K →+* F) :
    ∃ act : Pic O → EllCMOver F O → EllCMOver F O,
      (∀ (W W' : WeierstrassCurve.Affine F) [W.IsElliptic] [W'.IsElliptic] (i : O.toSubalgebra ≃+* Hom W W),
          IsNormalizedCM ι i →
          ∀ (I : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ) (J : Ideal O.toSubalgebra),
          ((J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) = I) →
          (hW : W.j ∈ EllCMOver F O) → (hW' : W'.j ∈ EllCMOver F O) → (φ : Hom W W') → IsAIsogeny i J φ →
            act (ClassGroup.mk (K := K) I) ⟨W.j, hW⟩ = ⟨W'.j, hW'⟩) ∧
      ∀ x₀, Function.Bijective fun c ↦ act c x₀ :=
  classGroupActionPrincipalNormalized_of_ringHom F (nonempty_ringHom_complex F hF).some K O hK hTC ι

/-- **Proposition 12.21, corrected, over the algebraic numbers** `ℚ̄ = AlgebraicClosure ℚ`. -/
@[kb "milne2017mf" "Section 12, Prop. 12.21 (pdf p. 126), corrected, over the algebraic closure of Q"]
theorem classGroupActionPrincipalNormalized_algebraicClosure_rat (K : Type) [Field K] [NumberField K]
    (O : NumberFieldOrder K) (hK : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K)
    (ι : K →+* AlgebraicClosure ℚ) :
    ∃ act : Pic O → EllCMOver (AlgebraicClosure ℚ) O → EllCMOver (AlgebraicClosure ℚ) O,
      (∀ (W W' : WeierstrassCurve.Affine (AlgebraicClosure ℚ)) [W.IsElliptic] [W'.IsElliptic]
          (i : O.toSubalgebra ≃+* Hom W W), IsNormalizedCM ι i →
          ∀ (I : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ) (J : Ideal O.toSubalgebra),
          ((J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) = I) →
          (hW : W.j ∈ EllCMOver (AlgebraicClosure ℚ) O) → (hW' : W'.j ∈ EllCMOver (AlgebraicClosure ℚ) O) →
          (φ : Hom W W') → IsAIsogeny i J φ →
            act (ClassGroup.mk (K := K) I) ⟨W.j, hW⟩ = ⟨W'.j, hW'⟩) ∧
      ∀ x₀, Function.Bijective fun c ↦ act c x₀ := by
  obtain ⟨τ⟩ : Nonempty (AlgebraicClosure ℚ →+* ℂ) := ⟨(IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ).toRingHom⟩
  exact classGroupActionPrincipalNormalized_of_ringHom _ τ K O hK hTC ι

end ModularFormsKB.Milne.Wave9
