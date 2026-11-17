/-
# Kohnen's trace identity, reduced to the lifts, one dimension inequality and multiplicity one

`KohnenTraceIdentity k` (`KohnenTrace.lean`, Kohnen 1980 `kohnen1980`, §2–§4 [unverified]) is the last input of H2
(`kohnenIsomorphism_of_trace_theta`). Kohnen proves it with a trace formula on $S^+_{k+1/2}(4)$, which is in neither
Mathlib nor Tau Ceti (Tau Ceti has only the level one Eichler–Selberg formula). This file proves it from three smaller
named statements of Kohnen's paper that it implies (`kohnenDLift_of_trace`, `kohnenDimensionLe_of_trace`,
`kohnenPlusMultOne_of_trace`):

- `KohnenDLift` (all admissible $D$): the $D$-th lift maps $S^+_{k+1/2}(4)$ into $S_{2k}(1)$;
- `KohnenDimensionLe`: $\dim S_{2k}(1) \le \dim S^+_{k+1/2}(4)$;
- `KohnenPlusMultOne`: multiplicity one in the plus space.

**Proved here.**
- `kohnenPlusEigenbasis_theta`: $S^+_{k+1/2}(4)$ has a basis of eigenforms of the $T(p^2)$, $p$ odd, with no input. The
  $T(p^2)$ are symmetric for the Petersson inner product (`plusHeckeSelfAdjoint`, `plusInnerCore`), hence semisimple
  (Mathlib `LinearMap.IsSymmetric.isFinitelySemisimple`), so each joint generalized eigenspace is a joint eigenspace.
- `kohnenTraceIdentity_of_iso_dLift`: the trace identity from Kohnen's isomorphism and the lifts. The isomorphism
  $\Phi$ intertwines $T(p^2)$ and $T(p)$ for odd $p$; on $\Phi^{-1}(F)$, $F$ a level one newform, $T^+(4)$ acts by a scalar
  $t$ (the joint odd eigenspaces of $S_{2k}(1)$ are lines, by strong multiplicity one), some $c(|D|)$ is nonzero (the
  Hecke recursion `eq_zero_of_fundamental_coeff_eq_zero`), and the $D$-th lift is $c(|D|)F$ and a $T(2)$-eigensequence
  with eigenvalue $t$ (`kohnenLiftCoeff_heckeTPlusFour`), so $t = a_F(2)$. Hence $\Phi$ conjugates every product of the
  plus-space Hecke operators to the corresponding product at level one, and traces agree.
- `kohnenTraceIdentity_of_inputs`: the trace identity from `KohnenDLift`, `KohnenDimensionLe` and `KohnenPlusMultOne`.
- `kohnenIsomorphism_theta_of_inputs`: **H2** from the same three statements.
-/
import ModularFormsKB.HalfIntegral.KohnenLUFourProof
import ModularFormsKB.HalfIntegral.PlusHeckeAdjoint
import ModularFormsKB.HalfIntegral.Abstract.KohnenZagierInner
import Mathlib.Analysis.InnerProductSpace.Semisimple

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups ModularForm

local notation "ℍ" => UpperHalfPlane

variable {k : ℕ}

/-! ### The eigenbasis of the plus space, from self-adjointness -/

/-- **The odd $T(p^2)$ are semisimple on the plus space:** a generalized eigenvector is an eigenvector, because
$T(p^2)$ is symmetric for the Petersson inner product. -/
theorem plusHeckeOdd_maxGenEigenspace_eq (k : ℕ) (p : OddPrime) (c : ℂ) :
    (plusHeckeOdd k p).maxGenEigenspace c = (plusHeckeOdd k p).eigenspace c := by
  let _ : NormedAddCommGroup (PlusSpace k) := (plusInnerCore thetaMultiplierSystem k).toNormedAddCommGroup
  let _ : InnerProductSpace ℂ (PlusSpace k) :=
    InnerProductSpace.ofCore (plusInnerCore thetaMultiplierSystem k).toCore
  have hsym : (plusHeckeOdd k p).IsSymmetric := by
    intro x y
    obtain ⟨a, ha⟩ := plusSpace_exists_hasQExp x
    obtain ⟨b, hb⟩ := plusSpace_exists_hasQExp y
    exact (PlusHeckeAdjoint.plusHeckeSelfAdjoint k).selfAdjoint p.1.2 p.2 x y (plusHeckeOdd k p x) (plusHeckeOdd k p y) a b x.2 y.2
      (plusHeckeOdd k p x).2 (plusHeckeOdd k p y).2 ha hb (hasQExp_plusHecke k p.1.2 p.2 x ha)
      (hasQExp_plusHecke k p.1.2 p.2 y hb)
  exact hsym.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace c

/-- **The plus space is spanned by joint eigenvectors of the odd $T(p^2)$.** -/
theorem span_plusHeckeOdd_jointEigen (k : ℕ) :
    Submodule.span ℂ {v : PlusSpace k | ∃ ν, IsJointEigenvector (plusHeckeOdd k) ν v} = ⊤ := by
  rw [eq_top_iff, ← iSup_jointGen (plusHeckeOdd k) (plusHeckeOdd_commute k)]
  refine iSup_le fun χ x hx ↦ Submodule.subset_span ⟨χ, fun i ↦ ?_⟩
  have hx' : x ∈ (plusHeckeOdd k i).maxGenEigenspace (χ i) := by
    simp only [jointGen, Submodule.mem_iInf] at hx
    exact hx i
  rw [plusHeckeOdd_maxGenEigenspace_eq] at hx'
  exact Module.End.mem_eigenspace_iff.1 hx'

/-- A joint eigenvector of `plusHeckeOdd` is an eigenform, with the eigenvalues extended by $0$. -/
private theorem isPlusEigenform_of_jointEigen {v : PlusSpace k} {ν : OddPrime → ℂ}
    (hv : IsJointEigenvector (plusHeckeOdd k) ν v) :
    IsPlusEigenform thetaMultiplierSystem k v
      (fun p ↦ if hp : p.Prime ∧ p ≠ 2 then ν ⟨⟨p, hp.1⟩, hp.2⟩ else 0) := by
  obtain ⟨c, hc⟩ := plusSpace_exists_hasQExp v
  refine ⟨v.2, c, hc, fun p hp hp2 ↦ ?_⟩
  have h1 := hasQExp_plusHecke k hp hp2 v hc
  have h2 := hv ⟨⟨p, hp⟩, hp2⟩
  have e : plusHeckeOdd k ⟨⟨p, hp⟩, hp2⟩ = plusHecke k hp hp2 := rfl
  rw [e] at h2
  rw [h2] at h1
  show _ = (if hp' : p.Prime ∧ p ≠ 2 then ν ⟨⟨p, hp'.1⟩, hp'.2⟩ else 0) • c
  rw [dite_eq_left_of_eq_true (eq_true ⟨hp, hp2⟩)]
  exact Abstract.hasQExp_unique h1 (Abstract.hasQExp_smul _ hc)

/-- **$S^+_{k+1/2}(4)$ has a basis of eigenforms of the odd $T(p^2)$** (Kohnen 1980 `kohnen1980`, §1 [unverified]),
with no input: `KohnenPlusEigenbasis` for the theta multiplier, from `plusHeckeSelfAdjoint`. -/
@[kb "kohnen1980" "§1: S⁺_{k+1/2}(4) has a basis of simultaneous eigenforms of the T(p²), p odd [unverified]"]
theorem kohnenPlusEigenbasis_theta (k : ℕ) : KohnenPlusEigenbasis thetaMultiplierSystem k := by
  classical
  refine ⟨fun _ ↦ ?_⟩
  have hspan := span_plusHeckeOdd_jointEigen k
  set s : Set (PlusSpace k) := {v | ∃ ν, IsJointEigenvector (plusHeckeOdd k) ν v}
  obtain ⟨t, hts, htspan, hli⟩ := exists_linearIndependent ℂ s
  have htfin : t.Finite := hli.setFinite
  let e : Fin htfin.toFinset.card ≃ t :=
    (htfin.toFinset.equivFin.symm).trans (Equiv.subtypeEquivRight fun x ↦ htfin.mem_toFinset)
  have hsys : ∀ i : Fin htfin.toFinset.card, ∃ ν, IsJointEigenvector (plusHeckeOdd k) ν (e i : PlusSpace k) :=
    fun i ↦ hts (e i).2
  choose ν hν using hsys
  refine ⟨htfin.toFinset.card, fun i ↦ ((e i : PlusSpace k) : ℍ → ℂ),
    fun i p ↦ if hp : p.Prime ∧ p ≠ 2 then ν i ⟨⟨p, hp.1⟩, hp.2⟩ else 0,
    fun i ↦ isPlusEigenform_of_jointEigen (hν i), ?_, ?_⟩
  · have hli' : LinearIndependent ℂ (fun i ↦ (e i : PlusSpace k)) :=
      hli.comp (fun i ↦ e i) e.injective
    exact hli'.map' (PlusSpace k).subtype (Submodule.ker_subtype _)
  · intro g hg
    have hmem : (⟨g, hg⟩ : PlusSpace k) ∈ Submodule.span ℂ t := by
      rw [htspan, hspan]; exact Submodule.mem_top
    have hrange : Set.range (fun i ↦ (e i : PlusSpace k)) = t := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩; exact (e i).2
      · intro hx; exact ⟨e.symm ⟨x, hx⟩, by simp⟩
    rw [← hrange] at hmem
    have := Submodule.mem_map_of_mem (f := (PlusSpace k).subtype) hmem
    rw [Submodule.map_span, ← Set.range_comp] at this
    exact this

/-! ### Level one: the joint odd eigenspaces are lines -/

/-- The $f'$-th coordinate in the newform basis turns $T(p)$ into multiplication by the eigenvalue of $f'$. -/
private theorem coord_levelOneHecke (k : ℕ) (f' : HeckeRing.GL2.Newform 1 ((2 * k : ℕ) : ℤ)) (p : Nat.Primes)
    (G : CuspForm 𝒮ℒ (2 * k : ℕ)) :
    (TauCeti.levelOneNewformBasis _).coord f' (levelOneHecke k p G) =
      levelOneEigenvalue k f' p * (TauCeti.levelOneNewformBasis _).coord f' G := by
  have h : ((TauCeti.levelOneNewformBasis ((2 * k : ℕ) : ℤ)).coord f').comp (levelOneHecke k p) =
      levelOneEigenvalue k f' p • (TauCeti.levelOneNewformBasis ((2 * k : ℕ) : ℤ)).coord f' := by
    refine (TauCeti.levelOneNewformBasis ((2 * k : ℕ) : ℤ)).ext fun i ↦ ?_
    rw [LinearMap.comp_apply, levelOneHecke_basis k p i, map_smul, LinearMap.smul_apply]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul]
    by_cases hi : i = f'
    · subst hi; rfl
    · simp [hi]
  exact congrArg (fun L : CuspForm 𝒮ℒ (2 * k : ℕ) →ₗ[ℂ] ℂ ↦ L G) h

/-- **A level one cusp form with the odd eigenvalues of a newform $f$ is a multiple of $f$** (Tau Ceti's newform basis
and strong multiplicity one). -/
theorem levelOne_eq_smul_of_oddEigen (k : ℕ) (f : HeckeRing.GL2.Newform 1 ((2 * k : ℕ) : ℤ))
    (G : CuspForm 𝒮ℒ (2 * k : ℕ))
    (hG : ∀ p : OddPrime, levelOneHecke k p.1 G = levelOneEigenvalue k f p.1 • G) :
    G = (TauCeti.levelOneNewformBasis _).coord f G • TauCeti.levelOneNewformBasis _ f := by
  classical
  set b := TauCeti.levelOneNewformBasis ((2 * k : ℕ) : ℤ)
  have : Fintype (HeckeRing.GL2.Newform 1 ((2 * k : ℕ) : ℤ)) :=
    @Fintype.ofFinite _ (Module.Finite.finite_basis b)
  have hz : ∀ f', f' ≠ f → b.coord f' G = 0 := by
    intro f' hf'
    by_contra hne
    apply hf'
    apply levelOneEigenvalue_odd_injective k
    funext p
    have h1 := coord_levelOneHecke k f' p.1 G
    rw [hG p, map_smul, smul_eq_mul] at h1
    exact (mul_right_cancel₀ hne h1).symm
  conv_lhs => rw [← b.sum_repr G]
  rw [Finset.sum_eq_single f (fun f' _ hf' ↦ by rw [← Module.Basis.coord_apply, hz f' hf', zero_smul])
    (fun h ↦ absurd (Finset.mem_univ f) h)]
  rfl

/-! ### The trace identity from the isomorphism and the lifts -/

/-- Conjugation by a linear equivalence preserves traces of products. -/
theorem trace_listProd_conj {ι V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) (A : ι → Module.End ℂ V) (B : ι → Module.End ℂ W) (h : ∀ i, e.conj (A i) = B i)
    (l : List ι) : LinearMap.trace ℂ V (l.map A).prod = LinearMap.trace ℂ W (l.map B).prod := by
  have hprod : (l.map B).prod = e.conj (l.map A).prod := by
    induction l with
    | nil =>
      simp only [List.map_nil, List.prod_nil]
      exact (e.conj_id).symm
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [ih, ← h a, Module.End.mul_eq_comp, Module.End.mul_eq_comp, e.conj_comp]
  rw [hprod, LinearMap.trace_conj']

section Iso

variable (Φ : PlusSpace k ≃ₗ[ℂ] CuspForm 𝒮ℒ (2 * k : ℕ))
  (hΦ : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ f f' : PlusSpace k, ∀ a b : ℕ → ℂ,
      Abstract.HasQExp f a → Abstract.HasQExp f' (heckeT k 1 1 p a) → Abstract.HasQExp (Φ f) b →
        Abstract.HasQExp (Φ f') (heckeTInt (2 * k) 1 1 p b))
include hΦ

/-- The isomorphism intertwines $T(p^2)$ and $T(p)$ for odd $p$, as operators. -/
private theorem iso_odd (p : OddPrime) (x : PlusSpace k) : Φ (plusHeckeOdd k p x) = levelOneHeckeOdd k p (Φ x) := by
  obtain ⟨a, ha⟩ := plusSpace_exists_hasQExp x
  have hb := hasQExp_qExpansion (Φ x)
  have h1 := hΦ p.1 p.1.2 p.2 x (plusHeckeOdd k p x) a _ ha (hasQExp_plusHecke k p.1.2 p.2 x ha) hb
  have h2 := hasQExp_levelOneHecke k p.1 hb
  exact DFunLike.coe_injective (Abstract.eq_of_hasQExp h1 h2)

private theorem conj_odd (p : OddPrime) : Φ.conj (plusHeckeOdd k p) = levelOneHeckeOdd k p := by
  ext1 y
  rw [LinearEquiv.conj_apply_apply, iso_odd Φ hΦ, LinearEquiv.apply_symm_apply]

omit hΦ in
/-- The coefficients of a plus form satisfy the plus condition. -/
private theorem mem_plusSeq_of_hasQExp' (g : PlusSpace k) {c : ℕ → ℂ} (hc : Abstract.HasQExp g c) :
    c ∈ plusSeq k := by
  obtain ⟨-, a, ha, hap⟩ := g.2
  rw [Abstract.hasQExp_unique hc ha]
  exact hap

/-- **On the preimage of a newform, $T^+(4)$ acts by the eigenvalue of $T(2)$.** -/
private theorem iso_two_basis (hk : 1 ≤ k) (hL : ∀ D, KohnenDisc k D → KohnenDLift thetaMultiplierSystem k D)
    {T4 : Module.End ℂ (PlusSpace k)} (h4 : IsTPlusFour k T4) (f : HeckeRing.GL2.Newform 1 ((2 * k : ℕ) : ℤ)) :
    Φ (T4 (Φ.symm (TauCeti.levelOneNewformBasis _ f))) =
      levelOneHecke k ⟨2, Nat.prime_two⟩ (TauCeti.levelOneNewformBasis _ f) := by
  classical
  set b := TauCeti.levelOneNewformBasis ((2 * k : ℕ) : ℤ)
  set F := b f with hF
  set g := Φ.symm F with hg
  set ev := levelOneEigenvalue k f
  -- `g` is an odd eigenform with the eigenvalues of `f`
  have hgodd : ∀ p : OddPrime, plusHeckeOdd k p g = ev p.1 • g := by
    intro p
    apply Φ.injective
    rw [iso_odd Φ hΦ, map_smul, hg, LinearEquiv.apply_symm_apply]
    exact levelOneHecke_basis k p.1 f
  -- so is `T4 g`, and its image is a multiple of `F`
  have h4odd : ∀ p : OddPrime, levelOneHecke k p.1 (Φ (T4 g)) = ev p.1 • Φ (T4 g) := by
    intro p
    have hc : Commute (plusHeckeOdd k p) T4 := by
      have := plusHeckeAll_commute k h4 p.1 ⟨2, Nat.prime_two⟩
      rwa [plusHeckeAll_of_ne_two k T4 p.2,
        plusHeckeAll_two k T4 (show ((⟨2, Nat.prime_two⟩ : Nat.Primes) : ℕ) = 2 from rfl)] at this
    have e := iso_odd Φ hΦ p (T4 g)
    rw [← mul_apply_eq_comp, hc.eq, mul_apply_eq_comp, hgodd p, map_smul, map_smul] at e
    exact e.symm
  set s := b.coord f (Φ (T4 g))
  have hT4 : T4 g = s • g := by
    apply Φ.injective
    rw [map_smul, hg, LinearEquiv.apply_symm_apply]
    exact levelOne_eq_smul_of_oddEigen k f _ h4odd
  -- the coefficients of `g`
  obtain ⟨c, hc⟩ := plusSpace_exists_hasQExp g
  have hplus := mem_plusSeq_of_hasQExp' g hc
  obtain ⟨μ, hμ⟩ : ∃ μ : ℕ → ℂ, ∀ (p : ℕ) (hp : p.Prime), μ p = ev ⟨p, hp⟩ :=
    ⟨fun p ↦ if hp : p.Prime then ev ⟨p, hp⟩ else 0, fun p hp ↦ dite_eq_left_of_eq_true (eq_true hp)⟩
  have hcodd : ∀ p : ℕ, p.Prime → p ≠ 2 → heckeT k 1 1 p c = μ p • c := by
    intro p hp hp2
    have h1 := hasQExp_plusHecke k hp hp2 g hc
    have h2 := hgodd ⟨⟨p, hp⟩, hp2⟩
    have e : plusHeckeOdd k ⟨⟨p, hp⟩, hp2⟩ = plusHecke k hp hp2 := rfl
    rw [e] at h2
    rw [h2] at h1
    rw [hμ p hp]
    exact Abstract.hasQExp_unique h1 (Abstract.hasQExp_smul _ hc)
  have hc4 : heckeTPlusFour k c = s • c := by
    have h1 := h4 g c hc
    rw [hT4] at h1
    exact Abstract.hasQExp_unique h1 (Abstract.hasQExp_smul _ hc)
  -- some fundamental coefficient is nonzero
  have hg0 : g ≠ 0 := by
    intro h0
    have : F = 0 := by rw [← Φ.apply_symm_apply F, ← hg, h0, map_zero]
    exact b.ne_zero f this
  obtain ⟨D, hD, hcD⟩ : ∃ D, KohnenDisc k D ∧ c D.natAbs ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 := eq_zero_of_fundamental_coeff_eq_zero hplus μ hcodd s hc4 hall
    exact hg0 (Subtype.ext (Abstract.eq_zero_of_hasQExp_const
      (thetaMultiplierSystem.plusCuspForms_le k 1 1 g.2) hc h0))
  -- the `D`-th lift
  obtain ⟨G, hG⟩ := (hL D hD).lift hk g g.2 c hc
  set bl := kohnenLiftCoeff k D c with hbl
  have hGodd : ∀ p : OddPrime, levelOneHecke k p.1 G = ev p.1 • G := by
    intro p
    have h1 := hasQExp_levelOneHecke k p.1 hG
    have e := kohnenLiftCoeff_heckeT_of_fundamental k hD.1 hD.2 p.1.2 p.2 c
    rw [hcodd p.1 p.1.2 p.2, show kohnenLiftCoeff k D (μ p.1 • c) = μ p.1 • kohnenLiftCoeff k D c from
      (kohnenLiftLin k D).map_smul _ c] at e
    rw [← e] at h1
    rw [hμ p.1 p.1.2] at h1
    exact DFunLike.coe_injective (Abstract.eq_of_hasQExp h1 (Abstract.hasQExp_smul _ hG))
  have hG2 : levelOneHecke k ⟨2, Nat.prime_two⟩ G = s • G := by
    have h1 := hasQExp_levelOneHecke k ⟨2, Nat.prime_two⟩ hG
    have e := kohnenLiftCoeff_heckeTPlusFour k hD hplus
    rw [hc4, show kohnenLiftCoeff k D (s • c) = s • kohnenLiftCoeff k D c from
      (kohnenLiftLin k D).map_smul _ c] at e
    rw [show ((⟨2, Nat.prime_two⟩ : Nat.Primes) : ℕ) = 2 from rfl, ← e] at h1
    exact DFunLike.coe_injective (Abstract.eq_of_hasQExp h1 (Abstract.hasQExp_smul _ hG))
  -- `G = s' F` with `s' = c(|D|) ≠ 0`
  set s' := b.coord f G
  have hGF : G = s' • F := levelOne_eq_smul_of_oddEigen k f G hGodd
  obtain ⟨a, ha, -, ha1, -⟩ := exists_hasQExp_levelOneNewformBasis k f
  have hs' : s' ≠ 0 := by
    have h1 : Abstract.HasQExp G (s' • a) := by rw [hGF]; exact Abstract.hasQExp_smul _ ha
    have e := congrFun (Abstract.hasQExp_unique hG h1) 1
    rw [hbl, kohnenLiftCoeff_one, Pi.smul_apply, ha1, smul_eq_mul, mul_one] at e
    rwa [← e]
  have hF2 : levelOneHecke k ⟨2, Nat.prime_two⟩ F = ev ⟨2, Nat.prime_two⟩ • F := levelOneHecke_basis k _ f
  have hs : s = ev ⟨2, Nat.prime_two⟩ := by
    have e := hG2
    rw [hGF, map_smul, hF2, smul_smul, smul_smul] at e
    have hF0 : F ≠ 0 := b.ne_zero f
    have := smul_left_injective ℂ hF0 e
    exact (mul_left_cancel₀ hs' (this.trans (mul_comm s s'))).symm
  rw [hT4, map_smul, hg, LinearEquiv.apply_symm_apply, hF2, hs]

/-- The isomorphism conjugates $T^+(4)$ to $T(2)$. -/
private theorem conj_two (hk : 1 ≤ k) (hL : ∀ D, KohnenDisc k D → KohnenDLift thetaMultiplierSystem k D)
    {T4 : Module.End ℂ (PlusSpace k)} (h4 : IsTPlusFour k T4) :
    Φ.conj T4 = levelOneHecke k ⟨2, Nat.prime_two⟩ :=
  (TauCeti.levelOneNewformBasis _).ext fun f ↦ by
    rw [LinearEquiv.conj_apply_apply]
    exact iso_two_basis Φ hΦ hk hL h4 f

end Iso

/-- **Kohnen's trace identity from Kohnen's isomorphism and the $D$-th lifts.** -/
@[kb "kohnen1980" "Thm. 1: the Hecke-module isomorphism and the D-th lifts give tr T⁺(n²) = tr T(n), here for products of prime Hecke operators [unverified]"]
theorem kohnenTraceIdentity_of_iso_dLift (hI : KohnenIsomorphism thetaMultiplierSystem k)
    (hL : ∀ D, KohnenDisc k D → KohnenDLift thetaMultiplierSystem k D) : KohnenTraceIdentity k := by
  refine ⟨fun hk l ↦ ?_, fun hk T4 h4 l ↦ ?_⟩
  · obtain ⟨Φ, hΦ⟩ := hI.iso hk
    exact trace_listProd_conj Φ _ _ (conj_odd Φ hΦ) l
  · obtain ⟨Φ, hΦ⟩ := hI.iso hk
    refine trace_listProd_conj Φ _ _ (fun p ↦ ?_) l
    by_cases hp : (p : ℕ) = 2
    · rw [plusHeckeAll_two k T4 hp, conj_two Φ hΦ hk hL h4]
      congr 1
      exact Subtype.ext hp.symm
    · rw [plusHeckeAll_of_ne_two k T4 hp]
      exact conj_odd Φ hΦ ⟨p, hp⟩

/-- **H2, Kohnen's isomorphism for the theta multiplier, from the lifts, one dimension inequality and multiplicity
one.** The eigenbasis (`kohnenPlusEigenbasis_theta`) and $T^+(4)$ (`kohnenTPlusFourStable_theta`) are proved. -/
@[kb "kohnen1980" "Thm. 1 for the theta multiplier from the D-th lifts, dim S_{2k}(1) ≤ dim S⁺ and multiplicity one [unverified]"]
theorem kohnenIsomorphism_theta_of_inputs (k : ℕ)
    (hL : ∀ D, KohnenDisc k D → KohnenDLift thetaMultiplierSystem k D)
    (hdim : KohnenDimensionLe thetaMultiplierSystem k) (h1 : KohnenPlusMultOne thetaMultiplierSystem k) :
    KohnenIsomorphism thetaMultiplierSystem k :=
  kohnenIsomorphism_of_tPlusFour thetaMultiplierSystem k hL hdim (kohnenPlusEigenbasis_theta k) h1
    (kohnenTPlusFourStable_theta k)

/-- **Kohnen's trace identity from the lifts, one dimension inequality and multiplicity one** (the reduction of
`KohnenTraceIdentity`; each of the three is implied by it: `kohnenDLift_of_trace`, `kohnenDimensionLe_of_trace`,
`kohnenPlusMultOne_of_trace`). -/
@[kb "kohnen1980" "tr T⁺(n²) = tr T(n) from the D-th lifts, dim S_{2k}(1) ≤ dim S⁺ and multiplicity one [unverified]"]
theorem kohnenTraceIdentity_of_inputs (k : ℕ)
    (hL : ∀ D, KohnenDisc k D → KohnenDLift thetaMultiplierSystem k D)
    (hdim : KohnenDimensionLe thetaMultiplierSystem k) (h1 : KohnenPlusMultOne thetaMultiplierSystem k) :
    KohnenTraceIdentity k :=
  kohnenTraceIdentity_of_iso_dLift (kohnenIsomorphism_theta_of_inputs k hL hdim h1) hL

end ModularFormsKB.HalfIntegral
