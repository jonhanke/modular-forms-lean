import TauCeti.NumberTheory.HeckeRing.Associativity
import TauCeti.NumberTheory.HeckeRing.Multiplicity.Equiv
import ModularFormsKB.Miyake.Wave12.Gamma1Delta1

/-!
# Miyake, Theorem 4.5.18 (1): `R(Γ₁(N), Δ₁(N)) ≅ R(Γ₀(N), Δ₀(N))`

Miyake, *Modular Forms* (Springer 1989), Theorem 4.5.18 (1), p. 151: the correspondence
`Γ₁(N) α Γ₁(N) ↦ Γ₀(N) α Γ₀(N)` (`α ∈ Δ₁(N)`) extends to a ring isomorphism of the Hecke rings
`R(Γ₁(N), Δ₁(N)) ≅ R(Γ₀(N), Δ₀(N))`. Wave 8 proved the bijection of double cosets
(`ModularFormsKB.Miyake.Wave8.doubleCoset_gamma1_eq_iff`, `exists_delta1_doubleCoset_eq`); this
file proves that the structure constants agree, so the bijection is a ring isomorphism.

## The abstract comparison

For `Γ' ≤ Γ` (subgroups) and `Δ' ≤ Δ` (submonoids) of a group, `IsHeckeRestriction Δ Δ' Γ Γ'`
records:
* `Γ' ⊆ Δ'`;
* right cancellation: `x ∈ Δ'`, `γ ∈ Γ`, `x γ ∈ Δ'` imply `γ ∈ Γ'`;
* `Γ g Γ ⊆ Γ' g Γ` for `g ∈ Δ'` (the left-coset form of Miyake's (4.5.42));
* every double coset `Γ x Γ`, `x ∈ Δ`, meets `Δ'`.
Under these, `Γ' g Γ' ↦ Γ g Γ` is a bijection `Γ'\Δ'/Γ' ≃ Γ\Δ/Γ` (`cosetEquiv`) and Shimura's
multiplicities agree (`multiplicity_eq`), so it extends linearly to a ring isomorphism
`heckeRingEquiv : 𝕋 Δ' Γ' R ≃+* 𝕋 Δ Γ R` over every semiring `R` of coefficients. This is the
argument of Shimura, *Introduction to the arithmetic theory of automorphic functions*, §3.1, which
Miyake cites; the multiplicities are compared as counts of left cosets
(`multiplicity_eq_natCard_cosetCount`).

Hecke rings here are Tau Ceti's `𝕋 Δ H R` (Shimura's multiplicities, computed with left cosets
`σᵢ g H`); Miyake's Hecke ring uses right cosets `H αᵢ`. Both conventions give the same theorem:
the statement and proof are symmetric.

## Main results
* `heckeRingGamma1EquivGamma0` (**Theorem 4.5.18 (1)**): `𝕋 Δ₁(N) Γ₁(N) R ≃+* 𝕋 Δ₀(N) Γ₀(N) R`,
  with `heckeRingGamma1EquivGamma0_single`: `[Γ₁(N) α Γ₁(N)] ↦ [Γ₀(N) α Γ₀(N)]`.
-/

open DoubleCoset
open scoped Pointwise HeckeCosetModule

noncomputable section

namespace ModularFormsKB.Miyake.Wave12

section Abstract

variable {G : Type*} [Group G]

/-! ### Multiplicities as counts of left cosets -/

/-- The left cosets `x H₂` inside `H₁ g H₂` with `d ∈ x H₂ h H₃`: Shimura's multiplicity
`m(g, h; d)` counts them (`multiplicity_eq_natCard_cosetCount`). The set depends on `g` and `h`
only through the double cosets `H₁ g H₂` and `H₂ h H₃`. -/
def cosetCount (H₁ H₂ H₃ : Subgroup G) (g h d : G) : Set (G ⧸ H₂) :=
  {c | ∃ x ∈ doubleCoset g (H₁ : Set G) H₂, (x : G ⧸ H₂) = c ∧
    x⁻¹ * d ∈ doubleCoset h (H₂ : Set G) H₃}

lemma mul_mem_doubleCoset_of_mem_left {H K : Subgroup G} {h k y : G} (hk : k ∈ H)
    (hy : y ∈ doubleCoset h (H : Set G) K) : k * y ∈ doubleCoset h (H : Set G) K := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hy
  exact mem_doubleCoset.mpr ⟨k * a, mul_mem hk ha, b, hb, by simp only [mul_assoc]⟩

lemma doubleCoset_subset_of_le {H H' K K' : Subgroup G} (hH : H ≤ H') (hK : K ≤ K') (g : G) :
    doubleCoset g (H : Set G) K ⊆ doubleCoset g (H' : Set G) K' := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hx
  exact mem_doubleCoset.mpr ⟨a, hH ha, b, hK hb, rfl⟩

/-- **Shimura's multiplicity counts left cosets**: `m(g, h; d)` is the number of left cosets
`x H₂ ⊆ H₁ g H₂` with `x⁻¹ d ∈ H₂ h H₃`. -/
theorem multiplicity_eq_natCard_cosetCount (H₁ H₂ H₃ : Subgroup G) (g h d : G)
    [Finite (DecompQuotient H₁ H₂ g)] [Finite (DecompQuotient H₂ H₃ h)] :
    multiplicity H₁ H₂ H₃ g h d = Nat.card (cosetCount H₁ H₂ H₃ g h d) := by
  rw [multiplicity_eq_card_filter]
  refine Nat.card_congr (Equiv.ofBijective
    (fun i ↦ ⟨(((i.1.out : G) * g : G) : G ⧸ H₂), (i.1.out : G) * g,
      mem_doubleCoset.mpr ⟨i.1.out, i.1.out.2, 1, one_mem _, by rw [mul_one]⟩, rfl, i.2⟩)
    ⟨fun i j hij ↦ Subtype.ext (mk_out_mul_injective H₁ H₂ g (congrArg Subtype.val hij)), ?_⟩)
  rintro ⟨c, x, hx, rfl, hxd⟩
  rw [doubleCoset_eq_iUnion_leftCosets, Set.mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  rw [mem_leftCoset_iff] at hi
  refine ⟨⟨i, ?_⟩, Subtype.ext (QuotientGroup.eq.mpr hi)⟩
  show ((i.out : G) * g)⁻¹ * d ∈ doubleCoset h (H₂ : Set G) H₃
  have := mul_mem_doubleCoset_of_mem_left hi hxd
  simpa only [mul_assoc, mul_inv_cancel_left] using this

/-- The multiplicity depends on its first argument only through its double coset (finite
decomposition quotients). -/
theorem multiplicity_congr_first (H₁ H₂ H₃ : Subgroup G) {g g' : G} (h d : G)
    (hg : g' ∈ doubleCoset g (H₁ : Set G) H₂)
    [Finite (DecompQuotient H₁ H₂ g)] [Finite (DecompQuotient H₁ H₂ g')]
    [Finite (DecompQuotient H₂ H₃ h)] :
    multiplicity H₁ H₂ H₃ g' h d = multiplicity H₁ H₂ H₃ g h d := by
  rw [multiplicity_eq_natCard_cosetCount, multiplicity_eq_natCard_cosetCount, cosetCount,
    cosetCount, doubleCoset_eq_of_mem hg]

/-! ### Restriction of a Hecke pair -/

/-- The conditions under which `Γ' g Γ' ↦ Γ g Γ` identifies the Hecke ring of `(Γ', Δ')` with
that of `(Γ, Δ)` (Shimura §3.1; Miyake, proof of Theorem 4.5.18). -/
structure IsHeckeRestriction (Δ Δ' : Submonoid G) (Γ Γ' : Subgroup G) : Prop where
  delta_le : Δ' ≤ Δ
  gamma_le : Γ' ≤ Γ
  gamma'_le : Γ'.toSubmonoid ≤ Δ'
  cancel : ∀ x ∈ Δ', ∀ γ ∈ Γ, x * γ ∈ Δ' → γ ∈ Γ'
  doubleCoset_subset : ∀ g ∈ Δ', doubleCoset g (Γ : Set G) Γ ⊆ doubleCoset g (Γ' : Set G) Γ
  exists_mem : ∀ x ∈ Δ, ∃ y ∈ Δ', y ∈ doubleCoset x (Γ : Set G) Γ

namespace IsHeckeRestriction

variable {Δ Δ' : Submonoid G} {Γ Γ' : Subgroup G} (hR : IsHeckeRestriction Δ Δ' Γ Γ')
include hR

lemma doubleCoset_subset_delta' {g : G} (hg : g ∈ Δ') : doubleCoset g (Γ' : Set G) Γ' ⊆ Δ' := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hx
  exact mul_mem (mul_mem (hR.gamma'_le ha) hg) (hR.gamma'_le hb)

/-- The key step: for `x, h, d ∈ Δ'`, `x⁻¹ d ∈ Γ h Γ` implies `x⁻¹ d ∈ Γ' h Γ'`. -/
lemma mem_doubleCoset_of_mem {x h d : G} (hx : x ∈ Δ') (hh : h ∈ Δ') (hd : d ∈ Δ')
    (hm : x⁻¹ * d ∈ doubleCoset h (Γ : Set G) Γ) : x⁻¹ * d ∈ doubleCoset h (Γ' : Set G) Γ' := by
  obtain ⟨a, ha, b, hb, he⟩ := mem_doubleCoset.mp (hR.doubleCoset_subset h hh hm)
  have hd' : x * a * h * b = d := by
    rw [show x * a * h * b = x * (a * h * b) by group, ← he, mul_inv_cancel_left]
  have hxah : x * a * h ∈ Δ' := mul_mem (mul_mem hx (hR.gamma'_le ha)) hh
  have hb' : b ∈ Γ' := hR.cancel _ hxah b hb (by rw [hd']; exact hd)
  exact mem_doubleCoset.mpr ⟨a, ha, b, hb', he⟩

/-- For `g, h ∈ Δ'`: `Γ' g Γ' = Γ' h Γ'` if and only if `Γ g Γ = Γ h Γ`. -/
lemma doubleCoset_eq_iff {g h : G} (hg : g ∈ Δ') (hh : h ∈ Δ') :
    doubleCoset g (Γ' : Set G) Γ' = doubleCoset h (Γ' : Set G) Γ' ↔
      doubleCoset g (Γ : Set G) Γ = doubleCoset h (Γ : Set G) Γ := by
  constructor
  · intro e
    have hm : g ∈ doubleCoset h (Γ' : Set G) Γ' := e ▸ mem_doubleCoset_self _ _ _
    exact doubleCoset_eq_of_mem (doubleCoset_subset_of_le hR.gamma_le hR.gamma_le h hm)
  · intro e
    have hm : g ∈ doubleCoset h (Γ : Set G) Γ := e ▸ mem_doubleCoset_self _ _ _
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp (hR.doubleCoset_subset h hh hm)
    have hb' : b ∈ Γ' := hR.cancel _ (mul_mem (hR.gamma'_le ha) hh) b hb hg
    exact doubleCoset_eq_of_mem (mem_doubleCoset.mpr ⟨a, ha, b, hb', rfl⟩)

/-- The bijection `Γ'\Δ'/Γ' ≃ Γ\Δ/Γ`, `Γ' g Γ' ↦ Γ g Γ`. -/
def cosetEquiv : HeckeCoset Δ' Γ' Γ' ≃ HeckeCoset Δ Γ Γ :=
  Equiv.ofBijective (HeckeCoset.map hR.delta_le hR.gamma_le hR.gamma_le) <| by
    refine ⟨fun D₁ D₂ ↦ ?_, fun D ↦ ?_⟩
    · induction D₁ using HeckeCoset.induction with | h g =>
      induction D₂ using HeckeCoset.induction with | h h =>
      rw [HeckeCoset.map_mk, HeckeCoset.map_mk, HeckeCoset.eq_iff, HeckeCoset.eq_iff]
      exact (hR.doubleCoset_eq_iff g.2 h.2).mpr
    · induction D using HeckeCoset.induction with | h x =>
      obtain ⟨y, hy, hyx⟩ := hR.exists_mem x x.2
      refine ⟨HeckeCoset.mk Γ' Γ' ⟨y, hy⟩, ?_⟩
      rw [HeckeCoset.map_mk]
      exact HeckeCoset.mk_eq_mk_of_mem hyx

@[simp] lemma cosetEquiv_mk (g : Δ') :
    hR.cosetEquiv (HeckeCoset.mk Γ' Γ' g) =
      HeckeCoset.mk Γ Γ (Submonoid.inclusion hR.delta_le g) :=
  rfl

lemma cosetEquiv_rep_mem (D : HeckeCoset Δ' Γ' Γ') :
    (((hR.cosetEquiv D).rep : Δ) : G) ∈ doubleCoset ((D.rep : Δ') : G) (Γ : Set G) Γ := by
  have e : hR.cosetEquiv D = HeckeCoset.mk Γ Γ (Submonoid.inclusion hR.delta_le D.rep) := by
    conv_lhs => rw [← HeckeCoset.mk_rep D]
    rfl
  rw [e]
  exact HeckeCoset.rep_mk_mem_doubleCoset (H₁ := Γ) (H₂ := Γ)
    (Submonoid.inclusion hR.delta_le D.rep)

/-- **The multiplicities agree**: for `g, h, d ∈ Δ'`,
`m_{Γ'}(g, h; d) = m_Γ(g, h; d)`. -/
theorem multiplicity_eq {g h d : G} (hg : g ∈ Δ') (hh : h ∈ Δ') (hd : d ∈ Δ')
    [Finite (DecompQuotient Γ' Γ' g)] [Finite (DecompQuotient Γ' Γ' h)]
    [Finite (DecompQuotient Γ Γ g)] [Finite (DecompQuotient Γ Γ h)] :
    multiplicity Γ' Γ' Γ' g h d = multiplicity Γ Γ Γ g h d := by
  rw [multiplicity_eq_natCard_cosetCount, multiplicity_eq_natCard_cosetCount]
  refine Nat.card_congr (Set.BijOn.equiv (Subgroup.quotientMapOfLE hR.gamma_le : G ⧸ Γ' → G ⧸ Γ)
    (?_ : Set.BijOn _ (cosetCount Γ' Γ' Γ' g h d) (cosetCount Γ Γ Γ g h d)))
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl, hxd⟩
    exact ⟨x, doubleCoset_subset_of_le hR.gamma_le hR.gamma_le g hx,
      Subgroup.quotientMapOfLE_apply_mk hR.gamma_le x,
      doubleCoset_subset_of_le hR.gamma_le hR.gamma_le h hxd⟩
  · rintro _ ⟨x, hx, rfl, -⟩ _ ⟨y, hy, rfl, -⟩ e
    rw [Subgroup.quotientMapOfLE_apply_mk hR.gamma_le x,
      Subgroup.quotientMapOfLE_apply_mk hR.gamma_le y, QuotientGroup.eq] at e
    have hx' := hR.doubleCoset_subset_delta' hg hx
    have hy' := hR.doubleCoset_subset_delta' hg hy
    exact QuotientGroup.eq.mpr (hR.cancel x hx' _ e (by rw [mul_inv_cancel_left]; exact hy'))
  · rintro _ ⟨x, hx, rfl, hxd⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp (hR.doubleCoset_subset g hg hx)
    have hag : a * g ∈ doubleCoset g (Γ' : Set G) Γ' :=
      mem_doubleCoset.mpr ⟨a, ha, 1, one_mem _, by rw [mul_one]⟩
    have hag' : a * g ∈ Δ' := mul_mem (hR.gamma'_le ha) hg
    have hm : (a * g)⁻¹ * d ∈ doubleCoset h (Γ : Set G) Γ := by
      have := mul_mem_doubleCoset_of_mem_left hb hxd
      simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using this
    refine ⟨((a * g : G) : G ⧸ Γ'), ⟨a * g, hag, rfl, hR.mem_doubleCoset_of_mem hag' hh hd hm⟩, ?_⟩
    rw [Subgroup.quotientMapOfLE_apply_mk hR.gamma_le (a * g), QuotientGroup.eq]
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, SetLike.mem_coe] using hb

/-! ### The ring isomorphism -/

variable (R : Type*) [Semiring R]

/-- The underlying finitely supported function of an element of a Hecke coset module. -/
def toFinsupp {Δ₀ : Submonoid G} {H : Subgroup G} (f : 𝕋 Δ₀ H R) : HeckeCoset Δ₀ H H →₀ R := f

/-- An element of a Hecke coset module from a finitely supported function. -/
def ofFinsupp {Δ₀ : Submonoid G} {H : Subgroup G} (f : HeckeCoset Δ₀ H H →₀ R) : 𝕋 Δ₀ H R := f

omit hR in
@[simp] lemma ofFinsupp_apply {Δ₀ : Submonoid G} {H : Subgroup G} (f : HeckeCoset Δ₀ H H →₀ R)
    (D : HeckeCoset Δ₀ H H) : ofFinsupp R f D = f D := rfl

omit hR in
@[simp] lemma toFinsupp_apply {Δ₀ : Submonoid G} {H : Subgroup G} (f : 𝕋 Δ₀ H R)
    (D : HeckeCoset Δ₀ H H) : toFinsupp R f D = f D := rfl

/-- The comparison map on Hecke rings: `Σ c_D [D] ↦ Σ c_D [cosetEquiv D]`. -/
def ringMap (f : 𝕋 Δ' Γ' R) : 𝕋 Δ Γ R :=
  ofFinsupp R (Finsupp.equivMapDomain hR.cosetEquiv (toFinsupp R f))

lemma ringMap_apply_cosetEquiv (f : 𝕋 Δ' Γ' R) (D : HeckeCoset Δ' Γ' Γ') :
    hR.ringMap R f (hR.cosetEquiv D) = f D := by
  rw [ringMap, ofFinsupp_apply, Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply,
    toFinsupp_apply]

lemma ringMap_ext {f g : 𝕋 Δ Γ R} (h : ∀ D : HeckeCoset Δ' Γ' Γ', f (hR.cosetEquiv D) =
    g (hR.cosetEquiv D)) : f = g := by
  refine DFunLike.ext _ _ fun E ↦ ?_
  rw [← hR.cosetEquiv.apply_symm_apply E]
  exact h _

lemma ringMap_single (D : HeckeCoset Δ' Γ' Γ') (a : R) :
    hR.ringMap R (HeckeCosetModule.single R D a) =
      HeckeCosetModule.single R (hR.cosetEquiv D) a := by
  classical
  refine hR.ringMap_ext R fun E ↦ ?_
  rw [ringMap_apply_cosetEquiv, HeckeCosetModule.single_apply, HeckeCosetModule.single_apply]
  simp only [hR.cosetEquiv.injective.eq_iff]

lemma ringMap_add (f g : 𝕋 Δ' Γ' R) :
    hR.ringMap R (f + g) = hR.ringMap R f + hR.ringMap R g := by
  refine hR.ringMap_ext R fun E ↦ ?_
  rw [ringMap_apply_cosetEquiv, HeckeCosetModule.add_apply, HeckeCosetModule.add_apply,
    ringMap_apply_cosetEquiv, ringMap_apply_cosetEquiv]

lemma ringMap_zero : hR.ringMap R 0 = 0 := by
  refine hR.ringMap_ext R fun E ↦ ?_
  rw [ringMap_apply_cosetEquiv, HeckeCosetModule.zero_apply, HeckeCosetModule.zero_apply]

lemma ringMap_smul (a : R) (f : 𝕋 Δ' Γ' R) : hR.ringMap R (a • f) = a • hR.ringMap R f := by
  refine hR.ringMap_ext R fun E ↦ ?_
  rw [ringMap_apply_cosetEquiv, HeckeCosetModule.smul_apply, HeckeCosetModule.smul_apply,
    ringMap_apply_cosetEquiv]

variable [IsHeckeTriple Δ Γ Γ] [IsHeckeTriple Δ' Γ' Γ']

/-- The structure constants correspond. -/
lemma ringMap_structureConstants (D₁ D₂ : HeckeCoset Δ' Γ' Γ') :
    hR.ringMap R (HeckeCosetModule.structureConstants R Γ' Γ' Γ' D₁.rep D₂.rep) =
      HeckeCosetModule.structureConstants R Γ Γ Γ (hR.cosetEquiv D₁).rep
        (hR.cosetEquiv D₂).rep := by
  refine hR.ringMap_ext R fun E ↦ ?_
  rw [ringMap_apply_cosetEquiv, HeckeCosetModule.structureConstants_apply,
    HeckeCosetModule.structureConstants_apply]
  congr 1
  have hfin (x : Δ') : Finite (DecompQuotient Γ Γ ((x : Δ') : G)) :=
    inferInstanceAs (Finite (DecompQuotient Γ Γ ((Submonoid.inclusion hR.delta_le x : Δ) : G)))
  have := hfin D₁.rep
  have := hfin D₂.rep
  rw [hR.multiplicity_eq D₁.rep.2 D₂.rep.2 E.rep.2,
    multiplicity_doubleCoset_congr _ _ (hR.cosetEquiv_rep_mem E),
    multiplicity_doubleCoset_congr_second _ _ _ _ _ (hR.cosetEquiv_rep_mem D₂)]
  exact (multiplicity_congr_first _ _ _ _ _ (hR.cosetEquiv_rep_mem D₁)).symm

lemma ringMap_mul (f g : 𝕋 Δ' Γ' R) :
    hR.ringMap R (f * g) = hR.ringMap R f * hR.ringMap R g := by
  induction f using HeckeCosetModule.induction_linear with
  | h0 => rw [MulZeroClass.zero_mul, ringMap_zero, MulZeroClass.zero_mul]
  | hadd f₁ f₂ h₁ h₂ => rw [right_distrib, ringMap_add, h₁, h₂, ringMap_add, right_distrib]
  | hsingle D₁ a =>
    induction g using HeckeCosetModule.induction_linear with
    | h0 => rw [MulZeroClass.mul_zero, ringMap_zero, MulZeroClass.mul_zero]
    | hadd g₁ g₂ h₁ h₂ => rw [left_distrib, ringMap_add, h₁, h₂, ringMap_add, left_distrib]
    | hsingle D₂ b =>
      rw [HeckeCosetModule.single_mul_single, ringMap_single, ringMap_single,
        HeckeCosetModule.single_mul_single, ringMap_smul, ringMap_smul,
        hR.ringMap_structureConstants R D₁ D₂]

/-- **The Hecke rings of `(Γ', Δ')` and `(Γ, Δ)` are isomorphic** under `Γ' g Γ' ↦ Γ g Γ`. -/
def heckeRingEquiv : 𝕋 Δ' Γ' R ≃+* 𝕋 Δ Γ R where
  toFun := hR.ringMap R
  invFun f := ofFinsupp R (Finsupp.equivMapDomain hR.cosetEquiv.symm (toFinsupp R f))
  left_inv f := by
    refine DFunLike.ext _ _ fun E ↦ ?_
    rw [ofFinsupp_apply, Finsupp.equivMapDomain_apply, Equiv.symm_symm, toFinsupp_apply,
      ringMap_apply_cosetEquiv]
  right_inv f := by
    refine hR.ringMap_ext R fun E ↦ ?_
    rw [ringMap_apply_cosetEquiv, ofFinsupp_apply, Finsupp.equivMapDomain_apply,
      Equiv.symm_symm, toFinsupp_apply]
  map_mul' := hR.ringMap_mul R
  map_add' := hR.ringMap_add R

lemma heckeRingEquiv_single (D : HeckeCoset Δ' Γ' Γ') (a : R) :
    hR.heckeRingEquiv R (HeckeCosetModule.single R D a) =
      HeckeCosetModule.single R (hR.cosetEquiv D) a :=
  hR.ringMap_single R D a

end IsHeckeRestriction

end Abstract

/-! ### Theorem 4.5.18 (1) -/

open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2
open ModularFormsKB.Miyake.Wave7 ModularFormsKB.Miyake.Wave8

variable {N : ℕ} [NeZero N]

/-- `(Γ₁(N), Δ₁(N))` is a restriction of `(Γ₀(N), Δ₀(N))` in the sense of
`IsHeckeRestriction`. -/
theorem isHeckeRestriction_gamma1 :
    IsHeckeRestriction (Delta0 N) (Delta1 N) (gamma0Q N) (gamma1Q N) where
  delta_le := Delta1_le_Delta0
  gamma_le := gamma1Q_le_gamma0Q
  gamma'_le := gamma1Q_le_delta1
  cancel := fun _ hx _ hγ h ↦ mem_gamma1Q_of_mul_mem_delta1 hx hγ h
  doubleCoset_subset := fun _ hg ↦ doubleCoset_gamma0_subset_gamma1_gamma0 hg
  exists_mem := fun _ hx ↦ exists_mem_delta1_mem_doubleCoset hx

/-- **Miyake, Theorem 4.5.18 (1)**: the Hecke rings `R(Γ₁(N), Δ₁(N))` and `R(Γ₀(N), Δ₀(N))`
(coefficients in any semiring `R`) are isomorphic under `Γ₁(N) α Γ₁(N) ↦ Γ₀(N) α Γ₀(N)`
(`heckeRingGamma1EquivGamma0_single`). -/
@[kb "miyake1989" "Theorem 4.5.18 (1), p. 151 (ring isomorphism)"]
def heckeRingGamma1EquivGamma0 (R : Type*) [Semiring R] :
    𝕋 (Delta1 N) (gamma1Q N) R ≃+* 𝕋 (Delta0 N) (gamma0Q N) R :=
  isHeckeRestriction_gamma1.heckeRingEquiv R

/-- **Miyake, Theorem 4.5.18 (1)**, on basis elements: `[Γ₁(N) α Γ₁(N)] ↦ [Γ₀(N) α Γ₀(N)]`. -/
@[kb "miyake1989" "Theorem 4.5.18 (1), p. 151 (ring isomorphism on double cosets)"]
theorem heckeRingGamma1EquivGamma0_single (R : Type*) [Semiring R] (α : Delta1 N) (a : R) :
    heckeRingGamma1EquivGamma0 R
        (HeckeCosetModule.single R (HeckeCoset.mk (gamma1Q N) (gamma1Q N) α) a) =
      HeckeCosetModule.single R (HeckeCoset.mk (gamma0Q N) (gamma0Q N)
        ⟨(α : GL (Fin 2) ℚ), Delta1_le_Delta0 α.2⟩) a :=
  isHeckeRestriction_gamma1.heckeRingEquiv_single R _ a

end ModularFormsKB.Miyake.Wave12
