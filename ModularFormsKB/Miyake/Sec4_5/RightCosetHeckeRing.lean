import ModularFormsKB.Miyake.Wave12.HeckeRingIso
import ModularFormsKB.Citation
/-!
# Miyake, Theorem 4.5.18 (1), for the Hecke ring built from right cosets

Miyake, *Modular Forms* (Springer 1989), Theorem 4.5.18 (1), p. 151; Shimura, *Introduction to
the arithmetic theory of automorphic functions* (1971), §3.1.

Tau Ceti's Hecke ring `𝕋 Δ H R` counts **left** cosets `x H`. Miyake's Hecke ring `R(Γ, Δ)` is
built from **right** cosets `Γ αᵢ`: the structure constants of
`(Γ α Γ)(Γ β Γ) = Σ m(α, β; ξ) Γ ξ Γ` are `m(α, β; ξ) = #{(i, j) : Γ αᵢ βⱼ = Γ ξ}`, equivalently
the number of right cosets `Γ y ⊆ Γ β Γ` with `ξ y⁻¹ ∈ Γ α Γ`.

## Construction

We model Miyake's ring through the opposite group `Gᵐᵒᵖ`. A right coset `Γ y` of `G` is the left
coset `op y · Γ.op` in `Gᵐᵒᵖ`, so Tau Ceti's left-coset count in `Gᵐᵒᵖ` is Miyake's right-coset
count in `G` (`multiplicity_op_eq_natCard_rightCosetCount`). The product in `𝕋 Δ.op Γ.op R` of
`[Γ.op (op β) Γ.op]` and `[Γ.op (op α) Γ.op]` has the Miyake count `m(α, β; ξ)` for
`[Γ ξ Γ]`; to restore the order of the factors we take the opposite ring, so
`RightHeckeRing Δ Γ R = (𝕋 Δ.op Γ.op R)ᵐᵒᵖ` has `[Γ α Γ] · [Γ β Γ] = Σ_ξ m(α, β; ξ) [Γ ξ Γ]`
with Miyake's right-coset `m`. (The order reversal coming from `ᵐᵒᵖ` is exactly what makes
Miyake's `α · β` correspond to `(op β) · (op α)`.)

The comparison of Wave 12 (`IsHeckeRestriction`) is transported to `Gᵐᵒᵖ`: right cancellation
becomes left cancellation in `G`, and the left-coset form of (4.5.42) in `Gᵐᵒᵖ` becomes Miyake's
actual right-coset form `Γ₀ α Γ₀ = Γ₀ α Γ₁` (`doubleCoset_op`).

This closes the loose end LE-MF-0224 (Wave 12 proved the theorem for Tau Ceti's left-coset ring).

## Main results
* `RightHeckeRing`, `isHeckeTriple_op`: Miyake's ring and its Hecke triple.
* `multiplicity_op_eq_natCard_rightCosetCount`: Miyake's count of right cosets.
* `isHeckeRestriction_op_gamma1`: the comparison hypotheses for `(Γ₁(N), Δ₁(N)) ⊆ (Γ₀(N), Δ₀(N))`.
* `rightHeckeRingGamma1EquivGamma0` (**Theorem 4.5.18 (1)**).
-/

open DoubleCoset MulOpposite
open scoped Pointwise HeckeCosetModule

noncomputable section

namespace ModularFormsKB.Miyake.Sec4_5

open ModularFormsKB.Miyake.Wave12 ModularFormsKB.Miyake.Wave8 ModularFormsKB.Miyake.Wave7
open HeckeRing.GL2 CongruenceSubgroup

section General

variable {G : Type*} [Group G]

/-- Double cosets in the opposite group, membership form. -/
theorem mem_doubleCoset_op {H K : Subgroup G} {g x : G} :
    op x ∈ doubleCoset (op g) (H.op : Set Gᵐᵒᵖ) K.op ↔
      x ∈ doubleCoset g (K : Set G) H := by
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, he⟩ := mem_doubleCoset.mp h
    refine mem_doubleCoset.mpr ⟨b.unop, hb, a.unop, ha, ?_⟩
    have := congrArg unop he
    simpa [mul_assoc] using this
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp h
    refine mem_doubleCoset.mpr ⟨op b, hb, op a, ha, ?_⟩
    simp [mul_assoc]

/-- Double cosets in the opposite group: `Γ.op (op g) Γ'.op = op '' (Γ' g Γ)` (the sides swap). -/
theorem doubleCoset_op (H K : Subgroup G) (g : G) :
    doubleCoset (op g) (H.op : Set Gᵐᵒᵖ) K.op = op '' doubleCoset g (K : Set G) H := by
  ext x
  obtain ⟨y, rfl⟩ := op_surjective x
  rw [mem_doubleCoset_op]
  simp

theorem commensurable_op_iff {H K : Subgroup G} :
    Subgroup.Commensurable H.op K.op ↔ Subgroup.Commensurable H K := by
  have h : ∀ L : Subgroup G, L.op = L.map (MulEquiv.inv' G).toMonoidHom := by
    intro L
    ext x
    obtain ⟨y, rfl⟩ := op_surjective x
    simp only [Subgroup.mem_op, unop_op, Subgroup.mem_map]
    constructor
    · intro hy
      exact ⟨y⁻¹, inv_mem hy, by simp [MulEquiv.inv']⟩
    · rintro ⟨z, hz, hzy⟩
      have : z⁻¹ = y := by
        have := congrArg unop hzy
        simpa [MulEquiv.inv'] using this
      rw [← this]; exact inv_mem hz
  rw [h, h]
  exact Subgroup.Commensurable.map_injective_iff (MulEquiv.inv' G).injective

theorem conj_op_smul (g : G) (H : Subgroup G) :
    MulAut.conj (op g) • H.op = (MulAut.conj g⁻¹ • H).op := by
  ext x
  obtain ⟨y, rfl⟩ := op_surjective x
  simp only [Subgroup.mem_op, unop_op, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def, mul_assoc]

/-- A Hecke triple stays a Hecke triple in the opposite group (the commensurator of `H.op` is the
op of the commensurator of `H`). -/
instance isHeckeTriple_op {Δ : Submonoid G} {H₁ H₂ : Subgroup G} [h : IsHeckeTriple Δ H₁ H₂] :
    IsHeckeTriple Δ.op H₁.op H₂.op where
  left_le := fun _ hx ↦ h.left_le hx
  right_le := fun _ hx ↦ h.right_le hx
  commensurable := commensurable_op_iff.mpr h.commensurable
  le_commensurator_right := by
    intro x hx
    obtain ⟨g, rfl⟩ := op_surjective x
    have hg : g ∈ Subgroup.Commensurable.commensurator H₂ := h.le_commensurator_right hx
    have := inv_mem hg
    show op g ∈ Subgroup.Commensurable.commensurator H₂.op
    rw [Subgroup.Commensurable.commensurator_mem_iff] at this ⊢
    rw [conj_op_smul]
    exact commensurable_op_iff.mpr this

/-- **Miyake's Hecke ring** `R(Γ, Δ)` with coefficients in `R`, built from right cosets `Γ α`:
the opposite ring of Tau Ceti's Hecke ring of `(Δ.op, Γ.op)` in the opposite group. Its product is
`[Γ α Γ] · [Γ β Γ] = Σ_ξ m(α, β; ξ) [Γ ξ Γ]` with `m` the right-coset count
(`multiplicity_op_eq_natCard_rightCosetCount`). -/
abbrev RightHeckeRing (Δ : Submonoid G) (Γ : Subgroup G) (R : Type*) [Semiring R]
    [IsHeckeTriple Δ.op Γ.op Γ.op] : Type _ :=
  (𝕋 Δ.op Γ.op R)ᵐᵒᵖ

/-- Miyake's right cosets: the right cosets `Γ y` (as left cosets `op y · Γ.op` in `Gᵐᵒᵖ`) with
`y ∈ Γ β Γ` and `ξ y⁻¹ ∈ Γ α Γ`. Their number is the structure constant `m(α, β; ξ)`. -/
def rightCosetCount (Γ : Subgroup G) (α β ξ : G) : Set (Gᵐᵒᵖ ⧸ Γ.op) :=
  {c | ∃ y ∈ doubleCoset β (Γ : Set G) Γ, ((op y : Gᵐᵒᵖ) : Gᵐᵒᵖ ⧸ Γ.op) = c ∧
    ξ * y⁻¹ ∈ doubleCoset α (Γ : Set G) Γ}

theorem cosetCount_op_eq (Γ : Subgroup G) (α β ξ : G) :
    cosetCount Γ.op Γ.op Γ.op (op β) (op α) (op ξ) = rightCosetCount Γ α β ξ := by
  ext c
  constructor
  · rintro ⟨x, hx, rfl, hxd⟩
    obtain ⟨y, rfl⟩ := op_surjective x
    refine ⟨y, ?_, rfl, ?_⟩
    · exact (mem_doubleCoset_op.mp hx)
    · have : op (ξ * y⁻¹) ∈ doubleCoset (op α) (Γ.op : Set Gᵐᵒᵖ) Γ.op := by
        simpa using hxd
      exact mem_doubleCoset_op.mp this
  · rintro ⟨y, hy, rfl, hd⟩
    refine ⟨op y, mem_doubleCoset_op.mpr hy, rfl, ?_⟩
    have := mem_doubleCoset_op.mpr hd
    simpa using this

/-- **Miyake's structure constants**: for `α, β ∈ Δ`, the multiplicity in the opposite group is
the number of right cosets `Γ y ⊆ Γ β Γ` with `ξ y⁻¹ ∈ Γ α Γ`. Hence the product of
`RightHeckeRing` is `[Γ α Γ] · [Γ β Γ] = Σ_ξ m(α, β; ξ) [Γ ξ Γ]` with Miyake's right-coset `m`. -/
theorem multiplicity_op_eq_natCard_rightCosetCount {Δ : Submonoid G} {Γ : Subgroup G}
    [IsHeckeTriple Δ Γ Γ] {α β : G} (hα : α ∈ Δ) (hβ : β ∈ Δ) (ξ : G) :
    DoubleCoset.multiplicity Γ.op Γ.op Γ.op (op β) (op α) (op ξ) =
      Nat.card (rightCosetCount Γ α β ξ) := by
  have key : ∀ g : Δ.op, Finite (DecompQuotient Γ.op Γ.op (g : Gᵐᵒᵖ)) :=
    fun g ↦ inferInstance
  have : Finite (DecompQuotient Γ.op Γ.op (op β)) := key ⟨op β, hβ⟩
  have : Finite (DecompQuotient Γ.op Γ.op (op α)) := key ⟨op α, hα⟩
  rw [multiplicity_eq_natCard_cosetCount, cosetCount_op_eq]

end General

/-! ### Theorem 4.5.18 (1) -/

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- Left cancellation: if `x ∈ Δ₁(N)`, `γ ∈ Γ₀(N)` and `γ x ∈ Δ₁(N)`, then `γ ∈ Γ₁(N)`. -/
theorem mem_gamma1Q_of_mul_mem_delta1' {x γ : GL (Fin 2) ℚ} (hx : x ∈ Delta1 N)
    (hγ : γ ∈ gamma0Q N) (hγx : γ * x ∈ Delta1 N) : γ ∈ gamma1Q N := by
  have hγ' : γ ∈ Delta0 N := gamma0Q_le_delta0 hγ
  have hx' : x ∈ Delta0 N := Delta1_le_Delta0 hx
  refine mem_gamma1Q_of_delta0UpperUnit_eq_one hγ hγ' ?_
  have h1 := delta0UpperUnit_eq_one_of_mem_delta1 hx
  have h2 := delta0UpperUnit_eq_one_of_mem_delta1 hγx
  have hm := upperUnit_mul hγ' hx'
  change upperUnit x hx' = 1 at h1
  change upperUnit (γ * x) (mul_mem hγ' hx') = 1 at h2
  rw [h2, h1, mul_one] at hm
  exact hm.symm

/-- The comparison hypotheses for `(Γ₁(N), Δ₁(N)) ⊆ (Γ₀(N), Δ₀(N))` in the opposite group. -/
theorem isHeckeRestriction_op_gamma1 :
    IsHeckeRestriction (Delta0 N).op (Delta1 N).op (gamma0Q N).op (gamma1Q N).op where
  delta_le := fun _ hx ↦ Delta1_le_Delta0 hx
  gamma_le := fun _ hx ↦ gamma1Q_le_gamma0Q hx
  gamma'_le := fun _ hx ↦ gamma1Q_le_delta1 hx
  cancel := fun _ hx _ hγ h ↦ mem_gamma1Q_of_mul_mem_delta1' hx hγ h
  doubleCoset_subset := by
    intro g hg
    obtain ⟨g, rfl⟩ := op_surjective g
    have hg' : g ∈ Delta1 N := hg
    rw [doubleCoset_op, doubleCoset_op, doubleCoset_gamma0_eq_gamma0_gamma1
      (Delta1_le_Delta0 hg')]
  exists_mem := by
    intro x hx
    obtain ⟨b, rfl⟩ := op_surjective x
    obtain ⟨α, hα, hm⟩ := exists_mem_delta1_mem_doubleCoset hx
    exact ⟨op α, hα, mem_doubleCoset_op.mpr hm⟩

/-- **Miyake, Theorem 4.5.18 (1)** for Miyake's right-coset Hecke rings: `R(Γ₁(N), Δ₁(N)) ≅
R(Γ₀(N), Δ₀(N))` under `Γ₁(N) α Γ₁(N) ↦ Γ₀(N) α Γ₀(N)`. -/
@[kb "miyake1989" "Theorem 4.5.18 (1), p. 151 (right-coset Hecke rings)"]
def rightHeckeRingGamma1EquivGamma0 (R : Type*) [Semiring R] :
    RightHeckeRing (Delta1 N) (gamma1Q N) R ≃+* RightHeckeRing (Delta0 N) (gamma0Q N) R :=
  (isHeckeRestriction_op_gamma1.heckeRingEquiv R).op

/-- On basis elements: `[Γ₁(N) α Γ₁(N)] ↦ [Γ₀(N) α Γ₀(N)]`. -/
theorem rightHeckeRingGamma1EquivGamma0_single (R : Type*) [Semiring R] {α : GL (Fin 2) ℚ}
    (hα : α ∈ Delta1 N) (a : R) :
    rightHeckeRingGamma1EquivGamma0 R
        (op (HeckeCosetModule.single R
          (HeckeCoset.mk (gamma1Q N).op (gamma1Q N).op (⟨op α, hα⟩ : (Delta1 N).op)) a)) =
      op (HeckeCosetModule.single R (HeckeCoset.mk (gamma0Q N).op (gamma0Q N).op
        (⟨op α, Delta1_le_Delta0 hα⟩ : (Delta0 N).op)) a) :=
  congrArg op (isHeckeRestriction_op_gamma1.heckeRingEquiv_single R _ a)

end ModularFormsKB.Miyake.Sec4_5
