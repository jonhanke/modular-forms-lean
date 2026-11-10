import TauCeti.NumberTheory.HeckeRing.Associativity
import TauCeti.NumberTheory.HeckeRing.Multiplicity.Equiv
import TauCeti.NumberTheory.HeckeRing.LinearExtension
import TauCeti.NumberTheory.HeckeRing.One
import ModularFormsKB.Citation
/-!
# Miyake, Lemma 2.7.5: the Hecke algebra of a smaller semigroup is a subalgebra

Miyake, *Modular Forms* (Springer 1989), §2.7, p. 72, Lemma 2.7.5.

Miyake's Hecke algebra `ℛ_K(Γ, Δ)` (free `K`-module on the double cosets `ΓαΓ`, `α ∈ Δ`) is
Mathlib's `HeckeRing Δ Γ K` (notation `𝕋 Δ Γ K`), with the ring structure of Tau Ceti
(`TauCeti/NumberTheory/HeckeRing/`: Shimura's product through the multiplicities
`HeckeCosetModule.multiplicity`). For `Δ ⊆ Δ'` the "natural correspondence" sends the basis
element `ΓαΓ` of `𝕋 Δ Γ K` to the same double coset in `𝕋 Δ' Γ K`
(Tau Ceti's `HeckeCoset.map`, extended linearly by `Finsupp.mapDomain`).

Lemma 2.7.5: this map is an injective ring homomorphism (`heckeRingInclusion`,
`heckeRingInclusion_injective`). The multiplicities only involve the double cosets as subsets of
`G`, not the semigroup. This is the "missing lemma" of wave 2A.
-/

open scoped Pointwise

noncomputable section

namespace ModularFormsKB.Miyake

open HeckeCosetModule

variable {G : Type*} [Group G] {Δ Δ' : Submonoid G} {Γ : Subgroup G} (R : Type*) [CommRing R]

open DoubleCoset in
/-- Shimura's multiplicity as a count of left cosets `xΓ₂` inside `Γ₁gΓ₂`. -/
private lemma multiplicity_eq_card_cosets {Γ₁ Γ₂ Γ₃ : Subgroup G} (g h d : G)
    [Finite (DecompQuotient Γ₁ Γ₂ g)] [Finite (DecompQuotient Γ₂ Γ₃ h)] :
    multiplicity Γ₁ Γ₂ Γ₃ g h d =
      Nat.card {y : G ⧸ Γ₂ | ∃ x : G, x ∈ doubleCoset g Γ₁ Γ₂ ∧ (x : G ⧸ Γ₂) = y ∧
        x⁻¹ * d ∈ doubleCoset h Γ₂ Γ₃} := by
  rw [multiplicity_eq_card_filter]
  refine Nat.card_congr (Equiv.ofBijective
    (fun i => ⟨((i.1.out : G) * g : G ⧸ Γ₂), (i.1.out : G) * g, ?_, rfl, i.2⟩) ⟨?_, ?_⟩)
  · exact mem_doubleCoset.mpr ⟨i.1.out, i.1.out.2, 1, Γ₂.one_mem, by simp⟩
  · intro i j hij
    exact Subtype.ext (mk_out_mul_injective Γ₁ Γ₂ g (congrArg Subtype.val hij))
  · rintro ⟨y, x, hx, rfl, hxd⟩
    rw [doubleCoset_eq_iUnion_leftCosets, Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    rw [mem_leftCoset_iff] at hi
    have hi' : ((i.out : G) * g)⁻¹ * x ∈ Γ₂ := hi
    refine ⟨⟨i, ?_⟩, Subtype.ext ?_⟩
    · obtain ⟨k, hk, l, hl, e⟩ := mem_doubleCoset.mp hxd
      refine mem_doubleCoset.mpr ⟨_ * k, Γ₂.mul_mem hi' hk, l, hl, ?_⟩
      calc ((i.out : G) * g)⁻¹ * d = (((i.out : G) * g)⁻¹ * x) * (x⁻¹ * d) := by group
        _ = _ := by rw [e]; group
    · exact QuotientGroup.eq.mpr hi'

open DoubleCoset in
/-- Shimura's multiplicity depends on its first input only through its double coset. -/
private lemma multiplicity_doubleCoset_congr_first {Γ₁ Γ₂ Γ₃ : Subgroup G} {g g' : G} (h d : G)
    [Finite (DecompQuotient Γ₁ Γ₂ g)] [Finite (DecompQuotient Γ₁ Γ₂ g')]
    [Finite (DecompQuotient Γ₂ Γ₃ h)] (hg : g' ∈ doubleCoset g Γ₁ Γ₂) :
    multiplicity Γ₁ Γ₂ Γ₃ g' h d = multiplicity Γ₁ Γ₂ Γ₃ g h d := by
  rw [multiplicity_eq_card_cosets, multiplicity_eq_card_cosets, doubleCoset_eq_of_mem hg]

open DoubleCoset in
private lemma multiplicity_congr_all {Γ₁ Γ₂ Γ₃ : Subgroup G} {g g' h h' d d' : G}
    [Finite (DecompQuotient Γ₁ Γ₂ g)] [Finite (DecompQuotient Γ₁ Γ₂ g')]
    [Finite (DecompQuotient Γ₂ Γ₃ h)] [Finite (DecompQuotient Γ₂ Γ₃ h')]
    (hg : g' ∈ doubleCoset g Γ₁ Γ₂) (hh : h' ∈ doubleCoset h Γ₂ Γ₃)
    (hd : d' ∈ doubleCoset d Γ₁ Γ₃) :
    multiplicity Γ₁ Γ₂ Γ₃ g' h' d' = multiplicity Γ₁ Γ₂ Γ₃ g h d := by
  rw [multiplicity_doubleCoset_congr _ _ hd, multiplicity_doubleCoset_congr_second Γ₁ Γ₂ Γ₃ g' d hh,
    multiplicity_doubleCoset_congr_first _ _ hg]

section Incl

variable (hΔ : Δ ≤ Δ')

private lemma map_injective' :
    Function.Injective (HeckeCoset.map (H₁ := Γ) (H₂ := Γ) hΔ le_rfl le_rfl) := by
  intro D E h
  induction D using HeckeCoset.induction with | h a =>
  induction E using HeckeCoset.induction with | h b =>
  simpa [HeckeCoset.eq_iff] using h

private lemma toSet_map (D : HeckeCoset Δ Γ Γ) :
    (HeckeCoset.map hΔ le_rfl le_rfl D).toSet = D.toSet := by
  induction D using HeckeCoset.induction with | h a =>
  simp

/-- The representative of the image coset lies in the double coset of the original one. -/
private lemma rep_map_mem (D : HeckeCoset Δ Γ Γ) :
    (((HeckeCoset.map hΔ le_rfl le_rfl D).rep : Δ') : G) ∈
      DoubleCoset.doubleCoset ((D.rep : Δ) : G) Γ Γ := by
  have h := HeckeCoset.rep_mem (HeckeCoset.map hΔ le_rfl le_rfl D)
  rwa [toSet_map, HeckeCoset.toSet_eq_doubleCoset_rep] at h

/-- The linear map underlying the inclusion. -/
private def inclLin : HeckeRing Δ Γ R →ₗ[R] HeckeRing Δ' Γ R :=
  Finsupp.lmapDomain R R (HeckeCoset.map (H₁ := Γ) (H₂ := Γ) hΔ le_rfl le_rfl)

private lemma inclLin_single (D : HeckeCoset Δ Γ Γ) (r : R) :
    inclLin R hΔ (single R D r) = single R (HeckeCoset.map hΔ le_rfl le_rfl D) r :=
  Finsupp.mapDomain_single

private lemma inclLin_injective : Function.Injective (inclLin (Γ := Γ) R hΔ) :=
  Finsupp.mapDomain_injective (map_injective' (Γ := Γ) hΔ)

private lemma inclLin_structureConstants [IsHeckeTriple Δ Γ Γ] [IsHeckeTriple Δ' Γ Γ]
    (D₁ D₂ : HeckeCoset Δ Γ Γ) :
    inclLin R hΔ (structureConstants R Γ Γ Γ D₁.rep D₂.rep) =
      structureConstants R Γ Γ Γ (HeckeCoset.map hΔ le_rfl le_rfl D₁).rep
        (HeckeCoset.map hΔ le_rfl le_rfl D₂).rep := by
  have hΓ : Γ.toSubmonoid ≤ Δ := IsHeckeTriple.left_le (H₂ := Γ)
  refine Finsupp.ext fun E => ?_
  by_cases hE : ∃ D, HeckeCoset.map hΔ le_rfl le_rfl D = E
  · obtain ⟨D, rfl⟩ := hE
    refine (Finsupp.mapDomain_apply_of_injective (map_injective' (Γ := Γ) hΔ)
      (structureConstants R Γ Γ Γ D₁.rep D₂.rep : HeckeCoset Δ Γ Γ →₀ R) D).trans ?_
    exact congrArg (fun n : ℕ => (n : R)) (multiplicity_congr_all (rep_map_mem hΔ D₁)
      (rep_map_mem hΔ D₂) (rep_map_mem hΔ D)).symm
  · push Not at hE
    refine (Finsupp.mapDomain_of_notMem_range
      (structureConstants R Γ Γ Γ D₁.rep D₂.rep : HeckeCoset Δ Γ Γ →₀ R) E
      (by simpa [Set.mem_range] using hE)).trans ?_
    symm
    have h0 : DoubleCoset.multiplicity Γ Γ Γ (((HeckeCoset.map hΔ le_rfl le_rfl D₁).rep : Δ') : G)
        (((HeckeCoset.map hΔ le_rfl le_rfl D₂).rep : Δ') : G) ((E.rep : Δ') : G) = 0 := by
      by_contra hne
      rw [multiplicity_congr_all (rep_map_mem hΔ D₁) (rep_map_mem hΔ D₂)
        (DoubleCoset.mem_doubleCoset_self Γ Γ _)] at hne
      obtain ⟨y, hy, k, hk, hE'⟩ :=
        DoubleCoset.mem_doubleCoset.mp (DoubleCoset.multiplicity_ne_zero_iff.mp hne)
      obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hy
      have hx : ((E.rep : Δ') : G) ∈ Δ := by
        rw [hE']
        exact Δ.mul_mem (Δ.mul_mem (Δ.mul_mem (Δ.mul_mem (hΓ ha) D₁.rep.2) (hΓ hb))
          D₂.rep.2) (hΓ hk)
      refine hE (HeckeCoset.mk Γ Γ ⟨_, hx⟩) ?_
      rw [HeckeCoset.map_mk]
      exact (E.mk_rep : HeckeCoset.mk Γ Γ E.rep = E)
    exact (congrArg (fun n : ℕ => (n : R)) h0).trans (Nat.cast_zero)

private lemma smul_mul_assoc' [IsHeckeTriple Δ' Γ Γ] (r : R) (x y : 𝕋 Δ' Γ R) :
    (r • x) * y = r • (x * y) := by
  induction x using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd x₁ x₂ h₁ h₂ => rw [smul_add, _root_.add_mul, _root_.add_mul, smul_add, h₁, h₂]
  | hsingle D₁ a =>
    induction y using HeckeCosetModule.induction_linear with
    | h0 => simp
    | hadd y₁ y₂ h₁ h₂ => rw [_root_.mul_add, _root_.mul_add, smul_add, h₁, h₂]
    | hsingle D₂ b =>
      rw [show r • single R D₁ a = single R D₁ (r * a) from Finsupp.smul_single _ _ _,
        single_mul_single, single_mul_single, mul_smul]

private lemma mul_smul_comm' [IsHeckeTriple Δ' Γ Γ] (r : R) (x y : 𝕋 Δ' Γ R) :
    x * (r • y) = r • (x * y) := by
  induction x using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd x₁ x₂ h₁ h₂ => rw [_root_.add_mul, h₁, h₂, _root_.add_mul, smul_add]
  | hsingle D₁ a =>
    induction y using HeckeCosetModule.induction_linear with
    | h0 => simp
    | hadd y₁ y₂ h₁ h₂ => rw [smul_add, _root_.mul_add, h₁, h₂, _root_.mul_add, smul_add]
    | hsingle D₂ b =>
      rw [show r • single R D₂ b = single R D₂ (r * b) from Finsupp.smul_single _ _ _,
        single_mul_single, single_mul_single, mul_smul, smul_comm a r]

end Incl

/-- The natural correspondence `𝕋 Δ Γ R → 𝕋 Δ' Γ R` for `Δ ≤ Δ'`, `ΓαΓ ↦ ΓαΓ`, as a ring
homomorphism (Miyake, Lemma 2.7.5). -/
@[kb "miyake1989" "Lemma 2.7.5, p. 72"]
def heckeRingInclusion (hΔ : Δ ≤ Δ') [IsHeckeTriple Δ Γ Γ] [IsHeckeTriple Δ' Γ Γ] :
    HeckeRing Δ Γ R →+* HeckeRing Δ' Γ R where
  toFun := inclLin R hΔ
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    change inclLin R hΔ (single R 1 1) = single R 1 1
    rw [inclLin_single]
    rfl
  map_mul' := by
    have : IsScalarTower R (𝕋 Δ' Γ R) (𝕋 Δ' Γ R) := ⟨smul_mul_assoc' R⟩
    have : SMulCommClass R (𝕋 Δ' Γ R) (𝕋 Δ' Γ R) := ⟨fun r x y => by
      rw [smul_eq_mul, smul_eq_mul, mul_smul_comm' R]⟩
    refine LinearMap.map_mul_of_basis (Δ := Δ) (H := Γ) (A := 𝕋 Δ' Γ R) (inclLin R hΔ)
      (fun D₁ D₂ => ?_)
    rw [single_mul_single, one_smul, one_smul, inclLin_structureConstants, inclLin_single,
      inclLin_single, single_mul_single, one_smul, one_smul]

/-- The natural correspondence sends the basis element `ΓαΓ` to `ΓαΓ`. -/
@[kb "miyake1989" "Lemma 2.7.5, p. 72"]
theorem heckeRingInclusion_single (hΔ : Δ ≤ Δ') [IsHeckeTriple Δ Γ Γ] [IsHeckeTriple Δ' Γ Γ]
    (D : HeckeCoset Δ Γ Γ) (r : R) :
    heckeRingInclusion R hΔ (single R D r) =
      single R (HeckeCoset.map hΔ le_rfl le_rfl D) r :=
  inclLin_single R hΔ D r

/-- **Miyake, Lemma 2.7.5.** If `Δ ⊆ Δ'`, then `ℛ_K(Γ, Δ)` is a subalgebra of `ℛ_K(Γ, Δ')`
under the natural correspondence: the correspondence is an injective ring homomorphism. -/
@[kb "miyake1989" "Lemma 2.7.5, p. 72"]
theorem heckeRingInclusion_injective (hΔ : Δ ≤ Δ') [IsHeckeTriple Δ Γ Γ]
    [IsHeckeTriple Δ' Γ Γ] : Function.Injective (heckeRingInclusion (Γ := Γ) R hΔ) :=
  fun _ _ h => inclLin_injective (Γ := Γ) R hΔ h

end ModularFormsKB.Miyake
