import ModularFormsKB.Milne.Wave5.MultiplicationIsogeny
import ModularFormsKB.Milne.Ch11.TateModule
import ModularFormsKB.Milne.Ch12.VariableChangeEnd
import TauCeti.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.TensorProduct.Free
import ModularFormsKB.Citation
/-!
# Milne, Proposition 11.5: the Betti, `ℓ`-adic and tangent representations of `End(E)` over `ℂ`

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 11, pdf pp. 112–113.

Let `E` be an elliptic curve over `ℂ` and `A = End(E)`. Milne's proof writes `E = ℂ/Λ` and uses the canonical
identifications `H₁(E, ℤ) ≅ π₁(E, 0) ≅ Λ` (covering-space theory) and `ℂ ≅ Tgt₀(E)` (the differential of the
covering map `ℂ → E`). We formalize the proposition for the curve `E(Λ)` of a lattice `Λ` (Mathlib's `PeriodPair`), and then for every
elliptic curve over `ℂ` by transport along a change of variables `E ≅ E(Λ)` (`ComplexUniformization.exists_lattice`),
with these two identifications built in, as in Milne's proof:

* the endomorphism `f` lifts to `z ↦ ρ(f) z` on `ℂ` (wave 5, `Wave5.complexUniformization`); `ρ(f) ∈ ℂ` is the
  action of `f` on `Tgt₀(E) = ℂ` (`tangentRep`);
* `ρ_B(f)` is the action of `f` on `H₁(E, ℤ) = Λ`, multiplication by `ρ(f)` (`bettiRep`);
* `ρ_ℓ(f)` is the action of `f` on the Tate module `T_ℓ E` of the point group (`tateRep`, Section 11).

## Results

* `tateModule_equiv_tensor`: `Λ ⊗ ℤ_ℓ ≅ T_ℓ(ℂ/Λ)` (Milne: `Λ ⊗ ℤ/ℓᴺ = Λ/ℓᴺΛ ≅ ℓ⁻ᴺΛ/Λ = E_{ℓᴺ}`, in the limit).
* **Proposition 11.5** `proposition_11_5` (for `E(Λ)`), `proposition_11_5_general` (for every `E`): (a) `ρ_B ⊗ ℤ_ℓ ≅ ρ_ℓ` and (b) `ρ_B ⊗ ℂ ≅ ρ ⊕ ρ̄`, as representations
  of `End(E)`: there are linear isomorphisms intertwining the actions of every endomorphism.
-/

open TauCeti TauCeti.Isogeny TensorProduct
open scoped WeierstrassCurve ComplexConjugate

noncomputable section

namespace ModularFormsKB.Milne.Wave6

variable (L : PeriodPair)

/-! ### The torus `ℂ/Λ` as a group and its `ℓ`-power torsion -/

/-- The complex torus `ℂ/Λ` as an abelian group. -/
abbrev TorusGroup : Type := ℂ ⧸ L.lattice.toAddSubgroup

/-- The uniformization `ℂ/Λ → E(Λ)(ℂ)`, `z ↦ (℘(z), ℘'(z)/2)`, as a homomorphism of groups. -/
def torusPointHom : TorusGroup L →+ L.weierstrassCurve.toAffine.Point :=
  QuotientAddGroup.lift _ (AddMonoidHom.mk' L.weierstrassPoint weierstrassPoint_add)
    fun _ hz ↦ L.weierstrassPoint_of_mem hz

theorem torusPointHom_mk (z : ℂ) : torusPointHom L (z : TorusGroup L) = L.weierstrassPoint z := rfl

theorem bijective_torusPointHom : Function.Bijective (torusPointHom L) := by
  refine ⟨fun x y h ↦ ?_, fun P ↦ ?_⟩
  · induction x using QuotientAddGroup.induction_on with | H z => ?_
    induction y using QuotientAddGroup.induction_on with | H w => ?_
    rw [QuotientAddGroup.eq_iff_sub_mem]
    exact sub_mem_of_weierstrassPoint_eq h
  · obtain ⟨x, hx⟩ := surjective_torusPoint (L := L) P
    induction x using Quotient.inductionOn with | h z => exact ⟨(z : TorusGroup L), hx⟩

/-- The uniformization `ℂ/Λ ≅ E(Λ)(ℂ)` as an isomorphism of groups (Milne, Proposition 3.12). -/
def torusPointEquiv : TorusGroup L ≃+ L.weierstrassCurve.toAffine.Point :=
  AddEquiv.ofBijective (torusPointHom L) (bijective_torusPointHom L)

/-- Multiplication by `α` with `αΛ ⊆ Λ` on `ℂ/Λ`. -/
def torusMul (α : ℂ) (hα : ∀ x ∈ L.lattice, α * x ∈ L.lattice) : TorusGroup L →+ TorusGroup L :=
  QuotientAddGroup.map _ _ (AddMonoidHom.mulLeft α) fun x hx ↦ hα x hx

theorem torusMul_mk (α : ℂ) (hα : ∀ x ∈ L.lattice, α * x ∈ L.lattice) (z : ℂ) :
    torusMul L α hα (z : TorusGroup L) = ((α * z : ℂ) : TorusGroup L) := rfl

/-! ### `Λ ⊗ ℤ_ℓ ≅ T_ℓ(ℂ/Λ)` -/

section Tate

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

theorem pow_ne_zero_complex (n : ℕ) : ((ℓ : ℂ) ^ n) ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.2 hℓ.out.ne_zero)

/-- `λ ↦ λ/ℓⁿ mod Λ`, a point of order dividing `ℓⁿ`. -/
def latticeLevel (n : ℕ) : L.lattice →+ TateModuleLevel ℓ (TorusGroup L) n where
  toFun x := ⟨(((x : ℂ) / (ℓ : ℂ) ^ n : ℂ) : TorusGroup L), by
    rw [AddSubgroup.torsionBy.nsmul_iff, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    have : ((ℓ ^ n : ℕ) • ((x : ℂ) / (ℓ : ℂ) ^ n)) = x := by
      rw [nsmul_eq_mul]; push_cast; field_simp [pow_ne_zero_complex ℓ n]
    rw [this]; exact x.2⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [add_div]

theorem coe_latticeLevel (n : ℕ) (x : L.lattice) :
    ((latticeLevel L ℓ n x : TateModuleLevel ℓ (TorusGroup L) n) : TorusGroup L) =
      (((x : ℂ) / (ℓ : ℂ) ^ n : ℂ) : TorusGroup L) := rfl

theorem latticeLevel_compat (n : ℕ) :
    (tateModuleTransition ℓ (TorusGroup L) n).comp (latticeLevel L ℓ (n + 1)) = latticeLevel L ℓ n := by
  ext x
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, tateModuleTransition_apply, coe_latticeLevel]
  rw [← QuotientAddGroup.mk_nsmul]
  congr 1
  rw [nsmul_eq_mul, pow_succ]
  field_simp [pow_ne_zero_complex ℓ n, (Nat.cast_ne_zero.2 hℓ.out.ne_zero : (ℓ : ℂ) ≠ 0)]

/-- The map `Λ → T_ℓ(ℂ/Λ)`, `λ ↦ (λ/ℓⁿ mod Λ)ₙ`. -/
def latticeToTate : L.lattice →+ TateModule ℓ (TorusGroup L) :=
  TateModule.lift (latticeLevel L ℓ) (latticeLevel_compat L ℓ)

theorem proj_latticeToTate (n : ℕ) (x : L.lattice) :
    TateModule.proj n (latticeToTate L ℓ x) = latticeLevel L ℓ n x := rfl

/-- The `ℤ_ℓ`-linear extension `ℤ_ℓ ⊗ Λ → T_ℓ(ℂ/Λ)`. -/
def tensorToTate : ℤ_[ℓ] ⊗[ℤ] L.lattice →ₗ[ℤ_[ℓ]] TateModule ℓ (TorusGroup L) :=
  LinearMap.liftBaseChange ℤ_[ℓ] (latticeToTate L ℓ).toIntLinearMap

theorem tensorToTate_tmul (a : ℤ_[ℓ]) (x : L.lattice) :
    tensorToTate L ℓ (a ⊗ₜ x) = a • latticeToTate L ℓ x := by
  simp [tensorToTate]

/-- The two coordinates. -/
def coordToTate (a b : ℤ_[ℓ]) : TateModule ℓ (TorusGroup L) :=
  a • latticeToTate L ℓ (L.latticeBasis 0) + b • latticeToTate L ℓ (L.latticeBasis 1)

theorem coe_proj_coordToTate (a b : ℤ_[ℓ]) (n : ℕ) :
    ((TateModule.proj n (coordToTate L ℓ a b) : TateModuleLevel ℓ (TorusGroup L) n) : TorusGroup L) =
      ((((PadicInt.toZModPow n a).val * L.ω₁ + (PadicInt.toZModPow n b).val * L.ω₂) / (ℓ : ℂ) ^ n : ℂ) :
        TorusGroup L) := by
  simp only [coordToTate, map_add, TateModule.proj_smul, AddSubgroup.coe_add,
    TateModule.coe_zmod_smul, proj_latticeToTate, coe_latticeLevel, PeriodPair.latticeBasis_zero,
    PeriodPair.latticeBasis_one, ← QuotientAddGroup.mk_nsmul, ← QuotientAddGroup.mk_add, nsmul_eq_mul]
  congr 1
  ring

/-- If `(aω₁ + bω₂)/ℓⁿ ∈ Λ` with `a, b` integers then `ℓⁿ` divides `a` and `b`. -/
theorem dvd_of_mem_lattice {n : ℕ} {a b : ℤ} (h : ((a : ℂ) * L.ω₁ + b * L.ω₂) / (ℓ : ℂ) ^ n ∈ L.lattice) :
    ((ℓ ^ n : ℕ) : ℤ) ∣ a ∧ ((ℓ ^ n : ℕ) : ℤ) ∣ b := by
  set m : ℤ := ((ℓ ^ n : ℕ) : ℤ)
  have hm : m ≠ 0 := by simp [m, hℓ.out.ne_zero]
  have hq : ((((a : ℚ) / (m : ℚ) : ℚ) : ℂ) * L.ω₁ + (((b : ℚ) / (m : ℚ) : ℚ) : ℂ) * L.ω₂) =
      ((a : ℂ) * L.ω₁ + b * L.ω₂) / (ℓ : ℂ) ^ n := by
    simp only [m]; push_cast; field_simp [pow_ne_zero_complex ℓ n]
  rw [← hq, PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice] at h
  exact ⟨(Rat.den_div_intCast_eq_one_iff a m hm).1 h.1, (Rat.den_div_intCast_eq_one_iff b m hm).1 h.2⟩

theorem toZModPow_eq_zero_of_dvd {n : ℕ} {a : ℤ_[ℓ]}
    (h : ((ℓ ^ n : ℕ) : ℤ) ∣ ((PadicInt.toZModPow n a).val : ℤ)) : PadicInt.toZModPow n a = 0 := by
  rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow n a), ZMod.natCast_eq_zero_iff]
  exact_mod_cast h

theorem coordToTate_injective {a b : ℤ_[ℓ]} (h : coordToTate L ℓ a b = 0) : a = 0 ∧ b = 0 := by
  have key : ∀ n, PadicInt.toZModPow n a = 0 ∧ PadicInt.toZModPow n b = 0 := by
    intro n
    have h1 := congrArg (fun t ↦ ((TateModule.proj n t : TateModuleLevel ℓ (TorusGroup L) n) : TorusGroup L)) h
    simp only [coe_proj_coordToTate, map_zero, ZeroMemClass.coe_zero, QuotientAddGroup.eq_zero_iff] at h1
    have h2 := dvd_of_mem_lattice L ℓ (a := (PadicInt.toZModPow n a).val) (b := (PadicInt.toZModPow n b).val)
      (by push_cast; exact h1)
    exact ⟨toZModPow_eq_zero_of_dvd ℓ h2.1, toZModPow_eq_zero_of_dvd ℓ h2.2⟩
  exact ⟨PadicInt.ext_of_toZModPow.1 fun n ↦ by simp [(key n).1],
    PadicInt.ext_of_toZModPow.1 fun n ↦ by simp [(key n).2]⟩

theorem proj_coordToTate (a b : ℤ_[ℓ]) (n : ℕ) :
    TateModule.proj n (coordToTate L ℓ a b) =
      PadicInt.toZModPow n a • latticeLevel L ℓ n (L.latticeBasis 0) +
        PadicInt.toZModPow n b • latticeLevel L ℓ n (L.latticeBasis 1) := by
  simp [coordToTate, proj_latticeToTate]

theorem continuous_coordToTate : Continuous fun p : ℤ_[ℓ] × ℤ_[ℓ] ↦ coordToTate L ℓ p.1 p.2 := by
  refine TateModule.continuous_iff.2 fun n ↦ ?_
  have hc : Continuous fun p : ℤ_[ℓ] × ℤ_[ℓ] ↦ (PadicInt.toZModPow n p.1, PadicInt.toZModPow n p.2) :=
    ((PadicInt.continuous_toZModPow n).comp continuous_fst).prodMk
      ((PadicInt.continuous_toZModPow n).comp continuous_snd)
  have := (IsLocallyConstant.of_discrete (fun q : ZMod (ℓ ^ n) × ZMod (ℓ ^ n) ↦
    q.1 • latticeLevel L ℓ n (L.latticeBasis 0) + q.2 • latticeLevel L ℓ n (L.latticeBasis 1))).comp_continuous hc
  convert this using 1
  funext p
  simp [proj_coordToTate]

theorem coordToTate_surjective : Function.Surjective fun p : ℤ_[ℓ] × ℤ_[ℓ] ↦ coordToTate L ℓ p.1 p.2 := by
  refine TateModule.surjective_of_forall_surjective_proj (continuous_coordToTate L ℓ) fun n y ↦ ?_
  obtain ⟨y, hy⟩ := y
  induction y using QuotientAddGroup.induction_on with | H z => ?_
  rw [AddSubgroup.torsionBy.nsmul_iff, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at hy
  obtain ⟨m, k, hmk⟩ := PeriodPair.mem_lattice.1 hy
  refine ⟨((m : ℤ_[ℓ]), (k : ℤ_[ℓ])), Subtype.ext ?_⟩
  simp only [proj_coordToTate, map_intCast, Int.cast_smul_eq_zsmul, AddSubgroup.coe_add,
    AddSubgroup.coe_zsmul, coe_latticeLevel, PeriodPair.latticeBasis_zero, PeriodPair.latticeBasis_one,
    ← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_add]
  congr 1
  rw [nsmul_eq_mul] at hmk
  have hz : z = (m * L.ω₁ + k * L.ω₂) / (ℓ : ℂ) ^ n := by
    rw [hmk]; push_cast; field_simp [pow_ne_zero_complex ℓ n]
  rw [hz]; ring

/-- The basis of `A ⊗ Λ` coming from `ω₁, ω₂`. -/
abbrev tensorBasis (A : Type*) [CommRing A] : Module.Basis (Fin 2) A (A ⊗[ℤ] L.lattice) :=
  L.latticeBasis.baseChange A

/-- A linear map out of `A ⊗ Λ` in coordinates. -/
theorem apply_eq_coords {A N : Type*} [CommRing A] [AddCommGroup N] [Module A N]
    (F : A ⊗[ℤ] L.lattice →ₗ[A] N) (x : A ⊗[ℤ] L.lattice) :
    F x = (tensorBasis L A).repr x 0 • F (1 ⊗ₜ L.latticeBasis 0) +
      (tensorBasis L A).repr x 1 • F (1 ⊗ₜ L.latticeBasis 1) := by
  conv_lhs => rw [← (tensorBasis L A).sum_repr x]
  simp [Fin.sum_univ_two, map_add, map_smul]

theorem tensorToTate_eq (x : ℤ_[ℓ] ⊗[ℤ] L.lattice) :
    tensorToTate L ℓ x = coordToTate L ℓ ((tensorBasis L ℤ_[ℓ]).repr x 0) ((tensorBasis L ℤ_[ℓ]).repr x 1) := by
  rw [apply_eq_coords L (tensorToTate L ℓ) x]
  simp [coordToTate, tensorToTate_tmul]

theorem bijective_tensorToTate : Function.Bijective (tensorToTate L ℓ) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun t ↦ ?_⟩
  · rw [tensorToTate_eq] at hx
    obtain ⟨h0, h1⟩ := coordToTate_injective L ℓ hx
    refine (tensorBasis L ℤ_[ℓ]).repr.injective (Finsupp.ext fun i ↦ ?_)
    fin_cases i <;> simp [h0, h1]
  · obtain ⟨⟨a, b⟩, rfl⟩ := coordToTate_surjective L ℓ t
    refine ⟨a • tensorBasis L ℤ_[ℓ] 0 + b • tensorBasis L ℤ_[ℓ] 1, ?_⟩
    rw [tensorToTate_eq]
    simp

/-- **`ℤ_ℓ ⊗ Λ ≅ T_ℓ(ℂ/Λ)`** (Milne, proof of Proposition 11.5). -/
def tensorTateEquiv : ℤ_[ℓ] ⊗[ℤ] L.lattice ≃ₗ[ℤ_[ℓ]] TateModule ℓ (TorusGroup L) :=
  LinearEquiv.ofBijective (tensorToTate L ℓ) (bijective_tensorToTate L ℓ)

end Tate

/-! ### The three representations -/

/-- The action of an endomorphism `f` of `E(Λ)` on the tangent space `Tgt₀(E) = ℂ` (identified through the covering
`ℂ → E(Λ)`): the complex number `ρ(f)` with `f(z mod Λ) = ρ(f) z mod Λ` (wave 5). -/
@[kb "milne2017mf" "Section 11, the tangent representation (pdf p. 112)"]
def tangentRep : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine →+* ℂ :=
  (Subring.subtype _).comp (Wave5.complexUniformization.endRingEquiv L).choose.toRingHom

theorem tangentRep_spec (f : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine) (z : ℂ) :
    f.pointMap (L.weierstrassPoint z) = L.weierstrassPoint (tangentRep L f * z) :=
  (Wave5.complexUniformization.endRingEquiv L).choose_spec f z

theorem tangentRep_mem (f : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine) :
    ∀ x ∈ L.lattice, tangentRep L f * x ∈ L.lattice :=
  ((Wave5.complexUniformization.endRingEquiv L).choose f).2

/-- Multiplication by `α` with `αΛ ⊆ Λ` on `Λ`. -/
def latticeMul (α : ℂ) (hα : ∀ x ∈ L.lattice, α * x ∈ L.lattice) : Module.End ℤ L.lattice :=
  (LinearMap.mulLeft ℤ α).restrict hα

theorem coe_latticeMul (α : ℂ) (hα : ∀ x ∈ L.lattice, α * x ∈ L.lattice) (x : L.lattice) :
    (latticeMul L α hα x : ℂ) = α * x := rfl

/-- Milne's `ρ_B(f)`: the action of `f` on `H₁(E, ℤ) = Λ`, multiplication by `ρ(f)`. -/
@[kb "milne2017mf" "Section 11, the Betti representation (pdf p. 112)"]
def bettiRep (f : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine) :
    Module.End ℤ L.lattice :=
  latticeMul L (tangentRep L f) (tangentRep_mem L f)

theorem coe_bettiRep (f : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine) (x : L.lattice) :
    (bettiRep L f x : ℂ) = tangentRep L f * x := rfl

section TateTransfer

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Tate modules of isomorphic groups are isomorphic. -/
def tateMapEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) :
    TateModule ℓ A ≃ₗ[ℤ_[ℓ]] TateModule ℓ B :=
  LinearEquiv.ofLinearMap (TateModule.mapLinearMap (e : A →+ B)) (TateModule.mapLinearMap (e.symm : B →+ A))
    (by
      ext x n
      simp [TateModule.proj_map])
    (by
      ext x n
      simp [TateModule.proj_map])

theorem tateMapEquiv_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B)
    (x : TateModule ℓ A) : tateMapEquiv ℓ e x = TateModule.map (e : A →+ B) x := rfl

theorem latticeToTate_latticeMul (α : ℂ) (hα : ∀ x ∈ L.lattice, α * x ∈ L.lattice) (x : L.lattice) :
    latticeToTate L ℓ (latticeMul L α hα x) = TateModule.map (torusMul L α hα) (latticeToTate L ℓ x) := by
  ext n
  simp only [proj_latticeToTate, TateModule.proj_map, TateModule.levelMap_apply, coe_latticeLevel,
    coe_latticeMul, torusMul_mk]
  congr 1
  ring

theorem latticeToTate_mul (f : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine) (x : L.lattice) :
    latticeToTate L ℓ (bettiRep L f x) =
      TateModule.map (torusMul L (tangentRep L f) (tangentRep_mem L f)) (latticeToTate L ℓ x) :=
  latticeToTate_latticeMul L ℓ _ _ x

/-- **Transport.** If `u : ℂ/Λ ≅ P` carries multiplication by `α` to `g`, then `ℤ_ℓ ⊗ Λ ≅ T_ℓ P` carries
`(α·) ⊗ 1` to the action of `g` on the Tate module. -/
theorem tate_transport {P : Type*} [AddCommGroup P] (u : TorusGroup L ≃+ P) (α : ℂ)
    (hα : ∀ x ∈ L.lattice, α * x ∈ L.lattice) (g : P →+ P)
    (hg : g.comp (u : TorusGroup L →+ P) = (u : TorusGroup L →+ P).comp (torusMul L α hα)) :
    ((tensorTateEquiv L ℓ).trans (tateMapEquiv ℓ u)).toLinearMap ∘ₗ (latticeMul L α hα).baseChange ℤ_[ℓ] =
      TateModule.mapLinearMap g ∘ₗ ((tensorTateEquiv L ℓ).trans (tateMapEquiv ℓ u)).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  | tmul a y =>
    show (tateMapEquiv ℓ u) (tensorToTate L ℓ (a ⊗ₜ latticeMul L α hα y)) =
      TateModule.mapLinearMap g ((tateMapEquiv ℓ u) (tensorToTate L ℓ (a ⊗ₜ y)))
    rw [tensorToTate_tmul, tensorToTate_tmul, map_smul, map_smul, map_smul, latticeToTate_latticeMul,
      tateMapEquiv_apply, tateMapEquiv_apply, TateModule.mapLinearMap_apply,
      ← AddMonoidHom.comp_apply (TateModule.map g), ← TateModule.map_comp, hg, TateModule.map_comp,
      AddMonoidHom.comp_apply]

theorem pointMapHom_comp_torusPoint (f : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine) :
    f.pointMapHom.comp (torusPointEquiv L : TorusGroup L →+ L.weierstrassCurve.toAffine.Point) =
      (torusPointEquiv L : TorusGroup L →+ L.weierstrassCurve.toAffine.Point).comp
        (torusMul L (tangentRep L f) (tangentRep_mem L f)) := by
  ext z
  simp [torusPointEquiv, torusPointHom_mk, Hom.pointMapHom_apply, tangentRep_spec, torusMul_mk]

omit [Fact ℓ.Prime] in
theorem tate_equivariant (f : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine)
    (x : TateModule ℓ (TorusGroup L)) :
    TateModule.map f.pointMapHom (TateModule.map (torusPointEquiv L : TorusGroup L →+ _) x) =
      TateModule.map (torusPointEquiv L : TorusGroup L →+ _)
        (TateModule.map (torusMul L (tangentRep L f) (tangentRep_mem L f)) x) := by
  rw [← AddMonoidHom.comp_apply (TateModule.map _), ← TateModule.map_comp, pointMapHom_comp_torusPoint,
    TateModule.map_comp, AddMonoidHom.comp_apply]

end TateTransfer

/-! ### Proposition 11.5 -/

/-- The map `ℂ ⊗ Λ → ℂ ⊕ ℂ`, `c ⊗ λ ↦ (cλ, c λ̄)`. -/
def complexSplit : ℂ ⊗[ℤ] L.lattice →ₗ[ℂ] ℂ × ℂ :=
  LinearMap.liftBaseChange ℂ
    { toFun := fun x ↦ ((x : ℂ), conj (x : ℂ))
      map_add' := fun x y ↦ by simp
      map_smul' := fun m x ↦ by simp }

theorem complexSplit_tmul (c : ℂ) (x : L.lattice) :
    complexSplit L (c ⊗ₜ x) = (c * x, c * conj (x : ℂ)) := by
  simp [complexSplit]

theorem periods_det_ne_zero : L.ω₁ * conj L.ω₂ - conj L.ω₁ * L.ω₂ ≠ 0 := by
  intro hD
  have h2 : L.ω₂ ≠ 0 := L.indep.ne_zero 1
  have hreal : ((L.ω₁ * conj L.ω₂).re : ℂ) = L.ω₁ * conj L.ω₂ := by
    rw [← Complex.conj_eq_iff_re]
    simp only [map_mul, Complex.conj_conj]
    linear_combination -hD
  have := LinearIndependent.pair_iff.1 L.indep (-Complex.normSq L.ω₂) (L.ω₁ * conj L.ω₂).re
    (by
      rw [Complex.real_smul, Complex.real_smul, hreal, Complex.ofReal_neg, Complex.normSq_eq_conj_mul_self]
      ring)
  exact h2 (Complex.normSq_eq_zero.1 (neg_eq_zero.1 this.1))

theorem bijective_complexSplit : Function.Bijective (complexSplit L) := by
  have hD := periods_det_ne_zero L
  have hc : ∀ x, complexSplit L x =
      ((tensorBasis L ℂ).repr x 0 * L.ω₁ + (tensorBasis L ℂ).repr x 1 * L.ω₂,
        (tensorBasis L ℂ).repr x 0 * conj L.ω₁ + (tensorBasis L ℂ).repr x 1 * conj L.ω₂) := by
    intro x
    rw [apply_eq_coords L (complexSplit L) x]
    simp [complexSplit_tmul]
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun ⟨u, v⟩ ↦ ?_⟩
  · rw [hc, Prod.mk_eq_zero] at hx
    obtain ⟨h1, h2⟩ := hx
    set c₀ := (tensorBasis L ℂ).repr x 0
    set c₁ := (tensorBasis L ℂ).repr x 1
    have e0 : c₀ = 0 := by
      have : c₀ * (L.ω₁ * conj L.ω₂ - conj L.ω₁ * L.ω₂) = 0 := by
        linear_combination conj L.ω₂ * h1 - L.ω₂ * h2
      simpa [hD] using this
    have e1 : c₁ = 0 := by
      have : c₁ * (L.ω₁ * conj L.ω₂ - conj L.ω₁ * L.ω₂) = 0 := by
        linear_combination L.ω₁ * h2 - conj L.ω₁ * h1
      simpa [hD] using this
    refine (tensorBasis L ℂ).repr.injective (Finsupp.ext fun i ↦ ?_)
    fin_cases i
    · simpa using e0
    · simpa using e1
  · set D := L.ω₁ * conj L.ω₂ - conj L.ω₁ * L.ω₂
    refine ⟨((u * conj L.ω₂ - v * L.ω₂) / D) • tensorBasis L ℂ 0 +
      ((v * L.ω₁ - u * conj L.ω₁) / D) • tensorBasis L ℂ 1, ?_⟩
    rw [hc]
    simp only [map_add, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.add_apply,
      Finsupp.single_apply, smul_eq_mul]
    simp only [Fin.isValue, one_ne_zero, zero_ne_one, ite_true, ite_false, mul_one, mul_zero, add_zero,
      zero_add]
    ext
    · field_simp; ring
    · field_simp; ring

/-- `ℂ ⊗ Λ ≅ ℂ ⊕ ℂ`, `c ⊗ λ ↦ (cλ, c λ̄)`. -/
def complexSplitEquiv : ℂ ⊗[ℤ] L.lattice ≃ₗ[ℂ] ℂ × ℂ :=
  LinearEquiv.ofBijective (complexSplit L) (bijective_complexSplit L)

/-- Under `ℂ ⊗ Λ ≅ ℂ ⊕ ℂ`, `(α·) ⊗ 1` becomes `α ⊕ ᾱ`. -/
theorem complex_transport (α : ℂ) (hα : ∀ x ∈ L.lattice, α * x ∈ L.lattice) (x : ℂ ⊗[ℤ] L.lattice) :
    complexSplitEquiv L ((latticeMul L α hα).baseChange ℂ x) =
      (α * (complexSplitEquiv L x).1, conj α * (complexSplitEquiv L x).2) := by
  induction x using TensorProduct.induction_on with
  | zero => ext <;> simp
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    ext <;> simp [mul_add]
  | tmul c y =>
    show complexSplit L (c ⊗ₜ latticeMul L α hα y) =
      (α * (complexSplit L (c ⊗ₜ y)).1, conj α * (complexSplit L (c ⊗ₜ y)).2)
    simp only [complexSplit_tmul, coe_latticeMul, map_mul]
    ext <;> ring

/-- **Milne, Proposition 11.5**, for the curve `E(Λ)` of a lattice. Let `ρ` be the action of `End(E)` on
`Tgt₀(E) = ℂ`, `ρ_B` its action on `H₁(E, ℤ) = Λ` and `ρ_ℓ` its action on the Tate module `T_ℓE`. Then
(a) `ρ_B ⊗ ℤ_ℓ ≅ ρ_ℓ` and (b) `ρ_B ⊗ ℂ ≅ ρ ⊕ ρ̄`: there are linear isomorphisms `ℤ_ℓ ⊗ Λ ≅ T_ℓE` and
`ℂ ⊗ Λ ≅ ℂ ⊕ ℂ` intertwining, for every endomorphism `f`, `ρ_B(f) ⊗ 1` with `ρ_ℓ(f)` and with
`ρ(f) ⊕ conj ρ(f)`. -/
@[kb "milne2017mf" "Section 11, Proposition 11.5 (pdf p. 112)"]
theorem proposition_11_5 (ℓ : ℕ) [Fact ℓ.Prime] :
    (∃ Φ : ℤ_[ℓ] ⊗[ℤ] L.lattice ≃ₗ[ℤ_[ℓ]] TateModule ℓ L.weierstrassCurve.toAffine.Point,
      ∀ f : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine,
        Φ.toLinearMap ∘ₗ (bettiRep L f).baseChange ℤ_[ℓ] = tateRep L.weierstrassCurve ℓ f ∘ₗ Φ.toLinearMap) ∧
    (∃ Ψ : ℂ ⊗[ℤ] L.lattice ≃ₗ[ℂ] ℂ × ℂ,
      ∀ (f : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine) (x : ℂ ⊗[ℤ] L.lattice),
        Ψ ((bettiRep L f).baseChange ℂ x) = (tangentRep L f * (Ψ x).1, conj (tangentRep L f) * (Ψ x).2)) :=
  ⟨⟨(tensorTateEquiv L ℓ).trans (tateMapEquiv ℓ (torusPointEquiv L)), fun f ↦
      tate_transport L ℓ (torusPointEquiv L) _ _ f.pointMapHom (pointMapHom_comp_torusPoint L f)⟩,
    ⟨complexSplitEquiv L, fun _ x ↦ complex_transport L _ _ x⟩⟩

/-! ### Every complex elliptic curve -/

section General

variable (W : WeierstrassCurve ℂ) [W.IsElliptic]

/-- **Milne, Proposition 11.5**, for every elliptic curve `E` over `ℂ` (Weierstrass model `W`). There are a lattice
`Λ`, the uniformization `u : ℂ/Λ ≅ E(ℂ)` (a group isomorphism, `z ↦ (℘(z), ℘'(z)/2)` followed by a change of
variables), and the ring homomorphism `ρ : End(E) → ℂ` with `f(u(z)) = u(ρ(f) z)` (so `ρ(f)` is the action of `f` on
`Tgt₀(E) = ℂ` through the covering `ℂ → E`, and `ρ(f)Λ ⊆ Λ`); with `ρ_B(f)` multiplication by `ρ(f)` on
`H₁(E, ℤ) = Λ` and `ρ_ℓ(f)` the action on `T_ℓE`: (a) `ρ_B ⊗ ℤ_ℓ ≅ ρ_ℓ` and (b) `ρ_B ⊗ ℂ ≅ ρ ⊕ ρ̄`. -/
@[kb "milne2017mf" "Section 11, Proposition 11.5 (pdf p. 112)"]
theorem proposition_11_5_general (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (L : PeriodPair) (u : TorusGroup L ≃+ W.toAffine.Point) (ρ : Hom W.toAffine W.toAffine →+* ℂ)
      (hρ : ∀ f, ∀ x ∈ L.lattice, ρ f * x ∈ L.lattice),
      (∀ f z, f.pointMap (u z) = u (torusMul L (ρ f) (hρ f) z)) ∧
      (∃ Φ : ℤ_[ℓ] ⊗[ℤ] L.lattice ≃ₗ[ℤ_[ℓ]] TateModule ℓ W.toAffine.Point,
        ∀ f, Φ.toLinearMap ∘ₗ (latticeMul L (ρ f) (hρ f)).baseChange ℤ_[ℓ] = tateRep W ℓ f ∘ₗ Φ.toLinearMap) ∧
      (∃ Ψ : ℂ ⊗[ℤ] L.lattice ≃ₗ[ℂ] ℂ × ℂ, ∀ f (x : ℂ ⊗[ℤ] L.lattice),
        Ψ ((latticeMul L (ρ f) (hρ f)).baseChange ℂ x) = (ρ f * (Ψ x).1, conj (ρ f) * (Ψ x).2)) := by
  obtain ⟨L, C, hC⟩ := Wave5.complexUniformization.exists_lattice W
  have hC' : C⁻¹ • L.weierstrassCurve = W := by rw [← hC, inv_smul_smul]
  let φ : Hom W.toAffine L.weierstrassCurve.toAffine := Hom.ofIsogeny (variableChangeIsogeny C hC)
  let ψ : Hom L.weierstrassCurve.toAffine W.toAffine := Hom.ofIsogeny (variableChangeIsogeny C⁻¹ hC')
  have hψφ : ψ.comp φ = Hom.id W.toAffine := by
    simp only [φ, ψ, Hom.ofIsogeny_comp_ofIsogeny, variableChangeIsogeny_inv_comp C hC hC', Hom.id]
  have hφψ : φ.comp ψ = Hom.id L.weierstrassCurve.toAffine := by
    have := variableChangeIsogeny_inv_comp (C := C⁻¹) hC' (by rw [inv_inv]; exact hC)
    simp only [φ, ψ, Hom.ofIsogeny_comp_ofIsogeny, inv_inv] at this ⊢
    rw [this]; rfl
  have hψφ' : ∀ P, ψ.pointMap (φ.pointMap P) = P := fun P ↦ by
    rw [← Hom.comp_pointMap, hψφ, Hom.id_pointMap]
  have hφψ' : ∀ P, φ.pointMap (ψ.pointMap P) = P := fun P ↦ by
    rw [← Hom.comp_pointMap, hφψ, Hom.id_pointMap]
  let v : L.weierstrassCurve.toAffine.Point ≃+ W.toAffine.Point :=
    { toFun := ψ.pointMap, invFun := φ.pointMap, left_inv := hφψ', right_inv := hψφ',
      map_add' := ψ.pointMap_add }
  let u : TorusGroup L ≃+ W.toAffine.Point := (torusPointEquiv L).trans v
  let conjHom : Hom W.toAffine W.toAffine →+* Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine :=
    { toFun := fun f ↦ φ.comp (f.comp ψ)
      map_one' := by
        rw [Hom.one_def, Hom.id_comp, hφψ]; rfl
      map_mul' := fun f g ↦ by
        simp only [Hom.mul_def]
        calc φ.comp ((f.comp g).comp ψ)
            = φ.comp ((f.comp ((Hom.id _).comp g)).comp ψ) := by rw [Hom.id_comp]
          _ = φ.comp ((f.comp ((ψ.comp φ).comp g)).comp ψ) := by rw [hψφ]
          _ = (φ.comp (f.comp ψ)).comp (φ.comp (g.comp ψ)) := by simp only [Hom.comp_assoc]
      map_zero' := by simp
      map_add' := fun f g ↦ by rw [Hom.add_comp, Hom.comp_add] }
  let ρ := (tangentRep L).comp conjHom
  have hρ : ∀ f, ∀ x ∈ L.lattice, ρ f * x ∈ L.lattice := fun f ↦ tangentRep_mem L (conjHom f)
  have hu : ∀ f z, f.pointMap (u z) = u (torusMul L (ρ f) (hρ f) z) := by
    intro f z
    induction z using QuotientAddGroup.induction_on with | H z => ?_
    have h1 := tangentRep_spec L (conjHom f) z
    have h2 : (conjHom f).pointMap (L.weierstrassPoint z) =
        φ.pointMap (f.pointMap (ψ.pointMap (L.weierstrassPoint z))) := by
      show (φ.comp (f.comp ψ)).pointMap _ = _
      rw [Hom.comp_pointMap, Hom.comp_pointMap]
    rw [h2] at h1
    have h3 := congrArg ψ.pointMap h1
    rw [hψφ'] at h3
    exact h3
  refine ⟨L, u, ρ, hρ, hu, ⟨(tensorTateEquiv L ℓ).trans (tateMapEquiv ℓ u), fun f ↦ ?_⟩,
    ⟨complexSplitEquiv L, fun _ x ↦ complex_transport L _ _ x⟩⟩
  refine tate_transport L ℓ u _ _ f.pointMapHom ?_
  ext z
  simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_ofClass, Function.comp_apply, Hom.pointMapHom_apply]
  exact hu f z

end General

end ModularFormsKB.Milne.Wave6
