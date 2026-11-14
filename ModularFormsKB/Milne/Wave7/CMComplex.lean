import ModularFormsKB.Milne.Wave7.HomLift
import ModularFormsKB.Milne.Wave7.LatticeIsogeny
import ModularFormsKB.Milne.Wave5.CMUnconditional
import ModularFormsKB.Milne.Ch12.Isogenies

/-!
# Milne wave 7: Propositions 12.20 and 12.21 over `ℂ`, for the curves `E(Λ)`

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, pdf p. 126.

For an order `R` of an imaginary quadratic field `K ⊆ ℂ` (embedding `ι`) and an invertible fractional ideal `Λ`,
`E(Λ) = E(ι Λ)` has complex multiplication by `R` through `z ↦ ι(a) z` (the normalized action: `ι(a)` on the tangent
space). For an invertible integral ideal `𝔞`, `Ker(𝔞)` on `ℂ/Λ` is `{z | ι(a) z ∈ Λ for all a ∈ 𝔞}`
(`latticeCMKer`), which is `Λ𝔞⁻¹` (`mem_idealLattice_mul_inv_iff`, Lemma 12.19).

* `proposition_12_20_complex` (**Proposition 12.20 over `ℂ`**): the morphism `E(Λ) → E(Λ𝔞⁻¹)` induced by the identity
  of `ℂ` (`exists_hom_of_mul_mem`) has kernel `Ker(𝔞)`, and every morphism `E(Λ) → E(Λ'')` vanishing on `Ker(𝔞)`
  factors through it uniquely.
* `proposition_12_21_complex` (**Proposition 12.21 over `ℂ`**): `[𝔞] · j(ℂ/Λ) = j(ℂ/Λ𝔞⁻¹)` is an action of `Pic(R)`
  on `Ell(R)` (Milne's `𝔞 * E`), simply transitive, and compatible with `𝔞`-isogenies: if `φ : E(Λ) → E(Λ')` has
  kernel `Ker(𝔞)` then `j(E(Λ')) = [𝔞] · j(E(Λ))`.

**Proof.** Every morphism `E(Λ) → E(Λ')` is `z ↦ αz` with `αΛ ⊆ Λ'` (`exists_mul_of_hom`); its kernel is `α⁻¹Λ'`, so
an `𝔞`-isogeny has `α⁻¹Λ' = Λ𝔞⁻¹` and `j(E(Λ')) = j(E(Λ𝔞⁻¹))` (homothetic lattices, `j_eq_iff_homothetic`). The
action is transported from `Pic(R)` along Proposition 12.6 (`Wave5.exists_equiv_pic_ellCM'`).

Restriction (loose end): the statements are for the curves `E(Λ)` and kernels on `ℂ`-points, not for an arbitrary
algebraically closed field of characteristic zero with kernels on `k̄`-points (the named statements
`AIsogenyExists`, `ClassGroupActionPrincipalNormalized`); Milne's proper ideals are taken invertible (equivalent for
orders of quadratic fields).
-/

open NumberField TauCeti TauCeti.Isogeny TauCeti.GlobalNumberFields PeriodPair WeierstrassCurve.Affine

namespace ModularFormsKB.Milne.Wave7

/-- Two morphisms `E(Λ) → E(Λ')` agreeing on the points `P(z)` are equal. -/
theorem hom_ext_of_weierstrassPoint' {L L' : PeriodPair}
    {f g : Hom L.weierstrassCurve.toAffine L'.weierstrassCurve.toAffine}
    (h : ∀ z, f.pointMap (L.weierstrassPoint z) = g.pointMap (L.weierstrassPoint z)) : f = g := by
  refine Hom.ext_pointMap_of_prime_zsmul_eq_zero fun _ _ _ P _ ↦ ?_
  obtain ⟨x, rfl⟩ := surjective_torusPoint (L := L) P
  induction x using Quotient.inductionOn with | h z => exact h z

/-- A lattice is not all of `ℂ`. -/
theorem exists_notMem_lattice (L : PeriodPair) : ∃ z : ℂ, z ∉ L.lattice := by
  by_contra h
  push_neg at h
  obtain ⟨ε, hε, hball⟩ := Metric.exists_ball_inter_eq_singleton_of_mem_discrete
    (s := (L.lattice : Set ℂ)) ⟨inferInstanceAs (DiscreteTopology L.lattice)⟩ (zero_mem L.lattice)
  have hmem : ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ε ∩ (L.lattice : Set ℂ) :=
    ⟨by simp [abs_of_pos hε]; linarith, h _⟩
  rw [hball] at hmem
  have : ((ε / 2 : ℝ) : ℂ) = 0 := hmem
  norm_num at this
  linarith

section CM

variable {K : Type*} [Field K] [NumberField K] (ι : K →+* ℂ) (O : NumberFieldOrder K)

local notation "Frac" => FractionalIdeal (nonZeroDivisors O.toSubalgebra) K

/-- The kernel of a morphism `E(L) → E(L')` lifting `z ↦ αz`, pulled back to `ℂ`. -/
theorem pointMap_eq_zero_iff_of_lift {L L' : PeriodPair}
    {f : Hom L.weierstrassCurve.toAffine L'.weierstrassCurve.toAffine} {α : ℂ}
    (hf : ∀ z, f.pointMap (L.weierstrassPoint z) = L'.weierstrassPoint (α * z)) (z : ℂ) :
    f.pointMap (L.weierstrassPoint z) = 0 ↔ α * z ∈ L'.lattice := by
  rw [hf, L'.weierstrassPoint_eq_zero_iff]

/-- **Proposition 12.20 over `ℂ`** (Milne; Silverman III.4.12): for invertible fractional and integral ideals `Λ`,
`𝔞` of `R`, the canonical morphism `φ_𝔞 : E(Λ) → E(Λ𝔞⁻¹)` has kernel `Ker(𝔞)`, and every morphism
`ψ : E(Λ) → E(Λ'')` with `Ker(𝔞) ⊆ Ker(ψ)` factors uniquely through `φ_𝔞`. -/
@[kb "milne2017mf" "Section 12, Prop. 12.20 (pdf p. 126), over the complex numbers"]
theorem proposition_12_20_complex (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (Λ : Frac) (hΛ : Λ ≠ 0)
    (J : Ideal O.toSubalgebra) (hJ : IsUnit (J : Frac)) (L : PeriodPair) (hL : L.lattice = idealLattice ι O Λ) :
    ∃ (L' : PeriodPair) (φ : Hom L.weierstrassCurve.toAffine L'.weierstrassCurve.toAffine),
      L'.lattice = idealLattice ι O (Λ * (J : Frac)⁻¹) ∧
      (∀ z, φ.pointMap (L.weierstrassPoint z) = 0 ↔ z ∈ latticeCMKer ι O Λ J) ∧
      ∀ (L'' : PeriodPair) (ψ : Hom L.weierstrassCurve.toAffine L''.weierstrassCurve.toAffine),
        (∀ z ∈ latticeCMKer ι O Λ J, ψ.pointMap (L.weierstrassPoint z) = 0) →
          ∃! χ : Hom L'.weierstrassCurve.toAffine L''.weierstrassCurve.toAffine, χ.comp φ = ψ := by
  have hne : Λ * (J : Frac)⁻¹ ≠ 0 := by
    intro h
    apply hΛ
    have hu : (J : Frac)⁻¹ * J = 1 := by
      rw [mul_comm]; exact (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mpr hJ
    calc Λ = Λ * ((J : Frac)⁻¹ * J) := by rw [hu, mul_one]
      _ = 0 := by rw [← mul_assoc, h, zero_mul]
  obtain ⟨L', hL'⟩ := exists_periodPair_idealLattice ι O hK _ hne
  have hker : ∀ z, z ∈ L'.lattice ↔ z ∈ latticeCMKer ι O Λ J := fun z ↦ by
    rw [hL', mem_idealLattice_mul_inv_iff ι O Λ J hJ]
  -- `Λ ⊆ Λ𝔞⁻¹`
  have hsub : ∀ x ∈ L.lattice, (1 : ℂ) * x ∈ L'.lattice := by
    intro x hx
    rw [one_mul, hker]
    intro a ha
    rw [hL] at hx
    obtain ⟨w, hw, rfl⟩ := (mem_idealLattice_iff ι O Λ _).1 hx
    refine (mem_idealLattice_iff ι O Λ _).2 ⟨(a : K) * w, ?_, by simp⟩
    have : ((a : K) * w) = (a : O.toSubalgebra) • w := by simp [Algebra.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ hw
  obtain ⟨φ, hφ⟩ := exists_hom_of_mul_mem L L' 1 hsub
  refine ⟨L', φ, hL', fun z ↦ by rw [pointMap_eq_zero_iff_of_lift hφ, one_mul, hker], ?_⟩
  intro L'' ψ hψ
  obtain ⟨β, -, hβ⟩ := exists_mul_of_hom L L'' ψ
  have hβM : ∀ x ∈ L'.lattice, β * x ∈ L''.lattice := by
    intro x hx
    rw [← L''.weierstrassPoint_eq_zero_iff, ← hβ]
    exact hψ x ((hker x).1 hx)
  obtain ⟨χ, hχ⟩ := exists_hom_of_mul_mem L' L'' β hβM
  refine ⟨χ, hom_ext_of_weierstrassPoint' fun z ↦ ?_, fun χ' hχ' ↦ ?_⟩
  · rw [Hom.comp_pointMap, hφ, one_mul, hχ, hβ]
  · refine hom_ext_of_weierstrassPoint' fun z ↦ ?_
    have h1 := congrArg (fun g : Hom _ _ ↦ g.pointMap (L.weierstrassPoint z)) hχ'
    simp only [Hom.comp_pointMap, hφ, one_mul] at h1
    rw [h1, hχ, hβ]

/-- **Proposition 12.21 over `ℂ`** (Milne; proof omitted in the book): `Pic(R)` acts on `Ell(R)` by
`[𝔞] · j(ℂ/Λ) = j(ℂ/Λ𝔞⁻¹)` (Milne's `𝔞 * E`), the action is simply transitive, and for every invertible integral
ideal `𝔞` and every morphism `φ : E(Λ) → E(Λ')` with kernel `Ker(𝔞)` (an `𝔞`-isogeny), `j(E(Λ')) = [𝔞] · j(E(Λ))`. -/
@[kb "milne2017mf" "Section 12, Prop. 12.21 (pdf p. 126), over the complex numbers"]
theorem proposition_12_21_complex (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] :
    ∃ act : Pic O → EllCM O → EllCM O,
      (∀ x, act 1 x = x) ∧ (∀ c d x, act (c * d) x = act c (act d x)) ∧
      (∀ x₀, Function.Bijective fun c ↦ act c x₀) ∧
      ∀ (Λ I : (Frac)ˣ) (J : Ideal O.toSubalgebra), (J : Frac) = I →
        ∀ (L L' : PeriodPair), L.lattice = idealLattice ι O Λ →
        ∀ (φ : Hom L.weierstrassCurve.toAffine L'.weierstrassCurve.toAffine),
          (∀ z, φ.pointMap (L.weierstrassPoint z) = 0 ↔ z ∈ latticeCMKer ι O Λ J) →
          ∀ hx : L.weierstrassCurve.j ∈ EllCM O,
            ((act (ClassGroup.mk (K := K) I) ⟨_, hx⟩ : EllCM O) : ℂ) = L'.weierstrassCurve.j := by
  obtain ⟨e, he⟩ := Wave5.exists_equiv_pic_ellCM' ι O hK
  refine ⟨fun c x ↦ e (e.symm x * c⁻¹), fun x ↦ by simp, fun c d x ↦ by simp [mul_comm, mul_assoc],
    fun x₀ ↦ ?_, ?_⟩
  · refine e.bijective.comp ?_
    exact (Group.mulLeft_bijective (e.symm x₀)).comp inv_involutive.bijective
  intro Λ I J hJI L L' hL φ hφ hx
  have hJ : IsUnit (J : Frac) := hJI ▸ I.isUnit
  -- `e⁻¹ (j L) = [Λ]`
  have hΛ : e.symm ⟨_, hx⟩ = ClassGroup.mk (K := K) Λ := by
    rw [Equiv.symm_apply_eq]
    exact Subtype.ext (he Λ L hL).symm
  -- the lattice `Λ𝔞⁻¹`
  obtain ⟨M, hM⟩ := exists_periodPair_idealLattice ι O hK ((Λ * I⁻¹ : (Frac)ˣ) : Frac) (Units.ne_zero _)
  have hMker : ∀ z, z ∈ M.lattice ↔ z ∈ latticeCMKer ι O Λ J := fun z ↦ by
    have hval : ((I⁻¹ : (Frac)ˣ) : Frac) = (J : Frac)⁻¹ := by
      rw [hJI]; exact FractionalIdeal.right_inverse_eq K _ _ (Units.mul_inv I)
    rw [hM]
    simp only [Units.val_mul, hval]
    rw [mem_idealLattice_mul_inv_iff ι O Λ J hJ]
  obtain ⟨α, -, hα⟩ := exists_mul_of_hom L L' φ
  have hkerα : ∀ z, α * z ∈ L'.lattice ↔ z ∈ M.lattice := fun z ↦ by
    rw [hMker, ← hφ z, pointMap_eq_zero_iff_of_lift hα]
  have hα0 : α ≠ 0 := by
    rintro rfl
    obtain ⟨z, hz⟩ := exists_notMem_lattice M
    exact hz ((hkerα z).1 (by simp))
  have hjM : M.weierstrassCurve.j = L'.weierstrassCurve.j := by
    rw [j_eq_iff_homothetic]
    refine ⟨α, hα0, ?_⟩
    ext w
    simp only [Submodule.mem_map, LinearMap.mulLeft_apply]
    constructor
    · intro hw
      refine ⟨α⁻¹ * w, (hkerα _).1 ?_, by field_simp⟩
      rwa [← mul_assoc, mul_inv_cancel₀ hα0, one_mul]
    · rintro ⟨z, hz, rfl⟩
      exact (hkerα z).2 hz
  show ((e (e.symm ⟨_, hx⟩ * (ClassGroup.mk (K := K) I)⁻¹) : EllCM O) : ℂ) = _
  rw [hΛ, ← map_inv, ← map_mul, he _ M hM, hjM]

end CM

end ModularFormsKB.Milne.Wave7
