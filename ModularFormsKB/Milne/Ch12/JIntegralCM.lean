import ModularFormsKB.Milne.Ch12.ComplexMultiplication
import ModularFormsKB.Milne.Ch12.JIntegral
import ModularFormsKB.Milne.Ch12.CMBaseChange
import ModularFormsKB.Milne.Ch12.CMReductions
import ModularFormsKB.Milne.Ch12.VariableChangeEnd
import ModularFormsKB.Milne.Ch3.ComplexUniformization
import ModularFormsKB.Citation
/-!
# Milne, Corollary 12.15 from the analytic theory

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, Cor. 12.15 (pdf p. 125).

Milne proves Corollary 12.15 (integrality of $j(E)$ for $E$ with complex multiplication over a number field) from
Theorem 12.14 (potential good reduction, Serre–Tate). Here it follows instead from the analytic theory of elliptic
curves over $\mathbb C$ (`ComplexUniformization`, a named statement) and the integrality of $j$ at quadratic
imaginary points (`ModularFormsKB.Milne.CMIntegral.isIntegral_j_of_quadratic`, proved through the modular
polynomial):

- `isIntegral_j_of_latticeEnd`: if $\alpha\Lambda \subseteq \Lambda$ with $\alpha \notin \mathbb Z$, then
  $\tau = \omega_1/\omega_2$ (or $-\tau$, whichever lies in $\mathbb H$) satisfies $c\tau^2 + (d - a)\tau - b = 0$
  where $\alpha\omega_1 = a\omega_1 + b\omega_2$, $\alpha\omega_2 = c\omega_1 + d\omega_2$, and $c \ne 0$; and
  $j(\Lambda) = j(\tau)$.
- `isIntegral_j_of_hasComplexMultiplication`: an elliptic curve over $\mathbb C$ with complex multiplication has
  integral $j$.
- `cmJIntegral_of_complexUniformization`: `ComplexUniformization → CMJIntegral` (embed the number field in
  $\mathbb C$; endomorphisms base change injectively, Tau Ceti `TauCeti.Isogeny.Hom.map_injective`).
- `cmPotentialGoodReduction_of_complexUniformization`: hence Theorem 12.14 from `ComplexUniformization`.
-/

open NumberField TauCeti TauCeti.Isogeny TauCeti.GlobalNumberFields UpperHalfPlane
open scoped WeierstrassCurve

namespace ModularFormsKB.Milne

/-- If `ω₁ = ± ω₂ τ` with `τ ∈ ℍ`, the lattice of `(ω₁, ω₂)` is a homothetic copy of `ℤ τ + ℤ`, so its `j`-invariant
is `j τ`. -/
theorem weierstrassCurve_j_eq_of_ω₁ (L : PeriodPair) (τ : ℍ)
    (h : L.ω₁ = L.ω₂ * τ ∨ L.ω₁ = -(L.ω₂ * τ)) :
    L.weierstrassCurve.j = TauCeti.ModularForm.j τ := by
  have hω₂ : L.ω₂ ≠ 0 := by
    simpa using LinearIndependent.ne_zero (1 : Fin 2) L.indep
  have key := (j_eq_iff_homothetic τ.periodPair L).2 ⟨L.ω₂, hω₂, ?_⟩
  · rw [← weierstrassCurve_j_periodPair τ]
    exact key.symm
  · ext x
    simp only [Submodule.mem_map, LinearMap.mulLeft_apply, PeriodPair.mem_lattice, periodPair_ω₁,
      periodPair_ω₂]
    constructor
    · rintro ⟨m, n, rfl⟩
      rcases h with h | h
      · exact ⟨_, ⟨m, n, rfl⟩, by rw [h]; ring⟩
      · exact ⟨_, ⟨-m, n, rfl⟩, by rw [h]; push_cast; ring⟩
    · rintro ⟨y, ⟨m, n, rfl⟩, rfl⟩
      rcases h with h | h
      · exact ⟨m, n, by rw [h]; ring⟩
      · exact ⟨-m, n, by rw [h]; push_cast; ring⟩

/-- A point of `ℍ` satisfying a nontrivial integral quadratic has integral `j`. -/
theorem isIntegral_j_of_quadratic_ne (z : ℍ) (c e f : ℤ) (hc : c ≠ 0)
    (h : (c : ℂ) * (z : ℂ) ^ 2 + e * z + f = 0) : IsIntegral ℤ (TauCeti.ModularForm.j z) := by
  rcases hc.lt_or_gt with hc | hc
  · exact CMIntegral.isIntegral_j_of_quadratic z (-c) (-e) (-f) (by omega)
      (by push_cast; linear_combination -h)
  · exact CMIntegral.isIntegral_j_of_quadratic z c e f hc h

/-- If a lattice has a multiplier $\alpha \notin \mathbb Z$, its $j$-invariant is an algebraic integer. -/
theorem isIntegral_j_of_latticeEnd (L : PeriodPair) {α : ℂ}
    (hα : α ∈ latticeEnd L.lattice) (hα' : ∀ n : ℤ, α ≠ n) : IsIntegral ℤ L.weierstrassCurve.j := by
  have hω₂ : L.ω₂ ≠ 0 := by
    simpa using LinearIndependent.ne_zero (1 : Fin 2) L.indep
  obtain ⟨a, b, h1⟩ := PeriodPair.mem_lattice.1 (hα _ L.ω₁_mem_lattice)
  obtain ⟨c, d, h2⟩ := PeriodPair.mem_lattice.1 (hα _ L.ω₂_mem_lattice)
  have hc : c ≠ 0 := by
    rintro rfl
    apply hα' d
    apply mul_right_cancel₀ hω₂
    rw [← h2]; simp
  have him : (L.ω₁ / L.ω₂).im ≠ 0 := by
    intro him
    have hre : L.ω₁ / L.ω₂ = ((L.ω₁ / L.ω₂).re : ℂ) := Complex.ext (by simp) (by simpa using him)
    have hω : L.ω₁ = ((L.ω₁ / L.ω₂).re : ℂ) * L.ω₂ := by
      rw [← hre]; field_simp
    have := LinearIndependent.pair_iff.1 L.indep 1 (-(L.ω₁ / L.ω₂).re) (by
      simp only [Complex.real_smul]
      push_cast
      rw [one_mul, neg_mul, ← hω]; ring)
    exact one_ne_zero this.1
  have hq : (c : ℂ) * (L.ω₁ / L.ω₂) ^ 2 + ((d : ℤ) - a : ℤ) * (L.ω₁ / L.ω₂) + (-b : ℤ) = 0 := by
    have : (c : ℂ) * L.ω₁ ^ 2 + ((d : ℤ) - a : ℤ) * (L.ω₁ * L.ω₂) + (-b : ℤ) * L.ω₂ ^ 2 = 0 := by
      push_cast
      linear_combination L.ω₁ * h2 - L.ω₂ * h1
    field_simp
    linear_combination this
  rcases him.lt_or_gt with hneg | hpos
  · let τ : ℍ := ⟨-(L.ω₁ / L.ω₂), by simpa using hneg⟩
    have hτ : (τ : ℂ) = -(L.ω₁ / L.ω₂) := rfl
    rw [weierstrassCurve_j_eq_of_ω₁ L τ (Or.inr (by rw [hτ]; field_simp))]
    refine isIntegral_j_of_quadratic_ne τ c (-((d : ℤ) - a)) (-b) hc ?_
    rw [hτ]; push_cast at hq ⊢; linear_combination hq
  · let τ : ℍ := ⟨L.ω₁ / L.ω₂, hpos⟩
    have hτ : (τ : ℂ) = L.ω₁ / L.ω₂ := rfl
    rw [weierstrassCurve_j_eq_of_ω₁ L τ (Or.inl (by rw [hτ]; field_simp))]
    refine isIntegral_j_of_quadratic_ne τ c ((d : ℤ) - a) (-b) hc ?_
    rw [hτ]; exact hq

/-- **An elliptic curve over $\mathbb C$ with complex multiplication has integral $j$-invariant**, given the analytic
theory `ComplexUniformization`. -/
@[kb "milne2017mf" "Section 12, Cor. 12.15 over C, from the analytic theory (pdf p. 125)"]
theorem isIntegral_j_of_hasComplexMultiplication (hU : ComplexUniformization) (W : WeierstrassCurve ℂ)
    [W.IsElliptic] (hW : HasComplexMultiplication W) : IsIntegral ℤ W.j := by
  obtain ⟨L, C, hC⟩ := hU.exists_lattice W
  obtain ⟨e, -⟩ := hU.endRingEquiv L
  obtain ⟨f, hf⟩ := hW
  let e' := (endRingEquivOfVariableChange hC).trans e
  have hα : ∀ n : ℤ, (e' f : ℂ) ≠ n := by
    intro n hn
    apply hf n
    apply e'.injective
    rw [map_zsmul, map_one]
    ext
    simp [hn]
  rw [← j_eq_of_variableChange hC]
  exact isIntegral_j_of_latticeEnd L (e' f).2 hα

/-- A number field order of a quadratic field contains an element that is not an integer. -/
theorem exists_not_int_of_finrank_two {K : Type*} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (O : NumberFieldOrder K) : ∃ x : O.toSubalgebra, ∀ n : ℤ, x ≠ (n : O.toSubalgebra) := by
  by_contra hcon
  push Not at hcon
  have hle : Submodule.span ℚ (O.toSubalgebra : Set K) ≤ Submodule.span ℚ {(1 : K)} := by
    apply Submodule.span_le.2
    intro y hy
    obtain ⟨n, hn⟩ := hcon ⟨y, hy⟩
    have : (n : K) = y := by simpa using (congrArg Subtype.val hn).symm
    rw [← this, SetLike.mem_coe, Submodule.mem_span_singleton]
    exact ⟨n, by simp⟩
  rw [O.spans] at hle
  have h1 := Submodule.finrank_mono hle
  rw [finrank_top, hK] at h1
  have h2 := finrank_span_singleton (K := ℚ) (one_ne_zero : (1 : K) ≠ 0)
  rw [h2] at h1
  omega

/-- **Corollary 12.15 from the case of $\mathbb C$**: if every elliptic curve over $\mathbb C$ with complex
multiplication has integral $j$, then every elliptic curve over a number field with complex multiplication over it has integral $j$ (embed the number field in $\mathbb C$; endomorphisms base change
injectively, Tau Ceti `TauCeti.Isogeny.Hom.map_injective`). -/
theorem isIntegral_j_of_complex
    (h : ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic], HasComplexMultiplication W → IsIntegral ℤ W.j)
    {k : Type} [Field k] [NumberField k] (W : WeierstrassCurve k) [W.IsElliptic] {K : Type} [Field K]
    [NumberField K] (O : NumberFieldOrder K) (hW : HasCMBy W O) : IsIntegral ℤ W.j := by
  obtain ⟨σ⟩ : Nonempty (k →+* ℂ) := inferInstance
  have hCM : HasComplexMultiplication (W.map σ) := by
    obtain ⟨hK, -, ⟨e⟩⟩ := hW
    obtain ⟨x, hx⟩ := exists_not_int_of_finrank_two hK O
    have hinj : Function.Injective (Hom.mapRingHom (W₁ := W.toAffine) σ) := Hom.map_injective σ
    refine ⟨Hom.mapRingHom (W₁ := W.toAffine) σ (e x), fun n hn => hx n ?_⟩
    apply e.injective
    apply hinj
    rw [hn, map_intCast, map_intCast, zsmul_one]
  have h := h (W.map σ) hCM
  rw [WeierstrassCurve.map_j] at h
  exact (isIntegral_algHom_iff σ.toIntAlgHom σ.injective).1 h

/-- **Corollary 12.15 from the analytic theory**: `ComplexUniformization` implies `CMJIntegral`. -/
@[kb "milne2017mf" "Section 12, Cor. 12.15 (pdf p. 125), from the analytic theory"]
theorem cmJIntegral_of_complexUniformization (hU : ComplexUniformization) : CMJIntegral :=
  ⟨fun _ _ _ W _ _ _ _ O hW =>
    isIntegral_j_of_complex (fun W _ hW => isIntegral_j_of_hasComplexMultiplication hU W hW) W O hW⟩

/-! ### Sharper: only the endomorphism lifting is needed -/

/-- Under `EndomorphismLiftStatement`, an endomorphism of $E(\Lambda)$ that is not multiplication by an integer is
multiplication by some $\alpha \notin \mathbb Z$ with $\alpha\Lambda \subseteq \Lambda$. -/
theorem exists_latticeEnd_of_hom (h₁ : EndomorphismLiftStatement) (L : PeriodPair)
    (f : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine)
    (hf : ∀ n : ℤ, f ≠ n • (1 : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine)) :
    ∃ α ∈ latticeEnd L.lattice, ∀ n : ℤ, α ≠ n := by
  obtain ⟨α, hα⟩ := h₁.out L f
  refine ⟨α, fun x hx => ?_, fun n hn => hf n ?_⟩
  · have := hα x
    rw [L.weierstrassPoint_of_mem hx, hom_pointMap_zero, eq_comm,
      L.weierstrassPoint_eq_zero_iff] at this
    exact this
  · refine hom_ext_of_weierstrassPoint fun z => ?_
    let P : ℂ →+ L.weierstrassCurve.toAffine.Point :=
      AddMonoidHom.mk' L.weierstrassPoint (weierstrassPoint_add (L := L))
    have hP : ∀ w, P w = L.weierstrassPoint w := fun _ => rfl
    rw [hα, hn, Hom.zsmul_pointMap, Hom.one_def, Hom.id_pointMap, ← hP, ← hP, ← map_zsmul, zsmul_eq_mul]

/-- **An elliptic curve over $\mathbb C$ with complex multiplication has integral $j$-invariant**, given only the
lifting of endomorphisms to $\mathbb C$ (`EndomorphismLiftStatement`; the other parts of the analytic theory used,
`exists_periodPair_variableChange` and `j_eq_iff_homothetic`, are proved). -/
@[kb "milne2017mf" "Section 12, Cor. 12.15 over C, from the lifting of endomorphisms (pdf p. 125)"]
theorem isIntegral_j_of_hasComplexMultiplication_of_lift (h₁ : EndomorphismLiftStatement)
    (W : WeierstrassCurve ℂ) [W.IsElliptic] (hW : HasComplexMultiplication W) : IsIntegral ℤ W.j := by
  obtain ⟨L, C, hC⟩ := exists_periodPair_variableChange W
  obtain ⟨f, hf⟩ := hW
  let e := endRingEquivOfVariableChange hC
  obtain ⟨α, hα, hα'⟩ := exists_latticeEnd_of_hom h₁ L (e f) fun n hn => hf n (by
    apply e.injective
    rw [hn, map_zsmul, map_one])
  rw [← j_eq_of_variableChange hC]
  exact isIntegral_j_of_latticeEnd L hα hα'

/-- **Theorem 12.14 from the analytic theory**: `ComplexUniformization` implies `CMPotentialGoodReduction`. -/
@[kb "milne2017mf" "Section 12, Thm. 12.14 (pdf p. 125), from the analytic theory"]
theorem cmPotentialGoodReduction_of_complexUniformization (hU : ComplexUniformization) :
    CMPotentialGoodReduction :=
  cmPotentialGoodReduction_iff_cmJIntegral.2 (cmJIntegral_of_complexUniformization hU)

/-- **Corollary 12.15 from the lifting of endomorphisms**: `EndomorphismLiftStatement` implies `CMJIntegral`. -/
@[kb "milne2017mf" "Section 12, Cor. 12.15 (pdf p. 125), from the lifting of endomorphisms"]
theorem cmJIntegral_of_endomorphismLift (h₁ : EndomorphismLiftStatement) : CMJIntegral :=
  ⟨fun _ _ _ W _ _ _ _ O hW =>
    isIntegral_j_of_complex (fun W _ hW => isIntegral_j_of_hasComplexMultiplication_of_lift h₁ W hW) W O hW⟩

/-- **Theorem 12.14 from the lifting of endomorphisms**: `EndomorphismLiftStatement` implies
`CMPotentialGoodReduction`. -/
@[kb "milne2017mf" "Section 12, Thm. 12.14 (pdf p. 125), from the lifting of endomorphisms"]
theorem cmPotentialGoodReduction_of_endomorphismLift (h₁ : EndomorphismLiftStatement) :
    CMPotentialGoodReduction :=
  cmPotentialGoodReduction_iff_cmJIntegral.2 (cmJIntegral_of_endomorphismLift h₁)

end ModularFormsKB.Milne
