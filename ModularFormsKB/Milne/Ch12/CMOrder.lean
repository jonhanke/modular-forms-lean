import ModularFormsKB.Milne.Ch12.CMDefs
import ModularFormsKB.Citation
/-!
# Milne, Section 12: the endomorphism ring of a lattice with complex multiplication is a quadratic order

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, pdf p. 123: "if
$\mathrm{End}(E) \ne \mathbb Z$, then $\mathrm{End}(E)$ is an order in a quadratic imaginary field". At the level of
lattices: if $\alpha\Lambda \subseteq \Lambda$ for some $\alpha \notin \mathbb Z$, then $\{\alpha \mid \alpha\Lambda
\subseteq \Lambda\}$ is isomorphic to an order of the quadratic imaginary field $\mathbb Q(\alpha) \subseteq
\mathbb C$. Used in the proof of Theorem 12.8.
-/

open NumberField TauCeti TauCeti.GlobalNumberFields Polynomial

namespace ModularFormsKB.Milne

private lemma end_matrix (L : PeriodPair) {β : ℂ} (hβ : β ∈ latticeEnd L.lattice) :
    ∃ a b c d : ℤ, β * L.ω₁ = a * L.ω₁ + b * L.ω₂ ∧ β * L.ω₂ = c * L.ω₁ + d * L.ω₂ := by
  obtain ⟨a, b, h1⟩ := PeriodPair.mem_lattice.mp (hβ _ L.ω₁_mem_lattice)
  obtain ⟨c, d, h2⟩ := PeriodPair.mem_lattice.mp (hβ _ L.ω₂_mem_lattice)
  exact ⟨a, b, c, d, h1.symm, h2.symm⟩

private lemma ω₁_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  have := L.indep.ne_zero 0
  simpa using this

private lemma end_quad (L : PeriodPair) {β : ℂ} (hβ : β ∈ latticeEnd L.lattice) :
    ∃ s p : ℤ, β ^ 2 - s * β + p = 0 := by
  obtain ⟨a, b, c, d, h1, h2⟩ := end_matrix L hβ
  refine ⟨a + d, a * d - b * c, ?_⟩
  have h0 : (β ^ 2 - ((a + d : ℤ) : ℂ) * β + ((a * d - b * c : ℤ) : ℂ)) * L.ω₁ = 0 := by
    push_cast
    linear_combination (β - d) * h1 + b * h2
  exact (mul_eq_zero.mp h0).resolve_right (ω₁_ne_zero L)

private lemma end_isIntegral (L : PeriodPair) {β : ℂ} (hβ : β ∈ latticeEnd L.lattice) :
    IsIntegral ℤ β := by
  obtain ⟨s, p, h⟩ := end_quad L hβ
  refine ⟨X ^ 2 - C s * X + C p, ?_, ?_⟩
  · monicity!
  · simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
    simp only [algebraMap_int_eq, eq_intCast]
    linear_combination h

private lemma alpha_data (L : PeriodPair) {α : ℂ} (hα : α ∈ latticeEnd L.lattice)
    (hα' : ∀ n : ℤ, α ≠ n) :
    ∃ a b : ℤ, b ≠ 0 ∧ α * L.ω₁ = a * L.ω₁ + b * L.ω₂ ∧ α.im ≠ 0 := by
  obtain ⟨a, b, c, d, h1, h2⟩ := end_matrix L hα
  have hb : b ≠ 0 := by
    rintro rfl
    apply hα' a
    apply mul_right_cancel₀ (ω₁_ne_zero L)
    simpa using h1
  refine ⟨a, b, hb, h1, fun him => ?_⟩
  have hre : α = (α.re : ℂ) := Complex.ext (by simp) (by simpa using him)
  have key : (α.re - a) • L.ω₁ + (-(b : ℝ)) • L.ω₂ = (0 : ℝ) • L.ω₁ + (0 : ℝ) • L.ω₂ := by
    simp only [Complex.real_smul]
    push_cast
    rw [hre] at h1
    linear_combination h1
  have := (L.indep.eq_of_pair key).2
  exact hb (by exact_mod_cast neg_eq_zero.mp this)

private lemma end_mem_adjoin (L : PeriodPair) {α : ℂ} (hα : α ∈ latticeEnd L.lattice)
    (hα' : ∀ n : ℤ, α ≠ n) {β : ℂ} (hβ : β ∈ latticeEnd L.lattice) :
    β ∈ IntermediateField.adjoin ℚ {α} := by
  obtain ⟨a, b, hb, h1, -⟩ := alpha_data L hα hα'
  obtain ⟨a', b', c', d', h1', h2'⟩ := end_matrix L hβ
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  have heq : β = a' + b' * (α - a) / b := by
    apply mul_right_cancel₀ (ω₁_ne_zero L)
    field_simp
    linear_combination (b : ℂ) * h1' - b' * h1
  rw [heq]
  have hαm : α ∈ IntermediateField.adjoin ℚ {α} := IntermediateField.mem_adjoin_simple_self ℚ α
  exact add_mem (intCast_mem _ _) (div_mem (mul_mem (intCast_mem _ _)
    (sub_mem hαm (intCast_mem _ _))) (intCast_mem _ _))

/-- (Milne, pdf p. 123) If a lattice $\Lambda$ has a multiplier $\alpha \notin \mathbb Z$, then
$\{\alpha \mid \alpha\Lambda \subseteq \Lambda\}$ is isomorphic to an order of a quadratic imaginary field. -/
@[kb "milne2017mf" "Section 12, End(E) is an order in a quadratic imaginary field (pdf p. 123)"]
theorem exists_order_ringEquiv_latticeEnd (L : PeriodPair) {α : ℂ} (hα : α ∈ latticeEnd L.lattice)
    (hα' : ∀ n : ℤ, α ≠ n) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (O : NumberFieldOrder K),
      Module.finrank ℚ K = 2 ∧ IsTotallyComplex K ∧ Nonempty (O.toSubalgebra ≃+* latticeEnd L.lattice) := by
  obtain ⟨a, b, hb, h1, him⟩ := alpha_data L hα hα'
  obtain ⟨s, p, hq⟩ := end_quad L hα
  have haint : IsIntegral ℚ α := (end_isIntegral L hα).tower_top
  set F : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {α} with hF
  have hαF : α ∈ F := IntermediateField.mem_adjoin_simple_self ℚ α
  have : FiniteDimensional ℚ F := IntermediateField.adjoin.finiteDimensional haint
  have : NumberField F := ⟨⟩
  -- degree two
  have hdeg : (minpoly ℚ α).natDegree = 2 := by
    apply le_antisymm
    · have hmon : (X ^ 2 - C (s : ℚ) * X + C (p : ℚ)).Monic := by monicity!
      have hroot : aeval α (X ^ 2 - C (s : ℚ) * X + C (p : ℚ)) = 0 := by
        simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C]
        simp only [eq_ratCast, Rat.cast_intCast]
        linear_combination hq
      have := minpoly.min ℚ α hmon hroot
      have h2 : (X ^ 2 - C (s : ℚ) * X + C (p : ℚ)).natDegree ≤ 2 := by compute_degree
      exact (natDegree_le_natDegree this).trans h2
    · apply (minpoly.two_le_natDegree_iff haint).mpr
      rintro ⟨q, hq'⟩
      apply him
      rw [← hq']
      simp
  have hrank : Module.finrank ℚ F = 2 := by
    rw [IntermediateField.adjoin.finrank haint, hdeg]
  have hcomplex : IsTotallyComplex F := by
    refine ⟨fun w => ?_⟩
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.isComplex_mk_iff]
    set φ := w.embedding
    intro hφ
    rw [ComplexEmbedding.isReal_iff] at hφ
    set g : F := IntermediateField.AdjoinSimple.gen ℚ α with hg
    have hgq : (g : ℂ) ^ 2 - s * (g : ℂ) + p = 0 := by simpa [hg] using hq
    have hgq' : g ^ 2 - (s : F) * g + (p : F) = 0 := by
      apply Subtype.val_injective
      simpa using hgq
    have hz := congrArg φ hgq'
    simp only [map_add, map_sub, map_mul, map_pow, map_intCast, map_zero] at hz
    have hzim : (φ g).im = 0 := by
      have := congrArg (fun ψ => ψ g) hφ
      simp only [ComplexEmbedding.conjugate_coe_eq] at this
      exact Complex.conj_eq_iff_im.mp this
    have hprod : (φ g - α) * (φ g + α - s) = 0 := by
      linear_combination hz - hq
    rcases mul_eq_zero.mp hprod with h | h
    · apply him
      have := congrArg Complex.im h
      simp [hzim] at this
      linarith
    · apply him
      have := congrArg Complex.im h
      simp [hzim] at this
      exact this
  -- the order
  let O : Subalgebra ℤ F :=
    { carrier := {x | (x : ℂ) ∈ latticeEnd L.lattice}
      mul_mem' := fun {x y} hx hy => by
        have := mul_mem (s := latticeEnd L.lattice) hx hy
        simpa using this
      add_mem' := fun {x y} hx hy => by
        have := add_mem (s := latticeEnd L.lattice) hx hy
        simpa using this
      zero_mem' := by simp
      algebraMap_mem' := fun n => by
        have := intCast_mem (latticeEnd L.lattice) n
        simp }
  have hOint : ∀ x ∈ O, IsIntegral ℤ x := fun x hx =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F ℂ) (algebraMap F ℂ).injective).mp
      (end_isIntegral L hx)
  have hle : O ≤ integralClosure ℤ F := fun x hx => hOint x hx
  have : Module.Finite ℤ (integralClosure ℤ F) := inferInstanceAs (Module.Finite ℤ (𝓞 F))
  have hfin : Module.Finite ℤ O :=
    Module.Finite.of_injective (Subalgebra.inclusion hle).toLinearMap
      (Subalgebra.inclusion_injective hle)
  have hgenO : (IntermediateField.AdjoinSimple.gen ℚ α : F) ∈ O := hα
  have hspan : Submodule.span ℚ (O : Set F) = ⊤ := by
    rw [eq_top_iff]
    let pb := IntermediateField.adjoin.powerBasis haint
    rw [← pb.basis.span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    show pb.basis i ∈ O
    rw [pb.coe_basis]
    exact pow_mem hgenO _
  refine ⟨F, inferInstance, inferInstance, ⟨O, hfin, hspan⟩, hrank, hcomplex, ⟨?_⟩⟩
  let f : O →+* latticeEnd L.lattice :=
    { toFun := fun x => ⟨((x : F) : ℂ), x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  refine RingEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    have h' : ((x : F) : ℂ) = ((y : F) : ℂ) :=
      congrArg (fun z : latticeEnd L.lattice => (z : ℂ)) h
    exact Subtype.ext (Subtype.val_injective h')
  · rintro ⟨β, hβ⟩
    exact ⟨⟨⟨β, end_mem_adjoin L hα hα' hβ⟩, hβ⟩, rfl⟩

end ModularFormsKB.Milne
