import ModularFormsKB.Milne.Ch12.CMDefs
import TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.Basic
import TauCeti.NumberTheory.NumberField.Global.Orders.Lattice
import ModularFormsKB.Citation
/-!
# Milne, Section 12: lattices of ideals of an order in a quadratic imaginary field

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, pdf p. 123, proof of
Proposition 12.6. For an embedding $\iota \colon K \to \mathbb C$ of a quadratic imaginary field and an order $R$ of
$K$:

* `exists_periodPair_idealLattice`: $\iota(\mathfrak a)$ is a lattice in $\mathbb C$ for every nonzero fractional
  ideal $\mathfrak a$;
* `idealLattice_spanSingleton_mul`, `exists_eq_spanSingleton_mul_of_idealLattice_eq_map`: $\iota(x\mathfrak a) =
  \iota(x)\iota(\mathfrak a)$, and conversely homothetic ideal lattices come from ideals in the same class;
* `range_ringHom_eq_image`: every ring homomorphism $R \to \mathbb C$ has image $\iota(R)$;
* `exists_idealLattice_of_latticeEnd`: a lattice $\Lambda$ with $\{\alpha \mid \alpha\Lambda \subseteq \Lambda\} =
  \iota(R)$ is homothetic to $\iota(\mathfrak a)$ for a proper fractional ideal $\mathfrak a$ of $R$ ("$\Lambda$ is
  homothetic to a lattice contained in $K$, and it is then an $R$-module", Milne's proof).
-/

open NumberField TauCeti TauCeti.GlobalNumberFields

namespace ModularFormsKB.Milne

variable {K : Type*} [Field K] [NumberField K] (ι : K →+* ℂ)

/-- In a quadratic imaginary field, an element outside $\mathbb Q$ has non-real image under every complex
embedding. -/
theorem im_ne_zero_of_notMem_range (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] {x : K}
    (hx : x ∉ Set.range (algebraMap ℚ K)) : (ι x).im ≠ 0 := by
  intro him
  have hli : LinearIndependent ℚ ![(1 : K), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hx
      refine ⟨-s / t, ?_⟩
      simp only [Rat.smul_def, mul_one] at hst
      have ht' : (t : K) ≠ 0 := by exact_mod_cast ht
      simp only [eq_ratCast]
      push_cast
      field_simp
      linear_combination -hst
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [hK])
  have hreal : ∀ y : K, (ι y).im = 0 := by
    intro y
    have hy : y ∈ Submodule.span ℚ (Set.range ![(1 : K), x]) := hspan ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      fin_cases i <;> simp [him]
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul q y _ hy => simp [Rat.smul_def, hy]
  apply IsTotallyComplex.complexEmbedding_not_isReal ι
  rw [ComplexEmbedding.isReal_iff]
  ext y
  simp [ComplexEmbedding.conjugate_coe_eq, Complex.conj_eq_iff_im.mpr (hreal y)]

/-- The images of two $\mathbb Q$-linearly independent elements of a quadratic imaginary field are
$\mathbb R$-linearly independent in $\mathbb C$. -/
theorem linearIndependent_real_map (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] {a b : K}
    (h : LinearIndependent ℚ ![a, b]) : LinearIndependent ℝ ![ι a, ι b] := by
  have ha : a ≠ 0 := h.ne_zero 0
  have hb : b ≠ 0 := h.ne_zero 1
  have hq : a / b ∉ Set.range (algebraMap ℚ K) := by
    rintro ⟨q, hq⟩
    have := (LinearIndependent.pair_iff.mp h) 1 (-q) (by
      simp only [Rat.smul_def, Rat.cast_one, one_mul, Rat.cast_neg]
      have : (q : K) = a / b := by simpa using hq
      rw [this]
      field_simp
      ring)
    simp at this
  have hz := im_ne_zero_of_notMem_range ι hK hq
  have hιb : ι b ≠ 0 := by simpa using hb
  have hιa : ι a = ι (a / b) * ι b := by
    rw [← map_mul, div_mul_cancel₀ _ hb]
  rw [LinearIndependent.pair_iff]
  intro s t hst
  simp only [Complex.real_smul] at hst
  rw [hιa] at hst
  have h2 : ((s : ℂ) * ι (a / b) + t) * ι b = 0 := by linear_combination hst
  have h3 : (s : ℂ) * ι (a / b) + t = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h hιb
  generalize ι (a / b) = z at hz h3
  have h4 := congrArg Complex.im h3
  have h5 := congrArg Complex.re h3
  simp at h4 h5
  have hs : s = 0 := by
    rcases h4 with h | h
    · exact h
    · exact absurd h hz
  subst hs
  simp at h5
  exact ⟨rfl, h5⟩

variable (O : NumberFieldOrder K)

private lemma exists_pair_basis (hK : Module.finrank ℚ K = 2)
    (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) (hI : I ≠ 0) :
    ∃ e₁ e₂ : K, LinearIndependent ℚ ![e₁, e₂] ∧
      (I : Submodule O.toSubalgebra K).restrictScalars ℤ = Submodule.span ℤ {e₁, e₂} := by
  obtain ⟨b, hb⟩ := NumberFieldOrder.exists_basis_restrictScalars_eq_span O hI
  have h0 : 0 < Module.finrank ℚ K := by omega
  have h1 : 1 < Module.finrank ℚ K := by omega
  refine ⟨b ⟨0, h0⟩, b ⟨1, h1⟩, ?_, ?_⟩
  · have := b.linearIndependent.comp ![(⟨0, h0⟩ : Fin (Module.finrank ℚ K)), ⟨1, h1⟩] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff])
    convert this using 1
    ext i
    fin_cases i <;> rfl
  · rw [hb]
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      have hi : i.val < 2 := by omega
      have : i.val = 0 ∨ i.val = 1 := by omega
      rcases this with h | h
      · left; congr 1; exact Fin.ext h
      · right; congr 1; exact Fin.ext h
    · rintro (rfl | rfl)
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩

/-- **Proof of Proposition 12.6** (Milne): $\iota(\mathfrak a)$ is a lattice in $\mathbb C$. -/
theorem exists_periodPair_idealLattice (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K]
    (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) (hI : I ≠ 0) :
    ∃ L : PeriodPair, L.lattice = idealLattice ι O I := by
  obtain ⟨e₁, e₂, hli, he⟩ := exists_pair_basis O hK I hI
  refine ⟨⟨ι e₁, ι e₂, linearIndependent_real_map ι hK hli⟩, ?_⟩
  unfold idealLattice
  rw [he, Submodule.map_span, Set.image_pair]
  rfl

/-- $\iota(x\mathfrak a) = \iota(x)\iota(\mathfrak a)$. -/
theorem idealLattice_spanSingleton_mul (x : K) (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) :
    idealLattice ι O (FractionalIdeal.spanSingleton _ x * I) =
      (idealLattice ι O I).map (LinearMap.mulLeft ℤ (ι x)) := by
  ext y
  simp only [idealLattice, Submodule.mem_map, Submodule.restrictScalars_mem,
    FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨k, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨ι j, ⟨j, hj, rfl⟩, by simp⟩
  · rintro ⟨w, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨x * j, ⟨j, hj, rfl⟩, by simp⟩

private lemma mem_idealLattice_iff (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) (k : K) :
    ι k ∈ idealLattice ι O I ↔ k ∈ I := by
  simp only [idealLattice, Submodule.mem_map, Submodule.restrictScalars_mem,
    FractionalIdeal.mem_coe]
  constructor
  · rintro ⟨j, hj, hjk⟩
    have : j = k := ι.injective hjk
    exact this ▸ hj
  · intro h
    exact ⟨k, h, rfl⟩

/-- The ideal lattice determines the fractional ideal. -/
theorem idealLattice_injective : Function.Injective (idealLattice ι O) := by
  intro I J h
  ext k
  rw [← mem_idealLattice_iff ι O I, ← mem_idealLattice_iff ι O J, h]

/-- **Proof of Proposition 12.6** (Milne): if $\iota(\mathfrak b) = \alpha\,\iota(\mathfrak a)$ with $\mathfrak a \ne
0$, then $\mathfrak b = x\mathfrak a$ for some $x \in K$ (with $\iota(x) = \alpha$). -/
theorem exists_eq_spanSingleton_mul_of_idealLattice_eq_map
    (I J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) (hI : I ≠ 0) (α : ℂ)
    (h : idealLattice ι O J = (idealLattice ι O I).map (LinearMap.mulLeft ℤ α)) :
    ∃ x : K, J = FractionalIdeal.spanSingleton _ x * I := by
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr hI)
  have hmem : ι a ∈ idealLattice ι O I := (mem_idealLattice_iff ι O I a).mpr haI
  have h1 : α * ι a ∈ idealLattice ι O J := by
    rw [h]
    exact ⟨ι a, hmem, rfl⟩
  obtain ⟨j, -, hj⟩ := h1
  have hj' : ι j = α * ι a := hj
  have hιa : ι a ≠ 0 := by simpa using ha
  have hx : ι (j / a) = α := by
    rw [map_div₀, hj']
    field_simp
  refine ⟨j / a, idealLattice_injective ι O ?_⟩
  rw [idealLattice_spanSingleton_mul, hx, h]

private lemma exists_quad_rel (hK : Module.finrank ℚ K = 2) (y : K) (hy : IsIntegral ℤ y) :
    ∃ b c : ℤ, y ^ 2 + b * y + c = 0 := by
  have hmon : (minpoly ℤ y).Monic := minpoly.monic hy
  have hdeg : (minpoly ℤ y).natDegree ≤ 2 := by
    have h1 := minpoly.natDegree_le (A := ℚ) y
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hy, hmon.natDegree_map] at h1
    omega
  have hpos : 0 < (minpoly ℤ y).natDegree := minpoly.natDegree_pos hy
  have hz := minpoly.aeval ℤ y
  rw [hmon.as_sum] at hz
  have hn : (minpoly ℤ y).natDegree = 1 ∨ (minpoly ℤ y).natDegree = 2 := by omega
  rcases hn with h | h
  · rw [h] at hz
    refine ⟨(minpoly ℤ y).coeff 0, 0, ?_⟩
    simp at hz
    linear_combination y * hz
  · rw [h] at hz
    refine ⟨(minpoly ℤ y).coeff 1, (minpoly ℤ y).coeff 0, ?_⟩
    simp [Finset.sum_range_succ] at hz
    linear_combination hz

/-- Every ring homomorphism $R \to \mathbb C$ from an order of a quadratic field has the same image as $\iota$:
it is $\iota$ or $\bar\iota$ on $R$, and $\overline{\iota(R)} = \iota(R)$. -/
theorem range_ringHom_eq_image (hK : Module.finrank ℚ K = 2) (ψ : O.toSubalgebra →+* ℂ) :
    Set.range ψ = ι '' (O.toSubalgebra : Set K) := by
  have key : ∀ y : O.toSubalgebra,
      ψ y = ι y ∨ ∃ z : O.toSubalgebra, ψ y = ι z ∧ ι y = ψ z := by
    intro y
    obtain ⟨b, c, hbc⟩ := exists_quad_rel hK (y : K) (O.isIntegral y)
    have hO : (y : O.toSubalgebra) ^ 2 + (b : O.toSubalgebra) * y + (c : O.toSubalgebra) = 0 := by
      apply Subtype.ext
      simpa using hbc
    have h1 := congrArg ψ hO
    simp only [map_add, map_pow, map_mul, map_intCast, map_zero] at h1
    have h2 := congrArg ι hbc
    simp only [map_add, map_pow, map_mul, map_intCast, map_zero] at h2
    have h3 : (ψ y - ι y) * (ψ y + ι y + b) = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.mp h3 with h | h
    · left
      exact sub_eq_zero.mp h
    · right
      refine ⟨-(b : O.toSubalgebra) - y, ?_, ?_⟩
      · push_cast
        simp only [map_sub, map_neg, map_intCast]
        linear_combination h
      · simp only [map_sub, map_neg, map_intCast]
        linear_combination h
  ext w
  constructor
  · rintro ⟨y, rfl⟩
    rcases key y with h | ⟨z, hz, -⟩
    · exact ⟨y, y.2, h.symm⟩
    · exact ⟨z, z.2, hz.symm⟩
  · rintro ⟨x, hx, rfl⟩
    rcases key ⟨x, hx⟩ with h | ⟨z, -, hz⟩
    · exact ⟨⟨x, hx⟩, h⟩
    · exact ⟨z, hz.symm⟩

/-- **Proof of Proposition 12.6** (Milne): a lattice $\Lambda$ with $\{\alpha \mid \alpha\Lambda \subseteq \Lambda\}
= \iota(R)$ is homothetic to $\iota(\mathfrak a)$ for a proper fractional ideal $\mathfrak a$ of $R$. -/
theorem exists_idealLattice_of_latticeEnd (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (L : PeriodPair)
    (hL : (latticeEnd L.lattice : Set ℂ) = ι '' (O.toSubalgebra : Set K)) :
    ∃ (α : ℂ) (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K), α ≠ 0 ∧
      O.IsProperFractionalIdeal I ∧ L.lattice.map (LinearMap.mulLeft ℤ α) = idealLattice ι O I := by
  classical
  have hω₁ : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  -- an element of `O` outside `ℚ`
  obtain ⟨β, hβO, hβ⟩ : ∃ β ∈ O.toSubalgebra, β ∉ Set.range (algebraMap ℚ K) := by
    by_contra hcon
    push Not at hcon
    have hle : (⊤ : Submodule ℚ K) ≤ Submodule.span ℚ {(1 : K)} := by
      rw [← O.spans]
      apply Submodule.span_le.mpr
      intro x hx
      obtain ⟨q, rfl⟩ := hcon x hx
      exact Submodule.mem_span_singleton.mpr ⟨q, by simp⟩
    rw [top_le_iff] at hle
    have h1 := finrank_span_singleton (K := ℚ) (one_ne_zero : (1 : K) ≠ 0)
    rw [hle, finrank_top] at h1
    omega
  have hβim := im_ne_zero_of_notMem_range ι hK hβ
  set α : ℂ := L.ω₁⁻¹ with hα
  set τ : ℂ := L.ω₂ / L.ω₁ with hτ
  have hα0 : α ≠ 0 := inv_ne_zero hω₁
  have hmem : ∀ y : ℂ, y ∈ L.lattice.map (LinearMap.mulLeft ℤ α) ↔
      ∃ m n : ℤ, (m : ℂ) + n * τ = y := by
    intro y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hx
      refine ⟨m, n, ?_⟩
      simp only [LinearMap.mulLeft_apply, hα, hτ]
      field_simp
    · rintro ⟨m, n, rfl⟩
      refine ⟨m * L.ω₁ + n * L.ω₂, PeriodPair.mem_lattice.mpr ⟨m, n, rfl⟩, ?_⟩
      simp only [LinearMap.mulLeft_apply, hα, hτ]
      field_simp
  -- endomorphisms of the scaled lattice
  have hendA : ∀ γ ∈ ι '' (O.toSubalgebra : Set K),
      ∀ x ∈ L.lattice.map (LinearMap.mulLeft ℤ α), γ * x ∈ L.lattice.map (LinearMap.mulLeft ℤ α) := by
    intro γ hγ x hx
    rw [← hL] at hγ
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    exact ⟨γ * x₀, hγ x₀ hx₀, by simp only [LinearMap.mulLeft_apply]; ring⟩
  have hendB : ∀ γ : ℂ, (∀ x ∈ L.lattice.map (LinearMap.mulLeft ℤ α),
      γ * x ∈ L.lattice.map (LinearMap.mulLeft ℤ α)) → γ ∈ ι '' (O.toSubalgebra : Set K) := by
    intro γ hγ
    rw [← hL]
    intro x₀ hx₀
    obtain ⟨x₁, hx₁, h⟩ := hγ (α * x₀) ⟨x₀, hx₀, rfl⟩
    have : x₁ = γ * x₀ := by
      simp only [LinearMap.mulLeft_apply] at h
      apply mul_left_cancel₀ hα0
      rw [h]; ring
    exact this ▸ hx₁
  have h1mem : (1 : ℂ) ∈ L.lattice.map (LinearMap.mulLeft ℤ α) :=
    (hmem 1).mpr ⟨1, 0, by simp⟩
  have hτmem : τ ∈ L.lattice.map (LinearMap.mulLeft ℤ α) :=
    (hmem τ).mpr ⟨0, 1, by simp⟩
  -- `τ` lies in `ι K`
  obtain ⟨m, n, hmn⟩ := (hmem (ι β * 1)).mp (hendA (ι β) ⟨β, hβO, rfl⟩ 1 h1mem)
  have hn : n ≠ 0 := by
    rintro rfl
    apply hβim
    have := congrArg Complex.im hmn
    simpa using this.symm
  have hn' : ((n : K)) ≠ 0 := by exact_mod_cast hn
  obtain ⟨t, ht⟩ : ∃ t : K, ι t = τ := by
    refine ⟨((β - m) / n : K), ?_⟩
    simp only [map_div₀, map_sub, map_intCast]
    have hn'' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    field_simp
    linear_combination -hmn
  let M : Submodule O.toSubalgebra K := Submodule.span O.toSubalgebra {1, t}
  let I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K :=
    ⟨M, FractionalIdeal.isFractional_of_fg ⟨{1, t}, by simp [M]⟩⟩
  have hIM : ∀ k : K, k ∈ I ↔ ∃ a b : O.toSubalgebra, (a : K) + b * t = k := by
    intro k
    show k ∈ M ↔ _
    simp only [M, Submodule.mem_span_pair, Algebra.smul_def, mul_one]
    rfl
  have hlat : idealLattice ι O I = L.lattice.map (LinearMap.mulLeft ℤ α) := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨a, b, rfl⟩ := (hIM k).mp hk
      have ha := hendA (ι a) ⟨a, a.2, rfl⟩ 1 h1mem
      have hb := hendA (ι b) ⟨b, b.2, rfl⟩ τ hτmem
      have := Submodule.add_mem _ ha hb
      simpa [ht] using this
    · intro hy
      obtain ⟨m, n, rfl⟩ := (hmem y).mp hy
      refine ⟨(m : K) + n * t, (hIM _).mpr ⟨m, n, ?_⟩, ?_⟩
      · simp
      · simp [ht]
  refine ⟨α, I, hα0, ?_, hlat.symm⟩
  rw [NumberFieldOrder.isProperFractionalIdeal_iff]
  intro x hx
  have h1I : (1 : K) ∈ I := (hIM 1).mpr ⟨1, 0, by simp⟩
  have hxI := hx 1 h1I
  have hγ : ι x ∈ ι '' (O.toSubalgebra : Set K) := by
    apply hendB
    rw [← hlat]
    rintro w ⟨k, hk, rfl⟩
    exact ⟨x * k, hx k hk, by simp⟩
  obtain ⟨o, ho, hox⟩ := hγ
  exact ι.injective hox ▸ ho

end ModularFormsKB.Milne
