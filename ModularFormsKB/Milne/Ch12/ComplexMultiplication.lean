import ModularFormsKB.Milne.Ch12.CMDefs
import ModularFormsKB.Milne.Ch12.IdealLattices
import ModularFormsKB.Milne.Ch12.CMOrder
import ModularFormsKB.Milne.Ch12.VariableChangeEnd
import ModularFormsKB.Milne.Ch12.CMBaseChange
import ModularFormsKB.Milne.Ch12.AutComplex
import TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.Basic
import TauCeti.NumberTheory.NumberField.Global.Orders.RayClass
import ModularFormsKB.Citation
/-!
# Milne, Section 12: elliptic curves with complex multiplication over $\mathbb C$ and over number fields

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, pdf pp. 123–125.

## Conventions

- An *endomorphism* of an elliptic curve over a field $k$ is a Tau Ceti morphism `Hom W W` of its affine Weierstrass
  model (defined over $k$).
- **D125** `HasComplexMultiplication`: $\mathrm{End}(E) \ne \mathbb Z$, i.e. some endomorphism is not multiplication by
  an integer.
- **D129** `HasCMBy`: an isomorphism $R \to \mathrm{End}(E)$ for an order $R$ (Tau Ceti `NumberFieldOrder`) of a
  quadratic imaginary field $K$.
- **D126** `EllCM`: Milne's $\mathrm{Ell}(R)$, the set of isomorphism classes of elliptic curves over $\mathbb C$ with
  complex multiplication by $R$. Over $\mathbb C$ two elliptic curves are isomorphic exactly when their $j$-invariants
  agree (Mathlib `WeierstrassCurve.exists_variableChange_of_j_eq` and `variableChange_j`), so the classes are recorded
  by their $j$-invariants.
- The curve $E(\Lambda) = \mathbb C/\Lambda$ of a lattice is Tau Ceti's `PeriodPair.weierstrassCurve`
  ($y^2 = x^3 - \frac{g_2}4x - \frac{g_3}4$, the model $z \mapsto (\wp(z), \wp'(z)/2)$), and **D128** $j(z)$ is Tau Ceti's
  `TauCeti.ModularForm.j` $= E_4^3/\Delta$, which is $j(E(\mathbb Z z + \mathbb Z))$
  (`UpperHalfPlane.weierstrassCurve_j_periodPair`).
- `latticeEnd Λ` $= \{\alpha \in \mathbb C \mid \alpha\Lambda \subseteq \Lambda\}$.

## Named statements

- `ComplexUniformization`: Milne's summary of the analytic theory (pdf p. 123, "every elliptic curve over
  $\mathbb C$ arises in this way", $\mathrm{Hom}(E(\Lambda), E(\Lambda')) = \{\alpha \mid \alpha\Lambda \subseteq
  \Lambda'\}$, $E(\Lambda) \cong E(\Lambda') \iff \Lambda' = \alpha\Lambda$); Neither Mathlib nor Tau Ceti has the
  uniformization theorem or the analytic description of morphisms.
- `CMPotentialGoodReduction`: Theorem 12.14 (Serre–Tate; proof by class field theory).

## Items

- **Proposition 12.6** `latticeEnd_map_ideal` (the curve $\mathbb C/\mathfrak a$ has endomorphism ring $R$, at the level
  of lattices), `exists_equiv_pic_ellCM` (the bijection $\mathrm{Cl}(R) \to \mathrm{Ell}(R)$).
- **Corollary 12.7** `card_ellCM`: $\#\mathrm{Ell}(R) = h(R)$.
- **Theorem 12.8** `isAlgebraic_j_of_hasComplexMultiplication`.
- **Corollary 12.9** `isAlgebraic_j_of_quadratic`.
- **Theorem 12.14** `CMPotentialGoodReduction` (named).
- **Corollary 12.15** `isIntegral_j_of_hasCMBy` (from Theorem 12.14 and Tau Ceti's
  `HasPotentialGoodReduction.isInteger_j`). Milne writes $j(E) \in \mathcal O_K$; the field is the base field $k$.
- **Corollary 12.16** `isIntegral_j_of_quadratic`.
-/

open NumberField TauCeti TauCeti.Isogeny TauCeti.GlobalNumberFields UpperHalfPlane
open scoped WeierstrassCurve

namespace ModularFormsKB.Milne

/-! ### Proposition 12.6 and Corollary 12.7 -/

section Ideals

variable {K : Type*} [Field K] [NumberField K] (ι : K →+* ℂ) (O : NumberFieldOrder K)

/-- **Proposition 12.6** (Milne), first part, at the level of lattices: for a proper ideal $\mathfrak a$ of an order
$R$ in a quadratic imaginary field $K \subseteq \mathbb C$, $\{\alpha \in \mathbb C \mid \alpha\mathfrak a \subseteq
\mathfrak a\} = R$, so $E(\mathfrak a) = \mathbb C/\mathfrak a$ has complex multiplication by $R$. -/
@[kb "milne2017mf" "Section 12, Prop. 12.6 (pdf p. 123), endomorphisms of C/a"]
theorem latticeEnd_idealLattice (hK : Module.finrank ℚ K = 2)
    (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) (hI : O.IsProperFractionalIdeal I) :
    (latticeEnd (idealLattice ι O I) : Set ℂ) = ι '' (O.toSubalgebra : Set K) := by
  have hmem : ∀ c : ℂ, c ∈ idealLattice ι O I ↔ ∃ w ∈ I, ι w = c := by
    intro c
    simp [idealLattice]
  ext α
  constructor
  · intro hα
    have hI0 : I ≠ 0 := hI.ne_zero
    obtain ⟨x, hxI, hx0⟩ : ∃ x ∈ I, x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hI0 (FractionalIdeal.eq_zero_iff.2 hcon)
    have hα' : α * ι x ∈ idealLattice ι O I := hα _ ((hmem _).2 ⟨x, hxI, rfl⟩)
    obtain ⟨y, hyI, hy⟩ := (hmem _).1 hα'
    have hαeq : α = ι (y / x) := by
      have : ι x ≠ 0 := (map_ne_zero_iff _ ι.injective).2 hx0
      rw [map_div₀, hy, eq_div_iff this]
    have hmult : y / x ∈ O.multiplierRing I := by
      rw [O.mem_multiplierRing_iff]
      intro w hw
      have h1 : α * ι w ∈ idealLattice ι O I := hα _ ((hmem _).2 ⟨w, hw, rfl⟩)
      obtain ⟨w', hw'I, hw'⟩ := (hmem _).1 h1
      have : w' = y / x * w := ι.injective (by rw [hw', hαeq, map_mul])
      rw [← this]; exact hw'I
    rw [(O.isProperFractionalIdeal_def I).1 hI] at hmult
    exact ⟨y / x, hmult, hαeq.symm⟩
  · rintro ⟨o, ho, rfl⟩ c hc
    obtain ⟨w, hwI, rfl⟩ := (hmem _).1 hc
    refine (hmem _).2 ⟨o * w, ?_, by rw [map_mul]⟩
    have : (⟨o, ho⟩ : O.toSubalgebra) • w ∈ I := Submodule.smul_mem (I : Submodule O.toSubalgebra K) _ hwI
    simpa [Algebra.smul_def] using this

/-- An isomorphism of elliptic curves over $\mathbb C$ (a change of variables) preserves $j$. -/
theorem j_eq_of_variableChange {W W' : WeierstrassCurve ℂ} [W.IsElliptic] [W'.IsElliptic]
    {C : WeierstrassCurve.VariableChange ℂ} (h : C • W = W') : W'.j = W.j := by
  subst h
  rw [WeierstrassCurve.variableChange_j]

/-- Two invertible fractional ideals have the same class exactly when $\mathfrak b = x\mathfrak a$ for some $x \in K$. -/
theorem classGroup_mk_eq_mk_iff (I J : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ) :
    ClassGroup.mk K I = ClassGroup.mk K J ↔
      ∃ x : K, (J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) =
        FractionalIdeal.spanSingleton _ x * (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) := by
  rw [eq_comm, ← div_eq_one, ← map_div, ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← hx, div_eq_mul_inv, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [div_eq_mul_inv, Units.val_mul, hx, mul_assoc, Units.mul_inv, mul_one]

/-- The ring isomorphism $R \to \{\alpha \mid \alpha\Lambda \subseteq \Lambda\}$ given by $\iota$, when the latter
ring is $\iota(R)$. -/
noncomputable def orderRingEquivLatticeEnd (Λ : Submodule ℤ ℂ)
    (h : (latticeEnd Λ : Set ℂ) = ι '' (O.toSubalgebra : Set K)) : O.toSubalgebra ≃+* latticeEnd Λ :=
  RingEquiv.ofBijective
    ((ι.comp O.toSubalgebra.val.toRingHom).codRestrict (latticeEnd Λ) fun x => by
      show ι x ∈ (latticeEnd Λ : Set ℂ)
      rw [h]
      exact ⟨x, x.2, rfl⟩)
    ⟨fun x y hxy => Subtype.ext (ι.injective (congrArg Subtype.val hxy)), fun y => by
      obtain ⟨x, hx, hxy⟩ : (y : ℂ) ∈ ι '' (O.toSubalgebra : Set K) := h ▸ y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

/-- **Proof of Proposition 12.6** (Milne): for invertible ideals $\mathfrak a, \mathfrak b$, the curves
$\mathbb C/\iota(\mathfrak a)$ and $\mathbb C/\iota(\mathfrak b)$ are isomorphic exactly when $\mathfrak a$ and
$\mathfrak b$ have the same class. -/
theorem j_eq_iff_classGroup_mk_eq (hU : ComplexUniformization)
    (I J : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ) (L L' : PeriodPair)
    (hL : L.lattice = idealLattice ι O I) (hL' : L'.lattice = idealLattice ι O J) :
    L.weierstrassCurve.j = L'.weierstrassCurve.j ↔ ClassGroup.mk K I = ClassGroup.mk K J := by
  rw [hU.j_eq_iff, classGroup_mk_eq_mk_iff, hL, hL']
  constructor
  · rintro ⟨α, -, h⟩
    exact exists_eq_spanSingleton_mul_of_idealLattice_eq_map ι O I J I.ne_zero α h
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      have h0 : FractionalIdeal.spanSingleton (nonZeroDivisors O.toSubalgebra) (0 : K) = 0 := by simp
      rw [h0, zero_mul] at hx
      exact J.ne_zero hx
    exact ⟨ι x, (map_ne_zero ι).2 hx0, by rw [hx, idealLattice_spanSingleton_mul]⟩

/-- **Proposition 12.6** (Milne): for an order $R$ of a quadratic imaginary field $K \subseteq \mathbb C$, the map
$\mathfrak a \mapsto \mathbb C/\mathfrak a$ induces a bijection $\mathrm{Cl}(R) \to \mathrm{Ell}(R)$: the class of an
invertible ideal $\mathfrak a$ goes to $j(E(L))$ for every lattice $L$ with $L = \sigma(\mathfrak a)$. -/
@[kb "milne2017mf" "Section 12, Prop. 12.6 (pdf p. 123)"]
theorem exists_equiv_pic_ellCM (hU : ComplexUniformization) (hK : Module.finrank ℚ K = 2)
    [IsTotallyComplex K] :
    ∃ φ : Pic O ≃ EllCM O, ∀ (I : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ)
      (L : PeriodPair), L.lattice = idealLattice ι O I →
        (φ (ClassGroup.mk (K := K) I : Pic O) : ℂ) = L.weierstrassCurve.j := by
  classical
  have hrep : ∀ c : Pic O, ∃ I : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ,
      ClassGroup.mk K I = c := fun c => ClassGroup.induction (K := K) (fun I => ⟨I, rfl⟩) c
  have hlat : ∀ I : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ,
      ∃ L : PeriodPair, L.lattice = idealLattice ι O I := fun I =>
    exists_periodPair_idealLattice ι O hK I I.ne_zero
  let f : Pic O → ℂ := fun c => (hlat (hrep c).choose).choose.weierstrassCurve.j
  have hf_spec : ∀ (I : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ) (L : PeriodPair),
      L.lattice = idealLattice ι O I → f (ClassGroup.mk K I) = L.weierstrassCurve.j := fun I L hL =>
    (j_eq_iff_classGroup_mk_eq ι O hU _ I _ L (hlat _).choose_spec hL).2 (hrep _).choose_spec
  have hmem : ∀ (I : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ) (L : PeriodPair),
      L.lattice = idealLattice ι O I → L.weierstrassCurve.j ∈ EllCM O := by
    intro I L hL
    obtain ⟨e, -⟩ := hU.endRingEquiv L
    have hEnd := latticeEnd_idealLattice ι O hK I (O.isProperFractionalIdeal_of_isUnit I.isUnit)
    rw [← hL] at hEnd
    exact ⟨L.weierstrassCurve, inferInstance,
      ⟨hK, inferInstance, ⟨(orderRingEquivLatticeEnd ι O _ hEnd).trans e.symm⟩⟩, rfl⟩
  have hinj : Function.Injective f := by
    intro c d h
    rw [← (hrep c).choose_spec, ← (hrep d).choose_spec]
    exact (j_eq_iff_classGroup_mk_eq ι O hU _ _ _ _ (hlat _).choose_spec (hlat _).choose_spec).1 h
  have hsurj : ∀ x ∈ EllCM O, ∃ c, f c = x := by
    rintro _ ⟨W, hWe, ⟨-, -, ⟨eO⟩⟩, rfl⟩
    obtain ⟨L, C, hC⟩ := hU.exists_lattice W
    obtain ⟨e, -⟩ := hU.endRingEquiv L
    let e' : O.toSubalgebra ≃+* latticeEnd L.lattice := (eO.trans (endRingEquivOfVariableChange hC)).trans e
    have hrange : Set.range ((latticeEnd L.lattice).subtype.comp e'.toRingHom) =
        (latticeEnd L.lattice : Set ℂ) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact (e' x).2
      · intro hy
        exact ⟨e'.symm ⟨y, hy⟩, by simp⟩
    have hEnd : (latticeEnd L.lattice : Set ℂ) = ι '' (O.toSubalgebra : Set K) := by
      rw [← hrange]
      exact range_ringHom_eq_image ι O hK _
    obtain ⟨α, I, hα, hIp, hmap⟩ := exists_idealLattice_of_latticeEnd ι O hK L hEnd
    have hu := (O.isProperFractionalIdeal_iff_isUnit_of_finrank_eq_two hK I).mp hIp
    obtain ⟨L', hL'⟩ := hlat hu.unit
    refine ⟨ClassGroup.mk K hu.unit, ?_⟩
    rw [hf_spec _ L' hL']
    have hj : L.weierstrassCurve.j = W.j := j_eq_of_variableChange hC
    rw [← hj, eq_comm, hU.j_eq_iff]
    exact ⟨α, hα, by rw [hL', IsUnit.unit_spec, ← hmap]⟩
  refine ⟨Equiv.ofBijective (fun c => ⟨f c, hmem _ _ (hlat _).choose_spec⟩)
    ⟨fun c d h => hinj (congrArg Subtype.val h), ?_⟩, ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ := hsurj x hx
    exact ⟨c, Subtype.ext hc⟩
  · intro I L hL
    exact hf_spec I L hL

/-- **Corollary 12.7** (Milne): there are exactly $h(R) = \#\mathrm{Cl}(R)$ elliptic curves over $\mathbb C$, up to
isomorphism, with complex multiplication by $R$. -/
@[kb "milne2017mf" "Section 12, Cor. 12.7 (pdf p. 123)"]
theorem card_ellCM (hU : ComplexUniformization) (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] :
    Nat.card (EllCM O) = Nat.card (Pic O) := by
  obtain ⟨ι'⟩ : Nonempty (K →+* ℂ) := inferInstance
  obtain ⟨φ, -⟩ := exists_equiv_pic_ellCM ι' O hU hK
  exact (Nat.card_congr φ).symm

end Ideals

/-! ### Algebraicity of $j$ (Theorem 12.8, Corollary 12.9) -/

/-- **Theorem 12.8** (Milne): if an elliptic curve $E$ over $\mathbb C$ has complex multiplication then $j(E)$ is
algebraic. -/
@[kb "milne2017mf" "Section 12, Thm. 12.8 (pdf p. 124)"]
theorem isAlgebraic_j_of_hasComplexMultiplication (hU : ComplexUniformization) (W : WeierstrassCurve ℂ)
    [W.IsElliptic] (hW : HasComplexMultiplication W) : IsAlgebraic ℚ W.j := by
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
  obtain ⟨K, _, _, O, hK, hTC, ⟨eO⟩⟩ := exists_order_ringEquiv_latticeEnd L (e' f).2 hα
  have hmem : W.j ∈ EllCM O := ⟨L.weierstrassCurve, inferInstance, ⟨hK, hTC, ⟨eO.trans e.symm⟩⟩,
    j_eq_of_variableChange hC⟩
  have : Finite (EllCM O) := by
    obtain ⟨ι⟩ : Nonempty (K →+* ℂ) := inferInstance
    obtain ⟨φ, -⟩ := exists_equiv_pic_ellCM ι O hU hK
    exact Finite.of_equiv _ φ
  apply isAlgebraic_of_finite_range_ringEquiv
  exact (Set.toFinite (EllCM O)).subset (by rintro _ ⟨σ, rfl⟩; exact j_map_mem_ellCM σ hmem)

/-- **Corollary 12.9** (Milne): if $z \in \mathbb H$ generates a quadratic imaginary field $\mathbb Q[z]$, then
$j(z)$ is algebraic. -/
@[kb "milne2017mf" "Section 12, Cor. 12.9 (pdf p. 124)"]
theorem isAlgebraic_j_of_quadratic (hU : ComplexUniformization) (z : ℍ) (hz : IsIntegral ℚ (z : ℂ))
    (hz2 : (minpoly ℚ (z : ℂ)).natDegree = 2) : IsAlgebraic ℚ (TauCeti.ModularForm.j z) := by
  have hCM : HasComplexMultiplication z.periodPair.weierstrassCurve := by
    obtain ⟨e, -⟩ := hU.endRingEquiv z.periodPair
    have hmonic := minpoly.monic hz
    have hroot := minpoly.aeval ℚ (z : ℂ)
    set p := minpoly ℚ (z : ℂ) with hpdef
    have hc2 : p.coeff 2 = 1 := by
      have := hmonic.coeff_natDegree
      rwa [hz2] at this
    rw [Polynomial.aeval_eq_sum_range, hz2] at hroot
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc2, zero_add] at hroot
    set b := p.coeff 1
    set c := p.coeff 0
    have hq : (z : ℂ) ^ 2 + (b : ℂ) * z + (c : ℂ) = 0 := by
      simpa [Rat.smul_def, add_comm, add_left_comm, add_assoc] using hroot
    set d : ℕ := b.den * c.den with hd
    have hdpos : 0 < d := Nat.mul_pos b.den_pos c.den_pos
    have hB : (d : ℂ) * b = ((b.num * c.den : ℤ) : ℂ) := by
      have : (d : ℚ) * b = ((b.num * c.den : ℤ) : ℚ) := by
        have h := Rat.mul_den_eq_num b
        push_cast [hd]
        linear_combination (c.den : ℚ) * h
      exact_mod_cast congrArg (fun q : ℚ => (q : ℂ)) this
    have hC : (d : ℂ) * c = ((c.num * b.den : ℤ) : ℂ) := by
      have : (d : ℚ) * c = ((c.num * b.den : ℤ) : ℚ) := by
        have h := Rat.mul_den_eq_num c
        push_cast [hd]
        linear_combination (b.den : ℚ) * h
      exact_mod_cast congrArg (fun q : ℚ => (q : ℂ)) this
    set B : ℤ := b.num * c.den
    set C : ℤ := c.num * b.den
    have hw : (d : ℂ) * z ∈ latticeEnd z.periodPair.lattice := by
      intro x hx
      obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 hx
      refine PeriodPair.mem_lattice.2 ⟨-m * B + n * d, -m * C, ?_⟩
      simp only [periodPair_ω₁, periodPair_ω₂]
      push_cast
      linear_combination (-((m : ℂ) * d)) * hq + ((m : ℂ) * z) * hB + (m : ℂ) * hC
    refine ⟨e.symm ⟨(d : ℂ) * z, hw⟩, fun n hf => ?_⟩
    have h1 := congrArg e hf
    rw [e.apply_symm_apply, map_zsmul, map_one] at h1
    have h2 := congrArg (fun x : latticeEnd z.periodPair.lattice => (x : ℂ)) h1
    simp at h2
    have h3 := congrArg Complex.im h2
    simp at h3
    rcases h3 with h3 | h3
    · omega
    · exact absurd h3 z.im_ne_zero
  have := isAlgebraic_j_of_hasComplexMultiplication hU _ hCM
  rwa [weierstrassCurve_j_periodPair] at this

/-! ### Integrality of $j$ (Theorem 12.14, Corollaries 12.15, 12.16) -/

/-- **Theorem 12.14** (Milne; Serre–Tate 1968, Theorem 7 [unverified]): an elliptic curve over a number field $k$ with
complex multiplication by an order $R$ over $k$ has potential good reduction at every prime $v$ of $k$ (here: at the
localization of $\mathcal O_k$ at $v$, Tau Ceti's `HasPotentialGoodReduction`). Named statement; the proof uses
class field theory. -/
@[kb "milne2017mf" "Section 12, Thm. 12.14 (pdf p. 125)"]
structure CMPotentialGoodReduction : Prop where
  potentialGood : ∀ (k : Type) [Field k] [NumberField k] (W : WeierstrassCurve k) [W.IsElliptic]
    (K : Type) [Field K] [NumberField K] (O : NumberFieldOrder K), HasCMBy W O →
    ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 k),
      W.HasPotentialGoodReduction (Localization.AtPrime v.asIdeal)

/-- **Corollary 12.15** (Milne): if an elliptic curve $E$ over a number field $k$ has complex multiplication (by an
order $R$, over $k$), then $j(E)$ is an algebraic integer; from Theorem 12.14. -/
@[kb "milne2017mf" "Section 12, Cor. 12.15 (pdf p. 125)"]
theorem isIntegral_j_of_hasCMBy (h : CMPotentialGoodReduction) {k : Type} [Field k] [NumberField k]
    (W : WeierstrassCurve k) [W.IsElliptic] {K : Type} [Field K] [NumberField K] (O : NumberFieldOrder K)
    (hW : HasCMBy W O) : IsIntegral ℤ W.j := by
  have hv : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 k), ∃ a s : 𝓞 k, s ∈ v.asIdeal.primeCompl ∧
      W.j = algebraMap (𝓞 k) k a * (algebraMap (𝓞 k) k s)⁻¹ := by
    intro v
    have : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 k) v.ne_bot _
    have hint := (h.potentialGood k W K O hW v).isInteger_j
    obtain ⟨r, hr⟩ := hint
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq v.asIdeal.primeCompl r
    refine ⟨a, s, s.2, ?_⟩
    have hs : algebraMap (𝓞 k) k s ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 k) k)).2
        (fun h0 => s.2 (by simp [h0]))
    have hspec := congrArg (algebraMap (Localization.AtPrime v.asIdeal) k)
      (IsLocalization.mk'_spec (Localization.AtPrime v.asIdeal) a s)
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hspec
    rw [← hr]
    exact (eq_mul_inv_iff_mul_eq₀ hs).2 hspec
  have hmem : W.j ∈ (⨅ v : IsDedekindDomain.HeightOneSpectrum (𝓞 k),
        Localization.subalgebra.ofField k _ v.asIdeal.primeCompl_le_nonZeroDivisors) := by
    rw [Algebra.mem_iInf]
    intro v
    obtain ⟨a, s, hs, e⟩ := hv v
    exact ⟨a, s, hs, e⟩
  rw [IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot (𝓞 k) k] at hmem
  obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hmem
  rw [← ha]
  exact RingOfIntegers.isIntegral_coe a

/-- **Corollary 12.16** (Milne): if $z \in \mathbb H$ generates a quadratic imaginary field, then $j(z)$ is an
algebraic integer. Named statement: Milne derives it from Corollary 12.15, which needs a model of $E(\mathbb Z z +
\mathbb Z)$ over a number field with its endomorphisms defined over that field (not available here). -/
@[kb "milne2017mf" "Section 12, Cor. 12.16 (pdf p. 125)"]
structure JIntegralAtCM : Prop where
  isIntegral : ∀ z : ℍ, IsIntegral ℚ (z : ℂ) → (minpoly ℚ (z : ℂ)).natDegree = 2 →
    IsIntegral ℤ (TauCeti.ModularForm.j z)

end ModularFormsKB.Milne
