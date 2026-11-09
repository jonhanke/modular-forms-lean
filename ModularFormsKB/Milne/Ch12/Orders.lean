import TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.Conductor
import TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.Basic
import TauCeti.NumberTheory.NumberField.Global.Orders.ClassNumber
import TauCeti.RingTheory.DedekindDomain.Totient
import ModularFormsKB.Citation
/-!
# Milne, Section 12: orders in a quadratic field (Propositions 12.2–12.4, Remark 12.5)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, pdf pp. 122–123.

Milne: an *order* of a quadratic imaginary field $K$ is a subring $R$ containing $\mathbb Z$ and free of rank $2$ over
$\mathbb Z$. We use Tau Ceti's `NumberFieldOrder K` (a subring, finite over $\mathbb Z$, spanning $K$ over
$\mathbb Q$); `numberFieldOrderOfFreeRankTwo` shows that Milne's orders are Tau Ceti orders. Nothing below uses that
$K$ is imaginary: the statements hold for every quadratic field ($[K:\mathbb Q] = 2$).

## Items

- **Proposition 12.2**: `exists_unique_conductor` ($R = \mathbb Z + f\mathcal O_K$ for a unique $f > 0$; the integer
  is Tau Ceti's index $[\mathcal O_K : R]$, from `NumberFieldOrder.mem_toRingOfIntegers_iff_exists_int_add_index_mul`)
  and `exists_order_eq_int_add_mul` (conversely $\mathbb Z + f\mathcal O_K$ is an order).
- **D120** (the conductor $f$ of $R$): `NumberFieldOrder.index`; `exists_unique_conductor` identifies it.
- **Proposition 12.3**: `proper_tfae` for a nonzero fractional ideal $\mathfrak a$ of $R$: (a) projective,
  (b) $\{x \in K \mid x\mathfrak a \subseteq \mathfrak a\} = R$ (Tau Ceti's `IsProperFractionalIdeal`, **D121**),
  (c) locally principal at every maximal ideal of $R$. *Erratum*: Milne's (c) reads $\mathfrak a = x\cdot\mathcal O_K$
  for an idele $x$, i.e. $\mathfrak a\mathcal O_v = x_v\mathcal O_v$ for all primes $v$ of $\mathcal O_K$; that holds
  for every lattice, so the condition must be local principality over $R$; the equivalence with that condition is
  proved here (`proper_tfae`).
- **Proposition 12.4**: `proper_mul`, `proper_one`, `proper_exists_inv` (the proper ideals form a group with identity
  $R$; Tau Ceti: proper $\Leftrightarrow$ invertible in a quadratic order).
- **D122, D123** (principal ideals, $\mathrm{Cl}(R)$): Mathlib's `toPrincipalIdeal` and Tau Ceti's
  `NumberFieldOrder.Pic O = ClassGroup O`, the invertible (= proper, by Proposition 12.4) fractional ideals modulo the
  principal ones.
- **Remark 12.5**: `card_pic_formula`, $h(R) = h\,f\,(\mathcal O_K^\times : R^\times)^{-1}\prod_{p\mid f}
  \bigl(1 - (\tfrac Kp)\tfrac1p\bigr)$, with $(\tfrac Kp)$ defined by the splitting of $p$ (`splittingSymbol`).
-/

open NumberField TauCeti.GlobalNumberFields

namespace ModularFormsKB.Milne

variable {K : Type*} [Field K] [NumberField K]

/-- Milne's definition of an order (a subring of $K$, free of rank $2$ over $\mathbb Z$) gives a Tau Ceti order when
$[K:\mathbb Q] = 2$. -/
@[kb "milne2017mf" "Section 12, definition of an order (pdf p. 122)"]
noncomputable def numberFieldOrderOfFreeRankTwo (hK : Module.finrank ℚ K = 2) (R : Subalgebra ℤ K)
    [Module.Free ℤ R] [Module.Finite ℤ R] (hR : Module.finrank ℤ R = 2) : NumberFieldOrder K where
  toSubalgebra := R
  finite := inferInstance
  spans := by
    classical
    let b := Module.finBasisOfFinrankEq ℤ R hR
    have hli : LinearIndependent ℤ (fun i : Fin 2 => ((b i : R) : K)) :=
      b.linearIndependent.map' (Submodule.subtype R.toSubmodule) (Submodule.ker_subtype _)
    have hli' : LinearIndependent ℚ (fun i : Fin 2 => ((b i : R) : K)) :=
      (LinearIndependent.iff_fractionRing ℤ ℚ).mp hli
    have htop := hli'.span_eq_top_of_card_eq_finrank' (by simp [hK])
    refine top_le_iff.mp (htop ▸ Submodule.span_mono ?_)
    rintro _ ⟨i, rfl⟩
    exact (b i).2

/-- The set $\mathbb Z + f\mathcal O_K \subseteq K$. -/
def intAddMulRingOfIntegers (K : Type*) [Field K] [NumberField K] (f : ℕ) : Set K :=
  {x | ∃ (a : ℤ) (y : 𝓞 K), x = a + f * (y : K)}

private theorem coe_toSubalgebra_eq_aux (hK : Module.finrank ℚ K = 2) (O : NumberFieldOrder K) :
    (O.toSubalgebra : Set K) = intAddMulRingOfIntegers K O.index := by
  ext x
  simp only [SetLike.mem_coe, intAddMulRingOfIntegers, Set.mem_ofPred_eq]
  constructor
  · intro hx
    have hxi : x ∈ integralClosure ℤ K := O.le_ringOfIntegers hx
    have h := (O.mem_toRingOfIntegers_iff_exists_int_add_index_mul hK ⟨x, hxi⟩).mp hx
    obtain ⟨a, y, hy⟩ := h
    refine ⟨a, y, ?_⟩
    have := congrArg (fun z : 𝓞 K => (z : K)) hy
    simpa using this
  · rintro ⟨a, y, rfl⟩
    have := (O.mem_toRingOfIntegers_iff_exists_int_add_index_mul hK
      ((a : 𝓞 K) + O.index * y)).mpr ⟨a, y, rfl⟩
    simpa using this

private theorem dvd_of_subset_aux (hK : Module.finrank ℚ K = 2) {f g : ℕ}
    (h : intAddMulRingOfIntegers K f ⊆ intAddMulRingOfIntegers K g) : g ∣ f := by
  obtain ⟨b, hb⟩ := (Module.Free.isUnimodular_one (R := ℤ) (A := 𝓞 K)).exists_basis_zero_eq
    (by rw [RingOfIntegers.rank, hK])
  have hmem : (f : K) * (b 1 : K) ∈ intAddMulRingOfIntegers K f := ⟨0, b 1, by simp⟩
  obtain ⟨a, y, hy⟩ := h hmem
  have hy' : (f : 𝓞 K) * b 1 = a + g * y := by
    apply RingOfIntegers.ext
    push_cast
    exact hy
  have hc := congrArg (b.coord 1) hy'
  have e1 : (f : 𝓞 K) * b 1 = (f : ℤ) • b 1 := by simp
  have e2 : (a : 𝓞 K) = a • b 0 := by simp [hb]
  have e3 : (g : 𝓞 K) * y = (g : ℤ) • y := by simp
  rw [e1, e2, e3, map_add, map_smul, map_smul, map_smul] at hc
  simp [Module.Basis.coord_apply] at hc
  have : (g : ℤ) ∣ f := ⟨b.coord 1 y, by simpa using hc⟩
  exact_mod_cast this

/-- **Proposition 12.2** (Milne), first part: for an order $R$ of a quadratic field $K$ there is a unique integer
$f > 0$ with $R = \mathbb Z + f\mathcal O_K$ (namely the index $[\mathcal O_K : R]$, Tau Ceti's `index`). -/
@[kb "milne2017mf" "Section 12, Prop. 12.2 (pdf p. 122)"]
theorem exists_unique_conductor (hK : Module.finrank ℚ K = 2) (O : NumberFieldOrder K) :
    ∃! f : ℕ, 0 < f ∧ (O.toSubalgebra : Set K) = intAddMulRingOfIntegers K f := by
  refine ⟨O.index, ⟨Nat.pos_of_ne_zero O.index_ne_zero, coe_toSubalgebra_eq_aux hK O⟩, ?_⟩
  rintro g ⟨-, hg⟩
  have h := coe_toSubalgebra_eq_aux hK O
  exact Nat.dvd_antisymm (dvd_of_subset_aux hK (h.symm.le.trans hg.le))
    (dvd_of_subset_aux hK (hg.symm.le.trans h.le))

/-- The integer of Proposition 12.2 is Tau Ceti's index $[\mathcal O_K : R]$ (Milne's conductor, **D120**). -/
@[kb "milne2017mf" "Section 12, conductor of an order (pdf p. 122)"]
theorem coe_toSubalgebra_eq_intAddMul_index (hK : Module.finrank ℚ K = 2) (O : NumberFieldOrder K) :
    (O.toSubalgebra : Set K) = intAddMulRingOfIntegers K O.index :=
  coe_toSubalgebra_eq_aux hK O

/-- **Proposition 12.2** (Milne), converse: for every integer $f > 0$, $\mathbb Z + f\mathcal O_K$ is an order. -/
@[kb "milne2017mf" "Section 12, Prop. 12.2, converse (pdf p. 122)"]
theorem exists_order_eq_int_add_mul (hK : Module.finrank ℚ K = 2) (f : ℕ) (hf : 0 < f) :
    ∃ O : NumberFieldOrder K, (O.toSubalgebra : Set K) = intAddMulRingOfIntegers K f := by
  let S : Subalgebra ℤ K :=
    { carrier := intAddMulRingOfIntegers K f
      mul_mem' := by
        rintro _ _ ⟨a, y, rfl⟩ ⟨a', y', rfl⟩
        refine ⟨a * a', a * y' + a' * y + f * (y * y'), ?_⟩
        have hc : ∀ n : ℤ, (((n : 𝓞 K)) : K) = n := fun n => map_intCast (algebraMap (𝓞 K) K) n
        push_cast
        simp only [hc]
        ring
      add_mem' := by
        rintro _ _ ⟨a, y, rfl⟩ ⟨a', y', rfl⟩
        refine ⟨a + a', y + y', ?_⟩
        push_cast
        ring
      zero_mem' := ⟨0, 0, by simp⟩
      algebraMap_mem' := fun n => ⟨n, 0, by simp⟩ }
  have hSmem : ∀ x, x ∈ S ↔ x ∈ intAddMulRingOfIntegers K f := fun x => Iff.rfl
  let φ : (ℤ × 𝓞 K) →ₗ[ℤ] K :=
    { toFun := fun p => (p.1 : K) + f * (p.2 : K)
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add]
        push_cast
        ring
      map_smul' := by
        intro c p
        simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_eq_mul]
        push_cast
        simp only [zsmul_eq_mul]
        ring }
  have hφ : ∀ p, φ p ∈ S.toSubmodule := fun p => ⟨p.1, p.2, rfl⟩
  have hfin : Module.Finite ℤ S := by
    refine Module.Finite.of_surjective (φ.codRestrict S.toSubmodule hφ) ?_
    rintro ⟨x, a, y, rfl⟩
    exact ⟨(a, y), rfl⟩
  refine ⟨⟨S, hfin, ?_⟩, rfl⟩
  have hb := (NumberField.integralBasis K).span_eq
  rw [eq_top_iff, ← hb, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hfq : (f : ℚ) ≠ 0 := by exact_mod_cast hf.ne'
  have hm : (f : K) * NumberField.integralBasis K i ∈ (S : Set K) :=
    ⟨0, RingOfIntegers.basis K i, by simp⟩
  have : NumberField.integralBasis K i = (f : ℚ)⁻¹ • ((f : K) * NumberField.integralBasis K i) := by
    have hfK : (f : K) ≠ 0 := by exact_mod_cast hf.ne'
    rw [Rat.smul_def]
    push_cast
    field_simp
  rw [SetLike.mem_coe, this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

/-- Local principality of a fractional ideal $\mathfrak a$ of $R$ at a maximal ideal $\mathfrak p$:
$\mathfrak a R_{\mathfrak p} = xR_{\mathfrak p}$ for some $x \in \mathfrak a$, written without localizations:
every $y \in \mathfrak a$ has $sy \in Rx$ for some $s \in R \setminus \mathfrak p$. -/
def IsLocallyPrincipalAt (O : NumberFieldOrder K) (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)
    (P : Ideal O.toSubalgebra) : Prop :=
  ∃ x ∈ (I : Submodule O.toSubalgebra K), ∀ y ∈ (I : Submodule O.toSubalgebra K),
    ∃ s : O.toSubalgebra, s ∉ P ∧ s • y ∈ Submodule.span O.toSubalgebra {x}

/-- Dual basis data of a projective nonzero fractional ideal: finitely many generators `p` and scalars
`q p ∈ K` with `q p * I ⊆ R` and `∑ q p * p = 1`. -/
private theorem exists_dual_aux (O : NumberFieldOrder K)
    (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) (hI : I ≠ 0)
    [Module.Projective O.toSubalgebra (I : Submodule O.toSubalgebra K)] :
    ∃ (T : Finset ↥(I : Submodule O.toSubalgebra K)) (q : ↥(I : Submodule O.toSubalgebra K) → K),
      (∀ (p : ↥(I : Submodule O.toSubalgebra K)) (y : K), y ∈ I →
        ∃ r : O.toSubalgebra, algebraMap O.toSubalgebra K r = q p * y) ∧
      ∑ p ∈ T, q p * (p : K) = 1 := by
  obtain ⟨s, hs⟩ := Module.Projective.out (R := O.toSubalgebra)
    (P := ↥(I : Submodule O.toSubalgebra K))
  obtain ⟨y0, hy0I, hy0⟩ : ∃ y ∈ I, y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hI (FractionalIdeal.eq_zero_iff.mpr hcon)
  obtain ⟨d, hdS, hd⟩ := I.isFractional
  have hd0 : algebraMap O.toSubalgebra K d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O.toSubalgebra K)).mpr
      (nonZeroDivisors.ne_zero hdS)
  let y0' : ↥(I : Submodule O.toSubalgebra K) := ⟨y0, hy0I⟩
  let f : ↥(I : Submodule O.toSubalgebra K) →
      (↥(I : Submodule O.toSubalgebra K) →ₗ[O.toSubalgebra] O.toSubalgebra) :=
    fun p => (Finsupp.lapply p).comp s
  let q : ↥(I : Submodule O.toSubalgebra K) → K :=
    fun p => (algebraMap O.toSubalgebra K (f p y0')) / y0
  have hq : ∀ p (y : ↥(I : Submodule O.toSubalgebra K)),
      algebraMap O.toSubalgebra K (f p y) = q p * y := by
    intro p y
    obtain ⟨r0, hr0⟩ := hd y0 hy0I
    obtain ⟨r1, hr1⟩ := hd y y.2
    rw [Algebra.smul_def] at hr0 hr1
    have hmul : r0 • y = r1 • y0' := by
      apply Subtype.ext
      show algebraMap O.toSubalgebra K r0 * (y : K) = algebraMap O.toSubalgebra K r1 * y0
      rw [hr0, hr1]
      ring
    have h2 := congrArg (f p) hmul
    rw [map_smul, map_smul] at h2
    have hK := congrArg (algebraMap O.toSubalgebra K) h2
    simp only [smul_eq_mul, map_mul] at hK
    rw [hr0, hr1] at hK
    have h3 : algebraMap O.toSubalgebra K d *
        (algebraMap O.toSubalgebra K (f p y) * y0 -
          algebraMap O.toSubalgebra K (f p y0') * (y : K)) = 0 := by
      linear_combination hK
    have h4 := (mul_eq_zero.mp h3).resolve_left hd0
    show _ = (algebraMap O.toSubalgebra K (f p y0') / y0) * (y : K)
    field_simp
    linear_combination h4
  refine ⟨(s y0').support, q, fun p y hy => ⟨f p ⟨y, hy⟩, hq p ⟨y, hy⟩⟩, ?_⟩
  have h1 := congrArg (fun m : ↥(I : Submodule O.toSubalgebra K) => (m : K)) (hs y0')
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, id, Submodule.coe_sum,
    Submodule.coe_smul, Algebra.smul_def] at h1
  have h2 : (∑ p ∈ (s y0').support, q p * (p : K)) * y0 = 1 * y0 := by
    rw [Finset.sum_mul, one_mul]
    calc _ = ∑ p ∈ (s y0').support, algebraMap O.toSubalgebra K (s y0' p) * (p : K) := by
          apply Finset.sum_congr rfl
          intro p _
          have h5 : algebraMap O.toSubalgebra K (s y0' p) = q p * y0 := hq p y0'
          rw [h5]
          ring
      _ = y0 := h1
  exact mul_right_cancel₀ hy0 h2

private theorem locPrincipal_of_dual_aux (O : NumberFieldOrder K)
    (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)
    (T : Finset ↥(I : Submodule O.toSubalgebra K)) (q : ↥(I : Submodule O.toSubalgebra K) → K)
    (hq : ∀ (p : ↥(I : Submodule O.toSubalgebra K)) (y : K), y ∈ I →
        ∃ r : O.toSubalgebra, algebraMap O.toSubalgebra K r = q p * y)
    (hsum : ∑ p ∈ T, q p * (p : K) = 1) (P : Ideal O.toSubalgebra) (hP : P.IsMaximal) :
    IsLocallyPrincipalAt O I P := by
  have key : ∃ p ∈ T, ∃ r : O.toSubalgebra, algebraMap O.toSubalgebra K r = q p * p ∧ r ∉ P := by
    by_contra hcon
    push Not at hcon
    choose r hr using fun p : ↥(I : Submodule O.toSubalgebra K) => hq p p.1 p.2
    have h1 : ∑ p ∈ T, r p = 1 := by
      apply IsFractionRing.injective O.toSubalgebra K
      rw [map_sum, map_one, ← hsum]
      exact Finset.sum_congr rfl fun p _ => hr p
    have h2 : ∑ p ∈ T, r p ∈ P :=
      Ideal.sum_mem _ fun p hp => hcon p hp (r p) (hr p)
    rw [h1] at h2
    exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr h2)
  obtain ⟨p, -, r, hr, hrP⟩ := key
  refine ⟨p, p.2, fun y hy => ⟨r, hrP, ?_⟩⟩
  obtain ⟨r', hr'⟩ := hq p y hy
  rw [Submodule.mem_span_singleton]
  refine ⟨r', ?_⟩
  simp only [Algebra.smul_def]
  rw [hr', hr]
  ring

private theorem proper_of_locPrincipal_aux (O : NumberFieldOrder K)
    (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) (hI : I ≠ 0)
    (h : ∀ P : Ideal O.toSubalgebra, P.IsMaximal → IsLocallyPrincipalAt O I P) :
    O.IsProperFractionalIdeal I := by
  rw [O.isProperFractionalIdeal_iff]
  intro z hz
  by_contra hzO
  obtain ⟨y0, hy0I, hy0⟩ : ∃ y ∈ I, y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hI (FractionalIdeal.eq_zero_iff.mpr hcon)
  let A : Ideal O.toSubalgebra :=
    (1 : Submodule O.toSubalgebra K).comap (LinearMap.toSpanSingleton O.toSubalgebra K z)
  have hA : A ≠ ⊤ := by
    intro hA
    have h1 : (1 : O.toSubalgebra) ∈ A := hA ▸ Submodule.mem_top
    have h2 : (1 : O.toSubalgebra) • z ∈ (1 : Submodule O.toSubalgebra K) := h1
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp h2
    apply hzO
    have : z = (r : K) := by simpa using hr.symm
    rw [this]
    exact r.2
  obtain ⟨P, hP, hAP⟩ := Ideal.exists_le_maximal A hA
  obtain ⟨x, hxI, hx⟩ := h P hP
  have hx0 : x ≠ 0 := by
    intro hx0
    obtain ⟨s0, hs0P, hs0⟩ := hx y0 hy0I
    rw [hx0, Submodule.mem_span_singleton] at hs0
    obtain ⟨r0, hr0⟩ := hs0
    simp only [smul_zero, Algebra.smul_def, mul_zero] at hr0
    have h3 : algebraMap O.toSubalgebra K s0 = 0 := by
      rcases mul_eq_zero.mp hr0.symm with h | h
      · exact h
      · exact absurd h hy0
    have : s0 = 0 := (map_eq_zero_iff _ (IsFractionRing.injective O.toSubalgebra K)).mp h3
    exact hs0P (this ▸ P.zero_mem)
  obtain ⟨s, hsP, hs⟩ := hx (z * x) (hz x hxI)
  rw [Submodule.mem_span_singleton] at hs
  obtain ⟨r, hr⟩ := hs
  simp only [Algebra.smul_def] at hr
  have h4 : algebraMap O.toSubalgebra K s * z = algebraMap O.toSubalgebra K r := by
    apply mul_right_cancel₀ hx0
    linear_combination -hr
  have hsA : s ∈ A := by
    show s • z ∈ (1 : Submodule O.toSubalgebra K)
    rw [Submodule.mem_one]
    exact ⟨r, by rw [← h4, Algebra.smul_def]⟩
  exact hsP (hAP hsA)

/-- **Proposition 12.3** (Milne, corrected (c)): for a nonzero fractional ideal $\mathfrak a$ of an order $R$ in a
quadratic field, the following are equivalent: (a) $\mathfrak a$ is a projective $R$-module; (b)
$R = \{x\in K \mid x\mathfrak a\subseteq\mathfrak a\}$; (c) $\mathfrak a$ is locally principal at every maximal ideal
of $R$. -/
@[kb "milne2017mf" "Section 12, Prop. 12.3 (pdf p. 122), (c) corrected"]
theorem proper_tfae (hK : Module.finrank ℚ K = 2) (O : NumberFieldOrder K)
    (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) (hI : I ≠ 0) :
    [Module.Projective O.toSubalgebra (I : Submodule O.toSubalgebra K),
      O.IsProperFractionalIdeal I,
      ∀ P : Ideal O.toSubalgebra, P.IsMaximal → IsLocallyPrincipalAt O I P].TFAE := by
  tfae_have 1 → 3 := by
    intro h P hP
    obtain ⟨T, q, hq, hsum⟩ := exists_dual_aux O I hI
    exact locPrincipal_of_dual_aux O I T q hq hsum P hP
  tfae_have 3 → 2 := proper_of_locPrincipal_aux O I hI
  tfae_have 2 → 1 := by
    intro h
    have hU := (O.isProperFractionalIdeal_iff_isUnit_of_finrank_eq_two hK I).mp h
    have e : ((FractionalIdeal.unitsMulEquivSubmodule hU.unit : (Submodule O.toSubalgebra K)ˣ) :
        Submodule O.toSubalgebra K) = I.coeToSubmodule :=
      congrArg FractionalIdeal.coeToSubmodule hU.unit_spec
    exact Submodule.projective_of_isUnit (by rw [← e]; exact Units.isUnit _)
  tfae_finish

/-- **Proposition 12.4** (Milne): the product of proper ideals of a quadratic order is proper. -/
@[kb "milne2017mf" "Section 12, Prop. 12.4 (pdf p. 122)"]
theorem proper_mul (hK : Module.finrank ℚ K = 2) (O : NumberFieldOrder K)
    {I J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K} (hI : O.IsProperFractionalIdeal I)
    (hJ : O.IsProperFractionalIdeal J) : O.IsProperFractionalIdeal (I * J) :=
  O.isProperFractionalIdeal_of_isUnit
    ((hI.isUnit_of_finrank_eq_two hK).mul (hJ.isUnit_of_finrank_eq_two hK))

/-- **Proposition 12.4** (Milne): $R$ itself is a proper ideal, the identity for the multiplication. -/
@[kb "milne2017mf" "Section 12, Prop. 12.4 (pdf p. 122)"]
theorem proper_one (O : NumberFieldOrder K) : O.IsProperFractionalIdeal 1 :=
  O.isProperFractionalIdeal_one

/-- **Proposition 12.4** (Milne): every proper ideal of a quadratic order has a proper inverse. -/
@[kb "milne2017mf" "Section 12, Prop. 12.4 (pdf p. 122)"]
theorem proper_exists_inv (hK : Module.finrank ℚ K = 2) (O : NumberFieldOrder K)
    {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K} (hI : O.IsProperFractionalIdeal I) :
    ∃ J, O.IsProperFractionalIdeal J ∧ I * J = 1 := by
  obtain ⟨J, hJ⟩ := isUnit_iff_exists_inv.mp (hI.isUnit_of_finrank_eq_two hK)
  exact ⟨J, O.isProperFractionalIdeal_of_mul_eq_one (by rwa [mul_comm]), hJ⟩

/-- The symbol $(\tfrac Kp)$ of Remark 12.5 for a quadratic field $K$: $0$ if $p$ ramifies in $K$, $1$ if $p$ splits
(two primes above $p$), $-1$ if $p$ stays prime. -/
noncomputable def splittingSymbol (K : Type*) [Field K] [NumberField K] (p : ℕ) : ℤ :=
  open Classical in
  if ∃ P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K), 2 ≤ P.ramificationIdx ℤ then 0
  else if Nat.card ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) = 2 then 1 else -1

private theorem int_dvd_of_natCast_dvd_aux (hK : Module.finrank ℚ K = 2) {f : ℕ} {n : ℤ}
    (h : (f : 𝓞 K) ∣ (n : 𝓞 K)) : (f : ℤ) ∣ n := by
  obtain ⟨b, hb⟩ := (Module.Free.isUnimodular_one (R := ℤ) (A := 𝓞 K)).exists_basis_zero_eq
    (by rw [RingOfIntegers.rank, hK])
  obtain ⟨c, hc⟩ := h
  have hc' := congrArg (b.coord 0) hc
  have e1 : (n : 𝓞 K) = n • b 0 := by simp [hb]
  have e2 : (f : 𝓞 K) * c = (f : ℤ) • c := by simp
  rw [e1, e2, map_smul, map_smul] at hc'
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] at hc'
  exact ⟨b.coord 0 c, by simpa using hc'⟩

private theorem card_units_order_quot_aux (hK : Module.finrank ℚ K = 2) (O : NumberFieldOrder K) :
    Nat.card (O.toRingOfIntegers ⧸ O.conductor.comap
      (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K))ˣ = Nat.totient O.index := by
  have hpos : NeZero O.index := ⟨O.index_ne_zero⟩
  let J : Ideal O.toRingOfIntegers := O.conductor.comap
    (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K)
  let ψ : ℤ →+* O.toRingOfIntegers ⧸ J :=
    (Ideal.Quotient.mk J).comp (Int.castRingHom O.toRingOfIntegers)
  have hcond := O.conductor_eq_span_index hK
  have hmemJ : ∀ x : O.toRingOfIntegers, x ∈ J ↔ ((x : 𝓞 K) ∈ Ideal.span {(O.index : 𝓞 K)}) := by
    intro x
    rw [← hcond]
    rfl
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, y, hy⟩ := (O.mem_toRingOfIntegers_iff_exists_int_add_index_mul hK (x : 𝓞 K)).mp x.2
    refine ⟨a, ?_⟩
    show Ideal.Quotient.mk J (a : O.toRingOfIntegers) = Ideal.Quotient.mk J x
    rw [Ideal.Quotient.eq, hmemJ]
    rw [Ideal.mem_span_singleton]
    refine ⟨-y, ?_⟩
    rw [show (((a : O.toRingOfIntegers) - x : O.toRingOfIntegers) : 𝓞 K) = (a : 𝓞 K) - x by simp,
      hy]
    ring
  have hker : RingHom.ker ψ = Ideal.span {(O.index : ℤ)} := by
    ext n
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    show Ideal.Quotient.mk J (n : O.toRingOfIntegers) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, hmemJ, Ideal.mem_span_singleton]
    constructor
    · intro h
      have : ((n : O.toRingOfIntegers) : 𝓞 K) = (n : 𝓞 K) := by simp
      rw [this] at h
      exact int_dvd_of_natCast_dvd_aux hK h
    · rintro ⟨c, rfl⟩
      refine ⟨c, ?_⟩
      simp
  let e : ZMod O.index ≃+* O.toRingOfIntegers ⧸ J :=
    (Int.quotientSpanNatEquivZMod O.index).symm.trans
      ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj))
  rw [← Nat.card_congr (Units.mapEquiv e.toMulEquiv).toEquiv, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient]

private theorem local_prod_aux {ι : Type*} [Fintype ι] (e g : ι → ℕ) (p : ℕ) (hp : 2 ≤ p)
    (he : ∀ i, 1 ≤ e i) (hg : ∀ i, 1 ≤ g i) (hsum : ∑ i, e i * g i = 2) :
    ∏ i, (1 - ((p ^ g i : ℕ) : ℚ)⁻¹) = (1 - (p : ℚ)⁻¹) *
      (1 - (((if ∃ i, 2 ≤ e i then 0 else if Fintype.card ι = 2 then 1 else -1 : ℤ) : ℚ)) / p) := by
  classical
  have hp0 : (p : ℚ) ≠ 0 := by positivity
  have hcard : Fintype.card ι ≤ 2 := by
    rw [← hsum, Fintype.card_eq_sum_ones]
    exact Finset.sum_le_sum fun i _ => Nat.mul_pos (he i) (hg i)
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hsum
  have hc1 : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hcase : Fintype.card ι = 1 ∨ Fintype.card ι = 2 := by omega
  rcases hcase with h1 | h2
  · obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp h1
    have huniv : (Finset.univ : Finset ι) = {a} := by
      ext y; simp [ha y]
    rw [huniv, Finset.sum_singleton] at hsum
    rw [huniv, Finset.prod_singleton]
    have hea := he a
    have hga := hg a
    have hx : e a ≤ 2 := by nlinarith
    have hne2 : Fintype.card ι ≠ 2 := by omega
    have hcases : (e a = 1 ∧ g a = 2) ∨ (e a = 2 ∧ g a = 1) := by
      rcases (by omega : e a = 1 ∨ e a = 2) with h | h <;> rw [h] at hsum <;> omega
    rcases hcases with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
    · have hno : ¬∃ i, 2 ≤ e i := fun ⟨i, hi⟩ => by rw [ha i] at hi; omega
      rw [if_neg hno, if_neg hne2, h2']
      push_cast
      field_simp
      ring
    · have hyes : ∃ i, 2 ≤ e i := ⟨a, by omega⟩
      rw [if_pos hyes, h2']
      push_cast
      field_simp
      ring
  · obtain ⟨a, b, hab, hv⟩ := Finset.card_eq_two.mp
      (by rw [Finset.card_univ]; exact h2 : (Finset.univ : Finset ι).card = 2)
    have hsum' : e a * g a + e b * g b = 2 := by
      rw [hv, Finset.sum_pair hab] at hsum; exact hsum
    have ha1 := Nat.mul_pos (he a) (hg a)
    have hb1 := Nat.mul_pos (he b) (hg b)
    have hea : e a * g a = 1 := by omega
    have heb : e b * g b = 1 := by omega
    have hea' : e a = 1 := Nat.eq_one_of_mul_eq_one_right hea
    have hga' : g a = 1 := Nat.eq_one_of_mul_eq_one_left hea
    have heb' : e b = 1 := Nat.eq_one_of_mul_eq_one_right heb
    have hgb' : g b = 1 := Nat.eq_one_of_mul_eq_one_left heb
    have hno : ¬ ∃ i, 2 ≤ e i := by
      rintro ⟨i, hi⟩
      have : i = a ∨ i = b := by
        have : i ∈ ({a, b} : Finset ι) := hv ▸ Finset.mem_univ i
        simpa using this
      rcases this with rfl | rfl <;> omega
    rw [hv, Finset.prod_pair hab]
    simp only [hno, if_false, h2, if_true, hga', hgb']
    push_cast
    ring

private theorem local_factor_aux (hK : Module.finrank ℚ K = 2) (p : ℕ) (hp : p.Prime)
    [Fintype ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K))] :
    ∏ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
      (1 - ((p ^ q.1.inertiaDeg ℤ : ℕ) : ℚ)⁻¹) =
      (1 - (p : ℚ)⁻¹) * (1 - (splittingSymbol K p : ℚ) / p) := by
  classical
  have hpne : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
    simpa using hp.ne_zero
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpp.ne_zero).mpr hpp
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)
  have hrank : Module.finrank ℤ (𝓞 K) = 2 := by rw [RingOfIntegers.rank, hK]
  rw [hrank] at hsum
  have he : ∀ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K), 1 ≤ q.1.ramificationIdx ℤ := by
    intro q
    exact Ideal.ramificationIdx_pos_of_isDedekindDomain' q.1 hpne
  have hg : ∀ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K), 1 ≤ q.1.inertiaDeg ℤ := fun q =>
    Ideal.inertiaDeg_pos q.1 ℤ
  have := local_prod_aux (fun q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) => q.1.ramificationIdx ℤ)
    (fun q => q.1.inertiaDeg ℤ) p hp.two_le he hg hsum
  rw [this]
  unfold splittingSymbol
  have h1 : (∃ P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K), 2 ≤ P.ramificationIdx ℤ) ↔
      ∃ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K), 2 ≤ q.1.ramificationIdx ℤ :=
    ⟨fun ⟨P, hP, h⟩ => ⟨⟨P, hP⟩, h⟩, fun ⟨q, h⟩ => ⟨q.1, q.2, h⟩⟩
  have h2 : Nat.card ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) =
      Fintype.card ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) := Nat.card_eq_fintype_card
  simp only [h1, h2]

private theorem natCast_mem_of_liesOver_aux (p : ℕ) (P : Ideal (𝓞 K))
    (h : P.LiesOver (Ideal.span {(p : ℤ)})) : (p : 𝓞 K) ∈ P := by
  have h1 : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton_self _
  rw [h.over] at h1
  simpa using Ideal.mem_comap.mp h1

private theorem exists_prime_under_aux (n : ℕ) (hn : n ≠ 0) (P : Ideal (𝓞 K)) [hP : P.IsPrime]
    (hnP : (n : 𝓞 K) ∈ P) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ P.LiesOver (Ideal.span {(p : ℤ)}) := by
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal (P.under ℤ)).principal
  have hnq : (n : ℤ) ∈ P.under ℤ := by
    rw [Ideal.mem_comap]
    simpa using hnP
  have hq : (P.under ℤ).IsPrime := Ideal.IsPrime.comap _
  have ha' : P.under ℤ = Ideal.span {a} := ha
  have hnq' := hnq
  rw [ha', Ideal.mem_span_singleton] at hnq'
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hnq'
    exact hn hnq'
  have hpr : Prime a := by
    rw [ha'] at hq
    exact (Ideal.span_singleton_prime ha0).mp hq
  refine ⟨a.natAbs, Int.prime_iff_natAbs_prime.mp hpr, ?_, ⟨?_⟩⟩
  · exact Int.natAbs_dvd_natAbs.mpr hnq' |>.trans (by simp)
  · rw [Int.span_natAbs, ha']

private theorem prod_heightOne_aux (n : ℕ) (hn : n ≠ 0)
    [∀ p : ℕ, Fintype ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K))]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v, v ∈ S ↔ v.asIdeal ∣ Ideal.span {(n : 𝓞 K)}) :
    ∏ v ∈ S, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℚ)⁻¹) =
      ∏ p ∈ n.primeFactors, ∏ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
        (1 - ((p ^ q.1.inertiaDeg ℤ : ℕ) : ℚ)⁻¹) := by
  classical
  have hsig : ∏ p ∈ n.primeFactors, ∏ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
        (1 - ((p ^ q.1.inertiaDeg ℤ : ℕ) : ℚ)⁻¹) =
      ∏ x ∈ n.primeFactors.sigma (fun p => (Finset.univ :
          Finset ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)))),
        (1 - ((x.1 ^ x.2.1.inertiaDeg ℤ : ℕ) : ℚ)⁻¹) := by
    rw [Finset.prod_sigma]
  rw [hsig]
  symm
  have hpne : ∀ p : ℕ, p ≠ 0 → (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
    intro p hp
    simpa using hp
  refine Finset.prod_bij
    (fun x hx => (⟨x.2.1, x.2.2.1, Ideal.ne_bot_of_mem_primesOver
      (hpne x.1 (Nat.pos_of_mem_primeFactors (Finset.mem_sigma.mp hx).1).ne') x.2.2⟩ :
      IsDedekindDomain.HeightOneSpectrum (𝓞 K))) ?_ ?_ ?_ ?_
  · intro x hx
    have hxp : x.1 ∈ n.primeFactors := (Finset.mem_sigma.mp hx).1
    rw [hS, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    have h1 := natCast_mem_of_liesOver_aux x.1 x.2.1 x.2.2.2
    obtain ⟨c, hc⟩ := Nat.dvd_of_mem_primeFactors hxp
    show (n : 𝓞 K) ∈ x.2.1
    rw [hc]
    push_cast
    exact Ideal.mul_mem_right _ _ h1
  · intro x hx y hy hxy
    have hI : x.2.1 = y.2.1 := congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hxy
    have hxl : x.2.1.LiesOver (Ideal.span {(x.1 : ℤ)}) := x.2.2.2
    have hyl : y.2.1.LiesOver (Ideal.span {(y.1 : ℤ)}) := y.2.2.2
    have h2 : Ideal.span {(x.1 : ℤ)} = Ideal.span {(y.1 : ℤ)} := by
      rw [hxl.over, hyl.over, hI]
    have h3 : x.1 = y.1 := by
      have := Ideal.span_singleton_eq_span_singleton.mp h2
      have := Int.associated_iff_natAbs.mp this
      simpa using this
    exact Sigma.subtype_ext h3 hI
  · intro v hv
    obtain ⟨p, hp, hpn, hl⟩ := exists_prime_under_aux n hn v.asIdeal
      (by
        have := (Ideal.dvd_iff_le.mp ((hS v).mp hv))
        exact this (Ideal.mem_span_singleton_self _))
    refine ⟨⟨p, ⟨v.asIdeal, v.isPrime, hl⟩⟩, ?_, rfl⟩
    exact Finset.mem_sigma.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩, Finset.mem_univ _⟩
  · intro x hx
    have : x.2.1.LiesOver (Ideal.span {(x.1 : ℤ)}) := x.2.2.2
    have := Ideal.pow_inertiaDeg x.1 x.2.1
    simp only [← this]

private theorem finite_primesOver_aux (p : ℕ) :
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)).Finite := by
  by_cases hp0 : p = 0
  · subst hp0
    have : Ideal.span {((0 : ℕ) : ℤ)} = ⊥ := by simp
    rw [this, Ideal.primesOver_bot]
    exact Set.finite_singleton _
  by_cases hp : (Ideal.span {(p : ℤ)}).IsPrime
  · haveI := hp
    haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
      Ideal.IsPrime.isMaximal hp (by simpa using hp0)
    exact IsDedekindDomain.primesOver_finite _ _
  · have : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun P hP => hp ?_
      have hl : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
      haveI := hP.1
      rw [hl.over]
      exact Ideal.IsPrime.comap _
    rw [this]
    exact Set.finite_empty

/-- **Remark 12.5** (Milne; Shimura 1971, Exercise 4.12): the class number of an order $R$ of conductor $f$ in a
quadratic field $K$ is $h(R) = h\,f\,(\mathcal O_K^\times : R^\times)^{-1}\prod_{p\mid f}(1 - (\tfrac Kp)\tfrac1p)$,
with $h$ the class number of $\mathcal O_K$. -/
@[kb "milne2017mf" "Section 12, Rem. 12.5 (pdf p. 123)"]
theorem card_pic_formula (hK : Module.finrank ℚ K = 2) (O : NumberFieldOrder K) :
    (Nat.card (Pic O) : ℚ) =
      Nat.card (ClassGroup (𝓞 K)) * O.index /
          (Units.map (O.toRingOfIntegers.val : O.toRingOfIntegers →* 𝓞 K)).range.index *
        ∏ p ∈ O.index.primeFactors, (1 - (splittingSymbol K p : ℚ) / p) := by
  classical
  have hrank : Module.finrank ℤ (𝓞 K) = 2 := by rw [RingOfIntegers.rank, hK]
  have hn : O.index ≠ 0 := O.index_ne_zero
  letI : ∀ p : ℕ, Fintype ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) := fun p =>
    (finite_primesOver_aux (K := K) p).fintype
  have hcond := O.conductor_eq_span_index hK
  have hI0 : Ideal.span {(O.index : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  have hnorm : Ideal.absNorm (Ideal.span {(O.index : 𝓞 K)}) = O.index ^ 2 := by
    rw [Ideal.absNorm_span_singleton]
    have : (O.index : 𝓞 K) = algebraMap ℤ (𝓞 K) (O.index : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, hrank, Int.natAbs_pow]
    simp
  haveI hfin : Finite (𝓞 K ⧸ Ideal.span {(O.index : 𝓞 K)}) :=
    (Ideal.absNorm_ne_zero_iff _).mp (by rw [hnorm]; positivity)
  let S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
    (Ideal.finite_factors hI0).toFinset
  have hS : ∀ v, v ∈ S ↔ v.asIdeal ∣ Ideal.span {(O.index : 𝓞 K)} := by
    intro v
    simp [S]
  have hcount : (Nat.card (𝓞 K ⧸ O.conductor)ˣ : ℚ) = (O.index : ℚ) ^ 2 *
      ∏ p ∈ O.index.primeFactors, ((1 - (p : ℚ)⁻¹) * (1 - (splittingSymbol K p : ℚ) / p)) := by
    rw [hcond, Ideal.card_units_quotient_eq_absNorm_mul_prod _ hS, hnorm,
      prod_heightOne_aux O.index hn S hS]
    push_cast
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    have h := local_factor_aux hK p (Nat.prime_of_mem_primeFactors hp)
    push_cast at h
    exact h
  have htot : ((Nat.totient O.index : ℕ) : ℚ) = O.index * ∏ p ∈ O.index.primeFactors, (1 - (p : ℚ)⁻¹) :=
    Nat.totient_eq_mul_prod_factors _
  have htotpos : (0 : ℚ) < (Nat.totient O.index : ℕ) := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)
  have hmain := NumberFieldOrder.card_pic_mul_index_mul_card_units O
  rw [card_units_order_quot_aux hK O] at hmain
  have hmainQ : (Nat.card (Pic O) : ℚ) *
      ((Units.map (O.toRingOfIntegers.val : O.toRingOfIntegers →* 𝓞 K)).range.index : ℚ) *
        (Nat.totient O.index : ℕ) =
      Nat.card (ClassGroup (𝓞 K)) * ((Nat.card (𝓞 K ⧸ O.conductor)ˣ : ℕ) : ℚ) := by
    exact_mod_cast hmain
  have hidx : ((Units.map (O.toRingOfIntegers.val : O.toRingOfIntegers →* 𝓞 K)).range.index : ℚ)
      ≠ 0 := by
    have hpos : 0 < Nat.card (ClassGroup (𝓞 K)) * Nat.card (𝓞 K ⧸ O.conductor)ˣ := by
      have : Finite (𝓞 K ⧸ O.conductor) := hcond ▸ hfin
      exact Nat.mul_pos Nat.card_pos Nat.card_pos
    intro h0
    have h0' : (Units.map (O.toRingOfIntegers.val : O.toRingOfIntegers →* 𝓞 K)).range.index = 0 := by
      exact_mod_cast h0
    rw [h0', mul_zero, zero_mul] at hmain
    omega
  rw [hcount, htot, Finset.prod_mul_distrib] at hmainQ
  have hP1 : (O.index : ℚ) * ∏ p ∈ O.index.primeFactors, (1 - (p : ℚ)⁻¹) ≠ 0 := by
    rw [← htot]; exact htotpos.ne'
  rw [div_mul_eq_mul_div, eq_div_iff hidx]
  apply mul_right_cancel₀ hP1
  linear_combination hmainQ

end ModularFormsKB.Milne
