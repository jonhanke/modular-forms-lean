import ModularFormsKB.Miyake.Wave4.Notation
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Dimension
import TauCeti.NumberTheory.ModularForms.QExpansion.Positive
import TauCeti.NumberTheory.DirichletCharacter.Basic
import ModularFormsKB.Citation
/-!
# Miyake §4.7: the Eisenstein space `ℰ_k(N, χ)` (4.7.17) and Theorem 4.7.2 for `k ≥ 3`

Miyake, *Modular Forms* (Springer 1989), §4.7, pp. 178–181.

For a Dirichlet character `χ` modulo `N` with `χ(-1) = (-1)^k`, Miyake puts (4.7.17)

`ℰ_k(N, χ) = ⟨ f_k(lz; χ₁, χ₂) | l M₁ M₂ ∣ N, χ₁ χ₂ = χ, χ₁, χ₂ satisfy (4.7.2) ⟩`,

where `f_k(z; χ₁, χ₂) = Σ aₙ e^{2πinz}` is the modular form of Theorem 4.7.1, characterized by
`L(s; f) = L(s, χ₁) L(s - k + 1, χ₂)`, that is `aₙ = Σ_{0 < d ∣ n} χ₁(n/d) χ₂(d) d^{k-1}` for
`n ≥ 1`. For `k ≥ 3` condition (4.7.2) is case (ii): `χ₁` modulo `M₁` and `χ₂` modulo `M₂` are
primitive. (Case (i), both characters trivial, is the weight `k = 2`.)

**Definition.** `IsEisensteinGen k χ g` says that `g ∈ 𝒢_k(N, χ)` is `f_k(lz; χ₁, χ₂)` for such
data, through its Fourier coefficients at `n ≥ 1` (the coefficient of `e^{2πinz}` is `a_{n/l}`
when `l ∣ n` and `0` otherwise). In weight `k ≠ 0` a modular form is determined by those
coefficients (Tau Ceti's `TauCeti.ModularForm.eq_of_forall_pos_qExpansion_coeff_eq`), so this is
the book's `f_k(lz; χ₁, χ₂)` exactly, with no condition on the constant term. Miyake's
`ℰ_k(N, χ)` is `eisensteinSpace k χ`, the span of these forms in `𝒢_k(N, χ)`.

**Results (`k ≥ 3`, `χ(-1) = (-1)^k`).**
* `eisensteinSpace_eq_eisensteinSubspace`: `ℰ_k(N, χ)` is Tau Ceti's span
  `TauCeti.eisensteinSubspace` of the normalized raised Eisenstein series `E_k^{(ψ, φ, t)}`
  (whose positive coefficients are those of `f_k(tz; ψ, φ)`).
* `isCompl_eisensteinSpace_range_cuspSpace` (**Theorem 4.7.2**, in the form
  `𝒢_k(N, χ) = 𝒮_k(N, χ) ⊕ ℰ_k(N, χ)`): `ℰ_k(N, χ)` is a complement of the cusp forms. Miyake
  states `ℰ_k(N, χ) = 𝒩_k(N, χ)`, the orthogonal complement of `𝒮_k(N, χ)` under the Petersson
  product; the identification of the complement with `𝒩_k(N, χ)` is not formalized here (no
  Petersson product on `𝒢_k(N, χ) × 𝒮_k(N, χ)` with character is available; LE-MF-0227).
* `linearIndependent_isEisensteinGen` (proof of Theorem 4.7.2, 1°): the forms `f_k(lz; χ₁, χ₂)`
  are linearly independent; `finrank_eisensteinSpace` (1°): `dim ℰ_k(N, χ)` is the number of pairs
  `(χ'₁, χ'₂)` of Dirichlet characters modulo `M'₁` and `M'₂` (not necessarily primitive) with
  `M'₁ M'₂ = N` and `χ'₁ χ'₂ = χ`.
* (4.7.19) `eisensteinSpaceGamma1 k = ⊕_χ ℰ_k(N, χ)` inside `𝒢_k(Γ₁(N))`, the sum over `χ` modulo
  `N` with `χ(-1) = (-1)^k`; `isCompl_eisensteinSpaceGamma1_cuspFormSubmodule`:
  `𝒢_k(Γ₁(N)) = 𝒮_k(Γ₁(N)) ⊕ ℰ_k(Γ₁(N))`; and the table of `dim ℰ_k(Γ₁(N))` for `k ≥ 3`
  (`two_mul_finrank_eisensteinSpaceGamma1`, `finrank_eisensteinSpaceGamma1_four`, `_two`, `_one`),
  together with its equality with the number of cusps of `Γ₁(N)` for `N ∉ {1, 2, 4}`.

**Proofs.** Tau Ceti (pinned revision) proves the linear independence, spanning and counting of
its series (Diamond–Shurman, Theorem 4.5.2) by comparing with the cusps; Miyake's own proof of
Theorem 4.7.2 uses the dimension formula of Theorem 2.5.2 instead. The bijection of the count is
Tau Ceti's private `TauCeti.EisensteinSeries.CharIndex.toLevel` (`EisensteinSeries/Count.lean`),
copied with credit and restricted to a fixed nebentypus.

Weights `k = 1` and `k = 2` (cases 3° and 2° of the proof) are in `WeightOne.lean` and
`WeightTwo.lean`; in weight two `IsEisensteinGen` omits case (i) of (4.7.2), and Miyake's `ℰ₂(N, χ)`
is `eisensteinSpaceTwo` there.

**Not covered:** the identification with `𝒩_k(N, χ)` (LE-MF-0227), the Hecke stability of `ℰ_k(N, χ)` and the first step of the proof (LE-MF-0226) (a Hecke eigenform of `𝒢_k(N, χ)` with
the eigenvalues of some `f_k(z; χ₁, χ₂)` has no cuspidal part), which the comparison of dimensions
makes unnecessary here.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup DirichletCharacter
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave10

open ModularFormsKB.Miyake.Wave4 TauCeti.EisensteinSeries

variable {N : ℕ}

lemma dvd_left_of_level {l M₁ M₂ : ℕ} (h : l * (M₁ * M₂) ∣ N) : M₁ ∣ N :=
  (dvd_mul_right M₁ M₂).trans ((dvd_mul_left _ l).trans h)

lemma dvd_right_of_level {l M₁ M₂ : ℕ} (h : l * (M₁ * M₂) ∣ N) : M₂ ∣ N :=
  (dvd_mul_left M₂ M₁).trans ((dvd_mul_left _ l).trans h)

variable [NeZero N]

/-- The `n`-th Fourier coefficient (`n ≥ 1`) of Miyake's `f_k(lz; χ₁, χ₂)`: `a_{n/l}` with
`a_m = Σ_{0 < d ∣ m} χ₁(m/d) χ₂(d) d^{k-1}` (Theorem 4.7.1) when `l ∣ n`, and `0` otherwise. -/
def eisCoeff (k : ℕ) {M₁ M₂ : ℕ} (χ₁ : DirichletCharacter ℂ M₁) (χ₂ : DirichletCharacter ℂ M₂)
    (l n : ℕ) : ℂ :=
  if l ∣ n then ∑ d ∈ (n / l).divisors, χ₁ ((n / l) / d : ℕ) * χ₂ d * (d : ℂ) ^ (k - 1) else 0

/-- `g ∈ 𝒢_k(N, χ)` is one of Miyake's generators `f_k(lz; χ₁, χ₂)` of (4.7.17), for `k ≠ 2`
(for `k = 2` see `IsEisensteinGenTwo`, which adds case (i) of (4.7.2)):
primitive `χ₁` modulo `M₁`, `χ₂` modulo `M₂` ((4.7.2) (ii)), `l M₁ M₂ ∣ N`, `χ₁ χ₂ = χ` (both
raised to level `N`), and the Fourier coefficients of `g` at `n ≥ 1` are those of
`f_k(lz; χ₁, χ₂)`. -/
@[kb "miyake1989" "(4.7.17), p. 179"]
def IsEisensteinGen (k : ℕ) (χ : DirichletCharacter ℂ N) (g : modSpace (k : ℤ) χ) : Prop :=
  ∃ (l M₁ M₂ : ℕ) (χ₁ : DirichletCharacter ℂ M₁) (χ₂ : DirichletCharacter ℂ M₂)
    (h : l * (M₁ * M₂) ∣ N), χ₁.IsPrimitive ∧ χ₂.IsPrimitive ∧
    χ₁.changeLevel (dvd_left_of_level h) * χ₂.changeLevel (dvd_right_of_level h) = χ ∧
    ∀ n : ℕ, 0 < n → coeffMod g n = eisCoeff k χ₁ χ₂ l n

/-- **Miyake (4.7.17)**: the Eisenstein space `ℰ_k(N, χ)` (`k ≥ 3`), the span in `𝒢_k(N, χ)` of
the forms `f_k(lz; χ₁, χ₂)`. -/
@[kb "miyake1989" "(4.7.17), p. 179"]
def eisensteinSpace (k : ℕ) (χ : DirichletCharacter ℂ N) : Submodule ℂ (modSpace (k : ℤ) χ) :=
  Submodule.span ℂ {g | IsEisensteinGen k χ g}

omit [NeZero N] in
/-- The nebentypus of a Tau Ceti index is `χ` exactly when the product of its two characters,
raised to level `N`, is `χ`. -/
lemma nebentypus_eq_iff {k : ℕ} (a : CharIndex N k) (χ : DirichletCharacter ℂ N) :
    a.nebentypus = χ.toUnitHom ↔ a.psi.changeLevel a.u_dvd * a.phi.changeLevel a.v_dvd = χ := by
  rw [CharIndex.nebentypus_def]
  constructor
  · intro h
    apply MulChar.equivToUnitHom.injective
    rw [← MulChar.toUnitHom_eq, ← MulChar.toUnitHom_eq]
    exact h
  · rintro h
    rw [h]

lemma eisCoeff_eq_twistedDivisorSum (k : ℕ) {M₁ M₂ : ℕ} (χ₁ : DirichletCharacter ℂ M₁)
    (χ₂ : DirichletCharacter ℂ M₂) (l n : ℕ) :
    eisCoeff k χ₁ χ₂ l n =
      if l ∣ n then twistedDivisorSum (k - 1) χ₁ χ₂ (n / l) else 0 := by
  rw [eisCoeff, twistedDivisorSum_apply]

/-- Each Tau Ceti series of nebentypus `χ` is a generator `f_k(tz; ψ, φ)` of (4.7.17). -/
theorem isEisensteinGen_inCharSpace {k : ℕ} (hk : 3 ≤ k) {χ : DirichletCharacter ℂ N}
    (a : CharIndex N k) (ha : a.nebentypus = χ.toUnitHom) :
    IsEisensteinGen k χ (a.inCharSpace (by exact_mod_cast hk) ha) := by
  refine ⟨a.t, a.u, a.v, a.psi, a.phi, a.level_dvd, a.psi_primitive, a.phi_primitive,
    (nebentypus_eq_iff a χ).1 ha, fun n hn ↦ ?_⟩
  show (qExpansion 1 (a.form (by exact_mod_cast hk))).coeff n = _
  rw [CharIndex.qExpansion_form_coeff _ _ hn.ne', eisCoeff_eq_twistedDivisorSum]

omit [NeZero N] in
/-- The parity of a pair of characters with product `χ`. -/
lemma parity_of_mul_eq {k : ℕ} {M₁ M₂ : ℕ} {χ₁ : DirichletCharacter ℂ M₁}
    {χ₂ : DirichletCharacter ℂ M₂} {χ : DirichletCharacter ℂ N} (h₁ : M₁ ∣ N) (h₂ : M₂ ∣ N)
    (hprod : χ₁.changeLevel h₁ * χ₂.changeLevel h₂ = χ) (hχ : χ (-1) = (-1) ^ k) :
    χ₁ (-1) * χ₂ (-1) = (-1) ^ (k : ℤ) := by
  have h := congrArg (fun ψ : DirichletCharacter ℂ N ↦ ψ (-1)) hprod
  simp only [MulChar.coeToFun_mul, Pi.mul_apply, changeLevel_apply_neg_one] at h
  rw [h, hχ, zpow_natCast]

/-- Each generator `f_k(lz; χ₁, χ₂)` of (4.7.17) is a Tau Ceti series of nebentypus `χ`. -/
theorem IsEisensteinGen.exists_charIndex {k : ℕ} (hk : 3 ≤ k) {χ : DirichletCharacter ℂ N}
    (hχ : χ (-1) = (-1) ^ k) {g : modSpace (k : ℤ) χ} (hg : IsEisensteinGen k χ g) :
    ∃ (a : CharIndex N k) (ha : a.nebentypus = χ.toUnitHom),
      g = a.inCharSpace (by exact_mod_cast hk) ha := by
  obtain ⟨l, M₁, M₂, χ₁, χ₂, h, h₁, h₂, hprod, hcoeff⟩ := hg
  let a : CharIndex N k :=
    ⟨M₁, M₂, l, χ₁, χ₂, h₁, h₂, parity_of_mul_eq _ _ hprod hχ, h⟩
  have ha : a.nebentypus = χ.toUnitHom := (nebentypus_eq_iff a χ).2 hprod
  refine ⟨a, ha, Subtype.ext ?_⟩
  refine TauCeti.ModularForm.eq_of_forall_pos_qExpansion_coeff_eq one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map N) (by omega) fun n hn ↦ ?_
  have := hcoeff n hn
  rw [coeffMod] at this
  rw [this, CharIndex.coe_inCharSpace, CharIndex.qExpansion_form_coeff _ _ hn.ne',
    eisCoeff_eq_twistedDivisorSum]

/-- `ℰ_k(N, χ)` (4.7.17) is Tau Ceti's Eisenstein subspace of `𝒢_k(N, χ)`, for `k ≥ 3` and
`χ(-1) = (-1)^k`. -/
@[kb "miyake1989" "(4.7.17), p. 179"]
theorem eisensteinSpace_eq_eisensteinSubspace {k : ℕ} (hk : 3 ≤ k) {χ : DirichletCharacter ℂ N}
    (hχ : χ (-1) = (-1) ^ k) :
    eisensteinSpace k χ = TauCeti.eisensteinSubspace χ.toUnitHom (by exact_mod_cast hk) := by
  refine le_antisymm (Submodule.span_le.2 fun g hg ↦ ?_)
    (TauCeti.eisensteinSubspace_le _ _ fun a ha ↦
      Submodule.subset_span (isEisensteinGen_inCharSpace hk a ha))
  obtain ⟨a, ha, rfl⟩ := IsEisensteinGen.exists_charIndex hk hχ hg
  exact TauCeti.mem_eisensteinSubspace _ _ a ha

/-- **Miyake, Theorem 4.7.2** for `k ≥ 3`, as a decomposition: `𝒢_k(N, χ) = 𝒮_k(N, χ) ⊕ ℰ_k(N, χ)`,
the Eisenstein space `ℰ_k(N, χ)` of (4.7.17) being a complement of the cusp forms. (Miyake states
`ℰ_k(N, χ) = 𝒩_k(N, χ)`, the Petersson orthogonal complement of `𝒮_k(N, χ)`; see LE-MF-0227.) -/
@[kb "miyake1989" "Theorem 4.7.2, p. 179 (k >= 3, complement of the cusp forms)"]
theorem isCompl_eisensteinSpace_range_cuspSpace {k : ℕ} (hk : 3 ≤ k)
    {χ : DirichletCharacter ℂ N} (hχ : χ (-1) = (-1) ^ k) :
    IsCompl (eisensteinSpace k χ)
      (LinearMap.range (TauCeti.cuspToModFormCharSpace (k : ℤ) χ.toUnitHom)) := by
  rw [eisensteinSpace_eq_eisensteinSubspace hk hχ]
  exact TauCeti.isCompl_eisensteinSubspace_range_cuspToModFormCharSpace _ _

/-- **Miyake, proof of Theorem 4.7.2, 1°** (`k ≥ 3`): the forms `f_k(lz; χ₁, χ₂)` of (4.7.17)
are linearly independent (as a family indexed by themselves). -/
@[kb "miyake1989" "Theorem 4.7.2, proof, 1°, p. 179 (linear independence, k >= 3)"]
theorem linearIndependent_isEisensteinGen {k : ℕ} (hk : 3 ≤ k) {χ : DirichletCharacter ℂ N}
    (hχ : χ (-1) = (-1) ^ k) :
    LinearIndependent ℂ (fun g : {g : modSpace (k : ℤ) χ // IsEisensteinGen k χ g} ↦ g.1) := by
  have hk' : 3 ≤ (k : ℤ) := by exact_mod_cast hk
  have hli := CharIndex.linearIndependent_inCharSpace χ.toUnitHom hk'
  -- The generators are the range of the independent Tau Ceti family.
  have hrange : {g : modSpace (k : ℤ) χ | IsEisensteinGen k χ g} =
      Set.range fun a : {a : CharIndex N k // a.nebentypus = χ.toUnitHom} ↦
        a.1.inCharSpace hk' a.2 := by
    ext g
    refine ⟨fun hg ↦ ?_, ?_⟩
    · obtain ⟨a, ha, rfl⟩ := IsEisensteinGen.exists_charIndex hk hχ hg
      exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨⟨a, ha⟩, rfl⟩
      exact isEisensteinGen_inCharSpace hk a ha
  have := (linearIndepOn_id_range_iff hli.injective).2 hli
  rw [← hrange] at this
  exact this

/-! ### The dimension of `ℰ_k(N, χ)` (proof of Theorem 4.7.2, 1°)

The bijection below is Tau Ceti's `CharIndex.toLevel` (`EisensteinSeries/Count.lean`, private
there), copied with credit and restricted to the indices of a fixed nebentypus `χ`. -/

section Count

variable {k : ℕ}

/-- The level data of an index of nebentypus `χ`: the divisor `g = t u` of `N` and the two
characters raised to level `N`, factoring through `g` and `N / g`, with product `χ`. (After Tau
Ceti's `CharIndex.toLevel`.) -/
def toLevelChar (χ : DirichletCharacter ℂ N)
    (a : {a : CharIndex N k // a.nebentypus = χ.toUnitHom}) :
    Σ g : N.divisors, {p : DirichletCharacter ℂ N × DirichletCharacter ℂ N //
      p.1.FactorsThrough g ∧ p.2.FactorsThrough (N / g) ∧ p.1 * p.2 = χ} :=
  have hg : a.1.t * a.1.u ∣ N := (Dvd.intro _ (mul_assoc _ _ _)).trans a.1.level_dvd
  ⟨⟨a.1.t * a.1.u, Nat.mem_divisors.mpr ⟨hg, NeZero.ne N⟩⟩,
    ⟨(a.1.psi.changeLevel a.1.u_dvd, a.1.phi.changeLevel a.1.v_dvd),
      ⟨hg, a.1.psi.changeLevel (dvd_mul_left a.1.u a.1.t), changeLevel_trans _ _ _⟩,
      ⟨Nat.div_dvd_of_dvd hg,
        a.1.phi.changeLevel (Nat.dvd_div_of_mul_dvd (by rw [mul_assoc]; exact a.1.level_dvd)),
        changeLevel_trans _ _ _⟩,
      (nebentypus_eq_iff a.1 χ).1 a.2⟩⟩

theorem toLevelChar_injective (χ : DirichletCharacter ℂ N) :
    Function.Injective (toLevelChar (k := k) χ) := by
  intro a b h
  have hg : a.1.t * a.1.u = b.1.t * b.1.u := congrArg (fun x ↦ (x.1 : ℕ)) h
  have hpsi : a.1.psi.changeLevel a.1.u_dvd = b.1.psi.changeLevel b.1.u_dvd :=
    congrArg (fun x ↦ x.2.1.1) h
  have hu := CharIndex.u_eq_of_changeLevel_eq hpsi
  have hu₀ : 0 < b.1.u := Nat.pos_of_dvd_of_pos b.1.u_dvd (NeZero.pos N)
  exact Subtype.ext (CharIndex.eq_of_changeLevel_eq
    (Nat.eq_of_mul_eq_mul_right hu₀ (hu ▸ hg)) hpsi (congrArg (fun x ↦ x.2.1.2) h))

theorem toLevelChar_surjective {χ : DirichletCharacter ℂ N} (hχ : χ (-1) = (-1) ^ k) :
    Function.Surjective (toLevelChar (k := k) χ) := by
  rintro ⟨⟨g, hg⟩, ⟨⟨χ₁, χ₂⟩, h₁, h₂, hprod⟩⟩
  have hgN : g ∣ N := Nat.dvd_of_mem_divisors hg
  have hu : χ₁.conductor ∣ g := χ₁.conductor_dvd_of_mem_conductorSet h₁
  have hv : χ₂.conductor ∣ N / g := χ₂.conductor_dvd_of_mem_conductorSet h₂
  have hpar : χ₁ (-1) * χ₂ (-1) = (-1) ^ (k : ℤ) := by
    have h := congrArg (fun ψ : DirichletCharacter ℂ N ↦ ψ (-1)) hprod
    simp only [MulChar.coeToFun_mul, Pi.mul_apply] at h
    rw [h, hχ, zpow_natCast]
  let a : CharIndex N k := ⟨χ₁.conductor, χ₂.conductor, g / χ₁.conductor, χ₁.primitiveCharacter,
    χ₂.primitiveCharacter, χ₁.primitiveCharacter_isPrimitive, χ₂.primitiveCharacter_isPrimitive,
    by rwa [← changeLevel_apply_neg_one χ₁.conductor_dvd_level,
      ← changeLevel_apply_neg_one χ₂.conductor_dvd_level, changeLevel_primitiveCharacter,
      changeLevel_primitiveCharacter],
    by
      rw [← mul_assoc, Nat.div_mul_cancel hu]
      exact (mul_dvd_mul_left g hv).trans (dvd_of_eq (Nat.mul_div_cancel' hgN))⟩
  have ha : a.nebentypus = χ.toUnitHom := by
    rw [nebentypus_eq_iff]
    show χ₁.primitiveCharacter.changeLevel χ₁.conductor_dvd_level *
      χ₂.primitiveCharacter.changeLevel χ₂.conductor_dvd_level = χ
    rw [changeLevel_primitiveCharacter, changeLevel_primitiveCharacter, hprod]
  refine ⟨⟨a, ha⟩, ?_⟩
  exact Sigma.subtype_ext (Subtype.ext (Nat.div_mul_cancel hu))
    (Prod.ext (changeLevel_primitiveCharacter χ₁) (changeLevel_primitiveCharacter χ₂))

/-- Pairs at level `N` factoring through `g` and `N / g` with product `χ` are the raises of the
pairs modulo `g` and `N / g` with product `χ`. -/
def factorsThroughPairEquiv {g : ℕ} (hg : g ∣ N) (χ : DirichletCharacter ℂ N) :
    {p : DirichletCharacter ℂ N × DirichletCharacter ℂ N //
      p.1.FactorsThrough g ∧ p.2.FactorsThrough (N / g) ∧ p.1 * p.2 = χ} ≃
    {q : DirichletCharacter ℂ g × DirichletCharacter ℂ (N / g) //
      q.1.changeLevel hg * q.2.changeLevel (Nat.div_dvd_of_dvd hg) = χ} where
  toFun p := ⟨(p.2.1.χ₀, p.2.2.1.χ₀), by
    rw [← p.2.1.eq_changeLevel, ← p.2.2.1.eq_changeLevel]
    exact p.2.2.2⟩
  invFun q := ⟨(q.1.1.changeLevel hg, q.1.2.changeLevel (Nat.div_dvd_of_dvd hg)),
    changeLevel_factorsThrough _ _, changeLevel_factorsThrough _ _, q.2⟩
  left_inv p := Subtype.ext (Prod.ext p.2.1.eq_changeLevel.symm p.2.2.1.eq_changeLevel.symm)
  right_inv q := Subtype.ext (Prod.ext
    (changeLevel_injective hg (changeLevel_factorsThrough q.1.1 hg).eq_changeLevel).symm
    (changeLevel_injective (Nat.div_dvd_of_dvd hg)
      (changeLevel_factorsThrough q.1.2 (Nat.div_dvd_of_dvd hg)).eq_changeLevel).symm)

/-- The number of Tau Ceti indices of nebentypus `χ` is Miyake's count of pairs `(χ'₁, χ'₂)`. -/
theorem card_charIndex_nebentypus {χ : DirichletCharacter ℂ N} (hχ : χ (-1) = (-1) ^ k) :
    Nat.card {a : CharIndex N k // a.nebentypus = χ.toUnitHom} =
      ∑ g : N.divisors, Nat.card {q : DirichletCharacter ℂ g × DirichletCharacter ℂ (N / g) //
        q.1.changeLevel (Nat.dvd_of_mem_divisors g.2) *
          q.2.changeLevel (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors g.2)) = χ} := by
  rw [Nat.card_eq_of_bijective _ ⟨toLevelChar_injective χ, toLevelChar_surjective hχ⟩,
    Nat.card_sigma]
  exact Finset.sum_congr rfl fun g _ ↦
    Nat.card_congr (factorsThroughPairEquiv (Nat.dvd_of_mem_divisors g.2) χ)

end Count

/-- **Miyake, proof of Theorem 4.7.2, 1°** (`k ≥ 3`): `dim ℰ_k(N, χ)` is the number of pairs
`(χ'₁, χ'₂)` of Dirichlet characters modulo `M'₁` and `M'₂` (not necessarily primitive) with
`M'₁ M'₂ = N` and `χ'₁ χ'₂ = χ`; here `M'₁ = g` runs over the divisors of `N` and `M'₂ = N / g`. -/
@[kb "miyake1989" "Theorem 4.7.2, proof, 1°, p. 180 (dimension, k >= 3)"]
theorem finrank_eisensteinSpace {k : ℕ} (hk : 3 ≤ k) {χ : DirichletCharacter ℂ N}
    (hχ : χ (-1) = (-1) ^ k) :
    Module.finrank ℂ (eisensteinSpace k χ) =
      ∑ g : N.divisors, Nat.card {q : DirichletCharacter ℂ g × DirichletCharacter ℂ (N / g) //
        q.1.changeLevel (Nat.dvd_of_mem_divisors g.2) *
          q.2.changeLevel (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors g.2)) = χ} := by
  rw [eisensteinSpace_eq_eisensteinSubspace hk hχ, TauCeti.finrank_eisensteinSubspace,
    card_charIndex_nebentypus hχ]

/-! ### `ℰ_k(Γ₁(N))` (4.7.19) and its dimension -/

/-- **Miyake (4.7.19)** for the Eisenstein spaces: `ℰ_k(Γ₁(N)) = ⊕_χ ℰ_k(N, χ)` inside
`𝒢_k(Γ₁(N))`, the sum over the Dirichlet characters `χ` modulo `N` with `χ(-1) = (-1)^k`. (The sum
is direct by the independence of the character spaces.) -/
@[kb "miyake1989" "(4.7.19), p. 180"]
def eisensteinSpaceGamma1 (k : ℕ) : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨆ (χ : DirichletCharacter ℂ N) (_ : χ (-1) = (-1) ^ k),
    (eisensteinSpace k χ).map (modSpace (k : ℤ) χ).subtype

/-- `ℰ_k(Γ₁(N))` is Tau Ceti's Eisenstein subspace of `𝒢_k(Γ₁(N))`, for `k ≥ 3`. -/
theorem eisensteinSpaceGamma1_eq {k : ℕ} (hk : 3 ≤ k) :
    eisensteinSpaceGamma1 (N := N) k =
      congruenceEisensteinSubspace (Gamma_le_Gamma1 N) (by exact_mod_cast hk) := by
  have hk' : 3 ≤ (k : ℤ) := by exact_mod_cast hk
  rw [← span_range_form_eq_congruenceEisensteinSubspace hk']
  refine le_antisymm (iSup₂_le fun χ hχ ↦ ?_) (Submodule.span_le.2 ?_)
  · rw [eisensteinSpace_eq_eisensteinSubspace hk hχ, TauCeti.eisensteinSubspace_def,
      Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨a, rfl⟩
  · rintro _ ⟨a, rfl⟩
    set χ : DirichletCharacter ℂ N := a.psi.changeLevel a.u_dvd * a.phi.changeLevel a.v_dvd
    have ha : a.nebentypus = χ.toUnitHom := (nebentypus_eq_iff a χ).2 rfl
    have hχ : χ (-1) = (-1) ^ k := by
      simp only [χ, MulChar.coeToFun_mul, Pi.mul_apply, changeLevel_apply_neg_one]
      rw [a.parity, zpow_natCast]
    refine Submodule.mem_iSup_of_mem χ (Submodule.mem_iSup_of_mem hχ ?_)
    refine ⟨a.inCharSpace hk' ha, ?_, rfl⟩
    rw [eisensteinSpace_eq_eisensteinSubspace hk hχ]
    exact TauCeti.mem_eisensteinSubspace _ _ a ha

/-- **Miyake, Theorem 4.7.2**, end of the proof, for `k ≥ 3`: `𝒢_k(Γ₁(N)) = 𝒮_k(Γ₁(N)) ⊕ ℰ_k(Γ₁(N))`
(the book's `ℰ_k(Γ₁(N)) = 𝒩_k(Γ₁(N))`, with the complement taken in the sense of linear algebra). -/
@[kb "miyake1989" "Theorem 4.7.2, proof, p. 181 (Gamma_1(N), k >= 3, complement)"]
theorem isCompl_eisensteinSpaceGamma1_cuspFormSubmodule {k : ℕ} (hk : 3 ≤ k) :
    IsCompl (eisensteinSpaceGamma1 (N := N) k)
      (cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) k) := by
  rw [eisensteinSpaceGamma1_eq hk]
  exact isCompl_congruenceEisensteinSubspace_cuspFormSubmodule _ _

theorem finrank_eisensteinSpaceGamma1 {k : ℕ} (hk : 3 ≤ k) :
    Module.finrank ℂ (eisensteinSpaceGamma1 (N := N) k) = Nat.card (CharIndex N k) := by
  rw [eisensteinSpaceGamma1_eq hk, finrank_congruenceEisensteinSubspace]

/-- **Miyake, proof of Theorem 4.7.2**, the dimension table (p. 181), `k ≥ 3`, `N ≥ 3`, `N ≠ 4`:
`dim ℰ_k(Γ₁(N)) = ½ Σ_{M ∣ N} φ(M) φ(N/M)`. -/
@[kb "miyake1989" "Theorem 4.7.2, proof, p. 181 (dim E_k(Gamma_1(N)), k >= 3, N >= 3, N != 4)"]
theorem two_mul_finrank_eisensteinSpaceGamma1 {k : ℕ} (hk : 3 ≤ k) (hN : 3 ≤ N) (hN4 : N ≠ 4) :
    2 * Module.finrank ℂ (eisensteinSpaceGamma1 (N := N) k) =
      ∑ M ∈ N.divisors, M.totient * (N / M).totient := by
  rw [finrank_eisensteinSpaceGamma1 hk, CharIndex.two_mul_card (by omega) hN4]

/-- For `k ≥ 3` and `N ∉ {1, 2, 4}`, `dim ℰ_k(Γ₁(N))` is the number of cusps of `Γ₁(N)` (the
comparison Miyake makes through Theorems 4.2.9 and 2.5.2). -/
theorem finrank_eisensteinSpaceGamma1_eq_card_cusps {k : ℕ} (hk : 3 ≤ k) (hN : 3 ≤ N)
    (hN4 : N ≠ 4) :
    Module.finrank ℂ (eisensteinSpaceGamma1 (N := N) k) =
      Nat.card ((Gamma1 N).map sl2zToPSL2R).CuspOrbit := by
  rw [finrank_eisensteinSpaceGamma1 hk, CharIndex.card_eq_card_cuspOrbit_Gamma1 (by omega) hN4]

/-- **Miyake, proof of Theorem 4.7.2**, the dimension table (p. 181) at `N = 4`, `k ≥ 3`:
`3` for `k` even, `2` for `k` odd. -/
@[kb "miyake1989" "Theorem 4.7.2, proof, p. 181 (dim E_k(Gamma_1(4)), k >= 3)"]
theorem finrank_eisensteinSpaceGamma1_four {k : ℕ} (hk : 3 ≤ k) :
    Module.finrank ℂ (eisensteinSpaceGamma1 (N := 4) k) = if Even k then 3 else 2 := by
  rw [finrank_eisensteinSpaceGamma1 hk, CharIndex.card_four]

/-- **Miyake, proof of Theorem 4.7.2**, the dimension table (p. 181) at `N = 2`, `k ≥ 3`:
`2` for `k` even, `0` for `k` odd. -/
@[kb "miyake1989" "Theorem 4.7.2, proof, p. 181 (dim E_k(Gamma_1(2)), k >= 3)"]
theorem finrank_eisensteinSpaceGamma1_two {k : ℕ} (hk : 3 ≤ k) :
    Module.finrank ℂ (eisensteinSpaceGamma1 (N := 2) k) = if Even k then 2 else 0 := by
  rw [finrank_eisensteinSpaceGamma1 hk, CharIndex.card_two]

/-- **Miyake, proof of Theorem 4.7.2**, the dimension table (p. 181) at `N = 1`, `k ≥ 3`:
`1` for `k` even, `0` for `k` odd. -/
@[kb "miyake1989" "Theorem 4.7.2, proof, p. 181 (dim E_k(Gamma_1(1)), k >= 3)"]
theorem finrank_eisensteinSpaceGamma1_one {k : ℕ} (hk : 3 ≤ k) :
    Module.finrank ℂ (eisensteinSpaceGamma1 (N := 1) k) = if Even k then 1 else 0 := by
  rw [finrank_eisensteinSpaceGamma1 hk, CharIndex.card_one]

end ModularFormsKB.Miyake.Wave10
