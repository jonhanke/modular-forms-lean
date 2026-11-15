import ModularFormsKB.Miyake.Wave10.EisensteinSpace
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.Bounds

/-!
# Miyake §4.7 in weight one: `ℰ₁(N, χ)`, the proof of Theorem 4.7.2, 3°, and Theorem 4.7.3

Miyake, *Modular Forms* (Springer 1989), §4.7, pp. 179–182.

In weight `k = 1` condition (4.7.2) is again case (ii) (both characters primitive), so
`ℰ₁(N, χ) = eisensteinSpace 1 χ` with the generators `f₁(lz; χ₁, χ₂)` of
`ModularFormsKB.Miyake.Wave10.IsEisensteinGen` (coefficients `Σ_{d ∣ m} χ₁(m/d) χ₂(d)`).

* `eisensteinSpace_one_eq`: `ℰ₁(N, χ)` is Tau Ceti's `TauCeti.weightOneEisensteinSubspace`.
* `two_mul_finrank_eisensteinSpace_one` (proof of Theorem 4.7.2, 3°): since
  `f₁(z; χ₁, χ₂) = f₁(z; ψ₁, ψ₂)` exactly when `{χ₁, χ₂} = {ψ₁, ψ₂}`
  (`isEisensteinGen_one_eq_iff`), `dim ℰ₁(N, χ) = ½ #{(χ'₁, χ'₂) | χ'₁ χ'₂ = χ, M'₁ M'₂ = N}`;
  and `ℰ₁(N, χ) ≠ {0}` forces `N ≥ 3` (`three_le_of_eisensteinSpace_one_ne_bot`).
* `eisensteinSpaceGamma1_one_eq` and the weight-one rows of the dimension table of
  `ℰ₁(Γ₁(N))` (p. 181): `½ Σ_{M ∣ N} φ(M) φ(N/M)` for `N ≥ 3`, `N ≠ 4`; `1` for `N = 4`; `0` for
  `N ≤ 2`.
* `coeffMod_isBigO_of_mem_eisensteinSpace_one` (**Theorem 4.7.3** for `k = 1`): the Fourier
  coefficients of every `f ∈ ℰ₁(N, χ)` are `O(n^ε)` for every `ε > 0`.

Miyake's identification `ℰ₁(N, χ) = 𝒩₁(N, χ)` (the statement of Theorem 4.7.2 in weight one) is
not formalized (no Petersson product with character on `𝒢₁(N, χ) × 𝒮₁(N, χ)`; LE-MF-0227).

Proofs: Tau Ceti's weight-one Eisenstein series `E₁^{ψ, φ, t}` (pinned revision), with the
coefficients, the exchange relation, the dimension count and the divisor bound.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup DirichletCharacter
open Filter Asymptotics
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave10

open ModularFormsKB.Miyake.Wave4 TauCeti.EisensteinSeries

variable {N : ℕ} [NeZero N]

/-- Each Tau Ceti weight-one series of nebentypus `χ` is a generator `f₁(tz; ψ, φ)`. -/
theorem isEisensteinGen_weightOneInCharSpace {χ : DirichletCharacter ℂ N} (a : CharIndex N 1)
    (ha : a.nebentypus = χ.toUnitHom) :
    IsEisensteinGen 1 χ (a.weightOneInCharSpace ha) := by
  refine ⟨a.t, a.u, a.v, a.psi, a.phi, a.level_dvd, a.psi_primitive, a.phi_primitive,
    (nebentypus_eq_iff a χ).1 ha, fun n hn ↦ ?_⟩
  show (qExpansion 1 a.weightOneForm).coeff n = _
  rw [CharIndex.qExpansion_weightOneForm_coeff _ hn.ne', eisCoeff_eq_twistedDivisorSum]

/-- Each weight-one generator `f₁(lz; χ₁, χ₂)` is a Tau Ceti weight-one series. -/
theorem IsEisensteinGen.exists_charIndex_one {χ : DirichletCharacter ℂ N} (hχ : χ (-1) = -1)
    {g : modSpace (1 : ℕ) χ} (hg : IsEisensteinGen 1 χ g) :
    ∃ (a : CharIndex N 1) (ha : a.nebentypus = χ.toUnitHom), g = a.weightOneInCharSpace ha := by
  obtain ⟨l, M₁, M₂, χ₁, χ₂, h, h₁, h₂, hprod, hcoeff⟩ := hg
  let a : CharIndex N 1 :=
    ⟨M₁, M₂, l, χ₁, χ₂, h₁, h₂, parity_of_mul_eq _ _ hprod (by rw [hχ, pow_one]), h⟩
  have ha : a.nebentypus = χ.toUnitHom := (nebentypus_eq_iff a χ).2 hprod
  refine ⟨a, ha, Subtype.ext ?_⟩
  refine TauCeti.ModularForm.eq_of_forall_pos_qExpansion_coeff_eq one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map N) one_ne_zero fun n hn ↦ ?_
  have := hcoeff n hn
  rw [coeffMod] at this
  rw [this, CharIndex.coe_weightOneInCharSpace, CharIndex.qExpansion_weightOneForm_coeff _ hn.ne',
    eisCoeff_eq_twistedDivisorSum]

/-- `ℰ₁(N, χ)` (4.7.17) is Tau Ceti's weight-one Eisenstein subspace of `𝒢₁(N, χ)`. -/
@[kb "miyake1989" "(4.7.17), p. 179 (k = 1)"]
theorem eisensteinSpace_one_eq {χ : DirichletCharacter ℂ N} (hχ : χ (-1) = -1) :
    eisensteinSpace 1 χ = TauCeti.weightOneEisensteinSubspace χ.toUnitHom := by
  refine le_antisymm (Submodule.span_le.2 fun g hg ↦ ?_)
    (TauCeti.weightOneEisensteinSubspace_le _ fun a ha ↦
      Submodule.subset_span (isEisensteinGen_weightOneInCharSpace a ha))
  obtain ⟨a, ha, rfl⟩ := IsEisensteinGen.exists_charIndex_one hχ hg
  exact TauCeti.mem_weightOneEisensteinSubspace _ a ha

/-- **Miyake, proof of Theorem 4.7.2, 3°**: `f₁(lz; χ₁, χ₂) = f₁(l'z; ψ₁, ψ₂)` exactly when the
data agree up to exchanging the two characters (stated for Tau Ceti's indices `(χ₁, χ₂, l)`). -/
@[kb "miyake1989" "Theorem 4.7.2, proof, 3°, p. 180 (f_1(z; chi_1, chi_2) = f_1(z; chi_2, chi_1))"]
theorem isEisensteinGen_one_eq_iff {a b : CharIndex N 1} :
    a.weightOneForm = b.weightOneForm ↔ b = a ∨ b = a.swap :=
  CharIndex.weightOneForm_eq_weightOneForm_iff

/-- **Miyake, proof of Theorem 4.7.2, 3°**: `dim ℰ₁(N, χ)` is half the number of pairs
`(χ'₁, χ'₂)` of Dirichlet characters modulo `M'₁` and `M'₂` with `M'₁ M'₂ = N` and
`χ'₁ χ'₂ = χ` (`M'₁ = g` runs over the divisors of `N`). -/
@[kb "miyake1989" "Theorem 4.7.2, proof, 3°, p. 180 (dimension, k = 1)"]
theorem two_mul_finrank_eisensteinSpace_one {χ : DirichletCharacter ℂ N} (hχ : χ (-1) = -1) :
    2 * Module.finrank ℂ (eisensteinSpace 1 χ) =
      ∑ g : N.divisors, Nat.card {q : DirichletCharacter ℂ g × DirichletCharacter ℂ (N / g) //
        q.1.changeLevel (Nat.dvd_of_mem_divisors g.2) *
          q.2.changeLevel (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors g.2)) = χ} := by
  rw [eisensteinSpace_one_eq hχ]
  exact (TauCeti.two_mul_finrank_weightOneEisensteinSubspace _).trans
    (card_charIndex_nebentypus (by rw [hχ, pow_one]))

/-- **Miyake, proof of Theorem 4.7.2, 3°**: if `ℰ₁(N, χ) ≠ {0}` then `N ≥ 3` (and `χ(-1) = -1`,
which is assumed here as in the book). -/
@[kb "miyake1989" "Theorem 4.7.2, proof, 3°, p. 180 (E_1(N, chi) != 0 implies N >= 3)"]
theorem three_le_of_eisensteinSpace_one_ne_bot {χ : DirichletCharacter ℂ N} (hχ : χ (-1) = -1)
    (hne : eisensteinSpace 1 χ ≠ ⊥) : 3 ≤ N := by
  rw [eisensteinSpace_one_eq hχ] at hne
  by_contra hN
  have hfin : Module.finrank ℂ (TauCeti.weightOneEisensteinSubspace χ.toUnitHom) ≠ 0 :=
    fun h ↦ hne (Submodule.finrank_eq_zero.mp h)
  have h2 := TauCeti.two_mul_finrank_weightOneEisensteinSubspace χ.toUnitHom
  have hpos : 0 < Nat.card {a : CharIndex N 1 // a.nebentypus = χ.toUnitHom} := by omega
  obtain ⟨⟨a, -⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  have hcard : 0 < Nat.card (CharIndex N 1) := Nat.card_pos_iff.mpr ⟨⟨a⟩, inferInstance⟩
  have hN0 : N ≠ 0 := NeZero.ne N
  obtain rfl | rfl : N = 1 ∨ N = 2 := by omega
  · rw [CharIndex.card_one] at hcard; simp at hcard
  · rw [CharIndex.card_two] at hcard; simp at hcard

/-! ### `ℰ₁(Γ₁(N))` and its dimension -/

/-- `ℰ₁(Γ₁(N))` (4.7.19) is the span of all of Tau Ceti's weight-one series. -/
theorem eisensteinSpaceGamma1_one_eq :
    eisensteinSpaceGamma1 (N := N) 1 =
      Submodule.span ℂ (Set.range (CharIndex.weightOneForm (N := N))) := by
  refine le_antisymm (iSup₂_le fun χ hχ ↦ ?_) (Submodule.span_le.2 ?_)
  · rw [pow_one] at hχ
    rw [eisensteinSpace_one_eq hχ, TauCeti.weightOneEisensteinSubspace_def,
      Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨a, rfl⟩
  · rintro _ ⟨a, rfl⟩
    set χ : DirichletCharacter ℂ N := a.psi.changeLevel a.u_dvd * a.phi.changeLevel a.v_dvd
    have ha : a.nebentypus = χ.toUnitHom := (nebentypus_eq_iff a χ).2 rfl
    have hχ : χ (-1) = -1 := by
      simp only [χ, MulChar.coeToFun_mul, Pi.mul_apply, changeLevel_apply_neg_one]
      simpa using a.parity
    refine Submodule.mem_iSup_of_mem χ (Submodule.mem_iSup_of_mem (by rw [hχ, pow_one]) ?_)
    refine ⟨a.weightOneInCharSpace ha, ?_, rfl⟩
    rw [eisensteinSpace_one_eq hχ]
    exact TauCeti.mem_weightOneEisensteinSubspace _ a ha

theorem two_mul_finrank_eisensteinSpaceGamma1_one_eq_card :
    2 * Module.finrank ℂ (eisensteinSpaceGamma1 (N := N) 1) = Nat.card (CharIndex N 1) := by
  rw [eisensteinSpaceGamma1_one_eq]
  exact two_mul_finrank_span_range_weightOneForm

/-- **Miyake, proof of Theorem 4.7.2**, the dimension table (p. 181), `k = 1`, `N ≥ 3`, `N ≠ 4`:
`dim ℰ₁(Γ₁(N)) = ½ Σ_{M ∣ N} φ(M) φ(N/M)`. -/
@[kb "miyake1989" "Theorem 4.7.2, proof, p. 181 (dim E_1(Gamma_1(N)), N >= 3, N != 4)"]
theorem four_mul_finrank_eisensteinSpaceGamma1_one (hN : 3 ≤ N) (hN4 : N ≠ 4) :
    4 * Module.finrank ℂ (eisensteinSpaceGamma1 (N := N) 1) =
      ∑ M ∈ N.divisors, M.totient * (N / M).totient := by
  rw [← CharIndex.two_mul_card (k := 1) (by omega) hN4, ← two_mul_finrank_eisensteinSpaceGamma1_one_eq_card]
  ring

/-- **Miyake, proof of Theorem 4.7.2**, the dimension table (p. 181) at `N = 4`, `k = 1`: `1`. -/
@[kb "miyake1989" "Theorem 4.7.2, proof, p. 181 (dim E_1(Gamma_1(4)) = 1)"]
theorem finrank_eisensteinSpaceGamma1_one_four :
    Module.finrank ℂ (eisensteinSpaceGamma1 (N := 4) 1) = 1 := by
  have h := two_mul_finrank_eisensteinSpaceGamma1_one_eq_card (N := 4)
  rw [CharIndex.card_four] at h
  simp at h
  omega

/-- **Miyake, proof of Theorem 4.7.2**, the dimension table (p. 181) at `N ≤ 2`, `k = 1`: `0`. -/
@[kb "miyake1989" "Theorem 4.7.2, proof, p. 181 (dim E_1(Gamma_1(N)) = 0 for N <= 2)"]
theorem finrank_eisensteinSpaceGamma1_one_of_le_two (hN : N ≤ 2) :
    Module.finrank ℂ (eisensteinSpaceGamma1 (N := N) 1) = 0 := by
  have h := two_mul_finrank_eisensteinSpaceGamma1_one_eq_card (N := N)
  have hN0 : N ≠ 0 := NeZero.ne N
  obtain rfl | rfl : N = 1 ∨ N = 2 := by omega
  · rw [CharIndex.card_one] at h; simp only [Nat.not_even_one, ↓reduceIte] at h; omega
  · rw [CharIndex.card_two] at h; simp only [Nat.not_even_one, ↓reduceIte] at h; omega

/-- **Miyake, Theorem 4.7.3** for `k = 1`: if `f = Σ aₙ e^{2πinz} ∈ ℰ₁(N, χ)`, then
`aₙ = O(n^ε)` for every `ε > 0`. -/
@[kb "miyake1989" "Theorem 4.7.3, p. 181 (k = 1)"]
theorem coeffMod_isBigO_of_mem_eisensteinSpace_one {χ : DirichletCharacter ℂ N}
    (hχ : χ (-1) = -1) {f : modSpace (1 : ℕ) χ} (hf : f ∈ eisensteinSpace 1 χ) {ε : ℝ}
    (hε : 0 < ε) :
    (fun n ↦ coeffMod f n) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ ε) := by
  refine isBigO_qExpansion_coeff_of_mem_span_weightOneForm hε ?_
  rw [← eisensteinSpaceGamma1_one_eq]
  exact Submodule.mem_iSup_of_mem χ (Submodule.mem_iSup_of_mem (by rw [hχ, pow_one])
    ⟨f, hf, rfl⟩)

end ModularFormsKB.Miyake.Wave10
