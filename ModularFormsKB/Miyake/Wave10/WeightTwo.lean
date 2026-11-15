import ModularFormsKB.Miyake.Wave10.EisensteinSpace
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Dimension

/-!
# Miyake §4.7 in weight two: `ℰ₂(N, χ)` and Theorem 4.7.2 for `k = 2`

Miyake, *Modular Forms* (Springer 1989), §4.7, pp. 176–181.

In weight `k = 2` condition (4.7.2) has two cases: (i) `χ₁` and `χ₂` are both trivial, `M₁ = 1`
and `M₂ = p` is a prime; (ii) otherwise `χ₁`, `χ₂` are primitive. In case (i),
`L(s; f) = ζ(s) L(s - 1, 1_p)` and `f₂(z; 1, 1_p)` has coefficients `Σ_{d ∣ n, p ∤ d} d`,
that is `σ₁(n) - p σ₁(n/p)`: it is `-(1/24) (E₂(z) - p E₂(pz))`.

* `IsEisensteinGenTwo χ g`: `g ∈ 𝒢₂(N, χ)` is a generator `f₂(lz; χ₁, χ₂)` of (4.7.17), with
  (4.7.2) for `k = 2` (`Cond472Two`); `eisensteinSpaceTwo χ` is `ℰ₂(N, χ)`.
* `eisensteinSpaceTwo_eq`: `ℰ₂(N, χ)` is Tau Ceti's `TauCeti.weightTwoEisensteinSubspace`,
  spanned by `E₂^{ψ, φ, t}` (pairs other than the trivial one) and `E₂(z) - t E₂(tz)` (`t ∣ N`).
  The case (i) generators and the corrected series span the same space:
  `E₂(z) - lp E₂(lpz) = (E₂(z) - l E₂(lz)) - 24 l f₂(lz; 1, 1_p)` (`weightTwoTriv_mul`).
* `isCompl_eisensteinSpaceTwo_range_cuspSpace` (**Theorem 4.7.2**, `k = 2`, in the form
  `𝒢₂(N, χ) = 𝒮₂(N, χ) ⊕ ℰ₂(N, χ)`; the Petersson identification with `𝒩₂(N, χ)` is
  LE-MF-0227).
* `finrank_eisensteinSpaceTwo_add` (proof of Theorem 4.7.2, 1° for `χ` non-trivial and 2° for `χ`
  trivial): `dim ℰ₂(N, χ)` is the number of pairs `(χ'₁, χ'₂)` with `M'₁ M'₂ = N` and
  `χ'₁ χ'₂ = χ`, less one when `χ` is trivial (the excluded pair is `M'₁ = 1`, `χ'₂` the
  principal character modulo `N`).
* `ℰ₂(Γ₁(N))` (4.7.19), `𝒢₂(Γ₁(N)) = 𝒮₂(Γ₁(N)) ⊕ ℰ₂(Γ₁(N))`, and the weight-two rows of the
  dimension table (p. 181): `½ Σ_{M ∣ N} φ(M) φ(N/M) - 1` for `N ≥ 3`, `N ≠ 4`; `2` for `N = 4`;
  `1` for `N = 2`; `0` for `N = 1`.

Proofs: Tau Ceti's weight-two Eisenstein series (pinned revision), Diamond–Shurman Theorem 4.6.2.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup DirichletCharacter
open ArithmeticFunction
open scoped MatrixGroups ArithmeticFunction.sigma

noncomputable section

namespace ModularFormsKB.Miyake.Wave10

open ModularFormsKB.Miyake.Wave4 TauCeti.EisensteinSeries

/-- Miyake's condition (4.7.2) in weight `k = 2`: (i) `χ₁`, `χ₂` trivial, `M₁ = 1`, `M₂` prime;
or (ii) not both trivial, and both primitive. -/
def Cond472Two {M₁ M₂ : ℕ} (χ₁ : DirichletCharacter ℂ M₁) (χ₂ : DirichletCharacter ℂ M₂) : Prop :=
  (χ₁ = 1 ∧ χ₂ = 1 ∧ M₁ = 1 ∧ M₂.Prime) ∨
    (¬ (χ₁ = 1 ∧ χ₂ = 1) ∧ χ₁.IsPrimitive ∧ χ₂.IsPrimitive)

variable {N : ℕ} [NeZero N]

/-- `g ∈ 𝒢₂(N, χ)` is one of Miyake's generators `f₂(lz; χ₁, χ₂)` of (4.7.17) in weight two. -/
@[kb "miyake1989" "(4.7.17), p. 179 (k = 2)"]
def IsEisensteinGenTwo (χ : DirichletCharacter ℂ N) (g : modSpace 2 χ) : Prop :=
  ∃ (l M₁ M₂ : ℕ) (χ₁ : DirichletCharacter ℂ M₁) (χ₂ : DirichletCharacter ℂ M₂)
    (h : l * (M₁ * M₂) ∣ N), Cond472Two χ₁ χ₂ ∧
    χ₁.changeLevel (dvd_left_of_level h) * χ₂.changeLevel (dvd_right_of_level h) = χ ∧
    ∀ n : ℕ, 0 < n → coeffMod g n = eisCoeff 2 χ₁ χ₂ l n

/-- **Miyake (4.7.17)** in weight two: `ℰ₂(N, χ)`. -/
@[kb "miyake1989" "(4.7.17), p. 179 (k = 2)"]
def eisensteinSpaceTwo (χ : DirichletCharacter ℂ N) : Submodule ℂ (modSpace 2 χ) :=
  Submodule.span ℂ {g | IsEisensteinGenTwo χ g}

/-! ### Coefficients as linear functionals -/

omit [NeZero N] in
lemma coeffMod_sub {χ : DirichletCharacter ℂ N} (f g : modSpace 2 χ) (n : ℕ) :
    coeffMod (f - g) n = coeffMod f n - coeffMod g n := by
  have := congrArg (PowerSeries.coeff n) (map_sub (TauCeti.ModularForm.qExpansionLinearMap one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map N) 2)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) 2) (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) 2))
  simpa [coeffMod] using this

omit [NeZero N] in
lemma coeffMod_smul {χ : DirichletCharacter ℂ N} (c : ℂ) (f : modSpace 2 χ) (n : ℕ) :
    coeffMod (c • f) n = c * coeffMod f n := by
  show (qExpansion 1 (c • (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) 2))).coeff n = _
  rw [ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N)]
  simp only [map_smul, smul_eq_mul]

/-! ### The trivial pair: `E₂(z) - t E₂(tz)` and `f₂(lz; 1, 1_p)` -/

/-- Tau Ceti's index `(1, 1, t)` of weight two, for `t ∣ N`. -/
def trivIndex (t : ℕ) (ht : t ∣ N) : CharIndex N 2 where
  u := 1
  v := 1
  t := t
  psi := 1
  phi := 1
  psi_primitive := isPrimitive_one_level_one
  phi_primitive := isPrimitive_one_level_one
  parity := by
    rw [show (-1 : ZMod 1) = 1 from Subsingleton.elim _ _, MulChar.map_one, mul_one]
    norm_num
  level_dvd := by simpa using ht

omit [NeZero N] in
lemma trivIndex_nebentypus (t : ℕ) (ht : t ∣ N) :
    (trivIndex t ht).nebentypus = (1 : DirichletCharacter ℂ N).toUnitHom := by
  rw [CharIndex.nebentypus_eq_one _ ⟨rfl, rfl⟩]
  ext; simp

/-- `E₂(z) - t E₂(tz)` in `𝒢₂(N, 1)` (Tau Ceti's series of the index `(1, 1, t)`). -/
def weightTwoTriv (t : ℕ) (ht : t ∣ N) : modSpace 2 (1 : DirichletCharacter ℂ N) :=
  (trivIndex t ht).weightTwoInCharSpace (trivIndex_nebentypus t ht)

lemma coeffMod_weightTwoTriv (t : ℕ) (ht : t ∣ N) {n : ℕ} (hn : 0 < n) :
    coeffMod (weightTwoTriv t ht) n =
      -24 * ((σ 1 n : ℂ) - if t ∣ n then t * (σ 1 (n / t) : ℂ) else 0) :=
  CharIndex.qExpansion_weightTwoForm_coeff_of_eq_one (trivIndex t ht) ⟨rfl, rfl⟩ hn.ne'

lemma weightTwoTriv_one : weightTwoTriv (N := N) 1 (one_dvd N) = 0 :=
  Subtype.ext ((CharIndex.weightTwoForm_eq_zero_iff _).2 ⟨rfl, rfl, rfl⟩)

/-- Miyake's `f₂(lz; 1, 1_p)` in `𝒢₂(N, 1)`, for `l p ∣ N`: `-(24 l)⁻¹ ((E₂(z) - lp E₂(lpz)) -
(E₂(z) - l E₂(lz)))`. -/
def trivGen (l p : ℕ) (h : l * p ∣ N) : modSpace 2 (1 : DirichletCharacter ℂ N) :=
  (-(24 * l : ℂ))⁻¹ • (weightTwoTriv (l * p) h - weightTwoTriv l (dvd_of_mul_right_dvd h))

/-- `Σ_{d ∣ m, p ∤ d} d = σ₁(m) - p σ₁(m/p)` (the second term when `p ∣ m`). -/
lemma sum_divisors_trivChar {p : ℕ} (hp : p.Prime) (m : ℕ) :
    ∑ d ∈ m.divisors, (1 : DirichletCharacter ℂ p) d * (d : ℂ) =
      (σ 1 m : ℂ) - if p ∣ m then p * (σ 1 (m / p) : ℂ) else 0 := by
  have hval (d : ℕ) : (1 : DirichletCharacter ℂ p) d * (d : ℂ) =
      (d : ℂ) - if p ∣ d then (d : ℂ) else 0 := by
    by_cases hd : p ∣ d
    · have : ¬ IsUnit (d : ZMod p) := by
        rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm, hp.coprime_iff_not_dvd]
        exact not_not.2 hd
      simp [hd, MulChar.map_nonunit _ this]
    · have : IsUnit (d : ZMod p) := by
        rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm, hp.coprime_iff_not_dvd]
        exact hd
      simp [hd, MulChar.one_apply this]
  simp only [hval, Finset.sum_sub_distrib, sigma_one_apply, Nat.cast_sum]
  congr 1
  rw [← Finset.sum_filter]
  split_ifs with hm
  · rw [Finset.mul_sum]
    refine Finset.sum_nbij' (fun d ↦ d / p) (fun e ↦ p * e) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      exact ⟨Nat.div_dvd_div hd.2 hd.1.1, by
        have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd.1.2) hm) hp.pos
        exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd.1.2) hm) hp.pos).ne'⟩
    · intro e he
      simp only [Nat.mem_divisors] at he
      simp only [Finset.mem_filter, Nat.mem_divisors]
      refine ⟨⟨?_, ?_⟩, dvd_mul_right p e⟩
      · rw [← Nat.mul_div_cancel' hm]; exact Nat.mul_dvd_mul_left p he.1
      · intro h0; exact he.2 (Nat.div_eq_zero_iff.2 (Or.inr (by rw [h0]; exact hp.pos)))
    · intro d hd
      simp only [Finset.mem_filter] at hd
      exact Nat.mul_div_cancel' hd.2
    · intro e _
      exact Nat.mul_div_cancel_left e hp.pos
    · intro d hd
      simp only [Finset.mem_filter] at hd
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hd.2]
  · refine Finset.sum_eq_zero fun d hd ↦ ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    exact absurd (hd.2.trans hd.1.1) hm

lemma eisCoeff_trivChar {p : ℕ} (hp : p.Prime) (l n : ℕ) :
    eisCoeff 2 (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ p) l n =
      if l ∣ n then (σ 1 (n / l) : ℂ) - (if p ∣ n / l then p * (σ 1 (n / l / p) : ℂ) else 0)
      else 0 := by
  rw [eisCoeff]
  by_cases hl : l ∣ n
  · simp only [hl, ↓reduceIte]
    rw [← sum_divisors_trivChar hp]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [show ((1 : DirichletCharacter ℂ 1) ((n / l / d : ℕ) : ZMod 1)) = 1 from
      MulChar.one_apply (isUnit_of_subsingleton _)]
    simp
  · simp only [hl, ↓reduceIte]

lemma coeffMod_trivGen {l p : ℕ} (hp : p.Prime) (h : l * p ∣ N) {n : ℕ} (hn : 0 < n) :
    coeffMod (trivGen l p h) n = eisCoeff 2 (1 : DirichletCharacter ℂ 1)
      (1 : DirichletCharacter ℂ p) l n := by
  have hl : l ≠ 0 := by
    rintro rfl
    exact NeZero.ne N (Nat.eq_zero_of_zero_dvd (by simpa using h))
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  rw [trivGen, coeffMod_smul, coeffMod_sub, coeffMod_weightTwoTriv _ _ hn,
    coeffMod_weightTwoTriv _ _ hn, eisCoeff_trivChar hp]
  by_cases hln : l ∣ n
  · have hiff : l * p ∣ n ↔ p ∣ n / l := by
      constructor
      · intro hd; exact Nat.dvd_div_of_mul_dvd hd
      · intro hd
        have := Nat.mul_dvd_mul_left l hd
        rwa [Nat.mul_div_cancel' hln] at this
    simp only [hln, ↓reduceIte]
    by_cases hpd : p ∣ n / l
    · simp only [hiff.2 hpd, hpd, ↓reduceIte]
      rw [Nat.div_div_eq_div_mul]
      push_cast
      field_simp
      ring
    · simp only [mt hiff.1 hpd, hpd, ↓reduceIte]
      field_simp
      ring
  · have : ¬ l * p ∣ n := fun hd ↦ hln (dvd_of_mul_right_dvd hd)
    simp only [this, hln, ↓reduceIte]
    field_simp
    ring

lemma isEisensteinGenTwo_trivGen {l p : ℕ} (hp : p.Prime) (h : l * p ∣ N) :
    IsEisensteinGenTwo 1 (trivGen l p h) :=
  ⟨l, 1, p, 1, 1, by simpa using h, Or.inl ⟨rfl, rfl, rfl, hp⟩,
    by rw [changeLevel_one, changeLevel_one, mul_one], fun n hn ↦ coeffMod_trivGen hp h hn⟩

/-- `E₂(z) - lp E₂(lpz) = (E₂(z) - l E₂(lz)) - 24 l f₂(lz; 1, 1_p)`. -/
lemma weightTwoTriv_mul {l p : ℕ} (h : l * p ∣ N) :
    weightTwoTriv (l * p) h =
      weightTwoTriv l (dvd_of_mul_right_dvd h) + (-(24 * l : ℂ)) • trivGen l p h := by
  have hl : l ≠ 0 := by
    rintro rfl
    exact NeZero.ne N (Nat.eq_zero_of_zero_dvd (by simpa using h))
  have hc : (-(24 * l : ℂ)) ≠ 0 := by
    have : (l : ℂ) ≠ 0 := by exact_mod_cast hl
    simpa using this
  rw [trivGen, smul_smul, mul_inv_cancel₀ hc, one_smul, add_sub_cancel]

/-- Each corrected series `E₂(z) - t E₂(tz)` (`t ∣ N`) lies in `ℰ₂(N, 1)`. -/
lemma weightTwoTriv_mem (t : ℕ) (ht : t ∣ N) :
    weightTwoTriv t ht ∈ eisensteinSpaceTwo (1 : DirichletCharacter ℂ N) := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases ht1 : t = 1
    · subst ht1
      rw [weightTwoTriv_one]
      exact zero_mem _
    have ht0 : t ≠ 0 := by rintro rfl; exact NeZero.ne N (Nat.eq_zero_of_zero_dvd ht)
    have hp : t.minFac.Prime := Nat.minFac_prime ht1
    have htp : t / t.minFac * t.minFac = t := Nat.div_mul_cancel (Nat.minFac_dvd t)
    have hlt : t / t.minFac < t := Nat.div_lt_self (Nat.pos_of_ne_zero ht0) hp.one_lt
    have h' : t / t.minFac * t.minFac ∣ N := by rw [htp]; exact ht
    have key := weightTwoTriv_mul h'
    have e : weightTwoTriv t ht = weightTwoTriv (t / t.minFac * t.minFac) h' := by
      congr 1; simp [htp]
    rw [e, key]
    exact add_mem (ih _ hlt _) (Submodule.smul_mem _ _
      (Submodule.subset_span (isEisensteinGenTwo_trivGen hp h')))

/-! ### `ℰ₂(N, χ)` is Tau Ceti's weight-two Eisenstein subspace -/

omit [NeZero N] in
lemma toUnitHom_eq_one_iff (χ : DirichletCharacter ℂ N) :
    χ.toUnitHom = (1 : DirichletCharacter ℂ N).toUnitHom ↔ χ = 1 := by
  constructor
  · intro h
    apply MulChar.equivToUnitHom.injective
    rw [← MulChar.toUnitHom_eq, ← MulChar.toUnitHom_eq]
    exact h
  · rintro rfl; rfl

/-- Each Tau Ceti weight-two series of nebentypus `χ` lies in `ℰ₂(N, χ)`. -/
theorem weightTwoInCharSpace_mem {χ : DirichletCharacter ℂ N} (a : CharIndex N 2)
    (ha : a.nebentypus = χ.toUnitHom) :
    a.weightTwoInCharSpace ha ∈ eisensteinSpaceTwo χ := by
  by_cases h : a.psi = 1 ∧ a.phi = 1
  · have hχ : χ = 1 := (toUnitHom_eq_one_iff χ).1 (by
      rw [← ha, CharIndex.nebentypus_eq_one a h]
      ext; simp)
    subst hχ
    have he : a.weightTwoInCharSpace ha = weightTwoTriv a.t a.t_dvd := by
      refine Subtype.ext (TauCeti.ModularForm.eq_of_forall_pos_qExpansion_coeff_eq one_pos
        (TauCeti.one_mem_strictPeriods_Gamma1_map N) two_ne_zero fun n hn ↦ ?_)
      have := coeffMod_weightTwoTriv a.t a.t_dvd hn
      rw [coeffMod] at this
      rw [this, CharIndex.coe_weightTwoInCharSpace,
        CharIndex.qExpansion_weightTwoForm_coeff_of_eq_one a h hn.ne']
    rw [he]
    exact weightTwoTriv_mem a.t a.t_dvd
  · refine Submodule.subset_span ⟨a.t, a.u, a.v, a.psi, a.phi, a.level_dvd,
      Or.inr ⟨h, a.psi_primitive, a.phi_primitive⟩, (nebentypus_eq_iff a χ).1 ha, fun n hn ↦ ?_⟩
    show (qExpansion 1 a.weightTwoForm).coeff n = _
    rw [CharIndex.qExpansion_weightTwoForm_coeff_of_ne_one a (not_and_or.mp h) hn.ne',
      eisCoeff_eq_twistedDivisorSum]

/-- Each weight-two generator `f₂(lz; χ₁, χ₂)` lies in Tau Ceti's weight-two subspace. -/
theorem IsEisensteinGenTwo.mem_weightTwoEisensteinSubspace {χ : DirichletCharacter ℂ N}
    (hχ : χ (-1) = 1) {g : modSpace 2 χ} (hg : IsEisensteinGenTwo χ g) :
    g ∈ TauCeti.weightTwoEisensteinSubspace χ.toUnitHom := by
  obtain ⟨l, M₁, M₂, χ₁, χ₂, h, hc, hprod, hcoeff⟩ := hg
  rcases hc with ⟨rfl, rfl, rfl, hp⟩ | ⟨hne, h₁, h₂⟩
  · have hχ1 : χ = 1 := by rw [← hprod, changeLevel_one, changeLevel_one, mul_one]
    subst hχ1
    have hlp : l * M₂ ∣ N := by simpa using h
    have he : g = trivGen l M₂ hlp := by
      refine Subtype.ext (TauCeti.ModularForm.eq_of_forall_pos_qExpansion_coeff_eq one_pos
        (TauCeti.one_mem_strictPeriods_Gamma1_map N) two_ne_zero fun n hn ↦ ?_)
      have h1 := hcoeff n hn
      have h2 := coeffMod_trivGen hp hlp hn
      rw [coeffMod] at h1 h2
      rw [h1, h2]
    rw [he, trivGen]
    refine Submodule.smul_mem _ _ (sub_mem ?_ ?_)
    · exact TauCeti.mem_weightTwoEisensteinSubspace _ _ _
    · exact TauCeti.mem_weightTwoEisensteinSubspace _ _ _
  · let a : CharIndex N 2 :=
      ⟨M₁, M₂, l, χ₁, χ₂, h₁, h₂, parity_of_mul_eq _ _ hprod (by rw [hχ]; norm_num), h⟩
    have ha : a.nebentypus = χ.toUnitHom := (nebentypus_eq_iff a χ).2 hprod
    have he : g = a.weightTwoInCharSpace ha := by
      refine Subtype.ext (TauCeti.ModularForm.eq_of_forall_pos_qExpansion_coeff_eq one_pos
        (TauCeti.one_mem_strictPeriods_Gamma1_map N) two_ne_zero fun n hn ↦ ?_)
      have := hcoeff n hn
      rw [coeffMod] at this
      rw [this, CharIndex.coe_weightTwoInCharSpace,
        CharIndex.qExpansion_weightTwoForm_coeff_of_ne_one a (not_and_or.mp hne) hn.ne',
        eisCoeff_eq_twistedDivisorSum]
    rw [he]
    exact TauCeti.mem_weightTwoEisensteinSubspace _ a ha

/-- `ℰ₂(N, χ)` (4.7.17) is Tau Ceti's weight-two Eisenstein subspace of `𝒢₂(N, χ)`. -/
@[kb "miyake1989" "(4.7.17), p. 179 (k = 2)"]
theorem eisensteinSpaceTwo_eq {χ : DirichletCharacter ℂ N} (hχ : χ (-1) = 1) :
    eisensteinSpaceTwo χ = TauCeti.weightTwoEisensteinSubspace χ.toUnitHom :=
  le_antisymm (Submodule.span_le.2 fun _ hg ↦ IsEisensteinGenTwo.mem_weightTwoEisensteinSubspace hχ hg)
    (TauCeti.weightTwoEisensteinSubspace_le _ fun a ha ↦ weightTwoInCharSpace_mem a ha)

/-- **Miyake, Theorem 4.7.2** for `k = 2`, as a decomposition:
`𝒢₂(N, χ) = 𝒮₂(N, χ) ⊕ ℰ₂(N, χ)` (the identification with `𝒩₂(N, χ)` is LE-MF-0227). -/
@[kb "miyake1989" "Theorem 4.7.2, p. 179 (k = 2, complement of the cusp forms)"]
theorem isCompl_eisensteinSpaceTwo_range_cuspSpace {χ : DirichletCharacter ℂ N}
    (hχ : χ (-1) = 1) :
    IsCompl (eisensteinSpaceTwo χ)
      (LinearMap.range (TauCeti.cuspToModFormCharSpace 2 χ.toUnitHom)) := by
  rw [eisensteinSpaceTwo_eq hχ]
  exact TauCeti.isCompl_weightTwoEisensteinSubspace_range_cuspToModFormCharSpace _

/-! ### The dimension of `ℰ₂(N, χ)` -/

lemma card_subtype_split {α : Type*} [Finite α] (P Q : α → Prop) :
    Nat.card {a // P a} = Nat.card {a // P a ∧ Q a} + Nat.card {a // P a ∧ ¬ Q a} := by
  classical
  rw [← Nat.card_sum]
  refine Nat.card_congr ((Equiv.sumCompl fun x : {a // P a} ↦ Q x.1).symm.trans
    (Equiv.sumCongr (Equiv.subtypeSubtypeEquivSubtypeInter P Q)
      (Equiv.subtypeSubtypeEquivSubtypeInter P fun a ↦ ¬ Q a)))

open scoped Classical in
/-- **Miyake, proof of Theorem 4.7.2**, 1° (`χ` non-trivial) and 2° (`χ` trivial) in weight
two: `dim ℰ₂(N, χ)`, plus one when `χ` is trivial, is the number of pairs `(χ'₁, χ'₂)` of
characters modulo `M'₁ = g` and `M'₂ = N / g` with `χ'₁ χ'₂ = χ`. -/
@[kb "miyake1989" "Theorem 4.7.2, proof, 1° and 2°, p. 180 (dimension, k = 2)"]
theorem finrank_eisensteinSpaceTwo_add {χ : DirichletCharacter ℂ N} (hχ : χ (-1) = 1) :
    Module.finrank ℂ (eisensteinSpaceTwo χ) + (if χ = 1 then 1 else 0) =
      ∑ g : N.divisors, Nat.card {q : DirichletCharacter ℂ g × DirichletCharacter ℂ (N / g) //
        q.1.changeLevel (Nat.dvd_of_mem_divisors g.2) *
          q.2.changeLevel (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors g.2)) = χ} := by
  rw [← card_charIndex_nebentypus (k := 2) (by rw [hχ]; norm_num), eisensteinSpaceTwo_eq hχ,
    TauCeti.finrank_weightTwoEisensteinSubspace,
    card_subtype_split (fun a : CharIndex N 2 ↦ a.nebentypus = χ.toUnitHom)
      (fun a ↦ a.weightTwoForm ≠ 0)]
  congr 1
  simp only [not_not, CharIndex.weightTwoForm_eq_zero_iff_eq_one]
  split_ifs with h1
  · subst h1
    rw [eq_comm, Nat.card_eq_one_iff_exists]
    refine ⟨⟨CharIndex.one even_two, ?_, rfl⟩, fun x ↦ Subtype.ext x.2.2⟩
    rw [CharIndex.nebentypus_eq_one _ ⟨rfl, rfl⟩]
    ext; simp
  · rw [eq_comm, Nat.card_eq_zero]
    left
    refine ⟨fun x ↦ h1 ((toUnitHom_eq_one_iff χ).1 ?_)⟩
    rw [← x.2.1, x.2.2, CharIndex.nebentypus_eq_one _ ⟨rfl, rfl⟩]
    ext; simp

/-! ### `ℰ₂(Γ₁(N))` and its dimension -/

/-- **Miyake (4.7.19)** in weight two: `ℰ₂(Γ₁(N)) = ⊕_χ ℰ₂(N, χ)` over the even `χ` modulo `N`. -/
@[kb "miyake1989" "(4.7.19), p. 180 (k = 2)"]
def eisensteinSpaceGamma1Two : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) 2) :=
  ⨆ (χ : DirichletCharacter ℂ N) (_ : χ (-1) = 1), (eisensteinSpaceTwo χ).map (modSpace 2 χ).subtype

theorem eisensteinSpaceGamma1Two_eq :
    eisensteinSpaceGamma1Two (N := N) = congruenceG2Subspace (Gamma_le_Gamma1 N) := by
  rw [← span_range_weightTwoForm_eq_congruenceG2Subspace]
  refine le_antisymm (iSup₂_le fun χ hχ ↦ ?_) (Submodule.span_le.2 ?_)
  · rw [eisensteinSpaceTwo_eq hχ, TauCeti.weightTwoEisensteinSubspace_def,
      Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨a, rfl⟩
  · rintro _ ⟨a, rfl⟩
    set χ : DirichletCharacter ℂ N := a.psi.changeLevel a.u_dvd * a.phi.changeLevel a.v_dvd
    have ha : a.nebentypus = χ.toUnitHom := (nebentypus_eq_iff a χ).2 rfl
    have hχ : χ (-1) = 1 := by
      simp only [χ, MulChar.coeToFun_mul, Pi.mul_apply, changeLevel_apply_neg_one]
      simpa using a.parity
    refine Submodule.mem_iSup_of_mem χ (Submodule.mem_iSup_of_mem hχ ?_)
    exact ⟨a.weightTwoInCharSpace ha, weightTwoInCharSpace_mem a ha, rfl⟩

/-- **Miyake, Theorem 4.7.2**, end of the proof, `k = 2`:
`𝒢₂(Γ₁(N)) = 𝒮₂(Γ₁(N)) ⊕ ℰ₂(Γ₁(N))`. -/
@[kb "miyake1989" "Theorem 4.7.2, proof, p. 181 (Gamma_1(N), k = 2, complement)"]
theorem isCompl_eisensteinSpaceGamma1Two_cuspFormSubmodule :
    IsCompl (eisensteinSpaceGamma1Two (N := N)) (cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) 2) := by
  rw [eisensteinSpaceGamma1Two_eq]
  exact isCompl_congruenceG2Subspace_cuspFormSubmodule _

theorem finrank_eisensteinSpaceGamma1Two :
    Module.finrank ℂ (eisensteinSpaceGamma1Two (N := N)) = Nat.card (CharIndex N 2) - 1 := by
  rw [eisensteinSpaceGamma1Two_eq, finrank_congruenceG2Subspace]

/-- **Miyake, proof of Theorem 4.7.2**, the dimension table (p. 181), `k = 2`, `N ≥ 3`, `N ≠ 4`:
`dim ℰ₂(Γ₁(N)) = ½ Σ_{M ∣ N} φ(M) φ(N/M) - 1`. -/
@[kb "miyake1989" "Theorem 4.7.2, proof, p. 181 (dim E_2(Gamma_1(N)), N >= 3, N != 4)"]
theorem two_mul_finrank_eisensteinSpaceGamma1Two_add (hN : 3 ≤ N) (hN4 : N ≠ 4) :
    2 * (Module.finrank ℂ (eisensteinSpaceGamma1Two (N := N)) + 1) =
      ∑ M ∈ N.divisors, M.totient * (N / M).totient := by
  have h := CharIndex.two_mul_card (k := 2) (N := N) (by omega) hN4
  have hpos : 0 < Nat.card (CharIndex N 2) :=
    Nat.card_pos_iff.mpr ⟨⟨CharIndex.one even_two⟩, inferInstance⟩
  rw [finrank_eisensteinSpaceGamma1Two, Nat.sub_add_cancel hpos, h]

/-- **Miyake, proof of Theorem 4.7.2**, the dimension table (p. 181), `k = 2`: `2` for `N = 4`. -/
@[kb "miyake1989" "Theorem 4.7.2, proof, p. 181 (dim E_2(Gamma_1(4)) = 2)"]
theorem finrank_eisensteinSpaceGamma1Two_four :
    Module.finrank ℂ (eisensteinSpaceGamma1Two (N := 4)) = 2 := by
  rw [finrank_eisensteinSpaceGamma1Two, CharIndex.card_four]
  norm_num

/-- **Miyake, proof of Theorem 4.7.2**, the dimension table (p. 181), `k = 2`: `1` for `N = 2`. -/
@[kb "miyake1989" "Theorem 4.7.2, proof, p. 181 (dim E_2(Gamma_1(2)) = 1)"]
theorem finrank_eisensteinSpaceGamma1Two_two :
    Module.finrank ℂ (eisensteinSpaceGamma1Two (N := 2)) = 1 := by
  rw [finrank_eisensteinSpaceGamma1Two, CharIndex.card_two]
  norm_num

/-- **Miyake, proof of Theorem 4.7.2**, the dimension table (p. 181), `k = 2`: `0` for `N = 1`. -/
@[kb "miyake1989" "Theorem 4.7.2, proof, p. 181 (dim E_2(Gamma_1(1)) = 0)"]
theorem finrank_eisensteinSpaceGamma1Two_one :
    Module.finrank ℂ (eisensteinSpaceGamma1Two (N := 1)) = 0 := by
  rw [finrank_eisensteinSpaceGamma1Two, CharIndex.card_one]
  norm_num

end ModularFormsKB.Miyake.Wave10
