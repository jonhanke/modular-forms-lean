/-
# Auxiliary lemmas for the local factors of `LFunction (congruentCurve n)`

Part 1 (generic): the coefficient of an Euler product `eulerProduct (ofPowerSeries (q i) (f i))` at `p ^ k` is the
`k`-th coefficient of the factor at the place `i₀` with `q i₀ = p`, provided no other `q i` is divisible by `p`.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.Curve
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.Coefficients
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.Order.Northcott
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import TauCeti.AlgebraicGeometry.EllipticCurve.LFunction.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.LocalPolynomial
import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.PotentialGoodReduction

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open ArithmeticFunction Filter

section Euler

variable {ι R : Type*} [CommRing R]

set_option backward.isDefEq.respectTransparency.types false in
/-- Off the powers of `q`, `ofPowerSeries q f` vanishes (and is `0` away from `1` for `q ≤ 1`). -/
theorem ofPowerSeries_apply_eq_zero {q : ℕ} (f : PowerSeries R) {a : ℕ} (ha : a ≠ 1)
    (h : ∀ k, q ^ k ≠ a) : ofPowerSeries q f a = 0 := by
  by_cases hq : 1 < q
  · rw [ofPowerSeries_apply hq, Function.extend_apply', Pi.zero_apply]
    rintro ⟨k, hk⟩
    exact h k hk
  · simp only [ofPowerSeries, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, hq,
      dite_false, Algebra.algebraMap_eq_smul_one]
    simp [ArithmeticFunction.one_apply_ne ha]

theorem ofPowerSeries_apply_dvd_prime_pow {q p : ℕ} (hp : p.Prime) (hq : ¬ p ∣ q) (f : PowerSeries R)
    (j : ℕ) {a : ℕ} (ha : a ∣ p ^ j) (ha1 : a ≠ 1) : ofPowerSeries q f a = 0 := by
  refine ofPowerSeries_apply_eq_zero f ha1 fun k hk => ?_
  subst hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact ha1 (by simp)
  · have h1 : q ∣ p ^ j := (dvd_pow_self q hk0.ne').trans ha
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 h1
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact ha1 (by simp [hm])
    · exact hq (hm ▸ dvd_pow_self p hm0.ne')

/-- The coefficient of the Euler product at `p ^ k`. -/
theorem eulerProduct_ofPowerSeries_apply_prime_pow (q : ι → ℕ) [hN : Northcott q]
    (f : ι → PowerSeries R) (hf : ∀ i, (f i).constantCoeff = 1) (i₀ : ι) {p : ℕ} (hp : p.Prime)
    (hq₀ : q i₀ = p) (hq : ∀ i, i ≠ i₀ → ¬ p ∣ q i) (k : ℕ) :
    eulerProduct (fun i ↦ ofPowerSeries (q i) (f i)) (p ^ k) = (f i₀).coeff k := by
  classical
  have key : ∀ t : Finset ι, i₀ ∉ t → ∀ j,
      (∏ i ∈ t, ofPowerSeries (q i) (f i)) (p ^ j) = if j = 0 then 1 else 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _ j
      rw [Finset.prod_empty, ArithmeticFunction.one_apply]
      simp [hp.ne_one]
    | insert i t hi ih =>
      intro hmem j
      have hi0 : i ≠ i₀ := fun h => hmem (h ▸ Finset.mem_insert_self i t)
      have ht : i₀ ∉ t := fun h => hmem (Finset.mem_insert_of_mem h)
      rw [Finset.prod_insert hi, ArithmeticFunction.mul_apply]
      rw [Finset.sum_eq_single (1, p ^ j)]
      · simp only [ofPowerSeries_apply_one, hf, one_mul]
        exact ih ht j
      · rintro ⟨a, b⟩ hab hne
        have hab' := Nat.mem_divisorsAntidiagonal.1 hab
        have ha : a ∣ p ^ j := ⟨b, hab'.1.symm⟩
        by_cases ha1 : a = 1
        · subst ha1
          exact absurd (by simpa using hab'.1) hne
        · simp [ofPowerSeries_apply_dvd_prime_pow hp (hq i hi0) (f i) j ha ha1]
      · intro h
        exact absurd (Nat.mem_divisorsAntidiagonal.2 ⟨by simp, by simp [hp.ne_zero]⟩) h
  obtain ⟨s, hs1, hs2⟩ := ((tendsTo_eulerProduct_ofPowerSeries q f hf (p ^ k)).and
    (eventually_ge_atTop ({i₀} : Finset ι))).exists
  rw [← hs1, ← Finset.mul_prod_erase s _ (Finset.singleton_subset_iff.1 hs2),
    ArithmeticFunction.mul_apply, Finset.sum_eq_single (p ^ k, 1)]
  · have := ofPowerSeries_apply_pow (q := q i₀) (hq₀ ▸ hp.one_lt) (f i₀) k
    rw [hq₀] at this
    dsimp only
    rw [show (1:ℕ) = p ^ 0 by simp, key _ (Finset.notMem_erase i₀ s) 0]
    rw [hq₀]
    simpa using this
  · rintro ⟨a, b⟩ hab hne
    have hab' := Nat.mem_divisorsAntidiagonal.1 hab
    obtain ⟨m, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 (⟨a, by rw [← hab'.1, mul_comm]⟩ : b ∣ p ^ k)
    rw [key _ (Finset.notMem_erase i₀ s)]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact absurd (by simpa using hab'.1) hne
    · simp [hm.ne']
  · intro h
    exact absurd (Nat.mem_divisorsAntidiagonal.2 ⟨by simp, by simp [hp.ne_zero]⟩) h

end Euler

/-! ### Places of `ℚ` -/

section Places

open IsDedekindDomain NumberField Rat.HeightOneSpectrum

variable (w : HeightOneSpectrum (𝓞 ℚ))

/-- The completed integers at `w`. -/
local notation "𝒪w" => HeightOneSpectrum.adicCompletionIntegers ℚ w

theorem natGenerator_eq_primesEquiv : natGenerator w = (primesEquiv w : ℕ) := rfl

instance factPrimesEquiv : Fact (primesEquiv w : ℕ).Prime := ⟨(primesEquiv w).2⟩

/-- The residue field of the completion at `w` is `ZMod` of the rational prime below `w`. -/
noncomputable def residueEquiv :
    ZMod (natGenerator w) ≃+* IsLocalRing.ResidueField (HeightOneSpectrum.adicCompletionIntegers ℚ w) :=
  (Int.quotientSpanNatEquivZMod (natGenerator w)).symm.trans
    ((Ideal.quotEquivOfEq (span_natGenerator w)).trans
      ((Ideal.quotientEquiv w.asIdeal (w.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)))
          (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) rfl).symm.trans
        (w.residueFieldEquivAdicCompletionIntegers (K := ℚ))))

theorem natCard_residueField :
    Nat.card (IsLocalRing.ResidueField (HeightOneSpectrum.adicCompletionIntegers ℚ w)) =
      natGenerator w := by
  rw [← Nat.card_congr (residueEquiv w).toEquiv, Nat.card_zmod]

theorem northcott_natGenerator : Northcott fun w : HeightOneSpectrum (𝓞 ℚ) => natGenerator w := by
  refine ⟨fun B => ?_⟩
  have hinj : Function.Injective fun w : HeightOneSpectrum (𝓞 ℚ) => (primesEquiv w : ℕ) :=
    fun a b h => (primesEquiv).injective (Subtype.ext h)
  exact (Set.finite_Iic B).preimage (hinj.injOn)

/-- The ring equivalence of the completed integers with `ℤ_[p]`. -/
noncomputable def padicRingEquiv :
    HeightOneSpectrum.adicCompletionIntegers ℚ w ≃+* ℤ_[(primesEquiv w : ℕ)] :=
  (adicCompletionIntegers.padicIntEquiv w).toAlgEquiv.toRingEquiv

theorem isUnit_intCast_iff (m : ℤ) :
    IsUnit (m : HeightOneSpectrum.adicCompletionIntegers ℚ w) ↔ ¬ (((primesEquiv w : ℕ) : ℤ) ∣ m) := by
  rw [← MulEquiv.isUnit_map (padicRingEquiv w).toMulEquiv]
  have : (padicRingEquiv w) (m : HeightOneSpectrum.adicCompletionIntegers ℚ w) = (m : ℤ_[(primesEquiv w : ℕ)]) :=
    map_intCast _ m
  change IsUnit ((padicRingEquiv w) _) ↔ _
  rw [this, PadicInt.isUnit_iff, ← PadicInt.norm_int_lt_one_iff_dvd]
  have := PadicInt.norm_le_one (m : ℤ_[(primesEquiv w : ℕ)])
  constructor
  · intro h h'; linarith
  · intro h; exact le_antisymm this (not_lt.1 h)

theorem pow_dvd_intCast_iff (k : ℕ) (m : ℤ) :
    (((primesEquiv w : ℕ) : HeightOneSpectrum.adicCompletionIntegers ℚ w)) ^ k ∣
      (m : HeightOneSpectrum.adicCompletionIntegers ℚ w) ↔ ((primesEquiv w : ℕ) : ℤ) ^ k ∣ m := by
  rw [← map_dvd_iff (padicRingEquiv w)]
  rw [map_pow, map_natCast, map_intCast]
  exact_mod_cast PadicInt.pow_p_dvd_int_iff (p := (primesEquiv w : ℕ)) k m

theorem irreducible_primesEquiv :
    Irreducible ((primesEquiv w : ℕ) : HeightOneSpectrum.adicCompletionIntegers ℚ w) := by
  rw [← MulEquiv.irreducible_iff (padicRingEquiv w).toMulEquiv]
  change Irreducible ((padicRingEquiv w) _)
  rw [map_natCast]
  exact PadicInt.irreducible_p

end Places

/-! ### Generic lemmas over a discrete valuation ring -/

section DVR

open WeierstrassCurve IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum IsLocalRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem valuation_algebraMap_irreducible {ϖ : R} (hϖ : Irreducible ϖ) :
    valuation K (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R K ϖ) = WithZero.exp (-1) := by
  rw [valuation_of_algebraMap, intValuation_maximalIdeal, addVal_uniformizer hϖ]
  rw [← Nat.cast_one (R := ℕ∞), ENat.recTopCoe_natCast, ← WithZero.exp_eq_coe_ofAdd, WithZero.inv_exp]
  simp

theorem valuation_isUnit {r : R} (hr : IsUnit r) :
    valuation K (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R K r) = 1 :=
  ((IsDiscreteValuationRing.maximalIdeal R).valuation_eq_one_iff_notMem (K := K)).2 (IsLocalRing.notMem_maximalIdeal.2 hr)

theorem not_hasGoodReduction_minimal_of_valuation_Δ (W : WeierstrassCurve K) [W.IsElliptic] (d : ℕ)
    (hd : ¬ 12 ∣ d) (hΔ : valuation K (IsDiscreteValuationRing.maximalIdeal R) W.Δ = WithZero.exp (-(d : ℤ))) :
    ¬ (W.minimal R).HasGoodReduction R := by
  intro h
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal R
  have h1 := h.goodReduction
  rw [← hC, variableChange_Δ, map_mul, map_pow, hΔ, Units.val_inv_eq_inv_val, map_inv₀] at h1
  have hu : valuation K (IsDiscreteValuationRing.maximalIdeal R) (C.u : K) ≠ 0 := by
    simp
  obtain ⟨z, hz⟩ : ∃ z : ℤ, valuation K (IsDiscreteValuationRing.maximalIdeal R) (C.u : K) = WithZero.exp z :=
    ⟨_, (WithZero.exp_log hu).symm⟩
  rw [hz, ← WithZero.exp_neg, ← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero,
    WithZero.exp_inj] at h1
  apply hd
  exact ⟨(-z).toNat, by simp at h1; omega⟩

theorem not_hasGoodReduction_minimal_of_c₄ (W : WeierstrassCurve K) [W.IsElliptic]
    (h2 : Irreducible (2 : R))
    (hΔ : valuation K (IsDiscreteValuationRing.maximalIdeal R) W.Δ = WithZero.exp (-12))
    (hc : valuation K (IsDiscreteValuationRing.maximalIdeal R) W.c₄ = WithZero.exp (-6)) :
    ¬ (W.minimal R).HasGoodReduction R := by
  intro h
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal R
  have h1 := h.goodReduction
  rw [← hC, variableChange_Δ, map_mul, map_pow, hΔ, Units.val_inv_eq_inv_val, map_inv₀] at h1
  have hu : valuation K (IsDiscreteValuationRing.maximalIdeal R) (C.u : K) ≠ 0 := by
    simp
  obtain ⟨z, hz⟩ : ∃ z : ℤ, valuation K (IsDiscreteValuationRing.maximalIdeal R) (C.u : K) = WithZero.exp z :=
    ⟨_, (WithZero.exp_log hu).symm⟩
  rw [hz, ← WithZero.exp_neg, ← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero,
    WithZero.exp_inj] at h1
  have hz1 : z = -1 := by simp at h1; omega
  have hM : valuation K (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R K (integralModel R (W.minimal R)).c₄) = WithZero.exp (-2) := by
    rw [integralModel_c₄_eq, ← hC, variableChange_c₄, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀, hz, hz1, hc,
      ← WithZero.exp_neg, ← WithZero.exp_nsmul, ← WithZero.exp_add]
    congr 1
  set I := integralModel R (W.minimal R) with hI
  have hlt : valuation K (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R K I.c₄) < 1 := by
    rw [hM, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hmem : I.c₄ ∈ IsLocalRing.maximalIdeal R :=
    ((IsDiscreteValuationRing.maximalIdeal R).valuation_lt_one_iff_mem (K := K) I.c₄).1 hlt
  rw [h2.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
  have hc4 : I.c₄ = I.a₁ ^ 4 + 2 * (4 * I.a₁ ^ 2 * I.a₂ + 8 * I.a₂ ^ 2 - 24 * I.a₄ - 12 * I.a₁ * I.a₃) := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  have ha1 : (2 : R) ∣ I.a₁ := by
    refine h2.prime.dvd_of_dvd_pow (n := 4) ?_
    have : (2 : R) ∣ I.a₁ ^ 4 + 2 * (4 * I.a₁ ^ 2 * I.a₂ + 8 * I.a₂ ^ 2 - 24 * I.a₄ - 12 * I.a₁ * I.a₃) := hc4 ▸ hmem
    exact (dvd_add_left (dvd_mul_right _ _)).1 this
  obtain ⟨a, ha⟩ := ha1
  have hc16 : I.c₄ = 16 * (a ^ 4 + 2 * a ^ 2 * I.a₂ + I.a₂ ^ 2 - 3 * I.a₄ - 3 * a * I.a₃) := by
    rw [hc4, ha]; ring
  have hle : valuation K (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R K I.c₄) ≤ WithZero.exp (-4) := by
    rw [hc16, map_mul, map_mul]
    have h16 : valuation K (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R K (16 : R)) = WithZero.exp (-4) := by
      have : (16 : R) = 2 ^ 4 := by norm_num
      rw [this, map_pow, map_pow, show (2 : R) = 2 from rfl, valuation_algebraMap_irreducible R h2, ← WithZero.exp_nsmul]
      simp
    rw [h16]
    exact mul_le_of_le_one_right zero_le (valuation_le_one _ _)
  rw [hM, WithZero.exp_le_exp] at hle
  omega
end DVR

/-! ### The local polynomial at good reduction -/

section GoodLocal

open WeierstrassCurve IsLocalRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem localPolynomial_baseChange_of_isUnit_Δ (C : WeierstrassCurve R) (hC : IsUnit C.Δ) :
    (C.baseChange K).localPolynomial R =
      1 - Polynomial.C (C.map (residue R)).frobeniusTrace * Polynomial.X +
        Polynomial.C (Nat.card (ResidueField R) : ℤ) * Polynomial.X ^ 2 := by
  haveI : IsIntegral R (C.baseChange K) := ⟨C, rfl⟩
  have hint : (C.baseChange K).HasGoodReduction R := by
    rw [hasGoodReduction_iff_isUnit_integralModel_Δ, integralModel_baseChange_self]
    exact hC
  haveI := hint.toIsMinimal
  haveI : (C.baseChange K).IsElliptic := hint.isElliptic
  have hmin := hint.hasGoodReduction_minimal
  have key : (((C.baseChange K).minimal R).reduction R).frobeniusTrace =
      (C.map (residue R)).frobeniusTrace := by
    obtain ⟨D, hD⟩ := (C.baseChange K).exists_smul_eq_minimal R
    obtain ⟨C', hC'⟩ := exists_smul_reduction_eq_of_isMinimal_smul R D hD
    rw [← hC', variableChange_frobeniusTrace]
    simp [reduction]
  rw [localPolynomial_eq_of_hasGoodReduction R _ hmin, key]

end GoodLocal

/-! ### Coefficients of the inverse of `1 - a T + q T²` -/

open PowerSeries in
theorem coeff_inv_quadratic (a q : ℤ) (s : PowerSeries ℤ)
    (hs : ((1 - Polynomial.C a * Polynomial.X + Polynomial.C q * Polynomial.X ^ 2 :
      Polynomial ℤ) : PowerSeries ℤ) * s = 1) :
    s.coeff 0 = 1 ∧ s.coeff 1 = a ∧ ∀ k, s.coeff (k + 2) = a * s.coeff (k + 1) - q * s.coeff k := by
  have hs' : s - PowerSeries.C a * (X * s) + PowerSeries.C q * (X * (X * s)) = 1 := by
    rw [← hs]
    push_cast
    ring
  have h0 := congrArg (PowerSeries.coeff 0) hs'
  have h1 := congrArg (PowerSeries.coeff 1) hs'
  have h2 := fun k => congrArg (PowerSeries.coeff (k + 2)) hs'
  simp [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul] at h0 h1 h2
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at h0 h1
  refine ⟨h0, ?_, fun k => ?_⟩
  · rw [h0] at h1
    linarith
  · linarith [h2 k]

/-- The local power series is `1` when the local polynomial is `1`. -/
theorem localPowerSeries_eq_one {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K)
    (h : W.localPolynomial R = 1) : W.localPowerSeries R = 1 := by
  have := PowerSeries.mul_invOfUnit ((W.localPolynomial R : Polynomial ℤ) : PowerSeries ℤ) 1
    (by rw [h]; simp)
  rw [h] at this
  simpa [WeierstrassCurve.localPowerSeries, h] using this

/-! ### The Euler product coefficient at `p ^ k` for `ℚ` -/

section LFun

open IsDedekindDomain NumberField Rat.HeightOneSpectrum ArithmeticFunction

theorem natGenerator_symm {p : ℕ} (hp : p.Prime) :
    natGenerator (primesEquiv.symm (⟨p, hp⟩ : Nat.Primes) : HeightOneSpectrum (𝓞 ℚ)) = p :=
  congrArg Subtype.val (primesEquiv.apply_symm_apply (⟨p, hp⟩ : Nat.Primes))

/-- The base change of `W` to the completion at `w`, along the algebra structure used by `LFunction`. -/
noncomputable def baseChangeAt (W : WeierstrassCurve ℚ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    WeierstrassCurve (w.adicCompletion ℚ) :=
  W.map (@algebraMap ℚ (w.adicCompletion ℚ) _ _ (HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ w))

/-- The local power series of `W` at the place `w`. -/
noncomputable def localSeriesOf (W : WeierstrassCurve ℚ) (w : HeightOneSpectrum (𝓞 ℚ)) : PowerSeries ℤ :=
  (baseChangeAt W w).localPowerSeries (w.adicCompletionIntegers ℚ)

theorem LFunction_prime_pow_eq (W : WeierstrassCurve ℚ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    W.LFunction (p ^ k) =
      (localSeriesOf W (primesEquiv.symm (⟨p, hp⟩ : Nat.Primes))).coeff k := by
  set v : HeightOneSpectrum (𝓞 ℚ) := primesEquiv.symm (⟨p, hp⟩ : Nat.Primes) with hv
  have hvp : (primesEquiv v : ℕ) = p :=
    congrArg Subtype.val (primesEquiv.apply_symm_apply (⟨p, hp⟩ : Nat.Primes))
  have hN : Northcott (fun w : HeightOneSpectrum (𝓞 ℚ) =>
      Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers ℚ))) := by
    simp only [natCard_residueField]
    exact northcott_natGenerator
  unfold WeierstrassCurve.LFunction WeierstrassCurve.localEulerFactor
  refine eulerProduct_ofPowerSeries_apply_prime_pow
    (fun w : HeightOneSpectrum (𝓞 ℚ) => Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers ℚ)))
    (fun w => localSeriesOf W w)
    (fun w => WeierstrassCurve.constantCoeff_localPowerSeries _ _) v hp
    (by rw [natCard_residueField]; exact hvp) (fun w hw hdvd => hw ?_) k
  rw [natCard_residueField] at hdvd
  have h1 : p = natGenerator w := (Nat.prime_dvd_prime_iff_eq hp (prime_natGenerator w)).1 hdvd
  apply primesEquiv.injective
  apply Subtype.ext
  rw [hvp]
  exact h1.symm

end LFun

/-! ### The curves `E_n` over rings -/

section Curve

open WeierstrassCurve IsDedekindDomain NumberField Rat.HeightOneSpectrum

/-- `E_n : y² = x³ - n²x` over a ring. -/
def curveOver (A : Type*) [CommRing A] (n : ℕ) : WeierstrassCurve A := ⟨0, 0, 0, -((n : A) ^ 2), 0⟩

theorem curveOver_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (n : ℕ) :
    (curveOver A n).map f = curveOver B n := by
  ext <;> simp [curveOver]

theorem curveOver_Δ (A : Type*) [CommRing A] (n : ℕ) : (curveOver A n).Δ = 64 * (n : A) ^ 6 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curveOver]
  ring

theorem curveOver_c₄ (A : Type*) [CommRing A] (n : ℕ) : (curveOver A n).c₄ = 48 * (n : A) ^ 2 := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, curveOver]
  ring

theorem curveOver_j (K : Type*) [Field K] (n : ℕ) [(curveOver K n).IsElliptic] :
    (curveOver K n).j = 1728 := by
  rw [WeierstrassCurve.j, Units.inv_mul_eq_iff_eq_mul, WeierstrassCurve.coe_Δ', curveOver_Δ, curveOver_c₄]
  ring

theorem congruentCurve_eq_curveOver (n : ℕ) : congruentCurve n = curveOver ℚ n := rfl

theorem congruentCurveMod_eq_curveOver (n p : ℕ) : congruentCurveMod n p = curveOver (ZMod p) n := rfl

theorem congruentCurve_baseChange (K : Type*) [Field K] [Algebra ℚ K] (n : ℕ) :
    (congruentCurve n).baseChange K = curveOver K n :=
  curveOver_map (algebraMap ℚ K) n

/-- The Frobenius trace is invariant under isomorphism of the base field. -/
theorem frobeniusTrace_map_ringEquiv {F F' : Type*} [Field F] [Field F'] [Finite F] [Finite F']
    (e : F ≃+* F') (W : WeierstrassCurve F) :
    (W.map (e : F →+* F')).frobeniusTrace = W.frobeniusTrace := by
  have h : Nat.card {p : F' × F' // (W.map (e : F →+* F')).toAffine.Equation p.1 p.2} =
      Nat.card {p : F × F // W.toAffine.Equation p.1 p.2} :=
    (Nat.card_congr ((e.toEquiv.prodCongr e.toEquiv).subtypeEquiv fun xy =>
      (WeierstrassCurve.Affine.map_equation (W := W) (f := (e : F →+* F')) e.injective xy.1 xy.2).symm)).symm
  rw [frobeniusTrace_def, frobeniusTrace_def, pointCount_def, pointCount_def, h,
    Nat.card_congr e.toEquiv]

variable (w : HeightOneSpectrum (𝓞 ℚ))

theorem isUnit_natCast_iff (m : ℕ) :
    IsUnit (m : HeightOneSpectrum.adicCompletionIntegers ℚ w) ↔ ¬ natGenerator w ∣ m := by
  have := isUnit_intCast_iff w (m : ℤ)
  rw [Int.cast_natCast, Int.natCast_dvd_natCast] at this
  exact this

theorem valuation_pow_mul_natCast {g : ℕ} (hg : natGenerator w = g) (d m : ℕ) (hm : ¬ g ∣ m) :
    IsDedekindDomain.HeightOneSpectrum.valuation (w.adicCompletion ℚ)
      (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers ℚ))
      (algebraMap (w.adicCompletionIntegers ℚ) (w.adicCompletion ℚ)
        (((g : w.adicCompletionIntegers ℚ)) ^ d * (m : w.adicCompletionIntegers ℚ))) =
      WithZero.exp (-(d : ℤ)) := by
  subst hg
  have hirr : Irreducible ((natGenerator w : ℕ) : HeightOneSpectrum.adicCompletionIntegers ℚ w) :=
    irreducible_primesEquiv w
  rw [map_mul, map_pow, map_mul, map_pow,
    valuation_algebraMap_irreducible _ hirr,
    valuation_isUnit _ ((isUnit_natCast_iff w m).2 hm), mul_one, ← WithZero.exp_nsmul]
  simp

theorem trace_eq {g : ℕ} [Fact g.Prime] (hg : natGenerator w = g) (n : ℕ) :
    ((curveOver (w.adicCompletionIntegers ℚ) n).map (IsLocalRing.residue _)).frobeniusTrace =
      (congruentCurveMod n g).frobeniusTrace := by
  subst hg
  have := frobeniusTrace_map_ringEquiv (residueEquiv w) (curveOver (ZMod (natGenerator w)) n)
  rw [curveOver_map] at this
  rw [curveOver_map, congruentCurveMod_eq_curveOver]
  exact this

theorem baseChangeAt_congruentCurve (n : ℕ) :
    baseChangeAt (congruentCurve n) w = curveOver (w.adicCompletion ℚ) n :=
  curveOver_map _ n

theorem localSeries_good {g : ℕ} [Fact g.Prime] (hg : natGenerator w = g) (n : ℕ) (hn : ¬ g ∣ 64 * n ^ 6) :
    (localSeriesOf (congruentCurve n) w).coeff 0 = 1 ∧
      (localSeriesOf (congruentCurve n) w).coeff 1 = (congruentCurveMod n g).frobeniusTrace ∧
      ∀ k, (localSeriesOf (congruentCurve n) w).coeff (k + 2) = (congruentCurveMod n g).frobeniusTrace *
        (localSeriesOf (congruentCurve n) w).coeff (k + 1) -
          (g : ℤ) * (localSeriesOf (congruentCurve n) w).coeff k := by
  have hC : IsUnit (curveOver (w.adicCompletionIntegers ℚ) n).Δ := by
    rw [curveOver_Δ]
    have : (64 * (n : w.adicCompletionIntegers ℚ) ^ 6) = ((64 * n ^ 6 : ℕ) : w.adicCompletionIntegers ℚ) := by
      push_cast; ring
    rw [this, isUnit_natCast_iff]
    rw [hg]
    exact hn
  have hpoly := localPolynomial_baseChange_of_isUnit_Δ (K := w.adicCompletion ℚ)
    (w.adicCompletionIntegers ℚ) _ hC
  have hq : Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers ℚ)) = g := by
    rw [natCard_residueField, hg]
  rw [hq, trace_eq w hg] at hpoly
  have hcb : (curveOver (w.adicCompletionIntegers ℚ) n).baseChange (w.adicCompletion ℚ) =
      baseChangeAt (congruentCurve n) w := by
    rw [baseChangeAt_congruentCurve]
    exact curveOver_map _ n
  rw [hcb] at hpoly
  have hmul := PowerSeries.mul_invOfUnit
    ((((baseChangeAt (congruentCurve n) w)).localPolynomial (w.adicCompletionIntegers ℚ) :
      Polynomial ℤ) : PowerSeries ℤ) (1 : ℤˣ) (by rw [hpoly]; simp)
  rw [hpoly] at hmul
  refine coeff_inv_quadratic _ _ _ ?_
  unfold localSeriesOf WeierstrassCurve.localPowerSeries
  rw [hpoly]
  exact hmul

theorem valuation_natCast_of_eq {g : ℕ} (hg : natGenerator w = g) {a d m : ℕ} (hm : ¬ g ∣ m)
    (h : a = g ^ d * m) :
    IsDedekindDomain.HeightOneSpectrum.valuation (w.adicCompletion ℚ)
      (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers ℚ)) (a : w.adicCompletion ℚ) =
      WithZero.exp (-(d : ℤ)) := by
  rw [← valuation_pow_mul_natCast w hg d m hm]
  congr 1
  rw [h]
  push_cast
  simp [map_mul, map_pow, map_natCast]

theorem localPolynomial_bad {g : ℕ} (hgp : g.Prime) (hg : natGenerator w = g) (n : ℕ) [NeZero n]
    (hn : Squarefree n) (hgn : g ∣ 2 * n) :
    (baseChangeAt (congruentCurve n) w).localPolynomial (w.adicCompletionIntegers ℚ) = 1 := by
  rw [baseChangeAt_congruentCurve]
  set K := w.adicCompletion ℚ with hK
  set R := w.adicCompletionIntegers ℚ with hR
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  haveI hell : (curveOver K n).IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff, curveOver_Δ, isUnit_iff_ne_zero]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 6 hnK)
  have hpot : (curveOver K n).HasPotentialGoodReduction R :=
    hasPotentialGoodReduction_of_isInteger_j R ⟨1728, by rw [curveOver_j, map_ofNat]⟩
  refine localPolynomial_eq_one_of_hasPotentialGoodReduction_of_not_hasGoodReduction R hpot ?_
  have hΔ : (curveOver K n).Δ = ((64 * n ^ 6 : ℕ) : K) := by rw [curveOver_Δ]; push_cast; ring
  have hc4 : (curveOver K n).c₄ = ((48 * n ^ 2 : ℕ) : K) := by rw [curveOver_c₄]; push_cast; ring
  have hgdvd : ∀ a : ℕ, g ∣ a ^ 6 → g ∣ a := fun a h => hgp.dvd_of_dvd_pow h
  have hg64 : g ∣ 64 → g = 2 := fun h => by
    have : g ∣ 2 ^ 6 := by norm_num; exact h
    exact (Nat.prime_dvd_prime_iff_eq hgp Nat.prime_two).1 (hgp.dvd_of_dvd_pow this)
  by_cases hg2 : g = 2
  · subst hg2
    by_cases hodd : 2 ∣ n
    · obtain ⟨m, rfl⟩ := hodd
      have hm : ¬ 2 ∣ m := by
        rintro ⟨t, rfl⟩
        have := Nat.isUnit_iff.1 (hn 2 ⟨t, by ring⟩)
        omega
      have hmm : ¬ 2 ∣ 3 * m ^ 2 := by
        intro h
        rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
        · omega
        · exact hm (Nat.prime_two.dvd_of_dvd_pow h)
      have hm6 : ¬ 2 ∣ m ^ 6 := fun h => hm (Nat.prime_two.dvd_of_dvd_pow h)
      have h2 : Irreducible (2 : R) := by
        have := irreducible_primesEquiv w
        have h' : Irreducible ((natGenerator w : ℕ) : R) := this
        rw [hg] at h'
        simpa using h'
      refine not_hasGoodReduction_minimal_of_c₄ R _ h2 ?_ ?_
      · rw [hΔ, valuation_natCast_of_eq w hg hm6 (a := 64 * (2 * m) ^ 6) (d := 12) (m := m ^ 6)
          (by ring)]
        norm_num
      · rw [hc4, valuation_natCast_of_eq w hg hmm (a := 48 * (2 * m) ^ 2) (d := 6) (m := 3 * m ^ 2)
          (by ring)]
        norm_num
    · have hn6 : ¬ 2 ∣ n ^ 6 := fun h => hodd (Nat.prime_two.dvd_of_dvd_pow h)
      refine not_hasGoodReduction_minimal_of_valuation_Δ R _ 6 (by norm_num) ?_
      rw [hΔ]
      exact valuation_natCast_of_eq w hg hn6 (by ring)
  · have hgn' : g ∣ n := by
      rcases (Nat.Prime.dvd_mul hgp).1 hgn with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hgp Nat.prime_two).1 h) hg2
      · exact h
    obtain ⟨m, rfl⟩ := hgn'
    have hm : ¬ g ∣ m := by
      rintro ⟨t, rfl⟩
      have := hn g ⟨t, by ring⟩
      exact hgp.one_lt.ne' (Nat.isUnit_iff.1 this)
    have hm64 : ¬ g ∣ 64 * m ^ 6 := by
      intro h
      rcases (Nat.Prime.dvd_mul hgp).1 h with h | h
      · exact hg2 (hg64 h)
      · exact hm (hgdvd m h)
    refine not_hasGoodReduction_minimal_of_valuation_Δ R _ 6 (by norm_num) ?_
    rw [hΔ]
    exact valuation_natCast_of_eq w hg hm64 (by ring)

end Curve

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
