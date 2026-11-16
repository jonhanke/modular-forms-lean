import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.LocalFactorsAux
import ModularFormsKB.Miyake.Sec4_3.Defs
import TauCeti.AlgebraicGeometry.EllipticCurve.HasseBound
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# The Hasse bound for the coefficients of $L(E, s)$

For an elliptic curve $E$ over $\mathbb Q$ with $L(E, s) = \sum a_n n^{-s}$ (Mathlib's `WeierstrassCurve.LFunction`):
- `norm_coeffE_le`: $|a_n| \le d(n)\sqrt n$, from Hasse's bound $a_p^2 \le 4p$ at the primes of good reduction (Tau
  Ceti `WeierstrassCurve.frobeniusTrace_sq_le_four_mul_card`), $|a_{p^k}| \le 1$ at the bad primes, the recursion
  $a_{p^{k+2}} = a_pa_{p^{k+1}} - pa_{p^k}$ and multiplicativity;
- `lSeriesSummable_coeffE`, `abscissaOfAbsConv_coeffE_le`: the series converges absolutely on
  $\operatorname{Re}s > 3/2$, the half-plane of Milne's strong Hasse–Weil conjecture;
- `coeffGrowth_coeffE`: polynomial growth, the hypothesis of Miyake's converse theorems.
-/

namespace ModularFormsKB.Elliptic

open ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves Polynomial
open IsDedekindDomain NumberField Rat.HeightOneSpectrum Filter

/-! ### Auxiliary lemmas -/

/-- The recursion `c (k+2) = a c (k+1) - p c k` with `a² ≤ 4p` gives `|c k| ≤ (k+1) p^{k/2}`. -/
private theorem seq_bound (a : ℤ) (p : ℕ) (hp : 1 ≤ p) (ha : a ^ 2 ≤ 4 * (p : ℤ)) (c : ℕ → ℤ)
    (h0 : c 0 = 1) (h1 : c 1 = a) (hr : ∀ k, c (k + 2) = a * c (k + 1) - p * c k) (k : ℕ) :
    |(c k : ℝ)| ≤ ((k : ℝ) + 1) * Real.sqrt p ^ k := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  set s := Real.sqrt (p : ℝ) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = p := Real.sq_sqrt (by linarith)
  have ha' : (a : ℝ) ^ 2 ≤ 4 * p := by exact_mod_cast ha
  have hab : |(a : ℝ) / 2| ≤ s := by
    apply abs_le_of_sq_le_sq _ hs0
    rw [div_pow, hs2]; linarith
  have inv : ∀ k, (c (k + 1) : ℝ) ^ 2 - a * c k * c (k + 1) + p * (c k : ℝ) ^ 2 = (p : ℝ) ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp [h0, h1]; ring
    | succ k ih =>
      have h2 : (c (k + 2) : ℝ) = a * c (k + 1) - p * c k := by exact_mod_cast hr k
      rw [h2]
      linear_combination (p : ℝ) * ih
  have step : ∀ k, |(c (k + 1) : ℝ)| ≤ s * |(c k : ℝ)| + s ^ (k + 1) := by
    intro k
    have h := inv k
    have hsq : ((c (k + 1) : ℝ) - a * c k / 2) ^ 2 ≤ (s ^ (k + 1)) ^ 2 := by
      have : (s ^ (k + 1)) ^ 2 = (p : ℝ) ^ (k + 1) := by rw [← pow_mul, mul_comm, pow_mul, hs2]
      rw [this, ← h]
      nlinarith [mul_nonneg (sub_nonneg.2 ha') (sq_nonneg (c k : ℝ))]
    have h2 := abs_le_of_sq_le_sq hsq (pow_nonneg hs0 _)
    calc |(c (k + 1) : ℝ)| = |((c (k + 1) : ℝ) - a * c k / 2) + ((a : ℝ) / 2) * c k| := by ring_nf
      _ ≤ |(c (k + 1) : ℝ) - a * c k / 2| + |((a : ℝ) / 2) * c k| := abs_add_le _ _
      _ ≤ s ^ (k + 1) + s * |(c k : ℝ)| := by
        rw [abs_mul]; gcongr
      _ = _ := by ring
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    have := step k
    have h3 := mul_le_mul_of_nonneg_left ih hs0
    push_cast
    calc |(c (k + 1) : ℝ)| ≤ s * (((k : ℝ) + 1) * s ^ k) + s ^ (k + 1) := by linarith
      _ = ((k : ℝ) + 1 + 1) * s ^ (k + 1) := by ring

/-- The local polynomial of a Weierstrass curve is `1 - aT + qT²` with `a² ≤ 4q`, or `1 - aT` with
`a² ≤ 1`. -/
private theorem localPolynomial_cases {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (IsLocalRing.ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) :
    ∃ a : ℤ, (a ^ 2 ≤ 4 * (Nat.card (IsLocalRing.ResidueField R) : ℤ) ∧
        W.localPolynomial R = 1 - C a * X + C (Nat.card (IsLocalRing.ResidueField R) : ℤ) * X ^ 2) ∨
      (a ^ 2 ≤ 1 ∧ W.localPolynomial R = 1 - C a * X) := by
  by_cases h : (W.minimal R).HasGoodReduction R
  · exact ⟨_, Or.inl ⟨WeierstrassCurve.frobeniusTrace_sq_le_four_mul_card _,
      WeierstrassCurve.localPolynomial_eq_of_hasGoodReduction R W h⟩⟩
  · refine ⟨_, Or.inr ⟨?_, WeierstrassCurve.localPolynomial_eq_of_not_hasGoodReduction R W h⟩⟩
    rcases WeierstrassCurve.hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction R
      (W := W.minimal R) with hg | hm | ha
    · exact absurd hg h
    · by_cases hs : (W.minimal R).HasSplitMultiplicativeReduction R
      · rw [hs.frobeniusTrace_reduction_eq_one R]; norm_num
      · rw [hm.frobeniusTrace_reduction_eq_neg_one R hs]; norm_num
    · rw [ha.frobeniusTrace_reduction_eq_zero R]; norm_num

/-- The bound at prime powers. -/
private theorem norm_LFunction_prime_pow_le (W : WeierstrassCurve ℚ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ‖((W.LFunction (p ^ k) : ℤ) : ℂ)‖ ≤ ((k : ℝ) + 1) * Real.sqrt p ^ k := by
  rw [LFunction_prime_pow_eq W hp k, Complex.norm_intCast]
  set w : HeightOneSpectrum (𝓞 ℚ) := primesEquiv.symm (⟨p, hp⟩ : Nat.Primes) with hw
  have hq : Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers ℚ)) = p := by
    rw [natCard_residueField]; exact natGenerator_symm hp
  have hp1 : 1 ≤ p := hp.one_lt.le
  obtain ⟨a, ⟨h1, h⟩ | ⟨h1, h⟩⟩ := localPolynomial_cases (R := w.adicCompletionIntegers ℚ)
    (baseChangeAt W w)
  · rw [hq] at h1 h
    have hs : (((1 - C a * X + C (p : ℤ) * X ^ 2 : ℤ[X])) : PowerSeries ℤ) * localSeriesOf W w = 1 := by
      have := PowerSeries.mul_invOfUnit ((1 - C a * X + C (p : ℤ) * X ^ 2 : ℤ[X]) : PowerSeries ℤ)
        (1 : ℤˣ) (by simp)
      unfold localSeriesOf WeierstrassCurve.localPowerSeries
      rw [h]; exact this
    obtain ⟨c0, c1, cr⟩ := coeff_inv_quadratic a p _ hs
    exact seq_bound a p hp1 h1 (fun k => (localSeriesOf W w).coeff k) c0 c1 cr k
  · have hs : (((1 - C a * X + C (0 : ℤ) * X ^ 2 : ℤ[X])) : PowerSeries ℤ) * localSeriesOf W w = 1 := by
      have := PowerSeries.mul_invOfUnit ((1 - C a * X + C (0 : ℤ) * X ^ 2 : ℤ[X]) : PowerSeries ℤ)
        (1 : ℤˣ) (by simp)
      unfold localSeriesOf WeierstrassCurve.localPowerSeries
      rw [h]; simp
    obtain ⟨c0, c1, cr⟩ := coeff_inv_quadratic a 0 _ hs
    have hpow : ∀ k, (localSeriesOf W w).coeff k = a ^ k ∧
        (localSeriesOf W w).coeff (k + 1) = a ^ (k + 1) := by
      intro k
      induction k with
      | zero => simp [c0, c1]
      | succ k ih => refine ⟨ih.2, ?_⟩; rw [cr k, ih.2]; ring
    have ha1 : |a| ≤ 1 := by nlinarith [abs_nonneg a, sq_abs a]
    rw [(hpow k).1]
    have h2 : |(a : ℝ)| ≤ 1 := by exact_mod_cast ha1
    have h3 : |((a ^ k : ℤ) : ℝ)| ≤ 1 := by
      push_cast; rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h2
    have h4 : (1 : ℝ) ≤ Real.sqrt p ^ k :=
      one_le_pow₀ (Real.one_le_sqrt.2 (by exact_mod_cast hp1))
    have h5 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith

/-- The coefficients $a_n$ of $L(E, s)$ as complex numbers. -/
noncomputable def coeffE (E : WeierstrassCurve ℚ) (n : ℕ) : ℂ := (E.LFunction n : ℂ)

/-- **The Hasse bound for the coefficients of $L(E, s)$**: $|a_n| \le d(n)\sqrt n$. -/
theorem norm_coeffE_le (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) :
    ‖coeffE E n‖ ≤ (n.divisors.card : ℝ) * Real.sqrt n := by
  unfold coeffE
  refine Nat.recOnPosPrimePosCoprime
    (motive := fun n => ‖((E.LFunction n : ℤ) : ℂ)‖ ≤ (n.divisors.card : ℝ) * Real.sqrt n) ?_ ?_ ?_ ?_ n
  · intro p k hp _
    have hd : (p ^ k).divisors.card = k + 1 := by simp [Nat.divisors_prime_pow hp]
    have hsq : Real.sqrt ((p ^ k : ℕ) : ℝ) = Real.sqrt p ^ k := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
        Real.mul_self_sqrt (by positivity), Nat.cast_pow]
    rw [hd, hsq]
    exact_mod_cast norm_LFunction_prime_pow_le E hp k
  · simp
  · simp [E.isMultiplicative_LFunction.map_one]
  · intro a b _ _ hab iha ihb
    rw [E.isMultiplicative_LFunction.map_mul_of_coprime hab, Int.cast_mul, norm_mul,
      hab.card_divisors_mul, Nat.cast_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    calc _ ≤ ((a.divisors.card : ℝ) * Real.sqrt a) * ((b.divisors.card : ℝ) * Real.sqrt b) :=
          mul_le_mul iha ihb (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- $L(E, s)$ converges absolutely on $\operatorname{Re} s > 3/2$. -/
theorem lSeriesSummable_coeffE (E : WeierstrassCurve ℚ) [E.IsElliptic] {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable (coeffE E) s := by
  let Z : ArithmeticFunction ℂ := ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)
  have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
  have hZ : LSeriesSummable (fun n => Z n) (s - 1 / 2) :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.2 (by rw [hre]; linarith)
  have hd : ∀ n, (Z * Z) n = (n.divisors.card : ℂ) := by
    intro n
    have : Z * Z = ((ArithmeticFunction.sigma 0 : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) := by
      rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma, ArithmeticFunction.pow_zero_eq_zeta,
        ArithmeticFunction.natCoe_mul]
    rw [this, ArithmeticFunction.natCoe_apply, ArithmeticFunction.sigma_zero_apply]
  have hsum := ArithmeticFunction.LSeriesSummable_mul hZ hZ
  unfold LSeriesSummable at hsum ⊢
  rw [← summable_norm_iff] at hsum ⊢
  refine hsum.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  split_ifs with hn
  · exact le_rfl
  · have hx : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [hd,Complex.norm_natCast, hre,
      Real.rpow_sub hx, div_div_eq_mul_div, ← Real.sqrt_eq_rpow]
    exact div_le_div_of_nonneg_right (norm_coeffE_le E n) (by positivity)

/-- The abscissa of absolute convergence of $L(E, s)$ is at most $3/2$. -/
theorem abscissaOfAbsConv_coeffE_le (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    LSeries.abscissaOfAbsConv (coeffE E) ≤ ((3 / 2 : ℝ) : EReal) :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    lSeriesSummable_coeffE E (by simpa using hy)

/-- The coefficients of $L(E, s)$ have polynomial growth: $a_n = O(n^{3/2})$. -/
theorem coeffGrowth_coeffE (E : WeierstrassCurve ℚ) [E.IsElliptic] : Miyake.CoeffGrowth (coeffE E) := by
  refine ⟨3 / 2, Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun n => ?_)⟩
  have h := norm_coeffE_le E n
  have hd : (n.divisors.card : ℝ) ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
  have h32 : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * Real.sqrt n := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' (Nat.cast_nonneg n) (by norm_num),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [one_mul, Real.norm_of_nonneg (by positivity), h32]
  exact h.trans (mul_le_mul_of_nonneg_right hd (Real.sqrt_nonneg _))

end ModularFormsKB.Elliptic
