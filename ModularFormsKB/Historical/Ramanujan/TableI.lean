import ModularFormsKB.Historical.Ramanujan.EisensteinTable
import ModularFormsKB.Citation
/-!
# Ramanujan's Table I: `½ ζ(-s) + ∑ σ_s(n) xⁿ` as polynomials in `Q`, `R`, and the coefficients of `1/R`

Ramanujan, *Collected Papers*, No. 18 (*On certain arithmetical functions*, 1916), Table I, pp. 141–142: for odd
`s = 1, 3, …, 31` the series `½ ζ(-s) + ∑_{n ≥ 1} σ_s(n) xⁿ` is a polynomial in `Q`, `R` (in `P` for `s = 1`) of
weight `s + 1`. In modern terms this is the expression of the Eisenstein series `E_{s+1}` through `E₄`, `E₆`
(`½ ζ(-s) = -B_{s+1}/(2(s+1))`). The coefficients below were recomputed by exact rational arithmetic from the
`q`-expansions (and agree with the printed table); the
weight-`32` entry in Ramanujan's integral normalization, quoted by Hardy in No. 30, is `weightThirtyTwoIdentity`.

The proofs use the Sturm bound for level one (`ModularForm.sturm_bound_levelOne_nat`): a modular form of weight `k`
whose `q`-coefficients vanish up to `⌊k/12⌋` is zero; then `EisensteinSeries.q_expansion_bernoulli` and
`riemannZeta_neg_nat_eq_bernoulli` give the series form.

Hardy and Ramanujan, No. 37, § 6, (6.1), p. 317: the coefficients `p_n` of
`1/R = 1/(1 - 504 ∑ σ₅(m) xᵐ) = ∑ p_n xⁿ` are integers, `p₀, …, p₁₂ = 1, 504, 270648, …`. Formalized for the
formal power series of `R` over `ℚ` (`ramanujanRInvCoeffs`).
-/

noncomputable section

open Complex
open scoped ArithmeticFunction.sigma

namespace ModularFormsKB.Historical.Ramanujan

/-- Row `s` of Ramanujan's Table I (No. 18, pp. 141–142): `½ ζ(-s) + ∑_{n ≥ 1} σ_s(n) xⁿ = F(Q(x), R(x))` for
`‖x‖ < 1`. -/
def TableIRow (s : ℕ) (F : ℂ → ℂ → ℂ) : Prop :=
  ∀ x : ℂ, ‖x‖ < 1 →
    (1 / 2) * riemannZeta (-(s : ℂ)) + ∑' n : ℕ+, (σ s n : ℂ) * x ^ (n : ℕ) = F (Q x) (R x)

/-- Row `s = 1` of Table I: `½ ζ(-1) + ∑ σ₁(n) xⁿ = -P/24`. -/
@[kb "ramanujan1927" "No. 18, § 5, Table I, (26), p. 141"]
def TableIRowOne : Prop :=
  ∀ x : ℂ, ‖x‖ < 1 →
    (1 / 2) * riemannZeta (-1) + ∑' n : ℕ+, (σ 1 n : ℂ) * x ^ (n : ℕ) = -(1 / 24) * P x

/-- **Ramanujan, No. 18, Table I** (pp. 141–142): the rows `s = 3, 5, …, 31`. -/
@[kb "ramanujan1927" "No. 18, § 5, Table I, (26), pp. 141–142"]
def RamanujanTableI : Prop :=
  TableIRow 3 (fun Q _ ↦ 1 / 240 * Q) ∧
  TableIRow 5 (fun _ R ↦ -1 / 504 * R) ∧
  TableIRow 7 (fun Q _ ↦ 1 / 480 * Q ^ 2) ∧
  TableIRow 9 (fun Q R ↦ -1 / 264 * Q * R) ∧
  TableIRow 11 (fun Q R ↦ 7 / 1040 * Q ^ 3 + 25 / 6552 * R ^ 2) ∧
  TableIRow 13 (fun Q R ↦ -1 / 24 * Q ^ 2 * R) ∧
  TableIRow 15 (fun Q R ↦ 539 / 5440 * Q ^ 4 + 25 / 204 * Q * R ^ 2) ∧
  TableIRow 17 (fun Q R ↦ -203 / 152 * Q ^ 3 * R - 1375 / 7182 * R ^ 3) ∧
  TableIRow 19 (fun Q R ↦ 1617 / 400 * Q ^ 5 + 2425 / 264 * Q ^ 2 * R ^ 2) ∧
  TableIRow 21 (fun Q R ↦ -19061 / 184 * Q ^ 4 * R - 5125 / 138 * Q * R ^ 3) ∧
  TableIRow 23 (fun Q R ↦ 788557 / 2080 * Q ^ 6 + 17500 / 13 * Q ^ 3 * R ^ 2 + 257125 / 3276 * R ^ 4) ∧
  TableIRow 25 (fun Q R ↦ -130977 / 8 * Q ^ 5 * R - 33125 / 3 * Q ^ 2 * R ^ 3) ∧
  TableIRow 27 (fun Q R ↦
    163231299 / 2320 * Q ^ 7 + 83587875 / 232 * Q ^ 4 * R ^ 2 + 4943125 / 87 * Q * R ^ 4) ∧
  TableIRow 29 (fun Q R ↦
    -1177209957 / 248 * Q ^ 6 * R - 1748691875 / 341 * Q ^ 3 * R ^ 3 - 295693750 / 1953 * R ^ 5) ∧
  TableIRow 31 (fun Q R ↦
    254804057739 / 10880 * Q ^ 8 + 11091469725 / 68 * Q ^ 5 * R ^ 2 + 5065635625 / 102 * Q ^ 2 * R ^ 4)

/-- **Ramanujan's weight-`32` formula** (No. 18, Table I, last row, as quoted by Hardy in No. 30): `7709321041217 + 32640 ∑ σ₃₁(n) xⁿ = 764412173217 Q⁸ + 5323905468000 Q⁵ R² + 1621003400000 Q² R⁴`. -/
@[kb "ramanujan1927" "No. 18, § 5, Table I, (26), p. 142 (last row)"]
def WeightThirtyTwoIdentity : Prop :=
  ∀ x : ℂ, ‖x‖ < 1 →
    7709321041217 + 32640 * ∑' n : ℕ+, (σ 31 n : ℂ) * x ^ (n : ℕ) =
      764412173217 * Q x ^ 8 + 5323905468000 * Q x ^ 5 * R x ^ 2 + 1621003400000 * Q x ^ 2 * R x ^ 4

/-- The formal power series `R = 1 - 504 ∑_{m ≥ 1} σ₅(m) Xᵐ` over `ℚ`. -/
def Rseries : PowerSeries ℚ :=
  PowerSeries.mk fun m ↦ if m = 0 then 1 else -504 * (σ 5 m : ℚ)

/-- The values `p₀, …, p₁₂` (No. 37, § 6, p. 317). -/
def ramanujanRInvValues : List ℤ :=
  [1, 504, 270648, 144912096, 77599626552, 41553943041744, 22251789971649504, 11915647845248387520,
    6380729991419236488504, 3416827666558895485479576, 1829682703808504464920468048,
    979779820147442370107345764512, 524663917940510191509934144603104]

/-- **Hardy–Ramanujan, No. 37, § 6, (6.1)** (p. 317): the coefficients of `1/R`
are integers, and the first thirteen are `p₀, …, p₁₂ = 1, 504, 270648, …`. -/
@[kb "ramanujan1927" "No. 37, § 6, (6.1), p. 317"]
def RamanujanRInvCoeffs : Prop :=
  (∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n Rseries⁻¹ = z) ∧
  ∀ n : Fin 13, PowerSeries.coeff (n : ℕ) Rseries⁻¹ = (ramanujanRInvValues.get ⟨n, by simp [ramanujanRInvValues]⟩ : ℚ)

/-! ### Truncated `q`-expansion arithmetic (coefficients `0, 1, 2`) -/

/-- Truncated power series data `(c₀, c₁, c₂)` over `ℚ`. -/
private abbrev T3 := ℚ × ℚ × ℚ

/-- Product of truncations. -/
private def m3 (a b : T3) : T3 :=
  (a.1 * b.1, a.1 * b.2.1 + a.2.1 * b.1, a.1 * b.2.2 + a.2.1 * b.2.1 + a.2.2 * b.1)

/-- Power of a truncation. -/
private def p3 (a : T3) : ℕ → T3
  | 0 => (1, 0, 0)
  | n + 1 => m3 (p3 a n) a

/-- The truncation of `E₄`. -/
private def e4t : T3 := (1, 240, 2160)

/-- The truncation of `E₆`. -/
private def e6t : T3 := (1, -504, -16632)

/-- Coefficient `n < 3` of the truncated monomial `E₄ⁱ E₆ʲ`. -/
private def mc (i j : ℕ) (n : ℕ) : ℚ :=
  let t := m3 (p3 e4t i) (p3 e6t j)
  if n = 0 then t.1 else if n = 1 then t.2.1 else t.2.2

/-- `f` has truncation `a`. -/
private def Tr3 (f : PowerSeries ℂ) (a : T3) : Prop :=
  PowerSeries.coeff 0 f = a.1 ∧ PowerSeries.coeff 1 f = a.2.1 ∧ PowerSeries.coeff 2 f = a.2.2

private lemma Tr3.mul {f g : PowerSeries ℂ} {a b : T3} (hf : Tr3 f a) (hg : Tr3 g b) :
    Tr3 (f * g) (m3 a b) := by
  obtain ⟨f0, f1, f2⟩ := hf
  obtain ⟨g0, g1, g2⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · simp [PowerSeries.coeff_mul, -PowerSeries.coeff_zero_eq_constantCoeff, f0, g0, m3]
  · simp [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, -PowerSeries.coeff_zero_eq_constantCoeff,
      f0, f1, g0, g1, m3]
  · simp [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, -PowerSeries.coeff_zero_eq_constantCoeff,
      f0, f1, f2, g0, g1, g2, m3]
    ring

private lemma Tr3.one : Tr3 1 (1, 0, 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [PowerSeries.coeff_one]

private lemma Tr3.pow {f : PowerSeries ℂ} {a : T3} (hf : Tr3 f a) (n : ℕ) : Tr3 (f ^ n) (p3 a n) := by
  induction n with
  | zero => simpa [p3] using Tr3.one
  | succ n ih => rw [pow_succ]; exact ih.mul hf

private lemma Tr3.coeff {f : PowerSeries ℂ} {a : T3} (h : Tr3 f a) (n : ℕ) (hn : n < 3) :
    PowerSeries.coeff n f = (if n = 0 then a.1 else if n = 1 then a.2.1 else a.2.2 : ℚ) := by
  obtain ⟨h0, h1, h2⟩ := h
  interval_cases n <;> simp [h0, h1, h2]

/-! ### Fast evaluation of Bernoulli numbers -/

/-- The list `[B'₀, …, B'_{n-1}]` computed by the recursion for `bernoulli'` (kernel-friendly). -/
private def bernList : ℕ → List ℚ
  | 0 => []
  | n + 1 =>
    bernList n ++ [1 - ∑ k ∈ Finset.range n, (n.choose k : ℚ) / ((n : ℚ) - k + 1) * (bernList n).getD k 0]

private lemma bernList_length (n : ℕ) : (bernList n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bernList, ih]

private lemma bernList_getD (n : ℕ) : ∀ k < n, (bernList n).getD k 0 = bernoulli' k := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    have hlen := bernList_length n
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [bernList, List.getD_append _ _ _ _ (by omega), ih k hk]
    · rw [bernList, List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self, bernoulli'_def]
      simp only [List.getD_cons_zero]
      congr 1
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      rw [ih j (Finset.mem_range.mp hj)]

private lemma bernoulli_even_eq (k : ℕ) (hk : k ≠ 1) (q : ℚ) (h : (bernList (k + 1)).getD k 0 = q) :
    bernoulli k = q := by
  rw [bernoulli_eq_bernoulli'_of_ne_one hk, ← h, bernList_getD (k + 1) k (by omega)]

/-! ### From identities between Eisenstein series to rows of Table I -/

open UpperHalfPlane hiding I
open scoped MatrixGroups

/-- The monomial `E₄ⁱ E₆ʲ` as a level-one modular form of weight `k = 4i + 6j`. -/
private noncomputable def monoMF (k i j : ℕ) (h : 4 * i + 6 * j = k) : ModularForm 𝒮ℒ (k : ℤ) :=
  ModularForm.mcast (by omega) ((ModularForm.E₄.pow i).mul (ModularForm.E₆.pow j))

private lemma monoMF_apply (k i j : ℕ) (h : 4 * i + 6 * j = k) (z : ℍ) :
    monoMF k i j h z = ModularForm.E₄ z ^ i * ModularForm.E₆ z ^ j := by
  have h1 : (ModularForm.E₄.pow i) z = ModularForm.E₄ z ^ i := congrFun (ModularForm.coe_pow _ i) z
  have h2 : (ModularForm.E₆.pow j) z = ModularForm.E₆ z ^ j := congrFun (ModularForm.coe_pow _ j) z
  have hm : ((ModularForm.E₄.pow i).mul (ModularForm.E₆.pow j)) z =
      (ModularForm.E₄.pow i) z * (ModularForm.E₆.pow j) z := rfl
  show ((ModularForm.E₄.pow i).mul (ModularForm.E₆.pow j)) z = _
  rw [hm, h1, h2]

private lemma qE_sub {k : ℤ} (A B : ModularForm 𝒮ℒ k) :
    qExpansion 1 ⇑(A - B) = qExpansion 1 ⇑A - qExpansion 1 ⇑B := by
  rw [FunLike.coe_sub]
  exact ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL A B

private lemma qE_smul {k : ℤ} (c : ℂ) (A : ModularForm 𝒮ℒ k) :
    qExpansion 1 ⇑(c • A) = c • qExpansion 1 ⇑A := by
  rw [FunLike.coe_smul]
  exact ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c A

private lemma monoMF_q (k i j : ℕ) (h : 4 * i + 6 * j = k) :
    qExpansion 1 (monoMF k i j h) =
      qExpansion 1 ModularForm.E₄ ^ i * qExpansion 1 ModularForm.E₆ ^ j := by
  rw [monoMF, ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

private lemma sigma_one' (s : ℕ) : (σ s 1 : ℚ) = 1 := by
  simp [ArithmeticFunction.sigma_apply]

private lemma sigma_two' (s : ℕ) : (σ s 2 : ℚ) = 1 + 2 ^ s := by
  have : (σ s 2 : ℕ) = 1 + 2 ^ s := by
    rw [ArithmeticFunction.sigma_apply, Nat.Prime.divisors Nat.prime_two]
    simp
  exact_mod_cast this

private lemma tr3_E4 : Tr3 (qExpansion 1 ModularForm.E₄) e4t := by
  refine ⟨?_, ?_, ?_⟩
  · simp [e4t, EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩]
  · simp [e4t, ModularForm.E₄_qExpansion_coeff_one]
  · rw [EisensteinSeries.E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel]
    have : (σ 3 2 : ℂ) = 9 := by
      have := sigma_two' 3
      have h2 : (σ 3 2 : ℚ) = 9 := by rw [this]; norm_num
      exact_mod_cast h2
    simp [e4t, this]
    norm_num

private lemma tr3_E6 : Tr3 (qExpansion 1 ModularForm.E₆) e6t := by
  refine ⟨?_, ?_, ?_⟩
  · simp [e6t, EisensteinSeries.E_qExpansion_coeff_zero _ ⟨3, rfl⟩]
  · simp [e6t, ModularForm.E₆_qExpansion_coeff_one]
  · rw [EisensteinSeries.E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli 6 = 1 / 42 by decide +kernel]
    have : (σ 5 2 : ℂ) = 33 := by
      have := sigma_two' 5
      have h2 : (σ 5 2 : ℚ) = 33 := by rw [this]; norm_num
      exact_mod_cast h2
    simp [e6t, this]
    norm_num

private lemma mono_coeff (i j n : ℕ) (hn : n < 3) :
    PowerSeries.coeff n (qExpansion 1 ModularForm.E₄ ^ i * qExpansion 1 ModularForm.E₆ ^ j) =
      (mc i j n : ℂ) :=
  ((tr3_E4.pow i).mul (tr3_E6.pow j)).coeff n hn

/-- Sturm-bound step: a three-term polynomial in `E₄`, `E₆` whose truncation (up to `⌊k/12⌋`) matches
`ck E_k` equals `ck E_k`. -/
private lemma eis_poly3 (s : ℕ) (hs : Odd s) (hs3 : 3 ≤ s) (hs35 : s < 35) (b : ℚ)
    (hb : bernoulli (s + 1) = b) (hb0 : b ≠ 0) (c1 c2 c3 : ℚ) (i1 j1 i2 j2 i3 j3 : ℕ)
    (w1 : 4 * i1 + 6 * j1 = s + 1) (w2 : 4 * i2 + 6 * j2 = s + 1) (w3 : 4 * i3 + 6 * j3 = s + 1)
    (h : ∀ n < 3, n ≤ (s + 1) / 12 →
      c1 * mc i1 j1 n + c2 * mc i2 j2 n + c3 * mc i3 j3 n =
        if n = 0 then -b / (2 * (s + 1)) else (σ s n : ℚ)) (z : ℍ) :
    ((-b / (2 * (s + 1)) : ℚ) : ℂ) * ModularForm.E (k := s + 1) (by omega) z =
      c1 * (ModularForm.E₄ z ^ i1 * ModularForm.E₆ z ^ j1) +
      c2 * (ModularForm.E₄ z ^ i2 * ModularForm.E₆ z ^ j2) +
      c3 * (ModularForm.E₄ z ^ i3 * ModularForm.E₆ z ^ j3) := by
  have hk2 : Even (s + 1) := hs.add_one
  let f : ModularForm 𝒮ℒ ((s + 1 : ℕ) : ℤ) :=
    (((-b / (2 * (s + 1)) : ℚ) : ℂ)) • ModularForm.E (k := s + 1) (by omega) -
      (c1 : ℂ) • monoMF (s + 1) i1 j1 w1 - (c2 : ℂ) • monoMF (s + 1) i2 j2 w2 -
      (c3 : ℂ) • monoMF (s + 1) i3 j3 w3
  have hcoef : ∀ n, PowerSeries.coeff n (qExpansion 1 f) =
      ((-b / (2 * (s + 1)) : ℚ) : ℂ) * PowerSeries.coeff n (qExpansion 1
        (ModularForm.E (k := s + 1) (by omega))) -
      c1 * PowerSeries.coeff n (qExpansion 1 ModularForm.E₄ ^ i1 * qExpansion 1 ModularForm.E₆ ^ j1) -
      c2 * PowerSeries.coeff n (qExpansion 1 ModularForm.E₄ ^ i2 * qExpansion 1 ModularForm.E₆ ^ j2) -
      c3 * PowerSeries.coeff n (qExpansion 1 ModularForm.E₄ ^ i3 * qExpansion 1 ModularForm.E₆ ^ j3) := by
    intro n
    simp only [f, qE_sub, qE_smul, monoMF_q, map_sub, PowerSeries.coeff_smul, smul_eq_mul]
  have hb0' : (b : ℂ) ≠ 0 := Rat.cast_ne_zero.mpr hb0
  have hs1 : ((s : ℂ) + 1) ≠ 0 := by norm_cast
  have hz : ∀ n < 3, n ≤ (s + 1) / 12 → PowerSeries.coeff n (qExpansion 1 f) = 0 := by
    intro n hn hn12
    rw [hcoef, mono_coeff _ _ n hn, mono_coeff _ _ n hn, mono_coeff _ _ n hn,
      EisensteinSeries.E_qExpansion_coeff (by omega) hk2 n]
    have hh := congrArg (fun q : ℚ ↦ (q : ℂ)) (h n hn hn12)
    simp only [Rat.cast_add, Rat.cast_mul] at hh
    by_cases hn0 : n = 0
    · subst hn0
      simp only [ite_true] at hh ⊢
      linear_combination -hh
    · simp only [hn0, ite_false] at hh ⊢
      rw [hb]
      simp only [Nat.add_sub_cancel, Rat.cast_natCast] at hh ⊢
      push_cast at hh ⊢
      have key : (-(b : ℂ) / (2 * ((s : ℂ) + 1))) * (-(2 * ((s : ℂ) + 1) / b)) = 1 := by
        field_simp
      linear_combination ((σ s n : ℕ) : ℂ) * key - hh
  have h0 : f = 0 := by
    refine ModularForm.sturm_bound_levelOne_nat (k := s + 1) (f := f) ?_
    refine lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self _))
      (PowerSeries.nat_le_order _ ((s + 1) / 12 + 1) ?_)
    intro n hn
    exact hz n (by omega) (by omega)
  have := congrArg (fun g : ModularForm 𝒮ℒ ((s + 1 : ℕ) : ℤ) ↦ g z) h0
  simp [f] at this
  rw [monoMF_apply, monoMF_apply, monoMF_apply] at this
  push_cast at this ⊢
  linear_combination this

private lemma p3_fst (a : T3) (ha : a.1 = 1) (n : ℕ) : (p3 a n).1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [p3, m3, ih, ha]

private lemma mc_zero (i j : ℕ) : mc i j 0 = 1 := by
  have h4 := p3_fst e4t rfl i
  have h6 := p3_fst e6t rfl j
  simp [mc, m3, h4, h6]

/-- Rows of Table I with at most three monomials, from the coefficient check. -/
private lemma tableRow_poly3 (s : ℕ) (hs : Odd s) (hs3 : 3 ≤ s) (hs35 : s < 35) (b : ℚ)
    (hb : bernoulli (s + 1) = b) (hb0 : b ≠ 0) (c1 c2 c3 : ℚ) (i1 j1 i2 j2 i3 j3 : ℕ)
    (w1 : 4 * i1 + 6 * j1 = s + 1) (w2 : 4 * i2 + 6 * j2 = s + 1) (w3 : 4 * i3 + 6 * j3 = s + 1)
    (h : ∀ n < 3, n ≤ (s + 1) / 12 →
      c1 * mc i1 j1 n + c2 * mc i2 j2 n + c3 * mc i3 j3 n =
        if n = 0 then -b / (2 * (s + 1)) else (σ s n : ℚ))
    (F : ℂ → ℂ → ℂ)
    (hF : ∀ Q R : ℂ, F Q R = c1 * (Q ^ i1 * R ^ j1) + c2 * (Q ^ i2 * R ^ j2) + c3 * (Q ^ i3 * R ^ j3)) :
    TableIRow s F := by
  have hk2 : Even (s + 1) := hs.add_one
  have hs1 : ((s : ℂ) + 1) ≠ 0 := by norm_cast
  have hζ : (1 / 2 : ℂ) * riemannZeta (-(s : ℂ)) = ((-b / (2 * (s + 1)) : ℚ) : ℂ) := by
    rw [riemannZeta_neg_nat_eq_bernoulli, hs.neg_one_pow, hb]
    push_cast
    field_simp
  have h0 : c1 + c2 + c3 = -b / (2 * (s + 1)) := by
    have := h 0 (by norm_num) (Nat.zero_le _)
    simpa [mc_zero] using this
  intro x hx
  rw [hF]
  by_cases hx0 : x = 0
  · subst hx0
    have hsum0 : ∑' n : ℕ+, (σ s n : ℂ) * (0 : ℂ) ^ (n : ℕ) = 0 := by simp
    rw [hsum0, hζ, add_zero, Q_zero, R_zero]
    simp only [one_pow, mul_one]
    rw [← h0]
    push_cast
    rfl
  · obtain ⟨τ, rfl⟩ := exists_tau hx hx0
    rw [Q_exp, R_exp, hζ,
      ← eis_poly3 s hs hs3 hs35 b hb hb0 c1 c2 c3 i1 j1 i2 j2 i3 j3 w1 w2 w3 h τ]
    have hE := EisensteinSeries.q_expansion_bernoulli (k := s + 1) (by omega) hk2 τ
    simp_rw [zpow_natCast, Nat.add_sub_cancel] at hE
    show _ = _ * ModularForm.E (k := s + 1) _ τ
    rw [hE, hb]
    have hb0' : (b : ℂ) ≠ 0 := Rat.cast_ne_zero.mpr hb0
    push_cast
    field_simp
    ring

/-! ### The rows -/

private theorem row3 : TableIRow 3 (fun Q _ ↦ 1 / 240 * Q) :=
  tableRow_poly3 3 (by decide) (by norm_num) (by norm_num) (-1 / 30)
    (bernoulli_even_eq 4 (by norm_num) _ (by decide +kernel)) (by norm_num)
    (1 / 240) 0 0 1 0 1 0 1 0 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) _
    (by intro Q R; push_cast; ring)

private theorem row5 : TableIRow 5 (fun _ R ↦ -1 / 504 * R) :=
  tableRow_poly3 5 (by decide) (by norm_num) (by norm_num) (1 / 42)
    (bernoulli_even_eq 6 (by norm_num) _ (by decide +kernel)) (by norm_num)
    (-1 / 504) 0 0 0 1 0 1 0 1 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) _
    (by intro Q R; push_cast; ring)

private theorem row7 : TableIRow 7 (fun Q _ ↦ 1 / 480 * Q ^ 2) :=
  tableRow_poly3 7 (by decide) (by norm_num) (by norm_num) (-1 / 30)
    (bernoulli_even_eq 8 (by norm_num) _ (by decide +kernel)) (by norm_num)
    (1 / 480) 0 0 2 0 2 0 2 0 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) _
    (by intro Q R; push_cast; ring)

private theorem row9 : TableIRow 9 (fun Q R ↦ -1 / 264 * Q * R) :=
  tableRow_poly3 9 (by decide) (by norm_num) (by norm_num) (5 / 66)
    (bernoulli_even_eq 10 (by norm_num) _ (by decide +kernel)) (by norm_num)
    (-1 / 264) 0 0 1 1 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) _
    (by intro Q R; push_cast; ring)

private theorem row11 : TableIRow 11 (fun Q R ↦ 7 / 1040 * Q ^ 3 + 25 / 6552 * R ^ 2) :=
  tableRow_poly3 11 (by decide) (by norm_num) (by norm_num) (-691 / 2730)
    (bernoulli_even_eq 12 (by norm_num) _ (by decide +kernel)) (by norm_num)
    (7 / 1040) (25 / 6552) 0 3 0 0 2 0 2 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) _
    (by intro Q R; push_cast; ring)

private theorem row13 : TableIRow 13 (fun Q R ↦ -1 / 24 * Q ^ 2 * R) :=
  tableRow_poly3 13 (by decide) (by norm_num) (by norm_num) (7 / 6)
    (bernoulli_even_eq 14 (by norm_num) _ (by decide +kernel)) (by norm_num)
    (-1 / 24) 0 0 2 1 2 1 2 1 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) _
    (by intro Q R; push_cast; ring)

private theorem row15 : TableIRow 15 (fun Q R ↦ 539 / 5440 * Q ^ 4 + 25 / 204 * Q * R ^ 2) :=
  tableRow_poly3 15 (by decide) (by norm_num) (by norm_num) (-3617 / 510)
    (bernoulli_even_eq 16 (by norm_num) _ (by decide +kernel)) (by norm_num)
    (539 / 5440) (25 / 204) 0 4 0 1 2 1 2 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) _
    (by intro Q R; push_cast; ring)

private theorem row17 :
    TableIRow 17 (fun Q R ↦ -203 / 152 * Q ^ 3 * R - 1375 / 7182 * R ^ 3) :=
  tableRow_poly3 17 (by decide) (by norm_num) (by norm_num) (43867 / 798)
    (bernoulli_even_eq 18 (by norm_num) _ (by decide +kernel)) (by norm_num)
    (-203 / 152) (-1375 / 7182) 0 3 1 0 3 0 3 (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) _ (by intro Q R; push_cast; ring)

private theorem row19 : TableIRow 19 (fun Q R ↦ 1617 / 400 * Q ^ 5 + 2425 / 264 * Q ^ 2 * R ^ 2) :=
  tableRow_poly3 19 (by decide) (by norm_num) (by norm_num) (-174611 / 330)
    (bernoulli_even_eq 20 (by norm_num) _ (by decide +kernel)) (by norm_num)
    (1617 / 400) (2425 / 264) 0 5 0 2 2 2 2 (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) _ (by intro Q R; push_cast; ring)

private theorem row21 :
    TableIRow 21 (fun Q R ↦ -19061 / 184 * Q ^ 4 * R - 5125 / 138 * Q * R ^ 3) :=
  tableRow_poly3 21 (by decide) (by norm_num) (by norm_num) (854513 / 138)
    (bernoulli_even_eq 22 (by norm_num) _ (by decide +kernel)) (by norm_num)
    (-19061 / 184) (-5125 / 138) 0 4 1 1 3 1 3 (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) _ (by intro Q R; push_cast; ring)

private theorem row23 :
    TableIRow 23 (fun Q R ↦ 788557 / 2080 * Q ^ 6 + 17500 / 13 * Q ^ 3 * R ^ 2 + 257125 / 3276 * R ^ 4) :=
  tableRow_poly3 23 (by decide) (by norm_num) (by norm_num) (-236364091 / 2730)
    (bernoulli_even_eq 24 (by norm_num) _ (by decide +kernel)) (by norm_num)
    (788557 / 2080) (17500 / 13) (257125 / 3276) 6 0 3 2 0 4 (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) _ (by intro Q R; push_cast; ring)

private theorem row25 :
    TableIRow 25 (fun Q R ↦ -130977 / 8 * Q ^ 5 * R - 33125 / 3 * Q ^ 2 * R ^ 3) :=
  tableRow_poly3 25 (by decide) (by norm_num) (by norm_num) (8553103 / 6)
    (bernoulli_even_eq 26 (by norm_num) _ (by decide +kernel)) (by norm_num)
    (-130977 / 8) (-33125 / 3) 0 5 1 2 3 2 3 (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) _ (by intro Q R; push_cast; ring)

private theorem row27 :
    TableIRow 27 (fun Q R ↦
      163231299 / 2320 * Q ^ 7 + 83587875 / 232 * Q ^ 4 * R ^ 2 + 4943125 / 87 * Q * R ^ 4) :=
  tableRow_poly3 27 (by decide) (by norm_num) (by norm_num) (-23749461029 / 870)
    (bernoulli_even_eq 28 (by norm_num) _ (by decide +kernel)) (by norm_num)
    (163231299 / 2320) (83587875 / 232) (4943125 / 87) 7 0 4 2 1 4 (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) _ (by intro Q R; push_cast; ring)

private theorem row29 :
    TableIRow 29 (fun Q R ↦
      -1177209957 / 248 * Q ^ 6 * R - 1748691875 / 341 * Q ^ 3 * R ^ 3 - 295693750 / 1953 * R ^ 5) :=
  tableRow_poly3 29 (by decide) (by norm_num) (by norm_num) (8615841276005 / 14322)
    (bernoulli_even_eq 30 (by norm_num) _ (by decide +kernel)) (by norm_num)
    (-1177209957 / 248) (-1748691875 / 341) (-295693750 / 1953) 6 1 3 3 0 5
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) _
    (by intro Q R; push_cast; ring)

private theorem row31 :
    TableIRow 31 (fun Q R ↦
      254804057739 / 10880 * Q ^ 8 + 11091469725 / 68 * Q ^ 5 * R ^ 2 + 5065635625 / 102 * Q ^ 2 * R ^ 4) :=
  tableRow_poly3 31 (by decide) (by norm_num) (by norm_num) (-7709321041217 / 510)
    (bernoulli_even_eq 32 (by norm_num) _ (by decide +kernel)) (by norm_num)
    (254804057739 / 10880) (11091469725 / 68) (5065635625 / 102) 8 0 5 2 2 4
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) _
    (by intro Q R; push_cast; ring)

/-- Row `s = 1`, `½ ζ(-1) = -1/24`. -/
private lemma half_zeta_neg_one : (1 / 2 : ℂ) * riemannZeta (-1) = -(1 / 24) := by
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  simp only [Nat.cast_one, pow_one] at h
  rw [h, bernoulli_two]
  push_cast
  norm_num

/-- **Ramanujan, No. 18, Table I, `s = 1`**. Proof: `ζ(-1) = -B₂/2 = -1/12`
(`riemannZeta_neg_nat_eq_bernoulli`) and the definition of `P`. -/
@[kb "ramanujan1927" "No. 18, § 5, Table I, (26), p. 141"]
theorem tableIRowOne : TableIRowOne := by
  intro x hx
  rw [half_zeta_neg_one, P]
  ring

/-- **Ramanujan, No. 18, Table I**. Proof: for each row, the Sturm bound for
level one (`ModularForm.sturm_bound_levelOne_nat`) on `c E_{s+1} - ∑ cᵢ E₄^{aᵢ} E₆^{bᵢ}`, the truncated
`q`-expansions `E₄ = 1 + 240 q + 2160 q² + …`, `E₆ = 1 - 504 q - 16632 q² + …`, and
`EisensteinSeries.q_expansion_bernoulli` with `riemannZeta_neg_nat_eq_bernoulli` (generic step
`tableRow_poly3`; Bernoulli numbers evaluated by `bernList`). -/
@[kb "ramanujan1927" "No. 18, § 5, Table I, (26), pp. 141–142"]
theorem ramanujanTableI : RamanujanTableI :=
  ⟨row3, row5, row7, row9, row11, row13, row15, row17, row19, row21, row23, row25, row27, row29, row31⟩

/-- `½ ζ(-31) = 7709321041217 / 32640`. -/
private lemma half_zeta_neg_31 :
    (1 / 2 : ℂ) * riemannZeta (-((31 : ℕ) : ℂ)) = 7709321041217 / 32640 := by
  have h := riemannZeta_neg_nat_eq_bernoulli 31
  have hb : bernoulli 32 = -7709321041217 / 510 :=
    bernoulli_even_eq 32 (by norm_num) _ (by decide +kernel)
  rw [h, show (31 : ℕ) + 1 = 32 from rfl, hb]
  push_cast
  norm_num

/-- **Ramanujan's weight-`32` formula** (No. 18, Table I, last row, as quoted in No. 30). Proof: row `s = 31` of `ramanujanTableI` multiplied by `32640`, with
`½ ζ(-31) = 7709321041217 / 32640`. -/
@[kb "ramanujan1927" "No. 18, § 5, Table I, (26), p. 142 (last row)"]
theorem weightThirtyTwoIdentity : WeightThirtyTwoIdentity := by
  intro x hx
  have h := row31 x hx
  rw [half_zeta_neg_31] at h
  simp only at h
  linear_combination 32640 * h

/-! ### Integrality of `1 / R` -/

/-- The integer series of `R`. -/
private def Rz : PowerSeries ℤ :=
  PowerSeries.mk fun m ↦ if m = 0 then 1 else -504 * (σ 5 m : ℤ)

/-- The list `[p₀, …, p_{n-1}]` from the recursion `p_n = 504 ∑_{m=1}^n σ₅(m) p_{n-m}` (kernel-friendly). -/
private def pList : ℕ → List ℤ
  | 0 => []
  | n + 1 =>
    pList n ++ [if n = 0 then 1 else
      ∑ k ∈ Finset.range n, 504 * (σ 5 (n - k) : ℤ) * (pList n).getD k 0]

/-- The coefficients `p_n` of `1/R`, by the recursion. -/
private def pf (n : ℕ) : ℤ := (pList (n + 1)).getD n 0

private lemma pList_length (n : ℕ) : (pList n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pList, ih]

private lemma pList_getD (n : ℕ) : ∀ k < n, (pList n).getD k 0 = pf k := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    have hlen := pList_length n
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [pList, List.getD_append _ _ _ _ (by omega), ih k hk]
    · rfl

private lemma pf_rec (n : ℕ) :
    pf n = if n = 0 then 1 else ∑ k ∈ Finset.range n, 504 * (σ 5 (n - k) : ℤ) * pf k := by
  have hlen := pList_length n
  have hpf : pf n = (pList (n + 1)).getD n 0 := rfl
  rw [hpf, pList, List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
  simp only [List.getD_cons_zero]
  split_ifs with h0
  · rfl
  · refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [pList_getD n j (Finset.mem_range.mp hj)]

private lemma pf_mul_Rz : PowerSeries.mk pf * Rz = 1 := by
  ext n
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b ↦ PowerSeries.coeff a (PowerSeries.mk pf) * PowerSeries.coeff b Rz) n]
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_one, Rz]
  rcases n with _ | n
  · simp [pf_rec 0]
  · rw [Finset.sum_range_succ, pf_rec (n + 1)]
    have : ∑ k ∈ Finset.range (n + 1), pf k * (if n + 1 - k = 0 then 1 else -504 * (σ 5 (n + 1 - k) : ℤ)) =
        -∑ k ∈ Finset.range (n + 1), 504 * (σ 5 (n + 1 - k) : ℤ) * pf k := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      have : n + 1 - k ≠ 0 := by have := Finset.mem_range.mp hk; omega
      simp only [this, ite_false]
      ring
    rw [this]
    simp

private lemma Rseries_inv_eq : Rseries⁻¹ = (PowerSeries.mk pf).map (Int.castRingHom ℚ) := by
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp [Rseries])]
  have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) pf_mul_Rz
  rw [map_mul, map_one] at h
  have hR : PowerSeries.map (Int.castRingHom ℚ) Rz = Rseries := by
    ext m
    simp only [Rz, Rseries, PowerSeries.coeff_map, PowerSeries.coeff_mk]
    split_ifs <;> simp
  rwa [hR] at h

private lemma pf_values : ∀ n : Fin 13,
    pf n = ramanujanRInvValues.get ⟨n, by simp [ramanujanRInvValues]⟩ := by
  decide +kernel

/-- **Hardy–Ramanujan, No. 37, § 6, (6.1)**. Proof: `Rseries` is the image of
the integer series `Rz` with constant term `1`; its inverse is the image of the integer series with
coefficients `pf n` given by the recursion `p_n = 504 ∑_{m=1}^n σ₅(m) p_{n-m}` (`pf_mul_Rz`), and the
first thirteen values are checked by kernel evaluation (`pf_values`). -/
@[kb "ramanujan1927" "No. 37, § 6, (6.1), p. 317"]
theorem ramanujanRInvCoeffs : RamanujanRInvCoeffs := by
  refine ⟨fun n ↦ ⟨pf n, ?_⟩, fun n ↦ ?_⟩
  · rw [Rseries_inv_eq]; simp
  · rw [Rseries_inv_eq, PowerSeries.coeff_map, PowerSeries.coeff_mk, pf_values n]
    simp

end ModularFormsKB.Historical.Ramanujan
