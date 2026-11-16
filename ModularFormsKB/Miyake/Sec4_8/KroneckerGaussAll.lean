import ModularFormsKB.Miyake.Sec4_8.KroneckerGaussPrime
import ModularFormsKB.Miyake.DirichletCharacters
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Factorization

/-!
# Miyake Lemma 4.8.1 (1) for every fundamental discriminant

Miyake, *Modular Forms* (Springer 1989), Lemma 4.8.1 (1), p. 183: for a fundamental discriminant
`d`, the Gauss sum `W(χ_d)` of the Kronecker character is `√d` if `d > 0` and `i √|d|` if `d < 0`
(the named statement `Wave6.KroneckerGaussSumStatement`; the case `d = 1` also holds, with `W = 1`).

Proof, by elementary means (no functional equations):

* Gauss sums of Dirichlet characters of coprime levels multiply up to a Kronecker symbol factor
  (`gaussSum_mul_of_coprime`, Miyake Lemma 3.1.2). For coprime fundamental discriminants `D`, `E`
  this gives `W(χ_{DE}) = (D/|E|) (E/|D|) W(χ_D) W(χ_E)` (`kroneckerGaussW_mul`).
* For the even prime discriminants `-4`, `8`, `-8` the sum is computed directly from the eighth root
  of unity `e^{2πi/8} = (1 + i) √2 / 2` (`kroneckerGaussW_neg_four`, `kroneckerGaussW_eight`, `kroneckerGaussW_neg_eight`); for the odd
  prime discriminants it is the Gauss sign result of `Sec4_8/KroneckerGaussPrime.lean`.
* Quadratic reciprocity for prime discriminants (`reciprocity_two`, `reciprocity_prod`) shows that the Kronecker
  symbol factor `(D/|E|)(E/|D|)` is `-1` exactly when `D` and `E` are both negative, which is the
  same sign that appears in `√D √E = ± √(DE)` (`discrSqrt_mul`).
* Every fundamental discriminant is a product of prime discriminants, at most one of them even;
  induction over this factorization gives the result (`kroneckerGaussW_prod`, `kroneckerGaussSumStatement`).
-/

open Complex TauCeti.Multiquadratic

noncomputable section

namespace ModularFormsKB.Miyake.Sec4_8

/-- The Gauss sum `W(χ_d)` of the Kronecker character of a fundamental discriminant. -/
def kroneckerGaussW (d : ℤ) (hd : Int.IsFundamentalDiscr d) : ℂ :=
  haveI : NeZero d.natAbs := hd.neZero_natAbs
  Miyake.gaussW (TauCeti.kroneckerChar ℂ d (hd.emod_four_eq_zero_or_one.imp id id) hd.ne_zero)

/-- Level transport: Gauss sums of characters of equal levels with equal values agree. -/
lemma gaussW_congr {m n : ℕ} [NeZero m] [NeZero n] (h : m = n) (χ : DirichletCharacter ℂ m)
    (ψ : DirichletCharacter ℂ n) (hv : ∀ a : ℤ, χ a = ψ a) : Miyake.gaussW χ = Miyake.gaussW ψ := by
  subst h
  have : χ = ψ := by
    refine MulChar.ext fun x => ?_
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective (x : ZMod m)
    rw [← hz]
    exact hv z
  rw [this]

/-- Values of the product of the two level-changed Kronecker characters. -/
lemma changeLevel_mul_kroneckerChar {D E : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hE : Int.IsFundamentalDiscr E) (hDE : Int.IsFundamentalDiscr (D * E)) (a : ℤ) :
    haveI := hD.neZero_natAbs
    haveI := hE.neZero_natAbs
    ((TauCeti.kroneckerChar ℂ D (hD.emod_four_eq_zero_or_one.imp id id) hD.ne_zero).changeLevel
        (dvd_mul_right D.natAbs E.natAbs) *
      (TauCeti.kroneckerChar ℂ E (hE.emod_four_eq_zero_or_one.imp id id) hE.ne_zero).changeLevel
        (dvd_mul_left E.natAbs D.natAbs)) (a : ZMod (D.natAbs * E.natAbs)) =
    TauCeti.kroneckerChar ℂ (D * E) (hDE.emod_four_eq_zero_or_one.imp id id) hDE.ne_zero
      (a : ZMod (D * E).natAbs) := by
  have := hD.neZero_natAbs
  have := hE.neZero_natAbs
  have := hDE.neZero_natAbs
  have hlev : D.natAbs * E.natAbs = (D * E).natAbs := (Int.natAbs_mul D E).symm
  by_cases hc : IsCoprime a ((D.natAbs * E.natAbs : ℕ) : ℤ)
  · have h1 : IsCoprime a (D.natAbs : ℤ) := hc.of_isCoprime_of_dvd_right (by simp)
    have h2 : IsCoprime a (E.natAbs : ℤ) := hc.of_isCoprime_of_dvd_right (by simp)
    rw [MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hc,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hc, TauCeti.kroneckerChar_intCast,
      TauCeti.kroneckerChar_intCast, TauCeti.kroneckerChar_intCast,
      TauCeti.kroneckerSym_mul_left hD.ne_zero hE.ne_zero]
    push_cast
    rfl
  · have hc' : ¬ IsCoprime a ((D * E).natAbs : ℤ) := by rwa [← hlev]
    rw [(DirichletCharacter.apply_eq_zero_iff _ a).mpr hc, (DirichletCharacter.apply_eq_zero_iff _ a).mpr hc']

/-- **Multiplicativity of Gauss sums of Kronecker characters** (Miyake Lemma 3.1.2): for coprime
fundamental discriminants `D`, `E`,
`W(χ_{DE}) = (D / |E|) (E / |D|) W(χ_D) W(χ_E)`. -/
lemma kroneckerGaussW_mul {D E : ℤ} (hD : Int.IsFundamentalDiscr D) (hE : Int.IsFundamentalDiscr E)
    (hDE : Int.IsFundamentalDiscr (D * E)) (hcop : IsCoprime D E) :
    kroneckerGaussW (D * E) hDE = (TauCeti.kroneckerSym D (E.natAbs : ℤ) : ℂ) *
      (TauCeti.kroneckerSym E (D.natAbs : ℤ) : ℂ) * kroneckerGaussW D hD * kroneckerGaussW E hE := by
  have := hD.neZero_natAbs
  have := hE.neZero_natAbs
  have := hDE.neZero_natAbs
  have hm : D.natAbs.Coprime E.natAbs := by
    rw [← Int.isCoprime_iff_nat_coprime]
    exact hcop
  have h := gaussSum_mul_of_coprime hm
    (TauCeti.kroneckerChar ℂ D (hD.emod_four_eq_zero_or_one.imp id id) hD.ne_zero)
    (TauCeti.kroneckerChar ℂ E (hE.emod_four_eq_zero_or_one.imp id id) hE.ne_zero)
  have h2 : Miyake.gaussW
      (TauCeti.kroneckerChar ℂ (D * E) (hDE.emod_four_eq_zero_or_one.imp id id) hDE.ne_zero) =
      Miyake.gaussW ((TauCeti.kroneckerChar ℂ D (hD.emod_four_eq_zero_or_one.imp id id) hD.ne_zero).changeLevel
        (dvd_mul_right D.natAbs E.natAbs) *
      (TauCeti.kroneckerChar ℂ E (hE.emod_four_eq_zero_or_one.imp id id) hE.ne_zero).changeLevel
        (dvd_mul_left E.natAbs D.natAbs)) :=
    (gaussW_congr (Int.natAbs_mul D E).symm _ _
      (fun a => changeLevel_mul_kroneckerChar hD hE hDE a)).symm
  unfold kroneckerGaussW
  rw [h2]
  unfold Miyake.gaussW
  rw [h]
  rw [TauCeti.kroneckerChar_natCast, TauCeti.kroneckerChar_natCast]

/-- The Gauss sum `W(χ_d)` as an explicit finite sum of the Kronecker symbol times roots of unity. -/
lemma kroneckerGaussW_eq_sum {d : ℤ} (hd : Int.IsFundamentalDiscr d) :
    kroneckerGaussW d hd = ∑ x ∈ Finset.range d.natAbs,
      (TauCeti.kroneckerSym d (x : ℤ) : ℂ) * cexp (2 * Real.pi * I * x / d.natAbs) := by
  have := hd.neZero_natAbs
  unfold kroneckerGaussW Miyake.gaussW gaussSum
  rw [← HalfIntegral.sum_range_eq_sum_zmod (fun x : ZMod d.natAbs ↦
    TauCeti.kroneckerChar ℂ d (hd.emod_four_eq_zero_or_one.imp id id) hd.ne_zero x *
      ZMod.stdAddChar x)]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [TauCeti.kroneckerChar_natCast, ← HalfIntegral.cexp_eq_stdAddChar]

/-- The primitive eighth root of unity `e^{2πi/8} = (1 + i) √2 / 2`. -/
lemma cexp_eighth : cexp (2 * Real.pi * I / 8) = (Real.sqrt 2 / 2 : ℝ) * (1 + I) := by
  have h : 2 * (Real.pi : ℂ) * I / 8 = (Real.pi / 4 : ℝ) * I := by push_cast; ring
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  ring

/-- Powers of the eighth root of unity: `e^{2πi k/8} = ζ^k`. -/
lemma cexp_div_eight (k : ℕ) :
    cexp (2 * Real.pi * I * k / 8) = cexp (2 * Real.pi * I / 8) ^ k := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- `ζ² = i` for `ζ = e^{2πi/8}`. -/
lemma cexp_eighth_sq : cexp (2 * Real.pi * I / 8) ^ 2 = I := by
  rw [cexp_eighth]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; simp
  push_cast
  linear_combination (I / 2) * h2 + (((Real.sqrt 2 : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq

/-- The target value of Miyake's Lemma 4.8.1 (1): `√d` for `d > 0` and `i √|d|` for `d < 0`. -/
def discrSqrt (d : ℤ) : ℂ :=
  if 0 < d then ((Real.sqrt d : ℝ) : ℂ) else I * ((Real.sqrt |(d : ℝ)| : ℝ) : ℂ)

/-- Powers of `ζ = e^{2πi/8}`, reduced using `ζ² = i`. -/
lemma cexp_eighth_pows :
    (cexp (2 * Real.pi * I / 8)) ^ 2 = I ∧ (cexp (2 * Real.pi * I / 8)) ^ 3 =
      cexp (2 * Real.pi * I / 8) * I ∧ (cexp (2 * Real.pi * I / 8)) ^ 4 = -1 ∧
    (cexp (2 * Real.pi * I / 8)) ^ 5 = -cexp (2 * Real.pi * I / 8) ∧
    (cexp (2 * Real.pi * I / 8)) ^ 6 = -I ∧
    (cexp (2 * Real.pi * I / 8)) ^ 7 = -(cexp (2 * Real.pi * I / 8) * I) := by
  have hz := cexp_eighth_sq
  generalize cexp (2 * Real.pi * I / 8) = z at hz ⊢
  have h4 : z ^ 4 = -1 := by
    rw [show z ^ 4 = (z ^ 2) ^ 2 by ring, hz, Complex.I_sq]
  refine ⟨hz, by rw [pow_succ, hz]; ring, h4, by rw [pow_succ, h4]; ring, ?_, ?_⟩
  · rw [show z ^ 6 = z ^ 4 * z ^ 2 by ring, h4, hz]; ring
  · rw [show z ^ 7 = z ^ 4 * z ^ 2 * z by ring, h4, hz]; ring

/-- `√4 = 2`. -/
lemma sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- `√8 = 2 √2`. -/
lemma sqrt_eight : Real.sqrt 8 = 2 * Real.sqrt 2 := by
  rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

/-- **Lemma 4.8.1 (1) for `d = -4`**: `W(χ_{-4}) = 2i`. -/
lemma kroneckerGaussW_neg_four (h : Int.IsFundamentalDiscr (-4)) : kroneckerGaussW (-4) h = discrSqrt (-4) := by
  obtain ⟨hz2, hz3, hz4, hz5, hz6, hz7⟩ := cexp_eighth_pows
  rw [kroneckerGaussW_eq_sum h]
  have hn : ((-4 : ℤ).natAbs) = 4 := rfl
  have hk : ∀ x : ℕ, TauCeti.kroneckerSym (-4) (x : ℤ) = ZMod.χ₄ (x : ZMod 4) := by
    intro x
    rw [← primeDiscriminantCharFun_eq_kroneckerSym isPrimeDiscriminant_neg_four,
      primeDiscriminantCharFun_neg_four]
    simp
  have e : ∀ k : ℕ, cexp (2 * Real.pi * I * k / ((4 : ℕ) : ℂ)) =
      cexp (2 * Real.pi * I / 8) ^ (2 * k) := by
    intro k
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have c0 : ZMod.χ₄ ((0 : ℕ) : ZMod 4) = 0 := by decide
  have c1 : ZMod.χ₄ ((1 : ℕ) : ZMod 4) = 1 := by decide
  have c2 : ZMod.χ₄ ((2 : ℕ) : ZMod 4) = 0 := by decide
  have c3 : ZMod.χ₄ ((3 : ℕ) : ZMod 4) = -1 := by decide
  rw [hn]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hk, e, c0, c1, c2, c3]
  unfold discrSqrt
  norm_num [sqrt_four]
  rw [hz2, hz6]
  ring

/-- **Lemma 4.8.1 (1) for `d = 8`**: `W(χ_8) = 2 √2`. -/
lemma kroneckerGaussW_eight (h : Int.IsFundamentalDiscr 8) : kroneckerGaussW 8 h = discrSqrt 8 := by
  obtain ⟨hz2, hz3, hz4, hz5, hz6, hz7⟩ := cexp_eighth_pows
  have hs := cexp_eighth
  rw [kroneckerGaussW_eq_sum h]
  have hn : ((8 : ℤ).natAbs) = 8 := rfl
  have hk : ∀ x : ℕ, TauCeti.kroneckerSym 8 (x : ℤ) = ZMod.χ₈ (x : ZMod 8) := by
    intro x
    rw [← primeDiscriminantCharFun_eq_kroneckerSym isPrimeDiscriminant_eight,
      primeDiscriminantCharFun_eight]
    simp
  have c0 : ZMod.χ₈ ((0 : ℕ) : ZMod 8) = 0 := by decide
  have c1 : ZMod.χ₈ ((1 : ℕ) : ZMod 8) = 1 := by decide
  have c2 : ZMod.χ₈ ((2 : ℕ) : ZMod 8) = 0 := by decide
  have c3 : ZMod.χ₈ ((3 : ℕ) : ZMod 8) = -1 := by decide
  have c4 : ZMod.χ₈ ((4 : ℕ) : ZMod 8) = 0 := by decide
  have c5 : ZMod.χ₈ ((5 : ℕ) : ZMod 8) = -1 := by decide
  have c6 : ZMod.χ₈ ((6 : ℕ) : ZMod 8) = 0 := by decide
  have c7 : ZMod.χ₈ ((7 : ℕ) : ZMod 8) = 1 := by decide
  have e : ∀ k : ℕ, cexp (2 * Real.pi * I * k / ((8 : ℕ) : ℂ)) =
      cexp (2 * Real.pi * I / 8) ^ k := by
    intro k
    rw [Nat.cast_ofNat]
    exact cexp_div_eight k
  rw [hn]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hk, e, c0, c1, c2, c3, c4, c5, c6, c7]
  unfold discrSqrt
  norm_num [sqrt_eight]
  rw [hz3, hz5, hz7, hs]
  push_cast
  linear_combination (-((Real.sqrt 2 : ℝ) : ℂ)) * Complex.I_sq

/-- **Lemma 4.8.1 (1) for `d = -8`**: `W(χ_{-8}) = 2 √2 i`. -/
lemma kroneckerGaussW_neg_eight (h : Int.IsFundamentalDiscr (-8)) : kroneckerGaussW (-8) h = discrSqrt (-8) := by
  obtain ⟨hz2, hz3, hz4, hz5, hz6, hz7⟩ := cexp_eighth_pows
  have hs := cexp_eighth
  rw [kroneckerGaussW_eq_sum h]
  have hn : ((-8 : ℤ).natAbs) = 8 := rfl
  have hk : ∀ x : ℕ, TauCeti.kroneckerSym (-8) (x : ℤ) = ZMod.χ₈' (x : ZMod 8) := by
    intro x
    rw [← primeDiscriminantCharFun_eq_kroneckerSym isPrimeDiscriminant_neg_eight,
      primeDiscriminantCharFun_neg_eight]
    simp
  have c0 : ZMod.χ₈' ((0 : ℕ) : ZMod 8) = 0 := by decide
  have c1 : ZMod.χ₈' ((1 : ℕ) : ZMod 8) = 1 := by decide
  have c2 : ZMod.χ₈' ((2 : ℕ) : ZMod 8) = 0 := by decide
  have c3 : ZMod.χ₈' ((3 : ℕ) : ZMod 8) = 1 := by decide
  have c4 : ZMod.χ₈' ((4 : ℕ) : ZMod 8) = 0 := by decide
  have c5 : ZMod.χ₈' ((5 : ℕ) : ZMod 8) = -1 := by decide
  have c6 : ZMod.χ₈' ((6 : ℕ) : ZMod 8) = 0 := by decide
  have c7 : ZMod.χ₈' ((7 : ℕ) : ZMod 8) = -1 := by decide
  have e : ∀ k : ℕ, cexp (2 * Real.pi * I * k / ((8 : ℕ) : ℂ)) =
      cexp (2 * Real.pi * I / 8) ^ k := by
    intro k
    rw [Nat.cast_ofNat]
    exact cexp_div_eight k
  rw [hn]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hk, e, c0, c1, c2, c3, c4, c5, c6, c7]
  unfold discrSqrt
  norm_num [sqrt_eight]
  rw [hz3, hz5, hz7, hs]
  push_cast
  linear_combination ((Real.sqrt 2 : ℝ) : ℂ) * Complex.I_sq

/-- The sign factor `-1` if both `a` and `b` are negative, and `1` otherwise. -/
def bothNegSign (a b : ℤ) : ℤ := if a < 0 ∧ b < 0 then -1 else 1

/-- The sign factor is symmetric. -/
lemma bothNegSign_comm (a b : ℤ) : bothNegSign a b = bothNegSign b a := by
  unfold bothNegSign
  simp only [and_comm]

/-- The sign factor is multiplicative in the second variable, over nonzero factors. -/
lemma bothNegSign_mul_right {a x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) : bothNegSign a (x * y) = bothNegSign a x * bothNegSign a y :=
  Int.ite_and_mul_lt_zero hx hy

/-- Product of the target values: `discrSqrt a * discrSqrt b = ± discrSqrt (a b)`, with the sign
`-1` exactly when both `a` and `b` are negative. -/
lemma discrSqrt_mul {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    discrSqrt a * discrSqrt b = (bothNegSign a b : ℂ) * discrSqrt (a * b) := by
  have hxy : Real.sqrt |((a * b : ℤ) : ℝ)| = Real.sqrt |(a : ℝ)| * Real.sqrt |(b : ℝ)| := by
    rw [← Real.sqrt_mul (abs_nonneg _), ← abs_mul]
    push_cast
    rfl
  unfold discrSqrt bothNegSign
  rcases ha.lt_or_gt with ha' | ha' <;> rcases hb.lt_or_gt with hb' | hb'
  · have hab : 0 < a * b := mul_pos_of_neg_of_neg ha' hb'
    have h1 : ¬ 0 < a := not_lt.mpr ha'.le
    have h2 : ¬ 0 < b := not_lt.mpr hb'.le
    have h4 : Real.sqrt ((a * b : ℤ) : ℝ) = Real.sqrt |(a : ℝ)| * Real.sqrt |(b : ℝ)| := by
      rw [← hxy, abs_of_pos (by exact_mod_cast hab)]
    simp only [h1, h2, hab, ha', hb', and_self, ↓reduceIte, h4]
    push_cast
    linear_combination (((Real.sqrt |(a : ℝ)| : ℝ) : ℂ) * (Real.sqrt |(b : ℝ)| : ℝ)) * Complex.I_sq
  · have hab : a * b < 0 := mul_neg_of_neg_of_pos ha' hb'
    have h1 : ¬ 0 < a := not_lt.mpr ha'.le
    have h2 : ¬ 0 < a * b := not_lt.mpr hab.le
    have h4 : Real.sqrt (b : ℝ) = Real.sqrt |(b : ℝ)| := by
      rw [abs_of_pos (by exact_mod_cast hb')]
    simp only [h1, h2, hb', hb'.not_gt, ha', and_false, ↓reduceIte, h4, hxy]
    push_cast
    ring
  · have hab : a * b < 0 := mul_neg_of_pos_of_neg ha' hb'
    have h1 : ¬ 0 < b := not_lt.mpr hb'.le
    have h2 : ¬ 0 < a * b := not_lt.mpr hab.le
    have h4 : Real.sqrt (a : ℝ) = Real.sqrt |(a : ℝ)| := by
      rw [abs_of_pos (by exact_mod_cast ha')]
    simp only [h1, h2, ha', ha'.not_gt, hb', false_and, ↓reduceIte, h4, hxy]
    push_cast
    ring
  · have hab : 0 < a * b := mul_pos ha' hb'
    have h4 : Real.sqrt (a : ℝ) = Real.sqrt |(a : ℝ)| := by
      rw [abs_of_pos (by exact_mod_cast ha')]
    have h5 : Real.sqrt (b : ℝ) = Real.sqrt |(b : ℝ)| := by
      rw [abs_of_pos (by exact_mod_cast hb')]
    have h6 : Real.sqrt ((a * b : ℤ) : ℝ) = Real.sqrt |(a : ℝ)| * Real.sqrt |(b : ℝ)| := by
      rw [← hxy, abs_of_pos (by exact_mod_cast hab)]
    simp only [ha', hb', hab, ha'.not_gt, ↓reduceIte, h4, h5, h6, false_and]
    push_cast
    ring

/-- **Lemma 4.8.1 (1) for every prime discriminant**: `W(χ_P) = discrSqrt P`. -/
lemma kroneckerGaussW_primeDiscriminant {P : ℤ} (hP : IsPrimeDiscriminant P) (h : Int.IsFundamentalDiscr P) :
    kroneckerGaussW P h = discrSqrt P := by
  rcases isPrimeDiscriminant_iff.mp hP with (rfl | rfl | rfl) | ⟨p, hp, hodd, rfl⟩
  · exact kroneckerGaussW_neg_four h
  · exact kroneckerGaussW_eight h
  · exact kroneckerGaussW_neg_eight h
  · exact gaussW_kroneckerChar_oddPrimeDiscriminant hp hodd _ rfl h

/-- `(D / 4) = 1` for odd `D`. -/
lemma kroneckerSym_four_right {D : ℤ} (hD : D % 2 = 1) : TauCeti.kroneckerSym D 4 = 1 := by
  have h : (4 : ℤ) = 2 ^ 2 := by norm_num
  rw [h, TauCeti.kroneckerSym_pow_right, TauCeti.kroneckerSym_two_right,
    ZMod.χ₈_int_eq_if_mod_eight]
  split_ifs <;> omega

/-- `(D / 8) = χ₈(D)` for odd `D`, as `χ₈(D)` is `±1`. -/
lemma kroneckerSym_eight_right {D : ℤ} (hD : D % 2 = 1) :
    TauCeti.kroneckerSym D 8 = ZMod.χ₈ (D : ZMod 8) := by
  have h : (8 : ℤ) = 2 ^ 3 := by norm_num
  rw [h, TauCeti.kroneckerSym_pow_right, TauCeti.kroneckerSym_two_right]
  have := ZMod.χ₈_int_eq_if_mod_eight D
  split_ifs at this <;> rw [this] <;> omega

/-- Reciprocity between an even prime discriminant and an odd one. -/
lemma reciprocity_even_odd {P : ℤ} (hP : IsEvenPrimeDiscriminant P) {q : ℕ} (hodd : Odd q) :
    TauCeti.kroneckerSym P (oddPrimeDiscriminant q).natAbs *
      TauCeti.kroneckerSym (oddPrimeDiscriminant q) P.natAbs = bothNegSign P (oddPrimeDiscriminant q) := by
  rw [oddPrimeDiscriminant_natAbs, ← primeDiscriminantCharFun_eq_kroneckerSym hP.isPrimeDiscriminant]
  have hq8 : q % 2 = 1 := Nat.odd_iff.mp hodd
  have hmod : (q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7) := by omega
  have hdef : (q % 4 = 1 ∧ oddPrimeDiscriminant q = q) ∨ (q % 4 ≠ 1 ∧ oddPrimeDiscriminant q = -q) := by
    rw [oddPrimeDiscriminant_def]; split_ifs with h <;> simp [h]
  generalize oddPrimeDiscriminant q = D at hdef ⊢
  have hD : D % 2 = 1 := by omega
  unfold bothNegSign
  rcases hP with rfl | rfl | rfl
  · rw [primeDiscriminantCharFun_neg_four, show (-4 : ℤ).natAbs = 4 from rfl, Nat.cast_ofNat,
      kroneckerSym_four_right hD, ZMod.χ₄_int_eq_if_mod_four]
    push_cast
    split_ifs <;> simp only [true_and] at * <;> omega
  · rw [primeDiscriminantCharFun_eight, show (8 : ℤ).natAbs = 8 from rfl, Nat.cast_ofNat,
      kroneckerSym_eight_right hD, ZMod.χ₈_int_eq_if_mod_eight, ZMod.χ₈_int_eq_if_mod_eight]
    push_cast
    split_ifs <;> simp only [false_and] at * <;> omega
  · rw [primeDiscriminantCharFun_neg_eight, show (-8 : ℤ).natAbs = 8 from rfl, Nat.cast_ofNat,
      kroneckerSym_eight_right hD, ZMod.χ₈'_int_eq_if_mod_eight, ZMod.χ₈_int_eq_if_mod_eight]
    push_cast
    split_ifs <;> simp only [true_and] at * <;> omega

/-- Reciprocity between two distinct odd prime discriminants. -/
lemma reciprocity_odd_odd {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpo : Odd p) (hqo : Odd q)
    (hne : p ≠ q) :
    TauCeti.kroneckerSym (oddPrimeDiscriminant p) (oddPrimeDiscriminant q).natAbs *
      TauCeti.kroneckerSym (oddPrimeDiscriminant q) (oddPrimeDiscriminant p).natAbs =
      bothNegSign (oddPrimeDiscriminant p) (oddPrimeDiscriminant q) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have hp2 : p ≠ 2 := fun h => by subst h; exact absurd hpo (by decide)
  have hq2 : q ≠ 2 := fun h => by subst h; exact absurd hqo (by decide)
  rw [oddPrimeDiscriminant_natAbs, oddPrimeDiscriminant_natAbs,
    TauCeti.kroneckerSym_eq_legendreSym _ q hq2, TauCeti.kroneckerSym_eq_legendreSym _ p hp2,
    legendreSym_oddPrimeDiscriminant_eq_legendreSym hp2 hq2,
    legendreSym_oddPrimeDiscriminant_eq_legendreSym hq2 hp2]
  have hnz : ((q : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
  have hsq := legendreSym.sq_one p hnz
  have hp4 := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hpo)
  have hq4 := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hqo)
  unfold bothNegSign
  rw [Ne.eq_def] at hne
  rcases hp4 with hp4 | hp4
  · have h1 := legendreSym.quadratic_reciprocity_one_mod_four hp4 hq2
    have h2 : ¬ (oddPrimeDiscriminant p < 0) := by
      rw [oddPrimeDiscriminant_neg_iff hpo]; omega
    rw [ite_eq_right_iff.mpr (fun h => absurd h.1 h2), h1]
    nlinarith
  · rcases hq4 with hq4 | hq4
    · have h1 := legendreSym.quadratic_reciprocity_one_mod_four hq4 hp2
      have h2 : ¬ (oddPrimeDiscriminant q < 0) := by
        rw [oddPrimeDiscriminant_neg_iff hqo]; omega
      rw [ite_eq_right_iff.mpr (fun h => absurd h.2 h2), ← h1]
      nlinarith
    · have h1 := legendreSym.quadratic_reciprocity_three_mod_four hp4 hq4
      rw [ite_eq_left_iff.mpr (fun h => absurd ⟨(oddPrimeDiscriminant_neg_iff hpo).mpr hp4,
        (oddPrimeDiscriminant_neg_iff hqo).mpr hq4⟩ h), h1]
      nlinarith

/-- Reciprocity between two coprime prime discriminants. -/
lemma reciprocity_two {P Q : ℤ} (hP : IsPrimeDiscriminant P) (hQ : IsPrimeDiscriminant Q)
    (hcop : IsCoprime P Q) :
    TauCeti.kroneckerSym P Q.natAbs * TauCeti.kroneckerSym Q P.natAbs = bothNegSign P Q := by
  rcases isPrimeDiscriminant_iff.mp hP with hPe | ⟨p, hp, hpo, rfl⟩
  · rcases isPrimeDiscriminant_iff.mp hQ with hQe | ⟨q, hq, hqo, rfl⟩
    · exfalso
      have := Int.isCoprime_iff_gcd_eq_one.mp hcop
      rcases hPe with rfl | rfl | rfl <;> rcases hQe with rfl | rfl | rfl <;>
        exact absurd this (by decide)
    · exact reciprocity_even_odd hPe hqo
  · rcases isPrimeDiscriminant_iff.mp hQ with hQe | ⟨q, hq, hqo, rfl⟩
    · rw [mul_comm, bothNegSign_comm]
      exact reciprocity_even_odd hQe hpo
    · refine reciprocity_odd_odd hp hq hpo hqo ?_
      rintro rfl
      rw [Int.isCoprime_iff_nat_coprime, oddPrimeDiscriminant_natAbs, Nat.coprime_self] at hcop
      exact hp.one_lt.ne' hcop

/-- Reciprocity between a prime discriminant and a product of prime discriminants coprime to it. -/
lemma reciprocity_prod {P : ℤ} (hP : IsPrimeDiscriminant P) (s : Finset ℤ)
    (hs : ∀ Q ∈ s, IsPrimeDiscriminant Q) (hcop : ∀ Q ∈ s, IsCoprime P Q) :
    TauCeti.kroneckerSym P (∏ Q ∈ s, Q).natAbs * TauCeti.kroneckerSym (∏ Q ∈ s, Q) P.natAbs =
      bothNegSign P (∏ Q ∈ s, Q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bothNegSign]
  | insert Q s hQs ih =>
    have hQ := hs Q (Finset.mem_insert_self Q s)
    have hs' : ∀ R ∈ s, IsPrimeDiscriminant R := fun R hR => hs R (Finset.mem_insert_of_mem hR)
    have hcop' : ∀ R ∈ s, IsCoprime P R := fun R hR => hcop R (Finset.mem_insert_of_mem hR)
    have hQ0 : Q ≠ 0 := hQ.isFundamentalDiscr.ne_zero
    have hE0 : ∏ R ∈ s, R ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun R hR => (hs' R hR).isFundamentalDiscr.ne_zero
    rw [Finset.prod_insert hQs, Int.natAbs_mul, Nat.cast_mul,
      TauCeti.kroneckerSym_mul_right P (by exact_mod_cast Int.natAbs_ne_zero.mpr hQ0)
        (by exact_mod_cast Int.natAbs_ne_zero.mpr hE0),
      TauCeti.kroneckerSym_mul_left hQ0 hE0, bothNegSign_mul_right hQ0 hE0,
      mul_mul_mul_comm, reciprocity_two hP hQ (hcop Q (Finset.mem_insert_self Q s)), ih hs' hcop']

/-- `kroneckerGaussW` depends only on the value of the discriminant. -/
lemma kroneckerGaussW_congr {d d' : ℤ} (e : d = d') (h : Int.IsFundamentalDiscr d) (h' : Int.IsFundamentalDiscr d') :
    kroneckerGaussW d h = kroneckerGaussW d' h' := by
  subst e
  rfl

/-- **Lemma 4.8.1 (1) for `d = 1`**: the character of level `1` has `W = 1 = √1`. -/
lemma kroneckerGaussW_one (h : Int.IsFundamentalDiscr 1) : kroneckerGaussW 1 h = discrSqrt 1 := by
  rw [kroneckerGaussW_eq_sum h]
  simp [discrSqrt]

/-- The sign factor squares to `1`. -/
lemma bothNegSign_mul_self (a b : ℤ) : bothNegSign a b * bothNegSign a b = 1 := by
  unfold bothNegSign
  split_ifs <;> norm_num

/-- **Lemma 4.8.1 (1) for a product of prime discriminants**, at most one of them even. -/
lemma kroneckerGaussW_prod (s : Finset ℤ) (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ Q ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q)
    (h : Int.IsFundamentalDiscr (∏ P ∈ s, P)) : kroneckerGaussW (∏ P ∈ s, P) h = discrSqrt (∏ P ∈ s, P) := by
  classical
  have h1 : Int.IsFundamentalDiscr 1 :=
    Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨by norm_num, squarefree_one⟩)
  induction s using Finset.induction_on with
  | empty =>
    rw [kroneckerGaussW_congr Finset.prod_empty h h1, kroneckerGaussW_one, Finset.prod_empty]
  | insert P s hPs ih =>
    have hP := hs P (Finset.mem_insert_self P s)
    have hs' : ∀ R ∈ s, IsPrimeDiscriminant R := fun R hR => hs R (Finset.mem_insert_of_mem hR)
    have heven' : ∀ R ∈ s, ∀ R' ∈ s, IsEvenPrimeDiscriminant R → IsEvenPrimeDiscriminant R' →
        R = R' := fun R hR R' hR' => heven R (Finset.mem_insert_of_mem hR) R'
          (Finset.mem_insert_of_mem hR')
    have hE : Int.IsFundamentalDiscr (∏ R ∈ s, R) :=
      isFundamentalDiscr_prod (s := s) (D := id) hs' (fun _ _ _ _ h => h) heven'
    have hcop : IsCoprime P (∏ R ∈ s, R) := by
      refine IsCoprime.prod_right fun Q hQ => ?_
      refine isCoprime_primeDiscriminant_of_ne_of_not_both_even hP (hs' Q hQ) ?_ ?_
      · rintro rfl
        exact hPs hQ
      · rintro ⟨h1, h2⟩
        exact hPs (heven P (Finset.mem_insert_self P s) Q (Finset.mem_insert_of_mem hQ) h1 h2 ▸ hQ)
    have hPE : Int.IsFundamentalDiscr (P * ∏ R ∈ s, R) := by
      rwa [Finset.prod_insert hPs] at h
    rw [kroneckerGaussW_congr (Finset.prod_insert hPs) h hPE, Finset.prod_insert hPs,
      kroneckerGaussW_mul hP.isFundamentalDiscr hE hPE hcop, kroneckerGaussW_primeDiscriminant hP hP.isFundamentalDiscr,
      ih hs' heven' hE]
    have hrec : (TauCeti.kroneckerSym P (∏ R ∈ s, R).natAbs : ℂ) *
        (TauCeti.kroneckerSym (∏ R ∈ s, R) P.natAbs : ℂ) = (bothNegSign P (∏ R ∈ s, R) : ℂ) := by
      exact_mod_cast reciprocity_prod hP s hs' (fun Q hQ => by
        refine isCoprime_primeDiscriminant_of_ne_of_not_both_even hP (hs' Q hQ) ?_ ?_
        · rintro rfl
          exact hPs hQ
        · rintro ⟨h1, h2⟩
          exact hPs (heven P (Finset.mem_insert_self P s) Q (Finset.mem_insert_of_mem hQ) h1 h2 ▸ hQ))
    have hP0 : P ≠ 0 := hP.isFundamentalDiscr.ne_zero
    have hE0 : ∏ R ∈ s, R ≠ 0 := hE.ne_zero
    have hm := discrSqrt_mul hP0 hE0
    have hss : (bothNegSign P (∏ R ∈ s, R) : ℂ) * (bothNegSign P (∏ R ∈ s, R) : ℂ) = 1 := by
      exact_mod_cast bothNegSign_mul_self P (∏ R ∈ s, R)
    calc _ = ((TauCeti.kroneckerSym P (∏ R ∈ s, R).natAbs : ℂ) *
        (TauCeti.kroneckerSym (∏ R ∈ s, R) P.natAbs : ℂ)) * (discrSqrt P * discrSqrt (∏ R ∈ s, R)) := by
          ring
      _ = _ := by
          rw [hrec, hm, ← mul_assoc, hss, one_mul]

/-- **Miyake, Lemma 4.8.1 (1)**: for every fundamental discriminant `d` (the case `d = 1` being
trivial), the Gauss sum of the Kronecker character `χ_d` is `√d` if `d > 0` and `i √|d|` if
`d < 0`. -/
@[kb "miyake1989" "Lemma 4.8.1 (1), p. 183"]
theorem kroneckerGaussSumStatement : Wave6.KroneckerGaussSumStatement := by
  intro d hd _
  obtain ⟨s, hs, hev, hprod⟩ := Int.IsFundamentalDiscr.exists_finset_primeDiscriminant hd
  subst hprod
  exact kroneckerGaussW_prod s hs hev hd

end ModularFormsKB.Miyake.Sec4_8
