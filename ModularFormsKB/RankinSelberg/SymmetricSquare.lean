/-
# The Euler product of $L(f\times\bar g,s)$ and the symmetric square at level one

The second half of headline **H2**.

**The local identity.** If $A_0 = 1$, $A_1 = a$, $A_{r+2} = aA_{r+1} - qA_r$ and $B$ likewise with $b$ (the Hecke
recursion at a prime, $q = p^{k-1}$), then
$$\Big(\sum_r A_rB_rX^r\Big)\,D(X) = 1 - q^2X^2,\qquad
D(X) = 1 - abX + (a^2q + b^2q - 2q^2)X^2 - abq^2X^3 + q^4X^4$$
(`tsum_mul_rsLocalPoly`), and $D(X) = \prod_{i,j}(1 - \alpha_i\beta_jX)$ for $\alpha_1+\alpha_2 = a$, $\alpha_1\alpha_2 = q$,
$\beta_1+\beta_2 = b$, $\beta_1\beta_2 = q$ (`rsLocalPoly_eq_prod`). With Mathlib's Euler product this gives, for normalized
Hecke eigenforms $f, g$ of level one and $\operatorname{Re}s > 2$ (`hasProd_rankinSelbergL`):
$$L(f\times\bar g,s) = \prod_p D_p\big(p^{-(s+k-1)}\big)^{-1}.$$

**The symmetric square.** For $f = g$ with real coefficients, $D(X) = (1-qX)\,S_p(X)$ with
$S_p(X) = (1-qX)\big(1-(a_p^2-2q)X+q^2X^2\big) = (1-\alpha^2X)(1-\alpha\beta X)(1-\beta^2X)$, so with
$L(\mathrm{Sym}^2f,w) = \prod_pS_p(p^{-w})^{-1}$ (`symSqL`; Shimura's normalization, centre $w = k - \tfrac12$):
$$L(f\times\bar f,s) = \zeta(s)\,L(\mathrm{Sym}^2f,s+k-1)\qquad(\operatorname{Re}s > 2).$$
The quotient of the continued Rankin–Selberg function by $\zeta$ continues $L(\mathrm{Sym}^2f,\cdot)$ to
$\operatorname{Re}w \ge k$ (`symSqLc`), and the residue of `RankinSelberg/LevelOne.lean` gives
$$\langle f, f\rangle = c_k\,L(\mathrm{Sym}^2f,k),\qquad c_k = \frac{2\,\Gamma(k)}{\pi\,(4\pi)^k} = \frac{(k-1)!}{2^{2k-1}\pi^{k+1}}$$
(`petersson_eq_symSq`; Rankin 1939 `rankin1939`, Zagier 1977 `zagier1977` [unverified] for the constant). The entire
continuation of $L(\mathrm{Sym}^2f,\cdot)$ (Shimura 1975 `shimura1975`) is only stated (`SymmetricSquareHolomorphy`).
-/
import ModularFormsKB.RankinSelberg.LevelOne
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing

open MeasureTheory Set Filter Topology Complex Asymptotics MatrixGroups
open scoped UpperHalfPlane Real ComplexConjugate

noncomputable section

namespace ModularFormsKB.RankinSelberg

open ModularFormsKB.HalfIntegral UpperHalfPlane

/-! ### Normalized Hecke eigenforms of level one, through their coefficients -/

/-- **The coefficients of a normalized Hecke eigenform of weight $k$ and level one**: $a_1 = 1$, multiplicativity on
coprime indices, the prime-power recursion $a_{p^{r+2}} = a_pa_{p^{r+1}} - p^{k-1}a_{p^r}$, and real coefficients
(the Hecke operators of level one are self-adjoint). `isNormalizedEigenform_newform` checks this for Tau Ceti's
level-one newforms. -/
structure IsNormalizedEigenform (k : ℕ) (a : ℕ → ℂ) : Prop where
  one : a 1 = 1
  mul : ∀ {m n : ℕ}, Nat.Coprime m n → a (m * n) = a m * a n
  prime_pow : ∀ p : ℕ, p.Prime → ∀ r : ℕ, a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - (p : ℂ) ^ (k - 1) * a (p ^ r)
  real : ∀ n, conj (a n) = a n

/-! ### Row 16: the local identity -/

/-- $D(X) = 1 - abX + (a^2q + b^2q - 2q^2)X^2 - abq^2X^3 + q^4X^4$. -/
def rsLocalPoly (a b q X : ℂ) : ℂ :=
  1 - a * b * X + (a ^ 2 * q + b ^ 2 * q - 2 * q ^ 2) * X ^ 2 - a * b * q ^ 2 * X ^ 3 + q ^ 4 * X ^ 4

/-- **The Satake form** $D(X) = \prod_{i,j}(1-\alpha_i\beta_jX)$. -/
theorem rsLocalPoly_eq_prod {α₁ α₂ β₁ β₂ q X : ℂ} (hα : α₁ * α₂ = q) (hβ : β₁ * β₂ = q) :
    rsLocalPoly (α₁ + α₂) (β₁ + β₂) q X =
      (1 - α₁ * β₁ * X) * (1 - α₁ * β₂ * X) * (1 - α₂ * β₁ * X) * (1 - α₂ * β₂ * X) := by
  subst hα
  unfold rsLocalPoly
  linear_combination (-(((α₁ + α₂) ^ 2 - 2 * (α₁ * α₂)) * X ^ 2 -
    (α₁ + α₂) * (β₁ + β₂) * (α₁ * α₂) * X ^ 3 +
    (α₁ * α₂) ^ 2 * (α₁ * α₂ + β₁ * β₂) * X ^ 4)) * hβ

/-- A sequence obeying the Hecke recursion at a prime: $A_0 = 1$, $A_1 = a$, $A_{r+2} = aA_{r+1} - qA_r$. -/
structure IsHeckeSeq (a q : ℂ) (A : ℕ → ℂ) : Prop where
  zero : A 0 = 1
  one : A 1 = a
  succ : ∀ r, A (r + 2) = a * A (r + 1) - q * A r

/-- **The local identity** $\big(\sum_rA_rB_rx^r\big)D(x) = 1 - q^2x^2$ for absolutely convergent $\sum A_rB_rx^r$. -/
theorem tsum_mul_rsLocalPoly {a b q x : ℂ} {A B : ℕ → ℂ} (hA : IsHeckeSeq a q A) (hB : IsHeckeSeq b q B)
    (hs : Summable fun r ↦ ‖A r * B r * x ^ r‖) :
    (∑' r, A r * B r * x ^ r) * rsLocalPoly a b q x = 1 - q ^ 2 * x ^ 2 := by
  have hT : Summable fun r ↦ A r * B r * x ^ r := hs.of_norm
  have hA2 : A 2 = a ^ 2 - q := by
    have h : A 2 = a * A 1 - q * A 0 := hA.succ 0
    rw [h, hA.one, hA.zero]; ring
  have hB2 : B 2 = b ^ 2 - q := by
    have h : B 2 = b * B 1 - q * B 0 := hB.succ 0
    rw [h, hB.one, hB.zero]; ring
  have hA3 : A 3 = a ^ 3 - 2 * a * q := by
    have h : A 3 = a * A 2 - q * A 1 := hA.succ 1
    rw [h, hA2, hA.one]; ring
  have hB3 : B 3 = b ^ 3 - 2 * b * q := by
    have h : B 3 = b * B 2 - q * B 1 := hB.succ 1
    rw [h, hB2, hB.one]; ring
  have hrec : ∀ r, A (r + 4) * B (r + 4) - a * b * (A (r + 3) * B (r + 3)) +
      (a ^ 2 * q + b ^ 2 * q - 2 * q ^ 2) * (A (r + 2) * B (r + 2)) -
      a * b * q ^ 2 * (A (r + 1) * B (r + 1)) + q ^ 4 * (A r * B r) = 0 := by
    intro r
    have hA4 : A (r + 4) = a * A (r + 3) - q * A (r + 2) := hA.succ (r + 2)
    have hA3' : A (r + 3) = a * A (r + 2) - q * A (r + 1) := hA.succ (r + 1)
    have hA2' : A (r + 2) = a * A (r + 1) - q * A r := hA.succ r
    have hB4 : B (r + 4) = b * B (r + 3) - q * B (r + 2) := hB.succ (r + 2)
    have hB3' : B (r + 3) = b * B (r + 2) - q * B (r + 1) := hB.succ (r + 1)
    have hB2' : B (r + 2) = b * B (r + 1) - q * B r := hB.succ r
    rw [hA4, hB4, hA3', hB3', hA2', hB2']
    ring
  set T : ℕ → ℂ := fun r ↦ A r * B r * x ^ r with hTd
  have hTa : ∀ r, T r = A r * B r * x ^ r := fun r ↦ rfl
  have hT0 : T 0 = 1 := by simp [hTa, hA.zero, hB.zero]
  have hT1 : T 1 = a * b * x := by simp [hTa, hA.one, hB.one]
  have hT2 : T 2 = (a ^ 2 - q) * (b ^ 2 - q) * x ^ 2 := by rw [hTa, hA2, hB2]
  have hT3 : T 3 = (a ^ 3 - 2 * a * q) * (b ^ 3 - 2 * b * q) * x ^ 3 := by rw [hTa, hA3, hB3]
  have hU : ∀ m, Summable fun r ↦ T (r + m) := fun m ↦ (summable_nat_add_iff m).2 hT
  have h4 := hT.sum_add_tsum_nat_add 4
  have h3 := hT.sum_add_tsum_nat_add 3
  have h2 := hT.sum_add_tsum_nat_add 2
  have h1 := hT.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hT0, hT1, hT2, hT3] at h4 h3 h2 h1
  have hz : HasSum (fun r ↦ T (r + 4) - a * b * x * T (r + 3) +
      (a ^ 2 * q + b ^ 2 * q - 2 * q ^ 2) * x ^ 2 * T (r + 2) -
      a * b * q ^ 2 * x ^ 3 * T (r + 1) + q ^ 4 * x ^ 4 * T r) 0 := by
    have : ∀ r, T (r + 4) - a * b * x * T (r + 3) +
      (a ^ 2 * q + b ^ 2 * q - 2 * q ^ 2) * x ^ 2 * T (r + 2) -
      a * b * q ^ 2 * x ^ 3 * T (r + 1) + q ^ 4 * x ^ 4 * T r = 0 := by
      intro r
      simp only [hTa]
      linear_combination x ^ (r + 4) * hrec r
    simp only [this]
    exact hasSum_zero
  have hsum : HasSum (fun r ↦ T (r + 4) - a * b * x * T (r + 3) +
      (a ^ 2 * q + b ^ 2 * q - 2 * q ^ 2) * x ^ 2 * T (r + 2) -
      a * b * q ^ 2 * x ^ 3 * T (r + 1) + q ^ 4 * x ^ 4 * T r)
      ((∑' r, T (r + 4)) - a * b * x * (∑' r, T (r + 3)) +
      (a ^ 2 * q + b ^ 2 * q - 2 * q ^ 2) * x ^ 2 * (∑' r, T (r + 2)) -
      a * b * q ^ 2 * x ^ 3 * (∑' r, T (r + 1)) + q ^ 4 * x ^ 4 * (∑' r, T r)) :=
    ((((hU 4).hasSum.sub ((hU 3).hasSum.mul_left _)).add ((hU 2).hasSum.mul_left _)).sub
      ((hU 1).hasSum.mul_left _)).add (hT.hasSum.mul_left _)
  have htail := hsum.unique hz
  unfold rsLocalPoly
  linear_combination (-1 : ℂ) * h4 + (a * b * x) * h3 +
    (-(a ^ 2 * q + b ^ 2 * q - 2 * q ^ 2) * x ^ 2) * h2 + (a * b * q ^ 2 * x ^ 3) * h1 + htail

/-- The symmetric square factor for real $a$: $D(X) = (1-qX)\,(1-qX)(1-(a^2-2q)X+q^2X^2)$. -/
theorem rsLocalPoly_self (a q X : ℂ) :
    rsLocalPoly a a q X = (1 - q * X) * ((1 - q * X) * (1 - (a ^ 2 - 2 * q) * X + q ^ 2 * X ^ 2)) := by
  unfold rsLocalPoly
  ring

/-! ### Row 16: the Euler product of $L(f\times\bar g, s)$ -/

/-- The local factor $D_p(p^{-w})$ of $L(f\times\bar g)$ at $p$, $q = p^{k-1}$. -/
def rsLocal (k : ℕ) (a b : ℂ) (p : ℕ) (w : ℂ) : ℂ :=
  rsLocalPoly a b ((p : ℂ) ^ (k - 1)) ((p : ℂ) ^ (-w))

theorem isHeckeSeq_of_eigenform {k : ℕ} {a : ℕ → ℂ} (ha : IsNormalizedEigenform k a) {p : ℕ}
    (hp : p.Prime) : IsHeckeSeq (a p) ((p : ℂ) ^ (k - 1)) (fun r ↦ a (p ^ r)) where
  zero := by simpa using ha.one
  one := by simp
  succ r := ha.prime_pow p hp r

theorem isHeckeSeq_conj {a q : ℂ} {A : ℕ → ℂ} (hA : IsHeckeSeq a q A) (hq : conj q = q) :
    IsHeckeSeq (conj a) q (fun r ↦ conj (A r)) where
  zero := by simp [hA.zero]
  one := by simp [hA.one]
  succ r := by rw [hA.succ r, map_sub, map_mul, map_mul, hq]

private lemma coeff_isBigO' {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) :
    (fun n ↦ coeff f n) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ((k : ℝ) / 2) := by
  have h := CuspFormClass.qExpansion_isBigO (Γ := (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))) f
  rw [Subgroup.strictWidthInfty_SL2Z] at h
  simpa [coeff] using h

private lemma lSeriesSummable_rsCoeff' {k : ℕ} (f g : CuspForm 𝒮ℒ (k : ℤ)) {w : ℂ}
    (hw : (k : ℝ) + 1 < w.re) : LSeriesSummable (rsCoeff f g) w := by
  have hf := coeff_isBigO' f
  have hg := coeff_isBigO' g
  have hg' : (fun n ↦ conj (coeff g n)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ((k : ℝ) / 2) := by
    obtain ⟨C, hC⟩ := hg.bound
    exact IsBigO.of_bound C (hC.mono fun n h ↦ by simpa using h)
  have hO : rsCoeff f g =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ((k : ℝ) + 1 - 1) := by
    have h : rsCoeff f g =O[atTop]
        fun n : ℕ ↦ (n : ℝ) ^ ((k : ℝ) / 2) * (n : ℝ) ^ ((k : ℝ) / 2) := hf.mul hg'
    refine h.congr_right (fun n ↦ ?_)
    rw [← Real.rpow_add_of_nonneg (Nat.cast_nonneg _) (by positivity) (by positivity)]
    congr 1; ring
  exact LSeriesSummable_of_isBigO_rpow (x := (k : ℝ) + 1) hw hO

private lemma pow_mul_cpow_aux {k : ℕ} (hk : 1 ≤ k) {p : ℕ} (hp : p ≠ 0) (s : ℂ) :
    (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-(s + k - 1)) = (p : ℂ) ^ (-s) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [Nat.add_sub_cancel, ← cpow_natCast, ← cpow_add _ _ hp']
  congr 1
  push_cast
  ring

private lemma one_sub_cpow_ne_zero' {p : ℕ} (hp : 1 < p) {s : ℂ} (hs : 1 < s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have h2 : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_natCast_cpow_of_pos (by omega)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp) (by rw [Complex.neg_re]; linarith)
  rw [h1] at h2
  simp at h2

/-- **The Euler product of the Rankin–Selberg $L$-function** for normalized eigenforms of level one and
$\operatorname{Re}s > 2$: $L(f\times\bar g,s) = \prod_pD_p(p^{-(s+k-1)})^{-1}$. -/
theorem hasProd_rankinSelbergL (k : ℕ) (hk : 1 ≤ k) (f g : CuspForm 𝒮ℒ (k : ℤ))
    (hf : IsNormalizedEigenform k (coeff f)) (hg : IsNormalizedEigenform k (coeff g)) {s : ℂ}
    (hs : 2 < s.re) :
    HasProd (fun p : Nat.Primes ↦ (rsLocal k (coeff f p) (conj (coeff g p)) p (s + k - 1))⁻¹)
      (rankinSelbergL k f g s) := by
  obtain ⟨w, hwdef⟩ : ∃ w : ℂ, w = s + k - 1 := ⟨_, rfl⟩
  have hw : (k : ℝ) + 1 < w.re := by rw [hwdef]; simp; linarith
  have hLS := lSeriesSummable_rsCoeff' f g hw
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ → ℂ, F = LSeries.term (rsCoeff f g) w := ⟨_, rfl⟩
  have hsum : Summable (fun n ↦ ‖F n‖) := by rw [hFdef]; exact hLS.norm
  have hF0 : F 0 = 0 := by rw [hFdef]; exact LSeries.term_zero _ _
  have hF1 : F 1 = 1 := by
    rw [hFdef, LSeries.term_of_ne_zero one_ne_zero]
    simp [rsCoeff, hf.one, hg.one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → F (m * n) = F m * F n := by
    intro m n h
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hF0]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF0]
    rw [hFdef]
    rw [LSeries.term_of_ne_zero (Nat.mul_ne_zero hm.ne' hn.ne'), LSeries.term_of_ne_zero hm.ne',
      LSeries.term_of_ne_zero hn.ne', Nat.cast_mul, natCast_mul_natCast_cpow, div_mul_div_comm]
    congr 1
    simp only [rsCoeff, hf.mul h, hg.mul h, map_mul]
    ring
  have hE := EulerProduct.eulerProduct_hasProd hF1 hmul hsum hF0
  have hZ := riemannZeta_eulerProduct_hasProd (s := 2 * s)
    (by have : (2 * s).re = 2 * s.re := by simp
        rw [this]; linarith)
  have hloc : ∀ p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ * ∑' e, F ((p : ℕ) ^ e) =
      (rsLocal k (coeff f p) (conj (coeff g p)) p w)⁻¹ := by
    intro p
    have hp := p.2
    have hpow : ∀ e : ℕ, ((((p : ℕ) ^ e : ℕ)) : ℂ) ^ w = (((p : ℕ) : ℂ) ^ w) ^ e := by
      intro e
      induction e with
      | zero => simp
      | succ e ih => rw [pow_succ, Nat.cast_mul, natCast_mul_natCast_cpow, ih, pow_succ]
    have hFp : ∀ e : ℕ, F ((p : ℕ) ^ e) =
        coeff f ((p : ℕ) ^ e) * conj (coeff g ((p : ℕ) ^ e)) * (((p : ℕ) : ℂ) ^ (-w)) ^ e := by
      intro e
      have hne : (p : ℕ) ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
      rw [hFdef, LSeries.term_of_ne_zero hne, hpow, div_eq_mul_inv, cpow_neg, inv_pow]
      rfl
    have hAs := isHeckeSeq_of_eigenform hf hp
    have hq : conj (((p : ℕ) : ℂ) ^ (k - 1)) = ((p : ℕ) : ℂ) ^ (k - 1) := by simp
    have hBs := isHeckeSeq_conj (isHeckeSeq_of_eigenform hg hp) hq
    have hS : Summable fun e : ℕ ↦ ‖coeff f ((p : ℕ) ^ e) * conj (coeff g ((p : ℕ) ^ e)) *
        (((p : ℕ) : ℂ) ^ (-w)) ^ e‖ := by
      have := hsum.comp_injective (Nat.pow_right_injective hp.two_le : Function.Injective ((p : ℕ) ^ ·))
      refine this.congr (fun e ↦ ?_)
      simp only [Function.comp, hFp]
    have hmain := tsum_mul_rsLocalPoly hAs hBs hS
    have hsumeq : ∑' e, F ((p : ℕ) ^ e) = ∑' r, coeff f ((p : ℕ) ^ r) * conj (coeff g ((p : ℕ) ^ r)) *
        (((p : ℕ) : ℂ) ^ (-w)) ^ r := tsum_congr hFp
    have hqx : (((p : ℕ) : ℂ) ^ (k - 1)) ^ 2 * (((p : ℕ) : ℂ) ^ (-w)) ^ 2 =
        ((p : ℕ) : ℂ) ^ (-(2 * s)) := by
      rw [← mul_pow, hwdef, pow_mul_cpow_aux hk hp.ne_zero s, ← cpow_nat_mul]
      congr 1
      push_cast
      ring
    rw [hqx] at hmain
    have h1y := one_sub_cpow_ne_zero' (p := (p : ℕ)) hp.one_lt (s := 2 * s)
      (by have : (2 * s).re = 2 * s.re := by simp
          rw [this]; linarith)
    unfold rsLocal
    rw [hsumeq]
    have hD : rsLocalPoly (coeff f p) (conj (coeff g p)) (((p : ℕ) : ℂ) ^ (k - 1))
        (((p : ℕ) : ℂ) ^ (-w)) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hmain
      exact h1y (by linear_combination -hmain)
    rw [eq_div_of_mul_eq hD hmain]
    field_simp
  have hfun : (fun p : Nat.Primes ↦ (rsLocal k (coeff f p) (conj (coeff g p)) p w)⁻¹) =
      fun p : Nat.Primes ↦ (1 - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ * ∑' e, F ((p : ℕ) ^ e) :=
    funext fun p ↦ (hloc p).symm
  rw [← hwdef]
  rw [hfun]
  unfold rankinSelbergL
  rw [← hwdef]
  have hL : ∑' n, F n = LSeries (rsCoeff f g) w := by rw [hFdef]; rfl
  rw [hL] at hE
  exact hZ.mul hE

/-! ### Row 17: the symmetric square -/

/-- The symmetric square factor $S_p(p^{-w}) = (1-qX)(1-(a^2-2q)X+q^2X^2)$, $X = p^{-w}$, $q = p^{k-1}$. -/
def symSqLocal (k : ℕ) (a : ℂ) (p : ℕ) (w : ℂ) : ℂ :=
  (1 - (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-w)) *
    (1 - (a ^ 2 - 2 * (p : ℂ) ^ (k - 1)) * (p : ℂ) ^ (-w) + ((p : ℂ) ^ (k - 1)) ^ 2 * ((p : ℂ) ^ (-w)) ^ 2)

/-- **The symmetric square $L$-function** $L(\mathrm{Sym}^2f,w) = \prod_pS_p(p^{-w})^{-1}$ (Shimura 1975 `shimura1975`). -/
def symSqL (k : ℕ) (f : CuspForm 𝒮ℒ (k : ℤ)) (w : ℂ) : ℂ :=
  ∏' p : Nat.Primes, (symSqLocal k (coeff f p) p w)⁻¹

/-- **$L(f\times\bar f, s) = \zeta(s)L(\mathrm{Sym}^2f, s+k-1)$** for $\operatorname{Re}s > 2$, and the Euler product of
$L(\mathrm{Sym}^2f,w)$ converges for $\operatorname{Re}w > k+1$. -/
theorem symSqL_spec (k : ℕ) (hk : 1 ≤ k) (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : IsNormalizedEigenform k (coeff f))
    {s : ℂ} (hs : 2 < s.re) :
    HasProd (fun p : Nat.Primes ↦ (symSqLocal k (coeff f p) p (s + k - 1))⁻¹) (symSqL k f (s + k - 1)) ∧
      rankinSelbergL k f f s = riemannZeta s * symSqL k f (s + k - 1) := by
  have hP := hasProd_rankinSelbergL k hk f f hf hf hs
  have hs1 : 1 < s.re := by linarith
  have hZ := riemannZeta_eulerProduct_hasProd hs1
  have hZne := riemannZeta_ne_zero_of_one_lt_re hs1
  have hZi := hZ.inv₀ hZne
  have hM := hP.mul hZi
  have hkey : ∀ u S : ℂ, u ≠ 0 → (u * (u * S))⁻¹ * u = (u * S)⁻¹ := by
    intro u S hu
    rw [mul_inv, mul_inv]
    have : u⁻¹ * u = 1 := inv_mul_cancel₀ hu
    linear_combination (u⁻¹ * S⁻¹) * this
  have hfun : (fun p : Nat.Primes ↦ (rsLocal k (coeff f p) (conj (coeff f p)) p (s + k - 1))⁻¹ *
      ((1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹)⁻¹) =
      fun p : Nat.Primes ↦ (symSqLocal k (coeff f p) p (s + k - 1))⁻¹ := by
    funext p
    rw [hf.real p, inv_inv]
    unfold rsLocal
    rw [rsLocalPoly_self]
    have hqx := pow_mul_cpow_aux hk p.2.ne_zero s
    have hu := one_sub_cpow_ne_zero' (p := (p : ℕ)) p.2.one_lt hs1
    unfold symSqLocal
    rw [hqx]
    exact hkey _ _ hu
  have hM' : HasProd (fun p : Nat.Primes ↦ (symSqLocal k (coeff f p) p (s + k - 1))⁻¹)
      (rankinSelbergL k f f s * (riemannZeta s)⁻¹) := by
    rw [← hfun]; exact hM
  have e : symSqL k f (s + k - 1) = rankinSelbergL k f f s * (riemannZeta s)⁻¹ := hM'.tprod_eq
  refine ⟨by rw [e]; exact hM', ?_⟩
  rw [e]
  field_simp

end ModularFormsKB.RankinSelberg
