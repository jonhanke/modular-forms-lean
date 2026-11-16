import ModularFormsKB.Elliptic.CongruentModular
import ModularFormsKB.Elliptic.Bridge
import ModularFormsKB.Elliptic.QSeriesDilate
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.RootNumber

/-!
# The level of $f_{32} \otimes \chi_n$ is $32n^2$

For $n$ odd and squarefree, let $g$ be Tau Ceti's primitive twist of $f_{32}$ by $\chi_n = \left(\frac\cdot n\right)$,
of level $R$, so that $32 \mid R \mid 32n^2$ (`thirtyTwo_dvd_f32TwistLevel`, `f32TwistLevel_dvd`), and write
$32n^2 = RN'$. We prove $N' = 1$ (`f32TwistLevel_eq_of_odd`), so that `TwistLevelRamified` is not needed for
$f_{32}$ and `hasNewform_congruentCurve` is unconditional. The argument is the classical one (Atkin–Li 1978,
§3 [unverified]):

1. The coefficients $a(m) = \left(\frac nm\right) b(m)$ of $F = f_{32} \otimes \chi_n$ and the coefficients $b_g$ of
   $g$ satisfy $a = C * b_g$ (Dirichlet convolution), where $C$ is multiplicative, supported on the divisors
   of $N'$, with $C(p) = -b_g(p)$ and $C(p^2) = p\,[p \nmid R]$ at $p \mid n$ (`congruentCoeff_eq_sum_corr`).
   So $F(z) = \sum_{d \mid N'} C(d)\, g(dz)$.
2. $F|_2\omega_{32n^2} = -\left(\frac{-2}n\right) F$ (Miyake, Theorem 4.3.11, with $f_{32}|_2\omega_{32} = -f_{32}$;
   `fricke_congruentCoeff`), and $g|_2\omega_R = \varepsilon g$ (Tau Ceti's Fricke sign; `fricke_qSeries_nfCoeff`).
   Since $g(d\,\cdot)|_2\omega_{Rde} = \frac ed\,(g|_2\omega_R)(e\,\cdot)$ (`Miyake.fricke_two_dilate`),
   $F|_2\omega_{32n^2}(z) = \varepsilon \sum_{d \mid N'} C(d) \frac{N'/d}{d}\, g(\tfrac{N'}{d} z)$.
3. The coefficient of $q$ gives $\varepsilon C(N')/N' = -\left(\frac{-2}n\right)$, so $|C(N')| = N'$, while
   $|C(N')|^2 \le N'$ (`norm_corr_sq_le`: $|b_g(p)| = 1$ at $p \parallel R$, Tau Ceti's Atkin–Lehner eigenvalue).
   Hence $N' = 1$.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Elliptic

open HeckeRing.GL2 TauCeti
open scoped TauCeti.ExactDivisor

/-! ### Newforms of weight $2$ and their coefficients -/

section Newform

variable {R : ℕ} [NeZero R] (g : Newform R 2)

/-- The $q$-expansion coefficients of a newform. -/
def nfCoeff (m : ℕ) : ℂ := (qExpansion 1 g.toCuspForm).coeff m

theorem nfCoeff_zero : nfCoeff g 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero g.toCuspForm one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map R)

theorem nfCoeff_one : nfCoeff g 1 = 1 := g.isNorm

theorem nfCoeff_mul {u v : ℕ} (h : u.Coprime v) : nfCoeff g (u * v) = nfCoeff g u * nfCoeff g v := by
  have hE1 : (qExpansion 1 g.toEigenform.toCuspForm).coeff 1 = 1 := by
    rw [Newform.toEigenform_toCuspForm]; exact g.isNorm
  simpa [nfCoeff, Newform.toEigenform_toCuspForm] using g.toEigenform.qExpansion_coeff_mul hE1 h

private theorem nfCoeff_hrec (p : ℕ) (hp : p.Prime) (r : ℕ) :
    nfCoeff g (p ^ (r + 2)) = nfCoeff g p * nfCoeff g (p ^ (r + 1)) -
      (MulChar.ofUnitHom g.χ : DirichletCharacter ℂ R) p * (p : ℂ) ^ ((2 : ℤ) - 1) * nfCoeff g (p ^ r) := by
  have hE1 : (qExpansion 1 g.toEigenform.toCuspForm).coeff 1 = 1 := by
    rw [Newform.toEigenform_toCuspForm]; exact g.isNorm
  simpa [nfCoeff, Newform.toEigenform_toCuspForm, Newform.toEigenform_χ] using
    g.toEigenform.qExpansion_coeff_prime_pow_add_two hE1 hp r

/-- The Hecke recursion at a prime not dividing the level, trivial nebentypus, weight $2$. -/
theorem nfCoeff_prime_pow_add_two_of_coprime (hχ : g.χ = 1) {p : ℕ} (hp : p.Prime) (hpR : p.Coprime R)
    (j : ℕ) :
    nfCoeff g (p ^ (j + 2)) = nfCoeff g p * nfCoeff g (p ^ (j + 1)) - p * nfCoeff g (p ^ j) := by
  have hχp : (MulChar.ofUnitHom g.χ : DirichletCharacter ℂ R) p = 1 := by
    rw [← Newform.dirichletLift_def, g.dirichletLift_apply_of_coprime hpR, hχ]
    simp
  rw [nfCoeff_hrec g p hp j, hχp]
  norm_num

/-- The Hecke recursion at a prime dividing the level. -/
theorem nfCoeff_prime_pow_add_two_of_dvd {p : ℕ} (hp : p.Prime) (hpR : p ∣ R) (j : ℕ) :
    nfCoeff g (p ^ (j + 2)) = nfCoeff g p * nfCoeff g (p ^ (j + 1)) := by
  have hχp : (MulChar.ofUnitHom g.χ : DirichletCharacter ℂ R) p = 0 := by
    apply MulChar.map_nonunit
    rw [ZMod.isUnit_iff_coprime]
    exact fun h ↦ hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h hpR)
  rw [nfCoeff_hrec g p hp j, hχp]
  simp

/-- $a_p = 0$ when $p^2$ divides the level (trivial nebentypus). -/
theorem nfCoeff_prime_eq_zero_of_sq_dvd (hχ : g.χ = 1) {p : ℕ} (hp : p.Prime) (h : p ^ 2 ∣ R) :
    nfCoeff g p = 0 := by
  have hpR : p ∣ R := (dvd_pow_self p two_ne_zero).trans h
  have hsqR : 2 ≤ R.factorization p := by
    rw [← hp.pow_dvd_iff_le_factorization (NeZero.ne R)]; exact h
  have hcond : g.dirichletLift.conductor.factorization p = 0 := by
    have h1 : g.dirichletLift = 1 := by
      ext u
      rw [Newform.dirichletLift_def, MulChar.ofUnitHom_coe, hχ]
      simp
    rw [h1, DirichletCharacter.conductor_one]
    simp
  by_contra hne
  have := (g.qExpansion_coeff_prime_ne_zero_iff hp hpR).1 hne
  rw [hcond] at this
  omega

/-- $a_p^2 = 1$ when $p \parallel R$ (trivial nebentypus, weight $2$; Tau Ceti's Atkin–Lehner sign). -/
theorem nfCoeff_prime_sq_of_dvd_of_not_sq_dvd (hχ : g.χ = 1) {p : ℕ} (hp : p.Prime) (h : p ∣ R)
    (h2 : ¬ p ^ 2 ∣ R) : nfCoeff g p ^ 2 = 1 := by
  have hex : p ∥ R := .of_not_sq_dvd hp h h2
  have := Newform.qExpansion_coeff_prime_eq_neg_atkinLehnerSign_mul g hχ hp h h2
  show (qExpansion 1 g.toCuspForm).coeff p ^ 2 = 1
  rw [this, neg_sq, Newform.atkinLehnerSign_mul_sqrt_zpow_sq g hχ hex]
  simp

theorem coeffGrowth_nfCoeff : Miyake.CoeffGrowth (nfCoeff g) :=
  (cuspForm_qSeries_coeff g.toCuspForm).1

/-- **The Fricke relation of a newform** of weight $2$ and trivial nebentypus, in Miyake's normalization. -/
theorem fricke_qSeries_nfCoeff (hχ : g.χ = 1) (z : ℂ) (hz : 0 < z.im) :
    Miyake.fricke 2 R (Miyake.qSeries (nfCoeff g)) z = g.frickeSign hχ * Miyake.qSeries (nfCoeff g) z := by
  have hN : 0 < R := Nat.pos_of_ne_zero (NeZero.ne R)
  have hF : ⇑g.toCuspForm = fun τ : ℍ ↦ Miyake.qSeries (nfCoeff g) τ :=
    funext (cuspForm_qSeries_coeff g.toCuspForm).2
  have h1 := congrFun (Miyake.fricke_eq_smul_slash (k := 2) hN (Miyake.qSeries (nfCoeff g)))
    ⟨z, hz⟩
  have hW := congrArg
    (fun g : CuspForm ((Gamma1 R).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2 ↦ (⇑g : ℍ → ℂ))
    (g.normalizedFrickeOperatorCusp_eq_frickeSign_smul hχ)
  simp only [TauCeti.coe_normalizedFrickeOperatorCusp, FunLike.coe_smul, hF] at hW
  have hW' := congrFun hW ⟨z, hz⟩
  have hω : Miyake.omegaGL R hN = TauCeti.frickeGL ℝ R := rfl
  rw [hω] at h1
  simp [TauCeti.atkinLehnerNormalizer] at h1 hW'
  exact h1.trans hW'

end Newform

/-! ### The correction factor $C$ -/

/-- The local factor at $p$ of $C$: $1 - b(p)X + p\,[p \nmid R]\,X^2$ if $p \mid n$, and $1$ otherwise. -/
def corrLocal (n R : ℕ) (b : ℕ → ℂ) (p k : ℕ) : ℂ :=
  if k = 0 then 1 else if ¬ p ∣ n then 0 else
    if k = 1 then -b p else if k = 2 then (if p ∣ R then 0 else (p : ℂ)) else 0

/-- The multiplicative function $C$ with local factors `corrLocal`. -/
def corr (n R : ℕ) (b : ℕ → ℂ) (m : ℕ) : ℂ :=
  if m = 0 then 0 else m.factorization.prod fun p k ↦ corrLocal n R b p k

section corr

variable {n R : ℕ} {b : ℕ → ℂ}

theorem corr_one : corr n R b 1 = 1 := by
  simp [corr]

theorem corr_mul {u v : ℕ} (h : u.Coprime v) : corr n R b (u * v) = corr n R b u * corr n R b v := by
  rcases eq_or_ne u 0 with rfl | hu
  · have : v = 1 := Nat.coprime_zero_left v |>.1 h
    subst this
    simp [corr]
  rcases eq_or_ne v 0 with rfl | hv
  · have : u = 1 := Nat.coprime_zero_right u |>.1 h
    subst this
    simp [corr]
  unfold corr
  rw [if_neg (mul_ne_zero hu hv), if_neg hu, if_neg hv, Nat.factorization_mul_of_coprime h,
    Finsupp.prod_add_index_of_disjoint h.disjoint_primeFactors]

theorem corr_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : corr n R b (p ^ k) = corrLocal n R b p k := by
  unfold corr
  rw [if_neg (pow_ne_zero k hp.ne_zero), hp.factorization_pow,
    Finsupp.prod_single_index (by simp [corrLocal])]

/-- **The coefficient identity** $a = C * b$, for multiplicative $a$, $b$ which agree on the powers of the primes
$p \nmid n$, with $a(p^k) = 0$ ($k \ge 1$) and the Hecke recursion of $b$ (nebentypus $p \mapsto [p \nmid R]$) at
$p \mid n$. -/
theorem eq_sum_corr {a : ℕ → ℂ} (ha0 : a 0 = 0) (ha1 : a 1 = 1)
    (ham : ∀ u v : ℕ, u.Coprime v → a (u * v) = a u * a v) (hb0 : b 0 = 0) (hb1 : b 1 = 1)
    (hbm : ∀ u v : ℕ, u.Coprime v → b (u * v) = b u * b v)
    (hgood : ∀ p k : ℕ, p.Prime → ¬ p ∣ n → a (p ^ k) = b (p ^ k))
    (hbad : ∀ p k : ℕ, p.Prime → p ∣ n → 0 < k → a (p ^ k) = 0)
    (hrec : ∀ p j : ℕ, p.Prime → p ∣ n →
      b (p ^ (j + 2)) = b p * b (p ^ (j + 1)) - (if p ∣ R then 0 else (p : ℂ)) * b (p ^ j))
    (m : ℕ) : a m = ∑ d ∈ m.divisors, corr n R b d * b (m / d) := by
  classical
  let A : ArithmeticFunction ℂ := ⟨a, ha0⟩
  let B : ArithmeticFunction ℂ := ⟨b, hb0⟩
  let Cf : ArithmeticFunction ℂ := ⟨corr n R b, by simp [corr]⟩
  have hA : A.IsMultiplicative := ⟨ha1, fun {u v} huv ↦ ham u v huv⟩
  have hB : B.IsMultiplicative := ⟨hb1, fun {u v} huv ↦ hbm u v huv⟩
  have hCf : Cf.IsMultiplicative := ⟨corr_one, fun {u v} huv ↦ corr_mul huv⟩
  have key : A = Cf * B := by
    refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hA _ (hCf.mul hB)).2
      fun p k hp ↦ ?_
    have hexp : (Cf * B) (p ^ k) =
        ∑ i ∈ Finset.range (k + 1), corrLocal n R b p i * b (p ^ (k - i)) := by
      rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun i j ↦ Cf i * B j),
        Nat.divisors_prime_pow hp, Finset.sum_map]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      show corr n R b (p ^ i) * b (p ^ k / p ^ i) = _
      rw [corr_prime_pow hp, Nat.pow_div hik hp.pos]
    show a (p ^ k) = (Cf * B) (p ^ k)
    rw [hexp]
    by_cases hpn : p ∣ n
    · rcases k with _ | _ | j
      · simp [corrLocal, ha1, hb1]
      · rw [hbad p 1 hp hpn one_pos]
        simp [Finset.sum_range_succ, corrLocal, hpn, hb1]
      · rw [hbad p (j + 2) hp hpn (by omega)]
        have hzero : ∀ i ∈ Finset.range (j + 3), i ∉ Finset.range 3 →
            corrLocal n R b p i * b (p ^ (j + 2 - i)) = 0 := by
          intro i _ hi3
          have : 3 ≤ i := by simpa using hi3
          simp [corrLocal, hpn, show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega]
        rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : 3 ≤ j + 3)) hzero]
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
        have h1 : j + 2 - 1 = j + 1 := by omega
        have h2 : j + 2 - 2 = j := by omega
        rw [Nat.sub_zero, h1, h2, hrec p j hp hpn]
        simp [corrLocal, hpn]
        ring
    · rw [Finset.sum_eq_single 0]
      · simp [corrLocal, hgood p k hp hpn]
      · intro i _ hi
        simp [corrLocal, hi, hpn]
      · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos k)) h
  have := congrArg (fun F : ArithmeticFunction ℂ ↦ F m) key
  simp only [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun i j ↦ Cf i * B j)] at this
  exact this

/-- $C$ is supported on the divisors of $N' = 32n^2/R$. -/
theorem dvd_of_corr_ne_zero (hsq : Squarefree n) {N' : ℕ} (hRN : R * N' = 32 * n ^ 2)
    (hb : ∀ p : ℕ, p.Prime → p ^ 2 ∣ R → b p = 0) {d : ℕ} (hd : corr n R b d ≠ 0) : d ∣ N' := by
  have hn0 : n ≠ 0 := hsq.ne_zero
  have hd0 : d ≠ 0 := by rintro rfl; simp [corr] at hd
  have hRN0 : R * N' ≠ 0 := by rw [hRN]; positivity
  have hR0 : R ≠ 0 := left_ne_zero_of_mul hRN0
  have hN0 : N' ≠ 0 := right_ne_zero_of_mul hRN0
  have hprod : d.factorization.prod (fun p k ↦ corrLocal n R b p k) ≠ 0 := by
    simpa [corr, hd0] using hd
  rw [Finsupp.prod] at hprod
  rw [← Nat.factorization_le_iff_dvd hd0 hN0]
  intro p
  by_cases hpm : p ∈ d.factorization.support
  · have h := Finset.prod_ne_zero_iff.1 hprod p hpm
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hpm)
    have hi : d.factorization p ≠ 0 := Finsupp.mem_support_iff.1 hpm
    set i := d.factorization p with hidef
    have hpn : p ∣ n := by
      by_contra hpn; apply h; simp [corrLocal, hi, hpn]
    have hcases : (i = 1 ∧ b p ≠ 0) ∨ (i = 2 ∧ ¬ p ∣ R) := by
      by_cases h1 : i = 1
      · left; refine ⟨h1, ?_⟩; intro hb0; apply h; simp [corrLocal, hi, hpn, h1, hb0]
      · by_cases h2 : i = 2
        · right; refine ⟨h2, ?_⟩; intro hR; apply h; simp [corrLocal, hi, hpn, h1, h2, hR]
        · exfalso; apply h; simp [corrLocal, hi, hpn, h1, h2]
    have htot : R.factorization p + N'.factorization p ≥ 2 := by
      have h2 : p ^ 2 ∣ R * N' := by
        rw [hRN]; exact (pow_dvd_pow_of_dvd hpn 2).trans (Dvd.intro_left 32 rfl)
      have := (hp.pow_dvd_iff_le_factorization hRN0).1 h2
      rwa [Nat.factorization_mul hR0 hN0, Finsupp.add_apply] at this
    rcases hcases with ⟨h1, hbp⟩ | ⟨h2, hpR⟩
    · have hnsq : ¬ p ^ 2 ∣ R := fun h2 ↦ hbp (hb p hp h2)
      have : R.factorization p < 2 := by
        by_contra hc
        exact hnsq ((hp.pow_dvd_iff_le_factorization hR0).2 (by omega))
      omega
    · have : R.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpR
      omega
  · have : d.factorization p = 0 := by rwa [Finsupp.mem_support_iff, not_not] at hpm
    omega

/-- $|C(N')|^2 \le N'$. -/
theorem norm_corr_sq_le (hn : Odd n) (hsq : Squarefree n) {N' : ℕ} (hRN : R * N' = 32 * n ^ 2)
    (h32 : 32 ∣ R) (hb : ∀ p : ℕ, p.Prime → p ∣ R → ¬ p ^ 2 ∣ R → b p ^ 2 = 1) :
    ‖corr n R b N'‖ ^ 2 ≤ N' := by
  have hn0 : n ≠ 0 := hsq.ne_zero
  have hRN0 : R * N' ≠ 0 := by rw [hRN]; positivity
  have hR0 : R ≠ 0 := left_ne_zero_of_mul hRN0
  have hN0 : N' ≠ 0 := right_ne_zero_of_mul hRN0
  have hN'n : N' ∣ n ^ 2 := by
    obtain ⟨r, hr⟩ := h32
    refine ⟨r, ?_⟩
    have : 32 * (r * N') = 32 * n ^ 2 := by rw [← hRN, hr]; ring
    have := Nat.eq_of_mul_eq_mul_left (by norm_num) this
    linarith
  have hloc : ∀ p ∈ N'.factorization.support,
      ‖corrLocal n R b p (N'.factorization p)‖ ^ 2 ≤ (p : ℝ) ^ (N'.factorization p) := by
    intro p hpm
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hpm)
    have hk1 : 1 ≤ N'.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hpm)
    have hpN : p ∣ N' := (hp.dvd_iff_one_le_factorization hN0).2 hk1
    have hpn : p ∣ n := hp.dvd_of_dvd_pow (hpN.trans hN'n)
    have hp2 : p ≠ 2 := by
      rintro rfl
      have := Nat.odd_iff.1 hn
      omega
    have hnf : n.factorization p = 1 := by
      have h1 := (Nat.squarefree_iff_factorization_le_one hn0).1 hsq p
      have h2 := (hp.dvd_iff_one_le_factorization hn0).1 hpn
      omega
    have h32f : (32 : ℕ).factorization p = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd fun h ↦ hp2 ?_
      have h' : p ∣ 2 ^ 5 := by norm_num; exact h
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h')
    have htot : R.factorization p + N'.factorization p = 2 := by
      have := congrArg (fun m ↦ m.factorization p) hRN
      rw [Nat.factorization_mul hR0 hN0, Nat.factorization_mul (by norm_num) (pow_ne_zero 2 hn0),
        Nat.factorization_pow] at this
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, h32f, hnf] at this
      omega
    obtain hk | hk : N'.factorization p = 1 ∨ N'.factorization p = 2 := by omega
    · rw [hk]
      have hRf : R.factorization p = 1 := by omega
      have hpR : p ∣ R := (hp.dvd_iff_one_le_factorization hR0).2 (by omega)
      have hnsq : ¬ p ^ 2 ∣ R := fun h2 ↦ by
        have := (hp.pow_dvd_iff_le_factorization hR0).1 h2
        omega
      have hbp := hb p hp hpR hnsq
      have : corrLocal n R b p 1 = -b p := by simp [corrLocal, hpn]
      rw [this, norm_neg, ← norm_pow, hbp, norm_one]
      simpa using hp.one_lt.le
    · rw [hk]
      have hpR : ¬ p ∣ R := by
        rw [hp.dvd_iff_one_le_factorization hR0]; omega
      have : corrLocal n R b p 2 = (p : ℂ) := by simp [corrLocal, hpn, hpR]
      rw [this]
      simp
  have hnorm : ‖corr n R b N'‖ ^ 2 = ∏ p ∈ N'.factorization.support,
      ‖corrLocal n R b p (N'.factorization p)‖ ^ 2 := by
    unfold corr
    rw [if_neg hN0, Finsupp.prod, norm_prod, ← Finset.prod_pow]
  have hN'prod : (N' : ℝ) = ∏ p ∈ N'.factorization.support, (p : ℝ) ^ (N'.factorization p) := by
    have := congrArg (Nat.cast : ℕ → ℝ) (Nat.prod_factorization_pow_eq_self hN0)
    rw [Finsupp.prod] at this
    push_cast at this
    exact this.symm
  rw [hnorm]
  calc ∏ p ∈ N'.factorization.support, ‖corrLocal n R b p (N'.factorization p)‖ ^ 2
      ≤ ∏ p ∈ N'.factorization.support, (p : ℝ) ^ (N'.factorization p) :=
        Finset.prod_le_prod₀ (fun p _ ↦ by positivity) hloc
    _ = N' := hN'prod.symm

/-- Rewriting $\sum_{d \mid m} C(d)\,b(m/d)$ as a sum over the divisors of $N'$ when $C$ is supported on them. -/
theorem sum_divisors_eq_sum_dilate {C b : ℕ → ℂ} (hb0 : b 0 = 0) {N' : ℕ} (hN' : N' ≠ 0)
    (hC : ∀ d, C d ≠ 0 → d ∣ N') (m : ℕ) :
    ∑ d ∈ m.divisors, C d * b (m / d) = ∑ d ∈ N'.divisors, C d * Miyake.dilate d b m := by
  classical
  by_cases hm : m = 0
  · subst hm; simp [Miyake.dilate, hb0]
  have e1 : ∑ d ∈ m.divisors, C d * b (m / d) =
      ∑ d ∈ m.divisors with d ∣ N', C d * b (m / d) :=
    (Finset.sum_filter_of_ne (fun d _ h ↦ hC d (left_ne_zero_of_mul h))).symm
  have e2 : ∑ d ∈ N'.divisors, C d * Miyake.dilate d b m =
      ∑ d ∈ N'.divisors with d ∣ m, C d * b (m / d) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    by_cases h : d ∣ m <;> simp [Miyake.dilate, h]
  have e3 : m.divisors.filter (· ∣ N') = N'.divisors.filter (· ∣ m) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h2, hN'⟩, h1⟩
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h2, hm⟩, h1⟩
  rw [e1, e2, e3]

/-- **The Fricke transform of a combination of dilates** of a form $G = \sum b(m)q^m$ with
$G|_2\omega_R = \varepsilon G$:
$\bigl(\sum_{d \mid N'} C(d)\,G(d\,\cdot)\bigr)\big|_2\omega_{RN'} =
\varepsilon\sum_{d \mid N'} C(d)\,\frac{N'/d}{d}\,G(\tfrac{N'}d\,\cdot)$, as $q$-series. -/
theorem fricke_sum_dilate {R N' : ℕ} (hR : 0 < R) (hN' : 0 < N') {b : ℕ → ℂ} (hb : Miyake.CoeffGrowth b)
    {ε : ℂ} (hfr : ∀ z : ℂ, 0 < z.im → Miyake.fricke 2 R (Miyake.qSeries b) z = ε * Miyake.qSeries b z)
    (C : ℕ → ℂ) (z : ℂ) (hz : 0 < z.im) :
    Miyake.fricke 2 ((R * N' : ℕ) : ℝ)
        (Miyake.qSeries fun m ↦ ∑ d ∈ N'.divisors, C d * Miyake.dilate d b m) z =
      Miyake.qSeries (fun m ↦ ∑ d ∈ N'.divisors,
        C d * (((N' / d : ℕ) : ℂ) / d) * ε * Miyake.dilate (N' / d) b m) z := by
  classical
  have hdiv : ∀ d ∈ N'.divisors, 0 < d ∧ 0 < N' / d ∧ d * (N' / d) = N' := fun d hd ↦
    ⟨Nat.pos_of_mem_divisors hd, Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd),
      Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)⟩
  have hgrow1 : ∀ d ∈ N'.divisors, Miyake.CoeffGrowth (fun m ↦ C d * Miyake.dilate d b m) :=
    fun d hd ↦ Miyake.coeffGrowth_const_mul _ (Miyake.coeffGrowth_dilate (hdiv d hd).1 hb)
  have hgrow2 : ∀ d ∈ N'.divisors, Miyake.CoeffGrowth
      (fun m ↦ C d * (((N' / d : ℕ) : ℂ) / d) * ε * Miyake.dilate (N' / d) b m) :=
    fun d hd ↦ Miyake.coeffGrowth_const_mul _ (Miyake.coeffGrowth_dilate (hdiv d hd).2.1 hb)
  have hLHS : ∀ w : ℂ, 0 < w.im →
      Miyake.qSeries (fun m ↦ ∑ d ∈ N'.divisors, C d * Miyake.dilate d b m) w =
        ∑ d ∈ N'.divisors, C d * Miyake.qSeries b (d * w) := by
    intro w hw
    rw [Miyake.qSeries_finset_sum _ hgrow1 hw]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [Miyake.qSeries_const_mul', Miyake.qSeries_dilate (hdiv d hd).1]
  have hpos : (0 : ℝ) < ((R * N' : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hR hN'
  rw [Miyake.fricke_congr_upperHalfPlane (g := fun w ↦ ∑ d ∈ N'.divisors, C d * Miyake.qSeries b (d * w)) hpos
    hLHS hz, Miyake.fricke_finset_sum, Miyake.qSeries_finset_sum _ hgrow2 hz]
  have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  obtain ⟨hd0, he0, hde⟩ := hdiv d hd
  have hcast : ((R * N' : ℕ) : ℝ) = (R : ℝ) * d * ((N' / d : ℕ) : ℝ) := by
    rw [mul_assoc]; exact_mod_cast congrArg (R * ·) hde.symm
  have him : 0 < (((N' / d : ℕ) : ℂ) * z).im := by
    have : (((N' / d : ℕ) : ℂ) * z).im = ((N' / d : ℕ) : ℝ) * z.im := by simp
    rw [this]; exact mul_pos (by exact_mod_cast he0) hz
  rw [hcast, Miyake.fricke_two_dilate hR hd0 he0 (Miyake.qSeries b) hz0, hfr _ him,
    Miyake.qSeries_const_mul', ← Miyake.qSeries_dilate he0]
  ring

end corr

/-! ### The twist of $f_{32}$ by $\chi_n$ -/

section Twist

open ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves (congruentCoeff congruentSign f32Coeff f32Coeff_zero
  f32Coeff_one isMultiplicative_congruentArith congruentArith_apply congruentCurve)

theorem coeffGrowth_congruentCoeff (n : ℕ) : Miyake.CoeffGrowth fun m ↦ (congruentCoeff n m : ℂ) := by
  obtain ⟨ν, hν⟩ := ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.coeffGrowth_f32C
  refine ⟨ν, (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun m ↦ ?_)).trans hν⟩
  simp only [congruentCoeff, ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.f32C, one_mul]
  push_cast
  rw [norm_mul]
  rcases jacobiSym.trichotomy n m with h | h | h <;> simp [h]

open ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves in
/-- **The Fricke relation of $f_{32} \otimes \chi_n$** ($n$ odd squarefree): $F|_2\omega_{32n^2} =
-\left(\frac{-2}n\right) F$ (Miyake, Theorem 4.3.11, `Miyake.fricke_twist`, with `fricke_f32`). -/
theorem fricke_congruentCoeff {n : ℕ} [NeZero n] (hn : Odd n) (hsq : Squarefree n) (z : ℂ) (hz : 0 < z.im) :
    Miyake.fricke 2 ((32 * n ^ 2 : ℕ) : ℝ) (Miyake.qSeries fun m ↦ (congruentCoeff n m : ℂ)) z =
      -congruentSign n * Miyake.qSeries (fun m ↦ (congruentCoeff n m : ℂ)) z := by
  have hcop : n.Coprime 32 := by
    rw [show (32 : ℕ) = 2 ^ 5 by norm_num]
    exact (Nat.coprime_two_right.mpr hn).pow_right 5
  have hb : Miyake.CoeffGrowth (fun m ↦ -f32C m) := by
    obtain ⟨ν, hν⟩ := coeffGrowth_f32C
    exact ⟨ν, hν.neg_left⟩
  have h := Miyake.fricke_twist (k := 2) (N := 32) (m := n) two_pos (by norm_num) 1
    (ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.jacobiChar n) (isPrimitive_jacobiChar hn hsq) hcop coeffGrowth_f32C hb
    isCuspFormChar_f32.isModularFormChar (fun z hz ↦ by simpa using fricke_f32 z hz) z hz
  rw [jacobiChar_inv hn, weilConstant_jacobiChar hn hsq] at h
  have e1 : Miyake.twist (ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.jacobiChar n) f32C = fun m ↦ (congruentCoeff n m : ℂ) :=
    (twist_jacobiChar_f32C hn hsq).trans (lCoeff_eq hsq)
  have e2 : Miyake.twist (ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.jacobiChar n) (fun m ↦ -f32C m) =
      fun m ↦ -(congruentCoeff n m : ℂ) := by
    funext m
    have := congrFun e1 m
    simp only [Miyake.twist] at this ⊢
    simp [← this]
  rw [e1, e2] at h
  have e3 : Miyake.qSeries (fun m ↦ -(congruentCoeff n m : ℂ)) z =
      -Miyake.qSeries (fun m ↦ (congruentCoeff n m : ℂ)) z := by
    simp [Miyake.qSeries, tsum_neg]
  rw [e3] at h
  push_cast at h ⊢
  linear_combination h

/-- The coefficients of the twist $g$ of $f_{32}$ by $\chi_n$ on the powers of the primes $p \nmid n$:
$b_g(p^k) = \left(\frac n{p^k}\right) b(p^k)$ (at $p = 2$ both vanish, $4 \mid$ the level). -/
theorem nfCoeff_f32Twist_prime_pow {n : ℕ} [NeZero n] (hn : Odd n) {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n)
    (k : ℕ) :
    nfCoeff (f32NewformDef.primitiveTwist (jacobiChar n hn)) (p ^ k) = congruentCoeff n (p ^ k) := by
  set g := f32NewformDef.primitiveTwist (jacobiChar n hn) with hg
  have hχ : g.χ = 1 := f32Twist_χ hn
  by_cases hp2 : p = 2
  · subst hp2
    have hR4 : 2 ^ 2 ∣ f32NewformDef.primitiveTwistLevel (jacobiChar n hn) :=
      (show 2 ^ 2 ∣ 32 by norm_num).trans (thirtyTwo_dvd_f32TwistLevel hn)
    have hR2 : 2 ∣ f32NewformDef.primitiveTwistLevel (jacobiChar n hn) :=
      (dvd_pow_self 2 two_ne_zero).trans hR4
    have ha2 : nfCoeff g 2 = 0 := nfCoeff_prime_eq_zero_of_sq_dvd g hχ hp hR4
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [nfCoeff_one, congruentCoeff, f32Coeff_one]
    · rw [congruentCoeff_prime_pow_of_dvd hp (dvd_mul_right 2 n) hk]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rcases j with _ | j
      · simpa using ha2
      · rw [show j + 1 + 1 = j + 2 by ring, nfCoeff_prime_pow_add_two_of_dvd g hp hR2, ha2]
        simp
  · have hpn2 : ¬ p ∣ 2 * n := by
      intro h
      rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h2
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
      · exact hpn h2
    have hcopR : p.Coprime (f32NewformDef.primitiveTwistLevel (jacobiChar n hn)) := by
      refine Nat.Coprime.coprime_dvd_right (f32TwistLevel_dvd hn) ?_
      refine Nat.Coprime.mul_right ?_ (Nat.Coprime.pow_right 2 ?_)
      · have : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
        simpa using this.pow_right 5
      · exact (Nat.Prime.coprime_iff_not_dvd hp).2 hpn
    have hap : nfCoeff g p = (congruentCoeff n p : ℂ) := by
      show (qExpansion 1 g.toCuspForm).coeff p = _
      rw [qExpansion_coeff_f32Twist_prime hn hp hpn2, congruentCoeff_eq_jacobiChar hn p]
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      match k with
      | 0 => simp [nfCoeff_one, congruentCoeff, f32Coeff_one]
      | 1 => simpa using hap
      | j + 2 =>
        rw [nfCoeff_prime_pow_add_two_of_coprime g hχ hp hcopR j, ih (j + 1) (by omega),
          ih j (by omega), hap, congruentCoeff_prime_pow_add_two hp hpn2 j]
        push_cast
        ring

/-- **The level of $f_{32} \otimes \chi_n$ is $32n^2$** for odd squarefree $n$ (Atkin–Li 1978, Theorem 3.1
[unverified], for this twist; no named input). -/
theorem f32TwistLevel_eq_of_odd {n : ℕ} [NeZero n] (hn : Odd n) (hsq : Squarefree n) :
    f32NewformDef.primitiveTwistLevel (jacobiChar n hn) = 32 * n ^ 2 := by
  set R := f32NewformDef.primitiveTwistLevel (jacobiChar n hn) with hRdef
  set g := f32NewformDef.primitiveTwist (jacobiChar n hn) with hgdef
  have hχ : g.χ = 1 := f32Twist_χ hn
  obtain ⟨N', hN'⟩ := f32TwistLevel_dvd hn
  have hRN : R * N' = 32 * n ^ 2 := hN'.symm
  have hn0 : n ≠ 0 := NeZero.ne n
  have hR0 : 0 < R := Nat.pos_of_ne_zero (NeZero.ne R)
  have hN0 : 0 < N' := by
    rcases Nat.eq_zero_or_pos N' with h | h
    · rw [h, mul_zero] at hRN; exact absurd hRN.symm (by positivity)
    · exact h
  set a : ℕ → ℂ := fun m ↦ (congruentCoeff n m : ℂ) with ha
  set b : ℕ → ℂ := nfCoeff g with hb
  set C : ℕ → ℂ := corr n R b with hC
  -- step 1: `a = C * b`
  have hdec : ∀ m, a m = ∑ d ∈ m.divisors, C d * b (m / d) := by
    refine eq_sum_corr (by simp [ha, congruentCoeff, f32Coeff_zero])
      (by simp [ha, congruentCoeff, f32Coeff_one]) (fun u v huv ↦ ?_) (nfCoeff_zero g) (nfCoeff_one g)
      (fun u v huv ↦ nfCoeff_mul g huv) (fun p k hp hpn ↦ (nfCoeff_f32Twist_prime_pow hn hp hpn k).symm)
      (fun p k hp hpn hk ↦ ?_) (fun p j hp hpn ↦ ?_)
    · have := (isMultiplicative_congruentArith n).map_mul_of_coprime huv
      simp only [congruentArith_apply] at this
      simp [ha, this]
    · simp [ha, congruentCoeff_prime_pow_of_dvd hp (dvd_mul_of_dvd_right hpn 2) hk]
    · by_cases hpR : p ∣ R
      · simp [hb, hpR, nfCoeff_prime_pow_add_two_of_dvd g hp hpR]
      · simp only [hpR, ite_false, hb]
        exact nfCoeff_prime_pow_add_two_of_coprime g hχ hp ((Nat.Prime.coprime_iff_not_dvd hp).2 hpR) j
  have hsupp : ∀ d, C d ≠ 0 → d ∣ N' := fun d hd ↦
    dvd_of_corr_ne_zero hsq hRN (fun p hp h2 ↦ nfCoeff_prime_eq_zero_of_sq_dvd g hχ hp h2) hd
  have hcoeff : a = fun m ↦ ∑ d ∈ N'.divisors, C d * Miyake.dilate d b m := by
    funext m
    rw [hdec m, sum_divisors_eq_sum_dilate (nfCoeff_zero g) hN0.ne' hsupp m]
  -- step 2: the two Fricke relations
  have hgrowth : Miyake.CoeffGrowth b := coeffGrowth_nfCoeff g
  have hfr := fricke_sum_dilate hR0 hN0 hgrowth (fricke_qSeries_nfCoeff g hχ) C
  set ε := g.frickeSign hχ with hε
  set c' : ℕ → ℂ := fun m ↦ ∑ d ∈ N'.divisors,
    C d * (((N' / d : ℕ) : ℂ) / d) * ε * Miyake.dilate (N' / d) b m with hc'
  have hc'growth : Miyake.CoeffGrowth c' := by
    refine Miyake.coeffGrowth_finset_sum _ fun d hd ↦ ?_
    have hd0 : 0 < N' / d := Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)
    exact Miyake.coeffGrowth_const_mul _ (Miyake.coeffGrowth_dilate hd0 hgrowth)
  have hagrowth : Miyake.CoeffGrowth fun m ↦ -congruentSign n * a m :=
    Miyake.coeffGrowth_const_mul _ (coeffGrowth_congruentCoeff n)
  have heq : c' = fun m ↦ -congruentSign n * a m := by
    refine Miyake.qSeries_coeff_unique hc'growth hagrowth fun z hz ↦ ?_
    have h1 : Miyake.fricke 2 ((32 * n ^ 2 : ℕ) : ℝ) (Miyake.qSeries a) z =
        -congruentSign n * Miyake.qSeries a z := fricke_congruentCoeff hn hsq z hz
    rw [Miyake.qSeries_const_mul', ← hfr z hz, ← hcoeff, hRN, h1]
  -- step 3: the coefficient of `q`
  have h1 := congrFun heq 1
  have hsum : c' 1 = C N' * ((1 : ℂ) / N') * ε := by
    simp only [hc']
    rw [Finset.sum_eq_single N']
    · rw [Nat.div_self hN0, Miyake.dilate_one_left, hb, nfCoeff_one]
      push_cast
      ring
    · intro d hd hne
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      have hgt : 1 < N' / d := by
        obtain ⟨e, he⟩ := Nat.dvd_of_mem_divisors hd
        have he0 : e ≠ 0 := by rintro rfl; simp at he; omega
        have he1 : e ≠ 1 := by rintro rfl; exact hne (by simpa using he.symm)
        rw [he, Nat.mul_div_cancel_left _ hd0]
        omega
      rw [Miyake.dilate_one_apply _ hgt, mul_zero]
    · intro h; exact absurd (Nat.mem_divisors_self N' hN0.ne') h
  rw [hsum] at h1
  have ha1 : a 1 = 1 := by simp [ha, congruentCoeff, f32Coeff_one]
  rw [ha1, mul_one] at h1
  have hεn : ‖ε‖ = 1 := by
    rcases g.frickeSign_eq_one_or_neg_one hχ with h | h <;> simp [hε, h]
  have hsn : ‖congruentSign n‖ = 1 := by
    unfold congruentSign; split_ifs <;> simp
  have hnorm : ‖C N'‖ = N' := by
    have := congrArg norm h1
    rw [norm_mul, norm_mul, hεn, norm_neg, hsn, mul_one, norm_div, norm_one, Complex.norm_natCast] at this
    field_simp at this
    linarith
  have hle := norm_corr_sq_le (b := b) hn hsq hRN (thirtyTwo_dvd_f32TwistLevel hn)
    (fun p hp h1 h2 ↦ nfCoeff_prime_sq_of_dvd_of_not_sq_dvd g hχ hp h1 h2)
  rw [← hC, hnorm] at hle
  have hN1 : N' = 1 := by
    have : (N' : ℝ) ≤ 1 := by
      have hpos : (0 : ℝ) < N' := by exact_mod_cast hN0
      nlinarith
    exact le_antisymm (by exact_mod_cast this) hN0
  rw [hN1, mul_one] at hRN
  exact hRN

/-- **The newforms of the congruent number curves**: for odd squarefree $n$, $E_n : y^2 = x^3 - n^2x$ has the newform $f_{32} \otimes \chi_n$ of level
$32n^2$. Unconditional: the level is `f32TwistLevel_eq_of_odd`, the coefficients `hasNewform_of_level_eq`. -/
theorem hasNewform_congruentCurve {n : ℕ} [NeZero n] (hn : Odd n) (hsq : Squarefree n) :
    ∃ f : Newform (32 * n ^ 2) 2, HasNewform (congruentCurve n) (32 * n ^ 2) f :=
  hasNewform_congruentCurve_of_level_eq hn hsq (f32TwistLevel_eq_of_odd hn hsq)

end Twist

end ModularFormsKB.Elliptic
