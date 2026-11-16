/-
# The torsion of $E_n(\mathbb Q)$

**Theorem** (`two_smul_eq_zero_of_isOfFinAddOrder`; Koblitz 1984, Ch. I, Prop. 17 `koblitz1984` [unverified]).
For $n \ge 1$, every point of finite order of $E_n(\mathbb Q)$, $E_n : y^2 = x^3 - n^2x$, has order dividing $2$, so
$E_n(\mathbb Q)_{\mathrm{tors}} = \{O, (0,0), (\pm n, 0)\}$.

**Proof.** For a prime $p \equiv 3 \bmod 4$ with $p \nmid 2n$, $E_n$ has good reduction at $p$ and
$\#E_n(\mathbb F_p) = p + 1$ (the Frobenius trace vanishes: `frobeniusTrace_congruentCurveMod_twist`,
`frobeniusTrace_congruentCurveMod_one_of_three`). Reduction is injective on the torsion of order prime to $p$
(Tau Ceti `WeierstrassCurve.Affine.Point.card_torsionBy_dvd_card_reduction`), so $\#E_n(\mathbb Q)[m]$ divides
$p + 1$ for every $m$ prime to $p$. If $P$ has order $m \nmid 2$, then either an odd prime $\ell \mid m$, and a
prime $p \equiv 3 \bmod 8$, $p \equiv 1 \bmod \ell$, $p \nmid 2nm$ (Dirichlet) gives $\ell \mid p + 1 \equiv 2$; or
$4 \mid m$, and the eight points $E_n[2] + \langle (m/4)P \rangle$ of $E_n(\mathbb Q)[4]$ give $8 \mid p + 1 \equiv 4
\bmod 8$ for $p \equiv 3 \bmod 8$.

**Corollary** (`not_hasPointYNeZero_of_finite`): if $E_n(\mathbb Q)$ is finite, it has no point with $y \ne 0$. With
the rank statement of Coates–Wiles (`CoatesWilesRank`, `Criterion.lean`) this is the old input `CoatesWilesL`.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.Curve
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.PointCount
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TorsionReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralReduction
import Mathlib.NumberTheory.LSeries.PrimesInAP

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open WeierstrassCurve IsDedekindDomain

/-- The integral model $y^2 = x^3 - n^2x$ over $\mathbb Z$. -/
private def congruentCurveZ (n : ℕ) : WeierstrassCurve ℤ := ⟨0, 0, 0, -((n : ℤ) ^ 2), 0⟩

private theorem baseChange_congruentCurveZ (n : ℕ) :
    (congruentCurveZ n).baseChange ℚ = congruentCurve n := by
  ext <;> simp [congruentCurveZ, WeierstrassCurve.baseChange, congruentCurve]

private theorem map_congruentCurveZ (n p : ℕ) :
    (congruentCurveZ n).map (Int.castRingHom (ZMod p)) = congruentCurveMod n p := by
  ext <;> simp [congruentCurveZ, congruentCurveMod]

private theorem Δ_congruentCurveZ (n : ℕ) : (congruentCurveZ n).Δ = 64 * (n : ℤ) ^ 6 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, congruentCurveZ]
  ring

/-- The height-one prime $(p)$ of $\mathbb Z$. -/
private noncomputable def primeSpec (p : ℕ) [hp : Fact p.Prime] : HeightOneSpectrum ℤ :=
  ⟨Ideal.span {(p : ℤ)},
    (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp.out),
    by rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.out.ne_zero⟩

private theorem primeSpec_asIdeal (p : ℕ) [Fact p.Prime] :
    (primeSpec p).asIdeal = Ideal.span {(p : ℤ)} := rfl

private theorem natCast_mem_primeSpec_iff (p : ℕ) [Fact p.Prime] (q : ℕ) :
    (q : ℤ) ∈ (primeSpec p).asIdeal ↔ p ∣ q := by
  rw [primeSpec_asIdeal, Ideal.mem_span_singleton, Int.natCast_dvd_natCast]

private theorem card_torsion_dvd_aux {W : WeierstrassCurve ℚ} {n : ℕ} (hW : W = (congruentCurveZ n).baseChange ℚ)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpn : ¬ p ∣ n) :
    Nat.card (AddCommGroup.torsion W.toAffine.Point) ∣
      Nat.card (congruentCurveMod n p).toAffine.Point := by
  subst hW
  classical
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le; omega
  have hΔ : (congruentCurveZ n).Δ ∉ (primeSpec p).asIdeal := by
    rw [Δ_congruentCurveZ]
    have : (64 * (n : ℤ) ^ 6) = ((64 * n ^ 6 : ℕ) : ℤ) := by push_cast; ring
    rw [this, natCast_mem_primeSpec_iff]
    intro h
    rcases (Nat.Prime.dvd_mul Fact.out).mp h with h | h
    · have : p ∣ 2 ^ 6 := by simpa using h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp (Nat.Prime.dvd_of_dvd_pow Fact.out this))
    · exact hpn (Nat.Prime.dvd_of_dvd_pow Fact.out h)
  have hell := isElliptic_integralModel_baseChange (K := ℚ) (congruentCurveZ n) (primeSpec p) hΔ
  have hu : ∀ q : ℕ, q.Prime → (q : ℤ) ∉ (primeSpec p).asIdeal ^ (q - 1) := by
    intro q hq hmem
    have hq1 : q - 1 ≠ 0 := by have := hq.two_le; omega
    have hmem' : (q : ℤ) ∈ (primeSpec p).asIdeal := Ideal.pow_le_self hq1 hmem
    rw [natCast_mem_primeSpec_iff] at hmem'
    have hqp : q = p := ((Nat.prime_dvd_prime_iff_eq Fact.out hq).mp hmem').symm
    subst hqp
    rw [primeSpec_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    have h1 : q ^ (q - 1) ∣ q := by exact_mod_cast hmem
    have h2 := Nat.le_of_dvd hq.pos h1
    have h3 : q ^ 2 ≤ q ^ (q - 1) := Nat.pow_le_pow_right hq.pos (by omega)
    nlinarith
  have := Affine.Point.card_torsion_dvd_card_reduction (W := (congruentCurveZ n).baseChange ℚ) (primeSpec p) hu
  rw [card_point_reduction_baseChange (congruentCurveZ n) (primeSpec p) p rfl,
    map_congruentCurveZ] at this
  exact this

private theorem not_dvd_aux {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ} (hpn : ¬ p ∣ n) :
    ¬ p ∣ 64 * n ^ 6 := by
  intro h
  rcases (Nat.Prime.dvd_mul Fact.out).mp h with h | h
  · have : p ∣ 2 ^ 6 := by simpa using h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Fact.out this))
  · exact hpn (Nat.Prime.dvd_of_dvd_pow Fact.out h)

private theorem card_point_congruentCurveMod (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) {n : ℕ}
    (hpn : ¬ p ∣ n) : Nat.card (congruentCurveMod n p).toAffine.Point = p + 1 := by
  have hp2 : p ≠ 2 := by omega
  have hell : (congruentCurveMod n p).IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
    have : (congruentCurveMod n p).Δ = ((64 * n ^ 6 : ℕ) : ZMod p) := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
        WeierstrassCurve.b₈, congruentCurveMod]
      push_cast; ring
    rw [this, Ne, ZMod.natCast_eq_zero_iff]
    exact not_dvd_aux hp2 hpn
  have h0 : (congruentCurveMod n p).frobeniusTrace = 0 := by
    rw [frobeniusTrace_congruentCurveMod_twist hp2 hpn, frobeniusTrace_congruentCurveMod_one_of_three hp4,
      mul_zero]
  rw [WeierstrassCurve.frobeniusTrace_eq_card_point, Nat.card_zmod] at h0
  omega

private theorem card_torsion_dvd {n : ℕ} (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) (hpn : ¬ p ∣ n) :
    Nat.card (AddCommGroup.torsion (congruentCurve n).toAffine.Point) ∣ p + 1 := by
  have := card_torsion_dvd_aux (W := congruentCurve n) (baseChange_congruentCurveZ n).symm p
    (by omega) hpn
  rwa [card_point_congruentCurveMod p hp4 hpn] at this

/-- **The torsion of $E_n(\mathbb Q)$ is $E_n[2]$** (row 12). -/
theorem two_smul_eq_zero_of_isOfFinAddOrder {n : ℕ} (hn : 0 < n)
    {P : (congruentCurve n).toAffine.Point} (hP : IsOfFinAddOrder P) : (2 : ℤ) • P = 0 := by
  have : NeZero n := ⟨hn.ne'⟩
  set T := AddCommGroup.torsion (congruentCurve n).toAffine.Point with hT
  -- Step 1: `|T|` divides `p + 1` for all primes `p ≡ 3 mod 4` with `p > n`
  have hdvd : ∀ p : ℕ, p.Prime → p % 4 = 3 → n < p → Nat.card T ∣ p + 1 := by
    intro p hp hp4 hnp
    have : Fact p.Prime := ⟨hp⟩
    refine card_torsion_dvd p hp4 fun h => ?_
    exact absurd (Nat.le_of_dvd hn h) (by omega)
  obtain ⟨p0, hp0, hp0p, hp04⟩ : ∃ p, n < p ∧ p.Prime ∧ p % 4 = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨p, hp, hpp, hpm⟩ := Nat.forall_exists_prime_gt_and_eq_mod (q := 4) (a := 3)
      (by decide) n
    refine ⟨p, hp, hpp, ?_⟩
    have := (ZMod.natCast_eq_natCast_iff p 3 4).mp (by simpa using hpm)
    exact this
  have hN0 : Nat.card T ≠ 0 := by
    intro h0
    have := hdvd p0 hp0p hp04 hp0
    rw [h0, zero_dvd_iff] at this
    omega
  have hfin : Finite T := Nat.finite_of_card_ne_zero hN0
  -- Step 2: `|T|` divides `4`
  obtain ⟨a, m, hm, hNm⟩ := Nat.exists_eq_two_pow_mul_odd hN0
  have hr : ∃ r : ℕ, r ≡ 3 [MOD 8] ∧ r ≡ 1 [MOD m] := by
    have hcop : Nat.Coprime 8 m := by simpa using Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hm)
    obtain ⟨r, h1, h2⟩ := Nat.chineseRemainder hcop 3 1
    exact ⟨r, h1, h2⟩
  obtain ⟨r, hr8, hrm⟩ := hr
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have : NeZero (8 * m) := ⟨by positivity⟩
  have hunit : IsUnit (r : ZMod (8 * m)) := by
    rw [ZMod.isUnit_iff_coprime]
    refine Nat.Coprime.mul_right ?_ ?_
    · have := hr8.gcd_eq
      simpa [Nat.Coprime] using this
    · have := hrm.gcd_eq
      simpa [Nat.Coprime, Nat.gcd_comm m] using this
  obtain ⟨p, hpgt, hpp, hpr⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit n
  have hpr' : p ≡ r [MOD 8 * m] := (ZMod.natCast_eq_natCast_iff p r (8 * m)).mp hpr
  have hp8 : p ≡ 3 [MOD 8] := (hpr'.of_mul_right m).trans hr8
  have hpm : p ≡ 1 [MOD m] := (hpr'.of_mul_left 8).trans hrm
  have hp8' : p % 8 = 3 := hp8
  have hNp := hdvd p hpp (by omega) hpgt
  have hm1 : m = 1 := by
    have h1 : m ∣ p + 1 := (Dvd.intro_left _ hNm.symm).trans hNp
    have h2 : p + 1 ≡ 2 [MOD m] := hpm.add_right 1
    have h3 : m ∣ 2 := by
      have := h2.symm.trans ((Nat.modEq_zero_iff_dvd.mpr h1))
      exact Nat.modEq_zero_iff_dvd.mp this
    have := Nat.le_of_dvd (by norm_num) h3
    obtain ⟨k, hk⟩ := hm
    omega
  have ha2 : a ≤ 2 := by
    by_contra hlt
    have h8 : 8 ∣ 2 ^ a := by
      have : 2 ^ 3 ∣ 2 ^ a := Nat.pow_dvd_pow 2 (by omega)
      simpa using this
    have : 8 ∣ p + 1 := by
      refine h8.trans ?_
      rw [hm1, mul_one] at hNm
      exact hNm ▸ hNp
    omega
  have hN4 : Nat.card T ∣ 4 := by
    rw [hNm, hm1, mul_one]
    interval_cases a <;> norm_num
  -- Step 3: the four points `O, (0,0), (n,0), (-n,0)` lie in `T`
  have hnz : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hns : ∀ x : ℚ, x ^ 3 - (n : ℚ) ^ 2 * x = 0 → (congruentCurve n).toAffine.Nonsingular x 0 := by
    intro x hx
    exact (WeierstrassCurve.Affine.equation_iff_nonsingular).1
      ((congruentCurve_equation_iff n x 0).2 (by rw [hx]; ring))
  let P1 : (congruentCurve n).toAffine.Point := .some 0 0 (hns 0 (by ring))
  let P2 : (congruentCurve n).toAffine.Point := .some (n : ℚ) 0 (hns n (by ring))
  let P3 : (congruentCurve n).toAffine.Point := .some (-(n : ℚ)) 0 (hns (-n) (by ring))
  obtain ⟨S, hSdef⟩ : ∃ S : Finset (congruentCurve n).toAffine.Point, S = {0, P1, P2, P3} :=
    ⟨_, rfl⟩
  have hS : ∀ Q ∈ S, (2 : ℤ) • Q = 0 := by
    intro Q hQ
    rw [hSdef] at hQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
    rcases hQ with rfl | rfl | rfl | rfl
    · exact smul_zero (A := (congruentCurve n).toAffine.Point) (2 : ℤ)
    all_goals exact two_smul_eq_zero_of_y_eq_zero _ rfl
  have hmemT : ∀ Q : (congruentCurve n).toAffine.Point, (2 : ℤ) • Q = 0 → Q ∈ T := by
    intro Q hQ
    rw [hT, AddCommGroup.mem_torsion]
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2, by norm_num, ?_⟩
    rw [two_nsmul]
    rwa [two_zsmul] at hQ
  have hcard : S.card = 4 := by
    have e1 : (0 : (congruentCurve n).toAffine.Point) ≠ P1 := by simp [P1]
    have e2 : (0 : (congruentCurve n).toAffine.Point) ≠ P2 := by simp [P2]
    have e3 : (0 : (congruentCurve n).toAffine.Point) ≠ P3 := by simp [P3]
    have e4 : P1 ≠ P2 := by simp [P1, P2, hnz.symm]
    have e5 : P1 ≠ P3 := by simp [P1, P3, hn.ne']
    have e6 : P2 ≠ P3 := by
      simp only [P2, P3, ne_eq, WeierstrassCurve.Affine.Point.some.injEq, and_true]
      intro h
      apply hnz
      linarith
    rw [hSdef, Finset.card_insert_of_notMem (by simp [e1, e2, e3]),
      Finset.card_insert_of_notMem (by simp [e4, e5]), Finset.card_insert_of_notMem (by simp [e6])]
    rfl
  have hsub : (S : Set (congruentCurve n).toAffine.Point) ⊆ (T : Set _) :=
    fun Q hQ => hmemT Q (hS Q hQ)
  have hTfin : (T : Set (congruentCurve n).toAffine.Point).Finite := Set.toFinite _
  have hle : (T : Set (congruentCurve n).toAffine.Point).ncard ≤
      (S : Set (congruentCurve n).toAffine.Point).ncard := by
    rw [Set.ncard_coe_finset, hcard, ← Nat.card_coe_set_eq]
    exact Nat.le_of_dvd (by norm_num) hN4
  have heq := Set.eq_of_subset_of_ncard_le hsub hle hTfin
  have hPT : P ∈ (T : Set (congruentCurve n).toAffine.Point) := by
    rw [hT, SetLike.mem_coe, AddCommGroup.mem_torsion]; exact hP
  rw [← heq] at hPT
  exact hS P hPT

/-- **A finite $E_n(\mathbb Q)$ has no point with $y \ne 0$** (row 12). -/
theorem not_hasPointYNeZero_of_finite {n : ℕ} (hn : 0 < n)
    (hfin : Finite (congruentCurve n).toAffine.Point) : ¬ Tunnell.HasPointYNeZero n := by
  have : NeZero n := ⟨hn.ne'⟩
  rw [hasPointYNeZero_iff_exists_point]
  rintro ⟨x, y, h, hy, -⟩
  have h2 := two_smul_eq_zero_of_isOfFinAddOrder hn
    (isOfFinAddOrder_of_finite (WeierstrassCurve.Affine.Point.some x y h))
  rw [two_zsmul] at h2
  have h3 := eq_neg_of_add_eq_zero_left h2
  rw [WeierstrassCurve.Affine.Point.neg_some] at h3
  have h4 := (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _ |>.mp h3).2
  apply hy
  simp [WeierstrassCurve.Affine.negY] at h4
  linarith

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
