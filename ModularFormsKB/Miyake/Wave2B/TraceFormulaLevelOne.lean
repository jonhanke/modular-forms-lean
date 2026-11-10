import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.EichlerSelberg
import TauCeti.RingTheory.Polynomial.Dickson
import Mathlib.Basic.Real.Sign
import ModularFormsKB.Citation
/-!
# Miyake Theorem 6.8.4 at level one ($B = M_2(\mathbb Q)$, $N = 1$, trivial character)

Miyake, *Modular Forms* (Springer 1989), Theorem 6.8.4 and Remark 6.8.2, pp. 262–265.

For $B = M_2(\mathbb Q)$ we have $d_B = 1$ and $\Gamma_R = \Gamma_0(N)$, and $T(n)$ is the Hecke operator
of §4.5 (Remark 6.8.2). For $N = 1$ and trivial $\chi$ Miyake's formula reads
$$\operatorname{tr} T(n) = \delta(n)\,\frac{k-1}{12}\,n^{k/2-1}
  - \sum_t a(t) \sum_{f \mid m} b(t,f),$$
where $\delta(n) = 1$ if $n$ is a square and $0$ otherwise, $t$ runs over the integers with
$t^2 - 4n$ negative or a square, $\zeta,\eta$ are the roots of $X^2 - tX + n$,
$t^2 - 4n = m^2 d$, and ($c(t,f) = 1$ since $N = 1$):

* $t^2 < 4n$ (elliptic): $a(t) = (\zeta^{k-1} - \eta^{k-1})/(\zeta - \eta)$ and
  $\sum_{f \mid m} b(t,f) = \sum_{f\mid m} \frac{h(d)}{w(d)}\,f\prod_{p\mid f}(1 - (\tfrac dp)p^{-1})
  = \sum_{f \mid m} h(f^2 d)/w(f^2 d)$ (by Theorem 6.7.2, see p. 259);
* $t^2 - 4n = m^2 > 0$ (hyperbolic, $d = 1$): $a(t) = \frac12 \min(|\zeta|,|\eta|)^{k-1}
  |\zeta - \eta|^{-1}\operatorname{sgn}(\zeta)^k$ and $b(t,f) = \varphi(f)$;
* $t^2 = 4n$ (parabolic, $d = 0$): $a(t) = \frac14\operatorname{sgn}(t)^k n^{(k-1)/2}$, $m = 1$,
  $b = 1$.

**What is proved here.** `trace_T_levelOne` is this formula for even $k \ge 4$, derived from Tau
Ceti's Eichler–Selberg trace formula (Popa–Zagier's proof,
`TauCeti.trace_heckeTCuspLevelOne_eq_neg_hurwitzClassNumber_sub_min`), with one substitution: the
elliptic class-number factor $\sum_{f\mid m} h(f^2d)/w(f^2d)$ is written as $H(4n - t^2)/2$ with
the Hurwitz class number $H$ (Tau Ceti `TauCeti.hurwitzClassNumber`, a weighted count of reduced
binary quadratic forms). The identity $\sum_{f \mid m} h(f^2 d)/w(f^2 d) = H(m^2|d|)/2$ is the
classical correspondence between classes of primitive forms of discriminant $f^2 d$ and proper
ideal classes of the order of conductor $f$ (weights $1/2$, $1/3$ for the forms with extra
automorphisms matching $2/w$); it is not formalized here. Miyake's analytic proof (§6.1–6.4) is
not followed: the level-one formula is imported from Popa–Zagier's algebraic proof.
-/

open Complex Polynomial

noncomputable section

namespace ModularFormsKB.Miyake.Wave2B

/-- The root $\zeta = (t + i\sqrt{4n - t^2})/2$ of $X^2 - tX + n$ in the elliptic case
$t^2 < 4n$ (the other root is $\eta = \bar\zeta$). -/
def ellRoot (t : ℤ) (n : ℕ) : ℂ :=
  ((t : ℂ) + I * (Real.sqrt (4 * n - t ^ 2) : ℂ)) / 2

/-- Miyake's $a(t)$ in the elliptic case: $(\zeta^{k-1} - \eta^{k-1})/(\zeta - \eta)$ with
$\eta = \bar\zeta$. -/
def aEll (k : ℕ) (t : ℤ) (n : ℕ) : ℂ :=
  (ellRoot t n ^ (k - 1) - starRingEnd ℂ (ellRoot t n) ^ (k - 1)) /
    (ellRoot t n - starRingEnd ℂ (ellRoot t n))

/-- Miyake's $a(t)$ in the hyperbolic case $t^2 - 4n = m^2 > 0$, with real roots
$\zeta, \eta = (t \pm m)/2$:
$\frac12\min(|\zeta|,|\eta|)^{k-1}\,|\zeta - \eta|^{-1}\operatorname{sgn}(\zeta)^k$. -/
def aHyp (k : ℕ) (t : ℤ) (m : ℕ) : ℝ :=
  let ζ : ℝ := (t + m) / 2
  let η : ℝ := (t - m) / 2
  1 / 2 * min |ζ| |η| ^ (k - 1) / |ζ - η| * Real.sign ζ ^ k

/-- Miyake's $a(t)$ in the parabolic case $t^2 = 4n$: $\frac14 \operatorname{sgn}(t)^k n^{(k-1)/2}$
(trivial character). -/
def aPar (k : ℕ) (t : ℤ) (n : ℕ) : ℝ :=
  1 / 4 * Real.sign (t : ℝ) ^ k * (n : ℝ) ^ (((k : ℝ) - 1) / 2)

/-- The integers $t$ with $t^2 < 4n$. -/
def ellipticTs (n : ℕ) : Finset ℤ :=
  (Finset.Icc (-2 * (n : ℤ)) (2 * n)).filter fun t ↦ t ^ 2 < 4 * (n : ℤ)

/-- The integers $t$ with $t^2 - 4n$ a positive square $m^2$, paired with $m > 0$. -/
def hyperbolicTs (n : ℕ) : Finset (ℤ × ℕ) :=
  ((Finset.Icc (-(n : ℤ) - 1) (n + 1)) ×ˢ Finset.range (n + 1)).filter
    fun p ↦ 0 < p.2 ∧ p.1 ^ 2 - 4 * (n : ℤ) = (p.2 : ℤ) ^ 2

/-- The integers $t$ with $t^2 = 4n$. -/
def parabolicTs (n : ℕ) : Finset ℤ :=
  (Finset.Icc (-2 * (n : ℤ)) (2 * n)).filter fun t ↦ t ^ 2 = 4 * (n : ℤ)

/-- In the elliptic case the Dickson value is Miyake's $a(t)$ (with $w = k - 2$). -/
theorem dickson_eval_eq_aEll {k : ℕ} (hk : 2 ≤ k) {t : ℤ} {n : ℕ} (ht : t ^ 2 < 4 * (n : ℤ)) :
    (dickson 2 (n : ℂ) (k - 2)).eval (t : ℂ) = aEll k t n := by
  have hpos : (0 : ℝ) < 4 * n - (t : ℝ) ^ 2 := by
    have : ((t ^ 2 : ℤ) : ℝ) < ((4 * (n : ℤ) : ℤ) : ℝ) := by exact_mod_cast ht
    push_cast at this; linarith
  set s : ℝ := Real.sqrt (4 * n - (t : ℝ) ^ 2) with hs
  have hs2 : s ^ 2 = 4 * n - (t : ℝ) ^ 2 := Real.sq_sqrt hpos.le
  have hs0 : s ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hs2c : (s : ℂ) ^ 2 = 4 * n - (t : ℂ) ^ 2 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hs2
    push_cast at this; exact this
  have hconj : starRingEnd ℂ (ellRoot t n) = ((t : ℂ) - I * (s : ℂ)) / 2 := by
    unfold ellRoot
    have h2 : starRingEnd ℂ (2 : ℂ) = 2 := map_ofNat _ 2
    rw [map_div₀, map_add, map_mul, map_intCast, Complex.conj_I, Complex.conj_ofReal, h2]
    ring
  have hsum : ellRoot t n + starRingEnd ℂ (ellRoot t n) = (t : ℂ) := by
    rw [hconj]; unfold ellRoot; ring
  have hprod : ellRoot t n * starRingEnd ℂ (ellRoot t n) = (n : ℂ) := by
    rw [hconj]; unfold ellRoot
    linear_combination (-(s : ℂ) ^ 2 / 4) * Complex.I_sq + (1 / 4 : ℂ) * hs2c
  have hne : ellRoot t n ≠ starRingEnd ℂ (ellRoot t n) := by
    intro h
    rw [hconj] at h; unfold ellRoot at h
    have : I * (s : ℂ) = 0 := by linear_combination h
    simp [Complex.I_ne_zero, hs0] at this
  have := dickson_two_eval_add_eq_div hprod hne (k - 2)
  rw [hsum] at this
  rw [this]
  unfold aEll
  have e : k - 2 + 1 = k - 1 := by omega
  rw [e]

/-- The sum range of the Tau Ceti trace formula is the disjoint union of the elliptic and
parabolic ranges. -/
theorem filter_sq_le_eq (n : ℕ) [NeZero n] :
    (Finset.Icc (-4 * (n : ℤ)) (4 * n)).filter (fun t ↦ t ^ 2 ≤ 4 * (n : ℤ)) =
      ellipticTs n ∪ parabolicTs n := by
  have hn : 1 ≤ (n : ℤ) := by have := Nat.pos_of_ne_zero (NeZero.ne n); omega
  ext t
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, ellipticTs, parabolicTs]
  constructor
  · rintro ⟨_, h⟩
    have hb : -2 * (n : ℤ) ≤ t ∧ t ≤ 2 * n := by
      constructor
      · by_contra hc; push_neg at hc; nlinarith
      · by_contra hc; push_neg at hc; nlinarith
    rcases lt_or_eq_of_le h with h | h
    · left; exact ⟨hb, h⟩
    · right; exact ⟨hb, h⟩
  · rintro (⟨hb, h⟩ | ⟨hb, h⟩)
    · exact ⟨⟨by omega, by omega⟩, h.le⟩
    · exact ⟨⟨by omega, by omega⟩, h.le⟩

theorem disjoint_ellipticTs_parabolicTs (n : ℕ) : Disjoint (ellipticTs n) (parabolicTs n) := by
  rw [Finset.disjoint_left]
  intro t h1 h2
  simp only [ellipticTs, parabolicTs, Finset.mem_filter] at h1 h2
  omega

/-- No parabolic `t` unless `n` is a square. -/
theorem parabolicTs_of_not_square {n : ℕ} (hn : ¬ IsSquare n) : parabolicTs n = ∅ := by
  ext t
  simp only [parabolicTs, Finset.mem_filter, Finset.notMem_empty, iff_false]
  rintro ⟨_, h⟩
  apply hn
  rcases Int.even_or_odd' t with ⟨u, rfl | rfl⟩
  · refine ⟨u.natAbs, ?_⟩
    have h2 : ((u.natAbs : ℕ) : ℤ) * (u.natAbs : ℤ) = u * u := Int.natAbs_mul_self' u
    have : (n : ℤ) = u * u := by nlinarith
    exact_mod_cast this.trans h2.symm
  · exfalso
    have : (2 * u + 1) ^ 2 = 4 * (u ^ 2 + u) + 1 := by ring
    omega

/-- The parabolic `t` for `n = s²`. -/
theorem parabolicTs_of_square {n s : ℕ} (hs : 0 < s) (h : n = s * s) :
    parabolicTs n = {2 * (s : ℤ), -(2 * (s : ℤ))} := by
  ext t
  simp only [parabolicTs, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton]
  subst h
  have hs1 : (1 : ℤ) ≤ s := by exact_mod_cast hs
  constructor
  · rintro ⟨_, ht⟩
    have : t ^ 2 = (2 * (s : ℤ)) ^ 2 := by push_cast at ht; nlinarith
    exact sq_eq_sq_iff_eq_or_eq_neg.mp this
  · rintro (rfl | rfl)
    · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> push_cast <;> nlinarith
    · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> push_cast <;> nlinarith

theorem diag_of_not_square {n : ℕ} (hn : ¬ IsSquare n) :
    n.divisorsAntidiagonal.filter (fun p : ℕ × ℕ ↦ p.1 = p.2) = ∅ := by
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal, Finset.notMem_empty, iff_false]
  rintro ⟨⟨h, _⟩, rfl⟩
  exact hn ⟨a, h.symm⟩

theorem diag_of_square {n s : ℕ} (hs : 0 < s) (h : n = s * s) :
    n.divisorsAntidiagonal.filter (fun p : ℕ × ℕ ↦ p.1 = p.2) = {(s, s)} := by
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal, Finset.mem_singleton,
    Prod.mk.injEq]
  subst h
  constructor
  · rintro ⟨⟨h1, _⟩, rfl⟩
    have := Nat.mul_self_inj.mp h1
    exact ⟨this, this⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨rfl, by positivity⟩, rfl⟩

/-- The map from ordered off-diagonal factor pairs to hyperbolic pairs `(t, m)`. -/
def hypOf (p : ℕ × ℕ) : ℤ × ℕ :=
  if p.1 < p.2 then (((p.1 + p.2 : ℕ) : ℤ), p.2 - p.1) else (-((p.1 + p.2 : ℕ) : ℤ), p.1 - p.2)

theorem hypTerm_lt {k : ℕ} {a b : ℕ} (hab : a < b) :
    (aHyp k ((a + b : ℕ) : ℤ) (b - a) : ℝ) * ((b - a : ℕ) : ℝ) = 1 / 2 * (a : ℝ) ^ (k - 1) := by
  have hba : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := Nat.cast_sub hab.le
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have h1 : (((a + b : ℕ) : ℤ) : ℝ) = a + b := by push_cast; ring
  have e1 : ((a : ℝ) + b + (b - a)) / 2 = b := by ring
  have e2 : ((a : ℝ) + b - (b - a)) / 2 = a := by ring
  have hb0 : (0 : ℝ) < b := lt_of_le_of_lt (Nat.cast_nonneg a) hab'
  simp only [aHyp, h1, hba, e1, e2]
  rw [abs_of_pos hb0, abs_of_nonneg (Nat.cast_nonneg a), min_eq_right hab'.le,
    abs_of_pos (sub_pos.2 hab'), Real.sign_of_pos hb0, one_pow]
  have : (b : ℝ) - a ≠ 0 := (sub_pos.2 hab').ne'
  field_simp

theorem hypTerm_gt {k : ℕ} (hke : Even k) {a b : ℕ} (hb : 0 < b) (hab : b < a) :
    (aHyp k (-((a + b : ℕ) : ℤ)) (a - b) : ℝ) * ((a - b : ℕ) : ℝ) = 1 / 2 * (b : ℝ) ^ (k - 1) := by
  have hba : ((a - b : ℕ) : ℝ) = (a : ℝ) - b := Nat.cast_sub hab.le
  have hab' : (b : ℝ) < a := by exact_mod_cast hab
  have h1 : ((-((a + b : ℕ) : ℤ) : ℤ) : ℝ) = -(a + b) := by push_cast; ring
  have e1 : (-((a : ℝ) + b) + (a - b)) / 2 = -b := by ring
  have e2 : (-((a : ℝ) + b) - (a - b)) / 2 = -a := by ring
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have ha0 : (0 : ℝ) < a := lt_of_le_of_lt (Nat.cast_nonneg b) hab'
  simp only [aHyp, h1, hba, e1, e2]
  have hmin : min |-(b : ℝ)| |-(a : ℝ)| = b := by
    rw [abs_neg, abs_neg, abs_of_nonneg (Nat.cast_nonneg b), abs_of_pos ha0, min_eq_left hab'.le]
  have habs : |-(b : ℝ) - -(a : ℝ)| = a - b := by
    rw [show -(b : ℝ) - -(a : ℝ) = a - b by ring, abs_of_pos (sub_pos.2 hab')]
  have hsg : Real.sign (-(b : ℝ)) ^ k = 1 := by
    rw [Real.sign_of_neg (neg_neg_of_pos hb0), hke.neg_one_pow]
  rw [hmin, habs, hsg]
  have : (a : ℝ) - b ≠ 0 := (sub_pos.2 hab').ne'
  field_simp

theorem hypOf_inj {p q : ℕ × ℕ} (h : hypOf p = hypOf q) : p = q := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  unfold hypOf at h
  simp only [Prod.mk.injEq] at h ⊢
  split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> omega

theorem hypOf_mem {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ n.divisorsAntidiagonal) (hne : ¬ p.1 = p.2) :
    hypOf p ∈ hyperbolicTs n := by
  obtain ⟨a, b⟩ := p
  rw [Nat.mem_divisorsAntidiagonal] at hp
  obtain ⟨hab, hn⟩ := hp
  simp only at hab hne
  have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hab; exact hn hab.symm)
  have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hab; exact hn hab.symm)
  have hz : (a : ℤ) * b = n := by exact_mod_cast hab
  have ha1 : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb1 : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hsum : (a : ℤ) + b ≤ n + 1 := by nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hb1)]
  have hbn : (b : ℤ) ≤ n := by nlinarith
  have han : (a : ℤ) ≤ n := by nlinarith
  unfold hypOf
  simp only [hyperbolicTs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_range]
  split_ifs with h
  · have hc : (((b - a : ℕ)) : ℤ) = (b : ℤ) - a := by omega
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
    · push_cast; omega
    · push_cast; omega
    · omega
    · omega
    · rw [hc]; push_cast; linear_combination 4 * hz
  · have h' : b < a := by omega
    have hc : (((a - b : ℕ)) : ℤ) = (a : ℤ) - b := by omega
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
    · push_cast; omega
    · push_cast; omega
    · omega
    · omega
    · rw [hc]; push_cast; linear_combination 4 * hz

theorem hypOf_surj {n : ℕ} (hn : 0 < n) {q : ℤ × ℕ} (hq : q ∈ hyperbolicTs n) :
    ∃ p ∈ n.divisorsAntidiagonal.filter (fun p : ℕ × ℕ ↦ ¬ p.1 = p.2), hypOf p = q := by
  obtain ⟨t, m⟩ := q
  simp only [hyperbolicTs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_range] at hq
  obtain ⟨_, hm, h⟩ := hq
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hpar : (t + m) % 2 = 0 := by
    rcases Int.even_or_odd' t with ⟨u, hu | hu⟩ <;>
      rcases Int.even_or_odd' (m : ℤ) with ⟨v, hv | hv⟩ <;>
      · rw [hu, hv] at h ⊢
        ring_nf at h
        omega
  obtain ⟨c, hc⟩ : ∃ c : ℤ, t + m = 2 * c := ⟨(t + m) / 2, by omega⟩
  have hcn : c * (c - m) = n := by
    have : t = 2 * c - m := by omega
    subst this
    nlinarith
  have hpos : 0 < c * (c - m) := by rw [hcn]; exact hn'
  rcases mul_pos_iff.mp hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨A, hA⟩ : ∃ A : ℕ, (A : ℤ) = c - m := ⟨(c - m).toNat, Int.toNat_of_nonneg h2.le⟩
    obtain ⟨B, hB⟩ : ∃ B : ℕ, (B : ℤ) = c := ⟨c.toNat, Int.toNat_of_nonneg h1.le⟩
    have hAB : A * B = n := by
      have : (A : ℤ) * B = n := by rw [hA, hB]; linarith
      exact_mod_cast this
    have hlt : A < B := by omega
    refine ⟨(A, B), ?_, ?_⟩
    · rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
      exact ⟨⟨hAB, hn.ne'⟩, by simp only; omega⟩
    · simp only [hypOf, hlt, ite_true, Prod.mk.injEq]
      constructor
      · push_cast; omega
      · omega
  · obtain ⟨A, hA⟩ : ∃ A : ℕ, (A : ℤ) = m - c := ⟨(m - c).toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨B, hB⟩ : ∃ B : ℕ, (B : ℤ) = -c := ⟨(-c).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hAB : A * B = n := by
      have : (A : ℤ) * B = n := by rw [hA, hB]; linarith
      exact_mod_cast this
    have hlt : B < A := by omega
    refine ⟨(A, B), ?_, ?_⟩
    · rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
      exact ⟨⟨hAB, hn.ne'⟩, by simp only; omega⟩
    · have : ¬ A < B := by omega
      simp only [hypOf, this, ite_false, Prod.mk.injEq]
      constructor
      · push_cast; omega
      · omega

/-- The hyperbolic sum rewritten over ordered off-diagonal factor pairs. -/
theorem hyp_sum_eq {k : ℕ} (hke : Even k) {n : ℕ} (hn : 0 < n) :
    ∑ p ∈ hyperbolicTs n, (aHyp k p.1 p.2 : ℂ) * ∑ f ∈ p.2.divisors, (f.totient : ℂ) =
      ∑ p ∈ n.divisorsAntidiagonal.filter (fun p : ℕ × ℕ ↦ ¬ p.1 = p.2),
        (1 / 2 : ℂ) * ((min p.1 p.2 : ℕ) : ℂ) ^ (k - 1) := by
  symm
  refine (Finset.sum_bij (fun p _ ↦ hypOf p) ?_ ?_ ?_ ?_)
  · intro p hp
    rw [Finset.mem_filter] at hp
    exact hypOf_mem hp.1 hp.2
  · intro p _ q _ h
    exact hypOf_inj h
  · intro q hq
    obtain ⟨p, hp, h⟩ := hypOf_surj hn hq
    exact ⟨p, hp, h⟩
  · intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨a, b⟩ := p
    have hne : a ≠ b := hp.2
    have hb : 0 < b := by
      have := (Nat.mem_divisorsAntidiagonal.mp hp.1).1
      have h2 := (Nat.mem_divisorsAntidiagonal.mp hp.1).2
      exact Nat.pos_of_ne_zero (by rintro rfl; simp at this; exact h2 this.symm)
    have hsum : ∀ m : ℕ, ∑ f ∈ m.divisors, (f.totient : ℂ) = (m : ℂ) := fun m ↦ by
      rw [← Nat.cast_sum, Nat.sum_totient]
    rcases lt_or_gt_of_ne hne with h | h
    · have e := hypTerm_lt (k := k) h
      simp only [hypOf, h, ite_true, hsum]
      rw [min_eq_left h.le]
      have := congrArg (fun x : ℝ ↦ (x : ℂ)) e
      push_cast at this ⊢
      linear_combination -this
    · have e := hypTerm_gt (k := k) hke hb h
      have h' : ¬ a < b := by omega
      simp only [hypOf, h', ite_false, hsum]
      rw [min_eq_right h.le]
      have := congrArg (fun x : ℝ ↦ (x : ℂ)) e
      push_cast at this ⊢
      linear_combination -this

theorem aPar_sq {k s : ℕ} (hke : Even k) (hk : 1 ≤ k) (hs : 0 < s) {ε : ℤ}
    (hε : ε = 2 * (s : ℤ) ∨ ε = -(2 * (s : ℤ))) :
    aPar k ε (s * s) = 1 / 4 * (s : ℝ) ^ (k - 1) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hr : ((s * s : ℕ) : ℝ) ^ (((k : ℝ) - 1) / 2) = (s : ℝ) ^ (k - 1) := by
    have : ((s * s : ℕ) : ℝ) = (s : ℝ) ^ (2 : ℝ) := by
      rw [Real.rpow_two]; push_cast; ring
    rw [this, ← Real.rpow_mul hs0.le]
    have : (2 : ℝ) * (((k : ℝ) - 1) / 2) = ((k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hk]; push_cast; ring
    rw [this, Real.rpow_natCast]
  have hsg : Real.sign (ε : ℝ) ^ k = 1 := by
    rcases hε with rfl | rfl
    · rw [Real.sign_of_pos (by push_cast; positivity), one_pow]
    · rw [Real.sign_of_neg (by push_cast; simp; exact hs), hke.neg_one_pow]
  unfold aPar
  rw [hsg, hr]; ring

/-- **Miyake, Theorem 6.8.4 (with Remark 6.8.2), for $B = M_2(\mathbb Q)$, $N = 1$, trivial
character, even $k \ge 4$.** The trace of $T(n)$ on $S_k(SL_2(\mathbb Z))$ is
$$\delta(n)\frac{k-1}{12}n^{k/2-1}
 - \sum_{t^2<4n} a(t)\,\frac{H(4n-t^2)}{2}
 - \sum_{t^2-4n=m^2>0} a(t)\sum_{f\mid m}\varphi(f)
 - \sum_{t^2=4n} a(t),$$
where the elliptic factor $H(4n-t^2)/2$ stands for Miyake's $\sum_{f\mid m} b(t,f)$ (see the
module docstring). -/
@[kb "miyake1989" "Theorem 6.8.4, p. 263 (B = M2(Q), N = 1, chi trivial)"]
theorem trace_T_levelOne {k : ℕ} (hk : 4 ≤ k) (hke : Even k) (n : ℕ) [NeZero n] :
    LinearMap.trace ℂ _ (TauCeti.heckeTCuspLevelOne (k : ℤ) n) =
      (if IsSquare n then ((k : ℂ) - 1) / 12 * (n : ℂ) ^ (k / 2 - 1) else 0)
      - ∑ t ∈ ellipticTs n, aEll k t n * ((TauCeti.hurwitzClassNumber (4 * n - t ^ 2).toNat : ℂ) / 2)
      - ∑ p ∈ hyperbolicTs n, (aHyp k p.1 p.2 : ℂ) * ∑ f ∈ p.2.divisors, (f.totient : ℂ)
      - ∑ t ∈ parabolicTs n, (aPar k t n : ℂ) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hk2 : 2 ≤ k := by omega
  have hw : Even (k - 2) := by obtain ⟨r, hr⟩ := hke; exact ⟨r - 1, by omega⟩
  have hTC := TauCeti.trace_heckeTCuspLevelOne_eq_neg_hurwitzClassNumber_sub_min
    (k := (k : ℤ)) (w := k - 2) (by omega) hw (by omega) n
  have hexp : k - 2 + 1 = k - 1 := by omega
  rw [hexp] at hTC
  rw [hTC, filter_sq_le_eq, Finset.sum_union (disjoint_ellipticTs_parabolicTs n),
    ← Finset.sum_filter_add_sum_filter_not n.divisorsAntidiagonal (fun p : ℕ × ℕ ↦ p.1 = p.2),
    hyp_sum_eq hke hn0]
  have hell : ∑ t ∈ ellipticTs n, (TauCeti.hurwitzClassNumber (4 * (n : ℤ) - t ^ 2).toNat : ℂ) *
        (dickson 2 (n : ℂ) (k - 2)).eval (t : ℂ) =
      2 * ∑ t ∈ ellipticTs n, aEll k t n *
        ((TauCeti.hurwitzClassNumber (4 * n - t ^ 2).toNat : ℂ) / 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    have ht' : t ^ 2 < 4 * (n : ℤ) := by
      simp only [ellipticTs, Finset.mem_filter] at ht; exact ht.2
    rw [dickson_eval_eq_aEll hk2 ht']; ring
  have hoff : ∑ p ∈ n.divisorsAntidiagonal.filter (fun p : ℕ × ℕ ↦ ¬ p.1 = p.2),
      (1 / 2 : ℂ) * ((min p.1 p.2 : ℕ) : ℂ) ^ (k - 1) =
      1 / 2 * ∑ p ∈ n.divisorsAntidiagonal.filter (fun p : ℕ × ℕ ↦ ¬ p.1 = p.2),
        ((min p.1 p.2 : ℕ) : ℂ) ^ (k - 1) := by rw [Finset.mul_sum]
  by_cases hsq : IsSquare n
  · obtain ⟨s, hs⟩ := hsq
    have hs0 : 0 < s := by
      rcases Nat.eq_zero_or_pos s with h | h
      · subst h; simp at hs; omega
      · exact h
    have hne : (2 * (s : ℤ)) ≠ -(2 * (s : ℤ)) := by omega
    rw [if_pos ⟨s, hs⟩, parabolicTs_of_square hs0 hs, diag_of_square hs0 hs,
      Finset.sum_pair hne, Finset.sum_pair hne, Finset.sum_singleton]
    have hn' : (n : ℂ) = (s : ℂ) ^ 2 := by rw [hs]; push_cast; ring
    have hkc : ((k - 2 : ℕ) : ℂ) = (k : ℂ) - 2 := by rw [Nat.cast_sub hk2]; norm_num
    have hH : ∀ t : ℤ, t = 2 * (s : ℤ) ∨ t = -(2 * (s : ℤ)) →
        (TauCeti.hurwitzClassNumber (4 * (n : ℤ) - t ^ 2).toNat : ℂ) = -1 / 12 := by
      intro t ht
      have : 4 * (n : ℤ) - t ^ 2 = 0 := by
        rcases ht with rfl | rfl <;> (rw [hs]; push_cast; ring)
      rw [this]; simp
    have hP1 : (dickson 2 (n : ℂ) (k - 2)).eval ((2 * (s : ℤ) : ℤ) : ℂ) =
        ((k : ℂ) - 1) * (s : ℂ) ^ (k - 2) := by
      rw [hn']; push_cast
      rw [dickson_two_sq_eval_two_mul, hkc]; ring
    have hP2 : (dickson 2 (n : ℂ) (k - 2)).eval ((-(2 * (s : ℤ)) : ℤ) : ℂ) =
        ((k : ℂ) - 1) * (s : ℂ) ^ (k - 2) := by
      rw [← hP1]; push_cast
      exact dickson_eval_neg_of_even 2 _ _ hw
    rw [hH _ (Or.inl rfl), hH _ (Or.inr rfl), hP1, hP2]
    have hA1 := aPar_sq hke (by omega) hs0 (ε := 2 * (s : ℤ)) (Or.inl rfl)
    have hA2 := aPar_sq hke (by omega) hs0 (ε := -(2 * (s : ℤ))) (Or.inr rfl)
    rw [← hs] at hA1 hA2
    rw [hA1, hA2]
    have hite : ((k : ℂ) - 1) / 12 * (n : ℂ) ^ (k / 2 - 1) =
        ((k : ℂ) - 1) / 12 * (s : ℂ) ^ (k - 2) := by
      rw [hn']; congr 1; rw [← pow_mul]; congr 1; obtain ⟨r, hr⟩ := hke; omega
    rw [hite]
    simp only [min_self]
    have hsk : (s : ℂ) ^ (k - 1) = s * (s : ℂ) ^ (k - 2) := by
      rw [← pow_succ']; congr 1; omega
    push_cast
    rw [hsk]
    linear_combination (-1 / 2 : ℂ) * hell + hoff
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hsq), parabolicTs_of_not_square hsq, diag_of_not_square hsq]
    simp only [Finset.sum_empty, add_zero, sub_zero]
    rw [hoff]
    linear_combination (-1 / 2 : ℂ) * hell

end ModularFormsKB.Miyake.Wave2B
