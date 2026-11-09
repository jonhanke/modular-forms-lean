import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.TFAE
import Mathlib.Data.Finset.NatDivisors
import ModularFormsKB.Citation
/-!
# Miyake §4.5: Hecke-type recursions and Euler products

Miyake, *Modular Forms* (Springer 1989), §4.5, Lemma 4.5.12, p. 145: for sequences $t(n)$, $d(n)$
($n \ge 1$) in a commutative ring $K$ with $t(1) = d(1) = 1$ and $d$ completely multiplicative,
three conditions are equivalent: the Hecke recursion, a formal Euler product, and the
multiplication formula $t(m)t(n) = \sum_{l \mid (m,n)} l\,d(l)\,t(mn/l^2)$.

## Conventions
* Sequences are functions `ℕ → K`; only the values at $n \ge 1$ matter (the value at $0$ is
  ignored by every condition).
* Miyake's formal Dirichlet series $\sum t(n) n^{-s}$ has the formal Euler product
  $\prod_p (1 - t(p)p^{-s} + p\,d(p)p^{-2s})^{-1}$ exactly when $t$ is multiplicative and, for
  every prime $p$, $\sum_{e \ge 0} t(p^e) X^e = (1 - t(p) X + p\,d(p) X^2)^{-1}$ in $K[[X]]$ with
  $X = p^{-s}$ (Miyake's (4.5.29)–(4.5.30)). Condition (2) is stated in this local form,
  `HasHeckeEulerProduct`.
-/

open PowerSeries

namespace ModularFormsKB.Miyake

variable {K : Type*} [CommRing K]

/-- Sum over the divisors of a product of coprime numbers. -/
lemma sum_divisors_mul_coprime {a b : ℕ} (hab : a.Coprime b) (F : ℕ → K) :
    ∑ l ∈ (a * b).divisors, F l = ∑ l₁ ∈ a.divisors, ∑ l₂ ∈ b.divisors, F (l₁ * l₂) := by
  have : (a * b).divisors = (a.divisors ×ˢ b.divisors).image (fun x : ℕ × ℕ ↦ x.1 * x.2) := by
    rw [Nat.divisors_mul, Finset.mul_def]
  rw [this, Finset.sum_image hab.mul_injOn_divisors, Finset.sum_product]

/-- Euler factor identity versus the recursion at a single prime. -/
lemma heckeEulerFactor_iff (t d : ℕ → K) (ht : t 1 = 1) (p : ℕ) :
    (PowerSeries.mk (fun e ↦ t (p ^ e)) * (1 - C (t p) * X + C ((p : K) * d p) * X ^ 2) = 1) ↔
      ∀ e : ℕ, 1 ≤ e → t p * t (p ^ e) = t (p ^ (e + 1)) + p * d p * t (p ^ (e - 1)) := by
  have expand : PowerSeries.mk (fun e ↦ t (p ^ e)) *
      (1 - C (t p) * X + C ((p : K) * d p) * X ^ 2) =
      PowerSeries.mk (fun e ↦ t (p ^ e)) - C (t p) * (X * PowerSeries.mk (fun e ↦ t (p ^ e)))
        + C ((p : K) * d p) * (X * (X * PowerSeries.mk (fun e ↦ t (p ^ e)))) := by ring
  have key : ∀ n, coeff (n + 2) (PowerSeries.mk (fun e ↦ t (p ^ e)) *
      (1 - C (t p) * X + C ((p : K) * d p) * X ^ 2)) =
      t (p ^ (n + 2)) - t p * t (p ^ (n + 1)) + p * d p * t (p ^ n) := by
    intro n
    rw [expand]
    simp only [map_add, map_sub, coeff_C_mul, show n + 2 = (n + 1) + 1 from rfl,
      coeff_succ_X_mul, coeff_mk]
  constructor
  · intro h e he
    obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
    have := key n
    rw [h, coeff_one] at this
    have hne : n + 2 ≠ 0 := by omega
    simp only [hne, ↓reduceIte] at this
    simp only [Nat.add_sub_cancel]
    linear_combination this
  · intro h
    ext n
    rcases n with _ | _ | n
    · rw [expand]
      simp [ht]
    · rw [expand]
      simp only [map_add, map_sub, coeff_C_mul, coeff_one, coeff_mk]
      rw [coeff_succ_X_mul 0, coeff_succ_X_mul 0, coeff_zero_X_mul]
      simp [ht]
    · rw [key, coeff_one]
      have hne : n + 2 ≠ 0 := by omega
      simp only [hne, ↓reduceIte]
      have := h (n + 1) (by omega)
      simp only [Nat.add_sub_cancel] at this
      linear_combination -this

/-- Product identity for a sequence satisfying a three-term recursion. -/
lemma heckeRec_mul_succ (U : ℕ → K) (a b : K) (hU0 : U 0 = 1) (hU1 : U 1 = a)
    (hrec : ∀ e : ℕ, 1 ≤ e → a * U e = U (e + 1) + b * U (e - 1)) :
    ∀ f e : ℕ, U (e + 1) * U (f + 1) = U (e + f + 2) + b * (U e * U f) := by
  intro f
  induction f with
  | zero =>
    intro e
    have := hrec (e + 1) (by omega)
    simp only [Nat.add_sub_cancel] at this
    simp only [hU0, hU1, Nat.add_zero, mul_one, zero_add]
    linear_combination this
  | succ f ih =>
    intro e
    have h1 : a * U (f + 1) = U (f + 2) + b * U f := by
      simpa using hrec (f + 1) (by omega)
    have h2 : a * U (e + 1) = U (e + 2) + b * U e := by
      simpa using hrec (e + 1) (by omega)
    have h3 : U (e + 2) * U (f + 1) = U (e + f + 3) + b * (U (e + 1) * U f) := by
      have := ih (e + 1)
      rwa [show e + 1 + f + 2 = e + f + 3 by omega] at this
    rw [show e + (f + 1) + 2 = e + f + 3 by omega, show f + 1 + 1 = f + 2 by omega]
    linear_combination (-U (e + 1)) * h1 + U (f + 1) * h2 + h3

/-- Product formula for a sequence satisfying a three-term recursion. -/
lemma heckeRec_mul_eq_sum (U : ℕ → K) (a b : K) (hU0 : U 0 = 1) (hU1 : U 1 = a)
    (hrec : ∀ e : ℕ, 1 ≤ e → a * U e = U (e + 1) + b * U (e - 1)) :
    ∀ e f : ℕ, U e * U f =
      ∑ g ∈ Finset.range (min e f + 1), b ^ g * U (e + f - 2 * g) := by
  intro e
  induction e with
  | zero => intro f; simp [hU0]
  | succ e ih =>
    intro f
    rcases f with _ | f
    · simp [hU0]
    · rw [heckeRec_mul_succ U a b hU0 hU1 hrec f e, ih f,
        show min (e + 1) (f + 1) = min e f + 1 by omega, Finset.sum_range_succ' _ (min e f + 1),
        Finset.mul_sum]
      rw [add_comm]
      congr 1
      · apply Finset.sum_congr rfl
        intro g hg
        rw [show e + 1 + (f + 1) - 2 * (g + 1) = e + f - 2 * g by omega]
        ring
      · rw [pow_zero, one_mul]
        congr 1
        omega

/-- The right-hand side of condition (3): $S(m, n) = \sum_{0 < l \mid (m,n)} l\,d(l)\,t(mn/l^2)$. -/
def heckeS (t d : ℕ → K) (m n : ℕ) : K :=
  ∑ l ∈ (Nat.gcd m n).divisors, (l : K) * d l * t (m * n / l ^ 2)

/-- A completely multiplicative $d$ with $d(1) = 1$ satisfies $d(p^g) = d(p)^g$. -/
lemma heckeD_pow (d : ℕ → K) (hd : d 1 = 1)
    (hdmul : ∀ m n : ℕ, 0 < m → 0 < n → d (m * n) = d m * d n) (p : ℕ) (hp : 0 < p) :
    ∀ g : ℕ, d (p ^ g) = d p ^ g := by
  intro g
  induction g with
  | zero => simp [hd]
  | succ g ih => rw [pow_succ, hdmul _ _ (pow_pos hp g) hp, ih, pow_succ]

/-- Condition (3) for prime powers. -/
lemma heckeS_prime_pow (t d : ℕ → K) (ht : t 1 = 1) (hd : d 1 = 1)
    (hdmul : ∀ m n : ℕ, 0 < m → 0 < n → d (m * n) = d m * d n) (p : ℕ) (hp : p.Prime)
    (hrec : ∀ e : ℕ, 1 ≤ e → t p * t (p ^ e) = t (p ^ (e + 1)) + p * d p * t (p ^ (e - 1)))
    (e f : ℕ) : t (p ^ e) * t (p ^ f) = heckeS t d (p ^ e) (p ^ f) := by
  rw [heckeRec_mul_eq_sum (fun n ↦ t (p ^ n)) (t p) (p * d p) (by simpa using ht) (by simp) hrec e f]
  unfold heckeS
  have hg : Nat.gcd (p ^ e) (p ^ f) = p ^ (min e f) := by
    rcases le_total e f with h | h
    · rw [min_eq_left h, Nat.gcd_eq_left (pow_dvd_pow p h)]
    · rw [min_eq_right h, Nat.gcd_eq_right (pow_dvd_pow p h)]
  rw [hg, Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro g hg'
  have hgm : g ≤ min e f := by simpa [Nat.lt_succ_iff] using hg'
  have hge : g ≤ e := hgm.trans (min_le_left _ _)
  have hgf : g ≤ f := hgm.trans (min_le_right _ _)
  rw [heckeD_pow d hd hdmul p hp.pos, ← pow_add, ← pow_mul, Nat.pow_div (by omega) hp.pos,
    show 2 * g = g * 2 by ring]
  push_cast
  rw [mul_pow]

/-- Multiplicativity of the right-hand side of condition (3). -/
lemma heckeS_mul (t d : ℕ → K)
    (hdmul : ∀ m n : ℕ, 0 < m → 0 < n → d (m * n) = d m * d n)
    (htm : ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → t (m * n) = t m * t n)
    (m₁ m₂ n₁ n₂ : ℕ) (h1 : 0 < m₁) (h2 : 0 < m₂) (h3 : 0 < n₁) (h4 : 0 < n₂)
    (hc : (m₁ * n₁).Coprime (m₂ * n₂)) :
    heckeS t d (m₁ * m₂) (n₁ * n₂) = heckeS t d m₁ n₁ * heckeS t d m₂ n₂ := by
  have c12 : m₁.Coprime m₂ := (hc.coprime_dvd_left (Dvd.intro _ rfl)).coprime_dvd_right
    (Dvd.intro _ rfl)
  have c1 : m₁.Coprime n₂ := (hc.coprime_dvd_left (Dvd.intro _ rfl)).coprime_dvd_right
    (Dvd.intro_left _ rfl)
  have c2 : n₁.Coprime m₂ := (hc.coprime_dvd_left (Dvd.intro_left _ rfl)).coprime_dvd_right
    (Dvd.intro _ rfl)
  have c3 : n₁.Coprime n₂ := (hc.coprime_dvd_left (Dvd.intro_left _ rfl)).coprime_dvd_right
    (Dvd.intro_left _ rfl)
  have hg : Nat.gcd (m₁ * m₂) (n₁ * n₂) = Nat.gcd m₁ n₁ * Nat.gcd m₂ n₂ := by
    rw [Nat.Coprime.gcd_mul _ c3, Nat.Coprime.gcd_mul_right_cancel _ c2.symm,
      Nat.Coprime.gcd_mul_left_cancel _ c1.symm.symm]
  have cg : (Nat.gcd m₁ n₁).Coprime (Nat.gcd m₂ n₂) :=
    (hc.coprime_dvd_left ((Nat.gcd_dvd_left _ _).trans (Dvd.intro _ rfl))).coprime_dvd_right
      ((Nat.gcd_dvd_left _ _).trans (Dvd.intro _ rfl))
  unfold heckeS
  rw [hg, sum_divisors_mul_coprime cg, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro l₁ hl₁
  apply Finset.sum_congr rfl
  intro l₂ hl₂
  have l1pos : 0 < l₁ := Nat.pos_of_mem_divisors hl₁
  have l2pos : 0 < l₂ := Nat.pos_of_mem_divisors hl₂
  have hm₁ : l₁ ∣ m₁ := (Nat.dvd_of_mem_divisors hl₁).trans (Nat.gcd_dvd_left _ _)
  have hn₁ : l₁ ∣ n₁ := (Nat.dvd_of_mem_divisors hl₁).trans (Nat.gcd_dvd_right _ _)
  have hm₂ : l₂ ∣ m₂ := (Nat.dvd_of_mem_divisors hl₂).trans (Nat.gcd_dvd_left _ _)
  have hn₂ : l₂ ∣ n₂ := (Nat.dvd_of_mem_divisors hl₂).trans (Nat.gcd_dvd_right _ _)
  obtain ⟨u₁, hu₁⟩ : l₁ ^ 2 ∣ m₁ * n₁ := by rw [pow_two]; exact mul_dvd_mul hm₁ hn₁
  obtain ⟨u₂, hu₂⟩ : l₂ ^ 2 ∣ m₂ * n₂ := by rw [pow_two]; exact mul_dvd_mul hm₂ hn₂
  have u1pos : 0 < u₁ := by
    rcases Nat.eq_zero_or_pos u₁ with h | h
    · rw [h, mul_zero] at hu₁; exact absurd hu₁ (Nat.mul_pos h1 h3).ne'
    · exact h
  have u2pos : 0 < u₂ := by
    rcases Nat.eq_zero_or_pos u₂ with h | h
    · rw [h, mul_zero] at hu₂; exact absurd hu₂ (Nat.mul_pos h2 h4).ne'
    · exact h
  have e1 : m₁ * n₁ / l₁ ^ 2 = u₁ := by
    rw [hu₁]; exact Nat.mul_div_cancel_left _ (pow_pos l1pos 2)
  have e2 : m₂ * n₂ / l₂ ^ 2 = u₂ := by
    rw [hu₂]; exact Nat.mul_div_cancel_left _ (pow_pos l2pos 2)
  have hM : m₁ * m₂ * (n₁ * n₂) = (l₁ * l₂) ^ 2 * (u₁ * u₂) := by
    calc m₁ * m₂ * (n₁ * n₂) = (m₁ * n₁) * (m₂ * n₂) := by ring
      _ = _ := by rw [hu₁, hu₂]; ring
  have cu : u₁.Coprime u₂ :=
    (hc.coprime_dvd_left (Dvd.intro_left _ hu₁.symm)).coprime_dvd_right
      (Dvd.intro_left _ hu₂.symm)
  rw [e1, e2, hM, Nat.mul_div_cancel_left _ (pow_pos (Nat.mul_pos l1pos l2pos) 2),
    hdmul l₁ l₂ l1pos l2pos, htm u₁ u₂ u1pos u2pos cu, Nat.cast_mul]
  ring

/-- The recursion and multiplicativity give condition (3). -/
lemma heckeS_eq (t d : ℕ → K) (ht : t 1 = 1) (hd : d 1 = 1)
    (hdmul : ∀ m n : ℕ, 0 < m → 0 < n → d (m * n) = d m * d n)
    (h : ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → t (m * n) = t m * t n)
    (hrec : ∀ p e : ℕ, p.Prime → 1 ≤ e →
      t p * t (p ^ e) = t (p ^ (e + 1)) + p * d p * t (p ^ (e - 1))) :
    ∀ N m n : ℕ, m * n = N → 0 < m → 0 < n → t m * t n = heckeS t d m n := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro m n hN hm hn
  by_cases h1 : m * n = 1
  · have hm1 : m = 1 := Nat.eq_one_of_mul_eq_one_right h1
    have hn1 : n = 1 := Nat.eq_one_of_mul_eq_one_left h1
    subst hm1 hn1
    simp [heckeS, ht, hd]
  · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
    obtain ⟨e, m', hm', hme⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp.ne_one
    obtain ⟨f, n', hn', hnf⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.ne_one
    subst hme hnf
    have hm'pos : 0 < m' := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
    have hn'pos : 0 < n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hef : e + f ≠ 0 := by
      intro h0
      obtain ⟨rfl, rfl⟩ : e = 0 ∧ f = 0 := by omega
      simp only [pow_zero, one_mul] at hpd
      rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h <;> contradiction
    have hlt : m' * n' < N := by
      rw [← hN]
      have : p ^ (e + f) ≥ 2 := by
        calc p ^ (e + f) ≥ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
          _ ≥ 2 := by simpa using hp.two_le
      calc m' * n' < p ^ (e + f) * (m' * n') := by
            have := Nat.mul_pos hm'pos hn'pos
            nlinarith
        _ = _ := by rw [pow_add]; ring
    have IH := ih (m' * n') hlt m' n' rfl hm'pos hn'pos
    have cm : (p ^ e).Coprime m' := ((Nat.Prime.coprime_iff_not_dvd hp).2 hm').pow_left e
    have cn : (p ^ f).Coprime n' := ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').pow_left f
    have cc : (p ^ e * p ^ f).Coprime (m' * n') := by
      apply Nat.Coprime.mul_left <;> apply Nat.Coprime.mul_right
      · exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hm').pow_left e
      · exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').pow_left e
      · exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hm').pow_left f
      · exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').pow_left f
    have hpe : 0 < p ^ e := pow_pos hp.pos e
    have hpf : 0 < p ^ f := pow_pos hp.pos f
    rw [h _ _ hpe hm'pos cm, h _ _ hpf hn'pos cn,
      heckeS_mul t d hdmul h (p ^ e) m' (p ^ f) n' hpe hm'pos hpf hn'pos cc,
      ← heckeS_prime_pow t d ht hd hdmul p hp (fun e he ↦ hrec p e hp he) e f, ← IH]
    ring


/-- Condition (1) of Miyake, Lemma 4.5.12: $t(mn) = t(m)t(n)$ for coprime $m, n \ge 1$, and
$t(p)\,t(p^e) = t(p^{e+1}) + p\,d(p)\,t(p^{e-1})$ for every prime $p$ and $e \ge 1$. -/
def HeckeRecursion (t d : ℕ → K) : Prop :=
  (∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → t (m * n) = t m * t n) ∧
    ∀ p e : ℕ, p.Prime → 1 ≤ e → t p * t (p ^ e) = t (p ^ (e + 1)) + p * d p * t (p ^ (e - 1))

/-- Condition (2) of Miyake, Lemma 4.5.12, in local form: $t$ is multiplicative and for every
prime $p$, $\big(\sum_{e\ge0} t(p^e)X^e\big)(1 - t(p)X + p\,d(p)X^2) = 1$ in $K[[X]]$; with $X = p^{-s}$ this is
the formal Euler product $\sum_n t(n)n^{-s} = \prod_p (1 - t(p)p^{-s} + p\,d(p)p^{-2s})^{-1}$. -/
def HasHeckeEulerProduct (t d : ℕ → K) : Prop :=
  (∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → t (m * n) = t m * t n) ∧
    ∀ p : ℕ, p.Prime →
      PowerSeries.mk (fun e ↦ t (p ^ e)) * (1 - C (t p) * X + C ((p : K) * d p) * X ^ 2) = 1

/-- Condition (3) of Miyake, Lemma 4.5.12: for all $m, n \ge 1$,
$t(m)\,t(n) = \sum_{0 < l \mid (m,n)} l\,d(l)\,t(mn/l^2)$. -/
def HeckeMultiplication (t d : ℕ → K) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    t m * t n = ∑ l ∈ (Nat.gcd m n).divisors, (l : K) * d l * t (m * n / l ^ 2)

/-- **Miyake, Lemma 4.5.12.** Let $K$ be a commutative ring and $t, d$ sequences in $K$ with
$t(1) = d(1) = 1$ and $d(mn) = d(m)d(n)$ for all $m, n \ge 1$. Then the Hecke recursion (1), the
formal Euler product (2) and the multiplication formula (3) are equivalent. -/
@[kb "miyake1989" "Lemma 4.5.12, p. 145"]
theorem heckeRecursion_tfae (t d : ℕ → K) (ht : t 1 = 1) (hd : d 1 = 1)
    (hdmul : ∀ m n : ℕ, 0 < m → 0 < n → d (m * n) = d m * d n) :
    [HeckeRecursion t d, HasHeckeEulerProduct t d, HeckeMultiplication t d].TFAE := by
  tfae_have 1 ↔ 2 := by
    refine and_congr_right fun hm ↦ ?_
    constructor
    · intro h p hp
      exact (heckeEulerFactor_iff t d ht p).2 (h p · hp)
    · intro h p e hp he
      exact (heckeEulerFactor_iff t d ht p).1 (h p hp) e he
  tfae_have 1 → 3 := by
    intro h m n hm hn
    exact heckeS_eq t d ht hd hdmul h.1 h.2 _ m n rfl hm hn
  tfae_have 3 → 1 := by
    intro h
    refine ⟨fun m n hm hn hmn ↦ ?_, fun p e hp he ↦ ?_⟩
    · have := h m n hm hn
      rw [hmn.gcd_eq_one] at this
      simpa [hd] using this.symm
    · have := h p (p ^ e) hp.pos (pow_pos hp.pos e)
      have hg : Nat.gcd p (p ^ e) = p := Nat.gcd_eq_left (dvd_pow_self p (by omega))
      rw [hg, Nat.Prime.divisors hp, Finset.sum_pair hp.one_lt.ne] at this
      obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
      have h1 : p * p ^ (k + 1) = p ^ (k + 1 + 1) := by ring
      have h2 : p ^ (k + 1 + 1) / p ^ 2 = p ^ k := by
        rw [Nat.pow_div (by omega) hp.pos]
        simp
      rw [h1, h2] at this
      simp only [Nat.cast_one, hd, one_mul, Nat.one_pow, Nat.div_one] at this
      simp only [Nat.add_sub_cancel]
      rw [this]
  tfae_finish

end ModularFormsKB.Miyake
