import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import ModularFormsKB.Citation
/-!
# Jacobi's differential equation of the third order for all modular equations

Jacobi, *Fundamenta nova theoriae functionum ellipticarum* (1829), § 33, pp. 76–81: every modular equation
between the modulus `k` and the transformed modulus `λ` satisfies one and the same differential equation
of the third order, symmetric in `k` and `λ`:

  `3 λ''² - 2 λ' λ''' + λ'² [ ((1 + k²)/(k - k³))² - ((1 + λ²)/(λ - λ³))² λ'² ] = 0`,

with `λ' = dλ/dk` etc. (the sign as printed by Jacobi).

Jacobi derives it from Legendre's differential equation for the complete integrals `K`, `K'`
(`(k - k³) y'' + (1 - 3k²) y' - k y = 0`) and the multiplier formula: a transformation of order `n` gives
`Λ'/Λ = n K'/K`. We formalize exactly this derivation:

* the modular relation is expressed through the period ratio: `A`, `B` are solutions of Legendre's
  equation on `(0, 1)` (for Jacobi `A = K`, `B = K'`), and `λ = λ(k)` satisfies
  `B(λ)/A(λ) = M(B(k)/A(k))` for a real Möbius transformation `M(t) = (a t + b)/(c t + d)`, `ad - bc ≠ 0`
  (for a transformation of order `n`, `M(t) = n t`; Jacobi's check `λ = (1 - k')/(1 + k')` is `n = 2`);
* the conclusion is Jacobi's equation (`jacobi_modular_equation_ode`).

The proof is the Schwarzian derivative computation: the ratio of two solutions of `y'' + p y' + q y = 0`
has Schwarzian `2q - p²/2 - p'`, which for Legendre's equation is `½ ((1 + k²)/(k - k³))²`; the Schwarzian
is invariant under Möbius transformations and obeys the chain rule.

Regularity: `A`, `B` are assumed `C³` and `λ` `C³` (Jacobi differentiates freely; solutions of Legendre's
equation are analytic on `(0, 1)`). That `K`, `K'` themselves solve Legendre's equation is not proved here
(Tau Ceti: `legendreK_differential_equation`; Mathlib has no complete elliptic integrals); see the loose end.
-/

noncomputable section

open Set

namespace ModularFormsKB.Historical.Jacobi

/-- Legendre's differential equation for the complete elliptic integrals as functions of the modulus:
`(k - k³) y'' + (1 - 3k²) y' - k y = 0` (Legendre; used by Jacobi, *Fundamenta nova* § 33). A solution on
`(0, 1)`: three times continuously differentiable there, satisfying the equation. -/
def IsLegendreSolution (y : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 3 y (Ioo 0 1) ∧
    ∀ k ∈ Ioo (0 : ℝ) 1, (k - k ^ 3) * deriv (deriv y) k + (1 - 3 * k ^ 2) * deriv y k - k * y k = 0

/-- Jacobi's rational function `(1 + k²)/(k - k³)` of § 33. -/
def jacobiR (k : ℝ) : ℝ := (1 + k ^ 2) / (k - k ^ 3)

section Helpers

lemma d3 {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U) :
    ∀ y ∈ U, HasDerivAt f (deriv f y) y ∧ HasDerivAt (deriv f) (deriv (deriv f) y) y ∧
      HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) y) y := by
  have h3 : ContDiffOn ℝ ((2 : ℕ) + 1) f U := by exact_mod_cast hf
  obtain ⟨d1, -, h2⟩ := (contDiffOn_succ_iff_deriv_of_isOpen hU).1 h3
  have h2' : ContDiffOn ℝ ((1 : ℕ) + 1) (deriv f) U := by exact_mod_cast h2
  obtain ⟨d2, -, h1⟩ := (contDiffOn_succ_iff_deriv_of_isOpen hU).1 h2'
  have h1' : ContDiffOn ℝ ((0 : ℕ) + 1) (deriv (deriv f)) U := by exact_mod_cast h1
  obtain ⟨d3, -, -⟩ := (contDiffOn_succ_iff_deriv_of_isOpen hU).1 h1'
  intro y hy
  exact ⟨(d1.differentiableAt (hU.mem_nhds hy)).hasDerivAt,
    (d2.differentiableAt (hU.mem_nhds hy)).hasDerivAt,
    (d3.differentiableAt (hU.mem_nhds hy)).hasDerivAt⟩

lemma deriv_eq_aux {f g f' g' : ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J) (hfg : ∀ y ∈ J, f y = g y)
    (hf : ∀ y ∈ J, HasDerivAt f (f' y) y) (hg : ∀ y ∈ J, HasDerivAt g (g' y) y) :
    ∀ y ∈ J, f' y = g' y := by
  intro y hy
  have hev : f =ᶠ[nhds y] g := Filter.eventuallyEq_of_mem (hJ.mem_nhds hy) (fun z hz => hfg z hz)
  exact (hf y hy).unique ((hg y hy).congr_of_eventuallyEq hev)

lemma chain {f f1 f2 f3 h h1 h2 h3 : ℝ → ℝ} {J : Set ℝ}
    (hf : ∀ y ∈ J, HasDerivAt f (f1 (h y)) (h y) ∧ HasDerivAt f1 (f2 (h y)) (h y) ∧
      HasDerivAt f2 (f3 (h y)) (h y))
    (hh : ∀ y ∈ J, HasDerivAt h (h1 y) y ∧ HasDerivAt h1 (h2 y) y ∧ HasDerivAt h2 (h3 y) y) :
    ∀ y ∈ J, HasDerivAt (fun y => f (h y)) (f1 (h y) * h1 y) y ∧
      HasDerivAt (fun y => f1 (h y) * h1 y) (f2 (h y) * h1 y ^ 2 + f1 (h y) * h2 y) y ∧
      HasDerivAt (fun y => f2 (h y) * h1 y ^ 2 + f1 (h y) * h2 y)
        (f3 (h y) * h1 y ^ 3 + 3 * f2 (h y) * h1 y * h2 y + f1 (h y) * h3 y) y := by
  intro y hy
  obtain ⟨a1, a2, a3⟩ := hf y hy
  obtain ⟨b1, b2, b3⟩ := hh y hy
  have c1 : HasDerivAt (fun y => f (h y)) (f1 (h y) * h1 y) y := a1.comp y b1
  have c2 : HasDerivAt (fun y => f1 (h y)) (f2 (h y) * h1 y) y := a2.comp y b1
  have c3 : HasDerivAt (fun y => f2 (h y)) (f3 (h y) * h1 y) y := a3.comp y b1
  refine ⟨c1, ?_, ?_⟩
  · exact (c2.mul b2).congr_deriv (by ring)
  · have e1 : HasDerivAt (fun y => f2 (h y) * h1 y ^ 2)
        (f3 (h y) * h1 y * h1 y ^ 2 + f2 (h y) * (2 * h1 y * h2 y)) y :=
      c3.mul ((b2.pow 2).congr_deriv (by norm_num))
    have e2 : HasDerivAt (fun y => f1 (h y) * h2 y)
        (f2 (h y) * h1 y * h2 y + f1 (h y) * h3 y) y :=
      c2.mul b3
    have e3 : HasDerivAt (fun y => f2 (h y) * h1 y ^ 2 + f1 (h y) * h2 y)
        ((f3 (h y) * h1 y * h1 y ^ 2 + f2 (h y) * (2 * h1 y * h2 y)) +
          (f2 (h y) * h1 y * h2 y + f1 (h y) * h3 y)) y := HasDerivAt.add e1 e2
    exact e3.congr_deriv (by ring)

lemma mobius_deriv {a b c d : ℝ} (τ : ℝ) (he : c * τ + d ≠ 0) :
    HasDerivAt (fun τ => (a * τ + b) / (c * τ + d)) ((a * d - b * c) / (c * τ + d) ^ 2) τ ∧
    HasDerivAt (fun τ => (a * d - b * c) / (c * τ + d) ^ 2) ((-2 * c * (a * d - b * c)) / (c * τ + d) ^ 3) τ ∧
    HasDerivAt (fun τ => (-2 * c * (a * d - b * c)) / (c * τ + d) ^ 3)
      ((6 * c ^ 2 * (a * d - b * c)) / (c * τ + d) ^ 4) τ := by
  have hl : HasDerivAt (fun τ : ℝ => c * τ + d) c τ :=
    HasDerivAt.congr_deriv (((hasDerivAt_id' τ).const_mul c).add_const d) (by ring)
  have hn : HasDerivAt (fun τ : ℝ => a * τ + b) a τ :=
    HasDerivAt.congr_deriv (((hasDerivAt_id' τ).const_mul a).add_const b) (by ring)
  have hp2 : HasDerivAt (fun τ : ℝ => (c * τ + d) ^ 2) (2 * (c * τ + d) * c) τ :=
    (hl.pow 2).congr_deriv (by norm_num)
  have hp3 : HasDerivAt (fun τ : ℝ => (c * τ + d) ^ 3) (3 * (c * τ + d) ^ 2 * c) τ :=
    (hl.pow 3).congr_deriv (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · refine (hn.fun_div hl he).congr_deriv ?_
    field_simp
    ring
  · refine ((hasDerivAt_const τ (a * d - b * c)).fun_div hp2 (pow_ne_zero 2 he)).congr_deriv ?_
    field_simp
    ring
  · refine ((hasDerivAt_const τ (-2 * c * (a * d - b * c))).fun_div hp3 (pow_ne_zero 3 he)).congr_deriv ?_
    field_simp
    ring

/-- Wronskian `A B' - A' B`. -/
def tW (A B : ℝ → ℝ) (y : ℝ) : ℝ := A y * deriv B y - deriv A y * B y
def tm (A : ℝ → ℝ) (y : ℝ) : ℝ := -((1 - 3 * y ^ 2) / (y - y ^ 3)) - 2 * (deriv A y / A y)
def tdm (A : ℝ → ℝ) (y : ℝ) : ℝ :=
  -(((-6 * y) * (y - y ^ 3) - (1 - 3 * y ^ 2) * (1 - 3 * y ^ 2)) / (y - y ^ 3) ^ 2) -
    2 * ((deriv (deriv A) y * A y - deriv A y * deriv A y) / A y ^ 2)
def tt1 (A B : ℝ → ℝ) (y : ℝ) : ℝ := tW A B y / A y ^ 2
def tt2 (A B : ℝ → ℝ) (y : ℝ) : ℝ := tt1 A B y * tm A y
def tt3 (A B : ℝ → ℝ) (y : ℝ) : ℝ := tt2 A B y * tm A y + tt1 A B y * tdm A y

lemma key_id (y A A1 A2 : ℝ) (hP : y - y ^ 3 ≠ 0) (hA : A ≠ 0)
    (hL : (y - y ^ 3) * A2 + (1 - 3 * y ^ 2) * A1 - y * A = 0) :
    2 * (-(((-6 * y) * (y - y ^ 3) - (1 - 3 * y ^ 2) * (1 - 3 * y ^ 2)) / (y - y ^ 3) ^ 2) -
      2 * ((A2 * A - A1 * A1) / A ^ 2)) -
      (-((1 - 3 * y ^ 2) / (y - y ^ 3)) - 2 * (A1 / A)) ^ 2 = ((1 + y ^ 2) / (y - y ^ 3)) ^ 2 := by
  obtain ⟨P, hPd⟩ : ∃ P, P = y - y ^ 3 := ⟨_, rfl⟩
  rw [← hPd] at hP hL ⊢
  have hA2 : A2 = (y * A - (1 - 3 * y ^ 2) * A1) / P := by
    rw [eq_div_iff hP]
    linear_combination hL
  subst hA2
  field_simp
  subst hPd
  ring

lemma schw_ratio {A B : ℝ → ℝ} (hA : IsLegendreSolution A) (hB : IsLegendreSolution B)
    (hA0 : ∀ k ∈ Ioo (0 : ℝ) 1, A k ≠ 0)
    (hW : ∀ k ∈ Ioo (0 : ℝ) 1, A k * deriv B k - deriv A k * B k ≠ 0) :
    ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun y => B y / A y) (tt1 A B y) y ∧
      HasDerivAt (tt1 A B) (tt2 A B y) y ∧ HasDerivAt (tt2 A B) (tt3 A B y) y ∧
      tt1 A B y ≠ 0 ∧ 2 * tt1 A B y * tt3 A B y - 3 * tt2 A B y ^ 2 = jacobiR y ^ 2 * tt1 A B y ^ 2 := by
  intro y hy
  obtain ⟨a1, a2, -⟩ := d3 isOpen_Ioo hA.1 y hy
  obtain ⟨b1, b2, -⟩ := d3 isOpen_Ioo hB.1 y hy
  have hAy := hA0 y hy
  have hP : y - y ^ 3 ≠ 0 := by
    have h0 : 0 < y := hy.1
    have h1 : y < 1 := hy.2
    have : 0 < y - y ^ 3 := by nlinarith [mul_pos h0 h0, mul_pos (mul_pos h0 h0) (sub_pos.2 h1)]
    exact this.ne'
  have hLA := hA.2 y hy
  have hLB := hB.2 y hy
  have hA2 : deriv (deriv A) y = (y * A y - (1 - 3 * y ^ 2) * deriv A y) / (y - y ^ 3) := by
    rw [eq_div_iff hP]
    linear_combination hLA
  have hB2 : deriv (deriv B) y = (y * B y - (1 - 3 * y ^ 2) * deriv B y) / (y - y ^ 3) := by
    rw [eq_div_iff hP]
    linear_combination hLB
  have hd1 : HasDerivAt (fun y => B y / A y) (tt1 A B y) y := by
    have := b1.fun_div a1 hAy
    refine this.congr_deriv ?_
    simp only [tt1, tW]
    ring
  have hP' : HasDerivAt (fun y : ℝ => y - y ^ 3) (1 - 3 * y ^ 2) y := by
    have := (hasDerivAt_id' y).sub (hasDerivAt_pow 3 y)
    exact this.congr_deriv (by norm_num)
  have hQ' : HasDerivAt (fun y : ℝ => 1 - 3 * y ^ 2) (-6 * y) y := by
    have := (hasDerivAt_const y (1 : ℝ)).sub (((hasDerivAt_pow 2 y).const_mul (3 : ℝ)))
    exact this.congr_deriv (by norm_num; ring)
  have hq : HasDerivAt (fun y : ℝ => (1 - 3 * y ^ 2) / (y - y ^ 3))
      (((-6 * y) * (y - y ^ 3) - (1 - 3 * y ^ 2) * (1 - 3 * y ^ 2)) / (y - y ^ 3) ^ 2) y :=
    hQ'.fun_div hP' hP
  have hr : HasDerivAt (fun y => deriv A y / A y)
      ((deriv (deriv A) y * A y - deriv A y * deriv A y) / A y ^ 2) y := a2.fun_div a1 hAy
  have hm : HasDerivAt (tm A) (tdm A y) y := by
    have := hq.neg.sub (hr.const_mul 2)
    exact this
  have hW' : HasDerivAt (fun y => A y * deriv B y - deriv A y * B y)
      (deriv A y * deriv B y + A y * deriv (deriv B) y -
        (deriv (deriv A) y * B y + deriv A y * deriv B y)) y :=
    HasDerivAt.sub (HasDerivAt.mul a1 b2) (HasDerivAt.mul a2 b1)
  have hp : HasDerivAt (fun y => A y ^ 2) (2 * A y * deriv A y) y :=
    (a1.pow 2).congr_deriv (by norm_num)
  have ht1 : HasDerivAt (tt1 A B) (tt2 A B y) y := by
    have := hW'.fun_div hp (pow_ne_zero 2 hAy)
    refine this.congr_deriv ?_
    simp only [tt2, tt1, tW, tm]
    obtain ⟨P, hPd⟩ : ∃ P, P = y - y ^ 3 := ⟨_, rfl⟩
    rw [← hPd] at hA2 hB2 hP ⊢
    rw [hA2, hB2]
    field_simp
    subst hPd
    ring
  have ht2 : HasDerivAt (tt2 A B) (tt3 A B y) y := by
    have := ht1.mul hm
    exact this
  refine ⟨hd1, ht1, ht2, div_ne_zero (hW y hy) (pow_ne_zero 2 hAy), ?_⟩
  have hk := key_id y (A y) (deriv A y) (deriv (deriv A) y) hP hAy hLA
  simp only [tt3, tt2, tdm, tm, jacobiR]
  linear_combination (tt1 A B y) ^ 2 * hk

lemma alg_final (s1 s2 s3 t1 t2 t3 l1 l2 l3 e c D g1 g2 g3 Rk Ru : ℝ) (he : e ≠ 0)
    (hs1 : s1 ≠ 0) (ht1 : t1 ≠ 0)
    (hg1 : g1 = D / e ^ 2) (hg2 : g2 = -2 * c * D / e ^ 3) (hg3 : g3 = 6 * c ^ 2 * D / e ^ 4)
    (hS : 2 * s1 * s3 - 3 * s2 ^ 2 = Ru ^ 2 * s1 ^ 2)
    (hT : 2 * t1 * t3 - 3 * t2 ^ 2 = Rk ^ 2 * t1 ^ 2)
    (E1 : s1 * l1 = g1 * t1) (E2 : s2 * l1 ^ 2 + s1 * l2 = g2 * t1 ^ 2 + g1 * t2)
    (E3 : s3 * l1 ^ 3 + 3 * s2 * l1 * l2 + s1 * l3 =
      g3 * t1 ^ 3 + 3 * g2 * t1 * t2 + g1 * t3) :
    3 * l2 ^ 2 - 2 * l1 * l3 + l1 ^ 2 * (Rk ^ 2 - Ru ^ 2 * l1 ^ 2) = 0 := by
  subst hg1 hg2 hg3
  have hs3 : s3 = (Ru ^ 2 * s1 ^ 2 + 3 * s2 ^ 2) / (2 * s1) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hs1)]
    linear_combination hS
  have ht3 : t3 = (Rk ^ 2 * t1 ^ 2 + 3 * t2 ^ 2) / (2 * t1) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero ht1)]
    linear_combination hT
  have hl3 : l3 = (6 * c ^ 2 * D / e ^ 4 * t1 ^ 3 + 3 * (-2 * c * D / e ^ 3) * t1 * t2 +
      D / e ^ 2 * t3 - s3 * l1 ^ 3 - 3 * s2 * l1 * l2) / s1 := by
    rw [eq_div_iff hs1]
    linear_combination E3
  have hl2 : l2 = ((-2 * c * D / e ^ 3) * t1 ^ 2 + D / e ^ 2 * t2 - s2 * l1 ^ 2) / s1 := by
    rw [eq_div_iff hs1]
    linear_combination E2
  have hl1 : l1 = D / e ^ 2 * t1 / s1 := by
    rw [eq_div_iff hs1]
    linear_combination E1
  subst hl3 hl2 hl1 hs3 ht3
  field_simp
  ring


/-- The conclusion of Jacobi's equation in terms of `deriv`. -/
theorem jacobi_modular_equation_ode_aux {A B lam : ℝ → ℝ} {I : Set ℝ} {a b c d : ℝ}
    (hA : IsLegendreSolution A) (hB : IsLegendreSolution B)
    (hA0 : ∀ k ∈ Ioo (0 : ℝ) 1, A k ≠ 0)
    (hW : ∀ k ∈ Ioo (0 : ℝ) 1, A k * deriv B k - deriv A k * B k ≠ 0)
    (hI : IsOpen I) (hI01 : I ⊆ Ioo 0 1) (hlam : ContDiffOn ℝ 3 lam I)
    (hlam01 : MapsTo lam I (Ioo 0 1)) (_hM : a * d - b * c ≠ 0)
    (hden : ∀ k ∈ I, c * (B k / A k) + d ≠ 0)
    (hmod : ∀ k ∈ I, B (lam k) / A (lam k) = (a * (B k / A k) + b) / (c * (B k / A k) + d)) :
    ∀ k ∈ I,
      3 * deriv (deriv lam) k ^ 2 - 2 * deriv lam k * deriv (deriv (deriv lam)) k +
        deriv lam k ^ 2 * (jacobiR k ^ 2 - jacobiR (lam k) ^ 2 * deriv lam k ^ 2) = 0 := by
  have hs := schw_ratio hA hB hA0 hW
  have hP := chain (f := fun y => B y / A y) (f1 := tt1 A B) (f2 := tt2 A B) (f3 := tt3 A B)
    (h := lam) (h1 := deriv lam) (h2 := deriv (deriv lam)) (h3 := deriv (deriv (deriv lam)))
    (J := I)
    (fun y hy => by
      have := hs (lam y) (hlam01 hy)
      exact ⟨this.1, this.2.1, this.2.2.1⟩)
    (fun y hy => d3 hI hlam y hy)
  have hQ := chain (f := fun τ => (a * τ + b) / (c * τ + d))
    (f1 := fun τ => (a * d - b * c) / (c * τ + d) ^ 2)
    (f2 := fun τ => (-2 * c * (a * d - b * c)) / (c * τ + d) ^ 3)
    (f3 := fun τ => (6 * c ^ 2 * (a * d - b * c)) / (c * τ + d) ^ 4)
    (h := fun y => B y / A y) (h1 := tt1 A B) (h2 := tt2 A B) (h3 := tt3 A B) (J := I)
    (fun y hy => mobius_deriv (B y / A y) (hden y hy))
    (fun y hy => by
      have := hs y (hI01 hy)
      exact ⟨this.1, this.2.1, this.2.2.1⟩)
  have e1 := deriv_eq_aux hI hmod (fun y hy => (hP y hy).1) (fun y hy => (hQ y hy).1)
  have e2 := deriv_eq_aux hI e1 (fun y hy => (hP y hy).2.1) (fun y hy => (hQ y hy).2.1)
  have e3 := deriv_eq_aux hI e2 (fun y hy => (hP y hy).2.2) (fun y hy => (hQ y hy).2.2)
  intro k hk
  have hk01 := hI01 hk
  have hl01 := hlam01 hk
  have hsl := hs (lam k) hl01
  have hsk := hs k hk01
  have hAk := hA0 k hk01
  exact alg_final (tt1 A B (lam k)) (tt2 A B (lam k)) (tt3 A B (lam k)) (tt1 A B k) (tt2 A B k)
    (tt3 A B k) (deriv lam k) (deriv (deriv lam) k) (deriv (deriv (deriv lam)) k)
    (c * (B k / A k) + d) c (a * d - b * c) _ _ _ (jacobiR k) (jacobiR (lam k))
    (hden k hk) hsl.2.2.2.1 hsk.2.2.2.1 rfl rfl rfl
    hsl.2.2.2.2 hsk.2.2.2.2 (e1 k hk) (e2 k hk) (e3 k hk)

end Helpers

/-- **Jacobi's differential equation of modular equations** (*Fundamenta nova* 1829, § 33, (7)–(8),
pp. 77–78). Let `A`, `B` be solutions of Legendre's equation on `(0, 1)` with
`A ≠ 0` and nonvanishing Wronskian `A B' - A' B` there (for Jacobi, `A = K`, `B = K'`). Let `λ` be a
`C³` function on an open set `I ⊆ (0, 1)` with values in `(0, 1)`, related to `k` by a modular equation in
the form `B(λ)/A(λ) = (a B(k)/A(k) + b)/(c B(k)/A(k) + d)` with `ad - bc ≠ 0` (for a transformation of
order `n`: `Λ'/Λ = n K'/K`). Then on `I`

  `3 λ''² - 2 λ' λ''' + λ'² [ ((1 + k²)/(k - k³))² - ((1 + λ²)/(λ - λ³))² λ'² ] = 0`. -/
@[kb "jacobi1829" "§ 33, (7)–(8), pp. 77–78"]
theorem jacobi_modular_equation_ode {A B lam : ℝ → ℝ} {I : Set ℝ} {a b c d : ℝ}
    (hA : IsLegendreSolution A) (hB : IsLegendreSolution B)
    (hA0 : ∀ k ∈ Ioo (0 : ℝ) 1, A k ≠ 0)
    (hW : ∀ k ∈ Ioo (0 : ℝ) 1, A k * deriv B k - deriv A k * B k ≠ 0)
    (hI : IsOpen I) (hI01 : I ⊆ Ioo 0 1) (hlam : ContDiffOn ℝ 3 lam I)
    (hlam01 : MapsTo lam I (Ioo 0 1)) (hM : a * d - b * c ≠ 0)
    (hden : ∀ k ∈ I, c * (B k / A k) + d ≠ 0)
    (hmod : ∀ k ∈ I, B (lam k) / A (lam k) = (a * (B k / A k) + b) / (c * (B k / A k) + d)) :
    ∀ k ∈ I,
      3 * iteratedDeriv 2 lam k ^ 2 - 2 * deriv lam k * iteratedDeriv 3 lam k +
        deriv lam k ^ 2 * (jacobiR k ^ 2 - jacobiR (lam k) ^ 2 * deriv lam k ^ 2) = 0 := by
  intro k hk
  have h2 : iteratedDeriv 2 lam = deriv (deriv lam) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have h3 : iteratedDeriv 3 lam = deriv (deriv (deriv lam)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, h3]
  exact jacobi_modular_equation_ode_aux hA hB hA0 hW hI hI01 hlam hlam01 hM hden hmod k hk

end ModularFormsKB.Historical.Jacobi
