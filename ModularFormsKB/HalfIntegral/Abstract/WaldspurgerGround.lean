/-
# Groundwork for Waldspurger's theorem in the level 4 plus space

Waldspurger 1981 `waldspurger1981` (Cor. 2 [unverified]) specialized to Kohnen's plus space of
level $4$ (`WaldspurgerPlus`, `ModularFormsKB/HalfIntegral/Abstract/Waldspurger.lean`). This file proves the consequences that do
not need the theta correspondence. Throughout, $g = \sum c(n)q^n \in S^+_{k+1/2}(4)$ and the normalized Hecke eigenform
$F = \sum b(n)q^n \in S_{2k}(\mathrm{SL}_2(\mathbb Z))$ correspond (`Corresponds`), and $D$ is a fundamental discriminant with
$(-1)^kD > 0$.

**Quadratic twists.** $L(F,\chi_D,s) = \sum_{n\ge1}\left(\frac Dn\right)b(n)n^{-s}$ (`quadTwistCoeff`, `quadTwistL`), with the
Kronecker symbol `kroneckerDisc`. For odd $d$ the Kronecker symbol is the Jacobi symbol (`kroneckerDisc_of_odd`) and agrees
with the character of the $|D|$-th Shimura lift (`shimuraChar_natAbs_of_odd`).

**The Shimura-lift relation on a square class** (proved, from `shimuraCoeff_heckeT` and the Hecke relations):
$$ \sum_{d\mid m}\Big(\frac Dd\Big)d^{k-1}c\big(|D|m^2/d^2\big) = c(|D|)\,b(m) \qquad (m \text{ odd}) $$
(`Corresponds.shimuraCoeff_odd`, `Corresponds.sum_kronecker_odd`); in particular $c(|D|p^2) =
\big(b(p) - (\tfrac Dp)p^{k-1}\big)c(|D|)$ for odd primes $p$ (`Corresponds.coeff_mul_prime_sq`), and by Möbius inversion
$c(|D|m^2) = c(|D|)\sum_{d\mid m}\mu(d)\left(\frac Dd\right)d^{k-1}b(m/d)$ for odd $m$ (`Corresponds.coeff_mul_sq_odd`). So
on the square class of $|D|$, the coefficients at odd $m$ are determined by $c(|D|)$ and $F$. The case of even $m$ needs
Kohnen's operator $T^+(4)$ at $p = 2$, which `Corresponds` does not record; it is not treated here.

**Waldspurger from Kohnen–Zagier** (proved, conditional on named inputs). The Kohnen–Zagier formula (`KohnenZagier`)
gives the ratio form with $|c|^2$ in place of $c^2$ (`WaldspurgerPlusNorm`, `waldspurgerPlusNorm_of_kohnenZagier`), once
$\langle g,g\rangle \ne 0$ (`PlusPeterssonNonzero`). `WaldspurgerPlus` is stated with $c^2$; passing from $|c|^2$ to $c^2$ needs
that the coefficients of $g$ are a common complex multiple of real numbers (`PlusRealCoefficients`); without it the
$c^2$ form fails (rotate $c(|D_2|)$ alone by $i$). Result: `waldspurgerPlus_of_kohnenZagier`.
-/
import ModularFormsKB.HalfIntegral.Abstract.Waldspurger
import ModularFormsKB.HalfIntegral.Abstract.SquareClass

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup ModularForm
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-! ## Quadratic twists -/

/-- The coefficients $\left(\frac Dn\right)b(n)$ of the quadratic twist $L(F,\chi_D,s)$. -/
noncomputable def quadTwistCoeff (D : ℤ) (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  (kroneckerDisc D n : ℂ) * b n

/-- **The quadratic twist** $L(F,\chi_D,s) = \sum_{n \ge 1}\left(\frac Dn\right)b(n)n^{-s}$, as Mathlib's `LSeries` (the
Dirichlet series; its value is meaningful where it converges). The central value $L(F, D, k)$ of `KohnenZagier` and
`WaldspurgerPlus` is the value at $s = k$ of an entire continuation of this series (`IsEntireLSeries`). -/
noncomputable def quadTwistL (D : ℤ) (b : ℕ → ℂ) (s : ℂ) : ℂ :=
  LSeries (quadTwistCoeff D b) s

/-- The entire continuation of `KohnenZagier` and `WaldspurgerPlus` continues `quadTwistL`. -/
theorem IsEntireLSeries.eq_quadTwistL {D : ℤ} {b : ℕ → ℂ} {σ₀ : ℝ} {L : ℂ → ℂ}
    (h : IsEntireLSeries (fun n ↦ (kroneckerDisc D n : ℂ) * b n) σ₀ L) {s : ℂ} (hs : σ₀ < s.re) :
    L s = quadTwistL D b s :=
  h.2 s hs

/-- **For odd $n$ the Kronecker symbol is the Jacobi symbol.** -/
theorem kroneckerDisc_of_odd (D : ℤ) {n : ℕ} (hn : Odd n) : kroneckerDisc D n = jacobiSym D n := by
  have h2 : n.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h ↦ (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 h))
  simp [kroneckerDisc, h2]

/-- $(-1)^k|D| = D$ when $(-1)^k D > 0$. -/
theorem neg_one_pow_mul_natAbs {k : ℕ} {D : ℤ} (hsign : 0 < (-1) ^ k * D) :
    (-1) ^ k * (D.natAbs : ℤ) = D := by
  have habs : (D.natAbs : ℤ) = (-1) ^ k * D := by
    rw [Int.natCast_natAbs, ← abs_of_pos hsign, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [habs, ← mul_assoc, ← mul_pow]
  norm_num

/-- The trivial character mod $4$ is $1$ at odd primes. -/
private theorem one_four_apply_of_odd {p : ℕ} (hp : Odd p) : (1 : DirichletCharacter ℂ (4 * 1)) p = 1 := by
  apply MulChar.one_apply
  rw [ZMod.isUnit_iff_coprime]
  have : Nat.Coprime p 2 := Nat.coprime_two_right.2 hp
  simpa using this.pow_right 2

/-- **The character of the $|D|$-th Shimura lift is the Kronecker symbol** on odd $d$ (level $4$, trivial character). -/
theorem shimuraChar_natAbs_of_odd (k : ℕ) {D : ℤ} (hsign : 0 < (-1) ^ k * D) {d : ℕ} (hd : Odd d) :
    shimuraChar k 1 1 D.natAbs d = kroneckerDisc D d := by
  rw [shimuraChar, one_four_apply_of_odd hd, one_mul, neg_one_pow_mul_natAbs hsign, kroneckerDisc_of_odd D hd]

/-! ## The Shimura-lift relation on a square class -/

/-- `shimuraCoeff` is linear in the coefficient sequence (scalars). -/
theorem shimuraCoeff_smul (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ) (α : ℂ) (a : ℕ → ℂ) (n : ℕ) :
    shimuraCoeff k N χ t (α • a) n = α * shimuraCoeff k N χ t a n := by
  simp only [shimuraCoeff, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

theorem shimuraCoeff_one (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ) (a : ℕ → ℂ) :
    shimuraCoeff k N χ t a 1 = a t := by
  simp [shimuraCoeff, shimuraChar]

/-- **Hecke recursion for the lift** at an odd prime: if $T(p^2)c = \lambda c$ and $p^2 \nmid t$ then
$A_t(pn) = \lambda A_t(n) - [p\mid n]\,p^{2k-1}A_t(n/p)$. -/
private theorem shimuraCoeff_rec {k t p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ht : ¬ p ^ 2 ∣ t) {c : ℕ → ℂ} {lam : ℂ}
    (hc : heckeT k 1 1 p c = lam • c) {n : ℕ} (hn : 1 ≤ n) :
    shimuraCoeff k 1 1 t c (p * n) = lam * shimuraCoeff k 1 1 t c n -
      if p ∣ n then (p : ℂ) ^ (2 * (k : ℤ) - 1) * shimuraCoeff k 1 1 t c (n / p) else 0 := by
  have h := shimuraCoeff_heckeT k 1 1 hp ht c hn
  rw [hc, shimuraCoeff_smul] at h
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hχ : ((1 : DirichletCharacter ℂ (4 * 1)) ^ 2) p = 1 := by
    rw [one_pow, one_four_apply_of_odd hodd]
  rw [h, heckeTInt, hχ]
  split_ifs <;> push_cast <;> ring

/-- **Hecke recursion for $F$** at a prime, level one. -/
private theorem heckeTInt_rec {k p : ℕ} {b : ℕ → ℂ} (hb : heckeTInt (2 * k) 1 1 p b = b p • b) (n : ℕ) :
    b (p * n) = b p * b n - if p ∣ n then (p : ℂ) ^ (2 * (k : ℤ) - 1) * b (n / p) else 0 := by
  have h := congrFun hb n
  have h1 : (1 : DirichletCharacter ℂ 1) p = 1 := MulChar.one_apply (isUnit_of_subsingleton _)
  simp only [heckeTInt, h1, one_mul, Pi.smul_apply, smul_eq_mul] at h
  push_cast at h ⊢
  rw [← h]
  split_ifs <;> ring

/-- **The Shimura-lift relation for odd $m$, formal version:** if $T(p^2)c = b(p)c$ and $T(p)b = b(p)b$ for every odd
prime $p$, $b(1) = 1$, and $p^2 \nmid t$ for odd primes $p$, then $A_t(m) = c(t)\,b(m)$ for every odd $m$. -/
theorem shimuraCoeff_eq_of_eigen_odd {k t : ℕ} (ht : ∀ p, p.Prime → p ≠ 2 → ¬ p ^ 2 ∣ t) {c b : ℕ → ℂ}
    (hb1 : b 1 = 1) (hF : ∀ p, p.Prime → p ≠ 2 → heckeTInt (2 * k) 1 1 p b = b p • b)
    (hg : ∀ p, p.Prime → p ≠ 2 → heckeT k 1 1 p c = b p • c) :
    ∀ m, Odd m → shimuraCoeff k 1 1 t c m = c t * b m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm
  by_cases h1 : m = 1
  · subst h1; rw [shimuraCoeff_one, hb1, mul_one]
  obtain ⟨p, m', hp, hp2, rfl⟩ : ∃ p m', p.Prime ∧ p ≠ 2 ∧ m = p * m' := by
    refine ⟨m.minFac, m / m.minFac, Nat.minFac_prime h1, ?_, (Nat.mul_div_cancel' (Nat.minFac_dvd m)).symm⟩
    intro h
    have h2 := Nat.minFac_dvd m
    rw [h] at h2
    exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h2)
  have hm' : Odd m' := (Nat.odd_mul.1 hm).2
  have hm'pos : 1 ≤ m' := hm'.pos
  have hlt : m' < p * m' := lt_mul_left hm'pos hp.one_lt
  rw [shimuraCoeff_rec hp hp2 (ht p hp hp2) (hg p hp hp2) hm'pos, heckeTInt_rec (hF p hp hp2) m',
    ih m' hlt hm']
  split_ifs with hdvd
  · obtain ⟨r, rfl⟩ := hdvd
    have hr : Odd r := (Nat.odd_mul.1 hm').2
    rw [Nat.mul_div_cancel_left _ hp.pos,
      ih r (lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hp.pos) hlt) hr]
    ring
  · ring

/-- **The Shimura-lift relation on the square class of $|D|$, odd $m$:**
$A_{|D|}(m) = \sum_{d\mid m}\chi(d)\left(\frac{(-1)^k|D|}d\right)d^{k-1}c(|D|m^2/d^2) = c(|D|)\,b(m)$. -/
@[kb "kohnenzagier1981" "§II, the relation c(|D|n²) ↔ c(|D|), odd n (via Shimura 1973) [unverified]"]
theorem Corresponds.shimuraCoeff_odd {M : MultiplierSystem} {k : ℕ} {g : ℍ → ℂ} {c : ℕ → ℂ}
    {F : CuspForm 𝒮ℒ (2 * k : ℕ)} {b : ℕ → ℂ} (h : Corresponds M k g c F b) {D : ℤ}
    (hD : IsFundamentalDiscriminant D) {m : ℕ} (hm : Odd m) :
    shimuraCoeff k 1 1 D.natAbs c m = c D.natAbs * b m :=
  shimuraCoeff_eq_of_eigen_odd (fun _ hp hp2 ↦ hD.not_sq_dvd_natAbs hp hp2) h.normalized
    (fun p hp _ ↦ h.eigen_F p hp) h.eigen_g m hm

/-- **The same relation with the Kronecker symbol:** for odd $m$ and $(-1)^kD > 0$,
$\sum_{d\mid m}\left(\frac Dd\right)d^{k-1}c(|D|(m/d)^2) = c(|D|)\,b(m)$. -/
theorem Corresponds.sum_kronecker_odd {M : MultiplierSystem} {k : ℕ} {g : ℍ → ℂ} {c : ℕ → ℂ}
    {F : CuspForm 𝒮ℒ (2 * k : ℕ)} {b : ℕ → ℂ} (h : Corresponds M k g c F b) {D : ℤ}
    (hD : IsFundamentalDiscriminant D) (hsign : 0 < (-1) ^ k * D) {m : ℕ} (hm : Odd m) :
    ∑ d ∈ m.divisors, (kroneckerDisc D d : ℂ) * (d : ℂ) ^ ((k : ℤ) - 1) * c (D.natAbs * (m / d) ^ 2) =
      c D.natAbs * b m := by
  rw [← h.shimuraCoeff_odd hD hm, shimuraCoeff]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdo : Odd d := Odd.of_dvd_nat hm (Nat.dvd_of_mem_divisors hd)
  rw [shimuraChar_natAbs_of_odd k hsign hdo]

/-- **Hecke relation at an odd prime:** $c(|D|p^2) = \big(b(p) - \left(\frac Dp\right)p^{k-1}\big)\,c(|D|)$. -/
theorem Corresponds.coeff_mul_prime_sq {M : MultiplierSystem} {k : ℕ} {g : ℍ → ℂ} {c : ℕ → ℂ}
    {F : CuspForm 𝒮ℒ (2 * k : ℕ)} {b : ℕ → ℂ} (h : Corresponds M k g c F b) {D : ℤ}
    (hD : IsFundamentalDiscriminant D) (hsign : 0 < (-1) ^ k * D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    c (D.natAbs * p ^ 2) = (b p - (kroneckerDisc D p : ℂ) * (p : ℂ) ^ ((k : ℤ) - 1)) * c D.natAbs := by
  have h' := h.sum_kronecker_odd hD hsign (hp.odd_of_ne_two hp2)
  rw [Nat.Prime.sum_divisors hp] at h'
  simp only [Nat.div_self hp.pos, Nat.div_one, Nat.cast_one, one_zpow, mul_one, one_pow] at h'
  have h1 : kroneckerDisc D 1 = 1 := by simp [kroneckerDisc]
  rw [h1, Int.cast_one, one_mul] at h'
  linear_combination h'

/-- The weight $\chi_t(d)d^{k-1}$ of the lift is completely multiplicative. -/
private theorem shimuraWeight_mul (k t x y : ℕ) :
    shimuraChar k 1 1 t (x * y) * ((x * y : ℕ) : ℂ) ^ ((k : ℤ) - 1) =
      (shimuraChar k 1 1 t x * (x : ℂ) ^ ((k : ℤ) - 1)) * (shimuraChar k 1 1 t y * (y : ℂ) ^ ((k : ℤ) - 1)) := by
  have h0 : (1 : DirichletCharacter ℂ (4 * 1)) ((0 : ℕ) : ZMod (4 * 1)) = 0 := by
    rw [Nat.cast_zero]
    have : Fact (1 < 4 * 1) := ⟨by norm_num⟩
    exact MulChar.map_nonunit _ not_isUnit_zero
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [zero_mul, shimuraChar, h0]
  rcases eq_or_ne y 0 with rfl | hy
  · simp only [mul_zero, shimuraChar, h0, zero_mul]
  simp only [shimuraChar]
  push_cast
  rw [map_mul, jacobiSym.mul_right' _ hx hy, mul_zpow]
  push_cast
  ring

/-- **The coefficients on the square class of $|D|$, odd $m$** (Möbius-inverted form):
$c(|D|m^2) = c(|D|)\sum_{d\mid m}\mu(d)\left(\frac Dd\right)d^{k-1}b(m/d)$. -/
@[kb "kohnenzagier1981" "§II, c(|D|n²) = c(|D|) Σ μ(d)(D/d)d^{k-1}a(n/d), odd n (via Shimura 1973) [unverified]"]
theorem Corresponds.coeff_mul_sq_odd {M : MultiplierSystem} {k : ℕ} {g : ℍ → ℂ} {c : ℕ → ℂ}
    {F : CuspForm 𝒮ℒ (2 * k : ℕ)} {b : ℕ → ℂ} (h : Corresponds M k g c F b) {D : ℤ}
    (hD : IsFundamentalDiscriminant D) (hsign : 0 < (-1) ^ k * D) {m : ℕ} (hm : Odd m) :
    c (D.natAbs * m ^ 2) = c D.natAbs *
      ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) * (kroneckerDisc D d : ℂ) * (d : ℂ) ^ ((k : ℤ) - 1) *
        b (m / d) := by
  set f : ℕ → ℂ := fun d ↦ shimuraChar k 1 1 D.natAbs d * (d : ℂ) ^ ((k : ℤ) - 1) with hf
  have hinv := sum_moebius_mul_inversion f (fun n ↦ c (D.natAbs * n ^ 2)) (by simp [hf, shimuraChar])
    (shimuraWeight_mul k D.natAbs) hm.pos
  rw [hinv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdm : d ∣ m := Nat.dvd_of_mem_divisors hd
  have hdo : Odd d := Odd.of_dvd_nat hm hdm
  have hmd : Odd (m / d) := Odd.of_dvd_nat hm (Nat.div_dvd_of_dvd hdm)
  have hA : ∑ e ∈ (m / d).divisors, f e * c (D.natAbs * (m / d / e) ^ 2) = c D.natAbs * b (m / d) := by
    rw [← h.shimuraCoeff_odd hD hmd, shimuraCoeff]
  rw [hA, hf]
  simp only [shimuraChar_natAbs_of_odd k hsign hdo]
  ring

/-! ## Waldspurger's ratio form from the Kohnen–Zagier formula -/

/-- **The Petersson norm of a nonzero plus form is nonzero** (positivity of the Petersson inner product; Kohnen–Zagier
1981 use $\langle g, g\rangle > 0$ throughout [unverified]). Proved elsewhere as
`MultiplierSystem.peterssonNormSqFour_ne_zero`; restated here so that this file does not depend on that development. -/
@[kb "kohnenzagier1981" "positivity of ⟨g,g⟩ on S⁺_{k+1/2}(4) (used throughout) [unverified]"]
structure PlusPeterssonNonzero (M : MultiplierSystem) (k : ℕ) : Prop where
  ne_zero : ∀ g ∈ M.plusCuspForms k 1 1, g ≠ 0 → peterssonNormSqFour k g ≠ 0

/-- **A plus eigenform is a multiple of one with real coefficients** (Kohnen 1980 `kohnen1980`: multiplicity one in
$S^+_{k+1/2}(4)$ for the Hecke operators, and $S^+_{k+1/2}(4)$ has a basis with rational coefficients [unverified]):
if $g$ and $F$ correspond, $c = u\,r$ with $u \in \mathbb C$ and $r$ real. -/
@[kb "kohnen1980" "multiplicity one in S⁺_{k+1/2}(4) and a rational basis; eigenforms have real coefficients up to a scalar [unverified]"]
structure PlusRealCoefficients (M : MultiplierSystem) (k : ℕ) : Prop where
  real : 1 ≤ k → ∀ (g : ℍ → ℂ) (c : ℕ → ℂ) (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ),
    Corresponds M k g c F b → ∃ (u : ℂ) (r : ℕ → ℝ), ∀ n, c n = u * r n

/-- **Waldspurger's ratio form with absolute values** (level $4$ plus space): as `WaldspurgerPlus` with $|c(|D_i|)|^2$ in place
of $c(|D_i|)^2$. Proved from `KohnenZagier` in `waldspurgerPlusNorm_of_kohnenZagier`. -/
@[kb "waldspurger1981" "Cor. 2, ratio form with |c|², level 4 plus space [unverified]"]
structure WaldspurgerPlusNorm (M : MultiplierSystem) (k : ℕ) : Prop where
  ratio : 1 ≤ k → ∀ (g : ℍ → ℂ) (c : ℕ → ℂ) (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ),
    Corresponds M k g c F b → ∀ D₁ D₂ : ℤ, IsFundamentalDiscriminant D₁ → IsFundamentalDiscriminant D₂ →
      0 < (-1) ^ k * D₁ → 0 < (-1) ^ k * D₂ →
      ∀ L₁ L₂ : ℂ → ℂ, IsEntireLSeries (fun n ↦ (kroneckerDisc D₁ n : ℂ) * b n) ((k : ℝ) + 1) L₁ →
        IsEntireLSeries (fun n ↦ (kroneckerDisc D₂ n : ℂ) * b n) ((k : ℝ) + 1) L₂ →
        ((‖c D₁.natAbs‖ ^ 2 : ℝ) : ℂ) * ((D₂.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) * L₂ k =
          ((‖c D₂.natAbs‖ ^ 2 : ℝ) : ℂ) * ((D₁.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) * L₁ k

/-- **Waldspurger's ratio form with $|c|^2$ follows from the Kohnen–Zagier formula** once $\langle g,g\rangle \ne 0$: divide
the two instances of the formula. -/
theorem waldspurgerPlusNorm_of_kohnenZagier {M : MultiplierSystem} {k : ℕ} (hKZ : KohnenZagier M k)
    (hP : PlusPeterssonNonzero M k) : WaldspurgerPlusNorm M k where
  ratio hk g c F b h D₁ D₂ hD₁ hD₂ hs₁ hs₂ L₁ L₂ hL₁ hL₂ := by
    have hP4 := hP.ne_zero g h.plus h.ne_zero
    have e₁ := hKZ.formula hk g c F b h D₁ hD₁ hs₁ L₁ hL₁
    have e₂ := hKZ.formula hk g c F b h D₂ hD₂ hs₂ L₂ hL₂
    rw [div_eq_iff hP4] at e₁ e₂
    rw [e₁, e₂]
    ring

/-- **`WaldspurgerPlus` from the Kohnen–Zagier formula**, given $\langle g,g\rangle \ne 0$ and that the coefficients of $g$
are a common multiple of real numbers. -/
theorem waldspurgerPlus_of_norm {M : MultiplierSystem} {k : ℕ} (hW : WaldspurgerPlusNorm M k)
    (hR : PlusRealCoefficients M k) : WaldspurgerPlus M k where
  ratio hk g c F b h D₁ D₂ hD₁ hD₂ hs₁ hs₂ L₁ L₂ hL₁ hL₂ := by
    have e := hW.ratio hk g c F b h D₁ D₂ hD₁ hD₂ hs₁ hs₂ L₁ L₂ hL₁ hL₂
    obtain ⟨u, r, hr⟩ := hR.real hk g c F b h
    have hn : ∀ n, ((‖c n‖ ^ 2 : ℝ) : ℂ) = ((‖u‖ ^ 2 : ℝ) : ℂ) * (r n : ℂ) ^ 2 := by
      intro n
      rw [hr n, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      push_cast
      ring
    rw [hn, hn] at e
    set X₁ : ℂ := (((D₁.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) : ℂ)
    set X₂ : ℂ := (((D₂.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) : ℂ)
    rw [hr, hr]
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    have hu' : ((‖u‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
      exact_mod_cast pow_ne_zero 2 this
    have e' : (r D₁.natAbs : ℂ) ^ 2 * X₂ * L₂ k = (r D₂.natAbs : ℂ) ^ 2 * X₁ * L₁ k := by
      apply mul_left_cancel₀ hu'
      linear_combination e
    linear_combination u ^ 2 * e'

/-- **`WaldspurgerPlus` (level 4 plus space, ratio form) from `KohnenZagier`**, conditional on the named inputs
`PlusPeterssonNonzero` and `PlusRealCoefficients`. -/
theorem waldspurgerPlus_of_kohnenZagier {M : MultiplierSystem} {k : ℕ} (hKZ : KohnenZagier M k)
    (hP : PlusPeterssonNonzero M k) (hR : PlusRealCoefficients M k) : WaldspurgerPlus M k :=
  waldspurgerPlus_of_norm (waldspurgerPlusNorm_of_kohnenZagier hKZ hP) hR

end ModularFormsKB.HalfIntegral
