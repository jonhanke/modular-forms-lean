/-
# The class number relations: Kronecker–Hurwitz and Gauss's three-squares formula

Two classical identities for the Hurwitz class numbers $H(n)$ (`ClassNumber.lean`):

* **Kronecker–Hurwitz** (Kronecker 1860, Hurwitz 1885; Zagier 1975 `zagier1975` reproves it by holomorphic projection
  of $\mathcal H\theta$; Hirzebruch–Zagier 1976 `hirzebruchzagier1976`, §2.2 [unverified]): for $n \ge 1$,
  $$\sum_{t\in\mathbb Z,\ t^2\le 4n} H(4n-t^2) = 2\sigma(n) - \lambda(n), \qquad \lambda(n) = \sum_{d\mid n}\min(d, n/d).$$
* **Sums of three squares** (Gauss, *Disquisitiones* Art. 291–292; in this form Hirzebruch–Zagier 1976, §2.2, and
  Cohen 1975 `cohen1975` [unverified]): for all $n \ge 0$, $r_3(n) = 12\,(H(4n) - 2H(n))$. At $n = 0$ this is
  $1 = 12(-\tfrac1{12} + \tfrac2{12})$.

Both are deep (their sources' proofs go through Zagier's weight 3/2 Eisenstein series, `ZagierEisenstein.lean`), so they
are **named inputs** here (`KroneckerHurwitzRelation`, `ThreeSquaresClassNumber`), each **checked by the kernel** for
small $n$ (`kroneckerHurwitz_check`, `threeSquares_check`) so that the statements are not vacuous or misnormalized.

**Proved.**
* Unconditionally: $r_3(n) = 0$ for $n \equiv 7 \bmod 8$ (`r3_eq_zero_of_mod_eight`) and $r_3(4n) = r_3(n)$
  (`r3_four_mul`), both by congruences.
* From `ThreeSquaresClassNumber`: **Gauss's formula** $r_3(n) = 12H(4n)$ for $n \equiv 1, 2 \bmod 4$ (`gauss_r3`), since
  $H(n) = 0$ there; $H(4n) = 2H(n)$ for $n \equiv 7 \bmod 8$ (`hurwitz_four_mul_of_mod_eight`); and
  $H(16n) = 3H(4n) - 2H(n)$ (`hurwitz_sixteen_mul`).
-/
import ModularFormsKB.Hurwitz.ClassNumber

namespace ModularFormsKB.Hurwitz

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- $\sum_{t \in \mathbb Z,\ t^2 \le 4n} H(4n - t^2)$, the left side of the Kronecker–Hurwitz relation; $t$ runs over
$|t| \le \lfloor\sqrt{4n}\rfloor$, so $4n - t^2 \ge 0$ and natural subtraction is exact. -/
def classNumberSum (n : ℕ) : ℚ :=
  ∑ t ∈ Icc (-((4 * n).sqrt : ℤ)) (4 * n).sqrt, TauCeti.hurwitzClassNumber (4 * n - t.natAbs ^ 2)

/-- **Input: the Kronecker–Hurwitz class number relation** (Kronecker 1860, Hurwitz 1885; Zagier 1975 `zagier1975`;
Hirzebruch–Zagier 1976 `hirzebruchzagier1976`, §2.2 [unverified]): for $n \ge 1$,
$\sum_{t^2 \le 4n} H(4n - t^2) = 2\sigma(n) - \lambda(n)$. -/
@[kb "hirzebruchzagier1976" "§2.2: sum over t of H(4n - t^2) = 2 sigma(n) - lambda(n) (Kronecker-Hurwitz) [unverified]"]
structure KroneckerHurwitzRelation : Prop where
  relation : ∀ n : ℕ, 0 < n → classNumberSum n = 2 * (σ 1 n : ℚ) - kroneckerLambda n

/-- **Input: the three-squares formula** (Gauss, *Disquisitiones* Art. 291–292; Hirzebruch–Zagier 1976
`hirzebruchzagier1976`, §2.2; Cohen 1975 `cohen1975` [unverified]): $r_3(n) = 12\,(H(4n) - 2H(n))$ for all $n \ge 0$. -/
@[kb "hirzebruchzagier1976" "§2.2: r_3(n) = 12 (H(4n) - 2 H(n)) for all n >= 0 (Gauss) [unverified]"]
structure ThreeSquaresClassNumber : Prop where
  r3_eq : ∀ n : ℕ, (r3 n : ℚ) = 12 * (TauCeti.hurwitzClassNumber (4 * n) - 2 * TauCeti.hurwitzClassNumber n)

/-! ### Kernel checks of the two statements -/

/-- **The Kronecker–Hurwitz relation holds for $1 \le n \le 20$** (checked by the kernel; $\sigma$ written out by
`sigma_apply`). -/
theorem kroneckerHurwitz_check :
    ∀ n ∈ Icc 1 20, classNumberSum n = 2 * ((∑ d ∈ n.divisors, d : ℕ) : ℚ) - kroneckerLambda n := by
  decide +kernel

/-- **The three-squares formula holds for $0 \le n \le 25$** (checked by the kernel). -/
theorem threeSquares_check :
    ∀ n ∈ range 26, (r3 n : ℚ) =
      12 * (TauCeti.hurwitzClassNumber (4 * n) - 2 * TauCeti.hurwitzClassNumber n) := by
  decide +kernel

/-! ### Elementary facts about $r_3$ -/

/-- No sum of three squares is $\equiv 7 \bmod 8$. -/
theorem r3_eq_zero_of_mod_eight {n : ℕ} (hn : n % 8 = 7) : r3 n = 0 := by
  rw [r3, card_eq_zero, eq_empty_iff_forall_notMem]
  intro v hv
  rw [mem_threeSquareReps] at hv
  have h := congrArg (fun m : ℤ ↦ (m : ZMod 8)) hv
  have h7 : ((n : ℤ) : ZMod 8) = 7 := by
    rw [Int.cast_natCast, ← ZMod.natCast_mod, hn]
    rfl
  simp only [Int.cast_add, Int.cast_pow, h7] at h
  have key : ∀ a b c : ZMod 8, a ^ 2 + b ^ 2 + c ^ 2 ≠ 7 := by decide
  exact key _ _ _ h

/-- If $x^2 + y^2 + z^2 \equiv 0 \bmod 4$ then $x$ is even. -/
theorem even_of_sum_three_sq_four_dvd {x y z : ℤ} (h : 4 ∣ x ^ 2 + y ^ 2 + z ^ 2) : 2 ∣ x := by
  have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).2 h
  push_cast at h'
  have key : ∀ a b c : ZMod 4, a ^ 2 + b ^ 2 + c ^ 2 = 0 → 2 * a = 0 := by decide
  have h2 := key _ _ _ h'
  have : (4 : ℤ) ∣ 2 * x := by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * x) 4).1 (by push_cast; exact h2)
  omega

/-- **$r_3(4n) = r_3(n)$**: a representation of $4n$ has all coordinates even, so $v \mapsto 2v$ is a bijection. -/
theorem r3_four_mul (n : ℕ) : r3 (4 * n) = r3 n := by
  symm
  refine card_bij (fun v _ ↦ (2 * v.1, 2 * v.2.1, 2 * v.2.2)) ?_ ?_ ?_
  · intro v hv
    rw [mem_threeSquareReps] at hv ⊢
    push_cast
    linear_combination 4 * hv
  · intro v _ w _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    exact Prod.ext (by omega) (Prod.ext (by omega) (by omega))
  · intro w hw
    rw [mem_threeSquareReps] at hw
    have hd : (4 : ℤ) ∣ w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 := ⟨n, by rw [hw]; push_cast; ring⟩
    obtain ⟨a, ha⟩ := even_of_sum_three_sq_four_dvd hd
    obtain ⟨b, hb⟩ := even_of_sum_three_sq_four_dvd (x := w.2.1) (y := w.1) (z := w.2.2)
      (by convert hd using 1; ring)
    obtain ⟨c, hc⟩ := even_of_sum_three_sq_four_dvd (x := w.2.2) (y := w.1) (z := w.2.1)
      (by convert hd using 1; ring)
    refine ⟨(a, b, c), ?_, ?_⟩
    · rw [mem_threeSquareReps]
      rw [ha, hb, hc] at hw
      push_cast at hw
      linarith [show (2 * a) ^ 2 = 4 * a ^ 2 by ring, show (2 * b) ^ 2 = 4 * b ^ 2 by ring,
        show (2 * c) ^ 2 = 4 * c ^ 2 by ring]
    · simp [← ha, ← hb, ← hc]

/-! ### Consequences of the three-squares formula -/

/-- **Gauss's formula** (from `ThreeSquaresClassNumber`): $r_3(n) = 12\,H(4n)$ for $n \equiv 1, 2 \bmod 4$. -/
@[kb "hirzebruchzagier1976" "Gauss: r_3(n) = 12 H(4n) for n = 1, 2 mod 4, from r_3(n) = 12(H(4n) - 2H(n)) [unverified]"]
theorem gauss_r3 (h : ThreeSquaresClassNumber) {n : ℕ} (hn : n % 4 = 1 ∨ n % 4 = 2) :
    (r3 n : ℚ) = 12 * TauCeti.hurwitzClassNumber (4 * n) := by
  rw [h.r3_eq, TauCeti.hurwitzClassNumber_eq_zero_of_mod_four_eq_one_or_two hn]
  ring

/-- From `ThreeSquaresClassNumber`: $H(4n) = 2H(n)$ for $n \equiv 7 \bmod 8$, as $r_3(n) = 0$. -/
theorem hurwitz_four_mul_of_mod_eight (h : ThreeSquaresClassNumber) {n : ℕ} (hn : n % 8 = 7) :
    TauCeti.hurwitzClassNumber (4 * n) = 2 * TauCeti.hurwitzClassNumber n := by
  have := h.r3_eq n
  rw [r3_eq_zero_of_mod_eight hn] at this
  push_cast at this
  linarith

/-- From `ThreeSquaresClassNumber`: $H(16n) = 3H(4n) - 2H(n)$, as $r_3(4n) = r_3(n)$. -/
theorem hurwitz_sixteen_mul (h : ThreeSquaresClassNumber) (n : ℕ) :
    TauCeti.hurwitzClassNumber (16 * n) =
      3 * TauCeti.hurwitzClassNumber (4 * n) - 2 * TauCeti.hurwitzClassNumber n := by
  have h1 := h.r3_eq (4 * n)
  have h2 := h.r3_eq n
  rw [r3_four_mul, show 4 * (4 * n) = 16 * n by ring] at h1
  linarith

end ModularFormsKB.Hurwitz
