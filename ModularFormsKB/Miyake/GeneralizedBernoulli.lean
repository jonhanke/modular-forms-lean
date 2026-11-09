import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.BernoulliPolynomials
import ModularFormsKB.Citation
/-!
# Miyake §3.3: generalized Bernoulli numbers and $L(1-k, \chi)$

Miyake, *Modular Forms* (Springer 1989), §3.3, pp. 94–95.

Miyake defines the generalized Bernoulli numbers $B_{n,\chi}$ of a Dirichlet character $\chi$
mod $m$ by the Taylor expansion
$$F_\chi(t) = \sum_{a=1}^{m} \chi(a)\,\frac{t\,e^{at}}{e^{mt} - 1} = \sum_{n \ge 0} B_{n,\chi}\,\frac{t^n}{n!}.$$
We define $B_{n,\chi}$ by the equivalent closed formula
$B_{n,\chi} = m^{n-1}\sum_{a=1}^{m} \chi(a)\,B_n(a/m)$ with Mathlib's Bernoulli polynomials
(`Polynomial.bernoulli`), and prove Miyake's generating-function identity as
`generalizedBernoulli_generating_function` (in the ring of formal power series, multiplied out by
$e^{mt}-1$).

For the principal character ($m = 1$) this gives $B_{n,\chi_0} = B_n(1)$, Miyake's Bernoulli number
$B_n$ with $B_1 = +1/2$ (Mathlib's `bernoulli'`).

Tau Ceti has generalized Bernoulli numbers (`NumberTheory/DirichletCharacter/GeneralizedBernoulli.lean`,
`generalizedBernoulli_def`) and their link to Gauss sums (`LValues.lean`), but not the value
$L(1-k,\chi) = -B_{k,\chi}/k$; it cannot be imported at Mathlib v4.35.0.
-/

open Complex PowerSeries

namespace ModularFormsKB.Miyake

/-- The generalized Bernoulli number $B_{n,\chi}$ of a Dirichlet character $\chi$ mod $m$
($m \ge 1$), over $\mathbb C$:
$$B_{n,\chi} = m^{n-1}\sum_{a=1}^{m} \chi(a)\,B_n\!\left(\tfrac{a}{m}\right),$$
where $B_n(x)$ is the $n$-th Bernoulli polynomial (`Polynomial.bernoulli`, with rational
coefficients, mapped to $\mathbb C$) and $m^{n-1}$ is a power in $\mathbb C$ (so $m^{-1}$ for
$n = 0$). Miyake's definition is the generating function, see
`generalizedBernoulli_generating_function`. -/
@[kb "miyake1989" "§3.3, definition of B_{n,χ}, p. 94"]
noncomputable def generalizedBernoulli {m : ℕ} (χ : DirichletCharacter ℂ m) (n : ℕ) : ℂ :=
  (m : ℂ) ^ ((n : ℤ) - 1) *
    ∑ a ∈ Finset.Icc 1 m, χ a * ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / m)

/-- **Miyake's definition of $B_{n,\chi}$** (§3.3, p. 94): in $\mathbb C[[t]]$,
$$\Big(\sum_{n\ge0} B_{n,\chi}\frac{t^n}{n!}\Big)\,(e^{mt} - 1) = \sum_{a=1}^{m}\chi(a)\,t\,e^{at},$$
i.e. $\sum_n B_{n,\chi} t^n/n! = \sum_{a=1}^m \chi(a)\, t e^{at}/(e^{mt}-1)$. Since $e^{mt} - 1 = t \cdot
(\text{unit})$ this determines the $B_{n,\chi}$. -/
@[kb "miyake1989" "§3.3, definition of B_{n,χ}, p. 94"]
theorem generalizedBernoulli_generating_function {m : ℕ} [NeZero m]
    (χ : DirichletCharacter ℂ m) :
    PowerSeries.mk (fun n ↦ generalizedBernoulli χ n / n.factorial) *
        (rescale (m : ℂ) (exp ℂ) - 1) =
      ∑ a ∈ Finset.Icc 1 m, χ a • (X * rescale (a : ℂ) (exp ℂ)) := by
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have key : ∀ a : ℕ, PowerSeries.mk (fun n : ℕ ↦ (m : ℂ) ^ ((n : ℤ) - 1) *
      ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / m) / n.factorial) *
        (rescale (m : ℂ) (exp ℂ) - 1) = X * rescale (a : ℂ) (exp ℂ) := by
    intro a
    have h := Polynomial.bernoulli_generating_function (A := ℂ) ((a : ℂ) / m)
    have h2 := congrArg (rescale (m : ℂ)) h
    rw [map_mul, map_sub, map_one, map_mul, rescale_X, rescale_rescale, div_mul_cancel₀ _ hm,
      rescale_mk] at h2
    have h3 : (C (m : ℂ)) * (PowerSeries.mk (fun n : ℕ ↦ (m : ℂ) ^ ((n : ℤ) - 1) *
      ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / m) / n.factorial) *
        (rescale (m : ℂ) (exp ℂ) - 1)) = C (m : ℂ) * (X * rescale (a : ℂ) (exp ℂ)) := by
      have hc : C (m : ℂ) * PowerSeries.mk (fun n : ℕ ↦ (m : ℂ) ^ ((n : ℤ) - 1) *
          ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / m) / n.factorial) =
          PowerSeries.mk fun n => (m : ℂ) ^ n * (Polynomial.aeval ((a : ℂ) / m))
            ((1 / (n.factorial : ℚ)) • Polynomial.bernoulli n) := by
        ext n
        simp only [coeff_C_mul, coeff_mk]
        rw [zpow_sub₀ hm, zpow_natCast, zpow_one]
        rw [map_smul, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
        simp only [Rat.smul_def, one_div, Rat.cast_inv, Rat.cast_natCast]
        field_simp
      rw [← mul_assoc, hc, h2, mul_assoc]
    exact mul_left_cancel₀ ((map_ne_zero_iff _ (C_injective)).mpr hm) h3
  have hsum : PowerSeries.mk (fun n ↦ generalizedBernoulli χ n / n.factorial) =
      ∑ a ∈ Finset.Icc 1 m, χ a • PowerSeries.mk (fun n : ℕ ↦ (m : ℂ) ^ ((n : ℤ) - 1) *
      ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / m) / n.factorial) := by
    ext n
    simp only [coeff_mk, map_sum, coeff_smul, generalizedBernoulli, smul_eq_mul, Finset.mul_sum,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    ring
  rw [hsum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [smul_mul_assoc, key a]

/-- **Miyake, Theorem 3.3.4 (1)**, second formula: $L(1-k, \chi) = -B_{k,\chi}/k$.

Miyake states it for primitive $\chi$ and $k \equiv \delta_\chi \pmod 2$. Here $\chi$ is any Dirichlet
character mod $m \ge 1$ (Mathlib's `DirichletCharacter.LFunction`, the analytic continuation of
$\sum \chi(n) n^{-s}$ at level $m$) and $k \ge 2$ of either parity; the case $k = 1$ (only relevant
for odd $\chi$) is not covered. For $k \not\equiv \delta_\chi$ both sides vanish; the vanishing of the
left side is Mathlib's `DirichletCharacter.Even.LFunction_neg_two_mul_nat` and
`DirichletCharacter.Odd.LFunction_neg_two_mul_nat_sub_one` (Theorem 3.3.4 (2)). -/
@[kb "miyake1989" "Theorem 3.3.4 (1), p. 95"]
theorem LFunction_one_sub_nat {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) {k : ℕ}
    (hk : 2 ≤ k) :
    DirichletCharacter.LFunction χ (1 - k) = -generalizedBernoulli χ k / k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hn : n ≠ 0 := by omega
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hs : (1 : ℂ) - ((n + 1 : ℕ) : ℂ) = -(n : ℂ) := by push_cast; ring
  have hterm : ∀ a ∈ Finset.Icc 1 m, χ (a : ZMod m) *
      HurwitzZeta.hurwitzZeta (ZMod.toAddCircle (a : ZMod m)) (-(n : ℂ)) =
      χ a * (-1 / ((n : ℂ) + 1) *
        ((Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / m)) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    rw [ZMod.toAddCircle_natCast]
    have hx : ((a : ℝ) / m) ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m))]
      exact_mod_cast ha.2
    have := HurwitzZeta.hurwitzZeta_neg_nat (k := n) hn hx
    push_cast at this
    rw [this]
  have hbij : ∑ j : ZMod m, χ j * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) (-(n : ℂ)) =
      ∑ a ∈ Finset.Icc 1 m, χ (a : ZMod m) *
        HurwitzZeta.hurwitzZeta (ZMod.toAddCircle (a : ZMod m)) (-(n : ℂ)) := by
    symm
    refine Finset.sum_bij (fun a _ ↦ (a : ZMod m)) (fun _ _ ↦ Finset.mem_univ _) ?_ ?_ fun _ _ ↦ rfl
    · intro a ha b hb hab
      rw [Finset.mem_Icc] at ha hb
      rw [ZMod.natCast_eq_natCast_iff'] at hab
      rcases Nat.lt_or_ge a m with h1 | h1 <;> rcases Nat.lt_or_ge b m with h2 | h2
      · rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hab
      · have : b = m := by omega
        subst this
        rw [Nat.mod_eq_of_lt h1, Nat.mod_self] at hab
        omega
      · have : a = m := by omega
        subst this
        rw [Nat.mod_eq_of_lt h2, Nat.mod_self] at hab
        omega
      · omega
    · intro j _
      by_cases h0 : j.val = 0
      · refine ⟨m, Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero (NeZero.ne m), le_rfl⟩, ?_⟩
        rw [ZMod.val_eq_zero] at h0
        simp [h0]
      · refine ⟨j.val, Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero h0, (ZMod.val_lt j).le⟩, ?_⟩
        simp
  unfold DirichletCharacter.LFunction ZMod.LFunction generalizedBernoulli
  rw [hs, hbij, Finset.sum_congr rfl hterm]
  have : (m : ℂ) ^ (-(-(n : ℂ))) = (m : ℂ) ^ (((n + 1 : ℕ) : ℤ) - 1) := by
    rw [neg_neg, Complex.cpow_natCast]
    push_cast
    simp
  rw [this]
  simp only [← mul_assoc, Finset.mul_sum]
  push_cast
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [eq_div_iff hn1, ← Finset.sum_neg_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  field_simp


/-- **Miyake, Theorem 3.3.4 (2)** for the Bernoulli numbers: if $\chi(-1) = (-1)^{k+1}$ (i.e.
$k \not\equiv \delta_\chi \pmod 2$) and $k \ge 2$, then $B_{k,\chi} = 0$. Combined with
`LFunction_one_sub_nat` this is the vanishing of $L(1-k,\chi)$. -/
@[kb "miyake1989" "Theorem 3.3.4 (2), p. 95"]
theorem generalizedBernoulli_eq_zero_of_parity {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m)
    {k : ℕ} (hk : 2 ≤ k) (hχ : χ (-1) = -(-1) ^ k) :
    generalizedBernoulli χ k = 0 := by
  have hL := LFunction_one_sub_nat χ hk
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  suffices h : DirichletCharacter.LFunction χ (1 - k) = 0 by
    rw [h] at hL
    have := hL.symm
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · exact neg_eq_zero.mp h
    · exact absurd h hk0
  rcases Nat.even_or_odd' k with ⟨n, rfl | rfl⟩
  · have hodd : DirichletCharacter.Odd χ := by
      unfold DirichletCharacter.Odd
      rw [hχ]; simp
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have := hodd.LFunction_neg_two_mul_nat_sub_one n'
    convert this using 2
    push_cast; ring
  · have heven : DirichletCharacter.Even χ := by
      unfold DirichletCharacter.Even
      rw [hχ]; simp [pow_succ, pow_mul]
    have : NeZero n := ⟨by omega⟩
    have := heven.LFunction_neg_two_mul_nat n
    convert this using 2
    push_cast; ring

end ModularFormsKB.Miyake
