import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Fourier.ZMod
import ModularFormsKB.Miyake.GeneralizedBernoulli
import ModularFormsKB.Citation
/-!
# Shimura 2007, §4.11: the classical critical values $L(k,\chi)$ (Theorem 4.12)

G. Shimura, *Elementary Dirichlet Series and Modular Forms* (Springer 2007), §4.11,
pp. 32–33 (pdf pp. 38–39).

**Notation.** Shimura's $\mathbf e(x) = e^{2\pi i x}$, his Gauss sum (4.20)
$G(\chi) = \sum_{a=1}^{d} \chi(a)\mathbf e(a/d)$ is Mathlib's `gaussSum χ ZMod.stdAddChar`, and his
$L(s,\chi)$ (4.14) is Mathlib's `DirichletCharacter.LFunction χ s` (the continuation of
$\sum \chi(n)n^{-s}$). Shimura's $\overline\chi$ (complex conjugate) of a character with values in
roots of unity is the inverse character `χ⁻¹`. His Bernoulli polynomial $B_n(t)$ of (4.7b) is
Mathlib's `Polynomial.bernoulli n` (mapped to $\mathbb C$), and his $B_n = B_n(0)$ (4.8a) is
Mathlib's `bernoulli n` (with $B_1 = -1/2$).

**Results.**
* (4.25) (Theorem 4.12 (i)): `two_mul_factorial_mul_riemannZeta` and
  `nat_mul_riemannZeta_one_sub`, both from Mathlib's values of $\zeta$.
* (4.26), left equality (Theorem 4.12 (ii)), for **every** $k \ge 1$, including $k = 1$:
  `two_mul_factorial_gaussSum_mul_LFunction`, from Mathlib's functional equation of
  `ZMod.LFunction` and the discrete Fourier transform of a primitive character.
* (4.26), right equality, for $k \ge 2$: `nat_mul_LFunction_one_sub`, from
  `ModularFormsKB.Miyake.LFunction_one_sub_nat`. The case $k = 1$ (the value $L(0,\chi)$ of (4.27))
  needs the value of the Hurwitz zeta function at $s = 0$, which Mathlib does not have; it is
  stated as `LZeroValueStatement` and **not proved**.
* the combined (4.26) for $k \ge 2$: `theorem_4_12_ii`.

Lemma 4.13, (4.33) and Corollary 4.16 are in `ModularFormsKB.Shimura2007.Ch2.HalfRangeSums`.
-/

open Complex
open scoped Real ZMod

namespace ModularFormsKB.Shimura2007

open DirichletCharacter

/-- Shimura's Bernoulli polynomial $B_n(t)$ of (4.7b), over $\mathbb C$: Mathlib's
`Polynomial.bernoulli n` (rational coefficients) evaluated at $t \in \mathbb C$. This is a
notation, the same expression as in `ModularFormsKB.Miyake.generalizedBernoulli`. -/
noncomputable abbrev bernoulliPoly (n : ℕ) (t : ℂ) : ℂ :=
  ((Polynomial.bernoulli n).map (algebraMap ℚ ℂ)).eval t

/-! ## Theorem 4.12 (i): Euler's formula (4.25) -/

/-- **Theorem 4.12 (i)**, first part of (4.25): for $0 < n \in 2\mathbb Z$,
$2\cdot n!\,(2\pi i)^{-n}\zeta(n) = -B_n$. Euler; from Mathlib's `riemannZeta_two_mul_nat`. -/
@[kb "shimura2007" "Theorem 4.12 (i), (4.25), p. 32"]
theorem two_mul_factorial_mul_riemannZeta {n : ℕ} (hn : 0 < n) (hev : Even n) :
    2 * (n.factorial : ℂ) * ((2 * π * I) ^ n)⁻¹ * riemannZeta n = -(bernoulli n : ℂ) := by
  obtain ⟨m, rfl⟩ := hev
  have hm : m ≠ 0 := by omega
  rw [show ((m + m : ℕ) : ℂ) = 2 * (m : ℂ) by push_cast; ring, riemannZeta_two_mul_nat hm,
    show m + m = 2 * m by ring]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hf : ((2 * m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hI : (2 * π * I : ℂ) ^ (2 * m) = (-1) ^ m * 2 ^ (2 * m) * π ^ (2 * m) := by
    rw [mul_pow, mul_pow, pow_mul I, I_sq]; ring
  have h2 : (2 : ℂ) ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hI, h2]
  have hm1 : ((-1 : ℂ) ^ m) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  rw [pow_succ]
  ring

/-- **Theorem 4.12 (i)**, second part of (4.25): for $0 < n \in 2\mathbb Z$,
$n\,\zeta(1-n) = -B_n$. From Mathlib's `riemannZeta_neg_nat_eq_bernoulli`. -/
@[kb "shimura2007" "Theorem 4.12 (i), (4.25), p. 32"]
theorem nat_mul_riemannZeta_one_sub {n : ℕ} (hn : 0 < n) (hev : Even n) :
    (n : ℂ) * riemannZeta (1 - n) = -(bernoulli n : ℂ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : Odd k := by
    rcases Nat.even_or_odd k with h | h
    · exact absurd (h.add_one) (Nat.not_odd_iff_even.mpr hev)
    · exact h
  have h1 : (1 : ℂ) - ((k + 1 : ℕ) : ℂ) = -(k : ℂ) := by push_cast; ring
  rw [h1, riemannZeta_neg_nat_eq_bernoulli, hk.neg_one_pow]
  have : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  push_cast
  field_simp

/-! ## Theorem 4.12 (ii): the left equality of (4.26), all `k ≥ 1` -/

section FunctionalEquation

variable {d : ℕ} [NeZero d]

private lemma LFunction_const_mul (c : ℂ) (Φ : ZMod d → ℂ) (s : ℂ) :
    ZMod.LFunction (fun j ↦ c * Φ j) s = c * ZMod.LFunction Φ s := by
  simp only [ZMod.LFunction, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

private lemma exp_pi_I_nat_div_two (k : ℕ) : cexp (π * I * k / 2) = I ^ k := by
  have h : I = cexp (π / 2 * I) := exp_pi_div_two_mul_I.symm
  conv_rhs => rw [h]
  rw [← exp_nat_mul]; congr 1; ring

private lemma exp_neg_pi_I_nat_div_two (k : ℕ) : cexp (-π * I * k / 2) = (-I) ^ k := by
  have : -I = cexp (-(π / 2 * I)) := by rw [exp_neg, exp_pi_div_two_mul_I, inv_I]
  rw [this, ← exp_nat_mul]; congr 1; ring

/-- Functional equation of $L(s,\psi)$ at $s = k$, for a nontrivial primitive $\psi$:
$L(1-k,\psi) = 2\,d^{k-1}(k-1)!\,(2\pi i)^{-k}\,G(\psi)\,L(k,\psi^{-1})$ when
$\psi(-1) = (-1)^k$. -/
theorem LFunction_one_sub_eq_gaussSum_mul {ψ : DirichletCharacter ℂ d} (hψ : ψ.IsPrimitive)
    (hψ1 : ψ ≠ 1) {n : ℕ} (hpar : ψ (-1) = (-1) ^ (n + 1)) :
    LFunction ψ (1 - (n + 1 : ℕ)) = 2 * (d : ℂ) ^ n * (n.factorial : ℂ) *
      ((2 * π * I) ^ (n + 1))⁻¹ * gaussSum ψ ZMod.stdAddChar * LFunction ψ⁻¹ (n + 1 : ℕ) := by
  have : Nontrivial (ZMod d) := ZMod.nontrivial_iff.mpr fun h ↦ hψ1 (ψ.level_one' h)
  have hψ0 : ψ 0 = 0 := MulChar.map_nonunit ψ not_isUnit_zero
  have hs : ∀ m : ℕ, ((n + 1 : ℕ) : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have h' : ((n + 1 + m : ℕ) : ℂ) = 0 := by push_cast at h ⊢; linear_combination h
    exact absurd (by exact_mod_cast h' : n + 1 + m = 0) (by omega)
  have hFE := ZMod.LFunction_one_sub (ψ : ZMod d → ℂ) hs (Or.inl hψ0)
  -- the Fourier transforms
  have hF1 : (𝓕 (ψ : ZMod d → ℂ)) = fun j ↦ (ψ (-1) * gaussSum ψ ZMod.stdAddChar) * ψ⁻¹ j := by
    funext j
    rw [hψ.fourierTransform_eq_inv_mul_gaussSum, neg_eq_neg_one_mul, map_mul,
      MulChar.inv_apply_eq_inv']
    have h1 : ψ (-1) * ψ (-1) = 1 := by
      rw [← map_mul, neg_one_mul, neg_neg, map_one]
    have h2 : (ψ (-1))⁻¹ = ψ (-1) := by
      rw [inv_eq_of_mul_eq_one_right h1]
    rw [h2]; ring
  have hF2 : (𝓕 fun x ↦ (ψ : ZMod d → ℂ) (-x)) =
      fun j ↦ gaussSum ψ ZMod.stdAddChar * ψ⁻¹ j := by
    funext j
    rw [ZMod.dft_comp_neg, hF1]
    simp only
    rw [neg_eq_neg_one_mul j, map_mul, MulChar.inv_apply_eq_inv' ψ (-1)]
    have h1 : ψ (-1) * ψ (-1) = 1 := by
      rw [← map_mul, neg_one_mul, neg_neg, map_one]
    rw [inv_eq_of_mul_eq_one_right h1]
    linear_combination (gaussSum ψ ZMod.stdAddChar * ψ⁻¹ j) * h1
  rw [hF1, hF2, LFunction_const_mul, LFunction_const_mul] at hFE
  have hGam : Gamma ((n + 1 : ℕ) : ℂ) = n.factorial := by
    rw [Nat.cast_succ, Gamma_nat_eq_factorial]
  have hd' : (d : ℂ) ^ (((n + 1 : ℕ) : ℂ) - 1) = (d : ℂ) ^ n := by
    rw [Nat.cast_succ, add_sub_cancel_right, cpow_natCast]
  have h2pi : (2 * (π : ℂ)) ^ (-((n + 1 : ℕ) : ℂ)) = ((2 * (π : ℂ)) ^ (n + 1))⁻¹ := by
    rw [cpow_neg, cpow_natCast]
  have e1 : cexp (π * I * ((n + 1 : ℕ) : ℂ) / 2) = I ^ (n + 1) := exp_pi_I_nat_div_two _
  have e2 : cexp (-π * I * ((n + 1 : ℕ) : ℂ) / 2) = (-I) ^ (n + 1) :=
    exp_neg_pi_I_nat_div_two _
  rw [hGam, hd', h2pi, e1, e2, hpar] at hFE
  have key : (I : ℂ) ^ (n + 1) * (-1) ^ (n + 1) = (-I) ^ (n + 1) := by
    rw [← mul_pow]; ring_nf
  have hIinv : (I : ℂ) ^ (n + 1) * (-I) ^ (n + 1) = 1 := by
    rw [← mul_pow]; simp
  have hpow : (2 * (π : ℂ) * I) ^ (n + 1) = (2 * (π : ℂ)) ^ (n + 1) * I ^ (n + 1) := mul_pow _ _ _
  simp only [LFunction]
  rw [hFE, hpow, mul_inv, inv_eq_of_mul_eq_one_right hIinv]
  linear_combination (d : ℂ) ^ n * ((2 * (π : ℂ)) ^ (n + 1))⁻¹ * (n.factorial : ℂ) *
    gaussSum ψ ZMod.stdAddChar * ZMod.LFunction (ψ⁻¹ : ZMod d → ℂ) ((n + 1 : ℕ) : ℂ) * key

/-- **Theorem 4.12 (ii)**, left equality of (4.26): for a nontrivial primitive Dirichlet
character $\chi$ modulo $d$ and a positive integer $k$ with $\chi(-1) = (-1)^k$,
$$2\cdot k!\,(2\pi i)^{-k}\,G(\overline\chi)\,L(k,\chi) = k\,d^{1-k}\,L(1-k,\overline\chi).$$
Valid for every $k \ge 1$, including $k = 1$ (the left equality of (4.27) after
$\chi \leftrightarrow \overline\chi$). Shimura's $\overline\chi$ is `χ⁻¹`. -/
@[kb "shimura2007" "Theorem 4.12 (ii), (4.26), p. 32"]
theorem two_mul_factorial_gaussSum_mul_LFunction {χ : DirichletCharacter ℂ d}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {k : ℕ} (hk : 1 ≤ k) (hpar : χ (-1) = (-1) ^ k) :
    2 * (k.factorial : ℂ) * ((2 * π * I) ^ k)⁻¹ * gaussSum χ⁻¹ ZMod.stdAddChar *
        LFunction χ k =
      k * ((d : ℂ) ^ (k - 1))⁻¹ * LFunction χ⁻¹ (1 - k) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hψ : (χ⁻¹).IsPrimitive := by
    rwa [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
  have hψ1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ1
  have hparψ : χ⁻¹ (-1) = (-1) ^ (n + 1) := by
    rw [MulChar.inv_apply_eq_inv', hpar, ← inv_pow, inv_neg, inv_one]
  rw [LFunction_one_sub_eq_gaussSum_mul hψ hψ1 hparψ, inv_inv]
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  rw [Nat.factorial_succ, Nat.add_sub_cancel]
  push_cast
  field_simp

end FunctionalEquation

/-! ## Theorem 4.12 (ii): the right equality of (4.26) -/

section RightEquality

variable {d : ℕ} [NeZero d]

/-- For a character $\chi$ mod $d > 1$ the sum $\sum_{a=1}^{d}$ in $B_{k,\chi}$ may stop at
$d - 1$, since $\chi(d) = \chi(0) = 0$. -/
private lemma sum_Icc_eq_sum_Ico {χ : DirichletCharacter ℂ d} (hd : d ≠ 1) (f : ℕ → ℂ) :
    ∑ a ∈ Finset.Icc 1 d, χ a * f a = ∑ a ∈ Finset.Ico 1 d, χ a * f a := by
  have : Nontrivial (ZMod d) := ZMod.nontrivial_iff.mpr hd
  rw [← Finset.Ico_insert_right (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)),
    Finset.sum_insert Finset.right_notMem_Ico]
  simp [MulChar.map_nonunit χ not_isUnit_zero]

/-- A sum over residues mod $d$ is the sum over the representatives $0, \dots, d-1$. -/
lemma sum_range_eq_sum_zmod (f : ZMod d → ℂ) :
    ∑ a ∈ Finset.range d, f a = ∑ x : ZMod d, f x :=
  Finset.sum_nbij' (fun a : ℕ ↦ (a : ZMod d)) ZMod.val (by simp) (by simp [ZMod.val_lt])
    (fun a ha ↦ ZMod.val_cast_of_lt (Finset.mem_range.mp ha)) (fun x _ ↦ ZMod.natCast_zmod_val x)
    (fun _ _ ↦ rfl)

/-- For a character $\chi$ mod $d > 1$, $\sum_{a=1}^{d-1} \chi(a)\,f(a)$ is the sum over all
residues (the residue $0$ contributes $\chi(0) = 0$). -/
lemma sum_Ico_eq_sum_zmod {χ : DirichletCharacter ℂ d} (hd : d ≠ 1) (f : ZMod d → ℂ) :
    ∑ a ∈ Finset.Ico 1 d, χ a * f a = ∑ x : ZMod d, χ x * f x := by
  have : Nontrivial (ZMod d) := ZMod.nontrivial_iff.mpr hd
  rw [← sum_range_eq_sum_zmod, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (Nat.pos_of_ne_zero (NeZero.ne d))]
  simp [MulChar.map_nonunit χ not_isUnit_zero]

/-- $\sum_{a=1}^{d-1}\chi(a) = 0$ for a nontrivial character. -/
lemma sum_Ico_eq_zero {χ : DirichletCharacter ℂ d} (hχ1 : χ ≠ 1) :
    ∑ a ∈ Finset.Ico 1 d, χ a = 0 := by
  have hd1 : d ≠ 1 := fun h ↦ hχ1 (χ.level_one' h)
  have h := sum_Ico_eq_sum_zmod (χ := χ) hd1 (fun _ ↦ 1)
  simp only [mul_one] at h
  rw [h, MulChar.sum_eq_zero_of_ne_one hχ1]

/-- **Theorem 4.12 (ii)**, right equality of (4.26), for $k \ge 2$: for a nontrivial
Dirichlet character $\chi$ modulo $d$ (Shimura's $\overline\chi$; primitivity and parity are not
needed for this equality),
$$k\,d^{1-k}\,L(1-k,\chi) = -\sum_{a=1}^{d-1}\chi(a)\,B_k(a/d).$$
From Miyake's $L(1-k,\chi) = -B_{k,\chi}/k$ (`ModularFormsKB.Miyake.LFunction_one_sub_nat`).
The case $k = 1$ is `LZeroValueStatement`. -/
@[kb "shimura2007" "Theorem 4.12 (ii), (4.26), p. 32"]
theorem nat_mul_LFunction_one_sub {χ : DirichletCharacter ℂ d} (hχ1 : χ ≠ 1) {k : ℕ}
    (hk : 2 ≤ k) :
    k * ((d : ℂ) ^ (k - 1))⁻¹ * LFunction χ (1 - k) =
      -∑ a ∈ Finset.Ico 1 d, χ a * bernoulliPoly k ((a : ℂ) / d) := by
  have hd1 : d ≠ 1 := fun h ↦ hχ1 (χ.level_one' h)
  rw [Miyake.LFunction_one_sub_nat χ hk, Miyake.generalizedBernoulli,
    sum_Icc_eq_sum_Ico hd1 (fun a ↦ bernoulliPoly k ((a : ℂ) / d))]
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hz : (d : ℂ) ^ ((k : ℤ) - 1) = (d : ℂ) ^ (k - 1) := by
    rw [← zpow_natCast, Nat.cast_sub (by omega : 1 ≤ k)]; rfl
  rw [hz]
  field_simp

/-- **Theorem 4.12 (ii)**, (4.26) in full for $k \ge 2$: for a nontrivial primitive Dirichlet
character $\chi$ modulo $d$ and $k \ge 2$ with $\chi(-1) = (-1)^k$,
$$2\cdot k!\,(2\pi i)^{-k}G(\overline\chi)L(k,\chi) = k\,d^{1-k}L(1-k,\overline\chi)
  = -\sum_{a=1}^{d-1}\overline\chi(a)B_k(a/d).$$ -/
@[kb "shimura2007" "Theorem 4.12 (ii), (4.26), p. 32"]
theorem theorem_4_12_ii {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    {k : ℕ} (hk : 2 ≤ k) (hpar : χ (-1) = (-1) ^ k) :
    (2 * (k.factorial : ℂ) * ((2 * π * I) ^ k)⁻¹ * gaussSum χ⁻¹ ZMod.stdAddChar *
        LFunction χ k = k * ((d : ℂ) ^ (k - 1))⁻¹ * LFunction χ⁻¹ (1 - k)) ∧
      (k * ((d : ℂ) ^ (k - 1))⁻¹ * LFunction χ⁻¹ (1 - k) =
        -∑ a ∈ Finset.Ico 1 d, χ⁻¹ a * bernoulliPoly k ((a : ℂ) / d)) :=
  ⟨two_mul_factorial_gaussSum_mul_LFunction hχ hχ1 (by omega) hpar,
    nat_mul_LFunction_one_sub (inv_ne_one.mpr hχ1) hk⟩

/-- **Theorem 4.12 (ii)**, (4.26) at $k = 1$ and the right equality of (4.27), **stated, not
proved**: for a nontrivial Dirichlet character $\chi$ modulo $d$,
$$L(0,\chi) = -\sum_{a=1}^{d-1}\chi(a)\,B_1(a/d) = -\sum_{a=1}^{d-1}\chi(a)\,a/d$$
(the two sums agree as $\sum_a \chi(a) = 0$). The missing input is the value
$\zeta(0, x) = 1/2 - x$ of the Hurwitz zeta function for $0 < x < 1$ (Mathlib has its values at
$s = -n$, $n \ge 1$, only). Shimura proves the case $k = 1$ by Lemma 4.3 (ii) (conditional
convergence of $\sum \chi(h) h^{-s}$ on $s > 1/2$). -/
@[kb "shimura2007" "Theorem 4.12 (ii), (4.27), p. 32"]
def LZeroValueStatement : Prop :=
  ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), χ ≠ 1 →
    LFunction χ 0 = -∑ a ∈ Finset.Ico 1 d, χ a * bernoulliPoly 1 ((a : ℂ) / d)

/-- **Theorem 4.12 (ii)**, (4.27), conditional on `LZeroValueStatement`: for a primitive odd
character $\chi$ modulo $d$,
$(\pi i)^{-1}G(\chi)L(1,\overline\chi) = L(0,\chi) = -\sum_{a=1}^{d-1}\chi(a)\,a/d$. The left
equality is unconditional (`two_mul_factorial_gaussSum_mul_LFunction` at $k = 1$). -/
@[kb "shimura2007" "Theorem 4.12 (ii), (4.27), p. 32"]
theorem theorem_4_12_ii_one (hL0 : LZeroValueStatement) {χ : DirichletCharacter ℂ d}
    (hχ : χ.IsPrimitive) (hodd : χ (-1) = -1) :
    ((π * I)⁻¹ * gaussSum χ ZMod.stdAddChar * LFunction χ⁻¹ 1 = LFunction χ 0) ∧
      LFunction χ 0 = -∑ a ∈ Finset.Ico 1 d, χ a * ((a : ℂ) / d) := by
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    have : Nontrivial (ZMod d) := by
      refine ZMod.nontrivial_iff.mpr fun h ↦ ?_
      subst h
      exact absurd hodd (by simp; norm_num)
    exact absurd hodd (by rw [MulChar.one_apply (isUnit_one.neg)]; norm_num)
  have hψ : (χ⁻¹).IsPrimitive := by
    rwa [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
  have hψ1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ1
  have hparψ : χ⁻¹ (-1) = (-1) ^ 1 := by
    rw [MulChar.inv_apply_eq_inv', hodd, pow_one, inv_neg, inv_one]
  have h1 := two_mul_factorial_gaussSum_mul_LFunction hψ hψ1 le_rfl hparψ
  rw [inv_inv] at h1
  refine ⟨?_, ?_⟩
  · simp only [Nat.factorial_one, Nat.cast_one, pow_one, Nat.sub_self, pow_zero, inv_one,
      mul_one, one_mul, sub_self] at h1
    rw [← h1]
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  · rw [hL0 d χ hχ1]
    have hd1 : d ≠ 1 := fun h ↦ hχ1 (χ.level_one' h)
    have : Nontrivial (ZMod d) := ZMod.nontrivial_iff.mpr hd1
    have hsum0 : ∑ a ∈ Finset.Ico 1 d, χ a = 0 := sum_Ico_eq_zero hχ1
    have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    have hB1 : ∀ t : ℂ, bernoulliPoly 1 t = t - 1 / 2 := by
      intro t; simp [bernoulliPoly, Polynomial.bernoulli_one]
    simp only [hB1, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum0, zero_mul, sub_zero]

end RightEquality

end ModularFormsKB.Shimura2007
