import ModularFormsKB.Shimura2007.Ch2.CriticalValues

/-!
# Shimura 2007, §4.11 continued: Lemma 4.13, Theorem 4.14 (i), Corollary 4.16

G. Shimura, *Elementary Dirichlet Series and Modular Forms* (Springer 2007), pp. 33–38.

Throughout, $\chi$ is a nontrivial primitive Dirichlet character modulo $d$, $q = [(d-1)/2]$ is
`(d - 1) / 2` (natural division), sums over $a = 1,\dots,d-1$ are `∑ a ∈ Finset.Ico 1 d` and sums
over $a = 1,\dots,q$ are `∑ a ∈ Finset.Icc 1 ((d - 1) / 2)`. Shimura's $\overline\chi$ is `χ⁻¹`.

**Results.**
* Lemma 4.13 (i), (4.28): `sum_bernoulli_eq_two_mul_halfSum`, `sum_bernoulli_eq_zero_of_pred`.
* Lemma 4.13 (iv), (4.31a)–(4.31d) for $\chi(-1) = 1$: `sum_halfRange_eq_zero`,
  `sum_mul_self_eq_zero`, `sum_alternating_eq_zero`, `sum_mul_cube_eq`.
* Theorem 4.14 (i), (4.33): `theorem_4_14_i`.
* Corollary 4.16, (4.46): `corollary_4_16`.
-/

open Complex DirichletCharacter
open scoped Real

namespace ModularFormsKB.Shimura2007

section Reflection

variable {d : ℕ}

/-- Reflection $a \mapsto d - a$ on $\{1,\dots,d-1\}$ leaves a sum unchanged. -/
lemma sum_Ico_reflect_self (F : ℕ → ℂ) :
    ∑ a ∈ Finset.Ico 1 d, F (d - a) = ∑ a ∈ Finset.Ico 1 d, F a := by
  refine Finset.sum_nbij' (fun a ↦ d - a) (fun a ↦ d - a) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Ico] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Ico] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Ico] at ha; omega
  · intro a ha; simp only [Finset.mem_Ico] at ha; omega
  · intro a _; rfl

/-- If $F(d-a) = F(a)$ on $1 \le a < d$ and $F(d/2) = 0$ for even $d$, then
$\sum_{a=1}^{d-1} F(a) = 2\sum_{a=1}^{q} F(a)$ with $q = [(d-1)/2]$. -/
lemma sum_Ico_eq_two_mul_Icc (hd : 0 < d) (F : ℕ → ℂ)
    (hs : ∀ a, 1 ≤ a → a < d → F (d - a) = F a) (hmid : Even d → F (d / 2) = 0) :
    ∑ a ∈ Finset.Ico 1 d, F a = 2 * ∑ a ∈ Finset.Icc 1 ((d - 1) / 2), F a := by
  obtain ⟨q, hq⟩ : ∃ q, q = (d - 1) / 2 := ⟨_, rfl⟩
  rw [← hq]
  have hI : Finset.Icc 1 q = Finset.Ico 1 (q + 1) := by
    ext a; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hsplit : ∑ a ∈ Finset.Ico 1 d, F a =
      ∑ a ∈ Finset.Ico 1 (q + 1), F a + ∑ a ∈ Finset.Ico (q + 1) d, F a :=
    (Finset.sum_Ico_consecutive F (by omega) (by omega)).symm
  have hrefl : ∑ a ∈ Finset.Ico (q + 1) d, F a = ∑ a ∈ Finset.Ico 1 (d - q), F a := by
    refine Finset.sum_nbij' (fun a ↦ d - a) (fun a ↦ d - a) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Ico] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Ico] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Ico] at ha; omega
    · intro a ha; simp only [Finset.mem_Ico] at ha; omega
    · intro a ha
      simp only [Finset.mem_Ico] at ha
      exact (hs a (by omega) ha.2).symm
  rw [hsplit, hrefl, hI]
  rcases Nat.even_or_odd d with he | ho
  · have h1 : d - q = (q + 1) + 1 := by obtain ⟨r, hr⟩ := he; omega
    have h2 : q + 1 = d / 2 := by obtain ⟨r, hr⟩ := he; omega
    have h3 : F (q + 1) = 0 := by rw [h2]; exact hmid he
    rw [h1, Finset.sum_Ico_succ_top (show 1 ≤ q + 1 by omega) F, h3]
    ring
  · have h1 : d - q = q + 1 := by obtain ⟨r, hr⟩ := ho; omega
    rw [h1]; ring

end Reflection

section Characters

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- $\chi(d-a) = \chi(-1)\chi(a)$ for $a \le d$. -/
lemma char_sub {χ : DirichletCharacter ℂ d} {a : ℕ} (ha : a ≤ d) :
    χ ((d - a : ℕ) : ZMod d) = χ (-1) * χ (a : ZMod d) := by
  rw [Nat.cast_sub ha, ZMod.natCast_self, zero_sub, neg_eq_neg_one_mul, map_mul]

/-- For even $d$ and a nontrivial character $\chi$ modulo $d$, $\chi(d/2) = 0$ (as $d/2$ is not
a unit modulo $d$; there is no nontrivial character modulo $2$). -/
lemma char_half_eq_zero {χ : DirichletCharacter ℂ d} (hχ1 : χ ≠ 1) (he : Even d) :
    χ ((d / 2 : ℕ) : ZMod d) = 0 := by
  apply MulChar.map_nonunit
  intro hu
  obtain ⟨m, hm⟩ := he
  have hd1 : d ≠ 1 := fun h ↦ hχ1 (χ.level_one' h)
  have hdm : d / 2 = m := by omega
  rw [hdm] at hu
  have h2 : (2 : ZMod d) * (m : ZMod d) = 0 := by
    have : ((m + m : ℕ) : ZMod d) = 0 := by rw [← hm]; exact ZMod.natCast_self d
    push_cast at this
    linear_combination this
  have h2' : (2 : ZMod d) = 0 := hu.mul_left_eq_zero.mp h2
  have hdvd : d ∣ 2 := by
    have : ((2 : ℕ) : ZMod d) = 0 := by exact_mod_cast h2'
    exact (ZMod.natCast_eq_zero_iff 2 d).mp this
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have hd2 : d = 2 := by have := NeZero.ne d; omega
  subst hd2
  apply hχ1
  ext a
  have ha : a = 1 := by revert a; decide
  subst ha
  simp

omit [NeZero d] in
/-- $\sum_{a=1}^{d-1}F(\chi(a))$-type sums: the cast of $d - a$ to $\mathbb C$. -/
lemma natCast_sub_complex {a : ℕ} (ha : a ≤ d) : ((d - a : ℕ) : ℂ) = (d : ℂ) - a := by
  rw [Nat.cast_sub ha]

end Characters

/-! ## Lemma 4.13 (i) -/

/-- $B_n(1-t) = (-1)^nB_n(t)$ for the Bernoulli polynomial over $\mathbb C$. -/
lemma bernoulliPoly_one_sub (n : ℕ) (x : ℂ) :
    bernoulliPoly n (1 - x) = (-1) ^ n * bernoulliPoly n x := by
  have h := congr(Polynomial.aeval x $(Polynomial.bernoulli_comp_one_sub_X n))
  simp only [bernoulliPoly, Polynomial.eval_map_algebraMap]
  rw [Polynomial.aeval_comp] at h
  simpa using h

section Lemma413

variable {d : ℕ} [NeZero d]

private lemma bernoulli_term_reflect {χ : DirichletCharacter ℂ d} (n : ℕ) {a : ℕ} (ha : a < d) :
    χ ((d - a : ℕ) : ZMod d) * bernoulliPoly n (((d - a : ℕ) : ℂ) / d) =
      χ (-1) * (-1) ^ n * (χ (a : ZMod d) * bernoulliPoly n ((a : ℂ) / d)) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have h1 : ((d - a : ℕ) : ℂ) / d = 1 - (a : ℂ) / d := by
    rw [natCast_sub_complex ha.le]; field_simp
  rw [char_sub ha.le, h1, bernoulliPoly_one_sub]
  ring

/-- **Lemma 4.13 (i)**, (4.28), case $n = k$: for a nontrivial primitive $\chi$ modulo $d$ with
$\chi(-1) = (-1)^k$,
$$\sum_{a=1}^{d-1}\chi(a)B_k(a/d) = 2\sum_{a=1}^{q}\chi(a)B_k(a/d).$$ -/
@[kb "shimura2007" "Lemma 4.13 (i), (4.28), p. 33"]
theorem sum_bernoulli_eq_two_mul_halfSum {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {k : ℕ} (hk : 1 ≤ k) (hpar : χ (-1) = (-1) ^ k) :
    ∑ a ∈ Finset.Ico 1 d, χ a * bernoulliPoly k ((a : ℂ) / d) =
      2 * ∑ a ∈ Finset.Icc 1 ((d - 1) / 2), χ a * bernoulliPoly k ((a : ℂ) / d) := by
  refine sum_Ico_eq_two_mul_Icc (Nat.pos_of_ne_zero (NeZero.ne d)) _ ?_ ?_
  · intro a _ ha
    rw [bernoulli_term_reflect k ha, hpar, ← mul_pow]
    simp
  · intro he
    rw [char_half_eq_zero hχ1 he, zero_mul]

/-- **Lemma 4.13 (i)**, (4.28), case $n = k - 1$: for a nontrivial primitive $\chi$ modulo $d$
with $\chi(-1) = (-1)^k$, $k \ge 1$,
$$\sum_{a=1}^{d-1}\chi(a)B_{k-1}(a/d) = 0.$$ -/
@[kb "shimura2007" "Lemma 4.13 (i), (4.28), p. 33"]
theorem sum_bernoulli_eq_zero_of_pred {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {k : ℕ} (hk : 1 ≤ k) (hpar : χ (-1) = (-1) ^ k) :
    ∑ a ∈ Finset.Ico 1 d, χ a * bernoulliPoly (k - 1) ((a : ℂ) / d) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set S := ∑ a ∈ Finset.Ico 1 d, χ a * bernoulliPoly j ((a : ℂ) / d) with hS
  have h := sum_Ico_reflect_self (d := d)
    (fun a ↦ χ (a : ZMod d) * bernoulliPoly j ((a : ℂ) / d))
  have h2 : ∑ a ∈ Finset.Ico 1 d,
      χ ((d - a : ℕ) : ZMod d) * bernoulliPoly j (((d - a : ℕ) : ℂ) / d) = -S := by
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    rw [bernoulli_term_reflect j (Finset.mem_Ico.mp ha).2, hpar]
    have hp : ((-1 : ℂ) ^ j) * ((-1) ^ j) = 1 := by rw [← mul_pow]; simp
    have : ((-1 : ℂ) ^ (j + 1) * (-1) ^ j) = -1 := by
      rw [pow_succ]; linear_combination (-1 : ℂ) * hp
    rw [this]; ring
  rw [h2] at h
  exact self_eq_neg.mp h.symm

/-! ## Lemma 4.13 (iv) -/

private lemma char_reflect {χ : DirichletCharacter ℂ d} (hpar : χ (-1) = 1) {a : ℕ} (ha : a ≤ d) :
    χ ((d - a : ℕ) : ZMod d) = χ (a : ZMod d) := by
  rw [char_sub ha, hpar, one_mul]

/-- **Lemma 4.13 (iv)**, (4.31a): for a nontrivial primitive even $\chi$ modulo $d$,
$\sum_{a=1}^{q}\chi(a) = 0$. -/
@[kb "shimura2007" "Lemma 4.13 (iv), (4.31a), p. 34"]
theorem sum_halfRange_eq_zero {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) (hpar : χ (-1) = 1) :
    ∑ a ∈ Finset.Icc 1 ((d - 1) / 2), χ a = 0 := by
  have h := sum_Ico_eq_two_mul_Icc (Nat.pos_of_ne_zero (NeZero.ne d))
    (fun a ↦ χ (a : ZMod d)) (fun a _ ha ↦ char_reflect hpar ha.le)
    (fun he ↦ char_half_eq_zero hχ1 he)
  rw [sum_Ico_eq_zero hχ1] at h
  have : (2 : ℂ) * ∑ a ∈ Finset.Icc 1 ((d - 1) / 2), χ a = 0 := h.symm
  simpa using this

/-- **Lemma 4.13 (iv)**, (4.31b): for a nontrivial primitive even $\chi$ modulo $d$,
$\sum_{a=1}^{d-1}\chi(a)\,a = 0$. -/
@[kb "shimura2007" "Lemma 4.13 (iv), (4.31b), p. 34"]
theorem sum_mul_self_eq_zero {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) (hpar : χ (-1) = 1) :
    ∑ a ∈ Finset.Ico 1 d, χ a * (a : ℂ) = 0 := by
  have h := sum_Ico_reflect_self (d := d) (fun a ↦ χ (a : ZMod d) * (a : ℂ))
  have h2 : ∑ a ∈ Finset.Ico 1 d, χ ((d - a : ℕ) : ZMod d) * ((d - a : ℕ) : ℂ) =
      (d : ℂ) * ∑ a ∈ Finset.Ico 1 d, χ a - ∑ a ∈ Finset.Ico 1 d, χ a * (a : ℂ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    have ha' := (Finset.mem_Ico.mp ha).2
    rw [char_reflect hpar ha'.le, natCast_sub_complex ha'.le]
    ring
  rw [h2, sum_Ico_eq_zero hχ1] at h
  linear_combination (-1 / 2 : ℂ) * h

/-- **Lemma 4.13 (iv)**, (4.31c): for a nontrivial primitive even $\chi$ modulo an odd $d$,
$\sum_{a=1}^{d-1}(-1)^a\chi(a) = 0$. -/
@[kb "shimura2007" "Lemma 4.13 (iv), (4.31c), p. 34"]
theorem sum_alternating_eq_zero {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) (hpar : χ (-1) = 1) (hodd : Odd d) :
    ∑ a ∈ Finset.Ico 1 d, (-1 : ℂ) ^ a * χ a = 0 := by
  have h := sum_Ico_reflect_self (d := d) (fun a ↦ (-1 : ℂ) ^ a * χ (a : ZMod d))
  have h2 : ∑ a ∈ Finset.Ico 1 d, (-1 : ℂ) ^ (d - a) * χ ((d - a : ℕ) : ZMod d) =
      -∑ a ∈ Finset.Ico 1 d, (-1 : ℂ) ^ a * χ a := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    have ha' := (Finset.mem_Ico.mp ha).2
    rw [char_reflect hpar ha'.le]
    have e1 : (-1 : ℂ) ^ (d - a) * (-1) ^ a = -1 := by
      rw [← pow_add, Nat.sub_add_cancel ha'.le, hodd.neg_one_pow]
    have e2 : (-1 : ℂ) ^ a * (-1) ^ a = 1 := by
      rw [← mul_pow]; simp
    have e3 : (-1 : ℂ) ^ (d - a) = -(-1) ^ a := by
      linear_combination (-((-1 : ℂ) ^ (d - a))) * e2 + ((-1 : ℂ) ^ a) * e1
    rw [e3]; ring
  rw [h2] at h
  exact self_eq_neg.mp h.symm

/-- **Lemma 4.13 (iv)**, (4.31d): for a nontrivial primitive even $\chi$ modulo $d$,
$\sum_{a=1}^{d-1}\chi(a)a^3 = \frac{3d}{2}\sum_{a=1}^{d-1}\chi(a)a^2$. -/
@[kb "shimura2007" "Lemma 4.13 (iv), (4.31d), p. 34"]
theorem sum_mul_cube_eq {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) (hpar : χ (-1) = 1) :
    ∑ a ∈ Finset.Ico 1 d, χ a * (a : ℂ) ^ 3 =
      3 * d / 2 * ∑ a ∈ Finset.Ico 1 d, χ a * (a : ℂ) ^ 2 := by
  have h := sum_Ico_reflect_self (d := d) (fun a ↦ χ (a : ZMod d) * (a : ℂ) ^ 3)
  have h0 := sum_Ico_eq_zero hχ1 (χ := χ)
  have h1 := sum_mul_self_eq_zero hχ hχ1 hpar
  have h2 : ∑ a ∈ Finset.Ico 1 d, χ ((d - a : ℕ) : ZMod d) * ((d - a : ℕ) : ℂ) ^ 3 =
      (d : ℂ) ^ 3 * ∑ a ∈ Finset.Ico 1 d, χ a
        - 3 * (d : ℂ) ^ 2 * ∑ a ∈ Finset.Ico 1 d, χ a * (a : ℂ)
        + 3 * (d : ℂ) * ∑ a ∈ Finset.Ico 1 d, χ a * (a : ℂ) ^ 2
        - ∑ a ∈ Finset.Ico 1 d, χ a * (a : ℂ) ^ 3 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    have ha' := (Finset.mem_Ico.mp ha).2
    rw [char_reflect hpar ha'.le, natCast_sub_complex ha'.le]
    ring
  rw [h2, h0, h1] at h
  linear_combination (-1 / 2 : ℂ) * h

end Lemma413

/-! ## Theorem 4.14 (i) and Corollary 4.16 -/

section Theorem414

variable {d : ℕ} [NeZero d]

/-- **Theorem 4.14 (i)**, (4.33), for $k \ge 2$: for a nontrivial primitive $\chi$ modulo $d$
with $\chi(-1) = (-1)^k$,
$$k!\,(2\pi i)^{-k}\,G(\overline\chi)\,L(k,\chi) = -\sum_{a=1}^{q}\overline\chi(a)B_k(a/d).$$ -/
@[kb "shimura2007" "Theorem 4.14 (i), (4.33), p. 35"]
theorem theorem_4_14_i {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    {k : ℕ} (hk : 2 ≤ k) (hpar : χ (-1) = (-1) ^ k) :
    (k.factorial : ℂ) * ((2 * π * I) ^ k)⁻¹ * gaussSum χ⁻¹ ZMod.stdAddChar * LFunction χ k =
      -∑ a ∈ Finset.Icc 1 ((d - 1) / 2), χ⁻¹ a * bernoulliPoly k ((a : ℂ) / d) := by
  have hψ : (χ⁻¹).IsPrimitive := by
    rwa [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
  have hψ1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ1
  have hparψ : χ⁻¹ (-1) = (-1) ^ k := by
    rw [MulChar.inv_apply_eq_inv', hpar, ← inv_pow, inv_neg, inv_one]
  have h := theorem_4_12_ii hχ hχ1 hk hpar
  have e := h.1.trans h.2
  have e2 := sum_bernoulli_eq_two_mul_halfSum hψ hψ1 (by omega) hparψ
  linear_combination (1 / 2 : ℂ) * e - (1 / 2 : ℂ) * e2

/-- **Corollary 4.16**, (4.46): for a nontrivial primitive even character $\chi$ modulo $d$,
$$\pi^{-2}\,G(\overline\chi)\,L(2,\chi) = d^{-2}\sum_{a=1}^{d-1}\overline\chi(a)\,a^2.$$ -/
@[kb "shimura2007" "Corollary 4.16, (4.46), p. 38"]
theorem corollary_4_16 {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (hpar : χ (-1) = 1) :
    ((π : ℂ) ^ 2)⁻¹ * gaussSum χ⁻¹ ZMod.stdAddChar * LFunction χ 2 =
      ((d : ℂ) ^ 2)⁻¹ * ∑ a ∈ Finset.Ico 1 d, χ⁻¹ a * (a : ℂ) ^ 2 := by
  have hψ : (χ⁻¹).IsPrimitive := by
    rwa [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
  have hψ1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ1
  have hparψ : χ⁻¹ (-1) = 1 := by
    rw [MulChar.inv_apply_eq_inv', hpar, inv_one]
  have h := theorem_4_12_ii hχ hχ1 (k := 2) le_rfl (by rw [hpar]; norm_num)
  have e := h.1.trans h.2
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hB : ∀ t : ℂ, bernoulliPoly 2 t = t ^ 2 - t + 1 / 6 := by
    intro t
    simp [bernoulliPoly, Polynomial.bernoulli_def, Finset.sum_range_succ]
    ring
  have h0 := sum_Ico_eq_zero hψ1
  have h1 := sum_mul_self_eq_zero hψ hψ1 hparψ
  have hsum : ∑ a ∈ Finset.Ico 1 d, χ⁻¹ a * bernoulliPoly 2 ((a : ℂ) / d) =
      ((d : ℂ) ^ 2)⁻¹ * ∑ a ∈ Finset.Ico 1 d, χ⁻¹ a * (a : ℂ) ^ 2
        - (d : ℂ)⁻¹ * ∑ a ∈ Finset.Ico 1 d, χ⁻¹ a * (a : ℂ)
        + 1 / 6 * ∑ a ∈ Finset.Ico 1 d, χ⁻¹ a := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, hB]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    field_simp
  rw [hsum, h0, h1] at e
  have hI : ((2 * (π : ℂ) * I) ^ 2)⁻¹ = -(4 * (π : ℂ) ^ 2)⁻¹ := by
    rw [mul_pow, mul_pow, I_sq]; field_simp; ring
  simp only [Nat.factorial, Nat.cast_ofNat, Nat.succ_eq_add_one] at e
  norm_num at e
  rw [hI] at e
  have : ((π : ℂ) ^ 2)⁻¹ = 4 * (4 * (π : ℂ) ^ 2)⁻¹ := by field_simp
  rw [this]
  linear_combination (-1 : ℂ) * e

end Theorem414

/-! ## Theorem 4.15 (i) -/

section Theorem415

variable {d : ℕ} [NeZero d]

/-- Shimura's $A(k,\chi) = 2\cdot k!\,(2\pi i)^{-k}\,G(\overline\chi)\,L(k,\chi)$ of (4.41). -/
@[kb "shimura2007" "Theorem 4.15 (i), (4.41), p. 37"]
noncomputable def shimuraA (χ : DirichletCharacter ℂ d) (k : ℕ) : ℂ :=
  2 * (k.factorial : ℂ) * ((2 * π * I) ^ k)⁻¹ * gaussSum χ⁻¹ ZMod.stdAddChar * LFunction χ k

/-- Parity of $(-1)^a$ depends only on $a + b$ being even. -/
private lemma neg_one_pow_congr {a b : ℕ} (h : (a + b) % 2 = 0) :
    (-1 : ℂ) ^ a = (-1) ^ b := by
  by_cases ha : a % 2 = 0
  · rw [(Nat.even_iff.mpr ha).neg_one_pow, (Nat.even_iff.mpr (by omega : b % 2 = 0)).neg_one_pow]
  · rw [(Nat.odd_iff.mpr (by omega : a % 2 = 1)).neg_one_pow,
      (Nat.odd_iff.mpr (by omega : b % 2 = 1)).neg_one_pow]

/-- Reindexing: if $S$ vanishes at $0$ and at $\mu \not\equiv k \pmod 2$, then
$\sum_{\mu=0}^{k}\binom{k+1}{\mu}S(\mu) = (k+1)S(k) + \sum_{\nu=1}^{m}\binom{k+1}{2\nu+1}S(k-2\nu)$,
$m = [(k-1)/2]$. -/
lemma sum_choose_reindex (S : ℕ → ℂ) {k : ℕ} (hk : 1 ≤ k)
    (hS : ∀ μ, μ ≤ k → (μ = 0 ∨ (k + μ) % 2 = 1) → S μ = 0) :
    ∑ μ ∈ Finset.range (k + 1), ((k + 1).choose μ : ℂ) * S μ =
      (k + 1) * S k + ∑ ν ∈ Finset.Icc 1 ((k - 1) / 2), ((k + 1).choose (2 * ν + 1) : ℂ) *
        S (k - 2 * ν) := by
  rw [Finset.sum_range_succ, Nat.choose_succ_self_right]
  have hinj : Set.InjOn (fun ν : ℕ ↦ k - 2 * ν) (Finset.Icc 1 ((k - 1) / 2) : Set ℕ) := by
    intro x hx y hy hxy
    simp only [Finset.coe_Icc, Set.mem_Icc] at hx hy
    simp only at hxy
    omega
  have h1 : ∑ ν ∈ Finset.Icc 1 ((k - 1) / 2), ((k + 1).choose (2 * ν + 1) : ℂ) * S (k - 2 * ν) =
      ∑ μ ∈ (Finset.Icc 1 ((k - 1) / 2)).image (fun ν ↦ k - 2 * ν),
        ((k + 1).choose μ : ℂ) * S μ := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun ν hν ↦ ?_
    simp only [Finset.mem_Icc] at hν
    rw [Nat.choose_symm_of_eq_add (show k + 1 = (k - 2 * ν) + (2 * ν + 1) by omega)]
  rw [h1, Finset.sum_subset (s₁ := (Finset.Icc 1 ((k - 1) / 2)).image (fun ν ↦ k - 2 * ν))
    (s₂ := Finset.range k)]
  · rw [add_comm]; push_cast; ring
  · intro μ hμ
    simp only [Finset.mem_image, Finset.mem_Icc] at hμ
    obtain ⟨ν, hν, rfl⟩ := hμ
    simp only [Finset.mem_range]; omega
  · intro μ hμ hn
    simp only [Finset.mem_range] at hμ
    have : S μ = 0 := by
      apply hS μ (by omega)
      by_contra hc
      push_neg at hc
      apply hn
      simp only [Finset.mem_image, Finset.mem_Icc]
      exact ⟨(k - μ) / 2, ⟨by omega, by omega⟩, by omega⟩
    rw [this, mul_zero]

/-- $\sum_{\mu=0}^{k}\binom{k+1}{\mu}\sum_a\psi(a)B_\mu(a/d) = (k+1)d^{-k}\sum_a\psi(a)a^k$
(Mathlib's `Polynomial.sum_bernoulli`). -/
lemma sum_choose_bernoulli (ψ : DirichletCharacter ℂ d) (k : ℕ) :
    ∑ μ ∈ Finset.range (k + 1), ((k + 1).choose μ : ℂ) *
        ∑ a ∈ Finset.Ico 1 d, ψ a * bernoulliPoly μ ((a : ℂ) / d) =
      (k + 1) * (((d : ℂ) ^ k)⁻¹ * ∑ a ∈ Finset.Ico 1 d, ψ a * (a : ℂ) ^ k) := by
  have hB : ∀ t : ℂ, ∑ μ ∈ Finset.range (k + 1), ((k + 1).choose μ : ℂ) * bernoulliPoly μ t =
      (k + 1) * t ^ k := by
    intro t
    have h := congr(Polynomial.aeval t $(Polynomial.sum_bernoulli k))
    simp only [map_sum, Polynomial.aeval_monomial, map_smul] at h
    simp only [bernoulliPoly, Polynomial.eval_map_algebraMap]
    simp only [Algebra.smul_def, eq_ratCast, Rat.cast_natCast, map_natCast] at h
    simpa [Algebra.algebraMap_eq_smul_one] using h
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  have := hB ((a : ℂ) / d)
  calc ∑ μ ∈ Finset.range (k + 1), ((k + 1).choose μ : ℂ) * (ψ a * bernoulliPoly μ ((a : ℂ) / d))
      = ψ a * ∑ μ ∈ Finset.range (k + 1), ((k + 1).choose μ : ℂ) * bernoulliPoly μ ((a : ℂ) / d) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    _ = _ := by rw [this, div_pow]; ring

/-- (4.26) in the form $A(j,\chi) = -\sum_a\overline\chi(a)B_j(a/d)$, for $j \ge 2$, or $j = 1$
assuming `LZeroValueStatement`. -/
lemma shimuraA_eq_neg_sum {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    {j : ℕ} (hj : 1 ≤ j) (hpar : χ (-1) = (-1) ^ j) (hj' : 2 ≤ j ∨ LZeroValueStatement) :
    shimuraA χ j = -∑ a ∈ Finset.Ico 1 d, χ⁻¹ a * bernoulliPoly j ((a : ℂ) / d) := by
  by_cases h2 : 2 ≤ j
  · exact (theorem_4_12_ii hχ hχ1 h2 hpar).1.trans (theorem_4_12_ii hχ hχ1 h2 hpar).2
  · obtain rfl : j = 1 := by omega
    have hL0 : LZeroValueStatement := hj'.resolve_left h2
    have h := two_mul_factorial_gaussSum_mul_LFunction hχ hχ1 le_rfl hpar
    unfold shimuraA
    rw [h]
    simp only [Nat.cast_one, Nat.sub_self, pow_zero, inv_one, mul_one, one_mul, sub_self]
    exact hL0 d χ⁻¹ (inv_ne_one.mpr hχ1)

/-- **Theorem 4.15 (i)**, (4.42): for a nontrivial primitive $\chi$ modulo $d$, $k \ge 1$ with
$\chi(-1) = (-1)^k$ and $m = [(k-1)/2]$,
$$A(k,\chi) = -d^{-k}\sum_{a=1}^{d-1}\overline\chi(a)a^k
  - \frac1{k+1}\sum_{\nu=1}^{m}\binom{k+1}{2\nu+1}A(k-2\nu,\chi).$$
For odd $k$ the term $A(1,\chi)$ needs (4.27), assumed as `LZeroValueStatement`. -/
@[kb "shimura2007" "Theorem 4.15 (i), (4.42), p. 37"]
theorem theorem_4_15_i {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) (hpar : χ (-1) = (-1) ^ k) (hk' : Even k ∨ LZeroValueStatement) :
    shimuraA χ k = -((d : ℂ) ^ k)⁻¹ * ∑ a ∈ Finset.Ico 1 d, χ⁻¹ a * (a : ℂ) ^ k
      - ((k : ℂ) + 1)⁻¹ * ∑ ν ∈ Finset.Icc 1 ((k - 1) / 2),
          ((k + 1).choose (2 * ν + 1) : ℂ) * shimuraA χ (k - 2 * ν) := by
  have hψ : (χ⁻¹).IsPrimitive := by
    rwa [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
  have hψ1 : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ1
  have hparψ : χ⁻¹ (-1) = (-1) ^ k := by
    rw [MulChar.inv_apply_eq_inv', hpar, ← inv_pow, inv_neg, inv_one]
  set S : ℕ → ℂ := fun μ ↦ ∑ a ∈ Finset.Ico 1 d, χ⁻¹ a * bernoulliPoly μ ((a : ℂ) / d) with hSdef
  -- A(j) = -S j for j ≡ k mod 2, j ≥ 1
  have hA : ∀ j, 1 ≤ j → (k + j) % 2 = 0 → shimuraA χ j = -S j := by
    intro j hj hjk
    refine shimuraA_eq_neg_sum hχ hχ1 hj (hpar.trans (neg_one_pow_congr hjk)) ?_
    rcases hk' with he | hL
    · left
      have : Even j := Nat.even_iff.mpr (by obtain ⟨r, hr⟩ := he; omega)
      obtain ⟨r, hr⟩ := this; omega
    · right; exact hL
  have hvan : ∀ μ, μ ≤ k → (μ = 0 ∨ (k + μ) % 2 = 1) → S μ = 0 := by
    intro μ _ hμ
    rcases hμ with rfl | hodd
    · simp only [hSdef, bernoulliPoly, Polynomial.bernoulli_zero, Polynomial.map_one,
        Polynomial.eval_one, mul_one]
      exact sum_Ico_eq_zero hψ1
    · have hp : χ⁻¹ (-1) = (-1) ^ (μ + 1) :=
        hparψ.trans (neg_one_pow_congr (by omega : (k + (μ + 1)) % 2 = 0))
      have := sum_bernoulli_eq_zero_of_pred (k := μ + 1) hψ hψ1 (by omega) hp
      rw [Nat.add_sub_cancel] at this
      exact this
  have hmain := sum_choose_bernoulli χ⁻¹ k
  have hre := sum_choose_reindex S hk hvan
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hAk := hA k hk (by omega)
  have hsum : ∑ ν ∈ Finset.Icc 1 ((k - 1) / 2), ((k + 1).choose (2 * ν + 1) : ℂ) *
      shimuraA χ (k - 2 * ν) = -∑ ν ∈ Finset.Icc 1 ((k - 1) / 2),
        ((k + 1).choose (2 * ν + 1) : ℂ) * S (k - 2 * ν) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ν hν ↦ ?_
    simp only [Finset.mem_Icc] at hν
    rw [hA (k - 2 * ν) (by omega) (by omega)]; ring
  rw [hsum]
  have e : ((k : ℂ) + 1) * (((d : ℂ) ^ k)⁻¹ * ∑ a ∈ Finset.Ico 1 d, χ⁻¹ a * (a : ℂ) ^ k) =
      ((k : ℂ) + 1) * S k + ∑ ν ∈ Finset.Icc 1 ((k - 1) / 2),
        ((k + 1).choose (2 * ν + 1) : ℂ) * S (k - 2 * ν) := by
    rw [← hmain]
    exact hre
  rw [hAk]
  field_simp
  linear_combination e

/-- **Theorem 4.15 (i)**, (4.42), unconditional for even $k$. -/
@[kb "shimura2007" "Theorem 4.15 (i), (4.42), p. 37"]
theorem theorem_4_15_i_even {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) (hpar : χ (-1) = (-1) ^ k) (he : Even k) :
    shimuraA χ k = -((d : ℂ) ^ k)⁻¹ * ∑ a ∈ Finset.Ico 1 d, χ⁻¹ a * (a : ℂ) ^ k
      - ((k : ℂ) + 1)⁻¹ * ∑ ν ∈ Finset.Icc 1 ((k - 1) / 2),
          ((k + 1).choose (2 * ν + 1) : ℂ) * shimuraA χ (k - 2 * ν) :=
  theorem_4_15_i hχ hχ1 hk hpar (Or.inl he)

end Theorem415

end ModularFormsKB.Shimura2007
