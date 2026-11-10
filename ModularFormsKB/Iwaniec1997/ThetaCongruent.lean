import ModularFormsKB.Iwaniec1997.Theta

/-!
# Iwaniec, Section 10.3: elementary properties of the congruent theta functions

H. Iwaniec, *Topics in Classical Automorphic Forms* (`iwaniec1997`), Section 10.3, pp. 168-169. Page numbers are
printed pages.

$A$ is a symmetric integral $r\times r$ matrix, $P$ a polynomial, $N \ge 1$, and
$\Theta(z;h) = \sum_{m \equiv h\,(N)} P(m)\,e\big(A[m]z/2N^2\big)$ is the congruent theta function (10.3)
(`thetaCongruent`). The class $h$ lies in $\mathcal H = \{h \bmod N : Ah \equiv 0 \pmod N\}$.
These identities hold termwise, so no convergence is needed (for $z$ outside $\mathbb H$ both sides are the junk
value of a divergent sum in the same way).

## Items
- $\Theta(z;h)$ depends only on $h \bmod N$: `thetaCongruent_congr`.
- (10.14) $\Theta(z;-h) = (-1)^\nu\Theta(z;h)$ for $P$ homogeneous of degree $\nu$: `thetaCongruent_neg`.
- **Proposition 10.3**: (10.18) `thetaCongruent_add_two`, (10.19) `thetaCongruent_add_one` (diagonal of $A$ even).
-/

open Complex Matrix MvPolynomial
open scoped Real

noncomputable section

namespace ModularFormsKB.Iwaniec1997

variable {r : ℕ}

/-- Evaluating a homogeneous polynomial at the negative of a point. -/
lemma eval_neg_of_isHomogeneous {ν : ℕ} {P : MvPolynomial (Fin r) ℂ} (hP : P.IsHomogeneous ν)
    (x : Fin r → ℂ) : eval (-x) P = (-1) ^ ν * eval x P := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h1 := hP (mem_support_iff.mp hd)
  simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at h1
  rw [Finsupp.sum] at h1
  have : ∏ i ∈ d.support, (-x) i ^ d i = (-1) ^ ν * ∏ i ∈ d.support, x i ^ d i := by
    rw [← h1, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.neg_apply, neg_pow]
  rw [this]; ring

/-- The quadratic form at an integer vector is the cast of an integer. -/
lemma quadValue_intVec (A : Matrix (Fin r) (Fin r) ℤ) (m : Fin r → ℤ) :
    quadValue (A.map (fun a : ℤ ↦ (a : ℝ))) (intVec m) = ((m ⬝ᵥ (A *ᵥ m) : ℤ) : ℂ) := by
  simp [quadValue, dotProduct, Matrix.mulVec, Matrix.map_apply]

/-- Symmetric matrices: `x ⬝ A y = (A x) ⬝ y`. -/
lemma dot_mulVec_symm {A : Matrix (Fin r) (Fin r) ℤ} (hA : A.IsSymm) (x y : Fin r → ℤ) :
    x ⬝ᵥ (A *ᵥ y) = (A *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq]

/-- Symmetric integral matrices with even diagonal give even quadratic forms. -/
lemma even_quad_of_even_diag {A : Matrix (Fin r) (Fin r) ℤ} (hA : A.IsSymm)
    (hdiag : ∀ i, Even (A i i)) (n : Fin r → ℤ) : Even (n ⬝ᵥ (A *ᵥ n)) := by
  set f : Fin r → Fin r → ℤ := fun i j => n i * A i j * n j with hf
  have hfs : ∀ i j, f i j = f j i := by
    intro i j
    have : A i j = A j i := by simpa using (Matrix.IsSymm.apply hA j i)
    simp only [hf, this]; ring
  have hS : n ⬝ᵥ (A *ᵥ n) = ∑ i, ∑ j, f i j := by
    simp [dotProduct, Matrix.mulVec, hf, Finset.mul_sum, mul_assoc]
  have hpt : ∀ i j, f i j = (if j < i then f i j else 0) + (if j = i then f i j else 0)
      + (if i < j then f i j else 0) := by
    intro i j
    rcases lt_trichotomy j i with h | h | h
    · simp [h, h.ne, h.not_gt]
    · simp [h]
    · simp [h, h.ne', h.not_gt]
  have hL : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hfs j i]
  have hD : ∑ i, ∑ j, (if j = i then f i j else 0) = ∑ i, f i i := by
    simp
  have hS2 : ∑ i, ∑ j, f i j = (∑ i, ∑ j, (if j < i then f i j else 0))
      + (∑ i, ∑ j, (if j = i then f i j else 0)) + ∑ i, ∑ j, (if i < j then f i j else 0) := by
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j
  rw [hS, hS2, hD, hL]
  have : Even (∑ i, f i i) := by
    refine Finset.even_sum _ fun i _ => ?_
    obtain ⟨c, hc⟩ := hdiag i
    exact ⟨n i * c * n i, by simp only [hf, hc]; ring⟩
  obtain ⟨c, hc⟩ := this
  exact ⟨c + ∑ i, ∑ j, (if i < j then f i j else 0), by rw [hc]; ring⟩

/-- Core congruence: for `m ≡ h (N)` with `A h ≡ 0 (N)`, `A[m] = A[h] + N² (2 n·c + A[n])`. -/
lemma quad_modEq {A : Matrix (Fin r) (Fin r) ℤ} (hA : A.IsSymm) {N : ℕ} {h m : Fin r → ℤ}
    (hh : ∀ i, (N : ℤ) ∣ (A *ᵥ h) i) (hm : ∀ i, m i ≡ h i [ZMOD N]) :
    ∃ n c : Fin r → ℤ, m ⬝ᵥ (A *ᵥ m) =
      h ⬝ᵥ (A *ᵥ h) + (N : ℤ) ^ 2 * (2 * (n ⬝ᵥ c) + n ⬝ᵥ (A *ᵥ n)) := by
  choose n hn using fun i => (Int.modEq_iff_dvd.mp (hm i).symm)
  choose c hc using hh
  have hmh : m = h + (N : ℤ) • n := by
    funext i; have := hn i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; linarith
  have hAh : A *ᵥ h = (N : ℤ) • c := by
    funext i; simp [hc i]
  refine ⟨n, c, ?_⟩
  have e1 : n ⬝ᵥ (A *ᵥ h) = (N : ℤ) * (n ⬝ᵥ c) := by rw [hAh, dotProduct_smul, smul_eq_mul]
  have e2 : h ⬝ᵥ (A *ᵥ n) = (N : ℤ) * (n ⬝ᵥ c) := by
    rw [dot_mulVec_symm hA, hAh, smul_dotProduct, smul_eq_mul, dotProduct_comm]
  subst hmh
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, e1, e2]
  ring

/-- $\Theta(z;h)$ depends only on $h \bmod N$ (Section 10.3, p. 168). -/
@[kb "iwaniec1997" "Section 10.3, Theta(z;h) depends only on h mod N, p. 168"]
theorem thetaCongruent_congr (A : Matrix (Fin r) (Fin r) ℤ) (P : MvPolynomial (Fin r) ℂ) (N : ℕ)
    {h h' : Fin r → ℤ} (hh : ∀ i, h i ≡ h' i [ZMOD N]) (z : ℂ) :
    thetaCongruent A P N h z = thetaCongruent A P N h' z := by
  unfold thetaCongruent
  let e : {m : Fin r → ℤ // ∀ i, m i ≡ h i [ZMOD N]} ≃ {m : Fin r → ℤ // ∀ i, m i ≡ h' i [ZMOD N]} :=
    Equiv.subtypeEquivRight fun m => ⟨fun H i => (H i).trans (hh i), fun H i => (H i).trans (hh i).symm⟩
  exact Equiv.tsum_eq e (fun m : {m : Fin r → ℤ // ∀ i, m i ≡ h' i [ZMOD N]} ↦
    eval (intVec m.1) P *
      cexp (2 * π * I * (quadValue (A.map (fun a : ℤ ↦ (a : ℝ))) (intVec m.1) / (2 * (N : ℂ) ^ 2) * z)))

/-- **(10.14)**: for $P$ homogeneous of degree $\nu$, $\Theta(z;-h) = (-1)^\nu\,\Theta(z;h)$. -/
@[kb "iwaniec1997" "Section 10.3, (10.14), p. 168"]
theorem thetaCongruent_neg (A : Matrix (Fin r) (Fin r) ℤ) {ν : ℕ} {P : MvPolynomial (Fin r) ℂ}
    (hP : P.IsHomogeneous ν) (N : ℕ) (h : Fin r → ℤ) (z : ℂ) :
    thetaCongruent A P N (-h) z = (-1) ^ ν * thetaCongruent A P N h z := by
  unfold thetaCongruent
  let e : {m : Fin r → ℤ // ∀ i, m i ≡ h i [ZMOD N]} ≃ {m : Fin r → ℤ // ∀ i, m i ≡ (-h) i [ZMOD N]} :=
    { toFun := fun m => ⟨-m.1, fun i => by simpa using (m.2 i).neg⟩
      invFun := fun m => ⟨-m.1, fun i => by simpa using (m.2 i).neg⟩
      left_inv := fun m => by ext; simp
      right_inv := fun m => by ext; simp }
  rw [← Equiv.tsum_eq e, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have h1 : intVec (e m).1 = -intVec m.1 := by funext i; simp [e, intVec]
  have h2 : (e m).1 ⬝ᵥ (A *ᵥ (e m).1) = m.1 ⬝ᵥ (A *ᵥ m.1) := by simp [e, Matrix.mulVec_neg]
  simp only [quadValue_intVec, h2]
  simp only [h1, eval_neg_of_isHomogeneous hP]
  ring

/-- Shifting `z` by an integer `d` multiplies the congruent theta function by a root of unity. -/
lemma thetaCongruent_shift {A : Matrix (Fin r) (Fin r) ℤ} (hA : A.IsSymm) (P : MvPolynomial (Fin r) ℂ)
    {N : ℕ} (hN : N ≠ 0) {h : Fin r → ℤ} (hh : ∀ i, (N : ℤ) ∣ (A *ᵥ h) i) (d : ℤ)
    (hev : ∀ n c : Fin r → ℤ, ∃ s : ℤ, (2 * (n ⬝ᵥ c) + n ⬝ᵥ (A *ᵥ n)) * d = 2 * s) (z : ℂ) :
    thetaCongruent A P N h (z + d) =
      cexp (2 * π * I * (quadValue (A.map (fun a : ℤ ↦ (a : ℝ))) (intVec h) * d /
        (2 * (N : ℂ) ^ 2))) * thetaCongruent A P N h z := by
  unfold thetaCongruent
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  obtain ⟨n, c, hq⟩ := quad_modEq hA hh m.2
  obtain ⟨s, hs⟩ := hev n c
  simp only [quadValue_intVec]
  have hz : ((m.1 ⬝ᵥ (A *ᵥ m.1) : ℤ) * d : ℤ) = (h ⬝ᵥ (A *ᵥ h)) * d + 2 * (N : ℤ) ^ 2 * s := by
    rw [hq]
    linear_combination ((N : ℤ) ^ 2) * hs
  have key : ((m.1 ⬝ᵥ (A *ᵥ m.1) : ℤ) : ℂ) * d = ((h ⬝ᵥ (A *ᵥ h) : ℤ) : ℂ) * d + 2 * (N : ℂ) ^ 2 * s := by
    exact_mod_cast hz
  have hN2 : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hq' : ((m.1 ⬝ᵥ (A *ᵥ m.1) : ℤ) : ℂ) / (2 * (N : ℂ) ^ 2) * d =
      ((h ⬝ᵥ (A *ᵥ h) : ℤ) : ℂ) * d / (2 * (N : ℂ) ^ 2) + s := by
    field_simp
    linear_combination key
  rw [show 2 * π * I * (((m.1 ⬝ᵥ (A *ᵥ m.1) : ℤ) : ℂ) / (2 * (N : ℂ) ^ 2) * (z + d)) =
      (s : ℂ) * (2 * π * I) + 2 * π * I * (((h ⬝ᵥ (A *ᵥ h) : ℤ) : ℂ) * d / (2 * (N : ℂ) ^ 2)) +
        2 * π * I * (((m.1 ⬝ᵥ (A *ᵥ m.1) : ℤ) : ℂ) / (2 * (N : ℂ) ^ 2) * z) by
    linear_combination (2 * π * I) * hq']
  rw [Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  ring

/-- **Proposition 10.3, (10.18)**: for symmetric integral $A$ and $h \in \mathcal H$ (that is, $Ah \equiv 0 \pmod N$),
$\Theta(z+2;h) = e\big(A[h]/N^2\big)\,\Theta(z;h)$. -/
@[kb "iwaniec1997" "Section 10.3, Proposition 10.3, (10.18), p. 169"]
theorem thetaCongruent_add_two {A : Matrix (Fin r) (Fin r) ℤ} (hA : A.IsSymm) (P : MvPolynomial (Fin r) ℂ)
    {N : ℕ} {h : Fin r → ℤ} (hh : ∀ i, (N : ℤ) ∣ (A *ᵥ h) i) (z : ℂ) :
    thetaCongruent A P N h (z + 2) =
      cexp (2 * π * I * (quadValue (A.map (fun a : ℤ ↦ (a : ℝ))) (intVec h) / (N : ℂ) ^ 2)) *
        thetaCongruent A P N h z := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [thetaCongruent]
  · have hev : ∀ n c : Fin r → ℤ, ∃ s : ℤ,
        (2 * (n ⬝ᵥ c) + n ⬝ᵥ (A *ᵥ n)) * 2 = 2 * s := fun n c =>
      ⟨2 * (n ⬝ᵥ c) + n ⬝ᵥ (A *ᵥ n), by ring⟩
    have := thetaCongruent_shift hA P hN.ne' hh 2 hev z
    push_cast at this
    rw [this]
    congr 3
    ring

/-- **Proposition 10.3, (10.19)**: if moreover the diagonal of $A$ is even,
$\Theta(z+1;h) = e\big(A[h]/2N^2\big)\,\Theta(z;h)$. -/
@[kb "iwaniec1997" "Section 10.3, Proposition 10.3, (10.19), p. 169"]
theorem thetaCongruent_add_one {A : Matrix (Fin r) (Fin r) ℤ} (hA : A.IsSymm) (hdiag : ∀ i, Even (A i i))
    (P : MvPolynomial (Fin r) ℂ) {N : ℕ} {h : Fin r → ℤ} (hh : ∀ i, (N : ℤ) ∣ (A *ᵥ h) i) (z : ℂ) :
    thetaCongruent A P N h (z + 1) =
      cexp (2 * π * I * (quadValue (A.map (fun a : ℤ ↦ (a : ℝ))) (intVec h) / (2 * (N : ℂ) ^ 2))) *
        thetaCongruent A P N h z := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [thetaCongruent]
  · have hev : ∀ n c : Fin r → ℤ, ∃ s : ℤ,
        (2 * (n ⬝ᵥ c) + n ⬝ᵥ (A *ᵥ n)) * 1 = 2 * s := fun n c => by
      obtain ⟨u, hu⟩ := even_quad_of_even_diag hA hdiag n
      exact ⟨n ⬝ᵥ c + u, by rw [mul_one, hu]; ring⟩
    have := thetaCongruent_shift hA P hN.ne' hh 1 hev z
    push_cast at this
    rw [this]
    congr 3
    ring

end ModularFormsKB.Iwaniec1997
