import ModularFormsKB.Milne.Ch4.Poincare

/-!
# Milne, Theorems 4.28 and 4.33 in weight 2: the comparison series diverges

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 4, Theorems 4.28 and 4.33
(pdf pp. 62–64) are stated for $2k \ge 2$. The proof of convergence (our `poincareSeries_bound`) bounds the summand
attached to $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix}$ by $|cz+d|^{-2k}$ (`poincareSummand_norm_le`, since
$|\exp(2\pi in\gamma z/h)| \le 1$) and then uses that
$\sum_{(c,d) \in \mathbb Z^2 \smallsetminus 0}|cz+d|^{-2k}$ converges, via $|cz+d| \ge r(z)\max(|c|,|d|)$
and the convergence of $\sum_{v \ne 0}\|v\|^{-2k}$ (Mathlib's `EisensteinSeries.summable_one_div_norm_rpow`,
which assumes the exponent is $> 2$). Both majorants diverge when $2k = 2$:

- `not_summable_norm_mul_add_rpow_neg_two`: for every $z \in \mathbb H$,
  $\sum_{(c,d) \in \mathbb Z^2}|cz+d|^{-2}$ is not summable (the term at $(0,0)$ is $0^{-2} = 0$ in Mathlib's
  convention, so this is the series over $\mathbb Z^2 \smallsetminus 0$);
- `not_summable_norm_rpow_neg_two`: $\sum_{v \in \mathbb Z^2}\|v\|^{-2}$ is not summable (sup norm);
- `not_summable_poincareTerm_weight_two`: the weight-2 Poincaré series $\varphi_0$ for $\mathrm{SL}_2(\mathbb Z)$ is
  not absolutely convergent at any $z$ (bottom rows $(p, d)$, $p$ prime, $0 < d < p$; $\sum_p 1/p$ diverges).

Proof: for $c \ge 1$ and $0 \le d < c$, $|cz+d| \le c|z| + d \le c(|z|+1)$, so the $c$-th row contributes at least
$c\cdot c^{-2}(|z|+1)^{-2}$, and $\sum_c 1/c$ diverges. Hence the argument of Theorem 4.28 needs $2k > 2$, and the
corrected statements (`PoincareSeriesModular`, `PoincarePetersson`, all of their proofs) assume $k \ge 2$.
-/

open UpperHalfPlane
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne

/-- A nonnegative family on $\mathbb Z^2$ that is bounded below by $\frac{A}{c^2}$ on
$\{(c,d) : c \ge 1, 0 \le d < c\}$, $A > 0$, is not summable. -/
lemma not_summable_of_row_lower_bound {g : ℤ × ℤ → ℝ} (hg : ∀ p, 0 ≤ g p) {A : ℝ} (hA : 0 < A)
    (hlow : ∀ n : ℕ, ∀ d : ℕ, d < n + 1 → A / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ g ((n + 1 : ℕ), d)) :
    ¬ Summable g := by
  intro hs
  have hrow : Summable fun c : ℤ ↦ ∑' d : ℤ, g (c, d) := hs.prod
  have hinj : Function.Injective fun n : ℕ ↦ ((n + 1 : ℕ) : ℤ) := by
    intro m n h; simpa using h
  have hu := hrow.comp_injective hinj
  have hge : ∀ n : ℕ, A / ((n + 1 : ℕ) : ℝ) ≤ ∑' d : ℤ, g (((n + 1 : ℕ) : ℤ), d) := by
    intro n
    have hsum := (hs.prod_factor ((n + 1 : ℕ) : ℤ)).sum_le_tsum
      ((Finset.range (n + 1)).map ⟨fun d : ℕ ↦ (d : ℤ), Nat.cast_injective⟩) (fun i _ ↦ hg _)
    refine le_trans ?_ hsum
    rw [Finset.sum_map]
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    calc A / ((n + 1 : ℕ) : ℝ) = ∑ _d ∈ Finset.range (n + 1), A / ((n + 1 : ℕ) : ℝ) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
      _ ≤ _ := Finset.sum_le_sum fun d hd ↦ hlow n d (Finset.mem_range.1 hd)
  have hharm : Summable fun n : ℕ ↦ A / ((n + 1 : ℕ) : ℝ) :=
    Summable.of_nonneg_of_le (fun n ↦ by positivity) hge hu
  have h1 : Summable fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ) := by
    have := hharm.mul_left A⁻¹
    refine this.congr fun n ↦ ?_
    field_simp
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).1 (by exact_mod_cast h1))

/-- **Milne 4.28 in weight 2, the comparison series diverges**: for $z \in \mathbb H$,
$\sum_{(c,d)}|cz+d|^{-2}$ is not summable. -/
@[kb "milne2017mf" "Section 4, Theorem 4.28 (pdf p. 62), weight 2 erratum"]
theorem not_summable_norm_mul_add_rpow_neg_two (z : ℍ) :
    ¬ Summable fun v : Fin 2 → ℤ ↦ ‖((v 0 : ℤ) : ℂ) * z + (v 1 : ℤ)‖ ^ (-2 : ℝ) := by
  intro hs
  set B : ℝ := ‖(z : ℂ)‖ + 1 with hB
  have hB0 : 0 < B := by positivity
  refine not_summable_of_row_lower_bound (g := fun p : ℤ × ℤ ↦ ‖(p.1 : ℂ) * z + (p.2 : ℂ)‖ ^ (-2 : ℝ))
    (fun p ↦ by positivity) (A := (B ^ 2)⁻¹) (by positivity) (fun n d hd ↦ ?_) ?_
  · -- `|cz + d| ≤ c (|z| + 1)` for `0 ≤ d < c`
    set c : ℝ := ((n + 1 : ℕ) : ℝ)
    have hc : 0 < c := by positivity
    have hd' : (d : ℝ) ≤ c := by simp only [c]; exact_mod_cast hd.le
    have hnorm : ‖(((n + 1 : ℕ) : ℤ) : ℂ) * z + ((d : ℤ) : ℂ)‖ ≤ c * B := by
      calc ‖(((n + 1 : ℕ) : ℤ) : ℂ) * z + ((d : ℤ) : ℂ)‖
          ≤ ‖(((n + 1 : ℕ) : ℤ) : ℂ) * z‖ + ‖((d : ℤ) : ℂ)‖ := norm_add_le _ _
        _ = c * ‖(z : ℂ)‖ + d := by
          rw [norm_mul, Int.cast_natCast, Complex.norm_natCast, Int.cast_natCast, Complex.norm_natCast]
        _ ≤ c * ‖(z : ℂ)‖ + c := by gcongr
        _ = c * B := by rw [hB]; ring
    have hpos : 0 < ‖(((n + 1 : ℕ) : ℤ) : ℂ) * z + ((d : ℤ) : ℂ)‖ := by
      rw [norm_pos_iff]
      intro h0
      have := congrArg Complex.im h0
      simp at this
      exact (UpperHalfPlane.im_pos z).ne' (by
        rcases this with h | h
        · exact absurd h (by positivity)
        · exact h)
    dsimp only
    rw [Real.rpow_neg hpos.le, Real.rpow_two, div_eq_mul_inv, ← mul_inv]
    refine inv_anti₀ (by positivity) ?_
    calc ‖(((n + 1 : ℕ) : ℤ) : ℂ) * z + ((d : ℤ) : ℂ)‖ ^ 2 ≤ (c * B) ^ 2 := by gcongr
      _ = B ^ 2 * c ^ 2 := by ring
  · exact (finTwoArrowEquiv ℤ).symm.summable_iff.2 hs |>.congr fun p ↦ by simp [finTwoArrowEquiv]

/-- **Milne 4.28 in weight 2, the lattice majorant diverges**: $\sum_{v \in \mathbb Z^2}\|v\|^{-2}$ (sup norm) is not
summable, so `EisensteinSeries.summable_one_div_norm_rpow` cannot be used with exponent $2$. -/
@[kb "milne2017mf" "Section 4, Theorem 4.28 (pdf p. 62), weight 2 erratum"]
theorem not_summable_norm_rpow_neg_two :
    ¬ Summable fun v : Fin 2 → ℤ ↦ ‖v‖ ^ (-2 : ℝ) := by
  intro hs
  refine not_summable_of_row_lower_bound (g := fun p : ℤ × ℤ ↦ ‖(finTwoArrowEquiv ℤ).symm p‖ ^ (-2 : ℝ))
    (fun p ↦ by positivity) (A := 1) one_pos (fun n d hd ↦ ?_) ?_
  · have hnorm : ‖(finTwoArrowEquiv ℤ).symm (((n + 1 : ℕ) : ℤ), (d : ℤ))‖ = ((n + 1 : ℕ) : ℝ) := by
      refine le_antisymm ?_ ?_
      · refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun i ↦ ?_
        fin_cases i
        · show ‖(((n + 1 : ℕ) : ℤ))‖ ≤ _
          rw [Int.norm_natCast]
        · show ‖((d : ℤ))‖ ≤ _
          rw [Int.norm_natCast]
          exact_mod_cast hd.le
      · have : ‖(((n + 1 : ℕ) : ℤ))‖ ≤ ‖(finTwoArrowEquiv ℤ).symm (((n + 1 : ℕ) : ℤ), (d : ℤ))‖ :=
          norm_le_pi_norm ((finTwoArrowEquiv ℤ).symm (((n + 1 : ℕ) : ℤ), (d : ℤ))) 0
        rwa [Int.norm_natCast] at this
    rw [hnorm, Real.rpow_neg (by positivity), Real.rpow_two, one_div]
  · exact (finTwoArrowEquiv ℤ).symm.summable_iff.2 hs

/-- Coprime integers are the bottom row of a matrix in `SL(2, ℤ)`. -/
private lemma exists_sl_bottom_row {p d : ℤ} (h : IsCoprime p d) :
    ∃ γ : SL(2, ℤ), (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = p ∧ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = d := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨⟨!![b, -a; p, d], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linarith
  · simp
  · simp

private lemma mul_inv_apply_10' (x y : SL(2, ℤ)) :
    ((x * y⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = x 1 0 * y 1 1 - x 1 1 * y 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- **Milne 4.28 in weight 2, the Poincaré series does not converge absolutely**: for
$\Gamma = \mathrm{SL}_2(\mathbb Z)$, $2k = 2$, $n = 0$ and $z \in \mathbb H$, the family
$\bigl(|cz+d|^{-2}\bigr)$ indexed by the cosets $\Gamma_\infty\backslash\Gamma$ is not summable. -/
@[kb "milne2017mf" "Section 4, Theorem 4.28 (pdf p. 62), weight 2 erratum"]
theorem not_summable_poincareTerm_weight_two (z : ℍ) :
    ¬ Summable fun x : StabInftyCosets (⊤ : Subgroup SL(2, ℤ)) ↦ ‖poincareTerm ⊤ 1 0 x z‖ := by
  intro hs
  set B : ℝ := ‖(z : ℂ)‖ + 1 with hB
  have hB0 : 0 < B := by positivity
  let S : Set (ℕ × ℕ) := {q | q.1.Prime ∧ 0 < q.2 ∧ q.2 < q.1}
  have hex : ∀ q : S, ∃ γ : SL(2, ℤ), (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (q.1.1 : ℤ) ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = (q.1.2 : ℤ) := by
    intro q
    obtain ⟨hp, hd0, hdp⟩ := q.2
    refine exists_sl_bottom_row ?_
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hd0 hdp)
  choose γ hγ0 hγ1 using hex
  let f : S → StabInftyCosets (⊤ : Subgroup SL(2, ℤ)) := fun q ↦ Quotient.mk _ ⟨γ q, Subgroup.mem_top _⟩
  have finj : Function.Injective f := by
    intro q q' h
    obtain ⟨hp, hd0, hdp⟩ := q.2
    obtain ⟨hp', hd0', hdp'⟩ := q'.2
    have hrel := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
    have h10 : ((γ q' * (γ q)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := hrel
    rw [mul_inv_apply_10', hγ0, hγ1, hγ0, hγ1] at h10
    have h2 : q'.1.1 * q.1.2 = q'.1.2 * q.1.1 := by
      have : ((q'.1.1 : ℤ) * q.1.2 : ℤ) = (q'.1.2 : ℤ) * q.1.1 := by linarith
      exact_mod_cast this
    have hdvd : q.1.1 ∣ q'.1.1 * q.1.2 := ⟨q'.1.2, by rw [h2]; ring⟩
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h3 | h3
    · have hpp : q.1.1 = q'.1.1 := (Nat.prime_dvd_prime_iff_eq hp hp').1 h3
      have hdd : q.1.2 = q'.1.2 := by
        rw [← hpp] at h2
        exact Nat.eq_of_mul_eq_mul_left hp.pos (h2.trans (mul_comm _ _))
      exact Subtype.ext (Prod.ext hpp hdd)
    · exact absurd (Nat.le_of_dvd hd0 h3) (not_le.2 hdp)
  have hg := hs.comp_injective finj
  let w : ℕ × ℕ → ℝ := fun q ↦ 1 / (((q.1 : ℕ) : ℝ) ^ 2 * B ^ 2)
  have hlow : ∀ q : S, w q.1 ≤ ‖poincareTerm ⊤ 1 0 (f q) z‖ := by
    intro q
    obtain ⟨hp, hd0, hdp⟩ := q.2
    have hval : ‖poincareTerm ⊤ 1 0 (f q) z‖ =
        (‖((q.1.1 : ℕ) : ℂ) * z + ((q.1.2 : ℕ) : ℂ)‖ ^ 2)⁻¹ := by
      show ‖poincareSummand ⊤ 1 0 (γ q) z‖ = _
      simp [poincareSummand, hγ0 q, hγ1 q]
    rw [hval]
    set c : ℝ := ((q.1.1 : ℕ) : ℝ) with hc
    have hc0 : 0 < c := by simp only [c]; exact_mod_cast hp.pos
    have hd' : ((q.1.2 : ℕ) : ℝ) ≤ c := by simp only [c]; exact_mod_cast hdp.le
    have hnorm : ‖((q.1.1 : ℕ) : ℂ) * z + ((q.1.2 : ℕ) : ℂ)‖ ≤ c * B := by
      calc ‖((q.1.1 : ℕ) : ℂ) * z + ((q.1.2 : ℕ) : ℂ)‖
          ≤ ‖((q.1.1 : ℕ) : ℂ) * z‖ + ‖((q.1.2 : ℕ) : ℂ)‖ := norm_add_le _ _
        _ = c * ‖(z : ℂ)‖ + ((q.1.2 : ℕ) : ℝ) := by
          rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast]
        _ ≤ c * ‖(z : ℂ)‖ + c := by gcongr
        _ = c * B := by rw [hB]; ring
    have hpos : 0 < ‖((q.1.1 : ℕ) : ℂ) * z + ((q.1.2 : ℕ) : ℂ)‖ := by
      rw [norm_pos_iff]
      intro h0
      have := congrArg Complex.im h0
      simp at this
      exact (UpperHalfPlane.im_pos z).ne' (by
        rcases this with h | h
        · exact absurd h hp.ne_zero
        · exact h)
    simp only [w]
    rw [one_div]
    refine inv_anti₀ (by positivity) ?_
    calc ‖((q.1.1 : ℕ) : ℂ) * z + ((q.1.2 : ℕ) : ℂ)‖ ^ 2 ≤ (c * B) ^ 2 := by gcongr
      _ = c ^ 2 * B ^ 2 := by ring
  have hw0 : ∀ q, 0 ≤ w q := fun q ↦ by positivity
  have hsum : Summable fun q : S ↦ w q.1 :=
    Summable.of_nonneg_of_le (fun q ↦ hw0 _) hlow hg
  have hind : Summable (S.indicator w) := (summable_subtype_iff_indicator (f := w)).1 hsum
  have hrow : Summable fun a : ℕ ↦ ∑' b : ℕ, S.indicator w (a, b) := hind.prod
  have hge : ∀ p : Nat.Primes, 1 / (2 * (p : ℝ) * B ^ 2) ≤ ∑' b : ℕ, S.indicator w ((p : ℕ), b) := by
    intro p
    have hsm := (hind.prod_factor (p : ℕ)).sum_le_tsum (Finset.Ico 1 (p : ℕ))
      (fun i _ ↦ Set.indicator_nonneg (fun q _ ↦ hw0 q) _)
    refine le_trans ?_ hsm
    have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
    have hsum_eq : ∑ b ∈ Finset.Ico 1 (p : ℕ), S.indicator w ((p : ℕ), b) =
        ∑ _b ∈ Finset.Ico 1 (p : ℕ), w ((p : ℕ), 0) := by
      refine Finset.sum_congr rfl fun b hb ↦ ?_
      rw [Set.indicator_of_mem]
      exact ⟨p.2, (Finset.mem_Ico.1 hb).1, (Finset.mem_Ico.1 hb).2⟩
    rw [hsum_eq, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub p.2.one_le]
    simp only [w, Nat.cast_one]
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ (p : ℝ) * B ^ 2 * ((p : ℝ) - 2) := mul_nonneg (by positivity) (by linarith)
    nlinarith
  have hprimes := hrow.comp_injective Nat.Primes.coe_nat_injective
  have hp1 : Summable fun p : Nat.Primes ↦ 1 / (2 * (p : ℝ) * B ^ 2) :=
    Summable.of_nonneg_of_le (fun p ↦ by positivity) hge hprimes
  refine Nat.Primes.not_summable_one_div ?_
  refine (hp1.mul_left (2 * B ^ 2)).congr fun p ↦ ?_
  have : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  field_simp

end ModularFormsKB.Milne
