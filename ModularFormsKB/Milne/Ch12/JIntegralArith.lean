import ModularFormsKB.Milne.Ch6.CosetProduct
import ModularFormsKB.Citation
/-!
# Milne, Corollary 12.16: the arithmetic step

A quadratic imaginary $z \in \mathbb H$ is a fixed point of an integer matrix of non-square determinant, in the form
used with the modular polynomial (`ModularFormsKB.Milne.CMIntegral.exists_jN_smul_eq_j`).

If $az^2 + bz + c = 0$ with $a > 0$, put $D = 4ac - b^2 > 0$ ($z \notin \mathbb R$), $t = |D| + |b|$, $y = 1 + ta$,
$x = y - b$, $N = xy + ac$ and $\gamma = \begin{pmatrix} 1 & t \\ a & y\end{pmatrix} \in \mathrm{SL}_2(\mathbb Z)$.
Then $N\gamma z = z + e$ with $e = c + tx$ (direct computation using $az^2 = -bz - c$), so $j(N\gamma z) = j(z)$; and
$4N = (x + y)^2 + D$ with $x + y > D$, so $N$ is not a square.
-/

open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.CMIntegral

open TauCeti.ModularForm LevelTwo

/-- **A quadratic imaginary point is fixed by a matrix of non-square determinant.** If $az^2 + bz + c = 0$ with
integers $a > 0$, $b$, $c$, there are $N > 0$ not a square and $\gamma \in \mathrm{SL}_2(\mathbb Z)$ with
$j(N\gamma z) = j(z)$. -/
theorem exists_jN_smul_eq_j (z : ℍ) (a b c : ℤ) (ha : 0 < a)
    (hz : (a : ℂ) * (z : ℂ) ^ 2 + b * z + c = 0) :
    ∃ (N : ℕ) (hN : 0 < N), ¬ IsSquare N ∧ ∃ γ : SL(2, ℤ), jN hN (γ • z) = j z := by
  have hv := z.im_pos
  have h1 := congrArg Complex.im hz
  have h2 := congrArg Complex.re hz
  simp [pow_two] at h1 h2
  have hb : (b : ℝ) = -2 * a * z.re := by
    have h3 : (2 * (a : ℝ) * z.re + b) * z.im = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h3 with h | h
    · linarith
    · exact absurd h hv.ne'
  have hD : ((4 * a * c - b ^ 2 : ℤ) : ℝ) = 4 * (a : ℝ) ^ 2 * z.im ^ 2 := by
    push_cast
    linear_combination (4 * (a : ℝ)) * h2 - ((b : ℝ) + 2 * a * z.re) * hb
  have hDpos : 0 < 4 * a * c - b ^ 2 := by
    have : (0 : ℝ) < ((4 * a * c - b ^ 2 : ℤ) : ℝ) := by
      rw [hD]
      have : (0 : ℝ) < a := by exact_mod_cast ha
      positivity
    exact_mod_cast this
  obtain ⟨D, hDd⟩ : ∃ D : ℤ, D = 4 * a * c - b ^ 2 := ⟨_, rfl⟩
  rw [← hDd] at hDpos
  obtain ⟨t, htd⟩ : ∃ t : ℤ, t = |D| + |b| := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [htd]; positivity
  have ht1 : D ≤ t := by rw [htd]; linarith [le_abs_self D, abs_nonneg b]
  have ht2 : b ≤ t := by rw [htd]; linarith [le_abs_self b, abs_nonneg D]
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y = 1 + t * a := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℤ, x = y - b := ⟨_, rfl⟩
  obtain ⟨N, hNd⟩ : ∃ N : ℤ, N = x * y + a * c := ⟨_, rfl⟩
  obtain ⟨e, hed⟩ : ∃ e : ℤ, e = c + t * x := ⟨_, rfl⟩
  have hta : t ≤ t * a := by nlinarith
  have hw : D < x + y := by rw [hx, hy]; nlinarith
  have h4N : 4 * N = (x + y) ^ 2 + D := by
    rw [hNd, hDd, hx]; ring
  have hNpos : 0 < N := by nlinarith
  have hNc : ((N.toNat : ℕ) : ℤ) = N := Int.toNat_of_nonneg hNpos.le
  have hNpos' : 0 < N.toNat := by omega
  obtain ⟨γ, hγ⟩ : ∃ γ : SL(2, ℤ), (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, t; a, y] :=
    ⟨⟨!![1, t; a, y], by simp [Matrix.det_fin_two, hy]⟩, rfl⟩
  have g00 : γ 0 0 = 1 := by simp [hγ]
  have g01 : γ 0 1 = t := by simp [hγ]
  have g10 : γ 1 0 = a := by simp [hγ]
  have g11 : γ 1 1 = y := by simp [hγ]
  refine ⟨N.toNat, hNpos', ?_, γ, ?_⟩
  · rintro ⟨r, hr⟩
    have hr' : N = (r : ℤ) * r := by rw [← hNc, hr]; push_cast; ring
    have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg r
    have hlt : x + y < 2 * r := by
      by_contra h
      push Not at h
      nlinarith
    nlinarith
  · have hNcC : ((N.toNat : ℕ) : ℂ) = (N : ℂ) := by exact_mod_cast congrArg (fun n : ℤ => (n : ℂ)) hNc
    have hden : (a : ℂ) * z + y ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      rcases this with h | h
      · have : (0 : ℝ) < a := by exact_mod_cast ha
        linarith
      · exact hv.ne' h
    have hpt : scaleH N.toNat hNpos' (γ • z) = ModularGroup.T ^ e • z := by
      apply UpperHalfPlane.ext
      rw [modular_T_zpow_smul]
      have hc := coe_specialLinearGroup_apply γ z
      simp only [g00, g01, g10, g11, algebraMap_int_eq, eq_intCast, Int.cast_one] at hc
      simp only [scaleH, coe_vadd, hc, hNcC]
      push_cast
      rw [mul_div_assoc', div_eq_iff hden]
      simp only [one_mul]
      subst hNd hx hy hed
      push_cast
      linear_combination (-1 : ℂ) * hz
    unfold jN
    rw [hpt, j_smul_SL2Z]

/-- A quadratic irrationality $z \in \mathbb H$ satisfies $az^2 + bz + c = 0$ with integers $a > 0$, $b$, $c$. -/
theorem exists_int_quadratic (z : ℍ) (hz : IsIntegral ℚ (z : ℂ)) (hz2 : (minpoly ℚ (z : ℂ)).natDegree = 2) :
    ∃ a b c : ℤ, 0 < a ∧ (a : ℂ) * (z : ℂ) ^ 2 + b * z + c = 0 := by
  have hmonic := minpoly.monic hz
  have hroot := minpoly.aeval ℚ (z : ℂ)
  set p := minpoly ℚ (z : ℂ) with hpdef
  have hc2 : p.coeff 2 = 1 := by
    have := hmonic.coeff_natDegree
    rwa [hz2] at this
  rw [Polynomial.aeval_eq_sum_range, hz2] at hroot
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc2, zero_add] at hroot
  set b := p.coeff 1
  set c := p.coeff 0
  have hq : (z : ℂ) ^ 2 + (b : ℂ) * z + (c : ℂ) = 0 := by
    simpa [Rat.smul_def, add_comm, add_left_comm, add_assoc] using hroot
  set d : ℕ := b.den * c.den with hd
  have hdpos : 0 < d := Nat.mul_pos b.den_pos c.den_pos
  have hB : (d : ℂ) * b = ((b.num * c.den : ℤ) : ℂ) := by
    have : (d : ℚ) * b = ((b.num * c.den : ℤ) : ℚ) := by
      have h := Rat.mul_den_eq_num b
      push_cast [hd]
      linear_combination (c.den : ℚ) * h
    exact_mod_cast congrArg (fun q : ℚ => (q : ℂ)) this
  have hC : (d : ℂ) * c = ((c.num * b.den : ℤ) : ℂ) := by
    have : (d : ℚ) * c = ((c.num * b.den : ℤ) : ℚ) := by
      have h := Rat.mul_den_eq_num c
      push_cast [hd]
      linear_combination (b.den : ℚ) * h
    exact_mod_cast congrArg (fun q : ℚ => (q : ℂ)) this
  refine ⟨d, b.num * c.den, c.num * b.den, by exact_mod_cast hdpos, ?_⟩
  push_cast at hB hC ⊢
  linear_combination (d : ℂ) * hq - (z : ℂ) * hB - hC

end ModularFormsKB.Milne.CMIntegral
