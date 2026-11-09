import ModularFormsKB.Miyake.Sec4_3.QSeries

/-!
# Miyake §4.3: Gauss sums and twists; the set of moduli in Weil's theorem

* `Miyake.sum_transl_eq_gaussW_twist` (Lemma 4.3.10(1)):
  $\sum_{u \bmod m} \bar\psi(u)\, f(z + u/m) = W(\bar\psi)\, f_\psi(z)$.
* `Miyake.gaussW_mul_gaussW_inv`, `Miyake.gaussW_ne_zero`: $W(\psi)W(\bar\psi) = \psi(-1)m$ for
  primitive $\psi$ modulo $m$, so $W(\psi) \ne 0$.
* `Miyake.exists_weilSet`: a set $\mathcal M$ as in Theorem 4.3.15 exists (Dirichlet's theorem).
-/

open Complex Filter Asymptotics
open scoped Real

noncomputable section

namespace Miyake

lemma isPrimitive_inv_aux {m : ℕ} [NeZero m] {ψ : DirichletCharacter ℂ m} (hψ : ψ.IsPrimitive) :
    ψ⁻¹.IsPrimitive := by
  have h1 : ψ.conductor ≤ ψ⁻¹.conductor := by
    apply Nat.sInf_le
    obtain ⟨h, χ₀, hχ⟩ := DirichletCharacter.factorsThrough_conductor ψ⁻¹
    refine ⟨h, χ₀⁻¹, ?_⟩
    rw [map_inv, ← hχ, inv_inv]
  have h2 : ψ⁻¹.conductor ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m))
    (DirichletCharacter.conductor_dvd_level _)
  unfold DirichletCharacter.IsPrimitive at *
  omega

lemma stdAddChar_natCast_mul (m : ℕ) [NeZero m] (n : ℕ) (u : ZMod m) :
    (ZMod.stdAddChar ((n : ZMod m) * u) : ℂ) = cexp (2 * π * I * ((n * u.val : ℕ) : ℝ) / m) := by
  rw [ZMod.stdAddChar_apply]
  have : ((n : ZMod m) * u) = ((n * u.val : ℕ) : ZMod m) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [this, ZMod.toCircle_natCast]
  push_cast; rfl

/-- $W(\psi)\,W(\bar\psi) = \psi(-1)\,m$ for a primitive Dirichlet character $\psi$ modulo $m$. -/
lemma gaussW_mul_gaussW_inv {m : ℕ} [NeZero m] {ψ : DirichletCharacter ℂ m} (hψ : ψ.IsPrimitive) :
    gaussW ψ * gaussW ψ⁻¹ = ψ (-1) * m := by
  have h1 := ZMod.dft_dft (N := m) (fun k : ZMod m ↦ (ψ k : ℂ))
  have h2 := congrFun h1 1
  have h3 : ZMod.dft (fun k : ZMod m ↦ (ψ k : ℂ)) = fun k ↦ ψ⁻¹ (-k) * gaussW ψ := by
    funext k
    exact DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum hψ k
  rw [h3, ZMod.dft_mul_const (fun k : ZMod m ↦ (ψ⁻¹ (-k) : ℂ)) (gaussW ψ),
    ZMod.dft_comp_neg (fun k : ZMod m ↦ (ψ⁻¹ k : ℂ))] at h2
  have h5 := DirichletCharacter.fourierTransform_eq_gaussSum_mulShift (ψ⁻¹) (-1)
  rw [neg_neg] at h5
  have h6 : ZMod.dft (fun k : ZMod m ↦ (ψ⁻¹ k : ℂ)) (-1) = gaussW ψ⁻¹ := by
    rw [h5]
    unfold gaussW
    congr 1
    ext x
    simp
  simp only [smul_eq_mul] at h2
  rw [h6] at h2
  rw [mul_comm, h2, mul_comm]

/-- The Gauss sum of a primitive Dirichlet character is nonzero. -/
lemma gaussW_ne_zero {m : ℕ} [NeZero m] {ψ : DirichletCharacter ℂ m} (hψ : ψ.IsPrimitive) :
    gaussW ψ ≠ 0 := by
  intro h0
  have := gaussW_mul_gaussW_inv hψ
  rw [h0, zero_mul] at this
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hu : ψ (-1) ≠ 0 := by
    intro h
    have h1 : ψ (-1) * ψ (-1) = 1 := by rw [← map_mul]; simp
    rw [h] at h1
    simp at h1
  exact (mul_ne_zero hu hm) this.symm

/-- **Miyake Lemma 4.3.10(1).** For $f = \sum a_n e^{2\pi i n z}$ satisfying (4.3.7) and $\psi$ a
primitive Dirichlet character of conductor $m$,
$$\sum_{u \bmod m} \bar\psi(u)\,(f|_k\alpha(u/m))(z) = W(\bar\psi)\, f_\psi(z),$$
where $(f|_k\alpha(u/m))(z) = f(z + u/m)$ and $W$ is the Gauss sum. The sum runs over
$u \in \mathbb Z/m$ with representatives $0 \le u < m$ (Miyake: $1 \le u \le m$; same terms since $f$
has period $1$). Relation: same. -/
@[kb "miyake1989" "§4.3, Lemma 4.3.10(1), p. 123"]
theorem sum_transl_eq_gaussW_twist {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m)
    (hψ : ψ.IsPrimitive) {a : ℕ → ℂ} (ha : CoeffGrowth a) {z : ℂ} (hz : 0 < z.im) :
    ∑ u : ZMod m, ψ⁻¹ u * qSeries a (z + ((u.val : ℝ) / m : ℝ)) =
      gaussW ψ⁻¹ * qSeries (twist ψ a) z := by
  have hψi := isPrimitive_inv_aux hψ
  have key : ∀ n : ℕ, ∑ u : ZMod m, ψ⁻¹ u *
      (a n * cexp (2 * π * I * n * (z + ((u.val : ℝ) / m : ℝ)))) =
      gaussW ψ⁻¹ * (twist ψ a n * cexp (2 * π * I * n * z)) := by
    intro n
    have h1 : ∀ u : ZMod m, ψ⁻¹ u * (a n * cexp (2 * π * I * n * (z + ((u.val : ℝ) / m : ℝ)))) =
        (a n * cexp (2 * π * I * n * z)) *
          (ψ⁻¹ u * (ZMod.stdAddChar ((n : ZMod m) * u) : ℂ)) := by
      intro u
      rw [stdAddChar_natCast_mul, mul_add, Complex.exp_add]
      have : (2 * π * I * ((n * u.val : ℕ) : ℝ) / m : ℂ) =
          2 * π * I * n * (((u.val : ℝ) / m : ℝ) : ℂ) := by
        push_cast; ring
      rw [this]; ring
    simp_rw [h1]
    rw [← Finset.mul_sum]
    have h2 := gaussSum_mulShift_of_isPrimitive (e := ZMod.stdAddChar) hψi (n : ZMod m)
    have h3 : ∑ u : ZMod m, ψ⁻¹ u * (ZMod.stdAddChar ((n : ZMod m) * u) : ℂ) =
        gaussSum ψ⁻¹ (ZMod.stdAddChar.mulShift (n : ZMod m)) := by
      unfold gaussSum
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      simp [AddChar.mulShift_apply]
    rw [h3, h2, inv_inv]
    unfold twist gaussW
    ring
  have hA : HasSum (fun k : ℕ ↦ ∑ u : ZMod m, ψ⁻¹ u *
      (a k * cexp (2 * π * I * k * (z + ((u.val : ℝ) / m : ℝ)))))
      (∑ u : ZMod m, ψ⁻¹ u * qSeries a (z + ((u.val : ℝ) / m : ℝ))) := by
    refine hasSum_sum fun u _ ↦ ?_
    refine (hasSum_qSeries ha ?_).mul_left _
    simpa using hz
  have hB := (hasSum_qSeries (ha.twist ψ) hz).mul_left (gaussW ψ⁻¹)
  simp_rw [key] at hA
  exact hA.unique hB

/-- **Miyake §4.3, before Theorem 4.3.15**: a set $\mathcal M$ as required exists, for instance the
odd primes prime to $N$ (by Dirichlet's theorem on primes in arithmetic progressions, Mathlib's
`Nat.forall_exists_prime_gt_and_eq_mod`). Relation: same. -/
@[kb "miyake1989" "§4.3, remark before Theorem 4.3.15, p. 128"]
theorem exists_weilSet {N : ℕ} (hN : 0 < N) : IsWeilSet N {m | m.Prime ∧ m ≠ 2 ∧ m.Coprime N} := by
  refine ⟨fun m hm ↦ Or.inl ⟨hm.1, hm.2.1⟩, fun m hm ↦ hm.2.2, ?_⟩
  intro c d hc hd hcd
  have : NeZero d := ⟨hd.ne'⟩
  have hu : IsUnit (c : ZMod d) := (ZMod.isUnit_iff_coprime c d).2 hcd
  obtain ⟨p, hp, hpp, hpc⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu (max N 2)
  have hpN : N < p := lt_of_le_of_lt (le_max_left _ _) hp
  have hp2 : 2 < p := lt_of_le_of_lt (le_max_right _ _) hp
  refine ⟨p, ⟨hpp, hp2.ne', ?_⟩, ?_⟩
  · rw [Nat.Prime.coprime_iff_not_dvd hpp]
    exact fun h ↦ absurd (Nat.le_of_dvd hN h) (not_le.2 hpN)
  · have := (ZMod.intCast_eq_intCast_iff_dvd_sub (c : ℤ) (p : ℤ) d).1
      (by push_cast; exact hpc.symm)
    obtain ⟨t, ht⟩ := this
    exact ⟨t, by linear_combination ht⟩

end Miyake
