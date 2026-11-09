import ModularFormsKB.Milne.Ch6.ModularEquationProof
import ModularFormsKB.Milne.Ch6.CosetExpansion
import ModularFormsKB.Citation
/-!
# Milne, Corollary 12.16: the leading coefficient of $F_N(X, X)$

Let $F_N \in \mathbb Z[X, Y]$ with $F_N(j(z), Y) = \prod_c (Y - j(N\gamma_c z))$ (Section 6 here), and
$P_N(X) = F_N(X, X)$ (`diagPoly`). If $N$ is not a square, the leading coefficient of $P_N$ is $\pm 1$
(`leadingCoeff_diagPoly`): with $z = Nu$, $q = e^{2\pi i u}$, each factor $q^{N^2}(j(Nu) - j(N\gamma_c Nu))$ is
$q^{N^2-N}(1 + \dots) - \zeta^{-1}q^{N^2-a^2}(1 + \dots)$ ($ad = N$, $|\zeta| = 1$, see
`ModularFormsKB.Milne.LevelTwo.expands_coset`), and $a^2 \ne N$, so its lowest coefficient has absolute value $1$;
while the lowest coefficient of $q^M P_N(j(Nu))$ is $\mathrm{lc}(P_N)$.
-/

open UpperHalfPlane CongruenceSubgroup Polynomial
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.CMIntegral

open TauCeti.ModularForm QSeries LevelTwo

local notation "𝕢" => Function.Periodic.qParam

/-- $P(X) = F(X, X)$ for $F \in \mathbb Z[X, Y]$. -/
def diagPoly (F : MvPolynomial (Fin 2) ℤ) : ℤ[X] := MvPolynomial.aeval ![X, X] F

variable {N : ℕ} (hN : 0 < N) [NeZero N]


theorem expands_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ) (A : ι → PowerSeries ℂ)
    (h : ∀ i ∈ s, Expands (f i) (A i)) : Expands (fun z ↦ ∑ i ∈ s, f i z) (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (expands_one.const_mul 0).congr fun z ↦ by simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- $P(j(z)) = \prod_c (j(z) - j(N\gamma_c z))$. -/
theorem eval_diagPoly_j {F : MvPolynomial (Fin 2) ℤ}
    (hF : ∀ z : ℍ, MvPolynomial.eval₂ (Int.castRingHom ℂ[X]) ![C (j z), X] F = Φ hN z) (z : ℍ) :
    (diagPoly F).eval₂ (Int.castRingHom ℂ) (j z) = ∏ c : Cosets N, (j z - cosetVal hN c z) := by
  have h1 : ∀ G : MvPolynomial (Fin 2) ℤ, (diagPoly G).eval₂ (Int.castRingHom ℂ) (j z) =
      MvPolynomial.eval₂ (Int.castRingHom ℂ) ![j z, j z] G := by
    intro G
    induction G using MvPolynomial.induction_on with
    | C a => simp only [diagPoly, MvPolynomial.aeval_C, MvPolynomial.eval₂_C]; rw [Polynomial.algebraMap_eq, Polynomial.eval₂_C]
    | add p q hp hq =>
      simp only [diagPoly, map_add, Polynomial.eval₂_add, MvPolynomial.eval₂_add] at hp hq ⊢
      rw [hp, hq]
    | mul_X p i hp =>
      simp only [diagPoly, map_mul, Polynomial.eval₂_mul, MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_X] at hp ⊢
      rw [hp]
      fin_cases i <;> simp
  have h2 : ∀ G : MvPolynomial (Fin 2) ℤ,
      (MvPolynomial.eval₂ (Int.castRingHom ℂ[X]) ![C (j z), X] G).eval (j z) =
      MvPolynomial.eval₂ (Int.castRingHom ℂ) ![j z, j z] G := by
    intro G
    induction G using MvPolynomial.induction_on with
    | C a => simp only [MvPolynomial.eval₂_C]; simp
    | add p q hp hq =>
      simp only [MvPolynomial.eval₂_add, Polynomial.eval_add] at hp hq ⊢
      rw [hp, hq]
    | mul_X p i hp =>
      simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Polynomial.eval_mul] at hp ⊢
      rw [hp]
      fin_cases i <;> simp
  rw [h1, ← h2, hF z, Φ, Polynomial.eval_prod]
  simp

theorem constantCoeff_expandJ :
    PowerSeries.constantCoeff (PowerSeries.expand N hN.ne'
      (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ))) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_expand]
  simpa using TauCeti.ModularForm.qExpansion_qParam_mul_j_coeff_zero

/-- A variant of `expands_coset` recording the lowest term. -/
theorem expands_coset_low (hsq : ¬ IsSquare N) (c : Cosets N) : ∃ (a : ℕ) (B : PowerSeries ℂ),
    a * a ≤ N * N ∧ a * a ≠ N ∧ ‖PowerSeries.constantCoeff B‖ = 1 ∧
    Expands (fun u ↦ 𝕢 1 (u : ℂ) ^ (N * N) * cosetVal hN c (scaleH N hN u))
      (PowerSeries.X ^ (N * N - a * a) * B) := by
  obtain ⟨a, d, b, ha, hd, had, hc⟩ := exists_cosetVal_eq hN c
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * (b / d)) with hζ
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hζ1 : ‖ζ‖ = 1 := by
    have : (2 * Real.pi * Complex.I * (b / d) : ℂ) = ((2 * Real.pi * b / d : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hζ, this, Complex.norm_exp_ofReal_mul_I]
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have haN : a * a ≤ N * N := by
    have : a ≤ N := by rw [← had]; exact Nat.le_mul_of_pos_right a hd
    exact Nat.mul_le_mul this this
  have haa : a * a ≠ N := fun h ↦ hsq ⟨a, h.symm⟩
  set w : ℍ → ℍ := fun u ↦ affineH a b d (by exact_mod_cast ha) (by exact_mod_cast hd) (scaleH N hN u)
    with hwdef
  have hw : ∀ u : ℍ, 𝕢 1 ((w u : ℍ) : ℂ) = ζ * 𝕢 1 (u : ℂ) ^ (a * a) := by
    intro u
    simp only [hwdef, affineH, scaleH, Function.Periodic.qParam, UpperHalfPlane.coe_mk, hζ]
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    have hN' : (N : ℂ) = (a : ℂ) * d := by exact_mod_cast had.symm
    rw [hN']
    push_cast
    field_simp
    ring
  have h1 := expands_qParam_mul_j_comp (a * a) (Nat.mul_pos ha ha) ζ hζ1 w hw
  have h3 := (expands_qParam_pow (N * N - a * a)).mul (h1.const_mul ζ⁻¹)
  refine ⟨a, _, haN, haa, ?_, h3.congr fun u ↦ ?_⟩
  · simp [hζ1]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale]
    simp [TauCeti.ModularForm.qExpansion_qParam_mul_j_coeff_zero]
  · rw [hc (scaleH N hN u), hw u]
    have : 𝕢 1 (u : ℂ) ^ (N * N) = 𝕢 1 (u : ℂ) ^ (N * N - a * a) * 𝕢 1 (u : ℂ) ^ (a * a) := by
      rw [← pow_add, Nat.sub_add_cancel haN]
    rw [this]
    field_simp
    rfl

/-- **Lowest term of one factor.** For each coset $c$, $q^{N^2}(j(Nu) - j(N\gamma_c Nu))$ is $q^n$ times a power
series whose constant coefficient has absolute value $1$, if $N$ is not a square. -/
theorem expands_factor (hsq : ¬ IsSquare N) (c : Cosets N) : ∃ (n : ℕ) (B : PowerSeries ℂ),
    ‖PowerSeries.constantCoeff B‖ = 1 ∧
    Expands (fun u ↦ 𝕢 1 (u : ℂ) ^ (N * N) * (j (scaleH N hN u) - cosetVal hN c (scaleH N hN u)))
      (PowerSeries.X ^ n * B) := by
  obtain ⟨a, B2, haN, haa, hB2, h2⟩ := expands_coset_low hN hsq c
  have hNN : N ≤ N * N := Nat.le_mul_of_pos_left N hN
  have h0 := (expands_qParam_pow (N * N - N)).mul (expands_qParam_pow_mul_j_scale hN)
  set E1 := PowerSeries.expand N hN.ne' (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)) with hE1
  have hE1c : PowerSeries.constantCoeff E1 = 1 := constantCoeff_expandJ hN
  have h4 := h0.sub h2
  have hfun : ∀ u : ℍ, 𝕢 1 (u : ℂ) ^ (N * N - N) * (𝕢 1 (u : ℂ) ^ N * j (scaleH N hN u)) -
      𝕢 1 (u : ℂ) ^ (N * N) * cosetVal hN c (scaleH N hN u) =
      𝕢 1 (u : ℂ) ^ (N * N) * (j (scaleH N hN u) - cosetVal hN c (scaleH N hN u)) := by
    intro u
    have : 𝕢 1 (u : ℂ) ^ (N * N) = 𝕢 1 (u : ℂ) ^ (N * N - N) * 𝕢 1 (u : ℂ) ^ N := by
      rw [← pow_add, Nat.sub_add_cancel hNN]
    rw [this]; ring
  have h5 := h4.congr hfun
  rcases lt_or_gt_of_ne haa with hlt | hgt
  · obtain ⟨m, hm⟩ : ∃ m, N * N - a * a = (N * N - N) + (m + 1) := ⟨N - a * a - 1, by omega⟩
    refine ⟨N * N - N, E1 - PowerSeries.X ^ (m + 1) * B2, ?_, ?_⟩
    · simp [hE1c]
    · convert h5 using 1
      rw [hm, pow_add]
      ring
  · obtain ⟨m, hm⟩ : ∃ m, N * N - N = (N * N - a * a) + (m + 1) := ⟨a * a - N - 1, by omega⟩
    refine ⟨N * N - a * a, PowerSeries.X ^ (m + 1) * E1 - B2, ?_, ?_⟩
    · simp [hB2]
    · convert h5 using 1
      rw [hm, pow_add]
      ring

/-- **Lowest term of the product.** -/
theorem expands_prod (hsq : ¬ IsSquare N) : ∃ (n : ℕ) (B : PowerSeries ℂ),
    ‖PowerSeries.constantCoeff B‖ = 1 ∧
    Expands (fun u ↦ 𝕢 1 (u : ℂ) ^ (N * N * Fintype.card (Cosets N)) *
      ∏ c : Cosets N, (j (scaleH N hN u) - cosetVal hN c (scaleH N hN u)))
      (PowerSeries.X ^ n * B) := by
  classical
  have key : ∀ s : Finset (Cosets N), ∃ (n : ℕ) (B : PowerSeries ℂ),
      ‖PowerSeries.constantCoeff B‖ = 1 ∧
      Expands (fun u ↦ 𝕢 1 (u : ℂ) ^ (N * N * s.card) *
        ∏ c ∈ s, (j (scaleH N hN u) - cosetVal hN c (scaleH N hN u)))
        (PowerSeries.X ^ n * B) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨0, 1, by simp, by simpa using expands_one⟩
    | insert a s ha ih =>
      obtain ⟨n1, B1, hB1, h1⟩ := expands_factor hN hsq a
      obtain ⟨n2, B2, hB2, h2⟩ := ih
      refine ⟨n1 + n2, B1 * B2, by simp [hB1, hB2], ?_⟩
      have h3 := h1.mul h2
      convert h3.congr (fun u ↦ ?_) using 1
      · rw [pow_add]; ring
      · rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, mul_add, mul_one, pow_add]
        ring
  exact key Finset.univ

/-- **Lowest term of a polynomial in $j(Nu)$.** For $P \in \mathbb Z[X]$ of degree $d$ and $M \ge Nd$,
$q^M P(j(Nu))$ is $q^{M - Nd}$ times a power series with constant coefficient $\mathrm{lc}(P)$, and that power series
is $0$ when $P = 0$. -/
theorem expands_poly (P : ℤ[X]) (M : ℕ) (hM : N * P.natDegree ≤ M) : ∃ B : PowerSeries ℂ,
    PowerSeries.constantCoeff B = (P.leadingCoeff : ℂ) ∧ (P = 0 → B = 0) ∧
    Expands (fun u ↦ 𝕢 1 (u : ℂ) ^ M * P.eval₂ (Int.castRingHom ℂ) (j (scaleH N hN u)))
      (PowerSeries.X ^ (M - N * P.natDegree) * B) := by
  set d := P.natDegree with hd
  set E := PowerSeries.expand N hN.ne' (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)) with hE
  have hEx := expands_qParam_pow_mul_j_scale hN
  refine ⟨∑ k ∈ Finset.range (d + 1), PowerSeries.C (P.coeff k : ℂ) * (PowerSeries.X ^ (N * (d - k)) * E ^ k),
    ?_, ?_, ?_⟩
  · rw [map_sum, Finset.sum_eq_single d]
    · have : PowerSeries.constantCoeff E = 1 := by
        rw [hE, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_expand]
        simpa using TauCeti.ModularForm.qExpansion_qParam_mul_j_coeff_zero
      simp only [map_mul, map_pow, PowerSeries.constantCoeff_C, this, Nat.sub_self, mul_zero,
        pow_zero, one_pow, mul_one, map_one]
      rfl
    · intro k hk hkd
      have hk' : k < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hkd
      have : N * (d - k) ≠ 0 := Nat.mul_ne_zero hN.ne' (by omega)
      simp only [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow this, zero_mul, mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self d)) h
  · intro hP
    have hd0 : d = 0 := by rw [hd, hP]; simp
    simp [hd0, hP]
  · have hsum := expands_finset_sum (Finset.range (d + 1))
      (fun k u ↦ 𝕢 1 (u : ℂ) ^ (M - N * d) * ((P.coeff k : ℂ) * (𝕢 1 (u : ℂ) ^ (N * (d - k)) *
        (𝕢 1 (u : ℂ) ^ N * j (scaleH N hN u)) ^ k)))
      (fun k ↦ PowerSeries.X ^ (M - N * d) * (PowerSeries.C (P.coeff k : ℂ) *
        (PowerSeries.X ^ (N * (d - k)) * E ^ k)))
      (fun k _ ↦ (expands_qParam_pow _).mul (((expands_qParam_pow _).mul (hEx.pow k)).const_mul _))
    rw [← Finset.mul_sum] at hsum
    refine hsum.congr fun u ↦ ?_
    rw [Polynomial.eval₂_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have : M = (M - N * d) + N * (d - k) + N * k := by
      have : N * k ≤ N * d := Nat.mul_le_mul_left _ hk'
      have h2 : N * (d - k) + N * k = N * d := by rw [← mul_add, Nat.sub_add_cancel hk']
      omega
    simp only [eq_intCast, mul_pow, ← pow_mul]
    have e : 𝕢 1 (u : ℂ) ^ M = 𝕢 1 (u : ℂ) ^ (M - N * d) * 𝕢 1 (u : ℂ) ^ (N * (d - k)) *
        𝕢 1 (u : ℂ) ^ (N * k) := by
      rw [← pow_add, ← pow_add, ← this]
    rw [e]
    ring

/-- **The leading coefficient of $P_N = F_N(X, X)$ is $\pm 1$ when $N$ is not a square.** -/
theorem leadingCoeff_diagPoly (hsq : ¬ IsSquare N) {F : MvPolynomial (Fin 2) ℤ}
    (hF : ∀ z : ℍ, MvPolynomial.eval₂ (Int.castRingHom ℂ[X]) ![C (j z), X] F = Φ hN z) :
    (diagPoly F).leadingCoeff = 1 ∨ (diagPoly F).leadingCoeff = -1 := by
  set P := diagPoly F with hP
  set d := P.natDegree with hd
  set D := Fintype.card (Cosets N) with hD
  obtain ⟨n, B, hB, hEB⟩ := expands_prod hN hsq
  have hM : N * d ≤ N * N * D + N * d := Nat.le_add_left _ _
  obtain ⟨B', hB'c, hB'0, hEB'⟩ := expands_poly hN P (N * N * D + N * d) hM
  have hsub : N * N * D + N * d - N * d = N * N * D := Nat.add_sub_cancel _ _
  rw [hsub] at hEB'
  have hprod := (expands_qParam_pow (N * d)).mul hEB
  have hfun : ∀ u : ℍ, 𝕢 1 (u : ℂ) ^ (N * d) * (𝕢 1 (u : ℂ) ^ (N * N * D) *
      ∏ c : Cosets N, (j (scaleH N hN u) - cosetVal hN c (scaleH N hN u))) =
      𝕢 1 (u : ℂ) ^ (N * N * D + N * d) * P.eval₂ (Int.castRingHom ℂ) (j (scaleH N hN u)) := by
    intro u
    rw [hP, eval_diagPoly_j hN hF (scaleH N hN u), pow_add]
    ring
  have hEq : PowerSeries.X ^ (N * N * D) * B' = PowerSeries.X ^ (N * d) * (PowerSeries.X ^ n * B) :=
    hEB'.unique ((hprod.congr hfun))
  have hBne : ∀ k, PowerSeries.X ^ k * B ≠ 0 → True := fun _ _ ↦ trivial
  have hB0 : B ≠ 0 := by
    intro h
    rw [h] at hB
    simp at hB
  have hRHS : PowerSeries.X ^ (N * d) * (PowerSeries.X ^ n * B) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) hB0)
  have hlc : ‖(P.leadingCoeff : ℂ)‖ = 1 := by
    rw [← mul_assoc, ← pow_add] at hEq
    have hRHS' : PowerSeries.X ^ (N * d + n) * B ≠ 0 := by
      rw [pow_add, mul_assoc]; exact hRHS
    set a := N * N * D
    set b := N * d + n
    rcases lt_trichotomy a b with hab | hab | hab
    · exfalso
      have := congrArg (PowerSeries.coeff a) hEq
      rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul'] at this
      simp only [le_refl, ite_true, Nat.sub_self, not_le.mpr hab, ite_false] at this
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hB'c] at this
      have hz : P = 0 := by
        have : P.leadingCoeff = 0 := by exact_mod_cast this
        exact Polynomial.leadingCoeff_eq_zero.mp this
      rw [hB'0 hz, mul_zero] at hEq
      exact hRHS' hEq.symm
    · have := congrArg (PowerSeries.coeff a) hEq
      rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul'] at this
      simp only [le_refl, ite_true, Nat.sub_self, ← hab] at this
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        hB'c] at this
      rw [this]; exact hB
    · exfalso
      have := congrArg (PowerSeries.coeff b) hEq
      rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul'] at this
      simp only [le_refl, ite_true, Nat.sub_self, not_le.mpr hab, ite_false] at this
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
      rw [← this] at hB
      simp at hB
  have h : |P.leadingCoeff| = 1 := by
    have h1 := hlc
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs] at h1
    exact_mod_cast h1
  rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp h with h | h
  exacts [Or.inl h, Or.inr h]

end ModularFormsKB.Milne.CMIntegral
