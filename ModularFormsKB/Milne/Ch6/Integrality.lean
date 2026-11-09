import ModularFormsKB.Milne.Ch6.CosetExpansion
import ModularFormsKB.Milne.Ch6.Triangular

/-!
# The modular polynomial has integer coefficients

Milne, Section 6, proof of Theorem 6.1 (pdf p. 88). Let $F \in \mathbb C[X][Y]$ with
$F(j(z), Y) = \prod_c (Y - j(N\gamma_c z))$, and let $f = F_k \in \mathbb C[X]$ be the coefficient of $Y^k$, of degree
$\le D$. With $z = Nu$, $q = e^{2\pi i u}$:
- $q^{N^2(\psi - k)} f(j(z))$ is a $q$-series with algebraic integer coefficients (`expands_coeff_prod`,
  `expands_coset`);
- $q^{ND} f(j(z)) = \sum_i f_i q^{N(D-i)}(q^N j(Nu))^i$ is the $q$-series
  $\operatorname{expand}_N(\sum_i f_i X^{D-i} P^i)$, $P = qj$ (`expands_homog_scale`).
By uniqueness of $q$-expansions the coefficients of $\sum_i f_i X^{D-i}P^i$ are algebraic integers; they are rational
(`coeff_coeff_isRat`), hence integers, and since $P \in \mathbb Z[[q]]$ has constant term 1, all $f_i$ are integers
(`ModularFormsKB.Milne.Triangular.mem_of_homog_mem`). Hence `exists_int_eval₂_eq_Φ`: an integer polynomial
$F(X, Y)$ with $F(j(z), Y) = \prod_c (Y - j(N\gamma_c z))$.
-/

open UpperHalfPlane CongruenceSubgroup Polynomial
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.LevelTwo

open TauCeti.ModularForm QSeries

local notation "𝕢" => Function.Periodic.qParam

variable {N : ℕ} (hN : 0 < N)

/-- $q^{ND} f(j(Nu)) = \sum_i f_i\, q^{N(D-i)}(q^N j(Nu))^i$ as a $q$-series. -/
theorem expands_homog_scale (f : ℂ[X]) (D : ℕ) (hD : f.natDegree ≤ D) :
    Expands (fun u ↦ 𝕢 1 (u : ℂ) ^ (N * D) * f.eval (j (scaleH N hN u)))
      (PowerSeries.expand N hN.ne'
        (Triangular.homog (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)) D f.coeff)) := by
  set P := qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ) with hP
  have hser : PowerSeries.expand N hN.ne' (Triangular.homog P D f.coeff) =
      ∑ i ∈ Finset.range (D + 1), PowerSeries.C (f.coeff i) *
        ((PowerSeries.X ^ N) ^ (D - i) * (PowerSeries.expand N hN.ne' P) ^ i) := by
    simp only [Triangular.homog, map_sum, map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  rw [hser]
  refine (Expands.sum _ fun i _ ↦ (((expands_qParam_pow N).pow (D - i)).mul
    ((expands_qParam_pow_mul_j_scale hN).pow i)).const_mul (f.coeff i)).congr fun u ↦ ?_
  rw [eval_eq_sum_range' (n := D + 1) (by omega), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi : i ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have e : N * D = N * (D - i) + N * i := by rw [← mul_add]; congr 1; omega
  rw [e, pow_add, pow_mul, pow_mul]
  ring

variable [NeZero N]

/-- **The coset polynomial has integer coefficients.** -/
theorem coeff_coeff_isInt {F : ℂ[X][X]} (hF : ∀ z : ℍ, F.map (evalRingHom (j z)) = Φ hN z) (k i : ℕ) :
    ∃ r : ℤ, (r : ℂ) = (F.coeff k).coeff i := by
  classical
  obtain ⟨F₀, hF₀m, hF₀deg, hF₀⟩ := exists_coset_polynomial hN
  have hFF : F = F₀ := eq_of_map_eval_j_eq fun z ↦ by rw [hF z, hF₀ z]
  subst hFF
  set ψ := (Gamma0 N).index with hψ
  by_cases hk : ψ < k
  · exact ⟨0, by rw [coeff_eq_zero_of_natDegree_lt (p := F) (n := k) (by rwa [hF₀deg])]; simp⟩
  replace hk : k ≤ ψ := not_lt.1 hk
  set f := F.coeff k with hfdef
  set D := f.natDegree with hDdef
  set P := qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ) with hP
  have hΦk : ∀ z, (Φ hN z).coeff k = f.eval (j z) := by
    intro z
    rw [← hF z, coeff_map]
    rfl
  -- The algebraic integer expansion of `q^{N²(ψ-k)} f(j(Nu))`.
  obtain ⟨B, hB, hEB⟩ := expands_coeff_prod (S := algInt) (N * N) (Finset.univ : Finset (Cosets N))
    (fun c u ↦ cosetVal hN c (scaleH N hN u)) (fun c _ ↦ expands_coset hN c) k
    (by rw [Finset.card_univ, card_cosets]; exact hk)
  rw [Finset.card_univ, card_cosets] at hEB
  have hE := expands_homog_scale hN f D le_rfl
  have h1 := (expands_qParam_pow (N * N * (ψ - k))).mul hE
  have h2 := (expands_qParam_pow (N * D)).mul hEB
  have heq := Expands.unique h1 (h2.congr fun u ↦ by
    show 𝕢 1 (u : ℂ) ^ (N * D) * (𝕢 1 (u : ℂ) ^ (N * N * (ψ - k)) * (Φ hN (scaleH N hN u)).coeff k) = _
    rw [hΦk]
    ring)
  have hEint : ∀ n, PowerSeries.coeff n (PowerSeries.expand N hN.ne' (Triangular.homog P D f.coeff)) ∈
      algInt := by
    intro n
    have := congrArg (PowerSeries.coeff (n + N * N * (ψ - k))) heq
    rw [PowerSeries.coeff_X_pow_mul,
      PowerSeries.coeff_X_pow_mul'] at this
    rw [this]
    split_ifs
    · exact mem_coeffSubring.1 hB _
    · exact Subring.zero_mem _
  have hHint : ∀ n, PowerSeries.coeff n (Triangular.homog P D f.coeff) ∈ algInt := fun n ↦ by
    have := hEint (N * n)
    rwa [PowerSeries.coeff_expand_mul] at this
  -- Rationality.
  have hPmem : P ∈ (PowerSeries.map (Rat.castHom ℂ)).range :=
    (JCoefficients.mem_range_iff _).2 JCoefficients.j_coeff_isRat
  have hHrat : Triangular.homog P D f.coeff ∈ (PowerSeries.map (Rat.castHom ℂ)).range := by
    refine Subring.sum_mem _ fun i _ ↦ Subring.mul_mem _ (Subring.mul_mem _ ?_ ?_) (Subring.pow_mem _ hPmem _)
    · obtain ⟨r, hr⟩ := coeff_coeff_isRat hN hF₀ k i
      exact ⟨PowerSeries.C r, by rw [PowerSeries.map_C]; simp [hr, hfdef]⟩
    · exact ⟨PowerSeries.X ^ (D - i), by simp⟩
  have hHZ : ∀ n, PowerSeries.coeff n (Triangular.homog P D f.coeff) ∈ (Int.castRingHom ℂ).range := by
    intro n
    obtain ⟨r, hr⟩ := (JCoefficients.mem_range_iff _).1 hHrat n
    obtain ⟨m, hm⟩ := exists_int_of_rat_of_isIntegral r (by rw [hr]; exact mem_algInt.1 (hHint n))
    exact ⟨m, by rw [← hr, ← hm]; simp⟩
  have hPZ : ∀ n, PowerSeries.coeff n P ∈ (Int.castRingHom ℂ).range := fun n ↦ by
    obtain ⟨r, hr⟩ := JCoefficients.j_coeff_isInt n
    exact ⟨r, by simpa using hr⟩
  have hP0 : PowerSeries.constantCoeff P = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact qExpansion_qParam_mul_j_coeff_zero
  by_cases hi : i ≤ D
  · obtain ⟨m, hm⟩ := Triangular.mem_of_homog_mem _ P hPZ hP0 D f.coeff hHZ i hi
    exact ⟨m, by simpa using hm⟩
  · exact ⟨0, by rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp⟩

end ModularFormsKB.Milne.LevelTwo
