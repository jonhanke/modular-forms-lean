import ModularFormsKB.Milne.Ch6.Integrality
import ModularFormsKB.Milne.Ch6.KroneckerAlgebra
import ModularFormsKB.Milne.Ch6.ModularEquationGeneral

/-!
# Milne, Theorem 6.1: Kronecker's modular equation, unconditionally

`CosetPolynomialArithmetic N` holds for every $N \ge 1$ (`cosetPolynomialArithmetic`), hence `ModularEquation N`
(`modularEquation`).
- **Integrality**: `ModularFormsKB.Milne.LevelTwo.coeff_coeff_isInt` gives an integer polynomial
  $F(X, Y) = \sum_{k,i} n_{k,i} X^i Y^k$ with $F(j(z), Y) = \prod_c (Y - j(N\gamma_c z))$ (`exists_int_double_sum`).
- **Kronecker's congruence** for $N = p$ prime (Milne, pdf p. 89; argued here without $\mathbb Z[\zeta_p]$): the identity
  $F(j(z), j(pz)) = 0$, multiplied by $q^M$, is an identity $\sum n_{k,i} q^{M-i-pk} P^i P(q^p)^k = 0$ in
  $\mathbb Z[[q]]$, $P = qj$. Modulo $p$, $P(q^p) = P^p$ (`ModularFormsKB.Milne.Triangular.pow_char_eq_expand`), so
  $\bar g(X) = \bar F(X, X^p)$ satisfies $q^M \bar g(j) = 0$, hence $\bar g = 0$
  (`ModularFormsKB.Milne.Triangular.eq_zero_of_homog_eq_zero`). With the symmetry of $F$
  (`ModularFormsKB.Milne.LevelTwo.rename_swap_eq_of_eval₂_eq_Φ`) and $\psi(p) = p + 1$
  (`CongruenceSubgroup.Gamma0_prime_index`), `ModularFormsKB.Milne.KroneckerAlgebra.eq_kronecker` gives
  $\bar F = X^{p+1} + Y^{p+1} - X^pY^p - XY$.
-/

open UpperHalfPlane CongruenceSubgroup Polynomial
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.LevelTwo

open TauCeti.ModularForm QSeries

local notation "𝕢" => Function.Periodic.qParam

/-- The double sum $\sum_{k \le K}\sum_{i \le D} n_{k,i} X^iY^k$. -/
def doubleSum (K D : ℕ) (n : ℕ → ℕ → ℤ) : MvPolynomial (Fin 2) ℤ :=
  ∑ k ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (D + 1),
    MvPolynomial.C (n k i) * MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ k

variable {N : ℕ} (hN : 0 < N) [NeZero N]

/-- **An integer polynomial for the coset product.** -/
theorem exists_int_double_sum : ∃ (D : ℕ) (n : ℕ → ℕ → ℤ), ∀ z : ℍ,
    MvPolynomial.eval₂ (Int.castRingHom ℂ[X]) ![C (j z), X] (doubleSum (Gamma0 N).index D n) = Φ hN z := by
  classical
  obtain ⟨F, hFm, hFdeg, hF⟩ := exists_coset_polynomial hN
  choose n hn using coeff_coeff_isInt hN hF
  set ψ := (Gamma0 N).index with hψ
  set D := (Finset.range (ψ + 1)).sup fun k ↦ (F.coeff k).natDegree with hDdef
  have hdegk : ∀ k ∈ Finset.range (ψ + 1), (F.coeff k).natDegree < D + 1 := fun k hk ↦
    Nat.lt_succ_of_le (Finset.le_sup (f := fun k ↦ (F.coeff k).natDegree) hk)
  refine ⟨D, n, fun z ↦ ?_⟩
  rw [← hF z]
  have hmapdeg : (F.map (evalRingHom (j z))).natDegree < ψ + 1 :=
    lt_of_le_of_lt natDegree_map_le (by rw [hFdeg]; exact Nat.lt_succ_self _)
  conv_rhs => rw [(F.map (evalRingHom (j z))).as_sum_range' (ψ + 1) hmapdeg]
  rw [doubleSum, ← MvPolynomial.coe_eval₂Hom, map_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [coeff_map, coe_evalRingHom, eval_eq_sum_range' (hdegk k hk), ← C_mul_X_pow_eq_monomial, map_sum,
    map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [map_mul, map_pow, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← hn k i, eq_intCast, ← C_eq_intCast]

omit [NeZero N] in
/-- Evaluating the double sum at $(x, y)$. -/
theorem eval_eval₂_doubleSum (K D : ℕ) (n : ℕ → ℕ → ℤ) (x y : ℂ) :
    (MvPolynomial.eval₂ (Int.castRingHom ℂ[X]) ![C x, X] (doubleSum K D n)).eval y =
      ∑ k ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (D + 1), (n k i : ℂ) * x ^ i * y ^ k := by
  rw [doubleSum, ← MvPolynomial.coe_eval₂Hom]
  simp only [map_sum, map_mul, map_pow, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [eq_intCast, eval_finsetSum, eval_mul, eval_pow, eval_intCast, eval_C, eval_X]

/-- **The formal identity** $\sum_{k,i} n_{k,i}\, q^{M-i-Nk} P^i P(q^N)^k = 0$ in $\mathbb Z[[q]]$, $P = qj$,
$M = D + N\psi$: the $q$-expansion of $q^M F(j(z), j(Nz)) = 0$. -/
theorem formal_identity {D : ℕ} {n : ℕ → ℕ → ℤ}
    (hFz : ∀ z : ℍ, MvPolynomial.eval₂ (Int.castRingHom ℂ[X]) ![C (j z), X]
      (doubleSum (Gamma0 N).index D n) = Φ hN z)
    (Pz : PowerSeries ℤ)
    (hPz : PowerSeries.map (Int.castRingHom ℂ) Pz = qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)) :
    ∑ k ∈ Finset.range ((Gamma0 N).index + 1), ∑ i ∈ Finset.range (D + 1),
      PowerSeries.C (n k i) * (PowerSeries.X ^ (D + N * (Gamma0 N).index - i - N * k) * Pz ^ i *
        (PowerSeries.expand N hN.ne' Pz) ^ k) = 0 := by
  set ψ := (Gamma0 N).index with hψ
  set M := D + N * ψ with hM
  apply PowerSeries.map_injective (Int.castRingHom ℂ) (RingHom.injective_int _)
  rw [map_zero]
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, PowerSeries.map_expand, hPz]
  have hexp : Expands (fun z : ℍ ↦ ∑ k ∈ Finset.range (ψ + 1), ∑ i ∈ Finset.range (D + 1),
      ((Int.castRingHom ℂ) (n k i)) * (𝕢 1 (z : ℂ) ^ (M - i - N * k) * (𝕢 1 (z : ℂ) * j z) ^ i *
        (𝕢 1 (z : ℂ) ^ N * j (scaleH N hN z)) ^ k)) _ :=
    Expands.sum _ fun k _ ↦ Expands.sum _ fun i _ ↦ Expands.const_mul _
      (((expands_qParam_pow _).mul (expands_qParam_mul_j.pow i)).mul
        ((expands_qParam_pow_mul_j_scale hN).pow k))
  refine hexp.unique (expands_zero.congr fun z ↦ ?_)
  have h0 := Φ_eval_jN hN z
  rw [← hFz z, eval_eval₂_doubleSum] at h0
  have hsum : (∑ k ∈ Finset.range (ψ + 1), ∑ i ∈ Finset.range (D + 1),
      ((Int.castRingHom ℂ) (n k i)) * (𝕢 1 (z : ℂ) ^ (M - i - N * k) * (𝕢 1 (z : ℂ) * j z) ^ i *
        (𝕢 1 (z : ℂ) ^ N * j (scaleH N hN z)) ^ k)) =
      𝕢 1 (z : ℂ) ^ M * ∑ k ∈ Finset.range (ψ + 1), ∑ i ∈ Finset.range (D + 1),
        (n k i : ℂ) * j z ^ i * jN hN z ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hk' : k ≤ ψ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hi' : i ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hNk : N * k ≤ N * ψ := Nat.mul_le_mul_left N hk'
    have hMe : 𝕢 1 (z : ℂ) ^ M =
        𝕢 1 (z : ℂ) ^ (M - i - N * k) * 𝕢 1 (z : ℂ) ^ i * (𝕢 1 (z : ℂ) ^ N) ^ k := by
      rw [← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega
    rw [hMe, eq_intCast]
    simp only [jN]
    ring
  rw [hsum, h0, mul_zero]

/-- **Kronecker's congruence** for the double sum: if $N = p$ is prime then
$F \equiv X^{p+1} + Y^{p+1} - X^pY^p - XY \pmod p$. -/
theorem kronecker_congruence {D : ℕ} {n : ℕ → ℕ → ℤ}
    (hFz : ∀ z : ℍ, MvPolynomial.eval₂ (Int.castRingHom ℂ[X]) ![C (j z), X]
      (doubleSum (Gamma0 N).index D n) = Φ hN z) (hp : N.Prime) :
    MvPolynomial.map (Int.castRingHom (ZMod N)) (doubleSum (Gamma0 N).index D n) =
      MvPolynomial.X 0 ^ (N + 1) + MvPolynomial.X 1 ^ (N + 1) -
        MvPolynomial.X 0 ^ N * MvPolynomial.X 1 ^ N - MvPolynomial.X 0 * MvPolynomial.X 1 := by
  classical
  have : Fact N.Prime := ⟨hp⟩
  set ψ := (Gamma0 N).index with hψ
  have hψp : ψ = N + 1 := CongruenceSubgroup.Gamma0_prime_index N hp
  set Fz := doubleSum ψ D n with hFzdef
  set G := MvPolynomial.map (Int.castRingHom (ZMod N)) Fz with hG
  set Pz := MvPolynomial.eval₂ (C.comp C) ![(C X : ℤ[X][X]), X] Fz with hPzdef
  have hPz_def : MvPolynomial.eval₂ (C.comp C) ![C X, X] G =
      Pz.map (mapRingHom (Int.castRingHom (ZMod N))) := by
    have : (MvPolynomial.eval₂Hom (C.comp C) ![(C X : (ZMod N)[X][X]), X]).comp
        (MvPolynomial.map (Int.castRingHom (ZMod N))) =
        (mapRingHom (mapRingHom (Int.castRingHom (ZMod N)))).comp
          (MvPolynomial.eval₂Hom (C.comp C) ![(C X : ℤ[X][X]), X]) :=
      MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun i ↦ by fin_cases i <;> simp)
    exact congrArg (fun f ↦ f Fz) this
  have hPc : ∀ z : ℍ, (Pz.map (mapRingHom (Int.castRingHom ℂ))).map (evalRingHom (j z)) = Φ hN z := by
    intro z
    rw [← hFz z]
    have : (mapRingHom (evalRingHom (j z))).comp ((mapRingHom (mapRingHom (Int.castRingHom ℂ))).comp
        (MvPolynomial.eval₂Hom (C.comp C) ![(C X : ℤ[X][X]), X])) =
        MvPolynomial.eval₂Hom (Int.castRingHom ℂ[X]) ![C (j z), X] :=
      MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun i ↦ by fin_cases i <;> simp)
    exact congrArg (fun f ↦ f Fz) this
  obtain ⟨F₀, hF₀m, hF₀deg, hF₀⟩ := exists_coset_polynomial hN
  have hPcF : Pz.map (mapRingHom (Int.castRingHom ℂ)) = F₀ :=
    eq_of_map_eval_j_eq fun z ↦ by rw [hPc z, hF₀ z]
  have hinj : Function.Injective (mapRingHom (Int.castRingHom ℂ)) :=
    Polynomial.map_injective _ (RingHom.injective_int _)
  have hPzdeg : Pz.natDegree = ψ := by
    rw [hψ, ← hF₀deg, ← hPcF, natDegree_map_eq_of_injective hinj]
  have hPzm : Pz.Monic := by
    have h1 : (Pz.map (mapRingHom (Int.castRingHom ℂ))).leadingCoeff = 1 := by rw [hPcF]; exact hF₀m
    rw [leadingCoeff_map_of_injective hinj] at h1
    exact hinj (by rw [h1, map_one])
  refine KroneckerAlgebra.eq_kronecker N hp.two_le G ?_ ?_ ?_ ?_
  · rw [hG, ← MvPolynomial.map_rename, rename_swap_eq_of_eval₂_eq_Φ hN hp.one_lt hFz]
  · -- `G(X, X^p) = 0`
    obtain ⟨Pz', hPz'⟩ := (JCoefficients.mem_range_int_iff _).2 JCoefficients.j_coeff_isInt
    have hform := formal_identity hN hFz Pz' hPz'
    rw [← hψ] at hform
    set M := D + N * ψ with hM
    set Pb := PowerSeries.map (Int.castRingHom (ZMod N)) Pz' with hPb
    have hPz0 : PowerSeries.constantCoeff Pz' = 1 := by
      have h1 := congrArg (PowerSeries.coeff 0) hPz'
      rw [PowerSeries.coeff_map, qExpansion_qParam_mul_j_coeff_zero,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, eq_intCast] at h1
      exact_mod_cast h1
    have hPb0 : PowerSeries.constantCoeff Pb = 1 := by
      rw [hPb, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hPz0, map_one]
    have hmod := congrArg (PowerSeries.map (Int.castRingHom (ZMod N))) hform
    simp only [map_sum, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, PowerSeries.map_expand,
      map_zero] at hmod
    rw [← hPb, ← Triangular.pow_char_eq_expand] at hmod
    set g : (ZMod N)[X] := ∑ k ∈ Finset.range (ψ + 1), ∑ i ∈ Finset.range (D + 1),
      Polynomial.C ((n k i : ZMod N)) * X ^ (i + N * k) with hgdef
    have hhom : Triangular.homog Pb M (fun m ↦ g.coeff m) = 0 := by
      rw [hgdef, Triangular.homog_sum_coeff, ← hmod]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [Triangular.homog_sum_coeff]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hk' : k ≤ ψ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have hi' : i ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hNk : N * k ≤ N * ψ := Nat.mul_le_mul_left N hk'
      rw [Triangular.homog_C_mul_X_pow _ _ _ (by omega), eq_intCast, Nat.sub_sub, ← pow_mul]
      ring
    have hcoeff := Triangular.eq_zero_of_homog_eq_zero Pb hPb0 M (fun m ↦ g.coeff m) hhom
    have hgdeg : g.natDegree ≤ M := by
      refine natDegree_sum_le_of_forall_le _ _ fun k hk ↦ natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_
      have hk' : k ≤ ψ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have hi' : i ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hNk : N * k ≤ N * ψ := Nat.mul_le_mul_left N hk'
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [natDegree_X_pow]
      omega
    have hg0 : g = 0 := by
      ext m
      rw [coeff_zero]
      by_cases hm : m ≤ M
      · exact hcoeff m hm
      · exact coeff_eq_zero_of_natDegree_lt (by omega)
    have hGg : MvPolynomial.aeval ![(X : (ZMod N)[X]), X ^ N] G = g := by
      rw [hG, hFzdef, doubleSum, hgdef]
      simp only [map_sum, map_mul, map_pow, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.aeval_C,
        MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
      refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Polynomial.algebraMap_eq, ← pow_mul, eq_intCast]
      ring
    rw [hGg, hg0]
  · rw [hPz_def]
    exact hPzm.map _
  · rw [hPz_def, hPzm.natDegree_map, hPzdeg, hψp]

end ModularFormsKB.Milne.LevelTwo

namespace ModularFormsKB.Milne

open LevelTwo

/-- **The arithmetic of the coset polynomial, for every $N$**: integrality and Kronecker's congruence. -/
theorem LevelTwo.cosetPolynomialArithmetic (N : ℕ) (hN : 0 < N) : CosetPolynomialArithmetic N hN := by
  have : NeZero N := NeZero.of_pos hN
  obtain ⟨D, n, hFz⟩ := exists_int_double_sum hN
  exact ⟨⟨doubleSum (Gamma0 N).index D n, hFz, kronecker_congruence hN hFz⟩⟩

/-- **Milne, Theorem 6.1 (Kronecker's modular equation), unconditionally, for every $N \ge 1$.** -/
@[kb "milne2017mf" "Section 6, Theorem 6.1 (pdf p. 88)"]
theorem modularEquation (N : ℕ) (hN : 0 < N) : ModularEquation N hN :=
  modularEquation_of_cosetPolynomialArithmetic hN (cosetPolynomialArithmetic N hN)

end ModularFormsKB.Milne
