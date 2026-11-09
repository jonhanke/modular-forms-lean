import ModularFormsKB.Milne.Ch6.QSeries
import ModularFormsKB.Milne.Ch6.JRational
import ModularFormsKB.Milne.Ch6.Uniqueness

/-!
# The modular polynomial has rational coefficients

Milne, Section 6, proof of Theorem 6.1 (pdf p. 88). Let $F \in \mathbb C[X][Y]$ with
$F(j(z), Y) = \prod_{\Gamma_0(N)\gamma}(Y - j(N\gamma z))$. Multiplying $F(j(z), j(Nz)) = 0$ by $q^M$ gives an identity of
absolutely convergent $q$-series $\sum_{k,i} c_{k,i}\,U_{k,i} = 0$, $U_{k,i} = q^{M - i - Nk}(qj)^i(q^Nj(Nz))^k$, whose
coefficient series $U_{k,i}$ are rational (`ModularFormsKB.Milne.JCoefficients.j_coeff_isRat`). For a $\mathbb Q$-linear
$\lambda : \mathbb C \to \mathbb Q$ with $\lambda|_{\mathbb Q} = \mathrm{id}$, the numbers $\lambda(c_{k,i})$ solve the same
system, so they are the coefficients of a monic relation of $Y$-degree $\psi$ between $j(z)$ and $j(Nz)$, which is $F$
(`ModularFormsKB.Milne.LevelTwo.eq_of_eval_j_jN`). Hence $c_{k,i} = \lambda(c_{k,i}) \in \mathbb Q$
(`coeff_coeff_isRat`).
-/

open UpperHalfPlane CongruenceSubgroup Polynomial
open scoped MatrixGroups Manifold

noncomputable section

namespace ModularFormsKB.Milne.LevelTwo

open TauCeti.ModularForm QSeries

local notation "𝕢" => Function.Periodic.qParam

/-- A $\mathbb Q$-linear retraction $\mathbb C \to \mathbb Q$. -/
theorem exists_rat_retraction : ∃ l : ℂ →ₗ[ℚ] ℚ, ∀ r : ℚ, l (r : ℂ) = r := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℚ (one_ne_zero : (1 : ℂ) ≠ 0)
  refine ⟨(φ 1)⁻¹ • φ, fun r ↦ ?_⟩
  have h : (r : ℂ) = r • (1 : ℂ) := by rw [Rat.smul_def, mul_one]
  rw [h, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  field_simp

theorem expands_zero : Expands (fun _ ↦ 0) 0 := by
  have := Expands.const_mul 0 expands_one
  simpa using this

theorem Expands.sum {ι : Type*} (s : Finset ι) {f : ι → ℍ → ℂ} {A : ι → PowerSeries ℂ}
    (h : ∀ i ∈ s, Expands (f i) (A i)) : Expands (fun z ↦ ∑ i ∈ s, f i z) (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using expands_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

theorem Expands.eq_zero_of_eq_zero {f : ℍ → ℂ} (hf : Expands f 0) (z : ℍ) : f z = 0 := by
  have := (hf z).2
  simp only [map_zero, zero_mul] at this
  exact this.unique hasSum_zero

/-- **The coset polynomial has rational coefficients.** -/
theorem coeff_coeff_isRat {N : ℕ} [NeZero N] (hN : 0 < N) {F : ℂ[X][X]}
    (hF : ∀ z : ℍ, F.map (evalRingHom (j z)) = Φ hN z) (k i : ℕ) :
    ∃ r : ℚ, (r : ℂ) = (F.coeff k).coeff i := by
  classical
  obtain ⟨F₀, hF₀m, hF₀deg, hF₀⟩ := exists_coset_polynomial hN
  have hFF : F = F₀ := eq_of_map_eval_j_eq fun z ↦ by rw [hF z, hF₀ z]
  subst hFF
  set ψ := (Gamma0 N).index with hψ
  set P := qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ) with hPdef
  set D := (Finset.range (ψ + 1)).sup fun k ↦ (F.coeff k).natDegree with hDdef
  set M := D + N * ψ with hMdef
  let U : ℕ → ℕ → PowerSeries ℂ := fun k i ↦
    PowerSeries.X ^ (M - i - N * k) * P ^ i * (PowerSeries.expand N hN.ne' P) ^ k
  let S : (ℕ → ℕ → ℂ) → PowerSeries ℂ := fun c ↦
    ∑ k ∈ Finset.range (ψ + 1), ∑ i ∈ Finset.range (D + 1), PowerSeries.C (c k i) * U k i
  let G : (ℕ → ℕ → ℂ) → ℂ[X][X] := fun c ↦
    ∑ k ∈ Finset.range (ψ + 1), C (∑ i ∈ Finset.range (D + 1), C (c k i) * X ^ i) * X ^ k
  -- `q^M G(c)(j, j_N)` expands with coefficients `S c`.
  have hexp : ∀ c, Expands (fun z ↦ 𝕢 1 (z : ℂ) ^ M * ((G c).map (evalRingHom (j z))).eval (jN hN z))
      (S c) := by
    intro c
    have hfun : (fun z : ℍ ↦ 𝕢 1 (z : ℂ) ^ M * ((G c).map (evalRingHom (j z))).eval (jN hN z)) =
        fun z : ℍ ↦ ∑ k ∈ Finset.range (ψ + 1), ∑ i ∈ Finset.range (D + 1), c k i *
          (𝕢 1 (z : ℂ) ^ (M - i - N * k) * (𝕢 1 (z : ℂ) * j z) ^ i *
            (𝕢 1 (z : ℂ) ^ N * j (scaleH N hN z)) ^ k) := by
      funext z
      simp only [G, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_C, eval_finsetSum, eval_mul, eval_pow, eval_X, eval_C, coe_evalRingHom,
        Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k hk ↦ Finset.sum_congr rfl fun i hi ↦ ?_
      have hk' : k ≤ ψ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have hi' : i ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hNk : N * k ≤ N * ψ := Nat.mul_le_mul_left N hk'
      have hM : 𝕢 1 (z : ℂ) ^ M =
          𝕢 1 (z : ℂ) ^ (M - i - N * k) * 𝕢 1 (z : ℂ) ^ i * (𝕢 1 (z : ℂ) ^ N) ^ k := by
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 1
        omega
      rw [hM]
      simp only [jN]
      ring
    rw [hfun]
    refine Expands.sum _ fun k _ ↦ Expands.sum _ fun i _ ↦ ?_
    exact Expands.const_mul _ (((expands_qParam_pow _).mul (expands_qParam_mul_j.pow i)).mul
      ((expands_qParam_pow_mul_j_scale hN).pow k))
  -- `G c₀ = F` for the coefficients `c₀` of `F`.
  let c₀ : ℕ → ℕ → ℂ := fun k i ↦ (F.coeff k).coeff i
  have hdegk : ∀ k ∈ Finset.range (ψ + 1), (F.coeff k).natDegree < D + 1 := fun k hk ↦
    Nat.lt_succ_of_le (Finset.le_sup (f := fun k ↦ (F.coeff k).natDegree) hk)
  have hG₀ : G c₀ = F := by
    conv_rhs => rw [F.as_sum_range' (ψ + 1) (by rw [hF₀deg]; exact Nat.lt_succ_self _)]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    conv_rhs => rw [(F.coeff k).as_sum_range' (D + 1) (hdegk k hk)]
    rw [C_mul_X_pow_eq_monomial]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [C_mul_X_pow_eq_monomial]
  -- `S c₀ = 0`.
  have hS₀ : S c₀ = 0 := by
    have h1 := hexp c₀
    rw [hG₀] at h1
    have hzero : (fun z : ℍ ↦ 𝕢 1 (z : ℂ) ^ M * (F.map (evalRingHom (j z))).eval (jN hN z)) =
        fun _ ↦ 0 := by
      funext z
      rw [hF₀ z, Φ_eval_jN, mul_zero]
    rw [hzero] at h1
    exact h1.unique expands_zero
  -- The series `U k i` have rational coefficients.
  have hPmem : P ∈ (PowerSeries.map (Rat.castHom ℂ)).range :=
    (JCoefficients.mem_range_iff _).2 JCoefficients.j_coeff_isRat
  have hEmem : PowerSeries.expand N hN.ne' P ∈ (PowerSeries.map (Rat.castHom ℂ)).range := by
    refine (JCoefficients.mem_range_iff _).2 fun n ↦ ?_
    by_cases hdvd : N ∣ n
    · obtain ⟨m, rfl⟩ := hdvd
      obtain ⟨r, hr⟩ := JCoefficients.j_coeff_isRat m
      refine ⟨r, ?_⟩
      rw [PowerSeries.coeff_expand_mul, hr]
    · exact ⟨0, by rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hdvd, Rat.cast_zero]⟩
  have hU : ∀ k i n, ∃ u : ℚ, (u : ℂ) = (U k i).coeff n := by
    intro k i
    refine (JCoefficients.mem_range_iff _).1 ?_
    refine Subring.mul_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (RingHom.mem_range.2 ⟨PowerSeries.X, PowerSeries.map_X _⟩) _)
      (Subring.pow_mem _ hPmem _)) (Subring.pow_mem _ hEmem _)
  choose u hu using hU
  -- Apply a rational retraction to the coefficients.
  obtain ⟨l, hl⟩ := exists_rat_retraction
  let c' : ℕ → ℕ → ℂ := fun k i ↦ ((l (c₀ k i) : ℚ) : ℂ)
  have hS' : S c' = 0 := by
    ext n
    have h0 := congrArg (PowerSeries.coeff n) hS₀
    simp only [S, map_sum, PowerSeries.coeff_C_mul, map_zero] at h0 ⊢
    have hrw : (∑ k ∈ Finset.range (ψ + 1), ∑ i ∈ Finset.range (D + 1), c' k i * (U k i).coeff n) =
        ((l (∑ k ∈ Finset.range (ψ + 1), ∑ i ∈ Finset.range (D + 1), c₀ k i * (U k i).coeff n) : ℚ) :
          ℂ) := by
      rw [map_sum, Rat.cast_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [map_sum, Rat.cast_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hsm : (↑(u k i n) : ℂ) * c₀ k i = (u k i n) • c₀ k i := (Rat.smul_def _ _).symm
      rw [← hu k i n, mul_comm (c₀ k i), hsm, map_smul, smul_eq_mul, Rat.cast_mul, mul_comm]
    rw [hrw, h0, map_zero, Rat.cast_zero]
  -- `G c'` is a monic relation of degree `ψ`, hence equal to `F`.
  have hG'0 : ∀ z : ℍ, ((G c').map (evalRingHom (j z))).eval (jN hN z) = 0 := by
    intro z
    have h := (hexp c')
    rw [hS'] at h
    have h2 := Expands.eq_zero_of_eq_zero h z
    exact (mul_eq_zero.1 h2).resolve_left (pow_ne_zero _ (Function.Periodic.qParam_ne_zero _))
  have hcoeffG : ∀ c k, (G c).coeff k =
      if k ∈ Finset.range (ψ + 1) then ∑ i ∈ Finset.range (D + 1), C (c k i) * X ^ i else 0 := by
    intro c k
    simp only [G, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
  have hF₀ψ : F.coeff ψ = 1 := by
    have := hF₀m.coeff_natDegree
    rwa [hF₀deg] at this
  have hl1 : ((l (1 : ℂ) : ℚ) : ℂ) = 1 := by
    have := hl 1
    rw [Rat.cast_one] at this
    rw [this, Rat.cast_one]
  have hG'ψ : (G c').coeff ψ = 1 := by
    rw [hcoeffG, if_pos (Finset.mem_range.2 (Nat.lt_succ_self _))]
    have : ∀ i ∈ Finset.range (D + 1), C (c' ψ i) * X ^ i = if i = 0 then (1 : ℂ[X]) else 0 := by
      intro i _
      simp only [c', c₀, hF₀ψ, coeff_one]
      split_ifs with h
      · subst h; simp [hl1]
      · simp
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    simp
  have hG'le : (G c').natDegree ≤ ψ := by
    refine natDegree_le_iff_coeff_eq_zero.2 fun m hm ↦ ?_
    rw [hcoeffG, if_neg]
    intro hmem
    have := Finset.mem_range.1 hmem
    have hm' : ψ < m := by exact_mod_cast hm
    omega
  have hG'm : (G c').Monic := monic_of_natDegree_le_of_coeff_eq_one ψ hG'le hG'ψ
  have hG'deg : (G c').natDegree = ψ :=
    le_antisymm hG'le (le_natDegree_of_ne_zero (by rw [hG'ψ]; exact one_ne_zero))
  have hGF : G c' = F := eq_of_eval_j_jN hN hG'm hF₀m hG'deg hF₀deg hG'0
    (fun z ↦ by rw [hF₀ z]; exact Φ_eval_jN hN z)
  -- Conclude.
  by_cases hk : k ∈ Finset.range (ψ + 1)
  · by_cases hi : i ∈ Finset.range (D + 1)
    · refine ⟨l (c₀ k i), ?_⟩
      have := congrArg (fun p ↦ (p.coeff k).coeff i) hGF
      simp only [hcoeffG, if_pos hk, finsetSum_coeff, coeff_C_mul_X_pow] at this
      rw [Finset.sum_ite_eq, if_pos hi] at this
      exact this
    · refine ⟨0, ?_⟩
      rw [Rat.cast_zero, coeff_eq_zero_of_natDegree_lt]
      have := hdegk k hk
      have hi' : D + 1 ≤ i := by simpa using hi
      omega
  · refine ⟨0, ?_⟩
    have hk' : ψ < k := by simpa [Nat.lt_succ_iff] using hk
    have h0 : F.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by rw [hF₀deg]; exact hk')
    rw [h0]
    simp

end ModularFormsKB.Milne.LevelTwo
