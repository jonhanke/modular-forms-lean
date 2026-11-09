import ModularFormsKB.Milne.Ch6.JGrowth
import ModularFormsKB.Milne.Ch6.PolynomialInJ
import Mathlib.GroupTheory.Coset.Card

/-!
# The coset product $\prod_{\Gamma_0(N)\gamma} (Y - j(N\gamma z))$

Milne, Section 6, proof of Theorem 6.1 (pdf p. 88). For the right cosets $c = \Gamma_0(N)\gamma$ of $\Gamma_0(N)$ in
$\Gamma(1) = \mathrm{SL}_2(\mathbb Z)$, the value $j(N\gamma z)$ depends only on $c$ (`cosetVal`), and
$$\Phi_z(Y) = \prod_c \bigl(Y - j(N\gamma_c z)\bigr) \in \mathbb C[Y]$$
satisfies $\Phi_{\gamma z} = \Phi_z$ (right multiplication by $\gamma$ permutes the cosets). Its coefficients are
holomorphic on $\mathbb H$, invariant under $\mathrm{SL}_2(\mathbb Z)$ and have a pole of order at most $N\psi$ at
$i\infty$, so they are polynomials in $j$ (`ModularFormsKB.Milne.LevelTwo.exists_polynomial_of_invariant`). Hence
(`exists_coset_polynomial`) there is a monic $F \in \mathbb C[X][Y]$ of degree $\psi = (\Gamma(1) : \Gamma_0(N))$ with
$F(j(z), Y) = \Phi_z(Y)$; in particular $F(j(z), j(Nz)) = 0$.
-/

open UpperHalfPlane CongruenceSubgroup Matrix Filter Topology Polynomial
open scoped MatrixGroups Manifold

noncomputable section

namespace ModularFormsKB.Milne.LevelTwo

open TauCeti.ModularForm

/-! ### Coefficients of $\prod_i (X - a_i)$ -/

section ProdCoeff

variable {ι : Type*}

/-- Coefficients of $\prod_{i \in s}(X - f_i(z))$ are holomorphic if the $f_i$ are. -/
theorem mdiff_coeff_prod_X_sub_C (s : Finset ι) (f : ι → ℍ → ℂ) (hf : ∀ i ∈ s, MDiff (f i)) (k : ℕ) :
    MDiff (fun z : ℍ ↦ ((∏ i ∈ s, (X - C (f i z) : ℂ[X])).coeff k : ℂ)) := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, coeff_one]
    split_ifs
    · exact mdifferentiable_const
    · exact mdifferentiable_const
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, MDiff (f j) := fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)
    have hfi : MDiff (f i) := hf i (Finset.mem_insert_self _ _)
    have key : ∀ z : ℍ, ((∏ i ∈ insert i s, (X - C (f i z) : ℂ[X])).coeff k) =
        (match k with
          | 0 => 0
          | k + 1 => (∏ i ∈ s, (X - C (f i z) : ℂ[X])).coeff k) -
          f i z * (∏ i ∈ s, (X - C (f i z) : ℂ[X])).coeff k := by
      intro z
      rw [Finset.prod_insert hi, sub_mul, coeff_sub, coeff_C_mul]
      cases k with
      | zero => simp
      | succ k => simp [coeff_X_mul]
    simp_rw [key]
    cases k with
    | zero => exact (mdifferentiable_const).sub (hfi.mul (ih hs 0))
    | succ k => exact (ih hs k).sub (hfi.mul (ih hs (k + 1)))

/-- If $|a_i| \le B$ with $B \ge 1$, the coefficients of $\prod_{i \in s}(X - a_i)$ are at most $(2B)^{|s|}$. -/
theorem norm_coeff_prod_X_sub_C_le (s : Finset ι) (a : ι → ℂ) (B : ℝ) (hB : 1 ≤ B)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ B) (k : ℕ) :
    ‖(∏ i ∈ s, (X - C (a i))).coeff k‖ ≤ (2 * B) ^ s.card := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, coeff_one, Finset.card_empty, pow_zero]
    split_ifs <;> simp
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, ‖a j‖ ≤ B := fun j hj ↦ ha j (Finset.mem_insert_of_mem hj)
    have hai := ha i (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, sub_mul, coeff_sub, coeff_C_mul]
    have h1 : ‖(X * ∏ i ∈ s, (X - C (a i))).coeff k‖ ≤ (2 * B) ^ s.card := by
      cases k with
      | zero => rw [coeff_X_mul_zero, norm_zero]; exact pow_nonneg (by linarith) _
      | succ k => rw [coeff_X_mul]; exact ih hs k
    have h2 : ‖a i * (∏ i ∈ s, (X - C (a i))).coeff k‖ ≤ B * (2 * B) ^ s.card := by
      rw [norm_mul]
      exact mul_le_mul hai (ih hs k) (norm_nonneg _) (by linarith)
    have hp : 0 ≤ (2 * B) ^ s.card := pow_nonneg (by linarith) _
    generalize (X * ∏ i ∈ s, (X - C (a i))).coeff k = u at h1 ⊢
    generalize a i * (∏ i ∈ s, (X - C (a i))).coeff k = v at h2 ⊢
    have h3 : (2 * B) ^ (s.card + 1) = (2 * B) ^ s.card * (2 * B) := pow_succ _ _
    have := norm_sub_le u v
    nlinarith [mul_nonneg hp (sub_nonneg.2 hB)]

end ProdCoeff

/-! ### Cosets and their values -/

variable {N : ℕ} (hN : 0 < N)

/-- The right cosets $\Gamma_0(N)\backslash\mathrm{SL}_2(\mathbb Z)$. -/
abbrev Cosets (N : ℕ) : Type := Quotient (QuotientGroup.rightRel (Gamma0 N))

instance (N : ℕ) [NeZero N] : Finite (Cosets N) :=
  Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel _).symm

instance (N : ℕ) [NeZero N] : Fintype (Cosets N) := Fintype.ofFinite _

theorem card_cosets (N : ℕ) [NeZero N] : Fintype.card (Cosets N) = (Gamma0 N).index := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _),
    Subgroup.index]

/-- $j_N(z) = j(Nz)$. -/
def jN (z : ℍ) : ℂ := j (scaleH N hN z)

/-- The value $j(N\gamma z)$ on the coset $\Gamma_0(N)\gamma$. -/
def cosetVal (c : Cosets N) (z : ℍ) : ℂ :=
  Quotient.lift (fun γ : SL(2, ℤ) ↦ jN hN (γ • z)) (fun a b hab ↦ by
    have hab : QuotientGroup.rightRel _ a b := hab
    rw [QuotientGroup.rightRel_apply] at hab
    have := j_scale_smul hN _ hab (a • z)
    simp only [jN]
    rw [← this, ← mul_smul, inv_mul_cancel_right]) c

@[simp] theorem cosetVal_mk (γ : SL(2, ℤ)) (z : ℍ) :
    cosetVal hN (Quotient.mk _ γ) z = jN hN (γ • z) := rfl

/-- Right multiplication by $\gamma$ on the cosets. -/
def cosetMul (γ : SL(2, ℤ)) : Cosets N ≃ Cosets N where
  toFun := Quotient.map (· * γ) (fun a b hab ↦ by
    have hab : QuotientGroup.rightRel _ a b := hab
    show QuotientGroup.rightRel _ _ _
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa [mul_assoc] using hab)
  invFun := Quotient.map (· * γ⁻¹) (fun a b hab ↦ by
    have hab : QuotientGroup.rightRel _ a b := hab
    show QuotientGroup.rightRel _ _ _
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa [mul_assoc] using hab)
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h a => simp [Quotient.map_mk, mul_assoc]
  right_inv c := by
    induction c using Quotient.inductionOn with
    | h a => simp [Quotient.map_mk, mul_assoc]

theorem cosetVal_cosetMul (γ : SL(2, ℤ)) (c : Cosets N) (z : ℍ) :
    cosetVal hN (cosetMul γ c) z = cosetVal hN c (γ • z) := by
  induction c using Quotient.inductionOn with
  | h a => simp [cosetMul, Quotient.map_mk, mul_smul]

theorem mdiff_jN_smul (γ : SL(2, ℤ)) : MDiff (fun z : ℍ ↦ jN hN (γ • z)) := by
  have h1 : MDiff (fun z : ℍ ↦ j (scaleH N hN z)) :=
    mdiff_j_comp (N : ℝ) 0 1 (by exact_mod_cast hN) one_pos (fun τ ↦ by
      simp [scaleH])
  exact h1.comp (mdifferentiable_smul (g := (γ : GL (Fin 2) ℝ)) (by simp))

theorem mdiff_cosetVal (c : Cosets N) : MDiff (cosetVal hN c) := by
  induction c using Quotient.inductionOn with
  | h a => exact mdiff_jN_smul hN a

/-! ### The coset product -/

variable [NeZero N]

/-- $\Phi_z(Y) = \prod_c (Y - j(N\gamma_c z))$. -/
def Φ (z : ℍ) : ℂ[X] := ∏ c : Cosets N, (X - C (cosetVal hN c z))

theorem Φ_smul (γ : SL(2, ℤ)) (z : ℍ) : Φ hN (γ • z) = Φ hN z := by
  unfold Φ
  simp_rw [← cosetVal_cosetMul]
  exact Fintype.prod_equiv (cosetMul γ) _ _ (fun _ ↦ rfl)

theorem Φ_monic (z : ℍ) : (Φ hN z).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _

theorem Φ_natDegree (z : ℍ) : (Φ hN z).natDegree = (Gamma0 N).index := by
  rw [Φ, natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _]
  simp [card_cosets]

/-- $\Phi_z(j(Nz)) = 0$: the trivial coset contributes the factor $Y - j(Nz)$. -/
theorem Φ_eval_jN (z : ℍ) : (Φ hN z).eval (jN hN z) = 0 := by
  rw [Φ, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ (Quotient.mk _ 1)) (by simp)

theorem mdiff_coeff_Φ (k : ℕ) : MDiff (fun z ↦ (Φ hN z).coeff k) :=
  mdiff_coeff_prod_X_sub_C _ _ (fun c _ ↦ mdiff_cosetVal hN c) k

/-- **The coefficients of $\Phi_z$ have a pole of order at most $N\psi$ at $i\infty$.** -/
theorem bdd_coeff_Φ (k : ℕ) :
    IsBoundedAtImInfty (fun z : ℍ ↦
      Function.Periodic.qParam 1 (z : ℂ) ^ (N * (Gamma0 N).index) * (Φ hN z).coeff k) := by
  classical
  set ψ := (Gamma0 N).index with hψ
  have hex : ∀ c : Cosets N, ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im →
      ‖cosetVal hN c z‖ ≤ 2 * Real.exp (2 * Real.pi * N * z.im) := by
    intro c
    induction c using Quotient.inductionOn with
    | h a => exact norm_j_scale_smul_le hN a
  choose A hA using hex
  have hev : ∀ᶠ z : ℍ in atImInfty, ∀ c : Cosets N, A c ≤ z.im :=
    Filter.eventually_all.2 fun c ↦ (UpperHalfPlane.atImInfty_mem _).2 ⟨A c, fun z hz ↦ hz⟩
  refine Asymptotics.IsBigO.of_bound (4 ^ ψ) (hev.mono fun z hz ↦ ?_)
  have hB : 1 ≤ 2 * Real.exp (2 * Real.pi * N * z.im) := by
    have : 1 ≤ Real.exp (2 * Real.pi * N * z.im) := by
      apply Real.one_le_exp
      have := z.im_pos
      have := Real.pi_pos
      positivity
    linarith
  have hc := norm_coeff_prod_X_sub_C_le (Finset.univ : Finset (Cosets N)) (fun c ↦ cosetVal hN c z)
    _ hB (fun c _ ↦ hA c z (hz c)) k
  have hn : ‖Function.Periodic.qParam 1 (z : ℂ)‖ = Real.exp (-(2 * Real.pi * z.im)) := by
    rw [Function.Periodic.norm_qParam]; simp
  rw [Φ, Pi.one_apply, norm_one, mul_one, norm_mul, norm_pow, hn]
  simp only [Finset.card_univ, card_cosets] at hc
  have e1 : Real.exp (-(2 * Real.pi * z.im)) ^ (N * ψ) * Real.exp (2 * Real.pi * N * z.im) ^ ψ = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    have : ((N * ψ : ℕ) : ℝ) * (-(2 * Real.pi * z.im)) + (ψ : ℝ) * (2 * Real.pi * N * z.im) = 0 := by
      push_cast; ring
    rw [this, Real.exp_zero]
  have e2 : (2 * (2 * Real.exp (2 * Real.pi * N * z.im))) ^ ψ = 4 ^ ψ * Real.exp (2 * Real.pi * N * z.im) ^ ψ := by
    rw [← mul_pow]; congr 1; ring
  rw [e2] at hc
  have hq : 0 ≤ Real.exp (-(2 * Real.pi * z.im)) ^ (N * ψ) := by positivity
  calc _ ≤ Real.exp (-(2 * Real.pi * z.im)) ^ (N * ψ) * (4 ^ ψ * Real.exp (2 * Real.pi * N * z.im) ^ ψ) :=
        mul_le_mul_of_nonneg_left hc hq
    _ = 4 ^ ψ := by rw [mul_left_comm, e1, mul_one]
    _ = _ := by simp

/-- **The modular polynomial over $\mathbb C$**: a monic $F \in \mathbb C[X][Y]$ of degree $\psi$ with
$F(j(z), Y) = \Phi_z(Y)$. -/
theorem exists_coset_polynomial :
    ∃ F : ℂ[X][X], F.Monic ∧ F.natDegree = (Gamma0 N).index ∧
      ∀ z : ℍ, F.map (evalRingHom (j z)) = Φ hN z := by
  classical
  set ψ := (Gamma0 N).index with hψ
  have hex : ∀ k : Fin ψ, ∃ P : ℂ[X], P.natDegree ≤ N * ψ ∧ ∀ z : ℍ, (Φ hN z).coeff k = P.eval (j z) :=
    fun k ↦ exists_polynomial_of_invariant (N * ψ) (mdiff_coeff_Φ hN k)
      (fun γ z ↦ by rw [Φ_smul]) (bdd_coeff_Φ hN k)
  choose P _ hP using hex
  have hdeg : (∑ k : Fin ψ, C (P k) * (X : ℂ[X][X]) ^ (k : ℕ)).degree < ψ :=
    degree_sum_fin_lt P
  refine ⟨X ^ ψ + ∑ k : Fin ψ, C (P k) * X ^ (k : ℕ), monic_X_pow_add hdeg, ?_, fun z ↦ ?_⟩
  · rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  · conv_rhs => rw [(Φ_monic hN z).as_sum, Φ_natDegree, ← hψ, Finset.sum_range]
    simp [Polynomial.map_add, Polynomial.map_sum, hP]

end ModularFormsKB.Milne.LevelTwo
