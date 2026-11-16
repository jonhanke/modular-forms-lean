/-
# The dual Rankin integral does not depend on the coset representatives

Loose end LE-MF-0243. The named input
`ShimuraDualUnfolding M k N χ` (`Abstract/ShimuraRankin.lean`) asks for its identity for **every** list $R$ of right
coset representatives of $\Gamma_0(16Ntr^2)$. This file proves that the dual Rankin integral `rankinDual` is the same for
all such lists, so the identity for one list per level suffices:

* `gaussAt_congr`, `gaussAt_mul`: the Gauss sum $G(\omega,m) = \sum_{a=0}^{L-1}\omega(a)e(am/L)$ depends on $m$ modulo
  $L$, and $\omega(d)\,G(\omega,md) = G(\omega,m)$ for $d$ a unit modulo $L$;
* `eisensteinDual_smul`: the law of the dual Eisenstein series on $\Gamma_0(L)$,
  $\omega(d)\,\check E(\gamma z,s) = \big(|cz+d|/(cz+d)\big)^\lambda\,\check E(z,s)$ for $\lambda \ge 1$
  (the lattice $\mathbb Z^2$ is permuted by $p \mapsto p\gamma$, and the first coordinate changes by $d$ modulo $L$);
* `rankinDualIntegrand_smul`: with the unitary law of the Rankin kernel (`unitaryLaw_rankinKernel`) the integrand
  $G_\psi\,\check E$ is $\Gamma_0(L)$-invariant;
* `rankinDual_eq_of_reps`: hence, by the coset bookkeeping `RankinUnfold.repsIntegral_eq_sum_quotient`, the dual
  Rankin integral does not depend on $R$;
* `shimuraDualUnfolding_of_someReps`: the smaller named input `ShimuraDualUnfoldingSomeReps M k N χ` (the identity for
  some list of representatives of each level) gives `ShimuraDualUnfolding M k N χ` when `ThetaTwistLaw M` holds; for the
  theta multiplier, `shimuraTheorem_theta_of_dualUnfoldingSomeReps`.

**Index shift.** Matrix entries are 0-based: $c = \gamma_{1,0}$, $d = \gamma_{1,1}$.
-/
import ModularFormsKB.HalfIntegral.Rankin.ThetaShimura

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup MeasureTheory Set
open scoped Real

local notation "ℍ" => UpperHalfPlane

namespace DualReps

/-! ### Gauss sums -/

/-- The additive character $A \mapsto e(A/L)$ on $\mathbb Z$. -/
noncomputable def eL (L : ℕ) (A : ℤ) : ℂ := cexp (2 * π * I * A / L)

lemma eL_congr {L : ℕ} (hL : 1 ≤ L) {A B : ℤ} (h : A ≡ B [ZMOD L]) : eL L A = eL L B := by
  obtain ⟨q, hq⟩ : (L : ℤ) ∣ A - B := (Int.ModEq.dvd h.symm)
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  unfold eL
  have hA : (A : ℂ) = B + L * q := by
    have : A = B + L * q := by linarith
    rw [this]; push_cast; ring
  rw [hA, show 2 * π * I * ((B : ℂ) + L * q) / L = 2 * π * I * B / L + q * (2 * π * I) by
    field_simp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The Gauss sum as a sum over `ZMod L`. -/
lemma gaussAt_eq_sum_zmod {L : ℕ} [NeZero L] (ω : DirichletCharacter ℂ L) (m : ℤ) :
    gaussAt L ω m = ∑ x : ZMod L, ω x * eL L (x.val * m) := by
  unfold gaussAt
  refine Finset.sum_nbij' (fun a ↦ (a : ZMod L)) (fun x ↦ x.val) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro x _; exact Finset.mem_range.2 (ZMod.val_lt x)
  · intro a ha
    exact ZMod.val_cast_of_lt (Finset.mem_range.1 ha)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro a ha
    rw [ZMod.val_cast_of_lt (Finset.mem_range.1 ha)]
    unfold eL
    push_cast
    ring_nf

/-- **The Gauss sum depends on $m$ modulo $L$.** -/
theorem gaussAt_congr {L : ℕ} (hL : 1 ≤ L) (ω : DirichletCharacter ℂ L) {m m' : ℤ} (h : m ≡ m' [ZMOD L]) :
    gaussAt L ω m = gaussAt L ω m' := by
  have : NeZero L := ⟨by omega⟩
  rw [gaussAt_eq_sum_zmod, gaussAt_eq_sum_zmod]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [eL_congr hL (Int.ModEq.mul_left _ h)]

/-- **The Gauss sum under a unit:** $\omega(d)\,G(\omega,md) = G(\omega,m)$ for $d$ a unit modulo $L$. -/
theorem gaussAt_mul {L : ℕ} (hL : 1 ≤ L) (ω : DirichletCharacter ℂ L) (m d : ℤ) (hd : IsUnit (d : ZMod L)) :
    ω (d : ZMod L) * gaussAt L ω (m * d) = gaussAt L ω m := by
  have : NeZero L := ⟨by omega⟩
  obtain ⟨u, hu⟩ := hd
  rw [gaussAt_eq_sum_zmod, gaussAt_eq_sum_zmod, Finset.mul_sum]
  -- substitute `y = x * d`
  refine Finset.sum_bij' (fun x _ ↦ x * (u : ZMod L)) (fun y _ ↦ y * ((u⁻¹ : (ZMod L)ˣ) : ZMod L))
    (fun _ _ ↦ Finset.mem_univ _) (fun _ _ ↦ Finset.mem_univ _) ?_ ?_ ?_
  · intro x _; simp [mul_assoc]
  · intro y _; simp [mul_assoc]
  · intro x _
    have hω : ω (x * (u : ZMod L)) = ω (d : ZMod L) * ω x := by rw [map_mul, hu, mul_comm]
    have hc : ((x * (u : ZMod L)).val : ℤ) * m ≡ (x.val : ℤ) * (m * d) [ZMOD L] := by
      apply (ZMod.intCast_eq_intCast_iff _ _ L).1
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hu]
      ring
    rw [hω, eL_congr hL hc]
    ring

/-! ### The law of the dual Eisenstein series on `Γ₀(L)` -/

/-- $\mathbb Z^2 \to \mathbb Z^2$, $p \mapsto p\gamma$ (row vector times matrix), a bijection. -/
def rowAct (γ : SL(2, ℤ)) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1 * γ 0 0 + p.2 * γ 1 0, p.1 * γ 0 1 + p.2 * γ 1 1)
  invFun q := (q.1 * γ 1 1 - q.2 * γ 1 0, -(q.1 * γ 0 1) + q.2 * γ 0 0)
  left_inv p := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    refine Prod.ext ?_ ?_ <;> simp only
    · linear_combination (p.1 : ℤ) * h
    · linear_combination (p.2 : ℤ) * h
  right_inv q := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    refine Prod.ext ?_ ?_ <;> simp only
    · linear_combination (q.1 : ℤ) * h
    · linear_combination (q.2 : ℤ) * h

lemma rowAct_apply (γ : SL(2, ℤ)) (p : ℤ × ℤ) :
    rowAct γ p = (p.1 * γ 0 0 + p.2 * γ 1 0, p.1 * γ 0 1 + p.2 * γ 1 1) := rfl

/-- **The summand under division:** for $j \ne 0$ and $\lambda \ge 1$,
$\mathrm{eisTerm}(w/j) = (|j|^\lambda/j^\lambda)\,(|j|^s)^2\,\mathrm{eisTerm}(w)$. -/
lemma eisTerm_div {lam : ℕ} (hlam : 1 ≤ lam) (s : ℂ) (w : ℂ) {j : ℂ} (hj : j ≠ 0) :
    eisTerm lam s (w / j) = ((‖j‖ : ℂ) ^ lam / j ^ lam) * ((‖j‖ : ℂ) ^ s) ^ 2 * eisTerm lam s w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [eisTerm, zero_pow (show lam ≠ 0 by omega)]
  have hb : 0 < ‖j‖ := norm_pos_iff.2 hj
  have ha : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hb' : ((‖j‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have harg : ((‖j‖ : ℝ) : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hb.le]; exact Real.pi_ne_zero.symm
  unfold eisTerm
  rw [norm_div, div_eq_mul_inv ‖w‖, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha.le (by positivity),
    Complex.ofReal_inv, Complex.inv_cpow _ _ harg,
    show (-(lam : ℂ) - 2 * s) = -(lam : ℂ) + -(2 * s) by ring, Complex.cpow_add _ _ hb',
    Complex.cpow_neg, Complex.cpow_neg, Complex.cpow_natCast, show (2 : ℂ) * s = ((2 : ℕ) : ℂ) * s by simp,
    Complex.cpow_nat_mul, div_pow]
  have hs : ((‖j‖ : ℝ) : ℂ) ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hjl : j ^ lam ≠ 0 := pow_ne_zero _ hj
  have hbl : ((‖j‖ : ℝ) : ℂ) ^ lam ≠ 0 := pow_ne_zero _ hb'
  field_simp

/-- $d$ is a unit modulo $L$ for $\gamma \in \Gamma_0(L)$. -/
lemma isUnit_d {L : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 L) : IsUnit ((γ 1 1 : ℤ) : ZMod L) := by
  have h := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at h
  have hc : ((γ 1 0 : ℤ) : ZMod L) = 0 := Gamma0_mem.mp hγ
  refine isUnit_iff_exists_inv.2 ⟨((γ 0 0 : ℤ) : ZMod L), ?_⟩
  have := congrArg (fun x : ℤ ↦ (x : ZMod L)) h
  push_cast at this
  rw [hc] at this
  linear_combination this

/-- The first coordinate of $p\gamma$ times $d$ is $p_1$ modulo $L$, for $\gamma \in \Gamma_0(L)$. -/
lemma rowAct_fst_mul {L : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 L) (p : ℤ × ℤ) :
    -(rowAct γ p).1 * γ 1 1 ≡ -p.1 [ZMOD L] := by
  have h := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at h
  obtain ⟨q, hq⟩ := RankinUnfold.dvd_of_mem_Gamma0 hγ
  apply Int.modEq_iff_dvd.2
  refine ⟨q * (p.1 * γ 0 1 + p.2 * γ 1 1), ?_⟩
  rw [rowAct_apply]
  linear_combination (p.1 : ℤ) * h + (p.1 * γ 0 1 + p.2 * γ 1 1) * hq

/-- **The law of the dual Eisenstein series on $\Gamma_0(L)$:** for $L, \lambda \ge 1$ and $\gamma \in \Gamma_0(L)$,
$\omega(d)\,\check E(\gamma z,s) = \big(|cz+d|/(cz+d)\big)^\lambda\,\check E(z,s)$. -/
theorem eisensteinDual_smul {L lam : ℕ} (hL : 1 ≤ L) (hlam : 1 ≤ lam) (ω : DirichletCharacter ℂ L)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 L) (τ : ℍ) (s : ℂ) :
    ω (γ 1 1 : ZMod L) * eisensteinDual L lam ω (γ • τ) s =
      ((‖(γ 1 0 : ℂ) * τ + γ 1 1‖ : ℂ) / ((γ 1 0 : ℂ) * τ + γ 1 1)) ^ lam * eisensteinDual L lam ω τ s := by
  set j : ℂ := (γ 1 0 : ℂ) * τ + γ 1 1 with hjdef
  have hj : j ≠ 0 := by rw [hjdef, ← denom_SL_eq]; exact UpperHalfPlane.denom_ne_zero _ τ
  have hr : 0 < ‖j‖ := norm_pos_iff.mpr hj
  have hy := τ.im_pos
  -- the imaginary part
  have him : (γ • τ).im = τ.im / ‖j‖ ^ 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq, denom_SL_eq]
  have e1 : (((γ • τ).im : ℝ) : ℂ) ^ s = ((τ.im : ℂ) ^ s) * (((‖j‖ : ℂ) ^ s) ^ 2)⁻¹ := by
    rw [him, div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hy.le (by positivity)]
    congr 1
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_ne_zero.symm)]
    congr 1
    rw [Complex.ofReal_pow, sq, sq, Complex.mul_cpow_ofReal_nonneg hr.le hr.le]
  -- the point
  have hpt : ∀ p : ℤ × ℤ, (p.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + p.2 =
      (((rowAct γ p).1 : ℂ) * τ + (rowAct γ p).2) / j := by
    intro p
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    rw [rowAct_apply]
    simp only [algebraMap_int_eq, eq_intCast, Int.cast_add, Int.cast_mul]
    have hj' : (((γ 1 0 : ℤ) : ℝ) : ℂ) * τ + (((γ 1 1 : ℤ) : ℝ) : ℂ) = j := by rw [hjdef]; push_cast; ring
    rw [hj']
    field_simp
    push_cast
    ring
  -- the summand
  have hterm : ∀ p : ℤ × ℤ, ω (γ 1 1 : ZMod L) * (gaussAt L ω (-p.1) * eisTerm lam s ((p.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + p.2)) =
      ((‖j‖ : ℂ) ^ lam / j ^ lam) * ((‖j‖ : ℂ) ^ s) ^ 2 *
        (gaussAt L ω (-(rowAct γ p).1) * eisTerm lam s (((rowAct γ p).1 : ℂ) * τ + (rowAct γ p).2)) := by
    intro p
    rw [hpt p, eisTerm_div hlam s _ hj]
    have hG : gaussAt L ω (-p.1) = gaussAt L ω (-(rowAct γ p).1 * γ 1 1) :=
      gaussAt_congr hL ω (rowAct_fst_mul hγ p).symm
    have hG2 := gaussAt_mul hL ω (-(rowAct γ p).1) (γ 1 1) (isUnit_d hγ)
    rw [hG, ← hG2]
    ring
  unfold eisensteinDual
  rw [e1, mul_left_comm, ← tsum_mul_left]
  simp_rw [hterm]
  rw [tsum_mul_left, (rowAct γ).tsum_eq (fun q ↦ gaussAt L ω (-q.1) * eisTerm lam s ((q.1 : ℂ) * τ + q.2))]
  have hr' : ((‖j‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hs : ((‖j‖ : ℝ) : ℂ) ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h ↦ hr' h.1
  have hjl : j ^ lam ≠ 0 := pow_ne_zero _ hj
  rw [div_pow]
  generalize ((‖j‖ : ℝ) : ℂ) ^ s = X at hs ⊢
  generalize ((‖j‖ : ℝ) : ℂ) ^ lam = Y
  generalize (τ.im : ℂ) ^ s = Z
  field_simp
  congr 1
  refine tsum_congr fun p ↦ ?_
  rw [mul_comm (τ : ℂ)]

/-! ### The invariance of the dual integrand and the independence of the representatives -/

/-- **The dual Rankin integrand is $\Gamma_0(16Ntr^2)$-invariant**, for $r = 1$ or an odd prime and $\nu < k$:
the unitary law of the kernel (`unitaryLaw_rankinKernel`) and the law of $\check E$ (`eisensteinDual_smul`) cancel. -/
theorem rankinDualIntegrand_smul (M : MultiplierSystem) (hT : ThetaTwistLaw M) {k N : ℕ} (hN : 0 < N)
    {χ : DirichletCharacter ℂ (4 * N)} {f : ℍ → ℂ} (hf : M.Transforms k N χ f) {t : ℕ} (ht : 1 ≤ t) {r : ℕ}
    (hr : r = 1 ∨ (r.Prime ∧ r ≠ 2)) (ψ : DirichletCharacter ℂ r) (hk : charParity ψ < k) (s : ℂ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (rankinLevel N t r)) (τ : ℍ) :
    rankinKernel k ψ t f (γ • τ) *
        eisensteinDual (rankinLevel N t r) (k - charParity ψ) (rankinChar k N χ t ψ) (γ • τ) s =
      rankinKernel k ψ t f τ *
        eisensteinDual (rankinLevel N t r) (k - charParity ψ) (rankinChar k N χ t ψ) τ s := by
  have hr1 : 1 ≤ r := by
    rcases hr with rfl | ⟨hp, -⟩
    · exact le_rfl
    · exact hp.one_lt.le
  have hL : 1 ≤ rankinLevel N t r := by
    unfold rankinLevel
    have : 1 ≤ N * t * r ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  have hlaw := unitaryLaw_rankinKernel M hT hf ht hr ψ hk.le γ hγ τ
  have hE := eisensteinDual_smul hL (show 1 ≤ k - charParity ψ by omega) (rankinChar k N χ t ψ) hγ τ s
  set j : ℂ := (γ 1 0 : ℂ) * τ + γ 1 1 with hjdef
  have hj : j ≠ 0 := by rw [hjdef, ← denom_SL_eq]; exact UpperHalfPlane.denom_ne_zero _ τ
  have hr' : ((‖j‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hj).ne'
  have hph : (j / (‖j‖ : ℂ)) ^ (k - charParity ψ) * ((‖j‖ : ℂ) / j) ^ (k - charParity ψ) = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm j, div_self (mul_ne_zero hr' hj), one_pow]
  rw [hlaw]
  linear_combination (rankinKernel k ψ t f τ) * ((j / (‖j‖ : ℂ)) ^ (k - charParity ψ)) * hE +
    rankinKernel k ψ t f τ * eisensteinDual (rankinLevel N t r) (k - charParity ψ) (rankinChar k N χ t ψ) τ s * hph

/-- **The dual Rankin integral does not depend on the coset representatives** (for $r = 1$ or an odd prime and
$\nu < k$): both sums are the sum over $\mathrm{SL}_2(\mathbb Z)/\Gamma_0(L)$ of
`RankinUnfold.repsIntegral_eq_sum_quotient`. -/
theorem rankinDual_eq_of_reps (M : MultiplierSystem) (hT : ThetaTwistLaw M) {k N : ℕ} (hN : 0 < N)
    {χ : DirichletCharacter ℂ (4 * N)} {f : ℍ → ℂ} (hf : M.Transforms k N χ f) {t : ℕ} (ht : 1 ≤ t) {r : ℕ}
    (hr : r = 1 ∨ (r.Prime ∧ r ≠ 2)) (ψ : DirichletCharacter ℂ r) (hk : charParity ψ < k) {R R' : List SL(2, ℤ)}
    (hR : IsGamma0Reps (rankinLevel N t r) R) (hR' : IsGamma0Reps (rankinLevel N t r) R') (s : ℂ) :
    rankinDual k N χ t ψ f R s = rankinDual k N χ t ψ f R' s := by
  have hr1 : 1 ≤ r := by
    rcases hr with rfl | ⟨hp, -⟩
    · exact le_rfl
    · exact hp.one_lt.le
  have : NeZero (rankinLevel N t r) := ⟨by unfold rankinLevel; positivity⟩
  unfold rankinDual
  have hinv := fun γ hγ τ ↦ rankinDualIntegrand_smul M hT hN hf ht hr ψ hk s (γ := γ) hγ τ
  rw [RankinUnfold.repsIntegral_eq_sum_quotient hR _ hinv, RankinUnfold.repsIntegral_eq_sum_quotient hR' _ hinv]

end DualReps

/-! ### The smaller named input and the reduction -/

/-- **Shimura's dual unfolding identity for one list of representatives per level** (Shimura 1973 `shimura1973`,
proof of the Main Theorem [unverified]). The statement of `ShimuraDualUnfolding M k N χ` with "for every list $R$ of
right coset representatives of $\Gamma_0(16Ntm^2)$" weakened to "for some list": for $k \ge 2$, squarefree $t \ge 1$ and
$f \in S_{k+1/2}(4N,\chi)$ with $q$-expansion $a$ there is $b$ of polynomial growth, $b(0) = 0$, such that for $\psi = 1$
and for every primitive $\psi$ modulo an odd prime $m \nmid 4N$ there is a list $R$ of representatives with
$$\text{(`rankinDualFactor`)}\cdot\check{\mathcal R}_\psi\big(\tfrac{w-k+1}2\big) =
  i^{2k}C_\psi\,(2\pi/\sqrt{4Nm^2})^{-w}\Gamma(w)\sum_n\bar\psi(n)b(n)n^{-w}$$
for $\operatorname{Re}w$ large. By `rankinDual_eq_of_reps` the choice of $R$ does not matter
(`shimuraDualUnfolding_of_someReps`). -/
@[kb "shimura1973" "proof of the Main Theorem: the dual side of the Rankin integral, for one list of coset representatives [unverified]"]
structure ShimuraDualUnfoldingSomeReps (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop where
  dual : 2 ≤ k → ∀ t : ℕ, 1 ≤ t → Squarefree t → ∀ f ∈ M.cuspForms k N χ, ∀ a : ℕ → ℂ, Abstract.HasQExp f a →
    ∃ b : ℕ → ℂ, CoeffGrowth b ∧ b 0 = 0 ∧
      (∃ R : List SL(2, ℤ), IsGamma0Reps (rankinLevel N t 1) R ∧ ∃ σ : ℝ, ∀ w : ℂ, σ < w.re →
        rankinDualFactor k N t (1 : DirichletCharacter ℂ 1) w *
            rankinDual k N χ t (1 : DirichletCharacter ℂ 1) f R (rankinS k w) =
          I ^ (2 * k) * (gammaFactor (4 * N) w * LSeries b w)) ∧
      ∀ m : ℕ, m.Prime → m ≠ 2 → m.Coprime (4 * N) → ∀ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive →
        ∃ R : List SL(2, ℤ), IsGamma0Reps (rankinLevel N t m) R ∧ ∃ σ : ℝ, ∀ w : ℂ, σ < w.re →
          rankinDualFactor k N t ψ w * rankinDual k N χ t ψ f R (rankinS k w) =
            I ^ (2 * k) * weilConstant (χ ^ 2) ψ * (gammaFactor (4 * N * m ^ 2) w * LSeries (twist ψ⁻¹ b) w)

/-- **The reduction:** for $N \ge 1$ and a multiplier with `ThetaTwistLaw M`, the identity for one list of
representatives per level gives it for all lists. -/
theorem shimuraDualUnfolding_of_someReps (M : MultiplierSystem) (hT : ThetaTwistLaw M) (k N : ℕ)
    (χ : DirichletCharacter ℂ (4 * N)) (hN : 0 < N) (hD : ShimuraDualUnfoldingSomeReps M k N χ) :
    ShimuraDualUnfolding M k N χ := by
  refine ⟨fun hk t ht hsq f hf a ha ↦ ?_⟩
  have hfT : M.Transforms k N χ f := (show M.IsCuspForm k N χ f from hf).transforms
  obtain ⟨b, hb, hb0, ⟨R₀, hR₀, σ₁, h₁⟩, h₂⟩ := hD.dual hk t ht hsq f hf a ha
  refine ⟨b, hb, hb0, fun R hR ↦ ⟨σ₁, fun w hw ↦ ?_⟩, fun m hm hm2 hmN ψ hψ R hR ↦ ?_⟩
  · have hν : charParity (1 : DirichletCharacter ℂ 1) < k := by
      have := charParity_le_one (1 : DirichletCharacter ℂ 1); omega
    rw [DualReps.rankinDual_eq_of_reps M hT hN hfT ht (Or.inl rfl) 1 hν hR hR₀]
    exact h₁ w hw
  · obtain ⟨R₀, hR₀, σ₂, h₂'⟩ := h₂ m hm hm2 hmN ψ hψ
    refine ⟨σ₂, fun w hw ↦ ?_⟩
    have hν : charParity ψ < k := by have := charParity_le_one ψ; omega
    rw [DualReps.rankinDual_eq_of_reps M hT hN hfT ht (Or.inr ⟨hm, hm2⟩) ψ hν hR hR₀]
    exact h₂' w hw

/-- **Shimura's theorem for the theta multiplier, conditional on the dual unfolding for one list of representatives
per level** (Shimura 1973 `shimura1973`, Main Theorem): `shimuraTheorem_theta_of_dualUnfolding` with the smaller
input `ShimuraDualUnfoldingSomeReps thetaMultiplierSystem k N χ`. -/
@[kb "shimura1973" "Main Theorem for the theta multiplier, conditional on the dual unfolding for one list of representatives [unverified]"]
theorem shimuraTheorem_theta_of_dualUnfoldingSomeReps (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (hN : 0 < N)
    (hD : ShimuraDualUnfoldingSomeReps thetaMultiplierSystem k N χ) :
    ShimuraTheorem thetaMultiplierSystem k N χ :=
  shimuraTheorem_theta_of_dualUnfolding k N χ hN
    (shimuraDualUnfolding_of_someReps thetaMultiplierSystem thetaTwistLaw_thetaMultiplierSystem k N χ hN hD)

end ModularFormsKB.HalfIntegral
