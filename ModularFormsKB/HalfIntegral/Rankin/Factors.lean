/-
# The Gamma factors of the Rankin integral, Weil's constant, and coset representatives

- `rankinRho_mul_eq_gammaFactor`: with $s = (w-k+1)/2$ and $\lambda = k-\nu$,
  $\rho_\psi(w)\cdot L^s\pi^{-s}\Gamma(s+\tfrac\lambda2)\cdot 4\,\Gamma(\tfrac{w+\nu}2)(4\pi t)^{-(w+\nu)/2} =
  (2\pi/\sqrt{4Nr^2})^{-w}\Gamma(w)$, by Legendre's duplication formula
  $\Gamma(\tfrac w2)\Gamma(\tfrac{w+1}2) = 2^{1-w}\sqrt\pi\,\Gamma(w)$ (`Complex.Gamma_mul_Gamma_add_half`);
- `differentiable_rankinRho`, `bddVStrips_rankinRho`: $\rho_\psi$ is an entire exponential, bounded on vertical strips;
- `one_sub_rankinS_two_mul_sub`: $1 - s(2k-w) = s(w)$;
- `weilConstant_ne_zero`: Weil's constant $C_\psi$ for $\chi^2$ is nonzero for primitive $\psi$ modulo a prime $m \nmid 4N$;
- `exists_isGamma0Reps`: $\Gamma_0(L)$ has a finite list of right coset representatives, $L \ge 1$.
-/
import ModularFormsKB.HalfIntegral.Abstract.ShimuraRankin
import ModularFormsKB.HalfIntegral.WeilBridge
import ModularFormsKB.Miyake.Sec4_3.Gauss

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup
open scoped Real

private lemma cpow_ne' {x : ℂ} (hx : x ≠ 0) (y : ℂ) : x ^ y ≠ 0 :=
  fun h => hx ((Complex.cpow_eq_zero_iff _ _).1 h).1

private lemma rankinLevel_pos {N t r : ℕ} (hN : 0 < N) (ht : 1 ≤ t) (hr : 1 ≤ r) : 0 < rankinLevel N t r := by
  unfold rankinLevel; positivity

private lemma four_pi_t_pos {t : ℕ} (ht : 1 ≤ t) : (0 : ℝ) < 4 * π * t := by
  have : (1 : ℝ) ≤ t := by exact_mod_cast ht
  positivity

private lemma X_pos {N r : ℕ} (hN : 0 < N) (hr : 1 ≤ r) : (0 : ℝ) < 2 * π / Real.sqrt (4 * N * r ^ 2 : ℕ) := by
  have h : 0 < 4 * N * r ^ 2 := by positivity
  have : (0 : ℝ) < Real.sqrt ((4 * N * r ^ 2 : ℕ) : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast h)
  positivity

theorem rankinRho_mul_eq_gammaFactor (k N : ℕ) (hN : 0 < N) {t : ℕ} (ht : 1 ≤ t) {r : ℕ} (hr : 1 ≤ r)
    (ψ : DirichletCharacter ℂ r) (hν : charParity ψ ≤ 1) (hk : charParity ψ ≤ k) (w : ℂ) :
    rankinRho k N t ψ w *
        ((rankinLevel N t r : ℂ) ^ rankinS k w * (π : ℂ) ^ (-rankinS k w) *
          Gamma (rankinS k w + ((k - charParity ψ : ℕ) : ℂ) / 2) *
          (4 * Gamma ((w + charParity ψ) / 2) * (((4 * π * t : ℝ) : ℂ) ^ (-((w + charParity ψ) / 2))))) =
      gammaFactor (4 * N * r ^ 2) w := by
  have hL : (rankinLevel N t r : ℂ) ≠ 0 := by
    exact_mod_cast (rankinLevel_pos hN ht hr).ne'
  have hT : (((4 * π * t : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (four_pi_t_pos ht).ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsq : ((Real.sqrt π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hD : (4 * ((rankinLevel N t r : ℂ) ^ rankinS k w) * ((π : ℂ) ^ (-rankinS k w)) *
      (((4 * π * t : ℝ) : ℂ) ^ (-(w + charParity ψ) / 2)) * ((2 : ℂ) ^ (1 - w)) *
        ((Real.sqrt π : ℝ) : ℂ)) ≠ 0 := by
    have h1 := cpow_ne' hL (rankinS k w)
    have h2 := cpow_ne' hπ (-rankinS k w)
    have h3 := cpow_ne' hT (-(w + charParity ψ) / 2)
    have h4 := cpow_ne' (two_ne_zero : (2 : ℂ) ≠ 0) (1 - w)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h1) h2) h3) h4) hsq
  have key : Gamma (rankinS k w + ((k - charParity ψ : ℕ) : ℂ) / 2) * Gamma ((w + charParity ψ) / 2) =
      Gamma w * (2 : ℂ) ^ (1 - w) * ((Real.sqrt π : ℝ) : ℂ) := by
    have hd := Complex.Gamma_mul_Gamma_add_half (w / 2)
    have e2 : 2 * (w / 2) = w := by ring
    rw [e2] at hd
    have hcast : ((k - charParity ψ : ℕ) : ℂ) = k - (charParity ψ : ℂ) := by
      rw [Nat.cast_sub hk]
    rw [hcast]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hν with h | h
    · rw [h]
      have e3 : rankinS k w + ((k : ℂ) - ((0 : ℕ) : ℂ)) / 2 = w / 2 + 1 / 2 := by
        unfold rankinS; push_cast; ring
      rw [e3]
      have e4 : (w + ((0 : ℕ) : ℂ)) / 2 = w / 2 := by push_cast; ring
      rw [e4, mul_comm, hd]
    · rw [h]
      have e3 : rankinS k w + ((k : ℂ) - ((1 : ℕ) : ℂ)) / 2 = w / 2 := by
        unfold rankinS; push_cast; ring
      rw [e3]
      have e4 : (w + ((1 : ℕ) : ℂ)) / 2 = w / 2 + 1 / 2 := by push_cast; ring
      rw [e4, hd]
  unfold rankinRho gammaFactor
  rw [div_mul_eq_mul_div, div_eq_iff hD]
  have e : -(w + (charParity ψ : ℂ)) / 2 = -((w + charParity ψ) / 2) := by ring
  rw [e]
  linear_combination
    (((2 * π / Real.sqrt (4 * N * r ^ 2 : ℕ) : ℝ) : ℂ) ^ (-w) * (rankinLevel N t r : ℂ) ^ rankinS k w *
      (π : ℂ) ^ (-rankinS k w) * 4 * (((4 * π * t : ℝ) : ℂ) ^ (-((w + charParity ψ) / 2)))) * key

private lemma cpow_aff_diff {c : ℂ} (hc : c ≠ 0) (a b : ℂ) :
    Differentiable ℂ (fun w : ℂ => c ^ (a * w + b)) :=
  fun w => DifferentiableAt.const_cpow (by fun_prop) (Or.inl hc)

/-- (Positivity hypotheses `hN`, `ht`, `hr` added: for `N = 0` or `t = 0` or `r = 0` some base is `0` and the
function is not differentiable.) -/
theorem differentiable_rankinRho (k N t : ℕ) (hN : 0 < N) (ht : 1 ≤ t) {r : ℕ} (hr : 1 ≤ r)
    (ψ : DirichletCharacter ℂ r) :
    Differentiable ℂ (rankinRho k N t ψ) := by
  have hL : (rankinLevel N t r : ℂ) ≠ 0 := by
    exact_mod_cast (rankinLevel_pos hN ht hr).ne'
  have hT : (((4 * π * t : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (four_pi_t_pos ht).ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hX : (((2 * π / Real.sqrt (4 * N * r ^ 2 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (X_pos hN hr).ne'
  have hsq : ((Real.sqrt π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  have d1 := cpow_aff_diff hX (-1) 0
  have d2 := cpow_aff_diff hL (1/2) ((-(k : ℂ) + 1) / 2)
  have d3 := cpow_aff_diff hπ (-1/2) (-((-(k : ℂ) + 1) / 2))
  have d4 := cpow_aff_diff hT (-1/2) (-(charParity ψ : ℂ) / 2)
  have d5 := cpow_aff_diff (two_ne_zero : (2 : ℂ) ≠ 0) (-1) 1
  have f1 : Differentiable ℂ (fun w : ℂ => (((2 * π / Real.sqrt (4 * N * r ^ 2 : ℕ) : ℝ) : ℂ)) ^ (-w)) := by
    simpa using d1
  have f2 : Differentiable ℂ (fun w : ℂ => (rankinLevel N t r : ℂ) ^ rankinS k w) := by
    have e : (fun w : ℂ => (rankinLevel N t r : ℂ) ^ rankinS k w) =
        fun w : ℂ => (rankinLevel N t r : ℂ) ^ ((1 / 2 : ℂ) * w + (-(k : ℂ) + 1) / 2) := by
      funext w; unfold rankinS; exact congrArg _ (by ring)
    rw [e]; exact d2
  have f3 : Differentiable ℂ (fun w : ℂ => (π : ℂ) ^ (-rankinS k w)) := by
    have e : (fun w : ℂ => (π : ℂ) ^ (-rankinS k w)) =
        fun w : ℂ => (π : ℂ) ^ ((-1 / 2 : ℂ) * w + -((-(k : ℂ) + 1) / 2)) := by
      funext w; unfold rankinS; exact congrArg _ (by ring)
    rw [e]; exact d3
  have f4 : Differentiable ℂ (fun w : ℂ => (((4 * π * t : ℝ) : ℂ)) ^ (-(w + charParity ψ) / 2)) := by
    have e : (fun w : ℂ => (((4 * π * t : ℝ) : ℂ)) ^ (-(w + charParity ψ) / 2)) =
        fun w : ℂ => (((4 * π * t : ℝ) : ℂ)) ^ ((-1 / 2 : ℂ) * w + (-(charParity ψ : ℂ) / 2)) := by
      funext w; exact congrArg _ (by ring)
    rw [e]; exact d4
  have f5 : Differentiable ℂ (fun w : ℂ => (2 : ℂ) ^ (1 - w)) := by
    have e : (fun w : ℂ => (2 : ℂ) ^ (1 - w)) = fun w : ℂ => (2 : ℂ) ^ ((-1 : ℂ) * w + 1) := by
      funext w; exact congrArg _ (by ring)
    rw [e]; exact d5
  have c4 : Differentiable ℂ (fun _ : ℂ => (4 : ℂ)) := differentiable_const _
  have c6 : Differentiable ℂ (fun _ : ℂ => ((Real.sqrt π : ℝ) : ℂ)) := differentiable_const _
  have hden : Differentiable ℂ (fun w : ℂ =>
      4 * ((rankinLevel N t r : ℂ) ^ rankinS k w) * ((π : ℂ) ^ (-rankinS k w)) *
        (((4 * π * t : ℝ) : ℂ) ^ (-(w + charParity ψ) / 2)) * ((2 : ℂ) ^ (1 - w)) *
          ((Real.sqrt π : ℝ) : ℂ)) :=
    (((((c4.mul f2).mul f3).mul f4).mul f5).mul c6)
  have hne : ∀ w : ℂ,
      4 * ((rankinLevel N t r : ℂ) ^ rankinS k w) * ((π : ℂ) ^ (-rankinS k w)) *
        (((4 * π * t : ℝ) : ℂ) ^ (-(w + charParity ψ) / 2)) * ((2 : ℂ) ^ (1 - w)) *
          ((Real.sqrt π : ℝ) : ℂ) ≠ 0 := by
    intro w
    have h1 := cpow_ne' hL (rankinS k w)
    have h2 := cpow_ne' hπ (-rankinS k w)
    have h3 := cpow_ne' hT (-(w + charParity ψ) / 2)
    have h4 := cpow_ne' (two_ne_zero : (2 : ℂ) ≠ 0) (1 - w)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h1) h2) h3) h4) hsq
  have := Differentiable.div f1 hden hne
  unfold rankinRho
  exact this

/-- Real-cast form of `rankinRho`. -/
private lemma rankinRho_eq (k N t : ℕ) {r : ℕ} (ψ : DirichletCharacter ℂ r) (w : ℂ) :
    rankinRho k N t ψ w =
      (((2 * π / Real.sqrt (4 * N * r ^ 2 : ℕ) : ℝ) : ℂ) ^ (-w)) /
      (4 * (((rankinLevel N t r : ℝ) : ℂ) ^ rankinS k w) * (((π : ℝ) : ℂ) ^ (-rankinS k w)) *
        (((4 * π * t : ℝ) : ℂ) ^ (-(w + charParity ψ) / 2)) * (((2 : ℝ) : ℂ) ^ (1 - w)) *
          ((Real.sqrt π : ℝ) : ℂ)) := by
  unfold rankinRho
  simp

/-- (Positivity hypotheses `hN`, `ht`, `hr` added, as for `differentiable_rankinRho`.) -/
theorem bddVStrips_rankinRho (k N t : ℕ) (hN : 0 < N) (ht : 1 ≤ t) {r : ℕ} (hr : 1 ≤ r)
    (ψ : DirichletCharacter ℂ r) :
    BddVStrips (rankinRho k N t ψ) := by
  intro σ₁ σ₂
  have hL : (0 : ℝ) < rankinLevel N t r := by exact_mod_cast rankinLevel_pos hN ht hr
  have hT := four_pi_t_pos ht
  have hX := X_pos hN hr
  have hpi := Real.pi_pos
  have hsq := Real.sqrt_pos.2 hpi
  set X : ℝ := 2 * π / Real.sqrt (4 * N * r ^ 2 : ℕ) with hXdef
  set L : ℝ := (rankinLevel N t r : ℝ) with hLdef
  set T : ℝ := 4 * π * t with hTdef
  let g : ℝ → ℝ := fun x =>
    X ^ (-x) / (4 * L ^ ((x - k + 1) / 2) * π ^ (-((x - k + 1) / 2)) * T ^ (-(x + charParity ψ) / 2) *
      2 ^ (1 - x) * Real.sqrt π)
  have hg : Continuous g := by
    have hc : ∀ c : ℝ, 0 < c → ∀ f : ℝ → ℝ, Continuous f → Continuous (fun x => c ^ f x) :=
      fun c hc f hf => Continuous.rpow continuous_const hf (fun _ => Or.inl hc.ne')
    refine Continuous.div (hc X hX _ (by fun_prop)) ?_ ?_
    · refine Continuous.mul (Continuous.mul (Continuous.mul (Continuous.mul ?_ ?_) ?_) ?_) ?_
      · exact Continuous.mul continuous_const (hc L hL _ (by fun_prop))
      · exact hc π hpi _ (by fun_prop)
      · exact hc T hT _ (by fun_prop)
      · exact hc 2 two_pos _ (by fun_prop)
      · fun_prop
    · intro x
      have h1 : 0 < L ^ ((x - k + 1) / 2) := Real.rpow_pos_of_pos hL _
      have h2 : 0 < π ^ (-((x - k + 1) / 2)) := Real.rpow_pos_of_pos hpi _
      have h3 : 0 < T ^ (-(x + charParity ψ) / 2) := Real.rpow_pos_of_pos hT _
      have h4 : (0 : ℝ) < 2 ^ (1 - x) := Real.rpow_pos_of_pos two_pos _
      exact (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) h1) h2) h3) h4) hsq).ne'
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := σ₁) (b := σ₂)).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨B, fun s h1 h2 => ?_⟩
  have hn : ‖rankinRho k N t ψ s‖ = ‖g s.re‖ := by
    rw [rankinRho_eq]
    simp only [norm_div, norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, Complex.norm_cpow_eq_rpow_re_of_pos hL,
      Complex.norm_cpow_eq_rpow_re_of_pos hpi, Complex.norm_cpow_eq_rpow_re_of_pos hT,
      Complex.norm_cpow_eq_rpow_re_of_pos two_pos]
    simp only [g, Real.norm_eq_abs, Complex.norm_real, Complex.norm_ofNat, rankinS]
    have e1 : ((s - (k : ℂ) + 1) / 2).re = (s.re - k + 1) / 2 := by simp
    have e2 : (-((s - (k : ℂ) + 1) / 2)).re = -((s.re - k + 1) / 2) := by simp
    have e3 : (-(s + (charParity ψ : ℂ)) / 2).re = -(s.re + charParity ψ) / 2 := by simp
    have e4 : (1 - s).re = 1 - s.re := by simp
    rw [e1, e2, e3, e4, Complex.neg_re, abs_of_pos hsq]
    have h5 : 0 < L ^ ((s.re - k + 1) / 2) := Real.rpow_pos_of_pos hL _
    have h6 : 0 < π ^ (-((s.re - k + 1) / 2)) := Real.rpow_pos_of_pos hpi _
    have h7 : 0 < T ^ (-(s.re + charParity ψ) / 2) := Real.rpow_pos_of_pos hT _
    have h8 : (0 : ℝ) < 2 ^ (1 - s.re) := Real.rpow_pos_of_pos two_pos _
    have h9 : 0 < X ^ (-s.re) := Real.rpow_pos_of_pos hX _
    rw [abs_of_pos (by positivity)]
  rw [hn]
  exact hB _ ⟨h1, h2⟩

theorem one_sub_rankinS_two_mul_sub (k : ℕ) (w : ℂ) : 1 - rankinS k (2 * k - w) = rankinS k w := by
  unfold rankinS; ring

private lemma mulchar_unit_ne {n : ℕ} (χ : DirichletCharacter ℂ n) {a : ZMod n} (ha : IsUnit a) :
    χ a ≠ 0 := by
  obtain ⟨u, rfl⟩ := ha
  intro h
  have := map_mul χ (u : ZMod n) ((u⁻¹ : (ZMod n)ˣ) : ZMod n)
  rw [Units.mul_inv, map_one, h, zero_mul] at this
  exact one_ne_zero this

theorem weilConstant_ne_zero {N m : ℕ} (hm : m.Prime) (hmN : m.Coprime (4 * N))
    (χ : DirichletCharacter ℂ (4 * N)) (ψ : DirichletCharacter ℂ m) (hψ : ψ.IsPrimitive) :
    weilConstant (χ ^ 2) ψ ≠ 0 := by
  have : NeZero m := ⟨hm.ne_zero⟩
  have hu1 : IsUnit (m : ZMod (4 * N)) := (ZMod.isUnit_iff_coprime m (4 * N)).2 hmN
  have hu2 : IsUnit (-((4 * N : ℕ) : ZMod m)) :=
    (((ZMod.isUnit_iff_coprime (4 * N) m).2 hmN.symm)).neg
  have h1 : (χ ^ 2) (m : ZMod (4 * N)) ≠ 0 := by
    obtain ⟨u, hu⟩ := hu1
    rw [← hu]
    exact mulchar_unit_ne (χ ^ 2) u.isUnit
  have h2 : ψ (-((4 * N : ℕ) : ZMod m)) ≠ 0 := by
    obtain ⟨u, hu⟩ := hu2
    rw [← hu]
    exact mulchar_unit_ne ψ u.isUnit
  have hψ' : (ψ⁻¹).IsPrimitive := by
    unfold DirichletCharacter.IsPrimitive at hψ ⊢
    rw [DirichletCharacter.conductor_inv]; exact hψ
  have h3 : gaussW ψ ≠ 0 := by
    rw [gaussW_eq_miyake]; exact Miyake.gaussW_ne_zero hψ
  have h4 : gaussW ψ⁻¹ ≠ 0 := by
    rw [gaussW_eq_miyake]; exact Miyake.gaussW_ne_zero hψ'
  unfold weilConstant
  exact div_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4

theorem exists_isGamma0Reps (L : ℕ) (hL : 1 ≤ L) : ∃ R : List SL(2, ℤ), IsGamma0Reps L R := by
  have : NeZero L := ⟨by omega⟩
  let H : Subgroup SL(2, ℤ) := Gamma0 L
  have : Finite (Quotient (QuotientGroup.rightRel H)) := by
    have : Finite (SL(2, ℤ) ⧸ H) := H.finiteIndex_iff_finite_quotient.1 inferInstance
    exact Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  let Q := Quotient (QuotientGroup.rightRel H)
  let n := Nat.card Q
  let e : Q ≃ Fin n := Finite.equivFin Q
  refine ⟨List.ofFn (fun i : Fin n => (e.symm i).out), fun g => ?_⟩
  have hiff : ∀ q : Q, g * (q.out)⁻¹ ∈ H ↔ q = ⟦g⟧ := by
    intro q
    rw [← QuotientGroup.rightRel_apply]
    constructor
    · intro h
      have := Quotient.sound h
      rw [Quotient.out_eq] at this
      exact this
    · intro h
      subst h
      exact Quotient.exact (Quotient.out_eq _)
  let c : Fin (List.ofFn (fun i : Fin n => (e.symm i).out)).length ≃ Fin n :=
    finCongr (List.length_ofFn)
  refine ⟨c.symm (e ⟦g⟧), ?_, ?_⟩
  · simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact (hiff _).2 ((Equiv.symm_apply_eq e).2 (Fin.ext rfl))
  · intro j hj
    have hget : ((List.ofFn fun i : Fin n => Quotient.out (e.symm i)).get j) =
        Quotient.out (e.symm (c j)) := by simp [c]; rfl
    rw [hget] at hj
    have h2 : e.symm (c j) = ⟦g⟧ := (hiff _).1 hj
    exact (Equiv.eq_symm_apply c).2 ((Equiv.symm_apply_eq e).1 h2)

end ModularFormsKB.HalfIntegral
