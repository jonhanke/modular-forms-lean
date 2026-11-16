import ModularFormsKB.Miyake.Sec4_6.PseudoEigenvalue

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm TauCeti.ExactDivisor

/-!
# Miyake §4.6: Corollary 4.6.18 (1) for `N_q = q^e`

Prime-power generalization of `PseudoEigenvalue.lean` (loose end LE-MF-0217); `Q = q^(n+1)`,
`Q' = q^n`, `D_m = diag(m, 1)`.

## Result
* `corollary_4_6_18_one_primePow`: for a primitive form `f` of `𝒮_k^0(N, ψ φ)` with `ψ` primitive
  modulo `Q = q^e`, `f | η = c g` with `g` primitive and `c = Q⁻¹ ψ(-1) W(ψ) conj(a_Q)`.

## Proof
Take `η = γ D_Q`, `R = D_Q⁻¹ γ D_Q`, `S_a = f | [1 a/Q; 0 1]`, `Z = ∑_a ψ(a) S_a`.
1. For a unit `a`, `S_a | R = ψ(a)⁻¹ S_{-a⁻¹}` (`slash_coset'`); non-units contribute `0`, so
   `Z | R = ∑_{v unit} S_v` (`sum_slash_coset'`).
2. The non-units mod `q^(n+1)` are the multiples of `q`, so
   `∑_{v unit} S_v = ∑_v S_v - ∑_{w mod Q'} f | [1 w/Q'; 0 1]` (`sum_units_eq`).
3. Both sums are `U`-operator sums: `∑_{v mod m} S_v = m a_m f(m ·)` when `a_{m j} = a_m a_j`
   (`sum_tr_eq'`); the relation for `m = q^i` follows from the `U_q` relation (`coeff_pow_mul`).
4. Undoing `R`: `Z = (const) g + (const) (g | Y)`, `Y = η D_{Q'} η⁻¹ D_Q`-type element
   (`Z_eq'`). The matrix `γ D_{Q'} γ⁻¹ D_Q` is `γ₂ [Q B; 0 Q']` with `γ₂ ∈ Γ₀(N)`
   (`exists_gamma2`, by Bezout), so `g | Y` is a multiple of `g(x + qτ)` (`slash_Y_eq`,
   `slash_upperTri_apply`).
5. The first `q`-expansion coefficient of `Q⁻¹ Z` is `Q⁻¹ W(ψ)` (`exists_twist_psi'`) and
   also `Q⁻¹ · Q a_Q Q^(1-k) ψ(-1) c₀` since `g(x + q ·)` has no first coefficient
   (`coeff_one_of_eq'`): `pseudo_core'`.
6. `|a_q|² = q^(k-1)` by Li's theorem, since `ψ` primitive mod `q^(n+1)` forces the nebentypus not
   to factor through `N/q` (`not_exists_comp'`, via a CRT lift `exists_unit_crt'`); then
   `|a_Q|² = Q^(k-1)` and the constant becomes `Q⁻¹ ψ(-1) W(ψ) conj(a_Q)`.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace ModularFormsKB.Miyake.Sec4_6

open ModularFormsKB.Miyake.Wave4 ModularFormsKB.Miyake.Wave9

section CosetPP

variable {N : ℕ} [NeZero N] {Q : ℕ} [NeZero Q]

/-- Generalization of `exists_gamma_u` to an arbitrary modulus. -/
lemma exists_gamma_u' (γ : SL(2, ℤ)) (u t : ℤ)
    (ht : (Q : ℤ) ∣ (γ 0 1 + u * γ 1 1) - (γ 0 0 + u * γ 1 0) * t) :
    ∃ γu : SL(2, ℤ), γu 0 0 = γ 0 0 + u * γ 1 0 ∧ γu 1 0 = Q * γ 1 0 ∧
      γu 1 1 = γ 1 1 - γ 1 0 * t ∧
      (Q : ℤ) * γu 0 1 = γ 0 1 + u * γ 1 1 - (γ 0 0 + u * γ 1 0) * t := by
  obtain ⟨B', hB'⟩ := ht
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 :=
    Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
  refine ⟨⟨!![γ 0 0 + u * γ 1 0, B'; Q * γ 1 0, γ 1 1 - γ 1 0 * t], ?_⟩, by simp, by simp, by simp,
    ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (γ 1 0) * hB'
  · show (Q : ℤ) * B' = _
    linear_combination (-1 : ℤ) * hB'

/-- Generalization of `cond_dvd` to unit residues modulo `Q`. -/
lemma cond_dvd' (γ : SL(2, ℤ)) (hA : ((γ 0 0 : ℤ) : ZMod Q) = 0)
    (hB : ((γ 0 1 : ℤ) : ZMod Q) = -1) (hC : ((γ 1 0 : ℤ) : ZMod Q) = 1)
    (hD : ((γ 1 1 : ℤ) : ZMod Q) = 0) (u t : ℤ) (u' : ZMod Q) (hu : (u : ZMod Q) * u' = 1)
    (ht : (t : ZMod Q) = -u') :
    (Q : ℤ) ∣ (γ 0 1 + u * γ 1 1) - (γ 0 0 + u * γ 1 0) * t := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [hA, hB, hC, hD, ht]
  linear_combination hu

/-- The value of `ψ φ` at the diamond label of `γ ∈ Γ₀(N)`: `ψ(d) φ(d)`, for a general `Q`. -/
lemma splitChar_label' (hQ : Q ∥ N) (ψ : DirichletCharacter ℂ Q)
    (φ : DirichletCharacter ℂ (N / Q)) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    (((splitChar hQ ψ φ).toUnitHom ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩) : ℂˣ) : ℂ) =
      ψ ((γ 1 1 : ℤ) : ZMod Q) * φ ((γ 1 1 : ℤ) : ZMod (N / Q)) := by
  rw [MulChar.coe_toUnitHom, MonoidHom.coe_toHomUnits, Gamma0Map_apply]
  have hcop : IsCoprime (γ 1 1) (N : ℤ) := by
    obtain ⟨c, hc⟩ := mem_Gamma0_iff_dvd.mp hγ
    have hdet := Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
    exact ⟨γ 0 0, -(γ 0 1 * c), by rw [hc] at hdet; linear_combination hdet⟩
  simp only [splitChar, MulChar.coeToFun_mul, Pi.mul_apply,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop]

/-- The coset step for a unit residue `a` modulo `Q`:
`S_a ∣ R = ψ(a)⁻¹ S_{-a⁻¹}`. -/
lemma slash_coset' (k : ℤ) (hQ : Q ∥ N) (ψ : DirichletCharacter ℂ Q)
    (φ : DirichletCharacter ℂ (N / Q)) {F : ℍ → ℂ}
    (hF : ∀ γ' : SL(2, ℤ), γ' ∈ Gamma0 N → F ∣[k] mapGL ℝ γ' =
      (ψ ((γ' 1 1 : ℤ) : ZMod Q) * φ ((γ' 1 1 : ℤ) : ZMod (N / Q))) • F)
    {γ : SL(2, ℤ)} (hA : (Q : ℤ) ∣ γ 0 0) (hB : (Q : ℤ) ∣ γ 0 1 + 1) (hC : (Q : ℤ) ∣ γ 1 0 - 1)
    (hD : (Q : ℤ) ∣ γ 1 1) (hC' : ((N / Q : ℕ) : ℤ) ∣ γ 1 0) (hD' : ((N / Q : ℕ) : ℤ) ∣ γ 1 1 - 1)
    (a : (ZMod Q)ˣ) :
    (F ∣[k] Matrix.GeneralLinearGroup.upperRightHom (((a : ZMod Q).val : ℝ) / Q)) ∣[k]
        ((TauCeti.scaleGL Q)⁻¹ * (mapGL ℝ γ * TauCeti.scaleGL Q)) =
      ψ ((a⁻¹ : (ZMod Q)ˣ) : ZMod Q) •
        (F ∣[k] Matrix.GeneralLinearGroup.upperRightHom ((((-a⁻¹ : (ZMod Q)ˣ) : ZMod Q).val : ℝ) / Q)) := by
  have hN : N = Q * (N / Q) := (Nat.mul_div_cancel' hQ.dvd).symm
  set u : ℤ := ((a : ZMod Q).val : ℤ) with hu_def
  set t : ℤ := ((((-a⁻¹ : (ZMod Q)ˣ)) : ZMod Q).val : ℤ) with ht_def
  have hu : (u : ZMod Q) = a := by simp [u]
  have ht : (t : ZMod Q) = -((a⁻¹ : (ZMod Q)ˣ) : ZMod Q) := by simp [t]
  have hA0 : ((γ 0 0 : ℤ) : ZMod Q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hA
  have hB0 : ((γ 0 1 : ℤ) : ZMod Q) = -1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hB
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have hC0 : ((γ 1 0 : ℤ) : ZMod Q) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hC
    push_cast at this
    exact sub_eq_zero.mp this
  have hD0 : ((γ 1 1 : ℤ) : ZMod Q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hD
  obtain ⟨γu, h00, h10, h11, h01⟩ := exists_gamma_u' γ u t
    (cond_dvd' γ hA0 hB0 hC0 hD0 u t _ (by rw [hu]; exact a.mul_inv) ht)
  have hγu : γu ∈ Gamma0 N := by
    rw [Gamma0_mem, h10]
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_
    rw [hN]
    push_cast
    exact mul_dvd_mul_left _ hC'
  have hψ : ((γu 1 1 : ℤ) : ZMod Q) = ((a⁻¹ : (ZMod Q)ˣ) : ZMod Q) := by
    rw [h11]; push_cast; rw [hD0, hC0, ht]; ring
  have hφ : ((γu 1 1 : ℤ) : ZMod (N / Q)) = 1 := by
    rw [h11]
    have e1 : ((γ 1 1 : ℤ) : ZMod (N / Q)) = 1 :=
      sub_eq_zero.mp (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hD')
    have e2 : ((γ 1 0 : ℤ) : ZMod (N / Q)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hC'
    push_cast
    rw [e1, e2]; ring
  have e1 : (((a : ZMod Q).val : ℝ) / Q) = ((u : ℝ) / Q) := by simp [u]
  have e2 : ((((-a⁻¹ : (ZMod Q)ˣ) : ZMod Q).val : ℝ) / Q) = ((t : ℝ) / Q) := by simp [t]
  rw [e1, e2, ← SlashAction.slash_mul, ← mul_assoc, coset_identity γ γu u t h00 h10 h11 h01,
    SlashAction.slash_mul, hF γu hγu, hψ, hφ, MulChar.map_one, mul_one,
    ModularForm.smul_slash_of_det_pos k (by simp [Matrix.GeneralLinearGroup.upperRightHom_apply])]

/-- The element `D⁻¹ γ D` has positive determinant. -/
lemma det_R_pos' (γ : SL(2, ℤ)) :
    0 < ((((TauCeti.scaleGL Q)⁻¹ * (mapGL ℝ γ * TauCeti.scaleGL Q) : GL (Fin 2) ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  have h : Matrix.GeneralLinearGroup.det
      ((TauCeti.scaleGL Q)⁻¹ * (mapGL ℝ γ * TauCeti.scaleGL Q) : GL (Fin 2) ℝ) = 1 := by
    rw [map_mul, map_mul, map_inv, Matrix.SpecialLinearGroup.det_mapGL]
    simp
  rw [h]; simp

/-- `Z ∣ R = ∑_{v unit} S_v`. -/
lemma sum_slash_coset' (k : ℤ) (hQ : Q ∥ N) (ψ : DirichletCharacter ℂ Q)
    (φ : DirichletCharacter ℂ (N / Q)) {F : ℍ → ℂ}
    (hF : ∀ γ' : SL(2, ℤ), γ' ∈ Gamma0 N → F ∣[k] mapGL ℝ γ' =
      (ψ ((γ' 1 1 : ℤ) : ZMod Q) * φ ((γ' 1 1 : ℤ) : ZMod (N / Q))) • F)
    {γ : SL(2, ℤ)} (hA : (Q : ℤ) ∣ γ 0 0) (hB : (Q : ℤ) ∣ γ 0 1 + 1) (hC : (Q : ℤ) ∣ γ 1 0 - 1)
    (hD : (Q : ℤ) ∣ γ 1 1) (hC' : ((N / Q : ℕ) : ℤ) ∣ γ 1 0) (hD' : ((N / Q : ℕ) : ℤ) ∣ γ 1 1 - 1) :
    (∑ a : ZMod Q, ψ a • tr k Q F a) ∣[k]
        ((TauCeti.scaleGL Q)⁻¹ * (mapGL ℝ γ * TauCeti.scaleGL Q)) =
      ∑ u : (ZMod Q)ˣ, tr k Q F (u : ZMod Q) := by
  have hZ : ∑ a : ZMod Q, ψ a • tr k Q F a = ∑ u : (ZMod Q)ˣ, ψ (u : ZMod Q) • tr k Q F (u : ZMod Q) := by
    symm
    refine Fintype.sum_of_injective (Units.val) Units.val_injective _ _ ?_ (fun _ ↦ rfl)
    intro a ha
    have : ¬ IsUnit a := fun h ↦ ha ⟨h.unit, rfl⟩
    simp [MulChar.map_nonunit ψ this]
  rw [hZ, SlashAction.sum_slash]
  have key : ∀ u : (ZMod Q)ˣ, (ψ (u : ZMod Q) • tr k Q F (u : ZMod Q)) ∣[k]
      ((TauCeti.scaleGL Q)⁻¹ * (mapGL ℝ γ * TauCeti.scaleGL Q)) =
      tr k Q F ((-u⁻¹ : (ZMod Q)ˣ) : ZMod Q) := by
    intro u
    rw [ModularForm.smul_slash_of_det_pos k (det_R_pos' γ)]
    erw [slash_coset' k hQ ψ φ hF hA hB hC hD hC' hD' u]
    rw [smul_smul, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, MulChar.map_one,
      one_smul]
  simp_rw [key]
  exact Equiv.sum_comp ((Equiv.inv _).trans (Equiv.neg _)) (fun u : (ZMod Q)ˣ ↦ tr k Q F (u : ZMod Q))

end CosetPP

section NonUnits

variable {q : ℕ} [NeZero q]

/-- The non-units of `ZMod (q^(n+1))` are the multiples of `q`, parametrized by `ZMod (q^n)`:
`∑_{v unit mod q^(n+1)} S_v = ∑_{v mod q^(n+1)} S_v - ∑_{w mod q^n} f ∣ [1 w/q^n; 0 1]`. -/
lemma sum_units_eq (hq : q.Prime) (n : ℕ) (k : ℤ) (F : ℍ → ℂ) :
    ∑ u : (ZMod (q ^ (n + 1)))ˣ, tr k (q ^ (n + 1)) F (u : ZMod (q ^ (n + 1))) =
      ∑ v : ZMod (q ^ (n + 1)), tr k (q ^ (n + 1)) F v - ∑ w : ZMod (q ^ n), tr k (q ^ n) F w := by
  classical
  have hq0 : 0 < q := hq.pos
  have hQ : q ^ (n + 1) = q * q ^ n := by ring
  have hlt : ∀ w : ZMod (q ^ n), q * w.val < q ^ (n + 1) := fun w ↦ by
    rw [hQ]; exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt w) hq0
  set e : ZMod (q ^ n) → ZMod (q ^ (n + 1)) := fun w ↦ ((q * w.val : ℕ) : ZMod (q ^ (n + 1))) with he
  have hev : ∀ w, (e w).val = q * w.val := fun w ↦ ZMod.val_natCast_of_lt (hlt w)
  have hnu : ∀ v : ZMod (q ^ (n + 1)), ¬ IsUnit v ↔ q ∣ v.val := by
    intro v
    have h1 : IsUnit v ↔ v.val.Coprime (q ^ (n + 1)) := by
      rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
    rw [h1, Nat.coprime_pow_right_iff (Nat.succ_pos n), Nat.coprime_comm,
      hq.coprime_iff_not_dvd, not_not]
  have hsub : ∑ u : (ZMod (q ^ (n + 1)))ˣ, tr k (q ^ (n + 1)) F (u : ZMod (q ^ (n + 1))) =
      ∑ v ∈ Finset.univ.filter (fun v : ZMod (q ^ (n + 1)) ↦ IsUnit v), tr k (q ^ (n + 1)) F v := by
    rw [Finset.sum_filter]
    refine (Fintype.sum_of_injective (Units.val) Units.val_injective _
      (fun v : ZMod (q ^ (n + 1)) ↦ if IsUnit v then tr k (q ^ (n + 1)) F v else 0) ?_
      (fun u ↦ by simp))
    intro a ha
    have : ¬ IsUnit a := fun h ↦ ha ⟨h.unit, rfl⟩
    simp [this]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (ZMod (q ^ (n + 1))))
    (fun v ↦ IsUnit v) (tr k (q ^ (n + 1)) F)
  have hnon : ∑ v ∈ Finset.univ.filter (fun v : ZMod (q ^ (n + 1)) ↦ ¬ IsUnit v),
      tr k (q ^ (n + 1)) F v = ∑ w : ZMod (q ^ n), tr k (q ^ n) F w := by
    symm
    refine Finset.sum_nbij e ?_ ?_ ?_ ?_
    · intro w _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnu, hev]
      exact dvd_mul_right _ _
    · intro w _ w' _ h
      have := congrArg ZMod.val h
      rw [hev, hev] at this
      exact ZMod.val_injective _ (Nat.eq_of_mul_eq_mul_left hq0 this)
    · intro v hv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hnu] at hv
      obtain ⟨m, hm⟩ := hv
      have hmlt : m < q ^ n := by
        have := ZMod.val_lt v
        rw [hm, hQ] at this
        exact lt_of_mul_lt_mul_left this hq0.le
      refine ⟨(m : ZMod (q ^ n)), Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      apply ZMod.val_injective
      rw [hev, ZMod.val_natCast_of_lt hmlt, hm]
    · intro w _
      simp only [tr, he, ZMod.val_natCast_of_lt (hlt w)]
      congr 2
      rw [hQ]
      push_cast
      field_simp
  rw [hsub]
  linear_combination hsplit - hnon

end NonUnits

section UOperatorPP

variable {N : ℕ} [NeZero N] {m : ℕ} [NeZero m]

/-- `sum_tr_eq` for an arbitrary positive `m ∣ N`: `∑_{v mod m} f ∣ [1 v/m; 0 1] = m a f(m ·)`
when `a_{m j} = a a_j`. -/
lemma sum_tr_eq' (k : ℤ) (hmN : m ∣ N) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (a : ℂ)
    (hU : ∀ j, (qExpansion 1 ⇑f).coeff (m * j) = a * (qExpansion 1 ⇑f).coeff j) :
    ∑ v : ZMod m, tr k m ⇑f v = ((m : ℂ) * a) • (fun τ ↦ f (TauCeti.scaleGL m • τ)) := by
  have hNL : N * m ∣ m * N := by rw [mul_comm]
  have hML : m * m ∣ m * N := mul_dvd_mul_left m hmN
  set Φ : ZMod m → ℂ := Pi.single 0 1 with hΦ
  have hcoeff : ∀ j, (qExpansion 1 ⇑(CuspForm.twist Φ hNL hML f)).coeff j =
      a * (qExpansion 1 ⇑(TauCeti.CuspForm.levelRaise m
        (TauCeti.Gamma1_map_le_conjAct_scaleGL N m) f)).coeff j := by
    intro j
    rw [CuspForm.qExpansion_twist_coeff, TauCeti.CuspForm.qExpansion_levelRaise_coeff_Gamma1]
    by_cases hd : m ∣ j
    · obtain ⟨i, rfl⟩ := hd
      simp only [dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne m)), hU i]
      simp [hΦ]
    · have : (j : ZMod m) ≠ 0 := fun h ↦ hd ((ZMod.natCast_eq_zero_iff j m).mp h)
      simp [hΦ, hd, this]
  have h := funext_of_coeff _ _ a hcoeff
  funext τ
  have h1 := congrFun h τ
  rw [CuspForm.twist_apply, Pi.smul_apply, TauCeti.CuspForm.levelRaise_apply] at h1
  have hF : ∀ b : ZMod m, ZMod.dft Φ b = 1 := by
    intro b
    rw [ZMod.dft_apply]
    simp [hΦ, Pi.single_apply]
  simp only [hF, one_mul, smul_eq_mul] at h1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, tr,
    TauCeti.ModularForm.slash_upperRightHom_apply]
  have hq0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [mul_assoc]
  have h2 : ∑ x : ZMod m, (⇑f) (((x.val : ℝ) / m) +ᵥ τ) = (m : ℂ) * (a * f (TauCeti.scaleGL m • τ)) := by
    rw [← h1]; field_simp
  rw [← h2]

/-- Generalization of `exists_twist_psi` to a modulus `m` (the twist of `f` by the inverse
discrete Fourier transform of `ψ`; its first coefficient is `m⁻¹ W(ψ)`). -/
lemma exists_twist_psi' (k : ℤ) (hmN : m ∣ N) (ψ : DirichletCharacter ℂ m)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∃ T : CuspForm ((Gamma1 (m * N)).map (mapGL ℝ)) k,
      (∀ τ : ℍ, T τ = (m : ℂ)⁻¹ * (∑ a : ZMod m, ψ a • tr k m ⇑f a) τ) ∧
      (qExpansion 1 ⇑T).coeff 1 =
        (m : ℂ)⁻¹ * gaussSum ψ ZMod.stdAddChar * (qExpansion 1 ⇑f).coeff 1 := by
  have hNL : N * m ∣ m * N := by rw [mul_comm]
  have hML : m * m ∣ m * N := mul_dvd_mul_left m hmN
  set Φ : ZMod m → ℂ := ZMod.dft.symm (fun a ↦ ψ a) with hΦ
  have hF : ZMod.dft Φ = fun a ↦ ψ a := LinearEquiv.apply_symm_apply _ _
  refine ⟨CuspForm.twist Φ hNL hML f, ?_, ?_⟩
  · intro τ
    rw [CuspForm.twist_apply, hF]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, tr,
      TauCeti.ModularForm.slash_upperRightHom_apply]
  · rw [CuspForm.qExpansion_twist_coeff]
    have h1 : Φ ((1 : ℕ) : ZMod m) = (m : ℂ)⁻¹ * gaussSum ψ ZMod.stdAddChar := by
      rw [hΦ, ZMod.invDFT_apply]
      simp [gaussSum, mul_comm]
    rw [h1]

end UOperatorPP

section FirstCoeffPP

/-- If `T(τ) = α g(τ) + β g(x + qτ)` with `q ≥ 2`, the first coefficient of `T` is `α b₁`
(the shifted dilate only contributes to coefficients divisible by `q`). -/
lemma coeff_one_of_eq' (k : ℤ) {L N q : ℕ} [NeZero L] [NeZero N] [NeZero q] (hq : 2 ≤ q)
    (T : CuspForm ((Gamma1 L).map (mapGL ℝ)) k) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (α β : ℂ) (x : ℝ)
    (h : ∀ τ : ℍ, T τ = α * g τ + β * g (x +ᵥ (TauCeti.scaleGL q • τ))) :
    (qExpansion 1 ⇑T).coeff 1 = α * (qExpansion 1 ⇑g).coeff 1 := by
  have : Fact (IsCusp OnePoint.infty ((Gamma1 N).map (mapGL ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N)⟩
  have : Fact (IsCusp OnePoint.infty ((Gamma1 L).map (mapGL ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map L)⟩
  set E : ℂ := Function.Periodic.qParam 1 (x : ℂ) with hE
  set b : ℕ → ℂ := fun n ↦ (qExpansion 1 ⇑g).coeff n with hb
  set d : ℕ → ℂ := fun j ↦ if q ∣ j then b (j / q) * E ^ (j / q) else 0 with hd
  set c : ℕ → ℂ := fun j ↦ α * b j + β * d j with hc
  have hsum : ∀ τ : ℍ, HasSum (fun j ↦ c j • Function.Periodic.qParam 1 (τ : ℂ) ^ j) (T τ) := by
    intro τ
    have h1 := (ModularForm.hasSum_qExpansion (f := g) one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map N) τ).mul_left α
    have h2 := (ModularForm.hasSum_qExpansion (f := g) one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map N) (x +ᵥ (TauCeti.scaleGL q • τ)))
    have hqp : Function.Periodic.qParam 1 (((x +ᵥ (TauCeti.scaleGL q • τ) : ℍ)) : ℂ) =
        E * Function.Periodic.qParam 1 (τ : ℂ) ^ q := by
      rw [UpperHalfPlane.coe_vadd, TauCeti.coe_scaleGL_smul]
      simp only [Function.Periodic.qParam, hE, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have h3 : HasSum (fun j ↦ d j * Function.Periodic.qParam 1 (τ : ℂ) ^ j)
        (g (x +ᵥ (TauCeti.scaleGL q • τ))) := by
      have hinj : Function.Injective (fun n : ℕ ↦ q * n) :=
        fun a a' h ↦ Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne q)) h
      rw [← hinj.hasSum_iff]
      · rw [hqp] at h2
        convert h2 using 1
        funext n
        have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
        simp only [Function.comp, hd, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hq0,
          mul_pow, ← pow_mul]
        ring
      · intro j hj
        have : ¬ q ∣ j := fun ⟨i, hi⟩ ↦ hj ⟨i, hi.symm⟩
        simp [hd, this]
    rw [h τ]
    convert h1.add (h3.mul_left β) using 1
    funext j
    simp only [hc, smul_eq_mul]
    ring
  have := ModularFormClass.qExpansion_coeff_unique one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map L) (f := T) hsum 1
  rw [← this, hc]
  have : ¬ q ∣ 1 := fun h1 ↦ by have := Nat.le_of_dvd one_pos h1; omega
  simp [hd, this, hb]

end FirstCoeffPP

section UpperTri

/-- The upper triangular matrix `[q d, B; 0, d]` in `GL₂(ℝ)`. -/
def upperTri (q d : ℕ) [NeZero q] [NeZero d] (B : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![((q * d : ℕ) : ℝ), B; 0, (d : ℝ)] (by
    have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    simp [Matrix.det_fin_two, hq, hd])

lemma coe_upperTri (q d : ℕ) [NeZero q] [NeZero d] (B : ℝ) :
    ((upperTri q d B : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((q * d : ℕ) : ℝ), B; 0, (d : ℝ)] := by
  simp [upperTri]

lemma det_upperTri_pos (q d : ℕ) [NeZero q] [NeZero d] (B : ℝ) :
    0 < ((upperTri q d B : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  have hq : 0 < (q : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  rw [coe_upperTri]
  simp [Matrix.det_fin_two]
  positivity

/-- Slashing by `[q d, B; 0, d]` is a dilation by `q` and a shift by `B/d`, up to a constant. -/
lemma slash_upperTri_apply (k : ℤ) (q d : ℕ) [NeZero q] [NeZero d] (B : ℝ) (G : ℍ → ℂ) (τ : ℍ) :
    (G ∣[k] upperTri q d B) τ =
      (((q * d * d : ℕ) : ℂ) ^ (k - 1) * (d : ℂ) ^ (-k)) *
        G ((B / d) +ᵥ (TauCeti.scaleGL q • τ)) := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hpos := det_upperTri_pos q d B
  have hdet : (upperTri q d B).det.val = ((q * d * d : ℕ) : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_upperTri]
    simp [Matrix.det_fin_two]
  have hpt : (upperTri q d B) • τ = (B / d) +ᵥ (TauCeti.scaleGL q • τ) := by
    apply UpperHalfPlane.ext
    rw [coe_smul_of_det_pos (by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hpos),
      UpperHalfPlane.coe_vadd, TauCeti.coe_scaleGL_smul]
    simp only [UpperHalfPlane.num, UpperHalfPlane.denom, coe_upperTri]
    simp
    field_simp
    ring
  rw [ModularForm.slash_apply, UpperHalfPlane.σ_eq_refl_of_det_pos hpos, hpt, hdet]
  simp only [ContinuousAlgEquiv.refl_apply, UpperHalfPlane.denom, coe_upperTri]
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  simp only [Complex.ofReal_natCast]
  simp
  ring

/-- The matrix step: for `γ ∈ SL₂(ℤ)` with `q ∣ γ₀₀` and `N ∣ γ₁₀ γ₁₁`,
`γ D_{q^n} γ⁻¹ D_{q^(n+1)} = γ₂ [q^(n+1), B; 0, q^n]` with `γ₂ ∈ Γ₀(N)`. -/
lemma exists_gamma2 {N q : ℕ} [NeZero N] [NeZero q] (n : ℕ) (γ : SL(2, ℤ))
    (hqa : (q : ℤ) ∣ γ 0 0) (hNx : (N : ℤ) ∣ γ 1 0 * γ 1 1) :
    ∃ (γ₂ : SL(2, ℤ)) (B : ℤ), γ₂ ∈ Gamma0 N ∧
      mapGL ℝ γ * TauCeti.scaleGL (q ^ n) * (mapGL ℝ γ)⁻¹ * TauCeti.scaleGL (q ^ (n + 1)) =
        mapGL ℝ γ₂ * upperTri q (q ^ n) (B : ℝ) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 :=
    Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
  have hinv : (mapGL ℝ γ)⁻¹ = mapGL ℝ γ⁻¹ := (map_inv _ γ).symm
  generalize hQ'd : ((q : ℤ) ^ n) = Q' at *
  obtain ⟨x11, hx11⟩ : ∃ x : ℤ, x = Q' * γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 := ⟨_, rfl⟩
  obtain ⟨x21, hx21⟩ : ∃ x : ℤ, x = γ 1 0 * γ 1 1 * (Q' - 1) := ⟨_, rfl⟩
  obtain ⟨y12, hy12⟩ : ∃ x : ℤ, x = γ 0 0 * γ 0 1 * (1 - Q') := ⟨_, rfl⟩
  obtain ⟨y22, hy22⟩ : ∃ x : ℤ, x = γ 0 0 * γ 1 1 - Q' * γ 0 1 * γ 1 0 := ⟨_, rfl⟩
  have hQ' : Q' = x11 * y22 - x21 * y12 := by
    rw [hx11, hx21, hy12, hy22]
    linear_combination (-Q' * (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 + 1)) * hdet
  have hq1 : (q : ℤ) ∣ x11 - 1 := by
    obtain ⟨m, hm⟩ := hqa
    exact ⟨m * γ 1 1 * (Q' - 1), by rw [hx11]; linear_combination hdet + (γ 1 1 * (Q' - 1)) * hm⟩
  have hcop : IsCoprime x11 Q' := by
    obtain ⟨j, hj⟩ := hq1
    have : IsCoprime x11 (q : ℤ) := ⟨1, -j, by linear_combination hj⟩
    rw [← hQ'd]
    exact this.pow_right
  obtain ⟨u0, v0, h0⟩ := hcop
  obtain ⟨s, hs⟩ : ∃ s : ℤ, s = v0 * y12 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℤ, t = u0 + v0 * y22 := ⟨_, rfl⟩
  have hbez : x11 * t - s * x21 = 1 := by
    rw [hs, ht]; linear_combination h0 - v0 * hQ'
  obtain ⟨γ₂, h2a, h2b, h2c, h2d⟩ : ∃ γ₂ : SL(2, ℤ), γ₂ 0 0 = x11 ∧ γ₂ 0 1 = s ∧ γ₂ 1 0 = x21 ∧
      γ₂ 1 1 = t :=
    ⟨⟨!![x11, s; x21, t], by rw [Matrix.det_fin_two_of]; linear_combination hbez⟩,
      rfl, rfl, rfl, rfl⟩
  refine ⟨γ₂, t * y12 - s * y22, ?_, ?_⟩
  · rw [Gamma0_mem, h2c, ZMod.intCast_zmod_eq_zero_iff_dvd, hx21]
    exact Dvd.dvd.mul_right hNx _
  · rw [hinv]
    refine Units.ext ?_
    simp only [Units.val_mul, TauCeti.coe_scaleGL, coe_upperTri,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    have hQr : ((Q' : ℤ) : ℝ) = (q : ℝ) ^ n := by rw [← hQ'd]; push_cast; ring
    have hx11r : (x11 : ℝ) = (q : ℝ) ^ n * γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 := by
      have := congrArg (Int.cast : ℤ → ℝ) hx11
      push_cast at this; rw [hQr] at this; exact this
    have hx21r : (x21 : ℝ) = γ 1 0 * γ 1 1 * ((q : ℝ) ^ n - 1) := by
      have := congrArg (Int.cast : ℤ → ℝ) hx21
      push_cast at this; rw [hQr] at this; exact this
    have hy12r : (y12 : ℝ) = γ 0 0 * γ 0 1 * (1 - (q : ℝ) ^ n) := by
      have := congrArg (Int.cast : ℤ → ℝ) hy12
      push_cast at this; rw [hQr] at this; exact this
    have hy22r : (y22 : ℝ) = γ 0 0 * γ 1 1 - (q : ℝ) ^ n * γ 0 1 * γ 1 0 := by
      have := congrArg (Int.cast : ℤ → ℝ) hy22
      push_cast at this; rw [hQr] at this; exact this
    have hQ'r : (q : ℝ) ^ n = x11 * y22 - x21 * y12 := by
      have := congrArg (Int.cast : ℤ → ℝ) hQ'
      push_cast at this; rw [hQr] at this; exact this
    have hbezr : (x11 : ℝ) * t - s * x21 = 1 := by exact_mod_cast hbez
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h2a, h2b, h2c, h2d, Matrix.trace_fin_two,
        pow_succ]
    · linear_combination (-((q : ℝ) ^ n * q)) * hx11r
    · linear_combination (-(y12 : ℝ)) * hbezr + (-(s : ℝ)) * hQ'r - hy12r
    · linear_combination (-((q : ℝ) ^ n * q)) * hx21r
    · linear_combination (-(y22 : ℝ)) * hbezr + (-(t : ℝ)) * hQ'r - hy22r

/-- The new term: `G ∣ Y`, for `Y = η D' η⁻¹ D`-type element, is a constant multiple of
`G(x + q τ)` when `G` has a nebentypus character on `Γ₀(N)`. -/
lemma slash_Y_eq (k : ℤ) {N q : ℕ} [NeZero N] [NeZero q] (n : ℕ) (G : ℍ → ℂ)
    (hG : ∀ γ' : SL(2, ℤ), γ' ∈ Gamma0 N → ∃ c : ℂ, G ∣[k] mapGL ℝ γ' = c • G)
    (γ : SL(2, ℤ)) (hqa : (q : ℤ) ∣ γ 0 0) (hNx : (N : ℤ) ∣ γ 1 0 * γ 1 1) :
    ∃ (c : ℂ) (x : ℝ), ∀ τ : ℍ,
      (G ∣[k] ((mapGL ℝ γ * TauCeti.scaleGL (q ^ (n + 1))) *
        (TauCeti.scaleGL (q ^ n) * ((mapGL ℝ γ * TauCeti.scaleGL (q ^ (n + 1)))⁻¹ *
          TauCeti.scaleGL (q ^ (n + 1)))))) τ = c * G (x +ᵥ (TauCeti.scaleGL q • τ)) := by
  obtain ⟨γ₂, B, hγ₂, hY⟩ := exists_gamma2 (N := N) (q := q) n γ hqa hNx
  obtain ⟨c, hc⟩ := hG γ₂ hγ₂
  set D := TauCeti.scaleGL (q ^ (n + 1)) with hD
  set D' := TauCeti.scaleGL (q ^ n) with hD'
  have hcomm : D * D' = D' * D := by
    rw [hD, hD', ← TauCeti.scaleGL_mul, ← TauCeti.scaleGL_mul]
    congr 1
    exact mul_comm _ _
  have hY' : (mapGL ℝ γ * D) * (D' * ((mapGL ℝ γ * D)⁻¹ * D)) =
      mapGL ℝ γ₂ * upperTri q (q ^ n) (B : ℝ) := by
    rw [← hY]
    have : (mapGL ℝ γ * D) * (D' * ((mapGL ℝ γ * D)⁻¹ * D)) =
        mapGL ℝ γ * (D * D' * D⁻¹) * (mapGL ℝ γ)⁻¹ * D := by
      simp only [mul_inv_rev, mul_assoc]
    rw [this, hcomm, mul_inv_cancel_right]
  rw [hY']
  refine ⟨c * (((q * q ^ n * q ^ n : ℕ) : ℂ) ^ (k - 1) * ((q ^ n : ℕ) : ℂ) ^ (-k)),
    (B : ℝ) / ((q ^ n : ℕ) : ℝ), fun τ ↦ ?_⟩
  rw [SlashAction.slash_mul, hc, ModularForm.smul_slash_of_det_pos k (by
      have := det_upperTri_pos q (q ^ n) (B : ℝ)
      exact this)]
  rw [Pi.smul_apply, slash_upperTri_apply, smul_eq_mul]
  ring

end UpperTri

section ZEqPP

variable {N : ℕ} [NeZero N] {Q : ℕ} [NeZero Q]

/-- `slash_gamma_sq` for a general modulus `Q`. -/
lemma slash_gamma_sq' (k : ℤ) (hQ : Q ∥ N) (ψ : DirichletCharacter ℂ Q)
    (φ : DirichletCharacter ℂ (N / Q)) {F : ℍ → ℂ}
    (hF : ∀ γ' : SL(2, ℤ), γ' ∈ Gamma0 N → F ∣[k] mapGL ℝ γ' =
      (ψ ((γ' 1 1 : ℤ) : ZMod Q) * φ ((γ' 1 1 : ℤ) : ZMod (N / Q))) • F)
    {γ : SL(2, ℤ)} (hA : (Q : ℤ) ∣ γ 0 0) (hB : (Q : ℤ) ∣ γ 0 1 + 1) (hC : (Q : ℤ) ∣ γ 1 0 - 1)
    (hD : (Q : ℤ) ∣ γ 1 1) (hC' : ((N / Q : ℕ) : ℤ) ∣ γ 1 0) (hD' : ((N / Q : ℕ) : ℤ) ∣ γ 1 1 - 1) :
    (F ∣[k] mapGL ℝ γ) ∣[k] mapGL ℝ γ = ψ (-1) • F := by
  have hN : N = Q * (N / Q) := (Nat.mul_div_cancel' hQ.dvd).symm
  have e10 : ((γ * γ : SL(2, ℤ)) 1 0 : ℤ) = γ 1 0 * (γ 0 0 + γ 1 1) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  have e11 : ((γ * γ : SL(2, ℤ)) 1 1 : ℤ) = γ 1 0 * γ 0 1 + γ 1 1 * γ 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hmem : γ * γ ∈ Gamma0 N := by
    rw [Gamma0_mem, e10]
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_
    rw [hN]; push_cast
    rw [mul_comm (γ 1 0)]
    exact mul_dvd_mul (dvd_add hA hD) hC'
  have hB0 : ((γ 0 1 : ℤ) : ZMod Q) = -1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hB
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have hC0 : ((γ 1 0 : ℤ) : ZMod Q) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hC
    push_cast at this
    exact sub_eq_zero.mp this
  have hD0 : ((γ 1 1 : ℤ) : ZMod Q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hD
  have e1 : ((γ 1 1 : ℤ) : ZMod (N / Q)) = 1 :=
    sub_eq_zero.mp (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hD')
  have e2 : ((γ 1 0 : ℤ) : ZMod (N / Q)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hC'
  rw [← SlashAction.slash_mul, ← map_mul, hF _ hmem, e11]
  push_cast
  rw [hC0, hB0, hD0, e1, e2]
  simp

end ZEqPP

section ZEqPP2

variable {N : ℕ} [NeZero N] {q : ℕ} [NeZero q]

/-- The identity for `Z = ∑_a ψ(a) S_a` at `Q = q^(n+1)`:
`Z(τ) = Q a_Q Q^(1-k) ψ(-1) c₀ g(τ) + β g(x + qτ)` for some `β`, `x`. -/
lemma Z_eq' (k : ℤ) (hq : q.Prime) (n : ℕ) (hQ : q ^ (n + 1) ∥ N)
    (ψ : DirichletCharacter ℂ (q ^ (n + 1))) (φ : DirichletCharacter ℂ (N / q ^ (n + 1)))
    {F G₀ : ℍ → ℂ}
    (hF : ∀ γ' : SL(2, ℤ), γ' ∈ Gamma0 N → F ∣[k] mapGL ℝ γ' =
      (ψ ((γ' 1 1 : ℤ) : ZMod (q ^ (n + 1))) * φ ((γ' 1 1 : ℤ) : ZMod (N / q ^ (n + 1)))) • F)
    (hG : ∀ γ' : SL(2, ℤ), γ' ∈ Gamma0 N → ∃ c : ℂ, G₀ ∣[k] mapGL ℝ γ' = c • G₀)
    {γ : SL(2, ℤ)} (hA : ((q ^ (n + 1) : ℕ) : ℤ) ∣ γ 0 0) (hB : ((q ^ (n + 1) : ℕ) : ℤ) ∣ γ 0 1 + 1)
    (hC : ((q ^ (n + 1) : ℕ) : ℤ) ∣ γ 1 0 - 1) (hD : ((q ^ (n + 1) : ℕ) : ℤ) ∣ γ 1 1)
    (hC' : ((N / q ^ (n + 1) : ℕ) : ℤ) ∣ γ 1 0) (hD' : ((N / q ^ (n + 1) : ℕ) : ℤ) ∣ γ 1 1 - 1)
    (c₀ E aQ aQ' : ℂ) (hE0 : E ≠ 0)
    (hfg : F ∣[k] (mapGL ℝ γ * TauCeti.scaleGL (q ^ (n + 1))) = c₀ • G₀)
    (hE : (F ∣[k] (mapGL ℝ γ * TauCeti.scaleGL (q ^ (n + 1)))) ∣[k]
      (mapGL ℝ γ * TauCeti.scaleGL (q ^ (n + 1))) = E • F)
    (hsum : ∑ v : ZMod (q ^ (n + 1)), tr k (q ^ (n + 1)) F v =
      (((q ^ (n + 1) : ℕ) : ℂ) * aQ) • (fun τ ↦ F (TauCeti.scaleGL (q ^ (n + 1)) • τ)))
    (hsum' : ∑ w : ZMod (q ^ n), tr k (q ^ n) F w =
      (((q ^ n : ℕ) : ℂ) * aQ') • (fun τ ↦ F (TauCeti.scaleGL (q ^ n) • τ))) :
    ∃ (β : ℂ) (x : ℝ), ∀ τ : ℍ,
      (∑ a : ZMod (q ^ (n + 1)), ψ a • tr k (q ^ (n + 1)) F a) τ =
        (((q ^ (n + 1) : ℕ) : ℂ) * aQ * ((q ^ (n + 1) : ℕ) : ℂ) ^ (1 - k) * ψ (-1) * c₀) * G₀ τ +
          β * G₀ (x +ᵥ (TauCeti.scaleGL q • τ)) := by
  have hq0 : 0 < q := hq.pos
  have hQdvd : ((q ^ (n + 1) : ℕ) : ℤ) ∣ γ 0 0 := hA
  have hqa : (q : ℤ) ∣ γ 0 0 :=
    (by exact_mod_cast dvd_pow_self q (Nat.succ_ne_zero n) : (q : ℤ) ∣ ((q ^ (n + 1) : ℕ) : ℤ)).trans
      hA
  have hN : N = q ^ (n + 1) * (N / q ^ (n + 1)) := (Nat.mul_div_cancel' hQ.dvd).symm
  have hNx : (N : ℤ) ∣ γ 1 0 * γ 1 1 := by
    have := mul_dvd_mul hC' hD
    rw [← Nat.cast_mul, mul_comm, ← hN] at this
    exact this
  obtain ⟨c, x, hcx⟩ := slash_Y_eq k n G₀ hG γ hqa hNx
  set D := TauCeti.scaleGL (q ^ (n + 1)) with hD_def
  set D' := TauCeti.scaleGL (q ^ n) with hD'_def
  set g : GL (Fin 2) ℝ := mapGL ℝ γ with hg_def
  have hPDD : PD D := TauCeti.val_det_scaleGL_pos
  have hPDD' : PD D' := TauCeti.val_det_scaleGL_pos
  have hPDg : PD g := PD.mapGL γ
  have hεε : ψ (-1) * ψ (-1) = 1 := by
    rw [← map_mul]; simp
  have h1 : (∑ a : ZMod (q ^ (n + 1)), ψ a • tr k (q ^ (n + 1)) F a) ∣[k] (D⁻¹ * (g * D)) =
      (∑ v : ZMod (q ^ (n + 1)), tr k (q ^ (n + 1)) F v) -
        ∑ w : ZMod (q ^ n), tr k (q ^ n) F w := by
    rw [sum_slash_coset' k hQ ψ φ hF hA hB hC hD hC' hD', sum_units_eq hq n k F]
  have hFD : (fun τ ↦ F (D • τ)) = ((q ^ (n + 1) : ℕ) : ℂ) ^ (1 - k) • (F ∣[k] D) :=
    (TauCeti.smul_slash_scaleGL_eq k F).symm
  have hFD' : (fun τ ↦ F (D' • τ)) = ((q ^ n : ℕ) : ℂ) ^ (1 - k) • (F ∣[k] D') :=
    (TauCeti.smul_slash_scaleGL_eq k F).symm
  rw [hsum, hsum', hFD, hFD', smul_smul, smul_smul] at h1
  have hFγ : F ∣[k] g = c₀ • (G₀ ∣[k] D⁻¹) := by
    have : (F ∣[k] g) ∣[k] D = c₀ • G₀ := by rw [← SlashAction.slash_mul]; exact hfg
    calc F ∣[k] g = ((F ∣[k] g) ∣[k] D) ∣[k] D⁻¹ := (slash_cancel k D _).symm
      _ = _ := by rw [this, smul_slash_PD k hPDD.inv]
  have hγinv : F ∣[k] g⁻¹ = ψ (-1) • (F ∣[k] g) := by
    have hsq := slash_gamma_sq' k hQ ψ φ hF hA hB hC hD hC' hD'
    have h' : F ∣[k] g = ψ (-1) • (F ∣[k] g⁻¹) := by
      calc F ∣[k] g = ((F ∣[k] g) ∣[k] g) ∣[k] g⁻¹ := (slash_cancel k g _).symm
        _ = _ := by rw [hsq, smul_slash_PD k hPDg.inv]
    rw [h', smul_smul, hεε, one_smul]
  have hηinv : F ∣[k] (g * D)⁻¹ = (E⁻¹ * c₀) • G₀ := by
    have hPDη : PD (g * D) := hPDg.mul hPDD
    have h' : F ∣[k] (g * D) = E • (F ∣[k] (g * D)⁻¹) := by
      calc F ∣[k] (g * D) = ((F ∣[k] (g * D)) ∣[k] (g * D)) ∣[k] (g * D)⁻¹ :=
            (slash_cancel k (g * D) _).symm
        _ = _ := by rw [hE, smul_slash_PD k hPDη.inv]
    rw [hfg] at h'
    calc F ∣[k] (g * D)⁻¹ = E⁻¹ • (E • (F ∣[k] (g * D)⁻¹)) := by
          rw [smul_smul, inv_mul_cancel₀ hE0, one_smul]
      _ = _ := by rw [← h', smul_smul]
  have hDη : D * (g * D)⁻¹ = g⁻¹ := by
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  have hR : (D⁻¹ * (g * D))⁻¹ = (g * D)⁻¹ * D := by rw [mul_inv_rev, inv_inv]
  have hPDR : PD ((g * D)⁻¹ * D) := (hPDg.mul hPDD).inv.mul hPDD
  set Y : GL (Fin 2) ℝ := (g * D) * (D' * ((g * D)⁻¹ * D)) with hY_def
  have hPDY : PD Y := (hPDg.mul hPDD).mul (hPDD'.mul hPDR)
  have t1 : (F ∣[k] D) ∣[k] ((g * D)⁻¹ * D) = (ψ (-1) * c₀) • G₀ := by
    rw [← SlashAction.slash_mul, ← mul_assoc, hDη, SlashAction.slash_mul, hγinv, hFγ,
      smul_slash_PD k hPDD, smul_slash_PD k hPDD, slash_cancel' k D, smul_smul]
  have t2 : (F ∣[k] D') ∣[k] ((g * D)⁻¹ * D) = (E⁻¹ * c₀) • (G₀ ∣[k] Y) := by
    rw [← SlashAction.slash_mul, show D' * ((g * D)⁻¹ * D) = (g * D)⁻¹ * Y by
      rw [hY_def, inv_mul_cancel_left], SlashAction.slash_mul, hηinv,
      smul_slash_PD k hPDY]
  have hZ : ∑ a : ZMod (q ^ (n + 1)), ψ a • tr k (q ^ (n + 1)) F a =
      ((∑ a : ZMod (q ^ (n + 1)), ψ a • tr k (q ^ (n + 1)) F a) ∣[k] (D⁻¹ * (g * D))) ∣[k]
        (D⁻¹ * (g * D))⁻¹ :=
    (slash_cancel k _ _).symm
  refine ⟨-(((q ^ n : ℕ) : ℂ) * aQ' * ((q ^ n : ℕ) : ℂ) ^ (1 - k)) * (E⁻¹ * c₀ * c), x, fun τ ↦ ?_⟩
  rw [hZ, h1, hR, SlashAction.sub_slash, smul_slash_PD k hPDR, smul_slash_PD k hPDR, t1, t2]
  have := hcx τ
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [this]
  ring

end ZEqPP2

section PrimitivePP

variable {N : ℕ} [NeZero N] {q : ℕ} [NeZero q]

/-- CRT lift: a unit `v` modulo `q^(n+1)` that is `1` modulo `q^n` lifts to a unit modulo `N` that
is `1` modulo `N / q^(n+1)` and modulo `N / q`. -/
lemma exists_unit_crt' (hq : q.Prime) (n : ℕ) (hQ : q ^ (n + 1) ∥ N) (v : (ZMod (q ^ (n + 1)))ˣ)
    (hv : ZMod.unitsMap (pow_dvd_pow q (Nat.le_succ n)) v = 1) :
    ∃ x : (ZMod N)ˣ, ZMod.unitsMap hQ.dvd x = v ∧
      ZMod.unitsMap (Nat.div_dvd_of_dvd hQ.dvd) x = 1 ∧
      ZMod.unitsMap (Nat.div_dvd_of_dvd ((dvd_pow_self q (Nat.succ_ne_zero n)).trans hQ.dvd)) x = 1 := by
  have hqQ : q ∣ q ^ (n + 1) := dvd_pow_self q (Nat.succ_ne_zero n)
  have hqN : q ∣ N := hqQ.trans hQ.dvd
  obtain ⟨m, hm1, hm2⟩ := Nat.chineseRemainder hQ.coprime ((v : ZMod (q ^ (n + 1))).val) 1
  have hmq : (m : ZMod (q ^ (n + 1))) = v := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hm1]; exact ZMod.natCast_zmod_val _
  have hmN' : (m : ZMod (N / q ^ (n + 1))) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff m 1 (N / q ^ (n + 1))).mpr hm2
    simpa using this
  have hc1 : m.Coprime (q ^ (n + 1)) := (ZMod.isUnit_iff_coprime m _).mp (hmq ▸ v.isUnit)
  have hc2 : m.Coprime (N / q ^ (n + 1)) := (ZMod.isUnit_iff_coprime m _).mp (hmN' ▸ isUnit_one)
  have hN : N = q ^ (n + 1) * (N / q ^ (n + 1)) := (Nat.mul_div_cancel' hQ.dvd).symm
  have hcop : m.Coprime N := by
    rw [hN]; exact Nat.Coprime.mul_right hc1 hc2
  -- `m ≡ 1 mod q^n`
  have hm_pn : m ≡ 1 [MOD q ^ n] := by
    have h1 : m ≡ (v : ZMod (q ^ (n + 1))).val [MOD q ^ n] :=
      Nat.ModEq.of_dvd (pow_dvd_pow q (Nat.le_succ n)) hm1
    have h2 : ((v : ZMod (q ^ (n + 1))).val : ZMod (q ^ n)) = 1 := by
      have := congrArg (fun u : (ZMod (q ^ n))ˣ ↦ (u : ZMod (q ^ n))) hv
      simp only [ZMod.unitsMap_val, Units.val_one] at this
      rw [← this, ← ZMod.cast_natCast (pow_dvd_pow q (Nat.le_succ n)), ZMod.natCast_zmod_val]
    have h3 : (v : ZMod (q ^ (n + 1))).val ≡ 1 [MOD q ^ n] := by
      have := (ZMod.natCast_eq_natCast_iff (v : ZMod (q ^ (n + 1))).val 1 (q ^ n)).mp
        (by simpa using h2)
      exact this
    exact h1.trans h3
  have hm_Nq : m ≡ 1 [MOD N / q] := by
    have hNq : N / q = q ^ n * (N / q ^ (n + 1)) := by
      apply Nat.div_eq_of_eq_mul_left hq.pos
      conv_lhs => rw [hN]
      ring
    rw [hNq]
    have hcop' : (q ^ n).Coprime (N / q ^ (n + 1)) :=
      Nat.Coprime.coprime_dvd_left (pow_dvd_pow q (Nat.le_succ n)) hQ.coprime
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop').mp ⟨hm_pn, hm2⟩
  have hmNq : (m : ZMod (N / q)) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff m 1 (N / q)).mpr hm_Nq
    simpa using this
  refine ⟨ZMod.unitOfCoprime m hcop, Units.ext ?_, Units.ext ?_, Units.ext ?_⟩
  · rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime]
    simp only [ZMod.cast_natCast hQ.dvd, hmq]
  · rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime]
    simp only [ZMod.cast_natCast (Nat.div_dvd_of_dvd hQ.dvd), hmN', Units.val_one]
  · rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime]
    simp only [ZMod.cast_natCast (Nat.div_dvd_of_dvd hqN), hmNq, Units.val_one]

/-- A character of conductor `q^(n+1)` does not factor through `N / q`. -/
lemma not_exists_comp' (hq : q.Prime) (n : ℕ) (hQ : q ^ (n + 1) ∥ N)
    (ψ : DirichletCharacter ℂ (q ^ (n + 1))) (φ : DirichletCharacter ℂ (N / q ^ (n + 1)))
    (hψ : ψ.IsPrimitive) :
    ¬ ∃ χ₀ : (ZMod (N / q))ˣ →* ℂˣ, (splitChar hQ ψ φ).toUnitHom =
      χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd
        ((dvd_pow_self q (Nat.succ_ne_zero n)).trans hQ.dvd))) := by
  rintro ⟨χ₀, h⟩
  have hfac : ψ.FactorsThrough (q ^ n) := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (pow_dvd_pow q (Nat.le_succ n))]
    intro v hv
    rw [MonoidHom.mem_ker] at hv ⊢
    obtain ⟨x, hx1, hx2, hx3⟩ := exists_unit_crt' hq n hQ v hv
    have := congrArg (fun χ : (ZMod N)ˣ →* ℂˣ ↦ ((χ x : ℂˣ) : ℂ)) h
    simp only [toUnitHom_splitChar, MonoidHom.mul_apply, MonoidHom.comp_apply, hx1, hx2, hx3,
      map_one, Units.val_one, mul_one] at this
    apply Units.ext
    simpa using this
  have hle : ψ.conductor ≤ q ^ n :=
    Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff ψ).mpr hfac)
  have := hψ
  rw [DirichletCharacter.IsPrimitive] at this
  have hlt : q ^ n < q ^ (n + 1) := Nat.pow_lt_pow_right hq.one_lt (Nat.lt_succ_self n)
  omega

end PrimitivePP

section CorePP

variable {N : ℕ} [NeZero N] {q : ℕ} [NeZero q] {M : Matrix (Fin 2) (Fin 2) ℤ}

/-- The `U_q` relation and the norm of `a_q` for a primitive form whose nebentypus has a
primitive `q^(n+1)`-part: Tau Ceti's Li theorem applies because the character does not factor
through `N / q` (`not_exists_comp'`). -/
lemma prim_facts' (k : ℤ) (hq : q.Prime) (n : ℕ) (hQ : q ^ (n + 1) ∥ N)
    (ψ : DirichletCharacter ℂ (q ^ (n + 1))) (φ : DirichletCharacter ℂ (N / q ^ (n + 1)))
    (hψ : ψ.IsPrimitive) {f : cuspSpace k (splitChar hQ ψ φ)} (hf : IsPrimitive f) :
    (∀ m, coeff f (q * m) = coeff f q * coeff f m) ∧
      coeff f q * starRingEnd ℂ (coeff f q) = (q : ℂ) ^ (k - 1) := by
  obtain ⟨F, hχ, hF⟩ := (isPrimitive_iff_exists_newform f).mp hf
  have hqN : q ∣ N := (dvd_pow_self q (Nat.succ_ne_zero n)).trans hQ.dvd
  have hU := F.heckeUCuspNat_eq_qExpansion_coeff_smul hq hqN
  have hU' := (HeckeRing.GL2.heckeUCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul k hq hqN
    _).mp hU
  rw [hF] at hU'
  refine ⟨hU', ?_⟩
  have hχ' : ¬ F.dirichletLift.FactorsThrough (N / q) := by
    intro hft
    apply not_exists_comp' hq n hQ ψ φ hψ
    refine ⟨hft.χ₀.toUnitHom, ?_⟩
    rw [← hχ, ← F.dirichletLift_toUnitHom]
    exact (congrArg MulChar.toUnitHom hft.eq_changeLevel).trans
      (DirichletCharacter.changeLevel_toUnitHom _ _)
  have hn := F.sq_norm_qExpansion_coeff_prime_of_not_factorsThrough hq hqN hχ'
  rw [hF] at hn
  change (qExpansion 1 (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff q *
    starRingEnd ℂ ((qExpansion 1 (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff q) = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn,
    Complex.ofReal_zpow, Complex.ofReal_natCast]

/-- From `a_{q m} = a_q a_m` and `a_1 = 1`: `a_{q^i m} = a_q^i a_m`. -/
lemma coeff_pow_mul {k : ℤ} {χ : DirichletCharacter ℂ N} (f : cuspSpace k χ)
    (hU : ∀ m, coeff f (q * m) = coeff f q * coeff f m) (i m : ℕ) :
    coeff f (q ^ i * m) = coeff f q ^ i * coeff f m := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [show q ^ (i + 1) * m = q * (q ^ i * m) by ring, hU, ih]
    ring

/-- The core identity `Q a_Q Q^(1-k) ψ(-1) c = W(ψ)`, `Q = q^(n+1)`. -/
lemma pseudo_core' (k : ℤ) (hq : q.Prime) (n : ℕ) (hQ : q ^ (n + 1) ∥ N)
    (hM : IsEtaMatrix N (q ^ (n + 1)) M) (ψ : DirichletCharacter ℂ (q ^ (n + 1)))
    (φ : DirichletCharacter ℂ (N / q ^ (n + 1))) (f : cuspSpace k (splitChar hQ ψ φ))
    (g : cuspSpace k (splitChar hQ ψ⁻¹ φ)) (c₀ : ℂ)
    (hfg : ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] etaGL hQ hM =
      c₀ • ⇑(g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hf1 : coeff f 1 = 1) (hg1 : coeff g 1 = 1)
    (hU : ∀ m, coeff f (q * m) = coeff f q * coeff f m) :
    ((q ^ (n + 1) : ℕ) : ℂ) * coeff f (q ^ (n + 1)) * ((q ^ (n + 1) : ℕ) : ℂ) ^ (1 - k) * ψ (-1) * c₀ =
      gaussSum ψ ZMod.stdAddChar := by
  have hqQ : q ∣ q ^ (n + 1) := dvd_pow_self q (Nat.succ_ne_zero n)
  have hQN : q ^ (n + 1) ∣ N := hQ.dvd
  have hQ'N : q ^ n ∣ N := (pow_dvd_pow q (Nat.le_succ n)).trans hQN
  obtain ⟨γ, hMeq, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hM.exists_entries
  have sq1 : ∀ x : ℤ, (((q ^ (n + 1)) ^ 2 : ℕ) : ℤ) ∣ x → ((q ^ (n + 1) : ℕ) : ℤ) ∣ x :=
    fun x hx ↦ (Dvd.intro_left ((q ^ (n + 1) : ℕ) : ℤ) (by push_cast; ring)).trans hx
  have sq2 : ∀ x : ℤ, (((N / q ^ (n + 1)) ^ 2 : ℕ) : ℤ) ∣ x → ((N / q ^ (n + 1) : ℕ) : ℤ) ∣ x :=
    fun x hx ↦ (Dvd.intro_left ((N / q ^ (n + 1) : ℕ) : ℤ) (by push_cast; ring)).trans hx
  have hGL := etaGL_eq_mul hQ hM hMeq
  rw [hGL] at hfg
  have hF : ∀ γ' : SL(2, ℤ), γ' ∈ Gamma0 N → ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k]
      mapGL ℝ γ' = (ψ ((γ' 1 1 : ℤ) : ZMod (q ^ (n + 1))) *
        φ ((γ' 1 1 : ℤ) : ZMod (N / q ^ (n + 1)))) •
        ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := fun γ' h ↦ by
    rw [(TauCeti.mem_cuspFormCharSpace_iff_nebentypus k _ _).mp f.2 ⟨γ', h⟩,
      splitChar_label' hQ ψ φ h]
  have hG : ∀ γ' : SL(2, ℤ), γ' ∈ Gamma0 N → ∃ c : ℂ,
      ⇑(g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] mapGL ℝ γ' =
        c • ⇑(g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := fun γ' h ↦
    ⟨_, (TauCeti.mem_cuspFormCharSpace_iff_nebentypus k _ _).mp g.2 ⟨γ', h⟩⟩
  have hE := eta_slash_eta k hQ hM ψ φ f
  rw [hGL] at hE
  have hE0 := etaSqConst_ne_zero k hQ ψ φ
  have hUQ : ∀ j, (qExpansion 1 ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff
      (q ^ (n + 1) * j) = coeff f (q ^ (n + 1)) * coeff f j := fun j ↦ by
    have h1' := coeff_pow_mul f hU (n + 1) j
    have h2' := coeff_pow_mul f hU (n + 1) 1
    rw [mul_one] at h2'
    rw [h2', hf1, mul_one] at *
    exact h1'
  have hUQ' : ∀ j, (qExpansion 1 ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff
      (q ^ n * j) = coeff f (q ^ n) * coeff f j := fun j ↦ by
    have h1' := coeff_pow_mul f hU n j
    have h2' := coeff_pow_mul f hU n 1
    rw [mul_one] at h2'
    rw [h2', hf1, mul_one] at *
    exact h1'
  have hsum := sum_tr_eq' k hQN (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) _ hUQ
  have hsum' := sum_tr_eq' k hQ'N (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) _ hUQ'
  obtain ⟨β, x, hZ⟩ := Z_eq' k hq n hQ ψ φ hF hG (sq1 _ h1) (sq1 _ h2) (sq1 _ h3) (sq1 _ h4)
    (sq2 _ h7) (sq2 _ h8) c₀ _ (coeff f (q ^ (n + 1))) (coeff f (q ^ n)) hE0 hfg hE hsum hsum'
  obtain ⟨T, hT1, hT2⟩ := exists_twist_psi' k hQN ψ (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
  have hq0 : ((q ^ (n + 1) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hcoef := coeff_one_of_eq' k hq.two_le T
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (((q ^ (n + 1) : ℕ) : ℂ)⁻¹ * (((q ^ (n + 1) : ℕ) : ℂ) * coeff f (q ^ (n + 1)) *
      ((q ^ (n + 1) : ℕ) : ℂ) ^ (1 - k) * ψ (-1) * c₀))
    (((q ^ (n + 1) : ℕ) : ℂ)⁻¹ * β) x (fun τ ↦ by
      rw [hT1, hZ τ]
      ring)
  rw [hT2, show (qExpansion 1 ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 = 1
    from hf1, show (qExpansion 1 ⇑(g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 = 1
    from hg1] at hcoef
  refine mul_left_cancel₀ (inv_ne_zero hq0) ?_
  simpa using hcoef.symm

end CorePP

section MainPP

variable {N : ℕ} [NeZero N] {M : Matrix (Fin 2) (Fin 2) ℤ}

/-- **Miyake, Corollary 4.6.18 (1)** (`N_q = q^e`, `χ_q` primitive modulo `q^e`): for a primitive
form `f = Σ a_n e(nz)` of `𝒮_k^0(N, χ_q χ'_q)`, `f | η_q = c g_q` with
`c = Q⁻¹ χ_q(-1) W(χ_q) conj(a_Q)`, `Q = q^e`, in Mathlib's normalization of the slash. -/
@[kb "miyake1989" "Corollary 4.6.18 (1), p. 172 (N_q = q^e)"]
theorem corollary_4_6_18_one_primePow (k : ℤ) {Q q e : ℕ} [NeZero Q] (hq : q.Prime) (he : 1 ≤ e)
    (hQe : Q = q ^ e) (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M) (ψ : DirichletCharacter ℂ Q)
    (hψ : ψ.IsPrimitive) (φ : DirichletCharacter ℂ (N / Q))
    {f : cuspSpace k (splitChar hQ ψ φ)} (hf : IsPrimitive f) :
    ∃ g : cuspSpace k (splitChar hQ ψ⁻¹ φ), IsPrimitive g ∧
      ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] etaGL hQ hM =
        ((Q : ℂ)⁻¹ * ψ (-1) * gaussSum ψ (ZMod.stdAddChar) * starRingEnd ℂ (coeff f Q)) •
          ⇑(g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
  subst hQe
  have : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨g, hg, ⟨c₀, -, hfg⟩, -⟩ := exists_isPrimitive_eta_all k hQ hM ψ φ hf
  obtain ⟨hU, hnorm⟩ := prim_facts' k hq n hQ ψ φ hψ hf
  have hcore := pseudo_core' k hq n hQ hM ψ φ f g c₀ hfg hf.2.2 hg.2.2 hU
  refine ⟨g, hg, ?_⟩
  rw [hfg]
  congr 1
  have hq0 : ((q ^ (n + 1) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hεε : ψ (-1) * ψ (-1) = 1 := by rw [← map_mul]; simp
  have hpow : ((q ^ (n + 1) : ℕ) : ℂ) ^ (1 - k) * ((q ^ (n + 1) : ℕ) : ℂ) ^ (k - 1) = 1 := by
    rw [← zpow_add₀ hq0]; simp
  have hnormQ : coeff f (q ^ (n + 1)) * starRingEnd ℂ (coeff f (q ^ (n + 1))) =
      ((q ^ (n + 1) : ℕ) : ℂ) ^ (k - 1) := by
    have h1 := coeff_pow_mul f hU (n + 1) 1
    rw [mul_one, hf.2.2, mul_one] at h1
    rw [h1, map_pow, ← mul_pow, hnorm, ← zpow_natCast, ← zpow_mul, Nat.cast_pow,
      ← zpow_natCast, ← zpow_mul, mul_comm]
  rw [← hcore]
  have : ((q ^ (n + 1) : ℕ) : ℂ)⁻¹ * ψ (-1) * (((q ^ (n + 1) : ℕ) : ℂ) * coeff f (q ^ (n + 1)) *
      ((q ^ (n + 1) : ℕ) : ℂ) ^ (1 - k) * ψ (-1) * c₀) * starRingEnd ℂ (coeff f (q ^ (n + 1))) =
      ((((q ^ (n + 1) : ℕ) : ℂ)⁻¹ * ((q ^ (n + 1) : ℕ) : ℂ))) * (ψ (-1) * ψ (-1)) *
        (((q ^ (n + 1) : ℕ) : ℂ) ^ (1 - k) * (coeff f (q ^ (n + 1)) *
          starRingEnd ℂ (coeff f (q ^ (n + 1))))) * c₀ := by ring
  rw [this, inv_mul_cancel₀ hq0, hεε, hnormQ, hpow]
  ring

end MainPP

end ModularFormsKB.Miyake.Sec4_6
