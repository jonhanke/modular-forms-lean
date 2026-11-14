import ModularFormsKB.Miyake.Wave9.EtaOperator
import TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.AtkinLehner

/-!
# Miyake §4.6: Theorem 4.6.16 (4) and Corollary 4.6.18 (2)

Miyake, *Modular Forms* (Springer 1989), Theorem 4.6.16 (4), pp. 168–169, and Corollary 4.6.18
(2), p. 173. Notation as in `ModularFormsKB.Miyake.Wave9.EtaOperator` (an exact divisor `Q ∥ N`,
`χ = ψ φ`, an `η`-matrix for `Q`, Mathlib's slash).

* `exists_isPrimitive_eta` (Theorem 4.6.16 (4), in part): if `f = Σ a_n e(nz)` is a primitive
  form of `𝒮_k^0(N, ψ φ)`, then `f | η = c g_q` with `c ≠ 0` and `g_q = Σ b_n e(nz)` a primitive
  form of `𝒮_k^0(N, conj ψ · φ)`, and `b_p = conj ψ(p) a_p` for every prime `p ∤ N`. Miyake also
  states `b_p = conj χ_q(p) a_p` for `p ∣ N/N_q` and `b_q = χ'_q(q) conj(a_q)`; those need the
  commutation (4.6.22)–(4.6.23) of `η_q` with `T(n)` for `n` not prime to `N`, and are proved in
  `EtaHecke.lean` (`exists_isPrimitive_eta_all`).
* `eta_eq_neg_conj_coeff_smul` (Corollary 4.6.18 (2)): if `N_q = q` and `m_q = 1` (that is,
  `q ∥ N` and `χ_q = 1`), a primitive form `f` satisfies `f | η_q = -conj(a_q) f` (Miyake's
  `c = -q^{1-k/2} conj(a_q)` in his normalization of the slash) and `conj(a_q) = conj χ'_q(q) a_q`.

Inputs from Tau Ceti: the Atkin–Lehner transport of newforms and its good-prime coefficients
(`Newform.atkinLehnerTransform`, `Newform.qExpansion_coeff_prime_atkinLehnerTransform_of_split`),
and Li's bad-prime eigenvalue at `q ∥ N` (`Newform.atkinLehnerOperatorGamma1Cusp_eq_neg_qExpansion_coeff_smul`,
`Newform.qExpansion_coeff_prime_sq_of_isExactDivisor`), proved there for the descent matrix
`diag(1, q) γ_q`; it is moved to Miyake's `η_q` by the diamond label computed in
`natCast_mul_apply_one_one_of_eq_mul`.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm TauCeti.ExactDivisor

noncomputable section

namespace ModularFormsKB.Miyake.Wave9

open ModularFormsKB.Miyake.Wave4 ModularFormsKB.Miyake.Wave7

variable {N Q : ℕ} [NeZero N] {M : Matrix (Fin 2) (Fin 2) ℤ}

/-- **Miyake, Theorem 4.6.16 (4)**, for the primes `p ∤ N`: if `f` is a primitive form of
`𝒮_k^0(N, ψ φ)`, then `f | η = c g` with `c ≠ 0` and `g = Σ b_n e(nz)` a primitive form of
`𝒮_k^0(N, conj ψ · φ)`, and `b_p = conj ψ(p) a_p` for every prime `p ∤ N`. -/
@[kb "miyake1989" "Theorem 4.6.16 (4), p. 168 (primes p ∤ N)"]
theorem exists_isPrimitive_eta (k : ℤ) (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M)
    (ψ : DirichletCharacter ℂ Q) (φ : DirichletCharacter ℂ (N / Q))
    {f : cuspSpace k (splitChar hQ ψ φ)} (hf : IsPrimitive f) :
    ∃ g : cuspSpace k (splitChar hQ ψ⁻¹ φ), IsPrimitive g ∧
      (∃ c : ℂ, c ≠ 0 ∧ ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] etaGL hQ hM =
        c • ⇑(g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) ∧
      ∀ p : ℕ, p.Prime → p.Coprime N → coeff g p = ψ⁻¹ (p : ZMod Q) * coeff f p := by
  obtain ⟨F, hχ, hF⟩ := (isPrimitive_iff_exists_newform f).mp hf
  have hW := hM.isAtkinLehnerMatrix hQ
  have hχ' : F.χ = ψ.toUnitHom.comp (ZMod.unitsMap hQ.dvd) *
      φ.toUnitHom.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hQ.dvd)) := by
    rw [hχ, toUnitHom_splitChar]
  set G := F.atkinLehnerTransform hQ
  have hGχ : G.χ = (splitChar hQ ψ⁻¹ φ).toUnitHom := by
    rw [HeckeRing.GL2.Newform.χ_atkinLehnerTransform, hχ', toUnitHom_splitChar,
      toUnitHom_inv_eq_inv]
    exact TauCeti.Nat.IsExactDivisor.comp_unitsInvPart hQ ψ.toUnitHom φ.toUnitHom
  have hmem : G.toCuspForm ∈ cuspSpace k (splitChar hQ ψ⁻¹ φ) := by
    change _ ∈ TauCeti.cuspFormCharSpace k _
    rw [← hGχ]
    exact G.mem_charSpace
  refine ⟨⟨_, hmem⟩, (isPrimitive_iff_exists_newform _).mpr ⟨G, hGχ, rfl⟩, ?_, ?_⟩
  · set c := (qExpansion 1 (TauCeti.atkinLehnerOperatorGamma1Cusp hQ.pos hQ.dvd hW k
      F.toCuspForm)).coeff 1
    have hc : c ≠ 0 := F.qExpansion_coeff_one_atkinLehnerOperatorGamma1Cusp_ne_zero hQ.pos hQ.dvd hW
    refine ⟨c, hc, ?_⟩
    have hG := F.toCuspForm_atkinLehnerTransform_of_isAtkinLehnerMatrix hQ hW
    show _ = c • ⇑G.toCuspForm
    rw [hG, FunLike.coe_smul, smul_smul, mul_inv_cancel₀ hc, one_smul,
      TauCeti.coe_atkinLehnerOperatorGamma1Cusp, hF]
  · intro p hp hpN
    have h := F.qExpansion_coeff_prime_atkinLehnerTransform_of_split hQ ψ.toUnitHom φ.toUnitHom
      hχ' hp hpN
    show (qExpansion 1 G.toCuspForm).coeff p = _
    rw [h, hF, MulChar.inv_apply_eq_inv', MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime]

/-- Two Atkin–Lehner matrices for `Q` with `W₁ = γ W₂`: the lower-right entry of `γ` satisfies
`Q γ₁₁ = (W₁)₁₁ (W₂)₀₀ - (W₁)₁₀ (W₂)₀₁`. -/
theorem natCast_mul_apply_one_one_of_eq_mul {W₁ W₂ : Matrix (Fin 2) (Fin 2) ℤ}
    (h₂ : TauCeti.IsAtkinLehnerMatrix N Q W₂) {γ : SL(2, ℤ)}
    (h : W₁ = (γ : Matrix (Fin 2) (Fin 2) ℤ) * W₂) :
    (Q : ℤ) * γ 1 1 = W₁ 1 1 * W₂ 0 0 - W₁ 1 0 * W₂ 0 1 := by
  have hdet := h₂.det_eq
  rw [Matrix.det_fin_two] at hdet
  rw [h]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (-(γ 1 1)) * hdet

/-- **Miyake, Corollary 4.6.18 (2)**: if `N_q = q` and `m_q = 1` (here `q ∥ N` and `χ = χ_q χ'_q`
with `χ_q = 1`), a primitive form `f = Σ a_n e(nz)` of `𝒮_k^0(N, χ)` satisfies
`f | η_q = -conj(a_q) f` (Miyake's `c = -q^{1-k/2} conj(a_q)`, in his normalization of the slash),
and `conj(a_q) = conj χ'_q(q) a_q`. -/
@[kb "miyake1989" "Corollary 4.6.18 (2), p. 173"]
theorem eta_eq_neg_conj_coeff_smul (k : ℤ) {q : ℕ} (hq : q.Prime) (hQ : q ∥ N)
    (hM : IsEtaMatrix N q M) (φ : DirichletCharacter ℂ (N / q))
    {f : cuspSpace k (splitChar hQ 1 φ)} (hf : IsPrimitive f) :
    ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] etaGL hQ hM =
        -(starRingEnd ℂ (coeff f q)) • ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∧
      starRingEnd ℂ (coeff f q) = φ⁻¹ (q : ZMod (N / q)) * coeff f q := by
  obtain ⟨F, hχ, hF⟩ := (isPrimitive_iff_exists_newform f).mp hf
  have hone : (1 : DirichletCharacter ℂ q).toUnitHom = 1 := by
    ext u; simp
  have hχ0 : F.χ = φ.toUnitHom.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hQ.dvd)) := by
    rw [hχ, toUnitHom_splitChar, hone, MonoidHom.one_comp, one_mul]
  have hpsq := hQ.not_sq_dvd hq.one_lt.ne'
  have hWd := TauCeti.isAtkinLehnerMatrix_descendExtra hq hQ.dvd hpsq
  have hdesc := F.atkinLehnerOperatorGamma1Cusp_eq_neg_qExpansion_coeff_smul hq hQ.dvd hpsq hχ0
  have hsq := F.qExpansion_coeff_prime_sq_of_isExactDivisor hq hQ hχ0
  set a := coeff f q with ha_def
  have ha : (qExpansion 1 F.toCuspForm).coeff q = a := by rw [hF]
  rw [ha] at hdesc hsq
  have hφq : ((φ.toUnitHom (ZMod.unitOfCoprime q hQ.coprime) : ℂˣ) : ℂ) = φ (q : ZMod (N / q)) := by
    rw [MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime]
  rw [hφq] at hsq
  -- `conj(a_q) = conj φ(q) a_q`
  have hconj : starRingEnd ℂ a = φ⁻¹ (q : ZMod (N / q)) * a := by
    have hu : IsUnit (q : ZMod (N / q)) := (ZMod.unitOfCoprime q hQ.coprime).isUnit
    have hw0 : φ (q : ZMod (N / q)) ≠ 0 := (hu.map φ).ne_zero
    have hc0 : (q : ℂ) ^ (k - 2) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hq.ne_zero)
    have ha0 : a ≠ 0 := by
      intro h0; rw [h0, zero_pow two_ne_zero] at hsq; exact (mul_ne_zero hw0 hc0) hsq.symm
    have hnw : ‖φ (q : ZMod (N / q))‖ = 1 := by
      rw [← ZMod.coe_unitOfCoprime q hQ.coprime]; exact φ.unit_norm_eq_one _
    have hnc : (((‖(q : ℂ) ^ (k - 2)‖ : ℝ)) : ℂ) = (q : ℂ) ^ (k - 2) := by
      rw [norm_zpow, Complex.norm_natCast, Complex.ofReal_zpow, Complex.ofReal_natCast]
    have hmul : starRingEnd ℂ a * a = (q : ℂ) ^ (k - 2) := by
      rw [Complex.conj_mul', ← Complex.ofReal_pow, ← norm_pow, hsq, norm_mul, hnw, one_mul, hnc]
    rw [MulChar.inv_apply_eq_inv']
    field_simp
    have : starRingEnd ℂ a * a * φ (q : ZMod (N / q)) = a * a := by
      rw [hmul, ← sq, hsq, mul_comm]
    exact mul_right_cancel₀ ha0 (by linear_combination this)
  refine ⟨?_, hconj⟩
  obtain ⟨γ, hγ, hmul⟩ := hWd.exists_mem_Gamma0_eq_mul_left hq.ne_zero hQ.dvd
    (hM.isAtkinLehnerMatrix hQ)
  -- the label of `γ`: `q γ₁₁ ≡ 1 mod N/q`
  have hlab : (q : ZMod (N / q)) * ((γ 1 1 : ℤ) : ZMod (N / q)) = 1 := by
    have hid := natCast_mul_apply_one_one_of_eq_mul hWd hmul
    have h11 := hM.intCast_apply_one_one
    have h10 : ((M 1 0 : ℤ) : ZMod (N / q)) = 0 := by
      obtain ⟨c, hc⟩ := (hM.isAtkinLehnerMatrix hQ).dvd_apply_one_zero
      rw [hc]
      have hN : (N : ℤ) = ((N / q : ℕ) : ℤ) * q := by exact_mod_cast (Nat.div_mul_cancel hQ.dvd).symm
      rw [hN, Int.cast_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_mul]
    have h00 : (((!![1, 0; 0, (q : ℤ)] * (TauCeti.descendExtraGamma q N : Matrix (Fin 2) (Fin 2) ℤ))
        0 0 : ℤ) : ZMod (N / q)) = 1 := by
      have := congr_fun₂ (congrArg Subtype.val
        (TauCeti.descendExtraGamma_map_intCast_zmod_div_eq_one hq hQ.dvd hpsq)) 0 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have := congrArg (Int.cast : ℤ → ZMod (N / q)) hid
    push_cast at this
    rw [this, h11, h10, h00]; ring
  -- move Tau Ceti's eigenvalue from the descent matrix to `η_q`
  have hop := TauCeti.atkinLehnerOperatorGamma1Cusp_mul_left_of_mem_cuspFormCharSpace hq.pos hQ.dvd
    hWd hγ F.mem_charSpace
  rw [hdesc] at hop
  have hfun := congrArg (fun G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k ↦ ⇑G) hop
  simp only [TauCeti.coe_atkinLehnerOperatorGamma1Cusp, FunLike.coe_smul, hF] at hfun
  subst hmul
  rw [hfun, hχ, splitChar_label_one hQ φ hγ hlab, smul_smul, hconj]
  simp [_root_.neg_smul, mul_comm]

end ModularFormsKB.Miyake.Wave9
