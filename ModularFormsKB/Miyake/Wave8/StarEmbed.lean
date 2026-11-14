import ModularFormsKB.Miyake.Wave8.GeneralAdjoint
import ModularFormsKB.Miyake.Wave6.LevelChange
import ModularFormsKB.Miyake.Wave4.HeckeCoefficients
import TauCeti.NumberTheory.ModularForms.SturmBound
import TauCeti.NumberTheory.ModularForms.Degeneracy

/-!
# Miyake, Theorem 4.5.10 for `T*(n)` with `n ∣ N^∞`: an erratum

Miyake, *Modular Forms* (Springer 1989), Theorem 4.5.10, p. 143: for `N ∣ M` and `n ∣ N^∞` or
`(n, M) = 1`, the natural embedding `𝒢_k(N, χ) → 𝒢_k(M, χ)` commutes with `T(n)` **and** with
`T*(n)`. For `T(n)` this is wave 6's `Wave6.heckeT_embed`; for `T*(n)` with `(n, M) = 1` it is
wave 7's `Wave7.heckeTStarN_embed`.

For `T*(n)` with `n ∣ N^∞`, `n > 1`, the statement is **false** as soon as the cusp space is
nonzero. Take a prime `p ∣ N` and `M` with `N p ∣ M`. Every representative `a = δ γ` of
`Γ₀(M) \ Γ₀(M) δ Γ₀(M)`, `δ = diag(p, 1)`, with `γ ∈ Γ₁(M)` (Theorem 2.7.6 with
`Γ₁(M)`, `isCosetReps_of_gamma1_of_eq`) satisfies `δ γ δ⁻¹ ∈ Γ₁(N)` and `d_a ≡ 1 (mod M)`, so for
`f` of level `N` every term of `f | T*(p)` at level `M` is `f ∣ δ`:

  `(ι f) | ^M T*(p) = r · f ∣_k diag(p, 1) = r p^{k-1} f(p z)`, `r ≥ 1`
  (`coe_heckeTStar_embed_eq_smul`).

If the diagram commuted, `f ↦ r p^{k-1} f(pz)` would be the endomorphism `^N T*(p)` of the nonzero
finite-dimensional space `𝒮_k(N, χ)`; but comparing the first nonzero Fourier coefficients shows
that this map has no eigenvector (`not_forall_heckeTStarN_embed`). Since `𝒮_k(N, χ) ⊂ 𝒢_k(N, χ)`
and the embedding respects cusp forms, the statement fails on `𝒢_k` as well.

(The correct statement for `n ∣ N^∞` concerns `T(n)` only; `T*(p)`, `p ∣ N`, is the adjoint of
`T(p) = U_p`, which does not preserve the image of the embedding.)
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup DoubleCoset
  HeckeRing.GL2 HeckeRing.GLn
open scoped MatrixGroups ModularForm Pointwise

noncomputable section

namespace ModularFormsKB.Miyake.Wave8

open ModularFormsKB.Miyake.Wave4 ModularFormsKB.Miyake.Wave7 TauCeti

attribute [local instance] Fintype.ofFinite

variable {N : ℕ} [NeZero N]

/-- `δ γ δ⁻¹ ∈ Γ₁(N)` for `δ = diag(p, 1)` and `γ ∈ Γ₁(M)`, `N p ∣ M`. -/
theorem exists_conj_natDiagGL_swap_mem_gamma1 {M p : ℕ} (hp : 0 < p) (hNp : N * p ∣ M)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 M) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma1 N ∧
      natDiagGL 2 ![p, 1] * mapGL ℚ γ = mapGL ℚ γ' * natDiagGL 2 ![p, 1] := by
  obtain ⟨h00, h11, h10⟩ := (Gamma1_mem M γ).mp hγ
  have h10' : ((N * p : ℕ) : ℤ) ∣ γ 1 0 :=
    (Int.natCast_dvd_natCast.mpr hNp).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10)
  obtain ⟨j, hj⟩ := h10'
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 :=
    Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
  let γ' : SL(2, ℤ) := ⟨!![γ 0 0, p * γ 0 1; N * j, γ 1 1], by
    rw [Matrix.det_fin_two_of]; rw [hj] at hdet; push_cast at hdet; linear_combination hdet⟩
  have hNM : (N : ℤ) ∣ M := Int.natCast_dvd_natCast.mpr ((dvd_mul_right N p).trans hNp)
  have hcast : ∀ x : ℤ, (x : ZMod M) = 1 → (x : ZMod N) = 1 := fun x hx ↦ by
    have h1 : ((x : ℤ) : ZMod M) = ((1 : ℤ) : ZMod M) := by simpa using hx
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1
    have h2 : ((x : ℤ) : ZMod N) = ((1 : ℤ) : ZMod N) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (hNM.trans h1)
    simpa using h2
  refine ⟨γ', (Gamma1_mem N γ').mpr ⟨hcast _ h00, hcast _ h11, ?_⟩, Units.ext ?_⟩
  · show ((N * j : ℤ) : ZMod N) = 0
    push_cast; simp
  · have hD : ((natDiagGL 2 ![p, 1] : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
        !![(p : ℚ), 0; 0, 1] := by
      rw [natDiagGL_coe 2 ![p, 1] (fun i ↦ by fin_cases i <;> simp [hp])]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [Units.val_mul, Units.val_mul, hD, coe_mapGL_int_rat_fin_two, coe_mapGL_int_rat_fin_two,
      Matrix.mul_fin_two, Matrix.mul_fin_two]
    simp only [γ', Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    congrm !![?_, ?_; ?_, ?_]
    all_goals (try rw [hj])
    all_goals push_cast
    all_goals ring

/-- **The computation behind the erratum**: for a prime `p ∣ N`, `N p ∣ M` and `f ∈ 𝒮_k(N, χ)`,
`(ι f) | ^M T*(p, 1) = r · f ∣_k diag(p, 1)` with `r ≥ 1` the degree of the double coset. -/
theorem coe_heckeTStar_embed_eq_smul {M : ℕ} [NeZero M] (k : ℤ) (χ : DirichletCharacter ℂ N)
    (h : N ∣ M) {p : ℕ} (hp : 0 < p) (hNp : N * p ∣ M) (f : cuspSpace k χ) :
    ∃ r : ℕ, 0 < r ∧
      ⇑((heckeTStar k (DirichletCharacter.changeLevel h χ) p 1 (Wave6.embed k χ h f) :
          cuspSpace (N := M) k _) : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) =
        (r : ℂ) • (⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] natDiagGL 2 ![p, 1]) := by
  classical
  have := finite_decompQuotient_swap (N := M) (l := 1) (m := p) one_pos hp (Nat.coprime_one_left M)
  set δ : GL (Fin 2) ℚ := natDiagGL 2 ![p, 1]
  have hA := coe_natDiagGL_eq_map hp one_pos
  have hA10 : (M : ℤ) ∣ (!![(p : ℤ), 0; 0, ((1 : ℕ) : ℤ)]) 1 0 := by simp
  have hlu : IsUnit (((!![(p : ℤ), 0; 0, ((1 : ℕ) : ℤ)]) 1 1 : ℤ) : ZMod M) := by simp
  have hreps : IsCosetReps M δ
      (fun v : DecompQuotient (gamma1Q M) (gamma1Q M) δ⁻¹ ↦ δ * ((v.out : GL (Fin 2) ℚ))⁻¹) :=
    isCosetReps_of_gamma1_of_eq hA hA10 (Or.inr hlu)
      (le_antisymm (doubleCoset_natDiagGL_swap_gamma0_subset (N := M) one_pos (one_dvd p) hp)
        (doubleCoset_mono le_rfl (gamma1Q_le_gamma0Q (N := M))))
      (doubleCoset_eq_iUnion_rightCosets _ _ _) (op_mul_out_inv_smul_injective _ _ _)
  refine ⟨Fintype.card (DecompQuotient (gamma1Q M) (gamma1Q M) δ⁻¹), Fintype.card_pos, ?_⟩
  rw [coe_heckeTStar k _ one_pos hp (Nat.coprime_one_left M) hreps, starSlashSum,
    ← Finset.card_univ, Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.mp (v.out.2)
  have hgi : g⁻¹ ∈ Gamma1 M := inv_mem hg
  obtain ⟨γ', hγ', hconj⟩ := exists_conj_natDiagGL_swap_mem_gamma1 hp hNp hgi
  have hrep : δ * ((v.out : GL (Fin 2) ℚ))⁻¹ = mapGL ℚ γ' * δ := by
    rw [← hge, ← map_inv, hconj]
  -- the weight: the lower-right entry of `δ g⁻¹` is `(g⁻¹)₁₁ ≡ 1 (mod M)`
  have hw : starWeight (DirichletCharacter.changeLevel h χ) (δ * ((v.out : GL (Fin 2) ℚ))⁻¹) = 1 := by
    obtain ⟨-, h11, -⟩ := (Gamma1_mem M g⁻¹).mp hgi
    have h11' : (((δ * ((v.out : GL (Fin 2) ℚ))⁻¹ : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ) 1 1) = (((g⁻¹ : SL(2, ℤ)) 1 1 : ℤ) : ℚ) := by
      rw [← hge, ← map_inv, Units.val_mul, coe_natDiagGL_eq_map hp one_pos,
        coe_mapGL_int_rat_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      simp
    rw [starWeight, h11', Rat.num_intCast, h11, map_one, map_one]
  rw [hw, one_smul, hrep, SlashAction.slash_mul]
  -- `f` is invariant under `γ' ∈ Γ₁(N)`
  have hf := coe_mem_functionCharSpace f
  have hinv : ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] (mapGL ℚ γ' : GL (Fin 2) ℚ) =
      ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    rw [ModularForm.rat_slash, Matrix.SpecialLinearGroup.map_mapGL]
    exact slash_mapGL_eq_self_of_mem_functionCharSpace_of_mem_Gamma1 hf hγ'
  rw [show ⇑((Wave6.embed k χ h f : cuspSpace (N := M) k _) :
      CuspForm ((Gamma1 M).map (mapGL ℝ)) k) = ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    from rfl, hinv]

/-- `f ∣_k diag(p, 1) = p^{k-1} f(pz)`, in terms of wave 6's `raise`. -/
theorem slash_natDiagGL_swap_eq_raise (k : ℤ) (χ : DirichletCharacter ℂ N) (p : ℕ) [NeZero p]
    (f : cuspSpace k χ) :
    ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] natDiagGL 2 ![p, 1] =
      ((p : ℂ) ^ (k - 1)) • ⇑((Wave6.raise k χ p f : cuspSpace (N := p * N) k _) :
        CuspForm ((Gamma1 (p * N)).map (mapGL ℝ)) k) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hδ : natDiagGL 2 ![p, 1] = scaleGLRat p := by
    apply Units.ext
    rw [natDiagGL_coe 2 ![p, 1] (fun i ↦ by fin_cases i <;> simp [hp]), scaleGLRat, diagGL_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hd : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  rw [hδ, ModularForm.rat_slash, map_ratCast_scaleGLRat]
  change _ = _ • ⇑(TauCeti.CuspForm.levelRaise p (TauCeti.Gamma1_map_le_conjAct_scaleGL N p)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
  rw [TauCeti.CuspForm.coe_levelRaise, smul_smul, ← zpow_add₀ hd]
  simp

/-- **Erratum to Miyake, Theorem 4.5.10** (`T*(n)`, `n ∣ N^∞`): for a prime `p ∣ N`, a multiple
`M` of `N p`, and `𝒮_k(N, χ) ≠ 0`, the natural embedding `𝒮_k(N, χ) → 𝒮_k(M, χ)` does **not**
commute with `T*(p)`. (So it does not on `𝒢_k(N, χ) ⊃ 𝒮_k(N, χ)` either.) -/
@[kb "miyake1989" "Theorem 4.5.10, p. 143 (erratum: T*(n), n | N^∞)"]
theorem not_forall_heckeTStarN_embed {M : ℕ} [NeZero M] (k : ℤ) (χ : DirichletCharacter ℂ N)
    (h : N ∣ M) {p : ℕ} (hp : p.Prime) (_hpN : p ∣ N) (hNp : N * p ∣ M)
    [Nontrivial (cuspSpace k χ)] :
    ¬ ∀ f : cuspSpace k χ,
      heckeTStarN k (DirichletCharacter.changeLevel h χ) p (Wave6.embed k χ h f) =
        Wave6.embed k χ h (heckeTStarN k χ p f) := by
  intro H
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hT : ∀ {L : ℕ} [NeZero L] (ψ : DirichletCharacter ℂ L),
      heckeTStarN k ψ p = heckeTStar k ψ p 1 := by
    intro L _ ψ
    have hdiv : (p.divisors.filter fun l ↦ l ∣ p / l) = {1} := by
      rw [Nat.Prime.divisors hp, Finset.filter_insert, Finset.filter_singleton]
      have h1 : ¬ p ∣ p / p := by
        rw [Nat.div_self hp.pos]; exact hp.not_dvd_one
      simp [h1]
    rw [heckeTStarN, hdiv, Finset.sum_singleton, Nat.div_one]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (heckeTStar k χ p 1)
  obtain ⟨f, hf⟩ := hc.exists_hasEigenvector
  have hTf := hf.apply_eq_smul
  obtain ⟨r, hr, hfun⟩ := coe_heckeTStar_embed_eq_smul k χ h hp.pos hNp f
  have H' := H f
  rw [hT, hT, hTf] at H'
  rw [H', slash_natDiagGL_swap_eq_raise, smul_smul] at hfun
  set C : ℂ := (r : ℂ) * (p : ℂ) ^ (k - 1)
  have hC : C ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hr.ne')
    (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero))
  -- the coefficient relation `c a(m) = C a(m / p) [p ∣ m]`
  have hrel : ∀ m, c * coeff f m = C * (if p ∣ m then coeff f (m / p) else 0) := by
    intro m
    have e : coeff (Wave6.embed k χ h (c • f)) m = coeff (C • Wave6.raise k χ p f) m := by
      show (qExpansion 1 _).coeff m = (qExpansion 1 _).coeff m
      rw [hfun]
      rfl
    rw [Wave6.coeff_embed, coeff_smul, coeff_smul, Wave6.coeff_raise] at e
    exact e
  apply hf.2
  refine ext_of_coeff fun m ↦ ?_
  rw [coeff_zero_elem]
  by_cases hc0 : c = 0
  · -- then `C a(j) = 0` for every `j`
    have := hrel (p * m)
    rw [hc0, zero_mul, if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m hp.pos] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hC
  · induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact coeff_zero_eq f
      · have := hrel m
        split_ifs at this with hpm
        · rw [ih (m / p) (Nat.div_lt_self hm hp.one_lt), mul_zero] at this
          exact (mul_eq_zero.mp this).resolve_left hc0
        · rw [mul_zero] at this
          exact (mul_eq_zero.mp this).resolve_left hc0

end ModularFormsKB.Miyake.Wave8
