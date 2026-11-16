import ModularFormsKB.Dimension.SturmGamma0
import TauCeti.NumberTheory.ModularForms.Norm.Cusps
import TauCeti.NumberTheory.ModularForms.Cusps.ConstantTerm

/-!
# There are no cusp forms of weight 2 on $\Gamma_0(16)$

$X_0(16)$ has genus $0$, so $S_2(\Gamma_0(16)) = 0$. This is the input to the newness of $f_{32}$
(`ModularFormsKB.Elliptic.f32Newform`): a newform of level dividing $16$ with trivial nebentypus
would be a nonzero element of $S_2(\Gamma_0(16))$.

The proof is the valence formula at general level (Tau Ceti
`TauCeti.ModularForm.valence_formula_finiteIndex`): for a nonzero weight-$k$ form on a finite-index
$\Gamma \le \mathrm{SL}_2(\mathbb Z)$ the orders at the interior points (nonnegative) and at the cusp
translation orbits add up to $k[\mathrm{SL}_2(\mathbb Z) : \Gamma]/12$, which is $2 \cdot 24/12 = 4$ for
$\Gamma_0(16)$. A cusp form has order at least $1$ at every cusp translation orbit, and $\Gamma_0(16)$
has at least $5$ of them: the cosets of $\begin{pmatrix}1&0\\c&1\end{pmatrix}$ for
$c = 0, 1, 2, 4, 8$ lie in different orbits, because the bottom-left entry of
$\begin{pmatrix}1&0\\c'&1\end{pmatrix}^{-1} T^{j} \begin{pmatrix}1&0\\c&1\end{pmatrix}$ is
$c - c' + jcc'$, never divisible by $16$ for two different such $c, c'$. So $5 \le 4$.

## Main results
- `ModularFormsKB.Elliptic.cuspForm_Gamma0_sixteen_eq_zero`: every weight-$2$ cusp form on $\Gamma_0(16)$
  vanishes.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup TauCeti.ModularForm
open scoped MatrixGroups

namespace ModularFormsKB.Elliptic

/-- The lower unipotent matrix $\begin{pmatrix}1&0\\c&1\end{pmatrix}$. -/
def lowerUnip (c : ℤ) : SL(2, ℤ) :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

/-- The cusp translation orbit of $\Gamma_0(16)$ of the coset of `lowerUnip c`. -/
noncomputable def orbitSixteen (c : ℤ) : CuspTranslationOrbit ((Gamma0 16).map (mapGL ℝ)) :=
  ⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict (lowerUnip c)) :
    𝒮ℒ ⧸ ((Gamma0 16).map (mapGL ℝ)).subgroupOf 𝒮ℒ)⟧

/-- Two integral matrices in the same cusp translation orbit differ by a power of $T$ on the left
and an element of $\Gamma_0(16)$ on the right (the unpacking of Tau Ceti's
`cuspOrbitOfSL2Z_inv_eq_of_cuspTranslationOrbit_mk_eq`). -/
lemma exists_eq_T_zpow_mul_mul_of_orbit_eq {γ γ' : SL(2, ℤ)}
    (h : (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ) :
        𝒮ℒ ⧸ ((Gamma0 16).map (mapGL ℝ)).subgroupOf 𝒮ℒ)⟧ :
          CuspTranslationOrbit ((Gamma0 16).map (mapGL ℝ))) =
      ⟦QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ')⟧) :
    ∃ j : ℤ, ∃ h₀ ∈ Gamma0 16, γ = ModularGroup.T ^ j * γ' * h₀ := by
  obtain ⟨⟨_, hg⟩, hgq⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hmk : (QuotientGroup.mk (TSL ^ j * (mapGL ℝ).rangeRestrict γ') :
      𝒮ℒ ⧸ ((Gamma0 16).map (mapGL ℝ)).subgroupOf 𝒮ℒ) =
        QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ) := by
    simpa only [Subgroup.mk_smul, MulAction.Quotient.smul_mk, smul_eq_mul] using hgq
  obtain ⟨h₀, hh₀, he⟩ :=
    Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hmk))
  have hcoe : (((TSL ^ j * (mapGL ℝ).rangeRestrict γ')⁻¹ * (mapGL ℝ).rangeRestrict γ : 𝒮ℒ) :
      GL (Fin 2) ℝ) = mapGL ℝ ((ModularGroup.T ^ j * γ')⁻¹ * γ) := by
    simp only [coe_TSL_zpow, Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, map_mul, map_inv,
      Subgroup.coe_mul, InvMemClass.coe_inv, MonoidHom.coe_rangeRestrict]
  refine ⟨j, h₀, hh₀, ?_⟩
  rw [mapGL_injective (he.trans hcoe)]
  group

/-- The bottom-left entry of $T^j \begin{pmatrix}1&0\\c'&1\end{pmatrix} h$ for the relation
`lowerUnip c = T ^ j * lowerUnip c' * h₀`: it forces $c - c' + jcc' \equiv 0 \pmod{16}$. -/
lemma sixteen_dvd_of_lowerUnip_eq {c c' j : ℤ} {h₀ : SL(2, ℤ)} (hh₀ : h₀ ∈ Gamma0 16)
    (he : lowerUnip c = ModularGroup.T ^ j * lowerUnip c' * h₀) :
    ((c - c' + j * c * c' : ℤ) : ZMod 16) = 0 := by
  have hm : (lowerUnip c : Matrix (Fin 2) (Fin 2) ℤ) =
      ((ModularGroup.T ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (lowerUnip c' : Matrix _ _ ℤ) *
        (h₀ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [he]; simp only [Matrix.SpecialLinearGroup.coe_mul]
  have e00 := congrFun (congrFun hm 0) 0
  have e10 := congrFun (congrFun hm 1) 0
  simp [lowerUnip, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
  have h10 : h₀ 1 0 = c - c' + j * c * c' := by
    linear_combination (-1 - j * c') * e10 + c' * e00
  rw [Gamma0_mem] at hh₀
  rw [← h10]
  exact_mod_cast hh₀

/-- The five values $c = 0, 1, 2, 4, 8$. -/
def sixteenCusps : Fin 5 → ℤ := ![0, 1, 2, 4, 8]

lemma orbitSixteen_injective : Function.Injective (fun i : Fin 5 ↦ orbitSixteen (sixteenCusps i)) := by
  intro a b hab
  obtain ⟨j, h₀, hh₀, he⟩ := exists_eq_T_zpow_mul_mul_of_orbit_eq hab
  have h := sixteen_dvd_of_lowerUnip_eq hh₀ he
  push_cast at h
  generalize (j : ZMod 16) = x at h
  revert x
  fin_cases a <;> fin_cases b <;> simp [sixteenCusps] <;> decide

lemma five_le_card_orbit :
    5 ≤ Fintype.card (CuspTranslationOrbit ((Gamma0 16).map (mapGL ℝ))) := by
  simpa using Fintype.card_le_of_injective _ orbitSixteen_injective

lemma card_quotient_Gamma0_sixteen :
    Nat.card (𝒮ℒ ⧸ ((Gamma0 16).map (mapGL ℝ)).subgroupOf 𝒮ℒ) = 24 := by
  rw [Subgroup.card_quotient_mapGL_eq_index, Dimension.Gamma0_index_eq_dedekindPsi,
    show (16 : ℕ) = 2 ^ 4 by norm_num, Dimension.dedekindPsi_prime_pow Nat.prime_two (by norm_num)]
  norm_num

/-- A nonzero cusp form has order at least $1$ at every cusp translation orbit. -/
lemma one_le_orderAtCuspTranslationOrbit {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsFiniteRelIndex 𝒮ℒ]
    [Γ.IsArithmetic] [Γ.HasDetOne] {k : ℤ} (f : CuspForm Γ k) (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (c : CuspTranslationOrbit Γ) : 1 ≤ orderAtCuspTranslationOrbit f c := by
  have hw : (0 : ℝ) < cuspTranslationOrbitWidth c := by
    exact_mod_cast cuspTranslationOrbitWidth_pos c
  have hne : qExpansion (cuspTranslationOrbitWidth c : ℝ) (SlashInvariantForm.quotientFunc f c.out)
      ≠ 0 :=
    mt (UpperHalfPlane.qExpansion_eq_zero_iff hw (periodic_quotientFunc_out f c)
      (TauCeti.SlashInvariantForm.mdifferentiable_quotientFunc f _)
      (TauCeti.SlashInvariantForm.isBoundedAtImInfty_quotientFunc f _)).mp
      ((TauCeti.SlashInvariantForm.quotientFunc_eq_zero_iff _).not.2 hf)
  have hmem : (f : ModularForm Γ k) ∈ cuspFormSubmodule Γ k :=
    (mem_cuspFormSubmodule_iff).2 ⟨f, rfl⟩
  have h0 := (mem_cuspFormSubmodule_iff_constantTermAtCuspTranslationOrbit_eq_zero.mp hmem) c
  rw [constantTermAtCuspTranslationOrbit_eq_qExpansion_coeff_zero] at h0
  have hord : (qExpansion (cuspTranslationOrbitWidth c : ℝ)
      (SlashInvariantForm.quotientFunc f c.out)).order ≠ 0 := by
    rw [Ne, ← ne_eq, PowerSeries.order_ne_zero_iff_constCoeff_eq_zero,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h0
  have htop : (qExpansion (cuspTranslationOrbitWidth c : ℝ)
      (SlashInvariantForm.quotientFunc f c.out)).order ≠ ⊤ := by
    rwa [Ne, PowerSeries.order_eq_top]
  rw [orderAtCuspTranslationOrbit, TauCeti.qExpansionOrderAtCusp_def]
  have : 1 ≤ (qExpansion (cuspTranslationOrbitWidth c : ℝ)
      (SlashInvariantForm.quotientFunc f c.out)).order.toNat := by
    rcases ENat.ne_top_iff_exists.mp htop with ⟨m, hm⟩
    rw [← hm] at hord ⊢
    simp only [ENat.toNat_natCast]
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hord)
  exact_mod_cast this

/-- **$S_2(\Gamma_0(16)) = 0$**: every cusp form of weight $2$ on $\Gamma_0(16)$ vanishes
($X_0(16)$ has genus $0$). -/
theorem cuspForm_Gamma0_sixteen_eq_zero (f : CuspForm ((Gamma0 16).map (mapGL ℝ)) 2) : f = 0 := by
  by_contra hf
  have hf' : (⇑f : ℍ → ℂ) ≠ 0 := fun h ↦ hf (DFunLike.coe_injective (by simpa using h))
  have hval := valence_formula_finiteIndex (Γ := Gamma0 16) f hf'
  have hint : (0 : ℚ) ≤ ∑ᶠ o : MulAction.orbitRel.Quotient
      ((Gamma0 16 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ℍ,
        weightedOrderOfVanishingOnSubgroupOrbit f o :=
    finsum_nonneg (weightedOrderOfVanishingOnSubgroupOrbit_nonneg f)
  have hcusp : (5 : ℚ) ≤ ∑ c : CuspTranslationOrbit
      ((Gamma0 16 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
        (orderAtCuspTranslationOrbit f c : ℚ) := by
    calc (5 : ℚ) ≤ Fintype.card (CuspTranslationOrbit ((Gamma0 16).map (mapGL ℝ))) := by
          exact_mod_cast five_le_card_orbit
      _ = ∑ _c : CuspTranslationOrbit ((Gamma0 16).map (mapGL ℝ)), (1 : ℚ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun c _ ↦ by
          exact_mod_cast one_le_orderAtCuspTranslationOrbit f hf' c
  have hcard : (Nat.card (𝒮ℒ ⧸ ((Gamma0 16 : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) : ℚ) = 24 := by
    exact_mod_cast card_quotient_Gamma0_sixteen
  rw [hcard] at hval
  push_cast at hval
  linarith

end ModularFormsKB.Elliptic
