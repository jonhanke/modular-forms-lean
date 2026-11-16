import ModularFormsKB.Elliptic.HasNewform
import ModularFormsKB.Elliptic.HasseCoeff
import ModularFormsKB.Miyake.Sec4_3.Twist
import ModularFormsKB.Miyake.Sec4_3.ModularQ
import TauCeti.NumberTheory.ModularForms.LFunction.Sign

/-!
# The newform of an elliptic curve in Miyake's language

If $E$ has the newform $f$ of level $N$ (`HasNewform E N f`), then, with $a = a_E$ the coefficients of $L(E, s)$
(`coeffE E`):
- `HasNewform.coe_eq_qSeries`: $f(\tau) = \sum_n a_n e^{2\pi i n\tau}$ (`Miyake.qSeries`);
- `HasNewform.isCuspFormChar`: $\sum a_n q^n \in S_2(N, 1)$ in Miyake's sense (`Miyake.IsCuspFormChar`), the
  hypothesis of Miyake's Theorems 4.3.11, 4.3.12;
- `HasNewform.fricke_eq`: $f|_2\omega_N = \varepsilon_N(f) f$ in Miyake's normalization, $\varepsilon_N(f)$ Tau Ceti's
  Fricke sign `Newform.frickeSign`. In weight $2$ Miyake's slash
  $(\sqrt N z)^{-2} f(-1/(Nz))$ and Tau Ceti's normalized Fricke operator $(\sqrt N)^{2-k}\,f|_k W_N$ (Mathlib slash,
  $\det^{k-1}$) agree.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Complex
open scoped MatrixGroups
open Matrix.SpecialLinearGroup (mapGL)

namespace ModularFormsKB.Elliptic

open HeckeRing.GL2

variable {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N] {f : Newform N 2}

/-- The `q`-expansion of a cusp form on `Γ₁(N)` is its `Miyake.qSeries`, with coefficients of polynomial
growth. -/
theorem cuspForm_qSeries_coeff {k : ℤ} (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    Miyake.CoeffGrowth (fun n ↦ (qExpansion 1 F).coeff n) ∧
      ∀ τ : ℍ, F τ = Miyake.qSeries (fun n ↦ (qExpansion 1 F).coeff n) τ := by
  have hΓ : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _
  have hg : Miyake.CoeffGrowth (fun n ↦ (qExpansion 1 F).coeff n) := by
    have := CuspFormClass.qExpansion_isBigO F
    rw [strictWidthInfty_Gamma1] at this
    exact ⟨_, this⟩
  refine ⟨hg, fun τ ↦ ?_⟩
  have : Fact (IsCusp OnePoint.infty (Gamma1 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  have h := UpperHalfPlane.hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex F hΓ) (ModularFormClass.holo F)
    (ModularFormClass.bdd_at_infty F) τ
  have e : (fun n : ℕ ↦ (qExpansion 1 F).coeff n • Function.Periodic.qParam 1 (τ : ℂ) ^ n) =
      fun n : ℕ ↦ (qExpansion 1 F).coeff n * Complex.exp (2 * Real.pi * Complex.I * n * τ) := by
    funext n
    rw [Function.Periodic.qParam, ← Complex.exp_nat_mul, smul_eq_mul]
    congr 2
    push_cast
    ring
  rw [e] at h
  exact h.tsum_eq.symm

private theorem HasNewform.coeffE_eq (hf : HasNewform E N f) :
    coeffE E = fun n ↦ (qExpansion 1 f.toCuspForm).coeff n :=
  funext fun n ↦ (hf.coeff_eq n).symm

/-- The newform of $E$ is the $q$-series of the coefficients of $L(E, s)$. -/
theorem HasNewform.coe_eq_qSeries (hf : HasNewform E N f) (τ : ℍ) :
    f.toCuspForm τ = Miyake.qSeries (coeffE E) τ := by
  rw [hf.coeffE_eq]
  exact (cuspForm_qSeries_coeff f.toCuspForm).2 τ

/-- The newform of $E$ lies in $S_2(N, 1)$ in Miyake's sense. -/
theorem HasNewform.isCuspFormChar (hf : HasNewform E N f) :
    Miyake.IsCuspFormChar 2 N 1 (fun τ : ℍ ↦ Miyake.qSeries (coeffE E) τ) := by
  have hF : ⇑f.toCuspForm = fun τ : ℍ ↦ Miyake.qSeries (coeffE E) τ :=
    funext hf.coe_eq_qSeries
  refine ⟨⟨f.toCuspForm, hF⟩, fun γ hγ ↦ ?_⟩
  have hmem : f.toCuspForm ∈ TauCeti.cuspFormCharSpace 2 (1 : (ZMod N)ˣ →* ℂˣ) := by
    have := f.mem_charSpace
    rwa [hf.χ_eq_one] at this
  have hinv := (TauCeti.mem_cuspFormCharSpace_one_iff _).1 hmem (mapGL ℝ γ)
    (Subgroup.mem_map_of_mem _ hγ)
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hz : ((γ 0 0 : ℤ) : ZMod N) * (γ 1 1 : ℤ) = 1 := by
    have h1 : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod N) = 1 := by
      rw [hdet]; simp
    have h2 : ((γ 1 0 : ℤ) : ZMod N) = 0 := (Gamma0_mem).1 hγ
    push_cast at h1
    rw [h2] at h1
    simpa using h1
  have hu : IsUnit ((γ 1 1 : ℤ) : ZMod N) := IsUnit.of_mul_eq_one ((γ 0 0 : ℤ) : ZMod N) (by rwa [mul_comm] at hz)
  rw [MulChar.one_apply hu, one_smul, ← hF, ModularForm.SL_slash]
  exact hinv

/-- **The Fricke relation of the newform of $E$** in Miyake's normalization: $f|_2\omega_N = \varepsilon_N(f)\,f$. -/
theorem HasNewform.fricke_eq (hf : HasNewform E N f) (z : ℂ) (hz : 0 < z.im) :
    Miyake.fricke 2 N (Miyake.qSeries (coeffE E)) z =
      f.frickeSign hf.χ_eq_one * Miyake.qSeries (coeffE E) z := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hF : ⇑f.toCuspForm = fun τ : ℍ ↦ Miyake.qSeries (coeffE E) τ :=
    funext hf.coe_eq_qSeries
  have h1 := congrFun (Miyake.fricke_eq_smul_slash (k := 2) hN (Miyake.qSeries (coeffE E)))
    ⟨z, hz⟩
  have hW := congrArg (fun g : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2 ↦ (⇑g : ℍ → ℂ))
    (f.normalizedFrickeOperatorCusp_eq_frickeSign_smul hf.χ_eq_one)
  simp only [TauCeti.coe_normalizedFrickeOperatorCusp, FunLike.coe_smul, hF] at hW
  have hW' := congrFun hW ⟨z, hz⟩
  have hω : Miyake.omegaGL N hN = TauCeti.frickeGL ℝ N := rfl
  rw [hω] at h1
  simp [TauCeti.atkinLehnerNormalizer] at h1 hW'
  exact h1.trans hW'

end ModularFormsKB.Elliptic
