import ModularFormsKB.Elliptic.HasNewform
import ModularFormsKB.Elliptic.Gamma0Sixteen
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.CongruentL
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.F32Theta
import TauCeti.NumberTheory.ModularForms.Newforms.Coefficient
import TauCeti.NumberTheory.ModularForms.Newforms.Conductor
import TauCeti.NumberTheory.ModularForms.TrivialNebentypus

/-!
# $f_{32}$ is a newform of level $32$

`F32Newform` (moved here from `CongruentModular.lean`, statement unchanged) says that there is a Tau
Ceti newform of level $32$, weight $2$ and trivial nebentypus with Fourier coefficients
$b(m) = $ `f32Coeff m`. It is proved here (`f32Newform`), with no named input:

1. **The cusp form.** `f32Modular` (from $f_{32} = \eta(4\tau)^2\eta(8\tau)^2$)
   gives $f_{32} \in S_2(\Gamma_0(32))$; restricted to $\Gamma_1(32)$ it has trivial nebentypus
   (Tau Ceti `restrict_mem_cuspFormCharSpace_one`).
2. **The Hecke eigen property away from $2$.** $b$ is multiplicative (`f32Coeff_mul_of_coprime`) and
   satisfies $b(p^{r+2}) = b(p)b(p^{r+1}) - p\,b(p^r)$ at odd primes (`f32Coeff_prime_pow_add_two`),
   which is Diamond–Shurman's coefficient criterion (Tau Ceti
   `EigenformAwayFromLevel.exists_toCuspForm_eq_and_χ_eq_of_qExpansion_coeff_mul_of_prime_pow_add_two`).
3. **Newness.** The conductor $M \mid 32$ of this eigenform (Tau Ceti
   `EigenformAwayFromLevel.conductor`) carries the primitive associate, a newform of level $M$ whose
   nebentypus induces the trivial character modulo $32$, hence is trivial. If $M \ne 32$ then
   $M \mid 16$ and the primitive associate is a nonzero element of $S_2(\Gamma_0(M)) \subseteq
   S_2(\Gamma_0(16)) = 0$ (`cuspForm_Gamma0_sixteen_eq_zero`). So $M = 32$, and an eigenform whose
   conductor is the level is new (`conductor_eq_self_iff_mem_cuspFormsNew`).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace ModularFormsKB.Elliptic

open HeckeRing.GL2 ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves TauCeti

/-- **$f_{32}$ is a newform of level $32$** (named statement, with newness): there is a Tau
Ceti newform of level $32$, weight $2$ and trivial nebentypus with Fourier coefficients $b(m)$ (`f32Coeff`). Classical:
$f_{32} = \eta(4\tau)^2\eta(8\tau)^2$, the theta series of the Hecke character $\alpha \mapsto \alpha$ of
$\mathbb Q(i)$ modulo $(2 + 2i)$ (Miyake Theorem 4.8.2 [unverified]). Proved: `f32Newform`. -/
structure F32Newform : Prop where
  exists_newform : ∃ f : Newform 32 2, f.χ = 1 ∧ ∀ m : ℕ, (qExpansion 1 f.toCuspForm).coeff m = (f32Coeff m : ℂ)

/-- $f_{32}$ as a cusp form on $\Gamma_1(32)$ (the restriction of `f32Modular`). -/
noncomputable def f32CuspGamma1 : CuspForm ((Gamma1 32).map (mapGL ℝ)) 2 :=
  CuspForm.restrict (Gamma1_map_le_Gamma0_map 32) f32Modular.exists_cuspForm.choose

theorem coe_f32CuspGamma1 : ⇑f32CuspGamma1 = f32 :=
  f32Modular.exists_cuspForm.choose_spec

theorem f32CuspGamma1_mem : f32CuspGamma1 ∈ cuspFormCharSpace 2 (1 : (ZMod 32)ˣ →* ℂˣ) :=
  restrict_mem_cuspFormCharSpace_one _

/-- The $q$-expansion of $f_{32}$ on $\Gamma_1(32)$ has coefficients $b(m)$. -/
theorem qExpansion_coeff_f32CuspGamma1 (m : ℕ) :
    (qExpansion 1 f32CuspGamma1).coeff m = (f32Coeff m : ℂ) := by
  symm
  refine ModularFormClass.qExpansion_coeff_unique (Γ := (Gamma1 32).map (mapGL ℝ)) (k := 2)
    (f := f32CuspGamma1) (c := fun m : ℕ ↦ (f32Coeff m : ℂ)) one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map 32) (fun τ ↦ ?_) m
  have hG : f32CuspGamma1 τ = f32 τ := congrFun coe_f32CuspGamma1 τ
  rw [hG]
  convert hasQExp_f32 τ using 2 with j
  rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem f32CuspGamma1_ne_zero : f32CuspGamma1 ≠ 0 := by
  intro h
  have h1 := qExpansion_coeff_f32CuspGamma1 1
  rw [h] at h1
  simp [f32Coeff_one, UpperHalfPlane.qExpansion_zero] at h1

/-- $f_{32}$ is a good Hecke eigenform of level $32$ with trivial nebentypus. -/
theorem exists_f32Eigenform :
    ∃ F : EigenformAwayFromLevel 32 2, F.toCuspForm = f32CuspGamma1 ∧ F.χ = 1 := by
  refine EigenformAwayFromLevel.exists_toCuspForm_eq_and_χ_eq_of_qExpansion_coeff_mul_of_prime_pow_add_two
    f32CuspGamma1_mem f32CuspGamma1_ne_zero (fun u v huv ↦ ?_) (fun p hp hpN r ↦ ?_)
  · simp only [qExpansion_coeff_f32CuspGamma1, f32Coeff_mul_of_coprime huv, Int.cast_mul]
  · have hp2 : p ≠ 2 := by
      rintro rfl
      norm_num at hpN
    simp only [qExpansion_coeff_f32CuspGamma1, MonoidHom.one_apply, Units.val_one, one_mul,
      f32Coeff_prime_pow_add_two hp hp2]
    push_cast
    norm_num

/-- The good Hecke eigenform $f_{32}$. -/
noncomputable def f32Eigenform : EigenformAwayFromLevel 32 2 := exists_f32Eigenform.choose

theorem f32Eigenform_toCuspForm : f32Eigenform.toCuspForm = f32CuspGamma1 :=
  exists_f32Eigenform.choose_spec.1

theorem f32Eigenform_χ : f32Eigenform.χ = 1 := exists_f32Eigenform.choose_spec.2

/-- A newform of level dividing $16$ with trivial nebentypus does not exist ($S_2(\Gamma_0(16)) = 0$). -/
theorem not_newform_dvd_sixteen {M : ℕ} [NeZero M] (hM : M ∣ 16) (g : Newform M 2) (hg : g.χ = 1) :
    False := by
  have hmem : g.toCuspForm ∈ cuspFormCharSpace 2 (1 : (ZMod M)ˣ →* ℂˣ) := hg ▸ g.mem_charSpace
  let G : CuspForm ((Gamma0 M).map (mapGL ℝ)) 2 := cuspFormCharSpaceOneEquiv M 2 ⟨_, hmem⟩
  let G16 : CuspForm ((Gamma0 16).map (mapGL ℝ)) 2 :=
    CuspForm.restrict (Subgroup.map_mono (Gamma0_le_Gamma0_of_dvd hM)) G
  have h0 := cuspForm_Gamma0_sixteen_eq_zero G16
  apply g.ne_zero
  ext τ
  have := congrArg (fun F : CuspForm ((Gamma0 16).map (mapGL ℝ)) 2 ↦ F τ) h0
  simpa [G16, G] using this

/-- **The conductor of $f_{32}$ is $32$.** -/
theorem f32Eigenform_conductor : f32Eigenform.conductor = 32 := by
  by_contra hne
  have hM : f32Eigenform.conductor ∣ 32 := f32Eigenform.conductor_dvd
  have hM16 : f32Eigenform.conductor ∣ 16 := by
    obtain ⟨i, hi, hiM⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show f32Eigenform.conductor ∣ 2 ^ 5 from hM)
    rw [hiM] at hne ⊢
    have : i ≠ 5 := by rintro rfl; exact hne rfl
    exact (Nat.pow_dvd_pow 2 (by omega : i ≤ 4))
  have hχ := f32Eigenform.primitiveAssociate_χ_comp_unitsMap hM
  rw [f32Eigenform_χ] at hχ
  have hg : f32Eigenform.primitiveAssociate.χ = 1 := by
    refine (MonoidHom.cancel_right (ZMod.unitsMap_surjective hM)).mp ?_
    rw [hχ]
    rfl
  exact not_newform_dvd_sixteen hM16 _ hg

/-- **$f_{32}$ is a newform of level $32$** (Tau Ceti's `Newform`). -/
noncomputable def f32NewformDef : Newform 32 2 where
  toEigenformAwayFromLevel := f32Eigenform
  isNew := (EigenformAwayFromLevel.conductor_eq_self_iff_mem_cuspFormsNew _).1 f32Eigenform_conductor
  isNorm := by rw [f32Eigenform_toCuspForm, qExpansion_coeff_f32CuspGamma1, f32Coeff_one]; simp

/-- **`F32Newform` holds**, with no named input: $f_{32}$ is a newform of level $32$, weight $2$ and trivial
nebentypus with coefficients $b(m)$. -/
theorem f32Newform : F32Newform :=
  ⟨⟨f32NewformDef, f32Eigenform_χ, fun m ↦ by
    show (qExpansion 1 f32Eigenform.toCuspForm).coeff m = _
    rw [f32Eigenform_toCuspForm, qExpansion_coeff_f32CuspGamma1]⟩⟩

end ModularFormsKB.Elliptic
