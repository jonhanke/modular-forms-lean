import ModularFormsKB.Miyake.Wave8.Gamma1Reps
import ModularFormsKB.Miyake.Wave7.StarAdjoint
import TauCeti.NumberTheory.ModularForms.Petersson.Trace
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Trace
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.Basic

/-!
# Miyake §4.5: Theorem 4.5.18 (2) and Theorem 4.5.4 (2) for every `T(l, m)` and `T(n)`

Miyake, *Modular Forms* (Springer 1989), §4.5, pp. 136 and 151.

* Theorem 4.5.18 (2): for `α ∈ Δ₁(N)` the action of `Γ₀(N) α Γ₀(N)` on `𝒢_k(N, χ)` (with
  character) is the action of `Γ₁(N) α Γ₁(N)` on `𝒢_k(Γ₁(N))` (without character)
  (`twistedHeckeSlashSum_eq_heckeSlashSum_gamma1`). Stated on the underlying functions, i.e. on
  every `χ`-invariant function, which is the commutativity of Miyake's diagram.
* `T(l, m)` and `T*(m, l)` on `𝒮_k(N, χ)` are `χ(l)` and `conj χ(l)` times the traces of the
  translates by `diag(l, m)` and `diag(m, l)` (`coe_heckeTT_eq_trace`, `coe_heckeTStar_eq_trace`).
* Theorem 4.5.4 (2) in full: `T(l, m)` and `T*(m, l)`, and `T(n)` and `T*(n)`, are mutually
  adjoint for the Petersson product, with **no** condition on `(m, N)` or `(n, N)`
  (`pet_heckeTT_left_all`, `pet_heckeT_left_all`). This closes the case left open in wave 7
  (LE-MF-0206). The analytic input is Tau Ceti's adjoint formula for double coset operators
  (`CuspForm.peterssonInnerCosets_trace_translate`, Miyake's Theorem 2.8.2); the arithmetic
  input is that `Γ₁(N)`-representatives of `Γ₁(N) α Γ₁(N)` are `Γ₀(N)`-representatives of
  `Γ₀(N) α Γ₀(N)` with constant character weight (`Wave8.isCosetReps_of_gamma1`).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup DoubleCoset
  HeckeRing.GL2 HeckeRing.GLn
open scoped MatrixGroups ModularForm Pointwise

noncomputable section

namespace ModularFormsKB.Miyake.Wave8

open ModularFormsKB.Miyake.Wave4 ModularFormsKB.Miyake.Wave7 TauCeti

local notation "φ" => Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℚ ℝ)

variable {N : ℕ} [NeZero N]

attribute [local instance] fintypeDecompQuotientGamma0 Fintype.ofFinite

/-- The `Γ₁(N)` double coset of `α ∈ Δ₀(N)`, in Tau Ceti's Hecke ring of `(Δ₀(N), Γ₁(N))`. -/
abbrev cosetGamma1 {α : GL (Fin 2) ℚ} (hα : α ∈ Delta0 N) :
    HeckeCoset (Delta0 N) (gamma1Q N) (gamma1Q N) :=
  HeckeCoset.mk (gamma1Q N) (gamma1Q N) ⟨α, hα⟩

/-- The `Γ₀(N)` double coset of `α ∈ Δ₀(N)`. -/
abbrev cosetGamma0 {α : GL (Fin 2) ℚ} (hα : α ∈ Delta0 N) :
    HeckeCoset (Delta0 N) (gamma0Q N) (gamma0Q N) :=
  HeckeCoset.mk (gamma0Q N) (gamma0Q N) ⟨α, hα⟩

theorem out_cosetGamma1_mem {α : GL (Fin 2) ℚ} (hα : α ∈ Delta0 N) :
    ((cosetGamma1 hα).out : GL (Fin 2) ℚ) ∈
      doubleCoset α (gamma1Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N) :=
  HeckeCoset.rep_mem (cosetGamma1 hα)

theorem doubleCoset_out_cosetGamma1 {α : GL (Fin 2) ℚ} (hα : α ∈ Delta0 N) :
    doubleCoset ((cosetGamma1 hα).out : GL (Fin 2) ℚ) (gamma1Q N : Set (GL (Fin 2) ℚ))
      (gamma1Q N) = doubleCoset α (gamma1Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N) :=
  doubleCoset_eq_of_mem (out_cosetGamma1_mem hα)

/-- Tau Ceti's representatives of `Γ₁(N) \ Γ₁(N) α Γ₁(N)` are a complete set of representatives
of `Γ₀(N) \ Γ₀(N) α Γ₀(N)`. -/
theorem isCosetReps_rightCosetRep_gamma1 {α : GL (Fin 2) ℚ} (hα : α ∈ Delta0 N) :
    IsCosetReps N α (rightCosetRep (cosetGamma1 hα)) := by
  have h := isCosetReps_of_gamma1 ((cosetGamma1 hα).out.2)
    (doubleCoset_eq_iUnion_rightCosetRep (cosetGamma1 hα))
    (op_rightCosetRep_smul_injective (cosetGamma1 hα))
  refine IsCosetReps.of_mem_doubleCoset ?_ h
  exact doubleCoset_mono (gamma1Q_le_gamma0Q (N := N)) (gamma1Q_le_gamma0Q (N := N))
    (by rw [doubleCoset_out_cosetGamma1 hα]; exact mem_doubleCoset_self _ _ _)

/-- Every representative of `Γ₁(N) \ Γ₁(N) α Γ₁(N)` has the `a`- and `d`-entries of `α`
modulo `N`. -/
theorem rightCosetRep_gamma1_entries {α : GL (Fin 2) ℚ} (hα : α ∈ Delta0 N)
    {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : (α : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hA10 : (N : ℤ) ∣ A 1 0) (v) :
    ∃ X : Matrix (Fin 2) (Fin 2) ℤ,
      ((rightCosetRep (cosetGamma1 hα) v : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
        X.map (Int.cast : ℤ → ℚ) ∧ ((X 1 0 : ℤ) : ZMod N) = 0 ∧
        ((X 0 0 : ℤ) : ZMod N) = A 0 0 ∧ ((X 1 1 : ℤ) : ZMod N) = A 1 1 := by
  have hv := rightCosetRep_mem_doubleCoset (cosetGamma1 hα) v
  rw [doubleCoset_out_cosetGamma1 hα] at hv
  exact mem_doubleCoset_gamma1_entries hA hA10 hv

/-- **Miyake, Theorem 4.5.18 (2)**: for `α ∈ Δ₁(N)` and `f` with `f ∣ γ = χ(d_γ) f` on `Γ₀(N)`,
`f | Γ₀(N) α Γ₀(N)` (with character, (4.5.9)) equals `f | Γ₁(N) α Γ₁(N)` (without character). -/
@[kb "miyake1989" "Theorem 4.5.18 (2), p. 151"]
theorem twistedHeckeSlashSum_eq_heckeSlashSum_gamma1 (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    {α : GL (Fin 2) ℚ} (hα : α ∈ Delta1 N) (f : ℍ → ℂ) (hf : f ∈ functionCharSpace k χ) :
    twistedHeckeSlashSum k χ (cosetGamma0 (Delta1_le_Delta0 hα)) f =
      heckeSlashSum k (cosetGamma1 (Delta1_le_Delta0 hα)) f := by
  classical
  have hα0 := Delta1_le_Delta0 hα
  have hrep : IsCosetReps N ((cosetGamma0 hα0).out : GL (Fin 2) ℚ)
      (rightCosetRep (cosetGamma1 hα0)) :=
    IsCosetReps.of_mem_doubleCoset (HeckeCoset.rep_mem (cosetGamma0 hα0))
      (isCosetReps_rightCosetRep_gamma1 hα0)
  rw [← sum_delta0NebentypusChar_smul_slash_eq k χ _ hrep f hf, heckeSlashSum_def]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  obtain ⟨A, hA, -, hA10, hA1⟩ := hα
  obtain ⟨X, hX, -, hX00, -⟩ := rightCosetRep_gamma1_entries hα0 hA hA10 v
  have hu := Delta0UpperUnit_apply_val N
    (g := ⟨_, hrep.mem_Delta0 (cosetGamma0 hα0).out.2 v⟩) hX
  have h1 : Delta0UpperUnit N ⟨_, hrep.mem_Delta0 (cosetGamma0 hα0).out.2 v⟩ = 1 :=
    Units.ext (by rw [hu, hX00, hA1]; rfl)
  rw [delta0NebentypusChar_apply, h1, map_one, Units.val_one, one_smul]

/-! ### `T(l, m)` and `T*(m, l)` as traces of translates -/

/-- The trace from `Γ₁(N) ∩ δ⁻¹ Γ₁(N) δ` to `Γ₁(N)` of the translate of `f` by `δ` is the slash sum
over Shimura's representatives `δ τ_v⁻¹` of `Γ₁(N) \ Γ₁(N) δ Γ₁(N)`. -/
theorem coe_trace_translate_gamma1 (k : ℤ) {δ : GL (Fin 2) ℚ}
    [Finite (DecompQuotient (gamma1Q N) (gamma1Q N) δ⁻¹)]
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(CuspForm.trace ((Gamma1 N).map (mapGL ℝ)) (CuspForm.translate f (φ δ))) =
      ∑ v : DecompQuotient (gamma1Q N) (gamma1Q N) δ⁻¹,
        ⇑f ∣[k] (δ * ((v.out : GL (Fin 2) ℚ))⁻¹) := by
  let D : HeckeCoset (⊤ : Submonoid (GL (Fin 2) ℚ)) (gamma1Q N) (gamma1Q N) :=
    HeckeCoset.mk _ _ ⟨δ, Submonoid.mem_top δ⟩
  have hD : ((D.out : GL (Fin 2) ℚ)) ∈ doubleCoset δ (gamma1Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N) :=
    HeckeCoset.rep_mem D
  have hδ : δ ∈ doubleCoset (D.out : GL (Fin 2) ℚ) (gamma1Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N) := by
    rw [doubleCoset_eq_of_mem hD]; exact mem_doubleCoset_self _ _ _
  haveI : Finite (DecompQuotient (gamma1Q N) (gamma1Q N) (D.out : GL (Fin 2) ℚ)⁻¹) :=
    finite_decompQuotient_inv_of_mem_doubleCoset hD
  have hf : ∀ γ ∈ gamma1Q N, ⇑f ∣[k] γ = ⇑f := fun γ hγ ↦ by
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
    rw [ModularForm.rat_slash, Matrix.SpecialLinearGroup.map_mapGL]
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hg)
  have h1 := heckeSlashSum_eq_coe_trace_translate k D hδ (Subgroup.map_mapGL (Gamma1 N))
    (Subgroup.map_mapGL (Gamma1 N)) f
  have h2 := heckeSlashSum_eq_sum_of_mem_doubleCoset k D hδ (⇑f) hf
  rw [← h2]
  exact h1.symm

/-- `diag(l, m)` as an integral matrix. -/
theorem coe_natDiagGL_eq_map {l m : ℕ} (hl : 0 < l) (hm : 0 < m) :
    ((natDiagGL 2 ![l, m] : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (!![(l : ℤ), 0; 0, (m : ℤ)]).map (Int.cast : ℤ → ℚ) := by
  rw [natDiagGL_coe 2 ![l, m] (fun i ↦ by fin_cases i <;> simp [hl, hm])]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Shimura's representatives of `Γ₁(N) \ Γ₁(N) δ Γ₁(N)` lie in the double coset. -/
theorem mul_out_inv_mem_doubleCoset (δ : GL (Fin 2) ℚ)
    (v : DecompQuotient (gamma1Q N) (gamma1Q N) δ⁻¹) :
    δ * ((v.out : GL (Fin 2) ℚ))⁻¹ ∈
      doubleCoset δ (gamma1Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N) :=
  mem_doubleCoset.mpr ⟨1, one_mem _, _, inv_mem v.out.2, by rw [one_mul]⟩

/-- **`T(l, m)` as a trace** (Miyake (4.5.9) with Theorem 4.5.18): for `l ∣ m`, `(l, N) = 1`,
`f | T(l, m) = χ(l) · tr(f ∣ diag(l, m))`, the trace taken from `Γ₁(N) ∩ diag(l, m)⁻¹ Γ₁(N)
diag(l, m)` to `Γ₁(N)`. -/
theorem coe_heckeTT_eq_smul_trace (k : ℤ) (χ : DirichletCharacter ℂ N) {l m : ℕ} (hl : 0 < l)
    (hlm : l ∣ m) (hm : 0 < m) (hlN : l.Coprime N)
    [Finite (DecompQuotient (gamma1Q N) (gamma1Q N) (natDiagGL 2 ![l, m])⁻¹)]
    (f : cuspSpace k χ) :
    ⇑((heckeTT k χ l m f : cuspSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      χ (l : ZMod N) • ⇑(CuspForm.trace ((Gamma1 N).map (mapGL ℝ))
        (CuspForm.translate (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
          (φ (natDiagGL 2 ![l, m])))) := by
  classical
  have hA := coe_natDiagGL_eq_map hl hm
  have hA10 : (N : ℤ) ∣ (!![(l : ℤ), 0; 0, (m : ℤ)]) 1 0 := by simp
  have hlu : IsUnit (((!![(l : ℤ), 0; 0, (m : ℤ)]) 0 0 : ℤ) : ZMod N) := by
    simpa using (ZMod.unitOfCoprime l hlN).isUnit
  have hreps : IsCosetReps N (natDiagGL 2 ![l, m])
      (fun v : DecompQuotient (gamma1Q N) (gamma1Q N) (natDiagGL 2 ![l, m])⁻¹ ↦
        natDiagGL 2 ![l, m] * ((v.out : GL (Fin 2) ℚ))⁻¹) :=
    isCosetReps_of_gamma1_of_eq hA hA10 (Or.inl hlu)
      (le_antisymm (doubleCoset_natDiagGL_gamma0_subset hl hlm hm)
        (doubleCoset_mono le_rfl (gamma1Q_le_gamma0Q (N := N))))
      (doubleCoset_eq_iUnion_rightCosets _ _ _) (op_mul_out_inv_smul_injective _ _ _)
  rw [coe_trace_translate_gamma1, Finset.smul_sum, coe_heckeTT_eq_sum k χ hl hm hlN hreps f]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  obtain ⟨X, hX, -, hX00, -⟩ :=
    mem_doubleCoset_gamma1_entries hA hA10 (mul_out_inv_mem_doubleCoset _ v)
  have h00 : (((natDiagGL 2 ![l, m] * ((v.out : GL (Fin 2) ℚ))⁻¹ : GL (Fin 2) ℚ) :
      Matrix (Fin 2) (Fin 2) ℚ) 0 0) = ((X 0 0 : ℤ) : ℚ) := by
    rw [hX]; rfl
  rw [h00, Rat.num_intCast, hX00]
  simp

/-- `diag(m, l)⁻¹` and `diag(l, m)` differ by the central scalar `(l m)⁻¹`, so they conjugate every
subgroup alike. -/
theorem conjAct_natDiagGL_swap_inv_smul {l m : ℕ} (hl : 0 < l) (hm : 0 < m)
    (H : Subgroup (GL (Fin 2) ℚ)) :
    ConjAct.toConjAct (natDiagGL 2 ![m, l])⁻¹ • H = ConjAct.toConjAct (natDiagGL 2 ![l, m]) • H := by
  set z : GL (Fin 2) ℚ := (natDiagGL 2 ![l, m] * natDiagGL 2 ![m, l])⁻¹
  have hz : z ∈ Subgroup.center (GL (Fin 2) ℚ) := by
    refine Subgroup.inv_mem _ (Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
      ⟨((l * m : ℕ) : ℚ), ?_⟩)
    rw [Units.val_mul, natDiagGL_coe 2 ![l, m] (fun i ↦ by fin_cases i <;> simp [hl, hm]),
      natDiagGL_coe 2 ![m, l] (fun i ↦ by fin_cases i <;> simp [hl, hm]),
      Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, mul_comm]
  have he : (natDiagGL 2 ![m, l])⁻¹ = z * natDiagGL 2 ![l, m] := by
    simp only [z]; group
  rw [he, map_mul, mul_smul,
    Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.center_le_normalizer _ hz)]

/-- The decomposition of `Γ₁(N) diag(m, l) Γ₁(N)` is finite (`l ∣ m` not needed). -/
theorem finite_decompQuotient_swap {l m : ℕ} (hl : 0 < l) (hm : 0 < m) (hlN : l.Coprime N) :
    Finite (DecompQuotient (gamma1Q N) (gamma1Q N) (natDiagGL 2 ![m, l])⁻¹) := by
  have hδ : natDiagGL 2 ![l, m] ∈ Delta0 N :=
    natDiagGL_mem_Delta0_of_coprime N _ fun _ ↦ by simpa using hlN
  show Finite (_ ⧸ _)
  rw [conjAct_natDiagGL_swap_inv_smul hl hm]
  exact @Finite.of_fintype _ (Subgroup.fintypeOfIndexNeZero
    (IsHeckeTriple.commensurable_conjAct_right (Δ := Delta0 N) (H₁ := gamma1Q N)
      (H₂ := gamma1Q N) ⟨natDiagGL 2 ![l, m], hδ⟩).1.relIndex_ne_zero)

/-- The decomposition of `Γ₁(N) diag(l, m) Γ₁(N)` is finite, for `(l, N) = 1`. -/
theorem finite_decompQuotient_diag {l m : ℕ} (hlN : l.Coprime N) :
    Finite (DecompQuotient (gamma1Q N) (gamma1Q N) (natDiagGL 2 ![l, m])⁻¹) := by
  have hδ : natDiagGL 2 ![l, m] ∈ Delta0 N :=
    natDiagGL_mem_Delta0_of_coprime N _ fun _ ↦ by simpa using hlN
  exact @Finite.of_fintype _ (Subgroup.fintypeOfIndexNeZero
    (IsHeckeTriple.commensurable_conjAct_inv_left (Δ := Delta0 N) (H₁ := gamma1Q N)
      (H₂ := gamma1Q N) ⟨natDiagGL 2 ![l, m], hδ⟩).1.relIndex_ne_zero)

/-- **`T*(m, l)` as a trace**: for `l ∣ m`, `(l, N) = 1`,
`f | T*(m, l) = conj(χ(l)) · tr(f ∣ diag(m, l))`. -/
theorem coe_heckeTStar_eq_smul_trace (k : ℤ) (χ : DirichletCharacter ℂ N) {l m : ℕ} (hl : 0 < l)
    (hlm : l ∣ m) (hm : 0 < m) (hlN : l.Coprime N)
    [Finite (DecompQuotient (gamma1Q N) (gamma1Q N) (natDiagGL 2 ![m, l])⁻¹)]
    (f : cuspSpace k χ) :
    ⇑((heckeTStar k χ m l f : cuspSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      starRingEnd ℂ (χ (l : ZMod N)) • ⇑(CuspForm.trace ((Gamma1 N).map (mapGL ℝ))
        (CuspForm.translate (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
          (φ (natDiagGL 2 ![m, l])))) := by
  classical
  have hA := coe_natDiagGL_eq_map hm hl
  have hA10 : (N : ℤ) ∣ (!![(m : ℤ), 0; 0, (l : ℤ)]) 1 0 := by simp
  have hlu : IsUnit (((!![(m : ℤ), 0; 0, (l : ℤ)]) 1 1 : ℤ) : ZMod N) := by
    simpa using (ZMod.unitOfCoprime l hlN).isUnit
  have hreps : IsCosetReps N (natDiagGL 2 ![m, l])
      (fun v : DecompQuotient (gamma1Q N) (gamma1Q N) (natDiagGL 2 ![m, l])⁻¹ ↦
        natDiagGL 2 ![m, l] * ((v.out : GL (Fin 2) ℚ))⁻¹) :=
    isCosetReps_of_gamma1_of_eq hA hA10 (Or.inr hlu)
      (le_antisymm (doubleCoset_natDiagGL_swap_gamma0_subset hl hlm hm)
        (doubleCoset_mono le_rfl (gamma1Q_le_gamma0Q (N := N))))
      (doubleCoset_eq_iUnion_rightCosets _ _ _) (op_mul_out_inv_smul_injective _ _ _)
  rw [coe_trace_translate_gamma1, Finset.smul_sum, coe_heckeTStar k χ hl hm hlN hreps f,
    starSlashSum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  obtain ⟨X, hX, -, -, hX11⟩ :=
    mem_doubleCoset_gamma1_entries hA hA10 (mul_out_inv_mem_doubleCoset _ v)
  have h11 : (((natDiagGL 2 ![m, l] * ((v.out : GL (Fin 2) ℚ))⁻¹ : GL (Fin 2) ℚ) :
      Matrix (Fin 2) (Fin 2) ℚ) 1 1) = ((X 1 1 : ℤ) : ℚ) := by
    rw [hX]; rfl
  rw [starWeight, h11, Rat.num_intCast, hX11]
  simp

/-- `adj(diag(l, m)) = diag(m, l)` over `ℝ`. -/
theorem adjugate_natDiagGL {l m : ℕ} (hl : 0 < l) (hm : 0 < m) :
    (φ (natDiagGL 2 ![l, m])).adjugate = φ (natDiagGL 2 ![m, l]) := by
  have h1 := natDiagGL_coe 2 ![l, m] (fun i ↦ by fin_cases i <;> simp [hl, hm])
  have h2 := natDiagGL_coe 2 ![m, l] (fun i ↦ by fin_cases i <;> simp [hl, hm])
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_adjugate, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map_apply, h1, h2, Matrix.diagonal]

/-! ### Theorem 4.5.4 (2) -/

/-- The trace of a translate depends only on the translating matrix (not on the proof of finite
index carried along). -/
theorem pet_trace_congr {k : ℤ} {β β' : GL (Fin 2) ℝ} (h : β = β')
    [(ConjAct.toConjAct β⁻¹ • (Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex
      ((Gamma1 N).map (mapGL ℝ))]
    [(ConjAct.toConjAct β'⁻¹ • (Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex
      ((Gamma1 N).map (mapGL ℝ))]
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm.peterssonInnerCosets f
        (CuspForm.trace ((Gamma1 N).map (mapGL ℝ)) (CuspForm.translate g β)) =
      CuspForm.peterssonInnerCosets f
        (CuspForm.trace ((Gamma1 N).map (mapGL ℝ)) (CuspForm.translate g β')) := by
  subst h
  rfl

private theorem pet_conj_symm8 {k : ℤ} {χ : DirichletCharacter ℂ N} (f g : cuspSpace k χ) :
    starRingEnd ℂ (pet g f) = pet f g :=
  CuspForm.peterssonInnerCosets_conj_symm _ _

/-- **Miyake, Theorem 4.5.4 (2)** for every `T(l, m)` (`l ∣ m`, `(l, N) = 1`; no condition on
`m`): `⟨f | T(l, m), g⟩ = ⟨f, g | T*(m, l)⟩` on `𝒮_k(N, χ)`. -/
@[kb "miyake1989" "Theorem 4.5.4 (2), p. 136"]
theorem pet_heckeTT_left_all (k : ℤ) (χ : DirichletCharacter ℂ N) {l m : ℕ} (hl : 0 < l)
    (hlm : l ∣ m) (hm : 0 < m) (hlN : l.Coprime N) (f g : cuspSpace k χ) :
    pet (heckeTT k χ l m f) g = pet f (heckeTStar k χ m l g) := by
  haveI := finite_decompQuotient_diag (N := N) (m := m) hlN
  haveI := finite_decompQuotient_swap (N := N) hl hm hlN
  have e1 : ((heckeTT k χ l m f : cuspSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      χ (l : ZMod N) • CuspForm.trace ((Gamma1 N).map (mapGL ℝ))
        (CuspForm.translate (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
          (φ (natDiagGL 2 ![l, m]))) :=
    DFunLike.coe_injective (by rw [coe_heckeTT_eq_smul_trace k χ hl hlm hm hlN f]; rfl)
  have e2 : ((heckeTStar k χ m l g : cuspSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      starRingEnd ℂ (χ (l : ZMod N)) • CuspForm.trace ((Gamma1 N).map (mapGL ℝ))
        (CuspForm.translate (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
          (φ (natDiagGL 2 ![m, l]))) :=
    DFunLike.coe_injective (by rw [coe_heckeTStar_eq_smul_trace k χ hl hlm hm hlN g]; rfl)
  have hadj := adjugate_natDiagGL (l := l) (m := m) hl hm
  have hdet : 0 < ((φ (natDiagGL 2 ![l, m]) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    have h1 := natDiagGL_coe 2 ![l, m] (fun i ↦ by fin_cases i <;> simp [hl, hm])
    rw [Matrix.det_fin_two]
    simp [Matrix.GeneralLinearGroup.map_apply, h1, Matrix.diagonal]
    positivity
  haveI : (ConjAct.toConjAct (φ (natDiagGL 2 ![l, m])).adjugate⁻¹ •
      (Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex ((Gamma1 N).map (mapGL ℝ)) := by
    rw [hadj]; infer_instance
  have key := CuspForm.peterssonInnerCosets_trace_translate (k := k) (Γ₁ := Gamma1 N)
    (Γ₂ := Gamma1 N) hdet Iff.rfl (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
  show CuspForm.peterssonInnerCosets _ _ = CuspForm.peterssonInnerCosets _ _
  rw [e1, e2, CuspForm.peterssonInnerCosets_smul_left, CuspForm.peterssonInnerCosets_smul_right,
    key, pet_trace_congr hadj]

/-- **Miyake, Theorem 4.5.4 (2)** for every `T(l, m)`, the other half:
`⟨f | T*(m, l), g⟩ = ⟨f, g | T(l, m)⟩`. -/
@[kb "miyake1989" "Theorem 4.5.4 (2), p. 136"]
theorem pet_heckeTStar_left_all (k : ℤ) (χ : DirichletCharacter ℂ N) {l m : ℕ} (hl : 0 < l)
    (hlm : l ∣ m) (hm : 0 < m) (hlN : l.Coprime N) (f g : cuspSpace k χ) :
    pet (heckeTStar k χ m l f) g = pet f (heckeTT k χ l m g) := by
  rw [← pet_conj_symm8, ← pet_heckeTT_left_all k χ hl hlm hm hlN g f, pet_conj_symm8]

section Sums

variable {k : ℤ} {χ : DirichletCharacter ℂ N}

private theorem pet_zero_left (g : cuspSpace k χ) : pet (0 : cuspSpace k χ) g = 0 := by
  simp [pet]

private theorem pet_zero_right (f : cuspSpace k χ) : pet f (0 : cuspSpace k χ) = 0 := by
  simp [pet]

/-- Adjointness passes to finite sums of operators. -/
private theorem pet_sum {s : Finset ℕ} {A B : ℕ → Module.End ℂ (cuspSpace k χ)}
    (h : ∀ l ∈ s, ∀ f g, pet (A l f) g = pet f (B l g)) (f g : cuspSpace k χ) :
    pet ((∑ l ∈ s, A l) f) g = pet f ((∑ l ∈ s, B l) g) := by
  induction s using Finset.cons_induction with
  | empty => simp [pet_zero_left, pet_zero_right]
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, LinearMap.add_apply, LinearMap.add_apply]
    have h1 : pet (A a f + (∑ l ∈ s, A l) f) g = pet (A a f) g + pet ((∑ l ∈ s, A l) f) g :=
      CuspForm.peterssonInnerCosets_add_left _ _ _
    have h2 : pet f (B a g + (∑ l ∈ s, B l) g) = pet f (B a g) + pet f ((∑ l ∈ s, B l) g) :=
      CuspForm.peterssonInnerCosets_add_right _ _ _
    rw [h1, h2, h a (Finset.mem_cons_self a s) f g,
      ih (fun l hl ↦ h l (Finset.mem_cons_of_mem hl))]

end Sums

private theorem heckeTT_eq_zero' (k : ℤ) (χ : DirichletCharacter ℂ N) {l m : ℕ}
    (h : ¬ (0 < l ∧ 0 < m ∧ l.Coprime N)) : heckeTT k χ l m = 0 := by
  show HeckeRing.GL2.heckeRingHomCuspCharSpace k χ.toUnitHom
    (HeckeRing.GL2.diagElemGamma0 N ![l, m]) = 0
  by_cases hp : ∀ i, 0 < (![l, m] : Fin 2 → ℕ) i
  · have hc : ¬ Nat.Coprime ((![l, m] : Fin 2 → ℕ) 0) N := by
      intro hc; exact h ⟨by simpa using hp 0, by simpa using hp 1, by simpa using hc⟩
    rw [HeckeRing.GL2.diagElemGamma0_of_not_coprime N hc, map_zero]
  · rw [HeckeRing.GL2.diagElemGamma0_of_not_pos N hp, map_zero]

/-- **Miyake, Theorem 4.5.4 (2)** for every `T(n)`, `n ≥ 1` (no condition on `(n, N)`): `T(n)` and
`T*(n)` are mutually adjoint for the Petersson product on `𝒮_k(N, χ)`. -/
@[kb "miyake1989" "Theorem 4.5.4 (2), p. 136"]
theorem pet_heckeT_left_all (k : ℤ) (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : 0 < n)
    (f g : cuspSpace k χ) :
    pet (heckeT k χ n f) g = pet f (heckeTStarN k χ n g) := by
  rw [heckeT_eq_sum_heckeTT k χ hn.ne', heckeTStarN]
  refine pet_sum (fun l hl f g ↦ ?_) f g
  obtain ⟨hmem, hl2⟩ := Finset.mem_filter.mp hl
  have hld : l ∣ n := Nat.dvd_of_mem_divisors hmem
  have hlpos : 0 < l := Nat.pos_of_dvd_of_pos hld hn
  have hm : 0 < n / l := Nat.div_pos (Nat.le_of_dvd hn hld) hlpos
  by_cases hlN : l.Coprime N
  · exact pet_heckeTT_left_all k χ hlpos hl2 hm hlN f g
  · have h1 : heckeTT k χ l (n / l) = 0 := heckeTT_eq_zero' k χ fun h ↦ hlN h.2.2
    have h2 : heckeTStar k χ (n / l) l = 0 := by
      rw [heckeTStar, dite_eq_right_iff.mpr fun h ↦ absurd h.2.2 hlN]
    rw [h1, h2, LinearMap.zero_apply, LinearMap.zero_apply, pet_zero_left, pet_zero_right]

/-- **Miyake, Theorem 4.5.4 (2)** for every `T(n)`, the other half. -/
@[kb "miyake1989" "Theorem 4.5.4 (2), p. 136"]
theorem pet_heckeTStarN_left_all (k : ℤ) (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : 0 < n)
    (f g : cuspSpace k χ) :
    pet (heckeTStarN k χ n f) g = pet f (heckeT k χ n g) := by
  rw [← pet_conj_symm8, ← pet_heckeT_left_all k χ hn g f, pet_conj_symm8]

end ModularFormsKB.Miyake.Wave8
