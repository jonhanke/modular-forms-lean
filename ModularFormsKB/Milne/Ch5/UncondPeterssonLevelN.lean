import ModularFormsKB.Milne.Ch5.UncondEulerLevelN
import TauCeti.NumberTheory.ModularForms.Petersson.Trace

/-!
# Milne, Proposition 5.37 unconditionally: $T(n)$ is self-adjoint up to $\varepsilon(n)$ at level $\Gamma(N)$

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf p. 85.

For $\alpha \in \Delta(N)$ over $T(a, d)$, $ad = n$ prime to $N$, the main involution
$\alpha^\iota = \det(\alpha)\alpha^{-1}$ lies in $R\,\Gamma(N)\alpha\Gamma(N)$ with $R \in \Gamma(1)$,
$R \equiv \mathrm{diag}(n, n^{-1}) \bmod N$ (`adj_mem_doubleCoset`). With Tau Ceti's adjoint formula for a double
coset operator (`CuspForm.peterssonInnerCosets_trace_translate`) this gives
$\langle T(n)f, g\rangle = \langle f, \varepsilon(n)^{-1}T(n)g\rangle$ for $g$ of character $\varepsilon$, which is
Proposition 5.37 since $|\varepsilon(n)| = 1$.
-/

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing HeckeRing.GLn HeckeRing.GL2
  DoubleCoset

open scoped MatrixGroups ModularForm Pointwise HeckeCosetModule

namespace ModularFormsKB.Milne.UncondLevelN

local notation "φ" => Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℚ ℝ)

/-- The adjugate on `GL`, now `Matrix.GeneralLinearGroup.adjugate` in Tau Ceti. -/
local notation "adjugateGL" => Matrix.GeneralLinearGroup.adjugate

variable {N : ℕ}

theorem adjugateGL_val_two (g : GL (Fin 2) ℚ) :
    ((adjugateGL g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = (g : Matrix (Fin 2) (Fin 2) ℚ).adjugate :=
  Matrix.GeneralLinearGroup.coe_adjugate g

theorem phi_adjugateGL (g : GL (Fin 2) ℚ) : φ (adjugateGL g) = adjugateGL (φ g) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.coe_adjugate, Matrix.GeneralLinearGroup.val_map_apply,
    Matrix.GeneralLinearGroup.val_map_apply, Matrix.GeneralLinearGroup.coe_adjugate]
  exact (algebraMap ℚ ℝ).map_adjugate (g : Matrix (Fin 2) (Fin 2) ℚ)

/-- The adjugate of `diag(a, d)` is `S diag(a, d) S⁻¹`. -/
theorem adjugateGL_natDiagGL (a d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    adjugateGL (natDiagGL 2 ![a, d]) =
      mapGL ℚ ModularGroup.S * natDiagGL 2 ![a, d] * mapGL ℚ ModularGroup.S⁻¹ := by
  rw [natDiagGL_eq_intGL a d ha hd, mapGL_eq_intGL, mapGL_eq_intGL, intGL_mul, intGL_mul]
  · refine Units.ext ?_
    rw [adjugateGL_val_two, intGL_coe, intGL_coe, Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_S,
      Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  all_goals simp only [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, Matrix.det_fin_two_of]; simp [ha.ne', hd.ne']

/-- **The adjugate stays in the `Γ(1)`-double coset.** -/
theorem adjugateGL_mem_dc {a d : ℕ} (ha : 0 < a) (hd : 0 < d) {α : GL (Fin 2) ℚ}
    (hα : α ∈ doubleCoset (natDiagGL 2 ![a, d]) (SLnZ 2 : Set (GL (Fin 2) ℚ)) (SLnZ 2)) :
    adjugateGL α ∈ doubleCoset α (SLnZ 2 : Set (GL (Fin 2) ℚ)) (SLnZ 2) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset.mp hα
  obtain ⟨s, rfl⟩ := (mem_SLnZ_iff 2).mp hu
  obtain ⟨t, rfl⟩ := (mem_SLnZ_iff 2).mp hv
  have hs : adjugateGL (s : GL (Fin 2) ℚ) = (s : GL (Fin 2) ℚ)⁻¹ :=
    Matrix.GeneralLinearGroup.adjugate_eq_inv_iff.mpr (by have := det_mapGL s; exact this)
  have ht : adjugateGL (t : GL (Fin 2) ℚ) = (t : GL (Fin 2) ℚ)⁻¹ :=
    Matrix.GeneralLinearGroup.adjugate_eq_inv_iff.mpr (by have := det_mapGL t; exact this)
  rw [Matrix.GeneralLinearGroup.adjugate_mul_distrib, Matrix.GeneralLinearGroup.adjugate_mul_distrib, hs, ht, adjugateGL_natDiagGL a d ha hd]
  refine mem_doubleCoset.mpr ⟨(t : GL (Fin 2) ℚ)⁻¹ * mapGL ℚ ModularGroup.S * (s : GL (Fin 2) ℚ)⁻¹,
    mul_mem (mul_mem (inv_mem (coe_mem_SLnZ 2 t)) (coe_mem_SLnZ 2 _)) (inv_mem (coe_mem_SLnZ 2 s)),
    (t : GL (Fin 2) ℚ)⁻¹ * mapGL ℚ ModularGroup.S⁻¹ * (s : GL (Fin 2) ℚ)⁻¹,
    mul_mem (mul_mem (inv_mem (coe_mem_SLnZ 2 t)) (coe_mem_SLnZ 2 _)) (inv_mem (coe_mem_SLnZ 2 s)), ?_⟩
  group


/-- `R ∈ SL₂(ℤ)` congruent to `diag(m, m⁻¹)` modulo `N`: the operator `R_{m⁻¹}`. -/
noncomputable def rhoN (N m : ℕ) [NeZero N] (hcop : m.Coprime N) : SL(2, ℤ) :=
  (exists_diamondRep N (ZMod.unitOfCoprime m hcop)⁻¹).choose

/-- `R⁻¹ α^ι ∈ Δ(N)` for `α ∈ Δ(N)` of determinant `m`. -/
theorem rho_adj_mem_DeltaN [NeZero N] {α : GL (Fin 2) ℚ} (hα : α ∈ DeltaN N) {m : ℕ}
    (hdet : (α : Matrix (Fin 2) (Fin 2) ℚ).det = m) (hcop : m.Coprime N) :
    (mapGL ℚ (rhoN N m hcop))⁻¹ * adjugateGL α ∈ DeltaN N := by
  obtain ⟨A, hA, hdA, hcA, hmA⟩ := hα
  set ρ := rhoN N m hcop
  set u := ZMod.unitOfCoprime m hcop
  have hσ : (ρ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) =
      !![(((u⁻¹)⁻¹ : (ZMod N)ˣ) : ZMod N), 0; 0, ((u⁻¹ : (ZMod N)ˣ) : ZMod N)] :=
    (exists_diamondRep N u⁻¹).choose_spec
  have hu : (u : ZMod N) = (m : ZMod N) := ZMod.coe_unitOfCoprime m hcop
  have hAm : A.det = m := by
    have : ((A.det : ℤ) : ℚ) = m := by rw [← hdet, hA, det_map_int]
    exact_mod_cast this
  have h00 : ((ρ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod N) = (u : ZMod N) := by
    simpa using congrFun (congrFun hσ 0) 0
  have h01 : ((ρ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod N) = 0 := by
    simpa using congrFun (congrFun hσ 0) 1
  have h10 : ((ρ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0 := by
    simpa using congrFun (congrFun hσ 1) 0
  have h11 : ((ρ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod N) = ((u⁻¹ : (ZMod N)ˣ) : ZMod N) := by
    simpa using congrFun (congrFun hσ 1) 1
  have hA00 : (A 0 0 : ZMod N) = 1 := by simpa using congrFun (congrFun hmA 0) 0
  have hA01 : (A 0 1 : ZMod N) = 0 := by simpa using congrFun (congrFun hmA 0) 1
  have hA10 : (A 1 0 : ZMod N) = 0 := by simpa using congrFun (congrFun hmA 1) 0
  have hA11 : (A 1 1 : ZMod N) = (A.det : ZMod N) := by simpa using congrFun (congrFun hmA 1) 1
  set B : Matrix (Fin 2) (Fin 2) ℤ := ((ρ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * A.adjugate with hB
  have hdB : B.det = m := by
    rw [hB, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul, Matrix.det_adjugate, hAm]; simp
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · have hadjA : (A.map (Int.cast : ℤ → ℚ)).adjugate = A.adjugate.map (Int.cast : ℤ → ℚ) :=
      ((Int.castRingHom ℚ).map_adjugate A).symm
    rw [← map_inv, Units.val_mul, adjugateGL_val_two, hA, coe_mapGL_int, hadjA]
    exact (Matrix.map_mul_intCast _ _).symm
  · rw [hdB]; exact_mod_cast (Nat.pos_of_ne_zero (by rintro rfl; simp at hAm; omega))
  · rw [hdB]; exact Nat.isCoprime_iff_coprime.mpr hcop
  · have e1 : (ρ : Matrix (Fin 2) (Fin 2) ℤ).adjugate.map (Int.cast : ℤ → ZMod N) =
        ((ρ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)).adjugate :=
      (Int.castRingHom (ZMod N)).map_adjugate _
    have e2 : A.adjugate.map (Int.cast : ℤ → ZMod N) = (A.map (Int.cast : ℤ → ZMod N)).adjugate :=
      (Int.castRingHom (ZMod N)).map_adjugate _
    rw [hdB, hB, Matrix.map_mul_intCast, Matrix.SpecialLinearGroup.coe_inv, e1, e2, hσ, hmA, hAm,
      Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
    have hinv : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (m : ZMod N) = 1 := by rw [← hu]; exact Units.inv_mul u
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hinv, hu]


section adjoint

variable [NeZero N] {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (hcop : (a * d).Coprime N)
  (D : HeckeCoset (DeltaN N) (GammaGL N) (GammaGL N))
  (hD : ((Quotient.out D : DeltaN N) : GL (Fin 2) ℚ) ∈
    doubleCoset (natDiagGL 2 ![a, d]) (SLnZ 2 : Set (GL (Fin 2) ℚ)) (SLnZ 2))
include ha hd hcop hD

theorem det_out_eq : (((Quotient.out D : DeltaN N) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = (a * d : ℕ) := by
  rw [det_eq_of_mem_dc hD, natDiagGL_eq_intGL a d ha hd, intGL_coe, det_map_int]
  simp [Matrix.det_fin_two_of]

/-- The element `R⁻¹ α^ι` of the double coset `Γ(N) α Γ(N)`. -/
noncomputable def adjRep (hcop : (a * d).Coprime N) : GL (Fin 2) ℚ :=
  (mapGL ℚ (rhoN N (a * d) hcop))⁻¹ * adjugateGL ((Quotient.out D : DeltaN N) : GL (Fin 2) ℚ)

theorem adjRep_mem : adjRep D hcop ∈ doubleCoset ((Quotient.out D : DeltaN N) : GL (Fin 2) ℚ)
    (GammaGL N : Set (GL (Fin 2) ℚ)) (GammaGL N) := by
  refine mem_doubleCoset_Gamma_of_SL (Quotient.out D).2
    (rho_adj_mem_DeltaN (Quotient.out D).2 (det_out_eq ha hd hcop D hD) hcop) ?_
  exact mul_mem_doubleCoset_left (inv_mem (coe_mem_SLnZ 2 _)) (adjugateGL_mem_dc ha hd hD)

omit ha hd hD in
theorem adj_eq : adjugateGL (φ ((Quotient.out D : DeltaN N) : GL (Fin 2) ℚ)) =
    mapGL ℝ (rhoN N (a * d) hcop) * φ (adjRep D hcop) := by
  rw [adjRep, map_mul, map_inv, map_mapGL_rat_real, mul_inv_cancel_left, phi_adjugateGL]

omit ha hd hD in
theorem level_eq : ConjAct.toConjAct (adjugateGL (φ ((Quotient.out D : DeltaN N) : GL (Fin 2) ℚ)))⁻¹ •
    (Gamma N).map (mapGL ℝ) = ConjAct.toConjAct (φ (adjRep D hcop))⁻¹ • (Gamma N).map (mapGL ℝ) := by
  rw [adj_eq hcop D, _root_.mul_inv_rev, ConjAct.toConjAct_mul, mul_smul, conj_Gamma_map N _]

theorem isFiniteRelIndex_adjRep : (ConjAct.toConjAct (φ (adjRep D hcop))⁻¹ •
    (Gamma N).map (mapGL ℝ)).IsFiniteRelIndex ((Gamma N).map (mapGL ℝ)) := by
  have := TauCeti.finite_decompQuotient_inv_of_mem_doubleCoset (adjRep_mem ha hd hcop D hD)
  exact TauCeti.isFiniteRelIndex_conj_mapGL (G := Gamma N) (H := Gamma N)

theorem isFiniteRelIndex_adj : (ConjAct.toConjAct (adjugateGL (φ ((Quotient.out D : DeltaN N) : GL (Fin 2) ℚ)))⁻¹ •
    (Gamma N).map (mapGL ℝ)).IsFiniteRelIndex ((Gamma N).map (mapGL ℝ)) := by
  rw [level_eq hcop D]; exact isFiniteRelIndex_adjRep ha hd hcop D hD

/-- **The adjoint double coset**: for `g` of character `ε`, the double coset operator of `α^ι` is
`ε(ad)⁻¹ [Γ(N) α Γ(N)]`. -/
theorem coe_trace_translate_adj (k : ℕ) {ε : (ZMod N)ˣ →* ℂˣ} (g : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k))
    (hg : g ∈ charSpaceN N k ε) :
    let _ := isFiniteRelIndex_adj ha hd hcop D hD
    ⇑(SlashInvariantForm.trace ((Gamma N).map (mapGL ℝ))
        (SlashInvariantForm.translate g (adjugateGL (φ ((Quotient.out D : DeltaN N) : GL (Fin 2) ℚ))))) =
      ((ε (ZMod.unitOfCoprime (a * d) hcop) : ℂ)⁻¹) •
        ⇑(heckeSlashModularFormEnd (2 * k) D (rep_mem_GLPos_DeltaN N D) g) := by
  intro _
  have := isFiniteRelIndex_adjRep ha hd hcop D hD
  have hδ := adjRep_mem ha hd hcop D hD
  have := TauCeti.finite_decompQuotient_inv_of_mem_doubleCoset hδ
  set u := ZMod.unitOfCoprime (a * d) hcop
  have hgρ : ⇑g ∣[(2 * k : ℤ)] mapGL ℝ (rhoN N (a * d) hcop) = ⇑(((ε u : ℂ)⁻¹) • g) := by
    have hdm := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hg u⁻¹)
    rw [rhoN, ← coe_diamondN, hdm, map_inv, Units.val_inv_eq_inv_val]
  have h1 : SlashInvariantForm.trace ((Gamma N).map (mapGL ℝ))
      (SlashInvariantForm.translate g (adjugateGL (φ ((Quotient.out D : DeltaN N) : GL (Fin 2) ℚ)))) =
      SlashInvariantForm.trace ((Gamma N).map (mapGL ℝ))
        (SlashInvariantForm.translate (((ε u : ℂ)⁻¹) • g) (φ (adjRep D hcop))) :=
    TauCeti.SlashInvariantForm.trace_eq_of_eq_of_coe_eq (level_eq hcop D) (by
      rw [SlashInvariantForm.coe_translate, SlashInvariantForm.coe_translate, adj_eq hcop D,
        SlashAction.slash_mul, hgρ])
  rw [h1, ← TauCeti.heckeSlashSum_eq_coe_trace_translate (2 * k) D hδ (Subgroup.map_mapGL (Gamma N))
    (Subgroup.map_mapGL (Gamma N)) (((ε u : ℂ)⁻¹) • g),
    ← coe_heckeSlashModularFormEnd (2 * k) D (rep_mem_GLPos_DeltaN N D), map_smul]
  rfl

end adjoint


/-! ### Proposition 5.37 -/

section main

variable [NeZero N]

theorem coe_cuspTrace_translate {k : ℤ} {𝒢 : Subgroup (GL (Fin 2) ℝ)} (x : GL (Fin 2) ℝ)
    [(ConjAct.toConjAct x⁻¹ • 𝒢).IsFiniteRelIndex 𝒢] (f : CuspForm 𝒢 k) :
    ⇑(CuspForm.trace 𝒢 (CuspForm.translate f x)) =
      ⇑(SlashInvariantForm.trace 𝒢 (SlashInvariantForm.translate f x)) := by
  rw [CuspForm.coe_trace, ← SlashInvariantForm.coe_trace]
  exact congrArg DFunLike.coe (TauCeti.SlashInvariantForm.trace_eq_of_eq_of_coe_eq rfl
    (by rw [CuspForm.coe_translate, SlashInvariantForm.coe_translate]))

theorem petersson_sum_right {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {ι : Type*} (s : Finset ι)
    (g : CuspForm (Γ.map (mapGL ℝ)) k) (F : ι → CuspForm (Γ.map (mapGL ℝ)) k) :
    CuspForm.peterssonInnerCosets g (∑ i ∈ s, F i) = ∑ i ∈ s, CuspForm.peterssonInnerCosets g (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h := CuspForm.peterssonInnerCosets_add_right g 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, CuspForm.peterssonInnerCosets_add_right, ih]

theorem petersson_sum_left {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {ι : Type*} (s : Finset ι)
    (F : ι → CuspForm (Γ.map (mapGL ℝ)) k) (f : CuspForm (Γ.map (mapGL ℝ)) k) :
    CuspForm.peterssonInnerCosets (∑ i ∈ s, F i) f = ∑ i ∈ s, CuspForm.peterssonInnerCosets (F i) f := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h := CuspForm.peterssonInnerCosets_add_left (0 : CuspForm (Γ.map (mapGL ℝ)) k) 0 f
    rw [add_zero] at h
    exact left_eq_add.mp h
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, CuspForm.peterssonInnerCosets_add_left, ih]

/-- A value of a character of a finite group lies on the unit circle: `conj (ε u)⁻¹ = ε u`. -/
theorem conj_inv_char (ε : (ZMod N)ˣ →* ℂˣ) (u : (ZMod N)ˣ) :
    (starRingEnd ℂ) ((ε u : ℂ)⁻¹) = (ε u : ℂ) := by
  have hpow : (ε u : ℂ) ^ Fintype.card (ZMod N)ˣ = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  have hn : ‖(ε u : ℂ)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hpow Fintype.card_ne_zero
  have hne : (ε u : ℂ) ≠ 0 := (ε u).ne_zero
  rw [map_inv₀, Complex.inv_def, Complex.conj_conj, Complex.normSq_eq_norm_sq, Complex.norm_conj, hn]
  simp


/-- **One double coset**: for `D = Γ(N) α Γ(N)` over `T(a, d)` and cusp forms `f`, `g` with `g` of character `ε`,
`⟪g, [D] f⟫ = ε(ad) ⟪[D] g, f⟫` (Tau Ceti's product, conjugate-linear in the first argument). -/
theorem petersson_heckeSlash {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (hcop : (a * d).Coprime N)
    (D : HeckeCoset (DeltaN N) (GammaGL N) (GammaGL N))
    (hD : ((Quotient.out D : DeltaN N) : GL (Fin 2) ℚ) ∈
      doubleCoset (natDiagGL 2 ![a, d]) (SLnZ 2 : Set (GL (Fin 2) ℚ)) (SLnZ 2))
    (k : ℕ) {ε : (ZMod N)ˣ →* ℂˣ} (f g : CuspForm ((Gamma N).map (mapGL ℝ)) (2 * k))
    (hg : (g : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)) ∈ charSpaceN N k ε) :
    CuspForm.peterssonInnerCosets g (heckeSlashCuspFormEnd (2 * k) D (rep_mem_GLPos_DeltaN N D) f) =
      (ε (ZMod.unitOfCoprime (a * d) hcop) : ℂ) *
        CuspForm.peterssonInnerCosets (heckeSlashCuspFormEnd (2 * k) D (rep_mem_GLPos_DeltaN N D) g) f := by
  set out : GL (Fin 2) ℚ := ((Quotient.out D : DeltaN N) : GL (Fin 2) ℚ) with hout
  have hδ0 : out ∈ doubleCoset out (GammaGL N : Set (GL (Fin 2) ℚ)) (GammaGL N) :=
    DoubleCoset.mem_doubleCoset_self _ _ _
  have := TauCeti.finite_decompQuotient_inv_of_mem_doubleCoset hδ0
  have i1 : (ConjAct.toConjAct (φ out)⁻¹ • (Gamma N).map (mapGL ℝ)).IsFiniteRelIndex
      ((Gamma N).map (mapGL ℝ)) := TauCeti.isFiniteRelIndex_conj_mapGL (G := Gamma N) (H := Gamma N)
  have i2 := isFiniteRelIndex_adj ha hd hcop D hD
  have hadj2 : adjugateGL (adjugateGL (φ out)) = φ out := Matrix.GeneralLinearGroup.adjugate_adjugate (by simp) _
  have i3 : (ConjAct.toConjAct (adjugateGL (adjugateGL (φ out)))⁻¹ • (Gamma N).map (mapGL ℝ)).IsFiniteRelIndex
      ((Gamma N).map (mapGL ℝ)) := by rw [hadj2]; exact i1
  have hdetpos : 0 < ((adjugateGL (φ out) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [Matrix.GeneralLinearGroup.coe_adjugate, Matrix.det_adjugate]
    simp only [Fintype.card_fin, Nat.add_one_sub_one, pow_one]
    have h := rep_mem_GLPos_DeltaN N D
    rw [Matrix.mem_glpos] at h
    have := ModularForm.det_map_ratCast_pos (g := out) (by simpa [Matrix.GeneralLinearGroup.val_det_apply] using h)
    exact this
  -- `[D] f` as a trace of a translate
  have hEf : heckeSlashCuspFormEnd (2 * k) D (rep_mem_GLPos_DeltaN N D) f =
      CuspForm.trace ((Gamma N).map (mapGL ℝ)) (CuspForm.translate f (adjugateGL (adjugateGL (φ out)))) := by
    apply DFunLike.coe_injective
    rw [coe_heckeSlashCuspFormEnd, coe_cuspTrace_translate,
      TauCeti.heckeSlashSum_eq_coe_trace_translate (2 * k) D hδ0 (Subgroup.map_mapGL (Gamma N))
        (Subgroup.map_mapGL (Gamma N)) f]
    exact congrArg DFunLike.coe (TauCeti.SlashInvariantForm.trace_eq_of_eq_of_coe_eq (by rw [hadj2])
      (by rw [SlashInvariantForm.coe_translate, SlashInvariantForm.coe_translate, hadj2]))
  -- the adjoint side
  have hEg : CuspForm.trace ((Gamma N).map (mapGL ℝ)) (CuspForm.translate g (adjugateGL (φ out))) =
      ((ε (ZMod.unitOfCoprime (a * d) hcop) : ℂ)⁻¹) • heckeSlashCuspFormEnd (2 * k) D (rep_mem_GLPos_DeltaN N D) g := by
    apply DFunLike.coe_injective
    rw [coe_cuspTrace_translate, FunLike.coe_smul, coe_heckeSlashCuspFormEnd]
    have h := coe_trace_translate_adj ha hd hcop D hD k (g : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)) hg
    rw [coe_heckeSlashModularFormEnd, ModularFormClass.coe_modularForm] at h
    rw [← h]
    exact congrArg DFunLike.coe (TauCeti.SlashInvariantForm.trace_eq_of_eq_of_coe_eq rfl
      (by rw [SlashInvariantForm.coe_translate, SlashInvariantForm.coe_translate]; rfl))
  have key := CuspForm.peterssonInnerCosets_trace_translate (k := 2 * k) (Γ₁ := Gamma N) (Γ₂ := Gamma N)
    hdetpos Iff.rfl g f
  rw [hEg, CuspForm.peterssonInnerCosets_smul_left, conj_inv_char, ← hEf] at key
  exact key.symm


theorem out_mem_dc_diag {a d : ℕ}
    (h : ∃ α : DeltaN N, α.1 ∈ doubleCoset (natDiagGL 2 ![a, d]) (SLnZ 2 : Set (GL (Fin 2) ℚ)) (SLnZ 2)) :
    ((Quotient.out (HeckeCoset.mk (GammaGL N) (GammaGL N) h.choose) : DeltaN N) : GL (Fin 2) ℚ) ∈
      doubleCoset (natDiagGL 2 ![a, d]) (SLnZ 2 : Set (GL (Fin 2) ℚ)) (SLnZ 2) := by
  have h1 : ((Quotient.out (HeckeCoset.mk (GammaGL N) (GammaGL N) h.choose) : DeltaN N) : GL (Fin 2) ℚ) ∈
      doubleCoset (h.choose : GL (Fin 2) ℚ) (GammaGL N : Set (GL (Fin 2) ℚ)) (GammaGL N) := by
    rw [← doubleCoset_out_mk]; exact DoubleCoset.mem_doubleCoset_self _ _ _
  have h2 := mem_dc_SL_of_mem_dc_Gamma h1
  rwa [DoubleCoset.doubleCoset_eq_of_mem h.choose_spec] at h2

theorem coe_sum_cusp {𝒢 : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {ι : Type*} (s : Finset ι)
    (F : ι → CuspForm 𝒢 k) : ⇑(∑ i ∈ s, F i) = ∑ i ∈ s, ⇑(F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, FunLike.coe_add, ih]

theorem coe_sum_mf {𝒢 : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {ι : Type*} (s : Finset ι)
    (F : ι → ModularForm 𝒢 k) : ⇑(∑ i ∈ s, F i) = ∑ i ∈ s, ⇑(F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, FunLike.coe_add, ih]

open Classical in
/-- The cusp-form summand of `T^N(n)` at `(a, d)`. -/
noncomputable def cuspTerm (k a d : ℕ) (f : CuspForm ((Gamma N).map (mapGL ℝ)) (2 * k)) :
    CuspForm ((Gamma N).map (mapGL ℝ)) (2 * k) :=
  if h : ∃ α : DeltaN N, α.1 ∈ doubleCoset (natDiagGL 2 ![a, d]) (SLnZ 2 : Set (GL (Fin 2) ℚ)) (SLnZ 2) then
    heckeSlashCuspFormEnd (2 * k) (HeckeCoset.mk (GammaGL N) (GammaGL N) h.choose)
      (rep_mem_GLPos_DeltaN N _) f
  else 0

theorem coe_heckeActN_heckeTN (k n : ℕ) (f : CuspForm ((Gamma N).map (mapGL ℝ)) (2 * k)) :
    ⇑(heckeActN N k (heckeTN N n) (f : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k))) =
      ⇑(∑ ad ∈ n.divisorsAntidiagonal.filter (fun ad ↦ ad.1 ∣ ad.2), cuspTerm k ad.1 ad.2 f) := by
  rw [heckeTN, map_sum, LinearMap.sum_apply, coe_sum_mf, coe_sum_cusp]
  refine Finset.sum_congr rfl fun ad _ ↦ ?_
  rw [heckeTNDiag, cuspTerm]
  split_ifs with h
  · rw [heckeActN, HeckeCosetModule.single]
    erw [Finsupp.linearCombination_single]
    rw [one_smul, coe_heckeSlashModularFormEnd, coe_heckeSlashCuspFormEnd, ModularFormClass.coe_modularForm]
  · rw [map_zero]; rfl

/-- **Milne, Proposition 5.37**, unconditionally: for cusp forms `f`, `g` of weight `2k` and character `ε` for
`Γ(N)` and `(n, N) = 1`, `⟨T(n)f, g⟩ = ε(n)⟨f, T(n)g⟩`. -/
@[kb "milne2017mf" "Section 5, Proposition 5.37 (pdf p. 85)"]
theorem peterssonHeckeLevelN (N : ℕ) [NeZero N] (k : ℕ) : PeterssonHeckeLevelN N k := by
  refine ⟨fun ε n hn0 hn f g F G _ hg hF hG ↦ ?_⟩
  classical
  set S := n.divisorsAntidiagonal.filter (fun ad : ℕ × ℕ ↦ ad.1 ∣ ad.2)
  have hFe : F = ∑ ad ∈ S, cuspTerm k ad.1 ad.2 f := DFunLike.coe_injective (hF.trans (coe_heckeActN_heckeTN k n f))
  have hGe : G = ∑ ad ∈ S, cuspTerm k ad.1 ad.2 g := DFunLike.coe_injective (hG.trans (coe_heckeActN_heckeTN k n g))
  rw [hFe, hGe, petersson_sum_right, petersson_sum_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ad had ↦ ?_
  obtain ⟨hmul, -⟩ := Nat.mem_divisorsAntidiagonal.mp (Finset.mem_filter.mp had).1
  have ha : 0 < ad.1 := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hmul; omega
  have hd : 0 < ad.2 := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hmul; omega
  have hcop : (ad.1 * ad.2).Coprime N := by rw [hmul]; exact hn
  have hex := exists_DeltaN_mem_diag N ha hd hcop
  have hu : ZMod.unitOfCoprime (ad.1 * ad.2) hcop = ZMod.unitOfCoprime n hn := by
    ext; simp [hmul]
  rw [cuspTerm, cuspTerm, dite_eq_left hex, dite_eq_left hex,
    petersson_heckeSlash ha hd hcop _ (out_mem_dc_diag hex) k f g hg, hu]

end main

end ModularFormsKB.Milne.UncondLevelN
