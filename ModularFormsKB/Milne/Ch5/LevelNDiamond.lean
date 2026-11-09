import ModularFormsKB.Milne.Ch5.LevelNIso
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Trace

/-!
# Milne, Chapter 5: proof of Lemma 5.34

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf p. 84.

Every operator $R_d$ commutes with the action of every double coset $\Gamma(N)\alpha\Gamma(N)$, $\alpha \in \Delta(N)$
(`diamondN_commute_heckeSlash`), because $R_d^{-1}\alpha R_d \in \Gamma(N)\alpha\Gamma(N)$ (Ogg's lemma). The named
statement `DiamondCommutesHecke` follows by linearity.
-/

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing HeckeRing.GLn HeckeRing.GL2
  DoubleCoset

open scoped MatrixGroups ModularForm Pointwise HeckeCosetModule

namespace ModularFormsKB.Milne

local notation "φ" => Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℚ ℝ)

/-- Conjugating an element of `Δ(N)` by a lift `σ ∈ SL₂(ℤ)` of `diag(d⁻¹, d)` stays in `Δ(N)`. -/
theorem conj_mem_DeltaN {N : ℕ} [NeZero N] (d : (ZMod N)ˣ) (σ : SL(2, ℤ))
    (hσ : (σ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) =
      !![((d⁻¹ : (ZMod N)ˣ) : ZMod N), 0; 0, (d : ZMod N)])
    {α : GL (Fin 2) ℚ} (hα : α ∈ DeltaN N) :
    (mapGL ℚ σ)⁻¹ * α * mapGL ℚ σ ∈ DeltaN N := by
  obtain ⟨A, hA, hdA, hcA, hmA⟩ := hα
  have hdet : (((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * A * (σ : Matrix (Fin 2) (Fin 2) ℤ)).det
      = A.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe,
      Matrix.SpecialLinearGroup.det_coe, one_mul, mul_one]
  have h00 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod N) = ((d⁻¹ : (ZMod N)ˣ) : ZMod N) := by
    simpa using congrFun (congrFun hσ 0) 0
  have h01 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod N) = 0 := by
    simpa using congrFun (congrFun hσ 0) 1
  have h10 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0 := by
    simpa using congrFun (congrFun hσ 1) 0
  have h11 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod N) = (d : ZMod N) := by
    simpa using congrFun (congrFun hσ 1) 1
  have h1 : ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) =
      !![(d : ZMod N), 0; 0, ((d⁻¹ : (ZMod N)ˣ) : ZMod N)] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  refine ⟨((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * A * (σ : Matrix (Fin 2) (Fin 2) ℤ), ?_, ?_, ?_, ?_⟩
  · rw [← map_inv, Units.val_mul, Units.val_mul, hA, coe_mapGL_int, coe_mapGL_int,
      ← Matrix.map_mul_intCast, ← Matrix.map_mul_intCast]
  · rw [hdet]; exact hdA
  · rw [hdet]; exact hcA
  · have h : (((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * A *
        (σ : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → ZMod N) =
        ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) *
          A.map (Int.cast : ℤ → ZMod N) * (σ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) := by
      rw [Matrix.map_mul_intCast, Matrix.map_mul_intCast]
    rw [h, h1, hmA, hσ, hdet]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Units.mul_inv]
    rw [mul_right_comm, Units.inv_mul, one_mul]

/-- `φ` sends `mapGL ℚ σ` to `mapGL ℝ σ`. -/
theorem map_mapGL_rat_real (σ : SL(2, ℤ)) : φ (mapGL ℚ σ) = mapGL ℝ σ := by
  refine Units.ext ?_
  ext i j
  simp [mapGL_coe_matrix, Matrix.GeneralLinearGroup.map]

/-- `Γ(1)` normalizes `Γ(N)`, as subgroups of `GL₂(ℝ)`, in the form needed for `normalizer`. -/
theorem mapGL_mem_normalizer_Gamma_map (N : ℕ) (σ : SL(2, ℤ)) :
    mapGL ℝ σ ∈ Subgroup.normalizer (((Gamma N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) :
      Set (GL (Fin 2) ℝ)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨σ * y * σ⁻¹, (Gamma_normal N).conj_mem y hy σ, by simp⟩
  · rintro ⟨y, hy, hxy⟩
    refine ⟨σ⁻¹ * y * σ, (Gamma_normal N).conj_mem y hy σ⁻¹ |> fun h' => ?_, ?_⟩
    · simpa using h'
    · have : h = (mapGL ℝ σ)⁻¹ * (mapGL ℝ y) * mapGL ℝ σ := by
        have : mapGL ℝ y = mapGL ℝ σ * h * (mapGL ℝ σ)⁻¹ := hxy
        rw [this]; group
      rw [this]
      simp

/-- Pointwise formula for `R_d`. -/
theorem coe_diamondN (N : ℕ) [NeZero N] (k : ℕ) (d : (ZMod N)ˣ)
    (f : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)) :
    ⇑(diamondN N k d f) = ⇑f ∣[(2 * k : ℤ)] mapGL ℝ (exists_diamondRep N d).choose :=
  funext fun z ↦ mcast_translate_apply_N N k _ f z

/-- Core computation: if `g = f | σ` then `(T f) | σ = T g` for every double coset operator `T`. -/
theorem slash_heckeEnd_eq (N : ℕ) [NeZero N] (k : ℕ) (d : (ZMod N)ˣ) (σ : SL(2, ℤ))
    (hσ : (σ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) =
      !![((d⁻¹ : (ZMod N)ˣ) : ZMod N), 0; 0, (d : ZMod N)])
    (D : HeckeCoset (DeltaN N) ((Gamma N).map (mapGL ℚ)) ((Gamma N).map (mapGL ℚ)))
    (f g : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k))
    (hg : ⇑g = ⇑f ∣[(2 * k : ℤ)] mapGL ℝ σ) :
    ⇑(heckeSlashModularFormEnd (2 * k) D (rep_mem_GLPos_DeltaN N D) f) ∣[(2 * k : ℤ)] mapGL ℝ σ =
      ⇑(heckeSlashModularFormEnd (2 * k) D (rep_mem_GLPos_DeltaN N D) g) := by
  classical
  simp only [coe_heckeSlashModularFormEnd]
  have hδ0 : (D.out : GL (Fin 2) ℚ) ∈ doubleCoset (D.out : GL (Fin 2) ℚ)
      ((Gamma N).map (mapGL ℚ)) ((Gamma N).map (mapGL ℚ)) :=
    DoubleCoset.mem_doubleCoset_self _ _ _
  have hδ'N := conj_mem_DeltaN d σ hσ (D.out).2
  have hδ' : (mapGL ℚ σ)⁻¹ * (D.out : GL (Fin 2) ℚ) * mapGL ℚ σ ∈ doubleCoset (D.out : GL (Fin 2) ℚ)
      ((Gamma N).map (mapGL ℚ)) ((Gamma N).map (mapGL ℚ)) :=
    mem_doubleCoset_Gamma_of_SL (D.out).2 hδ'N
      (mem_doubleCoset.mpr ⟨(mapGL ℚ σ)⁻¹, (SLnZ 2).inv_mem (coe_mem_SLnZ 2 σ), mapGL ℚ σ,
        coe_mem_SLnZ 2 σ, rfl⟩)
  have e : φ (D.out : GL (Fin 2) ℚ) * mapGL ℝ σ =
      mapGL ℝ σ * φ ((mapGL ℚ σ)⁻¹ * (D.out : GL (Fin 2) ℚ) * mapGL ℚ σ) := by
    rw [map_mul, map_mul, map_inv, map_mapGL_rat_real]
    group
  have hlevel : ConjAct.toConjAct (φ (D.out : GL (Fin 2) ℚ) * mapGL ℝ σ)⁻¹ •
      (Gamma N).map (mapGL ℝ) =
      ConjAct.toConjAct (φ ((mapGL ℚ σ)⁻¹ * (D.out : GL (Fin 2) ℚ) * mapGL ℚ σ))⁻¹ •
      (Gamma N).map (mapGL ℝ) := by
    rw [e, _root_.mul_inv_rev, ConjAct.toConjAct_mul, mul_smul, conj_Gamma_map N σ]
  have := TauCeti.finite_decompQuotient_inv_of_mem_doubleCoset hδ0
  have : (ConjAct.toConjAct (φ (D.out : GL (Fin 2) ℚ))⁻¹ • (Gamma N).map (mapGL ℝ)).IsFiniteRelIndex
      ((Gamma N).map (mapGL ℝ)) := by
    exact TauCeti.isFiniteRelIndex_conj_mapGL (G := Gamma N) (H := Gamma N)
  have := TauCeti.finite_decompQuotient_inv_of_mem_doubleCoset hδ'
  have : (ConjAct.toConjAct
      (φ ((mapGL ℚ σ)⁻¹ * (D.out : GL (Fin 2) ℚ) * mapGL ℚ σ))⁻¹ • (Gamma N).map (mapGL ℝ)).IsFiniteRelIndex
      ((Gamma N).map (mapGL ℝ)) := by
    exact TauCeti.isFiniteRelIndex_conj_mapGL (G := Gamma N) (H := Gamma N)
  have : (ConjAct.toConjAct (φ (D.out : GL (Fin 2) ℚ) * mapGL ℝ σ)⁻¹ • (Gamma N).map (mapGL ℝ)).IsFiniteRelIndex
      ((Gamma N).map (mapGL ℝ)) := hlevel ▸ ‹_›
  rw [TauCeti.heckeSlashSum_eq_coe_trace_translate (2 * k) D hδ0
      (Subgroup.map_mapGL (Gamma N)) (Subgroup.map_mapGL (Gamma N)) f,
    TauCeti.heckeSlashSum_eq_coe_trace_translate (2 * k) D hδ'
      (Subgroup.map_mapGL (Gamma N)) (Subgroup.map_mapGL (Gamma N)) g,
    ← TauCeti.SlashInvariantForm.coe_trace_translate_mul_of_mem_normalizer f _
      (mapGL_mem_normalizer_Gamma_map N σ)]
  refine congrArg DFunLike.coe (TauCeti.SlashInvariantForm.trace_eq_of_eq_of_coe_eq hlevel ?_)
  rw [SlashInvariantForm.coe_translate, SlashInvariantForm.coe_translate, hg, ← SlashAction.slash_mul, e]

/-- Every `R_d` commutes with the action of every double coset of `H(Γ(N), Δ(N))` on `M_{2k}(Γ(N))`. -/
theorem diamondN_commute_heckeSlash (N : ℕ) [NeZero N] (k : ℕ) (d : (ZMod N)ˣ)
    (D : HeckeCoset (DeltaN N) ((Gamma N).map (mapGL ℚ)) ((Gamma N).map (mapGL ℚ))) :
    Commute (diamondN N k d) (heckeSlashModularFormEnd (2 * k) D (rep_mem_GLPos_DeltaN N D)) := by
  refine LinearMap.ext fun f ↦ DFunLike.coe_injective ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, coe_diamondN]
  simp only [coe_heckeSlashModularFormEnd]
  have := slash_heckeEnd_eq N k d (exists_diamondRep N d).choose (exists_diamondRep N d).choose_spec D f
    (diamondN N k d f) (coe_diamondN N k d f)
  simp only [coe_heckeSlashModularFormEnd] at this
  exact this

/-- **Milne, Lemma 5.34** (proved; Milne: "See Ogg 1969, p. IV-13"). The operators $R_d$ commute with every
double coset operator $[\Gamma(N)\alpha\Gamma(N)]$, $\alpha \in \Delta(N)$, hence with $T^N(m)$ (for every $m$, so in
particular for $(m, N) = 1$). The key point is that $R_d^{-1}\alpha R_d \in \Gamma(N)\alpha\Gamma(N)$ by Ogg's lemma
(`mem_doubleCoset_Gamma_of_SL`). -/
@[kb "milne2017mf" "Section 5, Lemma 5.34 (pdf p. 84)"]
theorem diamondCommutesHecke (N : ℕ) [NeZero N] (k : ℕ) : DiamondCommutesHecke N k := by
  refine ⟨fun d m _ ↦ ?_⟩
  have key : ∀ x : HeckeCosetModule (DeltaN N) ((Gamma N).map (mapGL ℚ)) ((Gamma N).map (mapGL ℚ)) ℤ,
      Commute (diamondN N k d) (heckeActN N k x) := by
    intro x
    refine HeckeCosetModule.induction_linear ℤ (p := fun x ↦ Commute (diamondN N k d) (heckeActN N k x)) x ?_ ?_ ?_
    · rw [map_zero]; exact Commute.zero_right _
    · intro x y hx hy
      rw [map_add]; exact hx.add_right hy
    · intro D c
      have h : heckeActN N k (HeckeCosetModule.single ℤ D c) =
          c • heckeSlashModularFormEnd (2 * k) D (rep_mem_GLPos_DeltaN N D) :=
        Finsupp.linearCombination_single ℤ _ _
      rw [h]
      exact Commute.smul_right (diamondN_commute_heckeSlash N k d D) c
  exact key _

/-- **Milne, Lemma 5.34**, consequence, unconditionally: $V(\varepsilon)$ is invariant under $T^N(m)$,
$(m, N) = 1$. -/
@[kb "milne2017mf" "Section 5, Lemma 5.34 (pdf p. 84)"]
theorem heckeActN_mem_charSpaceN_of_coprime (N : ℕ) [NeZero N] {k : ℕ} (ε : (ZMod N)ˣ →* ℂˣ)
    {m : ℕ} (hm : m.Coprime N) {f : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)} (hf : f ∈ charSpaceN N k ε) :
    heckeActN N k (heckeTN N m) f ∈ charSpaceN N k ε :=
  heckeActN_mem_charSpaceN N (diamondCommutesHecke N k) ε hm hf

end ModularFormsKB.Milne
