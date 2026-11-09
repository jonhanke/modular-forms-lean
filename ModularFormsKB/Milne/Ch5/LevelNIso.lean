import ModularFormsKB.Milne.Ch5.LevelN
import ModularFormsKB.Milne.Ch5.Matrices

/-!
# Milne, Chapter 5: proofs of Lemmas 5.33 and 5.34

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf pp. 83–84.

Milne cites Ogg 1969 (pp. IV-10, IV-13) for these lemmas. This file proves the named statements `HeckeLevelIso` and
`DiamondCommutesHecke` of `LevelN.lean`.
-/

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing HeckeRing.GLn HeckeRing.GL2
  DoubleCoset

open scoped MatrixGroups ModularForm Pointwise HeckeCosetModule

namespace ModularFormsKB.Milne

variable {N : ℕ}

/-- Chinese remainder for `SL₂(ℤ)`: for coprime `N, n`, any `u` is congruent mod `N` to some `s ≡ 1 mod n`. -/
theorem exists_sl_crt {N n : ℕ} (h : N.Coprime n) (u : SL(2, ℤ)) :
    ∃ s : SL(2, ℤ), s ∈ Gamma n ∧ u * s⁻¹ ∈ Gamma N := by
  obtain ⟨s, hs⟩ := Matrix.SpecialLinearGroup.map_intCast_zmod_prod_surjective h
    (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) u, 1)
  have h1 := congrArg Prod.fst hs
  have h2 := congrArg Prod.snd hs
  simp only [MonoidHom.prod_apply] at h1 h2
  refine ⟨s, h2, ?_⟩
  rw [Gamma_mem', map_mul, map_inv, h1]
  simp

/-- If `s ≡ 1 mod n` and `det A = n`, then `A⁻¹ s A` is integral of determinant one. -/
theorem exists_sl_conj (A : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) (hn : A.det = n) (hn0 : 0 < n)
    (s : SL(2, ℤ)) (hs : s ∈ Gamma n) :
    ∃ w : SL(2, ℤ), (s : Matrix (Fin 2) (Fin 2) ℤ) * A = A * (w : Matrix (Fin 2) (Fin 2) ℤ) := by
  have hdvd : ∀ i j, (n : ℤ) ∣ ((s : Matrix (Fin 2) (Fin 2) ℤ) - 1) i j := by
    intro i j
    have h := congrArg (fun x : SL(2, ZMod n) => (x : Matrix (Fin 2) (Fin 2) (ZMod n)) i j) hs
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Matrix.sub_apply, Int.cast_sub]
    simp only [SL_reduction_mod_hom_val, Matrix.SpecialLinearGroup.coe_one] at h
    rw [sub_eq_zero]
    rw [h]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  choose M hM using hdvd
  let Mm : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of M
  have hsM : (s : Matrix (Fin 2) (Fin 2) ℤ) = 1 + (n : ℤ) • Mm := by
    ext i j
    have := hM i j
    simp only [Matrix.sub_apply] at this
    simp only [Matrix.add_apply, Matrix.smul_apply, Mm, Matrix.of_apply, smul_eq_mul]
    linarith
  let W : Matrix (Fin 2) (Fin 2) ℤ := 1 + A.adjugate * Mm * A
  have hAW : A * W = (s : Matrix (Fin 2) (Fin 2) ℤ) * A := by
    have h1 : A * (A.adjugate * Mm * A) = (n : ℤ) • (Mm * A) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_adjugate, hn, Matrix.smul_mul,
        Matrix.one_mul, Matrix.smul_mul]
    rw [hsM, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
    simp only [W, Matrix.mul_add, Matrix.mul_one, h1]
  have hdetW : W.det = 1 := by
    have h2 := congrArg Matrix.det hAW
    rw [Matrix.det_mul, Matrix.det_mul, s.det_coe, one_mul] at h2
    have hA0 : A.det ≠ 0 := by rw [hn]; exact_mod_cast hn0.ne'
    exact mul_left_cancel₀ hA0 (by rw [h2, mul_one])
  exact ⟨⟨W, hdetW⟩, hAW.symm⟩

/-- The matrix of `mapGL ℚ σ` is the entrywise cast of `σ`. -/
theorem coe_mapGL_int (σ : SL(2, ℤ)) :
    ((mapGL ℚ σ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (σ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) := by
  ext i j; simp [mapGL_coe_matrix]

/-- A matrix with determinant prime to `N` is invertible mod `N`. -/
theorem isUnit_map_zmod {N : ℕ} (A : Matrix (Fin 2) (Fin 2) ℤ) (hc : IsCoprime A.det (N : ℤ)) :
    IsUnit (A.map (Int.cast : ℤ → ZMod N)) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h0 : (A.map (Int.cast : ℤ → ZMod N)).det = (A.det : ZMod N) := by
    exact (RingHom.map_det (Int.castRingHom (ZMod N)) A).symm
  rw [h0]
  obtain ⟨a, b, hab⟩ := hc
  have h := congrArg (Int.cast : ℤ → ZMod N) hab
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, add_zero,
    Int.cast_one] at h
  exact IsUnit.of_mul_eq_one (a : ZMod N) (by rw [mul_comm]; exact h)

/-- If `g, g σ ∈ Δ(N)` with `σ ∈ SL₂(ℤ)` then `σ ∈ Γ(N)`. -/
theorem mem_Gamma_of_mul_mem {N : ℕ} {g : GL (Fin 2) ℚ} (hg : g ∈ DeltaN N) (σ : SL(2, ℤ))
    (h : g * mapGL ℚ σ ∈ DeltaN N) : σ ∈ Gamma N := by
  obtain ⟨A, hA, hdA, hcA, hmA⟩ := hg
  obtain ⟨B, hB, hdB, hcB, hmB⟩ := h
  have hBA : B = A * (σ : Matrix (Fin 2) (Fin 2) ℤ) := by
    have : B.map (Int.cast : ℤ → ℚ) = (A * (σ : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → ℚ) := by
      rw [← hB, Units.val_mul, hA, Matrix.map_mul_intCast]
      simp
    exact Matrix.map_injective Int.cast_injective this
  have hdet : B.det = A.det := by rw [hBA, Matrix.det_mul, σ.det_coe, mul_one]
  have hu := isUnit_map_zmod (N := N) A hcA
  have h1 : A.map (Int.cast : ℤ → ZMod N) * (σ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) =
      A.map (Int.cast : ℤ → ZMod N) * 1 := by
    rw [← Matrix.map_mul_intCast, ← hBA, hmB, hdet, hmA, Matrix.mul_one]
  have h2 := hu.mul_left_cancel h1
  rw [Gamma_mem']
  ext i j
  have := congrFun (congrFun h2 i) j
  simpa [Matrix.one_apply] using this

/-- If `g, y ∈ Δ(N)`, `x ∈ Δ₀(N)` and `g x = y` then `x ∈ Δ(N)`. -/
theorem mem_DeltaN_of_mul_eq {N : ℕ} {g y x : GL (Fin 2) ℚ} (hg : g ∈ DeltaN N) (hy : y ∈ DeltaN N)
    (hx : x ∈ DeltaPrime N) (h : g * x = y) : x ∈ DeltaN N := by
  obtain ⟨A, hA, hdA, hcA, hmA⟩ := hg
  obtain ⟨C, hC, hdC, hcC, hmC⟩ := hy
  obtain ⟨X, hX, hdX, hcX⟩ := hx
  have hCA : C = A * X := by
    have : C.map (Int.cast : ℤ → ℚ) = (A * X).map (Int.cast : ℤ → ℚ) := by
      rw [← hC, ← h, Units.val_mul, hA, hX, Matrix.map_mul_intCast]
    exact Matrix.map_injective Int.cast_injective this
  have hdet : C.det = A.det * X.det := by rw [hCA, Matrix.det_mul]
  refine ⟨X, hX, hdX, hcX, ?_⟩
  have hu := isUnit_map_zmod (N := N) A hcA
  have h1 : A.map (Int.cast : ℤ → ZMod N) * X.map (Int.cast : ℤ → ZMod N) =
      A.map (Int.cast : ℤ → ZMod N) * !![1, 0; 0, (X.det : ZMod N)] := by
    rw [← Matrix.map_mul_intCast, ← hCA, hmC, hmA, hdet]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  exact hu.mul_left_cancel h1

/-- Elements of `Γ(N)` lie in `Δ(N)`. -/
theorem map_Gamma_mem_DeltaN [NeZero N] {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma N) : mapGL ℚ γ ∈ DeltaN N :=
  IsHeckeTriple.mem_of_mem_left ((Gamma N).map (mapGL ℚ)) (Subgroup.mem_map_of_mem _ hγ)

/-- **Key fact (Ogg)**: if `α, β ∈ Δ(N)` and `β = uαv` with `u, v ∈ SL₂(ℤ)` then `β ∈ Γ(N) α Γ(N)`. -/
theorem exists_Gamma_double_of_SL_double [NeZero N] {α β : GL (Fin 2) ℚ} (hα : α ∈ DeltaN N)
    (hβ : β ∈ DeltaN N) (u v : SL(2, ℤ)) (h : β = mapGL ℚ u * α * mapGL ℚ v) :
    ∃ u' ∈ Gamma N, ∃ z ∈ Gamma N, β = mapGL ℚ u' * α * mapGL ℚ z := by
  obtain ⟨A, hA, hdA, hcA, hmA⟩ := hα
  have hα' : α ∈ DeltaN N := ⟨A, hA, hdA, hcA, hmA⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, A.det = n := ⟨A.det.toNat, (Int.toNat_of_nonneg hdA.le).symm⟩
  have hn0 : 0 < n := by rw [hn] at hdA; exact_mod_cast hdA
  have hcop : N.Coprime n := by
    rw [hn] at hcA
    exact (Nat.isCoprime_iff_coprime.mp hcA.symm)
  obtain ⟨s, hs1, hs2⟩ := exists_sl_crt hcop u
  obtain ⟨w, hw⟩ := exists_sl_conj A n hn hn0 s hs1
  have hGL : mapGL ℚ s * α = α * mapGL ℚ w := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hA, coe_mapGL_int, coe_mapGL_int, ← Matrix.map_mul_intCast,
      ← Matrix.map_mul_intCast, hw]
  have hβ' : β = mapGL ℚ (u * s⁻¹) * α * mapGL ℚ (w * v) := by
    have e : mapGL ℚ (u * s⁻¹) * α * mapGL ℚ (w * v) =
        mapGL ℚ u * (mapGL ℚ s)⁻¹ * (α * mapGL ℚ w) * mapGL ℚ v := by
      simp only [map_mul, map_inv]; group
    rw [h, e, ← hGL]; group
  have hz : α * mapGL ℚ (w * v) = mapGL ℚ (u * s⁻¹)⁻¹ * β := by
    rw [hβ']; simp only [map_inv, map_mul]; group
  have hzmem : α * mapGL ℚ (w * v) ∈ DeltaN N := by
    rw [hz]
    exact mul_mem (map_Gamma_mem_DeltaN (inv_mem hs2)) hβ
  exact ⟨u * s⁻¹, hs2, w * v, mem_Gamma_of_mul_mem hα' _ hzmem, hβ'⟩


/-- **Ogg's lemma**: for `α, β ∈ Δ(N)`, `β ∈ Γ(1) α Γ(1)` implies `β ∈ Γ(N) α Γ(N)`. -/
theorem mem_doubleCoset_Gamma_of_SL [NeZero N] {α β : GL (Fin 2) ℚ} (hα : α ∈ DeltaN N)
    (hβ : β ∈ DeltaN N) (h : β ∈ doubleCoset α (SLnZ 2 : Set _) (SLnZ 2)) :
    β ∈ doubleCoset α (((Gamma N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set _)
      (((Gamma N).map (mapGL ℚ) : Subgroup (GL (Fin 2) ℚ)) : Set _) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_doubleCoset.mp h
  obtain ⟨u, rfl⟩ := (mem_SLnZ_iff 2).mp hx
  obtain ⟨v, rfl⟩ := (mem_SLnZ_iff 2).mp hy
  obtain ⟨u', hu', z, hz, e⟩ := exists_Gamma_double_of_SL_double hα hβ u v hxy
  exact mem_doubleCoset.mpr ⟨mapGL ℚ u', Subgroup.mem_map_of_mem _ hu', mapGL ℚ z,
    Subgroup.mem_map_of_mem _ hz, e⟩

/-- The map of Lemma 5.33 is injective on double cosets. -/
theorem toLevelOneCosetN_injective [NeZero N] : Function.Injective (toLevelOneCosetN N) := by
  intro D1 D2 h
  unfold toLevelOneCosetN at h
  have h' := HeckeCoset.eq_iff.mp h
  have hmem : ((D2.rep : DeltaN N) : GL (Fin 2) ℚ) ∈
      doubleCoset ((D1.rep : DeltaN N) : GL (Fin 2) ℚ) (SLnZ 2 : Set _) (SLnZ 2) := by
    have h2 : ((D2.rep : DeltaN N) : GL (Fin 2) ℚ) ∈
        doubleCoset ((D2.rep : DeltaN N) : GL (Fin 2) ℚ) (SLnZ 2 : Set _) (SLnZ 2) :=
      mem_doubleCoset_self _ _ _
    rw [← h'] at h2
    exact h2
  have := mem_doubleCoset_Gamma_of_SL D1.rep.2 D2.rep.2 hmem
  calc D1 = HeckeCoset.mk _ _ D1.rep := (HeckeCoset.mk_rep D1).symm
    _ = HeckeCoset.mk _ _ D2.rep := (HeckeCoset.mk_eq_mk_of_mem this).symm
    _ = D2 := HeckeCoset.mk_rep D2

/-- Every `Γ(1)`-double coset of `Δ₀(N)` contains an element of `Δ(N)` (Smith normal form). -/
theorem toLevelOneCosetN_surjective [NeZero N] : Function.Surjective (toLevelOneCosetN N) := by
  intro D'
  obtain ⟨A, hA, hdA, hcA⟩ := (D'.rep).2
  obtain ⟨n, hn⟩ : ∃ n : ℕ, A.det = n := ⟨A.det.toNat, (Int.toNat_of_nonneg hdA.le).symm⟩
  have hn0 : 0 < n := by rw [hn] at hdA; exact_mod_cast hdA
  obtain ⟨⟨a, d⟩, ⟨hdvd, hprod, U, V, hAUV⟩, -⟩ := exists_unique_elementaryDivisors hn0 A hn
  simp only at hdvd hprod hAUV
  have ha : 0 < a := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hprod; omega
  have hd : 0 < d := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hprod; omega
  have hcop : (a * d).Coprime N := by
    rw [hprod]; rw [hn] at hcA; exact Nat.isCoprime_iff_coprime.mp hcA
  have ha' : ∀ i, 0 < (![a, d] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simpa
  have hDq : (↑(natDiagGL 2 ![a, d]) : Matrix (Fin 2) (Fin 2) ℚ) =
      (Matrix.diagonal (fun i ↦ ((![a, d] : Fin 2 → ℕ) i : ℤ))).map (Int.cast : ℤ → ℚ) :=
    natDiagGL_coe_eq_map_intCast 2 _ ha'
  have hD : (Matrix.diagonal ![(a : ℤ), (d : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) =
      Matrix.diagonal (fun i ↦ ((![a, d] : Fin 2 → ℕ) i : ℤ)) := by
    congr 1; funext i; fin_cases i <;> simp
  have hg : ((D'.rep : DeltaPrime N) : GL (Fin 2) ℚ) ∈
      doubleCoset (natDiagGL 2 ![a, d]) (SLnZ 2 : Set _) (SLnZ 2) := by
    refine mem_doubleCoset.mpr ⟨mapGL ℚ U, coe_mem_SLnZ 2 U, mapGL ℚ V, coe_mem_SLnZ 2 V, ?_⟩
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hA, coe_mapGL_int, coe_mapGL_int, hDq, ← hD,
      ← Matrix.map_mul_intCast, ← Matrix.map_mul_intCast, hAUV]
  obtain ⟨α, hα⟩ := exists_DeltaN_mem_diag N ha hd hcop
  refine ⟨HeckeCoset.mk _ _ α, ?_⟩
  rw [toLevelOneCosetN_eq_of_mem N α (natDiagGL_mem_DeltaPrime N ha hd hcop) hα]
  calc levelOneDiagCoset N (natDiagGL_mem_DeltaPrime N ha hd hcop)
      = HeckeCoset.mk _ _ (D'.rep : DeltaPrime N) :=
        HeckeCoset.mk_eq_mk_of_mem (mem_doubleCoset.mpr (by
          obtain ⟨x, hx, y, hy, e⟩ := mem_doubleCoset.mp hg
          refine ⟨x⁻¹, inv_mem hx, y⁻¹, inv_mem hy, ?_⟩
          rw [e]; group))
    _ = D' := HeckeCoset.mk_rep D'

/-- Lemma 5.33, bijectivity part. -/
theorem heckeLevelMap_bijective [NeZero N] : Function.Bijective (heckeLevelMap N) :=
  ⟨Finsupp.mapDomain_injective (toLevelOneCosetN_injective (N := N)),
    Finsupp.mapDomain_surjective (toLevelOneCosetN_surjective (N := N))⟩


/-- `Γ(N)` as a subgroup of `GL₂(ℚ)`. -/
abbrev GammaGL (N : ℕ) : Subgroup (GL (Fin 2) ℚ) := (Gamma N).map (mapGL ℚ)

theorem GammaGL_le_SLnZ (N : ℕ) : GammaGL N ≤ SLnZ 2 := by
  rintro _ ⟨γ, -, rfl⟩
  exact coe_mem_SLnZ 2 γ

/-- Membership in a conjugate subgroup. -/
theorem mem_conjAct_smul_iff {G : Type*} [Group G] (g x : G) (K : Subgroup G) :
    x ∈ ConjAct.toConjAct g • K ↔ g⁻¹ * x * g ∈ K := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, ConjAct.smul_def,
    ConjAct.ofConjAct_toConjAct, inv_inv]

/-- Conjugation by an element of `Δ₀(N)` preserves `Γ(1)` on `Γ(n)`, `n = det`. -/
theorem exists_conj_GL {N : ℕ} {g : GL (Fin 2) ℚ} (hg : g ∈ DeltaPrime N) :
    ∃ n : ℕ, 0 < n ∧ n.Coprime N ∧ ∀ s ∈ Gamma n, ∃ w : SL(2, ℤ), mapGL ℚ s * g = g * mapGL ℚ w := by
  obtain ⟨A, hA, hdA, hcA⟩ := hg
  obtain ⟨n, hn⟩ : ∃ n : ℕ, A.det = n := ⟨A.det.toNat, (Int.toNat_of_nonneg hdA.le).symm⟩
  have hn0 : 0 < n := by rw [hn] at hdA; exact_mod_cast hdA
  refine ⟨n, hn0, by rw [hn] at hcA; exact Nat.isCoprime_iff_coprime.mp hcA, fun s hs ↦ ?_⟩
  obtain ⟨w, hw⟩ := exists_sl_conj A n hn hn0 s hs
  refine ⟨w, Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, hA, coe_mapGL_int, coe_mapGL_int, ← Matrix.map_mul_intCast,
    ← Matrix.map_mul_intCast, hw]

/-- The comparison map `Γ(N)/(Γ(N) ∩ gΓ(N)g⁻¹) → Γ(1)/(Γ(1) ∩ gΓ(1)g⁻¹)`. -/
noncomputable def decompMap (N : ℕ) (g : GL (Fin 2) ℚ) :
    DecompQuotient (GammaGL N) (GammaGL N) g → DecompQuotient (SLnZ 2) (SLnZ 2) g :=
  Quotient.map' (Subgroup.inclusion (GammaGL_le_SLnZ N)) (fun a b hab ↦ by
    have hab' := QuotientGroup.leftRel_apply.mp hab
    refine QuotientGroup.leftRel_apply.mpr ?_
    rw [Subgroup.mem_subgroupOf, mem_conjAct_smul_iff] at hab' ⊢
    exact GammaGL_le_SLnZ N hab')

theorem decompMap_mk (N : ℕ) (g : GL (Fin 2) ℚ) (x : GammaGL N) :
    decompMap N g (QuotientGroup.mk x) = QuotientGroup.mk (Subgroup.inclusion (GammaGL_le_SLnZ N) x) :=
  rfl

theorem decompMap_injective [NeZero N] {g : GL (Fin 2) ℚ} (hg : g ∈ DeltaN N) :
    Function.Injective (decompMap N g) := by
  intro i j
  induction i using QuotientGroup.induction_on with | H x => ?_
  induction j using QuotientGroup.induction_on with | H y => ?_
  intro h
  have h' := QuotientGroup.eq.mp h
  apply QuotientGroup.eq.mpr
  rw [Subgroup.mem_subgroupOf, mem_conjAct_smul_iff] at h' ⊢
  have hγ : (x : GL (Fin 2) ℚ)⁻¹ * (y : GL (Fin 2) ℚ) ∈ GammaGL N := mul_mem (inv_mem x.2) y.2
  obtain ⟨w, hw⟩ := (mem_SLnZ_iff 2).mp h'
  have hwΔ : g * mapGL ℚ w ∈ DeltaN N := by
    have : g * mapGL ℚ w = (x : GL (Fin 2) ℚ)⁻¹ * (y : GL (Fin 2) ℚ) * g := by
      have h2 : g⁻¹ * ((x : GL (Fin 2) ℚ)⁻¹ * (y : GL (Fin 2) ℚ)) * g = mapGL ℚ w := hw.symm
      rw [← h2]; group
    rw [this]
    exact mul_mem (IsHeckeTriple.mem_of_mem_left (GammaGL N) hγ) hg
  have hwG := mem_Gamma_of_mul_mem hg w hwΔ
  have h3 : g⁻¹ * ((x : GL (Fin 2) ℚ)⁻¹ * (y : GL (Fin 2) ℚ)) * g = mapGL ℚ w := hw.symm
  show g⁻¹ * ((x : GL (Fin 2) ℚ)⁻¹ * (y : GL (Fin 2) ℚ)) * g ∈ GammaGL N
  rw [h3]
  exact Subgroup.mem_map_of_mem _ hwG

theorem decompMap_surjective [NeZero N] {g : GL (Fin 2) ℚ} (hg : g ∈ DeltaN N) :
    Function.Surjective (decompMap N g) := by
  intro j
  induction j using QuotientGroup.induction_on with | H y => ?_
  obtain ⟨σ, hσ⟩ := (mem_SLnZ_iff 2).mp y.2
  obtain ⟨n, hn0, hcop, hconj⟩ := exists_conj_GL (DeltaN_le_DeltaPrime N hg)
  obtain ⟨s, hs1, hs2⟩ := exists_sl_crt hcop.symm σ
  obtain ⟨w, hw⟩ := hconj s hs1
  refine ⟨QuotientGroup.mk ⟨mapGL ℚ (σ * s⁻¹), Subgroup.mem_map_of_mem _ hs2⟩, ?_⟩
  rw [decompMap_mk]
  apply QuotientGroup.eq.mpr
  rw [Subgroup.mem_subgroupOf, mem_conjAct_smul_iff]
  have h1 : (((Subgroup.inclusion (GammaGL_le_SLnZ N) ⟨mapGL ℚ (σ * s⁻¹), Subgroup.mem_map_of_mem _ hs2⟩)⁻¹ * y :
      SLnZ 2) : GL (Fin 2) ℚ) = mapGL ℚ s := by
    show (mapGL ℚ (σ * s⁻¹))⁻¹ * (y : GL (Fin 2) ℚ) = _
    rw [← hσ]; simp
  rw [h1, mul_assoc, hw, inv_mul_cancel_left]
  exact coe_mem_SLnZ 2 w


/-- The representatives of corresponding cosets differ by an element of `Γ(1)` on the right of `g`. -/
theorem decompMap_out (N : ℕ) (g : GL (Fin 2) ℚ) (i : DecompQuotient (GammaGL N) (GammaGL N) g) :
    ∃ w ∈ SLnZ 2, (((decompMap N g i).out : SLnZ 2) : GL (Fin 2) ℚ) * g =
      ((i.out : GammaGL N) : GL (Fin 2) ℚ) * g * w := by
  have h1 : (QuotientGroup.mk (decompMap N g i).out : DecompQuotient (SLnZ 2) (SLnZ 2) g) =
      QuotientGroup.mk (Subgroup.inclusion (GammaGL_le_SLnZ N) i.out) :=
    calc (QuotientGroup.mk (decompMap N g i).out : DecompQuotient (SLnZ 2) (SLnZ 2) g)
        = decompMap N g i := QuotientGroup.out_eq' _
      _ = decompMap N g (QuotientGroup.mk i.out) := by rw [QuotientGroup.out_eq']
      _ = _ := decompMap_mk N g i.out
  have h2 := QuotientGroup.eq.mp h1
  rw [Subgroup.mem_subgroupOf, mem_conjAct_smul_iff] at h2
  refine ⟨(g⁻¹ * ((((decompMap N g i).out : SLnZ 2) : GL (Fin 2) ℚ)⁻¹ *
    ((i.out : GammaGL N) : GL (Fin 2) ℚ)) * g)⁻¹, inv_mem h2, ?_⟩
  group

/-- Double cosets for `Γ(N)` sit inside those for `Γ(1)`. -/
theorem mem_dc_SL_of_mem_dc_Gamma {N : ℕ} {h x : GL (Fin 2) ℚ}
    (hx : x ∈ doubleCoset h (GammaGL N : Set _) (GammaGL N)) :
    x ∈ doubleCoset h (SLnZ 2 : Set _) (SLnZ 2) := by
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_doubleCoset.mp hx
  exact mem_doubleCoset.mpr ⟨p, GammaGL_le_SLnZ N hp, q, GammaGL_le_SLnZ N hq, rfl⟩

/-- Left multiplication by an element of the left group preserves a double coset. -/
theorem mul_mem_doubleCoset_left {G : Type*} [Group G] {H K : Subgroup G} {h x w : G} (hw : w ∈ H)
    (hx : x ∈ doubleCoset h (H : Set G) K) : w * x ∈ doubleCoset h (H : Set G) K := by
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_doubleCoset.mp hx
  exact mem_doubleCoset.mpr ⟨w * p, mul_mem hw hp, q, hq, by group⟩

/-- The level-one decomposition quotient of `g ∈ Δ(N)` is finite. -/
theorem finite_decomp_SL (g : DeltaN N) : Finite (DecompQuotient (SLnZ 2) (SLnZ 2) (g : GL (Fin 2) ℚ)) :=
  haveI : Fintype (DecompQuotient (SLnZ 2) (SLnZ 2) (g : GL (Fin 2) ℚ)) :=
    (inferInstance : Fintype (DecompQuotient (SLnZ 2) (SLnZ 2)
      ((⟨g, DeltaN_le_DeltaPrime N g.2⟩ : DeltaPrime N) : GL (Fin 2) ℚ)))
  Finite.of_fintype _

/-- **The structure constants at level `N` and level one agree** (Ogg): for `g, h, d ∈ Δ(N)`,
`m_{Γ(N)}(g, h; d) = m_{Γ(1)}(g, h; d)`. -/
theorem multiplicity_GammaGL_eq [NeZero N] (g h d : DeltaN N) :
    multiplicity (GammaGL N) (GammaGL N) (GammaGL N) (g : GL (Fin 2) ℚ) h d =
      multiplicity (SLnZ 2) (SLnZ 2) (SLnZ 2) (g : GL (Fin 2) ℚ) h d := by
  classical
  have _ := finite_decomp_SL g
  have _ := finite_decomp_SL h
  rw [multiplicity_eq_card_filter, multiplicity_eq_card_filter]
  refine Nat.card_congr (Equiv.subtypeEquiv
    (Equiv.ofBijective _ ⟨decompMap_injective g.2, decompMap_surjective g.2⟩) fun i ↦ ?_)
  obtain ⟨w, hw, hbw⟩ := decompMap_out N g i
  have hx : ((((decompMap N g i).out : SLnZ 2) : GL (Fin 2) ℚ) * g)⁻¹ * d =
      w⁻¹ * ((((i.out : GammaGL N) : GL (Fin 2) ℚ) * g)⁻¹ * d) := by
    rw [hbw]; group
  show ((((i.out : GammaGL N) : GL (Fin 2) ℚ) * g)⁻¹ * d) ∈ doubleCoset (h : GL (Fin 2) ℚ) (GammaGL N : Set _)
      (GammaGL N) ↔ (((((decompMap N g i).out : SLnZ 2) : GL (Fin 2) ℚ) * g)⁻¹ * d) ∈
        doubleCoset (h : GL (Fin 2) ℚ) (SLnZ 2 : Set _) (SLnZ 2)
  rw [hx]
  constructor
  · intro hP
    exact mul_mem_doubleCoset_left (inv_mem hw) (mem_dc_SL_of_mem_dc_Gamma hP)
  · intro hP
    have hP' : ((((i.out : GammaGL N) : GL (Fin 2) ℚ) * g)⁻¹ * d) ∈
        doubleCoset (h : GL (Fin 2) ℚ) (SLnZ 2 : Set _) (SLnZ 2) := by
      have := mul_mem_doubleCoset_left (H := SLnZ 2) (K := SLnZ 2) hw hP
      rwa [mul_inv_cancel_left] at this
    have hag : ((i.out : GammaGL N) : GL (Fin 2) ℚ) * g ∈ DeltaN N :=
      mul_mem (IsHeckeTriple.mem_of_mem_left (GammaGL N) i.out.2) g.2
    have hxP : ((((i.out : GammaGL N) : GL (Fin 2) ℚ) * g)⁻¹ * d) ∈ DeltaPrime N :=
      mem_DeltaPrime_of_mem_doubleCoset N ⟨h, DeltaN_le_DeltaPrime N h.2⟩ hP'
    have hxN := mem_DeltaN_of_mul_eq hag d.2 hxP (by group)
    exact mem_doubleCoset_Gamma_of_SL h.2 hxN hP'


theorem heckeLevelMap_single [NeZero N] (D : HeckeCoset (DeltaN N) (GammaGL N) (GammaGL N)) (c : ℤ) :
    heckeLevelMap N (HeckeCosetModule.single ℤ D c) =
      HeckeCosetModule.single ℤ (toLevelOneCosetN N D) c :=
  (Finsupp.lmapDomain_apply _ _ (toLevelOneCosetN N) _).trans Finsupp.mapDomain_single

/-- Structure constants of `H(Γ(1), Δ₀(N))` depend on the representatives only through their double cosets. -/
theorem structureConstants_SL_congr (g₁ g₂ g₁' g₂' : DeltaPrime N)
    (h₁ : (g₁' : GL (Fin 2) ℚ) ∈ doubleCoset (g₁ : GL (Fin 2) ℚ) (SLnZ 2 : Set _) (SLnZ 2))
    (h₂ : (g₂' : GL (Fin 2) ℚ) ∈ doubleCoset (g₂ : GL (Fin 2) ℚ) (SLnZ 2 : Set _) (SLnZ 2)) :
    HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2) g₁' g₂' =
      HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2) g₁ g₂ := by
  apply inclHecke_injective N
  rw [inclHecke_structureConstants N g₁ g₂ ⟨g₁', DeltaPrime_le_posDetInt N g₁'.2⟩
      ⟨g₂', DeltaPrime_le_posDetInt N g₂'.2⟩ h₁ h₂,
    inclHecke_structureConstants N g₁' g₂' ⟨g₁', DeltaPrime_le_posDetInt N g₁'.2⟩
      ⟨g₂', DeltaPrime_le_posDetInt N g₂'.2⟩ (mem_doubleCoset_self _ _ _) (mem_doubleCoset_self _ _ _)]

/-- The map of Lemma 5.33 carries structure constants to structure constants. -/
theorem heckeLevelMap_structureConstants [NeZero N] (g₁ g₂ : DeltaN N) :
    heckeLevelMap N (HeckeCosetModule.structureConstants ℤ (GammaGL N) (GammaGL N) (GammaGL N) g₁ g₂) =
      HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2)
        (⟨g₁, DeltaN_le_DeltaPrime N g₁.2⟩ : DeltaPrime N) ⟨g₂, DeltaN_le_DeltaPrime N g₂.2⟩ := by
  ext D'
  obtain ⟨D, rfl⟩ := toLevelOneCosetN_surjective (N := N) D'
  have e : ∀ X : 𝕋 (DeltaN N) (GammaGL N) ℤ, heckeLevelMap N X (toLevelOneCosetN N D) = X D := fun X ↦
    Finsupp.mapDomain_apply_of_injective (toLevelOneCosetN_injective (N := N)) (X : _ →₀ ℤ) D
  rw [e, HeckeCosetModule.structureConstants_apply, HeckeCosetModule.structureConstants_apply]
  congr 1
  have h1 := multiplicity_GammaGL_eq g₁ g₂ D.rep
  have h2 := multiplicity_doubleCoset_congr (Γ₁ := SLnZ 2) (Γ₂ := SLnZ 2) (Γ₃ := SLnZ 2)
    (g₁ : GL (Fin 2) ℚ) (g₂ : GL (Fin 2) ℚ)
    (HeckeCoset.mem_doubleCoset_rep_mk (⟨D.rep, DeltaN_le_DeltaPrime N D.rep.2⟩ : DeltaPrime N))
  exact h1.trans h2

/-- Lemma 5.33, multiplicativity part. -/
theorem heckeLevelMap_mul [NeZero N] (x y : 𝕋 (DeltaN N) (GammaGL N) ℤ) :
    heckeLevelMap N (x * y) = heckeLevelMap N x * heckeLevelMap N y := by
  induction x using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd f₁ f₂ h₁ h₂ => rw [add_mul, map_add, map_add, add_mul, h₁, h₂]
  | hsingle D₁ a =>
    induction y using HeckeCosetModule.induction_linear with
    | h0 => simp
    | hadd g₁ g₂ h₁ h₂ => rw [mul_add, map_add, map_add, mul_add, h₁, h₂]
    | hsingle D₂ b =>
      rw [HeckeCosetModule.single_mul_single, heckeLevelMap_single, heckeLevelMap_single,
        HeckeCosetModule.single_mul_single, map_smul, map_smul,
        heckeLevelMap_structureConstants]
      exact congrArg (a • b • ·) (structureConstants_SL_congr _ _ _ _
        (HeckeCoset.rep_mk_mem_doubleCoset (⟨D₁.rep, DeltaN_le_DeltaPrime N D₁.rep.2⟩ : DeltaPrime N))
        (HeckeCoset.rep_mk_mem_doubleCoset (⟨D₂.rep, DeltaN_le_DeltaPrime N D₂.rep.2⟩ : DeltaPrime N))).symm

/-- **Milne, Lemma 5.33** (proved; Milne: "Elementary. (See Ogg 1969, p. IV-10.)"): the map
$\Gamma(N)\alpha\Gamma(N) \mapsto \Gamma(1)\alpha\Gamma(1)$ is a ring isomorphism
$H(\Gamma(N), \Delta(N)) \to H(\Gamma(1), \Delta_0(N))$. Injectivity on double cosets is Ogg's argument (Chinese
remainder theorem in `SL₂(ℤ)`), surjectivity is Smith normal form, and multiplicativity follows from the equality of
the structure constants `multiplicity_GammaGL_eq`. -/
@[kb "milne2017mf" "Section 5, Lemma 5.33 (pdf p. 83)"]
theorem heckeLevelIso (N : ℕ) [NeZero N] : HeckeLevelIso N :=
  ⟨heckeLevelMap_bijective, heckeLevelMap_mul⟩

/-- **Relation (10)** (p. 83), unconditionally: in $H(\Gamma(N), \Delta(N))$,
$T^N(n)T^N(m) = \sum_{d \mid (n, m)} d\,T^N(d, d)\,T^N(mn/d^2)$ for $m, n \ge 1$ with $(mn, N) = 1$. -/
@[kb "milne2017mf" "Section 5, relation (10) (pdf p. 83)"]
theorem heckeTN_mul_heckeTN_of_coprime (N : ℕ) [NeZero N] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hcop : (m * n).Coprime N) :
    heckeTN N n * heckeTN N m =
      ∑ d ∈ (Nat.gcd n m).divisors, (d : ℤ) • (heckeTNDiag N d d * heckeTN N (m * n / d ^ 2)) :=
  heckeTN_mul_heckeTN N (heckeLevelIso N) hm hn hcop

end ModularFormsKB.Milne
