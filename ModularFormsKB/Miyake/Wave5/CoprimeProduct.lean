import ModularFormsKB.Miyake.Wave4.MiyakeHecke
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.CoprimeMul

/-!
# Miyake, Lemma 4.5.8 (1): `T(l, m) T(l', m') = T(l l', m m')` when `(l m, l' m') = 1`

Miyake, *Modular Forms* (Springer 1989), §4.5, p. 141.

The double-coset identity at level `Γ₀(N)`. The core case is `T(1, m) T(1, n) = T(1, m n)` for
coprime `m`, `n` (no condition relating `m` or `n` to `N`):

* every product of an element of `Γ₀(N) diag(1, m) Γ₀(N)` with one of `Γ₀(N) diag(1, n) Γ₀(N)` is
  primitive (its determinant `m n` has coprime factors), so it lies in `Γ₀(N) diag(1, mn) Γ₀(N)`
  (Tau Ceti `HeckeRing.GL2.mem_doubleCoset_natDiagGL_of_primitive`, Miyake Lemma 4.5.2);
* no left coset of the product is hit twice: if `x y Γ₀(N) = x' y' Γ₀(N)` then `x⁻¹ x'` is integral
  after scaling by `m` and after scaling by `n`, hence integral of determinant one, and it lies
  in `Γ₀(N)` by reading the congruences modulo `N` (the level-`Γ₀(N)`, left-coset form of
  Tau Ceti's `HeckeRing.GL2.op_smul_eq_of_op_mul_smul_eq` for `Γ₁(N)`).

The general case follows with the scalar row `T(c, c) T(a) = T(c a)`
(`HeckeRing.GL2.diagElemGamma0_const_mul`) and the commutativity of `ℛ(N)`.
-/

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups HeckeCosetModule

noncomputable section

namespace ModularFormsKB.Miyake.Wave5

open ModularFormsKB.Miyake.Wave4

/-- The double coset `Γ₀(N) diag(1, m) Γ₀(N)` as a subset of `GL₂(ℚ)`. -/
private abbrev DC (N m : ℕ) : Set (GL (Fin 2) ℚ) :=
  DoubleCoset.doubleCoset (HeckeRing.GLn.natDiagGL 2 ![1, m]) ((Gamma0 N).map (mapGL ℚ))
    ((Gamma0 N).map (mapGL ℚ))

/-- An integral `2 × 2` matrix whose entries have no common prime factor. -/
private def Prim (X : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬((p : ℤ) ∣ X 0 0 ∧ (p : ℤ) ∣ X 0 1 ∧ (p : ℤ) ∣ X 1 0 ∧ (p : ℤ) ∣ X 1 1)

private lemma dvd_mul_left_entries {p : ℤ} {X : Matrix (Fin 2) (Fin 2) ℤ}
    (A : Matrix (Fin 2) (Fin 2) ℤ) (h : ∀ i j, p ∣ X i j) (i j : Fin 2) : p ∣ (A * X) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ ↦ dvd_mul_of_dvd_right (h k j) _

private lemma dvd_mul_right_entries {p : ℤ} {X : Matrix (Fin 2) (Fin 2) ℤ}
    (B : Matrix (Fin 2) (Fin 2) ℤ) (h : ∀ i j, p ∣ X i j) (i j : Fin 2) : p ∣ (X * B) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ ↦ dvd_mul_of_dvd_left (h i k) _

private lemma forall_dvd_of_four {p : ℤ} {X : Matrix (Fin 2) (Fin 2) ℤ}
    (h : p ∣ X 0 0 ∧ p ∣ X 0 1 ∧ p ∣ X 1 0 ∧ p ∣ X 1 1) : ∀ i j, p ∣ X i j := by
  obtain ⟨h00, h01, h10, h11⟩ := h
  intro i j
  fin_cases i <;> fin_cases j <;> assumption

private lemma prim_mul {X Y : Matrix (Fin 2) (Fin 2) ℤ} {m n : ℕ} (hX : Prim X) (hY : Prim Y)
    (hdX : X.det = m) (hdY : Y.det = n) (hmn : m.Coprime n) : Prim (X * Y) := by
  intro p hp h
  have hall := forall_dvd_of_four h
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases hpn : (p : ℤ) ∣ n
  · have hpm : ¬ (p : ℤ) ∣ m := fun hpm ↦ hp.one_lt.ne' <| Nat.dvd_one.mp <|
      hmn ▸ Nat.dvd_gcd (Int.natCast_dvd_natCast.mp hpm) (Int.natCast_dvd_natCast.mp hpn)
    have h1 : ∀ i j, (p : ℤ) ∣ (m : ℤ) * Y i j := by
      intro i j
      have : (X.adjugate * (X * Y)) i j = (m : ℤ) * Y i j := by
        rw [← Matrix.mul_assoc, Matrix.adjugate_mul, hdX]
        simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul]
      rw [← this]; exact dvd_mul_left_entries _ hall i j
    exact hY p hp ⟨(hp'.dvd_or_dvd (h1 0 0)).resolve_left hpm,
      (hp'.dvd_or_dvd (h1 0 1)).resolve_left hpm,
      (hp'.dvd_or_dvd (h1 1 0)).resolve_left hpm, (hp'.dvd_or_dvd (h1 1 1)).resolve_left hpm⟩
  · have h1 : ∀ i j, (p : ℤ) ∣ (n : ℤ) * X i j := by
      intro i j
      have : (X * Y * Y.adjugate) i j = (n : ℤ) * X i j := by
        rw [Matrix.mul_assoc, Matrix.mul_adjugate, hdY]
        simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul]
      rw [← this]; exact dvd_mul_right_entries _ hall i j
    exact hX p hp ⟨(hp'.dvd_or_dvd (h1 0 0)).resolve_left hpn,
      (hp'.dvd_or_dvd (h1 0 1)).resolve_left hpn,
      (hp'.dvd_or_dvd (h1 1 0)).resolve_left hpn, (hp'.dvd_or_dvd (h1 1 1)).resolve_left hpn⟩

/-- Integral data of an element of `Γ₀(N) diag(1, m) Γ₀(N)`. -/
private lemma exists_int_data {N m : ℕ} (hm : 0 < m) {x : GL (Fin 2) ℚ} (hx : x ∈ DC N m) :
    ∃ X : Matrix (Fin 2) (Fin 2) ℤ, (↑x : Matrix (Fin 2) (Fin 2) ℚ) = X.map (Int.cast : ℤ → ℚ) ∧
      ((X 1 0 : ℤ) : ZMod N) = 0 ∧ IsUnit ((X 0 0 : ℤ) : ZMod N) ∧ X.det = m ∧ Prim X := by
  obtain ⟨_, ⟨g₁, hg₁, rfl⟩, _, ⟨g₂, hg₂, rfl⟩, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
  have hX := HeckeRing.GLn.mapGL_mul_coe_eq_intMatrix 2 g₁ g₂ _ _
    (HeckeRing.GL2.coe_natDiagGL_one_eq_map hm)
  have h1 := Gamma0_mem.mp hg₁
  have h2 := Gamma0_mem.mp hg₂
  refine ⟨_, hX, ?_, ?_, ?_, ?_⟩
  · simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2]
  · have : (((g₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (m : ℤ)] *
        (g₂ : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 : ZMod N) =
        (g₁ 0 0 : ZMod N) * (g₂ 0 0 : ZMod N) := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, h2]
    rw [this]
    exact (isUnit_iff_exists_inv.mpr ⟨_,
      intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hg₁⟩).mul
      (isUnit_iff_exists_inv.mpr ⟨_,
      intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hg₂⟩)
  · simp [Matrix.det_mul, Matrix.det_fin_two_of]
  · rintro p hp ⟨h00, h01, h10, h11⟩
    have hall := forall_dvd_of_four (X := ((g₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (m : ℤ)] *
        (g₂ : Matrix (Fin 2) (Fin 2) ℤ))) ⟨h00, h01, h10, h11⟩
    have e1 : ((g₁⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        (g₁ : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have e2 : (g₂ : Matrix (Fin 2) (Fin 2) ℤ) *
        ((g₂⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hD : ((g₁⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        ((g₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (m : ℤ)] *
          (g₂ : Matrix (Fin 2) (Fin 2) ℤ)) *
        ((g₂⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 0, (m : ℤ)] := by
      calc _ = (((g₁⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
            (g₁ : Matrix (Fin 2) (Fin 2) ℤ)) *
            !![1, 0; 0, (m : ℤ)] * ((g₂ : Matrix (Fin 2) (Fin 2) ℤ) *
            ((g₂⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [e1, e2]; simp
    have := dvd_mul_right_entries ((g₂⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      (dvd_mul_left_entries ((g₁⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) hall) 0 0
    rw [hD] at this
    exact (Nat.prime_iff_prime_int.mp hp).not_dvd_one (by simpa using this)

/-- Products of elements of `D_m` and `D_n` (coprime) lie in `D_{mn}`. -/
private lemma mul_mem_DC {N : ℕ} [NeZero N] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmn : m.Coprime n) {x y : GL (Fin 2) ℚ} (hx : x ∈ DC N m) (hy : y ∈ DC N n) :
    x * y ∈ DC N (m * n) := by
  obtain ⟨X, hX, hX10, hX00, hXd, hXp⟩ := exists_int_data hm hx
  obtain ⟨Y, hY, hY10, hY00, hYd, hYp⟩ := exists_int_data hn hy
  refine HeckeRing.GL2.mem_doubleCoset_natDiagGL_of_primitive N (m * n) (x * y) (X * Y) ?_ ?_ ?_ ?_
    (prim_mul hXp hYp hXd hYd hmn)
  · rw [Units.val_mul, hX, hY, Matrix.map_mul_intCast]
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp [Matrix.mul_apply, Fin.sum_univ_two, hX10, hY10]
  · apply Int.isUnit_intCast_iff_gcd_eq_one.mp
    have : (((X * Y) 0 0 : ℤ) : ZMod N) = (X 0 0 : ZMod N) * (Y 0 0 : ZMod N) := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, hY10]
    rw [this]; exact hX00.mul hY00
  · rw [Units.val_mul, Matrix.det_mul, hX, hY, ← Int.cast_det, ← Int.cast_det, hXd, hYd]
    push_cast; ring

/-- Left cosets: if `x y Γ = x' y' Γ` with `x, x' ∈ D_m`, `y, y' ∈ D_n`, `m, n` coprime, then
`x Γ = x' Γ`. -/
private lemma inv_mul_mem_of_mul_eq {N m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n)
    {x x' y y' : GL (Fin 2) ℚ} (hx : x ∈ DC N m) (hx' : x' ∈ DC N m) (hy : y ∈ DC N n)
    (hy' : y' ∈ DC N n) (h : (x * y)⁻¹ * (x' * y') ∈ (Gamma0 N).map (mapGL ℚ)) :
    x⁻¹ * x' ∈ (Gamma0 N).map (mapGL ℚ) := by
  obtain ⟨X, hX, hX10, -, hXd, -⟩ := exists_int_data hm hx
  obtain ⟨X', hX', hX'10, -, hX'd, -⟩ := exists_int_data hm hx'
  obtain ⟨Y, hY, hY10, -, hYd, -⟩ := exists_int_data hn hy
  obtain ⟨Y', hY', hY'10, -, hY'd, -⟩ := exists_int_data hn hy'
  obtain ⟨g, hg, hgeq⟩ := Subgroup.mem_map.mp h
  have hG10 := Gamma0_mem.mp hg
  have hgmat : (↑(mapGL ℚ g) : Matrix (Fin 2) (Fin 2) ℚ) =
      (g : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) := by
    simp [mapGL_coe_matrix, algebraMap_int_eq]
  have hdx : (↑x : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ) := by
    rw [hX, ← Int.cast_det, hXd]; simp
  have hdx' : (↑x' : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ) := by
    rw [hX', ← Int.cast_det, hX'd]; simp
  have hdy' : (↑y' : Matrix (Fin 2) (Fin 2) ℚ).det = (n : ℚ) := by
    rw [hY', ← Int.cast_det, hY'd]; simp
  have hZ : x⁻¹ * x' = y * mapGL ℚ g * y'⁻¹ := by rw [hgeq]; group
  have hZm : (m : ℚ) • (↑(x⁻¹ * x') : Matrix (Fin 2) (Fin 2) ℚ) =
      (X.adjugate * X').map (Int.cast : ℤ → ℚ) := by
    rw [Units.val_mul, ← Matrix.smul_mul, ← hdx,
      Matrix.GeneralLinearGroup.det_smul_coe_inv_eq_adjugate_map (Int.castRingHom ℚ) hX,
      Int.coe_castRingHom, hX', Matrix.map_mul_intCast]
  have hZn : (n : ℚ) • (↑(x⁻¹ * x') : Matrix (Fin 2) (Fin 2) ℚ) =
      (Y * (g : Matrix (Fin 2) (Fin 2) ℤ) * Y'.adjugate).map (Int.cast : ℤ → ℚ) := by
    rw [hZ, Units.val_mul, Units.val_mul, ← Matrix.mul_smul, ← hdy',
      Matrix.GeneralLinearGroup.det_smul_coe_inv_eq_adjugate_map (Int.castRingHom ℚ) hY',
      Int.coe_castRingHom, hY, hgmat, Matrix.map_mul_intCast, Matrix.map_mul_intCast]
  have hZdet : (↑(x⁻¹ * x') : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, Matrix.coe_units_inv, Matrix.det_nonsing_inv, hdx, hdx',
      Ring.inverse_eq_inv', inv_mul_cancel₀ (by exact_mod_cast hm.ne')]
  obtain ⟨σ, hσ⟩ := (HeckeRing.GLn.mem_SLnZ_iff 2).mp <|
    HeckeRing.GLn.mem_SLnZ_of_coprime_scaling 2 (x⁻¹ * x') m n hmn hZdet
      (fun i j ↦ ⟨_, by simpa using congrFun (congrFun hZm i) j⟩)
      (fun i j ↦ ⟨_, by simpa using congrFun (congrFun hZn i) j⟩)
  have hσmat : (↑(x⁻¹ * x') : Matrix (Fin 2) (Fin 2) ℚ) =
      (σ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) := by
    rw [← hσ]; simp [mapGL_coe_matrix, algebraMap_int_eq]
  have e1 : (m : ℤ) * σ 1 0 = (X.adjugate * X') 1 0 := by
    have := congrFun (congrFun hZm 1) 0
    rw [hσmat] at this
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this
    exact_mod_cast this
  have e2 : (n : ℤ) * σ 1 0 = (Y * (g : Matrix (Fin 2) (Fin 2) ℤ) * Y'.adjugate) 1 0 := by
    have := congrFun (congrFun hZn 1) 0
    rw [hσmat] at this
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this
    exact_mod_cast this
  have d1 : (N : ℤ) ∣ (m : ℤ) * σ 1 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [e1]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, hX10, hX'10]
  have d2 : (N : ℤ) ∣ (n : ℤ) * σ 1 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    rw [e2]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, hY10, hY'10, hG10]
  obtain ⟨s, t, hst⟩ : IsCoprime (m : ℤ) (n : ℤ) := by exact_mod_cast hmn.isCoprime
  have hd : (N : ℤ) ∣ σ 1 0 := by
    have : σ 1 0 = s * ((m : ℤ) * σ 1 0) + t * ((n : ℤ) * σ 1 0) := by
      linear_combination (-(σ 1 0)) * hst
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right d1 _) (dvd_mul_of_dvd_right d2 _)
  rw [← hσ]
  exact Subgroup.mem_map_of_mem _ (Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd))

variable (N : ℕ) [NeZero N]

/-- The standard coset `Γ₀(N) diag(1, m) Γ₀(N)`. -/
private noncomputable abbrev T1 (m : ℕ) :=
  HeckeRing.GL2.diagCosetGamma0 N ![1, m] fun _ ↦ Nat.coprime_one_left N

private lemma mul_rep_mem_DC {m : ℕ} {σ : GL (Fin 2) ℚ} (hσ : σ ∈ (Gamma0 N).map (mapGL ℚ)) :
    σ * ((T1 N m).rep : GL (Fin 2) ℚ) ∈ DC N m := by
  obtain ⟨L, hL, R, hR, hα⟩ :=
    HeckeRing.GL2.exists_rep_diagCosetGamma0_eq_mul_natDiagGL_mul N ![1, m]
      fun _ ↦ Nat.coprime_one_left N
  rw [hα]
  exact DoubleCoset.mem_doubleCoset.mpr
    ⟨σ * L, ((Gamma0 N).map (mapGL ℚ)).mul_mem hσ hL, R, hR, by group⟩

private lemma mulMap_T1 {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n)
    (p : DoubleCoset.DecompQuotient ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
        (((T1 N m).rep : GL (Fin 2) ℚ)) ×
      DoubleCoset.DecompQuotient ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
        (((T1 N n).rep : GL (Fin 2) ℚ))) :
    HeckeCoset.mulMap ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) (T1 N m).rep (T1 N n).rep p = T1 N (m * n) := by
  have hmem : (p.1.out : GL (Fin 2) ℚ) * ((T1 N m).rep : GL (Fin 2) ℚ) *
      ((p.2.out : GL (Fin 2) ℚ) * ((T1 N n).rep : GL (Fin 2) ℚ)) ∈ DC N (m * n) :=
    mul_mem_DC hm hn hmn (mul_rep_mem_DC N p.1.out.2) (mul_rep_mem_DC N p.2.out.2)
  obtain ⟨l, hl, r, hr, hlr⟩ := DoubleCoset.mem_doubleCoset.mp hmem
  have key := HeckeCoset.mulMap_eq_of_eq_mul_mul
    (H₁ := (Gamma0 N).map (mapGL ℚ)) (H₂ := (Gamma0 N).map (mapGL ℚ))
    (H₃ := (Gamma0 N).map (mapGL ℚ)) (g₁ := (T1 N m).rep) (g₂ := (T1 N n).rep)
    (d := ⟨HeckeRing.GLn.natDiagGL 2 ![1, m * n],
      HeckeRing.GL2.natDiagGL_mem_Delta0_of_coprime N _ fun _ ↦ Nat.coprime_one_left N⟩)
    (p := p) hl hr hlr
  exact key.trans (HeckeRing.GL2.diagCosetGamma0_def N _ _).symm

private lemma multiplicity_T1 {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n)
    (A : HeckeCoset (HeckeRing.GL2.Delta0 N) ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ))) :
    DoubleCoset.multiplicity ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) (((T1 N m).rep : GL (Fin 2) ℚ))
      (((T1 N n).rep : GL (Fin 2) ℚ)) ((A.rep : GL (Fin 2) ℚ)) ≤ 1 := by
  classical
  rw [DoubleCoset.multiplicity_def]
  have hfib : Subsingleton {p : DoubleCoset.DecompQuotient ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) (((T1 N m).rep : GL (Fin 2) ℚ)) ×
      DoubleCoset.DecompQuotient ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
        (((T1 N n).rep : GL (Fin 2) ℚ)) |
      ((p.1.out : GL (Fin 2) ℚ) * ((T1 N m).rep : GL (Fin 2) ℚ) *
        ((p.2.out : GL (Fin 2) ℚ) * ((T1 N n).rep : GL (Fin 2) ℚ)) :
        GL (Fin 2) ℚ ⧸ (Gamma0 N).map (mapGL ℚ)) = ((A.rep : GL (Fin 2) ℚ) :
        GL (Fin 2) ℚ ⧸ (Gamma0 N).map (mapGL ℚ))} := by
    constructor
    rintro ⟨⟨i₁, j₁⟩, hp₁⟩ ⟨⟨i₂, j₂⟩, hp₂⟩
    simp only [Set.mem_ofPred_eq] at hp₁ hp₂
    have h12 := hp₁.trans hp₂.symm
    rw [QuotientGroup.eq] at h12
    obtain rfl : i₁ = i₂ := by
      refine DoubleCoset.mk_out_mul_injective _ _ _ ?_
      rw [QuotientGroup.eq]
      exact inv_mul_mem_of_mul_eq hm hn hmn (mul_rep_mem_DC N i₁.out.2) (mul_rep_mem_DC N i₂.out.2)
        (mul_rep_mem_DC N j₁.out.2) (mul_rep_mem_DC N j₂.out.2) h12
    obtain rfl : j₁ = j₂ := DoubleCoset.snd_eq_of_fst_eq hp₁ hp₂
    rfl
  exact Finite.card_le_one_iff_subsingleton.mpr hfib

private lemma heckeTPair_one_zero : heckeTPair N 1 0 = 0 :=
  HeckeRing.GL2.diagElemGamma0_of_not_pos N (fun h ↦ by simpa using h 1)

private lemma heckeTPair_one_one : heckeTPair N 1 1 = 1 :=
  HeckeRing.GL2.diagElemGamma0_one_one N

private lemma heckeTPair_scalar_mul' (c b : ℕ) :
    heckeTPair N c (c * b) = heckeTPair N c c * heckeTPair N 1 b := by
  have h := HeckeRing.GL2.diagElemGamma0_const_mul N c ![1, b]
  have e1 : ((fun _ : Fin 2 ↦ c) : Fin 2 → ℕ) = ![c, c] := by ext i; fin_cases i <;> rfl
  have e2 : ((fun _ : Fin 2 ↦ c) * ![1, b] : Fin 2 → ℕ) = ![c, c * b] := by
    ext i; fin_cases i <;> simp
  rw [e2, e1] at h
  exact h.symm

private lemma heckeTPair_comm' (x y : HeckeRingGamma0 N) : x * y = y * x :=
  HeckeCosetModule.mul_comm_of_antiInvolution ℤ (HeckeRing.GL2.atkinLehnerAntiInvolution N)
    (HeckeRing.GL2.atkinLehnerAntiInvolution_onHeckeCoset_eq_self N) _ _

/-- **Miyake, Lemma 4.5.8 (1)**, core case: `T(1, m) T(1, n) = T(1, m n)` in `ℛ(N)` for coprime
`m`, `n`. -/
@[kb "miyake1989" "Lemma 4.5.8 (1), p. 141 (case l = l' = 1)"]
theorem heckeTPair_one_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) :
    heckeTPair N 1 m * heckeTPair N 1 n = heckeTPair N 1 (m * n) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hn : n = 1 := (Nat.coprime_zero_left _).mp hmn
    subst hn
    simp [heckeTPair_one_zero, heckeTPair_one_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hm1 : m = 1 := (Nat.coprime_zero_right _).mp hmn
    subst hm1
    simp [heckeTPair_one_zero, heckeTPair_one_one]
  have hposm : ∀ i, 0 < (![1, m] : Fin 2 → ℕ) i := fun i ↦ by fin_cases i <;> simp [hm]
  have hposn : ∀ i, 0 < (![1, n] : Fin 2 → ℕ) i := fun i ↦ by fin_cases i <;> simp [hn]
  have hposmn : ∀ i, 0 < (![1, m * n] : Fin 2 → ℕ) i := fun i ↦ by
    fin_cases i <;> simp [hm, hn]
  unfold heckeTPair
  rw [HeckeRing.GL2.diagElemGamma0_of_pos_of_coprime N hposm (Nat.coprime_one_left N),
    HeckeRing.GL2.diagElemGamma0_of_pos_of_coprime N hposn (Nat.coprime_one_left N),
    HeckeRing.GL2.diagElemGamma0_of_pos_of_coprime N hposmn (Nat.coprime_one_left N),
    HeckeCosetModule.mul_def]
  exact HeckeCosetModule.mul_single_single_of_mulMap_eq ℤ (T1 N m) (T1 N n) (T1 N (m * n))
    (mulMap_T1 N hm hn hmn) (multiplicity_T1 N hm hn hmn _)

/-- **Miyake, Lemma 4.5.8 (1)**: `T(l, m) T(l', m') = T(l l', m m')` in `ℛ(N)` when `l ∣ m`,
`l' ∣ m'` and `(l m, l' m') = 1`. -/
@[kb "miyake1989" "Lemma 4.5.8 (1), p. 141"]
theorem heckeTPair_mul_of_coprime {l m l' m' : ℕ} (hl : l ∣ m) (hl' : l' ∣ m')
    (hc : (l * m).Coprime (l' * m')) :
    heckeTPair N l m * heckeTPair N l' m' = heckeTPair N (l * l') (m * m') := by
  by_cases h1 : l * m = 0
  · have h2 : l' * m' = 1 := by rw [h1] at hc; exact (Nat.coprime_zero_left _).mp hc
    obtain ⟨rfl, rfl⟩ := mul_eq_one.mp h2
    simp [heckeTPair_one_one]
  by_cases h2 : l' * m' = 0
  · have h1' : l * m = 1 := by rw [h2] at hc; exact (Nat.coprime_zero_right _).mp hc
    obtain ⟨rfl, rfl⟩ := mul_eq_one.mp h1'
    simp [heckeTPair_one_one]
  obtain ⟨a, rfl⟩ := hl
  obtain ⟨b, rfl⟩ := hl'
  have hab : a.Coprime b :=
    Nat.Coprime.coprime_dvd_left (⟨l * l, by ring⟩ : a ∣ l * (l * a))
      (Nat.Coprime.coprime_dvd_right (⟨l' * l', by ring⟩ : b ∣ l' * (l' * b)) hc)
  have hsc : heckeTPair N l l * heckeTPair N l' l' = heckeTPair N (l * l') (l * l') :=
    HeckeRing.GL2.heckeTScalarGamma0_mul N l l'
  calc heckeTPair N l (l * a) * heckeTPair N l' (l' * b)
      = (heckeTPair N l l * heckeTPair N 1 a) * (heckeTPair N l' l' * heckeTPair N 1 b) := by
        rw [heckeTPair_scalar_mul', heckeTPair_scalar_mul']
    _ = heckeTPair N l l * (heckeTPair N 1 a * heckeTPair N l' l') * heckeTPair N 1 b := by
        simp only [mul_assoc]
    _ = (heckeTPair N l l * heckeTPair N l' l') * (heckeTPair N 1 a * heckeTPair N 1 b) := by
        rw [heckeTPair_comm' N (heckeTPair N 1 a) (heckeTPair N l' l')]
        simp only [mul_assoc]
    _ = heckeTPair N (l * l') (l * l' * (a * b)) := by
        rw [hsc, heckeTPair_one_mul_of_coprime N hab, heckeTPair_scalar_mul']
    _ = _ := by rw [show l * a * (l' * b) = l * l' * (a * b) by ring]

end ModularFormsKB.Miyake.Wave5
