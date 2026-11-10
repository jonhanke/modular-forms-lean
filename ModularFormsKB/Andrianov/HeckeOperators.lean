import ModularFormsKB.Andrianov.Hecke
import ModularFormsKB.Andrianov.ModularForms
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Andrianov–Zhuravlev, Chapter 4, §1: Hecke operators of level one

A. N. Andrianov and V. G. Zhuravlev, *Modular Forms and Hecke Operators* (`andrianovzhuravlev1995`), Chapter 2,
(3.14)–(3.15) (pdf p. 75) and Chapter 4, §1.1 (pdf pp. 235–237).

* The group `S^n = GSp_n^+(ℚ)` (`GSpPlus`, in `Hecke.lean`) acts on `H_n` by `M⟨Z⟩ = (AZ + B)(CZ + D)⁻¹`
  (`smulS`): a real similitude `M` with multiplier `r > 0` is `√r` times a real symplectic matrix, so Proposition 2.1
  of Chapter 1 applies (`moebius_mem_of_similitude`). The automorphy factor `det(CZ + D)` is a cocycle (`jS_mul`).
* The book's slash operator (3.14) of Chapter 2, `F|_k M = det(CZ + D)^{-k} F(M⟨Z⟩)` (`slashU`), and the normalized
  operator of Chapter 4, (1.3) with the normalized extension (1.16)–(1.17) of the trivial character of `Γ_n`
  (here `q = 1`, so `S(Γ_n) = S^n` and `χ_k(M) = r(M)^{-kn + ⟨n⟩}`, `⟨n⟩ = n(n+1)/2`):
  `F|_{k,χ} M = r(M)^{nk - ⟨n⟩} det(CZ + D)^{-k} F(M⟨Z⟩)` (`slashS`). Relation (3.15) of Chapter 2:
  `F|M|N = F|MN` (`slashS_mul`).
* For `M ∈ S^n` and a finite system of representatives `M_1, …, M_μ` of the left cosets `Γ_n M_i` in `Γ_n M Γ_n`
  (`LeftCosetReps`), the Hecke operator (1.6): `F|T(M) = ∑_i F|_{k,χ} M_i` (`heckeT`). It does not depend on the
  representatives (`heckeT_eq_of_reps`), and it preserves the functional equation `F|γ = F`, `γ ∈ Γ_n`
  (`slashS_heckeT_of_invariant`); this is the algebraic part of Proposition 1.1 of Chapter 4, proved here.
* Proposition 1.1 of Chapter 4 for `K = Γ_n`, `χ = 1`, integer weight (`heckeT_mem`, `heckeOp`), conditional on the
  analytic part of Proposition 3.8 of Chapter 2 (named input `SlashAnalytic`): the Hecke operator maps
  `𝔐_k(Γ_n)` to itself, linearly.

The existence of a finite system of representatives (Lemma 3.1 and Lemma 1.2 of Chapter 3) is the named statement
`LeftCosetRepsExist`.
-/

open Matrix

namespace ModularFormsKB.Andrianov

section Algebra

variable {n : ℕ}

/-- `M⟨Z⟩ (CZ + D) = AZ + B` whenever `CZ + D` is invertible. -/
theorem moebius_mul_jmat_of {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} {Z : Matrix (Fin n) (Fin n) ℂ}
    (hN : IsUnit (jmat N Z).det) : moebius N Z * jmat N Z = nmat N Z := by
  rw [moebius, Matrix.mul_assoc, nonsing_inv_mul _ hN, Matrix.mul_one]

theorem nmat_mul_of (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    {Z : Matrix (Fin n) (Fin n) ℂ} (hN : IsUnit (jmat N Z).det) :
    nmat (M * N) Z = nmat M (moebius N Z) * jmat N Z := by
  obtain ⟨h11, h12, -, -⟩ := toBlocks_mul M N
  rw [nmat, h11, h12, nmat, Matrix.add_mul, Matrix.mul_assoc (cx M.toBlocks₁₁), moebius_mul_jmat_of hN, nmat,
    jmat]
  simp only [cx_add, cx_mul]
  noncomm_ring

/-- The cocycle relation `j(MN, Z) = j(M, N⟨Z⟩) j(N, Z)` for arbitrary real `M`, `N` with `j(N, Z)` invertible
((3.14) of Chapter 1). -/
theorem jmat_mul_of (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    {Z : Matrix (Fin n) (Fin n) ℂ} (hN : IsUnit (jmat N Z).det) :
    jmat (M * N) Z = jmat M (moebius N Z) * jmat N Z := by
  obtain ⟨-, -, h21, h22⟩ := toBlocks_mul M N
  rw [jmat, h21, h22, jmat, Matrix.add_mul, Matrix.mul_assoc (cx M.toBlocks₂₁), moebius_mul_jmat_of hN, nmat,
    jmat]
  simp only [cx_add, cx_mul]
  noncomm_ring

theorem moebius_mul_of (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    {Z : Matrix (Fin n) (Fin n) ℂ} (hN : IsUnit (jmat N Z).det) :
    moebius (M * N) Z = moebius M (moebius N Z) := by
  rw [moebius, nmat_mul_of M hN, jmat_mul_of M hN, Matrix.mul_inv_rev, Matrix.mul_assoc,
    ← Matrix.mul_assoc (jmat N Z), mul_nonsing_inv _ hN, Matrix.one_mul]
  rfl

theorem cx_smul {ι κ : Type*} (c : ℝ) (A : Matrix ι κ ℝ) : cx (c • A) = (c : ℂ) • cx A := by
  ext i j; simp [cx]

theorem nmat_smul (c : ℝ) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    nmat (c • M) Z = (c : ℂ) • nmat M Z := by
  have h1 : (c • M).toBlocks₁₁ = c • M.toBlocks₁₁ := rfl
  have h2 : (c • M).toBlocks₁₂ = c • M.toBlocks₁₂ := rfl
  rw [nmat, nmat, h1, h2, cx_smul, cx_smul, Matrix.smul_mul, smul_add]

theorem jmat_smul (c : ℝ) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    jmat (c • M) Z = (c : ℂ) • jmat M Z := by
  have h1 : (c • M).toBlocks₂₁ = c • M.toBlocks₂₁ := rfl
  have h2 : (c • M).toBlocks₂₂ = c • M.toBlocks₂₂ := rfl
  rw [jmat, jmat, h1, h2, cx_smul, cx_smul, Matrix.smul_mul, smul_add]

/-- Scaling `M` by a nonzero real number does not change `M⟨Z⟩`. -/
theorem moebius_smul {c : ℝ} (hc : c ≠ 0) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hM : IsUnit (jmat M Z).det) :
    moebius (c • M) Z = moebius M Z := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc
  have hinv : (jmat (c • M) Z)⁻¹ = (c : ℂ)⁻¹ • (jmat M Z)⁻¹ := by
    rw [jmat_smul]
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc', one_smul, nonsing_inv_mul _ hM]
  rw [moebius, moebius, hinv, nmat_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc',
    one_smul]

/-- A real symplectic similitude with multiplier `r > 0`, divided by `√r`, is symplectic. -/
theorem inv_sqrt_smul_mem {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} {r : ℝ} (hr : 0 < r)
    (h : Mᵀ * Jn n ℝ * M = r • Jn n ℝ) : (Real.sqrt r)⁻¹ • M ∈ symplecticGroup (Fin n) ℝ := by
  rw [mem_symplecticGroup_iff_book, transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, h,
    smul_smul, smul_smul]
  have : (Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹ * r = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hr.le, inv_mul_cancel₀ hr.ne']
  rw [this, one_smul]

theorem eq_sqrt_smul {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} {r : ℝ} (hr : 0 < r) :
    M = Real.sqrt r • ((Real.sqrt r)⁻¹ • M) := by
  rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.2 hr).ne', one_smul]

/-- For a real similitude `M` with multiplier `r > 0` and `Z ∈ H_n`, `CZ + D` is invertible. -/
theorem isUnit_det_jmat_of_similitude {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} {r : ℝ} (hr : 0 < r)
    (h : Mᵀ * Jn n ℝ * M = r • Jn n ℝ) (Z : SiegelSpace n) : IsUnit (jmat M Z).det := by
  have hu := isUnit_det_jmat (inv_sqrt_smul_mem hr h) Z
  rw [eq_sqrt_smul (M := M) hr, jmat_smul, det_smul]
  refine IsUnit.mul (IsUnit.pow _ ?_) hu
  exact isUnit_iff_ne_zero.2 (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hr).ne')

/-- **Andrianov–Zhuravlev, Proposition 2.1 of Chapter 1, for similitudes.** A real similitude with positive
multiplier maps `H_n` to itself. -/
theorem moebius_mem_of_similitude {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} {r : ℝ} (hr : 0 < r)
    (h : Mᵀ * Jn n ℝ * M = r • Jn n ℝ) (Z : SiegelSpace n) : moebius M Z ∈ siegelSet n := by
  have hs := inv_sqrt_smul_mem hr h
  rw [eq_sqrt_smul (M := M) hr, moebius_smul (Real.sqrt_pos.2 hr).ne' _ (isUnit_det_jmat hs Z)]
  exact moebius_mem hs Z

end Algebra

section GSp

variable {n : ℕ}

/-- The real matrix of a rational matrix. -/
noncomputable def gR (g : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ).map (Rat.castHom ℝ)

theorem gR_mul (g h : GL (Fin n ⊕ Fin n) ℚ) : gR (g * h) = gR g * gR h := by
  simp only [gR, Units.val_mul]
  exact Matrix.map_mul

theorem Jn_map_real : (Jn n ℚ).map (Rat.castHom ℝ) = Jn n ℝ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Jn, Matrix.one_apply] <;> split_ifs <;> simp

/-- The multiplier `r(M)` of `M ∈ S^n`: `ᵗM J_n M = r(M) J_n`. -/
noncomputable def mult (g : GSpPlus n) : ℚ :=
  Classical.choose (show IsSimilitude ((g : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)
    from g.2)

theorem mult_pos (g : GSpPlus n) : 0 < mult g :=
  (Classical.choose_spec (show IsSimilitude ((g : GL (Fin n ⊕ Fin n) ℚ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) from g.2)).1

theorem mult_spec (g : GSpPlus n) :
    ((g : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ * Jn n ℚ *
      ((g : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) = mult g • Jn n ℚ :=
  (Classical.choose_spec (show IsSimilitude ((g : GL (Fin n ⊕ Fin n) ℚ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) from g.2)).2

/-- The multiplier is unique when `n ≥ 1`. -/
theorem smul_Jn_inj {R : Type*} [CommRing R] (hn : 0 < n) {r s : R} (h : r • Jn n R = s • Jn n R) : r = s := by
  have := congrFun (congrFun h (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)
  simpa [Jn] using this

theorem mult_mul (hn : 0 < n) (g h : GSpPlus n) : mult (g * h) = mult g * mult h := by
  apply smul_Jn_inj (R := ℚ) hn
  rw [← mult_spec, mul_smul, ← mult_spec, ← Matrix.smul_mul, ← Matrix.mul_smul, ← mult_spec]
  simp only [Subgroup.coe_mul, Units.val_mul, transpose_mul, Matrix.mul_assoc]

theorem gR_similitude (g : GSpPlus n) :
    (gR (g : GL (Fin n ⊕ Fin n) ℚ))ᵀ * Jn n ℝ * gR (g : GL (Fin n ⊕ Fin n) ℚ) = (mult g : ℝ) • Jn n ℝ := by
  have h := congrArg (fun X => X.map (Rat.castHom ℝ)) (mult_spec g)
  simp only [Matrix.map_mul, Jn_map_real] at h
  rw [gR, ← Matrix.transpose_map, h]
  ext i j
  simp [Jn_map_real.symm]

theorem mult_pos_real (g : GSpPlus n) : (0 : ℝ) < mult g := by exact_mod_cast mult_pos g

/-- **Andrianov–Zhuravlev, Chapter 2, (3.14).** `M⟨Z⟩` for `M ∈ S^n`, as a point of `H_n`. -/
noncomputable def smulS (g : GSpPlus n) (Z : SiegelSpace n) : SiegelSpace n :=
  ⟨moebius (gR (g : GL (Fin n ⊕ Fin n) ℚ)) Z, moebius_mem_of_similitude (mult_pos_real g) (gR_similitude g) Z⟩

/-- `det(CZ + D)` for `M ∈ S^n`. -/
noncomputable def jS (g : GSpPlus n) (Z : SiegelSpace n) : ℂ := (jmat (gR (g : GL (Fin n ⊕ Fin n) ℚ)) Z).det

theorem jS_ne_zero (g : GSpPlus n) (Z : SiegelSpace n) : jS g Z ≠ 0 :=
  (isUnit_det_jmat_of_similitude (mult_pos_real g) (gR_similitude g) Z).ne_zero

theorem smulS_mul (g h : GSpPlus n) (Z : SiegelSpace n) : smulS (g * h) Z = smulS g (smulS h Z) := by
  apply Subtype.ext
  show moebius (gR ((g * h : GSpPlus n) : GL (Fin n ⊕ Fin n) ℚ)) Z = moebius (gR (g : GL (Fin n ⊕ Fin n) ℚ))
    (moebius (gR (h : GL (Fin n ⊕ Fin n) ℚ)) Z)
  rw [Subgroup.coe_mul, gR_mul]
  exact moebius_mul_of _ (isUnit_det_jmat_of_similitude (mult_pos_real h) (gR_similitude h) Z)

/-- **The cocycle relation** for `S^n`: `det j(MN, Z) = det j(M, N⟨Z⟩) det j(N, Z)`. -/
theorem jS_mul (g h : GSpPlus n) (Z : SiegelSpace n) : jS (g * h) Z = jS g (smulS h Z) * jS h Z := by
  unfold jS
  rw [Subgroup.coe_mul, gR_mul, jmat_mul_of _ (isUnit_det_jmat_of_similitude (mult_pos_real h) (gR_similitude h) Z),
    det_mul]
  rfl

end GSp

section Slash

variable {n : ℕ}

/-- **Andrianov–Zhuravlev, Chapter 2, (3.14).** `F|_k M = det(CZ + D)^{-k} F(M⟨Z⟩)` for `M ∈ S^n`. -/
@[kb "andrianovzhuravlev1995" "Chapter 2, (3.14), p. 75"]
noncomputable def slashU (k : ℤ) (g : GSpPlus n) (F : SiegelSpace n → ℂ) : SiegelSpace n → ℂ :=
  fun Z => jS g Z ^ (-k) * F (smulS g Z)

/-- The exponent `nk - ⟨n⟩`, `⟨n⟩ = n(n+1)/2`, of the normalizing factor `r(M)^{nk - ⟨n⟩}`. -/
def slashExp (n : ℕ) (k : ℤ) : ℤ := n * k - ((n * (n + 1) / 2 : ℕ) : ℤ)

/-- **Andrianov–Zhuravlev, Chapter 4, (1.3) and (1.16)–(1.18), level one.** The normalized operator
`F|_{k,χ} M = χ_k(M)⁻¹ F|_k M = r(M)^{nk - ⟨n⟩} det(CZ + D)^{-k} F(M⟨Z⟩)` for `M ∈ S^n = S(Γ_n)`, where
`χ_k(M) = r(M)^{-kn + ⟨n⟩}` is the normalized extension (1.17) of the trivial character of `Γ_n` (`q = 1`). -/
@[kb "andrianovzhuravlev1995" "Chapter 4, (1.3), (1.16)–(1.18), pp. 236–237"]
noncomputable def slashS (k : ℤ) (g : GSpPlus n) (F : SiegelSpace n → ℂ) : SiegelSpace n → ℂ :=
  fun Z => ((mult g : ℚ) : ℂ) ^ slashExp n k * slashU k g F Z

theorem slashS_apply (k : ℤ) (g : GSpPlus n) (F : SiegelSpace n → ℂ) (Z : SiegelSpace n) :
    slashS k g F Z = ((mult g : ℚ) : ℂ) ^ slashExp n k * jS g Z ^ (-k) * F (smulS g Z) := by
  rw [slashS, slashU, mul_assoc]

theorem mult_zpow_mul (k : ℤ) (g h : GSpPlus n) :
    ((mult (g * h) : ℚ) : ℂ) ^ slashExp n k = ((mult g : ℚ) : ℂ) ^ slashExp n k * ((mult h : ℚ) : ℂ) ^ slashExp n k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [slashExp]
  · rw [mult_mul hn, Rat.cast_mul, mul_zpow]

/-- **Andrianov–Zhuravlev, Chapter 2, (3.15) and Chapter 4, (1.4).** `F|M|N = F|MN`. -/
@[kb "andrianovzhuravlev1995" "Chapter 4, (1.4), p. 236"]
theorem slashS_mul (k : ℤ) (g h : GSpPlus n) (F : SiegelSpace n → ℂ) :
    slashS k (g * h) F = slashS k h (slashS k g F) := by
  funext Z
  rw [slashS_apply, slashS_apply, slashS_apply, mult_zpow_mul, jS_mul, smulS_mul, mul_zpow]
  ring

theorem slashS_one (k : ℤ) (F : SiegelSpace n → ℂ) : slashS k 1 F = F := by
  have h := slashS_mul k 1 1 F
  have hm : ((mult (1 : GSpPlus n) : ℚ) : ℂ) ^ slashExp n k = 1 := by
    have := mult_zpow_mul (n := n) k 1 1
    rw [mul_one] at this
    have hne : ((mult (1 : GSpPlus n) : ℚ) : ℂ) ^ slashExp n k ≠ 0 :=
      zpow_ne_zero _ (by exact_mod_cast (mult_pos (1 : GSpPlus n)).ne')
    exact (mul_eq_left₀ hne).1 this.symm
  funext Z
  have hj : jS (1 : GSpPlus n) Z = 1 := by
    have := jS_mul (1 : GSpPlus n) 1 Z
    have hs : smulS (1 : GSpPlus n) Z = Z := by
      apply Subtype.ext
      show moebius (gR ((1 : GSpPlus n) : GL (Fin n ⊕ Fin n) ℚ)) Z = Z
      have : gR ((1 : GSpPlus n) : GL (Fin n ⊕ Fin n) ℚ) = 1 := by simp [gR]
      rw [this]; exact moebius_one _
    rw [mul_one, hs] at this
    exact (mul_eq_left₀ (jS_ne_zero 1 Z)).1 this.symm
  have hs : smulS (1 : GSpPlus n) Z = Z := by
    apply Subtype.ext
    show moebius (gR ((1 : GSpPlus n) : GL (Fin n ⊕ Fin n) ℚ)) Z = Z
    have : gR ((1 : GSpPlus n) : GL (Fin n ⊕ Fin n) ℚ) = 1 := by simp [gR]
    rw [this]; exact moebius_one _
  rw [slashS_apply, hm, hj, hs]; simp

theorem slashS_add (k : ℤ) (g : GSpPlus n) (F G : SiegelSpace n → ℂ) :
    slashS k g (F + G) = slashS k g F + slashS k g G := by
  funext Z; simp only [slashS_apply, Pi.add_apply]; ring

theorem slashS_smul (k : ℤ) (g : GSpPlus n) (c : ℂ) (F : SiegelSpace n → ℂ) :
    slashS k g (c • F) = c • slashS k g F := by
  funext Z; simp only [slashS_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem slashS_sum (k : ℤ) (g : GSpPlus n) {ι : Type*} (s : Finset ι) (F : ι → SiegelSpace n → ℂ) :
    slashS k g (∑ i ∈ s, F i) = ∑ i ∈ s, slashS k g (F i) := by
  funext Z
  simp only [slashS_apply, Finset.sum_apply, Finset.mul_sum]

end Slash

section Gamma

variable {n : ℕ}

/-- `Γ_n` as a subgroup of `S^n`. -/
noncomputable def gammaS (n : ℕ) : Subgroup (GSpPlus n) :=
  (SiegelModularGroup.toGL (n := n)).range.subgroupOf (GSpPlus n)

/-- The element of `S^n` given by `γ ∈ Γ_n`. -/
noncomputable def SiegelModularGroup.toGSp (γ : SiegelModularGroup n) : GSpPlus n :=
  ⟨SiegelModularGroup.toGL γ, SiegelModularGroup.toGL_mem γ⟩

theorem toGSp_mem_gammaS (γ : SiegelModularGroup n) : SiegelModularGroup.toGSp γ ∈ gammaS n :=
  Subgroup.mem_subgroupOf.2 ⟨γ, rfl⟩

theorem exists_of_mem_gammaS {g : GSpPlus n} (hg : g ∈ gammaS n) :
    ∃ γ : SiegelModularGroup n, SiegelModularGroup.toGSp γ = g := by
  obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.1 hg
  exact ⟨γ, Subtype.ext hγ⟩

theorem gR_toGSp (γ : SiegelModularGroup n) :
    gR ((SiegelModularGroup.toGSp γ : GSpPlus n) : GL (Fin n ⊕ Fin n) ℚ) =
      (SiegelModularGroup.toReal γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by
  ext i j
  simp [gR, SiegelModularGroup.toGSp, SiegelModularGroup.toGL, SiegelModularGroup.toReal_coe]

theorem smulS_toGSp (γ : SiegelModularGroup n) (Z : SiegelSpace n) :
    smulS (SiegelModularGroup.toGSp γ) Z = γ • Z := by
  apply Subtype.ext
  show moebius (gR ((SiegelModularGroup.toGSp γ : GSpPlus n) : GL (Fin n ⊕ Fin n) ℚ)) Z =
    moebius (SiegelModularGroup.toReal γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) Z
  rw [gR_toGSp]

theorem mult_toGSp_zpow (k : ℤ) (γ : SiegelModularGroup n) :
    ((mult (SiegelModularGroup.toGSp γ) : ℚ) : ℂ) ^ slashExp n k = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [slashExp]
  · have h1 : mult (SiegelModularGroup.toGSp γ) = 1 := by
      apply smul_Jn_inj (R := ℚ) hn
      rw [← mult_spec, one_smul]
      have h := SymplecticGroup.map_mem γ.2 (Int.castRingHom ℚ)
      rw [mem_symplecticGroup_iff_book] at h
      simpa [SiegelModularGroup.toGSp, SiegelModularGroup.toGL] using h
    rw [h1]; simp

/-- For `γ ∈ Γ_n` the normalized operator is the slash operator of Chapter 2. -/
theorem slashS_toGSp (k : ℤ) (γ : SiegelModularGroup n) (F : SiegelSpace n → ℂ) :
    slashS k (SiegelModularGroup.toGSp γ) F = slash k γ F := by
  funext Z
  rw [slashS_apply, mult_toGSp_zpow, one_mul, smulS_toGSp, slash, jdet, jS, gR_toGSp]

end Gamma

section HeckeOperator

variable {n : ℕ}

/-- **Andrianov–Zhuravlev, Chapter 3, (1.11) and Lemma 1.2.** A finite system of representatives `M_1, …, M_μ` of
the left cosets `Γ_n M_i` contained in the double coset `Γ_n M Γ_n`, `M ∈ S^n`: each `M_i` lies in `Γ_n M Γ_n`,
every element of `Γ_n M Γ_n` lies in some `Γ_n M_i`, and distinct `M_i` lie in distinct left cosets. -/
@[kb "andrianovzhuravlev1995" "Chapter 3, (1.11), Lemma 1.2, p. 104"]
structure LeftCosetReps (M : GSpPlus n) where
  μ : ℕ
  rep : Fin μ → GSpPlus n
  mem : ∀ i, ∃ a ∈ gammaS n, ∃ b ∈ gammaS n, rep i = a * M * b
  cover : ∀ a ∈ gammaS n, ∀ b ∈ gammaS n, ∃ i, ∃ c ∈ gammaS n, a * M * b = c * rep i
  disj : ∀ i j, ∀ c ∈ gammaS n, rep i = c * rep j → i = j

/-- **Andrianov–Zhuravlev, Chapter 3, Lemma 3.1 with Lemma 1.2**, named statement: every double coset
`Γ_n M Γ_n`, `M ∈ S^n`, is a finite union of left cosets. -/
@[kb "andrianovzhuravlev1995" "Chapter 3, Lemma 3.1, p. 132"]
structure LeftCosetRepsExist (n : ℕ) : Prop where
  exists_reps : ∀ M : GSpPlus n, Nonempty (LeftCosetReps M)

/-- **Andrianov–Zhuravlev, Chapter 4, (1.6) and (1.18).** The normalized Hecke operator of the double coset
`T = (M)_Γ = ∑_i (Γ_n M_i)`: `F|T = ∑_i F|_{k,χ} M_i`. -/
@[kb "andrianovzhuravlev1995" "Chapter 4, (1.6), p. 236"]
noncomputable def heckeT (k : ℤ) {M : GSpPlus n} (R : LeftCosetReps M) (F : SiegelSpace n → ℂ) :
    SiegelSpace n → ℂ :=
  ∑ i, slashS k (R.rep i) F

/-- For `γ ∈ Γ_n`, right multiplication by `γ` permutes the left cosets `Γ_n M_i`: the index of the coset of
`M_i γ`. -/
theorem LeftCosetReps.exists_right_mul {M : GSpPlus n} (R : LeftCosetReps M) {γ : GSpPlus n} (hγ : γ ∈ gammaS n)
    (i : Fin R.μ) : ∃ j, ∃ c ∈ gammaS n, R.rep i * γ = c * R.rep j := by
  obtain ⟨a, ha, b, hb, h⟩ := R.mem i
  obtain ⟨j, c, hc, h'⟩ := R.cover a ha (b * γ) (mul_mem hb hγ)
  exact ⟨j, c, hc, by rw [h, ← h', mul_assoc]⟩

/-- **Andrianov–Zhuravlev, Chapter 4, §1.1 (after (1.6)).** If `F|γ = F` for all `γ ∈ Γ_n`, then `F|T` does not
depend on the choice of representatives. -/
@[kb "andrianovzhuravlev1995" "Chapter 4, §1.1, p. 236"]
theorem heckeT_eq_of_reps (k : ℤ) {M : GSpPlus n} (R R' : LeftCosetReps M) {F : SiegelSpace n → ℂ}
    (hF : ∀ γ ∈ gammaS n, slashS k γ F = F) : heckeT k R F = heckeT k R' F := by
  -- each `M_i` lies in a unique left coset `Γ_n M'_j`
  have key : ∀ (R₁ R₂ : LeftCosetReps M) (i : Fin R₁.μ), ∃ j, ∃ c ∈ gammaS n, R₁.rep i = c * R₂.rep j := by
    intro R₁ R₂ i
    obtain ⟨a, ha, b, hb, h⟩ := R₁.mem i
    obtain ⟨j, c, hc, h'⟩ := R₂.cover a ha b hb
    exact ⟨j, c, hc, h.trans h'⟩
  choose σ c hc hσ using key R R'
  choose τ d hd hτ using key R' R
  have hσinj : Function.Injective σ := by
    intro i i' h
    apply R.disj i i' (c i * (c i')⁻¹) (mul_mem (hc i) (inv_mem (hc i')))
    rw [hσ i, hσ i', h, mul_assoc, inv_mul_cancel_left]
  have hτinj : Function.Injective τ := by
    intro j j' h
    apply R'.disj j j' (d j * (d j')⁻¹) (mul_mem (hd j) (inv_mem (hd j')))
    rw [hτ j, hτ j', h, mul_assoc, inv_mul_cancel_left]
  have hle1 := Fintype.card_le_of_injective σ hσinj
  have hle2 := Fintype.card_le_of_injective τ hτinj
  simp only [Fintype.card_fin] at hle1 hle2
  have hbij : Function.Bijective σ := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hσinj, by simp only [Fintype.card_fin]; omega⟩
  unfold heckeT
  rw [← Equiv.sum_comp (Equiv.ofBijective σ hbij)]
  refine Finset.sum_congr rfl fun i _ => ?_
  show slashS k (R.rep i) F = slashS k (R'.rep (σ i)) F
  rw [hσ i, slashS_mul, hF _ (hc i)]

/-- **Andrianov–Zhuravlev, Chapter 4, §1.1 (after (1.6)).** If `F|γ = F` for all `γ ∈ Γ_n`, then
`(F|T)|γ = F|T` for all `γ ∈ Γ_n`. -/
@[kb "andrianovzhuravlev1995" "Chapter 4, §1.1, p. 236"]
theorem slashS_heckeT_of_invariant (k : ℤ) {M : GSpPlus n} (R : LeftCosetReps M) {F : SiegelSpace n → ℂ}
    (hF : ∀ γ ∈ gammaS n, slashS k γ F = F) {γ : GSpPlus n} (hγ : γ ∈ gammaS n) :
    slashS k γ (heckeT k R F) = heckeT k R F := by
  choose σ c hc hσ using R.exists_right_mul hγ
  have hσinj : Function.Injective σ := by
    intro i i' h
    apply R.disj i i' (c i * (c i')⁻¹) (mul_mem (hc i) (inv_mem (hc i')))
    have e1 : R.rep i = c i * R.rep (σ i) * γ⁻¹ := by rw [← hσ i, mul_inv_cancel_right]
    have e2 : R.rep i' = c i' * R.rep (σ i') * γ⁻¹ := by rw [← hσ i', mul_inv_cancel_right]
    rw [e1, e2, h]; simp only [mul_assoc, inv_mul_cancel_left]
  have hbij : Function.Bijective σ := ⟨hσinj, Finite.surjective_of_injective hσinj⟩
  unfold heckeT
  rw [slashS_sum]
  refine Fintype.sum_equiv (Equiv.ofBijective σ hbij) _ _ fun i => ?_
  rw [Equiv.ofBijective_apply, ← slashS_mul, hσ i, slashS_mul, hF _ (hc i)]

theorem heckeT_add (k : ℤ) {M : GSpPlus n} (R : LeftCosetReps M) (F G : SiegelSpace n → ℂ) :
    heckeT k R (F + G) = heckeT k R F + heckeT k R G := by
  simp only [heckeT, slashS_add, Finset.sum_add_distrib]

theorem heckeT_smul (k : ℤ) {M : GSpPlus n} (R : LeftCosetReps M) (c : ℂ) (F : SiegelSpace n → ℂ) :
    heckeT k R (c • F) = c • heckeT k R F := by
  simp only [heckeT, slashS_smul, Finset.smul_sum]

/-- A modular form of weight `k` for `Γ_n` (trivial character) satisfies `F|_{k,χ} γ = F` for `γ ∈ Γ_n`
((1.5) of Chapter 4). -/
theorem slashS_eq_of_mem {k : ℤ} {F : SiegelSpace n → ℂ}
    (hF : F ∈ siegelModularForms n k ⊤ (1 : (⊤ : Subgroup (SiegelModularGroup n)) →* ℂˣ)) {γ : GSpPlus n}
    (hγ : γ ∈ gammaS n) : slashS k γ F = F := by
  obtain ⟨γ₀, rfl⟩ := exists_of_mem_gammaS hγ
  rw [slashS_toGSp]
  funext Z
  have := hF.transf ⟨γ₀, Subgroup.mem_top _⟩ Z
  simpa using this

/-- **Andrianov–Zhuravlev, Chapter 2, Proposition 3.8 (analytic part, integer weight, `K = Γ_n`)**, named statement.
For `F ∈ 𝔐_k(Γ_n)` and `M ∈ S^n`, the function `F|_k M` is holomorphic on `H_n` (Lemma 4.2 of Chapter 1) and,
if `n = 1`, bounded on every `H_1(ε)`, `ε > 0` (condition (3) of the definition for `F|_k M`, with `W = 1`). -/
@[kb "andrianovzhuravlev1995" "Chapter 2, Proposition 3.8, p. 81"]
structure SlashAnalytic (n : ℕ) (k : ℤ) : Prop where
  holo : ∀ F ∈ siegelModularForms n k ⊤ (1 : (⊤ : Subgroup (SiegelModularGroup n)) →* ℂˣ), ∀ g : GSpPlus n,
    IsHolomorphicOnSiegel (slashU k g F)
  bdd : ∀ F ∈ siegelModularForms n k ⊤ (1 : (⊤ : Subgroup (SiegelModularGroup n)) →* ℂˣ), ∀ g : GSpPlus n,
    n = 1 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Z ∈ siegelSetEps n ε, ‖slashU k g F Z‖ ≤ C

theorem isHolomorphicOnSiegel_sum {ι : Type*} (s : Finset ι) {F : ι → SiegelSpace n → ℂ}
    (hF : ∀ i ∈ s, IsHolomorphicOnSiegel (F i)) : IsHolomorphicOnSiegel (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isHolomorphicOnSiegel_zero (n := n))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-- **Andrianov–Zhuravlev, Chapter 4, Proposition 1.1 (level one, integer weight, trivial character)**, conditional
on the analytic input `SlashAnalytic` (Proposition 3.8 of Chapter 2): the Hecke operator `|T`, `T = (M)_Γ`, maps
`𝔐_k(Γ_n)` to itself. -/
@[kb "andrianovzhuravlev1995" "Chapter 4, Proposition 1.1, p. 237"]
theorem heckeT_mem {k : ℤ} (hA : SlashAnalytic n k) {M : GSpPlus n} (R : LeftCosetReps M) {F : SiegelSpace n → ℂ}
    (hF : F ∈ siegelModularForms n k ⊤ (1 : (⊤ : Subgroup (SiegelModularGroup n)) →* ℂˣ)) :
    heckeT k R F ∈ siegelModularForms n k ⊤ (1 : (⊤ : Subgroup (SiegelModularGroup n)) →* ℂˣ) := by
  have hinv : ∀ γ ∈ gammaS n, slashS k γ (heckeT k R F) = heckeT k R F := fun γ hγ =>
    slashS_heckeT_of_invariant k R (fun γ hγ => slashS_eq_of_mem hF hγ) hγ
  refine ⟨?_, fun γ Z => ?_, fun h1 γ ε hε => ?_⟩
  · unfold heckeT
    refine isHolomorphicOnSiegel_sum _ fun i _ => ?_
    have : slashS k (R.rep i) F = ((mult (R.rep i) : ℚ) : ℂ) ^ slashExp n k • slashU k (R.rep i) F := by
      funext Z; rfl
    rw [this]
    exact (hA.holo F hF (R.rep i)).const_smul _
  · rw [← slashS_toGSp k (γ : SiegelModularGroup n), hinv _ (toGSp_mem_gammaS _)]
    simp
  · rw [← slashS_toGSp k γ, hinv _ (toGSp_mem_gammaS _)]
    have hb : ∀ i, ∃ C : ℝ, ∀ Z ∈ siegelSetEps n ε, ‖slashS k (R.rep i) F Z‖ ≤ C := by
      intro i
      obtain ⟨C, hC⟩ := hA.bdd F hF (R.rep i) h1 ε hε
      refine ⟨‖((mult (R.rep i) : ℚ) : ℂ) ^ slashExp n k‖ * C, fun Z hZ => ?_⟩
      rw [slashS, norm_mul]
      exact mul_le_mul_of_nonneg_left (hC Z hZ) (norm_nonneg _)
    choose C hC using hb
    refine ⟨∑ i, C i, fun Z hZ => ?_⟩
    unfold heckeT
    rw [Finset.sum_apply]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hC i Z hZ)

/-- **Andrianov–Zhuravlev, Chapter 4, Proposition 1.1 (level one, integer weight)**: the Hecke operator of
`T = (M)_Γ` as a linear endomorphism of `𝔐_k(Γ_n)`, conditional on `SlashAnalytic`. -/
noncomputable def heckeOp {k : ℤ} (hA : SlashAnalytic n k) {M : GSpPlus n} (R : LeftCosetReps M) :
    Module.End ℂ (siegelModularForms n k ⊤ (1 : (⊤ : Subgroup (SiegelModularGroup n)) →* ℂˣ)) where
  toFun F := ⟨heckeT k R F, heckeT_mem hA R F.2⟩
  map_add' F G := Subtype.ext (heckeT_add k R F G)
  map_smul' c F := Subtype.ext (heckeT_smul k R c F)

end HeckeOperator

end ModularFormsKB.Andrianov
