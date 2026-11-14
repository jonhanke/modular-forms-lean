import ModularFormsKB.Miyake.Wave4.Notation
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Action
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Invariance
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Elem

/-!
# Miyake §2.8, §4.5: sums over an arbitrary set of coset representatives

Miyake, *Modular Forms* (Springer 1989), §2.8 (pp. 74–75) and §4.5 (pp. 132–137).

Miyake lets a double coset `Γ₀(N) α Γ₀(N) = ⊔_v Γ₀(N) α_v` act on `𝒢_k(N, χ)` by (2.8.2), (4.5.9):

  `f | Γ₀(N) α Γ₀(N) = det(α)^{k/2-1} Σ_v conj(χ(α_v)) f|_k α_v`,  `χ(α) = conj(χ(a))` on `Δ₀(N)`,

for **any** complete set of representatives `{α_v}` (Theorem 2.8.1 (1)). In Mathlib's slash
normalisation (`f ∣[k] α = det(α)^{k-1} j(α, z)^{-k} f(α z)`) the factor `det(α)^{k/2-1}` is
absorbed, and the weight `conj(χ(α_v)) = χ(a_v)` is Tau Ceti's `delta0NebentypusChar`. Tau Ceti
defines the operator (`twistedHeckeSlashSum`) with one chosen family of representatives.

This file records:

* `IsCosetReps N δ a`: the family `a : ι → GL₂(ℚ)` is a complete set of representatives of
  `Γ₀(N) \ Γ₀(N) δ Γ₀(N)`, in Miyake's sense `Γ₀(N) δ Γ₀(N) = ⊔_i Γ₀(N) a_i`;
* `sum_delta0NebentypusChar_smul_slash_eq`: Theorem 2.8.1 (1) for `Γ₀(N)` with character: the
  weighted sum over any complete set of representatives is Tau Ceti's `twistedHeckeSlashSum`;
* `coe_heckeTT`: Miyake's `T(l, m)` on `𝒮_k(N, χ)` (wave 4's `heckeTT`) is that sum.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup DoubleCoset
  HeckeRing.GL2 HeckeRing.GLn
open scoped MatrixGroups ModularForm Pointwise

noncomputable section

namespace ModularFormsKB.Miyake.Wave7

open ModularFormsKB.Miyake.Wave4

/-- `Γ₀(N)` as a subgroup of `GL₂(ℚ)`. -/
abbrev gamma0Q (N : ℕ) : Subgroup (GL (Fin 2) ℚ) := (Gamma0 N).map (mapGL ℚ)

/-- **A complete set of representatives** of `Γ₀(N) \ Γ₀(N) δ Γ₀(N)` (Miyake, p. 72):
`Γ₀(N) δ Γ₀(N) = ⊔_i Γ₀(N) a_i`, the right cosets `Γ₀(N) a_i` covering the double coset and
pairwise distinct. -/
structure IsCosetReps (N : ℕ) (δ : GL (Fin 2) ℚ) {ι : Type*} (a : ι → GL (Fin 2) ℚ) : Prop where
  cover : doubleCoset δ (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N) =
    ⋃ i, MulOpposite.op (a i) • (gamma0Q N : Set (GL (Fin 2) ℚ))
  injective : Function.Injective fun i ↦ MulOpposite.op (a i) • (gamma0Q N : Set (GL (Fin 2) ℚ))

variable {N : ℕ}

/-- Each representative lies in the double coset. -/
theorem IsCosetReps.mem_doubleCoset {δ : GL (Fin 2) ℚ} {ι : Type*} {a : ι → GL (Fin 2) ℚ}
    (ha : IsCosetReps N δ a) (i : ι) :
    a i ∈ doubleCoset δ (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N) := by
  rw [ha.cover]
  exact Set.mem_iUnion.mpr ⟨i, mem_own_rightCoset (gamma0Q N).toSubmonoid _⟩

/-- The representatives of a double coset of `Δ₀(N)` lie in `Δ₀(N)`. -/
theorem IsCosetReps.mem_Delta0 {δ : GL (Fin 2) ℚ} (hδ : δ ∈ Delta0 N) {ι : Type*}
    {a : ι → GL (Fin 2) ℚ} (ha : IsCosetReps N δ a) (i : ι) : a i ∈ Delta0 N := by
  obtain ⟨x, hx, y, hy, h⟩ := DoubleCoset.mem_doubleCoset.mp (ha.mem_doubleCoset i)
  have hG : ∀ z, z ∈ (gamma0Q N : Set (GL (Fin 2) ℚ)) → z ∈ Delta0 N := fun z hz ↦
    Gamma0Image_le_Delta0 N (by
      rw [Subgroup.mem_toSubmonoid, Gamma0Image_def]; exact hz)
  rw [h]
  exact mul_mem (mul_mem (hG x hx) hδ) (hG y hy)

/-- Two elements generating the same double coset have the same complete sets of
representatives. -/
theorem IsCosetReps.of_mem_doubleCoset {δ δ' : GL (Fin 2) ℚ}
    (h : δ' ∈ doubleCoset δ (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N)) {ι : Type*}
    {a : ι → GL (Fin 2) ℚ} (ha : IsCosetReps N δ a) : IsCosetReps N δ' a := by
  have := DoubleCoset.doubleCoset_eq_of_mem h
  refine ⟨?_, ha.injective⟩
  rw [this]; exact ha.cover

variable [NeZero N]

attribute [local instance] fintypeDecompQuotientGamma0

omit [NeZero N] in
/-- Tau Ceti's representatives `rightCosetRep D v` form a complete set of representatives. -/
theorem isCosetReps_rightCosetRep
    (D : HeckeCoset (Delta0 N) (gamma0Q N) (gamma0Q N)) :
    IsCosetReps N (D.out : GL (Fin 2) ℚ) (rightCosetRep D) := by
  exact ⟨doubleCoset_eq_iUnion_rightCosetRep D, op_rightCosetRep_smul_injective D⟩

/-- **Miyake, Theorem 2.8.1 (1)** for `Γ₀(N)` with character `χ`: the weighted slash sum
`Σ_i χ(a_i) f ∣[k] a_i` (Miyake's `Σ conj(χ(α_i)) f|_k α_i`, (4.5.9)) over **any** complete set of
representatives of `Γ₀(N) \ D` is Tau Ceti's `twistedHeckeSlashSum`, for `f` with
`f ∣ γ = χ(d_γ) f` on `Γ₀(N)`. -/
@[kb "miyake1989" "Theorem 2.8.1 (1), p. 74 (for Γ₀(N), (4.5.9))"]
theorem sum_delta0NebentypusChar_smul_slash_eq (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Delta0 N) (gamma0Q N) (gamma0Q N)) {ι : Type*} [Fintype ι]
    {a : ι → GL (Fin 2) ℚ} (ha : IsCosetReps N (D.out : GL (Fin 2) ℚ) a)
    (f : ℍ → ℂ) (hf : f ∈ functionCharSpace k χ) :
    ∑ i, (delta0NebentypusChar N χ ⟨a i, ha.mem_Delta0 D.out.2 i⟩ : ℂ) • (f ∣[k] a i) =
      twistedHeckeSlashSum k χ D f := by
  classical
  obtain ⟨φ, hφ, hφc⟩ := exists_bijective_rightCosetRep_smul_eq D a ha.cover ha.injective
  rw [twistedHeckeSlashSum_def]
  refine Fintype.sum_bijective φ hφ _ _ fun i ↦ ?_
  have h1 := (rightCoset_eq_iff (gamma0Q N)).mp (hφc i)
  obtain ⟨σ, hσ, hσe⟩ := Subgroup.mem_map.mp h1
  have hy := ha.mem_Delta0 D.out.2 i
  have hx := rightCosetRep_mem_Delta0 D (φ i)
  have := delta0NebentypusChar_smul_slash_mapGL_mul (k := k) (χ := χ) f hf ⟨σ, hσ⟩ hy hx
    (by simp only [hσe]; group)
  rw [← this, nebentypusWeight_def]

omit [NeZero N] in
/-- The underlying function of a cusp form in `𝒮_k(N, χ)` is `χ`-invariant in Tau Ceti's sense. -/
theorem coe_mem_functionCharSpace {k : ℤ} {χ : DirichletCharacter ℂ N} (f : cuspSpace k χ) :
    ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ functionCharSpace k χ.toUnitHom := by
  exact (coe_mem_functionCharSpace_iff _ _
    ((f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).mpr
    ((TauCeti.coe_mem_modFormCharSpace_iff _ _ _).mpr f.2)

/-- **Miyake's `T(l, m)` on `𝒮_k(N, χ)` as a slash sum** (4.5.9): for `l, m ≥ 1` and `(l, N) = 1`,
the action of `Γ₀(N) diag(l, m) Γ₀(N)` is `twistedHeckeSlashSum` over its double coset. -/
theorem coe_heckeTT (k : ℤ) (χ : DirichletCharacter ℂ N) {l m : ℕ} (hl : 0 < l) (hm : 0 < m)
    (hlN : l.Coprime N) (f : cuspSpace k χ) :
    ⇑((heckeTT k χ l m f : cuspSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      twistedHeckeSlashSum k χ.toUnitHom (diagCosetGamma0 N ![l, m] fun _ ↦ hlN)
        ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  have hpos : ∀ i, 0 < (![l, m] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [hl, hm]
  have hc : Nat.Coprime ((![l, m] : Fin 2 → ℕ) 0) N := by simpa using hlN
  rw [heckeTT, diagElemGamma0_of_pos_of_coprime N hpos hc, heckeRingHomCuspCharSpace_apply,
    twistedHeckeSlashCuspFormCharLinearMap_single, one_smul]
  rw [coe_twistedHeckeSlashCuspFormCharEnd]

/-- `T(l, m)` on `𝒮_k(N, χ)` as the weighted sum over any complete set of representatives of
`Γ₀(N) \ Γ₀(N) diag(l, m) Γ₀(N)` (Miyake (4.5.9) with Theorem 2.8.1 (1)). -/
@[kb "miyake1989" "(4.5.9), p. 134"]
theorem coe_heckeTT_eq_sum (k : ℤ) (χ : DirichletCharacter ℂ N) {l m : ℕ} (hl : 0 < l)
    (hm : 0 < m) (hlN : l.Coprime N) {ι : Type*} [Fintype ι] {a : ι → GL (Fin 2) ℚ}
    (ha : IsCosetReps N (natDiagGL 2 ![l, m]) a) (f : cuspSpace k χ) :
    ⇑((heckeTT k χ l m f : cuspSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ∑ i, χ ((((a i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 0 0).num : ZMod N) •
        (⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] a i) := by
  classical
  have hmem : ((diagCosetGamma0 N ![l, m] fun _ ↦ hlN).out : GL (Fin 2) ℚ) ∈
      doubleCoset (natDiagGL 2 ![l, m]) (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N) := by
    have := HeckeCoset.rep_mem (diagCosetGamma0 N ![l, m] fun _ ↦ hlN)
    have h2 := diagCosetGamma0_toSet N ![l, m] fun _ ↦ hlN
    exact h2 ▸ this
  have hD := IsCosetReps.of_mem_doubleCoset hmem ha
  have hf := coe_mem_functionCharSpace f
  rw [coe_heckeTT k χ hl hm hlN f,
    ← sum_delta0NebentypusChar_smul_slash_eq k χ.toUnitHom _ hD _ hf]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  have hy := hD.mem_Delta0 (diagCosetGamma0 N ![l, m] fun _ ↦ hlN).out.2 i
  obtain ⟨A, hA, -⟩ := (mem_Delta0_iff N).mp hy
  rw [delta0NebentypusChar_apply]
  have h00 : ((a i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 0 0 = ((A 0 0 : ℤ) : ℚ) := by
    rw [hA]; rfl
  have hu := Delta0UpperUnit_apply_val N (g := ⟨a i, hy⟩) hA
  rw [h00, Rat.num_intCast]
  rw [← hu]
  simp

end ModularFormsKB.Miyake.Wave7
