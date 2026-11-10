import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Order
import ModularFormsKB.Citation
/-!
# Andrianov–Zhuravlev, Chapter 1, §2: the symplectic group and the Siegel upper half-plane

A. N. Andrianov and V. G. Zhuravlev, *Modular Forms and Hecke Operators* (`andrianovzhuravlev1995`), Chapter 1 §2,
pdf pp. 16–21 (pdf page = printed page + 10).

* The Siegel upper half-plane of degree `n`, `H_n = {Z = X + iY ∈ S_n(ℂ) ; Y > 0}` (1.10), as the subtype
  `SiegelSpace n` of complex `n × n` matrices.
* The book's matrix `J_n = (0 E; -E 0)` (2.4) and the symplectic group `Sp_n(R) = {M ; ᵗM J_n M = J_n}` (2.6). Mathlib's
  `Matrix.symplecticGroup` uses `J = (0 -1; 1 0) = -J_n` and the condition `M J Mᵀ = J`; the two groups coincide
  (`mem_symplecticGroup_iff_book`), so we use Mathlib's group throughout.
* The fractional linear action `M⟨Z⟩ = (AZ + B)(CZ + D)⁻¹` (2.1), (2.10): `CZ + D` is invertible on `H_n` and
  `M⟨Z⟩ ∈ H_n` (Proposition 2.1, with Lemma 2.8: `Im M⟨Z⟩ = ᵗ(C\bar Z + D)⁻¹ Y (CZ + D)⁻¹`); it is an action
  (`MulAction`) of `Sp_n(ℝ)` on `H_n`, and `CZ + D` is a cocycle.
* The generators `U(V)`, `T(S)`, `J_n` (2.2)–(2.4) and their actions.

Indices: the book's `1, …, n` are `Fin n` here (0-based); block matrices are indexed by `Fin n ⊕ Fin n`, with
`A = M.toBlocks₁₁`, `B = M.toBlocks₁₂`, `C = M.toBlocks₂₁`, `D = M.toBlocks₂₂`.
-/

open Matrix
open scoped ComplexOrder

namespace ModularFormsKB.Andrianov

section Symplectic

variable (n : ℕ) (R : Type*) [CommRing R]

/-- The book's matrix `J_n = (0 E_n; -E_n 0)`, (2.4). It is the negative of Mathlib's `Matrix.J`. -/
def Jn : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := fromBlocks 0 1 (-1) 0

theorem Jn_eq_neg_J : Jn n R = -Matrix.J (Fin n) R := by
  simp [Jn, Matrix.J, fromBlocks_neg]

variable {n R}

/-- **Andrianov–Zhuravlev (2.6).** The book defines `Sp_n(R)` by `ᵗM J_n M = J_n`; this is Mathlib's symplectic
group. -/
@[kb "andrianovzhuravlev1995" "Chapter 1, (2.6), p. 17"]
theorem mem_symplecticGroup_iff_book {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} :
    M ∈ symplecticGroup (Fin n) R ↔ Mᵀ * Jn n R * M = Jn n R := by
  rw [SymplecticGroup.mem_iff', Jn_eq_neg_J]
  simp

/-- **Andrianov–Zhuravlev (2.7).** A block matrix is symplectic iff `ᵗAC = ᵗCA`, `ᵗBD = ᵗDB`, `ᵗAD - ᵗCB = E`.
(Mathlib's `SymplecticGroup.fromBlocks_mem_iff`.) -/
@[kb "andrianovzhuravlev1995" "Chapter 1, (2.7), p. 17"]
theorem fromBlocks_mem_symplecticGroup_iff {A B C D : Matrix (Fin n) (Fin n) R} :
    fromBlocks A B C D ∈ symplecticGroup (Fin n) R ↔
      Aᵀ * C = Cᵀ * A ∧ Bᵀ * D = Dᵀ * B ∧ Aᵀ * D - Cᵀ * B = 1 :=
  SymplecticGroup.fromBlocks_mem_iff

/-- The block relations (2.7) for a symplectic matrix, read off from its blocks. -/
theorem blocks_of_mem {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hM : M ∈ symplecticGroup (Fin n) R) :
    M.toBlocks₁₁ᵀ * M.toBlocks₂₁ = M.toBlocks₂₁ᵀ * M.toBlocks₁₁ ∧
      M.toBlocks₁₂ᵀ * M.toBlocks₂₂ = M.toBlocks₂₂ᵀ * M.toBlocks₁₂ ∧
      M.toBlocks₁₁ᵀ * M.toBlocks₂₂ - M.toBlocks₂₁ᵀ * M.toBlocks₁₂ = 1 := by
  rw [← fromBlocks_toBlocks M] at hM
  exact fromBlocks_mem_symplecticGroup_iff.1 hM

/-- **Andrianov–Zhuravlev (2.8).** For a symplectic matrix, `A ᵗB = B ᵗA`, `C ᵗD = D ᵗC`, `A ᵗD - B ᵗC = E`. -/
@[kb "andrianovzhuravlev1995" "Chapter 1, (2.8), p. 17"]
theorem blocks_of_mem' {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hM : M ∈ symplecticGroup (Fin n) R) :
    M.toBlocks₁₁ * M.toBlocks₁₂ᵀ = M.toBlocks₁₂ * M.toBlocks₁₁ᵀ ∧
      M.toBlocks₂₁ * M.toBlocks₂₂ᵀ = M.toBlocks₂₂ * M.toBlocks₂₁ᵀ ∧
      M.toBlocks₁₁ * M.toBlocks₂₂ᵀ - M.toBlocks₁₂ * M.toBlocks₂₁ᵀ = 1 := by
  have hT := SymplecticGroup.transpose_mem hM
  rw [← fromBlocks_toBlocks M, fromBlocks_transpose] at hT
  have h := fromBlocks_mem_symplecticGroup_iff.1 hT
  simp only [transpose_transpose] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- The matrix `U(V) = (V* 0; 0 V)`, `V* = ᵗV⁻¹`, (2.2), for an invertible `V`. -/
def Umat (V : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  fromBlocks (↑V⁻¹ : Matrix (Fin n) (Fin n) R)ᵀ 0 0 (V : Matrix (Fin n) (Fin n) R)

/-- The matrix `T(S) = (E S; 0 E)`, (2.3). -/
def Tmat (S : Matrix (Fin n) (Fin n) R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  fromBlocks 1 S 0 1

theorem Umat_mem (V : (Matrix (Fin n) (Fin n) R)ˣ) : Umat V ∈ symplecticGroup (Fin n) R := by
  rw [Umat, fromBlocks_mem_symplecticGroup_iff]
  refine ⟨by simp, by simp, ?_⟩
  simp only [transpose_transpose, Matrix.transpose_zero, Matrix.zero_mul, sub_zero]
  exact_mod_cast V.inv_mul

theorem Tmat_mem {S : Matrix (Fin n) (Fin n) R} (hS : Sᵀ = S) : Tmat S ∈ symplecticGroup (Fin n) R := by
  rw [Tmat, fromBlocks_mem_symplecticGroup_iff]
  refine ⟨by simp, by simp [hS], by simp⟩

theorem Jn_mem : Jn n R ∈ symplecticGroup (Fin n) R := by
  rw [Jn_eq_neg_J]
  exact SymplecticGroup.neg_mem (SymplecticGroup.J_mem _ _)

end Symplectic

section PosDefComplex

variable {ι : Type*} [Fintype ι]

/-- A real positive definite matrix stays positive definite over `ℂ`. -/
theorem posDef_map_ofReal {Y : Matrix ι ι ℝ} (hY : Y.PosDef) : (Y.map (↑) : Matrix ι ι ℂ).PosDef := by
  classical
  rw [posDef_iff_dotProduct_mulVec] at hY ⊢
  obtain ⟨hH, hpos⟩ := hY
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    have := congrFun (congrFun hH i) j
    simp only [conjTranspose_apply, map_apply, Complex.star_def, Complex.conj_ofReal, star_trivial] at this ⊢
    exact_mod_cast this
  · set a : ι → ℝ := fun i => (x i).re
    set b : ι → ℝ := fun i => (x i).im
    have hsym : ∀ i j, Y i j = Y j i := fun i j => by
      have := congrFun (congrFun hH j) i
      simpa [conjTranspose_apply] using this
    have hre : (star x ⬝ᵥ (Y.map (↑) *ᵥ x)).re = a ⬝ᵥ (Y *ᵥ a) + b ⬝ᵥ (Y *ᵥ b) := by
      simp only [dotProduct, mulVec, Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp [a, b, Complex.mul_re, Complex.mul_im]
    have him : (star x ⬝ᵥ (Y.map (↑) *ᵥ x)).im = 0 := by
      have h1 : (star x ⬝ᵥ (Y.map (↑) *ᵥ x)).im = ∑ i, ∑ j, Y i j * (a i * b j - b i * a j) := by
        simp only [dotProduct, mulVec, Complex.im_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp [a, b, Complex.mul_re, Complex.mul_im]; ring
      rw [h1]
      have h2 : ∑ i, ∑ j, Y i j * (a i * b j - b i * a j) =
          -∑ i, ∑ j, Y i j * (a i * b j - b i * a j) := by
        conv_rhs => rw [Finset.sum_comm]
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsym j i]; ring
      linarith
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      funext i
      apply Complex.ext
      · simpa [a] using congrFun h.1 i
      · simpa [b] using congrFun h.2 i
    have hpos' : 0 < a ⬝ᵥ (Y *ᵥ a) + b ⬝ᵥ (Y *ᵥ b) := by
      have hna : 0 ≤ a ⬝ᵥ (Y *ᵥ a) := by
        by_cases ha : a = 0
        · simp [ha]
        · simpa using (hpos ha).le
      have hnb : 0 ≤ b ⬝ᵥ (Y *ᵥ b) := by
        by_cases hb : b = 0
        · simp [hb]
        · simpa using (hpos hb).le
      rcases hab with ha | hb
      · have := hpos ha; simp only [star_trivial] at this; linarith
      · have := hpos hb; simp only [star_trivial] at this; linarith
    rw [Complex.lt_def]
    exact ⟨by simpa [hre] using hpos', by simpa using him.symm⟩

/-- A real symmetric matrix whose complexification is positive definite is positive definite. -/
theorem posDef_of_map_ofReal {Y : Matrix ι ι ℝ} (hY : (Y.map (↑) : Matrix ι ι ℂ).PosDef) : Y.PosDef := by
  classical
  rw [posDef_iff_dotProduct_mulVec] at hY ⊢
  obtain ⟨hH, hpos⟩ := hY
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    have := congrFun (congrFun hH i) j
    simp only [conjTranspose_apply, map_apply, Complex.star_def, Complex.conj_ofReal] at this
    simp only [conjTranspose_apply, star_trivial]
    exact_mod_cast this
  · have hx' : (fun i => (x i : ℂ)) ≠ 0 := by
      intro h; apply hx; ext i; simpa using congrFun h i
    have := hpos hx'
    have heq : star (fun i => (x i : ℂ)) ⬝ᵥ ((Y.map (↑) : Matrix ι ι ℂ) *ᵥ fun i => (x i : ℂ)) =
        ((star x ⬝ᵥ (Y *ᵥ x) : ℝ) : ℂ) := by
      simp [dotProduct, mulVec, Complex.ofReal_sum, Complex.ofReal_mul]
    rw [heq] at this
    exact_mod_cast this

end PosDefComplex

section HalfSpace

variable (n : ℕ)

/-- **Andrianov–Zhuravlev (1.10).** The Siegel upper half-plane of degree `n`: complex symmetric `n × n` matrices
`Z = X + iY` with `Y` positive definite. -/
@[kb "andrianovzhuravlev1995" "Chapter 1, (1.10), p. 15"]
def siegelSet : Set (Matrix (Fin n) (Fin n) ℂ) := {Z | Zᵀ = Z ∧ (Z.map Complex.im).PosDef}

/-- The Siegel upper half-plane `H_n` as a type. -/
abbrev SiegelSpace : Type := {Z : Matrix (Fin n) (Fin n) ℂ // Z ∈ siegelSet n}

variable {n}

namespace SiegelSpace

@[ext] theorem ext {Z W : SiegelSpace n} (h : (Z : Matrix (Fin n) (Fin n) ℂ) = W) : Z = W := Subtype.ext h

/-- The imaginary part `Y` of `Z = X + iY`. -/
def im (Z : SiegelSpace n) : Matrix (Fin n) (Fin n) ℝ := (Z : Matrix (Fin n) (Fin n) ℂ).map Complex.im

/-- The real part `X` of `Z = X + iY`. -/
def re (Z : SiegelSpace n) : Matrix (Fin n) (Fin n) ℝ := (Z : Matrix (Fin n) (Fin n) ℂ).map Complex.re

theorem transpose_eq (Z : SiegelSpace n) : (Z : Matrix (Fin n) (Fin n) ℂ)ᵀ = Z := Z.2.1

theorem im_posDef (Z : SiegelSpace n) : Z.im.PosDef := Z.2.2

end SiegelSpace

/-- **Andrianov–Zhuravlev, Proposition 2.6 (convexity).** `H_n` is convex (hence simply connected). -/
@[kb "andrianovzhuravlev1995" "Chapter 1, Proposition 2.6, p. 19"]
theorem convex_siegelSet : Convex ℝ (siegelSet n) := by
  intro Z hZ W hW a b ha hb hab
  refine ⟨by rw [transpose_add, transpose_smul, transpose_smul, hZ.1, hW.1], ?_⟩
  have him : (a • Z + b • W).map Complex.im = a • Z.map Complex.im + b • W.map Complex.im := by
    ext i j; simp
  rw [him]
  rcases ha.lt_or_eq with ha' | ha'
  · exact (hZ.2.smul ha').add_posSemidef (hW.2.posSemidef.smul hb)
  · subst ha'
    have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hW.2

end HalfSpace

section Action

variable {n : ℕ}

/-- Complexification of a real matrix. -/
abbrev cx {ι κ : Type*} (A : Matrix ι κ ℝ) : Matrix ι κ ℂ := A.map (↑)

/-- The automorphy matrix `CZ + D` of `M = (A B; C D)` at `Z`. -/
noncomputable def jmat (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  cx M.toBlocks₂₁ * Z + cx M.toBlocks₂₂

/-- The numerator `AZ + B` of `M⟨Z⟩`. -/
noncomputable def nmat (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  cx M.toBlocks₁₁ * Z + cx M.toBlocks₁₂

/-- The fractional linear transformation `M⟨Z⟩ = (AZ + B)(CZ + D)⁻¹`, (2.1). -/
noncomputable def moebius (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  nmat M Z * (jmat M Z)⁻¹

theorem cx_mul {ι κ μ : Type*} [Fintype κ] (A : Matrix ι κ ℝ) (B : Matrix κ μ ℝ) :
    cx (A * B) = cx A * cx B := by
  ext i j; simp [cx, Matrix.mul_apply]

theorem cx_transpose {ι κ : Type*} (A : Matrix ι κ ℝ) : (cx A)ᵀ = cx Aᵀ := rfl

theorem cx_conjTranspose {ι κ : Type*} (A : Matrix ι κ ℝ) : (cx A)ᴴ = (cx A)ᵀ := by
  ext i j; simp [conjTranspose_apply]

theorem cx_sub {ι κ : Type*} (A B : Matrix ι κ ℝ) : cx (A - B) = cx A - cx B := by
  ext i j; simp

theorem cx_add {ι κ : Type*} (A B : Matrix ι κ ℝ) : cx (A + B) = cx A + cx B := by
  ext i j; simp

theorem cx_zero {ι κ : Type*} : cx (0 : Matrix ι κ ℝ) = 0 := by
  ext i j; simp

theorem cx_one {ι : Type*} [DecidableEq ι] : cx (1 : Matrix ι ι ℝ) = 1 := by
  ext i j; by_cases h : i = j <;> simp [cx, Matrix.one_apply, h]

/-- The algebraic identity behind (2.11), for matrices satisfying (2.7) over any commutative ring. -/
theorem symplectic_identity {R : Type*} [CommRing R] {A B C D P S : Matrix (Fin n) (Fin n) R}
    (e1 : Aᵀ * C = Cᵀ * A) (e2 : Bᵀ * D = Dᵀ * B) (e3 : Aᵀ * D - Cᵀ * B = 1) :
    (C * P + D)ᵀ * (A * S + B) - (A * P + B)ᵀ * (C * S + D) = S - Pᵀ := by
  have e3' : Dᵀ * A - Bᵀ * C = 1 := by
    have := congrArg transpose e3
    simpa [transpose_sub, transpose_mul] using this
  have e3n : Cᵀ * B - Aᵀ * D = -1 := by rw [← e3]; abel
  simp only [transpose_add, transpose_mul]
  calc (Pᵀ * Cᵀ + Dᵀ) * (A * S + B) - (Pᵀ * Aᵀ + Bᵀ) * (C * S + D)
      = Pᵀ * (Cᵀ * A - Aᵀ * C) * S + Pᵀ * (Cᵀ * B - Aᵀ * D) + (Dᵀ * A - Bᵀ * C) * S
          + (Dᵀ * B - Bᵀ * D) := by noncomm_ring
    _ = S - Pᵀ := by rw [e1, sub_self, e3n, e3', e2, sub_self]; noncomm_ring

/-- The complexified block relations (2.7). -/
theorem cx_blocks {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hM : M ∈ symplecticGroup (Fin n) ℝ) :
    (cx M.toBlocks₁₁)ᵀ * cx M.toBlocks₂₁ = (cx M.toBlocks₂₁)ᵀ * cx M.toBlocks₁₁ ∧
      (cx M.toBlocks₁₂)ᵀ * cx M.toBlocks₂₂ = (cx M.toBlocks₂₂)ᵀ * cx M.toBlocks₁₂ ∧
      (cx M.toBlocks₁₁)ᵀ * cx M.toBlocks₂₂ - (cx M.toBlocks₂₁)ᵀ * cx M.toBlocks₁₂ = 1 := by
  obtain ⟨h1, h2, h3⟩ := blocks_of_mem hM
  simp only [cx_transpose, ← cx_mul, ← cx_sub]
  exact ⟨by rw [h1], by rw [h2], by rw [h3, cx_one]⟩

/-- The fundamental identity behind (2.11): for `M ∈ Sp_n(ℝ)` and arbitrary `P, R`,
`ᵗ(CP + D)(AR + B) - ᵗ(AP + B)(CR + D) = R - ᵗP`. -/
theorem jmat_transpose_mul_nmat_sub {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hM : M ∈ symplecticGroup (Fin n) ℝ) (P R : Matrix (Fin n) (Fin n) ℂ) :
    (jmat M P)ᵀ * nmat M R - (nmat M P)ᵀ * jmat M R = R - Pᵀ := by
  obtain ⟨e1, e2, e3⟩ := cx_blocks hM
  exact symplectic_identity e1 e2 e3

theorem jmat_conj_transpose (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (jmat M (Z.map star))ᵀ = (jmat M Z)ᴴ := by
  simp only [jmat, transpose_add, transpose_mul, conjTranspose_add, conjTranspose_mul, cx_conjTranspose]
  rfl

theorem nmat_conj_transpose (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (nmat M (Z.map star))ᵀ = (nmat M Z)ᴴ := by
  simp only [nmat, transpose_add, transpose_mul, conjTranspose_add, conjTranspose_mul, cx_conjTranspose]
  rfl

/-- For symmetric `W`, `W - Wᴴ = 2i Im W`. -/
theorem sub_conjTranspose_of_symm {W : Matrix (Fin n) (Fin n) ℂ} (hW : Wᵀ = W) :
    W - Wᴴ = (2 * Complex.I) • cx (W.map Complex.im) := by
  ext i j
  have : W j i = W i j := by simpa using congrFun (congrFun hW i) j
  simp only [Matrix.sub_apply, conjTranspose_apply, this, Matrix.smul_apply, map_apply, smul_eq_mul]
  rw [Complex.star_def, Complex.sub_conj]; push_cast; ring

/-- The identity `(CZ + D)ᴴ (AZ + B) - (AZ + B)ᴴ (CZ + D) = 2i Y` (from (2.11)). -/
theorem jmat_conjTranspose_identity {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hM : M ∈ symplecticGroup (Fin n) ℝ) (Z : SiegelSpace n) :
    (jmat M Z)ᴴ * nmat M Z - (nmat M Z)ᴴ * jmat M Z = (2 * Complex.I) • cx Z.im := by
  have h := jmat_transpose_mul_nmat_sub hM ((Z : Matrix (Fin n) (Fin n) ℂ).map star) Z
  rw [jmat_conj_transpose, nmat_conj_transpose] at h
  rw [h, ← transpose_map]
  exact sub_conjTranspose_of_symm Z.transpose_eq

/-- **Andrianov–Zhuravlev, Proposition 2.1 (first part).** For `M ∈ Sp_n(ℝ)` and `Z ∈ H_n` the matrix `CZ + D` is
invertible. -/
@[kb "andrianovzhuravlev1995" "Chapter 1, Proposition 2.1, p. 17"]
theorem isUnit_det_jmat {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hM : M ∈ symplecticGroup (Fin n) ℝ)
    (Z : SiegelSpace n) : IsUnit (jmat M Z).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hY := posDef_map_ofReal Z.im_posDef
  have hid := congrArg (fun X => star v ⬝ᵥ (X *ᵥ v)) (jmat_conjTranspose_identity hM Z)
  simp only [sub_mulVec, dotProduct_sub, ← mulVec_mulVec, hJv, mulVec_zero, dotProduct_zero, sub_zero,
    smul_mulVec, dotProduct_smul] at hid
  rw [dotProduct_mulVec, ← star_mulVec, hJv, star_zero, zero_dotProduct, smul_eq_mul] at hid
  have h2 : (2 * Complex.I) ≠ 0 := by simp
  have := (hY.dotProduct_mulVec_pos hv).ne'
  exact this (by simpa [h2] using hid.symm)

/-- `M⟨Z⟩` is symmetric. -/
theorem moebius_transpose {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hM : M ∈ symplecticGroup (Fin n) ℝ)
    (Z : SiegelSpace n) : (moebius M Z)ᵀ = moebius M Z := by
  have hu := isUnit_det_jmat hM Z
  have hut : IsUnit (jmat M Z)ᵀ.det := by rwa [det_transpose]
  have h := jmat_transpose_mul_nmat_sub hM (Z : Matrix (Fin n) (Fin n) ℂ) Z
  rw [Z.transpose_eq, sub_self, sub_eq_zero] at h
  set J := jmat M Z
  set N := nmat M Z
  rw [moebius, transpose_mul, transpose_nonsing_inv]
  calc Jᵀ⁻¹ * Nᵀ = Jᵀ⁻¹ * (Nᵀ * J) * J⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
    _ = Jᵀ⁻¹ * (Jᵀ * N) * J⁻¹ := by rw [h]
    _ = N * J⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hut, Matrix.one_mul]

/-- **Andrianov–Zhuravlev, Lemma 2.8.** If `Z' = X' + iY' = M⟨Z⟩`, then `Y' = ᵗ(C\bar Z + D)⁻¹ Y (CZ + D)⁻¹`; over
`ℂ`, `ᵗ(C\bar Z + D) = (CZ + D)ᴴ`. -/
@[kb "andrianovzhuravlev1995" "Chapter 1, Lemma 2.8, p. 20"]
theorem im_moebius {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hM : M ∈ symplecticGroup (Fin n) ℝ)
    (Z : SiegelSpace n) :
    cx ((moebius M Z).map Complex.im) = ((jmat M Z)⁻¹)ᴴ * cx Z.im * (jmat M Z)⁻¹ := by
  have hu := isUnit_det_jmat hM Z
  have huh : IsUnit (jmat M Z)ᴴ.det := by rw [det_conjTranspose]; exact hu.star
  have h1 := sub_conjTranspose_of_symm (moebius_transpose hM Z)
  have hid := jmat_conjTranspose_identity hM Z
  set J := jmat M Z
  set N := nmat M Z
  have h2 : moebius M Z - (moebius M Z)ᴴ = (J⁻¹)ᴴ * (Jᴴ * N - Nᴴ * J) * J⁻¹ := by
    show N * J⁻¹ - (N * J⁻¹)ᴴ = _
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
    rw [← Matrix.mul_assoc (Jᴴ⁻¹) Jᴴ, nonsing_inv_mul _ huh, Matrix.one_mul]
  rw [h1, hid, Matrix.mul_smul, Matrix.smul_mul] at h2
  have h2I : (2 * Complex.I) ≠ 0 := by simp
  exact smul_right_injective _ h2I h2

/-- **Andrianov–Zhuravlev, Lemma 2.8, (2.14).** `det Y' = |det(CZ + D)|⁻² det Y`. -/
@[kb "andrianovzhuravlev1995" "Chapter 1, Lemma 2.8, (2.14), p. 20"]
theorem det_im_moebius {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hM : M ∈ symplecticGroup (Fin n) ℝ)
    (Z : SiegelSpace n) :
    ((moebius M Z).map Complex.im).det = ‖(jmat M Z).det‖ ^ (-2 : ℤ) * Z.im.det := by
  have h := congrArg Matrix.det (im_moebius hM Z)
  have hcx : ∀ A : Matrix (Fin n) (Fin n) ℝ, (cx A).det = (A.det : ℂ) := fun A =>
    (RingHom.map_det Complex.ofRealHom A).symm
  rw [det_mul, det_mul, hcx, hcx, det_conjTranspose, det_nonsing_inv] at h
  have hu := isUnit_det_jmat hM Z
  set d := (jmat M Z).det
  have hd : d ≠ 0 := hu.ne_zero
  rw [Ring.inverse_eq_inv'] at h
  apply Complex.ofReal_injective
  have hn : ((‖d‖ : ℝ) : ℂ) ^ 2 = star d * d := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj']
  have hsd : star d ≠ 0 := star_ne_zero.2 hd
  rw [h, Complex.ofReal_mul, Complex.ofReal_zpow, _root_.zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hn, star_inv₀]
  field_simp

/-- **Andrianov–Zhuravlev, Proposition 2.1 (second part).** `M⟨Z⟩ ∈ H_n` for `M ∈ Sp_n(ℝ)`, `Z ∈ H_n`. -/
@[kb "andrianovzhuravlev1995" "Chapter 1, Proposition 2.1, p. 17"]
theorem moebius_mem {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hM : M ∈ symplecticGroup (Fin n) ℝ)
    (Z : SiegelSpace n) : moebius M Z ∈ siegelSet n := by
  refine ⟨moebius_transpose hM Z, posDef_of_map_ofReal ?_⟩
  have hinj : Function.Injective (jmat M Z)⁻¹.mulVec := by
    rw [mulVec_injective_iff_isUnit, isUnit_iff_isUnit_det, det_nonsing_inv]
    exact (isUnit_det_jmat hM Z).ringInverse
  have h := (posDef_map_ofReal Z.im_posDef).conjTranspose_mul_mul_same hinj
  rw [← im_moebius hM Z] at h
  exact h

end Action

section MulAction

variable {n : ℕ}

/-- The blocks of a product of `2n × 2n` matrices. -/
theorem toBlocks_mul {R : Type*} [CommRing R] (M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ + M.toBlocks₁₂ * N.toBlocks₂₁ ∧
    (M * N).toBlocks₁₂ = M.toBlocks₁₁ * N.toBlocks₁₂ + M.toBlocks₁₂ * N.toBlocks₂₂ ∧
    (M * N).toBlocks₂₁ = M.toBlocks₂₁ * N.toBlocks₁₁ + M.toBlocks₂₂ * N.toBlocks₂₁ ∧
    (M * N).toBlocks₂₂ = M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂ := by
  have h : M * N = fromBlocks (M.toBlocks₁₁ * N.toBlocks₁₁ + M.toBlocks₁₂ * N.toBlocks₂₁)
      (M.toBlocks₁₁ * N.toBlocks₁₂ + M.toBlocks₁₂ * N.toBlocks₂₂)
      (M.toBlocks₂₁ * N.toBlocks₁₁ + M.toBlocks₂₂ * N.toBlocks₂₁)
      (M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂) := by
    conv_lhs => rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N]
    rw [fromBlocks_multiply]
  rw [h]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem moebius_mul_jmat {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hN : N ∈ symplecticGroup (Fin n) ℝ)
    (Z : SiegelSpace n) : moebius N Z * jmat N Z = nmat N Z := by
  rw [moebius, Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det_jmat hN Z), Matrix.mul_one]

/-- `AZ + B` for a product: `(MN)` numerator `= (A N⟨Z⟩ + B)(C'Z + D')`. -/
theorem nmat_mul (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hN : N ∈ symplecticGroup (Fin n) ℝ) (Z : SiegelSpace n) :
    nmat (M * N) Z = nmat M (moebius N Z) * jmat N Z := by
  obtain ⟨h11, h12, -, -⟩ := toBlocks_mul M N
  rw [nmat, h11, h12, nmat, Matrix.add_mul, Matrix.mul_assoc (cx M.toBlocks₁₁), moebius_mul_jmat hN, nmat, jmat]
  simp only [cx_add, cx_mul]
  noncomm_ring

/-- **The cocycle relation** (used in (3.14) of Chapter 1): `j(MN, Z) = j(M, N⟨Z⟩) j(N, Z)` for `j(M, Z) = CZ + D`. -/
@[kb "andrianovzhuravlev1995" "Chapter 1, (3.14), p. 25"]
theorem jmat_mul (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hN : N ∈ symplecticGroup (Fin n) ℝ) (Z : SiegelSpace n) :
    jmat (M * N) Z = jmat M (moebius N Z) * jmat N Z := by
  obtain ⟨-, -, h21, h22⟩ := toBlocks_mul M N
  rw [jmat, h21, h22, jmat, Matrix.add_mul, Matrix.mul_assoc (cx M.toBlocks₂₁), moebius_mul_jmat hN, nmat, jmat]
  simp only [cx_add, cx_mul]
  noncomm_ring

theorem moebius_mul (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hN : N ∈ symplecticGroup (Fin n) ℝ) (Z : SiegelSpace n) :
    moebius (M * N) Z = moebius M (moebius N Z) := by
  rw [moebius, nmat_mul M hN, jmat_mul M hN, Matrix.mul_inv_rev, Matrix.mul_assoc,
    ← Matrix.mul_assoc (jmat N Z), mul_nonsing_inv _ (isUnit_det_jmat hN Z), Matrix.one_mul]
  rfl

theorem toBlocks_one_eq {R : Type*} [CommRing R] :
    (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R).toBlocks₁₁ = 1 ∧
    (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R).toBlocks₁₂ = 0 ∧
    (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R).toBlocks₂₁ = 0 ∧
    (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R).toBlocks₂₂ = 1 := by
  rw [← fromBlocks_one]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem moebius_one (Z : Matrix (Fin n) (Fin n) ℂ) : moebius 1 Z = Z := by
  obtain ⟨h1, h2, h3, h4⟩ := toBlocks_one_eq (n := n) (R := ℝ)
  simp [moebius, nmat, jmat, h1, h2, h3, h4, cx_one, cx_zero]

/-- **Andrianov–Zhuravlev, Proposition 2.1 and (2.10).** `M⟨Z⟩` as a point of `H_n`; `Sp_n(ℝ)` acts on `H_n` by
`Z ↦ M⟨Z⟩`. -/
@[kb "andrianovzhuravlev1995" "Chapter 1, Proposition 2.1, (2.10), p. 17–18"]
noncomputable def smulH (M : symplecticGroup (Fin n) ℝ) (Z : SiegelSpace n) : SiegelSpace n :=
  Subtype.mk (moebius M.1 Z.1) (moebius_mem M.2 Z)

noncomputable instance : SMul (symplecticGroup (Fin n) ℝ) (SiegelSpace n) := ⟨smulH⟩

theorem coe_smul' (M : symplecticGroup (Fin n) ℝ) (Z : SiegelSpace n) :
    (M • Z).1 = moebius (M : Matrix _ _ ℝ) Z.1 := rfl

noncomputable instance : MulAction (symplecticGroup (Fin n) ℝ) (SiegelSpace n) where
  one_smul Z := Subtype.ext (moebius_one Z.1)
  mul_smul M N Z := Subtype.ext (moebius_mul (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) N.2 Z)

theorem coe_smul (M : symplecticGroup (Fin n) ℝ) (Z : SiegelSpace n) :
    ((M • Z : SiegelSpace n) : Matrix (Fin n) (Fin n) ℂ) = moebius M Z := rfl

/-- The point `iE_n ∈ H_n`. -/
noncomputable def SiegelSpace.iE (n : ℕ) : SiegelSpace n :=
  ⟨Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ), by
    refine ⟨by simp, ?_⟩
    have : (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)).map Complex.im = 1 := by
      ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [this]; exact PosDef.one⟩

/-- The action of `T(S)`: `Z ↦ Z + S`. -/
theorem moebius_Tmat (S : Matrix (Fin n) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    moebius (Tmat S) Z = Z + cx S := by
  simp [moebius, nmat, jmat, Tmat, cx_one, cx_zero]

/-- The action of `U(V)`: `Z ↦ ᵗV⁻¹ Z V⁻¹`. -/
theorem moebius_Umat (V : (Matrix (Fin n) (Fin n) ℝ)ˣ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    moebius (Umat V) Z = cx (↑V⁻¹ : Matrix (Fin n) (Fin n) ℝ)ᵀ * Z * cx (↑V⁻¹ : Matrix (Fin n) (Fin n) ℝ) := by
  have h : (cx (V : Matrix (Fin n) (Fin n) ℝ))⁻¹ = cx (↑V⁻¹ : Matrix (Fin n) (Fin n) ℝ) := by
    apply Matrix.inv_eq_right_inv
    rw [← cx_mul, V.mul_inv, cx_one]
  simp [moebius, nmat, jmat, Umat, cx_zero, h]

/-- The action of `J_n`: `Z ↦ -Z⁻¹`. -/
theorem moebius_Jn (Z : SiegelSpace n) :
    moebius (Jn n ℝ) Z = -(Z : Matrix (Fin n) (Fin n) ℂ)⁻¹ := by
  have hj : jmat (Jn n ℝ) Z = -(Z : Matrix (Fin n) (Fin n) ℂ) := by
    have : cx (-1 : Matrix (Fin n) (Fin n) ℝ) = -1 := by ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
    simp [jmat, Jn, this, cx_zero]
  have hn : nmat (Jn n ℝ) Z = 1 := by simp [nmat, Jn, cx_one, cx_zero]
  have hu := isUnit_det_jmat (Jn_mem (n := n) (R := ℝ)) Z
  rw [hj, det_neg] at hu
  have hZ : IsUnit (Z : Matrix (Fin n) (Fin n) ℂ).det := (isUnit_of_mul_isUnit_right hu)
  rw [moebius, hn, hj, Matrix.one_mul]
  apply Matrix.inv_eq_left_inv
  rw [neg_mul_neg, nonsing_inv_mul _ hZ]

end MulAction

end ModularFormsKB.Andrianov
