import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.DoubleCoset
import ModularFormsKB.Citation
import ModularFormsKB.Milne.Ch5.Matrices

/-!
# Milne, Chapter 5: geometric interpretation of Hecke operators (Lemma 5.29, Remark 5.31)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf pp. 80–81.

$\Gamma$ is a subgroup of finite index of $\Gamma(1) = \mathrm{SL}_2(\mathbb Z)$, viewed in $\mathrm{GL}_2(\mathbb R)$
(`Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)`); right cosets are $\Gamma\beta$ and left cosets $\beta\Gamma$.

## Items
- Lemma 5.29 (`finite_rightCosets_iff`, `finite_leftCosets_iff`).
- Remark 5.31: correspondences (`Correspondence`, `Correspondence.ofGraph`), the Hecke correspondence
  $\Gamma\backslash\mathbb H \leftarrow \Gamma_\alpha\backslash\mathbb H \to \Gamma\backslash\mathbb H$
  (`heckeCorrespondence`), and the trace of $f \circ \alpha$ being $\Gamma$-invariant, p. 81 (`trace_slash_invariant`).
-/

open Matrix UpperHalfPlane

open scoped MatrixGroups ModularForm

namespace ModularFormsKB.Milne

/-- Cancellation of `D` in a sum of two products of relations `u * D = r`. -/
lemma prod_div_aux {D u v u' v' r s r' s' w : ℝ} (hu : u * D = r) (hv : v * D = s) (hu' : u' * D = r')
    (hv' : v' * D = s') (hD : D ≠ 0) (hrs : r * s + r' * s' = D * w) :
    (u * v + u' * v') * D = w := by
  have h : D * ((u * v + u' * v') * D - w) = 0 := by
    linear_combination (v * D) * hu + r * hv + (v' * D) * hu' + r' * hv' + hrs
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h hD
  · linarith

/-- The matrix-entry computation behind Lemma 5.29: if `α = (a b; c d)` of positive determinant conjugates
`(1 1; 0 1)^m` and `(1 0; 1 1)^m` into integer matrices `P`, `Q`, then `α` is a scalar multiple of an integer
matrix. -/
lemma scalar_int_of_conj (a b c d : ℝ) (m : ℤ) (hm : m ≠ 0) (hD : 0 < a * d - b * c)
    (p11 p12 p21 p22 q11 q12 q21 q22 : ℤ)
    (t1 : a = p11 * a + p12 * c) (t2 : m * a + b = p11 * b + p12 * d)
    (t3 : c = p21 * a + p22 * c) (t4 : m * c + d = p21 * b + p22 * d)
    (u1 : a + m * b = q11 * a + q12 * c) (u2 : b = q11 * b + q12 * d)
    (u3 : c + m * d = q21 * a + q22 * c) (u4 : d = q21 * b + q22 * d) :
    ∃ (c' : ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ),
      (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℝ) = c' • A.map (Int.cast : ℤ → ℝ) := by
  have hD0 : a * d - b * c ≠ 0 := hD.ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have f1 : ((p11 : ℝ) - 1) * (a * d - b * c) = -(m * a * c) := by linear_combination c * t2 - d * t1
  have f3 : (p12 : ℝ) * (a * d - b * c) = m * a * a := by linear_combination (-a) * t2 + b * t1
  have f5 : (p21 : ℝ) * (a * d - b * c) = -(m * c * c) := by linear_combination c * t4 - d * t3
  have f6 : ((p22 : ℝ) - 1) * (a * d - b * c) = m * a * c := by linear_combination b * t3 - a * t4
  have g2 : ((q11 : ℝ) - 1) * (a * d - b * c) = m * b * d := by linear_combination c * u2 - d * u1
  have g3 : (q12 : ℝ) * (a * d - b * c) = -(m * b * b) := by linear_combination b * u1 - a * u2
  have g5 : (q21 : ℝ) * (a * d - b * c) = m * d * d := by linear_combination c * u4 - d * u3
  have g6 : ((q22 : ℝ) - 1) * (a * d - b * c) = -(m * b * d) := by linear_combination b * u3 - a * u4
  have zaa : ∃ z : ℤ, (z : ℝ) * (a * d - b * c) = (m : ℝ) ^ 2 * (a * a) :=
    ⟨m * p12, by push_cast; linear_combination (m : ℝ) * f3⟩
  have zac : ∃ z : ℤ, (z : ℝ) * (a * d - b * c) = (m : ℝ) ^ 2 * (a * c) :=
    ⟨-(m * (p11 - 1)), by push_cast; linear_combination (-(m : ℝ)) * f1⟩
  have zcc : ∃ z : ℤ, (z : ℝ) * (a * d - b * c) = (m : ℝ) ^ 2 * (c * c) :=
    ⟨-(m * p21), by push_cast; linear_combination (-(m : ℝ)) * f5⟩
  have zbb : ∃ z : ℤ, (z : ℝ) * (a * d - b * c) = (m : ℝ) ^ 2 * (b * b) :=
    ⟨-(m * q12), by push_cast; linear_combination (-(m : ℝ)) * g3⟩
  have zbd : ∃ z : ℤ, (z : ℝ) * (a * d - b * c) = (m : ℝ) ^ 2 * (b * d) :=
    ⟨m * (q11 - 1), by push_cast; linear_combination (m : ℝ) * g2⟩
  have zdd : ∃ z : ℤ, (z : ℝ) * (a * d - b * c) = (m : ℝ) ^ 2 * (d * d) :=
    ⟨m * q21, by push_cast; linear_combination (m : ℝ) * g5⟩
  have zad : ∃ z : ℤ, (z : ℝ) * (a * d - b * c) = (m : ℝ) ^ 2 * (a * d) :=
    ⟨(p11 - 1) * (q11 - 1) + p12 * q21, by
      have := prod_div_aux (u := (p11 : ℝ) - 1) (v := (q11 : ℝ) - 1) (u' := p12) (v' := q21)
        (w := (m : ℝ) ^ 2 * (a * d)) f1 g2 f3 g5 hD0 (by ring)
      push_cast; linear_combination this⟩
  have zab : ∃ z : ℤ, (z : ℝ) * (a * d - b * c) = (m : ℝ) ^ 2 * (a * b) :=
    ⟨-((p11 - 1) * q12 + p12 * (q22 - 1)), by
      have := prod_div_aux (u := (p11 : ℝ) - 1) (v := (q12 : ℝ)) (u' := p12) (v' := (q22 : ℝ) - 1)
        (w := -((m : ℝ) ^ 2 * (a * b))) f1 g3 f3 g6 hD0 (by ring)
      push_cast; linear_combination -this⟩
  have zcd : ∃ z : ℤ, (z : ℝ) * (a * d - b * c) = (m : ℝ) ^ 2 * (c * d) :=
    ⟨p21 * (q11 - 1) + (p22 - 1) * q21, by
      have := prod_div_aux (u := (p21 : ℝ)) (v := (q11 : ℝ) - 1) (u' := (p22 : ℝ) - 1) (v' := q21)
        (w := (m : ℝ) ^ 2 * (c * d)) f5 g2 f6 g5 hD0 (by ring)
      push_cast; linear_combination this⟩
  have zbc : ∃ z : ℤ, (z : ℝ) * (a * d - b * c) = (m : ℝ) ^ 2 * (b * c) := by
    obtain ⟨z, hz⟩ := zad
    exact ⟨z - m ^ 2, by push_cast; linear_combination hz⟩
  have hZc : ∀ x y : ℝ, (∃ z : ℤ, (z : ℝ) * (a * d - b * c) = (m : ℝ) ^ 2 * (x * y)) →
      ∃ z : ℤ, (z : ℝ) * (a * d - b * c) = (m : ℝ) ^ 2 * (y * x) := by
    rintro x y ⟨z, hz⟩
    exact ⟨z, by rw [mul_comm y x]; exact hz⟩
  have hS : ∀ x ∈ ({a, b, c, d} : Set ℝ), ∀ y ∈ ({a, b, c, d} : Set ℝ),
      ∃ z : ℤ, (z : ℝ) * (a * d - b * c) = (m : ℝ) ^ 2 * (x * y) := by
    rintro x (rfl | rfl | rfl | rfl) y (rfl | rfl | rfl | rfl) <;>
    first
    | exact zaa | exact zab | exact zac | exact zad | exact zbb | exact zbc | exact zbd | exact zcc
    | exact zcd | exact zdd
    | exact hZc _ _ zab | exact hZc _ _ zac | exact hZc _ _ zad | exact hZc _ _ zbc
    | exact hZc _ _ zbd | exact hZc _ _ zcd
  obtain ⟨e, he, he0⟩ : ∃ e ∈ ({a, b, c, d} : Set ℝ), e ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have ha := hcon a (by simp)
    have hb := hcon b (by simp)
    have hc := hcon c (by simp)
    have hd := hcon d (by simp)
    rw [ha, hb, hc, hd] at hD
    simp at hD
  obtain ⟨z0, hz0⟩ := hS e he e he
  have hz0ne : (z0 : ℝ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hz0
    exact mul_ne_zero (pow_ne_zero 2 hm') (mul_ne_zero he0 he0) hz0.symm
  choose! zf hzf using fun x (hx : x ∈ ({a, b, c, d} : Set ℝ)) => hS x hx e he
  have key : ∀ x ∈ ({a, b, c, d} : Set ℝ), x = e / z0 * zf x := by
    intro x hx
    have h1 := hzf x hx
    have h2 : (a * d - b * c) * (x * z0 - e * zf x) = 0 := by
      linear_combination x * hz0 - e * h1
    have h3 : x * z0 - e * zf x = 0 := (mul_eq_zero.1 h2).resolve_left hD0
    rw [div_mul_eq_mul_div, eq_div_iff hz0ne]
    linarith
  refine ⟨e / z0, !![zf a, zf b; zf c, zf d], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using key a (by simp)
  · simpa using key b (by simp)
  · simpa using key c (by simp)
  · simpa using key d (by simp)

/-- The upper unipotent `(1 1; 0 1)` in `SL₂(ℤ)`. -/
def unipT : SL(2, ℤ) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

/-- The lower unipotent `(1 0; 1 1)` in `SL₂(ℤ)`. -/
def unipU : SL(2, ℤ) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

lemma unipT_pow (n : ℕ) :
    ((unipT ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (n : ℤ); 0, 1] := by
  induction n with
  | zero => simp [Matrix.one_fin_two]
  | succ n ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
    simp [unipT, add_comm]

/-- Entries of the real matrix of `mapGL ℝ g`. -/
lemma coe_mapGL_entry (g : SL(2, ℤ)) (i j : Fin 2) :
    ((SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      ((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ) := by
  simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]

lemma unipU_pow (n : ℕ) :
    ((unipU ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; (n : ℤ), 1] := by
  induction n with
  | zero => simp [Matrix.one_fin_two]
  | succ n ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
    simp [unipU, Matrix.mul_fin_two]

/-- Lemma 5.29 (⇒), matrix part: if a finite-index subgroup `H` of `SL₂(ℤ)` has all conjugates by `α`
integral, then `α` is a scalar multiple of an integer matrix. -/
lemma scalar_int_of_finite_index (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    (H : Subgroup SL(2, ℤ)) (hH : H.index ≠ 0)
    (hHmem : ∀ γ ∈ H, ∃ g : SL(2, ℤ),
      α * SpecialLinearGroup.mapGL ℝ γ = SpecialLinearGroup.mapGL ℝ g * α) :
    ∃ (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ),
      (α : Matrix (Fin 2) (Fin 2) ℝ) = c • A.map (Int.cast : ℤ → ℝ) := by
  obtain ⟨n, hn, -, hnT⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hH unipT
  obtain ⟨n', hn', -, hnU⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hH unipU
  have hT : unipT ^ (n * n') ∈ H := by rw [pow_mul]; exact H.pow_mem hnT _
  have hU : unipU ^ (n * n') ∈ H := by rw [mul_comm, pow_mul]; exact H.pow_mem hnU _
  obtain ⟨gT, hgT⟩ := hHmem _ hT
  obtain ⟨gU, hgU⟩ := hHmem _ hU
  have eT := congrArg (fun x : GL (Fin 2) ℝ => (x : Matrix (Fin 2) (Fin 2) ℝ)) hgT
  have eU := congrArg (fun x : GL (Fin 2) ℝ => (x : Matrix (Fin 2) (Fin 2) ℝ)) hgU
  simp only [Units.val_mul] at eT eU
  have hD : 0 < (α : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (α : Matrix (Fin 2) (Fin 2) ℝ) 1 1 -
      (α : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (α : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at hα
    exact hα
  have e00 := congrFun (congrFun eT 0) 0
  have e01 := congrFun (congrFun eT 0) 1
  have e10 := congrFun (congrFun eT 1) 0
  have e11 := congrFun (congrFun eT 1) 1
  have f00 := congrFun (congrFun eU 0) 0
  have f01 := congrFun (congrFun eU 0) 1
  have f10 := congrFun (congrFun eU 1) 0
  have f11 := congrFun (congrFun eU 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, coe_mapGL_entry, unipT_pow, unipU_pow] at e00 e01 e10 e11 f00 f01 f10 f11
  try simp at e00 e01 e10 e11 f00 f01 f10 f11
  obtain ⟨c', A, h⟩ := scalar_int_of_conj ((α : Matrix (Fin 2) (Fin 2) ℝ) 0 0)
    ((α : Matrix (Fin 2) (Fin 2) ℝ) 0 1) ((α : Matrix (Fin 2) (Fin 2) ℝ) 1 0)
    ((α : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ((n * n' : ℕ) : ℤ) (by positivity) hD
    ((gT : Matrix (Fin 2) (Fin 2) ℤ) 0 0) ((gT : Matrix (Fin 2) (Fin 2) ℤ) 0 1)
    ((gT : Matrix (Fin 2) (Fin 2) ℤ) 1 0) ((gT : Matrix (Fin 2) (Fin 2) ℤ) 1 1)
    ((gU : Matrix (Fin 2) (Fin 2) ℤ) 0 0) ((gU : Matrix (Fin 2) (Fin 2) ℤ) 0 1)
    ((gU : Matrix (Fin 2) (Fin 2) ℤ) 1 0) ((gU : Matrix (Fin 2) (Fin 2) ℤ) 1 1)
    (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
    (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith) (by push_cast; linarith)
  exact ⟨c', A, by rw [← h]; exact Matrix.eta_fin_two _⟩

/-- The subgroup of `γ ∈ Γ` with `α γ α⁻¹` in the image of `Γ`. -/
def conjStab (Γ : Subgroup SL(2, ℤ)) (α : GL (Fin 2) ℝ) : Subgroup SL(2, ℤ) :=
  Γ ⊓ (Γ.map (SpecialLinearGroup.mapGL ℝ)).comap
    ((MulAut.conj α).toMonoidHom.comp (SpecialLinearGroup.mapGL ℝ))

lemma mem_conjStab {Γ : Subgroup SL(2, ℤ)} {α : GL (Fin 2) ℝ} {γ : SL(2, ℤ)} :
    γ ∈ conjStab Γ α ↔ γ ∈ Γ ∧
      α * SpecialLinearGroup.mapGL ℝ γ * α⁻¹ ∈ Γ.map (SpecialLinearGroup.mapGL ℝ) := by
  simp [conjStab, MulAut.conj_apply]

/-- Lemma 5.29 (⇒) for right cosets. -/
lemma right_forward (Γ : Subgroup SL(2, ℤ)) (hΓ : Γ.index ≠ 0) (α : GL (Fin 2) ℝ)
    (hα : 0 < α.det.val) (s : Finset (GL (Fin 2) ℝ))
    (hs : DoubleCoset.doubleCoset α (Γ.map (SpecialLinearGroup.mapGL ℝ) : Set _)
        (Γ.map (SpecialLinearGroup.mapGL ℝ)) = ⋃ β ∈ s, {x | x * β⁻¹ ∈ Γ.map (SpecialLinearGroup.mapGL ℝ)}) :
    ∃ (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ),
      (α : Matrix (Fin 2) (Fin 2) ℝ) = c • A.map (Int.cast : ℤ → ℝ) := by
  have hex : ∀ δ : Γ, ∃ b : s, (α * SpecialLinearGroup.mapGL ℝ ((δ⁻¹ : Γ) : SL(2, ℤ))) *
      (b : GL (Fin 2) ℝ)⁻¹ ∈ Γ.map (SpecialLinearGroup.mapGL ℝ) := by
    intro δ
    have hmem : α * SpecialLinearGroup.mapGL ℝ ((δ⁻¹ : Γ) : SL(2, ℤ)) ∈
        DoubleCoset.doubleCoset α (Γ.map (SpecialLinearGroup.mapGL ℝ) : Set _)
          (Γ.map (SpecialLinearGroup.mapGL ℝ)) :=
      DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, _, Subgroup.mem_map_of_mem _ (δ⁻¹ : Γ).2, by simp⟩
    rw [hs] at hmem
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hmem
    obtain ⟨β, hβ, h⟩ := hmem
    exact ⟨⟨β, hβ⟩, h⟩
  choose g hg using hex
  have hinj : Function.Injective
      (fun q : Γ ⧸ (conjStab Γ α).subgroupOf Γ => g q.out) := by
    intro a b hab
    have hab' : g a.out = g b.out := hab
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b, QuotientGroup.eq]
    have h1 := hg a.out
    have h2 := hg b.out
    rw [hab'] at h1
    have h3 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
    refine Subgroup.mem_subgroupOf.2 (mem_conjStab.2 ⟨(a.out⁻¹ * b.out).2, ?_⟩)
    convert h3 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    group
  have : Finite (Γ ⧸ (conjStab Γ α).subgroupOf Γ) := Finite.of_injective _ hinj
  have hrel : ((conjStab Γ α).subgroupOf Γ).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hH : (conjStab Γ α).index ≠ 0 := by
    rw [← Subgroup.relIndex_mul_index (show conjStab Γ α ≤ Γ from fun x hx => (mem_conjStab.1 hx).1)]
    exact mul_ne_zero hrel hΓ
  refine scalar_int_of_finite_index α hα _ hH (fun γ hγ => ?_)
  obtain ⟨-, g', -, hg'⟩ := mem_conjStab.1 hγ
  exact ⟨g', by rw [hg']; group⟩

/-- Entries of the real matrix of `mapGL ℝ g`, as a matrix. -/
lemma coe_mapGL (g : SL(2, ℤ)) :
    ((SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (g : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ) := by
  ext i j
  simp [coe_mapGL_entry]

lemma map_cast_mul (M N : Matrix (Fin 2) (Fin 2) ℤ) :
    (M * N).map (Int.cast : ℤ → ℝ) = M.map (Int.cast : ℤ → ℝ) * N.map (Int.cast : ℤ → ℝ) := by
  ext i j
  simp [Matrix.mul_apply]

lemma eq_mul_of_mat (x y : GL (Fin 2) ℝ) (C : Matrix (Fin 2) (Fin 2) ℝ) (γx γy : SL(2, ℤ))
    (hx : (x : Matrix (Fin 2) (Fin 2) ℝ) =
      ((SpecialLinearGroup.mapGL ℝ γx : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * C)
    (hy : (y : Matrix (Fin 2) (Fin 2) ℝ) =
      ((SpecialLinearGroup.mapGL ℝ γy : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * C) :
    x = SpecialLinearGroup.mapGL ℝ (γx * γy⁻¹) * y := by
  apply Units.ext
  rw [Units.val_mul, hy, hx, ← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, mul_assoc,
    inv_mul_cancel, mul_one]

lemma hermite_rep (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) (hn : 0 < n) (hA : A.det = n)
    (g1 g2 : SL(2, ℤ)) :
    ∃ t ∈ hermiteTriples n, ∃ γ : SL(2, ℤ),
      (g1 : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ) * (c • A.map (Int.cast : ℤ → ℝ)) *
        (g2 : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ) *
        (c • (upperTri t.1 t.2.1 t.2.2).map (Int.cast : ℤ → ℝ)) := by
  have hdet : ((g1 : Matrix (Fin 2) (Fin 2) ℤ) * A * g2).det = n := by
    rw [Matrix.det_mul, Matrix.det_mul, g1.2, g2.2, one_mul, mul_one, hA]
  obtain ⟨t, ⟨ht, γ, hγ⟩, -⟩ := exists_unique_hermiteTriple_SL hn _ hdet
  refine ⟨t, ht, γ, ?_⟩
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, ← map_cast_mul, ← map_cast_mul,
    ← map_cast_mul, ← hγ]

lemma doubleCoset_left_mul_mem (Γ : Subgroup SL(2, ℤ)) (α z β : GL (Fin 2) ℝ)
    (hz : z ∈ Γ.map (SpecialLinearGroup.mapGL ℝ))
    (hβ : β ∈ DoubleCoset.doubleCoset α (Γ.map (SpecialLinearGroup.mapGL ℝ) : Set _)
      (Γ.map (SpecialLinearGroup.mapGL ℝ))) :
    z * β ∈ DoubleCoset.doubleCoset α (Γ.map (SpecialLinearGroup.mapGL ℝ) : Set _)
      (Γ.map (SpecialLinearGroup.mapGL ℝ)) := by
  obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hβ
  exact DoubleCoset.mem_doubleCoset.2 ⟨z * h, Subgroup.mul_mem _ hz hh, k, hk, by group⟩

/-- Lemma 5.29 (⇐) for right cosets. -/
lemma right_backward (Γ : Subgroup SL(2, ℤ)) (hΓ : Γ.index ≠ 0) (α : GL (Fin 2) ℝ)
    (hα : 0 < α.det.val) (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hcA : (α : Matrix (Fin 2) (Fin 2) ℝ) = c • A.map (Int.cast : ℤ → ℝ)) :
    ∃ s : Finset (GL (Fin 2) ℝ), DoubleCoset.doubleCoset α (Γ.map (SpecialLinearGroup.mapGL ℝ) : Set _)
        (Γ.map (SpecialLinearGroup.mapGL ℝ)) = ⋃ β ∈ s, {x | x * β⁻¹ ∈ Γ.map (SpecialLinearGroup.mapGL ℝ)} := by
  have hdetA : (A.map (Int.cast : ℤ → ℝ)).det = (A.det : ℝ) := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two]; simp
  have hdetα : α.det.val = c ^ 2 * (A.det : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hcA, Matrix.det_smul, Fintype.card_fin, hdetA]
  have hApos : 0 < A.det := by
    by_contra h
    push Not at h
    have h' : (A.det : ℝ) ≤ 0 := by exact_mod_cast h
    rw [hdetα] at hα
    nlinarith [mul_nonneg (sq_nonneg c) (neg_nonneg.2 h')]
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hApos.le
  have hn0 : 0 < n := by omega
  have hA' : ∀ x ∈ DoubleCoset.doubleCoset α (Γ.map (SpecialLinearGroup.mapGL ℝ) : Set _)
      (Γ.map (SpecialLinearGroup.mapGL ℝ)), ∃ t ∈ hermiteTriples n, ∃ γ : SL(2, ℤ),
      (x : Matrix (Fin 2) (Fin 2) ℝ) =
        ((SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
          (c • (upperTri t.1 t.2.1 t.2.2).map (Int.cast : ℤ → ℝ)) := by
    intro x hx
    obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hx
    obtain ⟨g1, -, rfl⟩ := Subgroup.mem_map.1 hh
    obtain ⟨g2, -, rfl⟩ := Subgroup.mem_map.1 hk
    obtain ⟨t, ht, γ, hγ⟩ := hermite_rep c A n hn0 hn g1 g2
    refine ⟨t, ht, γ, ?_⟩
    rw [Units.val_mul, Units.val_mul, hcA, coe_mapGL, coe_mapGL, coe_mapGL]
    exact hγ
  choose! tf htf γf hγf using hA'
  have : Γ.FiniteIndex := ⟨hΓ⟩
  let K : {x // x ∈ DoubleCoset.doubleCoset α (Γ.map (SpecialLinearGroup.mapGL ℝ) : Set _)
      (Γ.map (SpecialLinearGroup.mapGL ℝ))} → ↥(hermiteTriples n) × (SL(2, ℤ) ⧸ Γ) := fun x =>
    (⟨tf x.1, (htf x.1 x.2)⟩, (QuotientGroup.mk ((γf x.1)⁻¹) : SL(2, ℤ) ⧸ Γ))
  choose rep hrep using fun p : ↥(Set.range K) => p.2
  refine ⟨(Set.finite_range (fun p : ↥(Set.range K) => (rep p).1)).toFinset, ?_⟩
  ext x
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.Finite.mem_toFinset, Set.mem_range,
    exists_prop]
  constructor
  · intro hx
    refine ⟨(rep ⟨K ⟨x, hx⟩, ⟨_, rfl⟩⟩).1, ⟨_, rfl⟩, ?_⟩
    have hK := hrep ⟨K ⟨x, hx⟩, ⟨_, rfl⟩⟩
    have hy := (rep ⟨K ⟨x, hx⟩, ⟨_, rfl⟩⟩).2
    set y := rep ⟨K ⟨x, hx⟩, ⟨_, rfl⟩⟩ with hydef
    have ht : tf y.1 = tf x := by
      have := congrArg (fun q => (q.1 : ℕ × ℕ × ℕ)) hK
      simpa [K] using this
    have hq : (QuotientGroup.mk ((γf y.1)⁻¹) : SL(2, ℤ) ⧸ Γ) = QuotientGroup.mk ((γf x)⁻¹) := by
      have := congrArg (fun q => q.2) hK
      simpa [K] using this
    have hq2 := QuotientGroup.eq.1 hq.symm
    have hxm := hγf x hx
    have hym := hγf y.1 y.2
    rw [ht] at hym
    have := eq_mul_of_mat x y.1 _ (γf x) (γf y.1) hxm hym
    have hmem : γf x * (γf y.1)⁻¹ ∈ Γ := by simpa using hq2
    rw [mul_inv_eq_iff_eq_mul.2 this]
    exact Subgroup.mem_map_of_mem _ hmem
  · rintro ⟨β, ⟨p, rfl⟩, h⟩
    have := doubleCoset_left_mul_mem Γ α _ _ h (rep p).2
    simpa using this

/-- **Milne, Lemma 5.29** (right cosets). Let $\Gamma$ have finite index in $\Gamma(1)$ and
$\alpha \in \mathrm{GL}_2(\mathbb R)^+$. Then $\Gamma\alpha\Gamma$ is a finite union of right cosets $\Gamma\beta$ if
and only if $\alpha$ is a scalar multiple of a matrix with integer coefficients. (Milne omits the proof.) -/
@[kb "milne2017mf" "Section 5, Lemma 5.29 (pdf p. 80)"]
theorem finite_rightCosets_iff (Γ : Subgroup SL(2, ℤ)) (hΓ : Γ.index ≠ 0) (α : GL (Fin 2) ℝ)
    (hα : 0 < α.det.val) :
    (∃ s : Finset (GL (Fin 2) ℝ), DoubleCoset.doubleCoset α (Γ.map (SpecialLinearGroup.mapGL ℝ) : Set _)
        (Γ.map (SpecialLinearGroup.mapGL ℝ)) = ⋃ β ∈ s, {x | x * β⁻¹ ∈ Γ.map (SpecialLinearGroup.mapGL ℝ)}) ↔
      ∃ (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ), (α : Matrix (Fin 2) (Fin 2) ℝ) = c • A.map (Int.cast : ℤ → ℝ) := by
  constructor
  · rintro ⟨s, hs⟩
    exact right_forward Γ hΓ α hα s hs
  · rintro ⟨c, A, h⟩
    exact right_backward Γ hΓ α hα c A h

/-- Inversion maps the double coset of `α` into that of `α⁻¹`. -/
lemma doubleCoset_inv_aux (Γ : Subgroup SL(2, ℤ)) (α x : GL (Fin 2) ℝ)
    (hx : x ∈ DoubleCoset.doubleCoset α (Γ.map (SpecialLinearGroup.mapGL ℝ) : Set _)
      (Γ.map (SpecialLinearGroup.mapGL ℝ))) :
    x⁻¹ ∈ DoubleCoset.doubleCoset α⁻¹ (Γ.map (SpecialLinearGroup.mapGL ℝ) : Set _)
      (Γ.map (SpecialLinearGroup.mapGL ℝ)) := by
  obtain ⟨h, hh, k, hk, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hx
  exact DoubleCoset.mem_doubleCoset.2 ⟨k⁻¹, Subgroup.inv_mem _ hk, h⁻¹, Subgroup.inv_mem _ hh,
    by group⟩

/-- Left cosets for `α` correspond to right cosets for `α⁻¹`. -/
lemma left_iff_right_inv (Γ : Subgroup SL(2, ℤ)) (α : GL (Fin 2) ℝ) (s : Finset (GL (Fin 2) ℝ)) :
    (DoubleCoset.doubleCoset α (Γ.map (SpecialLinearGroup.mapGL ℝ) : Set _)
        (Γ.map (SpecialLinearGroup.mapGL ℝ)) =
      ⋃ β ∈ s, {x | β⁻¹ * x ∈ Γ.map (SpecialLinearGroup.mapGL ℝ)}) ↔
    (DoubleCoset.doubleCoset α⁻¹ (Γ.map (SpecialLinearGroup.mapGL ℝ) : Set _)
        (Γ.map (SpecialLinearGroup.mapGL ℝ)) =
      ⋃ β ∈ s.image (fun β => β⁻¹), {x | x * β⁻¹ ∈ Γ.map (SpecialLinearGroup.mapGL ℝ)}) := by
  have key : ∀ x, x ∈ DoubleCoset.doubleCoset α (Γ.map (SpecialLinearGroup.mapGL ℝ) : Set _)
      (Γ.map (SpecialLinearGroup.mapGL ℝ)) ↔ x⁻¹ ∈ DoubleCoset.doubleCoset α⁻¹
        (Γ.map (SpecialLinearGroup.mapGL ℝ) : Set _) (Γ.map (SpecialLinearGroup.mapGL ℝ)) :=
    fun x => ⟨doubleCoset_inv_aux Γ α x, fun h => by simpa using doubleCoset_inv_aux Γ α⁻¹ x⁻¹ h⟩
  have hL : ∀ x, (x ∈ ⋃ β ∈ s, {x | β⁻¹ * x ∈ Γ.map (SpecialLinearGroup.mapGL ℝ)}) ↔
      (x⁻¹ ∈ ⋃ β ∈ s.image (fun β => β⁻¹),
        {x | x * β⁻¹ ∈ Γ.map (SpecialLinearGroup.mapGL ℝ)}) := by
    intro x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_image, exists_prop]
    constructor
    · rintro ⟨β, hβ, h⟩
      refine ⟨β⁻¹, ⟨β, hβ, rfl⟩, ?_⟩
      simpa using Subgroup.inv_mem _ h
    · rintro ⟨_, ⟨β, hβ, rfl⟩, h⟩
      refine ⟨β, hβ, ?_⟩
      simpa using Subgroup.inv_mem _ h
  constructor
  · intro h
    ext y
    have := key y⁻¹
    rw [inv_inv] at this
    rw [← this, h, hL, inv_inv]
  · intro h
    ext x
    rw [key x, h, ← hL]

/-- The inverse of a scalar multiple of an integer matrix is again one. -/
lemma scalar_int_inv (α : GL (Fin 2) ℝ) (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (h : (α : Matrix (Fin 2) (Fin 2) ℝ) = c • A.map (Int.cast : ℤ → ℝ)) :
    ∃ (c' : ℝ) (A' : Matrix (Fin 2) (Fin 2) ℤ),
      ((α⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = c' • A'.map (Int.cast : ℤ → ℝ) := by
  have h' : ∀ i j, (α : Matrix (Fin 2) (Fin 2) ℝ) i j = c * A i j := fun i j => by
    rw [h]; simp
  refine ⟨((α : Matrix (Fin 2) (Fin 2) ℝ).det)⁻¹ * c,
    !![A 1 1, -A 0 1; -A 1 0, A 0 0], ?_⟩
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h'] <;> ring

/-- **Milne, Lemma 5.29** (left cosets): the same with left cosets $\beta\Gamma$. -/
@[kb "milne2017mf" "Section 5, Lemma 5.29 (pdf p. 80)"]
theorem finite_leftCosets_iff (Γ : Subgroup SL(2, ℤ)) (hΓ : Γ.index ≠ 0) (α : GL (Fin 2) ℝ)
    (hα : 0 < α.det.val) :
    (∃ s : Finset (GL (Fin 2) ℝ), DoubleCoset.doubleCoset α (Γ.map (SpecialLinearGroup.mapGL ℝ) : Set _)
        (Γ.map (SpecialLinearGroup.mapGL ℝ)) = ⋃ β ∈ s, {x | β⁻¹ * x ∈ Γ.map (SpecialLinearGroup.mapGL ℝ)}) ↔
      ∃ (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ), (α : Matrix (Fin 2) (Fin 2) ℝ) = c • A.map (Int.cast : ℤ → ℝ) := by
  have hα' : 0 < (α⁻¹).det.val := by simpa [map_inv] using inv_pos.2 hα
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨c, A, h⟩ := right_forward Γ hΓ α⁻¹ hα' _ ((left_iff_right_inv Γ α s).1 hs)
    obtain ⟨c', A', h'⟩ := scalar_int_inv α⁻¹ c A h
    exact ⟨c', A', by simpa using h'⟩
  · rintro ⟨c, A, h⟩
    obtain ⟨c', A', h'⟩ := scalar_int_inv α c A h
    obtain ⟨s, hs⟩ := right_backward Γ hΓ α⁻¹ hα' c' A' h'
    refine ⟨s.image (fun β => β⁻¹), (left_iff_right_inv Γ α _).2 ?_⟩
    have : (s.image (fun β => β⁻¹)).image (fun β => β⁻¹) = s := by ext; simp
    rw [this]
    exact hs

/-- **Correspondence** (Milne, Remark 5.31): a diagram $X \leftarrow Y \to Z$ of finite-to-one maps, a "many-valued
map" sending $x$ to the images in $Z$ of its inverse images in $Y$. -/
@[kb "milne2017mf" "Section 5, Remark 5.31, correspondence (pdf p. 81)"]
structure Correspondence (X Z : Type*) where
  /-- The middle object `Y`. -/
  Y : Type
  /-- The map `Y → X`. -/
  left : Y → X
  /-- The map `Y → Z`. -/
  right : Y → Z
  finite_left : ∀ x, (left ⁻¹' {x}).Finite
  finite_right : ∀ z, (right ⁻¹' {z}).Finite

/-- The many-valued map of a correspondence: $x \mapsto \{\mathrm{right}(y) : \mathrm{left}(y) = x\}$. -/
def Correspondence.image {X Z : Type*} (C : Correspondence X Z) (x : X) : Set Z :=
  C.right '' (C.left ⁻¹' {x})

/-- Remark 5.31: the graph of a map with finite fibres $\varphi : X \to Z$ is a correspondence whose projection to
$X$ is a bijection, and its many-valued map is $x \mapsto \{\varphi(x)\}$. -/
@[kb "milne2017mf" "Section 5, Remark 5.31, the graph of a map (pdf p. 81)"]
def Correspondence.ofGraph {X Z : Type} (φ : X → Z) (hφ : ∀ z, (φ ⁻¹' {z}).Finite) : Correspondence X Z where
  Y := X
  left := id
  right := φ
  finite_left x := by simp
  finite_right := hφ

theorem Correspondence.ofGraph_image {X Z : Type} (φ : X → Z) (hφ : ∀ z, (φ ⁻¹' {z}).Finite) (x : X) :
    (Correspondence.ofGraph φ hφ).image x = {φ x} := by
  simp [Correspondence.image, Correspondence.ofGraph]

/-- The group $\Gamma_\alpha = \Gamma \cap \alpha^{-1}\Gamma\alpha$ (p. 81). -/
def heckeSubgroup (Γ : Subgroup (GL (Fin 2) ℝ)) (α : GL (Fin 2) ℝ) : Subgroup (GL (Fin 2) ℝ) :=
  Γ ⊓ Γ.map (MulAut.conj α⁻¹).toMonoidHom

/-- If `g : G → Y` is constant on cosets `x * H` of a finite-index subgroup, its range is finite. -/
lemma finite_range_of_index {G Y : Type*} [Group G] (H : Subgroup G) (hH : H.index ≠ 0) (g : G → Y)
    (hg : ∀ x, ∀ k ∈ H, g (x * k) = g x) : (Set.range g).Finite := by
  have : H.FiniteIndex := ⟨hH⟩
  have : Finite (G ⧸ H) := inferInstance
  refine (Set.finite_range (fun q : G ⧸ H => g q.out)).subset ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul H x
  exact ⟨(x : G ⧸ H), by simp only; rw [hk, hg _ _ k.2]⟩

/-- **The Hecke correspondence** (Milne, p. 81 and Remark 5.31):
$\Gamma\backslash\mathbb H \leftarrow \Gamma_\alpha\backslash\mathbb H \to \Gamma\backslash\mathbb H$, the left map
$\Gamma_\alpha x \mapsto \Gamma x$ and the right map $\Gamma_\alpha x \mapsto \Gamma\alpha x$. It is a correspondence
(finite-to-one) when $\Gamma_\alpha$ has finite index in $\Gamma$ and $\alpha\Gamma_\alpha\alpha^{-1}$ has finite index
in $\Gamma$, which holds when $\Gamma\alpha\Gamma$ is a finite union of left and of right cosets (Lemma 5.29). -/
@[kb "milne2017mf" "Section 5, the Hecke correspondence (pdf p. 81)"]
noncomputable def heckeCorrespondence (Γ : Subgroup (GL (Fin 2) ℝ)) (α : GL (Fin 2) ℝ)
    (h₁ : (heckeSubgroup Γ α).relIndex Γ ≠ 0)
    (h₂ : ((heckeSubgroup Γ α).map (MulAut.conj α).toMonoidHom).relIndex Γ ≠ 0) :
    Correspondence (MulAction.orbitRel.Quotient Γ ℍ) (MulAction.orbitRel.Quotient Γ ℍ) where
  Y := MulAction.orbitRel.Quotient (heckeSubgroup Γ α) ℍ
  left := Quotient.map' id (by
    rintro x y ⟨⟨g, hg⟩, rfl⟩
    exact ⟨⟨g, hg.1⟩, rfl⟩)
  right := Quotient.map' (fun x ↦ α • x) (by
    rintro x y ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨h, hh, hgh⟩ := Subgroup.mem_map.1 hg.2
    refine ⟨⟨h, hh⟩, ?_⟩
    show h • (α • y) = α • (g • y)
    rw [← hgh, ← mul_smul, ← mul_smul]
    simp [MulAut.conj_apply, mul_assoc])
  finite_left := by
    intro q
    induction q using Quotient.inductionOn' with
    | h x =>
      have hfin := finite_range_of_index ((heckeSubgroup Γ α).subgroupOf Γ) h₁
        (fun γ : Γ ↦ (Quotient.mk'' ((γ : GL (Fin 2) ℝ)⁻¹ • x) :
          MulAction.orbitRel.Quotient (heckeSubgroup Γ α) ℍ)) (by
          intro γ k hk
          apply Quotient.sound
          refine ⟨⟨(k : GL (Fin 2) ℝ)⁻¹, ?_⟩, ?_⟩
          · exact inv_mem hk
          · show (k : GL (Fin 2) ℝ)⁻¹ • ((γ : GL (Fin 2) ℝ)⁻¹ • x) = ((γ * k : Γ) : GL (Fin 2) ℝ)⁻¹ • x
            rw [← mul_smul]; simp)
      refine hfin.subset ?_
      rintro q (hq : Quotient.map' _ _ q = _)
      induction q using Quotient.inductionOn' with
      | h y =>
        have hq' := Quotient.exact hq
        obtain ⟨⟨γ, hγ⟩, hγy⟩ := hq'
        refine ⟨⟨γ⁻¹, inv_mem hγ⟩, ?_⟩
        apply Quotient.sound
        refine ⟨1, ?_⟩
        show (1 : heckeSubgroup Γ α) • y = _
        rw [one_smul]
        simpa using hγy.symm
  finite_right := by
    intro q
    induction q using Quotient.inductionOn' with
    | h z =>
      have hfin := finite_range_of_index
        (((heckeSubgroup Γ α).map (MulAut.conj α).toMonoidHom).subgroupOf Γ) h₂
        (fun δ : Γ ↦ (Quotient.mk'' (α⁻¹ • ((δ : GL (Fin 2) ℝ)⁻¹ • z)) :
          MulAction.orbitRel.Quotient (heckeSubgroup Γ α) ℍ)) (by
          intro δ k hk
          obtain ⟨h, hh, hhk⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hk)
          apply Quotient.sound
          refine ⟨⟨h⁻¹, inv_mem hh⟩, ?_⟩
          show h⁻¹ • (α⁻¹ • ((δ : GL (Fin 2) ℝ)⁻¹ • z)) = α⁻¹ • (((δ * k : Γ) : GL (Fin 2) ℝ)⁻¹ • z)
          have hk' : (k : GL (Fin 2) ℝ) = α * h * α⁻¹ := by
            rw [← hhk]; simp [MulAut.conj_apply]
          rw [← mul_smul, ← mul_smul, ← mul_smul]
          congr 1
          simp [hk', mul_assoc])
      refine hfin.subset ?_
      rintro q (hq : Quotient.map' _ _ q = _)
      induction q using Quotient.inductionOn' with
      | h y =>
        have hq' := Quotient.exact hq
        obtain ⟨⟨δ, hδ⟩, hδy⟩ := hq'
        refine ⟨⟨δ⁻¹, inv_mem hδ⟩, ?_⟩
        apply Quotient.sound
        refine ⟨1, ?_⟩
        show (1 : heckeSubgroup Γ α) • y = _
        rw [one_smul]
        have : y = α⁻¹ • (δ • z) := by
          rw [show (δ • z : ℍ) = α • y from hδy]; simp
        simpa using this

/-- Milne, p. 81: if $\Gamma = \bigsqcup_i \Gamma_\alpha\beta_i$ and $f$ is invariant under $\Gamma$ (here: under the
slash action of weight $w$), then the trace $\sum_i f|_w(\alpha\beta_i)$ of $f \circ \alpha$ is again invariant under
$\Gamma$. By Lemma 5.30 it equals $\sum_j f|_w\alpha_j$ for $\Gamma\alpha\Gamma = \bigsqcup_j \Gamma\alpha_j$. -/
@[kb "milne2017mf" "Section 5, the trace of f ∘ α is invariant under Gamma (pdf p. 81)"]
theorem trace_slash_invariant (Γ : Subgroup (GL (Fin 2) ℝ)) (α : GL (Fin 2) ℝ) (w : ℤ) {ι : Type*} [Fintype ι]
    (β : ι → GL (Fin 2) ℝ) (hβ : ∀ i, β i ∈ Γ)
    (hdecomp : ∀ γ ∈ Γ, ∃! i, γ * (β i)⁻¹ ∈ heckeSubgroup Γ α) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ Γ, f ∣[w] γ = f) (γ : GL (Fin 2) ℝ) (hγ : γ ∈ Γ) :
    (∑ i, f ∣[w] (α * β i)) ∣[w] γ = ∑ i, f ∣[w] (α * β i) := by
  have hmem : ∀ i, β i * γ ∈ Γ := fun i ↦ Γ.mul_mem (hβ i) hγ
  choose σ hσ huniq using fun i ↦ hdecomp _ (hmem i)
  have hinj : Function.Injective σ := by
    intro i i' h
    have h1 := hσ i
    have h2 := hσ i'
    rw [← h] at h2
    have h3 : β i * (β i')⁻¹ ∈ heckeSubgroup Γ α := by
      have := (heckeSubgroup Γ α).mul_mem h1 ((heckeSubgroup Γ α).inv_mem h2)
      simpa [mul_assoc] using this
    obtain ⟨j, -, hj⟩ := hdecomp (β i) (hβ i)
    have e1 := hj i (by simp)
    have e2 := hj i' (by simpa using h3)
    rw [e2, e1]
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.1 hinj
  rw [SlashAction.sum_slash]
  have key : ∀ i, (f ∣[w] (α * β i)) ∣[w] γ = f ∣[w] (α * β (σ i)) := by
    intro i
    rw [← SlashAction.slash_mul]
    have hh := hσ i
    obtain ⟨g, hg, hgh⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 hh).2
    have e : α * (β i * γ) = g * (α * β (σ i)) := by
      have : (MulAut.conj α⁻¹).toMonoidHom g = β i * γ * (β (σ i))⁻¹ := hgh
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this
      have h2 : α⁻¹ * g * α * β (σ i) = β i * γ := by
        rw [this]; group
      calc α * (β i * γ) = α * (α⁻¹ * g * α * β (σ i)) := by rw [h2]
        _ = g * (α * β (σ i)) := by group
    rw [mul_assoc, e, SlashAction.slash_mul, hf g hg]
  simp_rw [key]
  exact Equiv.sum_comp (Equiv.ofBijective σ hbij) (fun i ↦ f ∣[w] (α * β i))

end ModularFormsKB.Milne
