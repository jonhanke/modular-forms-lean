import ModularFormsKB.Miyake.Wave3.HeckeLemma
import TauCeti.NumberTheory.ModularForms.Degeneracy
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.ElementaryDivisors
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.UpperTriCosets
import ModularFormsKB.Citation
/-!
# Miyake, Lemma 4.6.3 (Hecke's lemma): proof

Miyake, *Modular Forms* (Springer 1989), §4.6, p. 155, Lemma 4.6.3. The theorem `heckeLemma`
proves the wave 3 statement `ModularFormsKB.Miyake.HeckeLemmaStatement`.

Let `f` be a modular form of positive weight `k` for `Γ₁(N)` in the character space for `χ`, and
let `α` be an integer matrix with primitive entries, lower left entry divisible by `N`, upper left
entry prime to `N`, and determinant `l > 1` prime to `N`. Suppose the slash of `f` by `α` is again in
the character space. The proof shows that `f = 0`, in the following steps (Mathlib's slash operator,
which differs from Miyake's by a nonzero constant, is used throughout).

1. Every element of the character space is sent to a nonzero scalar multiple of itself by the
   slash of any element of `Γ₀(N)` (`exists_slash_gamma0`), and is fixed by the slash of any element
   of `Γ₁(N)` (`slash_gamma1`).
2. By Tau Ceti's theorem on elementary divisors in `Γ₀(N)`
   (`HeckeRing.GL2.mem_doubleCoset_natDiagGL_of_primitive`), `α = γ₁ · diag(1, l) · γ₂` with
   `γ₁, γ₂ ∈ Γ₀(N)`, transported from the rationals to the reals (`exists_gamma0_factor`).
3. Combining 1 and 2, the slash of `f` by `diag(1, l)` is a scalar multiple of an element of the
   character space, hence invariant under `z ↦ z + 1`. Since `diag(1, l)` conjugates the translation
   by `1/l` to the translation by `1`, `f` is invariant under `z ↦ z + 1/l`
   (`slash_tGL_eq_self`).
4. Choose integers `x, u` with `l x + N u = 1`. As integer matrices,
   `[l 1; 0 l] = [1 0; l N u 1] · [1 0; 0 l²] · [l 1; -N u x]`, where the first factor lies in
   `Γ₁(N)` and the last in `Γ₀(N)` (`mGL_eq`). The slash by `[l 1; 0 l]` is a multiple of the
   translation by `1/l` (`slash_mGL`), hence of `f` itself. Using 1, it follows that the slash of
   `f` by `diag(1, l²)` is a scalar multiple of `f` (`slash_dGL_sq`), that is, `f(z)` is a constant
   times `f(l² z)` for all `z` (`eq_const_mul_levelRaise`).
5. Comparing `q`-expansion coefficients with Tau Ceti's level raising operator, the coefficient
   `a(n)` is a constant times `a(n / l²)` if `l² ∣ n` and zero otherwise. By strong induction,
   `a(n) = 0` for all `n ≥ 1`, so `f` is constant. A constant modular form of nonzero weight is
   zero (`eq_zero_of_eq_const_mul_levelRaise`).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace ModularFormsKB.Miyake.Sec4_6

/-- The real matrix `[a b; c d]` as an element of `GL₂(ℝ)`. -/
noncomputable def glOf (a b c d : ℝ) (h : a * d - b * c ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by simpa [Matrix.det_fin_two] using h)

@[simp] lemma coe_glOf (a b c d : ℝ) (h : a * d - b * c ≠ 0) :
    ((glOf a b c d h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d] := by
  simp [glOf]

lemma det_glOf (a b c d : ℝ) (h : a * d - b * c ≠ 0) :
    (glOf a b c d h).det.val = a * d - b * c := by
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

lemma slash_apply_pos (k : ℤ) (F : ℍ → ℂ) (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) (z : ℍ) :
    (F ∣[k] g) z = F (g • z) * ((g.det.val : ℝ) : ℂ) ^ (k - 1) * denom g z ^ (-k) := by
  simp only [ModularForm.slash_apply, σ, hg, ite_true, abs_of_pos hg]
  rfl

/-- The integer matrix `[a b; c d]` of determinant one. -/
def slOf (a b c d : ℤ) (h : a * d - b * c = 1) : SL(2, ℤ) :=
  ⟨!![a, b; c, d], by simpa [Matrix.det_fin_two] using h⟩

lemma coe_mapGL_slOf (a b c d : ℤ) (h : a * d - b * c = 1) :
    ((mapGL ℝ (slOf a b c d h) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(a : ℝ), b; c, d] := by
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `diag(1, m)` over the reals. -/
noncomputable def dGL (m : ℕ) (hm : m ≠ 0) : GL (Fin 2) ℝ :=
  glOf 1 0 0 m (by simpa using hm)

/-- `[1 1/m; 0 1]` over the reals. -/
noncomputable def tGL (m : ℕ) : GL (Fin 2) ℝ :=
  glOf 1 (1 / m) 0 1 (by simp)

/-- `[m 1; 0 m]` over the reals. -/
noncomputable def mGL (m : ℕ) (hm : m ≠ 0) : GL (Fin 2) ℝ :=
  glOf m 1 0 m (by simpa using hm)

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

lemma exists_slash_gamma0 {F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hF : F ∈ TauCeti.modFormCharSpace k χ) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ∃ c : ℂ, c ≠ 0 ∧ ⇑F ∣[k] mapGL ℝ γ = c • ⇑F :=
  ⟨_, Units.ne_zero _, (TauCeti.mem_modFormCharSpace_iff_nebentypus k χ F).mp hF ⟨γ, hγ⟩⟩

lemma slash_gamma1 (F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma1 N) : ⇑F ∣[k] mapGL ℝ γ = ⇑F :=
  SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ hγ)

lemma det_mapGL_pos (γ : SL(2, ℤ)) : 0 < (mapGL ℝ γ).det.val := by
  simp

lemma dGL_pos (m : ℕ) (hm : m ≠ 0) : 0 < (dGL m hm).det.val := by
  have : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  rw [dGL, det_glOf]; simpa using this

lemma tGL_pos (m : ℕ) : 0 < (tGL m).det.val := by
  rw [tGL, det_glOf]; simp

lemma mGL_pos (m : ℕ) (hm : m ≠ 0) : 0 < (mGL m hm).det.val := by
  have : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  rw [mGL, det_glOf]; simpa using mul_pos this this

lemma tGL_mul_dGL (m : ℕ) (hm : m ≠ 0) :
    tGL m * dGL m hm = dGL m hm * mapGL ℝ (slOf 1 1 0 1 (by norm_num)) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_mapGL_slOf]
  simp only [tGL, dGL, coe_glOf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; field_simp

lemma mGL_eq (l : ℕ) (hl : l ≠ 0) (x u : ℤ) (h : (l : ℤ) * x + N * u = 1) :
    mGL l hl = mapGL ℝ (slOf 1 0 (l * N * u) 1 (by simp)) *
      dGL (l ^ 2) (pow_ne_zero 2 hl) * mapGL ℝ (slOf l 1 (-(N * u)) x (by linarith)) := by
  have hR : (l : ℝ) * x + N * u = 1 := by exact_mod_cast h
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_mapGL_slOf, coe_mapGL_slOf]
  simp only [mGL, dGL, coe_glOf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | ring1 | linear_combination (-(l : ℝ)) * hR

lemma slash_mGL (m : ℕ) (hm : m ≠ 0) (f : ℍ → ℂ) :
    f ∣[k] mGL m hm = ((m : ℂ) ^ (k - 2)) • (f ∣[k] tGL m) := by
  funext z
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hm'' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hs : mGL m hm • z = tGL m • z := by
    ext
    rw [coe_smul_of_det_pos (mGL_pos m hm), coe_smul_of_det_pos (tGL_pos m)]
    simp [num, denom, mGL, tGL]
    field_simp
  rw [Pi.smul_apply, slash_apply_pos _ _ _ (mGL_pos m hm), slash_apply_pos _ _ _ (tGL_pos m), hs]
  simp only [det_glOf, denom, mGL, tGL, coe_glOf]
  simp
  have hk : (m : ℂ) ^ k ≠ 0 := zpow_ne_zero _ hm'
  have key : ((m : ℂ) * m) ^ (k - 1) * ((m : ℂ) ^ k)⁻¹ = (m : ℂ) ^ (k - 2) := by
    rw [mul_zpow, zpow_sub₀ hm', zpow_sub₀ hm']
    field_simp
  rw [mul_assoc, key, mul_comm]


lemma slOf_T_mem : slOf 1 1 0 1 (by norm_num) ∈ Gamma1 N := by
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [slOf]

lemma slash_slash_inv (f : ℍ → ℂ) (g : GL (Fin 2) ℝ) : (f ∣[k] g) ∣[k] g⁻¹ = f := by
  rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

/-- Periodicity: if the slash of `f` by `α` lies in the character space and `α` lies in the double
coset of `diag(1, l)`, then `f` is invariant under `z ↦ z + 1/l`. -/
lemma slash_tGL_eq_self {f F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ TauCeti.modFormCharSpace k χ) (hF : F ∈ TauCeti.modFormCharSpace k χ)
    (l : ℕ) (hl : l ≠ 0) {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 N) (h₂ : γ₂ ∈ Gamma0 N)
    (hFf : ⇑F = ⇑f ∣[k] (mapGL ℝ γ₁ * dGL l hl * mapGL ℝ γ₂)) :
    ⇑f ∣[k] tGL l = ⇑f := by
  obtain ⟨c₁, hc₁, e₁⟩ := exists_slash_gamma0 hf h₁
  obtain ⟨c₂, hc₂, e₂⟩ := exists_slash_gamma0 hF (inv_mem h₂)
  have e3 : ⇑F = c₁ • ((⇑f ∣[k] dGL l hl) ∣[k] mapGL ℝ γ₂) := by
    rw [hFf, SlashAction.slash_mul, SlashAction.slash_mul, e₁,
      ModularForm.smul_slash_of_det_pos k (dGL_pos l hl),
      ModularForm.smul_slash_of_det_pos k (det_mapGL_pos γ₂)]
  have e5 : (⇑f ∣[k] dGL l hl) ∣[k] mapGL ℝ γ₂ = c₁⁻¹ • ⇑F := by
    rw [e3, smul_smul, inv_mul_cancel₀ hc₁, one_smul]
  have e4 : ⇑f ∣[k] dGL l hl = c₁⁻¹ • c₂ • ⇑F := by
    have : (⇑f ∣[k] dGL l hl) = ((⇑f ∣[k] dGL l hl) ∣[k] mapGL ℝ γ₂) ∣[k] mapGL ℝ γ₂⁻¹ := by
      rw [← SlashAction.slash_mul, ← map_mul, mul_inv_cancel, map_one, SlashAction.slash_one]
    rw [this, e5, ModularForm.smul_slash_of_det_pos k (det_mapGL_pos _), e₂]
  have hT : (⇑f ∣[k] dGL l hl) ∣[k] mapGL ℝ (slOf 1 1 0 1 (by norm_num)) = ⇑f ∣[k] dGL l hl := by
    rw [e4, ModularForm.smul_slash_of_det_pos k (det_mapGL_pos _),
      ModularForm.smul_slash_of_det_pos k (det_mapGL_pos _), slash_gamma1 F slOf_T_mem]
  have h5 : (⇑f ∣[k] tGL l) ∣[k] dGL l hl = ⇑f ∣[k] dGL l hl := by
    rw [← SlashAction.slash_mul, tGL_mul_dGL, SlashAction.slash_mul, hT]
  calc ⇑f ∣[k] tGL l = ((⇑f ∣[k] tGL l) ∣[k] dGL l hl) ∣[k] (dGL l hl)⁻¹ :=
        (slash_slash_inv _ _).symm
    _ = (⇑f ∣[k] dGL l hl) ∣[k] (dGL l hl)⁻¹ := by rw [h5]
    _ = ⇑f := slash_slash_inv _ _


lemma slOf_A_mem (l : ℕ) (u : ℤ) :
    slOf 1 0 (l * N * u) 1 (by simp) ∈ Gamma1 N := by
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [slOf]

lemma slOf_B_mem (l : ℕ) (x u : ℤ) (h : (l : ℤ) * x - 1 * (-(N * u)) = 1) :
    slOf l 1 (-(N * u)) x h ∈ Gamma0 N := by
  rw [Gamma0_mem]
  simp [slOf]

/-- If `f` is invariant under `z ↦ z + 1/l` and `l` is prime to `N`, then `f ∣ diag(1, l²)` is a
scalar multiple of `f`. -/
lemma slash_dGL_sq {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ TauCeti.modFormCharSpace k χ) (l : ℕ) (hl : l ≠ 0) (x u : ℤ)
    (h : (l : ℤ) * x + N * u = 1) (hper : ⇑f ∣[k] tGL l = ⇑f) :
    ∃ c : ℂ, ⇑f ∣[k] dGL (l ^ 2) (pow_ne_zero 2 hl) = c • ⇑f := by
  have hB : (l : ℤ) * x - 1 * (-(N * u)) = 1 := by linarith
  have hm : ⇑f ∣[k] mGL l hl = ((l : ℂ) ^ (k - 2)) • ⇑f := by rw [slash_mGL, hper]
  rw [mGL_eq l hl x u h, SlashAction.slash_mul, SlashAction.slash_mul,
    slash_gamma1 f (slOf_A_mem l u)] at hm
  obtain ⟨c, hc, e⟩ := exists_slash_gamma0 hf (inv_mem (slOf_B_mem (N := N) l x u hB))
  refine ⟨(l : ℂ) ^ (k - 2) * c, ?_⟩
  calc ⇑f ∣[k] dGL (l ^ 2) (pow_ne_zero 2 hl)
      = ((⇑f ∣[k] dGL (l ^ 2) (pow_ne_zero 2 hl)) ∣[k] mapGL ℝ (slOf l 1 (-(N * u)) x hB)) ∣[k]
          mapGL ℝ (slOf l 1 (-(N * u)) x hB)⁻¹ := by
        rw [← SlashAction.slash_mul, ← map_mul, mul_inv_cancel, map_one, SlashAction.slash_one]
    _ = _ := by
        rw [hm, ModularForm.smul_slash_of_det_pos k (det_mapGL_pos _), e, smul_smul]

lemma dGL_smul_scaleGL (m : ℕ) [NeZero m] (z : ℍ) :
    dGL m (NeZero.ne m) • (TauCeti.scaleGL m • z) = z := by
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hS : 0 < (TauCeti.scaleGL m).det.val := by
    have : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
    simpa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] using this
  ext
  rw [coe_smul_of_det_pos (dGL_pos _ _), coe_smul_of_det_pos hS]
  simp [num, denom, dGL]
  field_simp

lemma eq_const_mul_levelRaise {f : ℍ → ℂ} (m : ℕ) [NeZero m] (c : ℂ)
    (h : f ∣[k] dGL m (NeZero.ne m) = c • f) (w : ℍ) :
    f w = ((m : ℂ) * c) * f (TauCeti.scaleGL m • w) := by
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have := congrFun h (TauCeti.scaleGL m • w)
  rw [slash_apply_pos _ _ _ (dGL_pos _ _), dGL_smul_scaleGL] at this
  simp only [dGL, det_glOf, denom, coe_glOf, Pi.smul_apply, smul_eq_mul] at this
  simp at this
  have hk : (m : ℂ) ^ k ≠ 0 := zpow_ne_zero _ hm'
  have key : (m : ℂ) ^ (k - 1) * ((m : ℂ) ^ k)⁻¹ = (m : ℂ)⁻¹ := by
    rw [zpow_sub₀ hm']; field_simp
  rw [mul_assoc, key] at this
  calc f w = m * (f w * (m : ℂ)⁻¹) := by field_simp
    _ = _ := by rw [this]; ring


open HeckeRing.GL2 in
lemma exists_gamma0_factor (α : Matrix (Fin 2) (Fin 2) ℤ) (hN : (N : ℤ) ∣ α 1 0)
    (hco : IsCoprime (α 0 0) (N : ℤ)) (l : ℕ) (hl : l ≠ 0) (hdet : α.det = l)
    (hprim : ∀ m : ℤ, (∀ i j, m ∣ α i j) → IsUnit m) (g : GL (Fin 2) ℝ)
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = α.map Int.cast) :
    ∃ γ₁ ∈ Gamma0 N, ∃ γ₂ ∈ Gamma0 N, g = mapGL ℝ γ₁ * dGL l hl * mapGL ℝ γ₂ := by
  have hdetQ : (α.map (Int.cast : ℤ → ℚ)).det = (l : ℚ) := by
    have h1 : ((α.det : ℤ) : ℚ) = (α.map (Int.cast : ℤ → ℚ)).det := by
      simp [Matrix.det_fin_two]
    rw [← h1, hdet]; simp
  have hne : (α.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [hdetQ]; exact_mod_cast hl
  have hmem := mem_doubleCoset_natDiagGL_of_primitive N l
    (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hne) α
    (Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _) hN (Int.isCoprime_iff_gcd_eq_one.mp hco)
    (by rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]; exact hdetQ)
    (by
      intro p hp ⟨a, b, c, d⟩
      have hu := hprim p (by
        intro i j
        fin_cases i <;> fin_cases j <;> assumption)
      exact hp.ne_one (by simpa using Int.isUnit_iff_natAbs_eq.mp hu))
  obtain ⟨a, ha, b, hb, hx⟩ := DoubleCoset.mem_doubleCoset.mp hmem
  obtain ⟨γ₁, h1, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨γ₂, h2, rfl⟩ := Subgroup.mem_map.mp hb
  refine ⟨γ₁, h1, γ₂, h2, ?_⟩
  have hQ := congrArg (fun y : GL (Fin 2) ℚ => (y : Matrix (Fin 2) (Fin 2) ℚ)) hx
  simp only [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Units.val_mul,
    coe_natDiagGL_one (Nat.pos_of_ne_zero hl), coe_mapGL_int_rat_fin_two] at hQ
  refine Units.ext ?_
  rw [hg, Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix, dGL, coe_glOf]
  ext i j
  have hij := congrFun (congrFun hQ i) j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] at hij ⊢ <;> exact_mod_cast hij


/-- A modular form of positive weight with `f(z) = C f(L z)` for some `L > 1` vanishes. -/
lemma eq_zero_of_eq_const_mul_levelRaise (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hk : 0 < k) (L : ℕ) [NeZero L] (hL : 1 < L) (C : ℂ)
    (h : ∀ w, f w = C * f (TauCeti.scaleGL L • w)) : f = 0 := by
  let G := TauCeti.ModularForm.levelRaise L (TauCeti.Gamma1_map_le_conjAct_scaleGL N L) f
  have hfG : ⇑f = C • ⇑G := by
    funext w
    simp only [Pi.smul_apply, smul_eq_mul, G, TauCeti.ModularForm.levelRaise_apply]
    exact h w
  have hq : qExpansion 1 ⇑f = C • qExpansion 1 ⇑G := by
    rw [hfG]
    exact ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _) C G
  have hcoeff : ∀ n, (qExpansion 1 ⇑f).coeff n =
      C * (if L ∣ n then (qExpansion 1 ⇑f).coeff (n / L) else 0) := by
    intro n
    have e := TauCeti.ModularForm.qExpansion_levelRaise_coeff_Gamma1 (d := L) N f n
    calc (qExpansion 1 ⇑f).coeff n = C * (qExpansion 1 ⇑G).coeff n := by
          rw [hq, PowerSeries.coeff_smul, smul_eq_mul]
      _ = _ := by rw [e]
  have hzero : ∀ n, 1 ≤ n → (qExpansion 1 ⇑f).coeff n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rw [hcoeff]
      split_ifs with hd
      · obtain ⟨m, rfl⟩ := hd
        have hm : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with h0 | h0
          · subst h0; simp at hn
          · exact h0
        have hlt : m < L * m := by nlinarith
        rw [Nat.mul_div_cancel_left m (NeZero.pos L), ih m hlt hm, mul_zero]
      · simp
  have : Fact (IsCusp OnePoint.infty ((Gamma1 N).map (mapGL ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N)⟩
  have hconst : ∀ τ : ℍ, f τ = (qExpansion 1 ⇑f).coeff 0 := by
    intro τ
    have hs := ModularForm.hasSum_qExpansion (f := f) one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map N) τ
    have h2 : HasSum (fun m : ℕ => (qExpansion 1 ⇑f).coeff m * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
        ((qExpansion 1 ⇑f).coeff 0) := by
      have := hasSum_single (f := fun m : ℕ => (qExpansion 1 ⇑f).coeff m *
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) 0 (fun m hm => by
          rw [hzero m (Nat.one_le_iff_ne_zero.mpr hm), zero_mul])
      simpa using this
    exact hs.unique h2
  have h0 := TauCeti.ModularForm.eq_zero_of_eq_const (f := f) (c := (qExpansion 1 ⇑f).coeff 0)
    (funext hconst) hk.ne'
  ext τ
  rw [hconst, h0]
  rfl


/-- **Miyake, Lemma 4.6.3 (Hecke's lemma).** This proves the wave 3 statement
`ModularFormsKB.Miyake.HeckeLemmaStatement`. -/
@[kb "miyake1989" "Lemma 4.6.3, p. 155"]
theorem heckeLemma (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    HeckeLemmaStatement N k χ := by
  intro hk f hf α hN hco hdet1 hdetco hprim g hg ⟨F, hF, hFg⟩
  obtain ⟨l, hl⟩ : ∃ l : ℕ, α.det = l := ⟨α.det.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hl1 : 1 < l := by
    rw [hl] at hdet1
    exact_mod_cast hdet1
  have hl0 : l ≠ 0 := by omega
  obtain ⟨γ₁, h₁, γ₂, h₂, hgeq⟩ := exists_gamma0_factor α hN hco l hl0 hl hprim g hg
  have hper := slash_tGL_eq_self hf hF l hl0 h₁ h₂ (by rw [hFg, hgeq])
  have hcop : IsCoprime (l : ℤ) (N : ℤ) := hl ▸ hdetco
  obtain ⟨x, u, hxu⟩ := hcop
  have h : (l : ℤ) * x + N * u = 1 := by linarith
  obtain ⟨c, hc⟩ := slash_dGL_sq hf l hl0 x u h hper
  have : NeZero (l ^ 2) := ⟨pow_ne_zero 2 hl0⟩
  refine eq_zero_of_eq_const_mul_levelRaise f hk (l ^ 2) (by nlinarith) (((l ^ 2 : ℕ) : ℂ) * c) ?_
  intro w
  exact eq_const_mul_levelRaise (l ^ 2) c hc w


end ModularFormsKB.Miyake.Sec4_6
