import ModularFormsKB.Miyake.Wave7.CosetReps
import ModularFormsKB.Miyake.Wave4.MiyakeHecke
import ModularFormsKB.Miyake.Wave5.DoubleCosetRelations
import TauCeti.NumberTheory.ModularForms.Fricke.CharacterSpace
import TauCeti.NumberTheory.ModularForms.Fricke.Involution
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Miyake §4.5: the operators `T*(m, l)`, `T*(n)`; Theorems 4.5.4 (1) and 4.5.5

Miyake, *Modular Forms* (Springer 1989), §4.5, pp. 134–137.

Miyake extends the character `χ` of `Γ₀(N)` to the semigroup
`Δ₀*(N) = {[a b; c d] ∈ M₂(ℤ) : det > 0, c ≡ 0 (N), (d, N) = 1}` by `χ*(α) = χ(d)` (4.5.10), and
lets its Hecke ring `ℛ*(N)` act on `𝒢_k(N, χ)` by (4.5.11), (2.8.2):

  `f | Γ₀(N) α Γ₀(N) = det(α)^{k/2-1} Σ_v conj(χ*(α_v)) f|_k α_v`,  `Γ₀(N) α Γ₀(N) = ⊔_v Γ₀(N) α_v`.

He puts (4.5.15), (4.5.16)

  `T*(m, l) = Γ₀(N) diag(m, l) Γ₀(N)` (`l ∣ m`, `(l, N) = 1`),  `T*(n) = Σ_{l m = n} T*(m, l)`.

Neither Mathlib nor Tau Ceti has `Δ₀*(N)` or these operators. Here:

* `starWeight χ α = conj(χ(d))` and `starSlashSum k χ a f = Σ_i conj(χ(d_i)) f ∣[k] a_i` (Mathlib's
  slash absorbs `det^{k/2-1}`);
* `heckeTStar k χ m l` is `T*(m, l)` on `𝒮_k(N, χ)`: the endomorphism whose value at `f` has
  underlying function `starSlashSum` over **any** complete set of representatives of
  `Γ₀(N) \ Γ₀(N) diag(m, l) Γ₀(N)` (`coe_heckeTStar`; it is `0` unless `l, m ≥ 1`, `(l, N) = 1`,
  as for Tau Ceti's `T(l, m)`);
* `heckeTStarN k χ n = Σ_{l ∣ n, l ∣ n/l} T*(n/l, l)` is Miyake's `T*(n)` in the form (4.5.16)
  (Miyake defines `T*(n)` as the sum of the double cosets of `Δ₀*(N)` of determinant `n` and
  derives (4.5.16) from the `Δ₀*(N)` analogue of Lemma 4.5.2; here (4.5.16) is the definition,
  as wave 4 does for `T(n)` (`Wave4.miyakeHeckeT`)).

Results: Theorem 4.5.5 (`heckeTStar_omega`, `heckeTStarN_omega`: `ω_N` intertwines `T(l, m)` on
`𝒮_k(N, χ)` with `T*(m, l)` on `𝒮_k(N, conj χ)`) and Theorem 4.5.4 (1) (`heckeTStar_eq_smul_heckeTT`,
`heckeTStarN_eq_smul_heckeT`). Miyake's `ω_N = [0 -1; N 0]` is Tau Ceti's `frickeGL`.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup DoubleCoset
  HeckeRing.GL2 HeckeRing.GLn
open scoped MatrixGroups ModularForm Pointwise

noncomputable section

namespace ModularFormsKB.Miyake.Wave7

open ModularFormsKB.Miyake.Wave4

variable {N : ℕ} [NeZero N]

/-- **Miyake's weight on `Δ₀*(N)`** (4.5.10), (2.8.2): a representative `α = [a b; c d]` of a
double coset of `Δ₀*(N)` carries `conj(χ*(α)) = conj(χ(d))`. -/
def starWeight (χ : DirichletCharacter ℂ N) (α : GL (Fin 2) ℚ) : ℂ :=
  starRingEnd ℂ (χ (((α : Matrix (Fin 2) (Fin 2) ℚ) 1 1).num : ZMod N))

/-- **Miyake's action (4.5.11) of a double coset of `Δ₀*(N)`**, over the family of
representatives `a`: `Σ_i conj(χ(d_i)) f ∣[k] a_i`. -/
def starSlashSum (k : ℤ) (χ : DirichletCharacter ℂ N) {ι : Type*} [Fintype ι]
    (a : ι → GL (Fin 2) ℚ) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ i, starWeight χ (a i) • (f ∣[k] a i)

/-- Miyake's `ω_N = [0 -1; N 0]` (p. 115) over `ℚ`. -/
abbrev omegaQ (N : ℕ) [NeZero N] : GL (Fin 2) ℚ := TauCeti.frickeGL ℚ N

/-- Miyake's `ω_N` over `ℝ`, acting on functions on `ℍ` (Tau Ceti's Fricke matrix). -/
abbrev omega (N : ℕ) [NeZero N] : GL (Fin 2) ℝ := TauCeti.frickeGL ℝ N

/-- `ω_N diag(m, l) ω_N⁻¹ = diag(l, m)`. -/
theorem omegaQ_mul_natDiagGL_mul_inv (l m : ℕ) :
    omegaQ N * natDiagGL 2 ![m, l] * (omegaQ N)⁻¹ = natDiagGL 2 ![l, m] := by
  by_cases h : 0 < l ∧ 0 < m
  · have h1 : ∀ i, 0 < (![m, l] : Fin 2 → ℕ) i := by
      intro i; fin_cases i <;> simp [h.1, h.2]
    have h2 : ∀ i, 0 < (![l, m] : Fin 2 → ℕ) i := by
      intro i; fin_cases i <;> simp [h.1, h.2]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      natDiagGL_coe 2 _ h1, natDiagGL_coe 2 _ h2, TauCeti.coe_inv_frickeGL, TauCeti.coe_frickeGL]
    have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.vecMul, dotProduct] <;>
      field_simp
  · have h1 : ¬ ∀ i, 0 < (![m, l] : Fin 2 → ℕ) i := by
      intro H; exact h ⟨by simpa using H 1, by simpa using H 0⟩
    have h2 : ¬ ∀ i, 0 < (![l, m] : Fin 2 → ℕ) i := by
      intro H; exact h ⟨by simpa using H 0, by simpa using H 1⟩
    rw [natDiagGL_of_not_pos 2 h1, natDiagGL_of_not_pos 2 h2]
    group

private theorem conj_mem_gamma0Q (x : GL (Fin 2) ℚ) (hx : x ∈ gamma0Q N) :
    omegaQ N * x * (omegaQ N)⁻¹ ∈ gamma0Q N := by
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hx
  have := TauCeti.mapGL_frickeConjSL ℚ (N := N) ⟨σ, hσ⟩
  refine Subgroup.mem_map.mpr ⟨_, TauCeti.frickeConjSL_mem_Gamma0 ⟨σ, hσ⟩, ?_⟩
  exact this

private theorem conj_inv_mem_gamma0Q (x : GL (Fin 2) ℚ) (hx : x ∈ gamma0Q N) :
    (omegaQ N)⁻¹ * x * omegaQ N ∈ gamma0Q N := by
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hx
  have := TauCeti.mapGL_mul_frickeGL ℚ (N := N) ⟨σ, hσ⟩
  refine Subgroup.mem_map.mpr ⟨_, TauCeti.frickeConjSL_mem_Gamma0 ⟨σ, hσ⟩, ?_⟩
  rw [mul_assoc, eq_inv_mul_iff_mul_eq]
  exact this.symm

omit [NeZero N] in
private theorem isCosetReps_conj_aux (w : GL (Fin 2) ℚ)
    (hw : ∀ x ∈ gamma0Q N, w * x * w⁻¹ ∈ gamma0Q N)
    (hw' : ∀ x ∈ gamma0Q N, w⁻¹ * x * w ∈ gamma0Q N)
    {δ : GL (Fin 2) ℚ} {ι : Type*} {a : ι → GL (Fin 2) ℚ} (ha : IsCosetReps N δ a) :
    IsCosetReps N (w * δ * w⁻¹) fun i ↦ w * a i * w⁻¹ := by
  refine ⟨?_, ?_⟩
  · ext z
    simp only [Set.mem_iUnion, DoubleCoset.mem_doubleCoset, Set.mem_smul_set,
      MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, SetLike.mem_coe]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      have h1 : w⁻¹ * (x * (w * δ * w⁻¹) * y) * w ∈
          doubleCoset δ (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N) :=
        DoubleCoset.mem_doubleCoset.mpr ⟨w⁻¹ * x * w, hw' x hx, w⁻¹ * y * w, hw' y hy, by group⟩
      rw [ha.cover] at h1
      obtain ⟨i, g, hg, hgi⟩ := Set.mem_iUnion.mp h1 |>.imp fun i hi => by
        simpa only [Set.mem_smul_set, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op] using hi
      refine ⟨i, w * g * w⁻¹, hw g hg, ?_⟩
      have : w * (w⁻¹ * (x * (w * δ * w⁻¹) * y) * w) * w⁻¹ = w * (g * a i) * w⁻¹ := by
        rw [hgi]
      simpa [mul_assoc] using this.symm
    · rintro ⟨i, g, hg, rfl⟩
      obtain ⟨x, hx, y, hy, h⟩ := DoubleCoset.mem_doubleCoset.mp (ha.mem_doubleCoset i)
      refine ⟨g * (w * x * w⁻¹), mul_mem hg (hw x hx), w * y * w⁻¹, hw y hy, ?_⟩
      rw [h]; group
  · intro i j hij
    apply ha.injective
    simp only at hij ⊢
    rw [rightCoset_eq_iff] at hij ⊢
    have := hw' _ hij
    convert this using 1
    group

/-- **(4.5.12)**: conjugation by `ω_N` carries complete sets of representatives of
`Γ₀(N) \ Γ₀(N) δ Γ₀(N)` to complete sets of representatives of
`Γ₀(N) \ Γ₀(N) (ω_N δ ω_N⁻¹) Γ₀(N)`. -/
@[kb "miyake1989" "(4.5.12), p. 135"]
theorem IsCosetReps.omega_conj {δ : GL (Fin 2) ℚ} {ι : Type*} {a : ι → GL (Fin 2) ℚ}
    (ha : IsCosetReps N δ a) :
    IsCosetReps N (omegaQ N * δ * (omegaQ N)⁻¹) fun i ↦ omegaQ N * a i * (omegaQ N)⁻¹ :=
  isCosetReps_conj_aux _ conj_mem_gamma0Q conj_inv_mem_gamma0Q ha

private theorem map_omegaQ :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (omegaQ N) = omega N := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [TauCeti.coe_frickeGL]

private theorem slash_omega_mul (k : ℤ) (f : ℍ → ℂ) (b : GL (Fin 2) ℚ) :
    (f ∣[k] omega N) ∣[k] b = (f ∣[k] (omegaQ N * b * (omegaQ N)⁻¹)) ∣[k] omega N := by
  rw [rat_slash k b, rat_slash k (omegaQ N * b * (omegaQ N)⁻¹), ← SlashAction.slash_mul,
    ← SlashAction.slash_mul]
  congr 1
  rw [map_mul, map_mul, map_inv, map_omegaQ]
  group

omit [NeZero N] in
private theorem conj_inv_apply (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    starRingEnd ℂ (χ⁻¹ (u : ZMod N)) = χ (u : ZMod N) := by
  have h1 : ‖χ (u : ZMod N)‖ = 1 := DirichletCharacter.unit_norm_eq_one χ u
  have h2 : χ (u : ZMod N) * starRingEnd ℂ (χ (u : ZMod N)) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
  have h0 : χ (u : ZMod N) ≠ 0 := by
    intro h; rw [h] at h1; simp at h1
  rw [MulChar.inv_apply_eq_inv', map_inv₀]
  have : starRingEnd ℂ (χ (u : ZMod N)) = (χ (u : ZMod N))⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [this, inv_inv]

private theorem starWeight_inv (χ : DirichletCharacter ℂ N) {a b : GL (Fin 2) ℚ}
    (hab : b = (omegaQ N)⁻¹ * a * omegaQ N) (ha : a ∈ Delta0 N) :
    starWeight χ⁻¹ b = (delta0NebentypusChar N χ.toUnitHom ⟨a, ha⟩ : ℂ) := by
  obtain ⟨A, hA, -⟩ := (mem_Delta0_iff N).mp ha
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h11 : ((b : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = ((A 0 0 : ℤ) : ℚ) := by
    rw [hab, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      TauCeti.coe_inv_frickeGL, TauCeti.coe_frickeGL, hA]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have hu := Delta0UpperUnit_apply_val N (g := ⟨a, ha⟩) hA
  rw [starWeight, h11, Rat.num_intCast, delta0NebentypusChar_apply, ← hu]
  simpa using conj_inv_apply χ (Delta0UpperUnit N ⟨a, ha⟩)

omit [NeZero N] in
private theorem out_mem_doubleCoset (l m : ℕ) (hlN : l.Coprime N) :
    ((diagCosetGamma0 N ![l, m] fun _ ↦ hlN).out : GL (Fin 2) ℚ) ∈
      doubleCoset (natDiagGL 2 ![l, m]) (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N) := by
  have := HeckeCoset.rep_mem (diagCosetGamma0 N ![l, m] fun _ ↦ hlN)
  have h2 := diagCosetGamma0_toSet N ![l, m] fun _ ↦ hlN
  exact h2 ▸ this

omit [NeZero N] in
private theorem IsCosetReps.of_out {l m : ℕ} (hlN : l.Coprime N) {ι : Type*}
    {a : ι → GL (Fin 2) ℚ}
    (h : IsCosetReps N ((diagCosetGamma0 N ![l, m] fun _ ↦ hlN).out : GL (Fin 2) ℚ) a) :
    IsCosetReps N (natDiagGL 2 ![l, m]) a :=
  ⟨(doubleCoset_eq_of_mem (out_mem_doubleCoset (N := N) l m hlN)).symm.trans h.cover,
    h.injective⟩

/-- The transfer identity behind Theorem 4.5.5, on functions: for `f` with `f ∣ γ = χ(d_γ) f` on
`Γ₀(N)` and any complete set of representatives `b` of `Γ₀(N) \ Γ₀(N) diag(m, l) Γ₀(N)`,
`Σ_i χ(d_{b_i}) (f ∣ ω_N) ∣ b_i = (f | T(l, m)) ∣ ω_N`. -/
theorem starSlashSum_slash_omega (k : ℤ) (χ : DirichletCharacter ℂ N) {l m : ℕ} (hl : 0 < l)
    (hm : 0 < m) (hlN : l.Coprime N) {ι : Type*} [Fintype ι] {b : ι → GL (Fin 2) ℚ}
    (hb : IsCosetReps N (natDiagGL 2 ![m, l]) b) (f : ℍ → ℂ)
    (hf : f ∈ functionCharSpace k χ.toUnitHom) :
    starSlashSum k χ⁻¹ b (f ∣[k] omega N) =
      twistedHeckeSlashSum k χ.toUnitHom (diagCosetGamma0 N ![l, m] fun _ ↦ hlN) f ∣[k]
        omega N := by
  classical
  have hmem := out_mem_doubleCoset (N := N) l m hlN
  have ha : IsCosetReps N (natDiagGL 2 ![l, m]) fun i ↦ omegaQ N * b i * (omegaQ N)⁻¹ := by
    have := hb.omega_conj
    rwa [omegaQ_mul_natDiagGL_mul_inv] at this
  have hD : IsCosetReps N ((diagCosetGamma0 N ![l, m] fun _ ↦ hlN).out : GL (Fin 2) ℚ)
      fun i ↦ omegaQ N * b i * (omegaQ N)⁻¹ :=
    ⟨by rw [doubleCoset_eq_of_mem hmem]; exact ha.cover, ha.injective⟩
  have hsum := sum_delta0NebentypusChar_smul_slash_eq k χ.toUnitHom _ hD f hf
  rw [← hsum, SlashAction.sum_slash]
  unfold starSlashSum
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ModularForm.smul_slash_of_det_pos k TauCeti.val_det_frickeGL_pos, slash_omega_mul]
  congr 1
  exact starWeight_inv χ (by group) (hD.mem_Delta0 (diagCosetGamma0 N ![l, m] fun _ ↦ hlN).out.2 i)

attribute [local instance] fintypeDecompQuotientGamma0

/-- A chosen complete set of representatives of `Γ₀(N) \ Γ₀(N) diag(m, l) Γ₀(N)`: the
`ω_N`-conjugates `ω_N⁻¹ α_v ω_N` of Tau Ceti's representatives of `Γ₀(N) diag(l, m) Γ₀(N)`. -/
def starReps (l m : ℕ) (hlN : l.Coprime N) :
    DecompQuotient (gamma0Q N) (gamma0Q N)
      ((diagCosetGamma0 N ![l, m] fun _ ↦ hlN).out : GL (Fin 2) ℚ)⁻¹ → GL (Fin 2) ℚ :=
  fun v ↦ (omegaQ N)⁻¹ * rightCosetRep (diagCosetGamma0 N ![l, m] fun _ ↦ hlN) v * omegaQ N

theorem isCosetReps_starReps {l m : ℕ} (hl : 0 < l) (hm : 0 < m) (hlN : l.Coprime N) :
    IsCosetReps N (natDiagGL 2 ![m, l]) (starReps (N := N) l m hlN) := by
  have h1 := isCosetReps_rightCosetRep (N := N) (diagCosetGamma0 N ![l, m] fun _ ↦ hlN)
  have h2 := IsCosetReps.of_out hlN h1
  have h3 := isCosetReps_conj_aux (N := N) (omegaQ N)⁻¹
    (fun x hx ↦ by simpa using conj_inv_mem_gamma0Q x hx)
    (fun x hx ↦ by simpa using conj_mem_gamma0Q x hx) h2
  have e : natDiagGL 2 ![m, l] = (omegaQ N)⁻¹ * natDiagGL 2 ![l, m] * ((omegaQ N)⁻¹)⁻¹ := by
    rw [inv_inv, ← omegaQ_mul_natDiagGL_mul_inv (N := N) l m]; group
  rw [e]
  unfold starReps
  rw [inv_inv] at h3 ⊢
  exact h3

theorem starSlashSum_add (k : ℤ) (χ : DirichletCharacter ℂ N) {ι : Type*} [Fintype ι]
    (a : ι → GL (Fin 2) ℚ) (f g : ℍ → ℂ) :
    starSlashSum k χ a (f + g) = starSlashSum k χ a f + starSlashSum k χ a g := by
  simp only [starSlashSum, SlashAction.add_slash, smul_add, Finset.sum_add_distrib]

theorem starSlashSum_smul (k : ℤ) (χ : DirichletCharacter ℂ N) {ι : Type*} [Fintype ι]
    {a : ι → GL (Fin 2) ℚ} (ha : ∀ i, 0 < ((a i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det)
    (c : ℂ) (f : ℍ → ℂ) :
    starSlashSum k χ a (c • f) = c • starSlashSum k χ a f := by
  simp only [starSlashSum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ModularForm.rat_smul_slash_of_det_pos k (ha i), smul_comm]

/-- Representatives of `Γ₀(N) diag(m, l) Γ₀(N)` have positive determinant. -/
theorem IsCosetReps.det_pos_natDiagGL {l m : ℕ} (hl : 0 < l) (hm : 0 < m) {ι : Type*}
    {a : ι → GL (Fin 2) ℚ} (ha : IsCosetReps N (natDiagGL 2 ![m, l]) a) (i : ι) :
    0 < ((a i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
  obtain ⟨x, hx, y, hy, h⟩ := DoubleCoset.mem_doubleCoset.mp (ha.mem_doubleCoset i)
  have hdet : ∀ z ∈ (gamma0Q N : Set (GL (Fin 2) ℚ)),
      ((z : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
    intro z hz
    obtain ⟨σ, -, rfl⟩ := Subgroup.mem_map.mp hz
    simp only [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
    rw [← RingHom.map_det, σ.det_coe, map_one]
  have hd : 0 < ((natDiagGL 2 ![m, l] : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
    apply natDiagGL_det_pos
    intro j; fin_cases j <;> simp [hl, hm]
  rw [h, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul,
    Matrix.det_mul, hdet x hx, hdet y hy]
  simpa using hd

omit [NeZero N] in
private theorem toUnitHom_inv (χ : DirichletCharacter ℂ N) :
    (χ⁻¹).toUnitHom = (χ.toUnitHom)⁻¹ := by
  ext u
  simp [MulChar.inv_apply_eq_inv']

private theorem frickeCusp_mem (k : ℤ) (χ : DirichletCharacter ℂ N) (f : cuspSpace k χ) :
    TauCeti.frickeOperatorCusp k (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspSpace k χ⁻¹ := by
  have := TauCeti.frickeOperatorCusp_mem_cuspFormCharSpace k χ.toUnitHom f.2
  rw [← toUnitHom_inv] at this
  exact this

private theorem exists_inv_slash (k : ℤ) (χ : DirichletCharacter ℂ N) (f : cuspSpace k χ) :
    ∃ (g : cuspSpace k χ⁻¹) (c : ℂ), c ≠ 0 ∧
      ⇑(g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] omega N =
        c • ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  refine ⟨⟨_, frickeCusp_mem k χ f⟩, TauCeti.frickeScalar N k, TauCeti.frickeScalar_ne_zero k, ?_⟩
  show (⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] omega N) ∣[k] omega N = _
  rw [← SlashAction.slash_mul, TauCeti.frickeGL_sq_slash]

private theorem starSlashSum_eq_of_slash (k : ℤ) (χ : DirichletCharacter ℂ N) {l m : ℕ}
    (hl : 0 < l) (hm : 0 < m) (hlN : l.Coprime N) {ι : Type*} [Fintype ι]
    {b : ι → GL (Fin 2) ℚ} (hb : IsCosetReps N (natDiagGL 2 ![m, l]) b)
    (g : cuspSpace k χ⁻¹) (f : cuspSpace k χ) (c : ℂ) (hc : c ≠ 0)
    (hg : ⇑(g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] omega N =
      c • ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) :
    starSlashSum k χ b ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      c⁻¹ • (⇑((heckeTT k χ⁻¹ l m g : cuspSpace k χ⁻¹) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] omega N) := by
  have h1 := starSlashSum_slash_omega k χ⁻¹ hl hm hlN hb
    ⇑(g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (coe_mem_functionCharSpace g)
  rw [inv_inv, hg, starSlashSum_smul k χ (hb.det_pos_natDiagGL hl hm) c,
    ← coe_heckeTT k χ⁻¹ hl hm hlN g] at h1
  rw [← h1, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- `T*(m, l)` maps `𝒮_k(N, χ)` to itself (Miyake, Theorem 2.8.1 (1) for `Δ₀*(N)`): the slash sum
over `starReps` of a form in `𝒮_k(N, χ)` is again the function of a form in `𝒮_k(N, χ)`. -/
theorem exists_cuspSpace_coe_eq_starSlashSum (k : ℤ) (χ : DirichletCharacter ℂ N) {l m : ℕ}
    (hl : 0 < l) (hm : 0 < m) (hlN : l.Coprime N) (f : cuspSpace k χ) :
    ∃ F : cuspSpace k χ, ⇑(F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      starSlashSum k χ (starReps (N := N) l m hlN) ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  obtain ⟨g, c, hc, hg⟩ := exists_inv_slash k χ f
  have hS := starSlashSum_eq_of_slash k χ hl hm hlN (isCosetReps_starReps hl hm hlN) g f c hc hg
  have hmem := frickeCusp_mem k χ⁻¹ (heckeTT k χ⁻¹ l m g)
  rw [inv_inv] at hmem
  refine ⟨c⁻¹ • ⟨_, hmem⟩, ?_⟩
  rw [hS]
  rfl

/-- The `T*(m, l)` endomorphism in the good case `l, m ≥ 1`, `(l, N) = 1`. -/
def heckeTStarAux (k : ℤ) (χ : DirichletCharacter ℂ N) {l m : ℕ} (hl : 0 < l) (hm : 0 < m)
    (hlN : l.Coprime N) : Module.End ℂ (cuspSpace k χ) where
  toFun f := (exists_cuspSpace_coe_eq_starSlashSum k χ hl hm hlN f).choose
  map_add' f g := by
    have hf := (exists_cuspSpace_coe_eq_starSlashSum k χ hl hm hlN f).choose_spec
    have hg := (exists_cuspSpace_coe_eq_starSlashSum k χ hl hm hlN g).choose_spec
    have hfg := (exists_cuspSpace_coe_eq_starSlashSum k χ hl hm hlN (f + g)).choose_spec
    apply Subtype.ext
    apply DFunLike.coe_injective
    rw [hfg]
    simp only [Submodule.coe_add, FunLike.coe_add, hf, hg, starSlashSum_add]
  map_smul' c f := by
    have hf := (exists_cuspSpace_coe_eq_starSlashSum k χ hl hm hlN f).choose_spec
    have hcf := (exists_cuspSpace_coe_eq_starSlashSum k χ hl hm hlN (c • f)).choose_spec
    apply Subtype.ext
    apply DFunLike.coe_injective
    rw [RingHom.id_apply]
    rw [hcf]
    simp only [Submodule.coe_smul, CuspForm.coe_smul, hf]
    exact starSlashSum_smul k χ ((isCosetReps_starReps hl hm hlN).det_pos_natDiagGL hl hm) c _

/-- **Miyake's `T*(m, l) = Γ₀(N) diag(m, l) Γ₀(N)`** (4.5.15) acting on `𝒮_k(N, χ)` by (4.5.11);
`0` unless `l, m ≥ 1` and `(l, N) = 1` (the same junk convention as Tau Ceti's `T(l, m)`). -/
def heckeTStar (k : ℤ) (χ : DirichletCharacter ℂ N) (m l : ℕ) : Module.End ℂ (cuspSpace k χ) :=
  if h : 0 < l ∧ 0 < m ∧ l.Coprime N then heckeTStarAux k χ h.1 h.2.1 h.2.2 else 0

/-- **Miyake (4.5.11), Theorem 2.8.1 (1) for `Δ₀*(N)`**: `f | T*(m, l)` is
`Σ_i conj(χ(d_i)) f ∣[k] a_i` for **any** complete set of representatives `a` of
`Γ₀(N) \ Γ₀(N) diag(m, l) Γ₀(N)`. -/
@[kb "miyake1989" "(4.5.11), (4.5.15), p. 134-135"]
theorem coe_heckeTStar (k : ℤ) (χ : DirichletCharacter ℂ N) {l m : ℕ} (hl : 0 < l) (hm : 0 < m)
    (hlN : l.Coprime N) {ι : Type*} [Fintype ι] {a : ι → GL (Fin 2) ℚ}
    (ha : IsCosetReps N (natDiagGL 2 ![m, l]) a) (f : cuspSpace k χ) :
    ⇑((heckeTStar k χ m l f : cuspSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      starSlashSum k χ a ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  rw [heckeTStar, dif_pos ⟨hl, hm, hlN⟩]
  obtain ⟨g, c, hc, hg⟩ := exists_inv_slash k χ f
  rw [starSlashSum_eq_of_slash k χ hl hm hlN ha g f c hc hg]
  have := (exists_cuspSpace_coe_eq_starSlashSum k χ hl hm hlN f).choose_spec
  show ⇑((exists_cuspSpace_coe_eq_starSlashSum k χ hl hm hlN f).choose : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = _
  rw [this, starSlashSum_eq_of_slash k χ hl hm hlN (isCosetReps_starReps hl hm hlN) g f c hc hg]

/-- **Miyake's `T*(n)`** in the form (4.5.16): `Σ_{l m = n, l ∣ m, (l, N) = 1} T*(m, l)` (the terms
with `(l, N) ≠ 1` are `0`). -/
def heckeTStarN (k : ℤ) (χ : DirichletCharacter ℂ N) (n : ℕ) : Module.End ℂ (cuspSpace k χ) :=
  ∑ l ∈ n.divisors with l ∣ n / l, heckeTStar k χ (n / l) l

/-- Miyake's `T(n)` on `𝒮_k(N, χ)` (wave 4's `heckeT`, built from Tau Ceti's recurrence) is
`Σ_{l m = n, l ∣ m} T(l, m)` (4.5.16), by wave 5's double-coset relations. -/
theorem heckeT_eq_sum_heckeTT (k : ℤ) (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : n ≠ 0) :
    heckeT k χ n = ∑ l ∈ n.divisors with l ∣ n / l, heckeTT k χ l (n / l) := by
  have := Wave5.miyakeHeckeT_eq_heckeTCompositeGamma0' N hn
  show HeckeRing.GL2.heckeRingHomCuspCharSpace k χ.toUnitHom
    (HeckeRing.GL2.heckeTCompositeGamma0 N n) = _
  rw [← this, miyakeHeckeT, map_sum]

private theorem heckeTT_eq_zero (k : ℤ) (χ : DirichletCharacter ℂ N) {l m : ℕ}
    (h : ¬ (0 < l ∧ 0 < m ∧ l.Coprime N)) : heckeTT k χ l m = 0 := by
  show HeckeRing.GL2.heckeRingHomCuspCharSpace k χ.toUnitHom
    (HeckeRing.GL2.diagElemGamma0 N ![l, m]) = 0
  by_cases hp : ∀ i, 0 < (![l, m] : Fin 2 → ℕ) i
  · have hc : ¬ Nat.Coprime ((![l, m] : Fin 2 → ℕ) 0) N := by
      intro hc; exact h ⟨by simpa using hp 0, by simpa using hp 1, by simpa using hc⟩
    rw [HeckeRing.GL2.diagElemGamma0_of_not_coprime N hc, map_zero]
  · rw [HeckeRing.GL2.diagElemGamma0_of_not_pos N hp, map_zero]

private theorem coe_sum_cuspSpace {k : ℤ} {χ : DirichletCharacter ℂ N} {ι : Type*} (s : Finset ι)
    (x : ι → cuspSpace k χ) :
    ⇑((∑ i ∈ s, x i : cuspSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ∑ i ∈ s, ⇑((x i : cuspSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i t hi IH =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Submodule.coe_add, FunLike.coe_add, IH]

/-- `ω_N` maps `𝒮_k(N, χ)` to `𝒮_k(N, conj χ)` (Lemma 4.3.2 (2), from Tau Ceti). -/
theorem exists_cuspSpace_omega (k : ℤ) (χ : DirichletCharacter ℂ N) (f : cuspSpace k χ) :
    ∃ F : cuspSpace k χ⁻¹, ⇑(F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] omega N :=
  ⟨⟨_, frickeCusp_mem k χ f⟩, rfl⟩

/-- **Miyake, Theorem 4.5.5** for `T(l, m)`: the diagram

  `𝒮_k(N, χ) --T(l, m)--> 𝒮_k(N, χ)`,  `𝒮_k(N, conj χ) --T*(m, l)--> 𝒮_k(N, conj χ)`

with vertical maps `f ↦ f|_k ω_N` commutes: if `F = f ∣ ω_N`, then
`F | T*(m, l) = (f | T(l, m)) ∣ ω_N`. -/
@[kb "miyake1989" "Theorem 4.5.5, p. 137"]
theorem heckeTStar_omega (k : ℤ) (χ : DirichletCharacter ℂ N) (l m : ℕ) (f : cuspSpace k χ)
    (F : cuspSpace k χ⁻¹)
    (hF : ⇑(F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] omega N) :
    ⇑((heckeTStar k χ⁻¹ m l F : cuspSpace k χ⁻¹) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ⇑((heckeTT k χ l m f : cuspSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k]
        omega N := by
  by_cases h : 0 < l ∧ 0 < m ∧ l.Coprime N
  · obtain ⟨hl, hm, hlN⟩ := h
    rw [coe_heckeTStar k χ⁻¹ hl hm hlN (isCosetReps_starReps hl hm hlN) F, hF,
      starSlashSum_slash_omega k χ hl hm hlN (isCosetReps_starReps hl hm hlN) _
        (coe_mem_functionCharSpace f), coe_heckeTT k χ hl hm hlN f]
  · rw [heckeTStar, dif_neg h, heckeTT_eq_zero k χ h]
    simp

/-- **Miyake, Theorem 4.5.5** for `T(n)`: if `F = f ∣ ω_N`, then `F | T*(n) = (f | T(n)) ∣ ω_N`. -/
@[kb "miyake1989" "Theorem 4.5.5, p. 137"]
theorem heckeTStarN_omega (k : ℤ) (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : n ≠ 0)
    (f : cuspSpace k χ) (F : cuspSpace k χ⁻¹)
    (hF : ⇑(F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] omega N) :
    ⇑((heckeTStarN k χ⁻¹ n F : cuspSpace k χ⁻¹) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ⇑((heckeT k χ n f : cuspSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k]
        omega N := by
  rw [heckeT_eq_sum_heckeTT k χ hn, heckeTStarN, LinearMap.sum_apply, LinearMap.sum_apply,
    coe_sum_cuspSpace, coe_sum_cuspSpace, SlashAction.sum_slash]
  exact Finset.sum_congr rfl fun l _ ↦ heckeTStar_omega k χ l (n / l) f F hF

omit [NeZero N] in
private theorem IsCosetReps.det_eq_natDiagGL {l m : ℕ} (hl : 0 < l) (hm : 0 < m) {ι : Type*}
    {a : ι → GL (Fin 2) ℚ} (ha : IsCosetReps N (natDiagGL 2 ![m, l]) a) (i : ι) :
    ((a i : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = m * l := by
  obtain ⟨x, hx, y, hy, h⟩ := DoubleCoset.mem_doubleCoset.mp (ha.mem_doubleCoset i)
  have hdet : ∀ z ∈ (gamma0Q N : Set (GL (Fin 2) ℚ)),
      ((z : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
    intro z hz
    obtain ⟨σ, -, rfl⟩ := Subgroup.mem_map.mp hz
    simp only [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
    rw [← RingHom.map_det, σ.det_coe, map_one]
  have e1 : ∀ i, 0 < (![m, l] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [hl, hm]
  rw [h, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul,
    Matrix.det_mul, hdet x hx, hdet y hy, natDiagGL_det 2 _ e1]
  simp [Fin.prod_univ_two]

omit [NeZero N] in
private theorem mul_conj_unit (χ : DirichletCharacter ℂ N) {x : ZMod N} (hx : IsUnit x) :
    χ x * starRingEnd ℂ (χ x) = 1 := by
  have h1 : ‖χ x‖ = 1 := by
    have := DirichletCharacter.unit_norm_eq_one χ hx.unit
    simpa using this
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp

private theorem starWeight_eq_of_det (χ : DirichletCharacter ℂ N) {l m : ℕ}
    {a : GL (Fin 2) ℚ} (ha : a ∈ Delta0 N)
    (hdet : ((a : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = m * l) :
    starWeight χ a = starRingEnd ℂ (χ ((l : ZMod N) * m)) *
      χ ((((a : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 0 0).num : ZMod N) := by
  obtain ⟨A, hA, -, hN, hu⟩ := (mem_Delta0_iff N).mp ha
  have h00 : ((a : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 0 0 = ((A 0 0 : ℤ) : ℚ) := by
    rw [hA]; rfl
  have h11 : ((a : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = ((A 1 1 : ℤ) : ℚ) := by
    rw [hA]; rfl
  have hd : ((A 0 0 : ℚ) * A 1 1 - A 0 1 * A 1 0) = m * l := by
    rw [← hdet, hA, Matrix.det_fin_two]; simp
  have hdi : A 0 0 * A 1 1 - A 0 1 * A 1 0 = (m : ℤ) * l := by exact_mod_cast hd
  have hz := congrArg (Int.cast : ℤ → ZMod N) hdi
  have hr : ((A 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hN
  push_cast at hz
  rw [hr, mul_zero, sub_zero] at hz
  rw [starWeight, h00, h11, Rat.num_intCast, Rat.num_intCast]
  have hΛ : χ ((l : ZMod N) * m) = χ (A 0 0 : ZMod N) * χ (A 1 1 : ZMod N) := by
    rw [← map_mul, hz, mul_comm]
  have hP := mul_conj_unit χ hu
  rw [hΛ, map_mul]
  linear_combination (-(starRingEnd ℂ (χ (A 1 1 : ZMod N)))) * hP

omit [NeZero N] in
private theorem natDiagGL_swap_mem {l m : ℕ} (hl : 0 < l) (hm : 0 < m)
    (hlm : (l * m).Coprime N) :
    natDiagGL 2 ![m, l] ∈
      doubleCoset (natDiagGL 2 ![l, m]) (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N) := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hlm
  push_cast at huv
  let γ : SL(2, ℤ) := ⟨!![(m : ℤ), -v; (N : ℤ), (l : ℤ) * u], by
    rw [Matrix.det_fin_two_of]; linear_combination huv⟩
  let γ' : SL(2, ℤ) := ⟨!![u * (m : ℤ), v; -(N : ℤ), (l : ℤ)], by
    rw [Matrix.det_fin_two_of]; linear_combination huv⟩
  have h1 : γ ∈ Gamma0 N := by
    rw [Gamma0_mem]; simp [γ]
  have h2 : γ' ∈ Gamma0 N := by
    rw [Gamma0_mem]; simp [γ']
  refine DoubleCoset.mem_doubleCoset.mpr ⟨mapGL ℚ γ, Subgroup.mem_map.mpr ⟨γ, h1, rfl⟩,
    mapGL ℚ γ', Subgroup.mem_map.mpr ⟨γ', h2, rfl⟩, ?_⟩
  have e1 : ∀ i, 0 < (![m, l] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [hl, hm]
  have e2 : ∀ i, 0 < (![l, m] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [hl, hm]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    natDiagGL_coe 2 _ e1, natDiagGL_coe 2 _ e2, coe_mapGL_int_rat_fin_two,
    coe_mapGL_int_rat_fin_two]
  have huv' : (u : ℚ) * (l * m) + v * N = 1 := by exact_mod_cast huv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [γ, γ', Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;>
    first | ring1 | linear_combination (-↑m : ℚ) * huv' | linear_combination (-↑l : ℚ) * huv' | linear_combination (↑m : ℚ) * huv' | linear_combination (↑l : ℚ) * huv'

/-- **Miyake, Theorem 4.5.4 (1)** for `T(l, m)`: if `(l m, N) = 1`, then
`f | T*(m, l) = conj(χ(l m)) (f | T(l, m))` on `𝒮_k(N, χ)`. -/
@[kb "miyake1989" "Theorem 4.5.4 (1), p. 136"]
theorem heckeTStar_eq_smul_heckeTT (k : ℤ) (χ : DirichletCharacter ℂ N) {l m : ℕ}
    (hl : 0 < l) (hm : 0 < m) (hlm : (l * m).Coprime N) :
    heckeTStar k χ m l = starRingEnd ℂ (χ (l * m)) • heckeTT k χ l m := by
  have hlN : l.Coprime N := (Nat.coprime_mul_iff_left.mp hlm).1
  have hb := isCosetReps_starReps (N := N) hl hm hlN
  have hb' : IsCosetReps N (natDiagGL 2 ![l, m]) (starReps (N := N) l m hlN) :=
    ⟨(DoubleCoset.doubleCoset_eq_of_mem (natDiagGL_swap_mem hl hm hlm)).symm.trans hb.cover,
      hb.injective⟩
  have hD := IsCosetReps.of_mem_doubleCoset (out_mem_doubleCoset (N := N) l m hlN) hb'
  refine LinearMap.ext fun f ↦ ?_
  apply Subtype.ext
  apply DFunLike.coe_injective
  rw [coe_heckeTStar k χ hl hm hlN hb f, LinearMap.smul_apply, Submodule.coe_smul,
    FunLike.coe_smul, coe_heckeTT_eq_sum k χ hl hm hlN hb' f, starSlashSum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_smul]
  congr 1
  rw [starWeight_eq_of_det χ (hD.mem_Delta0 (diagCosetGamma0 N ![l, m] fun _ ↦ hlN).out.2 i)
    (hb.det_eq_natDiagGL hl hm i)]

/-- **Miyake, Theorem 4.5.4 (1)** for `T(n)`: if `(n, N) = 1`, then
`f | T*(n) = conj(χ(n)) (f | T(n))` on `𝒮_k(N, χ)`. -/
@[kb "miyake1989" "Theorem 4.5.4 (1), p. 136"]
theorem heckeTStarN_eq_smul_heckeT (k : ℤ) (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : 0 < n)
    (hnN : n.Coprime N) :
    heckeTStarN k χ n = starRingEnd ℂ (χ n) • heckeT k χ n := by
  rw [heckeTStarN, heckeT_eq_sum_heckeTT k χ hn.ne', Finset.smul_sum]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  obtain ⟨hmem, -⟩ := Finset.mem_filter.mp hl
  have hld : l ∣ n := Nat.dvd_of_mem_divisors hmem
  have hlpos : 0 < l := Nat.pos_of_dvd_of_pos hld hn
  have hmul : l * (n / l) = n := Nat.mul_div_cancel' hld
  have hm : 0 < n / l := Nat.div_pos (Nat.le_of_dvd hn hld) hlpos
  rw [heckeTStar_eq_smul_heckeTT k χ hlpos hm (by rwa [hmul])]
  have e : ((l : ZMod N) * ((n / l : ℕ) : ZMod N)) = (n : ZMod N) := by
    rw [← Nat.cast_mul, hmul]
  simp only [e]

end ModularFormsKB.Miyake.Wave7
