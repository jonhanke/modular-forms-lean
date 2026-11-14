import ModularFormsKB.Miyake.Wave7.CosetReps
import ModularFormsKB.Miyake.Wave5.HeckeGeneration
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.CoprimeMul

/-!
# Miyake §4.5: `Γ₀(N) α Γ₀(N) = Γ₀(N) α Γ₁(N)` and common coset representatives

Miyake, *Modular Forms* (Springer 1989), §4.5, pp. 151–152 (proof of Theorem 4.5.18).

Miyake proves (4.5.42), `Γ₀(N) α Γ₀(N) = Γ₀(N) α Γ₁(N)`, for `α ∈ Δ₁(N)`, first for
`α = diag(l, m)` and then for all `α` by Lemma 4.5.2. The argument uses only `α ∈ Δ₀(N)`, and so
does the statement here (`doubleCoset_gamma0_eq_gamma0_gamma1`). From it:

* every complete set of representatives of `Γ₁(N) \ Γ₁(N) α Γ₁(N)` is a complete set of
  representatives of `Γ₀(N) \ Γ₀(N) α Γ₀(N)` (`isCosetReps_of_gamma1`): Miyake's application of
  Theorem 2.7.6 with `(Γ, Δ, U, D) = (Γ₁(N), Δ₁(N), Γ₀(N), Δ₀(N))`;
* every element of `Γ₁(N) α Γ₁(N)` has the upper-left and lower-right entries of `α` modulo `N`
  (`mem_doubleCoset_gamma1_entries`), which is what makes Miyake's character weights constant on
  such representatives.

Here `Δ₀(N)` is Tau Ceti's `HeckeRing.GL2.Delta0` (upper-left entry a unit modulo `N`), which is
Miyake's `Δ₀(N)` of p. 132.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup DoubleCoset
  HeckeRing.GL2 HeckeRing.GLn
open scoped MatrixGroups ModularForm Pointwise

noncomputable section

namespace ModularFormsKB.Miyake.Wave8

open ModularFormsKB.Miyake.Wave4 ModularFormsKB.Miyake.Wave7

variable {N : ℕ}

/-- `Γ₁(N)` as a subgroup of `GL₂(ℚ)`. -/
abbrev gamma1Q (N : ℕ) : Subgroup (GL (Fin 2) ℚ) := (Gamma1 N).map (mapGL ℚ)

/-- Double cosets grow with the two subgroups. -/
theorem doubleCoset_mono {g : GL (Fin 2) ℚ} {H H' K K' : Subgroup (GL (Fin 2) ℚ)} (hH : H ≤ H')
    (hK : K ≤ K') :
    doubleCoset g (H : Set (GL (Fin 2) ℚ)) K ⊆ doubleCoset g (H' : Set (GL (Fin 2) ℚ)) K' := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hx
  exact mem_doubleCoset.mpr ⟨a, hH ha, b, hK hb, rfl⟩

theorem gamma1Q_le_gamma0Q : gamma1Q N ≤ gamma0Q N :=
  Subgroup.map_mono (Gamma1_in_Gamma0 N)

/-- An element of `Γ₁(N) α Γ₁(N)` (`α` integral with `N ∣ c_α`) is integral, with lower-left entry
`≡ 0`, upper-left entry `≡ a_α` and lower-right entry `≡ d_α` modulo `N`. -/
theorem mem_doubleCoset_gamma1_entries {α x : GL (Fin 2) ℚ} {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : (α : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ)) (hA10 : (N : ℤ) ∣ A 1 0)
    (hx : x ∈ doubleCoset α (gamma1Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N)) :
    ∃ X : Matrix (Fin 2) (Fin 2) ℤ, (x : Matrix (Fin 2) (Fin 2) ℚ) = X.map (Int.cast : ℤ → ℚ) ∧
      ((X 1 0 : ℤ) : ZMod N) = 0 ∧ ((X 0 0 : ℤ) : ZMod N) = A 0 0 ∧
        ((X 1 1 : ℤ) : ZMod N) = A 1 1 := by
  obtain ⟨_, ⟨g₁, hg₁, rfl⟩, _, ⟨g₂, hg₂, rfl⟩, rfl⟩ := mem_doubleCoset.mp hx
  obtain ⟨h₁00, h₁11, h₁10⟩ := (Gamma1_mem N g₁).mp hg₁
  obtain ⟨h₂00, h₂11, h₂10⟩ := (Gamma1_mem N g₂).mp hg₂
  have hA' : ((A 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hA10
  refine ⟨_, mapGL_mul_coe_eq_intMatrix 2 g₁ g₂ _ _ hA, ?_, ?_, ?_⟩ <;>
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    simp [h₁00, h₁11, h₁10, h₂00, h₂11, h₂10, hA']

/-- **Miyake (4.5.42) for `diag(l, m)`**: `Γ₀(N) diag(l, m) Γ₀(N) ⊆ Γ₀(N) diag(l, m) Γ₁(N)` for
`l, m ≥ 1`, `l ∣ m`. -/
theorem doubleCoset_natDiagGL_gamma0_subset {l m : ℕ} [NeZero N] (hl : 0 < l) (hlm : l ∣ m)
    (hm : 0 < m) :
    doubleCoset (natDiagGL 2 ![l, m]) (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N) ⊆
      doubleCoset (natDiagGL 2 ![l, m]) (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N) := by
  intro x hx
  obtain ⟨_, ⟨g₁, hg₁, rfl⟩, _, ⟨g₂, hg₂, rfl⟩, rfl⟩ := mem_doubleCoset.mp hx
  obtain ⟨n, rfl⟩ := hlm
  have hn : 0 < n := Nat.pos_of_mul_pos_left hm
  have : NeZero n := ⟨hn.ne'⟩
  have h₁ := intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hg₂
  let u : (ZMod N)ˣ := ⟨g₂ 1 1, g₂ 0 0, by rw [mul_comm]; exact h₁, h₁⟩
  obtain ⟨t, htc, htu⟩ := ZMod.exists_isCoprime_mul_intCast_eq n u
  have ht : ((t : ℤ) : ZMod N) = ((g₂ 1 1 : ℤ) : ZMod N) := htu
  obtain ⟨A, A', hA10, hA11, hA'10, hA'11, hcomm⟩ :=
    exists_natDiagGL_mul_mapGL_eq_of_isCoprime hn htc
  -- `diag(l, l n) = l • diag(1, n)` commutes past `A` in the same way
  have hD : ((natDiagGL 2 ![l, l * n] : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (l : ℚ) • ((natDiagGL 2 ![1, n] : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) := by
    rw [natDiagGL_coe 2 ![l, l * n] (fun i ↦ by fin_cases i <;> simp [hl, hm]),
      coe_natDiagGL_one hn]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hcomm' : natDiagGL 2 ![l, l * n] * mapGL ℚ A = mapGL ℚ A' * natDiagGL 2 ![l, l * n] := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hD, Matrix.smul_mul, Matrix.mul_smul, ← Units.val_mul,
      ← Units.val_mul, hcomm]
  have hA' : A' ∈ Gamma0 N := mem_Gamma0_iff_dvd.mpr (by rw [hA'10]; exact dvd_mul_left _ _)
  have hdetA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one A
  refine mem_doubleCoset.mpr ⟨mapGL ℚ (g₁ * A'), Subgroup.mem_map_of_mem _ (mul_mem hg₁ hA'),
    mapGL ℚ (A⁻¹ * g₂), Subgroup.mem_map_of_mem _ ?_, ?_⟩
  · -- `A⁻¹ g₂ = (g₂⁻¹ (A⁻¹)⁻¹)⁻¹`, and `g₂⁻¹`, `A⁻¹` have the same lower row modulo `N`
    have : A⁻¹ * g₂ = (g₂⁻¹ * (A⁻¹)⁻¹)⁻¹ := by group
    rw [this]
    refine inv_mem (mul_inv_mem_Gamma1_iff_dvd_sub.mpr ?_)
    rw [SL2_inv_expl, SL2_inv_expl]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
    refine ⟨?_, ?_⟩
    · rw [hA10]
      have := mem_Gamma0_iff_dvd.mp hg₂
      have h2 : (N : ℤ) ∣ -g₂ 1 0 - -(N : ℤ) := by
        rw [show -g₂ 1 0 - -(N : ℤ) = -(g₂ 1 0 - N) by ring]
        exact (dvd_sub this (dvd_refl _)).neg_right
      exact h2
    · rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      have hAt : ((A 0 0 : ℤ) : ZMod N) * ((t : ℤ) : ZMod N) = 1 := by
        have := congrArg (Int.cast : ℤ → ZMod N) hdetA
        push_cast at this
        rw [hA10, hA11] at this
        simpa using this
      rw [ht] at hAt
      linear_combination (g₂ 0 0 : ZMod N) * hAt - (A 0 0 : ZMod N) * h₁
  · rw [map_mul, map_mul, map_inv, mul_assoc (mapGL ℚ g₁) (mapGL ℚ A'), ← hcomm']
    group

/-- The mirror of Tau Ceti's `exists_natDiagGL_mul_mapGL_eq_of_isCoprime` for `diag(n, 1)`: for
`t` coprime to `n N` there are `A, A' ∈ SL₂(ℤ)` with lower rows `(n N, t)`, `(N, t)` and
`diag(n, 1) A = A' diag(n, 1)`. -/
theorem exists_natDiagGL_swap_mul_mapGL_eq {n : ℕ} (hn : 0 < n) {t : ℤ}
    (ht : IsCoprime t ((n * N : ℕ) : ℤ)) :
    ∃ A A' : SL(2, ℤ), A 1 0 = n * N ∧ A 1 1 = t ∧ A' 1 0 = N ∧ A' 1 1 = t ∧
      natDiagGL 2 ![n, 1] * mapGL ℚ A = mapGL ℚ A' * natDiagGL 2 ![n, 1] := by
  obtain ⟨α, β, hαβ⟩ := ht
  push_cast at hαβ
  let A : SL(2, ℤ) :=
    ⟨!![α, -β; n * (N : ℤ), t], by rw [Matrix.det_fin_two_of]; linear_combination hαβ⟩
  let A' : SL(2, ℤ) :=
    ⟨!![α, -(β * n); (N : ℤ), t], by rw [Matrix.det_fin_two_of]; linear_combination hαβ⟩
  refine ⟨A, A', rfl, rfl, rfl, rfl, Units.ext ?_⟩
  have hD : ((natDiagGL 2 ![n, 1] : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      !![(n : ℚ), 0; 0, 1] := by
    rw [natDiagGL_coe 2 ![n, 1] (fun i ↦ by fin_cases i <;> simp [hn])]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [Units.val_mul, Units.val_mul, hD, coe_mapGL_int_rat_fin_two, coe_mapGL_int_rat_fin_two,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [A, A', Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  congrm !![?_, ?_; ?_, ?_] <;> push_cast <;> ring

/-- **(4.5.42) for `diag(m, l)`** (`l ∣ m`, an element of Miyake's `Δ₀*(N)` when `(l, N) = 1`):
`Γ₀(N) diag(m, l) Γ₀(N) ⊆ Γ₀(N) diag(m, l) Γ₁(N)`. -/
theorem doubleCoset_natDiagGL_swap_gamma0_subset {l m : ℕ} [NeZero N] (hl : 0 < l) (hlm : l ∣ m)
    (hm : 0 < m) :
    doubleCoset (natDiagGL 2 ![m, l]) (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N) ⊆
      doubleCoset (natDiagGL 2 ![m, l]) (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N) := by
  intro x hx
  obtain ⟨_, ⟨g₁, hg₁, rfl⟩, _, ⟨g₂, hg₂, rfl⟩, rfl⟩ := mem_doubleCoset.mp hx
  obtain ⟨n, rfl⟩ := hlm
  have hn : 0 < n := Nat.pos_of_mul_pos_left hm
  have : NeZero n := ⟨hn.ne'⟩
  have h₁ := intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hg₂
  let u : (ZMod N)ˣ := ⟨g₂ 1 1, g₂ 0 0, by rw [mul_comm]; exact h₁, h₁⟩
  obtain ⟨t, htc, htu⟩ := ZMod.exists_isCoprime_mul_intCast_eq n u
  have ht : ((t : ℤ) : ZMod N) = ((g₂ 1 1 : ℤ) : ZMod N) := htu
  obtain ⟨A, A', hA10, hA11, hA'10, hA'11, hcomm⟩ := exists_natDiagGL_swap_mul_mapGL_eq hn htc
  have hD : ((natDiagGL 2 ![l * n, l] : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (l : ℚ) • ((natDiagGL 2 ![n, 1] : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) := by
    rw [natDiagGL_coe 2 ![l * n, l] (fun i ↦ by fin_cases i <;> simp [hl, hm]),
      natDiagGL_coe 2 ![n, 1] (fun i ↦ by fin_cases i <;> simp [hn])]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]
  have hcomm' : natDiagGL 2 ![l * n, l] * mapGL ℚ A = mapGL ℚ A' * natDiagGL 2 ![l * n, l] := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hD, Matrix.smul_mul, Matrix.mul_smul, ← Units.val_mul,
      ← Units.val_mul, hcomm]
  have hA' : A' ∈ Gamma0 N := mem_Gamma0_iff_dvd.mpr (by rw [hA'10])
  have hdetA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 :=
    Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one A
  refine mem_doubleCoset.mpr ⟨mapGL ℚ (g₁ * A'), Subgroup.mem_map_of_mem _ (mul_mem hg₁ hA'),
    mapGL ℚ (A⁻¹ * g₂), Subgroup.mem_map_of_mem _ ?_, ?_⟩
  · have : A⁻¹ * g₂ = (g₂⁻¹ * (A⁻¹)⁻¹)⁻¹ := by group
    rw [this]
    refine inv_mem (mul_inv_mem_Gamma1_iff_dvd_sub.mpr ?_)
    rw [SL2_inv_expl, SL2_inv_expl]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
    refine ⟨?_, ?_⟩
    · rw [hA10]
      have := mem_Gamma0_iff_dvd.mp hg₂
      rw [show -g₂ 1 0 - -((n : ℤ) * N) = -(g₂ 1 0 - n * N) by push_cast; ring]
      exact (dvd_sub this (dvd_mul_left _ _)).neg_right
    · rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      have hAt : ((A 0 0 : ℤ) : ZMod N) * ((t : ℤ) : ZMod N) = 1 := by
        have := congrArg (Int.cast : ℤ → ZMod N) hdetA
        push_cast at this
        rw [hA10, hA11] at this
        simpa using this
      rw [ht] at hAt
      linear_combination (g₂ 0 0 : ZMod N) * hAt - (A 0 0 : ZMod N) * h₁
  · rw [map_mul, map_mul, map_inv, mul_assoc (mapGL ℚ g₁) (mapGL ℚ A'), ← hcomm']
    group

/-- Lemma 4.5.2 at the level of elements (wave 5's `exists_single_eq_heckeTPair`): every
`α ∈ Δ₀(N)` lies in `Γ₀(N) diag(l, m) Γ₀(N)` for some `l ∣ m`, `(l, N) = 1`. -/
theorem exists_mem_doubleCoset_natDiagGL [NeZero N] {α : GL (Fin 2) ℚ} (hα : α ∈ Delta0 N) :
    ∃ l m : ℕ, 0 < l ∧ l ∣ m ∧ 0 < m ∧ l.Coprime N ∧
      α ∈ doubleCoset (natDiagGL 2 ![l, m]) (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N) := by
  obtain ⟨l, m, hl, hlm, hm, hlN, h⟩ :=
    Wave5.exists_single_eq_heckeTPair N (HeckeCoset.mk (gamma0Q N) (gamma0Q N) ⟨α, hα⟩)
  refine ⟨l, m, hl, hlm, hm, hlN, ?_⟩
  have hpos : ∀ i, 0 < (![l, m] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [hl, hm]
  have hc : Nat.Coprime ((![l, m] : Fin 2 → ℕ) 0) N := by simpa using hlN
  rw [heckeTPair, diagElemGamma0_of_pos_of_coprime N hpos hc] at h
  have hD := Finsupp.single_left_injective (one_ne_zero (α := ℤ)) h
  have hset := congrArg HeckeCoset.toSet hD
  rw [HeckeCoset.toSet_mk, diagCosetGamma0_toSet] at hset
  rw [← hset]
  exact mem_doubleCoset_self _ _ _

/-- **Miyake (4.5.42)**, for every `α ∈ Δ₀(N)`: `Γ₀(N) α Γ₀(N) = Γ₀(N) α Γ₁(N)`. -/
@[kb "miyake1989" "(4.5.42), p. 151 (for α ∈ Δ₀(N))"]
theorem doubleCoset_gamma0_eq_gamma0_gamma1 [NeZero N] {α : GL (Fin 2) ℚ} (hα : α ∈ Delta0 N) :
    doubleCoset α (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N) =
      doubleCoset α (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N) := by
  obtain ⟨l, m, hl, hlm, hm, -, h⟩ := exists_mem_doubleCoset_natDiagGL hα
  have h1 := doubleCoset_natDiagGL_gamma0_subset (N := N) hl hlm hm
  have hα1 : α ∈ doubleCoset (natDiagGL 2 ![l, m]) (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N) :=
    h1 h
  rw [doubleCoset_eq_of_mem h, doubleCoset_eq_of_mem hα1]
  exact le_antisymm h1 (doubleCoset_mono le_rfl (gamma1Q_le_gamma0Q (N := N)))

/-- **Miyake, Theorem 2.7.6 for `(Γ₁(N), Γ₀(N))`**, general form: if `α` is integral with
`c_α ≡ 0 (mod N)`, `a_α` or `d_α` a unit modulo `N`, and `Γ₀(N) α Γ₀(N) = Γ₀(N) α Γ₁(N)`, then a
complete set of representatives of `Γ₁(N) \ Γ₁(N) α Γ₁(N)` is one of `Γ₀(N) \ Γ₀(N) α Γ₀(N)`. -/
theorem isCosetReps_of_gamma1_of_eq [NeZero N] {α : GL (Fin 2) ℚ} {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : (α : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ)) (hA10 : (N : ℤ) ∣ A 1 0)
    (hAu : IsUnit (A 0 0 : ZMod N) ∨ IsUnit (A 1 1 : ZMod N))
    (hcov : doubleCoset α (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N) =
      doubleCoset α (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N)) {ι : Type*}
    {a : ι → GL (Fin 2) ℚ}
    (hcover : doubleCoset α (gamma1Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N) =
      ⋃ i, MulOpposite.op (a i) • (gamma1Q N : Set (GL (Fin 2) ℚ)))
    (hinj : Function.Injective fun i ↦ MulOpposite.op (a i) • (gamma1Q N : Set (GL (Fin 2) ℚ))) :
    IsCosetReps N α a := by
  have hmem : ∀ i, a i ∈ doubleCoset α (gamma1Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N) := fun i ↦ by
    rw [hcover]
    exact Set.mem_iUnion.mpr ⟨i, mem_own_rightCoset (gamma1Q N).toSubmonoid _⟩
  refine ⟨?_, ?_⟩
  · rw [hcov]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      obtain ⟨g, hg, γ, hγ, rfl⟩ := mem_doubleCoset.mp hx
      have hαγ : α * γ ∈ doubleCoset α (gamma1Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N) :=
        mem_doubleCoset.mpr ⟨1, one_mem _, γ, hγ, by group⟩
      rw [hcover, Set.mem_iUnion] at hαγ
      obtain ⟨i, hi⟩ := hαγ
      refine ⟨i, ?_⟩
      rw [mem_rightCoset_iff] at hi ⊢
      have := mul_mem hg (gamma1Q_le_gamma0Q hi)
      simpa [mul_assoc] using this
    · rintro ⟨i, hi⟩
      rw [mem_rightCoset_iff] at hi
      obtain ⟨h, hh, γ, hγ, he⟩ := mem_doubleCoset.mp (hmem i)
      refine mem_doubleCoset.mpr ⟨x * (a i)⁻¹ * h, mul_mem hi (gamma1Q_le_gamma0Q hh), γ, hγ, ?_⟩
      calc x = x * (a i)⁻¹ * a i := by group
        _ = _ := by rw [he]; group
  · intro i j hij
    apply hinj
    simp only at hij ⊢
    rw [rightCoset_eq_iff] at hij ⊢
    obtain ⟨Xi, hXi, hXi10, hXi00, hXi11⟩ := mem_doubleCoset_gamma1_entries hA hA10 (hmem i)
    obtain ⟨Xj, hXj, -, hXj00, hXj11⟩ := mem_doubleCoset_gamma1_entries hA hA10 (hmem j)
    obtain ⟨d, hd, hde⟩ := Subgroup.mem_map.mp hij
    have heq : a j = mapGL ℚ d * a i * mapGL ℚ (1 : SL(2, ℤ)) := by
      rw [map_one, mul_one, hde]; group
    have hX : Xj = (d : Matrix (Fin 2) (Fin 2) ℤ) * Xi * ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) :=
      Matrix.map_injective Int.cast_injective
        (hXj.symm.trans (heq ▸ mapGL_mul_coe_eq_intMatrix 2 d 1 (a i) Xi hXi))
    have hd10 := Gamma0_mem.mp hd
    have hdet := intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hd
    have h00 : ((d 0 0 : ℤ) : ZMod N) * ((A 0 0 : ℤ) : ZMod N) = (A 0 0 : ZMod N) := by
      have := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℤ ↦ ((X 0 0 : ℤ) : ZMod N)) hX
      simp only [Matrix.SpecialLinearGroup.coe_one, mul_one, Matrix.mul_apply,
        Fin.sum_univ_two] at this
      push_cast at this
      rw [hXj00, hXi00, hXi10] at this
      simpa using this.symm
    have h11 : ((d 1 1 : ℤ) : ZMod N) * ((A 1 1 : ℤ) : ZMod N) = (A 1 1 : ZMod N) := by
      have := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℤ ↦ ((X 1 1 : ℤ) : ZMod N)) hX
      simp only [Matrix.SpecialLinearGroup.coe_one, mul_one, Matrix.mul_apply,
        Fin.sum_univ_two] at this
      push_cast at this
      rw [hXj11, hXi11, hd10] at this
      simpa using this.symm
    have hd00 : ((d 0 0 : ℤ) : ZMod N) = 1 ∧ ((d 1 1 : ℤ) : ZMod N) = 1 := by
      rcases hAu with hu | hu
      · have h1 : ((d 0 0 : ℤ) : ZMod N) = 1 := by
          have := congrArg (· * (hu.unit⁻¹ : (ZMod N)ˣ).val) h00
          simp only [mul_assoc] at this
          simpa using this
        refine ⟨h1, ?_⟩
        rwa [h1, one_mul] at hdet
      · have h1 : ((d 1 1 : ℤ) : ZMod N) = 1 := by
          have := congrArg (· * (hu.unit⁻¹ : (ZMod N)ˣ).val) h11
          simp only [mul_assoc] at this
          simpa using this
        refine ⟨?_, h1⟩
        rwa [h1, mul_one] at hdet
    rw [← hde]
    exact Subgroup.mem_map_of_mem _ ((Gamma1_mem N d).mpr ⟨hd00.1, hd00.2, hd10⟩)

/-- **Miyake, Theorem 2.7.6 for `(Γ₁(N), Γ₀(N))`** (proof of Theorem 4.5.18): for `α ∈ Δ₀(N)`,
a complete set of representatives of `Γ₁(N) \ Γ₁(N) α Γ₁(N)` is a complete set of
representatives of `Γ₀(N) \ Γ₀(N) α Γ₀(N)`. -/
@[kb "miyake1989" "Theorem 4.5.18, proof, p. 151"]
theorem isCosetReps_of_gamma1 [NeZero N] {α : GL (Fin 2) ℚ} (hα : α ∈ Delta0 N) {ι : Type*}
    {a : ι → GL (Fin 2) ℚ}
    (hcover : doubleCoset α (gamma1Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N) =
      ⋃ i, MulOpposite.op (a i) • (gamma1Q N : Set (GL (Fin 2) ℚ)))
    (hinj : Function.Injective fun i ↦ MulOpposite.op (a i) • (gamma1Q N : Set (GL (Fin 2) ℚ))) :
    IsCosetReps N α a := by
  obtain ⟨A, hA, -, hA10, hAu⟩ := (mem_Delta0_iff N).mp hα
  exact isCosetReps_of_gamma1_of_eq hA hA10 (Or.inl hAu)
    (doubleCoset_gamma0_eq_gamma0_gamma1 hα) hcover hinj

/-! ### `Δ₁(N)` and Theorem 4.5.18 -/

/-- **Miyake's `Δ₁(N)`** (p. 151): integral matrices `[a b; c d]` of positive determinant with
`a ≡ 1`, `c ≡ 0 (mod N)`. -/
def Delta1 (N : ℕ) : Submonoid (GL (Fin 2) ℚ) where
  carrier := {g | ∃ A : Matrix (Fin 2) (Fin 2) ℤ,
    (↑g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) ∧
      0 < (↑g : Matrix (Fin 2) (Fin 2) ℚ).det ∧ (N : ℤ) ∣ A 1 0 ∧ (A 0 0 : ZMod N) = 1}
  one_mem' := ⟨1, by simp, by simp, by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨A, hA, hda, hAN, hA1⟩ ⟨B, hB, hdb, hBN, hB1⟩
    refine ⟨A * B, ?_, ?_, ?_, ?_⟩
    · ext i j
      simp [hA, hB, Matrix.mul_apply, Matrix.map_apply]
    · simpa [Matrix.det_mul] using mul_pos hda hdb
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_mul_of_dvd_left hAN _) (dvd_mul_of_dvd_right hBN _)
    · have hentry : ((A * B) 0 0 : ZMod N) = (A 0 0 : ZMod N) * (B 0 0 : ZMod N) := by
        simp [Matrix.mul_apply, Fin.sum_univ_two,
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hBN]
      rw [hentry, hA1, hB1, one_mul]

theorem Delta1_le_Delta0 : Delta1 N ≤ Delta0 N := by
  rintro g ⟨A, hA, hd, hN, h1⟩
  exact ⟨A, hA, hd, hN, by rw [h1]; exact isUnit_one⟩

/-- **Miyake, Theorem 4.5.18 (1)**, the correspondence of double cosets: for `α, β ∈ Δ₁(N)`,
`Γ₁(N) α Γ₁(N) = Γ₁(N) β Γ₁(N)` if and only if `Γ₀(N) α Γ₀(N) = Γ₀(N) β Γ₀(N)`; so
`Γ₁(N) α Γ₁(N) ↦ Γ₀(N) α Γ₀(N)` is well defined and injective. -/
@[kb "miyake1989" "Theorem 4.5.18 (1), p. 151 (bijection of double cosets)"]
theorem doubleCoset_gamma1_eq_iff [NeZero N] {α β : GL (Fin 2) ℚ} (hα : α ∈ Delta1 N)
    (hβ : β ∈ Delta1 N) :
    doubleCoset α (gamma1Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N) =
        doubleCoset β (gamma1Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N) ↔
      doubleCoset α (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N) =
        doubleCoset β (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N) := by
  constructor
  · intro h
    have hα1 : α ∈ doubleCoset β (gamma1Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N) :=
      h ▸ mem_doubleCoset_self _ _ _
    exact doubleCoset_eq_of_mem
      (doubleCoset_mono (gamma1Q_le_gamma0Q (N := N)) (gamma1Q_le_gamma0Q (N := N)) hα1)
  · intro h
    have hα0 : α ∈ doubleCoset β (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N) :=
      h ▸ mem_doubleCoset_self _ _ _
    rw [doubleCoset_gamma0_eq_gamma0_gamma1 (Delta1_le_Delta0 hβ)] at hα0
    obtain ⟨_, ⟨g, hg, rfl⟩, γ, hγ, he⟩ := mem_doubleCoset.mp hα0
    obtain ⟨A, hA, -, -, hA1⟩ := hα
    obtain ⟨B, hB, -, hB10, hB1⟩ := hβ
    -- the integral matrix of `β γ` is `≡ [1 *; 0 *]`
    obtain ⟨Y, hY, hY10, hY00, -⟩ := mem_doubleCoset_gamma1_entries hB hB10
      (mem_doubleCoset.mpr ⟨1, one_mem _, γ, hγ, by rw [one_mul]⟩ :
        β * γ ∈ doubleCoset β (gamma1Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N))
    have heq : α = mapGL ℚ g * (β * γ) * mapGL ℚ (1 : SL(2, ℤ)) := by
      rw [map_one, mul_one, he, mul_assoc]
    have hX : A = (g : Matrix (Fin 2) (Fin 2) ℤ) * Y * ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) :=
      Matrix.map_injective Int.cast_injective
        (hA.symm.trans (heq ▸ mapGL_mul_coe_eq_intMatrix 2 g 1 (β * γ) Y hY))
    have hg10 := Gamma0_mem.mp hg
    have hg00 : ((g 0 0 : ℤ) : ZMod N) = 1 := by
      have := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℤ ↦ ((X 0 0 : ℤ) : ZMod N)) hX
      simp only [Matrix.SpecialLinearGroup.coe_one, mul_one, Matrix.mul_apply,
        Fin.sum_univ_two] at this
      push_cast at this
      rw [hA1, hY00, hB1, hY10] at this
      simpa using this.symm
    have hg11 : ((g 1 1 : ℤ) : ZMod N) = 1 := by
      have := intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hg
      rwa [hg00, one_mul] at this
    have hg1 : mapGL ℚ g ∈ gamma1Q N :=
      Subgroup.mem_map_of_mem _ ((Gamma1_mem N g).mpr ⟨hg00, hg11, hg10⟩)
    exact doubleCoset_eq_of_mem (mem_doubleCoset.mpr ⟨mapGL ℚ g, hg1, γ, hγ, he⟩)

/-- **Miyake, Theorem 4.5.18 (1)**, surjectivity of the correspondence: every double coset
`Γ₀(N) β Γ₀(N)`, `β ∈ Δ₀(N)`, is `Γ₀(N) α Γ₀(N)` for some `α ∈ Δ₁(N)`. -/
@[kb "miyake1989" "Theorem 4.5.18 (1), p. 151 (bijection of double cosets)"]
theorem exists_delta1_doubleCoset_eq [NeZero N] {β : GL (Fin 2) ℚ} (hβ : β ∈ Delta0 N) :
    ∃ α ∈ Delta1 N, doubleCoset α (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N) =
      doubleCoset β (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N) := by
  obtain ⟨B, hB, hdet, hB10, hBu⟩ := (mem_Delta0_iff N).mp hβ
  obtain ⟨t, htc, htu⟩ := ZMod.exists_isCoprime_mul_intCast_eq 1 hBu.unit
  obtain ⟨A, -, hA10, hA11, -, -, -⟩ := exists_natDiagGL_mul_mapGL_eq_of_isCoprime one_pos htc
  have hA0 : A ∈ Gamma0 N := mem_Gamma0_iff_dvd.mpr (by rw [hA10])
  have hdetA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 :=
    Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one A
  have ht : ((t : ℤ) : ZMod N) = (B 0 0 : ZMod N) := by
    rw [htu, IsUnit.unit_spec]
  have hB10' : ((B 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hB10
  have heq : mapGL ℚ A * β = mapGL ℚ A * β * mapGL ℚ (1 : SL(2, ℤ)) := by rw [map_one, mul_one]
  have hX : ((mapGL ℚ A * β : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      ((A : Matrix (Fin 2) (Fin 2) ℤ) * B).map (Int.cast : ℤ → ℚ) := by
    rw [heq, mapGL_mul_coe_eq_intMatrix 2 A 1 β B hB]
    simp
  refine ⟨mapGL ℚ A * β, ⟨_, hX, ?_, ?_, ?_⟩, ?_⟩
  · rw [Units.val_mul, Matrix.det_mul]
    have : ((mapGL ℚ A : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      simp
    rw [this, one_mul]
    exact hdet
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hA10]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right hB10 _)
  · have h1 := congrArg (Int.cast : ℤ → ZMod N) hdetA
    push_cast at h1
    rw [hA10, hA11, ht] at h1
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [hB10']
    simpa using h1
  · exact doubleCoset_eq_of_mem
      (mem_doubleCoset.mpr ⟨mapGL ℚ A, Subgroup.mem_map_of_mem _ hA0, 1, one_mem _, by simp⟩)

end ModularFormsKB.Miyake.Wave8
