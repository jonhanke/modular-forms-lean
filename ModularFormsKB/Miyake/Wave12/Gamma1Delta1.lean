import ModularFormsKB.Miyake.Wave8.Gamma1Reps
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.UpperUnit

/-!
# Miyake §4.5: `Δ₁(N)` and `Γ₁(N)` inside `Δ₀(N)` and `Γ₀(N)`

Miyake, *Modular Forms* (Springer 1989), Theorem 4.5.18 (1), p. 151. Facts about the pairs
`(Γ₁(N), Δ₁(N)) ⊆ (Γ₀(N), Δ₀(N))` used for the ring isomorphism of Theorem 4.5.18 (1)
(`HeckeRingIso.lean`): the Hecke triple instance for `Δ₁(N)`, cancellation of `Γ₀(N)`-factors
into `Γ₁(N)`, and the left-coset form `Γ₀(N) α Γ₀(N) = Γ₁(N) α Γ₀(N)` of (4.5.42) (wave 8 proved
the right-coset form `Γ₀(N) α Γ₀(N) = Γ₀(N) α Γ₁(N)`).

Tool: Tau Ceti's upper-left unit character `HeckeRing.GL2.Delta0UpperUnit : Δ₀(N) →* (ZMod N)ˣ`;
`Δ₁(N)` and `Γ₁(N)` are the elements of `Δ₀(N)` and `Γ₀(N)` on which it is `1`.
-/

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup DoubleCoset HeckeRing.GL2
open scoped MatrixGroups Pointwise

noncomputable section

namespace ModularFormsKB.Miyake.Wave12

open ModularFormsKB.Miyake.Wave7 ModularFormsKB.Miyake.Wave8

variable {N : ℕ} [NeZero N]

/-- The upper-left unit modulo `N` of an element of `Δ₀(N)`. -/
abbrev upperUnit (x : GL (Fin 2) ℚ) (hx : x ∈ Delta0 N) : (ZMod N)ˣ :=
  Delta0UpperUnit N ⟨x, hx⟩

omit [NeZero N] in
theorem upperUnit_mul {x y : GL (Fin 2) ℚ} (hx : x ∈ Delta0 N) (hy : y ∈ Delta0 N) :
    upperUnit (x * y) (mul_mem hx hy) = upperUnit x hx * upperUnit y hy :=
  map_mul (Delta0UpperUnit N) ⟨x, hx⟩ ⟨y, hy⟩

omit [NeZero N] in
theorem gamma0Q_le_delta0 : (gamma0Q N).toSubmonoid ≤ Delta0 N := by
  rintro _ ⟨g, hg, rfl⟩
  exact mapGL_mem_Delta0 N ⟨g, hg⟩

omit [NeZero N] in
/-- The upper-left unit of `γ ∈ Γ₀(N)` is its upper-left entry modulo `N`. -/
theorem upperUnit_mapGL_val {g : SL(2, ℤ)} (hg : g ∈ Gamma0 N) :
    (upperUnit (mapGL ℚ g) (mapGL_mem_Delta0 N ⟨g, hg⟩) : ZMod N) = ((g 0 0 : ℤ) : ZMod N) :=
  Delta0UpperUnit_apply_val N (A := (g : Matrix (Fin 2) (Fin 2) ℤ))
    (by simp [mapGL_coe_matrix, algebraMap_int_eq])

omit [NeZero N] in
/-- The upper-left unit of an element of `Δ₁(N)` is `1`. -/
theorem delta0UpperUnit_eq_one_of_mem_delta1 {x : GL (Fin 2) ℚ} (hx : x ∈ Delta1 N) :
    Delta0UpperUnit N ⟨x, Delta1_le_Delta0 hx⟩ = 1 := by
  obtain ⟨A, hA, -, -, h1⟩ := hx
  ext
  rw [Delta0UpperUnit_apply_val N hA, h1, Units.val_one]

omit [NeZero N] in
/-- An element of `Δ₀(N)` with upper-left unit `1` lies in `Δ₁(N)`. -/
theorem mem_delta1_of_delta0UpperUnit_eq_one {x : GL (Fin 2) ℚ} (hx : x ∈ Delta0 N)
    (h : Delta0UpperUnit N ⟨x, hx⟩ = 1) : x ∈ Delta1 N := by
  obtain ⟨A, hA, hd, hN, -⟩ := (mem_Delta0_iff N).mp hx
  refine ⟨A, hA, hd, hN, ?_⟩
  have := congrArg Units.val h
  rwa [Delta0UpperUnit_apply_val N hA, Units.val_one] at this

omit [NeZero N] in
/-- An element of `Γ₀(N)` with upper-left unit `1` lies in `Γ₁(N)`. -/
theorem mem_gamma1Q_of_delta0UpperUnit_eq_one {γ : GL (Fin 2) ℚ} (hγ : γ ∈ gamma0Q N)
    (hγ' : γ ∈ Delta0 N) (h : Delta0UpperUnit N ⟨γ, hγ'⟩ = 1) : γ ∈ gamma1Q N := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
  have h00 : ((g 0 0 : ℤ) : ZMod N) = 1 := by
    rw [← upperUnit_mapGL_val hg]
    exact congrArg Units.val h
  have h11 : ((g 1 1 : ℤ) : ZMod N) = 1 := by
    have := intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hg
    rwa [h00, one_mul] at this
  exact Subgroup.mem_map_of_mem _ ((Gamma1_mem N g).mpr ⟨h00, h11, Gamma0_mem.mp hg⟩)

omit [NeZero N] in
theorem gamma1Q_le_delta1 : (gamma1Q N).toSubmonoid ≤ Delta1 N := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨h00, -, h10⟩ := (Gamma1_mem N g).mp hg
  have hg0 : g ∈ Gamma0 N := Gamma1_in_Gamma0 N hg
  refine mem_delta1_of_delta0UpperUnit_eq_one (mapGL_mem_Delta0 N ⟨g, hg0⟩) ?_
  ext
  rw [upperUnit_mapGL_val hg0, h00, Units.val_one]

/-- `(Δ₁(N), Γ₁(N), Γ₁(N))` is a Hecke triple. -/
instance instIsHeckeTripleDelta1 : IsHeckeTriple (Delta1 N) (gamma1Q N) (gamma1Q N) where
  left_le := gamma1Q_le_delta1
  right_le := gamma1Q_le_delta1
  commensurable := Subgroup.Commensurable.refl _
  le_commensurator_right := fun _ hx ↦
    IsHeckeTriple.le_commensurator_right (Δ := Delta0 N) (H₁ := gamma1Q N) (H₂ := gamma1Q N)
      (Delta1_le_Delta0 hx)

omit [NeZero N] in
/-- Right cancellation: if `x ∈ Δ₁(N)`, `γ ∈ Γ₀(N)` and `x γ ∈ Δ₁(N)`, then `γ ∈ Γ₁(N)`. -/
theorem mem_gamma1Q_of_mul_mem_delta1 {x γ : GL (Fin 2) ℚ} (hx : x ∈ Delta1 N)
    (hγ : γ ∈ gamma0Q N) (hxγ : x * γ ∈ Delta1 N) : γ ∈ gamma1Q N := by
  have hγ' : γ ∈ Delta0 N := gamma0Q_le_delta0 hγ
  have hx' : x ∈ Delta0 N := Delta1_le_Delta0 hx
  refine mem_gamma1Q_of_delta0UpperUnit_eq_one hγ hγ' ?_
  have h1 := delta0UpperUnit_eq_one_of_mem_delta1 hx
  have h2 := delta0UpperUnit_eq_one_of_mem_delta1 hxγ
  have hm := upperUnit_mul hx' hγ'
  change upperUnit x hx' = 1 at h1
  change upperUnit (x * γ) (mul_mem hx' hγ') = 1 at h2
  rw [h2, h1, one_mul] at hm
  exact hm.symm

/-- **(4.5.42), left-coset form**: for `α ∈ Δ₁(N)`, `Γ₀(N) α Γ₀(N) ⊆ Γ₁(N) α Γ₀(N)`. -/
@[kb "miyake1989" "(4.5.42), p. 151 (left-coset form, for α ∈ Δ₁(N))"]
theorem doubleCoset_gamma0_subset_gamma1_gamma0 {α : GL (Fin 2) ℚ} (hα : α ∈ Delta1 N) :
    doubleCoset α (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N) ⊆
      doubleCoset α (gamma1Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N) := by
  intro x hx
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, rfl⟩ := mem_doubleCoset.mp hx
  have hα0 : α ∈ Delta0 N := Delta1_le_Delta0 hα
  -- `α γ₁ ∈ Γ₀ α Γ₀ = Γ₀ α Γ₁`
  have hmem : α * γ₁ ∈ doubleCoset α (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma1Q N) := by
    rw [← doubleCoset_gamma0_eq_gamma0_gamma1 hα0]
    exact mem_doubleCoset.mpr ⟨1, one_mem _, γ₁, hγ₁, by rw [one_mul]⟩
  obtain ⟨δ, hδ, σ, hσ, he⟩ := mem_doubleCoset.mp hmem
  have hσ0 : σ ∈ gamma0Q N := gamma1Q_le_gamma0Q hσ
  set τ := γ₁ * σ⁻¹ with hτ
  have hτ0 : τ ∈ gamma0Q N := mul_mem hγ₁ (inv_mem hσ0)
  have hδα : δ * α = α * τ := by
    rw [hτ, ← mul_assoc, he]; group
  -- units: `u(δ) = u(τ) = u(γ₁)`
  have hδ' := gamma0Q_le_delta0 hδ
  have hτ' := gamma0Q_le_delta0 hτ0
  have hγ₁' := gamma0Q_le_delta0 hγ₁
  have hσ' := gamma0Q_le_delta0 hσ0
  have hσinv0 : σ⁻¹ ∈ gamma0Q N := inv_mem hσ0
  have hσinv' := gamma0Q_le_delta0 hσinv0
  have huα : upperUnit α hα0 = 1 := delta0UpperUnit_eq_one_of_mem_delta1 hα
  have huσ : upperUnit σ hσ' = 1 :=
    delta0UpperUnit_eq_one_of_mem_delta1 (gamma1Q_le_delta1 hσ)
  have huσinv : upperUnit σ⁻¹ hσinv' = 1 :=
    delta0UpperUnit_eq_one_of_mem_delta1 (gamma1Q_le_delta1 ((gamma1Q N).inv_mem hσ))
  have hδτ : upperUnit δ hδ' = upperUnit τ hτ' := by
    have h1 := upperUnit_mul hδ' hα0
    have h2 := upperUnit_mul hα0 hτ'
    have h3 : upperUnit (δ * α) (mul_mem hδ' hα0) = upperUnit (α * τ) (mul_mem hα0 hτ') := by
      simp only [upperUnit, hδα]
    rw [h1, h2, huα, mul_one, one_mul] at h3
    exact h3
  have hτγ : upperUnit τ hτ' = upperUnit γ₁ hγ₁' := by
    have := upperUnit_mul hγ₁' hσinv'
    rw [huσinv, mul_one] at this
    exact this
  -- `σ' = γ₁ δ⁻¹ ∈ Γ₁(N)`
  have hδinv0 : δ⁻¹ ∈ gamma0Q N := inv_mem hδ
  have hδinv' := gamma0Q_le_delta0 hδinv0
  have hσ'0 : γ₁ * δ⁻¹ ∈ gamma0Q N := mul_mem hγ₁ hδinv0
  have hσ'1 : γ₁ * δ⁻¹ ∈ gamma1Q N := by
    refine mem_gamma1Q_of_delta0UpperUnit_eq_one hσ'0 (gamma0Q_le_delta0 hσ'0) ?_
    have hm := upperUnit_mul (gamma0Q_le_delta0 hσ'0) hδ'
    have hc : upperUnit (γ₁ * δ⁻¹ * δ) (mul_mem (gamma0Q_le_delta0 hσ'0) hδ') =
        upperUnit γ₁ hγ₁' := by
      simp only [upperUnit, inv_mul_cancel_right]
    rw [hc, hδτ.trans hτγ |>.symm] at hm
    have : upperUnit δ hδ' * 1 = upperUnit δ hδ' * upperUnit (γ₁ * δ⁻¹)
        (gamma0Q_le_delta0 hσ'0) := by
      rw [mul_one, mul_comm]; exact hm
    exact (mul_left_cancel this).symm
  refine mem_doubleCoset.mpr ⟨γ₁ * δ⁻¹, hσ'1, τ * γ₂, mul_mem hτ0 hγ₂, ?_⟩
  calc γ₁ * α * γ₂ = γ₁ * δ⁻¹ * (δ * α) * γ₂ := by group
    _ = γ₁ * δ⁻¹ * α * (τ * γ₂) := by rw [hδα]; group

/-- Every double coset `Γ₀(N) β Γ₀(N)`, `β ∈ Δ₀(N)`, meets `Δ₁(N)`. -/
theorem exists_mem_delta1_mem_doubleCoset {β : GL (Fin 2) ℚ} (hβ : β ∈ Delta0 N) :
    ∃ α ∈ Delta1 N, α ∈ doubleCoset β (gamma0Q N : Set (GL (Fin 2) ℚ)) (gamma0Q N) := by
  obtain ⟨α, hα, he⟩ := exists_delta1_doubleCoset_eq hβ
  exact ⟨α, hα, he ▸ mem_doubleCoset_self _ _ _⟩

end ModularFormsKB.Miyake.Wave12
