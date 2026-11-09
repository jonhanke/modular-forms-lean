import ModularFormsKB.Milne.Ch5.LevelOne
import TauCeti.NumberTheory.ModularForms.Petersson.Normal

/-!
# Milne, Chapter 5: the Hecke operators for $\Gamma(1)$ are Hermitian (Theorem 5.23)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf pp. 75–77.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2
open scoped MatrixGroups ModularForm ArithmeticFunction.sigma HeckeCosetModule

namespace ModularFormsKB.Milne

/-! ### Theorem 5.23: $T(n)$ is Hermitian -/

/-- The Petersson inner product on $S_w(\Gamma(1))$: Tau Ceti's `CuspForm.peterssonInnerCosets` for
$\Gamma_1(1) = \mathrm{SL}_2(\mathbb Z)$, which is $\iint_D \bar f g\, y^{w}\,\frac{dx\,dy}{y^2}$ over the standard
fundamental domain $D$. Milne's $\langle f, g\rangle = \iint_D f\bar g\,y^{2k-2}dx\,dy$ is `levelOnePetersson g f`. -/
noncomputable def levelOnePetersson (w : ℤ) (f g : CuspForm 𝒮ℒ w) : ℂ :=
  CuspForm.peterssonInnerCosets ((levelOneCuspEquiv w).symm f : CuspForm ((Gamma1 1).map (mapGL ℝ)) w)
    ((levelOneCuspEquiv w).symm g)

/-- The Hecke elements of level one whose cusp-form action on `S_w(Γ₁(1), 1)` is Petersson-self-adjoint form a
subring (the Hecke ring is commutative). -/
noncomputable def petersson_selfAdjointSubring (w : ℤ) :
    Subring (𝕋 (Delta0 1) ((Gamma0 1).map (mapGL ℚ)) ℤ) where
  carrier := {x | ∀ u v, (TauCeti.CuspForm.peterssonInnerCosetsCharSpaceₛₗ w (1 : (ZMod 1)ˣ →* ℂˣ)).flip
    (heckeRingHomCuspCharSpace (N := 1) w 1 x u) v =
    (TauCeti.CuspForm.peterssonInnerCosetsCharSpaceₛₗ w (1 : (ZMod 1)ˣ →* ℂˣ)).flip u
    (heckeRingHomCuspCharSpace (N := 1) w 1 x v)}
  mul_mem' := by
    intro x y hx hy u v
    have hc : x * y = y * x := HeckeCosetModule.mul_comm_of_antiInvolution ℤ (atkinLehnerAntiInvolution 1)
      (atkinLehnerAntiInvolution_onHeckeCoset_eq_self 1) x y
    have e : ∀ a, heckeRingHomCuspCharSpace (N := 1) w 1 (x * y) a =
        heckeRingHomCuspCharSpace (N := 1) w 1 x (heckeRingHomCuspCharSpace (N := 1) w 1 y a) :=
      fun a => by rw [map_mul]; rfl
    have e' : ∀ a, heckeRingHomCuspCharSpace (N := 1) w 1 (x * y) a =
        heckeRingHomCuspCharSpace (N := 1) w 1 y (heckeRingHomCuspCharSpace (N := 1) w 1 x a) :=
      fun a => by rw [hc, map_mul]; rfl
    rw [e u, e' v, hx, hy]
  one_mem' := by
    intro u v
    simp
  add_mem' := by
    intro x y hx hy u v
    simp only [map_add, LinearMap.add_apply, map_add, hx u v, hy u v]
  zero_mem' := by
    intro u v
    simp
  neg_mem' := by
    intro x hx u v
    simp only [map_neg, LinearMap.neg_apply, map_neg, hx u v]

/-- **Milne, Theorem 5.23.** The Hecke operators are Hermitian for the Petersson inner product on cusp forms of
weight $2k$ for $\Gamma(1)$: $\langle T(n)f, g\rangle = \langle f, T(n)g\rangle$ for all $n \ge 1$. -/
@[kb "milne2017mf" "Section 5, Theorem 5.23 (pdf p. 77)"]
theorem petersson_heckeTCusp_left (k : ℕ) {n : ℕ} (hn : n ≠ 0) (f g : CuspForm 𝒮ℒ (2 * k)) :
    levelOnePetersson (2 * k) (heckeTCusp (2 * k) n f) g = levelOnePetersson (2 * k) f (heckeTCusp (2 * k) n g) := by
  have hmem : heckeTCompositeGamma0 1 n ∈ petersson_selfAdjointSubring (2 * (k : ℤ)) := by
    refine heckeTCompositeGamma0_mem_of_forall_prime_dvd 1 (fun p hp _ ↦ ?_) fun p hp _ ↦ ?_
    · have h := isAdjointPair_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 (N := 1) (k := 2 * (k : ℤ))
        (χ := (1 : (ZMod 1)ˣ →* ℂˣ)) hp (Nat.coprime_one_right p)
      intro u v
      simpa using h u v
    · have hs := heckeRingHomCuspCharSpace_heckeTScalarGamma0 (N := 1) (2 * (k : ℤ))
        (1 : (ZMod 1)ˣ →* ℂˣ) p hp.pos (Nat.coprime_one_right p)
      intro u v
      show _ = _
      rw [hs]
      simp only [LinearMap.flip_apply, LinearMap.smul_apply, Module.End.one_apply,
        map_smulₛₗ, LinearMap.smul_apply]
      simp [map_zpow₀]
  have h := hmem ((levelOneCuspEquiv _).symm g) ((levelOneCuspEquiv _).symm f)
  simp only [levelOnePetersson, heckeTCusp, LinearEquiv.conj_apply]
  simpa using h.symm

end ModularFormsKB.Milne
