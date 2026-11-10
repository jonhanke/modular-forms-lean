import ModularFormsKB.Milne.RiemannSurface.Examples
import ModularFormsKB.Milne.Wave4A.CanonicalClass

/-!
# Milne, Exercise 1.24: the Riemann–Roch theorem for the Riemann sphere

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §1, Example 1.23 and Exercise 1.24 (pdf p. 22).

Following the hint of the exercise (partial fractions / Example 1.23):

* multiplication by a nonzero meromorphic function `h` identifies `L(D)` with `L(D - div h)` (`rrSpaceEquivMul`);
* `div(z - a) = [a] - [∞]` (`principalDivisor_coordinate_sub`), so every divisor `D` on the sphere is linearly
  equivalent to `(deg D) [∞]` and `L(D) ≅ L((deg D) [∞])` (`ell_eq_ell_degree_smul`);
* `ℓ(n [∞]) = n + 1` for `n ≥ 0` (Example 1.23, `ell_nsmul_divisorInfty`) and `0` for `n < 0`;
* every canonical divisor has degree `-2` (`div(dz) = -2[∞]`, `divisor_differential_coordinate`, and
  `RS.degree_divisor_eq_of_not_isZero`).

Hence `ℓ(D) = deg D + 1 + ℓ(K - D)` with `g = 0` (`riemannRoch_sphere`).
-/

open Filter Topology Set
open scoped Manifold

namespace ModularFormsKB.Milne

open TauCeti.RiemannSurface TauCeti.AlgebraicGeometry MeromorphicFunction RiemannSurface

section General

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X]
  [CompactSpace X]

/-- Multiplication by `h ≠ 0` maps `L(D)` onto `L(D - div h)`. -/
noncomputable def rrSpaceEquivMul {h : MeromorphicFunction X} (hh : h ≠ 0) (D : WeilDivisor X) :
    rrSpace X D ≃ₗ[ℂ] rrSpace X (D - principalDivisor X h) where
  toFun f := ⟨f.1 * h, fun x ↦ by
    have hf := f.2 x
    rw [(order x).map_mul, ← coe_principalDivisor_apply hh x]
    simp only [Finsupp.coe_sub, Pi.sub_apply, neg_sub]
    generalize order x f.1 = a at hf ⊢
    induction a using WithTop.recTopCoe with
    | top => simp
    | coe k =>
      have : -(D x) ≤ k := by exact_mod_cast hf
      exact_mod_cast (by omega : principalDivisor X h x - D x ≤ k + principalDivisor X h x)⟩
  invFun f := ⟨f.1 * h⁻¹, fun x ↦ by
    have hf := f.2 x
    have hinv : order x h⁻¹ = ((-principalDivisor X h x : ℤ) : WithTop ℤ) := by
      rw [AddValuation.map_inv, ← coe_principalDivisor_apply hh x]
      rfl
    rw [(order x).map_mul, hinv]
    simp only [Finsupp.coe_sub, Pi.sub_apply, neg_sub] at hf
    generalize order x f.1 = a at hf ⊢
    induction a using WithTop.recTopCoe with
    | top => simp
    | coe k =>
      have : principalDivisor X h x - D x ≤ k := by exact_mod_cast hf
      rw [← WithTop.coe_add]
      exact_mod_cast (by omega : -(D x) ≤ k + -principalDivisor X h x)⟩
  map_add' f g := by ext1; simp [add_mul]
  map_smul' c f := by ext1; simp [Algebra.smul_def, mul_assoc]
  left_inv f := by ext1; simp [mul_assoc, mul_inv_cancel₀ hh]
  right_inv f := by ext1; simp [mul_assoc, inv_mul_cancel₀ hh]

theorem ell_sub_principalDivisor {h : MeromorphicFunction X} (hh : h ≠ 0) (D : WeilDivisor X) :
    ell X (D - principalDivisor X h) = ell X D :=
  (rrSpaceEquivMul hh D).finrank_eq.symm

end General

/-! ### The sphere -/

section Sphere

/-- The point `a` as a divisor. -/
noncomputable abbrev pt (a : OnePoint ℂ) : WeilDivisor (OnePoint ℂ) := Finsupp.single a 1

/-- The order of `z - a` at `∞` is `-1`. -/
theorem order_coordinate_sub_infty (a : ℂ) :
    order OnePoint.infty (coordinate - algebraMap ℂ (MeromorphicFunction (OnePoint ℂ)) a) = -1 := by
  rw [AddValuation.map_sub_eq_of_lt_left, order_coordinate_infty]
  rw [order_coordinate_infty]
  by_cases ha : a = 0
  · subst ha; rw [map_zero, AddValuation.map_zero]; exact WithTop.coe_lt_top _
  · rw [order_algebraMap ha]; decide

theorem coordinate_sub_ne_zero (a : ℂ) :
    (coordinate - algebraMap ℂ (MeromorphicFunction (OnePoint ℂ)) a) ≠ 0 := by
  intro h
  have := order_coordinate_sub_infty a
  rw [h, AddValuation.map_zero] at this
  exact absurd this (by decide)

theorem coordinate_sub_apply_coe (a z : ℂ) :
    (coordinate - algebraMap ℂ (MeromorphicFunction (OnePoint ℂ)) a) (z : OnePoint ℂ) = ((z - a : ℂ) : OnePoint ℂ) :=
  sub_apply_of_eq_coe (coordinate_apply _) (congrFun (coe_algebraMap a) _)

/-- **`div(z - a) = [a] - [∞]`.** -/
theorem principalDivisor_coordinate_sub (a : ℂ) :
    principalDivisor (OnePoint ℂ) (coordinate - algebraMap ℂ (MeromorphicFunction (OnePoint ℂ)) a) =
      pt (a : OnePoint ℂ) - pt OnePoint.infty := by
  classical
  set h := coordinate - algebraMap ℂ (MeromorphicFunction (OnePoint ℂ)) a with hdef
  have hh : h ≠ 0 := coordinate_sub_ne_zero a
  have hinf : principalDivisor (OnePoint ℂ) h OnePoint.infty = -1 := by
    have h1 : ((principalDivisor (OnePoint ℂ) h OnePoint.infty : ℤ) : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) := by
      rw [coe_principalDivisor_apply hh, order_coordinate_sub_infty]; rfl
    exact WithTop.coe_injective h1
  have hoff : ∀ z : ℂ, z ≠ a → principalDivisor (OnePoint ℂ) h z = 0 := by
    intro z hz
    refine principalDivisor_apply_eq_zero hh _ ?_ ?_
    · rw [coordinate_sub_apply_coe]
      intro h0
      exact hz (sub_eq_zero.1 (OnePoint.coe_injective h0))
    · rw [coordinate_sub_apply_coe]; exact OnePoint.coe_ne_infty _
  have hsupp : (principalDivisor (OnePoint ℂ) h).support ⊆ {(a : OnePoint ℂ), OnePoint.infty} := by
    intro x hx
    rw [Finsupp.mem_support_iff] at hx
    induction x using OnePoint.rec with
    | infty => simp
    | coe z =>
      by_cases hz : z = a
      · simp [hz]
      · exact absurd (hoff z hz) hx
  have hdeg := degree_principalDivisor (X := OnePoint ℂ) h
  rw [WeilDivisor.degree_apply, Finset.sum_subset hsupp (fun x _ hx ↦ by
    simpa using hx), Finset.sum_pair (OnePoint.coe_ne_infty a), hinf] at hdeg
  have ha : principalDivisor (OnePoint ℂ) h a = 1 := by omega
  refine Finsupp.ext fun x ↦ ?_
  induction x using OnePoint.rec with
  | infty =>
    rw [hinf]
    simp [pt, Finsupp.single_apply, (OnePoint.coe_ne_infty a)]
  | coe z =>
    by_cases hz : z = a
    · subst hz; rw [ha]; simp [pt, Finsupp.single_apply, (OnePoint.coe_ne_infty z).symm]
    · rw [hoff z hz]
      simp [pt, Finsupp.single_apply, (OnePoint.coe_ne_infty z).symm, Ne.symm hz,
        OnePoint.coe_injective.ne_iff]

/-- `L(A) ≅ L(B)` as complex vector spaces. -/
def REq (A B : WeilDivisor (OnePoint ℂ)) : Prop :=
  Nonempty (rrSpace (OnePoint ℂ) A ≃ₗ[ℂ] rrSpace (OnePoint ℂ) B)

theorem REq.of_eq {A B : WeilDivisor (OnePoint ℂ)} (h : A = B) : REq A B :=
  ⟨LinearEquiv.ofEq _ _ (congrArg _ h)⟩

theorem REq.trans {A B C : WeilDivisor (OnePoint ℂ)} (h₁ : REq A B) (h₂ : REq B C) : REq A C :=
  ⟨h₁.some.trans h₂.some⟩

theorem REq.symm {A B : WeilDivisor (OnePoint ℂ)} (h : REq A B) : REq B A := ⟨h.some.symm⟩

theorem REq.ell_eq {A B : WeilDivisor (OnePoint ℂ)} (h : REq A B) : ell (OnePoint ℂ) A = ell (OnePoint ℂ) B :=
  h.some.finrank_eq

/-- Moving one point to `∞`: `L(D) ≅ L(D - [a] + [∞])`. -/
theorem req_sub_pt_add_infty (a : ℂ) (D : WeilDivisor (OnePoint ℂ)) :
    REq D (D - pt (a : OnePoint ℂ) + pt OnePoint.infty) := by
  refine (show REq _ _ from ⟨rrSpaceEquivMul (coordinate_sub_ne_zero a) D⟩).trans (REq.of_eq ?_)
  rw [principalDivisor_coordinate_sub]
  abel

/-- `L(D + b [a]) ≅ L(D + b [∞])` for every point `a` and `b ∈ ℤ`. -/
theorem req_add_zsmul_pt (a : OnePoint ℂ) (b : ℤ) (D : WeilDivisor (OnePoint ℂ)) :
    REq (D + b • pt a) (D + b • pt OnePoint.infty) := by
  induction a using OnePoint.rec with
  | infty => exact REq.of_eq rfl
  | coe a =>
    induction b using Int.induction_on generalizing D with
    | zero => exact REq.of_eq (by simp)
    | succ n ih =>
      refine (req_sub_pt_add_infty a _).trans ((REq.of_eq ?_).trans ((ih (D + pt OnePoint.infty)).trans
        (REq.of_eq ?_)))
      · rw [add_smul, one_smul]; abel
      · rw [add_smul, one_smul]; abel
    | pred n ih =>
      refine (REq.of_eq ?_).trans ((req_sub_pt_add_infty a
        (D - pt OnePoint.infty + (-(n : ℤ)) • pt (a : OnePoint ℂ))).symm.trans
        ((ih (D - pt OnePoint.infty)).trans (REq.of_eq ?_)))
      · rw [sub_smul, one_smul]; abel
      · rw [sub_smul, one_smul]; abel

/-- **Every divisor on the sphere is equivalent to `(deg D)[∞]`**: `L(D + E) ≅ L((deg D)[∞] + E)`. -/
theorem req_add_degree_smul (D : WeilDivisor (OnePoint ℂ)) :
    ∀ E, REq (D + E) (WeilDivisor.degree D • pt OnePoint.infty + E) := by
  induction D using Finsupp.induction with
  | zero => intro E; exact REq.of_eq (by simp)
  | single_add a b D _ _ ih =>
    intro E
    have hs : Finsupp.single a b = b • pt a := by simp [pt]
    refine (REq.of_eq ?_).trans ((ih (Finsupp.single a b + E)).trans ((REq.of_eq ?_).trans
      ((req_add_zsmul_pt a b (WeilDivisor.degree D • pt OnePoint.infty + E)).trans (REq.of_eq ?_))))
    · abel
    · rw [hs]; abel
    · have hd : WeilDivisor.degree (Finsupp.single a b) = b := by
        simp [WeilDivisor.degree, Finsupp.degree_single]
      rw [map_add, hd, add_smul]
      abel

theorem req_degree_smul (D : WeilDivisor (OnePoint ℂ)) :
    REq D (WeilDivisor.degree D • pt OnePoint.infty) := by
  simpa using req_add_degree_smul D 0

theorem pt_infty_eq_divisorInfty : pt OnePoint.infty = divisorInfty := rfl

theorem rrSpace_mono {D₁ D₂ : WeilDivisor (OnePoint ℂ)} (h : D₁ ≤ D₂) :
    rrSpace (OnePoint ℂ) D₁ ≤ rrSpace (OnePoint ℂ) D₂ := by
  intro f hf x
  exact le_trans (by exact_mod_cast (neg_le_neg (h x))) (hf x)

/-- `ℓ(D) = max(0, deg D + 1)` on the Riemann sphere. -/
theorem ell_sphere (D : WeilDivisor (OnePoint ℂ)) :
    (ell (OnePoint ℂ) D : ℤ) = if 0 ≤ WeilDivisor.degree D then WeilDivisor.degree D + 1 else 0 := by
  rw [(req_degree_smul D).ell_eq]
  split_ifs with hd
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hd
    rw [hn, natCast_zsmul, pt_infty_eq_divisorInfty, ell_nsmul_divisorInfty]
    push_cast; rfl
  · rw [ell_eq_zero_of_degree_neg]
    · rfl
    · rw [map_zsmul, pt_infty_eq_divisorInfty, degree_divisorInfty, smul_eq_mul, mul_one]
      omega

/-- `L(D)` is finite-dimensional on the sphere. -/
theorem finiteDimensional_rrSpace_sphere (D : WeilDivisor (OnePoint ℂ)) :
    FiniteDimensional ℂ (rrSpace (OnePoint ℂ) D) := by
  have hfin : ∀ n : ℕ, FiniteDimensional ℂ (rrSpace (OnePoint ℂ) (n • divisorInfty)) := fun n ↦
    FiniteDimensional.of_finrank_pos (by
      have := ell_nsmul_divisorInfty n
      unfold ell at this
      omega)
  obtain ⟨e⟩ := req_degree_smul D
  suffices h : FiniteDimensional ℂ (rrSpace (OnePoint ℂ) (WeilDivisor.degree D • pt OnePoint.infty)) from
    Module.Finite.equiv e.symm
  rcases le_or_gt 0 (WeilDivisor.degree D) with hd | hd
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hd
    rw [hn, natCast_zsmul, pt_infty_eq_divisorInfty]
    exact hfin n
  · have hle : WeilDivisor.degree D • pt OnePoint.infty ≤ (0 : ℕ) • divisorInfty := by
      intro x
      simp only [zero_smul, Finsupp.coe_zero, Pi.zero_apply, Finsupp.smul_apply, smul_eq_mul, pt]
      classical
      rw [Finsupp.single_apply]
      split_ifs <;> omega
    have := hfin 0
    exact Submodule.finiteDimensional_of_le (rrSpace_mono hle)

/-- Every canonical divisor of the sphere has degree `-2`. -/
theorem degree_divisor_sphere {ω : MeromorphicDifferential (OnePoint ℂ)} (hω : ¬ ω.IsZero) :
    WeilDivisor.degree ω.divisor = -2 := by
  have hdz : ¬ (differential (coordinate : MeromorphicFunction (OnePoint ℂ))).IsZero := by
    intro h
    have := h ((0 : ℂ) : OnePoint ℂ)
    rw [ord_differential_coordinate_coe] at this
    exact absurd this (by simp)
  rw [RS.degree_divisor_eq_of_not_isZero hω hdz, divisor_differential_coordinate, map_zsmul,
    degree_divisorInfty]
  rfl

/-- **Milne, Exercise 1.24.** The Riemann–Roch theorem holds for the Riemann sphere, with `g = 0`. -/
@[kb "milne2017mf" "Exercise 1.24: Riemann-Roch for the Riemann sphere, pdf p. 22"]
theorem riemannRoch_sphere : RiemannRochStatement (OnePoint ℂ) where
  finiteDimensional := finiteDimensional_rrSpace_sphere
  exists_genus := ⟨0, fun ω hω D ↦ by
    rw [ell_sphere, ell_sphere, map_sub, degree_divisor_sphere hω]
    split_ifs <;> omega⟩

end Sphere

end ModularFormsKB.Milne
