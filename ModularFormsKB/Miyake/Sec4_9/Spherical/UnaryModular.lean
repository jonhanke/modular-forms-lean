import ModularFormsKB.Miyake.Sec4_9.Spherical.UnaryLaw
import ModularFormsKB.HalfIntegral.SerreStark

/-!
# The unary theta series are modular forms of half-integral weight

The statement `HalfIntegral.UnaryThetaModular`. For `(Φ, t) ∈ Ω_ν(4N, χ)`
(`HalfIntegral.unaryIndex`), the unary theta series `θ_{Φ*,t}` lies in `M_{ν+1/2}(4N, χ)`
(`unaryThetaOf_mem`), and for `ν = 1` in `S_{3/2}(4N, χ)` (`unaryThetaOf_mem_cusp_of_one`). Both are
proved with no input: the law is `thetaTwist_law` (every character), holomorphy and the cusp
conditions come from the coset decomposition `thetaTwist_eq_sum` and the absolute-slash bounds of
`Spherical/Cusps.lean` in rank one.

Consequently `UnaryThetaModular 1 N χ` is proved (`unaryThetaModular_one`), and
`UnaryThetaModular 0 N χ` is reduced to the Serre–Stark cusp criterion in weight `1/2`
(`UnaryThetaCuspCriterion`, a named input: `θ_{ψ,t}` is a cusp form exactly when `ψ` is not totally
even), `unaryThetaModular_zero_of_cuspCriterion`. Serre–Stark's Theorem A is then conditional on its
spanning half only (`serreStark_basis_of_span`).
-/

open Complex Module
open scoped Real RealInnerProductSpace UpperHalfPlane MatrixGroups Manifold

set_option linter.unusedSectionVars false

namespace ModularFormsKB.HalfIntegral

open ModularFormsKB.Miyake.Sec4_9

theorem mdifferentiable_thetaLat {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t)
    (hr : 1 ≤ r) : MDiff (thetaLat ψ ht hr) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h : ∀ a ∈ Finset.range r, DifferentiableOn ℂ ((fun τ ↦ ψ⁻¹ (a : ZMod r) *
      thetaSph (twistLattice ht hr) (charParity ψ) 1 0 (twistVec t a) τ) ∘
        UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} := fun a _ ↦
    UpperHalfPlane.mdifferentiable_iff.mp
      ((mdifferentiable_thetaW _ (polyBounded_isoForm_pow 1 0 _) _).const_smul (ψ⁻¹ (a : ZMod r)))
  have := DifferentiableOn.sum h
  refine this.congr fun z _ ↦ ?_
  simp [thetaLat, Finset.sum_apply]

/-- The parity of the primitive character inducing `Φ` is that of `Φ`. -/
theorem charParity_primitiveCharacter {M : ℕ} [NeZero M] (Φ : DirichletCharacter ℂ M) :
    charParity Φ.primitiveCharacter = charParity Φ := by
  have h := Φ.primitiveCharacter_apply_of_isCoprime (a := -1) isCoprime_one_left.neg_left
  push_cast at h
  unfold charParity
  rw [h]

theorem conductor_pos {M : ℕ} [NeZero M] (Φ : DirichletCharacter ℂ M) : 1 ≤ Φ.conductor :=
  Nat.pos_of_ne_zero Φ.conductor_ne_zero

/-- Absolute slashes of a finite combination are dominated by the absolute slashes of the terms. -/
theorem absSlash_sum_le {ι : Type*} (s : Finset ι) (c : ι → ℂ) (g : ι → ℍ → ℂ) (w : ℝ)
    (γ : SL(2, ℤ)) (τ : ℍ) :
    absSlash w (fun σ ↦ ∑ i ∈ s, c i * g i σ) γ τ ≤ ∑ i ∈ s, ‖c i‖ * absSlash w (g i) γ τ := by
  unfold absSlash
  dsimp only
  calc _ ≤ ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-w) * ∑ i ∈ s, ‖c i * g i (γ • τ)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [norm_mul]
        ring

/-- The unary theta series as `c⁻¹ thetaLat`. -/
theorem unaryThetaOf_eq {N : ℕ} [NeZero N] (p : DirichletCharacter ℂ (4 * N) × ℕ) (ht : 1 ≤ p.2) :
    unaryThetaOf p = fun τ ↦ (((√(2 * p.2) : ℝ) : ℂ) ^ charParity p.1.primitiveCharacter⁻¹)⁻¹ *
      thetaLat p.1.primitiveCharacter⁻¹ ht (conductor_pos p.1) τ := by
  funext τ
  rw [unaryThetaOf, unaryTheta_eq_thetaTwist, thetaTwist_eq_sum _ ht (conductor_pos p.1)]

/-- The coefficient of the `a`-th coset piece. -/
noncomputable def unaryCoeff {N : ℕ} [NeZero N] (p : DirichletCharacter ℂ (4 * N) × ℕ) (a : ℕ) : ℝ :=
  ‖(((√(2 * p.2) : ℝ) : ℂ) ^ charParity p.1.primitiveCharacter⁻¹)⁻¹ *
    p.1.primitiveCharacter⁻¹⁻¹ (a : ZMod p.1.conductor)‖

/-- The `a`-th coset piece. -/
noncomputable def unaryPiece {N : ℕ} [NeZero N] (p : DirichletCharacter ℂ (4 * N) × ℕ)
    (ht : 1 ≤ p.2) (a : ℕ) : ℍ → ℂ :=
  thetaSph (twistLattice ht (conductor_pos p.1)) (charParity p.1.primitiveCharacter⁻¹) 1 0
    (twistVec p.2 a)

/-- Bounds of the absolute slash of a unary theta series by its coset pieces. -/
theorem absSlash_unaryThetaOf_le {N : ℕ} [NeZero N] (p : DirichletCharacter ℂ (4 * N) × ℕ)
    (ht : 1 ≤ p.2) (w : ℝ) (γ : SL(2, ℤ)) (τ : ℍ) :
    absSlash w (unaryThetaOf p) γ τ ≤ ∑ a ∈ Finset.range p.1.conductor,
      unaryCoeff p a * absSlash w (unaryPiece p ht a) γ τ := by
  rw [unaryThetaOf_eq p ht]
  have h := absSlash_sum_le (Finset.range p.1.conductor)
    (fun a ↦ (((√(2 * p.2) : ℝ) : ℂ) ^ charParity p.1.primitiveCharacter⁻¹)⁻¹ *
      p.1.primitiveCharacter⁻¹⁻¹ (a : ZMod p.1.conductor)) (unaryPiece p ht) w γ τ
  convert h using 3
  · rw [thetaLat, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ ↦ by simp only [unaryPiece]; ring
  · rfl

theorem cuspNorm_eq_absSlash' (k : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    cuspNorm k f γ τ = absSlash ((k : ℝ) + finrank ℝ ℝ / 2) f γ τ := by
  simp only [cuspNorm, absSlash, Module.finrank_self]
  norm_num

theorem isBounded_cuspNorm_unaryThetaOf {N : ℕ} [NeZero N] (p : DirichletCharacter ℂ (4 * N) × ℕ)
    (ht : 1 ≤ p.2) (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty
      (cuspNorm (charParity p.1.primitiveCharacter⁻¹) (unaryThetaOf p) γ) := by
  have hb : ∀ a ∈ Finset.range p.1.conductor, UpperHalfPlane.IsBoundedAtImInfty
      (absSlash ((charParity p.1.primitiveCharacter⁻¹ : ℝ) + finrank ℝ ℝ / 2)
        (unaryPiece p ht a) γ) := fun a _ ↦
    isBoundedAtImInfty_absSlash_thetaSph (isEven_twistLattice ht (conductor_pos p.1))
      (isSphericalDatum_one_zero _) γ (twistVec_mem_dual ht (conductor_pos p.1) a)
  have hsum : UpperHalfPlane.IsBoundedAtImInfty (∑ a ∈ Finset.range p.1.conductor, fun τ ↦
      unaryCoeff p a * absSlash ((charParity p.1.primitiveCharacter⁻¹ : ℝ) + finrank ℝ ℝ / 2)
        (unaryPiece p ht a) γ τ) :=
    Asymptotics.IsBigO.sum (s := Finset.range p.1.conductor)
      (fun a ha ↦ (hb a ha).const_mul_left (unaryCoeff p a))
  refine isBounded_of_le_add (b := fun _ ↦ 0) hsum UpperHalfPlane.zero_form_isBoundedAtImInfty
    (cuspNorm_nonneg _ _ _) fun τ ↦ ?_
  rw [add_zero, cuspNorm_eq_absSlash', Finset.sum_apply]
  exact absSlash_unaryThetaOf_le p ht _ γ τ

theorem isZero_cuspNorm_unaryThetaOf {N : ℕ} [NeZero N] (p : DirichletCharacter ℂ (4 * N) × ℕ)
    (ht : 1 ≤ p.2) (hν : charParity p.1.primitiveCharacter⁻¹ = 1) (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty
      (cuspNorm (charParity p.1.primitiveCharacter⁻¹) (unaryThetaOf p) γ) := by
  have hb : ∀ a ∈ Finset.range p.1.conductor, Filter.Tendsto
      (absSlash ((charParity p.1.primitiveCharacter⁻¹ : ℝ) + finrank ℝ ℝ / 2)
        (unaryPiece p ht a) γ) UpperHalfPlane.atImInfty (nhds 0) := fun a _ ↦
    isZeroAtImInfty_absSlash_thetaSph (isEven_twistLattice ht (conductor_pos p.1)) (by omega)
      (isSphericalDatum_one_zero _) γ (twistVec_mem_dual ht (conductor_pos p.1) a)
  have hsum : Filter.Tendsto (fun τ ↦ ∑ a ∈ Finset.range p.1.conductor,
      unaryCoeff p a * absSlash ((charParity p.1.primitiveCharacter⁻¹ : ℝ) + finrank ℝ ℝ / 2)
        (unaryPiece p ht a) γ τ) UpperHalfPlane.atImInfty (nhds 0) := by
    have := tendsto_finsetSum (Finset.range p.1.conductor) fun a ha ↦
      (hb a ha).const_mul (unaryCoeff p a)
    simpa using this
  refine squeeze_zero (cuspNorm_nonneg _ _ _) (fun τ ↦ ?_) hsum
  rw [cuspNorm_eq_absSlash']
  exact absSlash_unaryThetaOf_le p ht _ γ τ

/-- **Membership of the unary theta series** (the field `mem` of `UnaryThetaModular`, proved). -/
@[kb "serrestark1977" "§3 with Shimura 1973 Prop. 2.2: theta_{psi,t} lies in M_{nu+1/2}(4N, chi) for (psi,t) in Omega_nu(4N,chi) (membership, proved)"]
theorem unaryThetaOf_mem {ν N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ (4 * N)}
    {p : DirichletCharacter ℂ (4 * N) × ℕ} (hp : p ∈ unaryIndex ν N χ) :
    unaryThetaOf p ∈ halfIntModularForms ν N χ := by
  obtain ⟨hν, ht, hdvd, hχ⟩ := hp
  have hr : 1 ≤ p.1.conductor := conductor_pos p.1
  have hpar : charParity p.1.primitiveCharacter⁻¹ = ν := by
    rw [charParity_inv, charParity_primitiveCharacter, hν]
  refine ⟨?_, fun γ hγ τ ↦ ?_, fun γ ↦ ?_⟩
  · rw [unaryThetaOf_eq p ht]
    exact (mdifferentiable_thetaLat _ ht hr).const_smul _
  · have hγ' : γ ∈ CongruenceSubgroup.Gamma0 (4 * p.2 * p.1.conductor ^ 2) := by
      have h := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hγ
      exact CongruenceSubgroup.mem_Gamma0_iff_dvd.mpr
        (dvd_trans (by exact_mod_cast (show 4 * p.2 * p.1.conductor ^ 2 ∣ 4 * N by
          simpa [mul_comm, mul_assoc, mul_left_comm] using hdvd)) h)
    have hγ4 : γ ∈ CongruenceSubgroup.Gamma0 4 := by
      have h := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hγ
      exact CongruenceSubgroup.mem_Gamma0_iff_dvd.mpr (dvd_trans (by exact_mod_cast
        (⟨N, rfl⟩ : (4 : ℕ) ∣ 4 * N)) h)
    have hcop : IsCoprime (γ 1 1) (4 * N : ℕ) := by
      obtain ⟨u, hu⟩ := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hγ
      have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
        have h := γ.det_coe
        rwa [Matrix.det_fin_two] at h
      exact ⟨γ 0 0, -(γ 0 1 * u), by linear_combination hdet + γ 0 1 * hu⟩
    have hlaw := thetaTwist_law p.1.primitiveCharacter⁻¹ hr ht hγ' τ
    rw [hpar, inv_inv] at hlaw
    have hψ : p.1.primitiveCharacter (γ 1 1 : ZMod p.1.conductor) = p.1 (γ 1 1 : ZMod (4 * N)) :=
      p.1.primitiveCharacter_apply_of_isCoprime (by exact_mod_cast hcop)
    rw [hψ] at hlaw
    show unaryTheta p.1.primitiveCharacter p.2 ((γ • τ : ℍ) : ℂ) = _ * _ * unaryTheta _ _ (τ : ℂ)
    rw [unaryTheta_eq_thetaTwist, hlaw, hχ _ (by exact_mod_cast hcop)]
    set X : ℂ := (ZMod.χ₄ (γ 1 1 : ZMod 4) : ℂ)
    set j := thetaMult γ τ
    set D : ℂ := (γ 1 0 : ℂ) * τ + γ 1 1
    have hX : X ^ 2 = 1 := by
      have h2 : (γ 1 1) % 2 = 1 := Int.odd_iff.mp (Gamma0_four_odd hγ4)
      have h := chi4_int_sq h2
      simp only [X]
      exact_mod_cast h
    have hj2 : j ^ 2 = X * D := thetaMult_sq hγ4 τ
    have hD : D ^ ν * j = X ^ ν * j ^ (2 * ν + 1) := by
      have : D = X * j ^ 2 := by rw [hj2, ← mul_assoc, ← sq, hX, one_mul]
      rw [this, mul_pow, ← pow_mul, pow_succ]
      ring
    linear_combination (p.1 (γ 1 1 : ZMod (4 * N)) * (jacobiSym p.2 (γ 1 1).natAbs : ℂ) *
      thetaTwist p.1.primitiveCharacter⁻¹ p.2 τ) * hD
  · have h := isBounded_cuspNorm_unaryThetaOf p ht γ
    rwa [hpar] at h

/-- **For `ν = 1` the unary theta series are cusp forms** (the field `cusp_odd`, proved). -/
@[kb "serrestark1977" "theta_{psi,t} with psi odd lies in S_{3/2}(4N, chi) (proved)"]
theorem unaryThetaOf_mem_cusp_of_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ (4 * N)}
    {p : DirichletCharacter ℂ (4 * N) × ℕ} (hp : p ∈ unaryIndex 1 N χ) :
    unaryThetaOf p ∈ halfIntCuspForms 1 N χ := by
  obtain ⟨h1, h2, -⟩ := unaryThetaOf_mem hp
  have hpar : charParity p.1.primitiveCharacter⁻¹ = 1 := by
    rw [charParity_inv, charParity_primitiveCharacter, hp.1]
  refine ⟨h1, h2, fun γ ↦ ?_⟩
  have h := isZero_cuspNorm_unaryThetaOf p hp.2.1 hpar γ
  rwa [hpar] at h

/-- **The Serre–Stark cusp criterion in weight `1/2`** (Serre–Stark 1977 `serrestark1977`, §3
[unverified]): `θ_{ψ,t}` is a cusp form exactly when `ψ` is not totally even. The remaining input of
`UnaryThetaModular 0 N χ`; it needs the constant terms at every cusp. -/
@[kb "serrestark1977" "§3: theta_{psi,t} in M_{1/2}(4N, chi) is a cusp form iff psi is not totally even [unverified]"]
structure UnaryThetaCuspCriterion (N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop where
  cusp_iff : ∀ p ∈ unaryIndex 0 N χ,
    (unaryThetaOf p ∈ halfIntCuspForms 0 N χ ↔ ¬ IsTotallyEven p.1.primitiveCharacter)

/-- **`UnaryThetaModular 1 N χ` holds** (row 11, weight `3/2`, unconditional). -/
@[kb "serrestark1977" "UnaryThetaModular in weight 3/2 (nu = 1), proved"]
theorem unaryThetaModular_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ (4 * N)) :
    UnaryThetaModular 1 N χ where
  mem _ hp := unaryThetaOf_mem hp
  cusp_iff h := absurd h one_ne_zero
  cusp_odd _ _ hp := unaryThetaOf_mem_cusp_of_one hp

/-- **`UnaryThetaModular 0 N χ` from the Serre–Stark cusp criterion** (row 11, weight `1/2`):
membership is proved; only the cusp criterion is assumed. -/
theorem unaryThetaModular_zero_of_cuspCriterion {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ (4 * N)} (h : UnaryThetaCuspCriterion N χ) :
    UnaryThetaModular 0 N χ where
  mem _ hp := unaryThetaOf_mem hp
  cusp_iff _ := h.cusp_iff
  cusp_odd h := absurd h zero_ne_one

/-- A family of elements of a submodule that is linearly independent and spans it is a basis. -/
private noncomputable def basisOfSpan' {ι : Type*} {V : Submodule ℂ (ℍ → ℂ)} (v : ι → ℍ → ℂ)
    (hv : ∀ i, v i ∈ V) (hli : LinearIndependent ℂ v) (hsp : V ≤ Submodule.span ℂ (Set.range v)) :
    Module.Basis ι ℂ V :=
  Module.Basis.mk (v := fun i ↦ (⟨v i, hv i⟩ : V))
    (LinearIndependent.of_comp V.subtype hli)
    (by
      rintro ⟨f, hf⟩ -
      have h : f ∈ Submodule.map V.subtype
          (Submodule.span ℂ (Set.range fun i ↦ (⟨v i, hv i⟩ : V))) := by
        rw [Submodule.map_span, ← Set.range_comp]
        exact hsp hf
      obtain ⟨w, hw, hwf⟩ := h
      have : w = ⟨f, hf⟩ := Subtype.ext hwf
      rw [← this]
      exact hw)

/-- **Serre–Stark, Theorem A, conditional on spanning only**: the `θ_{ψ,t}`, `(ψ, t) ∈ Ω(4N, χ)`,
form a basis of `M_{1/2}(4N, χ)`; membership (`unaryThetaOf_mem`) and independence are proved. -/
theorem serreStark_basis_of_span {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ (4 * N)}
    (hA : SerreStarkSpan N χ) :
    ∃ b : Module.Basis (unaryIndex 0 N χ) ℂ (halfIntModularForms 0 N χ),
      ∀ p, (b p : ℍ → ℂ) = unaryThetaOf p.1 := by
  have hsp := hA.span
  rw [Set.image_eq_range] at hsp
  exact ⟨basisOfSpan' _ (fun p ↦ unaryThetaOf_mem p.2) (linearIndependent_unaryThetaOf χ _ subset_rfl)
    hsp, fun p ↦ by simp [basisOfSpan']⟩

end ModularFormsKB.HalfIntegral
