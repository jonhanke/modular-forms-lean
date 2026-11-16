import ModularFormsKB.Miyake.Sec4_9.Spherical.CuspEquivariant
import ModularFormsKB.Miyake.Sec4_9.Spherical.UnaryModular

/-!
# The Serre–Stark cusp criterion in weight 1/2: one direction

Loose end LE-MF-0239 (`UnaryThetaCuspCriterion`).

**Theorem** (`unaryThetaOf_mem_cusp_of_not_totallyEven`). Let `(Φ, t) ∈ Ω₀(4N, χ)` and let `ψ = Φ*` be the primitive
character, of conductor `r`. If `ψ` is not totally even, then `θ_{ψ,t} ∈ S_{1/2}(4N, χ)`.

**Proof.** `θ_{ψ,t}` is, up to a constant, `∑_{b mod r} ψ(b) θ_{√(2t)b + L}` for the lattice `L = √(2t) r ℤ`
(`unaryThetaOf_eq`), whose discriminant group is cyclic of order `2tr²`.
1. Since `ψ` is not totally even there is an integer `u` with `u² ≡ 1 mod 4tr²` and `ψ(u) ≠ 1`
   (`exists_sq_modEq_one_of_not_isTotallyEven`, by the Chinese remainder theorem: `u ≡ -1` at the prime `p` where the
   local component of `ψ` is odd, `u ≡ 1` elsewhere).
2. Multiplication by `u` is an isometry of the discriminant form of `L` (`isDiscIsom_twistMul`), since
   `u² ≡ 1 mod 4tr²`.
3. It permutes the cosets `√(2t)b + L` by `b ↦ ub`, and the coefficient `ψ(b)` picks up `ψ(u) ≠ 1`. The equivariant
   transformation law (`isZeroAtImInfty_absSlash_sum_thetaSph`, `CuspEquivariant.lean`) gives a vanishing constant
   term at every cusp.

The other direction (a totally even `ψ` gives a nonzero constant term at some cusp) is
`unaryThetaOf_not_mem_cusp_of_totallyEven` (`UnaryCuspConverse.lean`), which proves `UnaryThetaCuspCriterion`.
-/

open Complex Module Filter
open scoped Real RealInnerProductSpace UpperHalfPlane MatrixGroups

set_option linter.unusedSectionVars false

namespace ModularFormsKB.HalfIntegral

open ModularFormsKB.Miyake.Sec4_9

/-! ### Step 1: a unit `u` with `u² ≡ 1` and `ψ(u) ≠ 1` -/

/-- **A square root of `1` moved by `ψ`.** If `ψ` (modulo `r`) is not totally even and `r ∣ M ≠ 0`, there is an integer
`u` with `M ∣ u² - 1` and `ψ(u) ≠ 1`. -/
theorem exists_sq_modEq_one_of_not_isTotallyEven {r : ℕ} (ψ : DirichletCharacter ℂ r)
    (hψ : ¬ IsTotallyEven ψ) {M : ℕ} (hM : M ≠ 0) (hrM : r ∣ M) :
    ∃ u : ℤ, (M : ℤ) ∣ u ^ 2 - 1 ∧ ψ (u : ZMod r) ≠ 1 := by
  unfold IsTotallyEven at hψ
  push_neg at hψ
  obtain ⟨p, hp, a, ha1, ha2, hψa⟩ := hψ
  have hr : r ≠ 0 := by rintro rfl; exact hM (Nat.eq_zero_of_zero_dvd hrM)
  set P := p ^ M.factorization p
  set Q := M / p ^ M.factorization p
  have hcop : Nat.Coprime P Q := (Nat.coprime_ordCompl hp hM).pow_left _
  have hPQ : P * Q = M := Nat.ordProj_mul_ordCompl_eq_self M p
  have hP1 : 1 ≤ P := Nat.one_le_pow _ _ hp.pos
  obtain ⟨k, hkP, hkQ⟩ := Nat.chineseRemainder hcop (P - 1) 1
  refine ⟨k, ?_, ?_⟩
  · -- `P ∣ u + 1` and `Q ∣ u - 1`
    have h1 : (P : ℤ) ∣ (k : ℤ) + 1 := by
      have h' : (k : ℤ) ≡ ((P - 1 : ℕ) : ℤ) [ZMOD P] := Int.natCast_modEq_iff.mpr hkP
      rw [Nat.cast_sub hP1, Nat.cast_one] at h'
      have hd := Int.ModEq.dvd h'.symm
      have e : (k : ℤ) + 1 = ((k : ℤ) - (P - 1)) + P := by ring
      rw [e]
      exact dvd_add hd (dvd_refl _)
    have h2 : (Q : ℤ) ∣ (k : ℤ) - 1 := by
      have h' : (k : ℤ) ≡ ((1 : ℕ) : ℤ) [ZMOD Q] := Int.natCast_modEq_iff.mpr hkQ
      exact (Int.ModEq.dvd h'.symm)
    have : ((P * Q : ℕ) : ℤ) ∣ ((k : ℤ) + 1) * ((k : ℤ) - 1) := by
      push_cast
      exact Int.mul_dvd_mul h1 h2
    rw [hPQ] at this
    convert this using 1
    ring
  · -- `u ≡ a mod r`
    intro hk
    apply hψa
    set e := r.factorization p
    have hle : e ≤ M.factorization p := (Nat.factorization_le_iff_dvd hr hM).mpr hrM p
    have hpe : p ^ e ∣ P := pow_dvd_pow p hle
    have hq : r / p ^ e ∣ Q := Nat.ordCompl_dvd_ordCompl_of_dvd hrM p
    have hk1 : (k : ℤ) ≡ a [ZMOD ((p ^ e : ℕ) : ℤ)] := by
      have h' : (k : ℤ) ≡ ((P - 1 : ℕ) : ℤ) [ZMOD P] := Int.natCast_modEq_iff.mpr hkP
      rw [Nat.cast_sub hP1, Nat.cast_one] at h'
      have h'' : (k : ℤ) ≡ -1 [ZMOD P] := by
        exact h'.trans (Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩)
      exact (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hpe) h'').trans ha1.symm
    have hk2 : (k : ℤ) ≡ a [ZMOD ((r / p ^ e : ℕ) : ℤ)] := by
      have h' : (k : ℤ) ≡ ((1 : ℕ) : ℤ) [ZMOD Q] := Int.natCast_modEq_iff.mpr hkQ
      exact (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hq) (by simpa using h')).trans ha2.symm
    have hcop' : Nat.Coprime (p ^ e) (r / p ^ e) := (Nat.coprime_ordCompl hp hr).pow_left _
    have hmul : (k : ℤ) ≡ a [ZMOD ((p ^ e : ℕ) : ℤ) * ((r / p ^ e : ℕ) : ℤ)] :=
      (Int.modEq_and_modEq_iff_modEq_mul (by simpa only [Int.natAbs_natCast] using hcop')).mp ⟨hk1, hk2⟩
    rw [← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self r p] at hmul
    have hz : ((k : ℤ) : ZMod r) = (a : ZMod r) := (ZMod.intCast_eq_intCast_iff _ _ r).mpr hmul
    rw [← hz]
    exact_mod_cast hk

/-! ### Step 2: multiplication by `u` on the discriminant group of `√(2t) r ℤ` -/

section Lattice

variable {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r)

noncomputable instance : Fintype (ZLattice.DiscriminantGroup (twistLattice ht hr)) :=
  have := (isEven_twistLattice ht hr).isIntegral.finite_discriminantGroup
  Fintype.ofFinite _

/-- A vector `y` of the dual of `√(2t) r ℤ` is `m / (√(2t) r)` with `m ∈ ℤ`; its square norm is `m² / (2tr²)`. -/
theorem twistLattice_dual_eq {y : ℝ} (hy : y ∈ ZLattice.dual (twistLattice ht hr)) :
    ∃ m : ℤ, y * twistGen t r = m := (mem_dual_rankOneLattice _).mp hy

theorem mul_mem_twistLattice_of_dvd {y : ℝ} (hy : y ∈ ZLattice.dual (twistLattice ht hr)) {n : ℤ}
    (hn : (2 * t * r ^ 2 : ℤ) ∣ n) : (n : ℝ) * y ∈ twistLattice ht hr := by
  obtain ⟨m, hm⟩ := twistLattice_dual_eq ht hr hy
  obtain ⟨k, rfl⟩ := hn
  rw [mem_rankOneLattice]
  refine ⟨k * m, ?_⟩
  have hx := twistGen_ne_zero ht hr
  have hsq := twistGen_sq t r
  have hy' : y = m / twistGen t r := by rw [← hm]; field_simp
  rw [hy']
  push_cast
  field_simp
  rw [hsq]
  ring

variable {ht hr}

/-- Multiplication by an integer `u` with `u² ≡ 1 mod 2tr²` is an involution of the discriminant group. -/
theorem twistMul_involutive {u : ℤ} (hu : (2 * t * r ^ 2 : ℤ) ∣ u ^ 2 - 1) :
    Function.Involutive fun x : ZLattice.DiscriminantGroup (twistLattice ht hr) ↦ u • x := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    simp only [← Submodule.Quotient.mk_smul, smul_smul]
    rw [Submodule.Quotient.eq]
    rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
    have h := mul_mem_twistLattice_of_dvd ht hr y.2 hu
    convert h using 1
    simp only [Submodule.coe_sub, Submodule.coe_smul, zsmul_eq_mul]
    push_cast
    ring

/-- The involution `x ↦ u x` of the discriminant group. -/
noncomputable def twistMul (u : ℤ) (hu : (2 * t * r ^ 2 : ℤ) ∣ u ^ 2 - 1) :
    ZLattice.DiscriminantGroup (twistLattice ht hr) ≃ ZLattice.DiscriminantGroup (twistLattice ht hr) :=
  (twistMul_involutive hu).toPerm _

theorem twistMul_apply {u : ℤ} (hu : (2 * t * r ^ 2 : ℤ) ∣ u ^ 2 - 1)
    (x : ZLattice.DiscriminantGroup (twistLattice ht hr)) : twistMul u hu x = u • x := rfl

/-- **Multiplication by `u` is an isometry of the discriminant form** when `u² ≡ 1 mod 4tr²`. -/
theorem isDiscIsom_twistMul {u : ℤ} (hu4 : (4 * t * r ^ 2 : ℤ) ∣ u ^ 2 - 1) :
    IsDiscIsom (isEven_twistLattice ht hr)
      (twistMul u (dvd_trans ⟨2, by ring⟩ hu4)) := by
  have hx := twistGen_ne_zero ht hr
  have hsq := twistGen_sq t r
  obtain ⟨k, hk⟩ := hu4
  have hu' : ((u : ℝ) ^ 2) = 1 + 4 * t * r ^ 2 * k := by
    have : ((u ^ 2 - 1 : ℤ) : ℝ) = ((4 * t * r ^ 2 * k : ℤ) : ℝ) := by rw [hk]
    push_cast at this
    linarith
  refine ⟨fun x ↦ ?_, fun x y ↦ ?_⟩
  · induction x using Submodule.Quotient.induction_on with
    | H y =>
      rw [twistMul_apply, ← Submodule.Quotient.mk_smul, ZLattice.IsEven.discriminantQuadraticChar_mk,
        ZLattice.IsEven.discriminantQuadraticChar_mk, Complex.exp_eq_exp_iff_exists_int]
      obtain ⟨m, hm⟩ := twistLattice_dual_eq ht hr y.2
      have hy' : (y : ℝ) = m / twistGen t r := by rw [← hm]; field_simp
      refine ⟨k * m ^ 2, ?_⟩
      simp only [Submodule.coe_smul, zsmul_eq_mul, Real.norm_eq_abs, sq_abs]
      rw [hy']
      have : ((u * (m / twistGen t r)) ^ 2 : ℝ) = (m / twistGen t r) ^ 2 + 2 * (k * m ^ 2) := by
        rw [mul_pow, hu', div_pow, hsq]
        field_simp
        ring
      rw [this]
      push_cast
      ring
  · induction x using Submodule.Quotient.induction_on with
    | H a =>
    induction y using Submodule.Quotient.induction_on with
    | H b =>
      rw [twistMul_apply, twistMul_apply, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
        ZLattice.IsIntegral.discriminantPairingChar_mk_mk, ZLattice.IsIntegral.discriminantPairingChar_mk_mk,
        Complex.exp_eq_exp_iff_exists_int]
      obtain ⟨m, hm⟩ := twistLattice_dual_eq ht hr a.2
      obtain ⟨m', hm'⟩ := twistLattice_dual_eq ht hr b.2
      have ha' : (a : ℝ) = m / twistGen t r := by rw [← hm]; field_simp
      have hb' : (b : ℝ) = m' / twistGen t r := by rw [← hm']; field_simp
      refine ⟨2 * k * m * m', ?_⟩
      simp only [Submodule.coe_smul, zsmul_eq_mul, real_inner_eq_re_inner, RCLike.inner_apply,
        conj_trivial]
      rw [ha', hb']
      have : (u * (m / twistGen t r) * (u * (m' / twistGen t r)) : ℝ) =
          m / twistGen t r * (m' / twistGen t r) + 2 * k * m * m' := by
        rw [show (u * (m / twistGen t r) * (u * (m' / twistGen t r)) : ℝ) =
          (u : ℝ) ^ 2 * (m * m') / twistGen t r ^ 2 by ring, hu', hsq]
        field_simp
        rw [hsq]
        ring
      rw [mul_comm ((u : ℝ) * _), this]
      push_cast
      ring

end Lattice

/-! ### Step 3: the cusp condition -/

/-- The class of the coset vector `√(2t) b` in the discriminant group of `√(2t) r ℤ`. -/
noncomputable def twistClass {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r) (b : ZMod r) :
    ZLattice.DiscriminantGroup (twistLattice ht hr) :=
  Submodule.Quotient.mk ⟨twistVec t b.val, twistVec_mem_dual ht hr b.val⟩

theorem twistVec_sub_mem {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r) {a b : ℤ} (h : (r : ℤ) ∣ a - b) :
    twistVec t a - twistVec t b ∈ twistLattice ht hr := by
  obtain ⟨n, hn⟩ := h
  rw [mem_rankOneLattice]
  refine ⟨n, ?_⟩
  unfold twistVec twistGen
  have : ((a : ℝ) - b) = r * n := by exact_mod_cast hn
  rw [mul_comm (n : ℝ), mul_assoc, ← this]
  ring

theorem thetaSph_twistClass {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r) (ν : ℕ) (b : ZMod r) :
    thetaSph (twistLattice ht hr) ν 1 0 (discRep (twistClass ht hr b)) =
      thetaSph (twistLattice ht hr) ν 1 0 (twistVec t b.val) := by
  unfold thetaSph
  refine thetaW_eq_of_sub_mem _ _ ?_
  have h := mk_discRep (twistClass ht hr b)
  nth_rewrite 2 [twistClass] at h
  rw [Submodule.Quotient.eq] at h
  simpa [discRep, Submodule.submoduleOf] using h

theorem twistClass_mul {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r) [NeZero r] {u : ℤ}
    (hu : (2 * t * r ^ 2 : ℤ) ∣ u ^ 2 - 1) (b : ZMod r) :
    twistClass ht hr ((u : ZMod r) * b) = twistMul u hu (twistClass ht hr b) := by
  rw [twistMul_apply, twistClass, twistClass, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
    Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
  have h : (r : ℤ) ∣ (((u : ZMod r) * b).val : ℤ) - u * (b.val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  have h' := twistVec_sub_mem ht hr h
  convert h' using 1
  simp only [Submodule.coe_sub, Submodule.coe_smul, zsmul_eq_mul, twistVec]
  push_cast
  ring

/-- A sum over `Finset.range r` as a sum over `ZMod r`. -/
theorem sum_range_eq_sum_zmod_val {r : ℕ} [NeZero r] (g : ℕ → ℂ) :
    ∑ a ∈ Finset.range r, g a = ∑ b : ZMod r, g b.val := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by have := NeZero.ne r; omega⟩
  exact (Fin.sum_univ_eq_sum_range g (n + 1)).symm

/-- The unary theta series (`ν = 0`) as a sum over the classes `√(2t) b`, `b mod r`. -/
theorem thetaLat_eq_sum_twistClass {r : ℕ} [NeZero r] (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t)
    (hr : 1 ≤ r) (hpar : charParity ψ = 0) :
    thetaLat ψ ht hr = fun τ ↦ ∑ b : ZMod r, ψ⁻¹ b *
      thetaSph (twistLattice ht hr) 0 1 0 (discRep (twistClass ht hr b)) τ := by
  funext τ
  rw [thetaLat, sum_range_eq_sum_zmod_val (fun a ↦ ψ⁻¹ (a : ZMod r) *
    thetaSph (twistLattice ht hr) (charParity ψ) 1 0 (twistVec t a) τ)]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [thetaSph_twistClass, hpar, ZMod.natCast_zmod_val]

/-- **`θ_{ψ,t}` vanishes at every cusp when `ψ` is not totally even** (weight `1/2`): the lattice form. -/
theorem isZeroAtImInfty_absSlash_thetaLat {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t)
    (hr : 1 ≤ r) (hpar : charParity ψ = 0) {u : ℤ} (hu4 : (4 * t * r ^ 2 : ℤ) ∣ u ^ 2 - 1)
    (hψu : ψ⁻¹ (u : ZMod r) ≠ 1) (A : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty (absSlash ((0 : ℕ) + finrank ℝ ℝ / 2) (thetaLat ψ ht hr) A) := by
  have : NeZero r := ⟨by omega⟩
  have hu : (2 * t * r ^ 2 : ℤ) ∣ u ^ 2 - 1 := dvd_trans ⟨2, by ring⟩ hu4
  have hur : (u : ZMod r) * (u : ZMod r) = 1 := by
    have h : (r : ℤ) ∣ u ^ 2 - 1 := dvd_trans ⟨4 * t * r, by ring⟩ hu4
    have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr h
    push_cast at h'
    linear_combination h'
  let σ : ZMod r ≃ ZMod r := Function.Involutive.toPerm (fun b ↦ (u : ZMod r) * b)
    (fun b ↦ by simp only [← mul_assoc, hur, one_mul])
  have heq := thetaLat_eq_sum_twistClass ψ ht hr hpar
  rw [heq]
  refine isZeroAtImInfty_absSlash_sum_thetaSph (isEven_twistLattice ht hr) (1 : ℝ) 0 (fun b ↦ ψ⁻¹ b)
    (twistClass ht hr) (twistMul u hu) (isDiscIsom_twistMul hu4) ?_ σ hψu (fun b ↦ ?_) (fun b ↦ ?_) A
  · rw [twistMul_apply, smul_zero]
  · exact twistClass_mul ht hr hu b
  · show ψ⁻¹ ((u : ZMod r) * b) = ψ⁻¹ (u : ZMod r) * ψ⁻¹ b
    exact map_mul _ _ _

/-- **One direction of the Serre–Stark cusp criterion** (Serre–Stark 1977 `serrestark1977`, §3 [unverified]): for `(Φ, t) ∈ Ω₀(4N, χ)` with `Φ*` not totally even, `θ_{Φ*,t}` is a cusp form of weight `1/2`. -/
@[kb "serrestark1977" "§3: theta_{psi,t} in S_{1/2}(4N, chi) when psi is not totally even (proved; no Gauss sum)"]
theorem unaryThetaOf_mem_cusp_of_not_totallyEven {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ (4 * N)}
    {p : DirichletCharacter ℂ (4 * N) × ℕ} (hp : p ∈ unaryIndex 0 N χ)
    (hψ : ¬ IsTotallyEven p.1.primitiveCharacter) :
    unaryThetaOf p ∈ halfIntCuspForms 0 N χ := by
  obtain ⟨h1, h2, -⟩ := unaryThetaOf_mem hp
  obtain ⟨hν, ht, hdvd, -⟩ := hp
  have hr : 1 ≤ p.1.conductor := conductor_pos p.1
  set ψ := p.1.primitiveCharacter
  have hpar : charParity ψ⁻¹ = 0 := by rw [charParity_inv, charParity_primitiveCharacter, hν]
  have hM : 4 * p.2 * p.1.conductor ^ 2 ≠ 0 := by positivity
  obtain ⟨u, hu, hψu⟩ := exists_sq_modEq_one_of_not_isTotallyEven ψ hψ hM ⟨4 * p.2 * p.1.conductor, by ring⟩
  have hu4 : (4 * p.2 * p.1.conductor ^ 2 : ℤ) ∣ u ^ 2 - 1 := by exact_mod_cast hu
  have hψu' : ψ⁻¹⁻¹ (u : ZMod p.1.conductor) ≠ 1 := by rwa [inv_inv]
  refine ⟨h1, h2, fun γ ↦ ?_⟩
  have hz := isZeroAtImInfty_absSlash_thetaLat ψ⁻¹ ht hr hpar hu4 hψu' γ
  set c : ℂ := (((√(2 * p.2) : ℝ) : ℂ) ^ charParity ψ⁻¹)⁻¹
  have hrw : cuspNorm 0 (unaryThetaOf p) γ =
      fun τ ↦ ‖c‖ * absSlash ((0 : ℕ) + finrank ℝ ℝ / 2) (thetaLat ψ⁻¹ ht hr) γ τ := by
    funext τ
    rw [cuspNorm_eq_absSlash', unaryThetaOf_eq p ht]
    simp only [absSlash, norm_mul]
    ring
  rw [hrw]
  have h := (hz : Tendsto _ _ _).const_mul ‖c‖
  rw [mul_zero] at h
  exact h

end ModularFormsKB.HalfIntegral
