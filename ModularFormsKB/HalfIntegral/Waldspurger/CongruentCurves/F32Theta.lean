/-
# $f_{32}$ is a theta series with a spherical weight: `f32Modular`

$f_{32} = \frac{1+i}{2}\,\theta_{\gamma+L}(\cdot\,; x + iy)$ for the lattice $L = 4\mathbb Z \oplus 4\mathbb Z$ (even, level
dividing $32$, discriminant group of order $256$) and the coset vector $\gamma = (1,-1) \in L^\vee$. Indeed, for
$(x, y) \in \gamma + L$ put $a = (x-y)/2$, $c = (x+y)/2$: then $\frac{1+i}{2}(x+iy) = a + ic$,
$x^2 + y^2 = 2(a^2 + c^2)$, and $\gamma + L$ corresponds to $a$ odd, $c$ even, $a + c \equiv 1 \bmod 4$.
The modularity is `IsEvenSph.thetaSphCosetCuspForm` with $\psi = \chi_{-4}$ lifted to level $32$.
-/
import ModularFormsKB.Miyake.Sec4_9.Spherical.Characteristic
import ModularFormsKB.Miyake.Sec4_9.Spherical.RankOne
import ModularFormsKB.Miyake.Sec4_9.Spherical.Odd
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.F32Modular

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
open Complex Module
open scoped Real RealInnerProductSpace
open ModularFormsKB.Miyake.Sec4_9

/-- The plane `ℝ²` with the Euclidean inner product. -/
abbrev E2 := WithLp 2 (ℝ × ℝ)

/-- `4ℤ ⊆ ℝ`. -/
noncomputable abbrev L4 : Submodule ℤ ℝ := twistLattice (t := 2) (r := 2) (by norm_num) (by norm_num)

/-- `4ℤ ⊕ 4ℤ`. -/
noncomputable abbrev L32 : Submodule ℤ E2 := ZLattice.orthSum L4 L4

theorem twistGen_two_two : twistGen 2 2 = 4 := by
  unfold twistGen
  have : √(2 * ((2 : ℕ) : ℝ)) = 2 := by
    rw [show (2 * ((2 : ℕ) : ℝ)) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [this]; norm_num

theorem mem_L4 {y : ℝ} : y ∈ L4 ↔ ∃ m : ℤ, (m : ℝ) * 4 = y := by
  rw [mem_rankOneLattice, twistGen_two_two]

theorem mem_dual_L4 {y : ℝ} : y ∈ ZLattice.dual L4 ↔ ∃ m : ℤ, y * 4 = m := by
  rw [mem_dual_rankOneLattice, twistGen_two_two]

theorem mem_L32 {x : E2} : x ∈ L32 ↔ ∃ m n : ℤ, x.fst = 4 * m ∧ x.snd = 4 * n := by
  rw [ZLattice.mem_orthSum, mem_L4, mem_L4]
  constructor
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩; exact ⟨m, n, by linarith, by linarith⟩
  · rintro ⟨m, n, h1, h2⟩; exact ⟨⟨m, by linarith⟩, ⟨n, by linarith⟩⟩

theorem mem_dual_L32 {x : E2} : x ∈ ZLattice.dual L32 ↔ ∃ m n : ℤ, x.fst * 4 = m ∧ x.snd * 4 = n := by
  rw [ZLattice.dual_orthSum, ZLattice.mem_orthSum, mem_dual_L4, mem_dual_L4]
  constructor
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩; exact ⟨m, n, hm, hn⟩
  · rintro ⟨m, n, h1, h2⟩; exact ⟨⟨m, h1⟩, ⟨n, h2⟩⟩

theorem isEven_L32 : ZLattice.IsEven L32 :=
  ZLattice.isEven_orthSum_iff.mpr ⟨isEven_twistLattice _ _, isEven_twistLattice _ _⟩

theorem level_L32_dvd : ZLattice.level L32 ∣ 32 := by
  rw [ZLattice.level_orthSum]
  exact Nat.lcm_dvd (level_twistLattice_dvd _ _) (level_twistLattice_dvd _ _)

theorem covolume_L32 : ZLattice.covolume L32 = 16 := by
  rw [ZLattice.covolume_orthSum, covolume_rankOneLattice, twistGen_two_two]; norm_num

theorem card_disc_L32 : Nat.card (ZLattice.DiscriminantGroup L32) = 256 := by
  have hcard : (Nat.card (ZLattice.DiscriminantGroup L32) : ℝ) = 256 := by
    rw [← isEven_L32.isIntegral.det_eq_card_discriminantGroup, ZLattice.det_def, covolume_L32]
    norm_num
  exact_mod_cast hcard

theorem finrank_E2 : finrank ℝ E2 = 2 * 1 := finrank_twist₂


/-! ### The datum -/

/-- `u = (1, 0)`. -/
noncomputable def u1 : E2 := WithLp.toLp 2 ((1 : ℝ), (0 : ℝ))
/-- `w = (0, 1)`. -/
noncomputable def w1 : E2 := WithLp.toLp 2 ((0 : ℝ), (1 : ℝ))
/-- `γ = (1, -1)`. -/
noncomputable def γ32 : E2 := WithLp.toLp 2 ((1 : ℝ), (-1 : ℝ))

theorem isoForm_u1_w1 (x : E2) : isoForm u1 w1 x = (x.fst : ℂ) + I * x.snd := by
  simp [isoForm, u1, w1, WithLp.prod_inner_apply]

theorem isSph_u1_w1 : IsSphericalDatum 1 u1 w1 := Or.inl le_rfl

theorem γ32_mem : γ32 ∈ ZLattice.dual L32 :=
  mem_dual_L32.mpr ⟨4, -4, by simp [γ32], by simp [γ32]⟩

theorem γ32_norm : ∃ m : ℤ, ‖γ32‖ ^ 2 = 2 * m :=
  ⟨1, by rw [γ32, WithLp.prod_norm_sq_eq_of_L2]; simp; norm_num⟩

/-- `χ₋₄` lifted to level `32`. -/
noncomputable def ψ32 : DirichletCharacter ℂ 32 :=
  DirichletCharacter.changeLevel (by norm_num : 4 ∣ 32) chi4C

theorem odd_of_isCoprime_32 {d : ℤ} (hd : IsCoprime d 32) : d % 2 = 1 := by
  by_contra h
  obtain ⟨a, b, hab⟩ := hd
  have h2 : (2 : ℤ) ∣ d := by omega
  have h3 : (2 : ℤ) ∣ a * d + b * 32 :=
    dvd_add (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right (by norm_num) _)
  rw [hab] at h3
  omega

theorem psi32_apply {d : ℤ} (hd : IsCoprime d 32) :
    ψ32 (d : ZMod 32) = ((ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ) := by
  have hd' : IsCoprime d ((32 : ℕ) : ℤ) := by exact_mod_cast hd
  rw [ψ32, DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hd']
  simp [chi4C, MulChar.ringHomComp_apply]

theorem psi32_neg_one : ψ32 (-1) = (-1) ^ 1 := by
  have h := psi32_apply (d := -1) (isCoprime_one_left.neg_left)
  have e : ((-1 : ℤ) : ZMod 32) = -1 := by simp
  rw [e] at h
  rw [h, ZMod.χ₄_int_eq_if_mod_four]; norm_num

theorem theta_coset_eq {x y : E2} (h : x - y ∈ L32) (ν : ℕ) :
    thetaSph L32 ν u1 w1 x = thetaSph L32 ν u1 w1 y :=
  by unfold thetaSph; exact thetaW_eq_of_sub_mem _ _ h

theorem theta_smul_coprime (a : ℕ) (ha : a.Coprime 32) :
    thetaSph L32 1 u1 w1 ((a : ℝ) • γ32) = ψ32 a • thetaSph L32 1 u1 w1 γ32 := by
  have hc : IsCoprime (a : ℤ) 32 := by
    have := Nat.isCoprime_iff_coprime.mpr ha
    exact_mod_cast this
  have hodd := odd_of_isCoprime_32 hc
  have hp := psi32_apply hc
  rw [Int.cast_natCast] at hp
  rw [hp]
  have h4 : (a : ℤ) % 4 = 1 ∨ (a : ℤ) % 4 = 3 := by omega
  have hχ := ZMod.χ₄_int_eq_if_mod_four (a : ℤ)
  rcases h4 with h4 | h4
  · obtain ⟨q, hq⟩ : ∃ q : ℤ, (a : ℤ) = 4 * q + 1 := ⟨(a : ℤ) / 4, by omega⟩
    have hqr : (a : ℝ) = 4 * q + 1 := by exact_mod_cast hq
    have hmem : (a : ℝ) • γ32 - γ32 ∈ L32 :=
      mem_L32.mpr ⟨q, -q, by simp [γ32, hqr], by simp [γ32, hqr]⟩
    rw [theta_coset_eq hmem]
    have : (ZMod.χ₄ ((a : ℤ) : ZMod 4) : ℤ) = 1 := by
      rw [hχ]; simp [h4]; omega
    rw [this]; simp
  · obtain ⟨q, hq⟩ : ∃ q : ℤ, (a : ℤ) = 4 * q + 3 := ⟨(a : ℤ) / 4, by omega⟩
    have hqr : (a : ℝ) = 4 * q + 3 := by exact_mod_cast hq
    have hmem : (a : ℝ) • γ32 - (-γ32) ∈ L32 :=
      mem_L32.mpr ⟨q + 1, -(q + 1), by simp [γ32, hqr]; ring, by simp [γ32, hqr]; ring⟩
    rw [theta_coset_eq hmem]
    have : (ZMod.χ₄ ((a : ℤ) : ZMod 4) : ℤ) = -1 := by
      rw [hχ]; simp; omega
    rw [this]
    funext τ
    rw [thetaSph_neg]
    simp


theorem kron_L32 (hE : Even (finrank ℝ E2)) {n : ℕ} (hn : IsCoprime (n : ℤ) 32) :
    isEven_L32.thetaCharacter hE (n : ℤ) = ((ZMod.χ₄ ((n : ℤ) : ZMod 4) : ℤ) : ℂ) := by
  have hnl : IsCoprime (n : ℤ) (ZLattice.level L32) :=
    hn.of_isCoprime_of_dvd_right (by exact_mod_cast level_L32_dvd)
  have hodd : Odd n := by
    have := odd_of_isCoprime_32 hn
    rw [← Int.odd_natCast, Int.odd_iff]; exact this
  rw [ZLattice.IsEven.thetaCharacter_intCast isEven_L32 hE hnl,
    TauCeti.kroneckerSym_eq_jacobiSym _ hodd,
    ZLattice.signedDiscr_of_finrank_eq L32 finrank_E2, card_disc_L32]
  have e : ((-1 : ℤ) ^ 1 * ((256 : ℕ) : ℤ)) = (-1) * 16 ^ 2 := by norm_num
  rw [e, jacobiSym.mul_left, jacobiSym.at_neg_one hodd]
  have hg : (16 : ℤ).gcd n = 1 := by
    rw [Int.gcd_comm]
    exact Int.isCoprime_iff_gcd_eq_one.mp (hn.of_isCoprime_of_dvd_right (by norm_num))
  rw [jacobiSym.sq_one' hg]
  simp

theorem htriv32 (hE : Even (finrank ℝ E2)) (d : ℤ) (hd : IsCoprime d 32) :
    ((DirichletCharacter.changeLevel level_L32_dvd (isEven_L32.thetaCharacter hE)) * ψ32⁻¹)
      (d : ZMod 32) = 1 := by
  set n : ℕ := (d % 32).toNat with hn
  have hd0 : 0 ≤ d % 32 := Int.emod_nonneg _ (by norm_num)
  have hnd : (n : ℤ) = d % 32 := by rw [hn]; exact Int.toNat_of_nonneg hd0
  have hcast : (d : ZMod 32) = ((n : ℤ) : ZMod 32) := by
    rw [hnd, ← ZMod.intCast_mod d 32]; norm_num
  have hcop : IsCoprime (n : ℤ) 32 := by
    rw [hnd, Int.emod_def]
    have : IsCoprime (d - 32 * (d / 32)) 32 := by
      have := hd.add_mul_left_left (-(d / 32))
      convert this using 1; ring
    exact this
  rw [hcast, MulChar.mul_apply, MulChar.inv_apply_eq_inv',
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ (by exact_mod_cast hcop), kron_L32 hE hcop,
    psi32_apply hcop]
  have hχ := ZMod.χ₄_int_eq_if_mod_four (n : ℤ)
  have := odd_of_isCoprime_32 hcop
  have h4 : (n : ℤ) % 4 = 1 ∨ (n : ℤ) % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · have hv : (ZMod.χ₄ ((n : ℤ) : ZMod 4) : ℤ) = 1 := by rw [hχ]; simp [h4]; omega
    rw [hv]; simp
  · have hv : (ZMod.χ₄ ((n : ℤ) : ZMod 4) : ℤ) = -1 := by rw [hχ]; simp; omega
    rw [hv]; simp


open CongruenceSubgroup in
/-- The cusp form `θ_{γ+L}(·; x + iy)` of weight `2` on `Γ₀(32)`. -/
noncomputable def theta32 :
    CuspForm ((Gamma0 32).map (Matrix.SpecialLinearGroup.mapGL ℝ)) (1 + 1 : ℕ) :=
  IsEvenSph.thetaSphCosetCuspForm (L := L32) isEven_L32 finrank_E2 (ν := 1) le_rfl isSph_u1_w1
    level_L32_dvd γ32_mem γ32_norm ψ32 theta_smul_coprime psi32_neg_one
    (fun d hd ↦ htriv32 _ d hd)

theorem theta32_apply : ⇑theta32 = thetaSph L32 1 u1 w1 γ32 := rfl


/-! ### The q-expansion -/

theorem norm_sq_E2 (x : E2) : ‖x‖ ^ 2 = x.fst ^ 2 + x.snd ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]; simp [Real.norm_eq_abs, sq_abs]

/-- The primary-type residue classes `a` odd, `c` even, `a + c ≡ 1 mod 4`. -/
def Sset : Set (ℤ × ℤ) := {p | p.1 % 2 = 1 ∧ p.2 % 2 = 0 ∧ (p.1 + p.2) % 4 = 1}

/-- The term `(a + ic) e(2 π i (a² + c²) τ)` on `Sset`. -/
noncomputable def Gterm (τ : UpperHalfPlane) : ℤ × ℤ → ℂ :=
  Sset.indicator fun p ↦ ((p.1 : ℂ) + I * p.2) * cexp (2 * π * I * ((p.1 ^ 2 + p.2 ^ 2 : ℤ) : ℂ) * τ)

/-- `(m, n) ↦ (1 + 2m - 2n, 2m + 2n)`. -/
def gmap (p : ℤ × ℤ) : ℤ × ℤ := (1 + 2 * p.1 - 2 * p.2, 2 * p.1 + 2 * p.2)

theorem gmap_mem (p : ℤ × ℤ) : gmap p ∈ Sset := by
  simp only [gmap, Sset, Set.mem_ofPred_eq]; omega

theorem gmap_injective : Function.Injective gmap := by
  intro p q h
  simp only [gmap, Prod.mk.injEq] at h
  ext <;> omega

theorem exists_gmap {p : ℤ × ℤ} (hp : p ∈ Sset) : ∃ q, gmap q = p := by
  simp only [Sset, Set.mem_ofPred_eq] at hp
  refine ⟨((p.1 + p.2 - 1) / 4, (p.2 - p.1 + 1) / 4), ?_⟩
  simp only [gmap]
  ext <;> simp only <;> omega

/-- The parametrisation `ℤ² → 4ℤ ⊕ 4ℤ`. -/
noncomputable def jL (p : ℤ × ℤ) : L32 :=
  ⟨WithLp.toLp 2 ((4 * p.1 : ℝ), (4 * p.2 : ℝ)), mem_L32.mpr ⟨p.1, p.2, by simp, by simp⟩⟩

theorem jL_bijective : Function.Bijective jL := by
  constructor
  · intro p q h
    have h1 := congrArg (fun v : L32 ↦ (v : E2).fst) h
    have h2 := congrArg (fun v : L32 ↦ (v : E2).snd) h
    simp [jL] at h1 h2
    ext <;> assumption_mod_cast
  · intro v
    obtain ⟨m, n, h1, h2⟩ := mem_L32.mp v.2
    refine ⟨(m, n), ?_⟩
    apply Subtype.ext
    apply WithLp.ofLp_injective
    ext
    · simpa [jL] using h1.symm
    · simpa [jL] using h2.symm

theorem alg_aux (m n : ℤ) :
    (1 + I) / 2 * (((1 + 4 * m : ℝ) : ℂ) + I * ((-1 + 4 * n : ℝ) : ℂ)) =
      ((1 + 2 * m - 2 * n : ℤ) : ℂ) + I * ((2 * m + 2 * n : ℤ) : ℂ) := by
  push_cast
  linear_combination ((-1 + 4 * (n : ℂ)) / 2) * Complex.I_sq

theorem exp_aux (m n : ℤ) (τ : ℂ) :
    cexp (π * I * (((1 + 4 * m : ℝ) ^ 2 + (-1 + 4 * n : ℝ) ^ 2 : ℝ) : ℂ) * τ) =
      cexp (2 * π * I * (((1 + 2 * m - 2 * n) ^ 2 + (2 * m + 2 * n) ^ 2 : ℤ) : ℂ) * τ) := by
  congr 1
  push_cast
  ring

theorem term_jL (τ : UpperHalfPlane) (p : ℤ × ℤ) :
    (1 + I) / 2 * (isoForm u1 w1 (γ32 + (jL p : E2)) ^ 1 *
        cexp (π * I * (‖γ32 + (jL p : E2)‖ ^ 2 : ℝ) * τ)) = Gterm τ (gmap p) := by
  rw [Gterm, Set.indicator_of_mem (gmap_mem p), isoForm_u1_w1, norm_sq_E2]
  have hx : (γ32 + (jL p : E2)).fst = 1 + 4 * p.1 := by simp [γ32, jL]
  have hy : (γ32 + (jL p : E2)).snd = -1 + 4 * p.2 := by simp [γ32, jL]
  rw [hx, hy]
  simp only [gmap]
  rw [pow_one, ← mul_assoc, alg_aux, exp_aux]

theorem hasSum_Gterm (τ : UpperHalfPlane) :
    HasSum (Gterm τ) ((1 + I) / 2 * thetaSph L32 1 u1 w1 γ32 τ) := by
  have hT := (summable_thetaW L32 (polyBounded_isoForm_pow u1 w1 1) γ32 τ).hasSum
  have h1 := (Equiv.ofBijective jL jL_bijective).hasSum_iff.mpr hT
  have h2 := h1.mul_left ((1 + I) / 2)
  have h3 : HasSum (Gterm τ ∘ gmap) ((1 + I) / 2 * thetaSph L32 1 u1 w1 γ32 τ) := by
    convert h2 using 1
    · funext p
      exact (term_jL τ p).symm
    · rfl
  refine (gmap_injective.hasSum_iff (fun x hx ↦ ?_)).mp h3
  rw [Gterm, Set.indicator_of_notMem]
  intro hxS
  exact hx (exists_gmap hxS)


/-- The norm `a² + c²` as a natural number. -/
def Nrm (p : ℤ × ℤ) : ℕ := (p.1 ^ 2 + p.2 ^ 2).toNat

theorem hasSum_fiber {f : ℤ × ℤ → ℂ} {a : ℂ} (h : HasSum f a) (N : ℤ × ℤ → ℕ) :
    HasSum (fun m : ℕ ↦ ∑' b : {x // N x = m}, f b) a := by
  have h1 := (Equiv.sigmaFiberEquiv N).hasSum_iff.mpr h
  exact h1.sigma fun m ↦ (h1.summable.sigma_factor m).hasSum

theorem abs_le_sq (a : ℤ) : |a| ≤ a ^ 2 := by
  rcases eq_or_ne a 0 with rfl | h
  · simp
  · have : 1 ≤ |a| := Int.one_le_abs h
    nlinarith [sq_abs a]

theorem mem_primaryOfNorm_iff (m : ℕ) (p : ℤ × ℤ) : p ∈ primaryOfNorm m ↔ p ∈ Sset ∧ Nrm p = m := by
  simp only [primaryOfNorm, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Sset,
    Set.mem_ofPred_eq, Nrm]
  constructor
  · rintro ⟨-, h1, h2, h3, h4⟩
    exact ⟨⟨h2, h3, h4⟩, by omega⟩
  · rintro ⟨⟨h2, h3, h4⟩, h5⟩
    have h1 : p.1 ^ 2 + p.2 ^ 2 = m := by
      have := sq_nonneg p.1; have := sq_nonneg p.2; omega
    have a1 := abs_le_sq p.1
    have a2 := abs_le_sq p.2
    have b1 := abs_le.mp (show |p.1| ≤ m by nlinarith [sq_nonneg p.2])
    have b2 := abs_le.mp (show |p.2| ≤ m by nlinarith [sq_nonneg p.1])
    exact ⟨⟨⟨b1.1, b1.2⟩, ⟨b2.1, b2.2⟩⟩, h1, h2, h3, h4⟩

theorem sum_snd_primary (m : ℕ) : ∑ x ∈ primaryOfNorm m, x.2 = 0 := by
  have h : ∑ x ∈ primaryOfNorm m, x.2 = ∑ x ∈ primaryOfNorm m, -x.2 := by
    refine Finset.sum_nbij' (fun x ↦ (x.1, -x.2)) (fun x ↦ (x.1, -x.2)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_primaryOfNorm_iff, Sset, Set.mem_ofPred_eq, Nrm] at hx ⊢
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hx
      refine ⟨⟨h1, by omega, by omega⟩, ?_⟩
      simpa using h4
    · intro x hx
      simp only [mem_primaryOfNorm_iff, Sset, Set.mem_ofPred_eq, Nrm] at hx ⊢
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hx
      refine ⟨⟨h1, by omega, by omega⟩, ?_⟩
      simpa using h4
    · intro x _; simp
    · intro x _; simp
    · intro x _; simp
  linarith [Finset.sum_neg_distrib (s := primaryOfNorm m) (f := fun x : ℤ × ℤ ↦ x.2)]

theorem fibre_sum (τ : UpperHalfPlane) (m : ℕ) :
    ∑' b : {x // Nrm x = m}, Gterm τ b = (f32Coeff m : ℂ) * cexp (2 * π * I * m * τ) := by
  have h1 : ∑' b : {x // Nrm x = m}, Gterm τ b =
      ∑' x, {x | Nrm x = m}.indicator (Gterm τ) x := tsum_subtype {x | Nrm x = m} (Gterm τ)
  rw [h1, tsum_eq_sum (s := primaryOfNorm m)]
  · have h2 : ∀ x ∈ primaryOfNorm m, {x | Nrm x = m}.indicator (Gterm τ) x =
        ((x.1 : ℂ) + I * x.2) * cexp (2 * π * I * m * τ) := by
      intro x hx
      obtain ⟨hS, hN⟩ := (mem_primaryOfNorm_iff m x).mp hx
      have hn : x.1 ^ 2 + x.2 ^ 2 = (m : ℤ) := by
        have := sq_nonneg x.1; have := sq_nonneg x.2
        simp only [Nrm] at hN; omega
      rw [Set.indicator_of_mem (by exact hN), Gterm, Set.indicator_of_mem hS, hn]
      simp
    rw [Finset.sum_congr rfl h2, ← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h0 : ∑ x ∈ primaryOfNorm m, (x.2 : ℂ) = 0 := by
      exact_mod_cast congrArg (fun z : ℤ ↦ (z : ℂ)) (sum_snd_primary m)
    rw [h0, mul_zero, add_zero, f32Coeff]
    push_cast
    rfl
  · intro b hb
    by_cases hN : Nrm b = m
    · rw [Set.indicator_of_mem (by exact hN), Gterm, Set.indicator_of_notMem]
      intro hS
      exact hb ((mem_primaryOfNorm_iff m b).mpr ⟨hS, hN⟩)
    · rw [Set.indicator_of_notMem (by exact hN)]

theorem f32_eq_theta (τ : UpperHalfPlane) : f32 τ = (1 + I) / 2 * thetaSph L32 1 u1 w1 γ32 τ := by
  have h := hasSum_fiber (hasSum_Gterm τ) Nrm
  simp_rw [fibre_sum] at h
  exact h.tsum_eq

open CongruenceSubgroup in
/-- **`f₃₂` is a cusp form of weight `2` on `Γ₀(32)`**, as `((1 + i)/2) θ_{γ+L}(·; x + iy)` for the
lattice `L = 4ℤ ⊕ 4ℤ`, `γ = (1, -1)`. -/
theorem f32Modular : F32Modular :=
  ⟨⟨((1 + I) / 2) • theta32, funext fun τ ↦ by
    rw [f32_eq_theta]; rfl⟩⟩

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
