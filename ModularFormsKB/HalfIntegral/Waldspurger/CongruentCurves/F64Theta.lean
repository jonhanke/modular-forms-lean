/-
# $f_{64}$ is a theta series with a spherical weight

$f_{64} = f_{32} \otimes \left(\frac 2\cdot\right) = \sum_m \left(\frac 2m\right) b(m) q^m$ equals
$\frac{1}{\sqrt 2}\,\theta_{\gamma+L}(\cdot\,; x + iy)$ for the lattice $L = 4\sqrt2\,\mathbb Z \oplus 2\sqrt2\,\mathbb Z$
(even, level dividing $64$, discriminant group of order $256$) and the coset vector $\gamma = (\sqrt2, 0) \in L^\vee$.
Indeed $\gamma + L = \{\sqrt2\,(a, 2q) : a \equiv 1 \bmod 4,\ q \in \mathbb Z\}$, the norm is $2(a^2 + 4q^2)$ and the
spherical weight is $\sqrt2\,(a + 2iq)$; the sum of $a$ over the pairs with $a^2 + 4q^2 = m$ is
$\left(\frac 2m\right) b(m)$ (`sum_re_sec64`, file `F64Coeff`). The modularity is
`IsEvenSph.thetaSphCosetCuspForm` with $\psi = \chi_{-4}$ lifted to level $64$.

Proved here: `f64Modular` (a cusp form of weight $2$ on $\Gamma_0(64)$ with the $q$-series `qSeries f64C`),
`coeffGrowth_f64C` and `isCuspFormChar_f64` (membership in Miyake's $S_2(64, 1)$).
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.F64Coeff
import ModularFormsKB.Miyake.Sec4_3.Twist

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open Complex Module MatrixGroups CongruenceSubgroup ModularForm
open scoped Real RealInnerProductSpace
open ModularFormsKB.Miyake.Sec4_9
local notation "ℍ" => UpperHalfPlane

/-- `4√2 ℤ ⊆ ℝ`. -/
noncomputable abbrev La : Submodule ℤ ℝ := twistLattice (t := 1) (r := 4) (by norm_num) (by norm_num)

/-- `2√2 ℤ ⊆ ℝ`. -/
noncomputable abbrev Lb : Submodule ℤ ℝ := twistLattice (t := 1) (r := 2) (by norm_num) (by norm_num)

/-- `4√2 ℤ ⊕ 2√2 ℤ`. -/
noncomputable abbrev L64 : Submodule ℤ E2 := ZLattice.orthSum La Lb

theorem twistGen_one_four : twistGen 1 4 = 4 * √2 := by
  unfold twistGen; norm_num; try ring

theorem twistGen_one_two : twistGen 1 2 = 2 * √2 := by
  unfold twistGen; norm_num; try ring

theorem sqrt_two_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem mem_La {y : ℝ} : y ∈ La ↔ ∃ m : ℤ, (m : ℝ) * (4 * √2) = y := by
  rw [mem_rankOneLattice, twistGen_one_four]

theorem mem_Lb {y : ℝ} : y ∈ Lb ↔ ∃ m : ℤ, (m : ℝ) * (2 * √2) = y := by
  rw [mem_rankOneLattice, twistGen_one_two]

theorem mem_dual_La {y : ℝ} : y ∈ ZLattice.dual La ↔ ∃ m : ℤ, y * (4 * √2) = m := by
  rw [mem_dual_rankOneLattice, twistGen_one_four]

theorem mem_dual_Lb {y : ℝ} : y ∈ ZLattice.dual Lb ↔ ∃ m : ℤ, y * (2 * √2) = m := by
  rw [mem_dual_rankOneLattice, twistGen_one_two]

theorem mem_L64 {x : E2} : x ∈ L64 ↔ ∃ m n : ℤ, x.fst = m * (4 * √2) ∧ x.snd = n * (2 * √2) := by
  rw [ZLattice.mem_orthSum, mem_La, mem_Lb]
  constructor
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩; exact ⟨m, n, hm.symm, hn.symm⟩
  · rintro ⟨m, n, h1, h2⟩; exact ⟨⟨m, h1.symm⟩, ⟨n, h2.symm⟩⟩

theorem mem_dual_L64 {x : E2} :
    x ∈ ZLattice.dual L64 ↔ ∃ m n : ℤ, x.fst * (4 * √2) = m ∧ x.snd * (2 * √2) = n := by
  rw [ZLattice.dual_orthSum, ZLattice.mem_orthSum, mem_dual_La, mem_dual_Lb]
  constructor
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩; exact ⟨m, n, hm, hn⟩
  · rintro ⟨m, n, h1, h2⟩; exact ⟨⟨m, h1⟩, ⟨n, h2⟩⟩

theorem isEven_L64 : ZLattice.IsEven L64 :=
  ZLattice.isEven_orthSum_iff.mpr ⟨isEven_twistLattice _ _, isEven_twistLattice _ _⟩

theorem level_L64_dvd : ZLattice.level L64 ∣ 64 := by
  rw [ZLattice.level_orthSum]
  exact Nat.lcm_dvd ((level_twistLattice_dvd (t := 1) (r := 4) (by norm_num) (by norm_num)).trans
      (by norm_num))
    ((level_twistLattice_dvd (t := 1) (r := 2) (by norm_num) (by norm_num)).trans (by norm_num))

theorem covolume_L64 : ZLattice.covolume L64 = 16 := by
  rw [ZLattice.covolume_orthSum, covolume_rankOneLattice, covolume_rankOneLattice, twistGen_one_four,
    twistGen_one_two, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  nlinarith [sqrt_two_sq]

theorem card_disc_L64 : Nat.card (ZLattice.DiscriminantGroup L64) = 256 := by
  have hcard : (Nat.card (ZLattice.DiscriminantGroup L64) : ℝ) = 256 := by
    rw [← isEven_L64.isIntegral.det_eq_card_discriminantGroup, ZLattice.det_def, covolume_L64]
    norm_num
  exact_mod_cast hcard

/-! ### The datum -/

/-- `γ = (√2, 0)`. -/
noncomputable def γ64 : E2 := WithLp.toLp 2 ((√2 : ℝ), (0 : ℝ))

theorem γ64_mem : γ64 ∈ ZLattice.dual L64 :=
  mem_dual_L64.mpr ⟨8, 0, by
    show √2 * (4 * √2) = ((8 : ℤ) : ℝ)
    push_cast; nlinarith [sqrt_two_sq], by simp [γ64]⟩

theorem γ64_norm : ∃ m : ℤ, ‖γ64‖ ^ 2 = 2 * m :=
  ⟨1, by rw [norm_sq_E2]; simp [γ64]⟩

/-- `χ₋₄` lifted to level `64`. -/
noncomputable def ψ64 : DirichletCharacter ℂ 64 :=
  DirichletCharacter.changeLevel (by norm_num : 4 ∣ 64) chi4C

theorem odd_of_isCoprime_64 {d : ℤ} (hd : IsCoprime d 64) : d % 2 = 1 := by
  by_contra h
  obtain ⟨a, b, hab⟩ := hd
  have h2 : (2 : ℤ) ∣ d := by omega
  have h3 : (2 : ℤ) ∣ a * d + b * 64 :=
    dvd_add (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right (by norm_num) _)
  rw [hab] at h3
  omega

theorem psi64_apply {d : ℤ} (hd : IsCoprime d 64) :
    ψ64 (d : ZMod 64) = ((ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ) := by
  have hd' : IsCoprime d ((64 : ℕ) : ℤ) := by exact_mod_cast hd
  rw [ψ64, DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hd']
  simp [chi4C, MulChar.ringHomComp_apply]

theorem psi64_neg_one : ψ64 (-1) = (-1) ^ 1 := by
  have h := psi64_apply (d := -1) (isCoprime_one_left.neg_left)
  have e : ((-1 : ℤ) : ZMod 64) = -1 := by simp
  rw [e] at h
  rw [h, ZMod.χ₄_int_eq_if_mod_four]; norm_num

theorem theta_coset_eq64 {x y : E2} (h : x - y ∈ L64) (ν : ℕ) :
    thetaSph L64 ν u1 w1 x = thetaSph L64 ν u1 w1 y :=
  by unfold thetaSph; exact thetaW_eq_of_sub_mem _ _ h

theorem theta_smul_coprime64 (a : ℕ) (ha : a.Coprime 64) :
    thetaSph L64 1 u1 w1 ((a : ℝ) • γ64) = ψ64 a • thetaSph L64 1 u1 w1 γ64 := by
  have hc : IsCoprime (a : ℤ) 64 := by
    have := Nat.isCoprime_iff_coprime.mpr ha
    exact_mod_cast this
  have hodd := odd_of_isCoprime_64 hc
  have hp := psi64_apply hc
  rw [Int.cast_natCast] at hp
  rw [hp]
  have h4 : (a : ℤ) % 4 = 1 ∨ (a : ℤ) % 4 = 3 := by omega
  have hχ := ZMod.χ₄_int_eq_if_mod_four (a : ℤ)
  rcases h4 with h4 | h4
  · obtain ⟨q, hq⟩ : ∃ q : ℤ, (a : ℤ) = 4 * q + 1 := ⟨(a : ℤ) / 4, by omega⟩
    have hqr : (a : ℝ) = 4 * q + 1 := by exact_mod_cast hq
    have hmem : (a : ℝ) • γ64 - γ64 ∈ L64 :=
      mem_L64.mpr ⟨q, 0, by simp [γ64, hqr]; ring, by simp [γ64]⟩
    rw [theta_coset_eq64 hmem]
    have : (ZMod.χ₄ ((a : ℤ) : ZMod 4) : ℤ) = 1 := by
      rw [hχ]; simp [h4]; omega
    rw [this]; simp
  · obtain ⟨q, hq⟩ : ∃ q : ℤ, (a : ℤ) = 4 * q + 3 := ⟨(a : ℤ) / 4, by omega⟩
    have hqr : (a : ℝ) = 4 * q + 3 := by exact_mod_cast hq
    have hmem : (a : ℝ) • γ64 - (-γ64) ∈ L64 :=
      mem_L64.mpr ⟨q + 1, 0, by simp [γ64, hqr]; ring, by simp [γ64]⟩
    rw [theta_coset_eq64 hmem]
    have : (ZMod.χ₄ ((a : ℤ) : ZMod 4) : ℤ) = -1 := by
      rw [hχ]; simp; omega
    rw [this]
    funext τ
    rw [thetaSph_neg]
    simp

theorem kron_L64 (hE : Even (finrank ℝ E2)) {n : ℕ} (hn : IsCoprime (n : ℤ) 64) :
    isEven_L64.thetaCharacter hE (n : ℤ) = ((ZMod.χ₄ ((n : ℤ) : ZMod 4) : ℤ) : ℂ) := by
  have hnl : IsCoprime (n : ℤ) (ZLattice.level L64) :=
    hn.of_isCoprime_of_dvd_right (by exact_mod_cast level_L64_dvd)
  have hodd : Odd n := by
    have := odd_of_isCoprime_64 hn
    rw [← Int.odd_natCast, Int.odd_iff]; exact this
  rw [ZLattice.IsEven.thetaCharacter_intCast isEven_L64 hE hnl,
    TauCeti.kroneckerSym_eq_jacobiSym _ hodd,
    ZLattice.signedDiscr_of_finrank_eq L64 finrank_E2, card_disc_L64]
  have e : ((-1 : ℤ) ^ 1 * ((256 : ℕ) : ℤ)) = (-1) * 16 ^ 2 := by norm_num
  rw [e, jacobiSym.mul_left, jacobiSym.at_neg_one hodd]
  have hg : (16 : ℤ).gcd n = 1 := by
    rw [Int.gcd_comm]
    exact Int.isCoprime_iff_gcd_eq_one.mp (hn.of_isCoprime_of_dvd_right (by norm_num))
  rw [jacobiSym.sq_one' hg]
  simp

theorem htriv64 (hE : Even (finrank ℝ E2)) (d : ℤ) (hd : IsCoprime d 64) :
    ((DirichletCharacter.changeLevel level_L64_dvd (isEven_L64.thetaCharacter hE)) * ψ64⁻¹)
      (d : ZMod 64) = 1 := by
  set n : ℕ := (d % 64).toNat with hn
  have hd0 : 0 ≤ d % 64 := Int.emod_nonneg _ (by norm_num)
  have hnd : (n : ℤ) = d % 64 := by rw [hn]; exact Int.toNat_of_nonneg hd0
  have hcast : (d : ZMod 64) = ((n : ℤ) : ZMod 64) := by
    rw [hnd, ← ZMod.intCast_mod d 64]; norm_num
  have hcop : IsCoprime (n : ℤ) 64 := by
    rw [hnd, Int.emod_def]
    have : IsCoprime (d - 64 * (d / 64)) 64 := by
      have := hd.add_mul_left_left (-(d / 64))
      convert this using 1; ring
    exact this
  rw [hcast, MulChar.mul_apply, MulChar.inv_apply_eq_inv',
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ (by exact_mod_cast hcop), kron_L64 hE hcop,
    psi64_apply hcop]
  have hχ := ZMod.χ₄_int_eq_if_mod_four (n : ℤ)
  have := odd_of_isCoprime_64 hcop
  have h4 : (n : ℤ) % 4 = 1 ∨ (n : ℤ) % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · have hv : (ZMod.χ₄ ((n : ℤ) : ZMod 4) : ℤ) = 1 := by rw [hχ]; simp [h4]; omega
    rw [hv]; simp
  · have hv : (ZMod.χ₄ ((n : ℤ) : ZMod 4) : ℤ) = -1 := by rw [hχ]; simp; omega
    rw [hv]; simp

/-- The cusp form `θ_{γ+L}(·; x + iy)` of weight `2` on `Γ₀(64)`. -/
noncomputable def theta64 :
    CuspForm ((Gamma0 64).map (Matrix.SpecialLinearGroup.mapGL ℝ)) (1 + 1 : ℕ) :=
  IsEvenSph.thetaSphCosetCuspForm (L := L64) isEven_L64 finrank_E2 (ν := 1) le_rfl isSph_u1_w1
    level_L64_dvd γ64_mem γ64_norm ψ64 theta_smul_coprime64 psi64_neg_one
    (fun d hd ↦ htriv64 _ d hd)

theorem theta64_apply : ⇑theta64 = thetaSph L64 1 u1 w1 γ64 := rfl

/-! ### The q-expansion -/

/-- The term `(a + 2iq) e(2 π i (a² + 4q²) τ)` on `a ≡ 1 mod 4`. -/
noncomputable def Gterm64 (τ : UpperHalfPlane) : ℤ × ℤ → ℂ :=
  {p : ℤ × ℤ | p.1 % 4 = 1}.indicator fun p ↦
    ((p.1 : ℂ) + 2 * I * p.2) * cexp (2 * π * I * ((p.1 ^ 2 + 4 * p.2 ^ 2 : ℤ) : ℂ) * τ)

/-- `(p, q) ↦ (1 + 4p, q)`. -/
def gmap64 (p : ℤ × ℤ) : ℤ × ℤ := (1 + 4 * p.1, p.2)

theorem gmap64_mem (p : ℤ × ℤ) : gmap64 p ∈ {p : ℤ × ℤ | p.1 % 4 = 1} := by
  simp only [gmap64, Set.mem_ofPred_eq]; omega

theorem gmap64_injective : Function.Injective gmap64 := by
  intro p q h
  simp only [gmap64, Prod.mk.injEq] at h
  ext <;> omega

theorem exists_gmap64 {p : ℤ × ℤ} (hp : p ∈ {p : ℤ × ℤ | p.1 % 4 = 1}) : ∃ q, gmap64 q = p := by
  simp only [Set.mem_ofPred_eq] at hp
  refine ⟨((p.1 - 1) / 4, p.2), ?_⟩
  simp only [gmap64]
  ext <;> simp only <;> omega

/-- The parametrisation `ℤ² → 4√2 ℤ ⊕ 2√2 ℤ`. -/
noncomputable def jL64 (p : ℤ × ℤ) : L64 :=
  ⟨WithLp.toLp 2 ((p.1 : ℝ) * (4 * √2), (p.2 : ℝ) * (2 * √2)), mem_L64.mpr ⟨p.1, p.2, rfl, rfl⟩⟩

theorem jL64_bijective : Function.Bijective jL64 := by
  constructor
  · intro p q h
    have h1 := congrArg (fun v : L64 ↦ (v : E2).fst) h
    have h2 := congrArg (fun v : L64 ↦ (v : E2).snd) h
    have hs : (√2 : ℝ) ≠ 0 := by positivity
    simp only [jL64] at h1 h2
    have e1 : (p.1 : ℝ) = q.1 := by
      have := mul_right_cancel₀ (show (4 * √2 : ℝ) ≠ 0 by positivity) h1
      exact this
    have e2 : (p.2 : ℝ) = q.2 := mul_right_cancel₀ (show (2 * √2 : ℝ) ≠ 0 by positivity) h2
    ext <;> assumption_mod_cast
  · intro v
    obtain ⟨m, n, h1, h2⟩ := mem_L64.mp v.2
    refine ⟨(m, n), ?_⟩
    apply Subtype.ext
    apply WithLp.ofLp_injective
    ext
    · simpa [jL64] using h1.symm
    · simpa [jL64] using h2.symm

theorem term_jL64 (τ : UpperHalfPlane) (p : ℤ × ℤ) :
    (√2 : ℂ)⁻¹ * (isoForm u1 w1 (γ64 + (jL64 p : E2)) ^ 1 *
        cexp (π * I * (‖γ64 + (jL64 p : E2)‖ ^ 2 : ℝ) * τ)) = Gterm64 τ (gmap64 p) := by
  rw [Gterm64, Set.indicator_of_mem (gmap64_mem p), isoForm_u1_w1, norm_sq_E2]
  have hx : (γ64 + (jL64 p : E2)).fst = √2 * (1 + 4 * p.1) := by simp [γ64, jL64]; ring
  have hy : (γ64 + (jL64 p : E2)).snd = 2 * √2 * p.2 := by simp [γ64, jL64]; ring
  have hn : (γ64 + (jL64 p : E2)).fst ^ 2 + (γ64 + (jL64 p : E2)).snd ^ 2 =
      2 * ((1 + 4 * (p.1 : ℝ)) ^ 2 + 4 * (p.2 : ℝ) ^ 2) := by
    rw [hx, hy]
    linear_combination ((1 + 4 * (p.1 : ℝ)) ^ 2 + 4 * (p.2 : ℝ) ^ 2) * sqrt_two_sq
  have hs : (√2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; positivity
  rw [hn, hx, hy, pow_one]
  simp only [gmap64]
  have e : cexp (π * I * ((2 * ((1 + 4 * (p.1 : ℝ)) ^ 2 + 4 * (p.2 : ℝ) ^ 2) : ℝ) : ℂ) * τ) =
      cexp (2 * π * I * (((1 + 4 * p.1) ^ 2 + 4 * p.2 ^ 2 : ℤ) : ℂ) * τ) := by
    congr 1; push_cast; ring
  rw [e]
  push_cast
  field_simp

theorem hasSum_Gterm64 (τ : UpperHalfPlane) :
    HasSum (Gterm64 τ) ((√2 : ℂ)⁻¹ * thetaSph L64 1 u1 w1 γ64 τ) := by
  have hT := (summable_thetaW L64 (polyBounded_isoForm_pow u1 w1 1) γ64 τ).hasSum
  have h1 := (Equiv.ofBijective jL64 jL64_bijective).hasSum_iff.mpr hT
  have h2 := h1.mul_left ((√2 : ℂ)⁻¹)
  have h3 : HasSum (Gterm64 τ ∘ gmap64) ((√2 : ℂ)⁻¹ * thetaSph L64 1 u1 w1 γ64 τ) := by
    convert h2 using 1
    · funext p
      exact (term_jL64 τ p).symm
    · rfl
  refine (gmap64_injective.hasSum_iff (fun x hx ↦ ?_)).mp h3
  rw [Gterm64, Set.indicator_of_notMem]
  intro hxS
  exact hx (exists_gmap64 hxS)

/-- The norm `a² + 4q²` as a natural number. -/
def Nrm64 (p : ℤ × ℤ) : ℕ := (p.1 ^ 2 + 4 * p.2 ^ 2).toNat

/-- **The coefficients of $f_{64}$**: $\left(\frac 2m\right) b(m)$. -/
noncomputable def f64C (m : ℕ) : ℂ := (congruentCoeff 2 m : ℂ)

theorem fibre_sum64 (τ : UpperHalfPlane) (m : ℕ) :
    ∑' b : {x // Nrm64 x = m}, Gterm64 τ b = f64C m * cexp (2 * π * I * m * τ) := by
  have h1 : ∑' b : {x // Nrm64 x = m}, Gterm64 τ b =
      ∑' x, {x | Nrm64 x = m}.indicator (Gterm64 τ) x := tsum_subtype {x | Nrm64 x = m} (Gterm64 τ)
  rw [h1, tsum_eq_sum (s := sec64 m)]
  · have h2 : ∀ x ∈ sec64 m, {x | Nrm64 x = m}.indicator (Gterm64 τ) x =
        ((x.1 : ℂ) + 2 * I * x.2) * cexp (2 * π * I * m * τ) := by
      intro x hx
      obtain ⟨hn, h4⟩ := (mem_sec64 m x).mp hx
      have hN : Nrm64 x = m := by simp only [Nrm64]; omega
      rw [Set.indicator_of_mem (by exact hN), Gterm64, Set.indicator_of_mem (by exact h4), hn]
      simp
    rw [Finset.sum_congr rfl h2, ← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h0 : ∑ x ∈ sec64 m, (x.2 : ℂ) = 0 := by
      exact_mod_cast congrArg (fun z : ℤ ↦ (z : ℂ)) (sum_im_sec64 m)
    have hc : congruentCoeff 2 m = ∑ x ∈ sec64 m, x.1 := by
      rw [sum_re_sec64, congruentCoeff]; norm_num
    rw [h0, mul_zero, add_zero, f64C, hc]
    push_cast
    rfl
  · intro b hb
    by_cases hN : Nrm64 b = m
    · rw [Set.indicator_of_mem (by exact hN), Gterm64, Set.indicator_of_notMem]
      intro hS
      have hS' : b.1 % 4 = 1 := hS
      refine hb ((mem_sec64 m b).mpr ⟨?_, hS'⟩)
      simp only [Nrm64] at hN
      have := sq_nonneg b.1; have := sq_nonneg b.2
      omega
    · rw [Set.indicator_of_notMem (by exact hN)]

theorem f64_eq_theta (τ : UpperHalfPlane) :
    Miyake.qSeries f64C τ = (√2 : ℂ)⁻¹ * thetaSph L64 1 u1 w1 γ64 τ := by
  have h := hasSum_fiber (hasSum_Gterm64 τ) Nrm64
  simp_rw [fibre_sum64] at h
  exact h.tsum_eq

/-- **$f_{64}$ is a cusp form of weight `2` on `Γ₀(64)`**, as `(1/√2) θ_{γ+L}(·; x + iy)`. -/
theorem f64Modular :
    ∃ F : CuspForm ((Gamma0 64).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2,
      ⇑F = fun τ : ℍ ↦ Miyake.qSeries f64C τ :=
  ⟨((√2 : ℂ)⁻¹) • theta64, funext fun τ ↦ by
    rw [f64_eq_theta]; rfl⟩

theorem coeffGrowth_f64C : Miyake.CoeffGrowth f64C := by
  refine ⟨1, Asymptotics.IsBigO.of_bound 6 (Filter.Eventually.of_forall fun m ↦ ?_)⟩
  have hb := abs_f32Coeff_le m
  have hj : |(jacobiSym 2 m : ℤ)| ≤ 1 := by
    rcases jacobiSym.trichotomy 2 m with h | h | h <;> simp [h]
  have : |congruentCoeff 2 m| ≤ 6 * m := by
    rw [congruentCoeff, abs_mul]
    push_cast
    nlinarith [abs_nonneg (f32Coeff m), abs_nonneg (jacobiSym 2 m)]
  rw [f64C, Complex.norm_intCast, Real.rpow_one, Real.norm_natCast]
  exact_mod_cast this

theorem isCuspFormChar_f64 :
    Miyake.IsCuspFormChar 2 64 1 (fun τ : ℍ ↦ Miyake.qSeries f64C τ) := by
  obtain ⟨F, hF⟩ := f64Modular
  have hmem : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 64 → (F : ℍ → ℂ) ∣[(2 : ℤ)] γ = F := by
    intro γ hγ
    have := F.slash_action_eq' (Matrix.SpecialLinearGroup.mapGL ℝ γ) ⟨γ, hγ, rfl⟩
    rwa [← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← ModularForm.SL_slash] at this
  refine ⟨⟨CuspForm.restrict (Subgroup.map_mono (Gamma1_in_Gamma0 64)) F, ?_⟩, ?_⟩
  · rw [← hF]; rfl
  · intro γ hγ
    have hu : IsUnit ((γ 1 1 : ℤ) : ZMod 64) := by
      have hdet := γ.det_coe
      rw [Matrix.det_fin_two] at hdet
      rw [Gamma0_mem] at hγ
      refine isUnit_iff_exists_inv.mpr ⟨((γ 0 0 : ℤ) : ZMod 64), ?_⟩
      have := congrArg (fun x : ℤ ↦ (x : ZMod 64)) hdet
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hγ, mul_zero, sub_zero] at this
      rw [mul_comm]; exact this
    rw [← hF, hmem γ hγ, MulChar.one_apply hu, one_smul]

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
