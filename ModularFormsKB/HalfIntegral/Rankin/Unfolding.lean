/-
# The Rankin–Selberg unfolding principle, proved

This file proves the named input
`RankinUnfolding` of `Abstract/ShimuraRankin.lean` (`rankinUnfolding`): for $L \ge 1$, right coset representatives
$R$ of $\Gamma_0(L)$, a continuous $G$ with the unitary weight-$\lambda$ law, $\operatorname{Re}s > 1$ and
$\int_0^\infty\!\int_0^1|G|\,y^{\sigma-2} < \infty$,
$$\sum_{\gamma\in R}\int_{\mathcal F}G(\gamma\tau)E(\gamma\tau,s)\,d\mu = 2L(2s,\omega)\int_0^\infty\!\int_0^1G\,y^{s-2}\,dx\,dy.$$

**Proof.**
- (A) *Regrouping the lattice sum* (`mul_eisensteinLattice_eq`). The nonzero terms of
  $E(z,s) = y^s\sum_{(c,d)\in L\mathbb Z\times\mathbb Z}\omega(d)(cz+d)^\lambda|cz+d|^{-\lambda-2s}$ have
  $\gcd(d, L) = 1$, so $(c,d) = \pm n\,(c_0,d_0)$ with $n \ge 1$ and $(c_0,d_0)$ the bottom row of a representative of
  a coset in $\Gamma_\infty\backslash\Gamma_0(L)$ (the map is injective, `Phi_injective`, and its range contains the
  support, `support_subset_range_Phi`). With the unitary law, $G(z)\,y^s\omega(d_0)(c_0z+d_0)^\lambda|c_0z+d_0|^{-\lambda-2s}
  = F(\gamma z)$, $F = G\,y^s$, so $G\,E(\cdot,s) = (1+\omega(-1)(-1)^\lambda)\,L(2s,\omega)\sum_{\Gamma_\infty\backslash\Gamma_0(L)}
  F(\gamma z)$. If $\omega(-1)(-1)^\lambda \ne 1$ the law at $-1$ forces $G = 0$.
- (B) *Coset bookkeeping* (`repsIntegral_eq_sum_quotient`): for a $\Gamma_0(L)$-invariant $h$, the sum over $R$ of the
  integrals over `ModularGroup.fd` is the sum over $\mathrm{SL}_2(\mathbb Z)/\Gamma_0(L)$ of the integrals over the
  translates of `fdo` used by `Milne.unfolding_core`.
- (C) *Unfolding* (`Milne.unfolding_terms`, the tiling of the strip $0 \le x < 1$ by the translates of the coset domain
  under $\Gamma_\infty$) and Fubini on the strip (`Milne.integral_stripSet`).

**Index shift.** Matrix entries are 0-based: $c = \gamma_{1,0}$, $d = \gamma_{1,1}$.
-/
import ModularFormsKB.HalfIntegral.Abstract.ShimuraRankin
import ModularFormsKB.Milne.Ch4.Unfolding
import ModularFormsKB.HalfIntegral.Abstract.FundamentalDomainVolume
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.NumberTheory.LSeries.Basic

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup MeasureTheory Set ModularGroup
open scoped Real Pointwise

local notation "ℍ" => UpperHalfPlane

namespace RankinUnfold

/-! ### Elementary facts about `Γ₀(L)` -/

lemma neg_one_mem_Gamma0 (L : ℕ) : (-1 : SL(2, ℤ)) ∈ Gamma0 L := by
  rw [Gamma0_mem]; simp

lemma T_mem_Gamma0 (L : ℕ) : ModularGroup.T ∈ Gamma0 L := by
  rw [Gamma0_mem]; simp [ModularGroup.T]

lemma widthAtInfty_Gamma0 (L : ℕ) : Milne.widthAtInfty (Gamma0 L) = 1 := by
  unfold Milne.widthAtInfty
  have h := Subgroup.strictWidthInfty_eq_one_of_T_mem (T_mem_Gamma0 L)
  rw [Subgroup.widthInfty, Subgroup.adjoinNegOne_eq_self_iff.mpr]
  · exact h
  · exact ⟨-1, neg_one_mem_Gamma0 L, by ext; simp⟩

lemma dvd_of_mem_Gamma0 {L : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 L) : (L : ℤ) ∣ γ 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ L).mp (Gamma0_mem.mp hγ)

lemma withCenter_Gamma0 (L : ℕ) : (Gamma0 L).withCenter = Gamma0 L := by
  apply le_antisymm _ (Subgroup.le_withCenter _)
  rw [Subgroup.withCenter_def, sup_le_iff]
  refine ⟨le_rfl, fun g hg ↦ ?_⟩
  rcases (Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one).1 hg with rfl | rfl
  · exact Subgroup.one_mem _
  · exact neg_one_mem_Gamma0 L

/-- The bottom row of an element of `SL(2, ℤ)` is coprime. -/
lemma isCoprime_row (g : SL(2, ℤ)) : IsCoprime (g 1 0) (g 1 1) :=
  ⟨-g 0 1, g 0 0, by have := Matrix.SpecialLinearGroup.det_coe g; rw [Matrix.det_fin_two] at this; linarith⟩

/-! ### The cosets `Γ_∞\Γ₀(L)` and their bottom rows -/

variable (L : ℕ)

/-- The cosets $\Gamma_\infty\backslash\Gamma_0(L)$. -/
abbrev X : Type := Milne.StabInftyCosets (Gamma0 L)

/-- The chosen representative of a coset, in `SL(2, ℤ)`. -/
noncomputable def rep (x : X L) : SL(2, ℤ) := ((x.out : Gamma0 L) : SL(2, ℤ))

lemma rep_mem (x : X L) : rep L x ∈ Gamma0 L := (x.out : Gamma0 L).2

/-- Two elements of `Γ₀(L)` whose bottom rows agree up to sign lie in the same coset. -/
lemma coset_eq_of_row {a b : Gamma0 L} (h : ((a : SL(2, ℤ)) 1 0 * (b : SL(2, ℤ)) 1 1 =
    (a : SL(2, ℤ)) 1 1 * (b : SL(2, ℤ)) 1 0)) :
    (Quotient.mk _ a : X L) = Quotient.mk _ b := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  show ((b * a⁻¹ : Gamma0 L) : SL(2, ℤ)) 1 0 = 0
  push_cast
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  linarith

/-- The representative of the coset of `a` is `β a` with `β ∈ Γ_∞`; its bottom row is `ε` times that of `a`,
`ε = ±1`. -/
lemma rep_row (a : Gamma0 L) : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
    rep L (Quotient.mk _ a) 1 0 = ε * (a : SL(2, ℤ)) 1 0 ∧
    rep L (Quotient.mk _ a) 1 1 = ε * (a : SL(2, ℤ)) 1 1 := by
  have h := QuotientGroup.rightRel_apply.mp (Quotient.exact (Quotient.out_eq (Quotient.mk _ a : X L)))
  -- `h : a * out⁻¹ ∈ Γ_∞`
  set o : Gamma0 L := (Quotient.mk _ a : X L).out with ho
  have h10 : ((a * o⁻¹ : Gamma0 L) : SL(2, ℤ)) 1 0 = 0 := h
  set β : SL(2, ℤ) := ((a * o⁻¹ : Gamma0 L) : SL(2, ℤ)) with hβ
  obtain ⟨ε, hε, h00, h11⟩ := Milne.sl_lower_zero β h10
  have hrep : rep L (Quotient.mk _ a) = β⁻¹ * (a : SL(2, ℤ)) := by
    simp [rep, β, ← ho, mul_assoc]
  refine ⟨ε, hε, ?_, ?_⟩
  · rw [hrep, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h00]
  · rw [hrep, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h00]

/-! ### (A) The regrouping map -/

/-- The sign `+1` or `-1`. -/
def sg (b : Bool) : ℤ := if b then 1 else -1

lemma sg_sq (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

/-- The regrouping map $(n, x, \pm) \mapsto \pm(n+1)\,(c_x/L, d_x)$. -/
noncomputable def Phi (p : ℕ × (X L × Bool)) : ℤ × ℤ :=
  (sg p.2.2 * (p.1 + 1) * (rep L p.2.1 1 0 / L), sg p.2.2 * (p.1 + 1) * rep L p.2.1 1 1)

lemma L_mul_Phi_fst (p : ℕ × (X L × Bool)) :
    (L : ℤ) * (Phi L p).1 = sg p.2.2 * (p.1 + 1) * rep L p.2.1 1 0 := by
  unfold Phi
  have := Int.mul_ediv_cancel' (dvd_of_mem_Gamma0 (rep_mem L p.2.1))
  simp only
  rw [← this]; ring_nf; rw [this]

lemma gcd_row_eq_one (g : SL(2, ℤ)) : Int.gcd (g 1 0) (g 1 1) = 1 :=
  Int.isCoprime_iff_gcd_eq_one.mp (isCoprime_row g)

lemma Phi_injective (hL : 1 ≤ L) : Function.Injective (Phi L) := by
  rintro ⟨n, x, b⟩ ⟨n', x', b'⟩ h
  have h1 : (L : ℤ) * (Phi L (n, x, b)).1 = (L : ℤ) * (Phi L (n', x', b')).1 := by rw [h]
  rw [L_mul_Phi_fst, L_mul_Phi_fst] at h1
  have h2 : (Phi L (n, x, b)).2 = (Phi L (n', x', b')).2 := by rw [h]
  simp only [Phi] at h2
  simp only at h1
  set c := rep L x 1 0; set d := rep L x 1 1
  set c' := rep L x' 1 0; set d' := rep L x' 1 1
  -- the gcd of both sides
  have hg : Int.gcd (sg b * (n + 1) * c) (sg b * (n + 1) * d) = n + 1 := by
    rw [Int.gcd_mul_left, gcd_row_eq_one]; cases b <;> simp [sg] <;> omega
  have hg' : Int.gcd (sg b' * (n' + 1) * c') (sg b' * (n' + 1) * d') = n' + 1 := by
    rw [Int.gcd_mul_left, gcd_row_eq_one]; cases b' <;> simp [sg] <;> omega
  rw [h1, h2] at hg
  have hn : n = n' := by omega
  subst hn
  have hn0 : ((n : ℤ) + 1) ≠ 0 := by omega
  have e1 : sg b * c = sg b' * c' := by
    have := h1; rw [mul_comm (sg b), mul_comm (sg b'), mul_assoc, mul_assoc] at this
    exact mul_left_cancel₀ hn0 this
  have e2 : sg b * d = sg b' * d' := by
    have := h2; rw [mul_comm (sg b), mul_comm (sg b'), mul_assoc, mul_assoc] at this
    exact mul_left_cancel₀ hn0 this
  have hx : x = x' := by
    have hr : (Quotient.mk _ (x.out) : X L) = Quotient.mk _ (x'.out) := by
      apply coset_eq_of_row
      show c * d' = d * c'
      have := sg_sq b
      have := sg_sq b'
      calc c * d' = (sg b * sg b) * (sg b' * sg b') * c * d' := by simp [sg_sq]
        _ = (sg b * c) * (sg b' * d') * sg b * sg b' := by ring
        _ = (sg b' * c') * (sg b * d) * sg b * sg b' := by rw [e1, e2]
        _ = (sg b * sg b) * (sg b' * sg b') * d * c' := by ring
        _ = d * c' := by simp [sg_sq]
    simpa [Quotient.out_eq] using hr
  subst hx
  have hb : b = b' := by
    have hcd : c ≠ 0 ∨ d ≠ 0 := by
      by_contra hc; push_neg at hc
      have this : Int.gcd c d = 1 := gcd_row_eq_one (rep L x)
      rw [hc.1, hc.2] at this; simp at this
    rcases hcd with hc | hd
    · have : sg b = sg b' := mul_right_cancel₀ hc e1
      cases b <;> cases b' <;> simp_all [sg]
    · have : sg b = sg b' := mul_right_cancel₀ hd e2
      cases b <;> cases b' <;> simp_all [sg]
  rw [hb]

/-! ### (A) The summand and its support -/

variable {L}

/-- The summand $\omega(d)\,v^\lambda|v|^{-\lambda-2s}$, $v = Lcz + d$, of `eisensteinLattice`. -/
noncomputable def term (lam : ℕ) (ω : DirichletCharacter ℂ L) (z : ℍ) (s : ℂ) (p : ℤ × ℤ) : ℂ :=
  ω (p.2 : ZMod L) * eisTerm lam s ((L : ℂ) * p.1 * z + p.2)

lemma eisTerm_zero (lam : ℕ) {s : ℂ} (hs : 1 < s.re) : eisTerm lam s 0 = 0 := by
  unfold eisTerm
  have : (-(lam : ℂ) - 2 * s) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  simp [Complex.zero_cpow this]

lemma vec_ne_zero {c d : ℤ} (z : ℍ) (h : (c : ℂ) * z + d = 0) : c = 0 ∧ d = 0 := by
  have him := congrArg Complex.im h
  simp at him
  rcases him with hc | hz
  · subst hc; simp at h; exact ⟨rfl, by exact_mod_cast h⟩
  · exact absurd hz z.im_ne_zero

lemma support_subset_range_Phi (hL : 1 ≤ L) (lam : ℕ) (ω : DirichletCharacter ℂ L) (z : ℍ) {s : ℂ}
    (hs : 1 < s.re) : Function.support (term lam ω z s) ⊆ Set.range (Phi L) := by
  rintro ⟨p1, p2⟩ hp
  simp only [Function.mem_support, term] at hp
  have hω : ω (p2 : ZMod L) ≠ 0 := left_ne_zero_of_mul hp
  have hv : ((L : ℂ) * p1 * z + p2) ≠ 0 := by
    intro h; apply hp; rw [h, eisTerm_zero lam hs, mul_zero]
  have hu : IsUnit (p2 : ZMod L) := by
    by_contra hu; exact hω (ω.map_nonunit hu)
  set c : ℤ := L * p1
  have hcd : c ≠ 0 ∨ p2 ≠ 0 := by
    by_contra h; push_neg at h; apply hv
    have : (L : ℂ) * p1 = ((c : ℤ) : ℂ) := by simp [c]
    rw [this, h.1, h.2]; simp
  set g : ℕ := Int.gcd c p2
  have hg0 : 0 < g := by
    rcases hcd with h1 | h1
    · exact Int.gcd_pos_of_ne_zero_left _ h1
    · exact Int.gcd_pos_of_ne_zero_right _ h1
  obtain ⟨c0, hc0⟩ : (g : ℤ) ∣ c := Int.gcd_dvd_left c p2
  obtain ⟨d0, hd0⟩ : (g : ℤ) ∣ p2 := Int.gcd_dvd_right c p2
  have hcop : IsCoprime c0 d0 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := Int.gcd_mul_left (g : ℤ) c0 d0
    rw [← hc0, ← hd0] at this
    have hga : (g : ℤ).natAbs = g := Int.natAbs_natCast g
    rw [hga] at this
    have : g * Int.gcd c0 d0 = g * 1 := by rw [mul_one]; exact this.symm
    exact Nat.eq_of_mul_eq_mul_left hg0 this
  -- `g` is prime to `L`, hence `L ∣ c0`
  have hgL : IsCoprime (g : ℤ) (L : ℤ) := by
    have hp2L : IsCoprime p2 (L : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have := (ZMod.isUnit_iff_coprime p2.natAbs L).1 (by
        rcases Int.natAbs_eq p2 with h | h
        · rw [h] at hu; simpa using hu
        · rw [h] at hu; simpa using hu.neg)
      simpa [Int.gcd] using this
    exact IsCoprime.of_mul_left_left (hd0 ▸ hp2L)
  have hLc0 : (L : ℤ) ∣ c0 := by
    have : (L : ℤ) ∣ g * c0 := hc0 ▸ dvd_mul_right _ _
    exact hgL.symm.dvd_of_dvd_mul_left this
  -- a matrix of `Γ₀(L)` with bottom row `(c0, d0)`
  obtain ⟨u, w, huw⟩ := hcop
  let γ : SL(2, ℤ) := ⟨!![w, -u; c0, d0], by rw [Matrix.det_fin_two_of]; linarith⟩
  have hγ : γ ∈ Gamma0 L := by
    rw [Gamma0_mem]; simpa [γ] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ L).mpr hLc0
  obtain ⟨ε, hε, h10, h11⟩ := rep_row L ⟨γ, hγ⟩
  have hγ10 : ((⟨γ, hγ⟩ : Gamma0 L) : SL(2, ℤ)) 1 0 = c0 := by simp [γ]
  have hγ11 : ((⟨γ, hγ⟩ : Gamma0 L) : SL(2, ℤ)) 1 1 = d0 := by simp [γ]
  refine ⟨(g - 1, Quotient.mk _ ⟨γ, hγ⟩, decide (ε = 1)), ?_⟩
  have hsg : sg (decide (ε = 1)) = ε := by rcases hε with rfl | rfl <;> simp [sg]
  have hg1 : ((g - 1 : ℕ) : ℤ) + 1 = g := by omega
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hL0 : (L : ℤ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  ext
  · apply mul_left_cancel₀ hL0
    rw [L_mul_Phi_fst]
    simp only [hsg, hg1, h10, hγ10]
    show ε * g * (ε * c0) = L * p1
    rw [show (L : ℤ) * p1 = c from rfl, hc0]
    linear_combination (g * c0) * hε2
  · simp only [Phi, hsg, hg1, h11, hγ11]
    rw [hd0]
    have e : (γ : SL(2, ℤ)) 1 1 = d0 := hγ11
    linear_combination (g * d0) * hε2 + (ε * ε * g) * e

/-! ### (A) Summability -/

lemma norm_eisTerm_le (lam : ℕ) {s : ℂ} (hs : 1 < s.re) (v : ℂ) :
    ‖eisTerm lam s v‖ ≤ ‖v‖ ^ (-(2 * s.re)) := by
  by_cases hv : v = 0
  · subst hv; rw [eisTerm_zero lam hs, norm_zero]; positivity
  have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
  unfold eisTerm
  rw [norm_mul, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hr]
  have : (-(lam : ℂ) - 2 * s).re = -(lam : ℝ) + -(2 * s.re) := by simp; ring
  rw [this, Real.rpow_add hr, Real.rpow_neg hr.le, Real.rpow_natCast]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]

lemma summable_term (hL : 1 ≤ L) (lam : ℕ) (ω : DirichletCharacter ℂ L) (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    Summable (term lam ω z s) := by
  have : NeZero L := ⟨by omega⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ a : ZMod L, ‖ω a‖ ≤ C :=
    ⟨1, fun a ↦ DirichletCharacter.norm_le_one ω a⟩
  have hk : 2 < 2 * s.re := by linarith
  let e : ℤ × ℤ → (Fin 2 → ℤ) := fun p ↦ ![(L : ℤ) * p.1, p.2]
  have he : Function.Injective e := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    simp [e] at h0 h1
    have hL0 : (L : ℤ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
    rcases h0 with h0 | h0
    · simp [h0, h1]
    · exact absurd h0 (by omega)
  have hS := ((EisensteinSeries.summable_one_div_norm_rpow hk).comp_injective he).mul_left
    (C * (EisensteinSeries.r z) ^ (-(2 * s.re)))
  refine Summable.of_norm_bounded hS fun p ↦ ?_
  simp only [term, norm_mul, Function.comp_apply]
  have h1 := norm_eisTerm_le lam hs ((L : ℂ) * p.1 * z + p.2)
  have h2 := EisensteinSeries.summand_bound z (k := 2 * s.re) (by linarith) (e p)
  have h3 : ((e p 0 : ℤ) : ℂ) * z + ((e p 1 : ℤ) : ℂ) = (L : ℂ) * p.1 * z + p.2 := by simp [e]
  rw [h3] at h2
  calc ‖ω (p.2 : ZMod L)‖ * ‖eisTerm lam s ((L : ℂ) * p.1 * z + p.2)‖
      ≤ C * (EisensteinSeries.r z ^ (-(2 * s.re)) * ‖e p‖ ^ (-(2 * s.re))) :=
        mul_le_mul (hC _) (h1.trans h2) (norm_nonneg _) ((norm_nonneg _).trans (hC 0))
    _ = _ := by ring

/-! ### (A) The value of the summand on the image of `Phi` -/

/-- The term of a coset: $\omega(d)\,(cz+d)^\lambda|cz+d|^{-\lambda-2s}$ for the bottom row of the representative. -/
noncomputable def cosetTerm (lam : ℕ) (ω : DirichletCharacter ℂ L) (z : ℍ) (s : ℂ) (x : X L) : ℂ :=
  ω (rep L x 1 1 : ZMod L) * eisTerm lam s ((rep L x 1 0 : ℂ) * z + rep L x 1 1)

lemma eisTerm_smul (lam : ℕ) (s : ℂ) (b : Bool) (n : ℕ) (v : ℂ) :
    eisTerm lam s (((sg b * (n + 1) : ℤ) : ℂ) * v) =
      ((sg b : ℂ) ^ lam * (((n + 1 : ℕ) : ℂ) ^ (2 * s))⁻¹) * eisTerm lam s v := by
  have ha : (0 : ℝ) < n + 1 := by positivity
  have hnorm : ‖((sg b * (n + 1) : ℤ) : ℂ) * v‖ = ((n : ℝ) + 1) * ‖v‖ := by
    have hs : (sg b : ℝ) = 1 ∨ (sg b : ℝ) = -1 := by cases b <;> simp [sg]
    rw [norm_mul, Complex.norm_intCast]; congr 1
    push_cast
    rcases hs with h | h <;> rw [h]
    · simp [abs_of_nonneg ha.le]
    · rw [show (-1 : ℝ) * ((n : ℝ) + 1) = -((n : ℝ) + 1) by ring, abs_neg, abs_of_nonneg ha.le]
  unfold eisTerm
  rw [hnorm, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha.le (norm_nonneg _), mul_pow]
  have hc : (((n : ℝ) + 1 : ℝ) : ℂ) = ((n + 1 : ℕ) : ℂ) := by push_cast; rfl
  have hne : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  rw [hc, show (-(lam : ℂ) - 2 * s) = -(lam : ℂ) + -(2 * s) by ring, Complex.cpow_add _ _ hne,
    Complex.cpow_neg, Complex.cpow_neg, Complex.cpow_natCast]
  push_cast
  simp only [mul_pow]
  have hne' : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast hne
  field_simp

lemma term_Phi (hL : 1 ≤ L) (lam : ℕ) (ω : DirichletCharacter ℂ L) (z : ℍ) (s : ℂ) (n : ℕ) (x : X L)
    (b : Bool) :
    term lam ω z s (Phi L (n, x, b)) =
      (ω (sg b : ZMod L) * (sg b : ℂ) ^ lam) *
        (ω ((n + 1 : ℕ) : ZMod L) * (((n + 1 : ℕ) : ℂ) ^ (2 * s))⁻¹) * cosetTerm lam ω z s x := by
  have h1 : (L : ℂ) * ((Phi L (n, x, b)).1 : ℂ) = ((sg b * (n + 1) * rep L x 1 0 : ℤ) : ℂ) := by
    rw [← L_mul_Phi_fst L (n, x, b)]; push_cast; ring
  have hv : (L : ℂ) * ((Phi L (n, x, b)).1 : ℂ) * z + ((Phi L (n, x, b)).2 : ℂ) =
      ((sg b * (n + 1) : ℤ) : ℂ) * ((rep L x 1 0 : ℂ) * z + rep L x 1 1) := by
    rw [h1]; simp only [Phi]; push_cast; ring
  unfold term cosetTerm
  rw [hv, eisTerm_smul]
  have hω : ω (((Phi L (n, x, b)).2 : ℤ) : ZMod L) =
      ω (sg b : ZMod L) * ω ((n + 1 : ℕ) : ZMod L) * ω (rep L x 1 1 : ZMod L) := by
    simp only [Phi]; push_cast; rw [map_mul, map_mul]
  rw [hω]; ring

/-! ### (A) Assembly of the regrouping -/

lemma sign_sum (lam : ℕ) (ω : DirichletCharacter ℂ L) (hpar : ω (-1) * (-1 : ℂ) ^ lam = 1) :
    ∑ b : Bool, ω (sg b : ZMod L) * (sg b : ℂ) ^ lam = 2 := by
  simp [sg, Fintype.sum_bool, hpar]; norm_num

/-- **The regrouped lattice sum:** $\sum_{(c,d)}\omega(d)\,v^\lambda|v|^{-\lambda-2s} =
2L(2s,\omega)\sum_{x\in\Gamma_\infty\backslash\Gamma_0(L)}\omega(d_x)(c_xz+d_x)^\lambda|c_xz+d_x|^{-\lambda-2s}$. -/
theorem tsum_term_eq (hL : 1 ≤ L) (lam : ℕ) (ω : DirichletCharacter ℂ L)
    (hpar : ω (-1) * (-1 : ℂ) ^ lam = 1) (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    ∑' p, term lam ω z s p = 2 * LSeries (fun n ↦ ω n) (2 * s) * ∑' x, cosetTerm lam ω z s x := by
  have hsum := summable_term hL lam ω z hs
  have hinj := Phi_injective L hL
  rw [← hinj.tsum_eq (support_subset_range_Phi hL lam ω z hs)]
  have hsumΦ : Summable (term lam ω z s ∘ Phi L) := hsum.comp_injective hinj
  change ∑' c, (term lam ω z s ∘ Phi L) c = _
  rw [hsumΦ.tsum_prod' (fun n ↦ hsumΦ.prod_factor n)]
  have hinner : ∀ n : ℕ, ∑' xb : X L × Bool, term lam ω z s (Phi L (n, xb)) =
      2 * (ω ((n + 1 : ℕ) : ZMod L) * (((n + 1 : ℕ) : ℂ) ^ (2 * s))⁻¹) * ∑' x, cosetTerm lam ω z s x := by
    intro n
    have hs2 : Summable fun xb : X L × Bool ↦ term lam ω z s (Phi L (n, xb)) := hsumΦ.prod_factor n
    rw [hs2.tsum_prod' (fun x ↦ (hasSum_fintype _).summable)]
    simp_rw [tsum_fintype, term_Phi hL, ← Finset.sum_mul, sign_sum lam ω hpar]
    rw [tsum_mul_left]
  simp_rw [Function.comp_apply, hinner]
  rw [tsum_mul_right, tsum_mul_left]
  congr 2
  -- the Dirichlet series
  have hLS : LSeriesSummable (fun n ↦ ω n) (2 * s) :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ ↦ DirichletCharacter.norm_le_one ω _)
      (by simp; linarith)
  have hLS' : Summable (LSeries.term (fun n ↦ ω n) (2 * s)) := hLS
  unfold LSeries
  conv_rhs => rw [tsum_eq_zero_add' ((summable_nat_add_iff 1).mpr hLS')]
  simp only [LSeries.term_zero, zero_add]
  refine tsum_congr fun n ↦ ?_
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), div_eq_mul_inv]

/-! ### (A) The pointwise identity -/

variable {lam : ℕ} {ω : DirichletCharacter ℂ L} {G : ℍ → ℂ}

/-- $F = G\,y^s$. -/
noncomputable def Fs (G : ℍ → ℂ) (s : ℂ) (z : ℍ) : ℂ := G z * ((z.im : ℂ) ^ s)

lemma cosetTerm_mul (hU : UnitaryLaw L lam ω G) (z : ℍ) (s : ℂ) (x : X L) :
    G z * ((z.im : ℂ) ^ s) * cosetTerm lam ω z s x = Fs G s (rep L x • z) := by
  set c := rep L x 1 0; set d := rep L x 1 1
  set v : ℂ := (c : ℂ) * z + d
  have hv : v ≠ 0 := by
    intro h
    obtain ⟨h1, h2⟩ := vec_ne_zero z h
    have := gcd_row_eq_one (rep L x)
    rw [show (rep L x : SL(2, ℤ)) 1 0 = 0 from h1, show (rep L x : SL(2, ℤ)) 1 1 = 0 from h2] at this
    simp at this
  have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hGl := hU (rep L x) (rep_mem L x) z
  have him : (rep L x • z).im = z.im / ‖v‖ ^ 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]; rfl
  unfold Fs cosetTerm eisTerm
  rw [hGl, him]
  have hy := z.im_pos
  have e1 : (((z.im / ‖v‖ ^ 2 : ℝ)) : ℂ) ^ s = ((z.im : ℂ) ^ s) * (((‖v‖ : ℂ) ^ s) ^ 2)⁻¹ := by
    rw [div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hy.le (by positivity)]
    congr 1
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_ne_zero.symm)]
    congr 1
    rw [Complex.ofReal_pow, sq, sq, Complex.mul_cpow_ofReal_nonneg hr.le hr.le]
  have e2 : ((‖v‖ : ℝ) : ℂ) ^ (-(lam : ℂ) - 2 * s) = (((‖v‖ : ℂ) ^ lam))⁻¹ * (((‖v‖ : ℂ) ^ s) ^ 2)⁻¹ := by
    have hne : ((‖v‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [show (-(lam : ℂ) - 2 * s) = -(lam : ℂ) + -(2 * s) by ring, Complex.cpow_add _ _ hne,
      Complex.cpow_neg, Complex.cpow_neg, Complex.cpow_natCast, show (2 : ℂ) * s = ((2 : ℕ) : ℂ) * s by simp,
      Complex.cpow_nat_mul]
  rw [e1, e2, div_pow]
  ring

/-- **The pointwise identity** $G\,E(\cdot,s) = 2L(2s,\omega)\sum_{\Gamma_\infty\backslash\Gamma_0(L)}F(\gamma z)$. -/
theorem mul_eisensteinLattice_eq (hL : 1 ≤ L) (hpar : ω (-1) * (-1 : ℂ) ^ lam = 1)
    (hU : UnitaryLaw L lam ω G) (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    G z * eisensteinLattice L lam ω z s =
      2 * LSeries (fun n ↦ ω n) (2 * s) * ∑' x : X L, Fs G s (rep L x • z) := by
  unfold eisensteinLattice
  have := tsum_term_eq hL lam ω hpar z hs
  unfold term at this
  rw [← mul_assoc, this]
  simp_rw [← cosetTerm_mul hU z s]
  rw [tsum_mul_left]; ring

/-- The parity: either $\omega(-1)(-1)^\lambda = 1$, or the law forces $G = 0$. -/
lemma parity_or_zero (hU : UnitaryLaw L lam ω G) :
    ω (-1) * (-1 : ℂ) ^ lam = 1 ∨ G = 0 := by
  by_cases h : ω (-1) * (-1 : ℂ) ^ lam = 1
  · exact Or.inl h
  right; funext τ
  have h1 := hU (-1) (neg_one_mem_Gamma0 L) τ
  rw [ModularGroup.SL_neg_smul, one_smul] at h1
  have h2 : ((((-1 : SL(2, ℤ)) 1 0 : ℤ) : ℂ) * τ + (((-1 : SL(2, ℤ)) 1 1 : ℤ) : ℂ)) = -1 := by simp
  rw [h2] at h1
  simp only [norm_neg, norm_one, Complex.ofReal_one, div_one] at h1
  have h3 : (((-1 : SL(2, ℤ)) 1 1 : ℤ) : ZMod L) = -1 := by simp
  rw [h3] at h1
  have : (1 - ω (-1) * (-1 : ℂ) ^ lam) * G τ = 0 := by linear_combination h1
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm h))

/-! ### (B) Invariance -/

lemma Fs_stab (hpar : ω (-1) * (-1 : ℂ) ^ lam = 1) (hU : UnitaryLaw L lam ω G) (s : ℂ)
    (β : Gamma0 L) (hβ : β ∈ Milne.stabInfty (Gamma0 L)) (z : ℍ) :
    Fs G s ((β : SL(2, ℤ)) • z) = Fs G s z := by
  have h10 : (β : SL(2, ℤ)) 1 0 = 0 := hβ
  obtain ⟨ε, hε, h00, h11⟩ := Milne.sl_lower_zero (β : SL(2, ℤ)) h10
  have hGl := hU β β.2 z
  rw [h10, h11] at hGl
  have him : ((β : SL(2, ℤ)) • z).im = z.im := by
    rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
    rcases hε with rfl | rfl <;> simp [h10, h11]
  unfold Fs
  rw [hGl, him]
  rcases hε with rfl | rfl
  · simp
  · simp only [Int.cast_neg, Int.cast_one, Int.cast_zero, zero_mul, zero_add, norm_neg, norm_one, Complex.ofReal_one, div_one]
    rw [hpar, one_mul]

/-- The function $H(z) = \sum_{\Gamma_\infty\backslash\Gamma_0(L)}F(\gamma z)$. -/
noncomputable def Hs (G : ℍ → ℂ) (s : ℂ) (z : ℍ) : ℂ := ∑' x : X L, Fs G s (rep L x • z)

/-- Right multiplication by `γ ∈ Γ₀(L)` permutes `Γ_∞\Γ₀(L)`. -/
noncomputable def rmul (γ : Gamma0 L) : X L ≃ X L where
  toFun := Quotient.map' (fun a ↦ a * γ) (fun a b h ↦ by
    have h' := QuotientGroup.rightRel_apply.mp h
    exact QuotientGroup.rightRel_apply.mpr (by simpa [mul_assoc] using h'))
  invFun := Quotient.map' (fun a ↦ a * γ⁻¹) (fun a b h ↦ by
    have h' := QuotientGroup.rightRel_apply.mp h
    exact QuotientGroup.rightRel_apply.mpr (by simpa [mul_assoc] using h'))
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h a => simp [Quotient.map'_mk'']
  right_inv x := by
    induction x using Quotient.inductionOn with
    | h a => simp [Quotient.map'_mk'']

lemma Hs_invariant (hpar : ω (-1) * (-1 : ℂ) ^ lam = 1) (hU : UnitaryLaw L lam ω G) (s : ℂ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 L) (z : ℍ) : Hs (L := L) G s (γ • z) = Hs (L := L) G s z := by
  unfold Hs
  conv_rhs => rw [← (rmul (⟨γ, hγ⟩ : Gamma0 L)).tsum_eq]
  refine tsum_congr fun x ↦ ?_
  have hx : (rmul (⟨γ, hγ⟩ : Gamma0 L)) x = Quotient.mk _ (x.out * ⟨γ, hγ⟩) := by
    conv_lhs => rw [← Quotient.out_eq x]
    rfl
  have h : (x.out * ⟨γ, hγ⟩) * ((rmul (⟨γ, hγ⟩ : Gamma0 L)) x).out⁻¹ ∈ Milne.stabInfty (Gamma0 L) :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact ((Quotient.out_eq _).trans hx))
  set y := (rmul (⟨γ, hγ⟩ : Gamma0 L)) x
  set β : Gamma0 L := y.out * (x.out * ⟨γ, hγ⟩)⁻¹
  have hβ : β ∈ Milne.stabInfty (Gamma0 L) := by
    have := Subgroup.inv_mem _ h
    simpa [β, mul_assoc] using this
  have hrep : rep L y = (β : SL(2, ℤ)) * (rep L x * γ) := by
    simp [rep, β, mul_assoc]
  rw [hrep, mul_smul, Fs_stab hpar hU s β hβ, mul_smul]

/-! ### (B) Coset bookkeeping -/

lemma setIntegral_SL_smul (g : SL(2, ℤ)) (S : Set ℍ) (h : ℍ → ℂ) :
    ∫ z in g • S, h z = ∫ z in S, h (g • z) := by
  have := Milne.setIntegral_smul_set' (g : PSL(2, ℤ)) S h
  rw [Matrix.SpecialLinearGroup.pslMk_smul_set] at this
  simpa [UpperHalfPlane.pslMk_smul] using this

instance finiteIndex_withCenter_Gamma0 [NeZero L] : (Gamma0 L).withCenter.FiniteIndex :=
  Subgroup.finiteIndex_of_le (Subgroup.le_withCenter _)

noncomputable instance fintypeQuotWithCenter [NeZero L] : Fintype (SL(2, ℤ) ⧸ (Gamma0 L).withCenter) :=
  Fintype.ofFinite _

/-- **The sum over right coset representatives** equals the sum over `SL(2, ℤ)/Γ₀(L)` of the integrals over the
translates of `fdo`. -/
theorem repsIntegral_eq_sum_quotient [NeZero L] {R : List SL(2, ℤ)} (hR : IsGamma0Reps L R) (h : ℍ → ℂ)
    (hh : ∀ γ ∈ Gamma0 L, ∀ z, h (γ • z) = h z) :
    repsIntegral R h = ∑ q : SL(2, ℤ) ⧸ (Gamma0 L).withCenter, ∫ z in (q.out)⁻¹ • ModularGroup.fdo, h z := by
  classical
  unfold repsIntegral
  rw [← Fin.sum_univ_fun_getElem R]
  let e : Fin R.length → SL(2, ℤ) ⧸ (Gamma0 L).withCenter := fun i ↦ QuotientGroup.mk (R[i.1])⁻¹
  have hmem : ∀ g : SL(2, ℤ), g ∈ (Gamma0 L).withCenter ↔ g ∈ Gamma0 L := by
    intro g; rw [withCenter_Gamma0]
  have he : Function.Bijective e := by
    constructor
    · intro i j hij
      have := QuotientGroup.eq.mp hij
      rw [inv_inv, hmem] at this
      obtain ⟨k, -, hk⟩ := hR R[i.1]
      have hi : R[i.1] * (R.get i)⁻¹ ∈ Gamma0 L := by simp
      have hj : R[i.1] * (R.get j)⁻¹ ∈ Gamma0 L := by simpa using this
      exact (hk i hi).trans (hk j hj).symm
    · intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        obtain ⟨i, hi, -⟩ := hR g⁻¹
        refine ⟨i, ?_⟩
        show QuotientGroup.mk (R[i.1])⁻¹ = QuotientGroup.mk g
        rw [QuotientGroup.eq, inv_inv, hmem]
        have := Subgroup.inv_mem _ hi
        simpa [mul_inv_rev] using this
  rw [← Fintype.sum_bijective e he (fun i ↦ ∫ τ in ModularGroup.fd, h (R[i.1] • τ))
    (fun q ↦ ∫ z in (q.out)⁻¹ • ModularGroup.fdo, h z)]
  intro i
  -- `(e i).out = R_i⁻¹ η` with `η ∈ Γ₀(L)`
  have hq : QuotientGroup.mk ((e i).out) = e i := QuotientGroup.out_eq' (e i)
  have hη : R[i.1] * (e i).out ∈ Gamma0 L := by
    have := QuotientGroup.eq.mp (hq.trans rfl : (QuotientGroup.mk ((e i).out) :
      SL(2, ℤ) ⧸ (Gamma0 L).withCenter) = QuotientGroup.mk (R[i.1])⁻¹)
    rw [hmem] at this
    have := Subgroup.inv_mem _ this
    simpa [mul_inv_rev] using this
  rw [setIntegral_SL_smul]
  have hae : (ModularGroup.fd : Set ℍ) =ᵐ[volume] ModularGroup.fdo := ModularGroup.fd_ae_eq_fdo
  rw [← setIntegral_congr_set hae]
  refine setIntegral_congr_fun measurableSet_fd fun τ _ ↦ ?_
  have : ((e i).out)⁻¹ = (R[i.1] * (e i).out)⁻¹ * R[i.1] := by group
  rw [this, mul_smul, hh _ (Subgroup.inv_mem _ hη)]

/-! ### (C) The strip -/

lemma stripPt_eq {x y : ℝ} (hy : 0 < y) :
    stripPt x y = UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I) := by
  have him : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos him, stripPt, dif_pos hy]

lemma continuous_Fs {G : ℍ → ℂ} (hG : Continuous G) (s : ℂ) : Continuous (Fs G s) := by
  unfold Fs
  refine hG.mul (Continuous.cpow ?_ continuous_const fun z ↦ ?_)
  · exact Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im
  · exact Complex.ofReal_mem_slitPlane.mpr z.im_pos

lemma norm_cpow_im (y : ℝ) (hy : 0 < y) (s : ℂ) : ‖(y : ℂ) ^ s‖ = y ^ s.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hy s

lemma integrableOn_Fs_strip {G : ℍ → ℂ} (hG : Continuous G) (s : ℂ)
    (hint : IntegrableOn (fun p : ℝ × ℝ ↦ ‖G (stripPt p.1 p.2)‖ * p.2 ^ (s.re - 2)) (Icc 0 1 ×ˢ Ioi 0)) :
    IntegrableOn (Fs G s) (Milne.stripSet 1) := by
  rw [← Milne.integrable_stripH_iff]
  have hmeas : MeasurableSet (Icc (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) := measurableSet_Icc.prod measurableSet_Ioi
  have hB : Integrable ((Icc (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)).indicator
      (fun p : ℝ × ℝ ↦ ‖G (stripPt p.1 p.2)‖ * p.2 ^ (s.re - 2))) :=
    (integrable_indicator_iff hmeas).2 hint
  refine hB.mono' ?_ ?_
  · unfold Milne.stripH
    rw [aestronglyMeasurable_indicator_iff (measurableSet_Ico.prod measurableSet_Ioi)]
    exact (Milne.continuousOn_stripH 1 (continuous_Fs hG s)).aestronglyMeasurable
      (measurableSet_Ico.prod measurableSet_Ioi)
  · refine Filter.Eventually.of_forall fun p ↦ ?_
    by_cases hp : p ∈ Ico (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)
    · have hy : 0 < p.2 := hp.2
      have hp' : p ∈ Icc (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ) := ⟨Ico_subset_Icc_self hp.1, hp.2⟩
      simp only [Milne.stripH, Set.indicator_of_mem hp, Set.indicator_of_mem hp']
      rw [norm_smul, Real.norm_of_nonneg (by positivity), ← stripPt_eq hy, Fs, norm_mul]
      have him : (stripPt p.1 p.2).im = p.2 := by
        rw [stripPt, dif_pos hy]; show ((p.1 : ℂ) + p.2 * Complex.I).im = p.2; simp
      rw [him, norm_cpow_im _ hy, Real.rpow_sub hy, Real.rpow_two]
      apply le_of_eq; field_simp
    · simp only [Milne.stripH, Set.indicator_of_notMem hp, norm_zero]
      exact Set.indicator_nonneg (fun q (hq : q ∈ Icc (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) ↦ mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (le_of_lt hq.2) _)) _

lemma integral_Fs_strip {G : ℍ → ℂ} (s : ℂ) (hF : IntegrableOn (Fs G s) (Milne.stripSet 1)) :
    ∫ z in Milne.stripSet 1, Fs G s z = stripMellin G s := by
  rw [Milne.integral_stripSet one_pos _ hF, stripMellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
  have hy : 0 < y := hy
  have hx : ∀ x : ℝ, Fs G s (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) =
      G (stripPt x y) * (y : ℂ) ^ s := by
    intro x
    rw [← stripPt_eq hy, Fs]
    congr 2
    rw [stripPt, dif_pos hy]; simp [UpperHalfPlane.im]
  simp_rw [hx]
  rw [intervalIntegral.integral_mul_const, Complex.real_smul]
  have hne : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [Complex.cpow_sub _ _ hne, Complex.cpow_two]
  push_cast
  field_simp

/-! ### The theorem -/

/-- **The Rankin–Selberg unfolding principle** (Rankin 1939 `rankin1939`, Selberg 1940 `selberg1940`): the named
input `RankinUnfolding` of `Abstract/ShimuraRankin.lean` holds. -/
@[kb "rankin1939" "the unfolding of a Petersson-type integral against an Eisenstein series, proved [unverified]"]
theorem rankinUnfolding : RankinUnfolding := by
  refine ⟨fun L lam ω R hL hR G hGc hU s hs hint ↦ ?_⟩
  have : NeZero L := ⟨by omega⟩
  rcases parity_or_zero hU with hpar | hG0
  swap
  · subst hG0
    simp [repsIntegral, stripMellin]
  set C := 2 * LSeries (fun n ↦ ω n) (2 * s)
  have hpt : ∀ z, G z * eisensteinLattice L lam ω z s = C * Hs (L := L) G s z := fun z ↦
    mul_eisensteinLattice_eq hL hpar hU z hs
  have hinv : ∀ γ ∈ Gamma0 L, ∀ z : ℍ, (fun τ ↦ G τ * eisensteinLattice L lam ω τ s) (γ • z) =
      (fun τ ↦ G τ * eisensteinLattice L lam ω τ s) z := by
    intro γ hγ z
    simp only [hpt, Hs_invariant hpar hU s γ hγ z]
  rw [repsIntegral_eq_sum_quotient hR _ hinv]
  simp_rw [hpt, integral_const_mul]
  rw [← Finset.mul_sum]
  congr 1
  -- unfolding
  have hFs := integrableOn_Fs_strip hGc s hint
  rw [← widthAtInfty_Gamma0 L] at hFs
  obtain ⟨hix, hsN, hsum⟩ := Milne.unfolding_terms (Gamma0 L) (Fs G s)
    (fun β hβ z ↦ Fs_stab hpar hU s β hβ z) hFs
  rw [widthAtInfty_Gamma0 L, integral_Fs_strip s (by rwa [widthAtInfty_Gamma0 L] at hFs)] at hsum
  rw [← hsum]
  set P : SL(2, ℤ) ⧸ (Gamma0 L).withCenter → Set ℍ := fun q ↦ (q.out)⁻¹ • ModularGroup.fdo
  have hsub : ∀ q, P q ⊆ ⋃ q, P q := fun q ↦ Set.subset_iUnion P q
  -- on each piece, the integral of the series is the series of the integrals
  have hpiece : ∀ q, ∫ z in P q, Hs (L := L) G s z =
      ∑' x : X L, ∫ z in P q, Fs G s (rep L x • z) := by
    intro q
    refine (integral_tsum_of_summable_integral_norm (fun x ↦ (hix x).mono_set (hsub q)) ?_).symm
    refine Summable.of_nonneg_of_le (fun x ↦ integral_nonneg fun _ ↦ norm_nonneg _) (fun x ↦ ?_) hsN
    exact setIntegral_mono_set ((hix x).norm) (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
      (Filter.Eventually.of_forall (hsub q))
  simp_rw [P] at hpiece
  rw [Finset.sum_congr rfl fun q _ ↦ hpiece q]
  have hsumm : ∀ q ∈ (Finset.univ : Finset (SL(2, ℤ) ⧸ (Gamma0 L).withCenter)),
      Summable fun x : X L ↦ ∫ z in P q, Fs G s (rep L x • z) := by
    intro q _
    refine Summable.of_norm_bounded hsN fun x ↦ ?_
    exact (norm_integral_le_integral_norm _).trans
      (setIntegral_mono_set ((hix x).norm) (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
        (Filter.Eventually.of_forall (hsub q)))
  rw [← Summable.tsum_finsetSum hsumm]
  refine tsum_congr fun x ↦ ?_
  rw [integral_iUnion_fintype (fun q ↦ (ModularGroup.isOpen_smul_fdo _).measurableSet)
    (ModularGroup.pairwise_disjoint_smul_fdo_out_withCenter (Gamma0 L))
    (fun q ↦ (hix x).mono_set (hsub q))]
  rfl

end RankinUnfold

end ModularFormsKB.HalfIntegral