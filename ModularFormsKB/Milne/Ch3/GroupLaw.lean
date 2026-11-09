import ModularFormsKB.Milne.Ch3.LatticeInvariants

/-!
# Milne, Chapter 3: `z ↦ (℘(z), ℘'(z)/2)` is a group homomorphism

The point map `ℂ → E(Λ)` is additive for Mathlib's group law on `E(Λ)`
(`weierstrassPoint_add`). For distinct `x`-coordinates this is the addition formula (Proposition 3.9) together
with the fact that `-(z + w)` lies on the line through `P(z)` and `P(w)` (the divisor of the line function); for
doubling we use the tangent line, whose divisor is `2(z) + (-2z) - 3(0)`, and the factorisation of the cubic with
a double root.
-/

open Complex Filter Topology Set PeriodPair WeierstrassCurve

namespace ModularFormsKB.Milne

noncomputable section

variable {L : PeriodPair}

/-- An effective-off-`0` divisor of degree zero with a pole of order three at `0`, a zero of order at least two
at `p`, and sum zero, is `2(p) + (-2p) - 3(0)`. -/
theorem divisor_three_double {D : Torus L →₀ ℤ} {p : Torus L} (hp : p ≠ 0) (h0 : D 0 = -3)
    (hpos : ∀ x, x ≠ 0 → 0 ≤ D x) (hp2 : 2 ≤ D p) (hdeg : degT L D = 0) (hsum : sumT L D = 0) :
    D = Finsupp.single p 2 + Finsupp.single (-p - p) 1 - Finsupp.single 0 3 := by
  classical
  set E := D + Finsupp.single 0 3 - Finsupp.single p 2
  have hE : ∀ x, 0 ≤ E x := by
    intro x
    have e : E x = D x + (if x = 0 then 3 else 0) - (if x = p then 2 else 0) := by
      simp [E, Finsupp.single_apply, eq_comm]
    rw [e]
    by_cases hx0 : x = 0
    · subst hx0
      rw [ite_eq_left rfl, ite_eq_right (Ne.symm hp), h0]; omega
    · by_cases hxp : x = p
      · subst hxp; rw [ite_eq_right hx0, ite_eq_left rfl]; omega
      · rw [ite_eq_right hx0, ite_eq_right hxp]; have := hpos x hx0; omega
  have hdE : degT L E = 1 := by
    simp only [E, map_sub, map_add, hdeg, degT_single]; norm_num
  obtain ⟨w, hw⟩ := eq_single_of_nonneg_of_degT_eq_one hE hdE
  have hD : D = Finsupp.single p 2 + Finsupp.single w 1 - Finsupp.single 0 3 := by
    have : D = E + Finsupp.single p 2 - Finsupp.single 0 3 := by simp only [E]; abel
    rw [this, hw]; abel
  have hw' : w = -p - p := by
    rw [hD] at hsum
    simp only [map_sub, map_add, sumT_single, one_smul, smul_zero, sub_zero] at hsum
    rw [← sub_eq_zero, ← hsum, two_zsmul]; abel
  rw [hD, hw']

theorem deriv_line {a b z : ℂ} (hz : z ∉ L.lattice) :
    deriv (fun u ↦ ℘'[L] u - a * ℘[L] u - b) z = deriv ℘'[L] z - a * ℘'[L] z := by
  have h1 := (analyticAt_derivWeierstrassP hz).differentiableAt.hasDerivAt
  have h2 : HasDerivAt ℘[L] (℘'[L] z) z := by
    have := (analyticAt_weierstrassP hz).differentiableAt.hasDerivAt
    rwa [deriv_weierstrassP] at this
  exact ((h1.fun_sub (h2.const_mul a)).sub_const b).deriv

/-- **The divisor of the tangent line function** at `P(p)`, `p ∉ Λ`, is `2(p) + (-2p) - 3(0)`. -/
theorem ellDiv_tangent {p : ℂ} (hp : p ∉ L.lattice) {a b : ℂ} (hap : ℘'[L] p = a * ℘[L] p + b)
    (hder : deriv ℘'[L] p = a * ℘'[L] p) :
    ellDiv (ellFun_line (L := L) a b).1 = Finsupp.single (tmk L p) 2 +
      Finsupp.single (-tmk L p - tmk L p) 1 - Finsupp.single 0 3 := by
  have hF := ellFun_line (L := L) a b
  have han : ∀ z, z ∉ L.lattice → AnalyticAt ℂ (fun z ↦ ℘'[L] z - a * ℘[L] z - b) z := fun z hz ↦
    ((analyticAt_derivWeierstrassP hz).sub (analyticAt_const.mul (analyticAt_weierstrassP hz))).sub
      analyticAt_const
  refine divisor_three_double (tmk_ne_zero hp) ?_ ?_ ?_
    (degT_ellDiv hF.1 hF.not_eventually_zero) (sumT_ellDiv hF.1 hF.not_eventually_zero)
  · rw [← tmk_zero, ellDiv_tmk, ordZ, meromorphicOrderAt_line _ _ L.lattice.zero_mem]; rfl
  · intro x hx
    obtain ⟨z, rfl⟩ := tmk_surjective x
    have hz : z ∉ L.lattice := fun h ↦ hx (tmk_eq_zero_iff.2 h)
    rw [ellDiv_tmk]
    exact ordZ_nonneg_of_analyticAt (han z hz)
  · rw [ellDiv_tmk]
    have h2 : ((2 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun z ↦ ℘'[L] z - a * ℘[L] z - b) p := by
      rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (han p hp)]
      intro i hi
      interval_cases i
      · simp only [iteratedDeriv_zero]; rw [hap]; ring
      · rw [iteratedDeriv_one, deriv_line hp, hder, sub_self]
    have hne' : analyticOrderAt (fun z ↦ ℘'[L] z - a * ℘[L] z - b) p ≠ ⊤ := by
      intro h; apply hF.2 p; rw [(han p hp).meromorphicOrderAt_eq, h]; rfl
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne'
    rw [← hn] at h2
    have h2' : 2 ≤ n := by exact_mod_cast h2
    rw [ordZ, (han p hp).meromorphicOrderAt_eq, ← hn, ENat.map_natCast, WithTop.untop₀_coe]
    exact_mod_cast h2'

/-- The cubic `4X³ - g₂X - g₃ - (aX + b)²` with a double root `x` factors as `4(X - x)²(X - (a²/4 - 2x))`. -/
theorem cubic_factor_double {g₂ g₃ a b x X : ℂ}
    (h1 : 4 * x ^ 3 - g₂ * x - g₃ - (a * x + b) ^ 2 = 0)
    (h2 : 12 * x ^ 2 - g₂ - 2 * a * (a * x + b) = 0) :
    4 * X ^ 3 - g₂ * X - g₃ - (a * X + b) ^ 2 = 4 * ((X - x) * ((X - x) * (X - (a ^ 2 / 4 - 2 * x)))) := by
  linear_combination h1 + (X - x) * h2

/-- **The duplication formula** `℘(2z) = (℘''(z)/(2℘'(z)))² - 2℘(z)`, in the form `a = ℘''/℘'`. -/
theorem weierstrassP_add_self {z : ℂ} (hz : z ∉ L.lattice) (h2z : z + z ∉ L.lattice) :
    ℘[L] (z + z) = (deriv ℘'[L] z / ℘'[L] z) ^ 2 / 4 - 2 * ℘[L] z := by
  classical
  have hd : ℘'[L] z ≠ 0 := by
    intro h0
    apply h2z
    have := tmk_eq_neg_of_derivWeierstrassP_eq_zero hz h0
    rw [← tmk_eq_zero_iff, tmk_add]; nth_rewrite 2 [this]; exact add_neg_cancel _
  set x := ℘[L] z
  set a := deriv ℘'[L] z / ℘'[L] z
  set b := ℘'[L] z - a * x
  have hap : ℘'[L] z = a * x + b := by simp only [b]; ring
  have hder : deriv ℘'[L] z = a * ℘'[L] z := by simp only [a]; field_simp
  set r := a ^ 2 / 4 - 2 * x
  obtain ⟨v, hv, hvr⟩ := exists_weierstrassP_eq (L := L) r
  have hode := deriv_derivWeierstrassP_eq L hz
  have hcub : ∀ u, u ∉ L.lattice →
      4 * ((℘[L] u - x) * ((℘[L] u - x) * (℘[L] u - ℘[L] v))) =
        (℘'[L] u - a * ℘[L] u - b) * (℘'[L] u - (-a) * ℘[L] u - (-b)) := by
    intro u hu
    have e1 : 4 * x ^ 3 - L.g₂ * x - L.g₃ - (a * x + b) ^ 2 = 0 := by
      rw [← hap, L.derivWeierstrassP_sq z hz]; ring
    have e2 : 12 * x ^ 2 - L.g₂ - 2 * a * (a * x + b) = 0 := by
      rw [← hap]; linear_combination 2 * hder - 2 * hode
    have := cubic_factor_double (X := ℘[L] u) e1 e2
    rw [hvr, ← this]
    linear_combination (-1 : ℂ) * (L.derivWeierstrassP_sq u hu)
  have hA1 := ellFun_weierstrassP_sub (L := L) x
  have hA3 := ellFun_weierstrassP_sub (L := L) (℘[L] v)
  have hA := (ellFun_const (L := L) (by norm_num : (4 : ℂ) ≠ 0)).mul (hA1.mul (hA1.mul hA3))
  have hh := ellFun_line (L := L) a b
  have hk := ellFun_line (L := L) (-a) (-b)
  have hAB : ellDiv hA.1 = ellDiv (hh.mul hk).1 := ellDiv_congr hA.1 (hh.mul hk).1 hcub
  rw [ellDiv_mul (ellFun_const (L := L) (by norm_num : (4 : ℂ) ≠ 0)) (hA1.mul (hA1.mul hA3)),
    ellDiv_const (by norm_num : (4 : ℂ) ≠ 0), ellDiv_mul hA1 (hA1.mul hA3), ellDiv_mul hA1 hA3,
    ellDiv_weierstrassP_sub hz, ellDiv_weierstrassP_sub hv, ellDiv_mul hh hk,
    ellDiv_tangent hz hap hder] at hAB
  have hnz : -z ∉ L.lattice := by simpa using hz
  have hap' : ℘'[L] (-z) = -a * ℘[L] (-z) + -b := by
    rw [L.derivWeierstrassP_neg, L.weierstrassP_neg, hap]; ring
  have hder' : deriv ℘'[L] (-z) = -a * ℘'[L] (-z) := by
    rw [deriv_derivWeierstrassP_eq L hnz, L.weierstrassP_neg, ← hode, hder, L.derivWeierstrassP_neg]
    ring
  rw [ellDiv_tangent hnz hap' hder'] at hAB
  simp only [tmk_neg, neg_neg, zero_add] at hAB
  set w := -tmk L z - tmk L z
  have e : tmk L z - -tmk L z = -w := by simp only [w]; abel
  rw [e] at hAB
  have hvw : Finsupp.single (tmk L v) (1 : ℤ) + Finsupp.single (-tmk L v) 1 =
      Finsupp.single w 1 + Finsupp.single (-w) 1 := by
    have h6 : Finsupp.single (0 : Torus L) (2 : ℤ) + Finsupp.single 0 2 + Finsupp.single 0 2 =
        Finsupp.single 0 3 + Finsupp.single 0 3 := by
      rw [← Finsupp.single_add, ← Finsupp.single_add, ← Finsupp.single_add]; norm_num
    have h2z' : Finsupp.single (tmk L z) (2 : ℤ) = Finsupp.single (tmk L z) 1 + Finsupp.single (tmk L z) 1 := by
      rw [← Finsupp.single_add]; norm_num
    have h2z'' : Finsupp.single (-tmk L z) (2 : ℤ) =
        Finsupp.single (-tmk L z) 1 + Finsupp.single (-tmk L z) 1 := by
      rw [← Finsupp.single_add]; norm_num
    rw [h2z', h2z''] at hAB
    exact eq_of_sub_eq_combo hAB h6 (by abel)
  have hw1 := congrArg (fun D : Torus L →₀ ℤ ↦ D w) hvw
  simp only [Finsupp.add_apply, Finsupp.single_apply] at hw1
  have hzz : tmk L (z + z) = tmk L v ∨ tmk L (z + z) = -tmk L v := by
    have e : tmk L (z + z) = -w := by simp only [w, tmk_add]; abel
    rw [e]
    by_cases h1 : tmk L v = w
    · right; rw [h1]
    · by_cases h2 : -tmk L v = w
      · left; rw [← h2, neg_neg]
      · rw [ite_eq_right h1, ite_eq_right h2] at hw1
        split_ifs at hw1 <;> omega
  rw [weierstrassP_eq_of_tmk hzz, hvr]

/-- A point of the line function's zero set: if `tmk u` is in the support of its divisor, `u` lies on the line. -/
theorem line_eq_of_ellDiv_pos {a b u : ℂ} (hu : u ∉ L.lattice)
    (h : 1 ≤ ellDiv (ellFun_line (L := L) a b).1 (tmk L u)) : ℘'[L] u = a * ℘[L] u + b := by
  rw [ellDiv_tmk] at h
  have := eq_zero_of_one_le_ordZ (f := fun z ↦ ℘'[L] z - a * ℘[L] z - b)
    (((analyticAt_derivWeierstrassP hu).sub (analyticAt_const.mul (analyticAt_weierstrassP hu))).sub
      analyticAt_const) h
  linear_combination this

/-- **The point map is a group homomorphism**: `P(z + w) = P(z) + P(w)`. -/
theorem weierstrassPoint_add (z w : ℂ) :
    L.weierstrassPoint (z + w) = L.weierstrassPoint z + L.weierstrassPoint w := by
  classical
  by_cases hz : z ∈ L.lattice
  · rw [L.weierstrassPoint_of_mem hz, zero_add, add_comm, L.weierstrassPoint_add_coe w ⟨z, hz⟩]
  by_cases hw : w ∈ L.lattice
  · rw [L.weierstrassPoint_of_mem hw, add_zero, L.weierstrassPoint_add_coe z ⟨w, hw⟩]
  by_cases hzw : z + w ∈ L.lattice
  · rw [L.weierstrassPoint_of_mem hzw]
    have : w = -z + (z + w) := by ring
    rw [this, L.weierstrassPoint_add_coe (-z) ⟨_, hzw⟩, L.weierstrassPoint_neg, add_neg_cancel]
  rw [L.weierstrassPoint_of_notMem hz, L.weierstrassPoint_of_notMem hw,
    L.weierstrassPoint_of_notMem hzw]
  by_cases hx : ℘[L] z = ℘[L] w
  · -- doubling
    have htw : tmk L z = tmk L w := by
      rcases tmk_eq_or_eq_neg_of_weierstrassP_eq hz hw hx with h | h
      · exact h
      · exact absurd (by rw [← tmk_eq_zero_iff, tmk_add, h, neg_add_cancel]) hzw
    have hwz : w = z + (w - z) := by ring
    have hwzL : w - z ∈ L.lattice := tmk_eq_tmk_iff.1 htw.symm
    have hy : ℘'[L] w = ℘'[L] z := by rw [hwz, L.derivWeierstrassP_add_coe z ⟨_, hwzL⟩]
    have h2z : z + z ∉ L.lattice := fun h ↦ hzw (by
      have : z + w = (z + z) + (w - z) := by ring
      rw [this]; exact add_mem h hwzL)
    have hzz : z + w = (z + z) + (w - z) := by ring
    have hP : ℘[L] (z + w) = ℘[L] (z + z) := by rw [hzz, L.weierstrassP_add_coe _ ⟨_, hwzL⟩]
    have hP' : ℘'[L] (z + w) = ℘'[L] (z + z) := by rw [hzz, L.derivWeierstrassP_add_coe _ ⟨_, hwzL⟩]
    have hd : ℘'[L] z ≠ 0 := by
      intro h0; apply h2z
      have := tmk_eq_neg_of_derivWeierstrassP_eq_zero hz h0
      rw [← tmk_eq_zero_iff, tmk_add]; nth_rewrite 2 [this]; exact add_neg_cancel _
    have hyne : ℘'[L] z / 2 ≠ L.weierstrassCurve.toAffine.negY (℘[L] w) (℘'[L] w / 2) := by
      simp only [Affine.negY, weierstrassCurve_a₁, weierstrassCurve_a₃, zero_mul, sub_zero, hy]
      intro h; apply hd; linear_combination h
    have hxw : ℘[L] z = ℘[L] w := hx
    simp only [Affine.Point.add_some (fun h ↦ hyne h.2), Affine.Point.some.injEq]
    set a := deriv ℘'[L] z / ℘'[L] z
    have hslope : L.weierstrassCurve.toAffine.slope (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2) =
        a / 2 := by
      rw [Affine.slope_of_Y_ne hx hyne]
      simp only [Affine.negY, weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃,
        weierstrassCurve_a₄, zero_mul, sub_zero, mul_zero, add_zero, a, deriv_derivWeierstrassP_eq L hz]
      field_simp; ring
    have hdup := weierstrassP_add_self hz h2z
    rw [hslope]
    -- the third point `-(z + z)` is on the tangent line
    set b := ℘'[L] z - a * ℘[L] z
    have hap : ℘'[L] z = a * ℘[L] z + b := by simp only [b]; ring
    have hder : deriv ℘'[L] z = a * ℘'[L] z := by simp only [a]; field_simp
    have hu : -(z + z) ∉ L.lattice := by rwa [neg_mem_iff]
    have hline : ℘'[L] (-(z + z)) = a * ℘[L] (-(z + z)) + b := by
      refine line_eq_of_ellDiv_pos hu ?_
      rw [ellDiv_tangent hz hap hder]
      simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply, tmk_neg, tmk_add]
      have h0 : (0 : Torus L) ≠ -(tmk L z + tmk L z) := by
        intro h; apply hu; rw [← tmk_eq_zero_iff, tmk_neg, tmk_add, ← h]
      rw [ite_eq_right h0, show -tmk L z - tmk L z = -(tmk L z + tmk L z) by abel, ite_eq_left rfl]
      split_ifs <;> omega
    rw [L.derivWeierstrassP_neg, L.weierstrassP_neg] at hline
    refine ⟨?_, ?_⟩
    · rw [hP, hdup]; simp only [Affine.addX, weierstrassCurve_a₁, weierstrassCurve_a₂]; rw [← hxw]; ring
    · rw [hP', Affine.addY, Affine.negAddY, Affine.negY]
      simp only [Affine.addX, weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃]
      rw [← hxw]
      have e : ℘'[L] (z + z) = -(a * ℘[L] (z + z) + b) := by linear_combination -hline
      rw [e, hdup]; simp only [b]; ring
  · -- distinct `x`-coordinates
    have hadd := weierstrassAdditionStatement.out L z w hz hw hzw hx
    have hd : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.2 hx
    simp only [Affine.Point.add_of_X_ne hx, Affine.Point.some.injEq]
    set a := (℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w)
    set b := ℘'[L] z - a * ℘[L] z
    have hap : ℘'[L] z = a * ℘[L] z + b := by simp only [b]; ring
    have haq : ℘'[L] w = a * ℘[L] w + b := by simp only [b, a]; field_simp; ring
    have htmk : tmk L z ≠ tmk L w := fun h ↦ hx (weierstrassP_eq_of_tmk (Or.inl h))
    have hu : -(z + w) ∉ L.lattice := by rwa [neg_mem_iff]
    have hline : ℘'[L] (-(z + w)) = a * ℘[L] (-(z + w)) + b := by
      refine line_eq_of_ellDiv_pos hu ?_
      rw [ellDiv_line hz hw htmk hap haq]
      simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply, tmk_neg, tmk_add]
      have h0 : (0 : Torus L) ≠ -(tmk L z + tmk L w) := by
        intro h; apply hu; rw [← tmk_eq_zero_iff, tmk_neg, tmk_add, ← h]
      rw [ite_eq_right h0, show -tmk L z - tmk L w = -(tmk L z + tmk L w) by abel, ite_eq_left rfl]
      split_ifs <;> omega
    rw [L.derivWeierstrassP_neg, L.weierstrassP_neg] at hline
    have hslope : L.weierstrassCurve.toAffine.slope (℘[L] z) (℘[L] w) (℘'[L] z / 2) (℘'[L] w / 2) =
        a / 2 := by
      rw [Affine.slope_of_X_ne hx]; simp only [a]; field_simp
    rw [hslope]
    refine ⟨?_, ?_⟩
    · rw [hadd]; simp only [Affine.addX, weierstrassCurve_a₁, weierstrassCurve_a₂, a]; ring
    · rw [Affine.addY, Affine.negAddY, Affine.negY]
      simp only [Affine.addX, weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃]
      have e : ℘'[L] (z + w) = -(a * ℘[L] (z + w) + b) := by linear_combination -hline
      have hadd' : ℘[L] (z + w) = (a / 2) ^ 2 - ℘[L] z - ℘[L] w := by rw [hadd]; simp only [a]; ring
      rw [e, hadd']; simp only [b]; ring

end

end ModularFormsKB.Milne
