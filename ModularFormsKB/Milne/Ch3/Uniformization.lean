import ModularFormsKB.Milne.Ch3.WeierstrassDivisors

/-!
# Milne, Chapter 3: the Weierstrass parametrisation and the addition formula

From the divisor of `℘ - ℘(v)` (`ellDiv_weierstrassP_sub`):

* `℘` takes every complex value off `Λ` (`exists_weierstrassP_eq`), and `℘(z) = ℘(w)` exactly when
  `z ≡ ±w` (`tmk_eq_or_eq_neg_of_weierstrassP_eq`);
* the map `[z] ↦ (℘(z), ℘'(z)/2)` is a bijection `ℂ/Λ → E(Λ)` (`bijective_weierstrassPoint`, the first two parts
  of Milne's Proposition 3.12).

From the divisor of the line function (`ellDiv_line`) and the factorisation of the cubic, the addition formula
(Milne, Proposition 3.9, `weierstrassAdditionStatement`).
-/

open Complex Filter Topology Set PeriodPair

namespace ModularFormsKB.Milne

noncomputable section

variable {L : PeriodPair}

/-! ### Values of `℘` -/

/-- `℘` takes every value. -/
theorem exists_weierstrassP_eq (c : ℂ) : ∃ v : ℂ, v ∉ L.lattice ∧ ℘[L] v = c := by
  classical
  have hF := ellFun_weierstrassP_sub (L := L) c
  set D := ellDiv hF.1
  have h0 : D 0 = -2 := by
    rw [← tmk_zero, ellDiv_tmk, ordZ, meromorphicOrderAt_weierstrassP_sub _ L.lattice.zero_mem]; rfl
  have hdeg : degT L D = 0 := degT_ellDiv hF.1 hF.not_eventually_zero
  by_contra hcon
  push Not at hcon
  have hle : ∀ x, x ≠ 0 → D x ≤ 0 := by
    intro x hx
    obtain ⟨z, rfl⟩ := tmk_surjective x
    have hz : z ∉ L.lattice := fun h ↦ hx (tmk_eq_zero_iff.2 h)
    rw [ellDiv_tmk]
    by_contra hpos
    push Not at hpos
    exact hcon z hz (sub_eq_zero.1 (eq_zero_of_one_le_ordZ (f := fun z ↦ ℘[L] z - c)
      ((analyticAt_weierstrassP hz).sub analyticAt_const) hpos))
  have hneg : degT L (D - Finsupp.single 0 (D 0)) ≤ 0 := by
    rw [degT_apply]
    refine Finset.sum_nonpos fun x _ ↦ ?_
    rw [Finsupp.sub_apply, Finsupp.single_apply]
    split_ifs with h
    · rw [← h]; simp
    · simpa using hle x (Ne.symm h)
  have e : degT L D = degT L (D - Finsupp.single 0 (D 0)) + D 0 := by
    rw [map_sub, degT_single]; ring
  omega

open Classical in
theorem ellDiv_weierstrassP_sub_apply {v : ℂ} (hv : v ∉ L.lattice) (x : Torus L) :
    ellDiv (ellFun_weierstrassP_sub (L := L) (℘[L] v)).1 x =
      (if tmk L v = x then 1 else 0) + (if -tmk L v = x then 1 else 0) - (if (0 : Torus L) = x then 2 else 0) := by
  rw [ellDiv_weierstrassP_sub hv]
  simp [Finsupp.single_apply]

/-- `℘(z) = ℘(w)` (off `Λ`) only if `z ≡ ±w`. -/
theorem tmk_eq_or_eq_neg_of_weierstrassP_eq {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (h : ℘[L] z = ℘[L] w) : tmk L z = tmk L w ∨ tmk L z = -tmk L w := by
  have hF := ellFun_weierstrassP_sub (L := L) (℘[L] w)
  have h1 : 1 ≤ ellDiv hF.1 (tmk L z) := by
    rw [ellDiv_tmk]
    exact one_le_ordZ_of_eq_zero ((analyticAt_weierstrassP hz).sub analyticAt_const)
      (by simp [h]) (hF.2 z)
  rw [ellDiv_weierstrassP_sub_apply hw, ite_eq_right (Ne.symm (tmk_ne_zero hz))] at h1
  by_contra hne
  push Not at hne
  rw [ite_eq_right (Ne.symm hne.1), ite_eq_right (Ne.symm hne.2)] at h1
  omega

/-- If `℘'(v) = 0` then `v` is a half period: `[v] = -[v]`. -/
theorem tmk_eq_neg_of_derivWeierstrassP_eq_zero {v : ℂ} (hv : v ∉ L.lattice) (h : ℘'[L] v = 0) :
    tmk L v = -tmk L v := by
  by_contra hne
  have hF := ellFun_weierstrassP_sub (L := L) (℘[L] v)
  have h1 : ellDiv hF.1 (tmk L v) = 1 := by
    rw [ellDiv_weierstrassP_sub_apply hv, ite_eq_left rfl, ite_eq_right (fun h' ↦ hne h'.symm),
      ite_eq_right (Ne.symm (tmk_ne_zero hv))]
    · rfl
  rw [ellDiv_tmk] at h1
  have hord : meromorphicOrderAt (fun z ↦ ℘[L] z - ℘[L] v) v = ((1 : ℤ) : WithTop ℤ) := by
    rw [hF.ordZ_eq, h1]
  have hd := meromorphicOrderAt_deriv_eq_sub_one (by norm_num) hord
  have hderiv : deriv (fun z ↦ ℘[L] z - ℘[L] v) = ℘'[L] := by
    funext z; rw [deriv_sub_const, deriv_weierstrassP]
  rw [hderiv] at hd
  have := one_le_ordZ_of_eq_zero (analyticAt_derivWeierstrassP hv) h (by rw [hd]; exact WithTop.coe_ne_top)
  rw [ordZ, hd] at this
  exact absurd this (by decide)

/-! ### Proposition 3.12: the bijection `ℂ/Λ → E(Λ)` -/

theorem complexTorus_mk_eq_of_sub_mem {z w : ℂ} (h : z - w ∈ L.lattice) :
    ComplexTorus.mk L z = ComplexTorus.mk L w := by
  unfold ComplexTorus.mk
  refine Quotient.sound ⟨⟨z - w, h⟩, ?_⟩
  show (z - w) + w = z
  ring

theorem sub_mem_of_complexTorus_mk_eq {z w : ℂ} (h : ComplexTorus.mk L z = ComplexTorus.mk L w) :
    z - w ∈ L.lattice := by
  unfold ComplexTorus.mk at h
  obtain ⟨⟨ω, hω⟩, hω'⟩ := Quotient.exact h
  have : ω + w = z := hω'
  rw [← this]; simpa using hω

/-- The point map on the torus. -/
def torusPoint (L : PeriodPair) : ComplexTorus L → L.weierstrassCurve.toAffine.Point :=
  Quotient.lift L.weierstrassPoint fun a b ⟨⟨ω, hω⟩, h⟩ ↦ by
    have : ω + b = a := h
    rw [← this, add_comm]
    exact L.weierstrassPoint_add_coe b ⟨ω, hω⟩

theorem torusPoint_mk (z : ℂ) : torusPoint L (ComplexTorus.mk L z) = L.weierstrassPoint z := rfl

theorem weierstrassPoint_some {z : ℂ} (hz : z ∉ L.lattice) :
    ∃ h, L.weierstrassPoint z = .some (℘[L] z) (℘'[L] z / 2) h :=
  ⟨_, L.weierstrassPoint_of_notMem hz⟩

/-- The point map is injective modulo `Λ`. -/
theorem sub_mem_of_weierstrassPoint_eq {z w : ℂ} (h : L.weierstrassPoint z = L.weierstrassPoint w) :
    z - w ∈ L.lattice := by
  by_cases hz : z ∈ L.lattice
  · have hw : w ∈ L.lattice := by
      rw [L.weierstrassPoint_of_mem hz, eq_comm, L.weierstrassPoint_eq_zero_iff] at h; exact h
    exact sub_mem hz hw
  have hw : w ∉ L.lattice := fun hw ↦ hz (by
    rw [L.weierstrassPoint_of_mem hw, L.weierstrassPoint_eq_zero_iff] at h; exact h)
  rw [L.weierstrassPoint_of_notMem hz, L.weierstrassPoint_of_notMem hw] at h
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at h
  obtain ⟨hx, hy⟩ := h
  have hy' : ℘'[L] z = ℘'[L] w := by linear_combination 2 * hy
  rcases tmk_eq_or_eq_neg_of_weierstrassP_eq hz hw hx with h1 | h1
  · exact tmk_eq_tmk_iff.1 h1
  · -- `z ≡ -w`, so `℘'(w) = -℘'(w)`
    have hzw : z - (-w) ∈ L.lattice := tmk_eq_tmk_iff.1 (by rw [h1, tmk_neg])
    have hz' : ℘'[L] z = -℘'[L] w := by
      have : z = -w + (z - (-w)) := by ring
      rw [this, L.derivWeierstrassP_add_coe (-w) ⟨_, hzw⟩, L.derivWeierstrassP_neg]
    have h0 : ℘'[L] w = 0 := by linear_combination (hz' - hy') / 2
    have h2 := tmk_eq_neg_of_derivWeierstrassP_eq_zero hw h0
    exact tmk_eq_tmk_iff.1 (by rw [h1, ← h2])

theorem injective_torusPoint : Function.Injective (torusPoint L) := by
  intro x y h
  induction x using Quotient.inductionOn with | h z => ?_
  induction y using Quotient.inductionOn with | h w => ?_
  exact complexTorus_mk_eq_of_sub_mem (sub_mem_of_weierstrassPoint_eq h)

theorem surjective_torusPoint : Function.Surjective (torusPoint L) := by
  intro P
  rcases P with _ | ⟨x, y, hxy⟩
  · exact ⟨ComplexTorus.mk L 0, by rw [torusPoint_mk, L.weierstrassPoint_zero]; rfl⟩
  obtain ⟨v, hv, hvx⟩ := exists_weierstrassP_eq (L := L) x
  have heq := L.equation_weierstrassP hv
  have hxy' := hxy.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq hxy'
  simp only [weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, weierstrassCurve_a₄,
    weierstrassCurve_a₆, zero_mul, add_zero] at heq hxy'
  rw [hvx] at heq
  have hsq : (℘'[L] v / 2 - y) * (℘'[L] v / 2 + y) = 0 := by linear_combination heq - hxy'
  rcases mul_eq_zero.1 hsq with h | h
  · refine ⟨ComplexTorus.mk L v, ?_⟩
    rw [torusPoint_mk, L.weierstrassPoint_of_notMem hv]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hvx, by linear_combination h⟩
  · have hv' : -v ∉ L.lattice := by simpa using hv
    refine ⟨ComplexTorus.mk L (-v), ?_⟩
    rw [torusPoint_mk, L.weierstrassPoint_of_notMem hv']
    simp only [WeierstrassCurve.Affine.Point.some.injEq, L.weierstrassP_neg, L.derivWeierstrassP_neg]
    exact ⟨hvx, by linear_combination -h⟩

/-- **Milne, Proposition 3.12** (second part): `[z] ↦ (℘(z) : ℘'(z) : 1)` is a bijection `ℂ/Λ → E(Λ)`. -/
theorem bijective_weierstrassPoint (L : PeriodPair) :
    ∃ F : ComplexTorus L → L.weierstrassCurve.toAffine.Point,
      Function.Bijective F ∧ ∀ z, F (ComplexTorus.mk L z) = L.weierstrassPoint z :=
  ⟨torusPoint L, ⟨injective_torusPoint, surjective_torusPoint⟩, fun _ ↦ rfl⟩

/-! ### Proposition 3.9: the addition formula -/

theorem ellDiv_congr {f g : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f) (hg : IsDoublyPeriodic L.lattice g)
    (h : ∀ u, u ∉ L.lattice → f u = g u) : ellDiv hf = ellDiv hg := by
  ext x
  obtain ⟨z, rfl⟩ := tmk_surjective x
  simp only [ellDiv_tmk, ordZ]
  congr 1
  apply meromorphicOrderAt_congr
  filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds z),
    self_mem_nhdsWithin] with u hu hne
  refine h u fun hu' ↦ hu ⟨hu', hne⟩

theorem weierstrassP_eq_of_tmk {x y : ℂ} (h : tmk L x = tmk L y ∨ tmk L x = -tmk L y) :
    ℘[L] x = ℘[L] y := by
  rcases h with h | h
  · have hxy := tmk_eq_tmk_iff.1 h
    have : x = y + (x - y) := by ring
    rw [this, L.weierstrassP_add_coe y ⟨_, hxy⟩]
  · have hxy : x - -y ∈ L.lattice := tmk_eq_tmk_iff.1 (by rw [h, tmk_neg])
    have : x = -y + (x - -y) := by ring
    rw [this, L.weierstrassP_add_coe (-y) ⟨_, hxy⟩, L.weierstrassP_neg]

theorem eq_of_sub_eq_combo {G : Type*} [AddCommGroup G] {x y X Y P Q : G} (h : X = Y) (h' : P = Q)
    (hxy : x - y = (X - Y) + (P - Q)) : x = y := by
  rw [h, h', sub_self, sub_self, add_zero, sub_eq_zero] at hxy; exact hxy

/-- The cubic `4X³ - g₂X - g₃ - (aX + b)²` with two distinct roots `x₁, x₂` factors as
`4(X - x₁)(X - x₂)(X - (a²/4 - x₁ - x₂))`. -/
theorem cubic_factor {g₂ g₃ a b x₁ x₂ X : ℂ} (h12 : x₁ ≠ x₂)
    (h1 : 4 * x₁ ^ 3 - g₂ * x₁ - g₃ - (a * x₁ + b) ^ 2 = 0)
    (h2 : 4 * x₂ ^ 3 - g₂ * x₂ - g₃ - (a * x₂ + b) ^ 2 = 0) :
    4 * X ^ 3 - g₂ * X - g₃ - (a * X + b) ^ 2 =
      4 * ((X - x₁) * ((X - x₂) * (X - (a ^ 2 / 4 - x₁ - x₂)))) := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.2 h12
  -- the difference is affine in `X` and vanishes at `x₁` and `x₂`
  set Δ : ℂ → ℂ := fun X ↦ 4 * X ^ 3 - g₂ * X - g₃ - (a * X + b) ^ 2 -
    4 * ((X - x₁) * ((X - x₂) * (X - (a ^ 2 / 4 - x₁ - x₂))))
  have hlin : ∀ X, Δ X * (x₁ - x₂) = (X - x₂) * Δ x₁ - (X - x₁) * Δ x₂ := by
    intro X; simp only [Δ]; ring
  have hΔ1 : Δ x₁ = 0 := by simp only [Δ]; rw [h1]; ring
  have hΔ2 : Δ x₂ = 0 := by simp only [Δ]; rw [h2]; ring
  have := hlin X
  rw [hΔ1, hΔ2, mul_zero, mul_zero, sub_zero] at this
  have hX : Δ X = 0 := (mul_eq_zero.1 this).resolve_right hd
  simp only [Δ] at hX
  linear_combination hX

/-- **Milne, Proposition 3.9 (addition formula)**, proved from the divisors of `℘ - c` and of the line
function, as in the algebraic proof of the group law. -/
theorem weierstrassAdditionStatement : WeierstrassAdditionStatement := by
  classical
  refine ⟨fun L z z' hz hz' hzz' hne ↦ ?_⟩
  set x₁ := ℘[L] z
  set x₂ := ℘[L] z'
  set a := (℘'[L] z - ℘'[L] z') / (x₁ - x₂)
  set b := ℘'[L] z - a * x₁
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hne
  have hp : ℘'[L] z = a * x₁ + b := by simp only [b]; ring
  have hq : ℘'[L] z' = a * x₂ + b := by
    simp only [b, a]; field_simp; ring
  have htmk : tmk L z ≠ tmk L z' := fun h ↦ hne (weierstrassP_eq_of_tmk (Or.inl h))
  set r := a ^ 2 / 4 - x₁ - x₂
  obtain ⟨v, hv, hvr⟩ := exists_weierstrassP_eq (L := L) r
  -- the cubic identity on `ℂ ∖ Λ`
  have hcub : ∀ u, u ∉ L.lattice →
      4 * ((℘[L] u - x₁) * ((℘[L] u - x₂) * (℘[L] u - ℘[L] v))) =
        (℘'[L] u - a * ℘[L] u - b) * (℘'[L] u - (-a) * ℘[L] u - (-b)) := by
    intro u hu
    have e1 : 4 * x₁ ^ 3 - L.g₂ * x₁ - L.g₃ - (a * x₁ + b) ^ 2 = 0 := by
      rw [← hp, L.derivWeierstrassP_sq z hz]; ring
    have e2 : 4 * x₂ ^ 3 - L.g₂ * x₂ - L.g₃ - (a * x₂ + b) ^ 2 = 0 := by
      rw [← hq, L.derivWeierstrassP_sq z' hz']; ring
    have := cubic_factor (X := ℘[L] u) hne e1 e2
    rw [hvr, ← this]
    linear_combination (-1 : ℂ) * (L.derivWeierstrassP_sq u hu)
  -- divisors of both sides
  have hA1 := ellFun_weierstrassP_sub (L := L) x₁
  have hA2 := ellFun_weierstrassP_sub (L := L) x₂
  have hA3 := ellFun_weierstrassP_sub (L := L) (℘[L] v)
  have hA := (ellFun_const (L := L) (by norm_num : (4 : ℂ) ≠ 0)).mul (hA1.mul (hA2.mul hA3))
  have hh := ellFun_line (L := L) a b
  have hk := ellFun_line (L := L) (-a) (-b)
  have hB := hh.mul hk
  have hAB : ellDiv hA.1 = ellDiv hB.1 := ellDiv_congr hA.1 hB.1 hcub
  rw [ellDiv_mul (ellFun_const (L := L) (by norm_num : (4 : ℂ) ≠ 0)) (hA1.mul (hA2.mul hA3)),
    ellDiv_const (by norm_num : (4 : ℂ) ≠ 0), ellDiv_mul hA1 (hA2.mul hA3), ellDiv_mul hA2 hA3, ellDiv_weierstrassP_sub hz,
    ellDiv_weierstrassP_sub hz', ellDiv_weierstrassP_sub hv, ellDiv_mul hh hk,
    ellDiv_line hz hz' htmk hp hq] at hAB
  have hnz : -z ∉ L.lattice := by simpa using hz
  have hnz' : -z' ∉ L.lattice := by simpa using hz'
  have htmk' : tmk L (-z) ≠ tmk L (-z') := by
    rw [tmk_neg, tmk_neg]; exact fun h ↦ htmk (neg_injective h)
  have hp' : ℘'[L] (-z) = -a * ℘[L] (-z) + -b := by
    rw [L.derivWeierstrassP_neg, L.weierstrassP_neg, hp]; ring
  have hq' : ℘'[L] (-z') = -a * ℘[L] (-z') + -b := by
    rw [L.derivWeierstrassP_neg, L.weierstrassP_neg, hq]; ring
  rw [ellDiv_line hnz hnz' htmk' hp' hq'] at hAB
  simp only [tmk_neg, neg_neg, zero_add] at hAB
  -- cancel to `(v) + (-v) = (w) + (-w)` with `w = -z - z'`
  set w := -tmk L z - tmk L z'
  have hvw : Finsupp.single (tmk L v) (1 : ℤ) + Finsupp.single (-tmk L v) 1 =
      Finsupp.single w 1 + Finsupp.single (-w) 1 := by
    have e : tmk L z - -tmk L z' = -w := by simp only [w]; abel
    rw [e] at hAB
    have h6 : Finsupp.single (0 : Torus L) (2 : ℤ) + Finsupp.single 0 2 + Finsupp.single 0 2 =
        Finsupp.single 0 3 + Finsupp.single 0 3 := by
      rw [← Finsupp.single_add, ← Finsupp.single_add, ← Finsupp.single_add]; norm_num
    exact eq_of_sub_eq_combo hAB h6 (by abel)
  have hw1 := congrArg (fun D : Torus L →₀ ℤ ↦ D w) hvw
  simp only [Finsupp.add_apply, Finsupp.single_apply] at hw1
  have hzz : tmk L (z + z') = tmk L v ∨ tmk L (z + z') = -tmk L v := by
    have e : tmk L (z + z') = -w := by simp only [w, tmk_add]; abel
    rw [e]
    by_cases h1 : tmk L v = w
    · right; rw [h1]
    · by_cases h2 : -tmk L v = w
      · left; rw [← h2, neg_neg]
      · rw [ite_eq_right h1, ite_eq_right h2] at hw1
        split_ifs at hw1 <;> omega
  rw [weierstrassP_eq_of_tmk hzz, hvr]
  simp only [r, a, x₁, x₂]
  ring

end

end ModularFormsKB.Milne
