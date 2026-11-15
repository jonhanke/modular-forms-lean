import ModularFormsKB.Milne.RiemannSurface.Results
import TauCeti.FieldTheory.FunctionField.Place.OfValuationSubring
import ModularFormsKB.Citation
/-!
# The place of the meromorphic function field attached to a point of a compact Riemann surface

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §1 (pdf pp. 18–22): the passage between a compact
Riemann surface `X` and its field of meromorphic functions `M(X)`, used for Riemann–Roch (Theorem 1.20).

Let `X` be a compact connected Riemann surface carrying a nonconstant meromorphic function, so that `M(X)` is an
algebraic function field of one variable over `ℂ` (`RiemannSurface.isFunctionField_of_exists_nonconstant`). For a
point `x`, the meromorphic functions without a pole at `x` form a proper valuation subring `𝒪_x` of `M(X)` containing
`ℂ` (`pointSubring`), hence the valuation ring of exactly one place `P_x` of `M(X)/ℂ` (Tau Ceti
`TauCeti.Place.ofValuationSubring`, Stichtenoth 1.1.13); this is `pointPlace`. The order function of `P_x` is the
analytic order at `x` divided by a positive integer `e_x` (`exists_order_eq_mul_ord`); `e_x = 1` as soon as some
meromorphic function has a simple zero at `x` (`order_eq_ord_of_order_eq_one`).
-/

open TauCeti TauCeti.RiemannSurface ModularFormsKB.Milne.RiemannSurface MeromorphicFunction
open scoped Manifold

noncomputable section

namespace ModularFormsKB.Milne.Wave11

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X]

/-- The meromorphic functions without a pole at `x`: a valuation subring of `M(X)`. -/
def pointSubring (x : X) : ValuationSubring (MeromorphicFunction X) where
  carrier := {g | g x ≠ OnePoint.infty}
  mul_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq] at hf hg ⊢
    rw [mul_apply hf hg]
    exact OnePoint.coe_ne_infty _
  one_mem' := by simp [coe_one]
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq] at hf hg ⊢
    rw [add_apply hf hg]
    exact OnePoint.coe_ne_infty _
  zero_mem' := by simp [coe_zero]
  neg_mem' {f} hf := by
    simp only [Set.mem_ofPred_eq] at hf ⊢
    rw [neg_apply hf]
    exact OnePoint.coe_ne_infty _
  mem_or_inv_mem' g := by
    by_cases h : g x = OnePoint.infty
    · right
      show g⁻¹ x ≠ OnePoint.infty
      rw [inv_apply_of_eq_infty h]
      exact OnePoint.coe_ne_infty _
    · exact Or.inl h

theorem mem_pointSubring_iff {x : X} {g : MeromorphicFunction X} :
    g ∈ pointSubring x ↔ g x ≠ OnePoint.infty := Iff.rfl

theorem mem_pointSubring_iff_order {x : X} {g : MeromorphicFunction X} :
    g ∈ pointSubring x ↔ 0 ≤ order x g := by
  rw [mem_pointSubring_iff, order_nonneg_iff]

theorem algebraMap_mem_pointSubring (x : X) (c : ℂ) :
    algebraMap ℂ (MeromorphicFunction X) c ∈ pointSubring x := by
  rw [mem_pointSubring_iff, coe_algebraMap]
  exact OnePoint.coe_ne_infty _

/-- A nonconstant meromorphic function gives a function with a pole at any prescribed point: `f` itself if `x` is a
pole, otherwise `(f - f(x))⁻¹`. -/
theorem exists_apply_eq_infty {f : MeromorphicFunction X} (hf : IsNonconstant f) (x : X) :
    ∃ g : MeromorphicFunction X, g x = OnePoint.infty := by
  by_cases hx : f x = OnePoint.infty
  · exact ⟨f, hx⟩
  obtain ⟨c, hc⟩ := OnePoint.ne_infty_iff_exists.1 hx
  set h := f - algebraMap ℂ (MeromorphicFunction X) c
  have hh0 : h x = ((0 : ℂ) : OnePoint ℂ) := by
    have hcx : (algebraMap ℂ (MeromorphicFunction X) c) x = (c : OnePoint ℂ) := by simp [coe_algebraMap]
    rw [sub_apply_of_eq_coe hc.symm hcx, sub_self]
  have hne : h ≠ 0 := by
    intro h0
    obtain ⟨a, b, hab⟩ := hf
    have hfa : f = algebraMap ℂ (MeromorphicFunction X) c := sub_eq_zero.1 h0
    exact hab (by rw [hfa]; simp [coe_algebraMap])
  refine ⟨h⁻¹, ?_⟩
  rw [← order_neg_iff, AddValuation.map_inv]
  have hpos : 0 < order x h := order_pos_iff.2 hh0
  have hfin : order x h ≠ ⊤ := (order x).ne_top_iff.2 hne
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hfin
  rw [← hn] at hpos ⊢
  have : (0 : ℤ) < n := by exact_mod_cast hpos
  exact_mod_cast (show -n < (0 : ℤ) by omega)

theorem pointSubring_ne_top {f : MeromorphicFunction X} (hf : IsNonconstant f) (x : X) :
    pointSubring x ≠ ⊤ := by
  obtain ⟨g, hg⟩ := exists_apply_eq_infty hf x
  intro htop
  have : g ∈ pointSubring x := htop ▸ ValuationSubring.mem_top g
  exact this hg

variable (hF : IsFunctionField ℂ (MeromorphicFunction X)) {f₀ : MeromorphicFunction X} (hf₀ : IsNonconstant f₀)

/-- **The place `P_x` of `M(X)/ℂ` at a point `x`**: the place whose valuation ring is the ring of meromorphic
functions without a pole at `x`. -/
def pointPlace (x : X) : Place ℂ (MeromorphicFunction X) :=
  Place.ofValuationSubring hF (algebraMap_mem_pointSubring x) (pointSubring_ne_top hf₀ x)

theorem integers_pointPlace (x : X) : (pointPlace hF hf₀ x).integers = pointSubring x :=
  Place.integers_ofValuationSubring _ _ _

theorem ord_pointPlace_nonneg_iff (x : X) {g : MeromorphicFunction X} :
    0 ≤ (pointPlace hF hf₀ x).ord g ↔ 0 ≤ order x g := by
  rw [← Place.mem_integers_iff_ord_nonneg, integers_pointPlace, mem_pointSubring_iff_order]

variable [CompactSpace X]

/-- The order at `x` of a nonzero meromorphic function, as an integer (the order system of `X`). -/
def ordAt (x : X) (g : MeromorphicFunction X) : ℤ := (order x g).untop₀

theorem coe_ordAt {x : X} {g : MeromorphicFunction X} (hg : g ≠ 0) : (ordAt x g : WithTop ℤ) = order x g := by
  rw [ordAt, WithTop.coe_untop₀_of_ne_top ((order x).ne_top_iff.2 hg)]

theorem ordAt_mul {x : X} {g h : MeromorphicFunction X} (hg : g ≠ 0) (hh : h ≠ 0) :
    ordAt x (g * h) = ordAt x g + ordAt x h := by
  have := (order x).map_mul g h
  rw [← coe_ordAt hg, ← coe_ordAt hh, ← coe_ordAt (mul_ne_zero hg hh)] at this
  exact_mod_cast this

theorem ordAt_inv {x : X} {g : MeromorphicFunction X} (hg : g ≠ 0) : ordAt x g⁻¹ = -ordAt x g := by
  have := (order x).map_inv (x := g)
  rw [← coe_ordAt hg, ← coe_ordAt (inv_ne_zero hg)] at this
  exact_mod_cast this

theorem ordAt_zpow {x : X} {g : MeromorphicFunction X} (hg : g ≠ 0) (n : ℤ) :
    ordAt x (g ^ n) = n * ordAt x g := by
  have key : ∀ m : ℕ, ordAt x (g ^ m) = m * ordAt x g := by
    intro m
    induction m with
    | zero =>
      simp only [pow_zero, Nat.cast_zero, zero_mul]
      have := coe_ordAt (x := x) (one_ne_zero (α := MeromorphicFunction X))
      rw [AddValuation.map_one] at this
      exact_mod_cast this
    | succ m ih =>
      rw [pow_succ, ordAt_mul (pow_ne_zero m hg) hg, ih]
      push_cast; ring
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, key]
  · rw [zpow_neg, zpow_natCast, ordAt_inv (pow_ne_zero m hg), key]
    ring

theorem ordAt_nonneg_iff {x : X} {g : MeromorphicFunction X} (hg : g ≠ 0) : 0 ≤ ordAt x g ↔ 0 ≤ order x g := by
  rw [← coe_ordAt hg]
  exact_mod_cast Iff.rfl

/-- **The order of `P_x` is the analytic order at `x` divided by a positive integer.** If `t` is a uniformizer of
`P_x`, then `ord_x = e · ord_{P_x}` with `e = ord_x(t) > 0`: write `g = t^{ord_{P_x} g} u` with `u` a unit of the
valuation ring `𝒪_x`, which has order `0` at `x`. -/
theorem exists_order_eq_mul_ord (x : X) :
    ∃ e : ℤ, 0 < e ∧ ∀ g : MeromorphicFunction X, g ≠ 0 → ordAt x g = e * (pointPlace hF hf₀ x).ord g := by
  set P := pointPlace hF hf₀ x
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  have ht1 : P.ord t = 1 := P.isUniformizer_iff_ord_eq_one.1 ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at ht1
    exact zero_ne_one ht1
  -- a unit of `𝒪_x` has order `0` at `x`
  have hunit : ∀ u : P.integersˣ, ordAt x (u : MeromorphicFunction X) = 0 := by
    intro u
    have hu0 : ((u : P.integers) : MeromorphicFunction X) ≠ 0 := by
      intro h
      have := u.ne_zero
      exact this (Subtype.ext h)
    have h1 : ((u : P.integers) : MeromorphicFunction X) ∈ P.integers := (u : P.integers).2
    have h2 : ((u : P.integers) : MeromorphicFunction X)⁻¹ ∈ P.integers := by
      have : ((u⁻¹ : P.integersˣ) : P.integers) * (u : P.integers) = 1 := u.inv_mul
      have h3 : (((u⁻¹ : P.integersˣ) : P.integers) : MeromorphicFunction X) =
          ((u : P.integers) : MeromorphicFunction X)⁻¹ := by
        exact eq_inv_of_mul_eq_one_left (by exact_mod_cast this)
      rw [← h3]
      exact ((u⁻¹ : P.integersˣ) : P.integers).2
    have h1' : 0 ≤ ordAt x ((u : P.integers) : MeromorphicFunction X) :=
      (ordAt_nonneg_iff hu0).2 ((ord_pointPlace_nonneg_iff hF hf₀ x).1 (P.mem_integers_iff_ord_nonneg.1 h1))
    have h2' : 0 ≤ ordAt x ((u : P.integers) : MeromorphicFunction X)⁻¹ :=
      (ordAt_nonneg_iff (inv_ne_zero hu0)).2
        ((ord_pointPlace_nonneg_iff hF hf₀ x).1 (P.mem_integers_iff_ord_nonneg.1 h2))
    rw [ordAt_inv hu0] at h2'
    omega
  refine ⟨ordAt x t, ?_, fun g hg ↦ ?_⟩
  · -- `t ∈ 𝒪_x` and `t⁻¹ ∉ 𝒪_x`
    have h1 : 0 ≤ ordAt x t := by
      rw [ordAt_nonneg_iff ht0, ← ord_pointPlace_nonneg_iff hF hf₀ x, ht1]
      exact zero_le_one
    have h2 : ¬ 0 ≤ ordAt x t⁻¹ := by
      rw [ordAt_nonneg_iff (inv_ne_zero ht0), ← ord_pointPlace_nonneg_iff hF hf₀ x, Place.ord_inv, ht1]
      norm_num
    rw [ordAt_inv ht0] at h2
    omega
  · obtain ⟨u, hu⟩ := P.exists_eq_zpow_mul_unit ht hg
    have hu0 : ((u : P.integers) : MeromorphicFunction X) ≠ 0 := by
      intro h
      exact u.ne_zero (Subtype.ext h)
    conv_lhs => rw [hu]
    rw [ordAt_mul (zpow_ne_zero _ ht0) hu0, ordAt_zpow ht0, hunit u, add_zero, mul_comm]

/-- If some meromorphic function has a simple zero at `x` (a local coordinate), the order of `P_x` is the analytic
order at `x`. -/
theorem order_eq_ord_of_ordAt_eq_one (x : X) {t : MeromorphicFunction X} (ht : t ≠ 0) (ht1 : ordAt x t = 1)
    (g : MeromorphicFunction X) (hg : g ≠ 0) : ordAt x g = (pointPlace hF hf₀ x).ord g := by
  obtain ⟨e, he, hord⟩ := exists_order_eq_mul_ord hF hf₀ x
  have h := hord t ht
  rw [ht1] at h
  have he1 : e = 1 := by
    have : e ∣ 1 := ⟨_, h⟩
    rcases Int.isUnit_iff.1 (isUnit_of_dvd_one this) with h | h <;> omega
  rw [hord g hg, he1, one_mul]

end ModularFormsKB.Milne.Wave11
