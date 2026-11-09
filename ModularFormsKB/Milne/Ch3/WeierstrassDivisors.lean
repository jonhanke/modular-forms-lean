import ModularFormsKB.Milne.Ch3.TorusDivisors

/-!
# Milne, Chapter 3: divisor calculus for elliptic functions

Degree and sum of divisors on the torus as additive maps, the multiplicativity of `ellDiv`, Liouville's theorem
in divisor form (a function with zero divisor is constant), and the divisors of `℘ - ℘(v)` and of the "line
function" `℘' - a ℘ - b`, computed from Proposition 3.1 (degree zero and Abel's condition) alone.
-/

open Complex Filter Topology Set PeriodPair

namespace ModularFormsKB.Milne

noncomputable section

variable {L : PeriodPair}

/-! ### Degree and sum -/

variable (L) in
/-- The degree of a divisor on the torus. -/
def degT : (Torus L →₀ ℤ) →+ ℤ := Finsupp.liftAddHom fun _ ↦ AddMonoidHom.id ℤ

variable (L) in
/-- The sum of a divisor in the group `ℂ ⧸ Λ`. -/
def sumT : (Torus L →₀ ℤ) →+ Torus L := Finsupp.liftAddHom fun x ↦ zmultiplesHom (Torus L) x

@[simp] theorem degT_single (x : Torus L) (n : ℤ) : degT L (Finsupp.single x n) = n := by
  simp [degT]

@[simp] theorem sumT_single (x : Torus L) (n : ℤ) : sumT L (Finsupp.single x n) = n • x := by
  simp [sumT]

theorem degT_apply (D : Torus L →₀ ℤ) : degT L D = ∑ x ∈ D.support, D x := by
  simp [degT, Finsupp.liftAddHom_apply, Finsupp.sum]

theorem degT_ellDiv {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f)
    (hnz : ¬ (∀ᶠ z in codiscrete ℂ, f z = 0)) : degT L (ellDiv hf) = 0 := by
  rw [degT, Finsupp.liftAddHom_apply]
  exact ellDiv_degree hf hnz

theorem sumT_ellDiv {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f)
    (hnz : ¬ (∀ᶠ z in codiscrete ℂ, f z = 0)) : sumT L (ellDiv hf) = 0 := by
  rw [sumT, Finsupp.liftAddHom_apply]
  exact ellDiv_sum hf hnz

/-! ### Effective divisors of small degree -/

theorem eq_zero_of_nonneg_of_degT_eq_zero {E : Torus L →₀ ℤ} (hE : ∀ x, 0 ≤ E x)
    (hd : degT L E = 0) : E = 0 := by
  rw [degT_apply] at hd
  have := (Finset.sum_eq_zero_iff_of_nonneg fun x _ ↦ hE x).1 hd
  ext x
  by_cases hx : x ∈ E.support
  · exact this x hx
  · simpa using hx

theorem eq_single_of_nonneg_of_degT_eq_one {E : Torus L →₀ ℤ} (hE : ∀ x, 0 ≤ E x)
    (hd : degT L E = 1) : ∃ w, E = Finsupp.single w 1 := by
  classical
  have hex : ∃ w, E w ≠ 0 := by
    by_contra h
    push Not at h
    have : E = 0 := by ext x; exact h x
    rw [this, map_zero] at hd
    exact zero_ne_one hd
  obtain ⟨w, hw⟩ := hex
  have hw1 : 1 ≤ E w := by have := hE w; omega
  refine ⟨w, ?_⟩
  have h0 : E - Finsupp.single w 1 = 0 := by
    refine eq_zero_of_nonneg_of_degT_eq_zero (fun x ↦ ?_) (by rw [map_sub, hd, degT_single]; rfl)
    rw [Finsupp.sub_apply, Finsupp.single_apply]
    split_ifs with h
    · rw [← h]; omega
    · have := hE x; omega
  exact sub_eq_zero.1 h0

/-- An effective-off-`0` divisor of degree zero with a pole of order two at `0`, a zero at `v`, and sum zero, is
`(v) + (-v) - 2(0)`. -/
theorem divisor_two {D : Torus L →₀ ℤ} {v : Torus L} (hv : v ≠ 0) (h0 : D 0 = -2)
    (hpos : ∀ x, x ≠ 0 → 0 ≤ D x) (hv1 : 1 ≤ D v) (hdeg : degT L D = 0) (hsum : sumT L D = 0) :
    D = Finsupp.single v 1 + Finsupp.single (-v) 1 - Finsupp.single 0 2 := by
  classical
  set E := D + Finsupp.single 0 2 - Finsupp.single v 1
  have hE : ∀ x, 0 ≤ E x := by
    intro x
    have e : E x = D x + (if x = 0 then 2 else 0) - (if x = v then 1 else 0) := by
      simp [E, Finsupp.single_apply, eq_comm]
    rw [e]
    by_cases hx0 : x = 0
    · subst hx0
      rw [ite_eq_left rfl, ite_eq_right (Ne.symm hv), h0]; omega
    · by_cases hxv : x = v
      · subst hxv; rw [ite_eq_right hx0, ite_eq_left rfl]; omega
      · rw [ite_eq_right hx0, ite_eq_right hxv]; have := hpos x hx0; omega
  have hdE : degT L E = 1 := by
    simp only [E, map_sub, map_add, hdeg, degT_single]; norm_num
  obtain ⟨w, hw⟩ := eq_single_of_nonneg_of_degT_eq_one hE hdE
  have hD : D = Finsupp.single v 1 + Finsupp.single w 1 - Finsupp.single 0 2 := by
    have : D = E + Finsupp.single v 1 - Finsupp.single 0 2 := by simp only [E]; abel
    rw [this, hw]; abel
  have hw' : w = -v := by
    rw [hD] at hsum
    simp only [map_sub, map_add, sumT_single, one_smul, smul_zero, sub_zero] at hsum
    exact eq_neg_of_add_eq_zero_right hsum
  rw [hD, hw']

/-- An effective-off-`0` divisor of degree zero with a pole of order three at `0`, zeros at two distinct
points `p`, `q`, and sum zero, is `(p) + (q) + (-p-q) - 3(0)`. -/
theorem divisor_three {D : Torus L →₀ ℤ} {p q : Torus L} (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q)
    (h0 : D 0 = -3) (hpos : ∀ x, x ≠ 0 → 0 ≤ D x) (hp1 : 1 ≤ D p) (hq1 : 1 ≤ D q)
    (hdeg : degT L D = 0) (hsum : sumT L D = 0) :
    D = Finsupp.single p 1 + Finsupp.single q 1 + Finsupp.single (-p - q) 1 - Finsupp.single 0 3 := by
  classical
  set E := D + Finsupp.single 0 3 - Finsupp.single p 1 - Finsupp.single q 1
  have hE : ∀ x, 0 ≤ E x := by
    intro x
    have e : E x = D x + (if x = 0 then 3 else 0) - (if x = p then 1 else 0) -
        (if x = q then 1 else 0) := by
      simp [E, Finsupp.single_apply, eq_comm]
    rw [e]
    by_cases hx0 : x = 0
    · subst hx0
      rw [ite_eq_left rfl, ite_eq_right (Ne.symm hp), ite_eq_right (Ne.symm hq), h0]; omega
    · by_cases hxp : x = p
      · subst hxp; rw [ite_eq_right hx0, ite_eq_left rfl, ite_eq_right hpq]; omega
      · by_cases hxq : x = q
        · subst hxq; rw [ite_eq_right hx0, ite_eq_right hxp, ite_eq_left rfl]; omega
        · rw [ite_eq_right hx0, ite_eq_right hxp, ite_eq_right hxq]; have := hpos x hx0; omega
  have hdE : degT L E = 1 := by
    simp only [E, map_sub, map_add, hdeg, degT_single]; norm_num
  obtain ⟨w, hw⟩ := eq_single_of_nonneg_of_degT_eq_one hE hdE
  have hD : D = Finsupp.single p 1 + Finsupp.single q 1 + Finsupp.single w 1 - Finsupp.single 0 3 := by
    have : D = E + Finsupp.single p 1 + Finsupp.single q 1 - Finsupp.single 0 3 := by simp only [E]; abel
    rw [this, hw]; abel
  have hw' : w = -p - q := by
    rw [hD] at hsum
    simp only [map_sub, map_add, sumT_single, one_smul, smul_zero, sub_zero] at hsum
    rw [← sub_eq_zero]
    rw [← hsum]; abel
  rw [hD, hw']

/-! ### Elliptic functions that are not identically zero -/

variable (L) in
/-- A doubly periodic function, not identically zero (all its orders are finite). -/
def EllFun (f : ℂ → ℂ) : Prop :=
  IsDoublyPeriodic L.lattice f ∧ ∀ z, meromorphicOrderAt f z ≠ ⊤

theorem EllFun.not_eventually_zero {f : ℂ → ℂ} (hf : EllFun L f) :
    ¬ (∀ᶠ z in codiscrete ℂ, f z = 0) := fun h ↦ by
  obtain ⟨z, hz⟩ := ((meromorphicOn_univ.1 hf.1.1).exists_meromorphicOrderAt_eq_top_iff_eventually_zero).2 h
  exact hf.2 z hz

theorem EllFun.of_ne_top {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f) {z₀ : ℂ}
    (h : meromorphicOrderAt f z₀ ≠ ⊤) : EllFun L f := by
  refine ⟨hf, fun z hz ↦ h ?_⟩
  have hev := ((meromorphicOn_univ.1 hf.1).exists_meromorphicOrderAt_eq_top_iff_eventually_zero).1 ⟨z, hz⟩
  rw [meromorphicOrderAt_eq_top_iff]
  exact (eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.1 hev) z₀

theorem EllFun.ordZ_eq {f : ℂ → ℂ} (hf : EllFun L f) (z : ℂ) : meromorphicOrderAt f z = ordZ f z :=
  (WithTop.coe_untop₀_of_ne_top (hf.2 z)).symm

theorem IsDoublyPeriodic.mul {f g : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f)
    (hg : IsDoublyPeriodic L.lattice g) : IsDoublyPeriodic L.lattice (fun z ↦ f z * g z) :=
  ⟨fun z _ ↦ (hf.1 z (mem_univ z)).mul (hg.1 z (mem_univ z)), fun ω hω z ↦ by
    simp only [hf.2 ω hω, hg.2 ω hω]⟩

theorem IsDoublyPeriodic.inv {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f) :
    IsDoublyPeriodic L.lattice (fun z ↦ (f z)⁻¹) :=
  ⟨fun z _ ↦ (hf.1 z (mem_univ z)).inv, fun ω hω z ↦ by simp only [hf.2 ω hω]⟩

theorem IsDoublyPeriodic.add {f g : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f)
    (hg : IsDoublyPeriodic L.lattice g) : IsDoublyPeriodic L.lattice (fun z ↦ f z + g z) :=
  ⟨fun z _ ↦ (hf.1 z (mem_univ z)).add (hg.1 z (mem_univ z)), fun ω hω z ↦ by
    simp only [hf.2 ω hω, hg.2 ω hω]⟩

theorem IsDoublyPeriodic.sub {f g : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f)
    (hg : IsDoublyPeriodic L.lattice g) : IsDoublyPeriodic L.lattice (fun z ↦ f z - g z) :=
  ⟨fun z _ ↦ (hf.1 z (mem_univ z)).sub (hg.1 z (mem_univ z)), fun ω hω z ↦ by
    simp only [hf.2 ω hω, hg.2 ω hω]⟩

theorem isDoublyPeriodic_const (c : ℂ) : IsDoublyPeriodic L.lattice (fun _ ↦ c) :=
  ⟨fun _ _ ↦ MeromorphicAt.const c _, fun _ _ _ ↦ rfl⟩

theorem isDoublyPeriodic_weierstrassP : IsDoublyPeriodic L.lattice ℘[L] :=
  ⟨fun z _ ↦ L.meromorphic_weierstrassP z, fun ω hω z ↦ L.weierstrassP_add_coe z ⟨ω, hω⟩⟩

theorem isDoublyPeriodic_derivWeierstrassP : IsDoublyPeriodic L.lattice ℘'[L] :=
  ⟨fun z _ ↦ L.meromorphic_derivWeierstrassP z, fun ω hω z ↦ L.derivWeierstrassP_add_coe z ⟨ω, hω⟩⟩

theorem EllFun.mul {f g : ℂ → ℂ} (hf : EllFun L f) (hg : EllFun L g) :
    EllFun L (fun z ↦ f z * g z) := by
  refine ⟨hf.1.mul hg.1, fun z ↦ ?_⟩
  rw [show (fun z ↦ f z * g z) = f * g from rfl,
    meromorphicOrderAt_mul (hf.1.1 z (mem_univ z)) (hg.1.1 z (mem_univ z)), hf.ordZ_eq, hg.ordZ_eq]
  exact WithTop.add_ne_top.2 ⟨WithTop.coe_ne_top, WithTop.coe_ne_top⟩

theorem EllFun.inv {f : ℂ → ℂ} (hf : EllFun L f) : EllFun L (fun z ↦ (f z)⁻¹) := by
  refine ⟨hf.1.inv, fun z ↦ ?_⟩
  rw [show (fun z ↦ (f z)⁻¹) = f⁻¹ from rfl, meromorphicOrderAt_inv, hf.ordZ_eq]
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]; exact WithTop.coe_ne_top

theorem ellFun_const {c : ℂ} (hc : c ≠ 0) : EllFun L (fun _ ↦ c) := by
  classical
  refine ⟨isDoublyPeriodic_const c, fun z ↦ ?_⟩
  rw [meromorphicOrderAt_const, ite_eq_right hc]; exact WithTop.zero_ne_top

theorem ellDiv_mul {f g : ℂ → ℂ} (hf : EllFun L f) (hg : EllFun L g) :
    ellDiv (hf.mul hg).1 = ellDiv hf.1 + ellDiv hg.1 := by
  ext x
  obtain ⟨z, rfl⟩ := tmk_surjective x
  simp only [ellDiv_tmk, Finsupp.add_apply, ordZ]
  rw [show (fun z ↦ f z * g z) = f * g from rfl,
    meromorphicOrderAt_mul (hf.1.1 z (mem_univ z)) (hg.1.1 z (mem_univ z)), hf.ordZ_eq,
    hg.ordZ_eq, ← WithTop.coe_add, WithTop.untop₀_coe]
  rfl

theorem ellDiv_inv {f : ℂ → ℂ} (hf : EllFun L f) : ellDiv hf.inv.1 = -ellDiv hf.1 := by
  ext x
  obtain ⟨z, rfl⟩ := tmk_surjective x
  simp only [ellDiv_tmk, Finsupp.neg_apply, ordZ]
  rw [show (fun z ↦ (f z)⁻¹) = f⁻¹ from rfl, meromorphicOrderAt_inv, hf.ordZ_eq, ← WithTop.LinearOrderedAddCommGroup.coe_neg,
    WithTop.untop₀_coe]
  rfl

theorem ellDiv_const {c : ℂ} (hc : c ≠ 0) : ellDiv (ellFun_const (L := L) hc).1 = 0 := by
  classical
  ext x
  obtain ⟨z, rfl⟩ := tmk_surjective x
  simp only [ellDiv_tmk, Finsupp.zero_apply, ordZ]
  rw [meromorphicOrderAt_const, ite_eq_right hc]; rfl

/-- **Liouville's theorem in divisor form**: an elliptic function with zero divisor is a nonzero constant. -/
theorem eq_const_of_ellDiv_eq_zero {f : ℂ → ℂ} (hf : EllFun L f) (h0 : ellDiv hf.1 = 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ᶠ z in codiscrete ℂ, f z = c := by
  obtain ⟨c, hc⟩ := const_of_no_poles hf.1 (fun z ↦ by
    rw [hf.ordZ_eq, ← ellDiv_tmk hf.1, h0, Finsupp.zero_apply]; rfl)
  refine ⟨c, fun hc0 ↦ hf.not_eventually_zero (by simpa [hc0] using hc), hc⟩

theorem EllFun.eventually_ne_zero {f : ℂ → ℂ} (hf : EllFun L f) : ∀ᶠ z in codiscrete ℂ, f z ≠ 0 :=
  hf.1.1.codiscreteWithin_setOfPred_ne_zero fun u _ ↦ hf.2 u

/-- Two elliptic functions with the same divisor are proportional. -/
theorem eq_const_mul_of_ellDiv_eq {f g : ℂ → ℂ} (hf : EllFun L f) (hg : EllFun L g)
    (h : ellDiv hf.1 = ellDiv hg.1) : ∃ c : ℂ, c ≠ 0 ∧ ∀ᶠ z in codiscrete ℂ, g z = c * f z := by
  have hq := hg.mul hf.inv
  have h0 : ellDiv hq.1 = 0 := by rw [ellDiv_mul hg hf.inv, ellDiv_inv hf, h, add_neg_cancel]
  obtain ⟨c, hc, hev⟩ := eq_const_of_ellDiv_eq_zero hq h0
  refine ⟨c, hc, ?_⟩
  filter_upwards [hev, hf.eventually_ne_zero] with z hz hfz
  rw [← hz]; field_simp

/-! ### Orders of `℘`, `℘'` and the line functions -/

theorem ordZ_nonneg_of_analyticAt {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) : 0 ≤ ordZ f z := by
  unfold ordZ
  rcases eq_or_ne (meromorphicOrderAt f z) ⊤ with h | h
  · rw [h]; rfl
  · have := hf.meromorphicOrderAt_nonneg
    rw [← WithTop.coe_untop₀_of_ne_top h] at this
    exact_mod_cast this

theorem one_le_ordZ_of_eq_zero {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (h0 : f z = 0)
    (hne : meromorphicOrderAt f z ≠ ⊤) : 1 ≤ ordZ f z := by
  have hpos : 0 < meromorphicOrderAt f z := by
    rw [← tendsto_zero_iff_meromorphicOrderAt_pos hf.meromorphicAt]
    have := hf.continuousAt.tendsto
    rw [h0] at this
    exact this.mono_left nhdsWithin_le_nhds
  unfold ordZ
  rw [← WithTop.coe_untop₀_of_ne_top hne] at hpos
  have : 0 < (meromorphicOrderAt f z).untop₀ := by exact_mod_cast hpos
  omega

theorem eq_zero_of_one_le_ordZ {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (h : 1 ≤ ordZ f z) :
    f z = 0 := by
  by_contra hne
  have h0 : meromorphicOrderAt f z = 0 := by
    rw [hf.meromorphicOrderAt_eq, (hf.analyticOrderAt_eq_zero).2 hne]; rfl
  unfold ordZ at h
  rw [h0] at h
  exact absurd h (by decide)

theorem meromorphicOrderAt_weierstrassP_sub (c : ℂ) {l : ℂ} (hl : l ∈ L.lattice) :
    meromorphicOrderAt (fun z ↦ ℘[L] z - c) l = -2 := by
  have e : (fun z ↦ ℘[L] z - c) = ℘[L] + fun _ ↦ -c := by funext z; simp [sub_eq_add_neg]
  rw [e, meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const _ _), L.order_weierstrassP l hl]
  rw [L.order_weierstrassP l hl]
  exact lt_of_lt_of_le (by decide) (analyticAt_const (v := -c) (x := l)).meromorphicOrderAt_nonneg

theorem meromorphicOrderAt_derivWeierstrassP {l : ℂ} (hl : l ∈ L.lattice) :
    meromorphicOrderAt ℘'[L] l = -3 := by
  have h := meromorphicOrderAt_deriv_eq_sub_one (f := ℘[L]) (x := l) (n := -2) (by norm_num)
    (by rw [L.order_weierstrassP l hl]; rfl)
  rw [deriv_weierstrassP] at h
  rw [h]; rfl

theorem meromorphicOrderAt_line (a b : ℂ) {l : ℂ} (hl : l ∈ L.lattice) :
    meromorphicOrderAt (fun z ↦ ℘'[L] z - a * ℘[L] z - b) l = -3 := by
  have e : (fun z ↦ ℘'[L] z - a * ℘[L] z - b) = ℘'[L] + fun z ↦ -(a * ℘[L] z + b) := by
    funext z; simp only [Pi.add_apply]; ring
  have hm : MeromorphicAt (fun z ↦ -(a * ℘[L] z + b)) l := by
    have := L.meromorphic_weierstrassP l; fun_prop
  rw [e, meromorphicOrderAt_add_eq_left_of_lt hm, meromorphicOrderAt_derivWeierstrassP hl]
  rw [meromorphicOrderAt_derivWeierstrassP hl]
  have h2 : (-2 : WithTop ℤ) ≤ meromorphicOrderAt (fun z ↦ -(a * ℘[L] z + b)) l := by
    have e2 : (fun z ↦ -(a * ℘[L] z + b)) = (fun z ↦ (-a) * ℘[L] z) + fun _ ↦ -b := by
      funext z; simp only [Pi.add_apply]; ring
    rw [e2]
    refine le_trans ?_ (meromorphicOrderAt_add (by have := L.meromorphic_weierstrassP l; fun_prop)
      (MeromorphicAt.const _ _))
    refine le_min ?_ ?_
    · rw [show (fun z ↦ (-a) * ℘[L] z) = (fun _ ↦ -a) * ℘[L] from rfl,
        meromorphicOrderAt_mul (MeromorphicAt.const _ _) (L.meromorphic_weierstrassP l),
        L.order_weierstrassP l hl]
      have : (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun _ ↦ -a) l :=
        (analyticAt_const (v := -a) (x := l)).meromorphicOrderAt_nonneg
      calc (-2 : WithTop ℤ) = 0 + -2 := by simp
        _ ≤ _ := add_le_add_left this _
    · exact le_trans (by decide) (analyticAt_const (v := -b) (x := l)).meromorphicOrderAt_nonneg
  exact lt_of_lt_of_le (by decide) h2

theorem analyticAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) : AnalyticAt ℂ ℘[L] z :=
  L.analyticOnNhd_weierstrassP z hz

theorem analyticAt_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) : AnalyticAt ℂ ℘'[L] z :=
  L.analyticOnNhd_derivWeierstrassP z hz

theorem ellFun_weierstrassP_sub (c : ℂ) : EllFun L (fun z ↦ ℘[L] z - c) :=
  EllFun.of_ne_top (isDoublyPeriodic_weierstrassP.sub (isDoublyPeriodic_const c)) (z₀ := 0)
    (by rw [meromorphicOrderAt_weierstrassP_sub c L.lattice.zero_mem]; decide)

theorem ellFun_line (a b : ℂ) : EllFun L (fun z ↦ ℘'[L] z - a * ℘[L] z - b) :=
  EllFun.of_ne_top ((isDoublyPeriodic_derivWeierstrassP.sub
      ((isDoublyPeriodic_const a).mul isDoublyPeriodic_weierstrassP)).sub (isDoublyPeriodic_const b))
    (z₀ := 0) (by rw [meromorphicOrderAt_line a b L.lattice.zero_mem]; decide)

theorem tmk_ne_zero {z : ℂ} (hz : z ∉ L.lattice) : tmk L z ≠ 0 := fun h ↦ hz (tmk_eq_zero_iff.1 h)

/-- **The divisor of `℘ - ℘(v)`** is `(v) + (-v) - 2(0)`. -/
theorem ellDiv_weierstrassP_sub {v : ℂ} (hv : v ∉ L.lattice) :
    ellDiv (ellFun_weierstrassP_sub (L := L) (℘[L] v)).1 =
      Finsupp.single (tmk L v) 1 + Finsupp.single (-tmk L v) 1 - Finsupp.single 0 2 := by
  have hF := ellFun_weierstrassP_sub (L := L) (℘[L] v)
  refine divisor_two (tmk_ne_zero hv) ?_ ?_ ?_ (degT_ellDiv hF.1 hF.not_eventually_zero)
    (sumT_ellDiv hF.1 hF.not_eventually_zero)
  · rw [← tmk_zero, ellDiv_tmk, ordZ, meromorphicOrderAt_weierstrassP_sub _ L.lattice.zero_mem]; rfl
  · intro x hx
    obtain ⟨z, rfl⟩ := tmk_surjective x
    have hz : z ∉ L.lattice := fun h ↦ hx (tmk_eq_zero_iff.2 h)
    rw [ellDiv_tmk]
    exact ordZ_nonneg_of_analyticAt ((analyticAt_weierstrassP hz).sub analyticAt_const)
  · rw [ellDiv_tmk]
    exact one_le_ordZ_of_eq_zero ((analyticAt_weierstrassP hv).sub analyticAt_const) (sub_self _)
      (hF.2 v)

/-- **The divisor of the line function** `℘' - a℘ - b` through two points `P(p) ≠ P(q)` of the curve is
`(p) + (q) + (-p-q) - 3(0)`. -/
theorem ellDiv_line {p q : ℂ} (hp : p ∉ L.lattice) (hq : q ∉ L.lattice) (hpq : tmk L p ≠ tmk L q)
    {a b : ℂ} (hap : ℘'[L] p = a * ℘[L] p + b) (haq : ℘'[L] q = a * ℘[L] q + b) :
    ellDiv (ellFun_line (L := L) a b).1 = Finsupp.single (tmk L p) 1 + Finsupp.single (tmk L q) 1 +
      Finsupp.single (-tmk L p - tmk L q) 1 - Finsupp.single 0 3 := by
  have hF := ellFun_line (L := L) a b
  have han : ∀ z, z ∉ L.lattice → AnalyticAt ℂ (fun z ↦ ℘'[L] z - a * ℘[L] z - b) z := fun z hz ↦
    ((analyticAt_derivWeierstrassP hz).sub (analyticAt_const.mul (analyticAt_weierstrassP hz))).sub
      analyticAt_const
  refine divisor_three (tmk_ne_zero hp) (tmk_ne_zero hq) hpq ?_ ?_ ?_ ?_
    (degT_ellDiv hF.1 hF.not_eventually_zero) (sumT_ellDiv hF.1 hF.not_eventually_zero)
  · rw [← tmk_zero, ellDiv_tmk, ordZ, meromorphicOrderAt_line _ _ L.lattice.zero_mem]; rfl
  · intro x hx
    obtain ⟨z, rfl⟩ := tmk_surjective x
    have hz : z ∉ L.lattice := fun h ↦ hx (tmk_eq_zero_iff.2 h)
    rw [ellDiv_tmk]
    exact ordZ_nonneg_of_analyticAt (han z hz)
  · rw [ellDiv_tmk]
    exact one_le_ordZ_of_eq_zero (han p hp) (by show ℘'[L] p - a * ℘[L] p - b = 0; rw [hap]; ring) (hF.2 p)
  · rw [ellDiv_tmk]
    exact one_le_ordZ_of_eq_zero (han q hq) (by show ℘'[L] q - a * ℘[L] q - b = 0; rw [haq]; ring) (hF.2 q)

end

end ModularFormsKB.Milne
