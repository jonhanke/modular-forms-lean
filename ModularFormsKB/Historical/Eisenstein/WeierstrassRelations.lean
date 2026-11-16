import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import ModularFormsKB.Citation
/-!
# Eisenstein's lattice sums `(g, x)` and Weierstrass's `℘`

Eisenstein, *Genaue Untersuchung der unendlichen Doppelproducte, aus welchen die elliptischen Functionen
als Quotienten zusammengesetzt sind* (Crelle 35, 1847), reprinted in *Mathematische Abhandlungen* (1847)
as *Beiträge* VI, §§ 5 and 8.

Eisenstein writes `(g, x) = ∑_w (x + w)^{-g}`, the sum over the lattice points `w = αm + βn`, and
`(g*, 0) = ∑'_w w^{-g}`, the same sum at `x = 0` with the term `w = 0` left out. For `g ≥ 3` both are
absolutely convergent. For `g = 2` (and `g = 1`) they converge only in Eisenstein's order of summation, but the
difference `(2, x) - (2*, 0) = x^{-2} + ∑'_w ((x + w)^{-2} - w^{-2})` is absolutely convergent and is Weierstrass's
`℘(x)` (Mathlib's `PeriodPair.weierstrassP`; the summand `l ↦ -l` turns Mathlib's `(x - l)` into Eisenstein's
`(x + w)`). So the relations below are Eisenstein's with `(2, x) - (2*, 0)` written `℘(x)` and `(4*, 0)` written
Mathlib's `G 4` (whose `l = 0` term is `0⁻¹ = 0`).

## What is formalized
* `hasDerivAt_eisensteinSum`, `eisensteinSum_three` (Beiträge VI, § 5, p. 283): `∂ₓ(g, x) =
  -g (g + 1, x)` for `g ≥ 3`, and `(3, x) = -½ ℘'(x)`.
* `eisensteinSum_four` (§ 8, remark III, (1.), p. 323): `(4, x) = ℘(x)² - 5 (4*, 0)`, the part of
  Eisenstein's formula `(4, x) = (2, x)² - 2 (2*, 0) (2, x) + (2δπi/α) ∂(2*, 0)/∂β` that does not involve the
  conditionally convergent constant `(2*, 0)` and its derivative in `β`.
* `eisensteinSum_five` (§ 8, remark III, (3.), p. 324): `(5, x) = (3, x) {(2, x) - (2*, 0)}`.
* `eisensteinSum_seven` (§ 5, (3.), p. 285): `(7, x) = (3, x) {(4, x) + 2 (4*, 0)}`.
* `deriv_derivWeierstrassP`: `℘'' = 6℘² - g₂/2`, from Mathlib's `℘'² = 4℘³ - g₂℘ - g₃`.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace ModularFormsKB.Historical.Eisenstein

open PeriodPair

variable (L : PeriodPair)

/-- Eisenstein's lattice sum `(g, x) = ∑_w (x + w)^{-g}` over the lattice `w ∈ L` (Crelle 35, § 5). For
`g ≥ 3` it converges absolutely; for `x ∈ L` the term `w = -x` is `0⁻¹ = 0` (a junk value). -/
def eisensteinSum (g : ℕ) (x : ℂ) : ℂ := ∑' l : L.lattice, ((x + l) ^ g)⁻¹

/-- The terms `((y + l)^g)⁻¹` are locally uniformly summable (`g ≥ 3`). -/
lemma hasSumLocallyUniformly_eisensteinSum {g : ℕ} (hg : 3 ≤ g) :
    HasSumLocallyUniformly (fun (l : L.lattice) (y : ℂ) => ((y + l) ^ g)⁻¹) (eisensteinSum L g) := by
  have h := L.hasSumLocallyUniformly_aux (fun (l : L.lattice) (y : ℂ) => ((y + l) ^ g)⁻¹)
    (fun _ => (fun l : L.lattice => (2 : ℝ) ^ g * ‖l‖ ^ (-(g : ℝ))))
    (fun _ _ => (ZLattice.summable_norm_rpow _ _ (by
      simp only [finrank_lattice]; have : (3 : ℝ) ≤ g := by exact_mod_cast hg
      push_cast; linarith)).mul_left _) ?_
  · exact h
  intro r hr
  refine Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro R hR s hs l rfl
  have hl : ‖l.1‖ ≤ 2 * ‖s + l.1‖ := by
    have := norm_sub_norm_le l.1 (-s)
    rw [norm_neg] at this
    have h2 : ‖(l.1 : ℂ) - -s‖ = ‖s + l.1‖ := by rw [sub_neg_eq_add, add_comm]
    linarith
  have hpos : 0 < ‖l.1‖ := by linarith
  have hne : 0 < ‖s + l.1‖ := by linarith
  have hn : ‖l‖ = ‖l.1‖ := rfl
  rw [hn, norm_inv, norm_pow, Real.rpow_neg hpos.le, Real.rpow_natCast, ← div_eq_mul_inv,
    inv_eq_one_div, div_le_div_iff₀ (pow_pos hne _) (pow_pos hpos _)]
  calc 1 * ‖l.1‖ ^ g ≤ (2 * ‖s + l.1‖) ^ g := by rw [one_mul]; gcongr
    _ = 2 ^ g * ‖s + l.1‖ ^ g := by ring

lemma tendsto_eisensteinSum {g : ℕ} (hg : 3 ≤ g) (x : ℂ) :
    Tendsto (fun t : Finset L.lattice => ∑ l ∈ t, ((x + l) ^ g)⁻¹) atTop (𝓝 (eisensteinSum L g x)) :=
  (hasSumLocallyUniformly_eisensteinSum L hg).tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ x)

lemma hasDerivAt_term (g : ℕ) (hg : 1 ≤ g) (l : ℂ) {x : ℂ} (h : x + l ≠ 0) :
    HasDerivAt (fun y => ((y + l) ^ g)⁻¹) (-(g : ℂ) * ((x + l) ^ (g + 1))⁻¹) x := by
  have h1 : HasDerivAt (fun y : ℂ => (y + l) ^ g) (g * (x + l) ^ (g - 1)) x :=
    (((hasDerivAt_id x).add_const l).fun_pow g).congr_deriv (by simp)
  have := h1.inv (pow_ne_zero g h)
  convert this using 1
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hg
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

lemma add_ne_zero_of_notMem {x : ℂ} (hx : x ∉ L.lattice) (l : L.lattice) : x + l ≠ 0 := by
  intro h
  apply hx
  have : x = -(l : ℂ) := by linear_combination h
  rw [this]
  exact neg_mem l.2

/-- **`(3, x) = -½ ℘'(x)`** (Eisenstein, Crelle 35, Beiträge VI, § 5, p. 283). -/
@[kb "eisenstein1847" "Crelle 35, Beiträge VI, § 5, p. 283: (3, x) = -1/2 ℘'(x)"]
theorem eisensteinSum_three (x : ℂ) : eisensteinSum L 3 x = -(1 / 2) * ℘'[L] x := by
  unfold eisensteinSum derivWeierstrassP
  rw [← (Equiv.neg L.lattice).tsum_eq (fun l : L.lattice => ((x + (l : ℂ)) ^ 3)⁻¹)]
  simp only [Equiv.neg_apply, NegMemClass.coe_neg, ← sub_eq_add_neg]
  rw [neg_mul, mul_neg, neg_neg, ← tsum_mul_left]
  congr with l
  ring

/-- **Eisenstein's differentiation rule** (Crelle 35, Beiträge VI, § 5, p. 283): for
`g ≥ 3` and `x` off the lattice, `∂ₓ (g, x) = -g (g + 1, x)`. -/
@[kb "eisenstein1847" "Crelle 35, Beiträge VI, § 5, p. 283: d/dx (g, x) = -g (g+1, x)"]
theorem hasDerivAt_eisensteinSum {g : ℕ} (hg : 3 ≤ g) {x : ℂ} (hx : x ∉ L.lattice) :
    HasDerivAt (eisensteinSum L g) (-(g : ℂ) * eisensteinSum L (g + 1) x) x := by
  have hU : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have hxU : x ∈ (L.lattice : Set ℂ)ᶜ := hx
  have hT := (hasSumLocallyUniformly_eisensteinSum L hg).tendstoLocallyUniformlyOn
    (s := (L.lattice : Set ℂ)ᶜ)
  have hterm : ∀ (l : L.lattice) {y : ℂ}, y ∈ (L.lattice : Set ℂ)ᶜ →
      HasDerivAt (fun y : ℂ => ((y + (l : ℂ)) ^ g)⁻¹) (-(g : ℂ) * ((y + (l : ℂ)) ^ (g + 1))⁻¹) y :=
    fun l y hy => hasDerivAt_term g (by omega) l (add_ne_zero_of_notMem L hy l)
  have hdiff : ∀ s : Finset L.lattice,
      DifferentiableOn ℂ (fun y : ℂ => ∑ i ∈ s, ((y + (i : ℂ)) ^ g)⁻¹) (L.lattice : Set ℂ)ᶜ := by
    intro s y hy
    exact (HasDerivAt.fun_sum (fun i _ => hterm i hy)).differentiableAt.differentiableWithinAt
  have hFd : DifferentiableOn ℂ (eisensteinSum L g) (L.lattice : Set ℂ)ᶜ :=
    hT.differentiableOn (.of_forall hdiff) hU
  have hd := (hT.deriv (.of_forall hdiff) hU).tendsto_at hxU
  have hs := (tendsto_eisensteinSum L (show 3 ≤ g + 1 by omega) x).const_mul (-(g : ℂ))
  have hd' : Tendsto (fun t : Finset L.lattice => ∑ l ∈ t, -(g : ℂ) * ((x + l) ^ (g + 1))⁻¹)
      atTop (𝓝 (deriv (eisensteinSum L g) x)) := by
    refine hd.congr fun t => ?_
    simp only [Function.comp_apply]
    exact (HasDerivAt.fun_sum (fun i _ => hterm i hxU)).deriv
  have hs' : Tendsto (fun t : Finset L.lattice => ∑ l ∈ t, -(g : ℂ) * ((x + l) ^ (g + 1))⁻¹)
      atTop (𝓝 (-(g : ℂ) * eisensteinSum L (g + 1) x)) := by
    simpa [Finset.mul_sum] using hs
  have := tendsto_nhds_unique hd' hs'
  rw [← this]
  exact (hFd.differentiableAt (hU.mem_nhds hxU)).hasDerivAt

lemma hasDerivAt_weierstrassP {x : ℂ} (hx : x ∉ L.lattice) : HasDerivAt ℘[L] (℘'[L] x) x := by
  have := ((L.analyticOnNhd_weierstrassP x hx).differentiableAt).hasDerivAt
  rwa [deriv_weierstrassP] at this

lemma hasDerivAt_derivWeierstrassP {x : ℂ} (hx : x ∉ L.lattice) :
    HasDerivAt ℘'[L] (deriv ℘'[L] x) x :=
  ((L.analyticOnNhd_derivWeierstrassP x hx).differentiableAt).hasDerivAt

/-- **`℘'' = 6℘² - g₂/2`** off the lattice, from Mathlib's differential equation `℘'² = 4℘³ - g₂℘ - g₃`. -/
theorem deriv_derivWeierstrassP {x : ℂ} (hx : x ∉ L.lattice) :
    deriv ℘'[L] x = 6 * ℘[L] x ^ 2 - L.g₂ / 2 := by
  have hU : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have hUc : IsPreconnected (L.lattice : Set ℂ)ᶜ := by
    refine (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) ?_).2
    exact Set.countable_coe_iff.mp (countable_of_Lindelof_of_discrete (X := L.lattice))
  have hP := L.analyticOnNhd_weierstrassP
  have hQ := L.analyticOnNhd_derivWeierstrassP
  have hQ' : AnalyticOnNhd ℂ (deriv ℘'[L]) (L.lattice : Set ℂ)ᶜ := hQ.deriv
  set H : ℂ → ℂ := fun z => 2 * deriv ℘'[L] z - 12 * ℘[L] z ^ 2 + L.g₂ with hHdef
  have hH : AnalyticOnNhd ℂ H (L.lattice : Set ℂ)ᶜ := by
    intro z hz
    exact (((analyticAt_const.mul (hQ' z hz)).sub
      (analyticAt_const.mul ((hP z hz).pow 2))).add analyticAt_const)
  have key : ∀ z ∈ (L.lattice : Set ℂ)ᶜ, ℘'[L] z * H z = 0 := by
    intro z hz
    have e : (fun y => ℘'[L] y ^ 2) =ᶠ[𝓝 z] fun y => 4 * ℘[L] y ^ 3 - L.g₂ * ℘[L] y - L.g₃ := by
      filter_upwards [hU.mem_nhds hz] with y hy using L.derivWeierstrassP_sq y hy
    have h1 : HasDerivAt (fun y => ℘'[L] y ^ 2) (2 * ℘'[L] z * deriv ℘'[L] z) z :=
      ((hasDerivAt_derivWeierstrassP L hz).fun_pow 2).congr_deriv (by norm_num)
    have h2 : HasDerivAt (fun y => 4 * ℘[L] y ^ 3 - L.g₂ * ℘[L] y - L.g₃)
        (4 * (3 * ℘[L] z ^ 2 * ℘'[L] z) - L.g₂ * ℘'[L] z) z :=
      ((((hasDerivAt_weierstrassP L hz).fun_pow 3).const_mul 4).sub
        ((hasDerivAt_weierstrassP L hz).const_mul L.g₂) |>.sub_const L.g₃).congr_deriv
        (by norm_num)
    have h3 := h1.unique (h2.congr_of_eventuallyEq e)
    simp only [hHdef]
    linear_combination h3
  have hHx : H x = 0 := by
    rcases (hQ x hx).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
    · exfalso
      have hz := hQ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hx h0
      obtain ⟨c, hc⟩ := hU.exists_is_const_of_deriv_eq_zero hUc
        (L.differentiableOn_weierstrassP) (fun z hz' => by simp [hz hz'])
      have hev : ℘[L] =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => c := by
        have := L.compl_lattice_sdiff_singleton_mem_nhds 0
        filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with z hz1 hz2
        apply hc
        intro hzl
        exact hz1 ⟨hzl, hz2⟩
      have h1 := meromorphicOrderAt_congr hev
      rw [L.order_weierstrassP 0 (zero_mem _)] at h1
      have h2 : (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun _ : ℂ => c) 0 :=
        (analyticAt_const (v := c) (x := (0 : ℂ))).meromorphicOrderAt_nonneg
      rw [← h1] at h2
      revert h2; decide
    · have hz0 : ∀ᶠ z in 𝓝[≠] x, H z = 0 := by
        filter_upwards [hne, nhdsWithin_le_nhds (hU.mem_nhds hx)] with z hz1 hz2
        exact (mul_eq_zero.mp (key z hz2)).resolve_left hz1
      have t1 : Tendsto H (𝓝[≠] x) (𝓝 (H x)) :=
        (hH x hx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have t2 : Tendsto H (𝓝[≠] x) (𝓝 0) :=
        tendsto_const_nhds.congr' (hz0.mono fun z hz => hz.symm)
      exact tendsto_nhds_unique t1 t2
  simp only [hHdef] at hHx
  linear_combination hHx / 2

/-- **Eisenstein's formula for `(4, x)`** (Crelle 35, Beiträge VI, § 8, remark III, (1.), p. 323),
absolutely convergent part: `(4, x) = ℘(x)² - 5 (4*, 0)`, where `℘(x) = (2, x) - (2*, 0)`. -/
@[kb "eisenstein1847" "Crelle 35, § 8, (1.), p. 323: (4, x) = ℘(x)^2 - 5 (4*, 0)"]
theorem eisensteinSum_four {x : ℂ} (hx : x ∉ L.lattice) :
    eisensteinSum L 4 x = ℘[L] x ^ 2 - 5 * L.G 4 := by
  have h3 : eisensteinSum L 3 = fun y => -(1 / 2) * ℘'[L] y := funext (eisensteinSum_three L)
  have hd : HasDerivAt (eisensteinSum L 3) (-(3 : ℂ) * eisensteinSum L 4 x) x := by
    simpa using hasDerivAt_eisensteinSum L (g := 3) le_rfl hx
  rw [h3] at hd
  have := hd.unique ((hasDerivAt_derivWeierstrassP L hx).const_mul (-(1 / 2 : ℂ)))
  rw [deriv_derivWeierstrassP L hx] at this
  unfold PeriodPair.g₂ at this
  linear_combination (-1 / 3 : ℂ) * this

/-- **`(5, x) = (3, x) {(2, x) - (2*, 0)}`** (Eisenstein, Crelle 35, Beiträge VI, § 8, remark III, (3.), p. 324),
with `(2, x) - (2*, 0) = ℘(x)`. -/
@[kb "eisenstein1847" "Crelle 35, § 8, (3.), p. 324: (5, x) = (3, x) {(2, x) - (2*, 0)}"]
theorem eisensteinSum_five {x : ℂ} (hx : x ∉ L.lattice) :
    eisensteinSum L 5 x = eisensteinSum L 3 x * ℘[L] x := by
  have hU : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have hd : HasDerivAt (eisensteinSum L 4) (-(4 : ℂ) * eisensteinSum L 5 x) x := by
    simpa using hasDerivAt_eisensteinSum L (g := 4) (by norm_num) hx
  have hd2 : HasDerivAt (fun y => ℘[L] y ^ 2 - 5 * L.G 4) (2 * ℘[L] x * ℘'[L] x) x := by
    have := ((hasDerivAt_weierstrassP L hx).pow 2).sub_const (5 * L.G 4)
    simpa using this
  have hd3 : HasDerivAt (eisensteinSum L 4) (2 * ℘[L] x * ℘'[L] x) x := by
    refine hd2.congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hx] with y hy using eisensteinSum_four L hy
  have := hd.unique hd3
  rw [eisensteinSum_three]
  linear_combination (-1 / 4 : ℂ) * this

lemma eisensteinSum_six {x : ℂ} (hx : x ∉ L.lattice) :
    eisensteinSum L 6 x = ℘[L] x ^ 3 - (3 / 20) * L.g₂ * ℘[L] x - L.g₃ / 10 := by
  have hU : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have hd : HasDerivAt (eisensteinSum L 5) (-(5 : ℂ) * eisensteinSum L 6 x) x := by
    simpa using hasDerivAt_eisensteinSum L (g := 5) (by norm_num) hx
  have hd2 : HasDerivAt (fun y => -(1 / 2 : ℂ) * (℘'[L] y * ℘[L] y))
      (-(1 / 2 : ℂ) * (deriv ℘'[L] x * ℘[L] x + ℘'[L] x * ℘'[L] x)) x :=
    ((hasDerivAt_derivWeierstrassP L hx).mul (hasDerivAt_weierstrassP L hx)).const_mul _
  have hd3 : HasDerivAt (eisensteinSum L 5)
      (-(1 / 2 : ℂ) * (deriv ℘'[L] x * ℘[L] x + ℘'[L] x * ℘'[L] x)) x := by
    refine hd2.congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [eisensteinSum_five L hy, eisensteinSum_three]; ring
  have := hd.unique hd3
  rw [deriv_derivWeierstrassP L hx] at this
  have hsq := L.derivWeierstrassP_sq x hx
  linear_combination (-1 / 5 : ℂ) * this + (1 / 10 : ℂ) * hsq

/-- **`(7, x) = (3, x) {(4, x) + 2 (4*, 0)}`** (Eisenstein, Crelle 35, Beiträge VI, § 5, (3.), p. 285). -/
@[kb "eisenstein1847" "Crelle 35, Beiträge VI, § 5, (3.), p. 285: (7, x) = (3, x) {(4, x) + 2 (4*, 0)}"]
theorem eisensteinSum_seven {x : ℂ} (hx : x ∉ L.lattice) :
    eisensteinSum L 7 x = eisensteinSum L 3 x * (eisensteinSum L 4 x + 2 * L.G 4) := by
  have hU : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have hd : HasDerivAt (eisensteinSum L 6) (-(6 : ℂ) * eisensteinSum L 7 x) x := by
    simpa using hasDerivAt_eisensteinSum L (g := 6) (by norm_num) hx
  have hP := hasDerivAt_weierstrassP L hx
  have hd2 : HasDerivAt (fun y => ℘[L] y ^ 3 - (3 / 20) * L.g₂ * ℘[L] y - L.g₃ / 10)
      (3 * ℘[L] x ^ 2 * ℘'[L] x - (3 / 20) * L.g₂ * ℘'[L] x) x := by
    have := ((hP.pow 3).sub (hP.const_mul ((3 / 20) * L.g₂))).sub_const (L.g₃ / 10)
    simpa using this
  have hd3 : HasDerivAt (eisensteinSum L 6)
      (3 * ℘[L] x ^ 2 * ℘'[L] x - (3 / 20) * L.g₂ * ℘'[L] x) x := by
    refine hd2.congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hx] with y hy using eisensteinSum_six L hy
  have := hd.unique hd3
  rw [eisensteinSum_three, eisensteinSum_four L hx]
  unfold PeriodPair.g₂ at this
  linear_combination (-1 / 6 : ℂ) * this

end ModularFormsKB.Historical.Eisenstein
