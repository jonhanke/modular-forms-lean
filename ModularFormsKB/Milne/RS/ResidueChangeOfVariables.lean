import TauCeti.Analysis.Contour.Residue.LogDeriv
import TauCeti.Analysis.Contour.MeromorphicLaurent

/-!
# Change of variables for residues

The residue of a meromorphic differential `f dz` on a Riemann surface does not depend on the chart
(Milne, *Modular Functions and Modular Forms*, §1, p. 18). In one variable this is the statement
that, for `φ` analytic at `z₀` and nonconstant, the residue of `(f ∘ φ) φ'` at `z₀` is
`e = ord_{z₀}(φ - φ z₀)` times the residue of `f` at `φ z₀`; in particular it is the residue of `f`
itself when `φ' z₀ ≠ 0` (a local biholomorphic change of coordinates).

## Main results

* `ModularFormsKB.Milne.RS.residue_deriv_eq_zero` -- the residue of a derivative vanishes.
* `ModularFormsKB.Milne.RS.residue_comp_mul_deriv` -- change of variables with ramification `e`.
* `ModularFormsKB.Milne.RS.residue_comp_mul_deriv_of_deriv_ne_zero` -- the unramified case.

The residue is Tau Ceti's `TauCeti.Contour.residue`.
-/

open Filter Topology TauCeti.Contour

namespace ModularFormsKB.Milne.RS

/-- Derivative of a single polar term away from its pole. -/
private theorem hasDerivAt_polar (a z₀ z : ℂ) (m : ℕ) (hz : z ≠ z₀) :
    HasDerivAt (fun w : ℂ ↦ a / (w - z₀) ^ (m + 1))
      (-((m + 1 : ℕ) : ℂ) * a / (z - z₀) ^ (m + 2)) z := by
  have hne : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
  have h1 : HasDerivAt (fun w : ℂ ↦ (w - z₀) ^ (m + 1)) (((m + 1 : ℕ) : ℂ) * (z - z₀) ^ m) z := by
    simpa using ((hasDerivAt_id z).sub_const z₀).fun_pow (m + 1)
  have h2 := (hasDerivAt_const z a).div h1 (pow_ne_zero _ hne)
  convert h2 using 1
  field_simp
  ring

/-- The residue of a derivative vanishes. -/
theorem residue_deriv_eq_zero {F : ℂ → ℂ} {z₀ : ℂ} (hF : MeromorphicAt F z₀) :
    TauCeti.Contour.residue (deriv F) z₀ = 0 := by
  obtain ⟨a, g, hg, hFeq⟩ := exists_laurent_data_of_meromorphicAt hF
  generalize meromorphicPolarOrderAt F z₀ = N at a hFeq
  have hderiv : ∀ᶠ z in 𝓝[≠] z₀, deriv F z =
      deriv g z + ∑ k : Fin N, (-((k.val + 1 : ℕ) : ℂ) * a k) / (z - z₀) ^ (k.val + 2) := by
    have h1 : ∀ᶠ z in 𝓝 z₀, z ≠ z₀ → F z = g z + ∑ k : Fin N, a k / (z - z₀) ^ (k.val + 1) := by
      simpa [eventually_nhdsWithin_iff] using hFeq
    rw [eventually_nhdsWithin_iff]
    filter_upwards [h1.eventually_nhds, hg.eventually_analyticAt] with z hz hga hzne
    have hEq : F =ᶠ[𝓝 z] fun y ↦ g y + ∑ k : Fin N, a k / (y - z₀) ^ (k.val + 1) := by
      filter_upwards [hz, isOpen_ne.mem_nhds hzne] with y hy hy2 using hy hy2
    rw [hEq.deriv_eq]
    refine HasDerivAt.deriv ?_
    have hs := HasDerivAt.fun_sum (u := Finset.univ) (x := z)
      (A := fun (k : Fin N) (y : ℂ) ↦ a k / (y - z₀) ^ (k.val + 1))
      (A' := fun (k : Fin N) ↦ -((k.val + 1 : ℕ) : ℂ) * a k / (z - z₀) ^ (k.val + 2))
      (fun k _ ↦ by
        have := hasDerivAt_polar (a k) z₀ z k.val hzne
        rw [neg_mul, neg_div] at this ⊢
        exact this)
    exact hga.differentiableAt.hasDerivAt.add hs
  have hmono : ∀ k : Fin N, MeromorphicAt
      (fun z ↦ (-((k.val + 1 : ℕ) : ℂ) * a k) / (z - z₀) ^ (k.val + 2)) z₀ :=
    fun k ↦ by fun_prop
  have hgd : AnalyticAt ℂ (deriv g) z₀ := hg.deriv
  have hfun : deriv F =ᶠ[𝓝[≠] z₀] deriv g +
      ∑ k : Fin N, fun z ↦ (-((k.val + 1 : ℕ) : ℂ) * a k) / (z - z₀) ^ (k.val + 2) := by
    filter_upwards [hderiv] with z hz
    simpa [Finset.sum_apply] using hz
  rw [residue_congr_nhdsNE hfun, residue_add hgd.meromorphicAt (MeromorphicAt.sum fun k _ ↦ hmono k),
    residue_eq_zero_of_analyticAt hgd, zero_add, residue_sum _ fun k _ ↦ hmono k]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  simp

/-- One term of the polar part, pulled back along `ψ` (analytic, vanishing at `z₀` to order `e`):
its residue is `a * e` for the simple pole term and `0` for higher-order terms. -/
private theorem residue_polar_term {ψ : ℂ → ℂ} {z₀ : ℂ} {e : ℕ} (hψ : AnalyticAt ℂ ψ z₀)
    (hne : ∀ᶠ z in 𝓝[≠] z₀, ψ z ≠ 0) (hord : meromorphicOrderAt ψ z₀ = ((e : ℤ) : WithTop ℤ))
    (a : ℂ) (n : ℕ) :
    TauCeti.Contour.residue (fun z ↦ a / ψ z ^ (n + 1) * deriv ψ z) z₀ =
      if n = 0 then a * e else 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : (fun z ↦ a / ψ z ^ (0 + 1) * deriv ψ z) = fun z ↦ a * logDeriv ψ z := by
      funext z
      simp [logDeriv_apply, div_mul_eq_mul_div, mul_div_assoc]
    rw [h1, residue_const_mul, residue_logDeriv_eq_meromorphicOrderAt hψ.meromorphicAt hord]
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
    set c : ℂ := -a / ((j + 1 : ℕ) : ℂ)
    set H : ℂ → ℂ := fun z ↦ c * (ψ z ^ (j + 1))⁻¹
    have hHm : MeromorphicAt H z₀ :=
      analyticAt_const.meromorphicAt.mul ((hψ.pow _).meromorphicAt.inv)
    have hdH : ∀ᶠ z in 𝓝[≠] z₀, deriv H z = a / ψ z ^ (j + 1 + 1) * deriv ψ z := by
      have hda : ∀ᶠ z in 𝓝[≠] z₀, AnalyticAt ℂ ψ z :=
        (hψ.eventually_analyticAt).filter_mono nhdsWithin_le_nhds
      filter_upwards [hne, hda] with z hz hza
      have h1 : HasDerivAt (fun y ↦ ψ y ^ (j + 1)) (((j + 1 : ℕ) : ℂ) * ψ z ^ j * deriv ψ z) z :=
        hza.differentiableAt.hasDerivAt.pow (j + 1)
      have h2 := (h1.inv (pow_ne_zero _ hz)).const_mul c
      have h3 : deriv H z = _ := h2.deriv
      rw [h3]
      have hj : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      simp only [c]
      field_simp
      ring
    exact (residue_congr_nhdsNE hdH).symm.trans (residue_deriv_eq_zero hHm)

/-- **Change of variables for residues.** If `φ` is analytic at `z₀`, not constant near `z₀`, with
`φ - φ z₀` of order `e` at `z₀`, and `f` is meromorphic at `φ z₀`, then the residue of `(f ∘ φ) φ'` at `z₀` is `e`
times the residue of `f` at `φ z₀`. -/
theorem residue_comp_mul_deriv {f φ : ℂ → ℂ} {z₀ : ℂ} (hf : MeromorphicAt f (φ z₀))
    (hφ : AnalyticAt ℂ φ z₀) {e : ℕ} (he : analyticOrderAt (fun z ↦ φ z - φ z₀) z₀ = e)
    (he0 : e ≠ 0) :
    TauCeti.Contour.residue (fun z ↦ f (φ z) * deriv φ z) z₀ = e * TauCeti.Contour.residue f (φ z₀) := by
  have _ := he0
  set ψ : ℂ → ℂ := fun z ↦ φ z - φ z₀ with hψdef
  have hψ : AnalyticAt ℂ ψ z₀ := hφ.sub analyticAt_const
  have hord : meromorphicOrderAt ψ z₀ = ((e : ℤ) : WithTop ℤ) := by
    rw [hψ.meromorphicOrderAt_eq, he]
    rfl
  have hne : ∀ᶠ z in 𝓝[≠] z₀, ψ z ≠ 0 := by
    rcases hψ.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (he.symm.trans (analyticOrderAt_eq_top.mpr h)) (by simp)
    · exact h
  have hdψ : deriv ψ = deriv φ := by
    funext z
    exact deriv_sub_const _
  obtain ⟨a, A, hA, hfeq⟩ := exists_laurent_data_of_meromorphicAt hf
  generalize meromorphicPolarOrderAt f (φ z₀) = N at a hfeq
  have htend : Tendsto φ (𝓝[≠] z₀) (𝓝[≠] (φ z₀)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hφ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
      hne.mono fun z hz ↦ by simpa [ψ, sub_eq_zero] using hz⟩
  have hfeq' := htend.eventually hfeq
  have hres_f := residue_of_laurent_expansion hA hfeq
  have hAφ : AnalyticAt ℂ (fun z ↦ A (φ z) * deriv φ z) z₀ :=
    (hA.comp hφ).mul hφ.deriv
  have hmono : ∀ k : Fin N, MeromorphicAt
      (fun z ↦ a k / ψ z ^ (k.val + 1) * deriv ψ z) z₀ := fun k ↦ by
    rw [hdψ]
    exact (analyticAt_const.meromorphicAt.div (hψ.pow _).meromorphicAt).mul hφ.deriv.meromorphicAt
  have hfun : (fun z ↦ f (φ z) * deriv φ z) =ᶠ[𝓝[≠] z₀]
      (fun z ↦ A (φ z) * deriv φ z) +
        ∑ k : Fin N, fun z ↦ a k / ψ z ^ (k.val + 1) * deriv ψ z := by
    filter_upwards [hfeq'] with z hz
    simp only [Pi.add_apply, Finset.sum_apply, hdψ, hz]
    rw [add_mul, Finset.sum_mul]
  rw [residue_congr_nhdsNE hfun,
    residue_add hAφ.meromorphicAt (MeromorphicAt.sum fun k _ ↦ hmono k),
    residue_eq_zero_of_analyticAt hAφ, zero_add, residue_sum _ fun k _ ↦ hmono k, hres_f]
  simp only [fun k : Fin N ↦ residue_polar_term hψ hne hord (a k) k.val]
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · simp
  · rw [dite_eq_left hpos, Finset.sum_eq_single ⟨0, hpos⟩ (fun k _ hk ↦ ite_eq_right fun h0 ↦
      hk (Fin.ext h0)) (by simp)]
    simp [mul_comm]

/-- The unramified case of `residue_comp_mul_deriv`: if `φ' z₀ ≠ 0` then the residue of
`(f ∘ φ) φ'` at `z₀` equals the residue of `f` at `φ z₀` (invariance under a local change of
coordinate). -/
theorem residue_comp_mul_deriv_of_deriv_ne_zero {f φ : ℂ → ℂ} {z₀ : ℂ} (hf : MeromorphicAt f (φ z₀))
    (hφ : AnalyticAt ℂ φ z₀) (hφ' : deriv φ z₀ ≠ 0) :
    TauCeti.Contour.residue (fun z ↦ f (φ z) * deriv φ z) z₀ = TauCeti.Contour.residue f (φ z₀) := by
  have h := residue_comp_mul_deriv hf hφ (e := 1) (by
    simpa using hφ.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hφ') one_ne_zero
  simpa using h

end ModularFormsKB.Milne.RS
