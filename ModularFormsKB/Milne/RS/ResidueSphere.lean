import ModularFormsKB.Milne.RS.DifferentialQuotient
import ModularFormsKB.Milne.RS.HurwitzOrder
import ModularFormsKB.Milne.RS.RatFuncResidue

/-!
# Milne, Proposition 1.12 (b) for the Riemann sphere

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Proposition 1.12 (b), pdf p. 19.

On the Riemann sphere every meromorphic differential is `ω = ρ dz` with `ρ = ω / dz` a meromorphic function
(`RS.diffQuot`), that is a rational function `r` (Tau Ceti's `ratFuncEquiv`). Its residues are those of `r(z) dz` at
the finite points and of `-r(1/u) u⁻² du` at `∞`, and these sum to zero (`RS.sum_residue_ratEval_add_residue_infty`).

Main result: `residueTheoremStatement_sphere : ResidueTheoremStatement (OnePoint ℂ)`.
-/

open Filter Topology Set OnePoint
open scoped Manifold

namespace ModularFormsKB.Milne.RS

open TauCeti.RiemannSurface TauCeti.AlgebraicGeometry MeromorphicFunction ModularFormsKB.Milne.RiemannSurface

theorem eventually_denom_eval_ne_zero (r : RatFunc ℂ) (c : ℂ) : ∀ᶠ v in 𝓝[≠] c, r.denom.eval v ≠ 0 := by
  classical
  have hS : ((r.denom.roots.toFinset.erase c : Finset ℂ) : Set ℂ)ᶜ ∈ 𝓝 c :=
    (Finset.finite_toSet _).isClosed.compl_mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hS, self_mem_nhdsWithin] with v hv hvc h
  apply hv
  simp only [Finset.coe_erase, mem_diff, Finset.mem_coe, Multiset.mem_toFinset, mem_singleton_iff]
  exact ⟨(Polynomial.mem_roots r.denom_ne_zero).2 h, hvc⟩

theorem eventually_denom_eval_inv_ne_zero (r : RatFunc ℂ) : ∀ᶠ u in 𝓝[≠] (0 : ℂ), r.denom.eval u⁻¹ ≠ 0 := by
  classical
  have hS : ((r.denom.roots.toFinset : Finset ℂ) : Set ℂ)ᶜ ∈ cocompact ℂ :=
    (Finset.finite_toSet _).isCompact.compl_mem_cocompact
  rw [← Metric.cobounded_eq_cocompact] at hS
  filter_upwards [tendsto_inv₀_nhdsNE_zero hS] with u hu h
  exact hu (by simpa [Polynomial.mem_roots r.denom_ne_zero] using h)

theorem finitePart_ratFuncEquiv (r : RatFunc ℂ) {z : ℂ} (hz : r.denom.eval z ≠ 0) :
    (ratFuncEquiv r).finitePart z = ratEval r z :=
  finitePart_of_eq_coe (ratFuncEquiv_apply_coe r hz)

theorem coordinate_finitePart_coe (v : ℂ) : (coordinate : MeromorphicFunction (OnePoint ℂ)).finitePart v = v :=
  finitePart_of_eq_coe (coordinate_apply _)

theorem isNonconstant_coordinate : IsNonconstant (coordinate : MeromorphicFunction (OnePoint ℂ)) :=
  ⟨((0 : ℂ) : OnePoint ℂ), ∞, by simp [coordinate_apply]⟩

theorem differential_coordinate_coeff_coe (c v : ℂ) :
    (differential (coordinate : MeromorphicFunction (OnePoint ℂ))).coeff (c : OnePoint ℂ) v = 1 := by
  change deriv (coordinate.finitePart ∘ (chartAt ℂ (c : OnePoint ℂ)).symm) v = 1
  have : (coordinate.finitePart ∘ (chartAt ℂ (c : OnePoint ℂ)).symm : ℂ → ℂ) = id := by
    funext u
    simp [chartAt_coe, coordinate_finitePart_coe]
  rw [this, deriv_id]

theorem differential_coordinate_coeff_infty {u : ℂ} (hu : u ≠ 0) :
    (differential (coordinate : MeromorphicFunction (OnePoint ℂ))).coeff ∞ u = -(u ^ 2)⁻¹ := by
  change deriv (coordinate.finitePart ∘ (chartAt ℂ (∞ : OnePoint ℂ)).symm) u = _
  have : (coordinate.finitePart ∘ (chartAt ℂ (∞ : OnePoint ℂ)).symm : ℂ → ℂ) =ᶠ[𝓝 u] fun v ↦ v⁻¹ := by
    filter_upwards [isOpen_ne.mem_nhds hu] with v hv
    simp [chartAt_infty, invChart_symm_of_ne_zero hv, coordinate_finitePart_coe]
  rw [this.deriv_eq, deriv_inv]

/-- **Milne, Proposition 1.12 (b), for the Riemann sphere**: the residues of a meromorphic differential on the
Riemann sphere sum to zero. -/
@[kb "milne2017mf" "Proposition 1.12 (b), pdf p. 19, for the Riemann sphere"]
theorem residueTheoremStatement_sphere : ResidueTheoremStatement (OnePoint ℂ) := by
  classical
  refine ⟨fun ω ↦ ?_⟩
  set dz := differential (coordinate : MeromorphicFunction (OnePoint ℂ))
  have hdz : ¬ dz.IsZero := differential_not_isZero isNonconstant_coordinate
  set r := ratFuncEquiv.symm (diffQuot ω dz)
  have hr : ratFuncEquiv r = diffQuot ω dz := ratFuncEquiv.apply_symm_apply _
  -- residues at finite points
  have hres_coe : ∀ c : ℂ, ω.res (c : OnePoint ℂ) = TauCeti.Contour.residue (ratEval r) c := by
    intro c
    have hw : c ∈ (chartAt ℂ (c : OnePoint ℂ)).target := by simp [chartAt_coe]
    have h1 := coeff_eventuallyEq_diffQuot_mul ω hdz (c : OnePoint ℂ) hw
    change TauCeti.Contour.residue (ω.coeff (c : OnePoint ℂ)) (chartAt ℂ (c : OnePoint ℂ) (c : OnePoint ℂ)) = _
    simp only [chartAt_coe, affineChart_coe]
    refine TauCeti.Contour.residue_congr_nhdsNE ?_
    filter_upwards [h1, eventually_denom_eval_ne_zero r c] with v hv hv'
    rw [hv, differential_coordinate_coeff_coe, mul_one, ← hr]
    simp only [chartAt_coe, affineChart_symm_apply]
    exact finitePart_ratFuncEquiv r hv'
  -- residue at infinity
  have hres_infty : ω.res ∞ = TauCeti.Contour.residue (fun u ↦ ratEval r u⁻¹ * -(u ^ 2)⁻¹) 0 := by
    have hw : (0 : ℂ) ∈ (chartAt ℂ (∞ : OnePoint ℂ)).target := by simp [chartAt_infty]
    have h1 := coeff_eventuallyEq_diffQuot_mul ω hdz ∞ hw
    change TauCeti.Contour.residue (ω.coeff ∞) (chartAt ℂ (∞ : OnePoint ℂ) ∞) = _
    simp only [chartAt_infty, invChart_infty]
    refine TauCeti.Contour.residue_congr_nhdsNE ?_
    filter_upwards [h1, eventually_denom_eval_inv_ne_zero r, self_mem_nhdsWithin] with v hv hv' hv0
    rw [hv, differential_coordinate_coeff_infty hv0, ← hr]
    simp only [chartAt_infty, invChart_symm_of_ne_zero hv0]
    rw [finitePart_ratFuncEquiv r hv']
  -- the support of the residues
  set S : Finset (OnePoint ℂ) := insert ∞ (r.denom.roots.toFinset.image (fun c : ℂ ↦ (c : OnePoint ℂ)))
  have hsupp : Function.support ω.res ⊆ S := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => simp [S]
    | coe c =>
      by_contra hc
      apply hx
      rw [hres_coe c]
      refine residue_ratEval_eq_zero r fun h ↦ hc ?_
      simp only [S, Finset.coe_insert, Finset.coe_image, mem_insert_iff, mem_image, Finset.mem_coe,
        Multiset.mem_toFinset]
      exact Or.inr ⟨c, (Polynomial.mem_roots r.denom_ne_zero).2 h, rfl⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_insert (by simp),
    Finset.sum_image (fun _ _ _ _ h ↦ OnePoint.coe_injective h), hres_infty, add_comm]
  simp only [hres_coe]
  exact sum_residue_ratEval_add_residue_infty r

end ModularFormsKB.Milne.RS
