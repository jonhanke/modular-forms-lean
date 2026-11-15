import ModularFormsKB.Historical.Jacobi.ModularEquationODE
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Relation
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.ModulusDerivative
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Hypergeometric

/-!
# Jacobi's equation of modular equations for the complete integrals `K`, `K'`, of any degree

Jacobi, *Fundamenta nova* (1829), § 33, (7)–(8), pp. 77–78. `ModularEquationODE`
proves Jacobi's third-order equation for any two solutions `A`, `B` of Legendre's equation whose ratio is
transformed by a Möbius map. Here `A = K`, `B = K'` are Jacobi's complete integrals of the first kind,
`K(k) = ∫₀^{π/2} (1 - k² sin² φ)^{-1/2} dφ`, `K'(k) = K(√(1 - k²))` (Tau Ceti's `TauCeti.Real.legendreK`), and the
modular equation of degree `n` is Jacobi's `Λ'/Λ = n K'/K` (`Λ = K(λ)`, `Λ' = K'(λ)`). The facts used:

* `K` and `K'` solve Legendre's equation `(k - k³) y'' + (1 - 3k²) y' - k y = 0` on `(0, 1)`
  (`isLegendreSolution_legendreK`, `isLegendreSolution_legendreK'`; Tau Ceti
  `legendreK_differential_equation`, analyticity `analyticOnNhd_legendreK`);
* `K > 0`, and the Wronskian `K K'′ - K′ K' = -π / (2(k - k³))` is nonzero (Legendre's relation, Tau Ceti
  `legendre_relation`; `wronskian_legendreK`).

The theorem `jacobi_modular_equation_ode_K` holds for every real degree `n ≠ 0` (Jacobi: `n` a positive
integer). The regularity of `λ` (three times differentiable) remains a hypothesis.
-/

noncomputable section

open Set TauCeti.Real
open scoped Real

namespace ModularFormsKB.Historical.Jacobi

/-- Jacobi's complementary integral `K'(k) = K(√(1 - k²))`. -/
def legendreK' (k : ℝ) : ℝ := legendreK √(1 - k ^ 2)


section KHelpers

lemma sq_sqrt_one_sub {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : √(1 - x ^ 2) ^ 2 = 1 - x ^ 2 := by
  apply Real.sq_sqrt
  nlinarith [hx.1, hx.2]

lemma sqrt_one_sub_mem {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : √(1 - x ^ 2) ∈ Ioo (0 : ℝ) 1 := by
  have h : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  refine ⟨Real.sqrt_pos.2 h, ?_⟩
  exact (Real.sqrt_lt' one_pos).2 (by nlinarith [hx.1])

lemma hasDerivAt_sqrt_one_sub {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ => √(1 - x ^ 2)) (-x / √(1 - x ^ 2)) x := by
  have h : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have h1 : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * x)) x :=
    ((hasDerivAt_pow 2 x).const_sub 1).congr_deriv (by norm_num)
  refine (h1.sqrt h.ne').congr_deriv ?_
  have : √(1 - x ^ 2) ≠ 0 := (Real.sqrt_pos.2 h).ne'
  field_simp

lemma contDiffOn_K : ContDiffOn ℝ 3 legendreK (Ioo (0 : ℝ) 1) :=
  (analyticOnNhd_legendreK.contDiffOn isOpen_Ioo.uniqueDiffOn).mono (Ioo_subset_Ioo (by norm_num) le_rfl)

lemma K_derivs : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt legendreK (deriv legendreK y) y ∧
    HasDerivAt (deriv legendreK) (deriv (deriv legendreK) y) y ∧
      HasDerivAt (deriv (deriv legendreK)) (deriv (deriv (deriv legendreK)) y) y :=
  d3 isOpen_Ioo contDiffOn_K

lemma K_ode {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    y * (1 - y ^ 2) * deriv (deriv legendreK) y + (1 - 3 * y ^ 2) * deriv legendreK y - y * legendreK y = 0 := by
  have := legendreK_differential_equation (k := y) (by nlinarith [hy.1, hy.2])
  exact this

lemma K'_hasDerivAt {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt legendreK' (deriv legendreK √(1 - x ^ 2) * (-x / √(1 - x ^ 2))) x :=
  ((K_derivs _ (sqrt_one_sub_mem hx)).1).comp x (hasDerivAt_sqrt_one_sub hx)

end KHelpers

/-- `K` solves Legendre's equation on `(0, 1)`. -/
theorem isLegendreSolution_legendreK : IsLegendreSolution legendreK := by
  refine ⟨contDiffOn_K, fun k hk => ?_⟩
  have := K_ode hk
  linear_combination this

/-- `K' = K(√(1 - k²))` solves Legendre's equation on `(0, 1)`. -/
theorem isLegendreSolution_legendreK' : IsLegendreSolution legendreK' := by
  have hs3 : ContDiffOn ℝ 3 (fun x : ℝ => √(1 - x ^ 2)) (Ioo (0 : ℝ) 1) := by
    intro x hx
    have h : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    have : ContDiffAt ℝ 3 (fun x : ℝ => 1 - x ^ 2) x :=
      contDiffAt_const.sub (contDiffAt_id.pow 2)
    exact (this.sqrt h.ne').contDiffWithinAt
  refine ⟨contDiffOn_K.comp hs3 (fun x hx => sqrt_one_sub_mem hx), fun k hk => ?_⟩
  obtain ⟨t, ht⟩ : ∃ t, t = √(1 - k ^ 2) := ⟨_, rfl⟩
  have htm : t ∈ Ioo (0 : ℝ) 1 := ht ▸ sqrt_one_sub_mem hk
  have ht0 : 0 < t := htm.1
  have hk2 : k ^ 2 = 1 - t ^ 2 := by rw [ht, sq_sqrt_one_sub hk]; ring
  have hev : deriv legendreK' =ᶠ[nhds k]
      fun x => deriv legendreK √(1 - x ^ 2) * (-x / √(1 - x ^ 2)) :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hk) (fun x hx => (K'_hasDerivAt hx).deriv)
  have hs0 := hasDerivAt_sqrt_one_sub hk
  have hs : HasDerivAt (fun x : ℝ => √(1 - x ^ 2)) (-k / t) k := by rw [ht]; exact hs0
  have hK'k : legendreK' k = legendreK t := by rw [ht]; rfl
  have hg : HasDerivAt (fun x : ℝ => -x / √(1 - x ^ 2))
      ((-1 * t - (-k) * (-k / t)) / t ^ 2) k := by
    have := ((hasDerivAt_id k).neg).div hs (by rw [ht] at ht0; exact ht0.ne')
    refine HasDerivAt.congr_deriv (f := fun x : ℝ => -x / √(1 - x ^ 2)) (by exact this) ?_
    rw [← ht]
    simp
  have h2 : HasDerivAt (fun x : ℝ => deriv legendreK √(1 - x ^ 2) * (-x / √(1 - x ^ 2)))
      (deriv (deriv legendreK) t * (-k / t) * (-k / t) +
        deriv legendreK t * ((-1 * t - (-k) * (-k / t)) / t ^ 2)) k := by
    have K2d := (K_derivs _ (sqrt_one_sub_mem hk)).2.1
    have := (K2d.comp k hs0).mul hg
    simp only [Function.comp_apply] at this
    rw [← ht] at this
    exact this
  have hd2 := (h2.congr_of_eventuallyEq hev).deriv
  have hd1 := (K'_hasDerivAt hk).deriv
  rw [← ht] at hd1
  rw [hd2, hd1]
  have hT := K_ode htm
  have key : (k - k ^ 3) * (deriv (deriv legendreK) t * (-k / t) * (-k / t) +
        deriv legendreK t * ((-1 * t - (-k) * (-k / t)) / t ^ 2)) +
      (1 - 3 * k ^ 2) * (deriv legendreK t * (-k / t)) - k * legendreK t =
      (k / t) * (t * (1 - t ^ 2) * deriv (deriv legendreK) t + (1 - 3 * t ^ 2) * deriv legendreK t
        - t * legendreK t) +
        (k * (k ^ 2 + t ^ 2 - 1) * (t ^ 2 - k ^ 2) / t ^ 2) * deriv (deriv legendreK) t +
        deriv legendreK t * (k * (k ^ 2 + 3 * t ^ 2) / t ^ 3) * (k ^ 2 + t ^ 2 - 1) := by
    have : t ≠ 0 := ht0.ne'
    field_simp
    ring
  have hu : k ^ 2 + t ^ 2 - 1 = 0 := by linarith
  rw [hK'k, key, hT, hu]
  ring

/-- The Wronskian of `K` and `K'` (from Legendre's relation): `K K'′ - K′ K' = -π / (2(k - k³))` on `(0, 1)`. -/
theorem wronskian_legendreK {k : ℝ} (hk : k ∈ Ioo (0 : ℝ) 1) :
    legendreK k * deriv legendreK' k - deriv legendreK k * legendreK' k = -π / (2 * (k - k ^ 3)) := by
  obtain ⟨t, ht⟩ : ∃ t, t = √(1 - k ^ 2) := ⟨_, rfl⟩
  have htm : t ∈ Ioo (0 : ℝ) 1 := ht ▸ sqrt_one_sub_mem hk
  have hk2 : k ^ 2 = 1 - t ^ 2 := by rw [ht, sq_sqrt_one_sub hk]; ring
  have ht2 : t ^ 2 = 1 - k ^ 2 := by linarith
  have hk0 := hk.1
  have ht0 := htm.1
  have hdK := hasDerivAt_legendreK (k := k) (by nlinarith [hk.1, hk.2])
  have hdKt := hasDerivAt_legendreK (k := t) (by nlinarith [htm.1, htm.2])
  have hd1 := (K'_hasDerivAt hk).deriv
  rw [← ht] at hd1
  rw [hd1, hdK.deriv, hdKt.deriv]
  have hL := legendre_relation hk.1 hk.2
  rw [← ht] at hL
  have hπ : π = 2 * (legendreEc k * legendreK t + legendreEc t * legendreK k - legendreK k * legendreK t) := by
    linarith
  have e1 : k - k ^ 3 = k * t ^ 2 := by linear_combination (-k) * hk2
  have e3 : 1 - t ^ 2 = k ^ 2 := by linarith
  have e4 : 1 - k ^ 2 = t ^ 2 := by linarith
  have hK'k : legendreK' k = legendreK t := by rw [ht]; rfl
  rw [hK'k, e1, e3, e4, hπ]
  have : t ≠ 0 := ht0.ne'
  have : k ≠ 0 := hk0.ne'
  have hu : k ^ 2 + t ^ 2 - 1 = 0 := by linarith
  field_simp
  linear_combination (legendreK k * legendreK t) * hu

/-- **Jacobi's differential equation for the modular equations of any degree** (*Fundamenta nova* § 33,
(7)–(8), pp. 77–78): let `n ≠ 0` and let `λ` be three times continuously
differentiable on an open set `I ⊆ (0, 1)`, with values in `(0, 1)`, satisfying the modular relation of
degree `n`, `K'(λ)/K(λ) = n K'(k)/K(k)`. Then on `I`
`3 λ''² - 2 λ' λ''' + λ'² [ ((1 + k²)/(k - k³))² - ((1 + λ²)/(λ - λ³))² λ'² ] = 0`. -/
@[kb "jacobi1829" "§ 33, (7)–(8), pp. 77–78"]
theorem jacobi_modular_equation_ode_K {lam : ℝ → ℝ} {I : Set ℝ} {n : ℝ} (hn : n ≠ 0)
    (hI : IsOpen I) (hI01 : I ⊆ Ioo 0 1) (hlam : ContDiffOn ℝ 3 lam I) (hlam01 : MapsTo lam I (Ioo 0 1))
    (hmod : ∀ k ∈ I, legendreK' (lam k) / legendreK (lam k) = n * (legendreK' k / legendreK k)) :
    ∀ k ∈ I,
      3 * iteratedDeriv 2 lam k ^ 2 - 2 * deriv lam k * iteratedDeriv 3 lam k +
        deriv lam k ^ 2 * (jacobiR k ^ 2 - jacobiR (lam k) ^ 2 * deriv lam k ^ 2) = 0 := by
  refine jacobi_modular_equation_ode (a := n) (b := 0) (c := 0) (d := 1) isLegendreSolution_legendreK
    isLegendreSolution_legendreK' (fun k hk => (legendreK_pos (by nlinarith [hk.1, hk.2])).ne') ?_
    hI hI01 hlam hlam01 (by simpa using hn) (by simp) (by simpa using hmod)
  intro k hk
  rw [wronskian_legendreK hk]
  have : 0 < k - k ^ 3 := by nlinarith [hk.1, hk.2, mul_pos hk.1 hk.1]
  have := Real.pi_pos
  exact (div_neg_of_neg_of_pos (by linarith) (by positivity)).ne

end ModularFormsKB.Historical.Jacobi
