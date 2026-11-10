import Mathlib.Algebra.DualNumber
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import ModularFormsKB.Citation
/-!
# Miyake §6.4–§6.8: elementary lemmas for the trace formula

Miyake, *Modular Forms* (Springer 1989), §6.4–§6.8, pp. 233–262.

* Lemma 6.4.4 (p. 233): the lattice-sum estimate
  $\sum_n ((a+nh)^2+b^2)^{-l} < C(|b|^{1-2l} + |b|^{-2l})$ for $h > 0$, $l > 1/2$.
* Lemma 6.5.1 (1) (p. 244): for a non-scalar $\alpha$ with principal polynomial $X^2 - tX + n$,
  $\mathbb Q[\alpha]$ is an imaginary quadratic field, $\mathbb Q \times \mathbb Q$, or
  $\mathbb Q[\varepsilon]$ ($\varepsilon^2 = 0$) according as $t^2 - 4n$ is negative, a positive
  square, or zero. Miyake's types elliptic / hyperbolic (with cusp fixed points) / parabolic are
  exactly these three discriminant conditions (proof of Lemma 6.5.1); we state the lemma for an
  arbitrary $\mathbb Q$-algebra $B$ in terms of the discriminant.
* Lemma 6.8.2 (p. 260): for $\alpha \in \mathbb Z \times \mathbb Z$ not in $\mathbb Z$, with minimal
  polynomial $X^2 - tX + n$, $t^2 - 4n = m^2$ with $m > 0$ and $[\mathbb Z\times\mathbb Z :
  \mathbb Z[\alpha]] = m$.
-/

open Real

noncomputable section

open Polynomial

namespace ModularFormsKB.Miyake.Wave2B

section LatticeSum

open MeasureTheory Set

/-- Helper: the integrable base function `(1+s²)^{-l}` for `l > 1/2`. -/
theorem phi_integrable {l : ℝ} (hl : 1 / 2 < l) :
    Integrable (fun s : ℝ ↦ ((1 : ℝ) + s ^ 2) ^ (-l)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * l)
    (by simp; linarith)
  refine h.congr (Filter.Eventually.of_forall fun s ↦ ?_)
  simp only [norm_eq_abs, sq_abs]
  congr 1; ring

/-- Helper: scaling identity for the integral of `((h y)^2+b^2)^{-l}` over `(0,∞)`. -/
theorem integral_scaled {h l : ℝ} (hh : 0 < h) (hl : 1 / 2 < l) {b : ℝ} (hb : b ≠ 0) :
    IntegrableOn (fun y : ℝ ↦ ((h * y) ^ 2 + b ^ 2) ^ (-l)) (Ioi 0) ∧
    ∫ y in Ioi (0:ℝ), ((h * y) ^ 2 + b ^ 2) ^ (-l) =
      |b| ^ (-2 * l + 1) / h * ∫ s in Ioi (0:ℝ), ((1:ℝ) + s ^ 2) ^ (-l) := by
  have hb' : 0 < |b| := abs_pos.mpr hb
  set k := h / |b| with hk
  have hkpos : 0 < k := div_pos hh hb'
  have key : ∀ y : ℝ, ((h * y) ^ 2 + b ^ 2) ^ (-l) =
      |b| ^ (-2 * l) * ((1:ℝ) + (k * y) ^ 2) ^ (-l) := by
    intro y
    have : (h * y) ^ 2 + b ^ 2 = (|b|) ^ 2 * ((1:ℝ) + (k * y) ^ 2) := by
      rw [hk]; field_simp; rw [sq_abs]; ring
    rw [this, Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb'.le]; congr 1; push_cast; ring
  simp_rw [key]
  have hI : IntegrableOn (fun y : ℝ ↦ ((1:ℝ) + (k * y) ^ 2) ^ (-l)) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff
      (fun s : ℝ ↦ ((1:ℝ) + s ^ 2) ^ (-l)) 0 hkpos).2 (phi_integrable hl).integrableOn
    exact this
  refine ⟨hI.const_mul _, ?_⟩
  rw [integral_const_mul, integral_comp_mul_left_Ioi (fun s : ℝ ↦ ((1:ℝ) + s ^ 2) ^ (-l)) 0 hkpos]
  simp only [mul_zero, smul_eq_mul, hk]
  have : |b| ^ (-2 * l + 1) = |b| ^ (-2 * l) * |b| := by
    rw [Real.rpow_add hb', Real.rpow_one]
  rw [this]; field_simp

/-- Helper: partial sums of `G(c + j h)`, `c ≥ 0`, with `G(y) = (y²+b²)^{-l}`. -/
theorem partial_sum_le {h l : ℝ} (hh : 0 < h) (hl : 1 / 2 < l) {b : ℝ} (hb : b ≠ 0)
    {c : ℝ} (hc : 0 ≤ c) (N : ℕ) :
    ∑ j ∈ Finset.range N, ((c + j * h) ^ 2 + b ^ 2) ^ (-l) ≤
      (b ^ 2) ^ (-l) + |b| ^ (-2 * l + 1) / h * ∫ s in Ioi (0:ℝ), ((1:ℝ) + s ^ 2) ^ (-l) := by
  obtain ⟨hint, hval⟩ := integral_scaled hh hl hb
  rw [← hval]
  set g : ℝ → ℝ := fun y ↦ ((h * y) ^ 2 + b ^ 2) ^ (-l) with hg
  have hb2 : 0 < b ^ 2 := by positivity
  have gnn : ∀ y, 0 ≤ g y := fun y ↦ by simp only [hg]; positivity
  have gmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → g y ≤ g x := by
    intro x y hx hxy
    simp only [hg]
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    have := mul_le_mul_of_nonneg_left hxy hh.le
    nlinarith [mul_nonneg hh.le hx]
  have hanti : AntitoneOn g (Ici 0) := fun x hx y _ hxy ↦ gmono x y hx hxy
  rcases N with _ | M
  · simp only [Finset.sum_range_zero]
    have : 0 ≤ ∫ y in Ioi (0:ℝ), g y := setIntegral_nonneg measurableSet_Ioi (fun y _ ↦ gnn y)
    have : 0 ≤ (b ^ 2) ^ (-l) := by positivity
    linarith
  · rw [Finset.sum_range_succ']
    have h1 : ∑ i ∈ Finset.range M, ((c + ((i + 1 : ℕ) : ℝ) * h) ^ 2 + b ^ 2) ^ (-l) ≤
        ∑ i ∈ Finset.range M, g (0 + ((i + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum; intro i _
      simp only [hg, zero_add]
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
      have : 0 ≤ ((i + 1 : ℕ) : ℝ) * h := by positivity
      nlinarith
    have h2 : ∑ i ∈ Finset.range M, g (0 + ((i + 1 : ℕ) : ℝ)) ≤ ∫ x in (0:ℝ)..0 + M, g x :=
      AntitoneOn.sum_le_integral (hanti.mono (by
        intro x hx; exact hx.1))
    have h3 : (∫ x in (0:ℝ)..0 + M, g x) ≤ ∫ y in Ioi (0:ℝ), g y := by
      rw [zero_add, intervalIntegral.integral_of_le (by positivity)]
      exact setIntegral_mono_set hint (Filter.Eventually.of_forall gnn)
        (Filter.Eventually.of_forall Ioc_subset_Ioi_self)
    have h4 : ((c + ((0:ℕ):ℝ) * h) ^ 2 + b ^ 2) ^ (-l) ≤ (b ^ 2) ^ (-l) := by
      simp only [Nat.cast_zero, zero_mul, add_zero]
      apply Real.rpow_le_rpow_of_nonpos hb2 _ (by linarith)
      nlinarith
    linarith

/-- Helper: the one-sided sum `∑_{j ≥ 0} G(c + j h)` is summable with the bound of
`partial_sum_le`. -/
theorem one_sided_sum {h l : ℝ} (hh : 0 < h) (hl : 1 / 2 < l) {b : ℝ} (hb : b ≠ 0)
    {c : ℝ} (hc : 0 ≤ c) :
    Summable (fun j : ℕ ↦ ((c + j * h) ^ 2 + b ^ 2) ^ (-l)) ∧
    ∑' j : ℕ, ((c + j * h) ^ 2 + b ^ 2) ^ (-l) ≤
      (b ^ 2) ^ (-l) + |b| ^ (-2 * l + 1) / h * ∫ s in Ioi (0:ℝ), ((1:ℝ) + s ^ 2) ^ (-l) := by
  have hnn : ∀ j : ℕ, 0 ≤ ((c + j * h) ^ 2 + b ^ 2) ^ (-l) := fun j ↦ by positivity
  exact ⟨summable_of_sum_range_le hnn (partial_sum_le hh hl hb hc),
    Real.tsum_le_of_sum_range_le hnn (partial_sum_le hh hl hb hc)⟩

/-- **Miyake, Lemma 6.4.4.** For $h > 0$ and $l > 1/2$ there is $C > 0$ such that for all real
$a$ and all real $b \ne 0$,
$$\sum_{n=-\infty}^{\infty} \big((a+nh)^2+b^2\big)^{-l} < C\,\big(|b|^{-2l+1} + |b|^{-2l}\big)$$
(the series converging). -/
@[kb "miyake1989" "Lemma 6.4.4, p. 233"]
theorem lattice_sum_estimate {h l : ℝ} (hh : 0 < h) (hl : 1 / 2 < l) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, b ≠ 0 →
      Summable (fun n : ℤ ↦ ((a + n * h) ^ 2 + b ^ 2) ^ (-l)) ∧
      ∑' n : ℤ, ((a + n * h) ^ 2 + b ^ 2) ^ (-l) <
        C * (|b| ^ (-2 * l + 1) + |b| ^ (-2 * l)) := by
  set J := ∫ s in Ioi (0:ℝ), ((1:ℝ) + s ^ 2) ^ (-l) with hJ
  have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi (fun s _ ↦ by positivity)
  refine ⟨2 * (1 + J / h) + 1, by positivity, fun a b hb ↦ ?_⟩
  have hb' : 0 < |b| := abs_pos.mpr hb
  set n0 : ℤ := ⌈-a / h⌉ with hn0
  set c := a + n0 * h with hc
  have hc0 : 0 ≤ c := by
    have := Int.le_ceil (-a / h)
    rw [div_le_iff₀ hh] at this
    rw [hc]; linarith
  have hch : c ≤ h := by
    have := Int.ceil_lt_add_one (-a / h)
    rw [← hn0, ← sub_lt_iff_lt_add, lt_div_iff₀ hh] at this
    rw [hc]; nlinarith
  set F : ℤ → ℝ := fun n ↦ ((a + n * h) ^ 2 + b ^ 2) ^ (-l) with hF
  have hshift : ∀ n : ℤ, F (n + n0) = ((c + n * h) ^ 2 + b ^ 2) ^ (-l) := by
    intro n; simp only [hF, hc]; congr 3; push_cast; ring
  have hpos := (one_sided_sum hh hl hb hc0)
  have hneg := (one_sided_sum hh hl hb (sub_nonneg.2 hch))
  have hneg' : ∀ k : ℕ, F ((-((k : ℤ) + 1)) + n0) =
      (((h - c) + k * h) ^ 2 + b ^ 2) ^ (-l) := by
    intro k; rw [hshift]; congr 1; push_cast; ring_nf
  set F' : ℤ → ℝ := fun n ↦ F (n + n0) with hF'
  have hshiftN : ∀ k : ℕ, F' k = ((c + k * h) ^ 2 + b ^ 2) ^ (-l) := by
    intro k; simp only [hF']; rw [hshift]; simp
  have hs1 : Summable (fun k : ℕ ↦ F' k) := hpos.1.congr (fun k ↦ (hshiftN k).symm)
  have hs2 : Summable (fun k : ℕ ↦ F' (-((k : ℤ) + 1))) :=
    hneg.1.congr (fun k ↦ (hneg' k).symm)
  have hsum : Summable F' := Summable.of_nat_of_neg_add_one hs1 hs2
  have hsumF : Summable F := (Equiv.addRight n0).summable_iff.mp hsum
  have htsum : ∑' n : ℤ, F n = ∑' n : ℤ, F' n := ((Equiv.addRight n0).tsum_eq F).symm
  refine ⟨hsumF, ?_⟩
  show ∑' n : ℤ, F n < _
  rw [htsum, tsum_of_nat_of_neg_add_one hs1 hs2]
  have e1 := le_trans (le_of_eq (tsum_congr (fun k : ℕ ↦ hshiftN k))) hpos.2
  have e2 := le_trans (le_of_eq (tsum_congr (fun k : ℕ ↦ hneg' k))) hneg.2
  have hb2 : (b ^ 2) ^ (-l) = |b| ^ (-2 * l) := by
    rw [← sq_abs b, ← Real.rpow_natCast, ← Real.rpow_mul hb'.le]; congr 1; push_cast; ring
  rw [hb2] at e1 e2
  set R := |b| ^ (-2 * l + 1) + |b| ^ (-2 * l) with hR
  have hR0 : 0 < R := by positivity
  have h1 : 0 < |b| ^ (-2 * l) := by positivity
  have h2 : 0 < |b| ^ (-2 * l + 1) := by positivity
  have : |b| ^ (-2 * l) + |b| ^ (-2 * l + 1) / h * J ≤ (1 + J / h) * R := by
    have : |b| ^ (-2 * l + 1) / h * J = J / h * |b| ^ (-2 * l + 1) := by ring
    rw [this]
    have : 0 ≤ J / h := by positivity
    nlinarith [mul_nonneg this h1.le, mul_nonneg this h2.le]
  nlinarith

end LatticeSum

/-- Helper: if `r₁ + r₂ = t`, `r₁ r₂ = n` then `(α - r₁)(α - r₂) = 0`. -/
theorem factor_aux {B : Type*} [Ring B] [Algebra ℚ B] {α : B} {t n : ℚ}
    (hα : α ^ 2 - t • α + algebraMap ℚ B n = 0) (r1 r2 : ℚ) (hsum : r1 + r2 = t)
    (hprod : r1 * r2 = n) :
    (α - algebraMap ℚ B r1) * (α - algebraMap ℚ B r2) = 0 := by
  have h := congrArg (Polynomial.aeval α)
    (show (X - C r1) * (X - C r2) = X ^ 2 - C (r1 + r2) * X + C (r1 * r2) by
      simp only [map_add, map_mul]; ring)
  simp only [map_mul, map_sub, aeval_X, aeval_C, map_pow, map_add] at h
  rw [h]
  subst hsum hprod
  rw [Algebra.smul_def] at hα
  simpa using hα

/-- **Miyake, Lemma 6.5.1 (1), elliptic case.** Let $B$ be a $\mathbb Q$-algebra and
$\alpha \in B$ with $\alpha^2 - t\alpha + n = 0$, $t, n \in \mathbb Q$, $t^2 - 4n < 0$. Then
$\mathbb Q[\alpha]$ is an imaginary quadratic field: a field of degree $2$ over $\mathbb Q$ with
no embedding into $\mathbb R$. -/
@[kb "miyake1989" "Lemma 6.5.1 (1), p. 244"]
theorem adjoin_isImagQuadratic {B : Type*} [Ring B] [Algebra ℚ B] [Nontrivial B] {α : B}
    {t n : ℚ} (hα : α ^ 2 - t • α + algebraMap ℚ B n = 0) (hdisc : t ^ 2 - 4 * n < 0) :
    IsField (Algebra.adjoin ℚ {α}) ∧ Module.finrank ℚ (Algebra.adjoin ℚ {α}) = 2 ∧
      IsEmpty (Algebra.adjoin ℚ {α} →ₐ[ℚ] ℝ) := by
  set p : ℚ[X] := X ^ 2 - C t * X + C n with hp
  have hdeg : p.natDegree = 2 := by
    rw [hp]; compute_degree!
  have hnr : ∀ x, ¬ p.IsRoot x := by
    intro x hx
    simp only [hp, IsRoot, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C] at hx
    nlinarith [sq_nonneg (2 * x - t)]
  have hirr : Irreducible p :=
    irreducible_of_degree_le_three_of_not_isRoot (by simp [hdeg]) hnr
  have : Fact (Irreducible p) := ⟨hirr⟩
  have hp0 : p ≠ 0 := hirr.ne_zero
  have haeval : aeval α p = 0 := by
    rw [Algebra.smul_def] at hα
    simpa [hp] using hα
  let φ : AdjoinRoot p →ₐ[ℚ] B :=
    Ideal.Quotient.liftₐ (Ideal.span {p}) (aeval α) (by
      intro a ha
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.1 ha
      simp [haeval])
  have hφmk : ∀ g : ℚ[X], φ (AdjoinRoot.mk p g) = aeval α g := fun g ↦ rfl
  have hinj : Function.Injective φ := (φ : AdjoinRoot p →+* B).injective
  have hrange : φ.range = Algebra.adjoin ℚ {α} := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective y
      change φ (AdjoinRoot.mk p g) ∈ _
      rw [hφmk]
      exact Polynomial.aeval_mem_adjoin_singleton ℚ α
    · apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff]
      refine ⟨AdjoinRoot.mk p X, ?_⟩
      change φ (AdjoinRoot.mk p X) = α
      rw [hφmk]; simp
  let e : Algebra.adjoin ℚ {α} ≃ₐ[ℚ] AdjoinRoot p :=
    (Subalgebra.equivOfEq _ _ hrange.symm).trans (AlgEquiv.ofInjective φ hinj).symm
  refine ⟨?_, ?_, ?_⟩
  · exact MulEquiv.isField (Field.toIsField (AdjoinRoot p)) e.toRingEquiv.toMulEquiv
  · rw [e.toLinearEquiv.finrank_eq, (AdjoinRoot.powerBasis hp0).finrank,
      AdjoinRoot.powerBasis_dim hp0, hdeg]
  · refine ⟨fun ψ ↦ ?_⟩
    let β : Algebra.adjoin ℚ {α} := ⟨α, Algebra.self_mem_adjoin_singleton ℚ α⟩
    have hβ : β ^ 2 - t • β + algebraMap ℚ _ n = 0 := by
      apply Subtype.ext
      simpa using hα
    have := congrArg ψ hβ
    simp only [map_sub, map_add, map_pow, map_smul, AlgHom.commutes, map_zero] at this
    set x := ψ β
    rw [Algebra.smul_def] at this
    simp only [eq_ratCast] at this
    have h2 : (t : ℝ) ^ 2 - 4 * n < 0 := by exact_mod_cast hdisc
    nlinarith [sq_nonneg (2 * x - t)]

/-- **Miyake, Lemma 6.5.1 (1), hyperbolic case.** If $\alpha \notin \mathbb Q$ satisfies
$\alpha^2 - t\alpha + n = 0$ with $t^2 - 4n = m^2$, $m \ne 0$ rational, then
$\mathbb Q[\alpha] \cong \mathbb Q \times \mathbb Q$. -/
@[kb "miyake1989" "Lemma 6.5.1 (1), p. 244"]
theorem adjoin_equiv_prod {B : Type*} [Ring B] [Algebra ℚ B] {α : B} {t n m : ℚ}
    (hα : α ^ 2 - t • α + algebraMap ℚ B n = 0)
    (hnot : α ∉ Set.range (algebraMap ℚ B)) (hm : m ≠ 0) (hdisc : t ^ 2 - 4 * n = m ^ 2) :
    Nonempty (Algebra.adjoin ℚ {α} ≃ₐ[ℚ] ℚ × ℚ) := by
  have hB : Nontrivial B := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hnot ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨r1, r2, hsum, hprod, hne⟩ : ∃ r1 r2 : ℚ, r1 + r2 = t ∧ r1 * r2 = n ∧ r1 - r2 ≠ 0 := by
    refine ⟨(t + m) / 2, (t - m) / 2, by ring, by linear_combination (1 / 4) * hdisc, ?_⟩
    intro h; apply hm; linarith
  have hvu := factor_aux hα r1 r2 hsum hprod
  set c : ℚ := r1 - r2 with hc
  set u : B := α - algebraMap ℚ B r2 with hu
  set v : B := α - algebraMap ℚ B r1 with hv
  have huv : u = v + c • (1 : B) := by
    rw [hu, hv, hc]
    simp only [Algebra.algebraMap_eq_smul_one, sub_smul]; abel
  have huu : u * u = c • u := by
    calc u * u = (v + c • (1 : B)) * u := by rw [← huv]
      _ = c • u := by rw [add_mul, hvu, zero_add, smul_mul_assoc, one_mul]
  set e : B := c⁻¹ • u with he_def
  have hce : c • e = u := by rw [he_def, smul_smul, mul_inv_cancel₀ hne, one_smul]
  have he : e * e = e := by
    rw [he_def, smul_mul_assoc, mul_smul_comm, huu, smul_smul, smul_smul]
    congr 1
    field_simp
  have hef : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have hfe : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h11 : (1 - e) * (1 - e) = 1 - e := by
    rw [mul_sub, mul_one, hfe, sub_zero]
  have hemem : e ∈ Algebra.adjoin ℚ {α} :=
    Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Algebra.subset_adjoin rfl)
      (Subalgebra.algebraMap_mem _ _)) _
  let f : ℚ × ℚ →ₗ[ℚ] B :=
    (LinearMap.toSpanSingleton ℚ B e).comp (LinearMap.fst ℚ ℚ ℚ) +
      (LinearMap.toSpanSingleton ℚ B (1 - e)).comp (LinearMap.snd ℚ ℚ ℚ)
  have hf : ∀ p, f p = p.1 • e + p.2 • (1 - e) := fun p => rfl
  let φ : ℚ × ℚ →ₐ[ℚ] B :=
    AlgHom.ofLinearMap f (by rw [hf]; simp)
      (by
        intro p q
        rw [hf, hf, hf]
        simp only [add_mul, mul_add, smul_mul_smul_comm, he, hef, hfe, h11, smul_zero, add_zero,
          zero_add, Prod.fst_mul, Prod.snd_mul, mul_smul])
  have hφ : ∀ p, φ p = p.1 • e + p.2 • (1 - e) := fun p => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, y⟩ hp
    rw [hφ] at hp
    simp only at hp
    have hxy : x - y = 0 := by
      by_contra hxy
      apply hnot
      have h1 : (x - y) • e = -(y • (1 : B)) := by
        have : (x - y) • e + y • (1 : B) = 0 := by rw [← hp]; module
        exact eq_neg_of_add_eq_zero_left this
      have h2 : e = (x - y)⁻¹ • (-(y • (1 : B))) := by
        rw [← h1, smul_smul, inv_mul_cancel₀ hxy, one_smul]
      refine ⟨c * ((x - y)⁻¹ * (-y)) + r2, ?_⟩
      have : α = u + algebraMap ℚ B r2 := by rw [hu]; abel
      rw [this, ← hce, h2, map_add, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      simp [smul_smul]
    have hx : x = y := sub_eq_zero.mp hxy
    subst hx
    have : x • (1 : B) = 0 := by rw [← hp]; module
    have hx0 : x = 0 := by
      by_contra h0
      exact one_ne_zero ((smul_eq_zero.mp this).resolve_left h0)
    simp [hx0]
  have hrange : φ.range = Algebra.adjoin ℚ {α} := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      change φ p ∈ _
      rw [hφ]
      exact Subalgebra.add_mem _ (Subalgebra.smul_mem _ hemem _)
        (Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.one_mem _) hemem) _)
    · rw [Algebra.adjoin_le_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨(r1, r2), ?_⟩
      change φ _ = _
      rw [hφ]
      have : r1 = c + r2 := by rw [hc]; ring
      have h3 : z = u + r2 • (1 : B) := by
        rw [hu, Algebra.algebraMap_eq_smul_one]; abel
      simp only
      rw [h3, ← hce, this]
      module
  exact ⟨((AlgEquiv.ofInjective φ hinj).trans (Subalgebra.equivOfEq _ _ hrange)).symm⟩

/-- **Miyake, Lemma 6.5.1 (1), parabolic case.** If $\alpha \notin \mathbb Q$ satisfies
$\alpha^2 - t\alpha + n = 0$ with $t^2 - 4n = 0$, then $\mathbb Q[\alpha] \cong \mathbb Q[\varepsilon]$,
$\varepsilon^2 = 0$ (the dual numbers). -/
@[kb "miyake1989" "Lemma 6.5.1 (1), p. 244"]
theorem adjoin_equiv_dualNumber {B : Type*} [Ring B] [Algebra ℚ B] {α : B} {t n : ℚ}
    (hα : α ^ 2 - t • α + algebraMap ℚ B n = 0)
    (hnot : α ∉ Set.range (algebraMap ℚ B)) (hdisc : t ^ 2 - 4 * n = 0) :
    Nonempty (Algebra.adjoin ℚ {α} ≃ₐ[ℚ] DualNumber ℚ) := by
  have : Nontrivial B := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hnot ⟨0, Subsingleton.elim _ _⟩
  have hr : (t / 2) + t / 2 = t := by ring
  have hr2 : (t / 2) * (t / 2) = n := by linear_combination (1 / 4) * hdisc
  have hε := factor_aux hα (t / 2) (t / 2) hr hr2
  set ε : B := α - algebraMap ℚ B (t / 2) with hεdef
  have hεmem : ε ∈ Algebra.adjoin ℚ {α} :=
    Subalgebra.sub_mem _ (Algebra.subset_adjoin rfl) (Subalgebra.algebraMap_mem _ _)
  have hεnot : ε ∉ Set.range (algebraMap ℚ B) := by
    rintro ⟨c, hc⟩
    apply hnot
    refine ⟨c + t / 2, ?_⟩
    rw [map_add, hc, hεdef]; abel
  let φ : DualNumber ℚ →ₐ[ℚ] B :=
    DualNumber.lift ⟨(Algebra.ofId ℚ B, ε), hε, fun a => (Algebra.commutes a ε).symm⟩
  have hφ : ∀ x : DualNumber ℚ, φ x = algebraMap ℚ B x.fst + algebraMap ℚ B x.snd * ε :=
    fun x => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hφ] at hx
    have hs : x.snd = 0 := by
      by_contra hne
      apply hεnot
      refine ⟨-(x.snd)⁻¹ * x.fst, ?_⟩
      have : ε = algebraMap ℚ B (x.snd)⁻¹ * (-(algebraMap ℚ B x.fst)) := by
        have h2 : algebraMap ℚ B x.snd * ε = -(algebraMap ℚ B x.fst) :=
          eq_neg_of_add_eq_zero_right hx
        calc ε = algebraMap ℚ B (x.snd)⁻¹ * (algebraMap ℚ B x.snd * ε) := by
              rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hne]; simp
          _ = _ := by rw [h2]
      rw [this]; simp [map_mul, map_neg]
    rw [hs] at hx
    simp only [map_zero, zero_mul, add_zero] at hx
    exact TrivSqZeroExt.ext ((algebraMap ℚ B).injective (hx.trans (map_zero _).symm)) hs
  have hrange : φ.range = Algebra.adjoin ℚ {α} := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      change φ x ∈ _
      rw [hφ]
      exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _)
        (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hεmem)
    · rw [Algebra.adjoin_le_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨TrivSqZeroExt.inl (t / 2) + DualNumber.eps, ?_⟩
      change φ _ = _
      rw [hφ]
      simp [hεdef]
  exact ⟨((AlgEquiv.ofInjective φ hinj).trans (Subalgebra.equivOfEq _ _ hrange)).symm⟩

/-- **Miyake, Lemma 6.8.2.** Let $H = \mathbb Q \times \mathbb Q$ with maximal order
$\mathfrak r_0 = \mathbb Z \times \mathbb Z$, let $\alpha \in \mathfrak r_0 \setminus \mathbb Z$
(with $\mathbb Z$ embedded diagonally), and let $X^2 - tX + n$ be its minimal polynomial. Then
$t^2 - 4n = m^2$ with $m > 0$, and $[\mathfrak r_0 : \mathbb Z[\alpha]] = m$. -/
@[kb "miyake1989" "Lemma 6.8.2, p. 260"]
theorem index_adjoin_prod (α : ℤ × ℤ) (hα : α ∉ Set.range (algebraMap ℤ (ℤ × ℤ))) {t n : ℤ}
    (hmin : α ^ 2 - t • α + algebraMap ℤ (ℤ × ℤ) n = 0) :
    ∃ m : ℕ, 0 < m ∧ t ^ 2 - 4 * n = (m : ℤ) ^ 2 ∧
      (Algebra.adjoin ℤ {α}).toSubmodule.toAddSubgroup.index = m := by
  obtain ⟨a, b⟩ := α
  have h1 := congrArg Prod.fst hmin
  have h2 := congrArg Prod.snd hmin
  simp [sq] at h1 h2
  have hab : a ≠ b := by
    rintro rfl
    exact hα ⟨a, by simp [Prod.ext_iff]⟩
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hab
  have ht : t = a + b := by
    have : (a - b) * (a + b - t) = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hsub
    · linarith
  have hn : n = a * b := by subst ht; linear_combination h1
  set m := (a - b).natAbs with hm
  have hmpos : 0 < m := Int.natAbs_pos.mpr hsub
  have hmsq : ((m : ℤ)) ^ 2 = (a - b) ^ 2 := by
    rw [hm, Int.natCast_natAbs, sq_abs]
  refine ⟨m, hmpos, ?_, ?_⟩
  · rw [hmsq, ht, hn]; ring
  · haveI : NeZero m := ⟨hmpos.ne'⟩
    let f : ℤ × ℤ →+ ZMod m :=
      (Int.castAddHom (ZMod m)).comp (AddMonoidHom.fst ℤ ℤ) -
        (Int.castAddHom (ZMod m)).comp (AddMonoidHom.snd ℤ ℤ)
    have hf : ∀ x : ℤ × ℤ, f x = 0 ↔ (m : ℤ) ∣ x.1 - x.2 := by
      intro x
      change ((x.1 : ZMod m) - (x.2 : ZMod m) = 0) ↔ _
      rw [← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hmd : (m : ℤ) ∣ a - b := by rw [hm]; exact Int.natAbs_dvd.mpr dvd_rfl
    have hker : (Algebra.adjoin ℤ {((a, b) : ℤ × ℤ)}).toSubmodule.toAddSubgroup = f.ker := by
      ext ⟨x, y⟩
      rw [AddMonoidHom.mem_ker, hf]
      simp only [Submodule.mem_toAddSubgroup, Subalgebra.mem_toSubmodule]
      constructor
      · intro hx
        let S : Subalgebra ℤ (ℤ × ℤ) :=
          { carrier := {z | (m : ℤ) ∣ z.1 - z.2}
            mul_mem' := by
              intro p q hp hq
              simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul] at *
              have : p.1 * q.1 - p.2 * q.2 = p.1 * (q.1 - q.2) + (p.1 - p.2) * q.2 := by ring
              rw [this]
              exact dvd_add (dvd_mul_of_dvd_right hq _) (dvd_mul_of_dvd_left hp _)
            add_mem' := by
              intro p q hp hq
              simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add] at *
              have : p.1 + q.1 - (p.2 + q.2) = (p.1 - p.2) + (q.1 - q.2) := by ring
              rw [this]; exact dvd_add hp hq
            algebraMap_mem' := by
              intro r; simp }
        have : Algebra.adjoin ℤ {((a, b) : ℤ × ℤ)} ≤ S := by
          rw [Algebra.adjoin_le_iff]
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          subst hz
          exact hmd
        exact this hx
      · intro hk
        have hmd' : (a - b) ∣ (m : ℤ) := by rw [hm]; exact Int.dvd_natAbs.mpr dvd_rfl
        obtain ⟨k, hk⟩ := dvd_trans hmd' hk
        have hmem : ((a, b) : ℤ × ℤ) ∈ Algebra.adjoin ℤ {((a, b) : ℤ × ℤ)} :=
          Algebra.subset_adjoin rfl
        have := Subalgebra.add_mem _ (Subalgebra.smul_mem _ (Subalgebra.one_mem _) x)
          (Subalgebra.smul_mem _ (Subalgebra.sub_mem _ hmem
            (Subalgebra.smul_mem _ (Subalgebra.one_mem _) a)) k)
        convert this using 1
        simp only [Prod.smul_mk, Prod.mk_add_mk, Prod.mk_sub_mk, smul_eq_mul, Prod.ext_iff,
          Prod.fst_one, Prod.snd_one, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
          Prod.smul_fst, Prod.smul_snd]
        constructor <;> simp <;> linarith
    rw [hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top_of_surjective]
    · simp [Nat.card_zmod]
    · intro z
      refine ⟨(z.val, 0), ?_⟩
      simp [f]

end ModularFormsKB.Miyake.Wave2B
