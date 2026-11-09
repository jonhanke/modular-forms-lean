import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Geometry.Manifold.IsManifold.Basic
import TauCeti.Analysis.Complex.Conformal.Area
import TauCeti.Geometry.Manifold.Complex.Chart
import ModularFormsKB.Milne.Ch4.Automorphy
import ModularFormsKB.Citation
/-!
# Milne, Chapter 4: $k$-fold differentials

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 4, pdf pp. 50–52 and 63.

No library has differential forms on Riemann surfaces. Here a **meromorphic $k$-fold differential** on a Riemann
surface $X$ (a charted space over $\mathbb C$ with holomorphic transition maps) is given by its local coefficients:
for each $x \in X$, a meromorphic function $f_x$ on the target of the chart $z_x$ = `chartAt ℂ x`, so that locally
$\omega = f_x(z_x)\,(dz_x)^k$, with the transformation rule $f_x(u) = f_y(\tau(u))\,\tau'(u)^k$ for the transition map
$\tau = z_y \circ z_x^{-1}$ (`KDifferential`), required away from a discrete set of points (as identities of meromorphic
functions). The order of $\omega$ at $x$ is the order of $f_x$ at $z_x(x)$ (`KDifferential.order`); it does not depend
on the chart (`KDifferential.order_eq_of_mem_source`, the claim in Milne's definition).

The **genus** of a compact Riemann surface is the dimension of its space of holomorphic differentials (`genus`).

## Items
- The definition of the order of a $k$-fold differential, p. 51 (`KDifferential.order`,
  `KDifferential.order_eq_of_mem_source`).
- Remark 4.8, on $\mathbb H$: $f(z)(dz)^k$ is invariant under $\Gamma$ iff $f(\gamma z) = (cz+d)^{2k}f(z)$
  (`kDifferential_invariant_iff`); the correspondence with differentials on $\Gamma\backslash\mathbb H$ is part of the
  named statement `ModularFormsKB.Milne.ModularFormDifferential` (Lemma 4.11).
- Example 4.10 (`meromorphicOrderAt_comp_pow`, `meromorphicOrderAt_pullback_pow`).
- Lemma 4.31 (`volume_image_eq_lintegral_norm_deriv_sq`, from Tau Ceti).
-/

open Complex Filter Topology MeasureTheory UpperHalfPlane
open scoped Manifold MatrixGroups ENNReal ContDiff

noncomputable section

namespace ModularFormsKB.Milne

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The transition map $z_y \circ z_x^{-1}$ between the charts at $x$ and at $y$. -/
def transition (x y : X) : ℂ → ℂ := chartAt ℂ y ∘ (chartAt ℂ x).symm

/-- **A meromorphic $k$-fold differential** on a Riemann surface $X$ (p. 51), by its local coefficients $f_x$ in the
charts $z_x$ = `chartAt ℂ x`: $\omega = f_x(z_x)(dz_x)^k$ near $x$. On overlaps
$f_x(u) = f_y(\tau(u))\,\tau'(u)^k$, $\tau = z_y\circ z_x^{-1}$, as meromorphic functions (on a punctured
neighbourhood of every point of the overlap). -/
@[kb "milne2017mf" "Section 4, k-fold differential forms, Remark 4.8 (pdf p. 51)"]
structure KDifferential (k : ℤ) where
  /-- The coefficient in the chart at `x`. -/
  coeff : X → ℂ → ℂ
  meromorphic : ∀ x, ∀ u ∈ (chartAt ℂ x).target, MeromorphicAt (coeff x) u
  compat : ∀ x y, ∀ u ∈ (chartAt ℂ x).target, (chartAt ℂ x).symm u ∈ (chartAt ℂ y).source →
    coeff x =ᶠ[𝓝[≠] u] fun v ↦ coeff y (transition X x y v) * deriv (transition X x y) v ^ k

variable {X}

/-- **The order of a $k$-fold differential** at a point (p. 51): $\omega = f(z)(dz)^k$ has a zero or pole of order
$m$ at a point according as $f$ has one there. -/
@[kb "milne2017mf" "Section 4, order of a k-fold differential (pdf p. 51)"]
def KDifferential.order {k : ℤ} (η : KDifferential X k) (x : X) : WithTop ℤ :=
  meromorphicOrderAt (η.coeff x) (chartAt ℂ x x)

/-- "This definition is independent of the choice of the local coordinate" (p. 51): the order of the coefficient of
$\omega$ in any chart $z_y$ whose domain contains $x$ is the order of $\omega$ at $x$. -/
@[kb "milne2017mf" "Section 4, order of a k-fold differential is independent of the coordinate (pdf p. 51)"]
theorem KDifferential.order_eq_of_mem_source [IsManifold 𝓘(ℂ) ω X] {k : ℤ} (ω' : KDifferential X k) {x y : X}
    (hx : x ∈ (chartAt ℂ y).source) :
    meromorphicOrderAt (ω'.coeff y) (chartAt ℂ y x) = ω'.order x := by
  have hxs : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hu0 : chartAt ℂ x x ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hxs
  have hsrc : (chartAt ℂ x).symm (chartAt ℂ x x) ∈ (chartAt ℂ y).source := by
    rw [(chartAt ℂ x).left_inv hxs]; exact hx
  have hc := ω'.compat x y _ hu0 hsrc
  have han : AnalyticAt ℂ (transition X x y) (chartAt ℂ x x) :=
    TauCeti.analyticAt_symm_trans (IsManifold.chart_mem_maximalAtlas x)
      (IsManifold.chart_mem_maximalAtlas y) hxs hx
  have hd : deriv (transition X x y) (chartAt ℂ x x) ≠ 0 :=
    TauCeti.deriv_symm_trans_ne_zero (IsManifold.chart_mem_maximalAtlas x)
      (IsManifold.chart_mem_maximalAtlas y) hxs hx
  have hτ : transition X x y (chartAt ℂ x x) = chartAt ℂ y x := by
    simp [transition, (chartAt ℂ x).left_inv hxs]
  have hg : AnalyticAt ℂ (fun v ↦ deriv (transition X x y) v ^ k) (chartAt ℂ x x) :=
    han.deriv.zpow hd
  have hg0 : (fun v ↦ deriv (transition X x y) v ^ k) (chartAt ℂ x x) ≠ 0 := zpow_ne_zero _ hd
  unfold KDifferential.order
  rw [meromorphicOrderAt_congr hc]
  have hmul : (fun v ↦ ω'.coeff y (transition X x y v) * deriv (transition X x y) v ^ k) =
      (fun v ↦ deriv (transition X x y) v ^ k) * (ω'.coeff y ∘ transition X x y) := by
    ext v; simp [mul_comm]
  rw [hmul, meromorphicOrderAt_mul_of_ne_zero hg hg0, meromorphicOrderAt_comp_of_deriv_ne_zero han hd,
    hτ]

variable (X) in
/-- The holomorphic differentials ($1$-fold, everywhere holomorphic) on $X$, as a complex vector space: families of
coefficients, holomorphic on each chart target and zero outside it, satisfying the transformation rule exactly. -/
def holomorphicDifferentials : Submodule ℂ (X → ℂ → ℂ) where
  carrier := {c | (∀ x, ∀ u ∉ (chartAt ℂ x).target, c x u = 0) ∧
    (∀ x, DifferentiableOn ℂ (c x) (chartAt ℂ x).target) ∧
    ∀ x y, ∀ u ∈ (chartAt ℂ x).target, (chartAt ℂ x).symm u ∈ (chartAt ℂ y).source →
      c x u = c y (transition X x y u) * deriv (transition X x y) u}
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨fun x u hu ↦ ?_, fun x ↦ (ha2 x).add (hb2 x), fun x y u hu hy ↦ ?_⟩
    · simp [ha1 x u hu, hb1 x u hu]
    · simp only [Pi.add_apply]
      rw [ha3 x y u hu hy, hb3 x y u hu hy, add_mul]
  zero_mem' := by
    refine ⟨fun x u _ ↦ rfl, fun x ↦ differentiableOn_const _, fun x y u _ _ ↦ ?_⟩
    simp
  smul_mem' := by
    rintro c a ⟨ha1, ha2, ha3⟩
    refine ⟨fun x u hu ↦ ?_, fun x ↦ (ha2 x).const_smul c, fun x y u hu hy ↦ ?_⟩
    · simp [ha1 x u hu]
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [ha3 x y u hu hy, mul_assoc]

variable (X) in
/-- **The genus** of a compact Riemann surface $X$: the dimension of the space of holomorphic differentials on $X$
(used in Theorem 4.9 and Proposition 4.12, "g is the genus of $X(\Gamma)$"). For a compact Riemann surface this is the
topological genus; on a non-compact surface the space is infinite-dimensional and `Module.finrank` gives $0$. -/
@[kb "milne2017mf" "Section 4, Theorem 4.9, the genus g of X(Gamma) (pdf p. 51); Section 1, genus"]
def genus : ℕ := Module.finrank ℂ (holomorphicDifferentials X)

/-- **Example 4.10**, functions: for $w(z) = z^e$, $\mathrm{ord}_0(f\circ w) = e\cdot\mathrm{ord}_0(f)$. -/
@[kb "milne2017mf" "Section 4, Example 4.10 (pdf p. 52)"]
theorem meromorphicOrderAt_comp_pow {f : ℂ → ℂ} (hf : MeromorphicAt f 0) {e : ℕ} (he : 1 ≤ e) (m : ℤ)
    (hm : meromorphicOrderAt f 0 = m) :
    meromorphicOrderAt (fun z ↦ f (z ^ e)) 0 = ((e * m : ℤ) : WithTop ℤ) := by
  have he0 : e ≠ 0 := by omega
  have hg : AnalyticAt ℂ (fun z : ℂ ↦ z ^ e) 0 := by fun_prop
  have h0 : (fun z : ℂ ↦ z ^ e) 0 = 0 := by simp [he0]
  have ho : analyticOrderAt (fun z : ℂ ↦ z ^ e - (fun z : ℂ ↦ z ^ e) 0) 0 = (e : ℕ∞) := by
    have : (fun z : ℂ ↦ z ^ e - (fun z : ℂ ↦ z ^ e) 0) = (· - 0) ^ e := by
      ext z; simp [he0]
    rw [this, analyticOrderAt_centeredMonomial]
  have hnc : ¬ EventuallyConst (fun z : ℂ ↦ z ^ e) (𝓝 0) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, ho]
    simp
  have hf' : MeromorphicAt f ((fun z : ℂ ↦ z ^ e) 0) := by rw [h0]; exact hf
  have this := MeromorphicAt.meromorphicOrderAt_comp (g := fun z : ℂ ↦ z ^ e) (x := 0) hf' hg hnc
  rw [ho] at this
  simp only [h0, hm] at this
  change meromorphicOrderAt (f ∘ fun z : ℂ ↦ z ^ e) 0 = _
  rw [this]
  simp [mul_comm]

/-- **Example 4.10**, $k$-fold differentials: for $w(z) = z^e$ and $\omega = f(w)(dw)^k$, the pullback
$w^*\omega = f(z^e)(ez^{e-1})^k(dz)^k$ has $\mathrm{ord}_0(w^*\omega) = e\cdot\mathrm{ord}_0(\omega) + k(e-1)$. -/
@[kb "milne2017mf" "Section 4, Example 4.10 (pdf p. 52)"]
theorem meromorphicOrderAt_pullback_pow {f : ℂ → ℂ} (hf : MeromorphicAt f 0) {e : ℕ} (he : 1 ≤ e) (k : ℤ) (m : ℤ)
    (hm : meromorphicOrderAt f 0 = m) :
    meromorphicOrderAt (fun z ↦ f (z ^ e) * ((e : ℂ) * z ^ (e - 1)) ^ k) 0 =
      ((e * m + k * (e - 1 : ℕ) : ℤ) : WithTop ℤ) := by
  have h1 := meromorphicOrderAt_comp_pow hf he m hm
  have he0 : (e : ℂ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
  have hg : MeromorphicAt (fun z : ℂ ↦ ((e : ℂ) * z ^ (e - 1)) ^ k) 0 := by
    have : MeromorphicAt (fun z : ℂ ↦ (e : ℂ) * z ^ (e - 1)) 0 := by fun_prop
    exact this.zpow k
  have h2 : meromorphicOrderAt (fun z : ℂ ↦ ((e : ℂ) * z ^ (e - 1)) ^ k) 0
      = ((k * (e - 1 : ℕ) : ℤ) : WithTop ℤ) := by
    have h3 : (fun z : ℂ ↦ (e : ℂ) * z ^ (e - 1)) = (e : ℂ) • ((· - 0) ^ (e - 1) : ℂ → ℂ) := by
      ext z; simp
    have h4 : meromorphicOrderAt (fun z : ℂ ↦ (e : ℂ) * z ^ (e - 1)) 0 =
        ((e - 1 : ℕ) : WithTop ℤ) := by
      rw [h3, meromorphicOrderAt_const_smul_eq_meromorphicOrderAt he0]
      exact meromorphicOrderAt_pow_id_sub_const
    have h5 : MeromorphicAt (fun z : ℂ ↦ (e : ℂ) * z ^ (e - 1)) 0 := by fun_prop
    change meromorphicOrderAt ((fun z : ℂ ↦ (e : ℂ) * z ^ (e - 1)) ^ k) 0 = _
    rw [meromorphicOrderAt_zpow h5, h4]
    norm_cast
  have hc : MeromorphicAt (fun z : ℂ ↦ f (z ^ e)) 0 := by
    have hg0 : AnalyticAt ℂ (fun z : ℂ ↦ z ^ e) 0 := by fun_prop
    have hf' : MeromorphicAt f ((fun z : ℂ ↦ z ^ e) 0) := by
      have : (fun z : ℂ ↦ z ^ e) 0 = 0 := by simp; omega
      rw [this]; exact hf
    exact MeromorphicAt.comp_analyticAt (g := fun z : ℂ ↦ z ^ e) (x := 0) hf' hg0
  change meromorphicOrderAt ((fun z : ℂ ↦ f (z ^ e)) * fun z : ℂ ↦ ((e : ℂ) * z ^ (e - 1)) ^ k) 0 = _
  rw [meromorphicOrderAt_mul hc hg, h1, h2]
  norm_cast

/-- **Remark 4.8** (on $\mathbb H$): for a subgroup $\Gamma$ of $\mathrm{SL}_2(\mathbb Z)$ and a function $f$ on
$\mathbb H$, the $k$-fold differential $f(z)(dz)^k$ is invariant under $\Gamma$, i.e.
$f(\gamma z)\,(d(\gamma z)/dz)^k = f(z)$, if and only if $f(\gamma z) = (cz+d)^{2k}f(z)$ for all $\gamma \in \Gamma$
(condition 4.5(a) in weight $2k$). The case $k = 1$ is the statement about $f(z)\,dz$. -/
@[kb "milne2017mf" "Section 4, Remark 4.8 (pdf p. 50)"]
theorem kDifferential_invariant_iff (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℂ → ℂ) :
    (∀ γ ∈ Γ, ∀ z : ℍ, f (moebius γ z) * deriv (moebius γ) z ^ k = f z) ↔
      ∀ γ ∈ Γ, ∀ z : ℍ, f (moebius γ z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ (2 * k) * f z := by
  have hne : ∀ (γ : SL(2, ℤ)) (z : ℍ), (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := by
    intro γ z
    have := denom_ne_zero_of_im (Matrix.SpecialLinearGroup.mapGL ℝ γ) (z := (z : ℂ)) z.im_pos.ne'
    simpa [denom] using this
  have e1 : ∀ (γ : SL(2, ℤ)) (z : ℍ),
      ((γ 1 0 : ℂ) * z + γ 1 1) ^ (2 * k) * ((γ 1 0 : ℂ) * z + γ 1 1) ^ (-2 * k) = 1 := by
    intro γ z
    rw [← zpow_add₀ (hne γ z), show 2 * k + -2 * k = 0 by ring, zpow_zero]
  constructor
  · intro h γ hγ z
    have := h γ hγ z
    rw [deriv_moebius, ← zpow_mul] at this
    rw [← this, mul_left_comm, e1, mul_one]
  · intro h γ hγ z
    rw [deriv_moebius, ← zpow_mul, h γ hγ z, mul_right_comm, e1, one_mul]

/-- **Lemma 4.31**: a holomorphic map $z \mapsto w(z)$ multiplies areas by $|dw/dz|^2$: for $w$ holomorphic on an open
set $U$ and injective on a measurable $s \subseteq U$, $\mathrm{area}(w(s)) = \int_s |w'(z)|^2\,dx\,dy$. This is Tau
Ceti's `TauCeti.volume_image_eq_lintegral_enorm_deriv_sq`. -/
@[kb "milne2017mf" "Section 4, Lemma 4.31 (pdf p. 63)"]
theorem volume_image_eq_lintegral_norm_deriv_sq {U s : Set ℂ} {w : ℂ → ℂ} (hU : IsOpen U)
    (hw : DifferentiableOn ℂ w U) (hs : NullMeasurableSet s volume) (hsU : s ⊆ U) (hinj : Set.InjOn w s) :
    volume (w '' s) = ∫⁻ z in s, ‖deriv w z‖ₑ ^ 2 :=
  TauCeti.volume_image_eq_lintegral_enorm_deriv_sq hU hw hs hsU hinj

end ModularFormsKB.Milne
