import ModularFormsKB.Miyake.Sec4_3.QSeries
import ModularFormsKB.Miyake.Sec4_3.Strip
import ModularFormsKB.Miyake.Sec4_3.Decay
import Mathlib.Analysis.MellinInversion
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit

/-!
# Hecke's converse theorem: the analytic core

The direction (B) ⇒ (A) of Miyake Theorem 4.3.5, by Mellin inversion on two vertical lines and a
contour shift between them. The poles of $\Lambda_N(s;f)$ at $s = 0$ and $s = k$ are removed by
explicit correction terms whose own poles lie outside the strip, so no residue computation is
needed: the corrections are Mellin transforms of the piecewise power functions `Miyake.lowPow`
and `Miyake.highPow`.
-/

open Complex Filter Asymptotics Set MeasureTheory
open scoped Real Topology

noncomputable section

namespace Miyake

/-- $t \mapsto t^a$ on $(0, 1]$, extended by $0$. -/
def lowPow (a : ℂ) (t : ℝ) : ℂ :=
  (Ioc 0 1).indicator (fun u : ℝ ↦ (u : ℂ) ^ a) t

/-- $t \mapsto t^{-a}$ on $[1, \infty)$, extended by $0$ (written as `lowPow a t⁻¹`). -/
def highPow (a : ℂ) (t : ℝ) : ℂ :=
  lowPow a t⁻¹

lemma mellinConvergent_congr {f g : ℝ → ℂ} {s : ℂ} (h : EqOn f g (Ioi 0))
    (hf : MellinConvergent f s) : MellinConvergent g s := by
  refine (integrableOn_congr_fun (fun t ht ↦ ?_) measurableSet_Ioi).1 hf
  simp only [h ht]

lemma mellin_congr {f g : ℝ → ℂ} {s : ℂ} (h : EqOn f g (Ioi 0)) : mellin f s = mellin g s :=
  setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ by simp only [h ht])

/-- $\int_0^1 t^{s+a-1}\,dt = 1/(s+a)$. -/
lemma hasMellin_lowPow (a : ℂ) {s : ℂ} (hs : 0 < s.re + a.re) :
    HasMellin (lowPow a) s (1 / (s + a)) :=
  hasMellin_cpow_Ioc a hs

/-- The Mellin transform of $f(t^{-1})$ at $s$ is that of $f$ at $-s$. -/
lemma HasMellin.comp_inv {f : ℝ → ℂ} {s m : ℂ} (h : HasMellin f (-s) m) :
    HasMellin (fun t ↦ f t⁻¹) s m := by
  refine ⟨?_, by rw [mellin_comp_inv]; exact h.2⟩
  have h1 : MellinConvergent (fun t ↦ f (t ^ (-1 : ℝ))) s :=
    (MellinConvergent.comp_rpow (f := f) (s := s) (a := -1) (by norm_num)).2
      (by simpa [div_neg] using h.1)
  exact mellinConvergent_congr (fun t ht ↦ by simp [Real.rpow_neg_one]) h1

/-- $\int_1^\infty t^{s-a-1}\,dt = 1/(a - s)$. -/
lemma hasMellin_highPow (a : ℂ) {s : ℂ} (hs : s.re < a.re) :
    HasMellin (highPow a) s (1 / (a - s)) := by
  have := HasMellin.comp_inv (hasMellin_lowPow a (s := -s) (by simp; linarith))
  rw [neg_add_eq_sub] at this
  exact this

/-- If $f$ has Mellin transform $m$ at $k - s$, then $t^{-k} f(t^{-1})$ has Mellin transform $m$
at $s$. -/
lemma HasMellin.inv_twist {f : ℝ → ℂ} {k : ℝ} {s m : ℂ} (h : HasMellin f (k - s) m) :
    HasMellin (fun t ↦ (t : ℂ) ^ (-(k : ℂ)) * f t⁻¹) s m := by
  have h1 : HasMellin (fun t ↦ f t⁻¹) (s - k) m := HasMellin.comp_inv (by simpa using h)
  refine ⟨?_, ?_⟩
  · have := (MellinConvergent.cpow_smul (f := fun t ↦ f t⁻¹) (s := s) (a := -(k : ℂ))).2
      (by simpa [sub_eq_add_neg] using h1.1)
    simpa [smul_eq_mul] using this
  · have := mellin_cpow_smul (fun t ↦ f t⁻¹) s (-(k : ℂ))
    simp only [smul_eq_mul] at this
    rw [this, ← sub_eq_add_neg, h1.2]

/-- For $s$ on a vertical line at distance at least $1$ from the real numbers $p$ and $q$,
$\|1/(s-p) - 1/(s-q)\| \le |p - q| / (1 + (\operatorname{Im} s)^2)$. -/
lemma norm_inv_sub_inv_le {s : ℂ} {p q : ℝ} (hp : 1 ≤ |s.re - p|) (hq : 1 ≤ |s.re - q|) :
    ‖1 / (s - p) - 1 / (s - q)‖ ≤ |p - q| / (1 + s.im ^ 2) := by
  have key : ∀ r : ℝ, 1 ≤ |s.re - r| → 1 + s.im ^ 2 ≤ ‖s - r‖ ^ 2 := by
    intro r hr
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]
    have : 1 ≤ (s.re - r) ^ 2 := by
      have := mul_le_mul hr hr zero_le_one (abs_nonneg _)
      rwa [one_mul, ← sq, sq_abs] at this
    nlinarith
  have hp' := key p hp
  have hq' := key q hq
  have hp0 : s - p ≠ 0 := by
    intro h; rw [h, norm_zero] at hp'; nlinarith [sq_nonneg s.im]
  have hq0 : s - q ≠ 0 := by
    intro h; rw [h, norm_zero] at hq'; nlinarith [sq_nonneg s.im]
  have e : 1 / (s - p) - 1 / (s - q) = ((p : ℂ) - q) / ((s - p) * (s - q)) := by
    field_simp; ring
  rw [e, norm_div, norm_mul]
  have hpos : 0 < 1 + s.im ^ 2 := by positivity
  have hprod : 1 + s.im ^ 2 ≤ ‖s - p‖ * ‖s - q‖ := by
    have h1 : 1 ≤ ‖s - p‖ := by nlinarith [norm_nonneg (s - p), sq_nonneg s.im]
    have h2 : 1 ≤ ‖s - q‖ := by nlinarith [norm_nonneg (s - q), sq_nonneg s.im]
    nlinarith [norm_nonneg (s - p), norm_nonneg (s - q), sq_nonneg (‖s - p‖ - ‖s - q‖)]
  rw [show ‖(p : ℂ) - q‖ = |p - q| by rw [← ofReal_sub, norm_real, Real.norm_eq_abs]]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hpos hprod

/-- **Mellin inversion across a strip.** Let $\Lambda$ be holomorphic and bounded on the closed strip
$\beta \le \operatorname{Re} s \le \alpha$ and $O(1/(1+t^2))$ on its two edges. If the Mellin transform
of $R$ converges on the line $\operatorname{Re} s = \alpha$ and equals $\Lambda$ there, and the Mellin
transform of $L$ converges on $\operatorname{Re} s = \beta$ and equals $\Lambda$ there, then $R(x) = L(x)$
at every $x > 0$ where both are continuous. -/
lemma eq_of_mellin_eq_on_strip {R L : ℝ → ℂ} {Λ : ℂ → ℂ} {β α : ℝ} (hβα : β < α)
    (hΛd : DifferentiableOn ℂ Λ {s : ℂ | β ≤ s.re ∧ s.re ≤ α})
    {B : ℝ} (hΛb : ∀ s : ℂ, β ≤ s.re → s.re ≤ α → ‖Λ s‖ ≤ B)
    {A : ℝ} (hα : ∀ t : ℝ, ‖Λ (α + t * I)‖ ≤ A / (1 + t ^ 2))
    (hβ : ∀ t : ℝ, ‖Λ (β + t * I)‖ ≤ A / (1 + t ^ 2))
    (hR : MellinConvergent R α) (hRm : ∀ y : ℝ, mellin R (α + y * I) = Λ (α + y * I))
    (hL : MellinConvergent L β) (hLm : ∀ y : ℝ, mellin L (β + y * I) = Λ (β + y * I))
    {x : ℝ} (hx : 0 < x) (hRx : ContinuousAt R x) (hLx : ContinuousAt L x) : R x = L x := by
  obtain ⟨A', hA'⟩ := strip_decay hβα hΛd hΛb hα hβ
  have hcont : ∀ σ : ℝ, β ≤ σ → σ ≤ α → Continuous fun y : ℝ ↦ Λ (σ + y * I) := fun σ h1 h2 ↦
    hΛd.continuousOn.comp_continuous (by fun_prop) (fun y ↦ ⟨by simpa using h1, by simpa using h2⟩)
  have hvi : ∀ σ : ℝ, β ≤ σ → σ ≤ α → Integrable fun y : ℝ ↦ Λ (σ + y * I) := by
    intro σ h1 h2
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul A') (hcont σ h1 h2).aestronglyMeasurable
      (Eventually.of_forall fun y ↦ ?_)
    have := hA' (σ + y * I) (by simpa using h1) (by simpa using h2)
    simpa [div_eq_mul_inv] using this
  have hRinv := mellinInv_mellin_eq α R hx hR
    ((hvi α hβα.le le_rfl).congr (Eventually.of_forall fun y ↦ (hRm y).symm)) hRx
  have hLinv := mellinInv_mellin_eq β L hx hL
    ((hvi β le_rfl hβα.le).congr (Eventually.of_forall fun y ↦ (hLm y).symm)) hLx
  rw [← hRinv, ← hLinv, mellinInv, mellinInv]
  refine congrArg₂ (· • ·) rfl ?_
  simp_rw [hRm, hLm, smul_eq_mul]
  -- shift the contour for `h s = x ^ (-s) * Λ s`
  set K : ℝ := x ^ (-α) + x ^ (-β) with hK
  have hxs : ∀ s : ℂ, β ≤ s.re → s.re ≤ α → ‖(x : ℂ) ^ (-s)‖ ≤ K := by
    intro s h1 h2
    rw [norm_cpow_eq_rpow_re_of_pos hx, neg_re]
    rcases le_total 1 x with h | h
    · have := Real.rpow_le_rpow_of_exponent_le h (show -s.re ≤ -β by linarith)
      have := Real.rpow_nonneg hx.le (-α)
      linarith
    · have := Real.rpow_le_rpow_of_exponent_ge hx h (show -α ≤ -s.re by linarith)
      have := Real.rpow_nonneg hx.le (-β)
      linarith
  have hd : DifferentiableOn ℂ (fun s ↦ (x : ℂ) ^ (-s) * Λ s) {s : ℂ | β ≤ s.re ∧ s.re ≤ α} := by
    refine DifferentiableOn.mul (fun s _ ↦ ?_) hΛd
    exact ((differentiableAt_id.neg).const_cpow (Or.inl (ofReal_ne_zero.2 hx.ne'))).differentiableWithinAt
  have := integral_vertical_eq_of_decay (h := fun s ↦ (x : ℂ) ^ (-s) * Λ s) hβα.le hd
    (A := K * A') (fun s h1 h2 ↦ by
      rw [norm_mul, mul_div_assoc]
      exact mul_le_mul (hxs s h1 h2) (hA' s h1 h2) (norm_nonneg _)
        (by positivity))
  simpa using this

lemma HasMellin.add' {f g : ℝ → ℂ} {s m m' : ℂ} (hf : HasMellin f s m) (hg : HasMellin g s m') :
    HasMellin (fun t ↦ f t + g t) s (m + m') := by
  obtain ⟨hf1, rfl⟩ := hf; obtain ⟨hg1, rfl⟩ := hg; exact hasMellin_add hf1 hg1

lemma HasMellin.sub' {f g : ℝ → ℂ} {s m m' : ℂ} (hf : HasMellin f s m) (hg : HasMellin g s m') :
    HasMellin (fun t ↦ f t - g t) s (m - m') := by
  obtain ⟨hf1, rfl⟩ := hf; obtain ⟨hg1, rfl⟩ := hg; exact hasMellin_sub hf1 hg1

lemma HasMellin.const_mul' {f : ℝ → ℂ} {s m : ℂ} (c : ℂ) (hf : HasMellin f s m) :
    HasMellin (fun t ↦ c * f t) s (c * m) := by
  obtain ⟨hf1, rfl⟩ := hf; simpa [smul_eq_mul] using hasMellin_const_smul hf1 c

lemma lowPow_of_mem {a : ℂ} {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) : lowPow a t = (t : ℂ) ^ a := by
  simp [lowPow, indicator_of_mem (show t ∈ Ioc 0 1 from ⟨h0, h1⟩)]

lemma highPow_of_lt_one {a : ℂ} {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : highPow a t = 0 := by
  have : 1 < t⁻¹ := (one_lt_inv₀ h0).2 h1
  simp [highPow, lowPow, indicator_of_notMem (show t⁻¹ ∉ Ioc 0 1 from fun h ↦ by linarith [h.2])]

/-- **Hecke (B) ⇒ (A) on the imaginary axis.** Under condition (B) with root number $1$, for
$0 < t < 1$: $f(it/\sqrt N) = t^{-k}\, g(i t^{-1}/\sqrt N)$. -/
lemma hecke_B_imag {k N : ℝ} (hk : 0 < k) (hN : 0 < N) {a b : ℕ → ℂ} {ν : ℝ}
    (ha : a =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ν) (hb : b =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ν)
    (hB : HeckeCondition k N 1 a b) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    qSeries a (I * ((t / √N : ℝ) : ℂ)) =
      (t : ℂ) ^ (-(k : ℂ)) * qSeries b (I * ((t⁻¹ / √N : ℝ) : ℂ)) := by
  obtain ⟨Φ, hΦd, hΦb, σ₀, hR, hL⟩ := hB
  set α : ℝ := max (max σ₀ (ν + 1)) (max k 0) + 1 with hαdef
  set β : ℝ := min (min (k - σ₀) (k - ν - 1)) (min k 0) - 1 with hβdef
  set c : ℝ := α + 1 with hcdef
  set k' : ℝ := β - 1 with hk'def
  have hα1 : σ₀ < α := by
    have := le_max_left σ₀ (ν + 1); have := le_max_left (max σ₀ (ν + 1)) (max k 0); linarith
  have hα2 : ν + 1 < α := by
    have := le_max_right σ₀ (ν + 1); have := le_max_left (max σ₀ (ν + 1)) (max k 0); linarith
  have hα3 : k + 1 ≤ α := by
    have := le_max_left k 0; have := le_max_right (max σ₀ (ν + 1)) (max k 0); linarith
  have hα4 : 1 ≤ α := by
    have := le_max_right k 0; have := le_max_right (max σ₀ (ν + 1)) (max k 0); linarith
  have hβ1 : σ₀ < k - β := by
    have := min_le_left (k - σ₀) (k - ν - 1)
    have := min_le_left (min (k - σ₀) (k - ν - 1)) (min k 0); linarith
  have hβ2 : ν + 1 < k - β := by
    have := min_le_right (k - σ₀) (k - ν - 1)
    have := min_le_left (min (k - σ₀) (k - ν - 1)) (min k 0); linarith
  have hβ3 : β ≤ k - 1 := by
    have := min_le_left k 0; have := min_le_right (min (k - σ₀) (k - ν - 1)) (min k 0); linarith
  have hβ4 : β ≤ -1 := by
    have := min_le_right k 0; have := min_le_right (min (k - σ₀) (k - ν - 1)) (min k 0); linarith
  have hβα : β < α := by linarith
  set F : ℝ → ℂ := fun t ↦ qSeries a (I * ((t / √N : ℝ) : ℂ)) with hFdef
  set G : ℝ → ℂ := fun t ↦ qSeries b (I * ((t / √N : ℝ) : ℂ)) with hGdef
  set corr : ℂ → ℂ := fun s ↦ a 0 * (1 / (s - ((0 : ℝ) : ℂ)) - 1 / (s - c)) +
    b 0 * (1 / (s - k') - 1 / (s - k)) with hcorr
  set Λ : ℂ → ℂ := fun s ↦ Φ s - a 0 / (s - c) - b 0 / (k' - s) with hΛdef
  -- nonvanishing of the denominators
  have hne : ∀ s : ℂ, ∀ p : ℝ, 1 ≤ |s.re - p| → s - p ≠ 0 := by
    intro s p h he
    have : s.re - p = 0 := by simpa using congrArg re he
    rw [this, abs_zero] at h; linarith
  have hne' : ∀ s : ℂ, ∀ p : ℝ, 1 ≤ |s.re - p| → (p : ℂ) - s ≠ 0 := by
    intro s p h he; exact hne s p h (by rw [← neg_sub, he, neg_zero])
  -- Λ on the two lines
  have hΛR : ∀ s : ℂ, s.re = α → Λ s = completedL N a s + corr s := by
    intro s hs
    have h0 : s ≠ 0 := by
      have := hne s 0 (by rw [hs]; simp [abs_of_pos (by linarith : (0:ℝ) < α)]; linarith)
      simpa using this
    have hc := hne s c (by rw [hs, hcdef]; simp)
    have hk1 := hne' s k (by rw [hs, abs_sub_comm, abs_of_neg (by linarith)]; linarith)
    have hk2 := hne' s k' (by rw [hs, abs_of_pos (by linarith)]; linarith)
    have hk3 := hne s k (by rw [hs, abs_of_pos (by linarith)]; linarith)
    have hk4 := hne s k' (by rw [hs, abs_of_pos (by linarith)]; linarith)
    simp only [hΛdef, hcorr, hR s (by rw [hs]; exact hα1), ofReal_zero, sub_zero, one_mul]
    field_simp
    ring
  have hΛL : ∀ s : ℂ, s.re = β → Λ s = completedL N b (k - s) + corr s := by
    intro s hs
    have h0 : s ≠ 0 := by
      have := hne s 0 (by rw [hs]; simp [abs_of_neg (by linarith : β < 0)]; linarith)
      simpa using this
    have hc := hne s c (by rw [hs, abs_sub_comm, abs_of_pos (by linarith)]; linarith)
    have hk1 := hne' s k (by rw [hs, abs_sub_comm, abs_of_pos (by linarith)]; linarith)
    have hk2 := hne' s k' (by rw [hs, hk'def]; simp)
    have hk3 := hne s k (by rw [hs, abs_sub_comm, abs_of_pos (by linarith)]; linarith)
    have hk4 := hne s k' (by rw [hs, hk'def]; simp)
    have hσ : σ₀ < k - s.re := by rw [hs]; exact hβ1
    simp only [hΛdef, hcorr, hL s hσ, one_mul, ofReal_zero, sub_zero]
    field_simp
    ring
  -- the two functions whose Mellin transforms are `Λ` on the two lines
  set Rf : ℝ → ℂ := fun t ↦ (F t - a 0) + a 0 * (lowPow 0 t + highPow c t) +
    b 0 * (lowPow (-k') t - lowPow (-k) t) with hRfdef
  set Lf : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-(k : ℂ)) * (G t⁻¹ - b 0) +
    a 0 * (highPow c t - highPow 0 t) + b 0 * (lowPow (-k') t + highPow k t) with hLfdef
  have hRm : ∀ s : ℂ, s.re = α → HasMellin Rf s (completedL N a s + corr s) := by
    intro s hs
    have h1 : HasMellin (fun t ↦ F t - a 0) s (completedL N a s) :=
      hasMellin_qSeries ha hN (by rw [hs]; exact hα2) (by rw [hs]; linarith)
    have h2 := HasMellin.add' (hasMellin_lowPow 0 (s := s) (by simp; linarith))
      (hasMellin_highPow (c : ℂ) (s := s) (by simp [hs, hcdef]))
    have h3 := HasMellin.sub' (hasMellin_lowPow (-(k' : ℂ)) (s := s) (by simp; linarith))
      (hasMellin_lowPow (-(k : ℂ)) (s := s) (by simp; linarith))
    have := HasMellin.add' (HasMellin.add' h1 (HasMellin.const_mul' (a 0) h2))
      (HasMellin.const_mul' (b 0) h3)
    convert this using 1
    have hc : (c : ℂ) - s ≠ 0 := hne' s c (by rw [hs, hcdef, abs_sub_comm]; simp)
    have hc' : s - c ≠ 0 := hne s c (by rw [hs, hcdef]; simp)
    simp only [hcorr, ofReal_zero, sub_zero, add_zero, ← sub_eq_add_neg]
    rw [show (c : ℂ) - s = -(s - c) by ring, div_neg]
    ring
  have hLm : ∀ s : ℂ, s.re = β → HasMellin Lf s (completedL N b (k - s) + corr s) := by
    intro s hs
    have h1 : HasMellin (fun t ↦ G t - b 0) (k - s) (completedL N b (k - s)) :=
      hasMellin_qSeries hb hN (by simp [hs]; linarith) (by simp [hs]; linarith)
    have h1' := HasMellin.inv_twist (f := fun t ↦ G t - b 0) (k := k) (s := s) h1
    have h2 := HasMellin.sub' (hasMellin_highPow (c : ℂ) (s := s) (by simp [hs]; linarith))
      (hasMellin_highPow 0 (s := s) (by simp [hs]; linarith))
    have h3 := HasMellin.add' (hasMellin_lowPow (-(k' : ℂ)) (s := s) (by simp [hs, hk'def]))
      (hasMellin_highPow (k : ℂ) (s := s) (by simp [hs]; linarith))
    have := HasMellin.add' (HasMellin.add' h1' (HasMellin.const_mul' (a 0) h2))
      (HasMellin.const_mul' (b 0) h3)
    convert this using 1
    simp only [hcorr, ofReal_zero, sub_zero, ← sub_eq_add_neg]
    rw [show (c : ℂ) - s = -(s - c) by ring, div_neg, show (0 : ℂ) - s = -s by ring, div_neg,
      show (k : ℂ) - s = -(s - k) by ring, div_neg]
    ring
  -- differentiability and boundedness on the closed strip
  have hstrip : ∀ s : ℂ, β ≤ s.re → s.re ≤ α → 1 ≤ |s.re - c| ∧ 1 ≤ |s.re - k'| := by
    intro s h1 h2
    refine ⟨?_, ?_⟩
    · rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hΛd : DifferentiableOn ℂ Λ {s : ℂ | β ≤ s.re ∧ s.re ≤ α} := by
    intro s ⟨h1, h2⟩
    have hc := hne s c (hstrip s h1 h2).1
    have hk := hne' s k' (hstrip s h1 h2).2
    refine DifferentiableAt.differentiableWithinAt ?_
    simp only [hΛdef]
    have dn1 : DifferentiableAt ℂ (fun s : ℂ ↦ s - (c : ℂ)) s := by fun_prop
    have dn2 : DifferentiableAt ℂ (fun s : ℂ ↦ (k' : ℂ) - s) s := by fun_prop
    have dc1 : DifferentiableAt ℂ (fun _ : ℂ ↦ a 0) s := differentiableAt_const _
    have dc2 : DifferentiableAt ℂ (fun _ : ℂ ↦ b 0) s := differentiableAt_const _
    have d1 : DifferentiableAt ℂ (fun s : ℂ ↦ a 0 / (s - (c : ℂ))) s := dc1.div dn1 hc
    have d2 : DifferentiableAt ℂ (fun s : ℂ ↦ b 0 / ((k' : ℂ) - s)) s := dc2.div dn2 hk
    exact ((hΦd s).sub d1).sub d2
  obtain ⟨B, hB⟩ := hΦb β α
  have hnorm_ge : ∀ s : ℂ, ∀ p : ℝ, |s.re - p| ≤ ‖s - p‖ := fun s p ↦ by
    simpa using abs_re_le_norm (s - p)
  have hΛb : ∀ s : ℂ, β ≤ s.re → s.re ≤ α → ‖Λ s‖ ≤ B + ‖a 0‖ + ‖b 0‖ := by
    intro s h1 h2
    obtain ⟨hc, hk⟩ := hstrip s h1 h2
    have e1 : ‖a 0 / (s - c)‖ ≤ ‖a 0‖ := by
      rw [norm_div]
      exact div_le_self (norm_nonneg _) (hc.trans (hnorm_ge s c))
    have e2 : ‖b 0 / (k' - s)‖ ≤ ‖b 0‖ := by
      rw [norm_div, norm_sub_rev]
      exact div_le_self (norm_nonneg _) (hk.trans (hnorm_ge s k'))
    have := hB s h1 h2
    calc ‖Λ s‖ ≤ ‖Φ s‖ + ‖a 0 / (s - c)‖ + ‖b 0 / (k' - s)‖ := by
          simp only [hΛdef]; exact (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ B + ‖a 0‖ + ‖b 0‖ := by gcongr
  -- decay on the two lines
  have hcorr_dec : ∀ s : ℂ, (s.re = α ∨ s.re = β) →
      ‖corr s‖ ≤ (‖a 0‖ * |0 - c| + ‖b 0‖ * |k' - k|) / (1 + s.im ^ 2) := by
    intro s hs
    have hd : 1 ≤ |s.re - 0| ∧ 1 ≤ |s.re - c| ∧ 1 ≤ |s.re - k'| ∧ 1 ≤ |s.re - k| := by
      rcases hs with hs | hs <;> rw [hs]
      · refine ⟨?_, ?_, ?_, ?_⟩
        · rw [sub_zero, abs_of_pos (by linarith)]; linarith
        · rw [hcdef]; simp
        · rw [abs_of_pos (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      · refine ⟨?_, ?_, ?_, ?_⟩
        · rw [sub_zero, abs_of_neg (by linarith)]; linarith
        · rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
        · rw [hk'def]; simp
        · rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
    have e1 := norm_inv_sub_inv_le hd.1 hd.2.1
    have e2 := norm_inv_sub_inv_le hd.2.2.1 hd.2.2.2
    calc ‖corr s‖ ≤ ‖a 0‖ * (|0 - c| / (1 + s.im ^ 2)) + ‖b 0‖ * (|k' - k| / (1 + s.im ^ 2)) := by
          simp only [hcorr]
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
          gcongr
      _ = _ := by ring
  obtain ⟨Aa, hAa⟩ := completedL_decay hN (by linarith : (0 : ℝ) < α)
    (lSeriesSummable_of_isBigO ha (by simpa using hα2))
  obtain ⟨Ab, hAb⟩ := completedL_decay hN (by linarith : (0 : ℝ) < k - β)
    (lSeriesSummable_of_isBigO hb (by simpa using hβ2))
  set A : ℝ := Aa + Ab + (‖a 0‖ * |0 - c| + ‖b 0‖ * |k' - k|) with hAdef
  have hAa0 : 0 ≤ Aa := by
    have := (norm_nonneg _).trans (hAa 0); simpa using this
  have hAb0 : 0 ≤ Ab := by
    have := (norm_nonneg _).trans (hAb 0); simpa using this
  have hdecα : ∀ y : ℝ, ‖Λ (α + y * I)‖ ≤ A / (1 + y ^ 2) := by
    intro y
    have hs : ((α : ℂ) + y * I).re = α := by simp
    have him : ((α : ℂ) + y * I).im = y := by simp
    rw [hΛR _ hs]
    have := hcorr_dec _ (Or.inl hs)
    rw [him] at this
    calc _ ≤ ‖completedL N a (α + y * I)‖ + ‖corr (α + y * I)‖ := norm_add_le _ _
      _ ≤ Aa / (1 + y ^ 2) + (‖a 0‖ * |0 - c| + ‖b 0‖ * |k' - k|) / (1 + y ^ 2) :=
          add_le_add (hAa y) this
      _ ≤ A / (1 + y ^ 2) := by
          rw [← add_div]; gcongr; rw [hAdef]; linarith
  have hdecβ : ∀ y : ℝ, ‖Λ (β + y * I)‖ ≤ A / (1 + y ^ 2) := by
    intro y
    have hs : ((β : ℂ) + y * I).re = β := by simp
    have him : ((β : ℂ) + y * I).im = y := by simp
    rw [hΛL _ hs]
    have := hcorr_dec _ (Or.inr hs)
    rw [him] at this
    have hkb : (k : ℂ) - (β + y * I) = ((k - β : ℝ) : ℂ) + (-y : ℝ) * I := by push_cast; ring
    have := hAb (-y)
    calc _ ≤ ‖completedL N b (k - (β + y * I))‖ + ‖corr (β + y * I)‖ := norm_add_le _ _
      _ ≤ Ab / (1 + y ^ 2) + (‖a 0‖ * |0 - c| + ‖b 0‖ * |k' - k|) / (1 + y ^ 2) := by
          rw [hkb]
          refine add_le_add ?_ (hcorr_dec _ (Or.inr hs) |>.trans (by rw [him]))
          simpa using hAb (-y)
      _ ≤ A / (1 + y ^ 2) := by
          rw [← add_div]; gcongr; rw [hAdef]; linarith
  -- continuity at `t`
  have hFc : ContinuousAt F t :=
    (continuousOn_qSeries_imag ⟨ν, ha⟩ hN).continuousAt (Ioi_mem_nhds ht0)
  have hGc : ContinuousAt (fun u : ℝ ↦ G u⁻¹) t :=
    ((continuousOn_qSeries_imag ⟨ν, hb⟩ hN).continuousAt
      (Ioi_mem_nhds (inv_pos.2 ht0))).comp (continuousAt_inv₀ ht0.ne')
  have hpow : ∀ p : ℂ, ContinuousAt (fun u : ℝ ↦ (u : ℂ) ^ p) t := fun p ↦
    continuousAt_ofReal_cpow_const t p (Or.inr ht0.ne')
  have hnear : ∀ᶠ u in 𝓝 t, 0 < u ∧ u < 1 := Ioo_mem_nhds ht0 ht1
  have hRc : ContinuousAt Rf t := by
    have : ContinuousAt (fun u : ℝ ↦ (F u - a 0) + a 0 * ((u : ℂ) ^ (0 : ℂ) + 0) +
        b 0 * ((u : ℂ) ^ (-(k' : ℂ)) - (u : ℂ) ^ (-(k : ℂ)))) t := by
      have m1 : ContinuousAt (fun u : ℝ ↦ F u - a 0) t := hFc.sub continuousAt_const
      have m2 : ContinuousAt (fun u : ℝ ↦ a 0 * ((u : ℂ) ^ (0 : ℂ) + 0)) t :=
        continuousAt_const.mul ((hpow 0).add continuousAt_const)
      have m3 : ContinuousAt (fun u : ℝ ↦ b 0 * ((u : ℂ) ^ (-(k' : ℂ)) - (u : ℂ) ^ (-(k : ℂ)))) t :=
        continuousAt_const.mul ((hpow (-(k' : ℂ))).sub (hpow (-(k : ℂ))))
      exact (m1.add m2).add m3
    refine this.congr (hnear.mono fun u ⟨h0, h1⟩ ↦ ?_)
    simp only [hRfdef, lowPow_of_mem h0 h1.le, highPow_of_lt_one h0 h1]
  have hLc : ContinuousAt Lf t := by
    have : ContinuousAt (fun u : ℝ ↦ (u : ℂ) ^ (-(k : ℂ)) * (G u⁻¹ - b 0) + a 0 * (0 - 0) +
        b 0 * ((u : ℂ) ^ (-(k' : ℂ)) + 0)) t := by
      have m1 : ContinuousAt (fun u : ℝ ↦ (u : ℂ) ^ (-(k : ℂ)) * (G u⁻¹ - b 0)) t :=
        (hpow (-(k : ℂ))).mul (hGc.sub continuousAt_const)
      have m2 : ContinuousAt (fun _ : ℝ ↦ a 0 * ((0 : ℂ) - 0)) t := continuousAt_const
      have m3 : ContinuousAt (fun u : ℝ ↦ b 0 * ((u : ℂ) ^ (-(k' : ℂ)) + 0)) t :=
        continuousAt_const.mul ((hpow (-(k' : ℂ))).add continuousAt_const)
      exact (m1.add m2).add m3
    refine this.congr (hnear.mono fun u ⟨h0, h1⟩ ↦ ?_)
    simp only [hLfdef, lowPow_of_mem h0 h1.le, highPow_of_lt_one h0 h1]
  -- Mellin inversion across the strip
  have key := eq_of_mellin_eq_on_strip hβα hΛd hΛb hdecα hdecβ
    (hRm α (by simp)).1 (fun y ↦ by rw [(hRm _ (by simp)).2, hΛR _ (by simp)])
    (hLm β (by simp)).1 (fun y ↦ by rw [(hLm _ (by simp)).2, hΛL _ (by simp)])
    ht0 hRc hLc
  simp only [hRfdef, hLfdef, lowPow_of_mem ht0 ht1.le, highPow_of_lt_one ht0 ht1] at key
  simp only [hFdef, hGdef] at key
  rw [cpow_zero] at key
  linear_combination key

/-- Two coefficient sequences of polynomial growth have a common growth exponent. -/
lemma CoeffGrowth.exists_common {a b : ℕ → ℂ} (ha : CoeffGrowth a) (hb : CoeffGrowth b) :
    ∃ ν : ℝ, (a =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ν) ∧ (b =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ν) := by
  obtain ⟨ν₁, h₁⟩ := ha
  obtain ⟨ν₂, h₂⟩ := hb
  have mono : ∀ μ : ℝ, μ ≤ max ν₁ ν₂ →
      (fun n : ℕ ↦ (n : ℝ) ^ μ) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ max ν₁ ν₂ := by
    intro μ hμ
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hn' hμ
  exact ⟨max ν₁ ν₂, h₁.trans (mono _ (le_max_left _ _)), h₂.trans (mono _ (le_max_right _ _))⟩

lemma im_neg_one_div_pos {N : ℝ} (hN : 0 < N) {z : ℂ} (hz : 0 < z.im) :
    0 < (-1 / (N * z)).im := by
  have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz
  have hns : 0 < normSq z := normSq_pos.2 hz0
  have : (-1 / ((N : ℂ) * z)).im = z.im / (N * normSq z) := by
    rw [neg_div, neg_im, div_eq_mul_inv, one_mul, mul_inv, mul_comm, ← ofReal_inv, im_mul_ofReal,
      inv_im]
    field_simp
  rw [this]; positivity

/-- The point $-i\sqrt N z$ for $z = it/\sqrt N$ is $t$. -/
lemma neg_I_mul_sqrt_mul_imag {N : ℝ} (hN : 0 < N) (t : ℝ) :
    -I * (√N : ℂ) * (I * ((t / √N : ℝ) : ℂ)) = t := by
  have : (√N : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 hN).ne'
  push_cast
  field_simp
  simp [I_sq]

/-- The point $-1/(Nz)$ for $z = it/\sqrt N$ is $i t^{-1}/\sqrt N$. -/
lemma neg_one_div_imag {N : ℝ} (hN : 0 < N) {t : ℝ} (ht : 0 < t) :
    -1 / ((N : ℂ) * (I * ((t / √N : ℝ) : ℂ))) = I * ((t⁻¹ / √N : ℝ) : ℂ) := by
  have hs : (√N : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 hN).ne'
  have hN' : (N : ℂ) ≠ 0 := ofReal_ne_zero.2 hN.ne'
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
  have hsq : (√N : ℂ) * √N = N := by rw [← ofReal_mul, Real.mul_self_sqrt hN.le]
  push_cast
  field_simp
  rw [← hsq]
  ring_nf
  rw [I_sq]
  ring

/-- **Hecke (B) ⇒ (A)** (Miyake Theorem 4.3.5): from the imaginary axis to $\mathbb H$ by the identity
theorem. -/
lemma hecke_A_of_B {k N : ℝ} (hk : 0 < k) (hN : 0 < N) {a b : ℕ → ℂ}
    (ha : CoeffGrowth a) (hb : CoeffGrowth b) (hB : HeckeCondition k N 1 a b) :
    ∀ z : ℂ, 0 < z.im →
      qSeries b z = (-I * (√N : ℂ) * z) ^ (-(k : ℂ)) * qSeries a (-1 / (N * z)) := by
  obtain ⟨ν, ha', hb'⟩ := ha.exists_common hb
  set U : Set ℂ := {z : ℂ | 0 < z.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_im
  have hUc : IsPreconnected U := (convex_halfSpace_gt Complex.imLm.isLinear 0).isPreconnected
  have hsN : 0 < √N := Real.sqrt_pos.2 hN
  have h1 : DifferentiableOn ℂ (qSeries b) U := differentiableOn_qSeries hb
  have h2 : DifferentiableOn ℂ
      (fun z ↦ (-I * (√N : ℂ) * z) ^ (-(k : ℂ)) * qSeries a (-1 / (N * z))) U := by
    intro z hz
    have hz0 : z ≠ 0 := fun h ↦ by simp [h, hU] at hz
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.mul ?_ ?_)
    · refine (differentiableAt_id.const_mul _).cpow_const ?_
      refine mem_slitPlane_iff.2 (Or.inl ?_)
      simp only [hU, Set.mem_ofPred_eq] at hz
      simp [mul_re, mul_im]
      positivity
    · have hd := (differentiableOn_qSeries ha).differentiableAt
        (hUo.mem_nhds (im_neg_one_div_pos hN hz))
      refine DifferentiableAt.comp (g := qSeries a) (f := fun w : ℂ ↦ -1 / ((N : ℂ) * w)) z hd ?_
      have hne : (N : ℂ) * z ≠ 0 := mul_ne_zero (ofReal_ne_zero.2 hN.ne') hz0
      fun_prop (disch := exact hne)
  set z₀ : ℂ := I * ((2 / √N : ℝ) : ℂ) with hz₀
  have hz₀U : z₀ ∈ U := by simp [hz₀, hU]; positivity
  set φ : ℝ → ℂ := fun u ↦ I * ((u / √N : ℝ) : ℂ) with hφ
  have hφinj : ∀ u v, φ u = φ v → u = v := by
    intro u v h
    have := congrArg im h
    simp [hφ] at this
    field_simp at this
    exact this
  have hφt : Tendsto φ (𝓝[≠] 2) (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((by fun_prop : Continuous φ).tendsto 2).mono_left (nhdsWithin_le_nhds (s := {2}ᶜ))
      convert this using 2
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact fun h ↦ hu (hφinj u 2 h)
  have hev : ∀ᶠ u in 𝓝[≠] (2 : ℝ), 1 < u :=
    eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds (by norm_num))
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀,
      qSeries b z = (-I * (√N : ℂ) * z) ^ (-(k : ℂ)) * qSeries a (-1 / (N * z)) := by
    refine hφt.frequently (Eventually.frequently ?_)
    filter_upwards [hev] with u hu
    have hu0 : 0 < u := by linarith
    have key := hecke_B_imag hk hN ha' hb' hB (t := u⁻¹) (inv_pos.2 hu0) (inv_lt_one_of_one_lt₀ hu)
    rw [inv_inv] at key
    simp only [hφ]
    rw [neg_I_mul_sqrt_mul_imag hN, neg_one_div_imag hN hu0]
    have hinv : ((u⁻¹ : ℝ) : ℂ) ^ (-(k : ℂ)) = ((u : ℂ) ^ (-(k : ℂ)))⁻¹ := by
      rw [ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hu0.le]; exact Real.pi_ne_zero.symm)]
    have hne : (u : ℂ) ^ (-(k : ℂ)) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; simp [hu0.ne']
    rw [key, hinv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  exact (h1.analyticOnNhd hUo).eqOn_of_preconnected_of_frequently_eq (h2.analyticOnNhd hUo) hUc
    hz₀U hfreq

/-- Exponential decay of $f(it/\sqrt N) - a_0$ as $t \to \infty$, in the form needed by FE-pairs. -/
lemma qSeries_imag_sub_isBigO {a : ℕ → ℂ} (ha : CoeffGrowth a) {N : ℝ} (hN : 0 < N) (r : ℝ) :
    (fun t : ℝ ↦ qSeries a (I * ((t / √N : ℝ) : ℂ)) - a 0) =O[atTop] (· ^ r) := by
  obtain ⟨C, hC⟩ := qSeries_sub_bound_large ha
  have hsN : 0 < √N := Real.sqrt_pos.2 hN
  have h1 : (fun t : ℝ ↦ qSeries a (I * ((t / √N : ℝ) : ℂ)) - a 0) =O[atTop]
      fun t : ℝ ↦ Real.exp (-(2 * π / √N) * t) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop √N] with t ht
    have hz : 1 ≤ (I * ((t / √N : ℝ) : ℂ)).im := by
      simp only [mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul, zero_add]
      rw [le_div_iff₀ hsN]; linarith
    refine (hC _ hz).trans (le_of_eq ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    congr 2
    simp only [mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul, zero_add]
    ring
  exact h1.trans (isLittleO_exp_neg_mul_rpow_atTop (by positivity) r).isBigO

/-- The weak FE-pair $(f(it/\sqrt N), g(it/\sqrt N))$ attached to a solution of (A). -/
def heckeFEPair {k N : ℝ} (hk : 0 < k) (hN : 0 < N) {a b : ℕ → ℂ}
    (ha : CoeffGrowth a) (hb : CoeffGrowth b)
    (hA : ∀ z : ℂ, 0 < z.im →
      qSeries b z = (-I * (√N : ℂ) * z) ^ (-(k : ℂ)) * qSeries a (-1 / (N * z))) :
    WeakFEPair ℂ where
  f t := qSeries a (I * ((t / √N : ℝ) : ℂ))
  g t := qSeries b (I * ((t / √N : ℝ) : ℂ))
  k := k
  ε := 1
  f₀ := a 0
  g₀ := b 0
  hf_int := (continuousOn_qSeries_imag ha hN).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_qSeries_imag hb hN).locallyIntegrableOn measurableSet_Ioi
  hk := hk
  hε := one_ne_zero
  h_feq x hx := by
    have hx0 : (0 : ℝ) < x := hx
    have hz : 0 < (I * ((x / √N : ℝ) : ℂ)).im := by
      simp only [mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul, zero_add]
      exact div_pos hx0 (Real.sqrt_pos.2 hN)
    rw [hA _ hz, neg_I_mul_sqrt_mul_imag hN, neg_one_div_imag hN hx0, one_div, one_mul,
      smul_eq_mul, ← mul_assoc, ofReal_cpow hx0.le, ← cpow_add _ _ (ofReal_ne_zero.2 hx0.ne')]
    simp
  hf_top := qSeries_imag_sub_isBigO ha hN
  hg_top := qSeries_imag_sub_isBigO hb hN

/-- **Hecke (A) ⇒ (B)** (Miyake Theorem 4.3.5), via Mathlib's FE-pairs. -/
lemma hecke_B_of_A {k N : ℝ} (hk : 0 < k) (hN : 0 < N) {a b : ℕ → ℂ}
    (ha : CoeffGrowth a) (hb : CoeffGrowth b)
    (hA : ∀ z : ℂ, 0 < z.im →
      qSeries b z = (-I * (√N : ℂ) * z) ^ (-(k : ℂ)) * qSeries a (-1 / (N * z))) :
    HeckeCondition k N 1 a b := by
  obtain ⟨ν, ha', hb'⟩ := ha.exists_common hb
  set P := heckeFEPair hk hN ha hb hA with hP
  refine ⟨P.Λ₀, P.differentiable_Λ₀, WeakFEPair.boundedOnVerticalStrips_Λ₀ P, max k (ν + 1),
    fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · have hks : P.k < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have h1 := (P.hasMellin hks).2
    have h2 := (hasMellin_qSeries ha' hN (lt_of_le_of_lt (le_max_right _ _) hs)
      (by linarith [le_max_left k (ν + 1)])).2
    rw [P.Λ₀_eq, ← h1]
    simp only [hP, heckeFEPair] at h2 ⊢
    rw [h2]
    simp [smul_eq_mul, div_eq_mul_inv]
    ring
  · have hs' : max k (ν + 1) < (k - s).re := by simpa using hs
    have hks : P.symm.k < (k - s).re := lt_of_le_of_lt (le_max_left _ _) hs'
    have h1 := (P.symm.hasMellin hks).2
    have h2 := (hasMellin_qSeries hb' hN (lt_of_le_of_lt (le_max_right _ _) hs')
      (by linarith [le_max_left k (ν + 1)])).2
    have e1 : P.symm.Λ (k - s) = completedL N b (k - s) := by rw [← h1]; exact h2
    have hPk : P.k = k := rfl
    have hPε : P.ε = 1 := rfl
    have hPf : P.f₀ = a 0 := rfl
    have hPg : P.g₀ = b 0 := rfl
    have hfe := P.functional_equation₀ (k - s)
    rw [hPk, sub_sub_cancel, hPε, one_smul] at hfe
    rw [hfe, P.symm_Λ₀_eq, e1, hPk, hPε, hPf, hPg, sub_sub_cancel]
    simp [smul_eq_mul, div_eq_mul_inv]
    ring

end Miyake
