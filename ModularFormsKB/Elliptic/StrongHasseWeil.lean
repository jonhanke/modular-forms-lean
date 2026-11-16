import ModularFormsKB.Elliptic.FunctionalEquation

/-!
# A curve with a newform of level its conductor satisfies the strong Hasse–Weil conjecture

Milne's `StrongHasseWeil E` (Conjecture 11.17, `Milne.Wave4B.StrongHasseWeil`) asks, for every primitive $\chi$ of
conductor $m$ prime to the conductor $N$ of $E$, for entire continuations of
$\Lambda_\chi(E, s) = N^{s/2}(m/2\pi)^s\Gamma(s)\sum a_n\chi(n)n^{-s}$ and of $\Lambda_{\bar\chi}$, bounded in vertical
strips, with $\Lambda_\chi(E, s) = \pm\chi(N)g(\chi)/g(\bar\chi)\,\Lambda_{\bar\chi}(E, 2 - s)$, the sign allowed to
depend on $\chi$.

- `StrongHasseWeilUniform E w`: the same with the sign $w\,\chi(-1)$ for one $w = \pm1$, which is what $E$ with a
  newform gives and what Weil's converse theorem (row 23) needs. `StrongHasseWeilUniform.strongHasseWeil`: it implies
  Milne's form.
- `HasNewform.strongHasseWeilUniform` (row 22): if $E$ has a newform $f$ of level its geometric conductor, then
  `StrongHasseWeilUniform E w_E` with $w_E$ the root number of row 21; hence `HasNewform.strongHasseWeil`, one half
  of Milne's Theorem 11.19 in analytic form, without `ModularIffStrongHasseWeil`.

Proof: Miyake Theorem 4.3.12 (`Miyake.twisted_completedL_cuspForm`) for $f \in S_2(N, 1)$ with
$f|_2\omega_N = \varepsilon f$ (`HasNewform.fricke_eq`) gives
$\Lambda_N(s; f, \chi) = i^2\chi(-N)\frac{W(\chi)}{W(\bar\chi)}\,\varepsilon\,\Lambda_N(2 - s; f, \bar\chi)$, and
$i^2\varepsilon = w_E$. Miyake's $\Lambda_N(s; f, \chi) = (2\pi/(m\sqrt N))^{-s}\Gamma(s)L(s; f, \chi)$ is Milne's
$\Lambda_\chi(E, s)$; the two continuations are matched on $\operatorname{Re}s > 3/2$ by the identity theorem and the
absolute convergence there (`lSeriesSummable_coeffE`).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Complex
open scoped MatrixGroups Real

namespace ModularFormsKB.Elliptic

open HeckeRing.GL2 ModularFormsKB.Milne.Wave4B

/-! ### Auxiliary lemmas -/

private lemma cpow_ofReal_eq {r : ℝ} (hr : 0 < r) (s : ℂ) :
    ((r : ℝ) : ℂ) ^ s = cexp ((Real.log r : ℝ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), ← Complex.ofReal_log hr.le]

/-- Miyake's twisted completed $L$-function is Milne's $\Lambda_\chi(E, s)$ (for every $s$). -/
lemma twistedCompletedL_eq (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ} [NeZero m]
    (χ : DirichletCharacter ℂ m) (s : ℂ) :
    Miyake.twistedCompletedL (geometricConductor E) χ (coeffE E) s = completedTwistedLSeries E χ s := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hN : (0 : ℝ) < geometricConductor E := by exact_mod_cast geometricConductor_pos E
  have hsq : 0 < √(geometricConductor E : ℝ) := Real.sqrt_pos.2 hN
  have hL : Miyake.twist χ (coeffE E) = fun n ↦ (E.LFunction n : ℂ) * χ n :=
    funext fun n ↦ mul_comm _ _
  unfold Miyake.twistedCompletedL completedTwistedLSeries
  rw [hL]
  have h1 : (((2 * π / (m * √(geometricConductor E : ℝ)) : ℝ) : ℂ)) ^ (-s) =
      (geometricConductor E : ℂ) ^ (s / 2) * ((m : ℂ) / (2 * π)) ^ s := by
    have hx : 0 < 2 * π / (m * √(geometricConductor E : ℝ)) := by positivity
    have hmr : 0 < (m : ℝ) / (2 * π) := by positivity
    have e1 : (geometricConductor E : ℂ) = (((geometricConductor E : ℕ) : ℝ) : ℂ) :=
      (Complex.ofReal_natCast _).symm
    have e2 : (m : ℂ) / (2 * π) = (((m : ℝ) / (2 * π) : ℝ) : ℂ) := by push_cast; ring
    have l1 : Real.log (2 * π / (m * √(geometricConductor E : ℝ))) =
        Real.log (2 * π) - (Real.log m + Real.log (geometricConductor E : ℝ) / 2) := by
      rw [Real.log_div (x := 2 * π) (y := m * √(geometricConductor E : ℝ)),
        Real.log_mul (x := (m : ℝ)) (y := √(geometricConductor E : ℝ)), Real.log_sqrt hN.le]
      all_goals positivity
    have l2 : Real.log ((m : ℝ) / (2 * π)) = Real.log m - Real.log (2 * π) := by
      rw [Real.log_div (x := (m : ℝ)) (y := 2 * π)]
      all_goals positivity
    rw [cpow_ofReal_eq hx, e1, e2, cpow_ofReal_eq hN, cpow_ofReal_eq hmr, ← Complex.exp_add, l1, l2]
    congr 1
    push_cast
    ring
  rw [h1]

private lemma lSeriesSummable_twist (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (χ : DirichletCharacter ℂ m) {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable (fun n ↦ (E.LFunction n : ℂ) * χ n) s := by
  have h := DirichletCharacter.LSeriesSummable_mul χ (lSeriesSummable_coeffE E hs)
  exact (LSeriesSummable_congr s (fun {n} _ ↦ by simp only [Pi.mul_apply, coeffE]; ring)).1 h

private lemma abscissa_twist_le (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (χ : DirichletCharacter ℂ m) :
    LSeries.abscissaOfAbsConv (fun n ↦ (E.LFunction n : ℂ) * χ n) ≤ ((3 / 2 : ℝ) : EReal) :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    lSeriesSummable_twist E χ (by simpa using hy)

private lemma differentiableOn_completed (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ} [NeZero m]
    (χ : DirichletCharacter ℂ m) :
    DifferentiableOn ℂ (completedTwistedLSeries E χ) {s : ℂ | 3 / 2 < s.re} := by
  intro s hs
  have hs' : (3 / 2 : ℝ) < s.re := hs
  have hs0 : 0 < s.re := by linarith
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hm' : (m : ℂ) / (2 * π) ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) / (2 * π) := by positivity
    have h2 : (((m : ℝ) / (2 * π) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
    simpa using h2
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold completedTwistedLSeries
  have h1 : DifferentiableAt ℂ (fun s : ℂ ↦ (geometricConductor E : ℂ) ^ (s / 2)) s :=
    (differentiableAt_id.div_const 2).const_cpow
      (Or.inl (by exact_mod_cast (geometricConductor_pos E).ne'))
  have h2 : DifferentiableAt ℂ (fun s : ℂ ↦ ((m : ℂ) / (2 * π)) ^ s) s :=
    differentiableAt_id.const_cpow (Or.inl hm')
  have h3 : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma s (by
      rintro k rfl
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      simp at hs0
      linarith)
  have h4 : DifferentiableAt ℂ (LSeries (fun n ↦ (E.LFunction n : ℂ) * χ n)) s :=
    ((LSeries_analyticOnNhd (fun n ↦ (E.LFunction n : ℂ) * χ n)) s
      ((abscissa_twist_le E χ).trans_lt (EReal.coe_lt_coe_iff.2 hs'))).differentiableAt
  exact ((h1.mul h2).mul h3).mul h4

private lemma isBoundedEntire_of (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ} [NeZero m]
    (χ : DirichletCharacter ℂ m) {Φ : ℂ → ℂ} (hd : Differentiable ℂ Φ)
    (hb : Miyake.BoundedOnVerticalStrips Φ) {σ₀ : ℝ}
    (he : ∀ s : ℂ, σ₀ < s.re → Φ s = Miyake.twistedCompletedL (geometricConductor E) χ (coeffE E) s) :
    IsBoundedEntireContinuation E χ Φ := by
  refine ⟨hd, ?_, hb⟩
  have hA : AnalyticOnNhd ℂ Φ Set.univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hd
  have hB : AnalyticOnNhd ℂ (completedTwistedLSeries E χ) {s : ℂ | 3 / 2 < s.re} :=
    (differentiableOn_completed E χ).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
  have hmem : ((max σ₀ 2 + 1 : ℝ) : ℂ) ∈ {s : ℂ | 3 / 2 < s.re} := by
    rw [Set.mem_ofPred_eq, Complex.ofReal_re]; linarith [le_max_right σ₀ 2]
  have hev : Φ =ᶠ[nhds ((max σ₀ 2 + 1 : ℝ) : ℂ)] completedTwistedLSeries E χ := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨{z : ℂ | max σ₀ 2 < z.re}, (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_,
        fun z hz ↦ ?_⟩
    · rw [Set.mem_ofPred_eq, Complex.ofReal_re]; linarith
    · rw [he z (lt_of_le_of_lt (le_max_left _ _) hz), twistedCompletedL_eq]
  intro s hs
  exact (hA.mono (Set.subset_univ _)).eqOn_of_preconnected_of_eventuallyEq hB
    (convex_halfSpace_re_gt (3 / 2 : ℝ)).isPreconnected hmem hev hs

lemma twistedCompletedL_const_mul (N : ℝ) {m : ℕ} (ψ : DirichletCharacter ℂ m) (C : ℂ)
    (a : ℕ → ℂ) (s : ℂ) :
    Miyake.twistedCompletedL N ψ (fun n ↦ C * a n) s = C * Miyake.twistedCompletedL N ψ a s := by
  have : Miyake.twist ψ (fun n ↦ C * a n) = C • Miyake.twist ψ a := by
    funext n; simp [Miyake.twist]; ring
  unfold Miyake.twistedCompletedL
  rw [this, LSeries_smul]
  ring

/-- **The strong Hasse–Weil conjecture with a uniform sign** (Weil 1967 [unverified]): for one $w = \pm1$ and every
primitive Dirichlet character $\chi$ of conductor $m$ prime to the geometric conductor $N$ of $E$, $\Lambda_\chi(E, s)$
and $\Lambda_{\bar\chi}(E, s)$ have entire continuations bounded in vertical strips with
$\Lambda_\chi(E, s) = w\,\chi(-1)\chi(N)\,g(\chi)/g(\bar\chi)\cdot\Lambda_{\bar\chi}(E, 2 - s)$. A predicate. -/
def StrongHasseWeilUniform (E : WeierstrassCurve ℚ) [E.IsElliptic] (w : ℂ) : Prop :=
  (w = 1 ∨ w = -1) ∧ ∀ (m : ℕ) [NeZero m], Nat.Coprime m (geometricConductor E) →
    ∀ χ : DirichletCharacter ℂ m, χ.IsPrimitive →
      ∃ Λ Λ' : ℂ → ℂ, IsBoundedEntireContinuation E χ Λ ∧ IsBoundedEntireContinuation E χ⁻¹ Λ' ∧
        ∀ s : ℂ, Λ s = w * χ (-1) * χ (geometricConductor E) *
          (gaussSum χ ZMod.stdAddChar / gaussSum χ⁻¹ ZMod.stdAddChar) * Λ' (2 - s)

/-- The uniform-sign form implies Milne's `StrongHasseWeil`: the sign $w\chi(-1)$ is $\pm1$. -/
theorem StrongHasseWeilUniform.strongHasseWeil {E : WeierstrassCurve ℚ} [E.IsElliptic] {w : ℂ}
    (h : StrongHasseWeilUniform E w) : StrongHasseWeil E := by
  intro m _ hm χ hχ
  obtain ⟨Λ, Λ', h1, h2, h3⟩ := h.2 m hm χ hχ
  refine ⟨Λ, Λ', h1, h2, w * χ (-1), ?_, h3⟩
  have hsq : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; simp
  rcases mul_self_eq_one_iff.1 hsq with h' | h' <;> rcases h.1 with hw | hw <;> rw [h', hw] <;>
    norm_num

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] {f : Newform (geometricConductor E) 2}

/-- Weil's constant for the trivial character modulo $N$ and $\chi$ modulo $m$ prime to $N$. -/
lemma weilConstant_one_eq (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ} [NeZero m]
    (hm : m.Coprime (geometricConductor E)) (χ : DirichletCharacter ℂ m) :
    Miyake.weilConstant (1 : DirichletCharacter ℂ (geometricConductor E)) χ =
      χ (-1) * χ (geometricConductor E : ZMod m) *
        (gaussSum χ ZMod.stdAddChar / gaussSum χ⁻¹ ZMod.stdAddChar) := by
  have hu : IsUnit ((m : ℕ) : ZMod (geometricConductor E)) := (ZMod.isUnit_iff_coprime m _).2 hm
  unfold Miyake.weilConstant Miyake.gaussW
  rw [MulChar.one_apply hu, one_mul, neg_eq_neg_one_mul, map_mul]
  ring

private lemma twistedHecke (hf : HasNewform E (geometricConductor E) f) {m : ℕ} [NeZero m]
    (hm : m.Coprime (geometricConductor E)) (χ : DirichletCharacter ℂ m) (hχ : χ.IsPrimitive) :
    Miyake.TwistedHeckeCondition 2 (geometricConductor E) χ
      (Miyake.weilConstant (1 : DirichletCharacter ℂ (geometricConductor E)) χ)
      (coeffE E) (fun n ↦ f.frickeSign hf.χ_eq_one * coeffE E n) := by
  refine Miyake.twisted_completedL_cuspForm (by norm_num) (geometricConductor_pos E) 1 χ hχ hm
    (coeffGrowth_coeffE E) ((coeffGrowth_coeffE E).const_mul _) hf.isCuspFormChar fun z hz ↦ ?_
  have := hf.fricke_eq z hz
  rw [Miyake.qSeries_const_mul]
  exact_mod_cast this

/-- **Row 22**: a curve with a newform of level its geometric conductor satisfies the strong Hasse–Weil conjecture
with the uniform sign $w_E$, its root number. -/
theorem HasNewform.strongHasseWeilUniform (hf : HasNewform E (geometricConductor E) f) :
    StrongHasseWeilUniform E (rootNumber f hf.χ_eq_one) := by
  refine ⟨rootNumber_eq_one_or_neg_one f hf.χ_eq_one, fun m _ hm χ hχ ↦ ?_⟩
  obtain ⟨Φ, hΦd, hΦb, σ₀, h1, h2⟩ := twistedHecke hf hm χ hχ
  obtain ⟨Φ', hΦ'd, hΦ'b, σ₁, h1', -⟩ := twistedHecke hf hm χ⁻¹ (Miyake.isPrimitive_inv_aux hχ)
  refine ⟨Φ, Φ', isBoundedEntire_of E χ hΦd hΦb h1, isBoundedEntire_of E χ⁻¹ hΦ'd hΦ'b h1', ?_⟩
  set ε := f.frickeSign hf.χ_eq_one with hε
  set C := Miyake.weilConstant (1 : DirichletCharacter ℂ (geometricConductor E)) χ with hCdef
  have hC : C = χ (-1) * χ (geometricConductor E : ZMod m) *
      (gaussSum χ ZMod.stdAddChar / gaussSum χ⁻¹ ZMod.stdAddChar) :=
    weilConstant_one_eq E hm χ
  set c : ℝ := 2 - max σ₀ σ₁ with hc
  have hopen : ∀ s : ℂ, s.re < c → Φ s = (-ε * C) * Φ' (2 - s) := by
    intro s hs
    have hs1 : σ₀ < 2 - s.re := by have := le_max_left σ₀ σ₁; rw [hc] at hs; linarith
    have hs2 : σ₁ < 2 - s.re := by have := le_max_right σ₀ σ₁; rw [hc] at hs; linarith
    have e := h2 s (by simpa using hs1)
    have e' := h1' (2 - s) (by simpa using hs2)
    simp only [Nat.cast_ofNat] at e
    rw [e, twistedCompletedL_const_mul, ← e', Complex.I_sq]
    ring
  have hA : AnalyticOnNhd ℂ Φ Set.univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hΦd
  have hB : AnalyticOnNhd ℂ (fun s ↦ (-ε * C) * Φ' (2 - s)) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      ((hΦ'd.comp ((differentiable_const _).sub differentiable_id)).const_mul _)
  have hev : Φ =ᶠ[nhds ((c - 1 : ℝ) : ℂ)] fun s ↦ (-ε * C) * Φ' (2 - s) := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨{z : ℂ | z.re < c}, (isOpen_lt Complex.continuous_re continuous_const).mem_nhds ?_, hopen⟩
    rw [Set.mem_ofPred_eq, Complex.ofReal_re]; linarith
  intro s
  have := hA.eqOn_of_preconnected_of_eventuallyEq hB isPreconnected_univ (Set.mem_univ _) hev
    (Set.mem_univ s)
  simp only at this
  rw [this, hC]
  unfold rootNumber
  ring

/-- **Row 22** (one half of Milne's Theorem 11.19, analytic form): a curve with a newform of level its geometric
conductor satisfies Milne's strong Hasse–Weil conjecture `StrongHasseWeil E`. -/
@[kb "milne2017mf" "Section 11, Thm. 11.19 (pdf p. 117), direction modular ⇒ strong Hasse-Weil, analytic form"]
theorem HasNewform.strongHasseWeil (hf : HasNewform E (geometricConductor E) f) : StrongHasseWeil E :=
  hf.strongHasseWeilUniform.strongHasseWeil

end ModularFormsKB.Elliptic
