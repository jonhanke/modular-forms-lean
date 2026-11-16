/-
# Weight $\tfrac32$: the unary theta space, its orthogonal complement, and ternary representation numbers

For a positive definite integral ternary quadratic form $Q$ of level $4N$, $\theta_Q = \sum_n r_Q(n)q^n \in M_{3/2}(4N,\chi)$
decomposes as
$$\theta_Q = E_Q + u_Q + g_Q, \qquad E_Q = \theta_{\mathrm{gen}\,Q},\quad u_Q = \theta_{\mathrm{spn}\,Q} - \theta_{\mathrm{gen}\,Q}
\in U_{3/2}(4N,\chi),\quad g_Q = \theta_Q - \theta_{\mathrm{spn}\,Q} \in U_{3/2}^\perp,$$
(Siegel–Weil for $E_Q$; Schulze-Pillot 1984 `schulzepillot1984` for the last two [unverified]). $E_Q$ is in the Eisenstein
space, $u_Q$ is a combination of the unary theta series $\sum\psi(m)mq^{tm^2}$ (`unaryThetaSpace`, `SerreStark.lean`),
so it lives on finitely many square classes, and $g_Q$ is a cusp form orthogonal to them. The coefficients of
$g_Q$ are small (Duke 1988; Duke–Schulze-Pillot 1990 `dukeschulzepillot1990` [unverified]), those of $E_Q$ are large
on locally represented $n$ (Siegel's lower bound), and this controls $r_Q(n)$.

Quadratic forms are not in this library, so the statements here are about coefficient sequences; a companion
library on quadratic forms supplies $r_Q$, $E_Q$ and the decomposition.

**Proved.**
- `exists_orthogonal_decomposition` (linear algebra, no input): for a positive definite Hermitian form $P$ on a complex
  vector space $V$ and a finite-dimensional subspace $U$, every $f \in V$ is $u + g$ with $u \in U$ and $g \perp_P U$.
  With $V = S_{3/2}(4N,\chi)$, $P$ the Petersson product and $U = U_{3/2}(4N,\chi)$ (finite-dimensional,
  `finrank_unaryThetaSpace`) this is $S_{3/2} = U_{3/2} \oplus U_{3/2}^\perp$; `orthogonal_decomposition_unique` gives
  uniqueness. The Petersson product of general level is not constructed here, so $P$ is a parameter.
- `unaryThetaSpace_coeff_squarefree`: an element of $U_{3/2}(4N,\chi)$ has $a(n) = 0$ for squarefree $n > N$.
- `eventually_ne_zero_of_decomposition`: if $r = e + c$ with $c$ the coefficients of a cusp form of weight $\tfrac32$,
  Duke's bound `DukeCoeffBound` holds, and $\operatorname{Re} e(n) \ge \kappa n^{1/2-\delta}$ on a set $A$ of squarefree
  $n$ for some $\delta < 1/28$, then $r(n) \ne 0$ for all large $n \in A$: **every sufficiently large squarefree
  locally represented $n$ is represented by $Q$** (Duke 1988, with Siegel's bound; the squarefree case of
  Duke–Schulze-Pillot 1990 [unverified]). For squarefree $n$ the unary part does not intervene (previous item).
-/
import ModularFormsKB.HalfIntegral.SerreStark
import ModularFormsKB.HalfIntegral.Abstract.CoeffBounds

namespace ModularFormsKB.HalfIntegral

open Complex

local notation "ℍ" => UpperHalfPlane

/-- A positive definite Hermitian form on a complex vector space: linear in the first variable, Hermitian, and
$\operatorname{Re}P(x,x) > 0$ for $x \neq 0$. -/
structure PosDefHermitian {V : Type*} [AddCommGroup V] [Module ℂ V] (P : V → V → ℂ) : Prop where
  add_left : ∀ x y z, P (x + y) z = P x z + P y z
  smul_left : ∀ (c : ℂ) x y, P (c • x) y = c * P x y
  conj_symm : ∀ x y, P y x = (starRingEnd ℂ) (P x y)
  pos : ∀ x, x ≠ 0 → 0 < (P x x).re

private theorem PosDefHermitian.sub_left {V : Type*} [AddCommGroup V] [Module ℂ V] {P : V → V → ℂ}
    (hP : PosDefHermitian P) (x y z : V) : P (x - y) z = P x z - P y z := by
  have : x - y = x + (-1 : ℂ) • y := by simp [sub_eq_add_neg]
  rw [this, hP.add_left, hP.smul_left]; ring

private theorem PosDefHermitian.smul_right {V : Type*} [AddCommGroup V] [Module ℂ V] {P : V → V → ℂ}
    (hP : PosDefHermitian P) (c : ℂ) (x y : V) : P x (c • y) = (starRingEnd ℂ) c * P x y := by
  rw [hP.conj_symm (c • y) x, hP.smul_left, map_mul, ← hP.conj_symm]

private theorem PosDefHermitian.add_right {V : Type*} [AddCommGroup V] [Module ℂ V] {P : V → V → ℂ}
    (hP : PosDefHermitian P) (x y z : V) : P x (y + z) = P x y + P x z := by
  rw [hP.conj_symm (y + z) x, hP.add_left, map_add, ← hP.conj_symm, ← hP.conj_symm]

private theorem PosDefHermitian.zero_right {V : Type*} [AddCommGroup V] [Module ℂ V] {P : V → V → ℂ}
    (hP : PosDefHermitian P) (x : V) : P x 0 = 0 := by
  have := hP.smul_right 0 x x
  simpa using this

private theorem exists_orthogonal_aux {V : Type*} [AddCommGroup V] [Module ℂ V] {P : V → V → ℂ}
    (hP : PosDefHermitian P) (s : Finset V) :
    ∀ f : V, ∃ u ∈ Submodule.span ℂ (s : Set V), ∀ v ∈ Submodule.span ℂ (s : Set V), P (f - u) v = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f
    refine ⟨0, Submodule.zero_mem _, fun v hv => ?_⟩
    simp only [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hv
    subst hv
    exact hP.zero_right _
  | insert w s hw ih =>
    intro f
    obtain ⟨u', hu', hu'o⟩ := ih f
    obtain ⟨u'', hu'', hu''o⟩ := ih w
    have hsub : Submodule.span ℂ (s : Set V) ≤ Submodule.span ℂ ((insert w s : Finset V) : Set V) :=
      Submodule.span_mono (Finset.coe_subset.2 (Finset.subset_insert _ _))
    have hwmem : w ∈ Submodule.span ℂ ((insert w s : Finset V) : Set V) :=
      Submodule.subset_span (by simp)
    by_cases hw0 : w - u'' = 0
    · refine ⟨u', hsub hu', ?_⟩
      intro v hv
      rw [Finset.coe_insert, Submodule.mem_span_insert] at hv
      obtain ⟨b, y, hy, hvdef⟩ := hv
      have hwu : w = u'' := sub_eq_zero.1 hw0
      apply hu'o
      rw [hvdef]
      exact add_mem (Submodule.smul_mem _ _ (hwu ▸ hu'')) hy
    · have hpos : P (w - u'') (w - u'') ≠ 0 := by
        intro h
        have := hP.pos _ hw0
        rw [h] at this
        simp at this
      refine ⟨u' + (P (f - u') (w - u'') / P (w - u'') (w - u'')) • (w - u''), ?_, ?_⟩
      · exact add_mem (hsub hu') (Submodule.smul_mem _ _ (sub_mem hwmem (hsub hu'')))
      · intro v hv
        rw [Finset.coe_insert, Submodule.mem_span_insert] at hv
        obtain ⟨b, y, hy, hvdef⟩ := hv
        have hv' : v = b • (w - u'') + (y + b • u'') := by
          rw [hvdef]; module
        have hy' : y + b • u'' ∈ Submodule.span ℂ (s : Set V) :=
          add_mem hy (Submodule.smul_mem _ _ hu'')
        have e1 : f - (u' + (P (f - u') (w - u'') / P (w - u'') (w - u'')) • (w - u'')) =
            (f - u') - (P (f - u') (w - u'') / P (w - u'') (w - u'')) • (w - u'') := by
          rw [sub_add_eq_sub_sub]
        have h1 := hu'o _ hy'
        have h2 := hu''o _ hy'
        rw [e1, hv']
        generalize w - u'' = w' at *
        generalize y + b • u'' = y' at *
        generalize f - u' = g at *
        simp only [hP.sub_left, hP.add_right, hP.smul_left, hP.smul_right, h1, h2]
        field_simp
        ring

/-- **Orthogonal decomposition along a finite-dimensional subspace:** every $f$ is $u + g$ with $u \in U$ and
$P(g, v) = 0$ for all $v \in U$. -/
theorem exists_orthogonal_decomposition {V : Type*} [AddCommGroup V] [Module ℂ V] {P : V → V → ℂ}
    (hP : PosDefHermitian P) (U : Submodule ℂ V) [FiniteDimensional ℂ U] (f : V) :
    ∃ u ∈ U, ∀ v ∈ U, P (f - u) v = 0 := by
  obtain ⟨S, hS⟩ := (Submodule.fg_iff_finiteDimensional U).2 ‹_›
  subst hS
  exact exists_orthogonal_aux hP S f

/-- **Uniqueness of the orthogonal decomposition.** -/
theorem orthogonal_decomposition_unique {V : Type*} [AddCommGroup V] [Module ℂ V] {P : V → V → ℂ}
    (hP : PosDefHermitian P) (U : Submodule ℂ V) {f u u' : V} (hu : u ∈ U) (hu' : u' ∈ U)
    (h : ∀ v ∈ U, P (f - u) v = 0) (h' : ∀ v ∈ U, P (f - u') v = 0) : u = u' := by
  have hd : u' - u ∈ U := sub_mem hu' hu
  have h0 : P (u' - u) (u' - u) = 0 := by
    have e : u' - u = (f - u) - (f - u') := by abel
    rw [e, hP.sub_left, ← e, h _ hd, h' _ hd]; simp
  by_contra hne
  have := hP.pos (u' - u) (sub_ne_zero.2 (Ne.symm hne))
  rw [h0] at this
  simp at this

/-- **The unary theta space has no squarefree coefficients beyond $N$:** for $g \in U_{3/2}(4N,\chi)$ with
$q$-expansion $a$ and $n > N$ squarefree, $a(n) = 0$ (an index $tm^2$ with $t \mid N$ and $n$ squarefree has $m = 1$). -/
theorem unaryThetaSpace_coeff_squarefree {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ (4 * N)} {g : ℍ → ℂ}
    (hg : g ∈ unaryThetaSpace N χ) {a : ℕ → ℂ} (ha : Abstract.HasQExp g a) {n : ℕ} (hn : N < n)
    (hsq : Squarefree n) : a n = 0 := by
  by_contra han
  obtain ⟨p, hp, m, hnm⟩ := unaryThetaSpace_coeff_support hg ha (by omega) han
  have hd : 4 * (p.1.conductor ^ 2 * p.2) ∣ 4 * N := by
    have := hp.2.2.1
    rwa [← mul_assoc]
  have hd2 : p.1.conductor ^ 2 * p.2 ∣ N := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hd
  have hdt : p.2 ∣ N := (Dvd.intro_left _ rfl).trans hd2
  have hle : p.2 ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdt
  have hm : IsUnit m := hsq m (by rw [hnm]; exact ⟨p.2, by ring⟩)
  have hm1 : m = 1 := Nat.isUnit_iff.1 hm
  rw [hm1] at hnm
  omega

/-- **Representation of large squarefree numbers from the decomposition** (Duke 1988 `duke1988` with Siegel's lower
bound; the squarefree case of Duke–Schulze-Pillot 1990 `dukeschulzepillot1990` [unverified]). Let $r = e + c$ where $c$
is the coefficient sequence of a cusp form $f \in S_{3/2}(4N,\chi)$ (for $r = r_Q$: $c$ is the coefficient sequence of
$\theta_Q - E_Q$, $e$ that of the genus Eisenstein series). Assume Duke's bound and, on a set $A$ of squarefree $n$,
Siegel's bound $\operatorname{Re}e(n) \ge \kappa n^{1/2-\delta}$ with $\kappa > 0$, $0 \le \delta < 1/28$. Then
$r(n) \ne 0$ for every sufficiently large $n \in A$. -/
theorem eventually_ne_zero_of_decomposition {M : MultiplierSystem} {N : ℕ} {χ : DirichletCharacter ℂ (4 * N)}
    (hDuke : DukeCoeffBound M 1 N χ) {f : ℍ → ℂ} (hf : f ∈ M.cuspForms 1 N χ) {c : ℕ → ℂ}
    (hc : Abstract.HasQExp f c) (e r : ℕ → ℂ) (hr : ∀ n, r n = e n + c n) (A : Set ℕ)
    (hA : ∀ n ∈ A, Squarefree n) {κ δ : ℝ} (hκ : 0 < κ) (hδ0 : 0 ≤ δ) (hδ : δ < 1 / 28)
    (he : ∀ n ∈ A, κ * (n : ℝ) ^ ((1 : ℝ) / 2 - δ) ≤ (e n).re) :
    ∃ n₀ : ℕ, ∀ n ∈ A, n₀ ≤ n → r n ≠ 0 := by
  set ε : ℝ := (1 / 28 - δ) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨C, hC⟩ := hDuke.bound rfl f hf c hc ε hε
  have hev : ∀ᶠ x : ℝ in Filter.atTop, |C| / κ < x ^ ε :=
    (tendsto_rpow_atTop hε).eventually_gt_atTop _
  have hev' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hev
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hev'
  refine ⟨n₀, fun n hnA hn => ?_⟩
  intro hr0
  have hsq := hA n hnA
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hsq.ne_zero
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have h1 := hC n hn1 hsq
  have h2 := he n hnA
  have hen : e n = - c n := by
    have := hr n
    rw [hr0] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have h3 : (e n).re ≤ ‖c n‖ := by
    rw [hen, Complex.neg_re]
    exact (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  have hE : ((1 : ℕ) : ℝ) / 2 - 1 / 28 + ε = ((1 : ℝ) / 2 - δ) - ε := by
    rw [hεdef]; push_cast; ring
  rw [hE] at h1
  have hsplit : (n : ℝ) ^ ((1 : ℝ) / 2 - δ) = (n : ℝ) ^ (((1 : ℝ) / 2 - δ) - ε) * (n : ℝ) ^ ε := by
    rw [← Real.rpow_add hnpos]; congr 1; ring
  have hpos : 0 < (n : ℝ) ^ (((1 : ℝ) / 2 - δ) - ε) := Real.rpow_pos_of_pos hnpos _
  have h4 := hn₀ n hn
  rw [div_lt_iff₀ hκ] at h4
  have h5 : κ * ((n : ℝ) ^ (((1 : ℝ) / 2 - δ) - ε) * (n : ℝ) ^ ε) ≤ |C| * (n : ℝ) ^ (((1 : ℝ) / 2 - δ) - ε) := by
    rw [← hsplit]
    calc _ ≤ _ := h2
      _ ≤ _ := h3
      _ ≤ C * _ := h1
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_abs_self C) hpos.le
  nlinarith [mul_lt_mul_of_pos_right h4 hpos]

end ModularFormsKB.HalfIntegral
