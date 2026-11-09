import ModularFormsKB.Milne.Ch9.Hecke
import ModularFormsKB.Miyake.Sec4_3.WeilTheorem

/-!
# Milne, Chapter 9: twisted Dirichlet series, Theorem 9.5 and Weil's theorem (Theorem 9.6)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 9, pdf pp. 103–104.

## Items

- (15) and the twisted series (D106): `milneLambda`, `milneTwistLambda`, `milneGauss`, `milneWeilConstant`;
  $L_\chi(s) = \sum a_n\chi(n)n^{-s}$ is `LSeries (Miyake.twist χ a)` and $f_\chi$ is `Miyake.qSeries (Miyake.twist χ a)`.
- **Theorem 9.5** (not in the audit's numbered list, row X003 of the chapter 9 table): `functional_equation_twist`
  (primitive $\chi$ modulo $m > 1$) and `functional_equation_untwisted` ($m = 1$).
- **Theorem 9.6** (Weil 1967): `weil_theorem`, with the corrected convergence hypothesis, and `weil_theorem_book`
  with Milne's literal hypothesis.

## Normalizations

Milne's weight is $2k$; Miyake's (and the repository's `Miyake.*` declarations) is $k_{\mathrm{Miyake}} = 2k$.
Milne's $\Lambda(s) = (2\pi)^{-s}\Gamma(s)L(s)$ and Miyake's $\Lambda_N(s) = (2\pi/\sqrt N)^{-s}\Gamma(s)L(s)$ differ by
$\Lambda_N(s) = N^{s/2}\Lambda(s)$; Milne's $\Lambda_\chi(s) = (m/2\pi)^s\Gamma(s)L_\chi(s)$ and Miyake's
$\Lambda_N(s; f, \chi)$ by the same factor. Milne's slash $f|_k\alpha = \det(\alpha)^k(cz+d)^{-2k}f(\alpha z)$ at
$W_N = \begin{pmatrix}0&-1\\N&0\end{pmatrix}$ is $N^k(Nz)^{-2k}f(-1/(Nz))$, which is Miyake's
`Miyake.fricke (2k) N f`. Milne's constant $C_\chi = C\,g(\chi)\chi(-N)/g(\bar\chi)$ is $C$ times Miyake's
`Miyake.weilConstant 1 χ` for the trivial character modulo $N$.

## Erratum (Theorem 9.6)

Milne asks that $L(s)$ converge absolutely at $s = k - \delta$. For weight $2k$ the right condition (Weil's and
Miyake's, with Miyake's weight $2k$) is absolute convergence at $s = 2k - \delta$. As printed the hypothesis holds only
for $f = 0$: for a nonzero form of weight $2k$, $\sum |a_n| n^{-\sigma}$ diverges for $\sigma \le k$
(`not_lseriesSummable_of_ne_zero`), and the printed hypotheses force $a = 0$ (`weil_theorem_book_coeff_eq_zero`), both
proved in `ModularFormsKB/Milne/Ch9/WeilPrinted.lean`. `weil_theorem` uses $2k - \delta$; `weil_theorem_book`
(Milne's hypothesis) follows from it.
-/

open Complex Filter Asymptotics CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Real Topology MatrixGroups ModularForm

noncomputable section

namespace ModularFormsKB.Milne

/-- Milne's (15): $\Lambda(s) = (2\pi)^{-s}\Gamma(s)L(s)$, $L(s) = \sum_{n\ge1}a_nn^{-s}$. -/
@[kb "milne2017mf" "Section 9, (15) (pdf p. 103)"]
def milneLambda (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  ((2 * π : ℝ) : ℂ) ^ (-s) * Gamma s * LSeries a s

/-- **Twisted completed series** (Milne, Section 9, pdf p. 103; D106): for a Dirichlet character $\chi$ modulo $m$,
$\Lambda_\chi(s) = (m/2\pi)^s\Gamma(s)L_\chi(s)$ with $L_\chi(s) = \sum_{n \ge 1} a_n\chi(n)n^{-s}$
(`LSeries (Miyake.twist χ a)`); the twisted function is $f_\chi(z) = \sum a_n\chi(n)e^{2\pi i n z}$
(`Miyake.qSeries (Miyake.twist χ a)`). -/
@[kb "milne2017mf" "Section 9, twisted series L_χ, Λ_χ, f_χ (pdf p. 103)"]
def milneTwistLambda {m : ℕ} (χ : DirichletCharacter ℂ m) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  ((m / (2 * π) : ℝ) : ℂ) ^ s * Gamma s * LSeries (Miyake.twist χ a) s

/-- **The Gauss sum** $g(\chi) = \sum_{n=1}^m \chi(n)e^{2\pi i n/m}$ (Milne, Section 9, pdf p. 103). -/
@[kb "milne2017mf" "Section 9, Gauss sum g(χ) (pdf p. 103)"]
def milneGauss {m : ℕ} (χ : DirichletCharacter ℂ m) : ℂ :=
  ∑ n ∈ Finset.Icc 1 m, χ n * cexp (2 * π * I * n / m)

/-- Milne's Gauss sum is the repository's `Miyake.gaussW` (Mathlib's `gaussSum χ ZMod.stdAddChar`). -/
theorem milneGauss_eq_gaussW {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) :
    milneGauss χ = Miyake.gaussW χ := by
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  set g : ℕ → ℂ := fun n ↦ χ (n : ZMod m) * cexp (2 * π * I * n / m) with hgdef
  have hg : ∀ n : ℕ, χ (n : ZMod m) * ZMod.stdAddChar (n : ZMod m) = g n := by
    intro n
    have := ZMod.stdAddChar_coe (N := m) (n : ℤ)
    simp only [Int.cast_natCast] at this
    rw [this]
  have hper : g m = g 0 := by
    simp only [hgdef, ZMod.natCast_self, Nat.cast_zero, mul_zero, zero_div, Complex.exp_zero]
    rw [show 2 * (π : ℂ) * I * m / m = 2 * π * I by field_simp, Complex.exp_two_pi_mul_I]
  have h1 : ∑ n ∈ Finset.Icc 1 m, g n = ∑ n ∈ Finset.range m, g n := by
    have e1 := Finset.sum_range_succ g m
    have e2 : ∑ n ∈ Finset.range (m + 1), g n = g 0 + ∑ n ∈ Finset.Icc 1 m, g n := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      congr 1
    rw [e1, hper] at e2
    linear_combination -e2
  have h2 : ∑ n ∈ Finset.range m, g n = ∑ x : ZMod m, χ x * ZMod.stdAddChar x := by
    refine Finset.sum_bij (fun n _ ↦ (n : ZMod m)) (fun _ _ ↦ Finset.mem_univ _) ?_ ?_ ?_
    · intro a ha b hb hab
      rw [Finset.mem_range] at ha hb
      rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hab
    · intro x _
      exact ⟨x.val, Finset.mem_range.2 (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
    · intro n _
      exact (hg n).symm
  unfold milneGauss Miyake.gaussW gaussSum
  exact h1.trans h2

/-- For $x > 0$ real, $x^z = \exp(z \log x)$. -/
lemma ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (z : ℂ) : (x : ℂ) ^ z = cexp (Real.log x * z) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← ofReal_log hx.le]

/-- Miyake's $\Lambda_N(s; f)$ is $N^{s/2}$ times Milne's $\Lambda(s)$. -/
lemma completedL_eq_milneLambda {N : ℕ} (hN : 0 < N) (a : ℕ → ℂ) (s : ℂ) :
    Miyake.completedL N a s = (N : ℂ) ^ (s / 2) * milneLambda a s := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < √(N : ℝ) := Real.sqrt_pos.2 hN'
  have h2pi : 0 < 2 * π := by positivity
  unfold Miyake.completedL milneLambda
  rw [show (N : ℂ) ^ (s / 2) = cexp (Real.log N * (s / 2)) from by
    rw [← ofReal_natCast, ofReal_cpow_eq_exp hN']]
  rw [ofReal_cpow_eq_exp (div_pos h2pi hs), ofReal_cpow_eq_exp h2pi,
    Real.log_div h2pi.ne' hs.ne', Real.log_sqrt hN'.le]
  have : cexp (((Real.log (2 * π) - Real.log N / 2 : ℝ) : ℂ) * -s) =
      cexp (Real.log N * (s / 2)) * cexp (Real.log (2 * π) * -s) := by
    rw [← exp_add]; congr 1; push_cast; ring
  rw [this]; ring

/-- Miyake's twisted $\Lambda_N(s; f, \chi)$ is $N^{s/2}$ times Milne's $\Lambda_\chi(s)$. -/
lemma twistedCompletedL_eq_milneTwistLambda {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    (χ : DirichletCharacter ℂ m) (a : ℕ → ℂ) (s : ℂ) :
    Miyake.twistedCompletedL N χ a s = (N : ℂ) ^ (s / 2) * milneTwistLambda χ a s := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < √(N : ℝ) := Real.sqrt_pos.2 hN'
  have h2pi : 0 < 2 * π := by positivity
  unfold Miyake.twistedCompletedL milneTwistLambda
  rw [show (N : ℂ) ^ (s / 2) = cexp (Real.log N * (s / 2)) from by
    rw [← ofReal_natCast, ofReal_cpow_eq_exp hN']]
  rw [ofReal_cpow_eq_exp (div_pos h2pi (mul_pos hm' hs)), ofReal_cpow_eq_exp (div_pos hm' h2pi),
    Real.log_div h2pi.ne' (mul_pos hm' hs).ne', Real.log_mul hm'.ne' hs.ne',
    Real.log_sqrt hN'.le, Real.log_div hm'.ne' h2pi.ne']
  have : cexp (((Real.log (2 * π) - (Real.log m + Real.log N / 2) : ℝ) : ℂ) * -s) =
      cexp (Real.log N * (s / 2)) * cexp (((Real.log m - Real.log (2 * π) : ℝ) : ℂ) * s) := by
    rw [← exp_add]; congr 1; push_cast; ring
  rw [this]; ring

/-- Milne's slash at $W_N$ is Miyake's Fricke transform in weight $2k$. -/
lemma milne_slash_eq_fricke {k N : ℕ} (hN : 0 < N) (a : ℕ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    (N : ℂ) ^ k * ((N : ℂ) * z) ^ (-(2 * k : ℤ)) * Miyake.qSeries a (-1 / (N * z)) =
      Miyake.fricke ((2 * k : ℕ) : ℤ) (N : ℝ) (Miyake.qSeries a) z := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∀ s : ℂ, s ≠ 0 → (s ^ 2) ^ k * (s ^ 2 * z) ^ (-(2 * k : ℤ)) = (s * z) ^ (-(2 * k : ℤ)) := by
    intro s hs
    rw [show (2 * k : ℤ) = ((2 * k : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_neg, zpow_natCast,
      zpow_natCast, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    field_simp
    ring
  have hsN : (N : ℂ) = ((√(N : ℝ) : ℝ) : ℂ) ^ 2 := by
    rw [← ofReal_pow, Real.sq_sqrt hN'.le]; simp
  have hs0 : ((√(N : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hN').ne'
  have h2 : (N : ℂ) ^ k * ((N : ℂ) * z) ^ (-(2 * k : ℤ)) =
      (((√(N : ℝ) : ℝ) : ℂ) * z) ^ (-(2 * k : ℤ)) := by
    conv_lhs => rw [hsN]
    exact key _ hs0
  unfold Miyake.fricke
  rw [h2]
  push_cast
  rfl

/-- **Milne's constant** $C_\chi = C\,g(\chi)\,\chi(-N)/g(\bar\chi)$ (Theorem 9.5), $\bar\chi = $ `χ⁻¹`. -/
@[kb "milne2017mf" "Section 9, Theorem 9.5, the constant C_χ (pdf p. 104)"]
def milneWeilConstant (C : ℂ) (N : ℕ) {m : ℕ} (χ : DirichletCharacter ℂ m) : ℂ :=
  C * milneGauss χ * χ (-(N : ZMod m)) / milneGauss χ⁻¹

/-- Identity theorem, left half-plane version. -/
lemma eq_of_eq_on_left_halfplane {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (σ : ℝ) (h : ∀ s : ℂ, s.re < σ → f s = g s) : f = g := by
  have := eq_of_eq_on_halfplane (f := fun s ↦ f (-s)) (g := fun s ↦ g (-s))
    (hf.comp differentiable_id.neg) (hg.comp differentiable_id.neg) (-σ)
    (fun s hs ↦ h (-s) (by simp; linarith))
  funext s
  simpa using congrFun this (-s)

/-- If an entire $\Phi$ satisfies the two half-plane formulas of a Hecke condition with $C^2 = 1$, then
$\Phi(K - s) = C\Phi(s)$. -/
lemma reflect_of_halfplanes {Φ P : ℂ → ℂ} (hd : Differentiable ℂ Φ) {K σ₀ : ℝ} {A C : ℂ}
    (hCC : C * C = 1)
    (hR : ∀ s : ℂ, σ₀ < s.re → Φ s = P s + A / s + C * A / (K - s))
    (hL : ∀ s : ℂ, σ₀ < K - s.re → Φ s = C * P (K - s) + A / s + C * A / (K - s)) :
    ∀ s, Φ (K - s) = C * Φ s := by
  have := eq_of_eq_on_halfplane (f := fun s ↦ Φ (K - s)) (g := fun s ↦ C * Φ s)
    (hd.comp ((differentiable_const _).sub differentiable_id)) ((differentiable_const _).mul hd) σ₀
    (fun s hs ↦ by
      have h1 := hL (K - s) (by simpa using hs)
      have h2 := hR s hs
      simp only [sub_sub_cancel] at h1
      rw [h1, h2]
      linear_combination (-A / (K - s)) * hCC)
  exact fun s ↦ congrFun this s

/-- A modular form for $\Gamma_0(N)$ with $q$-series $a$ gives `IsModularFormChar` for the trivial character. -/
lemma isModularFormChar_one_of_gamma0 {k : ℤ} {N : ℕ} (f : ModularForm (Gamma0 N) k) {a : ℕ → ℂ}
    (hfa : ∀ τ : ℍ, f τ = Miyake.qSeries a τ) :
    Miyake.IsModularFormChar k N 1 (fun τ : ℍ ↦ Miyake.qSeries a τ) := by
  have hfun : (fun τ : ℍ ↦ Miyake.qSeries a τ) = ⇑f := funext fun τ ↦ (hfa τ).symm
  refine ⟨⟨ModularForm.restrict (Subgroup.map_mono (Gamma1_in_Gamma0 N)) f, ?_⟩, ?_⟩
  · rw [hfun]; rfl
  · intro γ hγ
    rw [hfun, ModularForm.SL_slash, SlashInvariantForm.slash_action_eqn (Γ := (Gamma0 N : Subgroup (GL (Fin 2) ℝ))) f (γ : GL (Fin 2) ℝ) ⟨γ, hγ, rfl⟩]
    have h0 : ((γ 1 0 : ℤ) : ZMod N) = 0 := hγ
    have hdet := γ.det_coe
    rw [Matrix.det_fin_two] at hdet
    have had : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
      have := congrArg (fun r : ℤ ↦ (r : ZMod N)) hdet
      push_cast at this
      rw [h0, mul_zero, sub_zero] at this
      exact this
    rw [MulChar.one_apply (isUnit_iff_exists_inv.2 ⟨_, by rw [mul_comm]; exact had⟩), one_smul]

/-- The hypothesis `hW` of Theorem 9.5 says $f|W_N = $ `qSeries` of $C(-1)^k a$. -/
lemma fricke_eq_qSeries {k N : ℕ} (hN : 0 < N) {a : ℕ → ℂ} {C : ℂ}
    (hW : ∀ z : ℂ, 0 < z.im →
      (N : ℂ) ^ k * ((N : ℂ) * z) ^ (-(2 * k : ℤ)) * Miyake.qSeries a (-1 / (N * z)) =
        C * (-1) ^ k * Miyake.qSeries a z) :
    ∀ z : ℂ, 0 < z.im → Miyake.fricke ((2 * k : ℕ) : ℤ) (N : ℝ) (Miyake.qSeries a) z =
      Miyake.qSeries (fun n ↦ C * (-1) ^ k * a n) z := by
  intro z hz
  have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz
  rw [← milne_slash_eq_fricke hN a hz0, hW z hz, Miyake.qSeries_const_mul]

lemma I_pow_two_mul_mul (k : ℕ) (C : ℂ) : I ^ (2 * k) * (C * (-1) ^ k) = C := by
  rw [pow_mul, I_sq, mul_comm C, ← mul_assoc, ← mul_pow]
  simp

/-- **Milne, Theorem 9.5** (the case $m = 1$). Let $a_n = O(n^M)$ (Milne's standing hypothesis in Section 9) and
$f = \sum a_n e^{2\pi i n z}$ with $f|_kW_N = C(-1)^kf$, $C = \pm1$, $(f|_kW_N)(z) = N^k(Nz)^{-2k}f(-1/(Nz))$ (this
relation alone suffices; Milne assumes moreover that $f$ is a modular form for $\Gamma_0(N)$). Then $\Lambda(s)$
continues to a meromorphic function $\tilde\Lambda$, holomorphic except possibly at $s = 0, 2k$
($N^{s/2}\tilde\Lambda(s) + a_0/s + Ca_0/(2k - s)$ is entire), with $\tilde\Lambda(s) = CN^{k-s}\tilde\Lambda(2k-s)$ for
$s \ne 0, 2k$. -/
@[kb "milne2017mf" "Section 9, Theorem 9.5, case m = 1 (pdf p. 104)"]
theorem functional_equation_untwisted {k N : ℕ} (hk : 0 < k) (hN : 0 < N)
    {a : ℕ → ℂ} (ha : Miyake.CoeffGrowth a) {C : ℂ} (hC : C = 1 ∨ C = -1)
    (hW : ∀ z : ℂ, 0 < z.im →
      (N : ℂ) ^ k * ((N : ℂ) * z) ^ (-(2 * k : ℤ)) * Miyake.qSeries a (-1 / (N * z)) =
        C * (-1) ^ k * Miyake.qSeries a z) :
    ∃ Ψ : ℂ → ℂ, Differentiable ℂ Ψ ∧
      (∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
        Ψ s = (N : ℂ) ^ (s / 2) * milneLambda a s + a 0 / s + C * a 0 / (2 * k - s)) ∧
      ∀ s : ℂ, s ≠ 0 → s ≠ 2 * k →
        (N : ℂ) ^ (-s / 2) * (Ψ s - a 0 / s - C * a 0 / (2 * k - s)) =
          C * (N : ℂ) ^ ((k : ℂ) - s) * ((N : ℂ) ^ (-(2 * k - s) / 2) *
            (Ψ (2 * k - s) - a 0 / (2 * k - s) - C * a 0 / (2 * k - (2 * k - s)))) := by
  have hK : 0 < 2 * k := by omega
  have hCC : C * C = 1 := by rcases hC with rfl | rfl <;> norm_num
  have hb : Miyake.CoeffGrowth (fun n ↦ C * (-1) ^ k * a n) := ha.const_mul _
  obtain ⟨Φ, hd, -, σ₀, hR, hL⟩ :=
    (Miyake.hecke_fricke hK hN ha hb).1 (fun z hz ↦ (fricke_eq_qSeries hN hW z hz).symm)
  have hIc := I_pow_two_mul_mul k C
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hR' : ∀ s : ℂ, σ₀ < s.re →
      Φ s = Miyake.completedL N a s + a 0 / s + C * a 0 / ((2 * k : ℝ) - s) := by
    intro s hs
    have := hR s hs
    push_cast at this ⊢
    rw [this]
    linear_combination (a 0 / (2 * k - s)) * hIc
  have hL' : ∀ s : ℂ, σ₀ < (2 * k : ℝ) - s.re →
      Φ s = C * Miyake.completedL N a ((2 * k : ℝ) - s) + a 0 / s + C * a 0 / ((2 * k : ℝ) - s) := by
    intro s hs
    have := hL s (by push_cast at hs ⊢; exact hs)
    rw [Miyake.completedL_const_mul] at this
    push_cast at this ⊢
    rw [this]
    linear_combination (Miyake.completedL N a (2 * k - s) + a 0 / (2 * k - s)) * hIc
  have key := reflect_of_halfplanes hd hCC hR' hL'
  push_cast at key
  refine ⟨Φ, hd, ⟨σ₀, fun s hs ↦ ?_⟩, fun s _ _ ↦ ?_⟩
  · rw [hR' s hs, completedL_eq_milneLambda hN]; push_cast; ring
  · rw [key s, sub_sub_cancel]
    have hexp : (N : ℂ) ^ ((k : ℂ) - s) * (N : ℂ) ^ (-(2 * k - s) / 2) = (N : ℂ) ^ (-s / 2) := by
      rw [← cpow_add _ _ hN0]; congr 1; ring
    linear_combination (-(Φ s - a 0 / s - C * a 0 / (2 * k - s))) * hexp -
      ((N : ℂ) ^ ((k : ℂ) - s) * (N : ℂ) ^ (-(2 * k - s) / 2)) *
        ((Φ s - a 0 / s - C * a 0 / (2 * k - s)) + C * a 0 / (2 * k - s)) * hCC

lemma twistedCompletedL_const_mul (N : ℝ) {m : ℕ} (ψ : DirichletCharacter ℂ m) (c : ℂ) (a : ℕ → ℂ)
    (s : ℂ) :
    Miyake.twistedCompletedL N ψ (fun n ↦ c * a n) s = c * Miyake.twistedCompletedL N ψ a s := by
  have : Miyake.twist ψ (fun n ↦ c * a n) = c • Miyake.twist ψ a := by
    funext n; simp only [Miyake.twist, Pi.smul_apply, smul_eq_mul]; ring
  simp only [Miyake.twistedCompletedL, this, LSeries_smul]
  ring

lemma cpow_neg_half_mul (N : ℂ) (hN : N ≠ 0) (s : ℂ) : N ^ (-s / 2) * N ^ (s / 2) = 1 := by
  rw [← cpow_add _ _ hN, show -s / 2 + s / 2 = 0 by ring, cpow_zero]

lemma milneWeilConstant_eq {C : ℂ} {N m : ℕ} [NeZero m] (hmN : m.Coprime N)
    (χ : DirichletCharacter ℂ m) :
    milneWeilConstant C N χ = C * Miyake.weilConstant (1 : DirichletCharacter ℂ N) χ := by
  have h1 : (1 : DirichletCharacter ℂ N) (m : ZMod N) = 1 :=
    MulChar.one_apply ((ZMod.isUnit_iff_coprime m N).2 hmN)
  unfold milneWeilConstant Miyake.weilConstant
  rw [milneGauss_eq_gaussW χ, milneGauss_eq_gaussW χ⁻¹, h1]
  ring

/-- **Milne, Theorem 9.5** (twisted case). Let $f = \sum a_n e^{2\pi i n z}$ be a modular form of weight $2k$ for
$\Gamma_0(N)$, with $a_n = O(n^M)$ (Milne's standing hypothesis in Section 9; without it `hfa` would not determine
$a$, a divergent `tsum` being $0$), and $f|_kW_N = C(-1)^kf$, $C = \pm1$, where
$(f|_kW_N)(z) = N^k(Nz)^{-2k}f(-1/(Nz))$. For a primitive character $\chi$ modulo $m > 1$ with $\gcd(m, N) = 1$,
$\Lambda_\chi$ and $\Lambda_{\bar\chi}$ continue to entire functions satisfying
$\Lambda_\chi(s) = C_\chi N^{k-s}\Lambda_{\bar\chi}(2k - s)$. -/
@[kb "milne2017mf" "Section 9, Theorem 9.5 (pdf p. 104)"]
theorem functional_equation_twist {k N : ℕ} (hk : 0 < k) (hN : 0 < N)
    (f : ModularForm (Gamma0 N) (2 * k))
    {a : ℕ → ℂ} (ha : Miyake.CoeffGrowth a) (hfa : ∀ τ : ℍ, f τ = Miyake.qSeries a τ)
    {C : ℂ} (_hC : C = 1 ∨ C = -1)
    (hW : ∀ z : ℂ, 0 < z.im →
      (N : ℂ) ^ k * ((N : ℂ) * z) ^ (-(2 * k : ℤ)) * Miyake.qSeries a (-1 / (N * z)) =
        C * (-1) ^ k * Miyake.qSeries a z)
    {m : ℕ} (hm : 1 < m) (hmN : m.Coprime N) (χ : DirichletCharacter ℂ m) (hχ : χ.IsPrimitive) :
    ∃ Ψ Ψ' : ℂ → ℂ, Differentiable ℂ Ψ ∧ Differentiable ℂ Ψ' ∧
      (∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → Ψ s = milneTwistLambda χ a s ∧ Ψ' s = milneTwistLambda χ⁻¹ a s) ∧
      ∀ s : ℂ, Ψ s = milneWeilConstant C N χ * (N : ℂ) ^ ((k : ℂ) - s) * Ψ' (2 * k - s) := by
  have : NeZero m := ⟨by omega⟩
  have hK : 0 < 2 * k := by omega
  have hm0 : 0 < m := by omega
  have hb : Miyake.CoeffGrowth (fun n ↦ C * (-1) ^ k * a n) := ha.const_mul _
  have hf1 : Miyake.IsModularFormChar ((2 * k : ℕ) : ℤ) N 1 (fun τ : ℍ ↦ Miyake.qSeries a τ) := by
    have := isModularFormChar_one_of_gamma0 f hfa
    push_cast
    exact this
  have hg := fricke_eq_qSeries hN hW
  have step : ∀ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive →
      Miyake.TwistedHeckeCondition (2 * k) N ψ (Miyake.weilConstant (1 : DirichletCharacter ℂ N) ψ) a
        (fun n ↦ C * (-1) ^ k * a n) := fun ψ hψ ↦
    (Miyake.twisted_hecke hK hN hm ψ hψ ha hb _).1
      (Miyake.fricke_twist hK hN 1 ψ hψ hmN ha hb hf1 (fun z hz ↦ (hg z hz)))
  obtain ⟨Φ, hΦd, -, σ₁, hΦR, hΦL⟩ := step χ hχ
  obtain ⟨Φ', hΦ'd, -, σ₂, hΦ'R, -⟩ := step χ⁻¹ (Miyake.isPrimitive_inv_aux hχ)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hdN : ∀ g : ℂ → ℂ, Differentiable ℂ g → Differentiable ℂ (fun s ↦ (N : ℂ) ^ (-s / 2) * g s) :=
    fun g hg ↦ (((differentiable_id.neg.div_const 2).const_cpow (Or.inl hN0)).mul hg)
  have hIc := I_pow_two_mul_mul k C
  -- the functional equation for `Φ`
  have hFE : Φ = fun s ↦ C * Miyake.weilConstant (1 : DirichletCharacter ℂ N) χ * Φ' (2 * k - s) := by
    refine eq_of_eq_on_left_halfplane hΦd
      ((differentiable_const _).mul (hΦ'd.comp ((differentiable_const _).sub differentiable_id)))
      (((2 * k : ℕ) : ℝ) - max σ₁ σ₂) (fun s hs ↦ ?_)
    have h1 : σ₁ < ((2 * k : ℕ) : ℝ) - s.re := by
      have := le_max_left σ₁ σ₂; linarith
    have h2 : σ₂ < ((2 * k : ℕ) : ℝ) - s.re := by
      have := le_max_right σ₁ σ₂; linarith
    have e1 := hΦL s h1
    have e2 := hΦ'R (2 * k - s) (by simpa using h2)
    rw [twistedCompletedL_const_mul] at e1
    push_cast at e1
    rw [e1, e2]
    linear_combination (Miyake.weilConstant (1 : DirichletCharacter ℂ N) χ *
      Miyake.twistedCompletedL (N : ℝ) χ⁻¹ a (2 * k - s)) * hIc
  refine ⟨fun s ↦ (N : ℂ) ^ (-s / 2) * Φ s, fun s ↦ (N : ℂ) ^ (-s / 2) * Φ' s, hdN _ hΦd, hdN _ hΦ'd,
    ⟨max σ₁ σ₂, fun s hs ↦ ⟨?_, ?_⟩⟩, fun s ↦ ?_⟩
  · simp only
    rw [hΦR s (lt_of_le_of_lt (le_max_left _ _) hs),
      twistedCompletedL_eq_milneTwistLambda hN hm0, ← mul_assoc, cpow_neg_half_mul _ hN0, one_mul]
  · simp only
    rw [hΦ'R s (lt_of_le_of_lt (le_max_right _ _) hs),
      twistedCompletedL_eq_milneTwistLambda hN hm0, ← mul_assoc, cpow_neg_half_mul _ hN0, one_mul]
  · simp only
    have hexp : (N : ℂ) ^ ((k : ℂ) - s) * (N : ℂ) ^ (-(2 * k - s) / 2) = (N : ℂ) ^ (-s / 2) := by
      rw [← cpow_add _ _ hN0]; congr 1; ring
    rw [milneWeilConstant_eq hmN, congrFun hFE s, ← hexp]
    ring

lemma differentiable_mul_cpow {N : ℕ} (hN : 0 < N) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ (fun s ↦ (N : ℂ) ^ (s / 2) * g s) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  exact ((differentiable_id.div_const 2).const_cpow (Or.inl hN0)).mul hg

lemma boundedOnVerticalStrips_mul_cpow {N : ℕ} (hN : 0 < N) {Θ : ℂ → ℂ}
    (h : Miyake.BoundedOnVerticalStrips Θ) :
    Miyake.BoundedOnVerticalStrips (fun s ↦ (N : ℂ) ^ (s / 2) * Θ s) := by
  intro σ₁ σ₂
  obtain ⟨B, hB⟩ := h σ₁ σ₂
  refine ⟨(N : ℝ) ^ (σ₂ / 2) * |B|, fun s h1 h2 ↦ ?_⟩
  rw [norm_mul]
  have e : ‖(N : ℂ) ^ (s / 2)‖ = (N : ℝ) ^ (s.re / 2) := by
    rw [Complex.norm_natCast_cpow_of_pos hN]; simp
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have e2 : (N : ℝ) ^ (s.re / 2) ≤ (N : ℝ) ^ (σ₂ / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  rw [e]
  exact mul_le_mul e2 ((hB s h1 h2).trans (le_abs_self B)) (norm_nonneg _) (by positivity)

/-- A cusp form for $\Gamma_1(N)$ with the trivial-character $\Gamma_0(N)$ invariance is a cusp form for
$\Gamma_0(N)$. -/
lemma exists_cuspForm_gamma0 {K : ℤ} {N : ℕ} [NeZero N] {a : ℕ → ℂ}
    (h : Miyake.IsCuspFormChar K N 1 (fun τ : ℍ ↦ Miyake.qSeries a τ)) :
    ∃ F : CuspForm (Gamma0 N) K, ∀ τ : ℍ, F τ = Miyake.qSeries a τ := by
  obtain ⟨⟨F1, hF1⟩, hs⟩ := h
  refine ⟨{ toFun := fun τ : ℍ ↦ Miyake.qSeries a τ
            slash_action_eq' := ?_
            holo' := ?_
            zero_at_cusps' := ?_ }, fun τ ↦ rfl⟩
  · rintro _ ⟨g, hg, rfl⟩
    have h1 := hs g hg
    have hu : IsUnit ((g 1 1 : ℤ) : ZMod N) := by
      have h0 : ((g 1 0 : ℤ) : ZMod N) = 0 := hg
      have hdet := g.det_coe
      rw [Matrix.det_fin_two] at hdet
      have had : ((g 0 0 : ℤ) : ZMod N) * ((g 1 1 : ℤ) : ZMod N) = 1 := by
        have := congrArg (fun r : ℤ ↦ (r : ZMod N)) hdet
        push_cast at this
        rw [h0, mul_zero, sub_zero] at this
        exact this
      exact isUnit_iff_exists_inv.2 ⟨_, by rw [mul_comm]; exact had⟩
    rw [MulChar.one_apply hu, one_smul] at h1
    exact h1
  · have := ModularFormClass.holo F1
    rw [hF1] at this
    exact this
  · intro c hc
    have hc' : IsCusp c (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) :=
      (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).2
        ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).1 hc)
    have := CuspFormClass.zero_at_cusps F1 hc'
    rw [hF1] at this
    exact this

/-- **Milne, Theorem 9.6** (Weil 1967), with the convergence hypothesis at $s = 2k - \delta$ (see the module
docstring). Let $a_1, a_2, \dots$ have $a_n = O(n^M)$ (and $a_0 = 0$), $f(z) = \sum a_ne^{2\pi i n z}$, $k, N \ge 1$,
$C = \pm1$. Suppose $\Lambda(s)$ continues to an entire function bounded on vertical strips with
$\Lambda(s) = CN^{k-s}\Lambda(2k - s)$; that for all but finitely many primes $p \nmid N$ and every primitive character
$\chi$ modulo $p$, $\Lambda_\chi$ and $\Lambda_{\bar\chi}$ continue to entire functions bounded on vertical strips with
$\Lambda_\chi(s) = C_\chi N^{k-s}\Lambda_{\bar\chi}(2k - s)$; and that $L(s)$ converges absolutely at $s = 2k - \delta$
for some $\delta > 0$. Then $f$ is a cusp form of weight $2k$ for $\Gamma_0(N)$. -/
@[kb "milne2017mf" "Section 9, Theorem 9.6 (Weil) (pdf p. 104), corrected convergence point"]
theorem weil_theorem {k N : ℕ} (hk : 0 < k) (hN : 0 < N) {a : ℕ → ℂ} {M : ℝ}
    (ha : a =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ M) (ha0 : a 0 = 0) {C : ℂ} (_hC : C = 1 ∨ C = -1)
    (hΛ : ∃ Ψ : ℂ → ℂ, Differentiable ℂ Ψ ∧ BoundedOnVerticalStrips Ψ ∧
      (∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → Ψ s = milneLambda a s) ∧
      ∀ s : ℂ, Ψ s = C * (N : ℂ) ^ ((k : ℂ) - s) * Ψ (2 * k - s))
    (hχ : ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → ¬ p ∣ N → p ∉ S →
      ∀ χ : DirichletCharacter ℂ p, χ.IsPrimitive →
        ∃ Ψ Ψ' : ℂ → ℂ, Differentiable ℂ Ψ ∧ Differentiable ℂ Ψ' ∧
          BoundedOnVerticalStrips Ψ ∧ BoundedOnVerticalStrips Ψ' ∧
          (∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
            Ψ s = milneTwistLambda χ a s ∧ Ψ' s = milneTwistLambda χ⁻¹ a s) ∧
          ∀ s : ℂ, Ψ s = milneWeilConstant C N χ * (N : ℂ) ^ ((k : ℂ) - s) * Ψ' (2 * k - s))
    {δ : ℝ} (hδ : 0 < δ) (hL : LSeriesSummable a (2 * k - δ)) :
    ∃ F : CuspForm (Gamma0 N) (2 * k), ∀ τ : ℍ, F τ = Miyake.qSeries a τ := by
  have hK : 0 < 2 * k := by omega
  have : NeZero N := ⟨hN.ne'⟩
  have haG : Miyake.CoeffGrowth a := ⟨M, ha⟩
  have hb : Miyake.CoeffGrowth (fun n ↦ C * (-1) ^ k * a n) := haG.const_mul _
  obtain ⟨Ψ, hΨd, hΨb, ⟨σ₀, hΨR⟩, hΨFE⟩ := hΛ
  obtain ⟨S, hS⟩ := hχ
  have hΨb' := (boundedOnVerticalStrips_iff hΨd.continuous).1 hΨb
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hIc := I_pow_two_mul_mul k C
  have hexp : ∀ s : ℂ, (N : ℂ) ^ (s / 2) * (N : ℂ) ^ ((k : ℂ) - s) = (N : ℂ) ^ ((2 * k - s) / 2) := by
    intro s
    rw [← cpow_add _ _ hN0]; congr 1; ring
  -- condition (B) of Hecke's theorem for `a` and `b = C (-1)^k a`
  have h1 : Miyake.HeckeCondition ((2 * k : ℕ) : ℝ) (N : ℝ) (I ^ (2 * k)) a
      (fun n ↦ C * (-1) ^ k * a n) := by
    refine ⟨fun s ↦ (N : ℂ) ^ (s / 2) * Ψ s, differentiable_mul_cpow hN hΨd,
      boundedOnVerticalStrips_mul_cpow hN hΨb', σ₀, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
    · simp only [ha0, mul_zero, zero_div, add_zero]
      rw [hΨR s hs, completedL_eq_milneLambda hN]
    · have e1 := hΨFE s
      have e2 := hΨR (2 * k - s) (by simpa using hs)
      simp only [ha0, mul_zero, zero_div, add_zero]
      rw [Miyake.completedL_const_mul, completedL_eq_milneLambda hN]
      push_cast
      rw [← e2, e1]
      linear_combination (C * Ψ (2 * k - s)) * hexp s -
        ((N : ℂ) ^ ((2 * k - s) / 2) * Ψ (2 * k - s)) * hIc
  -- the twisted conditions `(B_ψ)` for the moduli in the Weil set
  have h2 : ∀ (m : ℕ) [NeZero m], m ∈ {p : ℕ | p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ N ∧ p ∉ S} →
      ∀ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive →
        Miyake.TwistedHeckeCondition (2 * k) N ψ
          (Miyake.weilConstant (1 : DirichletCharacter ℂ N) ψ) a (fun n ↦ C * (-1) ^ k * a n) := by
    intro m _ hm ψ hψ
    obtain ⟨hp, -, hnd, hnS⟩ := hm
    obtain ⟨Θ, Θ', hΘd, -, hΘb, -, ⟨σ₁, hσ₁⟩, hΘFE⟩ := hS m hp hnd hnS ψ hψ
    have hΘb' := (boundedOnVerticalStrips_iff hΘd.continuous).1 hΘb
    have hmN : m.Coprime N := (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
    have hm0 : 0 < m := hp.pos
    refine ⟨fun s ↦ (N : ℂ) ^ (s / 2) * Θ s, differentiable_mul_cpow hN hΘd,
      boundedOnVerticalStrips_mul_cpow hN hΘb', σ₁, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
    · beta_reduce
      rw [twistedCompletedL_eq_milneTwistLambda hN hm0, (hσ₁ s hs).1]
    · have e1 := hΘFE s
      have e2 := (hσ₁ (2 * k - s) (by simpa using hs)).2
      rw [twistedCompletedL_const_mul, twistedCompletedL_eq_milneTwistLambda hN hm0]
      push_cast
      rw [← e2, e1, milneWeilConstant_eq hmN]
      linear_combination (C * Miyake.weilConstant (1 : DirichletCharacter ℂ N) ψ * Θ' (2 * k - s)) *
          hexp s -
        (Miyake.weilConstant (1 : DirichletCharacter ℂ N) ψ * Θ' (2 * k - s) *
          (N : ℂ) ^ ((2 * k - s) / 2)) * hIc
  have hMW : Miyake.IsWeilSet N {p : ℕ | p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ N ∧ p ∉ S} := by
    refine ⟨fun m hm ↦ Or.inl ⟨hm.1, hm.2.1⟩,
      fun m hm ↦ (Nat.Prime.coprime_iff_not_dvd hm.1).2 hm.2.2.1, fun c d hc hd hcd ↦ ?_⟩
    have : NeZero d := ⟨hd.ne'⟩
    obtain ⟨p, hpgt, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod (q := d) (a := (c : ZMod d))
      ((ZMod.isUnit_iff_coprime c d).2 hcd) (max (max 2 N) (S.sup id))
    have hp2 : 2 < p := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hpgt
    have hpN : N < p := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hpgt
    have hpS : S.sup id < p := lt_of_le_of_lt (le_max_right _ _) hpgt
    refine ⟨p, ⟨hp, by omega, fun hdvd ↦ by have := Nat.le_of_dvd hN hdvd; omega,
      fun hmem ↦ by have := Finset.le_sup (f := id) hmem; simp only [id] at this; omega⟩, ?_⟩
    obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (c : ℤ) (p : ℤ) d).1
      (by push_cast; exact hpmod.symm)
    exact ⟨t, by linarith⟩
  have hχ1 : (1 : DirichletCharacter ℂ N) (-1) = (-1) ^ (2 * k) := by
    rw [MulChar.one_apply isUnit_one.neg, pow_mul]
    simp
  obtain ⟨hcf, -⟩ := Miyake.weil_cusp hK hN 1 hχ1 haG hb hMW h1 h2 hδ (by push_cast; exact hL)
  exact exists_cuspForm_gamma0 hcf

/-- **Milne, Theorem 9.6, as printed**: the hypotheses of `weil_theorem` with absolute convergence of $L(s)$ at
$s = k - \delta$ instead of $2k - \delta$ (a stronger hypothesis; see the module docstring). -/
@[kb "milne2017mf" "Section 9, Theorem 9.6 (Weil) (pdf p. 104), as printed"]
theorem weil_theorem_book {k N : ℕ} (hk : 0 < k) (hN : 0 < N) {a : ℕ → ℂ} {M : ℝ}
    (ha : a =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ M) (ha0 : a 0 = 0) {C : ℂ} (hC : C = 1 ∨ C = -1)
    (hΛ : ∃ Ψ : ℂ → ℂ, Differentiable ℂ Ψ ∧ BoundedOnVerticalStrips Ψ ∧
      (∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → Ψ s = milneLambda a s) ∧
      ∀ s : ℂ, Ψ s = C * (N : ℂ) ^ ((k : ℂ) - s) * Ψ (2 * k - s))
    (hχ : ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → ¬ p ∣ N → p ∉ S →
      ∀ χ : DirichletCharacter ℂ p, χ.IsPrimitive →
        ∃ Ψ Ψ' : ℂ → ℂ, Differentiable ℂ Ψ ∧ Differentiable ℂ Ψ' ∧
          BoundedOnVerticalStrips Ψ ∧ BoundedOnVerticalStrips Ψ' ∧
          (∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
            Ψ s = milneTwistLambda χ a s ∧ Ψ' s = milneTwistLambda χ⁻¹ a s) ∧
          ∀ s : ℂ, Ψ s = milneWeilConstant C N χ * (N : ℂ) ^ ((k : ℂ) - s) * Ψ' (2 * k - s))
    {δ : ℝ} (hδ : 0 < δ) (hL : LSeriesSummable a (k - δ)) :
    ∃ F : CuspForm (Gamma0 N) (2 * k), ∀ τ : ℍ, F τ = Miyake.qSeries a τ :=
  weil_theorem hk hN ha ha0 hC hΛ hχ hδ (hL.of_re_le_re (by simp; linarith [(Nat.cast_pos.2 hk : (0 : ℝ) < k)]))

end ModularFormsKB.Milne
