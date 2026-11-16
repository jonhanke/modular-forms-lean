/-
# The twisted $L$-function $L(F, D, s)$

Groundwork for `KohnenZagier` (Kohnen–Zagier 1981 `kohnenzagier1981`, Thm. 1).

For $F \in S_{2k}(\mathrm{SL}_2(\mathbb Z))$ with $q$-expansion coefficients $b$ and a discriminant $D$,
$$L(F, D, s) = \sum_{n \ge 1}\left(\frac Dn\right) b(n)\,n^{-s}$$
with the Kronecker symbol `kroneckerDisc` (`Abstract/Kohnen.lean`). The coefficients are `twistCoeff D b`.

Proved here:
- the Kronecker symbol takes values in $\{0, \pm1\}$ (`kroneckerDisc_trichotomy`), is multiplicative in $n \ge 1$
  (`kroneckerDisc_mul`), and $\left(\frac 1n\right) = 1$ (`kroneckerDisc_one_left`), so $L(F, 1, s) = L(F, s)$;
- **uniqueness of the entire continuation** (`IsEntireLSeries.unique`): two entire functions that agree with the
  Dirichlet series on a right half-plane are equal (identity theorem), so the `L` in `KohnenZagier` is determined by $F$
  and $D$;
- **absolute convergence:** the $q$-expansion coefficients of $F \in S_{2k}(\mathrm{SL}_2(\mathbb Z))$ given through
  `Abstract.HasQExp` are Mathlib's `qExpansion` coefficients (`hasQExp_coeff_eq_qExpansion`), hence $O(n^k)$ by Hecke's
  bound (`cuspForm_coeff_isBigO`); so $L(F, D, s)$ converges absolutely for $\operatorname{Re}s > k + 1$
  (`LSeriesSummable_twist`) and is holomorphic there (`twistL_differentiableOn`), the half-plane of the `KohnenZagier`
  statement.

The existence of the entire continuation (Hecke) is the named input `TwistContinuation`.
-/
import ModularFormsKB.HalfIntegral.Abstract.Kohnen
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Convergence

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup ModularForm Filter Asymptotics
open scoped Real
open scoped Manifold

local notation "ℍ" => UpperHalfPlane

/-- The coefficients $\left(\frac Dn\right) b(n)$ of $L(F, D, s)$. -/
noncomputable def twistCoeff (D : ℤ) (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  (kroneckerDisc D n : ℂ) * b n

/-- **The twisted Dirichlet series** $L(F, D, s) = \sum_{n\ge1}\left(\frac Dn\right) b(n) n^{-s}$ (Mathlib's `LSeries`, which
ignores $n = 0$ and is $0$ where the series does not converge). -/
noncomputable def twistL (D : ℤ) (b : ℕ → ℂ) (s : ℂ) : ℂ :=
  LSeries (twistCoeff D b) s

theorem kroneckerTwo_trichotomy (D : ℤ) : kroneckerTwo D = 0 ∨ kroneckerTwo D = 1 ∨ kroneckerTwo D = -1 := by
  unfold kroneckerTwo
  split_ifs <;> simp

private theorem trichotomy_mul {x y : ℤ} (hx : x = 0 ∨ x = 1 ∨ x = -1) (hy : y = 0 ∨ y = 1 ∨ y = -1) :
    x * y = 0 ∨ x * y = 1 ∨ x * y = -1 := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp

private theorem trichotomy_pow {x : ℤ} (hx : x = 0 ∨ x = 1 ∨ x = -1) (e : ℕ) :
    x ^ e = 0 ∨ x ^ e = 1 ∨ x ^ e = -1 := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ]; exact trichotomy_mul ih hx

/-- **The Kronecker symbol takes values in $\{0, 1, -1\}$.** -/
theorem kroneckerDisc_trichotomy (D : ℤ) (n : ℕ) :
    kroneckerDisc D n = 0 ∨ kroneckerDisc D n = 1 ∨ kroneckerDisc D n = -1 :=
  trichotomy_mul (trichotomy_pow (kroneckerTwo_trichotomy D) _) (jacobiSym.trichotomy D _)

theorem abs_kroneckerDisc_le_one (D : ℤ) (n : ℕ) : |kroneckerDisc D n| ≤ 1 := by
  rcases kroneckerDisc_trichotomy D n with h | h | h <;> simp [h]

theorem norm_kroneckerDisc_le_one (D : ℤ) (n : ℕ) : ‖(kroneckerDisc D n : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast abs_kroneckerDisc_le_one D n

/-- **Multiplicativity:** $\left(\frac D{mn}\right) = \left(\frac Dm\right)\left(\frac Dn\right)$ for $m, n \ge 1$. -/
theorem kroneckerDisc_mul (D : ℤ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    kroneckerDisc D (m * n) = kroneckerDisc D m * kroneckerDisc D n := by
  unfold kroneckerDisc
  have h := Nat.ordCompl_mul m n 2
  have : NeZero (m / 2 ^ m.factorization 2) := ⟨(Nat.ordCompl_pos 2 hm).ne'⟩
  have : NeZero (n / 2 ^ n.factorization 2) := ⟨(Nat.ordCompl_pos 2 hn).ne'⟩
  rw [Nat.factorization_mul hm hn, Finsupp.add_apply] at h
  rw [Nat.factorization_mul hm hn, Finsupp.add_apply, pow_add, h, jacobiSym.mul_right]
  ring

@[simp] theorem kroneckerDisc_one_right (D : ℤ) : kroneckerDisc D 1 = 1 := by
  simp [kroneckerDisc]

/-- $\left(\frac 1n\right) = 1$: the twist by $D = 1$ is the untwisted series. -/
@[simp] theorem kroneckerDisc_one_left (n : ℕ) : kroneckerDisc 1 n = 1 := by
  simp [kroneckerDisc, kroneckerTwo]

theorem twistL_one (b : ℕ → ℂ) (s : ℂ) : twistL 1 b s = LSeries b s := by
  exact LSeries_congr (fun {n} _ ↦ by simp [twistCoeff]) s

theorem norm_twistCoeff_le (D : ℤ) (b : ℕ → ℂ) (n : ℕ) : ‖twistCoeff D b n‖ ≤ ‖b n‖ := by
  rw [twistCoeff, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_kroneckerDisc_le_one D n)

/-- **Uniqueness of the entire continuation:** two entire functions agreeing with $\sum b(n)n^{-s}$ for
$\operatorname{Re}s > \sigma_0$ are equal. -/
theorem IsEntireLSeries.unique {b : ℕ → ℂ} {σ₀ : ℝ} {L₁ L₂ : ℂ → ℂ} (h₁ : IsEntireLSeries b σ₀ L₁)
    (h₂ : IsEntireLSeries b σ₀ L₂) : L₁ = L₂ := by
  have ha₁ : AnalyticOnNhd ℂ L₁ Set.univ := fun z _ ↦ h₁.1.analyticAt z
  have ha₂ : AnalyticOnNhd ℂ L₂ Set.univ := fun z _ ↦ h₂.1.analyticAt z
  refine ha₁.eq_of_eventuallyEq ha₂ (z₀ := ((σ₀ + 1 : ℝ) : ℂ)) ?_
  have hopen : IsOpen {s : ℂ | σ₀ < s.re} := isOpen_lt continuous_const continuous_re
  filter_upwards [hopen.mem_nhds (by simp : σ₀ < (((σ₀ + 1 : ℝ) : ℂ)).re)] with s hs
  rw [h₁.2 s hs, h₂.2 s hs]

/-- **Absolute convergence from a coefficient bound:** if $b(n) = O(n^\alpha)$ then $L(F, D, s)$ converges absolutely for
$\operatorname{Re}s > \alpha + 1$. -/
theorem LSeriesSummable_twist_of_isBigO (D : ℤ) {b : ℕ → ℂ} {α : ℝ} (hb : b =O[atTop] fun n ↦ (n : ℝ) ^ α)
    {s : ℂ} (hs : α + 1 < s.re) : LSeriesSummable (twistCoeff D b) s := by
  refine LSeriesSummable_of_isBigO_rpow (x := α + 1) hs ?_
  have h1 : twistCoeff D b =O[atTop] b :=
    IsBigO.of_bound 1 (Eventually.of_forall fun n ↦ by simpa using norm_twistCoeff_le D b n)
  simpa using h1.trans hb

/-- **$q$-expansions are unique:** coefficients $b$ with $F(\tau) = \sum b(n)e^{2\pi i n\tau}$ are Mathlib's
`qExpansion` coefficients of $F \in S_w(\mathrm{SL}_2(\mathbb Z))$. -/
theorem hasQExp_coeff_eq_qExpansion {w : ℤ} (F : CuspForm 𝒮ℒ w) {b : ℕ → ℂ} (hF : Abstract.HasQExp F b)
    (n : ℕ) : b n = (UpperHalfPlane.qExpansion 1 F).coeff n := by
  refine ModularFormClass.qExpansion_coeff_unique (Γ := 𝒮ℒ) (k := w) one_pos ?_ (fun τ ↦ ?_) n
  · have := Subgroup.strictWidthInfty_mem_strictPeriods (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))
    rwa [Subgroup.strictWidthInfty_SL2Z] at this
  · convert hF τ using 2 with m
    rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring

/-- **Hecke's bound** for coefficients given through `Abstract.HasQExp`: $b(n) = O(n^k)$ for $F \in S_{2k}$. -/
theorem cuspForm_coeff_isBigO (k : ℕ) (F : CuspForm 𝒮ℒ (2 * k : ℕ)) {b : ℕ → ℂ} (hF : Abstract.HasQExp F b) :
    b =O[atTop] fun n ↦ (n : ℝ) ^ (k : ℝ) := by
  have h := CuspFormClass.qExpansion_isBigO (Γ := 𝒮ℒ) (k := ((2 * k : ℕ) : ℤ)) F
  rw [Subgroup.strictWidthInfty_SL2Z] at h
  have hb : b = fun n ↦ (UpperHalfPlane.qExpansion 1 F).coeff n := funext (hasQExp_coeff_eq_qExpansion F hF)
  rw [hb]
  convert h using 3 with n
  push_cast
  ring

/-- **$L(F, D, s)$ converges absolutely for $\operatorname{Re}s > k + 1$.** -/
theorem LSeriesSummable_twist (k : ℕ) (F : CuspForm 𝒮ℒ (2 * k : ℕ)) {b : ℕ → ℂ} (hF : Abstract.HasQExp F b)
    (D : ℤ) {s : ℂ} (hs : (k : ℝ) + 1 < s.re) : LSeriesSummable (twistCoeff D b) s :=
  LSeriesSummable_twist_of_isBigO D (cuspForm_coeff_isBigO k F hF) hs

/-- **$L(F, D, s)$ is holomorphic for $\operatorname{Re}s > k + 1$.** -/
theorem twistL_differentiableOn (k : ℕ) (F : CuspForm 𝒮ℒ (2 * k : ℕ)) {b : ℕ → ℂ} (hF : Abstract.HasQExp F b)
    (D : ℤ) : DifferentiableOn ℂ (twistL D b) {s : ℂ | (k : ℝ) + 1 < s.re} := by
  refine (LSeries_differentiableOn (twistCoeff D b)).mono fun s hs ↦ ?_
  have hle : LSeries.abscissaOfAbsConv (twistCoeff D b) ≤ ((k : ℝ) + 1 : ℝ) := by
    refine LSeries.abscissaOfAbsConv_le_of_isBigO_rpow (x := (k : ℝ)) ?_
    have h1 : twistCoeff D b =O[atTop] b :=
      IsBigO.of_bound 1 (Eventually.of_forall fun n ↦ by simpa using norm_twistCoeff_le D b n)
    simpa using h1.trans (cuspForm_coeff_isBigO k F hF)
  exact lt_of_le_of_lt hle (by exact_mod_cast hs)

/-- **Hecke's continuation of the twisted $L$-series** (Hecke 1936 `hecke1936`; Shimura 1971 [unverified]): for
$F \in S_{2k}(\mathrm{SL}_2(\mathbb Z))$ and a fundamental discriminant $D$, the series $L(F, D, s)$ has an entire
continuation (`F|χ_D` is a cusp form of level $D^2$). -/
@[kb "hecke1936" "the twist of a level one cusp form by a quadratic character has an entire L-function [unverified]"]
structure TwistContinuation (k : ℕ) : Prop where
  exists_entire : ∀ (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ), Abstract.HasQExp F b →
    ∀ D : ℤ, IsFundamentalDiscriminant D → ∃ L : ℂ → ℂ, IsEntireLSeries (twistCoeff D b) ((k : ℝ) + 1) L

/-- **The value $L(F, D, s)$** of the entire continuation, given `TwistContinuation`; by `IsEntireLSeries.unique` it does not
depend on the choice. -/
noncomputable def twistLEntire {k : ℕ} (h : TwistContinuation k) (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ)
    (hF : Abstract.HasQExp F b) (D : ℤ) (hD : IsFundamentalDiscriminant D) : ℂ → ℂ :=
  (h.exists_entire F b hF D hD).choose

theorem twistLEntire_spec {k : ℕ} (h : TwistContinuation k) (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ)
    (hF : Abstract.HasQExp F b) (D : ℤ) (hD : IsFundamentalDiscriminant D) :
    IsEntireLSeries (twistCoeff D b) ((k : ℝ) + 1) (twistLEntire h F b hF D hD) :=
  (h.exists_entire F b hF D hD).choose_spec

/-- The entire continuation agrees with the twisted Dirichlet series `twistL` where the latter converges absolutely. -/
theorem twistLEntire_eq_twistL {k : ℕ} (h : TwistContinuation k) (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ)
    (hF : Abstract.HasQExp F b) (D : ℤ) (hD : IsFundamentalDiscriminant D) {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    twistLEntire h F b hF D hD s = twistL D b s :=
  (twistLEntire_spec h F b hF D hD).2 s hs

end ModularFormsKB.HalfIntegral
