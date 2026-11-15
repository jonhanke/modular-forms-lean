/-
# Shimura's theorem from Weil's converse theorem

This file reduces the named input `ShimuraTheorem` (`Abstract/Shimura.lean`) to three smaller
named inputs, following Shimura's original argument (Shimura 1973 `shimura1973` [unverified]):
1. `WeilConverse`: Weil's converse theorem with twists (Weil 1967 `weil1967`; Miyake 1989 `miyake1989`, Thm. 4.3.15),
   in its cusp-form form. **It is proved in Lean** in this library (`weil_cusp` together with `exists_weilSet`),
   but not in this file's import closure; here it is a named `Prop`.
2. `HeckeCoeffBound`: Hecke's bound $a(n) = O(n^{(2k+1)/4})$ for the coefficients of a cusp form of weight $k+\tfrac12$.
3. `ShimuraTwistedFE`: the analytic heart of Shimura's proof. For every primitive character $\psi$ of odd prime conductor
   prime to $4N$ (and for $\psi = 1$), the products $L(s-k+1,\psi\chi_t)\sum_m\psi(m)a(tm^2)m^{-s}$ satisfy the functional
   equations demanded by Weil's theorem in weight $2k$, level $4N$, character $\chi^2$, against the twists of one dual
   sequence $b$. Shimura obtains them from a Rankin-type integral of $f$ against $\theta_t$ and an Eisenstein series.

The Dirichlet series identity `LSeries_twist_shimuraCoeff_of_bound` (`ShimuraTwist.lean`, proved) turns the products into
the twisted Dirichlet series of the lift itself, and Hecke's bound supplies the growth and convergence conditions:
**`shimuraTheorem_of_weil`** proves `ShimuraTheorem M k N χ` for $N \ge 1$ from the three inputs. The hypothesis $k \ge 2$
is used exactly once: the series $\sum A_t(n)n^{-s}$ must converge absolutely at some $s < 2k$, and it does for
$\operatorname{Re}s > k+\tfrac32$.

**Fidelity of `WeilConverse` (record).** The headline of `weil_cusp` was copied from its published statement,
but its auxiliary definitions (`HeckeCondition`, `TwistedHeckeCondition`, `CoeffGrowth`, `qSeries`, `twist`,
`weilConstant`, `IsWeilSet`, `IsCuspFormChar`) could not be read when this file was written. They are
reconstructed below from Miyake §4.3, with the normalizations
$\Lambda_N(s) = (2\pi/\sqrt N)^{-s}\Gamma(s)L(s)$, $\Lambda_N(k-s;a) = C\Lambda_N(s;b)$ (Miyake Thms. 4.3.5, 4.3.6, $C = i^k$ for
$b$ the coefficients of $f|_kW_N$), and $C_\psi = \chi(m)\psi(-N)\tau(\psi)/\tau(\bar\psi)$ (Thm. 4.3.11). The Weil set is
specialized to the odd primes prime to $N$ (`exists_weilSet`). **To check:** that these agree with
`ModularFormsKB/Miyake/Sec4_3/*.lean`. (Checked later: `WeilConverse` is proved from
`Miyake.weil_cusp` as `weilConverse` in `ModularFormsKB/HalfIntegral/WeilBridge.lean`.)

**Index shift.** Matrix entries are 0-based: $c = \gamma_{1,0}$, $d = \gamma_{1,1}$.
-/
import ModularFormsKB.HalfIntegral.Abstract.Shimura
import ModularFormsKB.HalfIntegral.ShimuraTwist
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup Asymptotics
open scoped Real
open scoped Manifold

local notation "ℍ" => UpperHalfPlane

/-- **Polynomial growth of a coefficient sequence:** $a(n) = O(n^\nu)$ for some real $\nu$. -/
def CoeffGrowth (a : ℕ → ℂ) : Prop :=
  ∃ ν : ℝ, a =O[Filter.atTop] fun n : ℕ ↦ (n : ℝ) ^ ν

/-- **The $q$-series** $\sum_{n \ge 0} a(n)e^{2\pi i n z}$ (a `tsum`, so $0$ where it does not converge). -/
noncomputable def qSeries (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, a n * cexp (2 * π * I * n * z)

/-- **Bounded on vertical strips:** bounded on every strip $\sigma_1 \le \operatorname{Re}s \le \sigma_2$. -/
def BddVStrips (E : ℂ → ℂ) : Prop :=
  ∀ σ₁ σ₂ : ℝ, ∃ B : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖E s‖ ≤ B

/-- **The gamma factor at level $N$:** $(2\pi/\sqrt N)^{-s}\,\Gamma(s)$ (Miyake 1989 `miyake1989`, §4.3). -/
noncomputable def gammaFactor (N : ℕ) (s : ℂ) : ℂ :=
  ((2 * π / Real.sqrt N : ℝ) : ℂ) ^ (-s) * Complex.Gamma s

/-- **Hecke's condition for given Dirichlet series** $L_a, L_b$ with constant terms $a_0, b_0$ (Miyake 1989
`miyake1989`, Thm. 4.3.5 (2) [unverified]): with $\Lambda_a = \gamma_N L_a$ and $\Lambda_b = \gamma_N L_b$, the functions
$E_a = \Lambda_a + a_0/s + Cb_0/(k-s)$ and $E_b = \Lambda_b + b_0/s + C^{-1}a_0/(k-s)$, given on a right half plane, extend to
entire functions bounded on vertical strips with $E_a(k-s) = C\,E_b(s)$, that is $\Lambda_a(k-s) = C\Lambda_b(s)$. Only the
values of $L_a, L_b$ on some right half plane enter (`HeckeConditionL.congr`). -/
def HeckeConditionL (k N : ℕ) (C : ℂ) (La Lb : ℂ → ℂ) (a0 b0 : ℂ) : Prop :=
  ∃ Ea Eb : ℂ → ℂ, Differentiable ℂ Ea ∧ Differentiable ℂ Eb ∧ BddVStrips Ea ∧ BddVStrips Eb ∧
    (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Ea s = gammaFactor N s * La s + a0 / s + C * b0 / (k - s) ∧
      Eb s = gammaFactor N s * Lb s + b0 / s + C⁻¹ * a0 / (k - s)) ∧
    ∀ s : ℂ, Ea (k - s) = C * Eb s

/-- **Hecke's condition** for coefficient sequences $a, b$: `HeckeConditionL` for their Dirichlet series. -/
def HeckeCondition (k N : ℕ) (C : ℂ) (a b : ℕ → ℂ) : Prop :=
  HeckeConditionL k N C (LSeries a) (LSeries b) (a 0) (b 0)

/-- **The twisted Hecke condition** (Miyake 1989 `miyake1989`, Lemma 4.3.9 [unverified]): Hecke's condition at level
$Nm^2$ for $\psi a$ and $\bar\psi b$ with constant $i^kC$, equivalently $(f_\psi)|_kW_{Nm^2} = C\,g_{\bar\psi}$. -/
def TwistedHeckeCondition (k N : ℕ) {m : ℕ} (ψ : DirichletCharacter ℂ m) (C : ℂ) (a b : ℕ → ℂ) : Prop :=
  HeckeCondition k (N * m ^ 2) (I ^ k * C) (twist ψ a) (twist ψ⁻¹ b)

/-- **The Gauss sum** $\tau(\psi) = \sum_{u=0}^{m-1}\psi(u)e^{2\pi iu/m}$. -/
noncomputable def gaussW {m : ℕ} (ψ : DirichletCharacter ℂ m) : ℂ :=
  ∑ u ∈ Finset.range m, ψ u * cexp (2 * π * I * u / m)

/-- **Weil's constant** $C_\psi = \chi(m)\psi(-N)\tau(\psi)/\tau(\bar\psi)$ (Miyake 1989 `miyake1989`, Thm. 4.3.11
[unverified]); equivalently $\chi(m)\psi(N)\tau(\psi)^2/m$ for primitive $\psi$. -/
noncomputable def weilConstant {N m : ℕ} (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ m) : ℂ :=
  χ m * ψ (-(N : ZMod m)) * gaussW ψ / gaussW ψ⁻¹

/-- **Weil's converse theorem, cusp-form part** (Weil 1967 `weil1967`; Miyake 1989 `miyake1989`, Thm. 4.3.15
[unverified]). Let $k, N \ge 1$, $\chi$ a character mod $N$ with $\chi(-1) = (-1)^k$, and $a, b$ of polynomial growth with
Hecke's condition (constant $i^k$) and the twisted conditions (constant $C_\psi$) for all primitive $\psi$ modulo the odd
primes prime to $N$. If $\sum a(n)n^{-s}$ converges absolutely at $s = k-\delta$ for some $\delta > 0$, then
$\sum a(n)q^n \in S_k(N,\chi)$ and $\sum b(n)q^n \in S_k(N,\bar\chi)$.

**Proved in this library** (`ModularFormsKB/Miyake/Sec4_3/WeilTheorem.lean`, theorem `weil_cusp`, with the Weil
set `exists_weilSet`), but not in this file's import closure. This structure mirrors `weil_cusp`; the auxiliary definitions are reconstructed (see the module docstring) and the cusp-form
predicate is `IsIntCuspForm`. -/
@[kb "miyake1989" "Thm. 4.3.15: Weil's converse theorem, cusp-form part; proved as weil_cusp [unverified]"]
structure WeilConverse : Prop where
  cusp : ∀ k N : ℕ, 0 < k → 0 < N → ∀ χ : DirichletCharacter ℂ N, χ (-1) = (-1) ^ k →
    ∀ a b : ℕ → ℂ, CoeffGrowth a → CoeffGrowth b → HeckeCondition k N (I ^ k) a b →
    (∀ m : ℕ, m.Prime → m ≠ 2 → m.Coprime N → ∀ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive →
      TwistedHeckeCondition k N ψ (weilConstant χ ψ) a b) →
    ∀ δ : ℝ, 0 < δ → LSeriesSummable a (((k : ℝ) - δ : ℝ) : ℂ) →
      IsIntCuspForm k N χ (fun τ : ℍ ↦ qSeries a τ) ∧ IsIntCuspForm k N χ⁻¹ (fun τ : ℍ ↦ qSeries b τ)

/-- **Hecke's bound in weight $k+\tfrac12$** (Iwaniec 1997 `iwaniec1997`, §5 [unverified]; Hecke's argument): the
coefficients of $f \in S_{k+1/2}(4N,\chi)$ satisfy $|a(n)| \le Cn^{(2k+1)/4}$ for $n \ge 1$. -/
@[kb "iwaniec1997" "§5: Hecke's bound a(n) = O(n^{w/2}) for cusp forms of weight w, here w = k + 1/2 [unverified]"]
structure HeckeCoeffBound (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop where
  bound : ∀ f ∈ M.cuspForms k N χ, ∀ a : ℕ → ℂ, Abstract.HasQExp f a →
    ∃ C : ℝ, ∀ n, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 4)

/-- **The functional equations of the twisted Dirichlet series of the lift** (Shimura 1973 `shimura1973`, proof of the
Main Theorem [unverified]). For $k \ge 2$, squarefree $t \ge 1$ and $f = \sum a(n)q^n \in S_{k+1/2}(4N,\chi)$ there is a
sequence $b$ of polynomial growth with $b(0) = 0$ such that
- $L(s-k+1,\chi_t)\sum_m a(tm^2)m^{-s}$ and $\sum b(n)n^{-s}$ satisfy Hecke's condition in weight $2k$, level $4N$,
  constant $i^{2k}$, constant terms $0$;
- for every odd prime $m \nmid 4N$ and primitive $\psi$ mod $m$, $L(s-k+1,\psi\chi_t)\sum_m\psi(m)a(tm^2)m^{-s}$ and
  $\sum\bar\psi(n)b(n)n^{-s}$ satisfy Hecke's condition at level $4Nm^2$ with constant $i^{2k}C_\psi$, $C_\psi$ Weil's
  constant for $\chi^2$.

Shimura derives these from the Rankin-type integral of $f$ against $\theta_t$ and an Eisenstein series of weight
$k-\tfrac12$; $b$ is the coefficient sequence of the image of the lift under the Fricke involution. -/
@[kb "shimura1973" "proof of the Main Theorem: functional equations of the twisted L-series of the t-th lift [unverified]"]
structure ShimuraTwistedFE (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop where
  fe : 2 ≤ k → ∀ t : ℕ, 1 ≤ t → Squarefree t → ∀ f ∈ M.cuspForms k N χ, ∀ a : ℕ → ℂ, Abstract.HasQExp f a →
    ∃ b : ℕ → ℂ, CoeffGrowth b ∧ b 0 = 0 ∧
      HeckeConditionL (2 * k) (4 * N) (I ^ (2 * k))
        (fun s ↦ LSeries (shimuraChar k N χ t) (s - (k - 1)) * LSeries (fun m ↦ a (t * m ^ 2)) s)
        (LSeries b) 0 0 ∧
      ∀ m : ℕ, m.Prime → m ≠ 2 → m.Coprime (4 * N) → ∀ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive →
        HeckeConditionL (2 * k) (4 * N * m ^ 2) (I ^ (2 * k) * weilConstant (χ ^ 2) ψ)
          (fun s ↦ LSeries (twist ψ (shimuraChar k N χ t)) (s - (k - 1)) *
            LSeries (twist ψ fun m ↦ a (t * m ^ 2)) s)
          (LSeries (twist ψ⁻¹ b)) 0 0

/-- **Hecke's condition depends only on a right half plane:** if $L_a = L_a'$ and $L_b = L_b'$ for $\operatorname{Re}s$
large, the conditions agree. -/
theorem HeckeConditionL.congr {k N : ℕ} {C : ℂ} {La La' Lb Lb' : ℂ → ℂ} {a0 b0 : ℂ}
    (ha : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → La s = La' s) (hb : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Lb s = Lb' s)
    (h : HeckeConditionL k N C La' Lb' a0 b0) : HeckeConditionL k N C La Lb a0 b0 := by
  obtain ⟨Ea, Eb, h1, h2, h3, h4, ⟨σ, hσ⟩, h5⟩ := h
  obtain ⟨σa, ha⟩ := ha
  obtain ⟨σb, hb⟩ := hb
  refine ⟨Ea, Eb, h1, h2, h3, h4, ⟨max σ (max σa σb), fun s hs ↦ ?_⟩, h5⟩
  have hs1 : σ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs2 : σa < s.re := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hs3 : σb < s.re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  rw [ha s hs2, hb s hs3]
  exact hσ s hs1

/-- The trivial character mod 1 does not twist. -/
theorem twist_one (a : ℕ → ℂ) : twist (1 : DirichletCharacter ℂ 1) a = a := by
  funext n
  simp only [twist]
  rw [MulChar.one_apply (isUnit_of_subsingleton _), one_mul]

/-- $\chi^2(-1) = 1 = (-1)^{2k}$. -/
theorem sq_apply_neg_one {L : ℕ} (χ : DirichletCharacter ℂ L) (k : ℕ) : (χ ^ 2) (-1) = (-1) ^ (2 * k) := by
  rw [MulChar.pow_apply' χ two_ne_zero, sq, ← map_mul, neg_one_mul, neg_neg, map_one, pow_mul]
  norm_num

/-- **The $t$-th lift as a coefficient sequence with constant term $0$.** -/
noncomputable def liftSeq (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ) (a : ℕ → ℂ) : ℕ → ℂ :=
  fun n ↦ if n = 0 then 0 else shimuraCoeff k N χ t a n

theorem liftSeq_zero (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ) (a : ℕ → ℂ) :
    liftSeq k N χ t a 0 = 0 := by simp [liftSeq]

theorem liftSeq_of_ne_zero (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ) (a : ℕ → ℂ) {n : ℕ}
    (hn : n ≠ 0) : liftSeq k N χ t a n = shimuraCoeff k N χ t a n := by simp [liftSeq, hn]

/-- $n^{(2k+1)/4} \le n^k$ for $n, k \ge 1$. -/
theorem rpow_le_pow_of_one_le {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (n : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 4) ≤ (n : ℝ) ^ k := by
  rw [← Real.rpow_natCast (n : ℝ) k]
  refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) ?_
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  push_cast
  linarith

/-- **Polynomial bound for the lift from Hecke's bound:** $|A_t(n)| \le C' n^{3k+1}$ for all $n$. -/
theorem liftSeq_bound (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {t : ℕ} (ht : 1 ≤ t) (hk : 1 ≤ k)
    {a : ℕ → ℂ} {C : ℝ} (ha : ∀ n, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 4)) :
    ∃ C' : ℝ, ∀ n, ‖liftSeq k N χ t a n‖ ≤ C' * (n : ℝ) ^ (3 * k + 1) := by
  have hC : 0 ≤ C := by
    have h := le_trans (norm_nonneg _) (ha 1 le_rfl)
    simpa using h
  have ha' : ∀ n, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ k := fun n hn ↦
    le_trans (ha n hn) (mul_le_mul_of_nonneg_left (rpow_le_pow_of_one_le hk hn) hC)
  refine ⟨C * (t : ℝ) ^ k, fun n ↦ ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [liftSeq_zero, norm_zero]
    positivity
  · rw [liftSeq_of_ne_zero k N χ t a hn.ne']
    exact norm_shimuraCoeff_le k N χ ht ha' hn

/-- A sequence bounded by $C'n^{j}$ has polynomial growth. -/
theorem coeffGrowth_of_bound {c : ℕ → ℂ} {C : ℝ} {j : ℕ} (h : ∀ n, ‖c n‖ ≤ C * (n : ℝ) ^ j) :
    CoeffGrowth c := by
  refine ⟨j, IsBigO.of_bound C (Filter.Eventually.of_forall fun n ↦ ?_)⟩
  rw [Real.rpow_natCast, Real.norm_of_nonneg (by positivity)]
  exact h n

/-- **A polynomially bounded $q$-series converges on $\mathbb H$:** if $|c(n)| \le C'n^j$ then
$\sum c(n)e^{2\pi in\tau}$ has sum `qSeries c τ`. -/
theorem hasSum_qSeries_of_bound {c : ℕ → ℂ} {C : ℝ} {j : ℕ} (h : ∀ n, ‖c n‖ ≤ C * (n : ℝ) ^ j) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ c n * cexp (2 * π * I * n * τ)) (qSeries c τ) := by
  refine Summable.hasSum ?_
  set r : ℂ := cexp (2 * π * I * τ) with hr
  have hr1 : ‖r‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
  have hsum : Summable fun n : ℕ ↦ C * ((n : ℝ) ^ j * ‖r‖ ^ n) := by
    refine Summable.mul_left C ?_
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) j (r := ‖r‖) (by simpa using hr1)
    exact this
  refine Summable.of_norm_bounded hsum fun n ↦ ?_
  have he : cexp (2 * π * I * n * τ) = r ^ n := by
    rw [hr, ← Complex.exp_nat_mul]
    ring_nf
  rw [he, norm_mul, norm_pow, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (h n) (by positivity)

/-- **Shimura's theorem from Weil's converse theorem** (Shimura 1973 `shimura1973`, Main Theorem, via Weil 1967
`weil1967` [unverified]): for $N \ge 1$, `ShimuraTheorem M k N χ` follows from `WeilConverse`, Hecke's bound
`HeckeCoeffBound M k N χ` and the functional equations `ShimuraTwistedFE M k N χ`. The lift is
$F = \sum_{n\ge1}A_t(n)q^n$; the twisted Dirichlet series identity (`LSeries_twist_shimuraCoeff_of_bound`) converts the
functional equations of the products into Weil's hypotheses for $A_t$. -/
@[kb "shimura1973" "Main Theorem, reduced to Weil's converse theorem, Hecke's bound and the twisted functional equations [unverified]"]
theorem shimuraTheorem_of_weil (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (hN : 0 < N)
    (hW : WeilConverse) (hB : HeckeCoeffBound M k N χ) (hFE : ShimuraTwistedFE M k N χ) :
    ShimuraTheorem M k N χ := by
  refine ⟨fun hk t ht hsq f hf a ha ↦ ?_⟩
  obtain ⟨C, hC⟩ := hB.bound f hf a ha
  obtain ⟨b, hb, hb0, h1, h2⟩ := hFE.fe hk t ht hsq f hf a ha
  obtain ⟨C', hC'⟩ := liftSeq_bound k N χ ht (by omega) hC
  set A := liftSeq k N χ t a with hA
  have hAs : ∀ {m : ℕ} (ψ : DirichletCharacter ℂ m) (s : ℂ), (k : ℝ) + 3 / 2 < s.re →
      LSeries (twist ψ A) s =
        LSeries (twist ψ (shimuraChar k N χ t)) (s - (k - 1)) * LSeries (twist ψ fun m ↦ a (t * m ^ 2)) s := by
    intro m ψ s hs
    rw [← LSeries_twist_shimuraCoeff_of_bound k N χ ht hC ψ hs]
    refine LSeries_congr (fun {n} hn ↦ ?_) s
    simp only [twist, hA, liftSeq_of_ne_zero k N χ t a hn]
  have hHecke : HeckeCondition (2 * k) (4 * N) (I ^ (2 * k)) A b := by
    unfold HeckeCondition
    rw [hA, liftSeq_zero, hb0]
    refine HeckeConditionL.congr ⟨(k : ℝ) + 3 / 2, fun s hs ↦ ?_⟩ ⟨0, fun s _ ↦ rfl⟩ h1
    have := hAs (1 : DirichletCharacter ℂ 1) s hs
    simpa only [twist_one] using this
  have hTw : ∀ m : ℕ, m.Prime → m ≠ 2 → m.Coprime (4 * N) → ∀ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive →
      TwistedHeckeCondition (2 * k) (4 * N) ψ (weilConstant (χ ^ 2) ψ) A b := by
    intro m hm hm2 hmN ψ hψ
    unfold TwistedHeckeCondition HeckeCondition
    have h0a : twist ψ A 0 = 0 := by simp [twist, hA, liftSeq_zero]
    have h0b : twist ψ⁻¹ b 0 = 0 := by simp [twist, hb0]
    rw [h0a, h0b]
    exact HeckeConditionL.congr ⟨(k : ℝ) + 3 / 2, fun s hs ↦ hAs ψ s hs⟩ ⟨0, fun s _ ↦ rfl⟩
      (h2 m hm hm2 hmN ψ hψ)
  have hSum : LSeriesSummable A ((((2 * k : ℕ) : ℝ) - 1 / 4 : ℝ) : ℂ) := by
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have h := LSeriesSummable_twist_shimuraCoeff k N χ ht hC (1 : DirichletCharacter ℂ 1)
      (s := ((((2 * k : ℕ) : ℝ) - 1 / 4 : ℝ) : ℂ)) (by rw [Complex.ofReal_re]; push_cast; linarith)
    rw [twist_one] at h
    exact (LSeriesSummable_congr _ (fun {n} hn ↦ liftSeq_of_ne_zero k N χ t a hn)).2 h
  have hW' := hW.cusp (2 * k) (4 * N) (by omega) (by omega) (χ ^ 2) (sq_apply_neg_one χ k) A b
    (coeffGrowth_of_bound hC') hb hHecke hTw (1 / 4) (by norm_num) hSum
  refine ⟨fun τ ↦ qSeries A τ, hW'.1, A, hasSum_qSeries_of_bound hC', fun n hn ↦ ?_⟩
  exact liftSeq_of_ne_zero k N χ t a (by omega)

end ModularFormsKB.HalfIntegral
