import ModularFormsKB.Miyake.HeckeTrick.PoissonS
import ModularFormsKB.Miyake.Wave2B.HeckeTrick
import ModularFormsKB.Miyake.HeckeTrick.TsumHolomorphic
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Miyake §7.2: continuation and Fourier expansion of $E_k(z,s;\chi,\psi)$ (Theorem 7.2.9)

Miyake, *Modular Forms*, §7.2, pp. 283–285. For Dirichlet characters $\chi$ mod $L$, $\psi$ mod $M$ with
$\chi(-1)\psi(-1) = (-1)^k$ and any integer $k$, the Eisenstein series with parameter $s$,
$E_k(z,s;\chi,\psi) = \sum'\chi(m)\psi(n)(mz+n)^{-k}|mz+n|^{-2s}$ (`eisensteinCharS`, (7.2.1), convergent for
$k + 2\operatorname{Re}s > 2$), equals
$$C(s) + D(s)y^{1-k-2s} + A(s)y^{-s}\sum_{n\ge1}a_n(s)n^{-s}e^{2\pi inz/M}\omega(4\pi yn/M;k+s,s)
 + B(s)y^{-k-s}\sum_{n\ge1}a_n(s)n^{-s-k}e^{-2\pi in\bar z/M}\omega(4\pi yn/M;s,k+s),$$
and the right-hand side (`eisensteinCharSCont`) is meromorphic in $s$ on $\mathbb C$, the two series being entire.

**Conventions.** $\chi_0$ in $C(s)$ is the principal character mod $1$ (`L = 1`), as in `eisensteinCharConst`;
"$\psi$ trivial" in $D(s)$ is the principal character mod $M$ (`ψ = 1`). $L_M(s,\psi)$ is Mathlib's
`DirichletCharacter.LFunction ψ` (the $L$-function of $\psi$ as a character mod $M$, continued), $W(\psi^0)$ the
Gauss sum of the primitive character attached to $\psi$, and $a_n(s)$ uses Miyake's divisor sum `gaussCoeff`
of (7.1.11). Where $\Gamma$ or an $L$-function has a pole, Lean's functions take junk values; the meromorphic
function is determined by its values off a discrete set.
-/

open MeasureTheory Set Filter Topology Complex
open scoped UpperHalfPlane
open scoped Real

noncomputable section

namespace ModularFormsKB.Miyake.HeckeTrick

open ModularFormsKB.Miyake.Wave2B

variable {L M : ℕ}

/-- **Miyake (7.2.6), Theorem 7.2.9.** $C(s) = 2L_M(2s+k,\psi)$ if $\chi = \chi_0$ ($L = 1$), $0$ otherwise. -/
@[kb "miyake1989" "(7.2.6) and Theorem 7.2.9, p. 284"]
def heckeC (k : ℤ) (L : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (s : ℂ) : ℂ :=
  if L = 1 then 2 * DirichletCharacter.LFunction ψ (2 * s + k) else 0

open scoped Classical in
/-- **Miyake, Theorem 7.2.9.** $D(s) = 2\sqrt\pi\,i^{-k}\prod_{p\mid M}(1-p^{-1})\,\Gamma(s)^{-1}\Gamma(s+k)^{-1}
\Gamma(\tfrac{2s+k-1}{2})\Gamma(\tfrac{2s+k}{2})L_L(2s+k-1,\chi)$ if $\psi$ is the trivial character mod $M$, $0$
otherwise. -/
@[kb "miyake1989" "Theorem 7.2.9, p. 284"]
def heckeD (k : ℤ) [NeZero L] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (s : ℂ) : ℂ :=
  if ψ = 1 then
    2 * (Real.sqrt π : ℂ) * I ^ (-k) * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹)) *
      (Gamma s)⁻¹ * (Gamma (s + k))⁻¹ * Gamma ((2 * s + k - 1) / 2) * Gamma ((2 * s + k) / 2) *
      DirichletCharacter.LFunction χ (2 * s + k - 1)
  else 0

/-- **Miyake, Theorem 7.2.9.** $A(s) = 2^{k+1}i^{-k}W(\psi^0)(\pi/M)^{s+k}\Gamma(s+k)^{-1}$. -/
@[kb "miyake1989" "Theorem 7.2.9, p. 285"]
def heckeA (k : ℤ) [NeZero M] (ψ : DirichletCharacter ℂ M) (s : ℂ) : ℂ :=
  haveI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  (2 : ℂ) ^ (k + 1) * I ^ (-k) * gaussSum ψ.primitiveCharacter ZMod.stdAddChar *
    ((π / M : ℝ) : ℂ) ^ (s + k) * (Gamma (s + k))⁻¹

/-- **Miyake, Theorem 7.2.9.** $B(s) = 2^{1-k}i^{-k}\psi(-1)W(\psi^0)(\pi/M)^{s}\Gamma(s)^{-1}$. -/
@[kb "miyake1989" "Theorem 7.2.9, p. 285"]
def heckeB (k : ℤ) [NeZero M] (ψ : DirichletCharacter ℂ M) (s : ℂ) : ℂ :=
  haveI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  (2 : ℂ) ^ (1 - k) * I ^ (-k) * ψ (-1) * gaussSum ψ.primitiveCharacter ZMod.stdAddChar *
    ((π / M : ℝ) : ℂ) ^ s * (Gamma s)⁻¹

/-- **Miyake, Theorem 7.2.9.** $a_n(s) = \sum_{0<c\mid n}\chi(n/c)c^{k+2s-1}
\sum_{0<d\mid(l,c)}d\,\mu(l/d)\psi^0(l/d)\overline{\psi^0}(c/d)$, $l = M/m_\psi$ (the inner sum is `gaussCoeff`). -/
@[kb "miyake1989" "Theorem 7.2.9, p. 285"]
def heckeCoeff (k : ℤ) (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (s : ℂ) (n : ℕ) : ℂ :=
  ∑ c ∈ n.divisors, χ ((n / c : ℕ) : ZMod L) * (c : ℂ) ^ ((k : ℂ) + 2 * s - 1) *
    gaussCoeff ψ.primitiveCharacter (M / ψ.conductor) c

/-- The $n$-th term $a_n(s)n^{-s}e^{2\pi inz/M}\omega(4\pi yn/M;k+s,s)$ of the first series of Theorem 7.2.9. -/
def heckeTermA (k : ℤ) (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (z : ℍ) (s : ℂ)
    (n : ℕ+) : ℂ :=
  heckeCoeff k χ ψ s n * ((n : ℕ) : ℂ) ^ (-s) * cexp (2 * π * I * (n : ℕ) * z / M) *
    omega (4 * π * z.im * (n : ℕ) / M : ℝ) (k + s) s

/-- The $n$-th term $a_n(s)n^{-s-k}e^{-2\pi in\bar z/M}\omega(4\pi yn/M;s,k+s)$ of the second series of
Theorem 7.2.9. -/
def heckeTermB (k : ℤ) (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (z : ℍ) (s : ℂ)
    (n : ℕ+) : ℂ :=
  heckeCoeff k χ ψ s n * ((n : ℕ) : ℂ) ^ (-s - k) *
    cexp (-2 * π * I * (n : ℕ) * (starRingEnd ℂ) (z : ℂ) / M) *
    omega (4 * π * z.im * (n : ℕ) / M : ℝ) s (k + s)

/-- **Miyake, Theorem 7.2.9**, the right-hand side: the continuation of $E_k(z,s;\chi,\psi)$ in $s$,
$C(s) + D(s)y^{1-k-2s} + A(s)y^{-s}\sum_{n\ge1}(\dots) + B(s)y^{-k-s}\sum_{n\ge1}(\dots)$. -/
@[kb "miyake1989" "Theorem 7.2.9, p. 284"]
def eisensteinCharSCont (k : ℤ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (z : ℍ) (s : ℂ) : ℂ :=
  heckeC k L ψ s + heckeD k χ ψ s * (z.im : ℂ) ^ (1 - k - 2 * s) +
    heckeA k ψ s * (z.im : ℂ) ^ (-s) * ∑' n : ℕ+, heckeTermA k χ ψ z s n +
    heckeB k ψ s * (z.im : ℂ) ^ (-k - s) * ∑' n : ℕ+, heckeTermB k χ ψ z s n

lemma norm_natCast_cpow_le' {c : ℕ} (hc : 1 ≤ c) {w : ℂ} {N : ℕ} (h : w.re ≤ N) :
    ‖(c : ℂ) ^ w‖ ≤ (c : ℝ) ^ N := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hc) h

lemma norm_gaussCoeff_le' {m : ℕ} (χ₀ : DirichletCharacter ℂ m) (l c : ℕ) (hc : 1 ≤ c) :
    ‖gaussCoeff χ₀ l c‖ ≤ (c : ℝ) ^ 2 := by
  unfold gaussCoeff
  have hg : Nat.gcd l c ≤ c := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right l c)
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ d ∈ (Nat.gcd l c).divisors,
      ‖(d : ℂ) * (ArithmeticFunction.moebius (l / d) : ℂ) * χ₀ ((l / d : ℕ) : ZMod m) *
        starRingEnd ℂ (χ₀ ((c / d : ℕ) : ZMod m))‖ ≤ (c : ℝ) := by
    intro d hd
    have hd' : d ≤ c := (Nat.divisor_le hd).trans hg
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
    have hμ : ‖(ArithmeticFunction.moebius (l / d) : ℂ)‖ ≤ 1 := by
      have := @ArithmeticFunction.abs_moebius_le_one (l / d)
      simpa [← Int.cast_abs] using (by exact_mod_cast this : ((|ArithmeticFunction.moebius (l / d)| : ℤ) : ℝ) ≤ 1)
    have h2 := DirichletCharacter.norm_le_one χ₀ ((l / d : ℕ) : ZMod m)
    have h3 := DirichletCharacter.norm_le_one χ₀ ((c / d : ℕ) : ZMod m)
    have hd0 : (d : ℝ) ≤ c := by exact_mod_cast hd'
    calc (d : ℝ) * ‖(ArithmeticFunction.moebius (l / d) : ℂ)‖ * ‖χ₀ ((l / d : ℕ) : ZMod m)‖ *
        ‖χ₀ ((c / d : ℕ) : ZMod m)‖ ≤ (c : ℝ) * 1 * 1 * 1 := by gcongr
      _ = c := by ring
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have : ((Nat.gcd l c).divisors.card : ℝ) ≤ c := by
    exact_mod_cast (Nat.card_divisors_le_self _).trans hg
  nlinarith [(Nat.cast_nonneg c : (0:ℝ) ≤ c)]

lemma norm_heckeCoeff_le {k : ℤ} {L M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) {s : ℂ} {N : ℕ} (hs : (k : ℝ) + 2 * s.re - 1 ≤ N) (n : ℕ) (hn : 1 ≤ n) :
    ‖heckeCoeff k χ ψ s n‖ ≤ (n : ℝ) ^ (N + 3) := by
  unfold heckeCoeff
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ c ∈ n.divisors, ‖χ ((n / c : ℕ) : ZMod L) * (c : ℂ) ^ ((k : ℂ) + 2 * s - 1) *
      gaussCoeff ψ.primitiveCharacter (M / ψ.conductor) c‖ ≤ (n : ℝ) ^ (N + 2) := by
    intro c hc
    have hc1 : 1 ≤ c := Nat.pos_of_mem_divisors hc
    have hcn : c ≤ n := Nat.divisor_le hc
    have hcn' : (c : ℝ) ≤ n := by exact_mod_cast hcn
    rw [norm_mul, norm_mul]
    have h2 := DirichletCharacter.norm_le_one χ ((n / c : ℕ) : ZMod L)
    have h3 := norm_natCast_cpow_le' hc1 (w := (k : ℂ) + 2 * s - 1) (N := N) (by simpa using hs)
    have h4 := norm_gaussCoeff_le' ψ.primitiveCharacter (M / ψ.conductor) c hc1
    have h5 : (c : ℝ) ^ N ≤ (n : ℝ) ^ N := by gcongr
    have h6 : (c : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by gcongr
    calc _ ≤ 1 * (n : ℝ) ^ N * (n : ℝ) ^ 2 := by
          gcongr
          · exact h3.trans h5
          · exact h4.trans h6
      _ = _ := by ring
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have : (n.divisors.card : ℝ) ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
  calc _ ≤ (n : ℝ) * (n : ℝ) ^ (N + 2) := by gcongr
    _ = _ := by ring

/-- **Miyake, Theorem 7.2.9 (convergence).** The two series converge absolutely and uniformly in $s$ on every
compact subset of $\mathbb C$: on such a set their terms have one summable majorant. -/
@[kb "miyake1989" "Theorem 7.2.9, p. 285"]
theorem heckeTerm_uniform (k : ℤ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (z : ℍ) {K : Set ℂ} (hK : IsCompact K) :
    ∃ u : ℕ+ → ℝ, Summable u ∧ ∀ s ∈ K, ∀ n : ℕ+,
      ‖heckeTermA k χ ψ z s n‖ ≤ u n ∧ ‖heckeTermB k χ ψ z s n‖ ≤ u n := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |(k : ℝ)| + 2 * R + 1 ≤ N := exists_nat_ge _
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hy := z.im_pos
  set y0 : ℝ := 4 * π * z.im / M with hy0
  have hy0pos : 0 < y0 := by positivity
  have hc1 : Continuous fun s : ℂ ↦ ((k : ℂ) + s, s) := by fun_prop
  have hc2 : Continuous fun s : ℂ ↦ (s, (k : ℂ) + s) := by fun_prop
  obtain ⟨A1, hA1, B1, hB1, h1⟩ := omega_bound (hK.image hc1)
  obtain ⟨A2, hA2, B2, hB2, h2⟩ := omega_bound (hK.image hc2)
  set W : ℝ := A1 * (1 + y0 ^ (-B1)) + A2 * (1 + y0 ^ (-B2)) with hW
  have hWpos : 0 ≤ W := by positivity
  set r : ℝ := Real.exp (-(2 * π * z.im / M)) with hr
  have hr1 : ‖r‖ < 1 := by
    rw [hr, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have : 0 < 2 * π * z.im / M := by positivity
    simpa using this
  have hsum : Summable fun n : ℕ ↦ (n : ℝ) ^ (2 * N + 3) * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one _ hr1
  refine ⟨fun n ↦ ((n : ℕ) : ℝ) ^ (2 * N + 3) * r ^ (n : ℕ) * W,
    (hsum.comp_injective PNat.coe_injective).mul_right W, fun s hs n ↦ ?_⟩
  have hn1 : 1 ≤ (n : ℕ) := n.pos
  have hn1' : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast hn1
  have hsR : |s.re| ≤ R := (Complex.abs_re_le_norm s).trans (hR s hs)
  have hcoef : ‖heckeCoeff k χ ψ s n‖ ≤ ((n : ℕ) : ℝ) ^ (N + 3) :=
    norm_heckeCoeff_le χ ψ (by have := le_abs_self s.re; have := le_abs_self (k : ℝ); linarith) _ hn1
  have hexp1 : ‖cexp (2 * π * I * (n : ℕ) * z / M)‖ = r ^ (n : ℕ) := by
    rw [Complex.norm_exp, hr, ← Real.exp_nat_mul]
    congr 1
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.normSq_natCast]
    field_simp
  have hexp2 : ‖cexp (-2 * π * I * (n : ℕ) * (starRingEnd ℂ) (z : ℂ) / M)‖ = r ^ (n : ℕ) := by
    rw [Complex.norm_exp, hr, ← Real.exp_nat_mul]
    congr 1
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.normSq_natCast]
    field_simp
  have hyn : y0 ≤ 4 * π * z.im * (n : ℕ) / M := by
    rw [hy0]
    have h4 : 4 * π * z.im ≤ 4 * π * z.im * (n : ℕ) := le_mul_of_one_le_right (by positivity) hn1'
    exact div_le_div_of_nonneg_right h4 hMpos.le
  have hyn0 : 0 < 4 * π * z.im * (n : ℕ) / M := hy0pos.trans_le hyn
  have hom1 : ‖omega (4 * π * z.im * (n : ℕ) / M : ℝ) (k + s) s‖ ≤ W := by
    have := h1 _ hyn0 ((k : ℂ) + s, s) ⟨s, hs, rfl⟩
    refine this.trans ?_
    have h3 : (4 * π * z.im * (n : ℕ) / M) ^ (-B1) ≤ y0 ^ (-B1) :=
      Real.rpow_le_rpow_of_nonpos hy0pos hyn (by linarith)
    have : 0 ≤ A2 * (1 + y0 ^ (-B2)) := by positivity
    rw [hW]
    nlinarith
  have hom2 : ‖omega (4 * π * z.im * (n : ℕ) / M : ℝ) s (k + s)‖ ≤ W := by
    have := h2 _ hyn0 (s, (k : ℂ) + s) ⟨s, hs, rfl⟩
    refine this.trans ?_
    have h3 : (4 * π * z.im * (n : ℕ) / M) ^ (-B2) ≤ y0 ^ (-B2) :=
      Real.rpow_le_rpow_of_nonpos hy0pos hyn (by linarith)
    have : 0 ≤ A1 * (1 + y0 ^ (-B1)) := by positivity
    rw [hW]
    nlinarith
  have hp1 : ‖((n : ℕ) : ℂ) ^ (-s)‖ ≤ ((n : ℕ) : ℝ) ^ N :=
    norm_natCast_cpow_le' hn1 (by simp; have := neg_le_abs s.re; have := abs_nonneg s.re; have := le_abs_self (k : ℝ); have := abs_nonneg (k:ℝ); linarith)
  have hp2 : ‖((n : ℕ) : ℂ) ^ (-s - k)‖ ≤ ((n : ℕ) : ℝ) ^ N :=
    norm_natCast_cpow_le' hn1 (by simp; have := neg_le_abs s.re; have := abs_nonneg s.re; have := neg_le_abs (k : ℝ); have := abs_nonneg (k:ℝ); linarith)
  have hnpow : ((n : ℕ) : ℝ) ^ (N + 3) * ((n : ℕ) : ℝ) ^ N = ((n : ℕ) : ℝ) ^ (2 * N + 3) := by
    rw [← pow_add]; congr 1; ring
  constructor
  · unfold heckeTermA
    rw [norm_mul, norm_mul, norm_mul, hexp1]
    calc _ ≤ ((n : ℕ) : ℝ) ^ (N + 3) * ((n : ℕ) : ℝ) ^ N * r ^ (n : ℕ) * W := by gcongr
      _ = _ := by rw [hnpow]
  · unfold heckeTermB
    rw [norm_mul, norm_mul, norm_mul, hexp2]
    calc _ ≤ ((n : ℕ) : ℝ) ^ (N + 3) * ((n : ℕ) : ℝ) ^ N * r ^ (n : ℕ) * W := by gcongr
      _ = _ := by rw [hnpow]

lemma differentiable_heckeCoeff (k : ℤ) [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (n : ℕ) : Differentiable ℂ (fun s ↦ heckeCoeff k χ ψ s n) := by
  unfold heckeCoeff
  refine Differentiable.fun_sum fun c hc ↦ ?_
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hc).ne'
  have : Differentiable ℂ fun s : ℂ ↦ (c : ℂ) ^ ((k : ℂ) + 2 * s - 1) :=
    Differentiable.const_cpow (by fun_prop) (Or.inl hc0)
  exact (this.const_mul _).mul_const _

lemma differentiable_omega_comp (x : ℝ) (hx : 0 < x) (f g : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) : Differentiable ℂ (fun s ↦ omega (x : ℂ) (f s) (g s)) := by
  intro s
  have h := differentiableOn_omega.differentiableAt (x := ((x : ℂ), f s, g s))
    ((isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).mem_nhds
      (by simpa using hx))
  have h2 : DifferentiableAt ℂ (fun s : ℂ ↦ ((x : ℂ), f s, g s)) s :=
    (differentiableAt_const _).prodMk ((hf s).prodMk (hg s))
  exact h.comp s h2

lemma differentiable_heckeTermA (k : ℤ) [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (z : ℍ) (n : ℕ+) :
    Differentiable ℂ (fun s ↦ heckeTermA k χ ψ z s n) := by
  unfold heckeTermA
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hn0 : (((n : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast n.pos.ne'
  have h1 : Differentiable ℂ fun s : ℂ ↦ ((n : ℕ) : ℂ) ^ (-s) :=
    Differentiable.const_cpow (by fun_prop) (Or.inl hn0)
  have h2 := differentiable_omega_comp (4 * π * z.im * (n : ℕ) / M) (by have := z.im_pos; positivity)
    (fun s ↦ (k : ℂ) + s) (fun s ↦ s) (by fun_prop) differentiable_id
  exact (((differentiable_heckeCoeff k χ ψ n).mul h1).mul_const _).mul h2

lemma differentiable_heckeTermB (k : ℤ) [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (z : ℍ) (n : ℕ+) :
    Differentiable ℂ (fun s ↦ heckeTermB k χ ψ z s n) := by
  unfold heckeTermB
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hn0 : (((n : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast n.pos.ne'
  have h1 : Differentiable ℂ fun s : ℂ ↦ ((n : ℕ) : ℂ) ^ (-s - k) :=
    Differentiable.const_cpow (by fun_prop) (Or.inl hn0)
  have h2 := differentiable_omega_comp (4 * π * z.im * (n : ℕ) / M) (by have := z.im_pos; positivity)
    (fun s ↦ s) (fun s ↦ (k : ℂ) + s) differentiable_id (by fun_prop)
  exact (((differentiable_heckeCoeff k χ ψ n).mul h1).mul_const _).mul h2

/-- **Miyake, Theorem 7.2.9.** The two series are entire functions of $s$. -/
@[kb "miyake1989" "Theorem 7.2.9, p. 285"]
theorem differentiable_tsum_heckeTermA (k : ℤ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (z : ℍ) :
    Differentiable ℂ (fun s ↦ ∑' n : ℕ+, heckeTermA k χ ψ z s n) := by
  refine differentiable_tsum_of_locally_bounded (differentiable_heckeTermA k χ ψ z) fun x ↦ ?_
  obtain ⟨u, hu, h⟩ := heckeTerm_uniform k χ ψ z (isCompact_closedBall x 1)
  exact ⟨_, Metric.closedBall_mem_nhds x one_pos, u, hu, fun n y hy ↦ (h y hy n).1⟩

/-- **Miyake, Theorem 7.2.9.** The two series are entire functions of $s$. -/
@[kb "miyake1989" "Theorem 7.2.9, p. 285"]
theorem differentiable_tsum_heckeTermB (k : ℤ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (z : ℍ) :
    Differentiable ℂ (fun s ↦ ∑' n : ℕ+, heckeTermB k χ ψ z s n) := by
  refine differentiable_tsum_of_locally_bounded (differentiable_heckeTermB k χ ψ z) fun x ↦ ?_
  obtain ⟨u, hu, h⟩ := heckeTerm_uniform k χ ψ z (isCompact_closedBall x 1)
  exact ⟨_, Metric.closedBall_mem_nhds x one_pos, u, hu, fun n y hy ↦ (h y hy n).2⟩

lemma meromorphicAt_LFunction' {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (w : ℂ) :
    MeromorphicAt (DirichletCharacter.LFunction χ) w := by
  by_cases h : w = 1 ∧ χ = 1
  · obtain ⟨rfl, rfl⟩ := h
    have h1 : MeromorphicAt (fun s : ℂ ↦ DirichletCharacter.LFunctionTrivChar₁ m s * (s - 1)⁻¹) 1 :=
      ((DirichletCharacter.differentiable_LFunctionTrivChar₁ m).analyticAt 1).meromorphicAt.mul
        (((analyticAt_id.sub analyticAt_const).meromorphicAt).inv)
    refine h1.congr ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s ≠ 1 := hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs'
    simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs']
    field_simp

  · refine (Complex.analyticAt_iff_eventually_differentiableAt.2 ?_).meromorphicAt
    by_cases hw : w = 1
    · have hχ : χ ≠ 1 := fun hχ ↦ h ⟨hw, hχ⟩
      exact Filter.Eventually.of_forall fun s ↦ DirichletCharacter.differentiableAt_LFunction χ s (Or.inr hχ)
    · filter_upwards [isOpen_ne.mem_nhds hw] with s hs
      exact DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)

lemma meromorphicAt_LFunction_comp {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) {g : ℂ → ℂ} {x : ℂ}
    (hg : AnalyticAt ℂ g x) : MeromorphicAt (fun s ↦ DirichletCharacter.LFunction χ (g s)) x :=
  (meromorphicAt_LFunction' χ (g x)).comp_analyticAt hg

lemma meromorphicAt_Gamma_comp {g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) :
    MeromorphicAt (fun s ↦ Gamma (g s)) x := by
  have h1 : MeromorphicAt ((fun s : ℂ ↦ (Gamma s)⁻¹)⁻¹) (g x) :=
    (((Complex.differentiable_one_div_Gamma).analyticAt (g x)).meromorphicAt).inv
  have h2 : MeromorphicAt Gamma (g x) := by
    convert h1 using 1
    funext s
    simp
  exact h2.comp_analyticAt hg

lemma differentiable_inv_Gamma_comp {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ (fun s ↦ (Gamma (g s))⁻¹) := by
  have := Complex.differentiable_one_div_Gamma.comp hg
  simpa [Function.comp_def, one_div] using this

lemma meromorphicAt_heckeC (k : ℤ) (L : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (x : ℂ) :
    MeromorphicAt (heckeC k L ψ) x := by
  by_cases h : L = 1
  · have e : heckeC k L ψ = fun s ↦ 2 * DirichletCharacter.LFunction ψ (2 * s + k) := by
      funext s; simp [heckeC, h]
    rw [e]
    exact (MeromorphicAt.const _ x).mul (meromorphicAt_LFunction_comp ψ (by fun_prop))
  · have e : heckeC k L ψ = fun _ ↦ 0 := by
      funext s; simp [heckeC, h]
    rw [e]
    exact MeromorphicAt.const _ x

lemma meromorphicAt_heckeD (k : ℤ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (x : ℂ) : MeromorphicAt (heckeD k χ ψ) x := by
  by_cases h : ψ = 1
  · have e : heckeD k χ ψ = fun s ↦
        2 * (Real.sqrt π : ℂ) * I ^ (-k) * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹)) *
        (Gamma s)⁻¹ * (Gamma (s + k))⁻¹ * Gamma ((2 * s + k - 1) / 2) * Gamma ((2 * s + k) / 2) *
        DirichletCharacter.LFunction χ (2 * s + k - 1) := by
      funext s; simp only [heckeD, h, ↓reduceIte]
    rw [e]
    have h1 : MeromorphicAt (fun s : ℂ ↦ (Gamma s)⁻¹) x :=
      ((differentiable_inv_Gamma_comp (g := id) differentiable_id).analyticAt x).meromorphicAt
    have h2 : MeromorphicAt (fun s : ℂ ↦ (Gamma (s + k))⁻¹) x :=
      ((differentiable_inv_Gamma_comp (g := fun s ↦ s + k) (by fun_prop)).analyticAt x).meromorphicAt
    exact ((((((MeromorphicAt.const _ x).mul h1).mul h2).mul
      (meromorphicAt_Gamma_comp (by fun_prop))).mul (meromorphicAt_Gamma_comp (by fun_prop))).mul
      (meromorphicAt_LFunction_comp χ (by fun_prop)))
  · have e : heckeD k χ ψ = fun _ ↦ 0 := by
      funext s; simp [heckeD, h]
    rw [e]
    exact MeromorphicAt.const _ x

lemma differentiable_heckeA (k : ℤ) [NeZero M] (ψ : DirichletCharacter ℂ M) :
    Differentiable ℂ (heckeA k ψ) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have h1 : Differentiable ℂ fun s : ℂ ↦ (((π / M : ℝ) : ℂ)) ^ (s + k) :=
    Differentiable.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast (by positivity : (π / M : ℝ) ≠ 0)))
  have h2 := differentiable_inv_Gamma_comp (g := fun s : ℂ ↦ s + k) (by fun_prop)
  unfold heckeA
  exact ((h1.const_mul _)).mul h2

lemma differentiable_heckeB (k : ℤ) [NeZero M] (ψ : DirichletCharacter ℂ M) :
    Differentiable ℂ (heckeB k ψ) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have h1 : Differentiable ℂ fun s : ℂ ↦ (((π / M : ℝ) : ℂ)) ^ s :=
    Differentiable.const_cpow differentiable_id (Or.inl (by exact_mod_cast (by positivity : (π / M : ℝ) ≠ 0)))
  have h2 := differentiable_inv_Gamma_comp (g := fun s : ℂ ↦ s) differentiable_id
  unfold heckeB
  exact ((h1.const_mul _)).mul h2

lemma differentiable_im_cpow (y : ℝ) (hy : 0 < y) (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    Differentiable ℂ (fun s ↦ (y : ℂ) ^ (g s)) :=
  Differentiable.const_cpow hg (Or.inl (by exact_mod_cast hy.ne'))

/-- **Miyake, Theorem 7.2.9 (meromorphy).** The continuation is meromorphic on the whole $s$-plane. -/
@[kb "miyake1989" "Theorem 7.2.9, p. 284"]
theorem meromorphicOn_eisensteinCharSCont (k : ℤ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (z : ℍ) :
    MeromorphicOn (eisensteinCharSCont k χ ψ z) univ := by
  intro x _
  have hy := z.im_pos
  have e1 := differentiable_im_cpow z.im hy (fun s ↦ 1 - k - 2 * s) (by fun_prop)
  have e2 := differentiable_im_cpow z.im hy (fun s ↦ -s) (by fun_prop)
  have e3 := differentiable_im_cpow z.im hy (fun s ↦ -k - s) (by fun_prop)
  have hA := ((differentiable_heckeA k ψ).mul e2).mul (differentiable_tsum_heckeTermA k χ ψ z)
  have hB := ((differentiable_heckeB k ψ).mul e3).mul (differentiable_tsum_heckeTermB k χ ψ z)
  show MeromorphicAt (fun s ↦ heckeC k L ψ s + heckeD k χ ψ s * (z.im : ℂ) ^ (1 - k - 2 * s) +
    heckeA k ψ s * (z.im : ℂ) ^ (-s) * ∑' n : ℕ+, heckeTermA k χ ψ z s n +
    heckeB k ψ s * (z.im : ℂ) ^ (-k - s) * ∑' n : ℕ+, heckeTermB k χ ψ z s n) x
  exact (((meromorphicAt_heckeC k L ψ x).add
    ((meromorphicAt_heckeD k χ ψ x).mul ((e1.analyticAt x).meromorphicAt))).add
      ((hA.analyticAt x).meromorphicAt)).add ((hB.analyticAt x).meromorphicAt)

end ModularFormsKB.Miyake.HeckeTrick
