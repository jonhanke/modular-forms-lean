/-
# The Petersson norm and $L(\mathrm{Sym}^2f, k)$ at level one

The end of headline **H2**: for a normalized Hecke eigenform
$f \in S_k(\mathrm{SL}_2(\mathbb Z))$, $\langle f,f\rangle = \frac{2\Gamma(k)}{\pi(4\pi)^k}L(\mathrm{Sym}^2f,k)$
(`petersson_eq_symSq`), where $L(\mathrm{Sym}^2f,\cdot)$ is continued to $\operatorname{Re}w \ge k$ as the quotient of the
continued Rankin–Selberg function by $\zeta$ (`symSqLc`). Shimura's entire continuation is only stated
(`SymmetricSquareHolomorphy`).
-/
import ModularFormsKB.RankinSelberg.SymmetricSquare

open MeasureTheory Set Filter Topology Complex Asymptotics MatrixGroups
open scoped UpperHalfPlane Real ComplexConjugate

noncomputable section

namespace ModularFormsKB.RankinSelberg

open ModularFormsKB.HalfIntegral UpperHalfPlane

/-! ### The value at $w = k$ and the Petersson norm -/

/-- $(s-1)\zeta(s)$, with its limit $1$ at $s = 1$. -/
def zetaEntire (s : ℂ) : ℂ := if s = 1 then 1 else (s - 1) * riemannZeta s

/-- **The continued symmetric square $L$-function** on $\operatorname{Re}w \ge k$:
$L(\mathrm{Sym}^2f,w) = (s-1)L(f\times\bar f,s)\,/\,(s-1)\zeta(s)$, $s = w-k+1$. -/
def symSqLc (k : ℕ) (f : CuspForm 𝒮ℒ (k : ℤ)) (w : ℂ) : ℂ :=
  rankinSelbergEntire k f f (w - k + 1) / zetaEntire (w - k + 1)


theorem zetaEntire_ne_zero {s : ℂ} (hs : 1 ≤ s.re) : zetaEntire s ≠ 0 := by
  unfold zetaEntire
  split_ifs with h
  · exact one_ne_zero
  · exact mul_ne_zero (sub_ne_zero.2 h) (riemannZeta_ne_zero_of_one_le_re hs)

theorem zetaEntire_eq {s : ℂ} (hs : s ≠ 1) : zetaEntire s = (s - 1) * riemannZeta s := by
  simp [zetaEntire, hs]

theorem differentiableAt_zetaEntire_of_ne {s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ zetaEntire s := by
  have hd : DifferentiableAt ℂ (fun s ↦ (s - 1) * riemannZeta s) s :=
    (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds hs] with t ht
  exact zetaEntire_eq ht

/-- $(s-1)\zeta(s)$ is entire (the pole of $\zeta$ at $1$ is simple with residue $1$). -/
theorem differentiable_zetaEntire : Differentiable ℂ zetaEntire := by
  have hc : ContinuousAt zetaEntire 1 := by
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
    have h1 : zetaEntire 1 = 1 := by simp [zetaEntire]
    rw [h1]
    refine riemannZeta_residue_one.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (zetaEntire_eq ht).symm
  have hon : DifferentiableOn ℂ zetaEntire (univ \ {1}) := fun t ht ↦
    (differentiableAt_zetaEntire_of_ne ht.2).differentiableWithinAt
  have := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
    (Filter.univ_mem (f := 𝓝 (1 : ℂ)))).1 ⟨hon, hc⟩
  exact fun t ↦ this.differentiableAt Filter.univ_mem

/-- The value $(s-1)L(f\times\bar g,s)|_{s=1} = \frac\pi2\frac{(4\pi)^k}{\Gamma(k)}\langle g,f\rangle$. -/
theorem rankinSelbergEntire_one (k : ℕ) (f g : CuspForm 𝒮ℒ (k : ℤ)) :
    rankinSelbergEntire k f g 1 =
      (π : ℂ) / 2 * (4 * π : ℂ) ^ k / Gamma k * CuspForm.peterssonInnerFd g f := by
  rw [rankinSelbergEntire, rsFactor]
  simp only [sub_self, zero_mul, mul_zero, Complex.Gamma_one, inv_one, mul_one, Complex.cpow_one]
  rw [show (1 : ℂ) + k - 1 = k by ring, Complex.cpow_natCast]
  ring

/-- **The Petersson norm and the symmetric square** (Rankin 1939 `rankin1939`; Zagier 1977 `zagier1977` [unverified];
headline H2, second half). For a normalized Hecke eigenform $f \in S_k(\mathrm{SL}_2(\mathbb Z))$, $k \ge 1$, the function
`symSqLc` agrees with the Euler product $L(\mathrm{Sym}^2f,w)$ for $\operatorname{Re}w > k+1$, is holomorphic at every $w$
with $\operatorname{Re}w \ge k$, and
$$\langle f,f\rangle = \frac{2\,\Gamma(k)}{\pi(4\pi)^k}\,L(\mathrm{Sym}^2f,k).$$ -/
@[kb "zagier1977" "the Petersson norm of a level one eigenform is 2 Gamma(k) / (pi (4 pi)^k) times L(Sym^2 f, k) [unverified]"]
theorem petersson_eq_symSq (k : ℕ) (hk : 1 ≤ k) (f : CuspForm 𝒮ℒ (k : ℤ))
    (hf : IsNormalizedEigenform k (coeff f)) :
    (∀ w : ℂ, (k : ℝ) + 1 < w.re → symSqLc k f w = symSqL k f w) ∧
    (∀ w : ℂ, (k : ℝ) ≤ w.re → DifferentiableAt ℂ (symSqLc k f) w) ∧
    CuspForm.peterssonInnerFd f f = 2 * Gamma k / ((π : ℂ) * (4 * π : ℂ) ^ k) * symSqLc k f k := by
  refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_, ?_⟩
  · set s := w - k + 1 with hs
    have hsre : 2 < s.re := by
      simp only [hs, Complex.add_re, Complex.sub_re, Complex.natCast_re, Complex.one_re]
      linarith
    have hs1 : s ≠ 1 := fun h ↦ by rw [h] at hsre; norm_num at hsre
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
    have hw' : s + k - 1 = w := by rw [hs]; ring
    have hE : rankinSelbergEntire k f f s = (s - 1) * rankinSelbergL k f f s := by
      rw [← rankinSelbergLc_eq_L k hk f f hsre, rankinSelbergLc]
      field_simp
    have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by linarith)
    unfold symSqLc
    rw [← hs, hE, (symSqL_spec k hk f hf hsre).2, hw', zetaEntire_eq hs1]
    field_simp
  · have hd : DifferentiableAt ℂ (fun w : ℂ ↦ w - k + 1) w :=
      (differentiableAt_id.sub_const _).add_const _
    have hre : 1 ≤ (w - k + 1).re := by
      simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re, Complex.one_re]
      linarith
    exact ((differentiable_rankinSelbergEntire k f f).differentiableAt.comp w hd).div
      (differentiable_zetaEntire.differentiableAt.comp w hd) (zetaEntire_ne_zero hre)
  · have h1 : symSqLc k f k =
        (π : ℂ) / 2 * (4 * π : ℂ) ^ k / Gamma k * CuspForm.peterssonInnerFd f f := by
      unfold symSqLc
      rw [show (k : ℂ) - k + 1 = 1 by ring, rankinSelbergEntire_one]
      simp [zetaEntire]
    rw [h1]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    have h4π : (4 * π : ℂ) ^ k ≠ 0 := pow_ne_zero _ (mul_ne_zero (by norm_num) hπ)
    have hG : Gamma (k : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
      simp only [Complex.natCast_re]; exact_mod_cast hk)
    field_simp

/-! ### Shimura's holomorphy, stated -/

/-- **Shimura's theorem** (Shimura 1975 `shimura1975`, Theorem 1 [unverified]): for a normalized Hecke eigenform $f$ of
level one, $L(\mathrm{Sym}^2f,w)$ continues to an entire function. Only stated; nothing in this library uses it
(the proof is Rankin's method with a theta series and a half-integral weight Eisenstein series, plan §4). -/
@[kb "shimura1975" "holomorphy of the symmetric square L-function of a level one eigenform [unverified]"]
def SymmetricSquareHolomorphy : Prop :=
  ∀ (k : ℕ) (f : CuspForm 𝒮ℒ (k : ℤ)), IsNormalizedEigenform k (coeff f) →
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ w : ℂ, (k : ℝ) + 1 < w.re → F w = symSqL k f w

end ModularFormsKB.RankinSelberg
