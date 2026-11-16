/-
# The root number of $E_n$

**Odd $n$ (proved).** For odd squarefree $n$, $L(E_n, s) = L(f_{32} \otimes \psi_n, s)$ with
$\psi_n = \left(\frac\cdot n\right)$, a real primitive character of conductor $n$ prime to $32$ (on the support of
$b$, $m \equiv 1 \bmod 4$, so $\left(\frac nm\right) = \left(\frac mn\right)$). Miyake's Theorem 4.3.11
(`Miyake.fricke_twist`, the coprime case of Atkin–Li) with the Fricke eigenvalue $f_{32}|_2\omega_{32} = -f_{32}$
(`fricke_f32`) gives the functional equation
$$\Lambda(2 - s) = \left(\tfrac{-2}{n}\right)\Lambda(s),\qquad
\Lambda(s) = \left(\frac{2\pi}{\sqrt{32n^2}}\right)^{-s}\Gamma(s)L(E_n, s)$$
(`congruentFE_odd`): Weil's constant is $C_\psi = \psi(-32) W(\psi)/W(\bar\psi) = \left(\frac{-32}n\right)$. So the
root number is $-1$ exactly for $n \equiv 5, 7 \bmod 8$.

**Even $n$ (named input).** For $n = 2m$, $2$ divides both the level $32$ and the conductor $8m$ of the twist, so
neither Miyake 4.3.11 nor Atkin–Li in the coprime form applies. The route is the Hecke
character $\xi$ of $\mathbb Q(i)$ attached to $f_{32}$: $L(E_{2m}, s) = L(\xi \cdot (\chi_{2m} \circ N), s)$ and Hecke's
functional equation for it. Mathlib's `HeckeCharacter.LFunction` is an Euler product with no continuation, so this is
the named input `HeckeCharacterRootNumber` (Hecke 1920; root number of Birch–Stephens 1966 [unverified]).

**Row 11** (`congruentRootNumber`): $L(E_n, 1) = 0$ for squarefree $n \equiv 5, 6, 7 \bmod 8$, from
`F32Modular` (proved, row 8) and `HeckeCharacterRootNumber` (even $n$ only).
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.LValue
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.F32Fricke
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.JacobiChar
import ModularFormsKB.Miyake.Sec4_3.Twist

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open Complex
open scoped Real

/-- **The root number of $E_n$** predicted by Birch–Stephens: $-1$ for $n \equiv 5, 6, 7 \bmod 8$, $+1$ otherwise
($n$ squarefree). -/
noncomputable def congruentSign (n : ℕ) : ℂ := if n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 then -1 else 1

/-- **Hecke's functional equation for $L(E_{2m}, s)$ with its root number** (Hecke 1920 `hecke1920`; the root
number by Birch–Stephens 1966 `birchstephens1966` [unverified]): for odd squarefree $m$, $E_{2m}$ has complex
multiplication by $\mathbb Z[i]$, $L(E_{2m}, s)$ is the $L$-function of the Hecke character $\xi\cdot(\chi_{2m}\circ N)$
of $\mathbb Q(i)$, and $\Lambda(s) = (2\pi/\sqrt{64m^2})^{-s}\Gamma(s)L(E_{2m}, s)$ continues to an entire function
with $\Lambda(2 - s) = w\,\Lambda(s)$, $w = -1$ for $m \equiv 3, 7 \bmod 8$ and $w = 1$ for $m \equiv 1, 5 \bmod 8$.
($64m^2$ is the conductor of $E_{2m}$.) A cited theorem, not proved here: Mathlib's Hecke $L$-functions have no
continuation (a loose end). -/
@[kb "birchstephens1966" "Λ(E_{2m}, s) = (√(64m²)/2π)^s Γ(s) L(E_{2m}, s) is entire with Λ(2 − s) = w Λ(s), w = −1 iff 2m ≡ 6 mod 8 (Hecke's functional equation for the Grössencharacter of Q(i)) [unverified]"]
structure HeckeCharacterRootNumber : Prop where
  fe : ∀ m : ℕ, Odd m → Squarefree m → CongruentFE (2 * m) (64 * m ^ 2) (congruentSign (2 * m))

/-- **The root number of $E_n$ is $-1$ for $n \equiv 5, 6, 7 \bmod 8$, so $L(E_n, 1) = 0$** (Birch–Stephens 1966
`birchstephens1966` [unverified]; the functional equation of $L(E_n, s)$ with sign $-1$). Proved here
(`congruentRootNumber`) from `HeckeCharacterRootNumber`; it is no longer a named input. -/
structure CongruentRootNumber : Prop where
  vanish : ∀ n : ℕ, 0 < n → Squarefree n → (n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7) → LValueAtOne n 0

/-! ## Odd $n$: the twist of $f_{32}$ by $\left(\frac\cdot n\right)$ -/

/-- On the support of $b$, $\left(\frac mn\right) b(m) = \left(\frac nm\right) b(m)$ ($b(m) \ne 0$ forces
$m \equiv 1 \bmod 4$, and quadratic reciprocity). -/
theorem lCoeff_eq {n : ℕ} [NeZero n] (hn : Squarefree n) :
    lCoeff n = fun d ↦ (congruentCoeff n d : ℂ) := by
  funext d; rw [lCoeff, LFunction_congruentCurve_eq hn d]

theorem twist_jacobiChar_f32C {n : ℕ} [NeZero n] (hn : Odd n) (hsq : Squarefree n) :
    Miyake.twist (jacobiChar n) f32C = lCoeff n := by
  rw [lCoeff_eq hsq]
  funext m
  simp only [Miyake.twist, f32C, congruentCoeff]
  by_cases hb : f32Coeff m = 0
  · simp [hb]
  have h4 := mod_four_eq_one_of_f32Coeff_ne_zero hb
  rw [jacobiChar_natCast hn, jacobiSym.quadratic_reciprocity_one_mod_four h4 hn]
  push_cast
  ring

/-- $\left(\frac{-32}{n}\right)$ is the predicted sign for odd $n$. -/
theorem jacobiSym_neg_thirtyTwo {n : ℕ} (hn : Odd n) : (jacobiSym (-32) n : ℂ) = congruentSign n := by
  have h16 : jacobiSym 16 n = 1 := by
    have : (16 : ℤ) = 4 ^ 2 := by norm_num
    rw [this]
    refine jacobiSym.sq_one' ?_
    have h2 : Nat.Coprime 4 n := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact (Nat.coprime_two_right.mpr hn).symm.pow_left 2
    have h3 : Int.gcd ((4 : ℕ) : ℤ) ((n : ℕ) : ℤ) = 1 := by rw [Int.gcd_natCast_natCast]; exact h2
    exact_mod_cast h3
  have : (-32 : ℤ) = -2 * 16 := by norm_num
  rw [this, jacobiSym.mul_left, h16, mul_one, jacobiSym.at_neg_two hn, ZMod.χ₈'_nat_eq_if_mod_eight]
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  have h8 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  unfold congruentSign
  rcases h8 with h | h | h | h <;> simp [h, hn2]

/-- **Weil's constant of the twist by $\left(\frac\cdot n\right)$** at level $32$ is $\left(\frac{-32}n\right)$. -/
theorem weilConstant_jacobiChar {n : ℕ} [NeZero n] (hn : Odd n) (hsq : Squarefree n) :
    Miyake.weilConstant (1 : DirichletCharacter ℂ 32) (jacobiChar n) = congruentSign n := by
  have hW : Miyake.gaussW (jacobiChar n) ≠ 0 := Miyake.gaussW_ne_zero (isPrimitive_jacobiChar hn hsq)
  have hu : IsUnit ((n : ℕ) : ZMod 32) := by
    rw [ZMod.isUnit_iff_coprime, show (32 : ℕ) = 2 ^ 5 by norm_num]
    exact (Nat.coprime_two_right.mpr hn).pow_right 5
  unfold Miyake.weilConstant
  rw [jacobiChar_inv hn, MulChar.one_apply hu, one_mul, mul_div_assoc, div_self hW, mul_one,
    ← jacobiSym_neg_thirtyTwo hn, ← jacobiChar_intCast hn]
  push_cast
  ring_nf

/-- $\sqrt{32 n^2} = n\sqrt{32}$. -/
theorem sqrt_thirtyTwo_mul_sq (n : ℕ) : √((32 * n ^ 2 : ℕ) : ℝ) = n * √(32 : ℕ) := by
  push_cast
  rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity), mul_comm]

/-- **Row 10 for $f_{32}$: the functional equation of $L(E_n, s)$, $n$ odd squarefree**, with conductor $32n^2$ and
sign $\left(\frac{-2}n\right)$ (Miyake Theorem 4.3.11 with the Fricke eigenvalue $-1$ of $f_{32}$). -/
theorem congruentFE_odd {n : ℕ} [NeZero n] (hn : Odd n) (hsq : Squarefree n) :
    CongruentFE n ((32 * n ^ 2 : ℕ) : ℝ) (congruentSign n) := by
  have hψ := isPrimitive_jacobiChar hn hsq
  have hcop : n.Coprime 32 := by
    rw [show (32 : ℕ) = 2 ^ 5 by norm_num]
    exact (Nat.coprime_two_right.mpr hn).pow_right 5
  have hb : Miyake.CoeffGrowth (fun m ↦ -f32C m) := by
    obtain ⟨ν, hν⟩ := coeffGrowth_f32C
    exact ⟨ν, hν.neg_left⟩
  obtain ⟨Φ, hΦd, -, σ₀, h1, h2⟩ := Miyake.twisted_completedL_cuspForm (k := 2) (N := 32) (m := n)
    two_pos (by norm_num) 1 (jacobiChar n) hψ hcop coeffGrowth_f32C hb isCuspFormChar_f32
    (fun z hz ↦ by simpa using fricke_f32 z hz)
  rw [jacobiChar_inv hn, weilConstant_jacobiChar hn hsq] at h2
  have htw : ∀ s : ℂ, Miyake.twistedCompletedL (32 : ℕ) (jacobiChar n) f32C s =
      Miyake.completedL ((32 * n ^ 2 : ℕ) : ℝ) (lCoeff n) s := by
    intro s
    rw [Miyake.twistedCompletedL, Miyake.completedL, twist_jacobiChar_f32C hn hsq, sqrt_thirtyTwo_mul_sq]
  have htwneg : ∀ s : ℂ, Miyake.twistedCompletedL (32 : ℕ) (jacobiChar n) (fun m ↦ -f32C m) s =
      -Miyake.twistedCompletedL (32 : ℕ) (jacobiChar n) f32C s := by
    intro s
    have : Miyake.twist (jacobiChar n) (fun m ↦ -f32C m) = -Miyake.twist (jacobiChar n) f32C := by
      funext m; simp [Miyake.twist]
    rw [Miyake.twistedCompletedL, Miyake.twistedCompletedL, this, LSeries_neg]
    ring
  refine ⟨Φ, hΦd, ⟨σ₀, fun s hs ↦ by rw [h1 s (by exact_mod_cast hs), htw]⟩, fun s ↦ ?_⟩
  -- both sides are entire and agree on `Re s > σ₀`
  have hA : AnalyticOnNhd ℂ (fun s ↦ Φ (2 - s)) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (hΦd.comp (differentiable_const _ |>.sub differentiable_id))
  have hB : AnalyticOnNhd ℂ (fun s ↦ congruentSign n * Φ s) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr ((differentiable_const _).mul hΦd)
  have heq : (fun s ↦ Φ (2 - s)) = fun s ↦ congruentSign n * Φ s := by
    refine hA.eq_of_eventuallyEq hB (z₀ := ((σ₀ + 1 : ℝ) : ℂ)) ?_
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨{z : ℂ | σ₀ < z.re},
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp), fun z hz ↦ ?_⟩
    have hz' : (σ₀ : ℝ) < ((2 : ℕ) : ℝ) - (2 - z).re := by simp; exact hz
    simp only
    rw [h2 (2 - z) hz', show ((2 : ℕ) : ℂ) - (2 - z) = z by push_cast; ring, htwneg,
      h1 z (by exact_mod_cast hz)]
    simp [I_sq]
  exact congrFun heq s

/-- **Row 11: `CongruentRootNumber`**, from `F32Modular` (proved) for odd $n$ and the named input
`HeckeCharacterRootNumber` for even $n$. -/
theorem congruentRootNumber (hH : HeckeCharacterRootNumber) : CongruentRootNumber where
  vanish n hn hsq h8 := by
    have : NeZero n := ⟨hn.ne'⟩
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨m, rfl⟩ := even_iff_two_dvd.mp he
      have hmodd : Odd m := by
        by_contra hc
        obtain ⟨j, rfl⟩ := Nat.not_odd_iff_even.mp hc
        exact absurd (hsq 2 ⟨j, by ring⟩) (by decide)
      have hsqm : Squarefree m := hsq.squarefree_of_dvd (dvd_mul_left m 2)
      have hs : congruentSign (2 * m) = -1 := by unfold congruentSign; exact ite_eq_left_iff.mpr (fun h ↦ absurd h8 h) |>.trans rfl
      have hfe := hH.fe m hmodd hsqm
      rw [hs] at hfe
      have hm : 0 < m := hmodd.pos
      exact lValueAtOne_zero_of_congruentFE hsq (by positivity) hfe
    · have hs : congruentSign n = -1 := by unfold congruentSign; exact ite_eq_left_iff.mpr (fun h ↦ absurd h8 h) |>.trans rfl
      have hfe := congruentFE_odd ho hsq
      rw [hs] at hfe
      exact lValueAtOne_zero_of_congruentFE hsq (by positivity) hfe

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
