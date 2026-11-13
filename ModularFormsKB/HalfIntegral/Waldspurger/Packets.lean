/-
# Waldspurger 1991: local signs, packets, and the fibres of the Shimura correspondence

Source: Waldspurger 1991 `waldspurger1991` (every locator is [unverified]: the paper was not checked).

Let $\pi$ be the cuspidal automorphic representation of $\mathrm{PGL}_2(\mathbb A)$ attached to a newform $f$ of weight $2k$.
For each place $v$ Waldspurger attaches a **local packet** $\{\sigma_v^+, \sigma_v^-\}$ of representations of the
metaplectic group $\mathrm{Mp}_2(\mathbb Q_v)$: $\sigma_v^+$ is the local theta lift of $\pi_v$ (from $\mathrm{PGL}_2 =
\mathrm{SO}(2,1)$), $\sigma_v^-$ the theta lift of the Jacquet–Langlands transfer $\pi'_v$ to the units of the division
quaternion algebra (from the anisotropic ternary space of its trace zero elements); $\sigma_v^- \ne 0$ exactly when
$\pi_v$ is a discrete series. A **sign pattern** $\varepsilon = (\varepsilon_v)_v$ ($\varepsilon_v = +1$ for almost all
$v$) gives $\sigma_\varepsilon = \bigotimes_v \sigma_v^{\varepsilon_v}$, and Waldspurger proves: $\sigma_\varepsilon$ occurs in the
space of cusp forms on $\mathrm{Mp}_2$ (with multiplicity one) iff $\prod_v\varepsilon_v = \varepsilon(\tfrac12,\pi)$.
Classical consequence: the half-integral weight forms whose Shimura lift is $f$ form a direct sum, over **admissible**
patterns, of tensor products of local fixed-vector spaces, so their dimension is
$\sum_{\varepsilon\ \mathrm{admissible}} \prod_v d_v(\varepsilon_v)$ (`LocalData.fibreDim`).

**Which square classes carry coefficients.** The $t$-th Fourier coefficient functional of $\sigma_\varepsilon$ is nonzero iff
(a) every $\sigma_v^{\varepsilon_v}$ is locally $\psi_t$-generic and (b) $L(\tfrac12, \pi\otimes\chi_t) \ne 0$. By the
local theta dichotomy (Waldspurger; Tunnell, Saito), $\sigma_v^{\varepsilon}$ is $\psi_t$-generic iff
$\varepsilon = \varepsilon_v(\pi)\,\varepsilon_v(\pi\otimes\chi_t)\,\chi_{t,v}(-1)$ (`TwistData.localSign`; the normalization
of $\psi_t$ is [unverified], see the docstring). Only the product formula `TwistData.prod_formula` is used below, and it
forces the global root number of $\pi\otimes\chi_t$ to be $+1$ on every carried square class
(`TwistData.twistRoot_eq_one_of_carries`); conversely every square class with root number $+1$ belongs to exactly one
admissible pattern (`TwistData.isAdmissible_localSign_iff`, `WaldspurgerCoefficients.carries_unique`).

**Classical instance** (odd squarefree level $N$, `classicalLocal`, `classicalTwist`): the local signs at $p \mid N$ are
the Atkin–Lehner eigenvalues $w_p$, and the square class of a fundamental discriminant $D$ prime to $N$ lies in the
pattern $\varepsilon_p = \left(\frac Dp\right)$, $\varepsilon_\infty = (-1)^k$ (`classical_localSign_some`). Kohnen's plus
space corresponds to the pattern $\varepsilon_p = w_p$ (`kohnenPattern`), which is always admissible
(`kohnenPattern_isAdmissible`) and carries $D$ iff $\left(\frac Dp\right) = w_p$ for all $p \mid N$
(`localSign_eq_kohnenPattern_iff`), Kohnen's condition; with one-dimensional local spaces on that pattern only, the fibre
is one-dimensional (`kohnen_fibreDim`).

Signs are units of $\mathbb Z$ (`ℤˣ`).
-/
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import ModularFormsKB.Citation
namespace ModularFormsKB.HalfIntegral.Waldspurger

open Finset

/-- A sign $\pm1$ read off an integer: $-1$ for $-1$, otherwise $+1$ (used for Legendre and Jacobi symbols at primes not
dividing the argument, where the symbol is $\pm 1$). -/
def signOf (x : ℤ) : ℤˣ := if x = -1 then -1 else 1

theorem signOf_neg_one : signOf (-1) = -1 := by simp [signOf]

theorem signOf_one : signOf 1 = 1 := by simp [signOf]

/-- `signOf` is the identity on $\pm 1$. -/
theorem coe_signOf {x : ℤ} (hx : x = 1 ∨ x = -1) : ((signOf x : ℤˣ) : ℤ) = x := by
  rcases hx with rfl | rfl <;> simp [signOf]

/-- **Local data of $\pi$ at a finite set of places** $\iota$ (the places where $\pi$ ramifies, and $\infty$; at all
other places $\sigma_v^- = 0$, $\varepsilon_v(\pi) = 1$ and only $\varepsilon_v = +1$ occurs).
* `discrete v`: $\pi_v$ is a discrete series (so the packet at $v$ has two members);
* `dim v ε`: the dimension of the fixed vectors of the relevant level and weight in $\sigma_v^{\varepsilon}$ (at $\infty$:
  $1$ for the member containing the holomorphic weight $k+\tfrac12$ vector, $0$ for the other);
* `rootLocal v`: the local root number $\varepsilon_v(\tfrac12, \pi_v)$. -/
structure LocalData (ι : Type*) where
  discrete : ι → Prop
  dim : ι → ℤˣ → ℕ
  dim_neg : ∀ v, ¬ discrete v → dim v (-1) = 0
  rootLocal : ι → ℤˣ

namespace LocalData

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (D : LocalData ι)

/-- The global root number $\varepsilon(\tfrac12, \pi) = \prod_v \varepsilon_v(\tfrac12,\pi_v)$. -/
def rootNumber : ℤˣ := ∏ v, D.rootLocal v

/-- **Admissible sign pattern** (Waldspurger 1991 `waldspurger1991` [unverified]): $\prod_v \varepsilon_v =
\varepsilon(\tfrac12, \pi)$. These are the patterns whose $\sigma_\varepsilon$ is automorphic. -/
def IsAdmissible (ε : ι → ℤˣ) : Prop := ∏ v, ε v = D.rootNumber

instance : DecidablePred D.IsAdmissible := fun ε ↦ inferInstanceAs (Decidable (∏ v, ε v = D.rootNumber))

/-- The finite set of admissible sign patterns. -/
def admissible : Finset (ι → ℤˣ) := univ.filter D.IsAdmissible

/-- The dimension of the fixed vectors in $\sigma_\varepsilon = \bigotimes_v\sigma_v^{\varepsilon_v}$: $\prod_v d_v(\varepsilon_v)$. -/
def componentDim (ε : ι → ℤˣ) : ℕ := ∏ v, D.dim v (ε v)

/-- **Waldspurger's dimension of the fibre** of the Shimura correspondence over $\pi$:
$\sum_{\varepsilon\ \mathrm{admissible}}\prod_v d_v(\varepsilon_v)$. -/
def fibreDim : ℕ := ∑ ε ∈ D.admissible, D.componentDim ε

/-- The places where a pattern takes the value $-1$ (for an admissible pattern with $\varepsilon(\tfrac12,\pi) = +1$, the
ramification set of the quaternion algebra from whose units $\sigma_\varepsilon$ is a theta lift). -/
def negSet (ε : ι → ℤˣ) : Finset ι := univ.filter (fun v ↦ ε v = -1)

theorem prod_eq_neg_one_pow (ε : ι → ℤˣ) : ∏ v, ε v = (-1) ^ (negSet ε).card := by
  have h : ∀ v, ε v = if ε v = -1 then -1 else 1 := by
    intro v
    rcases Int.units_eq_one_or (ε v) with h | h <;> simp [h]
  conv_lhs => rw [Finset.prod_congr rfl (fun v _ ↦ h v)]
  rw [Finset.prod_ite]
  simp [negSet]

/-- **Hilbert-reciprocity parity:** when $\varepsilon(\tfrac12,\pi) = +1$, a pattern is admissible iff it is $-1$ at an even
number of places, i.e. iff its $-1$ places are the ramification set of a quaternion algebra over $\mathbb Q$. -/
theorem isAdmissible_iff_even (h : D.rootNumber = 1) (ε : ι → ℤˣ) :
    D.IsAdmissible ε ↔ Even (negSet ε).card := by
  rw [IsAdmissible, h, prod_eq_neg_one_pow]
  exact neg_one_pow_eq_one_iff_even (by decide)

/-- **Half of all patterns are admissible:** $2^{|\iota| - 1}$ of them, when $\iota \ne \emptyset$. -/
theorem card_admissible [Nonempty ι] : D.admissible.card = 2 ^ (Fintype.card ι - 1) := by
  obtain ⟨i0⟩ := ‹Nonempty ι›
  let f : (ι → ℤˣ) → (ι → ℤˣ) := fun ε ↦ Function.update ε i0 (-ε i0)
  have hprod : ∀ ε, ∏ v, f ε v = -∏ v, ε v := by
    intro ε
    simp only [f]
    rw [Finset.prod_update_of_mem (Finset.mem_univ _), ← Finset.mul_prod_erase univ ε (Finset.mem_univ i0),
      Finset.sdiff_singleton_eq_erase]
    simp
  have hff : ∀ ε, f (f ε) = ε := by
    intro ε
    funext v
    by_cases hv : v = i0
    · subst hv; simp [f]
    · simp [f, hv]
  have hne : ∀ x : ℤˣ, -x ≠ x := by
    intro x
    rcases Int.units_eq_one_or x with h | h <;> simp [h]
  have hcard : D.admissible.card = (univ.filter (fun ε ↦ ¬ D.IsAdmissible ε)).card := by
    refine Finset.card_nbij' f f ?_ ?_ (fun ε _ ↦ hff ε) (fun ε _ ↦ hff ε)
    · intro ε hε
      simp only [admissible, coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hε ⊢
      rw [IsAdmissible] at hε ⊢
      rw [hprod, hε]
      exact hne _
    · intro ε hε
      simp only [admissible, coe_filter, Set.mem_setOf_eq, mem_univ, true_and, IsAdmissible] at hε ⊢
      rw [hprod]
      rcases Int.units_eq_one_or D.rootNumber with h | h <;>
      rcases Int.units_eq_one_or (∏ v, ε v) with h' | h' <;> simp_all
  have hsum := Finset.card_filter_add_card_filter_not (s := (univ : Finset (ι → ℤˣ))) D.IsAdmissible
  have hu : (univ : Finset (ι → ℤˣ)).card = 2 ^ Fintype.card ι := by
    simp
  have : D.admissible = univ.filter D.IsAdmissible := rfl
  have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i0⟩
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card ι = n + 1 := ⟨Fintype.card ι - 1, by omega⟩
  rw [hn] at hu ⊢
  rw [pow_succ] at hu
  rw [← this] at hsum
  simp only [Nat.add_sub_cancel]
  omega

/-- **Closed form of the fibre dimension:**
$2\dim = \prod_v (d_v^+ + d_v^-) + \varepsilon(\tfrac12,\pi)\prod_v(d_v^+ - d_v^-)$. -/
theorem two_mul_fibreDim :
    2 * (D.fibreDim : ℤ) = ∏ v, ((D.dim v 1 : ℤ) + D.dim v (-1)) +
      (D.rootNumber : ℤ) * ∏ v, ((D.dim v 1 : ℤ) - D.dim v (-1)) := by
  have hind : ∀ ε : ι → ℤˣ, (2 * (if D.IsAdmissible ε then 1 else 0) : ℤ) =
      1 + (D.rootNumber : ℤ) * ((∏ v, ε v : ℤˣ) : ℤ) := by
    intro ε
    unfold IsAdmissible
    rcases Int.units_eq_one_or D.rootNumber with h | h <;>
    rcases Int.units_eq_one_or (∏ v, ε v) with h' | h' <;> simp [h, h']
  have h1 : 2 * (D.fibreDim : ℤ) = ∑ ε : ι → ℤˣ,
      (1 + (D.rootNumber : ℤ) * ((∏ v, ε v : ℤˣ) : ℤ)) * (D.componentDim ε : ℤ) := by
    unfold fibreDim admissible
    rw [Finset.sum_filter]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ε _ ↦ ?_
    have := hind ε
    rw [Units.coe_prod] at this
    rw [← this]
    split_ifs <;> simp
  have hexp : ∀ g : ι → ℤˣ → ℤ, ∑ ε : ι → ℤˣ, ∏ v, g v (ε v) = ∏ v, (g v 1 + g v (-1)) := by
    intro g
    have hU : (univ : Finset ℤˣ) = {1, -1} := by decide
    have := Finset.prod_univ_sum (fun v ↦ (univ : Finset ℤˣ)) g
    simp only [hU, Finset.sum_pair (show (1 : ℤˣ) ≠ -1 by decide)] at this
    rw [this, ← hU]
    rfl
  rw [h1]
  simp only [add_mul, Finset.sum_add_distrib, one_mul, mul_assoc, ← Finset.mul_sum]
  congr 1
  · have := hexp (fun v u ↦ (D.dim v u : ℤ))
    simpa [componentDim] using this
  · congr 1
    have := hexp (fun v u ↦ (u : ℤ) * (D.dim v u : ℤ))
    simp only [Units.val_one, Units.val_neg, one_mul, neg_mul, ← sub_eq_add_neg] at this
    rw [← this]
    refine Finset.sum_congr rfl fun ε _ ↦ ?_
    simp [componentDim, Finset.prod_mul_distrib]

/-- **No discrete series places:** only the pattern $+1$ contributes, and it is admissible iff $\varepsilon(\tfrac12,\pi) = 1$. -/
theorem fibreDim_of_not_discrete (h : ∀ v, ¬ D.discrete v) :
    D.fibreDim = if D.rootNumber = 1 then ∏ v, D.dim v 1 else 0 := by
  have hz : ∀ ε : ι → ℤˣ, ε ≠ 1 → D.componentDim ε = 0 := by
    intro ε hε
    obtain ⟨v, hv⟩ : ∃ v, ε v ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hε (funext hcon)
    have hv' : ε v = -1 := (Int.units_eq_one_or (ε v)).resolve_left hv
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hv']; exact D.dim_neg v (h v))
  unfold fibreDim
  split_ifs with hr
  · rw [Finset.sum_eq_single (1 : ι → ℤˣ)]
    · rfl
    · intro b _ hb; exact hz b hb
    · intro h1
      exfalso; apply h1
      simp [admissible, IsAdmissible, hr]
  · apply Finset.sum_eq_zero
    intro ε hε
    apply hz
    rintro rfl
    simp [admissible, IsAdmissible] at hε
    exact hr hε.symm

/-- **Multiplicity one:** if at every place at most one member of the packet has fixed vectors, and then at most a line,
the fibre has dimension at most one. -/
theorem fibreDim_le_one (h : ∀ v, D.dim v 1 + D.dim v (-1) ≤ 1) : D.fibreDim ≤ 1 := by
  have hle : ∀ ε : ι → ℤˣ, D.componentDim ε ≤ 1 := by
    intro ε
    refine Finset.prod_le_one fun v _ ↦ ?_
    have := h v
    rcases Int.units_eq_one_or (ε v) with e | e <;> rw [e] <;> omega
  have huniq : ∀ ε ε' : ι → ℤˣ, D.componentDim ε ≠ 0 → D.componentDim ε' ≠ 0 → ε = ε' := by
    intro ε ε' h1 h2
    funext v
    have a1 : D.dim v (ε v) ≠ 0 := fun h0 ↦ h1 (Finset.prod_eq_zero (Finset.mem_univ v) h0)
    have a2 : D.dim v (ε' v) ≠ 0 := fun h0 ↦ h2 (Finset.prod_eq_zero (Finset.mem_univ v) h0)
    have := h v
    rcases Int.units_eq_one_or (ε v) with e | e <;> rcases Int.units_eq_one_or (ε' v) with e' | e' <;>
      rw [e] at a1 <;> rw [e'] at a2 <;> first | (exfalso; omega) | rw [e, e']
  unfold fibreDim
  by_cases hex : ∃ ε ∈ D.admissible, D.componentDim ε ≠ 0
  · obtain ⟨ε0, hmem, hε0⟩ := hex
    rw [Finset.sum_eq_single ε0]
    · exact hle ε0
    · intro b _ hb
      by_contra hc
      exact hb (huniq b ε0 hc hε0)
    · intro hn; exact absurd hmem hn
  · push_neg at hex
    rw [Finset.sum_eq_zero (fun ε hε ↦ hex ε hε)]
    exact Nat.zero_le _

end LocalData

/-- **Twisting data** for a type $T$ of square classes $t$ (Waldspurger 1991 `waldspurger1991` [unverified]):
* `twistLocal t v` $= \varepsilon_v(\tfrac12, \pi_v\otimes\chi_{t,v})$ and `charSign t v` $= \chi_{t,v}(-1)$ for $v \in \iota$;
* `twistRoot t` $= \varepsilon(\tfrac12, \pi\otimes\chi_t)$;
* `prod_formula`: $\prod_{v\in\iota}\varepsilon_v(\pi\otimes\chi_t)\chi_{t,v}(-1) = \varepsilon(\tfrac12,\pi\otimes\chi_t)$. This is the product
  of local root numbers over all places, since at a place $v \notin \iota$ ($\pi_v$ unramified principal series
  $\mu\boxplus\mu^{-1}$) one has $\varepsilon_v(\pi_v\otimes\chi_t) = \chi_{t,v}(-1)$, and $\prod_v \chi_{t,v}(-1) = 1$. -/
structure TwistData {ι : Type*} [Fintype ι] (D : LocalData ι) (T : Type*) where
  twistLocal : T → ι → ℤˣ
  charSign : T → ι → ℤˣ
  twistRoot : T → ℤˣ
  prod_formula : ∀ t, ∏ v, twistLocal t v * charSign t v = twistRoot t

namespace TwistData

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : LocalData ι} {T : Type*} (X : TwistData D T)

/-- **The local sign selected by the square class $t$** at $v$: $\varepsilon_v(\pi)\,\varepsilon_v(\pi\otimes\chi_t)\,\chi_{t,v}(-1)$.
By the local theta dichotomy (Waldspurger 1991; Tunnell 1983 `tunnell1983` and Saito for the toric form
[unverified]) the member $\sigma_v^{\varepsilon}$ of the packet admits a $\psi_t$-Whittaker functional iff $\varepsilon$ equals
this sign. (Conventions differ in the literature on whether $\psi_t$ or $\psi_{-t}$ is used; only the product formula
`prod_localSign` enters the proofs below.) -/
def localSign (t : T) (v : ι) : ℤˣ := D.rootLocal v * X.twistLocal t v * X.charSign t v

/-- $\prod_v(\text{local sign of } t) = \varepsilon(\tfrac12,\pi)\,\varepsilon(\tfrac12,\pi\otimes\chi_t)$. -/
theorem prod_localSign (t : T) : ∏ v, X.localSign t v = D.rootNumber * X.twistRoot t := by
  have : ∀ v, X.localSign t v = D.rootLocal v * (X.twistLocal t v * X.charSign t v) := fun v ↦ by
    simp [localSign, mul_assoc]
  simp_rw [this]
  rw [Finset.prod_mul_distrib, X.prod_formula t]
  rfl

/-- **The pattern selected by $t$ is admissible iff $\varepsilon(\tfrac12, \pi\otimes\chi_t) = +1$.** -/
theorem isAdmissible_localSign_iff (t : T) : D.IsAdmissible (X.localSign t) ↔ X.twistRoot t = 1 := by
  rw [LocalData.IsAdmissible, prod_localSign]
  constructor
  · intro h
    exact mul_left_cancel (h.trans (mul_one _).symm)
  · intro h
    rw [h, mul_one]

end TwistData

/-- **Waldspurger's coefficient theorem, packet form** (Waldspurger 1991 `waldspurger1991`, main theorem
[unverified]): for an admissible pattern $\varepsilon$, the automorphic $\sigma_\varepsilon$ has a nonzero $t$-th Fourier
coefficient (`carries ε t`) iff $\varepsilon$ is the pattern selected by $t$ (local genericity everywhere) and
$L(\tfrac12,\pi\otimes\chi_t) \ne 0$ (`centralNonzero t`). -/
@[kb "waldspurger1991" "main theorem: the t-th coefficient of σ_ε is nonzero iff ε = local signs of t and L(1/2, π ⊗ χ_t) ≠ 0 [unverified]"]
structure WaldspurgerCoefficients {ι : Type*} [Fintype ι] {D : LocalData ι} {T : Type*} (X : TwistData D T)
    (carries : (ι → ℤˣ) → T → Prop) (centralNonzero : T → Prop) : Prop where
  carries_iff : ∀ ε, D.IsAdmissible ε → ∀ t, carries ε t ↔ (ε = X.localSign t ∧ centralNonzero t)

namespace WaldspurgerCoefficients

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : LocalData ι} {T : Type*} {X : TwistData D T}
  {carries : (ι → ℤˣ) → T → Prop} {centralNonzero : T → Prop}

/-- **A carried square class has root number $+1$:** if an admissible $\sigma_\varepsilon$ has a nonzero $t$-th coefficient,
then $\varepsilon(\tfrac12,\pi\otimes\chi_t) = +1$ (consistent with $L(\tfrac12,\pi\otimes\chi_t) \ne 0$). -/
theorem twistRoot_eq_one (h : WaldspurgerCoefficients X carries centralNonzero) {ε : ι → ℤˣ}
    (hε : D.IsAdmissible ε) {t : T} (ht : carries ε t) : X.twistRoot t = 1 := by
  obtain ⟨he, _⟩ := (h.carries_iff ε hε t).1 ht
  rw [he] at hε
  exact (X.isAdmissible_localSign_iff t).1 hε

/-- **Each square class is carried by at most one admissible pattern.** -/
theorem carries_unique (h : WaldspurgerCoefficients X carries centralNonzero) {ε ε' : ι → ℤˣ}
    (hε : D.IsAdmissible ε) (hε' : D.IsAdmissible ε') {t : T} (ht : carries ε t) (ht' : carries ε' t) : ε = ε' := by
  rw [((h.carries_iff ε hε t).1 ht).1, ((h.carries_iff ε' hε' t).1 ht').1]

/-- **Square classes with root number $-1$ are carried by no admissible pattern.** -/
theorem not_carries_of_twistRoot (h : WaldspurgerCoefficients X carries centralNonzero) {t : T}
    (ht : X.twistRoot t = -1) {ε : ι → ℤˣ} (hε : D.IsAdmissible ε) : ¬ carries ε t := by
  intro hc
  have := h.twistRoot_eq_one hε hc
  rw [ht] at this
  exact absurd this (by decide)

/-- **Square classes with root number $+1$ and nonvanishing central value are carried by exactly the selected pattern.** -/
theorem carries_localSign (h : WaldspurgerCoefficients X carries centralNonzero) {t : T}
    (ht : X.twistRoot t = 1) (hL : centralNonzero t) : carries (X.localSign t) t := by
  have hadm : D.IsAdmissible (X.localSign t) := (X.isAdmissible_localSign_iff t).2 ht
  exact (h.carries_iff _ hadm t).2 ⟨rfl, hL⟩

end WaldspurgerCoefficients

/-! ## The classical instance: odd squarefree level -/

section Classical

variable (k N : ℕ)

/-- **Places for squarefree level $N$:** `none` is $\infty$, `some p` a prime $p \mid N$. -/
abbrev Places := Option N.primeFactors

/-- **Local data of a newform of weight $2k$ and squarefree level $N$** with Atkin–Lehner eigenvalues $w_p$: at $p \mid N$,
$\pi_p$ is an unramified twist of the Steinberg representation, with $\varepsilon_p(\tfrac12,\pi_p) = w_p$ [unverified
normalization: $b(p) = -w_p\,p^{k-1}$]; at $\infty$, $\pi_\infty$ is the discrete series of weight $2k$, with
$\varepsilon_\infty = i^{2k} = (-1)^k$, and the holomorphic weight $k + \tfrac12$ vector lies in $\sigma_\infty^{(-1)^k}$
(`dim` at $\infty$). Every place in $\iota$ is a discrete series place. `dimFin p ε` is the local fixed-vector dimension
at $p$, left as data. -/
def classicalLocal (w : N.primeFactors → ℤˣ) (dimFin : N.primeFactors → ℤˣ → ℕ) : LocalData (Places N) where
  discrete _ := True
  dim v ε := match v with
    | none => if ε = (-1) ^ k then 1 else 0
    | some p => dimFin p ε
  dim_neg _ h := absurd trivial h
  rootLocal v := match v with
    | none => (-1) ^ k
    | some p => w p

/-- The global root number in the classical instance: $\varepsilon(f) = (-1)^k\prod_{p\mid N} w_p$. -/
theorem classical_rootNumber (w : N.primeFactors → ℤˣ) (dimFin : N.primeFactors → ℤˣ → ℕ) :
    (classicalLocal k N w dimFin).rootNumber = (-1) ^ k * ∏ p : N.primeFactors, w p := by
  simp [LocalData.rootNumber, classicalLocal, Fintype.prod_option]

/-- **Fundamental discriminants prime to $N$ with $(-1)^k D > 0$**, the square classes of the classical theory. -/
def ClassicalClasses : Type :=
  {D : ℤ // 0 < (-1) ^ k * D ∧ IsCoprime D N}

/-- **Twisting data in the classical instance:** for $D$ prime to $N$, $\varepsilon_p(\pi\otimes\chi_D) = w_p\left(\frac Dp\right)$,
$\chi_{D,p}(-1) = 1$ ($\chi_D$ unramified at $p$), $\varepsilon_\infty(\pi\otimes\chi_D) = (-1)^k$, $\chi_{D,\infty}(-1) =
\operatorname{sign} D$, and $\varepsilon(\tfrac12,\pi\otimes\chi_D) = \varepsilon(f)\chi_D(-N) = (-1)^k\prod_p w_p\cdot\operatorname{sign}D
\prod_p\left(\frac Dp\right)$ (the classical twisting formula for the root number, $\gcd(D, N) = 1$ [unverified]). -/
def classicalTwist (w : N.primeFactors → ℤˣ) (dimFin : N.primeFactors → ℤˣ → ℕ) :
    TwistData (classicalLocal k N w dimFin) (ClassicalClasses k N) where
  twistLocal D v := match v with
    | none => (-1) ^ k
    | some p => w p * signOf (jacobiSym D.1 p)
  charSign D v := match v with
    | none => signOf (Int.sign D.1)
    | some _ => 1
  twistRoot D := (-1) ^ k * (∏ p : N.primeFactors, w p) * signOf (Int.sign D.1) * ∏ p : N.primeFactors, signOf (jacobiSym D.1 p)
  prod_formula D := by
    rw [Fintype.prod_option]
    simp only [mul_one, Finset.prod_mul_distrib]
    ac_rfl

/-- At $p \mid N$ the local sign selected by $D$ is the Legendre symbol $\left(\frac Dp\right)$. -/
theorem classical_localSign_some (w : N.primeFactors → ℤˣ) (dimFin : N.primeFactors → ℤˣ → ℕ)
    (D : ClassicalClasses k N) (p : N.primeFactors) :
    (classicalTwist k N w dimFin).localSign D (some p) = signOf (jacobiSym D.1 p) := by
  show w p * (w p * signOf (jacobiSym D.1 p)) * 1 = _
  rw [mul_one, ← mul_assoc, Int.units_mul_self, one_mul]

/-- At $\infty$ the local sign selected by $D$ is $\operatorname{sign} D = (-1)^k$. -/
theorem classical_localSign_none (w : N.primeFactors → ℤˣ) (dimFin : N.primeFactors → ℤˣ → ℕ)
    (D : ClassicalClasses k N) :
    (classicalTwist k N w dimFin).localSign D none = (-1) ^ k := by
  have key : ∀ d : ℤ, 0 < (-1 : ℤ) ^ k * d → signOf (Int.sign d) = (-1) ^ k := by
    intro d h
    rcases Nat.even_or_odd k with he | ho
    · rw [he.neg_one_pow] at h
      rw [he.neg_one_pow]
      have : 0 < d := by simpa using h
      rw [Int.sign_eq_one_of_pos this]; simp [signOf]
    · rw [ho.neg_one_pow] at h
      rw [ho.neg_one_pow]
      have : d < 0 := by simpa using h
      rw [Int.sign_eq_neg_one_of_neg this]; simp [signOf]
  have hs : signOf (Int.sign D.1) = (-1) ^ k := key D.1 D.2.1
  show (-1) ^ k * (-1) ^ k * signOf (Int.sign D.1) = _
  rw [hs, Int.units_mul_self, one_mul]

/-- **Kohnen's pattern:** $\varepsilon_p = w_p$ at $p \mid N$, $\varepsilon_\infty = (-1)^k$. -/
def kohnenPattern (w : N.primeFactors → ℤˣ) : Places N → ℤˣ
  | none => (-1) ^ k
  | some p => w p

/-- Kohnen's pattern is admissible for every newform. -/
theorem kohnenPattern_isAdmissible (w : N.primeFactors → ℤˣ) (dimFin : N.primeFactors → ℤˣ → ℕ) :
    (classicalLocal k N w dimFin).IsAdmissible (kohnenPattern k N w) := by
  unfold LocalData.IsAdmissible
  rw [classical_rootNumber, Fintype.prod_option]
  rfl

/-- **Kohnen's condition:** $D$ lies in Kohnen's pattern iff $\left(\frac Dp\right) = w_p$ for every $p \mid N$. -/
theorem localSign_eq_kohnenPattern_iff (w : N.primeFactors → ℤˣ) (dimFin : N.primeFactors → ℤˣ → ℕ)
    (D : ClassicalClasses k N) :
    (classicalTwist k N w dimFin).localSign D = kohnenPattern k N w ↔
      ∀ p : N.primeFactors, signOf (jacobiSym D.1 p) = w p := by
  constructor
  · intro h p
    have := congrFun h (some p)
    rw [classical_localSign_some] at this
    exact this
  · intro h
    funext v
    cases v with
    | none => exact classical_localSign_none k N w dimFin D
    | some p => rw [classical_localSign_some]; exact h p

/-- **The plus space is one-dimensional over $f$:** if the local fixed vectors are a line in $\sigma_p^{w_p}$ and zero in
$\sigma_p^{-w_p}$ at each $p \mid N$ (Kohnen's plus condition, as local input), the fibre dimension is $1$. -/
theorem kohnen_fibreDim (w : N.primeFactors → ℤˣ) :
    (classicalLocal k N w (fun p ε ↦ if ε = w p then 1 else 0)).fibreDim = 1 := by
  set D' := classicalLocal k N w (fun p ε ↦ if ε = w p then 1 else 0) with hD'
  have h := D'.two_mul_fibreDim
  have e1 : ∀ v, ((D'.dim v 1 : ℕ) : ℤ) + (D'.dim v (-1) : ℕ) = 1 := by
    intro v
    cases v with
    | none => rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ k) with h | h <;> simp [hD', classicalLocal, h]
    | some p => rcases Int.units_eq_one_or (w p) with h | h <;> simp [hD', classicalLocal, h]
  have e2 : ∀ v, ((D'.dim v 1 : ℕ) : ℤ) - (D'.dim v (-1) : ℕ) = (D'.rootLocal v : ℤ) := by
    intro v
    cases v with
    | none => rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ k) with h | h <;> simp [hD', classicalLocal, h]
    | some p => rcases Int.units_eq_one_or (w p) with h | h <;> simp [hD', classicalLocal, h]
  simp only [e1, e2] at h
  have hr : ∏ v, ((D'.rootLocal v : ℤˣ) : ℤ) = (D'.rootNumber : ℤ) := (Units.coe_prod _ _).symm
  rw [hr, ← Units.val_mul, Int.units_mul_self] at h
  simp at h
  omega

end Classical

end ModularFormsKB.HalfIntegral.Waldspurger
