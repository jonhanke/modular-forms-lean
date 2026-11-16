/-
# Waldspurger 1981 for every squarefree $n$, and Kohnen 1985 with the Petersson quotient

Loose ends LE-MF-0172, LE-MF-0174. Sources: Waldspurger 1981 `waldspurger1981`, Corollaire 2; Kohnen 1985 `kohnen1985`,
Theorem 1 and its Corollary. The papers could not be consulted: the placement of the factor
$\chi(n_2/n_1)$ and the normalization of the Petersson products follow the usual citations [unverified].

**Waldspurger's theorem on square classes for all squarefree $n$** (`WaldspurgerSquareClassFull`). The named
input `WaldspurgerSquareClass` of `Coefficients.lean` asks $n_1, n_2$ prime to $4N$ and omits Waldspurger's factor. Here
$n_1, n_2 \ge 1$ are any squarefree numbers in one square class at the primes dividing $4N$ (`SameSquareClass`), and
$$ c(n_1)^2\,L(F,\chi'_{n_2},k)\,\chi(n_2/n_1)\,n_2^{k-1/2} = c(n_2)^2\,L(F,\chi'_{n_1},k)\,n_1^{k-1/2}. $$
On a square class $n_1/n_2$ is a unit at every $p \mid 4N$, so $\chi(n_2/n_1) = \chi(n_2/g)\,\chi(n_1/g)^{-1}$ with
$g = \gcd(n_1, n_2)$ is defined (`squareClassFactor`). Even $n$ are allowed, which Tunnell's criterion needs at level
128.
Proved:
- `coprime_div_gcd_of_sameSquareClass`: on a square class, $n_1/g$ and $n_2/g$ are prime to $4N$;
- `isSquare_zmod_of_forall_isSquare_padic`: a number prime to $4N$ that is a square in $\mathbb Q_p$ for every
  $p \mid 4N$ is a square modulo $4N$;
- `squareClassFactor_eq_one`: for quadratic $\chi$ the factor is $1$ on every square class;
- `WaldspurgerSquareClassFull.toWaldspurgerSquareClass`: the full statement implies the prime-to-$4N$ input, so the
  consequences `exists_constant` and `coeff_eq_zero_iff` of `Coefficients.lean` follow from it.

**Kohnen's formula with the Petersson quotient** (`KohnenSquarefreePetersson`). The named input
`KohnenSquarefree` replaces $\langle g,g\rangle/\langle f,f\rangle$ by an unspecified constant $\kappa > 0$. Here
$\langle g, g\rangle$ is `peterssonLevel k N g g` (normalized by $[\mathrm{SL}_2(\mathbb Z):\Gamma_0(4N)]^{-1}$)
and $\langle f, f\rangle$ is Tau Ceti's `peterssonInnerCosets f f` on $\Gamma_0(N)$ divided by
$[\mathrm{SL}_2(\mathbb Z):\Gamma_0(N)]$ (`peterssonNormalized`):
$$\frac{|c(|D|)|^2}{\langle g,g\rangle} = 2^{\nu(N)}\frac{(k-1)!}{\pi^k}|D|^{k-1/2}\frac{L(f,D,k)}{\langle f,f\rangle}.$$
Proved: `KohnenSquarefreePetersson.toKohnenSquarefree`, the old input with $\kappa = \langle g,g\rangle/\langle f,f\rangle$,
positive by the definiteness of both products (`MultiplierSystem.peterssonLevel_self_re_pos` and Tau Ceti
`peterssonInnerCosets_self_eq_zero`).
-/
import ModularFormsKB.HalfIntegral.Waldspurger.Coefficients
import ModularFormsKB.HalfIntegral.Abstract.PeterssonLevel
import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.ModularForms.Petersson.FiniteIndex

namespace ModularFormsKB.HalfIntegral.Waldspurger

open Complex MatrixGroups CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-! ## Row 26: Waldspurger 1981 for every squarefree `n` -/

/-- **Waldspurger's factor** $\chi(n_2/n_1) = \chi(n_2/g)\,\chi(n_1/g)^{-1}$, $g = \gcd(n_1, n_2)$. On a square class
both quotients are prime to $4N$ (`coprime_div_gcd_of_sameSquareClass`). -/
noncomputable def squareClassFactor (N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (n₁ n₂ : ℕ) : ℂ :=
  χ ((n₂ / Nat.gcd n₁ n₂ : ℕ) : ZMod (4 * N)) * (χ ((n₁ / Nat.gcd n₁ n₂ : ℕ) : ZMod (4 * N)))⁻¹

/-- **Waldspurger's theorem on square classes, for all squarefree $n$** (Waldspurger 1981 `waldspurger1981`,
Corollaire 2 [unverified]), for quadratic $\chi$: for squarefree $n_1, n_2 \ge 1$ in one square class at the primes
dividing $4N$,
$c(n_1)^2 L(F,\chi'_{n_2},k)\,\chi(n_2/n_1)\,n_2^{k-1/2} = c(n_2)^2 L(F,\chi'_{n_1},k)\,n_1^{k-1/2}$, with
$L(F,\chi'_n,\cdot)$ any entire continuation of $\sum \chi'_n(d)b(d)d^{-s}$ from $\operatorname{Re}s > k+1$. -/
@[kb "waldspurger1981" "Cor. 2: c(n₁)² L(F,χ'_{n₂},k) χ(n₂/n₁) n₂^{k-1/2} = c(n₂)² L(F,χ'_{n₁},k) n₁^{k-1/2} for squarefree n₁, n₂ in one square class [unverified]"]
structure WaldspurgerSquareClassFull (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop where
  ratio : 1 ≤ k → χ ^ 2 = 1 → ∀ (g : ℍ → ℂ) (c : ℕ → ℂ) (F : ℍ → ℂ) (b : ℕ → ℂ), LiftsTo M k N χ g c F b →
    ∀ n₁ n₂ : ℕ, 1 ≤ n₁ → 1 ≤ n₂ → Squarefree n₁ → Squarefree n₂ → SameSquareClass N n₁ n₂ →
      ∀ L₁ L₂ : ℂ → ℂ, IsEntireLSeries (shimuraTwistCoeff k N χ n₁ b) ((k : ℝ) + 1) L₁ →
        IsEntireLSeries (shimuraTwistCoeff k N χ n₂ b) ((k : ℝ) + 1) L₂ →
        c n₁ ^ 2 * L₂ k * squareClassFactor N χ n₁ n₂ * ((n₂ : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) =
          c n₂ ^ 2 * L₁ k * ((n₁ : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ)

private theorem valuation_natCast' (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (n : ℚ_[p]).valuation = multiplicity p n := by
  rw [Padic.valuation_natCast]

private theorem padicValNat_le_one_of_squarefree {p n : ℕ} [Fact p.Prime] (hn : 1 ≤ n) (hs : Squarefree n) :
    multiplicity p n ≤ 1 := by
  by_contra h
  have h2 : p ^ 2 ∣ n := (multiplicity_dvd_iff_le (by omega)).2 (by omega)
  have := hs p (by simpa [sq] using h2)
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.isUnit_iff.mp this)

/-- If $n_1n_2$ is a $p$-adic square (both squarefree, positive), $p \mid n_1$ implies $p \mid n_2$. -/
private theorem dvd_of_isSquare_padic {p n₁ n₂ : ℕ} [Fact p.Prime] (h₁ : 1 ≤ n₁) (h₂ : 1 ≤ n₂)
    (hs₁ : Squarefree n₁) (hs₂ : Squarefree n₂) (hsq : IsSquare (((n₁ * n₂ : ℕ) : ℚ_[p]))) (hd : p ∣ n₁) :
    p ∣ n₂ := by
  obtain ⟨y, hy⟩ := hsq
  have hne : ((n₁ * n₂ : ℕ) : ℚ_[p]) ≠ 0 := by
    have : n₁ * n₂ ≠ 0 := by positivity
    exact_mod_cast this
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hy)
  have hv := valuation_natCast' p (n₁ * n₂)
  rw [hy, Padic.valuation_mul hy0 hy0] at hv
  rw [Nat.multiplicity_mul (by omega) (by omega)] at hv
  have ha := padicValNat_le_one_of_squarefree (p := p) h₁ hs₁
  have hb := padicValNat_le_one_of_squarefree (p := p) h₂ hs₂
  have ha1 : 1 ≤ multiplicity p n₁ := one_le_multiplicity_of_dvd (by omega) hd
  have : 1 ≤ multiplicity p n₂ := by omega
  exact dvd_of_one_le_multiplicity this

private theorem not_dvd_div_gcd {p n₁ n₂ : ℕ} (hp : p.Prime) (hs₁ : Squarefree n₁) (hd₁ : p ∣ n₁)
    (hd₂ : p ∣ n₂) : ¬ p ∣ n₁ / Nat.gcd n₁ n₂ := by
  intro h
  have hg : p ∣ Nat.gcd n₁ n₂ := Nat.dvd_gcd hd₁ hd₂
  have h2 : p * p ∣ n₁ := by
    have := mul_dvd_mul h hg
    rwa [Nat.div_mul_cancel (Nat.gcd_dvd_left n₁ n₂)] at this
  exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hs₁ p h2))

/-- **On a square class the quotients by the greatest common divisor are prime to $4N$**: for squarefree
$n_1, n_2 \ge 1$ with $n_1 n_2$ a square in $\mathbb Q_p$ for every $p \mid 4N$, a prime $p \mid 4N$ divides $n_1$
exactly when it divides $n_2$, and then only once. -/
theorem coprime_div_gcd_of_sameSquareClass {N n₁ n₂ : ℕ} (h₁ : 1 ≤ n₁) (h₂ : 1 ≤ n₂) (hs₁ : Squarefree n₁)
    (hs₂ : Squarefree n₂) (hcl : SameSquareClass N n₁ n₂) :
    Nat.Coprime (n₁ / Nat.gcd n₁ n₂) (4 * N) ∧ Nat.Coprime (n₂ / Nat.gcd n₁ n₂) (4 * N) := by
  constructor
  · refine Nat.coprime_of_dvd fun p hp hpa hpN ↦ ?_
    haveI := Fact.mk hp
    have hd₁ : p ∣ n₁ := hpa.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n₁ n₂))
    have hd₂ := dvd_of_isSquare_padic h₁ h₂ hs₁ hs₂ (hcl p hpN) hd₁
    exact not_dvd_div_gcd hp hs₁ hd₁ hd₂ hpa
  · refine Nat.coprime_of_dvd fun p hp hpa hpN ↦ ?_
    haveI := Fact.mk hp
    rw [Nat.gcd_comm] at hpa
    have hd₂ : p ∣ n₂ := hpa.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n₂ n₁))
    have hsq : IsSquare (((n₂ * n₁ : ℕ) : ℚ_[p])) := by rw [mul_comm]; exact hcl p hpN
    have hd₁ := dvd_of_isSquare_padic h₂ h₁ hs₂ hs₁ hsq hd₂
    exact not_dvd_div_gcd hp hs₂ hd₂ hd₁ hpa

/-- **A $p$-adic square at every $p \mid m$ is a square modulo $m$**, for $x$ prime to $m$ ($m \ge 1$). -/
theorem isSquare_zmod_of_forall_isSquare_padic {m x : ℕ} (hm : 1 ≤ m) (hx : Nat.Coprime x m)
    (h : ∀ (p : ℕ) [Fact p.Prime], p ∣ m → IsSquare ((x : ℚ_[p]))) : IsSquare (x : ZMod m) := by
  induction m using Nat.recOnPosPrimePosCoprime generalizing x with
  | prime_pow p n hp hn =>
    haveI := Fact.mk hp
    obtain ⟨y, hy⟩ := h p (dvd_pow_self p hn.ne')
    have hxp : ¬ p ∣ x := fun hd ↦ by
      have := Nat.Coprime.coprime_dvd_right (dvd_pow_self p hn.ne') hx
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 this.symm hd
    have hnorm : ‖(x : ℚ_[p])‖ = 1 := Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hxp)
    have hyy : ‖y‖ * ‖y‖ = 1 := by rw [← norm_mul, ← hy, hnorm]
    have hy1 : ‖y‖ ≤ 1 := by nlinarith [norm_nonneg y]
    let z : PadicInt p := ⟨y, hy1⟩
    have hz : z * z = (x : PadicInt p) := Subtype.ext (by
      simp only [PadicInt.coe_mul, PadicInt.coe_natCast]
      exact hy.symm)
    exact ⟨PadicInt.toZModPow n z, by rw [← map_mul, hz, map_natCast]⟩
  | zero => omega
  | one => exact ⟨0, Subsingleton.elim _ _⟩
  | coprime a b ha hb hab iha ihb =>
    have hxa : Nat.Coprime x a := (Nat.coprime_mul_iff_right.1 hx).1
    have hxb : Nat.Coprime x b := (Nat.coprime_mul_iff_right.1 hx).2
    obtain ⟨s, hs⟩ := iha (by omega) hxa fun p _ hp ↦ h p (hp.trans (dvd_mul_right a b))
    obtain ⟨t, ht⟩ := ihb (by omega) hxb fun p _ hp ↦ h p (hp.trans (dvd_mul_left b a))
    let e := ZMod.chineseRemainder hab
    refine ⟨e.symm (s, t), e.injective ?_⟩
    rw [map_mul, map_natCast, RingEquiv.apply_symm_apply]
    exact Prod.ext (by simp [hs]) (by simp [ht])

/-- **For quadratic $\chi$ Waldspurger's factor is $1$ on every square class.** -/
theorem squareClassFactor_eq_one {N : ℕ} {χ : DirichletCharacter ℂ (4 * N)} (hχ : χ ^ 2 = 1) {n₁ n₂ : ℕ}
    (h₁ : 1 ≤ n₁) (h₂ : 1 ≤ n₂) (hs₁ : Squarefree n₁) (hs₂ : Squarefree n₂) (hcl : SameSquareClass N n₁ n₂) :
    squareClassFactor N χ n₁ n₂ = 1 := by
  obtain ⟨hu, hv⟩ := coprime_div_gcd_of_sameSquareClass h₁ h₂ hs₁ hs₂ hcl
  have hgpos : 0 < Nat.gcd n₁ n₂ := Nat.gcd_pos_of_pos_left _ h₁
  have hn₁ : n₁ = n₁ / Nat.gcd n₁ n₂ * Nat.gcd n₁ n₂ := (Nat.div_mul_cancel (Nat.gcd_dvd_left n₁ n₂)).symm
  have hn₂ : n₂ = n₂ / Nat.gcd n₁ n₂ * Nat.gcd n₁ n₂ := (Nat.div_mul_cancel (Nat.gcd_dvd_right n₁ n₂)).symm
  unfold squareClassFactor
  generalize Nat.gcd n₁ n₂ = g at *
  generalize n₁ / g = u at *
  generalize n₂ / g = v at *
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hu1 : u = 1 := by simpa using hu
    have hv1 : v = 1 := by simpa using hv
    subst hu1 hv1
    simp
  have key : ∀ a : ZMod (4 * N), IsUnit a → χ a ^ 2 = 1 := by
    intro a ha
    obtain ⟨a', rfl⟩ := ha
    have := MulChar.ext_iff.1 hχ a'
    rwa [MulChar.pow_apply_coe, MulChar.one_apply_coe] at this
  have hnat : n₁ * n₂ = (u * v) * (g * g) := by rw [hn₁, hn₂]; ring
  have hpad : ∀ (p : ℕ) [Fact p.Prime], p ∣ 4 * N → IsSquare (((u * v : ℕ) : ℚ_[p])) := by
    intro p _ hpN
    obtain ⟨y, hy⟩ := hcl p hpN
    have hg0 : (g : ℚ_[p]) ≠ 0 := by exact_mod_cast hgpos.ne'
    refine ⟨y / g, ?_⟩
    rw [hnat] at hy
    push_cast at hy ⊢
    field_simp
    linear_combination hy
  obtain ⟨s, hs⟩ := isSquare_zmod_of_forall_isSquare_padic (by omega) (Nat.coprime_mul_iff_left.2 ⟨hu, hv⟩) hpad
  have hsU : IsUnit s := by
    have : IsUnit (((u * v : ℕ)) : ZMod (4 * N)) := (ZMod.isUnit_iff_coprime _ _).2 (Nat.coprime_mul_iff_left.2 ⟨hu, hv⟩)
    rw [hs] at this
    exact isUnit_of_mul_isUnit_left this
  have h1 : χ (u : ZMod (4 * N)) * χ (v : ZMod (4 * N)) = 1 := by
    calc χ (u : ZMod (4 * N)) * χ (v : ZMod (4 * N)) = χ (((u * v : ℕ)) : ZMod (4 * N)) := by
          rw [Nat.cast_mul, map_mul]
      _ = χ (s * s) := by rw [hs]
      _ = χ s ^ 2 := by rw [map_mul, sq]
      _ = 1 := key s hsU
  have h2 : χ (u : ZMod (4 * N)) ^ 2 = 1 := key _ ((ZMod.isUnit_iff_coprime _ _).2 hu)
  have hne : χ (u : ZMod (4 * N)) ≠ 0 := fun h0 ↦ by rw [h0] at h2; simp at h2
  have hvu : χ (v : ZMod (4 * N)) = χ (u : ZMod (4 * N)) :=
    mul_left_cancel₀ hne (by linear_combination h1 - h2)
  rw [hvu]
  exact mul_inv_cancel₀ hne

/-- **The prime-to-$4N$ form follows:** `WaldspurgerSquareClassFull` implies the named input
`WaldspurgerSquareClass` of `Coefficients.lean`. -/
theorem WaldspurgerSquareClassFull.toWaldspurgerSquareClass {M : MultiplierSystem} {k N : ℕ}
    {χ : DirichletCharacter ℂ (4 * N)} (h : WaldspurgerSquareClassFull M k N χ) :
    WaldspurgerSquareClass M k N χ where
  ratio hk hχ g c F b hg n₁ n₂ h₁ h₂ hs₁ hs₂ _ _ hcl L₁ L₂ hL₁ hL₂ := by
    have e := h.ratio hk hχ g c F b hg n₁ n₂ h₁ h₂ hs₁ hs₂ hcl L₁ L₂ hL₁ hL₂
    rwa [squareClassFactor_eq_one hχ h₁ h₂ hs₁ hs₂ hcl, mul_one] at e

/-- **The square-class ratio for quadratic $\chi$ and all squarefree $n$**, without the factor. -/
theorem WaldspurgerSquareClassFull.ratio_of_quadratic {M : MultiplierSystem} {k N : ℕ}
    {χ : DirichletCharacter ℂ (4 * N)} (h : WaldspurgerSquareClassFull M k N χ) (hk : 1 ≤ k) (hχ : χ ^ 2 = 1)
    {g : ℍ → ℂ} {c : ℕ → ℂ} {F : ℍ → ℂ} {b : ℕ → ℂ} (hg : LiftsTo M k N χ g c F b) {n₁ n₂ : ℕ}
    (h₁ : 1 ≤ n₁) (h₂ : 1 ≤ n₂) (hs₁ : Squarefree n₁) (hs₂ : Squarefree n₂) (hcl : SameSquareClass N n₁ n₂)
    {L₁ L₂ : ℂ → ℂ} (hL₁ : IsEntireLSeries (shimuraTwistCoeff k N χ n₁ b) ((k : ℝ) + 1) L₁)
    (hL₂ : IsEntireLSeries (shimuraTwistCoeff k N χ n₂ b) ((k : ℝ) + 1) L₂) :
    c n₁ ^ 2 * L₂ k * ((n₂ : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) = c n₂ ^ 2 * L₁ k * ((n₁ : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) := by
  have e := h.ratio hk hχ g c F b hg n₁ n₂ h₁ h₂ hs₁ hs₂ hcl L₁ L₂ hL₁ hL₂
  rwa [squareClassFactor_eq_one hχ h₁ h₂ hs₁ hs₂ hcl, mul_one] at e

/-! ## Row 28: Kohnen 1985 with the Petersson quotient -/

/-- **The Petersson product on $S_{2k}(\Gamma_0(N))$, normalized by the index**: Tau Ceti's `peterssonInnerCosets`
(the integral over $\Gamma_0(N)\backslash\mathbb H$) divided by $[\mathrm{SL}_2(\mathbb Z):\Gamma_0(N)]$. -/
noncomputable def peterssonNormalized (k N : ℕ) [NeZero N]
    (f g : CuspForm ((Gamma0 N).map (mapGL ℝ)) ((2 * k : ℕ) : ℤ)) : ℂ :=
  (((Gamma0 N).index : ℂ))⁻¹ * CuspForm.peterssonInnerCosets f g

/-- **Kohnen's formula for odd squarefree level, with the Petersson quotient** (Kohnen 1985 `kohnen1985`, Thm. 1 and
its Corollary [unverified]). For a form $g$ of weight $k+\tfrac12$ on $\Gamma_0(4N)$ with coefficients $c$, a cusp form
$f$ of weight $2k$ on $\Gamma_0(N)$ with coefficients $b$ and Atkin–Lehner eigenvalues `w ℓ` at $\ell \mid N$, and an
entire continuation `L D` of $L(f, D, s) = \sum (D/n)b(n)n^{-s}$: for fundamental $D$ with $(-1)^kD > 0$ and
$(D/\ell) = w_\ell$ for all $\ell \mid N$,
$|c(|D|)|^2/\langle g,g\rangle = 2^{\nu(N)}\,(k-1)!\,\pi^{-k}\,|D|^{k-1/2}\,L(f,D,k)/\langle f,f\rangle$; and
$c(|D|) = 0$ if $(D/\ell) = -w_\ell$ for some $\ell$. (The hypotheses relating $g$ and $f$: $N$ odd squarefree, $f$ a
newform, $g$ in Kohnen's plus space corresponding to $f$, are the caller's, as for `KohnenSquarefree`.) -/
@[kb "kohnen1985" "Thm. 1 and Cor.: |c(|D|)|²/⟨g,g⟩ = 2^ν(N) (k-1)!/π^k |D|^{k-1/2} L(f,D,k)/⟨f,f⟩ if (D/ℓ) = w_ℓ ∀ℓ|N; c(|D|) = 0 if (D/ℓ) = -w_ℓ for some ℓ [unverified]"]
structure KohnenSquarefreePetersson (k N : ℕ) [NeZero N] (w : N.primeFactors → ℤˣ) (g : ℍ → ℂ) (c : ℕ → ℂ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) ((2 * k : ℕ) : ℤ)) (b : ℕ → ℂ) (L : ℤ → ℂ → ℂ) : Prop where
  entire : ∀ D : ℤ, IsEntireLSeries (fun n ↦ (kroneckerDisc D n : ℂ) * b n) ((k : ℝ) + 1) (L D)
  formula : ∀ D : ℤ, IsFundamentalDiscriminant D → 0 < (-1) ^ k * D →
    (∀ ℓ : N.primeFactors, kroneckerDisc D ℓ = w ℓ) →
      ((‖c D.natAbs‖ ^ 2 : ℝ) : ℂ) / peterssonLevel k N g g =
        2 ^ N.primeFactors.card * ((k - 1).factorial / (π : ℂ) ^ k) *
          ((D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) * L D k / peterssonNormalized k N f f
  vanish : ∀ D : ℤ, IsFundamentalDiscriminant D → 0 < (-1) ^ k * D →
    (∃ ℓ : N.primeFactors, kroneckerDisc D ℓ = -(w ℓ : ℤ)) → c D.natAbs = 0

/-- **The Petersson form of Kohnen's formula implies the one with a constant:** for $0 \ne g \in S_{k+1/2}(4N,\chi)$
(any multiplier system) and $f \ne 0$, `KohnenSquarefreePetersson` gives `KohnenSquarefree` with
$\kappa = \langle g,g\rangle/\langle f,f\rangle > 0$. -/
theorem KohnenSquarefreePetersson.toKohnenSquarefree {M : MultiplierSystem} {k N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ (4 * N)} {w : N.primeFactors → ℤˣ} {g : ℍ → ℂ} {c : ℕ → ℂ}
    {f : CuspForm ((Gamma0 N).map (mapGL ℝ)) ((2 * k : ℕ) : ℤ)} {b : ℕ → ℂ} {L : ℤ → ℂ → ℂ}
    (h : KohnenSquarefreePetersson k N w g c f b L) (hg : g ∈ M.cuspForms k N χ) (hg0 : g ≠ 0) (hf0 : f ≠ 0) :
    KohnenSquarefree k N w c b L := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  set I := CuspForm.peterssonInnerCosets f f with hI
  have hIim : I.im = 0 := CuspForm.peterssonInnerCosets_self_im f
  have hIre : 0 < I.re := by
    refine lt_of_le_of_ne (CuspForm.peterssonInnerCosets_self_re_nonneg f) fun h0 ↦ hf0 ?_
    refine (CuspForm.peterssonInnerCosets_self_eq_zero f).1 (Complex.ext ?_ ?_)
    · rw [Complex.zero_re]; exact h0.symm
    · rw [Complex.zero_im]; exact hIim
  have hidx : (0 : ℝ) < ((Gamma0 N).index : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  set Q : ℝ := (((Gamma0 N).index : ℝ))⁻¹ * I.re with hQ
  have hQpos : 0 < Q := by positivity
  have hIc : I = (I.re : ℂ) := Complex.ext (by simp) (by simp [hIim])
  have hQc : peterssonNormalized k N f f = (Q : ℂ) := by
    rw [peterssonNormalized, ← hI, hQ]
    conv_lhs => rw [hIc]
    push_cast
    rfl
  set P : ℝ := (peterssonLevel k N g g).re with hP
  have hPpos : 0 < P := M.peterssonLevel_self_re_pos hN hg hg0
  have hPc : peterssonLevel k N g g = (P : ℂ) := (peterssonLevel_self_eq_ofReal k N g).1
  refine ⟨h.entire, ⟨P / Q, div_pos hPpos hQpos, fun D hD hs hw ↦ ?_⟩, h.vanish⟩
  have e := h.formula D hD hs hw
  rw [hPc, hQc] at e
  have hP0 : (P : ℂ) ≠ 0 := by exact_mod_cast hPpos.ne'
  have hQ0 : (Q : ℂ) ≠ 0 := by exact_mod_cast hQpos.ne'
  rw [div_eq_iff hP0] at e
  rw [e]
  push_cast
  field_simp

end ModularFormsKB.HalfIntegral.Waldspurger