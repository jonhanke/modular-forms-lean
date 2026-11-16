/-
# Tunnell's theorem with the true $L$-function

`Tunnell.lean` derives Tunnell's criterion from `TunnellFormula Lval β` and `CoatesWiles Lval` for an *abstract*
function `Lval` (LE-MF-0257: `TunnellFormula` can hold by definition). Here $L(E_n, 1)$ is the value at $1$ of the
continuation of the $L$-series of Mathlib's `(congruentCurve n).LFunction` (`lCoeff`), stated against every
continuation as in Tau Ceti's Birch and Swinnerton-Dyer statement (`LValueAtOne`). The file `CongruentL.lean`
shows that a continuation exists (it is entire).

**Named inputs** (each a single cited theorem):
- `WaldspurgerSquareClassFull` at level $128$, weight $3/2$, for the trivial character and for
  $\left(\frac 2\cdot\right)$;
- `TunnellEigenforms`: Tunnell's forms are $T(p^2)$-eigen with the eigenvalues $b(p)$ of $f_{32}$;
- `TunnellConstants`: $L(E_n, 1)$ at $n = 1, 3, 2, 10$, one $n$ per square class carrying a nonzero coefficient;
- `CoatesWilesCM` (`CoatesWiles.lean`): the Coates–Wiles theorem for curves with complex multiplication by a maximal
  order, used for $E_n$ ($j = 1728$) through `coatesWilesRank_of_coatesWilesCM`;
- for the converse: Tau Ceti's statement of the Birch and Swinnerton-Dyer conjecture for $E_n$ (`WeierstrassCurve.BirchSwinnertonDyer`).

**Proved** (formerly inputs): `F32Modular` (`f32Modular`), `CongruentRootNumber`
(`congruentRootNumber`), the torsion part of `CoatesWilesL` (`CoatesWilesRank.coatesWilesL`),
`HeckeCharacterRootNumber` (`heckeCharacterRootNumber`, through $f_{64}$), `TunnellMembership`
(`tunnellMembership`, through products of theta series) and `CoatesWilesRank` (from `CoatesWilesCM`).

**Proved:**
- `lValueAtOne_tunnell`: Tunnell's formula $L(E_n,1) = \beta(A(n) - 2B(n))^2/(16\sqrt n)$ ($n$ odd),
  $\beta(C(n) - 2D(n))^2/(8\sqrt n)$ ($n$ even), for squarefree $n \ge 1$, with the true $L$;
- `tunnellFormula_trueL`: the old input `TunnellFormula` holds for $\mathrm{Lval}(n) = \operatorname{Re} L(E_n, 1)$;
- `not_isCongruent_odd_trueL`, `not_isCongruent_even_trueL`: Tunnell's not-congruent direction;
- `weakBSD_of_birchSwinnertonDyer`: Tau Ceti's conjecture for $E_n$ gives a point with $y \ne 0$ when
  $L(E_n, 1) = 0$; hence `isCongruent_iff_odd_trueL`, `isCongruent_iff_even_trueL`.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.RootNumberEven
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.Torsion
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.CoatesWiles
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.TunnellThetaQ
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.TunnellThetaCusp
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.TunnellAux
import ModularFormsKB.HalfIntegral.Abstract.ThetaInstance
import ModularFormsKB.HalfIntegral.Waldspurger.Restated

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open Complex Tunnell WeierstrassCurve
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-! ## Named inputs -/

/-- **Tunnell's $q$-series are cusp forms** of weight $3/2$ on $\Gamma_0(128)$ for the theta multiplier, with
characters $1$ and $\left(\frac 2\cdot\right)$ (Tunnell 1983 `tunnell1983`, Koblitz 1984 Ch. IV §4 [unverified]:
$g_{\mathrm{odd}} = \eta(8\tau)\eta(16\tau)\theta(2\tau)$, $g_{\mathrm{even}} = \eta(8\tau)\eta(16\tau)\theta(4\tau)$).
Formerly a hypothesis; now proved (`tunnellMembership`). -/
structure TunnellMembership : Prop where
  odd : tunnellOdd ∈ thetaMultiplierSystem.cuspForms 1 32 tunnellChi0
  even : tunnellEven ∈ thetaMultiplierSystem.cuspForms 1 32 tunnellChi2

/-- **`TunnellMembership` is proved**: Tunnell's forms are $\tfrac12(\theta(z) - \theta(4z))\,\theta(2z)\,(2\theta(32z) -
\theta(8z))$ and the same with $\theta(4z)$ in the middle (`tunnellOdd_eq_theta`, `tunnellEven_eq_theta`); the law on
$\Gamma_0(128)$ is `thetaTwist_law` for each factor, and at every cusp one factor vanishes. -/
theorem tunnellMembership : TunnellMembership where
  odd := by
    rw [tunnellOdd_eq_theta]
    exact ⟨mdiff_tunnellOddTheta, transforms_tunnellOddTheta, zero_at_cusps_tunnellOddTheta⟩
  even := by
    rw [tunnellEven_eq_theta]
    exact ⟨mdiff_tunnellEvenTheta, transforms_tunnellEvenTheta, zero_at_cusps_tunnellEvenTheta⟩

/-- **Tunnell's eigenform proposition** (Tunnell 1983 `tunnell1983` [unverified]; checked numerically by
`docs/waldspurger/tunnell_forms.py`): for every odd prime $p$, Shimura's $T(p^2)$ acts on the coefficients of Tunnell's
forms by $b(p)$, the $p$-th coefficient of $f_{32}$. -/
@[kb "tunnell1983" "T(p²) g = a_p(E₁) g for g = η(8z)η(16z)θ(2z) ∈ S_{3/2}(128) and η(8z)η(16z)θ(4z) ∈ S_{3/2}(128, (2/·)) [unverified]"]
structure TunnellEigenforms : Prop where
  odd : ∀ p : ℕ, p.Prime → p ≠ 2 → heckeT 1 32 tunnellChi0 p tunnellOddCoeff = (f32Coeff p : ℂ) • tunnellOddCoeff
  even : ∀ p : ℕ, p.Prime → p ≠ 2 → heckeT 1 32 tunnellChi2 p tunnellEvenCoeff = (f32Coeff p : ℂ) • tunnellEvenCoeff

/-- **Tunnell's constants** (Tunnell 1983 `tunnell1983` [unverified]; checked numerically by
`docs/waldspurger/numerics.py tunnell`): $L(E_1, 1) = \beta/4$, $L(E_3, 1) = \beta/\sqrt3$, $L(E_2, 1) = \beta/(2\sqrt2)$,
$L(E_{10}, 1) = 2\beta/\sqrt{10}$ (exact central values of Hecke $L$-functions of $\mathbb Q(i)$; one $n$ per square
class at $2$ on which Tunnell's coefficients do not all vanish). -/
@[kb "tunnell1983" "L(E_1,1) = β/4, L(E_3,1) = β/√3, L(E_2,1) = β/(2√2), L(E_10,1) = 2β/√10 [unverified; numerics.py]"]
structure TunnellConstants : Prop where
  one : LValueAtOne 1 (tunnellBeta / 4)
  three : LValueAtOne 3 (tunnellBeta / Real.sqrt 3)
  two : LValueAtOne 2 (tunnellBeta / (2 * Real.sqrt 2))
  ten : LValueAtOne 10 (2 * tunnellBeta / Real.sqrt 10)

/-- **Coates–Wiles for the congruent number curves, with the true $L$**: if $L(E_n, 1) \ne 0$ then $E_n(\mathbb Q)$ is
finite. Formerly a named input; now the case $j = 1728$ of the cited theorem `CoatesWilesCM`
(`coatesWilesRank_of_coatesWilesCM`). The torsion computation that `CoatesWilesL` also carried is proved
(`not_hasPointYNeZero_of_finite`). -/
structure CoatesWilesRank : Prop where
  finite : ∀ n : ℕ, 0 < n → Squarefree n → ∀ ⦃F : ℂ → ℂ⦄ ⦃U : Set ℂ⦄,
    LSeries.IsContinuationOn (lCoeff n) F U → 1 ∈ U → F 1 ≠ 0 → Finite (congruentCurve n).toAffine.Point

/-- **Coates–Wiles with the torsion of $E_n$**: $L(E_n, 1) \ne 0 \Rightarrow$ no rational point with $y \ne 0$. Formerly
a named input; now derived from `CoatesWilesRank` and the torsion of $E_n(\mathbb Q)$. -/
structure CoatesWilesL : Prop where
  no_point : ∀ n : ℕ, 0 < n → Squarefree n → ∀ ⦃F : ℂ → ℂ⦄ ⦃U : Set ℂ⦄,
    LSeries.IsContinuationOn (lCoeff n) F U → 1 ∈ U → F 1 ≠ 0 → ¬ HasPointYNeZero n

/-- **`CoatesWilesRank` from the cited Coates–Wiles theorem**: $E_n$ has $j = 1728$, complex multiplication by
$\mathbb Z[i]$ (`j_congruentCurve_mem`), and `lCoeff n` is the coefficient sequence of Mathlib's `LFunction`. -/
theorem coatesWilesRank_of_coatesWilesCM (h : CoatesWilesCM) : CoatesWilesRank where
  finite n hn _ F U hF h1 h0 := by
    haveI : NeZero n := ⟨hn.ne'⟩
    exact h.finite (congruentCurve n) (j_congruentCurve_mem n) hF h1 h0

/-- `CoatesWilesL` from the rank statement and the torsion of $E_n(\mathbb Q)$. -/
theorem CoatesWilesRank.coatesWilesL (h : CoatesWilesRank) : CoatesWilesL where
  no_point n hn hsq _ _ hF h1 h0 := not_hasPointYNeZero_of_finite hn (h.finite n hn hsq hF h1 h0)

theorem CoatesWilesRank.no_point (h : CoatesWilesRank) : ∀ n : ℕ, 0 < n → Squarefree n →
    ∀ ⦃F : ℂ → ℂ⦄ ⦃U : Set ℂ⦄, LSeries.IsContinuationOn (lCoeff n) F U → 1 ∈ U → F 1 ≠ 0 →
      ¬ HasPointYNeZero n :=
  h.coatesWilesL.no_point

theorem CoatesWilesCM.no_point (h : CoatesWilesCM) : ∀ n : ℕ, 0 < n → Squarefree n →
    ∀ ⦃F : ℂ → ℂ⦄ ⦃U : Set ℂ⦄, LSeries.IsContinuationOn (lCoeff n) F U → 1 ∈ U → F 1 ≠ 0 →
      ¬ HasPointYNeZero n :=
  (coatesWilesRank_of_coatesWilesCM h).no_point

/-! ## Values at $1$ and the entire continuation -/

/-- An entire continuation of a series with abscissa at most $2$ is an `IsEntireLSeries` with $\sigma_0 = 1 + 1$. -/
theorem isEntireLSeries_of_univ {a b : ℕ → ℂ} (hab : a = b) {G : ℂ → ℂ}
    (hG : LSeries.IsContinuationOn a G Set.univ) (habs : LSeries.abscissaOfAbsConv a ≤ 2) :
    IsEntireLSeries b (((1 : ℕ) : ℝ) + 1) G := by
  subst hab
  refine ⟨Complex.analyticOnNhd_univ_iff_differentiable.mp hG.analyticOnNhd, fun s hs ↦ ?_⟩
  refine hG.eq_LSeries (Set.mem_univ s) (habs.trans_lt ?_)
  have : (2 : ℝ) < s.re := by simpa [one_add_one_eq_two] using hs
  have h2 : ((2 : ℝ) : EReal) < (s.re : EReal) := EReal.coe_lt_coe_iff.mpr this
  calc (2 : EReal) = ((2 : ℝ) : EReal) := by norm_cast
    _ < _ := h2

/-- **An entire continuation exists** (`CongruentL.lean`). -/
theorem exists_univ (hM : F32Modular) {n : ℕ} [NeZero n] (hn : Squarefree n) :
    ∃ G, LSeries.IsContinuationOn (lCoeff n) G Set.univ :=
  (hasEntireExtension_lCoeff hM hn).exists_isContinuationOn_univ

/-! ## Waldspurger's theorem for Tunnell's forms -/

theorem eigen_f32 {p : ℕ} (hp : p.Prime) (hp2 : ¬ p ∣ 4 * 32) :
    heckeTInt (2 * 1) (4 * 32) 1 p f32C = f32C p • f32C := by
  have hp2' : p ≠ 2 := fun h ↦ hp2 (h ▸ by norm_num)
  have hu : IsUnit ((p : ℕ) : ZMod (4 * 32)) := by
    rw [ZMod.isUnit_iff_coprime, show 4 * 32 = 2 ^ 7 by norm_num]
    exact ((Nat.coprime_primes hp Nat.prime_two).mpr hp2').pow_right 7
  funext n
  have h := f32Coeff_hecke hp hp2' n
  simp only [heckeTInt, f32C, Pi.smul_apply, smul_eq_mul, MulChar.one_apply hu, one_mul]
  split_ifs with hd
  · rw [if_pos hd] at h
    have : ((p : ℂ) ^ ((((2 * 1 : ℕ) : ℤ)) - 1)) = p := by norm_num
    rw [this]
    exact_mod_cast h
  · rw [if_neg hd, add_zero] at h
    rw [add_zero]
    exact_mod_cast h

/-- **Tunnell's odd form lifts to $f_{32}$** (given its membership, Tunnell's eigenform proposition and the
modularity of $f_{32}$). -/
theorem liftsTo_odd (hE : TunnellEigenforms) (hM : F32Modular) :
    LiftsTo thetaMultiplierSystem 1 32 tunnellChi0 tunnellOdd tunnellOddCoeff f32 f32C where
  mem := tunnellMembership.odd
  ne_zero := tunnellOdd_ne_zero
  coeff_g := hasQExp_tunnellOdd
  cusp_F := isIntCuspForm_f32 hM
  coeff_F := hasQExp_f32
  normalized := by simp [f32C, f32Coeff_one]
  eigen_F p hp hp2 := eigen_f32 hp hp2
  eigen_g p hp hp2 := hE.odd p hp (fun h ↦ hp2 (h ▸ by norm_num))

/-- **Tunnell's even form lifts to $f_{32}$.** -/
theorem liftsTo_even (hE : TunnellEigenforms) (hM : F32Modular) :
    LiftsTo thetaMultiplierSystem 1 32 tunnellChi2 tunnellEven tunnellEvenCoeff f32 f32C where
  mem := tunnellMembership.even
  ne_zero := tunnellEven_ne_zero
  coeff_g := hasQExp_tunnellEven
  cusp_F := isIntCuspForm_f32 hM
  coeff_F := hasQExp_f32
  normalized := by simp [f32C, f32Coeff_one]
  eigen_F p hp hp2 := eigen_f32 hp hp2
  eigen_g p hp hp2 := hE.even p hp (fun h ↦ hp2 (h ▸ by norm_num))

theorem rpow_half_eq_sqrt (x : ℕ) : ((x : ℝ) ^ (((1 : ℕ) : ℝ) - 1 / 2) : ℝ) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow]; norm_num

/-- **The ratio on one square class.** If $n_0 n \equiv 1 \bmod 8$ (both odd squarefree) and $g$ lifts to $f_{32}$
with character $\chi$, then $c(n_0)^2 G(1)\sqrt n = c(n)^2 G_0(1)\sqrt{n_0}$ for the entire continuations $G_0$, $G$ of
the twisted $L$-series of indices $n_0$, $n$ (Waldspurger). -/
theorem ratio_of_class {χ : DirichletCharacter ℂ (4 * 32)} (hχ : χ ^ 2 = 1)
    (hW : WaldspurgerSquareClassFull thetaMultiplierSystem 1 32 χ) {g : ℍ → ℂ} {c : ℕ → ℂ}
    (hg : LiftsTo thetaMultiplierSystem 1 32 χ g c f32 f32C)
    {n₀ n : ℕ} (h₀ : 1 ≤ n₀) (h₁ : 1 ≤ n) (hs₀ : Squarefree n₀) (hs : Squarefree n) (hcl : n₀ * n % 8 = 1)
    {a₀ a : ℕ → ℂ} (ha₀ : shimuraTwistCoeff 1 32 χ n₀ f32C = a₀) (ha : shimuraTwistCoeff 1 32 χ n f32C = a)
    (habs₀ : LSeries.abscissaOfAbsConv a₀ ≤ 2) (habs : LSeries.abscissaOfAbsConv a ≤ 2)
    {G₀ G : ℂ → ℂ} (hG₀ : LSeries.IsContinuationOn a₀ G₀ Set.univ)
    (hG : LSeries.IsContinuationOn a G Set.univ) :
    c n₀ ^ 2 * G 1 * Real.sqrt n = c n ^ 2 * G₀ 1 * Real.sqrt n₀ := by
  have hcl' := sameSquareClass_of_mod_eight hcl
  have h := hW.ratio le_rfl hχ g c f32 f32C hg n₀ n h₀ h₁ hs₀ hs hcl' G₀ G
    (isEntireLSeries_of_univ ha₀.symm hG₀ habs₀) (isEntireLSeries_of_univ ha.symm hG habs)
  rw [squareClassFactor_eq_one hχ h₀ h₁ hs₀ hs hcl', rpow_half_eq_sqrt, rpow_half_eq_sqrt] at h
  simpa using h

/-- All the inputs of Tunnell's formula with the true $L$-function: each a cited theorem. -/
structure TunnellInputs : Prop where
  waldspurger_odd : WaldspurgerSquareClassFull thetaMultiplierSystem 1 32 tunnellChi0
  waldspurger_even : WaldspurgerSquareClassFull thetaMultiplierSystem 1 32 tunnellChi2
  eigen : TunnellEigenforms
  constants : TunnellConstants

/-- `F32Modular` is proved (`f32Modular`); kept as a field name for the proofs below. -/
theorem TunnellInputs.f32 (_h : TunnellInputs) : F32Modular := f32Modular

/-- The root numbers (`congruentRootNumber`), with `HeckeCharacterRootNumber` proved
(`heckeCharacterRootNumber`, through $f_{64}$). -/
theorem TunnellInputs.rootNumber (_h : TunnellInputs) : CongruentRootNumber :=
  congruentRootNumber_proved

theorem chi0_twist {n : ℕ} [NeZero n] (hn : Squarefree n) :
    shimuraTwistCoeff 1 32 tunnellChi0 n f32C = lCoeff n := by
  rw [lCoeff_eq hn]; funext d; exact shimuraTwistCoeff_chi0 n d

theorem chi2_twist {m : ℕ} [NeZero m] (hn : Squarefree (2 * m)) :
    shimuraTwistCoeff 1 32 tunnellChi2 m f32C = lCoeff (2 * m) := by
  haveI : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  rw [lCoeff_eq hn]; funext d; exact shimuraTwistCoeff_chi2 m d

theorem squarefree_three : Squarefree 3 := Nat.prime_three.squarefree
theorem squarefree_two_mul_one : Squarefree (2 * 1) := by simpa using Nat.prime_two.squarefree
theorem squarefree_two_mul_five : Squarefree (2 * 5) :=
  (Nat.squarefree_mul (by norm_num)).mpr ⟨Nat.prime_two.squarefree, Nat.prime_five.squarefree⟩
theorem squarefree_five : Squarefree 5 := Nat.prime_five.squarefree

theorem solve_ratio {G₁ c c₀ v₀ s s₀ : ℂ} (hs : s ≠ 0) (hc₀ : c₀ ≠ 0)
    (h : c₀ ^ 2 * G₁ * s = c ^ 2 * v₀ * s₀) : G₁ = c ^ 2 * v₀ * s₀ / (c₀ ^ 2 * s) := by
  field_simp
  linear_combination h

theorem sqrt_ne_zero_of_pos {n : ℕ} (hn : 0 < n) : ((Real.sqrt n : ℝ) : ℂ) ≠ 0 := by
  have : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  exact_mod_cast this.ne'

/-- **Row 36: Tunnell's formula with the true $L$-function, odd $n$.** -/
theorem lValueAtOne_tunnell_odd (h : TunnellInputs) {n : ℕ} (hn : 0 < n) (hsq : Squarefree n) (hodd : Odd n) :
    LValueAtOne n ((tunnellBeta * ((tunnellA n : ℝ) - 2 * tunnellB n) ^ 2 / (16 * Real.sqrt n) : ℝ) : ℂ) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨G, hG⟩ := exists_univ h.f32 hsq
  intro F U hF h1
  rw [hF.eqOn_of_subset hG (Set.subset_univ U) h1]
  have hsn := sqrt_ne_zero_of_pos hn
  have hc : tunnellOddCoeff n = (tunnellB n : ℂ) - (tunnellA n : ℂ) / 2 := if_pos hodd
  have hmod : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    obtain ⟨k, rfl⟩ := hodd; omega
  have hlift := liftsTo_odd h.eigen h.f32
  have hχ : tunnellChi0 ^ 2 = 1 := one_pow 2
  rcases hmod with h8 | h8 | h8 | h8
  · -- the class of 1
    obtain ⟨G₀, hG₀⟩ := exists_univ (n := 1) h.f32 squarefree_one
    have hr := ratio_of_class hχ h.waldspurger_odd hlift le_rfl hn squarefree_one hsq (by omega)
      (chi0_twist squarefree_one) (chi0_twist hsq)
      (abscissaOfAbsConv_lCoeff_le squarefree_one) (abscissaOfAbsConv_lCoeff_le hsq) hG₀ hG
    rw [h.constants.one.eq_of_univ hG₀, tunnellOddCoeff_one] at hr
    simp only [Nat.cast_one, Real.sqrt_one, Complex.ofReal_one] at hr
    rw [solve_ratio hsn one_ne_zero hr, hc]
    push_cast
    field_simp
    ring
  · -- the class of 3
    obtain ⟨G₀, hG₀⟩ := exists_univ (n := 3) h.f32 squarefree_three
    have hr := ratio_of_class hχ h.waldspurger_odd hlift (by norm_num) hn squarefree_three hsq (by omega)
      (chi0_twist squarefree_three) (chi0_twist hsq)
      (abscissaOfAbsConv_lCoeff_le squarefree_three) (abscissaOfAbsConv_lCoeff_le hsq) hG₀ hG
    rw [h.constants.three.eq_of_univ hG₀, tunnellOddCoeff_three] at hr
    have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := sqrt_ne_zero_of_pos (n := 3) (by norm_num)
    rw [solve_ratio hsn two_ne_zero hr, hc]
    push_cast at h3 ⊢
    field_simp
    ring
  all_goals
    rw [LValueAtOne.eq_of_univ (h.rootNumber.vanish n hn hsq (by omega)) hG,
      tunnellA_eq_zero (by omega), tunnellB_eq_zero (by omega)]
    simp

/-- **Row 36: Tunnell's formula with the true $L$-function, even $n$.** -/
theorem lValueAtOne_tunnell_even (h : TunnellInputs) {n : ℕ} (hn : 0 < n) (hsq : Squarefree n) (heven : Even n) :
    LValueAtOne n ((tunnellBeta * ((tunnellC n : ℝ) - 2 * tunnellD n) ^ 2 / (8 * Real.sqrt n) : ℝ) : ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := even_iff_two_dvd.mp heven
  have hm : 0 < m := by omega
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have hmodd : Odd m := by
    by_contra hc
    obtain ⟨j, rfl⟩ := Nat.not_odd_iff_even.mp hc
    exact absurd (hsq 2 ⟨j, by ring⟩) (by decide)
  have hsqm : Squarefree m := hsq.squarefree_of_dvd (dvd_mul_left m 2)
  obtain ⟨G, hG⟩ := exists_univ h.f32 hsq
  intro F U hF h1
  rw [hF.eqOn_of_subset hG (Set.subset_univ U) h1]
  have hsm := sqrt_ne_zero_of_pos hm
  have hc : tunnellEvenCoeff m = (tunnellD (2 * m) : ℂ) - (tunnellC (2 * m) : ℂ) / 2 := if_pos hmodd
  have hsqrt : Real.sqrt ((2 * m : ℕ) : ℝ) = Real.sqrt 2 * Real.sqrt m := by
    push_cast; exact Real.sqrt_mul (by norm_num) _
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := sqrt_ne_zero_of_pos (n := 2) (by norm_num)
  have hmod : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by
    obtain ⟨k, rfl⟩ := hmodd; omega
  have hlift := liftsTo_even h.eigen h.f32
  rcases hmod with h8 | h8 | h8 | h8
  · -- the class of 1 (n₀ = 2)
    obtain ⟨G₀, hG₀⟩ := exists_univ (n := 2 * 1) h.f32 squarefree_two_mul_one
    have hr := ratio_of_class tunnellChi2_sq h.waldspurger_even hlift le_rfl hm squarefree_one hsqm
      (by omega) (chi2_twist (m := 1) squarefree_two_mul_one) (chi2_twist hsq)
      (abscissaOfAbsConv_lCoeff_le squarefree_two_mul_one) (abscissaOfAbsConv_lCoeff_le hsq) hG₀ hG
    rw [h.constants.two.eq_of_univ hG₀, tunnellEvenCoeff_one] at hr
    simp only [Nat.cast_one, Real.sqrt_one, Complex.ofReal_one] at hr
    rw [solve_ratio hsm one_ne_zero hr, hc, hsqrt]
    push_cast at h2 ⊢
    field_simp
    ring
  · rw [LValueAtOne.eq_of_univ (h.rootNumber.vanish (2 * m) hn hsq (by omega)) hG,
      tunnellC_eq_zero (by omega), tunnellD_eq_zero (by omega)]
    simp
  · -- the class of 5 (n₀ = 10)
    obtain ⟨G₀, hG₀⟩ := exists_univ (n := 2 * 5) h.f32 squarefree_two_mul_five
    have hr := ratio_of_class tunnellChi2_sq h.waldspurger_even hlift (by norm_num) hm squarefree_five hsqm
      (by omega) (chi2_twist (m := 5) squarefree_two_mul_five) (chi2_twist hsq)
      (abscissaOfAbsConv_lCoeff_le squarefree_two_mul_five) (abscissaOfAbsConv_lCoeff_le hsq) hG₀ hG
    rw [h.constants.ten.eq_of_univ hG₀, tunnellEvenCoeff_five] at hr
    have h5 : ((Real.sqrt 5 : ℝ) : ℂ) ≠ 0 := sqrt_ne_zero_of_pos (n := 5) (by norm_num)
    have h10 : Real.sqrt 10 = Real.sqrt 2 * Real.sqrt 5 := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    rw [solve_ratio hsm two_ne_zero hr, hc, hsqrt, h10]
    push_cast at h2 h5 ⊢
    field_simp
    ring
  · rw [LValueAtOne.eq_of_univ (h.rootNumber.vanish (2 * m) hn hsq (by omega)) hG,
      tunnellC_eq_zero (by omega), tunnellD_eq_zero (by omega)]
    simp

/-! ## Tunnell's theorem -/

/-- $L(E_n, 1)$ for squarefree $n \ge 1$: the value at $1$ of the entire continuation (`0` otherwise). -/
noncomputable def congruentLOne (h : TunnellInputs) (n : ℕ) : ℂ :=
  if hn : 0 < n ∧ Squarefree n then
    haveI : NeZero n := ⟨hn.1.ne'⟩
    (exists_univ h.f32 hn.2).choose 1
  else 0

theorem congruentLOne_spec (h : TunnellInputs) {n : ℕ} (hn : 0 < n) (hsq : Squarefree n) {v : ℂ}
    (hv : LValueAtOne n v) : congruentLOne h n = v := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [congruentLOne, dif_pos ⟨hn, hsq⟩]
  exact hv.eq_of_univ (exists_univ h.f32 hsq).choose_spec

/-- **The old input `TunnellFormula` holds for the true $L$-values** $\operatorname{Re} L(E_n, 1)$, with
$\beta = \int_1^\infty dx/\sqrt{x^3 - x}$. -/
theorem tunnellFormula_trueL (h : TunnellInputs) :
    TunnellFormula (fun n ↦ (congruentLOne h n).re) tunnellBeta where
  beta_pos := tunnellBeta_pos
  odd n hsq hodd := by
    rw [congruentLOne_spec h hodd.pos hsq (lValueAtOne_tunnell_odd h hodd.pos hsq hodd), Complex.ofReal_re]
  even n hsq heven := by
    have hn : 0 < n := Nat.pos_of_ne_zero fun h0 ↦ by
      subst h0; exact absurd hsq (by simp)
    rw [congruentLOne_spec h hn hsq (lValueAtOne_tunnell_even h hn hsq heven), Complex.ofReal_re]

/-- **Tunnell's not-congruent direction with the true $L$-function, odd $n$**, from Waldspurger 1981,
Tunnell's eigenform proposition and constants, and the Coates–Wiles theorem: an odd squarefree $n$ with $A(n) \ne 2B(n)$ is not congruent. -/
theorem not_isCongruent_odd_trueL (h : TunnellInputs) (hCW : CoatesWilesCM) {n : ℕ} (hn : 0 < n)
    (hsq : Squarefree n) (hodd : Odd n) (hAB : tunnellA n ≠ 2 * tunnellB n) : ¬ IsCongruent n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨G, hG⟩ := exists_univ h.f32 hsq
  intro hc
  refine hCW.no_point n hn hsq hG (Set.mem_univ 1) ?_ ((isCongruent_iff_point hn).mp hc)
  rw [lValueAtOne_tunnell_odd h hn hsq hodd hG (Set.mem_univ 1)]
  have h0 : ((tunnellA n : ℝ) - 2 * tunnellB n) ≠ 0 := by
    intro h0; apply hAB; exact_mod_cast (by linarith : (tunnellA n : ℝ) = 2 * tunnellB n)
  have := tunnellBeta_pos
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  exact_mod_cast (by positivity : tunnellBeta * ((tunnellA n : ℝ) - 2 * tunnellB n) ^ 2 / (16 * Real.sqrt n) ≠ 0)

/-- **Tunnell's not-congruent direction with the true $L$-function, even $n$.** -/
theorem not_isCongruent_even_trueL (h : TunnellInputs) (hCW : CoatesWilesCM) {n : ℕ} (hn : 0 < n)
    (hsq : Squarefree n) (heven : Even n) (hCD : tunnellC n ≠ 2 * tunnellD n) : ¬ IsCongruent n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨G, hG⟩ := exists_univ h.f32 hsq
  intro hc
  refine hCW.no_point n hn hsq hG (Set.mem_univ 1) ?_ ((isCongruent_iff_point hn).mp hc)
  rw [lValueAtOne_tunnell_even h hn hsq heven hG (Set.mem_univ 1)]
  have h0 : ((tunnellC n : ℝ) - 2 * tunnellD n) ≠ 0 := by
    intro h0; apply hCD; exact_mod_cast (by linarith : (tunnellC n : ℝ) = 2 * tunnellD n)
  have := tunnellBeta_pos
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  exact_mod_cast (by positivity : tunnellBeta * ((tunnellC n : ℝ) - 2 * tunnellD n) ^ 2 / (8 * Real.sqrt n) ≠ 0)

/-! ## Row 34: the converse from Tau Ceti's Birch and Swinnerton-Dyer statement -/

/-- **Row 34: `WeakBSD` from Tau Ceti's Birch and Swinnerton-Dyer conjecture for $E_n$**: if $L(E_n, 1) = 0$ for some
continuation, the rank is positive, so $E_n$ has a point with $y \ne 0$ (`hasPointYNeZero_of_finrank_pos`). -/
theorem hasPointYNeZero_of_birchSwinnertonDyer {n : ℕ} [NeZero n] (hBSD : (congruentCurve n).BirchSwinnertonDyer)
    {F : ℂ → ℂ} {U : Set ℂ} (hF : LSeries.IsContinuationOn (lCoeff n) F U) (h1 : 1 ∈ U) (h0 : F 1 = 0) :
    HasPointYNeZero n := by
  apply hasPointYNeZero_of_finrank_pos
  have := (hBSD.apply_one_ne_zero_iff hF h1).not.mp (not_not.mpr h0)
  omega

/-- **Tunnell's criterion, odd $n$**, conditional on the inputs of `TunnellInputs`, `CoatesWilesL` and Tau Ceti's
statement of the Birch and Swinnerton-Dyer conjecture for $E_n$. -/
theorem isCongruent_iff_odd_trueL (h : TunnellInputs) (hCW : CoatesWilesCM) {n : ℕ} [NeZero n]
    (hsq : Squarefree n) (hodd : Odd n) (hBSD : (congruentCurve n).BirchSwinnertonDyer) :
    IsCongruent n ↔ tunnellA n = 2 * tunnellB n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  refine ⟨fun hc ↦ by_contra fun hAB ↦ not_isCongruent_odd_trueL h hCW hn hsq hodd hAB hc, fun hAB ↦ ?_⟩
  obtain ⟨G, hG⟩ := exists_univ h.f32 hsq
  refine (isCongruent_iff_point hn).mpr (hasPointYNeZero_of_birchSwinnertonDyer hBSD hG (Set.mem_univ 1) ?_)
  rw [lValueAtOne_tunnell_odd h hn hsq hodd hG (Set.mem_univ 1)]
  have : (tunnellA n : ℝ) = 2 * tunnellB n := by exact_mod_cast hAB
  simp [this]

/-- **Tunnell's criterion, even $n$**, conditional as in `isCongruent_iff_odd_trueL`. -/
theorem isCongruent_iff_even_trueL (h : TunnellInputs) (hCW : CoatesWilesCM) {n : ℕ} [NeZero n]
    (hsq : Squarefree n) (heven : Even n) (hBSD : (congruentCurve n).BirchSwinnertonDyer) :
    IsCongruent n ↔ tunnellC n = 2 * tunnellD n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  refine ⟨fun hc ↦ by_contra fun hCD ↦ not_isCongruent_even_trueL h hCW hn hsq heven hCD hc, fun hCD ↦ ?_⟩
  obtain ⟨G, hG⟩ := exists_univ h.f32 hsq
  refine (isCongruent_iff_point hn).mpr (hasPointYNeZero_of_birchSwinnertonDyer hBSD hG (Set.mem_univ 1) ?_)
  rw [lValueAtOne_tunnell_even h hn hsq heven hG (Set.mem_univ 1)]
  have : (tunnellC n : ℝ) = 2 * tunnellD n := by exact_mod_cast hCD
  simp [this]

/-- **Tunnell's criterion from Tau Ceti's full conjecture** `TauCeti.BirchSwinnertonDyerConjecture`, odd $n$. -/
theorem isCongruent_iff_odd_of_conjecture (h : TunnellInputs) (hCW : CoatesWilesCM)
    (hBSD : TauCeti.BirchSwinnertonDyerConjecture) {n : ℕ} (hn : 0 < n) (hsq : Squarefree n) (hodd : Odd n) :
    IsCongruent n ↔ tunnellA n = 2 * tunnellB n :=
  haveI : NeZero n := ⟨hn.ne'⟩
  isCongruent_iff_odd_trueL h hCW hsq hodd (hBSD (congruentCurve n))

/-- **Tunnell's criterion from Tau Ceti's full conjecture, even $n$.** -/
theorem isCongruent_iff_even_of_conjecture (h : TunnellInputs) (hCW : CoatesWilesCM)
    (hBSD : TauCeti.BirchSwinnertonDyerConjecture) {n : ℕ} (hn : 0 < n) (hsq : Squarefree n) (heven : Even n) :
    IsCongruent n ↔ tunnellC n = 2 * tunnellD n :=
  haveI : NeZero n := ⟨hn.ne'⟩
  isCongruent_iff_even_trueL h hCW hsq heven (hBSD (congruentCurve n))

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
