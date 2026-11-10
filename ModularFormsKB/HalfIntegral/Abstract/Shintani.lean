/-
# Shintani's lift: cycle integrals and the cycle-integral formula

Completes the named input `ShintaniAdjoint` (`Abstract/Shimura.lean`), which only
asserts that an adjoint of the Shimura lift exists, by the explicit formula for the Shintani lift in the normalization of
Kohnen–Zagier 1981 `kohnenzagier1981` (§II [unverified]), going back to Shintani 1975 `shintani1975` [unverified]:
level one, Kohnen's plus space $S^+_{k+1/2}(4)$, a fundamental discriminant $D$ with $(-1)^kD > 0$.

**Cycle integrals.** For a binary quadratic form $Q = [a,b,c]$ (`BinQF`, `Abstract/BinaryForms.lean`) of discriminant
$\Delta > 0$, the geodesic $S_Q = \{z \in \mathbb H : a|z|^2 + b\operatorname{Re}z + c = 0\}$ is parametrized by hyperbolic arc
length as the flow of $\dot z = Q(z, 1)/\sqrt\Delta$ (`BinQF.geodesic`, `BinQF.hasDerivAt_geodesic`): for $a \ne 0$
$$ z_Q(s) = \frac{-b - \sqrt\Delta\tanh s}{2a} + i\,\frac{\sqrt\Delta}{2|a|\cosh s}, $$
running from the root $w_+ = \frac{-b+\sqrt\Delta}{2a}$ ($s \to -\infty$) to $w_- = \frac{-b-\sqrt\Delta}{2a}$ ($s \to +\infty$); for
$a = 0$ it is the vertical line $z_Q(s) = -c/b + i e^{\operatorname{sgn}(b)s}$. Along it $dz/Q(z,1) = ds/\sqrt\Delta$, so
$$ \int_{C_Q} G(z)\,Q(z,1)^{k-1}\,dz = \frac1{\sqrt\Delta}\int G(z_Q(s))\,Q(z_Q(s),1)^k\,ds $$
(`BinQF.cycleIntegral`), the integral running over one period $[0, 2\log\varepsilon]$ when $\Delta$ is not a square, where
$\varepsilon = (t + u\sqrt{\Delta_0})/2$ is the fundamental solution of $t^2 - \Delta_0u^2 = 4$, $\Delta_0 = \Delta/\gcd(a,b,c)^2$
(`BinQF.pellUnit`; the automorph `BinQF.automorphSL` generates the stabilizer of $Q$ modulo $\pm1$), and over all of
$\mathbb R$ when $\Delta$ is a square (the geodesic joins two cusps). The orientation (from $w_+$ to $w_-$) is a convention: the
opposite one changes every coefficient by the same sign, absorbed in the constant of `ShintaniShimuraAdjoint`.

**Genus character** (Gross–Kohnen–Zagier 1987 `gkz1987`, §I.2 [unverified]): for $\Delta = DD'$ with $D$ fundamental and $D'$
a discriminant, $\chi_D(Q) = \left(\frac Dm\right)$ for any integer $m$ represented by $Q$ and prime to $D$, and $0$ if there is
none. `BinQF.genusChar` takes the first such value in a fixed enumeration of $\mathbb Z^2$; that every choice gives the same
value is the named input `GenusCharacterWellDefined`, from which class invariance is proved (`BinQF.genusChar_comp`).
$\left(\frac Dm\right)$ for $m < 0$ is $\operatorname{sgn}(D)\left(\frac D{|m|}\right)$ (`kroneckerInt`).

**The Shintani coefficient** (`shintaniCoeff`): for $n \ge 1$ with $(-1)^kn \equiv 0, 1 \bmod 4$,
$$ r_{k,D}(G; n) = \sum_{Q \in \mathcal Q_{|D|n}/\mathrm{SL}_2(\mathbb Z)} \chi_D(Q)\int_{C_Q} G(z)\,Q(z,1)^{k-1}\,dz, $$
a finite sum over proper equivalence classes of forms of discriminant $|D|n$ (each class through a chosen representative;
the summand is class invariant for $G$ of level one), and $0$ for the other $n$.

**Named inputs and what follows.**
- `ShintaniCycleFormula`: $\sum_n r_{k,D}(G;n)q^n \in S^+_{k+1/2}(4)$ for $G \in S_{2k}(\mathrm{SL}_2(\mathbb Z))$.
- `ShintaniShimuraAdjoint`: with a nonzero constant $\lambda_{k,D}$, $\langle \mathcal S_D g, G\rangle = \lambda_{k,D}\langle g, \mathcal S^*_D G\rangle$,
  where $\mathcal S_D$ is the $D$-th Shimura lift on the plus space (`kzShimuraCoeff`) and $\mathcal S^*_D G$ the series of the
  cycle-integral coefficients.
- Proved: the Shintani lift `shintaniLift` is the unique function with these coefficients (`shintaniLift_unique`), it lies
  in the plus space (`shintaniLift_mem`), and it is the explicit adjoint of the Shimura lift (`shintani_adjoint_explicit`).

**Index shift.** Matrix entries are 0-based.
-/
import ModularFormsKB.HalfIntegral.Abstract.BinaryForms
import ModularFormsKB.HalfIntegral.Abstract.Kohnen
import Mathlib.NumberTheory.Pell
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Basic.Denumerable

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup ModularForm
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- **The Kronecker symbol at an integer:** $\left(\frac Dm\right) = \left(\frac D{|m|}\right)$ for $m \ge 0$ and
$\operatorname{sgn}(D)\left(\frac D{|m|}\right)$ for $m < 0$ (that is, $\left(\frac D{-1}\right) = \operatorname{sgn} D$). -/
def kroneckerInt (D m : ℤ) : ℤ :=
  kroneckerDisc D m.natAbs * (if m < 0 then D.sign else 1)

namespace BinQF

/-! ### Geodesics -/

/-- **The geodesic $S_Q$, parametrized by arc length** (formula in the module docstring). Meaningful for $\Delta > 0$. -/
noncomputable def geodesic (Q : BinQF) (s : ℝ) : ℂ :=
  if Q.a = 0 then
    ((-(Q.c : ℝ) / Q.b : ℝ) : ℂ) + I * (Real.exp (SignType.sign (Q.b : ℝ) * s) : ℝ)
  else
    (((-(Q.b : ℝ) - √(Q.disc : ℝ) * Real.tanh s) / (2 * Q.a) : ℝ) : ℂ) +
      I * ((√(Q.disc : ℝ) / (2 * |(Q.a : ℝ)| * Real.cosh s) : ℝ) : ℂ)

theorem geodesic_im_pos (Q : BinQF) (hQ : 0 < Q.disc) (s : ℝ) : 0 < (Q.geodesic s).im := by
  unfold geodesic
  split_ifs with ha
  · rw [add_im, ofReal_im, zero_add, mul_comm, im_ofReal_mul, I_im, mul_one]
    exact Real.exp_pos _
  · rw [add_im, ofReal_im, zero_add, mul_comm, im_ofReal_mul, I_im, mul_one]
    have h1 : (0 : ℝ) < √(Q.disc : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hQ)
    have h2 : (0 : ℝ) < |(Q.a : ℝ)| := abs_pos.2 (by exact_mod_cast ha)
    positivity

/-- The geodesic as a path in $\mathbb H$. -/
noncomputable def geodesicH (Q : BinQF) (hQ : 0 < Q.disc) (s : ℝ) : ℍ :=
  ⟨Q.geodesic s, Q.geodesic_im_pos hQ s⟩

/-! ### The fundamental unit -/

/-- The primitive discriminant $\Delta_0 = \Delta/\gcd(a,b,c)^2$. -/
def primDisc (Q : BinQF) : ℤ := Q.disc / (Q.content : ℤ) ^ 2

open Classical in
/-- **The least $u \ge 1$ with $\Delta u^2 + 4$ a square** ($0$ if there is none, e.g. for $\Delta$ a square). -/
noncomputable def pellU (Δ : ℤ) : ℕ :=
  if h : ∃ u : ℕ, 0 < u ∧ IsSquare (Δ * (u : ℤ) ^ 2 + 4) then Nat.find h else 0

/-- For $\Delta > 0$ not a square, $t^2 - \Delta u^2 = 4$ has a solution with $u \ge 1$ (from Pell's equation). -/
theorem exists_pellU (Δ : ℤ) (h₀ : 0 < Δ) (hΔ : ¬ IsSquare Δ) :
    ∃ u : ℕ, 0 < u ∧ IsSquare (Δ * (u : ℤ) ^ 2 + 4) := by
  obtain ⟨x, y, hxy, hy⟩ := Pell.exists_of_not_isSquare h₀ hΔ
  refine ⟨2 * y.natAbs, by omega, 2 * x, ?_⟩
  push_cast
  rw [mul_pow, sq_abs]
  linear_combination (-4) * hxy

/-- **The fundamental unit** $\varepsilon_\Delta = (t + u\sqrt\Delta)/2$, $u$ = `pellU Δ`, $t = \sqrt{\Delta u^2 + 4}$. -/
noncomputable def pellUnit (Δ : ℤ) : ℝ :=
  (√((Δ : ℝ) * (pellU Δ : ℝ) ^ 2 + 4) + (pellU Δ : ℝ) * √(Δ : ℝ)) / 2

/-- **The period** $2\log\varepsilon_{\Delta_0}$ of the geodesic of $Q$ under its stabilizer. -/
noncomputable def period (Q : BinQF) : ℝ := 2 * Real.log (pellUnit Q.primDisc)

/-! ### Cycle integrals -/

open Classical in
/-- **The cycle integral** $\int_{C_Q} G(z)Q(z,1)^{k-1}dz = \Delta^{-1/2}\int G(z_Q(s))Q(z_Q(s),1)^k\,ds$, over one period
$[0, 2\log\varepsilon]$ if $\Delta$ is not a square and over $\mathbb R$ if it is; $0$ if $\Delta \le 0$. -/
noncomputable def cycleIntegral (k : ℕ) (G : ℍ → ℂ) (Q : BinQF) : ℂ :=
  if hQ : 0 < Q.disc then
    if IsSquare Q.disc then
      ((√(Q.disc : ℝ))⁻¹ : ℂ) * ∫ s : ℝ, G (Q.geodesicH hQ s) * Q.evalC (Q.geodesic s) ^ k
    else
      ((√(Q.disc : ℝ))⁻¹ : ℂ) * ∫ s in (0 : ℝ)..Q.period, G (Q.geodesicH hQ s) * Q.evalC (Q.geodesic s) ^ k
  else 0

/-! ### The genus character -/

open Classical in
/-- **The genus character** $\chi_D(Q)$: $\left(\frac Dm\right)$ for the first value $m = Q(x, y)$ prime to $D$, $(x, y)$ running
through the fixed enumeration `Denumerable.ofNat (ℤ × ℤ)`; $0$ if no value of $Q$ is prime to $D$. -/
noncomputable def genusChar (D : ℤ) (Q : BinQF) : ℤ :=
  if h : ∃ p : ℕ, IsCoprime (Q.val (Denumerable.ofNat (ℤ × ℤ) p).1 (Denumerable.ofNat (ℤ × ℤ) p).2) D then
    kroneckerInt D (Q.val (Denumerable.ofNat (ℤ × ℤ) (Nat.find h)).1 (Denumerable.ofNat (ℤ × ℤ) (Nat.find h)).2)
  else 0

end BinQF

/-- **The genus character is well defined** (Gross–Kohnen–Zagier 1987 `gkz1987`, §I.2, Prop. 1 [unverified]; classical,
going back to Gauss): if $D$ is a fundamental discriminant and $Q$ has discriminant $DD'$ with $D'$ a discriminant
($D' \equiv 0, 1 \bmod 4$), then all integers $m$ represented by $Q$ and prime to $D$ have the same Kronecker symbol
$\left(\frac Dm\right)$. -/
@[kb "gkz1987" "§I.2, Prop. 1: the genus character χ_D(Q) = (D/m), m represented by Q and prime to D, is well defined [unverified]"]
structure GenusCharacterWellDefined (D : ℤ) : Prop where
  eq : IsFundamentalDiscriminant D → ∀ (Q : BinQF) (D' : ℤ), Q.disc = D * D' → (D' % 4 = 0 ∨ D' % 4 = 1) →
    ∀ x y x' y' : ℤ, IsCoprime (Q.val x y) D → IsCoprime (Q.val x' y') D →
      kroneckerInt D (Q.val x y) = kroneckerInt D (Q.val x' y')

namespace BinQF

/-- Under `GenusCharacterWellDefined`, $\chi_D(Q) = \left(\frac Dm\right)$ for every value $m = Q(x,y)$ prime to $D$. -/
theorem genusChar_eq {D : ℤ} (hW : GenusCharacterWellDefined D) (hD : IsFundamentalDiscriminant D) {Q : BinQF}
    {D' : ℤ} (hQ : Q.disc = D * D') (hD' : D' % 4 = 0 ∨ D' % 4 = 1) {x y : ℤ} (hxy : IsCoprime (Q.val x y) D) :
    genusChar D Q = kroneckerInt D (Q.val x y) := by
  have h : ∃ p : ℕ, IsCoprime (Q.val (Denumerable.ofNat (ℤ × ℤ) p).1 (Denumerable.ofNat (ℤ × ℤ) p).2) D :=
    ⟨Encodable.encode (x, y), by rw [Denumerable.ofNat_encode]; exact hxy⟩
  rw [genusChar, dite_eq_left_of_eq_true (eq_true h)]
  exact hW.eq hD Q D' hQ hD' _ _ _ _ (Nat.find_spec h) hxy

/-- $\chi_D(Q) = 0$ if no value of $Q$ is prime to $D$. -/
theorem genusChar_eq_zero {D : ℤ} {Q : BinQF} (h : ∀ x y : ℤ, ¬ IsCoprime (Q.val x y) D) : genusChar D Q = 0 := by
  rw [genusChar, dite_eq_right_of_eq_false (eq_false fun ⟨p, hp⟩ ↦ h _ _ hp)]

/-- **Class invariance of the genus character:** $\chi_D(Q \circ g) = \chi_D(Q)$ for $g \in \mathrm{SL}_2(\mathbb Z)$. -/
theorem genusChar_comp {D : ℤ} (hW : GenusCharacterWellDefined D) (hD : IsFundamentalDiscriminant D) {Q : BinQF}
    {D' : ℤ} (hQ : Q.disc = D * D') (hD' : D' % 4 = 0 ∨ D' % 4 = 1) (g : SL(2, ℤ)) :
    genusChar D (Q.comp g) = genusChar D Q := by
  have hQ' : (Q.comp g).disc = D * D' := by rw [disc_comp_SL, hQ]
  by_cases h : ∃ x y : ℤ, IsCoprime ((Q.comp g).val x y) D
  · obtain ⟨x, y, hxy⟩ := h
    rw [genusChar_eq hW hD hQ' hD' hxy]
    rw [val_comp] at hxy ⊢
    exact (genusChar_eq hW hD hQ hD' hxy).symm
  · push Not at h
    rw [genusChar_eq_zero h, genusChar_eq_zero]
    intro x y hxy
    obtain ⟨x', y', hx'⟩ := (Equiv.symm (⟨g, rfl⟩ : Equiv Q (Q.comp g))).represents x y
    exact h x' y' (hx' ▸ hxy)

/-! ### Classes of forms of a given discriminant -/

/-- Forms of discriminant $\Delta$. -/
def OfDisc (Δ : ℤ) : Type := {Q : BinQF // Q.disc = Δ}

/-- Proper equivalence on forms of discriminant $\Delta$. -/
def ofDiscSetoid (Δ : ℤ) : Setoid (OfDisc Δ) := Setoid.comap Subtype.val equivSetoid

/-- **Proper equivalence classes** $\mathcal Q_\Delta/\mathrm{SL}_2(\mathbb Z)$ of forms of discriminant $\Delta$. -/
def Classes (Δ : ℤ) : Type := Quotient (ofDiscSetoid Δ)

end BinQF

/-! ### The Shintani coefficients and the Shintani lift -/

open Classical in
/-- **The Shintani coefficient** $r_{k,D}(G; n) = \sum_{Q \in \mathcal Q_{|D|n}/\mathrm{SL}_2(\mathbb Z)}\chi_D(Q)\int_{C_Q}G(z)Q(z,1)^{k-1}dz$
for $n \ge 1$ with $(-1)^kn \equiv 0, 1 \bmod 4$; $0$ otherwise (in particular at $n = 0$). The sum is a `finsum` over the
(finitely many) classes, each through a chosen representative. -/
noncomputable def shintaniCoeff (k : ℕ) (D : ℤ) (G : ℍ → ℂ) (n : ℕ) : ℂ :=
  if 1 ≤ n ∧ (((-1) ^ k * n : ℤ) % 4 = 0 ∨ ((-1) ^ k * n : ℤ) % 4 = 1) then
    ∑ᶠ C : BinQF.Classes (D.natAbs * n : ℤ),
      (BinQF.genusChar D (Quotient.out C).1 : ℂ) * BinQF.cycleIntegral k G (Quotient.out C).1
  else 0

/-- **The Shintani lift** $\mathcal S^*_D G(\tau) = \sum_{n\ge1} r_{k,D}(G;n)\,e^{2\pi i n\tau}$ (the value of `tsum`). -/
noncomputable def shintaniLift (k : ℕ) (D : ℤ) (G : ℍ → ℂ) (τ : ℍ) : ℂ :=
  ∑' n : ℕ, shintaniCoeff k D G n * cexp (2 * π * I * n * τ)

/-- **The $D$-th Shimura lift on the plus space, on coefficients** (Kohnen 1980 `kohnen1980` [unverified];
Kohnen–Zagier 1981 `kohnenzagier1981`, §II [unverified]): $\sum_{d \mid n}\left(\frac Dd\right)d^{k-1}c\big(|D|n^2/d^2\big)$. -/
noncomputable def kzShimuraCoeff (k : ℕ) (D : ℤ) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, (kroneckerDisc D d : ℂ) * (d : ℂ) ^ (k - 1) * c (D.natAbs * (n / d) ^ 2)

/-- **Shintani's lift has the cycle-integral coefficients and lies in the plus space** (Shintani 1975 `shintani1975`;
Kohnen–Zagier 1981 `kohnenzagier1981`, §II, Prop. and Thm. 3 [unverified]): for $k \ge 2$, $G \in S_{2k}(\mathrm{SL}_2(\mathbb Z))$
and a fundamental discriminant $D$ with $(-1)^kD > 0$, the series $\sum_{n\ge1} r_{k,D}(G;n)q^n$ is the $q$-expansion of a
form in $S^+_{k+1/2}(4)$. -/
@[kb "kohnenzagier1981" "§II: the series of cycle-integral coefficients r_{k,D}(G;n) of a level one cusp form lies in S⁺_{k+1/2}(4) (Shintani 1975) [unverified]"]
structure ShintaniCycleFormula (M : MultiplierSystem) (k : ℕ) : Prop where
  mem : 2 ≤ k → ∀ D : ℤ, IsFundamentalDiscriminant D → 0 < (-1) ^ k * D →
    ∀ G : CuspForm 𝒮ℒ (2 * k : ℕ), ∃ g ∈ M.plusCuspForms k 1 1, Abstract.HasQExp g (shintaniCoeff k D G)

/-- **Shintani's lift is adjoint to the Shimura lift** (Shintani 1975 `shintani1975`; Kohnen–Zagier 1981
`kohnenzagier1981`, §II [unverified]): for $k \ge 2$ and $D$ as above there is a constant $\lambda_{k,D} \ne 0$ such that for
$g \in S^+_{k+1/2}(4)$ with coefficients $c$, any $F \in S_{2k}(\mathrm{SL}_2(\mathbb Z))$ with coefficients
$b(n) = $ `kzShimuraCoeff k D c n` ($n \ge 1$), any $G \in S_{2k}(\mathrm{SL}_2(\mathbb Z))$ and any $g^* \in S^+_{k+1/2}(4)$ with the
cycle-integral coefficients of $G$,
$$ \langle F, G\rangle = \lambda_{k,D}\,\langle g, g^*\rangle, $$
with $\langle\cdot,\cdot\rangle$ = `peterssonReps` on $\mathrm{SL}_2(\mathbb Z)$ (weight $2k$) and on $\Gamma_0(4)$ through `gamma0FourReps`
(weight $k+\tfrac12$), both conjugate-linear in the first argument. The value of $\lambda_{k,D}$ (a power of $2$, a binomial
coefficient, $\pi$ and $|D|^{1/2-k}$ in Kohnen–Zagier's normalization) is not stated: it depends on the orientation of the
cycles and on normalizations not yet checked against the source. -/
@[kb "kohnenzagier1981" "§II: ⟨S_D g, G⟩ = λ_{k,D} ⟨g, S*_D G⟩ with S*_D G the cycle-integral series (Shintani 1975) [unverified]"]
structure ShintaniShimuraAdjoint (M : MultiplierSystem) (k : ℕ) : Prop where
  adjoint : 2 ≤ k → ∀ D : ℤ, IsFundamentalDiscriminant D → 0 < (-1) ^ k * D →
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ g ∈ M.plusCuspForms k 1 1, ∀ c : ℕ → ℂ, Abstract.HasQExp g c →
      ∀ (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ), Abstract.HasQExp F b → (∀ n, 1 ≤ n → b n = kzShimuraCoeff k D c n) →
        ∀ G : CuspForm 𝒮ℒ (2 * k : ℕ), ∀ gs ∈ M.plusCuspForms k 1 1, Abstract.HasQExp gs (shintaniCoeff k D G) →
          peterssonReps [1] (2 * k) F G = lam * peterssonReps gamma0FourReps ((k : ℝ) + 1 / 2) g gs

/-- A function with a $q$-expansion is determined by it. -/
theorem Abstract.HasQExp.unique {f g : ℍ → ℂ} {a : ℕ → ℂ} (hf : Abstract.HasQExp f a) (hg : Abstract.HasQExp g a) :
    f = g :=
  funext fun τ ↦ (hf τ).unique (hg τ)

/-- **The Shintani lift is the only function with the cycle-integral coefficients.** -/
theorem shintaniLift_unique {k : ℕ} {D : ℤ} {G g : ℍ → ℂ} (hg : Abstract.HasQExp g (shintaniCoeff k D G)) :
    g = shintaniLift k D G :=
  funext fun τ ↦ ((hg τ).tsum_eq).symm

/-- **The Shintani lift lies in the plus space** and has the cycle-integral coefficients (from `ShintaniCycleFormula`). -/
theorem shintaniLift_mem {M : MultiplierSystem} {k : ℕ} (h : ShintaniCycleFormula M k) (hk : 2 ≤ k) {D : ℤ}
    (hD : IsFundamentalDiscriminant D) (hDk : 0 < (-1) ^ k * D) (G : CuspForm 𝒮ℒ (2 * k : ℕ)) :
    shintaniLift k D G ∈ M.plusCuspForms k 1 1 ∧ Abstract.HasQExp (shintaniLift k D G) (shintaniCoeff k D G) := by
  obtain ⟨g, hg, hq⟩ := h.mem hk D hD hDk G
  rw [← shintaniLift_unique hq]
  exact ⟨hg, hq⟩

/-- **The explicit adjoint** (from `ShintaniCycleFormula` and `ShintaniShimuraAdjoint`): for $g \in S^+_{k+1/2}(4)$, its
$D$-th Shimura lift $F$ and every $G \in S_{2k}(\mathrm{SL}_2(\mathbb Z))$, $\langle F, G\rangle = \lambda_{k,D}\langle g, \mathcal S^*_DG\rangle$ with
$\mathcal S^*_D G$ = `shintaniLift k D G`, the series of cycle integrals. This is the content missing from `ShintaniAdjoint`. -/
theorem shintani_adjoint_explicit {M : MultiplierSystem} {k : ℕ} (h₁ : ShintaniCycleFormula M k)
    (h₂ : ShintaniShimuraAdjoint M k) (hk : 2 ≤ k) {D : ℤ} (hD : IsFundamentalDiscriminant D)
    (hDk : 0 < (-1) ^ k * D) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ g ∈ M.plusCuspForms k 1 1, ∀ c : ℕ → ℂ, Abstract.HasQExp g c →
      ∀ (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ), Abstract.HasQExp F b →
        (∀ n, 1 ≤ n → b n = kzShimuraCoeff k D c n) → ∀ G : CuspForm 𝒮ℒ (2 * k : ℕ),
          shintaniLift k D G ∈ M.plusCuspForms k 1 1 ∧
          peterssonReps [1] (2 * k) F G =
            lam * peterssonReps gamma0FourReps ((k : ℝ) + 1 / 2) g (shintaniLift k D G) := by
  obtain ⟨lam, hlam, hadj⟩ := h₂.adjoint hk D hD hDk
  refine ⟨lam, hlam, fun g hg c hc F b hb hbc G ↦ ?_⟩
  obtain ⟨hmem, hq⟩ := shintaniLift_mem h₁ hk hD hDk G
  exact ⟨hmem, hadj g hg c hc F b hb hbc G _ hmem hq⟩

end ModularFormsKB.HalfIntegral
