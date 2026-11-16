/-
# `KohnenTPlusFourStable` from one $q$-expansion identity

Loose end LE-MF-0268.

Kohnen defines $T^+(4)$ on the plus space as $\tfrac32\,\mathrm{pr}\circ U(4)$ (Kohnen 1980 `kohnen1980`, §2
[unverified]). With $\mathrm{pr} = \tfrac13 + \tfrac2{3\alpha}L$ (`kohnenPr`) this is
$$T^+(4)g = \tfrac12\,U(4)g + \alpha^{-1}L(U(4)g), \qquad L = W(4)U(4),\ \alpha = (-1)^{\lfloor(k+1)/2\rfloor}2^k .$$
Both $U(4)$ and $L$ preserve $S_{k+1/2}(4)$ for the theta multiplier (`kohnenU4_mem_cuspForms`,
`kohnenL_mem_cuspForms`), so the stability of $S^+_{k+1/2}(4)$ under Kohnen's coefficient formula `heckeTPlusFour` reduces
to the $q$-expansion of $L(U(4)g)$ for $g \in S^+_{k+1/2}(4)$:

* `KohnenLUFour` (named input, LE-MF-0286): if $g \in S^+_{k+1/2}(4)$ has coefficients $c$, then $L(U(4)g)$ has
  coefficients $\alpha\,(T^+(4)c)(n) - \tfrac\alpha2\,c(4n)$. Checked numerically for
  $\theta(\tau)E_4(4\tau)$, $\theta(\tau)E_6(4\tau)$ and Cohen's $H_{r+1/2}$, $r = 2, \dots, 5$, to relative error $10^{-11}$
  (these are modular, not cusp, forms; the identity is the same).
* `kohnenTPlusFourStable_of_LUFour`: `KohnenLUFour` implies `KohnenTPlusFourStable` for the theta multiplier.
* `kohnenIsomorphism_of_trace_LUFour` (H2), `kohnenZagier_of_trace_LUFour` and `waldspurgerPlus_of_trace_LUFour` (H3):
  the headlines with `KohnenTPlusFourStable` replaced by `KohnenLUFour`.

What `KohnenLUFour` still needs (LE-MF-0286): $L(U(4)g) = W(4)U(16)g$ is the form $g$ seen at the cusps $0$ and $1/2$ of
$\Gamma_0(4)$ ($W(4)U(4)W(4)$ is a sum over $\begin{psmallmatrix}4&0\\-4j&1\end{psmallmatrix}$, $j = 0, \dots, 3$), i.e.
the same cusp computation that `KohnenPlusEigen` needs.
-/
import ModularFormsKB.HalfIntegral.KohnenW4U4
import ModularFormsKB.HalfIntegral.KohnenTrace
import ModularFormsKB.HalfIntegral.KohnenZagierPlusAdjoint

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups

local notation "ℍ" => UpperHalfPlane

/-- **The $q$-expansion of $W(4)U(4)U(4)g$ on the plus space** (Kohnen 1980 `kohnen1980`, §2, the definition
$T^+(4) = \tfrac32\,\mathrm{pr}\,U(4)$ and Prop. 2 [unverified]; constants in our normalization, checked numerically): for
$g \in S^+_{k+1/2}(4)$ with coefficients $c$, $L(U(4)g)$ has coefficients $\alpha\,(T^+(4)c)(n) - \tfrac\alpha2\,c(4n)$. -/
@[kb "kohnen1980" "§2: T⁺(4) = (3/2) pr U(4), i.e. W(4)U(4)U(4)g = α T⁺(4)g − (α/2) U(4)g on S⁺_{k+1/2}(4) [unverified]"]
structure KohnenLUFour (M : MultiplierSystem) (k : ℕ) : Prop where
  coeff : ∀ g ∈ M.plusCuspForms k 1 1, ∀ c : ℕ → ℂ, Abstract.HasQExp g c →
    Abstract.HasQExp (kohnenL k (kohnenU4 g))
      (fun n ↦ kohnenAlpha k * heckeTPlusFour k c n - kohnenAlpha k / 2 * c (4 * n))

/-- **`KohnenLUFour` implies `KohnenTPlusFourStable`** for the theta multiplier: $T^+(4)g = \tfrac12U(4)g +
\alpha^{-1}L(U(4)g)$ lies in $S_{k+1/2}(4)$ and its coefficients `heckeTPlusFour k c` satisfy the plus condition. -/
theorem kohnenTPlusFourStable_of_LUFour {k : ℕ} (h : KohnenLUFour thetaMultiplierSystem k) :
    KohnenTPlusFourStable thetaMultiplierSystem k := by
  refine ⟨fun _ g hg c hc ↦ ?_⟩
  have hU : kohnenU4 g ∈ thetaMultiplierSystem.cuspForms k 1 1 := kohnenU4_mem_cuspForms k hg.1
  have hL : kohnenL k (kohnenU4 g) ∈ thetaMultiplierSystem.cuspForms k 1 1 := kohnenL_mem_cuspForms k hU
  set α := kohnenAlpha k
  have hα : α ≠ 0 := kohnenAlpha_ne_zero k
  set g' := α⁻¹ • kohnenL k (kohnenU4 g) + (1 / 2 : ℂ) • kohnenU4 g
  have hq : Abstract.HasQExp g' (heckeTPlusFour k c) := by
    have h1 := Abstract.hasQExp_smul α⁻¹ (h.coeff g hg c hc)
    have h2 := Abstract.hasQExp_smul (1 / 2 : ℂ) (hasQExp_kohnenU4 hc)
    have h3 := Abstract.hasQExp_add h1 h2
    have e : (α⁻¹ • fun n ↦ α * heckeTPlusFour k c n - α / 2 * c (4 * n)) +
        (1 / 2 : ℂ) • (fun n ↦ c (4 * n)) = heckeTPlusFour k c := by
      funext n
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    rwa [e] at h3
  have hmem : g' ∈ thetaMultiplierSystem.cuspForms k 1 1 :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hL) (Submodule.smul_mem _ _ hU)
  exact ⟨g', ⟨hmem, heckeTPlusFour k c, hq, heckeTPlusFour_mem_plusSeq k c⟩, hq⟩

/-- **H2 (Kohnen's isomorphism) for the theta multiplier** from `KohnenTraceIdentity` and `KohnenLUFour`. -/
@[kb "kohnen1980" "Thm. 1 for the theta multiplier, from the trace identity and the q-expansion of W(4)U(4)U(4) on S⁺ [unverified]"]
theorem kohnenIsomorphism_of_trace_LUFour (k : ℕ) (h : KohnenTraceIdentity k)
    (hL : KohnenLUFour thetaMultiplierSystem k) : KohnenIsomorphism thetaMultiplierSystem k :=
  kohnenIsomorphism_of_trace h (kohnenTPlusFourStable_of_LUFour hL)

/-- **H3 (Kohnen–Zagier) for the theta multiplier** from `KohnenTraceIdentity`, `KohnenLUFour` and `KohnenAdjointCoeff`. -/
@[kb "kohnenzagier1981" "Kohnen–Zagier formula, theta multiplier, from the trace identity, the U(4) identity and the kernel coefficient [unverified]"]
theorem kohnenZagier_of_trace_LUFour (k : ℕ) (h : KohnenTraceIdentity k)
    (hL : KohnenLUFour thetaMultiplierSystem k)
    (hcoeff : ∀ D, KohnenDisc k D → ∀ Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ,
      KohnenAdjoint thetaMultiplierSystem k D Sstar → KohnenAdjointCoeff thetaMultiplierSystem k D Sstar) :
    KohnenZagier thetaMultiplierSystem k :=
  kohnenZagier_of_trace_stable k h (kohnenTPlusFourStable_of_LUFour hL) hcoeff

/-- **H3 (Waldspurger's plus-space theorem) for the theta multiplier**, from the same inputs as
`kohnenZagier_of_trace_LUFour`. -/
@[kb "kohnenzagier1981" "Waldspurger's theorem on the plus space, from the trace identity, the U(4) identity and the kernel coefficient [unverified]"]
theorem waldspurgerPlus_of_trace_LUFour (k : ℕ) (h : KohnenTraceIdentity k)
    (hL : KohnenLUFour thetaMultiplierSystem k)
    (hcoeff : ∀ D, KohnenDisc k D → ∀ Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ,
      KohnenAdjoint thetaMultiplierSystem k D Sstar → KohnenAdjointCoeff thetaMultiplierSystem k D Sstar) :
    WaldspurgerPlus thetaMultiplierSystem k :=
  waldspurgerPlus_of_trace_stable k h (kohnenTPlusFourStable_of_LUFour hL) hcoeff

end ModularFormsKB.HalfIntegral
