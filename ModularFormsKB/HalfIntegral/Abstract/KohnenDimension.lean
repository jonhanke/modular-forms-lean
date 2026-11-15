/-
# The dimension input of Kohnen's isomorphism, reduced

The first round stated the named input `KohnenDimension`
(both spaces finite-dimensional, of equal dimension). Two thirds of it are now proved or redundant:
- $S_{2k}(\mathrm{SL}_2(\mathbb Z))$ is finite-dimensional (`finiteDimensional_cuspForm_levelOne`): division by the
  discriminant is Mathlib's isomorphism `CuspForm.discriminantEquiv` onto $M_{2k-12}(\mathrm{SL}_2(\mathbb Z))$, which is
  finite-dimensional by Mathlib's level one dimension formula;
- finite dimension of $S^+_{k+1/2}(4)$ and $\dim S^+ \le \dim S_{2k}(1)$ follow from the injective combination of lifts
  (`kohnenIsomorphism_of_le`).

What remains is the named input `KohnenDimensionLe`: $\dim S_{2k}(1) \le \dim S^+_{k+1/2}(4)$. It holds for $k \le 5$ and
$k = 7$ (`kohnenDimensionLe_small`), where $S_{2k}(1) = 0$; the explicit dimension of $S_w(1)$ for even $w$ is
`finrank_cuspForm_levelOne_even`.

**Proved here.** `kohnenIsomorphism_of_dimLe`: `KohnenDLift`, `KohnenDimensionLe` and `KohnenLiftsInjective` imply
`KohnenIsomorphism`; `kohnenDimension_of_inputs`: the same inputs imply the first round's `KohnenDimension`.
-/
import ModularFormsKB.HalfIntegral.Abstract.KohnenReduction
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup ModularForm

/-- **Level one cusp forms are finite-dimensional:** $S_k(\mathrm{SL}_2(\mathbb Z)) \cong M_{k-12}(\mathrm{SL}_2(\mathbb Z))$
by division by $\Delta$ (`CuspForm.discriminantEquiv`), and the latter is finite-dimensional. -/
instance finiteDimensional_cuspForm_levelOne (k : ℤ) : FiniteDimensional ℂ (CuspForm 𝒮ℒ k) :=
  LinearEquiv.finiteDimensional CuspForm.discriminantEquiv.symm

/-- $\dim S_k(\mathrm{SL}_2(\mathbb Z)) = \dim M_{k-12}(\mathrm{SL}_2(\mathbb Z))$. -/
theorem finrank_cuspForm_levelOne (k : ℤ) :
    Module.finrank ℂ (CuspForm 𝒮ℒ k) = Module.finrank ℂ (ModularForm 𝒮ℒ (k - 12)) :=
  CuspForm.discriminantEquiv.finrank_eq

/-- **The dimension of $S_w(\mathrm{SL}_2(\mathbb Z))$ for even $w$:** $0$ for $w < 12$; otherwise $\lfloor (w-12)/12\rfloor$
if $w - 12 \equiv 2 \bmod 12$ and $\lfloor (w-12)/12\rfloor + 1$ if not (Mathlib's `dimension_level_one` in weight
$w - 12$). -/
theorem finrank_cuspForm_levelOne_even {w : ℕ} (hw : Even w) :
    Module.finrank ℂ (CuspForm 𝒮ℒ (w : ℤ)) =
      if w < 12 then 0 else if w - 12 ≡ 2 [MOD 12] then (w - 12) / 12 else (w - 12) / 12 + 1 := by
  split_ifs with h12 h2
  · exact Module.finrank_eq_zero_of_rank_eq_zero (CuspForm.rank_eq_zero_of_weight_lt_twelve (by omega))
  all_goals
    rw [finrank_cuspForm_levelOne, show (w : ℤ) - 12 = ((w - 12 : ℕ) : ℤ) by omega]
    have hev : Even (w - 12) := by
      obtain ⟨m, hm⟩ := hw
      exact ⟨m - 6, by omega⟩
    apply Module.finrank_eq_of_rank_eq
    rw [dimension_level_one (w - 12) hev]
  · simp [h2]
  · simp [h2]

/-- $S_{2k}(\mathrm{SL}_2(\mathbb Z)) = 0$ for $k \le 5$ and $k = 7$. -/
theorem finrank_cuspForm_levelOne_small {k : ℕ} (hk : k ≤ 5 ∨ k = 7) :
    Module.finrank ℂ (CuspForm 𝒮ℒ ((2 * k : ℕ) : ℤ)) = 0 := by
  rw [finrank_cuspForm_levelOne_even (even_two_mul k)]
  rcases hk with hk | rfl
  · simp [show 2 * k < 12 by omega]
  · decide

/-- **$\dim S_{2k}(1) \le \dim S^+_{k+1/2}(4)$** (Kohnen 1980 `kohnen1980`, §2–§3, via the trace formula [unverified]):
the half of the dimension equality that does not follow from the injective combination of lifts. -/
@[kb "kohnen1980" "dim S_{2k}(1) ≤ dim S⁺_{k+1/2}(4) (half of dim S⁺_{k+1/2}(4) = dim S_{2k}(1)) [unverified]"]
structure KohnenDimensionLe (M : MultiplierSystem) (k : ℕ) : Prop where
  le : 1 ≤ k → Module.finrank ℂ (CuspForm 𝒮ℒ (2 * k : ℕ)) ≤ Module.finrank ℂ (M.plusCuspForms k 1 1)

variable (M : MultiplierSystem) (k : ℕ)

/-- **`KohnenDimensionLe` holds for $k \le 5$ and $k = 7$**, since then $S_{2k}(1) = 0$. -/
theorem kohnenDimensionLe_small (hk : k ≤ 5 ∨ k = 7) : KohnenDimensionLe M k :=
  ⟨fun _ ↦ by rw [finrank_cuspForm_levelOne_small hk]; exact Nat.zero_le _⟩

/-- **Kohnen's isomorphism from the lifts, one dimension inequality, and an injective combination of lifts.** -/
@[kb "kohnen1980" "proof of Thm. 1: the isomorphism from the D-th lifts, dim S_{2k}(1) ≤ dim S⁺ and injectivity [unverified]"]
theorem kohnenIsomorphism_of_dimLe (hL : ∀ D, KohnenDisc k D → KohnenDLift M k D) (hdim : KohnenDimensionLe M k)
    (hinj : KohnenLiftsInjective M k) : KohnenIsomorphism M k :=
  kohnenIsomorphism_of_le M k hL (fun _ ↦ inferInstance) hdim.le hinj

/-- **The first round's dimension input follows** from the lifts, the dimension inequality and injectivity. -/
theorem kohnenDimension_of_inputs (hL : ∀ D, KohnenDisc k D → KohnenDLift M k D) (hdim : KohnenDimensionLe M k)
    (hinj : KohnenLiftsInjective M k) : KohnenDimension M k := by
  have hiso := (kohnenIsomorphism_of_dimLe M k hL hdim hinj).iso
  refine ⟨fun hk ↦ ?_, fun _ ↦ inferInstance, fun hk ↦ ?_⟩
  · obtain ⟨Φ, -⟩ := hiso hk
    exact LinearEquiv.finiteDimensional Φ.symm
  · obtain ⟨Φ, -⟩ := hiso hk
    exact Φ.finrank_eq

end ModularFormsKB.HalfIntegral
