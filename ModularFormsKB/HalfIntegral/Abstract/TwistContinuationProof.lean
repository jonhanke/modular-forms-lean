/-
# Hecke's continuation of the twisted $L$-series (proof of `TwistContinuation`)

Proves the named input `TwistContinuation k` of `Abstract/TwistL.lean` for every $k$ from Tau Ceti
(Tau Ceti `CuspForm.twist`, `CuspForm.qExpansion_twist_coeff`, `CuspForm.hasEntireExtension_qExpansion_coeff`,
`TauCeti.kroneckerChar`).

For a fundamental discriminant $D$ with $M = |D|$, the Kronecker character `kroneckerChar ℂ D` is a Dirichlet
character modulo $M$ with values $\left(\frac Dn\right)$ at $n$; the level-one cusp form $F$, viewed as a cusp form
for $\Gamma_1(1)$, twists to a cusp form for $\Gamma_1(M^2)$ whose $q$-coefficients are $\left(\frac Dn\right) b(n)$.
The Tau Ceti entire continuation of the $L$-series of that twist is the required $L$.

- `kroneckerDisc_eq_kroneckerSym`: our `kroneckerDisc` agrees with Tau Ceti's Kronecker symbol for $n \ge 1$.
- `twistContinuation`: the headline.
-/
import ModularFormsKB.HalfIntegral.Abstract.TwistL
import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
import TauCeti.NumberTheory.ModularForms.Twist.Basic
import TauCeti.NumberTheory.ModularForms.LFunction.Basic
import TauCeti.NumberTheory.LSeries.EntireExtension
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup ModularForm Filter Asymptotics
open Matrix.SpecialLinearGroup
open scoped Real

theorem kroneckerTwo_eq_chi8 (D : ℤ) : kroneckerTwo D = ZMod.χ₈ D := by
  rw [ZMod.χ₈_int_eq_if_mod_eight, kroneckerTwo]
  have : (2 : ℤ) ∣ D ↔ D % 2 = 0 := Int.dvd_iff_emod_eq_zero
  simp only [this]

/-- Our Kronecker symbol is Tau Ceti's `kroneckerSym` for $n \ge 1$. -/
theorem kroneckerDisc_eq_kroneckerSym (D : ℤ) {n : ℕ} (hn : n ≠ 0) :
    kroneckerDisc D n = TauCeti.kroneckerSym D n := by
  have hodd : Odd (n / 2 ^ n.factorization 2) :=
    Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two hn)
  have hm0 : n / 2 ^ n.factorization 2 ≠ 0 := (Nat.ordCompl_pos 2 hn).ne'
  have h := Nat.ordProj_mul_ordCompl_eq_self n 2
  have key := TauCeti.kroneckerSym_mul_right D (b := ((2 ^ n.factorization 2 : ℕ) : ℤ))
    (c := ((n / 2 ^ n.factorization 2 : ℕ) : ℤ)) (by positivity) (by exact_mod_cast hm0)
  rw [← Nat.cast_mul, h, Nat.cast_pow, Nat.cast_ofNat, TauCeti.kroneckerSym_pow_right,
    TauCeti.kroneckerSym_two_right, TauCeti.kroneckerSym_eq_jacobiSym D hodd] at key
  rw [key, kroneckerDisc, kroneckerTwo_eq_chi8]

/-- **Hecke's continuation of the twisted $L$-series**, proved from Tau Ceti. -/
theorem twistContinuation (k : ℕ) : TwistContinuation k := by
  refine ⟨fun F b hF D hD ↦ ?_⟩
  have hD0 : D ≠ 0 := by
    rcases hD with ⟨h4, -⟩ | ⟨m, rfl, -, hm⟩
    · rintro rfl; simp at h4
    · have := hm.ne_zero; omega
  have hD4 : D ≡ 0 [ZMOD 4] ∨ D ≡ 1 [ZMOD 4] := by
    rcases hD with ⟨h4, -⟩ | ⟨m, rfl, -, -⟩
    · right; simpa [Int.ModEq] using h4
    · left; exact Int.modEq_zero_iff_dvd.mpr ⟨m, rfl⟩
  have : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD0⟩
  set M := D.natAbs with hM
  let G : CuspForm ((Gamma1 1).map (mapGL ℝ)) ((2 * k : ℕ) : ℤ) :=
    CuspForm.restrict (TauCeti.Gamma1_one_map_eq_SL).le F
  let T := CuspForm.twist (M := M) (N := 1) (L := M * M)
    (fun x ↦ TauCeti.kroneckerChar ℂ D hD4 hD0 x) (by simp) dvd_rfl G
  have hcoef : ∀ {n : ℕ}, n ≠ 0 → (UpperHalfPlane.qExpansion 1 T).coeff n = twistCoeff D b n := by
    intro n hn
    rw [CuspForm.qExpansion_twist_coeff]
    rw [TauCeti.kroneckerChar_natCast, ← kroneckerDisc_eq_kroneckerSym D hn, twistCoeff,
      hasQExp_coeff_eq_qExpansion F hF n]
    rfl
  have hw := CuspForm.hasEntireExtension_qExpansion_coeff T
  have hwidth : ((Gamma1 (M * M)).map (mapGL ℝ)).strictWidthInfty = 1 := by simp
  rw [hwidth] at hw
  obtain ⟨Lf, hdiff, hag⟩ := hw.exists_extension
  have habs : LSeries.abscissaOfAbsConv (fun n ↦ (UpperHalfPlane.qExpansion 1 T).coeff n) =
      LSeries.abscissaOfAbsConv (twistCoeff D b) :=
    LSeries.abscissaOfAbsConv_congr (fun hn ↦ hcoef hn)
  have hle : LSeries.abscissaOfAbsConv (twistCoeff D b) ≤ ((k : ℝ) + 1 : ℝ) := by
    refine LSeries.abscissaOfAbsConv_le_of_isBigO_rpow (x := (k : ℝ)) ?_
    have h1 : twistCoeff D b =O[atTop] b :=
      IsBigO.of_bound 1 (Eventually.of_forall fun n ↦ by simpa using norm_twistCoeff_le D b n)
    simpa using h1.trans (cuspForm_coeff_isBigO k F hF)
  refine ⟨Lf, hdiff, fun s hs ↦ ?_⟩
  rw [hag (by rw [habs]; exact lt_of_le_of_lt hle (by exact_mod_cast hs))]
  exact LSeries_congr (fun hn ↦ hcoef hn) s

end ModularFormsKB.HalfIntegral
