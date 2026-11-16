/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
-/
import ModularFormsKB.HalfIntegral.ZagierKernel.SquareCycle.CuspIntegral
import ModularFormsKB.HalfIntegral.ZagierKernel.SquareCycle.Classes
import ModularFormsKB.HalfIntegral.ZagierKernel.Unfolding

/-!
# The Shintani coefficient at $|D|$ as a sum over $c \bmod |D|$

$r_{k,D}(G; |D|)$ (`shintaniCoeff k D G D.natAbs`) is a `finsum` over the classes of discriminant $D^2$, each through a
chosen representative. The classes are those of $[0, |D|, c]$, $0 \le c < |D|$ (`BinQF.exists_equiv_squareRep`,
`BinQF.eq_of_equiv_squareRep`), the genus character of the representative is $\left(\frac Dc\right)$
(`BinQF.genusChar_of_equiv_squareRep`) and its cycle integral is that of $[0, |D|, c]$ (`BinQF.cycleIntegral_comp_SL`), so
$$ r_{k,D}(G; |D|) = \sum_{0 \le c < |D|}\left(\frac Dc\right)\int_{C_{[0,|D|,c]}} G(z)\,(|D|z + c)^{k-1}\,dz. $$
-/

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups ModularForm

/-- **Step 1: the Shintani coefficient at $|D|$ as a sum over $c \bmod |D|$.** -/
theorem shintaniCoeff_natAbs_eq_sum {k : ℕ} (hk : 2 ≤ k) {D : ℤ} (hD : KohnenDisc k D)
    (G : CuspForm 𝒮ℒ (2 * k : ℕ)) :
    shintaniCoeff k D G D.natAbs =
      ∑ c ∈ Finset.range D.natAbs,
        (TauCeti.kroneckerSym D c : ℂ) * BinQF.cycleIntegral k G (BinQF.squareRep D.natAbs c) := by
  have hK := kernelIndex_natAbs hD
  have hn : 0 < D.natAbs := hK.1
  have hdisc : ((D.natAbs : ℤ) * (D.natAbs : ℕ) : ℤ) = ((D.natAbs : ℕ) : ℤ) ^ 2 := by ring
  let φ : Fin D.natAbs → BinQF.Classes ((D.natAbs : ℤ) * (D.natAbs : ℕ)) := fun c ↦
    Quotient.mk (BinQF.ofDiscSetoid _) ⟨BinQF.squareRep D.natAbs c, by rw [BinQF.disc_squareRep, hdisc]⟩
  have hinj : Function.Injective φ := by
    intro c c' h
    exact Fin.ext (BinQF.eq_of_equiv_squareRep hn c.2 c'.2 (Quotient.exact h))
  have hsurj : Function.Surjective φ := by
    intro C
    induction C using Quotient.inductionOn with
    | h Q =>
      obtain ⟨c, hc, hQc⟩ := BinQF.exists_equiv_squareRep Q.1 hn (by rw [Q.2, hdisc])
      exact ⟨⟨c, hc⟩, Quotient.sound (BinQF.Equiv.symm hQc)⟩
  let e := Equiv.ofBijective φ ⟨hinj, hsurj⟩
  have hcond : 1 ≤ D.natAbs ∧ (((-1) ^ k * (D.natAbs : ℕ) : ℤ) % 4 = 0 ∨ ((-1) ^ k * (D.natAbs : ℕ) : ℤ) % 4 = 1) :=
    hK
  rw [shintaniCoeff, ite_eq_left_iff.mpr (fun h ↦ absurd hcond h), ← finsum_comp_equiv e, finsum_eq_sum_of_fintype,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  have hout : BinQF.Equiv (Quotient.out (e c)).1 (BinQF.squareRep D.natAbs c) :=
    Quotient.mk_out (s := BinQF.ofDiscSetoid _) (⟨BinQF.squareRep D.natAbs c, by
      rw [BinQF.disc_squareRep, hdisc]⟩ : BinQF.OfDisc _)
  rw [BinQF.genusChar_of_equiv_squareRep hD.1 hout]
  obtain ⟨γ, hγ⟩ := hout
  rw [hγ, BinQF.cycleIntegral_comp_SL (by omega) G _ hn _ γ]
  rw [(Quotient.out (e c)).2, hdisc]

end ModularFormsKB.HalfIntegral
