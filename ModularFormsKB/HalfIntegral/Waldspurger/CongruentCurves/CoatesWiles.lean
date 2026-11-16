/-
# The Coates–Wiles theorem, as cited, and its case $E_n$

**The cited theorem** (`CoatesWilesCM`; Coates–Wiles 1977 `coateswiles1977`, Theorem 1 [unverified]). Let $E$ be an
elliptic curve over $\mathbb Q$ with complex multiplication by the ring of integers of an imaginary quadratic field
$K$ (necessarily of class number one). If $L(E, 1) \ne 0$ then $E(\mathbb Q)$ is finite.

Over $\mathbb Q$, "complex multiplication by the maximal order of $K$" is a condition on the $j$-invariant alone:
it holds exactly for the nine values $j(\mathcal O_K)$, $K = \mathbb Q(\sqrt{-d})$ with
$d \in \{3, 4, 7, 8, 11, 19, 43, 67, 163\}$ (`cmMaximalJ`; Silverman, *Advanced Topics*, Appendix A §3
[unverified]). The value of $L(E, 1)$ is taken, as in Tau Ceti's `WeierstrassCurve.BirchSwinnertonDyer`, from every
continuation of the Dirichlet series of Mathlib's `WeierstrassCurve.LFunction` to a connected open set containing
$1$. (For a non-minimal model this series differs from $L(E, s)$ by finitely many Euler factors, none of which
vanishes at $s = 1$, so the hypothesis $F(1) \ne 0$ does not depend on the model.)

**Proved here** (`coatesWilesRank_of_coatesWilesCM`): the case $E = E_n$, $y^2 = x^3 - n^2 x$, whose $j$-invariant
is $1728 = j(\mathbb Z[i])$ (`j_congruentCurve`). This is the statement `CoatesWilesRank` used by the headline H4,
which until this job was itself the named input.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.CongruentL

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open WeierstrassCurve

/-- The $j$-invariants of the elliptic curves over $\mathbb Q$ with complex multiplication by the maximal order of an
imaginary quadratic field: $j(\mathcal O_K)$ for the nine fields of class number one, $K = \mathbb Q(\sqrt{-3})$,
$\mathbb Q(i)$, $\mathbb Q(\sqrt{-7})$, $\mathbb Q(\sqrt{-2})$, $\mathbb Q(\sqrt{-11})$, $\mathbb Q(\sqrt{-19})$,
$\mathbb Q(\sqrt{-43})$, $\mathbb Q(\sqrt{-67})$, $\mathbb Q(\sqrt{-163})$ in this order. -/
def cmMaximalJ : Set ℚ :=
  {0, 1728, -3375, 8000, -32768, -884736, -884736000, -147197952000, -262537412640768000}

/-- **The Coates–Wiles theorem** (Coates–Wiles 1977 `coateswiles1977`, Theorem 1 [unverified]): an elliptic curve
$E$ over $\mathbb Q$ with complex multiplication by the maximal order of an imaginary quadratic field and
$L(E, 1) \ne 0$ has finitely many rational points. $L(E, 1)$ is the value at $1$ of any continuation of the
$L$-series of Mathlib's `E.LFunction` to a connected open set containing $1$ (the convention of Tau Ceti's
`WeierstrassCurve.BirchSwinnertonDyer`). A cited theorem, not proved here (its proof is by elliptic units and
Iwasawa theory). -/
@[kb "coateswiles1977" "Theorem 1: E/Q with CM by the ring of integers of an imaginary quadratic field, L(E,1) ≠ 0 ⇒ E(Q) finite [unverified]"]
structure CoatesWilesCM : Prop where
  finite : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], E.j ∈ cmMaximalJ →
    ∀ ⦃F : ℂ → ℂ⦄ ⦃U : Set ℂ⦄, LSeries.IsContinuationOn (fun m ↦ (E.LFunction m : ℂ)) F U → 1 ∈ U →
      F 1 ≠ 0 → Finite E.toAffine.Point

/-- $j(E_n) = 1728$: $c_4 = 48n^2$ and $\Delta = 64n^6$. -/
theorem j_congruentCurve (n : ℕ) [NeZero n] : (congruentCurve n).j = 1728 := by
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hc4 : (congruentCurve n).c₄ = 48 * (n : ℚ) ^ 2 := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, congruentCurve_a₁,
      congruentCurve_a₂, congruentCurve_a₃, congruentCurve_a₄]
    ring
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, coe_Δ', congruentCurve_Δ, hc4]
  field_simp
  ring

theorem j_congruentCurve_mem (n : ℕ) [NeZero n] : (congruentCurve n).j ∈ cmMaximalJ := by
  rw [j_congruentCurve]; simp [cmMaximalJ]

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
