import ModularFormsKB.Milne.Ch8.EllipticModuli
import ModularFormsKB.Milne.Ch8.FineModuli

/-!
# Milne, Chapter 8: Theorem 8.8 for $N \ge 3$ from the fine moduli variety

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 8, Theorem 8.8 and the
remark after it (pdf p. 100): for $N \ge 3$ the moduli problem $\mathcal E_N$ is representable, and its solution is a
fine moduli variety.

- `LevelFineModuli k N` (named statement, cited input): for $N$ invertible in $k$ and $\zeta$ a primitive $N$-th root
  of $1$, $\mathcal E_N$ is represented by a variety over $k$ (Katz and Mazur, *Arithmetic Moduli of Elliptic Curves*,
  Corollary 4.7.2 and Theorem 5.1.1, for $N \ge 3$; Deligne and Rapoport, IV.2). It is strictly stronger than the
  existence of a solution (Example 8.9 shows a solution need not be fine).
- `levelModuliSolution_of_levelFineModuli`: for $N \ge 3$, `LevelFineModuli k N → LevelModuliSolution k N`, through
  `isModuliSolution_of_iso`.
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

namespace ModularFormsKB.Milne

variable (k : Type u) [Field k] (N : ℕ) [NeZero N]

/-- **Representability of $\mathcal E_N$** (named statement, cited input; Katz and Mazur, Corollary 4.7.2 and
Theorem 5.1.1): for $N \ge 3$ invertible in the algebraically closed field $k$ and $\zeta$ a primitive $N$-th root of
$1$, there is a variety $M$ over $k$ with $\mathcal E_N \cong h_M$. (For $N = 2$ this is false:
`Ch8Counterexample.not_exists_isFineModuliSolution`.) -/
@[kb "milne2017mf" "Section 8, remark after Theorem 8.8: E_N is representable for N ≥ 3 (pdf p. 100)"]
structure LevelFineModuli [IsAlgClosed k] : Prop where
  represented : 3 ≤ N → ∀ (hN : (N : k) ≠ 0) (ζ : k), IsPrimitiveRoot ζ N → ∃ M : Variety k,
    Nonempty (levelNFunctor hN ζ ≅ yoneda.obj M ⋙ uliftFunctor.{u + 1})

/-- **Theorem 8.8 from representability**: a representing variety of $\mathcal E_N$ is a (fine) solution. -/
theorem levelModuliSolution_of_levelFineModuli [IsAlgClosed k] (hN3 : 3 ≤ N) (h : LevelFineModuli k N) :
    LevelModuliSolution k N := by
  refine ⟨fun hN ζ hζ ↦ ?_⟩
  obtain ⟨M, ⟨η⟩⟩ := h.represented hN3 hN ζ hζ
  exact ⟨M, pointEquivOfIso η, isModuliSolution_of_iso η⟩

end ModularFormsKB.Milne
