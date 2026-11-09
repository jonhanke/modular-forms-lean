import ModularFormsKB.Milne.Ch6.CosetSymmetry

/-!
# Milne, Theorem 6.1 from integrality and Kronecker's congruence

`ModularFormsKB.Milne.ModularEquation N` follows from the named statement
`ModularFormsKB.Milne.LevelTwo.CosetPolynomialArithmetic N` (an integer polynomial $F$ with
$F(j(z), Y) = \prod_{\Gamma_0(N)\gamma}(Y - j(N\gamma z))$ satisfying Kronecker's congruence for $N$ prime): everything
else (generation, degree, minimum polynomial, symmetry) is proved (`ModularEquationN.lean`, `CosetSymmetry.lean`).
-/

noncomputable section

namespace ModularFormsKB.Milne

open LevelTwo

/-- **Milne, Theorem 6.1, from the arithmetic of the coset polynomial.** Everything in `ModularEquation N` except the
integrality and the congruence of the coefficients is proved unconditionally. -/
@[kb "milne2017mf" "Section 6, Theorem 6.1 (pdf p. 88), from integrality and Kronecker's congruence"]
theorem modularEquation_of_cosetPolynomialArithmetic {N : ℕ} (hN : 0 < N)
    (h : CosetPolynomialArithmetic N hN) : ModularEquation N hN := by
  have : NeZero N := NeZero.of_pos hN
  obtain ⟨Fz, hFz, hkr⟩ := h.statement
  exact modularEquation_of_eval₂_eq_Φ hN Fz hFz (fun h1 ↦ rename_swap_eq_of_eval₂_eq_Φ hN h1 hFz) hkr

end ModularFormsKB.Milne
