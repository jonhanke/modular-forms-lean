import ModularFormsKB.Milne.Ch6.X0Degree
import ModularFormsKB.Milne.Ch4.LevelOne
import ModularFormsKB.Miyake.Wave6.Discriminant

/-!
# Miyake §4.1: modular functions of level one, Theorem 4.1.7 (3)

Miyake, *Modular Forms* (Springer 1989), Theorem 4.1.7 (3), p. 101: `𝒜₀(Γ) = ℂ(J)` for
`Γ = SL₂(ℤ)`, and `J(z) = e^{-2πiz} + Σ_{n ≥ 0} c_n e^{2πinz}` with `c_n ∈ ℤ`, where
`J = G₄³/Δ` ((4.1.15)).

* Miyake's `J` is Tau Ceti's `TauCeti.ModularForm.j = E₄³/Δ` (`J_eq`, with Mathlib's normalized
  `E₄ = 1 + 240 q + ⋯`, Miyake's `G₄` of (4.1.19)).
* `𝒜₀(Γ)`, the modular functions for `Γ` (meromorphic on `H` and at the cusps, invariant under
  `Γ`), is identified with the field of meromorphic functions on the compactified quotient
  `X(1) = Γ\H*` (Milne's `ModularFormsKB.Milne.isModularFunction_iff_compactifiedQuotient`; here
  `X(1)` is `ModularFormsKB.Milne.X0 1`, as `Γ₀(1) = SL₂(ℤ)`). On it `J` is
  `ModularFormsKB.Milne.jX 1`. `adjoin_J_eq_top` says that this field is `ℂ(J)`. The proof is
  not Miyake's: `J : X(1) → ℙ¹` has degree `[SL₂(ℤ) : Γ₀(1)] = 1`
  (`ModularFormsKB.Milne.natDegree_minpoly_le`, from Tau Ceti's degree theory of finite
  holomorphic maps).
* `J_expansion` is Milne's Theorem 4.22 (`ModularFormsKB.Milne.jFun_qExpansion`), which also
  gives `c₀ = 744`.
-/

open UpperHalfPlane Complex ModularForm
open scoped Real

noncomputable section

namespace ModularFormsKB.Miyake.Wave6

open ModularFormsKB.Milne

/-- Miyake's `J = G₄³/Δ` ((4.1.15)) is Tau Ceti's `j`. -/
@[kb "miyake1989" "(4.1.15), p. 101"]
theorem J_eq (z : ℍ) : TauCeti.ModularForm.j z = E₄ z ^ 3 / CuspForm.discriminant z := by
  rw [TauCeti.ModularForm.j_apply, CuspForm.coe_discriminant]

/-- **Miyake, Theorem 4.1.7 (3)**, first part: the field of modular functions of level one (the
meromorphic functions on `X(1) = SL₂(ℤ)\H*`) is `ℂ(J)`. -/
@[kb "miyake1989" "Theorem 4.1.7 (3), p. 101 (A_0(Gamma) = C(J))"]
theorem adjoin_J_eq_top : IntermediateField.adjoin ℂ {jX 1} = ⊤ := by
  rw [eq_top_iff]
  intro f _
  set K := IntermediateField.adjoin ℂ {jX 1}
  obtain ⟨hint, hdeg⟩ := natDegree_minpoly_le 1 f
  have hidx : (CongruenceSubgroup.Gamma0 1).index = 1 := by
    rw [CongruenceSubgroup.Gamma0_one_top, Subgroup.index_top]
  rw [hidx] at hdeg
  have h1 : (minpoly K f).natDegree = 1 :=
    le_antisymm hdeg (minpoly.natDegree_pos hint)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one K f
    (Polynomial.degree_eq_iff_natDegree_eq_of_pos one_pos |>.mpr h1)
  rw [← hc]
  exact c.2

/-- **Miyake, Theorem 4.1.7 (3)**, second part: `J(z) = e^{-2πiz} + Σ_{n ≥ 0} c_n e^{2πinz}` with
`c_n ∈ ℤ` (and `c₀ = 744`). -/
@[kb "miyake1989" "Theorem 4.1.7 (3), p. 101 (expansion of J)"]
theorem J_expansion :
    ∃ c : ℕ → ℤ, c 0 = 744 ∧ ∀ z : ℍ,
      HasSum (fun n : ℕ ↦ (c n : ℂ) * cexp (2 * π * Complex.I * z) ^ n)
        (TauCeti.ModularForm.j z - (cexp (2 * π * Complex.I * z))⁻¹) := by
  obtain ⟨c, h0, -, -, h⟩ := jFun_qExpansion
  refine ⟨c, h0, fun z ↦ ?_⟩
  have hz := h z
  rwa [jFun_eq] at hz

end ModularFormsKB.Miyake.Wave6
