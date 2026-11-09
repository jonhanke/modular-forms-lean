import ModularFormsKB.Milne.Ch6.ModularEquationGeneral

/-!
# Milne, Theorem 6.1 for $N = 2$, unconditionally

From Example 6.2 (`ModularFormsKB.Milne.LevelTwo.modularEquationLevelTwo`) the coset polynomial for $N = 2$ is
$F_2 = $ `modularPolynomialTwo`, which has integer coefficients, is symmetric, and satisfies Kronecker's congruence
$F_2 \equiv X^3 + Y^3 - X^2Y^2 - XY \pmod 2$. Hence `CosetPolynomialArithmetic 2` holds and
`ModularFormsKB.Milne.ModularEquation 2` is proved (`modularEquation_two`).
-/

open UpperHalfPlane CongruenceSubgroup Polynomial
open scoped MatrixGroups Manifold

noncomputable section

namespace ModularFormsKB.Milne.LevelTwo

open TauCeti.ModularForm TauCeti.RiemannSurface

/-- The coset polynomial for $N = 2$ is $F_2$. -/
theorem eval₂_modularPolynomialTwo_eq_Φ (z : ℍ) :
    MvPolynomial.eval₂ (Int.castRingHom ℂ[X]) ![C (j z), X] modularPolynomialTwo =
      @Φ 2 (by norm_num) ⟨by norm_num⟩ z := by
  have hN : (0 : ℕ) < 2 := by norm_num
  have : NeZero 2 := ⟨by norm_num⟩
  obtain ⟨F, -, -, hF⟩ := exists_coset_polynomial hN
  have h62 := modularEquationLevelTwo.statement (jX 2) (jNX 2 hN) (isJOnX0_jX 2) (isJNOnX0_jNX 2 hN)
  unfold IsModularPolynomial at h62
  rw [minpoly_jNX_eq hN hF, Polynomial.map_map, algebraMap_comp_toCj, eval₂_modularPolynomialTwo] at h62
  have hc : cubic (jX 2) = (cubic (X : ℂ[X])).map (Polynomial.aeval (jX 2)).toRingHom := by
    rw [cubic_map]; simp
  rw [hc] at h62
  have hinj : Function.Injective (Polynomial.aeval (jX 2)).toRingHom :=
    (transcendental_iff_injective).1 (ModularFormsKB.Milne.transcendental_jX 2)
  have hFc : F = cubic (X : ℂ[X]) := by
    have := Polynomial.map_injective _ hinj
    exact this (by simpa using h62)
  rw [← hF z, hFc, cubic_map, eval₂_modularPolynomialTwo]
  simp

theorem rename_swap_modularPolynomialTwo :
    MvPolynomial.rename (Equiv.swap 0 1) modularPolynomialTwo = modularPolynomialTwo := by
  simp only [modularPolynomialTwo, map_add, map_sub, map_mul, map_pow, map_ofNat, MvPolynomial.rename_X,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

theorem map_modularPolynomialTwo_zmod :
    MvPolynomial.map (Int.castRingHom (ZMod 2)) modularPolynomialTwo =
      MvPolynomial.X 0 ^ (2 + 1) + MvPolynomial.X 1 ^ (2 + 1) -
        MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 * MvPolynomial.X 1 := by
  have h2 : (2 : MvPolynomial (Fin 2) (ZMod 2)) = 0 := by
    rw [(map_ofNat MvPolynomial.C 2).symm, show (OfNat.ofNat 2 : ZMod 2) = 0 from rfl, map_zero]
  simp only [modularPolynomialTwo, map_add, map_sub, map_mul, map_pow, map_ofNat, MvPolynomial.map_X]
  linear_combination (744 * MvPolynomial.X 0 * MvPolynomial.X 1 * (MvPolynomial.X 0 + MvPolynomial.X 1) -
    81000 * (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2) + 20386688 * MvPolynomial.X 0 * MvPolynomial.X 1 +
    4374000000 * (MvPolynomial.X 0 + MvPolynomial.X 1) - 78732000000000) * h2

/-- **The arithmetic of the coset polynomial for $N = 2$.** -/
theorem cosetPolynomialArithmetic_two : CosetPolynomialArithmetic 2 (by norm_num) :=
  ⟨⟨modularPolynomialTwo, eval₂_modularPolynomialTwo_eq_Φ, fun _ ↦ map_modularPolynomialTwo_zmod⟩⟩

/-! ### $N = 1$ -/

/-- For $N = 1$ the coset polynomial is $Y - X$. -/
theorem cosetPolynomialArithmetic_one : CosetPolynomialArithmetic 1 (by norm_num) := by
  have : NeZero 1 := ⟨by norm_num⟩
  refine ⟨⟨MvPolynomial.X 1 - MvPolynomial.X 0, fun z ↦ ?_, fun h ↦ absurd h Nat.not_prime_one⟩⟩
  have hall : ∀ c : Cosets 1, c = Quotient.mk _ 1 := fun c ↦ by
    induction c using Quotient.inductionOn with
    | h γ =>
      apply Quotient.sound
      show QuotientGroup.rightRel _ γ 1
      rw [QuotientGroup.rightRel_apply, Gamma0_one_top]
      exact Subgroup.mem_top _
  rw [Φ, Finset.prod_eq_single (Quotient.mk _ 1) (fun c _ hc ↦ absurd (hall c) hc) (by simp)]
  have h1 : scaleH 1 (by norm_num) z = z := by ext; simp [scaleH]
  simp [jN, h1]

end ModularFormsKB.Milne.LevelTwo

namespace ModularFormsKB.Milne

/-- **Milne, Theorem 6.1 for $N = 1$** (the trivial case: $F = Y - X$). -/
@[kb "milne2017mf" "Section 6, Theorem 6.1 (pdf p. 88) for N = 1: proved"]
theorem modularEquation_one : ModularEquation 1 (by norm_num) :=
  modularEquation_of_cosetPolynomialArithmetic _ LevelTwo.cosetPolynomialArithmetic_one

/-- **Milne, Theorem 6.1 for $N = 2$**, unconditionally. -/
@[kb "milne2017mf" "Section 6, Theorem 6.1 (pdf p. 88) for N = 2: proved"]
theorem modularEquation_two : ModularEquation 2 (by norm_num) :=
  modularEquation_of_cosetPolynomialArithmetic _ LevelTwo.cosetPolynomialArithmetic_two

end ModularFormsKB.Milne
