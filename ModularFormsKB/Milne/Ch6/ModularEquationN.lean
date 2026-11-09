import ModularFormsKB.Milne.Ch6.X0MinPoly
import ModularFormsKB.Citation
/-!
# Milne, Theorem 6.1, assembled: everything but the arithmetic of the coefficients

Milne, Section 6, Theorem 6.1 (pdf p. 88), named statement `ModularFormsKB.Milne.ModularEquation`. Proved here
for every $N \ge 1$:

- $j(z)$ and $j(Nz)$ are meromorphic functions on $X_0(N)$ (`ModularFormsKB.Milne.jX`, `ModularFormsKB.Milne.jNX`);
- the minimum polynomial of $j(Nz)$ over $\mathbb C(j)$ has degree $\psi = (\Gamma(1) : \Gamma_0(N))$
  (`ModularFormsKB.Milne.LevelTwo.natDegree_minpoly_jNX`);
- $\mathbb C(X_0(N)) = \mathbb C(j, j_N)$ (`ModularFormsKB.Milne.adjoin_eq_top`);
- the minimum polynomial is $F(j, Y)$ for the coset polynomial
  $F(j(z), Y) = \prod_{\Gamma_0(N)\gamma}(Y - j(N\gamma z))$ (`minpoly_jNX_eq`).

What is not proved is the arithmetic of $F$ in Milne's proof: that $F$ has integer coefficients (Milne: the
$q$-expansion coefficients of the symmetric functions of the $j(N\gamma z)$ lie in $\mathbb Z[\zeta_N]$ and are fixed by
$\operatorname{Gal}(\mathbb Q(\zeta_N)/\mathbb Q)$), is symmetric for $N > 1$, and satisfies Kronecker's congruence for
$N = p$ prime. `modularEquation_of_eval₂_eq_Φ` derives `ModularEquation N` from such an $F$; symmetry is proved in
`CosetSymmetry.lean`, and the named statement `CosetPolynomialArithmetic` (integrality and Kronecker's congruence)
is the only input of `ModularFormsKB.Milne.modularEquation_of_cosetPolynomialArithmetic`
(`ModularEquationGeneral.lean`).
-/

open UpperHalfPlane CongruenceSubgroup Polynomial
open scoped MatrixGroups Manifold

noncomputable section

namespace ModularFormsKB.Milne.LevelTwo

open TauCeti.ModularForm TauCeti.RiemannSurface

/-- Two polynomials over $\mathbb C$ agreeing at all values of $j$ are equal. -/
theorem eq_of_eval_j_eq {p q : ℂ[X]} (h : ∀ z : ℍ, p.eval (j z) = q.eval (j z)) : p = q := by
  by_contra hne
  obtain ⟨z, hz⟩ := exists_eval_j_ne_zero (sub_ne_zero.2 hne)
  exact hz (by rw [eval_sub, h z, sub_self])

/-- Two polynomials in $\mathbb C[X][Y]$ with the same specializations at all values of $j$ are equal. -/
theorem eq_of_map_eval_j_eq {P Q : ℂ[X][X]}
    (h : ∀ z : ℍ, P.map (evalRingHom (j z)) = Q.map (evalRingHom (j z))) : P = Q := by
  ext1 k
  refine eq_of_eval_j_eq fun z ↦ ?_
  have := congrArg (fun R ↦ R.coeff k) (h z)
  simpa only [coeff_map, coe_evalRingHom] using this

variable {N : ℕ} [NeZero N] (hN : 0 < N)

/-- The map $\mathbb C[X] \to \mathbb C(j)$, $X \mapsto j$. -/
abbrev toCj (N : ℕ) : ℂ[X] →+* IntermediateField.adjoin ℂ {jX N} :=
  (Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℂ (jX N))).toRingHom

omit [NeZero N] in
theorem algebraMap_comp_toCj :
    (algebraMap (IntermediateField.adjoin ℂ {jX N}) (MeromorphicFunction (X0 N))).comp (toCj N) =
      (Polynomial.aeval (jX N)).toRingHom := by
  refine RingHom.ext fun p ↦ ?_
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  exact (Polynomial.aeval_algHom_apply (IntermediateField.val _) _ p).symm

/-- **The minimum polynomial of $j(Nz)$ is $F(j, Y)$** for any $F \in \mathbb C[X][Y]$ with
$F(j(z), Y) = \prod_c (Y - j(N\gamma_c z))$. -/
theorem minpoly_jNX_eq {F : ℂ[X][X]} (hF : ∀ z : ℍ, F.map (evalRingHom (j z)) = Φ hN z) :
    minpoly (IntermediateField.adjoin ℂ {jX N}) (jNX N hN) = F.map (toCj N) := by
  obtain ⟨F₀, hF₀m, hF₀deg, hF₀⟩ := exists_coset_polynomial hN
  have hFF₀ : F = F₀ := eq_of_map_eval_j_eq fun z ↦ by rw [hF z, hF₀ z]
  subst hFF₀
  have hroot : (F.map (Polynomial.aeval (jX N)).toRingHom).eval (jNX N hN) = 0 := by
    apply eq_zero_of_hasVal
    intro z
    have := HasVal.eval_map_aeval (isJOnX0_jX N z) (isJNOnX0_jNX N hN z) F
    rw [hF z] at this
    have h0 : (Φ hN z).eval (TauCeti.ModularForm.j (scaleH N hN z)) = 0 := Φ_eval_jN hN z
    rwa [h0] at this
  have hFK : aeval (jNX N hN) (F.map (toCj N)) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, Polynomial.map_map, algebraMap_comp_toCj, hroot]
  have hFKm : (F.map (toCj N)).Monic := hF₀m.map _
  have hint : IsIntegral (IntermediateField.adjoin ℂ {jX N}) (jNX N hN) := ⟨_, hFKm, hFK⟩
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hFKm (minpoly.dvd _ _ hFK) ?_).symm
  rw [hF₀m.natDegree_map, hF₀deg, natDegree_minpoly_jNX hN]

/-- **The arithmetic of the coset polynomial** (named statement; Milne, Section 6, proof of Theorem 6.1, pdf
pp. 88–89): there is $F(X, Y) \in \mathbb Z[X, Y]$ with $F(j(z), Y) = \prod_{\Gamma_0(N)\gamma}(Y - j(N\gamma z))$ for all
$z \in \mathbb H$, and $F \equiv X^{p+1} + Y^{p+1} - X^pY^p - XY \pmod p$ when $N = p$ is prime. (Symmetry for $N > 1$
is proved: `ModularFormsKB.Milne.LevelTwo.rename_swap_eq_of_eval₂_eq_Φ`.) -/
@[kb "milne2017mf" "Section 6, proof of Theorem 6.1: integrality and Kronecker's congruence (pdf pp. 88-89)"]
structure CosetPolynomialArithmetic (N : ℕ) (hN : 0 < N) : Prop where
  statement : ∃ F : MvPolynomial (Fin 2) ℤ,
    (∀ z : ℍ, MvPolynomial.eval₂ (Int.castRingHom ℂ[X]) ![C (j z), X] F =
      @Φ N hN (NeZero.of_pos hN) z) ∧
    (N.Prime → MvPolynomial.map (Int.castRingHom (ZMod N)) F =
      MvPolynomial.X 0 ^ (N + 1) + MvPolynomial.X 1 ^ (N + 1) -
        MvPolynomial.X 0 ^ N * MvPolynomial.X 1 ^ N - MvPolynomial.X 0 * MvPolynomial.X 1)

end ModularFormsKB.Milne.LevelTwo

namespace ModularFormsKB.Milne

open LevelTwo TauCeti.RiemannSurface

/-- **Milne, Theorem 6.1, from a polynomial with the stated properties**: if $F \in \mathbb Z[X, Y]$ satisfies
$F(j(z), Y) = \prod_{\Gamma_0(N)\gamma}(Y - j(N\gamma z))$ and the symmetry and congruence conditions, then
`ModularEquation N` holds. -/
theorem modularEquation_of_eval₂_eq_Φ {N : ℕ} (hN : 0 < N) (Fz : MvPolynomial (Fin 2) ℤ)
    (hFz : ∀ z : ℍ, MvPolynomial.eval₂ (Int.castRingHom ℂ[X]) ![C (TauCeti.ModularForm.j z), X] Fz =
      @Φ N hN (NeZero.of_pos hN) z)
    (hsym : 1 < N → MvPolynomial.rename (Equiv.swap 0 1) Fz = Fz)
    (hkr : N.Prime → MvPolynomial.map (Int.castRingHom (ZMod N)) Fz =
      MvPolynomial.X 0 ^ (N + 1) + MvPolynomial.X 1 ^ (N + 1) -
        MvPolynomial.X 0 ^ N * MvPolynomial.X 1 ^ N - MvPolynomial.X 0 * MvPolynomial.X 1) :
    ModularEquation N hN := by
  have : NeZero N := NeZero.of_pos hN
  refine ⟨jX N, jNX N hN, isJOnX0_jX N, isJNOnX0_jNX N hN, adjoin_eq_top N _ (natDegree_minpoly_jNX hN),
    natDegree_minpoly_jNX hN, Fz, ?_, hsym, hkr⟩
  let Fc : ℂ[X][X] := MvPolynomial.eval₂ (Int.castRingHom ℂ[X][X]) ![C X, X] Fz
  have hFc : ∀ z : ℍ, Fc.map (evalRingHom (TauCeti.ModularForm.j z)) = Φ hN z := by
    intro z
    rw [← hFz z, ← coe_mapRingHom, MvPolynomial.eval₂_comp_left]
    congr 1
    · exact RingHom.ext_int _ _
    · funext i
      fin_cases i <;> simp
  unfold IsModularPolynomial
  rw [minpoly_jNX_eq hN hFc, Polynomial.map_map, algebraMap_comp_toCj, ← coe_mapRingHom,
    MvPolynomial.eval₂_comp_left]
  congr 1
  · exact RingHom.ext_int _ _
  · funext i
    fin_cases i <;> simp

end ModularFormsKB.Milne
