import ModularFormsKB.Milne.Ch6.ModularEquationN

/-!
# Uniqueness of relations between $j(z)$ and $j(Nz)$

A polynomial $G \in \mathbb C[X][Y]$ of $Y$-degree less than $\psi = (\Gamma(1) : \Gamma_0(N))$ with $G(j(z), j(Nz)) = 0$
for all $z \in \mathbb H$ is zero (`eq_zero_of_eval_j_jN`), because the minimum polynomial of $j(Nz)$ over
$\mathbb C(j)$ has degree $\psi$ (`ModularFormsKB.Milne.LevelTwo.natDegree_minpoly_jNX`). Hence the coset polynomial
is the unique monic $F$ of $Y$-degree $\psi$ with $F(j(z), j(Nz)) = 0$ (`eq_of_eval_j_jN`). This is the uniqueness
step of the rationality argument for the modular polynomial.
-/

open UpperHalfPlane CongruenceSubgroup Polynomial
open scoped MatrixGroups Manifold

noncomputable section

namespace ModularFormsKB.Milne.LevelTwo

open TauCeti.ModularForm TauCeti.RiemannSurface

variable {N : ℕ} [NeZero N] (hN : 0 < N)

theorem toCj_injective : Function.Injective (toCj N) := by
  have h := (transcendental_iff_injective).1 (ModularFormsKB.Milne.transcendental_jX N)
  intro p q hpq
  apply h
  have := congrArg (algebraMap (IntermediateField.adjoin ℂ {jX N}) (MeromorphicFunction (X0 N))) hpq
  simp only [← RingHom.comp_apply, algebraMap_comp_toCj] at this
  exact this

omit [NeZero N] in
/-- $G(j_X, j_{N,X}) = 0$ in $\mathbb C(X_0(N))$ if $G(j(z), j(Nz)) = 0$ on $\mathbb H$. -/
theorem aeval_map_toCj_eq_zero {G : ℂ[X][X]}
    (hG : ∀ z : ℍ, (G.map (evalRingHom (j z))).eval (jN hN z) = 0) :
    aeval (jNX N hN) (G.map (toCj N)) = 0 := by
  rw [aeval_def, eval₂_eq_eval_map, Polynomial.map_map, algebraMap_comp_toCj]
  apply eq_zero_of_hasVal
  intro z
  have := HasVal.eval_map_aeval (isJOnX0_jX N z) (isJNOnX0_jNX N hN z) G
  have h0 : (G.map (evalRingHom (j z))).eval (TauCeti.ModularForm.j (scaleH N hN z)) = 0 := hG z
  rwa [h0] at this

/-- **No relation of $Y$-degree $< \psi$.** -/
theorem eq_zero_of_eval_j_jN {G : ℂ[X][X]} (hdeg : G.natDegree < (Gamma0 N).index)
    (hG : ∀ z : ℍ, (G.map (evalRingHom (j z))).eval (jN hN z) = 0) : G = 0 := by
  by_contra hne
  have hne' : G.map (toCj N) ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero_iff (toCj_injective (N := N))]
  have hdvd := minpoly.dvd (IntermediateField.adjoin ℂ {jX N}) (jNX N hN) (aeval_map_toCj_eq_zero hN hG)
  have hle := natDegree_le_of_dvd hdvd hne'
  rw [natDegree_minpoly_jNX hN, natDegree_map_eq_of_injective (toCj_injective (N := N))] at hle
  omega

/-- **Uniqueness of the modular polynomial over $\mathbb C$**: a monic $F$ of $Y$-degree $\psi$ with
$F(j(z), j(Nz)) = 0$ is the coset polynomial. -/
theorem eq_of_eval_j_jN {F G : ℂ[X][X]} (hF : F.Monic) (hG : G.Monic)
    (hFdeg : F.natDegree = (Gamma0 N).index) (hGdeg : G.natDegree = (Gamma0 N).index)
    (hF0 : ∀ z : ℍ, (F.map (evalRingHom (j z))).eval (jN hN z) = 0)
    (hG0 : ∀ z : ℍ, (G.map (evalRingHom (j z))).eval (jN hN z) = 0) : F = G := by
  have hψ : 0 < (Gamma0 N).index := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero)
  refine sub_eq_zero.1 (eq_zero_of_eval_j_jN hN ?_ fun z ↦ ?_)
  · rcases eq_or_ne (F - G) 0 with h | h
    · rw [h, natDegree_zero]; exact hψ
    · have hdeg : F.degree = G.degree := by
        rw [degree_eq_natDegree hF.ne_zero, degree_eq_natDegree hG.ne_zero, hFdeg, hGdeg]
      have hd := degree_sub_lt_left hdeg hF.ne_zero (by rw [hF.leadingCoeff, hG.leadingCoeff])
      have := natDegree_lt_natDegree h hd
      omega
  · rw [Polynomial.map_sub, eval_sub, hF0 z, hG0 z, sub_zero]

end ModularFormsKB.Milne.LevelTwo
