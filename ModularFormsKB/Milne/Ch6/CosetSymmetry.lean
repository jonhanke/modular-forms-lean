import ModularFormsKB.Milne.Ch6.Uniqueness

/-!
# Symmetry of the modular polynomial

Milne, Section 6, proof of Theorem 6.1 (pdf p. 89): for $N > 1$ the modular polynomial is symmetric. If
$F(X, Y) \in \mathbb Z[X, Y]$ satisfies $F(j(z), Y) = \prod_{\Gamma_0(N)\gamma}(Y - j(N\gamma z))$, then by the Fricke
involution $z \mapsto -1/(Nz)$ also $F(j(Nz), j(z)) = 0$, so $F(j, Y)$ (irreducible over $\mathbb C(j)$, the minimum
polynomial of $j(Nz)$) divides $F(Y, j)$; by Gauss's lemma $F(Y, X) = c F(X, Y)$ with $c = \pm 1$, and $c = -1$ would make
$X - Y$ a factor of $F$, impossible when $\psi > 1$.
-/

open UpperHalfPlane CongruenceSubgroup Polynomial
open scoped MatrixGroups Manifold

noncomputable section

namespace ModularFormsKB.Milne.LevelTwo

open TauCeti.ModularForm TauCeti.RiemannSurface

variable {N : ℕ} [NeZero N] (hN : 0 < N)

/-- $F$ read as a polynomial in $Y$ over $\mathbb C[X]$. -/
abbrev Fc (F : MvPolynomial (Fin 2) ℤ) : ℂ[X][X] :=
  MvPolynomial.eval₂ (Int.castRingHom ℂ[X][X]) ![C X, X] F

theorem Fc_map_eval (F : MvPolynomial (Fin 2) ℤ) (a : ℂ) :
    (Fc F).map (evalRingHom a) = MvPolynomial.eval₂ (Int.castRingHom ℂ[X]) ![C a, X] F := by
  have : (Polynomial.mapRingHom (evalRingHom a)).comp
      (MvPolynomial.eval₂Hom (Int.castRingHom ℂ[X][X]) ![C X, X]) =
      MvPolynomial.eval₂Hom (Int.castRingHom ℂ[X]) ![C a, X] := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
    · simp
    · fin_cases i <;> simp
  exact congrArg (fun f ↦ f F) this

theorem Fc_eval_eval (F : MvPolynomial (Fin 2) ℤ) (a b : ℂ) :
    ((Fc F).map (evalRingHom a)).eval b = MvPolynomial.eval₂ (Int.castRingHom ℂ) ![a, b] F := by
  have : (evalRingHom b).comp ((Polynomial.mapRingHom (evalRingHom a)).comp
      (MvPolynomial.eval₂Hom (Int.castRingHom ℂ[X][X]) ![C X, X])) =
      MvPolynomial.eval₂Hom (Int.castRingHom ℂ) ![a, b] := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
    · simp
    · fin_cases i <;> simp
  exact congrArg (fun f ↦ f F) this

theorem Fc_rename_eval_eval (F : MvPolynomial (Fin 2) ℤ) (a b : ℂ) :
    ((Fc (MvPolynomial.rename (Equiv.swap 0 1) F)).map (evalRingHom a)).eval b =
      ((Fc F).map (evalRingHom b)).eval a := by
  have h : (![a, b] : Fin 2 → ℂ) ∘ (Equiv.swap 0 1) = ![b, a] := by
    funext i
    fin_cases i <;> simp
  rw [Fc_eval_eval, Fc_eval_eval, MvPolynomial.eval₂_rename, h]

/-- The ring map $\mathbb C[X][Y] \to \mathbb C[X_0, X_1]$. -/
def Ψ : ℂ[X][X] →+* MvPolynomial (Fin 2) ℂ :=
  (Polynomial.eval₂RingHom (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ)).toRingHom
    (MvPolynomial.X 1))

theorem Ψ_Fc (F : MvPolynomial (Fin 2) ℤ) : Ψ (Fc F) = MvPolynomial.map (Int.castRingHom ℂ) F := by
  have : Ψ.comp (MvPolynomial.eval₂Hom (Int.castRingHom ℂ[X][X]) ![C X, X]) =
      MvPolynomial.map (Int.castRingHom ℂ) := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
    · simp
    · fin_cases i <;> simp [Ψ]
  exact congrArg (fun f ↦ f F) this

/-- Fricke: $F(j(Nz), j(z)) = 0$. -/
theorem fricke_eval {F : MvPolynomial (Fin 2) ℤ}
    (hF : ∀ z : ℍ, MvPolynomial.eval₂ (Int.castRingHom ℂ[X]) ![C (j z), X] F = Φ hN z) (z : ℍ) :
    ((Fc F).map (evalRingHom (j (scaleH N hN z)))).eval (j z) = 0 := by
  set w : ℍ := ModularGroup.S • scaleH N hN z with hw
  have h1 : j w = j (scaleH N hN z) := jSL _ _
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h2 : jN hN w = j z := by
    unfold jN
    apply j_eq_of_coe 0 (-1) 1 0 (by norm_num)
    rw [hw]
    show (N : ℂ) * ((ModularGroup.S • scaleH N hN z : ℍ) : ℂ) = _
    rw [coe_S_smul]
    show (N : ℂ) * (-1 / ((N : ℂ) * z)) = _
    push_cast
    simp only [zero_mul, zero_add, add_zero, one_mul]
    field_simp
  have h3 := Φ_eval_jN hN w
  rw [← hF w, ← Fc_map_eval, h1, h2] at h3
  exact h3
  
theorem monic_Fc {F : MvPolynomial (Fin 2) ℤ}
    (hF : ∀ z : ℍ, MvPolynomial.eval₂ (Int.castRingHom ℂ[X]) ![C (j z), X] F = Φ hN z) :
    (Fc F).Monic ∧ (Fc F).natDegree = (Gamma0 N).index := by
  obtain ⟨F₀, hF₀m, hF₀deg, hF₀⟩ := exists_coset_polynomial hN
  have : Fc F = F₀ := eq_of_map_eval_j_eq fun z ↦ by rw [Fc_map_eval, hF z, hF₀ z]
  rw [this]
  exact ⟨hF₀m, hF₀deg⟩

theorem minpoly_Fc {F : MvPolynomial (Fin 2) ℤ}
    (hF : ∀ z : ℍ, MvPolynomial.eval₂ (Int.castRingHom ℂ[X]) ![C (j z), X] F = Φ hN z) :
    minpoly (IntermediateField.adjoin ℂ {jX N}) (jNX N hN) = (Fc F).map (toCj N) :=
  minpoly_jNX_eq hN fun z ↦ by rw [Fc_map_eval, hF z]

/-- Divisibility of a polynomial with monic divisor can be checked after an injective ring map. -/
theorem dvd_of_map_dvd {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ)
    {f g : R[X]} (hf : f.Monic) (h : f.map φ ∣ g.map φ) : f ∣ g := by
  rw [← modByMonic_eq_zero_iff_dvd hf]
  have h0 := (modByMonic_eq_zero_iff_dvd (hf.map φ)).2 h
  rw [← Polynomial.map_modByMonic _ hf] at h0
  exact (Polynomial.map_injective φ hφ) (by rw [h0, Polynomial.map_zero])

theorem Fc_dvd {F : MvPolynomial (Fin 2) ℤ}
    (hF : ∀ z : ℍ, MvPolynomial.eval₂ (Int.castRingHom ℂ[X]) ![C (j z), X] F = Φ hN z) :
    Fc F ∣ Fc (MvPolynomial.rename (Equiv.swap 0 1) F) := by
  set K := IntermediateField.adjoin ℂ {jX N}
  set H := Fc (MvPolynomial.rename (Equiv.swap 0 1) F)
  have hroot : (H.map (Polynomial.aeval (jX N)).toRingHom).eval (jNX N hN) = 0 := by
    apply eq_zero_of_hasVal
    intro z
    have := HasVal.eval_map_aeval (isJOnX0_jX N z) (isJNOnX0_jNX N hN z) H
    rw [Fc_rename_eval_eval] at this
    have h0 := fricke_eval hN hF z
    rwa [h0] at this
  have hHK : aeval (jNX N hN) (H.map (toCj N)) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, Polynomial.map_map, algebraMap_comp_toCj, hroot]
  have hdvd : minpoly K (jNX N hN) ∣ H.map (toCj N) := minpoly.dvd _ _ hHK
  rw [minpoly_Fc hN hF] at hdvd
  exact dvd_of_map_dvd (toCj N) toCj_injective (monic_Fc hN hF).1 hdvd

omit [NeZero N] in
theorem one_lt_index (hN : 0 < N) (h1 : 1 < N) : 1 < (Gamma0 N).index := by
  have h := index_Gamma0_eq hN
  have hp : (1 : ℚ) ≤ ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℚ)) := by
    apply Finset.one_le_prod₀ 
    intro p _
    have : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
    linarith
  have : (N : ℚ) ≤ ((Gamma0 N).index : ℚ) := by
    rw [h]
    nlinarith [(Nat.cast_pos.2 hN : (0 : ℚ) < N)]
  have : N ≤ (Gamma0 N).index := by exact_mod_cast this
  omega

/-- $F(x, x)$ does not vanish for all $x = j(z)$. -/
theorem exists_diag_ne {F : MvPolynomial (Fin 2) ℤ} (h1 : 1 < N)
    (hF : ∀ z : ℍ, MvPolynomial.eval₂ (Int.castRingHom ℂ[X]) ![C (j z), X] F = Φ hN z) :
    ∃ z : ℍ, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![j z, j z] F ≠ 0 := by
  by_contra hall
  push Not at hall
  set K := IntermediateField.adjoin ℂ {jX N}
  have hroot : ((Fc F).map (Polynomial.aeval (jX N)).toRingHom).eval (jX N) = 0 := by
    apply eq_zero_of_hasVal
    intro z
    have := HasVal.eval_map_aeval (isJOnX0_jX N z) (isJOnX0_jX N z) (Fc F)
    rw [Fc_eval_eval, hall z] at this
    exact this
  have hm : aeval (IntermediateField.AdjoinSimple.gen ℂ (jX N)) ((Fc F).map (toCj N)) = 0 := by
    apply (algebraMap K (MeromorphicFunction (X0 N))).injective
    rw [map_zero, ← Polynomial.aeval_algebraMap_apply, aeval_def, eval₂_eq_eval_map,
      Polynomial.map_map, algebraMap_comp_toCj]
    exact hroot
  have hmono := (monic_Fc hN hF).1
  have hint : IsIntegral K (jNX N hN) := by
    by_contra hni
    have := minpoly_Fc hN hF
    rw [minpoly.eq_zero hni] at this
    exact hmono.map (toCj N) |>.ne_zero this.symm
  have hirr : Irreducible ((Fc F).map (toCj N)) := by
    rw [← minpoly_Fc hN hF]
    exact minpoly.irreducible hint
  have hdeg := degree_eq_one_of_irreducible_of_root hirr (x := IntermediateField.AdjoinSimple.gen ℂ (jX N))
    (by simpa [IsRoot, aeval_def, eval₂_eq_eval_map] using hm)
  have h2 := natDegree_eq_of_degree_eq_some hdeg
  rw [hmono.natDegree_map, (monic_Fc hN hF).2] at h2
  have := one_lt_index hN h1
  have h3 : (Gamma0 N).index = 1 := h2
  omega

/-- **Symmetry of the modular polynomial** for $N > 1$. -/
theorem rename_swap_eq_of_eval₂_eq_Φ (h1 : 1 < N) {F : MvPolynomial (Fin 2) ℤ}
    (hF : ∀ z : ℍ, MvPolynomial.eval₂ (Int.castRingHom ℂ[X]) ![C (j z), X] F = Φ hN z) :
    MvPolynomial.rename (Equiv.swap 0 1) F = F := by
  set σ : Equiv.Perm (Fin 2) := Equiv.swap 0 1 with hσ
  have hσσ : ∀ p : MvPolynomial (Fin 2) ℂ, MvPolynomial.rename σ (MvPolynomial.rename σ p) = p := by
    intro p
    rw [MvPolynomial.rename_rename]
    have : (σ ∘ σ) = id := by
      funext i
      simp [hσ]
    rw [this]
    exact MvPolynomial.rename_id_apply p
  set G : MvPolynomial (Fin 2) ℂ := MvPolynomial.map (Int.castRingHom ℂ) F with hG
  have hGs : MvPolynomial.map (Int.castRingHom ℂ) (MvPolynomial.rename σ F) =
      MvPolynomial.rename σ G := MvPolynomial.map_rename _ _ _
  have hd1 : G ∣ MvPolynomial.rename σ G := by
    have := map_dvd Ψ (Fc_dvd hN hF)
    rwa [Ψ_Fc, Ψ_Fc, hGs] at this
  have hd2 : MvPolynomial.rename σ G ∣ G := by
    have := map_dvd (MvPolynomial.rename σ : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) hd1
    rwa [hσσ] at this
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hd1 hd2
  obtain ⟨c, hc, hcu⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 u.isUnit
  rw [hcu] at hu
  have hc0 : c ≠ 0 := hc.ne_zero
  have hF0 : F ≠ 0 := by
    rintro rfl
    have : Φ hN UpperHalfPlane.I = 0 := by rw [← hF UpperHalfPlane.I]; simp
    exact (Φ_monic hN _).ne_zero this
  have hG0 : G ≠ 0 := by
    intro h
    exact hF0 (MvPolynomial.map_injective _ (RingHom.injective_int _) (by rw [← hG, h, map_zero]))
  -- apply the swap again
  have hu2 : G = G * MvPolynomial.C (c * c) := by
    have := congrArg (MvPolynomial.rename σ) hu
    rw [map_mul, hσσ, MvPolynomial.rename_C, ← hu, mul_assoc, ← map_mul] at this
    exact this.symm
  have hcc : c * c = 1 := by
    have h' : G * (MvPolynomial.C (c * c) - 1) = 0 := by
      rw [mul_sub, ← hu2]; simp
    rcases mul_eq_zero.1 h' with h | h
    · exact absurd h hG0
    · have h5 : (MvPolynomial.C (c * c) : MvPolynomial (Fin 2) ℂ) = MvPolynomial.C 1 := by
        rw [map_one]; exact sub_eq_zero.1 h
      exact MvPolynomial.C_injective _ _ h5
  have hc1 : c = 1 ∨ c = -1 := by
    have : (c - 1) * (c + 1) = 0 := by linear_combination hcc
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases hc1 with rfl | rfl
  · apply MvPolynomial.map_injective (Int.castRingHom ℂ) (RingHom.injective_int _)
    rw [hGs]
    simpa using hu.symm
  · exfalso
    obtain ⟨z, hz⟩ := exists_diag_ne hN h1 hF
    apply hz
    have h1 := congrArg (MvPolynomial.eval (![j z, j z] : Fin 2 → ℂ)) hu
    have h2 : (![j z, j z] : Fin 2 → ℂ) ∘ σ = ![j z, j z] := by
      funext i; fin_cases i <;> simp [hσ]
    rw [MvPolynomial.eval_rename, h2, map_mul] at h1
    simp only [MvPolynomial.eval_C] at h1
    rw [hG, MvPolynomial.eval_map] at h1
    have h3 : MvPolynomial.eval₂ (Int.castRingHom ℂ) ![j z, j z] F * 2 = 0 := by linear_combination -h1
    simpa using h3

end ModularFormsKB.Milne.LevelTwo
