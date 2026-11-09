import ModularFormsKB.Milne.Ch11.TwistField
import ModularFormsKB.Milne.Ch11.TwistFixed
import ModularFormsKB.Milne.Ch11.TwistResidue
import ModularFormsKB.Milne.Ch11.TwistBurnside
import TauCeti.FieldTheory.FunctionField.Place.Extension.Fibre

/-!
# The twisting identity $\sum_{\tau \in \Gamma} N_1(F_\tau) = |\Gamma|\, N_1(F^\Gamma)$

Let $F/k$ be a function field over a finite field $k$ with $q$ elements, $k$ exact, $\Gamma$ a finite group of
$k$-automorphisms of $F$, $F' = F \cdot k'$ a constant field extension of degree $m$ with $|\Gamma| \mid m$, and
$\rho$ the Frobenius of $k'/k$. For $\tau \in \Gamma$ let $F_\tau$ be the fixed field of $\tau \otimes \rho$
(`twistField`), a function field over $k$ of the genus of $F$. Then (`sum_card_degree_one_twistField`)
$$\sum_{\tau \in \Gamma} N_1(F_\tau) = |\Gamma| \cdot N_1(L_0), \qquad L_0 = F'^{\,\Gamma \otimes \mathrm{Gal}(k'/k)}
\cong F^\Gamma.$$
(Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., proof of Theorem 5.2.3 [unverified numbering];
Bombieri, Séminaire Bourbaki 430.)

Proof. $N_1(F_\tau)$ is the number of rational places $Q$ of $F'/k'$ fixed by $\tau\otimes\rho$
(`card_degree_one_twistField`). Such a $Q$ lies over a rational place $P$ of $L_0$, and conversely every $Q$ over a
rational $P$ is rational: its degree over $k$ divides the exponent $m$ of $\Omega = \mathrm{Gal}(F'/L_0)$
(`degree_dvd_of_forall_pow_eq_one`). Over a fixed rational $P$, the group $\Omega = \Gamma \times \mathrm{Gal}(k'/k)$
acts transitively on the places above $P$, and each stabilizer contains an element $\tau \otimes \rho$ (a Frobenius
element, `exists_smul_eq_valuation_sub_pow_lt_one`), so the coset count `sum_card_fixed_coset` gives $|\Gamma|$.
-/

open TauCeti Module IntermediateField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ModularFormsKB.Milne

section Bridge

variable {k k' F' : Type*} [Field k] [Field k'] [Field F'] [Algebra k k'] [Algebra k F'] [Algebra k' F']
  [IsScalarTower k k' F'] [Algebra.IsIntegral k k']

/-- Degrees of the same place over $k$ and over $k'$: $\deg_k Q = [k':k] \deg_{k'} Q$. -/
theorem degree_constantsEquiv_symm (Q : Place k' F') :
    ((Place.constantsEquiv k k' F').symm Q).degree = finrank k k' * Q.degree := by
  set Q₀ := (Place.constantsEquiv k k' F').symm Q
  letI : Algebra k' Q₀.ResidueField := (inferInstance : Algebra k' Q.ResidueField)
  haveI : IsScalarTower k k' Q₀.ResidueField := IsScalarTower.of_algebraMap_eq fun c => by
    change IsLocalRing.residue Q₀.integers (algebraMap k Q₀.integers c) =
      IsLocalRing.residue Q.integers (algebraMap k' Q.integers (algebraMap k k' c))
    congr 1
    exact Subtype.ext (IsScalarTower.algebraMap_apply k k' F' c)
  rw [Place.degree, Place.degree, ← Module.finrank_mul_finrank k k' Q₀.ResidueField]
  rfl

end Bridge

section Setup

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Finite k] [Finite k'] [Algebra.IsSeparable k k']
  (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)

/-- A $k$-automorphism of $k'$ raising to the $q$-th power is the Frobenius. -/
theorem eq_frobenius_of_forall {ρ : k' ≃ₐ[k] k'} (hρq : ∀ c, ρ c = c ^ Nat.card k) :
    letI := Fintype.ofFinite k
    ρ = FiniteField.frobeniusAlgEquivOfAlgebraic k k' := by
  letI := Fintype.ofFinite k
  ext c
  rw [hρq, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Nat.card_eq_fintype_card]

theorem orderOf_of_forall {ρ : k' ≃ₐ[k] k'} (hρq : ∀ c, ρ c = c ^ Nat.card k) :
    orderOf ρ = finrank k k' := by
  letI := Fintype.ofFinite k
  rw [eq_frobenius_of_forall hρq, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]

theorem exists_pow_eq_of_forall {ρ : k' ≃ₐ[k] k'} (hρq : ∀ c, ρ c = c ^ Nat.card k)
    (ρ' : k' ≃ₐ[k] k') : ∃ j : ℕ, ρ' = ρ ^ j := by
  letI := Fintype.ofFinite k
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k k').2 ρ'
  exact ⟨j.1, by rw [eq_frobenius_of_forall hρq]; exact hj.symm⟩

theorem pow_eq_one_of_dvd {Γ : Subgroup (F ≃ₐ[k] F)} [Finite Γ] (hm : Nat.card Γ ∣ finrank k k')
    {τ : F ≃ₐ[k] F} (hτ : τ ∈ Γ) (ρ' : k' ≃ₐ[k] k') : twistAut hex h τ ρ' ^ finrank k k' = 1 := by
  rw [twistAut_pow]
  have h1 : τ ^ finrank k k' = 1 := by
    have : (⟨τ, hτ⟩ : Γ) ^ finrank k k' = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard _).trans hm)
    simpa using congrArg Subtype.val this
  have h2 : ρ' ^ finrank k k' = 1 := by
    refine orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard _).trans ?_)
    rw [IsGalois.card_aut_eq_finrank]
  rw [h1, h2, twistAut_one]

variable (Γ : Subgroup (F ≃ₐ[k] F)) [Finite Γ]

instance : Finite (twistGroup hex h Γ ⊤) := finite_twistGroup hex h Γ ⊤

instance : IsGalois (fixedField (twistGroup hex h Γ ⊤)) F' :=
  IsGalois.of_fixed_field F' (twistGroup hex h Γ ⊤)

instance : FiniteDimensional (fixedField (twistGroup hex h Γ ⊤)) F' :=
  inferInstanceAs (FiniteDimensional (FixedPoints.subfield (twistGroup hex h Γ ⊤) F') F')

/-- The Galois group of $F'$ over $L_0$ is $\Omega = \Gamma \otimes \mathrm{Gal}(k'/k)$. -/
noncomputable def twistGaloisEquiv :
    twistGroup hex h Γ ⊤ ≃* (F' ≃ₐ[fixedField (twistGroup hex h Γ ⊤)] F') :=
  FixedPoints.toAlgAutMulEquiv (twistGroup hex h Γ ⊤) F'

@[simp]
theorem twistGaloisEquiv_apply (ω : twistGroup hex h Γ ⊤) (x : F') :
    twistGaloisEquiv hex h Γ ω x = ω.1 x := rfl

theorem twistGaloisEquiv_symm_apply (ω : twistGroup hex h Γ ⊤) (x : F') :
    (twistGaloisEquiv hex h Γ ω).symm x = ω.1.symm x := by
  rw [AlgEquiv.symm_apply_eq, twistGaloisEquiv_apply, AlgEquiv.apply_symm_apply]

theorem exists_twistAut_of_galois (σ : F' ≃ₐ[fixedField (twistGroup hex h Γ ⊤)] F') :
    ∃ τ ∈ Γ, ∃ ρ' : k' ≃ₐ[k] k', ∃ hω : twistAut hex h τ ρ' ∈ twistGroup hex h Γ ⊤,
      σ = twistGaloisEquiv hex h Γ ⟨_, hω⟩ := by
  obtain ⟨ω, rfl⟩ := (twistGaloisEquiv hex h Γ).surjective σ
  obtain ⟨τ, hτ, ρ', -, hω⟩ := (mem_twistGroup_iff hex h ω.1).mp ω.2
  refine ⟨τ, hτ, ρ', hω ▸ ω.2, ?_⟩
  congr 1
  exact Subtype.ext hω

theorem galois_pow_eq_one (hm : Nat.card Γ ∣ finrank k k')
    (σ : F' ≃ₐ[fixedField (twistGroup hex h Γ ⊤)] F') : σ ^ finrank k k' = 1 := by
  obtain ⟨τ, hτ, ρ', hω, rfl⟩ := exists_twistAut_of_galois hex h Γ σ
  rw [← map_pow]
  have : (⟨_, hω⟩ : twistGroup hex h Γ ⊤) ^ finrank k k' = 1 :=
    Subtype.ext (by simpa using pow_eq_one_of_dvd hex h hm hτ ρ')
  rw [this, map_one]

/-- The Galois action of $\omega \in \Omega$ on places of $F'/k$ is the semilinear transport `twistPlace` on
places of $F'/k'$. -/
theorem smul_constantsEquiv_symm {ω : F' ≃ₐ[k] F'} (hω : ω ∈ twistGroup hex h Γ ⊤) (ρ' : k' ≃ₐ[k] k')
    (hωρ : ∀ c : k', ω (algebraMap k' F' c) = algebraMap k' F' (ρ' c)) (Q : Place k' F') :
    twistGaloisEquiv hex h Γ ⟨ω, hω⟩ • (Place.constantsEquiv k k' F').symm Q =
      (Place.constantsEquiv k k' F').symm (twistPlace ω ρ' hωρ Q) := by
  ext x
  rw [Place.smul_eq_map, Place.valuation_map, Place.valuation_constantsEquiv_symm,
    Place.valuation_constantsEquiv_symm, twistPlace, Place.valuation_equivOfRingEquiv]
  congr 1

/-- The fixed field $L_0$ of $\Omega = \Gamma \otimes \mathrm{Gal}(k'/k)$. -/
noncomputable abbrev twistBase : IntermediateField k F' := fixedField (twistGroup hex h Γ ⊤)

theorem restrict_constantsEquiv_symm (Q : Place k' F') :
    ((Place.constantsEquiv k k' F').symm Q).restrict k (twistBase hex h Γ) =
      Q.restrict k (twistBase hex h Γ) := by
  ext1
  rfl

end Setup

section Count

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Finite k] [Finite k'] [Algebra.IsSeparable k k']
  (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)
  (Γ : Subgroup (F ≃ₐ[k] F)) [Fintype Γ] {ρ : k' ≃ₐ[k] k'} (hρq : ∀ c, ρ c = c ^ Nat.card k)

include hF h in
theorem isFunctionField_of_constantCompositum : IsFunctionField k F' := by
  have : FiniteDimensional k k' := Module.Finite.of_finite
  exact (hF.of_constantCompositum_eq_top h).of_finiteDimensional

include hF hρq in
/-- **The count over one rational place**: for a rational place $P$ of $L_0$,
$\sum_{\tau \in \Gamma} \#\{Q \mid P : (\tau \otimes \rho) Q = Q\} = |\Gamma|$. -/
theorem sum_card_fixed_fibre (P : Place k (twistBase hex h Γ)) (hP : P.degree = 1) :
    ∑ τ : Γ, Nat.card {Q : Place k' F' // Q.restrict k (twistBase hex h Γ) = P ∧
      twistPlace (twistAut hex h τ ρ) ρ (twistAut_algebraMap_right hex h τ ρ) Q = Q} = Nat.card Γ := by
  classical
  let L := twistBase hex h Γ
  have hF'k := isFunctionField_of_constantCompositum hF h
  have hL : IsFunctionField k L := hF'k.fixedField _
  let X := {Q₀ : Place k F' // Q₀.restrict k L = P}
  have hXfin : Finite X := (Place.finite_setOf_restrict_eq k L P).to_subtype
  have hXne : Nonempty X := by
    obtain ⟨Q, hQ⟩ := Place.restrict_surjective_of_finiteDimensional hL hF'k P
    exact ⟨⟨Q, hQ⟩⟩
  let G := Γ × (k' ≃ₐ[k] k')
  let ψ₀ : G →* (F' ≃ₐ[k] F') := (twistAutHom hex h).comp (MonoidHom.prodMap Γ.subtype (MonoidHom.id _))
  have hψ₀ : ∀ g, ψ₀ g ∈ twistGroup hex h Γ ⊤ := fun g =>
    twistAut_mem_twistGroup hex h g.1.2 (Subgroup.mem_top _)
  let ψ : G →* (F' ≃ₐ[L] F') := (twistGaloisEquiv hex h Γ).toMonoidHom.comp (ψ₀.codRestrict _ hψ₀)
  letI act : MulAction (F' ≃ₐ[L] F') X :=
    { smul := fun σ x => ⟨σ • x.1, (Place.restrict_smul σ x.1).trans x.2⟩
      one_smul := fun x => Subtype.ext (one_smul _ x.1)
      mul_smul := fun σ τ x => Subtype.ext (mul_smul σ τ x.1) }
  letI : MulAction G X := MulAction.compHom X ψ
  have hsmul : ∀ (g : G) (x : X), (g • x).1 = ψ g • x.1 := fun _ _ => rfl
  let N := (MonoidHom.snd Γ (k' ≃ₐ[k] k')).ker
  have : Finite G := inferInstance
  letI : Fintype N := Fintype.ofFinite N
  let φ : G := (1, ρ)
  have hmemN : ∀ τ : Γ, ((τ, 1) : G) ∈ N := fun τ => MonoidHom.mem_ker.mpr rfl
  have hmain := sum_card_fixed_coset (X := X) N φ
    (fun ω => by
      obtain ⟨j, hj⟩ := exists_pow_eq_of_forall hρq ω.2
      refine ⟨j, (ω.1, 1), hmemN ω.1, ?_⟩
      exact Prod.ext (by change ω.1 = (φ ^ j).1 * ω.1; rw [Prod.pow_fst]; simp [φ])
        (by change ω.2 = (φ ^ j).2 * 1; rw [Prod.pow_snd]; simp [φ, hj]))
    (fun x y => by
      obtain ⟨σ, hσ⟩ := (Place.restrict_eq_iff_exists_smul_eq (F := L)).mp (x.2.trans y.2.symm)
      obtain ⟨τ, hτ, ρ', hω, rfl⟩ := exists_twistAut_of_galois hex h Γ σ
      exact ⟨(⟨τ, hτ⟩, ρ'), Subtype.ext hσ⟩)
    (fun x => by
      obtain ⟨d, hdx, hd⟩ := exists_smul_eq_valuation_sub_pow_lt_one (F₀ := L) hF'k x.1 (by rw [x.2]; exact hP)
      obtain ⟨τ, hτ, ρ', hω, rfl⟩ := exists_twistAut_of_galois hex h Γ d
      have hρ' : ρ' = ρ := AlgEquiv.ext fun c => by
        have hint : algebraMap k' F' c ∈ x.1.integers :=
          x.1.mem_integers_of_mem_algebraicClosure (mem_algebraicClosure_iff.mpr
            ((Algebra.IsIntegral.isIntegral (R := k) c).algebraMap.isAlgebraic))
        have hc := hd (algebraMap k' F' c) hint
        rw [twistGaloisEquiv_apply, twistAut_algebraMap_right, ← map_pow, ← hρq, ← map_sub] at hc
        by_contra hne
        have h1 := x.1.valuation_eq_one_of_isAlgebraic
          ((Algebra.IsIntegral.isIntegral (R := k) (ρ' c - ρ c)).algebraMap.isAlgebraic)
          ((map_ne_zero (algebraMap k' F')).mpr (sub_ne_zero.mpr hne))
        rw [h1] at hc
        exact lt_irrefl _ hc
      subst hρ'
      refine ⟨(⟨τ, hτ⟩, 1), hmemN _, Subtype.ext ?_⟩
      rw [hsmul]
      have : φ * ((⟨τ, hτ⟩, 1) : G) = (⟨τ, hτ⟩, ρ') := Prod.ext (one_mul _) (mul_one _)
      rw [this]
      exact hdx)
  -- translate the fixed points into places of `F'/k'`
  have hconv : ∀ τ : Γ, Nat.card {x : X // (φ * ((τ, 1) : G)) • x = x} =
      Nat.card {Q : Place k' F' // Q.restrict k L = P ∧
        twistPlace (twistAut hex h τ ρ) ρ (twistAut_algebraMap_right hex h τ ρ) Q = Q} := by
    intro τ
    have hφτ : φ * ((τ, 1) : G) = (τ, ρ) := Prod.ext (one_mul _) (mul_one _)
    have hkey : ∀ Q : Place k' F', ψ (τ, ρ) • (Place.constantsEquiv k k' F').symm Q =
        (Place.constantsEquiv k k' F').symm
          (twistPlace (twistAut hex h τ ρ) ρ (twistAut_algebraMap_right hex h τ ρ) Q) :=
      fun Q => smul_constantsEquiv_symm hex h Γ (hψ₀ (τ, ρ)) ρ _ Q
    refine (Nat.card_congr
      { toFun := fun Q => ⟨⟨(Place.constantsEquiv k k' F').symm Q.1,
            (restrict_constantsEquiv_symm hex h Γ Q.1).trans Q.2.1⟩, by
          apply Subtype.ext
          rw [hsmul, hφτ, hkey]
          exact congrArg _ Q.2.2⟩
        invFun := fun x => ⟨Place.constantsEquiv k k' F' x.1.1, by
            rw [← restrict_constantsEquiv_symm hex h Γ, Equiv.symm_apply_apply]; exact x.1.2, by
            apply (Place.constantsEquiv k k' F').symm.injective
            rw [← hkey, Equiv.symm_apply_apply, ← hφτ, ← hsmul, x.2]⟩
        left_inv := fun Q => Subtype.ext (Equiv.apply_symm_apply _ _)
        right_inv := fun x => Subtype.ext (Subtype.ext (Equiv.symm_apply_apply _ _)) }).symm
  let heqv : N ≃ Γ :=
    { toFun := fun n => n.1.1
      invFun := fun τ => ⟨(τ, 1), hmemN τ⟩
      left_inv := fun n => Subtype.ext (Prod.ext rfl (MonoidHom.mem_ker.mp n.2).symm)
      right_inv := fun τ => rfl }
  rw [← Nat.card_congr heqv, ← hmain]
  refine (Fintype.sum_equiv heqv _ _ fun n => ?_).symm
  have hn : (n : G) = ((n : G).1, 1) := Prod.ext rfl (MonoidHom.mem_ker.mp n.2)
  have h1 : Nat.card {x : X // (φ * (n : G)) • x = x} =
      Nat.card {x : X // (φ * (((n : G).1, 1) : G)) • x = x} := by rw [← hn]
  exact h1.trans (hconv _)

include hF hρq in
/-- **The twisting identity** $\sum_{\tau \in \Gamma} N_1(F_\tau) = |\Gamma| \cdot N_1(L_0)$, where
$F_\tau$ is the fixed field of $\tau \otimes \rho$ and $L_0$ that of $\Gamma \otimes \mathrm{Gal}(k'/k)$. -/
theorem sum_card_degree_one_twistField (hm : Nat.card Γ ∣ finrank k k') :
    ∑ τ : Γ, Nat.card {R : Place k (twistField (twistAut hex h τ ρ)) // R.degree = 1} =
      Nat.card Γ * Nat.card {P : Place k (twistBase hex h Γ) // P.degree = 1} := by
  classical
  let L := twistBase hex h Γ
  have hF'k := isFunctionField_of_constantCompositum hF h
  have hF'k' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  have hex' : IsIntegrallyClosedIn k' F' := IsIntegrallyClosedIn.of_constantCompositum_eq_top hex h
  have hL : IsFunctionField k L := hF'k.fixedField _
  have hρ := orderOf_of_forall hρq
  have hm0 : 0 < finrank k k' := Module.finrank_pos
  -- the rational places of `L₀` form a finite type
  have hSfin : {P : Place k L | P.degree = 1}.Finite :=
    (Place.finite_setOf_degree_le hL 1).subset fun P hP => le_of_eq hP
  letI : Fintype {P : Place k L // P.degree = 1} := hSfin.fintype
  -- step 1: rational fixed places of `F'/k'` are counted over the rational places of `L₀`
  have hstep : ∀ τ : Γ,
      Nat.card {Q : Place k' F' // Q.degree = 1 ∧
        twistPlace (twistAut hex h τ ρ) ρ (twistAut_algebraMap_right hex h τ ρ) Q = Q} =
      ∑ P : {P : Place k L // P.degree = 1}, Nat.card {Q : Place k' F' // Q.restrict k L = P.1 ∧
        twistPlace (twistAut hex h τ ρ) ρ (twistAut_algebraMap_right hex h τ ρ) Q = Q} := by
    intro τ
    have hfixL : ∀ x ∈ L, twistAut hex h τ ρ x = x := fun x hx =>
      (mem_fixedField_iff _ _).mp hx _ (twistAut_mem_twistGroup hex h τ.2 (Subgroup.mem_top _))
    have hdeg1 : ∀ Q : Place k' F', (Q.restrict k L).degree = 1 → Q.degree = 1 := by
      intro Q hQ
      have h1 := degree_dvd_of_forall_pow_eq_one (F₀ := L) hF'k (galois_pow_eq_one hex h Γ hm)
        ((Place.constantsEquiv k k' F').symm Q)
        (by rw [restrict_constantsEquiv_symm]; exact hQ)
      rw [degree_constantsEquiv_symm] at h1
      have h2 : Q.degree ∣ 1 := Nat.dvd_of_mul_dvd_mul_left hm0 (by simpa using h1)
      exact Nat.dvd_one.mp h2
    have hfib : ∀ P : {P : Place k L // P.degree = 1}, Finite {Q : Place k' F' //
        Q.restrict k L = P.1 ∧
        twistPlace (twistAut hex h τ ρ) ρ (twistAut_algebraMap_right hex h τ ρ) Q = Q} := by
      intro P
      have : {Q : Place k' F' | Q.restrict k L = P.1 ∧
          twistPlace (twistAut hex h τ ρ) ρ (twistAut_algebraMap_right hex h τ ρ) Q = Q}.Finite :=
        (Place.finite_setOf_restrict_eq k L P.1).subset fun Q hQ => hQ.1
      exact this.to_subtype
    rw [← Nat.card_sigma]
    refine Nat.card_congr
      { toFun := fun Q => ⟨⟨Q.1.restrict k L, degree_restrict_eq_one_of_twistPlace_eq' _ ρ
            (twistAut_algebraMap_right hex h τ ρ) hρ L hfixL Q.2.1 Q.2.2⟩, ⟨Q.1, rfl, Q.2.2⟩⟩
        invFun := fun x => ⟨x.2.1, hdeg1 _ (by rw [x.2.2.1]; exact x.1.2), x.2.2.2⟩
        left_inv := fun Q => rfl
        right_inv := fun x => Sigma.subtype_ext (Subtype.ext x.2.2.1) rfl }
  -- step 2: exchange the sums and use the count over each rational place
  have hcard : ∀ τ : Γ, Nat.card {R : Place k (twistField (twistAut hex h τ ρ)) // R.degree = 1} =
      Nat.card {Q : Place k' F' // Q.degree = 1 ∧
        twistPlace (twistAut hex h τ ρ) ρ (twistAut_algebraMap_right hex h τ ρ) Q = Q} := fun τ =>
    card_degree_one_twistField _ ρ (twistAut_algebraMap_right hex h τ ρ) hρ
      (pow_eq_one_of_dvd hex h hm τ.2 ρ) hF'k' hex'
  simp_rw [hcard, hstep]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun P _ => sum_card_fixed_fibre hF hex h Γ hρq P.1 P.2]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm, ← Nat.card_eq_fintype_card]

end Count

end ModularFormsKB.Milne
