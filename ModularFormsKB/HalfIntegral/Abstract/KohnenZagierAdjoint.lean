/-
# `KohnenAdjoint` from `KohnenDLift`

Let $D$ be a fundamental discriminant with $(-1)^kD > 0$.

If the $D$-th lift maps $S^+_{k+1/2}(4)$ to $S_{2k}(\mathrm{SL}_2(\mathbb Z))$ (`KohnenDLift`) and $S^+_{k+1/2}(4)$ is
finite dimensional, then there is a map $\mathcal S_D^*$ with $\langle \mathcal S_D g', G\rangle = \langle g', \mathcal S_D^*G\rangle$
(`kohnenAdjoint_of_dLift`, the structure `KohnenAdjoint`).

**Proof.** `KohnenDLift` gives a linear map $T : S^+ \to S_{2k}$ (`kzLift`), because a level one form is determined by
its $q$-expansion. For $G \in S_{2k}$, $g' \mapsto \langle G, Tg'\rangle$ is a linear functional on $S^+$. By Riesz
representation (`exists_riesz`; $S^+$ finite dimensional, `plusInnerCore` definite) it is $g' \mapsto \langle h_G, g'\rangle$.
Put $\mathcal S_D^*G = h_G$. Mathlib's `LinearMap.adjoint` is not used: it needs both spaces finite dimensional, and
finite dimension of $S_{2k}$ is not needed here.

Uniqueness: any two maps with the property agree (`KohnenAdjoint` determines `Sstar G` through `KohnenDLift` and
definiteness), so a hypothesis "for every `Sstar` with `KohnenAdjoint`" says the same as "for the adjoint".
-/
import ModularFormsKB.HalfIntegral.Abstract.KohnenZagierInner
import ModularFormsKB.HalfIntegral.Abstract.KohnenReduction
import ModularFormsKB.HalfIntegral.Abstract.KohnenEigen

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup MeasureTheory UpperHalfPlane ModularForm
open scoped Real ComplexConjugate

variable {M : MultiplierSystem} {k : ℕ} {D : ℤ}

/-- Every element of $S^+_{k+1/2}(4)$ has a $q$-expansion. -/
theorem exists_hasQExp_plus (f : M.plusCuspForms k 1 1) : ∃ a, Abstract.HasQExp f a := by
  obtain ⟨_, a, ha, _⟩ := f.2
  exact ⟨a, ha⟩

/-- A level one cusp form is determined by its $q$-expansion coefficients (as a function). -/
theorem cuspForm_ext_of_hasQExp {w : ℤ} {F G : CuspForm 𝒮ℒ w} {a : ℕ → ℂ} (hF : Abstract.HasQExp F a)
    (hG : Abstract.HasQExp G a) : F = G :=
  DFunLike.ext _ _ (congrFun (Abstract.eq_of_hasQExp hF hG))

/-- The lift of an element of $S^+$ exists with the expansion `kohnenLiftCoeff k D a`, for every expansion $a$. -/
theorem exists_kzLift (hk : 1 ≤ k) (hL : KohnenDLift M k D) (f : M.plusCuspForms k 1 1) :
    ∃ F : CuspForm 𝒮ℒ (2 * k : ℕ), ∀ a, Abstract.HasQExp f a → Abstract.HasQExp F (kohnenLiftCoeff k D a) := by
  obtain ⟨a0, ha0⟩ := exists_hasQExp_plus f
  obtain ⟨F, hF⟩ := hL.lift hk f f.2 a0 ha0
  exact ⟨F, fun a ha ↦ by rw [Abstract.hasQExp_unique ha ha0]; exact hF⟩

/-- **The $D$-th lift as a linear map** $S^+_{k+1/2}(4) \to S_{2k}(\mathrm{SL}_2(\mathbb Z))$. -/
noncomputable def kzLift (hk : 1 ≤ k) (hL : KohnenDLift M k D) :
    M.plusCuspForms k 1 1 →ₗ[ℂ] CuspForm 𝒮ℒ (2 * k : ℕ) where
  toFun f := Classical.choose (exists_kzLift hk hL f)
  map_add' f g := by
    obtain ⟨a, ha⟩ := exists_hasQExp_plus f
    obtain ⟨b, hb⟩ := exists_hasQExp_plus g
    have h1 := Classical.choose_spec (exists_kzLift hk hL (f + g)) (a + b)
      (by simpa using Abstract.hasQExp_add ha hb)
    have h2 := Abstract.hasQExp_add (Classical.choose_spec (exists_kzLift hk hL f) a ha)
      (Classical.choose_spec (exists_kzLift hk hL g) b hb)
    have hl : kohnenLiftCoeff k D (a + b) = kohnenLiftCoeff k D a + kohnenLiftCoeff k D b :=
      (kohnenLiftLin k D).map_add a b
    rw [hl] at h1
    exact cuspForm_ext_of_hasQExp h1 (by simpa using h2)
  map_smul' c f := by
    obtain ⟨a, ha⟩ := exists_hasQExp_plus f
    have h1 := Classical.choose_spec (exists_kzLift hk hL (c • f)) (c • a)
      (by simpa using Abstract.hasQExp_smul c ha)
    have h2 := Abstract.hasQExp_smul c (Classical.choose_spec (exists_kzLift hk hL f) a ha)
    have : kohnenLiftCoeff k D (c • a) = c • kohnenLiftCoeff k D a := (kohnenLiftLin k D).map_smul c a
    rw [this] at h1
    exact cuspForm_ext_of_hasQExp h1 (by simpa using h2)

/-- The defining property of `kzLift`. -/
theorem hasQExp_kzLift (hk : 1 ≤ k) (hL : KohnenDLift M k D) (f : M.plusCuspForms k 1 1) {a : ℕ → ℂ}
    (ha : Abstract.HasQExp f a) : Abstract.HasQExp (kzLift hk hL f) (kohnenLiftCoeff k D a) :=
  Classical.choose_spec (exists_kzLift hk hL f) a ha

/-- A level one cusp form has $q$-expansion coefficient $0$ at $n = 0$. -/
theorem coeff_zero_of_cusp {w : ℤ} (F : CuspForm 𝒮ℒ w) {b : ℕ → ℂ} (hF : Abstract.HasQExp F b) : b 0 = 0 := by
  rw [hasQExp_coeff_eq_qExpansion F hF 0]
  have hp : (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    have := Subgroup.strictWidthInfty_mem_strictPeriods (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))
    rwa [Subgroup.strictWidthInfty_SL2Z] at this
  exact CuspFormClass.qExpansion_coeff_zero F one_pos hp

/-- **The adjoint functional:** for $G \in S_{2k}$, $g' \mapsto \langle G, Tg'\rangle$ is linear on $S^+$. -/
noncomputable def kzFunctional (hk : 1 ≤ k) (hL : KohnenDLift M k D) (G : CuspForm 𝒮ℒ (2 * k : ℕ)) :
    M.plusCuspForms k 1 1 →ₗ[ℂ] ℂ where
  toFun g' := peterssonOne k G (kzLift hk hL g')
  map_add' g₁ g₂ := by
    rw [map_add]
    exact peterssonOne_add_right k G _ _
  map_smul' c g' := by
    rw [map_smul]
    simp only [peterssonOne]
    rw [show ((c • kzLift hk hL g' : CuspForm 𝒮ℒ (2 * k : ℕ)) : ℍ → ℂ) = c • ⇑(kzLift hk hL g') from rfl,
      peterssonReps_smul_right]
    rfl

/-- **Row 20: `KohnenAdjoint` from `KohnenDLift`.** If $S^+_{k+1/2}(4)$ is finite dimensional and the $D$-th lift maps
it to level one cusp forms, then the adjoint $\mathcal S_D^*$ exists. -/
theorem kohnenAdjoint_of_dLift (M : MultiplierSystem) (k : ℕ) (hk : 1 ≤ k)
    (hfin : FiniteDimensional ℂ (M.plusCuspForms k 1 1)) {D : ℤ} (hL : KohnenDLift M k D) :
    ∃ Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ, KohnenAdjoint M k D Sstar := by
  have hR := fun G ↦ exists_riesz (plusInnerCore M k) (kzFunctional hk hL G)
  choose h hh using hR
  refine ⟨fun G ↦ (h G : ℍ → ℂ), ⟨fun G ↦ (h G).2, ?_⟩⟩
  intro g' hg' c' hc' G' b' hb' hb G
  set g'' : M.plusCuspForms k 1 1 := ⟨g', hg'⟩
  have hGT : G' = kzLift hk hL g'' := by
    refine cuspForm_ext_of_hasQExp (a := b') hb' ?_
    have h0 : b' 0 = 0 := coeff_zero_of_cusp G' hb'
    have hfun : b' = kohnenLiftCoeff k D c' := by
      funext n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [h0, kohnenLiftCoeff_zero]
      · exact hb n hn
    rw [hfun]
    exact hasQExp_kzLift hk hL g'' hc'
  subst hGT
  have e : peterssonFour k (h G : ℍ → ℂ) g' = peterssonOne k G (kzLift hk hL g'') := hh G g''
  rw [peterssonFour_conj_symm k (h G : ℍ → ℂ) g', e]
  exact peterssonReps_conj_symm _ _ _ _ 

end ModularFormsKB.HalfIntegral
