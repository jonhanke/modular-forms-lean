import ModularFormsKB.Elliptic.StrongHasseWeil
import ModularFormsKB.Miyake.Sec4_3.WeilTheorem
import ModularFormsKB.HalfIntegral.WeilBridge

/-!
# Weil's converse theorem for elliptic curves; H3 for all curves from the modularity theorem

- `StrongHasseWeilUniform.isCuspFormChar` (unconditional): if $E$ satisfies the strong Hasse–Weil conjecture with a
  uniform sign $w$, then $\sum a_n(E)q^n \in S_2(N, 1)$, $N$ the geometric conductor, and
  $f|_2\omega_N = -w f$. This is Weil's converse theorem (Miyake Theorem 4.3.15, `Miyake.weil_cusp`, with the Weil
  set of `Miyake.exists_weilSet`), the cusp condition coming from the absolute convergence of $L(E, s)$ at
  $s = 2 - 1/4$ (`lSeriesSummable_coeffE`).
- `NewformOfConductor` (named statement): a cusp form on $\Gamma_0(N)$, $N$ the conductor of $E$, whose coefficients
  are those of $L(E, s)$ is a newform. Classically: Atkin–Lehner–Li theory (Miyake Theorems 4.6.13, 4.6.19) and the
  fact that the conductor of the twisted functional equations is the level of the primitive form (Li 1975
  [unverified]). Tau Ceti main's `Newforms/Conductor.lean` (past our pin) is the route.
- `exists_hasNewform_of_strongHasseWeilUniform` (row 23): with `NewformOfConductor`, the uniform strong Hasse–Weil
  conjecture gives a newform of level $N$ with the coefficients of $E$; `exists_hasNewform_iff` is the equivalence.
- **H3 for every curve, from `ModularityTheorem` alone**: `ModularityTheorem.strongHasseWeil`,
  `ModularityTheorem.hasEntireExtension`, `ModularityTheorem.exists_functionalEquation`.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Complex
open scoped MatrixGroups Real

namespace ModularFormsKB.Elliptic

open HeckeRing.GL2 ModularFormsKB.Milne.Wave4B

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] {w : ℂ}

/-- The `q`-expansion of a cusp form on `Γ₁(N)` is its `Miyake.qSeries`, with coefficients of polynomial
growth. -/
private theorem cuspForm_qSeries_coeff' {N : ℕ} [NeZero N] {k : ℤ} (F : CuspForm ((Gamma1 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) :
    Miyake.CoeffGrowth (fun n ↦ (qExpansion 1 F).coeff n) ∧
      ∀ τ : ℍ, F τ = Miyake.qSeries (fun n ↦ (qExpansion 1 F).coeff n) τ := by
  have hΓ : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _
  have hg : Miyake.CoeffGrowth (fun n ↦ (qExpansion 1 F).coeff n) := by
    have := CuspFormClass.qExpansion_isBigO F
    rw [strictWidthInfty_Gamma1] at this
    exact ⟨_, this⟩
  refine ⟨hg, fun τ ↦ ?_⟩
  have : Fact (IsCusp OnePoint.infty (Gamma1 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  have h := UpperHalfPlane.hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex F hΓ) (ModularFormClass.holo F)
    (ModularFormClass.bdd_at_infty F) τ
  have e : (fun n : ℕ ↦ (qExpansion 1 F).coeff n • Function.Periodic.qParam 1 (τ : ℂ) ^ n) =
      fun n : ℕ ↦ (qExpansion 1 F).coeff n * Complex.exp (2 * Real.pi * Complex.I * n * τ) := by
    funext n
    rw [Function.Periodic.qParam, ← Complex.exp_nat_mul, smul_eq_mul]
    congr 2
    push_cast
    ring
  rw [e] at h
  exact h.tsum_eq.symm

private lemma twistedHecke_of_uniform (h : StrongHasseWeilUniform E w) {m : ℕ} [NeZero m]
    (hm : m.Coprime (geometricConductor E)) (ψ : DirichletCharacter ℂ m) (hψ : ψ.IsPrimitive) :
    Miyake.TwistedHeckeCondition 2 (geometricConductor E) ψ
      (Miyake.weilConstant (1 : DirichletCharacter ℂ (geometricConductor E)) ψ)
      (coeffE E) (fun n ↦ -w * coeffE E n) := by
  obtain ⟨Λ, Λ', ⟨hd, he, hb⟩, ⟨-, he', -⟩, hfe⟩ := h.2 m hm ψ hψ
  refine ⟨Λ, hd, hb, 3 / 2, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · rw [he s hs, twistedCompletedL_eq]
  · simp only [Nat.cast_ofNat] at hs ⊢
    have h3 : (3 / 2 : ℝ) < (2 - s).re := by simpa using hs
    rw [hfe s, he' (2 - s) h3, ← twistedCompletedL_eq E ψ⁻¹ (2 - s), twistedCompletedL_const_mul,
      weilConstant_one_eq E hm ψ, Complex.I_sq]
    ring

private lemma heckeCondition_of_uniform (h : StrongHasseWeilUniform E w) :
    Miyake.HeckeCondition ((2 : ℕ) : ℝ) (geometricConductor E) (Complex.I ^ 2) (coeffE E)
      (fun n ↦ -w * coeffE E n) := by
  have hprim : (1 : DirichletCharacter ℂ 1).IsPrimitive := DirichletCharacter.isPrimitive_one_level_one
  obtain ⟨Λ, Λ', ⟨hd, he, hb⟩, ⟨-, he', -⟩, hfe⟩ := h.2 1 (Nat.coprime_one_left _) 1 hprim
  rw [inv_one] at he' hfe
  have hu : ∀ x : ZMod 1, (1 : DirichletCharacter ℂ 1) x = 1 := fun x ↦
    MulChar.one_apply (isUnit_of_subsingleton x)
  have hg : gaussSum (1 : DirichletCharacter ℂ 1) ZMod.stdAddChar /
      gaussSum (1 : DirichletCharacter ℂ 1) ZMod.stdAddChar = 1 :=
    div_self (Miyake.gaussW_ne_zero hprim)
  have hcomp : ∀ s, Miyake.twistedCompletedL (geometricConductor E) (1 : DirichletCharacter ℂ 1) (coeffE E) s =
      Miyake.completedL (geometricConductor E) (coeffE E) s := by
    intro s
    have : Miyake.twist (1 : DirichletCharacter ℂ 1) (coeffE E) = coeffE E := by
      funext n; simp [Miyake.twist, hu]
    simp [Miyake.twistedCompletedL, Miyake.completedL, this]
  have ha0 : coeffE E 0 = 0 := by simp [coeffE]
  refine ⟨Λ, hd, hb, 3 / 2, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · rw [he s hs, ← twistedCompletedL_eq, hcomp]; simp [ha0]
  · simp only [Nat.cast_ofNat] at hs ⊢
    have h3 : (3 / 2 : ℝ) < (2 - s).re := by simpa using hs
    rw [hfe s, he' (2 - s) h3, ← twistedCompletedL_eq E 1 (2 - s), hcomp,
      show (fun n ↦ -w * coeffE E n) = fun n ↦ -w * coeffE E n from rfl, Miyake.completedL_const_mul,
      hu, hu, hg, Complex.I_sq, ha0]
    simp

/-- **Weil's converse theorem for an elliptic curve** (row 23; Weil 1967, Miyake Theorem 4.3.15): the uniform strong
Hasse–Weil conjecture makes $\sum a_n(E)q^n$ a cusp form of weight $2$ on $\Gamma_0(N)$, $N$ the geometric conductor,
with $f|_2\omega_N = -w f$. -/
@[kb "miyake1989" "§4.3, Theorem 4.3.15 (Weil), applied to L(E,s) with its twists"]
theorem StrongHasseWeilUniform.isCuspFormChar {E : WeierstrassCurve ℚ} [E.IsElliptic] {w : ℂ}
    (h : StrongHasseWeilUniform E w) :
    Miyake.IsCuspFormChar 2 (geometricConductor E) 1 (fun τ : ℍ ↦ Miyake.qSeries (coeffE E) τ) ∧
      ∀ z : ℂ, 0 < z.im →
        Miyake.fricke 2 (geometricConductor E) (Miyake.qSeries (coeffE E)) z = -w * Miyake.qSeries (coeffE E) z := by
  have hN := geometricConductor_pos E
  have hM := Miyake.exists_weilSet hN
  have hcχ : (1 : DirichletCharacter ℂ (geometricConductor E)) (-1) = (-1) ^ 2 := by
    rw [MulChar.one_apply isUnit_one.neg]; norm_num
  have hL : LSeriesSummable (coeffE E) (((2 : ℕ) : ℂ) - ((1 / 4 : ℝ) : ℂ)) :=
    lSeriesSummable_coeffE E (by simp; norm_num)
  have h1 := heckeCondition_of_uniform h
  have h2 : ∀ (m : ℕ) [NeZero m], m ∈ {m : ℕ | m.Prime ∧ m ≠ 2 ∧ m.Coprime (geometricConductor E)} →
      ∀ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive →
        Miyake.TwistedHeckeCondition 2 (geometricConductor E) ψ
          (Miyake.weilConstant (1 : DirichletCharacter ℂ (geometricConductor E)) ψ)
          (coeffE E) (fun n ↦ -w * coeffE E n) :=
    fun m _ hm ψ hψ ↦ twistedHecke_of_uniform h hm.2.2 ψ hψ
  refine ⟨(Miyake.weil_cusp (k := 2) (by norm_num) hN 1 hcχ (coeffGrowth_coeffE E)
    ((coeffGrowth_coeffE E).const_mul _) hM h1 h2 (δ := 1 / 4) (by norm_num) hL).1, fun z hz ↦ ?_⟩
  have := (Miyake.weil (k := 2) (by norm_num) hN 1 hcχ (coeffGrowth_coeffE E)
    ((coeffGrowth_coeffE E).const_mul _) hM h1 h2).2.2 z hz
  rw [Miyake.qSeries_const_mul] at this
  exact_mod_cast this.symm

/-- **Newness from the conductor** (named statement; Atkin–Lehner 1970, Li 1975 [unverified]; Miyake Theorems 4.6.13
and 4.6.19 with the conductor of the functional equations): a cusp form of weight $2$ on $\Gamma_1(N)$, invariant under
$\Gamma_0(N)$, $N$ the geometric conductor of $E$, whose Fourier coefficients are those of $L(E, s)$, is (the
underlying form of) a Tau Ceti newform of level $N$. -/
structure NewformOfConductor : Prop where
  exists_newform : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (F : CuspForm ((Gamma1 (geometricConductor E)).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2),
    (∀ γ ∈ Gamma0 (geometricConductor E), (⇑F : ℍ → ℂ) ∣[(2 : ℤ)] γ = ⇑F) →
    (∀ n : ℕ, (qExpansion 1 F).coeff n = (E.LFunction n : ℂ)) →
      ∃ f : Newform (geometricConductor E) 2, f.toCuspForm = F

/-- **Row 23**: with `NewformOfConductor`, a curve satisfying the uniform strong Hasse–Weil conjecture has a newform
of level its geometric conductor. -/
theorem exists_hasNewform_of_strongHasseWeilUniform (hN : NewformOfConductor) {E : WeierstrassCurve ℚ}
    [E.IsElliptic] {w : ℂ} (h : StrongHasseWeilUniform E w) :
    ∃ f : Newform (geometricConductor E) 2, HasNewform E (geometricConductor E) f := by
  obtain ⟨⟨⟨F, hF⟩, hinv⟩, -⟩ := h.isCuspFormChar
  have hcoeff : ∀ n : ℕ, (qExpansion 1 F).coeff n = (E.LFunction n : ℂ) := by
    obtain ⟨hg, hq⟩ := cuspForm_qSeries_coeff' F
    have := Miyake.qSeries_coeff_unique hg (coeffGrowth_coeffE E) fun z hz ↦
      (hq ⟨z, hz⟩).symm.trans (congrFun hF ⟨z, hz⟩)
    exact fun n ↦ congrFun this n
  have hΓ : ∀ γ ∈ Gamma0 (geometricConductor E), (⇑F : ℍ → ℂ) ∣[(2 : ℤ)] γ = ⇑F := by
    intro γ hγ
    have hdet := γ.det_coe
    rw [Matrix.det_fin_two] at hdet
    have hz : ((γ 0 0 : ℤ) : ZMod (geometricConductor E)) * (γ 1 1 : ℤ) = 1 := by
      have h1 : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod (geometricConductor E)) = 1 := by
        rw [hdet]; simp
      have h2 : ((γ 1 0 : ℤ) : ZMod (geometricConductor E)) = 0 := (Gamma0_mem).1 hγ
      push_cast at h1
      rw [h2] at h1
      simpa using h1
    have hu : IsUnit ((γ 1 1 : ℤ) : ZMod (geometricConductor E)) :=
      IsUnit.of_mul_eq_one ((γ 0 0 : ℤ) : ZMod (geometricConductor E)) (by rwa [mul_comm] at hz)
    have := hinv γ hγ
    rw [MulChar.one_apply hu, one_smul] at this
    rw [hF]; exact this
  obtain ⟨f, hfF⟩ := hN.exists_newform E F hΓ hcoeff
  have hmem : F ∈ TauCeti.cuspFormCharSpace 2 (1 : (ZMod (geometricConductor E))ˣ →* ℂˣ) := by
    refine (TauCeti.mem_cuspFormCharSpace_one_iff _).2 ?_
    rintro - ⟨g, hg, rfl⟩
    have := hΓ g hg
    rw [ModularForm.SL_slash] at this
    exact this
  have hne : F ≠ 0 := by
    intro h0
    have := hcoeff 1
    have h2 : qExpansion 1 (⇑F) = 0 := by rw [h0]; exact qExpansion_zero 1
    rw [h2, WeierstrassCurve.LFunction_apply_one] at this
    simp at this
  have hf := f.mem_charSpace
  rw [hfF] at hf
  exact ⟨f, TauCeti.eq_of_mem_cuspFormCharSpace_of_ne_zero hf hmem hne,
    fun n ↦ by rw [hfF]; exact hcoeff n⟩

/-- **Row 23, the equivalence** (Milne's Theorem 11.19 in analytic form, with the uniform sign): given
`NewformOfConductor`, $E$ has a newform of level its conductor if and only if it satisfies the uniform strong
Hasse–Weil conjecture for some $w$. -/
@[kb "milne2017mf" "Section 11, Thm. 11.19 (pdf p. 117), analytic form: newform of level N_E ⇔ strong Hasse-Weil"]
theorem exists_hasNewform_iff (hN : NewformOfConductor) (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (∃ f : Newform (geometricConductor E) 2, HasNewform E (geometricConductor E) f) ↔
      ∃ w : ℂ, StrongHasseWeilUniform E w :=
  ⟨fun ⟨f, hf⟩ ↦ ⟨_, hf.strongHasseWeilUniform⟩,
    fun ⟨_, h⟩ ↦ exists_hasNewform_of_strongHasseWeilUniform hN h⟩

/-! ### H3 for every elliptic curve over $\mathbb Q$, from the modularity theorem -/

/-- **H3**: from `ModularityTheorem`, every elliptic curve over $\mathbb Q$ satisfies Milne's strong Hasse–Weil
conjecture. -/
theorem ModularityTheorem.strongHasseWeil (h : ModularityTheorem) (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    StrongHasseWeil E := by
  obtain ⟨f, hf⟩ := h.exists_newform E
  exact hf.strongHasseWeil

/-- **H3**: from `ModularityTheorem`, $L(E, s)$ is entire for every elliptic curve $E$ over $\mathbb Q$. -/
theorem ModularityTheorem.hasEntireExtension (h : ModularityTheorem) (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    LSeries.HasEntireExtension (coeffE E) := by
  obtain ⟨f, hf⟩ := h.exists_newform E
  exact hf.hasEntireExtension

/-- **H3**: from `ModularityTheorem`, every elliptic curve $E$ over $\mathbb Q$ of conductor $N$ has an entire
$\Lambda(E, s)$, equal to $N^{s/2}(2\pi)^{-s}\Gamma(s)L(E, s)$ on $\operatorname{Re}s > 3/2$, with
$\Lambda(E, 2 - s) = w\Lambda(E, s)$ for a sign $w = \pm1$; if $w = -1$, every continuation of $L(E, s)$ to a connected
open set containing $1$ vanishes there. -/
theorem ModularityTheorem.exists_functionalEquation (h : ModularityTheorem) (E : WeierstrassCurve ℚ)
    [E.IsElliptic] :
    ∃ Λ : ℂ → ℂ, ∃ w : ℂ, Differentiable ℂ Λ ∧ (w = 1 ∨ w = -1) ∧
      (∀ s : ℂ, 3 / 2 < s.re → Λ s = (geometricConductor E : ℂ) ^ (s / 2) * (2 * π : ℂ) ^ (-s) * Gamma s *
        LSeries (coeffE E) s) ∧
      (∀ s : ℂ, Λ (2 - s) = w * Λ s) ∧
      (w = -1 → ∀ ⦃F : ℂ → ℂ⦄ ⦃U : Set ℂ⦄, LSeries.IsContinuationOn ((↑) ∘ E.LFunction) F U → 1 ∈ U → F 1 = 0) := by
  obtain ⟨f, hf⟩ := h.exists_newform E
  exact ⟨completedLE f, rootNumber f hf.χ_eq_one, differentiable_completedLE f,
    rootNumber_eq_one_or_neg_one f hf.χ_eq_one, fun s hs ↦ hf.completedLE_eq hs, hf.completedLE_two_sub,
    fun hw _ _ hF h1 ↦ hf.eq_zero_at_one_of_isContinuationOn hw hF h1⟩

end ModularFormsKB.Elliptic
