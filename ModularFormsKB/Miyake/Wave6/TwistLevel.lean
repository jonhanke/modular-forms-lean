import ModularFormsKB.Miyake.Wave6.LevelChange
import TauCeti.NumberTheory.ModularForms.Twist.Basic

/-!
# Miyake §4.3: the level of a twist, Lemma 4.3.10 (2)

Miyake, *Modular Forms* (Springer 1989), Lemma 4.3.10 (2), p. 124: let `f ∈ 𝒢_k(N, χ)`, `m_χ` the
conductor of `χ`, `ψ` a primitive Dirichlet character of conductor `m = m_ψ`, and `M` the least
common multiple of `N`, `m²` and `m m_χ`. Then `f_ψ = Σ ψ(n) a_n e^{2πinz}` belongs to
`𝒢_k(M, χψ²)`; if `f` is a cusp form, so is `f_ψ`.

Credit: `slash_translate_slash_gamma0` and `sum_slash_translate_slash_gamma0` adapt the proofs of
Tau Ceti's private lemmas `slash_upperRightHom_slash_mapGL` and `sum_slash_upperRightHom_slash_mapGL`
(Tau Ceti 4908b03, `TauCeti/NumberTheory/ModularForms/Twist/Basic.lean`, Apache-2.0), with the
step using `N m ∣ L` replaced by the conductor argument below.

Tau Ceti's `ModularForm.twist` puts `f_ψ` at any level `L` with `N m ∣ L` and `m² ∣ L`
(`TauCeti.ModularForm.twist_mem_modFormCharSpace`), which is coarser than Miyake's `M` when
`m_χ` is a proper divisor of `N` and `m` shares a factor with `N/m_χ`. Here `f_ψ` is first built
at `L = N m²` and then descended to `Γ₁(M)` by Miyake's argument: for
`γ = [a b; cM d] ∈ Γ₀(M)` and `γ' = α(u/m) γ α(d²u/m)⁻¹`, `γ' ∈ Γ₀(N)` and `d' ≡ d mod m_χ`.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave6

open Wave4

/-- Miyake's level `M = lcm(N, m², m m_χ)` of the twist of `𝒢_k(N, χ)` by a character of
conductor `m` (Lemma 4.3.10 (2)). -/
def twistLevel {N : ℕ} (χ : DirichletCharacter ℂ N) (m : ℕ) : ℕ :=
  N.lcm ((m ^ 2).lcm (m * χ.conductor))

lemma dvd_twistLevel_left {N : ℕ} (χ : DirichletCharacter ℂ N) (m : ℕ) : N ∣ twistLevel χ m :=
  Nat.dvd_lcm_left _ _

lemma dvd_twistLevel_right {N : ℕ} (χ : DirichletCharacter ℂ N) (m : ℕ) : m ∣ twistLevel χ m :=
  (Dvd.intro m (sq m).symm).trans ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _))

instance {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (m : ℕ) [NeZero m] :
    NeZero (twistLevel χ m) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne N) (Nat.lcm_ne_zero (pow_ne_zero 2 (NeZero.ne m))
    (mul_ne_zero (NeZero.ne m) (DirichletCharacter.conductor_ne_zero χ)))⟩

/-- The character `χψ²` modulo `M = twistLevel χ m`. -/
abbrev twistChar {N : ℕ} (χ : DirichletCharacter ℂ N) {m : ℕ} (ψ : DirichletCharacter ℂ m) :
    DirichletCharacter ℂ (twistLevel χ m) :=
  DirichletCharacter.changeLevel (dvd_twistLevel_left χ m) χ *
    DirichletCharacter.changeLevel (dvd_twistLevel_right χ m) ψ ^ 2

variable {N : ℕ} [NeZero N]

open Matrix.GeneralLinearGroup (upperRightHom)
open scoped ZMod

/-- The lower-right entry of a matrix of `SL(2, ℤ)` is coprime to any `n` dividing the lower-left
entry. -/
lemma isCoprime_lowerRight_of_dvd {n : ℕ} (γ : SL(2, ℤ)) (h : (n : ℤ) ∣ γ 1 0) :
    IsCoprime (γ 1 1) (n : ℤ) := by
  obtain ⟨e, he⟩ := h
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rwa [Matrix.det_fin_two] at this
  exact ⟨γ 0 0, -(γ 0 1 * e), by linear_combination hdet + (γ 0 1) * he⟩

omit [NeZero N] in
/-- A Dirichlet character takes equal values at integers coprime to the level that are congruent
modulo its conductor. -/
lemma apply_eq_of_conductor_dvd (χ : DirichletCharacter ℂ N) {a b : ℤ}
    (ha : IsCoprime a N) (hb : IsCoprime b N) (h : (χ.conductor : ℤ) ∣ a - b) :
    χ a = χ b := by
  rw [← χ.primitiveCharacter_apply_of_isCoprime ha, ← χ.primitiveCharacter_apply_of_isCoprime hb]
  congr 1
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub a b _).mpr (by simpa [neg_sub] using dvd_neg.mpr h)

omit [NeZero N] in
/-- Miyake's matrix computation: for `g ∈ Γ₀(M)`, `M = lcm(N, m², m m_χ)`, slashing a translate of
a form with nebentypus `χ` modulo `N` by `g` gives `χ(d)` times the translate by `a d² / m`. -/
lemma slash_translate_slash_gamma0 (k : ℤ) (χ : DirichletCharacter ℂ N) {m : ℕ} [NeZero m]
    {f : ℍ → ℂ}
    (hf : ∀ g : Gamma0 N, f ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
      (χ.toUnitHom ((Gamma0Map N).toHomUnits g) : ℂ) • f)
    (g : SL(2, ℤ)) (hg : (twistLevel χ m : ℤ) ∣ g 1 0) (a : ZMod m) :
    (f ∣[k] upperRightHom ((a.val : ℝ) / m)) ∣[k] mapGL ℝ g =
      χ (g 1 1 : ZMod N) •
        (f ∣[k] upperRightHom (((a * (g 1 1 : ZMod m) ^ 2).val : ℝ) / m)) := by
  have hmM : m * m ∣ twistLevel χ m := by
    have : m ^ 2 ∣ twistLevel χ m := (Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)
    simpa [sq] using this
  have hcM : m * χ.conductor ∣ twistLevel χ m :=
    (Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)
  have hNM := dvd_twistLevel_left χ m
  obtain ⟨r, hr⟩ := hmM
  obtain ⟨s, hs⟩ := hcM
  obtain ⟨t, ht⟩ := hg
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hc : g 1 0 = m * m * (r * t) := by rw [ht, hr]; push_cast; ring
  have h1 : (m : ℤ) * m * r = m * χ.conductor * s := by exact_mod_cast hr.symm.trans hs
  have h2 : (m : ℤ) * r = χ.conductor * s := by
    apply mul_left_cancel₀ hm0
    linear_combination h1
  have hcd : (χ.conductor : ℤ) ∣ m * (r * t) := ⟨s * t, by linear_combination t * h2⟩
  have hNg : (N : ℤ) ∣ g 1 0 := (Int.natCast_dvd_natCast.mpr hNM).trans ⟨t, ht⟩
  obtain ⟨γ', hA', hC', hD', heq⟩ := TauCeti.exists_upperRightHom_mul_mapGL_eq_mapGL_mul_upperRightHom
    (M := m) g (a := a.val) (a' := (a * (g 1 1 : ZMod m) ^ 2).val) hc (by simp)
  have hγ' : γ' ∈ Gamma0 N := by
    rw [Gamma0_mem, hC']
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNg
  simp only [Int.cast_natCast] at heq
  rw [← SlashAction.slash_mul, heq, SlashAction.slash_mul, hf ⟨γ', hγ'⟩]
  have hχ : (χ.toUnitHom ((Gamma0Map N).toHomUnits ⟨γ', hγ'⟩) : ℂ) = χ (g 1 1 : ZMod N) := by
    rw [MulChar.coe_toUnitHom, MonoidHom.coe_toHomUnits, Gamma0Map_apply]
    refine (apply_eq_of_conductor_dvd χ
      (isCoprime_lowerRight_of_dvd g hNg)
      (isCoprime_lowerRight_of_dvd γ' (by rw [hC']; exact hNg)) ?_).symm
    rw [hD', sub_sub_cancel, mul_assoc]
    exact hcd.mul_left _
  rw [hχ]
  ext τ
  simp

omit [NeZero N] in
/-- The transformation law of the twisted function under `Γ₀(M)`: it transforms by `χ(d) ψ(d)²`. -/
lemma sum_slash_translate_slash_gamma0 (k : ℤ) (χ : DirichletCharacter ℂ N) {m : ℕ} [NeZero m]
    (ψ : DirichletCharacter ℂ m) {f : ℍ → ℂ}
    (hf : ∀ g : Gamma0 N, f ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
      (χ.toUnitHom ((Gamma0Map N).toHomUnits g) : ℂ) • f)
    (g : SL(2, ℤ)) (hg : (twistLevel χ m : ℤ) ∣ g 1 0) :
    ((m : ℂ)⁻¹ • ∑ a : ZMod m, 𝓕 ψ a • (f ∣[k] upperRightHom ((a.val : ℝ) / m))) ∣[k]
        mapGL ℝ g =
      (χ (g 1 1 : ZMod N) * ψ (g 1 1 : ZMod m) ^ 2) •
        ((m : ℂ)⁻¹ • ∑ a : ZMod m, 𝓕 ψ a • (f ∣[k] upperRightHom ((a.val : ℝ) / m))) := by
  have hmg : (m : ℤ) ∣ g 1 0 :=
    (Int.natCast_dvd_natCast.mpr (dvd_twistLevel_right χ m)).trans hg
  set u := ZMod.unitOfIsCoprime (g 1 1) (isCoprime_lowerRight_of_dvd g hmg) with hu_def
  have hu : (u : ZMod m) = (g 1 1 : ZMod m) := ZMod.coe_unitOfIsCoprime _ _
  have hsmul (c : ℂ) (F : ℍ → ℂ) :
      (c • F) ∣[k] mapGL ℝ g = c • F ∣[k] mapGL ℝ g :=
    _root_.ModularForm.SL_smul_slash k g F c
  have hF (a : ZMod m) : 𝓕 ψ a = ψ u ^ 2 * 𝓕 ψ (a * (u : ZMod m) ^ 2) := by
    have h := ZMod.dft_comp_unitMul (⇑ψ) (u ^ 2) (↑(u ^ 2) * a)
    have hfun : (fun j ↦ ψ (↑(u ^ 2) * j)) = ψ ↑(u ^ 2) • ⇑ψ := by
      ext j
      simp
    rw [hfun, _root_.map_smul, Units.inv_mul_cancel_left, Pi.smul_apply, smul_eq_mul] at h
    rw [← h, mul_comm _ a]
    simp [Units.val_pow_eq_pow_val]
  have hre (c : ℂ) (F : ZMod m → ℍ → ℂ) :
      ∑ a : ZMod m, 𝓕 ψ a • c • F (a * (u : ZMod m) ^ 2) = (c * ψ u ^ 2) • ∑ a, 𝓕 ψ a • F a := by
    rw [Finset.smul_sum]
    refine Fintype.sum_equiv (Units.mulRight (u ^ 2)) _ _ fun a ↦ ?_
    simp only [Units.mulRight_apply, Units.val_pow_eq_pow_val]
    rw [hF a, smul_smul, smul_smul]
    congr 1
    ring
  rw [hsmul, SlashAction.sum_slash]
  simp_rw [hsmul, slash_translate_slash_gamma0 k χ hf g hg, ← hu]
  rw [hre _ (fun b ↦ f ∣[k] upperRightHom ((b.val : ℝ) / m)), smul_comm]

omit [NeZero N] in
/-- The twisted function transforms under `Γ₀(M)` by the character `χψ²` modulo `M`. -/
lemma twist_slash_gamma0 (k : ℤ) (χ : DirichletCharacter ℂ N) {m : ℕ} [NeZero m]
    (ψ : DirichletCharacter ℂ m) {f F : ℍ → ℂ}
    (hf : ∀ g : Gamma0 N, f ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
      (χ.toUnitHom ((Gamma0Map N).toHomUnits g) : ℂ) • f)
    (hF : F = (m : ℂ)⁻¹ • ∑ a : ZMod m, 𝓕 ψ a • (f ∣[k] upperRightHom ((a.val : ℝ) / m)))
    (g : SL(2, ℤ)) (hg : (twistLevel χ m : ℤ) ∣ g 1 0) :
    F ∣[k] mapGL ℝ g = (twistChar χ ψ (g 1 1 : ZMod (twistLevel χ m)) : ℂ) • F := by
  have hcop := isCoprime_lowerRight_of_dvd g hg
  have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ (dvd_twistLevel_left χ m) hcop
  have h2 := DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ (dvd_twistLevel_right χ m) hcop
  rw [hF, sum_slash_translate_slash_gamma0 k χ ψ hf g hg]
  congr 1
  rw [twistChar, MulChar.mul_apply, MulChar.pow_apply' _ two_ne_zero, h1, h2]

/-- **Miyake, Lemma 4.3.10 (2)** (modular forms): for `f ∈ 𝒢_k(N, χ)` and a primitive character `ψ`
modulo `m`, the twist `f_ψ = Σ ψ(n) a_n qⁿ` lies in `𝒢_k(M, χψ²)`, `M = lcm(N, m², m m_χ)`. -/
@[kb "miyake1989" "Lemma 4.3.10 (2), p. 124 (modular forms)"]
theorem exists_modSpace_twist (k : ℤ) (χ : DirichletCharacter ℂ N) {m : ℕ} [NeZero m]
    (ψ : DirichletCharacter ℂ m) (hψ : ψ.IsPrimitive) (f : modSpace k χ) :
    ∃ g : modSpace k (twistChar χ ψ), ∀ n : ℕ, coeffMod g n = ψ n * coeffMod f n := by
  have hNL : N * m ∣ N * (m * m) := mul_dvd_mul_left N (dvd_mul_right m m)
  have hML : m * m ∣ N * (m * m) := dvd_mul_left _ _
  have hf : ∀ g : Gamma0 N, ⇑f.1 ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
      (χ.toUnitHom ((Gamma0Map N).toHomUnits g) : ℂ) • ⇑f.1 :=
    (TauCeti.mem_modFormCharSpace_iff_nebentypus k χ.toUnitHom f.1).mp f.2
  have hsum : ⇑(ModularForm.twist ψ hNL hML f.1) =
      (m : ℂ)⁻¹ • ∑ a : ZMod m, 𝓕 ψ a • (⇑f.1 ∣[k] upperRightHom ((a.val : ℝ) / m)) := by
    ext τ
    simp only [ModularForm.twist_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
      TauCeti.ModularForm.slash_upperRightHom_apply]
  have hslash := twist_slash_gamma0 k χ ψ hf hsum
  let gF : ModularForm ((Gamma1 (twistLevel χ m)).map (mapGL ℝ)) k :=
    ModularForm.ofSlashInvariant Subgroup.IsArithmetic.isCusp_of_isCusp
      (ModularForm.twist ψ hNL hML f.1) (by
        rintro _ ⟨γ, hγ, rfl⟩
        obtain ⟨hA, hD, hC⟩ := (Gamma1_mem _ γ).mp hγ
        have hdvd : (twistLevel χ m : ℤ) ∣ γ 1 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hC
        rw [hslash γ hdvd, hD, map_one, one_smul])
  have hgF : ⇑gF = ⇑(ModularForm.twist ψ hNL hML f.1) := ModularForm.coe_ofSlashInvariant _ _ _
  refine ⟨⟨gF, (TauCeti.mem_modFormCharSpace_iff_nebentypus k _ gF).mpr fun g ↦ ?_⟩, fun n ↦ ?_⟩
  · have hg : (twistLevel χ m : ℤ) ∣ (g : SL(2, ℤ)) 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp g.2)
    rw [hgF, hslash _ hg, MulChar.coe_toUnitHom, MonoidHom.coe_toHomUnits, Gamma0Map_apply]
  · show (qExpansion 1 ⇑gF).coeff n = ψ n * (qExpansion 1 ⇑f.1).coeff n
    rw [hgF]
    exact ModularForm.qExpansion_twist_coeff ψ hNL hML f.1 n

/-- **Miyake, Lemma 4.3.10 (2)** (cusp forms): if `f ∈ 𝒮_k(N, χ)`, then `f_ψ ∈ 𝒮_k(M, χψ²)`. -/
@[kb "miyake1989" "Lemma 4.3.10 (2), p. 124 (cusp forms)"]
theorem exists_cuspSpace_twist (k : ℤ) (χ : DirichletCharacter ℂ N) {m : ℕ} [NeZero m]
    (ψ : DirichletCharacter ℂ m) (hψ : ψ.IsPrimitive) (f : cuspSpace k χ) :
    ∃ g : cuspSpace k (twistChar χ ψ), ∀ n : ℕ, coeff g n = ψ n * coeff f n := by
  have hNL : N * m ∣ N * (m * m) := mul_dvd_mul_left N (dvd_mul_right m m)
  have hML : m * m ∣ N * (m * m) := dvd_mul_left _ _
  have hf : ∀ g : Gamma0 N, ⇑f.1 ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
      (χ.toUnitHom ((Gamma0Map N).toHomUnits g) : ℂ) • ⇑f.1 :=
    (TauCeti.mem_cuspFormCharSpace_iff_nebentypus k χ.toUnitHom f.1).mp f.2
  have hsum : ⇑(CuspForm.twist ψ hNL hML f.1) =
      (m : ℂ)⁻¹ • ∑ a : ZMod m, 𝓕 ψ a • (⇑f.1 ∣[k] upperRightHom ((a.val : ℝ) / m)) := by
    ext τ
    simp only [CuspForm.twist_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
      TauCeti.ModularForm.slash_upperRightHom_apply]
  have hslash := twist_slash_gamma0 k χ ψ hf hsum
  let gF : CuspForm ((Gamma1 (twistLevel χ m)).map (mapGL ℝ)) k :=
    CuspForm.ofSlashInvariant Subgroup.IsArithmetic.isCusp_of_isCusp
      (CuspForm.twist ψ hNL hML f.1) (by
        rintro _ ⟨γ, hγ, rfl⟩
        obtain ⟨hA, hD, hC⟩ := (Gamma1_mem _ γ).mp hγ
        have hdvd : (twistLevel χ m : ℤ) ∣ γ 1 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hC
        rw [hslash γ hdvd, hD, map_one, one_smul])
  have hgF : ⇑gF = ⇑(CuspForm.twist ψ hNL hML f.1) := CuspForm.coe_ofSlashInvariant _ _ _
  refine ⟨⟨gF, (TauCeti.mem_cuspFormCharSpace_iff_nebentypus k _ gF).mpr fun g ↦ ?_⟩, fun n ↦ ?_⟩
  · have hg : (twistLevel χ m : ℤ) ∣ (g : SL(2, ℤ)) 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp g.2)
    rw [hgF, hslash _ hg, MulChar.coe_toUnitHom, MonoidHom.coe_toHomUnits, Gamma0Map_apply]
  · show (qExpansion 1 ⇑gF).coeff n = ψ n * (qExpansion 1 ⇑f.1).coeff n
    rw [hgF]
    exact CuspForm.qExpansion_twist_coeff ψ hNL hML f.1 n

end ModularFormsKB.Miyake.Wave6
