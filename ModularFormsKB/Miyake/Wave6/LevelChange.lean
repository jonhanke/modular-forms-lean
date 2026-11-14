import ModularFormsKB.Miyake.Wave4.HeckeCoefficients
import TauCeti.NumberTheory.ModularForms.Degeneracy

/-!
# Miyake §4.5–4.6: Hecke operators and the maps between levels

Miyake, *Modular Forms* (Springer 1989), Theorem 4.5.10 (p. 143), Lemma 4.6.1 (p. 153) and
Lemma 4.6.2 (p. 154).

* `embed`, `embedMod`: the natural embedding `𝒮_k(N, χ) ⊂ 𝒮_k(M, χ)` (resp. `𝒢_k`) for `N ∣ M`,
  the character `χ` read modulo `M` (`DirichletCharacter.changeLevel`). The underlying function
  does not change (Mathlib's `ModularForm.restrict`, Tau Ceti's nebentypus lemma
  `TauCeti.ModularForm.restrict_mem_modFormCharSpace`).
* `raise`, `raiseMod`: Miyake's `f(z) ↦ f(lz)` (his (4.6.2): `f(lz) = l^{-k/2} (f ∣_k δ_l)(z)`),
  from level `N` to level `lN`, through Tau Ceti's `levelRaise`.
* **Theorem 4.5.10**: for `N ∣ M` and `n` with `n ∣ N^∞` or `(n, M) = 1`, the embedding commutes
  with `T(n)` (`heckeT_embed`, `heckeTMod_embedMod`).
* **Lemma 4.6.1**: `f(lz) ∈ 𝒢_k(lN, χ)` (resp. `𝒮_k`) (`exists_modSpace_apply_eq`,
  `exists_cuspSpace_apply_eq`).
* **Lemma 4.6.2**: for `(n, lN) = 1`, `f ↦ f(lz)` commutes with `T(n)` (`heckeT_raise`,
  `heckeTMod_raiseMod`).

Proofs: by the coefficient formula of `T(n)` (Miyake Lemma 4.5.14, wave 4) and uniqueness of the
`q`-expansion. On `𝒢_k`, wave 4's coefficient formula covers the indices `n ≥ 1`; the constant
term is handled by the vanishing of a constant modular form of nonzero weight, so the statements
on `𝒢_k` assume `k ≠ 0` (Miyake's `k` is a positive integer in §4.6; LE-MF-0199).

The Hecke operators `T*(n)` of the "resp." clause of Theorem 4.5.10 are not defined in this
repository; that half is not formalized (LE-MF-0200).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave6

open Wave4

/-! ### Characters read at a multiple level -/

/-- The unit homomorphism of `χ` read modulo a multiple `M` of `N` is the composite with the
reduction `(ℤ/M)ˣ → (ℤ/N)ˣ`. -/
lemma toUnitHom_changeLevel {N M : ℕ} (h : N ∣ M) (χ : DirichletCharacter ℂ N) :
    (DirichletCharacter.changeLevel h χ).toUnitHom = χ.toUnitHom.comp (ZMod.unitsMap h) := by
  ext a
  simp [DirichletCharacter.changeLevel_eq_cast_of_dvd χ h a, ZMod.unitsMap_def]

/-- Under the hypothesis of Theorem 4.5.10 (`n ∣ N^∞` or `(n, M) = 1`), the characters `χ` modulo
`N` and `χ` read modulo `M` agree at every divisor of `n`. -/
lemma changeLevel_apply_of_dvd {N M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M)
    (χ : DirichletCharacter ℂ N) {n : ℕ}
    (hn : (∀ p : ℕ, p.Prime → p ∣ n → p ∣ N) ∨ n.Coprime M) {d : ℕ} (hd : d ∣ n) :
    DirichletCharacter.changeLevel h χ d = χ d := by
  by_cases hdM : d.Coprime M
  · have hc : IsCoprime (d : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.mpr hdM
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ h hc
    exact_mod_cast this
  · have hdN : ¬ d.Coprime N := by
      rcases hn with hn | hn
      · intro hdN
        apply hdM
        refine Nat.coprime_of_dvd fun p hp hpd _ ↦ ?_
        exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hdN hpd (hn p hp (hpd.trans hd)))
      · exact absurd (hn.coprime_dvd_left hd) hdM
    have h1 : ¬ IsUnit (d : ZMod M) := fun hu ↦ hdM ((ZMod.isUnit_iff_coprime d M).mp hu)
    have h2 : ¬ IsUnit (d : ZMod N) := fun hu ↦ hdN ((ZMod.isUnit_iff_coprime d N).mp hu)
    rw [MulChar.map_nonunit _ h1, MulChar.map_nonunit _ h2]

/-! ### The natural embedding `𝒢_k(N, χ) ⊂ 𝒢_k(M, χ)` -/

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- Miyake's natural embedding `𝒢_k(N, χ) ⊂ 𝒢_k(M, χ)` for `N ∣ M` (p. 143): the same function,
read as a modular form on `Γ₁(M)` with the character `χ` modulo `M`. -/
def embedMod (k : ℤ) (χ : DirichletCharacter ℂ N) (h : N ∣ M) :
    modSpace k χ →ₗ[ℂ] modSpace (N := M) k (DirichletCharacter.changeLevel h χ) where
  toFun f := ⟨_root_.ModularForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd h) f.1, by
    change _ ∈ TauCeti.modFormCharSpace k _
    rw [toUnitHom_changeLevel]
    exact TauCeti.ModularForm.restrict_mem_modFormCharSpace χ.toUnitHom h f.2⟩
  map_add' f g := by ext τ; rfl
  map_smul' c f := by ext τ; rfl

/-- Miyake's natural embedding `𝒮_k(N, χ) ⊂ 𝒮_k(M, χ)` for `N ∣ M`. -/
def embed (k : ℤ) (χ : DirichletCharacter ℂ N) (h : N ∣ M) :
    cuspSpace k χ →ₗ[ℂ] cuspSpace (N := M) k (DirichletCharacter.changeLevel h χ) where
  toFun f := ⟨_root_.CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd h) f.1, by
    change _ ∈ TauCeti.cuspFormCharSpace k _
    rw [toUnitHom_changeLevel]
    exact TauCeti.CuspForm.restrict_mem_cuspFormCharSpace χ.toUnitHom h f.2⟩
  map_add' f g := by ext τ; rfl
  map_smul' c f := by ext τ; rfl

@[simp] lemma embedMod_apply_apply (k : ℤ) (χ : DirichletCharacter ℂ N) (h : N ∣ M)
    (f : modSpace k χ) (τ : ℍ) : (embedMod k χ h f).1 τ = f.1 τ :=
  rfl

@[simp] lemma embed_apply_apply (k : ℤ) (χ : DirichletCharacter ℂ N) (h : N ∣ M)
    (f : cuspSpace k χ) (τ : ℍ) :
    (embed k χ h f).1 τ = f.1 τ :=
  rfl

/-- The embedding does not change the `q`-expansion. -/
lemma coeffMod_embedMod {k : ℤ} {χ : DirichletCharacter ℂ N} (h : N ∣ M) (f : modSpace k χ)
    (n : ℕ) : coeffMod (embedMod k χ h f) n = coeffMod f n := by
  rfl

/-- The embedding does not change the `q`-expansion. -/
lemma coeff_embed {k : ℤ} {χ : DirichletCharacter ℂ N} (h : N ∣ M) (f : cuspSpace k χ)
    (n : ℕ) : coeff (embed k χ h f) n = coeff f n := by
  rfl

/-! ### Theorem 4.5.10 -/

/-- **Miyake, Theorem 4.5.10** (cusp forms, `T(n)`): let `M` be a multiple of `N` and `n` a
positive integer with `n ∣ N^∞` (every prime factor of `n` divides `N`) or `(n, M) = 1`. Then the
natural embedding `𝒮_k(N, χ) → 𝒮_k(M, χ)` commutes with `T(n)`. -/
@[kb "miyake1989" "Theorem 4.5.10, p. 143 (T(n), cusp forms)"]
theorem heckeT_embed (k : ℤ) (χ : DirichletCharacter ℂ N) (h : N ∣ M) {n : ℕ} (hn0 : n ≠ 0)
    (hn : (∀ p : ℕ, p.Prime → p ∣ n → p ∣ N) ∨ n.Coprime M) (f : cuspSpace k χ) :
    heckeT k (DirichletCharacter.changeLevel h χ) n (embed k χ h f) =
      embed k χ h (heckeT k χ n f) := by
  refine ext_of_coeff fun m ↦ ?_
  rw [coeff_heckeT k _ hn0, coeff_embed, coeff_heckeT k χ hn0]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [coeff_embed, changeLevel_apply_of_dvd h χ hn
    ((Nat.dvd_of_mem_divisors hd).trans (Nat.gcd_dvd_left n m))]

/-- A constant modular form on `Γ₁(N)` of nonzero weight vanishes. -/
lemma const_eq_zero_of_wt {k : ℤ} (hk : k ≠ 0)
    (h : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (c : ℂ) (hc : ∀ τ, h τ = c) : c = 0 := by
  let γ : SL(2, ℤ) := ⟨!![1, 0; (N : ℤ), 1], by simp [Matrix.det_fin_two]⟩
  have hγ : γ ∈ Gamma1 N := by
    rw [Gamma1_mem]
    simp [γ]
  have hmem : mapGL ℝ γ ∈ (Gamma1 N).map (mapGL ℝ) := Subgroup.mem_map_of_mem _ hγ
  have h0 := SlashInvariantForm.slash_action_eqn' h hmem UpperHalfPlane.I
  rw [hc, hc] at h0
  by_contra hc0
  have h1 : ((mapGL ℝ γ) 1 0 * (UpperHalfPlane.I : ℂ) + (mapGL ℝ γ) 1 1) ^ k = 1 := by
    have h2 : c * 1 = c * ((mapGL ℝ γ) 1 0 * (UpperHalfPlane.I : ℂ) + (mapGL ℝ γ) 1 1) ^ k := by
      rw [mul_one, mul_comm]; exact h0
    exact (mul_left_cancel₀ hc0 h2).symm
  have h3 : ((mapGL ℝ γ) 1 0 * (UpperHalfPlane.I : ℂ) + (mapGL ℝ γ) 1 1) = (N : ℂ) * Complex.I + 1 := by
    have e : ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; (N : ℝ), 1] := by
      rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
      ext i j
      change (((!![1, 0; (N : ℤ), 1] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℝ) = _
      fin_cases i <;> fin_cases j <;> simp
    simp [e]
  rw [h3] at h1
  have h4 := congrArg norm h1
  rw [norm_zpow, norm_one] at h4
  have h5 : 1 < ‖(N : ℂ) * Complex.I + 1‖ := by
    have hN : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
    have : ‖(N : ℂ) * Complex.I + 1‖ ^ 2 = (N : ℝ) ^ 2 + 1 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp
      ring
    nlinarith [norm_nonneg ((N : ℂ) * Complex.I + 1)]
  exact hk ((zpow_eq_one_iff_right₀ (norm_nonneg _) h5.ne').mp h4)

/-- For nonzero weight, an element of `𝒢_k(N, χ)` is determined by its coefficients at the
indices `n ≥ 1`. -/
lemma ext_of_coeffMod {k : ℤ} (hk : k ≠ 0) {χ : DirichletCharacter ℂ N} {f g : modSpace k χ}
    (h : ∀ n, n ≠ 0 → coeffMod f n = coeffMod g n) : f = g := by
  have hΓ := TauCeti.one_mem_strictPeriods_Gamma1_map N
  have hs : ∀ (u : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (τ : ℍ),
      HasSum (fun m : ℕ ↦ (qExpansion 1 u).coeff m • Function.Periodic.qParam 1 τ ^ m)
        (u τ) := fun u τ ↦
    hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex u hΓ)
      (ModularFormClass.holo u) (ModularFormClass.bdd_at_infty u) τ
  have key : ∀ τ : ℍ, f.1 τ - g.1 τ = coeffMod f 0 - coeffMod g 0 := by
    intro τ
    have h1 := (hs f.1 τ).sub (hs g.1 τ)
    have h2 : HasSum (fun m : ℕ ↦ (qExpansion 1 f.1).coeff m • Function.Periodic.qParam 1 τ ^ m -
        (qExpansion 1 g.1).coeff m • Function.Periodic.qParam 1 τ ^ m)
        (coeffMod f 0 - coeffMod g 0) := by
      have := hasSum_ite_eq (0 : ℕ) (coeffMod f 0 - coeffMod g 0)
      convert this using 1
      ext m
      by_cases hm : m = 0
      · subst hm; simp [coeffMod]
      · simp only [hm, if_false, ← sub_smul, smul_eq_mul]
        have := h m hm
        simp only [coeffMod] at this
        rw [this]; simp
    exact h1.unique h2
  have hz := const_eq_zero_of_wt hk (f.1 - g.1) _ (fun τ ↦ key τ)
  refine Subtype.ext (DFunLike.ext _ _ fun τ ↦ ?_)
  have := key τ
  rw [hz] at this
  exact sub_eq_zero.mp this

/-- **Miyake, Theorem 4.5.10** (modular forms, `T(n)`), for weight `k ≠ 0` (LE-MF-0199): the
natural embedding `𝒢_k(N, χ) → 𝒢_k(M, χ)` commutes with `T(n)` when `n ∣ N^∞` or `(n, M) = 1`. -/
@[kb "miyake1989" "Theorem 4.5.10, p. 143 (T(n), modular forms, k ≠ 0)"]
theorem heckeTMod_embedMod {k : ℤ} (hk : k ≠ 0) (χ : DirichletCharacter ℂ N) (h : N ∣ M)
    {n : ℕ} (hn0 : n ≠ 0) (hn : (∀ p : ℕ, p.Prime → p ∣ n → p ∣ N) ∨ n.Coprime M)
    (f : modSpace k χ) :
    heckeTMod k (DirichletCharacter.changeLevel h χ) n (embedMod k χ h f) =
      embedMod k χ h (heckeTMod k χ n f) := by
  refine ext_of_coeffMod hk fun m hm ↦ ?_
  rw [coeffMod_heckeTMod k _ hn0 _ hm, coeffMod_embedMod, coeffMod_heckeTMod k χ hn0 f hm]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [coeffMod_embedMod, changeLevel_apply_of_dvd h χ hn
    ((Nat.dvd_of_mem_divisors hd).trans (Nat.gcd_dvd_left n m))]

/-! ### Lemma 4.6.1: `f(lz)` -/

/-- Miyake's `f ↦ f(lz)` from `𝒢_k(N, χ)` to `𝒢_k(lN, χ)` (Lemma 4.6.1, (4.6.2)), through Tau
Ceti's level-raising operator `V_l`. -/
def raiseMod (k : ℤ) (χ : DirichletCharacter ℂ N) (l : ℕ) [NeZero l] :
    modSpace k χ →ₗ[ℂ] modSpace (N := l * N) k
      (DirichletCharacter.changeLevel (Dvd.intro_left l rfl) χ) where
  toFun f := ⟨TauCeti.ModularForm.levelRaise l (TauCeti.Gamma1_map_le_conjAct_scaleGL N l) f.1, by
    change _ ∈ TauCeti.modFormCharSpace k _
    rw [toUnitHom_changeLevel]
    exact TauCeti.ModularForm.levelRaise_mem_modFormCharSpace N l χ.toUnitHom f.2⟩
  map_add' f g := by ext τ; simp
  map_smul' c f := by ext τ; simp

/-- Miyake's `f ↦ f(lz)` from `𝒮_k(N, χ)` to `𝒮_k(lN, χ)`. -/
def raise (k : ℤ) (χ : DirichletCharacter ℂ N) (l : ℕ) [NeZero l] :
    cuspSpace k χ →ₗ[ℂ] cuspSpace (N := l * N) k
      (DirichletCharacter.changeLevel (Dvd.intro_left l rfl) χ) where
  toFun f := ⟨TauCeti.CuspForm.levelRaise l (TauCeti.Gamma1_map_le_conjAct_scaleGL N l) f.1, by
    change _ ∈ TauCeti.cuspFormCharSpace k _
    rw [toUnitHom_changeLevel]
    exact TauCeti.CuspForm.levelRaise_mem_cuspFormCharSpace N l χ.toUnitHom f.2⟩
  map_add' f g := by ext τ; simp
  map_smul' c f := by ext τ; simp

/-- **Miyake, Lemma 4.6.1** (modular forms): if `f ∈ 𝒢_k(N, χ)` and `l` is a positive integer,
then `z ↦ f(lz)` lies in `𝒢_k(lN, χ)`. -/
@[kb "miyake1989" "Lemma 4.6.1, p. 153 (modular forms)"]
theorem exists_modSpace_apply_eq (k : ℤ) (χ : DirichletCharacter ℂ N) (l : ℕ) [NeZero l]
    (f : modSpace k χ) :
    ∃ g : modSpace (N := l * N) k (DirichletCharacter.changeLevel (Dvd.intro_left l rfl) χ),
      ∀ τ : ℍ, g.1 τ =
        f.1 ⟨(l : ℂ) * τ, by
          simpa using mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne l))) τ.im_pos⟩ := by
  refine ⟨raiseMod k χ l f, fun τ ↦ ?_⟩
  change TauCeti.ModularForm.levelRaise l (TauCeti.Gamma1_map_le_conjAct_scaleGL N l) f.1 τ = _
  rw [TauCeti.ModularForm.levelRaise_apply]
  congr 1
  ext
  exact TauCeti.coe_scaleGL_smul τ

/-- **Miyake, Lemma 4.6.1** (cusp forms): if `f ∈ 𝒮_k(N, χ)`, then `z ↦ f(lz)` lies in
`𝒮_k(lN, χ)`. -/
@[kb "miyake1989" "Lemma 4.6.1, p. 153 (cusp forms)"]
theorem exists_cuspSpace_apply_eq (k : ℤ) (χ : DirichletCharacter ℂ N) (l : ℕ) [NeZero l]
    (f : cuspSpace k χ) :
    ∃ g : cuspSpace (N := l * N) k (DirichletCharacter.changeLevel (Dvd.intro_left l rfl) χ),
      ∀ τ : ℍ, g.1 τ =
        f.1 ⟨(l : ℂ) * τ, by
          simpa using mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne l))) τ.im_pos⟩ := by
  refine ⟨raise k χ l f, fun τ ↦ ?_⟩
  change TauCeti.CuspForm.levelRaise l (TauCeti.Gamma1_map_le_conjAct_scaleGL N l) f.1 τ = _
  rw [TauCeti.CuspForm.levelRaise_apply]
  congr 1
  ext
  exact TauCeti.coe_scaleGL_smul τ

/-- The coefficients of `f(lz)`: `b(m) = a(m/l)` if `l ∣ m`, and `0` otherwise. -/
lemma coeff_raise {k : ℤ} {χ : DirichletCharacter ℂ N} (l : ℕ) [NeZero l] (f : cuspSpace k χ)
    (m : ℕ) : coeff (raise k χ l f) m = if l ∣ m then coeff f (m / l) else 0 :=
  TauCeti.CuspForm.qExpansion_levelRaise_coeff_Gamma1 N f.1 m

/-- The coefficients of `f(lz)` on `𝒢_k`. -/
lemma coeffMod_raiseMod {k : ℤ} {χ : DirichletCharacter ℂ N} (l : ℕ) [NeZero l]
    (f : modSpace k χ) (m : ℕ) :
    coeffMod (raiseMod k χ l f) m = if l ∣ m then coeffMod f (m / l) else 0 :=
  TauCeti.ModularForm.qExpansion_levelRaise_coeff_Gamma1 N f.1 m

/-! ### Lemma 4.6.2 -/

/-- **Miyake, Lemma 4.6.2** (cusp forms): for a positive integer `l` and `(n, lN) = 1`, the map
`f(z) ↦ f(lz)` from `𝒮_k(N, χ)` to `𝒮_k(lN, χ)` commutes with `T(n)`. (Miyake's vertical arrow
is `f ↦ f ∣_k δ_l = l^{k/2} f(lz)`, a constant multiple.) -/
@[kb "miyake1989" "Lemma 4.6.2, p. 154 (cusp forms)"]
theorem heckeT_raise (k : ℤ) (χ : DirichletCharacter ℂ N) (l : ℕ) [NeZero l] {n : ℕ}
    (hn0 : n ≠ 0) (hn : n.Coprime (l * N)) (f : cuspSpace k χ) :
    heckeT k _ n (raise k χ l f) = raise k χ l (heckeT k χ n f) := by
  have hnl : n.Coprime l := hn.coprime_dvd_right (Dvd.intro _ rfl)
  have hlpos : 0 < l := Nat.pos_of_ne_zero (NeZero.ne l)
  refine ext_of_coeff fun m ↦ ?_
  rw [coeff_heckeT k _ hn0, coeff_raise]
  by_cases hl : l ∣ m
  · rw [if_pos hl]
    obtain ⟨j, rfl⟩ := hl
    rw [Nat.mul_div_cancel_left _ hlpos, coeff_heckeT k χ hn0,
      Nat.Coprime.gcd_mul_left_cancel_right j hnl.symm]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    have hdg := Nat.dvd_of_mem_divisors hd
    have hdn : d ∣ n := hdg.trans (Nat.gcd_dvd_left n j)
    have hdj : d ∣ j := hdg.trans (Nat.gcd_dvd_right n j)
    have hd2 : d ^ 2 ∣ n * j := by rw [pow_two]; exact mul_dvd_mul hdn hdj
    have e : n * (l * j) / d ^ 2 = l * (n * j / d ^ 2) := by
      rw [show n * (l * j) = l * (n * j) by ring, Nat.mul_div_assoc _ hd2]
    rw [coeff_raise, e, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hlpos,
      changeLevel_apply_of_dvd (Dvd.intro_left l rfl) χ (Or.inr hn) hdn]
  · rw [if_neg hl]
    refine Finset.sum_eq_zero fun d hd ↦ ?_
    have hdg := Nat.dvd_of_mem_divisors hd
    have hdn : d ∣ n := hdg.trans (Nat.gcd_dvd_left n m)
    have hdm : d ∣ m := hdg.trans (Nat.gcd_dvd_right n m)
    have hd2 : d ^ 2 ∣ n * m := by rw [pow_two]; exact mul_dvd_mul hdn hdm
    rw [coeff_raise, if_neg, mul_zero]
    intro h1
    exact hl (hnl.symm.dvd_of_dvd_mul_left ((h1.trans (Nat.div_dvd_of_dvd hd2))))

/-- **Miyake, Lemma 4.6.2** (modular forms, weight `k ≠ 0`, LE-MF-0199). -/
@[kb "miyake1989" "Lemma 4.6.2, p. 154 (modular forms, k ≠ 0)"]
theorem heckeTMod_raiseMod {k : ℤ} (hk : k ≠ 0) (χ : DirichletCharacter ℂ N) (l : ℕ) [NeZero l]
    {n : ℕ} (hn0 : n ≠ 0) (hn : n.Coprime (l * N)) (f : modSpace k χ) :
    heckeTMod k _ n (raiseMod k χ l f) = raiseMod k χ l (heckeTMod k χ n f) := by
  have hnl : n.Coprime l := hn.coprime_dvd_right (Dvd.intro _ rfl)
  have hlpos : 0 < l := Nat.pos_of_ne_zero (NeZero.ne l)
  refine ext_of_coeffMod hk fun m hm ↦ ?_
  rw [coeffMod_heckeTMod k _ hn0 _ hm, coeffMod_raiseMod]
  by_cases hl : l ∣ m
  · rw [if_pos hl]
    obtain ⟨j, rfl⟩ := hl
    have hj : j ≠ 0 := fun h0 ↦ hm (by simp [h0])
    rw [Nat.mul_div_cancel_left _ hlpos, coeffMod_heckeTMod k χ hn0 f hj,
      Nat.Coprime.gcd_mul_left_cancel_right j hnl.symm]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    have hdg := Nat.dvd_of_mem_divisors hd
    have hdn : d ∣ n := hdg.trans (Nat.gcd_dvd_left n j)
    have hdj : d ∣ j := hdg.trans (Nat.gcd_dvd_right n j)
    have hd2 : d ^ 2 ∣ n * j := by rw [pow_two]; exact mul_dvd_mul hdn hdj
    have e : n * (l * j) / d ^ 2 = l * (n * j / d ^ 2) := by
      rw [show n * (l * j) = l * (n * j) by ring, Nat.mul_div_assoc _ hd2]
    rw [coeffMod_raiseMod, e, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hlpos,
      changeLevel_apply_of_dvd (Dvd.intro_left l rfl) χ (Or.inr hn) hdn]
  · rw [if_neg hl]
    refine Finset.sum_eq_zero fun d hd ↦ ?_
    have hdg := Nat.dvd_of_mem_divisors hd
    have hdn : d ∣ n := hdg.trans (Nat.gcd_dvd_left n m)
    have hdm : d ∣ m := hdg.trans (Nat.gcd_dvd_right n m)
    have hd2 : d ^ 2 ∣ n * m := by rw [pow_two]; exact mul_dvd_mul hdn hdm
    rw [coeffMod_raiseMod, if_neg, mul_zero]
    intro h1
    exact hl (hnl.symm.dvd_of_dvd_mul_left ((h1.trans (Nat.div_dvd_of_dvd hd2))))

end ModularFormsKB.Miyake.Wave6
