import ModularFormsKB.Miyake.HeckeTrick.FourierTerms

/-!
# Miyake §7.2: poles of $E_k(z,s;\chi,\psi)$ (Corollary 7.2.10)

Miyake, *Modular Forms*, §7.2, p. 285. "Holomorphic on $U$" for the continuation of $E_k(z,s;\chi,\psi)$ is stated
as: some function holomorphic on $U$ agrees with the series (7.2.1) on its half-plane of convergence
$k + 2\operatorname{Re}s > 2$ (when $U$ meets that half-plane and $U \cup \{k+2\operatorname{Re}s>2\}$ is connected,
this function is the continuation of Theorem 7.2.9, by the identity theorem). In (1) the continuation
`eisensteinCharSCont` itself is entire.
-/

open MeasureTheory Set Filter Topology Complex
open scoped UpperHalfPlane
open scoped Real

noncomputable section

namespace ModularFormsKB.Miyake.HeckeTrick

open ModularFormsKB.Miyake.Wave2B

variable {L M : ℕ}

lemma differentiable_cpow_im (z : ℍ) (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    Differentiable ℂ (fun s ↦ (z.im : ℂ) ^ (f s)) :=
  hf.const_cpow (Or.inl (by exact_mod_cast z.im_pos.ne'))

/-- The two Fourier series parts of `eisensteinCharSCont`. -/
def heckeRest (k : ℤ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (z : ℍ) (s : ℂ) : ℂ :=
  heckeA k ψ s * (z.im : ℂ) ^ (-s) * ∑' n : ℕ+, heckeTermA k χ ψ z s n +
      heckeB k ψ s * (z.im : ℂ) ^ (-k - s) * ∑' n : ℕ+, heckeTermB k χ ψ z s n

/-- The two Fourier series parts of `eisensteinCharSCont` are entire. -/
lemma differentiable_heckeRest (k : ℤ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (z : ℍ) :
    Differentiable ℂ (heckeRest k χ ψ z) := by
  unfold heckeRest
  have hA := ((differentiable_heckeA k ψ).mul
    (differentiable_cpow_im z (fun s ↦ -s) differentiable_neg)).mul
    (differentiable_tsum_heckeTermA k χ ψ z)
  have hB := ((differentiable_heckeB k ψ).mul
    (differentiable_cpow_im z (fun s ↦ -k - s) ((differentiable_const _).sub differentiable_id))).mul
    (differentiable_tsum_heckeTermB k χ ψ z)
  exact hA.add hB

lemma eisensteinCharSCont_eq (k : ℤ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (z : ℍ) (s : ℂ) :
    eisensteinCharSCont k χ ψ z s = heckeC k L ψ s + heckeD k χ ψ s * (z.im : ℂ) ^ (1 - k - 2 * s) +
      heckeRest k χ ψ z s := by
  unfold eisensteinCharSCont heckeRest; ring

lemma differentiableAt_gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gamma s := by
  refine Complex.differentiableAt_Gamma s fun m h ↦ ?_
  rw [h] at hs
  simp at hs
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- `heckeC` is differentiable except possibly at `2s + k = 1` when `L = 1`, `ψ = 1`. -/
lemma differentiableAt_heckeC (k : ℤ) (L : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) {s : ℂ}
    (h : 2 * s + k ≠ 1 ∨ ψ ≠ 1 ∨ L ≠ 1) : DifferentiableAt ℂ (heckeC k L ψ) s := by
  unfold heckeC
  by_cases hL : L = 1
  · simp only [hL, ite_true]
    have h' : 2 * s + k ≠ 1 ∨ ψ ≠ 1 := by tauto
    exact (differentiableAt_const _).mul
      ((DirichletCharacter.differentiableAt_LFunction ψ _ h').comp s (by fun_prop))
  · simp [hL]

lemma diffAt_comp' {f w : ℂ → ℂ} {s : ℂ} (hf : DifferentiableAt ℂ f (w s))
    (hw : DifferentiableAt ℂ w s) : DifferentiableAt ℂ (fun s ↦ f (w s)) s := hf.comp s hw

/-- Differentiability of `heckeD` away from the poles of the Gamma factors and the `L`-function. -/
lemma differentiableAt_heckeD (k : ℤ) [NeZero L] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) {s : ℂ} (h1 : 0 < ((2 * s + k - 1) / 2).re)
    (h2 : 0 < ((2 * s + k) / 2).re) (h3 : 2 * s + k - 1 ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (heckeD k χ ψ) s := by
  unfold heckeD
  by_cases hψ : ψ = 1
  · simp only [hψ, ite_true]
    have g1 : DifferentiableAt ℂ (fun s : ℂ ↦ Gamma ((2 * s + k - 1) / 2)) s :=
      diffAt_comp' (w := fun s ↦ (2 * s + k - 1) / 2) (differentiableAt_gamma_of_re_pos h1) (by fun_prop)
    have g2 : DifferentiableAt ℂ (fun s : ℂ ↦ Gamma ((2 * s + k) / 2)) s :=
      diffAt_comp' (w := fun s ↦ (2 * s + k) / 2) (differentiableAt_gamma_of_re_pos h2) (by fun_prop)
    have g3 : DifferentiableAt ℂ (fun s : ℂ ↦ (Gamma s)⁻¹) s :=
      Complex.differentiable_one_div_Gamma s
    have g4 : DifferentiableAt ℂ (fun s : ℂ ↦ (Gamma (s + k))⁻¹) s :=
      (Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const (k : ℂ))) s
    have g5 : DifferentiableAt ℂ (fun s : ℂ ↦ DirichletCharacter.LFunction χ (2 * s + k - 1)) s :=
      diffAt_comp' (w := fun s ↦ 2 * s + k - 1)
        (DirichletCharacter.differentiableAt_LFunction χ (2 * s + k - 1) h3) (by fun_prop)
    exact ((((((differentiableAt_const _).mul g3).mul g4).mul g1).mul g2).mul g5)
  · simp [hψ]

/-- **Miyake, Corollary 7.2.10 (1).** If $\psi$ is non-trivial, the continuation of $E_k(z,s;\chi,\psi)$ is an
entire function of $s$. -/
@[kb "miyake1989" "Corollary 7.2.10 (1), p. 285"]
theorem differentiable_eisensteinCharSCont (k : ℤ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L)
    {ψ : DirichletCharacter ℂ M} (hψ : ψ ≠ 1) (z : ℍ) :
    Differentiable ℂ (eisensteinCharSCont k χ ψ z) := by
  have hD : heckeD k χ ψ = fun _ ↦ 0 := by
    funext s; simp [heckeD, hψ]
  have hC : Differentiable ℂ (heckeC k L ψ) := fun s ↦
    differentiableAt_heckeC k L ψ (Or.inr (Or.inl hψ))
  have : eisensteinCharSCont k χ ψ z = fun s ↦ heckeC k L ψ s + 0 + heckeRest k χ ψ z s := by
    funext s
    rw [eisensteinCharSCont_eq, hD]; simp
  rw [this]
  exact (hC.add (differentiable_const _)).add (differentiable_heckeRest k χ ψ z)

lemma heckeD_one_eq (k : ℤ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L) (s : ℂ) :
    heckeD k χ (1 : DirichletCharacter ℂ M) s =
      (2 * (Real.sqrt π : ℂ) * I ^ (-k) * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹))) *
        (Gamma (s + k))⁻¹ * Gamma ((2 * s + k - 1) / 2) * Gamma ((2 * s + k) / 2) *
        ((Gamma s)⁻¹ * DirichletCharacter.LFunction χ (2 * s + k - 1)) := by
  unfold heckeD
  rw [if_pos rfl]
  ring

lemma holo_aux {k : ℤ} (hk : 1 ≤ k) [NeZero L] [NeZero M]
    (χ : DirichletCharacter ℂ L) (hpar : χ (-1) * (1 : DirichletCharacter ℂ M) (-1) = (-1) ^ k)
    (z : ℍ) (G : ℂ → ℂ) (hG : DifferentiableOn ℂ G {s | (1 - k : ℝ) / 2 < s.re})
    (hGeq : ∀ s : ℂ, 2 < (k : ℝ) + 2 * s.re →
      G s = (Gamma s)⁻¹ * DirichletCharacter.LFunction χ (2 * s + k - 1)) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {s | (1 - k : ℝ) / 2 < s.re} ∧
      ∀ s : ℂ, 2 < (k : ℝ) + 2 * s.re →
        F s = eisensteinCharS k s χ (1 : DirichletCharacter ℂ M) z := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨fun s ↦ heckeC k L (1 : DirichletCharacter ℂ M) s +
    ((2 * (Real.sqrt π : ℂ) * I ^ (-k) * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹))) *
        (Gamma (s + k))⁻¹ * Gamma ((2 * s + k - 1) / 2) * Gamma ((2 * s + k) / 2) * G s) *
      (z.im : ℂ) ^ (1 - k - 2 * s) + heckeRest k χ (1 : DirichletCharacter ℂ M) z s, ?_, ?_⟩
  · intro s hs
    have hs' : (1 - (k : ℝ)) / 2 < s.re := hs
    have hre1 : 0 < ((2 * s + k - 1) / 2).re := by
      simp [Complex.div_ofNat_re]; linarith
    have hre2 : 0 < ((2 * s + k) / 2).re := by
      simp [Complex.div_ofNat_re]; linarith
    have hopen : IsOpen {s : ℂ | (1 - k : ℝ) / 2 < s.re} :=
      isOpen_lt continuous_const continuous_re
    have g1 : DifferentiableAt ℂ (fun s : ℂ ↦ Gamma ((2 * s + k - 1) / 2)) s :=
      diffAt_comp' (w := fun s ↦ (2 * s + k - 1) / 2) (differentiableAt_gamma_of_re_pos hre1) (by fun_prop)
    have g2 : DifferentiableAt ℂ (fun s : ℂ ↦ Gamma ((2 * s + k) / 2)) s :=
      diffAt_comp' (w := fun s ↦ (2 * s + k) / 2) (differentiableAt_gamma_of_re_pos hre2) (by fun_prop)
    have g4 : DifferentiableAt ℂ (fun s : ℂ ↦ (Gamma (s + k))⁻¹) s :=
      (Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const (k : ℂ))) s
    have g6 : DifferentiableAt ℂ G s := hG.differentiableAt (hopen.mem_nhds hs)
    have g7 : DifferentiableAt ℂ (fun s : ℂ ↦ (z.im : ℂ) ^ (1 - (k : ℂ) - 2 * s)) s :=
      (differentiable_cpow_im z (fun s ↦ 1 - (k : ℂ) - 2 * s) (by fun_prop)) s
    have gC : DifferentiableAt ℂ (heckeC k L (1 : DirichletCharacter ℂ M)) s := by
      refine differentiableAt_heckeC k L _ (Or.inl fun h ↦ ?_)
      have := congrArg Complex.re h
      simp at this
      linarith
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (gC.add ((((((differentiableAt_const _).mul g4).mul g1).mul g2).mul g6).mul g7)).add
      (differentiable_heckeRest k χ (1 : DirichletCharacter ℂ M) z s)
  · intro s hs
    rw [eisensteinCharS_eq_cont k χ 1 hpar z hs, eisensteinCharSCont_eq, heckeD_one_eq]
    beta_reduce
    rw [hGeq s hs]

/-- **Miyake, Corollary 7.2.10 (2).** If $\psi$ is trivial and $k \ge 1$ (and $\chi(-1)\psi(-1) = (-1)^k$),
$E_k(z,s;\chi,\psi)$ is holomorphic for $\operatorname{Re}s > (1-k)/2$. -/
@[kb "miyake1989" "Corollary 7.2.10 (2), p. 285"]
theorem eisensteinCharS_holomorphic_of_trivial {k : ℤ} (hk : 1 ≤ k) [NeZero L] [NeZero M]
    (χ : DirichletCharacter ℂ L) (hpar : χ (-1) * (1 : DirichletCharacter ℂ M) (-1) = (-1) ^ k)
    (z : ℍ) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {s | (1 - k : ℝ) / 2 < s.re} ∧
      ∀ s : ℂ, 2 < (k : ℝ) + 2 * s.re →
        F s = eisensteinCharS k s χ (1 : DirichletCharacter ℂ M) z := by
  by_cases hχ : χ = 1
  · subst hχ
    have h1 : ∀ {N : ℕ} [NeZero N], (1 : DirichletCharacter ℂ N) (-1) = 1 := fun {N} _ ↦
      MulChar.one_apply isUnit_one.neg
    have hpar0 := hpar
    rw [h1, h1, one_mul] at hpar
    have hev : Even k := by
      by_contra hne
      have hodd : Odd k := Int.not_even_iff_odd.mp hne
      rw [hodd.neg_one_zpow] at hpar
      norm_num at hpar
    obtain ⟨m, hm⟩ := hev
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) + 1 := ⟨(m - 1).toNat, by omega⟩
    have hkc : (k : ℂ) = 2 * ((n : ℂ) + 1) := by
      have : k = 2 * ((n : ℤ) + 1) := by omega
      rw [this]; push_cast; ring
    set s₀ : ℂ := 1 - (k : ℂ) / 2 with hs₀
    have hs₀n : s₀ = -(n : ℂ) := by rw [hs₀, hkc]; ring
    set f : ℂ → ℂ := fun s ↦ (Gamma s)⁻¹ with hf
    have hf0 : f s₀ = 0 := by
      simp only [hf, hs₀n, Complex.Gamma_neg_nat_eq_zero, inv_zero]
    refine holo_aux hk _ hpar0 z
      (fun s ↦ dslope f s₀ s * DirichletCharacter.LFunctionTrivChar₁ L (2 * s + k - 1) / 2) ?_ ?_
    · refine Differentiable.differentiableOn ?_
      have hd : Differentiable ℂ (dslope f s₀) := by
        have := (differentiableOn_dslope (f := f) (s := Set.univ) (c := s₀) Filter.univ_mem).mpr
          Complex.differentiable_one_div_Gamma.differentiableOn
        exact differentiableOn_univ.mp this
      have hL : Differentiable ℂ (fun s : ℂ ↦ DirichletCharacter.LFunctionTrivChar₁ L (2 * s + k - 1)) :=
        (DirichletCharacter.differentiable_LFunctionTrivChar₁ L).comp (by fun_prop)
      exact (hd.mul hL).div_const 2
    · intro s hs
      have hne : s ≠ s₀ := by
        rintro rfl
        have : (k : ℝ) + 2 * (1 - (k : ℂ) / 2).re = 2 := by simp; ring
        linarith
      have hw : (2 * s + k - 1 : ℂ) ≠ 1 := by
        intro h
        apply hne
        rw [hs₀]
        linear_combination h / 2
      have hsub : s - s₀ ≠ 0 := sub_ne_zero.2 hne
      have hup : DirichletCharacter.LFunctionTrivChar₁ L (2 * s + k - 1) =
          (2 * s + k - 1 - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ L) (2 * s + k - 1) := by
        simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hw,
          DirichletCharacter.LFunctionTrivChar]
      show dslope f s₀ s * _ / 2 = _
      rw [dslope_of_ne _ hne, slope_def_field, hf0, hup]
      have : (2 * s + k - 1 - 1 : ℂ) = 2 * (s - s₀) := by rw [hs₀]; ring
      rw [this]
      simp only [hf]
      field_simp
      ring
  · exact holo_aux hk χ hpar z (fun s ↦ (Gamma s)⁻¹ * DirichletCharacter.LFunction χ (2 * s + k - 1))
      (Differentiable.differentiableOn
        (Complex.differentiable_one_div_Gamma.mul
          ((DirichletCharacter.differentiable_LFunction hχ).comp (by fun_prop))))
      (fun _ _ ↦ rfl)

/-- **Miyake, Corollary 7.2.10 (2), $k = 1$.** If $\psi$ is trivial (and $\chi(-1)\psi(-1) = -1$),
$E_1(z,s;\chi,\psi)$ is holomorphic for $\operatorname{Re}s > -1/2$. -/
@[kb "miyake1989" "Corollary 7.2.10 (2), p. 285"]
theorem eisensteinCharS_one_holomorphic_of_trivial [NeZero L] [NeZero M]
    (χ : DirichletCharacter ℂ L) (hpar : χ (-1) * (1 : DirichletCharacter ℂ M) (-1) = -1) (z : ℍ) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {s | -1 / 2 < s.re} ∧
      ∀ s : ℂ, 2 < 1 + 2 * s.re → F s = eisensteinCharS 1 s χ (1 : DirichletCharacter ℂ M) z := by
  have h1 : ∀ {N : ℕ} [NeZero N], (1 : DirichletCharacter ℂ N) (-1) = 1 := fun {N} _ ↦
    MulChar.one_apply isUnit_one.neg
  have hL : L ≠ 1 := by
    rintro rfl
    have h2 : χ (-1) = 1 := by
      have : (-1 : ZMod 1) = 1 := Subsingleton.elim _ _
      rw [this, map_one]
    rw [h2, h1] at hpar
    norm_num at hpar
  have hpar' : χ (-1) * (1 : DirichletCharacter ℂ M) (-1) = (-1) ^ (1 : ℤ) := by
    rw [hpar]; norm_num
  refine ⟨fun s ↦ heckeC (1 : ℤ) L (1 : DirichletCharacter ℂ M) s +
    ((2 * (Real.sqrt π : ℂ) * I ^ (-(1 : ℤ)) * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹))) *
      (Gamma (s + ((1 : ℤ) : ℂ)))⁻¹ * Gamma ((2 * s + ((1 : ℤ) : ℂ)) / 2) *
      DirichletCharacter.LFunction χ (2 * s + ((1 : ℤ) : ℂ) - 1)) *
      (z.im : ℂ) ^ (1 - ((1 : ℤ) : ℂ) - 2 * s) + heckeRest 1 χ (1 : DirichletCharacter ℂ M) z s,
    ?_, ?_⟩
  · intro s hs
    have hs' : -1 / 2 < s.re := hs
    have hre2 : 0 < ((2 * s + ((1 : ℤ) : ℂ)) / 2).re := by
      simp [Complex.div_ofNat_re]; linarith
    have hχ : χ ≠ 1 := by
      rintro rfl
      rw [h1, h1] at hpar
      norm_num at hpar
    have g2 : DifferentiableAt ℂ (fun s : ℂ ↦ Gamma ((2 * s + ((1 : ℤ) : ℂ)) / 2)) s :=
      diffAt_comp' (w := fun s ↦ (2 * s + ((1 : ℤ) : ℂ)) / 2)
        (differentiableAt_gamma_of_re_pos hre2) (by fun_prop)
    have g4 : DifferentiableAt ℂ (fun s : ℂ ↦ (Gamma (s + ((1 : ℤ) : ℂ)))⁻¹) s :=
      (Complex.differentiable_one_div_Gamma.comp
        (differentiable_id.add_const (((1 : ℤ)) : ℂ))) s
    have g5 : DifferentiableAt ℂ
        (fun s : ℂ ↦ DirichletCharacter.LFunction χ (2 * s + ((1 : ℤ) : ℂ) - 1)) s :=
      ((DirichletCharacter.differentiable_LFunction hχ).comp (by fun_prop :
        Differentiable ℂ (fun s : ℂ ↦ 2 * s + ((1 : ℤ) : ℂ) - 1))) s
    have g7 : DifferentiableAt ℂ (fun s : ℂ ↦ (z.im : ℂ) ^ (1 - ((1 : ℤ) : ℂ) - 2 * s)) s :=
      (differentiable_cpow_im z (fun s ↦ 1 - ((1 : ℤ) : ℂ) - 2 * s) (by fun_prop)) s
    have gC : DifferentiableAt ℂ (heckeC (1 : ℤ) L (1 : DirichletCharacter ℂ M)) s :=
      differentiableAt_heckeC _ L _ (Or.inr (Or.inr hL))
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (gC.add ((((((differentiableAt_const _).mul g4).mul g2).mul g5)).mul g7)).add
      (differentiable_heckeRest 1 χ (1 : DirichletCharacter ℂ M) z s)
  · intro s hs
    have hs2 : 2 < ((1 : ℤ) : ℝ) + 2 * s.re := by push_cast; exact hs
    have hre : 0 < s.re := by linarith
    have hG : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre
    have hGG : Gamma s * (Gamma s)⁻¹ = 1 := mul_inv_cancel₀ hG
    rw [eisensteinCharS_eq_cont 1 χ 1 hpar' z hs2, eisensteinCharSCont_eq, heckeD_one_eq]
    beta_reduce
    have ha : (2 * s + ((1 : ℤ) : ℂ) - 1) / 2 = s := by push_cast; ring
    rw [ha]
    linear_combination (-1 : ℂ) *
      (2 * (Real.sqrt π : ℂ) * I ^ (-(1 : ℤ)) * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹))) *
      (Gamma (s + ((1 : ℤ) : ℂ)))⁻¹ * Gamma ((2 * s + ((1 : ℤ) : ℂ)) / 2) *
      DirichletCharacter.LFunction χ (2 * s + ((1 : ℤ) : ℂ) - 1) *
      (z.im : ℂ) ^ (1 - ((1 : ℤ) : ℂ) - 2 * s) * hGG

lemma tendsto_sub_one_mul_zero {g : ℂ → ℂ} (hg : DifferentiableAt ℂ g 1) :
    Tendsto (fun s ↦ (s - 1) * g s) (𝓝[≠] 1) (𝓝 0) := by
  have h : ContinuousAt (fun s ↦ (s - 1) * g s) 1 :=
    (continuousAt_id.sub continuousAt_const).mul hg.continuousAt
  have := h.tendsto
  simp only [sub_self, zero_mul] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- **Miyake, Corollary 7.2.10 (3).** If $\chi$ and $\psi$ are both trivial and $k = 0$, then $E_0(z,s;\chi,\psi)$ is
holomorphic for $\operatorname{Re}s > 1$ and has a simple pole at $s = 1$ with residue
$\frac{\pi}{y}\prod_{p\mid L}(1-p^{-1})\prod_{p\mid M}(1-p^{-1})$: its continuation is holomorphic on
$\{\operatorname{Re}s > 1\}$ and on a punctured disc around $1$, and $(s-1)E_0(z,s)$ tends to the residue. -/
@[kb "miyake1989" "Corollary 7.2.10 (3), p. 285"]
theorem eisensteinCharS_zero_residue [NeZero L] [NeZero M] (z : ℍ) :
    ∃ F : ℂ → ℂ, ∃ ε > (0 : ℝ),
      DifferentiableOn ℂ F ({s | 1 < s.re} ∪ (Metric.ball 1 ε \ {1})) ∧
      (∀ s : ℂ, 1 < s.re →
        F s = eisensteinCharS 0 s (1 : DirichletCharacter ℂ L) (1 : DirichletCharacter ℂ M) z) ∧
      Tendsto (fun s ↦ (s - 1) * F s) (𝓝[≠] 1)
        (𝓝 (π / z.im * (∏ p ∈ L.primeFactors, (1 - (p : ℂ)⁻¹)) *
          ∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹))) := by
  have h1 : ∀ {N : ℕ} [NeZero N], (1 : DirichletCharacter ℂ N) (-1) = 1 := fun {N} _ ↦
    MulChar.one_apply isUnit_one.neg
  have hpar : (1 : DirichletCharacter ℂ L) (-1) * (1 : DirichletCharacter ℂ M) (-1) =
      (-1) ^ (0 : ℤ) := by
    rw [h1, h1]; norm_num
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun s ↦
      (2 * (Real.sqrt π : ℂ) * I ^ (-(0 : ℤ)) * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹))) *
        (Gamma (s + ((0 : ℤ) : ℂ)))⁻¹ * Gamma ((2 * s + ((0 : ℤ) : ℂ) - 1) / 2) *
        Gamma ((2 * s + ((0 : ℤ) : ℂ)) / 2) * (Gamma s)⁻¹ *
        (z.im : ℂ) ^ (1 - ((0 : ℤ) : ℂ) - 2 * s) := ⟨_, rfl⟩
  have hF : ∀ s, eisensteinCharSCont 0 (1 : DirichletCharacter ℂ L) (1 : DirichletCharacter ℂ M) z s =
      heckeC 0 L (1 : DirichletCharacter ℂ M) s +
        P s * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ L) (2 * s + ((0 : ℤ) : ℂ) - 1) +
        heckeRest 0 (1 : DirichletCharacter ℂ L) (1 : DirichletCharacter ℂ M) z s := by
    intro s
    rw [eisensteinCharSCont_eq, heckeD_one_eq]
    simp only [hP]
    ring
  have hdom : ∀ s ∈ ({s : ℂ | 1 < s.re} ∪ (Metric.ball (1 : ℂ) (1 / 4) \ {1})),
      3 / 4 < s.re ∧ s ≠ 1 := by
    intro s hs
    rcases hs with hs | ⟨hb, hne⟩
    · refine ⟨by simp at hs; linarith, ?_⟩
      rintro rfl
      simp at hs
    · refine ⟨?_, hne⟩
      have h2 : |(s - 1).re| ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
      rw [Metric.mem_ball, dist_eq_norm] at hb
      have h3 : |s.re - 1| < 1 / 4 := by simpa using lt_of_le_of_lt h2 hb
      linarith [(abs_lt.mp h3).1]
  have hR : Differentiable ℂ (heckeRest 0 (1 : DirichletCharacter ℂ L) (1 : DirichletCharacter ℂ M) z) :=
    differentiable_heckeRest 0 _ _ z
  have hcond1 : ∀ s : ℂ, 3 / 4 < s.re → 2 * s + ((0 : ℤ) : ℂ) ≠ 1 := by
    intro s hs h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hcond2 : ∀ s : ℂ, s ≠ 1 → 2 * s + ((0 : ℤ) : ℂ) - 1 ≠ 1 := by
    intro s hs h
    apply hs
    push_cast at h
    linear_combination h / 2
  have hre1 : ∀ s : ℂ, 3 / 4 < s.re → 0 < ((2 * s + ((0 : ℤ) : ℂ) - 1) / 2).re := by
    intro s hs
    simp [Complex.div_ofNat_re]; linarith
  have hre2 : ∀ s : ℂ, 3 / 4 < s.re → 0 < ((2 * s + ((0 : ℤ) : ℂ)) / 2).re := by
    intro s hs
    simp [Complex.div_ofNat_re]; linarith
  have hPd : ∀ s : ℂ, 3 / 4 < s.re → DifferentiableAt ℂ P s := by
    intro s hs
    have g1 : DifferentiableAt ℂ (fun s : ℂ ↦ Gamma ((2 * s + ((0 : ℤ) : ℂ) - 1) / 2)) s :=
      diffAt_comp' (w := fun s ↦ (2 * s + ((0 : ℤ) : ℂ) - 1) / 2)
        (differentiableAt_gamma_of_re_pos (hre1 s hs)) (by fun_prop)
    have g2 : DifferentiableAt ℂ (fun s : ℂ ↦ Gamma ((2 * s + ((0 : ℤ) : ℂ)) / 2)) s :=
      diffAt_comp' (w := fun s ↦ (2 * s + ((0 : ℤ) : ℂ)) / 2)
        (differentiableAt_gamma_of_re_pos (hre2 s hs)) (by fun_prop)
    have g3 : DifferentiableAt ℂ (fun s : ℂ ↦ (Gamma s)⁻¹) s :=
      Complex.differentiable_one_div_Gamma s
    have g4 : DifferentiableAt ℂ (fun s : ℂ ↦ (Gamma (s + ((0 : ℤ) : ℂ)))⁻¹) s :=
      (Complex.differentiable_one_div_Gamma.comp
        (differentiable_id.add_const (((0 : ℤ)) : ℂ))) s
    have g7 : DifferentiableAt ℂ (fun s : ℂ ↦ (z.im : ℂ) ^ (1 - ((0 : ℤ) : ℂ) - 2 * s)) s :=
      (differentiable_cpow_im z (fun s ↦ 1 - ((0 : ℤ) : ℂ) - 2 * s) (by fun_prop)) s
    rw [hP]
    exact (((((differentiableAt_const _).mul g4).mul g1).mul g2).mul g3).mul g7
  refine ⟨eisensteinCharSCont 0 (1 : DirichletCharacter ℂ L) (1 : DirichletCharacter ℂ M) z, 1 / 4,
    by norm_num, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨hre, hne⟩ := hdom s hs
    have gC := differentiableAt_heckeC (0 : ℤ) L (1 : DirichletCharacter ℂ M) (s := s)
      (Or.inl (hcond1 s hre))
    have gL : DifferentiableAt ℂ
        (fun s : ℂ ↦ DirichletCharacter.LFunction (1 : DirichletCharacter ℂ L)
          (2 * s + ((0 : ℤ) : ℂ) - 1)) s :=
      diffAt_comp' (w := fun s ↦ 2 * s + ((0 : ℤ) : ℂ) - 1)
        (DirichletCharacter.differentiableAt_LFunction _ _ (Or.inl (hcond2 s hne))) (by fun_prop)
    have hfun : eisensteinCharSCont 0 (1 : DirichletCharacter ℂ L) (1 : DirichletCharacter ℂ M) z =
        fun s ↦ heckeC 0 L (1 : DirichletCharacter ℂ M) s +
          P s * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ L)
            (2 * s + ((0 : ℤ) : ℂ) - 1) +
          heckeRest 0 (1 : DirichletCharacter ℂ L) (1 : DirichletCharacter ℂ M) z s :=
      funext hF
    rw [hfun]
    exact DifferentiableAt.differentiableWithinAt
      ((gC.add ((hPd s hre).mul gL)).add (hR s))
  · intro s hs
    exact (eisensteinCharS_eq_cont 0 1 1 hpar z (by push_cast; linarith)).symm
  · have hw : Tendsto (fun s : ℂ ↦ 2 * s + ((0 : ℤ) : ℂ) - 1) (𝓝[≠] 1) (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : Continuous (fun s : ℂ ↦ 2 * s + ((0 : ℤ) : ℂ) - 1) := by fun_prop
        have h := hc.tendsto 1
        have e : (2 * 1 + ((0 : ℤ) : ℂ) - 1 : ℂ) = 1 := by norm_num
        rw [e] at h
        exact h.mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun s hs ↦ hcond2 s hs
    have hres := (DirichletCharacter.LFunctionTrivChar_residue_one (N := L)).comp hw
    have hPc : Tendsto P (𝓝[≠] 1) (𝓝 (P 1)) :=
      (hPd 1 (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hC0 := tendsto_sub_one_mul_zero (differentiableAt_heckeC (0 : ℤ) L
      (1 : DirichletCharacter ℂ M) (s := 1) (Or.inl (hcond1 1 (by norm_num))))
    have hR0 := tendsto_sub_one_mul_zero (hR 1)
    have hlim := (hC0.add (hPc.mul (hres.const_mul (1 / 2 : ℂ)))).add hR0
    have hlim' : Tendsto (fun s ↦ (s - 1) * eisensteinCharSCont 0 (1 : DirichletCharacter ℂ L)
        (1 : DirichletCharacter ℂ M) z s) (𝓝[≠] 1)
        (𝓝 (0 + P 1 * (1 / 2 * ∏ p ∈ L.primeFactors, (1 - (p : ℂ)⁻¹)) + 0)) := by
      refine hlim.congr (fun s ↦ ?_)
      rw [hF s]
      simp only [Function.comp]
      push_cast
      ring_nf
    have hsq : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = (π : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
    have hΓ : Gamma (2⁻¹) = (Real.sqrt π : ℂ) := by
      have := Complex.Gamma_ofReal (1 / 2 : ℝ)
      rw [Real.Gamma_one_half_eq] at this
      push_cast at this
      rw [← this]
      norm_num
    have hP1 : P 1 = 2 * (π : ℂ) * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹)) * (z.im : ℂ)⁻¹ := by
      rw [hP]
      norm_num [Complex.Gamma_one, hΓ, Complex.cpow_neg_one]
      left
      rw [one_div, hΓ]
      linear_combination (2 * ∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹)) * hsq
    convert hlim' using 2
    rw [hP1]
    ring

end ModularFormsKB.Miyake.HeckeTrick
