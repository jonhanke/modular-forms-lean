import ModularFormsKB.Miyake.Sec4_3.Hecke
import ModularFormsKB.Miyake.Sec4_3.Gauss

/-!
# Miyake §4.3: twists by Dirichlet characters

* `Miyake.fricke_isModularFormChar`, `Miyake.fricke_isCuspFormChar` (Lemma 4.3.2(2)):
  $f \mapsto f|_k\omega_N$ maps $M_k(N,\chi)$ to $M_k(N,\bar\chi)$ and $S_k(N,\chi)$ to $S_k(N,\bar\chi)$.
* `Miyake.twisted_hecke` (Lemma 4.3.9): $(A_\psi) \iff (B_\psi)$.
* `Miyake.fricke_twist` (Theorem 4.3.11): $f_\psi|_k\omega(Nm^2) = C_\psi\, g_{\bar\psi}$.
* `Miyake.twisted_completedL_cuspForm` (Theorem 4.3.12): cusp forms satisfy $(B_\psi)$.
* `Miyake.completedL_cuspForm` (Corollary 4.3.7): cusp forms with character satisfy (B).
-/

open Complex Filter Asymptotics CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Pointwise

noncomputable section

namespace Miyake

/-- The Fricke matrix `ω_N = !![0, -1; N, 0]` in `GL₂(ℝ)`. -/
def omegaGL (N : ℕ) (hN : 0 < N) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; (N : ℝ), 0]
    (by simp [Matrix.det_fin_two]; exact_mod_cast hN.ne')

lemma omegaGL_apply (N : ℕ) (hN : 0 < N) :
    (omegaGL N hN : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (N : ℝ), 0] := rfl

lemma omegaGL_det (N : ℕ) (hN : 0 < N) : (omegaGL N hN).det.val = N := by
  simp [omegaGL, Matrix.det_fin_two]

/-- Mathlib's slash by `ω_N` is `N^(k/2 - 1)` times Miyake's `fricke`. -/
lemma omegaGL_slash_apply {k : ℤ} {N : ℕ} (hN : 0 < N) (f : ℂ → ℂ) (τ : ℍ) :
    ((fun τ : ℍ ↦ f τ) ∣[k] omegaGL N hN) τ =
      ((√(N:ℝ) : ℂ) ^ (k - 2)) * fricke k N f τ := by
  have hdet : 0 < (omegaGL N hN).det.val := by rw [omegaGL_det]; exact_mod_cast hN
  have hσ : ∀ x, σ (omegaGL N hN) x = x := by intro x; unfold σ; rw [ite_eq_left hdet]; rfl
  have hden : denom (omegaGL N hN) τ = N * τ := by
    simp [denom, omegaGL_apply]
  have hnum : num (omegaGL N hN) τ = -1 := by
    simp [num, omegaGL_apply]
  have hsm : ((omegaGL N hN • τ : ℍ) : ℂ) = -1 / (N * τ) := by
    rw [coe_smul_of_det_pos hdet, hnum, hden]
  rw [ModularForm.slash_apply, hσ, hsm, hden, omegaGL_det]
  have hs : (√(N:ℝ) : ℂ) ≠ 0 := by
    simp; exact_mod_cast hN.ne'
  have hNs : (N : ℂ) = (√(N:ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; simp
  unfold fricke
  rw [abs_of_pos (by exact_mod_cast hN)]
  push_cast
  generalize (√(N:ℝ) : ℂ) = s at hs hNs ⊢
  generalize f (-1 / ((N:ℂ) * τ)) = F
  rw [hNs, mul_zpow, mul_zpow, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
  have h1 : s ^ ((2:ℕ) * (k - 1)) * s ^ ((2:ℕ) * (-k)) = s ^ (k - 2) * s ^ (-k) := by
    rw [← zpow_add₀ hs, ← zpow_add₀ hs]; congr 1; push_cast; ring
  linear_combination (F * (τ : ℂ) ^ (-k)) * h1

/-- Conjugation of `Γ₀(N)` by `ω_N`: `ω_N γ = γ' ω_N` with `γ' = [[d, -c/N], [-bN, a]]`. -/
lemma exists_fricke_conj {N : ℕ} (hN : 0 < N) (γ : SL(2, ℤ)) (h : (γ 1 0 : ZMod N) = 0) :
    ∃ γ' : SL(2, ℤ), γ' 1 0 = -(γ 0 1) * N ∧ γ' 1 1 = γ 0 0 ∧ γ' 0 0 = γ 1 1 ∧
      Matrix.SpecialLinearGroup.mapGL ℝ γ' * omegaGL N hN =
        omegaGL N hN * Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  obtain ⟨c', hc'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hmem : (!![γ 1 1, -c'; -(γ 0 1) * N, γ 0 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two]; simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hc'] at hdet
    linear_combination hdet
  obtain ⟨γ', hγ'⟩ : ∃ γ' : SL(2, ℤ),
      (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![γ 1 1, -c'; -(γ 0 1) * N, γ 0 0] :=
    ⟨⟨_, hmem⟩, rfl⟩
  have e00 : γ' 0 0 = γ 1 1 := by rw [hγ']; rfl
  have e01 : γ' 0 1 = -c' := by rw [hγ']; rfl
  have e10 : γ' 1 0 = -(γ 0 1) * N := by rw [hγ']; rfl
  have e11 : γ' 1 1 = γ 0 0 := by rw [hγ']; rfl
  refine ⟨γ', e10, e11, e00, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [omegaGL, Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10, e11, hc'] <;> ring)

/-- Miyake's `fricke` as a scalar multiple of Mathlib's slash by `ω_N`. -/
lemma fricke_eq_smul_slash {k : ℤ} {N : ℕ} (hN : 0 < N) (f : ℂ → ℂ) :
    (fun τ : ℍ ↦ fricke k N f τ) =
      ((√(N:ℝ) : ℂ) ^ (2 - k)) • ((fun τ : ℍ ↦ f τ) ∣[k] omegaGL N hN) := by
  have hs : (√(N:ℝ) : ℂ) ≠ 0 := by
    simp; exact_mod_cast hN.ne'
  funext τ
  simp only [Pi.smul_apply, omegaGL_slash_apply hN, smul_eq_mul]
  rw [← mul_assoc, ← zpow_add₀ hs]
  simp

/-- Slash by `Γ₀(N)` of the Fricke transform of an eigenfunction. -/
lemma slash_omega_char {k : ℤ} {N : ℕ} (hN : 0 < N) (χ : DirichletCharacter ℂ N)
    {F : ℍ → ℂ} (hF : ∀ γ ∈ Gamma0 N, F ∣[k] γ = χ (γ 1 1 : ZMod N) • F) :
    ∀ γ ∈ Gamma0 N, (F ∣[k] omegaGL N hN) ∣[k] γ = χ⁻¹ (γ 1 1 : ZMod N) • (F ∣[k] omegaGL N hN) := by
  intro γ hγ
  obtain ⟨γ', e10, e11, e00, hmul⟩ := exists_fricke_conj hN γ hγ
  have hγ' : γ' ∈ Gamma0 N := by
    rw [Gamma0_mem, e10]; simp
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hz : ((γ 0 0 : ℤ) : ZMod N) * (γ 1 1 : ℤ) = 1 := by
    have h1 : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod N) = 1 := by
      rw [hdet]; simp
    have h2 : ((γ 1 0 : ℤ) : ZMod N) = 0 := hγ
    push_cast at h1
    rw [h2] at h1
    simpa using h1
  have hσ : ∀ x, σ (omegaGL N hN) x = x := by
    intro x; unfold σ
    rw [ite_eq_left (by rw [omegaGL_det]; exact_mod_cast hN)]; rfl
  have hchi : χ (γ' 1 1 : ZMod N) = χ⁻¹ (γ 1 1 : ZMod N) := by
    rw [e11, MulChar.inv_apply_eq_inv']
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, hz, map_one])
  show (F ∣[k] omegaGL N hN) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) = _
  rw [← SlashAction.slash_mul, ← hmul, SlashAction.slash_mul]
  have := hF γ' hγ'
  rw [show F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ') = F ∣[k] γ' from rfl, this,
    ModularForm.smul_slash, hσ, hchi]

/-- `Γ₁(N)` is contained in its conjugate by `ω_N`. -/
lemma gamma1_le_conj {N : ℕ} (hN : 0 < N) :
    (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (omegaGL N hN)⁻¹ • (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) := by
  intro x hx
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hx
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul]
  have hγ1 := (Gamma1_mem N γ).1 hγ
  obtain ⟨γ', e10, e11, e00, hmul⟩ := exists_fricke_conj hN γ hγ1.2.2
  refine Subgroup.mem_map.2 ⟨γ', ?_, ?_⟩
  · rw [Gamma1_mem, e10, e11, e00]
    refine ⟨hγ1.2.1, hγ1.1, ?_⟩
    simp
  · rw [eq_mul_inv_iff_mul_eq]; exact hmul

/-- The Fricke transform of a `χ`-eigenfunction is a `χ⁻¹`-eigenfunction. -/
lemma fricke_slash_gamma0 {k : ℤ} {N : ℕ} (hN : 0 < N) (χ : DirichletCharacter ℂ N) {f : ℂ → ℂ}
    (hf : ∀ γ ∈ Gamma0 N, (fun τ : ℍ ↦ f τ) ∣[k] γ = χ (γ 1 1 : ZMod N) • (fun τ : ℍ ↦ f τ)) :
    ∀ γ ∈ Gamma0 N, (fun τ : ℍ ↦ fricke k N f τ) ∣[k] γ =
      χ⁻¹ (γ 1 1 : ZMod N) • (fun τ : ℍ ↦ fricke k N f τ) := by
  intro γ hγ
  rw [fricke_eq_smul_slash hN f, ModularForm.SL_smul_slash, slash_omega_char hN χ hf γ hγ,
    smul_comm]

lemma denom_SL (γ : SL(2, ℤ)) (w : ℂ) :
    denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map
      (Int.castRingHom ℝ)) γ)) w = ((γ 1 0 : ℤ) : ℂ) * w + ((γ 1 1 : ℤ) : ℂ) := by
  simp [denom]

/-- The per-term identity of Miyake's proof of Theorem 4.3.11, via the matrix identity (4.3.22):
`ω(Nm²) ∘ α(u/m)` applied to `f` equals `χ(m)` times `g` translated by `v/m`. -/
lemma fricke_translate_term_eq {k : ℤ} {N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    (χ : DirichletCharacter ℂ N) {a b : ℕ → ℂ}
    (hslash : ∀ γ ∈ Gamma0 N, (fun τ : ℍ ↦ qSeries a τ) ∣[k] γ =
      χ (γ 1 1 : ZMod N) • (fun τ : ℍ ↦ qSeries a τ))
    (hg : ∀ z : ℂ, 0 < z.im → fricke k N (qSeries a) z = qSeries b z)
    (u v n : ℤ) (h : (m : ℤ) * n - u * v * N = 1) {z : ℂ} (hz : 0 < z.im) :
    fricke k ((N : ℝ) * (m : ℝ) ^ 2) (fun ζ ↦ qSeries a (ζ + ((u : ℝ) / m : ℝ))) z =
      χ m * qSeries b (z + ((v : ℝ) / m : ℝ)) := by
  have hz' : 0 < (z + (((v : ℝ) / m : ℝ) : ℂ)).im := by simpa using hz
  let w : ℍ := ⟨z + (((v : ℝ) / m : ℝ) : ℂ), hz'⟩
  have hγ0 : gammaMV N m v u n h ∈ Gamma0 N := by
    rw [Gamma0_mem]; simp [gammaMV]
  have h1 := congrFun (fricke_slash_gamma0 hN χ hslash _ hγ0) w
  rw [ModularForm.SL_slash_apply] at h1
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  have hζ := coe_specialLinearGroup_apply (gammaMV N m v u n h) w
  have hden : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map
      (Int.castRingHom ℝ)) (gammaMV N m v u n h))) (w : ℂ) =
      -((u : ℂ) * N) * (z + v / m) + n := by
    rw [denom_SL]; simp [gammaMV, w]
  have hζ' : ((gammaMV N m v u n h • w : ℍ) : ℂ) =
      (m * (z + v / m) + -v) / (-((u : ℂ) * N) * (z + v / m) + n) := by
    rw [hζ]; simp [gammaMV, w]
  have hD0 : (-((u : ℂ) * N) * (z + v / m) + n) ≠ 0 := by
    rw [← hden]; exact denom_ne_zero _ _
  rw [hden] at h1
  have hwC : (w : ℂ) = z + v / m := by simp [w]
  have hg_w := hg (w : ℂ) w.im_pos
  have hn : (gammaMV N m v u n h : SL(2, ℤ)) 1 1 = n := rfl
  rw [hn, hg_w, hwC] at h1
  rw [hζ'] at h1
  generalize hD : (-((u : ℂ) * N) * (z + v / m) + n) = D at hD0 h1 hζ'
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  have hhC : (m : ℂ) * n - u * v * N = 1 := by exact_mod_cast h
  have hDm : (m : ℂ) * D = 1 - u * N * m * z := by
    rw [← hD]; field_simp; linear_combination hhC
  have hζ2 : (m * (z + v / m) + -v) / D = m * z / D := by
    congr 1; field_simp; ring
  rw [hζ2] at h1
  have hs : (√(N : ℝ) : ℂ) ≠ 0 := by simp; exact_mod_cast hN.ne'
  have hsq : (√((N : ℝ) * (m : ℝ) ^ 2) : ℂ) = m * (√(N : ℝ) : ℂ) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]; push_cast; ring
  have harg : -1 / (((N : ℝ) * (m : ℝ) ^ 2 : ℝ) * z : ℂ) + (((u : ℝ) / m : ℝ) : ℂ) =
      -1 / ((N : ℂ) * (m * z / D)) := by
    push_cast
    field_simp
    linear_combination hDm
  unfold fricke at h1 ⊢
  beta_reduce
  rw [harg, hsq]
  have e : (m : ℂ) * (√(N : ℝ) : ℂ) * z = ((√(N : ℝ) : ℂ) * (m * z / D)) * D := by
    field_simp
  rw [e, mul_zpow]
  simp only [Complex.ofReal_natCast] at h1 ⊢
  have hmn : (n : ZMod N) * (m : ZMod N) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod N) h
    push_cast at this
    simpa [mul_comm] using this
  have hχ : χ⁻¹ (n : ZMod N) = χ (m : ZMod N) := by
    rw [MulChar.inv_apply_eq_inv']
    exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, hmn, map_one])
  rw [hχ] at h1
  have hc : (((v : ℝ) / m : ℝ) : ℂ) = v / m := by push_cast; rfl
  rw [hc]
  linear_combination h1

/-- The bijection `u ↦ -(uN)⁻¹` of `(ℤ/m)ˣ` (`N` a unit mod `m`). -/
def phiEq {m N : ℕ} [NeZero m] (hmN : m.Coprime N) : (ZMod m)ˣ ≃ (ZMod m)ˣ :=
  (Equiv.mulRight (ZMod.unitOfCoprime N hmN.symm)).trans ((Equiv.inv _).trans (Equiv.neg _))

lemma phiEq_spec {m N : ℕ} [NeZero m] (hmN : m.Coprime N) (u : (ZMod m)ˣ) :
    ((phiEq hmN u : (ZMod m)ˣ) : ZMod m) * (u : ZMod m) * (N : ZMod m) = -1 := by
  have h1 : (((u * ZMod.unitOfCoprime N hmN.symm)⁻¹ : (ZMod m)ˣ) : ZMod m) *
      ((u : ZMod m) * (N : ZMod m)) = 1 := by
    have := Units.inv_mul (u * ZMod.unitOfCoprime N hmN.symm)
    simpa using this
  simp only [phiEq, Equiv.trans_apply, Equiv.coe_mulRight, Equiv.inv_apply, Equiv.neg_apply,
    Units.val_neg]
  linear_combination -h1

/-- A sum over `ZMod m` of a function vanishing off units is the sum over the units. -/
lemma sum_units_eq {m : ℕ} [NeZero m] (h : ZMod m → ℂ) (h0 : ∀ u, ¬ IsUnit u → h u = 0) :
    ∑ u : ZMod m, h u = ∑ u : (ZMod m)ˣ, h (u : ZMod m) := by
  rw [← Finset.sum_image (f := h) (s := Finset.univ) (g := fun u : (ZMod m)ˣ => (u : ZMod m))
    (fun x _ y _ hxy ↦ Units.ext hxy)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro u _ hu
  apply h0
  intro hunit
  exact hu (Finset.mem_image.2 ⟨hunit.unit, Finset.mem_univ _, rfl⟩)

/-- For `u` a unit mod `m` and `v = φ(u)`, there is `n` with `mn - uvN = 1`. -/
lemma exists_n_of_phi {m N : ℕ} [NeZero m] (hmN : m.Coprime N) (u : (ZMod m)ˣ) :
    ∃ n : ℤ, (m : ℤ) * n - (((u : ZMod m).val : ℕ) : ℤ) *
      ((((phiEq hmN u : (ZMod m)ˣ) : ZMod m).val : ℕ) : ℤ) * N = 1 := by
  have h0 : (((((u : ZMod m).val : ℕ) : ℤ) * ((((phiEq hmN u : (ZMod m)ˣ) : ZMod m).val : ℕ) : ℤ)
      * N + 1 : ℤ) : ZMod m) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    linear_combination phiEq_spec hmN u
  obtain ⟨n, hn⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).1 h0
  exact ⟨n, by linarith⟩

/-- **Miyake Lemma 4.3.2(2)**: if $f \in M_k(N, \chi)$ then $f|_k\omega_N \in M_k(N, \bar\chi)$
(here $\bar\chi$ = `χ⁻¹`). Relation: same (the book also states it is an isomorphism; its inverse
is $(-1)^k$ times the same map). -/
@[kb "miyake1989" "§4.3, Lemma 4.3.2(2), p. 115"]
theorem fricke_isModularFormChar {k : ℤ} {N : ℕ} (hN : 0 < N) (χ : DirichletCharacter ℂ N)
    {f : ℂ → ℂ} (hf : IsModularFormChar k N χ fun τ : ℍ ↦ f τ) :
    IsModularFormChar k N χ⁻¹ fun τ : ℍ ↦ fricke k N f τ := by
  obtain ⟨⟨F, hF⟩, hslash⟩ := hf
  have hslash' := slash_omega_char hN χ hslash
  have hfr := fricke_eq_smul_slash (k := k) hN f
  refine ⟨⟨(√(N:ℝ) : ℂ) ^ (2 - k) •
    ModularForm.restrict (gamma1_le_conj hN) (ModularForm.translate F (omegaGL N hN)), ?_⟩, ?_⟩
  · rw [hfr, ← hF]
    simp only [FunLike.coe_smul]
    rfl
  · intro γ hγ
    rw [hfr, ModularForm.SL_smul_slash, hslash' γ hγ, smul_comm]

/-- **Miyake Lemma 4.3.2(2)**, cusp forms: if $f \in S_k(N, \chi)$ then
$f|_k\omega_N \in S_k(N, \bar\chi)$. Relation: same. -/
@[kb "miyake1989" "§4.3, Lemma 4.3.2(2), p. 115"]
theorem fricke_isCuspFormChar {k : ℤ} {N : ℕ} (hN : 0 < N) (χ : DirichletCharacter ℂ N)
    {f : ℂ → ℂ} (hf : IsCuspFormChar k N χ fun τ : ℍ ↦ f τ) :
    IsCuspFormChar k N χ⁻¹ fun τ : ℍ ↦ fricke k N f τ := by
  obtain ⟨⟨F, hF⟩, hslash⟩ := hf
  have hslash' := slash_omega_char hN χ hslash
  have hfr := fricke_eq_smul_slash (k := k) hN f
  refine ⟨⟨(√(N:ℝ) : ℂ) ^ (2 - k) •
    CuspForm.restrict (gamma1_le_conj hN) (CuspForm.translate F (omegaGL N hN)), ?_⟩, ?_⟩
  · rw [hfr, ← hF]
    simp only [FunLike.coe_smul]
    rfl
  · intro γ hγ
    rw [hfr, ModularForm.SL_smul_slash, hslash' γ hγ, smul_comm]

lemma completedL_sq_mul (N : ℝ) (hN : 0 < N) {m : ℕ} (hm : 0 < m) (a : ℕ → ℂ) (s : ℂ) :
    completedL (N * m ^ 2) a s =
      ((2 * π / (m * √N) : ℝ) : ℂ) ^ (-s) * Gamma s * LSeries a s := by
  rw [completedL, Real.sqrt_mul hN.le, Real.sqrt_sq (by positivity), mul_comm (√N)]

/-- Condition (B) at level $Nm^2$ for the twisted coefficients, when their constant terms vanish,
is condition $(B_\psi)$. -/
lemma heckeCondition_twist_iff {k N m : ℕ} (hN : 0 < N) (hm : 0 < m)
    (ψ : DirichletCharacter ℂ m) (C : ℂ) {a b : ℕ → ℂ}
    (h0 : twist ψ a 0 = 0) (h0' : twist ψ⁻¹ b 0 = 0) :
    HeckeCondition k ((N : ℝ) * (m : ℝ) ^ 2) (I ^ k) (twist ψ a) (fun n ↦ C * twist ψ⁻¹ b n) ↔
      TwistedHeckeCondition k N ψ C a b := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [HeckeCondition, TwistedHeckeCondition, completedL_const_mul]
  simp only [h0, h0', mul_zero, zero_div, add_zero, completedL_sq_mul N hN' hm,
    twistedCompletedL]
  push_cast
  simp only [mul_assoc, mul_left_comm C]

lemma twist_zero_of_one_lt {m : ℕ} (hm : 1 < m) (ψ : DirichletCharacter ℂ m) (a : ℕ → ℂ) :
    twist ψ a 0 = 0 := by
  have : Fact (1 < m) := ⟨hm⟩
  simp [twist, MulChar.map_nonunit ψ not_isUnit_zero]

/-- **Miyake Lemma 4.3.9.** Let $f = \sum a_n e^{2\pi i n z}$, $g = \sum b_n e^{2\pi i n z}$ satisfy
(4.3.7), $k, N$ positive integers, and $\psi$ a primitive Dirichlet character of conductor $m > 1$.
For a constant $C$, the relation
$$(A_\psi)\quad f_\psi|_k\omega(Nm^2) = C\, g_{\bar\psi}$$
holds iff $(B_\psi)$: $\Lambda_N(s; f, \psi)$ continues to an entire function, bounded on vertical
strips, with $\Lambda_N(s;f,\psi) = i^k C\,\Lambda_N(k-s; g, \bar\psi)$. Relation: same. -/
@[kb "miyake1989" "§4.3, Lemma 4.3.9, p. 123"]
theorem twisted_hecke {k N m : ℕ} (hk : 0 < k) (hN : 0 < N) (hm : 1 < m)
    (ψ : DirichletCharacter ℂ m) (hψ : ψ.IsPrimitive) {a b : ℕ → ℂ}
    (ha : CoeffGrowth a) (hb : CoeffGrowth b) (C : ℂ) :
    (∀ z : ℂ, 0 < z.im →
      fricke k (N * m ^ 2) (qSeries (twist ψ a)) z = C * qSeries (twist ψ⁻¹ b) z) ↔
    TwistedHeckeCondition k N ψ C a b := by
  have hm0 : 0 < m := by omega
  have hk' := hecke_fricke (k := k) (N := N * m ^ 2) hk (by positivity) (ha.twist ψ)
    ((hb.twist ψ⁻¹).const_mul C)
  rw [← heckeCondition_twist_iff hN hm0 ψ C (twist_zero_of_one_lt hm ψ a)
    (twist_zero_of_one_lt hm ψ⁻¹ b)]
  push_cast at hk'
  rw [← hk']
  refine forall_congr' fun z ↦ imp_congr_right fun _ ↦ ?_
  rw [qSeries_const_mul, eq_comm]

/-- **Miyake Theorem 4.3.11.** Let $f \in M_k(N,\chi)$ with Fourier coefficients $a$, let
$g = f|_k\omega_N$ have Fourier coefficients $b$, and let $\psi$ be a primitive Dirichlet character
of conductor $m$ with $\gcd(m, N) = 1$. Then
$$f_\psi|_k\omega(Nm^2) = C_\psi\, g_{\bar\psi},\qquad
C_\psi = \chi(m)\,\psi(-N)\,W(\psi)/W(\bar\psi).$$
Relation: same (Miyake also writes $C_\psi = \chi(m)\psi(N)W(\psi)^2/m$). -/
@[kb "miyake1989" "§4.3, Theorem 4.3.11, p. 124"]
theorem fricke_twist {k N m : ℕ} [NeZero m] (hk : 0 < k) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ m) (hψ : ψ.IsPrimitive)
    (hmN : m.Coprime N) {a b : ℕ → ℂ} (ha : CoeffGrowth a) (hb : CoeffGrowth b)
    (hf : IsModularFormChar k N χ fun τ : ℍ ↦ qSeries a τ)
    (hg : ∀ z : ℂ, 0 < z.im → fricke k N (qSeries a) z = qSeries b z) :
    ∀ z : ℂ, 0 < z.im →
      fricke k (N * m ^ 2) (qSeries (twist ψ a)) z = weilConstant χ ψ * qSeries (twist ψ⁻¹ b) z := by
  intro z hz
  obtain ⟨_, hslash⟩ := hf
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hψi : ψ⁻¹.IsPrimitive := isPrimitive_inv_aux hψ
  have hWi : gaussW ψ⁻¹ ≠ 0 := gaussW_ne_zero hψi
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  set c : ℝ := (N : ℝ) * (m : ℝ) ^ 2 with hc
  have hcpos : 0 < c := by positivity
  have hζ : 0 < (-1 / ((c : ℂ) * z)).im := by
    have h1 : (-1 / ((c : ℂ) * z)) = -((c : ℂ) * z)⁻¹ := by rw [neg_div, one_div]
    rw [h1, Complex.neg_im, Complex.inv_im]
    have h2 : 0 < Complex.normSq ((c : ℂ) * z) :=
      Complex.normSq_pos.2 (mul_ne_zero (by exact_mod_cast hcpos.ne') hz0)
    have h3 : ((c : ℂ) * z).im = c * z.im := by simp
    rw [h3, neg_div, neg_neg]
    have : 0 < c * z.im := mul_pos hcpos hz
    positivity
  have hA := sum_transl_eq_gaussW_twist ψ hψ ha hζ
  have hT : ∑ u : ZMod m, ψ⁻¹ u * fricke k c
        (fun ζ ↦ qSeries a (ζ + ((u.val : ℝ) / m : ℝ))) z =
      fricke k c (qSeries (twist ψ a)) z * gaussW ψ⁻¹ := by
    unfold fricke
    beta_reduce
    have e : ∀ u : ZMod m, ψ⁻¹ u * (((√c : ℝ) * z : ℂ) ^ (-(k : ℤ)) *
        qSeries a (-1 / ((c : ℂ) * z) + (((u.val : ℝ) / m : ℝ) : ℂ))) =
        ((√c : ℝ) * z : ℂ) ^ (-(k : ℤ)) * (ψ⁻¹ u *
        qSeries a (-1 / ((c : ℂ) * z) + (((u.val : ℝ) / m : ℝ) : ℂ))) := fun u => by ring
    simp only [e]
    rw [← Finset.mul_sum, hA]
    ring
  have hB := sum_transl_eq_gaussW_twist ψ⁻¹ hψi hb hz
  simp only [inv_inv] at hB
  have hunit : ∀ u : (ZMod m)ˣ, ψ⁻¹ (u : ZMod m) * fricke k c
      (fun ζ ↦ qSeries a (ζ + ((((u : ZMod m).val : ℕ) : ℝ) / m : ℝ))) z =
      ψ (-(N : ZMod m)) * χ m * (ψ ((phiEq hmN u : (ZMod m)ˣ) : ZMod m) *
        qSeries b (z + (((((phiEq hmN u : (ZMod m)ˣ) : ZMod m).val : ℕ) : ℝ) / m : ℝ))) := by
    intro u
    obtain ⟨n, hn⟩ := exists_n_of_phi hmN u
    have h1 := fricke_translate_term_eq (k := (k : ℤ)) hN hm χ hslash hg _ _ n hn hz
    rw [← hc] at h1
    simp only [Int.cast_natCast] at h1
    have hψu : ψ⁻¹ (u : ZMod m) = ψ (-(N : ZMod m)) * ψ ((phiEq hmN u : (ZMod m)ˣ) : ZMod m) := by
      rw [MulChar.inv_apply_eq_inv', eq_comm]
      have h2 : ψ (-(N : ZMod m)) * ψ ((phiEq hmN u : (ZMod m)ˣ) : ZMod m) * ψ (u : ZMod m) = 1 := by
        rw [← map_mul, ← map_mul,
          show -(N : ZMod m) * ((phiEq hmN u : (ZMod m)ˣ) : ZMod m) * (u : ZMod m) = 1 by
            linear_combination -(phiEq_spec hmN u), map_one]
      exact eq_inv_of_mul_eq_one_left h2
    rw [hψu, h1]
    ring
  have hMain : ∑ u : ZMod m, ψ⁻¹ u * fricke k c
        (fun ζ ↦ qSeries a (ζ + ((u.val : ℝ) / m : ℝ))) z =
      ψ (-(N : ZMod m)) * χ m * (gaussW ψ * qSeries (twist ψ⁻¹ b) z) := by
    rw [sum_units_eq _ (fun u hu => by simp [(ψ⁻¹).map_nonunit hu])]
    rw [Finset.sum_congr rfl (fun u _ => hunit u), ← Finset.mul_sum]
    rw [Equiv.sum_comp (phiEq hmN) (fun v : (ZMod m)ˣ => ψ (v : ZMod m) *
      qSeries b (z + ((((v : ZMod m).val : ℕ) : ℝ) / m : ℝ)))]
    rw [← sum_units_eq (fun v : ZMod m => ψ v * qSeries b (z + (((v.val : ℕ) : ℝ) / m : ℝ)))
      (fun v hv => by simp [ψ.map_nonunit hv]), hB]
  unfold weilConstant
  rw [div_mul_eq_mul_div, eq_div_iff hWi]
  linear_combination hT.symm.trans hMain

/-- A cusp form with character is a modular form with character. -/
lemma IsCuspFormChar.isModularFormChar {k : ℤ} {N : ℕ} {χ : DirichletCharacter ℂ N}
    {f : ℍ → ℂ} (hf : IsCuspFormChar k N χ f) : IsModularFormChar k N χ f := by
  obtain ⟨⟨F, hF⟩, h2⟩ := hf
  exact ⟨⟨ModularFormClass.modularForm F, by rw [← hF]; rfl⟩, h2⟩

/-- The constant coefficient of a cusp form with character vanishes. -/
lemma IsCuspFormChar.coeff_zero {k : ℤ} {N : ℕ} (hN : 0 < N) {χ : DirichletCharacter ℂ N}
    {a : ℕ → ℂ} (ha : CoeffGrowth a) (hf : IsCuspFormChar k N χ fun τ : ℍ ↦ qSeries a τ) :
    a 0 = 0 := by
  obtain ⟨⟨F, hF⟩, -⟩ := hf
  obtain ⟨b, hb, hb0, hFb⟩ := exists_qSeries_cuspForm hN F
  have hab : a = b := qSeries_coeff_unique ha hb fun z hz ↦ by
    have h1 := congrFun hF ⟨z, hz⟩
    have h2 := hFb ⟨z, hz⟩
    simp only at h1 h2
    rw [← h1, h2]
  rw [hab, hb0]

/-- If $g = f|_k\omega_N$ on $\mathbb H$ and $f \in S_k(N, \chi)$, then $g \in S_k(N, \bar\chi)$. -/
lemma isCuspFormChar_of_fricke_eq {k : ℤ} {N : ℕ} (hN : 0 < N) {χ : DirichletCharacter ℂ N}
    {a b : ℕ → ℂ} (hf : IsCuspFormChar k N χ fun τ : ℍ ↦ qSeries a τ)
    (hg : ∀ z : ℂ, 0 < z.im → fricke k N (qSeries a) z = qSeries b z) :
    IsCuspFormChar k N χ⁻¹ fun τ : ℍ ↦ qSeries b τ := by
  have h := fricke_isCuspFormChar hN χ hf
  have he : (fun τ : ℍ ↦ fricke k N (qSeries a) τ) = fun τ : ℍ ↦ qSeries b τ :=
    funext fun τ ↦ hg τ τ.im_pos
  rwa [he] at h

/-- **Miyake Theorem 4.3.12.** Let $f \in S_k(N,\chi)$ with Fourier coefficients $a$, let
$g = f|_k\omega_N$ have coefficients $b$, and let $\psi$ be a primitive Dirichlet character of
conductor $m$ with $\gcd(m,N) = 1$. Then $\Lambda_N(s; f, \psi)$ continues to an entire function,
bounded on vertical strips, with $\Lambda_N(s;f,\psi) = i^k C_\psi \Lambda_N(k - s; g, \bar\psi)$.
Relation: same. -/
@[kb "miyake1989" "§4.3, Theorem 4.3.12, p. 125"]
theorem twisted_completedL_cuspForm {k N m : ℕ} [NeZero m] (hk : 0 < k) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ m) (hψ : ψ.IsPrimitive)
    (hmN : m.Coprime N) {a b : ℕ → ℂ} (ha : CoeffGrowth a) (hb : CoeffGrowth b)
    (hf : IsCuspFormChar k N χ fun τ : ℍ ↦ qSeries a τ)
    (hg : ∀ z : ℂ, 0 < z.im → fricke k N (qSeries a) z = qSeries b z) :
    TwistedHeckeCondition k N ψ (weilConstant χ ψ) a b := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hA := fricke_twist hk hN χ ψ hψ hmN ha hb hf.isModularFormChar hg
  have ha0 : a 0 = 0 := hf.coeff_zero hN ha
  have hb0 : b 0 = 0 := (isCuspFormChar_of_fricke_eq hN hf hg).coeff_zero hN hb
  rw [← heckeCondition_twist_iff hN hm0 ψ _ (by simp [twist, ha0]) (by simp [twist, hb0])]
  have hk' := hecke_fricke (k := k) (N := N * m ^ 2) hk (by positivity) (ha.twist ψ)
    ((hb.twist ψ⁻¹).const_mul (weilConstant χ ψ))
  push_cast at hk'
  refine hk'.1 fun z hz ↦ ?_
  rw [qSeries_const_mul, hA z hz]

/-- **Miyake Corollary 4.3.7.** Let $f \in S_k(N,\chi)$ have Fourier coefficients $a$ of polynomial
growth. Then $f|_k\omega_N = \sum b_n e^{2\pi i n z}$ for coefficients $b$ of polynomial growth,
$a_0 = b_0 = 0$, and $\Lambda_N(s; f)$ continues to an entire function, bounded on vertical strips,
with $\Lambda_N(s;f) = i^k \Lambda_N(k-s; f|_k\omega_N)$ (`Miyake.HeckeCondition` with $C = i^k$ and
vanishing constant terms). Relation: same. -/
@[kb "miyake1989" "§4.3, Corollary 4.3.7, p. 122"]
theorem completedL_cuspForm {k N : ℕ} (hk : 0 < k) (hN : 0 < N) (χ : DirichletCharacter ℂ N)
    {a : ℕ → ℂ} (ha : CoeffGrowth a) (hf : IsCuspFormChar k N χ fun τ : ℍ ↦ qSeries a τ) :
    ∃ b : ℕ → ℂ, CoeffGrowth b ∧ a 0 = 0 ∧ b 0 = 0 ∧
      (∀ z : ℂ, 0 < z.im → fricke k N (qSeries a) z = qSeries b z) ∧
      HeckeCondition k N (I ^ k) a b := by
  obtain ⟨⟨G, hG⟩, -⟩ := fricke_isCuspFormChar hN χ hf
  obtain ⟨b, hb, hb0, hGb⟩ := exists_qSeries_cuspForm hN G
  have hfg : ∀ z : ℂ, 0 < z.im → fricke k N (qSeries a) z = qSeries b z := fun z hz ↦ by
    have h1 := congrFun hG ⟨z, hz⟩
    have h2 := hGb ⟨z, hz⟩
    simp only at h1 h2
    rw [← h1, h2]
  refine ⟨b, hb, hf.coeff_zero hN ha, hb0, hfg, ?_⟩
  exact (hecke_fricke hk hN ha hb).1 fun z hz ↦ (hfg z hz).symm

end Miyake
