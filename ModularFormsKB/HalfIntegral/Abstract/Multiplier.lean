/-
# Half-integral weight over an abstract multiplier system

The theta multiplier is constructed elsewhere (`ModularFormsKB/HalfIntegral/Theta.lean`,
job tk-hiw-foundations). This file works over an **abstract multiplier system** on $\Gamma_0(4)$: a function
$j : \mathrm{SL}_2(\mathbb Z) \times \mathbb H \to \mathbb C$ which, on $\Gamma_0(4)$,
1. is a cocycle: $j(\gamma_1\gamma_2, \tau) = j(\gamma_1, \gamma_2\tau)\, j(\gamma_2, \tau)$;
2. never vanishes, and is holomorphic in $\tau$;
3. has absolute value $|j(\gamma,\tau)|^2 = |c\tau + d|$;
4. is trivial on the translation $T = \begin{pmatrix}1&1\\0&1\end{pmatrix}$, so that invariant functions have $q$-expansions.

The theta multiplier $j(\gamma,\tau) = \theta(\gamma\tau)/\theta(\tau)$ (Shimura 1973 `shimura1973`, §1 [unverified]) is the
intended instance. Relative to a multiplier system $j$, for $k \in \mathbb N$, $N \ge 1$ and a Dirichlet character $\chi$ mod $4N$:
- the **weight $k+\tfrac12$ slash action** $(f|_\gamma)(\tau) = \chi(d)^{-1} j(\gamma,\tau)^{-(2k+1)} f(\gamma\tau)$ (`MultiplierSystem.slash`);
- the transformation law $f(\gamma\tau) = \chi(d)\,j(\gamma,\tau)^{2k+1}f(\tau)$ on $\Gamma_0(4N)$ (`MultiplierSystem.Transforms`),
  equivalently $f|_\gamma = f$ (`MultiplierSystem.transforms_iff_slash`);
- the spaces $M_{k+1/2}(4N,\chi)$ and $S_{k+1/2}(4N,\chi)$ (`MultiplierSystem.modularForms`, `MultiplierSystem.cuspForms`)
  with the cusp conditions stated through absolute values, as in `ModularFormsKB/HalfIntegral/Forms.lean`;
- Kohnen's plus space (`MultiplierSystem.plusCuspForms`).

**Index shift.** Matrix entries are 0-based: $c = \gamma_{1,0}$, $d = \gamma_{1,1}$.
-/
import ModularFormsKB.HalfIntegral.Hecke
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.Modular

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup
open scoped Real
open scoped Manifold

local notation "ℍ" => UpperHalfPlane

/-- **An abstract multiplier system of weight $\tfrac12$ on $\Gamma_0(4)$.** The theta multiplier is the intended instance. -/
structure MultiplierSystem where
  /-- The automorphy factor $j(\gamma, \tau)$. Only its values on $\Gamma_0(4)$ matter. -/
  j : SL(2, ℤ) → ℍ → ℂ
  /-- The cocycle relation on $\Gamma_0(4)$. -/
  cocycle : ∀ γ₁ ∈ Gamma0 4, ∀ γ₂ ∈ Gamma0 4, ∀ τ : ℍ, j (γ₁ * γ₂) τ = j γ₁ (γ₂ • τ) * j γ₂ τ
  /-- $j(\gamma, \cdot)$ never vanishes. -/
  ne_zero : ∀ γ ∈ Gamma0 4, ∀ τ : ℍ, j γ τ ≠ 0
  /-- $j(\gamma, \cdot)$ is holomorphic on $\mathbb H$. -/
  holo : ∀ γ ∈ Gamma0 4, MDiff (j γ)
  /-- $|j(\gamma,\tau)|^2 = |c\tau + d|$. -/
  norm_sq : ∀ γ ∈ Gamma0 4, ∀ τ : ℍ, ‖j γ τ‖ ^ 2 = ‖(γ 1 0 : ℂ) * τ + γ 1 1‖
  /-- $j(T, \tau) = 1$. -/
  j_T : ∀ τ : ℍ, j ModularGroup.T τ = 1

namespace Abstract

/-- The **cusp quantity** $|c\tau + d|^{-(k+1/2)}\,|f(\gamma\tau)|$ of $f$ at the cusp $\gamma\infty$ (the same as `cuspNorm`
in `Forms.lean`; repeated so that this file does not depend on the concrete multiplier). -/
noncomputable def cuspNorm (k : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) : ℝ :=
  ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-((k : ℝ) + 1 / 2)) * ‖f (γ • τ)‖

/-- **$q$-expansion:** $f(\tau) = \sum_{n\ge0} a(n)\,e^{2\pi i n\tau}$ for all $\tau \in \mathbb H$. -/
def HasQExp (f : ℍ → ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun n : ℕ ↦ a n * cexp (2 * π * I * n * τ)) (f τ)

end Abstract

namespace MultiplierSystem

variable (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N))

private lemma cuspNorm_add_le (f g : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    Abstract.cuspNorm k (f + g) γ τ ≤ Abstract.cuspNorm k f γ τ + Abstract.cuspNorm k g γ τ := by
  unfold Abstract.cuspNorm
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (by simpa using norm_add_le (f (γ • τ)) (g (γ • τ))) (by positivity)

private lemma cuspNorm_nonneg (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) : 0 ≤ Abstract.cuspNorm k f γ τ := by
  unfold Abstract.cuspNorm; positivity

private lemma cuspNorm_smul (c : ℂ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) :
    Abstract.cuspNorm k (c • f) γ = fun τ ↦ ‖c‖ * Abstract.cuspNorm k f γ τ := by
  funext τ
  simp only [Abstract.cuspNorm, Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

private lemma bdd_add {u v w : ℍ → ℝ} (hu : UpperHalfPlane.IsBoundedAtImInfty u)
    (hv : UpperHalfPlane.IsBoundedAtImInfty v) (h0 : ∀ τ, 0 ≤ w τ) (h : ∀ τ, w τ ≤ u τ + v τ)
    (hu0 : ∀ τ, 0 ≤ u τ) (hv0 : ∀ τ, 0 ≤ v τ) :
    UpperHalfPlane.IsBoundedAtImInfty w := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at *
  obtain ⟨M1, A1, h1⟩ := hu
  obtain ⟨M2, A2, h2⟩ := hv
  refine ⟨M1 + M2, max A1 A2, fun z hz ↦ ?_⟩
  have a1 := h1 z (le_trans (le_max_left _ _) hz)
  have a2 := h2 z (le_trans (le_max_right _ _) hz)
  rw [Real.norm_of_nonneg (h0 z)]
  rw [Real.norm_of_nonneg (hu0 z)] at a1
  rw [Real.norm_of_nonneg (hv0 z)] at a2
  linarith [h z]

private lemma zero_add' {u v w : ℍ → ℝ} (hu : UpperHalfPlane.IsZeroAtImInfty u)
    (hv : UpperHalfPlane.IsZeroAtImInfty v) (h0 : ∀ τ, 0 ≤ w τ) (h : ∀ τ, w τ ≤ u τ + v τ)
    (hu0 : ∀ τ, 0 ≤ u τ) (hv0 : ∀ τ, 0 ≤ v τ) :
    UpperHalfPlane.IsZeroAtImInfty w := by
  rw [UpperHalfPlane.isZeroAtImInfty_iff] at *
  intro ε hε
  obtain ⟨A1, h1⟩ := hu (ε / 2) (by positivity)
  obtain ⟨A2, h2⟩ := hv (ε / 2) (by positivity)
  refine ⟨max A1 A2, fun z hz ↦ ?_⟩
  have a1 := h1 z (le_trans (le_max_left _ _) hz)
  have a2 := h2 z (le_trans (le_max_right _ _) hz)
  rw [Real.norm_of_nonneg (h0 z)]
  rw [Real.norm_of_nonneg (hu0 z)] at a1
  rw [Real.norm_of_nonneg (hv0 z)] at a2
  linarith [h z]

private lemma bdd_smul' (c : ℂ) {u : ℍ → ℝ} (hu : UpperHalfPlane.IsBoundedAtImInfty u)
    (hu0 : ∀ τ, 0 ≤ u τ) : UpperHalfPlane.IsBoundedAtImInfty (fun τ ↦ ‖c‖ * u τ) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at *
  obtain ⟨M1, A1, h1⟩ := hu
  refine ⟨‖c‖ * M1, A1, fun z hz ↦ ?_⟩
  have a1 := h1 z hz
  rw [Real.norm_of_nonneg (hu0 z)] at a1
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg c) (hu0 z))]
  exact mul_le_mul_of_nonneg_left a1 (norm_nonneg c)

private lemma zero_smul' (c : ℂ) {u : ℍ → ℝ} (hu : UpperHalfPlane.IsZeroAtImInfty u) :
    UpperHalfPlane.IsZeroAtImInfty (fun τ ↦ ‖c‖ * u τ) := by
  have := Filter.Tendsto.const_mul ‖c‖ hu
  show Filter.Tendsto _ _ _
  simpa using this

private lemma gamma0_four {γ : SL(2, ℤ)} (h : γ ∈ Gamma0 (4 * N)) : γ ∈ Gamma0 4 := by
  rw [Gamma0_mem] at *
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at *
  exact dvd_trans (by push_cast; exact dvd_mul_right (4 : ℤ) N) h

private lemma chi_ne_zero {γ : SL(2, ℤ)} (h : γ ∈ Gamma0 (4 * N)) :
    χ (γ 1 1 : ZMod (4 * N)) ≠ 0 := by
  have hc : ((γ 1 0 : ℤ) : ZMod (4 * N)) = 0 := by rwa [Gamma0_mem] at h
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have h1 : ((γ 0 0 : ℤ) : ZMod (4 * N)) * (γ 1 1 : ℤ) = 1 := by
    have := congrArg (fun x : ℤ ↦ (x : ZMod (4 * N))) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at this
    rw [hc] at this
    simpa using this
  have hu : IsUnit ((γ 1 1 : ℤ) : ZMod (4 * N)) :=
    IsUnit.of_mul_eq_one ((γ 0 0 : ℤ) : ZMod (4 * N)) (by rw [← h1]; ring)
  exact (hu.map χ).ne_zero

/-- **The weight $k+\tfrac12$ slash action** $(f|_\gamma)(\tau) = \chi(d)^{-1}\,j(\gamma,\tau)^{-(2k+1)}\,f(\gamma\tau)$. -/
noncomputable def slash (γ : SL(2, ℤ)) (f : ℍ → ℂ) : ℍ → ℂ :=
  fun τ ↦ (χ (γ 1 1 : ZMod (4 * N)))⁻¹ * (M.j γ τ ^ (2 * k + 1))⁻¹ * f (γ • τ)

/-- **The transformation law** $f(\gamma\tau) = \chi(d)\,j(\gamma,\tau)^{2k+1}f(\tau)$ for all $\gamma \in \Gamma_0(4N)$. -/
def Transforms (f : ℍ → ℂ) : Prop :=
  ∀ γ ∈ Gamma0 (4 * N), ∀ τ : ℍ, f (γ • τ) = χ (γ 1 1 : ZMod (4 * N)) * M.j γ τ ^ (2 * k + 1) * f τ

/-- **$f \in M_{k+1/2}(4N,\chi)$ relative to $j$:** holomorphic, the transformation law, bounded at every cusp. -/
structure IsModularForm (f : ℍ → ℂ) : Prop where
  holo : MDiff f
  transforms : M.Transforms k N χ f
  bdd_at_cusps : ∀ γ : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty (Abstract.cuspNorm k f γ)

/-- **$f \in S_{k+1/2}(4N,\chi)$ relative to $j$:** holomorphic, the transformation law, vanishing at every cusp. -/
structure IsCuspForm (f : ℍ → ℂ) : Prop where
  holo : MDiff f
  transforms : M.Transforms k N χ f
  zero_at_cusps : ∀ γ : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty (Abstract.cuspNorm k f γ)

/-- **The space $M_{k+1/2}(4N, \chi)$** relative to the multiplier system $j$. -/
def modularForms : Submodule ℂ (ℍ → ℂ) where
  carrier := {f | M.IsModularForm k N χ f}
  zero_mem' := by
    refine ⟨mdifferentiable_const, fun γ _ τ ↦ by simp, fun γ ↦ ?_⟩
    have : Abstract.cuspNorm k (0 : ℍ → ℂ) γ = 0 := by
      funext τ; simp [Abstract.cuspNorm]
    rw [this]
    exact UpperHalfPlane.zero_form_isBoundedAtImInfty
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.holo.add hg.holo, fun γ hγ τ ↦ ?_, fun γ ↦ ?_⟩
    · show f (γ • τ) + g (γ • τ) = _
      rw [hf.transforms γ hγ τ, hg.transforms γ hγ τ]
      show _ = _ * _ * (f τ + g τ)
      ring
    · exact bdd_add (hf.bdd_at_cusps γ) (hg.bdd_at_cusps γ) (cuspNorm_nonneg k _ γ)
        (cuspNorm_add_le k f g γ) (cuspNorm_nonneg k _ γ) (cuspNorm_nonneg k _ γ)
  smul_mem' := by
    intro c f hf
    refine ⟨hf.holo.const_smul c, fun γ hγ τ ↦ ?_, fun γ ↦ ?_⟩
    · show c • f (γ • τ) = _ * _ * (c • f τ)
      rw [hf.transforms γ hγ τ]
      simp only [smul_eq_mul]
      ring
    · rw [cuspNorm_smul]
      exact bdd_smul' c (hf.bdd_at_cusps γ) (cuspNorm_nonneg k _ γ)

/-- **The space $S_{k+1/2}(4N, \chi)$** relative to the multiplier system $j$. -/
def cuspForms : Submodule ℂ (ℍ → ℂ) where
  carrier := {f | M.IsCuspForm k N χ f}
  zero_mem' := by
    refine ⟨mdifferentiable_const, fun γ _ τ ↦ by simp, fun γ ↦ ?_⟩
    have : Abstract.cuspNorm k (0 : ℍ → ℂ) γ = 0 := by
      funext τ; simp [Abstract.cuspNorm]
    rw [this]
    exact tendsto_const_nhds
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.holo.add hg.holo, fun γ hγ τ ↦ ?_, fun γ ↦ ?_⟩
    · show f (γ • τ) + g (γ • τ) = _
      rw [hf.transforms γ hγ τ, hg.transforms γ hγ τ]
      show _ = _ * _ * (f τ + g τ)
      ring
    · exact zero_add' (hf.zero_at_cusps γ) (hg.zero_at_cusps γ) (cuspNorm_nonneg k _ γ)
        (cuspNorm_add_le k f g γ) (cuspNorm_nonneg k _ γ) (cuspNorm_nonneg k _ γ)
  smul_mem' := by
    intro c f hf
    refine ⟨hf.holo.const_smul c, fun γ hγ τ ↦ ?_, fun γ ↦ ?_⟩
    · show c • f (γ • τ) = _ * _ * (c • f τ)
      rw [hf.transforms γ hγ τ]
      simp only [smul_eq_mul]
      ring
    · rw [cuspNorm_smul]
      exact zero_smul' c (hf.zero_at_cusps γ)

/-- $S_{k+1/2}(4N,\chi) \subseteq M_{k+1/2}(4N,\chi)$. -/
theorem cuspForms_le : M.cuspForms k N χ ≤ M.modularForms k N χ := fun _ hf ↦
  ⟨hf.holo, hf.transforms, fun γ ↦ (hf.zero_at_cusps γ).isBoundedAtImInfty⟩

/-- **Kohnen's plus space** $S^+_{k+1/2}(4N,\chi)$: cusp forms whose $q$-expansion satisfies `PlusCond k`
(Kohnen 1980 `kohnen1980` for $N = 1$, $\chi = 1$; Kohnen 1982 for $N$ odd squarefree [unverified]). -/
def plusCuspForms : Submodule ℂ (ℍ → ℂ) where
  carrier := {f | f ∈ M.cuspForms k N χ ∧ ∃ a, Abstract.HasQExp f a ∧ PlusCond k a}
  zero_mem' := by
    exact ⟨(M.cuspForms k N χ).zero_mem, 0, fun τ ↦ by simp,
      (plusSeq k).zero_mem⟩
  add_mem' := by
    rintro f g ⟨hf, a, ha, hap⟩ ⟨hg, b, hb, hbp⟩
    refine ⟨(M.cuspForms k N χ).add_mem hf hg, a + b, fun τ ↦ ?_,
      (plusSeq k).add_mem hap hbp⟩
    simpa [add_mul] using (ha τ).add (hb τ)
  smul_mem' := by
    rintro c f ⟨hf, a, ha, hap⟩
    refine ⟨(M.cuspForms k N χ).smul_mem c hf, c • a, fun τ ↦ ?_,
      (plusSeq k).smul_mem c hap⟩
    simpa [mul_assoc] using (ha τ).mul_left c

theorem plusCuspForms_le : M.plusCuspForms k N χ ≤ M.cuspForms k N χ := fun _ hf ↦ hf.1

/-- **Invariance under the slash action** is the transformation law: for $\gamma \in \Gamma_0(4N)$, $\chi(d) \neq 0$
(as $d$ is prime to $4N$) and $j(\gamma,\tau) \neq 0$. -/
theorem transforms_iff_slash (f : ℍ → ℂ) :
    M.Transforms k N χ f ↔ ∀ γ ∈ Gamma0 (4 * N), M.slash k N χ γ f = f := by
  refine forall₂_congr fun γ hγ ↦ ?_
  have h1 := chi_ne_zero N χ hγ
  rw [funext_iff]
  refine forall_congr' fun τ ↦ ?_
  have h2 : M.j γ τ ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ (M.ne_zero γ (gamma0_four N hγ) τ)
  simp only [slash]
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    field_simp at h
    linear_combination h

/-- **The slash action is $\mathbb C$-linear.** -/
noncomputable def slashLin (γ : SL(2, ℤ)) : (ℍ → ℂ) →ₗ[ℂ] (ℍ → ℂ) where
  toFun := M.slash k N χ γ
  map_add' f g := by
    funext τ
    simp [slash, mul_add]
  map_smul' c f := by
    funext τ
    simp [slash]
    ring

/-- **The slash action is a right action of $\Gamma_0(4N)$:** $f|_{\gamma_1\gamma_2} = (f|_{\gamma_1})|_{\gamma_2}$. Uses the
cocycle relation and $d(\gamma_1\gamma_2) \equiv d(\gamma_1)d(\gamma_2) \bmod 4N$. -/
theorem slash_mul {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 (4 * N)) (h₂ : γ₂ ∈ Gamma0 (4 * N)) (f : ℍ → ℂ) :
    M.slash k N χ (γ₁ * γ₂) f = M.slash k N χ γ₂ (M.slash k N χ γ₁ f) := by
  funext τ
  have hc : ((γ₁ 1 0 : ℤ) : ZMod (4 * N)) = 0 := by rwa [Gamma0_mem] at h₁
  have hd : (((γ₁ * γ₂) 1 1 : ℤ) : ZMod (4 * N)) = (γ₁ 1 1 : ℤ) * (γ₂ 1 1 : ℤ) := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hc]
  simp only [slash]
  rw [hd, map_mul, M.cocycle γ₁ (gamma0_four N h₁) γ₂ (gamma0_four N h₂) τ, mul_smul, mul_pow, mul_inv, mul_inv]
  ring

end MultiplierSystem

end ModularFormsKB.HalfIntegral
