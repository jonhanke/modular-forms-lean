/-
# The spaces $M_{k+1/2}(4N, \chi)$ and $S_{k+1/2}(4N, \chi)$

Following Shimura 1973 `shimura1973` (his $M_{\kappa/2}(N, \chi)$ with $\kappa = 2k+1$ odd and $4 \mid N$)
[unverified], for $k \in \mathbb N$, $N \ge 1$ and a Dirichlet character $\chi$ mod $4N$, a function $f : \mathbb H \to \mathbb C$ is
a **modular form of weight $k + \tfrac12$ on $\Gamma_0(4N)$ with character $\chi$** if
1. $f$ is holomorphic on $\mathbb H$;
2. $f(\gamma z) = \chi(d)\, j(\gamma, z)^{2k+1} f(z)$ for all $\gamma \in \Gamma_0(4N)$, with $j$ the theta multiplier (`thetaMult`);
3. $f$ is holomorphic at every cusp: for every $\gamma \in \mathrm{SL}_2(\mathbb Z)$, $|cz+d|^{-(k+1/2)}|f(\gamma z)|$ is bounded as
   $\operatorname{Im} z \to \infty$.

It is a **cusp form** if in 3. the expression tends to $0$. Condition 3 is stated with absolute values, which makes it
independent of the branch of $(cz+d)^{k+1/2}$ and of the multiplier at the other cusps; it is equivalent to the usual
"holomorphic at the cusps" because $f$ has a Fourier expansion at each cusp [unverified: standard, e.g. Koblitz IV.§1].

The multiplier $j(\gamma,z)$ is defined explicitly, not as $\theta(\gamma z)/\theta(z)$ (`ModularFormsKB/HalfIntegral/Theta.lean`). The
two agree on $\Gamma_0(4)$ exactly when `ThetaTransformationLaw` holds.

**Fourier coefficients.** `HasQExpansion f a` says $f(\tau) = \sum_{n \ge 0} a(n) e(n\tau)$ on $\mathbb H$. Every
$f \in M_{k+1/2}(4N,\chi)$ has one, since $T \in \Gamma_0(4N)$ and $j(T, z) = 1$ [unverified as a Lean statement here];
the Hecke operators, the plus space and the Shimura lift below are stated on coefficient sequences, through `HasQExpansion`.

**Index shift.** Matrix entries are 0-based: $c = \gamma_{1,0}$, $d = \gamma_{1,1}$.
-/
import ModularFormsKB.HalfIntegral.Theta
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup
open scoped Real
open scoped Manifold

local notation "ℍ" => UpperHalfPlane

/-- **The weight $k+\tfrac12$ transformation law with character $\chi$ on $\Gamma_0(4N)$:**
$f(\gamma\tau) = \chi(d)\,j(\gamma,\tau)^{2k+1} f(\tau)$. -/
def HalfIntTransforms (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (f : ℍ → ℂ) : Prop :=
  ∀ γ ∈ Gamma0 (4 * N), ∀ τ : ℍ,
    f (γ • τ) = χ (γ 1 1 : ZMod (4 * N)) * thetaMult γ τ ^ (2 * k + 1) * f τ

/-- The **cusp quantity** $|c\tau + d|^{-(k+1/2)}\,|f(\gamma\tau)|$ of $f$ at the cusp $\gamma\infty$. -/
noncomputable def cuspNorm (k : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) : ℝ :=
  ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-((k : ℝ) + 1 / 2)) * ‖f (γ • τ)‖

/-- **$f \in M_{k+1/2}(4N, \chi)$:** holomorphic, the transformation law, and bounded at every cusp. -/
structure IsHalfIntModularForm (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (f : ℍ → ℂ) : Prop where
  holo : MDiff f
  transforms : HalfIntTransforms k N χ f
  bdd_at_cusps : ∀ γ : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty (cuspNorm k f γ)

/-- **$f \in S_{k+1/2}(4N, \chi)$:** holomorphic, the transformation law, and vanishing at every cusp. -/
structure IsHalfIntCuspForm (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (f : ℍ → ℂ) : Prop where
  holo : MDiff f
  transforms : HalfIntTransforms k N χ f
  zero_at_cusps : ∀ γ : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty (cuspNorm k f γ)

lemma cuspNorm_add_le (k : ℕ) (f g : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    cuspNorm k (f + g) γ τ ≤ cuspNorm k f γ τ + cuspNorm k g γ τ := by
  unfold cuspNorm
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (by simpa using norm_add_le (f (γ • τ)) (g (γ • τ)))
    (Real.rpow_nonneg (norm_nonneg _) _)

lemma cuspNorm_smul (k : ℕ) (c : ℂ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    cuspNorm k (c • f) γ τ = ‖c‖ * cuspNorm k f γ τ := by
  unfold cuspNorm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

lemma cuspNorm_nonneg (k : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) : 0 ≤ cuspNorm k f γ τ :=
  mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _)

lemma cuspNorm_zero (k : ℕ) (γ : SL(2, ℤ)) : cuspNorm k (0 : ℍ → ℂ) γ = 0 := by
  funext τ; simp [cuspNorm]

lemma isBounded_of_le_add {a b h : ℍ → ℝ} (ha : UpperHalfPlane.IsBoundedAtImInfty a)
    (hb : UpperHalfPlane.IsBoundedAtImInfty b) (h0 : ∀ τ, 0 ≤ h τ) (hle : ∀ τ, h τ ≤ a τ + b τ) :
    UpperHalfPlane.IsBoundedAtImInfty h := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at *
  obtain ⟨M, A, hA⟩ := ha
  obtain ⟨M', A', hA'⟩ := hb
  refine ⟨M + M', max A A', fun z hz => ?_⟩
  have h1 := hA z (le_trans (le_max_left _ _) hz)
  have h2 := hA' z (le_trans (le_max_right _ _) hz)
  rw [Real.norm_eq_abs] at *
  rw [abs_of_nonneg (h0 z)]
  have := hle z
  have := le_abs_self (a z)
  have := le_abs_self (b z)
  linarith

lemma isZero_of_le_add {a b h : ℍ → ℝ} (ha : UpperHalfPlane.IsZeroAtImInfty a)
    (hb : UpperHalfPlane.IsZeroAtImInfty b) (h0 : ∀ τ, 0 ≤ h τ) (hle : ∀ τ, h τ ≤ a τ + b τ) :
    UpperHalfPlane.IsZeroAtImInfty h := by
  rw [UpperHalfPlane.isZeroAtImInfty_iff] at *
  intro ε hε
  obtain ⟨A, hA⟩ := ha (ε / 2) (by linarith)
  obtain ⟨A', hA'⟩ := hb (ε / 2) (by linarith)
  refine ⟨max A A', fun z hz => ?_⟩
  have h1 := hA z (le_trans (le_max_left _ _) hz)
  have h2 := hA' z (le_trans (le_max_right _ _) hz)
  rw [Real.norm_eq_abs] at *
  rw [abs_of_nonneg (h0 z)]
  have := hle z
  have := le_abs_self (a z)
  have := le_abs_self (b z)
  linarith

lemma isBounded_smul_real {a : ℍ → ℝ} (c : ℝ) (ha : UpperHalfPlane.IsBoundedAtImInfty a) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ => c * a τ) := by
  unfold UpperHalfPlane.IsBoundedAtImInfty at *
  exact ha.smul c

lemma isZero_smul_real {a : ℍ → ℝ} (c : ℝ) (ha : UpperHalfPlane.IsZeroAtImInfty a) :
    UpperHalfPlane.IsZeroAtImInfty (fun τ => c * a τ) := by
  unfold UpperHalfPlane.IsZeroAtImInfty at *
  exact ha.smul c

/-- **The space $M_{k+1/2}(4N, \chi)$** as a $\mathbb C$-submodule of functions $\mathbb H \to \mathbb C$. -/
def halfIntModularForms (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Submodule ℂ (ℍ → ℂ) where
  carrier := {f | IsHalfIntModularForm k N χ f}
  zero_mem' := by
    refine ⟨mdifferentiable_const, fun γ _ τ => by simp, fun γ => ?_⟩
    rw [cuspNorm_zero]; exact UpperHalfPlane.zero_form_isBoundedAtImInfty
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3⟩ ⟨hg1, hg2, hg3⟩
    refine ⟨hf1.add hg1, fun γ hγ τ => ?_, fun γ => ?_⟩
    · simp only [Pi.add_apply, hf2 γ hγ τ, hg2 γ hγ τ]; ring
    · exact isBounded_of_le_add (hf3 γ) (hg3 γ) (cuspNorm_nonneg k _ γ) (cuspNorm_add_le k f g γ)
  smul_mem' := by
    rintro c f ⟨hf1, hf2, hf3⟩
    refine ⟨hf1.const_smul c, fun γ hγ τ => ?_, fun γ => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hf2 γ hγ τ]; ring
    · have := isBounded_smul_real ‖c‖ (hf3 γ)
      convert this using 1
      funext τ; exact cuspNorm_smul k c f γ τ

/-- **The space $S_{k+1/2}(4N, \chi)$** of cusp forms, as a $\mathbb C$-submodule. -/
def halfIntCuspForms (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Submodule ℂ (ℍ → ℂ) where
  carrier := {f | IsHalfIntCuspForm k N χ f}
  zero_mem' := by
    refine ⟨mdifferentiable_const, fun γ _ τ => by simp, fun γ => ?_⟩
    rw [cuspNorm_zero]; exact Filter.zero_zeroAtFilter _
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3⟩ ⟨hg1, hg2, hg3⟩
    refine ⟨hf1.add hg1, fun γ hγ τ => ?_, fun γ => ?_⟩
    · simp only [Pi.add_apply, hf2 γ hγ τ, hg2 γ hγ τ]; ring
    · exact isZero_of_le_add (hf3 γ) (hg3 γ) (cuspNorm_nonneg k _ γ) (cuspNorm_add_le k f g γ)
  smul_mem' := by
    rintro c f ⟨hf1, hf2, hf3⟩
    refine ⟨hf1.const_smul c, fun γ hγ τ => ?_, fun γ => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hf2 γ hγ τ]; ring
    · have := isZero_smul_real ‖c‖ (hf3 γ)
      convert this using 1
      funext τ; exact cuspNorm_smul k c f γ τ

/-- $S_{k+1/2}(4N,\chi) \subseteq M_{k+1/2}(4N,\chi)$. -/
theorem halfIntCuspForms_le (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) :
    halfIntCuspForms k N χ ≤ halfIntModularForms k N χ :=
  fun _ hf => ⟨hf.holo, hf.transforms, fun γ => (hf.zero_at_cusps γ).isBoundedAtImInfty⟩

/-- **$q$-expansion:** $f(\tau) = \sum_{n\ge0} a(n)\,e^{2\pi i n\tau}$ for all $\tau \in \mathbb H$. -/
def HasQExpansion (f : ℍ → ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun n : ℕ ↦ a n * cexp (2 * π * I * n * τ)) (f τ)

/-- **Products land in integral weight.** If $f$ has weight $k+\tfrac12$ and character $\chi$ and $g$ has weight $l+\tfrac12$
and character $\psi$ (same level $4N$), then $fg$ satisfies the integral weight $k+l+1$ law with character
$\chi\psi\chi_{-4}^{\,k+l+1}$: $(fg)(\gamma\tau) = \chi\psi(d)\,\chi_{-4}(d)^{k+l+1}(c\tau+d)^{k+l+1}(fg)(\tau)$. Uses `thetaMult_sq`. -/
theorem HalfIntTransforms.mul {k l N : ℕ} {χ ψ : DirichletCharacter ℂ (4 * N)} {f g : ℍ → ℂ}
    (hf : HalfIntTransforms k N χ f) (hg : HalfIntTransforms l N ψ g) :
    ∀ γ ∈ Gamma0 (4 * N), ∀ τ : ℍ,
      f (γ • τ) * g (γ • τ) = χ (γ 1 1 : ZMod (4 * N)) * ψ (γ 1 1 : ZMod (4 * N)) *
        (ZMod.χ₄ (γ 1 1 : ZMod 4) : ℂ) ^ (k + l + 1) * ((γ 1 0 : ℂ) * τ + γ 1 1) ^ (k + l + 1) *
        (f τ * g τ) := by
  intro γ hγ τ
  have h4 : γ ∈ Gamma0 4 := by
    rw [Gamma0_mem] at hγ ⊢
    have h' : ((γ 1 0 : ℤ) : ZMod (4 * N)) = 0 := hγ
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h' ⊢
    exact dvd_trans (by exact_mod_cast Dvd.intro N rfl) h'
  rw [hf γ hγ τ, hg γ hγ τ]
  have hsq := thetaMult_sq h4 (τ : ℂ)
  have e : thetaMult γ τ ^ (2 * k + 1) * thetaMult γ τ ^ (2 * l + 1) =
      (thetaMult γ τ ^ 2) ^ (k + l + 1) := by rw [← pow_add, ← pow_mul]; congr 1; ring
  calc _ = (χ (γ 1 1 : ZMod (4 * N)) * ψ (γ 1 1 : ZMod (4 * N))) *
        (thetaMult γ τ ^ (2 * k + 1) * thetaMult γ τ ^ (2 * l + 1)) * (f τ * g τ) := by ring
    _ = _ := by rw [e, hsq, mul_pow]; ring

/-- **$\theta \in M_{1/2}(4, 1)$, given the transformation law and the cusp bounds** (Shimura 1973 `shimura1973`, §1
[unverified]). Both hypotheses are proved (`theta_transformationLaw` in `Law.lean`, `theta_cusp_bdd_of_bound` with
`norm_theta_le` in `Cusps.lean` and `ThetaBound.lean`); the unconditional statement is `theta_isHalfIntModularForm'`
(`ThetaForms.lean`). -/
theorem theta_isHalfIntModularForm (hlaw : ThetaTransformationLaw)
    (hcusp : ∀ γ : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty (cuspNorm 0 (fun τ : ℍ ↦ theta τ) γ)) :
    IsHalfIntModularForm 0 1 1 (fun τ : ℍ ↦ theta τ) := by
  refine ⟨?_, ?_, hcusp⟩
  · rw [UpperHalfPlane.mdifferentiable_iff]
    refine theta_differentiableOn.congr fun z hz => ?_
    simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  · intro γ hγ τ
    have hγ' : γ ∈ Gamma0 4 := by simpa using hγ
    have hu : IsUnit ((γ 1 1 : ℤ) : ZMod (4 * 1)) := by
      have h0 := (Gamma0_mem).mp hγ'
      have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
        have := Matrix.SpecialLinearGroup.det_coe γ
        rwa [Matrix.det_fin_two] at this
      refine IsUnit.of_mul_eq_one ((γ 0 0 : ℤ) : ZMod (4 * 1)) ?_
      have h0' : ((γ 1 0 : ℤ) : ZMod (4 * 1)) = 0 := by simpa using h0
      have : (((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ)) : ZMod (4 * 1)) = 1 := by rw [hdet]; simp
      push_cast at this
      rw [h0'] at this
      simpa [mul_comm] using this
    simp only [MulChar.one_apply hu, Nat.mul_zero, Nat.zero_add, pow_one, one_mul]
    exact hlaw γ hγ' τ

end ModularFormsKB.HalfIntegral
