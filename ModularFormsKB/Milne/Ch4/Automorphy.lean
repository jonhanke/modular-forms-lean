import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import ModularFormsKB.Citation
/-!
# Milne, Chapter 4: automorphy factors

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 4, "Modular forms as
sections of line bundles", pdf pp. 58–60.

The group $\Gamma$ acts on an open set $U \subseteq \mathbb C$ (Milne's $H$) through maps $z \mapsto \gamma z$ given
here as functions `act γ : ℂ → ℂ` that preserve $U$ and satisfy the action laws on $U$ (`IsHolAction`).

## Items
- Definition 4.23, automorphy factor (`IsAutomorphyFactor`), and the remark after it that $j^k$ is again one
  (`IsAutomorphyFactor.pow`).
- Example 4.24: the derivative $(d\gamma)_z$ is an automorphy factor (`isAutomorphyFactor_deriv`); for
  $\mathrm{SL}_2(\mathbb Z)$ on $\mathbb H$ it is $(cz+d)^{-2}$ (`deriv_moebius`).
- Proposition 4.25, the part that takes place on $U \times \mathbb C$: an automorphy factor with $j_1 = 1$ is the same
  as an action of $\Gamma$ on $U \times \mathbb C$ of the form $\gamma(\tau, z) = (\gamma\tau, j_\gamma(\tau)z)$
  (`isAutomorphyFactor_iff_fiberAction`), and equivariant sections $\tau \mapsto (\tau, f(\tau))$ are the functions
  with $f(\gamma\tau) = j_\gamma(\tau)f(\tau)$ (`fiberAction_section_iff`). The passage to line bundles on
  $\Gamma\backslash U$ is not formalized: no library has holomorphic line bundles on the quotient Riemann surface.
- Remark 4.26, every holomorphic line bundle on $\mathbb H$ is trivial: named statement `LineBundlesOnHTrivial`.

## Deviation from the book
Definition 4.23 admits the zero map $j \equiv 0$, which satisfies (a) and (b) but corresponds to no line bundle;
in Proposition 4.25 the factors coming from a trivialization satisfy $j_1 = 1$ and are nowhere zero. The
correspondence is therefore stated for factors with $j_1(\tau) = 1$ (`isAutomorphyFactor_iff_fiberAction`).
Recorded in `docs/updates-and-errata.md`.
-/

open Complex UpperHalfPlane Matrix
open scoped MatrixGroups Manifold ContDiff

noncomputable section

namespace ModularFormsKB.Milne

variable {Γ : Type*} [Group Γ]

/-- A group $\Gamma$ acting on an open set $U \subseteq \mathbb C$ by holomorphic maps: each `act γ` maps $U$ into
itself and is holomorphic on $U$, and `act` satisfies the action laws on $U$. -/
structure IsHolAction (U : Set ℂ) (act : Γ → ℂ → ℂ) : Prop where
  isOpen : IsOpen U
  mapsTo : ∀ γ, Set.MapsTo (act γ) U U
  one : ∀ z ∈ U, act 1 z = z
  mul : ∀ γ γ', ∀ z ∈ U, act (γ * γ') z = act γ (act γ' z)
  holo : ∀ γ, DifferentiableOn ℂ (act γ) U

/-- **Definition 4.23**: an automorphy factor for $\Gamma$ acting on $U$ is a map $j : \Gamma \times U \to \mathbb C$
such that (a) $\tau \mapsto j_\gamma(\tau)$ is holomorphic on $U$ for each $\gamma$, and (b)
$j_{\gamma\gamma'}(\tau) = j_\gamma(\gamma'\tau)\,j_{\gamma'}(\tau)$. -/
@[kb "milne2017mf" "Section 4, Definition 4.23 (pdf p. 59)"]
structure IsAutomorphyFactor (U : Set ℂ) (act : Γ → ℂ → ℂ) (j : Γ → ℂ → ℂ) : Prop where
  holo : ∀ γ, DifferentiableOn ℂ (j γ) U
  cocycle : ∀ γ γ', ∀ τ ∈ U, j (γ * γ') τ = j γ (act γ' τ) * j γ' τ

/-- "If $j$ is an automorphy factor, so also is $j^k$" (p. 59), for $k \in \mathbb N$. -/
@[kb "milne2017mf" "Section 4, remark after Definition 4.23 (pdf p. 59)"]
theorem IsAutomorphyFactor.pow {U : Set ℂ} {act : Γ → ℂ → ℂ} {j : Γ → ℂ → ℂ}
    (hj : IsAutomorphyFactor U act j) (k : ℕ) : IsAutomorphyFactor U act (fun γ τ ↦ j γ τ ^ k) where
  holo γ := (hj.holo γ).pow k
  cocycle γ γ' τ hτ := by rw [hj.cocycle γ γ' τ hτ, mul_pow]

/-- "If $j$ is an automorphy factor, so also is $j^k$ for every integer $k$" (p. 59): for $k \in \mathbb Z$ this
needs $j$ to have no zeros on $U$ (otherwise $j^{-1}$ is not holomorphic). -/
@[kb "milne2017mf" "Section 4, remark after Definition 4.23 (pdf p. 59)"]
theorem IsAutomorphyFactor.zpow {U : Set ℂ} {act : Γ → ℂ → ℂ} {j : Γ → ℂ → ℂ}
    (hj : IsAutomorphyFactor U act j) (hne : ∀ γ, ∀ τ ∈ U, j γ τ ≠ 0) (k : ℤ) :
    IsAutomorphyFactor U act (fun γ τ ↦ j γ τ ^ k) where
  holo γ := (hj.holo γ).zpow (Or.inl (hne γ))
  cocycle γ γ' τ hτ := by rw [hj.cocycle γ γ' τ hτ, mul_zpow]

/-- **Example 4.24**: for a group acting holomorphically on an open $U \subseteq \mathbb C$, the derivative
$j_\gamma(\tau) = (d\gamma)_\tau$ is an automorphy factor (chain rule). -/
@[kb "milne2017mf" "Section 4, Example 4.24 (pdf p. 59)"]
theorem isAutomorphyFactor_deriv {U : Set ℂ} {act : Γ → ℂ → ℂ} (h : IsHolAction U act) :
    IsAutomorphyFactor U act (fun γ ↦ deriv (act γ)) where
  holo γ := (h.holo γ).deriv h.isOpen
  cocycle γ γ' τ hτ := by
    have hU : U ∈ nhds τ := h.isOpen.mem_nhds hτ
    have heq : act (γ * γ') =ᶠ[nhds τ] act γ ∘ act γ' :=
      Filter.eventually_of_mem hU fun z hz ↦ h.mul γ γ' z hz
    rw [heq.deriv_eq]
    have h1 : DifferentiableAt ℂ (act γ') τ := (h.holo γ').differentiableAt hU
    have h2 : DifferentiableAt ℂ (act γ) (act γ' τ) :=
      (h.holo γ).differentiableAt (h.isOpen.mem_nhds (h.mapsTo γ' hτ))
    exact deriv_comp τ h2 h1

/-- The Möbius action of $\mathrm{SL}_2(\mathbb Z)$ on $\mathbb C$: $\gamma z = (az+b)/(cz+d)$. -/
def moebius (γ : SL(2, ℤ)) (z : ℂ) : ℂ := (γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)

/-- On $\mathbb H$ the Möbius formula is the action of $\mathrm{SL}_2(\mathbb Z)$. -/
theorem moebius_eq_smul (γ : SL(2, ℤ)) (τ : ℍ) : moebius γ τ = ((γ • τ : ℍ) : ℂ) := by
  rw [coe_specialLinearGroup_apply]
  simp [moebius]

/-- **Example 4.24** for $\Gamma(1)$ on $\mathbb H$: $d(\gamma z)/dz = (cz+d)^{-2}$, so the canonical automorphy factor
is $j_\gamma(z) = (cz+d)^{-2}$ and $j_\gamma(z)^k = (cz+d)^{-2k}$. -/
@[kb "milne2017mf" "Section 4, Example 4.24 (pdf p. 59); Remark 4.8 (pdf p. 50)"]
theorem deriv_moebius (γ : SL(2, ℤ)) (τ : ℍ) :
    deriv (moebius γ) τ = ((γ 1 0 : ℂ) * τ + γ 1 1) ^ (-2 : ℤ) := by
  have hev : moebius γ =ᶠ[nhds (τ : ℂ)]
      (fun z ↦ ↑(Matrix.SpecialLinearGroup.mapGL ℝ γ • ofComplex z) : ℂ → ℂ) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    have : ofComplex z = ⟨z, hz⟩ := ofComplex_apply_of_im_pos hz
    rw [this]
    exact moebius_eq_smul γ ⟨z, hz⟩
  have hdet : ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ)).det = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h ⊢
    simp only [Matrix.map_apply]
    exact_mod_cast h
  rw [hev.deriv_eq, UpperHalfPlane.deriv_smul (by simp [hdet])]
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) (τ : ℂ) = (γ 1 0 : ℂ) * τ + γ 1 1 := by
    simp [denom]
  rw [hd, _root_.zpow_neg, zpow_ofNat]
  simp [hdet, div_eq_mul_inv]

/-- $\mathrm{SL}_2(\mathbb Z)$ acts holomorphically on $\mathbb H$ through `moebius`. -/
theorem isHolAction_moebius : IsHolAction {z : ℂ | 0 < z.im} moebius := by
  have key : ∀ (γ : SL(2, ℤ)) (z : ℂ) (hz : 0 < z.im), moebius γ z = ((γ • ⟨z, hz⟩ : ℍ) : ℂ) :=
    fun γ z hz ↦ moebius_eq_smul γ ⟨z, hz⟩
  refine ⟨isOpen_upperHalfPlaneSet, ?_, ?_, ?_, ?_⟩
  · intro γ z hz
    show 0 < (moebius γ z).im
    rw [key γ z hz]
    exact (γ • (⟨z, hz⟩ : ℍ)).im_pos
  · intro z hz
    simp [moebius]
  · intro γ γ' z hz
    have h1 : 0 < (moebius γ' z).im := by
      rw [key γ' z hz]; exact (γ' • (⟨z, hz⟩ : ℍ)).im_pos
    rw [key (γ * γ') z hz, key γ _ h1, mul_smul]
    congr 3
    ext
    simp [key γ' z hz]
  · intro γ z hz
    have hne : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := by
      have := denom_ne_zero_of_im (Matrix.SpecialLinearGroup.mapGL ℝ γ) (z := z) hz.ne'
      simpa [denom] using this
    apply DifferentiableAt.differentiableWithinAt
    unfold moebius
    exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ ↦ (γ 0 0 : ℂ) * z + γ 0 1) z).div
      (by fun_prop) hne

/-- Automorphy factors are invariant under changing `j` on `U`. -/
theorem IsAutomorphyFactor.congr {U : Set ℂ} {act : Γ → ℂ → ℂ} {j j' : Γ → ℂ → ℂ}
    (hj : IsAutomorphyFactor U act j) (hm : ∀ γ, Set.MapsTo (act γ) U U)
    (he : ∀ γ, ∀ τ ∈ U, j γ τ = j' γ τ) : IsAutomorphyFactor U act j' where
  holo γ := (hj.holo γ).congr fun τ hτ ↦ (he γ τ hτ).symm
  cocycle γ γ' τ hτ := by
    rw [← he _ _ hτ, ← he γ _ (hm γ' hτ), ← he γ' τ hτ]
    exact hj.cocycle γ γ' τ hτ

/-- **Example 4.24** for $\Gamma(1)$: $(cz+d)^{-2k}$ is an automorphy factor on $\mathbb H$, for every $k \in \mathbb Z$. -/
@[kb "milne2017mf" "Section 4, Example 4.24 (pdf p. 59)"]
theorem isAutomorphyFactor_denom_zpow (k : ℤ) :
    IsAutomorphyFactor {z : ℂ | 0 < z.im} moebius (fun γ z ↦ ((γ 1 0 : ℂ) * z + γ 1 1) ^ (-2 * k)) := by
  have h := isHolAction_moebius
  have hne : ∀ γ : SL(2, ℤ), ∀ τ ∈ {z : ℂ | 0 < z.im}, (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := by
    intro γ z hz
    have := denom_ne_zero_of_im (Matrix.SpecialLinearGroup.mapGL ℝ γ) (z := z) (ne_of_gt hz)
    simpa [denom] using this
  have hd : ∀ γ : SL(2, ℤ), ∀ τ ∈ {z : ℂ | 0 < z.im}, deriv (moebius γ) τ ≠ 0 := by
    intro γ τ hτ
    have := deriv_moebius γ ⟨τ, hτ⟩
    rw [this]
    exact zpow_ne_zero _ (hne γ τ hτ)
  have hz := (isAutomorphyFactor_deriv h).zpow hd k
  refine hz.congr h.mapsTo fun γ τ hτ ↦ ?_
  have := deriv_moebius γ ⟨τ, hτ⟩
  simp only [this, ← _root_.zpow_mul]

/-- The map $\gamma(\tau, z) = (\gamma\tau, j_\gamma(\tau)z)$ on $U \times \mathbb C$ (proof of Proposition 4.25). -/
def fiberAction (act : Γ → ℂ → ℂ) (j : Γ → ℂ → ℂ) (γ : Γ) (p : ℂ × ℂ) : ℂ × ℂ := (act γ p.1, j γ p.1 * p.2)

/-- **Proposition 4.25**, the correspondence on $U \times \mathbb C$: for a holomorphic action of $\Gamma$ on $U$ and
$j$ holomorphic in $\tau$, the maps $(\tau, z) \mapsto (\gamma\tau, j_\gamma(\tau)z)$ form an action of $\Gamma$ on
$U \times \mathbb C$ if and only if $j$ is an automorphy factor with $j_1 = 1$ on $U$. -/
@[kb "milne2017mf" "Section 4, Proposition 4.25 and its proof (pdf p. 59)"]
theorem isAutomorphyFactor_iff_fiberAction {U : Set ℂ} {act : Γ → ℂ → ℂ} (h : IsHolAction U act)
    {j : Γ → ℂ → ℂ} (hj : ∀ γ, DifferentiableOn ℂ (j γ) U) :
    (IsAutomorphyFactor U act j ∧ ∀ τ ∈ U, j 1 τ = 1) ↔
      ((∀ p : ℂ × ℂ, p.1 ∈ U → fiberAction act j 1 p = p) ∧
        ∀ γ γ', ∀ p : ℂ × ℂ, p.1 ∈ U →
          fiberAction act j (γ * γ') p = fiberAction act j γ (fiberAction act j γ' p)) := by
  constructor
  · rintro ⟨hf, h1⟩
    refine ⟨fun p hp ↦ ?_, fun γ γ' p hp ↦ ?_⟩
    · simp [fiberAction, h.one _ hp, h1 _ hp]
    · simp only [fiberAction, Prod.mk.injEq]
      exact ⟨h.mul γ γ' _ hp, by rw [hf.cocycle γ γ' _ hp, mul_assoc]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨hj, fun γ γ' τ hτ ↦ ?_⟩, fun τ hτ ↦ ?_⟩
    · have := congrArg Prod.snd (h2 γ γ' (τ, 1) hτ)
      simpa [fiberAction] using this
    · have := congrArg Prod.snd (h1 (τ, 1) hτ)
      simpa [fiberAction] using this

omit [Group Γ] in
/-- **Sections** (pp. 59–60): a section $F(\tau) = (\tau, f(\tau))$ of $U \times \mathbb C$ commutes with the action
$\gamma(\tau, z) = (\gamma\tau, j_\gamma(\tau)z)$ if and only if $f(\gamma\tau) = j_\gamma(\tau)f(\tau)$; with
$j_\gamma(\tau) = (c\tau+d)^{2k}$ this is condition 4.5(a). -/
@[kb "milne2017mf" "Section 4, sections of line bundles, after Remark 4.26 (pdf p. 60)"]
theorem fiberAction_section_iff {U : Set ℂ} (act : Γ → ℂ → ℂ) (j : Γ → ℂ → ℂ) (f : ℂ → ℂ) :
    (∀ γ, ∀ τ ∈ U, (act γ τ, f (act γ τ)) = fiberAction act j γ (τ, f τ)) ↔
      ∀ γ, ∀ τ ∈ U, f (act γ τ) = j γ τ * f τ := by
  simp [fiberAction]

/-- **Remark 4.26** (named statement): every holomorphic line bundle on $\mathbb H$ is trivial. A holomorphic line
bundle $E$ over $\mathbb H$ (fibres $\mathbb C$, complex-analytic structure group) is trivial exactly when it has a
holomorphic section with no zeros; that is the form stated here. Not proved here (it follows from the vanishing of
$H^1(\mathbb H, \mathcal O^\times)$, Oka–Grauert, or from $\mathbb H$ being a contractible Stein manifold). -/
@[kb "milne2017mf" "Section 4, Remark 4.26 (pdf p. 59)"]
structure LineBundlesOnHTrivial : Prop where
  trivial : ∀ (E : ℍ → Type) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
    [TopologicalSpace (Bundle.TotalSpace ℂ E)] [FiberBundle ℂ E] [VectorBundle ℂ ℂ E]
    [ContMDiffVectorBundle ω ℂ E 𝓘(ℂ)],
    ∃ s : (x : ℍ) → E x, ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω (fun x ↦ (⟨x, s x⟩ : Bundle.TotalSpace ℂ E)) ∧
      ∀ x, s x ≠ 0

end ModularFormsKB.Milne
