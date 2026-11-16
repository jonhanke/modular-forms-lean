/-
# The plus space as an eigenspace of $W(4)U(4)$, and Kohnen's projection

Level $4$, trivial character, weight $k+\tfrac12$, relative to an
abstract multiplier system `M` (meant to be the theta multiplier).

**Operators** (on functions $\mathbb H \to \mathbb C$):
- $(f|U(4))(\tau) = \tfrac14\sum_{j=0}^{3} f\big(\tfrac{\tau+j}4\big)$ (`kohnenU4`); on $q$-expansions it is $\sum a(4n)q^n$;
- $(g|W(4))(\tau) = (-2i\tau)^{-(k+1/2)}\,g(-1/4\tau)$ (`kohnenW4`), principal branch ($\operatorname{Re}(-2i\tau) > 0$);
- $L = W(4)\circ U(4)$, $f \mapsto (f|U(4))|W(4)$ (`kohnenL`).

With these normalizations $\theta|W(4) = \theta$ (`theta_fricke`) and $\theta|U(4) = \theta$, so $\theta|L = \theta$.

**Eigenvalues** (Kohnen 1980 `kohnen1980`, Prop. 2 [unverified], in our normalization): on $S_{k+1/2}(4)$, $L$ satisfies
$(L-\alpha)(L-\beta) = 0$ with $\alpha = (-1)^{\lfloor (k+1)/2\rfloor}2^k$ (`kohnenAlpha`) and $\beta = -\alpha/2$, and the plus space
is the $\alpha$-eigenspace. Kohnen's constants differ by his normalization of $W(4)$; ours were checked numerically
(2026-10-28): $\theta(\tau)E_4(4\tau)$ and $\theta(\tau)E_6(4\tau)$ (plus forms, $k = 4, 6$) have $L$-eigenvalue $16$ and $-64$,
and on $M_{5/2}(4) = \langle\theta^5, \theta F\rangle$ ($F = \sum_{n \text{ odd}}\sigma_1(n)q^n$) $L$ has eigenvalues $-4$ and $2$.
This is the named input `KohnenPlusEigen`.

**Proved here** from `KohnenPlusEigen`: Kohnen's projection $\mathrm{pr} = \tfrac13 + \tfrac{2}{3\alpha}L$ (`kohnenPr`) maps
$S_{k+1/2}(4)$ onto $S^+_{k+1/2}(4)$ and is the identity there (`kohnenPr_mem_plus`, `kohnenPr_of_mem_plus`,
`kohnenPr_idem`); it is a linear map (`kohnenPrLin`) whose range is the plus space (`range_kohnenPrLin`). Its kernel is
the $\beta$-eigenspace (`kohnenPr_eq_zero_iff`). The plus space is the set of cusp forms whose coefficients satisfy the
plus condition (definition of `plusCuspForms`), so `KohnenPlusEigen.plus_iff` is the characterization by coefficients.
-/
import ModularFormsKB.HalfIntegral.Abstract.Kohnen

namespace ModularFormsKB.HalfIntegral

open Complex
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- The point $(\tau + j)/4$ of $\mathbb H$. -/
noncomputable def quarterPt (j : ℕ) (τ : ℍ) : ℍ :=
  ⟨((τ : ℂ) + j) / 4, by
    simpa using div_pos τ.im_pos (by norm_num : (0 : ℝ) < 4)⟩

/-- The point $-1/(4\tau)$ of $\mathbb H$. -/
noncomputable def frickePt (τ : ℍ) : ℍ :=
  ⟨-1 / (4 * (τ : ℂ)), by
    have h1 := τ.im_pos
    have h2 : 0 < Complex.normSq (4 * (τ : ℂ)) :=
      Complex.normSq_pos.2 (mul_ne_zero (by norm_num) τ.ne_zero)
    rw [Complex.div_im]
    simp only [Complex.neg_re, Complex.one_re, Complex.neg_im, Complex.one_im, neg_zero, zero_mul, zero_div,
      Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_sub, neg_mul, one_mul, add_zero]
    rw [neg_div, neg_neg]
    exact div_pos (by simpa using h1) h2⟩

@[simp] theorem coe_frickePt (τ : ℍ) : ((frickePt τ : ℍ) : ℂ) = -1 / (4 * (τ : ℂ)) := rfl

/-- $(f|U(4))(\tau) = \tfrac14\sum_{j=0}^3 f((\tau+j)/4)$. -/
noncomputable def kohnenU4 (f : ℍ → ℂ) : ℍ → ℂ :=
  fun τ ↦ (1 / 4 : ℂ) * ∑ j ∈ Finset.range 4, f (quarterPt j τ)

/-- $(g|W(4))(\tau) = (-2i\tau)^{-(k+1/2)}g(-1/4\tau)$. -/
noncomputable def kohnenW4 (k : ℕ) (g : ℍ → ℂ) : ℍ → ℂ :=
  fun τ ↦ (-2 * I * τ) ^ (-((k : ℂ) + 1 / 2)) * g (frickePt τ)

/-- **Kohnen's operator** $L = W(4)U(4)$: $f \mapsto (f|U(4))|W(4)$. -/
noncomputable def kohnenL (k : ℕ) (f : ℍ → ℂ) : ℍ → ℂ := kohnenW4 k (kohnenU4 f)

/-- **The plus-space eigenvalue** $\alpha_k = (-1)^{\lfloor (k+1)/2\rfloor}2^k$ of $L$ (our normalization). -/
noncomputable def kohnenAlpha (k : ℕ) : ℂ := (-1) ^ ((k + 1) / 2) * 2 ^ k

theorem kohnenAlpha_ne_zero (k : ℕ) : kohnenAlpha k ≠ 0 := by
  unfold kohnenAlpha
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))

/-- $L$ is $\mathbb C$-linear on functions. -/
noncomputable def kohnenLLin (k : ℕ) : (ℍ → ℂ) →ₗ[ℂ] (ℍ → ℂ) where
  toFun := kohnenL k
  map_add' f g := by
    funext τ
    simp only [kohnenL, kohnenW4, kohnenU4, Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c f := by
    funext τ
    simp only [kohnenL, kohnenW4, kohnenU4, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

@[simp] theorem kohnenLLin_apply (k : ℕ) (f : ℍ → ℂ) : kohnenLLin k f = kohnenL k f := rfl

/-- **The plus space is the $\alpha$-eigenspace of $W(4)U(4)$** (Kohnen 1980 `kohnen1980`, Prop. 2 [unverified]; constants
in our normalization, checked numerically, see the module docstring): $L$ preserves $S_{k+1/2}(4)$, satisfies
$(L-\alpha)(L-\beta) = 0$ there with $\beta = -\alpha/2$, i.e. $L^2 = \tfrac\alpha2 L + \tfrac{\alpha^2}2$, and
$f \in S^+_{k+1/2}(4) \iff Lf = \alpha f$. -/
@[kb "kohnen1980" "Prop. 2: S⁺_{k+1/2}(4) is the α-eigenspace of W(4)U(4), other eigenvalue -α/2 [unverified]"]
structure KohnenPlusEigen (M : MultiplierSystem) (k : ℕ) : Prop where
  maps : ∀ f ∈ M.cuspForms k 1 1, kohnenL k f ∈ M.cuspForms k 1 1
  quadratic : ∀ f ∈ M.cuspForms k 1 1,
    kohnenL k (kohnenL k f) = (kohnenAlpha k / 2) • kohnenL k f + (kohnenAlpha k ^ 2 / 2) • f
  plus_iff : ∀ f ∈ M.cuspForms k 1 1, f ∈ M.plusCuspForms k 1 1 ↔ kohnenL k f = kohnenAlpha k • f

/-- **Kohnen's projection** $\mathrm{pr} = \tfrac13 + \tfrac2{3\alpha}L$ (Kohnen 1980 `kohnen1980`, Prop. 3 [unverified]). -/
noncomputable def kohnenPr (k : ℕ) (f : ℍ → ℂ) : ℍ → ℂ :=
  (1 / 3 : ℂ) • f + (2 / (3 * kohnenAlpha k)) • kohnenL k f

variable {M : MultiplierSystem} {k : ℕ}

private theorem kohnenL_kohnenPr (f : ℍ → ℂ) :
    kohnenL k (kohnenPr k f) = (1 / 3 : ℂ) • kohnenL k f + (2 / (3 * kohnenAlpha k)) • kohnenL k (kohnenL k f) := by
  have := (kohnenLLin k).map_add ((1 / 3 : ℂ) • f) ((2 / (3 * kohnenAlpha k)) • kohnenL k f)
  simp only [kohnenLLin_apply, map_smul] at this
  rw [kohnenPr]
  exact this

theorem kohnenPr_mem_cusp (h : KohnenPlusEigen M k) {f : ℍ → ℂ} (hf : f ∈ M.cuspForms k 1 1) :
    kohnenPr k f ∈ M.cuspForms k 1 1 :=
  (M.cuspForms k 1 1).add_mem ((M.cuspForms k 1 1).smul_mem _ hf) ((M.cuspForms k 1 1).smul_mem _ (h.maps f hf))

/-- **$\mathrm{pr}$ maps $S_{k+1/2}(4)$ into the plus space.** -/
@[kb "kohnen1980" "Prop. 3: Kohnen's projection pr maps S_{k+1/2}(4) onto S⁺_{k+1/2}(4) [unverified]"]
theorem kohnenPr_mem_plus (h : KohnenPlusEigen M k) {f : ℍ → ℂ} (hf : f ∈ M.cuspForms k 1 1) :
    kohnenPr k f ∈ M.plusCuspForms k 1 1 := by
  rw [h.plus_iff _ (kohnenPr_mem_cusp h hf), kohnenL_kohnenPr, h.quadratic f hf, kohnenPr]
  have hα := kohnenAlpha_ne_zero k
  funext τ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **$\mathrm{pr}$ is the identity on the plus space.** -/
theorem kohnenPr_of_mem_plus (h : KohnenPlusEigen M k) {f : ℍ → ℂ} (hf : f ∈ M.plusCuspForms k 1 1) :
    kohnenPr k f = f := by
  have hL := (h.plus_iff f (M.plusCuspForms_le k 1 1 hf)).1 hf
  rw [kohnenPr, hL]
  have hα := kohnenAlpha_ne_zero k
  funext τ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **$\mathrm{pr}$ is idempotent** on $S_{k+1/2}(4)$. -/
theorem kohnenPr_idem (h : KohnenPlusEigen M k) {f : ℍ → ℂ} (hf : f ∈ M.cuspForms k 1 1) :
    kohnenPr k (kohnenPr k f) = kohnenPr k f :=
  kohnenPr_of_mem_plus h (kohnenPr_mem_plus h hf)

/-- **The kernel of $\mathrm{pr}$ is the $\beta = -\alpha/2$ eigenspace of $L$.** -/
theorem kohnenPr_eq_zero_iff (f : ℍ → ℂ) :
    kohnenPr k f = 0 ↔ kohnenL k f = (-(kohnenAlpha k) / 2) • f := by
  have hα := kohnenAlpha_ne_zero k
  constructor
  · intro h0
    funext τ
    have := congrFun h0 τ
    simp only [kohnenPr, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    field_simp at this
    linear_combination (1 / 2 : ℂ) * this
  · intro h1
    funext τ
    have := congrFun h1 τ
    simp only [kohnenPr, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    rw [this]
    field_simp
    ring

/-- **Kohnen's projection as a linear map** $S_{k+1/2}(4) \to S^+_{k+1/2}(4)$. -/
noncomputable def kohnenPrLin (h : KohnenPlusEigen M k) : M.cuspForms k 1 1 →ₗ[ℂ] M.plusCuspForms k 1 1 where
  toFun f := ⟨kohnenPr k f, kohnenPr_mem_plus h f.2⟩
  map_add' f g := by
    apply Subtype.ext
    simp only [Submodule.coe_add, kohnenPr]
    rw [show kohnenL k (↑f + ↑g) = kohnenL k f + kohnenL k g from (kohnenLLin k).map_add f g]
    simp only [smul_add]
    abel
  map_smul' c f := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, kohnenPr, RingHom.id_apply]
    rw [show kohnenL k (c • (f : ℍ → ℂ)) = c • kohnenL k f from (kohnenLLin k).map_smul c f]
    simp only [smul_add, smul_comm c]

/-- **The range of Kohnen's projection is the whole plus space.** -/
theorem range_kohnenPrLin (h : KohnenPlusEigen M k) : LinearMap.range (kohnenPrLin h) = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro g
  refine ⟨⟨g, M.plusCuspForms_le k 1 1 g.2⟩, Subtype.ext ?_⟩
  exact kohnenPr_of_mem_plus h g.2

end ModularFormsKB.HalfIntegral
