/-
# The Petersson inner product on $\Gamma_0(4)$, half-integral weight

Groundwork for `KohnenZagier` (Kohnen–Zagier 1981 `kohnenzagier1981`, Thm. 1).

For $f, g : \mathbb H \to \mathbb C$ and $k \in \mathbb N$ we set, as in Kohnen–Zagier,
$$\langle f, g\rangle = \frac16\int_{\Gamma_0(4)\backslash\mathbb H}\overline{f(\tau)}\,g(\tau)\,v^{k+1/2}\,\frac{du\,dv}{v^2}
  \qquad(\tau = u + iv),$$
computed as $\tfrac16\sum_{\gamma}\int_{\mathcal F}$ over the six right coset representatives `gamma0FourReps` of
$\Gamma_0(4)$ in $\mathrm{SL}_2(\mathbb Z)$, with $\mathcal F$ = `ModularGroup.fd` (`peterssonFour`). The factor $\tfrac16$ is
$1/[\mathrm{SL}_2(\mathbb Z):\Gamma_0(4)]$. By definition `peterssonFour k g g = peterssonNormSqFour k g`, the normalization of
the existing `KohnenZagier` statement. The product is conjugate-linear in the first and linear in the second argument.

Proved here, for an arbitrary list of representatives (`peterssonReps`), with no integrability hypothesis unless stated:
- hermitian symmetry $\langle g, f\rangle = \overline{\langle f, g\rangle}$ (`peterssonReps_conj_symm`);
- $\langle f, cg\rangle = c\langle f, g\rangle$ and $\langle cf, g\rangle = \bar c\langle f, g\rangle$;
- additivity in each argument, given integrability on $\mathcal F$ of each term (`peterssonReps_add_right`);
- $\langle f, f\rangle$ is a nonnegative real number (`peterssonReps_self_eq_ofReal`, `peterssonReps_self_re_nonneg`).

Convergence for cusp forms and definiteness are in `ModularFormsKB/HalfIntegral/Abstract/PeterssonConvergence.lean`.
-/
import ModularFormsKB.HalfIntegral.Abstract.Kohnen

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup MeasureTheory
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- The integrand of `peterssonReps` for one representative $\gamma$:
$\overline{f(\gamma\tau)}\,g(\gamma\tau)\,\operatorname{Im}(\gamma\tau)^w$. -/
noncomputable def peterssonIntegrand (γ : SL(2, ℤ)) (w : ℝ) (f g : ℍ → ℂ) (τ : ℍ) : ℂ :=
  (starRingEnd ℂ) (f (γ • τ)) * g (γ • τ) * (((γ • τ).im ^ w : ℝ) : ℂ)

theorem peterssonReps_eq (R : List SL(2, ℤ)) (w : ℝ) (f g : ℍ → ℂ) :
    peterssonReps R w f g = (R.map fun γ ↦ ∫ τ in ModularGroup.fd, peterssonIntegrand γ w f g τ).sum := rfl

/-- **The Petersson product on $\Gamma_0(4)$** in Kohnen–Zagier's normalization:
$\langle f, g\rangle = \tfrac16\int_{\Gamma_0(4)\backslash\mathbb H}\overline f\,g\,v^{k+1/2}\,d\mu$. -/
noncomputable def peterssonFour (k : ℕ) (f g : ℍ → ℂ) : ℂ :=
  (1 / 6 : ℂ) * peterssonReps gamma0FourReps ((k : ℝ) + 1 / 2) f g

/-- **The Petersson product on $\mathrm{SL}_2(\mathbb Z)$**, weight $2k$, unnormalized:
$\langle F, G\rangle = \int_{\mathrm{SL}_2(\mathbb Z)\backslash\mathbb H}\overline F\,G\,v^{2k}\,d\mu$. -/
noncomputable def peterssonOne (k : ℕ) (F G : ℍ → ℂ) : ℂ :=
  peterssonReps [1] (2 * k) F G

/-- The Petersson product of $g$ with itself is the norm of the `KohnenZagier` statement. -/
theorem peterssonFour_self (k : ℕ) (g : ℍ → ℂ) : peterssonFour k g g = peterssonNormSqFour k g := rfl

theorem peterssonOne_self (k : ℕ) (F : ℍ → ℂ) : peterssonOne k F F = peterssonNormSqOne k F := rfl

theorem peterssonIntegrand_conj (γ : SL(2, ℤ)) (w : ℝ) (f g : ℍ → ℂ) (τ : ℍ) :
    peterssonIntegrand γ w g f τ = (starRingEnd ℂ) (peterssonIntegrand γ w f g τ) := by
  simp only [peterssonIntegrand, map_mul, conj_conj, conj_ofReal]
  ring

/-- **Hermitian symmetry:** $\langle g, f\rangle = \overline{\langle f, g\rangle}$. -/
theorem peterssonReps_conj_symm (R : List SL(2, ℤ)) (w : ℝ) (f g : ℍ → ℂ) :
    peterssonReps R w g f = (starRingEnd ℂ) (peterssonReps R w f g) := by
  rw [peterssonReps_eq, peterssonReps_eq, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun γ _ ↦ ?_
  simp only [Function.comp_apply]
  rw [show (fun τ ↦ peterssonIntegrand γ w g f τ) = fun τ ↦ (starRingEnd ℂ) (peterssonIntegrand γ w f g τ) from
    funext (peterssonIntegrand_conj γ w f g)]
  exact integral_conj

theorem peterssonFour_conj_symm (k : ℕ) (f g : ℍ → ℂ) :
    peterssonFour k g f = (starRingEnd ℂ) (peterssonFour k f g) := by
  rw [peterssonFour, peterssonFour, peterssonReps_conj_symm, map_mul]
  congr 1
  simp [map_ofNat]

/-- **Linearity in the second argument (scalars).** -/
theorem peterssonReps_smul_right (R : List SL(2, ℤ)) (w : ℝ) (f g : ℍ → ℂ) (c : ℂ) :
    peterssonReps R w f (c • g) = c * peterssonReps R w f g := by
  rw [peterssonReps_eq, peterssonReps_eq, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun γ _ ↦ ?_
  rw [← integral_const_mul]
  congr 1
  funext τ
  simp only [peterssonIntegrand, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Conjugate-linearity in the first argument (scalars).** -/
theorem peterssonReps_smul_left (R : List SL(2, ℤ)) (w : ℝ) (f g : ℍ → ℂ) (c : ℂ) :
    peterssonReps R w (c • f) g = (starRingEnd ℂ) c * peterssonReps R w f g := by
  rw [peterssonReps_conj_symm, peterssonReps_smul_right, map_mul, ← peterssonReps_conj_symm]

/-- **Additivity in the second argument**, when every term is integrable on the fundamental domain. -/
theorem peterssonReps_add_right (R : List SL(2, ℤ)) (w : ℝ) (f g h : ℍ → ℂ)
    (hg : ∀ γ ∈ R, IntegrableOn (peterssonIntegrand γ w f g) ModularGroup.fd)
    (hh : ∀ γ ∈ R, IntegrableOn (peterssonIntegrand γ w f h) ModularGroup.fd) :
    peterssonReps R w f (g + h) = peterssonReps R w f g + peterssonReps R w f h := by
  rw [peterssonReps_eq, peterssonReps_eq, peterssonReps_eq, ← List.sum_map_add]
  congr 1
  refine List.map_congr_left fun γ hγ ↦ ?_
  rw [← integral_add (hg γ hγ) (hh γ hγ)]
  congr 1
  funext τ
  simp only [peterssonIntegrand, Pi.add_apply]
  ring

theorem integrableOn_peterssonIntegrand_swap {γ : SL(2, ℤ)} {w : ℝ} {f g : ℍ → ℂ} {s : Set ℍ}
    (h : IntegrableOn (peterssonIntegrand γ w f g) s) : IntegrableOn (peterssonIntegrand γ w g f) s := by
  have := (conjCLE.toContinuousLinearMap).integrable_comp h
  rw [show peterssonIntegrand γ w g f = fun τ ↦ (starRingEnd ℂ) (peterssonIntegrand γ w f g τ) from
    funext (peterssonIntegrand_conj γ w f g)]
  simpa [IntegrableOn] using this

/-- **Additivity in the first argument**, when every term is integrable on the fundamental domain. -/
theorem peterssonReps_add_left (R : List SL(2, ℤ)) (w : ℝ) (f g h : ℍ → ℂ)
    (hf : ∀ γ ∈ R, IntegrableOn (peterssonIntegrand γ w f h) ModularGroup.fd)
    (hg : ∀ γ ∈ R, IntegrableOn (peterssonIntegrand γ w g h) ModularGroup.fd) :
    peterssonReps R w (f + g) h = peterssonReps R w f h + peterssonReps R w g h := by
  have hf' : ∀ γ ∈ R, IntegrableOn (peterssonIntegrand γ w h f) ModularGroup.fd := fun γ hγ ↦
    integrableOn_peterssonIntegrand_swap (hf γ hγ)
  have hg' : ∀ γ ∈ R, IntegrableOn (peterssonIntegrand γ w h g) ModularGroup.fd := fun γ hγ ↦
    integrableOn_peterssonIntegrand_swap (hg γ hγ)
  rw [peterssonReps_conj_symm, peterssonReps_add_right R w h f g hf' hg', map_add,
    ← peterssonReps_conj_symm, ← peterssonReps_conj_symm]

/-- The self-integrand is the real number $|f(\gamma\tau)|^2\operatorname{Im}(\gamma\tau)^w$. -/
theorem peterssonIntegrand_self (γ : SL(2, ℤ)) (w : ℝ) (f : ℍ → ℂ) (τ : ℍ) :
    peterssonIntegrand γ w f f τ = ((‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ w : ℝ) : ℂ) := by
  rw [peterssonIntegrand, mul_comm ((starRingEnd ℂ) _), mul_conj, normSq_eq_norm_sq]
  push_cast
  ring

/-- **$\langle f, f\rangle$ is real:** it is the cast of
$\sum_\gamma\int_{\mathcal F}|f(\gamma\tau)|^2\operatorname{Im}(\gamma\tau)^w\,d\mu$. -/
theorem peterssonReps_self_eq_ofReal (R : List SL(2, ℤ)) (w : ℝ) (f : ℍ → ℂ) :
    peterssonReps R w f f =
      (((R.map fun γ ↦ ∫ τ in ModularGroup.fd, ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ w).sum : ℝ) : ℂ) := by
  rw [peterssonReps_eq, ← Complex.ofRealHom_eq_coe, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun γ _ ↦ ?_
  simp only [Function.comp_apply, Complex.ofRealHom_eq_coe, peterssonIntegrand_self]
  exact integral_ofReal

theorem peterssonReps_self_nonneg (R : List SL(2, ℤ)) (w : ℝ) (f : ℍ → ℂ) :
    0 ≤ (R.map fun γ ↦ ∫ τ in ModularGroup.fd, ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ w).sum := by
  refine List.sum_nonneg fun x hx ↦ ?_
  obtain ⟨γ, -, rfl⟩ := List.mem_map.1 hx
  exact integral_nonneg fun τ ↦ mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (γ • τ).im_pos.le _)

theorem peterssonReps_self_re_nonneg (R : List SL(2, ℤ)) (w : ℝ) (f : ℍ → ℂ) :
    0 ≤ (peterssonReps R w f f).re := by
  rw [peterssonReps_self_eq_ofReal, ofReal_re]
  exact peterssonReps_self_nonneg R w f

theorem peterssonReps_self_im (R : List SL(2, ℤ)) (w : ℝ) (f : ℍ → ℂ) :
    (peterssonReps R w f f).im = 0 := by
  rw [peterssonReps_self_eq_ofReal, ofReal_im]

/-- **$\langle g, g\rangle \ge 0$** in Kohnen–Zagier's normalization (as a complex number: real part $\ge 0$, imaginary part $0$). -/
theorem peterssonNormSqFour_nonneg (k : ℕ) (g : ℍ → ℂ) :
    0 ≤ (peterssonNormSqFour k g).re ∧ (peterssonNormSqFour k g).im = 0 := by
  rw [← peterssonFour_self, peterssonFour, peterssonReps_self_eq_ofReal]
  refine ⟨?_, ?_⟩
  · rw [show (1 / 6 : ℂ) = ((1 / 6 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_mul, ofReal_re]
    exact mul_nonneg (by norm_num) (peterssonReps_self_nonneg _ _ g)
  · rw [show (1 / 6 : ℂ) = ((1 / 6 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_mul, ofReal_im]

theorem peterssonNormSqOne_nonneg (k : ℕ) (F : ℍ → ℂ) :
    0 ≤ (peterssonNormSqOne k F).re ∧ (peterssonNormSqOne k F).im = 0 :=
  ⟨peterssonReps_self_re_nonneg _ _ F, peterssonReps_self_im _ _ F⟩

end ModularFormsKB.HalfIntegral
