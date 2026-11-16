/-
# The Rankin kernel after the Fricke involution $W_L$: $f|W_{4N}$ and $\theta_{\bar\psi}(4N\cdot)$

Loose end LE-MF-0256.

With $L = 16Ntr^2$ (`rankinLevel N t r`), $W_Lz = -1/(Lz)$ and $G_\psi(z) = f(z)\overline{\theta_{\psi,t}(z)}y^{(k+\nu+1)/2}$
(`rankinKernel`), the kernel $G_\psi(W_Lz)$ of the Fricke-transformed dual integral `frickeDualIntegral` is computed
(`rankinKernel_fricke`) for $N, t \ge 1$ and $\psi$ primitive modulo $r \ge 1$:
$$G_\psi(W_Lz) = (-2iNw)^{k+1/2}\,(f|W_{4N})(w)\cdot
  \overline{\frac r{\tau(\psi)}(-2iu)^{1/2}(2ru)^\nu\,\theta_{\bar\psi}(u)}\cdot
  \Big(\frac{y}{L|z|^2}\Big)^{(k+\nu+1)/2},\qquad w = 4tr^2z,\ u = 4Nz$$
(`frickeKernel`). Here $W_Lz = W_{4N}(4tr^2z)$ gives the first factor (`frickeHalf`, row 5), and
$t\,W_Lz = -1/(4r^2u)$ with the inversion formula of the twisted theta series at the cusp $0$
(`thetaTwist_inversion`, from `ThetaCuspZero`, row 6) gives the second.

So Shimura's Fricke-side identity `ShimuraFrickeUnfolding` follows from the same identity with the kernel
`frickeKernel` (`ShimuraFrickeKernelUnfolding`, `shimuraFrickeUnfolding_of_kernel`). In the new input there is no
Fricke involution left: it is the unfolding of $(f|W_{4N})(4tr^2z)\,\overline{\theta_{\bar\psi}(4Nz)}$ (a cusp form in
$S_{k+1/2}(4N,\bar\chi(\tfrac{4N}\cdot))$, by `frickeHalf_mem_cuspForms`, times a theta series) against the Eisenstein
series at $\infty$ of `DualFricke.eisensteinPrimSum` over $\Gamma_0(L)\backslash\mathbb H$.
-/
import ModularFormsKB.HalfIntegral.Rankin.FrickeHalf
import ModularFormsKB.HalfIntegral.Rankin.FrickeReduction
import ModularFormsKB.HalfIntegral.Rankin.ThetaCuspZero

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup MeasureTheory
open scoped Real

local notation "ℍ" => UpperHalfPlane

namespace FrickeKernel

lemma thetaTwist_t {r : ℕ} (ψ : DirichletCharacter ℂ r) (t : ℕ) (z : ℂ) :
    thetaTwist ψ t z = thetaTwist ψ 1 (t * z) := by
  unfold thetaTwist
  refine tsum_congr fun n ↦ ?_
  have : 2 * (π : ℂ) * I * (t : ℂ) * (n : ℂ) ^ 2 * z =
      2 * π * I * ((1 : ℕ) : ℂ) * (n : ℂ) ^ 2 * ((t : ℂ) * z) := by push_cast; ring
  rw [this]

/-- **The twisted theta series at the cusp 0, both parities:**
$\theta_\psi(-1/(4r^2w)) = r\,\tau(\psi)^{-1}(-2iw)^{1/2}(2rw)^\nu\,\theta_{\overline\psi}(w)$ for $\psi$ primitive
(`thetaTwist_inversion_even`, `thetaTwist_inversion_odd`). -/
theorem thetaTwist_inversion {r : ℕ} [NeZero r] {ψ : DirichletCharacter ℂ r} (hψ : ψ.IsPrimitive) {w : ℂ}
    (hw : 0 < w.im) :
    thetaTwist ψ 1 (-1 / (4 * (r : ℂ) ^ 2 * w)) =
      (r : ℂ) / gaussAt r ψ 1 * (-2 * I * w) ^ (1 / 2 : ℂ) * (2 * r * w) ^ charParity ψ *
        thetaTwist ψ⁻¹ 1 w := by
  rcases ψ.even_or_odd with h | h
  · have h' : ψ (-1) = 1 := h
    have hp : charParity ψ = 0 := by simp [charParity, h']
    rw [hp, pow_zero, mul_one]
    exact ThetaCuspZero.thetaTwist_inversion_even hψ h' hw
  · have h' : ψ (-1) = -1 := h
    have hm1 : (-1 : ℂ) ≠ 1 := by norm_num
    have hp : charParity ψ = 1 := by simp [charParity, h', hm1]
    rw [hp, pow_one]
    exact ThetaCuspZero.thetaTwist_inversion_odd hψ h' hw

lemma im_fricke {L : ℕ} [NeZero L] (z : ℍ) :
    (TauCeti.frickeGL ℝ L • z).im = z.im / ((L : ℝ) * Complex.normSq (z : ℂ)) := by
  have h := DualFricke.coe_fricke_smul (L := L) z
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hz : Complex.normSq (z : ℂ) ≠ 0 := (Complex.normSq_pos.mpr z.ne_zero).ne'
  rw [← UpperHalfPlane.coe_im, h]
  simp only [Complex.div_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, Complex.normSq_mul,
    Complex.normSq_natCast, UpperHalfPlane.coe_im, UpperHalfPlane.coe_re]
  field_simp
  ring

end FrickeKernel

open FrickeKernel FrickeHalf

/-- **The Rankin kernel after $W_L$**, $L = 16Ntr^2$, $w = 4tr^2z$, $u = 4Nz$:
$(-2iNw)^{k+1/2}(f|W_{4N})(w)\,\overline{r\tau(\psi)^{-1}(-2iu)^{1/2}(2ru)^\nu\theta_{\bar\psi}(u)}\,
(y/(L|z|^2))^{(k+\nu+1)/2}$. -/
noncomputable def frickeKernel (k N t : ℕ) {r : ℕ} (ψ : DirichletCharacter ℂ r) (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  (-2 * I * (N * (((4 * t * r ^ 2 : ℕ) : ℂ) * z))) ^ ((k : ℂ) + 1 / 2) *
      frickeHalf k N f (scalePt (4 * t * r ^ 2) z) *
    (starRingEnd ℂ) ((r : ℂ) / gaussAt r ψ 1 * (-2 * I * (4 * N * (z : ℂ))) ^ (1 / 2 : ℂ) *
      (2 * r * (4 * N * (z : ℂ))) ^ charParity ψ * thetaTwist ψ⁻¹ 1 (4 * N * (z : ℂ))) *
    (((z.im / ((rankinLevel N t r : ℝ) * Complex.normSq (z : ℂ))) ^
      (((k + charParity ψ + 1 : ℕ) : ℝ) / 2) : ℝ) : ℂ)

/-- **The Rankin kernel at $W_Lz$** for $N, t \ge 1$ and $\psi$ primitive modulo $r \ge 1$:
$G_\psi(W_Lz) = $ `frickeKernel k N t ψ f z`. -/
theorem rankinKernel_fricke {k N t r : ℕ} (hN : 0 < N) (ht : 1 ≤ t) [NeZero r] [NeZero (rankinLevel N t r)]
    {ψ : DirichletCharacter ℂ r} (hψ : ψ.IsPrimitive) (f : ℍ → ℂ) (z : ℍ) :
    rankinKernel k ψ t f (TauCeti.frickeGL ℝ (rankinLevel N t r) • z) = frickeKernel k N t ψ f z := by
  have hr : (r : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne r
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hm : 0 < 4 * t * r ^ 2 := by
    have := Nat.pos_of_ne_zero (NeZero.ne r); positivity
  set w := scalePt (4 * t * r ^ 2) z with hw
  have hwc : (w : ℂ) = ((4 * t * r ^ 2 : ℕ) : ℂ) * z := coe_scalePt hm z
  -- the form factor
  have hpt : TauCeti.frickeGL ℝ (rankinLevel N t r) • z = frickePt (scalePt N w) := by
    ext
    rw [DualFricke.coe_fricke_smul, coe_frickePt, coe_scalePt hN, hwc]
    unfold rankinLevel
    push_cast
    field_simp
    ring
  have hX : (-2 * I * (N * (((4 * t * r ^ 2 : ℕ) : ℂ) * z))) ≠ 0 := by
    have : ((4 * t * r ^ 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    exact mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) (mul_ne_zero hN' (mul_ne_zero this hz))
  have hf : f (TauCeti.frickeGL ℝ (rankinLevel N t r) • z) =
      (-2 * I * (N * (((4 * t * r ^ 2 : ℕ) : ℂ) * z))) ^ ((k : ℂ) + 1 / 2) * frickeHalf k N f w := by
    rw [(frickeHalf_eq hN f w).1, hwc, hpt, ← mul_assoc, Complex.cpow_neg, mul_inv_cancel₀, one_mul]
    exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])).mpr hX
  -- the theta factor
  have hu : 0 < (4 * N * (z : ℂ)).im := by
    have : (4 * N * (z : ℂ)).im = 4 * N * z.im := by simp
    rw [this]; have := z.im_pos; positivity
  have hθ : thetaTwist ψ t ((TauCeti.frickeGL ℝ (rankinLevel N t r) • z : ℍ) : ℂ) =
      (r : ℂ) / gaussAt r ψ 1 * (-2 * I * (4 * N * (z : ℂ))) ^ (1 / 2 : ℂ) *
        (2 * r * (4 * N * (z : ℂ))) ^ charParity ψ * thetaTwist ψ⁻¹ 1 (4 * N * (z : ℂ)) := by
    rw [thetaTwist_t, DualFricke.coe_fricke_smul, ← thetaTwist_inversion hψ hu]
    congr 1
    unfold rankinLevel
    push_cast
    field_simp
    ring
  unfold rankinKernel frickeKernel
  rw [hf, hθ, im_fricke]

/-- **The Fricke-side dual integral with the explicit kernel:**
$\sum_{\gamma\in R}\int_{\mathcal F}K(\gamma\tau)L^s(|\gamma\tau|/\gamma\tau)^\lambda E^{\mathrm{prim}}(\gamma\tau,s)\,d\mu$,
$K$ = `frickeKernel`. -/
noncomputable def frickeKernelIntegral (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ) {r : ℕ}
    (ψ : DirichletCharacter ℂ r) [NeZero (rankinLevel N t r)] (f : ℍ → ℂ) (R : List SL(2, ℤ)) (s : ℂ) : ℂ :=
  repsIntegral R fun z ↦ frickeKernel k N t ψ f z *
    ((rankinLevel N t r : ℂ) ^ s * (((‖(z : ℂ)‖ : ℝ) : ℂ) / z) ^ (k - charParity ψ) *
      DualFricke.eisensteinPrimSum (rankinLevel N t r) (k - charParity ψ) (rankinChar k N χ t ψ) z s)

theorem frickeDualIntegral_eq_kernel {k N t r : ℕ} (hN : 0 < N) (ht : 1 ≤ t) [NeZero r]
    [NeZero (rankinLevel N t r)] (χ : DirichletCharacter ℂ (4 * N)) {ψ : DirichletCharacter ℂ r}
    (hψ : ψ.IsPrimitive) (f : ℍ → ℂ) (R : List SL(2, ℤ)) (s : ℂ) :
    FrickeReduction.frickeDualIntegral k N χ t ψ f R s = frickeKernelIntegral k N χ t ψ f R s := by
  unfold FrickeReduction.frickeDualIntegral frickeKernelIntegral
  refine repsIntegral_congr R fun z ↦ ?_
  rw [rankinKernel_fricke hN ht hψ f z]

open FrickeReduction in
/-- **Shimura's Fricke-side identity with the explicit kernel** (Shimura 1973 `shimura1973`, proof of the Main Theorem
[unverified]): the statement of `ShimuraFrickeUnfolding M k N χ` with `frickeDualIntegral` replaced by
`frickeKernelIntegral` (equal to it, `frickeDualIntegral_eq_kernel`). The integrand is
$(-2iNw)^{k+1/2}(f|W_{4N})(w)\,\overline{r\tau(\psi)^{-1}(-2iu)^{1/2}(2ru)^\nu\theta_{\bar\psi}(u)}\,
(y/(L|z|^2))^{(k+\nu+1)/2}\cdot L^s(|z|/z)^\lambda E^{\mathrm{prim}}(z,s)$ with $w = 4tr^2z$, $u = 4Nz$; for the theta
multiplier $f|W_{4N} \in S_{k+1/2}(4N,\bar\chi(\tfrac{4N}\cdot))$ (`frickeHalf_mem_cuspForms`). What is left
(LE-MF-0285): the unfolding of this integrand over $\Gamma_0(L)\backslash\mathbb H$ against the Eisenstein series at $\infty$
of level $f\,g_0/e$ in `DualFricke.eisensteinPrimSum`, which needs the expansions of $(f|W_{4N})(4tr^2\cdot)$ and
$\theta_{\bar\psi}(4N\cdot)$ at the cusps $\delta\infty$, $\delta \in \Gamma_0(L)\backslash\Gamma_0(fg_0/e)$, and the
identification of the resulting Dirichlet series with one sequence $b$ for all $\psi$. -/
@[kb "shimura1973" "proof of the Main Theorem: the dual Rankin integral with the kernel f|W(4N) times the theta series at the cusp 0, unfolded at infinity [unverified]"]
structure ShimuraFrickeKernelUnfolding (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) :
    Prop where
  dual : ∀ hN : 0 < N, 2 ≤ k → ∀ t : ℕ, ∀ ht : 1 ≤ t, Squarefree t → ∀ f ∈ M.cuspForms k N χ, ∀ a : ℕ → ℂ,
    Abstract.HasQExp f a →
    ∃ b : ℕ → ℂ, CoeffGrowth b ∧ b 0 = 0 ∧
      (haveI : NeZero (rankinLevel N t 1) := ⟨(rankinLevel_pos hN ht le_rfl).ne'⟩
        ∃ R : List SL(2, ℤ), IsGamma0Reps (rankinLevel N t 1) R ∧ ∃ σ : ℝ, ∀ w : ℂ, σ < w.re →
        rankinDualFactor k N t (1 : DirichletCharacter ℂ 1) w *
            frickeKernelIntegral k N χ t (1 : DirichletCharacter ℂ 1) f R (rankinS k w) =
          I ^ (2 * k) * (gammaFactor (4 * N) w * LSeries b w)) ∧
      ∀ m : ℕ, ∀ hm : m.Prime, m ≠ 2 → m.Coprime (4 * N) → ∀ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive →
        haveI : NeZero (rankinLevel N t m) := ⟨(rankinLevel_pos hN ht hm.one_lt.le).ne'⟩
        ∃ R : List SL(2, ℤ), IsGamma0Reps (rankinLevel N t m) R ∧ ∃ σ : ℝ, ∀ w : ℂ, σ < w.re →
          rankinDualFactor k N t ψ w * frickeKernelIntegral k N χ t ψ f R (rankinS k w) =
            I ^ (2 * k) * weilConstant (χ ^ 2) ψ * (gammaFactor (4 * N * m ^ 2) w * LSeries (twist ψ⁻¹ b) w)

open FrickeReduction in
/-- **The reduction:** `ShimuraFrickeKernelUnfolding M k N χ` gives `ShimuraFrickeUnfolding M k N χ`. -/
theorem shimuraFrickeUnfolding_of_kernel (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N))
    (hK : ShimuraFrickeKernelUnfolding M k N χ) : ShimuraFrickeUnfolding M k N χ := by
  refine ⟨fun hN hk t ht hsq f hf a ha ↦ ?_⟩
  obtain ⟨b, hb, hb0, ⟨R₁, hR₁, σ₁, h₁⟩, h₂⟩ := hK.dual hN hk t ht hsq f hf a ha
  refine ⟨b, hb, hb0, ⟨R₁, hR₁, σ₁, fun w hw ↦ ?_⟩, fun m hm hm2 hmN ψ hψ ↦ ?_⟩
  · have : NeZero (rankinLevel N t 1) := ⟨(rankinLevel_pos hN ht le_rfl).ne'⟩
    rw [frickeDualIntegral_eq_kernel hN ht χ DirichletCharacter.isPrimitive_one_level_one]
    exact h₁ w hw
  · have : NeZero (rankinLevel N t m) := ⟨(rankinLevel_pos hN ht hm.one_lt.le).ne'⟩
    have : NeZero m := ⟨hm.ne_zero⟩
    obtain ⟨R₂, hR₂, σ₂, h₂'⟩ := h₂ m hm hm2 hmN ψ hψ
    refine ⟨R₂, hR₂, σ₂, fun w hw ↦ ?_⟩
    rw [frickeDualIntegral_eq_kernel hN ht χ hψ]
    exact h₂' w hw

/-- **Shimura's theorem for the theta multiplier from the explicit-kernel identity** (Shimura 1973 `shimura1973`,
Main Theorem): `shimuraTheorem_theta_of_frickeUnfolding` with the input `ShimuraFrickeKernelUnfolding`. -/
@[kb "shimura1973" "Main Theorem for the theta multiplier, conditional on the dual identity with the kernel f|W(4N) times theta at the cusp 0 [unverified]"]
theorem shimuraTheorem_theta_of_frickeKernel (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (hN : 0 < N)
    (hK : ShimuraFrickeKernelUnfolding thetaMultiplierSystem k N χ) :
    ShimuraTheorem thetaMultiplierSystem k N χ :=
  shimuraTheorem_theta_of_frickeUnfolding k N χ hN
    (shimuraFrickeUnfolding_of_kernel thetaMultiplierSystem k N χ hK)

end ModularFormsKB.HalfIntegral
