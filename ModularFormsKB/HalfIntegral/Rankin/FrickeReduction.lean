/-
# Shimura's dual unfolding after the Fricke involution: the reduction of `ShimuraDualUnfoldingSomeReps`

Loose end LE-MF-0256.

The dual Rankin integral $\check{\mathcal R}_\psi(s) = \int_{\Gamma_0(L)\backslash\mathbb H}G_\psi\,\check E(\cdot,s)\,d\mu$,
$L = 16Ntr^2$ (`rankinDual`), is rewritten in three proved steps:

1. `integrableOn_rankinDualIntegrand`: for $\operatorname{Re}s > 1$ the integrand is integrable on the coset fundamental
   domain $D_L$ (the kernel decays at every cusp, `rankinKernel_bound_fd`; $\check E$ grows at most polynomially in $y$
   and $1/y$, by Hecke's functional equation `Miyake.HeckeTrick.eisensteinFE`);
2. the Fricke change of variables `ChangeOfVariables.repsIntegral_comp_fricke` (row 4, wave 1);
3. the dual Eisenstein series at $W_Lz$ as a combination of Eisenstein series at $\infty$ of level $f$ (the conductor of
   the Rankin character $\omega$) with the primitive character $\overline{\omega^*}$ at the points $(g_0/e)z$
   (`DualFricke.eisensteinDual_fricke`, `DualFricke.eisensteinGauss_eq_sum`, with the Gauss sum of the imprimitive
   character, row 7).

So (`rankinDual_eq_frickeIntegral`)
$$\check{\mathcal R}_\psi(s) = \sum_{\gamma\in R}\int_{\mathcal F}G_\psi(W_L\gamma\tau)\,L^s\Big(\frac{|\gamma\tau|}{\gamma\tau}\Big)^\lambda
  E^{\mathrm{prim}}(\gamma\tau,s)\,d\mu(\tau),$$
and Shimura's dual identity becomes the smaller named input `ShimuraFrickeUnfolding`: the same identity with the
right-hand side above in place of `rankinDual`. Here the Gauss sums, the Fricke matrix and the dual lattice are gone; what
is left is the unfolding of the transformed kernel $z \mapsto G_\psi(W_Lz)(|z|/z)^\lambda$ against Eisenstein series at
$\infty$ of the levels $f\cdot g_0/e$, that is, the constant terms of $f$ and $\theta_{\psi,t}$ at the cusps $W_L\gamma\infty$.
`shimuraDualUnfoldingSomeReps_of_frickeUnfolding` proves the implication, and
`shimuraTheorem_theta_of_frickeUnfolding` Shimura's theorem for the theta multiplier from the new input.

**Index shift.** Matrix entries are 0-based.
-/
import ModularFormsKB.HalfIntegral.Rankin.DualFricke
import ModularFormsKB.HalfIntegral.Abstract.ChangeOfVariables
import ModularFormsKB.HalfIntegral.Abstract.FundamentalDomainVolume
import ModularFormsKB.Miyake.HeckeTrick.LatticeInversion
import ModularFormsKB.HalfIntegral.Rankin.Decay
import ModularFormsKB.HalfIntegral.Rankin.Assembly

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup MeasureTheory Set
open scoped Real

local notation "ℍ" => UpperHalfPlane

namespace FrickeReduction

lemma eisTerm_neg (lam : ℕ) (s v : ℂ) : eisTerm lam s (-v) = (-1) ^ lam * eisTerm lam s v := by
  unfold eisTerm
  rw [norm_neg, neg_pow]
  ring

lemma eisensteinDual_eq_zero_of_parity {L lam : ℕ} (hL : 2 ≤ L) (ω : DirichletCharacter ℂ L)
    (h : ω (-1) ≠ (-1) ^ lam) (z : ℍ) (s : ℂ) : eisensteinDual L lam ω z s = 0 := by
  have hc : ω (-1) * (-1) ^ lam = -1 := by
    have h1 : ω (-1) * ω (-1) = 1 := by
      rw [← map_mul]; simp
    rcases mul_self_eq_one_iff.1 h1 with h2 | h2 <;>
      rcases neg_one_pow_eq_or ℂ lam with h3 | h3 <;>
      first | exact absurd (h2.trans h3.symm) h | (rw [h2, h3]; norm_num)
  set S := ∑' p : ℤ × ℤ, gaussAt L ω (-p.1) * eisTerm lam s ((p.1 : ℂ) * z + p.2) with hS
  have hunit : IsUnit (((-1 : ℤ)) : ZMod L) := by simp
  have key : ∀ p : ℤ × ℤ, gaussAt L ω (-(Equiv.neg (ℤ × ℤ) p).1) * eisTerm lam s
      (((Equiv.neg (ℤ × ℤ) p).1 : ℂ) * z + (Equiv.neg (ℤ × ℤ) p).2) =
      (ω (-1) * (-1) ^ lam) * (gaussAt L ω (-p.1) * eisTerm lam s ((p.1 : ℂ) * z + p.2)) := by
    intro p
    have hg' : gaussAt L ω (-(-p.1)) = ω (-1) * gaussAt L ω (-p.1) := by
      have h1 := DualReps.gaussAt_mul (by omega) ω (-p.1) (-1) hunit
      have h2 : ω (-1) * ω (-1) = 1 := by rw [← map_mul]; simp
      have h1' : ω (-1) * gaussAt L ω p.1 = gaussAt L ω (-p.1) := by simpa using h1
      rw [neg_neg, ← h1', ← mul_assoc, h2, one_mul]
    simp only [Equiv.neg_apply, Prod.fst_neg, Prod.snd_neg]
    rw [hg']
    have : ((-p.1 : ℤ) : ℂ) * z + ((-p.2 : ℤ) : ℂ) = -((p.1 : ℂ) * z + p.2) := by push_cast; ring
    rw [this, eisTerm_neg]
    ring
  have h2 : S = (ω (-1) * (-1) ^ lam) * S := by
    calc S = ∑' p : ℤ × ℤ, gaussAt L ω (-(Equiv.neg (ℤ × ℤ) p).1) * eisTerm lam s
          (((Equiv.neg (ℤ × ℤ) p).1 : ℂ) * z + (Equiv.neg (ℤ × ℤ) p).2) :=
          (Equiv.tsum_eq (Equiv.neg (ℤ × ℤ)) fun p : ℤ × ℤ ↦
            gaussAt L ω (-p.1) * eisTerm lam s ((p.1 : ℂ) * z + p.2)).symm
      _ = _ := by rw [tsum_congr key, tsum_mul_left]
  rw [hc] at h2
  have : S = 0 := by linear_combination (1/2 : ℂ) * h2
  unfold eisensteinDual
  show (z.im : ℂ) ^ s * S = 0
  rw [this, mul_zero]

/-- **Polynomial growth of the dual Eisenstein series** for $\operatorname{Re}s > 1$, $L \ge 2$, $\lambda \ge 1$:
$|\check E(z,s)| \le B(y^A + y^{-A})$, and $\check E(\cdot,s)$ is continuous. From Hecke's functional equation
(`Miyake.HeckeTrick.eisensteinFE`) when $\omega(-1) = (-1)^\lambda$; otherwise $\check E = 0$ (the terms $p$ and $-p$
cancel). -/
theorem eisensteinDual_bound {L lam : ℕ} (hL : 2 ≤ L) (hlam : 1 ≤ lam) (ω : DirichletCharacter ℂ L) {s : ℂ}
    (hs : 1 < s.re) :
    Continuous (fun z ↦ eisensteinDual L lam ω z s) ∧
      ∃ A B : ℝ, ∀ z : ℍ, ‖eisensteinDual L lam ω z s‖ ≤ B * (z.im ^ A + z.im ^ (-A)) := by
  by_cases hpar : ω (-1) = (-1) ^ lam
  · obtain ⟨E, -, hcont, -, hFE, hbd⟩ := Miyake.HeckeTrick.eisensteinFE.fe L lam ω hL hlam hpar
    set s' : ℂ := 1 - s with hs'
    have hre : s'.re < 0 := by simp [hs']; linarith
    set F : ℂ := (L : ℂ) ^ (-s') * (π : ℂ) ^ (-s) * Gamma (s + lam / 2) with hF
    have hss : 1 - s' = s := by rw [hs']; ring
    have hF0 : F ≠ 0 := by
      have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
      have hπ0 : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
      · rw [Ne, Complex.cpow_eq_zero_iff]; tauto
      · rw [Ne, Complex.cpow_eq_zero_iff]; tauto
      · apply Complex.Gamma_ne_zero_of_re_pos
        simp; positivity
    have hEq : ∀ z : ℍ, eisensteinDual L lam ω z s = E z s' / F := by
      intro z
      have := hFE z s' hre
      rw [hss] at this
      rw [this, eq_div_iff hF0, hF]
      ring
    refine ⟨?_, ?_⟩
    · simp_rw [hEq]
      exact (hcont s').div_const F
    · obtain ⟨A, B, hAB⟩ := hbd s'.re s'.re
      refine ⟨A, B / ‖F‖, fun z ↦ ?_⟩
      have hFp : 0 < ‖F‖ := norm_pos_iff.2 hF0
      rw [hEq, norm_div, div_le_iff₀ hFp]
      calc ‖E z s'‖ ≤ B * (z.im ^ A + z.im ^ (-A)) := hAB z s' le_rfl le_rfl
        _ = _ := by field_simp
  · refine ⟨?_, 0, 0, fun z ↦ ?_⟩
    · simp only [eisensteinDual_eq_zero_of_parity hL ω hpar]
      exact continuous_const
    · simp [eisensteinDual_eq_zero_of_parity hL ω hpar]

lemma one_le_of_hr {r : ℕ} (hr : r = 1 ∨ (r.Prime ∧ r ≠ 2)) : 1 ≤ r := by
  rcases hr with rfl | ⟨hp, -⟩
  · exact le_rfl
  · exact hp.one_lt.le

/-- **Integrability of the dual Rankin integrand** on the coset fundamental domain $D_L$, $L = 16Ntr^2$, for
$\operatorname{Re}s > 1$, $f$ a cusp form, $r = 1$ or an odd prime and $\nu < k$. -/
theorem integrableOn_rankinDualIntegrand (M : MultiplierSystem) (hT : ThetaTwistLaw M) {k N : ℕ} (hN : 0 < N)
    {χ : DirichletCharacter ℂ (4 * N)} {f : ℍ → ℂ} (hf : f ∈ M.cuspForms k N χ) {t : ℕ} (ht : 1 ≤ t) {r : ℕ}
    (hr : r = 1 ∨ (r.Prime ∧ r ≠ 2)) (ψ : DirichletCharacter ℂ r) (hk : charParity ψ < k) {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn (fun τ ↦ rankinKernel k ψ t f τ *
        eisensteinDual (rankinLevel N t r) (k - charParity ψ) (rankinChar k N χ t ψ) τ s)
      (ChangeOfVariables.gamma0Domain (rankinLevel N t r)) := by
  have hfT : M.Transforms k N χ f := (show M.IsCuspForm k N χ f from hf).transforms
  have hr1 := one_le_of_hr hr
  have hL2 : 2 ≤ rankinLevel N t r := by
    unfold rankinLevel
    have : 1 ≤ N * t * r ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  have hνk : charParity ψ ≤ k := by omega
  have hlam : 1 ≤ k - charParity ψ := by omega
  have : NeZero (rankinLevel N t r) := ⟨by omega⟩
  obtain ⟨R, hR⟩ := exists_isGamma0Reps (rankinLevel N t r) (by omega)
  refine ChangeOfVariables.integrableOn_gamma0Domain hR
    (fun γ hγ z ↦ DualReps.rankinDualIntegrand_smul M hT hN hfT ht hr ψ hk s hγ z) fun γ _ ↦ ?_
  obtain ⟨hEc, A, B, hB⟩ := eisensteinDual_bound (L := rankinLevel N t r) (lam := k - charParity ψ) hL2 hlam
    (rankinChar k N χ t ψ) hs
  have hθ := norm_thetaTwist_le ψ ht
  obtain ⟨C, hC⟩ := rankinKernel_bound_fd M hN hf ψ (continuous_thetaTwist ψ ht)
    (let ⟨C, _, h⟩ := hθ; ⟨C, h⟩) γ A
  have hγ : Continuous (fun τ : ℍ ↦ γ • τ) := continuous_const_smul (γ : GL (Fin 2) ℝ)
  have hcont : Continuous fun τ : ℍ ↦ rankinKernel k ψ t f (γ • τ) *
      eisensteinDual (rankinLevel N t r) (k - charParity ψ) (rankinChar k N χ t ψ) (γ • τ) s :=
    ((continuous_rankinKernel k ψ ht (show M.IsCuspForm k N χ f from hf).holo.continuous).comp hγ).mul
      (hEc.comp hγ)
  refine Measure.integrableOn_of_bounded (M := |B| * |C|) volume_fd_lt_top.ne
    hcont.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_fd fun τ hτ ↦ ?_)
  have h1 := hB (γ • τ)
  have hpos : 0 ≤ (γ • τ).im ^ A + (γ • τ).im ^ (-A) := by
    have := (γ • τ).im_pos
    positivity
  rw [norm_mul]
  calc ‖rankinKernel k ψ t f (γ • τ)‖ *
        ‖eisensteinDual (rankinLevel N t r) (k - charParity ψ) (rankinChar k N χ t ψ) (γ • τ) s‖
      ≤ ‖rankinKernel k ψ t f (γ • τ)‖ * (|B| * ((γ • τ).im ^ A + (γ • τ).im ^ (-A))) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hpos))
          (norm_nonneg _)
    _ = |B| * (‖rankinKernel k ψ t f (γ • τ)‖ * ((γ • τ).im ^ A + (γ • τ).im ^ (-A))) := by ring
    _ ≤ |B| * |C| := mul_le_mul_of_nonneg_left ((hC τ hτ).trans (le_abs_self _)) (abs_nonneg _)

lemma rankinLevel_pos {N t r : ℕ} (hN : 0 < N) (ht : 1 ≤ t) (hr : 1 ≤ r) : 0 < rankinLevel N t r := by
  unfold rankinLevel; positivity

/-- **The Fricke-transformed dual integral**
$\sum_{\gamma\in R}\int_{\mathcal F}G_\psi(W_L\gamma\tau)\,L^s(|\gamma\tau|/\gamma\tau)^\lambda
E^{\mathrm{prim}}(\gamma\tau,s)\,d\mu(\tau)$, $L = 16Ntr^2$, $\lambda = k - \nu$, $E^{\mathrm{prim}}$ =
`DualFricke.eisensteinPrimSum` for the Rankin character. -/
noncomputable def frickeDualIntegral (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ) {r : ℕ}
    (ψ : DirichletCharacter ℂ r) [NeZero (rankinLevel N t r)] (f : ℍ → ℂ) (R : List SL(2, ℤ)) (s : ℂ) : ℂ :=
  repsIntegral R fun z ↦ rankinKernel k ψ t f (TauCeti.frickeGL ℝ (rankinLevel N t r) • z) *
    ((rankinLevel N t r : ℂ) ^ s * (((‖(z : ℂ)‖ : ℝ) : ℂ) / z) ^ (k - charParity ψ) *
      DualFricke.eisensteinPrimSum (rankinLevel N t r) (k - charParity ψ) (rankinChar k N χ t ψ) z s)

/-- **The dual Rankin integral after the Fricke involution** (for $\operatorname{Re}s > 1$, $f$ a cusp form, $r = 1$ or an
odd prime, $\nu < k$): `rankinDual` = `frickeDualIntegral`. -/
theorem rankinDual_eq_frickeIntegral (M : MultiplierSystem) (hT : ThetaTwistLaw M) {k N : ℕ} (hN : 0 < N)
    {χ : DirichletCharacter ℂ (4 * N)} {f : ℍ → ℂ} (hf : f ∈ M.cuspForms k N χ) {t : ℕ} (ht : 1 ≤ t) {r : ℕ}
    (hr : r = 1 ∨ (r.Prime ∧ r ≠ 2)) (ψ : DirichletCharacter ℂ r) (hk : charParity ψ < k)
    [NeZero (rankinLevel N t r)] {R : List SL(2, ℤ)} (hR : IsGamma0Reps (rankinLevel N t r) R) {s : ℂ}
    (hs : 1 < s.re) :
    rankinDual k N χ t ψ f R s = frickeDualIntegral k N χ t ψ f R s := by
  have hfT : M.Transforms k N χ f := (show M.IsCuspForm k N χ f from hf).transforms
  have hinv := fun γ hγ τ ↦ DualReps.rankinDualIntegrand_smul M hT hN hfT ht hr ψ hk s (γ := γ) hγ τ
  have hint := integrableOn_rankinDualIntegrand M hT hN hf ht hr ψ hk hs
  unfold rankinDual frickeDualIntegral
  rw [← ChangeOfVariables.repsIntegral_comp_fricke hR _ hinv hint]
  refine repsIntegral_congr R fun z ↦ ?_
  rw [DualFricke.eisensteinDual_fricke (by omega), DualFricke.eisensteinGauss_eq_sum (by omega) _ _ hs]

end FrickeReduction

open FrickeReduction in
/-- **Shimura's dual unfolding after the Fricke involution** (Shimura 1973 `shimura1973`, proof of the Main Theorem
[unverified]): the statement of `ShimuraDualUnfoldingSomeReps M k N χ` with the dual Rankin integral replaced by its
Fricke transform `frickeDualIntegral` (proved equal for $\operatorname{Re}s > 1$, `rankinDual_eq_frickeIntegral`). For
$N \ge 1$, $k \ge 2$, squarefree $t \ge 1$ and $f \in S_{k+1/2}(4N,\chi)$ with $q$-expansion $a$ there is $b$ of polynomial
growth, $b(0) = 0$, such that for $\psi = 1$ and every primitive $\psi$ modulo an odd prime $m \nmid 4N$ there is a list
$R$ of representatives of $\Gamma_0(16Ntm^2)$ with
$$\text{(`rankinDualFactor`)}\cdot\sum_{\gamma\in R}\int_{\mathcal F}G_\psi(W_L\gamma\tau)L^s
  \Big(\frac{|\gamma\tau|}{\gamma\tau}\Big)^\lambda E^{\mathrm{prim}}(\gamma\tau,s)\,d\mu =
  i^{2k}C_\psi(2\pi/\sqrt{4Nm^2})^{-w}\Gamma(w)\sum_n\bar\psi(n)b(n)n^{-w},\quad s = \tfrac{w-k+1}2,$$
for $\operatorname{Re}w$ large. What is left is the unfolding of $G_\psi\circ W_L$ against Eisenstein series at $\infty$
of the levels $f g_0/e$: the constant terms of $f$ and $\theta_{\psi,t}$ at the cusps $W_L\gamma\infty$ (LE-MF-0256). -/
@[kb "shimura1973" "proof of the Main Theorem: the dual Rankin integral after the Fricke involution, unfolded at infinity [unverified]"]
structure ShimuraFrickeUnfolding (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop where
  dual : ∀ hN : 0 < N, 2 ≤ k → ∀ t : ℕ, ∀ ht : 1 ≤ t, Squarefree t → ∀ f ∈ M.cuspForms k N χ, ∀ a : ℕ → ℂ,
    Abstract.HasQExp f a →
    ∃ b : ℕ → ℂ, CoeffGrowth b ∧ b 0 = 0 ∧
      (haveI : NeZero (rankinLevel N t 1) := ⟨(rankinLevel_pos hN ht le_rfl).ne'⟩
        ∃ R : List SL(2, ℤ), IsGamma0Reps (rankinLevel N t 1) R ∧ ∃ σ : ℝ, ∀ w : ℂ, σ < w.re →
        rankinDualFactor k N t (1 : DirichletCharacter ℂ 1) w *
            frickeDualIntegral k N χ t (1 : DirichletCharacter ℂ 1) f R (rankinS k w) =
          I ^ (2 * k) * (gammaFactor (4 * N) w * LSeries b w)) ∧
      ∀ m : ℕ, ∀ hm : m.Prime, m ≠ 2 → m.Coprime (4 * N) → ∀ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive →
        haveI : NeZero (rankinLevel N t m) := ⟨(rankinLevel_pos hN ht hm.one_lt.le).ne'⟩
        ∃ R : List SL(2, ℤ), IsGamma0Reps (rankinLevel N t m) R ∧ ∃ σ : ℝ, ∀ w : ℂ, σ < w.re →
          rankinDualFactor k N t ψ w * frickeDualIntegral k N χ t ψ f R (rankinS k w) =
            I ^ (2 * k) * weilConstant (χ ^ 2) ψ * (gammaFactor (4 * N * m ^ 2) w * LSeries (twist ψ⁻¹ b) w)

open FrickeReduction in
/-- **The reduction:** `ShimuraFrickeUnfolding M k N χ` gives `ShimuraDualUnfoldingSomeReps M k N χ` for $N \ge 1$ and a
multiplier with `ThetaTwistLaw M`. -/
theorem shimuraDualUnfoldingSomeReps_of_frickeUnfolding (M : MultiplierSystem) (hT : ThetaTwistLaw M) (k N : ℕ)
    (χ : DirichletCharacter ℂ (4 * N)) (hN : 0 < N) (hF : ShimuraFrickeUnfolding M k N χ) :
    ShimuraDualUnfoldingSomeReps M k N χ := by
  refine ⟨fun hk t ht hsq f hf a ha ↦ ?_⟩
  obtain ⟨b, hb, hb0, ⟨R₁, hR₁, σ₁, h₁⟩, h₂⟩ := hF.dual hN hk t ht hsq f hf a ha
  have hre : ∀ w : ℂ, (k : ℝ) + 1 < w.re → 1 < (rankinS k w).re := fun w hw ↦ by
    rw [re_rankinS]; linarith
  refine ⟨b, hb, hb0, ⟨R₁, hR₁, max σ₁ ((k : ℝ) + 1), fun w hw ↦ ?_⟩, fun m hm hm2 hmN ψ hψ ↦ ?_⟩
  · have : NeZero (rankinLevel N t 1) := ⟨(rankinLevel_pos hN ht le_rfl).ne'⟩
    have hν : charParity (1 : DirichletCharacter ℂ 1) < k := by
      have := charParity_le_one (1 : DirichletCharacter ℂ 1); omega
    rw [rankinDual_eq_frickeIntegral M hT hN hf ht (Or.inl rfl) 1 hν hR₁
      (hre w (lt_of_le_of_lt (le_max_right _ _) hw))]
    exact h₁ w (lt_of_le_of_lt (le_max_left _ _) hw)
  · have : NeZero (rankinLevel N t m) := ⟨(rankinLevel_pos hN ht hm.one_lt.le).ne'⟩
    obtain ⟨R₂, hR₂, σ₂, h₂'⟩ := h₂ m hm hm2 hmN ψ hψ
    refine ⟨R₂, hR₂, max σ₂ ((k : ℝ) + 1), fun w hw ↦ ?_⟩
    have hν : charParity ψ < k := by have := charParity_le_one ψ; omega
    rw [rankinDual_eq_frickeIntegral M hT hN hf ht (Or.inr ⟨hm, hm2⟩) ψ hν hR₂
      (hre w (lt_of_le_of_lt (le_max_right _ _) hw))]
    exact h₂' w (lt_of_le_of_lt (le_max_left _ _) hw)

/-- **Shimura's theorem for the theta multiplier from the Fricke-side dual identity** (Shimura 1973 `shimura1973`,
Main Theorem): `shimuraTheorem_theta_of_dualUnfoldingSomeReps` with the smaller input
`ShimuraFrickeUnfolding thetaMultiplierSystem k N χ`. -/
@[kb "shimura1973" "Main Theorem for the theta multiplier, conditional on the dual identity after the Fricke involution [unverified]"]
theorem shimuraTheorem_theta_of_frickeUnfolding (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (hN : 0 < N)
    (hF : ShimuraFrickeUnfolding thetaMultiplierSystem k N χ) :
    ShimuraTheorem thetaMultiplierSystem k N χ :=
  shimuraTheorem_theta_of_dualUnfoldingSomeReps k N χ hN
    (shimuraDualUnfoldingSomeReps_of_frickeUnfolding thetaMultiplierSystem thetaTwistLaw_thetaMultiplierSystem
      k N χ hN hF)

end ModularFormsKB.HalfIntegral
