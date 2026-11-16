/-
# $T(p^2)$, $p$ odd, is self-adjoint on $S_{k+1/2}(4)$ for the Petersson product

Proves the named input `PlusHeckeSelfAdjoint` (LE-MF-0269), the last extra
input of H3 besides `KohnenTPlusFourStable`.

For the theta multiplier, level $4$, trivial character, write
$P(F, G)(z) = \overline{F(z)}\,G(z)\operatorname{Im}(z)^{k+1/2}$ (`pInt`), so that
$\langle F, G\rangle = \tfrac16\sum_{\gamma}\int_{\mathcal F}P(F,G)(\gamma\tau)\,d\mu$ (`peterssonFour`). Let $p$ be an odd
prime, $f_\alpha(z) = f(z/p^2)$ (`fAlpha`), $f^\beta(z) = f(p^2z)$ (`fBeta`), $r_x$ the $p^2 + p$ representatives of
$H\backslash\Gamma_0(4)$ (`HeckeCoset.rep`, $H = \{\gamma : p^2 \mid b\}$) and $r_0 = \begin{pmatrix}p^2&y\\4&w\end{pmatrix}$.

1. `pInt_slash`: $P(F|\gamma, G|\gamma)(z) = P(F, G)(\gamma z)$, because $|j(\gamma, z)|^2 = |cz+d|$.
2. `pInt_heckeFun_left`: from $p^2\,T(p^2)f = \sum_x f_\alpha|r_x$ (`HeckeCoset.sum_slash_rep`) and
   $f_\alpha|r_0 = p^{2k+1}f^\beta$ (`slash_repZero`),
   $p^2\,P(T(p^2)f, g)(z) = p^{2k+1}\sum_x P(f^\beta, g)(r_0^{-1}r_xz)$; symmetrically (`pInt_heckeFun_right`)
   $p^2\,P(f, T(p^2)g)(z) = p^{2k+1}\sum_x P(f, g^\beta)(r_0^{-1}r_xz)$.
3. The elements $r_0^{-1}r_x\gamma_i$ represent $\Gamma_0(4p^2)\backslash\mathrm{SL}_2(\mathbb Z)$
   (`isGamma0Reps_conjReps`), and $f^\beta$, $g$ lie in $S_{k+1/2}(4p^2)$ (`fBeta_mem_cuspForms`, `mem_cuspForms_sq`), so
   both sides are integrals over $\Gamma_0(4p^2)\backslash\mathbb H$ of $\Gamma_0(4p^2)$-invariant integrable functions.
4. `pInt_fBeta_Mmat`: for the Atkin–Lehner matrix $M = \mathrm{diag}(1,p^2)\,r_0$, which normalizes $\Gamma_0(4p^2)$
   (`conjAct_normalizer`), $P(f^\beta, g)(Mz) = P(f, g^\beta)(z)$. The change of variables `repsIntegral_comp_smul`
   gives `peterssonFour_heckeFun`: $\langle T(p^2)f, g\rangle = \langle f, T(p^2)g\rangle$ for $f, g \in S_{k+1/2}(4)$.
5. `plusHeckeSelfAdjoint`: the named input `PlusHeckeSelfAdjoint k`, for every $k$.

This is the classical argument (Shimura 1973 `shimura1973`, §1 [unverified]) with the double coset
$\Gamma_0(4)\,\mathrm{diag}(1,p^2)\,\Gamma_0(4)$ replaced by the explicit representatives of `HeckeCoset`.
-/
import ModularFormsKB.HalfIntegral.PlusHeckeAdjointGroup
import ModularFormsKB.HalfIntegral.Abstract.PeterssonConvergence
import ModularFormsKB.HalfIntegral.Abstract.KohnenZagierHecke

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup MeasureTheory
open scoped Real ComplexConjugate

local notation "ℍ" => UpperHalfPlane

namespace PlusHeckeAdjoint

open ModularFormsKB.HalfIntegral.HeckeCoset

/-- The Petersson integrand $P(F, G)(z) = \overline{F(z)}\,G(z)\operatorname{Im}(z)^{k+1/2}$. -/
noncomputable def pInt (k : ℕ) (F G : ℍ → ℂ) (z : ℍ) : ℂ :=
  conj (F z) * G z * ((z.im ^ ((k : ℝ) + 1 / 2) : ℝ) : ℂ)

lemma peterssonIntegrand_eq_pInt (k : ℕ) (γ : SL(2, ℤ)) (F G : ℍ → ℂ) (τ : ℍ) :
    peterssonIntegrand γ ((k : ℝ) + 1 / 2) F G τ = pInt k F G (γ • τ) := rfl

lemma pInt_swap (k : ℕ) (F G : ℍ → ℂ) (z : ℍ) : pInt k G F z = conj (pInt k F G z) := by
  simp only [pInt, map_mul, conj_conj, conj_ofReal]
  ring

lemma pInt_smul_left (k : ℕ) (c : ℂ) (F G : ℍ → ℂ) (z : ℍ) :
    pInt k (c • F) G z = conj c * pInt k F G z := by
  simp only [pInt, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

lemma pInt_smul_right (k : ℕ) (c : ℂ) (F G : ℍ → ℂ) (z : ℍ) :
    pInt k F (c • G) z = c * pInt k F G z := by
  simp only [pInt, Pi.smul_apply, smul_eq_mul]
  ring

/-- The trivial character takes the value $1$ at the lower-right entry of $\gamma \in \Gamma_0(4N)$. -/
lemma one_apply_of_mem {N : ℕ} {γ : SL(2, ℤ)} (h : γ ∈ Gamma0 (4 * N)) :
    (1 : DirichletCharacter ℂ (4 * N)) (γ 1 1 : ZMod (4 * N)) = 1 := by
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
  exact MulChar.one_apply hu

lemma mem_gamma0_four {N : ℕ} {γ : SL(2, ℤ)} (h : γ ∈ Gamma0 (4 * N)) : γ ∈ Gamma0 4 := by
  rw [Gamma0_mem] at *
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at *
  exact dvd_trans (by push_cast; exact dvd_mul_right (4 : ℤ) N) h

/-- **The Petersson integrand under a simultaneous slash:** $P(F|\gamma, G|\gamma)(z) = P(F, G)(\gamma z)$ for
$\gamma \in \Gamma_0(4N)$ and the trivial character. -/
theorem pInt_slash (M : MultiplierSystem) (k N : ℕ) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (4 * N)) (F G : ℍ → ℂ)
    (z : ℍ) : pInt k (M.slash k N 1 γ F) (M.slash k N 1 γ G) z = pInt k F G (γ • z) := by
  have h4 := mem_gamma0_four hγ
  have hj := M.norm_sq γ h4 z
  have hD : 0 < ‖(γ 1 0 : ℂ) * z + γ 1 1‖ := by
    rw [← hj]; exact pow_pos (norm_pos_iff.2 (M.ne_zero γ h4 z)) 2
  set J := M.j γ z ^ (2 * k + 1) with hJ
  set D := ‖(γ 1 0 : ℂ) * z + γ 1 1‖ with hDdef
  have hn : ‖J‖ ^ 2 = D ^ (2 * k + 1) := by rw [hJ, norm_pow, ← pow_mul, mul_comm, pow_mul, hj]
  have e1 : conj J⁻¹ * J⁻¹ = (((D ^ (2 * k + 1))⁻¹ : ℝ) : ℂ) := by
    rw [map_inv₀, ← mul_inv, Complex.conj_mul', ← hn]
    push_cast; ring
  have e2 : D ^ (-((k : ℝ) + 1 / 2)) * D ^ (-((k : ℝ) + 1 / 2)) = (D ^ (2 * k + 1))⁻¹ := by
    rw [← Real.rpow_add hD, ← Real.rpow_natCast, ← Real.rpow_neg hD.le]
    congr 1; push_cast; ring
  simp only [pInt, MultiplierSystem.slash, one_apply_of_mem hγ, inv_one, one_mul]
  rw [im_smul_rpow γ ((k : ℝ) + 1 / 2) z, ← hDdef, e2]
  rw [map_mul]
  calc conj J⁻¹ * conj (F (γ • z)) * (J⁻¹ * G (γ • z)) * ((z.im ^ ((k : ℝ) + 1 / 2) : ℝ) : ℂ)
      = (conj J⁻¹ * J⁻¹) * (conj (F (γ • z)) * G (γ • z) * ((z.im ^ ((k : ℝ) + 1 / 2) : ℝ) : ℂ)) := by ring
    _ = _ := by rw [e1]; push_cast; ring

/-- **Invariance:** if $F$, $G$ satisfy the transformation law on $\Gamma_0(4N)$ (trivial character), then $P(F, G)$ is
$\Gamma_0(4N)$-invariant. -/
theorem pInt_invariant (M : MultiplierSystem) (k N : ℕ) {F G : ℍ → ℂ} (hF : M.Transforms k N 1 F)
    (hG : M.Transforms k N 1 G) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (4 * N)) (z : ℍ) :
    pInt k F G (γ • z) = pInt k F G z := by
  rw [← pInt_slash M k N hγ, (M.transforms_iff_slash k N 1 F).1 hF γ hγ,
    (M.transforms_iff_slash k N 1 G).1 hG γ hγ]

/-! ### Level raising -/

/-- $f^\beta(z) = f(p^2z)$. -/
noncomputable def fBeta (P : ℕ+) (f : ℍ → ℂ) (z : ℍ) : ℂ := f (affPt (P ^ 2) 1 0 z)

/-- A form for $\Gamma_0(4)$ is a form for $\Gamma_0(4p^2)$. -/
theorem mem_cuspForms_sq (M : MultiplierSystem) (k : ℕ) (P : ℕ+) {g : ℍ → ℂ} (hg : g ∈ M.cuspForms k 1 1) :
    g ∈ M.cuspForms k ((P : ℕ) ^ 2) 1 := by
  refine ⟨hg.holo, fun γ hγ τ ↦ ?_, hg.zero_at_cusps⟩
  have hγ1 : γ ∈ Gamma0 (4 * 1) := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at *
    exact dvd_trans (by push_cast; exact dvd_mul_right (4 : ℤ) _) hγ
  rw [hg.transforms γ hγ1 τ, one_apply_of_mem hγ1, one_apply_of_mem hγ]

private lemma shimuraSym_sq_mul' (P : ℕ) (hP0 : 0 < P) (c d : ℤ) (h : Int.gcd P d = 1) :
    shimuraSym ((P : ℤ) ^ 2 * c) d = shimuraSym c d := by
  unfold shimuraSym
  have hg : Int.gcd P (d.natAbs : ℕ) = 1 := by
    unfold Int.gcd at h ⊢
    simpa only [Int.natAbs_natCast] using h
  have hP : (0 : ℤ) < (P : ℤ) ^ 2 := by positivity
  have hneg : ((P : ℤ) ^ 2 * c < 0 ∧ d < 0) ↔ (c < 0 ∧ d < 0) := by
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, h2⟩ <;> nlinarith
  have hj : jacobiSym ((P : ℤ) ^ 2 * c) d.natAbs = jacobiSym c d.natAbs := by
    rw [jacobiSym.mul_left, jacobiSym.sq_one' hg, one_mul]
  rw [if_congr hneg rfl rfl, hj]

lemma coe_smul_sl' (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ • τ : ℍ) : ℂ) = ((γ 0 0 : ℂ) * τ + γ 0 1) / ((γ 1 0 : ℂ) * τ + γ 1 1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

/-- **$f^\beta$ satisfies the transformation law on $\Gamma_0(4p^2)$** (theta multiplier). -/
theorem fBeta_transforms (k : ℕ) (P : ℕ+) (hp : (P : ℕ).Prime) {f : ℍ → ℂ}
    (hf : thetaMultiplierSystem.Transforms k 1 1 f) :
    thetaMultiplierSystem.Transforms k ((P : ℕ) ^ 2) 1 (fBeta P f) := by
  intro γ hγ τ
  obtain ⟨q, hq⟩ := (gamma0_mem_iff_dvd _ γ).1 hγ
  have hc : γ 1 0 = (P : ℤ) ^ 2 * (4 * q) := by rw [hq]; push_cast; ring
  set γ'' := lowerDiv P γ hc
  have hγ'' : γ'' ∈ Gamma0 (4 * 1) := by
    rw [gamma0_mem_iff_dvd, lowerDiv_10]; exact ⟨q, by push_cast; ring⟩
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at this
  have hpg : Int.gcd ((P : ℕ) : ℤ) (γ 1 1) = 1 := by
    have hpz : Prime ((P : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hnd : ¬ ((P : ℕ) : ℤ) ∣ γ 1 1 := by
      intro hd
      have h1 : ((P : ℕ) : ℤ) ∣ γ 1 0 := ⟨(P : ℤ) * (4 * q), by rw [hc]; ring⟩
      have : ((P : ℕ) : ℤ) ∣ γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 :=
        dvd_sub (Dvd.dvd.mul_left hd _) (Dvd.dvd.mul_left h1 _)
      rw [hdet] at this
      exact hpz.not_dvd_one this
    exact Int.isCoprime_iff_gcd_eq_one.mp ((Prime.coprime_iff_not_dvd hpz).mpr hnd)
  have hden : (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := cuspDenom_ne_zero γ τ
  have hP0 : ((P : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr P.ne_zero
  have hden' : ((γ'' 1 0 : ℤ) : ℂ) * (affPt (P ^ 2) 1 0 τ : ℂ) + (γ'' 1 1 : ℤ) =
      (γ 1 0 : ℂ) * τ + γ 1 1 := by
    rw [lowerDiv_10, lowerDiv_11, coe_affPt]
    have : (γ 1 0 : ℂ) = ((P : ℕ) : ℂ) ^ 2 * (4 * q) := by exact_mod_cast hc
    rw [this]; push_cast; ring
  have hpt : affPt (P ^ 2) 1 0 (γ • τ) = γ'' • affPt (P ^ 2) 1 0 τ := by
    apply UpperHalfPlane.ext
    rw [coe_affPt, coe_smul_sl', coe_smul_sl', hden', lowerDiv_00, lowerDiv_01, coe_affPt]
    push_cast
    field_simp
    ring
  have hj : thetaMult γ'' (affPt (P ^ 2) 1 0 τ) = thetaMult γ τ := by
    unfold thetaMult thetaMultCD
    rw [hden', lowerDiv_10, lowerDiv_11, hc, shimuraSym_sq_mul' _ P.pos _ _ hpg]
  have key := hf γ'' hγ'' (affPt (P ^ 2) 1 0 τ)
  simp only [fBeta, hpt, key, thetaMultiplierSystem_j, hj, one_apply_of_mem hγ, one_apply_of_mem hγ'']

/-- **$f^\beta \in S_{k+1/2}(4p^2)$** for $f \in S_{k+1/2}(4)$ (theta multiplier). -/
theorem fBeta_mem_cuspForms (k : ℕ) (P : ℕ+) (hp : (P : ℕ).Prime) {f : ℍ → ℂ}
    (hf : f ∈ thetaMultiplierSystem.cuspForms k 1 1) :
    fBeta P f ∈ thetaMultiplierSystem.cuspForms k ((P : ℕ) ^ 2) 1 :=
  ⟨mdiff_comp_affPt hf.holo (P ^ 2) 1 0, fBeta_transforms k P hp hf.transforms,
    cuspNorm_affPt_zero k hf.zero_at_cusps (P ^ 2) 1 0⟩

/-! ### The Hecke operator inside the integrand -/

section Hecke

variable (k : ℕ) (P : ℕ+) (hp : (P : ℕ).Prime) (hpN : ¬ (P : ℕ) ∣ 4 * 1)

include hp hpN in
lemma one_apply_P : (1 : DirichletCharacter ℂ (4 * 1)) ((P : ℕ) : ZMod (4 * 1)) = 1 :=
  MulChar.one_apply ((ZMod.isUnit_iff_coprime _ _).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN))

lemma natCast_pow_conj (n : ℕ) : conj (((P : ℕ) : ℂ) ^ n) = ((P : ℕ) : ℂ) ^ n := by
  rw [map_pow, Complex.conj_natCast]

/-- $f_\alpha|r_0 = p^{2k+1}f^\beta$ (`slash_repZero`, trivial character). -/
lemma slash_r0_fAlpha {f : ℍ → ℂ} (hf : thetaMultiplierSystem.Transforms k 1 1 f) :
    thetaMultiplierSystem.slash k 1 1 (r0 P hp hpN) (fAlpha P f) = ((P : ℕ) : ℂ) ^ (2 * k + 1) • fBeta P f := by
  funext τ
  rw [r0, slash_repZero k 1 1 P hp hpN hf, one_apply_P P hp hpN, one_pow, one_mul]
  rfl

include hpN in
lemma pInt_fAlpha {f g : ℍ → ℂ} (hf : thetaMultiplierSystem.Transforms k 1 1 f)
    (hg : thetaMultiplierSystem.Transforms k 1 1 g) (u : ℍ) :
    pInt k (fAlpha P f) g u = ((P : ℕ) : ℂ) ^ (2 * k + 1) * pInt k (fBeta P f) g ((r0 P hp hpN)⁻¹ • u) := by
  have e : u = r0 P hp hpN • ((r0 P hp hpN)⁻¹ • u) := (smul_inv_smul _ u).symm
  conv_lhs => rw [e]
  rw [← pInt_slash thetaMultiplierSystem k 1 (r0_mem P hp hpN), slash_r0_fAlpha k P hp hpN hf,
    (thetaMultiplierSystem.transforms_iff_slash k 1 1 g).1 hg _ (r0_mem P hp hpN), pInt_smul_left,
    natCast_pow_conj]

/-- **$p^2\,P(T(p^2)f, g)(z) = p^{2k+1}\sum_x P(f^\beta, g)(r_0^{-1}r_xz)$.** -/
theorem pInt_heckeFun_left {f g : ℍ → ℂ} (hf : thetaMultiplierSystem.Transforms k 1 1 f)
    (hg : thetaMultiplierSystem.Transforms k 1 1 g) (z : ℍ) :
    ((P : ℕ) : ℂ) ^ 2 * pInt k (heckeFun k 1 1 P f) g z =
      ((P : ℕ) : ℂ) ^ (2 * k + 1) *
        ∑ x, pInt k (fBeta P f) g (((r0 P hp hpN)⁻¹ * rep 1 P hp hpN x) • z) := by
  have hs := sum_slash_rep 1 P hp hpN k 1 hf z
  have step1 : ((P : ℕ) : ℂ) ^ 2 * pInt k (heckeFun k 1 1 P f) g z =
      ∑ x, pInt k (thetaMultiplierSystem.slash k 1 1 (rep 1 P hp hpN x) (fAlpha P f)) g z := by
    simp only [pInt]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← map_sum, hs, map_mul, natCast_pow_conj]
    ring
  rw [step1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have hx := rep_mem 1 P hp hpN x
  conv_lhs => rw [← (thetaMultiplierSystem.transforms_iff_slash k 1 1 g).1 hg _ hx]
  rw [pInt_slash thetaMultiplierSystem k 1 hx, pInt_fAlpha k P hp hpN hf hg, mul_smul]

/-- **$p^2\,P(f, T(p^2)g)(z) = p^{2k+1}\sum_x P(f, g^\beta)(r_0^{-1}r_xz)$.** -/
theorem pInt_heckeFun_right {f g : ℍ → ℂ} (hf : thetaMultiplierSystem.Transforms k 1 1 f)
    (hg : thetaMultiplierSystem.Transforms k 1 1 g) (z : ℍ) :
    ((P : ℕ) : ℂ) ^ 2 * pInt k f (heckeFun k 1 1 P g) z =
      ((P : ℕ) : ℂ) ^ (2 * k + 1) *
        ∑ x, pInt k f (fBeta P g) (((r0 P hp hpN)⁻¹ * rep 1 P hp hpN x) • z) := by
  have h := congrArg conj (pInt_heckeFun_left k P hp hpN hg hf z)
  rw [map_mul, map_mul, natCast_pow_conj, natCast_pow_conj, ← pInt_swap, map_sum] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← pInt_swap]

lemma affPt_cancel (σ : ℍ) : affPt (P ^ 2) 1 0 (affPt 1 (P ^ 2) 0 σ) = σ := by
  apply UpperHalfPlane.ext
  have hP0 : ((P : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr P.ne_zero
  simp only [coe_affPt, PNat.pow_coe, PNat.one_coe]
  push_cast
  field_simp
  simp

lemma rpow_div_sq (x : ℝ) (hx : 0 ≤ x) :
    (x / ((P : ℕ) : ℝ) ^ 2) ^ ((k : ℝ) + 1 / 2) = x ^ ((k : ℝ) + 1 / 2) / ((P : ℕ) : ℝ) ^ (2 * k + 1) := by
  have hP : (0 : ℝ) ≤ (P : ℕ) := Nat.cast_nonneg _
  rw [Real.div_rpow hx (pow_nonneg hP 2)]
  congr 1
  rw [← Real.rpow_natCast ((P : ℕ) : ℝ) 2, ← Real.rpow_mul hP, ← Real.rpow_natCast]
  congr 1; push_cast; ring

/-- **The Atkin–Lehner change of variables on the integrand:** $P(f^\beta, g)(Mz) = P(f, g^\beta)(z)$. -/
theorem pInt_fBeta_Mmat {f g : ℍ → ℂ} (hf : thetaMultiplierSystem.Transforms k 1 1 f)
    (hg : thetaMultiplierSystem.Transforms k 1 1 g) (z : ℍ) :
    pInt k (fBeta P f) g (Mmat P hp hpN • z) = pInt k f (fBeta P g) z := by
  rw [Mmat_smul]
  set σ := r0 P hp hpN • z with hσ
  have hPn : ((P : ℕ) : ℂ) ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr P.ne_zero)
  have h1 : pInt k (fBeta P f) g (affPt 1 (P ^ 2) 0 σ) =
      (((P : ℕ) : ℂ) ^ (2 * k + 1))⁻¹ * pInt k f (fAlpha P g) σ := by
    simp only [pInt, fBeta, fAlpha, affPt_cancel, im_affPt, PNat.pow_coe, PNat.one_coe, Nat.cast_one, one_mul,
      Nat.cast_pow]
    rw [rpow_div_sq k P _ σ.im_pos.le]
    push_cast
    field_simp
  have h2 : pInt k f (fAlpha P g) σ = ((P : ℕ) : ℂ) ^ (2 * k + 1) * pInt k f (fBeta P g) z := by
    rw [hσ, ← pInt_slash thetaMultiplierSystem k 1 (r0_mem P hp hpN),
      (thetaMultiplierSystem.transforms_iff_slash k 1 1 f).1 hf _ (r0_mem P hp hpN),
      slash_r0_fAlpha k P hp hpN hg, pInt_smul_right]
  rw [h1, h2, ← mul_assoc, inv_mul_cancel₀ hPn, one_mul]

end Hecke

/-! ### Assembly -/

lemma peterssonReps_eq_sum (k : ℕ) (R : List SL(2, ℤ)) (F G : ℍ → ℂ) :
    peterssonReps R ((k : ℝ) + 1 / 2) F G = ∑ i : Fin R.length, ∫ τ in ModularGroup.fd, pInt k F G (R[i.1] • τ) := by
  rw [peterssonReps_eq, ← Fin.sum_univ_fun_getElem]
  rfl


section Assembly

variable (k : ℕ) (P : ℕ+) (hp : (P : ℕ).Prime) (hpN : ¬ (P : ℕ) ∣ 4 * 1)

lemma sum_eq_repsIntegral (Φ : ℍ → ℂ) :
    ∑ i : Fin gamma0FourReps.length, ∑ x, ∫ τ in ModularGroup.fd,
        Φ (((r0 P hp hpN)⁻¹ * rep 1 P hp hpN x * gamma0FourReps[i.1]) • τ) =
      repsIntegral ((Finset.univ : Finset (Idx P)).toList.map (conjRep P hp hpN)) Φ := by
  rw [repsIntegral, List.map_map, Finset.sum_map_toList, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

include hp in
lemma integrableOn_fBeta {f g : ℍ → ℂ} (hf : f ∈ thetaMultiplierSystem.cuspForms k 1 1)
    (hg : g ∈ thetaMultiplierSystem.cuspForms k 1 1) (γ : SL(2, ℤ)) :
    IntegrableOn (fun τ ↦ pInt k (fBeta P f) g (γ • τ)) ModularGroup.fd :=
  thetaMultiplierSystem.integrableOn_peterssonIntegrand k ((P : ℕ) ^ 2) (by positivity) 1
    (fBeta_mem_cuspForms k P hp hf) (mem_cuspForms_sq thetaMultiplierSystem k P hg) γ

include hp in
lemma integrableOn_fBeta' {f g : ℍ → ℂ} (hf : f ∈ thetaMultiplierSystem.cuspForms k 1 1)
    (hg : g ∈ thetaMultiplierSystem.cuspForms k 1 1) (γ : SL(2, ℤ)) :
    IntegrableOn (fun τ ↦ pInt k f (fBeta P g) (γ • τ)) ModularGroup.fd :=
  thetaMultiplierSystem.integrableOn_peterssonIntegrand k ((P : ℕ) ^ 2) (by positivity) 1
    (mem_cuspForms_sq thetaMultiplierSystem k P hf) (fBeta_mem_cuspForms k P hp hg) γ

lemma reps_left {f g : ℍ → ℂ} (hf : f ∈ thetaMultiplierSystem.cuspForms k 1 1)
    (hg : g ∈ thetaMultiplierSystem.cuspForms k 1 1) :
    ((P : ℕ) : ℂ) ^ 2 * peterssonReps gamma0FourReps ((k : ℝ) + 1 / 2) (heckeFun k 1 1 P f) g =
      ((P : ℕ) : ℂ) ^ (2 * k + 1) *
        repsIntegral ((Finset.univ : Finset (Idx P)).toList.map (conjRep P hp hpN)) (pInt k (fBeta P f) g) := by
  rw [peterssonReps_eq_sum, Finset.mul_sum, ← sum_eq_repsIntegral P hp hpN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← integral_const_mul]
  simp_rw [pInt_heckeFun_left k P hp hpN hf.transforms hg.transforms]
  rw [integral_const_mul]
  simp_rw [← mul_smul]
  rw [integral_finsetSum _ fun x _ ↦ integrableOn_fBeta k P hp hf hg _]

lemma reps_right {f g : ℍ → ℂ} (hf : f ∈ thetaMultiplierSystem.cuspForms k 1 1)
    (hg : g ∈ thetaMultiplierSystem.cuspForms k 1 1) :
    ((P : ℕ) : ℂ) ^ 2 * peterssonReps gamma0FourReps ((k : ℝ) + 1 / 2) f (heckeFun k 1 1 P g) =
      ((P : ℕ) : ℂ) ^ (2 * k + 1) *
        repsIntegral ((Finset.univ : Finset (Idx P)).toList.map (conjRep P hp hpN)) (pInt k f (fBeta P g)) := by
  rw [peterssonReps_eq_sum, Finset.mul_sum, ← sum_eq_repsIntegral P hp hpN, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← integral_const_mul]
  simp_rw [pInt_heckeFun_right k P hp hpN hf.transforms hg.transforms]
  rw [integral_const_mul]
  simp_rw [← mul_smul]
  rw [integral_finsetSum _ fun x _ ↦ integrableOn_fBeta' k P hp hf hg _]

include hp hpN in
/-- **$T(p^2)$, $p$ odd, is self-adjoint on $S_{k+1/2}(4)$** for the Petersson product `peterssonFour` (theta
multiplier, trivial character). -/
theorem peterssonFour_heckeFun {f g : ℍ → ℂ} (hf : f ∈ thetaMultiplierSystem.cuspForms k 1 1)
    (hg : g ∈ thetaMultiplierSystem.cuspForms k 1 1) :
    peterssonFour k (heckeFun k 1 1 P f) g = peterssonFour k f (heckeFun k 1 1 P g) := by
  have : NeZero (4 * (P : ℕ) ^ 2) := ⟨by positivity⟩
  set R := (Finset.univ : Finset (Idx P)).toList.map (conjRep P hp hpN)
  have hR := isGamma0Reps_conjReps P hp hpN
  have hinv : ∀ γ ∈ Gamma0 (4 * (P : ℕ) ^ 2), ∀ z : ℍ, pInt k (fBeta P f) g (γ • z) = pInt k (fBeta P f) g z :=
    fun γ hγ z ↦ pInt_invariant thetaMultiplierSystem k ((P : ℕ) ^ 2) (fBeta_transforms k P hp hf.transforms)
      (mem_cuspForms_sq thetaMultiplierSystem k P hg).transforms hγ z
  have hint := ChangeOfVariables.integrableOn_gamma0Domain hR hinv
    (fun γ _ ↦ integrableOn_fBeta k P hp hf hg γ)
  have hcv := ChangeOfVariables.repsIntegral_comp_smul hR (conjAct_normalizer P hp hpN) _ hinv hint
  have hΦ : repsIntegral R (pInt k f (fBeta P g)) = repsIntegral R (pInt k (fBeta P f) g) := by
    rw [← hcv]
    congr 1
    funext z
    exact (pInt_fBeta_Mmat k P hp hpN hf.transforms hg.transforms z).symm
  have hL := reps_left k P hp hpN hf hg
  have hRt := reps_right k P hp hpN hf hg
  rw [hΦ, ← hL] at hRt
  have hP2 : ((P : ℕ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr P.ne_zero)
  rw [peterssonFour, peterssonFour, mul_left_cancel₀ hP2 hRt]

end Assembly

/-- **The named input `PlusHeckeSelfAdjoint` holds for every $k$** (LE-MF-0269): $T(p^2)$, $p$ odd, is self-adjoint on
Kohnen's plus space, indeed on all of $S_{k+1/2}(4)$. -/
theorem plusHeckeSelfAdjoint (k : ℕ) : PlusHeckeSelfAdjoint k := by
  refine ⟨fun {p} hp hp2 g₁ g₂ g₁' g₂' c₁ c₂ h1 h2 _ _ hc1 hc2 hc1' hc2' ↦ ?_⟩
  have hnd : ¬ p ∣ 4 * 1 := by
    intro h
    have h4 : p ∣ 2 ^ 2 := by simpa using h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
  have e1 : g₁' = heckeFun k 1 1 ⟨p, hp.pos⟩ g₁ := by
    have := hasQExp_heckeOpCusp k 1 1 hp hnd ⟨g₁, h1.1⟩ hc1
    rw [coe_heckeOpCusp] at this
    funext τ
    exact (hc1' τ).unique (this τ)
  have e2 : g₂' = heckeFun k 1 1 ⟨p, hp.pos⟩ g₂ := by
    have := hasQExp_heckeOpCusp k 1 1 hp hnd ⟨g₂, h2.1⟩ hc2
    rw [coe_heckeOpCusp] at this
    funext τ
    exact (hc2' τ).unique (this τ)
  rw [e1, e2]
  exact PlusHeckeAdjoint.peterssonFour_heckeFun k ⟨p, hp.pos⟩ hp hnd h1.1 h2.1

end PlusHeckeAdjoint

end ModularFormsKB.HalfIntegral
