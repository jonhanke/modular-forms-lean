/-
# The Fricke-side Rankin integral, unfolded at every cusp of $\Gamma_0(L)$

`ShimuraFrickeKernelUnfolding` (LE-MF-0285) is an identity for the Fricke-side dual integral
$$\texttt{frickeKernelIntegral} = \sum_{\rho\in R}\int_{\mathcal F}G(\rho\tau)\,E^{\mathrm{prim}}(\rho\tau,s)\,d\mu,\qquad
G(z) = K(z)\,L^s\Big(\frac{|z|}{z}\Big)^\lambda,$$
$K$ = `frickeKernel`, $L = 16Ntr^2$, $\lambda = k-\nu$. This file unfolds it at all cusps of $\Gamma_0(L)$ at once.

1. $E^{\mathrm{prim}} = E^G$ (`DualFricke.eisensteinGauss_eq_sum`) is the full-lattice series (`CosetUnfold.latticeSeries`)
   with the coefficients $\Phi(C,D) = [L\mid C]\,G(\omega_0,D)$ (`gaussPhi`, `eisensteinGauss_eq_latticeSeries`), which
   satisfy $\Phi(p\gamma) = \bar\omega_0(d_\gamma)\Phi(p)$ on $\Gamma_0(L)$ (`gaussPhi_rowAct`).
2. $G(z) = K_0(W_Lz)\,L^s(|z|/z)^\lambda$ with $K_0$ = `rankinKernel` (`rankinKernel_fricke`), so $G$ has the unitary
   weight-$\lambda$ law with the character $\bar\omega_0$ (`unitaryLaw_fricke`: $W_L\gamma = \gamma'W_L$ with
   $\gamma' = \begin{pmatrix}d&-c/L\\-Lb&a\end{pmatrix}$, and the factors in $z$ match).
3. The integrand is integrable on every $\rho\mathcal F$ (from `integrableOn_rankinDualIntegrand` and the Fricke change of
   variables, `integrableOn_fd_of_gamma0Domain`).

With `CosetUnfold.repsIntegral_mul_latticeSeries` this gives (`frickeKernelIntegral_eq_cosetSum`)
$$\texttt{frickeKernelIntegral}(s) = \sum_{\rho\in R}c_\rho(s)\,\int_0^\infty\!\!\int_0^1
  \Big(\frac{|j_\rho|}{j_\rho}\Big)^\lambda G(\rho z)\,y^{s-2}\,dx\,dy\qquad(\operatorname{Re}s>1),$$
$c_\rho(s) = \sum_{n\ge1}n^{-2s}(\Phi(n\,r_\rho)+(-1)^\lambda\Phi(-n\,r_\rho))$, $r_\rho = (0,1)\rho^{-1}$: for the coset of the cusp
$\rho\infty = a/c$, $c_\rho(s) = \sum_{n\ge1,\,L\mid nc}n^{-2s}(G(\omega_0,na)+(-1)^\lambda G(\omega_0,-na))$.

**Index shift.** Matrix entries are 0-based.
-/
import ModularFormsKB.HalfIntegral.Rankin.CosetUnfolding
import ModularFormsKB.HalfIntegral.Rankin.FrickeKernel
import ModularFormsKB.HalfIntegral.Rankin.DecayStrip
import ModularFormsKB.HalfIntegral.HeckeCusp

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup MeasureTheory Set
open scoped Real Pointwise

local notation "ℍ" => UpperHalfPlane

namespace FrickeCoset

open DualReps CosetUnfold

/-! ### The Gauss-sum coefficients -/

/-- **The coefficients of $E^G$ on the full lattice:** $\Phi(C,D) = G(\omega,D)$ if $L \mid C$, else $0$. -/
noncomputable def gaussPhi (L : ℕ) (ω : DirichletCharacter ℂ L) (p : ℤ × ℤ) : ℂ :=
  if (L : ℤ) ∣ p.1 then gaussAt L ω p.2 else 0

lemma norm_gaussAt_le (L : ℕ) (ω : DirichletCharacter ℂ L) (m : ℤ) : ‖gaussAt L ω m‖ ≤ L := by
  unfold gaussAt
  refine (norm_sum_le _ _).trans ?_
  have : ∀ a ∈ Finset.range L, ‖ω a * cexp (2 * π * I * a * m / L)‖ ≤ 1 := by
    intro a _
    rw [norm_mul]
    have h1 := DirichletCharacter.norm_le_one ω (a : ZMod L)
    have h2 : ‖cexp (2 * π * I * a * m / L)‖ = 1 := by
      rw [Complex.norm_exp]
      have : (2 * π * I * a * m / L : ℂ).re = 0 := by
        simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
      rw [this, Real.exp_zero]
    rw [h2, mul_one]
    exact_mod_cast h1
  calc ∑ a ∈ Finset.range L, ‖ω a * cexp (2 * π * I * a * m / L)‖ ≤ ∑ a ∈ Finset.range L, (1 : ℝ) :=
        Finset.sum_le_sum this
    _ = L := by simp

lemma norm_gaussPhi_le (L : ℕ) (ω : DirichletCharacter ℂ L) (p : ℤ × ℤ) : ‖gaussPhi L ω p‖ ≤ L := by
  unfold gaussPhi
  split_ifs
  · exact norm_gaussAt_le L ω p.2
  · simp

/-- **The law of the coefficients:** $\Phi(p\gamma) = \bar\omega(d_\gamma)\Phi(p)$ for $\gamma \in \Gamma_0(L)$. -/
lemma gaussPhi_rowAct {L : ℕ} (hL : 1 ≤ L) (ω : DirichletCharacter ℂ L) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 L)
    (p : ℤ × ℤ) : gaussPhi L ω (rowAct γ p) = ω⁻¹ (γ 1 1 : ZMod L) * gaussPhi L ω p := by
  obtain ⟨q, hq⟩ := RankinUnfold.dvd_of_mem_Gamma0 hγ
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  have hu := isUnit_d hγ
  -- `L ∣ p₁ a + p₂ c` iff `L ∣ p₁`
  have hdvd : (L : ℤ) ∣ (rowAct γ p).1 ↔ (L : ℤ) ∣ p.1 := by
    rw [rowAct_apply]
    simp only
    constructor
    · intro h
      -- `p₁ = (p₁ a + p₂ c) d - p₁ b c - p₂ c d`
      have : p.1 = (p.1 * γ 0 0 + p.2 * γ 1 0) * γ 1 1 - (L : ℤ) * (q * (p.1 * γ 0 1 + p.2 * γ 1 1)) := by
        linear_combination (-p.1) * hdet + (-(p.1 * γ 0 1 + p.2 * γ 1 1)) * hq
      rw [this]
      exact dvd_sub (dvd_mul_of_dvd_left h _) (dvd_mul_right _ _)
    · intro h
      exact dvd_add (dvd_mul_of_dvd_left h _) (by rw [hq]; exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
  unfold gaussPhi
  by_cases h : (L : ℤ) ∣ p.1
  · simp only [hdvd.2 h, h, ↓reduceIte]
    obtain ⟨e, he⟩ := h
    have hcong : (rowAct γ p).2 ≡ p.2 * γ 1 1 [ZMOD L] := by
      rw [rowAct_apply]
      apply Int.modEq_iff_dvd.2
      exact ⟨-(e * γ 0 1), by simp only; rw [he]; ring⟩
    rw [gaussAt_congr hL ω hcong]
    have h2 := gaussAt_mul hL ω p.2 (γ 1 1) hu
    have hne : ω (γ 1 1 : ZMod L) ≠ 0 := (hu.map ω).ne_zero
    rw [MulChar.inv_apply_eq_inv', ← h2]
    field_simp
  · simp only [show ¬ (L : ℤ) ∣ (rowAct γ p).1 from fun h' ↦ h (hdvd.1 h'), h, ↓reduceIte, mul_zero]

/-- **$E^G$ is the full-lattice series with the coefficients `gaussPhi`.** -/
theorem eisensteinGauss_eq_latticeSeries {L : ℕ} [NeZero L] (lam : ℕ) (ω : DirichletCharacter ℂ L) (z : ℍ)
    (s : ℂ) : DualFricke.eisensteinGauss L lam ω z s = latticeSeries lam (gaussPhi L ω) z s := by
  unfold DualFricke.eisensteinGauss latticeSeries
  congr 1
  have hL0 : (L : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne L
  set g : ℤ × ℤ → ℤ × ℤ := fun p ↦ ((L : ℤ) * p.1, p.2) with hg
  have hinj : Function.Injective g := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [hg, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    simp [mul_left_cancel₀ hL0 h1, h2]
  have hsupp : Function.support (fun p : ℤ × ℤ ↦ gaussPhi L ω p * eisTerm lam s ((p.1 : ℂ) * z + p.2)) ⊆
      Set.range g := by
    intro p hp
    simp only [Function.mem_support, gaussPhi] at hp
    by_cases h : (L : ℤ) ∣ p.1
    · obtain ⟨e, he⟩ := h
      exact ⟨(e, p.2), Prod.ext he.symm rfl⟩
    · simp [h] at hp
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun p ↦ ?_
  simp only [hg, gaussPhi, dvd_mul_right, ite_true]
  push_cast
  ring_nf

/-! ### The law of the Fricke-side kernel -/

lemma coe_fricke_smul' {L : ℕ} [NeZero L] (z : ℍ) :
    ((TauCeti.frickeGL ℝ L • z : ℍ) : ℂ) = -1 / ((L : ℂ) * z) := DualFricke.coe_fricke_smul z

/-- **The kernel after $W_L$ keeps a unitary law**, with the inverse character: if $K$ has the unitary weight-$\lambda$
law with $\omega$ on $\Gamma_0(L)$, then $z \mapsto K(W_Lz)\,c\,(|z|/z)^\lambda$ has it with $\bar\omega$. -/
theorem unitaryLaw_fricke {L lam : ℕ} [NeZero L] {ω : DirichletCharacter ℂ L} {K : ℍ → ℂ}
    (hK : UnitaryLaw L lam ω K) (c : ℂ) :
    UnitaryLaw L lam ω⁻¹ (fun z ↦ K (TauCeti.frickeGL ℝ L • z) * (c * (((‖(z : ℂ)‖ : ℝ) : ℂ) / z) ^ lam)) := by
  intro γ hγ z
  set γ' := TauCeti.frickeConjSL (⟨γ, hγ⟩ : Gamma0 L) with hγ'def
  have hγ' : γ' ∈ Gamma0 L := TauCeti.frickeConjSL_mem_Gamma0 _
  have hW : TauCeti.frickeGL ℝ L • (γ • z) = γ' • (TauCeti.frickeGL ℝ L • z) := by
    have h := TauCeti.frickeGL_mul_mapGL ℝ (⟨γ, hγ⟩ : Gamma0 L)
    calc TauCeti.frickeGL ℝ L • (γ • z) = (TauCeti.frickeGL ℝ L * Matrix.SpecialLinearGroup.mapGL ℝ γ) • z := by rw [mul_smul]; rfl
      _ = (Matrix.SpecialLinearGroup.mapGL ℝ γ' * TauCeti.frickeGL ℝ L) • z := by rw [h]
      _ = γ' • (TauCeti.frickeGL ℝ L • z) := by rw [mul_smul]; rfl
  have h10 : γ' 1 0 = -(L : ℤ) * γ 0 1 := by simp [hγ'def, TauCeti.frickeConjSL]
  have h11 : γ' 1 1 = γ 0 0 := by simp [hγ'def, TauCeti.frickeConjSL]
  simp only
  rw [hW, hK γ' hγ', h10, h11]
  -- the characters
  have hω : ω (γ 0 0 : ZMod L) = ω⁻¹ (γ 1 1 : ZMod L) := by
    have h := char_d_mul_d_inv ω hγ
    have hinv : (γ⁻¹ : SL(2, ℤ)) 1 1 = γ 0 0 := by simp
    rw [hinv] at h
    rw [MulChar.inv_apply_eq_inv']
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h)
  rw [hω]
  -- the factors in `z`
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne L
  set a : ℂ := ((γ 0 0 : ℤ) : ℂ)
  set b : ℂ := ((γ 0 1 : ℤ) : ℂ)
  set u : ℂ := a * z + b with hu
  set v : ℂ := ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) with hv
  have hv0 : v ≠ 0 := by rw [hv, ← denom_SL_eq]; exact UpperHalfPlane.denom_ne_zero _ z
  have hγz : ((γ • z : ℍ) : ℂ) = u / v := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [hu, hv, a, b]
  have hu0 : u ≠ 0 := by
    intro h0
    have := (γ • z).ne_zero
    rw [hγz, h0, zero_div] at this
    exact this rfl
  have hj : (((-(L : ℤ) * γ 0 1 : ℤ) : ℂ) * ((TauCeti.frickeGL ℝ L • z : ℍ) : ℂ) + a) = u / z := by
    rw [coe_fricke_smul']
    push_cast
    field_simp
    rw [hu]
    ring
  rw [hj, hγz]
  have hnu : 0 < ‖u‖ := norm_pos_iff.2 hu0
  have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have hnz : 0 < ‖(z : ℂ)‖ := norm_pos_iff.2 hz
  have key : (u / z / ((‖u / z‖ : ℝ) : ℂ)) * (((‖u / v‖ : ℝ) : ℂ) / (u / v)) =
      (v / ((‖v‖ : ℝ) : ℂ)) * (((‖(z : ℂ)‖ : ℝ) : ℂ) / z) := by
    rw [norm_div, norm_div]
    push_cast
    have h1 : ((‖u‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnu.ne'
    have h2 : ((‖v‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnv.ne'
    have h3 : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnz.ne'
    field_simp
  have key' : (u / z / ((‖u / z‖ : ℝ) : ℂ)) ^ lam * (((‖u / v‖ : ℝ) : ℂ) / (u / v)) ^ lam =
      (v / ((‖v‖ : ℝ) : ℂ)) ^ lam * (((‖(z : ℂ)‖ : ℝ) : ℂ) / z) ^ lam := by
    rw [← mul_pow, key, mul_pow]
  linear_combination (ω⁻¹ (γ 1 1 : ZMod L) * K (TauCeti.frickeGL ℝ L • z) * c) * key'

/-! ### Integrability on the translates of the fundamental domain -/

/-- **$W_L\gamma = \gamma'W_L$** on $\mathbb H$, $\gamma' = $ `TauCeti.frickeConjSL γ` $\in \Gamma_0(L)$. -/
lemma fricke_smul_comm {L : ℕ} [NeZero L] {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 L) (z : ℍ) :
    TauCeti.frickeGL ℝ L • (γ • z) = TauCeti.frickeConjSL (⟨γ, hγ⟩ : Gamma0 L) • (TauCeti.frickeGL ℝ L • z) := by
  have h := TauCeti.frickeGL_mul_mapGL ℝ (⟨γ, hγ⟩ : Gamma0 L)
  calc TauCeti.frickeGL ℝ L • (γ • z)
      = (TauCeti.frickeGL ℝ L * Matrix.SpecialLinearGroup.mapGL ℝ γ) • z := by rw [mul_smul]; rfl
    _ = (Matrix.SpecialLinearGroup.mapGL ℝ (TauCeti.frickeConjSL (⟨γ, hγ⟩ : Gamma0 L)) *
          TauCeti.frickeGL ℝ L) • z := by rw [h]
    _ = _ := by rw [mul_smul]; rfl

/-- Integrability of an invariant function on every translate $\rho\mathcal F$ from integrability on $D_L$. -/
lemma integrableOn_fd_of_gamma0Domain {L : ℕ} [NeZero L] {h : ℍ → ℂ}
    (hh : ∀ γ ∈ Gamma0 L, ∀ z, h (γ • z) = h z) (hint : IntegrableOn h (ChangeOfVariables.gamma0Domain L))
    (ρ : SL(2, ℤ)) : IntegrableOn (fun τ ↦ h (ρ • τ)) ModularGroup.fd := by
  set q : SL(2, ℤ) ⧸ (Gamma0 L).withCenter := QuotientGroup.mk ρ⁻¹ with hqdef
  have hq : IntegrableOn h ((q.out)⁻¹ • (ModularGroup.fdo : Set ℍ)) :=
    hint.mono_set (Set.subset_iUnion (fun q : SL(2, ℤ) ⧸ (Gamma0 L).withCenter ↦
      (q.out)⁻¹ • (ModularGroup.fdo : Set ℍ)) q)
  rw [ModularGroup.sl_smul_set, ChangeOfVariables.integrableOn_GL_smul] at hq
  have hq' : IntegrableOn (fun τ ↦ h (((q.out)⁻¹ : SL(2, ℤ)) • τ)) (ModularGroup.fdo : Set ℍ) := hq
  have hmem : ρ * q.out ∈ Gamma0 L := by
    have hw : ∀ g : SL(2, ℤ), g ∈ (Gamma0 L).withCenter ↔ g ∈ Gamma0 L := fun g ↦ by
      rw [RankinUnfold.withCenter_Gamma0]
    have h1 := (hw _).1 (QuotientGroup.eq.mp ((QuotientGroup.out_eq' q).trans hqdef))
    have := Subgroup.inv_mem _ h1
    simpa [mul_inv_rev] using this
  have heq : ∀ τ, h (((q.out)⁻¹ : SL(2, ℤ)) • τ) = h (ρ • τ) := by
    intro τ
    have : (q.out)⁻¹ = (ρ * q.out)⁻¹ * ρ := by group
    rw [this, mul_smul, hh _ (Subgroup.inv_mem _ hmem)]
  simp_rw [heq] at hq'
  exact hq'.congr_set_ae ModularGroup.fd_ae_eq_fdo

/-- **Integrability after the Fricke involution:** an invariant function integrable on $D_L$ stays so after $W_L$. -/
lemma integrableOn_gamma0Domain_fricke {L : ℕ} [NeZero L] {h : ℍ → ℂ}
    (hh : ∀ γ ∈ Gamma0 L, ∀ z, h (γ • z) = h z) (hint : IntegrableOn h (ChangeOfVariables.gamma0Domain L)) :
    IntegrableOn (fun z ↦ h (TauCeti.frickeGL ℝ L • z)) (ChangeOfVariables.gamma0Domain L) ∧
      ∀ γ ∈ Gamma0 L, ∀ z, h (TauCeti.frickeGL ℝ L • (γ • z)) = h (TauCeti.frickeGL ℝ L • z) := by
  have hD := ChangeOfVariables.isFundamentalDomain_gamma0Domain L
  have hαD := ModularGroup.isFundamentalDomain_smul_of_inv_conjAct_eq
    (ChangeOfVariables.gamma0_map_inv_conjAct_frickeGL_eq L) hD
  refine ⟨?_, fun γ hγ z ↦ ?_⟩
  · rw [← ChangeOfVariables.integrableOn_GL_smul]
    exact (hD.integrableOn_iff hαD (ChangeOfVariables.hinvG hh)).1 hint
  · rw [fricke_smul_comm hγ, hh _ (TauCeti.frickeConjSL_mem_Gamma0 _)]

/-! ### The unfolded Fricke-side integral -/

/-- **The Fricke-side kernel** $G(z) = K(z)\,L^s(|z|/z)^\lambda$, $K$ = `frickeKernel`, $\lambda = k-\nu$. -/
noncomputable def frickeG (k N t : ℕ) {r : ℕ} (ψ : DirichletCharacter ℂ r) (f : ℍ → ℂ) (s : ℂ) (z : ℍ) : ℂ :=
  frickeKernel k N t ψ f z * ((rankinLevel N t r : ℂ) ^ s * (((‖(z : ℂ)‖ : ℝ) : ℂ) / z) ^ (k - charParity ψ))

/-- **The sum over the cosets** $\sum_{\rho\in R}c_\rho(s)\int_0^\infty\!\int_0^1(|j_\rho|/j_\rho)^\lambda G(\rho z)y^{s-2}$,
with $c_\rho$ = `CosetUnfold.cosetCoeff` for the coefficients `gaussPhi` of the Rankin character. -/
noncomputable def frickeCosetSum (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ) {r : ℕ}
    (ψ : DirichletCharacter ℂ r) (f : ℍ → ℂ) (R : List SL(2, ℤ)) (s : ℂ) : ℂ :=
  (R.map fun ρ ↦ cosetCoeff (k - charParity ψ) (gaussPhi (rankinLevel N t r) (rankinChar k N χ t ψ)) ρ s *
    stripMellin (fun v ↦ uFac (k - charParity ψ) ρ v * frickeG k N t ψ f s (ρ • v)) s).sum

/-- **The Fricke-side integral unfolded at every cusp, conditional on the strip integrability of the kernel at each
coset:** for $f$ a cusp form, $r = 1$ or an odd prime, $\psi$ primitive, $\nu < k$ and $\operatorname{Re}s > 1$,
`frickeKernelIntegral` = `frickeCosetSum`. -/
theorem frickeKernelIntegral_eq_cosetSum_of_strip (M : MultiplierSystem) (hT : ThetaTwistLaw M) {k N : ℕ}
    (hN : 0 < N) {χ : DirichletCharacter ℂ (4 * N)} {f : ℍ → ℂ} (hf : f ∈ M.cuspForms k N χ) {t : ℕ} (ht : 1 ≤ t)
    {r : ℕ} (hr : r = 1 ∨ (r.Prime ∧ r ≠ 2)) [NeZero r] [NeZero (rankinLevel N t r)]
    {ψ : DirichletCharacter ℂ r} (hψ : ψ.IsPrimitive) (hk : charParity ψ < k) {R : List SL(2, ℤ)}
    (hR : IsGamma0Reps (rankinLevel N t r) R) {s : ℂ} (hs : 1 < s.re)
    (hstrip : ∀ ρ ∈ R, IntegrableOn (fun p : ℝ × ℝ ↦ ‖frickeG k N t ψ f s (ρ • stripPt p.1 p.2)‖ *
      p.2 ^ (s.re - 2)) (Icc 0 1 ×ˢ Ioi 0)) :
    frickeKernelIntegral k N χ t ψ f R s = frickeCosetSum k N χ t ψ f R s := by
  set L := rankinLevel N t r with hLdef
  set lam := k - charParity ψ with hlamdef
  set ω := rankinChar k N χ t ψ with hωdef
  have hlam : 1 ≤ lam := by omega
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hfT : M.Transforms k N χ f := (show M.IsCuspForm k N χ f from hf).transforms
  -- `G = K₀ ∘ W_L` times the factors
  have hGeq : frickeG k N t ψ f s = fun z ↦ rankinKernel k ψ t f (TauCeti.frickeGL ℝ L • z) *
      ((L : ℂ) ^ s * (((‖(z : ℂ)‖ : ℝ) : ℂ) / z) ^ lam) := by
    funext z
    rw [frickeG, rankinKernel_fricke hN ht hψ f z]
  have hU : UnitaryLaw L lam ω⁻¹ (frickeG k N t ψ f s) := by
    rw [hGeq]
    exact unitaryLaw_fricke (unitaryLaw_rankinKernel M hT hfT ht hr ψ hk.le) _
  have hGc : Continuous (frickeG k N t ψ f s) := by
    rw [hGeq]
    have hz : Continuous fun z : ℍ ↦ (((‖(z : ℂ)‖ : ℝ) : ℂ) / z) ^ lam :=
      ((Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_coe.norm)).div UpperHalfPlane.continuous_coe
        fun z ↦ z.ne_zero).pow lam
    exact ((continuous_rankinKernel k ψ ht (show M.IsCuspForm k N χ f from hf).holo.continuous).comp
      (continuous_const_smul _)).mul (continuous_const.mul hz)
  -- the integrand
  have hpt : ∀ z, frickeKernel k N t ψ f z * ((L : ℂ) ^ s * (((‖(z : ℂ)‖ : ℝ) : ℂ) / z) ^ lam *
      DualFricke.eisensteinPrimSum L lam ω z s) = frickeG k N t ψ f s z * latticeSeries lam (gaussPhi L ω) z s := by
    intro z
    rw [← DualFricke.eisensteinGauss_eq_sum hlam ω z hs, eisensteinGauss_eq_latticeSeries, frickeG]
    ring
  have hdual : ∀ z, frickeG k N t ψ f s z * latticeSeries lam (gaussPhi L ω) z s =
      (fun τ ↦ rankinKernel k ψ t f τ * eisensteinDual L lam ω τ s) (TauCeti.frickeGL ℝ L • z) := by
    intro z
    rw [hGeq]
    simp only
    rw [DualFricke.eisensteinDual_fricke hlam, ← eisensteinGauss_eq_latticeSeries]
    ring
  have hinv := fun γ hγ τ ↦ DualReps.rankinDualIntegrand_smul M hT hN hfT ht hr ψ hk s (γ := γ) hγ τ
  have hint := FrickeReduction.integrableOn_rankinDualIntegrand M hT hN hf ht hr ψ hk hs
  obtain ⟨hintW, hinvW⟩ := integrableOn_gamma0Domain_fricke hinv hint
  have hfd : ∀ ρ ∈ R, IntegrableOn (fun τ ↦ frickeG k N t ψ f s (ρ • τ) *
      latticeSeries lam (gaussPhi L ω) (ρ • τ) s) ModularGroup.fd := by
    intro ρ _
    simp_rw [hdual]
    exact integrableOn_fd_of_gamma0Domain hinvW hintW ρ
  unfold frickeKernelIntegral frickeCosetSum
  rw [repsIntegral_congr R hpt]
  exact repsIntegral_mul_latticeSeries hlam hR hGc hU (fun γ hγ p ↦ gaussPhi_rowAct hL1 ω hγ p)
    (norm_gaussPhi_le L ω) hs hfd hstrip

/-! ### Integrability on the strip -/

lemma stripPt_im_pos {x y : ℝ} (hy : 0 < y) : (stripPt x y).im = y := by
  simp only [stripPt, hy, ↓reduceDIte]
  show ((x : ℂ) + y * I).im = y
  simp

lemma stripPt_re_pos {x y : ℝ} (hy : 0 < y) : ((stripPt x y : ℍ) : ℂ).re = x := by
  simp only [stripPt, hy, ↓reduceDIte]
  show ((x : ℂ) + y * I).re = x
  simp

lemma continuousOn_stripPt :
    ContinuousOn (fun p : ℝ × ℝ ↦ stripPt p.1 p.2) {p : ℝ × ℝ | 0 < p.2} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : Continuous (fun p : {p : ℝ × ℝ | 0 < p.2} ↦
      (⟨((p.1.1 : ℝ) : ℂ) + (p.1.2 : ℝ) * I, by
        have : 0 < p.1.2 := p.2
        simpa using this⟩ : ℍ)) :=
    UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr (by
      show Continuous fun p : {p : ℝ × ℝ | 0 < p.2} ↦ ((p.1.1 : ℝ) : ℂ) + (p.1.2 : ℝ) * I
      fun_prop)
  convert h using 1
  funext p
  have hp : 0 < p.1.2 := p.2
  simp [Set.domRestrict, stripPt, hp]

/-- **Integrability on the strip from a bound and polynomial decay:** if $F$ is continuous, $|F| \le B$, and
$|F(x+iy)| \le C y^{-\sigma}$ for $0 \le x \le 1$, $y \ge Y > 0$, then $\int_0^\infty\!\int_0^1|F|y^{\sigma-2} < \infty$
for $\sigma > 1$. -/
theorem integrableOn_strip_of_bound {F : ℍ → ℂ} (hF : Continuous F) {σ : ℝ} (hσ : 1 < σ) {B C Y : ℝ}
    (hY : 0 < Y) (hB : ∀ z, ‖F z‖ ≤ B)
    (hdec : ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → Y ≤ y → ‖F (stripPt x y)‖ ≤ C * y ^ (-σ)) :
    IntegrableOn (fun p : ℝ × ℝ ↦ ‖F (stripPt p.1 p.2)‖ * p.2 ^ (σ - 2)) (Icc 0 1 ×ˢ Ioi 0) := by
  set H : ℝ → ℝ := fun y ↦ |B| * (Ioc (0 : ℝ) Y).indicator (fun y ↦ y ^ (σ - 2)) y +
    |C| * (Ioi Y).indicator (fun y ↦ y ^ (-2 : ℝ)) y with hH
  have hI1 : Integrable ((Ioc (0 : ℝ) Y).indicator (fun y ↦ y ^ (σ - 2))) volume := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := Y) (r := σ - 2) (by linarith))
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hY.le] at this
  have hI2 : Integrable ((Ioi Y).indicator (fun y : ℝ ↦ y ^ (-2 : ℝ))) volume := by
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact integrableOn_Ioi_rpow_of_lt (by norm_num) hY
  have hHint : Integrable H (volume.restrict (Ioi (0 : ℝ))) :=
    ((hI1.integrableOn.const_mul |B|).add (hI2.integrableOn.const_mul |C|))
  have hprod : IntegrableOn (fun p : ℝ × ℝ ↦ H p.2) (Icc 0 1 ×ˢ Ioi 0) := by
    have := (integrable_const (1 : ℝ) (μ := volume.restrict (Icc (0 : ℝ) 1))).mul_prod hHint
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    simpa using this
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ ‖F (stripPt p.1 p.2)‖ * p.2 ^ (σ - 2)) (volume.restrict (Icc 0 1 ×ˢ Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Icc.prod measurableSet_Ioi)
    refine ContinuousOn.mono (s := {p : ℝ × ℝ | 0 < p.2}) ?_ (fun p hp ↦ ?_)
    · exact ((hF.comp_continuousOn continuousOn_stripPt).norm).mul
        ((continuous_snd.continuousOn).rpow_const (fun p hp ↦ Or.inl (ne_of_gt hp)))
    · exact hp.2
  refine Integrable.mono' hprod hmeas ?_
  refine (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Ioi)).2 (Filter.Eventually.of_forall ?_)
  rintro ⟨x, y⟩ ⟨⟨hx0, hx1⟩, hy⟩
  have hy : 0 < y := hy
  have hFn := norm_nonneg (F (stripPt x y))
  rw [Real.norm_of_nonneg (by positivity)]
  simp only [hH]
  by_cases hyY : y ≤ Y
  · rw [Set.indicator_of_mem (show y ∈ Ioc (0 : ℝ) Y from ⟨hy, hyY⟩),
      Set.indicator_of_notMem (show y ∉ Ioi Y from fun h ↦ absurd (h : Y < y) (not_lt.2 hyY)), mul_zero,
      add_zero]
    exact mul_le_mul_of_nonneg_right ((hB _).trans (le_abs_self B)) (by positivity)
  · rw [not_le] at hyY
    rw [Set.indicator_of_notMem (show y ∉ Ioc (0 : ℝ) Y from fun h ↦ absurd h.2 (not_le.2 hyY)),
      Set.indicator_of_mem (show y ∈ Ioi Y from hyY), mul_zero, zero_add]
    have h1 := hdec x y hx0 hx1 hyY.le
    have h2 : y ^ (-σ) * y ^ (σ - 2) = y ^ (-2 : ℝ) := by rw [← Real.rpow_add hy]; ring_nf
    calc ‖F (stripPt x y)‖ * y ^ (σ - 2) ≤ (C * y ^ (-σ)) * y ^ (σ - 2) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = C * y ^ (-2 : ℝ) := by rw [mul_assoc, h2]
      _ ≤ |C| * y ^ (-2 : ℝ) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)

/-! ### The Rankin kernel is bounded, and decays at every cusp after `W_L` -/

lemma norm_rankinKernel_smul (M : MultiplierSystem) (hT : ThetaTwistLaw M) {k N : ℕ}
    {χ : DirichletCharacter ℂ (4 * N)} {f : ℍ → ℂ} (hf : M.Transforms k N χ f) {t : ℕ} (ht : 1 ≤ t) {r : ℕ}
    (hr : r = 1 ∨ (r.Prime ∧ r ≠ 2)) (ψ : DirichletCharacter ℂ r) (hk : charParity ψ ≤ k)
    {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 (rankinLevel N t r)) (z : ℍ) :
    ‖rankinKernel k ψ t f (δ • z)‖ = ‖rankinKernel k ψ t f z‖ := by
  rw [unitaryLaw_rankinKernel M hT hf ht hr ψ hk δ hδ z, norm_mul, norm_mul]
  have h1 : ‖rankinChar k N χ t ψ (δ 1 1 : ZMod (rankinLevel N t r))‖ = 1 :=
    DirichletCharacter.unit_norm_eq_one _ (isUnit_d hδ).unit
  have hj : (δ 1 0 : ℂ) * z + δ 1 1 ≠ 0 := by rw [← denom_SL_eq]; exact UpperHalfPlane.denom_ne_zero _ z
  have hn : 0 < ‖(δ 1 0 : ℂ) * z + δ 1 1‖ := norm_pos_iff.2 hj
  have h2 : ‖(((δ 1 0 : ℂ) * z + δ 1 1) / ((‖(δ 1 0 : ℂ) * z + δ 1 1‖ : ℝ) : ℂ)) ^ (k - charParity ψ)‖ = 1 := by
    rw [norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg hn.le, div_self hn.ne', one_pow]
  rw [h1, h2, one_mul, one_mul]

/-- **The Rankin kernel is bounded on $\mathbb H$:** $|G_\psi|$ is $\Gamma_0(L)$-invariant and bounded on the translates
$\rho\mathcal F$ of the fundamental domain (`rankinKernel_bound_fd`). -/
theorem rankinKernel_bounded (M : MultiplierSystem) (hT : ThetaTwistLaw M) {k N : ℕ} (hN : 0 < N)
    {χ : DirichletCharacter ℂ (4 * N)} {f : ℍ → ℂ} (hf : f ∈ M.cuspForms k N χ) {t : ℕ} (ht : 1 ≤ t) {r : ℕ}
    (hr : r = 1 ∨ (r.Prime ∧ r ≠ 2)) (ψ : DirichletCharacter ℂ r) (hk : charParity ψ ≤ k) :
    ∃ B : ℝ, ∀ z, ‖rankinKernel k ψ t f z‖ ≤ B := by
  have hfT : M.Transforms k N χ f := (show M.IsCuspForm k N χ f from hf).transforms
  have hr1 := FrickeReduction.one_le_of_hr hr
  have hL1 : 1 ≤ rankinLevel N t r := FrickeReduction.rankinLevel_pos hN ht hr1
  obtain ⟨R0, hR0⟩ := exists_isGamma0Reps (rankinLevel N t r) hL1
  have hθ := norm_thetaTwist_le ψ ht
  have hb : ∀ ρ : SL(2, ℤ), ∃ C : ℝ, ∀ τ ∈ ModularGroup.fd, ‖rankinKernel k ψ t f (ρ • τ)‖ ≤ C := by
    intro ρ
    obtain ⟨C, hC⟩ := rankinKernel_bound_fd M hN hf ψ (continuous_thetaTwist ψ ht)
      (let ⟨C, _, h⟩ := hθ; ⟨C, h⟩) ρ 0
    refine ⟨C / 2, fun τ hτ ↦ ?_⟩
    have := hC τ hτ
    simp only [Real.rpow_zero, neg_zero] at this
    linarith
  choose C hC using hb
  refine ⟨(R0.map fun ρ ↦ |C ρ|).sum, fun z ↦ ?_⟩
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  obtain ⟨i, hi, -⟩ := hR0 g⁻¹
  have hz : z = (g⁻¹ * (R0.get i)⁻¹) • ((R0.get i) • (g • z)) := by
    rw [← mul_smul, ← mul_smul, show g⁻¹ * (R0.get i)⁻¹ * R0.get i * g = 1 by group, one_smul]
  rw [hz, norm_rankinKernel_smul M hT hfT ht hr ψ hk hi]
  refine (hC _ _ hg).trans ((le_abs_self _).trans ?_)
  exact List.single_le_sum (fun _ h ↦ by
    obtain ⟨ρ, -, rfl⟩ := List.mem_map.1 h; exact abs_nonneg _) _ (List.mem_map.2 ⟨_, List.get_mem _ _, rfl⟩)

lemma fricke_eq_S_affPt {L : ℕ} [NeZero L] (w : ℍ) :
    TauCeti.frickeGL ℝ L • w =
      ModularGroup.S • affPt (Nat.toPNat' L) 1 0 w := by
  have hL : ((Nat.toPNat' L : ℕ) : ℂ) = L := by
    simp [Nat.toPNat'_coe, Nat.pos_of_ne_zero (NeZero.ne L)]
  have hP : ((affPt (Nat.toPNat' L) 1 0 w : ℍ) : ℂ) = (L : ℂ) * w := by
    rw [coe_affPt, hL]; simp
  ext1
  rw [DualFricke.coe_fricke_smul, UpperHalfPlane.coe_specialLinearGroup_apply, hP]
  simp [ModularGroup.S]

/-- **Decay of the Rankin kernel after $W_L$ at the cusp $\rho\infty$:** for $\rho \in \mathrm{SL}_2(\mathbb Z)$ and every
$A$, $|G_\psi(W_L\rho(x+iy))| \le C y^{-A}$ for $0 \le x \le 1$, $y \ge Y$. ($L\rho = \eta\alpha$ with
$\eta \in \mathrm{SL}_2(\mathbb Z)$ and $\alpha$ upper triangular, `affPt_decomp`, and `rankinKernel_bound_strip`.) -/
theorem rankinKernel_fricke_decay (M : MultiplierSystem) {k N : ℕ} (hN : 0 < N)
    {χ : DirichletCharacter ℂ (4 * N)} {f : ℍ → ℂ} (hf : f ∈ M.cuspForms k N χ) {r : ℕ}
    (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t) (L : ℕ) [NeZero L] (ρ : SL(2, ℤ)) (A : ℝ) :
    ∃ C Y : ℝ, 0 < Y ∧ ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → Y ≤ y →
      ‖rankinKernel k ψ t f (TauCeti.frickeGL ℝ L • (ρ • stripPt x y))‖ ≤ C * y ^ (-A) := by
  obtain ⟨η, A', D', B', hsm, -⟩ := affPt_decomp (Nat.toPNat' L) 1 0 ρ
  have hA' : (0 : ℝ) < (A' : ℕ) := by exact_mod_cast A'.pos
  have hD' : (0 : ℝ) < (D' : ℕ) := by exact_mod_cast D'.pos
  set X : ℝ := (((A' : ℕ) : ℝ) + |((B' : ℤ) : ℝ)|) / ((D' : ℕ) : ℝ) with hX
  obtain ⟨C, hC⟩ := rankinKernel_bound_strip M hN hf ψ (continuous_thetaTwist ψ ht)
    (let ⟨C, _, h⟩ := norm_thetaTwist_le ψ ht; ⟨C, h⟩) (ModularGroup.S * η) X A
  refine ⟨C * ((((A' : ℕ) : ℝ) / ((D' : ℕ) : ℝ)) ^ (-A)), ((D' : ℕ) : ℝ) / ((A' : ℕ) : ℝ), by positivity,
    fun x y hx0 hx1 hy ↦ ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  set v := stripPt x y with hv
  have hW : TauCeti.frickeGL ℝ L • (ρ • v) = (ModularGroup.S * η) • affPt A' D' B' v := by
    rw [fricke_eq_S_affPt, hsm, mul_smul]
  set τ := affPt A' D' B' v with hτ
  have him : τ.im = ((A' : ℕ) : ℝ) / ((D' : ℕ) : ℝ) * y := by
    rw [hτ, im_affPt, stripPt_im_pos hy0]; ring
  have hre : ((τ : ℂ)).re = (((A' : ℕ) : ℝ) * x + ((B' : ℤ) : ℝ)) / ((D' : ℕ) : ℝ) := by
    rw [hτ, coe_affPt]
    have h := stripPt_re_pos (x := x) hy0
    rw [← hv] at h
    simp [Complex.div_re]
    field_simp
    rw [← h]
    rfl
  have hre' : |(τ : ℂ).re| ≤ X := by
    rw [hre, abs_div, abs_of_pos hD', hX]
    refine div_le_div_of_nonneg_right ((abs_add_le _ _).trans ?_) hD'.le
    rw [abs_mul, abs_of_pos hA', abs_of_nonneg hx0]
    nlinarith
  have h1 : 1 ≤ τ.im := by
    rw [him]
    have : ((A' : ℕ) : ℝ) / ((D' : ℕ) : ℝ) * (((D' : ℕ) : ℝ) / ((A' : ℕ) : ℝ)) = 1 := by field_simp
    calc (1 : ℝ) = ((A' : ℕ) : ℝ) / ((D' : ℕ) : ℝ) * (((D' : ℕ) : ℝ) / ((A' : ℕ) : ℝ)) := this.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hy (by positivity)
  rw [hW]
  refine (hC τ hre' h1).trans (le_of_eq ?_)
  rw [him, Real.mul_rpow (by positivity) hy0.le]
  ring

lemma norm_frickeG {k N t r : ℕ} (hN : 0 < N) (ht : 1 ≤ t) [NeZero r] [NeZero (rankinLevel N t r)]
    {ψ : DirichletCharacter ℂ r} (hψ : ψ.IsPrimitive) (f : ℍ → ℂ) (s : ℂ) (z : ℍ) :
    ‖frickeG k N t ψ f s z‖ =
      (rankinLevel N t r : ℝ) ^ s.re * ‖rankinKernel k ψ t f (TauCeti.frickeGL ℝ (rankinLevel N t r) • z)‖ := by
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hn : 0 < ‖(z : ℂ)‖ := norm_pos_iff.2 hz
  rw [frickeG, ← rankinKernel_fricke hN ht hψ f z, norm_mul, norm_mul, norm_pow, norm_div, Complex.norm_real,
    Real.norm_of_nonneg hn.le, div_self hn.ne', one_pow, mul_one,
    Complex.norm_natCast_cpow_of_pos (FrickeReduction.rankinLevel_pos hN ht (Nat.one_le_iff_ne_zero.2 (NeZero.ne r)))]
  ring

/-- **Strip integrability of the Fricke-side kernel at every coset.** -/
theorem integrableOn_frickeG_strip (M : MultiplierSystem) (hT : ThetaTwistLaw M) {k N : ℕ} (hN : 0 < N)
    {χ : DirichletCharacter ℂ (4 * N)} {f : ℍ → ℂ} (hf : f ∈ M.cuspForms k N χ) {t : ℕ} (ht : 1 ≤ t) {r : ℕ}
    (hr : r = 1 ∨ (r.Prime ∧ r ≠ 2)) [NeZero r] [NeZero (rankinLevel N t r)] {ψ : DirichletCharacter ℂ r}
    (hψ : ψ.IsPrimitive) (hk : charParity ψ < k) (ρ : SL(2, ℤ)) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun p : ℝ × ℝ ↦ ‖frickeG k N t ψ f s (ρ • stripPt p.1 p.2)‖ * p.2 ^ (s.re - 2))
      (Icc 0 1 ×ˢ Ioi 0) := by
  set L := rankinLevel N t r
  have hGeq : frickeG k N t ψ f s = fun z ↦ rankinKernel k ψ t f (TauCeti.frickeGL ℝ L • z) *
      ((L : ℂ) ^ s * (((‖(z : ℂ)‖ : ℝ) : ℂ) / z) ^ (k - charParity ψ)) := by
    funext z
    rw [frickeG, rankinKernel_fricke hN ht hψ f z]
  have hGc : Continuous (frickeG k N t ψ f s) := by
    rw [hGeq]
    have hz : Continuous fun z : ℍ ↦ (((‖(z : ℂ)‖ : ℝ) : ℂ) / z) ^ (k - charParity ψ) :=
      ((Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_coe.norm)).div UpperHalfPlane.continuous_coe
        fun z ↦ z.ne_zero).pow _
    exact ((continuous_rankinKernel k ψ ht (show M.IsCuspForm k N χ f from hf).holo.continuous).comp
      (continuous_const_smul _)).mul (continuous_const.mul hz)
  obtain ⟨B, hB⟩ := rankinKernel_bounded M hT hN hf ht hr ψ hk.le
  obtain ⟨C, Y, hY, hC⟩ := rankinKernel_fricke_decay M hN hf ψ ht L ρ s.re
  have hLs : 0 ≤ (L : ℝ) ^ s.re := by positivity
  refine integrableOn_strip_of_bound (F := fun v ↦ frickeG k N t ψ f s (ρ • v))
    (hGc.comp (continuous_const_smul (ρ : GL (Fin 2) ℝ))) hs (B := (L : ℝ) ^ s.re * B) (C := (L : ℝ) ^ s.re * C) hY
    (fun z ↦ ?_) (fun x y hx0 hx1 hy ↦ ?_)
  · rw [norm_frickeG hN ht hψ]
    exact mul_le_mul_of_nonneg_left (hB _) hLs
  · rw [norm_frickeG hN ht hψ, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC x y hx0 hx1 hy) hLs

/-- **The Fricke-side integral unfolded at every cusp of $\Gamma_0(L)$** (Shimura 1973 `shimura1973`, proof of the Main
Theorem, the cusps other than $\infty$ [unverified]): for $f$ a cusp form, $r = 1$ or an odd prime, $\psi$ primitive modulo
$r$, $\nu < k$ and $\operatorname{Re}s > 1$, `frickeKernelIntegral` = `frickeCosetSum`
$= \sum_{\rho\in R}c_\rho(s)\int_0^\infty\!\int_0^1(|j_\rho|/j_\rho)^\lambda G(\rho z)\,y^{s-2}\,dx\,dy$. -/
@[kb "shimura1973" "proof of the Main Theorem: the Fricke-side Rankin integral unfolded at every cusp of Gamma0(L), coset by coset, proved [unverified]"]
theorem frickeKernelIntegral_eq_cosetSum (M : MultiplierSystem) (hT : ThetaTwistLaw M) {k N : ℕ}
    (hN : 0 < N) {χ : DirichletCharacter ℂ (4 * N)} {f : ℍ → ℂ} (hf : f ∈ M.cuspForms k N χ) {t : ℕ} (ht : 1 ≤ t)
    {r : ℕ} (hr : r = 1 ∨ (r.Prime ∧ r ≠ 2)) [NeZero r] [NeZero (rankinLevel N t r)]
    {ψ : DirichletCharacter ℂ r} (hψ : ψ.IsPrimitive) (hk : charParity ψ < k) {R : List SL(2, ℤ)}
    (hR : IsGamma0Reps (rankinLevel N t r) R) {s : ℂ} (hs : 1 < s.re) :
    frickeKernelIntegral k N χ t ψ f R s = frickeCosetSum k N χ t ψ f R s :=
  frickeKernelIntegral_eq_cosetSum_of_strip M hT hN hf ht hr hψ hk hR hs
    fun ρ _ ↦ integrableOn_frickeG_strip M hT hN hf ht hr hψ hk ρ hs

end FrickeCoset

open FrickeCoset FrickeReduction

/-- **Shimura's Fricke-side identity, coset by coset** (Shimura 1973 `shimura1973`, §§3-5, proof of the Main Theorem;
Niwa 1975 `niwa1975` [unverified]): the statement of `ShimuraFrickeKernelUnfolding M k N χ` with `frickeKernelIntegral`
replaced by its unfolding `frickeCosetSum` (equal to it for $\operatorname{Re}s > 1$, `frickeKernelIntegral_eq_cosetSum`):
$$\text{(`rankinDualFactor`)}\cdot\sum_{\rho\in R}c_\rho(s)\int_0^\infty\!\!\int_0^1
  \Big(\frac{|j_\rho|}{j_\rho}\Big)^\lambda G(\rho z)\,y^{s-2}\,dx\,dy
  = i^{2k}C_\psi\,(2\pi/\sqrt{4Nm^2})^{-w}\Gamma(w)\sum_n\bar\psi(n)b(n)n^{-w},\qquad s = \tfrac{w-k+1}2,$$
$G(z) = $ `frickeKernel` $\cdot L^s(|z|/z)^\lambda$, and for the coset of the cusp $\rho\infty = a/c$,
$c_\rho(s) = \sum_{n\ge1, L\mid nc}n^{-2s}(G(\omega_0,na)+(-1)^\lambda G(\omega_0,-na))$. No Eisenstein series and no
integral over $\Gamma_0(L)\backslash\mathbb H$ is left: each term is the Mellin transform of the constant term of
$(f|W_{4N})(4tr^2\cdot)\,\overline{\theta_{\bar\psi}(4N\cdot)}$ at the cusp $\rho\infty$. What is missing: the expansions of
$f|W_{4N}$ and $\theta_{\bar\psi}$ at the cusps $\rho\infty$ and the identification of the resulting sum of Dirichlet series
with one sequence $b$ for all $\psi$. -/
@[kb "shimura1973" "§§3-5, proof of the Main Theorem: the Fricke-side Rankin integral as a sum over the cusps of Gamma0(L) of Mellin transforms of constant terms, identified with one Dirichlet series [unverified]"]
structure ShimuraCosetIdentity (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop where
  dual : ∀ hN : 0 < N, 2 ≤ k → ∀ t : ℕ, ∀ ht : 1 ≤ t, Squarefree t → ∀ f ∈ M.cuspForms k N χ, ∀ a : ℕ → ℂ,
    Abstract.HasQExp f a →
    ∃ b : ℕ → ℂ, CoeffGrowth b ∧ b 0 = 0 ∧
      (haveI : NeZero (rankinLevel N t 1) := ⟨(rankinLevel_pos hN ht le_rfl).ne'⟩
        ∃ R : List SL(2, ℤ), IsGamma0Reps (rankinLevel N t 1) R ∧ ∃ σ : ℝ, ∀ w : ℂ, σ < w.re →
        rankinDualFactor k N t (1 : DirichletCharacter ℂ 1) w *
            frickeCosetSum k N χ t (1 : DirichletCharacter ℂ 1) f R (rankinS k w) =
          I ^ (2 * k) * (gammaFactor (4 * N) w * LSeries b w)) ∧
      ∀ m : ℕ, ∀ hm : m.Prime, m ≠ 2 → m.Coprime (4 * N) → ∀ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive →
        haveI : NeZero (rankinLevel N t m) := ⟨(rankinLevel_pos hN ht hm.one_lt.le).ne'⟩
        ∃ R : List SL(2, ℤ), IsGamma0Reps (rankinLevel N t m) R ∧ ∃ σ : ℝ, ∀ w : ℂ, σ < w.re →
          rankinDualFactor k N t ψ w * frickeCosetSum k N χ t ψ f R (rankinS k w) =
            I ^ (2 * k) * weilConstant (χ ^ 2) ψ * (gammaFactor (4 * N * m ^ 2) w * LSeries (twist ψ⁻¹ b) w)

/-- **The reduction:** `ShimuraCosetIdentity M k N χ` gives `ShimuraFrickeKernelUnfolding M k N χ`, for a multiplier with
`ThetaTwistLaw M` (by `frickeKernelIntegral_eq_cosetSum` for $\operatorname{Re}w > k+1$). -/
theorem shimuraFrickeKernelUnfolding_of_coset (M : MultiplierSystem) (hT : ThetaTwistLaw M) (k N : ℕ)
    (χ : DirichletCharacter ℂ (4 * N)) (hC : ShimuraCosetIdentity M k N χ) :
    ShimuraFrickeKernelUnfolding M k N χ := by
  refine ⟨fun hN hk t ht hsq f hf a ha ↦ ?_⟩
  obtain ⟨b, hb, hb0, ⟨R₁, hR₁, σ₁, h₁⟩, h₂⟩ := hC.dual hN hk t ht hsq f hf a ha
  have hre : ∀ w : ℂ, (k : ℝ) + 1 < w.re → 1 < (rankinS k w).re := fun w hw ↦ by
    rw [re_rankinS]; linarith
  refine ⟨b, hb, hb0, ⟨R₁, hR₁, max σ₁ ((k : ℝ) + 1), fun w hw ↦ ?_⟩, fun m hm hm2 hmN ψ hψ ↦ ?_⟩
  · have : NeZero (rankinLevel N t 1) := ⟨(rankinLevel_pos hN ht le_rfl).ne'⟩
    have hν : charParity (1 : DirichletCharacter ℂ 1) < k := by
      have := charParity_le_one (1 : DirichletCharacter ℂ 1); omega
    rw [frickeKernelIntegral_eq_cosetSum M hT hN hf ht (Or.inl rfl)
      DirichletCharacter.isPrimitive_one_level_one hν hR₁ (hre w (lt_of_le_of_lt (le_max_right _ _) hw))]
    exact h₁ w (lt_of_le_of_lt (le_max_left _ _) hw)
  · have : NeZero (rankinLevel N t m) := ⟨(rankinLevel_pos hN ht hm.one_lt.le).ne'⟩
    have : NeZero m := ⟨hm.ne_zero⟩
    obtain ⟨R₂, hR₂, σ₂, h₂'⟩ := h₂ m hm hm2 hmN ψ hψ
    refine ⟨R₂, hR₂, max σ₂ ((k : ℝ) + 1), fun w hw ↦ ?_⟩
    have hν : charParity ψ < k := by have := charParity_le_one ψ; omega
    rw [frickeKernelIntegral_eq_cosetSum M hT hN hf ht (Or.inr ⟨hm, hm2⟩) hψ hν hR₂
      (hre w (lt_of_le_of_lt (le_max_right _ _) hw))]
    exact h₂' w (lt_of_le_of_lt (le_max_left _ _) hw)

/-- **Shimura's theorem for the theta multiplier from the coset-by-coset identity** (Shimura 1973 `shimura1973`, Main
Theorem): `shimuraTheorem_theta_of_frickeKernel` with the input `ShimuraCosetIdentity`. -/
@[kb "shimura1973" "Main Theorem for the theta multiplier, conditional on the Fricke-side identity coset by coset (the identification of the Dirichlet series at the cusps of Gamma0(L)) [unverified]"]
theorem shimuraTheorem_theta_of_cosetIdentity (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (hN : 0 < N)
    (hC : ShimuraCosetIdentity thetaMultiplierSystem k N χ) :
    ShimuraTheorem thetaMultiplierSystem k N χ :=
  shimuraTheorem_theta_of_frickeKernel k N χ hN
    (shimuraFrickeKernelUnfolding_of_coset thetaMultiplierSystem thetaTwistLaw_thetaMultiplierSystem k N χ hC)

end ModularFormsKB.HalfIntegral
