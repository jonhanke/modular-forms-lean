/-
# Unfolding a full-lattice Eisenstein series over $\Gamma_0(L)\backslash\mathbb H$, coset by coset

`RankinUnfolding` (`Unfolding.lean`) unfolds the Eisenstein series of $\Gamma_0(L)$ *at $\infty$*: only the cusp
$\infty$ contributes. The Fricke side of Shimura's argument has the series
$E^G(z,s) = y^s\sum_{(c,d)}G(\omega,d)(Lcz+d)^\lambda|Lcz+d|^{-\lambda-2s}$, whose Gauss sums $G(\omega,d)$ do not vanish
for $\gcd(d,L) > 1$ when $\omega$ is imprimitive, so the cusps of $\Gamma_0(L)$ other than $\infty$ contribute. This file
proves the unfolding at all cusps at once, coset by coset.

For a function $\Phi : \mathbb Z^2 \to \mathbb C$ the **full-lattice series** is
$S_\Phi(z,s) = y^s\sum_{p\in\mathbb Z^2}\Phi(p)\,(p_1z+p_2)^\lambda|p_1z+p_2|^{-\lambda-2s}$ (`latticeSeries`). If
$\Phi$ is bounded with $\Phi(p\gamma) = \omega(d_\gamma)\Phi(p)$ on $\Gamma_0(L)$ and $G$ has the unitary weight-$\lambda$ law
with character $\omega$ (`UnitaryLaw`), then for $\operatorname{Re}s > 1$ (`repsIntegral_mul_latticeSeries`)
$$\sum_{\rho\in R}\int_{\mathcal F}G(\rho\tau)\,S_\Phi(\rho\tau,s)\,d\mu(\tau) =
  \sum_{\rho\in R}c_\rho(s)\int_0^\infty\!\!\int_0^1\Big(\frac{|j(\rho,z)|}{j(\rho,z)}\Big)^\lambda G(\rho z)\,y^{s-2}\,dx\,dy,
  \qquad z = x+iy,$$
with $c_\rho(s) = \sum_{n\ge1}n^{-2s}\big(\Phi(n\,r_\rho) + (-1)^\lambda\Phi(-n\,r_\rho)\big)$, $r_\rho = (0,1)\rho^{-1}$
(`cosetCoeff`). The coset $\Gamma_0(L)\rho$ belongs to the cusp $\rho\infty$; the cosets of a cusp of width $h$ are
$\rho, \rho T, \dots, \rho T^{h-1}$, so the sum over the cosets of the strip integrals over $[0,1]$ is the sum over the
cusps of the strip integrals over $[0,h]$, and no classification of the cusps is needed.

**Proof.** (1) *The trace* (`trace_eq`): $\sum_\rho G(\rho\tau)S_\Phi(\rho\tau,s) = \sum_{\zeta\in\Gamma_\infty\backslash
\mathrm{SL}_2(\mathbb Z)}U(\zeta\tau)$ with $U(v) = y^s\sum_\rho c_\rho(s)(|j_\rho|/j_\rho)^\lambda G(\rho v)$: move
$\rho$ into the lattice ($p \mapsto p\rho$), write $\mathbb Z^2\setminus0$ as $\pm n\cdot$(bottom rows of
$\Gamma_\infty\backslash\mathrm{SL}_2(\mathbb Z)$) (`RankinUnfold.Phi` at level $1$), and reindex the cosets
$\rho \mapsto \rho\zeta^{-1}$ (`sum_reps_mul`; the summand is a function of the coset, `eFun_class`). (2) *Level one*:
the trace is $\mathrm{SL}_2(\mathbb Z)$-invariant and `Milne.unfolding_terms` unfolds it to the strip.

**Index shift.** Matrix entries are 0-based: $c = \gamma_{1,0}$, $d = \gamma_{1,1}$.
-/
import ModularFormsKB.HalfIntegral.Rankin.DualFricke

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup MeasureTheory Set
open scoped Real Pointwise

local notation "ℍ" => UpperHalfPlane

namespace CosetUnfold

open DualReps

/-! ### The automorphy factor -/

/-- The automorphy factor $j(\gamma,z) = cz+d$. -/
noncomputable def jf (γ : SL(2, ℤ)) (z : ℍ) : ℂ := (γ 1 0 : ℂ) * z + γ 1 1

lemma jf_ne_zero (γ : SL(2, ℤ)) (z : ℍ) : jf γ z ≠ 0 := by
  rw [jf, ← denom_SL_eq]; exact UpperHalfPlane.denom_ne_zero _ z

lemma jf_mul (g h : SL(2, ℤ)) (z : ℍ) : jf (g * h) z = jf g (h • z) * jf h z := by
  have hd := jf_ne_zero h z
  simp only [jf] at hd ⊢
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [algebraMap_int_eq, eq_intCast, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two]
  push_cast at hd ⊢
  field_simp
  ring

/-- The unitary factor $(|j(\gamma,z)|/j(\gamma,z))^\lambda$. -/
noncomputable def uFac (lam : ℕ) (γ : SL(2, ℤ)) (z : ℍ) : ℂ := (((‖jf γ z‖ : ℝ) : ℂ) / jf γ z) ^ lam

lemma uFac_mul (lam : ℕ) (g h : SL(2, ℤ)) (z : ℍ) :
    uFac lam (g * h) z = uFac lam g (h • z) * uFac lam h z := by
  unfold uFac
  rw [← mul_pow, jf_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm]

lemma uFac_mul_inv (lam : ℕ) (γ : SL(2, ℤ)) (z : ℍ) :
    uFac lam γ z * (jf γ z / ((‖jf γ z‖ : ℝ) : ℂ)) ^ lam = 1 := by
  have h1 := jf_ne_zero γ z
  have h2 : ((‖jf γ z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 h1).ne'
  unfold uFac
  rw [← mul_pow, div_mul_div_comm, mul_comm, div_self (mul_ne_zero h1 h2), one_pow]

lemma norm_uFac (lam : ℕ) (γ : SL(2, ℤ)) (z : ℍ) : ‖uFac lam γ z‖ = 1 := by
  have h1 := jf_ne_zero γ z
  have h2 : 0 < ‖jf γ z‖ := norm_pos_iff.2 h1
  unfold uFac
  rw [norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg h2.le, div_self h2.ne', one_pow]

lemma continuous_uFac (lam : ℕ) (γ : SL(2, ℤ)) : Continuous (uFac lam γ) := by
  have hj : Continuous (jf γ) := by unfold jf; fun_prop
  unfold uFac
  exact ((Complex.continuous_ofReal.comp hj.norm).div hj (jf_ne_zero γ)).pow lam

/-- **The law in terms of the unitary factor:** for $\delta \in \Gamma_0(L)$,
$u(\delta g,z)G(\delta gz) = \omega(d_\delta)\,u(g,z)G(gz)$. -/
lemma law_uFac {L lam : ℕ} {ω : DirichletCharacter ℂ L} {G : ℍ → ℂ} (hU : UnitaryLaw L lam ω G) {δ : SL(2, ℤ)}
    (hδ : δ ∈ Gamma0 L) (g : SL(2, ℤ)) (z : ℍ) :
    uFac lam (δ * g) z * G ((δ * g) • z) = ω (δ 1 1 : ZMod L) * (uFac lam g z * G (g • z)) := by
  have h := uFac_mul_inv lam δ (g • z)
  have hl := hU δ hδ (g • z)
  rw [uFac_mul, mul_smul, hl]
  simp only [jf] at h
  linear_combination (ω (δ 1 1 : ZMod L) * uFac lam g z * G (g • z)) * h

/-! ### Rows and cosets -/

lemma rowAct_mul (g h : SL(2, ℤ)) (p : ℤ × ℤ) : rowAct (g * h) p = rowAct h (rowAct g p) := by
  simp only [rowAct_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ext <;> simp only <;> ring

lemma rowAct_one (p : ℤ × ℤ) : rowAct 1 p = p := by
  simp [rowAct_apply]

lemma rowAct_inv_rowAct (g : SL(2, ℤ)) (p : ℤ × ℤ) : rowAct g⁻¹ (rowAct g p) = p := by
  rw [← rowAct_mul, mul_inv_cancel, rowAct_one]

lemma rowAct_zero_left (g : SL(2, ℤ)) (m : ℤ) : rowAct g (0, m) = (m * g 1 0, m * g 1 1) := by
  simp [rowAct_apply]

lemma char_d_mul_d_inv {L : ℕ} (ω : DirichletCharacter ℂ L) {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 L) :
    ω (δ 1 1 : ZMod L) * ω ((δ⁻¹ : SL(2, ℤ)) 1 1 : ZMod L) = 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet
  have hc : ((δ 1 0 : ℤ) : ZMod L) = 0 := Gamma0_mem.mp hδ
  have hinv : (δ⁻¹ : SL(2, ℤ)) 1 1 = δ 0 0 := by
    simp
  rw [hinv, ← map_mul]
  have : ((δ 1 1 : ℤ) : ZMod L) * ((δ 0 0 : ℤ) : ZMod L) = 1 := by
    have := congrArg (fun x : ℤ ↦ (x : ZMod L)) hdet
    push_cast at this
    rw [hc] at this
    linear_combination this
  rw [this, map_one]

/-- The summand $u(g,w)\,G(gw)\,\Phi((0,m)g^{-1})$ of the trace. -/
noncomputable def eFun (lam : ℕ) (G : ℍ → ℂ) (Φ : ℤ × ℤ → ℂ) (w : ℍ) (m : ℤ) (g : SL(2, ℤ)) : ℂ :=
  uFac lam g w * G (g • w) * Φ (rowAct g⁻¹ (0, m))

/-- **The summand is a function of the coset** $\Gamma_0(L)g$. -/
lemma eFun_class {L lam : ℕ} {ω : DirichletCharacter ℂ L} {G : ℍ → ℂ} (hU : UnitaryLaw L lam ω G)
    {Φ : ℤ × ℤ → ℂ} (hΦ : ∀ γ ∈ Gamma0 L, ∀ p, Φ (rowAct γ p) = ω (γ 1 1 : ZMod L) * Φ p)
    (w : ℍ) (m : ℤ) {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 L) (g : SL(2, ℤ)) :
    eFun lam G Φ w m (δ * g) = eFun lam G Φ w m g := by
  unfold eFun
  rw [law_uFac hU hδ, mul_inv_rev, rowAct_mul, hΦ _ (Subgroup.inv_mem _ hδ)]
  have := char_d_mul_d_inv ω hδ
  linear_combination (uFac lam g w * G (g • w) * Φ (rowAct g⁻¹ (0, m))) * this

/-- **Right translation permutes the cosets:** for a function $f$ of the coset $\Gamma_0(L)g$,
$\sum_{\rho\in R}f(\rho\zeta) = \sum_{\rho\in R}f(\rho)$. -/
lemma sum_reps_mul {L : ℕ} {R : List SL(2, ℤ)} (hR : IsGamma0Reps L R) (f : SL(2, ℤ) → ℂ)
    (hf : ∀ δ ∈ Gamma0 L, ∀ g, f (δ * g) = f g) (ζ : SL(2, ℤ)) :
    (R.map fun ρ ↦ f (ρ * ζ)).sum = (R.map f).sum := by
  rw [← Fin.sum_univ_fun_getElem R, ← Fin.sum_univ_fun_getElem R]
  choose σ hσ hσu using fun i : Fin R.length ↦ hR (R[i.1] * ζ)
  have hinj : Function.Injective σ := by
    intro i i' h
    have h1 := hσ i
    have h2 := hσ i'
    rw [h] at h1
    -- `R_i ζ R_j⁻¹` and `R_i' ζ R_j⁻¹` lie in `Γ₀(L)`, so `R_i R_i'⁻¹` does
    have h3 : R[i.1] * (R[i'.1])⁻¹ ∈ Gamma0 L := by
      have := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
      simpa [mul_assoc] using this
    obtain ⟨j, -, hj⟩ := hR R[i.1]
    have e1 : i = j := hj i (by simp)
    have e2 : i' = j := hj i' (by simpa using h3)
    rw [e1, e2]
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hinj
  refine Fintype.sum_bijective σ hbij _ _ fun i ↦ ?_
  have h := hσ i
  have : R[i.1] * ζ = (R[i.1] * ζ * (R.get (σ i))⁻¹) * R[(σ i).1] := by simp
  rw [this, hf _ h]

/-! ### The full-lattice series and the coset coefficients -/

/-- **The full-lattice series** $S_\Phi(z,s) = y^s\sum_{p\in\mathbb Z^2}\Phi(p)\,(p_1z+p_2)^\lambda|p_1z+p_2|^{-\lambda-2s}$. -/
noncomputable def latticeSeries (lam : ℕ) (Φ : ℤ × ℤ → ℂ) (z : ℍ) (s : ℂ) : ℂ :=
  ((z.im : ℂ) ^ s) * ∑' p : ℤ × ℤ, Φ p * eisTerm lam s ((p.1 : ℂ) * z + p.2)

/-- **The coefficient of the coset** $\Gamma_0(L)\rho$:
$c_\rho(s) = \sum_{n\ge1}n^{-2s}\big(\Phi(n\,r_\rho) + (-1)^\lambda\Phi(-n\,r_\rho)\big)$, $r_\rho = (0,1)\rho^{-1}$. -/
noncomputable def cosetCoeff (lam : ℕ) (Φ : ℤ × ℤ → ℂ) (ρ : SL(2, ℤ)) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (2 * s))⁻¹ *
    (Φ (rowAct ρ⁻¹ (0, ((n + 1 : ℕ) : ℤ))) + (-1 : ℂ) ^ lam * Φ (rowAct ρ⁻¹ (0, -((n + 1 : ℕ) : ℤ))))

/-- **The trace** $\sum_{\rho\in R}c_\rho(s)\,(|j_\rho|/j_\rho)^\lambda\,G(\rho v)$; the function unfolded to the strip is
$y^s$ times it. -/
noncomputable def traceFun (lam : ℕ) (Φ : ℤ × ℤ → ℂ) (R : List SL(2, ℤ)) (G : ℍ → ℂ) (s : ℂ) (v : ℍ) : ℂ :=
  (R.map fun ρ ↦ cosetCoeff lam Φ ρ s * (uFac lam ρ v * G (ρ • v))).sum

lemma summable_coeff {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ ↦ ‖(((n + 1 : ℕ) : ℂ) ^ (2 * s))⁻¹‖ := by
  have h : ∀ n : ℕ, ‖(((n + 1 : ℕ) : ℂ) ^ (2 * s))⁻¹‖ = (((n + 1 : ℕ) : ℝ) ^ (2 * s.re))⁻¹ := by
    intro n
    rw [norm_inv, Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n)]
    simp
  simp_rw [h]
  have := (Real.summable_nat_rpow_inv (p := 2 * s.re)).2 (by linarith)
  exact (summable_nat_add_iff 1).2 this

lemma im_smul_cpow (ρ : SL(2, ℤ)) (τ : ℍ) (s : ℂ) :
    (((ρ • τ).im : ℝ) : ℂ) ^ s = ((τ.im : ℂ) ^ s) * ((((‖jf ρ τ‖ : ℝ) : ℂ) ^ s) ^ 2)⁻¹ := by
  have hr : 0 < ‖jf ρ τ‖ := norm_pos_iff.2 (jf_ne_zero ρ τ)
  have hy := τ.im_pos
  have him : (ρ • τ).im = τ.im / ‖jf ρ τ‖ ^ 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq, denom_SL_eq]; rfl
  rw [him, div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hy.le (by positivity)]
  congr 1
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_ne_zero.symm)]
  congr 1
  rw [Complex.ofReal_pow, sq, sq, Complex.mul_cpow_ofReal_nonneg hr.le hr.le]

/-- **The lattice series at $\rho\tau$:** $S_\Phi(\rho\tau,s) =
(|j_\rho|/j_\rho)^\lambda\,y^s\sum_q\Phi(q\rho^{-1})(q_1\tau+q_2)^\lambda|q_1\tau+q_2|^{-\lambda-2s}$. -/
lemma latticeSeries_smul {lam : ℕ} (hlam : 1 ≤ lam) (Φ : ℤ × ℤ → ℂ) (ρ : SL(2, ℤ)) (τ : ℍ) (s : ℂ) :
    latticeSeries lam Φ (ρ • τ) s = uFac lam ρ τ * (((τ.im : ℂ) ^ s) *
      ∑' q : ℤ × ℤ, Φ (rowAct ρ⁻¹ q) * eisTerm lam s ((q.1 : ℂ) * τ + q.2)) := by
  set j := jf ρ τ with hjdef
  have hj : j ≠ 0 := jf_ne_zero ρ τ
  have hpt : ∀ p : ℤ × ℤ, (p.1 : ℂ) * ((ρ • τ : ℍ) : ℂ) + p.2 =
      (((rowAct ρ p).1 : ℂ) * τ + (rowAct ρ p).2) / j := by
    intro p
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, rowAct_apply]
    simp only [algebraMap_int_eq, eq_intCast, Int.cast_add, Int.cast_mul]
    have hj' : (((ρ 1 0 : ℤ) : ℝ) : ℂ) * τ + (((ρ 1 1 : ℤ) : ℝ) : ℂ) = j := by rw [hjdef, jf]; push_cast; ring
    rw [hj']
    field_simp
    rw [hjdef, jf]
    push_cast
    ring
  have hsum : ∑' p : ℤ × ℤ, Φ p * eisTerm lam s ((p.1 : ℂ) * ((ρ • τ : ℍ) : ℂ) + p.2) =
      ((‖j‖ : ℂ) ^ lam / j ^ lam) * ((‖j‖ : ℂ) ^ s) ^ 2 *
        ∑' q : ℤ × ℤ, Φ (rowAct ρ⁻¹ q) * eisTerm lam s ((q.1 : ℂ) * τ + q.2) := by
    rw [← tsum_mul_left]
    rw [← (rowAct ρ).tsum_eq (fun q ↦ ((‖j‖ : ℂ) ^ lam / j ^ lam) * ((‖j‖ : ℂ) ^ s) ^ 2 *
      (Φ (rowAct ρ⁻¹ q) * eisTerm lam s ((q.1 : ℂ) * τ + q.2)))]
    refine tsum_congr fun p ↦ ?_
    rw [hpt p, eisTerm_div hlam s _ hj, rowAct_inv_rowAct]
    ring
  unfold latticeSeries
  rw [hsum, im_smul_cpow, uFac, div_pow, ← hjdef]
  have hr' : ((‖j‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hj).ne'
  have hs' : ((‖j‖ : ℝ) : ℂ) ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h ↦ hr' h.1
  generalize (∑' q : ℤ × ℤ, Φ (rowAct ρ⁻¹ q) * eisTerm lam s ((q.1 : ℂ) * τ + q.2)) = T
  generalize ((τ.im : ℂ) ^ s) = Y
  have hjl : j ^ lam ≠ 0 := pow_ne_zero _ hj
  field_simp

/-- $y^s\,(cz+d)^\lambda|cz+d|^{-\lambda-2s}\,(|j|/j)^\lambda = \operatorname{Im}(\zeta\tau)^s$. -/
lemma im_mul_eisTerm_uFac (lam : ℕ) (ζ : SL(2, ℤ)) (τ : ℍ) (s : ℂ) :
    ((τ.im : ℂ) ^ s) * eisTerm lam s (jf ζ τ) * uFac lam ζ τ = (((ζ • τ).im : ℝ) : ℂ) ^ s := by
  set j := jf ζ τ with hjdef
  have hj : j ≠ 0 := jf_ne_zero ζ τ
  have hr : 0 < ‖j‖ := norm_pos_iff.2 hj
  have hne : ((‖j‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have e2 : ((‖j‖ : ℝ) : ℂ) ^ (-(lam : ℂ) - 2 * s) = (((‖j‖ : ℂ) ^ lam))⁻¹ * (((‖j‖ : ℂ) ^ s) ^ 2)⁻¹ := by
    rw [show (-(lam : ℂ) - 2 * s) = -(lam : ℂ) + -(2 * s) by ring, Complex.cpow_add _ _ hne,
      Complex.cpow_neg, Complex.cpow_neg, Complex.cpow_natCast, show (2 : ℂ) * s = ((2 : ℕ) : ℂ) * s by simp,
      Complex.cpow_nat_mul]
  rw [im_smul_cpow, uFac, eisTerm, e2, div_pow, ← hjdef]
  have hjl : j ^ lam ≠ 0 := pow_ne_zero _ hj
  have hl : ((‖j‖ : ℝ) : ℂ) ^ lam ≠ 0 := pow_ne_zero _ hne
  have hs' : ((‖j‖ : ℝ) : ℂ) ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h ↦ hne h.1
  field_simp

/-- **The reindexing of the cosets** $\rho \mapsto \rho\zeta^{-1}$:
$\sum_\rho u(\rho,\tau)G(\rho\tau)\Phi((0,m)\zeta\rho^{-1}) = u(\zeta,\tau)\sum_\rho u(\rho,\zeta\tau)G(\rho\zeta\tau)
\Phi((0,m)\rho^{-1})$. -/
lemma sum_reindex {L lam : ℕ} {R : List SL(2, ℤ)} (hR : IsGamma0Reps L R) {ω : DirichletCharacter ℂ L}
    {G : ℍ → ℂ} (hU : UnitaryLaw L lam ω G)
    {Φ : ℤ × ℤ → ℂ} (hΦ : ∀ γ ∈ Gamma0 L, ∀ p, Φ (rowAct γ p) = ω (γ 1 1 : ZMod L) * Φ p)
    (ζ : SL(2, ℤ)) (τ : ℍ) (m : ℤ) :
    (R.map fun ρ ↦ uFac lam ρ τ * G (ρ • τ) * Φ (rowAct ρ⁻¹ (rowAct ζ (0, m)))).sum =
      uFac lam ζ τ * (R.map fun ρ ↦ eFun lam G Φ (ζ • τ) m ρ).sum := by
  have hpt : ∀ ρ : SL(2, ℤ), uFac lam ρ τ * G (ρ • τ) * Φ (rowAct ρ⁻¹ (rowAct ζ (0, m))) =
      uFac lam ζ τ * eFun lam G Φ (ζ • τ) m (ρ * ζ⁻¹) := by
    intro ρ
    unfold eFun
    have h1 : (ρ * ζ⁻¹) • (ζ • τ) = ρ • τ := by rw [← mul_smul, inv_mul_cancel_right]
    have h2 : uFac lam ρ τ = uFac lam (ρ * ζ⁻¹) (ζ • τ) * uFac lam ζ τ := by
      rw [← uFac_mul, inv_mul_cancel_right]
    rw [h1, h2, mul_inv_rev, inv_inv, rowAct_mul]
    ring
  simp_rw [hpt]
  rw [List.sum_map_mul_left,
    sum_reps_mul hR (eFun lam G Φ (ζ • τ) m) (fun δ hδ g ↦ eFun_class hU hΦ (ζ • τ) m hδ g) ζ⁻¹]

/-! ### The trace as a series over `Γ_∞\SL(2, ℤ)` -/

lemma norm_list_map_sum_le {ι : Type*} (R : List ι) (f : ι → ℂ) :
    ‖(R.map f).sum‖ ≤ (R.map fun i ↦ ‖f i‖).sum := by
  induction R with
  | nil => simp
  | cons a R ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

/-- A sum over a list commutes with a convergent series. -/
lemma tsum_list_sum {ι β : Type*} (R : List ι) (f : ι → β → ℂ) (hf : ∀ i ∈ R, Summable (f i)) :
    Summable (fun n ↦ (R.map fun i ↦ f i n).sum) ∧
      ∑' n, (R.map fun i ↦ f i n).sum = (R.map fun i ↦ ∑' n, f i n).sum := by
  induction R with
  | nil => simp
  | cons a R ih =>
    obtain ⟨hs, he⟩ := ih fun i hi ↦ hf i (List.mem_cons_of_mem a hi)
    have ha := hf a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    exact ⟨ha.add hs, by rw [ha.tsum_add hs, he]⟩

open RankinUnfold in
lemma Phi_one_eq (n : ℕ) (x : X 1) (b : Bool) :
    Phi 1 (n, x, b) = rowAct (rep 1 x) (0, sg b * ((n : ℤ) + 1)) := by
  rw [rowAct_zero_left]
  simp only [Phi, Nat.cast_one, Int.ediv_one]

open RankinUnfold in
/-- **The trace identity:** $\sum_{\rho\in R}G(\rho\tau)S_\Phi(\rho\tau,s) =
\sum_{\zeta\in\Gamma_\infty\backslash\mathrm{SL}_2(\mathbb Z)}\operatorname{Im}(\zeta\tau)^s\,T(\zeta\tau)$, $T$ = `traceFun`. -/
theorem trace_eq {L lam : ℕ} (hlam : 1 ≤ lam) {R : List SL(2, ℤ)} (hR : IsGamma0Reps L R)
    {ω : DirichletCharacter ℂ L} {G : ℍ → ℂ} (hU : UnitaryLaw L lam ω G)
    {Φ : ℤ × ℤ → ℂ} (hΦ : ∀ γ ∈ Gamma0 L, ∀ p, Φ (rowAct γ p) = ω (γ 1 1 : ZMod L) * Φ p)
    {C : ℝ} (hΦC : ∀ p, ‖Φ p‖ ≤ C) {s : ℂ} (hs : 1 < s.re) (τ : ℍ) :
    (R.map fun ρ ↦ G (ρ • τ) * latticeSeries lam Φ (ρ • τ) s).sum =
      ∑' x : X 1, Fs (traceFun lam Φ R G s) s (rep 1 x • τ) := by
  set Y : ℂ := (τ.im : ℂ) ^ s with hY
  set A : ℤ × ℤ → ℂ := fun q ↦ (R.map fun ρ ↦ uFac lam ρ τ * G (ρ • τ) * Φ (rowAct ρ⁻¹ q)).sum with hA
  set F : ℤ × ℤ → ℂ := fun q ↦ A q * eisTerm lam s ((q.1 : ℂ) * τ + q.2) with hF
  have hE : Summable (fun q : ℤ × ℤ ↦ ‖eisTerm lam s ((q.1 : ℂ) * τ + q.2)‖) := by
    have := DualFricke.summable_norm_eisTerm (L := 1) le_rfl lam τ hs
    simpa using this
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hΦC 0)
  -- Step 1: move `ρ` into the lattice
  have hsumρ : ∀ ρ : SL(2, ℤ), Summable (fun q : ℤ × ℤ ↦
      uFac lam ρ τ * G (ρ • τ) * Φ (rowAct ρ⁻¹ q) * eisTerm lam s ((q.1 : ℂ) * τ + q.2)) := by
    intro ρ
    refine Summable.of_norm_bounded (hE.mul_left (‖uFac lam ρ τ * G (ρ • τ)‖ * C)) fun q ↦ ?_
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hΦC _) (norm_nonneg _)) (norm_nonneg _)
  have h1 : (R.map fun ρ ↦ G (ρ • τ) * latticeSeries lam Φ (ρ • τ) s).sum = Y * ∑' q, F q := by
    have hF' : ∀ q, F q = (R.map fun ρ ↦
        uFac lam ρ τ * G (ρ • τ) * Φ (rowAct ρ⁻¹ q) * eisTerm lam s ((q.1 : ℂ) * τ + q.2)).sum := by
      intro q
      simp only [hF, hA]
      rw [← List.sum_map_mul_right]
    simp_rw [hF', (tsum_list_sum R _ fun ρ _ ↦ hsumρ ρ).2, latticeSeries_smul hlam]
    rw [← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun ρ _ ↦ ?_
    simp_rw [mul_assoc (uFac lam ρ τ * G (ρ • τ))]
    rw [tsum_mul_left, ← hY]
    ring
  -- Step 2: regroup the lattice over `ℕ × Γ_∞\SL(2, ℤ) × {±1}`
  set B : ℝ := (R.map fun ρ ↦ ‖G (ρ • τ)‖ * C).sum with hB
  have hAb : ∀ q, ‖A q‖ ≤ B := by
    intro q
    simp only [hA, hB]
    refine (norm_list_map_sum_le R _).trans (List.sum_le_sum fun ρ _ ↦ ?_)
    rw [norm_mul, norm_mul, norm_uFac, one_mul]
    exact mul_le_mul_of_nonneg_left (hΦC _) (norm_nonneg _)
  have hFs : Summable F := by
    refine Summable.of_norm_bounded (hE.mul_left B) fun q ↦ ?_
    rw [hF, norm_mul]
    exact mul_le_mul_of_nonneg_right (hAb q) (norm_nonneg _)
  have hsupp : Function.support F ⊆ Set.range (Phi 1) := by
    refine subset_trans (fun q hq ↦ ?_) (support_subset_range_Phi le_rfl lam (1 : DirichletCharacter ℂ 1) τ hs)
    simp only [Function.mem_support, hF] at hq ⊢
    have he : eisTerm lam s ((q.1 : ℂ) * τ + q.2) ≠ 0 := right_ne_zero_of_mul hq
    simp only [term, Nat.cast_one, one_mul]
    rw [MulChar.one_apply (isUnit_of_subsingleton _), one_mul]
    exact he
  have hinj := Phi_injective 1 le_rfl
  let e : X 1 × (ℕ × Bool) ≃ ℕ × (X 1 × Bool) :=
    ⟨fun d ↦ (d.2.1, d.1, d.2.2), fun c ↦ (c.2.1, c.1, c.2.2), fun _ ↦ rfl, fun _ ↦ rfl⟩
  have hS : Summable (fun d ↦ F (Phi 1 (e d))) := (hFs.comp_injective hinj).comp_injective e.injective
  have h2 : ∑' q, F q = ∑' x : X 1, ∑' nb : ℕ × Bool, F (Phi 1 (nb.1, x, nb.2)) := by
    rw [← hinj.tsum_eq hsupp, ← e.tsum_eq]
    exact hS.tsum_prod' (fun x ↦ hS.prod_factor x)
  rw [h1, h2, ← tsum_mul_left]
  refine tsum_congr fun x ↦ ?_
  -- Step 3: one coset `x = Γ_∞ ζ`
  set ζ := rep 1 x with hζ
  set w := ζ • τ with hw
  set Em : ℤ → ℂ := fun m ↦ (R.map fun ρ ↦ eFun lam G Φ w m ρ).sum with hEm
  have hterm : ∀ n : ℕ, ∀ b : Bool, Y * F (Phi 1 (n, x, b)) =
      (((w.im : ℝ) : ℂ) ^ s) * (((sg b : ℂ) ^ lam * (((n + 1 : ℕ) : ℂ) ^ (2 * s))⁻¹) * Em (sg b * ((n : ℤ) + 1))) := by
    intro n b
    have hv : ((Phi 1 (n, x, b)).1 : ℂ) * τ + ((Phi 1 (n, x, b)).2 : ℂ) =
        ((sg b * (n + 1) : ℤ) : ℂ) * jf ζ τ := by
      rw [Phi_one_eq, rowAct_zero_left, jf]
      push_cast
      ring
    have hAx : A (Phi 1 (n, x, b)) = uFac lam ζ τ * Em (sg b * ((n : ℤ) + 1)) := by
      simp only [hA, hEm]
      rw [Phi_one_eq]
      exact sum_reindex hR hU hΦ ζ τ _
    simp only [hF]
    rw [hv, eisTerm_smul, hAx, ← im_mul_eisTerm_uFac lam ζ τ s, ← hY]
    ring
  have hS' : Summable (fun nb : ℕ × Bool ↦ Y * F (Phi 1 (nb.1, x, nb.2))) :=
    (hS.prod_factor x).mul_left Y
  rw [← tsum_mul_left]
  simp_rw [show ∀ nb : ℕ × Bool, Y * F (Phi 1 (nb.1, x, nb.2)) = _ from fun nb ↦ hterm nb.1 nb.2] at hS' ⊢
  rw [hS'.tsum_prod' (fun n ↦ hS'.prod_factor n)]
  simp only [tsum_bool, sg, ↓reduceIte, Bool.false_eq_true, Int.cast_one, one_pow, one_mul,
    Int.cast_neg, neg_one_mul]
  -- the trace at `w`
  set c : ℕ → ℂ := fun n ↦ (((n + 1 : ℕ) : ℂ) ^ (2 * s))⁻¹ with hc
  set f : SL(2, ℤ) → ℕ → ℂ := fun ρ n ↦
    c n * (eFun lam G Φ w ((n : ℤ) + 1) ρ + (-1 : ℂ) ^ lam * eFun lam G Φ w (-((n : ℤ) + 1)) ρ) with hf
  have hfs : ∀ ρ : SL(2, ℤ), Summable (f ρ) := by
    intro ρ
    refine Summable.of_norm_bounded ((summable_coeff hs).mul_right (2 * (‖G (ρ • w)‖ * C))) fun n ↦ ?_
    simp only [hf, eFun, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_uFac,
      one_mul]
    have h1 := mul_le_mul_of_nonneg_left (hΦC (rowAct ρ⁻¹ (0, (n : ℤ) + 1))) (norm_nonneg (G (ρ • w)))
    have h2 := mul_le_mul_of_nonneg_left (hΦC (rowAct ρ⁻¹ (0, -((n : ℤ) + 1)))) (norm_nonneg (G (ρ • w)))
    have h3 : ‖uFac lam ρ w * G (ρ • w)‖ = ‖G (ρ • w)‖ := by rw [norm_mul, norm_uFac, one_mul]
    rw [h3]
    linarith
  have htr : traceFun lam Φ R G s w = ∑' n, c n * (Em ((n : ℤ) + 1) + (-1 : ℂ) ^ lam * Em (-((n : ℤ) + 1))) := by
    have hρ : ∀ ρ : SL(2, ℤ), cosetCoeff lam Φ ρ s * (uFac lam ρ w * G (ρ • w)) = ∑' n, f ρ n := by
      intro ρ
      unfold cosetCoeff
      rw [← tsum_mul_right]
      refine tsum_congr fun n ↦ ?_
      simp only [hf, hc, eFun]
      push_cast
      ring
    unfold traceFun
    simp_rw [hρ]
    rw [← (tsum_list_sum R f fun ρ _ ↦ hfs ρ).2]
    refine tsum_congr fun n ↦ ?_
    simp only [hf, hEm]
    rw [List.sum_map_mul_left, List.sum_map_add, List.sum_map_mul_left]
  rw [Fs, htr, ← tsum_mul_right]
  refine tsum_congr fun n ↦ ?_
  simp only [hc]
  push_cast
  ring

/-! ### The trace is invariant under `Γ_∞` -/

lemma cosetCoeff_mul_left {L lam : ℕ} {ω : DirichletCharacter ℂ L} {Φ : ℤ × ℤ → ℂ}
    (hΦ : ∀ γ ∈ Gamma0 L, ∀ p, Φ (rowAct γ p) = ω (γ 1 1 : ZMod L) * Φ p) {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 L)
    (g : SL(2, ℤ)) (s : ℂ) :
    cosetCoeff lam Φ (δ * g) s = ω ((δ⁻¹ : SL(2, ℤ)) 1 1 : ZMod L) * cosetCoeff lam Φ g s := by
  unfold cosetCoeff
  rw [← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  rw [mul_inv_rev, rowAct_mul, rowAct_mul, hΦ _ (Subgroup.inv_mem _ hδ), hΦ _ (Subgroup.inv_mem _ hδ)]
  ring

lemma cosetCoeff_mul_stab (lam : ℕ) (Φ : ℤ × ℤ → ℂ) {β : SL(2, ℤ)} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (h10 : β 1 0 = 0) (h00 : β 0 0 = ε) (g : SL(2, ℤ)) (s : ℂ) :
    cosetCoeff lam Φ (g * β) s = (ε : ℂ) ^ lam * cosetCoeff lam Φ g s := by
  have hrow : ∀ m : ℤ, rowAct (g * β)⁻¹ (0, m) = rowAct g⁻¹ (0, ε * m) := by
    intro m
    rw [mul_inv_rev, rowAct_mul, rowAct_zero_left]
    have h1 : (β⁻¹ : SL(2, ℤ)) 1 0 = 0 := by simp [h10]
    have h2 : (β⁻¹ : SL(2, ℤ)) 1 1 = ε := by simp [h00]
    rw [h1, h2, mul_zero, mul_comm m ε]
  unfold cosetCoeff
  rw [← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  rw [hrow, hrow]
  rcases hε with rfl | rfl
  · simp
  · simp only [Int.reduceNeg, neg_mul, one_mul, neg_neg, Int.cast_neg, Int.cast_one]
    have h2 : ((-1 : ℂ) ^ lam) * ((-1 : ℂ) ^ lam) = 1 := by rw [← mul_pow]; simp
    linear_combination (-(((n + 1 : ℕ) : ℂ) ^ (2 * s))⁻¹ * Φ (rowAct g⁻¹ (0, -((n + 1 : ℕ) : ℤ)))) * h2

/-- The summand $c_g\,u(g,v)\,G(gv)$ of the trace, as a function of $g$. -/
noncomputable def tFun (lam : ℕ) (Φ : ℤ × ℤ → ℂ) (G : ℍ → ℂ) (s : ℂ) (v : ℍ) (g : SL(2, ℤ)) : ℂ :=
  cosetCoeff lam Φ g s * (uFac lam g v * G (g • v))

lemma tFun_class {L lam : ℕ} {ω : DirichletCharacter ℂ L} {G : ℍ → ℂ} (hU : UnitaryLaw L lam ω G)
    {Φ : ℤ × ℤ → ℂ} (hΦ : ∀ γ ∈ Gamma0 L, ∀ p, Φ (rowAct γ p) = ω (γ 1 1 : ZMod L) * Φ p) (s : ℂ) (v : ℍ)
    {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 L) (g : SL(2, ℤ)) :
    tFun lam Φ G s v (δ * g) = tFun lam Φ G s v g := by
  unfold tFun
  rw [cosetCoeff_mul_left hΦ hδ, law_uFac hU hδ]
  have := char_d_mul_d_inv ω hδ
  linear_combination (cosetCoeff lam Φ g s * (uFac lam g v * G (g • v))) * this

lemma traceFun_stab {L lam : ℕ} {R : List SL(2, ℤ)} (hR : IsGamma0Reps L R) {ω : DirichletCharacter ℂ L}
    {G : ℍ → ℂ} (hU : UnitaryLaw L lam ω G)
    {Φ : ℤ × ℤ → ℂ} (hΦ : ∀ γ ∈ Gamma0 L, ∀ p, Φ (rowAct γ p) = ω (γ 1 1 : ZMod L) * Φ p) (s : ℂ)
    {β : SL(2, ℤ)} (h10 : β 1 0 = 0) (v : ℍ) :
    traceFun lam Φ R G s (β • v) = traceFun lam Φ R G s v := by
  obtain ⟨ε, hε, h00, h11⟩ := Milne.sl_lower_zero β h10
  have hj : jf β v = ε := by simp [jf, h10, h11]
  have huβ : uFac lam β v = (ε : ℂ) ^ lam := by
    rw [uFac, hj]
    rcases hε with rfl | rfl <;> simp
  have hεε : ((ε : ℂ) ^ lam) * ((ε : ℂ) ^ lam) = 1 := by
    rw [← mul_pow]; rcases hε with rfl | rfl <;> simp
  have hpt : ∀ ρ : SL(2, ℤ), cosetCoeff lam Φ ρ s * (uFac lam ρ (β • v) * G (ρ • β • v)) =
      tFun lam Φ G s v (ρ * β) := by
    intro ρ
    unfold tFun
    rw [cosetCoeff_mul_stab lam Φ hε h10 h00, uFac_mul, huβ, mul_smul]
    linear_combination (-(cosetCoeff lam Φ ρ s * (uFac lam ρ (β • v) * G (ρ • β • v)))) * hεε
  unfold traceFun
  simp_rw [hpt]
  exact sum_reps_mul hR _ (fun δ hδ g ↦ tFun_class hU hΦ s v hδ g) β

/-! ### Lists of integrable and continuous functions -/

lemma continuous_list_map_sum {ι : Type*} (R : List ι) (f : ι → ℍ → ℂ) (hf : ∀ i ∈ R, Continuous (f i)) :
    Continuous fun v ↦ (R.map fun i ↦ f i v).sum := by
  induction R with
  | nil => simpa using continuous_const
  | cons a R ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hf a List.mem_cons_self).add (ih fun i hi ↦ hf i (List.mem_cons_of_mem a hi))

lemma integrableOn_list_map_sum {ι : Type*} (R : List ι) (f : ι → ℍ → ℂ) (S : Set ℍ)
    (hf : ∀ i ∈ R, IntegrableOn (f i) S) :
    IntegrableOn (fun v ↦ (R.map fun i ↦ f i v).sum) S ∧
      ∫ v in S, (R.map fun i ↦ f i v).sum = (R.map fun i ↦ ∫ v in S, f i v).sum := by
  induction R with
  | nil => simp
  | cons a R ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi ↦ hf i (List.mem_cons_of_mem a hi)
    have ha := hf a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons]
    exact ⟨ha.add h1, by rw [integral_add ha h1, h2]⟩

/-! ### The unfolding -/

open RankinUnfold in
lemma isGamma0Reps_one : IsGamma0Reps 1 [1] := by
  intro g
  refine ⟨⟨0, by simp⟩, ?_, fun i _ ↦ ?_⟩
  · simp
  · ext; simp

open RankinUnfold in
lemma trace_invariant {L lam : ℕ} {R : List SL(2, ℤ)} (hR : IsGamma0Reps L R) {ω : DirichletCharacter ℂ L}
    {G : ℍ → ℂ} (hU : UnitaryLaw L lam ω G)
    {Φ : ℤ × ℤ → ℂ} (hΦ : ∀ γ ∈ Gamma0 L, ∀ p, Φ (rowAct γ p) = ω (γ 1 1 : ZMod L) * Φ p) (s : ℂ)
    (γ : SL(2, ℤ)) (z : ℍ) :
    ∑' x : X 1, Fs (traceFun lam Φ R G s) s (rep 1 x • γ • z) =
      ∑' x : X 1, Fs (traceFun lam Φ R G s) s (rep 1 x • z) := by
  have hγ : γ ∈ Gamma0 1 := by simp
  have hstab : ∀ β : Gamma0 1, β ∈ Milne.stabInfty (Gamma0 1) → ∀ v : ℍ,
      Fs (traceFun lam Φ R G s) s ((β : SL(2, ℤ)) • v) = Fs (traceFun lam Φ R G s) s v := by
    intro β hβ v
    have h10 : (β : SL(2, ℤ)) 1 0 = 0 := hβ
    obtain ⟨ε, hε, -, h11⟩ := Milne.sl_lower_zero (β : SL(2, ℤ)) h10
    have him : ((β : SL(2, ℤ)) • v).im = v.im := by
      rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
      rcases hε with rfl | rfl <;> simp [h10, h11]
    unfold Fs
    rw [traceFun_stab hR hU hΦ s h10, him]
  conv_rhs => rw [← (rmul (⟨γ, hγ⟩ : Gamma0 1)).tsum_eq]
  refine tsum_congr fun x ↦ ?_
  have hx : (rmul (⟨γ, hγ⟩ : Gamma0 1)) x = Quotient.mk _ (x.out * ⟨γ, hγ⟩) := by
    conv_lhs => rw [← Quotient.out_eq x]
    rfl
  have h : (x.out * ⟨γ, hγ⟩) * ((rmul (⟨γ, hγ⟩ : Gamma0 1)) x).out⁻¹ ∈ Milne.stabInfty (Gamma0 1) :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact ((Quotient.out_eq _).trans hx))
  set y := (rmul (⟨γ, hγ⟩ : Gamma0 1)) x
  set β : Gamma0 1 := y.out * (x.out * ⟨γ, hγ⟩)⁻¹
  have hβ : β ∈ Milne.stabInfty (Gamma0 1) := by
    have := Subgroup.inv_mem _ h
    simpa [β, mul_assoc] using this
  have hrep : rep 1 y = (β : SL(2, ℤ)) * (rep 1 x * γ) := by
    simp [rep, β, mul_assoc]
  rw [hrep, mul_smul, hstab β hβ, mul_smul]

open RankinUnfold in
/-- **The unfolding of a full-lattice series, coset by coset** (Rankin 1939 `rankin1939`; the cusps other than
$\infty$ as in Shimura 1973 `shimura1973`, proof of the Main Theorem [unverified]): for $L, \lambda \ge 1$, right coset
representatives $R$ of $\Gamma_0(L)$, $G$ continuous with the unitary weight-$\lambda$ law with character $\omega$,
$\Phi$ bounded with $\Phi(p\gamma) = \omega(d_\gamma)\Phi(p)$ on $\Gamma_0(L)$, $\operatorname{Re}s > 1$, the integrand
integrable on $\rho\mathcal F$ and $\int_0^\infty\!\int_0^1|G(\rho z)|y^{\sigma-2} < \infty$ for every $\rho \in R$:
$$\sum_{\rho\in R}\int_{\mathcal F}G(\rho\tau)S_\Phi(\rho\tau,s)\,d\mu =
  \sum_{\rho\in R}c_\rho(s)\int_0^\infty\!\!\int_0^1\Big(\frac{|j_\rho|}{j_\rho}\Big)^\lambda G(\rho z)\,y^{s-2}\,dx\,dy.$$ -/
@[kb "rankin1939" "the unfolding of a lattice Eisenstein series with periodic coefficients at all cusps, coset by coset, proved [unverified]"]
theorem repsIntegral_mul_latticeSeries {L lam : ℕ} [NeZero L] (hlam : 1 ≤ lam) {R : List SL(2, ℤ)}
    (hR : IsGamma0Reps L R) {ω : DirichletCharacter ℂ L} {G : ℍ → ℂ} (hG : Continuous G)
    (hU : UnitaryLaw L lam ω G) {Φ : ℤ × ℤ → ℂ}
    (hΦ : ∀ γ ∈ Gamma0 L, ∀ p, Φ (rowAct γ p) = ω (γ 1 1 : ZMod L) * Φ p) {C : ℝ} (hΦC : ∀ p, ‖Φ p‖ ≤ C)
    {s : ℂ} (hs : 1 < s.re)
    (hfd : ∀ ρ ∈ R, IntegrableOn (fun τ ↦ G (ρ • τ) * latticeSeries lam Φ (ρ • τ) s) ModularGroup.fd)
    (hint : ∀ ρ ∈ R, IntegrableOn (fun p : ℝ × ℝ ↦ ‖G (ρ • stripPt p.1 p.2)‖ * p.2 ^ (s.re - 2))
      (Icc 0 1 ×ˢ Ioi 0)) :
    repsIntegral R (fun τ ↦ G τ * latticeSeries lam Φ τ s) =
      (R.map fun ρ ↦ cosetCoeff lam Φ ρ s * stripMellin (fun v ↦ uFac lam ρ v * G (ρ • v)) s).sum := by
  set T := traceFun lam Φ R G s with hT
  set H : ℍ → ℂ := fun z ↦ ∑' x : X 1, Fs T s (rep 1 x • z) with hH
  -- the pieces `Gρ = u(ρ, ·) G(ρ ·)`
  have hGρc : ∀ ρ : SL(2, ℤ), Continuous fun v ↦ uFac lam ρ v * G (ρ • v) := fun ρ ↦
    (continuous_uFac lam ρ).mul (hG.comp (continuous_const_smul (ρ : GL (Fin 2) ℝ)))
  have hGρi : ∀ ρ ∈ R, IntegrableOn (Fs (fun v ↦ uFac lam ρ v * G (ρ • v)) s) (Milne.stripSet 1) := by
    intro ρ hρ
    refine integrableOn_Fs_strip (hGρc ρ) s ?_
    simpa only [norm_mul, norm_uFac, one_mul] using hint ρ hρ
  have hFsT : ∀ v, Fs T s v = (R.map fun ρ ↦ cosetCoeff lam Φ ρ s *
      Fs (fun v ↦ uFac lam ρ v * G (ρ • v)) s v).sum := by
    intro v
    simp only [Fs, hT, traceFun]
    rw [← List.sum_map_mul_right]
    congr 1
    exact List.map_congr_left fun ρ _ ↦ by ring
  have hFsT' : Fs T s = fun v ↦ (R.map fun ρ ↦ cosetCoeff lam Φ ρ s *
      Fs (fun v ↦ uFac lam ρ v * G (ρ • v)) s v).sum := funext hFsT
  have hTi : IntegrableOn (Fs T s) (Milne.stripSet 1) := by
    rw [hFsT']
    exact (integrableOn_list_map_sum R _ _ fun ρ hρ ↦ (hGρi ρ hρ).const_mul _).1
  -- the coset sum is the integral of the trace over `fd`
  have hpt := trace_eq hlam hR hU hΦ hΦC hs
  have h1 : repsIntegral R (fun τ ↦ G τ * latticeSeries lam Φ τ s) = ∫ τ in ModularGroup.fd, H τ := by
    unfold repsIntegral
    rw [← (integrableOn_list_map_sum R (fun ρ τ ↦ G (ρ • τ) * latticeSeries lam Φ (ρ • τ) s) _ hfd).2]
    exact setIntegral_congr_fun measurableSet_fd fun τ _ ↦ hpt τ
  have hinvH : ∀ γ ∈ Gamma0 1, ∀ z, H (γ • z) = H z := fun γ _ z ↦ trace_invariant hR hU hΦ s γ z
  have h2 : ∫ τ in ModularGroup.fd, H τ =
      ∑ q : SL(2, ℤ) ⧸ (Gamma0 1).withCenter, ∫ z in (q.out)⁻¹ • ModularGroup.fdo, H z := by
    rw [← repsIntegral_eq_sum_quotient isGamma0Reps_one H hinvH]
    simp [repsIntegral]
  rw [h1, h2]
  -- the level-one unfolding
  have hstab : ∀ β : Gamma0 1, β ∈ Milne.stabInfty (Gamma0 1) → ∀ v : ℍ,
      Fs T s ((β : SL(2, ℤ)) • v) = Fs T s v := by
    intro β hβ v
    have h10 : (β : SL(2, ℤ)) 1 0 = 0 := hβ
    obtain ⟨ε, hε, -, h11⟩ := Milne.sl_lower_zero (β : SL(2, ℤ)) h10
    have him : ((β : SL(2, ℤ)) • v).im = v.im := by
      rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
      rcases hε with rfl | rfl <;> simp [h10, h11]
    unfold Fs
    rw [hT, traceFun_stab hR hU hΦ s h10, him]
  have hFs : IntegrableOn (Fs T s) (Milne.stripSet (Milne.widthAtInfty (Gamma0 1))) := by
    rwa [widthAtInfty_Gamma0 1]
  obtain ⟨hix, hsN, hsum⟩ := Milne.unfolding_terms (Gamma0 1) (Fs T s) hstab hFs
  rw [widthAtInfty_Gamma0 1] at hsum
  have hstrip : ∫ z in Milne.stripSet 1, Fs T s z =
      (R.map fun ρ ↦ cosetCoeff lam Φ ρ s * stripMellin (fun v ↦ uFac lam ρ v * G (ρ • v)) s).sum := by
    rw [hFsT', (integrableOn_list_map_sum R _ _ fun ρ hρ ↦ (hGρi ρ hρ).const_mul _).2]
    congr 1
    refine List.map_congr_left fun ρ hρ ↦ ?_
    rw [integral_const_mul, integral_Fs_strip s (hGρi ρ hρ)]
  rw [← hstrip, ← hsum]
  set P : SL(2, ℤ) ⧸ (Gamma0 1).withCenter → Set ℍ := fun q ↦ (q.out)⁻¹ • ModularGroup.fdo
  have hsub : ∀ q, P q ⊆ ⋃ q, P q := fun q ↦ Set.subset_iUnion P q
  have hpiece : ∀ q, ∫ z in P q, H z = ∑' x : X 1, ∫ z in P q, Fs T s (rep 1 x • z) := by
    intro q
    refine (integral_tsum_of_summable_integral_norm (fun x ↦ (hix x).mono_set (hsub q)) ?_).symm
    refine Summable.of_nonneg_of_le (fun x ↦ integral_nonneg fun _ ↦ norm_nonneg _) (fun x ↦ ?_) hsN
    exact setIntegral_mono_set ((hix x).norm) (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
      (Filter.Eventually.of_forall (hsub q))
  simp_rw [P] at hpiece
  rw [Finset.sum_congr rfl fun q _ ↦ hpiece q]
  have hsumm : ∀ q ∈ (Finset.univ : Finset (SL(2, ℤ) ⧸ (Gamma0 1).withCenter)),
      Summable fun x : X 1 ↦ ∫ z in P q, Fs T s (rep 1 x • z) := by
    intro q _
    refine Summable.of_norm_bounded hsN fun x ↦ ?_
    exact (norm_integral_le_integral_norm _).trans
      (setIntegral_mono_set ((hix x).norm) (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
        (Filter.Eventually.of_forall (hsub q)))
  rw [← Summable.tsum_finsetSum hsumm]
  refine tsum_congr fun x ↦ ?_
  rw [integral_iUnion_fintype (fun q ↦ (ModularGroup.isOpen_smul_fdo _).measurableSet)
    (ModularGroup.pairwise_disjoint_smul_fdo_out_withCenter (Gamma0 1))
    (fun q ↦ (hix x).mono_set (hsub q))]
  rfl

end CosetUnfold

end ModularFormsKB.HalfIntegral
