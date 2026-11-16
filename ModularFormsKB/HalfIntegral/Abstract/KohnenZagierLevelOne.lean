/-
# Level one bridge for the Kohnen–Zagier formula: Hecke operators and multiplicity one

Tau Ceti has the Hecke operator `TauCeti.heckeTCuspLevelOne` on
$S_w(\mathrm{SL}_2(\mathbb Z))$ and strong multiplicity one for newforms. This file connects them to the coefficient
formulas of this library (`heckeTInt`, `Abstract.HasQExp`):

- `hasQExp_qExpansion`: a level one cusp form has the $q$-expansion given by Mathlib's `qExpansion`;
- `hasQExp_heckeTCuspLevelOne`: $T(p)F$ has the coefficients `heckeTInt w 1 1 p b` (for $F$ with coefficients $b$);
- `heckeTCuspLevelOne_eq_smul`: if the coefficients are a $T(p)$-eigenvector, so is the form;
- `eq_smul_of_odd_eigen`: **multiplicity one away from $2$:** if $F \ne 0$ and $G$ are level one cusp forms with
  $T(p)F = \mu_pF$ and $T(p)G = \mu_pG$ for all odd primes $p$, then $G$ is a multiple of $F$. Proof: in the basis of
  newforms (`levelOneNewformBasis`), the coordinates of an odd-prime eigenvector with eigenvalues $\mu$ are supported on
  newforms with eigenvalues $\mu$ at odd primes; there is only one such newform (`Newform.eq_of_forall_notMem_prime_eigenvalue_eq`
  with the exceptional set $\{2\}$).
-/
import ModularFormsKB.HalfIntegral.Abstract.KohnenZagierAdjoint
import TauCeti.NumberTheory.ModularForms.LevelOne.Eigenbasis
import TauCeti.NumberTheory.ModularForms.Newforms.StrongMultiplicityOne.Basic

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup UpperHalfPlane ModularForm HeckeRing.GL2 TauCeti
open scoped Real

/-- **A level one cusp form has the $q$-expansion `qExpansion`.** -/
theorem hasQExp_qExpansion {w : ℤ} (F : CuspForm 𝒮ℒ w) :
    Abstract.HasQExp F (fun n ↦ (UpperHalfPlane.qExpansion 1 F).coeff n) := fun τ ↦ by
  have hp : (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    have := Subgroup.strictWidthInfty_mem_strictPeriods (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))
    rwa [Subgroup.strictWidthInfty_SL2Z] at this
  have h := UpperHalfPlane.hasSum_qExpansion (h := 1) (f := F) one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex F hp) (ModularFormClass.holo F)
    (ModularFormClass.bdd_at_infty F) τ
  convert h using 2 with m
  rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- **The coefficients of $T(p)F$** (Tau Ceti's operator) are `heckeTInt`. -/
theorem coeff_heckeTCuspLevelOne (w : ℕ) {p : ℕ} [NeZero p] (hp : p.Prime) (F : CuspForm 𝒮ℒ (w : ℤ)) (m : ℕ) :
    (UpperHalfPlane.qExpansion 1 (heckeTCuspLevelOne (w : ℤ) p F)).coeff m =
      heckeTInt w 1 1 p (fun n ↦ (UpperHalfPlane.qExpansion 1 F).coeff n) m := by
  rw [qExpansion_coeff_heckeTCuspLevelOne]
  unfold heckeTInt
  by_cases hd : p ∣ m
  · obtain ⟨t, rfl⟩ := hd
    have hg : (p * t).gcd p = p := Nat.gcd_eq_right (dvd_mul_right p t)
    have hpos : 0 < p := hp.pos
    rw [hg, hp.divisors, Finset.sum_pair hp.one_lt.ne, if_pos (dvd_mul_right p t)]
    have e1 : p * t * p / 1 ^ 2 = p * (p * t) := by simp [mul_comm, mul_left_comm]
    have e2 : p * t * p / p ^ 2 = t := by
      rw [show p * t * p = p ^ 2 * t by ring, Nat.mul_div_cancel_left _ (by positivity)]
    have e3 : p * t / p = t := Nat.mul_div_cancel_left _ hpos
    rw [e1, e2, e3]
    simp
  · have hg : m.gcd p = 1 := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hd)
    rw [hg, if_neg hd]
    simp [mul_comm]

/-- **$T(p)F$ has the coefficients `heckeTInt w 1 1 p b`.** -/
theorem hasQExp_heckeTCuspLevelOne (w : ℕ) {p : ℕ} [NeZero p] (hp : p.Prime) (F : CuspForm 𝒮ℒ (w : ℤ))
    {b : ℕ → ℂ} (hF : Abstract.HasQExp F b) :
    Abstract.HasQExp (heckeTCuspLevelOne (w : ℤ) p F) (heckeTInt w 1 1 p b) := by
  have hb : b = fun n ↦ (UpperHalfPlane.qExpansion 1 F).coeff n := funext (hasQExp_coeff_eq_qExpansion F hF)
  subst hb
  have := hasQExp_qExpansion (heckeTCuspLevelOne (w : ℤ) p F)
  convert this using 1
  funext m
  exact (coeff_heckeTCuspLevelOne w hp F m).symm

/-- **Eigenvectors on coefficients are eigenforms.** -/
theorem heckeTCuspLevelOne_eq_smul (w : ℕ) {p : ℕ} [NeZero p] (hp : p.Prime) (F : CuspForm 𝒮ℒ (w : ℤ))
    {b : ℕ → ℂ} (hF : Abstract.HasQExp F b) {μ : ℂ} (h : heckeTInt w 1 1 p b = μ • b) :
    heckeTCuspLevelOne (w : ℤ) p F = μ • F := by
  refine cuspForm_ext_of_hasQExp (a := μ • b) ?_ ?_
  · rw [← h]; exact hasQExp_heckeTCuspLevelOne w hp F hF
  · simpa using Abstract.hasQExp_smul μ hF

/-- The $p$-th eigenvalue of a level one newform. -/
noncomputable def newformEig {w : ℤ} (f : Newform 1 w) (p : ℕ) : ℂ := (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff p

/-- **Coordinates in the newform basis are scaled by the eigenvalues.** -/
theorem repr_heckeTCuspLevelOne (w : ℤ) (p : Nat.Primes) (h : CuspForm 𝒮ℒ w) (f : Newform 1 w) :
    (levelOneNewformBasis w).repr (heckeTCuspLevelOne w p.1 h) f =
      newformEig f p.1 * (levelOneNewformBasis w).repr h f := by
  let B := levelOneNewformBasis w
  let L1 : CuspForm 𝒮ℒ w →ₗ[ℂ] ℂ := (Finsupp.lapply f) ∘ₗ B.repr.toLinearMap ∘ₗ (heckeTCuspLevelOne w p.1)
  let L2 : CuspForm 𝒮ℒ w →ₗ[ℂ] ℂ := newformEig f p.1 • ((Finsupp.lapply f) ∘ₗ B.repr.toLinearMap)
  have : L1 = L2 := by
    refine B.ext fun f' ↦ ?_
    simp only [L1, L2, LinearMap.comp_apply, LinearMap.smul_apply, Finsupp.lapply_apply,
      LinearEquiv.coe_coe, B, heckeTCuspLevelOne_levelOneNewformBasis, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases hf : f' = f
    · subst hf; simp [newformEig]
    · simp [hf]
  exact LinearMap.congr_fun this h

/-- **Multiplicity one away from $2$ at level one.** If $F \ne 0$ and $G$ are eigenforms of $T(p)$ for all odd
primes $p$ with the same eigenvalues $\mu_p$, then $G$ is a multiple of $F$. -/
theorem eq_smul_of_odd_eigen (w : ℤ) (F G : CuspForm 𝒮ℒ w) (hF : F ≠ 0) (μ : Nat.Primes → ℂ)
    (hFe : ∀ p : Nat.Primes, p.1 ≠ 2 → heckeTCuspLevelOne w p.1 F = μ p • F)
    (hGe : ∀ p : Nat.Primes, p.1 ≠ 2 → heckeTCuspLevelOne w p.1 G = μ p • G) :
    ∃ lam : ℂ, G = lam • F := by
  let B := levelOneNewformBasis w
  -- coordinates supported on newforms with eigenvalue μ at odd primes
  have key : ∀ (h : CuspForm 𝒮ℒ w), (∀ p : Nat.Primes, p.1 ≠ 2 → heckeTCuspLevelOne w p.1 h = μ p • h) →
      ∀ f : Newform 1 w, B.repr h f ≠ 0 → ∀ p : Nat.Primes, p.1 ≠ 2 → newformEig f p.1 = μ p := by
    intro h hh f hf p hp
    have e := repr_heckeTCuspLevelOne w p h f
    rw [hh p hp, map_smul, Finsupp.smul_apply, smul_eq_mul] at e
    exact (mul_right_cancel₀ hf e).symm
  have hFne : B.repr F ≠ 0 := fun h ↦ hF (B.repr.injective (by simpa using h))
  obtain ⟨f₀, hf₀⟩ := Finsupp.ne_iff.mp hFne
  have hf₀' : B.repr F f₀ ≠ 0 := by simpa using hf₀
  have hunique : ∀ f : Newform 1 w, (∀ p : Nat.Primes, p.1 ≠ 2 → newformEig f p.1 = μ p) → f = f₀ := by
    intro f hf
    have h₀ := key F hFe f₀ hf₀'
    refine Newform.eq_of_forall_notMem_prime_eigenvalue_eq (Subsingleton.elim f.χ f₀.χ) (S := {2})
      fun p hp hp1 hpS ↦ ?_
    have hp2 : p ≠ 2 := by simpa using hpS
    rw [← f.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue f.isNorm ⟨p, hp.pos⟩ hp1,
      ← f₀.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue f₀.isNorm ⟨p, hp.pos⟩ hp1]
    exact (hf ⟨p, hp⟩ hp2).trans (h₀ ⟨p, hp⟩ hp2).symm
  refine ⟨B.repr G f₀ / B.repr F f₀, B.repr.injective ?_⟩
  ext f
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases hf : f = f₀
  · subst hf; field_simp
  · have h1 : B.repr F f = 0 := by
      by_contra hne
      exact hf (hunique f (key F hFe f hne))
    have h2 : B.repr G f = 0 := by
      by_contra hne
      exact hf (hunique f (key G hGe f hne))
    simp [h1, h2]

end ModularFormsKB.HalfIntegral
