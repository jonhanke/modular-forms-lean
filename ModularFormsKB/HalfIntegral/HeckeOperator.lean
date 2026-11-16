/-
# Shimura's $T(p^2)$ as commuting linear operators on $M_{k+1/2}(4N,\chi)$ and $S_{k+1/2}(4N,\chi)$

Loose end LE-MF-0167.

Until now $T(p^2)$ was available as the coset sum `heckeFun` on functions and as Shimura's coefficient formula `heckeT` on
coefficient sequences, with the two related through Gauss's sign (`heckeFun_hasQExp`, proved by `quadGaussSumSign`).
The commutation `heckeT_comm` was proved on coefficient sequences only. This file makes $T(p^2)$, for a prime
$p \nmid 4N$, a $\mathbb C$-linear endomorphism of the spaces of the theta multiplier (`heckeOpModular`, `heckeOpCusp`)
and proves that any two of them commute (`heckeOpModular_comm`, `heckeOpCusp_comm`; Shimura 1973 `shimura1973`, §1
[unverified]):

- `MultiplierSystem.exists_hasQExp`: every $f \in M_{k+1/2}(4N,\chi)$, for any multiplier system, has a $q$-expansion
  ($f$ has period 1 since $T \in \Gamma_0(4N)$ and $j(T,\tau) = 1$; Mathlib's `UpperHalfPlane.hasSum_qExpansion`);
- the operators act on $q$-expansions by `heckeT` (`hasQExp_heckeOpCusp`), and commute because `heckeT` does
  (`heckeT_comm`) and a function is determined by its $q$-expansion.
-/
import ModularFormsKB.HalfIntegral.GaussSign
import ModularFormsKB.HalfIntegral.QExpUnique
import Mathlib.NumberTheory.ModularForms.QExpansion

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup
open scoped Real

local notation "ℍ" => UpperHalfPlane

private lemma prime_ne_two_of_not_dvd' {p N : ℕ} (hpN : ¬ p ∣ 4 * N) : p ≠ 2 := by
  rintro rfl
  exact hpN ⟨2 * N, by ring⟩

/-- **Every modular form of weight $k+\tfrac12$ has a $q$-expansion**, for any multiplier system. -/
theorem MultiplierSystem.exists_hasQExp (M : MultiplierSystem) {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)}
    {f : ℍ → ℂ} (hf : f ∈ M.modularForms k N χ) : ∃ a : ℕ → ℂ, Abstract.HasQExp f a := by
  have hT : ModularGroup.T ∈ Gamma0 (4 * N) := by
    rw [Gamma0_mem]; simp [ModularGroup.coe_T]
  have hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1 := by
    refine UpperHalfPlane.periodic_comp_ofComplex (fun τ ↦ ?_)
    have h := hf.transforms _ hT τ
    rw [UpperHalfPlane.modular_T_smul, M.j_T] at h
    simpa [ModularGroup.coe_T] using h
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty f := by
    have h := hf.bdd_at_cusps 1
    have e : Abstract.cuspNorm k f 1 = fun τ ↦ ‖f τ‖ := by
      funext τ; simp [Abstract.cuspNorm]
    rw [e, UpperHalfPlane.isBoundedAtImInfty_iff] at h
    rw [UpperHalfPlane.isBoundedAtImInfty_iff]
    obtain ⟨M', A, hA⟩ := h
    exact ⟨M', A, fun z hz ↦ by simpa using hA z hz⟩
  refine ⟨fun m ↦ (UpperHalfPlane.qExpansion 1 f).coeff m, fun τ ↦ ?_⟩
  have h := UpperHalfPlane.hasSum_qExpansion one_pos hper hf.holo hbdd τ
  convert h using 2 with m
  rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- **Every cusp form of weight $k+\tfrac12$ has a $q$-expansion.** -/
theorem MultiplierSystem.exists_hasQExp_of_mem_cuspForms (M : MultiplierSystem) {k N : ℕ}
    {χ : DirichletCharacter ℂ (4 * N)} {f : ℍ → ℂ} (hf : f ∈ M.cuspForms k N χ) :
    ∃ a : ℕ → ℂ, Abstract.HasQExp f a :=
  MultiplierSystem.exists_hasQExp M (M.cuspForms_le k N χ hf)

/-- The coset sum `heckeFun` is $\mathbb C$-linear in the function. -/
theorem heckeFun_add (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (p : ℕ+) (f g : ℍ → ℂ) :
    heckeFun k N χ p (f + g) = heckeFun k N χ p f + heckeFun k N χ p g := by
  funext τ
  simp only [heckeFun, Pi.add_apply, Finset.sum_add_distrib, mul_add]
  ring

theorem heckeFun_smul (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (p : ℕ+) (c : ℂ) (f : ℍ → ℂ) :
    heckeFun k N χ p (c • f) = c • heckeFun k N χ p f := by
  funext τ
  have h2 : ∑ i ∈ Finset.range (p : ℕ), (jacobiSym i p : ℂ) * (c * f (affPt p p (4 * i) τ)) =
      c * ∑ i ∈ Finset.range (p : ℕ), (jacobiSym i p : ℂ) * f (affPt p p (4 * i) τ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
  simp only [heckeFun, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, h2]
  ring

/-- **Shimura's $T(p^2)$ on $M_{k+1/2}(4N,\chi)$** for the theta multiplier, $p \nmid 4N$ prime: the coset sum `heckeFun`. -/
noncomputable def heckeOpModular (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ 4 * N) :
    thetaMultiplierSystem.modularForms k N χ →ₗ[ℂ] thetaMultiplierSystem.modularForms k N χ where
  toFun f := ⟨heckeFun k N χ ⟨p, hp.pos⟩ f,
    ⟨heckeFun_mdiff k N χ _ f.2.holo, heckeFun_transforms k N χ ⟨p, hp.pos⟩ hp hpN f.2.transforms,
      heckeFun_bdd k N χ _ f.2.bdd_at_cusps⟩⟩
  map_add' f g := Subtype.ext (heckeFun_add k N χ _ f g)
  map_smul' c f := Subtype.ext (heckeFun_smul k N χ _ c f)

/-- **Shimura's $T(p^2)$ on $S_{k+1/2}(4N,\chi)$** for the theta multiplier, $p \nmid 4N$ prime. -/
noncomputable def heckeOpCusp (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ 4 * N) :
    thetaMultiplierSystem.cuspForms k N χ →ₗ[ℂ] thetaMultiplierSystem.cuspForms k N χ where
  toFun f := ⟨heckeFun k N χ ⟨p, hp.pos⟩ f,
    ⟨heckeFun_mdiff k N χ _ f.2.holo, heckeFun_transforms k N χ ⟨p, hp.pos⟩ hp hpN f.2.transforms,
      heckeFun_zero k N χ _ f.2.zero_at_cusps⟩⟩
  map_add' f g := Subtype.ext (heckeFun_add k N χ _ f g)
  map_smul' c f := Subtype.ext (heckeFun_smul k N χ _ c f)

theorem coe_heckeOpModular (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ 4 * N) (f : thetaMultiplierSystem.modularForms k N χ) :
    ((heckeOpModular k N χ hp hpN f : thetaMultiplierSystem.modularForms k N χ) : ℍ → ℂ) =
      heckeFun k N χ ⟨p, hp.pos⟩ f := rfl

theorem coe_heckeOpCusp (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ 4 * N) (f : thetaMultiplierSystem.cuspForms k N χ) :
    ((heckeOpCusp k N χ hp hpN f : thetaMultiplierSystem.cuspForms k N χ) : ℍ → ℂ) =
      heckeFun k N χ ⟨p, hp.pos⟩ f := rfl

/-- **$T(p^2)$ acts on $q$-expansions by Shimura's formula** `heckeT`. -/
theorem hasQExp_heckeOpModular (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ 4 * N) (f : thetaMultiplierSystem.modularForms k N χ) {a : ℕ → ℂ}
    (ha : Abstract.HasQExp f a) :
    Abstract.HasQExp (heckeOpModular k N χ hp hpN f) (heckeT k N χ p a) := by
  rw [coe_heckeOpModular]
  exact heckeFun_hasQExp quadGaussSumSign k N χ ⟨p, hp.pos⟩ hp (prime_ne_two_of_not_dvd' hpN) ha

theorem hasQExp_heckeOpCusp (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ 4 * N) (f : thetaMultiplierSystem.cuspForms k N χ) {a : ℕ → ℂ}
    (ha : Abstract.HasQExp f a) :
    Abstract.HasQExp (heckeOpCusp k N χ hp hpN f) (heckeT k N χ p a) := by
  rw [coe_heckeOpCusp]
  exact heckeFun_hasQExp quadGaussSumSign k N χ ⟨p, hp.pos⟩ hp (prime_ne_two_of_not_dvd' hpN) ha

/-- **The operators $T(p^2)$, $p \nmid 4N$, commute on $M_{k+1/2}(4N,\chi)$.** -/
theorem heckeOpModular_comm (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {p q : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ 4 * N) (hq : q.Prime) (hqN : ¬ q ∣ 4 * N) :
    heckeOpModular k N χ hp hpN ∘ₗ heckeOpModular k N χ hq hqN =
      heckeOpModular k N χ hq hqN ∘ₗ heckeOpModular k N χ hp hpN := by
  by_cases hpq : p = q
  · subst hpq; rfl
  refine LinearMap.ext fun f ↦ Subtype.ext ?_
  obtain ⟨a, ha⟩ := MultiplierSystem.exists_hasQExp _ f.2
  have h1 := hasQExp_heckeOpModular k N χ hp hpN _ (hasQExp_heckeOpModular k N χ hq hqN f ha)
  have h2 := hasQExp_heckeOpModular k N χ hq hqN _ (hasQExp_heckeOpModular k N χ hp hpN f ha)
  rw [heckeT_comm k N χ hp hq hpq a] at h1
  exact funext fun τ ↦ (h1 τ).unique (h2 τ)

/-- **The operators $T(p^2)$, $p \nmid 4N$, commute on $S_{k+1/2}(4N,\chi)$.** -/
theorem heckeOpCusp_comm (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {p q : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ 4 * N) (hq : q.Prime) (hqN : ¬ q ∣ 4 * N) :
    heckeOpCusp k N χ hp hpN ∘ₗ heckeOpCusp k N χ hq hqN = heckeOpCusp k N χ hq hqN ∘ₗ heckeOpCusp k N χ hp hpN := by
  by_cases hpq : p = q
  · subst hpq; rfl
  refine LinearMap.ext fun f ↦ Subtype.ext ?_
  obtain ⟨a, ha⟩ := MultiplierSystem.exists_hasQExp_of_mem_cuspForms _ f.2
  have h1 := hasQExp_heckeOpCusp k N χ hp hpN _ (hasQExp_heckeOpCusp k N χ hq hqN f ha)
  have h2 := hasQExp_heckeOpCusp k N χ hq hqN _ (hasQExp_heckeOpCusp k N χ hp hpN f ha)
  rw [heckeT_comm k N χ hp hq hpq a] at h1
  exact funext fun τ ↦ (h1 τ).unique (h2 τ)

end ModularFormsKB.HalfIntegral
