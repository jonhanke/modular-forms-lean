/-
# Hecke stability of $M_{k+1/2}(4N,\chi)$ and $S_{k+1/2}(4N,\chi)$ for the theta multiplier

Shimura 1973 `shimura1973`, Thm. 1.7 [unverified]: for a prime $p \nmid 4N$,
$T(p^2)$ maps $M_{k+1/2}(4N,\chi)$ and $S_{k+1/2}(4N,\chi)$ to themselves and acts on $q$-expansions by `heckeT`.

`thetaMultiplierSystem_heckeStable` proves the named input `HeckeStable` for `thetaMultiplierSystem`, **conditional only on
Gauss's sign of the quadratic Gauss sum** (`QuadGaussSumSign`), which is needed to identify the coefficients. The form is
the explicit coset sum `heckeFun` (`HeckeOp.lean`):
* holomorphy and the cusp conditions: `heckeFun_mdiff`, `heckeFun_bdd`, `heckeFun_zero` (`HeckeCusp.lean`);
* the transformation law: `heckeFun_transforms` (`HeckeCoset.lean`, with the multiplier computations of `HeckeMult.lean`);
* the $q$-expansion: `heckeFun_hasQExp` (`HeckeCoeff.lean`).
-/
import ModularFormsKB.HalfIntegral.HeckeCoeff
import ModularFormsKB.HalfIntegral.HeckeCusp
import ModularFormsKB.HalfIntegral.HeckeCoset

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup

local notation "ℍ" => UpperHalfPlane

private lemma prime_ne_two_of_not_dvd {p N : ℕ} (hpN : ¬ p ∣ 4 * N) : p ≠ 2 := by
  rintro rfl
  exact hpN ⟨2 * N, by ring⟩

/-- **$T(p^2)$ on $M_{k+1/2}(4N,\chi)$ for the theta multiplier**, $p \nmid 4N$ prime: the coset sum of a modular form is a
modular form, and its $q$-expansion is `heckeT` of the $q$-expansion. -/
theorem heckeFun_mem_modularForms (hG : QuadGaussSumSign) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {p : ℕ}
    (hp : p.Prime) (hpN : ¬ p ∣ 4 * N) {f : ℍ → ℂ} (hf : f ∈ thetaMultiplierSystem.modularForms k N χ)
    {a : ℕ → ℂ} (ha : Abstract.HasQExp f a) :
    heckeFun k N χ ⟨p, hp.pos⟩ f ∈ thetaMultiplierSystem.modularForms k N χ ∧
      Abstract.HasQExp (heckeFun k N χ ⟨p, hp.pos⟩ f) (heckeT k N χ p a) :=
  ⟨⟨heckeFun_mdiff k N χ _ hf.holo, heckeFun_transforms k N χ ⟨p, hp.pos⟩ hp hpN hf.transforms,
      heckeFun_bdd k N χ _ hf.bdd_at_cusps⟩,
    heckeFun_hasQExp hG k N χ ⟨p, hp.pos⟩ hp (prime_ne_two_of_not_dvd hpN) ha⟩

/-- **$T(p^2)$ on $S_{k+1/2}(4N,\chi)$ for the theta multiplier**, $p \nmid 4N$ prime. -/
theorem heckeFun_mem_cuspForms (hG : QuadGaussSumSign) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {p : ℕ}
    (hp : p.Prime) (hpN : ¬ p ∣ 4 * N) {f : ℍ → ℂ} (hf : f ∈ thetaMultiplierSystem.cuspForms k N χ)
    {a : ℕ → ℂ} (ha : Abstract.HasQExp f a) :
    heckeFun k N χ ⟨p, hp.pos⟩ f ∈ thetaMultiplierSystem.cuspForms k N χ ∧
      Abstract.HasQExp (heckeFun k N χ ⟨p, hp.pos⟩ f) (heckeT k N χ p a) :=
  ⟨⟨heckeFun_mdiff k N χ _ hf.holo, heckeFun_transforms k N χ ⟨p, hp.pos⟩ hp hpN hf.transforms,
      heckeFun_zero k N χ _ hf.zero_at_cusps⟩,
    heckeFun_hasQExp hG k N χ ⟨p, hp.pos⟩ hp (prime_ne_two_of_not_dvd hpN) ha⟩

/-- **Shimura's Thm. 1.7 for the theta multiplier** (Shimura 1973 `shimura1973`, Thm. 1.7 [unverified]): the named input
`HeckeStable` holds for `thetaMultiplierSystem`, given Gauss's sign of the quadratic Gauss sum. -/
@[kb "shimura1973" "Thm. 1.7 for the theta multiplier: T(p²) preserves M and S_{k+1/2}(4N, χ), p ∤ 4N, given Gauss's sign [unverified]"]
theorem thetaMultiplierSystem_heckeStable (hG : QuadGaussSumSign) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) :
    HeckeStable thetaMultiplierSystem k N χ where
  modular p hp hpN f hf a ha :=
    ⟨_, (heckeFun_mem_modularForms hG k N χ hp hpN hf ha).1, (heckeFun_mem_modularForms hG k N χ hp hpN hf ha).2⟩
  cusp p hp hpN f hf a ha :=
    ⟨_, (heckeFun_mem_cuspForms hG k N χ hp hpN hf ha).1, (heckeFun_mem_cuspForms hG k N χ hp hpN hf ha).2⟩

/-- **Hecke stability for the concrete spaces** `halfIntModularForms`, `halfIntCuspForms` (Shimura 1973 `shimura1973`,
Thm. 1.7 [unverified]), given Gauss's sign of the quadratic Gauss sum. -/
@[kb "shimura1973" "Thm. 1.7 for the concrete spaces: T(p²) preserves halfIntModularForms and halfIntCuspForms, given Gauss's sign [unverified]"]
theorem halfInt_heckeStable_of_gaussSign (hG : QuadGaussSumSign) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {p : ℕ}
    (hp : p.Prime) (hpN : ¬ p ∣ 4 * N) :
    (∀ f ∈ halfIntModularForms k N χ, ∀ a : ℕ → ℂ, HasQExpansion f a →
      ∃ g ∈ halfIntModularForms k N χ, HasQExpansion g (heckeT k N χ p a)) ∧
    (∀ f ∈ halfIntCuspForms k N χ, ∀ a : ℕ → ℂ, HasQExpansion f a →
      ∃ g ∈ halfIntCuspForms k N χ, HasQExpansion g (heckeT k N χ p a)) := by
  have h := thetaMultiplierSystem_heckeStable hG k N χ
  rw [← thetaMultiplierSystem_modularForms, ← thetaMultiplierSystem_cuspForms]
  exact ⟨fun f hf a ha ↦ h.modular p hp hpN f hf a ha, fun f hf a ha ↦ h.cusp p hp hpN f hf a ha⟩

end ModularFormsKB.HalfIntegral
