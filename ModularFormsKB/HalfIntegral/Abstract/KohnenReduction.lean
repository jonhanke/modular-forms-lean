/-
# Kohnen's isomorphism from three smaller inputs

Level $4$, trivial character, relative to an abstract multiplier
system `M` (meant to be the theta multiplier `thetaMultiplierSystem`). The target statement is the named input
`KohnenIsomorphism` (`ModularFormsKB/HalfIntegral/Abstract/Kohnen.lean`):
$S^+_{k+1/2}(4) \cong S_{2k}(\mathrm{SL}_2(\mathbb Z))$, compatibly with $T(p^2) \mapsto T(p)$ for odd $p$.

Kohnen's proof (Kohnen 1980 `kohnen1980`, Thm. 1 and §§2–4 [unverified]) has three analytic ingredients, stated here as
named inputs:
1. `KohnenDLift`: for a fundamental discriminant $D$ with $(-1)^kD > 0$, the $D$-th lift
   $\sum c(n)q^n \mapsto \sum_n\big(\sum_{d\mid n}(\frac Dd)d^{k-1}c(|D|n^2/d^2)\big)q^n$ (`kohnenLiftCoeff`) maps
   $S^+_{k+1/2}(4)$ to $S_{2k}(1)$;
2. `KohnenDimension`: both spaces are finite-dimensional, of the same dimension (Kohnen gets this by comparing traces of
   Hecke operators; equivalently from the Cohen–Eisenstein series and explicit bases);
3. `KohnenLiftsInjective`: some finite linear combination of $D$-th lifts is injective on $S^+_{k+1/2}(4)$ (Kohnen: by
   multiplicity one, a Hecke eigenform $g$ maps to $c(|D|)F$, and every nonzero $g$ has some $c(|D|) \neq 0$).

**Proved here.** `kohnenIsomorphism_of_inputs`: the three inputs imply `KohnenIsomorphism M k`. The map is the
combination of lifts in input 3, built as a linear map using `Abstract.hasQExp_unique`; its Hecke compatibility for odd
$p$ is the proved coefficient identity `kohnenLiftCoeff_heckeT_of_fundamental` (`ModularFormsKB/HalfIntegral/KohnenLift.lean`);
bijectivity is injectivity plus equal finite dimension.
-/
import ModularFormsKB.HalfIntegral.Abstract.Kohnen
import ModularFormsKB.HalfIntegral.KohnenLift
import ModularFormsKB.HalfIntegral.QExpUnique

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup ModularForm
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- **The discriminants of Kohnen's theorem:** $D$ fundamental with $(-1)^k D > 0$. -/
def KohnenDisc (k : ℕ) (D : ℤ) : Prop := IsFundamentalDiscriminant D ∧ 0 < (-1) ^ k * D

/-- **The $D$-th lift maps $S^+_{k+1/2}(4)$ to $S_{2k}(1)$** (Kohnen 1980 `kohnen1980`, Thm. 1 [unverified]): for every
$g \in S^+_{k+1/2}(4)$ with coefficients $a$, the $q$-series with coefficients `kohnenLiftCoeff k D a` is a level one cusp
form of weight $2k$. Meant for $D$ with `KohnenDisc k D`. -/
@[kb "kohnen1980" "Thm. 1: the D-th lift maps S⁺_{k+1/2}(4) to S_{2k}(1), D fundamental, (-1)^k D > 0 [unverified]"]
structure KohnenDLift (M : MultiplierSystem) (k : ℕ) (D : ℤ) : Prop where
  lift : 1 ≤ k → ∀ f ∈ M.plusCuspForms k 1 1, ∀ a : ℕ → ℂ, Abstract.HasQExp f a →
    ∃ F : CuspForm 𝒮ℒ (2 * k : ℕ), Abstract.HasQExp F (kohnenLiftCoeff k D a)

/-- **$\dim S^+_{k+1/2}(4) = \dim S_{2k}(1)$** (Kohnen 1980 `kohnen1980`, §2–§3, via the trace formula [unverified]),
with both spaces finite-dimensional. -/
@[kb "kohnen1980" "dim S⁺_{k+1/2}(4) = dim S_{2k}(1) [unverified]"]
structure KohnenDimension (M : MultiplierSystem) (k : ℕ) : Prop where
  finite_plus : 1 ≤ k → FiniteDimensional ℂ (M.plusCuspForms k 1 1)
  finite_one : 1 ≤ k → FiniteDimensional ℂ (CuspForm 𝒮ℒ (2 * k : ℕ))
  finrank_eq : 1 ≤ k →
    Module.finrank ℂ (M.plusCuspForms k 1 1) = Module.finrank ℂ (CuspForm 𝒮ℒ (2 * k : ℕ))

/-- **A combination of $D$-th lifts is injective** (Kohnen 1980 `kohnen1980`, proof of Thm. 1 [unverified]): there are
finitely many admissible $D$ and scalars $c_D$ such that $g \in S^+_{k+1/2}(4)$ is $0$ as soon as
$\sum_D c_D\,\mathcal S_D(a) = 0$ for its coefficients $a$. -/
@[kb "kohnen1980" "proof of Thm. 1: a linear combination of the D-th lifts is injective on S⁺_{k+1/2}(4) [unverified]"]
structure KohnenLiftsInjective (M : MultiplierSystem) (k : ℕ) : Prop where
  combo : 1 ≤ k → ∃ (s : Finset ℤ) (c : ℤ → ℂ), (∀ D ∈ s, KohnenDisc k D) ∧
    ∀ f ∈ M.plusCuspForms k 1 1, ∀ a : ℕ → ℂ, Abstract.HasQExp f a →
      (∀ n, ∑ D ∈ s, c D * kohnenLiftCoeff k D a n = 0) → f = 0

namespace Abstract

theorem hasQExp_add {f g : ℍ → ℂ} {a b : ℕ → ℂ} (hf : HasQExp f a) (hg : HasQExp g b) :
    HasQExp (f + g) (a + b) := fun τ ↦ by
  simpa [add_mul] using (hf τ).add (hg τ)

theorem hasQExp_smul (c : ℂ) {f : ℍ → ℂ} {a : ℕ → ℂ} (hf : HasQExp f a) : HasQExp (c • f) (c • a) := fun τ ↦ by
  simpa [mul_assoc] using (hf τ).mul_left c

theorem hasQExp_zero : HasQExp (0 : ℍ → ℂ) 0 := fun τ ↦ by simp

/-- A function is determined by its $q$-expansion. -/
theorem eq_of_hasQExp {f g : ℍ → ℂ} {a : ℕ → ℂ} (hf : HasQExp f a) (hg : HasQExp g a) : f = g :=
  funext fun τ ↦ (hf τ).unique (hg τ)

end Abstract

section Reduction

variable (M : MultiplierSystem) (k : ℕ)

private theorem exists_coef (f : M.plusCuspForms k 1 1) : ∃ a, Abstract.HasQExp f a := by
  obtain ⟨_, a, ha, _⟩ := f.2
  exact ⟨a, ha⟩

/-- The (unique) coefficient sequence of a plus form. -/
private noncomputable def coef (f : M.plusCuspForms k 1 1) : ℕ → ℂ := Classical.choose (exists_coef M k f)

private theorem hasQExp_coef (f : M.plusCuspForms k 1 1) : Abstract.HasQExp f (coef M k f) :=
  Classical.choose_spec (exists_coef M k f)

private theorem coef_eq {f : M.plusCuspForms k 1 1} {a : ℕ → ℂ} (ha : Abstract.HasQExp f a) : coef M k f = a :=
  Abstract.hasQExp_unique (hasQExp_coef M k f) ha

/-- The combination $\sum_{D\in s} c_D\,\mathcal S_D$ of $D$-th lifts, on coefficients. -/
private noncomputable def combL (s : Finset ℤ) (c : ℤ → ℂ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) :=
  ∑ D ∈ s, c D • kohnenLiftLin k D

private theorem combL_apply (s : Finset ℤ) (c : ℤ → ℂ) (a : ℕ → ℂ) (n : ℕ) :
    combL k s c a n = ∑ D ∈ s, c D * kohnenLiftCoeff k D a n := by
  simp [combL, Finset.sum_apply]

private theorem cuspForm_eq_of_hasQExp {F G : CuspForm 𝒮ℒ (2 * k : ℕ)} {a : ℕ → ℂ}
    (hF : Abstract.HasQExp F a) (hG : Abstract.HasQExp G a) : F = G :=
  DFunLike.coe_injective (Abstract.eq_of_hasQExp hF hG)

private theorem exists_comb (hk : 1 ≤ k) (s : Finset ℤ) (c : ℤ → ℂ)
    (hL : ∀ D ∈ s, KohnenDLift M k D) (f : M.plusCuspForms k 1 1) :
    ∃ F : CuspForm 𝒮ℒ (2 * k : ℕ), Abstract.HasQExp F (combL k s c (coef M k f)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simpa [combL] using Abstract.hasQExp_zero⟩
  | insert D s hD ih =>
    obtain ⟨F, hF⟩ := ih (fun D' hD' ↦ hL D' (Finset.mem_insert_of_mem hD'))
    obtain ⟨G, hG⟩ := (hL D (Finset.mem_insert_self D s)).lift hk f f.2 (coef M k f) (hasQExp_coef M k f)
    refine ⟨c D • G + F, ?_⟩
    have h := Abstract.hasQExp_add (Abstract.hasQExp_smul (c D) hG) hF
    have e : combL k (insert D s) c (coef M k f) = c D • kohnenLiftCoeff k D (coef M k f) + combL k s c (coef M k f) := by
      simp [combL, Finset.sum_insert hD]
    rw [e]
    simpa using h

/-- **Kohnen's isomorphism from the lifts, an injective combination, and one dimension inequality:** the $D$-th lifts
land in $S_{2k}(1)$, a combination of them is injective, $S_{2k}(1)$ is finite-dimensional and
$\dim S_{2k}(1) \le \dim S^+_{k+1/2}(4)$. Finite dimension of the plus space and the reverse inequality follow from the
injective combination. The Hecke compatibility is the proved coefficient identity `kohnenLiftCoeff_heckeT_of_fundamental`. -/
@[kb "kohnen1980" "proof of Thm. 1: the isomorphism from the D-th lifts, injectivity and dim S_{2k}(1) ≤ dim S⁺ [unverified]"]
theorem kohnenIsomorphism_of_le (hL : ∀ D, KohnenDisc k D → KohnenDLift M k D)
    (hfin : 1 ≤ k → FiniteDimensional ℂ (CuspForm 𝒮ℒ (2 * k : ℕ)))
    (hle : 1 ≤ k → Module.finrank ℂ (CuspForm 𝒮ℒ (2 * k : ℕ)) ≤ Module.finrank ℂ (M.plusCuspForms k 1 1))
    (hinj : KohnenLiftsInjective M k) : KohnenIsomorphism M k := by
  refine ⟨fun hk ↦ ?_⟩
  obtain ⟨s, c, hs, hzero⟩ := hinj.combo hk
  have hL' : ∀ D ∈ s, KohnenDLift M k D := fun D hD ↦ hL D (hs D hD)
  let Ψ : M.plusCuspForms k 1 1 → CuspForm 𝒮ℒ (2 * k : ℕ) := fun f ↦ Classical.choose (exists_comb M k hk s c hL' f)
  have hΨ : ∀ f, Abstract.HasQExp (Ψ f) (combL k s c (coef M k f)) := fun f ↦
    Classical.choose_spec (exists_comb M k hk s c hL' f)
  let Φ : M.plusCuspForms k 1 1 →ₗ[ℂ] CuspForm 𝒮ℒ (2 * k : ℕ) :=
    { toFun := Ψ
      map_add' := fun f g ↦ by
        have hfg : coef M k (f + g) = coef M k f + coef M k g :=
          coef_eq M k (Abstract.hasQExp_add (hasQExp_coef M k f) (hasQExp_coef M k g))
        refine cuspForm_eq_of_hasQExp k (hΨ (f + g)) ?_
        rw [hfg, map_add]
        simpa using Abstract.hasQExp_add (hΨ f) (hΨ g)
      map_smul' := fun r f ↦ by
        have hrf : coef M k (r • f) = r • coef M k f :=
          coef_eq M k (Abstract.hasQExp_smul r (hasQExp_coef M k f))
        refine cuspForm_eq_of_hasQExp k (hΨ (r • f)) ?_
        rw [hrf, map_smul]
        simpa using Abstract.hasQExp_smul r (hΨ f) }
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have h0 : combL k s c (coef M k f) = 0 := by
      have h1 := hΨ f
      have h2 : Ψ f = 0 := hf
      rw [h2] at h1
      exact Abstract.hasQExp_unique h1 (by simpa using Abstract.hasQExp_zero)
    apply Subtype.ext
    refine hzero f f.2 (coef M k f) (hasQExp_coef M k f) fun n ↦ ?_
    rw [← combL_apply, h0]
    rfl
  have := hfin hk
  have : FiniteDimensional ℂ (M.plusCuspForms k 1 1) := Module.Finite.of_injective Φ hΦinj
  have hrank : Module.finrank ℂ (M.plusCuspForms k 1 1) = Module.finrank ℂ (CuspForm 𝒮ℒ (2 * k : ℕ)) :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective hΦinj) (hle hk)
  refine ⟨LinearMap.linearEquivOfInjective Φ hΦinj hrank, ?_⟩
  intro p hp hp2 f f' a b ha ha' hb
  rw [LinearMap.linearEquivOfInjective_apply] at hb ⊢
  have hca : coef M k f = a := coef_eq M k ha
  have hca' : coef M k f' = heckeT k 1 1 p a := coef_eq M k ha'
  have hbΦ : b = combL k s c a := by
    rw [← hca]; exact Abstract.hasQExp_unique hb (hΨ f)
  have heq : combL k s c (heckeT k 1 1 p a) = heckeTInt (2 * k) 1 1 p (combL k s c a) := by
    funext n
    have hterm : ∀ D ∈ s, c D * kohnenLiftCoeff k D (heckeT k 1 1 p a) n =
        c D * kohnenLiftCoeff k D a (p * n) + (if p ∣ n then (1 : DirichletCharacter ℂ 1) p *
          (p : ℂ) ^ (((2 * k : ℕ) : ℤ) - 1) * (c D * kohnenLiftCoeff k D a (n / p)) else 0) := by
      intro D hD
      rw [kohnenLiftCoeff_heckeT_of_fundamental k (hs D hD).1 (hs D hD).2 hp hp2 a]
      simp only [heckeTInt]
      split_ifs <;> ring
    rw [combL_apply, Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    simp only [heckeTInt, combL_apply]
    split_ifs <;> simp [Finset.mul_sum]
  have := hΨ f'
  rw [hca', heq, ← hbΦ] at this
  exact this

/-- **Kohnen's isomorphism from three inputs:** the $D$-th lifts land in $S_{2k}(1)$, the dimensions agree, and a
combination of lifts is injective (a corollary of `kohnenIsomorphism_of_le`). -/
@[kb "kohnen1980" "proof of Thm. 1: the isomorphism from the D-th lifts, dimension equality and injectivity [unverified]"]
theorem kohnenIsomorphism_of_inputs (hL : ∀ D, KohnenDisc k D → KohnenDLift M k D) (hdim : KohnenDimension M k)
    (hinj : KohnenLiftsInjective M k) : KohnenIsomorphism M k :=
  kohnenIsomorphism_of_le M k hL hdim.finite_one (fun hk ↦ (hdim.finrank_eq hk).ge) hinj

end Reduction

end ModularFormsKB.HalfIntegral
