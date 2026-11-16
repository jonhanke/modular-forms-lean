/-
# The nonvanishing input of Kohnen's isomorphism, reduced to $T^+(4)$

Level $4$, trivial character, relative to an abstract
multiplier system `M`. Kohnen's isomorphism reduces to, among others, the named input
`KohnenPlusNonvanishing` (a nonzero eigenform has $c(|D|) \ne 0$ for some fundamental $D$ with $(-1)^kD > 0$). This file
proves it from one statement about Kohnen's operator $T^+(4)$ (`heckeTPlusFour`, `ModularFormsKB/HalfIntegral/KohnenRecursion.lean`):

- `KohnenTPlusFourStable` (Kohnen 1980 `kohnen1980`, Prop. 2 [unverified]): $T^+(4)$, given on coefficients by
  $a(n) \mapsto a(4n) + \left(\frac{(-1)^kn}{2}\right)2^{k-1}a(n) + 2^{2k-1}a(n/4)$ for $(-1)^kn \equiv 0, 1 \bmod 4$ and
  $a(n) \mapsto 0$ otherwise, maps $S^+_{k+1/2}(4)$ to itself. (Corrected: an earlier `heckeTPlusFour`
  applied the formula at every index, and the statement was then false; see `heckeTPlusFour`.)

**Proved here.**
- `kohnenPlusTwoEigen_of_stable`: with multiplicity one (`KohnenPlusMultOne`), every eigenform of the $T(p^2)$, $p$ odd,
  is an eigenform of $T^+(4)$ (`KohnenPlusTwoEigen`), because $T^+(4)$ commutes with the $T(p^2)$ (`heckeTPlusFour_comm`).
- `kohnenPlusNonvanishing_of_twoEigen`: `KohnenPlusTwoEigen` implies `KohnenPlusNonvanishing`. If all $c(|D|)$ vanish,
  the Hecke recursion (`eq_zero_of_fundamental_coeff_eq_zero`) kills every $c(n)$, $n \ge 1$; a cusp form with only a
  constant term is $0$ (`Abstract.eq_zero_of_hasQExp_const`).
- `kohnenIsomorphism_of_tPlusFour`: Kohnen's isomorphism from `KohnenDLift`, `KohnenDimensionLe`,
  `KohnenPlusEigenbasis`, `KohnenPlusMultOne` and `KohnenTPlusFourStable`.
-/
import ModularFormsKB.HalfIntegral.Abstract.KohnenEigen
import ModularFormsKB.HalfIntegral.KohnenTPlusFourComm

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup ModularForm
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- **$T^+(4)$ maps the plus space to itself** (Kohnen 1980 `kohnen1980`, Prop. 2 [unverified]): for
$g \in S^+_{k+1/2}(4)$ with coefficients $c$, the $q$-series with coefficients $T^+(4)c$ (`heckeTPlusFour`: Kohnen's formula
at $(-1)^kn \equiv 0, 1 \bmod 4$, and $0$ at the other $n$) is again in $S^+_{k+1/2}(4)$. -/
@[kb "kohnen1980" "Prop. 2: T⁺(4): a(n) ↦ a(4n) + ((-1)^k n/2) 2^{k-1} a(n) + 2^{2k-1} a(n/4) for (-1)^k n ≡ 0,1 mod 4, 0 otherwise, maps S⁺_{k+1/2}(4) to itself [unverified]"]
structure KohnenTPlusFourStable (M : MultiplierSystem) (k : ℕ) : Prop where
  stable : 1 ≤ k → ∀ g ∈ M.plusCuspForms k 1 1, ∀ c : ℕ → ℂ, Abstract.HasQExp g c →
    ∃ g' ∈ M.plusCuspForms k 1 1, Abstract.HasQExp g' (heckeTPlusFour k c)

/-- **Eigenforms of the odd $T(p^2)$ are eigenforms of $T^+(4)$** (Kohnen 1980 `kohnen1980`, from Prop. 2 and multiplicity
one [unverified]). Proved from `KohnenTPlusFourStable` and `KohnenPlusMultOne` in `kohnenPlusTwoEigen_of_stable`. -/
@[kb "kohnen1980" "an eigenform of the T(p²), p odd, in S⁺_{k+1/2}(4) is an eigenform of T⁺(4) [unverified]"]
structure KohnenPlusTwoEigen (M : MultiplierSystem) (k : ℕ) : Prop where
  two_eigen : 1 ≤ k → ∀ (g : ℍ → ℂ) (μ : ℕ → ℂ), IsPlusEigenform M k g μ →
    ∀ c : ℕ → ℂ, Abstract.HasQExp g c → ∃ t : ℂ, heckeTPlusFour k c = t • c

namespace Abstract

/-- **A cusp form with only a constant term is $0$:** if $g \in S_{k+1/2}(4N,\chi)$ has coefficients $c$ with $c(n) = 0$
for $n \ge 1$, then $g$ is the constant $c(0)$, and vanishing at the cusp $\infty$ forces $c(0) = 0$. -/
theorem eq_zero_of_hasQExp_const {M : MultiplierSystem} {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)} {g : ℍ → ℂ}
    (hg : g ∈ M.cuspForms k N χ) {c : ℕ → ℂ} (hc : HasQExp g c) (h : ∀ n : ℕ, 0 < n → c n = 0) : g = 0 := by
  have hconst : ∀ τ : ℍ, g τ = c 0 := by
    intro τ
    have hs : HasSum (fun n : ℕ ↦ c n * cexp (2 * π * I * n * τ)) (c 0) := by
      have := hasSum_single (f := fun n : ℕ ↦ c n * cexp (2 * π * I * n * τ)) 0 fun n hn ↦ by
        rw [h n (Nat.pos_of_ne_zero hn), zero_mul]
      simpa using this
    exact (hc τ).unique hs
  have hz := hg.zero_at_cusps 1
  have hnorm : ∀ τ : ℍ, cuspNorm k g 1 τ = ‖c 0‖ := by
    intro τ
    simp [cuspNorm, hconst]
  rw [UpperHalfPlane.isZeroAtImInfty_iff] at hz
  have hc0 : c 0 = 0 := by
    by_contra hne
    have hpos : 0 < ‖c 0‖ := norm_pos_iff.2 hne
    obtain ⟨A, hA⟩ := hz (‖c 0‖ / 2) (by positivity)
    let τ : ℍ := ⟨(max A 1 : ℝ) * I, by simp⟩
    have := hA τ (by simp [τ, UpperHalfPlane.im])
    rw [hnorm, norm_norm] at this
    linarith
  funext τ
  rw [hconst, hc0]
  rfl

end Abstract

variable (M : MultiplierSystem) (k : ℕ)

private theorem plusCond_of_mem {g : ℍ → ℂ} (hg : g ∈ M.plusCuspForms k 1 1) {c : ℕ → ℂ} (hc : Abstract.HasQExp g c) :
    c ∈ plusSeq k := by
  obtain ⟨-, a, ha, hap⟩ := hg
  rw [Abstract.hasQExp_unique hc ha]
  exact hap

/-- **`KohnenPlusTwoEigen` implies `KohnenPlusNonvanishing`:** a nonzero eigenform has a nonzero fundamental
coefficient, by the Hecke recursion at odd primes and at $2$. -/
@[kb "kohnenzagier1981" "§II: c(|D|m²) is determined by c(|D|) and the eigenvalues, so some c(|D|) ≠ 0 [unverified]"]
theorem kohnenPlusNonvanishing_of_twoEigen (h : KohnenPlusTwoEigen M k) : KohnenPlusNonvanishing M k := by
  refine ⟨fun hk g μ hg hne c hc ↦ ?_⟩
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  obtain ⟨c', hc', heig⟩ := hg.2
  have hcc : c' = c := Abstract.hasQExp_unique hc' hc
  subst hcc
  obtain ⟨t, ht⟩ := h.two_eigen hk g μ hg c' hc
  have h0 := eq_zero_of_fundamental_coeff_eq_zero (plusCond_of_mem M k hg.1 hc) μ heig t ht hall
  exact hne (Abstract.eq_zero_of_hasQExp_const (M.plusCuspForms_le k 1 1 hg.1) hc h0)

/-- **$T^+(4)$-stability and multiplicity one give `KohnenPlusTwoEigen`:** if $g$ is an eigenform with eigenvalues
$\mu$, the form $g'$ with coefficients $T^+(4)c$ is an eigenform with the same eigenvalues (`heckeTPlusFour_comm`), so
$g' = t g$ by multiplicity one. -/
@[kb "kohnen1980" "Prop. 2 and multiplicity one: eigenforms of the odd T(p²) are T⁺(4)-eigenforms [unverified]"]
theorem kohnenPlusTwoEigen_of_stable (hS : KohnenTPlusFourStable M k) (h1 : KohnenPlusMultOne M k) :
    KohnenPlusTwoEigen M k := by
  refine ⟨fun hk g μ hg c hc ↦ ?_⟩
  obtain ⟨c', hc', heig⟩ := hg.2
  have hcc : c' = c := Abstract.hasQExp_unique hc' hc
  subst hcc
  by_cases hg0 : g = 0
  · subst hg0
    have : c' = 0 := Abstract.hasQExp_unique hc Abstract.hasQExp_zero
    subst this
    refine ⟨0, ?_⟩
    rw [zero_smul]
    exact (heckeTPlusFourLin k).map_zero
  obtain ⟨g', hg', hc4⟩ := hS.stable hk g hg.1 c' hc
  have hg'eig : IsPlusEigenform M k g' μ := by
    refine ⟨hg', heckeTPlusFour k c', hc4, fun p hp hp2 ↦ ?_⟩
    rw [heckeTPlusFour_comm k hp hp2, heig p hp hp2]
    exact (heckeTPlusFourLin k).map_smul (μ p) c'
  obtain ⟨t, ht⟩ := h1.mult_one hk g g' μ hg hg'eig hg0
  refine ⟨t, ?_⟩
  rw [ht] at hc4
  exact Abstract.hasQExp_unique hc4 (Abstract.hasQExp_smul t hc)

/-- **Kohnen's isomorphism from the lifts, one dimension inequality, an eigenbasis, multiplicity one and $T^+(4)$:**
the round 2 input `KohnenPlusNonvanishing` is replaced by `KohnenTPlusFourStable`. -/
@[kb "kohnen1980" "Thm. 1 from the D-th lifts, dim S_{2k}(1) ≤ dim S⁺, an eigenbasis, multiplicity one and T⁺(4) [unverified]"]
theorem kohnenIsomorphism_of_tPlusFour (hL : ∀ D, KohnenDisc k D → KohnenDLift M k D) (hdim : KohnenDimensionLe M k)
    (hB : KohnenPlusEigenbasis M k) (h1 : KohnenPlusMultOne M k) (hS : KohnenTPlusFourStable M k) :
    KohnenIsomorphism M k :=
  kohnenIsomorphism_of_eigen M k hL hdim hB h1
    (kohnenPlusNonvanishing_of_twoEigen M k (kohnenPlusTwoEigen_of_stable M k hS h1))

end ModularFormsKB.HalfIntegral
