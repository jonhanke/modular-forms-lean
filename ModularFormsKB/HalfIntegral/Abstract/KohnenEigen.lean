/-
# Injectivity of a combination of Kohnen's lifts, from an eigenbasis and multiplicity one

Level $4$, trivial character, relative to an abstract
multiplier system `M`. The first round reduced Kohnen's isomorphism to three named inputs; this file reduces the third,
`KohnenLiftsInjective` (a finite combination $\sum_D c_D\mathcal S_D$ of $D$-th lifts is injective on $S^+_{k+1/2}(4)$),
to three statements about Hecke eigenforms. An *eigenform* (`IsPlusEigenform`) is a $g \in S^+_{k+1/2}(4)$ whose
coefficients $c$ satisfy $T(p^2)c = \mu(p)\,c$ for every odd prime $p$.
1. `KohnenPlusEigenbasis`: $S^+_{k+1/2}(4)$ has a basis of eigenforms (the $T(p^2)$ commute and are hermitian for the
   Petersson product);
2. `KohnenPlusMultOne`: multiplicity one, i.e. two eigenforms with the same eigenvalues at all odd primes are
   proportional;
3. `KohnenPlusNonvanishing`: every nonzero eigenform has $c(|D|) \ne 0$ for some fundamental $D$ with $(-1)^kD > 0$.

**Proved here.** `kohnenLiftsInjective_of_eigen`: the three statements imply `KohnenLiftsInjective`. Kohnen's argument:
for a basis $g_1, \dots, g_r$ of eigenforms pick $D_i$ with $c_i(|D_i|) \ne 0$, and scalars $w_D$ avoiding the finitely
many hyperplanes $\sum_D w_D c_i(|D|) = 0$ (`Module.Dual.exists_forall_ne_zero_of_forall_exists`). The images
$\Lambda c_i$ under $\Lambda = \sum_D w_D\mathcal S_D$ have first coefficient $\sum_D w_D c_i(|D|) \ne 0$, are
$T(p)$-eigenvectors with the eigenvalues of $g_i$ (`kohnenLiftCoeff_heckeT_of_fundamental`), and these systems are
pairwise distinct by multiplicity one, so the $\Lambda c_i$ are linearly independent (`linearIndependent_of_jointEigen`).

`kohnenIsomorphism_of_eigen` combines this with `kohnenIsomorphism_of_dimLe`: Kohnen's isomorphism from `KohnenDLift`,
`KohnenDimensionLe` and the three eigenform statements.
-/
import ModularFormsKB.HalfIntegral.Abstract.KohnenDimension
import ModularFormsKB.HalfIntegral.JointEigen
import Mathlib.Algebra.Module.Submodule.Union

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup ModularForm

local notation "ℍ" => UpperHalfPlane

/-- **A plus-space eigenform with eigenvalues $\mu$:** $g \in S^+_{k+1/2}(4)$ has coefficients $c$ with
$T(p^2)c = \mu(p)\,c$ for every odd prime $p$. -/
def IsPlusEigenform (M : MultiplierSystem) (k : ℕ) (g : ℍ → ℂ) (μ : ℕ → ℂ) : Prop :=
  g ∈ M.plusCuspForms k 1 1 ∧ ∃ c : ℕ → ℂ, Abstract.HasQExp g c ∧
    ∀ p : ℕ, p.Prime → p ≠ 2 → heckeT k 1 1 p c = μ p • c

/-- **$S^+_{k+1/2}(4)$ has a basis of eigenforms** (Kohnen 1980 `kohnen1980`, §1 [unverified]: the $T(p^2)$, $p$ odd,
preserve the plus space, commute and are hermitian for the Petersson product): there are finitely many linearly
independent eigenforms spanning the plus space. -/
@[kb "kohnen1980" "§1: S⁺_{k+1/2}(4) has a basis of simultaneous eigenforms of the T(p²), p odd [unverified]"]
structure KohnenPlusEigenbasis (M : MultiplierSystem) (k : ℕ) : Prop where
  basis : 1 ≤ k → ∃ (r : ℕ) (g : Fin r → ℍ → ℂ) (μ : Fin r → ℕ → ℂ),
    (∀ i, IsPlusEigenform M k (g i) (μ i)) ∧ LinearIndependent ℂ g ∧
      M.plusCuspForms k 1 1 ≤ Submodule.span ℂ (Set.range g)

/-- **Multiplicity one in the plus space** (Kohnen 1980 `kohnen1980`, Thm. 1 and its corollary [unverified]): two
eigenforms with the same eigenvalues $\mu(p)$ at all odd primes are proportional. -/
@[kb "kohnen1980" "multiplicity one: eigenforms in S⁺_{k+1/2}(4) with equal T(p²)-eigenvalues, p odd, are proportional [unverified]"]
structure KohnenPlusMultOne (M : MultiplierSystem) (k : ℕ) : Prop where
  mult_one : 1 ≤ k → ∀ (g g' : ℍ → ℂ) (μ : ℕ → ℂ), IsPlusEigenform M k g μ → IsPlusEigenform M k g' μ → g ≠ 0 →
    ∃ t : ℂ, g' = t • g

/-- **A nonzero eigenform has a nonzero fundamental coefficient** (Kohnen–Zagier 1981 `kohnenzagier1981`, §II, the
coefficient formula $c(|D|m^2) = c(|D|)\sum_{d\mid m}\mu(d)\left(\frac Dd\right)d^{k-1}a(m/d)$ [unverified]): if
$g \ne 0$ is an eigenform with coefficients $c$, then $c(|D|) \ne 0$ for some fundamental $D$ with $(-1)^kD > 0$. -/
@[kb "kohnenzagier1981" "§II: a nonzero eigenform in S⁺_{k+1/2}(4) has c(|D|) ≠ 0 for some fundamental D, (-1)^k D > 0 [unverified]"]
structure KohnenPlusNonvanishing (M : MultiplierSystem) (k : ℕ) : Prop where
  nonvanishing : 1 ≤ k → ∀ (g : ℍ → ℂ) (μ : ℕ → ℂ), IsPlusEigenform M k g μ → g ≠ 0 →
    ∀ c : ℕ → ℂ, Abstract.HasQExp g c → ∃ D : ℤ, KohnenDisc k D ∧ c D.natAbs ≠ 0

namespace Abstract

theorem hasQExp_sum {ι : Type*} (s : Finset ι) (x : ι → ℂ) {g : ι → ℍ → ℂ} {c : ι → ℕ → ℂ}
    (h : ∀ i ∈ s, HasQExp (g i) (c i)) : HasQExp (∑ i ∈ s, x i • g i) (∑ i ∈ s, x i • c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasQExp_zero
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact hasQExp_add (hasQExp_smul _ (h j (Finset.mem_insert_self j s)))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

end Abstract

/-- The first coefficient of the $D$-th lift is $a(|D|)$. -/
theorem kohnenLiftCoeff_one (k : ℕ) (D : ℤ) (a : ℕ → ℂ) : kohnenLiftCoeff k D a 1 = a D.natAbs := by
  simp [kohnenLiftCoeff, kroneckerDisc_one]

variable (M : MultiplierSystem) (k : ℕ)

/-- **Injectivity of a combination of lifts from an eigenbasis, multiplicity one and nonvanishing** (Kohnen 1980
`kohnen1980`, proof of Thm. 1 [unverified]). -/
@[kb "kohnen1980" "proof of Thm. 1: a combination of D-th lifts is injective, by multiplicity one [unverified]"]
theorem kohnenLiftsInjective_of_eigen (hB : KohnenPlusEigenbasis M k) (h1 : KohnenPlusMultOne M k)
    (hN : KohnenPlusNonvanishing M k) : KohnenLiftsInjective M k := by
  classical
  refine ⟨fun hk ↦ ?_⟩
  obtain ⟨r, g, μ, hg, hli, hspan⟩ := hB.basis hk
  choose c hc heig using fun i ↦ (hg i).2
  have hne : ∀ i, g i ≠ 0 := hli.ne_zero
  choose D hD hcD using fun i ↦ hN.nonvanishing hk (g i) (μ i) (hg i) (hne i) (c i) (hc i)
  -- distinct eigenvalue systems, by multiplicity one
  have hsep : ∀ i j, i ≠ j → ∃ p, p.Prime ∧ p ≠ 2 ∧ μ i p ≠ μ j p := by
    intro i j hij
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hj' : IsPlusEigenform M k (g j) (μ i) :=
      ⟨(hg j).1, c j, hc j, fun p hp hp2 ↦ by rw [heig j p hp hp2, hcon p hp hp2]⟩
    obtain ⟨t, ht⟩ := h1.mult_one hk (g i) (g j) (μ i) (hg i) hj' (hne i)
    have hinj : Function.Injective ![i, j] := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
    have h2 := hli.comp ![i, j] hinj
    have e : g ∘ ![i, j] = ![g i, g j] := by
      funext x; fin_cases x <;> rfl
    rw [e, LinearIndependent.pair_iff' (hne i)] at h2
    exact h2 t ht.symm
  -- the combination of lifts
  let sD : Finset ℤ := Finset.univ.image D
  let ℓ : Fin r → Module.Dual ℂ (ℤ → ℂ) := fun i ↦ ∑ E ∈ sD, c i E.natAbs • LinearMap.proj E
  have hℓ : ∀ i (w : ℤ → ℂ), ℓ i w = ∑ E ∈ sD, w E * c i E.natAbs := by
    intro i w
    simp [ℓ, mul_comm]
  obtain ⟨w, hw⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists ℓ fun i ↦ by
    refine ⟨Pi.single (D i) 1, ?_⟩
    rw [hℓ]
    have hmem : D i ∈ sD := Finset.mem_image_of_mem D (Finset.mem_univ i)
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', hmem, ↓reduceIte]
    exact hcD i
  have hsD : ∀ E ∈ sD, KohnenDisc k E := by
    intro E hE
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hE
    exact hD i
  refine ⟨sD, w, hsD, ?_⟩
  intro f hf a ha hzero
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan hf)
  have hsumq := Abstract.hasQExp_sum Finset.univ x (g := g) (c := c) fun i _ ↦ hc i
  rw [hx] at hsumq
  have ha' : a = ∑ i, x i • c i := Abstract.hasQExp_unique ha hsumq
  let Λ : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) := ∑ E ∈ sD, w E • kohnenLiftLin k E
  have hΛ : ∀ b n, Λ b n = ∑ E ∈ sD, w E * kohnenLiftCoeff k E b n := by
    intro b n
    simp [Λ, Finset.sum_apply]
  have hΛa : Λ a = 0 := funext fun n ↦ by rw [hΛ]; exact hzero n
  let v : Fin r → ℕ → ℂ := fun i ↦ Λ (c i)
  have hvne : ∀ i, v i ≠ 0 := by
    intro i h
    apply hw i
    rw [hℓ]
    have h' := congrFun h 1
    simp only [v, hΛ, kohnenLiftCoeff_one, Pi.zero_apply] at h'
    exact h'
  have hcomm : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ b,
      heckeTIntLin (2 * k) 1 1 p (Λ b) = Λ (heckeT k 1 1 p b) := by
    intro p hp hp2 b
    simp only [Λ, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    refine Finset.sum_congr rfl fun E hE ↦ ?_
    rw [heckeTIntLin_apply, kohnenLiftLin_apply, kohnenLiftLin_apply,
      kohnenLiftCoeff_heckeT_of_fundamental k (hsD E hE).1 (hsD E hE).2 hp hp2]
  have hT : ∀ i (p : {p : ℕ // p.Prime ∧ p ≠ 2}),
      heckeTIntLin (2 * k) 1 1 p.1 (v i) = μ i p.1 • v i := by
    intro i p
    simp only [v]
    rw [hcomm p.1 p.2.1 p.2.2, heig i p.1 p.2.1 p.2.2, map_smul]
  have hli' := linearIndependent_of_jointEigen (fun p : {p : ℕ // p.Prime ∧ p ≠ 2} ↦ heckeTIntLin (2 * k) 1 1 p.1)
    (fun i p ↦ μ i p.1) v hvne hT fun i j hij ↦ by
      obtain ⟨p, hp, hp2, hne⟩ := hsep i j hij
      exact ⟨⟨p, hp, hp2⟩, hne⟩
  have hrel : ∑ i, x i • v i = 0 := by
    rw [← hΛa, ha', map_sum]
    simp [v, map_smul]
  have hx0 := Fintype.linearIndependent_iff.1 hli' x hrel
  rw [← hx]
  simp [hx0]

/-- **Kohnen's isomorphism from the lifts, one dimension inequality, and the eigenform statements:** the $D$-th lifts
land in $S_{2k}(1)$, $\dim S_{2k}(1) \le \dim S^+_{k+1/2}(4)$, the plus space has a basis of eigenforms, multiplicity
one holds, and nonzero eigenforms have a nonzero fundamental coefficient. -/
@[kb "kohnen1980" "Thm. 1 from the D-th lifts, dim S_{2k}(1) ≤ dim S⁺, an eigenbasis, multiplicity one and nonvanishing [unverified]"]
theorem kohnenIsomorphism_of_eigen (hL : ∀ D, KohnenDisc k D → KohnenDLift M k D) (hdim : KohnenDimensionLe M k)
    (hB : KohnenPlusEigenbasis M k) (h1 : KohnenPlusMultOne M k) (hN : KohnenPlusNonvanishing M k) :
    KohnenIsomorphism M k :=
  kohnenIsomorphism_of_dimLe M k hL hdim (kohnenLiftsInjective_of_eigen M k hB h1 hN)

end ModularFormsKB.HalfIntegral
