import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import TauCeti.NumberTheory.ModularForms.FiniteDimensional
import TauCeti.NumberTheory.ModularForms.LevelOne.ValenceFormula
import TauCeti.NumberTheory.ModularForms.LevelOne.GradedRing
import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Finite
import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
import ModularFormsKB.Milne.Ch4.Differentials
import ModularFormsKB.Milne.Ch4.ModularFunction
import ModularFormsKB.Citation
/-!
# Milne, Chapter 4: dimension of the space of modular forms, zeros of modular forms, $\Gamma(1)$

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 4, pdf pp. 51–55.

For a subgroup $\Gamma$ of finite index in $\mathrm{SL}_2(\mathbb Z)$, $\bar\Gamma$ is its image in
$\mathrm{PSL}_2(\mathbb R)$ (`Γ.map sl2zToPSL2R`) and $X(\Gamma) = \Gamma\backslash\mathbb H^*$ is Tau Ceti's compact
Riemann surface `(Γ.map sl2zToPSL2R).CompactifiedQuotient` (`modularCurve`). Its genus is `genus` (holomorphic
differentials), $\epsilon_\infty$ is the number of cusp orbits, and for $z \in \mathbb H$, $e_z$ is the order of the
stabilizer of $z$ in $\bar\Gamma$ (`stabOrder`).

Milne's weight $2k$ is Mathlib's weight `2 * k`.

## Items
- Theorem 4.9: $k < 0$ and $k = 0$ proved (`finrank_neg`, `finrank_zero`); $k \ge 1$ is the named statement
  `DimensionFormula` (Riemann–Roch on $X(\Gamma)$ is not available).
- Lemma 4.11: named statement `ModularFormDifferential`.
- Proposition 4.12: named statement `ValenceFormula`.
- Example 4.13: the holomorphic case is Tau Ceti's `TauCeti.ModularForm.valence_formula` (`valence_formula_one`);
  the meromorphic case is `ValenceFormula ⊤`.
- Example 4.14 (`finrank_one`, `finrank_one_mod_six`).
- Example 4.15 (`G_two_eq_zero_iff`, `order_G_two_rho`, `G_three_eq_zero_iff`, `order_G_three_I`, `disc_ne_zero`,
  `cuspOrder_disc`).
- Proposition 4.16 (`GForm`, `finrank_GForm_basis`, `mvPolynomialEquiv_G`); parts (a), (c) are Mathlib's
  `ModularForm.levelOne_neg_weight_rank_zero`, `ModularForm.levelOne_weight_two_rank_zero`,
  `CuspForm.discriminantEquiv`.
-/

open UpperHalfPlane Complex Filter Topology ModularForm MulAction
open scoped MatrixGroups Manifold Real ContDiff

noncomputable section

namespace ModularFormsKB.Milne

/-- The modular curve $X(\Gamma) = \Gamma\backslash\mathbb H^*$ as a compact Riemann surface (Tau Ceti). -/
abbrev modularCurve (Γ : Subgroup SL(2, ℤ)) : Type :=
  (Γ.map sl2zToPSL2R).CompactifiedQuotient

/-- The quotient map $p : \mathbb H \to X(\Gamma)$. -/
def modularCurve.proj (Γ : Subgroup SL(2, ℤ)) (z : ℍ) : modularCurve Γ :=
  Subgroup.CompactifiedQuotient.ofQuotient (Quotient.mk _ z)

/-- $e_z$: the order of the stabilizer of $z \in \mathbb H$ in $\bar\Gamma \subseteq \mathrm{PSL}_2(\mathbb R)$ (the
ramification index of $\mathbb H \to \Gamma\backslash\mathbb H$ at $z$; $e_z = 1$ except at elliptic points). -/
def stabOrder (Γ : Subgroup SL(2, ℤ)) (z : ℍ) : ℕ := Nat.card (stabilizer (Γ.map sl2zToPSL2R) z)

/-- $\epsilon_\infty$: the number of inequivalent cusps of $\Gamma$. -/
def cuspCount (Γ : Subgroup SL(2, ℤ)) : ℕ := Nat.card (CuspOrbits (Γ : Subgroup (GL (Fin 2) ℝ)))

/-- A representative $\gamma \in \mathrm{SL}_2(\mathbb Z)$ of a cusp orbit $c$: $\gamma(i\infty) \in c$. -/
def cuspRep (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (c : CuspOrbits (Γ : Subgroup (GL (Fin 2) ℝ))) : SL(2, ℤ) :=
  ((surjective_cosetToCuspOrbit (Γ : Subgroup (GL (Fin 2) ℝ)) c).choose.out)⁻¹

/-- The elliptic term $\sum_P \lfloor k(1 - 1/e_P)\rfloor$ of Theorem 4.9, over representatives $P$ of the elliptic
orbits of $\bar\Gamma$ on $\mathbb H$. -/
def ellipticTerm (Γ : Subgroup SL(2, ℤ)) (k : ℕ) : ℤ :=
  ∑ᶠ P ∈ (Γ.map sl2zToPSL2R).ellipticOrbits, ⌊(k : ℚ) * (1 - 1 / (stabOrder Γ P.out : ℚ))⌋

/-- **Theorem 4.9**, $k < 0$: $\dim M_k(\Gamma) = 0$. -/
@[kb "milne2017mf" "Section 4, Theorem 4.9 (pdf p. 51)"]
theorem finrank_neg (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {k : ℤ} (hk : k < 0) :
    Module.finrank ℂ (ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * k)) = 0 := by
  have := ModularForm.subsingleton_of_neg_weight (𝒢 := (Γ : Subgroup (GL (Fin 2) ℝ))) (k := 2 * k) (by omega)
  exact Module.finrank_zero_of_subsingleton

/-- **Theorem 4.9**, $k = 0$: $\dim M_0(\Gamma) = 1$. -/
@[kb "milne2017mf" "Section 4, Theorem 4.9 (pdf p. 51)"]
theorem finrank_zero (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    Module.finrank ℂ (ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0) = 1 :=
  ModularForm.finrank_weight_zero (𝒢 := (Γ : Subgroup (GL (Fin 2) ℝ)))

/-- **Theorem 4.9**, $k \ge 1$ (named statement): $\dim M_k(\Gamma) = (2k-1)(g-1) + \epsilon_\infty k +
\sum_P \lfloor k(1 - 1/e_P)\rfloor$, with $g$ the genus of $X(\Gamma)$. Milne proves it by Riemann–Roch on $X(\Gamma)$
(Theorem 1.22) together with Lemma 4.11; neither is available here. -/
@[kb "milne2017mf" "Section 4, Theorem 4.9 (pdf p. 51)"]
structure DimensionFormula (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : Prop where
  formula : ∀ k : ℕ, 1 ≤ k →
    (Module.finrank ℂ (ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * k : ℕ)) : ℤ) =
      (2 * k - 1) * ((genus (modularCurve Γ) : ℤ) - 1) + cuspCount Γ * k + ellipticTerm Γ k

/-- **Lemma 4.11** (named statement): to a meromorphic modular form $f$ of weight $2k$ for $\Gamma$ corresponds a
meromorphic $k$-fold differential $\omega$ on $X(\Gamma)$, whose pullback to $\mathbb H$ is $f(z)(dz)^k$ (Remark 4.8),
and for $Q \in \mathbb H$ over $P \in X(\Gamma)$:
(a) $\mathrm{ord}_Q(f) = e\,\mathrm{ord}_P(\omega) + k(e - 1)$ with $e = e_Q$ (this contains (c), the case $e = 1$);
(b) at a cusp $Q$, $\mathrm{ord}_Q(f) = \mathrm{ord}_P(\omega) + k$. -/
@[kb "milne2017mf" "Section 4, Lemma 4.11 (pdf p. 52)"]
structure ModularFormDifferential (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : Prop where
  exists_diff : ∀ (k : ℕ) (f : ℍ → ℂ), IsMeromorphicModularForm Γ k f →
    ∃ D : KDifferential (modularCurve Γ) k,
      (∀ z : ℍ, (f ∘ ofComplex) =ᶠ[𝓝[≠] (z : ℂ)] fun w ↦
        D.coeff (modularCurve.proj Γ z) (chartAt ℂ (modularCurve.proj Γ z) (modularCurve.proj Γ (ofComplex w))) *
          deriv (chartAt ℂ (modularCurve.proj Γ z) ∘ modularCurve.proj Γ ∘ ofComplex) w ^ k) ∧
      (∀ z : ℍ, ∀ m : ℤ, D.order (modularCurve.proj Γ z) = m →
        meromorphicOrderAt (f ∘ ofComplex) (z : ℂ) = ((stabOrder Γ z * m + k * (stabOrder Γ z - 1 : ℕ) : ℤ))) ∧
      (∀ (C : (Γ.map sl2zToPSL2R).CuspOrbit) (γ : SL(2, ℤ)),
        (C : (Γ.map sl2zToPSL2R).BoundaryOrbit) = Quotient.mk'' (sl2zToPSL2R γ • (OnePoint.infty : OnePoint ℝ)) →
        ∀ m : ℤ, D.order (Subgroup.CompactifiedQuotient.ofCusp C) = m → cuspOrder Γ k f γ = ((m + k : ℤ)))

/-- The left side of Proposition 4.12: $\sum_Q (\mathrm{ord}_Q(f)/e_Q - k(1 - 1/e_Q))$ over representatives $Q$ of
the points of $\Gamma\backslash\mathbb H^*$ ($e_Q = 1$ at cusps). Orders are `WithTop ℤ`; for $f \ne 0$ they are
finite, and `WithTop.untopD 0` reads them in $\mathbb Z$. -/
def valenceSum (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) (f : ℍ → ℂ) : ℚ :=
  (∑ᶠ p : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ,
      ((((meromorphicOrderAt (f ∘ ofComplex) (p.out : ℂ)).untopD 0 : ℤ) : ℚ) / stabOrder Γ p.out -
        k * (1 - 1 / (stabOrder Γ p.out : ℚ)))) +
    ∑ᶠ c : CuspOrbits (Γ : Subgroup (GL (Fin 2) ℝ)), (((cuspOrder Γ k f (cuspRep Γ c)).untopD 0 : ℤ) : ℚ)

/-- **Proposition 4.12** (named statement, the valence formula): for a nonzero meromorphic modular form $f$ of weight
$2k$ for $\Gamma$, $\sum_Q(\mathrm{ord}_Q(f)/e_Q - k(1 - 1/e_Q)) = k(2g - 2) + k\epsilon_\infty$, the sum over
representatives of $\Gamma\backslash\mathbb H^*$. "Nonzero" is: $f$ does not vanish identically near some point. Milne
derives it from Lemma 4.11 and $\deg\operatorname{div}(\omega) = k(2g-2)$ (Corollary 1.21). For holomorphic $f$ the
interior and cusp terms are those of Tau Ceti's `TauCeti.ModularForm.valence_formula_finiteIndex`, whose right side is
$k[\Gamma(1):\Gamma]/6$; the two agree by the genus formula. -/
@[kb "milne2017mf" "Section 4, Proposition 4.12 (pdf p. 53)"]
structure ValenceFormula (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : Prop where
  formula : ∀ (k : ℤ) (f : ℍ → ℂ), IsMeromorphicModularForm Γ k f →
    (∃ z : ℍ, ¬ (f ∘ ofComplex) =ᶠ[𝓝[≠] (z : ℂ)] 0) →
    valenceSum Γ k f = k * (2 * (genus (modularCurve Γ) : ℚ) - 2) + k * cuspCount Γ

/-- **Example 4.13**, holomorphic forms (Tau Ceti): for a nonzero modular form $f$ of weight $2k$ for $\Gamma(1)$,
$\mathrm{ord}_{i\infty}(f) + \frac12\mathrm{ord}_i(f) + \frac13\mathrm{ord}_\rho(f) + \sum_Q\mathrm{ord}_Q(f) = k/6$. -/
@[kb "milne2017mf" "Section 4, Example 4.13 (pdf p. 54)"]
theorem valence_formula_one {k : ℕ} (f : ModularForm 𝒮ℒ (2 * k : ℕ)) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    ((∑ᶠ q : TauCeti.ModularForm.NonEllipticOrbit, TauCeti.ModularForm.orderOfVanishingOnOrbit f q.val : ℤ) : ℂ)
      + 1 / 2 * ((TauCeti.orderOfVanishingAt ⇑f UpperHalfPlane.I : ℤ) : ℂ)
      + 1 / 3 * ((TauCeti.orderOfVanishingAt ⇑f UpperHalfPlane.ρ : ℤ) : ℂ)
      + TauCeti.qExpansionOrderAtCusp 1 ⇑f = (k : ℂ) / 6 := by
  have h := TauCeti.ModularForm.valence_formula f hf
  rw [h]
  push_cast
  ring

/-- Helper: the level-one dimension formula in Milne's indexing, from Mathlib's `dimension_level_one`. -/
theorem finrank_levelOne_aux (k : ℕ) :
    Module.finrank ℂ (ModularForm 𝒮ℒ (2 * k : ℕ)) = if k % 6 = 1 then k / 6 else k / 6 + 1 := by
  have h := dimension_level_one (2 * k) (even_two_mul k)
  rw [← Module.finrank_eq_rank] at h
  have h' := Nat.cast_injective h
  rw [h']
  clear h h'
  by_cases h1 : k % 6 = 1
  · have h2 : 2 * k ≡ 2 [MOD 12] := by unfold Nat.ModEq; omega
    simp only [h1, h2, ite_true]; omega
  · have h2 : ¬ 2 * k ≡ 2 [MOD 12] := by unfold Nat.ModEq; omega
    simp only [h1, h2, ite_false]; omega

/-- **Example 4.14**: for $\Gamma(1)$ and $k > 1$, $\dim M_k = 1 - k + \lfloor k/2\rfloor + \lfloor 2k/3\rfloor$. -/
@[kb "milne2017mf" "Section 4, Example 4.14 (pdf p. 54)"]
theorem finrank_one {k : ℕ} (_hk : 1 < k) :
    (Module.finrank ℂ (ModularForm 𝒮ℒ (2 * k : ℕ)) : ℤ) = 1 - k + k / 2 + 2 * k / 3 := by
  rw [finrank_levelOne_aux k]
  split_ifs <;> omega

/-- **Example 4.14 (b)**: for $\Gamma(1)$ and $k \ge 0$, $\dim M_k = \lfloor k/6\rfloor$ if $k \equiv 1 \pmod 6$ and
$\lfloor k/6\rfloor + 1$ otherwise. -/
@[kb "milne2017mf" "Section 4, Example 4.14 (pdf p. 54)"]
theorem finrank_one_mod_six (k : ℕ) :
    Module.finrank ℂ (ModularForm 𝒮ℒ (2 * k : ℕ)) = if k % 6 = 1 then k / 6 else k / 6 + 1 := by
  exact finrank_levelOne_aux k

/-- Helper: a nonzero constant multiple does not change the analytic order. -/
theorem analyticOrderAt_const_mul {f : ℂ → ℂ} {z c : ℂ} (hc : c ≠ 0) (hf : AnalyticAt ℂ f z) :
    analyticOrderAt (fun w ↦ c * f w) z = analyticOrderAt f z := by
  change analyticOrderAt ((fun _ ↦ c) * f) z = _
  rw [analyticOrderAt_mul analyticAt_const hf, analyticAt_const.analyticOrderAt_eq_zero.mpr hc,
    zero_add]

/-- Helper: $\pi^4/45 \ne 0$. -/
theorem pi_pow_div_ne_zero : (π : ℂ) ^ 4 / 45 ≠ 0 :=
  div_ne_zero (pow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)) (by norm_num)

/-- **Example 4.15**: $G_2$ vanishes exactly on the $\Gamma(1)$-orbit of $\rho = e^{2\pi i/3}$. -/
@[kb "milne2017mf" "Section 4, Example 4.15 (pdf p. 54)"]
theorem G_two_eq_zero_iff (z : ℍ) : G 2 z = 0 ↔ ∃ γ : SL(2, ℤ), γ • UpperHalfPlane.ρ = z := by
  rw [G_two, mul_eq_zero, or_iff_right pi_pow_div_ne_zero, ← TauCeti.ModularForm.j_eq_zero_iff]
  constructor
  · intro h
    have h1 : jFun z = jFun UpperHalfPlane.ρ := by rw [jFun_eq, h, TauCeti.ModularForm.j_ρ]
    obtain ⟨γ, hγ⟩ := jFun_bijective.2 z _ h1
    exact ⟨γ, hγ⟩
  · rintro ⟨γ, rfl⟩
    have h1 := jFun_smul γ UpperHalfPlane.ρ
    rw [jFun_eq] at h1
    rw [h1, TauCeti.ModularForm.j_ρ]

/-- **Example 4.15**: the zero of $G_2$ at $\rho$ is simple. -/
@[kb "milne2017mf" "Section 4, Example 4.15 (pdf p. 54)"]
theorem order_G_two_rho : analyticOrderAt (G 2 ∘ ofComplex) (UpperHalfPlane.ρ : ℂ) = 1 := by
  have heq : G 2 ∘ ofComplex = fun w ↦ ((π : ℂ) ^ 4 / 45) * (E₄ ∘ ofComplex) w := by
    funext w
    simp [G_two]
  rw [heq, analyticOrderAt_const_mul pi_pow_div_ne_zero
    (TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex (ModularFormClass.holo E₄) UpperHalfPlane.ρ.im_pos)]
  exact TauCeti.ModularForm.analyticOrderAt_E₄_comp_ofComplex_ρ

/-- **Example 4.15**: $G_3$ vanishes exactly on the $\Gamma(1)$-orbit of $i$. -/
@[kb "milne2017mf" "Section 4, Example 4.15 (pdf p. 54)"]
theorem G_three_eq_zero_iff (z : ℍ) : G 3 z = 0 ↔ ∃ γ : SL(2, ℤ), γ • UpperHalfPlane.I = z := by
  have h6 : 2 * (π : ℂ) ^ 6 / 945 ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)))
      (by norm_num)
  rw [G_three, mul_eq_zero, or_iff_right h6]
  have hE : E₆ z = 0 ↔ TauCeti.ModularForm.j z = 1728 := (TauCeti.ModularForm.j_eq_1728_iff z).symm
  rw [hE]
  constructor
  · intro h
    have h1 : jFun z = jFun UpperHalfPlane.I := by rw [jFun_eq, h, TauCeti.ModularForm.j_I]
    obtain ⟨γ, hγ⟩ := jFun_bijective.2 z _ h1
    exact ⟨γ, hγ⟩
  · rintro ⟨γ, rfl⟩
    have h1 := jFun_smul γ UpperHalfPlane.I
    rw [jFun_eq] at h1
    rw [h1, TauCeti.ModularForm.j_I]

/-- **Example 4.15**: the zero of $G_3$ at $i$ is simple. -/
@[kb "milne2017mf" "Section 4, Example 4.15 (pdf p. 54)"]
theorem order_G_three_I : analyticOrderAt (G 3 ∘ ofComplex) Complex.I = 1 := by
  have h6 : 2 * (π : ℂ) ^ 6 / 945 ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)))
      (by norm_num)
  have heq : G 3 ∘ ofComplex = fun w ↦ (2 * (π : ℂ) ^ 6 / 945) * (E₆ ∘ ofComplex) w := by
    funext w
    simp [G_three]
  rw [heq, ← UpperHalfPlane.coe_I, analyticOrderAt_const_mul h6
    (TauCeti.UpperHalfPlane.analyticAt_comp_ofComplex (ModularFormClass.holo E₆) UpperHalfPlane.I.im_pos)]
  rw [UpperHalfPlane.coe_I]
  exact TauCeti.ModularForm.analyticOrderAt_E₆_comp_ofComplex_I

/-- **Example 4.15**: $\Delta$ has no zeros in $\mathbb H$. -/
@[kb "milne2017mf" "Section 4, Example 4.15 (pdf p. 54)"]
theorem disc_ne_zero (z : ℍ) : disc z ≠ 0 := by
  rw [disc_eq]
  exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)))
    (ModularForm.discriminant_ne_zero z)

/-- **Example 4.15**: $\Delta$ has a simple zero at $i\infty$. -/
@[kb "milne2017mf" "Section 4, Example 4.15 (pdf p. 54)"]
theorem cuspOrder_disc : cuspOrder ⊤ 6 disc 1 = 1 := by
  unfold cuspOrder
  rw [cuspWidth_top, show (2 * 6 : ℤ) = 12 from rfl, SlashAction.slash_one]
  have heq : Function.Periodic.cuspFunction 1 (disc ∘ ofComplex) =ᶠ[𝓝[≠] 0]
      (fun _ : ℂ ↦ (2 * π : ℂ) ^ 12) • UpperHalfPlane.cuspFunction 1 ModularForm.discriminant := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    rw [Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq]
    show _ = (2 * π : ℂ) ^ 12 * UpperHalfPlane.cuspFunction 1 ModularForm.discriminant q
    rw [UpperHalfPlane.cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq]
    simp [disc_eq]
  have han : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ModularForm.discriminant) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant one_pos one_mem_strictPeriods_SL
  rw [meromorphicOrderAt_congr heq,
    meromorphicOrderAt_smul_of_ne_zero (analyticAt_const) (by simp),
    han.meromorphicOrderAt_eq, ← TauCeti.qExpansion_order_eq_analyticOrderAt_cuspFunction han,
    ModularForm.discriminant_qExpansion_order]
  rfl

/-- Milne's $G_k$ ($k \ge 2$) as an element of $M_k(\Gamma(1))$: $2\zeta(2k)E_{2k}$. -/
def GForm (k : ℕ) (hk : 3 ≤ 2 * k) : ModularForm 𝒮ℒ (2 * k : ℕ) := (2 * riemannZeta (2 * k : ℕ)) • E hk

theorem coe_GForm (k : ℕ) (hk : 3 ≤ 2 * k) : ⇑(GForm k hk) = G k := by
  funext z
  rw [G_eq hk z]
  rfl

/-- Helper: $2\zeta(2k) \ne 0$ for $k \ge 1$. -/
theorem two_mul_zeta_ne_zero (k : ℕ) (hk : 3 ≤ 2 * k) : (2 * riemannZeta (2 * k : ℕ)) ≠ 0 := by
  refine mul_ne_zero two_ne_zero (riemannZeta_ne_zero_of_one_lt_re ?_)
  rw [Complex.natCast_re]
  exact_mod_cast (by omega : 1 < 2 * k)

/-- **Proposition 4.16 (b)**: for $k = 2, 3, 4, 5$, $M_k$ is one-dimensional with basis $G_k$; and
$S_k(\Gamma(1)) = 0$ for $0 \le k \le 5$. -/
@[kb "milne2017mf" "Section 4, Proposition 4.16 (b) (pdf p. 54)"]
theorem finrank_GForm_basis (k : ℕ) (hk : 3 ≤ 2 * k) (hk5 : k ≤ 5) :
    (Module.finrank ℂ (ModularForm 𝒮ℒ (2 * k : ℕ)) = 1 ∧ GForm k hk ≠ 0) ∧
      Module.finrank ℂ (CuspForm 𝒮ℒ (2 * k : ℕ)) = 0 := by
  have hk1 : ¬ k % 6 = 1 := by omega
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [finrank_levelOne_aux]
    simp only [hk1, ↓reduceIte]
    omega
  · intro h
    exact EisensteinSeries.E_ne_zero hk (even_two_mul k) ((smul_eq_zero.mp h).resolve_left (two_mul_zeta_ne_zero k hk))
  · exact Module.finrank_eq_zero_of_rank_eq_zero
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (k := ((2 * k : ℕ) : ℤ)) (by omega))

/-- **Proposition 4.16 (d)**: $\bigoplus_k M_k = \mathbb C[G_2, G_3]$, with $G_2$, $G_3$ algebraically independent:
the $\mathbb C$-algebra map $\mathbb C[X_0, X_1] \to \bigoplus_k M_k$, $X_0 \mapsto G_2$, $X_1 \mapsto G_3$, is
bijective (generation is Mathlib's `ModularForm.evalE₄E₆_surjective`, independence Tau Ceti's
`TauCeti.ModularForm.evalE₄E₆_injective`). -/
@[kb "milne2017mf" "Section 4, Proposition 4.16 (d) (pdf p. 55)"]
theorem bijective_aeval_G :
    Function.Bijective (MvPolynomial.aeval (R := ℂ) ![DirectSum.of (ModularForm 𝒮ℒ) 4 (GForm 2 (by norm_num)),
      DirectSum.of (ModularForm 𝒮ℒ) 6 (GForm 3 (by norm_num))]) := by
  set c4 : ℂ := 2 * riemannZeta (2 * 2 : ℕ) with hc4
  set c6 : ℂ := 2 * riemannZeta (2 * 3 : ℕ) with hc6
  have h4 : c4 ≠ 0 := two_mul_zeta_ne_zero 2 (by norm_num)
  have h6 : c6 ≠ 0 := two_mul_zeta_ne_zero 3 (by norm_num)
  let φ : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
    MvPolynomial.aeval ![MvPolynomial.C c4 * MvPolynomial.X 0, MvPolynomial.C c6 * MvPolynomial.X 1]
  let ψ : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
    MvPolynomial.aeval ![MvPolynomial.C c4⁻¹ * MvPolynomial.X 0, MvPolynomial.C c6⁻¹ * MvPolynomial.X 1]
  have hψφ : ψ.comp φ = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [φ, ψ, ← mul_assoc, ← MvPolynomial.C_mul, h4]
    · simp [φ, ψ, ← mul_assoc, ← MvPolynomial.C_mul, h6]
  have hφψ : φ.comp ψ = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [φ, ψ, ← mul_assoc, ← MvPolynomial.C_mul, h4]
    · simp [φ, ψ, ← mul_assoc, ← MvPolynomial.C_mul, h6]
  have hφ : Function.Bijective φ :=
    ⟨Function.LeftInverse.injective (g := ψ) (fun x ↦ congrArg (fun f ↦ f x) hψφ),
      Function.RightInverse.surjective (g := ψ) (fun x ↦ congrArg (fun f ↦ f x) hφψ)⟩
  have hcomp : MvPolynomial.aeval (R := ℂ) ![DirectSum.of (ModularForm 𝒮ℒ) 4 (GForm 2 (by norm_num)),
      DirectSum.of (ModularForm 𝒮ℒ) 6 (GForm 3 (by norm_num))] = ModularForm.evalE₄E₆.comp φ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, MvPolynomial.aeval_X, AlgHom.comp_apply, φ,
        map_mul, ModularForm.evalE₄E₆_X_zero]
      rw [MvPolynomial.algHom_C, ← Algebra.smul_def, ← DirectSum.of_smul]
      rfl
    · show _ = ModularForm.evalE₄E₆ (φ (MvPolynomial.X 1))
      rw [show φ (MvPolynomial.X 1) = MvPolynomial.C c6 * MvPolynomial.X 1 from
        MvPolynomial.aeval_X _ 1, map_mul, ModularForm.evalE₄E₆_X_one, MvPolynomial.algHom_C,
        ← Algebra.smul_def, ← DirectSum.of_smul, MvPolynomial.aeval_X]
      rfl
  rw [hcomp]
  exact ⟨(TauCeti.ModularForm.evalE₄E₆_injective.comp hφ.1 : _),
    ModularForm.evalE₄E₆_surjective.comp hφ.2⟩

end ModularFormsKB.Milne
