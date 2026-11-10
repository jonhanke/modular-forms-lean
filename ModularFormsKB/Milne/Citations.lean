import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Basic
import ModularFormsKB.Citation
/-!
# Milne, Chapters 0–3: items already in Mathlib

Milne, *Modular Functions and Modular Forms* (`milne2017mf`). Short restatements, in the book's form, of the numbered
items of Chapters 0–3 that Mathlib proves, each tagged with the book's locator. Items whose Mathlib form is the book's
are cited by docstring pointers only:

* Definition 0.2 (modular forms of level `N` and weight `2k`): Mathlib's `ModularForm` for
  `CongruenceSubgroup.Gamma N` and weight `2k`, see `modularFormLevelWeight`.
* Lemma 3.7 in the model case: `ZLattice.summable_norm_rpow`; the general form is
  `ModularFormsKB.Milne.tendstoUniformlyOn_lattice_sum`.
* Proposition 3.10: `EisensteinSeries.eisensteinSeries_tendstoLocallyUniformly`,
  `EisensteinSeries.eisensteinSeriesSIF_mdifferentiable` (Mathlib's weight index is the book's `2k`).
* Proposition 3.11 (second part): `PeriodPair.derivWeierstrassP_sq`, `℘'² = 4℘³ - g₂℘ - g₃` with `g₂ = 60 G₄`,
  `g₃ = 140 G₆` in Mathlib's indexing (the book's `60 G₂`, `140 G₃`).
* Definitions in running text: the full modular group (D004, `SL(2, ℤ)` acting on `UpperHalfPlane`), `Γ(N)` (D005,
  `CongruenceSubgroup.Gamma`), complex structures and Riemann surfaces (D019, `ChartedSpace ℂ X` with
  `IsManifold 𝓘(ℂ) 1 X`), holomorphic functions (D020, `MDifferentiableOn`), ringed spaces (D025,
  `AlgebraicGeometry.SheafedSpace`; the book's concrete form is `ModularFormsKB.Milne.RiemannSurface.SheafOfFunctions`),
  properly discontinuous actions (D040, `ProperlyDiscontinuousSMul`), congruence subgroups (D042,
  `CongruenceSubgroup.IsCongruenceSubgroup`), linear fractional transformations (D044, `OnePoint.instGLAction`),
  parabolic, elliptic and hyperbolic elements (D045, D046, `Matrix.IsParabolic`, `Matrix.IsElliptic`,
  `Matrix.IsHyperbolic`), cusps (D048, `IsCusp`), lattices (D057, `PeriodPair.lattice`).
-/

open Matrix MatrixGroups UpperHalfPlane Topology Filter

namespace ModularFormsKB.Milne

/-- **Milne, Definition 0.2.** Modular forms of level `N` and weight `2k`: Mathlib's `ModularForm` for `Γ(N)` and
weight `2k` (holomorphic on `ℍ`, `f(αz) = (cz + d)^{2k} f(z)` for `α ∈ Γ(N)`, bounded at the cusps). -/
@[kb "milne2017mf" "Definition 0.2, pdf p. 7"]
abbrev modularFormLevelWeight (N : ℕ) (k : ℤ) :=
  ModularForm ((CongruenceSubgroup.Gamma N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) (2 * k)

/-- **Milne, Proposition 2.1 (a).** `SL₂(ℝ)` acts transitively on `ℍ`. Mathlib: `UpperHalfPlane.isPretransitiveSL2R`. -/
@[kb "milne2017mf" "Proposition 2.1 (a), pdf p. 25"]
theorem exists_SL2R_smul_eq (z w : ℍ) : ∃ g : SL(2, ℝ), g • z = w :=
  MulAction.exists_smul_eq SL(2, ℝ) z w

/-- **Milne, Proposition 2.5.** Let `Γ` be a discrete subgroup of `SL₂(ℝ)`. (a) For every `x ∈ ℍ` the stabilizer of
`x` in `Γ` is finite. (b) Every `x` has a neighbourhood `U` such that `γU ∩ U ≠ ∅` implies `γx = x`. (c) If `x, y` are
not in the same orbit, they have neighbourhoods `U ∋ x` and `V ∋ y` with `γU ∩ V = ∅` for all `γ ∈ Γ` (this is the
Hausdorff property of `Γ\ℍ`, Corollary 2.6). Mathlib: `ProperlyDiscontinuousSMul.finite_stabilizer`,
`ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self`, `UpperHalfPlane.instProperlyDiscontinuousSL2RSubgroup`. -/
@[kb "milne2017mf" "Proposition 2.5, pdf p. 27"]
theorem discrete_subgroup_action_properties (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ] (x : ℍ) :
    (MulAction.stabilizer Γ x : Set Γ).Finite ∧
      ∃ U ∈ 𝓝 x, ∀ γ : Γ, ((γ • ·) '' U ∩ U).Nonempty → γ • x = x :=
  ⟨ProperlyDiscontinuousSMul.finite_stabilizer x,
    ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self Γ x⟩

/-- **Milne, Corollary 2.6.** For a discrete subgroup `Γ` of `SL₂(ℝ)`, the quotient `Γ\ℍ` is Hausdorff. Mathlib:
`t2Space_of_properlyDiscontinuousSMul_of_t2Space`. -/
@[kb "milne2017mf" "Corollary 2.6, pdf p. 27"]
theorem t2Space_quotient_upperHalfPlane (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ] :
    T2Space (MulAction.orbitRel.Quotient Γ ℍ) :=
  inferInstance

/-- **Milne, Exercise 2.8 (a), (b).** Commensurability is an equivalence relation on the subgroups of `SL₂(ℝ)`, and a
subgroup commensurable with a discrete subgroup is discrete. Mathlib: `Commensurable.equivalence`,
`Subgroup.Commensurable.discreteTopology_iff`. -/
@[kb "milne2017mf" "Exercise 2.8 (a), (b), pdf p. 29"]
theorem commensurable_equivalence_and_discrete :
    Equivalence (@Subgroup.Commensurable SL(2, ℝ) _) ∧
      ∀ {Γ Γ' : Subgroup SL(2, ℝ)}, Subgroup.Commensurable Γ Γ' → (DiscreteTopology Γ ↔ DiscreteTopology Γ') :=
  ⟨Subgroup.Commensurable.equivalence, fun h ↦ h.discreteTopology_iff⟩

/-- **Milne, Remark 2.11** (cusps): the cusps of `SL₂(ℤ)` are the points of `ℚ ∪ {∞}`, and they are all
`SL₂(ℤ)`-equivalent to `∞`. Mathlib: `isCusp_SL2Z_iff`, `isCusp_SL2Z_iff'`. -/
@[kb "milne2017mf" "Remark 2.11: cusps of Gamma(1), pdf p. 31"]
theorem isCusp_SL2Z_iff_and_equiv_infty {c : OnePoint ℝ} :
    (IsCusp c 𝒮ℒ ↔ c ∈ Set.range (OnePoint.map ((↑) : ℚ → ℝ))) ∧
      (IsCusp c 𝒮ℒ ↔ ∃ g : SL(2, ℤ), c = SpecialLinearGroup.mapGL ℝ g • (OnePoint.infty : OnePoint ℝ)) :=
  ⟨isCusp_SL2Z_iff, isCusp_SL2Z_iff'⟩

/-- **Milne, Theorem 2.12.** Let `D` be the region `|z| > 1`, `|Re z| < 1/2`. Every point of `ℍ` is equivalent under
`Γ(1)` to a point of the closure `D̄`; if `z ∈ D` and `γz ∈ D̄` then `γ = ±I`; and `Γ(1)` is generated by `S` and
`T`. Mathlib: `ModularGroup.exists_smul_mem_fd`, `ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd`,
`SpecialLinearGroup.SL2Z_generators`. -/
@[kb "milne2017mf" "Theorem 2.12, pdf p. 32"]
theorem fundamentalDomain_SL2Z :
    (∀ z : ℍ, ∃ g : SL(2, ℤ), g • z ∈ ModularGroup.fd) ∧
      (∀ (z : ℍ) (g : SL(2, ℤ)), z ∈ ModularGroup.fdo → g • z ∈ ModularGroup.fd → g = 1 ∨ g = -1) ∧
      Subgroup.closure {ModularGroup.S, ModularGroup.T} = ⊤ :=
  ⟨ModularGroup.exists_smul_mem_fd, fun _ _ hz hg ↦ ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hz hg,
    SpecialLinearGroup.SL2Z_generators⟩

end ModularFormsKB.Milne
