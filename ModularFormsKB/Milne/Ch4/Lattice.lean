import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import ModularFormsKB.Citation
/-!
# Milne, Chapter 4: Lemma 4.6, functions on lattices and weakly modular forms

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 4, Lemma 4.6, pdf pp. 49–50.

A lattice in $\mathbb C$ is $\mathbb Z\omega_1 + \mathbb Z\omega_2$ with $\omega_1, \omega_2$ linearly independent over
$\mathbb R$ (`IsLattice`; the lattices of Mathlib's `PeriodPair`). For $z \in \mathbb H$, $\Lambda(z, 1) = \mathbb Z z +
\mathbb Z$ (`latticeOf`). A function $F$ on lattices has weight $2k$ if $F(\lambda\Lambda) = \lambda^{-2k}F(\Lambda)$ for
all $\lambda \in \mathbb C^\times$ (`IsWeight`). A weakly modular form of weight $2k$ (for $\Gamma(1)$) is a function on
$\mathbb H$ satisfying 4.5(a), i.e. Mathlib's `SlashInvariantForm 𝒮ℒ (2k)`.
-/

open UpperHalfPlane Complex
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne

/-- A lattice in $\mathbb C$: a subgroup $\mathbb Z\omega_1 + \mathbb Z\omega_2$ with $\omega_1, \omega_2$ linearly
independent over $\mathbb R$ (p. 49; Section 3). -/
@[kb "milne2017mf" "Section 4, the set L of lattices in C (pdf p. 49)"]
def IsLattice (Λ : Submodule ℤ ℂ) : Prop := ∃ L : PeriodPair, L.lattice = Λ

/-- The set $\mathcal L$ of lattices in $\mathbb C$. -/
abbrev Lattices : Type := {Λ : Submodule ℤ ℂ // IsLattice Λ}

/-- The homothety image of a lattice is a lattice. -/
theorem isLattice_map_smul (c : ℂˣ) {Λ : Submodule ℤ ℂ} (h : IsLattice Λ) :
    IsLattice (Λ.map ((c : ℂ) • LinearMap.id)) := by
  obtain ⟨L, rfl⟩ := h
  have hc : (c : ℂ) ≠ 0 := c.ne_zero
  refine ⟨⟨c * L.ω₁, c * L.ω₂, ?_⟩, ?_⟩
  · refine LinearIndependent.pair_iff.2 fun s t hst ↦ ?_
    refine LinearIndependent.pair_iff.1 L.indep s t ?_
    have h2 : (c : ℂ) * (s • L.ω₁ + t • L.ω₂) = 0 := by
      simp only [Complex.real_smul] at hst ⊢
      linear_combination hst
    simpa [hc] using h2
  · simp [PeriodPair.lattice, Submodule.map_span]

/-- The lattice $\lambda\Lambda$. -/
def Lattices.smul (c : ℂˣ) (Λ : Lattices) : Lattices :=
  ⟨Λ.1.map ((c : ℂ) • LinearMap.id), isLattice_map_smul c Λ.2⟩

/-- An integer combination `p z + q` with `z ∈ ℍ` vanishes only if `p = q = 0`. -/
theorem int_pair_eq_zero {z : ℍ} {p q : ℤ} (h : (p : ℂ) * z + q = 0) : p = 0 ∧ q = 0 := by
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
    add_zero, Complex.zero_im] at him
  have hp : (p : ℝ) = 0 := by
    rcases mul_eq_zero.1 him with h | h
    · exact h
    · exact absurd h z.im_pos.ne'
  have hp' : p = 0 := by exact_mod_cast hp
  subst hp'
  simp only [Int.cast_zero, zero_mul, zero_add] at h
  exact ⟨rfl, by exact_mod_cast h⟩

theorem isLattice_span (z : ℍ) : IsLattice (Submodule.span ℤ {(z : ℂ), 1}) := by
  refine ⟨⟨z, 1, ?_⟩, rfl⟩
  refine LinearIndependent.pair_iff.2 fun s t hst ↦ ?_
  simp only [Complex.real_smul, mul_one] at hst
  have him := congrArg Complex.im hst
  simp at him
  have hs : s = 0 := by
    rcases him with h | h
    · exact h
    · exact absurd h z.im_pos.ne'
  subst hs
  simp at hst
  exact ⟨rfl, hst⟩

/-- The lattice $\Lambda(z, 1) = \mathbb Z z + \mathbb Z$ for $z \in \mathbb H$. -/
def latticeOf (z : ℍ) : Lattices := ⟨Submodule.span ℤ {(z : ℂ), 1}, isLattice_span z⟩

/-- A function $F : \mathcal L \to \mathbb C$ **of weight $2k$**: $F(\lambda\Lambda) = \lambda^{-2k}F(\Lambda)$ for all
$\lambda \in \mathbb C^\times$. -/
@[kb "milne2017mf" "Section 4, Lemma 4.6, function of weight 2k on lattices (pdf p. 49)"]
def IsWeight (k : ℕ) (F : Lattices → ℂ) : Prop :=
  ∀ (c : ℂˣ) (Λ : Lattices), F (Λ.smul c) = (c : ℂ) ^ (-(2 * k : ℤ)) * F Λ

/-- The underlying module of `c • latticeOf z`. -/
theorem smul_latticeOf_eq (c : ℂˣ) (z : ℍ) :
    (Lattices.smul c (latticeOf z)).1 = Submodule.span ℤ {(c : ℂ) * z, (c : ℂ)} := by
  simp [Lattices.smul, latticeOf, Submodule.map_span]

theorem smul_one_lattice (Λ : Lattices) : Lattices.smul 1 Λ = Λ := by
  apply Subtype.ext
  ext x
  simp [Lattices.smul]

theorem smul_smul_lattice (c c' : ℂˣ) (Λ : Lattices) :
    Lattices.smul c' (Lattices.smul c Λ) = Lattices.smul (c' * c) Λ := by
  apply Subtype.ext
  ext x
  simp only [Lattices.smul, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply,
    smul_eq_mul, Units.val_mul]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by ring⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, by ring⟩

theorem span_neg_left (a b : ℂ) :
    Submodule.span ℤ {-a, b} = Submodule.span ℤ ({a, b} : Set ℂ) := by
  have hb : b ∈ Submodule.span ℤ ({a, b} : Set ℂ) := Submodule.subset_span (by simp)
  have ha : a ∈ Submodule.span ℤ ({a, b} : Set ℂ) := Submodule.subset_span (by simp)
  have hb' : b ∈ Submodule.span ℤ ({-a, b} : Set ℂ) := Submodule.subset_span (by simp)
  have ha' : -a ∈ Submodule.span ℤ ({-a, b} : Set ℂ) := Submodule.subset_span (by simp)
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    rcases hx with h | h
    · rw [h]; exact neg_mem ha
    · rw [Set.mem_singleton_iff.1 h]; exact hb
  · rw [Submodule.span_le]
    intro x hx
    rcases hx with h | h
    · rw [h]; simpa using neg_mem ha'
    · rw [Set.mem_singleton_iff.1 h]; exact hb'

theorem im_div_ne_zero (L : PeriodPair) : (L.ω₁ / L.ω₂).im ≠ 0 := by
  intro h
  have h2 : L.ω₂ ≠ 0 := L.indep.ne_zero 1
  set r := (L.ω₁ / L.ω₂).re with hr
  have hw : L.ω₁ / L.ω₂ = (r : ℂ) := Complex.ext (by simp [hr]) (by simpa using h)
  have hω : L.ω₁ = (r : ℂ) * L.ω₂ := by
    rw [← hw]; field_simp
  have := (LinearIndependent.pair_iff.mp L.indep 1 (-r) (by
    simp only [Complex.real_smul]
    rw [hω]; push_cast; ring)).1
  exact one_ne_zero this

/-- Every lattice is a homothety image of some `Λ(z, 1)` with `z ∈ ℍ`. -/
theorem exists_rep (Λ : Lattices) : ∃ p : ℂˣ × ℍ, Λ = Lattices.smul p.1 (latticeOf p.2) := by
  obtain ⟨Λ, L, hL⟩ := Λ
  have h2 : L.ω₂ ≠ 0 := L.indep.ne_zero 1
  have e1 : L.ω₂ * (L.ω₁ / L.ω₂) = L.ω₁ := by field_simp
  rcases lt_or_gt_of_ne (im_div_ne_zero L) with hlt | hgt
  · refine ⟨(Units.mk0 L.ω₂ h2, ⟨-(L.ω₁ / L.ω₂), by simpa using hlt⟩), Subtype.ext ?_⟩
    change Λ = (Lattices.smul _ _).1
    rw [smul_latticeOf_eq, ← hL]
    simp only [Units.val_mk0, PeriodPair.lattice]
    have : L.ω₂ * -(L.ω₁ / L.ω₂) = -L.ω₁ := by rw [mul_neg, e1]
    rw [this, span_neg_left]
  · refine ⟨(Units.mk0 L.ω₂ h2, ⟨L.ω₁ / L.ω₂, hgt⟩), Subtype.ext ?_⟩
    change Λ = (Lattices.smul _ _).1
    rw [smul_latticeOf_eq, ← hL]
    simp only [Units.val_mk0, PeriodPair.lattice]
    rw [e1]

/-- The lattice `(cz+d) Λ(γ z, 1) = Λ(z, 1)` for `γ ∈ SL(2, ℤ)`. -/
theorem smul_latticeOf_sl2 (γ : SL(2, ℤ)) (z : ℍ) :
    Lattices.smul (Units.mk0 _ (denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) z))
      (latticeOf (γ • z)) = latticeOf z := by
  apply Subtype.ext
  rw [smul_latticeOf_eq]
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) (z : ℂ) = (γ 1 0 : ℂ) * z + γ 1 1 := by
    simp [denom]
  have hne : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := hd ▸ denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) z
  have hs : ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) := by
    rw [coe_specialLinearGroup_apply]; simp
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rwa [Matrix.det_fin_two] at this
  have hdetC : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast hdet
  simp only [Units.val_mk0, hd, hs]
  rw [mul_div_cancel₀ _ hne]
  show _ = Submodule.span ℤ {(z : ℂ), 1}
  apply le_antisymm <;> rw [Submodule.span_le] <;> intro x hx <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx <;> rcases hx with rfl | rfl <;>
    rw [SetLike.mem_coe]
  · rw [Submodule.mem_span_pair]
    exact ⟨γ 0 0, γ 0 1, by simp⟩
  · rw [Submodule.mem_span_pair]
    exact ⟨γ 1 0, γ 1 1, by simp⟩
  · rw [Submodule.mem_span_pair]
    exact ⟨γ 1 1, -γ 0 1, by linear_combination (z : ℂ) * hdetC⟩
  · rw [Submodule.mem_span_pair]
    exact ⟨-γ 1 0, γ 0 0, by linear_combination hdetC⟩

/-- If `c Λ(z, 1) = c' Λ(z', 1)` then `z' = γ z` and `c' = c (c_γ z + d_γ)` for some `γ ∈ SL(2, ℤ)`. -/
theorem exists_sl2_of_smul_eq {c c' : ℂˣ} {z z' : ℍ}
    (h : Lattices.smul c (latticeOf z) = Lattices.smul c' (latticeOf z')) :
    ∃ γ : SL(2, ℤ), γ • z = z' ∧ (c' : ℂ) = c * ((γ 1 0 : ℂ) * z + γ 1 1) := by
  have hS := congrArg Subtype.val h
  rw [smul_latticeOf_eq, smul_latticeOf_eq] at hS
  have hc : (c : ℂ) ≠ 0 := c.ne_zero
  have hc' : (c' : ℂ) ≠ 0 := c'.ne_zero
  have m1 : (c' : ℂ) * z' ∈ Submodule.span ℤ ({(c : ℂ) * z, (c : ℂ)} : Set ℂ) := by
    rw [hS]; exact Submodule.subset_span (by simp)
  have m2 : (c' : ℂ) ∈ Submodule.span ℤ ({(c : ℂ) * z, (c : ℂ)} : Set ℂ) := by
    rw [hS]; exact Submodule.subset_span (by simp)
  have m3 : (c : ℂ) * z ∈ Submodule.span ℤ ({(c' : ℂ) * z', (c' : ℂ)} : Set ℂ) := by
    rw [← hS]; exact Submodule.subset_span (by simp)
  have m4 : (c : ℂ) ∈ Submodule.span ℤ ({(c' : ℂ) * z', (c' : ℂ)} : Set ℂ) := by
    rw [← hS]; exact Submodule.subset_span (by simp)
  obtain ⟨a, b, E1⟩ := Submodule.mem_span_pair.1 m1
  obtain ⟨e, d, E2⟩ := Submodule.mem_span_pair.1 m2
  obtain ⟨a', b', E3⟩ := Submodule.mem_span_pair.1 m3
  obtain ⟨e', d', E4⟩ := Submodule.mem_span_pair.1 m4
  simp only [zsmul_eq_mul] at E1 E2 E3 E4
  have Q1 : (a' * a + b' * e - 1 : ℤ) = 0 ∧ (a' * b + b' * d : ℤ) = 0 := by
    apply int_pair_eq_zero (z := z)
    have : (c : ℂ) * (((a' * a + b' * e - 1 : ℤ) : ℂ) * z + ((a' * b + b' * d : ℤ) : ℂ)) = 0 := by
      push_cast
      linear_combination a' * E1 + b' * E2 + E3
    exact (mul_eq_zero.1 this).resolve_left hc
  have Q2 : (e' * a + d' * e : ℤ) = 0 ∧ (e' * b + d' * d - 1 : ℤ) = 0 := by
    apply int_pair_eq_zero (z := z)
    have : (c : ℂ) * (((e' * a + d' * e : ℤ) : ℂ) * z + ((e' * b + d' * d - 1 : ℤ) : ℂ)) = 0 := by
      push_cast
      linear_combination e' * E1 + d' * E2 + E4
    exact (mul_eq_zero.1 this).resolve_left hc
  have hprod : (a * d - b * e) * (a' * d' - b' * e') = 1 := by
    obtain ⟨h1, h2⟩ := Q1
    obtain ⟨h3, h4⟩ := Q2
    linear_combination (e' * b + d' * d) * h1 + h4 - (e' * a + d' * e) * h2 - 0 * h3
  set w : ℂ := (e : ℂ) * z + d with hwdef
  have hcw : (c' : ℂ) = c * w := by rw [hwdef]; linear_combination -E2
  have hw0 : w ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hcw; exact hc' hcw
  have hzw : (z' : ℂ) * w = a * z + b := by
    have : (c : ℂ) * ((z' : ℂ) * w - (a * z + b)) = 0 := by
      rw [hcw] at E1
      linear_combination -E1
    have := (mul_eq_zero.1 this).resolve_left hc
    linear_combination this
  have hre := congrArg Complex.re hzw
  have him := congrArg Complex.im hzw
  simp [hwdef, Complex.mul_re, Complex.mul_im] at hre him
  have hnorm : 0 < (w.re ^ 2 + w.im ^ 2) := by
    have := Complex.normSq_pos.2 hw0
    rw [Complex.normSq_apply] at this
    nlinarith
  have hδ : (a * d - b * e : ℤ) = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hprod with h1 | h1
    · exact h1
    · exfalso
      have key : (z' : ℂ).im * (w.re ^ 2 + w.im ^ 2) = ((a * d - b * e : ℤ) : ℝ) * z.im := by
        simp only [hwdef] at hnorm ⊢
        push_cast
        simp [Complex.mul_re, Complex.mul_im] at hre him ⊢
        linear_combination ((e : ℝ) * z.re + d) * him - ((e : ℝ) * z.im) * hre
      rw [h1] at key
      have h2 : 0 < (z' : ℂ).im * (w.re ^ 2 + w.im ^ 2) := mul_pos z'.im_pos hnorm
      rw [key] at h2
      have := z.im_pos
      simp at h2
      linarith
  obtain ⟨γ, g00, g01, g10, g11⟩ : ∃ γ : SL(2, ℤ), γ 0 0 = a ∧ γ 0 1 = b ∧ γ 1 0 = e ∧ γ 1 1 = d :=
    ⟨⟨!![a, b; e, d], by simpa [Matrix.det_fin_two_of] using hδ⟩, rfl, rfl, rfl, rfl⟩
  have hw0' : (e : ℂ) * z + d ≠ 0 := hwdef ▸ hw0
  rw [hwdef] at hzw hcw
  refine ⟨γ, ?_, ?_⟩
  · apply UpperHalfPlane.ext
    rw [coe_specialLinearGroup_apply]
    simp only [g00, g01, g10, g11, algebraMap_int_eq, eq_intCast]
    push_cast
    rw [div_eq_iff hw0']
    linear_combination -hzw
  · rw [g10, g11]; exact hcw

/-- A chosen representation `Λ = c Λ(z, 1)`. -/
noncomputable def latticeRep (Λ : Lattices) : ℂˣ × ℍ := Classical.choose (exists_rep Λ)

theorem latticeRep_spec (Λ : Lattices) :
    Λ = Lattices.smul (latticeRep Λ).1 (latticeOf (latticeRep Λ).2) :=
  Classical.choose_spec (exists_rep Λ)

/-- The function on lattices attached to `f : ℍ → ℂ`: `F(c Λ(z, 1)) = c^(-2k) f(z)`. -/
noncomputable def latticeFun (k : ℕ) (f : ℍ → ℂ) (Λ : Lattices) : ℂ :=
  ((latticeRep Λ).1 : ℂ) ^ (-(2 * k : ℤ)) * f (latticeRep Λ).2

/-- The transformation law of a level-one slash invariant form, for `γ ∈ SL(2, ℤ)`. -/
theorem sl2_invariant (k : ℕ) (f : SlashInvariantForm 𝒮ℒ (2 * k : ℕ)) (γ : SL(2, ℤ)) (z : ℍ) :
    f (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ ((2 * k : ℕ) : ℤ) * f z :=
  (ModularForm.slash_action_eq'_iff _ _ γ z).1
    (congrFun (SlashInvariantForm.slash_action_eqn f (Matrix.SpecialLinearGroup.mapGL ℝ γ)
      ⟨γ, rfl⟩) z)

theorem latticeFun_smul (k : ℕ) (f : ℍ → ℂ)
    (hf : ∀ (γ : SL(2, ℤ)) (z : ℍ),
      f (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ ((2 * k : ℕ) : ℤ) * f z)
    (c : ℂˣ) (z : ℍ) :
    latticeFun k f (Lattices.smul c (latticeOf z)) = (c : ℂ) ^ (-(2 * k : ℤ)) * f z := by
  obtain ⟨γ, hγ, hc⟩ := exists_sl2_of_smul_eq (latticeRep_spec (Lattices.smul c (latticeOf z)))
  have hj : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hc
    exact (latticeRep _).1.ne_zero hc
  have hc0 : (c : ℂ) ≠ 0 := c.ne_zero
  unfold latticeFun
  rw [← hγ, hf, hc]
  have e : ((2 * k : ℕ) : ℤ) = 2 * (k : ℤ) := by push_cast; ring
  have key : ∀ j : ℂ, j ≠ 0 → ∀ n : ℤ, j ^ (-n) * j ^ n = 1 := fun j hj n ↦ by
    rw [← zpow_add₀ hj]; simp
  rw [e, mul_zpow]
  linear_combination ((c : ℂ) ^ (-(2 * (k : ℤ))) * f z) * key _ hj (2 * (k : ℤ))

theorem latticeFun_isWeight (k : ℕ) (f : ℍ → ℂ)
    (hf : ∀ (γ : SL(2, ℤ)) (z : ℍ),
      f (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ ((2 * k : ℕ) : ℤ) * f z) :
    IsWeight k (latticeFun k f) := by
  intro c' Λ
  obtain ⟨p, rfl⟩ := exists_rep Λ
  rw [smul_smul_lattice, latticeFun_smul k f hf, latticeFun_smul k f hf, Units.val_mul, mul_zpow]
  ring

theorem latticeFun_latticeOf (k : ℕ) (f : ℍ → ℂ)
    (hf : ∀ (γ : SL(2, ℤ)) (z : ℍ),
      f (γ • z) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ ((2 * k : ℕ) : ℤ) * f z) (z : ℍ) :
    latticeFun k f (latticeOf z) = f z := by
  have := latticeFun_smul k f hf 1 z
  rwa [smul_one_lattice, Units.val_one, one_zpow, one_mul] at this

/-- A function of weight `2k` on lattices gives a function on `ℍ` with the transformation law. -/
theorem weight_transform (k : ℕ) (F : Lattices → ℂ) (hF : IsWeight k F) (γ : SL(2, ℤ)) (z : ℍ) :
    F (latticeOf (γ • z)) = ((γ 1 0 : ℂ) * z + γ 1 1) ^ ((2 * k : ℕ) : ℤ) * F (latticeOf z) := by
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) (z : ℂ) = (γ 1 0 : ℂ) * z + γ 1 1 := by
    simp [denom]
  have hj : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := hd ▸ denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) z
  have h := hF (Units.mk0 _ (denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) z))
    (latticeOf (γ • z))
  rw [smul_latticeOf_sl2] at h
  simp only [Units.val_mk0, hd] at h
  have e : ((2 * k : ℕ) : ℤ) + -(2 * (k : ℤ)) = 0 := by push_cast; ring
  rw [h, ← mul_assoc, ← zpow_add₀ hj, e, zpow_zero, one_mul]

/-- **Lemma 4.6**: $F \mapsto f$, $f(z) = F(\Lambda(z, 1))$, is a bijection from the functions of weight $2k$ on the set
of lattices to the weakly modular forms of weight $2k$ on $\mathbb H$. -/
@[kb "milne2017mf" "Section 4, Lemma 4.6 (pdf p. 49)"]
theorem lattice_weight_equiv (k : ℕ) :
    ∃ e : {F : Lattices → ℂ // IsWeight k F} ≃ SlashInvariantForm 𝒮ℒ (2 * k : ℕ),
      ∀ F z, e F z = F.1 (latticeOf z) := by
  refine ⟨{
    toFun := fun F ↦ ⟨fun z ↦ F.1 (latticeOf z), ?_⟩
    invFun := fun f ↦ ⟨latticeFun k f, latticeFun_isWeight k f (sl2_invariant k f)⟩
    left_inv := ?_
    right_inv := ?_ }, fun F z ↦ rfl⟩
  · rintro g ⟨γ, rfl⟩
    funext z
    exact (ModularForm.slash_action_eq'_iff _ _ γ z).2 (weight_transform k F.1 F.2 γ z)
  · rintro ⟨F, hF⟩
    apply Subtype.ext
    funext Λ
    obtain ⟨p, rfl⟩ := exists_rep Λ
    show latticeFun k (fun z ↦ F (latticeOf z)) _ = _
    rw [latticeFun_smul k _ (weight_transform k F hF)]
    exact (hF p.1 (latticeOf p.2)).symm
  · intro f
    apply SlashInvariantForm.ext
    intro z
    exact latticeFun_latticeOf k f (sl2_invariant k f) z

end ModularFormsKB.Milne
