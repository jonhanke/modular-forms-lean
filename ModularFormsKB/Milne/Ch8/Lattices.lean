import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import ModularFormsKB.Citation
/-!
# Milne, Chapter 8: $\Gamma_0(N)\backslash\mathbb H$ classifies lattices with a cyclic subgroup of order $N$ (Lemma 8.5)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 8, pdf p. 99.

**Lattice form.** Milne's $\mathcal E_{0,N}(\mathbb C)$ (isomorphism classes of complex elliptic curves with a cyclic
subgroup of order $N$) and $\mathcal E_N(\mathbb C)$ (with a level-$N$ structure of Weil pairing $\zeta$) are read
through the analytic description of complex elliptic curves (Milne, Section 3): $E \cong \mathbb C/\Lambda$, and
isomorphisms $\mathbb C/\Lambda \to \mathbb C/\Lambda'$ are the homotheties $z \mapsto cz$ with $c\Lambda = \Lambda'$.
A cyclic subgroup $S$ of order $N$ of $\mathbb C/\Lambda$ is $\Lambda'/\Lambda$ for a lattice $\Lambda' \supseteq \Lambda$
with $\Lambda'/\Lambda$ cyclic of order $N$. A lattice is the period lattice of a Mathlib `PeriodPair`. Lemma 8.7
(level-$N$ structures, $\Gamma(N)$) is in `ModularFormsKB.Milne.Ch8.LevelStructures`.

- **Lemma 8.5**: `lemma_8_5_injective` (two points give homothetic pairs iff they are $\Gamma_0(N)$-equivalent) and
  `lemma_8_5_surjective`.
-/

open Complex CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Real
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne

/-- A lattice in $\mathbb C$: the $\mathbb Z$-span of two $\mathbb R$-linearly independent complex numbers (Mathlib's
`PeriodPair.lattice`). -/
def IsLatticeC (Λ : Submodule ℤ ℂ) : Prop :=
  ∃ P : PeriodPair, P.lattice = Λ

/-- The image $c\Lambda$ of a lattice under the homothety $z \mapsto cz$. -/
def homothety (c : ℂ) (Λ : Submodule ℤ ℂ) : Submodule ℤ ℂ :=
  Λ.map ((LinearMap.mulLeft ℤ c : ℂ →ₗ[ℤ] ℂ))

/-- A pair $(\Lambda, \Lambda')$ of lattices with $\Lambda \subseteq \Lambda'$ and $\Lambda'/\Lambda$ cyclic of order $N$:
the torus $\mathbb C/\Lambda$ with the cyclic subgroup $\Lambda'/\Lambda$ of order $N$. -/
def IsCyclicPair (N : ℕ) (Λ Λ' : Submodule ℤ ℂ) : Prop :=
  IsLatticeC Λ ∧ Λ ≤ Λ' ∧ IsAddCyclic (Λ' ⧸ Λ.comap Λ'.subtype) ∧ Nat.card (Λ' ⧸ Λ.comap Λ'.subtype) = N

/-- The lattice $(\omega_1, \omega_2) = \mathbb Z\omega_1 + \mathbb Z\omega_2$. -/
def complexLatticeSpan (ω₁ ω₂ : ℂ) : Submodule ℤ ℂ :=
  Submodule.span ℤ {ω₁, ω₂}

/-- Membership in `complexLatticeSpan`: integer combinations. -/
theorem mem_complexLatticeSpan {x a b : ℂ} :
    x ∈ complexLatticeSpan a b ↔ ∃ m n : ℤ, (m : ℂ) * a + n * b = x := by
  simp [complexLatticeSpan, Submodule.mem_span_pair]

/-- Membership in a homothetic image. -/
theorem mem_homothety {c y : ℂ} {Λ : Submodule ℤ ℂ} :
    y ∈ homothety c Λ ↔ ∃ x ∈ Λ, c * x = y := by
  simp [homothety]

/-- A homothety carries `complexLatticeSpan a b` to `complexLatticeSpan (c a) (c b)`. -/
theorem homothety_complexLatticeSpan (c a b : ℂ) :
    homothety c (complexLatticeSpan a b) = complexLatticeSpan (c * a) (c * b) := by
  simp [homothety, complexLatticeSpan, Submodule.map_span]

/-- Integral independence of `(z, 1)` for `Im z > 0`. -/
theorem int_indep {z : ℂ} (hz : 0 < z.im) {m n : ℤ} (h : (m : ℂ) * z + n = 0) : m = 0 ∧ n = 0 := by
  have h1 := congrArg Complex.im h
  have h2 : (m : ℝ) * z.im = 0 := by simpa using h1
  have hm : m = 0 := by
    have := (mul_eq_zero.mp h2).resolve_right hz.ne'
    exact_mod_cast this
  subst hm
  refine ⟨rfl, ?_⟩
  simpa using h

/-- Real independence of `(z, 1)` for `Im z > 0`. -/
theorem real_indep {z : ℂ} (hz : 0 < z.im) {s t : ℝ} (h : (s : ℂ) * z + t = 0) : s = 0 ∧ t = 0 := by
  have h1 := congrArg Complex.im h
  have h2 : s * z.im = 0 := by simpa using h1
  have hm : s = 0 := (mul_eq_zero.mp h2).resolve_right hz.ne'
  subst hm
  refine ⟨rfl, ?_⟩
  have := congrArg Complex.re h
  simpa using this

/-- Change of basis by a unimodular integer matrix does not change the lattice. -/
theorem complexLatticeSpan_unimodular (x y : ℂ) (a b c d : ℤ) (h : a * d - b * c = 1) :
    complexLatticeSpan ((a : ℂ) * x + b * y) ((c : ℂ) * x + d * y) = complexLatticeSpan x y := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro t ht
    rcases ht with rfl | rfl
    · exact mem_complexLatticeSpan.mpr ⟨a, b, rfl⟩
    · exact mem_complexLatticeSpan.mpr ⟨c, d, rfl⟩
  · apply Submodule.span_le.mpr
    intro t ht
    have hh : (a : ℂ) * d - b * c = 1 := by exact_mod_cast h
    rcases ht with rfl | rfl
    · refine mem_complexLatticeSpan.mpr ⟨d, -b, ?_⟩
      push_cast
      linear_combination t * hh
    · refine mem_complexLatticeSpan.mpr ⟨-c, a, ?_⟩
      push_cast
      linear_combination t * hh

/-- A cyclic group's cardinality is the order of a generator. -/
theorem natCard_eq_addOrderOf {Q : Type*} [AddCommGroup Q] (g : Q)
    (hg : Function.Surjective (fun k : ℤ => k • g)) : Nat.card Q = addOrderOf g := by
  rw [← Nat.card_zmultiples]
  apply Nat.card_congr
  exact (Equiv.subtypeUnivEquiv (fun x => by
    obtain ⟨k, rfl⟩ := hg x
    exact AddSubgroup.zsmul_mem_zmultiples g k)).symm

/-- Order characterization via divisibility. -/
theorem addOrderOf_eq_of_dvd_iff {G : Type*} [AddMonoid G] (g : G) (N : ℕ)
    (h : ∀ k : ℕ, k • g = 0 ↔ N ∣ k) : addOrderOf g = N := by
  apply Nat.dvd_antisymm
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    exact (h N).mpr dvd_rfl
  · exact (h _).mp (addOrderOf_nsmul_eq_zero g)

/-- Positivity of the determinant relating two oriented bases. -/
theorem det_pos_aux {Z W c : ℂ} (hZ : 0 < Z.im) (hW : 0 < W.im) (hc : c ≠ 0) {p q r s : ℤ}
    (hpq : (p : ℂ) * W + q * 1 = c * Z) (hrs : (r : ℂ) * W + s * 1 = c) : 0 < p * s - q * r := by
  have ea1 : c.re = r * W.re + s := by
    have := congrArg Complex.re hrs; simpa using this.symm
  have ea2 : c.im = r * W.im := by
    have := congrArg Complex.im hrs; simpa using this.symm
  have reeq : c.re * Z.re - c.im * Z.im = p * W.re + q := by
    have := congrArg Complex.re hpq; simp at this; linarith
  have imeq : c.re * Z.im + c.im * Z.re = p * W.im := by
    have := congrArg Complex.im hpq; simp at this; linarith
  have key : Z.im * (c.re ^ 2 + c.im ^ 2) = ((p * s - q * r : ℤ) : ℝ) * W.im := by
    push_cast
    linear_combination c.re * imeq - c.im * reeq + p * W.im * ea1 - (p * W.re + q) * ea2
  have hc2 : 0 < c.re ^ 2 + c.im ^ 2 := by
    by_contra hneg
    apply hc
    apply Complex.ext
    · simp only [Complex.zero_re]; nlinarith [sq_nonneg c.re, sq_nonneg c.im]
    · simp only [Complex.zero_im]; nlinarith [sq_nonneg c.re, sq_nonneg c.im]
  have h0 : (0 : ℝ) < ((p * s - q * r : ℤ) : ℝ) * W.im := by
    rw [← key]; exact mul_pos hZ hc2
  have h3 : (0 : ℝ) < ((p * s - q * r : ℤ) : ℝ) := by
    by_contra hneg
    have hneg' := not_lt.mp hneg
    nlinarith
  exact_mod_cast h3

/-- The easy direction of Lemma 8.5 (injectivity) in terms of matrix entries. -/
theorem inj_aux {N : ℕ} (hN : 0 < N) {z : ℂ} (hz : 0 < z.im) (a b k d : ℤ)
    (hdet : a * d - b * (N * k) = 1) :
    ∃ c : ℂ, c ≠ 0 ∧
      homothety c (complexLatticeSpan z 1) = complexLatticeSpan (((a : ℂ) * z + b) / ((N * k : ℤ) * z + d)) 1 ∧
      homothety c (complexLatticeSpan z (1 / N)) =
        complexLatticeSpan (((a : ℂ) * z + b) / ((N * k : ℤ) * z + d)) (1 / N) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hD : (((N * k : ℤ) : ℂ) * z + d) ≠ 0 := by
    intro h0
    obtain ⟨h1, h2⟩ := int_indep hz h0
    rw [h1, h2] at hdet; simp at hdet
  refine ⟨1 / (((N * k : ℤ) : ℂ) * z + d), one_div_ne_zero hD, ?_, ?_⟩
  · rw [← complexLatticeSpan_unimodular z 1 a b (N * k) d hdet, homothety_complexLatticeSpan]
    have e2 : 1 / (((N * k : ℤ) : ℂ) * z + d) * (((N * k : ℤ) : ℂ) * z + d * 1) = 1 := by
      rw [mul_one]; exact one_div_mul_cancel hD
    rw [e2]
    congr 1
    ring
  · have hdet' : a * d - (N * b) * k = 1 := by linarith
    rw [← complexLatticeSpan_unimodular z (1 / N) a (N * b) k d hdet', homothety_complexLatticeSpan]
    have e1 : (((N * b : ℤ) : ℂ)) * (1 / N) = b := by push_cast; field_simp
    have e2 : 1 / (((N * k : ℤ) : ℂ) * z + d) * ((k : ℂ) * z + d * (1 / N)) = 1 / N := by
      have : ((k : ℂ) * z + d * (1 / N)) = (((N * k : ℤ) : ℂ) * z + d) / N := by
        push_cast; field_simp
      rw [this]; field_simp
    rw [e1, e2]
    congr 1
    ring

/-- Multiples of a class in the quotient `Λ'/Λ` vanish iff the multiple lies in `Λ`. -/
theorem quot_nsmul_mk_eq_zero (Λ Λ' : Submodule ℤ ℂ) (x : Λ') (k : ℕ) :
    k • (Submodule.Quotient.mk x : Λ' ⧸ Λ.comap Λ'.subtype) = 0 ↔ (k : ℂ) * (x : ℂ) ∈ Λ := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  simp

/-- `k/N ∈ ℤ z + ℤ` iff `N ∣ k`. -/
theorem natCast_mul_inv_mem_iff {N : ℕ} (hN : 0 < N) {z : ℂ} (hz : 0 < z.im) (k : ℕ) :
    (k : ℂ) * (1 / N) ∈ complexLatticeSpan z 1 ↔ N ∣ k := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  constructor
  · intro h
    obtain ⟨m, n, hmn⟩ := mem_complexLatticeSpan.mp h
    have := int_indep hz (m := N * m) (n := N * n - k) (by
      push_cast
      field_simp at hmn
      linear_combination hmn)
    have h2 : (k : ℤ) = N * n := by linarith [this.2]
    exact Int.natCast_dvd_natCast.mp ⟨n, h2⟩
  · rintro ⟨j, rfl⟩
    exact mem_complexLatticeSpan.mpr ⟨0, j, by push_cast; field_simp; simp⟩

/-- `complexLatticeSpan` is symmetric. -/
theorem complexLatticeSpan_comm (a b : ℂ) : complexLatticeSpan a b = complexLatticeSpan b a := by
  simp [complexLatticeSpan, Set.pair_comm]

/-- Negating the second generator does not change the lattice. -/
theorem complexLatticeSpan_neg_right (a b : ℂ) : complexLatticeSpan a (-b) = complexLatticeSpan a b := by
  ext x
  simp only [mem_complexLatticeSpan]
  constructor
  · rintro ⟨m, n, h⟩; exact ⟨m, -n, by push_cast; linear_combination h⟩
  · rintro ⟨m, n, h⟩; exact ⟨m, -n, by push_cast; linear_combination h⟩

/-- Integer multiples of members of a submodule stay in it. -/
theorem intCast_mul_mem (Λ : Submodule ℤ ℂ) (k : ℤ) {x : ℂ} (hx : x ∈ Λ) : (k : ℂ) * x ∈ Λ := by
  simpa [zsmul_eq_mul] using Λ.smul_mem k hx

/-- Final normalization: bases `(y', y)` of `Λ` and `(y', y/N)` of `Λ'` with `Im (y'/y) ≠ 0`. -/
theorem surj_final {N : ℕ} (hN : 0 < N) {y y' : ℂ} (hy : y ≠ 0) (him : (y' / y).im ≠ 0)
    (Λ Λ' : Submodule ℤ ℂ) (hΛ : Λ = complexLatticeSpan y' y) (hΛ' : Λ' = complexLatticeSpan y' (y / N)) :
    ∃ (z : ℍ) (c : ℂ), c ≠ 0 ∧ homothety c Λ = complexLatticeSpan z 1 ∧
      homothety c Λ' = complexLatticeSpan z (1 / N) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  subst hΛ hΛ'
  rcases lt_or_gt_of_ne him with h | h
  · refine ⟨⟨-(y' / y), by simpa using h⟩, -(1 / y), neg_ne_zero.mpr (one_div_ne_zero hy), ?_, ?_⟩
    · rw [homothety_complexLatticeSpan]
      have e1 : -(1 / y) * y' = -(y' / y) := by ring
      have e2 : -(1 / y) * y = -1 := by field_simp
      rw [e1, e2, complexLatticeSpan_neg_right]
    · rw [homothety_complexLatticeSpan]
      have e1 : -(1 / y) * y' = -(y' / y) := by ring
      have e2 : -(1 / y) * (y / N) = -(1 / N) := by field_simp
      rw [e1, e2, complexLatticeSpan_neg_right]
  · refine ⟨⟨y' / y, h⟩, 1 / y, one_div_ne_zero hy, ?_, ?_⟩
    · rw [homothety_complexLatticeSpan]
      have e1 : 1 / y * y' = y' / y := by ring
      have e2 : 1 / y * y = 1 := by field_simp
      rw [e1, e2]
    · rw [homothety_complexLatticeSpan]
      have e1 : 1 / y * y' = y' / y := by ring
      have e2 : 1 / y * (y / N) = 1 / N := by field_simp
      rw [e1, e2]

/-- **Milne, Lemma 8.5** (injectivity, lattice form): $z \mapsto (\mathbb C/(z, 1), (z, N^{-1})/(z, 1))$; the pairs
attached to $z, w \in \mathbb H$ are homothetic iff $w \in \Gamma_0(N) z$. -/
@[kb "milne2017mf" "Section 8, Lemma 8.5 (pdf p. 99), lattice form, injectivity"]
theorem lemma_8_5_injective {N : ℕ} (hN : 0 < N) (z w : ℍ) :
    (∃ c : ℂ, c ≠ 0 ∧ homothety c (complexLatticeSpan z 1) = complexLatticeSpan w 1 ∧
      homothety c (complexLatticeSpan z (1 / N)) = complexLatticeSpan w (1 / N)) ↔ ∃ γ ∈ Gamma0 N, γ • z = w := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  constructor
  · rintro ⟨c, hc, h1, h2⟩
    have hmem1 : ∀ x ∈ complexLatticeSpan (z : ℂ) 1, c * x ∈ complexLatticeSpan (w : ℂ) 1 := fun x hx => by
      rw [← h1]; exact mem_homothety.mpr ⟨x, hx, rfl⟩
    have hz1 : (z : ℂ) ∈ complexLatticeSpan (z : ℂ) 1 := mem_complexLatticeSpan.mpr ⟨1, 0, by simp⟩
    have h11 : (1 : ℂ) ∈ complexLatticeSpan (z : ℂ) 1 := mem_complexLatticeSpan.mpr ⟨0, 1, by simp⟩
    obtain ⟨p, q, hpq⟩ := mem_complexLatticeSpan.mp (hmem1 _ hz1)
    obtain ⟨r, s, hrs⟩ := mem_complexLatticeSpan.mp (by simpa using hmem1 _ h11)
    have hw1 : (w : ℂ) ∈ complexLatticeSpan (w : ℂ) 1 := mem_complexLatticeSpan.mpr ⟨1, 0, by simp⟩
    have h11' : (1 : ℂ) ∈ complexLatticeSpan (w : ℂ) 1 := mem_complexLatticeSpan.mpr ⟨0, 1, by simp⟩
    obtain ⟨x1, hx1, hx1e⟩ := mem_homothety.mp (h1 ▸ hw1)
    obtain ⟨x2, hx2, hx2e⟩ := mem_homothety.mp (h1 ▸ h11')
    obtain ⟨α, β, hαβ⟩ := mem_complexLatticeSpan.mp hx1
    obtain ⟨γ, δ, hγδ⟩ := mem_complexLatticeSpan.mp hx2
    have hα : c * ((α : ℂ) * z + β * 1) = w := by rw [hαβ]; exact hx1e
    have hδ : c * ((γ : ℂ) * z + δ * 1) = 1 := by rw [hγδ]; exact hx2e
    have e1 := int_indep w.im_pos (m := α * p + β * r - 1) (n := α * q + β * s) (by
      push_cast; linear_combination (α : ℂ) * hpq + (β : ℂ) * hrs + hα)
    have e2 := int_indep w.im_pos (m := γ * p + δ * r) (n := γ * q + δ * s - 1) (by
      push_cast; linear_combination (γ : ℂ) * hpq + (δ : ℂ) * hrs + hδ)
    have hprod : (α * δ - β * γ) * (p * s - q * r) = 1 := by
      have : (α * δ - β * γ) * (p * s - q * r)
          = (α * p + β * r) * (γ * q + δ * s) - (α * q + β * s) * (γ * p + δ * r) := by ring
      rw [this]
      have a1 : α * p + β * r = 1 := by linarith [e1.1]
      have a2 : α * q + β * s = 0 := e1.2
      have a3 : γ * p + δ * r = 0 := e2.1
      have a4 : γ * q + δ * s = 1 := by linarith [e2.2]
      rw [a1, a2, a3, a4]; norm_num
    -- positivity of the determinant
    have hpos : 0 < p * s - q * r := det_pos_aux z.im_pos w.im_pos hc hpq hrs
    have hdet : p * s - q * r = 1 := by
      rw [mul_comm] at hprod
      exact Int.eq_one_of_mul_eq_one_right hpos.le hprod
    -- N divides r
    have hmemN : c * (1 / (N : ℂ)) ∈ complexLatticeSpan (w : ℂ) (1 / N) := by
      rw [← h2]
      exact mem_homothety.mpr ⟨1 / (N : ℂ), mem_complexLatticeSpan.mpr ⟨0, 1, by simp⟩, rfl⟩
    obtain ⟨u, v, huv⟩ := mem_complexLatticeSpan.mp hmemN
    have hN' : (N : ℂ) * (1 / N) = 1 := by field_simp
    have e3 := int_indep w.im_pos (m := N * u - r) (n := v - s) (by
      push_cast
      linear_combination (N : ℂ) * huv - hrs + (c - v) * hN')
    have hNr : (N : ℤ) ∣ r := ⟨u, by linarith [e3.1]⟩
    have hdetC : (p : ℂ) * s - q * r = 1 := by exact_mod_cast hdet
    let g : SL(2, ℤ) := ⟨!![s, -q; -r, p], by simp [Matrix.det_fin_two]; linarith⟩
    have hg : g ∈ Gamma0 N := by
      rw [Gamma0_mem]
      have : g 1 0 = -r := by simp [g]
      rw [this]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact (dvd_neg).mpr hNr
    refine ⟨g, hg, ?_⟩
    have hcz : c * (z : ℂ) = p * w + q := by linear_combination -hpq
    have hcr : c = r * w + s := by linear_combination -hrs
    have hne : (-(r : ℂ) * z + p) ≠ 0 := by
      intro h0
      have : c * (-(r : ℂ) * z + p) = 1 := by
        linear_combination (-(r : ℂ)) * hcz + (p : ℂ) * hcr + hdetC
      rw [h0] at this; simp at this
    have hne' : -((r : ℂ) * z) + p ≠ 0 := by rwa [neg_mul] at hne
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [g]
    rw [div_eq_iff hne']
    apply mul_left_cancel₀ hc
    linear_combination ((r : ℂ) * w + s) * hcz - ((p : ℂ) * w + q) * hcr
  · rintro ⟨γ, hγ, rfl⟩
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.det_coe
      rw [Matrix.det_fin_two] at this
      exact this
    obtain ⟨k, hk⟩ : (N : ℤ) ∣ γ 1 0 := by
      have := Gamma0_mem.mp hγ
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
    have hdet' : γ 0 0 * γ 1 1 - γ 0 1 * (N * k) = 1 := by rw [← hk]; exact hdet
    obtain ⟨c, hc, h1, h2⟩ := inj_aux hN z.im_pos (γ 0 0) (γ 0 1) k (γ 1 1) hdet'
    have hw : ((γ • z : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * z + (γ 0 1 : ℤ)) /
        (((N * k : ℤ) : ℂ) * z + (γ 1 1 : ℤ)) := by
      rw [UpperHalfPlane.coe_specialLinearGroup_apply, ← hk]
      simp
    exact ⟨c, hc, by rw [hw]; exact h1, by rw [hw]; exact h2⟩

/-- **Milne, Lemma 8.5** (surjectivity, lattice form): every lattice with a cyclic subgroup of order $N$ is homothetic
to $((z, 1), (z, N^{-1}))$ for some $z \in \mathbb H$. -/
@[kb "milne2017mf" "Section 8, Lemma 8.5 (pdf p. 99), lattice form, surjectivity"]
theorem lemma_8_5_surjective {N : ℕ} (hN : 0 < N) (Λ Λ' : Submodule ℤ ℂ) (h : IsCyclicPair N Λ Λ') :
    ∃ (z : ℍ) (c : ℂ), c ≠ 0 ∧ homothety c Λ = complexLatticeSpan z 1 ∧ homothety c Λ' = complexLatticeSpan z (1 / N) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨⟨P, hP⟩, hle, hcyc, hcard⟩ := h
  have hΛ : Λ = complexLatticeSpan P.ω₁ P.ω₂ := hP.symm
  obtain ⟨g, hg⟩ := hcyc.exists_zsmul_surjective
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ g
  have hord : addOrderOf (Submodule.Quotient.mk x : Λ' ⧸ Λ.comap Λ'.subtype) = N := by
    rw [← natCard_eq_addOrderOf _ hg]; exact hcard
  have hk : ∀ k : ℕ, (k : ℂ) * (x : ℂ) ∈ Λ ↔ N ∣ k := fun k => by
    rw [← quot_nsmul_mk_eq_zero Λ Λ' x k, ← addOrderOf_dvd_iff_nsmul_eq_zero, hord]
  have hNx : (N : ℂ) * (x : ℂ) ∈ Λ := (hk N).mpr dvd_rfl
  rw [hΛ] at hNx
  obtain ⟨m, n, hmn⟩ := mem_complexLatticeSpan.mp hNx
  obtain ⟨gg, m', n', hcop, hm, hn⟩ : ∃ (gg : ℤ) (m' n' : ℤ), IsCoprime m' n' ∧ m = m' * gg ∧
      n = n' * gg := by
    by_cases h0 : Int.gcd m n = 0
    · obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp h0
      exact ⟨0, 1, 0, isCoprime_one_left, by simp, by simp⟩
    · obtain ⟨g, m', n', hpos, hgcd, hm, hn⟩ := Int.exists_gcd_one' (Nat.pos_of_ne_zero h0)
      exact ⟨g, m', n', Int.isCoprime_iff_gcd_eq_one.mpr hgcd, hm, hn⟩
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨y, hy⟩ : ∃ y : ℂ, y = m' * P.ω₁ + n' * P.ω₂ := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y' : ℂ, y' = -v * P.ω₁ + u * P.ω₂ := ⟨_, rfl⟩
  have hNxy : (N : ℂ) * x = gg * y := by
    rw [← hmn, hm, hn, hy]; push_cast; ring
  have hyΛ : ∀ t : ℤ, (t : ℂ) * y ∈ Λ := fun t => by
    rw [hΛ]
    exact mem_complexLatticeSpan.mpr ⟨t * m', t * n', by rw [hy]; push_cast; ring⟩
  have hcopgN : IsCoprime gg (N : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have hdN : Int.gcd gg N ∣ N := Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right gg (N : ℤ))
    obtain ⟨k, hkN⟩ := hdN
    obtain ⟨g1, hg1⟩ : ((Int.gcd gg N : ℕ) : ℤ) ∣ gg := Int.gcd_dvd_left gg N
    have hd0 : 0 < Int.gcd gg N := Nat.pos_of_dvd_of_pos ⟨k, hkN⟩ hN
    have hdc : ((Int.gcd gg N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hkx : (k : ℂ) * x = g1 * y := by
      apply mul_left_cancel₀ hdc
      have h1 : ((Int.gcd gg N : ℕ) : ℂ) * k = N := by exact_mod_cast hkN.symm
      have h2 : (gg : ℂ) = ((Int.gcd gg N : ℕ) : ℂ) * g1 := by exact_mod_cast hg1
      linear_combination (x : ℂ) * h1 + hNxy + y * h2
    have hkΛ : (k : ℂ) * x ∈ Λ := by rw [hkx]; exact hyΛ g1
    have hNk : N ∣ k := (hk k).mp hkΛ
    have hkN' : k ∣ N := Dvd.intro_left (Int.gcd gg N) hkN.symm
    have hkeq : k = N := Nat.dvd_antisymm hkN' hNk
    rw [hkeq] at hkN
    exact Nat.eq_of_mul_eq_mul_right hN (by rw [one_mul]; exact hkN.symm)
  obtain ⟨a, b, hab⟩ := hcopgN
  have hdet : m' * u - n' * (-v) = 1 := by linarith
  have hΛy : Λ = complexLatticeSpan y' y := by
    rw [hΛ, complexLatticeSpan_comm y' y, hy, hy', ← complexLatticeSpan_unimodular P.ω₁ P.ω₂ m' n' (-v) u hdet]
    push_cast; rfl
  have hx' : (x : ℂ) = gg * y / N := by
    rw [eq_div_iff hNc]; linear_combination hNxy
  have hNN : (N : ℂ) * (N : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hNc
  have hΛ' : Λ' = complexLatticeSpan y' (y / N) := by
    apply le_antisymm
    · intro t ht
      obtain ⟨j, hj⟩ := hg (Submodule.Quotient.mk ⟨t, ht⟩)
      have hj' : (j : ℂ) * x - t ∈ Λ := by
        have h2 : (Submodule.Quotient.mk (j • x) : Λ' ⧸ Λ.comap Λ'.subtype) =
            Submodule.Quotient.mk ⟨t, ht⟩ := by rw [Submodule.Quotient.mk_smul]; exact hj
        have := (Submodule.Quotient.eq _).mp h2
        simpa [zsmul_eq_mul] using this
      rw [hΛy] at hj'
      obtain ⟨α, β, hαβ⟩ := mem_complexLatticeSpan.mp hj'
      refine mem_complexLatticeSpan.mpr ⟨-α, j * gg - β * N, ?_⟩
      rw [hx'] at hαβ
      push_cast
      simp only [div_eq_mul_inv] at hαβ ⊢
      linear_combination -hαβ - (β * y) * hNN
    · apply Submodule.span_le.mpr
      intro t ht
      have hyΛ' : ∀ t : ℤ, (t : ℂ) * y ∈ Λ' := fun t => hle (hyΛ t)
      rcases ht with rfl | rfl
      · apply hle
        rw [hΛy]
        exact mem_complexLatticeSpan.mpr ⟨1, 0, by simp⟩
      · have : y / N = (a : ℂ) * x + b * y := by
          rw [hx']
          have hab' : (a : ℂ) * gg + b * N = 1 := by exact_mod_cast hab
          simp only [div_eq_mul_inv]
          linear_combination (-(y * (N : ℂ)⁻¹)) * hab' + (b * y) * hNN
        rw [this]
        exact Λ'.add_mem (intCast_mul_mem Λ' a x.2) (hyΛ' b)
  have hy0 : y ≠ 0 := by
    intro h0
    have := LinearIndependent.pair_iff.mp P.indep (m' : ℝ) (n' : ℝ) (by
      simpa [Complex.real_smul, hy] using h0)
    have h1 : m' = 0 := by exact_mod_cast this.1
    have h2 : n' = 0 := by exact_mod_cast this.2
    rw [h1, h2] at huv; simp at huv
  have him : (y' / y).im ≠ 0 := by
    intro h0
    have hr : y' / y = (((y' / y).re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using h0)
    set r : ℝ := (y' / y).re
    have hyr : y' = r * y := by
      rw [div_eq_iff hy0] at hr; exact hr
    have := LinearIndependent.pair_iff.mp P.indep (-v - r * m') (u - r * n') (by
      simp only [Complex.real_smul]
      push_cast
      rw [hy, hy'] at hyr
      linear_combination hyr)
    have e1 : (v : ℝ) = -(r * m') := by linarith [this.1]
    have e2 : (u : ℝ) = r * n' := by linarith [this.2]
    have huv' : (u : ℝ) * m' + v * n' = 1 := by exact_mod_cast huv
    rw [e1, e2] at huv'
    nlinarith
  exact surj_final hN hy0 him Λ Λ' hΛy hΛ'

/-- The pairs attached to $z$ are cyclic pairs of order $N$. -/
theorem isCyclicPair_complexLatticeSpan {N : ℕ} (hN : 0 < N) (z : ℍ) :
    IsCyclicPair N (complexLatticeSpan z 1) (complexLatticeSpan z (1 / N)) := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hle : complexLatticeSpan (z : ℂ) 1 ≤ complexLatticeSpan (z : ℂ) (1 / N) := by
    intro x hx
    obtain ⟨m, n, rfl⟩ := mem_complexLatticeSpan.mp hx
    exact mem_complexLatticeSpan.mpr ⟨m, n * N, by push_cast; field_simp⟩
  have hg : (1 / (N : ℂ)) ∈ complexLatticeSpan (z : ℂ) (1 / N) := mem_complexLatticeSpan.mpr ⟨0, 1, by simp⟩
  let g : complexLatticeSpan (z : ℂ) (1 / N) ⧸ (complexLatticeSpan (z : ℂ) 1).comap
      (complexLatticeSpan (z : ℂ) (1 / N)).subtype := Submodule.Quotient.mk ⟨1 / N, hg⟩
  have hsurj : Function.Surjective (fun k : ℤ => k • g) := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨m, n, hmn⟩ := mem_complexLatticeSpan.mp x.2
      refine ⟨n, ?_⟩
      show n • Submodule.Quotient.mk _ = _
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      refine mem_complexLatticeSpan.mpr ⟨-m, 0, ?_⟩
      simp only [Submodule.subtype_apply, Submodule.coe_sub,
        Submodule.coe_smul, zsmul_eq_mul]
      push_cast
      rw [← hmn]; ring
  refine ⟨⟨⟨z, 1, ?_⟩, rfl⟩, hle, ⟨g, hsurj⟩, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro s t h
    have := real_indep z.im_pos (s := s) (t := t) (by simpa using h)
    exact this
  · rw [natCard_eq_addOrderOf g hsurj]
    apply addOrderOf_eq_of_dvd_iff
    intro k
    rw [← natCast_mul_inv_mem_iff hN z.im_pos k]
    exact quot_nsmul_mk_eq_zero _ _ ⟨1 / N, hg⟩ k

end ModularFormsKB.Milne
