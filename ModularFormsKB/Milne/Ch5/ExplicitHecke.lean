import ModularFormsKB.Milne.Ch5.LevelOne
import ModularFormsKB.Milne.Ch5.LatticeHeckeAlgebra

/-!
# Milne, Chapter 5: the explicit Hecke operator on functions on $\mathbb H$ (pp. 73–76)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf pp. 73–76.

Milne defines $T(n)f(z) = n^{2k-1}(T(n)F)(\Lambda(z,1))$ for $F$ the function on lattices attached to $f$, that is
$T(n)f(z) = n^{2k-1}\sum d^{-2k}f\big(\frac{az+b}{d}\big)$ over the triples of Lemma 5.13 (`milneHeckeSum`). For a
modular form this is the operator `heckeT` of `LevelOneBridge.lean` (`heckeT_apply`).

**Slash operators.** Milne's slash operator (p. 75) is $f|_k\alpha = (\det\alpha)^k(cz+d)^{-2k}f(\alpha z)$ for
$\alpha \in \mathrm{GL}_2(\mathbb R)^+$ (`milneSlash`). Mathlib's weight-$w$ slash action is
$f \mid_w \alpha = (\det\alpha)^{w-1}(cz+d)^{-w}f(\alpha z)$ for $\det\alpha > 0$; with $w = 2k$ the two differ by
$(\det\alpha)^{k-1}$ (`milneSlash_eq`).

## Items
- The operator $T(n)$ on functions, p. 73 (`milneHeckeSum`), and on modular forms (`heckeT_apply`).
- The relation with functions on lattices, p. 73 (`milneHeckeSum_latticeFun`).
- Proposition 5.16(a) for weakly modular forms (`milneHeckeSum_slash_invariant`, `milneHeckeSum_mul_of_coprime`,
  `milneHeckeSum_prime_mul_prime_pow`).
- The slash operator, p. 75 (`milneSlash`, `milneSlash_eq`, `milneSlash_scalar`).
- The restatement $T(n)f = n^{k-1}\sum_{\alpha \in \Gamma(1)\backslash M(n)} f|_k\alpha$, independent of the
  representatives, p. 76 (`milneHeckeSum_eq_sum_milneSlash`).
-/

open UpperHalfPlane ModularForm Matrix

open scoped MatrixGroups ModularForm

namespace ModularFormsKB.Milne

/-- **Milne's Hecke operator on functions on $\mathbb H$** (p. 73):
$T(n)f(z) = n^{2k-1}\sum d^{-2k}f\big(\frac{az+b}{d}\big)$, the sum over the triples $ad = n$, $a \ge 1$, $0 \le b < d$
of Lemma 5.13. -/
@[kb "milne2017mf" "Section 5, definition of T(n) f (pdf p. 73)"]
noncomputable def milneHeckeSum (k n : ℕ) (f : ℍ → ℂ) : ℍ → ℂ :=
  fun z ↦ (n : ℂ) ^ (2 * k - 1 : ℤ) * ∑ t ∈ hermiteTriples n,
    (t.2.2 : ℂ) ^ (-(2 * k : ℤ)) * f (UpperHalfPlane.ofComplex ((t.1 * (z : ℂ) + t.2.1) / t.2.2))


/-- Sum over the triples of Lemma 5.13, organised by the pair $(a, d)$. -/
theorem sum_hermiteTriples {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℕ × ℕ × ℕ → M) :
    ∑ t ∈ hermiteTriples n, F t =
      ∑ ad ∈ n.divisorsAntidiagonal, ∑ b ∈ Finset.range ad.2, F (ad.1, b, ad.2) := by
  rw [hermiteTriples, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun ad _ => ?_
    rw [Finset.sum_image]
    intro b _ b' _ h
    simpa using h
  · intro ad _ ad' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro t ht ht'
    simp only [Finset.mem_image, Finset.mem_range] at ht ht'
    obtain ⟨b, _, rfl⟩ := ht
    obtain ⟨b', _, h⟩ := ht'
    apply hne
    ext
    · exact (congrArg Prod.fst h).symm
    · exact (congrArg (fun x => x.2.2) h).symm

/-- $\sum_{b<d}e^{2\pi i b m/d} = d$ if $d \mid m$ and $0$ otherwise. -/
theorem sum_exp_roots {d : ℕ} (hd : 0 < d) (m : ℕ) :
    ∑ b ∈ Finset.range d, (Complex.exp (2 * Real.pi * Complex.I * (b / d))) ^ m =
      if d ∣ m then (d : ℂ) else 0 := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  set x : ℂ := Complex.exp (2 * Real.pi * Complex.I * (m / d)) with hx
  have h1 : ∀ b : ℕ, (Complex.exp (2 * Real.pi * Complex.I * (b / d))) ^ m = x ^ b := by
    intro b
    rw [hx, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    ring
  simp_rw [h1]
  split_ifs with hdm
  · obtain ⟨j, rfl⟩ := hdm
    have : x = 1 := by
      rw [hx, Complex.exp_eq_one_iff]
      refine ⟨j, ?_⟩
      push_cast
      field_simp
    simp [this]
  · have hx1 : x ≠ 1 := by
      intro h
      rw [hx, Complex.exp_eq_one_iff] at h
      obtain ⟨l, hl⟩ := h
      apply hdm
      have h2 : (m : ℂ) = l * d := by
        field_simp at hl
        rw [hl]; ring
      have h3 : (m : ℤ) = l * d := by exact_mod_cast h2
      have : (d : ℤ) ∣ (m : ℤ) := ⟨l, by rw [h3]; ring⟩
      exact_mod_cast this
    rw [geom_sum_eq hx1]
    have : x ^ d = 1 := by
      rw [hx, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
      refine ⟨m, ?_⟩
      field_simp
      simp
    rw [this]
    simp


/-- For $ad = n$: the contribution of the $d$ triples $(a, b, d)$ to $T(n)f(z)$, as a series in $q = e^{2\pi iz}$
(only the exponents divisible by $d$ survive the sum over $b$). -/
theorem hasSum_block (k : ℕ) (f : ModularForm 𝒮ℒ (2 * k)) (z : ℍ) {n a d : ℕ} (hn : 0 < n)
    (had : a * d = n) :
    HasSum (fun j : ℕ ↦ (a : ℂ) ^ (2 * k - 1 : ℤ) * (qExpansion 1 f).coeff (d * j) *
        (Function.Periodic.qParam 1 (z : ℂ)) ^ (a * j))
      (∑ b ∈ Finset.range d, (n : ℂ) ^ (2 * k - 1 : ℤ) * ((d : ℂ) ^ (-(2 * k : ℤ)) *
        f (UpperHalfPlane.ofComplex (((a : ℂ) * (z : ℂ) + b) / d)))) := by
  have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have him : ∀ b : ℕ, 0 < ((((a : ℂ) * (z : ℂ) + b) / d)).im := by
    intro b
    simp only [Complex.div_natCast_im, Complex.add_im, Complex.mul_im, Complex.natCast_re,
      Complex.natCast_im, zero_mul, add_zero, mul_zero]
    have := z.im_pos
    have h1 : (0 : ℝ) < a := by exact_mod_cast ha
    have h2 : (0 : ℝ) < d := by exact_mod_cast hd
    simp only [UpperHalfPlane.coe_im]
    positivity
  have hS : ∀ b ∈ Finset.range d, HasSum (fun m : ℕ ↦ (n : ℂ) ^ (2 * k - 1 : ℤ) * ((d : ℂ) ^ (-(2 * k : ℤ)) *
      ((qExpansion 1 f).coeff m * Complex.exp (2 * Real.pi * Complex.I * (((a : ℂ) * z + b) / d)) ^ m)))
      ((n : ℂ) ^ (2 * k - 1 : ℤ) * ((d : ℂ) ^ (-(2 * k : ℤ)) *
        f (UpperHalfPlane.ofComplex (((a : ℂ) * (z : ℂ) + b) / d)))) := by
    intro b _
    have h := ModularForm.hasSum_qExpansion (h := 1) (F := ModularForm 𝒮ℒ (2 * k)) (f := f) one_pos
      one_mem_strictPeriods_SL (UpperHalfPlane.ofComplex (((a : ℂ) * (z : ℂ) + b) / d))
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (him b)] at h ⊢
    simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one] at h
    exact (h.mul_left _).mul_left _
  have hT := hasSum_sum hS
  have hP : ∀ m : ℕ, ∑ b ∈ Finset.range d, (n : ℂ) ^ (2 * k - 1 : ℤ) * ((d : ℂ) ^ (-(2 * k : ℤ)) *
      ((qExpansion 1 f).coeff m * Complex.exp (2 * Real.pi * Complex.I * (((a : ℂ) * z + b) / d)) ^ m)) =
      if d ∣ m then (n : ℂ) ^ (2 * k - 1 : ℤ) * ((d : ℂ) ^ (-(2 * k : ℤ)) * ((qExpansion 1 f).coeff m *
        Complex.exp (2 * Real.pi * Complex.I * (a * z / d)) ^ m)) * d else 0 := by
    intro m
    have : ∀ b : ℕ, Complex.exp (2 * Real.pi * Complex.I * (((a : ℂ) * z + b) / d)) ^ m =
        Complex.exp (2 * Real.pi * Complex.I * (a * z / d)) ^ m *
          Complex.exp (2 * Real.pi * Complex.I * (b / d)) ^ m := by
      intro b
      rw [← mul_pow, ← Complex.exp_add]
      congr 2
      ring
    simp_rw [this]
    have h2 := sum_exp_roots hd m
    rw [show (∑ b ∈ Finset.range d, (n : ℂ) ^ (2 * k - 1 : ℤ) * ((d : ℂ) ^ (-(2 * k : ℤ)) *
        ((qExpansion 1 f).coeff m * (Complex.exp (2 * Real.pi * Complex.I * (a * z / d)) ^ m *
          Complex.exp (2 * Real.pi * Complex.I * (b / d)) ^ m)))) =
        (n : ℂ) ^ (2 * k - 1 : ℤ) * ((d : ℂ) ^ (-(2 * k : ℤ)) * ((qExpansion 1 f).coeff m *
        Complex.exp (2 * Real.pi * Complex.I * (a * z / d)) ^ m)) *
        ∑ b ∈ Finset.range d, Complex.exp (2 * Real.pi * Complex.I * (b / d)) ^ m by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring, h2]
    split_ifs <;> simp
  simp_rw [hP] at hT
  have hinj : Function.Injective (fun j : ℕ ↦ d * j) := fun x y h ↦ Nat.eq_of_mul_eq_mul_left hd h
  have hoff : ∀ x, x ∉ Set.range (fun j : ℕ ↦ d * j) → (if d ∣ x then (n : ℂ) ^ (2 * k - 1 : ℤ) *
      ((d : ℂ) ^ (-(2 * k : ℤ)) * ((qExpansion 1 f).coeff x *
        Complex.exp (2 * Real.pi * Complex.I * (a * z / d)) ^ x)) * d else 0) = 0 := by
    intro x hx
    rw [if_neg]
    rintro ⟨j, rfl⟩
    exact hx ⟨j, rfl⟩
  have hT2 := (hinj.hasSum_iff hoff).mpr hT
  refine hT2.congr_fun ?_
  intro j
  simp only [Function.comp_apply]
  rw [if_pos (dvd_mul_right d j)]
  have hA : Complex.exp (2 * Real.pi * Complex.I * (a * z / d)) ^ (d * j) =
      (Function.Periodic.qParam 1 (z : ℂ)) ^ (a * j) := by
    simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hz : (d : ℂ) ^ (2 * k - 1 : ℤ) * (d : ℂ) ^ (-(2 * k : ℤ)) * d = 1 := by
    rw [← zpow_add₀ hd']
    have : (2 * k - 1 : ℤ) + -(2 * k : ℤ) = -1 := by ring
    rw [this, _root_.zpow_neg_one, inv_mul_cancel₀ hd']
  rw [hA, ← had]
  push_cast
  rw [mul_zpow]
  generalize (d : ℂ) ^ (2 * k - 1 : ℤ) = X at hz ⊢
  generalize (d : ℂ) ^ (-(2 * k : ℤ)) = Y at hz ⊢
  generalize (a : ℂ) ^ (2 * k - 1 : ℤ) = Z
  linear_combination (-Z * (qExpansion 1 f).coeff (d * j) *
    (Function.Periodic.qParam 1 (z : ℂ)) ^ (a * j)) * hz


/-- The same contribution as a series in the exponents divisible by $a$ (coefficients of $T(n)f$). -/
theorem hasSum_block' (k : ℕ) (f : ModularForm 𝒮ℒ (2 * k)) (z : ℍ) {n a d : ℕ} (hn : 0 < n)
    (had : a * d = n) :
    HasSum (fun m : ℕ ↦ if a ∣ m then (a : ℂ) ^ (2 * k - 1 : ℤ) * (qExpansion 1 f).coeff (m * n / a ^ 2) *
        (Function.Periodic.qParam 1 (z : ℂ)) ^ m else 0)
      (∑ b ∈ Finset.range d, (n : ℂ) ^ (2 * k - 1 : ℤ) * ((d : ℂ) ^ (-(2 * k : ℤ)) *
        f (UpperHalfPlane.ofComplex (((a : ℂ) * (z : ℂ) + b) / d)))) := by
  have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have h := hasSum_block k f z hn had
  have hinj : Function.Injective (fun j : ℕ ↦ a * j) := fun x y h ↦ Nat.eq_of_mul_eq_mul_left ha h
  have hoff : ∀ x, x ∉ Set.range (fun j : ℕ ↦ a * j) → (if a ∣ x then (a : ℂ) ^ (2 * k - 1 : ℤ) *
      (qExpansion 1 f).coeff (x * n / a ^ 2) * (Function.Periodic.qParam 1 (z : ℂ)) ^ x else 0) = 0 := by
    intro x hx
    rw [if_neg]
    rintro ⟨j, rfl⟩
    exact hx ⟨j, rfl⟩
  refine ((hinj.hasSum_iff hoff).mp ?_)
  convert h using 2 with j
  simp only [Function.comp_apply]
  rw [if_pos (dvd_mul_right a j)]
  have : a * j * n / a ^ 2 = d * j := by
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    rw [← had]; ring
  rw [this]

/-- **Milne, p. 73**: on modular forms of weight $2k$, Milne's operator is `heckeT`:
$T(n)f(z) = n^{2k-1}\sum d^{-2k} f\big(\frac{az+b}{d}\big)$. -/
@[kb "milne2017mf" "Section 5, definition of T(n) on modular forms (pdf p. 73)"]
theorem heckeT_apply (k : ℕ) {n : ℕ} (hn : 0 < n) (f : ModularForm 𝒮ℒ (2 * k)) :
    ⇑(heckeT (2 * k) n f) = milneHeckeSum k n f := by
  funext z
  have hn' : n ≠ 0 := hn.ne'
  have hg := ModularForm.hasSum_qExpansion (h := 1) (F := ModularForm 𝒮ℒ (2 * k)) (f := heckeT (2 * k) n f)
    one_pos one_mem_strictPeriods_SL z
  have hQ := hasSum_sum (s := n.divisorsAntidiagonal) (fun ad had ↦
    hasSum_block' k f z hn (Nat.mem_divisorsAntidiagonal.mp had).1)
  have hcoef : ∀ m : ℕ, (qExpansion 1 (heckeT (2 * k) n f)).coeff m *
      (Function.Periodic.qParam 1 (z : ℂ)) ^ m = ∑ ad ∈ n.divisorsAntidiagonal,
        (if ad.1 ∣ m then (ad.1 : ℂ) ^ (2 * k - 1 : ℤ) * (qExpansion 1 f).coeff (m * n / ad.1 ^ 2) *
          (Function.Periodic.qParam 1 (z : ℂ)) ^ m else 0) := by
    intro m
    rw [qExpansion_coeff_heckeT k hn', Nat.sum_divisorsAntidiagonal (fun a _ ↦
      if a ∣ m then (a : ℂ) ^ (2 * k - 1 : ℤ) * (qExpansion 1 f).coeff (m * n / a ^ 2) *
          (Function.Periodic.qParam 1 (z : ℂ)) ^ m else 0), Finset.sum_mul]
    have hdiv : (Nat.gcd m n).divisors = n.divisors.filter (· ∣ m) := by
      ext a
      simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
      have : Nat.gcd m n ≠ 0 := Nat.gcd_ne_zero_right hn'
      tauto
    rw [hdiv, Finset.sum_filter]
  simp_rw [← hcoef] at hQ
  have hz := hg.unique hQ
  show (heckeT (2 * k) n f) z = _
  rw [hz, milneHeckeSum, sum_hermiteTriples, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ad had ↦ ?_
  rw [Finset.mul_sum]

/-- **Milne, p. 73**: if $f(z) = F(\Lambda(z, 1))$ with $F$ of weight $2k$ on lattices, then
$T(n)f(z) = n^{2k-1}(T(n)F)(\Lambda(z,1))$, where $\Lambda(z,1) = \mathbb Zz + \mathbb Z$. -/
@[kb "milne2017mf" "Section 5, T(n) f via functions on lattices (pdf p. 73)"]
theorem milneHeckeSum_latticeFun {k : ℕ} {F : Submodule ℤ ℂ → ℂ}
    (hF : ∀ (c : ℂˣ) (L : PeriodPair), F (scaleC c L.lattice) = (c : ℂ) ^ (-(2 * k : ℤ)) * F L.lattice)
    {n : ℕ} (hn : 0 < n) (z : ℍ) :
    milneHeckeSum k n (fun w ↦ F (Submodule.span ℤ {(w : ℂ), 1})) z =
      (n : ℂ) ^ (2 * k - 1 : ℤ) * latticeOpFun (latticeT n) F (Submodule.span ℤ {(z : ℂ), 1}) := by
  have hli : LinearIndependent ℤ ![(z : ℂ), 1] := by
    rw [LinearIndependent.pair_iff]
    intro s u h
    have h1 := congrArg Complex.im h
    simp only [zsmul_eq_mul, Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      UpperHalfPlane.coe_im, zero_mul, add_zero, Complex.one_im, mul_zero, Complex.zero_im] at h1
    have hs : s = 0 := by
      have := z.im_pos
      have : (s : ℝ) = 0 := by
        rcases mul_eq_zero.mp h1 with h | h
        · exact h
        · exact absurd h this.ne'
      exact_mod_cast this
    subst hs
    simpa using h
  have hT : latticeT n (Finsupp.single (Submodule.span ℤ {(z : ℂ), 1}) (1 : ℤ)) =
      ∑ t ∈ hermiteTriples n, Finsupp.single (Submodule.span ℤ {(t.1 : ℤ) • (z : ℂ) + (t.2.1 : ℤ) • 1,
        (t.2.2 : ℤ) • (1 : ℂ)}) (1 : ℤ) := by
    have hb := bijOn_hermiteTriples_subOfIndex hli hn
    unfold latticeT
    rw [Finsupp.linearCombination_single, one_smul]
    rw [← finsum_mem_eq_of_bijOn _ hb (fun x _ ↦ rfl), finsum_mem_coe_finset]
  unfold latticeOpFun
  rw [hT, ← Finsupp.sum_finsetSum_index (by simp) (by intros; push_cast; ring), milneHeckeSum,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  rw [Finsupp.sum_single_index (by simp)]
  obtain ⟨a, b, d⟩ := t
  obtain ⟨h1, h2, h3⟩ := mem_hermiteTriples.mp ht
  simp only at h1 h2
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have him : 0 < (((a : ℂ) * (z : ℂ) + b) / d).im := by
    simp only [Complex.div_natCast_im, Complex.add_im, Complex.mul_im, Complex.natCast_re,
      Complex.natCast_im, zero_mul, add_zero]
    have := z.im_pos
    have h1 : (0 : ℝ) < a := by exact_mod_cast ha
    have h2 : (0 : ℝ) < d := by exact_mod_cast hd
    simp only [UpperHalfPlane.coe_im]
    positivity
  have hind : LinearIndependent ℝ ![((a : ℂ) * (z : ℂ) + b) / d, 1] := by
    rw [LinearIndependent.pair_iff]
    intro s u h
    have h1 := congrArg Complex.im h
    simp only [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Complex.one_im, mul_zero, Complex.zero_im] at h1
    have hs : s = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h him.ne'
    subst hs
    simpa using h
  let L : PeriodPair := ⟨_, 1, hind⟩
  have hc := hF (Units.mk0 (d : ℂ) hd') L
  have hlat : scaleC ((Units.mk0 (d : ℂ) hd' : ℂˣ) : ℂ) L.lattice =
      Submodule.span ℤ {(a : ℤ) • (z : ℂ) + (b : ℤ) • (1 : ℂ), (d : ℤ) • (1 : ℂ)} := by
    simp only [scaleC, PeriodPair.lattice, L]
    rw [Submodule.map_span, Set.image_pair]
    congr 2
    · simp only [LinearMap.mulLeft_apply, Units.val_mk0, zsmul_eq_mul, Int.cast_natCast, mul_one]
      field_simp
    · simp
  rw [hlat] at hc
  rw [hc, UpperHalfPlane.ofComplex_apply_of_im_pos him]
  simp only [Units.val_mk0, PeriodPair.lattice, L, UpperHalfPlane.coe_mk, Complex.ofReal_one]
  push_cast
  ring

/-! ### From weakly modular functions to functions on lattices -/

/-- An oriented basis ($\mathrm{Im}(\omega_1/\omega_2) > 0$) has $\omega_2 \ne 0$. -/
theorem ne_zero_of_oriented {ω₁ ω₂ : ℂ} (h : 0 < (ω₁ / ω₂).im) : ω₂ ≠ 0 := by
  rintro rfl
  simp at h

/-- An oriented basis is `ℤ`-independent. -/
theorem coeffs_of_oriented {ω₁ ω₂ : ℂ} (h : 0 < (ω₁ / ω₂).im) {s t : ℤ}
    (hst : (s : ℂ) * ω₁ + t * ω₂ = 0) : s = 0 ∧ t = 0 := by
  have h2 := ne_zero_of_oriented h
  have h3 : (s : ℂ) * (ω₁ / ω₂) + t = 0 := by
    field_simp
    linear_combination hst
  have h4 := congrArg Complex.im h3
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero,
    Complex.zero_im] at h4
  have hs : s = 0 := by
    have : (s : ℝ) = 0 := by
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact h5
      · exact absurd h5 h.ne'
    exact_mod_cast this
  subst hs
  refine ⟨rfl, ?_⟩
  simp only [Int.cast_zero, zero_mul, zero_add, mul_eq_zero] at hst
  rcases hst with h5 | h5
  · exact_mod_cast h5
  · exact absurd h5 h2

/-- Two oriented bases of the same lattice give the same value $\omega_2^{-2k} f(\omega_1/\omega_2)$, for $f$ weakly
modular of weight $2k$. -/
theorem orient_wd {k : ℕ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[(2 * k : ℤ)] γ = f)
    {ω₁ ω₂ ω₁' ω₂' : ℂ} (h : 0 < (ω₁ / ω₂).im) (h' : 0 < (ω₁' / ω₂').im)
    (hs : Submodule.span ℤ {ω₁, ω₂} = Submodule.span ℤ {ω₁', ω₂'}) :
    ω₂' ^ (-(2 * k : ℤ)) * f (UpperHalfPlane.ofComplex (ω₁' / ω₂')) =
      ω₂ ^ (-(2 * k : ℤ)) * f (UpperHalfPlane.ofComplex (ω₁ / ω₂)) := by
  have hm1 : ω₁' ∈ Submodule.span ℤ {ω₁, ω₂} := hs ▸ Submodule.subset_span (by simp)
  have hm2 : ω₂' ∈ Submodule.span ℤ {ω₁, ω₂} := hs ▸ Submodule.subset_span (by simp)
  have hm3 : ω₁ ∈ Submodule.span ℤ {ω₁', ω₂'} := hs ▸ Submodule.subset_span (by simp)
  have hm4 : ω₂ ∈ Submodule.span ℤ {ω₁', ω₂'} := hs ▸ Submodule.subset_span (by simp)
  obtain ⟨a, b, e1⟩ := Submodule.mem_span_pair.mp hm1
  obtain ⟨c, d, e2⟩ := Submodule.mem_span_pair.mp hm2
  obtain ⟨a', b', e3⟩ := Submodule.mem_span_pair.mp hm3
  obtain ⟨c', d', e4⟩ := Submodule.mem_span_pair.mp hm4
  simp only [zsmul_eq_mul] at e1 e2 e3 e4
  have h2 := ne_zero_of_oriented h
  have h2' := ne_zero_of_oriented h'
  have k11 := coeffs_of_oriented h (s := a' * a + b' * c - 1) (t := a' * b + b' * d) (by
    push_cast; linear_combination e3 + a' * e1 + b' * e2)
  have k22 := coeffs_of_oriented h (s := c' * a + d' * c) (t := c' * b + d' * d - 1) (by
    push_cast; linear_combination e4 + c' * e1 + d' * e2)
  have hdet : (a * d - b * c) * (a' * d' - b' * c') = 1 := by
    have : (a * d - b * c) * (a' * d' - b' * c') =
        (a' * a + b' * c) * (c' * b + d' * d) - (a' * b + b' * d) * (c' * a + d' * c) := by ring
    rw [this]
    have u1 : a' * a + b' * c = 1 := by linarith [k11.1]
    have u2 : a' * b + b' * d = 0 := k11.2
    have u3 : c' * a + d' * c = 0 := k22.1
    have u4 : c' * b + d' * d = 1 := by linarith [k22.2]
    rw [u1, u2, u3, u4]; norm_num
  set τ : ℂ := ω₁ / ω₂ with hτ
  have hden : (c : ℂ) * τ + d = ω₂' / ω₂ := by
    rw [hτ, ← e2]; field_simp
  have hnum : (a : ℂ) * τ + b = ω₁' / ω₂ := by
    rw [hτ, ← e1]; field_simp
  have hrat : ω₁' / ω₂' = ((a : ℂ) * τ + b) / ((c : ℂ) * τ + d) := by
    rw [hden, hnum]; field_simp
  -- the determinant is positive
  have hpos : 0 < a * d - b * c := by
    have hne : (c : ℂ) * τ + d ≠ 0 := by
      rw [hden]; exact div_ne_zero h2' h2
    have hns : 0 < Complex.normSq ((c : ℂ) * τ + d) := Complex.normSq_pos.mpr hne
    have him : (ω₁' / ω₂').im = ((a * d - b * c : ℤ) : ℝ) * τ.im / Complex.normSq ((c : ℂ) * τ + d) := by
      rw [hrat, Complex.div_im]
      simp only [Complex.add_im, Complex.mul_im, Complex.add_re, Complex.mul_re, Complex.intCast_re,
        Complex.intCast_im, zero_mul, add_zero, zero_add, mul_zero, sub_zero]
      push_cast
      field_simp
      ring
    rw [him] at h'
    have : 0 < ((a * d - b * c : ℤ) : ℝ) * τ.im := by
      by_contra hcon
      push_neg at hcon
      have := div_nonpos_of_nonpos_of_nonneg hcon hns.le
      linarith
    have h5 : 0 < ((a * d - b * c : ℤ) : ℝ) := by
      by_contra hcon
      push_neg at hcon
      nlinarith [mul_nonneg (neg_nonneg.mpr hcon) h.le]
    exact_mod_cast h5
  have hdet1 : a * d - b * c = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h5 | h5
    · exact h5
    · omega
  let γ : SL(2, ℤ) := ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact hdet1⟩
  have hinv := (ModularForm.slash_action_eq'_iff (2 * k : ℤ) f γ (UpperHalfPlane.ofComplex τ)).mp
    (congrFun (hf γ) _)
  have hτim : 0 < τ.im := h
  have hco : ((UpperHalfPlane.ofComplex τ : ℍ) : ℂ) = τ := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hτim]
  have hsm : γ • UpperHalfPlane.ofComplex τ = UpperHalfPlane.ofComplex (ω₁' / ω₂') := by
    ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.ofComplex_apply_of_im_pos h', hco]
    simp [γ, hrat]
  have hc : ((γ 1 0 : ℤ) : ℂ) * ((UpperHalfPlane.ofComplex τ : ℍ) : ℂ) + ((γ 1 1 : ℤ) : ℂ) = ω₂' / ω₂ := by
    rw [hco]; exact hden
  rw [← hsm, hinv, hc, div_zpow, _root_.zpow_neg, _root_.zpow_neg]
  field_simp

/-- $\{w, 1\}$ is `ℝ`-linearly independent for $\mathrm{Im}\,w > 0$. -/
theorem linearIndependent_real_pair_one {w : ℂ} (hw : 0 < w.im) : LinearIndependent ℝ ![w, (1 : ℂ)] := by
  rw [LinearIndependent.pair_iff]
  intro s u h
  have h1 := congrArg Complex.im h
  simp only [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.one_im, mul_zero, Complex.zero_im] at h1
  have hs : s = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hw.ne'
  subst hs
  simpa using h

/-- The imaginary part of $\omega_1/\omega_2$ is nonzero for a period pair. -/
theorem im_ne_zero_of_indep (L : PeriodPair) : (L.ω₁ / L.ω₂).im ≠ 0 := by
  intro h
  have hpair := LinearIndependent.pair_iff.mp L.indep
  have h2 : L.ω₂ ≠ 0 := by
    intro h0
    have := hpair 0 1 (by simp [h0])
    simp at this
  have hr : L.ω₁ / L.ω₂ = (((L.ω₁ / L.ω₂).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h])
  have := hpair 1 (-(L.ω₁ / L.ω₂).re) (by
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    rw [← hr]
    field_simp
    ring)
  simp at this

open Classical in
/-- The function on lattices attached to $f$: $F(\mathbb Z\omega_1 + \mathbb Z\omega_2) = \omega_2^{-2k}f(\omega_1/\omega_2)$
for $\mathrm{Im}(\omega_1/\omega_2) > 0$ (junk value $0$ on other subgroups). -/
noncomputable def latF (k : ℕ) (f : ℍ → ℂ) (Λ : Submodule ℤ ℂ) : ℂ :=
  if h : ∃ p : ℂ × ℂ, 0 < (p.1 / p.2).im ∧ Submodule.span ℤ {p.1, p.2} = Λ then
    h.choose.2 ^ (-(2 * k : ℤ)) * f (UpperHalfPlane.ofComplex (h.choose.1 / h.choose.2))
  else 0

/-- The value of `latF` on an oriented basis. -/
theorem latF_span {k : ℕ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[(2 * k : ℤ)] γ = f) {ω₁ ω₂ : ℂ}
    (h : 0 < (ω₁ / ω₂).im) :
    latF k f (Submodule.span ℤ {ω₁, ω₂}) = ω₂ ^ (-(2 * k : ℤ)) * f (UpperHalfPlane.ofComplex (ω₁ / ω₂)) := by
  have hex : ∃ p : ℂ × ℂ, 0 < (p.1 / p.2).im ∧ Submodule.span ℤ {p.1, p.2} = Submodule.span ℤ {ω₁, ω₂} :=
    ⟨(ω₁, ω₂), h, rfl⟩
  rw [latF, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  exact orient_wd hf h h1 h2.symm

/-- `latF` has weight $2k$. -/
theorem latF_weight {k : ℕ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[(2 * k : ℤ)] γ = f) (c : ℂˣ)
    (L : PeriodPair) :
    latF k f (scaleC c L.lattice) = (c : ℂ) ^ (-(2 * k : ℤ)) * latF k f L.lattice := by
  have key : ∀ ω₁ ω₂ : ℂ, 0 < (ω₁ / ω₂).im →
      latF k f (scaleC c (Submodule.span ℤ {ω₁, ω₂})) =
        (c : ℂ) ^ (-(2 * k : ℤ)) * latF k f (Submodule.span ℤ {ω₁, ω₂}) := by
    intro ω₁ ω₂ h
    have hs : scaleC c (Submodule.span ℤ {ω₁, ω₂}) = Submodule.span ℤ {(c : ℂ) * ω₁, (c : ℂ) * ω₂} := by
      simp [scaleC, Submodule.map_span, Set.image_pair]
    have hc : 0 < ((c : ℂ) * ω₁ / ((c : ℂ) * ω₂)).im := by
      rwa [mul_div_mul_left _ _ c.ne_zero]
    rw [hs, latF_span hf hc, latF_span hf h, mul_div_mul_left _ _ c.ne_zero, mul_zpow]
    ring
  rcases lt_or_gt_of_ne (im_ne_zero_of_indep L) with h | h
  · have hne : L.ω₁ / L.ω₂ ≠ 0 := fun h0 ↦ by simp [h0] at h
    have h' : 0 < (L.ω₂ / L.ω₁).im := by
      rw [← inv_div, Complex.inv_im]
      exact div_pos (neg_pos.mpr h) (Complex.normSq_pos.mpr hne)
    have : L.lattice = Submodule.span ℤ {L.ω₂, L.ω₁} := by
      simp [PeriodPair.lattice, Set.pair_comm]
    rw [this]
    exact key _ _ h'
  · exact key _ _ h

/-- `latF` restricted to $\Lambda(w, 1)$ recovers $f$. -/
theorem latF_span_one {k : ℕ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[(2 * k : ℤ)] γ = f) (w : ℍ) :
    latF k f (Submodule.span ℤ {(w : ℂ), 1}) = f w := by
  rw [latF_span hf (by simpa using w.im_pos)]
  simp

/-- `latticeOpFun` is linear in the function. -/
theorem latticeOpFun_const_mul (T : (Submodule ℤ ℂ →₀ ℤ) →ₗ[ℤ] (Submodule ℤ ℂ →₀ ℤ)) (c : ℂ)
    (G : Submodule ℤ ℂ → ℂ) (Λ : Submodule ℤ ℂ) :
    latticeOpFun T (fun Λ' ↦ c * G Λ') Λ = c * latticeOpFun T G Λ := by
  unfold latticeOpFun
  rw [Finsupp.mul_sum]
  exact Finsupp.sum_congr fun Λ' _ ↦ by ring

/-- The function on lattices $n^{2k-1}(T(n)\cdot F)$ attached to $T(n)f$ (Milne p. 73). -/
noncomputable def latFn (k : ℕ) (f : ℍ → ℂ) (N : ℕ) (Λ : Submodule ℤ ℂ) : ℂ :=
  (N : ℂ) ^ (2 * k - 1 : ℤ) * latticeOpFun (latticeT N) (latF k f) Λ

/-- $T(N)f(z) = N^{2k-1}(T(N)F)(\Lambda(z,1))$ for the lattice function $F$ of $f$. -/
theorem milneHeckeSum_eq_latFn {k : ℕ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[(2 * k : ℤ)] γ = f) {N : ℕ}
    (hN : 0 < N) (z : ℍ) :
    milneHeckeSum k N f z = latFn k f N (Submodule.span ℤ {(z : ℂ), 1}) := by
  have := milneHeckeSum_latticeFun (k := k) (F := latF k f) (latF_weight hf) hN z
  have hfun : (fun w : ℍ ↦ latF k f (Submodule.span ℤ {(w : ℂ), 1})) = f := funext (latF_span_one hf)
  rw [hfun] at this
  exact this

/-- `latFn` has weight $2k$ (Milne, Proposition 5.12). -/
theorem latFn_weight {k : ℕ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[(2 * k : ℤ)] γ = f) {N : ℕ}
    (hN : 0 < N) (c : ℂˣ) (L : PeriodPair) :
    latFn k f N (scaleC c L.lattice) = (c : ℂ) ^ (-(2 * k : ℤ)) * latFn k f N L.lattice := by
  unfold latFn
  rw [latticeOpFun_latticeT_isWeight (latF_weight hf) hN c L, mul_left_comm]

/-- Composition formula for the explicit Hecke operators on weakly modular functions. -/
theorem milneHeckeSum_comp {k : ℕ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[(2 * k : ℤ)] γ = f) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (z : ℍ) :
    milneHeckeSum k m (milneHeckeSum k n f) z =
      ∑ d ∈ (Nat.gcd m n).divisors, (d : ℂ) ^ (2 * k - 1 : ℤ) * milneHeckeSum k (m * n / d ^ 2) f z := by
  have e1 : milneHeckeSum k n f = fun w : ℍ ↦ latFn k f n (Submodule.span ℤ {(w : ℂ), 1}) :=
    funext fun w ↦ milneHeckeSum_eq_latFn hf hn w
  rw [e1, milneHeckeSum_latticeFun (k := k) (F := latFn k f n) (latFn_weight hf hn) hm z]
  have hzim : 0 < (z : ℂ).im := by simpa using z.im_pos
  let L : PeriodPair := ⟨(z : ℂ), 1, linearIndependent_real_pair_one hzim⟩
  have hL : L.lattice = Submodule.span ℤ {(z : ℂ), 1} := rfl
  have h52 := latticeOpFun_latticeT_mul (latF_weight hf) hm hn L
  have hlin : latticeOpFun (latticeT m) (latFn k f n) L.lattice =
      (n : ℂ) ^ (2 * k - 1 : ℤ) * latticeOpFun (latticeT m) (latticeOpFun (latticeT n) (latF k f)) L.lattice :=
    latticeOpFun_const_mul _ _ _ _
  rw [← hL, hlin, h52, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hd' := Nat.mem_divisors.mp hd
  have hdm : d ∣ m := hd'.1.trans (Nat.gcd_dvd_left m n)
  have hdn : d ∣ n := hd'.1.trans (Nat.gcd_dvd_right m n)
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdm hm
  have hd2 : d ^ 2 ∣ m * n := by
    rw [pow_two]; exact mul_dvd_mul hdm hdn
  have hNpos : 0 < m * n / d ^ 2 := Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hm hn) hd2) (by positivity)
  have hN : (m * n / d ^ 2) * d ^ 2 = m * n := Nat.div_mul_cancel hd2
  rw [milneHeckeSum_eq_latFn hf hNpos, ← hL]
  unfold latFn
  have hD : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hmn : (m : ℂ) ^ (2 * k - 1 : ℤ) * (n : ℂ) ^ (2 * k - 1 : ℤ) =
      ((m * n / d ^ 2 : ℕ) : ℂ) ^ (2 * k - 1 : ℤ) * ((d : ℂ) ^ (2 * k - 1 : ℤ)) ^ 2 := by
    have hsq : ∀ x : ℂ, (x ^ 2) ^ (2 * k - 1 : ℤ) = (x ^ (2 * k - 1 : ℤ)) ^ 2 := fun x ↦ by
      rw [← zpow_natCast x 2, ← _root_.zpow_mul, ← zpow_natCast (x ^ (2 * k - 1 : ℤ)) 2, ← _root_.zpow_mul, mul_comm]
    have hc : (m : ℂ) * n = ((m * n / d ^ 2 : ℕ) : ℂ) * (d : ℂ) ^ 2 := by exact_mod_cast hN.symm
    rw [← mul_zpow, hc, mul_zpow, hsq]
  have hinv : (d : ℂ) ^ (1 - 2 * k : ℤ) * (d : ℂ) ^ (2 * k - 1 : ℤ) = 1 := by
    rw [← zpow_add₀ hD]; simp
  have hs : (d : ℂ) ^ (2 * k - 1 : ℤ) ≠ 0 := zpow_ne_zero _ hD
  generalize (d : ℂ) ^ (2 * k - 1 : ℤ) = X at hmn hinv hs ⊢
  generalize (d : ℂ) ^ (1 - 2 * k : ℤ) = Y at hmn hinv ⊢
  generalize ((m * n / d ^ 2 : ℕ) : ℂ) ^ (2 * k - 1 : ℤ) = Z at hmn ⊢
  generalize (m : ℂ) ^ (2 * k - 1 : ℤ) = M at hmn ⊢
  generalize (n : ℂ) ^ (2 * k - 1 : ℤ) = N at hmn ⊢
  generalize latticeOpFun (latticeT (m * n / d ^ 2)) (latF k f) L.lattice = V
  linear_combination (V * Y) * hmn + (V * Z * X) * hinv

/-- **Milne, Proposition 5.16(a)**, first part: if $f$ is weakly modular of weight $2k$ for $\Gamma(1)$ then so is
$T(n)f$. Here "weakly modular" is only the transformation law $f \mid_{2k} \gamma = f$; Milne also asks $f$ to be
meromorphic, which is not used. -/
@[kb "milne2017mf" "Section 5, Proposition 5.16(a) (pdf p. 73)"]
theorem milneHeckeSum_slash_invariant {k : ℕ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[(2 * k : ℤ)] γ = f)
    {n : ℕ} (hn : 0 < n) (γ : SL(2, ℤ)) : milneHeckeSum k n f ∣[(2 * k : ℤ)] γ = milneHeckeSum k n f := by
  funext w
  rw [ModularForm.SL_slash_apply, milneHeckeSum_eq_latFn hf hn, milneHeckeSum_eq_latFn hf hn]
  have hc : denom (γ : GL (Fin 2) ℝ) w ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have hcC : denom (γ : GL (Fin 2) ℝ) w = ((γ 1 0 : ℤ) : ℂ) * w + ((γ 1 1 : ℤ) : ℂ) := by
    simp [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  have hdetC : ((γ 0 0 : ℤ) : ℂ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by exact_mod_cast hdet
  have hgw : ((γ • w : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * w + ((γ 0 1 : ℤ) : ℂ)) / denom (γ : GL (Fin 2) ℝ) w := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, hcC]
    simp
  have hzim : 0 < ((γ • w : ℍ) : ℂ).im := by simpa using (γ • w).im_pos
  let L : PeriodPair := ⟨((γ • w : ℍ) : ℂ), 1, linearIndependent_real_pair_one hzim⟩
  have hspan : scaleC (Units.mk0 _ hc : ℂˣ) L.lattice = Submodule.span ℤ {(w : ℂ), 1} := by
    have h1 : scaleC (Units.mk0 _ hc : ℂˣ) L.lattice =
        Submodule.span ℤ {((γ 0 0 : ℤ) : ℂ) * w + ((γ 0 1 : ℤ) : ℂ), ((γ 1 0 : ℤ) : ℂ) * w + ((γ 1 1 : ℤ) : ℂ)} := by
      simp only [scaleC, PeriodPair.lattice, L, Submodule.map_span, Set.image_pair, LinearMap.mulLeft_apply,
        Units.val_mk0]
      rw [hgw, ← hcC]
      field_simp
    rw [h1]
    apply le_antisymm
    · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨Submodule.mem_span_pair.mpr ⟨γ 0 0, γ 0 1, by simp⟩,
        Submodule.mem_span_pair.mpr ⟨γ 1 0, γ 1 1, by simp⟩⟩
    · rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨Submodule.mem_span_pair.mpr ⟨γ 1 1, -(γ 0 1), ?_⟩, Submodule.mem_span_pair.mpr ⟨-(γ 1 0), γ 0 0, ?_⟩⟩
      · simp only [zsmul_eq_mul, Int.cast_neg]
        linear_combination (w : ℂ) * hdetC
      · simp only [zsmul_eq_mul, Int.cast_neg]
        linear_combination hdetC
  have hw := latFn_weight hf hn (Units.mk0 _ hc) L
  rw [hspan] at hw
  rw [hw]
  simp only [Units.val_mk0]
  have : L.lattice = Submodule.span ℤ {((γ • w : ℍ) : ℂ), 1} := rfl
  rw [this]
  exact mul_comm _ _

/-- **Milne, Proposition 5.16(a)(i)** for weakly modular $f$: $T(m)T(n)f = T(mn)f$ for coprime $m, n \ge 1$. -/
@[kb "milne2017mf" "Section 5, Proposition 5.16(a)(i) (pdf p. 73)"]
theorem milneHeckeSum_mul_of_coprime {k : ℕ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[(2 * k : ℤ)] γ = f)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) :
    milneHeckeSum k m (milneHeckeSum k n f) = milneHeckeSum k (m * n) f := by
  funext z
  rw [milneHeckeSum_comp hf hm hn z, Nat.Coprime.gcd_eq_one hmn]
  simp

/-- **Milne, Proposition 5.16(a)(ii)** for weakly modular $f$:
$T(p)T(p^n)f = T(p^{n+1})f + p^{2k-1}T(p^{n-1})f$ for $p$ prime and $n \ge 1$. -/
@[kb "milne2017mf" "Section 5, Proposition 5.16(a)(ii) (pdf p. 73)"]
theorem milneHeckeSum_prime_mul_prime_pow {k : ℕ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[(2 * k : ℤ)] γ = f)
    {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 1 ≤ n) :
    milneHeckeSum k p (milneHeckeSum k (p ^ n) f) =
      milneHeckeSum k (p ^ (n + 1)) f + (p : ℂ) ^ (2 * k - 1 : ℤ) • milneHeckeSum k (p ^ (n - 1)) f := by
  funext z
  have hp0 := hp.pos
  have hpn : 0 < p ^ n := pow_pos hp0 n
  rw [milneHeckeSum_comp hf hp0 hpn z, Nat.gcd_eq_left (dvd_pow_self p (by omega)), Nat.Prime.divisors hp,
    Finset.sum_pair hp.one_lt.ne]
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  have h1 : p * p ^ (r + 1) / 1 ^ 2 = p ^ (r + 1 + 1) := by
    rw [one_pow, Nat.div_one, pow_succ' p (r + 1)]
  have h2 : p * p ^ (r + 1) / p ^ 2 = p ^ (r + 1 - 1) := by
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    rw [Nat.add_sub_cancel]; ring
  rw [h1, h2]
  simp

/-- **Milne's slash operator** (p. 75): $f|_k\alpha(z) = (\det\alpha)^k(cz+d)^{-2k}f\big(\frac{az+b}{cz+d}\big)$, for
$\alpha \in \mathrm{GL}_2(\mathbb R)^+$ (the value for $\det\alpha < 0$ is not used). -/
@[kb "milne2017mf" "Section 5, the slash operator f|_k α (pdf p. 75)"]
noncomputable def milneSlash (k : ℕ) (α : GL (Fin 2) ℝ) (f : ℍ → ℂ) : ℍ → ℂ :=
  fun z ↦ ((α.det.val : ℝ) : ℂ) ^ k * (denom α z) ^ (-(2 * k : ℤ)) * f (α • z)

/-- Mathlib's `σ` is the identity on matrices of positive determinant. -/
theorem sigma_apply_of_pos {α : GL (Fin 2) ℝ} (hα : 0 < α.det.val) (w : ℂ) : UpperHalfPlane.σ α w = w := by
  have h : 0 < (α : Matrix (Fin 2) (Fin 2) ℝ).det := hα
  simp [UpperHalfPlane.σ, h]

/-- Milne's slash operator and Mathlib's: $f|_k\alpha = (\det\alpha)^{1-k}\,(f \mid_{2k}\alpha)$ for
$\det\alpha > 0$. -/
@[kb "milne2017mf" "Section 5, the slash operator f|_k α (pdf p. 75)"]
theorem milneSlash_eq (k : ℕ) {α : GL (Fin 2) ℝ} (hα : 0 < α.det.val) (f : ℍ → ℂ) :
    milneSlash k α f = ((α.det.val : ℝ) : ℂ) ^ (1 - k : ℤ) • (f ∣[(2 * k : ℤ)] α) := by
  funext z
  have hd : ((α.det.val : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  simp only [milneSlash, Pi.smul_apply, ModularForm.slash_apply, sigma_apply_of_pos hα, smul_eq_mul,
    abs_of_pos hα]
  have : ((α.det.val : ℝ) : ℂ) ^ k = ((α.det.val : ℝ) : ℂ) ^ (1 - k : ℤ) *
      ((α.det.val : ℝ) : ℂ) ^ ((2 * k : ℤ) - 1) := by
    rw [← zpow_add₀ hd, ← zpow_natCast]; congr 1; push_cast; ring
  rw [this]
  ring

/-- Milne, p. 75: the centre of $\mathrm{GL}_2(\mathbb R)^+$ acts trivially, $f|_k\begin{pmatrix} a & 0 \\ 0 & a
\end{pmatrix} = f$ for $a > 0$. -/
@[kb "milne2017mf" "Section 5, the centre acts trivially (pdf p. 75)"]
theorem milneSlash_scalar (k : ℕ) {a : ℝ} (ha : 0 < a) (f : ℍ → ℂ) :
    milneSlash k (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.scalar (Fin 2) a)
      (by simp [Matrix.det_fin_two]; positivity)) f = f := by
  funext z
  have hd : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set M := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.scalar (Fin 2) a)
      (by simp [Matrix.det_fin_two]; positivity) with hM
  have hdet : (M.det.val : ℝ) = a ^ 2 := by
    simp [hM, Matrix.det_fin_two]
  have hpos : 0 < M.det.val := by rw [hdet]; positivity
  have hsm : M • z = z := by
    ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hpos]
    simp [hM, UpperHalfPlane.num, UpperHalfPlane.denom, hd]
  have hden : denom M z = (a : ℂ) := by
    simp [hM, UpperHalfPlane.denom]
  rw [milneSlash, hsm, hden, hdet]
  push_cast
  rw [← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ hd]
  rw [show ((2 : ℕ) : ℤ) * k + -(2 * k : ℤ) = 0 by push_cast; ring]
  simp

/-- The integer matrix $A$ as an element of $\mathrm{GL}_2(\mathbb R)$ (junk value $1$ if $\det A = 0$). -/
noncomputable def intMatGL (A : Matrix (Fin 2) (Fin 2) ℤ) : GL (Fin 2) ℝ :=
  if h : (A.map (Int.cast : ℤ → ℝ)).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero _ h else 1

/-- The real matrix underlying `intMatGL A` for $\det A \ne 0$. -/
theorem intMatGL_coe {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) :
    ((intMatGL A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = A.map (Int.cast : ℤ → ℝ) := by
  have h' : (A.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    have : (A.map (Int.cast : ℤ → ℝ)).det = (A.det : ℝ) := by
      simp [Matrix.det_fin_two]
    rw [this]; exact_mod_cast h
  rw [intMatGL, dif_pos h']
  rfl

/-- The determinant of `intMatGL A`. -/
theorem intMatGL_det {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) :
    (intMatGL A).det.val = (A.det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, intMatGL_coe h]
  simp [Matrix.det_fin_two]

/-- `intMatGL` is multiplicative for left multiplication by $\mathrm{SL}_2(\mathbb Z)$. -/
theorem intMatGL_SL_mul (γ : SL(2, ℤ)) {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) :
    intMatGL ((γ : Matrix (Fin 2) (Fin 2) ℤ) * A) = Matrix.SpecialLinearGroup.mapGL ℝ γ * intMatGL A := by
  have h2 : ((γ : Matrix (Fin 2) (Fin 2) ℤ) * A).det ≠ 0 := by
    rw [Matrix.det_mul, γ.det_coe, one_mul]; exact h
  apply Units.ext
  rw [Units.val_mul, intMatGL_coe h2, intMatGL_coe h, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  exact Matrix.map_mul (f := Int.castRingHom ℝ)

/-- Milne's slash operator does not change when $A$ is multiplied on the left by an element of
$\mathrm{SL}_2(\mathbb Z)$, for $f$ invariant of weight $2k$. -/
theorem milneSlash_SL_mul {k : ℕ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[(2 * k : ℤ)] γ = f)
    (γ : SL(2, ℤ)) {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : 0 < A.det) :
    milneSlash k (intMatGL ((γ : Matrix (Fin 2) (Fin 2) ℤ) * A)) f = milneSlash k (intMatGL A) f := by
  have h2 : ((γ : Matrix (Fin 2) (Fin 2) ℤ) * A).det = A.det := by
    rw [Matrix.det_mul, γ.det_coe, one_mul]
  have hp : 0 < (intMatGL A).det.val := by rw [intMatGL_det hA.ne']; exact_mod_cast hA
  have hp2 : 0 < (intMatGL ((γ : Matrix (Fin 2) (Fin 2) ℤ) * A)).det.val := by
    rw [intMatGL_det (by rw [h2]; exact hA.ne'), h2]; exact_mod_cast hA
  rw [milneSlash_eq k hp2, milneSlash_eq k hp, intMatGL_det (by rw [h2]; exact hA.ne'), h2,
    intMatGL_det hA.ne', intMatGL_SL_mul γ hA.ne', SlashAction.slash_mul]
  have : f ∣[(2 * k : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ) = f := hf γ
  rw [this]

/-- Milne's slash operator on $\begin{pmatrix} a & b \\ 0 & d\end{pmatrix}$. -/
theorem milneSlash_upperTri (k : ℕ) {n : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ hermiteTriples n) (f : ℍ → ℂ) (z : ℍ) :
    milneSlash k (intMatGL (upperTri t.1 t.2.1 t.2.2)) f z =
      (n : ℂ) ^ k * ((t.2.2 : ℂ) ^ (-(2 * k : ℤ)) *
        f (UpperHalfPlane.ofComplex ((t.1 * (z : ℂ) + t.2.1) / t.2.2))) := by
  obtain ⟨a, b, d⟩ := t
  obtain ⟨h1, h2, h3⟩ := mem_hermiteTriples.mp ht
  simp only at h1 h2
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hdet : (upperTri a b d).det = n := by
    simp [upperTri, Matrix.det_fin_two, ← h1]
  have hne : (upperTri (a : ℤ) b d).det ≠ 0 := by rw [hdet]; exact_mod_cast h3
  have hcoe := intMatGL_coe hne
  have hpos : 0 < (intMatGL (upperTri a b d)).det.val := by
    rw [intMatGL_det hne, hdet]; exact_mod_cast Nat.pos_of_ne_zero h3
  have he : ∀ i j, (intMatGL (upperTri a b d) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      ((upperTri a b d i j : ℤ) : ℝ) := fun i j ↦ by rw [hcoe]; rfl
  have hden : denom (intMatGL (upperTri a b d)) z = d := by
    simp only [UpperHalfPlane.denom, he]
    simp [upperTri]
  have hnum : UpperHalfPlane.num (intMatGL (upperTri a b d)) z = a * z + b := by
    simp only [UpperHalfPlane.num, he]
    simp [upperTri]
  have him : 0 < (((a : ℂ) * (z : ℂ) + b) / d).im := by
    simp only [Complex.div_natCast_im, Complex.add_im, Complex.mul_im, Complex.natCast_re,
      Complex.natCast_im, zero_mul, add_zero]
    have := z.im_pos
    have h1 : (0 : ℝ) < a := by exact_mod_cast ha
    have h2 : (0 : ℝ) < d := by exact_mod_cast hd
    simp only [UpperHalfPlane.coe_im]
    positivity
  have hsm : intMatGL (upperTri a b d) • z = UpperHalfPlane.ofComplex (((a : ℂ) * (z : ℂ) + b) / d) := by
    ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hpos, UpperHalfPlane.ofComplex_apply_of_im_pos him, hden, hnum]
  rw [milneSlash, hsm, hden, intMatGL_det hne, hdet]
  push_cast
  ring

/-- **Milne, p. 76**: $T(n)f = n^{k-1}\sum_\alpha f|_k\alpha$, the sum over any set of representatives $\alpha_i$ of
$\Gamma(1)\backslash M(n)$; for weakly modular $f$ the sum does not depend on the choice of representatives. -/
@[kb "milne2017mf" "Section 5, T(n) f as a sum over Gamma(1) \\ M(n) (pdf p. 76)"]
theorem milneHeckeSum_eq_sum_milneSlash {k : ℕ} {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), f ∣[(2 * k : ℤ)] γ = f)
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] (α : ι → Matrix (Fin 2) (Fin 2) ℤ) (hdet : ∀ i, (α i).det = n)
    (hrep : ∀ A : Matrix (Fin 2) (Fin 2) ℤ, A.det = n →
      ∃! i, ∃ γ : SpecialLinearGroup (Fin 2) ℤ, A = (γ : Matrix (Fin 2) (Fin 2) ℤ) * α i) :
    milneHeckeSum k n f = (n : ℂ) ^ (k - 1 : ℤ) • ∑ i, milneSlash k (intMatGL (α i)) f := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hex : ∀ i, ∃! t : ℕ × ℕ × ℕ, t ∈ hermiteTriples n ∧
      ∃ γ : SpecialLinearGroup (Fin 2) ℤ, α i = (γ : Matrix (Fin 2) (Fin 2) ℤ) * upperTri t.1 t.2.1 t.2.2 :=
    fun i ↦ exists_unique_hermiteTriple_SL hn (α i) (hdet i)
  choose σ hσ using fun i ↦ (hex i).exists
  have hval : ∀ i, milneSlash k (intMatGL (α i)) f = milneSlash k (intMatGL (upperTri (σ i).1 (σ i).2.1 (σ i).2.2)) f := by
    intro i
    obtain ⟨γ, hγ⟩ := (hσ i).2
    have hpos : (0 : ℤ) < (upperTri (σ i).1 (σ i).2.1 (σ i).2.2).det := by
      rw [det_upperTri_of_mem (hσ i).1]; exact_mod_cast hn
    rw [hγ]
    exact milneSlash_SL_mul hf γ hpos
  have key : ∀ z : ℍ, ∑ i, milneSlash k (intMatGL (α i)) f z =
      ∑ t ∈ hermiteTriples n, milneSlash k (intMatGL (upperTri t.1 t.2.1 t.2.2)) f z := by
    intro z
    refine Finset.sum_bij (fun i _ ↦ σ i) (fun i _ ↦ (hσ i).1) ?_ ?_ ?_
    · intro i _ j _ hij
      obtain ⟨_, γi, hi⟩ := hσ i
      obtain ⟨_, γj, hj⟩ := hσ j
      rw [← hij] at hj
      refine (hrep (α i) (hdet i)).unique ⟨1, by simp⟩ ⟨γi * γj⁻¹, ?_⟩
      rw [hi, hj, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc,
        ← Matrix.mul_assoc ((γj⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ),
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_mul]
    · intro t ht
      have hA := det_upperTri_of_mem ht
      obtain ⟨i, ⟨γ, hγ⟩, _⟩ := hrep _ hA
      refine ⟨i, Finset.mem_univ _, ?_⟩
      refine (hex i).unique (hσ i) ⟨ht, γ⁻¹, ?_⟩
      rw [hγ, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
    · intro i _
      rw [hval i]
  funext z
  rw [Pi.smul_apply, Finset.sum_apply, key z, milneHeckeSum, smul_eq_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  have h2 : (n : ℂ) ^ (2 * k - 1 : ℤ) = (n : ℂ) ^ (k - 1 : ℤ) * (n : ℂ) ^ k := by
    rw [← zpow_natCast, ← zpow_add₀ hn']
    congr 1
    push_cast; ring
  rw [milneSlash_upperTri k ht, h2, mul_assoc]

end ModularFormsKB.Milne
