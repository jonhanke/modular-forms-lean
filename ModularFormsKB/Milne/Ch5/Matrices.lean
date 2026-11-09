import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.Index
import TauCeti.LinearAlgebra.Matrix.SmithNormalForm.Int
import ModularFormsKB.Citation
/-!
# Milne, Chapter 5: lemmas on $2 \times 2$ matrices (Lemma 5.13, Remarks 5.14, 5.15, Lemmas 5.24, 5.30)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf pp. 72–80.

$M(n)$ is the set of $2 \times 2$ integer matrices of determinant $n$; it is written `{A | A.det = n}` and not given a
name. The triples of condition (6) of Lemma 5.13, $ad = n$, $a \ge 1$, $0 \le b < d$, form `hermiteTriples n`.
Throughout $n \ge 1$: condition (6) forces $d > 0$, hence $n = ad > 0$, so Milne's $n$ is positive.

## Items
- Lemma 5.13 (`exists_unique_hermiteTriple`).
- Remark 5.14, orbits of $\mathrm{SL}_2(\mathbb Z)$ on $M(n)$ (`exists_unique_hermiteTriple_SL`) and the count of
  $p + 1$ (`card_hermiteTriples`, `card_hermiteTriples_prime`).
- Remark 5.15 (`exists_unique_elementaryDivisors`).
- Lemma 5.24 (`exists_common_representatives`).
- Lemma 5.30 (`doubleCoset_eq_iUnion_of_rightCosets`).
-/

open Matrix

namespace ModularFormsKB.Milne

/-- The upper triangular integer matrix $\begin{pmatrix} a & b \\ 0 & d \end{pmatrix}$. -/
def upperTri (a b d : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![a, b; 0, d]

/-- The triples $(a, b, d)$ of condition (6) of Lemma 5.13: $ad = n$, $a \ge 1$, $0 \le b < d$. -/
def hermiteTriples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  n.divisorsAntidiagonal.biUnion fun ad ↦ (Finset.range ad.2).image fun b ↦ (ad.1, b, ad.2)

theorem mem_hermiteTriples {n : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ hermiteTriples n ↔ t.1 * t.2.2 = n ∧ t.2.1 < t.2.2 ∧ n ≠ 0 := by
  obtain ⟨a, b, d⟩ := t
  simp only [hermiteTriples, Finset.mem_biUnion, Nat.mem_divisorsAntidiagonal, Finset.mem_image,
    Finset.mem_range, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨a', d', ⟨h1, h2⟩, b', hb, rfl, rfl, rfl⟩
    exact ⟨h1, hb, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨a, d, ⟨h1, h3⟩, b, h2, rfl, rfl, rfl⟩

/-- Uniqueness core of Lemma 5.13: a matrix carrying one Hermite form to another is trivial. -/
lemma herm_unique_aux {a b d a' b' d' n : ℤ} (hn : 0 < n) (had : a * d = n) (had' : a' * d' = n)
    (ha : 0 < a) (ha' : 0 < a') (hd : 0 < d) (hd' : 0 < d') (hb : 0 ≤ b) (hbd : b < d)
    (hb' : 0 ≤ b') (hbd' : b' < d') (W : Matrix (Fin 2) (Fin 2) ℤ)
    (h : W * !![a, b; 0, d] = !![a', b'; 0, d']) : a = a' ∧ b = b' ∧ d = d' := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  have hw10 : W 1 0 = 0 := by
    rcases h10 with h | h
    · exact h
    · omega
  rw [hw10] at h11
  simp at h11
  have hprod : W 0 0 * W 1 1 = 1 := by
    have : (W 0 0 * W 1 1) * (a * d) = 1 * (a * d) := by
      calc (W 0 0 * W 1 1) * (a * d) = (W 0 0 * a) * (W 1 1 * d) := by ring
        _ = a' * d' := by rw [h00, h11]
        _ = 1 * (a * d) := by rw [had, had']; ring
    exact mul_right_cancel₀ (by positivity) this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hprod with h1 | h1
  · rw [h1] at hprod
    have h2 : W 1 1 = 1 := by linarith
    rw [h1] at h00
    rw [h2] at h11
    have hw01 : W 0 1 = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hl | hl
      · nlinarith
      · nlinarith
    rw [h1, hw01] at h01
    refine ⟨by linarith, by linarith, by linarith⟩
  · rw [h1] at h00
    omega

/-- Existence core of Lemma 5.13, with `U` in `SL₂(ℤ)`. -/
lemma herm_exists_SL {n : ℕ} (hn : 0 < n) (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det = n) :
    ∃ t ∈ hermiteTriples n, ∃ U : SpecialLinearGroup (Fin 2) ℤ,
      (U : Matrix (Fin 2) (Fin 2) ℤ) * A = upperTri t.1 t.2.1 t.2.2 := by
  have hgcd := Int.gcd_eq_gcd_ab (A 0 0) (A 1 0)
  obtain ⟨a', ha'⟩ := Int.gcd_dvd_left (a := A 0 0) (b := A 1 0)
  obtain ⟨c', hc'⟩ := Int.gcd_dvd_right (a := A 0 0) (b := A 1 0)
  generalize hga : Int.gcd (A 0 0) (A 1 0) = ga at hgcd ha' hc'
  generalize hx : Int.gcdA (A 0 0) (A 1 0) = x at hgcd
  generalize hy : Int.gcdB (A 0 0) (A 1 0) = y at hgcd
  have hdet := Matrix.det_fin_two A
  have hga0 : ga ≠ 0 := by
    rintro rfl
    simp at ha' hc'
    rw [ha', hc'] at hdet
    simp at hdet
    omega
  have hgpos : (0 : ℤ) < ga := by positivity
  have hxy : x * a' + y * c' = 1 := by
    have : (ga : ℤ) * (x * a' + y * c') = (ga : ℤ) * 1 := by
      rw [ha', hc'] at hgcd
      linarith
    exact mul_left_cancel₀ (by exact_mod_cast hga0) this
  let U : SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![x, y; -c', a'], by rw [Matrix.det_fin_two_of]; linarith⟩
  have hU : (U : Matrix (Fin 2) (Fin 2) ℤ) = !![x, y; -c', a'] := rfl
  have hT : (U : Matrix (Fin 2) (Fin 2) ℤ) * A = !![(ga : ℤ), ((U : Matrix (Fin 2) (Fin 2) ℤ) * A) 0 1;
      0, ((U : Matrix (Fin 2) (Fin 2) ℤ) * A) 1 1] := by
    have e00 : ((U : Matrix (Fin 2) (Fin 2) ℤ) * A) 0 0 = ga := by
      rw [hU]; simp [Matrix.mul_apply, Fin.sum_univ_two]; linarith
    have e10 : ((U : Matrix (Fin 2) (Fin 2) ℤ) * A) 1 0 = 0 := by
      rw [hU]; simp [Matrix.mul_apply, Fin.sum_univ_two]; rw [ha', hc']; ring
    ext i j; fin_cases i <;> fin_cases j <;> simp [e00, e10]
  generalize hb : ((U : Matrix (Fin 2) (Fin 2) ℤ) * A) 0 1 = b at hT
  generalize hd : ((U : Matrix (Fin 2) (Fin 2) ℤ) * A) 1 1 = d at hT
  have hdet2 : (ga : ℤ) * d = n := by
    have := congrArg Matrix.det hT
    rw [Matrix.det_mul, U.2, one_mul, hA, Matrix.det_fin_two_of] at this
    linarith
  have hdpos : 0 < d := by
    by_contra hneg
    nlinarith
  let V : SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![1, -(b / d); 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩
  have hV : (V : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -(b / d); 0, 1] := rfl
  have hdiv := Int.emod_add_mul_ediv b d
  have hmod0 : 0 ≤ b % d := Int.emod_nonneg _ hdpos.ne'
  have hmod1 : b % d < d := Int.emod_lt_of_pos _ hdpos
  refine ⟨(ga, (b % d).toNat, d.toNat), ?_, V * U, ?_⟩
  · rw [mem_hermiteTriples]
    refine ⟨?_, ?_, by omega⟩
    · have : ((ga * d.toNat : ℕ) : ℤ) = n := by
        push_cast; rw [Int.toNat_of_nonneg hdpos.le]; exact hdet2
      exact_mod_cast this
    · show (b % d).toNat < d.toNat
      omega
  · rw [SpecialLinearGroup.coe_mul, Matrix.mul_assoc, hT, hV, upperTri]
    simp only [Matrix.mul_fin_two]
    have e1 : (((b % d).toNat : ℕ) : ℤ) = b % d := Int.toNat_of_nonneg hmod0
    have e2 : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg hdpos.le
    simp only [e1, e2]
    congr 1
    · ext i j; fin_cases i <;> fin_cases j <;> simp
      linarith


/-- Uniqueness core of Lemma 5.13 for invertible `U`, `U'`. -/
lemma herm_unique {n : ℕ} (hn : 0 < n) (A : Matrix (Fin 2) (Fin 2) ℤ) {t t' : ℕ × ℕ × ℕ}
    (ht : t ∈ hermiteTriples n) (ht' : t' ∈ hermiteTriples n) (U U' : GL (Fin 2) ℤ)
    (hU : (U : Matrix (Fin 2) (Fin 2) ℤ) * A = upperTri t.1 t.2.1 t.2.2)
    (hU' : (U' : Matrix (Fin 2) (Fin 2) ℤ) * A = upperTri t'.1 t'.2.1 t'.2.2) : t = t' := by
  obtain ⟨a, b, d⟩ := t
  obtain ⟨a', b', d'⟩ := t'
  rw [mem_hermiteTriples] at ht ht'
  simp only at ht ht' hU hU'
  obtain ⟨h1, h2, -⟩ := ht
  obtain ⟨h1', h2', -⟩ := ht'
  have hW : ((U' * U⁻¹ : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * upperTri a b d =
      upperTri a' b' d' := by
    rw [← hU, ← hU', Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (↑U⁻¹ : Matrix (Fin 2) (Fin 2) ℤ),
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at h1; omega)
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at h1; omega)
  have ha' : 0 < a' := Nat.pos_of_ne_zero (by rintro rfl; simp at h1'; omega)
  have hd' : 0 < d' := Nat.pos_of_ne_zero (by rintro rfl; simp at h1'; omega)
  have key := herm_unique_aux (n := (n : ℤ)) (a := a) (b := b) (d := d) (a' := a') (b' := b') (d' := d')
    (by exact_mod_cast hn) (by exact_mod_cast h1) (by exact_mod_cast h1')
    (by exact_mod_cast ha) (by exact_mod_cast ha') (by exact_mod_cast hd) (by exact_mod_cast hd')
    (by positivity) (by exact_mod_cast h2) (by positivity) (by exact_mod_cast h2') _ hW
  obtain ⟨k1, k2, k3⟩ := key
  simp only [Prod.mk.injEq]
  exact ⟨by exact_mod_cast k1, by exact_mod_cast k2, by exact_mod_cast k3⟩

/-- **Milne, Lemma 5.13.** Let $A$ be a $2 \times 2$ integer matrix of determinant $n \ge 1$. There is an invertible
$U \in M_2(\mathbb Z)$ with $UA = \begin{pmatrix} a & b \\ 0 & d \end{pmatrix}$, $ad = n$, $a \ge 1$, $0 \le b < d$, and
$a, b, d$ are uniquely determined. -/
@[kb "milne2017mf" "Section 5, Lemma 5.13 (pdf p. 72)"]
theorem exists_unique_hermiteTriple {n : ℕ} (hn : 0 < n) (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det = n) :
    ∃! t : ℕ × ℕ × ℕ, t ∈ hermiteTriples n ∧
      ∃ U : GL (Fin 2) ℤ, (U : Matrix (Fin 2) (Fin 2) ℤ) * A = upperTri t.1 t.2.1 t.2.2 := by
  obtain ⟨t, ht, U, hU⟩ := herm_exists_SL hn A hA
  refine ⟨t, ⟨ht, SpecialLinearGroup.toGL U, hU⟩, ?_⟩
  rintro t' ⟨ht', U', hU'⟩
  exact (herm_unique hn A ht ht' (SpecialLinearGroup.toGL U) U' hU hU').symm

/-- **Milne, Remark 5.14.** $M(n) = \bigsqcup \mathrm{SL}_2(\mathbb Z)\begin{pmatrix} a & b \\ 0 & d\end{pmatrix}$,
disjoint union over the triples of Lemma 5.13. -/
@[kb "milne2017mf" "Section 5, Remark 5.14 (pdf p. 72)"]
theorem exists_unique_hermiteTriple_SL {n : ℕ} (hn : 0 < n) (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det = n) :
    ∃! t : ℕ × ℕ × ℕ, t ∈ hermiteTriples n ∧
      ∃ γ : SpecialLinearGroup (Fin 2) ℤ, A = (γ : Matrix (Fin 2) (Fin 2) ℤ) * upperTri t.1 t.2.1 t.2.2 := by
  obtain ⟨t, ht, U, hU⟩ := herm_exists_SL hn A hA
  refine ⟨t, ⟨ht, U⁻¹, ?_⟩, ?_⟩
  · rw [← hU, ← Matrix.mul_assoc, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
      SpecialLinearGroup.coe_one, Matrix.one_mul]
  · rintro t' ⟨ht', γ, hγ⟩
    refine (herm_unique hn A ht ht' (SpecialLinearGroup.toGL U) (SpecialLinearGroup.toGL γ⁻¹) hU ?_).symm
    show ((γ⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * A = _
    rw [hγ, ← Matrix.mul_assoc, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
      SpecialLinearGroup.coe_one, Matrix.one_mul]

/-- The number of triples of Lemma 5.13 is $\sigma_1(n) = \sum_{d \mid n} d$. -/
theorem card_hermiteTriples (n : ℕ) : (hermiteTriples n).card = ArithmeticFunction.sigma 1 n := by
  rw [hermiteTriples, Finset.card_biUnion]
  · rw [ArithmeticFunction.sigma_one_apply]
    have : ∀ ad ∈ n.divisorsAntidiagonal,
        ((Finset.range ad.2).image fun b ↦ (ad.1, b, ad.2)).card = ad.2 := by
      intro ad _
      rw [Finset.card_image_of_injective _ (by intro x y h; simpa using h)]
      simp
    rw [Finset.sum_congr rfl this]
    exact Nat.sum_divisorsAntidiagonal' (fun _ d ↦ d)
  · intro ad1 _ ad2 _ hne
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_image, Finset.mem_range] at hx1 hx2
    obtain ⟨b1, _, rfl⟩ := hx1
    obtain ⟨b2, _, h⟩ := hx2
    simp only [Prod.mk.injEq] at h
    exact hne (Prod.ext h.1.symm h.2.2.symm)

/-- **Milne, Remark 5.14**: for $n = p$ prime there are $p + 1$ orbits (equivalently, $p + 1$ sublattices of index
$p$ in a lattice, see `LatticeHecke.lean`). -/
@[kb "milne2017mf" "Section 5, Remark 5.14 (pdf pp. 72-73)"]
theorem card_hermiteTriples_prime {p : ℕ} (hp : p.Prime) : (hermiteTriples p).card = p + 1 := by
  rw [card_hermiteTriples, ArithmeticFunction.sigma_one_apply, Nat.Prime.sum_divisors hp]

/-- Divisibility chain for a two-term vector. -/
lemma divchain_two {a d : ℤ} (hd : a ∣ d) :
    ∀ ⦃i j : Fin 2⦄, i ≤ j → (![a, d] : Fin 2 → ℤ) i ∣ (![a, d] : Fin 2 → ℤ) j := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact dvd_refl _
  · exact hd
  · exfalso; revert hij; decide
  · exact dvd_refl _

/-- Conjugating by `SL₂(ℤ)` elements. -/
lemma sl_conj (L R : SpecialLinearGroup (Fin 2) ℤ) (A B : Matrix (Fin 2) (Fin 2) ℤ)
    (h : (L : Matrix (Fin 2) (Fin 2) ℤ) * A * (R : Matrix (Fin 2) (Fin 2) ℤ) = B) :
    A = ((L⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * B *
      ((R⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) := by
  have h1 : ((L⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * (L : Matrix (Fin 2) (Fin 2) ℤ)
      = 1 := by rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one]
  have h2 : (R : Matrix (Fin 2) (Fin 2) ℤ) * ((R⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
      = 1 := by rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
  subst h
  calc A = (((L⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * (L : Matrix (Fin 2) (Fin 2) ℤ)) * A *
      ((R : Matrix (Fin 2) (Fin 2) ℤ) * ((R⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)) := by
        rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- **Milne, Remark 5.15.** $M(n) = \bigsqcup \mathrm{SL}_2(\mathbb Z)\begin{pmatrix} a & 0 \\ 0 & d\end{pmatrix}
\mathrm{SL}_2(\mathbb Z)$, disjoint union over $a \mid d$, $ad = n$, $a \ge 1$: every $A \in M(n)$ lies in exactly one
such double coset. The proof uses the matrix Smith normal form of Tau Ceti
(`Matrix.exists_smith_normal_form_of_det_pos`, `Matrix.smith_normal_form_unique`). -/
@[kb "milne2017mf" "Section 5, Remark 5.15 (pdf p. 73)"]
theorem exists_unique_elementaryDivisors {n : ℕ} (hn : 0 < n) (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det = n) :
    ∃! ad : ℕ × ℕ, ad.1 ∣ ad.2 ∧ ad.1 * ad.2 = n ∧
      ∃ U V : SpecialLinearGroup (Fin 2) ℤ,
        A = (U : Matrix (Fin 2) (Fin 2) ℤ) * diagonal ![(ad.1 : ℤ), ad.2] * (V : Matrix (Fin 2) (Fin 2) ℤ) := by
  obtain ⟨L, R, d, hpos, hdiv, hLR⟩ :=
    Matrix.exists_smith_normal_form_of_det_pos A (by rw [hA]; exact_mod_cast hn)
  have hdet : d 0 * d 1 = n := by
    have := congrArg Matrix.det hLR
    rw [Matrix.det_mul, Matrix.det_mul, L.2, R.2, one_mul, mul_one, hA, Matrix.det_diagonal,
      Fin.prod_univ_two] at this
    exact this.symm
  have hd0 := hpos 0
  have hd1 := hpos 1
  have hdvd : d 0 ∣ d 1 := hdiv (by decide : (0 : Fin 2) ≤ 1)
  have e0 : (((d 0).toNat : ℕ) : ℤ) = d 0 := Int.toNat_of_nonneg hd0.le
  have e1 : (((d 1).toNat : ℕ) : ℤ) = d 1 := Int.toNat_of_nonneg hd1.le
  refine ⟨((d 0).toNat, (d 1).toNat), ⟨?_, ?_, L⁻¹, R⁻¹, ?_⟩, ?_⟩
  · show (d 0).toNat ∣ (d 1).toNat
    exact Int.natCast_dvd_natCast.mp (by rw [e0, e1]; exact hdvd)
  · show (d 0).toNat * (d 1).toNat = n
    have : (((d 0).toNat * (d 1).toNat : ℕ) : ℤ) = n := by push_cast; rw [e0, e1]; exact hdet
    exact_mod_cast this
  · have hD : (diagonal ![(((d 0).toNat : ℕ) : ℤ), (((d 1).toNat : ℕ) : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) =
        diagonal d := by
      congr 1
      funext i
      fin_cases i <;> simp [e0, e1]
    show A = _ * diagonal ![(((d 0).toNat : ℕ) : ℤ), (((d 1).toNat : ℕ) : ℤ)] * _
    rw [hD]
    exact sl_conj L R A _ hLR
  · rintro ⟨a', d'⟩ ⟨hdv, hpr, U', V', hA'⟩
    simp only at hdv hpr hA'
    have key := Matrix.smith_normal_form_unique (c := ![(a' : ℤ), (d' : ℤ)]) (d := d)
      (by intro i; fin_cases i <;> simp) (fun i ↦ (hpos i).le)
      (divchain_two (Int.natCast_dvd_natCast.mpr hdv)) hdiv
      (SpecialLinearGroup.toGL (L * U')) (SpecialLinearGroup.toGL (V' * R)) (by
        show ((L * U' : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
          diagonal ![(a' : ℤ), (d' : ℤ)] * ((V' * R : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = _
        rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul]
        calc (L : Matrix (Fin 2) (Fin 2) ℤ) * (U' : Matrix (Fin 2) (Fin 2) ℤ) * diagonal ![(a' : ℤ), (d' : ℤ)] *
              ((V' : Matrix (Fin 2) (Fin 2) ℤ) * (R : Matrix (Fin 2) (Fin 2) ℤ))
            = (L : Matrix (Fin 2) (Fin 2) ℤ) * ((U' : Matrix (Fin 2) (Fin 2) ℤ) * diagonal ![(a' : ℤ), (d' : ℤ)] *
              (V' : Matrix (Fin 2) (Fin 2) ℤ)) * (R : Matrix (Fin 2) (Fin 2) ℤ) := by
                simp only [Matrix.mul_assoc]
          _ = _ := by rw [← hA']; exact hLR)
    have k0 := congrFun key 0
    have k1 := congrFun key 1
    simp at k0 k1
    simp only [Prod.mk.injEq]
    omega

/-- Determinant of the Hermite form. -/
lemma det_upperTri_of_mem {n : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ hermiteTriples n) :
    (upperTri t.1 t.2.1 t.2.2).det = n := by
  rw [mem_hermiteTriples] at ht
  rw [upperTri, Matrix.det_fin_two_of]
  have : ((t.1 * t.2.2 : ℕ) : ℤ) = n := by exact_mod_cast ht.1
  push_cast at this
  linarith

/-- Left cancellation in `SL₂(ℤ)` at matrix level. -/
lemma sl_cancel_left (U1 U2 : SpecialLinearGroup (Fin 2) ℤ) (X : Matrix (Fin 2) (Fin 2) ℤ) :
    ((U2 * U1⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
      ((U1 : Matrix (Fin 2) (Fin 2) ℤ) * X) = (U2 : Matrix (Fin 2) (Fin 2) ℤ) * X := by
  rw [← Matrix.mul_assoc, ← SpecialLinearGroup.coe_mul, inv_mul_cancel_right]

/-- Right cancellation in `SL₂(ℤ)` at matrix level. -/
lemma sl_cancel_right (V1 V2 : SpecialLinearGroup (Fin 2) ℤ) (X : Matrix (Fin 2) (Fin 2) ℤ) :
    (X * (V2 : Matrix (Fin 2) (Fin 2) ℤ)) *
      ((V2⁻¹ * V1 : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      X * (V1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [Matrix.mul_assoc, ← SpecialLinearGroup.coe_mul, mul_inv_cancel_left]

/-- For `p` prime, every matrix of determinant `p` is `U diag(1,p) V` with `U, V ∈ SL₂(ℤ)`. -/
lemma exists_diag_one_p {p : ℕ} (hp : p.Prime) (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = p) :
    ∃ U V : SpecialLinearGroup (Fin 2) ℤ,
      B = (U : Matrix (Fin 2) (Fin 2) ℤ) * diagonal ![(1 : ℤ), (p : ℤ)] * (V : Matrix (Fin 2) (Fin 2) ℤ) := by
  obtain ⟨⟨a, d⟩, ⟨hdvd, hprod, U, V, hUV⟩, -⟩ := exists_unique_elementaryDivisors hp.pos B hB
  simp only at hdvd hprod hUV
  have ha : a = 1 := by
    have hpa : a ∣ p := ⟨d, hprod.symm⟩
    rcases (Nat.dvd_prime hp).mp hpa with h | h
    · exact h
    · exfalso
      subst h
      have hd1 : d = 1 := by
        have := hp.pos
        nlinarith
      subst hd1
      have := Nat.le_of_dvd one_pos hdvd
      have := hp.one_lt
      omega
  subst ha
  have hd : d = p := by simpa using hprod
  subst hd
  exact ⟨U, V, by simpa using hUV⟩

/-- A common element of the left orbit of `B1` and the right orbit of `B2`, when both have determinant `p`. -/
lemma exists_mem_both_orbits {p : ℕ} (hp : p.Prime) (B1 B2 : Matrix (Fin 2) (Fin 2) ℤ)
    (h1 : B1.det = p) (h2 : B2.det = p) :
    ∃ M : Matrix (Fin 2) (Fin 2) ℤ, ∃ γ1 γ2 : SpecialLinearGroup (Fin 2) ℤ,
      M = (γ1 : Matrix (Fin 2) (Fin 2) ℤ) * B1 ∧ M = B2 * (γ2 : Matrix (Fin 2) (Fin 2) ℤ) := by
  obtain ⟨U1, V1, hB1⟩ := exists_diag_one_p hp B1 h1
  obtain ⟨U2, V2, hB2⟩ := exists_diag_one_p hp B2 h2
  refine ⟨(U2 : Matrix (Fin 2) (Fin 2) ℤ) * diagonal ![(1 : ℤ), (p : ℤ)] * (V1 : Matrix (Fin 2) (Fin 2) ℤ),
    U2 * U1⁻¹, V2⁻¹ * V1, ?_, ?_⟩
  · rw [hB1, Matrix.mul_assoc (U1 : Matrix (Fin 2) (Fin 2) ℤ), sl_cancel_left, Matrix.mul_assoc]
  · rw [hB2, sl_cancel_right]

/-- **Milne, Lemma 5.24.** For $p$ prime there is a common set of representatives $\{\alpha_i\}$ for the left orbits
$\Gamma(1)\backslash M(p)$ and the right orbits $M(p)/\Gamma(1)$: every $A \in M(p)$ is $\gamma\alpha_i$ for exactly one
$i$ and is $\alpha_j\gamma'$ for exactly one $j$. (Milne's proof shows that every left orbit meets every right orbit;
a common system also needs the two orbit counts to agree, both being $p + 1$.) -/
@[kb "milne2017mf" "Section 5, Lemma 5.24 (pdf p. 77)"]
theorem exists_common_representatives {p : ℕ} (hp : p.Prime) :
    ∃ α : Fin (p + 1) → Matrix (Fin 2) (Fin 2) ℤ, (∀ i, (α i).det = p) ∧
      (∀ A : Matrix (Fin 2) (Fin 2) ℤ, A.det = p →
        ∃! i, ∃ γ : SpecialLinearGroup (Fin 2) ℤ, A = (γ : Matrix (Fin 2) (Fin 2) ℤ) * α i) ∧
      (∀ A : Matrix (Fin 2) (Fin 2) ℤ, A.det = p →
        ∃! i, ∃ γ : SpecialLinearGroup (Fin 2) ℤ, A = α i * (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
  let X := hermiteTriples p
  let e : Fin (p + 1) ≃ X :=
    (Fintype.equivFinOfCardEq (by simp [X, card_hermiteTriples_prime hp])).symm
  have hM : ∀ t : X, ∃ M : Matrix (Fin 2) (Fin 2) ℤ, ∃ γ1 γ2 : SpecialLinearGroup (Fin 2) ℤ,
      M = (γ1 : Matrix (Fin 2) (Fin 2) ℤ) * upperTri t.1.1 t.1.2.1 t.1.2.2 ∧
      M = (upperTri t.1.1 t.1.2.1 t.1.2.2)ᵀ * (γ2 : Matrix (Fin 2) (Fin 2) ℤ) := fun t ↦
    exists_mem_both_orbits hp _ _ (det_upperTri_of_mem t.2)
      (by rw [Matrix.det_transpose]; exact det_upperTri_of_mem t.2)
  choose M γ1 γ2 h1 h2 using hM
  have hleft : ∀ A : Matrix (Fin 2) (Fin 2) ℤ, A.det = p →
      ∃! t : X, ∃ γ : SpecialLinearGroup (Fin 2) ℤ, A = (γ : Matrix (Fin 2) (Fin 2) ℤ) * M t := by
    intro A hA
    obtain ⟨t0, ⟨ht0, γ0, hγ0⟩, huniq⟩ := exists_unique_hermiteTriple_SL hp.pos A hA
    refine ⟨⟨t0, ht0⟩, ⟨γ0 * (γ1 ⟨t0, ht0⟩)⁻¹, ?_⟩, ?_⟩
    · show A = _ * M ⟨t0, ht0⟩
      rw [h1 ⟨t0, ht0⟩, sl_cancel_left]
      exact hγ0
    · rintro t' ⟨γ, hγ⟩
      apply Subtype.ext
      refine huniq t'.1 ⟨t'.2, γ * γ1 t', ?_⟩
      rw [hγ, h1 t', SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
  have hright : ∀ A : Matrix (Fin 2) (Fin 2) ℤ, A.det = p →
      ∃! t : X, ∃ γ : SpecialLinearGroup (Fin 2) ℤ, A = M t * (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
    intro A hA
    obtain ⟨t0, ⟨ht0, γ0, hγ0⟩, huniq⟩ :=
      exists_unique_hermiteTriple_SL hp.pos Aᵀ (by rw [Matrix.det_transpose]; exact hA)
    refine ⟨⟨t0, ht0⟩, ⟨(γ2 ⟨t0, ht0⟩)⁻¹ * γ0.transpose, ?_⟩, ?_⟩
    · have hAt : A = (upperTri t0.1 t0.2.1 t0.2.2)ᵀ * ((γ0.transpose : SpecialLinearGroup (Fin 2) ℤ) :
          Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [← Matrix.transpose_transpose A, hγ0, Matrix.transpose_mul]
        rfl
      show A = M ⟨t0, ht0⟩ * _
      rw [h2 ⟨t0, ht0⟩, sl_cancel_right]
      exact hAt
    · rintro t' ⟨γ, hγ⟩
      apply Subtype.ext
      refine huniq t'.1 ⟨t'.2, γ.transpose * (γ2 t').transpose, ?_⟩
      rw [hγ, h2 t']
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, SpecialLinearGroup.coe_mul,
        Matrix.mul_assoc]
      rfl
  refine ⟨fun i ↦ M (e i), fun i ↦ ?_, fun A hA ↦ ?_, fun A hA ↦ ?_⟩
  · show (M (e i)).det = p
    rw [h1 (e i), Matrix.det_mul, (γ1 (e i)).2, one_mul]
    exact det_upperTri_of_mem (e i).2
  · obtain ⟨t, ht, hu⟩ := hleft A hA
    refine ⟨e.symm t, by simpa using ht, fun j hj ↦ ?_⟩
    have := hu (e j) hj
    rw [← this]; simp
  · obtain ⟨t, ht, hu⟩ := hright A hA
    refine ⟨e.symm t, by simpa using ht, fun j hj ↦ ?_⟩
    have := hu (e j) hj
    rw [← this]; simp

/-- **Milne, Lemma 5.30** (in any group $G$; Milne takes $G = \mathrm{GL}_2(\mathbb R)^+$ and $\Gamma$ of finite index in
$\Gamma(1)$). If $\Gamma = \bigsqcup_i (\Gamma \cap \alpha^{-1}\Gamma\alpha)\beta_i$, then
$\Gamma\alpha\Gamma = \bigsqcup_i \Gamma\alpha\beta_i$. -/
@[kb "milne2017mf" "Section 5, Lemma 5.30 (pdf p. 80)"]
theorem doubleCoset_eq_iUnion_of_rightCosets {G : Type*} [Group G] (Γ : Subgroup G) (α : G) {ι : Type*}
    (β : ι → G) (hβ : ∀ i, β i ∈ Γ)
    (hdecomp : ∀ γ ∈ Γ, ∃! i, γ * (β i)⁻¹ ∈ Γ ∧ α * (γ * (β i)⁻¹) * α⁻¹ ∈ Γ) :
    ∀ x ∈ DoubleCoset.doubleCoset α (Γ : Set G) Γ, ∃! i, x * (α * β i)⁻¹ ∈ Γ := by
  intro x hx
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
  obtain ⟨i, ⟨hi1, hi2⟩, -⟩ := hdecomp γ₂ hγ₂
  have key : ∀ j, γ₁ * α * γ₂ * (α * β j)⁻¹ ∈ Γ → α * (β j * (β i)⁻¹) * α⁻¹ ∈ Γ := by
    intro j hj
    have h1 : γ₁ * α * γ₂ * (α * β i)⁻¹ ∈ Γ := by
      have : γ₁ * α * γ₂ * (α * β i)⁻¹ = γ₁ * (α * (γ₂ * (β i)⁻¹) * α⁻¹) := by group
      rw [this]
      exact Γ.mul_mem hγ₁ hi2
    have := Γ.mul_mem (Γ.inv_mem hj) h1
    have e : (γ₁ * α * γ₂ * (α * β j)⁻¹)⁻¹ * (γ₁ * α * γ₂ * (α * β i)⁻¹) =
        α * (β j * (β i)⁻¹) * α⁻¹ := by group
    rwa [e] at this
  refine ⟨i, ?_, fun j hj ↦ ?_⟩
  · show γ₁ * α * γ₂ * (α * β i)⁻¹ ∈ Γ
    have : γ₁ * α * γ₂ * (α * β i)⁻¹ = γ₁ * (α * (γ₂ * (β i)⁻¹) * α⁻¹) := by group
    rw [this]
    exact Γ.mul_mem hγ₁ hi2
  · have hk := key j hj
    refine (hdecomp (β j) (hβ j)).unique ⟨?_, ?_⟩ ⟨?_, hk⟩
    · simp
    · simp
    · exact Γ.mul_mem (hβ j) (Γ.inv_mem (hβ i))

end ModularFormsKB.Milne
