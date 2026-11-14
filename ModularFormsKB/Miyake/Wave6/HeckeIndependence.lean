import ModularFormsKB.Miyake.Wave5.DoubleCosetRelations
import ModularFormsKB.Miyake.Wave4.HeckeCoefficients

/-!
# Miyake §4.5: `ℛ(N)` is a polynomial ring, Theorem 4.5.9 in full

Miyake, *Modular Forms* (Springer 1989), Theorem 4.5.9, p. 142: the Hecke ring
`ℛ(N) = ℛ(Γ₀(N), Δ₀(N))` over `ℤ` is the polynomial ring in `T(p)`, `T(p, p)` for the primes
`p ∤ N` and `T(q)` for the primes `q ∣ N`.

Wave 5 proved the generation half (`Wave5.closure_heckeGenerator_eq_top`). This file proves the
algebraic independence ("easily verified" in the book) and assembles the named statement
`Miyake.HeckeAlgebraPolynomialStatement N` of wave 3 (`heckeAlgebraPolynomial`), closing
LE-MF-0185.

## The leading-term argument
The double cosets `T(l, m)` (`0 < l ∣ m`, `(l, N) = 1`) are distinct basis elements of the free
`ℤ`-module `ℛ(N)` (`pairCoeff_heckeTPair`: `T(l, m)` determines `l`, the greatest common divisor of
the entries, and `l m`, the determinant). The monomial `∏ T(p)^{a_p} T(p, p)^{b_p} ∏ T(q)^{c_q}`
equals `T(L, M) + (a combination of T(l, m) with l m = L M, L ∣ l, L < l)`, where
`L = ∏ p^{b_p}` and `M = ∏ p^{a_p + b_p} ∏ q^{c_q}` (`aeval_monomial_lead`), by Lemma 4.5.7 (1)
and Lemma 4.5.8 (1) (wave 5). The exponents are recovered from `(L, M)`
(`leadPair_injective`). For a nonzero polynomial, the coefficient of `T(L, M)` at a monomial of
its support with least `L` is the coefficient of that monomial.
-/

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups HeckeCosetModule

noncomputable section

namespace ModularFormsKB.Miyake.Wave6

open ModularFormsKB.Miyake.Wave4

variable (N : ℕ) [NeZero N]

/-- `ℛ(N)` is commutative (Miyake Theorem 4.5.3 (1), wave 4's `heckeRing_mul_comm`); this is the
commutative ring structure used to evaluate polynomials in its elements. -/
abbrev heckeCommRing : CommRing (HeckeRingGamma0 N) :=
  { (inferInstance : Ring (HeckeRingGamma0 N)) with mul_comm := heckeRing_mul_comm }

attribute [local instance] heckeCommRing

/-- Miyake's admissible pairs: `0 < l`, `l ∣ m`, `(l, N) = 1`. -/
def IsPair (l m : ℕ) : Prop := 0 < l ∧ l ∣ m ∧ l.Coprime N

/-- The coefficient of the double coset `T(l, m)` in an element of `ℛ(N)` (`0` if `(l, N) ≠ 1`). -/
def pairCoeff (l m : ℕ) : HeckeRingGamma0 N →+ ℤ :=
  if h : l.Coprime N then
    Finsupp.applyAddHom (HeckeRing.GL2.diagCosetGamma0 N ![l, m] fun _ ↦ h)
  else 0

/-- `pairCoeff` on a basis element, when `(l, N) = 1`. -/
theorem pairCoeff_single {l m : ℕ} (h : Nat.Coprime ((![l, m] : Fin 2 → ℕ) 0) N)
    (D : HeckeCoset (HeckeRing.GL2.Delta0 N) ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ))) (b : ℤ) [Decidable (D =
        HeckeRing.GL2.diagCosetGamma0 N ![l, m] fun _ ↦ h)] :
    pairCoeff N l m (HeckeCosetModule.single ℤ D b) =
      if D = HeckeRing.GL2.diagCosetGamma0 N ![l, m] fun _ ↦ h then b else 0 := by
  have h' : l.Coprime N := h
  have e : pairCoeff N l m = _ := dif_pos h'
  rw [e]
  exact Finsupp.single_apply

/-- **Distinct pairs give distinct double cosets**: the coefficient of `T(l, m)` in `T(l', m')`
(for `0 < m`; at `m = 0` the junk coset `diag(l, 0) = 1` would collide with `T(1, 1)`). -/
theorem pairCoeff_heckeTPair {l m l' m' : ℕ} (h : IsPair N l m) (h' : IsPair N l' m')
    (hm : 0 < m) :
    pairCoeff N l m (heckeTPair N l' m') = if l = l' ∧ m = m' then 1 else 0 := by
  classical
  obtain ⟨hl, hlm, hlN⟩ := h
  obtain ⟨hl', hlm', hlN'⟩ := h'
  rcases Nat.eq_zero_or_pos m' with rfl | hm'
  · have : heckeTPair N l' 0 = 0 :=
      HeckeRing.GL2.diagElemGamma0_of_not_pos N (fun h ↦ by simpa using h 1)
    rw [this, map_zero]; exact (if_neg (by omega)).symm
  · have hpos' : ∀ i, 0 < (![l', m'] : Fin 2 → ℕ) i := fun i ↦ by
      fin_cases i <;> simp [hl', hm']
    have hpos : ∀ i, 0 < (![l, m] : Fin 2 → ℕ) i := fun i ↦ by
      fin_cases i <;> simp [hl, hm]
    have hc' : Nat.Coprime ((![l', m'] : Fin 2 → ℕ) 0) N := hlN'
    have hc : Nat.Coprime ((![l, m] : Fin 2 → ℕ) 0) N := hlN
    unfold heckeTPair
    rw [HeckeRing.GL2.diagElemGamma0_of_pos_of_coprime N hpos' hc']
    rw [pairCoeff_single N hc]
    by_cases hD : HeckeRing.GL2.diagCosetGamma0 N ![l', m'] (fun _ ↦ hc') =
        HeckeRing.GL2.diagCosetGamma0 N ![l, m] (fun _ ↦ hc)
    · rw [if_pos hD]
      have h1 := congrArg (HeckeRing.GL2.toLevelOneCoset N) hD
      simp only [HeckeRing.GL2.toLevelOneCoset_diagCosetGamma0] at h1
      have h2 := HeckeRing.GLn.eq_of_diagCoset_eq hpos' hpos
        (by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all [Fin.le_def]) 
        (by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all [Fin.le_def]) h1
      have e0 := congr_fun h2 0
      have e1 := congr_fun h2 1
      simp at e0 e1
      rw [if_pos ⟨e0.symm, e1.symm⟩]
    · have hne : ¬ (l = l' ∧ m = m') := by
        rintro ⟨rfl, rfl⟩
        exact hD rfl
      simp only [hD, hne, if_false]

/-- The combinations of `T(l, m)` with `l m = L M`, `L ∣ l` and `L < l`. -/
def upper (L M : ℕ) : Submodule ℤ (HeckeRingGamma0 N) :=
  Submodule.span ℤ {x | ∃ l m : ℕ, IsPair N l m ∧ l * m = L * M ∧ L ∣ l ∧ L < l ∧
    x = heckeTPair N l m}

/-- Elements of `upper L' M'` have no `T(l, m)`-coefficient for `l ≤ L'` (`0 < m`). -/
theorem pairCoeff_eq_zero_of_mem_upper {L' M' l m : ℕ} (hlm : IsPair N l m) (hm : 0 < m)
    (hl : l ≤ L') {x : HeckeRingGamma0 N} (hx : x ∈ upper N L' M') : pairCoeff N l m x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l', m', hp, -, -, hlt, rfl⟩ := hy
    rw [pairCoeff_heckeTPair N hlm hp hm]
    have : ¬ (l = l' ∧ m = m') := by
      rintro ⟨rfl, -⟩
      omega
    simp [this]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_zsmul, hx, smul_zero]

/-- A product of two admissible double cosets with coprime determinants. -/
theorem isPair_mul_heckeTPair_mul {l m l' m' : ℕ} (h : IsPair N l m) (h' : IsPair N l' m')
    (hc : (l * m).Coprime (l' * m')) :
    IsPair N (l * l') (m * m') ∧
      heckeTPair N l m * heckeTPair N l' m' = heckeTPair N (l * l') (m * m') :=
  ⟨⟨Nat.mul_pos h.1 h'.1, Nat.mul_dvd_mul h.2.1 h'.2.1, Nat.Coprime.mul_left h.2.2 h'.2.2⟩,
    Wave5.heckeTPair_mul_of_coprime N h.2.1 h'.2.1 hc⟩

/-- `T(l, m) · y ∈ upper (L L') (M M')` for `y ∈ upper L' M'`, where `T(l, m)` is a double coset
with `l m = L M`, `L ∣ l`, and coprime determinants. -/
theorem heckeTPair_mul_mem_upper {L M L' M' l m : ℕ} (hlm : IsPair N l m)
    (hdiv : L ∣ l) (hdet : l * m = L * M)
    (hc : (L * M).Coprime (L' * M')) {y : HeckeRingGamma0 N} (hy : y ∈ upper N L' M') :
    heckeTPair N l m * y ∈ upper N (L * L') (M * M') := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l', m', hp', hdet', hd', hlt', rfl⟩ := hz
    have hc' : (l * m).Coprime (l' * m') := by rw [hdet, hdet']; exact hc
    obtain ⟨hpair, hmul⟩ := isPair_mul_heckeTPair_mul N hlm hp' hc'
    rw [hmul]
    refine Submodule.subset_span ⟨l * l', m * m', hpair, ?_, mul_dvd_mul hdiv hd', ?_, rfl⟩
    · calc l * l' * (m * m') = (l * m) * (l' * m') := by ring
        _ = L * L' * (M * M') := by rw [hdet, hdet']; ring
    · have hLpos : 0 < L := Nat.pos_of_dvd_of_pos hdiv hlm.1
      have hle : L ≤ l := Nat.le_of_dvd hlm.1 hdiv
      calc L * L' < L * l' := Nat.mul_lt_mul_of_pos_left hlt' hLpos
        _ ≤ l * l' := Nat.mul_le_mul_right _ hle
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

/-- The product of two elements of `upper` lies in the product `upper`, for coprime
determinants. -/
theorem mul_mem_upper_of_upper {L M L' M' : ℕ}
    (hc : (L * M).Coprime (L' * M')) {x y : HeckeRingGamma0 N} (hx : x ∈ upper N L M)
    (hy : y ∈ upper N L' M') : x * y ∈ upper N (L * L') (M * M') := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, m, hp, hdet, hd, -, rfl⟩ := hz
    exact heckeTPair_mul_mem_upper N hp hd hdet hc hy
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx

/-- `y · T(L', M') ∈ upper (L L') (M M')` for `y ∈ upper L M`. -/
theorem mul_heckeTPair_mem_upper {L M L' M' : ℕ} (hL'M' : IsPair N L' M')
    (hc : (L * M).Coprime (L' * M')) {y : HeckeRingGamma0 N} (hy : y ∈ upper N L M) :
    y * heckeTPair N L' M' ∈ upper N (L * L') (M * M') := by
  rw [heckeRing_mul_comm y, mul_comm L L', mul_comm M M']
  exact heckeTPair_mul_mem_upper N hL'M' (dvd_refl _) rfl hc.symm hy

/-- A double coset is "led" by `T(L, M)`: it is `T(L, M)` plus an element of `upper L M`. -/
def Lead (x : HeckeRingGamma0 N) (L M : ℕ) : Prop := x - heckeTPair N L M ∈ upper N L M

/-- Leading terms multiply, for admissible pairs with coprime determinants. -/
theorem Lead.mul {x y : HeckeRingGamma0 N} {L M L' M' : ℕ} (hx : Lead N x L M)
    (hy : Lead N y L' M') (hLM : IsPair N L M) (hL'M' : IsPair N L' M')
    (hc : (L * M).Coprime (L' * M')) : Lead N (x * y) (L * L') (M * M') := by
  unfold Lead at *
  obtain ⟨hpair, hmul⟩ := isPair_mul_heckeTPair_mul N hLM hL'M' hc
  have key : x * y - heckeTPair N (L * L') (M * M') =
      heckeTPair N L M * (y - heckeTPair N L' M') + (x - heckeTPair N L M) * heckeTPair N L' M' +
        (x - heckeTPair N L M) * (y - heckeTPair N L' M') := by
    rw [← hmul]; noncomm_ring
  rw [key]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact heckeTPair_mul_mem_upper N hLM (dvd_refl L) rfl hc hy
  · exact mul_heckeTPair_mem_upper N hL'M' hc hx
  · exact mul_mem_upper_of_upper N hc hx hy

/-- The scalar `T(c, c)` shifts the leading pair. -/
theorem heckeTPair_scalar_mul (c l m : ℕ) :
    heckeTPair N c c * heckeTPair N l m = heckeTPair N (c * l) (c * m) := by
  have h := HeckeRing.GL2.diagElemGamma0_const_mul N c ![l, m]
  have e1 : ((fun _ : Fin 2 ↦ c) : Fin 2 → ℕ) = ![c, c] := by ext i; fin_cases i <;> rfl
  have e2 : ((fun _ : Fin 2 ↦ c) * ![l, m] : Fin 2 → ℕ) = ![c * l, c * m] := by
    ext i; fin_cases i <;> simp
  rw [e2, e1] at h
  exact h

/-- `T(c, c) · upper L M ⊆ upper (c L) (c M)`, for `c` positive and prime to `N`. -/
theorem scalar_mul_mem_upper {c L M : ℕ} (hc : 0 < c) (hcN : c.Coprime N)
    {y : HeckeRingGamma0 N} (hy : y ∈ upper N L M) :
    heckeTPair N c c * y ∈ upper N (c * L) (c * M) := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, m, hp, hdet, hd, hlt, rfl⟩ := hz
    rw [heckeTPair_scalar_mul]
    refine Submodule.subset_span ⟨c * l, c * m,
      ⟨Nat.mul_pos hc hp.1, Nat.mul_dvd_mul_left c hp.2.1, Nat.Coprime.mul_left hcN hp.2.2⟩, ?_,
      Nat.mul_dvd_mul_left c hd, Nat.mul_lt_mul_of_pos_left hlt hc, rfl⟩
    calc c * l * (c * m) = c * c * (l * m) := by ring
      _ = c * L * (c * M) := by rw [hdet]; ring
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

/-- The scalar `T(c, c)` shifts the leading pair. -/
theorem Lead.scalar_mul {x : HeckeRingGamma0 N} {c L M : ℕ} (hc : 0 < c) (hcN : c.Coprime N)
    (hx : Lead N x L M) : Lead N (heckeTPair N c c * x) (c * L) (c * M) := by
  unfold Lead at *
  rw [← heckeTPair_scalar_mul, ← mul_sub]
  exact scalar_mul_mem_upper N hc hcN hx

/-- `T(1, 1) = 1`. -/
theorem heckeTPair_one_one : heckeTPair N 1 1 = 1 := HeckeRing.GL2.diagElemGamma0_one_one N

/-- `(p^i, p^j)` is an admissible pair for a prime `p ∤ N` and `i ≤ j`. -/
theorem isPair_pow {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) {i j : ℕ} (hij : i ≤ j) :
    IsPair N (p ^ i) (p ^ j) :=
  ⟨pow_pos hp.pos _, pow_dvd_pow p hij,
    Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN)⟩

/-- `T(p^i, p^j)` lies in `upper p^b p^c` when `b < i ≤ j` and `i + j = b + c`. -/
theorem heckeTPair_pow_mem_upper {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) {b c i j : ℕ}
    (hij : i ≤ j) (hb : b < i) (hsum : i + j = b + c) :
    heckeTPair N (p ^ i) (p ^ j) ∈ upper N (p ^ b) (p ^ c) :=
  Submodule.subset_span ⟨p ^ i, p ^ j, isPair_pow N hp hpN hij,
    by rw [← pow_add, ← pow_add, hsum], pow_dvd_pow p hb.le,
    Nat.pow_lt_pow_right hp.one_lt hb, rfl⟩

/-- The generators of `upper p^b p^c` are `T(p^i, p^j)` with `b < i ≤ j`, `i + j = b + c`. -/
theorem exists_pow_of_pair {p : ℕ} (hp : p.Prime) {b c l m : ℕ} (hlm : IsPair N l m)
    (hdet : l * m = p ^ b * p ^ c) (hlt : p ^ b < l) :
    ∃ i j, l = p ^ i ∧ m = p ^ j ∧ i ≤ j ∧ b < i ∧ i + j = b + c := by
  have hl : l ∣ p ^ (b + c) := ⟨m, by rw [pow_add, ← hdet]⟩
  have hm : m ∣ p ^ (b + c) := ⟨l, by rw [pow_add, ← hdet, mul_comm]⟩
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hl
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hm
  refine ⟨i, j, rfl, rfl, (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hlm.2.1,
    (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt, ?_⟩
  apply Nat.pow_right_injective hp.two_le
  simp only [pow_add] at hdet ⊢
  exact hdet

/-- `T(1, p) T(p^i, p^i) = T(p^i, p^(i+1))` for a prime `p ∤ N`. -/
theorem heckeTPair_one_mul_diag (i p : ℕ) :
    heckeTPair N 1 p * heckeTPair N (p ^ i) (p ^ i) = heckeTPair N (p ^ i) (p ^ (i + 1)) := by
  rw [heckeRing_mul_comm, heckeTPair_scalar_mul, mul_one, ← pow_succ]

/-- `T(1, p) T(p^i, p^j) = T(p^i, p^(j+1)) + k T(p^(i+1), p^j)` for `i < j`, `p ∤ N`. -/
theorem heckeTPair_one_mul_pow_lt {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) {i j : ℕ} (h : i < j) :
    ∃ k : ℤ, heckeTPair N 1 p * heckeTPair N (p ^ i) (p ^ j) =
      heckeTPair N (p ^ i) (p ^ (j + 1)) + k • heckeTPair N (p ^ (i + 1)) (p ^ j) := by
  obtain ⟨e, rfl⟩ : ∃ e, j = i + (e + 1) := ⟨j - i - 1, by omega⟩
  have h1 := Wave5.heckeTPair_one_prime_mul N hp hpN (e := e + 1) (by omega)
  refine ⟨((if e + 1 = 1 then p + 1 else p : ℕ) : ℤ), ?_⟩
  have e1 : heckeTPair N (p ^ i) (p ^ (i + (e + 1))) =
      heckeTPair N (p ^ i) (p ^ i) * heckeTPair N 1 (p ^ (e + 1)) := by
    rw [heckeTPair_scalar_mul, mul_one, pow_add]
  have e2 : heckeTPair N (p ^ (i + 1)) (p ^ (i + (e + 1))) =
      heckeTPair N (p ^ i) (p ^ i) * heckeTPair N p (p ^ (e + 1)) := by
    rw [heckeTPair_scalar_mul, pow_succ, pow_add]
  have e3 : heckeTPair N (p ^ i) (p ^ (i + (e + 1) + 1)) =
      heckeTPair N (p ^ i) (p ^ i) * heckeTPair N 1 (p ^ (e + 1 + 1)) := by
    rw [heckeTPair_scalar_mul, mul_one, ← pow_add, add_assoc]
  rw [e1, e2, e3, mul_left_comm, h1, mul_add, mul_smul_comm]

/-- `T(1, p)` carries `upper p^b p^c` to `upper p^b p^(c+1)`, for a prime `p ∤ N`. -/
theorem heckeTPair_one_mul_mem_upper {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) {b c : ℕ}
    {y : HeckeRingGamma0 N} (hy : y ∈ upper N (p ^ b) (p ^ c)) :
    heckeTPair N 1 p * y ∈ upper N (p ^ b) (p ^ (c + 1)) := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, m, hlm, hdet, hd, hlt, rfl⟩ := hz
    obtain ⟨i, j, rfl, rfl, hij, hbi, hs⟩ := exists_pow_of_pair N hp hlm hdet hlt
    rcases hij.eq_or_lt with rfl | hlt'
    · rw [heckeTPair_one_mul_diag]
      exact heckeTPair_pow_mem_upper N hp hpN (Nat.le_succ i) hbi (by omega)
    · obtain ⟨k, hk⟩ := heckeTPair_one_mul_pow_lt N hp hpN hlt'
      rw [hk]
      exact Submodule.add_mem _ (heckeTPair_pow_mem_upper N hp hpN (by omega) hbi (by omega))
        (Submodule.smul_mem _ _
          (heckeTPair_pow_mem_upper N hp hpN (by omega) (by omega) (by omega)))
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

/-- Multiplying a leading term by `T(1, p)` raises the second exponent. -/
theorem Lead.one_mul_good {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) {x : HeckeRingGamma0 N}
    {b c : ℕ} (hbc : b ≤ c) (hx : Lead N x (p ^ b) (p ^ c)) :
    Lead N (heckeTPair N 1 p * x) (p ^ b) (p ^ (c + 1)) := by
  unfold Lead at *
  have e : heckeTPair N 1 p * x - heckeTPair N (p ^ b) (p ^ (c + 1)) =
      (heckeTPair N 1 p * heckeTPair N (p ^ b) (p ^ c) - heckeTPair N (p ^ b) (p ^ (c + 1))) +
        heckeTPair N 1 p * (x - heckeTPair N (p ^ b) (p ^ c)) := by noncomm_ring
  rw [e]
  refine Submodule.add_mem _ ?_ (heckeTPair_one_mul_mem_upper N hp hpN hx)
  rcases hbc.eq_or_lt with rfl | hlt
  · rw [heckeTPair_one_mul_diag, sub_self]; exact Submodule.zero_mem _
  · obtain ⟨k, hk⟩ := heckeTPair_one_mul_pow_lt N hp hpN hlt
    rw [hk, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (heckeTPair_pow_mem_upper N hp hpN (by omega) (by omega)
      (by omega))

/-- The leading term of `T(1, p)^a T(p, p)^b`, for a prime `p ∤ N`. -/
theorem lead_good {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (a b : ℕ) :
    Lead N (heckeTPair N 1 p ^ a * heckeTPair N p p ^ b) (p ^ b) (p ^ (a + b)) := by
  have hpc : p.Coprime N := (Nat.Prime.coprime_iff_not_dvd hp).2 hpN
  have h1 : ∀ b : ℕ, Lead N (heckeTPair N p p ^ b) (p ^ b) (p ^ (0 + b)) := by
    intro b
    induction b with
    | zero => simp [Lead, heckeTPair_one_one]
    | succ b ih =>
      have := Lead.scalar_mul N hp.pos hpc ih
      rw [pow_succ']
      simpa only [← pow_succ', zero_add] using this
  induction a with
  | zero => simpa using h1 b
  | succ a ih =>
    have := Lead.one_mul_good N hp hpN (Nat.le_add_left b a) ih
    rw [pow_succ' (heckeTPair N 1 p) a, mul_assoc, show a + 1 + b = a + b + 1 by omega]
    exact this

/-- The leading term of `T(q)^c` for a prime `q ∣ N`. -/
theorem lead_bad {q : ℕ} (hq : q.Prime) (hqN : q ∣ N) (c : ℕ) :
    Lead N (heckeTPair N 1 q ^ c) 1 (q ^ c) := by
  have : heckeTPair N 1 q ^ c = heckeTPair N 1 (q ^ c) := by
    induction c with
    | zero => simp [heckeTPair_one_one]
    | succ c ih => rw [pow_succ', ih, Wave5.heckeTPair_one_prime_mul_of_dvd N hq hqN c]
  rw [Lead, this, sub_self]
  exact Submodule.zero_mem _

/-- The leading pair `(L, M)` of a monomial in the generators of Theorem 4.5.9:
`L = ∏_{p ∤ N} p^{b_p}`, `M = ∏_{p ∤ N} p^{a_p + b_p} ∏_{q ∣ N} q^{c_q}`, for the exponents
`a` of `T(p)`, `b` of `T(p, p)` and `c` of `T(q)`. -/
def leadPair (s : HeckeGenerators N →₀ ℕ) : ℕ × ℕ :=
  (s.prod fun i e ↦ match i with
      | .inl _ => 1
      | .inr (.inl p) => p.1 ^ e
      | .inr (.inr _) => 1,
    s.prod fun i e ↦ match i with
      | .inl p => p.1 ^ e
      | .inr (.inl p) => p.1 ^ e
      | .inr (.inr q) => q.1 ^ e)

/-- The prime attached to a generator. -/
def genPrime : HeckeGenerators N → ℕ
  | .inl p => p.1
  | .inr (.inl p) => p.1
  | .inr (.inr q) => q.1

/-- The attached prime is prime. -/
theorem genPrime_prime (j : HeckeGenerators N) : (genPrime N j).Prime := by
  rcases j with ⟨p, hp, -⟩ | ⟨p, hp, -⟩ | ⟨p, hp, -⟩ <;> exact hp

/-- The leading pair of the zero monomial. -/
theorem leadPair_zero : leadPair N 0 = (1, 1) := by simp [leadPair]

/-- The leading pair is multiplicative in the exponent vector. -/
theorem leadPair_add (s t : HeckeGenerators N →₀ ℕ) :
    leadPair N (s + t) =
      ((leadPair N s).1 * (leadPair N t).1, (leadPair N s).2 * (leadPair N t).2) := by
  unfold leadPair
  refine Prod.ext ?_ ?_ <;> dsimp only <;>
    refine Finsupp.prod_add_index' (fun i ↦ ?_) (fun i b₁ b₂ ↦ ?_) <;>
    rcases i with p | p | q <;> simp [pow_add]

/-- The leading pair of a single `T(p)`. -/
theorem leadPair_single_inl (p : {p : ℕ // p.Prime ∧ ¬ p ∣ N}) (e : ℕ) :
    leadPair N (Finsupp.single (.inl p) e) = (1, p.1 ^ e) := by
  simp [leadPair, Finsupp.prod_single_index]

/-- The leading pair of a single `T(p, p)`. -/
theorem leadPair_single_inr_inl (p : {p : ℕ // p.Prime ∧ ¬ p ∣ N}) (e : ℕ) :
    leadPair N (Finsupp.single (.inr (.inl p)) e) = (p.1 ^ e, p.1 ^ e) := by
  simp [leadPair, Finsupp.prod_single_index]

/-- The leading pair of a single `T(q)`. -/
theorem leadPair_single_inr_inr (q : {q : ℕ // q.Prime ∧ q ∣ N}) (e : ℕ) :
    leadPair N (Finsupp.single (.inr (.inr q)) e) = (1, q.1 ^ e) := by
  simp [leadPair, Finsupp.prod_single_index]

/-- Admissible pairs are closed under products. -/
theorem IsPair.mul' {l m l' m' : ℕ} (h : IsPair N l m) (h' : IsPair N l' m') :
    IsPair N (l * l') (m * m') :=
  ⟨Nat.mul_pos h.1 h'.1, Nat.mul_dvd_mul h.2.1 h'.2.1, Nat.Coprime.mul_left h.2.2 h'.2.2⟩

/-- The leading pair is admissible, and its second entry is positive. -/
theorem isPair_leadPair_aux (s : HeckeGenerators N →₀ ℕ) :
    IsPair N (leadPair N s).1 (leadPair N s).2 ∧ 0 < (leadPair N s).2 := by
  induction s using Finsupp.induction_linear with
  | zero => simp [leadPair_zero, IsPair]
  | add s t hs ht =>
    rw [leadPair_add]
    exact ⟨hs.1.mul' N ht.1, Nat.mul_pos hs.2 ht.2⟩
  | single j e =>
    rcases j with ⟨p, hp, hpN⟩ | ⟨p, hp, hpN⟩ | ⟨q, hq, hqN⟩
    · rw [leadPair_single_inl]
      exact ⟨⟨one_pos, one_dvd _, Nat.coprime_one_left _⟩, pow_pos hp.pos _⟩
    · rw [leadPair_single_inr_inl]
      exact ⟨isPair_pow N hp hpN le_rfl, pow_pos hp.pos _⟩
    · rw [leadPair_single_inr_inr]
      exact ⟨⟨one_pos, one_dvd _, Nat.coprime_one_left _⟩, pow_pos hq.pos _⟩

/-- The leading pair is admissible. -/
theorem isPair_leadPair (s : HeckeGenerators N →₀ ℕ) :
    IsPair N (leadPair N s).1 (leadPair N s).2 :=
  (isPair_leadPair_aux N s).1

/-- The second entry of the leading pair is positive. -/
theorem leadPair_snd_pos (s : HeckeGenerators N →₀ ℕ) : 0 < (leadPair N s).2 :=
  (isPair_leadPair_aux N s).2

/-- The `p`-adic valuation of `L` is the exponent of `T(p, p)`. -/
theorem leadPair_fst_factorization {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (s : HeckeGenerators N →₀ ℕ) :
    (leadPair N s).1.factorization p = s (.inr (.inl ⟨p, hp, hpN⟩)) := by
  induction s using Finsupp.induction_linear with
  | zero => simp [leadPair_zero]
  | add s t hs ht =>
    rw [leadPair_add, Nat.factorization_mul (isPair_leadPair N s).1.ne'
      (isPair_leadPair N t).1.ne', Finsupp.add_apply, hs, ht, Finsupp.add_apply]
  | single j e =>
    rcases j with ⟨r, hr, hrN⟩ | ⟨r, hr, hrN⟩ | ⟨r, hr, hrN⟩
    · simp [leadPair_single_inl]
    · rw [leadPair_single_inr_inl]
      by_cases h : r = p
      · subst h; simp [Nat.factorization_pow, hr.factorization]
      · simp [Nat.factorization_pow, hr.factorization, Finsupp.single_apply, h,
          Ne.symm h]
    · simp [leadPair_single_inr_inr]

/-- The `p`-adic valuation of `M` is `a_p + b_p`, for `p ∤ N`. -/
theorem leadPair_snd_factorization_good {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (s : HeckeGenerators N →₀ ℕ) :
    (leadPair N s).2.factorization p =
      s (.inl ⟨p, hp, hpN⟩) + s (.inr (.inl ⟨p, hp, hpN⟩)) := by
  induction s using Finsupp.induction_linear with
  | zero => simp [leadPair_zero]
  | add s t hs ht =>
    rw [leadPair_add, Nat.factorization_mul (leadPair_snd_pos N s).ne'
      (leadPair_snd_pos N t).ne', Finsupp.add_apply, hs, ht]
    simp only [Finsupp.add_apply]
    ring
  | single j e =>
    rcases j with ⟨r, hr, hrN⟩ | ⟨r, hr, hrN⟩ | ⟨r, hr, hrN⟩
    · rw [leadPair_single_inl]
      by_cases h : r = p
      · subst h; simp [Nat.factorization_pow, hr.factorization]
      · simp [Nat.factorization_pow, hr.factorization, Finsupp.single_apply, h,
          Ne.symm h]
    · rw [leadPair_single_inr_inl]
      by_cases h : r = p
      · subst h; simp [Nat.factorization_pow, hr.factorization]
      · simp [Nat.factorization_pow, hr.factorization, Finsupp.single_apply, h,
          Ne.symm h]
    · rw [leadPair_single_inr_inr]
      have h : r ≠ p := fun h ↦ hpN (h ▸ hrN)
      simp [Nat.factorization_pow, hr.factorization, Finsupp.single_apply, h,
          Ne.symm h]

/-- The `q`-adic valuation of `M` is the exponent of `T(q)`, for `q ∣ N`. -/
theorem leadPair_snd_factorization_bad {q : ℕ} (hq : q.Prime) (hqN : q ∣ N)
    (s : HeckeGenerators N →₀ ℕ) :
    (leadPair N s).2.factorization q = s (.inr (.inr ⟨q, hq, hqN⟩)) := by
  induction s using Finsupp.induction_linear with
  | zero => simp [leadPair_zero]
  | add s t hs ht =>
    rw [leadPair_add, Nat.factorization_mul (leadPair_snd_pos N s).ne'
      (leadPair_snd_pos N t).ne', Finsupp.add_apply, hs, ht, Finsupp.add_apply]
  | single j e =>
    rcases j with ⟨r, hr, hrN⟩ | ⟨r, hr, hrN⟩ | ⟨r, hr, hrN⟩
    · rw [leadPair_single_inl]
      have h : r ≠ q := fun h ↦ hrN (h ▸ hqN)
      simp [Nat.factorization_pow, hr.factorization, Finsupp.single_apply, h, Ne.symm h]
    · rw [leadPair_single_inr_inl]
      have h : r ≠ q := fun h ↦ hrN (h ▸ hqN)
      simp [Nat.factorization_pow, hr.factorization, Finsupp.single_apply, h, Ne.symm h]
    · rw [leadPair_single_inr_inr]
      by_cases h : r = q
      · subst h; simp [Nat.factorization_pow, hr.factorization]
      · simp [Nat.factorization_pow, hr.factorization, Finsupp.single_apply, h,
          Ne.symm h]

/-- The exponents are determined by the leading pair. -/
theorem leadPair_injective : Function.Injective (leadPair N) := by
  intro s t h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  ext j
  rcases j with ⟨p, hp, hpN⟩ | ⟨p, hp, hpN⟩ | ⟨q, hq, hqN⟩
  · have e1 := leadPair_fst_factorization N hp hpN s
    have e2 := leadPair_fst_factorization N hp hpN t
    have e3 := leadPair_snd_factorization_good N hp hpN s
    have e4 := leadPair_snd_factorization_good N hp hpN t
    rw [h1] at e1
    rw [h2] at e3
    omega
  · rw [← leadPair_fst_factorization N hp hpN s, ← leadPair_fst_factorization N hp hpN t, h1]
  · rw [← leadPair_snd_factorization_bad N hq hqN s, ← leadPair_snd_factorization_bad N hq hqN t,
      h2]

/-- The monomial `∏ gen i ^ s i` in the Hecke ring. -/
def genMonomial (s : HeckeGenerators N →₀ ℕ) : HeckeRingGamma0 N :=
  s.prod fun i e ↦ heckeGenerator N i ^ e

/-- The monomial is multiplicative in the exponent vector. -/
theorem genMonomial_add (s t : HeckeGenerators N →₀ ℕ) :
    genMonomial N (s + t) = genMonomial N s * genMonomial N t :=
  Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _)

/-- The monomial of a single generator power. -/
theorem genMonomial_single (i : HeckeGenerators N) (e : ℕ) :
    genMonomial N (Finsupp.single i e) = heckeGenerator N i ^ e :=
  Finsupp.prod_single_index (pow_zero _)

/-- The leading-term property of the monomial `s`. -/
def Rd (s : HeckeGenerators N →₀ ℕ) : Prop :=
  Lead N (genMonomial N s) (leadPair N s).1 (leadPair N s).2

/-- Monomials with coprime determinants multiply. -/
theorem Rd.add {s t : HeckeGenerators N →₀ ℕ} (h1 : Rd N s) (h2 : Rd N t)
    (hc : ((leadPair N s).1 * (leadPair N s).2).Coprime
      ((leadPair N t).1 * (leadPair N t).2)) : Rd N (s + t) := by
  unfold Rd at *
  rw [genMonomial_add, leadPair_add]
  exact Lead.mul N h1 h2 (isPair_leadPair N s) (isPair_leadPair N t) hc

/-- If no generator in the support of `t` has prime `p`, then `p` is prime to the determinant
of the leading pair of `t`. -/
theorem coprime_det_leadPair {p : ℕ} (hp : p.Prime) {t : HeckeGenerators N →₀ ℕ}
    (ht : ∀ j ∈ t.support, genPrime N j ≠ p) :
    p.Coprime ((leadPair N t).1 * (leadPair N t).2) := by
  unfold leadPair
  dsimp only
  simp only [Finsupp.prod]
  refine Nat.Coprime.mul_right (Nat.Coprime.prod_right fun j hj ↦ ?_)
    (Nat.Coprime.prod_right fun j hj ↦ ?_)
  · have hne := ht j hj
    rcases j with ⟨r, hr, hrN⟩ | ⟨r, hr, hrN⟩ | ⟨r, hr, hrN⟩
    · exact Nat.coprime_one_right _
    · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hr).2 (Ne.symm hne))
    · exact Nat.coprime_one_right _
  · have hne := ht j hj
    rcases j with ⟨r, hr, hrN⟩ | ⟨r, hr, hrN⟩ | ⟨r, hr, hrN⟩
    · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hr).2 (Ne.symm hne))
    · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hr).2 (Ne.symm hne))
    · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hr).2 (Ne.symm hne))

/-- Splitting off the generators of a good prime `p`. -/
theorem Rd.of_erase_good {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (s : HeckeGenerators N →₀ ℕ)
    (h2 : Rd N ((s.erase (Sum.inl ⟨p, hp, hpN⟩)).erase (Sum.inr (Sum.inl ⟨p, hp, hpN⟩)))) :
    Rd N s := by
  have hab : (Sum.inl ⟨p, hp, hpN⟩ : HeckeGenerators N) ≠ Sum.inr (Sum.inl ⟨p, hp, hpN⟩) := by
    simp
  have hs : s = (Finsupp.single (Sum.inl ⟨p, hp, hpN⟩ : HeckeGenerators N)
        (s (Sum.inl ⟨p, hp, hpN⟩)) +
      Finsupp.single (Sum.inr (Sum.inl ⟨p, hp, hpN⟩) : HeckeGenerators N)
        (s (Sum.inr (Sum.inl ⟨p, hp, hpN⟩)))) +
      (s.erase (Sum.inl ⟨p, hp, hpN⟩)).erase (Sum.inr (Sum.inl ⟨p, hp, hpN⟩)) := by
    ext j
    simp only [Finsupp.add_apply, Finsupp.single_apply, Finsupp.erase_apply]
    by_cases ha : j = Sum.inl ⟨p, hp, hpN⟩
    · subst ha
      simp [hab]
    · by_cases hb : j = Sum.inr (Sum.inl ⟨p, hp, hpN⟩)
      · subst hb
        simp [hab.symm]
      · simp [Ne.symm ha, Ne.symm hb, ha, hb]
  have hlead : ∀ α β : ℕ, leadPair N (Finsupp.single (Sum.inl ⟨p, hp, hpN⟩ : HeckeGenerators N) α +
      Finsupp.single (Sum.inr (Sum.inl ⟨p, hp, hpN⟩) : HeckeGenerators N) β) =
      (p ^ β, p ^ (α + β)) := by
    intro α β
    rw [leadPair_add, leadPair_single_inl, leadPair_single_inr_inl]
    simp [pow_add]
  have h1 : Rd N (Finsupp.single (Sum.inl ⟨p, hp, hpN⟩ : HeckeGenerators N)
        (s (Sum.inl ⟨p, hp, hpN⟩)) +
      Finsupp.single (Sum.inr (Sum.inl ⟨p, hp, hpN⟩) : HeckeGenerators N)
        (s (Sum.inr (Sum.inl ⟨p, hp, hpN⟩)))) := by
    unfold Rd
    rw [hlead, genMonomial_add, genMonomial_single, genMonomial_single]
    have e1 : heckeGenerator N (Sum.inl ⟨p, hp, hpN⟩) = heckeTPair N 1 p :=
      HeckeRing.GL2.heckeTGeneratorGamma0_def N p
    have e2 : heckeGenerator N (Sum.inr (Sum.inl ⟨p, hp, hpN⟩)) = heckeTPair N p p :=
      HeckeRing.GL2.heckeTScalarGamma0_def N p
    rw [e1, e2]
    exact lead_good N hp hpN _ _
  have hj : ∀ j ∈ ((s.erase (Sum.inl ⟨p, hp, hpN⟩)).erase
      (Sum.inr (Sum.inl ⟨p, hp, hpN⟩))).support, genPrime N j ≠ p := by
    intro j hj h
    rw [Finsupp.support_erase, Finset.mem_erase, Finsupp.support_erase, Finset.mem_erase] at hj
    obtain ⟨hjb, hja, -⟩ := hj
    rcases j with ⟨r, hr, hrN⟩ | ⟨r, hr, hrN⟩ | ⟨r, hr, hrN⟩
    · have h' : r = p := h
      subst h'
      exact hja rfl
    · have h' : r = p := h
      subst h'
      exact hjb rfl
    · have h' : r = p := h
      subst h'
      exact hpN hrN
  have hcop := coprime_det_leadPair N hp hj
  rw [hs]
  refine Rd.add N h1 h2 ?_
  rw [hlead]
  exact Nat.Coprime.mul_left (Nat.Coprime.pow_left _ hcop) (Nat.Coprime.pow_left _ hcop)

/-- Splitting off the generator of a bad prime `q`. -/
theorem Rd.of_erase_bad {q : ℕ} (hq : q.Prime) (hqN : q ∣ N) (s : HeckeGenerators N →₀ ℕ)
    (h2 : Rd N (s.erase (Sum.inr (Sum.inr ⟨q, hq, hqN⟩)))) : Rd N s := by
  have hs : s = Finsupp.single (Sum.inr (Sum.inr ⟨q, hq, hqN⟩) : HeckeGenerators N)
        (s (Sum.inr (Sum.inr ⟨q, hq, hqN⟩))) +
      s.erase (Sum.inr (Sum.inr ⟨q, hq, hqN⟩)) :=
    (Finsupp.single_add_erase _ _).symm
  have h1 : Rd N (Finsupp.single (Sum.inr (Sum.inr ⟨q, hq, hqN⟩) : HeckeGenerators N)
        (s (Sum.inr (Sum.inr ⟨q, hq, hqN⟩)))) := by
    unfold Rd
    rw [leadPair_single_inr_inr, genMonomial_single]
    have e1 : heckeGenerator N (Sum.inr (Sum.inr ⟨q, hq, hqN⟩)) = heckeTPair N 1 q :=
      HeckeRing.GL2.heckeTGeneratorGamma0_def N q
    rw [e1]
    exact lead_bad N hq hqN _
  have hj : ∀ j ∈ (s.erase (Sum.inr (Sum.inr ⟨q, hq, hqN⟩))).support, genPrime N j ≠ q := by
    intro j hj h
    rw [Finsupp.support_erase, Finset.mem_erase] at hj
    obtain ⟨hja, -⟩ := hj
    rcases j with ⟨r, hr, hrN⟩ | ⟨r, hr, hrN⟩ | ⟨r, hr, hrN⟩
    · have h' : r = q := h
      subst h'
      exact hrN hqN
    · have h' : r = q := h
      subst h'
      exact hrN hqN
    · have h' : r = q := h
      subst h'
      exact hja rfl
  have hcop := coprime_det_leadPair N hq hj
  rw [hs]
  refine Rd.add N h1 h2 ?_
  rw [leadPair_single_inr_inr]
  simpa using Nat.Coprime.pow_left _ hcop

/-- Every monomial has the leading-term property. -/
theorem Rd_all (s : HeckeGenerators N →₀ ℕ) : Rd N s := by
  suffices h : ∀ n, ∀ s : HeckeGenerators N →₀ ℕ, s.support.card = n → Rd N s from
    h _ s rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hn
    by_cases hs0 : s = 0
    · subst hs0
      simp [Rd, genMonomial, leadPair_zero, Lead, heckeTPair_one_one]
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.2 hs0
    have hlt : ∀ a : HeckeGenerators N, i = a → (s.erase a).support.card < n := by
      intro a ha
      rw [Finsupp.support_erase, ← hn]
      exact Finset.card_erase_lt_of_mem (ha ▸ hi)
    rcases i with ⟨p, hp, hpN⟩ | ⟨p, hp, hpN⟩ | ⟨q, hq, hqN⟩
    · refine Rd.of_erase_good N hp hpN s (ih _ ?_ _ rfl)
      simp only [Finsupp.support_erase]
      exact lt_of_le_of_lt Finset.card_erase_le (hn ▸ Finset.card_erase_lt_of_mem hi)
    · refine Rd.of_erase_good N hp hpN s (ih _ ?_ _ rfl)
      simp only [Finsupp.support_erase]
      have hb : (Sum.inr (Sum.inl ⟨p, hp, hpN⟩) : HeckeGenerators N) ∈
          s.support.erase (Sum.inl ⟨p, hp, hpN⟩) := Finset.mem_erase.2 ⟨by simp, hi⟩
      exact lt_of_lt_of_le (Finset.card_erase_lt_of_mem hb)
        (Finset.card_erase_le.trans hn.le)
    · exact Rd.of_erase_bad N hq hqN s (ih _ (hlt _ rfl) _ rfl)

/-- **The leading term of a monomial**: the image of the monomial `s` is `T(L, M)` plus an element
of `upper L M`. -/
theorem aeval_monomial_lead (s : HeckeGenerators N →₀ ℕ) :
    MvPolynomial.aeval (heckeGenerator N) (MvPolynomial.monomial s (1 : ℤ)) -
        heckeTPair N (leadPair N s).1 (leadPair N s).2 ∈
      upper N (leadPair N s).1 (leadPair N s).2 := by
  have h : MvPolynomial.aeval (heckeGenerator N) (MvPolynomial.monomial s (1 : ℤ)) =
      genMonomial N s := by
    rw [MvPolynomial.aeval_monomial, map_one, one_mul]
    rfl
  rw [h]
  exact Rd_all N s

/-- The `T(L₀, M₀)`-coefficient of a monomial, for `(L₀, M₀)` the leading pair of `s₀` and
`L₀ ≤ L_s`: it is `1` at `s = s₀` and `0` otherwise. -/
theorem pairCoeff_aeval_monomial {s0 s : HeckeGenerators N →₀ ℕ} (c : ℤ)
    (hmin : (leadPair N s0).1 ≤ (leadPair N s).1) :
    pairCoeff N (leadPair N s0).1 (leadPair N s0).2
        (MvPolynomial.aeval (heckeGenerator N) (MvPolynomial.monomial s c)) =
      if s = s0 then c else 0 := by
  have hmono : MvPolynomial.monomial s c = c • MvPolynomial.monomial s (1 : ℤ) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have h := aeval_monomial_lead N s
  have hsplit : MvPolynomial.aeval (heckeGenerator N) (MvPolynomial.monomial s (1 : ℤ)) =
      heckeTPair N (leadPair N s).1 (leadPair N s).2 +
        (MvPolynomial.aeval (heckeGenerator N) (MvPolynomial.monomial s (1 : ℤ)) -
          heckeTPair N (leadPair N s).1 (leadPair N s).2) := by abel
  rw [hmono, map_zsmul, map_zsmul, hsplit, map_add,
    pairCoeff_eq_zero_of_mem_upper N (isPair_leadPair N s0) (leadPair_snd_pos N s0) hmin h,
    add_zero, pairCoeff_heckeTPair N (isPair_leadPair N s0) (isPair_leadPair N s)
      (leadPair_snd_pos N s0)]
  by_cases hs : s = s0
  · subst hs; simp
  · have : ¬ ((leadPair N s0).1 = (leadPair N s).1 ∧ (leadPair N s0).2 = (leadPair N s).2) :=
      fun h ↦ hs (leadPair_injective N (Prod.ext h.1.symm h.2.symm))
    simp [this, hs]

/-- **Miyake, Theorem 4.5.9**, independence half: `T(p)`, `T(p, p)` (`p ∤ N`) and `T(q)`
(`q ∣ N`) are algebraically independent over `ℤ`. -/
@[kb "miyake1989" "Theorem 4.5.9, p. 142 (independence)"]
theorem aeval_heckeGenerator_injective :
    Function.Injective (MvPolynomial.aeval (R := ℤ) (heckeGenerator N)) := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  by_contra hne
  have hsupp : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hne
  obtain ⟨s0, hs0, hmin⟩ := P.support.exists_min_image (fun s ↦ (leadPair N s).1) hsupp
  have key : pairCoeff N (leadPair N s0).1 (leadPair N s0).2
      (MvPolynomial.aeval (heckeGenerator N) P) = P.coeff s0 := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum, map_sum, Finset.sum_eq_single s0]
    · rw [pairCoeff_aeval_monomial N _ le_rfl, if_pos rfl]
    · intro s hs hne
      rw [pairCoeff_aeval_monomial N _ (hmin s hs), if_neg hne]
    · intro h; exact absurd hs0 h
  rw [hP, map_zero] at key
  exact (MvPolynomial.mem_support_iff.1 hs0) key.symm

/-- **Miyake, Theorem 4.5.9**: `ℛ(N)` is the polynomial ring over `ℤ` in `T(p)`, `T(p, p)`
(`p ∤ N`) and `T(q)` (`q ∣ N`). -/
@[kb "miyake1989" "Theorem 4.5.9, p. 142"]
theorem heckeAlgebraPolynomial : HeckeAlgebraPolynomialStatement N := by
  have hsurj : Function.Surjective (MvPolynomial.aeval (R := ℤ) (heckeGenerator N)) := by
    intro y
    have hy : y ∈ Subring.closure (Set.range (heckeGenerator N)) := by
      rw [Wave5.closure_heckeGenerator_eq_top N]; trivial
    have hy' : y ∈ (MvPolynomial.aeval (R := ℤ) (heckeGenerator N)).range := by
      rw [MvPolynomial.aeval_range, Algebra.mem_adjoin_iff]
      exact Subring.closure_mono Set.subset_union_right hy
    exact (AlgHom.mem_range _).1 hy'
  refine ⟨⟨RingEquiv.ofBijective (MvPolynomial.aeval (R := ℤ) (heckeGenerator N))
    ⟨aeval_heckeGenerator_injective N, hsurj⟩, fun i ↦ ?_⟩⟩
  exact MvPolynomial.aeval_X _ _

end ModularFormsKB.Miyake.Wave6
