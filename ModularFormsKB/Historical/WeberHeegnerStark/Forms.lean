import ModularFormsKB.Historical.WeberHeegnerStark.Defs
import Mathlib.NumberTheory.FundamentalDiscriminant

/-!
# Reduced forms of negative discriminant: the elementary reduction

Gauss's theory of reduced forms (Gauss, *Disquisitiones Arithmeticae* §§ 171–172; Cox, *Primes of the
form x² + ny²*, § 2) says that a reduced primitive positive definite form `a x² + b x y + c y²` of
discriminant `D < 0` satisfies `|b| ≤ a ≤ c`, hence `4a² ≤ 4ac = b² - D ≤ a² + |D|` and `3a² ≤ |D|`.
So only finitely many `(a, b, c)` occur, and `reducedForms D` is the set of those satisfying
`IsReducedForm D a b c` (`mem_reducedForms`).

Consequences proved here, all elementary:

* `formClassNumber_eq_one_of_mem`: the nine discriminants of class number one have exactly one reduced
  form (by kernel computation).
* `eq_of_formClassNumber_eq_one`: if `D < 0` is a fundamental discriminant with `h(D) = 1`, then
  `D ∈ {-3, -4, -7, -8}` or `D = -p` with `p` prime, `p ≡ 3 mod 8`. Proof: besides the principal form
  (`a = 1`) one exhibits a second reduced form with `a ≥ 2`, in every case but these. For `D = -4m`
  these are `(2, 2, (m+1)/2)` and `(2, 0, m/2)`; for `D = -n` with `n ≡ 7 mod 8` the form
  `(2, 1, (n+1)/8)`; for composite `n ≡ 3 mod 8` with `n = q r`, `q < r`, the form `(q, q, (q+r)/4)`
  if `r ≥ 3q` and `((q+r)/4, (r-q)/2, (q+r)/4)` otherwise. For odd squarefree discriminants
  primitivity is automatic (`isPrimitiveForm_of_squarefree`).
-/

namespace ModularFormsKB.WeberHeegnerStark

/-- A form with leading coefficient `1` is primitive. -/
theorem isPrimitiveForm_one (b c : ℤ) : IsPrimitiveForm 1 b c := by
  simp [IsPrimitiveForm]

/-- A reduced form of negative discriminant `D` lies in `reducedForms D`, and conversely. -/
theorem mem_reducedForms {D a b c : ℤ} (hD : D < 0) :
    (a, b, c) ∈ reducedForms D ↔ IsReducedForm D a b c := by
  unfold reducedForms
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_product, Finset.mem_Icc,
    Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    have hb := abs_le.mp h3
    have hN : a ≤ (Nat.sqrt D.natAbs : ℤ) := by
      by_contra hlt
      have h7 : (Nat.sqrt D.natAbs : ℤ) + 1 ≤ a := by omega
      have h8 := Nat.lt_succ_sqrt D.natAbs
      have h9 : (D.natAbs : ℤ) = -D := Int.ofNat_natAbs_of_nonpos hD.le
      have h10 : ((D.natAbs : ℕ) : ℤ) < ((Nat.sqrt D.natAbs + 1) * (Nat.sqrt D.natAbs + 1) : ℕ) := by
        exact_mod_cast h8
      push_cast at h10
      rw [abs_of_neg hD] at h10
      have hb2 : b ^ 2 ≤ a ^ 2 := by nlinarith [sq_abs b, abs_nonneg b]
      nlinarith
    refine ⟨a, b, ⟨⟨by omega, hN⟩, ⟨by omega, by omega⟩⟩, rfl, rfl, ?_⟩
    have : (b ^ 2 - D) = 4 * a * c := by linarith
    rw [this]
    have : (4 * a : ℤ) ≠ 0 := by omega
    exact Int.mul_ediv_cancel_left c this

/-- Every `D < 0` with `D ≡ 0, 1 mod 4` has a reduced form with leading coefficient `1`. -/
theorem exists_principal {D : ℤ} (hD : D < 0) (h4 : D % 4 = 0 ∨ D % 4 = 1) :
    ∃ b c, IsReducedForm D 1 b c := by
  rcases h4 with h | h
  · refine ⟨0, -D / 4, ?_, by norm_num, by simp, by omega, fun _ => le_rfl,
      isPrimitiveForm_one _ _⟩
    norm_num; omega
  · refine ⟨1, (1 - D) / 4, ?_, by norm_num, by simp, by omega, fun _ => by norm_num,
      isPrimitiveForm_one _ _⟩
    norm_num; omega

/-- A reduced form with `a ≥ 2` gives class number at least `2` (besides the principal form). -/
theorem two_le_formClassNumber {D a b c : ℤ} (hD : D < 0) (h4 : D % 4 = 0 ∨ D % 4 = 1)
    (h : IsReducedForm D a b c) (ha : 2 ≤ a) : 2 ≤ formClassNumber D := by
  obtain ⟨b0, c0, h0⟩ := exists_principal hD h4
  unfold formClassNumber
  apply Finset.one_lt_card.mpr
  refine ⟨(1, b0, c0), (mem_reducedForms hD).2 h0, (a, b, c), (mem_reducedForms hD).2 h, ?_⟩
  intro e
  have := congrArg Prod.fst e
  simp at this
  omega

/-- If the discriminant of `a x² + b x y + c y²` has squarefree absolute value, the form is
primitive: `g = gcd(a, b, c)` has `g² ∣ D`. -/
theorem isPrimitiveForm_of_squarefree {D a b c : ℤ} (hD : b ^ 2 - 4 * a * c = D)
    (h : Squarefree D.natAbs) : IsPrimitiveForm a b c := by
  unfold IsPrimitiveForm
  set g := Int.gcd (Int.gcd a b) c with hg
  have hc : (g : ℤ) ∣ c := Int.gcd_dvd_right _ _
  have h2 : (g : ℤ) ∣ (Int.gcd a b : ℤ) := Int.gcd_dvd_left _ _
  have ha : (g : ℤ) ∣ a := h2.trans (Int.gcd_dvd_left _ _)
  have hb : (g : ℤ) ∣ b := h2.trans (Int.gcd_dvd_right _ _)
  have h3 : (g : ℤ) * g ∣ D := by
    rw [← hD, sq]
    exact dvd_sub (mul_dvd_mul hb hb) (mul_dvd_mul (ha.mul_left 4) hc)
  have h4 : g * g ∣ D.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr h3
    simpa [Int.natAbs_mul] using this
  exact Nat.isUnit_iff.mp (h g h4)

/-- For `D ≡ 1 mod 4` satisfying the odd-prime clause of `Int.IsFundamentalDiscr`, `|D|` is
squarefree. -/
theorem squarefree_natAbs_of_odd {D : ℤ} (h1 : D % 4 = 1)
    (hp : ∀ p : ℕ, p.Prime → Odd p → ¬ (p : ℤ) ^ 2 ∣ D) : Squarefree D.natAbs := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hpp hdvd
  rcases hpp.eq_two_or_odd' with h2 | ho
  · subst h2
    omega
  · apply hp p hpp ho
    apply Int.natCast_dvd.2
    rw [sq]
    exact_mod_cast hdvd

theorem gcd_two_of_odd {c : ℤ} (hc : c % 2 = 1) : Int.gcd 2 c = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, c = 2 * k + 1 := ⟨c / 2, by omega⟩
  have : IsCoprime (2 : ℤ) c := ⟨-k, 1, by rw [hk]; ring⟩
  exact Int.isCoprime_iff_gcd_eq_one.mp this

/-- The even case: `D = 4x`; apart from `-4, -8` there is a reduced form with `a = 2`. -/
theorem exists_second_even {D : ℤ} (hD : D < 0)
    (hx : ∀ x, D = 4 * x → ¬ 4 ∣ x ∧ x % 4 ≠ 1) (h0 : D % 4 = 0) :
    D = -4 ∨ D = -8 ∨ ∃ a b c, IsReducedForm D a b c ∧ 2 ≤ a := by
  obtain ⟨x, rfl⟩ : ∃ x, D = 4 * x := ⟨D / 4, by omega⟩
  have := hx x rfl
  have hx4 : x % 4 = 2 ∨ x % 4 = 3 := by omega
  rcases hx4 with h | h
  · by_cases hx2 : x = -2
    · right; left; omega
    · right; right
      refine ⟨2, 0, -x / 2, ⟨?_, by norm_num, by simp, by omega, fun _ => le_rfl, ?_⟩, le_rfl⟩
      · norm_num; omega
      · have : Int.gcd 2 0 = 2 := rfl
        unfold IsPrimitiveForm
        rw [this]
        exact gcd_two_of_odd (by omega)
  · by_cases hx1 : x = -1
    · left; omega
    · right; right
      refine ⟨2, 2, (1 - x) / 2, ⟨?_, by norm_num, by simp, by omega, fun _ => by norm_num, ?_⟩,
        le_rfl⟩
      · omega
      · have : Int.gcd 2 2 = 2 := rfl
        unfold IsPrimitiveForm
        rw [this]
        exact gcd_two_of_odd (by omega)

/-- The composite case, in integers: `n = q r` with `3 ≤ q < r` odd and `q + r ≡ 0 mod 4`. -/
theorem exists_second_composite {D q r : ℤ} (hD : D = -(q * r)) (hq3 : 3 ≤ q) (hqr : q < r)
    (hq2 : q % 2 = 1) (hr2 : r % 2 = 1) (h4 : (q + r) % 4 = 0) (hs : Squarefree D.natAbs) :
    ∃ a b c, IsReducedForm D a b c ∧ 2 ≤ a := by
  obtain ⟨k, hk⟩ : ∃ k, q + r = 4 * k := ⟨(q + r) / 4, by omega⟩
  by_cases hr : 3 * q ≤ r
  · have hd : q ^ 2 - 4 * q * k = D := by linear_combination q * hk - hD
    exact ⟨q, q, k, ⟨hd, by omega, by rw [abs_of_pos (by omega)], by omega,
      fun _ => by omega, isPrimitiveForm_of_squarefree hd hs⟩, by omega⟩
  · obtain ⟨t, ht⟩ : ∃ t, r - q = 2 * t := ⟨(r - q) / 2, by omega⟩
    have e1 : t - 2 * k = -q := by omega
    have e2 : t + 2 * k = r := by omega
    have hd : t ^ 2 - 4 * k * k = D := by
      have : t ^ 2 - 4 * k * k = (t - 2 * k) * (t + 2 * k) := by ring
      rw [this, e1, e2, hD]; ring
    refine ⟨k, t, k, ⟨hd, by omega, ?_, le_rfl, fun _ => by omega,
      isPrimitiveForm_of_squarefree hd hs⟩, by omega⟩
    rw [abs_of_pos (by omega)]; omega

/-- The odd case: `D ≡ 1 mod 4`; apart from the listed discriminants there is a reduced form with
`a ≥ 2`. -/
theorem exists_second_odd {D : ℤ} (hD : D < 0) (h1 : D % 4 = 1)
    (hp : ∀ p : ℕ, p.Prime → Odd p → ¬ (p : ℤ) ^ 2 ∣ D) :
    D = -3 ∨ D = -7 ∨ (∃ p : ℕ, p.Prime ∧ p % 8 = 3 ∧ D = -p) ∨
      ∃ a b c, IsReducedForm D a b c ∧ 2 ≤ a := by
  have hs := squarefree_natAbs_of_odd h1 hp
  obtain ⟨n, hn⟩ : ∃ n : ℕ, D = -(n : ℤ) := ⟨D.natAbs, by omega⟩
  have hnat : D.natAbs = n := by omega
  have h8 : n % 8 = 3 ∨ n % 8 = 7 := by omega
  rcases h8 with h8 | h8
  · by_cases hpr : n.Prime
    · right; right; left
      exact ⟨n, hpr, h8, hn⟩
    · right; right; right
      have hn1 : n ≠ 1 := by omega
      have hn0 : 0 < n := by omega
      set q := n.minFac with hqdef
      have hq : q.Prime := Nat.minFac_prime hn1
      obtain ⟨r, hr⟩ : q ∣ n := Nat.minFac_dvd n
      have hsq : q ^ 2 ≤ n := Nat.minFac_sq_le_self hn0 hpr
      have hsf : Squarefree (q * r) := by rw [← hr, ← hnat]; exact hs
      have hcop : Nat.Coprime q r := (Nat.squarefree_mul_iff.mp hsf).1
      have hodd : Odd (q * r) := by rw [← hr, Nat.odd_iff]; omega
      obtain ⟨hqo, hro⟩ := Nat.odd_mul.mp hodd
      rw [Nat.odd_iff] at hqo hro
      have hq2 := hq.two_le
      have hqle : q ≤ r := by
        rw [hr, pow_two] at hsq
        exact Nat.le_of_mul_le_mul_left hsq (by omega)
      have hqne : q ≠ r := by
        intro e
        rw [← e] at hcop
        simp [Nat.Coprime] at hcop
        omega
      have hn3 : (q * r) % 4 = 3 := by omega
      have h4 : (q + r) % 4 = 0 := by
        have := Nat.mul_mod q r 4
        rcases (by omega : q % 4 = 1 ∨ q % 4 = 3) with h | h <;>
          rcases (by omega : r % 4 = 1 ∨ r % 4 = 3) with h' | h' <;>
          rw [h, h'] at this <;> omega
      refine exists_second_composite (q := (q : ℤ)) (r := (r : ℤ)) ?_ (by omega) (by omega)
        (by omega) (by omega) (by omega) hs
      rw [hn, hr]; push_cast; ring
  · by_cases h7 : n = 7
    · right; left; omega
    · right; right; right
      refine ⟨2, 1, (1 - D) / 8, ⟨?_, by norm_num, by norm_num, by omega, fun _ => by norm_num,
        isPrimitiveForm_of_squarefree (D := D) ?_ hs⟩, le_rfl⟩ <;> (norm_num; omega)

/-- `D = -3, -4, -7, -8, -11, -19, -43, -67, -163` have exactly one reduced form (the principal
form), i.e. class number one. -/
theorem formClassNumber_eq_one_of_mem {D : ℤ}
    (hD : D ∈ ({-3, -4, -7, -8, -11, -19, -43, -67, -163} : Finset ℤ)) : formClassNumber D = 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- A fundamental discriminant `D < 0` of class number one is `-3, -4, -7, -8` or `-p` with `p`
prime, `p ≡ 3 mod 8` (the remaining case is Heegner–Stark territory). -/
theorem eq_of_formClassNumber_eq_one {D : ℤ} (hD : D < 0) (hf : Int.IsFundamentalDiscr D)
    (h1 : formClassNumber D = 1) :
    D ∈ ({-3, -4, -7, -8} : Finset ℤ) ∨ ∃ p : ℕ, p.Prime ∧ p % 8 = 3 ∧ D = -p := by
  obtain ⟨h4, hx, hp⟩ := hf
  rcases h4 with h0 | h1'
  · rcases exists_second_even hD hx h0 with h | h | ⟨a, b, c, hr, ha⟩
    · left; simp [h]
    · left; simp [h]
    · exfalso
      have := two_le_formClassNumber hD (Or.inl h0) hr ha
      omega
  · rcases exists_second_odd hD h1' hp with h | h | h | ⟨a, b, c, hr, ha⟩
    · left; simp [h]
    · left; simp [h]
    · right; exact h
    · exfalso
      have := two_le_formClassNumber hD (Or.inr h1') hr ha
      omega

end ModularFormsKB.WeberHeegnerStark
