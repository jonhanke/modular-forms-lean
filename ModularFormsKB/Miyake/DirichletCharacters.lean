import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import ModularFormsKB.Citation
/-!
# Miyake §3.1: Gauss sums of Dirichlet characters

Miyake, *Modular Forms* (Springer 1989), §3.1, pp. 79–83.

## Conventions
* A Dirichlet character modulo $m$ is Mathlib's `DirichletCharacter ℂ m`, a multiplicative
  character of `ZMod m` (value $0$ at non-units); Miyake's $\chi(a)$ for $a \in \mathbb Z$ is
  `χ (a : ZMod m)`.
* Miyake's Gauss sum $W(\chi) = \sum_{a=0}^{m-1} \chi(a) e^{2\pi i a/m}$ (3.1.5) is Mathlib's
  `gaussSum χ ZMod.stdAddChar`, where `ZMod.stdAddChar j` $= e^{2\pi i j/m}$. Miyake defines $W$ only
  for primitive $\chi$; the formula makes sense for every $\chi$.
* For characters $\chi$ mod $m$ and $\psi$ mod $n$ with $(m,n) = 1$, Miyake's product
  $(\chi\psi)(a) = \chi(a)\psi(a)$ is a character mod $mn$; in Lean it is the product of the
  characters induced to level $mn$ (`DirichletCharacter.changeLevel`).
-/

open Complex DirichletCharacter
open scoped Real

namespace ModularFormsKB.Miyake

/-- Splitting `range (l * m)` into `l` blocks of length `m`. -/
lemma sum_range_mul_split (f : ℕ → ℂ) (l m : ℕ) :
    ∑ a ∈ Finset.range (l * m), f a =
      ∑ b ∈ Finset.range l, ∑ d ∈ Finset.range m, f (b * m + d) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Summing over `range m` equals summing over `ZMod m`. -/
lemma sum_range_eq_sum_zmod {m : ℕ} [NeZero m] (g : ZMod m → ℂ) :
    ∑ a ∈ Finset.range m, g (a : ZMod m) = ∑ x : ZMod m, g x := by
  refine Finset.sum_nbij' (fun a => (a : ZMod m)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro a _; simp
  · intro x _; simp [ZMod.val_lt]
  · intro a ha
    simp only [Finset.mem_range] at ha
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt ha]
  · intro x _; simp
  · intro a _; rfl

/-- Geometric sum of roots of unity. -/
lemma sum_exp_range (l : ℕ) (hl : 0 < l) (q : ℤ) :
    ∑ b ∈ Finset.range l, exp (2 * π * I * b * q / l) =
      if (l : ℤ) ∣ q then (l : ℂ) else 0 := by
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have key : ∀ b : ℕ, exp (2 * π * I * b * q / l) = (exp (2 * π * I * q / l)) ^ b := by
    intro b; rw [← Complex.exp_nat_mul]; congr 1; ring
  simp_rw [key]
  split_ifs with h
  · obtain ⟨r, rfl⟩ := h
    have : exp (2 * π * I * ((l * r : ℤ) : ℂ) / l) = 1 := by
      rw [Complex.exp_eq_one_iff]; refine ⟨r, ?_⟩; push_cast; field_simp
    rw [this]; simp
  · have hne : exp (2 * π * I * q / l) ≠ 1 := by
      intro h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      apply h
      refine ⟨n, ?_⟩
      have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      field_simp at hn
      exact_mod_cast hn
    rw [geom_sum_eq hne, ← Complex.exp_nat_mul]
    have : exp (l * (2 * π * I * q / l)) = 1 := by
      rw [Complex.exp_eq_one_iff]; refine ⟨q, ?_⟩; field_simp
    rw [this]; simp

/-- Block decomposition of the sum in Lemma 3.1.3 (1). -/
lemma sum_mul_exp_split {m l : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hl : 0 < l) (q : ℤ) :
    ∑ a ∈ Finset.range (l * m), χ a * exp (2 * π * I * a * q / (l * m)) =
      (∑ d ∈ Finset.range m, χ d * exp (2 * π * I * d * q / (l * m))) *
        (if (l : ℤ) ∣ q then (l : ℂ) else 0) := by
  rw [← sum_exp_range l hl q, sum_range_mul_split, Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => ?_
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have h1 : ((b * m + d : ℕ) : ZMod m) = (d : ZMod m) := by simp
  rw [h1, mul_assoc (χ (d : ZMod m)), ← Complex.exp_add]
  congr 2
  push_cast
  field_simp
  ring

/-- Evaluation of the product of induced characters (coprime levels). -/
lemma prod_changeLevel_apply {m n : ℕ} [NeZero m] [NeZero n] (_hmn : m.Coprime n)
    (χ : DirichletCharacter ℂ m) (ψ : DirichletCharacter ℂ n) (x : ZMod (m * n)) :
    (χ.changeLevel (dvd_mul_right m n) * ψ.changeLevel (dvd_mul_left n m)) x =
      χ (ZMod.cast x) * ψ (ZMod.cast x) := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    rw [MulChar.coeToFun_mul, Pi.mul_apply, changeLevel_eq_cast_of_dvd,
      changeLevel_eq_cast_of_dvd]
  · rw [MulChar.map_nonunit _ hx]
    have hx' : ¬ (x.val.Coprime (m * n)) := by
      rwa [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
    rw [Nat.coprime_mul_iff_right, not_and_or] at hx'
    rcases hx' with h | h
    · have : ¬ IsUnit (ZMod.cast x : ZMod m) := by
        rw [ZMod.cast_eq_val, ZMod.isUnit_iff_coprime]
        exact h
      rw [MulChar.map_nonunit _ this, zero_mul]
    · have : ¬ IsUnit (ZMod.cast x : ZMod n) := by
        rw [ZMod.cast_eq_val, ZMod.isUnit_iff_coprime]
        exact h
      rw [MulChar.map_nonunit ψ this, mul_zero]

/-- The map `(b, c) ↦ b n + c m` is a bijection `ZMod m × ZMod n → ZMod (m n)`. -/
lemma crt_bijective {m n : ℕ} [NeZero m] [NeZero n] (hmn : m.Coprime n) :
    Function.Bijective (fun p : ZMod m × ZMod n =>
      (((p.1.val * n + p.2.val * m : ℕ)) : ZMod (m * n))) := by
  have hinj : Function.Injective (fun p : ZMod m × ZMod n =>
      (((p.1.val * n + p.2.val * m : ℕ)) : ZMod (m * n))) := by
    rintro ⟨b, c⟩ ⟨b', c'⟩ h
    simp only at h
    have h1 := congrArg (ZMod.castHom (dvd_mul_right m n) (ZMod m)) h
    have h2 := congrArg (ZMod.castHom (dvd_mul_left n m) (ZMod n)) h
    simp only [map_natCast] at h1 h2
    push_cast at h1 h2
    simp only [ZMod.natCast_self, ZMod.natCast_zmod_val, mul_zero, add_zero, zero_add] at h1 h2
    have hu1 : IsUnit (n : ZMod m) := (ZMod.isUnit_iff_coprime n m).2 hmn.symm
    have hu2 : IsUnit (m : ZMod n) := (ZMod.isUnit_iff_coprime m n).2 hmn
    have e1 : b = b' := hu1.mul_left_inj.1 h1
    have e2 : c = c' := hu2.mul_left_inj.1 h2
    rw [e1, e2]
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨hinj, ?_⟩
  simp [ZMod.card]

/-- `stdAddChar` on a natural number. -/
lemma stdAddChar_natCast' {N : ℕ} [NeZero N] (k : ℕ) :
    (ZMod.stdAddChar (N := N) (k : ZMod N) : ℂ) = exp (2 * π * I * k / N) := by
  have := ZMod.stdAddChar_coe (N := N) (k : ℤ)
  simpa using this

/-- The additive character on the combined residue `b n + c m`. -/
lemma stdAddChar_crt {m n : ℕ} [NeZero m] [NeZero n] (b : ZMod m) (c : ZMod n) :
    (ZMod.stdAddChar (N := m * n) ((b.val * n + c.val * m : ℕ) : ZMod (m * n)) : ℂ) =
      ZMod.stdAddChar b * ZMod.stdAddChar c := by
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  conv_rhs => rw [← ZMod.natCast_zmod_val b, ← ZMod.natCast_zmod_val c]
  rw [stdAddChar_natCast', stdAddChar_natCast', stdAddChar_natCast', ← Complex.exp_add]
  congr 1
  push_cast
  field_simp

/-- **Miyake, Lemma 3.1.2.** For Dirichlet characters $\chi$ mod $m$ and $\psi$ mod $n$ with
$(m, n) = 1$,
$$W(\chi\psi) = \chi(n)\,\psi(m)\,W(\chi)\,W(\psi).$$
Miyake assumes $\chi, \psi$ primitive of conductors $m, n$; the identity holds for all characters
(generalization). -/
@[kb "miyake1989" "Lemma 3.1.2, p. 81"]
theorem gaussSum_mul_of_coprime {m n : ℕ} [NeZero m] [NeZero n] (hmn : m.Coprime n)
    (χ : DirichletCharacter ℂ m) (ψ : DirichletCharacter ℂ n) :
    gaussSum (χ.changeLevel (dvd_mul_right m n) * ψ.changeLevel (dvd_mul_left n m))
        (ZMod.stdAddChar (N := m * n)) =
      χ n * ψ m * gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar := by
  unfold gaussSum
  rw [← (Equiv.ofBijective _ (crt_bijective hmn)).sum_comp, Fintype.sum_prod_type]
  have hterm : ∀ (b : ZMod m) (c : ZMod n),
      (χ.changeLevel (dvd_mul_right m n) * ψ.changeLevel (dvd_mul_left n m))
          ((Equiv.ofBijective _ (crt_bijective hmn)) (b, c)) *
        ZMod.stdAddChar ((Equiv.ofBijective _ (crt_bijective hmn)) (b, c)) =
      (χ n * (χ b * ZMod.stdAddChar b)) * (ψ m * (ψ c * ZMod.stdAddChar c)) := by
    intro b c
    simp only [Equiv.ofBijective_apply]
    rw [prod_changeLevel_apply hmn, stdAddChar_crt]
    have h1 : (ZMod.cast (((b.val * n + c.val * m : ℕ)) : ZMod (m * n)) : ZMod m) = b * n := by
      rw [ZMod.cast_natCast (dvd_mul_right m n)]
      push_cast
      simp
    have h2 : (ZMod.cast (((b.val * n + c.val * m : ℕ)) : ZMod (m * n)) : ZMod n) = c * m := by
      rw [ZMod.cast_natCast (dvd_mul_left n m)]
      push_cast
      simp
    rw [h1, h2, map_mul, map_mul]
    ring
  simp_rw [hterm]
  rw [← Fintype.sum_mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- **Miyake, Lemma 3.1.3 (1)**, case $l \nmid q$: for a Dirichlet character $\chi$ mod $m$ and
integers $l > 0$, $q$,
$$\sum_{a=0}^{lm-1} \chi(a)\, e^{2\pi i a q/(lm)} = 0 \quad\text{if } l \nmid q.$$ -/
@[kb "miyake1989" "Lemma 3.1.3 (1), p. 82"]
theorem sum_mul_exp_eq_zero {m l : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hl : 0 < l)
    {q : ℤ} (hq : ¬ (l : ℤ) ∣ q) :
    ∑ a ∈ Finset.range (l * m), χ a * exp (2 * π * I * a * q / (l * m)) = 0 := by
  rw [sum_mul_exp_split χ hl q]
  simp [hq]

/-- **Miyake, Lemma 3.1.3 (1)**, case $l \mid q$: with $r = q/l$,
$$\sum_{a=0}^{lm-1} \chi(a)\, e^{2\pi i a q/(lm)} = l \sum_{a=0}^{m-1} \chi(a)\, e^{2\pi i a r/m}.$$ -/
@[kb "miyake1989" "Lemma 3.1.3 (1), p. 82"]
theorem sum_mul_exp_eq_of_dvd {m l : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hl : 0 < l)
    {q r : ℤ} (hq : q = l * r) :
    ∑ a ∈ Finset.range (l * m), χ a * exp (2 * π * I * a * q / (l * m)) =
      l * ∑ a ∈ Finset.range m, χ a * exp (2 * π * I * a * r / m) := by
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hd : (l : ℤ) ∣ q := ⟨r, hq⟩
  rw [sum_mul_exp_split χ hl q]
  simp only [hd, ↓reduceIte]
  rw [mul_comm]
  refine congrArg (fun x => (l : ℂ) * x) (Finset.sum_congr rfl fun d _ => ?_)
  refine congrArg (fun y => χ (d : ZMod m) * y) (congrArg Complex.exp ?_)
  subst hq
  push_cast
  field_simp

/-- Sum over the multiples of `d` in `range (d * N)`. -/
lemma sum_range_dvd {d : ℕ} (hd : 0 < d) (N : ℕ) (f : ℕ → ℂ) :
    ∑ a ∈ Finset.range (d * N), (if d ∣ a then f a else 0) =
      ∑ n ∈ Finset.range N, f (d * n) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun a => a / d) (fun n => d * n) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    exact (Nat.div_lt_iff_lt_mul hd).2 (by rw [mul_comm]; exact ha.1)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    exact ⟨Nat.mul_lt_mul_of_pos_left hn hd, dvd_mul_right _ _⟩
  · intro a ha
    simp only [Finset.mem_filter] at ha
    exact Nat.mul_div_cancel' ha.2
  · intro n _
    exact Nat.mul_div_cancel_left n hd
  · intro a ha
    simp only [Finset.mem_filter] at ha
    simp [Nat.mul_div_cancel' ha.2]

/-- Gauss sum with a shift, for a primitive character (Miyake Lemma 3.1.1 (1)). -/
lemma sum_range_gauss_shift {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (hχ : χ.IsPrimitive) (r : ℤ) :
    ∑ a ∈ Finset.range m, χ a * exp (2 * π * I * a * r / m) =
      starRingEnd ℂ (χ (r : ZMod m)) * gaussSum χ ZMod.stdAddChar := by
  have h := gaussSum_mulShift_of_isPrimitive (e := ZMod.stdAddChar (N := m)) hχ (r : ZMod m)
  have h2 : starRingEnd ℂ (χ (r : ZMod m)) = χ⁻¹ (r : ZMod m) := by
    rw [← MulChar.star_apply']; rfl
  rw [h2, ← h]
  unfold gaussSum
  rw [← sum_range_eq_sum_zmod (fun x => χ x * (ZMod.stdAddChar.mulShift (r : ZMod m)) x)]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [AddChar.mulShift_apply]
  have := ZMod.stdAddChar_coe (N := m) (r * (a : ℤ))
  push_cast at this
  rw [this]
  congr 1
  ring

/-- Inner sum of Lemma 3.1.3 (2). -/
lemma sum_range_exp_primitive {m c : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (hχ : χ.IsPrimitive) (hc : 0 < c) (q : ℤ) :
    ∑ a ∈ Finset.range (c * m), χ a * exp (2 * π * I * a * q / (c * m)) =
      if (c : ℤ) ∣ q then
        (c : ℂ) * (starRingEnd ℂ (χ ((q / c : ℤ) : ZMod m)) * gaussSum χ ZMod.stdAddChar)
      else 0 := by
  by_cases h : (c : ℤ) ∣ q
  · have hd := h
    obtain ⟨r, hr⟩ := h
    rw [sum_mul_exp_eq_of_dvd χ hc hr, sum_range_gauss_shift hχ]
    have : q / c = r := by rw [hr]; exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hc.ne')
    rw [this]
    simp only [hd, ↓reduceIte]
  · rw [sum_mul_exp_eq_zero χ hc h]
    simp [h]

/-- Möbius sum over divisors. -/
lemma sum_moebius_divisors_complex (n : ℕ) :
    ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) = if n = 1 then 1 else 0 := by
  have h := DFunLike.congr_fun ArithmeticFunction.moebius_mul_coe_zeta n
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  have h' := congrArg (fun z : ℤ => (z : ℂ)) h
  simp only [Int.cast_sum] at h'
  rw [h']
  split_ifs <;> simp

/-- Coprimality indicator via the Möbius function. -/
lemma coprime_indicator {l : ℕ} (hl : 0 < l) (a : ℕ) :
    (if a.Coprime l then (1 : ℂ) else 0) =
      ∑ d ∈ l.divisors, if d ∣ a then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0 := by
  rw [← Finset.sum_filter]
  have : l.divisors.filter (· ∣ a) = (Nat.gcd a l).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h3, h1⟩, Nat.gcd_pos_of_pos_right _ hl |>.ne'⟩
    · rintro ⟨⟨h3, h1⟩, _⟩; exact ⟨⟨h1, hl.ne'⟩, h3⟩
  rw [this, sum_moebius_divisors_complex]

/-- Induced character on naturals. -/
lemma changeLevel_natCast {m l : ℕ} [NeZero m] [NeZero l] (χ : DirichletCharacter ℂ m) (a : ℕ) :
    χ.changeLevel (dvd_mul_left m l) (a : ZMod (l * m)) =
      if a.Coprime l then χ a else 0 := by
  by_cases hu : IsUnit (a : ZMod (l * m))
  · have hc : a.Coprime (l * m) := (ZMod.isUnit_iff_coprime a (l * m)).1 hu
    have hl : a.Coprime l := Nat.Coprime.coprime_mul_right_right hc
    split_ifs
    obtain ⟨u, hu'⟩ := hu
    rw [← hu', changeLevel_eq_cast_of_dvd, hu', ZMod.cast_natCast (dvd_mul_left m l)]
  · rw [MulChar.map_nonunit _ hu]
    by_cases hl : a.Coprime l
    · split_ifs
      by_cases hm : IsUnit (a : ZMod m)
      · exfalso; apply hu
        rw [ZMod.isUnit_iff_coprime] at hm ⊢
        exact Nat.Coprime.mul_right hl hm
      · rw [MulChar.map_nonunit _ hm]
    · simp [hl]

/-- **Miyake, Lemma 3.1.3 (2).** Let $\chi$ be a primitive character mod $m$ and $\chi'$ the
character mod $lm$ induced from $\chi$ ($l > 0$). For every integer $q$,
$$\sum_{a=0}^{lm-1} \chi'(a)\, e^{2\pi i a q/(lm)}
  = W(\chi) \sum_{0 < c \mid (l, q)} c\, \mu(l/c)\, \chi(l/c)\, \overline{\chi}(q/c),$$
with $\mu$ the Möbius function and $(l, 0) = l$. -/
@[kb "miyake1989" "Lemma 3.1.3 (2), p. 82"]
theorem sum_changeLevel_mul_exp {m l : ℕ} [NeZero m] [NeZero l] {χ : DirichletCharacter ℂ m}
    (hχ : χ.IsPrimitive) (q : ℤ) :
    ∑ a ∈ Finset.range (l * m),
        χ.changeLevel (dvd_mul_left m l) a * exp (2 * π * I * a * q / (l * m)) =
      gaussSum χ ZMod.stdAddChar *
        ∑ c ∈ (Int.gcd l q).divisors,
          c * ArithmeticFunction.moebius (l / c) * χ ((l / c : ℕ) : ZMod m) *
            starRingEnd ℂ (χ ((q / c : ℤ) : ZMod m)) := by
  have hl : 0 < l := Nat.pos_of_ne_zero (NeZero.ne l)
  set W := gaussSum χ ZMod.stdAddChar with hW
  -- step 1: Möbius expansion
  have step1 : ∑ a ∈ Finset.range (l * m),
        χ.changeLevel (dvd_mul_left m l) a * exp (2 * π * I * a * q / (l * m)) =
      ∑ d ∈ l.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑ a ∈ Finset.range (l * m),
          if d ∣ a then χ a * exp (2 * π * I * a * q / (l * m)) else 0 := by
    simp_rw [changeLevel_natCast]
    have : ∀ a : ℕ, (if a.Coprime l then χ a else 0) * exp (2 * π * I * a * q / (l * m)) =
        ∑ d ∈ l.divisors, if d ∣ a then
          (ArithmeticFunction.moebius d : ℂ) * (χ a * exp (2 * π * I * a * q / (l * m))) else 0 := by
      intro a
      have h := coprime_indicator hl a
      calc (if a.Coprime l then χ a else 0) * exp (2 * π * I * a * q / (l * m))
          = (if a.Coprime l then (1 : ℂ) else 0) *
              (χ a * exp (2 * π * I * a * q / (l * m))) := by
            split_ifs <;> simp
        _ = _ := by
            rw [h, Finset.sum_mul]
            refine Finset.sum_congr rfl fun d _ => ?_
            split_ifs <;> simp
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp
  -- step 2: each divisor
  have step2 : ∀ d ∈ l.divisors,
      (ArithmeticFunction.moebius d : ℂ) *
        ∑ a ∈ Finset.range (l * m),
          (if d ∣ a then χ a * exp (2 * π * I * a * q / (l * m)) else 0) =
      W * (if ((l / d : ℕ) : ℤ) ∣ q then
        ((l / d : ℕ) : ℂ) * (ArithmeticFunction.moebius d : ℂ) * χ ((d : ℕ) : ZMod m) *
          starRingEnd ℂ (χ ((q / ((l / d : ℕ) : ℤ) : ℤ) : ZMod m)) else 0) := by
    intro d hd
    have hdl : d ∣ l := (Nat.mem_divisors.1 hd).1
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdl hl
    obtain ⟨c, hc⟩ := hdl
    have hcd : l / d = c := by rw [hc]; exact Nat.mul_div_cancel_left c hd0
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; omega
      · exact h
    have hlm : l * m = d * (c * m) := by rw [hc, mul_assoc]
    have h1 := sum_range_dvd hd0 (c * m)
      (fun a => χ a * exp (2 * π * I * a * q / (l * m)))
    rw [hlm, h1, hcd]
    have h2 : ∀ n : ℕ, χ ((d * n : ℕ) : ZMod m) * exp (2 * π * I * ((d * n : ℕ) : ℂ) * q / (l * m))
        = χ (d : ZMod m) * (χ n * exp (2 * π * I * n * q / (c * m))) := by
      intro n
      have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
      have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
      have hl' : (l : ℂ) = d * c := by exact_mod_cast hc
      push_cast
      rw [map_mul, mul_assoc, hl']
      refine congrArg (fun y => χ (d : ZMod m) * y) (congrArg₂ (· * ·) rfl (congrArg Complex.exp ?_))
      field_simp
    simp_rw [h2]
    rw [← Finset.mul_sum, sum_range_exp_primitive hχ hc0 q]
    split_ifs with hq
    · ring
    · simp
  rw [step1, Finset.sum_congr rfl step2, ← Finset.mul_sum]
  congr 1
  -- reindex
  have step3 : ∑ d ∈ l.divisors, (if ((l / d : ℕ) : ℤ) ∣ q then
        ((l / d : ℕ) : ℂ) * (ArithmeticFunction.moebius d : ℂ) * χ ((d : ℕ) : ZMod m) *
          starRingEnd ℂ (χ ((q / ((l / d : ℕ) : ℤ) : ℤ) : ZMod m)) else 0) =
      ∑ c ∈ l.divisors, (if (c : ℤ) ∣ q then
        (c : ℂ) * (ArithmeticFunction.moebius (l / c) : ℂ) * χ ((l / c : ℕ) : ZMod m) *
          starRingEnd ℂ (χ ((q / (c : ℤ) : ℤ) : ZMod m)) else 0) := by
    rw [← Nat.sum_div_divisors l (fun c => if (c : ℤ) ∣ q then
        (c : ℂ) * (ArithmeticFunction.moebius (l / c) : ℂ) * χ ((l / c : ℕ) : ZMod m) *
          starRingEnd ℂ (χ ((q / (c : ℤ) : ℤ) : ZMod m)) else 0)]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdl : d ∣ l := (Nat.mem_divisors.1 hd).1
    rw [Nat.div_div_self hdl (NeZero.ne l)]
  rw [step3, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext c
  simp only [Finset.mem_filter, Nat.mem_divisors]
  have hg : Int.gcd (l : ℤ) q ≠ 0 := by
    intro h
    have := Int.gcd_eq_zero_iff.1 h
    exact (NeZero.ne l) (by exact_mod_cast this.1)
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩
    refine ⟨?_, hg⟩
    exact Int.dvd_coe_gcd (Int.natCast_dvd_natCast.2 h1) h2 |> fun h => by exact_mod_cast h
  · rintro ⟨h1, _⟩
    have h3 : (c : ℤ) ∣ (Int.gcd (l : ℤ) q : ℤ) := Int.natCast_dvd_natCast.2 h1
    exact ⟨⟨Int.natCast_dvd_natCast.1 (h3.trans (Int.gcd_dvd_left _ _)), NeZero.ne l⟩,
      h3.trans (Int.gcd_dvd_right _ _)⟩

end ModularFormsKB.Miyake
