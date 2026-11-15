/-
# The $q$-expansion of the coset sum `heckeFun` is Shimura's coefficient formula

If $f = \sum_n a(n)q^n$, then
* $\sum_{b=0}^{p^2-1} f((\tau+b)/p^2) = p^2\sum_n a(p^2n)q^n$ (`sum_affPt_div`),
* $\sum_{i=0}^{p-1}\big(\frac ip\big) f(\tau + 4i/p) = G_p\sum_n \big(\frac np\big)a(n)q^n$ (`sum_jacobi_affPt`),
* $f(p^2\tau) = \sum_n a(n/p^2)q^n$, with $a(n/p^2) = 0$ unless $p^2 \mid n$ (`affPt_mul`),

so, given Gauss's sign $G_p = \varepsilon_p\sqrt p$ (`QuadGaussSumSign`), `heckeFun k N χ p f` has $q$-expansion
`heckeT k N χ p a` (`heckeFun_hasQExp`). Uses $\varepsilon_p^2 = \big(\frac{-1}{p}\big)$.
-/
import ModularFormsKB.HalfIntegral.HeckeOp
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.GaussSum

namespace ModularFormsKB.HalfIntegral

open Complex
open scoped Real

local notation "ℍ" => UpperHalfPlane

lemma sum_range_zmod (p : ℕ) [NeZero p] (g : ZMod p → ℂ) :
    ∑ i ∈ Finset.range p, g (i : ZMod p) = ∑ x : ZMod p, g x := by
  refine Finset.sum_nbij' (fun i => (i : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intros; exact Finset.mem_univ _
  · intro x _; exact Finset.mem_range.2 (ZMod.val_lt x)
  · intro i hi; exact ZMod.val_cast_of_lt (Finset.mem_range.1 hi)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intros; rfl

lemma gauss_shift (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (m : ℤ) :
    ∑ i ∈ Finset.range p, (jacobiSym i p : ℂ) * cexp (2 * π * I * (m * i) / p) =
      (jacobiSym m p : ℂ) * gaussQ p := by
  have hring : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have key : ∀ i : ℕ, (jacobiSym i p : ℂ) = (quadraticChar (ZMod p) (i : ZMod p) : ℂ) := by
    intro i
    rw [← jacobiSym.legendreSym.to_jacobiSym p (i : ℤ)]
    simp [legendreSym]
  have keyZ : (jacobiSym m p : ℂ) = (quadraticChar (ZMod p) (m : ZMod p) : ℂ) := by
    rw [← jacobiSym.legendreSym.to_jacobiSym p m]
    simp [legendreSym]
  have e1 : ∀ i : ℕ, cexp (2 * π * I * (m * i) / p) = ZMod.stdAddChar ((m : ZMod p) * (i : ZMod p)) := by
    intro i
    rw [ZMod.stdAddChar_apply, show ((m : ZMod p) * (i : ZMod p)) = ((m * i : ℤ) : ZMod p) by push_cast; rfl,
      ZMod.toCircle_intCast]
    push_cast; rfl
  have e2 : gaussQ p = ∑ x : ZMod p, (quadraticChar (ZMod p) x : ℂ) * ZMod.stdAddChar x := by
    unfold gaussQ
    rw [← sum_range_zmod p (fun x => (quadraticChar (ZMod p) x : ℂ) * ZMod.stdAddChar x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  simp_rw [key, e1]
  rw [sum_range_zmod p (fun x => (quadraticChar (ZMod p) x : ℂ) * ZMod.stdAddChar ((m : ZMod p) * x)), keyZ, e2]
  by_cases h0 : (m : ZMod p) = 0
  · have h := quadraticChar_sum_zero (F := ZMod p) hring
    simp only [h0, zero_mul, AddChar.map_zero_eq_one, mul_one, MulChar.map_zero, Int.cast_zero]
    exact_mod_cast h
  · have hsq : ((quadraticChar (ZMod p) (m : ZMod p) : ℤ) : ℂ) * (quadraticChar (ZMod p) (m : ZMod p) : ℤ) = 1 := by
      have := quadraticChar_sq_one h0
      exact_mod_cast (by rw [← sq]; exact this : (quadraticChar (ZMod p) (m : ZMod p)) * quadraticChar (ZMod p) (m : ZMod p) = 1)
    have hG : ∑ y : ZMod p, (quadraticChar (ZMod p) y : ℂ) * ZMod.stdAddChar y =
        ((quadraticChar (ZMod p) (m : ZMod p) : ℤ) : ℂ) *
          ∑ x : ZMod p, (quadraticChar (ZMod p) x : ℂ) * ZMod.stdAddChar ((m : ZMod p) * x) := by
      rw [Finset.mul_sum]
      symm
      refine Fintype.sum_equiv (Equiv.mulLeft₀ (m : ZMod p) h0) _ _ ?_
      intro x
      simp only [Equiv.mulLeft₀_apply, map_mul, Int.cast_mul]
      ring
    rw [hG, ← mul_assoc, hsq, one_mul]

lemma sum_exp_geom (M n : ℕ) (hM : 0 < M) :
    ∑ b ∈ Finset.range M, cexp (2 * π * I * n * b / M) = if M ∣ n then (M : ℂ) else 0 := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  set z : ℂ := cexp (2 * π * I * n / M) with hz
  have h1 : ∀ b : ℕ, cexp (2 * π * I * n * b / M) = z ^ b := by
    intro b
    rw [hz, ← Complex.exp_nat_mul]; congr 1; ring
  simp_rw [h1]
  split_ifs with hd
  · obtain ⟨c, rfl⟩ := hd
    have : z = 1 := by
      rw [hz, Complex.exp_eq_one_iff]
      exact ⟨c, by push_cast; field_simp⟩
    simp [this]
  · have hz1 : z ≠ 1 := by
      intro h
      rw [hz, Complex.exp_eq_one_iff] at h
      obtain ⟨k, hk⟩ := h
      apply hd
      have hk' : (n : ℂ) = M * k := by
        have h2 : (2 * π * I) ≠ 0 := by simp [Real.pi_ne_zero]
        field_simp at hk
        linear_combination hk
      have : (n : ℤ) = M * k := by exact_mod_cast hk'
      have h3 : (M : ℤ) ∣ n := ⟨k, this⟩
      exact_mod_cast h3
    have hzM : z ^ M = 1 := by
      rw [hz, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
      exact ⟨n, by field_simp; simp⟩
    rw [geom_sum_eq hz1, hzM]; simp

lemma hasSum_dvd_iff (M : ℕ) (hM : 0 < M) (c : ℕ → ℂ) (s : ℂ) :
    HasSum (fun m => c (M * m)) s ↔ HasSum (fun n => if M ∣ n then c n else 0) s := by
  have inj : Function.Injective (fun m : ℕ => M * m) := mul_right_injective₀ hM.ne'
  rw [← inj.hasSum_iff (f := fun n => if M ∣ n then c n else 0)]
  · refine iff_of_eq ?_
    congr 1
    funext m
    simp
  · intro x hx
    have : ¬ M ∣ x := by
      rintro ⟨m, rfl⟩
      exact hx ⟨m, rfl⟩
    simp [this]

lemma sum_affPt_div (p : ℕ+) {f : ℍ → ℂ} {a : ℕ → ℂ} (hf : Abstract.HasQExp f a) (τ : ℍ) :
    HasSum (fun m : ℕ => ((p : ℕ) : ℂ) ^ 2 * a ((p : ℕ) ^ 2 * m) * cexp (2 * π * I * m * τ))
      (∑ b ∈ Finset.range ((p : ℕ) ^ 2), f (affPt 1 (p ^ 2) b τ)) := by
  have hM : 0 < (p : ℕ) ^ 2 := by positivity
  have hM' : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.pos.ne'
  have h := hasSum_sum (s := Finset.range ((p : ℕ) ^ 2)) (fun b _ => hf (affPt 1 (p ^ 2) b τ))
  set c : ℕ → ℂ := fun n => ((p : ℕ) : ℂ) ^ 2 * a n * cexp (2 * π * I * n * τ / (((p : ℕ) : ℂ) ^ 2)) with hc
  have h2 : (fun n : ℕ => ∑ b ∈ Finset.range ((p : ℕ) ^ 2), a n * cexp (2 * π * I * n * (affPt 1 (p ^ 2) b τ : ℂ)))
      = fun n => if (p : ℕ) ^ 2 ∣ n then c n else 0 := by
    funext n
    have e : ∀ b : ℕ, cexp (2 * π * I * n * (affPt 1 (p ^ 2) b τ : ℂ)) =
        cexp (2 * π * I * n * τ / (((p : ℕ) : ℂ) ^ 2)) * cexp (2 * π * I * n * b / (((p : ℕ) ^ 2 : ℕ) : ℂ)) := by
      intro b
      rw [← Complex.exp_add, coe_affPt]
      congr 1
      push_cast
      field_simp
    simp_rw [e]
    simp_rw [mul_left_comm (a n)]
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_exp_geom _ _ hM]
    simp only [hc]
    split_ifs <;> push_cast <;> ring
  rw [h2, ← hasSum_dvd_iff _ hM] at h
  convert h using 2 with m
  simp only [hc]
  push_cast
  congr 2
  field_simp

lemma affPt_mul (p : ℕ+) {f : ℍ → ℂ} {a : ℕ → ℂ} (hf : Abstract.HasQExp f a) (τ : ℍ) :
    HasSum (fun n : ℕ => if (p : ℕ) ^ 2 ∣ n then a (n / (p : ℕ) ^ 2) * cexp (2 * π * I * n * τ) else 0)
      (f (affPt (p ^ 2) 1 0 τ)) := by
  have hM : 0 < (p : ℕ) ^ 2 := by positivity
  have h := hf (affPt (p ^ 2) 1 0 τ)
  rw [← hasSum_dvd_iff _ hM (fun n => a (n / (p : ℕ) ^ 2) * cexp (2 * π * I * n * τ))]
  convert h using 2 with m
  rw [Nat.mul_div_cancel_left _ hM, coe_affPt]
  push_cast
  simp
  left
  congr 1
  ring

lemma sum_jacobi_affPt (p : ℕ+) [Fact (p : ℕ).Prime] (hp2 : (p : ℕ) ≠ 2) {f : ℍ → ℂ} {a : ℕ → ℂ}
    (hf : Abstract.HasQExp f a) (τ : ℍ) :
    HasSum (fun n : ℕ => gaussQ p * (jacobiSym n p : ℂ) * a n * cexp (2 * π * I * n * τ))
      (∑ i ∈ Finset.range (p : ℕ), (jacobiSym i p : ℂ) * f (affPt p p (4 * i) τ)) := by
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.pos.ne'
  have h := hasSum_sum (s := Finset.range (p : ℕ))
    (fun i _ => (hf (affPt p p (4 * i) τ)).mul_left (jacobiSym i p : ℂ))
  convert h using 2 with n
  have e : ∀ i : ℕ, (jacobiSym i p : ℂ) * (a n * cexp (2 * π * I * n * (affPt p p (4 * i) τ : ℂ))) =
      a n * cexp (2 * π * I * n * τ) *
        ((jacobiSym i p : ℂ) * cexp (2 * π * I * (((4 * n : ℤ) : ℂ) * i) / ((p : ℕ) : ℂ))) := by
    intro i
    have : cexp (2 * π * I * n * (affPt p p (4 * i) τ : ℂ)) =
        cexp (2 * π * I * n * τ) * cexp (2 * π * I * (((4 * n : ℤ) : ℂ) * i) / ((p : ℕ) : ℂ)) := by
      rw [← Complex.exp_add, coe_affPt]
      congr 1
      push_cast
      field_simp
    rw [this]; ring
  simp_rw [e]
  rw [← Finset.mul_sum, gauss_shift p hp2 (4 * n)]
  have h4 : jacobiSym (4 * (n : ℤ)) p = jacobiSym n p := by
    have h2 : (2 : ℤ).gcd p = 1 := by
      have := (Nat.coprime_primes Nat.prime_two (Fact.out : (p : ℕ).Prime)).2 (Ne.symm hp2)
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, Int.gcd_natCast_natCast]
      exact this
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, jacobiSym.mul_left, jacobiSym.sq_one' h2, one_mul]
  rw [h4]
  ring

lemma eps_sq (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : epsD (p : ℤ) ^ 2 = (jacobiSym (-1) p : ℂ) := by
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  rw [jacobiSym.at_neg_one hodd]
  have h : p % 4 = 1 ∨ p % 4 = 3 := by obtain ⟨j, rfl⟩ := hodd; omega
  rcases h with h | h
  · have h' : (p : ℤ) % 4 = 1 := by omega
    simp [epsD, h', ZMod.χ₄_nat_one_mod_four h]
  · have h' : ¬ (p : ℤ) % 4 = 1 := by omega
    simp [epsD, h', ZMod.χ₄_nat_three_mod_four h]

lemma coeff2 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hs : gaussQ p = epsD (p : ℤ) * (Real.sqrt p : ℂ))
    (k : ℕ) (c : ℂ) (n : ℕ) (x : ℂ) :
    ((p : ℂ)) ^ (-2 : ℤ) * (c * ((epsD (p : ℤ))⁻¹ * (Real.sqrt p : ℂ)) ^ (2 * k + 1) *
        (gaussQ p * (jacobiSym n p : ℂ) * x)) =
      c * (jacobiSym ((-1) ^ k * n) p : ℂ) * (p : ℂ) ^ ((k : ℤ) - 1) * x := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hj := eps_sq p hp hp2
  have hjj : (jacobiSym (-1) p : ℂ) * (jacobiSym (-1) p : ℂ) = 1 := by
    have : jacobiSym (-1) p * jacobiSym (-1) p = 1 := by
      have h := jacobiSym.sq_one (a := (-1 : ℤ)) (b := p) (by simp)
      rw [← sq]; exact h
    exact_mod_cast this
  have hε : epsD (p : ℤ) ≠ 0 := by
    intro h; rw [h] at hj
    rw [← hj] at hjj; simp at hjj
  have hs2 : ((Real.sqrt p : ℂ)) ^ 2 = p := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  have A : ((epsD (p : ℤ))⁻¹ * (Real.sqrt p : ℂ)) ^ (2 * k + 1) * (epsD (p : ℤ) * (Real.sqrt p : ℂ)) =
      (jacobiSym (-1) p : ℂ) ^ k * (p : ℂ) ^ (k + 1) := by
    have : ((epsD (p : ℤ))⁻¹ * (Real.sqrt p : ℂ)) ^ (2 * k + 1) * (epsD (p : ℤ) * (Real.sqrt p : ℂ)) =
        (((epsD (p : ℤ))⁻¹) ^ 2) ^ k * ((Real.sqrt p : ℂ) ^ 2) ^ (k + 1) * ((epsD (p : ℤ))⁻¹ * epsD (p : ℤ)) := by
      ring
    rw [this, inv_mul_cancel₀ hε, inv_pow, hj, hs2, mul_one]
    congr 1
    rw [inv_eq_of_mul_eq_one_right hjj]
  have hpz : (p : ℂ) ^ ((k : ℤ) - 1) = (p : ℂ) ^ (k + 1) * (p : ℂ) ^ (-2 : ℤ) := by
    rw [← zpow_natCast, ← zpow_add₀ hp0]; congr 1; push_cast; ring
  have hjac : (jacobiSym ((-1) ^ k * n) p : ℂ) = (jacobiSym (-1) p : ℂ) ^ k * (jacobiSym n p : ℂ) := by
    rw [jacobiSym.mul_left, jacobiSym.pow_left]; push_cast; rfl
  rw [hjac, hpz, hs]
  calc _ = c * ((((epsD (p : ℤ))⁻¹ * (Real.sqrt p : ℂ)) ^ (2 * k + 1) * (epsD (p : ℤ) * (Real.sqrt p : ℂ)))) *
        (jacobiSym n p : ℂ) * x * (p : ℂ) ^ (-2 : ℤ) := by ring
    _ = _ := by rw [A]; ring

lemma coeff3 (p : ℕ) (hp : p ≠ 0) (k : ℕ) (c : ℂ) (x : ℂ) :
    (p : ℂ) ^ (-2 : ℤ) * (c ^ 2 * (p : ℂ) ^ (2 * k + 1) * x) = c ^ 2 * (p : ℂ) ^ (2 * (k : ℤ) - 1) * x := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hpz : (p : ℂ) ^ (2 * (k : ℤ) - 1) = (p : ℂ) ^ (2 * k + 1) * (p : ℂ) ^ (-2 : ℤ) := by
    rw [← zpow_natCast, ← zpow_add₀ hp0]; congr 1; push_cast; ring
  rw [hpz]; ring

/-- **The $q$-expansion of $T(p^2)f$:** given Gauss's sign of the quadratic Gauss sum, the coset sum `heckeFun` of a function
with $q$-expansion $a$ has $q$-expansion `heckeT k N χ p a` (Shimura 1973 `shimura1973`, Thm. 1.7 [unverified]). -/
theorem heckeFun_hasQExp (hG : QuadGaussSumSign) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (p : ℕ+)
    (hp : (p : ℕ).Prime) (hp2 : (p : ℕ) ≠ 2) {f : ℍ → ℂ} {a : ℕ → ℂ} (hf : Abstract.HasQExp f a) :
    Abstract.HasQExp (heckeFun k N χ p f) (heckeT k N χ p a) := by
  have : Fact (p : ℕ).Prime := ⟨hp⟩
  intro τ
  have hs := hG.sign p hp hp2
  have h1 := sum_affPt_div p hf τ
  have h2 := sum_jacobi_affPt p hp2 hf τ
  have h3 := affPt_mul p hf τ
  have h := ((h1.add (h2.mul_left (χ (p : ℕ) * ((epsD (p : ℕ))⁻¹ * (Real.sqrt (p : ℕ) : ℂ)) ^ (2 * k + 1)))).add
    (h3.mul_left (χ (p : ℕ) ^ 2 * ((p : ℕ) : ℂ) ^ (2 * k + 1)))).mul_left (((p : ℕ) : ℂ) ^ (-2 : ℤ))
  unfold heckeFun
  convert h using 1
  funext n
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.pos.ne'
  have c2 := coeff2 p hp hp2 hs k (χ (p : ℕ)) n (a n * cexp (2 * π * I * n * τ))
  have c1 : ((p : ℕ) : ℂ) ^ (-2 : ℤ) * (((p : ℕ) : ℂ) ^ 2 * a ((p : ℕ) ^ 2 * n) * cexp (2 * π * I * n * τ)) =
      a ((p : ℕ) ^ 2 * n) * cexp (2 * π * I * n * τ) := by
    rw [zpow_neg, ← mul_assoc]
    field_simp
  simp only [heckeT]
  by_cases hd : (p : ℕ) ^ 2 ∣ n
  · simp only [hd, ite_true]
    have c3 := coeff3 p p.pos.ne' k (χ (p : ℕ)) (a (n / (p : ℕ) ^ 2) * cexp (2 * π * I * n * τ))
    linear_combination -(c1 + c2 + c3)
  · simp only [hd, ite_false]
    linear_combination -(c1 + c2)

end ModularFormsKB.HalfIntegral
