/-
# $U(4)$ on $q$-expansions

The function-level operator $(f|U(4))(\tau) = \tfrac14\sum_{j=0}^3 f((\tau+j)/4)$
(`kohnenU4`, `ModularFormsKB/HalfIntegral/Abstract/KohnenProjection.lean`) acts on $q$-expansions by $a(n) \mapsto a(4n)$:
$\tfrac14\sum_j e(n(\tau+j)/4) = e(n\tau/4)$ if $4 \mid n$ and $0$ otherwise.
-/
import ModularFormsKB.HalfIntegral.Abstract.KohnenProjection

namespace ModularFormsKB.HalfIntegral

open Complex
open scoped Real

local notation "ℍ" => UpperHalfPlane

private lemma cexp_quarter (n j : ℕ) (τ : ℂ) :
    cexp (2 * π * I * n * ((τ + j) / 4)) =
      cexp (2 * π * I * n * τ / 4) * (I ^ n) ^ j := by
  have hI : I = cexp (π / 2 * I) := by
    rw [Complex.exp_mul_I]; simp
  have : (I ^ n) ^ j = cexp (2 * π * I * n * j / 4) := by
    rw [show 2 * (π : ℂ) * I * n * j / 4 = ((n * j : ℕ) : ℂ) * (π / 2 * I) by push_cast; ring,
      Complex.exp_nat_mul, ← hI, pow_mul]
  rw [this, ← Complex.exp_add]
  congr 1
  ring

private lemma sum_quarter (n : ℕ) :
    (1 / 4 : ℂ) * ∑ j ∈ Finset.range 4, (I ^ n) ^ j = if 4 ∣ n then 1 else 0 := by
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 4 ∧ n = 4 * m + r :=
    ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
  have h4 : (I ^ 4 : ℂ) = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]; simp
  have hp : (I ^ (4 * m + r) : ℂ) = I ^ r := by rw [pow_add, pow_mul, h4]; simp
  rw [hp]
  interval_cases r
  · simp
  all_goals rw [if_neg (by omega)]
  all_goals simp [Finset.sum_range_succ, pow_succ]

/-- **$U(4)$ on $q$-expansions:** if $f = \sum a(n)q^n$ then $f|U(4) = \sum a(4n)q^n$. -/
theorem hasQExp_kohnenU4 {f : ℍ → ℂ} {a : ℕ → ℂ} (hf : Abstract.HasQExp f a) :
    Abstract.HasQExp (kohnenU4 f) (fun n ↦ a (4 * n)) := by
  intro τ
  have h := (hasSum_sum (s := Finset.range 4) (fun j _ ↦ hf (quarterPt j τ))).mul_left (1 / 4 : ℂ)
  have hF : ∀ n : ℕ, (1 / 4 : ℂ) * ∑ j ∈ Finset.range 4,
      a n * cexp (2 * π * I * n * (quarterPt j τ : ℂ)) =
      if 4 ∣ n then a n * cexp (2 * π * I * n * τ / 4) else 0 := by
    intro n
    have : ∀ j ∈ Finset.range 4, a n * cexp (2 * π * I * n * (quarterPt j τ : ℂ)) =
        a n * cexp (2 * π * I * n * τ / 4) * (I ^ n) ^ j := by
      intro j _
      rw [show (quarterPt j τ : ℂ) = ((τ : ℂ) + j) / 4 from rfl, cexp_quarter]; ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, ← mul_assoc, mul_comm (1/4 : ℂ),
      mul_assoc, sum_quarter]
    split_ifs <;> simp
  simp_rw [hF] at h
  have hinj : Function.Injective (fun m : ℕ ↦ 4 * m) := fun x y hxy ↦ by simpa using hxy
  have h0 : ∀ n ∉ Set.range (fun m : ℕ ↦ 4 * m),
      (if 4 ∣ n then a n * cexp (2 * π * I * n * τ / 4) else 0) = 0 := by
    intro n hn
    rw [if_neg]
    rintro ⟨m, rfl⟩
    exact hn ⟨m, rfl⟩
  rw [← hinj.hasSum_iff h0] at h
  change HasSum _ ((1 / 4 : ℂ) * ∑ j ∈ Finset.range 4, f (quarterPt j τ))
  convert h using 2 with m
  simp only [Function.comp, dvd_mul_right, ite_true]
  congr 2
  push_cast
  ring_nf

end ModularFormsKB.HalfIntegral
