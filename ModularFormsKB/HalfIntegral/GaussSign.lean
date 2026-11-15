import ModularFormsKB.HalfIntegral.HeckeStable
import TauCeti.NumberTheory.ModularForms.JacobiTheta.GaussSum

/-!
# Gauss's sign of the quadratic Gauss sum, and Hecke stability without inputs

The named input `QuadGaussSumSign` (`HeckeOp.lean`) is Gauss's theorem: for an odd prime `p`,
`G_p = Σ_{x < p} (x/p) e^{2πi x/p}` equals `√p` if `p ≡ 1 mod 4` and `i√p` if `p ≡ 3 mod 4`.
It is proved here (`quadGaussSumSign`) from Tau Ceti's evaluation of the quadratic exponential sum
(`TauCeti.sum_range_cexp_two_pi_I_sq_div`, by the Landsberg–Schaar identity):
`Σ_{r < N} e^{2πi r²/N} = (1 + i)/2 · (1 + (-i)^N) · √N`.
The bridge is `G_p = Σ_{r < p} e^{2πi r²/p}`: the number of square roots of `x` modulo `p` is
`1 + (x/p)`, and `Σ_{x < p} e^{2πi x/p} = 0`.

Consequently Shimura's Theorem 1.7 for the theta multiplier (the named input `HeckeStable`) holds
unconditionally: `thetaMultiplierSystem_heckeStable_uncond`, `halfInt_heckeStable_uncond`.
-/

open Complex Finset
open scoped Real

namespace ModularFormsKB.HalfIntegral

/-- **Gauss's evaluation at an odd modulus**: for odd `m`, `Σ_{r < m} e^{2πi r²/m} = ε_m √m`
with `ε_m` = `epsD m` (`1` if `m ≡ 1 mod 4`, `i` if `m ≡ 3 mod 4`). From Tau Ceti's
`TauCeti.sum_range_cexp_two_pi_I_sq_div`. -/
theorem sum_range_cexp_sq_eq_epsD {m : ℕ} (hm : m % 2 = 1) :
    ∑ r ∈ range m, cexp (2 * π * I * (r : ℂ) ^ 2 / m) = epsD m * (Real.sqrt m : ℂ) := by
  have h := TauCeti.sum_range_cexp_two_pi_I_sq_div m
  rw [h]
  unfold epsD
  have hI4 : (-I) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    simp
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · have hI : (-I) ^ m = -I := by
      rw [← Nat.div_add_mod m 4, h4, pow_add, pow_mul, hI4]
      simp
    have hz : ((m : ℤ) % 4 = 1) := by omega
    rw [hI, if_pos hz]
    have : (1 + I) / 2 * (1 + -I) = 1 := by
      ring_nf
      simp [I_sq]
      ring
    rw [this]
  · have hI : (-I) ^ m = I := by
      rw [← Nat.div_add_mod m 4, h4, pow_add, pow_mul, hI4]
      simp [pow_three, I_mul_I]
    have hz : ¬((m : ℤ) % 4 = 1) := by omega
    rw [hI, if_neg hz]
    have : (1 + I) / 2 * (1 + I) = I := by
      ring_nf
      simp [I_sq]
    rw [this]

/-- A sum over `x < p` of a function of the residue class of `x` is the sum over `ZMod p`. -/
theorem sum_range_eq_sum_zmod {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    ∑ x ∈ range p, f (x : ZMod p) = ∑ y : ZMod p, f y := by
  refine Finset.sum_bij (fun x _ ↦ (x : ZMod p)) (fun _ _ ↦ mem_univ _) ?_ ?_ (fun _ _ ↦ rfl)
  · intro a ha b hb hab
    have := congrArg ZMod.val hab
    rwa [ZMod.val_natCast_of_lt (mem_range.mp ha), ZMod.val_natCast_of_lt (mem_range.mp hb)] at this
  · intro y _
    exact ⟨y.val, mem_range.mpr (ZMod.val_lt y), ZMod.natCast_zmod_val y⟩

/-- The summand `e^{2πi n/p}` as the standard additive character of `ZMod p`. -/
theorem cexp_eq_stdAddChar (p n : ℕ) [NeZero p] :
    cexp (2 * π * I * n / p) = ZMod.stdAddChar (n : ZMod p) := by
  have := ZMod.stdAddChar_coe (N := p) (n : ℤ)
  push_cast at this
  rw [this]

/-- **The quadratic Gauss sum as an exponential sum over squares**: for an odd prime `p`,
`G_p = Σ_{x < p} (x/p) e^{2πi x/p} = Σ_{r < p} e^{2πi r²/p}`. -/
theorem gaussQ_eq_sum_range_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    gaussQ p = ∑ r ∈ range p, cexp (2 * π * I * (r : ℂ) ^ 2 / p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  set ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar
  -- the right-hand side: `Σ_y ψ(y²)`
  have hR : ∑ r ∈ range p, cexp (2 * π * I * (r : ℂ) ^ 2 / p) = ∑ y : ZMod p, ψ (y ^ 2) := by
    rw [← sum_range_eq_sum_zmod (fun y ↦ ψ (y ^ 2))]
    refine sum_congr rfl fun r _ ↦ ?_
    rw [← Nat.cast_pow, cexp_eq_stdAddChar]
    push_cast
    rfl
  -- the left-hand side: `Σ_a χ(a) ψ(a)`
  have hL : gaussQ p = ∑ a : ZMod p, (quadraticChar (ZMod p) a : ℂ) * ψ a := by
    rw [gaussQ, ← sum_range_eq_sum_zmod (fun a ↦ (quadraticChar (ZMod p) a : ℂ) * ψ a)]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [cexp_eq_stdAddChar]
    congr 1
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    simp [legendreSym]
  -- count the square roots: `#{y | y² = a} = χ(a) + 1`
  have hfib : ∑ y : ZMod p, ψ (y ^ 2) =
      ∑ a : ZMod p, ((quadraticChar (ZMod p) a : ℂ) + 1) * ψ a := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun y : ZMod p ↦ y ^ 2) (t := univ)
      (fun _ _ ↦ mem_univ _)]
    refine sum_congr rfl fun a _ ↦ ?_
    have hc := quadraticChar_card_sqrts hF a
    rw [sum_congr rfl fun y hy ↦ by rw [(mem_filter.mp hy).2]]
    rw [sum_const, nsmul_eq_mul]
    congr 1
    have : (univ.filter fun y : ZMod p ↦ y ^ 2 = a) = {x : ZMod p | x ^ 2 = a}.toFinset := by
      ext y
      simp
    rw [this]
    exact_mod_cast hc
  have hψ : ψ ≠ 1 := by
    have := ZMod.isPrimitive_stdAddChar p (one_ne_zero (α := ZMod p))
    rwa [AddChar.mulShift_one] at this
  have hsum : ∑ a : ZMod p, ψ a = 0 := AddChar.sum_eq_zero_of_ne_one hψ
  rw [hR, hfib, hL]
  simp only [add_mul, one_mul, sum_add_distrib, hsum, add_zero]

/-- **Gauss's sign of the quadratic Gauss sum** (Gauss 1811): the named input
`QuadGaussSumSign` holds. Proof: `gaussQ_eq_sum_range_sq` and Tau Ceti's evaluation
`TauCeti.sum_range_cexp_two_pi_I_sq_div` of `Σ_{r < p} e^{2πi r²/p}`. -/
@[kb "lidl1997" "Thm. 5.15: the quadratic Gauss sum over F_p is √p or i√p according as p ≡ 1 or 3 mod 4 (proved)"]
theorem quadGaussSumSign : QuadGaussSumSign where
  sign p hp hp2 := by
    rw [gaussQ_eq_sum_range_sq hp hp2]
    exact sum_range_cexp_sq_eq_epsD (hp.eq_two_or_odd.resolve_left hp2)

/-- **Shimura's Theorem 1.7 for the theta multiplier, unconditionally**: the named input
`HeckeStable` holds for `thetaMultiplierSystem`. -/
@[kb "shimura1973" "Thm. 1.7 for the theta multiplier: T(p²) preserves M and S_{k+1/2}(4N, χ), p ∤ 4N [unverified]"]
theorem thetaMultiplierSystem_heckeStable_uncond (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) :
    HeckeStable thetaMultiplierSystem k N χ :=
  thetaMultiplierSystem_heckeStable quadGaussSumSign k N χ

/-- **Hecke stability of `halfIntModularForms` and `halfIntCuspForms`** (Shimura 1973, Thm. 1.7),
unconditionally: for a prime `p ∤ 4N`, `T(p²)` maps forms to forms and acts on `q`-expansions
by `heckeT`. -/
@[kb "shimura1973" "Thm. 1.7 for the concrete spaces: T(p²) preserves halfIntModularForms and halfIntCuspForms [unverified]"]
theorem halfInt_heckeStable_uncond (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {p : ℕ}
    (hp : p.Prime) (hpN : ¬ p ∣ 4 * N) :
    (∀ f ∈ halfIntModularForms k N χ, ∀ a : ℕ → ℂ, HasQExpansion f a →
      ∃ g ∈ halfIntModularForms k N χ, HasQExpansion g (heckeT k N χ p a)) ∧
    (∀ f ∈ halfIntCuspForms k N χ, ∀ a : ℕ → ℂ, HasQExpansion f a →
      ∃ g ∈ halfIntCuspForms k N χ, HasQExpansion g (heckeT k N χ p a)) :=
  halfInt_heckeStable_of_gaussSign quadGaussSumSign k N χ hp hpN

end ModularFormsKB.HalfIntegral
