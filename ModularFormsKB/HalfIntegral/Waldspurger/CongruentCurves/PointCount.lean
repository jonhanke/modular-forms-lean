/-
# Point counts of $y^2 = x^3 - n^2x$ over $\mathbb F_p$

For an odd prime $p$, the Frobenius trace (Tau Ceti `WeierstrassCurve.frobeniusTrace`, $p + 1 - \#E(\mathbb F_p)$ with
the point at infinity counted) of $E_n \bmod p$ is minus a character sum:
$$ a_p(E_n) = -\sum_{x \in \mathbb F_p} \left(\frac{x^3 - n^2x}{p}\right)$$
(`frobeniusTrace_congruentCurveMod`). Hence:
- row 32, the twist rule: $a_p(E_n) = \left(\frac np\right) a_p(E_1)$ for $p \nmid 2n$ (substitute $x = nt$);
- $a_p(E_n) = 0$ for odd $p \mid n$ (the curve is $y^2 = x^3$);
- $a_p(E_1) = 0 = b(p)$ for $p \equiv 3 \bmod 4$ ($x \mapsto -x$ changes the sign of the sum);
- row 30 for $p \equiv 1 \bmod 4$, $a_p(E_1) = b(p)$ (Gauss): `GaussCountX3SubX`.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.Coefficients
import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open WeierstrassCurve

variable {p : ℕ} [Fact p.Prime]

/-- **The Frobenius trace as a character sum** ($p$ odd). -/
theorem frobeniusTrace_congruentCurveMod (hp : p ≠ 2) (n : ℕ) :
    (congruentCurveMod n p).frobeniusTrace =
      -∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - (n : ZMod p) ^ 2 * x) := by
  classical
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  rw [WeierstrassCurve.frobeniusTrace_def, WeierstrassCurve.pointCount_def]
  let e : {q : ZMod p × ZMod p // (congruentCurveMod n p).toAffine.Equation q.1 q.2} ≃
      Σ x : ZMod p, {y : ZMod p // y ^ 2 = x ^ 3 - (n : ZMod p) ^ 2 * x} :=
    (Equiv.subtypeProdEquivSigmaSubtype
      (fun x y => (congruentCurveMod n p).toAffine.Equation x y)).trans
      (Equiv.sigmaCongrRight fun x => Equiv.subtypeEquivRight fun y => by
        rw [WeierstrassCurve.Affine.equation_iff]
        simp only [congruentCurveMod]
        constructor <;> intro h <;> linear_combination h)
  have key : (Nat.card {q : ZMod p × ZMod p // (congruentCurveMod n p).toAffine.Equation q.1 q.2} : ℤ)
      = ∑ x : ZMod p, (quadraticChar (ZMod p) (x ^ 3 - (n : ZMod p) ^ 2 * x) + 1) := by
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← quadraticChar_card_sqrts hF, Fintype.card_subtype]
    simp
  push_cast
  rw [key, Finset.sum_add_distrib, Nat.card_zmod]
  simp

/-- **Row 32: the twist rule** $a_p(E_n) = \left(\frac np\right) a_p(E_1)$ for $p \nmid 2n$. -/
theorem frobeniusTrace_congruentCurveMod_twist (hp : p ≠ 2) {n : ℕ} (hn : ¬ p ∣ n) :
    (congruentCurveMod n p).frobeniusTrace = jacobiSym n p * (congruentCurveMod 1 p).frobeniusTrace := by
  have hn' : (n : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  rw [frobeniusTrace_congruentCurveMod hp, frobeniusTrace_congruentCurveMod hp,
    ← jacobiSym.legendreSym.to_jacobiSym]
  have h1 : legendreSym p (n : ℤ) = quadraticChar (ZMod p) (n : ZMod p) := by
    simp [legendreSym]
  have h2 : ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - (n : ZMod p) ^ 2 * x) =
      quadraticChar (ZMod p) (n : ZMod p) *
        ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - ((1 : ℕ) : ZMod p) ^ 2 * x) := by
    rw [← Equiv.sum_comp (Equiv.mulLeft₀ (n : ZMod p) hn'), Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h3 : quadraticChar (ZMod p) (n : ZMod p) ^ 2 = 1 := quadraticChar_sq_one hn'
    have : (Equiv.mulLeft₀ (n : ZMod p) hn') t ^ 3 - (n : ZMod p) ^ 2 * (Equiv.mulLeft₀ (n : ZMod p) hn') t
        = (n : ZMod p) ^ 3 * (t ^ 3 - ((1 : ℕ) : ZMod p) ^ 2 * t) := by
      have e : (Equiv.mulLeft₀ (n : ZMod p) hn') t = (n : ZMod p) * t := rfl
      rw [e, Nat.cast_one]; ring
    rw [this, map_mul, map_pow]
    have : quadraticChar (ZMod p) (n : ZMod p) ^ 3 = quadraticChar (ZMod p) (n : ZMod p) := by
      rw [pow_succ, h3, one_mul]
    rw [this]
  rw [h1, h2]; ring

/-- $a_p(E_n) = 0$ for odd $p \mid n$. -/
theorem frobeniusTrace_congruentCurveMod_of_dvd (hp : p ≠ 2) {n : ℕ} (hn : p ∣ n) :
    (congruentCurveMod n p).frobeniusTrace = 0 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hn' : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hn
  rw [frobeniusTrace_congruentCurveMod hp, hn']
  have : ∀ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - 0 ^ 2 * x) = quadraticChar (ZMod p) x := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have := quadraticChar_sq_one hx
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, sub_zero, map_pow]
      rw [pow_succ, this, one_mul]
  rw [Finset.sum_congr rfl fun x _ => this x, quadraticChar_sum_zero hF]
  simp

/-- $a_p(E_1) = 0$ for $p \equiv 3 \bmod 4$. -/
theorem frobeniusTrace_congruentCurveMod_one_of_three (hp : p % 4 = 3) :
    (congruentCurveMod 1 p).frobeniusTrace = 0 := by
  have h2 : p ≠ 2 := by omega
  have hsq : ¬ IsSquare (-1 : ZMod p) := by
    rw [FiniteField.isSquare_neg_one_iff, ZMod.card]; omega
  rw [frobeniusTrace_congruentCurveMod h2]
  have := quadraticChar_sum_comp_eq_zero_of_odd hsq
    (f := fun x : ZMod p => x ^ 3 - ((1 : ℕ) : ZMod p) ^ 2 * x) (by intro x; simp only [Nat.cast_one]; ring)
  rw [this]; simp

omit [Fact p.Prime] in
/-- $b(p) = 0$ for $p \equiv 3 \bmod 4$: $p$ is not a sum of two squares. -/
theorem f32Coeff_of_three (hp : p % 4 = 3) : f32Coeff p = 0 := by
  unfold f32Coeff
  refine Finset.sum_eq_zero fun v hv => ?_
  exfalso
  simp only [primaryOfNorm, Finset.mem_filter] at hv
  obtain ⟨-, h2, h3, h4, -⟩ := hv
  obtain ⟨k, hk⟩ : ∃ k, v.1 = 2 * k + 1 := ⟨v.1 / 2, by omega⟩
  obtain ⟨l, hl⟩ : ∃ l, v.2 = 2 * l := ⟨v.2 / 2, by omega⟩
  have h : (p : ℤ) = 4 * (k ^ 2 + k + l ^ 2) + 1 := by rw [← h2, hk, hl]; ring
  generalize k ^ 2 + k + l ^ 2 = t at h
  omega

/-- **Gauss's count for $y^2 = x^3 - x$** (Gauss; Ireland–Rosen 1990 `irelandrosen1990`, Ch. 18, §4, Thm. 5
[unverified]): for a prime $p \equiv 1 \bmod 4$ write $p = a^2 + c^2$ with $a + ci \equiv 1 \bmod (2 + 2i)$; then
$\#E_1(\mathbb F_p) = p + 1 - 2a$, i.e. $a_p(E_1) = b(p)$. -/
@[kb "irelandrosen1990" "Ch. 18 §4 Thm. 5: #{y² = x³ − x} over F_p is p + 1 − 2a, p = a² + b², a + bi ≡ 1 mod (2+2i) [unverified]"]
structure GaussCountX3SubX : Prop where
  trace_eq : ∀ (p : ℕ) [Fact p.Prime], p % 4 = 1 → (congruentCurveMod 1 p).frobeniusTrace = f32Coeff p

/-- **$a_p(E_n) = \left(\frac np\right) b(p)$ for every odd prime $p$** (for $p \mid n$ both sides vanish). -/
theorem frobeniusTrace_congruentCurveMod_eq (hG : GaussCountX3SubX) (hp : p ≠ 2) (n : ℕ) :
    (congruentCurveMod n p).frobeniusTrace = congruentCoeff n p := by
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp
    · exact h
  by_cases hd : p ∣ n
  · rw [frobeniusTrace_congruentCurveMod_of_dvd hp hd, congruentCoeff, ← jacobiSym.legendreSym.to_jacobiSym]
    have : legendreSym p (n : ℤ) = 0 := by
      rw [legendreSym.eq_zero_iff]; simpa using (ZMod.natCast_eq_zero_iff _ _).2 hd
    rw [this, zero_mul]
  · rw [frobeniusTrace_congruentCurveMod_twist hp hd, congruentCoeff]
    have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases h4 with h | h
    · rw [hG.trace_eq p h]
    · rw [frobeniusTrace_congruentCurveMod_one_of_three h, f32Coeff_of_three h]

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
