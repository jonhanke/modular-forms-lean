import ModularFormsKB.Historical.Ramanujan.PartitionDefs
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Ramanujan's congruences `p(5m+4) ≡ 0 (mod 5)`, `p(7m+5) ≡ 0 (mod 7)`, `p(35m+19) ≡ 0 (mod 35)`

Ramanujan, *Some properties of p(n)* (1919; *Collected Papers*, No. 25, §§ 2–3, pp. 211–212), and the
Frobenius congruence `∏(1 - xⁿ)^p ≡ ∏(1 - x^{pn}) (mod p)` of No. 30, § 2, (2.2).

Proof structure, with `E = ∏ (1 - Xⁿ)` and `P = ∑ p(n) Xⁿ`:
* `partitionSeries_mul_eulerSeries`: `P · E = 1` (Euler; Mathlib's generating function of partitions).
* `eulerSeries_eq_pentagonalSeries`: Euler's pentagonal number theorem (Mathlib).
* `eulerFrobenius`: modulo `p`, `E^{p^k} ≡ ∏ (1 - X^{p^k n})`, via `sub_pow_char_pow` on partial
  products and continuity of reduction mod `p` for the coefficientwise topology.
* Modulo `q` (`q = 5, 7`), `E^q = E(X^q)` (`PowerSeries.expand`), so `X^{q-r} E^{q-1} = X^{q-r} E^q P`
  has `X^{q(m+1)}`-coefficient `≡ ∑_k e_k p(q(m-k)+r)`, and strong induction
  (`dvd_partitionCount_of_coeff_zero`) reduces `q ∣ p(qm+r)` to the vanishing of the
  `X^{q(m+1)}`-coefficient of `X^{q-r} E^{q-1}`.
* Given Jacobi's identity `E³ = ∑ (-1)ᵏ (2k+1) X^{k(k+1)/2}` (kept as the hypothesis
  `eulerSeries ^ 3 = jacobiCubeSeries`), that coefficient is `X E · J` (mod 5) resp. `X² J²` (mod 7),
  and every term vanishes since `k(3k-1) + l(l+1) + 2 ≡ 0 (mod 5)` forces `5 ∣ 2l+1`
  (`term_five`), resp. `a(a+1) + b(b+1) + 4 ≡ 0 (mod 7)` forces `7 ∣ 2a+1` (`term_seven`).
* The congruence modulo `35` follows from the two, the moduli being coprime.
-/

noncomputable section

open PowerSeries Finset
open scoped PowerSeries.WithPiTopology

namespace ModularFormsKB.Historical.Ramanujan

/-- The discrete topology on `ZMod q`, used only to speak of convergent products modulo `q`. -/
local instance instTopologicalSpaceZMod (q : ℕ) : TopologicalSpace (ZMod q) := ⊥

local instance instDiscreteZMod (q : ℕ) : DiscreteTopology (ZMod q) := ⟨rfl⟩

/-- Power series over a field of characteristic `p` have characteristic `p`. -/
theorem charP_powerSeries_zmod (p : ℕ) [Fact p.Prime] : CharP (ZMod p)⟦X⟧ p :=
  charP_of_injective_ringHom (f := (PowerSeries.C : ZMod p →+* (ZMod p)⟦X⟧))
    PowerSeries.C_injective p

/-- **Euler's pentagonal number theorem** in the form `∏ (1 - Xⁿ) = ∑ (-1)ᵏ X^{k(3k-1)/2}` (Mathlib). -/
theorem eulerSeries_eq_pentagonalSeries : eulerSeries = PowerSeries.pentagonalSeries ℤ :=
  PowerSeries.WithPiTopology.tprod_one_sub_X_pow ℤ

theorem hasProd_eulerSeries : HasProd (fun n : ℕ ↦ (1 - X ^ (n + 1) : ℤ⟦X⟧)) eulerSeries := by
  rw [eulerSeries_eq_pentagonalSeries]
  exact PowerSeries.WithPiTopology.hasProd_one_sub_X_pow ℤ

/-- **Euler**: `(∑ p(n) Xⁿ) · ∏ (1 - Xⁿ) = 1`, from Mathlib's product formula for the generating function of partitions. -/
theorem partitionSeries_mul_eulerSeries : partitionSeries * eulerSeries = 1 := by
  have h1 := Nat.Partition.hasProd_powerSeriesMk_card_restricted ℤ (fun _ ↦ True)
  have h2 := hasProd_eulerSeries
  have h3 := h1.mul h2
  have e1 : (PowerSeries.mk fun n ↦ ((Nat.Partition.restricted n fun _ ↦ True).card : ℤ)) =
      partitionSeries := by
    ext n
    simp [partitionSeries, partitionCount, Nat.Partition.restricted]
  rw [e1] at h3
  have e2 : (fun i : ℕ ↦ (if True then ∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j) else 1) *
      (1 - X ^ (i + 1))) = fun _ ↦ 1 := by
    funext i
    simp only [ite_true]
    have := PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero
      (f := (X : ℤ⟦X⟧) ^ (i + 1)) (by simp)
    simpa [pow_mul] using this
  rw [e2] at h3
  exact h3.unique hasProd_one

theorem hasProd_eulerSeriesPow (m : ℕ) (hm : 0 < m) :
    HasProd (fun n : ℕ ↦ (1 - X ^ (m * (n + 1)) : ℤ⟦X⟧)) (eulerSeriesPow m) := by
  have : Multipliable (fun n : ℕ ↦ (1 - X ^ (m * (n + 1)) : ℤ⟦X⟧)) := by
    simp_rw [sub_eq_add_neg]
    apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
    refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n ↦ Filter.eventually_atTop.mpr ⟨n, ?_⟩)
    intro k hk
    rw [order_neg, order_X_pow]
    norm_cast
    nlinarith
  exact this.hasProd

/-- Reduction modulo `q` commutes with convergent products. -/
theorem hasProd_map_zmod {ι : Type*} {f : ι → ℤ⟦X⟧} {F : ℤ⟦X⟧} (h : HasProd f F) (q : ℕ) :
    HasProd (fun i ↦ PowerSeries.map (Int.castRingHom (ZMod q)) (f i))
      (PowerSeries.map (Int.castRingHom (ZMod q)) F) := by
  unfold HasProd at h ⊢
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto] at h ⊢
  intro d
  have := h d
  have hc : Continuous (Int.castRingHom (ZMod q)) := continuous_of_discreteTopology
  have h2 := (hc.tendsto _).comp this
  simpa [← map_prod, coeff_map, Function.comp_def] using h2

/-- Frobenius: `(1 - Xⁿ)^{p^k} = 1 - X^{p^k n}` modulo `p` gives the congruence for `p^k`. -/
theorem eulerSeries_pow_prime_pow (p : ℕ) [hp : Fact p.Prime] (k : ℕ) :
    PowerSeries.map (Int.castRingHom (ZMod p)) eulerSeries ^ (p ^ k) =
      PowerSeries.map (Int.castRingHom (ZMod p)) (eulerSeriesPow (p ^ k)) := by
  have h1 := (hasProd_map_zmod hasProd_eulerSeries p).map (powMonoidHom (p ^ k))
    (continuous_pow _)
  have h2 := hasProd_map_zmod (hasProd_eulerSeriesPow (p ^ k) (pow_pos hp.out.pos k)) p
  have e : (fun n : ℕ ↦ (powMonoidHom (p ^ k) : (ZMod p)⟦X⟧ →* (ZMod p)⟦X⟧)
      (PowerSeries.map (Int.castRingHom (ZMod p)) (1 - X ^ (n + 1)))) =
      fun n ↦ PowerSeries.map (Int.castRingHom (ZMod p)) (1 - X ^ (p ^ k * (n + 1))) := by
    funext n
    simp only [powMonoidHom_apply, map_sub, map_one, map_pow, map_X]
    have := charP_powerSeries_zmod p
    rw [sub_pow_char_pow, one_pow, ← pow_mul, mul_comm (n + 1)]
  rw [Function.comp_def] at h1
  rw [e] at h1
  exact h1.unique h2

/-- **Ramanujan No. 30, (2.2)**:`∏(1 - xⁿ)^p ≡ ∏(1 - x^{pn})` and `∏(1 - xⁿ)^{p²} ≡ ∏(1 - x^{p²n})` modulo a prime `p`, coefficientwise. -/
@[kb "ramanujan1927" "No. 30, § 2, (2.2), p. 234"]
theorem eulerFrobenius : EulerFrobenius := by
  intro p hp n
  have : Fact p.Prime := ⟨hp⟩
  have h1 := eulerSeries_pow_prime_pow p 1
  have h2 := eulerSeries_pow_prime_pow p 2
  rw [pow_one] at h1
  have key : ∀ (a b : ℤ⟦X⟧), PowerSeries.map (Int.castRingHom (ZMod p)) a =
      PowerSeries.map (Int.castRingHom (ZMod p)) b → a.coeff n ≡ b.coeff n [ZMOD p] := by
    intro a b hab
    have := congrArg (PowerSeries.coeff n) hab
    simp only [coeff_map] at this
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mp this
  refine ⟨key _ _ ?_, key _ _ ?_⟩
  · rw [map_pow]; exact h1
  · rw [map_pow]; exact h2

/-! ### The congruences modulo `5` and `7` -/

section Mod

variable (q : ℕ) [Fact q.Prime]

/-- Over `ZMod q`, the `q`-th power is the expansion `X ↦ X^q` (Frobenius). -/
theorem pow_prime_eq_expand (f : (ZMod q)⟦X⟧) :
    f ^ q = PowerSeries.expand q (Fact.out : q.Prime).ne_zero f := by
  have := FiniteField.PowerSeries.expand_card f
  simp only [ZMod.card] at this
  exact this.symm

theorem coeff_zero_eulerSeries : eulerSeries.coeff 0 = 1 := by
  rw [eulerSeries_eq_pentagonalSeries]
  have := PowerSeries.coeff_pentagonalSeries_pentagonal (R := ℤ) 0
  simpa [pentagonal_def] using this

/-- Strong induction step shared by the congruences modulo `5` and `7`: if the coefficients of
`X^{q-r} E^{q-1}` at `X^{q(m+1)}` vanish modulo `q` (`E` Euler's product), then `q ∣ p(qm + r)`. -/
theorem dvd_partitionCount_of_coeff_zero (r : ℕ) (hr : r < q)
    (hL : ∀ m : ℕ, (X ^ (q - r) * (PowerSeries.map (Int.castRingHom (ZMod q)) eulerSeries) ^ (q - 1) :
      (ZMod q)⟦X⟧).coeff (q * m + q) = 0) :
    ∀ m : ℕ, q ∣ partitionCount (q * m + r) := by
  have hq : q.Prime := Fact.out
  set E := PowerSeries.map (Int.castRingHom (ZMod q)) eulerSeries with hE
  set P := PowerSeries.map (Int.castRingHom (ZMod q)) partitionSeries with hP
  have hPE : P * E = 1 := by
    rw [hP, hE, ← map_mul, partitionSeries_mul_eulerSeries, map_one]
  have hEq : E ^ (q - 1) = PowerSeries.expand q hq.ne_zero E * P := by
    rw [← pow_prime_eq_expand]
    have h1 : E ^ q = E ^ (q - 1) * E := by
      rw [← pow_succ, Nat.sub_add_cancel hq.one_le]
    rw [h1]
    linear_combination (-(E ^ (q - 1))) * hPE
  have hP' : ∀ n, P.coeff n = ((partitionCount n : ℕ) : ZMod q) := by
    intro n
    simp [hP, partitionSeries, coeff_map]
  have hE0 : (PowerSeries.expand q hq.ne_zero E).coeff 0 = 1 := by
    rw [coeff_zero_eq_constantCoeff, constantCoeff_expand, ← coeff_zero_eq_constantCoeff]
    simp [hE, coeff_map, coeff_zero_eulerSeries]
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  have h0 := hL m
  have hle : q - r ≤ q * m + q := by omega
  rw [hEq, coeff_X_pow_mul'] at h0
  simp only [hle, ↓reduceIte] at h0
  rw [show q * m + q - (q - r) = q * m + r by omega, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_eq_single 0] at h0
  · rw [hE0, one_mul, Nat.sub_zero, hP'] at h0
    exact (ZMod.natCast_eq_zero_iff _ _).mp h0
  · intro i hi hi0
    by_cases hd : q ∣ i
    · obtain ⟨k, rfl⟩ := hd
      have hk : k ≠ 0 := by rintro rfl; simp at hi0
      have hile := Finset.mem_range.mp hi
      have hkm : k ≤ m := by
        by_contra hlt
        have : q * (m + 1) ≤ q * k := Nat.mul_le_mul_left q (by omega)
        rw [Nat.mul_add] at this
        omega
      obtain ⟨d, rfl⟩ : ∃ d, m = k + d := ⟨m - k, by omega⟩
      have hdm : d < k + d := by omega
      have := ih d hdm
      rw [show q * (k + d) + r - q * k = q * d + r by rw [Nat.mul_add]; omega, hP',
        (ZMod.natCast_eq_zero_iff _ _).mpr this, mul_zero]
    · rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hd, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

end Mod

/-! ### The coefficients of Jacobi's series and of Euler's product, modulo `q` -/

/-- If `q ∣ 2l + 1` whenever `l(l+1)/2 = j`, then `q` divides the `X^j`-coefficient of Jacobi's
series. -/
theorem jacobiCubeCoeff_cast_eq_zero (q j : ℕ)
    (h : ∀ l : ℕ, l * (l + 1) / 2 = j → (2 * (l : ZMod q) + 1 = 0)) :
    (jacobiCubeCoeff j : ZMod q) = 0 := by
  unfold jacobiCubeCoeff
  push_cast
  apply Finset.sum_eq_zero
  intro l _
  split_ifs with hl
  · rw [h l hl, mul_zero]
  · rfl

theorem two_mul_triangular (l : ℕ) : 2 * (l * (l + 1) / 2) = l * (l + 1) :=
  Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self l)

theorem five_aux : ∀ k l : ZMod 5, k * (3 * k - 1) + l * (l + 1) + 2 = 0 → 2 * l + 1 = 0 := by
  decide

theorem seven_aux : ∀ a b : ZMod 7, a * (a + 1) + b * (b + 1) + 4 = 0 → 2 * a + 1 = 0 := by
  decide

theorem five_sum_aux : ∀ a b : ZMod 5, a + b = 4 → 2 * a + 2 * b + 2 = 0 := by decide

theorem seven_sum_aux : ∀ a b : ZMod 7, a + b = 5 → 2 * a + 2 * b + 4 = 0 := by decide

/-- The products `e_i J_j` of coefficients with `i + j ≡ 4 (mod 5)` vanish modulo `5`
(Ramanujan, No. 25, § 2). -/
theorem term_five (i j : ℕ) (hij : ((i + j : ℕ) : ZMod 5) = 4) :
    (eulerSeries.coeff i : ZMod 5) * (jacobiCubeCoeff j : ZMod 5) = 0 := by
  rw [eulerSeries_eq_pentagonalSeries]
  by_cases hi : i ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hi
    suffices (jacobiCubeCoeff j : ZMod 5) = 0 by rw [this, mul_zero]
    apply jacobiCubeCoeff_cast_eq_zero
    intro l hl
    apply five_aux (k : ZMod 5) l
    have h1 : ((k : ℤ) : ZMod 5) * (3 * (k : ZMod 5) - 1) = 2 * ((pentagonal k : ℕ) : ZMod 5) := by
      have := congrArg (Int.cast : ℤ → ZMod 5) (two_mul_natCast_pentagonal k)
      push_cast at this
      exact this.symm
    have h2 : (l : ZMod 5) * (l + 1) = 2 * (j : ZMod 5) := by
      have := two_mul_triangular l
      rw [hl] at this
      have h3 := congrArg (Nat.cast : ℕ → ZMod 5) this
      push_cast at h3
      exact h3.symm
    rw [h1, h2]
    push_cast at hij
    exact five_sum_aux _ _ hij
  · rw [PowerSeries.coeff_pentagonalSeries_eq_zero ℤ hi]
    simp

/-- The products `J_i J_j` of coefficients with `i + j ≡ 5 (mod 7)` vanish modulo `7`
(Ramanujan, No. 25, § 3). -/
theorem term_seven (i j : ℕ) (hij : ((i + j : ℕ) : ZMod 7) = 5) :
    (jacobiCubeCoeff i : ZMod 7) * (jacobiCubeCoeff j : ZMod 7) = 0 := by
  by_cases hb : ∃ b : ℕ, b * (b + 1) / 2 = j
  · obtain ⟨b, hb⟩ := hb
    suffices (jacobiCubeCoeff i : ZMod 7) = 0 by rw [this, zero_mul]
    apply jacobiCubeCoeff_cast_eq_zero
    intro a ha
    apply seven_aux (a : ZMod 7) b
    have h1 : (a : ZMod 7) * (a + 1) = 2 * (i : ZMod 7) := by
      have := two_mul_triangular a
      rw [ha] at this
      have h3 := congrArg (Nat.cast : ℕ → ZMod 7) this
      push_cast at h3
      exact h3.symm
    have h2 : (b : ZMod 7) * (b + 1) = 2 * (j : ZMod 7) := by
      have := two_mul_triangular b
      rw [hb] at this
      have h3 := congrArg (Nat.cast : ℕ → ZMod 7) this
      push_cast at h3
      exact h3.symm
    rw [h1, h2]
    push_cast at hij
    exact seven_sum_aux _ _ hij
  · suffices (jacobiCubeCoeff j : ZMod 7) = 0 by rw [this, mul_zero]
    apply jacobiCubeCoeff_cast_eq_zero
    intro l hl
    exact absurd ⟨l, hl⟩ hb

/-! ### The theorems -/

/-- **Ramanujan's congruence modulo 5** (No. 25, § 2, p. 211), given Jacobi's cube identity `E³ = ∑ (-1)ᵏ (2k+1) X^{k(k+1)/2}`: the coefficient of `X^{5m+5}` in `X E⁴ = X E J` vanishes mod 5. -/
theorem ramanujanModFive_of_cube (h : eulerSeries ^ 3 = jacobiCubeSeries) : RamanujanModFive := by

  refine @dvd_partitionCount_of_coeff_zero 5 ⟨by norm_num⟩ 4 (by norm_num) ?_
  intro m
  have hE3 : PowerSeries.map (Int.castRingHom (ZMod 5)) eulerSeries ^ 3 =
      PowerSeries.map (Int.castRingHom (ZMod 5)) jacobiCubeSeries := by rw [← map_pow, h]
  have e : (X : (ZMod 5)⟦X⟧) ^ (5 - 4) *
      (PowerSeries.map (Int.castRingHom (ZMod 5)) eulerSeries) ^ (5 - 1) =
      X * (PowerSeries.map (Int.castRingHom (ZMod 5)) eulerSeries *
        PowerSeries.map (Int.castRingHom (ZMod 5)) jacobiCubeSeries) := by
    rw [← hE3]
    norm_num
    ring
  rw [e, show 5 * m + 5 = (5 * m + 4) + 1 by ring, coeff_succ_X_mul, coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [Finset.mem_antidiagonal] at hij
  have hc : ((ij.1 + ij.2 : ℕ) : ZMod 5) = 4 := by
    rw [hij]
    push_cast
    have : (5 : ZMod 5) = 0 := by decide
    rw [this]
    ring
  have := term_five ij.1 ij.2 hc
  simpa [coeff_map, jacobiCubeSeries] using this

/-- **Ramanujan's congruence modulo 7** (No. 25, § 3, p. 212), given Jacobi's cube identity `E³ = ∑ (-1)ᵏ (2k+1) X^{k(k+1)/2}`: the coefficient of `X^{7m+7}` in `X² E⁶ = X² J²` vanishes mod 7. -/
theorem ramanujanModSeven_of_cube (h : eulerSeries ^ 3 = jacobiCubeSeries) : RamanujanModSeven := by

  refine @dvd_partitionCount_of_coeff_zero 7 ⟨by norm_num⟩ 5 (by norm_num) ?_
  intro m
  have hE3 : PowerSeries.map (Int.castRingHom (ZMod 7)) eulerSeries ^ 3 =
      PowerSeries.map (Int.castRingHom (ZMod 7)) jacobiCubeSeries := by rw [← map_pow, h]
  have e : (X : (ZMod 7)⟦X⟧) ^ (7 - 5) *
      (PowerSeries.map (Int.castRingHom (ZMod 7)) eulerSeries) ^ (7 - 1) =
      X ^ 2 * (PowerSeries.map (Int.castRingHom (ZMod 7)) jacobiCubeSeries *
        PowerSeries.map (Int.castRingHom (ZMod 7)) jacobiCubeSeries) := by
    rw [← hE3]
    norm_num
    ring
  rw [e, coeff_X_pow_mul']
  have hle : 2 ≤ 7 * m + 7 := by omega
  simp only [hle, ↓reduceIte]
  rw [show 7 * m + 7 - 2 = 7 * m + 5 by omega, coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [Finset.mem_antidiagonal] at hij
  have hc : ((ij.1 + ij.2 : ℕ) : ZMod 7) = 5 := by
    rw [hij]
    push_cast
    have : (7 : ZMod 7) = 0 := by decide
    rw [this]
    ring
  have := term_seven ij.1 ij.2 hc
  simpa [coeff_map, jacobiCubeSeries] using this

/-- **Ramanujan's corollary modulo 35** (No. 25, (3), p. 210), from the congruences modulo 5 and 7 (coprime moduli), given Jacobi's cube identity. -/
theorem ramanujanModThirtyFive_of_cube (h : eulerSeries ^ 3 = jacobiCubeSeries) :
    RamanujanModThirtyFive := by
  intro m
  have h5 := ramanujanModFive_of_cube h (7 * m + 3)
  have h7 := ramanujanModSeven_of_cube h (5 * m + 2)
  rw [show 5 * (7 * m + 3) + 4 = 35 * m + 19 by ring] at h5
  rw [show 7 * (5 * m + 2) + 5 = 35 * m + 19 by ring] at h7
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 5 7) h5 h7

end ModularFormsKB.Historical.Ramanujan
