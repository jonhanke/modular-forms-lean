import ModularFormsKB.Milne.Ch5.LevelOneBridge
import ModularFormsKB.Milne.Ch5.EulerFactor

/-!
# Milne, Chapter 5: Hecke operators for $\Gamma(1)$ (Proposition 5.16, Corollary 5.17)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf pp. 68–79.

$T(n)$ is `heckeT (2 * k) n` (Milne's weight $2k$ is Mathlib's weight `2 * k`), see `LevelOneBridge.lean`.
The Fourier coefficients of $f$ are `(qExpansion 1 f).coeff m`, with $q = e^{2\pi i z}$.

## Items
- Proposition 5.16(a) for modular forms (`heckeT_mul_of_coprime`, `heckeT_prime_mul_prime_pow`).
- Proposition 5.16(b) (`qExpansion_coeff_heckeT`).
- Corollary 5.17 (`qExpansion_coeff_zero_heckeT`, `qExpansion_coeff_one_heckeT`, `qExpansion_coeff_heckeT_prime`,
  `heckeT_mem_cuspFormSubmodule`).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2
open scoped MatrixGroups ModularForm ArithmeticFunction.sigma
open TauCeti (modFormCharSpace cuspFormCharSpace diamondOpNat diamondOpNat_of_coprime cuspToModFormCharSpace diamondOp_one)

namespace ModularFormsKB.Milne

/-! ### Proposition 5.16 and Corollary 5.17 -/

/-- Pointwise form of coprime multiplicativity. -/
theorem heckeT_mul_comp (w : ℤ) {m n : ℕ} (hmn : m.Coprime n) (f : ModularForm 𝒮ℒ w) :
    heckeT w (m * n) f = heckeT w m (heckeT w n f) := by
  rw [heckeT_apply_eq, heckeT_apply_eq, heckeT_apply_eq, heckeTCompositeGamma0_mul_of_coprime 1 hmn,
    map_mul]
  simp

/-- The prime-power recurrence for `heckeT`, pointwise. -/
theorem heckeT_rec (w : ℤ) {p : ℕ} (hp : p.Prime) (r : ℕ) (f : ModularForm 𝒮ℒ w) :
    heckeT w (p ^ (r + 2)) f = heckeT w p (heckeT w (p ^ (r + 1)) f) -
      ((p : ℂ) ^ (w - 1)) • heckeT w (p ^ r) f := by
  rw [heckeT_apply_eq, heckeT_apply_eq, heckeT_apply_eq, heckeT_apply_eq,
    heckeTCompositeGamma0_prime_pow 1 hp, heckeTCompositeGamma0_prime_pow 1 hp,
    heckeTCompositeGamma0_prime_pow 1 hp]
  rw [heckeTCompositeGamma0_prime 1 hp, LinearEquiv.symm_apply_apply,
    heckeRingHomCharSpace_heckeTGeneratorRecGamma0_succ_succ_apply w 1 hp.pos (Nat.coprime_one_right p)]
  simp [map_sub]

/-- Prime case of the coefficient formula, any weight, any `m`. -/
theorem coeff_heckeT_prime (w : ℤ) {p : ℕ} (hp : p.Prime) (f : ModularForm 𝒮ℒ w) (m : ℕ) :
    (qExpansion 1 (heckeT w p f)).coeff m =
      (qExpansion 1 f).coeff (p * m) +
        if p ∣ m then (p : ℂ) ^ (w - 1) * (qExpansion 1 f).coeff (m / p) else 0 := by
  rw [heckeT_apply_eq, heckeTCompositeGamma0_prime 1 hp]
  have h := qExpansion_coeff_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_prime (N := 1) (k := w) hp
    ((levelOneEquiv w).symm f : ModularForm ((Gamma1 1).map (mapGL ℝ)) w) m
  have h2 : diamondOpNat w p ((levelOneEquiv w).symm f : ModularForm ((Gamma1 1).map (mapGL ℝ)) w) = ((levelOneEquiv w).symm f : ModularForm ((Gamma1 1).map (mapGL ℝ)) w) := by
    rw [diamondOpNat_of_coprime w (Nat.coprime_one_right p), Subsingleton.elim (ZMod.unitOfCoprime p _) 1, diamondOp_one]
    rfl
  rw [h2] at h
  have _ : NeZero p := ⟨hp.ne_zero⟩
  have h3 := coe_heckeRingHomCharSpace_heckeTGeneratorGamma0 w 1 hp ((levelOneEquiv w).symm f)
  rw [heckeTNat_def] at h3
  have h4 : ⇑(levelOneEquiv w (heckeRingHomCharSpace w 1 (heckeTGeneratorGamma0 1 p)
      ((levelOneEquiv w).symm f))) = ⇑(heckeSlashGamma1ModularFormEnd w (diagCosetGamma1 1 p)
        ((levelOneEquiv w).symm f : ModularForm ((Gamma1 1).map (mapGL ℝ)) w)) :=
    (coe_levelOneEquiv _ _).trans (congrArg _ h3)
  have h5 := congrArg (fun g => (qExpansion 1 g).coeff m) h4
  rw [h5, h]
  rfl

/-- `T(1)` is the identity. -/
theorem heckeT_one (w : ℤ) (f : ModularForm 𝒮ℒ w) : heckeT w 1 f = f := by
  rw [heckeT_apply_eq, heckeTCompositeGamma0_one, map_one]
  simp

/-- A coefficient of `f - c • g`. -/
theorem coeff_sub_smul (w : ℤ) (f g : ModularForm 𝒮ℒ w) (c : ℂ) (m : ℕ) :
    (qExpansion 1 ⇑(f - c • g)).coeff m =
      (qExpansion 1 f).coeff m - c * (qExpansion 1 g).coeff m := by
  rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, map_sub, PowerSeries.coeff_smul,
    smul_eq_mul]

/-- At level one the trivial character is identically `1`. -/
theorem ofUnitHom_levelOne (d : ℕ) :
    (MulChar.ofUnitHom (1 : (ZMod 1)ˣ →* ℂˣ) : DirichletCharacter ℂ 1) d = 1 := by
  have : ((d : ℕ) : ZMod 1) = 1 := Subsingleton.elim _ _
  rw [this, MulChar.map_one]

/-- The coefficient formula for positive indices. -/
theorem coeff_heckeT_pos (w : ℤ) {n : ℕ} (hn : n ≠ 0) (f : ModularForm 𝒮ℒ w) {m : ℕ} (hm : m ≠ 0) :
    (qExpansion 1 (heckeT w n f)).coeff m =
      ∑ a ∈ (Nat.gcd m n).divisors, (a : ℂ) ^ (w - 1) * (qExpansion 1 f).coeff (m * n / a ^ 2) := by
  have h := qExpansion_coeff_heckeRingHomCharSpace_heckeTCompositeGamma0_of_ne_zero (N := 1) (k := w)
    (χ := 1) hn ((levelOneEquiv w).symm f) hm
  have h5 := congrArg (fun g : ℍ → ℂ => (qExpansion 1 g).coeff m)
    (coe_levelOneEquiv w (heckeRingHomCharSpace (N := 1) w 1 (heckeTCompositeGamma0 1 n)
      ((levelOneEquiv w).symm f)))
  rw [heckeT_apply_eq]
  refine h5.trans (h.trans (Finset.sum_congr rfl fun a _ => ?_))
  rw [ofUnitHom_levelOne, one_mul]
  rfl

/-- Sums of `a ^ z` over divisors are multiplicative. -/
theorem sum_divisors_zpow_mul (z : ℤ) {m n : ℕ} (h : m.Coprime n) :
    ∑ a ∈ (m * n).divisors, (a : ℂ) ^ z =
      (∑ a ∈ m.divisors, (a : ℂ) ^ z) * ∑ a ∈ n.divisors, (a : ℂ) ^ z := by
  let g : ArithmeticFunction ℂ := ⟨fun a => if a = 0 then 0 else (a : ℂ) ^ z, by simp⟩
  have hg : g.IsMultiplicative := by
    refine ⟨by simp [g], fun {m n} _ => ?_⟩
    simp only [g, ArithmeticFunction.coe_mk]
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp [hm, hn, mul_zpow]
  have key : ∀ n : ℕ, ∑ a ∈ n.divisors, (a : ℂ) ^ z =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * g) n := by
    intro n
    rw [ArithmeticFunction.coe_zeta_mul_apply]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp [g, (Nat.pos_of_mem_divisors ha).ne']
  rw [key, key, key]
  exact (ArithmeticFunction.isMultiplicative_zeta.natCast.mul hg).map_mul_of_coprime h

/-- Sum of `a ^ z` over divisors of a prime power, as a geometric sum. -/
theorem sum_divisors_prime_pow_zpow (z : ℤ) {p : ℕ} (hp : p.Prime) (v : ℕ) :
    ∑ a ∈ (p ^ v).divisors, (a : ℂ) ^ z = ∑ i ∈ Finset.range (v + 1), ((p : ℂ) ^ z) ^ i := by
  rw [Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.cast_pow, ← zpow_natCast (p : ℂ) i, ← zpow_mul, ← zpow_natCast ((p : ℂ) ^ z) i,
    ← zpow_mul, mul_comm]

/-- Constant term of `T(p^v) f`. -/
theorem coeff_zero_heckeT_prime_pow (w : ℤ) {p : ℕ} (hp : p.Prime) (v : ℕ) :
    ∀ f : ModularForm 𝒮ℒ w, (qExpansion 1 (heckeT w (p ^ v) f)).coeff 0 =
      (∑ a ∈ (p ^ v).divisors, (a : ℂ) ^ (w - 1)) * (qExpansion 1 f).coeff 0 := by
  have hx : (p : ℂ) ^ (w - 1) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  have key : ∀ v, (∀ f : ModularForm 𝒮ℒ w, (qExpansion 1 (heckeT w (p ^ v) f)).coeff 0 =
      (∑ a ∈ (p ^ v).divisors, (a : ℂ) ^ (w - 1)) * (qExpansion 1 f).coeff 0) ∧
      (∀ f : ModularForm 𝒮ℒ w, (qExpansion 1 (heckeT w (p ^ (v + 1)) f)).coeff 0 =
      (∑ a ∈ (p ^ (v + 1)).divisors, (a : ℂ) ^ (w - 1)) * (qExpansion 1 f).coeff 0) := by
    intro v
    induction v with
    | zero =>
      refine ⟨fun f => ?_, fun f => ?_⟩
      · simp [heckeT_one]
      · have := coeff_heckeT_prime w hp f 0
        simp only [zero_add, pow_one, mul_zero, dvd_zero, ite_true, Nat.zero_div] at this ⊢
        rw [this, Nat.Prime.sum_divisors hp]
        simp [add_mul]
        ring
    | succ v ih =>
      refine ⟨ih.2, fun f => ?_⟩
      rw [heckeT_rec w hp v f, coeff_sub_smul, coeff_heckeT_prime w hp]
      simp only [mul_zero, dvd_zero, ite_true, Nat.zero_div]
      rw [ih.1, ih.2]
      rw [sum_divisors_prime_pow_zpow _ hp, sum_divisors_prime_pow_zpow _ hp,
        sum_divisors_prime_pow_zpow _ hp, Finset.sum_range_succ _ (v + 1 + 1),
        Finset.sum_range_succ _ (v + 1)]
      ring
  exact (key v).1

/-- Constant term of `T(n) f`, general form. -/
theorem coeff_zero_heckeT (w : ℤ) {n : ℕ} (hn : n ≠ 0) (f : ModularForm 𝒮ℒ w) :
    (qExpansion 1 (heckeT w n f)).coeff 0 =
      (∑ a ∈ n.divisors, (a : ℂ) ^ (w - 1)) * (qExpansion 1 f).coeff 0 := by
  induction n using Nat.recOnPosPrimePosCoprime generalizing f with
  | prime_pow p v hp hv => exact coeff_zero_heckeT_prime_pow w hp v f
  | zero => exact absurd rfl hn
  | one => simp [heckeT_one]
  | coprime a b _ _ hab ha hb =>
    rw [heckeT_mul_comp w hab, ha (by omega), hb (by omega), sum_divisors_zpow_mul _ hab]
    ring

/-- **Milne, Proposition 5.16(b).** For a modular form $f = \sum_{m \ge 0} c(m)q^m$ of weight $2k$ for $\Gamma(1)$
and $n \ge 1$, $T(n)f = \sum_{m \ge 0}\gamma(m)q^m$ with
$\gamma(m) = \sum_{a \mid (m,n),\, a \ge 1} a^{2k-1}c(mn/a^2)$. (For $m = 0$, $\gcd(0, n) = n$.) -/
@[kb "milne2017mf" "Section 5, Proposition 5.16(b) (pdf p. 73)"]
theorem qExpansion_coeff_heckeT (k : ℕ) {n : ℕ} (hn : n ≠ 0) (f : ModularForm 𝒮ℒ (2 * k)) (m : ℕ) :
    (qExpansion 1 (heckeT (2 * k) n f)).coeff m =
      ∑ a ∈ (Nat.gcd m n).divisors, (a : ℂ) ^ ((2 * k : ℤ) - 1) * (qExpansion 1 f).coeff (m * n / a ^ 2) := by
  by_cases hm : m = 0
  · subst hm
    rw [coeff_zero_heckeT _ hn]
    simp [Nat.gcd_zero_left, Finset.sum_mul]
  · exact coeff_heckeT_pos _ hn f hm

/-- **Milne, Proposition 5.16(a)(i)**, for modular forms: $T(m)T(n) = T(mn)$ for coprime $m, n$. -/
@[kb "milne2017mf" "Section 5, Proposition 5.16(a)(i) (pdf p. 73)"]
theorem heckeT_mul_of_coprime (k : ℕ) {m n : ℕ} (hmn : m.Coprime n) :
    heckeT (2 * k) m * heckeT (2 * k) n = heckeT (2 * k) (m * n) :=
  LinearMap.ext fun f => (heckeT_mul_comp (2 * k) hmn f).symm

/-- **Milne, Proposition 5.16(a)(ii)**, for modular forms:
$T(p)T(p^n) = T(p^{n+1}) + p^{2k-1}T(p^{n-1})$ for $p$ prime and $n \ge 1$. -/
@[kb "milne2017mf" "Section 5, Proposition 5.16(a)(ii) (pdf p. 73)"]
theorem heckeT_prime_mul_prime_pow (k : ℕ) {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 1 ≤ n) :
    heckeT (2 * k) p * heckeT (2 * k) (p ^ n) =
      heckeT (2 * k) (p ^ (n + 1)) + ((p : ℂ) ^ ((2 * k : ℤ) - 1)) • heckeT (2 * k) (p ^ (n - 1)) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  refine LinearMap.ext fun f => ?_
  have h := heckeT_rec (2 * k) hp r f
  rw [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, Nat.add_sub_cancel]
  rw [show r + 1 + 1 = r + 2 from rfl, h]
  abel

/-- **Milne, Corollary 5.17(a)**, constant term: $\gamma(0) = \sigma_{2k-1}(n)c(0)$. -/
@[kb "milne2017mf" "Section 5, Corollary 5.17(a) (pdf p. 74)"]
theorem qExpansion_coeff_zero_heckeT (k : ℕ) {n : ℕ} (hn : n ≠ 0) (f : ModularForm 𝒮ℒ (2 * k)) :
    (qExpansion 1 (heckeT (2 * k) n f)).coeff 0 =
      (∑ a ∈ n.divisors, (a : ℂ) ^ ((2 * k : ℤ) - 1)) * (qExpansion 1 f).coeff 0 :=
  coeff_zero_heckeT _ hn f

/-- **Milne, Corollary 5.17(a)**, first coefficient: $\gamma(1) = c(n)$. -/
@[kb "milne2017mf" "Section 5, Corollary 5.17(a) (pdf p. 74)"]
theorem qExpansion_coeff_one_heckeT (k : ℕ) {n : ℕ} (hn : n ≠ 0) (f : ModularForm 𝒮ℒ (2 * k)) :
    (qExpansion 1 (heckeT (2 * k) n f)).coeff 1 = (qExpansion 1 f).coeff n := by
  rw [coeff_heckeT_pos _ hn f one_ne_zero]
  simp

/-- **Milne, Corollary 5.17(b)**: for $n = p$ prime, $\gamma(m) = c(pm)$ if $p \nmid m$ and
$\gamma(m) = c(pm) + p^{2k-1}c(m/p)$ if $p \mid m$. -/
@[kb "milne2017mf" "Section 5, Corollary 5.17(b) (pdf p. 74)"]
theorem qExpansion_coeff_heckeT_prime (k : ℕ) {p : ℕ} (hp : p.Prime) (f : ModularForm 𝒮ℒ (2 * k)) (m : ℕ) :
    (qExpansion 1 (heckeT (2 * k) p f)).coeff m =
      (qExpansion 1 f).coeff (p * m) +
        if p ∣ m then (p : ℂ) ^ ((2 * k : ℤ) - 1) * (qExpansion 1 f).coeff (m / p) else 0 :=
  coeff_heckeT_prime _ hp f m

/-- **Milne, Corollary 5.17(c)**: $T(n)$ maps cusp forms to cusp forms. -/
@[kb "milne2017mf" "Section 5, Corollary 5.17(c) (pdf p. 74)"]
theorem heckeT_mem_cuspFormSubmodule (k : ℕ) {n : ℕ} (hn : n ≠ 0) {f : ModularForm 𝒮ℒ (2 * k)}
    (hf : f ∈ cuspFormSubmodule 𝒮ℒ (2 * k)) : heckeT (2 * k) n f ∈ cuspFormSubmodule 𝒮ℒ (2 * k) := by
  rw [mem_cuspFormSubmodule_iff, isCuspForm_iff_coeffZero_eq_zero] at hf ⊢
  rw [coeff_zero_heckeT _ hn, hf, mul_zero]

/-- The operator `heckeTCusp` on cusp forms is the restriction of `heckeT`. -/
theorem toModularForm_heckeTCusp (w : ℤ) (n : ℕ) (f : CuspForm 𝒮ℒ w) :
    CuspForm.toModularFormₗ (heckeTCusp w n f) = heckeT w n (CuspForm.toModularFormₗ f) := by
  ext z
  have hc : cuspToModFormCharSpace w 1 ((levelOneCuspEquiv w).symm f) =
      (levelOneEquiv w).symm (CuspForm.toModularFormₗ f) :=
    Subtype.ext (DFunLike.coe_injective rfl)
  have key := cuspToModFormCharSpace_twistedHeckeSlashCuspFormCharLinearMap (k := w) (χ := 1)
    (heckeTCompositeGamma0 1 n) ((levelOneCuspEquiv w).symm f)
  rw [hc] at key
  exact congrArg (fun x : modFormCharSpace w 1 => ((x : ModularForm ((Gamma1 1).map (mapGL ℝ)) w) : ℍ → ℂ) z) key

end ModularFormsKB.Milne
