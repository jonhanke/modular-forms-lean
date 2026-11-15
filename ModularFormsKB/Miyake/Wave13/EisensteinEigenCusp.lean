import ModularFormsKB.Miyake.Wave11.EisensteinHecke
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Miyake, proof of Theorem 4.7.2, first step: no cuspidal part in an Eisenstein eigensystem

Miyake, *Modular Forms* (Springer 1989), proof of Theorem 4.7.2, pp. 179–180. Let
`g ∈ 𝒢_k(N, χ)` be a common eigenfunction of the `T(n)`, `(n, N) = 1`, write
`g = g₁ + g₂` with `g₁ ∈ ℰ_k(N, χ)` and `g₂ ∈ 𝒮_k(N, χ)`, and suppose that `g` has the eigenvalues of
some `f_k(z; χ₁, χ₂)`, i.e. `g | T(p) = (χ₁(p) + χ₂(p) p^{k-1}) g` for the primes `p ∤ N`. The first
step of the proof is that then `g₂ = 0`, i.e. `g ∈ ℰ_k(N, χ)`. Miyake compares the Euler products
of `L(s; f_k(z; χ₁, χ₂)) = L(s, χ₁) L(s - k + 1, χ₂)` and of the primitive form attached to `g₂`
(the former has a pole at `s = k`, the latter is entire).

For `k ≥ 3` this file proves the step by a shorter route, through **Hecke's bound**
`a(n) = O(n^{k/2})` for cusp forms (Mathlib's `CuspFormClass.qExpansion_isBigO`): if
`h ∈ 𝒮_k(N, χ)` is nonzero, pick `m` with `a(m) ≠ 0`; for every prime `p ∤ Nm`, Lemma 4.5.14 gives
`a(pm) = λ_p a(m)`, so `|a(pm)| ≥ (p^{k-1} - 1) |a(m)|`, which exceeds `C (pm)^{k/2}` for large `p`
because `k - 1 > k/2`.

## Results (namespace `ModularFormsKB.Miyake.Wave13`)
* `eq_zero_of_heckeT_eq_smul_of_norm_ge`: a cusp form in `𝒮_k(N, χ)` (`k ≥ 3`) which is an
  eigenfunction of every `T(p)`, `p ∤ N` prime, with eigenvalues `|λ_p| ≥ p^{k-1} - 1` vanishes.
* `eq_zero_of_heckeT_eq_eisenstein_eigen`: in particular no nonzero cusp form has the eigenvalues
  `χ₁(p) + χ₂(p) p^{k-1}` of an Eisenstein series (`χ₂` modulo a divisor of `N`).
* `mem_eisensteinSpace_of_heckeTMod_eq_eisenstein_eigen` (**proof of Theorem 4.7.2, first step**,
  `k ≥ 3`): an element of `𝒢_k(N, χ)` with these eigenvalues lies in `ℰ_k(N, χ)`.

The weights `k = 1, 2` (where `k - 1 ≤ k/2` and Hecke's bound does not suffice) remain open; see
the loose end of this wave.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup Filter Asymptotics
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave13

open Wave4 Wave10 Wave11

variable {N : ℕ} [NeZero N]

/-- The real inequality behind the argument: for `k ≥ 3`, `A > 0` and any `c`, the inequality
`(p^{k-1} - 1) A ≤ c (p m)^{k/2}` fails for every large `p`. -/
lemma exists_large_of_weight {k : ℤ} (hk : 3 ≤ k) {A c : ℝ} (hA : 0 < A) (m : ℕ) :
    ∃ B : ℕ, ∀ p : ℕ, B ≤ p →
      c * ((p * m : ℕ) : ℝ) ^ ((k : ℝ) / 2) < ((p : ℝ) ^ (k - 1) - 1) * A := by
  set D : ℝ := |c| * (m : ℝ) ^ ((k : ℝ) / 2) / A with hD
  obtain ⟨B, hB⟩ := exists_nat_gt ((D + 1) ^ 2 + 1)
  refine ⟨B, fun p hp ↦ ?_⟩
  have hpB : (B : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by nlinarith [sq_nonneg (D + 1)]
  have hp0 : (0 : ℝ) < p := by linarith
  have hD0 : 0 ≤ D := by positivity
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  -- `p^{k-1} = p^{k/2} p^{k/2 - 1} ≥ p^{k/2} √p`
  have hsplit : (p : ℝ) ^ (k - 1) = (p : ℝ) ^ ((k : ℝ) / 2) * (p : ℝ) ^ ((k : ℝ) / 2 - 1) := by
    rw [← Real.rpow_add hp0, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  have hsqrt : Real.sqrt p ≤ (p : ℝ) ^ ((k : ℝ) / 2 - 1) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hgt : D + 1 < Real.sqrt p := by
    rw [Real.lt_sqrt (by linarith)]
    linarith
  have hpk : (1 : ℝ) ≤ (p : ℝ) ^ ((k : ℝ) / 2) := Real.one_le_rpow hp1 (by linarith)
  have hpm : ((p * m : ℕ) : ℝ) ^ ((k : ℝ) / 2) =
      (p : ℝ) ^ ((k : ℝ) / 2) * (m : ℝ) ^ ((k : ℝ) / 2) := by
    push_cast
    exact Real.mul_rpow hp0.le (Nat.cast_nonneg m)
  have hcA : c * (m : ℝ) ^ ((k : ℝ) / 2) ≤ D * A := by
    rw [hD, div_mul_cancel₀ _ hA.ne']
    exact mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
  rw [hpm, hsplit]
  set P := (p : ℝ) ^ ((k : ℝ) / 2)
  set Q := (p : ℝ) ^ ((k : ℝ) / 2 - 1)
  have hQ : D + 1 < Q := hgt.trans_le hsqrt
  have h1 : c * (P * (m : ℝ) ^ ((k : ℝ) / 2)) ≤ P * (D * A) := by
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left hcA (by positivity)
  have h2 : P * (D * A) + A ≤ P * (D * A) + P * A := by nlinarith
  nlinarith

/-- **Hecke's bound against large eigenvalues** (`k ≥ 3`): a cusp form `h ∈ 𝒮_k(N, χ)` that is an
eigenfunction of every `T(p)`, `p ∤ N` prime, with eigenvalue `λ_p` of absolute value at least
`p^{k-1} - 1`, vanishes. -/
theorem eq_zero_of_heckeT_eq_smul_of_norm_ge {k : ℤ} (hk : 3 ≤ k) {χ : DirichletCharacter ℂ N}
    (h : cuspSpace k χ) (lam : ℕ → ℂ)
    (heig : ∀ p : ℕ, p.Prime → ¬ p ∣ N → heckeT k χ p h = lam p • h)
    (hlam : ∀ p : ℕ, p.Prime → ¬ p ∣ N → (p : ℝ) ^ (k - 1) - 1 ≤ ‖lam p‖) : h = 0 := by
  by_contra hne
  obtain ⟨m, hm⟩ : ∃ m, coeff h m ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hne (ext_of_coeff fun n ↦ by rw [hall n, coeff_zero_elem])
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (coeff_zero_eq h)
  have hA : 0 < ‖coeff h m‖ := norm_pos_iff.mpr hm
  -- Hecke's bound
  have hB := CuspFormClass.qExpansion_isBigO (h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
  rw [strictWidthInfty_Gamma1] at hB
  obtain ⟨c, hc⟩ := hB.bound
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hc
  obtain ⟨B, hBig⟩ := exists_large_of_weight hk hA m
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (max (max n₀ B) (N * m + 1))
  have hpNm : ¬ p ∣ N * m := fun hd ↦ by
    have := Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne N))
      (Nat.pos_of_ne_zero hm0)) hd
    omega
  have hpN : ¬ p ∣ N := fun hd ↦ hpNm (dvd_mul_of_dvd_left hd m)
  have hpm : p.Coprime m :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd ↦ hpNm (dvd_mul_of_dvd_right hd N)
  -- `a(pm) = λ_p a(m)`
  have hcoef : coeff h (p * m) = lam p * coeff h m := by
    have h1 := coeff_heckeT_of_coprime (k := k) (χ := χ) hp.ne_zero hpm h
    rw [heig p hp hpN, coeff_smul] at h1
    exact h1.symm
  have hle := hn₀ (p * m) (by
    have : p ≤ p * m := Nat.le_mul_of_pos_right p (Nat.pos_of_ne_zero hm0)
    omega)
  change ‖coeff h (p * m)‖ ≤ _ at hle
  rw [hcoef, norm_mul, Real.norm_of_nonneg (by positivity)] at hle
  have hlow := mul_le_mul_of_nonneg_right (hlam p hp hpN) hA.le
  have hbig := hBig p (by omega)
  linarith

/-- No nonzero cusp form of weight `k ≥ 3` has the eigenvalues `χ₁(p) + χ₂(p) p^{k-1}` (`p ∤ N`) of an
Eisenstein series `f_k(z; χ₁, χ₂)`, for any Dirichlet character `χ₁` and any Dirichlet character
`χ₂` modulo a divisor of `N`. -/
theorem eq_zero_of_heckeT_eq_eisenstein_eigen {k : ℕ} (hk : 3 ≤ k) {χ : DirichletCharacter ℂ N}
    {M₁ M₂ : ℕ} (χ₁ : DirichletCharacter ℂ M₁) (χ₂ : DirichletCharacter ℂ M₂) (hM₂ : M₂ ∣ N)
    (h : cuspSpace (k : ℤ) χ)
    (heig : ∀ p : ℕ, p.Prime → ¬ p ∣ N →
      heckeT (k : ℤ) χ p h = (χ₁ p + χ₂ p * (p : ℂ) ^ (k - 1)) • h) : h = 0 := by
  refine eq_zero_of_heckeT_eq_smul_of_norm_ge (by exact_mod_cast hk) h _ heig fun p hp hpN ↦ ?_
  have hu : IsUnit (p : ZMod M₂) := (ZMod.isUnit_iff_coprime p M₂).mpr
    ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd ↦ hpN (hd.trans hM₂))
  have h2 : ‖χ₂ p‖ = 1 := by
    have := χ₂.unit_norm_eq_one hu.unit
    rwa [IsUnit.unit_spec] at this
  have h1 : ‖χ₁ p‖ ≤ 1 := χ₁.norm_le_one _
  have hpow : ‖(p : ℂ) ^ (k - 1)‖ = (p : ℝ) ^ ((k : ℤ) - 1) := by
    rw [norm_pow, Complex.norm_natCast, ← zpow_natCast]
    congr 1
    omega
  have htri := norm_sub_norm_le (χ₂ p * (p : ℂ) ^ (k - 1)) (-(χ₁ p))
  rw [norm_neg, sub_neg_eq_add, add_comm, norm_mul, h2, one_mul, hpow] at htri
  linarith

/-- `T(n)` on `𝒢_k(N, χ)` restricts to `T(n)` on `𝒮_k(N, χ)`. -/
lemma heckeTMod_cuspToMod (k : ℤ) (χ : DirichletCharacter ℂ N) (n : ℕ) (h : cuspSpace k χ) :
    heckeTMod k χ n (TauCeti.cuspToModFormCharSpace k χ.toUnitHom h) =
      TauCeti.cuspToModFormCharSpace k χ.toUnitHom (heckeT k χ n h) := by
  simp only [heckeTMod, heckeT, HeckeRing.GL2.heckeRingHomCuspCharSpace_apply,
    HeckeRing.GL2.heckeRingHomCharSpace_apply,
    HeckeRing.GL2.cuspToModFormCharSpace_twistedHeckeSlashCuspFormCharLinearMap]

/-- **Miyake, proof of Theorem 4.7.2, first step** (`k ≥ 3`): let `g ∈ 𝒢_k(N, χ)` be an
eigenfunction of every `T(p)`, `p ∤ N` prime, with the eigenvalues `χ₁(p) + χ₂(p) p^{k-1}` of some
`f_k(z; χ₁, χ₂)` (`χ₂` modulo a divisor of `N`). Then the cuspidal component of `g` vanishes:
`g ∈ ℰ_k(N, χ)`. -/
@[kb "miyake1989" "Theorem 4.7.2, proof, first step, p. 179 (k >= 3)"]
theorem mem_eisensteinSpace_of_heckeTMod_eq_eisenstein_eigen {k : ℕ} (hk : 3 ≤ k)
    {χ : DirichletCharacter ℂ N} (hχ : χ (-1) = (-1) ^ k)
    {M₁ M₂ : ℕ} (χ₁ : DirichletCharacter ℂ M₁) (χ₂ : DirichletCharacter ℂ M₂) (hM₂ : M₂ ∣ N)
    (g : modSpace (k : ℤ) χ)
    (heig : ∀ p : ℕ, p.Prime → ¬ p ∣ N →
      heckeTMod (k : ℤ) χ p g = (χ₁ p + χ₂ p * (p : ℂ) ^ (k - 1)) • g) :
    g ∈ eisensteinSpace k χ := by
  have hc := isCompl_eisensteinSpace_range_cuspSpace hk hχ
  obtain ⟨e, he, c, hcR, rfl⟩ := Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top (x := g))
  obtain ⟨h, rfl⟩ := hcR
  set ι := TauCeti.cuspToModFormCharSpace (k : ℤ) χ.toUnitHom
  suffices h0 : h = 0 by rw [h0, map_zero, add_zero]; exact he
  refine eq_zero_of_heckeT_eq_eisenstein_eigen hk χ₁ χ₂ hM₂ h fun p hp hpN ↦ ?_
  set t : ℂ := χ₁ p + χ₂ p * (p : ℂ) ^ (k - 1)
  have hpN' : p.Coprime N := (Nat.Prime.coprime_iff_not_dvd hp).2 hpN
  have hTe : heckeTMod (k : ℤ) χ p e ∈ eisensteinSpace k χ :=
    heckeTMod_mem_eisensteinSpace (by omega) hpN' he
  -- `T(p) ι h - t ι h = t e - T(p) e` lies in both summands, hence vanishes
  have hx : ι (heckeT (k : ℤ) χ p h - t • h) = t • e - heckeTMod (k : ℤ) χ p e := by
    have := heig p hp hpN
    rw [map_add, heckeTMod_cuspToMod, smul_add] at this
    rw [map_sub, map_smul]
    linear_combination (norm := module) this
  have hzero : ι (heckeT (k : ℤ) χ p h - t • h) = 0 :=
    Submodule.disjoint_def.mp hc.disjoint _
      (hx ▸ Submodule.sub_mem _ (Submodule.smul_mem _ _ he) hTe) ⟨_, rfl⟩
  have := TauCeti.cuspToModFormCharSpace_injective (k : ℤ) χ.toUnitHom (hzero.trans (map_zero ι).symm)
  exact sub_eq_zero.mp this

end ModularFormsKB.Miyake.Wave13
