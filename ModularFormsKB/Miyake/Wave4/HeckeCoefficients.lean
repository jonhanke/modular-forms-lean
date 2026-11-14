import ModularFormsKB.Miyake.Wave4.Notation
import TauCeti.NumberTheory.ModularForms.Newforms.Coefficient
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.AtkinLehner

/-!
# Miyake §4.5: the Hecke algebra of `Γ₀(N)`, coefficients of `T(m) f`, eigenforms

Miyake, *Modular Forms* (Springer 1989), §4.5, pp. 133–149. Notation from `Notation.lean`:
`cuspSpace k χ = 𝒮_k(N, χ)`, `heckeT k χ n = T(n)`, `heckeTT k χ l m = T(l, m)`, `coeff f n`
the `n`-th Fourier coefficient at `∞`.

## Results
* Theorem 4.5.3 (1) for `ℛ(N)`: the Hecke ring `ℛ(Γ₀(N), Δ₀(N))` is commutative
  (`heckeRing_mul_comm`). Miyake's second algebra `ℛ*(N)` (built on `Δ₀*(N)`) is not treated.
* Lemma 4.5.8 (2) and Theorem 4.5.13 (1), in the Hecke ring and on `𝒮_k(N, χ)`:
  `T(m) T(n) = Σ_{d ∣ (m, n)} d T(d, d) T(mn/d²)`; on `𝒮_k(N, χ)`,
  `T(m) T(n) = Σ_{d ∣ (m, n)} χ(d) d^{k-1} T(mn/d²)`.
* Lemma 4.5.14: `b(n) = Σ_{0 < d ∣ (m, n)} χ(d) d^{k-1} c(mn/d²)` on `𝒮_k(N, χ)` for all `n`,
  and on `𝒢_k(N, χ)` for `n ≥ 1` (the constant term `n = 0` of a non-cusp form is not covered).
* Lemma 4.5.15 (1), with (4.5.37).
* Theorem 4.5.16, with Miyake's condition (2) in its coefficient form (see the docstring).

Proofs: through Tau Ceti's composite Hecke element and its coefficient formula
(`HeckeRing.GL2.qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0`,
`HeckeRing.GL2.heckeTCompositeGamma0_mul_eq_sum_divisors_gcd`).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups HeckeCosetModule

noncomputable section

namespace ModularFormsKB.Miyake.Wave4

variable {N : ℕ} [NeZero N]

/-- **Miyake, Theorem 4.5.3 (1)** for `ℛ(N)`: the Hecke ring `ℛ(Γ₀(N), Δ₀(N))` over `ℤ` is
commutative. -/
@[kb "miyake1989" "Theorem 4.5.3 (1), p. 133 (R(N))"]
theorem heckeRing_mul_comm (a b : 𝕋 (HeckeRing.GL2.Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ) :
    a * b = b * a := by
  exact HeckeCosetModule.mul_comm_of_antiInvolution ℤ (HeckeRing.GL2.atkinLehnerAntiInvolution N)
    (HeckeRing.GL2.atkinLehnerAntiInvolution_onHeckeCoset_eq_self N) a b

/-- **Miyake, Theorem 4.5.13 (1)** in the Hecke ring (Lemma 4.5.8 (2) is the case `(m, n) = 1`):
for `m, n ≥ 1`, `T(m) T(n) = Σ_{d ∣ (m, n)} d T(d, d) T(mn/d²)`. -/
@[kb "miyake1989" "Theorem 4.5.13 (1), p. 147 (Hecke ring)"]
theorem heckeT_mul_heckeT_ring {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    HeckeRing.GL2.heckeTCompositeGamma0 N m * HeckeRing.GL2.heckeTCompositeGamma0 N n =
      ∑ d ∈ (Nat.gcd m n).divisors, (d : ℤ) •
        (HeckeRing.GL2.diagElemGamma0 N ![d, d] *
          HeckeRing.GL2.heckeTCompositeGamma0 N (m * n / d ^ 2)) := by
  exact HeckeRing.GL2.heckeTCompositeGamma0_mul_eq_sum_divisors_gcd N hm hn

/-- **Miyake, Lemma 4.5.8 (2)**: `T(m) T(n) = T(mn)` for coprime `m`, `n`, in the Hecke ring. -/
@[kb "miyake1989" "Lemma 4.5.8 (2), p. 141"]
theorem heckeT_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) :
    HeckeRing.GL2.heckeTCompositeGamma0 N (m * n) =
      HeckeRing.GL2.heckeTCompositeGamma0 N m * HeckeRing.GL2.heckeTCompositeGamma0 N n := by
  exact HeckeRing.GL2.heckeTCompositeGamma0_mul_of_coprime N hmn

/-- **Miyake, Theorem 4.5.13 (1)** on `𝒮_k(N, χ)`: for `m, n ≥ 1`,
`T(m) T(n) = Σ_{d ∣ (m, n)} χ(d) d^{k-1} T(mn/d²)`. -/
@[kb "miyake1989" "Theorem 4.5.13 (1), p. 147 (on S_k(N, chi))"]
theorem heckeT_mul_heckeT (k : ℤ) (χ : DirichletCharacter ℂ N) {m n : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) :
    heckeT k χ m * heckeT k χ n =
      ∑ d ∈ (Nat.gcd m n).divisors, (χ d * (d : ℂ) ^ (k - 1)) • heckeT k χ (m * n / d ^ 2) := by
  unfold heckeT
  rw [← map_mul, HeckeRing.GL2.heckeTCompositeGamma0_mul_eq_sum_divisors_gcd N hm hn, map_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  rw [map_zsmul, map_mul]
  have h := heckeTT_self k χ hd0
  change (d : ℤ) • (heckeTT k χ d d * _) = _
  rw [h, smul_mul_assoc, one_mul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
  congr 1
  have hk : k - 1 = k - 2 + 1 := by ring
  rw [hk, zpow_add_one₀ (Nat.cast_ne_zero.mpr hd0.ne')]
  push_cast
  ring

/-- **Miyake, Lemma 4.5.14** on `𝒮_k(N, χ)`: if `f = Σ c(n) qⁿ` and `f ∣ T(m) = Σ b(n) qⁿ`
(`m ≥ 1`), then `b(n) = Σ_{0 < d ∣ (m, n)} χ(d) d^{k-1} c(mn/d²)` for every `n ≥ 0`. -/
@[kb "miyake1989" "Lemma 4.5.14, p. 147 (cusp forms)"]
theorem coeff_heckeT (k : ℤ) (χ : DirichletCharacter ℂ N) {m : ℕ} (hm : m ≠ 0)
    (f : cuspSpace k χ) (n : ℕ) :
    coeff (heckeT k χ m f) n =
      ∑ d ∈ (Nat.gcd m n).divisors, χ d * (d : ℂ) ^ (k - 1) * coeff f (m * n / d ^ 2) := by
  have h := HeckeRing.GL2.qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0
    (k := k) (χ := χ.toUnitHom) hm f n
  rw [Nat.gcd_comm m n, mul_comm m n]
  simpa only [ofUnitHom_toUnitHom] using h

/-- **Miyake, Lemma 4.5.14** on `𝒢_k(N, χ)`, at the indices `n ≥ 1`. -/
@[kb "miyake1989" "Lemma 4.5.14, p. 147 (modular forms, n >= 1)"]
theorem coeffMod_heckeTMod (k : ℤ) (χ : DirichletCharacter ℂ N) {m : ℕ} (hm : m ≠ 0)
    (f : modSpace k χ) {n : ℕ} (hn : n ≠ 0) :
    coeffMod (heckeTMod k χ m f) n =
      ∑ d ∈ (Nat.gcd m n).divisors, χ d * (d : ℂ) ^ (k - 1) * coeffMod f (m * n / d ^ 2) := by
  have h := HeckeRing.GL2.qExpansion_coeff_heckeRingHomCharSpace_heckeTCompositeGamma0_of_ne_zero
    (k := k) (χ := χ.toUnitHom) hm f hn
  rw [Nat.gcd_comm m n, mul_comm m n]
  simpa only [ofUnitHom_toUnitHom] using h

section Helpers

variable {k : ℤ} {χ : DirichletCharacter ℂ N}

/-- Scalar multiples act on coefficients by multiplication. -/
lemma coeff_smul (t : ℂ) (f : cuspSpace k χ) (n : ℕ) : coeff (t • f) n = t * coeff f n := by
  simp only [coeff, Submodule.coe_smul, FunLike.coe_smul]
  rw [ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _),
    PowerSeries.coeff_smul, smul_eq_mul]

/-- The constant coefficient of a cusp form vanishes. -/
lemma coeff_zero_eq (f : cuspSpace k χ) : coeff f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero _ one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _)

/-- The coefficients of the zero element vanish. -/
lemma coeff_zero_elem (n : ℕ) : coeff (0 : cuspSpace k χ) n = 0 := by
  have := coeff_smul (0 : ℂ) (0 : cuspSpace k χ) n
  simpa using this

/-- An element of `𝒮_k(N, χ)` is determined by its Fourier coefficients. -/
lemma ext_of_coeff {f g : cuspSpace k χ} (h : ∀ n, coeff f n = coeff g n) : f = g :=
  Subtype.ext (CuspForm.qExpansion_injective one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map N) (PowerSeries.ext h))

lemma coeff_heckeT_of_coprime {m n : ℕ} (hm : m ≠ 0) (hmn : m.Coprime n) (f : cuspSpace k χ) :
    coeff (heckeT k χ m f) n = coeff f (m * n) := by
  rw [coeff_heckeT k χ hm f n, Nat.Coprime.gcd_eq_one hmn, Nat.divisors_one,
    Finset.sum_singleton]
  simp

lemma coeff_heckeT_prime_mul {p : ℕ} (hp : p.Prime) (f : cuspSpace k χ) (m : ℕ) :
    coeff (heckeT k χ p f) (p * m) =
      coeff f (p * (p * m)) + χ p * (p : ℂ) ^ (k - 1) * coeff f m := by
  rw [coeff_heckeT k χ hp.ne_zero f (p * m), Nat.gcd_eq_left (dvd_mul_right p m), hp.divisors,
    Finset.sum_pair hp.one_lt.ne]
  have h2 : p * (p * m) / p ^ 2 = m := by
    rw [show p * (p * m) = p ^ 2 * m by ring, Nat.mul_div_cancel_left _ (pow_pos hp.pos 2)]
  rw [h2]
  simp only [Nat.cast_one, map_one, one_zpow, mul_one, one_mul, Nat.div_one, one_pow]

lemma heckeT_mul_of_coprime' {a b : ℕ} (hab : a.Coprime b) :
    heckeT k χ (a * b) = heckeT k χ a * heckeT k χ b := by
  unfold heckeT
  rw [heckeT_mul_of_coprime hab, map_mul]

lemma heckeT_one : heckeT k χ 1 = 1 := by
  unfold heckeT
  rw [HeckeRing.GL2.heckeTCompositeGamma0_one, map_one]

lemma heckeT_prime_pow_add_two {p : ℕ} (hp : p.Prime) (r : ℕ) :
    heckeT k χ (p ^ (r + 2)) = heckeT k χ p * heckeT k χ (p ^ (r + 1)) -
      (χ p * (p : ℂ) ^ (k - 1)) • heckeT k χ (p ^ r) := by
  have h := heckeT_mul_heckeT k χ (m := p) (n := p ^ (r + 1)) hp.ne_zero
    (pow_ne_zero _ hp.ne_zero)
  have hg : Nat.gcd p (p ^ (r + 1)) = p := Nat.gcd_eq_left (dvd_pow_self p (by omega))
  rw [hg, hp.divisors, Finset.sum_pair hp.one_lt.ne] at h
  have h1 : p * p ^ (r + 1) / 1 ^ 2 = p ^ (r + 2) := by rw [one_pow, Nat.div_one]; ring
  have h2 : p * p ^ (r + 1) / p ^ 2 = p ^ r := by
    rw [show p * p ^ (r + 1) = p ^ 2 * p ^ r by ring, Nat.mul_div_cancel_left _ (pow_pos hp.pos 2)]
  rw [h1, h2] at h
  simp only [Nat.cast_one, map_one, one_zpow, mul_one, one_smul] at h
  rw [h]
  abel

lemma exists_heckeT_prime_pow_eq_smul (f : cuspSpace k χ) {p : ℕ} (hp : p.Prime)
    (hf : ∃ t : ℂ, heckeT k χ p f = t • f) (r : ℕ) :
    (∃ s : ℂ, heckeT k χ (p ^ r) f = s • f) ∧ (∃ s : ℂ, heckeT k χ (p ^ (r + 1)) f = s • f) := by
  induction r with
  | zero =>
    refine ⟨⟨1, ?_⟩, ?_⟩
    · rw [pow_zero, heckeT_one]; simp
    · simpa using hf
  | succ r ih =>
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
    obtain ⟨t, ht⟩ := hf
    refine ⟨⟨b, hb⟩, ⟨t * b - (χ p * (p : ℂ) ^ (k - 1)) * a, ?_⟩⟩
    rw [heckeT_prime_pow_add_two hp r]
    simp only [LinearMap.sub_apply, mul_apply_eq_comp, LinearMap.smul_apply, hb, ha,
      map_smul, ht]
    module

lemma exists_heckeT_eq_smul_aux (f : cuspSpace k χ) (M : Set ℕ) (hM : ∀ p ∈ M, p.Prime)
    (hf : ∀ p ∈ M, ∃ t : ℂ, heckeT k χ p f = t • f) :
    ∀ m : ℕ, m ≠ 0 → (∀ p ∈ m.primeFactors, p ∈ M) → ∃ t : ℂ, heckeT k χ m f = t • f := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro _ hmM
    have hpM : p ∈ M := hmM p (by simp [Nat.primeFactors_prime_pow hn.ne' hp])
    exact (exists_heckeT_prime_pow_eq_smul f hp (hf p hpM) n).1
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; exact ⟨1, by rw [heckeT_one]; simp⟩
  | coprime a b ha hb hab iha ihb =>
    intro hne hmM
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    obtain ⟨s, hs⟩ := iha ha0 fun p hp ↦
      hmM p (Nat.primeFactors_mono (dvd_mul_right a b) hne hp)
    obtain ⟨u, hu⟩ := ihb hb0 fun p hp ↦
      hmM p (Nat.primeFactors_mono (dvd_mul_left b a) hne hp)
    refine ⟨s * u, ?_⟩
    rw [heckeT_mul_of_coprime' hab, mul_apply_eq_comp, hu, map_smul, hs, smul_smul, mul_comm]

lemma coeff_eq_of_eigen {m : ℕ} (hm : m ≠ 0) {f : cuspSpace k χ} {t : ℂ}
    (h : heckeT k χ m f = t • f) : coeff f m = t * coeff f 1 := by
  have := coeff_heckeT_of_coprime hm (Nat.coprime_one_right m) f
  rw [h, coeff_smul] at this
  simpa using this.symm

lemma coeff_one_ne_zero_of_eigen {f : cuspSpace k χ} (hf : f ≠ 0)
    (h : ∀ n : ℕ, n ≠ 0 → ∃ t : ℂ, heckeT k χ n f = t • f) : coeff f 1 ≠ 0 := by
  intro h1
  apply hf
  apply ext_of_coeff
  intro n
  rw [coeff_zero_elem]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact coeff_zero_eq f
  · obtain ⟨t, ht⟩ := h n hn.ne'
    rw [coeff_eq_of_eigen hn.ne' ht, h1, mul_zero]

end Helpers

/-- **Miyake, Lemma 4.5.15 (1)** with (4.5.37). Let `f = Σ c(n) qⁿ ∈ 𝒮_k(N, χ)` and `M` a set of
primes with `f ∣ T(p) = t(p) f` for `p ∈ M`. If every prime factor of `m ≥ 1` lies in `M`, then `f`
is an eigenfunction of `T(m)`, `f ∣ T(m) = t f`, and `c(mn) = t c(n)` for every `n` prime to `m`;
in particular (`n = 1`) `c(m) = t c(1)`. -/
@[kb "miyake1989" "Lemma 4.5.15 (1), p. 148"]
theorem exists_heckeT_eq_smul_of_forall_prime (k : ℤ) (χ : DirichletCharacter ℂ N)
    (f : cuspSpace k χ) (M : Set ℕ) (hM : ∀ p ∈ M, p.Prime)
    (hf : ∀ p ∈ M, ∃ t : ℂ, heckeT k χ p f = t • f) {m : ℕ} (hm : m ≠ 0)
    (hmM : ∀ p ∈ m.primeFactors, p ∈ M) :
    ∃ t : ℂ, heckeT k χ m f = t • f ∧ (∀ n, n.Coprime m → coeff f (m * n) = t * coeff f n) ∧
      coeff f m = t * coeff f 1 := by
  obtain ⟨t, ht⟩ := exists_heckeT_eq_smul_aux f M hM hf m hm hmM
  refine ⟨t, ht, fun n hn ↦ ?_, coeff_eq_of_eigen hm ht⟩
  have := coeff_heckeT_of_coprime hm hn.symm f
  rw [ht, coeff_smul] at this
  exact this.symm

/-- **Miyake, Theorem 4.5.16.** Let `f = Σ c(n) qⁿ` be a nonzero element of `𝒮_k(N, χ)`. Then
`f` is a common eigenfunction of all `T(n)` (`n ≥ 1`) if and only if `c(1) ≠ 0` and
`L(s; f) = c(1) Π_p (1 - t(p) p^{-s} + χ(p) p^{k-1-2s})^{-1}` (with `t(p) = c(p)/c(1)`).

The Euler product is stated through its coefficients, which is what the identity of formal
Dirichlet series means: `c(1) c(uv) = c(u) c(v)` for coprime `u, v`, and
`c(1) c(p^{r+2}) = c(p) c(p^{r+1}) - χ(p) p^{k-1} c(1) c(p^r)` for every prime `p` and `r ≥ 0`
(the convergent `L`-series form is not treated here). -/
@[kb "miyake1989" "Theorem 4.5.16, p. 149 (Euler product in coefficient form)"]
theorem forall_heckeT_eigen_iff (k : ℤ) (χ : DirichletCharacter ℂ N) (f : cuspSpace k χ)
    (hf : f ≠ 0) :
    (∀ n : ℕ, n ≠ 0 → ∃ t : ℂ, heckeT k χ n f = t • f) ↔
      coeff f 1 ≠ 0 ∧
      (∀ u v : ℕ, u.Coprime v → coeff f 1 * coeff f (u * v) = coeff f u * coeff f v) ∧
      ∀ (p : ℕ), p.Prime → ∀ r : ℕ,
        coeff f 1 * coeff f (p ^ (r + 2)) =
          coeff f p * coeff f (p ^ (r + 1)) -
            χ p * (p : ℂ) ^ (k - 1) * coeff f 1 * coeff f (p ^ r) := by
  constructor
  · intro h
    have hc1 := coeff_one_ne_zero_of_eigen hf h
    choose! t ht using h
    have hct : ∀ n, n ≠ 0 → coeff f n = t n * coeff f 1 := fun n hn ↦
      coeff_eq_of_eigen hn (ht n hn)
    refine ⟨hc1, ?_, ?_⟩
    · intro u v huv
      by_cases hu : u = 0
      · subst hu
        have := (Nat.coprime_zero_left v).1 huv
        subst this
        simp [mul_comm]
      by_cases hv : v = 0
      · subst hv
        have := (Nat.coprime_zero_right u).1 huv
        subst this
        simp
      have h1 := coeff_heckeT_of_coprime hu huv f
      rw [ht u hu, coeff_smul] at h1
      rw [hct u hu, ← h1]
      ring
    · intro p hp r
      have h1 := coeff_heckeT_prime_mul hp f (p ^ r)
      rw [← pow_succ', ← pow_succ', ht p hp.ne_zero, coeff_smul] at h1
      rw [hct p hp.ne_zero]
      linear_combination (-(coeff f 1)) * h1
  · rintro ⟨hc1, hmul, hrec⟩
    have hprime : ∀ p : ℕ, p.Prime → heckeT k χ p f = (coeff f p / coeff f 1) • f := by
      intro p hp
      apply ext_of_coeff
      intro m
      rw [coeff_smul]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [coeff_zero_eq, coeff_zero_eq]; ring
      by_cases hpm : p ∣ m
      · obtain ⟨m', rfl⟩ := hpm
        have hm' : m' ≠ 0 := by rintro rfl; simp at hm
        obtain ⟨e, m'', hm'', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm' p hp.ne_one
        rw [coeff_heckeT_prime_mul hp f]
        have hcop : ∀ j : ℕ, (p ^ j).Coprime m'' := fun j ↦
          Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp).2 hm'')
        have e2 := hmul _ _ (hcop (e + 2))
        have e1 := hmul _ _ (hcop (e + 1))
        have e0 := hmul _ _ (hcop e)
        have hr := hrec p hp e
        rw [show p * (p * (p ^ e * m'')) = p ^ (e + 2) * m'' by ring,
          show p * (p ^ e * m'') = p ^ (e + 1) * m'' by ring]
        rw [div_mul_eq_mul_div, eq_div_iff hc1]
        apply mul_left_cancel₀ hc1
        linear_combination coeff f 1 * e2 + (χ p * (p : ℂ) ^ (k - 1)) * coeff f 1 * e0
          - coeff f p * e1 + coeff f m'' * hr
      · have hcop : p.Coprime m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
        rw [coeff_heckeT_of_coprime hp.ne_zero hcop f]
        have := hmul p m hcop
        rw [div_mul_eq_mul_div, eq_div_iff hc1]
        linear_combination this
    intro n hn
    obtain ⟨t, ht, -⟩ := exists_heckeT_eq_smul_of_forall_prime k χ f {p | p.Prime}
      (fun p hp ↦ hp) (fun p hp ↦ ⟨_, hprime p hp⟩) hn
      (fun p hp ↦ Nat.prime_of_mem_primeFactors hp)
    exact ⟨t, ht⟩

/-- **Miyake, Theorem 4.5.16**, last assertion: if `f ≠ 0` is a common eigenfunction of all
`T(n)`, then `c(1) ≠ 0` and `f ∣ T(n) = (c(n)/c(1)) f` for all `n ≥ 1`. -/
@[kb "miyake1989" "Theorem 4.5.16, p. 149 (eigenvalues)"]
theorem heckeT_eq_coeff_div_smul (k : ℤ) (χ : DirichletCharacter ℂ N) (f : cuspSpace k χ)
    (hf : f ≠ 0) (h : ∀ n : ℕ, n ≠ 0 → ∃ t : ℂ, heckeT k χ n f = t • f) :
    coeff f 1 ≠ 0 ∧ ∀ n : ℕ, n ≠ 0 → heckeT k χ n f = (coeff f n / coeff f 1) • f := by
  have hc1 := coeff_one_ne_zero_of_eigen hf h
  refine ⟨hc1, fun n hn ↦ ?_⟩
  obtain ⟨t, ht⟩ := h n hn
  rw [ht, coeff_eq_of_eigen hn ht, mul_div_cancel_right₀ _ hc1]

end ModularFormsKB.Miyake.Wave4
