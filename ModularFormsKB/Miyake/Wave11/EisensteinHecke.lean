import ModularFormsKB.Miyake.Wave10.WeightTwo
import ModularFormsKB.Miyake.Wave4.HeckeCoefficients
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime.Recurrence

/-!
# Miyake (4.7.16): the Eisenstein spaces `ℰ_k(N, χ)` are stable under `T(n)`, `(n, N) = 1`

Miyake, *Modular Forms* (Springer 1989), §4.7, (4.7.16)–(4.7.17), pp. 178–179.

For primitive Dirichlet characters `χ₁` modulo `M₁`, `χ₂` modulo `M₂` and `l M₁ M₂ ∣ N`, the
generator `f_k(lz; χ₁, χ₂)` of `ℰ_k(N, χ)` (Theorem 4.7.1, (4.7.17)) has Fourier coefficients
`a_{n/l}` (`l ∣ n`), `a_m = Σ_{0 < d ∣ m} χ₁(m/d) χ₂(d) d^{k-1}`. Miyake notes ((4.7.16), from
`L(s; f) = L(s, χ₁) L(s - k + 1, χ₂)` and Theorem 4.5.16) that it is a common eigenfunction of
the `T(n)`, `(n, N) = 1`; hence `ℰ_k(N, χ)` is stable under these operators and spanned by
common eigenfunctions.

## Results (namespace `ModularFormsKB.Miyake.Wave11`)
* `heckeTMod_prime_eq_smul_of_coeff`: for a prime `p ∤ N`, `f | T(p) = (χ₁(p) + χ₂(p) p^{k-1}) f`
  for every `f ∈ 𝒢_k(N, χ)` (`k ≥ 1`) whose coefficients at `n ≥ 1` are those of
  `f_k(lz; χ₁, χ₂)` (here `χ₁`, `χ₂` need not be primitive).
* `heckeTMod_eq_smul_of_coeff` (**(4.7.16)**): for every `n ≥ 1` prime to `N`,
  `f | T(n) = (Σ_{0 < d ∣ n} χ₁(n/d) χ₂(d) d^{k-1}) f`, i.e. the eigenvalue of `T(n)` is the
  `n`-th coefficient of `f_k(z; χ₁, χ₂)`.
* `IsEisensteinGen.heckeTMod_eq_smul`, `IsEisensteinGenTwo.heckeTMod_eq_smul`: the generators of
  (4.7.17) are common eigenfunctions of all `T(n)`, `(n, N) = 1`.
* `heckeTMod_mem_eisensteinSpace`, `heckeTMod_mem_eisensteinSpaceTwo` (**(4.7.16)–(4.7.17)**):
  `ℰ_k(N, χ)` (all `k ≥ 1`; for `k = 2` both `eisensteinSpace 2 χ` and Miyake's
  `ℰ₂(N, χ) = eisensteinSpaceTwo χ`) is stable under `T(n)`, `(n, N) = 1`.
* `mapsTo_heckeTMod_of_prime`: an abstract step, any subspace of `𝒢_k(N, χ)` stable under the
  `T(p)`, `p ∤ N` prime, is stable under all `T(n)`, `(n, N) = 1` (from Tau Ceti's prime-power
  recurrence and multiplicativity).

**Proof.** At a prime `p ∤ N`, Lemma 4.5.14 (`Wave4.coeffMod_heckeTMod`) gives the coefficients of
`f | T(p)` as `a(pn) + χ(p) p^{k-1} a(n/p)`; the twisted divisor sums satisfy
`σ(pm) + χ₁(p) χ₂(p) p^{k-1} σ(m/p) = σ(p) σ(m)` (multiplicativity and the prime-power formula of
Tau Ceti's `DirichletCharacter.twistedDivisorSum`), and a form of weight `k ≠ 0` is determined by
its coefficients at `n ≥ 1`. For composite `n`, the operator `T(n)` lies in the algebra generated
by the `T(p)`, and the eigenvalue is read off at the coefficient of index `l`.

**Not covered:** the first step of Miyake's proof of Theorem 4.7.2 (an eigenform with the
eigenvalues of `f_k(z; χ₁, χ₂)` has no cuspidal component) remains open (the loose end recorded
by wave 10 as LE-MF-0226, whose Hecke-stability part this file settles).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup DirichletCharacter
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave11

open ModularFormsKB.Miyake.Wave4 ModularFormsKB.Miyake.Wave10

/-! ### The twisted divisor sums at `p n` -/

section DivisorSum

variable {R : Type*} [CommRing R]

/-- `T(r) = Σ_{j ≤ r} x^{r-j} y^j` satisfies `T(r+1) = x T(r) + y^{r+1}`. -/
lemma geomSum_succ (x y : R) (r : ℕ) :
    ∑ j ∈ Finset.range (r + 2), x ^ (r + 1 - j) * y ^ j =
      x * ∑ j ∈ Finset.range (r + 1), x ^ (r - j) * y ^ j + y ^ (r + 1) := by
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Nat.sub_add_comm hj, pow_succ]
  ring

/-- The three-term relation of the sums `T(r) = Σ_{j ≤ r} x^{r-j} y^j`. -/
lemma geomSum_rec (x y : R) (r : ℕ) :
    ∑ j ∈ Finset.range (r + 3), x ^ (r + 2 - j) * y ^ j +
        x * y * ∑ j ∈ Finset.range (r + 1), x ^ (r - j) * y ^ j =
      (x + y) * ∑ j ∈ Finset.range (r + 2), x ^ (r + 1 - j) * y ^ j := by
  have h1 : ∑ j ∈ Finset.range (r + 3), x ^ (r + 2 - j) * y ^ j =
      x * ∑ j ∈ Finset.range (r + 2), x ^ (r + 1 - j) * y ^ j + y ^ (r + 2) :=
    geomSum_succ x y (r + 1)
  have h2 := geomSum_succ x y r
  rw [h1, h2]
  ring

lemma twistedDivisorSum_prime_pow_eq {u v : ℕ} (e : ℕ) (ψ : DirichletCharacter R u)
    (φ : DirichletCharacter R v) {p : ℕ} (hp : p.Prime) (r : ℕ) :
    twistedDivisorSum e ψ φ (p ^ r) =
      ∑ j ∈ Finset.range (r + 1), ψ p ^ (r - j) * (φ p * (p : R) ^ e) ^ j := by
  rw [twistedDivisorSum_apply_prime_pow e ψ φ r hp]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mul_pow, ← pow_mul, mul_comm e j, mul_assoc]

/-- **The Hecke relation of the twisted divisor sums at a prime**: for `n ≥ 1`,
`σ(pn) + χ₁(p) χ₂(p) p^e σ(n/p) = (χ₁(p) + χ₂(p) p^e) σ(n)` when `p ∣ n`, and
`σ(pn) = (χ₁(p) + χ₂(p) p^e) σ(n)` when `p ∤ n`. -/
theorem twistedDivisorSum_prime_mul {u v : ℕ} (e : ℕ) (ψ : DirichletCharacter R u)
    (φ : DirichletCharacter R v) {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
    twistedDivisorSum e ψ φ (p * n) +
        (if p ∣ n then ψ p * φ p * (p : R) ^ e * twistedDivisorSum e ψ φ (n / p) else 0) =
      (ψ p + φ p * (p : R) ^ e) * twistedDivisorSum e ψ φ n := by
  have hmul := isMultiplicative_twistedDivisorSum e ψ φ
  obtain ⟨a, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hcop : ∀ r, Nat.Coprime (p ^ r) m := fun r ↦
    Nat.Coprime.pow_left r ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  have hprime := twistedDivisorSum_apply_prime e ψ φ hp
  rw [← mul_assoc, ← pow_succ', hmul.map_mul_of_coprime (hcop _),
    hmul.map_mul_of_coprime (hcop _)]
  rcases a with _ | b
  · have : ¬ p ∣ p ^ 0 * m := by simpa using hpm
    rw [if_neg this, add_zero, pow_one, pow_zero, twistedDivisorSum_one, one_mul, hprime]
  · have hdvd : p ∣ p ^ (b + 1) * m := Dvd.dvd.mul_right (dvd_pow_self p b.succ_ne_zero) m
    rw [if_pos hdvd, show p ^ (b + 1) * m / p = p ^ b * m by
      rw [pow_succ', mul_assoc, Nat.mul_div_cancel_left _ hp.pos],
      hmul.map_mul_of_coprime (hcop _)]
    rw [twistedDivisorSum_prime_pow_eq e ψ φ hp, twistedDivisorSum_prime_pow_eq e ψ φ hp,
      twistedDivisorSum_prime_pow_eq e ψ φ hp]
    have := geomSum_rec (ψ p) (φ p * (p : R) ^ e) b
    rw [show b + 1 + 1 = b + 2 by ring]
    linear_combination twistedDivisorSum e ψ φ m * this

end DivisorSum

/-! ### The eigenvalue of `T(p)` -/

variable {N : ℕ} [NeZero N]

/-- Weight `k ≥ 1`: modular forms in `𝒢_k(N, χ)` with equal coefficients at `n ≥ 1` are equal. -/
lemma eq_of_coeffMod_eq {k : ℕ} (hk : 1 ≤ k) {χ : DirichletCharacter ℂ N}
    {f g : modSpace (k : ℤ) χ} (h : ∀ n : ℕ, 0 < n → coeffMod f n = coeffMod g n) : f = g :=
  Subtype.ext <| TauCeti.ModularForm.eq_of_forall_pos_qExpansion_coeff_eq one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map N) (by omega) h

lemma coeffMod_smul' {k : ℤ} {χ : DirichletCharacter ℂ N} (c : ℂ) (f : modSpace k χ) (n : ℕ) :
    coeffMod (c • f) n = c * coeffMod f n := by
  change (qExpansion 1 (c • (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k))).coeff n = _
  rw [ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N)]
  simp only [map_smul, smul_eq_mul]

/-- For `p ∤ N` and `M ∣ N`, the value of a character modulo `M` raised to level `N` at `p` is the
value of the character itself. -/
lemma changeLevel_apply_of_coprime {M : ℕ} (ψ : DirichletCharacter ℂ M) (h : M ∣ N) {p : ℕ}
    (hp : p.Coprime N) : ψ.changeLevel h p = ψ p := by
  have := changeLevel_eq_cast_of_dvd' (χ := ψ) h (a := (p : ℤ)) (Nat.isCoprime_iff_coprime.2 hp)
  simpa using this

/-- The `k`-th power convention: for `k ≥ 1`, `(d : ℂ) ^ ((k : ℤ) - 1) = d ^ (k - 1)`. -/
lemma zpow_natCast_sub_one {k : ℕ} (hk : 1 ≤ k) (x : ℂ) : x ^ ((k : ℤ) - 1) = x ^ (k - 1) := by
  rw [show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) by omega, zpow_natCast]

/-- **The eigenvalue of `T(p)` on `f_k(lz; χ₁, χ₂)`** (Miyake (4.7.16), at a prime): if
`f ∈ 𝒢_k(N, χ)`, `k ≥ 1`, has the coefficients of `f_k(lz; χ₁, χ₂)` at `n ≥ 1`, with
`l M₁ M₂ ∣ N` and `χ₁ χ₂ = χ`, then `f | T(p) = (χ₁(p) + χ₂(p) p^{k-1}) f` for every prime `p ∤ N`. -/
@[kb "miyake1989" "(4.7.16), p. 178 (T(p), p prime to N)"]
theorem heckeTMod_prime_eq_smul_of_coeff {k : ℕ} (hk : 1 ≤ k) {χ : DirichletCharacter ℂ N}
    {l M₁ M₂ : ℕ} {χ₁ : DirichletCharacter ℂ M₁} {χ₂ : DirichletCharacter ℂ M₂}
    (h : l * (M₁ * M₂) ∣ N)
    (hprod : χ₁.changeLevel (dvd_left_of_level h) * χ₂.changeLevel (dvd_right_of_level h) = χ)
    {f : modSpace (k : ℤ) χ} (hf : ∀ n : ℕ, 0 < n → coeffMod f n = eisCoeff k χ₁ χ₂ l n)
    {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) :
    heckeTMod (k : ℤ) χ p f = (χ₁ p + χ₂ p * (p : ℂ) ^ (k - 1)) • f := by
  have hpN' : p.Coprime N := (Nat.Prime.coprime_iff_not_dvd hp).2 hpN
  have hχp : χ p = χ₁ p * χ₂ p := by
    rw [← hprod, MulChar.mul_apply, changeLevel_apply_of_coprime _ _ hpN',
      changeLevel_apply_of_coprime _ _ hpN']
  have hl : ¬ p ∣ l := fun hpl ↦ hpN (hpl.trans ((dvd_mul_right l _).trans h))
  refine eq_of_coeffMod_eq hk fun n hn ↦ ?_
  rw [coeffMod_heckeTMod (k : ℤ) χ hp.ne_zero f hn.ne', coeffMod_smul']
  by_cases hpn : p ∣ n
  · -- `gcd(p, n) = p`: two terms.
    have hg : Nat.gcd p n = p := Nat.gcd_eq_left hpn
    rw [hg, Nat.Prime.sum_divisors hp]
    simp only [Nat.cast_one, MulChar.map_one, one_zpow, one_mul, one_pow, Nat.div_one]
    rw [show p * n / p ^ 2 = n / p by
      rw [sq, Nat.mul_div_mul_left _ _ hp.pos]]
    rw [hf _ (Nat.mul_pos hp.pos hn), hf _ (Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos),
      hf _ hn, eisCoeff_eq_twistedDivisorSum, eisCoeff_eq_twistedDivisorSum,
      eisCoeff_eq_twistedDivisorSum]
    have hlpn : l ∣ p * n ↔ l ∣ n :=
      ⟨fun h' ↦ ((Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hl)).dvd_of_dvd_mul_left h'),
        fun h' ↦ h'.mul_left p⟩
    have hlp : Nat.Coprime l p := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hl)
    have hlnp : l ∣ n / p ↔ l ∣ n := by
      conv_rhs => rw [← Nat.mul_div_cancel' hpn]
      exact ⟨fun h' ↦ h'.mul_left p, fun h' ↦ hlp.dvd_of_dvd_mul_left h'⟩
    by_cases hln : l ∣ n
    · rw [if_pos (hlpn.2 hln), if_pos (hlnp.2 hln), if_pos hln]
      obtain ⟨m, rfl⟩ := hln
      have hl0 : 0 < l := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hn
      have hm0 : m ≠ 0 := fun h0 ↦ by simp [h0] at hn
      have hpm : p ∣ m :=
        ((Nat.Prime.coprime_iff_not_dvd hp).2 hl).dvd_of_dvd_mul_left hpn
      rw [show p * (l * m) / l = p * m by
          rw [mul_left_comm, Nat.mul_div_cancel_left _ hl0],
        show l * m / p / l = m / p by
          obtain ⟨c, rfl⟩ := hpm
          rw [mul_left_comm, Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel_left _ hp.pos,
            Nat.mul_div_cancel_left _ hl0],
        Nat.mul_div_cancel_left _ hl0]
      have key := twistedDivisorSum_prime_mul (k - 1) χ₁ χ₂ hp hm0
      rw [if_pos hpm] at key
      rw [hχp, zpow_natCast_sub_one hk, ← key]
      ring
    · rw [if_neg (mt hlpn.1 hln), if_neg (mt hlnp.1 hln), if_neg hln]
      ring
  · -- `gcd(p, n) = 1`: one term.
    have hg : Nat.gcd p n = 1 :=
      (Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn))
    rw [hg, Nat.divisors_one, Finset.sum_singleton]
    simp only [Nat.cast_one, MulChar.map_one, one_zpow, one_mul, one_pow, Nat.div_one]
    rw [hf _ (Nat.mul_pos hp.pos hn), hf _ hn, eisCoeff_eq_twistedDivisorSum,
      eisCoeff_eq_twistedDivisorSum]
    have hlpn : l ∣ p * n ↔ l ∣ n :=
      ⟨fun h' ↦ ((Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hl)).dvd_of_dvd_mul_left h'),
        fun h' ↦ h'.mul_left p⟩
    by_cases hln : l ∣ n
    · rw [if_pos (hlpn.2 hln), if_pos hln]
      obtain ⟨m, rfl⟩ := hln
      have hl0 : 0 < l := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hn
      have hm0 : m ≠ 0 := fun h0 ↦ by simp [h0] at hn
      have hpm : ¬ p ∣ m := fun h' ↦ hpn (h'.mul_left l)
      rw [show p * (l * m) / l = p * m by
          rw [mul_left_comm, Nat.mul_div_cancel_left _ hl0],
        Nat.mul_div_cancel_left _ hl0]
      have key := twistedDivisorSum_prime_mul (k - 1) χ₁ χ₂ hp hm0
      rw [if_neg hpm, add_zero] at key
      rw [key]
    · rw [if_neg (mt hlpn.1 hln), if_neg hln, mul_zero]

/-! ### From primes to all `n` prime to `N` -/

/-- The prime-power operators `T(p^v)`, `p ∤ N`, preserve every subspace preserved by `T(p)`. -/
lemma mapsTo_heckeTGeneratorRec {k : ℤ} {χ : DirichletCharacter ℂ N}
    (W : Submodule ℂ (modSpace k χ)) {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N)
    (hW : ∀ f ∈ W, heckeTMod k χ p f ∈ W) (v : ℕ) :
    ∀ f ∈ W, HeckeRing.GL2.heckeRingHomCharSpace k χ.toUnitHom
      (HeckeRing.GL2.heckeTGeneratorRecGamma0 N p v) f ∈ W := by
  have hgen : ∀ f ∈ W, HeckeRing.GL2.heckeRingHomCharSpace k χ.toUnitHom
      (HeckeRing.GL2.heckeTGeneratorGamma0 N p) f ∈ W := by
    intro f hf
    have := hW f hf
    rwa [heckeTMod, HeckeRing.GL2.heckeTCompositeGamma0_prime N hp] at this
  have key : ∀ v, (∀ f ∈ W, HeckeRing.GL2.heckeRingHomCharSpace k χ.toUnitHom
      (HeckeRing.GL2.heckeTGeneratorRecGamma0 N p v) f ∈ W) ∧
      (∀ f ∈ W, HeckeRing.GL2.heckeRingHomCharSpace k χ.toUnitHom
      (HeckeRing.GL2.heckeTGeneratorRecGamma0 N p (v + 1)) f ∈ W) := by
    intro v
    induction v with
    | zero =>
      refine ⟨fun f hf ↦ ?_, fun f hf ↦ ?_⟩
      · rw [HeckeRing.GL2.heckeTGeneratorRecGamma0_zero, map_one]
        exact hf
      · rw [HeckeRing.GL2.heckeTGeneratorRecGamma0_one]
        exact hgen f hf
    | succ r ih =>
      refine ⟨ih.2, fun f hf ↦ ?_⟩
      rw [HeckeRing.GL2.heckeRingHomCharSpace_heckeTGeneratorRecGamma0_succ_succ_apply k
        χ.toUnitHom hpN f r]
      exact W.sub_mem (hgen _ (ih.2 f hf)) (W.smul_mem _ (ih.1 f hf))
  exact (key v).1

/-- **From `T(p)` to `T(n)`**: a subspace of `𝒢_k(N, χ)` stable under `T(p)` for every prime
`p ∤ N` is stable under `T(n)` for every `n` prime to `N`. -/
theorem mapsTo_heckeTMod_of_prime {k : ℤ} {χ : DirichletCharacter ℂ N}
    (W : Submodule ℂ (modSpace k χ))
    (hW : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ f ∈ W, heckeTMod k χ p f ∈ W) (n : ℕ)
    (hn : n.Coprime N) : ∀ f ∈ W, heckeTMod k χ n f ∈ W := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf
    rcases lt_or_ge 1 n with h1 | h1
    · have hp := Nat.minFac_prime (show n ≠ 1 by omega)
      have hpn : n.minFac ∣ n := Nat.minFac_dvd n
      have hpN : n.minFac.Coprime N := Nat.Coprime.coprime_dvd_left hpn hn
      set v := n.factorization n.minFac
      have hlt : n / n.minFac ^ v < n := by
        refine Nat.div_lt_self (by omega) (Nat.one_lt_pow ?_ hp.one_lt)
        exact (Nat.Prime.factorization_pos_of_dvd hp (by omega) hpn).ne'
      have hcop : (n / n.minFac ^ v).Coprime N :=
        Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.ordProj_dvd n _)) hn
      rw [heckeTMod, HeckeRing.GL2.heckeTCompositeGamma0_of_one_lt N h1, map_mul,
        Module.End.mul_apply]
      refine mapsTo_heckeTGeneratorRec W hp hpN
        (hW _ hp ((Nat.Prime.coprime_iff_not_dvd hp).1 hpN)) _ _ ?_
      exact ih _ hlt hcop f hf
    · interval_cases n
      · rw [heckeTMod, HeckeRing.GL2.heckeTCompositeGamma0_zero, map_one]
        exact hf
      · rw [heckeTMod, HeckeRing.GL2.heckeTCompositeGamma0_one, map_one]
        exact hf

/-- **Miyake (4.7.16)**: `f_k(lz; χ₁, χ₂)` is a common eigenfunction of the `T(n)`, `(n, N) = 1`,
with eigenvalue the `n`-th coefficient `Σ_{0 < d ∣ n} χ₁(n/d) χ₂(d) d^{k-1}` of
`f_k(z; χ₁, χ₂)`: if `f ∈ 𝒢_k(N, χ)`, `k ≥ 1`, has the coefficients of `f_k(lz; χ₁, χ₂)` at
`n ≥ 1`, with `l M₁ M₂ ∣ N` and `χ₁ χ₂ = χ`, then
`f | T(n) = (Σ_{0 < d ∣ n} χ₁(n/d) χ₂(d) d^{k-1}) f`. -/
@[kb "miyake1989" "(4.7.16), p. 178"]
theorem heckeTMod_eq_smul_of_coeff {k : ℕ} (hk : 1 ≤ k) {χ : DirichletCharacter ℂ N}
    {l M₁ M₂ : ℕ} {χ₁ : DirichletCharacter ℂ M₁} {χ₂ : DirichletCharacter ℂ M₂}
    (h : l * (M₁ * M₂) ∣ N)
    (hprod : χ₁.changeLevel (dvd_left_of_level h) * χ₂.changeLevel (dvd_right_of_level h) = χ)
    {f : modSpace (k : ℤ) χ} (hf : ∀ n : ℕ, 0 < n → coeffMod f n = eisCoeff k χ₁ χ₂ l n)
    {n : ℕ} (hn0 : 0 < n) (hn : n.Coprime N) :
    heckeTMod (k : ℤ) χ n f =
      (∑ d ∈ n.divisors, χ₁ (n / d : ℕ) * χ₂ d * (d : ℂ) ^ (k - 1)) • f := by
  have hspan := mapsTo_heckeTMod_of_prime (ℂ ∙ f) (fun p hp hpN g hg ↦ by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hg
    rw [map_smul, heckeTMod_prime_eq_smul_of_coeff hk h hprod hf hp hpN, smul_smul]
    exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩) n hn f (Submodule.mem_span_singleton_self f)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hspan
  rw [← hc]
  congr 1
  -- Read off the eigenvalue at the coefficient of index `l`.
  have hl0 : 0 < l := Nat.pos_of_dvd_of_pos ((dvd_mul_right l _).trans h) (NeZero.pos N)
  have hnl : n.gcd l = 1 :=
    Nat.Coprime.coprime_dvd_right ((dvd_mul_right l _).trans h) hn
  have hcoeff : coeffMod (c • f) l = coeffMod (heckeTMod (k : ℤ) χ n f) l := by rw [hc]
  rw [coeffMod_heckeTMod (k : ℤ) χ hn0.ne' f hl0.ne', hnl, Nat.divisors_one,
    Finset.sum_singleton, coeffMod_smul'] at hcoeff
  simp only [Nat.cast_one, MulChar.map_one, one_zpow, one_mul, one_pow, Nat.div_one] at hcoeff
  rw [hf _ hl0, hf _ (Nat.mul_pos hn0 hl0)] at hcoeff
  rw [eisCoeff_eq_twistedDivisorSum, eisCoeff_eq_twistedDivisorSum, if_pos (dvd_mul_left l n),
    if_pos dvd_rfl, Nat.mul_div_cancel _ hl0, Nat.div_self hl0, twistedDivisorSum_one,
    mul_one] at hcoeff
  rw [hcoeff, twistedDivisorSum_apply]

/-- The generators `f_k(lz; χ₁, χ₂)` of (4.7.17) (`k ≠ 2`, and the case (ii) generators for
`k = 2`) are common eigenfunctions of the `T(n)`, `(n, N) = 1` (Miyake (4.7.16)). -/
@[kb "miyake1989" "(4.7.16), p. 178"]
theorem IsEisensteinGen.heckeTMod_eq_smul {k : ℕ} (hk : 1 ≤ k) {χ : DirichletCharacter ℂ N}
    {g : modSpace (k : ℤ) χ} (hg : IsEisensteinGen k χ g) {n : ℕ} (hn0 : 0 < n)
    (hn : n.Coprime N) : ∃ c : ℂ, heckeTMod (k : ℤ) χ n g = c • g := by
  obtain ⟨l, M₁, M₂, χ₁, χ₂, h, -, -, hprod, hcoeff⟩ := hg
  exact ⟨_, heckeTMod_eq_smul_of_coeff hk h hprod hcoeff hn0 hn⟩

/-- The generators `f₂(lz; χ₁, χ₂)` of Miyake's `ℰ₂(N, χ)` (both cases of (4.7.2)) are common
eigenfunctions of the `T(n)`, `(n, N) = 1` (Miyake (4.7.16)). -/
@[kb "miyake1989" "(4.7.16), p. 178 (k = 2)"]
theorem IsEisensteinGenTwo.heckeTMod_eq_smul {χ : DirichletCharacter ℂ N} {g : modSpace 2 χ}
    (hg : IsEisensteinGenTwo χ g) {n : ℕ} (hn0 : 0 < n) (hn : n.Coprime N) :
    ∃ c : ℂ, heckeTMod 2 χ n g = c • g := by
  obtain ⟨l, M₁, M₂, χ₁, χ₂, h, -, hprod, hcoeff⟩ := hg
  exact ⟨_, heckeTMod_eq_smul_of_coeff (k := 2) (by norm_num) h hprod hcoeff hn0 hn⟩

/-- A span of common eigenvectors of an operator is stable under it. -/
lemma span_mapsTo_of_eigen {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M)
    (S : Set M) (hS : ∀ g ∈ S, ∃ c : ℂ, T g = c • g) {f : M} (hf : f ∈ Submodule.span ℂ S) :
    T f ∈ Submodule.span ℂ S := by
  have hle : Submodule.span ℂ S ≤ (Submodule.span ℂ S).comap T :=
    Submodule.span_le.2 fun g hg ↦ by
      obtain ⟨c, hc⟩ := hS g hg
      rw [SetLike.mem_coe, Submodule.mem_comap, hc]
      exact Submodule.smul_mem _ c (Submodule.subset_span hg)
  exact hle hf

/-- **Miyake (4.7.16)–(4.7.17)**: `ℰ_k(N, χ)` is stable under `T(n)` for every `n` prime to `N`
(`k ≥ 1`). -/
@[kb "miyake1989" "(4.7.16)-(4.7.17), p. 179 (Hecke stability)"]
theorem heckeTMod_mem_eisensteinSpace {k : ℕ} (hk : 1 ≤ k) {χ : DirichletCharacter ℂ N}
    {n : ℕ} (hn : n.Coprime N) {f : modSpace (k : ℤ) χ} (hf : f ∈ eisensteinSpace k χ) :
    heckeTMod (k : ℤ) χ n f ∈ eisensteinSpace k χ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rwa [heckeTMod, HeckeRing.GL2.heckeTCompositeGamma0_zero, map_one]
  exact span_mapsTo_of_eigen _ _ (fun g hg ↦ IsEisensteinGen.heckeTMod_eq_smul hk hg hn0 hn) hf

/-- **Miyake (4.7.16)–(4.7.17)** in weight two: `ℰ₂(N, χ)` is stable under `T(n)`, `(n, N) = 1`. -/
@[kb "miyake1989" "(4.7.16)-(4.7.17), p. 179 (Hecke stability, k = 2)"]
theorem heckeTMod_mem_eisensteinSpaceTwo {χ : DirichletCharacter ℂ N} {n : ℕ}
    (hn : n.Coprime N) {f : modSpace 2 χ} (hf : f ∈ eisensteinSpaceTwo χ) :
    heckeTMod 2 χ n f ∈ eisensteinSpaceTwo χ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rwa [heckeTMod, HeckeRing.GL2.heckeTCompositeGamma0_zero, map_one]
  exact span_mapsTo_of_eigen _ _ (fun g hg ↦ IsEisensteinGenTwo.heckeTMod_eq_smul hg hn0 hn) hf

end ModularFormsKB.Miyake.Wave11
