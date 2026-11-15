import ModularFormsKB.Miyake.Wave13.HeckeConstantTerm
import ModularFormsKB.Miyake.Wave6.LevelChange

/-!
# Miyake Theorem 4.5.10 and Lemma 4.6.2 on modular forms, every weight

Miyake, *Modular Forms* (Springer 1989), Theorem 4.5.10 (p. 143) and Lemma 4.6.2 (p. 154), on
`𝒢_k(N, χ)`. Wave 6 proved both for weight `k ≠ 0` (`Wave6.heckeTMod_embedMod`,
`Wave6.heckeTMod_raiseMod`), because the coefficient formula of `T(n)` available then covered the
indices `n ≥ 1` only and the constant term was recovered from the vanishing of constant forms of
nonzero weight (LE-MF-0199). With the constant term of Lemma 4.5.14 (`coeffMod_heckeTMod_all`,
this wave) the same proofs run through the uniqueness of the full `q`-expansion, with no
restriction on `k`:

* `heckeTMod_embedMod_all` (Theorem 4.5.10, modular forms, `T(n)`);
* `heckeTMod_raiseMod_all` (Lemma 4.6.2, modular forms).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave13

open Wave4 Wave6

variable {N M : ℕ} [NeZero N] [NeZero M]

omit [NeZero N] in
/-- An element of `𝒢_k(N, χ)` is determined by its Fourier coefficients (every weight). -/
lemma ext_of_coeffMod_all {k : ℤ} {χ : DirichletCharacter ℂ N} {f g : modSpace k χ}
    (h : ∀ n, coeffMod f n = coeffMod g n) : f = g :=
  Subtype.ext (ModularForm.qExpansion_injective one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map N) (PowerSeries.ext h))

/-- **Miyake, Theorem 4.5.10** (modular forms, `T(n)`), every weight: let `M` be a multiple of
`N` and `n` a positive integer with `n ∣ N^∞` or `(n, M) = 1`. Then the natural embedding
`𝒢_k(N, χ) → 𝒢_k(M, χ)` commutes with `T(n)`. -/
@[kb "miyake1989" "Theorem 4.5.10, p. 143 (T(n), modular forms)"]
theorem heckeTMod_embedMod_all (k : ℤ) (χ : DirichletCharacter ℂ N) (h : N ∣ M)
    {n : ℕ} (hn0 : n ≠ 0) (hn : (∀ p : ℕ, p.Prime → p ∣ n → p ∣ N) ∨ n.Coprime M)
    (f : modSpace k χ) :
    heckeTMod k (DirichletCharacter.changeLevel h χ) n (embedMod k χ h f) =
      embedMod k χ h (heckeTMod k χ n f) := by
  refine ext_of_coeffMod_all fun m ↦ ?_
  rw [coeffMod_heckeTMod_all k _ hn0, coeffMod_embedMod, coeffMod_heckeTMod_all k χ hn0 f]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [coeffMod_embedMod, changeLevel_apply_of_dvd h χ hn
    ((Nat.dvd_of_mem_divisors hd).trans (Nat.gcd_dvd_left n m))]

/-- **Miyake, Lemma 4.6.2** (modular forms), every weight: for a positive integer `l` and
`(n, lN) = 1`, the map `f(z) ↦ f(lz)` from `𝒢_k(N, χ)` to `𝒢_k(lN, χ)` commutes with `T(n)`. -/
@[kb "miyake1989" "Lemma 4.6.2, p. 154 (modular forms)"]
theorem heckeTMod_raiseMod_all (k : ℤ) (χ : DirichletCharacter ℂ N) (l : ℕ) [NeZero l]
    {n : ℕ} (hn0 : n ≠ 0) (hn : n.Coprime (l * N)) (f : modSpace k χ) :
    heckeTMod k _ n (raiseMod k χ l f) = raiseMod k χ l (heckeTMod k χ n f) := by
  have hnl : n.Coprime l := hn.coprime_dvd_right (Dvd.intro _ rfl)
  have hlpos : 0 < l := Nat.pos_of_ne_zero (NeZero.ne l)
  refine ext_of_coeffMod_all fun m ↦ ?_
  rw [coeffMod_heckeTMod_all k _ hn0, coeffMod_raiseMod]
  by_cases hl : l ∣ m
  · rw [ite_eq_left hl]
    obtain ⟨j, rfl⟩ := hl
    rw [Nat.mul_div_cancel_left _ hlpos, coeffMod_heckeTMod_all k χ hn0 f,
      Nat.Coprime.gcd_mul_left_cancel_right j hnl.symm]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    have hdg := Nat.dvd_of_mem_divisors hd
    have hdn : d ∣ n := hdg.trans (Nat.gcd_dvd_left n j)
    have hdj : d ∣ j := hdg.trans (Nat.gcd_dvd_right n j)
    have hd2 : d ^ 2 ∣ n * j := by rw [pow_two]; exact mul_dvd_mul hdn hdj
    have e : n * (l * j) / d ^ 2 = l * (n * j / d ^ 2) := by
      rw [show n * (l * j) = l * (n * j) by ring, Nat.mul_div_assoc _ hd2]
    rw [coeffMod_raiseMod, e, ite_eq_left (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hlpos,
      changeLevel_apply_of_dvd (Dvd.intro_left l rfl) χ (Or.inr hn) hdn]
  · rw [ite_eq_right hl]
    refine Finset.sum_eq_zero fun d hd ↦ ?_
    have hdg := Nat.dvd_of_mem_divisors hd
    have hdn : d ∣ n := hdg.trans (Nat.gcd_dvd_left n m)
    have hdm : d ∣ m := hdg.trans (Nat.gcd_dvd_right n m)
    have hd2 : d ^ 2 ∣ n * m := by rw [pow_two]; exact mul_dvd_mul hdn hdm
    rw [coeffMod_raiseMod, ite_eq_right, mul_zero]
    intro h1
    exact hl (hnl.symm.dvd_of_dvd_mul_left ((h1.trans (Nat.div_dvd_of_dvd hd2))))

end ModularFormsKB.Miyake.Wave13
