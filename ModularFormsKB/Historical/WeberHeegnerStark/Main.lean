import ModularFormsKB.Historical.WeberHeegnerStark.Heegner
import ModularFormsKB.Historical.WeberHeegnerStark.Diophantine
import ModularFormsKB.Historical.WeberHeegnerStark.Numerics
import ModularFormsKB.Historical.WeberHeegnerStark.Forms
import ModularFormsKB.Historical.WeberHeegnerStark.QuadraticField
import Mathlib.Tactic.NormNum.Prime

/-!
# The class number one theorem (Heegner 1952, Stark 1967), conditional on named inputs

**Theorem.** An imaginary quadratic field `K` has class number one if and only if its discriminant is one
of `-3, -4, -7, -8, -11, -19, -43, -67, -163`, that is, `K = ℚ(√-d)` with
`d ∈ {1, 2, 3, 7, 11, 19, 43, 67, 163}` (`D = -d` for `d ≡ 3 mod 4`, `D = -4d` for `d = 1, 2`).

`heegnerStark_classNumber_eq_one_iff` proves this from the structure `WeberHeegnerStarkInputs` (eight classical
theorems of complex multiplication and of the theory of binary quadratic forms, each with its source;
see `Inputs.lean`). Everything else is proved here:
* Gauss's reduction: a fundamental discriminant `D < 0` with `h(D) = 1` is `-3, -4, -7, -8` or `-p` for a
  prime `p ≡ 3 mod 8` (`eq_of_formClassNumber_eq_one`), and the nine discriminants have `h(D) = 1`
  (`formClassNumber_eq_one_of_mem`, by computation);
* Heegner's step for `p ≥ 11` (`exists_heegner_cubic`);
* Heegner's Diophantine equation `y² = 2u(u³ + 1)` (`heegner_gamma_mem`, ported from Tau Ceti);
* the enclosure of `j((-3 + √-p)/2)` that recovers `p` (`mem_of_kleinJ_eq_pow_three`, ported from Tau Ceti).

In the sense of Stark's *On the "gap" in a theorem of Heegner* (1969) [from memory; to check against the
paper]: Heegner's proof is complete modulo Weber's theorems, and here "modulo" is made precise by the list
of fields of `WeberHeegnerStarkInputs`.
-/

open NumberField Module

namespace ModularFormsKB.WeberHeegnerStark

/-- **Heegner's theorem for `p ≡ 3 mod 8`.** Given the named inputs, a prime `p ≡ 3 mod 8` with `p ≥ 11`
and `h(-p) = 1` is one of `11, 19, 43, 67, 163`. -/
theorem mem_of_formClassNumber_eq_one (hin : WeberHeegnerStarkInputs) {p : ℕ} (hp : p.Prime)
    (h8 : p % 8 = 3) (h11 : 11 ≤ p) (h1 : formClassNumber (-p) = 1) :
    p ∈ ({11, 19, 43, 67, 163} : Finset ℕ) := by
  have hsmall := norm_weberF₂_pow_24_lt_one (τ := cmPointS p hp.pos) (by
    rw [cmPointS_im]
    gcongr
    exact_mod_cast h11)
  obtain ⟨g, hjg, a, b, c, h1', hc, hg⟩ := exists_heegner_cubic hin hp h8 h11 h1 hsmall
  have hv := heegner_gamma_mem h1' hc hg
  have hmem := mem_of_kleinJ_eq_pow_three (by omega) (cmPointS_im p hp.pos) (hin.weber_cubic _) hv hjg
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
  omega

/-- **The class number one theorem (Heegner 1952, Stark 1967), conditional on Weber's theorems.**
Let `K` be an imaginary quadratic field. Given the named inputs `WeberHeegnerStarkInputs`, `K` has class
number one if and only if its discriminant is `-3, -4, -7, -8, -11, -19, -43, -67` or `-163`, i.e.
`K = ℚ(√-d)` for `d = 3, 1, 7, 2, 11, 19, 43, 67, 163`. -/
theorem heegnerStark_classNumber_eq_one_iff (hin : WeberHeegnerStarkInputs) (K : Type) [Field K] [NumberField K]
    (hK : finrank ℚ K = 2) (hD : discr K < 0) :
    classNumber K = 1 ↔
      discr K ∈ ({-3, -4, -7, -8, -11, -19, -43, -67, -163} : Finset ℤ) := by
  obtain ⟨hfund, hcl⟩ := hin.imaginaryQuadratic K hK hD
  rw [hcl]
  refine ⟨fun h1 ↦ ?_, formClassNumber_eq_one_of_mem⟩
  rcases eq_of_formClassNumber_eq_one hD hfund h1 with h | ⟨p, hp, h8, hDp⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    omega
  · rw [hDp] at h1 ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases h11 : 11 ≤ p
    · have := mem_of_formClassNumber_eq_one hin hp h8 h11 h1
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
    · omega

/-- **The class number one theorem, in Gauss's form.** Given the named inputs, an imaginary quadratic
field `K` has class number one if and only if `K = ℚ(√-d)` for some
`d ∈ {1, 2, 3, 7, 11, 19, 43, 67, 163}`, i.e. `-d` is a square in `K`. The extra input
`QuadraticDiscriminantInput` (the discriminant of `ℚ(√m)`) translates between `d` and `d_K`. -/
theorem heegnerStark_classNumber_eq_one_iff_isSquare (hin : WeberHeegnerStarkInputs)
    (hq : QuadraticDiscriminantInput) (K : Type) [Field K] [NumberField K]
    (hK : finrank ℚ K = 2) (hD : discr K < 0) :
    classNumber K = 1 ↔
      ∃ d ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ), IsSquare (-(d : K)) := by
  rw [heegnerStark_classNumber_eq_one_iff hin K hK hD]
  constructor
  · intro hmem
    obtain ⟨m, hsf, hm1, hsq⟩ := exists_squarefree_isSquare K hK
    have hdm := hq.discr_eq K hK m hsf hm1 hsq
    rw [hdm] at hmem hD
    have hneg : m ≤ 0 := by split_ifs at hD <;> omega
    obtain ⟨d, rfl⟩ := Int.exists_eq_neg_ofNat hneg
    refine ⟨d, ?_, by simpa using hsq⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    split_ifs at hmem <;> omega
  · rintro ⟨d, hd, hsq⟩
    have hsf : Squarefree (-(d : ℤ)) := by
      rw [← Int.squarefree_natAbs, Int.natAbs_neg, Int.natAbs_natCast]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact squarefree_one
      all_goals exact (Nat.Prime.prime (by norm_num)).squarefree
    have hdK := hq.discr_eq K hK (-(d : ℤ)) hsf (by omega) (by simpa using hsq)
    rw [hdK]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
    split_ifs <;> omega

end ModularFormsKB.WeberHeegnerStark
