import ModularFormsKB.Miyake.Wave4.Newforms
import ModularFormsKB.Miyake.Wave6.OldSpace
import TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.Classification

/-!
# Miyake §4.6: Theorem 4.6.17 (the coefficients `a_q`, `q ∣ N`, of a primitive form)

Miyake, *Modular Forms* (Springer 1989), Theorem 4.6.17, p. 170.

Let `f = Σ a_n e(nz)` be a primitive form of `𝒮_k^0(N, χ)` (wave 4's `IsPrimitive`), `m` the
conductor of `χ`, and for a prime `q ∣ N` let `N_q`, `m_q` be the `q`-components of `N` and `m`.

* (1) If `N_q = m_q`, then `|a_q| = q^{(k-1)/2}` (`norm_coeff_prime_of_factorization_conductor_eq`).
* (2) If `N_q = q` and `m_q = 1`, then `a_q² = χ'_q(q) q^{k-2}`
  (`coeff_prime_sq_of_factorization_eq_one`), where `χ'_q = Π_{p ≠ q} χ_p` is the prime-to-`q`
  part of `χ`; here it is Tau Ceti's `primeToPart q χ`, the prime-to-`q` part of the primitive
  character attached to `χ`, which agrees with Miyake's `χ'_q` at `q`.
* (3) If `q² ∣ N_q` and `N_q ≠ m_q`, then `a_q = 0`
  (`coeff_prime_eq_zero_of_factorization_conductor_lt`; since `m_q ∣ N_q`, `N_q ≠ m_q` is
  `v_q(m) < v_q(N)`).

`N_q = m_q` etc. are written with `Nat.factorization`. The proofs transport Tau Ceti's
classification of the bad-prime eigenvalues of newforms (W.-C. W. Li, *Newforms and functional
equations*, Theorem 3), `HeckeRing.GL2.Newform.norm_qExpansion_coeff_prime_of_factorization_conductor_eq`,
`qExpansion_coeff_prime_sq_of_factorization_eq_one`,
`qExpansion_coeff_prime_eq_zero_of_factorization_conductor_lt`, along wave 4's
`isPrimitive_iff_exists_newform`.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave8

open ModularFormsKB.Miyake.Wave4

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : DirichletCharacter ℂ N}

/-- A primitive form is a Tau Ceti newform whose Dirichlet character is `χ`. -/
theorem exists_newform_of_isPrimitive {f : cuspSpace k χ} (hf : IsPrimitive f) :
    ∃ F : HeckeRing.GL2.Newform N k, F.dirichletLift = χ ∧
      ∀ n, (qExpansion 1 F.toCuspForm).coeff n = coeff f n := by
  obtain ⟨F, hχ, hF⟩ := (isPrimitive_iff_exists_newform f).mp hf
  refine ⟨F, Wave6.toUnitHom_injective ?_, fun n ↦ by rw [hF]⟩
  rw [F.dirichletLift_toUnitHom, hχ]

/-- **Miyake, Theorem 4.6.17 (1)**: if `N_q = m_q`, then `|a_q| = q^{(k-1)/2}`. -/
@[kb "miyake1989" "Theorem 4.6.17 (1), p. 170"]
theorem norm_coeff_prime_of_factorization_conductor_eq {f : cuspSpace k χ} (hf : IsPrimitive f)
    {q : ℕ} (hq : q.Prime) (hqN : q ∣ N)
    (h : χ.conductor.factorization q = N.factorization q) :
    ‖coeff f q‖ = Real.sqrt q ^ (k - 1) := by
  obtain ⟨F, hχ, hF⟩ := exists_newform_of_isPrimitive hf
  rw [← hF]
  exact F.norm_qExpansion_coeff_prime_of_factorization_conductor_eq hq hqN (hχ ▸ h)

/-- **Miyake, Theorem 4.6.17 (2)**: if `N_q = q` and `m_q = 1`, then `a_q² = χ'_q(q) q^{k-2}`. -/
@[kb "miyake1989" "Theorem 4.6.17 (2), p. 170"]
theorem coeff_prime_sq_of_factorization_eq_one {f : cuspSpace k χ} (hf : IsPrimitive f)
    {q : ℕ} (hq : q.Prime) (hN : N.factorization q = 1) (hc : χ.conductor.factorization q = 0) :
    coeff f q ^ 2 = TauCeti.primeToPart q χ q * (q : ℂ) ^ (k - 2) := by
  obtain ⟨F, hχ, hF⟩ := exists_newform_of_isPrimitive hf
  rw [← hF, ← hχ]
  exact F.qExpansion_coeff_prime_sq_of_factorization_eq_one hq hN (hχ ▸ hc)

/-- **Miyake, Theorem 4.6.17 (3)**: if `q² ∣ N_q` and `N_q ≠ m_q`, then `a_q = 0`. -/
@[kb "miyake1989" "Theorem 4.6.17 (3), p. 170"]
theorem coeff_prime_eq_zero_of_factorization_conductor_lt {f : cuspSpace k χ}
    (hf : IsPrimitive f) {q : ℕ} (hq : q.Prime) (hN : 2 ≤ N.factorization q)
    (hc : χ.conductor.factorization q < N.factorization q) :
    coeff f q = 0 := by
  obtain ⟨F, hχ, hF⟩ := exists_newform_of_isPrimitive hf
  rw [← hF]
  exact F.qExpansion_coeff_prime_eq_zero_of_factorization_conductor_lt hq hN (hχ ▸ hc)

end ModularFormsKB.Miyake.Wave8
