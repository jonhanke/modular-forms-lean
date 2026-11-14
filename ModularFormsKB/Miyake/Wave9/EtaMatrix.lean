import TauCeti.NumberTheory.ModularForms.AtkinLehner.Matrix
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import ModularFormsKB.Citation
/-!
# Miyake §4.6: the matrices `η_q`, `η'_q` of (4.6.19)–(4.6.21)

Miyake, *Modular Forms* (Springer 1989), (4.6.19)–(4.6.21), pp. 166–167.

For a prime `q ∣ N` with `q`-component `N_q`, Miyake takes `γ_q, γ'_q ∈ SL₂(ℤ)` with

* `γ_q ≡ [0 -1; 1 0] mod N_q²`, `γ_q ≡ 1 mod (N/N_q)²`,
* `γ'_q ≡ 1 mod N_q²`, `γ'_q ≡ [0 -1; 1 0] mod (N/N_q)²`,

and puts `η_q = γ_q [N_q 0; 0 1]`, `η'_q = γ'_q [N/N_q 0; 0 1]`.

Both are instances of one shape, for an exact divisor `Q` of `N` (`Q ∥ N`): `M = γ [Q 0; 0 1]`
with `γ ≡ [0 -1; 1 0] mod Q²` and `γ ≡ 1 mod (N/Q)²` (`IsEtaMatrix N Q M`). Miyake's `η_q` is the
case `Q = N_q` and `η'_q` the case `Q = N/N_q` (then `N/Q = N_q`).

## Results
* `exists_isEtaMatrix`: such matrices exist (strong approximation for `SL₂`, Tau Ceti's
  `Matrix.SpecialLinearGroup.map_intCast_zmod_surjective`). Miyake takes this for granted.
* `IsEtaMatrix.isAtkinLehnerMatrix`: `M` is an Atkin–Lehner matrix for `Q` in Tau Ceti's sense
  (`!![Q a, b; N c, Q d]` of determinant `Q`), and `IsEtaMatrix.intCast_apply_one_one`: its
  lower-right entry is `1` modulo `N/Q` (Atkin–Li's normalization), as Miyake's congruences
  `η_q ≡ [0 -1; N_q 0] mod N_q²`, `η_q ≡ [N_q 0; 0 1] mod (N/N_q)²` say.
* `IsEtaMatrix.exists_mul_eq_fricke`: the matrix step of the proof of Theorem 4.6.16 (3):
  `η_q η'_q = γ ω_N` with `γ ∈ Γ₀(N)`, `γ ≡ 1 mod N_q` and `γ ≡ [N_q 0; 0 1/N_q] mod N/N_q`; here
  read on the lower-right entry `d` of `γ`: `d ≡ 1 mod Q` and `Q d ≡ 1 mod N/Q`.
-/

open Matrix CongruenceSubgroup
open scoped MatrixGroups TauCeti.ExactDivisor

namespace ModularFormsKB.Miyake.Wave9

/-- Miyake's matrix `[0 -1; 1 0]`. -/
abbrev S2 : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]

/-- **Miyake's `η_q`, `η'_q`** ((4.6.19)–(4.6.21), pp. 166–167), for an exact divisor `Q` of `N`:
`M = γ [Q 0; 0 1]` with `γ ∈ SL₂(ℤ)`, `γ ≡ [0 -1; 1 0] mod Q²`, `γ ≡ 1 mod (N/Q)²`. Miyake's `η_q`
is the case `Q = N_q`, his `η'_q` the case `Q = N/N_q`. -/
def IsEtaMatrix (N Q : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  ∃ γ : SL(2, ℤ),
    (∀ i j, (((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod (Q ^ 2)) = (S2 i j : ZMod (Q ^ 2))) ∧
    (∀ i j, (((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod ((N / Q) ^ 2)) =
      ((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ZMod ((N / Q) ^ 2))) ∧
    M = (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(Q : ℤ), 0; 0, 1]

variable {N Q : ℕ} {M M' : Matrix (Fin 2) (Fin 2) ℤ}

private lemma dvd_of_cast_eq {n : ℕ} {x y : ℤ} (h : ((x : ℤ) : ZMod n) = ((y : ℤ) : ZMod n)) :
    (n : ℤ) ∣ x - y :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub y x n).mp h.symm

private lemma cast_eq_one_of_dvd {n : ℕ} {x : ℤ} (h : (n : ℤ) ∣ x - 1) :
    ((x : ℤ) : ZMod n) = 1 := by
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 x n).mpr h
  simpa using this.symm

private lemma dvd_of_sq_dvd {n : ℕ} {x : ℤ} (h : ((n ^ 2 : ℕ) : ℤ) ∣ x) : (n : ℤ) ∣ x :=
  (Dvd.intro_left _ (by push_cast; ring) : (n : ℤ) ∣ ((n ^ 2 : ℕ) : ℤ)).trans h

/-- Entries of an `η`-matrix, as divisibilities. -/
theorem IsEtaMatrix.exists_entries (hM : IsEtaMatrix N Q M) :
    ∃ γ : SL(2, ℤ), M = (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(Q : ℤ), 0; 0, 1] ∧
      ((Q ^ 2 : ℕ) : ℤ) ∣ γ 0 0 ∧ ((Q ^ 2 : ℕ) : ℤ) ∣ γ 0 1 + 1 ∧
      ((Q ^ 2 : ℕ) : ℤ) ∣ γ 1 0 - 1 ∧ ((Q ^ 2 : ℕ) : ℤ) ∣ γ 1 1 ∧
      (((N / Q) ^ 2 : ℕ) : ℤ) ∣ γ 0 0 - 1 ∧ (((N / Q) ^ 2 : ℕ) : ℤ) ∣ γ 0 1 ∧
      (((N / Q) ^ 2 : ℕ) : ℤ) ∣ γ 1 0 ∧ (((N / Q) ^ 2 : ℕ) : ℤ) ∣ γ 1 1 - 1 := by
  obtain ⟨γ, h1, h2, rfl⟩ := hM
  refine ⟨γ, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using dvd_of_cast_eq (h1 0 0)
  · simpa using dvd_of_cast_eq (h1 0 1)
  · simpa using dvd_of_cast_eq (h1 1 0)
  · simpa using dvd_of_cast_eq (h1 1 1)
  · simpa using dvd_of_cast_eq (h2 0 0)
  · simpa using dvd_of_cast_eq (h2 0 1)
  · simpa using dvd_of_cast_eq (h2 1 0)
  · simpa using dvd_of_cast_eq (h2 1 1)

/-- **Miyake's `η_q` is an Atkin–Lehner matrix** for `Q` (p. 167:
`η_q ≡ [0 -1; N_q 0] mod N_q²`, `η_q ≡ [N_q 0; 0 1] mod (N/N_q)²`). -/
@[kb "miyake1989" "(4.6.21), p. 167"]
theorem IsEtaMatrix.isAtkinLehnerMatrix (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M) :
    TauCeti.IsAtkinLehnerMatrix N Q M := by
  obtain ⟨γ, rfl, -, -, -, h11, -, -, h10, -⟩ := hM.exists_entries
  have hN : (N : ℤ) = (Q : ℤ) * ((N / Q : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mul_div_cancel' hQ.dvd).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      mul_zero, add_zero]
    rw [hN, mul_comm (γ 1 0)]
    exact mul_dvd_mul_left _ (dvd_of_sq_dvd h10)
  · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      mul_zero, zero_add, mul_one]
    exact dvd_of_sq_dvd h11
  · rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, Matrix.det_fin_two_of]
    ring

/-- **The lower-right entry of `η_q` is `1` modulo `N / Q`** (Atkin–Li's normalization). -/
theorem IsEtaMatrix.intCast_apply_one_one (hM : IsEtaMatrix N Q M) :
    ((M 1 1 : ℤ) : ZMod (N / Q)) = 1 := by
  obtain ⟨γ, rfl, -, -, -, -, -, -, -, h11⟩ := hM.exists_entries
  have h := dvd_of_sq_dvd h11
  have : ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(Q : ℤ), 0; 0, 1]) 1 1 = γ 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [this]
  exact cast_eq_one_of_dvd h

private lemma entry_mul_diag (γ : Matrix (Fin 2) (Fin 2) ℤ) (Q : ℤ) (i : Fin 2) :
    (γ * !![Q, 0; 0, 1]) i 0 = γ i 0 * Q ∧ (γ * !![Q, 0; 0, 1]) i 1 = γ i 1 := by
  constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **The matrix step of Miyake, Theorem 4.6.16 (3)** (p. 169): for `η = η_q` (an `η`-matrix for
`Q`) and `η' = η'_q` (an `η`-matrix for `N/Q`), `η η' = γ ω_N` with `γ ∈ Γ₀(N)` whose lower-right
entry `d` satisfies `d ≡ 1 mod Q` and `Q d ≡ 1 mod N/Q` (Miyake: `γ ≡ 1 mod N_q`,
`γ ≡ [N_q 0; 0 1/N_q] mod N/N_q`). -/
@[kb "miyake1989" "Theorem 4.6.16 (3), proof, p. 169"]
theorem IsEtaMatrix.exists_mul_eq_fricke [NeZero N] (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M)
    (hM' : IsEtaMatrix N (N / Q) M') :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 N ∧
      M * M' = (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![0, -1; (N : ℤ), 0] ∧
      ((γ 1 1 : ℤ) : ZMod Q) = 1 ∧ (Q : ZMod (N / Q)) * ((γ 1 1 : ℤ) : ZMod (N / Q)) = 1 := by
  have hQ' : (N / Q) ∥ N := hQ.div (NeZero.ne N)
  have hNQ : N / (N / Q) = Q := Nat.div_div_self hQ.dvd (NeZero.ne N)
  have hAL := hM.isAtkinLehnerMatrix hQ
  have hAL' := hM'.isAtkinLehnerMatrix hQ'
  have hmulN : Q * (N / Q) = N := Nat.mul_div_cancel' hQ.dvd
  have hprod := hAL.mul (by rw [hmulN]) hAL'
  rw [hmulN] at hprod
  obtain ⟨γ, hγ, heq⟩ := (TauCeti.isAtkinLehnerMatrix_fricke (N := N)).exists_mem_Gamma0_eq_mul_left
    (NeZero.ne N) dvd_rfl hprod
  refine ⟨γ, hγ, heq, ?_⟩
  -- entries of the two `η`-matrices
  obtain ⟨g, rfl, -, g01Q, -, -, g00R, g01R, -, -⟩ := hM.exists_entries
  obtain ⟨g', rfl, -, g'01R, -, -, -, -, -, g'11Q⟩ := hM'.exists_entries
  rw [hNQ] at g'11Q
  -- the upper-left entry of `γ` is `-(η η')₀₁`
  have h01 := congrFun (congrFun heq 0) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    mul_zero, add_zero, zero_add, mul_one, mul_neg] at h01
  have ha : γ 0 0 = -((Q : ℤ) * g 0 0 * g' 0 1 + g 0 1 * g' 1 1) := by linear_combination h01
  -- `a d ≡ 1 mod N`
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
  obtain ⟨c, hc⟩ := mem_Gamma0_iff_dvd.mp hγ
  have hN : (N : ℤ) = (Q : ℤ) * ((N / Q : ℕ) : ℤ) := by exact_mod_cast hmulN.symm
  have had : (N : ℤ) ∣ γ 0 0 * γ 1 1 - 1 := ⟨γ 0 1 * c, by rw [hc] at hdet; linear_combination hdet⟩
  have hadQ : (Q : ℤ) ∣ γ 0 0 * γ 1 1 - 1 := (Dvd.intro _ hN.symm).trans had
  have hadR : ((N / Q : ℕ) : ℤ) ∣ γ 0 0 * γ 1 1 - 1 := (Dvd.intro_left _ hN.symm).trans had
  -- `a ≡ 1 mod Q`, `a ≡ Q mod N/Q`
  have haQ : (Q : ℤ) ∣ γ 0 0 - 1 := by
    have e1 := dvd_of_sq_dvd g01Q
    have e2 := dvd_of_sq_dvd g'11Q
    obtain ⟨u, hu⟩ := e1
    obtain ⟨v, hv⟩ := e2
    refine ⟨-(g 0 0 * g' 0 1) - Q * u * v - u + v, ?_⟩
    rw [ha]
    have h1 : g 0 1 = Q * u - 1 := by linear_combination hu
    have h2 : g' 1 1 = Q * v + 1 := by linear_combination hv
    rw [h1, h2]
    ring
  have haR : ((N / Q : ℕ) : ℤ) ∣ γ 0 0 - Q := by
    obtain ⟨u, hu⟩ := dvd_of_sq_dvd g00R
    obtain ⟨v, hv⟩ := dvd_of_sq_dvd g'01R
    obtain ⟨w, hw⟩ := dvd_of_sq_dvd g01R
    have h1 : g 0 0 = (N / Q : ℕ) * u + 1 := by linear_combination hu
    have h2 : g' 0 1 = (N / Q : ℕ) * v - 1 := by linear_combination hv
    rw [ha, h1, h2, hw]
    exact ⟨-(Q * (u * ((N / Q : ℕ) * v - 1) + v)) - w * g' 1 1, by ring⟩
  constructor
  · refine cast_eq_one_of_dvd ?_
    have : γ 1 1 - 1 = (γ 0 0 * γ 1 1 - 1) - (γ 0 0 - 1) * γ 1 1 := by ring
    rw [this]
    exact dvd_sub hadQ (Dvd.dvd.mul_right haQ _)
  · have hc1 : (((Q : ℤ) * γ 1 1 : ℤ) : ZMod (N / Q)) = 1 := by
      refine cast_eq_one_of_dvd ?_
      have : (Q : ℤ) * γ 1 1 - 1 = (γ 0 0 * γ 1 1 - 1) - (γ 0 0 - Q) * γ 1 1 := by ring
      rw [this]
      exact dvd_sub hadR (Dvd.dvd.mul_right haR _)
    simpa using hc1

/-- **Miyake's `γ_q` exist** ((4.6.19), p. 166): for an exact divisor `Q` of `N` there is an
`η`-matrix for `Q`. (Chinese remainder theorem and strong approximation for `SL₂`.) -/
@[kb "miyake1989" "(4.6.19), p. 166 (existence)"]
theorem exists_isEtaMatrix (hQ : Q ∥ N) : ∃ M, IsEtaMatrix N Q M := by
  set R := N / Q
  have hcop : IsCoprime ((Q ^ 2 : ℕ) : ℤ) ((R ^ 2 : ℕ) : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow 2 2 hQ.coprime
  obtain ⟨x, y, hxy⟩ := id hcop
  set e : ℤ := y * ((R ^ 2 : ℕ) : ℤ)
  -- `e ≡ 1 mod Q²`, `e ≡ 0 mod R²`
  have he1 : ((Q ^ 2 : ℕ) : ℤ) ∣ e - 1 := ⟨-x, by linear_combination hxy⟩
  have he0 : ((R ^ 2 : ℕ) : ℤ) ∣ e := Dvd.intro_left _ rfl
  set A : Matrix (Fin 2) (Fin 2) ℤ := !![1 - e, -e; e, 1 - e]
  have hdetQ : ((Q ^ 2 : ℕ) : ℤ) ∣ A.det - 1 := by
    obtain ⟨t, ht⟩ := he1
    refine ⟨2 * ((Q ^ 2 : ℕ) : ℤ) * t * t + 2 * t, ?_⟩
    simp only [A, Matrix.det_fin_two_of]
    have : e = ((Q ^ 2 : ℕ) : ℤ) * t + 1 := by linear_combination ht
    rw [this]
    ring
  have hdetR : ((R ^ 2 : ℕ) : ℤ) ∣ A.det - 1 := by
    obtain ⟨t, ht⟩ := he0
    simp only [A, Matrix.det_fin_two_of]
    rw [ht]
    exact ⟨2 * ((R ^ 2 : ℕ) : ℤ) * t * t - 2 * t, by ring⟩
  set n := Q ^ 2 * R ^ 2
  have hdet : (n : ℤ) ∣ A.det - 1 := by
    have := hcop.mul_dvd hdetQ hdetR
    simpa [n] using this
  let Abar : SL(2, ZMod n) := ⟨A.map (Int.cast : ℤ → ZMod n), by
    rw [← Int.cast_det, ← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdet⟩
  obtain ⟨γ, hγ⟩ := Matrix.SpecialLinearGroup.map_intCast_zmod_surjective Abar
  have hent : ∀ i j, (n : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) i j - A i j := fun i j ↦ by
    have := congrArg (fun g : SL(2, ZMod n) ↦ (g : Matrix (Fin 2) (Fin 2) (ZMod n)) i j) hγ
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      Int.coe_castRingHom, Abar] at this
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp this.symm
  have hQn : ((Q ^ 2 : ℕ) : ℤ) ∣ (n : ℤ) := ⟨((R ^ 2 : ℕ) : ℤ), by simp [n]⟩
  have hRn : ((R ^ 2 : ℕ) : ℤ) ∣ (n : ℤ) := ⟨((Q ^ 2 : ℕ) : ℤ), by simp [n, mul_comm]⟩
  refine ⟨_, γ, fun i j ↦ ?_, fun i j ↦ ?_, rfl⟩
  · rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    have h := hQn.trans (hent i j)
    have : S2 i j - (γ : Matrix (Fin 2) (Fin 2) ℤ) i j =
        -((γ : Matrix (Fin 2) (Fin 2) ℤ) i j - A i j) - (A i j - S2 i j) := by ring
    rw [this]
    refine dvd_sub (dvd_neg.mpr (by exact_mod_cast h)) ?_
    obtain ⟨t, ht⟩ := he1
    fin_cases i <;> fin_cases j <;> simp only [A, S2, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    first | exact ⟨t, by linear_combination ht⟩ | exact ⟨-t, by linear_combination -ht⟩
  · rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    have h := hRn.trans (hent i j)
    have : (1 : Matrix (Fin 2) (Fin 2) ℤ) i j - (γ : Matrix (Fin 2) (Fin 2) ℤ) i j =
        -((γ : Matrix (Fin 2) (Fin 2) ℤ) i j - A i j) - (A i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j) := by
      ring
    rw [this]
    refine dvd_sub (dvd_neg.mpr (by exact_mod_cast h)) ?_
    rw [Matrix.one_fin_two]
    obtain ⟨t, ht⟩ := he0
    fin_cases i <;> fin_cases j <;> simp only [A, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    first | exact ⟨t, by linear_combination ht⟩ | exact ⟨-t, by linear_combination -ht⟩

end ModularFormsKB.Miyake.Wave9
