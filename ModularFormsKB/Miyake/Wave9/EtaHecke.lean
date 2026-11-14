import ModularFormsKB.Miyake.Wave9.EtaPrimitive
import TauCeti.NumberTheory.ModularForms.AtkinLehner.Hecke
import TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform
import TauCeti.NumberTheory.ModularForms.Newforms.Fricke

/-!
# Miyake §4.6: (4.6.22)–(4.6.23) and Theorem 4.6.16 (4) at the primes dividing `N`

Miyake, *Modular Forms* (Springer 1989), (4.6.22)–(4.6.23), p. 168, and Theorem 4.6.16 (4),
pp. 168–170.

* `atkinLehnerOperatorGamma1_heckeTNat_of_coprime`: for an Atkin–Lehner matrix `W` of `Q ∥ N` and
  every `n` coprime to `Q` (not only to `N`), `W_Q (T_n f) = ⟨u⟩ T_n (W_Q f)` on `M_k(Γ₁(N))`, with
  `u ≡ n⁻¹ mod Q`, `u ≡ 1 mod N/Q`. For `n ∣ N` the operator `T_n` is Tau Ceti's
  `Γ₁(N) diag(1, n) Γ₁(N)`, which is `U_n` (`heckeUCuspNat_eq_heckeTCuspNat`).

  **Credit.** The three declarations `exists_natDiagGL_mul_atkinLehnerGL_eq_of_coprime`,
  `atkinLehnerOperatorGamma1_heckeTNat_of_mul_eq'`, `atkinLehnerOperatorGamma1_heckeTNat_of_coprime`
  and the cusp-form version are copied from Tau Ceti
  (`TauCeti/NumberTheory/ModularForms/AtkinLehner/Hecke.lean`, pinned revision 4908b03, private
  lemmas `exists_natDiagGL_mul_atkinLehnerGL_eq`, `atkinLehnerOperatorGamma1_heckeTNat_of_mul_eq`
  and theorems `atkinLehnerOperatorGamma1_heckeTNat`, `atkinLehnerOperatorGamma1Cusp_heckeTCuspNat`)
  with the hypothesis `n.Coprime N` weakened to `n.Coprime Q`: the proof only inverts the
  upper-left entry `Q` of the Atkin–Li matrix modulo `n`.
* `eta_heckeTCuspNat` ((4.6.22), (4.6.23)): on `𝒮_k(N, ψ φ)`, `η (T(n) f) = ψ(n) T(n) (η f)` for
  `(n, Q) = 1`; Miyake's `(f | η_q) | T(n) = conj χ_q(n) (f | T(n)) | η_q` for `(n, N_q) = 1`, and
  for `Q = N/N_q` his (4.6.23).
* `exists_isPrimitive_eta_all` (Theorem 4.6.16 (4)): `b_p = conj ψ(p) a_p` for every prime
  `p ∤ Q`, and `b_p = φ(p) conj(a_p)` for every prime `p ∣ Q`. For `Q = N_q` this is Miyake's
  `b_p = conj χ_q(p) a_p` (`p ≠ q`) and `b_q = χ'_q(q) conj(a_q)`.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2
open Matrix
open scoped MatrixGroups ModularForm TauCeti.ExactDivisor

noncomputable section

namespace ModularFormsKB.Miyake.Wave9

open TauCeti

section Gamma1

open DoubleCoset HeckeRing.GLn
open scoped Pointwise

local notation "φ" => Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℚ ℝ)

variable {N Q : ℕ} [NeZero N] {M : Matrix (Fin 2) (Fin 2) ℤ} {k : ℤ}
variable {n : ℕ} [NeZero n]

omit [NeZero N] in
/-- **`diag(1, n)` moves across an Atkin–Lehner matrix of Atkin–Li shape.** For `n` coprime to
`Q` there are an Atkin–Lehner matrix `W` for `Q`, `A ∈ Γ₀(N)` and `B ∈ Γ₁(N)` with
`diag(1, n) · W = W · A · diag(1, n) · B`, where the diamond label of `A` is `n⁻¹` modulo `Q` and
`1` modulo `N / Q`. The matrix `W = !![Q, 1; N z, Q w]` has the shape of Atkin and Li's: its
upper-left entry `Q` is invertible modulo `n`, which lets `B` be a power of `T`. -/
theorem exists_natDiagGL_mul_atkinLehnerGL_eq_of_coprime (h : Q ∥ N) (hn : n.Coprime Q) :
    ∃ M : Matrix (Fin 2) (Fin 2) ℤ, ∃ hM : IsAtkinLehnerMatrix N Q M,
      ∃ A : SL(2, ℤ), ∃ hA : A ∈ Gamma0 N,
        ZMod.unitsMap h.dvd ((Gamma0Map N).toHomUnits ⟨A, hA⟩) =
            (ZMod.unitOfCoprime n hn)⁻¹ ∧
          ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd) ((Gamma0Map N).toHomUnits ⟨A, hA⟩) = 1 ∧
          ∃ B ∈ Gamma1 N, φ (natDiagGL 2 ![1, n]) * atkinLehnerGL h.pos hM =
            atkinLehnerGL h.pos hM * mapGL ℝ A * φ (natDiagGL 2 ![1, n] * mapGL ℚ B) := by
  set m := N / Q with hm
  have hNm : N = Q * m := (Nat.mul_div_cancel' h.dvd).symm
  have hN : (N : ℤ) = Q * m := by exact_mod_cast hNm
  set a : ℤ := Nat.gcdA Q m
  set b : ℤ := Nat.gcdB Q m
  have hred : (Q : ℤ) * a + m * b = 1 := by
    have := Nat.gcd_eq_gcd_ab Q m
    rw [h.coprime, Nat.cast_one] at this
    exact this.symm
  obtain ⟨j, l, hjl⟩ := Nat.isCoprime_iff_coprime.mpr hn.symm
  -- the integral matrices of `diag(1, n)`, `W`, `A` and `B = Tʲ`
  set X : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, (n : ℤ)]
  set W : Matrix (Fin 2) (Fin 2) ℤ := !![(Q : ℤ) * 1, 1; (Q : ℤ) * m * -b, (Q : ℤ) * a]
  have hW : IsAtkinLehnerMatrix N Q W :=
    isAtkinLehnerMatrix_of_entries hNm 1 1 (-b) a (by linear_combination hred)
  set Am : Matrix (Fin 2) (Fin 2) ℤ :=
    !![Q * a + n * m * b, a * l - a - j * m * b;
      -((Q : ℤ) * m) * b * (n - 1), Q * a + j * (Q * m) * b + m * b * l]
  set Bm : Matrix (Fin 2) (Fin 2) ℤ := !![1, j; 0, 1]
  have key : X * W = W * Am * X * Bm := by
    simp only [X, W, Am, Bm, Matrix.mul_fin_two]
    congrm !![?_, ?_; ?_, ?_]
    · linear_combination (-(Q : ℤ)) * hred
    · linear_combination (-1 : ℤ) * hred - (Q * a + m * b) * hjl
    · linear_combination ((n : ℤ) * Q * m * b) * hred
    · linear_combination (-((n : ℤ) * Q * a)) * hred
  have hdetAm : Am.det = 1 := by
    have hdet := congrArg Matrix.det key
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, hW.det_eq] at hdet
    have hX : X.det = n := by simp [X, Matrix.det_fin_two_of]
    have hB : Bm.det = 1 := by simp [Bm, Matrix.det_fin_two_of]
    rw [hX, hB] at hdet
    have hQn : (Q : ℤ) * n ≠ 0 :=
      mul_ne_zero (by exact_mod_cast h.pos.ne') (by exact_mod_cast NeZero.ne n)
    exact mul_left_cancel₀ hQn (by linear_combination -hdet)
  let A : SL(2, ℤ) := ⟨Am, hdetAm⟩
  let B : SL(2, ℤ) := ⟨Bm, by simp [Bm, Matrix.det_fin_two_of]⟩
  have hA : A ∈ Gamma0 N := mem_Gamma0_iff_dvd.mpr ⟨-b * (n - 1), by simp [A, Am, hN]; ring⟩
  -- the diamond label of `A` is its lower-right entry
  have hlabel : (((Gamma0Map N).toHomUnits ⟨A, hA⟩ : (ZMod N)ˣ) : ZMod N) =
      ((Q * a + j * (Q * m) * b + m * b * l : ℤ) : ZMod N) := by
    simp [A, Am, Gamma0Map_apply]
  refine ⟨W, hW, A, hA, eq_inv_of_mul_eq_one_left (Units.ext ?_), Units.ext ?_, B,
    mem_Gamma1_of_dvd_lowerRow (by simp [B, Bm]) (by simp [B, Bm]), Units.ext ?_⟩
  · -- modulo `Q`, the label times `n` is `1`
    rw [Units.val_mul, ZMod.unitsMap_val, hlabel, ZMod.cast_intCast h.dvd,
      ZMod.coe_unitOfCoprime, Units.val_one]
    have hmod : (Q * a + j * (Q * m) * b + m * b * l) * (n : ℤ) =
        1 + Q * (n * a + n * j * m * b - n * l * a - j) := by
      linear_combination ((n : ℤ) * l) * hred + hjl
    have := congrArg (Int.cast : ℤ → ZMod Q) hmod
    push_cast [ZMod.natCast_self] at this
    simpa using this
  · -- modulo `N / Q`, the label is `1`
    rw [ZMod.unitsMap_val, hlabel, ZMod.cast_intCast (Nat.div_dvd_of_dvd h.dvd), Units.val_one]
    have hmod : Q * a + j * (Q * m) * b + m * b * l = 1 + m * (b * (j * Q + l - 1)) := by
      linear_combination hred
    rw [hmod]
    push_cast [← hm, ZMod.natCast_self]
    ring
  · -- the matrix identity, read in `GL (Fin 2) ℝ`
    have hX : (↑(φ (natDiagGL 2 ![1, n])) : Matrix (Fin 2) (Fin 2) ℝ) = X.map (↑) := by
      rw [Matrix.GeneralLinearGroup.val_map_apply, coe_map_natDiagGL_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [X]
    have hφB : (↑(φ (natDiagGL 2 ![1, n] * mapGL ℚ B)) : Matrix (Fin 2) (Fin 2) ℝ) =
        (X * Bm).map (↑) := by
      -- `mapGL` of the literal `B = ⟨Bm, _⟩` is `Bm` with its entries cast, by definition
      rw [map_mul, Units.val_mul, hX, Matrix.map_mul_intCast, map_mapGL]
      rfl
    -- likewise for the literal `A = ⟨Am, _⟩`
    have hAm : (↑(mapGL ℝ A) : Matrix (Fin 2) (Fin 2) ℝ) = Am.map (↑) := by
      rw [mapGL_coe_matrix]
      rfl
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hX, hφB, coe_atkinLehnerGL, hAm,
      ← Matrix.map_mul_intCast, ← Matrix.map_mul_intCast, ← Matrix.map_mul_intCast, key]
    simp only [Matrix.mul_assoc]

set_option maxHeartbeats 1000000 in
/-- The trace argument behind `atkinLehnerOperatorGamma1_heckeTNat`: a factorization
`diag(1, n) · W = W · A · diag(1, n) · B` with `A ∈ Γ₀(N)` and `B ∈ Γ₁(N)` gives
`W_Q (Tₙ f) = Tₙ (⟨d_A⟩ (W_Q f))`. -/
theorem atkinLehnerOperatorGamma1_heckeTNat_of_mul_eq' (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) {A : SL(2, ℤ)} (hA : A ∈ Gamma0 N) {B : SL(2, ℤ)}
    (hB : B ∈ Gamma1 N)
    (hmul : φ (natDiagGL 2 ![1, n]) * atkinLehnerGL hQ h =
      atkinLehnerGL hQ h * mapGL ℝ A * φ (natDiagGL 2 ![1, n] * mapGL ℚ B))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    atkinLehnerOperatorGamma1 hQ hQN h k (heckeTNat k n f) =
      heckeTNat k n (diamondOp k ((Gamma0Map N).toHomUnits ⟨A, hA⟩)
        (atkinLehnerOperatorGamma1 hQ hQN h k f)) := by
  have hδ₀ : natDiagGL 2 ![1, n] ∈ doubleCoset ((diagCosetGamma1 N n).out : GL (Fin 2) ℚ)
      ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) := by
    rw [doubleCoset_out_diagCosetGamma1_eq_doubleCoset_natDiagGL]
    exact mem_doubleCoset_self _ _ _
  have hδ : natDiagGL 2 ![1, n] * mapGL ℚ B ∈
      doubleCoset ((diagCosetGamma1 N n).out : GL (Fin 2) ℚ)
        ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) := by
    rw [doubleCoset_out_diagCosetGamma1_eq_doubleCoset_natDiagGL]
    exact mem_doubleCoset.mpr
      ⟨1, one_mem _, mapGL ℚ B, Subgroup.mem_map_of_mem _ hB, by rw [one_mul]⟩
  have := finite_decompQuotient_inv_of_mem_doubleCoset hδ₀
  have : (ConjAct.toConjAct (φ (natDiagGL 2 ![1, n]))⁻¹ •
      (Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex ((Gamma1 N).map (mapGL ℝ)) := by
    rw [← Subgroup.map_mapGL (S := ℚ) (Gamma1 N)]
    exact isFiniteRelIndex_ratCast_conj
  -- the translate by `diag(1, n) · W` has the level of the translate by `diag(1, n) · B`,
  -- because `W` and `A` normalize `Γ₁(N)`
  have hlevel : ConjAct.toConjAct (φ (natDiagGL 2 ![1, n]) * atkinLehnerGL hQ h)⁻¹ •
      (Gamma1 N).map (mapGL ℝ) =
      ConjAct.toConjAct (φ (natDiagGL 2 ![1, n] * mapGL ℚ B))⁻¹ • (Gamma1 N).map (mapGL ℝ) := by
    rw [hmul, mul_assoc, _root_.mul_inv_rev, map_mul, mul_smul,
      Gamma1_map_inv_conjAct_atkinLehnerGL_eq hQ hQN h, conjAct_mapGL_mul_smul_Gamma1 hA]
  have := finite_decompQuotient_inv_of_mem_doubleCoset hδ
  have : (ConjAct.toConjAct (φ (natDiagGL 2 ![1, n] * mapGL ℚ B))⁻¹ •
      (Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex ((Gamma1 N).map (mapGL ℝ)) := by
    rw [← Subgroup.map_mapGL (S := ℚ) (Gamma1 N)]
    exact isFiniteRelIndex_ratCast_conj
  have : (ConjAct.toConjAct (φ (natDiagGL 2 ![1, n]) * atkinLehnerGL hQ h)⁻¹ •
      (Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex ((Gamma1 N).map (mapGL ℝ)) := hlevel ▸ ‹_›
  have hW : atkinLehnerGL hQ h ∈
      Subgroup.normalizer ((Gamma1 N).map (mapGL ℝ) : Set (GL (Fin 2) ℝ)) :=
    (Subgroup.normalizer _).inv_mem_iff.mp
      (Subgroup.conjAct_pointwise_smul_iff.mp (Gamma1_map_inv_conjAct_atkinLehnerGL_eq hQ hQN h))
  apply DFunLike.coe_injective
  rw [coe_atkinLehnerOperatorGamma1, coe_heckeTNat, coe_heckeTNat,
    heckeSlashSum_eq_coe_trace_translate k (diagCosetGamma1 N n) hδ₀
      (Subgroup.map_mapGL (Gamma1 N)) (Subgroup.map_mapGL (Gamma1 N)) f,
    heckeSlashSum_eq_coe_trace_translate k (diagCosetGamma1 N n) hδ
      (Subgroup.map_mapGL (Gamma1 N)) (Subgroup.map_mapGL (Gamma1 N)),
    ← SlashInvariantForm.coe_trace_translate_mul_of_mem_normalizer f _ hW]
  refine congrArg DFunLike.coe (SlashInvariantForm.trace_eq_of_eq_of_coe_eq hlevel ?_)
  rw [_root_.SlashInvariantForm.coe_translate, _root_.SlashInvariantForm.coe_translate,
    coe_diamondOp k _ ⟨A, hA⟩ rfl, coe_atkinLehnerOperatorGamma1, ← SlashAction.slash_mul,
    ← SlashAction.slash_mul, hmul, mul_assoc]

/-- **`W_Q` transports a good `Tₙ` to a diamond twist of `Tₙ`** on `M_k(Γ₁(N))`: for `n` coprime
to `Q`, `W_Q (Tₙ f) = ⟨u⟩ (Tₙ (W_Q f))`, where `u ∈ (ZMod N)ˣ` is `n⁻¹` modulo `Q` and `1` modulo
`N / Q`. At `Q = N` this is the Fricke relation `W_N Tₙ = ⟨n⟩⁻¹ Tₙ W_N`; on a nebentypus space
`⟨u⟩` becomes the scalar of `atkinLehnerOperatorGamma1_heckeTNat_of_mem_modFormCharSpace`. -/
theorem atkinLehnerOperatorGamma1_heckeTNat_of_coprime (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (hn : n.Coprime Q) {u : (ZMod N)ˣ}
    (hu : ZMod.unitsMap hQN u = (ZMod.unitOfCoprime n hn)⁻¹)
    (hu' : ZMod.unitsMap (Nat.div_dvd_of_dvd hQN) u = 1)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    atkinLehnerOperatorGamma1 hQ hQN h k (heckeTNat k n f) =
      diamondOp k u (heckeTNat k n (atkinLehnerOperatorGamma1 hQ hQN h k f)) := by
  have hQN' := h.isExactDivisor hQ.ne' hQN
  obtain ⟨M₀, h₀, A, hA, hAQ, hAm, B, hB, hmul⟩ := exists_natDiagGL_mul_atkinLehnerGL_eq_of_coprime hQN' hn
  have hAu : (Gamma0Map N).toHomUnits ⟨A, hA⟩ = u :=
    hQN'.unitsEquivProd.injective <| Prod.ext
      (by rw [Nat.IsExactDivisor.unitsEquivProd_apply_fst,
        Nat.IsExactDivisor.unitsEquivProd_apply_fst, hAQ, hu])
      (by rw [Nat.IsExactDivisor.unitsEquivProd_apply_snd,
        Nat.IsExactDivisor.unitsEquivProd_apply_snd, hAm, hu'])
  -- every Atkin–Lehner matrix for `Q` is `γ W₀` with `γ ∈ Γ₀(N)`, and `⟨d_γ⟩` commutes with `Tₙ`
  obtain ⟨γ, hγ, rfl⟩ := h₀.exists_mem_Gamma0_eq_mul_left hQ.ne' hQN h
  have hc := fun g ↦ DFunLike.congr_fun
    (commute_heckeTNat_diamondOp k n ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩)).eq g
  have hc' := DFunLike.congr_fun (commute_heckeTNat_diamondOp k n u).eq
  simp only [mul_apply_eq_comp] at hc hc'
  rw [atkinLehnerOperatorGamma1_mul_left hQ hQN h₀ k hγ, LinearMap.comp_apply,
    LinearMap.comp_apply, ← hc, ← hc', ← hAu]
  exact atkinLehnerOperatorGamma1_heckeTNat_of_mul_eq' hQ hQN h₀ hA hB hmul _

/-- **`W_Q` transports a good `Tₙ` to a diamond twist of `Tₙ`** on `S_k(Γ₁(N))`: the cusp-form
counterpart of `atkinLehnerOperatorGamma1_heckeTNat`. -/
theorem atkinLehnerOperatorGamma1Cusp_heckeTCuspNat_of_coprime (hQ : 0 < Q) (hQN : Q ∣ N)
    (h : IsAtkinLehnerMatrix N Q M) (hn : n.Coprime Q) {u : (ZMod N)ˣ}
    (hu : ZMod.unitsMap hQN u = (ZMod.unitOfCoprime n hn)⁻¹)
    (hu' : ZMod.unitsMap (Nat.div_dvd_of_dvd hQN) u = 1)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    atkinLehnerOperatorGamma1Cusp hQ hQN h k (heckeTCuspNat k n f) =
      diamondOpCusp k u (heckeTCuspNat k n (atkinLehnerOperatorGamma1Cusp hQ hQN h k f)) := by
  apply CuspForm.toModularFormₗ_injective
  simpa only [CuspForm.toModularFormₗ_eq_coe, atkinLehnerOperatorGamma1_coe_cuspForm,
    heckeTNat_coe_cuspForm, diamondOp_coe_cuspForm] using
    atkinLehnerOperatorGamma1_heckeTNat_of_coprime hQ hQN h hn hu hu'
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)

end Gamma1

open ModularFormsKB.Miyake.Wave4 ModularFormsKB.Miyake.Wave7

variable {N Q : ℕ} [NeZero N] {M : Matrix (Fin 2) (Fin 2) ℤ}

/-- The value of `conj ψ · φ` at the unit that is `n⁻¹` modulo `Q` and `1` modulo `N/Q` is `ψ(n)`. -/
theorem splitChar_inv_unit_eq (hQ : Q ∥ N) (ψ : DirichletCharacter ℂ Q)
    (φ : DirichletCharacter ℂ (N / Q)) {n : ℕ} (hn : n.Coprime Q) {u : (ZMod N)ˣ}
    (hu : ZMod.unitsMap hQ.dvd u = (ZMod.unitOfCoprime n hn)⁻¹)
    (hu' : ZMod.unitsMap (Nat.div_dvd_of_dvd hQ.dvd) u = 1) :
    (((splitChar hQ ψ⁻¹ φ).toUnitHom u : ℂˣ) : ℂ) = ψ (n : ZMod Q) := by
  rw [toUnitHom_splitChar, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, hu,
    hu', map_one, mul_one, map_inv, Units.val_inv_eq_inv_val, MulChar.coe_toUnitHom,
    ZMod.coe_unitOfCoprime, MulChar.inv_apply_eq_inv', inv_inv]

/-- **Miyake, (4.6.22)** (and (4.6.23) for `Q = N/N_q`): for `f ∈ 𝒮_k(N, ψ φ)` and `(n, Q) = 1`,
`η (T(n) f) = ψ(n) T(n) (η f)`, i.e. `(f | η) | T(n) = conj ψ(n) (f | T(n)) | η` (here `T(n)` is
Tau Ceti's `Γ₁(N) diag(1, n) Γ₁(N)`, Miyake's `T(n)` on `𝒮_k(N, χ)` by Theorem 4.5.18 (2)). -/
@[kb "miyake1989" "(4.6.22), (4.6.23), p. 168"]
theorem eta_heckeTCuspNat (k : ℤ) (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M)
    (ψ : DirichletCharacter ℂ Q) (φ : DirichletCharacter ℂ (N / Q)) {n : ℕ} [NeZero n]
    (hn : n.Coprime Q) (f : cuspSpace k (splitChar hQ ψ φ)) :
    atkinLehnerOperatorGamma1Cusp hQ.pos hQ.dvd (hM.isAtkinLehnerMatrix hQ) k
        (heckeTCuspNat k n (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) =
      ψ (n : ZMod Q) • heckeTCuspNat k n (atkinLehnerOperatorGamma1Cusp hQ.pos hQ.dvd
        (hM.isAtkinLehnerMatrix hQ) k (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  set u := hQ.unitsEquivProd.symm ((ZMod.unitOfCoprime n hn)⁻¹, 1)
  have hu : ZMod.unitsMap hQ.dvd u = (ZMod.unitOfCoprime n hn)⁻¹ := by
    rw [← Nat.IsExactDivisor.unitsEquivProd_apply_fst hQ, MulEquiv.apply_symm_apply]
  have hu' : ZMod.unitsMap (Nat.div_dvd_of_dvd hQ.dvd) u = 1 := by
    rw [← Nat.IsExactDivisor.unitsEquivProd_apply_snd hQ, MulEquiv.apply_symm_apply]
  have hc := DFunLike.congr_fun (commute_heckeTCuspNat_diamondOpCusp k n u).eq
    (atkinLehnerOperatorGamma1Cusp hQ.pos hQ.dvd (hM.isAtkinLehnerMatrix hQ) k
      (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
  simp only [mul_apply_eq_comp] at hc
  rw [atkinLehnerOperatorGamma1Cusp_heckeTCuspNat_of_coprime hQ.pos hQ.dvd _ hn hu hu', ← hc,
    diamondOpCusp_apply_of_mem_cuspFormCharSpace k _ u (etaOp_mem k hQ hM ψ φ f), map_smul,
    splitChar_inv_unit_eq hQ ψ φ hn hu hu']

/-- If `X = c • G` (`c ≠ 0`, `G` a newform) is a `T_p`-eigenvector with eigenvalue `lam`, then
`lam` is the `p`-th coefficient of `G`. -/
private lemma coeff_eq_of_heckeT_eq_smul {k : ℤ} {G : HeckeRing.GL2.Newform N k}
    {X : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} {c : ℂ} (hc : c ≠ 0)
    (hX : X = c • G.toCuspForm) {p : ℕ} (hp : p.Prime) {lam : ℂ}
    (hT : heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) X = lam • X) :
    (qExpansion 1 G.toCuspForm).coeff p = lam := by
  have hG := G.heckeTCuspNat_eq_qExpansion_coeff_smul hp
  rw [hX, map_smul, hG, smul_smul, smul_smul, mul_comm c, mul_comm lam] at hT
  have h1 := smul_left_injective ℂ G.ne_zero hT
  exact mul_right_cancel₀ hc (h1.trans (mul_comm c lam))

/-- **Miyake, Theorem 4.6.16 (4)**: if `f = Σ a_n e(nz)` is a primitive form of `𝒮_k^0(N, ψ φ)`,
then `f | η = c g` with `c ≠ 0` and `g = Σ b_n e(nz)` a primitive form of
`𝒮_k^0(N, conj ψ · φ)`, `b_p = conj ψ(p) a_p` for every prime `p ∤ Q`, and
`b_p = φ(p) conj(a_p)` for every prime `p ∣ Q`. For `Q = N_q`, `ψ = χ_q`, `φ = χ'_q` this is
Miyake's `b_p = conj χ_q(p) a_p` (`p ≠ q`), `b_q = χ'_q(q) conj(a_q)`. -/
@[kb "miyake1989" "Theorem 4.6.16 (4), p. 168"]
theorem exists_isPrimitive_eta_all (k : ℤ) (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M)
    (ψ : DirichletCharacter ℂ Q) (φ : DirichletCharacter ℂ (N / Q))
    {f : cuspSpace k (splitChar hQ ψ φ)} (hf : IsPrimitive f) :
    ∃ g : cuspSpace k (splitChar hQ ψ⁻¹ φ), IsPrimitive g ∧
      (∃ c : ℂ, c ≠ 0 ∧ ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] etaGL hQ hM =
        c • ⇑(g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) ∧
      (∀ p : ℕ, p.Prime → p.Coprime Q → coeff g p = ψ⁻¹ (p : ZMod Q) * coeff f p) ∧
      (∀ p : ℕ, p.Prime → p ∣ Q →
        coeff g p = φ (p : ZMod (N / Q)) * starRingEnd ℂ (coeff f p)) := by
  obtain ⟨g, hg, ⟨c, hc0, hfg⟩, -⟩ := exists_isPrimitive_eta k hQ hM ψ φ hf
  obtain ⟨F, hχ, hF⟩ := (isPrimitive_iff_exists_newform f).mp hf
  obtain ⟨G, -, hG⟩ := (isPrimitive_iff_exists_newform g).mp hg
  have hAL := hM.isAtkinLehnerMatrix hQ
  set W := atkinLehnerOperatorGamma1Cusp hQ.pos hQ.dvd hAL k
  have hWF : W F.toCuspForm = c • G.toCuspForm := by
    apply DFunLike.coe_injective
    rw [coe_atkinLehnerOperatorGamma1Cusp, FunLike.coe_smul, hF, hG]
    exact hfg
  have hcoeffG : ∀ p, coeff g p = (qExpansion 1 G.toCuspForm).coeff p := fun p ↦ by rw [hG]
  have hcoeffF : ∀ p, coeff f p = (qExpansion 1 F.toCuspForm).coeff p := fun p ↦ by rw [hF]
  refine ⟨g, hg, ⟨c, hc0, hfg⟩, ?_, ?_⟩
  · -- primes prime to `Q`: (4.6.22)
    intro p hp hpQ
    have : NeZero p := ⟨hp.ne_zero⟩
    have hcomm := eta_heckeTCuspNat k hQ hM ψ φ hpQ f
    rw [← hF, F.heckeTCuspNat_eq_qExpansion_coeff_smul hp, map_smul] at hcomm
    have hψ : ψ (p : ZMod Q) ≠ 0 := by
      rw [← ZMod.coe_unitOfCoprime p hpQ]; exact ((Units.isUnit _).map ψ).ne_zero
    have hT : heckeTCuspNat k p (W F.toCuspForm) =
        ((ψ (p : ZMod Q))⁻¹ * (qExpansion 1 F.toCuspForm).coeff p) • W F.toCuspForm := by
      rw [mul_smul, hcomm, smul_smul, inv_mul_cancel₀ hψ, one_smul]
    rw [hcoeffG, coeff_eq_of_heckeT_eq_smul hc0 hWF hp hT, MulChar.inv_apply_eq_inv', hcoeffF]
  · -- primes dividing `Q`: through `ω_N` and an Atkin–Lehner matrix for `N/Q`, (4.6.23)
    intro p hp hpQ
    have : NeZero p := ⟨hp.ne_zero⟩
    have hQ' : (N / Q) ∥ N := hQ.div (NeZero.ne N)
    have hNQ : N / (N / Q) = Q := Nat.div_div_self hQ.dvd (NeZero.ne N)
    have hAL' := isAtkinLehnerMatrix_atkinLehnerMatrix hQ'
    set W' := atkinLehnerOperatorGamma1Cusp hQ'.pos hQ'.dvd hAL' k
    -- `W' (W F)` is a multiple of the conjugate newform `F_ρ`
    have hs1 : ∃ s₁ : ℂ, W' (W F.toCuspForm) = s₁ • F.conj.toCuspForm := by
      have hmulN : Q * (N / Q) = N := Nat.mul_div_cancel' hQ.dvd
      have hprod := hAL.mul (by rw [hmulN]) hAL'
      rw [hmulN] at hprod
      obtain ⟨γ, hγ, heq⟩ := (isAtkinLehnerMatrix_fricke (N := N)).exists_mem_Gamma0_eq_mul_left
        (NeZero.ne N) dvd_rfl hprod
      have hGL : atkinLehnerGL hQ.pos hAL * atkinLehnerGL hQ'.pos hAL' =
          mapGL ℝ γ * Wave7.omega N := by
        refine Units.ext ?_
        ext i j
        have h := congrFun (congrFun heq i) j
        simp only [Units.val_mul, coe_atkinLehnerGL, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.map_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix, coe_frickeGL] at h ⊢
        fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> exact_mod_cast h
      obtain ⟨c₁, hc₁⟩ := F.exists_normalizedFrickeOperatorCusp_eq_smul_conj
      rw [normalizedFrickeOperatorCusp_def, LinearMap.smul_apply] at hc₁
      have ha := atkinLehnerNormalizer_ne_zero (NeZero.ne N) k
      refine ⟨((F.χ ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩) : ℂˣ) : ℂ) *
        ((atkinLehnerNormalizer N k)⁻¹ * c₁), ?_⟩
      apply DFunLike.coe_injective
      have hfr : ⇑F.toCuspForm ∣[k] Wave7.omega N =
          (atkinLehnerNormalizer N k)⁻¹ • ⇑(c₁ • F.conj.toCuspForm) := by
        rw [← hc₁, FunLike.coe_smul, smul_smul, inv_mul_cancel₀ ha, one_smul]
        rfl
      rw [coe_atkinLehnerOperatorGamma1Cusp, coe_atkinLehnerOperatorGamma1Cusp,
        ← SlashAction.slash_mul, hGL, SlashAction.slash_mul,
        (mem_cuspFormCharSpace_iff_nebentypus k _ _).mp F.mem_charSpace ⟨γ, hγ⟩,
        ModularForm.smul_slash_of_det_pos k val_det_frickeGL_pos, hfr, FunLike.coe_smul,
        FunLike.coe_smul, smul_smul, smul_smul, mul_assoc]
    obtain ⟨s₁, hs₁⟩ := hs1
    -- `W' ∘ W'` is a nonzero scalar on the character space of `W F`
    have hmemWF := atkinLehnerOperatorGamma1Cusp_mem_cuspFormCharSpace hQ.pos hQ.dvd hAL
      F.mem_charSpace
    obtain ⟨γ', hγ', hsq⟩ := hAL'.exists_mem_Gamma0_mul_self hQ'.ne_zero hQ'.dvd
    have hWW := atkinLehnerOperatorGamma1Cusp_atkinLehnerOperatorGamma1Cusp hQ'.pos hQ'.dvd hAL'
      (hAL'.unitsMap_toHomUnits_gamma0Map_of_mul_self_eq hQ'.ne_zero hQ'.dvd hγ' hsq)
      (hAL'.natCast_mul_toHomUnits_gamma0Map_of_mul_self_eq hγ' hsq) (W F.toCuspForm)
    rw [diamondOpCusp_apply_of_mem_cuspFormCharSpace k _ _ hmemWF, smul_smul] at hWW
    obtain ⟨s₂, hs₂0, hs₂⟩ : ∃ s₂ : ℂ, s₂ ≠ 0 ∧ W' (W' (W F.toCuspForm)) = s₂ • W F.toCuspForm :=
      ⟨_, mul_ne_zero (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hQ'.ne_zero)) (Units.ne_zero _), hWW⟩
    have hWF' : W F.toCuspForm = (s₂⁻¹ * s₁) • W' F.conj.toCuspForm := by
      rw [mul_smul, ← map_smul, ← hs₁, hs₂, smul_smul, inv_mul_cancel₀ hs₂0, one_smul]
    -- (4.6.23): `T_p` on `W' F_ρ`
    have hpQ' : p.Coprime (N / Q) := hQ.coprime.coprime_dvd_left hpQ
    set u := hQ'.unitsEquivProd.symm ((ZMod.unitOfCoprime p hpQ')⁻¹, 1)
    have hu : ZMod.unitsMap hQ'.dvd u = (ZMod.unitOfCoprime p hpQ')⁻¹ := by
      rw [← Nat.IsExactDivisor.unitsEquivProd_apply_fst hQ', MulEquiv.apply_symm_apply]
    have hu' : ZMod.unitsMap (Nat.div_dvd_of_dvd hQ'.dvd) u = 1 := by
      rw [← Nat.IsExactDivisor.unitsEquivProd_apply_snd hQ', MulEquiv.apply_symm_apply]
    have hcomm := atkinLehnerOperatorGamma1Cusp_heckeTCuspNat_of_coprime hQ'.pos hQ'.dvd hAL'
      hpQ' hu hu' F.conj.toCuspForm
    have hc := DFunLike.congr_fun (commute_heckeTCuspNat_diamondOpCusp k p u).eq
      (W' F.conj.toCuspForm)
    simp only [mul_apply_eq_comp] at hc
    have hmemC := atkinLehnerOperatorGamma1Cusp_mem_cuspFormCharSpace hQ'.pos hQ'.dvd hAL'
      F.conj.mem_charSpace
    rw [F.conj.heckeTCuspNat_eq_qExpansion_coeff_smul hp, map_smul, ← hc,
      diamondOpCusp_apply_of_mem_cuspFormCharSpace k _ u hmemC, map_smul] at hcomm
    -- the value of the character of `W' F_ρ` at `u` is `φ(p)⁻¹`
    have hvQ' : ZMod.unitsMap hQ'.dvd (hQ'.unitsInvPart u) = ZMod.unitOfCoprime p hpQ' := by
      rw [Nat.IsExactDivisor.unitsMap_unitsInvPart_left, hu, inv_inv]
    have hvQ : ZMod.unitsMap hQ.dvd (hQ'.unitsInvPart u) = 1 := by
      have h1 : ZMod.unitsMap (Nat.div_dvd_of_dvd hQ'.dvd) (hQ'.unitsInvPart u) = 1 := by
        rw [Nat.IsExactDivisor.unitsMap_unitsInvPart_right, hu']
      have key : ∀ (d : ℕ) (hd : d ∣ N), d = Q →
          ZMod.unitsMap hd (hQ'.unitsInvPart u) = 1 →
          ZMod.unitsMap hQ.dvd (hQ'.unitsInvPart u) = 1 := by
        rintro d hd rfl h; exact h
      exact key _ _ hNQ h1
    have hval : (((splitChar hQ ψ φ).toUnitHom (hQ'.unitsInvPart u) : ℂˣ) : ℂ) =
        φ (p : ZMod (N / Q)) := by
      rw [toUnitHom_splitChar, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
        hvQ]
      change ((ψ.toUnitHom 1 * φ.toUnitHom (ZMod.unitsMap hQ'.dvd (hQ'.unitsInvPart u)) : ℂˣ) : ℂ)
        = _
      rw [hvQ', map_one, one_mul, MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime]
    have hval' : ((F.conj.χ.comp ((hAL'.isExactDivisor hQ'.pos.ne' hQ'.dvd).unitsInvPart :
        (ZMod N)ˣ →* (ZMod N)ˣ) u : ℂˣ) : ℂ) = (φ (p : ZMod (N / Q)))⁻¹ := by
      rw [MonoidHom.comp_apply, HeckeRing.GL2.Newform.χ_conj, hχ, MonoidHom.inv_apply,
        Units.val_inv_eq_inv_val]
      exact congrArg (·⁻¹) hval
    rw [hval'] at hcomm
    have hφ : φ (p : ZMod (N / Q)) ≠ 0 := by
      rw [← ZMod.coe_unitOfCoprime p hpQ']; exact ((Units.isUnit _).map φ).ne_zero
    have hconjp : (qExpansion 1 F.conj.toCuspForm).coeff p =
        starRingEnd ℂ ((qExpansion 1 F.toCuspForm).coeff p) := by
      rw [F.qExpansion_conj, PowerSeries.coeff_map]
    have hTC : heckeTCuspNat k p (W' F.conj.toCuspForm) =
        (φ (p : ZMod (N / Q)) * starRingEnd ℂ ((qExpansion 1 F.toCuspForm).coeff p)) •
          W' F.conj.toCuspForm := by
      have h2 := congrArg (fun X ↦ φ (p : ZMod (N / Q)) • X) hcomm
      simp only [smul_smul, mul_inv_cancel₀ hφ, one_smul] at h2
      rw [← hconjp, h2]
    have hT : heckeTCuspNat k p (W F.toCuspForm) =
        (φ (p : ZMod (N / Q)) * starRingEnd ℂ ((qExpansion 1 F.toCuspForm).coeff p)) •
          W F.toCuspForm := by
      rw [hWF', map_smul, hTC, smul_comm]
    rw [hcoeffG, coeff_eq_of_heckeT_eq_smul hc0 hWF hp hT, hcoeffF]

end ModularFormsKB.Miyake.Wave9
