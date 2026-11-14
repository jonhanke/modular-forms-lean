import ModularFormsKB.Miyake.Wave9.EtaMatrix
import ModularFormsKB.Miyake.Wave8.FrickePrimitive
import TauCeti.NumberTheory.ModularForms.AtkinLehner.NewSpace
import TauCeti.NumberTheory.ModularForms.AtkinLehner.OldSpace
import TauCeti.NumberTheory.ModularForms.AtkinLehner.Hecke
import TauCeti.NumberTheory.ModularForms.AtkinLehner.PseudoEigenvalue

/-!
# Miyake §4.6: Theorem 4.6.16 (the operators `η_q`, `η'_q`)

Miyake, *Modular Forms* (Springer 1989), Theorem 4.6.16, pp. 168–170.

Let `q` be a prime factor of `N`, `N_q` the `q`-component of `N`, and split `χ = χ_q χ'_q` with
`χ_q` modulo `N_q` and `χ'_q` modulo `N/N_q` (p. 166). Everything here is stated for an exact
divisor `Q ∥ N` and a character `χ = ψ φ` with `ψ` modulo `Q`, `φ` modulo `N/Q`
(`splitChar hQ ψ φ`), and an `η`-matrix `M` for `Q` (`IsEtaMatrix N Q M`):

* Miyake's `η_q` is the case `Q = N_q`, `ψ = χ_q`, `φ = χ'_q`;
* Miyake's `η'_q` is the case `Q = N/N_q`, `ψ = χ'_q`, `φ = χ_q` (then `N/Q = N_q`).

The slash is Mathlib's, `(f ∣[k] α)(z) = det(α)^{k-1} (cz+d)^{-k} f(αz)`; Miyake's is
`det(α)^{k/2} (cz+d)^{-k} f(αz)`. For `det α = Q` they differ by the positive constant
`Q^{1-k/2}`; this changes no statement except the constants of (3), where `η²` acquires the
factor `Q^{k-2}` (the slash of the scalar matrix `Q`). Miyake's `conj χ` is `χ⁻¹`.

## Results
* (1), (2): `etaNewEquiv`, `etaOldEquiv`: `η` induces isomorphisms
  `𝒮_k^0(N, ψ φ) ≃ 𝒮_k^0(N, conj ψ · φ)`, `𝒮_k^1(N, ψ φ) ≃ 𝒮_k^1(N, conj ψ · φ)`. With
  `Q = N_q` this is (1); with `Q = N/N_q` it is (2).
* (3): `eta_slash_eta`: `f | η² = Q^{k-2} ψ(-1) conj φ(Q) f`. With `Q = N_q` this is Miyake's
  `f | η_q² = χ_q(-1) conj χ'_q(N_q) f`. With `Q = N/N_q` it gives
  `f | η'_q² = χ'_q(-1) conj χ_q(N/N_q) f`; Miyake prints `χ_q(N/N_q)` without the bar, which is
  wrong whenever `χ_q(N/N_q)² ≠ 1` and `f ≠ 0` (`eta_slash_eta_eq_book_iff`, erratum).
  `eta_slash_eta'`: `f | η_q η'_q = conj χ'_q(N_q) f | ω_N`.
* (4): `exists_isPrimitive_eta`: for a primitive form `f`, `f | η = c g` with `c ≠ 0` and `g` a
  primitive form of `𝒮_k^0(N, conj ψ · φ)`, and `b_p = conj ψ(p) a_p` for every prime `p ∤ N`.
  Miyake's `b_p = conj χ_q(p) a_p` for primes `p ∣ N/N_q` and `b_q = χ'_q(q) conj(a_q)` are
  proved in `EtaHecke.lean` (`exists_isPrimitive_eta_all`).

Inputs from Tau Ceti: the Atkin–Lehner operators on `Γ₁(N)` (`atkinLehnerOperatorGamma1Cusp`),
their character shift, square, preservation of new and old forms, and the Atkin–Lehner transport
of newforms (`Newform.atkinLehnerTransform`).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm TauCeti.ExactDivisor

noncomputable section

namespace ModularFormsKB.Miyake.Wave9

open ModularFormsKB.Miyake.Wave4 ModularFormsKB.Miyake.Wave6 ModularFormsKB.Miyake.Wave7
  ModularFormsKB.Miyake.Wave8

variable {N Q : ℕ} [NeZero N] {M M' : Matrix (Fin 2) (Fin 2) ℤ}

/-- The character `ψ φ` modulo `N` of a character `ψ` modulo `Q` and `φ` modulo `N/Q` (Miyake's
`χ = χ_q χ'_q`, p. 166, for `Q = N_q`). -/
abbrev splitChar (hQ : Q ∥ N) (ψ : DirichletCharacter ℂ Q) (φ : DirichletCharacter ℂ (N / Q)) :
    DirichletCharacter ℂ N :=
  ψ.changeLevel hQ.dvd * φ.changeLevel (Nat.div_dvd_of_dvd hQ.dvd)

theorem toUnitHom_splitChar (hQ : Q ∥ N) (ψ : DirichletCharacter ℂ Q)
    (φ : DirichletCharacter ℂ (N / Q)) :
    (splitChar hQ ψ φ).toUnitHom =
      ψ.toUnitHom.comp (ZMod.unitsMap hQ.dvd) *
        φ.toUnitHom.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hQ.dvd)) := by
  ext u
  have h1 := congrArg (fun χ : (ZMod N)ˣ →* ℂˣ ↦ ((χ u : ℂˣ) : ℂ))
    (DirichletCharacter.changeLevel_toUnitHom (χ := ψ) hQ.dvd)
  have h2 := congrArg (fun χ : (ZMod N)ˣ →* ℂˣ ↦ ((χ u : ℂˣ) : ℂ))
    (DirichletCharacter.changeLevel_toUnitHom (χ := φ) (Nat.div_dvd_of_dvd hQ.dvd))
  simp only [MonoidHom.comp_apply, MulChar.coe_toUnitHom] at h1 h2
  simp [splitChar, MulChar.coe_toUnitHom, h1, h2]

/-- `η` (slash by an `η`-matrix for `Q`, read in `GL₂(ℝ)`). -/
abbrev etaGL (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M) : GL (Fin 2) ℝ :=
  TauCeti.atkinLehnerGL hQ.pos (hM.isAtkinLehnerMatrix hQ)

theorem etaOp_mem (k : ℤ) (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M) (ψ : DirichletCharacter ℂ Q)
    (φ : DirichletCharacter ℂ (N / Q)) (f : cuspSpace k (splitChar hQ ψ φ)) :
    TauCeti.atkinLehnerOperatorGamma1Cusp hQ.pos hQ.dvd (hM.isAtkinLehnerMatrix hQ) k
      (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspSpace k (splitChar hQ ψ⁻¹ φ) := by
  have h := TauCeti.atkinLehnerOperatorGamma1Cusp_mem_cuspFormCharSpace hQ.pos hQ.dvd
    (hM.isAtkinLehnerMatrix hQ) f.2
  rw [toUnitHom_splitChar] at h
  have he : (hM.isAtkinLehnerMatrix hQ).isExactDivisor hQ.pos.ne' hQ.dvd = hQ := rfl
  rw [he] at h
  have hc := TauCeti.Nat.IsExactDivisor.comp_unitsInvPart hQ ψ.toUnitHom φ.toUnitHom
  show _ ∈ TauCeti.cuspFormCharSpace k (splitChar hQ ψ⁻¹ φ).toUnitHom
  rw [toUnitHom_splitChar, toUnitHom_inv_eq_inv, ← hc]
  exact h

/-- Miyake's `f ↦ f |_k η` from `𝒮_k(N, ψ φ)` to `𝒮_k(N, conj ψ · φ)` (Mathlib's slash). -/
def etaMap (k : ℤ) (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M) (ψ : DirichletCharacter ℂ Q)
    (φ : DirichletCharacter ℂ (N / Q)) :
    cuspSpace k (splitChar hQ ψ φ) →ₗ[ℂ] cuspSpace k (splitChar hQ ψ⁻¹ φ) :=
  ((TauCeti.atkinLehnerOperatorGamma1Cusp hQ.pos hQ.dvd (hM.isAtkinLehnerMatrix hQ) k).comp
    (cuspSpace k (splitChar hQ ψ φ)).subtype).codRestrict _ (etaOp_mem k hQ hM ψ φ)

theorem coe_etaMap (k : ℤ) (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M) (ψ : DirichletCharacter ℂ Q)
    (φ : DirichletCharacter ℂ (N / Q)) (f : cuspSpace k (splitChar hQ ψ φ)) :
    ⇑((etaMap k hQ hM ψ φ f : cuspSpace k (splitChar hQ ψ⁻¹ φ)) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] etaGL hQ hM :=
  rfl

theorem etaMap_injective (k : ℤ) (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M)
    (ψ : DirichletCharacter ℂ Q) (φ : DirichletCharacter ℂ (N / Q)) :
    Function.Injective (etaMap k hQ hM ψ φ) := fun f g h ↦
  Subtype.ext (TauCeti.atkinLehnerOperatorGamma1Cusp_injective hQ.pos hQ.dvd _ k
    (congrArg Subtype.val h))

/-- **Miyake, Theorem 4.6.16 (3)**, first formula, in Mathlib's normalization:
`f | η² = Q^{k-2} ψ(-1) conj φ(Q) f` for `f ∈ 𝒮_k(N, ψ φ)`. For `Q = N_q` this is
`f | η_q² = χ_q(-1) conj χ'_q(N_q) f` (Miyake's normalization has no `Q^{k-2}`); for `Q = N/N_q`
it is the corrected second formula `f | η'_q² = χ'_q(-1) conj χ_q(N/N_q) f`. -/
@[kb "miyake1989" "Theorem 4.6.16 (3), p. 168 (squares)"]
theorem eta_slash_eta (k : ℤ) (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M) (ψ : DirichletCharacter ℂ Q)
    (φ : DirichletCharacter ℂ (N / Q)) (f : cuspSpace k (splitChar hQ ψ φ)) :
    (⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] etaGL hQ hM) ∣[k] etaGL hQ hM =
      ((Q : ℂ) ^ (k - 2) * ψ (-1) * φ⁻¹ (Q : ZMod (N / Q))) •
        ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  have hf : (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ TauCeti.cuspFormCharSpace k
      (ψ.toUnitHom.comp (ZMod.unitsMap hQ.dvd) *
        φ.toUnitHom.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hQ.dvd))) := by
    rw [← toUnitHom_splitChar]; exact f.2
  have h := TauCeti.atkinLehnerOperatorGamma1Cusp_atkinLehnerOperatorGamma1Cusp_of_mem_cuspFormCharSpace
    hQ.pos hQ.dvd (hM.isAtkinLehnerMatrix hQ) hM.intCast_apply_one_one ψ.toUnitHom φ.toUnitHom hf
  have h' := congrArg (fun F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k ↦ ⇑F) h
  simp only [TauCeti.coe_atkinLehnerOperatorGamma1Cusp, FunLike.coe_smul] at h'
  rw [h']
  congr 1
  have hQu : ((ZMod.unitOfCoprime Q hQ.coprime : (ZMod (N / Q))ˣ) : ZMod (N / Q)) =
      (Q : ZMod (N / Q)) := ZMod.coe_unitOfCoprime _ _
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, MulChar.coe_toUnitHom, Units.val_neg,
    Units.val_one, hQu, mul_assoc]
  rw [MulChar.inv_apply_eq_inv']

/-- **Miyake, Theorem 4.6.16 (1)**, new part (and (2) for `Q = N/N_q`): `η` maps
`𝒮_k^0(N, ψ φ)` into `𝒮_k^0(N, conj ψ · φ)`. -/
theorem etaMap_mem_newSpace (k : ℤ) (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M)
    (ψ : DirichletCharacter ℂ Q) (φ : DirichletCharacter ℂ (N / Q))
    {f : cuspSpace k (splitChar hQ ψ φ)} (hf : f ∈ newSpace k (splitChar hQ ψ φ)) :
    etaMap k hQ hM ψ φ f ∈ newSpace k (splitChar hQ ψ⁻¹ φ) :=
  TauCeti.atkinLehnerOperatorGamma1Cusp_mem_cuspFormsNew hQ.pos hQ.dvd _ hf

/-- **Miyake, Theorem 4.6.16 (1)**, old part (and (2) for `Q = N/N_q`): `η` maps
`𝒮_k^1(N, ψ φ)` into `𝒮_k^1(N, conj ψ · φ)`. -/
theorem etaMap_mem_oldSpace (k : ℤ) (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M)
    (ψ : DirichletCharacter ℂ Q) (φ : DirichletCharacter ℂ (N / Q))
    {f : cuspSpace k (splitChar hQ ψ φ)} (hf : f ∈ oldSpace k (splitChar hQ ψ φ)) :
    etaMap k hQ hM ψ φ f ∈ oldSpace k (splitChar hQ ψ⁻¹ φ) := by
  rw [mem_oldSpace_iff] at hf ⊢
  exact TauCeti.atkinLehnerOperatorGamma1Cusp_mem_cuspFormsOld hQ.pos hQ.dvd _ hf

/-- The constant of `eta_slash_eta`: `Q^{k-2} ψ(-1) conj φ(Q)`. -/
abbrev etaSqConst (k : ℤ) (ψ : DirichletCharacter ℂ Q) (φ : DirichletCharacter ℂ (N / Q)) : ℂ :=
  (Q : ℂ) ^ (k - 2) * ψ (-1) * φ⁻¹ (Q : ZMod (N / Q))

theorem etaSqConst_ne_zero (k : ℤ) (hQ : Q ∥ N) (ψ : DirichletCharacter ℂ Q)
    (φ : DirichletCharacter ℂ (N / Q)) : etaSqConst k ψ φ ≠ 0 := by
  have hu : IsUnit (Q : ZMod (N / Q)) := (ZMod.unitOfCoprime Q hQ.coprime).isUnit
  refine mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hQ.ne_zero)) ?_) ?_
  · exact (isUnit_one.neg.map ψ).ne_zero
  · exact (hu.map φ⁻¹).ne_zero

/-- Undoing `η`: every `g ∈ 𝒮_k(N, conj ψ · φ)` is `η f` for `f = c⁻¹ (g | η)`, `c` the constant
of `eta_slash_eta` for `conj ψ · φ`. -/
theorem exists_etaMap_eq (k : ℤ) (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M)
    (ψ : DirichletCharacter ℂ Q) (φ : DirichletCharacter ℂ (N / Q))
    (g : cuspSpace k (splitChar hQ ψ⁻¹ φ)) :
    ∃ f : cuspSpace k (splitChar hQ ψ φ), etaMap k hQ hM ψ φ f = g ∧
      (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = (etaSqConst k ψ⁻¹ φ)⁻¹ •
        TauCeti.atkinLehnerOperatorGamma1Cusp hQ.pos hQ.dvd (hM.isAtkinLehnerMatrix hQ) k
          (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  have hmem : (etaSqConst k ψ⁻¹ φ)⁻¹ •
      TauCeti.atkinLehnerOperatorGamma1Cusp hQ.pos hQ.dvd (hM.isAtkinLehnerMatrix hQ) k
        (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspSpace k (splitChar hQ ψ φ) := by
    have h := etaOp_mem k hQ hM ψ⁻¹ φ g
    rw [inv_inv] at h
    exact Submodule.smul_mem _ _ h
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_, rfl⟩
  have hsq := eta_slash_eta k hQ hM ψ⁻¹ φ g
  apply DFunLike.coe_injective
  show ⇑(TauCeti.atkinLehnerOperatorGamma1Cusp hQ.pos hQ.dvd (hM.isAtkinLehnerMatrix hQ) k
    ((etaSqConst k ψ⁻¹ φ)⁻¹ • TauCeti.atkinLehnerOperatorGamma1Cusp hQ.pos hQ.dvd
      (hM.isAtkinLehnerMatrix hQ) k (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k))) = _
  rw [map_smul, FunLike.coe_smul, TauCeti.coe_atkinLehnerOperatorGamma1Cusp,
    TauCeti.coe_atkinLehnerOperatorGamma1Cusp]
  rw [hsq, smul_smul, inv_mul_cancel₀ (etaSqConst_ne_zero k hQ ψ⁻¹ φ), one_smul]

/-- **Miyake, Theorem 4.6.16 (1)** (`Q = N_q`) and **(2)** (`Q = N/N_q`), new parts: `η` induces
an isomorphism `𝒮_k^0(N, ψ φ) ≃ 𝒮_k^0(N, conj ψ · φ)`. -/
@[kb "miyake1989" "Theorem 4.6.16 (1), (2), p. 168 (new part)"]
def etaNewEquiv (k : ℤ) (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M) (ψ : DirichletCharacter ℂ Q)
    (φ : DirichletCharacter ℂ (N / Q)) :
    newSpace k (splitChar hQ ψ φ) ≃ₗ[ℂ] newSpace k (splitChar hQ ψ⁻¹ φ) :=
  LinearEquiv.ofBijective
    (((etaMap k hQ hM ψ φ).comp (newSpace k (splitChar hQ ψ φ)).subtype).codRestrict _
      fun f ↦ etaMap_mem_newSpace k hQ hM ψ φ f.2)
    ⟨fun f g h ↦ Subtype.ext (etaMap_injective k hQ hM ψ φ (congrArg Subtype.val h)), fun g ↦ by
      obtain ⟨f, hf, hfe⟩ := exists_etaMap_eq k hQ hM ψ φ g
      have hnew : f ∈ newSpace k (splitChar hQ ψ φ) := by
        show (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ TauCeti.cuspFormsNew N k
        rw [hfe]
        exact Submodule.smul_mem _ _
          (TauCeti.atkinLehnerOperatorGamma1Cusp_mem_cuspFormsNew hQ.pos hQ.dvd _ g.2)
      exact ⟨⟨f, hnew⟩, Subtype.ext hf⟩⟩

theorem coe_etaNewEquiv (k : ℤ) (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M)
    (ψ : DirichletCharacter ℂ Q) (φ : DirichletCharacter ℂ (N / Q))
    (f : newSpace k (splitChar hQ ψ φ)) :
    ⇑(((etaNewEquiv k hQ hM ψ φ f : newSpace k (splitChar hQ ψ⁻¹ φ)) :
        cuspSpace k (splitChar hQ ψ⁻¹ φ)) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ⇑((f : cuspSpace k (splitChar hQ ψ φ)) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k]
        etaGL hQ hM :=
  rfl

/-- **Miyake, Theorem 4.6.16 (1)** (`Q = N_q`) and **(2)** (`Q = N/N_q`), old parts: `η` induces
an isomorphism `𝒮_k^1(N, ψ φ) ≃ 𝒮_k^1(N, conj ψ · φ)`. -/
@[kb "miyake1989" "Theorem 4.6.16 (1), (2), p. 168 (old part)"]
def etaOldEquiv (k : ℤ) (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M) (ψ : DirichletCharacter ℂ Q)
    (φ : DirichletCharacter ℂ (N / Q)) :
    oldSpace k (splitChar hQ ψ φ) ≃ₗ[ℂ] oldSpace k (splitChar hQ ψ⁻¹ φ) :=
  LinearEquiv.ofBijective
    (((etaMap k hQ hM ψ φ).comp (oldSpace k (splitChar hQ ψ φ)).subtype).codRestrict _
      fun f ↦ etaMap_mem_oldSpace k hQ hM ψ φ f.2)
    ⟨fun f g h ↦ Subtype.ext (etaMap_injective k hQ hM ψ φ (congrArg Subtype.val h)), fun g ↦ by
      obtain ⟨f, hf, hfe⟩ := exists_etaMap_eq k hQ hM ψ φ g
      have hold : f ∈ oldSpace k (splitChar hQ ψ φ) := by
        rw [mem_oldSpace_iff, hfe]
        refine Submodule.smul_mem _ _ ?_
        have := (mem_oldSpace_iff k (splitChar hQ ψ⁻¹ φ)
          (g : cuspSpace k (splitChar hQ ψ⁻¹ φ))).mp g.2
        exact TauCeti.atkinLehnerOperatorGamma1Cusp_mem_cuspFormsOld hQ.pos hQ.dvd _ this
      exact ⟨⟨f, hold⟩, Subtype.ext hf⟩⟩

theorem coe_etaOldEquiv (k : ℤ) (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M)
    (ψ : DirichletCharacter ℂ Q) (φ : DirichletCharacter ℂ (N / Q))
    (f : oldSpace k (splitChar hQ ψ φ)) :
    ⇑(((etaOldEquiv k hQ hM ψ φ f : oldSpace k (splitChar hQ ψ⁻¹ φ)) :
        cuspSpace k (splitChar hQ ψ⁻¹ φ)) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ⇑((f : cuspSpace k (splitChar hQ ψ φ)) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k]
        etaGL hQ hM :=
  rfl

/-- The value of `ψ φ` at the diamond label of `γ ∈ Γ₀(N)` with lower-right entry `d`,
`d ≡ 1 mod Q`, `Q d ≡ 1 mod N/Q`, is `conj φ(Q)`. -/
theorem splitChar_label_eq (hQ : Q ∥ N) (ψ : DirichletCharacter ℂ Q)
    (φ : DirichletCharacter ℂ (N / Q)) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N)
    (hd1 : ((γ 1 1 : ℤ) : ZMod Q) = 1)
    (hd2 : (Q : ZMod (N / Q)) * ((γ 1 1 : ℤ) : ZMod (N / Q)) = 1) :
    (((splitChar hQ ψ φ).toUnitHom ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩) : ℂˣ) : ℂ) =
      φ⁻¹ (Q : ZMod (N / Q)) := by
  rw [MulChar.coe_toUnitHom, MonoidHom.coe_toHomUnits, Gamma0Map_apply]
  have hcop : IsCoprime (γ 1 1) (N : ℤ) := by
    obtain ⟨c, hc⟩ := mem_Gamma0_iff_dvd.mp hγ
    have hdet := Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
    exact ⟨γ 0 0, -(γ 0 1 * c), by rw [hc] at hdet; linear_combination hdet⟩
  simp only [splitChar, MulChar.coeToFun_mul, Pi.mul_apply,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop]
  rw [hd1, MulChar.map_one, one_mul, MulChar.inv_apply_eq_inv']
  have h := congrArg φ hd2
  rw [map_mul, MulChar.map_one] at h
  exact (eq_inv_of_mul_eq_one_right h)

/-- The value of `1 · φ` at the diamond label of `γ ∈ Γ₀(N)` with `Q d ≡ 1 mod N/Q`, `d` the
lower-right entry of `γ`, is `conj φ(Q)`. -/
theorem splitChar_label_one (hQ : Q ∥ N) (φ : DirichletCharacter ℂ (N / Q)) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) (hd2 : (Q : ZMod (N / Q)) * ((γ 1 1 : ℤ) : ZMod (N / Q)) = 1) :
    (((splitChar hQ 1 φ).toUnitHom ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩) : ℂˣ) : ℂ) =
      φ⁻¹ (Q : ZMod (N / Q)) := by
  rw [MulChar.coe_toUnitHom, MonoidHom.coe_toHomUnits, Gamma0Map_apply]
  have hcop : IsCoprime (γ 1 1) (N : ℤ) := by
    obtain ⟨c, hc⟩ := mem_Gamma0_iff_dvd.mp hγ
    have hdet := Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
    exact ⟨γ 0 0, -(γ 0 1 * c), by rw [hc] at hdet; linear_combination hdet⟩
  have hcopQ : IsCoprime (γ 1 1) (Q : ℤ) :=
    hcop.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hQ.dvd)
  simp only [splitChar, MulChar.coeToFun_mul, Pi.mul_apply,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop]
  have hunit : IsUnit ((γ 1 1 : ℤ) : ZMod Q) := by
    rw [← ZMod.coe_unitOfIsCoprime _ hcopQ]; exact Units.isUnit _
  rw [MulChar.one_apply hunit, one_mul, MulChar.inv_apply_eq_inv']
  have h := congrArg φ hd2
  rw [map_mul, MulChar.map_one] at h
  exact (eq_inv_of_mul_eq_one_right h)

/-- **Miyake, Theorem 4.6.16 (3)**, third formula: `f | η_q η'_q = conj χ'_q(N_q) f | ω_N`, here
for `η = η_q` an `η`-matrix for `Q` and `η' = η'_q` one for `N/Q`, `f ∈ 𝒮_k(N, ψ φ)`: both sides
are slashes by matrices of determinant `N`, so the normalizations agree. -/
@[kb "miyake1989" "Theorem 4.6.16 (3), p. 168 (η_q η'_q)"]
theorem eta_slash_eta' (k : ℤ) (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M)
    (hM' : IsEtaMatrix N (N / Q) M') (ψ : DirichletCharacter ℂ Q)
    (φ : DirichletCharacter ℂ (N / Q)) (f : cuspSpace k (splitChar hQ ψ φ)) :
    (⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] etaGL hQ hM) ∣[k]
        etaGL (hQ.div (NeZero.ne N)) hM' =
      φ⁻¹ (Q : ZMod (N / Q)) • (⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] omega N) := by
  obtain ⟨γ, hγ, heq, hd1, hd2⟩ := hM.exists_mul_eq_fricke hQ hM'
  have hGL : etaGL hQ hM * etaGL (hQ.div (NeZero.ne N)) hM' = mapGL ℝ γ * omega N := by
    refine Units.ext ?_
    ext i j
    have h := congrFun (congrFun heq i) j
    simp only [Units.val_mul, TauCeti.coe_atkinLehnerGL, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.map_apply, Matrix.SpecialLinearGroup.mapGL_coe_matrix, TauCeti.coe_frickeGL] at h ⊢
    fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> exact_mod_cast h
  rw [← SlashAction.slash_mul, hGL, SlashAction.slash_mul,
    (TauCeti.mem_cuspFormCharSpace_iff_nebentypus k _ _).mp f.2 ⟨γ, hγ⟩,
    ModularForm.smul_slash_of_det_pos k TauCeti.val_det_frickeGL_pos, splitChar_label_eq hQ ψ φ hγ hd1 hd2]

/-- **Erratum to Miyake, Theorem 4.6.16 (3)** (`f | η'_q² = χ'_q(-1) χ_q(N/N_q) f`, p. 168): for
`Q = N/N_q`, `ψ = χ'_q`, `φ = χ_q`, the printed formula reads `f | η² = Q^{k-2} ψ(-1) φ(Q) f`
here. For `f ≠ 0` it holds if and only if `φ(Q)² = 1`; the correct constant has `conj φ(Q)`
(`eta_slash_eta`). -/
@[kb "miyake1989" "Theorem 4.6.16 (3), p. 168 (erratum: η'_q²)"]
theorem eta_slash_eta_eq_book_iff (k : ℤ) (hQ : Q ∥ N) (hM : IsEtaMatrix N Q M)
    (ψ : DirichletCharacter ℂ Q) (φ : DirichletCharacter ℂ (N / Q))
    {f : cuspSpace k (splitChar hQ ψ φ)} (hf : f ≠ 0) :
    (⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∣[k] etaGL hQ hM) ∣[k] etaGL hQ hM =
      ((Q : ℂ) ^ (k - 2) * ψ (-1) * φ (Q : ZMod (N / Q))) •
        ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ↔ φ (Q : ZMod (N / Q)) ^ 2 = 1 := by
  rw [eta_slash_eta]
  have hu : IsUnit (Q : ZMod (N / Q)) := (ZMod.unitOfCoprime Q hQ.coprime).isUnit
  have hφ : φ (Q : ZMod (N / Q)) ≠ 0 := (hu.map φ).ne_zero
  have hψ : ψ (-1) ≠ 0 := (isUnit_one.neg.map ψ).ne_zero
  have hQ0 : (Q : ℂ) ^ (k - 2) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hQ.ne_zero)
  have hf' : ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ≠ 0 := by
    intro h0
    exact hf (Subtype.ext (DFunLike.coe_injective (by simpa using h0)))
  have key : ∀ a b : ℂ, a • ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      b • ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ↔ a = b :=
    fun a b ↦ ⟨fun h ↦ smul_left_injective ℂ hf' h, fun h ↦ h ▸ rfl⟩
  rw [key, MulChar.inv_apply_eq_inv']
  constructor
  · intro h
    have h2 : (φ (Q : ZMod (N / Q)))⁻¹ = φ (Q : ZMod (N / Q)) :=
      mul_left_cancel₀ (mul_ne_zero hQ0 hψ) h
    have h3 := mul_inv_cancel₀ hφ
    rw [h2] at h3
    rw [sq]
    exact h3
  · intro h
    have h2 : (φ (Q : ZMod (N / Q)))⁻¹ = φ (Q : ZMod (N / Q)) :=
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h)
    rw [h2]

end ModularFormsKB.Miyake.Wave9
