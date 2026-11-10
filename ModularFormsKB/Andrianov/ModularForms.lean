import ModularFormsKB.Andrianov.ThetaSeries
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Andrianov–Zhuravlev, Chapter 2, §2–§3: Siegel modular forms of integer weight

A. N. Andrianov and V. G. Zhuravlev, *Modular Forms and Hecke Operators* (`andrianovzhuravlev1995`), Chapter 2,
pdf pp. 69–76.

* Finite characters, the slash operator `(F|_k M)(Z) = det(CZ + D)^{-k} F(M⟨Z⟩)`.
* `IsSiegelModularForm n k K χ F`: the three conditions of §2.2 (holomorphy in the `(n)` variables, the functional
  equation (2.4), boundedness of `F|_k M` on `H_1(ε)` when `n = 1`), and the space `𝔐_k(K, χ)` as a `ℂ`-submodule.
* Theorem 2.2 (theta series of even rank are modular forms), the Koecher principle and Fourier expansion (Theorem 3.1)
  as named statements.
* The triangular subgroup `Γ_0^n = {C = 0}` (3.1), the Siegel operator `Φ` ((3.50)–(3.51)) and cusp forms (3.67).

Half-integral weight (§2.3) needs the automorphy factor `j^{(2)}` of Chapter 1 (4.37), not formalized here.
-/

open Matrix Complex Filter

namespace ModularFormsKB.Andrianov

variable {n : ℕ}

/-- A finite character of a group `K`: a homomorphism into the roots of unity of some fixed order. -/
def IsFiniteCharacter {K : Type*} [Group K] (χ : K →* ℂˣ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∀ M, χ M ^ m = 1

/-- `det(CZ + D)` for `M ∈ Γ_n`. -/
noncomputable def jdet (M : SiegelModularGroup n) (Z : SiegelSpace n) : ℂ :=
  (jmat (SiegelModularGroup.toReal M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) Z).det

/-- The slash operator of integer weight `k`: `(F|_k M)(Z) = det(CZ + D)^{-k} F(M⟨Z⟩)`. -/
noncomputable def slash (k : ℤ) (M : SiegelModularGroup n) (F : SiegelSpace n → ℂ) : SiegelSpace n → ℂ :=
  fun Z => jdet M Z ^ (-k) * F (M • Z)

/-- **Andrianov–Zhuravlev, Chapter 2, §2.2.** `F` is a modular form of degree `n`, weight `k` and character `χ`
for `K`: (1) holomorphic on `H_n` in the `(n)` variables; (2) `det(CZ + D)^{-k} F(M⟨Z⟩) = χ(M) F(Z)` for `M ∈ K`
(2.4); (3) if `n = 1`, every `F|_k M`, `M ∈ Γ_1`, is bounded on every `H_1(ε)`, `ε > 0`. -/
@[kb "andrianovzhuravlev1995" "Chapter 2, §2.2, (2.4), p. 70"]
structure IsSiegelModularForm (k : ℤ) (K : Subgroup (SiegelModularGroup n)) (χ : K →* ℂˣ)
    (F : SiegelSpace n → ℂ) : Prop where
  holo : IsHolomorphicOnSiegel F
  transf : ∀ (M : K) (Z : SiegelSpace n), slash k (M : SiegelModularGroup n) F Z = (χ M : ℂ) * F Z
  bdd : n = 1 → ∀ (M : SiegelModularGroup n) (ε : ℝ), 0 < ε →
    ∃ C : ℝ, ∀ Z ∈ siegelSetEps n ε, ‖slash k M F Z‖ ≤ C

/-- **Andrianov–Zhuravlev, Chapter 2, §2.2.** The space `𝔐_k(K, χ)` of modular forms of degree `n`, weight `k` and
character `χ` for `K` (the book takes `K` a congruence subgroup and `χ` finite; the space makes sense for any). -/
@[kb "andrianovzhuravlev1995" "Chapter 2, §2.2, p. 70"]
noncomputable def siegelModularForms (n : ℕ) (k : ℤ) (K : Subgroup (SiegelModularGroup n)) (χ : K →* ℂˣ) :
    Submodule ℂ (SiegelSpace n → ℂ) where
  carrier := {F | IsSiegelModularForm k K χ F}
  add_mem' {F G} hF hG := by
    refine ⟨hF.holo.add hG.holo, fun M Z => ?_, fun h1 M ε hε => ?_⟩
    · have h1 := hF.transf M Z
      have h2 := hG.transf M Z
      simp only [slash, Pi.add_apply] at h1 h2 ⊢
      rw [mul_add, h1, h2, mul_add]
    · obtain ⟨C₁, hC₁⟩ := hF.bdd h1 M ε hε
      obtain ⟨C₂, hC₂⟩ := hG.bdd h1 M ε hε
      refine ⟨C₁ + C₂, fun Z hZ => ?_⟩
      have e : slash k M (F + G) Z = slash k M F Z + slash k M G Z := by
        simp only [slash, Pi.add_apply, mul_add]
      rw [e]
      exact (norm_add_le _ _).trans (add_le_add (hC₁ Z hZ) (hC₂ Z hZ))
  zero_mem' := by
    refine ⟨isHolomorphicOnSiegel_zero, fun M Z => by simp [slash], fun _ M ε _ => ⟨0, fun Z _ => by simp [slash]⟩⟩
  smul_mem' c F hF := by
    refine ⟨hF.holo.const_smul c, fun M Z => ?_, fun h1 M ε hε => ?_⟩
    · have h1 := hF.transf M Z
      simp only [slash, Pi.smul_apply, smul_eq_mul] at h1 ⊢
      rw [mul_left_comm, h1]; ring
    · obtain ⟨C, hC⟩ := hF.bdd h1 M ε hε
      refine ⟨‖c‖ * C, fun Z hZ => ?_⟩
      have e : slash k M (c • F) Z = c * slash k M F Z := by
        simp only [slash, Pi.smul_apply, smul_eq_mul]; ring
      rw [e, norm_mul]
      exact mul_le_mul_of_nonneg_left (hC Z hZ) (norm_nonneg _)

/-- **Andrianov–Zhuravlev, Chapter 2, Theorem 2.2 (even `m = 2k`)**, named statement: for `Q ∈ A_m⁺` of level `q`,
the theta series `θ^n(Z, Q)` lies in `𝔐_k(Γ_0^n(q), χ_Q)`, where `χ_Q(M) = χ(det D)` for the Dirichlet character
`χ` of Theorem 4.10 of Chapter 1 (characterized by (4.32)–(4.34)). -/
@[kb "andrianovzhuravlev1995" "Chapter 2, Theorem 2.2, p. 71"]
structure ThetaSeriesModularForm (m n k : ℕ) : Prop where
  mem : m = 2 * k → ∀ (Q : Matrix (Fin m) (Fin m) ℤ) (q : ℕ), Q ∈ evenPD m → IsLevel Q q →
    ∀ χ : DirichletCharacter ℂ q,
      χ (-1) = (-1) ^ k →
      (∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ q → χ p = (jacobiSym ((-1) ^ k * Q.det) p : ℂ)) →
      (Odd q → χ 2 = (2 : ℂ)⁻¹ ^ k * ∑ t : Fin m → ZMod 2,
        Complex.exp (Real.pi * Complex.I *
          ((∑ i, ∑ j, (Q i j : ℂ) * ((t i).val : ℂ) * ((t j).val : ℂ)) / 2))) →
      ∃ χQ : gammaZero n q →* ℂˣ,
        (∀ M : gammaZero n q, (χQ M : ℂ) = χ ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ).toBlocks₂₂.det)) ∧
        thetaSeries Q ∈ siegelModularForms n (k : ℤ) (gammaZero n q) χQ

/-- **Andrianov–Zhuravlev, Chapter 2, (3.1).** The triangular subgroup `Γ_0^n = {M ∈ Γ_n ; C = 0}`. -/
@[kb "andrianovzhuravlev1995" "Chapter 2, (3.1), p. 71"]
def triangularSubgroup (n : ℕ) : Subgroup (SiegelModularGroup n) := gammaZero n 0

theorem mem_triangularSubgroup_iff (M : SiegelModularGroup n) :
    M ∈ triangularSubgroup n ↔ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ).toBlocks₂₁ = 0 := by
  show (∀ i j, ((0 : ℕ) : ℤ) ∣ _) ↔ _
  simp only [Nat.cast_zero, zero_dvd_iff]
  exact ⟨fun h => Matrix.ext h, fun h i j => by rw [h]; rfl⟩

/-- The integral matrix `T(S)`, `S` integral symmetric, as an element of `Γ_n`. -/
def SiegelModularGroup.T (S : Matrix (Fin n) (Fin n) ℤ) (hS : Sᵀ = S) : SiegelModularGroup n :=
  ⟨Tmat S, Tmat_mem hS⟩

/-- **Andrianov–Zhuravlev, Chapter 2, §3.1, (3.2).** A modular form of character `χ` for a subgroup `T ⊆ Γ_0^n`:
holomorphic, `F(M⟨Z⟩) = χ(M) F(Z)` for `M ∈ T`, and bounded on every `H_1(ε)` if `n = 1`. -/
@[kb "andrianovzhuravlev1995" "Chapter 2, (3.2), p. 71"]
structure IsTriangularModularForm (T : Subgroup (SiegelModularGroup n)) (χ : T →* ℂˣ) (F : SiegelSpace n → ℂ) :
    Prop where
  holo : IsHolomorphicOnSiegel F
  transf : ∀ (M : T) (Z : SiegelSpace n), F ((M : SiegelModularGroup n) • Z) = (χ M : ℂ) * F Z
  bdd : n = 1 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ Z ∈ siegelSetEps n ε, ‖F Z‖ ≤ C

/-- **Andrianov–Zhuravlev, Chapter 2, Theorem 3.1 (Koecher effect, Fourier expansion)**, named statement. Let
`T ⊆ Γ_0^n` have finite index, `χ` a finite character of `T`, `F ∈ 𝔐(T, χ)`, and `q ≥ 1` with `T(qS) ∈ T` and
`χ(T(qS)) = 1` for all integral symmetric `S` (3.6) (the book takes the least such `q`; the expansion holds for every
such `q`). Then `F(Z) = ∑_{R ∈ A_n} f(R) e{q⁻¹ R Z}` (3.5), absolutely convergent on `H_n` and uniformly on every
`H_n(ε)`; in particular `F` is bounded on `H_n(ε)`. Uniform convergence is recorded as a summable majorant on
`H_n(ε)`. -/
@[kb "andrianovzhuravlev1995" "Chapter 2, Theorem 3.1, p. 72"]
structure KoecherFourierExpansion (n : ℕ) : Prop where
  expansion : ∀ (T : Subgroup (SiegelModularGroup n)), T ≤ triangularSubgroup n →
    (T.subgroupOf (triangularSubgroup n)).FiniteIndex →
    ∀ (χ : T →* ℂˣ), IsFiniteCharacter χ → ∀ F : SiegelSpace n → ℂ, IsTriangularModularForm T χ F →
    ∀ q : ℕ, 0 < q → (∀ (S : Matrix (Fin n) (Fin n) ℤ) (hS : Sᵀ = S),
        ∃ h : SiegelModularGroup.T ((q : ℤ) • S) (by rw [transpose_smul, hS]) ∈ T, χ ⟨_, h⟩ = 1) →
    ∃ f : evenPSD n → ℂ,
      (∀ Z : SiegelSpace n, HasSum (fun R : evenPSD n => f R * eTr (((q : ℂ)⁻¹ • zc (R : Matrix (Fin n) (Fin n) ℤ)) * (Z : Matrix (Fin n) (Fin n) ℂ)))
        (F Z)) ∧
      (∀ Z : SiegelSpace n, Summable fun R : evenPSD n => ‖f R * eTr (((q : ℂ)⁻¹ • zc (R : Matrix (Fin n) (Fin n) ℤ)) * (Z : Matrix (Fin n) (Fin n) ℂ))‖) ∧
      (∀ ε : ℝ, 0 < ε → ∃ u : evenPSD n → ℝ, Summable u ∧ ∀ R, ∀ Z ∈ siegelSetEps n ε,
        ‖f R * eTr (((q : ℂ)⁻¹ • zc (R : Matrix (Fin n) (Fin n) ℤ)) * (Z : Matrix (Fin n) (Fin n) ℂ))‖ ≤ u R)

/-- The point `Z_λ = (Z 0; 0 iλ)` of `H_{r+1}` for `Z ∈ H_r` (Chapter 2, (3.57)), as a matrix indexed by
`Fin (r + 1)` (the new coordinate is the last one). -/
noncomputable def zLambda {r : ℕ} (Z : Matrix (Fin r) (Fin r) ℂ) (t : ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  (fromBlocks Z 0 0 (fun _ _ => (t : ℂ) * Complex.I) : Matrix (Fin r ⊕ Fin 1) (Fin r ⊕ Fin 1) ℂ).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

/-- `F` extended by zero off `H_n`. -/
noncomputable def extendSiegel (F : SiegelSpace n → ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  open Classical in if h : Z ∈ siegelSet n then F ⟨Z, h⟩ else 0

/-- **Andrianov–Zhuravlev, Chapter 2, (3.50)–(3.52).** The Siegel operator: `(F|Φ)(Z) = lim_{λ → +∞} F(Z_λ)` for
`F` on `H_{r+1}` and `Z ∈ H_r` (for `r = 0`, `(3.51)`: `F|Φ = lim F(iλ)`, a function on the one-point `H_0`). -/
@[kb "andrianovzhuravlev1995" "Chapter 2, (3.50)–(3.52), p. 72–73"]
noncomputable def siegelPhi {r : ℕ} (F : SiegelSpace (r + 1) → ℂ) (Z : SiegelSpace r) : ℂ :=
  limUnder atTop fun t : ℝ => extendSiegel F (zLambda (Z : Matrix (Fin r) (Fin r) ℂ) t)

/-- **Andrianov–Zhuravlev, Chapter 2, (3.67) (integer weight).** A cusp form: a modular form `F ∈ 𝔐_k(K, χ)` with
`(F|_k M)|Φ = 0` for every `M ∈ Γ_n`. -/
@[kb "andrianovzhuravlev1995" "Chapter 2, (3.67), p. 75"]
def IsSiegelCuspForm {r : ℕ} (k : ℤ) (K : Subgroup (SiegelModularGroup (r + 1))) (χ : K →* ℂˣ)
    (F : SiegelSpace (r + 1) → ℂ) : Prop :=
  F ∈ siegelModularForms (r + 1) k K χ ∧ ∀ M : SiegelModularGroup (r + 1), siegelPhi (slash k M F) = 0

end ModularFormsKB.Andrianov
