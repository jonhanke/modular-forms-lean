import ModularFormsKB.Andrianov.ModularGroup
import ModularFormsKB.Andrianov.Holomorphic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Andrianov–Zhuravlev, Chapter 1: theta series of degree `n`

A. N. Andrianov and V. G. Zhuravlev, *Modular Forms and Hecke Operators* (`andrianovzhuravlev1995`), Chapter 1,
§1 and §3–§4 (pdf pp. 13–47).

* `repNum Q A = r(Q, A)`, the number of integral `N` with `ᵗN Q N = A` ((1.5)); Proposition 1.1
  (`repNum_equiv`): it depends only on the `GL(ℤ)`-classes of `Q` and `A`.
* `evenPSD n = A_n` and `evenPD n = A_n⁺` ((1.7), (1.8)): even symmetric integral semidefinite / definite matrices.
* `siegelSetEps n ε = H_n(ε) = {Z ∈ H_n ; Y ≥ εE}` (1.11).
* `thetaSeries Q Z = θ^n(Z, Q) = ∑_{N ∈ M_{m,n}(ℤ)} e{ᵗN Q N Z}` (1.13), `e{T} = exp(πi σ(T))` (3.23).
* Proposition 1.3 (absolute uniform convergence on `H_n(ε)`), Theorem 1.4 (holomorphy and boundedness), the level
  of `Q`, and the functional equation on `Γ_0^n(q)` (Theorem 3.13 with Theorem 4.10 for even `m`), as statements.

The matrix `Q` is `m × m` (`Fin m`), `Z` is `n × n` (`Fin n`); the book's `1, …, m` become `0, …, m - 1`.
-/

open Matrix Complex

namespace ModularFormsKB.Andrianov

variable {m n : ℕ}

/-- An even symmetric integral matrix: symmetric, with even diagonal (the matrix of an integral quadratic form,
(1.3)). -/
def IsEvenSymm (A : Matrix (Fin n) (Fin n) ℤ) : Prop := Aᵀ = A ∧ ∀ i, Even (A i i)

/-- **Andrianov–Zhuravlev (1.7).** `A_n`: even symmetric integral positive semidefinite `n × n` matrices. -/
@[kb "andrianovzhuravlev1995" "Chapter 1, (1.7), p. 15"]
def evenPSD (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℤ) :=
  {A | IsEvenSymm A ∧ (A.map (Int.cast : ℤ → ℝ)).PosSemidef}

/-- **Andrianov–Zhuravlev (1.8).** `A_n⁺ = {A ∈ A_n ; A > 0}`. -/
@[kb "andrianovzhuravlev1995" "Chapter 1, (1.8), p. 15"]
def evenPD (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℤ) :=
  {A | IsEvenSymm A ∧ (A.map (Int.cast : ℤ → ℝ)).PosDef}

/-- **Andrianov–Zhuravlev (1.5).** `r(Q, A)`: the number of integral `m × n` matrices `N` with `ᵗN Q N = A`
(`0` if there are infinitely many; for `Q > 0` there are finitely many, Problem 1.2). -/
@[kb "andrianovzhuravlev1995" "Chapter 1, (1.5), p. 14"]
noncomputable def repNum (Q : Matrix (Fin m) (Fin m) ℤ) (A : Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  Nat.card {N : Matrix (Fin m) (Fin n) ℤ // Nᵀ * Q * N = A}

/-- **Andrianov–Zhuravlev, Proposition 1.1.** `r(Q, A)` depends only on the `ℤ`-equivalence classes of `Q` and `A`:
`r(ᵗV Q V, ᵗV' A V') = r(Q, A)` for `V ∈ GL_m(ℤ)`, `V' ∈ GL_n(ℤ)`. -/
@[kb "andrianovzhuravlev1995" "Chapter 1, Proposition 1.1, p. 14"]
theorem repNum_equiv (Q : Matrix (Fin m) (Fin m) ℤ) (A : Matrix (Fin n) (Fin n) ℤ)
    (V : (Matrix (Fin m) (Fin m) ℤ)ˣ) (V' : (Matrix (Fin n) (Fin n) ℤ)ˣ) :
    repNum ((V : Matrix (Fin m) (Fin m) ℤ)ᵀ * Q * (V : Matrix (Fin m) (Fin m) ℤ))
      ((V' : Matrix (Fin n) (Fin n) ℤ)ᵀ * A * (V' : Matrix (Fin n) (Fin n) ℤ)) = repNum Q A := by
  -- the bijection `N ↦ V N W'` (`W' = V'⁻¹`) from solutions of the transformed problem to those of `(Q, A)`
  obtain ⟨W, hVW, hWV⟩ : ∃ W : Matrix (Fin m) (Fin m) ℤ,
      (V : Matrix (Fin m) (Fin m) ℤ) * W = 1 ∧ W * (V : Matrix (Fin m) (Fin m) ℤ) = 1 :=
    ⟨↑(V⁻¹), by simp, by simp⟩
  obtain ⟨W', hVW', hWV'⟩ : ∃ W : Matrix (Fin n) (Fin n) ℤ,
      (V' : Matrix (Fin n) (Fin n) ℤ) * W = 1 ∧ W * (V' : Matrix (Fin n) (Fin n) ℤ) = 1 :=
    ⟨↑(V'⁻¹), by simp, by simp⟩
  generalize (V : Matrix (Fin m) (Fin m) ℤ) = P at *
  generalize (V' : Matrix (Fin n) (Fin n) ℤ) = P' at *
  have a1 : ∀ X : Matrix (Fin m) (Fin n) ℤ, P * (W * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hVW, Matrix.one_mul]
  have a2 : ∀ X : Matrix (Fin m) (Fin n) ℤ, W * (P * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hWV, Matrix.one_mul]
  have b1 : ∀ X : Matrix (Fin m) (Fin n) ℤ, Wᵀ * (Pᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← transpose_mul, hVW, transpose_one, Matrix.one_mul]
  have b2 : ∀ X : Matrix (Fin m) (Fin n) ℤ, Pᵀ * (Wᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← transpose_mul, hWV, transpose_one, Matrix.one_mul]
  have b3 : ∀ X : Matrix (Fin n) (Fin n) ℤ, W'ᵀ * (P'ᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← transpose_mul, hVW', transpose_one, Matrix.one_mul]
  unfold repNum
  refine Nat.card_congr
    { toFun := fun N => ⟨P * N.1 * W', ?_⟩
      invFun := fun N => ⟨W * N.1 * P', ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hN := N.2
    have : (P * N.1 * W')ᵀ * Q * (P * N.1 * W') = W'ᵀ * (N.1ᵀ * (Pᵀ * Q * P) * N.1) * W' := by
      simp only [transpose_mul, Matrix.mul_assoc]
    rw [this, hN]
    simp only [Matrix.mul_assoc, b3, hVW', Matrix.mul_one]
  · have hN := N.2
    have : (W * N.1 * P')ᵀ * (Pᵀ * Q * P) * (W * N.1 * P') = P'ᵀ * (N.1ᵀ * Q * N.1) * P' := by
      simp only [transpose_mul, Matrix.mul_assoc, b1, a1]
    rw [this, hN]
  · intro N
    apply Subtype.ext
    simp only [Matrix.mul_assoc, a2, hWV', Matrix.mul_one]
  · intro N
    apply Subtype.ext
    simp only [Matrix.mul_assoc, a1, hVW', Matrix.mul_one]

/-- **Andrianov–Zhuravlev (3.23).** `e{T} = exp(πi σ(T))`, `σ` the trace. -/
noncomputable def eTr {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ) : ℂ := Complex.exp (Real.pi * Complex.I * T.trace)

/-- Integral matrices viewed over `ℂ`. -/
abbrev zc {ι κ : Type*} (N : Matrix ι κ ℤ) : Matrix ι κ ℂ := N.map (Int.cast : ℤ → ℂ)

/-- The term `e{Q[N] Z} = exp(πi σ(ᵗN Q N Z))` of the theta series. -/
noncomputable def thetaTerm (Q : Matrix (Fin m) (Fin m) ℤ) (Z : Matrix (Fin n) (Fin n) ℂ)
    (N : Matrix (Fin m) (Fin n) ℤ) : ℂ :=
  eTr ((zc N)ᵀ * zc Q * zc N * Z)

/-- **Andrianov–Zhuravlev (1.13).** The theta series of degree `n` of `Q`:
`θ^n(Z, Q) = ∑_{N ∈ M_{m,n}} e{ᵗN Q N Z}`. -/
@[kb "andrianovzhuravlev1995" "Chapter 1, (1.13), p. 16"]
noncomputable def thetaSeries (Q : Matrix (Fin m) (Fin m) ℤ) (Z : SiegelSpace n) : ℂ :=
  ∑' N : Matrix (Fin m) (Fin n) ℤ, thetaTerm Q Z N

/-- **Andrianov–Zhuravlev (1.11).** `H_n(ε) = {Z = X + iY ∈ H_n ; Y ≥ εE_n}`. -/
@[kb "andrianovzhuravlev1995" "Chapter 1, (1.11), p. 16"]
def siegelSetEps (n : ℕ) (ε : ℝ) : Set (SiegelSpace n) := {Z | (Z.im - ε • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef}

/-- A product of one-variable summable nonnegative families over a finite power is summable. -/
theorem summable_pi_prod_aux {α : Type*} (F : α → ℝ) (hF0 : ∀ a, 0 ≤ F a) (hF : Summable F) :
    ∀ k : ℕ, Summable (fun x : Fin k → α => ∏ i, F (x i)) := by
  intro k
  induction k with
  | zero => exact Summable.of_finite
  | succ k ih =>
    have h := hF.mul_of_nonneg ih hF0 (fun x => Finset.prod_nonneg fun i _ => hF0 _)
    let e : α × (Fin k → α) ≃ (Fin (k + 1) → α) :=
      { toFun := fun p => Fin.cons p.1 p.2
        invFun := fun x => (x 0, Fin.tail x)
        left_inv := fun p => by simp
        right_inv := fun x => by simp }
    refine (e.summable_iff (f := fun x : Fin (k + 1) → α => ∏ i, F (x i))).1 (h.congr fun p => ?_)
    simp [e, Fin.prod_univ_succ]

/-- The Gaussian `t ↦ exp(-a t²)` is summable over `ℤ` for `a > 0`. -/
theorem summable_gauss_int {a : ℝ} (ha : 0 < a) :
    Summable (fun t : ℤ => Real.exp (-a * (t : ℝ) ^ 2)) := by
  have hr : Real.exp (-a) < 1 := by simpa using Real.exp_lt_exp.2 (show -a < 0 by linarith)
  have hg : Summable (fun n : ℕ => Real.exp (-a) ^ n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le hr
  have hb : ∀ t : ℤ, Real.exp (-a * (t : ℝ) ^ 2) ≤ Real.exp (-a) ^ t.natAbs := by
    intro t
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have h1 : (t.natAbs : ℝ) ≤ (t : ℝ) ^ 2 := by
      have h3 : (t.natAbs : ℤ) ≤ t ^ 2 := by rw [Int.natCast_natAbs, ← sq_abs t]; exact Int.le_self_sq _
      calc (t.natAbs : ℝ) = ((t.natAbs : ℤ) : ℝ) := (Int.cast_natCast _).symm
        _ ≤ ((t ^ 2 : ℤ) : ℝ) := Int.cast_le.2 h3
        _ = (t : ℝ) ^ 2 := by push_cast; ring
    nlinarith
  refine Summable.of_nonneg_of_le (fun t => (Real.exp_pos _).le) hb ?_
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa using hg
  · simpa using hg

/-- A real positive definite matrix is coercive: `c |x|² ≤ xᵀ Q x` for some `c > 0` (compactness of the sphere). -/
theorem posDef_coercive {k : ℕ} {Q : Matrix (Fin k) (Fin k) ℝ} (hQ : Q.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin k → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Q *ᵥ x) := by
  by_cases hx : ∃ x : Fin k → ℝ, x ≠ 0
  · let S : Set (EuclideanSpace ℝ (Fin k)) := Metric.sphere 0 1
    let f : EuclideanSpace ℝ (Fin k) → ℝ := fun y => (y : Fin k → ℝ) ⬝ᵥ (Q *ᵥ (y : Fin k → ℝ))
    have hf : Continuous f := by
      simp only [f, dotProduct, mulVec]
      fun_prop
    have hnorm : ∀ x : Fin k → ℝ, ‖WithLp.toLp 2 x‖ ^ 2 = x ⬝ᵥ x := by
      intro x
      rw [EuclideanSpace.norm_sq_eq]
      simp [dotProduct, sq]
    have hne : S.Nonempty := by
      obtain ⟨x, hx⟩ := hx
      have : WithLp.toLp 2 x ≠ 0 := fun h => hx (by simpa using congrArg WithLp.ofLp h)
      refine ⟨(‖WithLp.toLp 2 x‖⁻¹) • WithLp.toLp 2 x, ?_⟩
      simp [S, norm_smul, norm_ne_zero_iff.2 this]
    obtain ⟨y0, hy0, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin k)) 1).exists_isMinOn hne
      hf.continuousOn
    have hy0ne : (y0 : Fin k → ℝ) ≠ 0 := by
      intro h
      have : y0 = 0 := by ext i; simpa using congrFun h i
      simp [this] at hy0
    have hpos : 0 < f y0 := by
      have := hQ.dotProduct_mulVec_pos hy0ne
      simpa [f] using this
    refine ⟨f y0, hpos, fun x => ?_⟩
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hxn : 0 < ‖WithLp.toLp 2 x‖ := by
        apply norm_pos_iff.2
        intro h; exact hx0 (by simpa using congrArg WithLp.ofLp h)
      set r := ‖WithLp.toLp 2 x‖ with hr
      have hy : r⁻¹ • WithLp.toLp 2 x ∈ S := by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hxn)]
        exact inv_mul_cancel₀ hxn.ne'
      have h1 := hmin hy
      have h2 : f (r⁻¹ • WithLp.toLp 2 x) = r⁻¹ ^ 2 * (x ⬝ᵥ (Q *ᵥ x)) := by
        simp only [f, WithLp.ofLp_smul, dotProduct_smul, smul_dotProduct, mulVec_smul, smul_eq_mul]
        ring
      have h3 : f y0 ≤ r⁻¹ ^ 2 * (x ⬝ᵥ (Q *ᵥ x)) := h2 ▸ h1
      rw [← hnorm x, ← hr] at *
      have hr2 : 0 < r ^ 2 := by positivity
      calc f y0 * r ^ 2 ≤ (r⁻¹ ^ 2 * (x ⬝ᵥ (Q *ᵥ x))) * r ^ 2 := by gcongr
        _ = x ⬝ᵥ (Q *ᵥ x) := by field_simp
  · have hx : ∀ x : Fin k → ℝ, x = 0 := fun x => by
      by_contra h; exact hx ⟨x, h⟩
    refine ⟨1, one_pos, fun x => ?_⟩
    simp [hx x]

/-- The trace of a product of two real positive semidefinite matrices is nonnegative. -/
theorem trace_mul_nonneg_of_posSemidef {k : ℕ} {A B : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  open scoped MatrixOrder in
  have hB0 : 0 ≤ B := Matrix.nonneg_iff_posSemidef.2 hB
  open scoped MatrixOrder in
  have hS : CFC.sqrt B * CFC.sqrt B = B := CFC.sqrt_mul_sqrt_self B hB0
  open scoped MatrixOrder in
  have hsa : IsSelfAdjoint (CFC.sqrt B) := (CFC.sqrt_nonneg B).isSelfAdjoint
  have hT : (CFC.sqrt B)ᴴ = CFC.sqrt B := hsa
  have h1 : (A * B).trace = ((CFC.sqrt B)ᴴ * A * CFC.sqrt B).trace := by
    conv_lhs => rw [← hS]
    rw [hT, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [h1]
  exact (hA.conjTranspose_mul_mul_same _).trace_nonneg

/-- The imaginary part of `tr(P Z)` for real `P`. -/
theorem trace_im_aux {k : ℕ} (P : Matrix (Fin k) (Fin k) ℝ) (Z : Matrix (Fin k) (Fin k) ℂ) :
    ((P.map (fun r : ℝ => (r : ℂ)) * Z).trace).im = (P * Z.map Complex.im).trace := by
  simp [Matrix.trace, Matrix.mul_apply, Complex.im_sum]

/-- Pointwise bound for the theta term (core of Proposition 1.3). -/
theorem thetaTerm_norm_le {Q : Matrix (Fin m) (Fin m) ℤ} (hQ : Q ∈ evenPD m) {c : ℝ}
    (hc : ∀ x : Fin m → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((Q.map (Int.cast : ℤ → ℝ)) *ᵥ x)) {ε : ℝ} (hε : 0 < ε)
    (Z : SiegelSpace n) (hZ : Z ∈ siegelSetEps n ε) (N : Matrix (Fin m) (Fin n) ℤ) :
    ‖thetaTerm Q (Z : Matrix (Fin n) (Fin n) ℂ) N‖ ≤
      Real.exp (-(Real.pi * ε * c) * ∑ i, ∑ j, ((N i j : ℤ) : ℝ) ^ 2) := by
  set Nr : Matrix (Fin m) (Fin n) ℝ := N.map (Int.cast : ℤ → ℝ) with hNr
  set Qr : Matrix (Fin m) (Fin m) ℝ := Q.map (Int.cast : ℤ → ℝ) with hQr
  have hQd : Qr.PosDef := hQ.2
  set P : Matrix (Fin n) (Fin n) ℝ := Nrᵀ * Qr * Nr with hP
  have hzN : zc N = Nr.map Complex.ofRealHom := by ext i j; simp [zc, hNr]
  have hzQ : zc Q = Qr.map Complex.ofRealHom := by ext i j; simp [zc, hQr]
  have hPC : (zc N)ᵀ * zc Q * zc N = P.map (fun r : ℝ => (r : ℂ)) := by
    have : P.map Complex.ofRealHom = P.map (fun r : ℝ => (r : ℂ)) := rfl
    rw [← this, hzN, hzQ, hP]
    simp only [Matrix.map_mul, transpose_map]
  have hre : ∀ T : ℂ, ((Real.pi : ℂ) * Complex.I * T).re = -(Real.pi * T.im) := fun T => by
    simp [Complex.mul_re]
  have hnorm : ‖thetaTerm Q (Z : Matrix (Fin n) (Fin n) ℂ) N‖ =
      Real.exp (-(Real.pi * (P * Z.im).trace)) := by
    unfold thetaTerm eTr
    rw [hPC, Complex.norm_exp, hre, trace_im_aux P (Z : Matrix (Fin n) (Fin n) ℂ)]
    rfl
  have hPsd : P.PosSemidef := by
    have := hQd.posSemidef.conjTranspose_mul_mul_same Nr
    simpa [hP, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have h1 : 0 ≤ (P * (Z.im - ε • (1 : Matrix (Fin n) (Fin n) ℝ))).trace :=
    trace_mul_nonneg_of_posSemidef hPsd hZ
  have h2 : (P * Z.im).trace = (P * (Z.im - ε • (1 : Matrix (Fin n) (Fin n) ℝ))).trace + ε * P.trace := by
    simp [Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_smul]
  have hd : ∀ j, P j j = (fun i => Nr i j) ⬝ᵥ (Qr *ᵥ fun i => Nr i j) := by
    intro j
    simp only [hP, Matrix.mul_apply, dotProduct, Matrix.mulVec, transpose_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h3 : c * ∑ i, ∑ j, ((N i j : ℤ) : ℝ) ^ 2 ≤ P.trace := by
    calc c * ∑ i, ∑ j, ((N i j : ℤ) : ℝ) ^ 2
        = ∑ j, c * ((fun i => Nr i j) ⬝ᵥ (fun i => Nr i j)) := by
          rw [Finset.sum_comm, Finset.mul_sum]
          simp [dotProduct, hNr, sq]
      _ ≤ ∑ j, P j j := Finset.sum_le_sum fun j _ => by rw [hd j]; exact hc _
      _ = P.trace := rfl
  rw [hnorm]
  apply Real.exp_le_exp.2
  have h4 : ε * (c * ∑ i, ∑ j, ((N i j : ℤ) : ℝ) ^ 2) ≤ (P * Z.im).trace := by
    nlinarith [mul_le_mul_of_nonneg_left h3 hε.le]
  have h5 := mul_le_mul_of_nonneg_left h4 Real.pi_pos.le
  nlinarith [h5]


/-- **Andrianov–Zhuravlev, Proposition 1.3.** For `Q ∈ A_m⁺` and `ε > 0` the theta series converges absolutely and
uniformly on `H_n(ε)`: its terms are dominated there by a summable sequence independent of `Z` (Weierstrass test). -/
@[kb "andrianovzhuravlev1995" "Chapter 1, Proposition 1.3, p. 16"]
theorem thetaSeries_dominated {Q : Matrix (Fin m) (Fin m) ℤ} (hQ : Q ∈ evenPD m) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : Matrix (Fin m) (Fin n) ℤ → ℝ, Summable u ∧
      ∀ N, ∀ Z ∈ siegelSetEps n ε, ‖thetaTerm Q (Z : Matrix (Fin n) (Fin n) ℂ) N‖ ≤ u N := by
  obtain ⟨c, hc0, hc⟩ := posDef_coercive (hQ.2 : (Q.map (Int.cast : ℤ → ℝ)).PosDef)
  have ha : 0 < Real.pi * ε * c := by positivity
  have g := summable_gauss_int ha
  have inner := summable_pi_prod_aux _ (fun t => (Real.exp_pos _).le) g n
  have outer := summable_pi_prod_aux (fun r : Fin n → ℤ => ∏ j, Real.exp (-(Real.pi * ε * c) * ((r j : ℤ) : ℝ) ^ 2))
    (fun r => Finset.prod_nonneg fun j _ => (Real.exp_pos _).le) inner m
  refine ⟨fun N => ∏ i, ∏ j, Real.exp (-(Real.pi * ε * c) * ((N i j : ℤ) : ℝ) ^ 2), outer, ?_⟩
  intro N Z hZ
  refine (thetaTerm_norm_le hQ hc hε Z hZ N).trans (le_of_eq ?_)
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Real.exp_sum]

/-- **Andrianov–Zhuravlev, Theorem 1.4 (boundedness).** `θ^n(Z, Q)` is bounded on every `H_n(ε)`, `ε > 0`. -/
@[kb "andrianovzhuravlev1995" "Chapter 1, Theorem 1.4, p. 16"]
theorem thetaSeries_bounded {Q : Matrix (Fin m) (Fin m) ℤ} (hQ : Q ∈ evenPD m) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ Z ∈ siegelSetEps n ε, ‖thetaSeries Q Z‖ ≤ C := by
  obtain ⟨u, hu, hle⟩ := thetaSeries_dominated (n := n) hQ hε
  refine ⟨∑' N, u N, fun Z hZ => ?_⟩
  have hs : Summable fun N => ‖thetaTerm Q (Z : Matrix (Fin n) (Fin n) ℂ) N‖ :=
    hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun N => hle N Z hZ)
  calc ‖thetaSeries Q Z‖ ≤ ∑' N, ‖thetaTerm Q (Z : Matrix (Fin n) (Fin n) ℂ) N‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' N, u N := hs.tsum_le_tsum (fun N => hle N Z hZ) hu

/-- **Andrianov–Zhuravlev, Theorem 1.4 (holomorphy)**, named statement: for `Q ∈ A_m⁺` the theta series is a
holomorphic function on `H_n`. (The book derives it from Proposition 1.3; the step "a locally uniform limit of
holomorphic functions of several variables is holomorphic" is not in Mathlib at this pin.) -/
@[kb "andrianovzhuravlev1995" "Chapter 1, Theorem 1.4, p. 16"]
structure ThetaSeriesHolomorphic (m n : ℕ) : Prop where
  holo : ∀ Q : Matrix (Fin m) (Fin m) ℤ, Q ∈ evenPD m → IsHolomorphicOnSiegel (n := n) (thetaSeries Q)

/-- **Andrianov–Zhuravlev, Chapter 1, §3.3.** The level of a nondegenerate even matrix `Q`: the least `q ≥ 1` with
`q Q⁻¹` even. Here `q Q⁻¹` even is expressed over `ℚ` as `q Q⁻¹ = Q'` for an even integral `Q'`. -/
def IsLevel (Q : Matrix (Fin m) (Fin m) ℤ) (q : ℕ) : Prop :=
  0 < q ∧ (∃ Q' : Matrix (Fin m) (Fin m) ℤ, IsEvenSymm Q' ∧
      (q : ℚ) • (Q.map (Int.cast : ℤ → ℚ))⁻¹ = Q'.map (Int.cast : ℤ → ℚ)) ∧
    ∀ q' : ℕ, 0 < q' → (∃ Q' : Matrix (Fin m) (Fin m) ℤ, IsEvenSymm Q' ∧
      (q' : ℚ) • (Q.map (Int.cast : ℤ → ℚ))⁻¹ = Q'.map (Int.cast : ℤ → ℚ)) → q ≤ q'

/-- **Andrianov–Zhuravlev, Theorem 3.13 with Theorem 4.10 (even `m = 2k`)**, named statement. Let `Q ∈ A_m⁺` have
level `q`, `m = 2k`, and let `χ` be a Dirichlet character modulo `q` with `χ(-1) = (-1)^k` (4.32) and
`χ(p) = ((-1)^k det Q / p)` for odd primes `p ∤ q` (4.33), and `χ(2) = 2^{-k} ∑_{t ∈ (ℤ/2)^m} exp(πi Q[t]/2)` if `q`
is odd (4.34). Then for `M = (A B; C D) ∈ Γ_0^n(q)`:
`θ^n(M⟨Z⟩, Q) = χ(det D) det(CZ + D)^k θ^n(Z, Q)` ((3.30), (4.31); for `q = 1`, (4.30) says the multiplier is `1`,
which is the same formula since every character modulo `1` is trivial). -/
@[kb "andrianovzhuravlev1995" "Chapter 1, Theorem 3.13 and Theorem 4.10, pp. 32, 47"]
structure ThetaTransformationEven (m n k : ℕ) : Prop where
  law : m = 2 * k → ∀ (Q : Matrix (Fin m) (Fin m) ℤ) (q : ℕ), Q ∈ evenPD m → IsLevel Q q →
    ∀ χ : DirichletCharacter ℂ q,
      χ (-1) = (-1) ^ k →
      (∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ q →
        χ p = (jacobiSym ((-1) ^ k * Q.det) p : ℂ)) →
      (Odd q → χ 2 = (2 : ℂ)⁻¹ ^ k * ∑ t : Fin m → ZMod 2,
        Complex.exp (Real.pi * Complex.I *
          ((∑ i, ∑ j, (Q i j : ℂ) * ((t i).val : ℂ) * ((t j).val : ℂ)) / 2))) →
      ∀ M : SiegelModularGroup n, M ∈ gammaZero n q → ∀ Z : SiegelSpace n,
        thetaSeries Q (SiegelModularGroup.toReal M • Z) =
          χ ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ).toBlocks₂₂.det) *
            (jmat (SiegelModularGroup.toReal M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) Z).det ^ k * thetaSeries Q Z

end ModularFormsKB.Andrianov
