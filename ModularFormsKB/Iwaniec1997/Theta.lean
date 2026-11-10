import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.PosDef
import ModularFormsKB.HalfIntegral.Abstract.Shintani
import ModularFormsKB.Citation
/-!
# Iwaniec, Chapter 10: theta functions with spherical polynomials

H. Iwaniec, *Topics in Classical Automorphic Forms* (`iwaniec1997`), Sections 9.1, 9.2, 10.1, 10.2 and 10.4. Page numbers
are printed pages. Indices are 0-based (`Fin r`); the book's $x_1, \dots, x_r$ are `x 0, …, x (r-1)`.

For a symmetric positive definite $r \times r$ matrix $A$ write $A[x] = {}^t x A x$ (10.6) and $B(x,y) = {}^t x A y$.
A **spherical function with respect to $A$** of degree $\nu$ (Sections 9.1, 9.2) is a homogeneous polynomial $P$ of
degree $\nu$ annihilated by the Laplace operator $\Delta_A = \sum_{i,j} a'_{ij}\,\partial^2/\partial x_i\partial x_j$
(9.4), where $A^{-1} = (a'_{ij})$. The theta function (10.1) is
$\Theta(z) = \Theta(z; A, P) = \sum_{m \in \mathbb Z^r} P(m)\, e(\tfrac12 A[m] z)$.

## Items
- (9.4), Section 9.2: `laplaceA`, `IsSphericalWRT`.
- (10.1): `thetaAP`; (10.3) the congruent theta function `thetaCongruent`.
- **Proposition 10.1** (generalized Jacobi inversion (10.9)): stated as `GeneralizedJacobiInversion`, not proved in
  general. **Proved** in rank one with $P = 1$ and any $x \in \mathbb C$ (`jacobiInversion_rankOne`), from Mathlib's
  `jacobiTheta₂_functional_equation`.
- **Theorem 10.9** (theta functions of even rank are modular forms on $\Gamma_0(N)$ with the character $\chi_D$):
  stated as `ThetaModularGamma0`, not proved. The character $\chi_D(d) = (D/d)$ of (10.45) is the Kronecker symbol
  `ModularFormsKB.HalfIntegral.kroneckerInt`.
- Theorem 10.8 in rank one ($A = (2)$, $N = 2$, $P = 1$, so $\Theta = \theta$ on $\Gamma_0(4)$) is proved in this
  repository: `ModularFormsKB.HalfIntegral.theta_transformationLaw`.
-/

open Complex Matrix MvPolynomial CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm

noncomputable section

namespace ModularFormsKB.Iwaniec1997

variable {r : ℕ}

/-- The quadratic form $A[x] = {}^t x A x$ (10.6) of a real matrix at a complex vector. -/
def quadValue (A : Matrix (Fin r) (Fin r) ℝ) (x : Fin r → ℂ) : ℂ :=
  x ⬝ᵥ ((A.map (fun a : ℝ ↦ (a : ℂ))) *ᵥ x)

/-- The integer vector $m$ as a complex vector. -/
abbrev intVec (m : Fin r → ℤ) : Fin r → ℂ := fun i ↦ (m i : ℂ)

/-- **The Laplace operator attached to $A$** (9.4): $\Delta_A = \sum_{i,j} a'_{ij}\,\partial_i\partial_j$ with
$A^{-1} = (a'_{ij})$, acting on polynomials with complex coefficients. -/
@[kb "iwaniec1997" "Section 9.1, (9.4), p. 148"]
def laplaceA (A : Matrix (Fin r) (Fin r) ℝ) (P : MvPolynomial (Fin r) ℂ) : MvPolynomial (Fin r) ℂ :=
  ∑ i, ∑ j, ((A⁻¹ i j : ℝ) : ℂ) • pderiv i (pderiv j P)

/-- **Spherical function with respect to $A$ of degree $\nu$** (Section 9.2, (9.7)): a homogeneous polynomial of degree
$\nu$ that is harmonic for $\Delta_A$. -/
@[kb "iwaniec1997" "Section 9.2, spherical functions, (9.7), p. 150"]
def IsSphericalWRT (A : Matrix (Fin r) (Fin r) ℝ) (ν : ℕ) (P : MvPolynomial (Fin r) ℂ) : Prop :=
  P.IsHomogeneous ν ∧ laplaceA A P = 0

/-- **The theta function (10.1)**: $\Theta(z; A, P) = \sum_{m\in\mathbb Z^r} P(m)\,e(\tfrac12 A[m]z)$. -/
@[kb "iwaniec1997" "Section 10.1, (10.1), p. 165"]
def thetaAP (A : Matrix (Fin r) (Fin r) ℝ) (P : MvPolynomial (Fin r) ℂ) (z : ℂ) : ℂ :=
  ∑' m : Fin r → ℤ, eval (intVec m) P * cexp (2 * π * I * (quadValue A (intVec m) / 2 * z))

/-- **The congruent theta function (10.3)**: for an integral $A$, $N \ge 1$ and $h \in \mathbb Z^r$,
$\Theta(z; h) = \sum_{m \equiv h\ (\mathrm{mod}\ N)} P(m)\, e\big(A[m] z / 2N^2\big)$. -/
@[kb "iwaniec1997" "Section 10.1, (10.3), p. 165"]
def thetaCongruent (A : Matrix (Fin r) (Fin r) ℤ) (P : MvPolynomial (Fin r) ℂ) (N : ℕ) (h : Fin r → ℤ) (z : ℂ) :
    ℂ :=
  ∑' m : {m : Fin r → ℤ // ∀ i, m i ≡ h i [ZMOD N]},
    eval (intVec m.1) P *
      cexp (2 * π * I * (quadValue (A.map (fun a : ℤ ↦ (a : ℝ))) (intVec m.1) / (2 * (N : ℂ) ^ 2) * z))

/-- The polynomial $P^*(x) = P(A^{-1}x)$ of Proposition 10.1. -/
def dualPoly (A : Matrix (Fin r) (Fin r) ℝ) (P : MvPolynomial (Fin r) ℂ) : MvPolynomial (Fin r) ℂ :=
  bind₁ (fun i ↦ ∑ j, ((A⁻¹ i j : ℝ) : ℂ) • X j) P

/-- **Proposition 10.1** (generalized Jacobi inversion (10.9); not proved here in general): let $A$ be a symmetric
positive definite real matrix and $P$ a spherical function with respect to $A$ of degree $\nu$, $k = \nu + r/2$. For
$z \in \mathbb H$ and $x \in \mathbb C^r$,
$$\sum_m P(m+x)\,e\big(\tfrac12 A[m+x]z\big) = \frac{i^{-\nu}}{\sqrt{|A|}}\Big(\frac iz\Big)^k
\sum_m P^*(m)\, e\Big(\frac{-A^{-1}[m]}{2z} + {}^t m x\Big),\qquad P^*(x) = P(A^{-1}x).$$ -/
@[kb "iwaniec1997" "Section 10.2, Proposition 10.1, (10.9), (10.10), p. 167"]
def GeneralizedJacobiInversion (r : ℕ) : Prop :=
  ∀ (A : Matrix (Fin r) (Fin r) ℝ), A.PosDef → ∀ (ν : ℕ) (P : MvPolynomial (Fin r) ℂ), IsSphericalWRT A ν P →
    ∀ (z : ℂ), 0 < z.im → ∀ (x : Fin r → ℂ),
      ∑' m : Fin r → ℤ, eval (intVec m + x) P * cexp (2 * π * I * (quadValue A (intVec m + x) / 2 * z)) =
        I ^ (-(ν : ℤ)) / (Real.sqrt A.det : ℂ) * (I / z) ^ ((ν : ℂ) + r / 2) *
          ∑' m : Fin r → ℤ, eval (intVec m) (dualPoly A P) *
            cexp (2 * π * I * (-quadValue A⁻¹ (intVec m) / (2 * z) + intVec m ⬝ᵥ x))

/-- For real $a > 0$ and $w \ne 0$, $(a w)^{1/2} = \sqrt a\, w^{1/2}$. -/
theorem mul_cpow_half_ofReal {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : w ≠ 0) :
    ((a : ℂ) * w) ^ (1 / 2 : ℂ) = (Real.sqrt a : ℂ) * w ^ (1 / 2 : ℂ) := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hs : (Real.sqrt a : ℂ) = (a : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha.le]; push_cast; rfl
  rw [hs, Complex.cpow_def_of_ne_zero (mul_ne_zero ha' hw), Complex.log_ofReal_mul ha hw,
    Complex.cpow_def_of_ne_zero ha', Complex.cpow_def_of_ne_zero hw, add_mul, Complex.exp_add, Complex.ofReal_log ha.le]

/-- **Proposition 10.1 in rank one with $P = 1$**: for $a > 0$, $z \in \mathbb H$ and $x \in \mathbb C$,
$$\sum_m e\big(\tfrac12 a(m+x)^2z\big) = a^{-1/2}\Big(\frac iz\Big)^{1/2} \sum_m e\Big(\frac{-m^2}{2az} + mx\Big).$$ -/
@[kb "iwaniec1997" "Section 10.2, Proposition 10.1, (10.9), rank one, P = 1, p. 167"]
theorem jacobiInversion_rankOne {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.im) (x : ℂ) :
    ∑' m : ℤ, cexp (2 * π * I * (a * (m + x) ^ 2 / 2 * z)) =
      1 / (Real.sqrt a : ℂ) * (I / z) ^ (1 / 2 : ℂ) *
        ∑' m : ℤ, cexp (2 * π * I * (-(m : ℂ) ^ 2 / (2 * a * z) + m * x)) := by
  set τ : ℂ := a * z with hτdef
  have hτim : 0 < τ.im := by
    simpa [hτdef] using mul_pos ha hz
  have hτ0 : τ ≠ 0 := fun h => by rw [h] at hτim; simp at hτim
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  -- left side
  have hL : ∀ m : ℤ, cexp (2 * π * I * (a * (m + x) ^ 2 / 2 * z)) =
      cexp (π * I * τ * x ^ 2) * jacobiTheta₂_term m (x * τ) τ := by
    intro m
    rw [jacobiTheta₂_term, ← Complex.exp_add, hτdef]
    congr 1; ring
  have hR : ∀ m : ℤ, cexp (2 * π * I * (-(m : ℂ) ^ 2 / (2 * a * z) + m * x)) =
      jacobiTheta₂_term m x (-1 / τ) := by
    intro m
    rw [jacobiTheta₂_term, hτdef]
    congr 1; field_simp; ring
  simp_rw [hL, hR]
  rw [tsum_mul_left]
  have hfe := jacobiTheta₂_functional_equation (x * τ) τ
  rw [mul_div_cancel_right₀ x hτ0] at hfe
  change cexp (π * I * τ * x ^ 2) * jacobiTheta₂ (x * τ) τ = _ * jacobiTheta₂ x (-1 / τ)
  rw [hfe]
  have hw : (-I * τ) = (a : ℂ) * (-I * z) := by rw [hτdef]; ring
  have hre : (-I * z).arg ≠ π := by
    apply ne_of_lt
    exact Complex.arg_lt_pi_iff.2 (Or.inl (by simpa using hz.le))
  have hinv : I / z = (-I * z)⁻¹ := by field_simp; simp
  have hz1 : (-I * z) ≠ 0 := by simp [hz0]
  rw [hinv, Complex.inv_cpow _ _ hre, hw, mul_cpow_half_ofReal ha hz1]
  have hexp : cexp (π * I * τ * x ^ 2) * cexp (-π * I * (x * τ) ^ 2 / τ) = 1 := by
    rw [← Complex.exp_add]; convert Complex.exp_zero using 2; field_simp; ring
  have hs : (Real.sqrt a : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 ha).ne'
  have hq : (-I * z) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; simp [hz0]
  calc _ = (cexp (π * I * τ * x ^ 2) * cexp (-π * I * (x * τ) ^ 2 / τ)) *
        (1 / ((Real.sqrt a : ℂ) * (-I * z) ^ (1 / 2 : ℂ))) * jacobiTheta₂ x (-1 / τ) := by ring
    _ = _ := by rw [hexp]; field_simp

/-- **Theorem 10.9** (not proved here): let $A$ be a symmetric positive definite integral matrix of even rank $r$, $N$
a positive integer with $A^* = NA^{-1}$ integral, both $A$ and $A^*$ with even diagonal entries, and $P$ a spherical
function with respect to $A$ of even degree $\nu$. Then $\Theta(z)$ is a modular form for $\Gamma_0(N)$ of weight
$k = \nu + r/2$ with multiplier the character $\chi_D(d) = (D/d)$, $D = (-1)^{r/2}|A|$ (10.45): for
$\tau = \begin{pmatrix} a & b \\ c & d\end{pmatrix} \in \Gamma_0(N)$, $\Theta(\tau z) = \chi_D(d)(cz+d)^k\Theta(z)$
(10.44); $\Theta$ is holomorphic on $\mathbb H$ and at the cusps (packaged as a modular form for
$\Gamma_1(N) \subseteq \Gamma_0(N)$, on which $\chi_D$ is trivial); and it is a cusp form if $\nu > 0$. -/
@[kb "iwaniec1997" "Section 10.4, Theorem 10.9, (10.44), (10.45), p. 175"]
def ThetaModularGamma0 (r : ℕ) : Prop :=
  Even r → ∀ (A : Matrix (Fin r) (Fin r) ℤ), A.IsSymm → (A.map (fun a : ℤ ↦ (a : ℝ))).PosDef →
    ∀ (N : ℕ) [NeZero N] (Astar : Matrix (Fin r) (Fin r) ℤ), A * Astar = (N : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ) →
    (∀ i, Even (A i i)) → (∀ i, Even (Astar i i)) →
    ∀ (ν : ℕ) (P : MvPolynomial (Fin r) ℂ), Even ν → IsSphericalWRT (A.map (fun a : ℤ ↦ (a : ℝ))) ν P →
      let k : ℕ := ν + r / 2
      let D : ℤ := (-1) ^ (r / 2) * A.det
      let Θ : ℍ → ℂ := fun z ↦ thetaAP (A.map (fun a : ℤ ↦ (a : ℝ))) P z
      (∀ γ ∈ Gamma0 N, ∀ z : ℍ,
        Θ (γ • z) = (HalfIntegral.kroneckerInt D (γ 1 1) : ℂ) * ((γ 1 0 : ℂ) * z + γ 1 1) ^ k * Θ z) ∧
      (∃ F : ModularForm ((Gamma1 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k, ⇑F = Θ) ∧
      (0 < ν → ∃ F : CuspForm ((Gamma1 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k, ⇑F = Θ)

end ModularFormsKB.Iwaniec1997
