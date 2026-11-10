import ModularFormsKB.Andrianov.SiegelSpace
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Holomorphic functions on the Siegel upper half-plane

Andrianov–Zhuravlev (`andrianovzhuravlev1995`) call a function on `H_n` holomorphic when it is "a holomorphic function
in `(n) = n(n + 1)/2` complex variables" (Chapter 2, §2.2, condition (1), pdf p. 70): the variables are the entries
`z_{αβ}`, `α ≤ β`, of the symmetric matrix `Z`. We formalize exactly this: coordinates are functions on the index
set `{(α, β) ; α ≤ β}`, a coordinate vector gives the symmetric matrix `symmOfCoords z`, and `F` is holomorphic when
`z ↦ F(symmOfCoords z)` is complex differentiable on the set of coordinate vectors that land in `H_n`.

The book says `H_n` is "obviously an open subset" of `(n)`-dimensional complex space ((1.10), pdf p. 15); this is
recorded as `SiegelCoordsOpen` (named statement; Mathlib at this pin lacks openness of the positive definite cone).
-/

open Matrix

namespace ModularFormsKB.Andrianov

variable {n : ℕ}

/-- The index set `{(α, β) ; α ≤ β}` of the `(n) = n(n+1)/2` coordinates `z_{αβ}` of a symmetric matrix. -/
abbrev UpperIdx (n : ℕ) : Type := {p : Fin n × Fin n // p.1 ≤ p.2}

/-- The symmetric matrix with upper-triangular entries `z`. -/
def symmOfCoords (z : UpperIdx n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if h : i ≤ j then z ⟨(i, j), h⟩ else z ⟨(j, i), le_of_not_ge h⟩

theorem symmOfCoords_transpose (z : UpperIdx n → ℂ) : (symmOfCoords z)ᵀ = symmOfCoords z := by
  ext i j
  simp only [transpose_apply, symmOfCoords, of_apply]
  rcases lt_trichotomy i j with h | h | h
  · simp [h.le, not_le.2 h]
  · subst h; simp
  · simp [h.le, not_le.2 h]

/-- The coordinates of `H_n`: the vectors `z` with `symmOfCoords z ∈ H_n`. -/
def siegelCoords (n : ℕ) : Set (UpperIdx n → ℂ) := symmOfCoords ⁻¹' siegelSet n

/-- The function of `(n)` complex variables attached to `F : H_n → ℂ` (zero off `H_n`). -/
noncomputable def coordFun (F : SiegelSpace n → ℂ) (z : UpperIdx n → ℂ) : ℂ :=
  open Classical in if h : symmOfCoords z ∈ siegelSet n then F ⟨symmOfCoords z, h⟩ else 0

/-- **Andrianov–Zhuravlev, Chapter 2, §2.2, condition (1).** `F` is a holomorphic function in the `(n)` complex
variables `z_{αβ}` (`α ≤ β`) on all of `H_n`. -/
@[kb "andrianovzhuravlev1995" "Chapter 2, §2.2, condition (1), p. 70"]
def IsHolomorphicOnSiegel (F : SiegelSpace n → ℂ) : Prop :=
  DifferentiableOn ℂ (coordFun F) (siegelCoords n)

/-- **Andrianov–Zhuravlev (1.10)**, named statement: `H_n` is an open subset of `(n)`-dimensional complex space. -/
@[kb "andrianovzhuravlev1995" "Chapter 1, (1.10), p. 15"]
structure SiegelCoordsOpen (n : ℕ) : Prop where
  isOpen : IsOpen (siegelCoords n)

theorem IsHolomorphicOnSiegel.add {F G : SiegelSpace n → ℂ} (hF : IsHolomorphicOnSiegel F)
    (hG : IsHolomorphicOnSiegel G) : IsHolomorphicOnSiegel (F + G) := by
  have : coordFun (F + G) = coordFun F + coordFun G := by
    funext z; simp only [coordFun, Pi.add_apply]; split_ifs <;> simp
  unfold IsHolomorphicOnSiegel; rw [this]; exact DifferentiableOn.add hF hG

theorem IsHolomorphicOnSiegel.const_smul {F : SiegelSpace n → ℂ} (c : ℂ) (hF : IsHolomorphicOnSiegel F) :
    IsHolomorphicOnSiegel (c • F) := by
  have : coordFun (c • F) = c • coordFun F := by
    funext z; simp only [coordFun, Pi.smul_apply]; split_ifs <;> simp
  unfold IsHolomorphicOnSiegel; rw [this]; exact DifferentiableOn.const_smul hF c

theorem isHolomorphicOnSiegel_zero : IsHolomorphicOnSiegel (0 : SiegelSpace n → ℂ) := by
  have : coordFun (0 : SiegelSpace n → ℂ) = 0 := by
    funext z; simp only [coordFun, Pi.zero_apply]; split_ifs <;> simp
  unfold IsHolomorphicOnSiegel; rw [this]; exact differentiableOn_const (0 : ℂ)

end ModularFormsKB.Andrianov
