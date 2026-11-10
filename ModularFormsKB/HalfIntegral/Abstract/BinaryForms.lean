/-
# Binary quadratic forms, the action of $\mathrm{SL}_2(\mathbb Z)$ and automorphs

Integral binary quadratic forms
$Q = [a, b, c]$, $Q(x, y) = ax^2 + bxy + cy^2$, of discriminant $\Delta = b^2 - 4ac$, with the right action
$(Q \circ g)(x, y) = Q(g_{0,0}x + g_{0,1}y,\ g_{1,0}x + g_{1,1}y)$ of $2 \times 2$ integer matrices. Everything here is
algebra (ring identities); the analytic objects (geodesics, cycle integrals) are in
`ModularFormsKB/HalfIntegral/Abstract/Shintani.lean`.

Proved:
- `BinQF.comp_one`, `BinQF.comp_mul`: a right action of $2 \times 2$ integer matrices;
- `BinQF.disc_comp`: $\operatorname{disc}(Q \circ g) = \det(g)^2 \operatorname{disc}(Q)$, so $\mathrm{SL}_2(\mathbb Z)$ preserves the
  discriminant;
- `BinQF.evalC_comp`: $Q\circ g\,(z, 1) = (g_{1,0}z + g_{1,1})^2\, Q(gz, 1)$ for $z \in \mathbb C$ with $g_{1,0}z + g_{1,1} \ne 0$;
- `BinQF.Equiv`: proper equivalence (an equivalence relation, `BinQF.equivSetoid`), preserving discriminant and the
  set of represented integers;
- `BinQF.automorph`: for a solution of $t^2 - \Delta u^2 = 4$ the matrix
  $\begin{pmatrix}(t - bu)/2 & -cu \\ au & (t + bu)/2\end{pmatrix}$ has determinant $1$ (`BinQF.det_automorph`) and fixes $Q$
  (`BinQF.comp_automorph`).

**Index shift.** Matrix entries are 0-based: $g = \begin{pmatrix} g_{0,0} & g_{0,1} \\ g_{1,0} & g_{1,1}\end{pmatrix}$.
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Nat.Prime.Int

namespace ModularFormsKB.HalfIntegral

open Matrix MatrixGroups

/-- **An integral binary quadratic form** $[a, b, c]$, i.e. $Q(x, y) = ax^2 + bxy + cy^2$. -/
@[ext]
structure BinQF where
  /-- The coefficient of $x^2$. -/
  a : ℤ
  /-- The coefficient of $xy$. -/
  b : ℤ
  /-- The coefficient of $y^2$. -/
  c : ℤ

namespace BinQF

/-- **Discriminant** $b^2 - 4ac$. -/
def disc (Q : BinQF) : ℤ := Q.b ^ 2 - 4 * Q.a * Q.c

/-- The value $Q(x, y) = ax^2 + bxy + cy^2$. -/
def val (Q : BinQF) (x y : ℤ) : ℤ := Q.a * x ^ 2 + Q.b * x * y + Q.c * y ^ 2

/-- The value $Q(z, 1) = az^2 + bz + c$ at a complex number $z$. -/
def evalC (Q : BinQF) (z : ℂ) : ℂ := Q.a * z ^ 2 + Q.b * z + Q.c

/-- **Content** $\gcd(a, b, c)$. -/
def content (Q : BinQF) : ℕ := Int.gcd Q.a (Int.gcd Q.b Q.c)

/-- **The right action** $(Q \circ g)(x, y) = Q(g_{0,0}x + g_{0,1}y,\ g_{1,0}x + g_{1,1}y)$. -/
def comp (Q : BinQF) (g : Matrix (Fin 2) (Fin 2) ℤ) : BinQF :=
  ⟨Q.val (g 0 0) (g 1 0),
    2 * Q.a * g 0 0 * g 0 1 + Q.b * (g 0 0 * g 1 1 + g 0 1 * g 1 0) + 2 * Q.c * g 1 0 * g 1 1,
    Q.val (g 0 1) (g 1 1)⟩

theorem val_comp (Q : BinQF) (g : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℤ) :
    (Q.comp g).val x y = Q.val (g 0 0 * x + g 0 1 * y) (g 1 0 * x + g 1 1 * y) := by
  simp only [comp, val]; ring

theorem comp_one (Q : BinQF) : Q.comp 1 = Q := by
  ext <;> simp [comp, val]

theorem comp_mul (Q : BinQF) (g h : Matrix (Fin 2) (Fin 2) ℤ) :
    Q.comp (g * h) = (Q.comp g).comp h := by
  ext <;> simp only [comp, val, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem disc_comp (Q : BinQF) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    (Q.comp g).disc = g.det ^ 2 * Q.disc := by
  simp only [comp, val, disc, Matrix.det_fin_two]; ring

theorem disc_comp_SL (Q : BinQF) (g : SL(2, ℤ)) : (Q.comp g).disc = Q.disc := by
  rw [disc_comp, g.det_coe, one_pow, one_mul]

/-- $Q\circ g\,(z, 1) = (g_{1,0}z + g_{1,1})^2\,Q\big(\tfrac{g_{0,0}z + g_{0,1}}{g_{1,0}z + g_{1,1}}, 1\big)$. -/
theorem evalC_comp (Q : BinQF) (g : Matrix (Fin 2) (Fin 2) ℤ) {z : ℂ}
    (hz : (g 1 0 : ℂ) * z + g 1 1 ≠ 0) :
    (Q.comp g).evalC z =
      ((g 1 0 : ℂ) * z + g 1 1) ^ 2 * Q.evalC ((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1)) := by
  set u := ((g 0 0 : ℂ) * z + g 0 1) / (g 1 0 * z + g 1 1) with hu
  have hu' : (g 0 0 : ℂ) * z + g 0 1 - u * (g 1 0 * z + g 1 1) = 0 := by
    rw [hu, div_mul_cancel₀ _ hz, sub_self]
  simp only [comp, val, evalC]
  push_cast
  linear_combination (Q.a * (((g 0 0 : ℂ) * z + g 0 1) + u * (g 1 0 * z + g 1 1)) +
    Q.b * ((g 1 0 : ℂ) * z + g 1 1)) * hu'

/-- $Q(z,1)$ at the image of $z$: $Q(gz, 1) = (g_{1,0}z+g_{1,1})^{-2}\,(Q\circ g)(z, 1)$. -/
theorem evalC_smul (Q : BinQF) (g : Matrix (Fin 2) (Fin 2) ℤ) {z : ℂ}
    (hz : (g 1 0 : ℂ) * z + g 1 1 ≠ 0) :
    Q.evalC ((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1)) =
      (Q.comp g).evalC z / ((g 1 0 : ℂ) * z + g 1 1) ^ 2 := by
  rw [evalC_comp Q g hz, mul_div_cancel_left₀ _ (pow_ne_zero 2 hz)]

/-- **Proper equivalence:** $Q' = Q \circ g$ for some $g \in \mathrm{SL}_2(\mathbb Z)$. -/
def Equiv (Q Q' : BinQF) : Prop := ∃ g : SL(2, ℤ), Q' = Q.comp g

theorem Equiv.refl (Q : BinQF) : Equiv Q Q := ⟨1, by simp [comp_one]⟩

theorem Equiv.symm {Q Q' : BinQF} (h : Equiv Q Q') : Equiv Q' Q := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g⁻¹, ?_⟩
  rw [← comp_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, comp_one]

theorem Equiv.trans {Q Q' Q'' : BinQF} (h : Equiv Q Q') (h' : Equiv Q' Q'') : Equiv Q Q'' := by
  obtain ⟨g, rfl⟩ := h
  obtain ⟨g', rfl⟩ := h'
  exact ⟨g * g', by rw [Matrix.SpecialLinearGroup.coe_mul, comp_mul]⟩

/-- Proper equivalence as a setoid. -/
def equivSetoid : Setoid BinQF := ⟨Equiv, ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩⟩

theorem Equiv.disc_eq {Q Q' : BinQF} (h : Equiv Q Q') : Q'.disc = Q.disc := by
  obtain ⟨g, rfl⟩ := h
  exact disc_comp_SL Q g

/-- Equivalent forms represent the same integers. -/
theorem Equiv.represents {Q Q' : BinQF} (h : Equiv Q Q') (x y : ℤ) :
    ∃ x' y' : ℤ, Q.val x' y' = Q'.val x y := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨_, _, (val_comp Q g x y).symm⟩

/-- In a solution of $t^2 - \Delta u^2 = 4$, $t \equiv bu \bmod 2$. -/
theorem two_dvd_sub_of_pell (Q : BinQF) {t u : ℤ} (h : t ^ 2 - Q.disc * u ^ 2 = 4) :
    2 ∣ t - Q.b * u := by
  have h2 : (2 : ℤ) ∣ (t - Q.b * u) * (t + Q.b * u) :=
    ⟨2 - 2 * Q.a * Q.c * u ^ 2, by simp only [disc] at h; linear_combination h⟩
  rcases (Int.prime_two).dvd_or_dvd h2 with h | h
  · exact h
  · have : t - Q.b * u = (t + Q.b * u) - 2 * (Q.b * u) := by ring
    rw [this]
    exact dvd_sub h (dvd_mul_right _ _)

/-- **The automorph** $\begin{pmatrix}(t - bu)/2 & -cu \\ au & (t + bu)/2\end{pmatrix}$ attached to $(t, u)$. -/
def automorph (Q : BinQF) (t u : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(t - Q.b * u) / 2, -Q.c * u; Q.a * u, (t + Q.b * u) / 2]

private theorem automorph_eq (Q : BinQF) {t u : ℤ} (h : t ^ 2 - Q.disc * u ^ 2 = 4) :
    ∃ p : ℤ, p ^ 2 + p * Q.b * u + Q.a * Q.c * u ^ 2 = 1 ∧
      Q.automorph t u = !![p, -Q.c * u; Q.a * u, p + Q.b * u] := by
  obtain ⟨p, hp⟩ := Q.two_dvd_sub_of_pell h
  have ht : t = 2 * p + Q.b * u := by linarith
  refine ⟨p, mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) ?_, ?_⟩
  · subst ht; simp only [disc] at h; linear_combination h
  have h1 : (t - Q.b * u) / 2 = p := by rw [hp]; simp
  have h2 : (t + Q.b * u) / 2 = p + Q.b * u := by
    rw [show t + Q.b * u = 2 * (p + Q.b * u) by linarith]; simp
  simp only [automorph, h1, h2]

theorem det_automorph (Q : BinQF) {t u : ℤ} (h : t ^ 2 - Q.disc * u ^ 2 = 4) :
    (Q.automorph t u).det = 1 := by
  obtain ⟨p, hp, he⟩ := Q.automorph_eq h
  rw [he, Matrix.det_fin_two_of]
  linear_combination hp

theorem comp_automorph (Q : BinQF) {t u : ℤ} (h : t ^ 2 - Q.disc * u ^ 2 = 4) :
    Q.comp (Q.automorph t u) = Q := by
  obtain ⟨p, hp, he⟩ := Q.automorph_eq h
  rw [he]
  ext <;> simp only [comp, val, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  · linear_combination Q.a * hp
  · linear_combination Q.b * hp
  · linear_combination Q.c * hp

/-- The automorph as an element of $\mathrm{SL}_2(\mathbb Z)$. -/
def automorphSL (Q : BinQF) {t u : ℤ} (h : t ^ 2 - Q.disc * u ^ 2 = 4) : SL(2, ℤ) :=
  ⟨Q.automorph t u, Q.det_automorph h⟩

theorem comp_automorphSL (Q : BinQF) {t u : ℤ} (h : t ^ 2 - Q.disc * u ^ 2 = 4) :
    Q.comp (Q.automorphSL h) = Q :=
  Q.comp_automorph h

end BinQF

end ModularFormsKB.HalfIntegral
