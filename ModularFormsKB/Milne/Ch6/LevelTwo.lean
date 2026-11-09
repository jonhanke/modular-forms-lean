import ModularFormsKB.Milne.Ch6.LevelTwoVanishing
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Complex.Polynomial.Basic
import ModularFormsKB.Citation
/-!
# Milne, Example 6.2: the modular equation of level two

We prove the named statement `ModularFormsKB.Milne.ModularEquationLevelTwo` (Milne, Example 6.2, pdf p. 90):
for meromorphic functions $j_X, j_{2,X}$ on $X_0(2)$ whose values at the class of $z \in \mathbb H$ are $j(z)$ and
$j(2z)$, the minimum polynomial of $j_{2,X}$ over $\mathbb C(j_X)$ is $F_2(j_X, Y)$.

1. **The relation.** $F_2(j(z), j(2z)) = 0$ on $\mathbb H$ (`ModularFormsKB.Milne.LevelTwo.F2_j_two_eq_zero`), so the
   meromorphic function $F_2(j_X, j_{2,X})$ vanishes on the open set of non-cusp points, hence everywhere by the
   identity theorem (`F2R_eq_zero`).
2. **Transcendence.** $j_X$ is not constant ($j(\rho) = 0$, $j(i) = 1728$), so it is transcendental over the
   algebraically closed field $\mathbb C$ (`transcendental_jX`), and $\mathbb C(j_X) \cong \mathbb C(t)$
   (Mathlib's `RatFunc.algEquivOfTranscendental`).
3. **Irreducibility.** $F_2(t, Y + 54000) = Y^3 + (1488t - t^2)Y^2 + (201477375t - 106512t^2)Y
   + (6549518250000t - 2835810000t^2 + t^3)$ is Eisenstein at the prime $t$ of $\mathbb C[t]$ (note
   $F_2(0, Y) = (Y - 54000)^3$), so $F_2(t, Y)$ is irreducible over $\mathbb C[t]$ and, by Gauss's lemma, over
   $\mathbb C(t)$ (`irreducible_cubic_ratFunc`).

The main theorem is `modularEquationLevelTwo`.
-/

open Polynomial UpperHalfPlane Filter

noncomputable section

namespace ModularFormsKB.Milne.LevelTwo

open TauCeti.ModularForm

/-! ### The cubic $F_2(x, Y)$ -/

/-- A monic cubic $Y^3 + aY^2 + bY + c$. -/
def cub {A : Type*} [CommRing A] (a b c : A) : A[X] :=
  X ^ 3 + (C a * X ^ 2 + C b * X + C c)

theorem cub_monic {A : Type*} [CommRing A] [Nontrivial A] (a b c : A) : (cub a b c).Monic :=
  monic_X_pow_add (lt_of_le_of_lt degree_quadratic_le (by norm_num))

theorem cub_degree {A : Type*} [CommRing A] [Nontrivial A] (a b c : A) : (cub a b c).degree = 3 := by
  unfold cub
  rw [degree_add_eq_left_of_degree_lt] <;> rw [degree_X_pow]
  · rfl
  · exact lt_of_le_of_lt degree_quadratic_le (by norm_num)

theorem cub_coeff_zero {A : Type*} [CommRing A] (a b c : A) : (cub a b c).coeff 0 = c := by
  simp [cub]

theorem cub_coeff_one {A : Type*} [CommRing A] (a b c : A) : (cub a b c).coeff 1 = b := by
  simp [cub]

theorem cub_coeff_two {A : Type*} [CommRing A] (a b c : A) : (cub a b c).coeff 2 = a := by
  simp [cub]

/-- $F_2(x, Y) \in A[Y]$ as a monic cubic. -/
def cubic {A : Type*} [CommRing A] (x : A) : A[X] :=
  cub (-x ^ 2 + 1488 * x - 162000) (1488 * x ^ 2 + 40773375 * x + 8748000000)
    (x ^ 3 - 162000 * x ^ 2 + 8748000000 * x - 157464000000000)

theorem cubic_monic {A : Type*} [CommRing A] [Nontrivial A] (x : A) : (cubic x).Monic :=
  cub_monic _ _ _

theorem cubic_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (x : A) :
    (cubic x).map φ = cubic (φ x) := by
  simp [cubic, cub, map_ofNat]

/-- `modularPolynomialTwo`, evaluated at $(x, Y)$, is the cubic `cubic x`. -/
theorem eval₂_modularPolynomialTwo {A : Type*} [CommRing A] (x : A) :
    MvPolynomial.eval₂ (Int.castRingHom A[X]) ![C x, X] modularPolynomialTwo = cubic x := by
  rw [eval_modularPolynomialTwo]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, cubic, cub, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat]
  ring

/-- $F_2(X, Y)$ in any commutative ring. -/
def F2R {R : Type*} [CommRing R] (X Y : R) : R :=
  X ^ 3 + Y ^ 3 - X ^ 2 * Y ^ 2 + 1488 * X * Y * (X + Y) - 162000 * (X ^ 2 + Y ^ 2) + 40773375 * X * Y +
    8748000000 * (X + Y) - 157464000000000

theorem eval_cubic {R : Type*} [CommRing R] (x y : R) : (cubic x).eval y = F2R x y := by
  simp [cubic, cub, F2R]
  ring

/-! ### Irreducibility over $\mathbb C(t)$ -/

/-- The variable $t$ of $\mathbb C[t]$. -/
abbrev t : ℂ[X] := X

/-- $F_2(t, Y + 54000)$, which is Eisenstein at $t$. -/
def eis : ℂ[X][X] :=
  cub (t * (1488 - t)) (t * (201477375 - 106512 * t)) (t * (6549518250000 - 2835810000 * t + t ^ 2))

theorem cubic_t_eq_taylor : cubic t = taylor (-54000 : ℂ[X]) eis := by
  rw [taylor_apply]
  simp only [eis, cubic, cub, add_comp, mul_comp, pow_comp, X_comp, C_comp]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  ring

theorem irreducible_eis : Irreducible eis := by
  have hprime : (Ideal.span {t}).IsPrime := (Ideal.span_singleton_prime X_ne_zero).2 prime_X
  have hdeg : eis.degree = 3 := cub_degree _ _ _
  have hmon : eis.Monic := cub_monic _ _ _
  refine irreducible_of_eisenstein_criterion hprime ?_ ?_ ?_ ?_ hmon.isPrimitive
  · rw [hmon.leadingCoeff]
    exact fun h ↦ hprime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  · intro n hn
    rw [hdeg] at hn
    have hn' : n < 3 := by exact_mod_cast hn
    interval_cases n
    · rw [eis, cub_coeff_zero]; exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
    · rw [eis, cub_coeff_one]; exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
    · rw [eis, cub_coeff_two]; exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
  · rw [hdeg]; norm_num
  · rw [eis, cub_coeff_zero, Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_two]
    intro h
    have h' := (mul_dvd_mul_iff_left (X_ne_zero : t ≠ 0)).1 h
    rw [X_dvd_iff] at h'
    simp at h'

theorem irreducible_cubic_t : Irreducible (cubic t) := by
  have : taylor (-54000 : ℂ[X]) eis = taylorEquiv (-54000 : ℂ[X]) eis := rfl
  rw [cubic_t_eq_taylor, this, MulEquiv.irreducible_iff]
  exact irreducible_eis

/-- **$F_2(t, Y)$ is irreducible over $\mathbb C(t)$.** -/
theorem irreducible_cubic_ratFunc : Irreducible (cubic (RatFunc.X : RatFunc ℂ)) := by
  have := ((cubic_monic t).isPrimitive.irreducible_iff_irreducible_map_fraction_map
    (K := RatFunc ℂ)).1 irreducible_cubic_t
  rwa [cubic_map, RatFunc.algebraMap_X] at this

/-! ### Values of meromorphic functions on $X_0(2)$ -/

section Values

open TauCeti.RiemannSurface

variable {N : ℕ}

/-- `f` takes the finite value `a` at `x`. -/
def HasVal (f : MeromorphicFunction (X0 N)) (x : X0 N) (a : ℂ) : Prop := f x = (a : OnePoint ℂ)

variable {f g : MeromorphicFunction (X0 N)} {x : X0 N} {a b : ℂ}

theorem HasVal.add (hf : HasVal f x a) (hg : HasVal g x b) : HasVal (f + g) x (a + b) :=
  MeromorphicFunction.add_apply_of_eq_coe hf hg

theorem HasVal.sub (hf : HasVal f x a) (hg : HasVal g x b) : HasVal (f - g) x (a - b) :=
  MeromorphicFunction.sub_apply_of_eq_coe hf hg

theorem HasVal.mul (hf : HasVal f x a) (hg : HasVal g x b) : HasVal (f * g) x (a * b) :=
  MeromorphicFunction.mul_apply_of_eq_coe hf hg

theorem HasVal.pow (hf : HasVal f x a) (n : ℕ) : HasVal (f ^ n) x (a ^ n) :=
  MeromorphicFunction.pow_apply_of_eq_coe hf n

theorem HasVal.ofNat (n : ℕ) [n.AtLeastTwo] :
    HasVal (OfNat.ofNat n : MeromorphicFunction (X0 N)) x (OfNat.ofNat n) := by
  rw [HasVal, ← map_ofNat (algebraMap ℂ (MeromorphicFunction (X0 N))) n, MeromorphicFunction.coe_algebraMap]

theorem HasVal.F2R (hf : HasVal f x a) (hg : HasVal g x b) : HasVal (F2R f g) x (F2 a b) := by
  unfold ModularFormsKB.Milne.LevelTwo.F2R ModularFormsKB.Milne.LevelTwo.F2
  have h1 := ((hf.pow 3).add (hg.pow 3)).sub ((hf.pow 2).mul (hg.pow 2))
  have h2 := (((HasVal.ofNat 1488).mul hf).mul hg).mul (hf.add hg)
  have h3 := (HasVal.ofNat 162000).mul ((hf.pow 2).add (hg.pow 2))
  have h4 := ((HasVal.ofNat 40773375).mul hf).mul hg
  have h5 := (HasVal.ofNat 8748000000).mul (hf.add hg)
  exact (((((h1.add h2).sub h3).add h4).add h5).sub (HasVal.ofNat 157464000000000))

end Values

/-! ### The relation and transcendence on $X_0(2)$ -/

open TauCeti.RiemannSurface

/-- The class in $X_0(2)$ of $z \in \mathbb H$. -/
abbrev pt (z : ℍ) : X0 2 := Subgroup.CompactifiedQuotient.ofQuotient (Quotient.mk _ z)

/-- **$F_2(j_X, j_{2,X}) = 0$** in the function field of $X_0(2)$. -/
theorem F2R_eq_zero {jX jNX : MeromorphicFunction (X0 2)} (hj : IsJOnX0 2 jX)
    (hjN : IsJNOnX0 2 (by norm_num) jNX) : F2R jX jNX = 0 := by
  set E := F2R jX jNX
  have hval : ∀ z : ℍ, E (pt z) = ((0 : ℂ) : OnePoint ℂ) := by
    intro z
    have := HasVal.F2R (hj z) (hjN z)
    rw [HasVal] at this
    rw [this]
    exact congrArg (fun w : ℂ => (w : OnePoint ℂ)) (F2_j_two_eq_zero z)
  have hU : IsOpen (Set.range (Subgroup.CompactifiedQuotient.ofQuotient
      (Γ := (CongruenceSubgroup.Gamma0 2).map sl2zToPSL2R))) :=
    Subgroup.CompactifiedQuotient.isOpen_range_ofQuotient
  have hconst : EventuallyConst E (nhds (pt UpperHalfPlane.I)) := by
    refine eventuallyConst_iff_exists_eventuallyEq.2 ⟨((0 : ℂ) : OnePoint ℂ), ?_⟩
    filter_upwards [hU.mem_nhds ⟨_, rfl⟩] with y hy
    obtain ⟨p, rfl⟩ := hy
    induction p using Quotient.inductionOn with
    | h z => exact hval z
  ext y
  rw [apply_eq_of_eventuallyConst E.mdifferentiable hconst y, hval, MeromorphicFunction.coe_zero]

/-- **$j_X$ is transcendental over $\mathbb C$**: it takes the values $0 = j(\rho)$ and $1728 = j(i)$. -/
theorem transcendental_jX {jX : MeromorphicFunction (X0 2)} (hj : IsJOnX0 2 jX) : Transcendental ℂ jX := by
  intro halg
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible halg.isIntegral)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one ℂ jX hdeg
  have h1 := hj ρ
  have h2 := hj UpperHalfPlane.I
  rw [← hc, MeromorphicFunction.coe_algebraMap] at h1 h2
  rw [j_ρ] at h1
  rw [j_I] at h2
  have := h1.symm.trans h2
  norm_num [OnePoint.coe_eq_coe] at this

/-! ### The main theorem -/

/-- **Milne, Example 6.2**: the modular polynomial of level two is `modularPolynomialTwo`. -/
@[kb "milne2017mf" "Section 6, Example 6.2 (pdf p. 90): proved"]
theorem modularEquationLevelTwo : ModularEquationLevelTwo := by
  refine ⟨fun jX jNX hj hjN ↦ ?_⟩
  set K := IntermediateField.adjoin ℂ {jX}
  have htr := transcendental_jX hj
  let e := RatFunc.algEquivOfTranscendental jX htr
  have he : e RatFunc.X = IntermediateField.AdjoinSimple.gen ℂ jX := by
    rw [← RatFunc.algEquivOfTranscendental_symm_gen jX htr]
    exact e.apply_symm_apply _
  have hirr : Irreducible (cubic (IntermediateField.AdjoinSimple.gen ℂ jX)) := by
    have h1 : (cubic (RatFunc.X : RatFunc ℂ)).map (e : RatFunc ℂ →+* K) =
        cubic (IntermediateField.AdjoinSimple.gen ℂ jX) := by
      rw [cubic_map]
      exact congrArg cubic he
    rw [← h1]
    exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv (e : RatFunc ℂ ≃+* K))).2 irreducible_cubic_ratFunc
  have hroot : aeval jNX (cubic (IntermediateField.AdjoinSimple.gen ℂ jX)) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, cubic_map, IntermediateField.AdjoinSimple.algebraMap_gen, eval_cubic,
      F2R_eq_zero hj hjN]
  have hmin := minpoly.eq_of_irreducible_of_monic hirr hroot (cubic_monic _)
  unfold IsModularPolynomial
  rw [← hmin, cubic_map, IntermediateField.AdjoinSimple.algebraMap_gen, eval₂_modularPolynomialTwo]

end ModularFormsKB.Milne.LevelTwo
