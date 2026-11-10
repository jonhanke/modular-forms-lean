import TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.OrderOfConductor
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Basic
import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
import ModularFormsKB.Miyake.CongruenceModularGroups
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.LinearAlgebra.Unimodular
import ModularFormsKB.Citation
/-!
# Miyake §6.7–§6.8: class numbers of quadratic orders, the index of $\mathbb Z[\alpha]$, and the volume

Miyake, *Modular Forms* (Springer 1989), §6.7–§6.8, pp. 257–262.

* **Theorem 6.7.2 (1)** (p. 257): for an order $\mathfrak r$ of index $n$ in a quadratic field $K$
  of discriminant $d$,
  $h(\mathfrak r) = h_K\, n \prod_{p \mid n}(1 - (\tfrac dp)p^{-1}) / [\mathfrak r_0^\times : \mathfrak r^\times]$.
  Miyake states it for imaginary $K$, where his idelic $h(\mathfrak r)$ is the order of the Picard
  group $\operatorname{Pic}\mathfrak r$; the formula for $\#\operatorname{Pic}$ holds for every
  quadratic field. Proved from Tau Ceti's `card_pic_intAddMulOrder_eq` (every order is
  $\mathbb Z + n\,\mathfrak r_0$, `eq_intAddMulOrder_index`).
* **Lemma 6.8.1** (p. 259): for $\alpha \in \mathfrak r_0 \setminus \mathbb Z$ with minimal
  polynomial $X^2 - tX + n$ and $t^2 - 4n = m^2 d$, $m > 0$, $[\mathfrak r_0 : \mathbb Z[\alpha]] = m$.
* **Theorem 6.8.3 for $B = M_2(\mathbb Q)$** (p. 262): $v(\Gamma_0(N)\backslash\mathbb H)
  = \frac{\pi}{3} N \prod_{p\mid N}(1 + p^{-1})$, from Tau Ceti's covolume $\pi/3$ of
  $SL_2(\mathbb Z)$ and Theorem 4.2.5 (2).
-/

open NumberField TauCeti.GlobalNumberFields TauCeti.Multiquadratic CongruenceSubgroup MeasureTheory
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave2B

variable {K : Type*} [Field K] [NumberField K]

/-- **Miyake, Theorem 6.7.2 (1).** For an order $O$ of index $n$ in a quadratic field $K$ with
discriminant $d$ and quadratic character $\chi_d = (\tfrac d\cdot)$,
$$\#\operatorname{Pic} O = \frac{h_K\, n}{[\mathcal O_K^\times : O^\times]}
  \prod_{p \mid n}\Big(1 - \frac{\chi_d(p)}{p}\Big).$$ -/
@[kb "miyake1989" "Theorem 6.7.2 (1), p. 257"]
theorem card_pic_order (hK : Module.finrank ℚ K = 2) (O : NumberFieldOrder K) :
    (Nat.card (Pic O) : ℚ) =
      Nat.card (ClassGroup (𝓞 K)) * O.index /
          (Units.map (O.toRingOfIntegers.val : O.toRingOfIntegers →* 𝓞 K)).range.index *
        ∏ p ∈ O.index.primeFactors,
          (1 - (fundamentalDiscriminantChar (NumberField.discr K) (isFundamentalDiscr_discr hK) p :
            ℚ) / p) := by
  have h := NumberFieldOrder.card_pic_intAddMulOrder_eq (F := ℚ) hK O.index
  rw [← NumberFieldOrder.eq_intAddMulOrder_index hK O] at h
  exact h

/-! ### A basis $\{1, \omega\}$ of the ring of integers of a quadratic field

For a $\mathbb Z$-basis $b$ of $\mathcal O_K$ with $b_0 = 1$ and $\omega = b_1$, write
$\omega^2 = v + u\omega$; then $\operatorname{disc} K = u^2 + 4v$. -/

section QuadBasis

variable (b : Module.Basis (Fin 2) ℤ (𝓞 K)) (hb : b 0 = 1)
include hb

/-- Every $x \in \mathcal O_K$ is $x_0 + x_1\omega$ in the coordinates of $b$. -/
lemma quadBasis_eq_coord (x : 𝓞 K) : x = (b.repr x 0 : 𝓞 K) + b.repr x 1 * b 1 := by
  conv_lhs => rw [← b.sum_repr x]
  simp [Fin.sum_univ_two, hb, zsmul_eq_mul]

/-- The coordinates of $A + B\omega$ are $(A, B)$. -/
lemma quadBasis_repr_add_mul (A B : ℤ) : b.repr ((A : 𝓞 K) + B * b 1) = Finsupp.single 0 A + Finsupp.single 1 B := by
  have : ((A : 𝓞 K) + B * b 1) = A • b 0 + B • b 1 := by simp [hb, zsmul_eq_mul]
  rw [this, map_add, map_zsmul, map_zsmul, b.repr_self, b.repr_self]
  simp

/-- The first coordinate of $A + B\omega$ is $A$. -/
lemma quadBasis_repr_add_mul_zero (A B : ℤ) : b.repr ((A : 𝓞 K) + B * b 1) 0 = A := by
  rw [quadBasis_repr_add_mul b hb]; simp

/-- The second coordinate of $A + B\omega$ is $B$. -/
lemma quadBasis_repr_add_mul_one (A B : ℤ) : b.repr ((A : 𝓞 K) + B * b 1) 1 = B := by
  rw [quadBasis_repr_add_mul b hb]; simp

/-- $\omega^2 = v + u\omega$ with $v, u$ the coordinates of $\omega^2$. -/
lemma quadBasis_sq_eq : b 1 * b 1 = ((b.repr (b 1 * b 1) 0 : ℤ) : 𝓞 K) + b.repr (b 1 * b 1) 1 * b 1 :=
  quadBasis_eq_coord b hb _

/-- The second coordinate of a product: $(xy)_1 = x_0y_1 + x_1y_0 + x_1y_1u$. -/
lemma quadBasis_repr_mul_one (x y : 𝓞 K) : b.repr (x * y) 1 =
    b.repr x 0 * b.repr y 1 + b.repr x 1 * b.repr y 0 +
      b.repr x 1 * b.repr y 1 * b.repr (b 1 * b 1) 1 := by
  set u := b.repr (b 1 * b 1) 1
  set v := b.repr (b 1 * b 1) 0
  have hω := quadBasis_sq_eq b hb
  have hxy : x * y = ((b.repr x 0 * b.repr y 0 + b.repr x 1 * b.repr y 1 * v : ℤ) : 𝓞 K) +
      ((b.repr x 0 * b.repr y 1 + b.repr x 1 * b.repr y 0 +
        b.repr x 1 * b.repr y 1 * u : ℤ) : 𝓞 K) * b 1 := by
    rw [quadBasis_eq_coord b hb x, quadBasis_eq_coord b hb y]
    simp only [quadBasis_repr_add_mul_zero b hb, quadBasis_repr_add_mul_one b hb]
    push_cast
    linear_combination ((b.repr x 1 : 𝓞 K) * b.repr y 1) * hω
  rw [hxy, quadBasis_repr_add_mul_one b hb]

/-- The trace $\operatorname{Tr}(x) = 2x_0 + u x_1$. -/
lemma quadBasis_trace_eq (x : 𝓞 K) : Algebra.trace ℤ (𝓞 K) x =
    2 * b.repr x 0 + b.repr (b 1 * b 1) 1 * b.repr x 1 := by
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, hb, mul_one,
    quadBasis_repr_mul_one b hb]
  simp [hb, b.repr_self]
  ring

/-- The discriminant of $K$ is $u^2 + 4v$ (the discriminant of the basis $1, \omega$). -/
lemma quadBasis_discr_eq : NumberField.discr K =
    b.repr (b 1 * b 1) 1 ^ 2 + 4 * b.repr (b 1 * b 1) 0 := by
  rw [← NumberField.discr_eq_discr K b, Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, quadBasis_trace_eq b hb, hb, one_mul,
    mul_one]
  simp [b.repr_self, ← hb]
  ring

end QuadBasis

/-- **Miyake, Lemma 6.8.1.** Let $K$ be a quadratic field with discriminant $d$ and ring of
integers $\mathfrak r_0$, $\alpha \in \mathfrak r_0 \setminus \mathbb Z$ with minimal polynomial
$X^2 - tX + n$, and $m > 0$ with $t^2 - 4n = m^2 d$. Then $[\mathfrak r_0 : \mathbb Z[\alpha]] = m$. -/
@[kb "miyake1989" "Lemma 6.8.1, p. 259"]
theorem index_adjoin_ringOfIntegers (hK : Module.finrank ℚ K = 2) (α : 𝓞 K)
    (hα : α ∉ Set.range (algebraMap ℤ (𝓞 K))) {t n : ℤ}
    (hmin : α ^ 2 - t • α + algebraMap ℤ (𝓞 K) n = 0) {m : ℕ} (hm : 0 < m)
    (hd : t ^ 2 - 4 * n = (m : ℤ) ^ 2 * NumberField.discr K) :
    (Algebra.adjoin ℤ {α}).toSubmodule.toAddSubgroup.index = m := by
  obtain ⟨b, hb⟩ := (Module.Free.isUnimodular_one (R := ℤ) (A := 𝓞 K)).exists_basis_zero_eq
    (by rw [NumberField.RingOfIntegers.rank, hK])
  set u := b.repr (b 1 * b 1) 1 with hu
  set v := b.repr (b 1 * b 1) 0 with hv
  set p := b.repr α 0 with hp
  set c := b.repr α 1 with hc
  have hω := quadBasis_sq_eq b hb
  have hαe := quadBasis_eq_coord b hb α
  have hc0 : c ≠ 0 := by
    intro h0
    apply hα
    refine ⟨p, ?_⟩
    rw [hαe, ← hc, h0]; simp [hp]
  -- coordinates of the minimal-polynomial relation
  have hrel : ((p ^ 2 + c ^ 2 * v - t * p + n : ℤ) : 𝓞 K) +
      ((2 * p * c + c ^ 2 * u - t * c : ℤ) : 𝓞 K) * b 1 = 0 := by
    rw [← hmin, hαe]
    push_cast
    simp only [zsmul_eq_mul, algebraMap_int_eq, eq_intCast]
    linear_combination (-(c : 𝓞 K) ^ 2) * hω
  have h1 := congrArg (fun x ↦ b.repr x 1) hrel
  have h0 := congrArg (fun x ↦ b.repr x 0) hrel
  simp only [quadBasis_repr_add_mul_one b hb, quadBasis_repr_add_mul_zero b hb, map_zero, Finsupp.coe_zero,
    Pi.zero_apply] at h1 h0
  have ht : t = 2 * p + c * u := by
    have : c * (2 * p + c * u - t) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hc0
    · linarith
  have hdisc : t ^ 2 - 4 * n = c ^ 2 * NumberField.discr K := by
    rw [quadBasis_discr_eq b hb, ← hu, ← hv]
    subst ht
    linear_combination (-4) * h0
  have hmc : (m : ℤ) = |c| := by
    have hD := NumberField.discr_ne_zero K
    have : (m : ℤ) ^ 2 = c ^ 2 := mul_right_cancel₀ hD (hd.symm.trans hdisc)
    have h2 := (sq_eq_sq_iff_abs_eq_abs _ _).mp this
    rwa [abs_of_nonneg (by positivity)] at h2
  -- the order `ℤ[α]` is `{x | c ∣ coord₁ x}`
  have hmem : ∀ x : 𝓞 K, x ∈ Algebra.adjoin ℤ {α} ↔ c ∣ b.repr x 1 := by
    intro x
    constructor
    · intro hx
      let S : Subalgebra ℤ (𝓞 K) :=
        { carrier := {z | c ∣ b.repr z 1}
          mul_mem' := by
            intro z w hz hw
            simp only [Set.mem_setOf_eq] at *
            rw [quadBasis_repr_mul_one b hb]
            exact dvd_add (dvd_add (dvd_mul_of_dvd_right hw _) (dvd_mul_of_dvd_left hz _))
              (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hz _) _)
          add_mem' := by
            intro z w hz hw
            simp only [Set.mem_setOf_eq, map_add, Finsupp.coe_add, Pi.add_apply] at *
            exact dvd_add hz hw
          algebraMap_mem' := by
            intro r
            simp only [Set.mem_setOf_eq, algebraMap_int_eq, eq_intCast]
            have : ((r : 𝓞 K)) = (r : 𝓞 K) + (0 : ℤ) * b 1 := by simp
            rw [this, quadBasis_repr_add_mul_one b hb]
            exact dvd_zero _ }
      have hle : Algebra.adjoin ℤ {α} ≤ S := by
        rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
        exact dvd_refl c
      exact hle hx
    · rintro ⟨k, hk⟩
      have hx := quadBasis_eq_coord b hb x
      have : x = (b.repr x 0 : 𝓞 K) + (k : 𝓞 K) * (α - (p : 𝓞 K)) := by
        conv_lhs => rw [hx]
        rw [hk]
        conv_rhs => rw [hαe]
        rw [hc, hp]
        push_cast
        ring
      rw [this]
      exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _)
        (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
          (Subalgebra.sub_mem _ (Algebra.subset_adjoin rfl) (Subalgebra.algebraMap_mem _ _)))
  haveI : NeZero m := ⟨hm.ne'⟩
  let f : 𝓞 K →+ ZMod m := (Int.castAddHom (ZMod m)).comp
    ((Finsupp.applyAddHom 1).comp b.repr.toLinearMap.toAddMonoidHom)
  have hf : ∀ x, f x = (b.repr x 1 : ZMod m) := fun x ↦ rfl
  have hker : (Algebra.adjoin ℤ {α}).toSubmodule.toAddSubgroup = f.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, hf, ZMod.intCast_zmod_eq_zero_iff_dvd, hmc, abs_dvd]
    exact hmem x
  rw [hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top_of_surjective]
  · simp
  · intro z
    refine ⟨(z.val : ℤ) • b 1, ?_⟩
    rw [hf, map_zsmul, b.repr_self]
    simp

/-- The kernel $\{\pm 1\}$ of $SL_2(\mathbb Z) \to PSL_2(\mathbb R)$ lies in $\Gamma_0(N)$. -/
lemma ker_sl2zToPSL2R_le_Gamma0 (N : ℕ) : sl2zToPSL2R.ker ≤ Gamma0 N := by
  intro g hg
  rw [sl2zToPSL2R_ker] at hg
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  rw [Gamma0_mem, ← hr, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide)]
  simp

/-- **Miyake, Theorem 6.8.3, for $B = M_2(\mathbb Q)$** ($d_B = 1$, $\Gamma_R = \Gamma_0(N)$): the
hyperbolic area of $\Gamma_0(N)\backslash\mathbb H$ is $\frac{\pi}{3}N\prod_{p\mid N}(1 + p^{-1})$. -/
@[kb "miyake1989" "Theorem 6.8.3, p. 262 (B = M2(Q))"]
theorem covolume_Gamma0 (N : ℕ) [NeZero N] :
    MeasureTheory.covolume ((Gamma0 N).map sl2zToPSL2R) UpperHalfPlane =
      ENNReal.ofReal (Real.pi / 3 * (N * ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℝ)))) := by
  have hle := (Gamma0 N).map_sl2zToPSL2R_le_range_psl2zToPSL2R
  rw [covolume_eq_card_mul_covolume hle, TauCeti.ModularGroup.covolume_psl2zToPSL2RRange]
  have hrel : ((Gamma0 N).map sl2zToPSL2R).relIndex psl2zToPSL2R.range = (Gamma0 N).index := by
    rw [Subgroup.relIndex_map_sl2zToPSL2R, Subgroup.withCenter_def, ← sl2zToPSL2R_ker,
      sup_eq_left.mpr (ker_sl2zToPSL2R_le_Gamma0 N)]
  rw [ENat.card_eq_coe_natCard, ← Subgroup.index, ← Subgroup.relIndex, hrel]
  have hq : ((Gamma0 N).index : ℝ) = N * ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℝ)) := by
    have := congrArg (fun x : ℚ ↦ (x : ℝ)) (ModularFormsKB.Miyake.index_Gamma0 N)
    simpa using this
  rw [← hq, mul_comm, ENNReal.ofReal_mul (by positivity)]
  simp

end ModularFormsKB.Miyake.Wave2B
