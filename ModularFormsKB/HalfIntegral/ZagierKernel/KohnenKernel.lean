/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
-/
import ModularFormsKB.HalfIntegral.ZagierKernel.Unfolding
import ModularFormsKB.HalfIntegral.KohnenLevelOneAdjoint
import ModularFormsKB.HalfIntegral.QExpUnique
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Kohnen–Zagier through Zagier's kernel (headline H5)

Kohnen–Zagier 1981 `kohnenzagier1981` (§II [unverified]) put the twisted kernels $f_{k,D,|D|m}$ (`zagierKernelChi`) into
one function of two variables,
$$ \Omega(z, \tau) = \sum_{m} c_{k,D}^{-1}\, m^{k-1/2}\, f_{k,D,|D|m}(z)\, e^{2\pi i m\tau},\qquad
   c_{k,D} = (-1)^{\lfloor k/2\rfloor}\,|D|^{1/2-k}\,\pi\binom{2k-2}{k-1}\,2^{2-3k}, $$
the sum over the indices $m \ge 1$ with $(-1)^k m \equiv 0, 1 \bmod 4$. It is a cusp form of weight $2k$ in $z$ and lies in
Kohnen's plus space $S^+_{k+1/2}(4)$ in $\tau$, and it is the kernel of the adjoint $\mathcal S_D^*$ of the $D$-th Shimura
lift: $\mathcal S_D^*G(\tau) = \langle \Omega(\cdot, -\bar\tau), G\rangle$, whose $m$-th coefficient is
$c_{k,D}^{-1}m^{k-1/2}\langle f_{k,D,|D|m}, G\rangle$ (`kohnenKernelCoeff`). That is the named input
`KohnenKernelModular`.

**Proved here.**
- `kohnenAdjoint_unique`: two adjoints of the $D$-th lift (`KohnenAdjoint`) agree, when the lift maps $S^+$ to level one
  (`KohnenDLift`); the Petersson product is definite on $S^+$ (`plusInnerCore`).
- `kohnenKernelConst_mul_unfold_mul_square`: the constants $c_{k,D}^{-1}|D|^{k-1/2}$, $U_{k,D^2}$ (`zagierUnfoldConst`) and
  the square-discriminant constant (`squareCycleConst`) multiply to $\frac{(k-1)!}{\pi^k}|D|^{k-1/2}$, the constant of
  Theorem 1 (`kzConstant`). The three are taken from (or derived along) Kohnen–Zagier's §II independently of Theorem 1,
  so this is a check of their normalizations.
- `kohnenAdjointCoeff_of_kernel`: `KohnenAdjointCoeff` for **every** adjoint, from `KohnenKernelModular`,
  `ZagierKernelUnfolding` and `KohnenSquareCycle`.
- **H5**: `kohnenZagier_of_kernel`, `waldspurgerPlus_of_kernel`: `KohnenZagier` and `WaldspurgerPlus` for the theta
  multiplier from `KohnenTraceIdentity`, the three kernel inputs and wave 1's two inputs (`KohnenTPlusFourStable`,
  `PlusHeckeSelfAdjoint`). In weight $k = 1$ the statements
  are vacuous ($S_2(\mathrm{SL}_2(\mathbb Z)) = 0$), so no kernel input is used there.
-/

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup UpperHalfPlane ModularForm
open scoped Real

/-- **Kohnen–Zagier's normalization of the kernel** $\Omega$: the coefficient $c_{k,D}^{-1}m^{k-1/2}$ of $f_{k,D,|D|m}$,
$$ c_{k,D}^{-1} = (-1)^{\lfloor k/2\rfloor}\,|D|^{k-1/2}\,\frac{2^{3k-2}}{\pi\binom{2k-2}{k-1}} $$
(Kohnen–Zagier 1981 `kohnenzagier1981`, §II [unverified]), with $2^{3k-2} = 8^k/4$. -/
noncomputable def kohnenKernelConst (k : ℕ) (D : ℤ) (m : ℕ) : ℝ :=
  (-1) ^ (k / 2) * (D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) * (8 ^ k / 4) /
    (π * ((2 * k - 2).choose (k - 1) : ℝ)) * (m : ℝ) ^ ((k : ℝ) - 1 / 2)

open Classical in
/-- **The $m$-th coefficient of $\mathcal S_D^*G = \langle\Omega(\cdot,-\bar\tau), G\rangle$**:
$c_{k,D}^{-1}m^{k-1/2}\langle f_{k,D,|D|m}, G\rangle$ for an index $m$ (`KernelIndex`), $0$ otherwise. -/
noncomputable def kohnenKernelCoeff (k : ℕ) (D : ℤ) (G : ℍ → ℂ) (m : ℕ) : ℂ :=
  if KernelIndex k m then
    (kohnenKernelConst k D m : ℂ) * peterssonOne k (zagierKernelChi k D (D.natAbs * m : ℕ)) G
  else 0

/-- **Kohnen–Zagier's kernel is modular in $\tau$ and is the kernel of the adjoint** (Kohnen–Zagier 1981
`kohnenzagier1981`, §II, Prop. and its proof [unverified]): for $k \ge 2$, $D$ a fundamental discriminant with
$(-1)^kD > 0$ and $G \in S_{2k}(\mathrm{SL}_2(\mathbb Z))$, the $q$-series with the coefficients `kohnenKernelCoeff k D G`
is the expansion of a form $g \in S^+_{k+1/2}(4)$ (the theta multiplier), and $g$ is the value at $G$ of the adjoint of
the $D$-th Shimura lift: $\langle \mathcal S_Dg', G\rangle = \langle g', g\rangle$ for every $g' \in S^+_{k+1/2}(4)$ whose lift
$\mathcal S_Dg'$ (coefficients `kzLiftCoeff`) is the level one form $G'$. The Petersson products are `peterssonOne` and
`peterssonFour`, as in `KohnenAdjoint`. Loose end LE-MF-0311. -/
@[kb "kohnenzagier1981" "§II: Ω(z,τ) = Σ c_{k,D}^{-1} m^{k-1/2} f_{k,D,|D|m}(z) e(mτ) lies in S⁺_{k+1/2}(4) in τ and is the kernel of S_D^* [unverified]"]
structure KohnenKernelModular (k : ℕ) : Prop where
  kernel : 2 ≤ k → ∀ D : ℤ, KohnenDisc k D → ∀ G : CuspForm 𝒮ℒ (2 * k : ℕ),
    ∃ g ∈ thetaMultiplierSystem.plusCuspForms k 1 1, Abstract.HasQExp g (kohnenKernelCoeff k D G) ∧
      ∀ g' ∈ thetaMultiplierSystem.plusCuspForms k 1 1, ∀ c' : ℕ → ℂ, Abstract.HasQExp g' c' →
        ∀ (G' : CuspForm 𝒮ℒ (2 * k : ℕ)) (b' : ℕ → ℂ), Abstract.HasQExp G' b' →
          (∀ n, 1 ≤ n → b' n = kzLiftCoeff k D c' n) → peterssonOne k G' G = peterssonFour k g' g

/-! ### The constants -/

/-- **The three constants of §II multiply to the constant of Theorem 1:**
$c_{k,D}^{-1}|D|^{k-1/2}\cdot U_{k,D^2}\cdot(-1)^{\lfloor k/2\rfloor}|D|^{k-1/2}\frac{(k-1)!}{(2\pi)^k} = \frac{(k-1)!}{\pi^k}|D|^{k-1/2}$. -/
theorem kohnenKernelConst_mul_unfold_mul_square (k : ℕ) (D : ℤ) (hD : D ≠ 0) :
    kohnenKernelConst k D D.natAbs * zagierUnfoldConst k (D.natAbs * D.natAbs) * squareCycleConst k D =
      (k - 1).factorial / π ^ k * (D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) := by
  set x : ℝ := (D.natAbs : ℝ) with hx
  have hx0 : 0 < x := by rw [hx]; exact_mod_cast Int.natAbs_pos.2 hD
  set A : ℝ := x ^ ((k : ℝ) - 1 / 2) with hA
  have hA0 : 0 < A := Real.rpow_pos_of_pos hx0 _
  have hU : ((D.natAbs * D.natAbs : ℕ) : ℝ) ^ ((1 : ℝ) / 2 - k) = (A * A)⁻¹ := by
    rw [Nat.cast_mul, ← hx, Real.mul_rpow hx0.le hx0.le, hA,
      show (1 : ℝ) / 2 - k = -((k : ℝ) - 1 / 2) by ring, Real.rpow_neg hx0.le, mul_inv]
  have hB : (0 : ℝ) < ((2 * k - 2).choose (k - 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hε : (-1 : ℝ) ^ (k / 2 * 2) = 1 := by
    rw [mul_comm, pow_mul, neg_one_sq, one_pow]
  have h8 : (8 : ℝ) ^ k = 2 ^ k * 4 ^ k := by rw [← mul_pow]; norm_num
  simp only [kohnenKernelConst, zagierUnfoldConst, squareCycleConst, hU, ← hx, ← hA]
  have hπ : (0 : ℝ) < π := Real.pi_pos
  field_simp
  rw [mul_pow, h8]
  linear_combination (π ^ k * 2 ^ k * 4 ^ k) * hε

/-! ### Uniqueness of the adjoint -/

/-- **The adjoint of the $D$-th lift is unique**: if the lift maps $S^+_{k+1/2}(4)$ to level one (`KohnenDLift`), any two
functions $g_1, g_2 \in S^+$ with $\langle \mathcal S_Dg', G\rangle = \langle g', g_i\rangle$ for all $g' \in S^+$ are equal. -/
theorem kohnenAdjoint_unique (M : MultiplierSystem) (k : ℕ) (hk : 1 ≤ k) {D : ℤ} (hL : KohnenDLift M k D)
    (G : CuspForm 𝒮ℒ (2 * k : ℕ)) {g₁ g₂ : ℍ → ℂ} (h₁ : g₁ ∈ M.plusCuspForms k 1 1) (h₂ : g₂ ∈ M.plusCuspForms k 1 1)
    (hadj₁ : ∀ g' ∈ M.plusCuspForms k 1 1, ∀ c' : ℕ → ℂ, Abstract.HasQExp g' c' →
      ∀ (G' : CuspForm 𝒮ℒ (2 * k : ℕ)) (b' : ℕ → ℂ), Abstract.HasQExp G' b' →
        (∀ n, 1 ≤ n → b' n = kzLiftCoeff k D c' n) → peterssonOne k G' G = peterssonFour k g' g₁)
    (hadj₂ : ∀ g' ∈ M.plusCuspForms k 1 1, ∀ c' : ℕ → ℂ, Abstract.HasQExp g' c' →
      ∀ (G' : CuspForm 𝒮ℒ (2 * k : ℕ)) (b' : ℕ → ℂ), Abstract.HasQExp G' b' →
        (∀ n, 1 ≤ n → b' n = kzLiftCoeff k D c' n) → peterssonOne k G' G = peterssonFour k g' g₂) :
    g₁ = g₂ := by
  let c := plusInnerCore M k
  let _ : NormedAddCommGroup (M.plusCuspForms k 1 1) := c.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ (M.plusCuspForms k 1 1) := InnerProductSpace.ofCore c.toCore
  have key : (⟨g₁, h₁⟩ : M.plusCuspForms k 1 1) = ⟨g₂, h₂⟩ := by
    refine ext_inner_left ℂ fun v ↦ ?_
    obtain ⟨c', hc'⟩ := exists_hasQExp_plus v
    obtain ⟨G', hG'⟩ := hL.lift hk v.1 v.2 c' hc'
    change peterssonFour k v.1 g₁ = peterssonFour k v.1 g₂
    rw [← hadj₁ v.1 v.2 c' hc' G' _ hG' (fun n _ ↦ rfl), ← hadj₂ v.1 v.2 c' hc' G' _ hG' (fun n _ ↦ rfl)]
  exact congrArg Subtype.val key

/-! ### The coefficient of the adjoint -/

/-- **`KohnenAdjointCoeff` for every adjoint**, from the kernel (`KohnenKernelModular`), the unfolding
(`ZagierKernelUnfolding`) and the square-discriminant cycle integrals (`KohnenSquareCycle`), for $k \ge 2$ and $D$ with
`KohnenDLift`. -/
theorem kohnenAdjointCoeff_of_kernel (k : ℕ) (hk : 2 ≤ k) (hK : KohnenKernelModular k)
    (hU : ZagierKernelUnfolding k) (hQ : KohnenSquareCycle k) {D : ℤ} (hD : KohnenDisc k D)
    (hL : KohnenDLift thetaMultiplierSystem k D) (Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ)
    (hS : KohnenAdjoint thetaMultiplierSystem k D Sstar) : KohnenAdjointCoeff thetaMultiplierSystem k D Sstar := by
  refine ⟨fun F b hb _ _ L hLs c' hc' ↦ ?_⟩
  obtain ⟨g, hg, hgq, hgadj⟩ := hK.kernel hk D hD F
  have hEq : Sstar F = g := kohnenAdjoint_unique thetaMultiplierSystem k (by omega) hL F (hS.mem_plus F) hg
    (fun g' hg' c'' hc'' G' b' hb' hbc ↦ hS.adjoint g' hg' c'' hc'' G' b' hb' hbc F) hgadj
  rw [hEq] at hc'
  have hc : c' = kohnenKernelCoeff k D F := Abstract.hasQExp_unique hc' hgq
  have hidx := kernelIndex_natAbs hD
  have hD0 : D ≠ 0 := by rintro rfl; exact absurd hD.2 (by simp)
  rw [hc, kohnenKernelCoeff, if_pos hidx, hU.unfold hk D hD _ hidx F, hQ.square hk D hD F b hb L hLs, kzConstant]
  have key := kohnenKernelConst_mul_unfold_mul_square k D hD0
  have key' : (kohnenKernelConst k D D.natAbs : ℂ) * (zagierUnfoldConst k (D.natAbs * D.natAbs) : ℂ) *
      (squareCycleConst k D : ℂ) = ((k - 1).factorial / (π : ℂ) ^ k) * ((D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) := by
    rw [← ofReal_mul, ← ofReal_mul, key]
    push_cast
    ring
  rw [← key']
  ring

/-! ### H5 -/

/-- In weight $2$ there are no nonzero level one cusp forms, so a normalized $F$ does not exist. -/
theorem not_hasQExp_normalized_two (F : CuspForm 𝒮ℒ ((2 * 1 : ℕ) : ℤ)) (b : ℕ → ℂ) (hb : Abstract.HasQExp F b)
    (h1 : b 1 = 1) : False := by
  apply cuspForm_ne_zero_of_coeff_one F hb h1
  have h0 := (rank_zero_iff_forall_zero.mp levelOne_weight_two_rank_zero) (CuspForm.toModularFormₗ F)
  ext τ
  have := congrArg (fun f : ModularForm 𝒮ℒ 2 ↦ f τ) h0
  simpa using this

/-- **`KohnenAdjointCoeff` for every adjoint and every admissible $D$**, in every weight $k \ge 1$ (vacuous at $k = 1$). -/
theorem hcoeff_of_kernel (k : ℕ) (hk1 : 1 ≤ k) (h : KohnenTraceIdentity k)
    (hT : KohnenTPlusFourStable thetaMultiplierSystem k)
    (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k) (hQ : KohnenSquareCycle k) :
    ∀ D, KohnenDisc k D → ∀ Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ,
      KohnenAdjoint thetaMultiplierSystem k D Sstar → KohnenAdjointCoeff thetaMultiplierSystem k D Sstar := by
  intro D hD Sstar hS
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by omega
    exact ⟨fun F b hb h1 _ _ _ _ _ ↦ (not_hasQExp_normalized_two F b hb h1).elim⟩
  · exact kohnenAdjointCoeff_of_kernel k hk hK hU hQ hD (kohnenDLift_of_trace h hT hD) Sstar hS

/-- **H5: the Kohnen–Zagier formula through Zagier's kernel**, for the theta multiplier, from `KohnenTraceIdentity`, the
kernel inputs `KohnenKernelModular`, `ZagierKernelUnfolding`, `KohnenSquareCycle`, and wave 1's `KohnenTPlusFourStable`
and `PlusHeckeSelfAdjoint`. -/
@[kb "kohnenzagier1981" "Thm. 1 through Zagier's kernel: from the trace identity, the kernel Ω, the unfolding and the square cycle integrals [unverified]"]
theorem kohnenZagier_of_kernel (k : ℕ) (h : KohnenTraceIdentity k)
    (hT : KohnenTPlusFourStable thetaMultiplierSystem k) (hS : PlusHeckeSelfAdjoint k)
    (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k) (hQ : KohnenSquareCycle k) :
    KohnenZagier thetaMultiplierSystem k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact ⟨fun hk ↦ absurd hk (by norm_num)⟩
  · exact kohnenZagier_of_trace' k h hT hS (hcoeff_of_kernel k hk1 h hT hK hU hQ)

/-- **H5: Waldspurger's theorem on the plus space through Zagier's kernel**, from the inputs of
`kohnenZagier_of_kernel`. -/
@[kb "kohnenzagier1981" "Waldspurger's theorem on the plus space through Zagier's kernel [unverified]"]
theorem waldspurgerPlus_of_kernel (k : ℕ) (h : KohnenTraceIdentity k)
    (hT : KohnenTPlusFourStable thetaMultiplierSystem k) (hS : PlusHeckeSelfAdjoint k)
    (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k) (hQ : KohnenSquareCycle k) :
    WaldspurgerPlus thetaMultiplierSystem k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact ⟨fun hk ↦ absurd hk (by norm_num)⟩
  · exact waldspurgerPlus_of_trace' k h hT hS (hcoeff_of_kernel k hk1 h hT hK hU hQ)

end ModularFormsKB.HalfIntegral
