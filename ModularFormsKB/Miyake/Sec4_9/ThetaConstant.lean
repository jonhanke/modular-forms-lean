import ModularFormsKB.Citation
import ModularFormsKB.HalfIntegral.GaussSign
import TauCeti.NumberTheory.QuadraticForm.GaussSum
import TauCeti.Data.Matrix.DotProduct

/-!
# Miyake Lemma 4.9.2: the constant of the theta transformation formula

Miyake, *Modular Forms* (Springer 1989), §4.9, (4.9.16) and Lemma 4.9.2, p. 190.

Let `A ∈ M_r(ℤ)` be symmetric and positive definite, `D = det A`, `N` a positive integer and
`h ∈ ℤ^r` with (4.9.1) `N A⁻¹ ∈ M_r(ℤ)` and (4.9.2) `A h ∈ N ℤ^r`. For
`γ = [a b; c d] ∈ SL₂(ℤ)` with `b ≡ 0 mod 2`, `c ≡ 0 mod 2N` and `d < 0`, Miyake puts (4.9.16)

  `M(γ) = |d|^{-r/2} (-sgn(c) i)^r Σ_{g ∈ ℤ^r / dNℤ^r, g ≡ h mod N} e(-b A[g] / 2|d|N²)`

and Lemma 4.9.2 says

  `M(γ) = e(ab A[h] / 2N²) (D/d) (2c/d)^r ε_d^{-r}`,  `ε_d = 1` if `d ≡ 1 mod 4`, `i` otherwise.

Conventions (Miyake's, made explicit):
* `(c/d)` for odd `d` is Shimura's symbol `HalfIntegral.shimuraSym`: the Jacobi symbol `(c/|d|)`,
  negated when `c < 0` and `d < 0` (this is what Miyake's proof uses: `(2c/(-p)) = sgn(c) (2c/p)`).
* `sgn(0) = 1` (Miyake, p. 189: "we understand sgn(d) = 1 when d = 0"); the case `c = 0` of the
  lemma (`a = d = -1`) needs it.
* The sum over `ℤ^r / dNℤ^r` is taken over the representatives `0 ≤ gᵢ < |d|N`; the summand is
  well defined modulo `dN` by (4.9.2) and `2 ∣ b`.
* `ε_d^{-r}` is `(HalfIntegral.epsD d)⁻¹ ^ r`.

The proof here is not Miyake's (he reduces to `-d` prime by Dirichlet's theorem and diagonalises
`A` modulo `p`). Since `c` is even, `d` is odd; put `m = |d|` and `b = 2β`. Writing `g = h + N u`
with `u` modulo `m` and completing the square with `t ≡ N⁻¹ h mod m` turns the sum into
`e(…) · Σ_{u mod m} e(-β A[u] / m)`, a Gauss sum of the quadratic form `-βA` modulo the odd
number `m` prime to `det(-βA)`. Tau Ceti evaluates it in even rank
(`Matrix.IsSymm.sum_stdAddChar_dotProduct_mulVec_eq_jacobiSym`); odd rank follows by adding a
coordinate with `A ⊕ (1)` and Gauss's evaluation `Σ_{x mod m} e(x²/m) = ε_m √m`
(`sum_range_cexp_two_pi_I_sq_div`).
-/

open Complex Matrix
open scoped Real

namespace ModularFormsKB.Miyake.Sec4_9

/-- `sgn` with Miyake's convention `sgn(0) = 1` (p. 189). -/
def sgnM (x : ℤ) : ℤ := if x < 0 then -1 else 1

/-- The representatives `g ∈ ℤ^r` with `0 ≤ gᵢ < |d| N` and `g ≡ h mod N`: a system of
representatives of `{g ∈ ℤ^r / dNℤ^r | g ≡ h mod N}`. -/
def thetaConstantReps (r N : ℕ) (h : Fin r → ℤ) (d : ℤ) : Finset (Fin r → ℕ) :=
  (Fintype.piFinset fun _ : Fin r ↦ Finset.range (d.natAbs * N)).filter
    fun g ↦ ∀ i, ((g i : ℕ) : ℤ) ≡ h i [ZMOD N]

/-- **Miyake's constant (4.9.16)**
`M(γ) = |d|^{-r/2} (-sgn(c) i)^r Σ_{g mod dN, g ≡ h mod N} e(-b A[g] / 2|d|N²)`
for `γ = [a b; c d]`; it depends on `b`, `c`, `d` only. -/
noncomputable def thetaConstant {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (N : ℕ) (h : Fin r → ℤ)
    (b c d : ℤ) : ℂ :=
  ((Real.sqrt d.natAbs : ℂ) ^ r)⁻¹ * (-(sgnM c : ℂ) * I) ^ r *
    ∑ g ∈ thetaConstantReps r N h d,
      cexp (2 * π * I * (-(b : ℂ) * (((fun i ↦ (g i : ℤ)) ⬝ᵥ A *ᵥ fun i ↦ (g i : ℤ) : ℤ) : ℂ) /
        (2 * (d.natAbs : ℂ) * (N : ℂ) ^ 2)))

/-- **Miyake, Lemma 4.9.2** (statement). With `A`, `N`, `h` as in (4.9.1), (4.9.2) and
`γ = [a b; c d] ∈ SL₂(ℤ)`, `b ≡ 0 mod 2`, `c ≡ 0 mod 2N`, `d < 0`:
`M(γ) = e(ab A[h]/2N²) (D/d) (2c/d)^r ε_d^{-r}`, `D = det A`. -/
def Lemma4_9_2Statement : Prop :=
  ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℤ) (N : ℕ) (h : Fin r → ℤ) (a b c d : ℤ),
    A.IsSymm → (A.map (Int.cast : ℤ → ℝ)).PosDef → 0 < N →
    (∃ B : Matrix (Fin r) (Fin r) ℤ, A * B = (N : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)) →
    (∀ i, (N : ℤ) ∣ (A *ᵥ h) i) →
    a * d - b * c = 1 → 2 ∣ b → 2 * (N : ℤ) ∣ c → d < 0 →
    thetaConstant A N h b c d =
      cexp (2 * π * I * ((a * b * (h ⬝ᵥ A *ᵥ h) : ℤ) : ℂ) / (2 * (N : ℂ) ^ 2)) *
        (HalfIntegral.shimuraSym A.det d : ℂ) * (HalfIntegral.shimuraSym (2 * c) d : ℂ) ^ r *
        (HalfIntegral.epsD d)⁻¹ ^ r

/-! ### Gauss sums of quadratic forms modulo an odd number, every rank -/

section GaussSum

variable {m : ℕ} [NeZero m]

/-- The Gauss sum `G_m(S) = Σ_{x ∈ (ℤ/m)^ι} e(xᵀ S x / m)` of an integer quadratic form. -/
noncomputable def quadGauss {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) [NeZero m]
    (S : Matrix ι ι ℤ) : ℂ :=
  ∑ x : ι → ZMod m, ZMod.stdAddChar (x ⬝ᵥ S.map (Int.cast : ℤ → ZMod m) *ᵥ x)

/-- `Σ_{y mod m} e(y²/m) = ε_m √m` for odd `m`. -/
theorem sum_zmod_sq_eq_epsD (hm : m % 2 = 1) :
    ∑ y : ZMod m, (ZMod.stdAddChar (y * y) : ℂ) = HalfIntegral.epsD m * (Real.sqrt m : ℂ) := by
  rw [← HalfIntegral.sum_range_cexp_sq_eq_epsD hm,
    ← HalfIntegral.sum_range_eq_sum_zmod (fun y : ZMod m ↦ (ZMod.stdAddChar (y * y) : ℂ))]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [← Nat.cast_mul, ← HalfIntegral.cexp_eq_stdAddChar]
  congr 1
  push_cast
  ring

/-- The Gauss sum of the form `x²` in one variable. -/
theorem quadGauss_one (hm : m % 2 = 1) :
    quadGauss m (1 : Matrix (Fin 1) (Fin 1) ℤ) = HalfIntegral.epsD m * (Real.sqrt m : ℂ) := by
  rw [quadGauss, ← sum_zmod_sq_eq_epsD hm]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (ZMod m)) _ _ fun x ↦ ?_
  congr 1
  rw [Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.one_mulVec]
  simp [dotProduct, Equiv.funUnique]

/-- `(ε_m √m)² = (-1/m) m` for odd `m`. -/
theorem epsD_mul_sqrt_sq (hm : m % 2 = 1) :
    (HalfIntegral.epsD m * (Real.sqrt m : ℂ)) ^ 2 = (jacobiSym (-1) m : ℂ) * m := by
  rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _),
    jacobiSym.at_neg_one (Nat.odd_iff.mpr hm)]
  unfold HalfIntegral.epsD
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · have hz : ((m : ℤ) % 4 = 1) := by omega
    rw [if_pos hz, ZMod.χ₄_nat_one_mod_four h4]
    simp
  · have hz : ¬((m : ℤ) % 4 = 1) := by omega
    rw [if_neg hz, ZMod.χ₄_nat_three_mod_four h4]
    simp

theorem epsD_mul_sqrt_ne_zero : HalfIntegral.epsD m * (Real.sqrt m : ℂ) ≠ 0 := by
  refine mul_ne_zero ?_ ?_
  · unfold HalfIntegral.epsD
    split_ifs <;> simp
  · rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)

/-- Even rank: Tau Ceti's evaluation, rewritten as `(det S / m) (ε_m √m)^{2k}`. -/
theorem quadGauss_even {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℤ}
    (hS : S.IsSymm) {k : ℕ} (hk : Fintype.card ι = 2 * k) (hm : m % 2 = 1)
    (hdet : IsCoprime S.det m) :
    quadGauss m S = jacobiSym S.det m * (HalfIntegral.epsD m * (Real.sqrt m : ℂ)) ^ (2 * k) := by
  rw [quadGauss, hS.sum_stdAddChar_dotProduct_mulVec_eq_jacobiSym hk (Nat.odd_iff.mpr hm) hdet,
    pow_mul, epsD_mul_sqrt_sq hm, jacobiSym.mul_left, jacobiSym.pow_left]
  push_cast
  ring

/-- Adding the coordinate `y²`: `G_m(S ⊕ (1)) = G_m(S) G_m((1))`. -/
theorem quadGauss_fromBlocks {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℤ) :
    quadGauss m (Matrix.fromBlocks S 0 0 (1 : Matrix (Fin 1) (Fin 1) ℤ)) =
      quadGauss m S * quadGauss m (1 : Matrix (Fin 1) (Fin 1) ℤ) := by
  rw [quadGauss, quadGauss, quadGauss, Finset.sum_mul_sum,
    ← (Equiv.sumArrowEquivProdArrow ι (Fin 1) (ZMod m)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  rw [← AddChar.map_add_eq_mul]
  congr 1
  have he : (Equiv.sumArrowEquivProdArrow ι (Fin 1) (ZMod m)).symm (x, y) = Sum.elim x y := by
    ext (i | i) <;> rfl
  rw [he, Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  simp

/-- **The Gauss sum of a quadratic form modulo an odd number, every rank**: for `S` symmetric
of size `r` and odd `m` prime to `det S`, `G_m(S) = (det S / m) (ε_m √m)^r`. -/
theorem quadGauss_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℤ}
    (hS : S.IsSymm) (hm : m % 2 = 1) (hdet : IsCoprime S.det m) :
    quadGauss m S =
      jacobiSym S.det m * (HalfIntegral.epsD m * (Real.sqrt m : ℂ)) ^ Fintype.card ι := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (Fintype.card ι)
  · rw [quadGauss_even hS hk hm hdet, hk]
  · have hS' : (Matrix.fromBlocks S 0 0 (1 : Matrix (Fin 1) (Fin 1) ℤ)).IsSymm :=
      hS.fromBlocks (by simp) (Matrix.isSymm_one)
    have hdet' : (Matrix.fromBlocks S 0 0 (1 : Matrix (Fin 1) (Fin 1) ℤ)).det = S.det := by
      rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
    have h1 := quadGauss_even (m := m) hS' (k := k + 1)
      (by rw [Fintype.card_sum, hk, Fintype.card_fin]; ring) hm (hdet'.symm ▸ hdet)
    rw [quadGauss_fromBlocks, quadGauss_one hm, hdet'] at h1
    rw [hk]
    refine mul_right_cancel₀ (epsD_mul_sqrt_ne_zero (m := m)) ?_
    rw [h1]
    ring

end GaussSum

/-! ### Completing the square -/

section Square

variable {m : ℕ} [NeZero m]

theorem map_mulVec_intCast {ι : Type*} [Fintype ι] {R : Type*} [CommRing R]
    (A : Matrix ι ι ℤ) (v : ι → ℤ) :
    A.map (Int.cast : ℤ → R) *ᵥ (fun i ↦ (v i : R)) = fun i ↦ ((A *ᵥ v) i : R) := by
  funext i
  exact ((Int.castRingHom R).map_mulVec A v i).symm

/-- The quadratic form of `c • A` is `c` times that of `A`. -/
theorem dotProduct_smul_map_mulVec {ι : Type*} [Fintype ι] {R : Type*} [CommRing R]
    (A : Matrix ι ι ℤ) (c : ℤ) (x : ι → R) :
    x ⬝ᵥ (c • A).map (Int.cast : ℤ → R) *ᵥ x = (c : R) * (x ⬝ᵥ A.map (Int.cast : ℤ → R) *ᵥ x) := by
  have : (c • A).map (Int.cast : ℤ → R) = (c : R) • A.map (Int.cast : ℤ → R) := by
    ext i j
    simp
  rw [this, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- For symmetric `A`, `(u + t)ᵀ A (u + t) = uᵀAu + 2 (At)·u + tᵀAt`. -/
theorem dotProduct_add_mulVec_add {ι : Type*} [Fintype ι] {R : Type*} [CommRing R]
    {A : Matrix ι ι R} (hA : A.IsSymm) (u t : ι → R) :
    (u + t) ⬝ᵥ A *ᵥ (u + t) = u ⬝ᵥ A *ᵥ u + 2 * ((A *ᵥ t) ⬝ᵥ u) + t ⬝ᵥ A *ᵥ t := by
  have h1 : t ⬝ᵥ A *ᵥ u = (A *ᵥ t) ⬝ᵥ u := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq]
  have h2 : u ⬝ᵥ A *ᵥ t = (A *ᵥ t) ⬝ᵥ u := dotProduct_comm _ _
  rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, h1, h2]
  ring

/-- **Completing the square in a Gauss sum.** If `A t = w` modulo `m` (`A` symmetric), then
`Σ_u e(-β (A[u] + 2 w·u) / m) = e(β A[t] / m) · G_m(-β A)`. -/
theorem sum_completeSquare {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} (hA : A.IsSymm) (β : ℤ)
    (t w : Fin r → ZMod m) (hAt : A.map (Int.cast : ℤ → ZMod m) *ᵥ t = w) :
    ∑ u : Fin r → ZMod m, (ZMod.stdAddChar (-(β : ZMod m) *
        (u ⬝ᵥ A.map (Int.cast : ℤ → ZMod m) *ᵥ u + 2 * (w ⬝ᵥ u))) : ℂ) =
      ZMod.stdAddChar ((β : ZMod m) * (t ⬝ᵥ A.map (Int.cast : ℤ → ZMod m) *ᵥ t)) *
        quadGauss m ((-β) • A) := by
  have hA' : (A.map (Int.cast : ℤ → ZMod m)).IsSymm := hA.map _
  have hq : ∀ u : Fin r → ZMod m, -(β : ZMod m) * (u ⬝ᵥ A.map (Int.cast : ℤ → ZMod m) *ᵥ u +
      2 * (w ⬝ᵥ u)) = (u + t) ⬝ᵥ ((-β) • A).map (Int.cast : ℤ → ZMod m) *ᵥ (u + t) +
        (β : ZMod m) * (t ⬝ᵥ A.map (Int.cast : ℤ → ZMod m) *ᵥ t) := by
    intro u
    rw [dotProduct_smul_map_mulVec, dotProduct_add_mulVec_add hA', hAt]
    push_cast
    ring
  calc _ = ∑ u : Fin r → ZMod m,
        (ZMod.stdAddChar ((β : ZMod m) * (t ⬝ᵥ A.map (Int.cast : ℤ → ZMod m) *ᵥ t)) : ℂ) *
          ZMod.stdAddChar ((u + t) ⬝ᵥ ((-β) • A).map (Int.cast : ℤ → ZMod m) *ᵥ (u + t)) :=
        Finset.sum_congr rfl fun u _ ↦ by rw [hq u, AddChar.map_add_eq_mul, mul_comm]
    _ = _ := by
      rw [← Finset.mul_sum, quadGauss]
      exact congrArg (fun z ↦ (ZMod.stdAddChar ((β : ZMod m) *
        (t ⬝ᵥ A.map (Int.cast : ℤ → ZMod m) *ᵥ t)) : ℂ) * z) (Equiv.sum_comp (Equiv.addRight t)
          (fun x ↦ (ZMod.stdAddChar (x ⬝ᵥ ((-β) • A).map (Int.cast : ℤ → ZMod m) *ᵥ x) : ℂ)))

end Square

/-! ### The sum over `g mod dN`, `g ≡ h mod N`, as a sum over `u mod |d|` -/

section Reindex

/-- The representative `g = (h mod N) + N u` of a class `u mod m`. -/
def repOf (r N m : ℕ) (h : Fin r → ℤ) (u : Fin r → ZMod m) : Fin r → ℕ :=
  fun i ↦ (h i % N).toNat + N * (u i).val

theorem toNat_emod_lt {N : ℕ} (hN : 0 < N) (x : ℤ) : (x % N).toNat < N := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have := Int.emod_lt_of_pos x hN'
  have := Int.emod_nonneg x hN'.ne'
  omega

theorem coe_repOf {r N m : ℕ} (hN : 0 < N) (h : Fin r → ℤ) (u : Fin r → ZMod m) (i : Fin r) :
    ((repOf r N m h u i : ℕ) : ℤ) = h i % N + N * ((u i).val : ℤ) := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  simp only [repOf]
  push_cast
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hN'.ne')]

theorem repOf_mem {r N m : ℕ} [NeZero m] (hN : 0 < N) {d : ℤ} (hmd : d.natAbs = m)
    (h : Fin r → ℤ) (u : Fin r → ZMod m) : repOf r N m h u ∈ thetaConstantReps r N h d := by
  subst hmd
  simp only [thetaConstantReps, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
  · have h1 := toNat_emod_lt hN (h i)
    have h2 : (u i).val + 1 ≤ d.natAbs := ZMod.val_lt (u i)
    simp only [repOf]
    nlinarith
  · rw [coe_repOf hN, Int.ModEq, Int.add_mul_emod_self_left, Int.emod_emod_of_dvd _ (dvd_refl _)]

/-- The sum over the representatives `0 ≤ gᵢ < |d|N`, `g ≡ h mod N`, is the sum over
`u ∈ (ℤ/|d|)^r` of the summand at `g = (h mod N) + N u`. -/
theorem sum_reps_eq {r N m : ℕ} [NeZero m] (hN : 0 < N) {d : ℤ} (hmd : d.natAbs = m)
    (h : Fin r → ℤ) (F : (Fin r → ℕ) → ℂ) :
    ∑ g ∈ thetaConstantReps r N h d, F g = ∑ u : Fin r → ZMod m, F (repOf r N m h u) := by
  subst hmd
  have hleft : ∀ g ∈ thetaConstantReps r N h d,
      repOf r N d.natAbs h (fun i ↦ ((g i / N : ℕ) : ZMod d.natAbs)) = g := by
    intro g hg
    simp only [thetaConstantReps, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hg
    funext i
    have hlt : g i / N < d.natAbs := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hg.1 i)
    have hmod : (h i % N).toNat = g i % N := by
      have h1 : ((g i : ℕ) : ℤ) % N = h i % N := hg.2 i
      have h2 : ((g i % N : ℕ) : ℤ) = ((g i : ℕ) : ℤ) % N := by push_cast; rfl
      omega
    simp only [repOf, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, hmod]
    exact Nat.mod_add_div (g i) N
  refine Finset.sum_nbij' (fun g i ↦ ((g i / N : ℕ) : ZMod d.natAbs)) (repOf r N d.natAbs h)
    (fun _ _ ↦ Finset.mem_univ _) (fun u _ ↦ repOf_mem hN rfl h u) hleft ?_
    (fun g hg ↦ by rw [hleft g hg])
  intro u _
  funext i
  simp only [repOf]
  rw [Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt (toNat_emod_lt hN (h i)), zero_add,
    ZMod.natCast_zmod_val]

end Reindex

/-! ### The summand at `g = h₀ + N u` -/

section Summand

/-- For symmetric `A` with `A h₀ = N w₀`: `A[h₀ + N v] = A[h₀] + N² (2 w₀·v + A[v])`. -/
theorem quad_add_smul {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} (hA : A.IsSymm) {N : ℤ}
    {h₀ w₀ : Fin r → ℤ} (hw : A *ᵥ h₀ = N • w₀) (v : Fin r → ℤ) :
    (h₀ + N • v) ⬝ᵥ A *ᵥ (h₀ + N • v) =
      h₀ ⬝ᵥ A *ᵥ h₀ + N ^ 2 * (2 * (w₀ ⬝ᵥ v) + v ⬝ᵥ A *ᵥ v) := by
  have h1 : (h₀ + N • v) ⬝ᵥ A *ᵥ (h₀ + N • v) =
      h₀ ⬝ᵥ A *ᵥ h₀ + 2 * ((A *ᵥ h₀) ⬝ᵥ (N • v)) + (N • v) ⬝ᵥ A *ᵥ (N • v) := by
    rw [add_comm h₀, dotProduct_add_mulVec_add hA]
    ring
  rw [h1, hw]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

variable {m : ℕ} [NeZero m]

/-- The summand of `M(γ)` at `g = (h mod N) + N u`, `b = 2β`, splits as a constant phase times
`e(-β (A[u] + 2 w₀·u) / m)`. -/
theorem summand_repOf {r N : ℕ} (hN : 0 < N) {A : Matrix (Fin r) (Fin r) ℤ} (hA : A.IsSymm)
    (h : Fin r → ℤ) {w₀ : Fin r → ℤ} (hw : A *ᵥ (fun i ↦ h i % N) = (N : ℤ) • w₀) (β : ℤ)
    (u : Fin r → ZMod m) :
    cexp (2 * π * I * (-((2 * β : ℤ) : ℂ) *
        (((fun i ↦ ((repOf r N m h u i : ℕ) : ℤ)) ⬝ᵥ A *ᵥ fun i ↦ ((repOf r N m h u i : ℕ) : ℤ) :
          ℤ) : ℂ) / (2 * (m : ℂ) * (N : ℂ) ^ 2))) =
      cexp (2 * π * I * (-(β : ℂ) * (((fun i ↦ h i % N) ⬝ᵥ A *ᵥ (fun i ↦ h i % N) : ℤ) : ℂ) /
          ((m : ℂ) * (N : ℂ) ^ 2))) *
        ZMod.stdAddChar (-(β : ZMod m) * (u ⬝ᵥ A.map (Int.cast : ℤ → ZMod m) *ᵥ u +
          2 * ((fun i ↦ (w₀ i : ZMod m)) ⬝ᵥ u))) := by
  set v : Fin r → ℤ := fun i ↦ ((u i).val : ℤ)
  set h₀ : Fin r → ℤ := fun i ↦ h i % N
  have hg : (fun i ↦ ((repOf r N m h u i : ℕ) : ℤ)) = h₀ + (N : ℤ) • v := by
    funext i
    rw [coe_repOf hN]
    simp [h₀, v]
  have hu : u = fun i ↦ (v i : ZMod m) := by
    funext i
    simp [v]
  have hz : -(β : ZMod m) * (u ⬝ᵥ A.map (Int.cast : ℤ → ZMod m) *ᵥ u +
      2 * ((fun i ↦ (w₀ i : ZMod m)) ⬝ᵥ u)) =
      ((-β * (v ⬝ᵥ A *ᵥ v + 2 * (w₀ ⬝ᵥ v)) : ℤ) : ZMod m) := by
    rw [hu, Matrix.intCast_dotProduct_mulVec]
    have : (fun i ↦ (w₀ i : ZMod m)) ⬝ᵥ (fun i ↦ (v i : ZMod m)) = ((w₀ ⬝ᵥ v : ℤ) : ZMod m) := by
      simp [dotProduct]
    rw [this]
    push_cast
    ring
  rw [hz, ZMod.stdAddChar_coe, ← Complex.exp_add, hg, quad_add_smul hA hw]
  congr 1
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  push_cast
  field_simp
  ring

end Summand

/-! ### Assembly -/

section Assembly

/-- The phase identity: `e(-β A[h₀]/(mN²)) e(β N̄² A[h₀]/m) = e(ab A[h]/2N²)` for `b = 2β`, where
`N̄ N ≡ 1 mod m`, `m = -d`, `ad - bc = 1` and `N ∣ c/2`. -/
theorem phase_eq {r N m : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} (hA : A.IsSymm)
    (h : Fin r → ℤ) {w₀ : Fin r → ℤ} (hw : A *ᵥ (fun i ↦ h i % N) = (N : ℤ) • w₀)
    (hN : 0 < N) (hm : 0 < m) (a β c' Nb : ℤ)
    (hdet : a * (-(m : ℤ)) - 2 * β * (2 * N * c') = 1) (hNb : (m : ℤ) ∣ Nb * N - 1)
    (hcop : IsCoprime (m : ℤ) N) :
    cexp (2 * π * I * (-(β : ℂ) * (((fun i ↦ h i % N) ⬝ᵥ A *ᵥ (fun i ↦ h i % N) : ℤ) : ℂ) /
          ((m : ℂ) * (N : ℂ) ^ 2))) *
        cexp (2 * π * I * ((β * Nb ^ 2 * ((fun i ↦ h i % N) ⬝ᵥ A *ᵥ (fun i ↦ h i % N)) : ℤ) : ℂ) /
          m) =
      cexp (2 * π * I * ((a * (2 * β) * (h ⬝ᵥ A *ᵥ h) : ℤ) : ℂ) / (2 * (N : ℂ) ^ 2)) := by
  set h₀ : Fin r → ℤ := fun i ↦ h i % N
  set s : Fin r → ℤ := fun i ↦ h i / N
  have hh : h = h₀ + (N : ℤ) • s := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h₀, s]
    rw [Int.emod_def]; ring
  -- `A[h₀] = N (h₀·w₀)`
  have hq : h₀ ⬝ᵥ A *ᵥ h₀ = N * (h₀ ⬝ᵥ w₀) := by
    rw [hw, dotProduct_smul, smul_eq_mul]
  -- `X = Nb² N² - 1 - a m` is divisible by `m N`
  obtain ⟨L, hL⟩ : (m : ℤ) * N ∣ Nb ^ 2 * N ^ 2 - 1 - a * m := by
    refine hcop.mul_dvd ?_ ?_
    · obtain ⟨t, ht⟩ := hNb
      exact ⟨t * (Nb * N + 1) - a, by linear_combination (Nb * N + 1) * ht⟩
    · exact ⟨Nb ^ 2 * N + 4 * β * c', by linear_combination hdet⟩
  set K := 2 * (w₀ ⬝ᵥ s) + s ⬝ᵥ A *ᵥ s
  have hAh : h ⬝ᵥ A *ᵥ h = h₀ ⬝ᵥ A *ᵥ h₀ + (N : ℤ) ^ 2 * K := by
    rw [hh]
    exact quad_add_smul hA hw s
  rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨β * (h₀ ⬝ᵥ w₀) * L - a * β * K, ?_⟩
  rw [hAh, hq]
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hLc : (Nb : ℂ) ^ 2 * (N : ℂ) ^ 2 - 1 - (a : ℂ) * m = m * N * L := by exact_mod_cast hL
  push_cast
  field_simp
  linear_combination (β * ((h₀ ⬝ᵥ w₀ : ℤ) : ℂ)) * hLc

/-- `-i ε_m = ε_{-m}⁻¹` for odd `m`. -/
theorem neg_I_mul_epsD {m : ℕ} (hm : m % 2 = 1) :
    -I * HalfIntegral.epsD m = (HalfIntegral.epsD (-(m : ℤ)))⁻¹ := by
  unfold HalfIntegral.epsD
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · rw [if_pos (by omega), if_neg (by omega), Complex.inv_I]
    ring
  · rw [if_neg (by omega), if_pos (by omega), inv_one]
    ring_nf
    simp

/-- If `x y ≡ 1 mod m` then `(x/m) = (y/m)`. -/
theorem jacobiSym_eq_of_mul {m : ℕ} {x y : ℤ} (hxy : (m : ℤ) ∣ x * y - 1) :
    jacobiSym x m = jacobiSym y m := by
  obtain ⟨t, ht⟩ := hxy
  have hx : IsCoprime x m := ⟨y, -t, by linear_combination ht⟩
  have hy : IsCoprime y m := ⟨x, -t, by linear_combination ht⟩
  have hprod : jacobiSym x m * jacobiSym y m = 1 := by
    rw [← jacobiSym.mul_left, jacobiSym.mod_left' (a₂ := 1), jacobiSym.one_left]
    rw [show x * y = 1 + m * t by linear_combination ht, Int.add_mul_emod_self_left]
  rcases jacobiSym.eq_one_or_neg_one (Int.isCoprime_iff_gcd_eq_one.mp hx) with h1 | h1 <;>
    rcases jacobiSym.eq_one_or_neg_one (Int.isCoprime_iff_gcd_eq_one.mp hy) with h2 | h2 <;>
    rw [h1, h2] at hprod ⊢ <;> norm_num at hprod

/-- **Miyake, Lemma 4.9.2.** -/
@[kb "miyake1989" "Lemma 4.9.2, p. 190: M(γ) = e(abA[h]/2N²)(D/d)(2c/d)^r ε_d^{-r} for γ ∈ SL2(Z), b even, 2N | c, d < 0"]
theorem lemma_4_9_2 : Lemma4_9_2Statement := by
  intro r A N h a b c d hA hP hN ⟨B, hB⟩ hAh hdet hb hc hd
  obtain ⟨β, rfl⟩ := hb
  obtain ⟨c', rfl⟩ := hc
  obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hd.le
  have hm : 0 < m := by omega
  haveI : NeZero m := ⟨hm.ne'⟩
  have hdm : (-(m : ℤ)).natAbs = m := by simp
  -- arithmetic of `γ`
  have hdet' : a * (-(m : ℤ)) - 2 * β * (2 * N * c') = 1 := by linear_combination hdet
  have hcopN : IsCoprime (m : ℤ) N := ⟨-a, -(4 * β * c'), by linear_combination hdet'⟩
  have hcopβ : IsCoprime β m := ⟨-(4 * N * c'), -a, by linear_combination hdet'⟩
  have hmodd : m % 2 = 1 := by
    have h2 : IsCoprime (m : ℤ) ((2 : ℕ) : ℤ) := ⟨-a, -(2 * β * N * c'), by push_cast; linear_combination hdet'⟩
    have := Nat.isCoprime_iff_coprime.mp h2
    exact Nat.odd_iff.mp (Nat.coprime_two_right.mp this)
  have hDN : A.det * B.det = (N : ℤ) ^ r := by
    rw [← Matrix.det_mul, hB, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  have hcopD : IsCoprime A.det m :=
    IsCoprime.of_mul_left_left (hDN ▸ hcopN.symm.pow_left)
  have hcopS : IsCoprime ((-β) • A).det m := by
    rw [Matrix.det_smul, Fintype.card_fin]
    exact (hcopβ.neg_left.pow_left).mul_left hcopD
  -- an inverse of `N` modulo `m`
  obtain ⟨Nb, v, hNbv⟩ := hcopN.symm
  have hNb : (m : ℤ) ∣ Nb * N - 1 := ⟨-v, by linear_combination hNbv⟩
  -- `A (h mod N) = N w₀`
  set h₀ : Fin r → ℤ := fun i ↦ h i % N
  choose w hw using hAh
  set s : Fin r → ℤ := fun i ↦ h i / N
  have hh : h = h₀ + (N : ℤ) • s := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h₀, s]
    rw [Int.emod_def]; ring
  have hw₀ : A *ᵥ h₀ = (N : ℤ) • (w - A *ᵥ s) := by
    have : A *ᵥ h = (N : ℤ) • w := by
      funext i
      simp [hw i]
    rw [smul_sub, ← this, hh, Matrix.mulVec_add, Matrix.mulVec_smul]
    abel
  -- `t = N⁻¹ h₀` modulo `m`, with `A t = w₀`
  have hAt : A.map (Int.cast : ℤ → ZMod m) *ᵥ (fun i ↦ (((Nb • h₀) i : ℤ) : ZMod m)) =
      fun i ↦ (((w - A *ᵥ s) i : ℤ) : ZMod m) := by
    rw [map_mulVec_intCast, Matrix.mulVec_smul, hw₀]
    funext i
    have h1 : ((Nb * N : ℤ) : ZMod m) = 1 := by
      rw [← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hNb
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
    rw [← mul_assoc, ← Int.cast_mul, h1, one_mul]
  -- the sum
  unfold thetaConstant
  rw [sum_reps_eq hN hdm h, hdm]
  simp_rw [summand_repOf hN hA h hw₀ β]
  rw [← Finset.mul_sum, sum_completeSquare hA β _ _ hAt, quadGauss_eq (hA.smul _) hmodd hcopS,
    Fintype.card_fin, Matrix.det_smul, Fintype.card_fin, jacobiSym.mul_left, jacobiSym.pow_left]
  -- the phase
  have hQt : (β : ZMod m) * ((fun i ↦ (((Nb • h₀) i : ℤ) : ZMod m)) ⬝ᵥ
      A.map (Int.cast : ℤ → ZMod m) *ᵥ (fun i ↦ (((Nb • h₀) i : ℤ) : ZMod m))) =
      ((β * Nb ^ 2 * (h₀ ⬝ᵥ A *ᵥ h₀) : ℤ) : ZMod m) := by
    rw [Matrix.intCast_dotProduct_mulVec, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp only [smul_eq_mul, Int.cast_mul, Int.cast_pow]
    ring
  rw [hQt, ZMod.stdAddChar_coe]
  have hphase := phase_eq hA h hw₀ hN hm a β c' Nb hdet' hNb hcopN
  -- the symbols
  have hJ : jacobiSym (-β) m = jacobiSym (2 * (2 * N * c')) m :=
    jacobiSym_eq_of_mul ⟨a, by linear_combination hdet'⟩
  have hshim : (HalfIntegral.shimuraSym (2 * (2 * N * c')) (-(m : ℤ)) : ℂ) =
      (sgnM (2 * N * c') : ℂ) * jacobiSym (2 * (2 * N * c')) m := by
    unfold HalfIntegral.shimuraSym sgnM
    rw [hdm]
    by_cases hc0 : 2 * (N : ℤ) * c' < 0
    · rw [if_pos ⟨by linarith, by omega⟩, if_pos hc0]
      push_cast
      ring
    · rw [if_neg (fun h ↦ hc0 (by linarith [h.1])), if_neg hc0]
      push_cast
      ring
  have hsqrt : (Real.sqrt m : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
    exact_mod_cast hm
  have hDpos : 0 < A.det := by
    have := hP.det_pos
    rw [← Int.cast_det] at this
    exact_mod_cast this
  have hshimD : (HalfIntegral.shimuraSym A.det (-(m : ℤ)) : ℂ) = jacobiSym A.det m := by
    unfold HalfIntegral.shimuraSym
    rw [if_neg (fun h ↦ by linarith [h.1]), hdm]
  rw [hshim, hshimD, ← neg_I_mul_epsD hmodd, hJ]
  push_cast at hphase ⊢
  rw [← hphase]
  simp only [h₀]
  field_simp
  ring

end Assembly

end ModularFormsKB.Miyake.Sec4_9
