import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing
import ModularFormsKB.Citation
/-!
# Eisenstein's Dirichlet series for the cubic residue character (`-00017`, `-00019`)

Eisenstein, *Mathematische Abhandlungen* (1847), the paper on the cubic forms and the class number of the cubic
field of conductor `p`. With a
modulus `E`, the primes `g ∤ E`, the integers `m` prime to `E`, and the cubic residue character `[m/π₁]` (a
Dirichlet character of order `3`), Eisenstein uses, for real `ε > 1`:

* the Euler products `∏_g (1 - g^{-ε})^{-1} = ∑ m^{-ε}`, `∏_g (1 - [g/π₁] g^{-ε})^{-1} = ∑ [m/π₁] m^{-ε}`,
  the same with `[·/π₁]²` and with `3ε`, and consequently the product of the three series divided by `∑ m^{-3ε}`
  as one Euler product;
* `lim_{ε → 0+} ε ∑_{(m, E) = 1} m^{-(1+ε)} = ∏_{f ∣ E} (1 - 1/f)`, and the convergence of
  `∑ [m/π₁]/m` and `∑ [m/π₁]²/m`;
* the non-vanishing of `∑ [n/π₁]/n` and `∑ [n/π₁]²/n` (from the class number being `≥ 1`).

They are formalized for an arbitrary Dirichlet character `χ` modulo `E` (the cubic residue character is one), with
complex `s`, `Re s > 1`, in place of real `ε > 1`; the trivial character `1` modulo `E` is the indicator of
`(m, E) = 1`. They are thin wrappers of Mathlib: the Euler product
`DirichletCharacter.LSeries_eulerProduct_hasProd`, the residue `DirichletCharacter.LFunctionTrivChar_residue_one`, and
the non-vanishing `DirichletCharacter.LFunction_apply_one_ne_zero` (Mathlib proves it for every non-trivial
character, which is the general claim Eisenstein makes at the end of his non-vanishing argument). Mathlib's `L(χ, 1)` is the
value at `1` of the analytic continuation; that it equals the sum of Eisenstein's conditionally convergent series
`∑ χ(m)/m` is `LSeriesValueAtOne`.
-/

noncomputable section

open Complex Filter Topology
open scoped LSeries.notation

namespace ModularFormsKB.Historical.Eisenstein

/-- **Eisenstein's Euler products** (1847): for a Dirichlet character `χ` modulo `E`
and `Re s > 1`, `∏_p (1 - χ(p) p^{-s})^{-1} = ∑_m χ(m) m^{-s}` (for `χ = 1` the primes `p ∣ E` and the integers
`m` not prime to `E` drop out). -/
@[kb "eisenstein1847" "Abhandlungen, cubic forms, Euler products"]
def EisensteinEulerProducts : Prop :=
  ∀ (E : ℕ) (χ : DirichletCharacter ℂ E) (s : ℂ), 1 < s.re →
    HasProd (fun p : Nat.Primes ↦ (1 - χ p * (p : ℂ) ^ (-s))⁻¹) (∑' m : ℕ, χ m * (m : ℂ) ^ (-s))

/-- The Dirichlet series `∑ χ(m) m^{-s}` is Mathlib's `L ↗χ s` for `Re s > 1`. -/
lemma tsum_eq_LSeries {E : ℕ} (χ : DirichletCharacter ℂ E) {s : ℂ} (hs : 1 < s.re) :
    ∑' m : ℕ, χ m * (m : ℂ) ^ (-s) = LSeries ↗χ s :=
  tsum_dirichletSummand χ hs

/-- **Eisenstein's Euler products**. Wrapper of
`DirichletCharacter.LSeries_eulerProduct_hasProd`. -/
@[kb "eisenstein1847" "Abhandlungen, cubic forms, Euler products"]
theorem eisensteinEulerProducts : EisensteinEulerProducts := by
  intro E χ s hs
  rw [tsum_eq_LSeries χ hs]
  exact DirichletCharacter.LSeries_eulerProduct_hasProd χ hs

/-- **Eisenstein's product of the three series** (1847, the consequence): for a
character `χ` modulo `E` with `χ³ = 1` and `Re s > 1`,
`(∑ m^{-s})(∑ χ(m) m^{-s})(∑ χ(m)² m^{-s}) / ∑ m^{-3s}` (sums over `m` prime to `E`) is the Euler product
`∏_{p ∤ E} (1 - p^{-3s}) / ((1 - p^{-s})(1 - χ(p) p^{-s})(1 - χ(p)² p^{-s}))`. -/
@[kb "eisenstein1847" "Abhandlungen, cubic forms, Euler products"]
def EisensteinCubicProduct : Prop :=
  ∀ (E : ℕ) (χ : DirichletCharacter ℂ E), χ ^ 3 = 1 → ∀ s : ℂ, 1 < s.re →
    HasProd
      (fun p : Nat.Primes ↦ (1 - (1 : DirichletCharacter ℂ E) p * (p : ℂ) ^ (-(3 * s))) /
        ((1 - (1 : DirichletCharacter ℂ E) p * (p : ℂ) ^ (-s)) * (1 - χ p * (p : ℂ) ^ (-s)) *
          (1 - χ p ^ 2 * (p : ℂ) ^ (-s))))
      ((∑' m : ℕ, (1 : DirichletCharacter ℂ E) m * (m : ℂ) ^ (-s)) * (∑' m : ℕ, χ m * (m : ℂ) ^ (-s)) *
          (∑' m : ℕ, χ m ^ 2 * (m : ℂ) ^ (-s)) /
        ∑' m : ℕ, (1 : DirichletCharacter ℂ E) m * (m : ℂ) ^ (-(3 * s)))

/-- **Eisenstein's product of the three series**. Combines four instances of
`DirichletCharacter.LSeries_eulerProduct_hasProd` with `HasProd.mul` and `HasProd.div₀`. -/
@[kb "eisenstein1847" "Abhandlungen, cubic forms, Euler products"]
theorem eisensteinCubicProduct : EisensteinCubicProduct := by
  intro E χ _ s hs
  have hs3 : 1 < (3 * s).re := by
    simp only [Complex.mul_re]; norm_num; linarith
  have h1 := eisensteinEulerProducts E 1 s hs
  have h2 := eisensteinEulerProducts E χ s hs
  have h3 := eisensteinEulerProducts E (χ ^ 2) s hs
  have h4 := eisensteinEulerProducts E 1 (3 * s) hs3
  have hne : ∑' m : ℕ, (1 : DirichletCharacter ℂ E) m * (m : ℂ) ^ (-(3 * s)) ≠ 0 := by
    rw [tsum_eq_LSeries _ hs3]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re _ hs3
  have key := ((h1.mul h2).mul h3).div₀ h4 hne
  simp_rw [MulChar.pow_apply' χ two_ne_zero] at key
  convert key using 2 with p
  simp only [div_eq_mul_inv, inv_inv, mul_inv]
  ring

/-- **Eisenstein's residue** (1847, first part): for `E ≥ 1`,
`lim_{ε → 0+} ε ∑_{(m, E) = 1} m^{-(1+ε)} = ∏_{p ∣ E} (1 - 1/p)`. -/
@[kb "eisenstein1847" "Abhandlungen, cubic forms"]
def EisensteinResidue : Prop :=
  ∀ E : ℕ, 0 < E →
    Tendsto (fun ε : ℝ ↦ ε * ∑' m : ℕ, if m.Coprime E then (m : ℝ) ^ (-(1 + ε)) else 0) (𝓝[>] 0)
      (𝓝 (∏ p ∈ E.primeFactors, (1 - (p : ℝ)⁻¹)))

/-- The trivial character modulo `E` is the indicator of `(m, E) = 1`. -/
lemma trivChar_natCast_apply (E m : ℕ) :
    (1 : DirichletCharacter ℂ E) (m : ZMod E) = if m.Coprime E then 1 else 0 := by
  split_ifs with h
  · exact MulChar.one_apply ((ZMod.isUnit_iff_coprime m E).mpr h)
  · exact MulChar.map_nonunit _ (fun hu ↦ h ((ZMod.isUnit_iff_coprime m E).mp hu))

/-- For real `ε > 0`, the real series of `EisensteinResidue` is `L(1, 1 + ε)` divided by `ε`, in `ℂ`. -/
lemma residue_aux (E : ℕ) [NeZero E] {ε : ℝ} (hε : 0 < ε) :
    (((ε * ∑' m : ℕ, if m.Coprime E then (m : ℝ) ^ (-(1 + ε)) else 0 : ℝ)) : ℂ) =
      (((1 + ε : ℝ) : ℂ) - 1) * DirichletCharacter.LFunctionTrivChar E ((1 + ε : ℝ) : ℂ) := by
  have hs : 1 < (((1 + ε : ℝ) : ℂ)).re := by simpa using hε
  rw [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_eq_LSeries _ hs, LSeries]
  have hne : (((1 + ε : ℝ) : ℂ)) ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  push_cast
  have : ∀ m : ℕ, (((if m.Coprime E then (m : ℝ) ^ (-(1 + ε)) else 0 : ℝ)) : ℂ) =
      LSeries.term (fun n : ℕ ↦ (1 : DirichletCharacter ℂ E) n) ((1 + ε : ℝ) : ℂ) m := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · rw [LSeries.term_zero]
      split_ifs
      · rw [Nat.cast_zero, Real.zero_rpow (by linarith)]; simp
      · simp
    · rw [LSeries.term_of_ne_zero hm, trivChar_natCast_apply]
      split_ifs
      · rw [Complex.ofReal_cpow (Nat.cast_nonneg m)]
        push_cast
        rw [Complex.cpow_neg]; simp
      · simp
  simp_rw [this]
  push_cast
  ring

/-- **Eisenstein's residue**. Wrapper of
`DirichletCharacter.LFunctionTrivChar_residue_one`, restricted to real `s = 1 + ε`. -/
@[kb "eisenstein1847" "Abhandlungen, cubic forms"]
theorem eisensteinResidue : EisensteinResidue := by
  intro E hE
  have : NeZero E := ⟨hE.ne'⟩
  have hf : Tendsto (fun ε : ℝ ↦ (((1 + ε : ℝ)) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun ε : ℝ ↦ (((1 + ε : ℝ)) : ℂ)) (𝓝 0) (𝓝 (((1 + 0 : ℝ)) : ℂ)) :=
        (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).tendsto 0
      simpa using tendsto_nhdsWithin_of_tendsto_nhds this
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
  have h1 := (DirichletCharacter.LFunctionTrivChar_residue_one (N := E)).comp hf
  rw [← Filter.tendsto_ofReal_iff]
  have h2 : ((∏ p ∈ E.primeFactors, (1 - (p : ℝ)⁻¹) : ℝ) : ℂ) = ∏ p ∈ E.primeFactors, (1 - (p : ℂ)⁻¹) := by
    push_cast; rfl
  rw [h2]
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simp only [Function.comp]
  rw [residue_aux E hε]

/-- **Convergence of `∑ χ(m)/m`** (1847, second part): for a non-trivial character `χ`
modulo `E ≥ 1` the partial sums `∑_{m < N} χ(m)/m` converge. -/
@[kb "eisenstein1847" "Abhandlungen, cubic forms"]
def EisensteinSeriesConverges : Prop :=
  ∀ (E : ℕ) [NeZero E] (χ : DirichletCharacter ℂ E), χ ≠ 1 →
    ∃ c : ℂ, Tendsto (fun N : ℕ ↦ ∑ m ∈ Finset.range N, χ m / m) atTop (𝓝 c)

/-- The sum of a non-trivial character over `m < E` (a full period) vanishes. -/
lemma sum_range_eq_zero {E : ℕ} [NeZero E] {χ : DirichletCharacter ℂ E} (hχ : χ ≠ 1) :
    ∑ m ∈ Finset.range E, χ (m : ZMod E) = 0 := by
  rw [← MulChar.sum_eq_zero_of_ne_one hχ]
  refine Finset.sum_nbij (fun m : ℕ ↦ (m : ZMod E)) (fun _ _ ↦ Finset.mem_univ _) ?_ ?_ (fun _ _ ↦ rfl)
  · intro m hm m' hm' h
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt (Finset.mem_range.mp hm), ZMod.val_natCast_of_lt (Finset.mem_range.mp hm')]
      at this
  · intro a _
    exact ⟨a.val, Finset.mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩

/-- The partial sums `∑_{m < n} χ(m)` of a non-trivial character are bounded by `E`. -/
lemma norm_sum_range_le {E : ℕ} [NeZero E] {χ : DirichletCharacter ℂ E} (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ m ∈ Finset.range n, χ (m : ZMod E)‖ ≤ E := by
  have hper : ∀ q : ℕ, ∑ m ∈ Finset.range (E * q), χ (m : ZMod E) = 0 := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, zero_add]
      have : ∀ x : ℕ, ((E * q + x : ℕ) : ZMod E) = (x : ZMod E) := by
        intro x; simp
      simp_rw [this]
      exact sum_range_eq_zero hχ
  have hn : n = E * (n / E) + n % E := (Nat.div_add_mod n E).symm
  rw [hn, Finset.sum_range_add, hper, zero_add]
  have : ∀ x : ℕ, ((E * (n / E) + x : ℕ) : ZMod E) = (x : ZMod E) := by
    intro x; simp
  simp_rw [this]
  calc ‖∑ x ∈ Finset.range (n % E), χ (x : ZMod E)‖ ≤ ∑ x ∈ Finset.range (n % E), ‖χ (x : ZMod E)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _x ∈ Finset.range (n % E), (1 : ℝ) := Finset.sum_le_sum fun x _ ↦ χ.norm_le_one _
    _ = (n % E : ℕ) := by simp
    _ ≤ E := by exact_mod_cast (Nat.mod_lt n (Nat.pos_of_ne_zero (NeZero.ne E))).le

/-- Quantitative Abel summation: for antitone `f ≥ 0` and `b` with partial sums bounded by `B`, a block sum
`∑_{N ≤ i < M} b i f i` has norm at most `2 B f N`. -/
lemma abel_tail (b : ℕ → ℂ) (f : ℕ → ℝ) (hf : Antitone f) (hf0 : ∀ i, 0 ≤ f i) (B : ℝ)
    (hB : ∀ n, ‖∑ i ∈ Finset.range n, b i‖ ≤ B) (N M : ℕ) (h : N ≤ M) :
    ‖∑ i ∈ Finset.Ico N M, b i * (f i : ℂ)‖ ≤ 2 * B * f N := by
  have hD : ∀ M, N ≤ M → ‖∑ i ∈ Finset.Ico N M, b i‖ ≤ 2 * B := by
    intro M hM
    rw [Finset.sum_Ico_eq_sub _ hM]
    calc _ ≤ ‖∑ i ∈ Finset.range M, b i‖ + ‖∑ i ∈ Finset.range N, b i‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith [hB M, hB N]
  have key : ∀ M, N ≤ M → ‖∑ i ∈ Finset.Ico N M, b i * (f i : ℂ) -
      (∑ i ∈ Finset.Ico N M, b i) * (f M : ℂ)‖ ≤ 2 * B * (f N - f M) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
      have e : ∑ i ∈ Finset.Ico N (M + 1), b i * (f i : ℂ) - (∑ i ∈ Finset.Ico N (M + 1), b i) * (f (M + 1) : ℂ)
          = (∑ i ∈ Finset.Ico N M, b i * (f i : ℂ) - (∑ i ∈ Finset.Ico N M, b i) * (f M : ℂ)) +
            (∑ i ∈ Finset.Ico N (M + 1), b i) * ((f M : ℂ) - (f (M + 1) : ℂ)) := by
        rw [Finset.sum_Ico_succ_top hM, Finset.sum_Ico_succ_top hM]; ring
      rw [e]
      have h2 : ‖(∑ i ∈ Finset.Ico N (M + 1), b i) * ((f M : ℂ) - (f (M + 1) : ℂ))‖ ≤
          2 * B * (f M - f (M + 1)) := by
        rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr (hf (by omega)))]
        exact mul_le_mul_of_nonneg_right (hD _ (by omega)) (sub_nonneg.mpr (hf (by omega)))
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ 2 * B * (f N - f M) + 2 * B * (f M - f (M + 1)) := add_le_add ih h2
        _ = _ := by ring
  have h1 := key M h
  have h3 : ‖(∑ i ∈ Finset.Ico N M, b i) * (f M : ℂ)‖ ≤ 2 * B * f M := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hf0 M)]
    exact mul_le_mul_of_nonneg_right (hD M h) (hf0 M)
  calc ‖∑ i ∈ Finset.Ico N M, b i * (f i : ℂ)‖
      ≤ ‖∑ i ∈ Finset.Ico N M, b i * (f i : ℂ) - (∑ i ∈ Finset.Ico N M, b i) * (f M : ℂ)‖ +
        ‖(∑ i ∈ Finset.Ico N M, b i) * (f M : ℂ)‖ := by
        have := norm_add_le (∑ i ∈ Finset.Ico N M, b i * (f i : ℂ) - (∑ i ∈ Finset.Ico N M, b i) * (f M : ℂ))
          ((∑ i ∈ Finset.Ico N M, b i) * (f M : ℂ))
        simpa using this
    _ ≤ 2 * B * (f N - f M) + 2 * B * f M := add_le_add h1 h3
    _ = 2 * B * f N := by ring

/-- **Convergence of `∑ χ(m)/m`**. Dirichlet's test
(`Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded`) with `1/m` antitone to `0` and bounded partial
sums of `χ`. -/
@[kb "eisenstein1847" "Abhandlungen, cubic forms"]
theorem eisensteinSeriesConverges : EisensteinSeriesConverges := by
  intro E _ χ hχ
  have hf : Antitone (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) := by
    intro a b hab
    simp only
    gcongr
  have hf0 : Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hb : ∀ n, ‖∑ i ∈ Finset.range n, χ ((i + 1 : ℕ) : ZMod E)‖ ≤ E + 1 := by
    intro n
    have h := Finset.sum_range_succ' (fun m : ℕ ↦ χ (m : ZMod E)) n
    have h2 : ∑ i ∈ Finset.range n, χ ((i + 1 : ℕ) : ZMod E) =
        ∑ m ∈ Finset.range (n + 1), χ (m : ZMod E) - χ ((0 : ℕ) : ZMod E) := by
      rw [h]; ring
    rw [h2]
    calc _ ≤ ‖∑ m ∈ Finset.range (n + 1), χ (m : ZMod E)‖ + ‖χ ((0 : ℕ) : ZMod E)‖ := norm_sub_le _ _
      _ ≤ E + 1 := add_le_add (norm_sum_range_le hχ _) (χ.norm_le_one _)
  have hc := hf.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 hb
  have hc' : CauchySeq (fun N : ℕ ↦ ∑ m ∈ Finset.range N, χ (m : ZMod E) / (m : ℂ)) := by
    rw [← cauchySeq_shift 1]
    convert hc using 2 with N
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, div_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    push_cast
    rw [Complex.real_smul]
    push_cast
    ring
  exact cauchySeq_tendsto_of_complete hc'

/-- The sum of `∑ χ(m)/m` is Mathlib's `L(χ, 1)` (the value of the analytic continuation). -/
def LSeriesValueAtOne : Prop :=
  ∀ (E : ℕ) [NeZero E] (χ : DirichletCharacter ℂ E), χ ≠ 1 →
    Tendsto (fun N : ℕ ↦ ∑ m ∈ Finset.range N, χ m / m) atTop (𝓝 (DirichletCharacter.LFunction χ 1))

/-- Partial sums of the shifted sequence `χ(i + 1)` are bounded by `E + 1`. -/
lemma norm_sum_shift_le {E : ℕ} [NeZero E] {χ : DirichletCharacter ℂ E} (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, χ ((i + 1 : ℕ) : ZMod E)‖ ≤ E + 1 := by
  have h := Finset.sum_range_succ' (fun m : ℕ ↦ χ (m : ZMod E)) n
  have h2 : ∑ i ∈ Finset.range n, χ ((i + 1 : ℕ) : ZMod E) =
      ∑ m ∈ Finset.range (n + 1), χ (m : ZMod E) - χ ((0 : ℕ) : ZMod E) := by
    rw [h]; ring
  rw [h2]
  calc _ ≤ ‖∑ m ∈ Finset.range (n + 1), χ (m : ZMod E)‖ + ‖χ ((0 : ℕ) : ZMod E)‖ := norm_sub_le _ _
    _ ≤ E + 1 := add_le_add (norm_sum_range_le hχ _) (χ.norm_le_one _)

/-- The `i`-th term (`m = i + 1`) of the real-exponent Dirichlet series. -/
def shiftTerm {E : ℕ} (χ : DirichletCharacter ℂ E) (t : ℝ) (i : ℕ) : ℂ :=
  χ ((i + 1 : ℕ) : ZMod E) * ((((i : ℝ) + 1) ^ (-t) : ℝ) : ℂ)

lemma shiftTerm_eq_term {E : ℕ} (χ : DirichletCharacter ℂ E) (t : ℝ) (i : ℕ) :
    shiftTerm χ t i = LSeries.term (fun n : ℕ ↦ χ n) (t : ℂ) (i + 1) := by
  rw [shiftTerm, LSeries.term_of_ne_zero (Nat.succ_ne_zero i), Complex.ofReal_cpow (by positivity)]
  push_cast
  rw [Complex.cpow_neg, div_eq_mul_inv]

/-- The sum of `∑ χ(m)/m` is Mathlib's `L(χ, 1)`: uniform convergence on `[1, ∞)` (quantitative Abel
summation `abel_tail`) gives continuity of the series at `1` from the right, where it agrees with
`DirichletCharacter.LFunction`. -/
theorem lSeriesValueAtOne : LSeriesValueAtOne := by
  intro E _ χ hχ
  set G : ℕ → ℝ → ℂ := fun N t ↦ ∑ i ∈ Finset.range N, shiftTerm χ t i with hG
  have hunif : UniformCauchySeqOn G atTop (Set.Ici (1 : ℝ)) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * (E + 1) / ε)
    refine ⟨N, fun m hm n hn t ht ↦ ?_⟩
    have ht1 : (1 : ℝ) ≤ t := ht
    have hbound : ∀ a b : ℕ, N ≤ a → a ≤ b → ‖G b t - G a t‖ < ε := by
      intro a b ha hab
      simp only [hG]
      rw [← Finset.sum_Ico_eq_sub _ hab]
      have := abel_tail (fun i ↦ χ ((i + 1 : ℕ) : ZMod E)) (fun i ↦ ((i : ℝ) + 1) ^ (-t))
        (fun x y hxy ↦ Real.rpow_le_rpow_of_nonpos (by positivity) (by simpa using hxy) (by linarith))
        (fun i ↦ by positivity) (E + 1) (norm_sum_shift_le hχ) a b hab
      refine lt_of_le_of_lt this ?_
      have h1 : ((a : ℝ) + 1) ^ (-t) ≤ ((a : ℝ) + 1) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]) (by linarith)
      rw [Real.rpow_neg_one] at h1
      have hNa : (N : ℝ) ≤ a := by exact_mod_cast ha
      have hpos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
      have h2 : 2 * ((E : ℝ) + 1) / ε < (a : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ hε] at h2
      calc 2 * ((E : ℝ) + 1) * ((a : ℝ) + 1) ^ (-t) ≤ 2 * ((E : ℝ) + 1) * ((a : ℝ) + 1)⁻¹ :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ < ε := by
            rw [mul_inv_lt_iff₀ hpos]; linarith
    rcases le_total m n with h | h
    · rw [dist_comm, dist_eq_norm]; exact hbound m n hm h
    · rw [dist_eq_norm]; exact hbound n m hn h
  have hlim : ∀ t ∈ Set.Ici (1 : ℝ), Tendsto (fun N ↦ G N t) atTop (𝓝 (limUnder atTop fun N ↦ G N t)) := by
    intro t ht
    exact (cauchySeq_tendsto_of_complete (hunif.cauchySeq ht)).choose_spec.limUnder_eq ▸
      (cauchySeq_tendsto_of_complete (hunif.cauchySeq ht)).choose_spec
  set F : ℝ → ℂ := fun t ↦ limUnder atTop fun N ↦ G N t with hF
  have hT : TendstoUniformlyOn G F atTop (Set.Ici (1 : ℝ)) :=
    hunif.tendstoUniformlyOn_of_tendsto hlim
  have hcont : ContinuousOn F (Set.Ici (1 : ℝ)) := by
    refine hT.continuousOn (Eventually.of_forall fun N ↦ ?_).frequently
    simp only [hG, shiftTerm]
    refine continuousOn_finsetSum _ fun i _ ↦ ?_
    refine continuous_const.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn ?_)
    exact (Real.continuous_const_rpow (by positivity)).comp_continuousOn continuousOn_neg
  have hG1 : ∀ N : ℕ, G N 1 = ∑ m ∈ Finset.range (N + 1), χ (m : ZMod E) / (m : ℂ) := by
    intro N
    rw [Finset.sum_range_succ']
    simp only [hG, Nat.cast_zero, div_zero, add_zero, shiftTerm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Real.rpow_neg_one]
    push_cast
    ring
  have hGt : ∀ t : ℝ, 1 < t → ∀ N : ℕ,
      G N t = ∑ m ∈ Finset.range (N + 1), LSeries.term (fun n : ℕ ↦ χ n) (t : ℂ) m := by
    intro t _ N
    rw [Finset.sum_range_succ', LSeries.term_zero, add_zero]
    exact Finset.sum_congr rfl fun i _ ↦ shiftTerm_eq_term χ t i
  have hF1 : Tendsto F (𝓝[>] (1 : ℝ)) (𝓝 (F 1)) :=
    ((hcont 1 (Set.mem_Ici.mpr le_rfl)).mono Set.Ioi_subset_Ici_self).tendsto
  have hL : Tendsto (fun t : ℝ ↦ DirichletCharacter.LFunction χ (t : ℂ)) (𝓝[>] (1 : ℝ))
      (𝓝 (DirichletCharacter.LFunction χ 1)) := by
    have := ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp
      Complex.continuous_ofReal).tendsto 1
    have h := tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi (1 : ℝ)) this
    simpa [Function.comp_def] using h
  have hev : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), F t = DirichletCharacter.LFunction χ (t : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 1 < t)
    have hs : 1 < ((t : ℂ)).re := by simpa using ht
    have h1 := hlim t (le_of_lt ht)
    have h2 : Tendsto (fun N ↦ G N t) atTop (𝓝 (LSeries (fun n : ℕ ↦ χ n) (t : ℂ))) := by
      have := (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs).hasSum.tendsto_sum_nat
      have h2' := (tendsto_add_atTop_iff_nat (f := fun n ↦ ∑ m ∈ Finset.range n,
        LSeries.term (fun n : ℕ ↦ χ n) (t : ℂ) m) 1).mpr this
      simp only [hGt t ht]
      exact h2'
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    exact tendsto_nhds_unique h1 h2
  have hEq : F 1 = DirichletCharacter.LFunction χ 1 :=
    tendsto_nhds_unique hF1 (hL.congr' (hev.mono fun t ht ↦ ht.symm))
  have h3 : Tendsto (fun N ↦ G N 1) atTop (𝓝 (F 1)) := hlim 1 (Set.mem_Ici.mpr le_rfl)
  rw [← hEq, ← tendsto_add_atTop_iff_nat 1]
  simpa only [hG1] using h3

/-- **Eisenstein's non-vanishing** (1847): for a character `χ` of order `3` modulo `E`,
`L(χ, 1) L(χ², 1) ≠ 0`, hence each factor is non-zero; and (Eisenstein's general claim) `L(ψ, 1) ≠ 0` for every
non-trivial character `ψ` modulo `E`. -/
@[kb "eisenstein1847" "Abhandlungen, cubic forms"]
def EisensteinNonvanishing : Prop :=
  ∀ (E : ℕ) [NeZero E],
    (∀ χ : DirichletCharacter ℂ E, χ ^ 3 = 1 → χ ≠ 1 →
      DirichletCharacter.LFunction χ 1 * DirichletCharacter.LFunction (χ ^ 2) 1 ≠ 0) ∧
    ∀ ψ : DirichletCharacter ℂ E, ψ ≠ 1 → DirichletCharacter.LFunction ψ 1 ≠ 0

/-- **Eisenstein's non-vanishing**. Wrapper of
`DirichletCharacter.LFunction_apply_one_ne_zero`; for `χ ≠ 1` of order dividing `3`, `χ² ≠ 1`. -/
@[kb "eisenstein1847" "Abhandlungen, cubic forms"]
theorem eisensteinNonvanishing : EisensteinNonvanishing := by
  intro E _
  refine ⟨fun χ h3 hχ ↦ ?_, fun ψ hψ ↦ DirichletCharacter.LFunction_apply_one_ne_zero hψ⟩
  have h2 : χ ^ 2 ≠ 1 := by
    intro h
    apply hχ
    have : χ ^ 3 = χ ^ 2 * χ := by rw [pow_succ]
    rw [h3, h, one_mul] at this
    exact this.symm
  exact mul_ne_zero (DirichletCharacter.LFunction_apply_one_ne_zero hχ)
    (DirichletCharacter.LFunction_apply_one_ne_zero h2)

end ModularFormsKB.Historical.Eisenstein
