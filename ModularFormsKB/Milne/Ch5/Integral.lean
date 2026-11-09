import ModularFormsKB.Milne.Ch5.LevelOne
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Milne, Chapter 5: the $\mathbb Z$-structure on $M_k(\Gamma(1))$ (Propositions 5.26, 5.27)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf p. 79.

$M_k(\mathbb Z)$ is the set of modular forms of weight $2k$ for $\Gamma(1)$ with integer Fourier coefficients
(`integralForms`). A $\mathbb Z$-structure on a complex vector space $V$ is a $\mathbb Z$-submodule freely generated
by a $\mathbb C$-basis of $V$ (Milne's second equivalent formulation).

**Correction to Milne's proof.** The proof of Proposition 5.26 claims $\bigoplus_k M_k(\mathbb Z) = \mathbb Z[E_2, E_3]$
(Milne's $E_2, E_3$ are the normalized Eisenstein series of weights $4$, $6$). This is false: $\Delta$ has integer
coefficients, but $1728\Delta = E_2^3 - E_3^2$ and $E_2, E_3$ are algebraically independent, so
$\Delta \notin \mathbb Z[E_2, E_3]$. The correct ring is $\mathbb Z[E_2, E_3, \Delta]$, and Milne's induction
$f = a_0E_2^aE_3^b + \Delta g$ (with $g$ integral) is the proof of that. The proposition itself is true.

## Items
- The $\mathbb Z$-module $M_k(\mathbb Z)$ (`integralForms`) and Proposition 5.26 (`exists_basis_integralForms`).
- Proposition 5.27 (`isIntegral_of_hasEigenvalue_heckeT`).
-/

open UpperHalfPlane ModularForm

open scoped MatrixGroups ModularForm

namespace ModularFormsKB.Milne

/-! ### Integral power series -/

/-- The subring of power series over `ℂ` with integer coefficients. -/
noncomputable def intSeries : Subring (PowerSeries ℂ) := (PowerSeries.map (Int.castRingHom ℂ)).range

/-- Membership in `intSeries` is integrality of all coefficients. -/
theorem mem_intSeries_iff {p : PowerSeries ℂ} : p ∈ intSeries ↔ ∀ n : ℕ, ∃ m : ℤ, p.coeff n = m := by
  constructor
  · rintro ⟨q, rfl⟩ n
    exact ⟨q.coeff n, by simp [PowerSeries.coeff_map]⟩
  · intro h
    choose m hm using h
    refine ⟨PowerSeries.mk m, ?_⟩
    ext n
    simp [PowerSeries.coeff_map, hm]

/-- The integer power series `∑_{n ≥ 1} σ_k(n) qⁿ`. -/
noncomputable def sigSeries (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then (0 : ℤ) else ((ArithmeticFunction.sigma k n : ℕ) : ℤ)

/-- `E₄ = 1 + 240 ∑ σ₃(n) qⁿ`. -/
theorem qExpansion_E₄_eq : qExpansion 1 E₄ =
    PowerSeries.map (Int.castRingHom ℂ) (1 + PowerSeries.C 240 * sigSeries 3) := by
  ext n
  rw [EisensteinSeries.E_qExpansion_coeff (by norm_num) ⟨2, rfl⟩]
  rw [PowerSeries.coeff_map, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sigSeries]
  · simp [hn.ne', sigSeries, show bernoulli 4 = -1 / 30 by decide +kernel]
    norm_num

/-- `E₆ = 1 - 504 ∑ σ₅(n) qⁿ`. -/
theorem qExpansion_E₆_eq : qExpansion 1 E₆ =
    PowerSeries.map (Int.castRingHom ℂ) (1 - PowerSeries.C 504 * sigSeries 5) := by
  ext n
  rw [EisensteinSeries.E_qExpansion_coeff (by norm_num) ⟨3, rfl⟩]
  rw [PowerSeries.coeff_map, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sigSeries]
  · simp [hn.ne', sigSeries, show bernoulli 6 = 1 / 42 by decide +kernel]
    norm_num

/-- Divisibility needed for the integrality of `Δ`: `12 ∣ 5 σ₃(n) + 7 σ₅(n)`. -/
theorem twelve_dvd_sigma_integral (n : ℕ) :
    (12 : ℤ) ∣ 5 * ((ArithmeticFunction.sigma 3 n : ℕ) : ℤ) + 7 * ((ArithmeticFunction.sigma 5 n : ℕ) : ℤ) := by
  have h : ∀ d : ℤ, (12 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
    intro d
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).mp ?_
    push_cast
    generalize (d : ZMod 12) = x
    revert x
    decide
  simp only [ArithmeticFunction.sigma_apply]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.dvd_sum fun d _ => h d

/-- The `q`-expansion of `Δ` has integer coefficients. -/
theorem qExpansion_discriminant_mem_intSeries : qExpansion 1 discriminant ∈ intSeries := by
  rw [mem_intSeries_iff]
  intro n
  set A := sigSeries 3 with hA
  set B := sigSeries 5 with hB
  have key : qExpansion 1 discriminant = (1728 : ℂ)⁻¹ •
      PowerSeries.map (Int.castRingHom ℂ) ((1 + PowerSeries.C 240 * A) ^ 3 - (1 - PowerSeries.C 504 * B) ^ 2) := by
    rw [TauCeti.ModularForm.qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq, qExpansion_E₄_eq, qExpansion_E₆_eq]
    simp only [map_sub, map_pow, hA, hB]
  have hD : (1 + PowerSeries.C 240 * A) ^ 3 - (1 - PowerSeries.C 504 * B) ^ 2 =
      PowerSeries.C 720 * A + PowerSeries.C 1008 * B +
        PowerSeries.C 1728 * (PowerSeries.C 100 * A ^ 2 - PowerSeries.C 147 * B ^ 2 + PowerSeries.C 8000 * A ^ 3) := by
    simp only [map_ofNat]
    ring
  have hdvd : (1728 : ℤ) ∣ ((1 + PowerSeries.C 240 * A) ^ 3 - (1 - PowerSeries.C 504 * B) ^ 2).coeff n := by
    rw [hD, map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hA, hB, sigSeries]
    · obtain ⟨t, ht⟩ := twelve_dvd_sigma_integral n
      refine ⟨t + (PowerSeries.coeff n) (PowerSeries.C 100 * A ^ 2 - PowerSeries.C 147 * B ^ 2 + PowerSeries.C 8000 * A ^ 3), ?_⟩
      simp only [hA, hB, sigSeries, PowerSeries.coeff_mk, hn.ne', ite_false]
      linear_combination 144 * ht
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨t, ?_⟩
  rw [key, PowerSeries.coeff_smul, PowerSeries.coeff_map, ht]
  simp only [smul_eq_mul, eq_intCast, Int.cast_mul]
  push_cast
  field_simp

/-- The number of leading `q`-coefficients that determine a form of weight `2n` (the dimension of `M_{2n}`). -/
def dimCount (n : ℕ) : ℕ := (2 * n) / 12 + if (2 * n) % 12 = 2 then 0 else 1

/-- A level-one form of weight `2n` whose `q`-expansion has order at least `dimCount n` vanishes. -/
theorem eq_zero_of_dimCount_le_order (n : ℕ) : ∀ (W : ℤ), W = 2 * n → ∀ f : ModularForm 𝒮ℒ W,
    (dimCount n : ℕ∞) ≤ (qExpansion 1 f).order → f = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hW f hf
  have hd : 1 ≤ dimCount n ∨ n = 1 := by
    unfold dimCount
    split_ifs with h <;> omega
  rcases hd with hd | rfl
  swap
  · obtain rfl : W = 2 := by simpa using hW
    exact rank_zero_iff_forall_zero.mp levelOne_weight_two_rank_zero f
  have h0 : (qExpansion 1 f).coeff 0 = 0 :=
    PowerSeries.coeff_of_lt_order _ (lt_of_lt_of_le (by exact_mod_cast hd) hf)
  suffices CuspForm.discriminantEquiv (toCuspForm f h0) = 0 by
    simpa [CuspForm.discriminantEquiv.map_eq_zero_iff, DFunLike.ext_iff] using this
  rcases lt_or_ge n 6 with hn | hn
  · have hz := rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (k := W) (by omega))
      (toCuspForm f h0)
    rw [hz]
    simp
  · have hmul := qExpansion_eq_qExpansion_discriminant_mul f h0
    rw [hmul, PowerSeries.order_mul, discriminant_qExpansion_order] at hf
    have hdc : dimCount n = dimCount (n - 6) + 1 := by
      unfold dimCount
      split_ifs <;> omega
    rw [hdc, Nat.cast_add, Nat.cast_one, add_comm (1 : ℕ∞)] at hf
    have hf' := (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp hf
    exact ih (n - 6) (by omega) (W - 12) (by omega) _ hf'

/-- A form of weight `W` with `q`-expansion `qⁱ r`, where `r` has integer coefficients and constant term `1`. -/
def LeadingForm (W : ℤ) (i : ℕ) : Prop :=
  ∃ (g : ModularForm 𝒮ℒ W) (r : PowerSeries ℂ), r ∈ intSeries ∧ PowerSeries.constantCoeff r = 1 ∧
    qExpansion 1 g = PowerSeries.X ^ i * r

theorem LeadingForm.congr {W W' : ℤ} {i : ℕ} (h : W = W') (hg : LeadingForm W i) : LeadingForm W' i := by
  subst h
  exact hg

theorem leadingForm_zero : LeadingForm 0 0 :=
  ⟨1, 1, one_mem _, by simp, by rw [pow_zero, one_mul]; exact ModularForm.qExpansion_one⟩

theorem LeadingForm.mul {W V : ℤ} {i : ℕ} (hg : LeadingForm W i) (h : ModularForm 𝒮ℒ V) (u : PowerSeries ℂ)
    (hu : u ∈ intSeries) (hc : PowerSeries.constantCoeff u = 1) (hh : qExpansion 1 h = u) :
    LeadingForm (W + V) i := by
  obtain ⟨g, r, hr, hrc, hgr⟩ := hg
  refine ⟨g.mul h, r * u, mul_mem hr hu, by simp [hrc, hc], ?_⟩
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL, hgr, hh, mul_assoc]

theorem LeadingForm.mul_E₄ {W : ℤ} {i : ℕ} (hg : LeadingForm W i) : LeadingForm (W + 4) i :=
  hg.mul E₄ _ (by rw [qExpansion_E₄_eq]; exact ⟨_, rfl⟩) (by simpa using EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 4) ⟨2, rfl⟩) rfl

theorem LeadingForm.mul_E₆ {W : ℤ} {i : ℕ} (hg : LeadingForm W i) : LeadingForm (W + 6) i :=
  hg.mul E₆ _ (by rw [qExpansion_E₆_eq]; exact ⟨_, rfl⟩) (by simpa using EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 6) ⟨3, rfl⟩) rfl

theorem LeadingForm.mul_discriminant {W : ℤ} {i : ℕ} (hg : LeadingForm W i) : LeadingForm (W + 12) (i + 1) := by
  set Δm : ModularForm 𝒮ℒ 12 := CuspForm.toModularFormₗ CuspForm.discriminant with hΔm
  have h1 : qExpansion 1 Δm = qExpansion 1 discriminant := rfl
  have h0 : (qExpansion 1 discriminant).coeff 0 = 0 := TauCeti.ModularForm.discriminant_qExpansion_coeff_zero
  let u : PowerSeries ℂ := PowerSeries.mk fun n => (qExpansion 1 discriminant).coeff (n + 1)
  have hX : qExpansion 1 discriminant = PowerSeries.X * u := by
    ext n
    rcases n with _ | n
    · simp [h0]
    · simp [u, PowerSeries.coeff_succ_X_mul]
  have hu : u ∈ intSeries := by
    rw [mem_intSeries_iff]
    intro n
    obtain ⟨m, hm⟩ := mem_intSeries_iff.mp qExpansion_discriminant_mem_intSeries (n + 1)
    exact ⟨m, by simpa [u] using hm⟩
  obtain ⟨g, r, hr, hrc, hgr⟩ := hg
  refine ⟨g.mul Δm, r * u, mul_mem hr hu, ?_, ?_⟩
  · rw [map_mul, hrc, one_mul]
    have hu1 : PowerSeries.constantCoeff u = (qExpansion 1 discriminant).coeff 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact PowerSeries.coeff_mk 0 _
    rw [hu1]
    exact discriminant_qExpansion_coeff_one
  · rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL, hgr, h1, hX, mul_mul_mul_comm,
      ← pow_succ]

/-- $M_k(\mathbb Z)$: the modular forms of weight $2k$ for $\Gamma(1)$ whose Fourier coefficients are integers. -/
@[kb "milne2017mf" "Section 5, the module M_k(Z) (pdf p. 79)"]
def integralForms (k : ℕ) : Submodule ℤ (ModularForm 𝒮ℒ (2 * k)) where
  carrier := {f | ∀ n : ℕ, ∃ m : ℤ, (qExpansion 1 f).coeff n = m}
  add_mem' := by
    intro a b ha hb n
    obtain ⟨x, hx⟩ := ha n
    obtain ⟨y, hy⟩ := hb n
    refine ⟨x + y, ?_⟩
    rw [FunLike.coe_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL, map_add, hx, hy]
    push_cast
    rfl
  zero_mem' := by
    intro n
    refine ⟨0, ?_⟩
    have : ((0 : ModularForm 𝒮ℒ (2 * k)) : ℍ → ℂ) = 0 := rfl
    rw [this, qExpansion_zero]
    simp
  smul_mem' := by
    intro c a ha n
    obtain ⟨x, hx⟩ := ha n
    refine ⟨c * x, ?_⟩
    have : ((c • a : ModularForm 𝒮ℒ (2 * k)) : ℍ → ℂ) = (c : ℂ) • (a : ℍ → ℂ) := by
      ext z
      simp
    rw [this, qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero a one_pos one_mem_strictPeriods_SL),
      PowerSeries.coeff_smul, hx]
    push_cast
    rfl

theorem leadingForm_exists (i a b : ℕ) : LeadingForm ((12 * i + 4 * a + 6 * b : ℕ) : ℤ) i := by
  have h1 : ∀ i : ℕ, LeadingForm ((12 * i : ℕ) : ℤ) i := by
    intro i
    induction i with
    | zero => simpa using leadingForm_zero
    | succ i ih => exact ih.mul_discriminant.congr (by push_cast; ring)
  have h2 : ∀ i a : ℕ, LeadingForm ((12 * i + 4 * a : ℕ) : ℤ) i := by
    intro i a
    induction a with
    | zero => simpa using h1 i
    | succ a ih => exact ih.mul_E₄.congr (by push_cast; ring)
  induction b with
  | zero => simpa using h2 i a
  | succ b ih => exact ih.mul_E₆.congr (by push_cast; ring)

/-- The `j`-th `q`-coefficient as a linear functional. -/
noncomputable def coeffLin (W : ℤ) (j : ℕ) : ModularForm 𝒮ℒ W →ₗ[ℂ] ℂ where
  toFun f := (qExpansion 1 ⇑f).coeff j
  map_add' f g := by
    rw [FunLike.coe_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL, map_add]
  map_smul' c f := by
    rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, PowerSeries.coeff_smul]
    rfl

theorem coeffLin_apply (W : ℤ) (j : ℕ) (f : ModularForm 𝒮ℒ W) :
    coeffLin W j f = (qExpansion 1 ⇑f).coeff j := rfl

/-- Existence of an integral form of weight `2k` with leading term `qⁱ`, for `i < dimCount k`. -/
theorem exists_leading (k i : ℕ) (hi : i < dimCount k) :
    ∃ g ∈ integralForms k, (∀ j < i, (qExpansion 1 ⇑g).coeff j = 0) ∧ (qExpansion 1 ⇑g).coeff i = 1 := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, 12 * i + 4 * a + 6 * b = 2 * k := by
    unfold dimCount at hi
    obtain ⟨a, b, h1, h2⟩ : ∃ a b : ℕ, 4 * a + 6 * b = 2 * k - 12 * i ∧ 12 * i ≤ 2 * k := by
      split_ifs at hi with h
      · by_cases h4 : (2 * k - 12 * i) % 4 = 0
        · exact ⟨(2 * k - 12 * i) / 4, 0, by omega, by omega⟩
        · exact ⟨(2 * k - 12 * i - 6) / 4, 1, by omega, by omega⟩
      · by_cases h4 : (2 * k - 12 * i) % 4 = 0
        · exact ⟨(2 * k - 12 * i) / 4, 0, by omega, by omega⟩
        · exact ⟨(2 * k - 12 * i - 6) / 4, 1, by omega, by omega⟩
    exact ⟨a, b, by omega⟩
  have hL := leadingForm_exists i a b
  rw [hab] at hL
  obtain ⟨g, r, hr, hrc, hgr⟩ := hL
  have hgm : g ∈ integralForms k := by
    intro n
    have hX : (PowerSeries.X : PowerSeries ℂ) ∈ intSeries := ⟨PowerSeries.X, by simp⟩
    have : qExpansion 1 ⇑g ∈ intSeries := by
      rw [hgr]
      exact mul_mem (pow_mem hX _) hr
    exact mem_intSeries_iff.mp this n
  refine ⟨g, hgm, fun j hj => ?_, ?_⟩
  · rw [hgr, PowerSeries.coeff_X_pow_mul']
    simp [Nat.not_le.mpr hj]
  · rw [hgr, PowerSeries.coeff_X_pow_mul']
    simpa using hrc

/-- Miller-type dual forms: an integral form with `q`-coefficients `δ_{ij}` for `j < dimCount k`. -/
theorem exists_dual (k : ℕ) : ∀ t i : ℕ, i < dimCount k → dimCount k - i ≤ t →
    ∃ f ∈ integralForms k, ∀ j < dimCount k, (qExpansion 1 ⇑f).coeff j = if j = i then 1 else 0 := by
  intro t
  induction t with
  | zero => intro i hi ht; omega
  | succ t ih =>
    intro i hi ht
    obtain ⟨g, hg, hg0, hg1⟩ := exists_leading k i hi
    have hF : ∀ l, i < l → l < dimCount k → ∃ f ∈ integralForms k, ∀ j < dimCount k,
        (qExpansion 1 ⇑f).coeff j = if j = l then 1 else 0 := fun l hl hld => ih l hld (by omega)
    choose! F hFm hFc using hF
    have hg' : ∀ n : ℕ, ∃ m : ℤ, (qExpansion 1 ⇑g).coeff n = m := hg
    choose c hc using hg'
    refine ⟨g - ∑ l ∈ Finset.Ioo i (dimCount k), c l • F l,
      sub_mem hg (sum_mem fun l hl => ?_), fun j hj => ?_⟩
    · have hl' := Finset.mem_Ioo.mp hl
      exact Submodule.smul_mem _ _ (hFm l hl'.1 hl'.2)
    · have h1 : (qExpansion 1 ⇑(g - ∑ l ∈ Finset.Ioo i (dimCount k), c l • F l)).coeff j =
          coeffLin (2 * k) j (g - ∑ l ∈ Finset.Ioo i (dimCount k), c l • F l) := rfl
      rw [h1]
      simp only [map_sub, map_sum, map_zsmul, zsmul_eq_mul, coeffLin_apply]
      rw [Finset.sum_congr rfl (fun l hl => by
        rw [hFc l (Finset.mem_Ioo.mp hl).1 (Finset.mem_Ioo.mp hl).2 j hj])]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_Ioo]
      rw [hc j]
      rcases lt_trichotomy j i with h | h | h
      · have h0 := hg0 j h
        rw [hc j] at h0
        simp [h0, h.ne, not_lt.mpr h.le]
      · subst h
        have h0 := hg1
        rw [hc j] at h0
        simp [h0]
      · simp [h, hj, h.ne']

/-- **Milne, Proposition 5.26.** $M_k(\mathbb Z)$ is a $\mathbb Z$-structure on $M_k(\Gamma(1))$: there is a
$\mathbb C$-basis of $M_k(\Gamma(1))$ consisting of forms with integer coefficients that generates $M_k(\mathbb Z)$
freely as a $\mathbb Z$-module. -/
@[kb "milne2017mf" "Section 5, Proposition 5.26 (pdf p. 79)"]
theorem exists_basis_integralForms (k : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℂ (ModularForm 𝒮ℒ (2 * k))),
      (∀ i, b i ∈ integralForms k) ∧
        ∀ f ∈ integralForms k, ∃ c : ι → ℤ, f = ∑ i, (c i : ℂ) • b i := by
  have hdual : ∀ i : Fin (dimCount k), ∃ f ∈ integralForms k, ∀ j < dimCount k,
      (qExpansion 1 ⇑f).coeff j = if j = i then 1 else 0 :=
    fun i => exists_dual k (dimCount k) i i.2 (by omega)
  choose v hvm hvc using hdual
  have hcoef : ∀ (c : Fin (dimCount k) → ℂ) (j : Fin (dimCount k)),
      coeffLin (2 * k) j (∑ i : Fin (dimCount k), c i • v i) = c j := by
    intro c j
    rw [map_sum, Finset.sum_eq_single j]
    · simp [coeffLin_apply, hvc j j j.2]
    · intro i _ hij
      have : (j : ℕ) ≠ i := fun h => hij (Fin.ext h.symm)
      simp [coeffLin_apply, hvc i j j.2, this]
    · simp
  have hexp : ∀ f : ModularForm 𝒮ℒ (2 * k), f = ∑ i : Fin (dimCount k), coeffLin (2 * k) (i : ℕ) f • v i := by
    intro f
    have h0 : f - ∑ i : Fin (dimCount k), coeffLin (2 * k) (i : ℕ) f • v i = 0 := by
      refine eq_zero_of_dimCount_le_order k _ rfl _ (PowerSeries.nat_le_order _ _ fun j hj => ?_)
      have := hcoef (fun i : Fin (dimCount k) => coeffLin (2 * k) (i : ℕ) f) ⟨j, hj⟩
      change coeffLin (2 * k) j (f - ∑ i : Fin (dimCount k), coeffLin (2 * k) (i : ℕ) f • v i) = 0
      rw [map_sub, this]
      simp
    exact sub_eq_zero.mp h0
  have hli : LinearIndependent ℂ v := by
    refine Fintype.linearIndependent_iff.mpr fun c hc i => ?_
    have := congrArg (coeffLin (2 * k) i) hc
    rw [hcoef] at this
    simpa using this
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    intro f _
    rw [hexp f]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨Fin (dimCount k), inferInstance, Module.Basis.mk hli hsp, fun i => ?_, fun f hf => ?_⟩
  · rw [Module.Basis.mk_apply]
    exact hvm i
  · have hf' : ∀ n : ℕ, ∃ m : ℤ, (qExpansion 1 ⇑f).coeff n = m := hf
    choose m hm using hf'
    refine ⟨fun i => m i, ?_⟩
    conv_lhs => rw [hexp f]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.Basis.mk_apply, coeffLin_apply, hm]

/-- For `k ≥ 1`, `T(n)` preserves `M_k(ℤ)` (the exponent `2k - 1` is a natural number). -/
theorem heckeT_mem_integralForms (k : ℕ) (hk : 0 < k) {n : ℕ} (hn : n ≠ 0) {f : ModularForm 𝒮ℒ (2 * k)}
    (hf : f ∈ integralForms k) : heckeT (2 * k) n f ∈ integralForms k := by
  have hf' : ∀ n : ℕ, ∃ m : ℤ, (qExpansion 1 ⇑f).coeff n = m := hf
  choose c hc using hf'
  intro m
  refine ⟨∑ a ∈ (Nat.gcd m n).divisors, ((a : ℤ) ^ (2 * k - 1)) * c (m * n / a ^ 2), ?_⟩
  rw [qExpansion_coeff_heckeT k hn f m]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hc, show ((2 * k : ℤ) - 1) = ((2 * k - 1 : ℕ) : ℤ) by omega, zpow_natCast]

/-- Counterexample to Proposition 5.27 as stated for `k = 0` (where `2k - 1 = -1`): `T(2)` acts on the constants
`M_0 = ℂ` by `σ_{-1}(2) = 3/2`, which is not an algebraic integer. -/
theorem exists_nonintegral_eigenvalue_heckeT_zero :
    ∃ μ : ℂ, Module.End.HasEigenvalue (heckeT (2 * ((0 : ℕ) : ℤ)) 2) μ ∧ ¬ IsIntegral ℤ μ := by
  let f : ModularForm 𝒮ℒ (2 * ((0 : ℕ) : ℤ)) := (1 : ModularForm 𝒮ℒ 0)
  have hf : qExpansion 1 ⇑f = 1 := ModularForm.qExpansion_one
  have hfc : ∀ j : ℕ, (qExpansion 1 ⇑f).coeff j = if j = 0 then 1 else 0 := by
    intro j
    rw [hf, PowerSeries.coeff_one]
  have hne : f ≠ 0 := by
    intro h
    have := congrArg (fun g : ModularForm 𝒮ℒ (2 * ((0 : ℕ) : ℤ)) => (qExpansion 1 ⇑g).coeff 0) h
    have h2 : (qExpansion 1 ⇑(0 : ModularForm 𝒮ℒ (2 * ((0 : ℕ) : ℤ)))).coeff 0 = 0 := by
      have : ((0 : ModularForm 𝒮ℒ (2 * ((0 : ℕ) : ℤ))) : ℍ → ℂ) = 0 := rfl
      rw [this, qExpansion_zero]
      simp
    rw [hfc 0, h2] at this
    simp at this
  have hT : heckeT (2 * ((0 : ℕ) : ℤ)) 2 f = (3 / 2 : ℂ) • f := by
    refine (ModularForm.qExpansion_inj one_pos one_mem_strictPeriods_SL).mp ?_
    ext m
    rw [qExpansion_coeff_heckeT 0 (by norm_num) f m, FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, PowerSeries.coeff_smul, hfc m]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [Nat.prime_two.divisors, hfc]
      norm_num
    · rw [Finset.sum_eq_zero]
      · simp [hm.ne']
      · intro a ha
        rw [Nat.mem_divisors] at ha
        have h2 : a ∣ 2 := ha.1.trans (Nat.gcd_dvd_right _ _)
        have hm' : a ∣ m := ha.1.trans (Nat.gcd_dvd_left _ _)
        rcases (Nat.dvd_prime Nat.prime_two).mp h2 with rfl | rfl
        · simp [hfc, hm.ne']
        · obtain ⟨t, rfl⟩ := hm'
          have : 2 * t * 2 / 2 ^ 2 = t := by omega
          rw [this, hfc]
          have : t ≠ 0 := by omega
          simp [this]
  refine ⟨3 / 2, Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.mpr hT, hne⟩, ?_⟩
  intro h
  have h' : IsIntegral ℤ ((3 / 2 : ℚ) : ℂ) := by simpa using h
  rw [show (((3 / 2 : ℚ)) : ℂ) = algebraMap ℚ ℂ (3 / 2) by simp,
    isIntegral_algebraMap_iff] at h'
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
  have : (2 * y : ℚ) = 3 := by
    simp only [eq_intCast] at hy
    rw [hy]; norm_num
  have : 2 * y = 3 := by exact_mod_cast this
  omega

/-- **Milne, Proposition 5.27.** The eigenvalues of the Hecke operators $T(n)$ on $M_k(\Gamma(1))$ are algebraic
integers, for weight $2k \ge 2$. In weight $0$ the statement fails: with Milne's normalization $n^{2k-1} = n^{-1}$,
$T(2)$ acts on the constants by $\sigma_{-1}(2) = 3/2$ (`exists_nonintegral_eigenvalue_heckeT_zero`). -/
@[kb "milne2017mf" "Section 5, Proposition 5.27 (pdf p. 79)"]
theorem isIntegral_of_hasEigenvalue_heckeT {k : ℕ} (hk : 0 < k) {n : ℕ} (hn : 0 < n) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (heckeT (2 * k) n) μ) : IsIntegral ℤ μ := by
  classical
  obtain ⟨ι, _, b, hbm, hbs⟩ := exists_basis_integralForms k
  have hT : ∀ j, ∃ c : ι → ℤ, heckeT (2 * k) n (b j) = ∑ i, (c i : ℂ) • b i :=
    fun j => hbs _ (heckeT_mem_integralForms k hk hn.ne' (hbm j))
  choose c hc using hT
  let N : Matrix ι ι ℤ := Matrix.of fun i j => c j i
  have hM : LinearMap.toMatrix b b (heckeT (2 * k) n) = N.map (Int.castRingHom ℂ) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hc j, b.repr_sum_self]
    simp [N]
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, ← LinearMap.charpoly_toMatrix _ b, hM,
    Matrix.charpoly_map] at hμ
  refine ⟨N.charpoly, Matrix.charpoly_monic N, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map]
  exact hμ

end ModularFormsKB.Milne
