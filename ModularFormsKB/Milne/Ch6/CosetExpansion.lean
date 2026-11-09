import ModularFormsKB.Milne.Ch6.Rationality
import ModularFormsKB.Milne.Ch6.JIntegral

/-!
# $q$-expansions of the conjugates $j(N\gamma z)$ with algebraic integer coefficients

Write $z = Nu$ and $q = e^{2\pi i u}$. For a coset $\Gamma_0(N)\gamma$ the Hermite normal form gives
$j(N\gamma z) = j((az + b)/d)$ with $ad = N$ (`ModularFormsKB.Milne.HNF.exists_SL2Z_mul_upper`), and
$(az+b)/d = a^2u + b/d$, so $e^{2\pi i (az+b)/d} = \zeta q^{a^2}$ with $\zeta = e^{2\pi i b/d}$ a root of unity. Hence
$q^{a^2} j(N\gamma z) = \zeta^{-1}\sum_n c_n \zeta^n q^{a^2 n}$ with $qj = \sum_n c_n q^n$, $c_n \in \mathbb Z$, and
$q^{N^2} j(N\gamma(Nu))$ is an absolutely convergent power series in $q$ with algebraic integer coefficients
(`expands_coset`). The coefficients of $\prod_c (Y - j(N\gamma_c z))$, multiplied by suitable powers of $q$, are then
power series with algebraic integer coefficients (`expands_coeff_prod`). This is the integrality step of Milne,
Section 6, proof of Theorem 6.1 (pdf p. 88), with the Galois action replaced by the rationality already proved
(`ModularFormsKB.Milne.LevelTwo.coeff_coeff_isRat`).
-/

open UpperHalfPlane CongruenceSubgroup Polynomial
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.LevelTwo

open TauCeti.ModularForm QSeries

local notation "𝕢" => Function.Periodic.qParam

/-- Power series over $\mathbb C$ with all coefficients in the subring $S$. -/
def coeffSubring (S : Subring ℂ) : Subring (PowerSeries ℂ) := (PowerSeries.map S.subtype).range

theorem mem_coeffSubring {S : Subring ℂ} {A : PowerSeries ℂ} :
    A ∈ coeffSubring S ↔ ∀ n, PowerSeries.coeff n A ∈ S := by
  constructor
  · rintro ⟨g, rfl⟩ n
    simp
  · intro h
    refine ⟨PowerSeries.mk fun n ↦ ⟨_, h n⟩, ?_⟩
    ext n
    simp

/-- The algebraic integers in $\mathbb C$. -/
abbrev algInt : Subring ℂ := (integralClosure ℤ ℂ).toSubring

theorem mem_algInt {x : ℂ} : x ∈ algInt ↔ IsIntegral ℤ x := mem_integralClosure_iff ℤ ℂ

theorem X_pow_mem_coeffSubring (S : Subring ℂ) (m : ℕ) : (PowerSeries.X ^ m : PowerSeries ℂ) ∈ coeffSubring S :=
  Subring.pow_mem _ (mem_coeffSubring.2 fun n ↦ by
    rw [PowerSeries.coeff_X]
    split_ifs
    exacts [S.one_mem, S.zero_mem]) _

theorem C_mem_coeffSubring {S : Subring ℂ} {x : ℂ} (hx : x ∈ S) : PowerSeries.C x ∈ coeffSubring S := by
  refine mem_coeffSubring.2 fun n ↦ ?_
  rw [PowerSeries.coeff_C]
  split_ifs
  exacts [hx, S.zero_mem]

/-- A rational number that is an algebraic integer is an integer. -/
theorem exists_int_of_rat_of_isIntegral (r : ℚ) (h : IsIntegral ℤ (r : ℂ)) : ∃ n : ℤ, (n : ℂ) = r := by
  have h' : IsIntegral ℤ r := by
    exact (isIntegral_algHom_iff ((Rat.castHom ℂ).toIntAlgHom) (RingHom.injective _) (x := r)).1
      (by simpa using h)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h'
  exact ⟨n, by rw [← hn]; simp⟩

theorem _root_.ModularFormsKB.Milne.QSeries.Expands.congr {f g : ℍ → ℂ} {A : PowerSeries ℂ} (h : Expands f A) (hfg : ∀ z, f z = g z) :
    Expands g A := by
  have : f = g := funext hfg
  rwa [← this]

theorem _root_.ModularFormsKB.Milne.QSeries.Expands.neg {f : ℍ → ℂ} {A : PowerSeries ℂ} (h : Expands f A) :
    Expands (fun z ↦ -f z) (-A) := by
  have := h.const_mul (-1)
  simpa [neg_one_mul, map_neg] using this

theorem _root_.ModularFormsKB.Milne.QSeries.Expands.sub {f g : ℍ → ℂ} {A B : PowerSeries ℂ} (hf : Expands f A) (hg : Expands g B) :
    Expands (fun z ↦ f z - g z) (A - B) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- $\sum_n c_n (\zeta q^m)^n$: the expansion of $qj$ at a point $w(u)$ with $e^{2\pi i w(u)} = \zeta q^m$. -/
theorem expands_qParam_mul_j_comp (m : ℕ) (hm : 0 < m) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (w : ℍ → ℍ)
    (hw : ∀ u : ℍ, 𝕢 1 ((w u : ℍ) : ℂ) = ζ * 𝕢 1 (u : ℂ) ^ m) :
    Expands (fun u ↦ 𝕢 1 ((w u : ℍ) : ℂ) * j (w u))
      (PowerSeries.expand m hm.ne' (PowerSeries.rescale ζ (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)))) := by
  intro u
  obtain ⟨hs, hh⟩ := expands_qParam_mul_j (w u)
  rw [hw u] at hs hh
  set P := qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ) with hP
  have hinj : Function.Injective (fun k : ℕ ↦ m * k) := mul_right_injective₀ hm.ne'
  have hco : ∀ n ∉ Set.range (fun k : ℕ ↦ m * k),
      PowerSeries.coeff n (PowerSeries.expand m hm.ne' (PowerSeries.rescale ζ P)) = 0 := by
    intro n hn
    rw [PowerSeries.coeff_expand, ite_eq_right_iff]
    rintro ⟨k, rfl⟩
    exact absurd ⟨k, rfl⟩ hn
  have hco' : ∀ k, PowerSeries.coeff (m * k) (PowerSeries.expand m hm.ne' (PowerSeries.rescale ζ P)) =
      ζ ^ k * PowerSeries.coeff k P := fun k ↦ by
    rw [PowerSeries.coeff_expand_mul, PowerSeries.coeff_rescale]
  refine ⟨?_, ?_⟩
  · refine (hinj.summable_iff (f := fun n ↦ ‖PowerSeries.coeff n (PowerSeries.expand m hm.ne'
      (PowerSeries.rescale ζ P))‖ * ‖𝕢 1 (u : ℂ)‖ ^ n) ?_).mp ?_
    · intro n hn
      simp [hco n hn]
    · refine hs.congr fun k ↦ ?_
      simp only [Function.comp_apply, hco', norm_mul, norm_pow, hζ, one_pow, one_mul, pow_mul]
  · refine (hinj.hasSum_iff (f := fun n ↦ PowerSeries.coeff n (PowerSeries.expand m hm.ne'
      (PowerSeries.rescale ζ P)) * 𝕢 1 (u : ℂ) ^ n) ?_).mp ?_
    · intro n hn
      simp [hco n hn]
    · convert hh using 1
      funext k
      simp only [Function.comp_apply, hco', mul_pow, pow_mul]
      ring

variable {N : ℕ} (hN : 0 < N)

/-- Every conjugate $j(N\gamma z)$ is $j((az+b)/d)$ with $ad = N$, $a, d > 0$. -/
theorem exists_cosetVal_eq (c : Cosets N) : ∃ (a d : ℕ) (b : ℤ) (ha : 0 < a) (hd : 0 < d), a * d = N ∧
    ∀ z : ℍ, cosetVal hN c z = j (affineH a b d (by exact_mod_cast ha) (by exact_mod_cast hd) z) := by
  induction c using Quotient.inductionOn with
  | h γ =>
    have hdet : 0 < (!![(N : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ)).det := by
      rw [Matrix.det_mul, γ.det_coe]; simp [Matrix.det_fin_two_of]; exact hN
    obtain ⟨δ, a, b, d, ha, hd, -, -, hM⟩ := ModularFormsKB.Milne.HNF.exists_SL2Z_mul_upper _ hdet
    have hadet : a * d = N := by
      have := congrArg Matrix.det hM
      rw [Matrix.det_mul, Matrix.det_mul, γ.det_coe, δ.det_coe] at this
      simpa [Matrix.det_fin_two_of] using this.symm
    lift a to ℕ using ha.le
    lift d to ℕ using hd.le
    refine ⟨a, d, b, by exact_mod_cast ha, by exact_mod_cast hd, by exact_mod_cast hadet, fun z ↦ ?_⟩
    rw [cosetVal_mk, jN, scaleH_smul_eq hN γ δ a b d ha hd hM z, jSL]

theorem intCast_mem_algInt (r : ℤ) : (r : ℂ) ∈ algInt := by
  rw [mem_algInt]
  simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := r))

/-- **The conjugate $q^{N^2} j(N\gamma(Nu))$ is a power series in $q = e^{2\pi i u}$ with algebraic integer
coefficients.** -/
theorem expands_coset (c : Cosets N) : ∃ B ∈ coeffSubring algInt,
    Expands (fun u ↦ 𝕢 1 (u : ℂ) ^ (N * N) * cosetVal hN c (scaleH N hN u)) B := by
  obtain ⟨a, d, b, ha, hd, had, hc⟩ := exists_cosetVal_eq hN c
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * (b / d)) with hζ
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hζ1 : ‖ζ‖ = 1 := by
    have : (2 * Real.pi * Complex.I * (b / d) : ℂ) = ((2 * Real.pi * b / d : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hζ, this, Complex.norm_exp_ofReal_mul_I]
  have hζd : ζ ^ d = 1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    have : (d : ℂ) * (2 * Real.pi * Complex.I * (b / d)) = (b : ℂ) * (2 * Real.pi * Complex.I) := by
      field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have hζint : IsIntegral ℤ ζ := IsIntegral.of_pow hd (by rw [hζd]; exact isIntegral_one)
  have hζiint : IsIntegral ℤ ζ⁻¹ := IsIntegral.of_pow hd (by rw [inv_pow, hζd, inv_one]; exact isIntegral_one)
  have haN : a * a ≤ N * N := by
    have : a ≤ N := by rw [← had]; exact Nat.le_mul_of_pos_right a hd
    exact Nat.mul_le_mul this this
  set w : ℍ → ℍ := fun u ↦ affineH a b d (by exact_mod_cast ha) (by exact_mod_cast hd) (scaleH N hN u)
    with hwdef
  have hw : ∀ u : ℍ, 𝕢 1 ((w u : ℍ) : ℂ) = ζ * 𝕢 1 (u : ℂ) ^ (a * a) := by
    intro u
    simp only [hwdef, affineH, scaleH, Function.Periodic.qParam, UpperHalfPlane.coe_mk, hζ]
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    have hN' : (N : ℂ) = (a : ℂ) * d := by exact_mod_cast had.symm
    rw [hN']
    push_cast
    field_simp
    ring
  have h1 := expands_qParam_mul_j_comp (a * a) (Nat.mul_pos ha ha) ζ hζ1 w hw
  have h3 := (expands_qParam_pow (N * N - a * a)).mul (h1.const_mul ζ⁻¹)
  refine ⟨_, ?_, h3.congr fun u ↦ ?_⟩
  · refine Subring.mul_mem _ (X_pow_mem_coeffSubring _ _) (Subring.mul_mem _
      (C_mem_coeffSubring (mem_algInt.2 hζiint)) (mem_coeffSubring.2 fun n ↦ ?_))
    rw [PowerSeries.coeff_expand]
    split_ifs
    · rw [PowerSeries.coeff_rescale]
      obtain ⟨r, hr⟩ := JCoefficients.j_coeff_isInt (n / (a * a))
      rw [← hr]
      exact Subring.mul_mem _ (Subring.pow_mem _ (mem_algInt.2 hζint) _) (intCast_mem_algInt r)
    · exact Subring.zero_mem _
  · rw [hc (scaleH N hN u), hw u]
    have : 𝕢 1 (u : ℂ) ^ (N * N) = 𝕢 1 (u : ℂ) ^ (N * N - a * a) * 𝕢 1 (u : ℂ) ^ (a * a) := by
      rw [← pow_add, Nat.sub_add_cancel haN]
    rw [this]
    field_simp
    rfl

/-- **Coefficients of $\prod_i (Y - v_i)$**: if every $q^M v_i$ is a power series with coefficients in $S$, then so
is $q^{M(n - k)}$ times the coefficient of $Y^k$, $n$ the number of factors. -/
theorem expands_coeff_prod {S : Subring ℂ} (M : ℕ) {ι : Type*} (s : Finset ι) (v : ι → ℍ → ℂ)
    (hv : ∀ i ∈ s, ∃ B ∈ coeffSubring S, Expands (fun u ↦ 𝕢 1 (u : ℂ) ^ M * v i u) B) :
    ∀ k ≤ s.card, ∃ B ∈ coeffSubring S,
      Expands (fun u ↦ 𝕢 1 (u : ℂ) ^ (M * (s.card - k)) * (∏ i ∈ s, (X - C (v i u))).coeff k) B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro k hk
    simp only [Finset.card_empty, nonpos_iff_eq_zero] at hk
    subst hk
    exact ⟨1, Subring.one_mem _, expands_one.congr fun u ↦ by simp⟩
  | insert a s ha ih =>
    intro k hk
    rw [Finset.card_insert_of_notMem ha] at hk ⊢
    obtain ⟨Ba, hBa, hEa⟩ := hv a (Finset.mem_insert_self _ _)
    have ih' := ih fun i hi ↦ hv i (Finset.mem_insert_of_mem hi)
    have hdeg : ∀ u, (∏ i ∈ s, (X - C (v i u))).natDegree = s.card := fun u ↦
      natDegree_finsetProd_X_sub_C_eq_card _ _
    simp_rw [Finset.prod_insert ha]
    rcases k with _ | k
    · obtain ⟨B0, hB0, hE0⟩ := ih' 0 (Nat.zero_le _)
      refine ⟨-(Ba * B0), Subring.neg_mem _ (Subring.mul_mem _ hBa hB0), (hEa.mul hE0).neg.congr
        fun u ↦ ?_⟩
      simp only [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, Nat.sub_zero]
      rw [mul_add, mul_one, pow_add]
      ring
    · have hcoeff : ∀ u, ((X - C (v a u)) * ∏ i ∈ s, (X - C (v i u))).coeff (k + 1) =
          (∏ i ∈ s, (X - C (v i u))).coeff k - v a u * (∏ i ∈ s, (X - C (v i u))).coeff (k + 1) := by
        intro u
        rw [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul]
      obtain ⟨B1, hB1, hE1⟩ := ih' k (by omega)
      have e1 : s.card + 1 - (k + 1) = s.card - k := by omega
      by_cases hks : k + 1 ≤ s.card
      · obtain ⟨B2, hB2, hE2⟩ := ih' (k + 1) hks
        refine ⟨B1 - Ba * B2, Subring.sub_mem _ hB1 (Subring.mul_mem _ hBa hB2),
          (hE1.sub (hEa.mul hE2)).congr fun u ↦ ?_⟩
        have e2 : M * (s.card - k) = M + M * (s.card - (k + 1)) := by
          have : s.card - k = 1 + (s.card - (k + 1)) := by omega
          rw [this, mul_add, mul_one]
        rw [hcoeff, e1, e2, pow_add]
        ring
      · refine ⟨B1, hB1, hE1.congr fun u ↦ ?_⟩
        have hz : (∏ i ∈ s, (X - C (v i u))).coeff (k + 1) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by rw [hdeg u]; omega)
        rw [hcoeff, hz, e1]
        ring

end ModularFormsKB.Milne.LevelTwo
