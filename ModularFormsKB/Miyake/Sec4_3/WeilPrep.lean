import ModularFormsKB.Miyake.Sec4_3.Twist
import ModularFormsKB.Miyake.Sec4_3.Growth

/-!
# Preparations for the proof of Weil's converse theorem

Ingredients of the proof of Miyake Theorem 4.3.15 (pp. 128–129):

* `Miyake.fricke_fricke`: $(f|_k\omega_N)|_k\omega_N = (-1)^k f$.
* `Miyake.qSeries_sub_bound_of_lSeriesSummable`: if $L(s;f)$ converges absolutely at $s = \sigma > 0$
  then $f(z) - a_0 = O(y^{-\sigma})$ on $\mathbb H$ (Miyake's estimate at the end of the proof,
  obtained here by bounding $n^\sigma e^{-2\pi n y} \le (\sigma/(2\pi e y))^\sigma$ termwise).
* `Miyake.slash_of_lower_left_eq_zero`: slash by $\pm T^b$ of a function of period $1$.
* `Miyake.exists_weil_factorization`: Miyake's factorization
  $\gamma = \alpha(t_1)\begin{pmatrix} m & v\\ uN & n\end{pmatrix}\alpha(t_2)$ with $m, n \in \mathcal M$.
-/

open Complex Filter Asymptotics CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm

noncomputable section

namespace Miyake

/-- The Fricke transform is an involution up to sign: $(f|_k\omega_N)|_k\omega_N = (-1)^k f$ on
$\mathbb H$ (Miyake, before Lemma 4.3.2). -/
lemma fricke_fricke (k : ℤ) {N : ℝ} (hN : 0 < N) (f : ℂ → ℂ) {z : ℂ} (hz : 0 < z.im) :
    fricke k N (fricke k N f) z = (-1) ^ k * f z := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hs : ((√N : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hN).ne'
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsq : ((√N : ℝ) : ℂ) * ((√N : ℝ) : ℂ) = N := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hN.le]
  have e1 : -1 / ((N : ℂ) * (-1 / (N * z))) = z := by field_simp
  have e2 : ((√N : ℝ) : ℂ) * z * (((√N : ℝ) : ℂ) * (-1 / (N * z))) = -1 := by
    rw [show ((√N : ℝ) : ℂ) * z * (((√N : ℝ) : ℂ) * (-1 / (N * z))) =
      (((√N : ℝ) : ℂ) * ((√N : ℝ) : ℂ)) * z * (-1 / (N * z)) by ring, hsq]
    field_simp
  unfold fricke
  rw [e1, ← mul_assoc, ← mul_zpow, e2]
  rcases Int.even_or_odd k with h | h
  · rw [h.neg.neg_one_zpow, h.neg_one_zpow]
  · rw [h.neg.neg_one_zpow, h.neg_one_zpow]

private lemma rpow_mul_exp_le' {c x ν : ℝ} (hc : 0 < c) (hx : 0 ≤ x) (hν : 0 < ν) :
    x ^ ν * Real.exp (-c * x) ≤ (ν / c) ^ ν * Real.exp (-ν) := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = c * x / ν := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have h1 : u ≤ Real.exp (u - 1) := by linarith [Real.add_one_le_exp (u - 1)]
  have h2 : u ^ ν ≤ Real.exp (u - 1) ^ ν := Real.rpow_le_rpow hu0 h1 hν.le
  have h3 : Real.exp (u - 1) ^ ν = Real.exp (c * x) * Real.exp (-ν) := by
    rw [← Real.exp_mul, ← Real.exp_add]; congr 1; rw [hu]; field_simp; ring
  have h4 : x = (ν / c) * u := by rw [hu]; field_simp
  have h5 : x ^ ν = (ν / c) ^ ν * u ^ ν := by
    conv_lhs => rw [h4]
    exact Real.mul_rpow (by positivity) hu0
  have h6 : Real.exp (c * x) * Real.exp (-c * x) = 1 := by rw [← Real.exp_add]; simp
  calc x ^ ν * Real.exp (-c * x) = (ν / c) ^ ν * u ^ ν * Real.exp (-c * x) := by rw [h5]
    _ ≤ (ν / c) ^ ν * (Real.exp (c * x) * Real.exp (-ν)) * Real.exp (-c * x) := by
        rw [← h3]; gcongr
    _ = (ν / c) ^ ν * Real.exp (-ν) * (Real.exp (c * x) * Real.exp (-c * x)) := by ring
    _ = _ := by rw [h6, mul_one]

private lemma norm_term' (a : ℕ → ℂ) (z : ℂ) (n : ℕ) :
    ‖a n * cexp (2 * π * I * n * z)‖ = ‖a n‖ * Real.exp (-(2 * π * z.im) * n) := by
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- If $\sum_n |a_n| n^{-\sigma} < \infty$ with $\sigma > 0$, then
$|f(z) - a_0| \le C\, y^{-\sigma}$ on $\mathbb H$, $y = \operatorname{Im} z$. -/
lemma qSeries_sub_bound_of_lSeriesSummable {a : ℕ → ℂ} {σ : ℝ} (hσ : 0 < σ)
    (hL : LSeriesSummable a σ) :
    ∃ C : ℝ, ∀ z : ℂ, 0 < z.im → ‖qSeries a z - a 0‖ ≤ C * z.im ^ (-σ) := by
  have hsum : Summable fun n : ℕ ↦ ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ := by
    have h := (summable_nat_add_iff 1).2 (summable_norm_iff.2 hL)
    refine h.congr (fun n => ?_)
    rw [LSeries.norm_term_eq]
    simp
  refine ⟨(∑' n : ℕ, ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ) * ((σ / (2 * π)) ^ σ * Real.exp (-σ)),
    fun z hz => ?_⟩
  have hy := hz
  have key : ∀ n : ℕ, ‖a (n + 1) * cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * z)‖ ≤
      ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ * ((σ / (2 * π)) ^ σ * Real.exp (-σ)) * z.im ^ (-σ) := by
    intro n
    rw [norm_term']
    have hn : (0 : ℝ) < ((n : ℝ) + 1) ^ σ := by positivity
    have hn' := hn.ne'
    have hk := rpow_mul_exp_le' (c := 2 * π * z.im) (x := (n : ℝ) + 1) (by positivity)
      (by positivity) hσ
    have hdiv : (σ / (2 * π * z.im)) ^ σ = (σ / (2 * π)) ^ σ * z.im ^ (-σ) := by
      rw [show σ / (2 * π * z.im) = (σ / (2 * π)) / z.im by field_simp,
        Real.div_rpow (by positivity) hy.le, Real.rpow_neg hy.le, div_eq_mul_inv]
    push_cast
    have e : ‖a (n + 1)‖ * Real.exp (-(2 * π * z.im) * ((n : ℝ) + 1)) =
        ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ *
          (((n : ℝ) + 1) ^ σ * Real.exp (-(2 * π * z.im) * ((n : ℝ) + 1))) := by
      field_simp
    rw [e]
    calc _ ≤ ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ *
          ((σ / (2 * π * z.im)) ^ σ * Real.exp (-σ)) :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := by rw [hdiv]; ring
  have hb := (hsum.mul_right (((σ / (2 * π)) ^ σ * Real.exp (-σ)))).mul_right (z.im ^ (-σ))
  have hs1 : Summable fun n : ℕ ↦ a (n + 1) * cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * z) :=
    Summable.of_norm_bounded hb key
  have hs : Summable fun n : ℕ ↦ a n * cexp (2 * π * I * n * z) :=
    (summable_nat_add_iff 1).1 hs1
  have e0 : qSeries a z - a 0 =
      ∑' n : ℕ, a (n + 1) * cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * z) := by
    unfold qSeries
    rw [hs.tsum_eq_zero_add]
    simp
  rw [e0]
  have := tsum_of_norm_bounded hb.hasSum key
  rw [tsum_mul_right, tsum_mul_right] at this
  exact this

/-- Slash by an element $\pm T^b$ of $\mathrm{SL}_2(\mathbb Z)$ (lower left entry $0$) of a function of
period $1$: $G|_k\gamma = d^k G$ with $d = \pm 1$ the lower right entry. -/
lemma slash_of_lower_left_eq_zero {k : ℤ} {G : ℍ → ℂ}
    (hG : ∀ τ : ℍ, G ((1 : ℝ) +ᵥ τ) = G τ) (γ : SL(2, ℤ)) (hγ : γ 1 0 = 0) :
    G ∣[k] γ = (((γ 1 1 : ℤ) : ℂ) ^ k) • G := by
  have hdet : γ 0 0 * γ 1 1 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two, hγ] at this; simpa using this
  have hd : γ 1 1 = 1 ∨ γ 1 1 = -1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h2
    · exact Or.inr h2
  have ha : γ 0 0 = γ 1 1 := by rcases hd with h | h <;> rw [h] at hdet ⊢ <;> linarith
  funext τ
  rw [ModularForm.SL_slash_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hperN : ∀ (n : ℕ) (τ : ℍ), G ((n : ℝ) +ᵥ τ) = G τ := by
    intro n
    induction n with
    | zero => intro τ; simp
    | succ n ih =>
      intro τ
      have : ((n + 1 : ℕ) : ℝ) +ᵥ τ = (1 : ℝ) +ᵥ ((n : ℝ) +ᵥ τ) := by
        rw [vadd_vadd]; congr 1; push_cast; ring
      rw [this, hG, ih]
  have hper : ∀ n : ℤ, G ((n : ℝ) +ᵥ τ) = G τ := by
    intro n
    rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
    · simpa using hperN m τ
    · have := hperN m (((-(m : ℤ) : ℤ) : ℝ) +ᵥ τ)
      rw [vadd_vadd] at this
      simp only [Int.cast_neg, Int.cast_natCast, add_neg_cancel, zero_vadd] at this
      rw [Int.cast_neg, Int.cast_natCast, ← this]
  have hden : ((γ 1 0 : ℤ) : ℂ) * τ + (γ 1 1 : ℤ) = γ 1 1 := by simp [hγ]
  have hsm : γ • τ = ((γ 0 1 * γ 1 1 : ℤ) : ℝ) +ᵥ τ := by
    ext
    rw [UpperHalfPlane.specialLinearGroup_apply]
    rw [UpperHalfPlane.coe_vadd]
    simp only [hγ, ha]
    rcases hd with h | h <;> simp [h] <;> ring
  have hdn : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (τ : ℂ) = ((γ 1 1 : ℤ) : ℂ) := by
    simp [denom, hγ]
  rw [hsm, hper, hdn]
  rcases hd with h | h <;> rw [h]
  · simp
  · rw [zpow_neg]
    rcases Int.even_or_odd k with h | h
    · simp [h.neg_one_zpow]
    · simp [h.neg_one_zpow]

/-- The matrix $\begin{pmatrix} m & v\\ uN & n\end{pmatrix} \in \Gamma_0(N)$ of Miyake Lemma 4.3.14,
for integers with $mn - uvN = 1$. -/
def gammaW (N m n u v : ℤ) (h : m * n - u * v * N = 1) : SL(2, ℤ) :=
  ⟨!![m, v; u * N, n], by simp [Matrix.det_fin_two]; linear_combination h⟩

/-- Any integer `x` coprime to `c ≠ 0` is congruent modulo `c` to an element of a Weil set. -/
lemma exists_weil_rep {N : ℕ} {M : Set ℕ} (hM : IsWeilSet N M) (x c : ℤ) (hx : IsCoprime x c)
    (hc : c ≠ 0) : ∃ m ∈ M, ∃ t : ℤ, (m : ℤ) = x + t * c := by
  have hK : 0 < c.natAbs := Int.natAbs_pos.2 hc
  obtain ⟨w, hw⟩ : ∃ w : ℤ, (c.natAbs : ℤ) = c * w := by
    rcases le_or_gt 0 c with h | h
    · exact ⟨1, by simp [Int.natAbs_of_nonneg h]⟩
    · exact ⟨-1, by simp [Int.ofNat_natAbs_of_nonpos h.le]⟩
  set K := c.natAbs with hKdef
  set c₀ : ℕ := (x % K).toNat + K with hc₀
  have hc₀z : (c₀ : ℤ) = x + c * ((1 - x / K) * w) := by
    have h0 : 0 ≤ x % (K : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hK.ne')
    simp only [hc₀]; push_cast
    rw [Int.toNat_of_nonneg h0]
    have := Int.emod_add_mul_ediv x K
    have e : c * ((1 - x / K) * w) = (1 - x / K) * K := by rw [hw]; ring
    rw [e]
    linarith
  have hpos : 0 < c₀ := by simp only [hc₀]; omega
  have hcop : Nat.Coprime c₀ K := by
    have h1 : IsCoprime (c₀ : ℤ) c := by
      rw [hc₀z]; exact hx.add_mul_left_left _
    have h2 := Int.isCoprime_iff_gcd_eq_one.1 h1
    simpa [Int.gcd, Nat.Coprime] using h2
  obtain ⟨m, hm, t, ht⟩ := hM.2.2 c₀ K hpos hK hcop
  refine ⟨m, hm, (1 - x / K) * w + t * w, ?_⟩
  rw [ht, hc₀z, hw]; ring

/-- **Miyake's factorization** (proof of Theorem 4.3.15): if $\mathcal M$ satisfies the conditions
of `Miyake.IsWeilSet` and $\gamma = \begin{pmatrix} a & b\\ cN & d\end{pmatrix} \in \Gamma_0(N)$ has
$c \ne 0$, then $\gamma = T^{t_1}\begin{pmatrix} m & v\\ uN & n\end{pmatrix}T^{t_2}$ with $m, n \in \mathcal M$,
$mn - uvN = 1$ and $m \equiv a \pmod N$. -/
lemma exists_weil_factorization {N : ℕ} {M : Set ℕ} (hM : IsWeilSet N M)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) (hc : γ 1 0 ≠ 0) :
    ∃ m ∈ M, ∃ n ∈ M, ∃ (u v t₁ t₂ : ℤ) (h : (m : ℤ) * n - u * v * N = 1),
      ((m : ℤ) : ZMod N) = (γ 0 0 : ZMod N) ∧
      γ = ModularGroup.T ^ t₁ * gammaW N m n u v h * ModularGroup.T ^ t₂ := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at this
  obtain ⟨u, hu⟩ : (N : ℤ) ∣ γ 1 0 := by
    have := (Gamma0_mem).1 hγ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this |>.imp fun u hu => by rw [hu]
  have hcop1 : IsCoprime (γ 0 0) (γ 1 0) := ⟨γ 1 1, -γ 0 1, by linear_combination hdet⟩
  have hcop2 : IsCoprime (γ 1 1) (γ 1 0) := ⟨γ 0 0, -γ 0 1, by linear_combination hdet⟩
  obtain ⟨m, hm, t, ht⟩ := exists_weil_rep hM _ _ hcop1 hc
  obtain ⟨n, hn, s, hs⟩ := exists_weil_rep hM _ _ hcop2 hc
  have hdm : (m : ℤ) * n - u * (γ 0 1 + s * γ 0 0 + t * n) * N = 1 := by
    have hu' : u * (N : ℤ) = γ 1 0 := by rw [hu]; ring
    rw [ht, hs]
    linear_combination hdet - (γ 0 1 + s * γ 0 0 + t * (γ 1 1 + s * γ 1 0)) * hu'
  refine ⟨m, hm, n, hn, u, γ 0 1 + s * γ 0 0 + t * n, -t, -s, hdm, ?_, ?_⟩
  · rw [ht]
    have : ((t * γ 1 0 : ℤ) : ZMod N) = 0 := by
      rw [hu]; push_cast; simp
    push_cast at this ⊢
    rw [this, add_zero]
  · have hu' : u * (N : ℤ) = γ 1 0 := by rw [hu]; ring
    refine Matrix.SpecialLinearGroup.ext _ _ (fun i j => ?_)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ModularGroup.coe_T_zpow, ModularGroup.coe_T_zpow]
    fin_cases i <;> fin_cases j <;>
      simp [gammaW, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination -ht + t * hu'
    · linear_combination s * ht - s * t * hu'
    · linear_combination -hu'
    · linear_combination -hs + s * hu'

end Miyake
