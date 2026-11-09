import ModularFormsKB.Miyake.Sec4_3.Weil

/-!
# Miyake Theorem 4.3.15: Weil's converse theorem

* `Miyake.weil`, `Miyake.weil_cusp`.
-/

open Complex Filter Asymptotics CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold

noncomputable section

namespace Miyake

lemma IsOddPrimeOrFour.one_lt {m : ℕ} (hm : IsOddPrimeOrFour m) : 1 < m := by
  rcases hm with ⟨hp, -⟩ | rfl
  · exact hp.one_lt
  · norm_num

lemma IsModularFormChar.smul {k : ℤ} {N : ℕ} {χ : DirichletCharacter ℂ N} {f : ℍ → ℂ}
    (hf : IsModularFormChar k N χ f) (c : ℂ) : IsModularFormChar k N χ (c • f) := by
  obtain ⟨⟨F, hF⟩, hs⟩ := hf
  refine ⟨⟨c • F, by rw [← hF]; rfl⟩, fun γ hγ ↦ ?_⟩
  rw [ModularForm.SL_smul_slash, hs γ hγ, smul_comm]

lemma IsCuspFormChar.smul {k : ℤ} {N : ℕ} {χ : DirichletCharacter ℂ N} {f : ℍ → ℂ}
    (hf : IsCuspFormChar k N χ f) (c : ℂ) : IsCuspFormChar k N χ (c • f) := by
  obtain ⟨⟨F, hF⟩, hs⟩ := hf
  refine ⟨⟨c • F, by rw [← hF]; rfl⟩, fun γ hγ ↦ ?_⟩
  rw [ModularForm.SL_smul_slash, hs γ hγ, smul_comm]

/-- A $\chi$-eigenfunction under $\Gamma_0(N)$ is invariant under $\Gamma_1(N)$. -/
lemma slash_gamma1_of_char {k : ℤ} {N : ℕ} {χ : DirichletCharacter ℂ N} {f : ℍ → ℂ}
    (hs : ∀ γ ∈ Gamma0 N, f ∣[k] γ = χ (γ 1 1 : ZMod N) • f) :
    ∀ γ ∈ Gamma1 N, f ∣[k] γ = f := by
  intro γ hγ
  have h1 := (Gamma1_mem N γ).1 hγ
  rw [hs γ (by rw [Gamma0_mem]; exact h1.2.2), h1.2.1, map_one, one_smul]

/-- Theorem 2.1.4 for $M_k(N,\chi)$: a holomorphic $\chi$-eigenfunction under $\Gamma_0(N)$ with
polynomial growth as $\operatorname{Im} z \to 0$ lies in $M_k(N, \chi)$. -/
lemma isModularFormChar_of_growth {k : ℤ} {N : ℕ} (hN : 0 < N) {χ : DirichletCharacter ℂ N}
    {f : ℍ → ℂ} (hf : MDiff f) (hs : ∀ γ ∈ Gamma0 N, f ∣[k] γ = χ (γ 1 1 : ZMod N) • f)
    {ν C : ℝ} (hbound : ∀ τ : ℍ, τ.im ≤ 1 → ‖f τ‖ ≤ C * τ.im ^ (-ν)) :
    IsModularFormChar k N χ f :=
  ⟨isModularForm_of_growth hN hf (slash_gamma1_of_char hs) hbound, hs⟩

lemma qSeries_growth_small {b : ℕ → ℂ} (hb : CoeffGrowth b) :
    ∃ ν C : ℝ, ∀ τ : ℍ, τ.im ≤ 1 → ‖qSeries b τ‖ ≤ C * τ.im ^ (-ν) := by
  obtain ⟨C, μ, -, h⟩ := qSeries_bound_small hb
  exact ⟨μ, C, fun τ hτ ↦ h τ τ.im_pos hτ⟩

/-- Lemma 4.3.9 turns the conditions $(B_\psi)$ for one modulus into the relations $(A_\psi)$. -/
lemma twistedFrickeRelations_of_weil {k N : ℕ} (hk : 0 < k) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) {a b : ℕ → ℂ} (ha : CoeffGrowth a) (hb : CoeffGrowth b)
    {m : ℕ} [NeZero m] (hm : IsOddPrimeOrFour m)
    (h2 : ∀ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive →
      TwistedHeckeCondition k N ψ (weilConstant χ ψ) a b) :
    TwistedFrickeRelations k N m χ a b := fun ψ hψ ↦
  (twisted_hecke hk hN hm.one_lt ψ hψ ha hb _).2 (h2 ψ hψ)

/-- The core of the proof of Theorem 4.3.15: $g|_k\gamma = \bar\chi(d)\,g$ for every
$\gamma \in \Gamma_0(N)$. -/
lemma weil_slash_gamma0 {k N : ℕ} (hk : 0 < k) (hN : 0 < N) (χ : DirichletCharacter ℂ N)
    (hχ : χ (-1) = (-1) ^ k) {a b : ℕ → ℂ} (ha : CoeffGrowth a) (hb : CoeffGrowth b)
    (hA : ∀ z : ℂ, 0 < z.im → qSeries b z = fricke k N (qSeries a) z)
    {M : Set ℕ} (hM : IsWeilSet N M)
    (hTw : ∀ m ∈ M, ∀ [NeZero m], TwistedFrickeRelations k N m χ a b) :
    ∀ γ ∈ Gamma0 N, (fun τ : ℍ ↦ qSeries b τ) ∣[(k : ℤ)] γ =
      χ⁻¹ (γ 1 1 : ZMod N) • fun τ : ℍ ↦ qSeries b τ := by
  intro γ hγ
  set G : ℍ → ℂ := fun τ ↦ qSeries b τ with hGdef
  have hper : ∀ τ : ℍ, G ((1 : ℝ) +ᵥ τ) = G τ := fun τ ↦ by
    simp only [hGdef, UpperHalfPlane.coe_vadd, Complex.ofReal_one]
    rw [add_comm]; exact qSeries_add_one _
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  by_cases hc : γ 1 0 = 0
  · rw [slash_of_lower_left_eq_zero hper γ hc]
    rw [hc, mul_zero, sub_zero] at hdet
    congr 1
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨-, h1⟩ | ⟨-, h1⟩
    · rw [h1]; simp
    · rw [h1, MulChar.inv_apply_eq_inv']
      push_cast
      rw [hχ, zpow_natCast, ← inv_pow, inv_neg, inv_one]
  · obtain ⟨m, hmM, n, hnM, u, v, t₁, t₂, h, hma, hfac⟩ := exists_weil_factorization hM γ hγ hc
    have hm := hM.1 m hmM
    have hn := hM.1 n hnM
    have : NeZero m := ⟨by have := hm.one_lt; omega⟩
    have : NeZero n := ⟨by have := hn.one_lt; omega⟩
    have h14 := weil_lemma_4_3_14 hk hN χ hχ ha hb hA hm hn (hM.2.1 m hmM) (hM.2.1 n hnM)
      (hTw m hmM) (hTw n hnM) u v h
    have hT : ∀ t : ℤ, G ∣[(k : ℤ)] (ModularGroup.T ^ t) = G := fun t ↦ by
      rw [slash_of_lower_left_eq_zero hper _ (by simp [ModularGroup.coe_T_zpow])]
      simp [ModularGroup.coe_T_zpow]
    conv_lhs => rw [hfac]
    rw [SlashAction.slash_mul, SlashAction.slash_mul, hT, ModularForm.SL_slash (γ := gammaW _ _ _ _ _ h)]
    erw [h14]
    rw [ModularForm.SL_smul_slash, hT]
    congr 1
    -- `χ(m) = χ(a) = χ(d)⁻¹`
    have h0 : ((γ 1 0 : ℤ) : ZMod N) = 0 := hγ
    have had : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
      have := congrArg (fun r : ℤ ↦ (r : ZMod N)) hdet
      push_cast at this
      rw [h0, mul_zero, sub_zero] at this
      exact this
    rw [MulChar.inv_apply_eq_inv', show ((m : ℕ) : ZMod N) = ((γ 0 0 : ℤ) : ZMod N) by
      rw [← hma, Int.cast_natCast]]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, had, map_one]

/-- **Weil's converse theorem** (Miyake Theorem 4.3.15). Let $k, N$ be positive integers, $\chi$ a
Dirichlet character modulo $N$ with $\chi(-1) = (-1)^k$, $a_n, b_n = O(n^\nu)$, and
$f = \sum a_n e^{2\pi i n z}$, $g = \sum b_n e^{2\pi i n z}$. Let $\mathcal M$ be as in
`Miyake.IsWeilSet`. Suppose
1. $\Lambda_N(s;f)$, $\Lambda_N(s;g)$ satisfy condition (B) of Theorem 4.3.6;
2. for every primitive $\psi$ whose conductor $m_\psi$ lies in $\mathcal M$,
   $\Lambda_N(s;f,\psi)$, $\Lambda_N(s;g,\bar\psi)$ satisfy $(B_\psi)$ of Lemma 4.3.9 with
   $C_\psi = \chi(m_\psi)\psi(-N)W(\psi)/W(\bar\psi)$.

Then $f \in M_k(N,\chi)$, $g \in M_k(N,\bar\chi)$ and $g = f|_k\omega_N$. Relation: same. -/
@[kb "miyake1989" "§4.3, Theorem 4.3.15 (Weil), p. 128"]
theorem weil {k N : ℕ} (hk : 0 < k) (hN : 0 < N) (χ : DirichletCharacter ℂ N)
    (hχ : χ (-1) = (-1) ^ k) {a b : ℕ → ℂ} (ha : CoeffGrowth a) (hb : CoeffGrowth b)
    {M : Set ℕ} (hM : IsWeilSet N M) (h1 : HeckeCondition k N (I ^ k) a b)
    (h2 : ∀ (m : ℕ) [NeZero m], m ∈ M → ∀ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive →
      TwistedHeckeCondition k N ψ (weilConstant χ ψ) a b) :
    IsModularFormChar k N χ (fun τ : ℍ ↦ qSeries a τ) ∧
      IsModularFormChar k N χ⁻¹ (fun τ : ℍ ↦ qSeries b τ) ∧
      ∀ z : ℂ, 0 < z.im → qSeries b z = fricke k N (qSeries a) z := by
  -- (1) and Theorem 4.3.6 give `g = f|ω_N`; (2) and Lemma 4.3.9 give the relations `(A_ψ)`
  have hA : ∀ z : ℂ, 0 < z.im → qSeries b z = fricke k N (qSeries a) z :=
    (hecke_fricke hk hN ha hb).2 h1
  have hTw : ∀ m ∈ M, ∀ [NeZero m], TwistedFrickeRelations k N m χ a b :=
    fun m hmM _ ↦ twistedFrickeRelations_of_weil hk hN χ ha hb (hM.1 m hmM) (h2 m hmM)
  -- `g ∈ M_k(N, χ̄)` by Lemma 4.3.14, Lemma 4.3.3 and Theorem 2.1.4
  obtain ⟨ν, C, hbd⟩ := qSeries_growth_small hb
  have hg : IsModularFormChar k N χ⁻¹ (fun τ : ℍ ↦ qSeries b τ) :=
    isModularFormChar_of_growth hN (mdifferentiable_qSeries hb)
      (weil_slash_gamma0 hk hN χ hχ ha hb hA hM hTw) hbd
  -- `f = (-1)^k g|ω_N ∈ M_k(N, χ)` by Lemma 4.3.2(2)
  have hfg := fricke_isModularFormChar hN χ⁻¹ (f := qSeries b) hg
  rw [inv_inv] at hfg
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : (fun τ : ℍ ↦ qSeries a τ) =
      ((-1 : ℂ) ^ (k : ℤ)) • fun τ : ℍ ↦ fricke k N (qSeries b) τ := by
    funext τ
    have e : fricke k N (qSeries b) τ = fricke k N (fricke k N (qSeries a)) τ := by
      unfold fricke
      rw [hA _ (im_neg_one_div_pos hN' τ.im_pos)]; rfl
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [e, fricke_fricke _ hN' _ τ.im_pos, ← mul_assoc, ← mul_zpow]
    norm_num
  exact ⟨heq ▸ hfg.smul _, hg, hA⟩

/-- **Weil's converse theorem, cusp forms** (Miyake Theorem 4.3.15, last sentence): under the
hypotheses of `Miyake.weil`, if moreover $L(s; f)$ converges absolutely at $s = k - \delta$ for
some $\delta > 0$, then $f$ and $g$ are cusp forms. Relation: same. -/
@[kb "miyake1989" "§4.3, Theorem 4.3.15 (Weil), p. 128"]
theorem weil_cusp {k N : ℕ} (hk : 0 < k) (hN : 0 < N) (χ : DirichletCharacter ℂ N)
    (hχ : χ (-1) = (-1) ^ k) {a b : ℕ → ℂ} (ha : CoeffGrowth a) (hb : CoeffGrowth b)
    {M : Set ℕ} (hM : IsWeilSet N M) (h1 : HeckeCondition k N (I ^ k) a b)
    (h2 : ∀ (m : ℕ) [NeZero m], m ∈ M → ∀ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive →
      TwistedHeckeCondition k N ψ (weilConstant χ ψ) a b)
    {δ : ℝ} (hδ : 0 < δ) (hL : LSeriesSummable a (k - δ)) :
    IsCuspFormChar k N χ (fun τ : ℍ ↦ qSeries a τ) ∧
      IsCuspFormChar k N χ⁻¹ (fun τ : ℍ ↦ qSeries b τ) := by
  obtain ⟨⟨-, hs⟩, -, hA⟩ := weil hk hN χ hχ ha hb hM h1 h2
  -- `f(z) = O(y^{-σ})` with `σ = k - min(δ, k/2) < k`
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set σ : ℝ := k - min δ (k / 2) with hσ
  have hσ0 : 0 < σ := by have := min_le_right δ ((k : ℝ) / 2); linarith
  have hσk : σ < k := by have := lt_min hδ (half_pos hk'); linarith
  have hL' : LSeriesSummable a (σ : ℂ) :=
    hL.of_re_le_re (by simp only [hσ]; push_cast; simp; linarith [min_le_left δ ((k : ℝ) / 2)])
  obtain ⟨C, hC⟩ := qSeries_sub_bound_of_lSeriesSummable hσ0 hL'
  have hbd : ∀ τ : ℍ, τ.im ≤ 1 → ‖qSeries a τ‖ ≤ (‖a 0‖ + |C|) * τ.im ^ (-σ) := by
    intro τ hτ
    have hy1 : 1 ≤ τ.im ^ (-σ) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos τ.im_pos hτ (by linarith)
    have h2 := hC τ τ.im_pos
    calc ‖qSeries a τ‖ ≤ ‖a 0‖ + ‖qSeries a τ - a 0‖ := by
          simpa using norm_add_le (a 0) (qSeries a τ - a 0)
      _ ≤ ‖a 0‖ * τ.im ^ (-σ) + |C| * τ.im ^ (-σ) := by
          gcongr
          · nlinarith [norm_nonneg (a 0)]
          · exact h2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg τ.im_pos.le _))
      _ = _ := by ring
  have hcf : IsCuspFormChar k N χ (fun τ : ℍ ↦ qSeries a τ) :=
    ⟨isCuspForm_of_growth hN (mdifferentiable_qSeries ha) (slash_gamma1_of_char hs)
      (by exact_mod_cast hσk) hbd, hs⟩
  refine ⟨hcf, ?_⟩
  -- `g = f|ω_N ∈ S_k(N, χ̄)` by Lemma 4.3.2(2)
  have := fricke_isCuspFormChar hN χ (f := qSeries a) hcf
  convert this using 1
  funext τ
  exact hA τ τ.im_pos
end Miyake
