/-
# The coset sum `heckeFun` is holomorphic and preserves the cusp conditions

No multiplier is involved. For an integral upper triangular
$\beta = \begin{pmatrix}A & B\\ 0 & D\end{pmatrix}$ ($A, D > 0$) and $\gamma \in \mathrm{SL}_2(\mathbb Z)$, write
$\beta\gamma = \eta\beta'$ with $\eta \in \mathrm{SL}_2(\mathbb Z)$ and $\beta' = \begin{pmatrix}A' & B'\\ 0 & D'\end{pmatrix}$ upper
triangular, $A', D' > 0$ (first column of $\beta\gamma$ divided by its gcd, completed by Bézout). Then
$c_\eta\,\beta'\tau + d_\eta = (D/D')(c\tau + d)$, so
$$|c\tau+d|^{-(k+1/2)}\,|f(\beta\gamma\tau)| = (D/D')^{k+1/2}\;\texttt{cuspNorm}\ k\ f\ \eta\ (\beta'\tau),$$
and $\operatorname{Im}\beta'\tau = (A'/D')\operatorname{Im}\tau \to \infty$. Hence boundedness (vanishing) of $f$ at every cusp
passes to $\tau \mapsto f(\beta\tau)$ (`cuspNorm_affPt_bdd`, `cuspNorm_affPt_zero`), and to the finite linear combination
`heckeFun` (`heckeFun_bdd`, `heckeFun_zero`).
-/
import ModularFormsKB.HalfIntegral.HeckeOp

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups
open scoped Real Manifold

local notation "ℍ" => UpperHalfPlane

variable (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (p : ℕ+)

/-! ### Holomorphy -/

lemma affPt_eq_smul (A D : ℕ+) (B : ℤ) :
    ∃ g : GL (Fin 2) ℝ, 0 < g.det.val ∧ ∀ τ : ℍ, affPt A D B τ = g • τ := by
  have hdet : (!![(A : ℝ), (B : ℝ); 0, (D : ℝ)]).det ≠ 0 := by
    simp [Matrix.det_fin_two]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_, fun τ ↦ ?_⟩
  · simp [Matrix.det_fin_two]
  · ext
    rw [UpperHalfPlane.coe_smul_of_det_pos (by simp [Matrix.det_fin_two])]
    simp [UpperHalfPlane.num, UpperHalfPlane.denom]

lemma mdiff_affPt (A D : ℕ+) (B : ℤ) : MDiff (affPt A D B) := by
  obtain ⟨g, hg, h⟩ := affPt_eq_smul A D B
  have : affPt A D B = fun τ : ℍ ↦ g • τ := funext h
  rw [this]
  exact UpperHalfPlane.mdifferentiable_smul hg

lemma mdiff_comp_affPt {f : ℍ → ℂ} (hf : MDiff f) (A D : ℕ+) (B : ℤ) :
    MDiff (fun τ ↦ f (affPt A D B τ)) :=
  hf.comp (mdiff_affPt A D B)

lemma mdiff_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ) (h : ∀ i ∈ s, MDiff (F i)) :
    MDiff (fun τ ↦ ∑ i ∈ s, F i τ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (mdifferentiable_const : MDiff (fun _ : ℍ ↦ (0 : ℂ)))
  | insert a s ha ih =>
    have h1 : MDiff (F a) := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi ↦ h i (Finset.mem_insert_of_mem hi))
    have e : (fun τ ↦ ∑ i ∈ insert a s, F i τ) = F a + (fun τ ↦ ∑ i ∈ s, F i τ) := by
      funext τ; simp [Finset.sum_insert ha]
    rw [e]
    exact h1.add h2

/-! ### The cusp quantity under `affPt` -/

lemma cd_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) : (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := by
  intro h
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  have hc' : γ 1 0 = 0 := by
    rcases him with h | h
    · exact h
    · exact absurd h τ.im_pos.ne'
  rw [hc'] at hre
  simp at hre
  have hd : γ 1 1 = 0 := by exact_mod_cast hre
  rw [hc', hd] at hdet
  simp at hdet

/-- **Decomposition $\beta\gamma = \eta\beta'$** (see the module docstring), in the form used below: the Möbius
identity and the identity of bottom rows $D'(c_\eta\,\beta'\tau + d_\eta) = D(c\tau+d)$. -/
lemma affPt_decomp (A D : ℕ+) (B : ℤ) (γ : SL(2, ℤ)) :
    ∃ (η : SL(2, ℤ)) (A' D' : ℕ+) (B' : ℤ),
      (∀ τ : ℍ, affPt A D B (γ • τ) = η • affPt A' D' B' τ) ∧
      ∀ τ : ℍ, (D' : ℂ) * ((η 1 0 : ℂ) * (affPt A' D' B' τ : ℂ) + η 1 1) =
        D * ((γ 1 0 : ℂ) * τ + γ 1 1) := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  set a := γ 0 0 with ha
  set b := γ 0 1 with hb
  set c := γ 1 0 with hc
  set d := γ 1 1 with hd
  have hA : (0 : ℤ) < (A : ℕ) := by exact_mod_cast A.pos
  have hD : (0 : ℤ) < (D : ℕ) := by exact_mod_cast D.pos
  set m : ℤ := (A : ℕ) * a + B * c with hm
  set n : ℤ := (D : ℕ) * c with hn
  set P : ℤ := (A : ℕ) * b + B * d with hP
  have hg : 0 < Int.gcd m n := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    rw [Int.gcd_eq_zero_iff] at h0
    obtain ⟨h1, h2⟩ := h0
    have hc0 : c = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · omega
      · exact h
    have h3 : ((A : ℕ) : ℤ) * a = 0 := by
      rw [hm, hc0] at h1; simpa using h1
    have ha0 : a = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · omega
      · exact h
    rw [hc0, ha0] at hdet
    simp at hdet
  have hbez := Int.gcd_eq_gcd_ab m n
  set x := Int.gcdA m n
  set y := Int.gcdB m n
  set g : ℤ := (Int.gcd m n : ℤ) with hgdef
  have hgpos : 0 < g := by omega
  obtain ⟨u, hu⟩ : g ∣ m := Int.gcd_dvd_left m n
  obtain ⟨v, hv⟩ : g ∣ n := Int.gcd_dvd_right m n
  have hux : u * x + v * y = 1 := by
    have : g * (u * x + v * y) = g * 1 := by
      calc g * (u * x + v * y) = (g * u) * x + (g * v) * y := by ring
        _ = m * x + n * y := by rw [← hu, ← hv]
        _ = g := hbez.symm
        _ = g * 1 := by ring
    exact mul_left_cancel₀ hgpos.ne' this
  set B' : ℤ := x * P + y * D * d with hB'
  set E : ℤ := -v * P + u * D * d with hE
  have hgE : g * E = (A : ℕ) * (D : ℕ) := by
    have : g * E = -(g * v) * P + (g * u) * D * d := by rw [hE]; ring
    rw [this, ← hu, ← hv, hm, hn, hP]
    have : (A : ℤ) * D * (a * d - b * c) = A * D := by rw [hdet]; ring
    linear_combination this
  have hEpos : 0 < E := by
    have : 0 < g * E := by rw [hgE]; positivity
    exact pos_of_mul_pos_right this hgpos.le
  let η : SL(2, ℤ) := ⟨!![u, -y; v, x], by simp [Matrix.det_fin_two]; linarith⟩
  let A' : ℕ+ := ⟨g.toNat, by omega⟩
  let D' : ℕ+ := ⟨E.toNat, by omega⟩
  have hAc : ((A' : ℕ) : ℂ) = (g : ℂ) := by
    have : ((A' : ℕ) : ℤ) = g := by simp only [A', PNat.mk_coe]; omega
    exact_mod_cast this
  have hDc : ((D' : ℕ) : ℂ) = (E : ℂ) := by
    have : ((D' : ℕ) : ℤ) = E := by simp only [D', PNat.mk_coe]; omega
    exact_mod_cast this
  have hCm : (m : ℂ) = g * u := by exact_mod_cast hu
  have hCn : (n : ℂ) = g * v := by exact_mod_cast hv
  have hCux : (u : ℂ) * x + v * y = 1 := by exact_mod_cast hux
  have hCdet : (a : ℂ) * d - b * c = 1 := by exact_mod_cast hdet
  have hEne : (E : ℂ) ≠ 0 := by exact_mod_cast hEpos.ne'
  have hgne : (g : ℂ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hDne : ((D : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hη10 : (η 1 0 : ℂ) = v := by simp [η]
  have hη11 : (η 1 1 : ℂ) = x := by simp [η]
  have hm' : (m : ℂ) = (A : ℕ) * a + B * c := by simp [hm]
  have hn' : (n : ℂ) = (D : ℕ) * c := by simp [hn]
  have hP' : (P : ℂ) = (A : ℕ) * b + B * d := by simp [hP]
  have hB'' : (B' : ℂ) = x * P + y * D * d := by simp [hB']
  have hE' : (E : ℂ) = -v * P + u * D * d := by simp [hE]
  have key2 : ∀ τ : ℍ, (D' : ℂ) * ((η 1 0 : ℂ) * (affPt A' D' B' τ : ℂ) + η 1 1) =
        D * ((γ 1 0 : ℂ) * τ + γ 1 1) := by
    intro τ
    rw [hη10, hη11, coe_affPt, hAc, hDc]
    have : (E : ℂ) * ((v : ℂ) * (((g : ℂ) * τ + B') / E) + x) = v * (g * τ + B') + x * E := by
      field_simp
    rw [this]
    linear_combination (τ : ℂ) * hn' - (τ : ℂ) * hCn + (v : ℂ) * hB'' + (x : ℂ) * hE' +
      ((D : ℕ) : ℂ) * d * hCux
  refine ⟨η, A', D', B', ?_, key2⟩
  intro τ
  have hs := cd_ne_zero γ τ
  have hη00 : (η 0 0 : ℂ) = u := by simp [η]
  have hη01 : (η 0 1 : ℂ) = -y := by simp [η]
  have hN : (u : ℂ) * (((g : ℂ) * τ + B') / E) + -y = (m * τ + P) / E := by
    field_simp
    linear_combination (-(τ : ℂ)) * hCm + (u : ℂ) * hB'' - (y : ℂ) * hE' + (P : ℂ) * hCux
  have hDn : (v : ℂ) * (((g : ℂ) * τ + B') / E) + x = D * ((c : ℂ) * τ + d) / E := by
    have := key2 τ
    rw [hη10, hη11, coe_affPt, hAc, hDc] at this
    rw [eq_div_iff hEne, mul_comm]
    exact this
  ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply η, coe_affPt, coe_affPt,
    UpperHalfPlane.coe_specialLinearGroup_apply γ]
  simp only [eq_intCast, Complex.ofReal_intCast]
  rw [← ha, ← hb, ← hc, ← hd, hη00, hη01, hη10, hη11, hAc, hDc, hN, hDn]
  rw [← hc, ← hd] at hs
  rw [hm', hP']
  have hs2 : (τ : ℂ) * c + d ≠ 0 := by rwa [mul_comm]
  have hs3 : (c : ℂ) * τ + d ≠ 0 := hs
  have hEq : ((A : ℕ) : ℂ) * ((a * τ + b) / (c * τ + d)) + B =
      (((A : ℕ) * a + B * c) * τ + ((A : ℕ) * b + B * d)) / (c * τ + d) := by
    field_simp
    ring
  rw [hEq]
  rw [div_div_div_cancel_right₀ hEne, div_div, mul_comm ((c : ℂ) * τ + d)]

private lemma cuspNorm_nonneg' (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    0 ≤ Abstract.cuspNorm k f γ τ := by
  unfold Abstract.cuspNorm; positivity

private lemma cuspNorm_comp_affPt (f : ℍ → ℂ) (A D : ℕ+) (B : ℤ) (γ : SL(2, ℤ)) :
    ∃ (η : SL(2, ℤ)) (A' D' : ℕ+) (B' : ℤ) (C : ℝ), 0 < C ∧
      ∀ τ : ℍ, Abstract.cuspNorm k (fun τ ↦ f (affPt A D B τ)) γ τ =
        C * Abstract.cuspNorm k f η (affPt A' D' B' τ) := by
  obtain ⟨η, A', D', B', hsm, hden⟩ := affPt_decomp A D B γ
  refine ⟨η, A', D', B', (((D' : ℕ) : ℝ) / ((D : ℕ) : ℝ)) ^ (-((k : ℝ) + 1 / 2)), by positivity, fun τ ↦ ?_⟩
  have hn : ((D' : ℕ) : ℝ) * ‖(η 1 0 : ℂ) * (affPt A' D' B' τ : ℂ) + η 1 1‖ =
      ((D : ℕ) : ℝ) * ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ := by
    have := congrArg norm (hden τ)
    simpa [norm_mul] using this
  have hDpos : (0 : ℝ) < ((D : ℕ) : ℝ) := by exact_mod_cast D.pos
  have hD'pos : (0 : ℝ) < ((D' : ℕ) : ℝ) := by exact_mod_cast D'.pos
  have hY : ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ =
      (((D' : ℕ) : ℝ) / ((D : ℕ) : ℝ)) * ‖(η 1 0 : ℂ) * (affPt A' D' B' τ : ℂ) + η 1 1‖ := by
    field_simp
    linarith
  unfold Abstract.cuspNorm
  show _ * ‖f (affPt A D B (γ • τ))‖ = _
  rw [hsm τ, hY, Real.mul_rpow (by positivity) (norm_nonneg _)]
  ring

private lemma bdd_of_comp {u w : ℍ → ℝ} (C : ℝ) (hC : 0 < C) (A' D' : ℕ+) (B' : ℤ)
    (hu : UpperHalfPlane.IsBoundedAtImInfty u) (hu0 : ∀ τ, 0 ≤ u τ)
    (hw : ∀ τ, w τ = C * u (affPt A' D' B' τ)) :
    UpperHalfPlane.IsBoundedAtImInfty w := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at *
  obtain ⟨M, A0, h⟩ := hu
  have hA' : (0 : ℝ) < ((A' : ℕ) : ℝ) := by exact_mod_cast A'.pos
  have hD' : (0 : ℝ) < ((D' : ℕ) : ℝ) := by exact_mod_cast D'.pos
  refine ⟨C * M, A0 * D' / A', fun z hz ↦ ?_⟩
  have him : A0 ≤ (affPt A' D' B' z).im := by
    rw [im_affPt, le_div_iff₀ hD']
    rw [div_le_iff₀ hA'] at hz
    linarith
  have := h _ him
  rw [Real.norm_of_nonneg (hu0 _)] at this
  rw [hw z, Real.norm_of_nonneg (mul_nonneg hC.le (hu0 _))]
  exact mul_le_mul_of_nonneg_left this hC.le

private lemma zero_of_comp {u w : ℍ → ℝ} (C : ℝ) (hC : 0 < C) (A' D' : ℕ+) (B' : ℤ)
    (hu : UpperHalfPlane.IsZeroAtImInfty u) (hu0 : ∀ τ, 0 ≤ u τ)
    (hw : ∀ τ, w τ = C * u (affPt A' D' B' τ)) :
    UpperHalfPlane.IsZeroAtImInfty w := by
  rw [UpperHalfPlane.isZeroAtImInfty_iff] at *
  have hA' : (0 : ℝ) < ((A' : ℕ) : ℝ) := by exact_mod_cast A'.pos
  have hD' : (0 : ℝ) < ((D' : ℕ) : ℝ) := by exact_mod_cast D'.pos
  intro ε hε
  obtain ⟨A0, h⟩ := hu (ε / C) (by positivity)
  refine ⟨A0 * D' / A', fun z hz ↦ ?_⟩
  have him : A0 ≤ (affPt A' D' B' z).im := by
    rw [im_affPt, le_div_iff₀ hD']
    rw [div_le_iff₀ hA'] at hz
    linarith
  have := h _ him
  rw [Real.norm_of_nonneg (hu0 _)] at this
  rw [hw z, Real.norm_of_nonneg (mul_nonneg hC.le (hu0 _))]
  calc C * u (affPt A' D' B' z) ≤ C * (ε / C) := mul_le_mul_of_nonneg_left this hC.le
    _ = ε := by field_simp

/-- If $f$ is bounded at every cusp, so is $\tau \mapsto f((A\tau+B)/D)$. -/
theorem cuspNorm_affPt_bdd {f : ℍ → ℂ}
    (hf : ∀ γ : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty (Abstract.cuspNorm k f γ))
    (A D : ℕ+) (B : ℤ) :
    ∀ γ : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
      (Abstract.cuspNorm k (fun τ ↦ f (affPt A D B τ)) γ) := by
  intro γ
  obtain ⟨η, A', D', B', C, hC, h⟩ := cuspNorm_comp_affPt k f A D B γ
  exact bdd_of_comp C hC A' D' B' (hf η) (cuspNorm_nonneg' k f η) h

/-- If $f$ vanishes at every cusp, so does $\tau \mapsto f((A\tau+B)/D)$. -/
theorem cuspNorm_affPt_zero {f : ℍ → ℂ}
    (hf : ∀ γ : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty (Abstract.cuspNorm k f γ))
    (A D : ℕ+) (B : ℤ) :
    ∀ γ : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty
      (Abstract.cuspNorm k (fun τ ↦ f (affPt A D B τ)) γ) := by
  intro γ
  obtain ⟨η, A', D', B', C, hC, h⟩ := cuspNorm_comp_affPt k f A D B γ
  exact zero_of_comp C hC A' D' B' (hf η) (cuspNorm_nonneg' k f η) h

/-! ### Closure of the cusp conditions under linear combinations -/

private lemma cuspNorm_add_le' (f g : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    Abstract.cuspNorm k (f + g) γ τ ≤ Abstract.cuspNorm k f γ τ + Abstract.cuspNorm k g γ τ := by
  unfold Abstract.cuspNorm
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (by simpa using norm_add_le (f (γ • τ)) (g (γ • τ))) (by positivity)

private lemma cuspNorm_smul' (c : ℂ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) :
    Abstract.cuspNorm k (c • f) γ = fun τ ↦ ‖c‖ * Abstract.cuspNorm k f γ τ := by
  funext τ
  simp only [Abstract.cuspNorm, Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

private lemma bdd_add' {u v w : ℍ → ℝ} (hu : UpperHalfPlane.IsBoundedAtImInfty u)
    (hv : UpperHalfPlane.IsBoundedAtImInfty v) (h0 : ∀ τ, 0 ≤ w τ) (h : ∀ τ, w τ ≤ u τ + v τ)
    (hu0 : ∀ τ, 0 ≤ u τ) (hv0 : ∀ τ, 0 ≤ v τ) :
    UpperHalfPlane.IsBoundedAtImInfty w := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at *
  obtain ⟨M1, A1, h1⟩ := hu
  obtain ⟨M2, A2, h2⟩ := hv
  refine ⟨M1 + M2, max A1 A2, fun z hz ↦ ?_⟩
  have a1 := h1 z (le_trans (le_max_left _ _) hz)
  have a2 := h2 z (le_trans (le_max_right _ _) hz)
  rw [Real.norm_of_nonneg (h0 z)]
  rw [Real.norm_of_nonneg (hu0 z)] at a1
  rw [Real.norm_of_nonneg (hv0 z)] at a2
  linarith [h z]

private lemma zero_add'' {u v w : ℍ → ℝ} (hu : UpperHalfPlane.IsZeroAtImInfty u)
    (hv : UpperHalfPlane.IsZeroAtImInfty v) (h0 : ∀ τ, 0 ≤ w τ) (h : ∀ τ, w τ ≤ u τ + v τ)
    (hu0 : ∀ τ, 0 ≤ u τ) (hv0 : ∀ τ, 0 ≤ v τ) :
    UpperHalfPlane.IsZeroAtImInfty w := by
  rw [UpperHalfPlane.isZeroAtImInfty_iff] at *
  intro ε hε
  obtain ⟨A1, h1⟩ := hu (ε / 2) (by positivity)
  obtain ⟨A2, h2⟩ := hv (ε / 2) (by positivity)
  refine ⟨max A1 A2, fun z hz ↦ ?_⟩
  have a1 := h1 z (le_trans (le_max_left _ _) hz)
  have a2 := h2 z (le_trans (le_max_right _ _) hz)
  rw [Real.norm_of_nonneg (h0 z)]
  rw [Real.norm_of_nonneg (hu0 z)] at a1
  rw [Real.norm_of_nonneg (hv0 z)] at a2
  linarith [h z]

private lemma bdd_smul'' (c : ℂ) {u : ℍ → ℝ} (hu : UpperHalfPlane.IsBoundedAtImInfty u)
    (hu0 : ∀ τ, 0 ≤ u τ) : UpperHalfPlane.IsBoundedAtImInfty (fun τ ↦ ‖c‖ * u τ) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at *
  obtain ⟨M1, A1, h1⟩ := hu
  refine ⟨‖c‖ * M1, A1, fun z hz ↦ ?_⟩
  have a1 := h1 z hz
  rw [Real.norm_of_nonneg (hu0 z)] at a1
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg c) (hu0 z))]
  exact mul_le_mul_of_nonneg_left a1 (norm_nonneg c)

private lemma zero_smul'' (c : ℂ) {u : ℍ → ℝ} (hu : UpperHalfPlane.IsZeroAtImInfty u) :
    UpperHalfPlane.IsZeroAtImInfty (fun τ ↦ ‖c‖ * u τ) := by
  have := Filter.Tendsto.const_mul ‖c‖ hu
  show Filter.Tendsto _ _ _
  simpa using this

private lemma bdd_smul_fun (c : ℂ) {F : ℍ → ℂ}
    (hF : ∀ γ : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty (Abstract.cuspNorm k F γ)) :
    ∀ γ : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty (Abstract.cuspNorm k (c • F) γ) := by
  intro γ
  rw [cuspNorm_smul']
  exact bdd_smul'' c (hF γ) (cuspNorm_nonneg' k F γ)

private lemma zero_smul_fun (c : ℂ) {F : ℍ → ℂ}
    (hF : ∀ γ : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty (Abstract.cuspNorm k F γ)) :
    ∀ γ : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty (Abstract.cuspNorm k (c • F) γ) := by
  intro γ
  rw [cuspNorm_smul']
  exact zero_smul'' c (hF γ)

private lemma bdd_add_fun {F G : ℍ → ℂ}
    (hF : ∀ γ : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty (Abstract.cuspNorm k F γ))
    (hG : ∀ γ : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty (Abstract.cuspNorm k G γ)) :
    ∀ γ : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty (Abstract.cuspNorm k (F + G) γ) := fun γ ↦
  bdd_add' (hF γ) (hG γ) (cuspNorm_nonneg' k _ γ) (cuspNorm_add_le' k F G γ)
    (cuspNorm_nonneg' k _ γ) (cuspNorm_nonneg' k _ γ)

private lemma zero_add_fun {F G : ℍ → ℂ}
    (hF : ∀ γ : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty (Abstract.cuspNorm k F γ))
    (hG : ∀ γ : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty (Abstract.cuspNorm k G γ)) :
    ∀ γ : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty (Abstract.cuspNorm k (F + G) γ) := fun γ ↦
  zero_add'' (hF γ) (hG γ) (cuspNorm_nonneg' k _ γ) (cuspNorm_add_le' k F G γ)
    (cuspNorm_nonneg' k _ γ) (cuspNorm_nonneg' k _ γ)

private lemma bdd_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, ∀ γ : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty (Abstract.cuspNorm k (F i) γ)) :
    ∀ γ : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
      (Abstract.cuspNorm k (fun τ ↦ ∑ i ∈ s, F i τ) γ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro γ
    have : Abstract.cuspNorm k (fun τ ↦ ∑ i ∈ (∅ : Finset ι), F i τ) γ = 0 := by
      funext τ; simp [Abstract.cuspNorm]
    rw [this]
    exact UpperHalfPlane.zero_form_isBoundedAtImInfty
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi ↦ h i (Finset.mem_insert_of_mem hi))
    have := bdd_add_fun k h1 h2
    have e : (fun τ ↦ ∑ i ∈ insert a s, F i τ) = F a + (fun τ ↦ ∑ i ∈ s, F i τ) := by
      funext τ; simp [Finset.sum_insert ha]
    rw [e]
    exact this

private lemma zero_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, ∀ γ : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty (Abstract.cuspNorm k (F i) γ)) :
    ∀ γ : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty
      (Abstract.cuspNorm k (fun τ ↦ ∑ i ∈ s, F i τ) γ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro γ
    have : Abstract.cuspNorm k (fun τ ↦ ∑ i ∈ (∅ : Finset ι), F i τ) γ = 0 := by
      funext τ; simp [Abstract.cuspNorm]
    rw [this]
    exact tendsto_const_nhds
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi ↦ h i (Finset.mem_insert_of_mem hi))
    have := zero_add_fun k h1 h2
    have e : (fun τ ↦ ∑ i ∈ insert a s, F i τ) = F a + (fun τ ↦ ∑ i ∈ s, F i τ) := by
      funext τ; simp [Finset.sum_insert ha]
    rw [e]
    exact this

/-! ### The Hecke coset sum -/

theorem heckeFun_mdiff {f : ℍ → ℂ} (hf : MDiff f) : MDiff (heckeFun k N χ p f) := by
  have h1 : MDiff (fun τ ↦ ∑ b ∈ Finset.range ((p : ℕ) ^ 2), f (affPt 1 (p ^ 2) b τ)) :=
    mdiff_finset_sum _ (fun (b : ℕ) τ ↦ f (affPt 1 (p ^ 2) b τ))
      (fun b _ ↦ mdiff_comp_affPt hf _ _ _)
  have h2 : MDiff (fun τ ↦ ∑ i ∈ Finset.range (p : ℕ),
      (jacobiSym i p : ℂ) • f (affPt p p (4 * i) τ)) :=
    mdiff_finset_sum _ (fun (i : ℕ) τ ↦ (jacobiSym i p : ℂ) • f (affPt p p (4 * i) τ))
      (fun i _ ↦ (mdiff_comp_affPt hf _ _ _).const_smul _)
  have h3 : MDiff (fun τ ↦ f (affPt (p ^ 2) 1 0 τ)) := mdiff_comp_affPt hf _ _ _
  have := (h1.add (h2.const_smul (χ (p : ℕ) * ((epsD (p : ℕ))⁻¹ * (Real.sqrt (p : ℕ) : ℂ)) ^ (2 * k + 1)))).add
    (h3.const_smul (χ (p : ℕ) ^ 2 * ((p : ℕ) : ℂ) ^ (2 * k + 1)))
  exact this.const_smul (((p : ℕ) : ℂ) ^ (-2 : ℤ))

theorem heckeFun_bdd {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty (Abstract.cuspNorm k f γ)) :
    ∀ γ : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty (Abstract.cuspNorm k (heckeFun k N χ p f) γ) := by
  have h1 := bdd_finset_sum k (Finset.range ((p : ℕ) ^ 2))
    (fun (b : ℕ) τ ↦ f (affPt 1 (p ^ 2) b τ)) (fun b _ ↦ cuspNorm_affPt_bdd k hf _ _ _)
  have h2 := bdd_finset_sum k (Finset.range (p : ℕ))
    (fun (i : ℕ) ↦ (jacobiSym i p : ℂ) • fun τ ↦ f (affPt p p (4 * i) τ))
    (fun i _ ↦ bdd_smul_fun k _ (cuspNorm_affPt_bdd k hf _ _ _))
  have h3 := cuspNorm_affPt_bdd k hf (p ^ 2) 1 0
  have := bdd_smul_fun k (((p : ℕ) : ℂ) ^ (-2 : ℤ)) (bdd_add_fun k
    (bdd_add_fun k h1 (bdd_smul_fun k (χ (p : ℕ) * ((epsD (p : ℕ))⁻¹ * (Real.sqrt (p : ℕ) : ℂ)) ^ (2 * k + 1)) h2))
    (bdd_smul_fun k (χ (p : ℕ) ^ 2 * ((p : ℕ) : ℂ) ^ (2 * k + 1)) h3))
  exact this

theorem heckeFun_zero {f : ℍ → ℂ} (hf : ∀ γ : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty (Abstract.cuspNorm k f γ)) :
    ∀ γ : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty (Abstract.cuspNorm k (heckeFun k N χ p f) γ) := by
  have h1 := zero_finset_sum k (Finset.range ((p : ℕ) ^ 2))
    (fun (b : ℕ) τ ↦ f (affPt 1 (p ^ 2) b τ)) (fun b _ ↦ cuspNorm_affPt_zero k hf _ _ _)
  have h2 := zero_finset_sum k (Finset.range (p : ℕ))
    (fun (i : ℕ) ↦ (jacobiSym i p : ℂ) • fun τ ↦ f (affPt p p (4 * i) τ))
    (fun i _ ↦ zero_smul_fun k _ (cuspNorm_affPt_zero k hf _ _ _))
  have h3 := cuspNorm_affPt_zero k hf (p ^ 2) 1 0
  have := zero_smul_fun k (((p : ℕ) : ℂ) ^ (-2 : ℤ)) (zero_add_fun k
    (zero_add_fun k h1 (zero_smul_fun k (χ (p : ℕ) * ((epsD (p : ℕ))⁻¹ * (Real.sqrt (p : ℕ) : ℂ)) ^ (2 * k + 1)) h2))
    (zero_smul_fun k (χ (p : ℕ) ^ 2 * ((p : ℕ) : ℂ) ^ (2 * k + 1)) h3))
  exact this

end ModularFormsKB.HalfIntegral
