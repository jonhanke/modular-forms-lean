import ModularFormsKB.Miyake.Wave2B.EisensteinSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import ModularFormsKB.Citation
/-!
# Miyake §7.2: Eisenstein series with a parameter $s$ (Hecke's trick), the convergent range

Miyake, *Modular Forms* (Springer 1989), §7.2, pp. 274–276.

For an integer $k$, a complex number $s$ and Dirichlet characters $\chi$ mod $L$, $\psi$ mod $M$,
Miyake (7.2.1) puts
$$E_k(z,s;\chi,\psi) = \sideset{}{'}\sum_{m,n} \chi(m)\psi(n)\,(mz+n)^{-k}\,|mz+n|^{-2s}.$$
We prove that the series converges absolutely for $k + 2\operatorname{Re}(s) > 2$, that it is
holomorphic in $s$ there, its transformation law (7.2.2) under $\Gamma_0(L,M)$, and that it vanishes
unless $\chi(-1)\psi(-1) = (-1)^k$ (p. 275).

The analytic continuation in $s$ (Lemmas 7.2.1–7.2.3, Theorems 7.2.4–7.2.9, via the confluent
hypergeometric function and Poisson summation) is not formalized here; see the end of the file
for the precise statements of the weight $2$ and weight $1$ results, Theorems 7.2.12 and 7.2.13,
recorded as propositions (not proved).
-/

open UpperHalfPlane ModularForm EisensteinSeries Matrix Complex
open scoped MatrixGroups Real

noncomputable section

namespace ModularFormsKB.Miyake.Wave2B

/-- The term $(mz+n)^{-k}|mz+n|^{-2s}$ of Miyake (7.2.1) for $v = (m,n) \ne 0$, and $0$ at
$v = 0$ (Miyake's $\sum'$ omits $(0,0)$). -/
def heckeSummand (k : ℤ) (s : ℂ) (v : Fin 2 → ℤ) (z : ℍ) : ℂ :=
  if v = 0 then 0 else
    ((v 0 : ℂ) * z + v 1) ^ (-k) * ((‖(v 0 : ℂ) * z + v 1‖ : ℝ) : ℂ) ^ (-2 * s)

lemma linear_ne_zero_of_ne_zero {v : Fin 2 → ℤ} (hv : v ≠ 0) (z : ℍ) :
    (v 0 : ℂ) * z + v 1 ≠ 0 := by
  have h := linear_ne_zero (cd := fun i ↦ ((v i : ℤ) : ℝ)) z
    (fun h ↦ hv (funext fun i ↦ by simpa using congrFun h i))
  simpa using h

/-- $|(mz+n)^{-k}|mz+n|^{-2s}| = |mz+n|^{-(k + 2\operatorname{Re} s)}$. -/
lemma norm_heckeSummand (k : ℤ) (s : ℂ) {v : Fin 2 → ℤ} (hv : v ≠ 0) (z : ℍ) :
    ‖heckeSummand k s v z‖ = ‖(v 0 : ℂ) * z + v 1‖ ^ (-((k : ℝ) + 2 * s.re)) := by
  have hw := linear_ne_zero_of_ne_zero hv z
  have hpos : 0 < ‖(v 0 : ℂ) * z + v 1‖ := norm_pos_iff.mpr hw
  simp only [heckeSummand, hv, ↓reduceIte]
  rw [norm_mul, norm_zpow, norm_cpow_eq_rpow_re_of_pos hpos,
    ← Real.rpow_intCast, ← Real.rpow_add hpos]
  congr 1
  simp
  ring

/-- The bound $|mz+n|^{-\sigma} \le r(z)^{-\sigma}\,\|(m,n)\|^{-\sigma}$ makes the series of
$|mz+n|^{-\sigma}$ summable for $\sigma > 2$. -/
lemma summable_norm_linear_rpow {σ : ℝ} (hσ : 2 < σ) (z : ℍ) :
    Summable fun v : Fin 2 → ℤ ↦ ‖(v 0 : ℂ) * z + v 1‖ ^ (-σ) := by
  refine ((summable_one_div_norm_rpow hσ).mul_left (r z ^ (-σ))).of_nonneg_of_le
    (fun _ ↦ by positivity) fun v ↦ ?_
  exact summand_bound z (by linarith) v

/-- **Miyake, p. 274.** The series (7.2.1) converges absolutely for $k + 2\operatorname{Re}(s) > 2$. -/
lemma summable_norm_heckeSummand {k : ℤ} {s : ℂ} (hks : 2 < (k : ℝ) + 2 * s.re) (z : ℍ) :
    Summable fun v : Fin 2 → ℤ ↦ ‖heckeSummand k s v z‖ := by
  refine (summable_norm_linear_rpow hks z).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun v ↦ ?_
  by_cases hv : v = 0
  · simp [heckeSummand, hv]
    positivity
  · rw [norm_heckeSummand k s hv]

/-- **Miyake (7.2.1).** The Eisenstein series with parameter $s$,
$E_k(z,s;\chi,\psi) = \sum'_{m,n}\chi(m)\psi(n)(mz+n)^{-k}|mz+n|^{-2s}$. -/
@[kb "miyake1989" "(7.2.1), p. 274"]
def eisensteinCharS (k : ℤ) (s : ℂ) {L M : ℕ} (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (z : ℍ) : ℂ :=
  ∑' v : Fin 2 → ℤ, χ (v 0) * ψ (v 1) * heckeSummand k s v z

/-- **Miyake, p. 274.** The series defining $E_k(z,s;\chi,\psi)$ converges absolutely for
$k + 2\operatorname{Re}(s) > 2$. -/
@[kb "miyake1989" "(7.2.1), p. 274"]
theorem summable_eisensteinCharS {k : ℤ} {s : ℂ} (hks : 2 < (k : ℝ) + 2 * s.re) {L M : ℕ}
    (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (z : ℍ) :
    Summable fun v : Fin 2 → ℤ ↦ ‖χ (v 0) * ψ (v 1) * heckeSummand k s v z‖ := by
  refine (summable_norm_heckeSummand hks z).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun v ↦ ?_
  rw [norm_mul, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  exact (mul_le_mul (DirichletCharacter.norm_le_one _ _) (DirichletCharacter.norm_le_one _ _)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- For $x > 0$ and $a \le t \le b$, $x^{-t} \le x^{-a} + x^{-b}$. -/
lemma rpow_neg_le_add {x a b t : ℝ} (hx : 0 < x) (ha : a ≤ t) (hb : t ≤ b) :
    x ^ (-t) ≤ x ^ (-a) + x ^ (-b) := by
  rcases le_or_gt 1 x with h1 | h1
  · have := Real.rpow_le_rpow_of_exponent_le h1 (neg_le_neg ha)
    linarith [Real.rpow_nonneg hx.le (-b)]
  · have := Real.rpow_le_rpow_of_exponent_ge hx h1.le (neg_le_neg hb)
    linarith [Real.rpow_nonneg hx.le (-a)]

/-- **Miyake, p. 274.** $E_k(z,s;\chi,\psi)$ is holomorphic in $s$ on $k + 2\operatorname{Re}(s) > 2$. -/
@[kb "miyake1989" "(7.2.1), p. 274"]
theorem differentiableOn_eisensteinCharS (k : ℤ) {L M : ℕ} (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (z : ℍ) :
    DifferentiableOn ℂ (fun s ↦ eisensteinCharS k s χ ψ z) {s | 2 < (k : ℝ) + 2 * s.re} := by
  intro s₀ hs₀
  simp only [Set.mem_ofPred_eq] at hs₀
  -- a vertical strip `a < Re s < b` around `s₀` inside the domain
  set a : ℝ := ((2 - k) / 2 + s₀.re) / 2 with ha
  set b : ℝ := s₀.re + 1 with hb
  set U : Set ℂ := {s | a < s.re ∧ s.re < b} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hs₀U : s₀ ∈ U := by
    simp only [hU, Set.mem_ofPred_eq, ha, hb]
    constructor <;> linarith
  have hka : 2 < (k : ℝ) + 2 * a := by simp only [ha]; linarith
  have hkb : 2 < (k : ℝ) + 2 * b := by simp only [hb]; linarith
  set u : (Fin 2 → ℤ) → ℝ := fun v ↦ ‖(v 0 : ℂ) * z + v 1‖ ^ (-((k : ℝ) + 2 * a)) +
    ‖(v 0 : ℂ) * z + v 1‖ ^ (-((k : ℝ) + 2 * b)) with hu
  have hus : Summable u :=
    (summable_norm_linear_rpow hka z).add (summable_norm_linear_rpow hkb z)
  have hdiff : DifferentiableOn ℂ (fun s ↦ ∑' v : Fin 2 → ℤ,
      χ (v 0) * ψ (v 1) * heckeSummand k s v z) U := by
    refine differentiableOn_tsum_of_summable_norm hus (fun v ↦ ?_) hUo fun v s hs ↦ ?_
    · by_cases hv : v = 0
      · simp only [heckeSummand, hv, ↓reduceIte, mul_zero]
        exact differentiableOn_const _
      · simp only [heckeSummand, hv, ↓reduceIte]
        have hpos : (((‖(v 0 : ℂ) * z + v 1‖ : ℝ)) : ℂ) ≠ 0 := by
          exact_mod_cast (norm_pos_iff.mpr (linear_ne_zero_of_ne_zero hv z)).ne'
        refine DifferentiableOn.const_mul (DifferentiableOn.const_mul ?_ _) _
        exact fun s _ ↦ ((differentiableAt_id.const_mul (-2)).const_cpow
          (Or.inl hpos)).differentiableWithinAt
    · by_cases hv : v = 0
      · simp only [heckeSummand, hv, ↓reduceIte, mul_zero, norm_zero, hu]
        positivity
      · rw [norm_mul, norm_heckeSummand k s hv]
        refine (mul_le_of_le_one_left (by positivity) ?_).trans ?_
        · rw [norm_mul]
          exact (mul_le_mul (DirichletCharacter.norm_le_one _ _)
            (DirichletCharacter.norm_le_one _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
        · simp only [hU, Set.mem_ofPred_eq] at hs
          exact rpow_neg_le_add (norm_pos_iff.mpr (linear_ne_zero_of_ne_zero hv z))
            (by linarith) (by linarith)
  exact (hdiff.differentiableAt (hUo.mem_nhds hs₀U)).differentiableWithinAt

/-- Negating $(m,n)$ multiplies the term of (7.2.1) by $(-1)^k$. -/
lemma heckeSummand_neg (k : ℤ) (s : ℂ) (v : Fin 2 → ℤ) (z : ℍ) :
    heckeSummand k s (-v) z = (-1) ^ k * heckeSummand k s v z := by
  by_cases hv : v = 0
  · simp [heckeSummand, hv]
  · have hv' : -v ≠ 0 := neg_ne_zero.mpr hv
    simp only [heckeSummand, hv, hv', ↓reduceIte, Pi.neg_apply, Int.cast_neg]
    rw [show -(v 0 : ℂ) * z + -(v 1 : ℂ) = (-1) * ((v 0 : ℂ) * z + v 1) by ring, mul_zpow,
      norm_mul, norm_neg, norm_one, one_mul]
    rw [_root_.zpow_neg (-1 : ℂ), ← _root_.inv_zpow, inv_neg, inv_one]
    ring

/-- **Miyake, p. 275.** If $\chi(-1)\psi(-1) \ne (-1)^k$ then $E_k(z,s;\chi,\psi) = 0$. -/
@[kb "miyake1989" "§7.2, p. 275"]
theorem eisensteinCharS_eq_zero_of_parity (k : ℤ) (s : ℂ) {L M : ℕ}
    (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (h : χ (-1) * ψ (-1) ≠ (-1) ^ k) (z : ℍ) : eisensteinCharS k s χ ψ z = 0 := by
  have hE : eisensteinCharS k s χ ψ z =
      (χ (-1) * ψ (-1) * (-1) ^ k) * eisensteinCharS k s χ ψ z := by
    simp only [eisensteinCharS]
    rw [← tsum_mul_left]
    conv_lhs => rw [← (Equiv.neg (Fin 2 → ℤ)).tsum_eq]
    refine tsum_congr fun v ↦ ?_
    simp only [Equiv.neg_apply, Pi.neg_apply, Int.cast_neg, heckeSummand_neg]
    rw [show -(v 0 : ZMod L) = (-1) * v 0 by ring, show -(v 1 : ZMod M) = (-1) * v 1 by ring,
      map_mul, map_mul]
    ring
  have hsq : ((-1 : ℂ) ^ k) * ((-1) ^ k) = 1 := by
    rw [← mul_zpow]; simp
  have hc : χ (-1) * ψ (-1) * (-1) ^ k ≠ 1 := by
    intro h1
    apply h
    calc χ (-1) * ψ (-1) = χ (-1) * ψ (-1) * ((-1) ^ k * (-1) ^ k) := by rw [hsq, mul_one]
      _ = (-1) ^ k := by rw [← mul_assoc, h1, one_mul]
  have : (1 - χ (-1) * ψ (-1) * (-1) ^ k) * eisensteinCharS k s χ ψ z = 0 := by
    rw [sub_mul, one_mul, ← hE, sub_self]
  simpa [sub_eq_zero, Ne.symm hc] using this

/-- How the term of (7.2.1) changes under $\gamma \in SL_2(\mathbb Z)$: with $j = cz + d$,
$(m\gamma z + n)^{-k}|m\gamma z+n|^{-2s} = j^k|j|^{2s}\,(m'z+n')^{-k}|m'z+n'|^{-2s}$ for
$(m',n') = (m,n)\gamma$. -/
lemma heckeSummand_smul (k : ℤ) (s : ℂ) (v : Fin 2 → ℤ) (γ : SL(2, ℤ)) (z : ℍ) :
    heckeSummand k s v (γ • z) = (denom γ z) ^ k * ((‖denom γ z‖ : ℝ) : ℂ) ^ (2 * s) *
      heckeSummand k s (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) z := by
  have hj : denom γ z ≠ 0 := denom_ne_zero _ z
  have hjn : 0 < ‖denom γ z‖ := norm_pos_iff.mpr hj
  by_cases hv : v = 0
  · simp [heckeSummand, hv]
  have hv' : v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ) ≠ 0 := by
    intro h0
    apply hv
    have := congrArg (fun w ↦ w ᵥ* ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) h0
    rwa [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one, Matrix.zero_vecMul] at this
  -- the linear form transforms with the factor `j⁻¹`
  have hlin := eisSummand_SL2_apply (-1) v γ z
  simp only [eisSummand, neg_neg, zpow_one] at hlin
  set w := (v 0 : ℂ) * (γ • z : ℍ) + v 1 with hw
  set w' := ((v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) 0 : ℂ) * z +
    (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) 1 with hw'
  have hw'0 : w' ≠ 0 := linear_ne_zero_of_ne_zero hv' z
  have hww : w = (denom γ z)⁻¹ * w' := by
    rw [hlin, _root_.zpow_neg, zpow_one]
  simp only [heckeSummand, hv, hv', ↓reduceIte]
  rw [← hw, ← hw', hww, mul_zpow, _root_.inv_zpow', neg_neg, norm_mul, norm_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (inv_nonneg.mpr hjn.le) (norm_nonneg _),
    Complex.ofReal_inv, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg hjn.le]; exact Real.pi_pos.ne),
    show -2 * s = -(2 * s) by ring, Complex.cpow_neg (((‖denom γ z‖ : ℝ)) : ℂ), inv_inv]
  ring

/-- **Miyake (7.2.2).** For $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \Gamma_0(L,M)$
and $k + 2\operatorname{Re}(s) > 2$ (where (7.2.1) converges),
$E_k(\gamma z,s;\chi,\psi) = \chi(d)\overline{\psi(d)}\,(cz+d)^k|cz+d|^{2s}E_k(z,s;\chi,\psi)$. -/
@[kb "miyake1989" "(7.2.2), p. 274"]
theorem eisensteinCharS_smul (k : ℤ) (s : ℂ) {L M : ℕ} (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) {γ : SL(2, ℤ)} (hγ : IsGamma0LM L M γ) (z : ℍ) :
    eisensteinCharS k s χ ψ (γ • z) = χ (γ 1 1) * starRingEnd ℂ (ψ (γ 1 1)) *
      (denom γ z) ^ k * ((‖denom γ z‖ : ℝ) : ℂ) ^ (2 * s) * eisensteinCharS k s χ ψ z := by
  simp only [eisensteinCharS, heckeSummand_smul, ← tsum_mul_left]
  have h1 : ∀ v : Fin 2 → ℤ, (v ᵥ* ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ᵥ*
      (γ : Matrix (Fin 2) (Fin 2) ℤ) = v := by
    intro v
    rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  have h2 : ∀ v : Fin 2 → ℤ, (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) ᵥ*
      ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = v := by
    intro v
    rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  let e : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) :=
    { toFun := fun v ↦ v ᵥ* ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      invFun := fun v ↦ v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)
      left_inv := h1
      right_inv := h2 }
  conv_lhs => rw [← e.tsum_eq]
  refine tsum_congr fun w ↦ ?_
  simp only [e, Equiv.coe_fn_mk, h1]
  rw [inv_apply_SL2]
  have hc : ((γ 1 0 : ℤ) : ZMod L) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hγ.2
  have hb : ((γ 0 1 : ℤ) : ZMod M) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hγ.1
  have h0 : (((w ᵥ* !![γ 1 1, -γ 0 1; -γ 1 0, γ 0 0]) 0 : ℤ) : ZMod L) =
      (w 0 : ZMod L) * (γ 1 1 : ZMod L) := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hc]
  have h1' : (((w ᵥ* !![γ 1 1, -γ 0 1; -γ 1 0, γ 0 0]) 1 : ℤ) : ZMod M) =
      (w 1 : ZMod M) * (γ 0 0 : ZMod M) := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hb]
  rw [h0, h1', map_mul, map_mul, char_a_eq_conj_char_d ψ hγ.1]
  ring

/-- The point $-\bar z$ of the upper half-plane. -/
def negConj (z : ℍ) : ℍ :=
  ⟨-(starRingEnd ℂ) (z : ℂ), by simpa using z.2⟩

lemma coe_negConj (z : ℍ) : (negConj z : ℂ) = -(starRingEnd ℂ) (z : ℂ) := rfl

/-- The termwise identity behind (7.2.4):
$(mz+n)^{-k}|mz+n|^{-2s} = (-m(-\bar z)+n)^{k}\,|{-m(-\bar z)}+n|^{-2(k+s)}$. -/
lemma heckeSummand_negConj (k : ℤ) (s : ℂ) (v : Fin 2 → ℤ) (z : ℍ) :
    heckeSummand (-k) (k + s) ![-v 0, v 1] (negConj z) = heckeSummand k s v z := by
  by_cases hv : v = 0
  · simp [heckeSummand, hv]
  have hv' : (![-v 0, v 1] : Fin 2 → ℤ) ≠ 0 := by
    intro h
    apply hv
    funext i
    fin_cases i
    · simpa using congrFun h 0
    · simpa using congrFun h 1
  set w : ℂ := (v 0 : ℂ) * z + v 1 with hw
  have hw0 : w ≠ 0 := linear_ne_zero_of_ne_zero hv z
  have hconj : ((-v 0 : ℤ) : ℂ) * (negConj z : ℂ) + (v 1 : ℂ) = (starRingEnd ℂ) w := by
    simp [hw, coe_negConj, map_add, map_mul]
  simp only [heckeSummand, hv, hv', ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [hconj, ← hw, Complex.norm_conj, neg_neg]
  have hn : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hw0).ne'
  have hsplit : ((‖w‖ : ℝ) : ℂ) ^ (-2 * ((k : ℂ) + s)) =
      ((‖w‖ : ℝ) : ℂ) ^ (-2 * s) * (((‖w‖ : ℝ) : ℂ) ^ (2 * k))⁻¹ := by
    rw [show -2 * ((k : ℂ) + s) = -2 * s + -((2 * k : ℤ) : ℂ) by push_cast; ring,
      Complex.cpow_add _ _ hn, Complex.cpow_neg, Complex.cpow_intCast]
  have hnorm : ((‖w‖ : ℝ) : ℂ) ^ (2 * k) = (w * (starRingEnd ℂ) w) ^ k := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, _root_.zpow_mul]
    push_cast
    rfl
  rw [hsplit, hnorm, mul_zpow, _root_.zpow_neg w k]
  have hc0 : (starRingEnd ℂ) w ≠ 0 := (map_ne_zero _).mpr hw0
  have hck : ((starRingEnd ℂ) w) ^ k ≠ 0 := zpow_ne_zero _ hc0
  field_simp

/-- **Miyake (7.2.4).** $E_k(z,s;\chi,\psi) = \chi(-1)\,E_{-k}(-\bar z,k+s;\chi,\psi)$. (This holds
termwise; Miyake states it for $k + 2\operatorname{Re}(s) > 2$, where both series converge.) -/
@[kb "miyake1989" "(7.2.4), p. 275"]
theorem eisensteinCharS_negConj (k : ℤ) (s : ℂ) {L M : ℕ} (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (z : ℍ) :
    eisensteinCharS k s χ ψ z = χ (-1) * eisensteinCharS (-k) (k + s) χ ψ (negConj z) := by
  let e : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) :=
    { toFun := fun v ↦ ![-v 0, v 1]
      invFun := fun v ↦ ![-v 0, v 1]
      left_inv := fun v ↦ by funext i; fin_cases i <;> simp
      right_inv := fun v ↦ by funext i; fin_cases i <;> simp }
  simp only [eisensteinCharS]
  rw [← tsum_mul_left]
  conv_rhs => rw [← e.tsum_eq]
  refine tsum_congr fun v ↦ ?_
  simp only [e, Equiv.coe_fn_mk, heckeSummand_negConj, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_neg]
  rw [show -(v 0 : ZMod L) = (-1) * v 0 by ring, map_mul]
  have h1 : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; simp
  linear_combination (-(ψ (v 1) * heckeSummand k s v z * χ (v 0))) * h1

/-! ### Weights two and one: Hecke's limit (statements only)

Miyake defines $E_2(z;\chi,\psi)$ and $E_1(z;\chi,\psi)$ as the value at $s = 0$ of the analytic
continuation of $E_k(z,s;\chi,\psi)$ (Theorem 7.2.9). That continuation (Lemmas 7.2.1–7.2.3,
Theorems 7.2.4–7.2.8: the confluent hypergeometric function $\omega(y;\alpha,\beta)$, its bounds,
and Poisson summation for $S(z;\alpha,\beta) = \sum_n (z+n)^{-\alpha}(\bar z+n)^{-\beta}$) is not
formalized. The missing input is Miyake's Theorem 7.2.8, the meromorphic continuation of
$S(z;\alpha,\beta)$ in $(\alpha, \beta)$ with its Fourier expansion; with it, Theorems 7.2.9,
7.2.12 and 7.2.13 follow as in the book. We record Theorems 7.2.12 and 7.2.13 as precise
propositions; they are **not** proved here. The holomorphic part of Theorem 7.2.12 for the
row-wise sum is `hasSum_eisensteinCharRowSum` (with $k = 2$). -/

/-- `IsHeckeLimit k χ ψ z w`: the function $s \mapsto E_k(z,s;\chi,\psi)$, defined by (7.2.1) for
$k + 2\operatorname{Re}(s) > 2$, continues holomorphically to the connected open set
$\{|s| < \varepsilon\} \cup \{\operatorname{Re}(s) > 0\}$ for some $\varepsilon > 0$, with value $w$ at
$s = 0$. (For $k \ge 1$ the convergence half-plane lies in this set, so by the identity theorem the
continuation, hence $w$, is unique.) -/
def IsHeckeLimit (k : ℤ) {L M : ℕ} (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (z : ℍ) (w : ℂ) : Prop :=
  ∃ ε > (0 : ℝ), ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ε ∪ {s | 0 < s.re}) ∧
    (∀ s : ℂ, 2 < (k : ℝ) + 2 * s.re → F s = eisensteinCharS k s χ ψ z) ∧ F 0 = w

open scoped Classical in
/-- **Miyake, Theorem 7.2.12** (statement only, not proved). If $\chi(-1)\psi(-1) = 1$, then
$E_2(z;\chi,\psi)$ (Hecke's limit) equals $C + D y^{-1} + A\sum_{n \ge 1} a_n e^{2\pi i n z/M}$,
with $C$ = `eisensteinCharConst 2`, $A = -8\pi^2W(\psi^0)/M^2$ = `eisensteinCharA 2`,
$a_n$ = `eisensteinCharCoeff 2`, and
$D = -\pi\prod_{p \mid M}(1-p^{-1})\prod_{p \mid L}(1-p^{-1})$ if $\chi$ and $\psi$ are both
principal, $D = 0$ otherwise. -/
@[kb "miyake1989" "Theorem 7.2.12, p. 288"]
def MiyakeTheorem7_2_12 : Prop :=
  ∀ (L M : ℕ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M),
    χ (-1) * ψ (-1) = 1 → ∀ z : ℍ, ∃ w : ℂ, IsHeckeLimit 2 χ ψ z w ∧
      HasSum (fun n : ℕ+ ↦ eisensteinCharA 2 ψ * eisensteinCharCoeff 2 χ ψ n *
          cexp (2 * π * Complex.I * (n : ℕ) * z / M))
        (w - eisensteinCharConst 2 (L := L) ψ -
          (if χ = 1 ∧ ψ = 1 then -π * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹)) *
            ∏ p ∈ L.primeFactors, (1 - (p : ℂ)⁻¹) else 0) / (z.im : ℂ))

open scoped Classical in
/-- **Miyake, Theorem 7.2.13** (statement only, not proved). If $\chi(-1)\psi(-1) = -1$, then
$E_1(z;\chi,\psi)$ (Hecke's limit) equals $C + D + A\sum_{n \ge 1} a_n e^{2\pi i n z/M}$, with
$C = 2L_M(1,\psi)$ if $\chi$ is the principal character $\chi_0$ (mod $1$) and $C = 0$ otherwise,
$D = -2\pi i\prod_{p \mid M}(1-p^{-1})\,L_L(0,\chi)$ if $\psi$ is principal and $D = 0$ otherwise,
$A = -4\pi i\,W(\psi^0)/M$ = `eisensteinCharA 1` and $a_n$ = `eisensteinCharCoeff 1`.
Here $L_M(s,\psi)$ is the (continued) Dirichlet $L$-function of $\psi$ as a character mod $M$. -/
@[kb "miyake1989" "Theorem 7.2.13, p. 288"]
def MiyakeTheorem7_2_13 : Prop :=
  ∀ (L M : ℕ) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M),
    χ (-1) * ψ (-1) = -1 → ∀ z : ℍ, ∃ w : ℂ, IsHeckeLimit 1 χ ψ z w ∧
      HasSum (fun n : ℕ+ ↦ eisensteinCharA 1 ψ * eisensteinCharCoeff 1 χ ψ n *
          cexp (2 * π * Complex.I * (n : ℕ) * z / M))
        (w - (if L = 1 then 2 * DirichletCharacter.LFunction ψ 1 else 0) -
          (if ψ = 1 then -2 * π * Complex.I * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹)) *
            DirichletCharacter.LFunction χ 0 else 0))

end ModularFormsKB.Miyake.Wave2B
