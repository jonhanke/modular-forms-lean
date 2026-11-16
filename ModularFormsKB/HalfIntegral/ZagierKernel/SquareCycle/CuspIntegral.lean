/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
-/
import ModularFormsKB.HalfIntegral.Abstract.ShintaniInvariance
import ModularFormsKB.HalfIntegral.Abstract.ShintaniGeodesic
import TauCeti.NumberTheory.ModularForms.GeodesicIntegral.Basic
import TauCeti.NumberTheory.ModularForms.SlashActionRat

/-!
# Cycle integrals at square discriminants are integrals between cusps

For a form $Q = [a, b, c]$ of discriminant $\Delta = n^2$, $n \ge 1$, the geodesic $S_Q$ joins two cusps, and the
cycle integral `BinQF.cycleIntegral k G Q` $= \int_{C_Q} G(z)\,Q(z,1)^{k-1}\,dz$ is an integral between cusps in the sense
of Tau Ceti (`Matrix.GeneralLinearGroup.geodesicIntegral`): for a rational matrix $g$ of positive determinant whose
columns are zeros of $Q$ in the right order (a **frame** of $Q$, `BinQF.IsFrame`), $g\cdot 0$ is the start and
$g\cdot\infty$ the end of the oriented geodesic, and
$$ \int_{C_Q} G(z)\,Q(z,1)^{k-1}\,dz = i\int_0^\infty (F_Q|_2\,g)(it)\,dt, \qquad F_Q(z) = G(z)\,Q(z,1)^{k-1}. $$
The orientation is that of `BinQF.geodesic` (from $w_+$ to $w_-$): the polarization $B_Q(g e_0, g e_1)$ is positive.

**Proved here.**
- `BinQF.exists_isFrame`: every form of discriminant $n^2$, $n \ge 1$, has a frame (explicit, by the sign of $a$ and $b$).
- `BinQF.geodesicIntegral_isFrame_eq`: two frames give the same geodesic integral ($g^{-1}g'$ is diagonal of positive
  determinant).
- `BinQF.cycleIntegral_eq_geodesicIntegral`: the cycle integral is the geodesic integral along any frame.
- `BinQF.cycleIntegral_comp_SL`: **class invariance** $\int_{C_{Q\circ\gamma}} = \int_{C_Q}$ for a level one cusp form $G$ of
  weight $2k$ and $\gamma \in \mathrm{SL}_2(\mathbb Z)$, at square discriminants (no integrability needed: the identity is
  the substitution $z \mapsto \gamma z$, `geodesicIntegral_mul`).

**Index shift.** Matrix entries are 0-based.
-/

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups ModularForm
open scoped Real

local notation "ℍ" => UpperHalfPlane

namespace BinQF

/-- The value $Q(x, y) = ax^2 + bxy + cy^2$ at rational $x, y$. -/
def valQ (Q : BinQF) (x y : ℚ) : ℚ := Q.a * x ^ 2 + Q.b * x * y + Q.c * y ^ 2

/-- The polarization $B_Q((x,y),(x',y')) = 2axx' + b(xy' + x'y) + 2cyy'$, so that
$Q(su + tv) = Q(u)s^2 + B_Q(u,v)st + Q(v)t^2$. -/
def polQ (Q : BinQF) (x y x' y' : ℚ) : ℚ := 2 * Q.a * x * x' + Q.b * (x * y' + x' * y) + 2 * Q.c * y * y'

/-- **A frame of $Q$**: $g \in \mathrm{GL}_2(\mathbb Q)$ of positive determinant whose two columns are zeros of $Q$, with
positive polarization. Then $Q \circ g = B\,xy$ with $B > 0$, $g \cdot 0$ is the start and $g \cdot \infty$ the end of the
oriented geodesic $S_Q$. -/
def IsFrame (Q : BinQF) (g : GL (Fin 2) ℚ) : Prop :=
  0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det ∧ Q.valQ (g 0 0) (g 1 0) = 0 ∧ Q.valQ (g 0 1) (g 1 1) = 0 ∧
    0 < Q.polQ (g 0 0) (g 1 0) (g 0 1) (g 1 1)

/-- The integrand $F_Q(z) = G(z)\,Q(z, 1)^{k-1}$ of the cycle integral, as a one-form $F_Q(z)\,dz$. -/
noncomputable def cycleIntegrand (k : ℕ) (G : ℍ → ℂ) (Q : BinQF) : ℍ → ℂ :=
  fun z ↦ G z * Q.evalC (z : ℂ) ^ (k - 1)

/-- A rational matrix of nonzero determinant as an element of `GL₂(ℚ)`. -/
private def mkQ (p q r s : ℚ) (h : p * s - q * r ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![p, q; r, s] (by simpa [Matrix.det_fin_two] using h)

private theorem mkQ_00 (p q r s : ℚ) (h) : (mkQ p q r s h) 0 0 = p := by simp [mkQ]
private theorem mkQ_01 (p q r s : ℚ) (h) : (mkQ p q r s h) 0 1 = q := by simp [mkQ]
private theorem mkQ_10 (p q r s : ℚ) (h) : (mkQ p q r s h) 1 0 = r := by simp [mkQ]
private theorem mkQ_11 (p q r s : ℚ) (h) : (mkQ p q r s h) 1 1 = s := by simp [mkQ]

private theorem mkQ_det (p q r s : ℚ) (h) :
    ((mkQ p q r s h : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = p * s - q * r := by
  simp [mkQ, Matrix.det_fin_two]

private theorem mkQ_isFrame (Q : BinQF) (p q r s : ℚ) (h : p * s - q * r ≠ 0) (h1 : 0 < p * s - q * r)
    (h2 : Q.valQ p r = 0) (h3 : Q.valQ q s = 0) (h4 : 0 < Q.polQ p r q s) :
    Q.IsFrame (mkQ p q r s h) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mkQ_det]; exact h1
  · rw [mkQ_00, mkQ_10]; exact h2
  · rw [mkQ_01, mkQ_11]; exact h3
  · rw [mkQ_00, mkQ_10, mkQ_01, mkQ_11]; exact h4

/-- The point `i e^s` of the upper half plane. -/
private noncomputable def axisPt (s : ℝ) : ℍ :=
  ⟨Complex.I * (Real.exp s : ℝ), by
    have := Real.exp_pos s
    simpa [Complex.exp_ofReal_re] using this⟩

private theorem coe_axisPt (s : ℝ) : ((axisPt s : ℍ) : ℂ) = Complex.I * (Real.exp s : ℝ) := rfl

private theorem coe_smul_mkQ (p q r s : ℚ) (h : p * s - q * r ≠ 0) (hd : 0 < p * s - q * r) (τ : ℍ) :
    (((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (mkQ p q r s h)) • τ : ℍ) : ℂ) =
      ((p : ℂ) * τ + q) / ((r : ℂ) * τ + s) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos]
  · simp [UpperHalfPlane.num, UpperHalfPlane.denom, Matrix.GeneralLinearGroup.map_apply, mkQ_00, mkQ_01, mkQ_10, mkQ_11]
  · have := ModularForm.det_map_ratCast_pos (g := mkQ p q r s h) (by rw [mkQ_det]; exact hd)
    simpa using this

private theorem frame_zero_pos (Q : BinQF) (ha : Q.a = 0) (hb : 0 < Q.b) :
    ∃ g : GL (Fin 2) ℚ, Q.IsFrame g ∧ ∀ s : ℝ,
      (((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g) • axisPt s : ℍ) : ℂ) = Q.geodesic s := by
  have hbq : (0 : ℚ) < Q.b := by exact_mod_cast hb
  have hbr : (0 : ℝ) < Q.b := by exact_mod_cast hb
  have h : (1 : ℚ) * 1 - (-(Q.c : ℚ) / Q.b) * 0 ≠ 0 := by norm_num
  refine ⟨mkQ 1 (-(Q.c : ℚ) / Q.b) 0 1 h, mkQ_isFrame _ _ _ _ _ h (by norm_num) ?_ ?_ ?_, fun s => ?_⟩
  · simp [valQ, ha]
  · simp only [valQ, ha]; push_cast; field_simp; ring
  · simp [polQ, ha, hb]
  · rw [coe_smul_mkQ _ _ _ _ h (by norm_num), coe_axisPt]
    simp only [geodesic, ha, ↓reduceIte, sign_pos hbr]
    push_cast
    ring_nf
    simp

private theorem frame_zero_neg (Q : BinQF) (ha : Q.a = 0) (hb : Q.b < 0) :
    ∃ g : GL (Fin 2) ℚ, Q.IsFrame g ∧ ∀ s : ℝ,
      (((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g) • axisPt s : ℍ) : ℂ) = Q.geodesic s := by
  have hbq : (Q.b : ℚ) < 0 := by exact_mod_cast hb
  have hbr : (Q.b : ℝ) < 0 := by exact_mod_cast hb
  have hbne : (Q.b : ℚ) ≠ 0 := hbq.ne
  have h : (-(Q.c : ℚ) / Q.b) * 0 - (-1) * 1 ≠ 0 := by norm_num
  refine ⟨mkQ (-(Q.c : ℚ) / Q.b) (-1) 1 0 (by simpa using h),
    mkQ_isFrame _ _ _ _ _ (by simpa using h) (by norm_num) ?_ ?_ ?_, fun s => ?_⟩
  · simp only [valQ, ha]; push_cast; field_simp; ring
  · simp [valQ, ha]
  · simp [polQ, ha]; linarith
  · rw [coe_smul_mkQ _ _ _ _ (by simpa using h) (by norm_num), coe_axisPt]
    simp only [geodesic, ha, ↓reduceIte, sign_neg hbr]
    have hE : (Real.exp s : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos s).ne'
    have hE2 : Complex.exp (-(s : ℂ)) = (Complex.exp s)⁻¹ := Complex.exp_neg _
    push_cast
    have h1 : (((1 : SignType) : ℝ) : ℂ) = 1 := by simp
    rw [h1, neg_one_mul, hE2]
    field_simp
    ring_nf
    simp

private theorem sqrt_disc_eq (Q : BinQF) {n : ℕ} (hQ : Q.disc = (n : ℤ) ^ 2) : √(Q.disc : ℝ) = n := by
  rw [hQ]; push_cast; exact Real.sqrt_sq (Nat.cast_nonneg _)

private theorem disc_rat (Q : BinQF) {n : ℕ} (hQ : Q.disc = (n : ℤ) ^ 2) :
    (Q.b : ℚ) ^ 2 - 4 * Q.a * Q.c = (n : ℚ) ^ 2 := by
  have := congrArg (Int.cast : ℤ → ℚ) hQ
  simp only [disc] at this
  push_cast at this
  exact this

private theorem frame_ne_aux (Q : BinQF) {n : ℕ} (hn : 0 < n) (hQ : Q.disc = (n : ℤ) ^ 2) (ha : Q.a ≠ 0)
    (ε : ℚ) (hε : ε = 1 ∨ ε = -1) (hεa : ε * Q.a < 0) :
    ∃ g : GL (Fin 2) ℚ, Q.IsFrame g ∧ ∀ s : ℝ,
      (((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g) • axisPt s : ℍ) : ℂ) = Q.geodesic s := by
  have hQq := disc_rat Q hQ
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have haq : (Q.a : ℚ) ≠ 0 := by exact_mod_cast ha
  have har : (Q.a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hεa' : ε * (Q.a : ℚ) < 0 := hεa
  have habs : |(Q.a : ℝ)| = -((ε : ℝ) * Q.a) := by
    rcases hε with rfl | rfl
    · have : (Q.a : ℝ) < 0 := by
        have : (Q.a : ℚ) < 0 := by simpa using hεa'
        exact_mod_cast this
      simp [abs_of_neg this]
    · have : (0 : ℝ) < Q.a := by
        have : (0 : ℚ) < Q.a := by simpa using hεa'
        exact_mod_cast this
      simp [abs_of_pos this]
  set wm : ℚ := (-(Q.b : ℚ) - n) / (2 * Q.a) with hwm
  set wp : ℚ := (-(Q.b : ℚ) + n) / (2 * Q.a) with hwp
  have hdet : ε * wm * 1 - wp * ε = (-(ε * Q.a)) * n / (Q.a : ℚ) ^ 2 := by
    rw [hwm, hwp]; field_simp; ring
  have hpos : 0 < ε * wm * 1 - wp * ε := by
    rw [hdet]; exact div_pos (mul_pos (neg_pos.2 hεa') hnq) (by positivity)
  have hne : ε * wm * 1 - wp * ε ≠ 0 := hpos.ne'
  have hm0 : (Q.a : ℚ) * wm ^ 2 + Q.b * wm + Q.c = 0 := by
    rw [hwm]; field_simp; linear_combination (-1) * hQq
  have hp0 : (Q.a : ℚ) * wp ^ 2 + Q.b * wp + Q.c = 0 := by
    rw [hwp]; field_simp; linear_combination (-1) * hQq
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  refine ⟨mkQ (ε * wm) wp ε 1 hne, mkQ_isFrame _ _ _ _ _ hne hpos ?_ ?_ ?_, fun s => ?_⟩
  · simp only [valQ]; linear_combination (ε * ε) * hm0
  · simp only [valQ]; linear_combination hp0
  · have : Q.polQ (ε * wm) ε wp 1 = (-(ε * Q.a)) * n ^ 2 / (Q.a : ℚ) ^ 2 := by
      simp only [polQ, hwm, hwp]; field_simp; linear_combination (-ε) * hQq
    rw [this]
    exact div_pos (mul_pos (neg_pos.2 hεa') (by positivity)) (by positivity)
  · rw [coe_smul_mkQ _ _ _ _ hne hpos, coe_axisPt]
    have hs := sqrt_disc_eq Q hQ
    simp only [geodesic, ha, ↓reduceIte]
    rw [hs]
    have ht : 0 < Real.exp s := Real.exp_pos s
    have hT : Real.tanh s = ((Real.exp s) ^ 2 - 1) / ((Real.exp s) ^ 2 + 1) := by
      rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
      field_simp
    have hC : Real.cosh s = ((Real.exp s) ^ 2 + 1) / (2 * Real.exp s) := by
      rw [Real.cosh_eq, Real.exp_neg]
      field_simp
    rw [hT, hC, habs]
    generalize Real.exp s = t at ht ⊢
    simp only [hwm, hwp]
    push_cast
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have ht2 : (t : ℂ) ^ 2 + 1 ≠ 0 := by
      have : (0 : ℝ) < t ^ 2 + 1 := by positivity
      exact_mod_cast this.ne'
    have hac : (Q.a : ℂ) ≠ 0 := by exact_mod_cast ha
    rcases hε with h | h
    · have hεc : (ε : ℂ) = 1 := by exact_mod_cast h
      rw [hεc]
      have hden : (1 : ℂ) * (Complex.I * t) + 1 ≠ 0 := by
        intro h0
        have := congrArg Complex.re h0
        simp at this
      rw [div_eq_iff hden]
      field_simp
      linear_combination (2 * (n : ℂ) * (t : ℂ) ^ 2) * Complex.I_sq
    · have hεc : (ε : ℂ) = -1 := by exact_mod_cast h
      rw [hεc]
      have hden : (-1 : ℂ) * (Complex.I * t) + 1 ≠ 0 := by
        intro h0
        have := congrArg Complex.re h0
        simp at this
      rw [div_eq_iff hden]
      field_simp
      linear_combination (2 * (n : ℂ) * (t : ℂ) ^ 2) * Complex.I_sq

private theorem exists_frame_geodesic (Q : BinQF) {n : ℕ} (hn : 0 < n) (hQ : Q.disc = (n : ℤ) ^ 2) :
    ∃ g : GL (Fin 2) ℚ, Q.IsFrame g ∧ ∀ s : ℝ,
      (((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g) • axisPt s : ℍ) : ℂ) = Q.geodesic s := by
  by_cases ha : Q.a = 0
  · have hb : Q.b ≠ 0 := by
      intro hb
      have hn' : (0 : ℤ) < (n : ℤ) ^ 2 := by positivity
      rw [← hQ] at hn'
      simp [disc, ha, hb] at hn'
    rcases lt_or_gt_of_ne hb with h | h
    · exact frame_zero_neg Q ha h
    · exact frame_zero_pos Q ha h
  · rcases lt_or_gt_of_ne ha with h | h
    · refine frame_ne_aux Q hn hQ ha 1 (Or.inl rfl) ?_
      have : (Q.a : ℚ) < 0 := by exact_mod_cast h
      simpa using this
    · refine frame_ne_aux Q hn hQ ha (-1) (Or.inr rfl) ?_
      have : (0 : ℚ) < Q.a := by exact_mod_cast h
      simpa using this

/-- **Every form of discriminant $n^2$, $n \ge 1$, has a frame.** -/
theorem exists_isFrame (Q : BinQF) {n : ℕ} (hn : 0 < n) (hQ : Q.disc = (n : ℤ) ^ 2) :
    ∃ g : GL (Fin 2) ℚ, Q.IsFrame g := by
  obtain ⟨g, hg, -⟩ := exists_frame_geodesic Q hn hQ
  exact ⟨g, hg⟩

/-- **Two frames give the same geodesic integral**: $g^{-1}g'$ is diagonal of positive determinant. -/
theorem geodesicIntegral_isFrame_eq {Q : BinQF} {g g' : GL (Fin 2) ℚ} (hg : Q.IsFrame g) (hg' : Q.IsFrame g')
    (F : ℍ → ℂ) : g.geodesicIntegral F = g'.geodesicIntegral F := by
  obtain ⟨hdg, hv0, hv1, hP⟩ := hg
  obtain ⟨hdg', hw0, hw1, hP'⟩ := hg'
  set d : GL (Fin 2) ℚ := g⁻¹ * g' with hd
  have hgd : g' = g * d := by rw [hd, mul_inv_cancel_left]
  have hm : ∀ i j, g' i j = g i 0 * d 0 j + g i 1 * d 1 j := by
    intro i j
    rw [hgd]
    show ((g * d : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j = _
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hdet : 0 < (d : Matrix (Fin 2) (Fin 2) ℚ).det := by
    have h1 := hdg'
    rw [hgd, Units.val_mul, Matrix.det_mul] at h1
    by_contra hneg
    have hneg := not_lt.mp hneg
    nlinarith
  have hdet0 := hdet
  have hdet2 := hdet
  rw [Matrix.det_fin_two] at hdet2
  rw [hm 0 0, hm 1 0] at hw0
  rw [hm 0 1, hm 1 1] at hw1
  rw [hm 0 0, hm 1 0, hm 0 1, hm 1 1] at hP'
  rw [Matrix.det_fin_two] at hdg
  simp only [valQ, polQ] at hv0 hv1 hP hw0 hw1 hP'
  generalize g 0 0 = p at *
  generalize g 0 1 = q at *
  generalize g 1 0 = r at *
  generalize g 1 1 = s at *
  have e1 : d 0 0 * d 1 0 * (2 * Q.a * p * q + Q.b * (p * s + q * r) + 2 * Q.c * r * s) = 0 := by
    linear_combination hw0 - (d 0 0) ^ 2 * hv0 - (d 1 0) ^ 2 * hv1
  have e2 : d 0 1 * d 1 1 * (2 * Q.a * p * q + Q.b * (p * s + q * r) + 2 * Q.c * r * s) = 0 := by
    linear_combination hw1 - (d 0 1) ^ 2 * hv0 - (d 1 1) ^ 2 * hv1
  have e3 : 2 * Q.a * (p * d 0 0 + q * d 1 0) * (p * d 0 1 + q * d 1 1) +
      Q.b * ((p * d 0 0 + q * d 1 0) * (r * d 0 1 + s * d 1 1) + (p * d 0 1 + q * d 1 1) * (r * d 0 0 + s * d 1 0)) +
      2 * Q.c * (r * d 0 0 + s * d 1 0) * (r * d 0 1 + s * d 1 1) =
      (2 * Q.a * p * q + Q.b * (p * s + q * r) + 2 * Q.c * r * s) * (d 0 0 * d 1 1 + d 1 0 * d 0 1) +
        2 * d 0 0 * d 0 1 * (Q.a * p ^ 2 + Q.b * p * r + Q.c * r ^ 2) +
        2 * d 1 0 * d 1 1 * (Q.a * q ^ 2 + Q.b * q * s + Q.c * s ^ 2) := by ring
  rw [e3, hv0, hv1] at hP'
  simp only [mul_zero, add_zero] at hP'
  have hP2 : 0 < 2 * Q.a * p * q + Q.b * (p * s + q * r) + 2 * Q.c * r * s := hP
  have h10 : d 0 0 * d 1 0 = 0 := (mul_eq_zero.1 e1).resolve_right hP2.ne'
  have h01 : d 0 1 * d 1 1 = 0 := (mul_eq_zero.1 e2).resolve_right hP2.ne'
  have hd10 : d 1 0 = 0 := by
    rcases mul_eq_zero.1 h10 with h | h
    · exfalso
      rw [h] at hP' hdet2
      have h3 : d 1 0 * d 0 1 < 0 := by nlinarith
      have := mul_neg_of_pos_of_neg hP2 h3
      nlinarith
    · exact h
  have hd01 : d 0 1 = 0 := by
    rcases mul_eq_zero.1 h01 with h | h
    · exact h
    · exfalso
      rw [h, hd10] at hdet2
      simp at hdet2
  rw [hgd, Matrix.GeneralLinearGroup.geodesicIntegral_mul_of_diagonal g hd10 hd01 hdet0]

private theorem hasDerivAt_mobius_axis (a b c d : ℝ) (s : ℝ)
    (hden : (c : ℂ) * (Complex.I * (Real.exp s : ℝ)) + d ≠ 0) :
    HasDerivAt (fun s : ℝ => ((a : ℂ) * (Complex.I * (Real.exp s : ℝ)) + b) /
        ((c : ℂ) * (Complex.I * (Real.exp s : ℝ)) + d))
      ((Complex.I * (Real.exp s : ℝ)) * ((a * d - b * c : ℝ) : ℂ) /
        ((c : ℂ) * (Complex.I * (Real.exp s : ℝ)) + d) ^ 2) s := by
  have hτ : HasDerivAt (fun s : ℝ => Complex.I * (Real.exp s : ℝ)) (Complex.I * (Real.exp s : ℝ)) s := by
    have := ((Real.hasDerivAt_exp s).ofReal_comp).const_mul Complex.I
    simpa using this
  have h := (((hτ.const_mul (a : ℂ)).add_const (b : ℂ)).div ((hτ.const_mul (c : ℂ)).add_const (d : ℂ)) hden)
  convert h using 1
  push_cast
  ring

/-- The pointwise form of the substitution `t = e^s` in the geodesic integral. -/
private theorem axis_integrand (g : GL (Fin 2) ℚ) (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det)
    (Q : BinQF) {n : ℕ} (hn : 0 < n) (hQ : Q.disc = (n : ℤ) ^ 2)
    (hz : ∀ s : ℝ, (((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g) • axisPt s : ℍ) : ℂ) = Q.geodesic s)
    (F : ℍ → ℂ) (s : ℝ) :
    Complex.I * (Real.exp s • UpperHalfPlane.resToImagAxis (F ∣[(2 : ℤ)] g) (Real.exp s)) =
      F (Q.geodesicH (by rw [hQ]; positivity) s) * (Q.evalC (Q.geodesic s) / (n : ℂ)) := by
  have hQpos : 0 < Q.disc := by rw [hQ]; positivity
  set ĝ : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g with hĝ
  have hĝdet : 0 < (ĝ : Matrix (Fin 2) (Fin 2) ℝ).det := ModularForm.det_map_ratCast_pos hdet
  have hĝdet' : 0 < ĝ.det.val := by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hĝdet
  have hzs : ĝ • axisPt s = Q.geodesicH hQpos s := UpperHalfPlane.ext (hz s)
  have hdenom : (ĝ 1 0 : ℂ) * (Complex.I * (Real.exp s : ℝ)) + ĝ 1 1 ≠ 0 :=
    UpperHalfPlane.denom_ne_zero ĝ (axisPt s)
  have hfun : Q.geodesic = fun s : ℝ => ((ĝ 0 0 : ℂ) * (Complex.I * (Real.exp s : ℝ)) + ĝ 0 1) /
      ((ĝ 1 0 : ℂ) * (Complex.I * (Real.exp s : ℝ)) + ĝ 1 1) := by
    funext s
    rw [← hz s, UpperHalfPlane.coe_smul_of_det_pos hĝdet', UpperHalfPlane.num, UpperHalfPlane.denom,
      coe_axisPt]
  have hder := hasDerivAt_mobius_axis (ĝ 0 0) (ĝ 0 1) (ĝ 1 0) (ĝ 1 1) s hdenom
  rw [← hfun] at hder
  have hder2 := hasDerivAt_geodesic Q hQpos s
  rw [sqrt_disc_eq Q hQ] at hder2
  have hkey := hder.unique hder2
  have hdetc : ((ĝ 0 0 * ĝ 1 1 - ĝ 0 1 * ĝ 1 0 : ℝ) : ℂ) = (|ĝ.det.val| : ℝ) := by
    rw [abs_of_pos hĝdet', Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  rw [hdetc] at hkey
  rw [Complex.real_smul, UpperHalfPlane.resToImagAxis_of_pos _ (Real.exp_pos s)]
  change Complex.I * (((Real.exp s : ℝ) : ℂ) * (F ∣[(2 : ℤ)] g) (axisPt s)) = _
  rw [ModularForm.rat_slash_apply_of_det_pos 2 hdet, ← hĝ, hzs]
  have hden2 : UpperHalfPlane.denom ĝ (axisPt s) = (ĝ 1 0 : ℂ) * (Complex.I * (Real.exp s : ℝ)) + ĝ 1 1 := by
    rw [UpperHalfPlane.denom, coe_axisPt]
  rw [hden2, Complex.ofReal_natCast] at *
  rw [← hkey]
  have e1 : ((2 : ℤ) - 1) = 1 := by norm_num
  rw [e1, zpow_one, zpow_neg, zpow_ofNat]
  ring

/-- **The cycle integral at a square discriminant is the geodesic integral along a frame.** -/
theorem cycleIntegral_eq_geodesicIntegral {k : ℕ} (hk : 1 ≤ k) (G : ℍ → ℂ) (Q : BinQF) {n : ℕ} (hn : 0 < n)
    (hQ : Q.disc = (n : ℤ) ^ 2) {g : GL (Fin 2) ℚ} (hg : Q.IsFrame g) :
    cycleIntegral k G Q = g.geodesicIntegral (cycleIntegrand k G Q) := by
  obtain ⟨g0, hg0, hz⟩ := exists_frame_geodesic Q hn hQ
  rw [geodesicIntegral_isFrame_eq hg hg0]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hQpos : 0 < Q.disc := by rw [hQ]; positivity
  have hsq : IsSquare Q.disc := ⟨n, by rw [hQ]; ring⟩
  rw [cycleIntegral, dif_pos hQpos, if_pos hsq, sqrt_disc_eq Q hQ, Matrix.GeneralLinearGroup.geodesicIntegral_def,
    ← MeasureTheory.integral_comp_exp (UpperHalfPlane.resToImagAxis
      (cycleIntegrand (m + 1) G Q ∣[(2 : ℤ)] g0)),
    ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  congr 1
  funext s
  rw [axis_integrand g0 hg0.1 Q hn hQ hz (cycleIntegrand (m + 1) G Q) s, Complex.ofReal_natCast]
  simp only [cycleIntegrand, Nat.add_sub_cancel, pow_succ]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : ∀ h, ((Q.geodesicH h s : ℍ) : ℂ) = Q.geodesic s := fun _ => rfl
  rw [hc]
  field_simp

/-- The integrand of `Q ∘ γ` is the weight-two slash of the integrand of `Q` by `γ`. -/
private theorem cycleIntegrand_comp {k : ℕ} (hk : 1 ≤ k) (G : CuspForm 𝒮ℒ (2 * k : ℕ)) (Q : BinQF)
    (γ : SL(2, ℤ)) :
    cycleIntegrand k G (Q.comp γ) = cycleIntegrand k G Q ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℚ γ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  funext τ
  rw [ModularForm.rat_slash_mapGL, ← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← ModularForm.SL_slash,
    ModularForm.SL_slash_apply]
  have hd := denom_ne_zero_SL γ τ
  have hden : UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ = (γ 1 0 : ℂ) * τ + γ 1 1 := by
    simp [UpperHalfPlane.denom]
  simp only [cycleIntegrand, Nat.add_sub_cancel]
  rw [hden, cuspForm_transform G γ τ, coe_smul_SL, evalC_smul Q (γ : Matrix (Fin 2) (Fin 2) ℤ) hd,
    zpow_neg, zpow_ofNat, div_pow]
  have e : ∀ D : ℂ, D ^ (2 * (m + 1)) = (D ^ 2) ^ m * D ^ 2 := fun D => by ring
  rw [e]
  generalize ((γ 1 0 : ℂ) * τ + γ 1 1) = D at hd ⊢
  field_simp

private theorem isFrame_comp (Q : BinQF) (γ : SL(2, ℤ)) {g : GL (Fin 2) ℚ} (hg : Q.IsFrame g) :
    (Q.comp γ).IsFrame (Matrix.SpecialLinearGroup.mapGL ℚ γ⁻¹ * g) := by
  obtain ⟨hdg, hv0, hv1, hP⟩ := hg
  set g' : GL (Fin 2) ℚ := Matrix.SpecialLinearGroup.mapGL ℚ γ⁻¹ * g with hg'
  have hgg : g = Matrix.SpecialLinearGroup.mapGL ℚ γ * g' := by
    rw [hg', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hm : ∀ i j, g i j = (γ i 0 : ℚ) * g' 0 j + (γ i 1 : ℚ) * g' 1 j := by
    intro i j
    rw [hgg]
    show ((Matrix.SpecialLinearGroup.mapGL ℚ γ * g' : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j = _
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.map_apply]
  have hdet1 : ((Matrix.SpecialLinearGroup.mapGL ℚ γ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.det_mapGL, Units.val_one]
  have key : ∀ x y, (Q.comp γ).valQ x y =
      Q.valQ ((γ 0 0 : ℚ) * x + γ 0 1 * y) ((γ 1 0 : ℚ) * x + γ 1 1 * y) := by
    intro x y; simp only [valQ, comp, val]; push_cast; ring
  have key2 : ∀ x y x' y', (Q.comp γ).polQ x y x' y' =
      Q.polQ ((γ 0 0 : ℚ) * x + γ 0 1 * y) ((γ 1 0 : ℚ) * x + γ 1 1 * y)
        ((γ 0 0 : ℚ) * x' + γ 0 1 * y') ((γ 1 0 : ℚ) * x' + γ 1 1 * y') := by
    intro x y x' y'; simp only [polQ, comp, val]; push_cast; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hg', Units.val_mul, Matrix.det_mul, hdet1, one_mul]; exact hdg
  · rw [key, ← hm 0 0, ← hm 1 0]; exact hv0
  · rw [key, ← hm 0 1, ← hm 1 1]; exact hv1
  · rw [key2, ← hm 0 0, ← hm 1 0, ← hm 0 1, ← hm 1 1]; exact hP

/-- **Class invariance of the cycle integrals at square discriminants**: for $G \in S_{2k}(\mathrm{SL}_2(\mathbb Z))$, $k \ge 1$,
and $\gamma \in \mathrm{SL}_2(\mathbb Z)$, $\int_{C_{Q\circ\gamma}} G(z)\,(Q\circ\gamma)(z,1)^{k-1}dz = \int_{C_Q} G(z)\,Q(z,1)^{k-1}dz$. -/
theorem cycleIntegral_comp_SL {k : ℕ} (hk : 1 ≤ k) (G : CuspForm 𝒮ℒ (2 * k : ℕ)) (Q : BinQF) {n : ℕ}
    (hn : 0 < n) (hQ : Q.disc = (n : ℤ) ^ 2) (γ : SL(2, ℤ)) :
    cycleIntegral k G (Q.comp γ) = cycleIntegral k G Q := by
  obtain ⟨g, hg⟩ := exists_isFrame Q hn hQ
  have hQ' : (Q.comp γ).disc = (n : ℤ) ^ 2 := by rw [disc_comp_SL, hQ]
  rw [cycleIntegral_eq_geodesicIntegral hk G (Q.comp γ) hn hQ' (isFrame_comp Q γ hg),
    cycleIntegral_eq_geodesicIntegral hk G Q hn hQ hg,
    Matrix.GeneralLinearGroup.geodesicIntegral_mul]
  congr 1
  have := cycleIntegrand_comp hk G (Q.comp γ) γ⁻¹
  rw [← this, ← comp_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, comp_one]

end BinQF

end ModularFormsKB.HalfIntegral
