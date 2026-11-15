/-
# The theta multiplier on the coset representatives of $T(p^2)$

Let $p \nmid 4N$ be prime, $\alpha = \mathrm{diag}(1, p^2)$ and
$f_\alpha(\tau) = f(\tau/p^2)$ (`fAlpha`). With the weight $k + \tfrac12$ slash action of the theta multiplier
(`thetaMultiplierSystem.slash`), for $f$ satisfying the transformation law on $\Gamma_0(4N)$:
* `slash_T_pow`: $f_\alpha|_{T^b}(\tau) = f((\tau+b)/p^2)$, since $j(T^b,\tau) = 1$;
* `slash_repZero`: for $r_0 = \begin{pmatrix}p^2 & y\\ 4N & w\end{pmatrix}$, $\alpha r_0 = \delta_0\,\mathrm{diag}(p^2, 1)$ with
  $\delta_0 = \begin{pmatrix}1 & y\\ 4N & p^2 w\end{pmatrix}$ and $j(\delta_0, p^2\tau) = p\,j(r_0,\tau)$, so
  $f_\alpha|_{r_0}(\tau) = \chi(p)^2 p^{2k+1} f(p^2\tau)$;
* `slash_repMid`: for $r_i = \begin{pmatrix}pA & 4iA + pB\\ -4N & 1\end{pmatrix}$ with $A(p + 16Ni) + 4NpB = 1$,
  $\alpha r_i = \delta_i\beta_i$ with $\delta_i = \begin{pmatrix}A & B\\ -4Np & p + 16Ni\end{pmatrix}$,
  $\beta_i = \begin{pmatrix}p & 4i\\ 0 & p\end{pmatrix}$, and $j(\delta_i, \beta_i\tau) = \varepsilon_p^{-1}\big(\frac ip\big)\sqrt p\,j(r_i,\tau)$
  (quadratic reciprocity, and $p + 16Ni \equiv p \bmod 16N$), so
  $f_\alpha|_{r_i}(\tau) = \chi(p)\big(\varepsilon_p^{-1}\sqrt p\big)^{2k+1}\big(\frac ip\big) f(\tau + 4i/p)$;
* `slash_conj`: $f_\alpha|_\delta = f_\alpha$ for $\delta \in \Gamma_0(4N)$ with $p^2 \mid b$, since
  $\delta' = \begin{pmatrix}a & b/p^2\\ p^2c & d\end{pmatrix}$ satisfies $\delta'(\tau/p^2) = (\delta\tau)/p^2$ and
  $j(\delta', \tau/p^2) = j(\delta,\tau)$.

This is the metaplectic computation behind Shimura 1973 `shimura1973`, §1 and Thm. 1.7 [unverified], done with the
explicit multiplier $j(\gamma,\tau) = \varepsilon_d^{-1}\big(\frac cd\big)(c\tau+d)^{1/2}$ (`thetaMult`).

**Index shift.** Matrix entries are 0-based: $c = \gamma_{1,0}$, $d = \gamma_{1,1}$.
-/
import ModularFormsKB.HalfIntegral.HeckeOp

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- The representative $r_0 = \begin{pmatrix}p^2 & y\\ 4N & w\end{pmatrix}$, for $p^2w - 4Ny = 1$. -/
def repZero (N : ℕ) (p : ℕ+) (y w : ℤ) (h : (p : ℤ) ^ 2 * w - 4 * N * y = 1) : SL(2, ℤ) :=
  ⟨!![(p : ℤ) ^ 2, y; 4 * N, w], by rw [Matrix.det_fin_two_of]; linarith⟩

/-- The representative $r_i = \begin{pmatrix}pA & 4iA + pB\\ -4N & 1\end{pmatrix}$, for $A(p + 16Ni) + 4NpB = 1$. -/
def repMid (N : ℕ) (p : ℕ+) (i A B : ℤ) (h : A * (p + 16 * N * i) + 4 * N * p * B = 1) : SL(2, ℤ) :=
  ⟨!![(p : ℤ) * A, 4 * i * A + p * B; -4 * N, 1], by rw [Matrix.det_fin_two_of]; linarith⟩

private lemma coe_smul_sl (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ • τ : ℍ) : ℂ) = ((γ 0 0 : ℂ) * τ + γ 0 1) / ((γ 1 0 : ℂ) * τ + γ 1 1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

private lemma shimuraSym_sq_mul (P : ℕ) (hP0 : 0 < P) (c d : ℤ) (h : Int.gcd P d = 1) :
    shimuraSym ((P : ℤ) ^ 2 * c) d = shimuraSym c d := by
  unfold shimuraSym
  have hg : Int.gcd P (d.natAbs : ℕ) = 1 := by
    unfold Int.gcd at h ⊢
    simpa only [Int.natAbs_natCast] using h
  have hP : (0 : ℤ) < (P : ℤ) ^ 2 := by positivity
  have hneg : ((P : ℤ) ^ 2 * c < 0 ∧ d < 0) ↔ (c < 0 ∧ d < 0) := by
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, h2⟩ <;> nlinarith
  have hj : jacobiSym ((P : ℤ) ^ 2 * c) d.natAbs = jacobiSym c d.natAbs := by
    rw [jacobiSym.mul_left, jacobiSym.sq_one' hg, one_mul]
  rw [if_congr hneg rfl rfl, hj]

private lemma chi_ne_zero' {N : ℕ} {γ : SL(2, ℤ)} (h : γ ∈ Gamma0 (4 * N)) (χ : DirichletCharacter ℂ (4 * N)) :
    χ (γ 1 1 : ZMod (4 * N)) ≠ 0 := by
  have hc : ((γ 1 0 : ℤ) : ZMod (4 * N)) = 0 := by rwa [Gamma0_mem] at h
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have h1 : ((γ 0 0 : ℤ) : ZMod (4 * N)) * (γ 1 1 : ℤ) = 1 := by
    have := congrArg (fun x : ℤ ↦ (x : ZMod (4 * N))) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at this
    rw [hc] at this
    simpa using this
  have hu : IsUnit ((γ 1 1 : ℤ) : ZMod (4 * N)) :=
    IsUnit.of_mul_eq_one ((γ 0 0 : ℤ) : ZMod (4 * N)) (by rw [← h1]; ring)
  exact (hu.map χ).ne_zero

private lemma thetaMult_ne_zero {N : ℕ} {γ : SL(2, ℤ)} (h : γ ∈ Gamma0 (4 * N)) (τ : ℍ) :
    thetaMult γ τ ≠ 0 := by
  have h4 : γ ∈ Gamma0 4 := by
    rw [Gamma0_mem] at *
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at *
    exact dvd_trans (by push_cast; exact dvd_mul_right (4 : ℤ) N) h
  exact thetaMultiplierSystem.ne_zero γ h4 τ

private lemma cpow_half_sq_mul_real (a : ℝ) (ha : 0 < a) (X : ℂ) (hX : X ≠ 0) :
    (((a : ℂ) ^ 2 * X)) ^ (1 / 2 : ℂ) = (a : ℂ) * X ^ (1 / 2 : ℂ) := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h2 : ((a : ℂ) ^ 2) = (((a : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hX2 : ((a : ℂ) ^ 2 * X) ≠ 0 := mul_ne_zero (pow_ne_zero 2 ha0) hX
  rw [cpow_def_of_ne_zero hX2, cpow_def_of_ne_zero hX, h2, Complex.log_ofReal_mul (by positivity) hX]
  have hl : ((Real.log ((a : ℝ) ^ 2) : ℝ) : ℂ) = 2 * Complex.log (a : ℂ) := by
    rw [Real.log_pow, Complex.ofReal_mul, Complex.ofReal_log ha.le]
    push_cast; ring
  have : (((Real.log ((a : ℝ) ^ 2) : ℝ) : ℂ) + Complex.log X) * (1 / 2) =
      Complex.log (a : ℂ) + Complex.log X * (1 / 2) := by
    rw [hl]; ring
  rw [this, Complex.exp_add, Complex.exp_log ha0]

private lemma cpow_half_sq_mul (a : ℕ) (ha : 0 < a) (X : ℂ) (hX : X ≠ 0) :
    (((a : ℂ) ^ 2 * X)) ^ (1 / 2 : ℂ) = (a : ℂ) * X ^ (1 / 2 : ℂ) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h2 : ((a : ℂ) ^ 2) = (((a : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hX2 : ((a : ℂ) ^ 2 * X) ≠ 0 := mul_ne_zero (pow_ne_zero 2 ha0) hX
  rw [cpow_def_of_ne_zero hX2, cpow_def_of_ne_zero hX, h2, Complex.log_ofReal_mul (by positivity) hX]
  have hl : ((Real.log ((a : ℝ) ^ 2) : ℝ) : ℂ) = 2 * Complex.log (a : ℂ) := by
    rw [Real.log_pow, Complex.ofReal_mul, Complex.ofReal_log ha'.le]
    push_cast; ring
  have : (((Real.log ((a : ℝ) ^ 2) : ℝ) : ℂ) + Complex.log X) * (1 / 2) =
      Complex.log (a : ℂ) + Complex.log X * (1 / 2) := by
    rw [hl]; ring
  rw [this, Complex.exp_add, Complex.exp_log ha0]

private lemma cpow_half_mul_sqrt (a : ℕ) (ha : 0 < a) (X : ℂ) (hX : X ≠ 0) :
    ((a : ℂ) * X) ^ (1 / 2 : ℂ) = (Real.sqrt a : ℂ) * X ^ (1 / 2 : ℂ) := by
  have h := cpow_half_sq_mul_real (Real.sqrt a) (Real.sqrt_pos.mpr (by exact_mod_cast ha)) X hX
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)] at h
  simpa using h

private lemma jacobi_mid (N i p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ 4 * N) :
    jacobiSym (-4 * (N : ℤ) * (p : ℤ)) (p + 16 * N * i) = jacobiSym (i : ℤ) p := by
  have hp2 : p ≠ 2 := by rintro rfl; exact hpN ⟨2 * N, by ring⟩
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hDo : Odd (p + 16 * N * i) := by
    obtain ⟨m, hm⟩ := hpo
    exact ⟨m + 8 * N * i, by rw [hm]; ring⟩
  have hcopN : Int.gcd (N : ℤ) p = 1 := by
    have : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => hpN (h.mul_left 4))
    rw [Int.gcd_natCast_natCast]; exact this.symm
  have hJN : jacobiSym (N : ℤ) p ^ 2 = 1 := jacobiSym.sq_one hcopN
  have h1 : jacobiSym (-4 * (N : ℤ)) (p + 16 * N * i) = jacobiSym (-4 * (N : ℤ)) p := by
    apply jacobiSym_congr_of_dvd _ hDo hpo
    have : ((-4 * (N : ℤ)).natAbs) = 4 * N := by omega
    rw [this]
    exact ⟨-i, by push_cast; ring⟩
  have h2 : jacobiSym (-4 * (N : ℤ)) p = ZMod.χ₄ (p : ZMod 4) * jacobiSym N p := by
    have : (-4 * (N : ℤ)) = (-1) * 4 * N := by ring
    rw [this, jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.at_neg_one hpo, jacobiSym.at_four hpo]
    ring
  have h3 : jacobiSym (((p + 16 * N * i : ℕ)) : ℤ) p = jacobiSym N p * jacobiSym i p := by
    rw [jacobiSym.mod_left' (a₂ := 16 * (N : ℤ) * i) (by push_cast; simp)]
    have : (16 * (N : ℤ) * i) = 4 * 4 * N * i := by ring
    rw [this, jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.at_four hpo]
    ring
  have hmod : (p + 16 * N * i) % 4 = p % 4 := by
    have : p + 16 * N * i = p + 4 * (4 * N * i) := by ring
    rw [this, Nat.add_mul_mod_self_left]
  rw [jacobiSym.mul_left, h1, h2]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hpo) with h4 | h4
  · rw [jacobiSym.quadratic_reciprocity_one_mod_four h4 hDo, h3, ZMod.χ₄_nat_one_mod_four h4]
    linear_combination (jacobiSym (i : ℤ) p) * hJN
  · rw [jacobiSym.quadratic_reciprocity_three_mod_four h4 (by omega), h3, ZMod.χ₄_nat_three_mod_four h4]
    linear_combination (jacobiSym (i : ℤ) p) * hJN

variable (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (p : ℕ+)

theorem slash_T_pow (f : ℍ → ℂ) (b : ℕ) (τ : ℍ) :
    thetaMultiplierSystem.slash k N χ (ModularGroup.T ^ (b : ℤ)) (fAlpha p f) τ = f (affPt 1 (p ^ 2) b τ) := by
  have h10 : (ModularGroup.T ^ (b : ℤ) : SL(2, ℤ)) 1 0 = 0 := by
    rw [ModularGroup.coe_T_zpow]; simp
  have h11 : (ModularGroup.T ^ (b : ℤ) : SL(2, ℤ)) 1 1 = 1 := by
    rw [ModularGroup.coe_T_zpow]; simp
  have h00 : (ModularGroup.T ^ (b : ℤ) : SL(2, ℤ)) 0 0 = 1 := by
    rw [ModularGroup.coe_T_zpow]; simp
  have h01 : (ModularGroup.T ^ (b : ℤ) : SL(2, ℤ)) 0 1 = b := by
    rw [ModularGroup.coe_T_zpow]; simp
  have hpt : (affPt 1 (p ^ 2) 0 (ModularGroup.T ^ (b : ℤ) • τ)) = affPt 1 (p ^ 2) b τ := by
    apply UpperHalfPlane.ext
    rw [coe_affPt, coe_affPt, coe_smul_sl, h00, h01, h10, h11]
    simp
  simp only [MultiplierSystem.slash, thetaMultiplierSystem_j, thetaMult, h10, h11, thetaMultCD_zero_one, fAlpha, hpt]
  simp

theorem slash_repZero (hp : (p : ℕ).Prime) (hpN : ¬ (p : ℕ) ∣ 4 * N) {f : ℍ → ℂ}
    (hf : thetaMultiplierSystem.Transforms k N χ f) (y w : ℤ) (h : (p : ℤ) ^ 2 * w - 4 * N * y = 1) (τ : ℍ) :
    thetaMultiplierSystem.slash k N χ (repZero N p y w h) (fAlpha p f) τ =
      χ (p : ℕ) ^ 2 * ((p : ℕ) : ℂ) ^ (2 * k + 1) * f (affPt (p ^ 2) 1 0 τ) := by
  have hN : N ≠ 0 := by rintro rfl; exact hpN (by simp)
  have hodd : Odd (p : ℕ) := by
    rcases hp.eq_two_or_odd' with h2 | h2
    · exfalso; apply hpN; rw [h2]; exact ⟨2 * N, by ring⟩
    · exact h2
  obtain ⟨m, hm⟩ := hodd
  have hsq : (p : ℤ) ^ 2 = 1 + 4 * ((m : ℤ) * (m + 1)) := by
    have : ((p : ℕ) : ℤ) = 2 * m + 1 := by exact_mod_cast hm
    rw [this]; ring
  have hw0 : w ≠ 0 := by
    rintro rfl
    have : (4 : ℤ) ∣ 1 := ⟨-(N * y), by linarith⟩
    omega
  set r0 := repZero N p y w h with hr0
  let δ0 : SL(2, ℤ) := ⟨!![1, y; 4 * N, (p : ℤ) ^ 2 * w], by
    rw [Matrix.det_fin_two_of]; linarith⟩
  have hδ0 : δ0 ∈ Gamma0 (4 * N) := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    change ((4 * N : ℕ) : ℤ) ∣ (4 : ℤ) * N
    push_cast; exact dvd_refl _
  have e00 : (δ0 0 0 : ℤ) = 1 := rfl
  have e01 : (δ0 0 1 : ℤ) = y := rfl
  have e10 : (δ0 1 0 : ℤ) = 4 * N := rfl
  have e11 : (δ0 1 1 : ℤ) = (p : ℤ) ^ 2 * w := rfl
  have r00 : (r0 0 0 : ℤ) = (p : ℤ) ^ 2 := rfl
  have r01 : (r0 0 1 : ℤ) = y := rfl
  have r10 : (r0 1 0 : ℤ) = 4 * N := rfl
  have r11 : (r0 1 1 : ℤ) = w := rfl
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.ne_zero
  have hden : (4 * (N : ℂ)) * τ + w ≠ 0 := by
    have := cuspDenom_ne_zero r0 τ
    unfold cuspDenom at this
    rw [r10, r11] at this
    exact_mod_cast this
  have hden2 : ((δ0 1 0 : ℤ) : ℂ) * (affPt (p ^ 2) 1 0 τ : ℂ) + (δ0 1 1 : ℤ) =
      ((p : ℕ) : ℂ) ^ 2 * (4 * (N : ℂ) * τ + w) := by
    rw [e10, e11, coe_affPt]
    push_cast
    ring
  have hpt : affPt 1 (p ^ 2) 0 (r0 • τ) = δ0 • affPt (p ^ 2) 1 0 τ := by
    apply UpperHalfPlane.ext
    rw [coe_affPt, coe_smul_sl, coe_smul_sl, hden2, e00, e01, coe_affPt, r00, r01, r10, r11]
    push_cast
    field_simp
    ring
  have hcop : Int.gcd ((4 * N : ℕ) : ℤ) ((p : ℕ) : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN).symm
  have hsym : shimuraSym (δ0 1 0) (δ0 1 1) = shimuraSym (r0 1 0) (r0 1 1) := by
    rw [e10, e11, r10, r11]
    have hN4 : ¬ ((4 : ℤ) * N < 0) := not_lt.mpr (by positivity)
    unfold shimuraSym
    simp only [hN4, false_and, ite_false]
    have hp0' : ((p : ℕ) ^ 2) ≠ 0 := pow_ne_zero 2 p.ne_zero
    have hw0' : w.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hw0
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast, jacobiSym.mul_right' _ hp0' hw0',
      jacobiSym.pow_right]
    have : jacobiSym (4 * N) (p : ℕ) ^ 2 = 1 := by
      apply jacobiSym.sq_one
      push_cast at hcop
      exact hcop
    rw [this, one_mul]
  have hjj : thetaMult δ0 (affPt (p ^ 2) 1 0 τ) = ((p : ℕ) : ℂ) * thetaMult r0 τ := by
    unfold thetaMult thetaMultCD
    rw [hden2, hsym, r10, r11, e11]
    have : epsD ((p : ℤ) ^ 2 * w) = epsD w := by
      unfold epsD
      rw [hsq]
      have : (1 + 4 * ((m : ℤ) * (m + 1))) * w % 4 = w % 4 := by
        have : (1 + 4 * ((m : ℤ) * (m + 1))) * w = w + 4 * ((m : ℤ) * (m + 1) * w) := by ring
        rw [this]; omega
      rw [this]
    rw [this, cpow_half_sq_mul _ p.pos _ hden]
    push_cast
    ring
  have key := hf δ0 hδ0 (affPt (p ^ 2) 1 0 τ)
  simp only [MultiplierSystem.slash, thetaMultiplierSystem_j, fAlpha, hpt, key, hjj, e11, r11]
  have hr : r0 ∈ Gamma0 (4 * N) := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    change ((4 * N : ℕ) : ℤ) ∣ (4 : ℤ) * N
    push_cast; exact dvd_refl _
  have h1 := chi_ne_zero' hr χ
  rw [r11] at h1
  have h2 := thetaMult_ne_zero hr τ
  have h3 : (((p ^ 2 * w : ℤ)) : ZMod (4 * N)) = ((p : ℕ) : ZMod (4 * N)) ^ 2 * (w : ZMod (4 * N)) := by
    push_cast; ring
  rw [h3, map_mul, map_pow, mul_pow]
  field_simp

theorem slash_repMid (hp : (p : ℕ).Prime) (hpN : ¬ (p : ℕ) ∣ 4 * N) {f : ℍ → ℂ}
    (hf : thetaMultiplierSystem.Transforms k N χ f) (i : ℕ) (hi : ¬ (p : ℕ) ∣ i) (A B : ℤ)
    (h : A * (p + 16 * N * i) + 4 * N * p * B = 1) (τ : ℍ) :
    thetaMultiplierSystem.slash k N χ (repMid N p i A B h) (fAlpha p f) τ =
      χ (p : ℕ) * ((epsD (p : ℕ))⁻¹ * (Real.sqrt (p : ℕ) : ℂ)) ^ (2 * k + 1) * (jacobiSym i p : ℂ) *
        f (affPt p p (4 * i) τ) := by
  have hp2 : (p : ℕ) ≠ 2 := by intro h2; exact hpN (by rw [h2]; exact ⟨2 * N, by ring⟩)
  have hpo : Odd (p : ℕ) := hp.odd_of_ne_two hp2
  have hN : N ≠ 0 := by rintro rfl; exact hpN (by simp)
  set r := repMid N p i A B h with hr0
  have hdetδ : A * ((p : ℤ) + 16 * N * i) - B * (-4 * N * p) = 1 := by linarith
  let δ : SL(2, ℤ) := ⟨!![A, B; -4 * N * p, (p : ℤ) + 16 * N * i], by
    rw [Matrix.det_fin_two_of]; linarith⟩
  have hδ : δ ∈ Gamma0 (4 * N) := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    change ((4 * N : ℕ) : ℤ) ∣ -4 * (N : ℤ) * p
    exact ⟨-p, by push_cast; ring⟩
  have e00 : (δ 0 0 : ℤ) = A := rfl
  have e01 : (δ 0 1 : ℤ) = B := rfl
  have e10 : (δ 1 0 : ℤ) = -4 * N * p := rfl
  have e11 : (δ 1 1 : ℤ) = (p : ℤ) + 16 * N * i := rfl
  have r00 : (r 0 0 : ℤ) = p * A := rfl
  have r01 : (r 0 1 : ℤ) = 4 * i * A + p * B := rfl
  have r10 : (r 1 0 : ℤ) = -4 * N := rfl
  have r11 : (r 1 1 : ℤ) = 1 := rfl
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.ne_zero
  have hden : -4 * (N : ℂ) * τ + 1 ≠ 0 := by
    have := cuspDenom_ne_zero r τ
    unfold cuspDenom at this
    rw [r10, r11] at this
    exact_mod_cast this
  have hden2 : ((δ 1 0 : ℤ) : ℂ) * (affPt p p (4 * i) τ : ℂ) + (δ 1 1 : ℤ) =
      ((p : ℕ) : ℂ) * (-4 * (N : ℂ) * τ + 1) := by
    rw [e10, e11, coe_affPt]
    push_cast
    field_simp
    ring
  have hpt : affPt 1 (p ^ 2) 0 (r • τ) = δ • affPt p p (4 * i) τ := by
    apply UpperHalfPlane.ext
    rw [coe_affPt, coe_smul_sl, coe_smul_sl, hden2, e00, e01, coe_affPt, r00, r01, r10, r11]
    push_cast
    field_simp
    ring
  have hjr : thetaMult r τ = (-4 * (N : ℂ) * τ + 1) ^ (1 / 2 : ℂ) := by
    unfold thetaMult thetaMultCD
    rw [r10, r11]
    have : epsD 1 = 1 := by simp [epsD]
    have h1 : shimuraSym (-4 * (N : ℤ)) 1 = 1 := by simp [shimuraSym]
    rw [this, h1]
    push_cast
    simp
  have hcopi : Int.gcd (i : ℤ) ((p : ℕ) : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hi).symm
  have hsym : shimuraSym (δ 1 0) (δ 1 1) = jacobiSym (i : ℤ) p := by
    rw [e10, e11]
    unfold shimuraSym
    have hD : ¬ ((p : ℤ) + 16 * N * i < 0) := not_lt.mpr (by positivity)
    simp only [hD, and_false, ite_false]
    have : ((p : ℤ) + 16 * N * i).natAbs = (p : ℕ) + 16 * N * i := by
      have e : ((p : ℕ) : ℤ) + 16 * N * i = (((p : ℕ) + 16 * N * i : ℕ) : ℤ) := by push_cast; ring
      rw [e, Int.natAbs_natCast]
    rw [this]
    exact jacobi_mid N i p hp hpN
  have heps : epsD ((p : ℤ) + 16 * N * i) = epsD (p : ℕ) := by
    have := epsD_add_right (c := 16 * N * i) (d := ((p : ℕ) : ℤ)) ⟨4 * N * i, by ring⟩
    exact this
  have hjj : thetaMult δ (affPt p p (4 * i) τ) =
      (epsD (p : ℕ))⁻¹ * (jacobiSym (i : ℤ) p : ℂ) * (Real.sqrt (p : ℕ) : ℂ) * thetaMult r τ := by
    rw [hjr]
    unfold thetaMult thetaMultCD
    rw [hden2, hsym, e11, heps, cpow_half_mul_sqrt _ p.pos _ hden]
    ring
  have hS : (jacobiSym (i : ℤ) p : ℂ) ^ (2 * k + 1) = (jacobiSym (i : ℤ) p : ℂ) := by
    rcases jacobiSym.eq_one_or_neg_one hcopi with h1 | h1
    · simp [h1]
    · rw [h1]; push_cast; exact Odd.neg_one_pow ⟨k, rfl⟩
  have hD : ((δ 1 1 : ℤ) : ZMod (4 * N)) = ((p : ℕ) : ZMod (4 * N)) := by
    rw [e11]
    have : ((4 * N : ℕ) : ZMod (4 * N)) = 0 := ZMod.natCast_self _
    push_cast
    have h4 : (4 : ZMod (4 * N)) * N = 0 := by exact_mod_cast this
    linear_combination (4 * (i : ZMod (4 * N))) * h4
  have key := hf δ hδ (affPt p p (4 * i) τ)
  have hrm : r ∈ Gamma0 (4 * N) := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    change ((4 * N : ℕ) : ℤ) ∣ -4 * (N : ℤ)
    exact ⟨-1, by push_cast; ring⟩
  have h2 := thetaMult_ne_zero hrm τ
  simp only [MultiplierSystem.slash, thetaMultiplierSystem_j, fAlpha, hpt, key, hjj, r11, hD]
  rw [mul_pow, mul_pow, mul_pow, hS]
  push_cast
  simp only [map_one, inv_one, one_mul]
  field_simp
  simp only [div_eq_mul_inv, mul_pow, one_pow, inv_pow]
  ring

theorem slash_conj (hp : (p : ℕ).Prime) (hpN : ¬ (p : ℕ) ∣ 4 * N) {f : ℍ → ℂ}
    (hf : thetaMultiplierSystem.Transforms k N χ f) {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 (4 * N))
    (hb : (p : ℤ) ^ 2 ∣ δ 0 1) :
    thetaMultiplierSystem.slash k N χ δ (fAlpha p f) = fAlpha p f := by
  obtain ⟨b', hb'⟩ := hb
  have hdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe δ
    rwa [Matrix.det_fin_two] at this
  have hc4 : ((δ 1 0 : ℤ) : ZMod (4 * N)) = 0 := by rwa [Gamma0_mem] at hδ
  have hc4' : ((4 * N : ℕ) : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc4
  have hdet' : δ 0 0 * δ 1 1 - b' * ((p : ℤ) ^ 2 * δ 1 0) = 1 := by
    linear_combination hdet + (δ 1 0 : ℤ) * hb'
  let δ' : SL(2, ℤ) := ⟨!![δ 0 0, b'; (p : ℤ) ^ 2 * δ 1 0, δ 1 1], by
    rw [Matrix.det_fin_two_of]; linarith⟩
  have hδ' : δ' ∈ Gamma0 (4 * N) := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Dvd.dvd.mul_left hc4' _
  have e00 : (δ' 0 0 : ℤ) = δ 0 0 := rfl
  have e01 : (δ' 0 1 : ℤ) = b' := rfl
  have e10 : (δ' 1 0 : ℤ) = (p : ℤ) ^ 2 * δ 1 0 := rfl
  have e11 : (δ' 1 1 : ℤ) = δ 1 1 := rfl
  have hp0 : ((p : ℕ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr p.ne_zero)
  have hpg : Int.gcd ((p : ℕ) : ℤ) (δ 1 1) = 1 := by
    have hpz : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hnd : ¬ ((p : ℕ) : ℤ) ∣ δ 1 1 := by
      intro hd
      have h1 : ((p : ℕ) : ℤ) ∣ δ 0 1 := ⟨(p : ℤ) * b', by rw [hb']; ring⟩
      have : ((p : ℕ) : ℤ) ∣ δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 :=
        dvd_sub (Dvd.dvd.mul_left hd _) (Dvd.dvd.mul_right h1 _)
      rw [hdet] at this
      exact hpz.not_dvd_one this
    exact Int.isCoprime_iff_gcd_eq_one.mp ((Prime.coprime_iff_not_dvd hpz).mpr hnd)
  funext τ
  have hden : (δ 1 0 : ℂ) * τ + δ 1 1 ≠ 0 := cuspDenom_ne_zero δ τ
  have hden' : ((δ' 1 0 : ℤ) : ℂ) * (affPt 1 (p ^ 2) 0 τ : ℂ) + (δ' 1 1 : ℤ) = (δ 1 0 : ℂ) * τ + δ 1 1 := by
    rw [e10, e11, coe_affPt]
    push_cast
    field_simp
    simp
  have hpt : affPt 1 (p ^ 2) 0 (δ • τ) = δ' • affPt 1 (p ^ 2) 0 τ := by
    apply UpperHalfPlane.ext
    rw [coe_affPt, coe_smul_sl, coe_smul_sl, hden', e00, e01]
    rw [coe_affPt]
    have : (δ 0 1 : ℂ) = (p : ℂ) ^ 2 * b' := by exact_mod_cast hb'
    rw [this]
    push_cast
    field_simp
    simp
  have hj : thetaMult δ' (affPt 1 (p ^ 2) 0 τ) = thetaMult δ τ := by
    unfold thetaMult thetaMultCD
    rw [hden', e10, e11, shimuraSym_sq_mul _ p.pos _ _ hpg]
  have key := hf δ' hδ' (affPt 1 (p ^ 2) 0 τ)
  simp only [MultiplierSystem.slash, thetaMultiplierSystem_j, fAlpha, hpt, key, hj, e11]
  have h1 := chi_ne_zero' hδ χ
  have h2 := thetaMult_ne_zero hδ τ
  field_simp

end ModularFormsKB.HalfIntegral
