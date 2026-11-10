/-
# The theta function $\theta(z) = \sum_n e(n^2 z)$ and its weight-½ multiplier on $\Gamma_0(4)$

With $e(x) = e^{2\pi i x}$,
$$\theta(z) = \sum_{n \in \mathbb Z} e(n^2 z) = \vartheta(2z),$$
where $\vartheta(\tau) = \sum_n e^{\pi i n^2 \tau}$ is Mathlib's `jacobiTheta`. For
$\gamma = \begin{pmatrix} a&b\\c&d\end{pmatrix} \in \Gamma_0(4)$ the **theta multiplier** is
$$j(\gamma, z) = \varepsilon_d^{-1}\Big(\frac cd\Big)(cz+d)^{1/2}, \qquad
  \varepsilon_d = \begin{cases} 1 & d \equiv 1 \bmod 4\\ i & d \equiv 3 \bmod 4,\end{cases}$$
with the principal branch $-\pi/2 < \arg w^{1/2} \le \pi/2$ (Mathlib's `cpow` with exponent $1/2$) and Shimura's extension of
the Jacobi symbol to negative $d$: $(c/d) = (c/|d|)$, except $(c/d) = -(c/|d|)$ when $c < 0$ and $d < 0$ (`shimuraSym`;
Shimura 1973 `shimura1973`, notation section; Koblitz, *Introduction to Elliptic Curves and Modular Forms*, IV.§1
[unverified]). The **weight-½ transformation law** is $\theta(\gamma z) = j(\gamma, z)\,\theta(z)$ on $\Gamma_0(4)$
(`ThetaTransformationLaw`).

**Checked numerically** (scratch script, 2026-10-27; not a proof): the law with exactly these conventions holds on 1443
random $\gamma \in \Gamma_0(4)$ with $|c| \le 24$, $|d| \le 25$, including $c < 0$ and $d < 0$.

**Index shift.** Matrix entries are 0-based: $c = \gamma_{1,0}$, $d = \gamma_{1,1}$.
-/
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Manifold
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import ModularFormsKB.Citation
namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups
open scoped Real
open UpperHalfPlane (coe_im)

local notation "ℍ" => UpperHalfPlane

/-- **The theta function** $\theta(z) = \sum_{n\in\mathbb Z} e(n^2 z) = \vartheta(2z)$, with $\vartheta$ = Mathlib's `jacobiTheta`. -/
noncomputable def theta (z : ℂ) : ℂ := jacobiTheta (2 * z)

/-- $\theta(z) = \sum_{n \in \mathbb Z} e^{2\pi i n^2 z}$. -/
theorem theta_eq_tsum (z : ℂ) : theta z = ∑' n : ℤ, cexp (2 * π * I * (n : ℂ) ^ 2 * z) := by
  unfold theta
  rw [jacobiTheta]
  refine tsum_congr fun n => ?_
  congr 1
  ring

/-- $\theta(z + 1) = \theta(z)$. -/
theorem theta_add_one (z : ℂ) : theta (z + 1) = theta z := by
  unfold theta
  rw [show 2 * (z + 1) = 2 + 2 * z by ring, jacobiTheta_two_add]

/-- $\theta$ is holomorphic on $\mathbb H$. -/
theorem theta_differentiableOn : DifferentiableOn ℂ theta {z : ℂ | 0 < z.im} := by
  intro z hz
  have h : DifferentiableAt ℂ theta z := by
    unfold theta
    refine DifferentiableAt.comp z (g := jacobiTheta) ?_ (by fun_prop)
    exact differentiableAt_jacobiTheta (by simpa using hz)
  exact h.differentiableWithinAt

/-- **The Fricke law** $\theta(-1/4z) = (-2iz)^{1/2}\,\theta(z)$ on $\mathbb H$, from Mathlib's `jacobiTheta_S_smul`. -/
theorem theta_fricke (z : ℂ) (hz : 0 < z.im) :
    theta (-1 / (4 * z)) = (-2 * I * z) ^ (1 / 2 : ℂ) * theta z := by
  have h := jacobiTheta_S_smul ⟨2 * z, by simpa using hz⟩
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  have e1 : ((ModularGroup.S • (⟨2 * z, by simpa using hz⟩ : ℍ) : ℍ) : ℂ) = 2 * (-1 / (4 * z)) := by
    rw [UpperHalfPlane.modular_S_smul]
    field_simp
    ring
  rw [e1] at h
  unfold theta
  rw [h]
  congr 2
  ring

/-- Principal square roots multiply for arguments in the right half plane. -/
theorem sqrt_mul_of_re_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    a ^ (1 / 2 : ℂ) * b ^ (1 / 2 : ℂ) = (a * b) ^ (1 / 2 : ℂ) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have h1 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha)
  have h2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb)
  rw [abs_lt] at h1 h2
  have hl : Complex.log (a * b) = Complex.log a + Complex.log b :=
    (Complex.log_mul_eq_add_log_iff ha0 hb0).mpr ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
  rw [cpow_def_of_ne_zero ha0, cpow_def_of_ne_zero hb0, cpow_def_of_ne_zero (mul_ne_zero ha0 hb0),
    ← Complex.exp_add, hl]
  congr 1
  ring

/-- **The law at $U = \begin{pmatrix}1&0\\4&1\end{pmatrix}$:** $\theta(z/(4z+1)) = (4z+1)^{1/2}\,\theta(z)$ on $\mathbb H$
(two Fricke steps around a translation; the two principal square roots multiply because both arguments lie in the right
half plane). -/
theorem theta_U (z : ℂ) (hz : 0 < z.im) :
    theta (z / (4 * z + 1)) = (4 * z + 1) ^ (1 / 2 : ℂ) * theta z := by
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  have h4 : 4 * z ≠ 0 := mul_ne_zero (by norm_num) hz0
  set u : ℂ := -1 - 1 / (4 * z) with hu
  have hui : 0 < u.im := by
    have : u.im = z.im / (4 * Complex.normSq z) := by
      rw [hu]
      simp [Complex.normSq_apply]
      field_simp
    rw [this]
    have : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
    positivity
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hui
  have h4u : 4 * u = -(4 * z + 1) / z := by rw [hu]; field_simp; ring
  have h1 : z / (4 * z + 1) = -1 / (4 * u) := by
    have : 4 * z + 1 ≠ 0 := fun h0 => by
      have := congrArg Complex.im h0
      simp at this
      linarith
    rw [h4u]; field_simp
  have h2 := theta_fricke u hui
  have h3 := theta_fricke z hz
  have h5 : theta u = theta (-1 / (4 * z)) := by
    have : -1 / (4 * z) = u + 1 := by rw [hu]; ring
    rw [this, theta_add_one]
  have hre1 : 0 < (-2 * I * u).re := by simpa using hui
  have hre2 : 0 < (-2 * I * z).re := by simpa using hz
  have hprod : (-2 * I * u) * (-2 * I * z) = 4 * z + 1 := by
    rw [hu]; field_simp; ring_nf; simp [Complex.I_sq]
  rw [h1, h2, h5, h3, ← mul_assoc, sqrt_mul_of_re_pos hre1 hre2, hprod]

/-- **Shimura's symbol** $(c/d)$ for odd $d$: the Jacobi symbol $(c/|d|)$, negated when $c < 0$ and $d < 0$. -/
def shimuraSym (c d : ℤ) : ℤ :=
  if c < 0 ∧ d < 0 then -jacobiSym c d.natAbs else jacobiSym c d.natAbs

/-- $\varepsilon_d$: $1$ if $d \equiv 1 \bmod 4$, $i$ otherwise (used for odd $d$ only). -/
noncomputable def epsD (d : ℤ) : ℂ := if d % 4 = 1 then 1 else I

/-- The multiplier $\varepsilon_d^{-1}(c/d)(cz+d)^{1/2}$ as a function of the bottom row $(c, d)$. -/
noncomputable def thetaMultCD (c d : ℤ) (z : ℂ) : ℂ :=
  (epsD d)⁻¹ * (shimuraSym c d : ℂ) * ((c : ℂ) * z + d) ^ (1 / 2 : ℂ)

/-- **The theta multiplier** $j(\gamma, z) = \varepsilon_d^{-1}(c/d)(cz+d)^{1/2}$ of $\gamma \in \mathrm{SL}_2(\mathbb Z)$
(meaningful for $\gamma \in \Gamma_0(4)$). -/
noncomputable def thetaMult (γ : SL(2, ℤ)) (z : ℂ) : ℂ := thetaMultCD (γ 1 0) (γ 1 1) z

/-- **The weight-½ transformation law of $\theta$ on $\Gamma_0(4)$** (Shimura 1973 `shimura1973`, Prop. 2.2; Koblitz IV.§4
[unverified]): $\theta(\gamma z) = j(\gamma, z)\,\theta(z)$ for $\gamma \in \Gamma_0(4)$, $z \in \mathbb H$. A target. -/
def ThetaTransformationLaw : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma0 4, ∀ τ : ℍ, theta ↑(γ • τ) = thetaMult γ τ * theta τ

/-- **The square of the multiplier is the weight-1 factor with character $\chi_{-4}$:** $j(\gamma,z)^2 = \big(\tfrac{-1}{d}\big)(cz+d)$
for $\gamma \in \Gamma_0(4)$. So $j^{2k+1}$ and $j^{2l+1}$ multiply to an integral-weight automorphy factor. -/
theorem thetaMult_sq {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) (z : ℂ) :
    thetaMult γ z ^ 2 = (ZMod.χ₄ (γ 1 1 : ZMod 4) : ℂ) * ((γ 1 0 : ℂ) * z + γ 1 1) := by
  -- Partial proof by the Sonnet agent, stopped 2026-10-27 (one goal unsolved in the `pos` case); resume from here.
  have h0 := (CongruenceSubgroup.Gamma0_mem).mp hγ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at this
  have h4 : (4 : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp (by exact_mod_cast h0)
  obtain ⟨k, hk⟩ := h4
  have hodd : γ 1 1 % 2 = 1 := by
    have : γ 1 1 * γ 0 0 = 1 + 4 * (γ 0 1 * k) := by rw [hk] at hdet; linarith
    rcases Int.emod_two_eq_zero_or_one (γ 1 1) with h | h
    · obtain ⟨t, ht⟩ := Int.dvd_of_emod_eq_zero h
      rw [ht] at this
      have h3 : 2 * (t * γ 0 0) = 1 + 4 * (γ 0 1 * k) := by linarith
      generalize t * γ 0 0 = A at h3
      generalize γ 0 1 * k = B at h3
      omega
    · exact h
  have hcop : IsCoprime (γ 1 0) (γ 1 1) := ⟨-γ 0 1, γ 0 0, by linarith⟩
  have hg : (γ 1 0).gcd (γ 1 1).natAbs = 1 := by
    have := Int.isCoprime_iff_gcd_eq_one.mp hcop
    simpa [Int.gcd, Int.natAbs_abs] using this
  have hj : jacobiSym (γ 1 0) (γ 1 1).natAbs ^ 2 = 1 := jacobiSym.sq_one hg
  have hs : (shimuraSym (γ 1 0) (γ 1 1) : ℂ) ^ 2 = 1 := by
    unfold shimuraSym
    split_ifs
    · push_cast; rw [neg_sq]; exact_mod_cast hj
    · exact_mod_cast hj
  have hsq : (((γ 1 0 : ℂ) * z + γ 1 1) ^ (1 / 2 : ℂ)) ^ 2 = (γ 1 0 : ℂ) * z + γ 1 1 := by
    have := Complex.cpow_nat_inv_pow ((γ 1 0 : ℂ) * z + γ 1 1) (n := 2) (by norm_num)
    simpa using this
  have he : ((epsD (γ 1 1))⁻¹) ^ 2 = (ZMod.χ₄ (γ 1 1 : ZMod 4) : ℂ) := by
    rw [ZMod.χ₄_int_eq_if_mod_four]
    unfold epsD
    have h2 : ¬ γ 1 1 % 2 = 0 := by omega
    by_cases h1 : γ 1 1 % 4 = 1
    · simp [h1, hodd]
    · simp [h1, h2]
  unfold thetaMult thetaMultCD
  rw [mul_pow, mul_pow, hs, hsq, he]
  ring

/-- $j(T, z) = 1$ for $T = \begin{pmatrix}1&1\\0&1\end{pmatrix}$. -/
theorem thetaMultCD_zero_one (z : ℂ) : thetaMultCD 0 1 z = 1 := by
  simp [thetaMultCD, epsD, shimuraSym]

/-- $j(-1, z) = 1$: the bottom row $(0, -1)$ gives $\varepsilon_{-1}^{-1}\,(0/{-1})\,(-1)^{1/2} = i^{-1} \cdot 1 \cdot i$. -/
theorem thetaMultCD_zero_neg_one (z : ℂ) : thetaMultCD 0 (-1) z = 1 := by
  have h : ((-1 : ℂ)) ^ (1 / 2 : ℂ) = I := by
    rw [cpow_def_of_ne_zero (by norm_num), Complex.log_neg_one]
    rw [show (↑Real.pi * I * (1 / 2) : ℂ) = Real.pi / 2 * I by ring, Complex.exp_pi_div_two_mul_I]
  have h2 : epsD (-1) = I := by simp [epsD]
  rw [one_div] at h
  simp [thetaMultCD, h2, shimuraSym, h]

/-- $j(U, z) = (4z+1)^{1/2}$ for $U = \begin{pmatrix}1&0\\4&1\end{pmatrix}$. -/
theorem thetaMultCD_four_one (z : ℂ) : thetaMultCD 4 1 z = (4 * z + 1) ^ (1 / 2 : ℂ) := by
  simp [thetaMultCD, epsD, shimuraSym]

end ModularFormsKB.HalfIntegral
