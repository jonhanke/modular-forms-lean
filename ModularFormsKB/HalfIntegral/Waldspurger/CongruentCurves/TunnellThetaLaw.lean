/-
# Tunnell's theta products: holomorphy and the transformation law on $\Gamma_0(128)$

For $\gamma \in \Gamma_0(128)$ with lower right entry $d$ (odd), `thetaTwist_law` (trivial character, level one) gives
$\theta(t\gamma\tau) = \left(\frac{t}{|d|}\right) j(\gamma,\tau)\,\theta(t\tau)$ for $t \in \{1,2,4,8,32\}$. Since
$\left(\frac{4}{|d|}\right) = 1$, $\left(\frac{8}{|d|}\right) = \left(\frac{32}{|d|}\right) = \left(\frac{2}{|d|}\right)$
and $\left(\frac{2}{|d|}\right)^2 = 1$, the product $\theta_{\mathrm{odd}}\,\theta(2\tau)\,\phi_8$ transforms with the
trivial character and $j^3$, while $\theta_{\mathrm{odd}}\,\theta(4\tau)\,\phi_8$ transforms with the character
$\left(\frac{2}{\cdot}\right)$ (`tunnellChi2`) and $j^3$.

Main results: `transforms_tunnellOddTheta`, `transforms_tunnellEvenTheta`, `mdiff_tunnellOddTheta`,
`mdiff_tunnellEvenTheta`.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.TunnellTheta

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open Complex MatrixGroups CongruenceSubgroup
open scoped Real Manifold

local notation "ℍ" => UpperHalfPlane

/-- Holomorphy of $\tau \mapsto \theta(t\tau)$ on the upper half plane. -/
theorem mdiff_theta_mul (t : ℕ) : MDiff (fun τ : ℍ ↦ HalfIntegral.theta ((t : ℂ) * τ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h : DifferentiableOn ℂ (fun z : ℂ ↦ HalfIntegral.theta ((t : ℂ) * z)) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hz' : 0 < ((t : ℂ) * z).im ∨ t = 0 := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · exact Or.inr h0
      · left
        have : ((t : ℂ) * z).im = t * z.im := by simp
        rw [this]; exact mul_pos (by exact_mod_cast h0) hz
    rcases hz' with hz' | h0
    · have h1 : DifferentiableAt ℂ HalfIntegral.theta ((t : ℂ) * z) :=
        (HalfIntegral.theta_differentiableOn.differentiableAt
          (isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds hz'))
      exact (h1.comp z (by fun_prop)).differentiableWithinAt
    · subst h0
      simp only [Nat.cast_zero, zero_mul]
      exact (differentiableWithinAt_const _)
  refine h.congr fun z hz ↦ ?_
  simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

theorem mdiff_theta_mul_two : MDiff (fun τ : ℍ ↦ HalfIntegral.theta ((2 : ℂ) * τ)) := by
  simpa using mdiff_theta_mul 2

theorem mdiff_thetaOddPart : MDiff thetaOddPart := by
  have h1 := mdiff_theta_mul 1
  have h4 := mdiff_theta_mul 4
  simp only [Nat.cast_one, one_mul] at h1
  simp only [Nat.cast_ofNat] at h4
  exact h1.sub h4

theorem mdiff_thetaSignPart : MDiff thetaSignPart := by
  have h8 := mdiff_theta_mul 8
  have h32 := mdiff_theta_mul 32
  simp only [Nat.cast_ofNat] at h8 h32
  exact (h32.const_smul (2 : ℂ)).sub h8

theorem mdiff_tunnellOddTheta : MDiff tunnellOddTheta := by
  have h2 := mdiff_theta_mul 2
  simp only [Nat.cast_ofNat] at h2
  have e : tunnellOddTheta = (1 / 2 : ℂ) • ((thetaOddPart * fun τ : ℍ ↦ HalfIntegral.theta ((2 : ℂ) * τ)) * thetaSignPart) := by
    funext τ
    simp [tunnellOddTheta]
    ring
  rw [e]
  exact ((mdiff_thetaOddPart.mul h2).mul mdiff_thetaSignPart).const_smul (1 / 2 : ℂ)

theorem mdiff_tunnellEvenTheta : MDiff tunnellEvenTheta := by
  have h4 := mdiff_theta_mul 4
  simp only [Nat.cast_ofNat] at h4
  have e : tunnellEvenTheta = (1 / 2 : ℂ) • ((thetaOddPart * fun τ : ℍ ↦ HalfIntegral.theta ((4 : ℂ) * τ)) * thetaSignPart) := by
    funext τ
    simp [tunnellEvenTheta]
    ring
  rw [e]
  exact ((mdiff_thetaOddPart.mul h4).mul mdiff_thetaSignPart).const_smul (1 / 2 : ℂ)

/-- The law $\theta(t\gamma\tau) = \left(\frac{t}{|d|}\right) j(\gamma,\tau)\,\theta(t\tau)$ on $\Gamma_0(4t)$. -/
theorem theta_mul_law (t : ℕ) (ht : 1 ≤ t) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (4 * t)) (τ : ℍ) :
    HalfIntegral.theta ((t : ℂ) * ((γ • τ : ℍ) : ℂ)) =
      (jacobiSym t (γ 1 1).natAbs : ℂ) * HalfIntegral.thetaMult γ τ * HalfIntegral.theta ((t : ℂ) * τ) := by
  have hp : HalfIntegral.charParity (1 : DirichletCharacter ℂ 1) = 0 := by
    simp [HalfIntegral.charParity]
  have h := HalfIntegral.thetaTwist_law (1 : DirichletCharacter ℂ 1) le_rfl ht
    (γ := γ) (by simpa using hγ) τ
  rw [hp] at h
  rw [theta_mul_eq_thetaTwist, theta_mul_eq_thetaTwist, h]
  simp

theorem gamma0_128_dvd {n : ℕ} (hn : 4 * n ∣ 4 * 32) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (4 * 32)) :
    γ ∈ Gamma0 (4 * n) := by
  rw [Gamma0_mem] at hγ ⊢
  have : ((4 * 32 : ℕ) : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by simpa using hγ)
  have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) (4 * n)).2
    (dvd_trans (by exact_mod_cast hn) this)
  simpa using h2

theorem odd_gamma_one_one {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (4 * 32)) : Odd (γ 1 1) := by
  have h4 : γ ∈ Gamma0 4 := gamma0_128_dvd (n := 1) (by norm_num) hγ
  exact HalfIntegral.Gamma0_four_odd h4

theorem jacobi_two_sq (d : ℤ) (hd : Odd d) : ((jacobiSym 2 d.natAbs : ℤ) : ℂ) ^ 2 = 1 := by
  have hodd : Odd d.natAbs := Int.natAbs_odd.2 hd
  have hg : Nat.gcd 2 d.natAbs = 1 := Nat.coprime_two_left.2 hodd
  have h0 : jacobiSym (2 ^ 2) d.natAbs = 1 :=
    jacobiSym.sq_one' (a := 2) (b := d.natAbs)
      (by show Nat.gcd (2 : ℤ).natAbs (d.natAbs : ℤ).natAbs = 1; exact hg)
  have h : (jacobiSym 2 d.natAbs) ^ 2 = 1 := by rw [← jacobiSym.pow_left]; exact h0
  rw [← Int.cast_pow, h]; simp

theorem coprime_of_odd_int {d : ℤ} (hd : Odd d) : IsCoprime d ((4 * 32 : ℕ) : ℤ) := by
  have h2 : IsCoprime d 2 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    rcases hd with ⟨k, rfl⟩
    simp [Int.gcd_comm]
  have := h2.pow_right (n := 7)
  simpa using this

theorem tunnellChi2_apply_int {d : ℤ} (hd : Odd d) :
    tunnellChi2 (d : ZMod (4 * 32)) = (jacobiSym 2 d.natAbs : ℂ) := by
  have hc := coprime_of_odd_int hd
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd' (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ))
    (by norm_num : 8 ∣ 4 * 32) hc
  rw [tunnellChi2, this]
  have hodd : Odd d.natAbs := by simpa [Int.natAbs_odd] using hd
  rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
  simp only [MulChar.ringHomComp_apply, ZMod.χ₈_int_eq_if_mod_eight, Int.cast_ite]
  have hm : d % 2 = 1 := Int.odd_iff.mp hd
  have hn : (d.natAbs : ℤ) = d ∨ (d.natAbs : ℤ) = -d := by omega
  have hn8 : (d.natAbs : ℤ) % 8 = d % 8 ∨ (d.natAbs : ℤ) % 8 = (-d) % 8 := by
    rcases hn with h | h <;> rw [h] <;> simp
  split_ifs <;> simp <;> omega

theorem jacobi_two_pow (k : ℕ) (n : ℕ) : jacobiSym ((2 ^ k : ℕ) : ℤ) n = jacobiSym 2 n ^ k := by
  push_cast
  rw [jacobiSym.pow_left]

/-- The five laws for $t \in \{1, 2, 4, 8, 32\}$, with $s = (2/|d|)$. -/
theorem tunnell_laws {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (4 * 32)) (τ : ℍ) :
    ∃ s : ℂ, s ^ 2 = 1 ∧ s = (jacobiSym 2 (γ 1 1).natAbs : ℂ) ∧
      HalfIntegral.theta ((γ • τ : ℍ) : ℂ) = HalfIntegral.thetaMult γ τ * HalfIntegral.theta τ ∧
      HalfIntegral.theta (2 * ((γ • τ : ℍ) : ℂ)) =
        s * HalfIntegral.thetaMult γ τ * HalfIntegral.theta (2 * τ) ∧
      HalfIntegral.theta (4 * ((γ • τ : ℍ) : ℂ)) = HalfIntegral.thetaMult γ τ * HalfIntegral.theta (4 * τ) ∧
      HalfIntegral.theta (8 * ((γ • τ : ℍ) : ℂ)) =
        s * HalfIntegral.thetaMult γ τ * HalfIntegral.theta (8 * τ) ∧
      HalfIntegral.theta (32 * ((γ • τ : ℍ) : ℂ)) =
        s * HalfIntegral.thetaMult γ τ * HalfIntegral.theta (32 * τ) := by
  have hs2 := jacobi_two_sq (γ 1 1) (odd_gamma_one_one hγ)
  set s : ℂ := (jacobiSym 2 (γ 1 1).natAbs : ℂ) with hs
  have h3 : s ^ 3 = s := by linear_combination s * hs2
  have h5 : s ^ 5 = s := by linear_combination (s ^ 3 + s) * hs2
  refine ⟨s, hs2, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · have := theta_mul_law 1 le_rfl (gamma0_128_dvd (n := 1) (by norm_num) hγ) τ
    simpa using this
  · have := theta_mul_law 2 (by norm_num) (gamma0_128_dvd (n := 2) (by norm_num) hγ) τ
    simpa using this
  · have := theta_mul_law 4 (by norm_num) (gamma0_128_dvd (n := 4) (by norm_num) hγ) τ
    have e : (jacobiSym ((4 : ℕ) : ℤ) (γ 1 1).natAbs : ℂ) = 1 := by
      have := jacobi_two_pow 2 (γ 1 1).natAbs
      have e2 : ((4 : ℕ) : ℤ) = ((2^2 : ℕ) : ℤ) := by norm_num
      rw [e2, this]
      push_cast
      exact hs2
    rw [e] at this
    simpa using this
  · have := theta_mul_law 8 (by norm_num) (gamma0_128_dvd (n := 8) (by norm_num) hγ) τ
    have e : (jacobiSym ((8 : ℕ) : ℤ) (γ 1 1).natAbs : ℂ) = s := by
      have := jacobi_two_pow 3 (γ 1 1).natAbs
      have e2 : ((8 : ℕ) : ℤ) = ((2^3 : ℕ) : ℤ) := by norm_num
      rw [e2, this]
      push_cast
      exact h3
    rw [e] at this
    simpa using this
  · have := theta_mul_law 32 (by norm_num) (gamma0_128_dvd (n := 32) (by norm_num) hγ) τ
    have e : (jacobiSym ((32 : ℕ) : ℤ) (γ 1 1).natAbs : ℂ) = s := by
      have := jacobi_two_pow 5 (γ 1 1).natAbs
      have e2 : ((32 : ℕ) : ℤ) = ((2^5 : ℕ) : ℤ) := by norm_num
      rw [e2, this]
      push_cast
      exact h5
    rw [e] at this
    simpa using this

theorem transforms_tunnellOddTheta :
    HalfIntegral.thetaMultiplierSystem.Transforms 1 32 tunnellChi0 tunnellOddTheta := by
  intro γ hγ τ
  obtain ⟨s, hs, -, h1, h2, h4, h8, h32⟩ := tunnell_laws hγ τ
  simp only [tunnellOddTheta, thetaOddPart, thetaSignPart, h1, h2, h4, h8, h32,
    HalfIntegral.thetaMultiplierSystem_j]
  have hu : IsUnit ((γ 1 1 : ℤ) : ZMod (4 * 32)) := by
    obtain ⟨a, b, hab⟩ := coprime_of_odd_int (odd_gamma_one_one hγ)
    refine IsUnit.of_mul_eq_one (a : ZMod (4 * 32)) ?_
    have := congrArg (Int.cast : ℤ → ZMod (4 * 32)) hab
    push_cast at this
    have h0 : (128 : ZMod (4 * 32)) = 0 := by decide
    rw [h0] at this
    simpa [mul_comm] using this
  have hχ : tunnellChi0 ((γ 1 1 : ℤ) : ZMod (4 * 32)) = 1 := MulChar.one_apply hu
  rw [hχ]
  generalize HalfIntegral.thetaMult γ τ = j
  generalize HalfIntegral.theta τ = a
  generalize HalfIntegral.theta (2 * (τ : ℂ)) = b
  generalize HalfIntegral.theta (4 * (τ : ℂ)) = c
  generalize HalfIntegral.theta (8 * (τ : ℂ)) = e
  generalize HalfIntegral.theta (32 * (τ : ℂ)) = g
  linear_combination (j ^ 3 * (a - c) * b * (2 * g - e) / 2) * hs

theorem transforms_tunnellEvenTheta :
    HalfIntegral.thetaMultiplierSystem.Transforms 1 32 tunnellChi2 tunnellEvenTheta := by
  intro γ hγ τ
  obtain ⟨s, hs, hsd, h1, -, h4, h8, h32⟩ := tunnell_laws hγ τ
  have hχ : tunnellChi2 ((γ 1 1 : ℤ) : ZMod (4 * 32)) = s := by
    rw [tunnellChi2_apply_int (odd_gamma_one_one hγ), hsd]
  simp only [tunnellEvenTheta, thetaOddPart, thetaSignPart, h1, h4, h8, h32,
    HalfIntegral.thetaMultiplierSystem_j, hχ]
  ring

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
