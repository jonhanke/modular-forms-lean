/-
# The character of the Rankin integral and the law of the Rankin kernel

`rankinChar k N χ t ψ` $= \chi\kappa\psi$
modulo $16Ntr^2$, $\kappa$ the Kronecker character of $4(-1)^kt$:
- `rankinChar_natCast`: $\omega(n) = \psi(n)\chi_t(n)$ for every $n \in \mathbb N$ ($\chi_t$ = `shimuraChar`);
- `rankinChar_intCast_of_mem`: for $\gamma \in \Gamma_0(16Ntr^2)$, $\omega(d) = \chi(d)\psi(d)\,(t/|d|)\,\chi_4(d)^k$;
- `unitaryLaw_rankinKernel`: from the laws of $f$ and $\theta_{\psi,t}$ (`ThetaTwistLaw`), $G_\psi(\gamma z) =
  \omega(d)\big(\tfrac{cz+d}{|cz+d|}\big)^{k-\nu}G_\psi(z)$ on $\Gamma_0(16Ntr^2)$.
-/
import ModularFormsKB.HalfIntegral.Abstract.ShimuraRankin
import ModularFormsKB.HalfIntegral.ShimuraLift
import ModularFormsKB.HalfIntegral.Abstract.PeterssonConvergence

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup
open scoped Real

local notation "ℍ" => UpperHalfPlane

theorem gamma0_mem_of_dvd {m L : ℕ} (h : m ∣ L) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 L) : γ ∈ Gamma0 m := by
  rw [Gamma0_mem] at hγ ⊢
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    ((Int.natCast_dvd_natCast.mpr h).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ))

theorem odd_of_coprime_four {n : ℕ} (h : n.Coprime 4) : Odd n := by
  rcases Nat.even_or_odd n with he | ho
  · exfalso
    have h2n : 2 ∣ n := even_iff_two_dvd.mp he
    have := (Nat.Coprime.coprime_dvd_right (show 2 ∣ 4 from by norm_num) h).symm
    have := Nat.Coprime.eq_one_of_dvd this h2n
    omega
  · exact ho

theorem jacobiSym_rankinDisc (k t : ℕ) {m : ℕ} (hm : Odd m) :
    jacobiSym (rankinDisc k t) m = jacobiSym ((-1) ^ k * t) m := by
  have h4 : rankinDisc k t = 2 ^ 2 * ((-1) ^ k * t) := by unfold rankinDisc; push_cast; ring
  have hg : (2 : ℤ).gcd m = 1 := by
    have : ¬ (2 ∣ m) := by
      have := Nat.odd_iff.mp hm; omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr this
  rw [h4, jacobiSym.mul_left, jacobiSym.sq_one' hg, one_mul]

theorem chi4_neg_natAbs (d : ℤ) (hd : Odd d) (hneg : d < 0) :
    ZMod.χ₄ (d : ZMod 4) = - ZMod.χ₄ (d.natAbs : ZMod 4) := by
  have hm : (d.natAbs : ℤ) = -d := by omega
  have h2 : ((d.natAbs : ℕ) : ZMod 4) = ((-d : ℤ) : ZMod 4) := by
    rw [← Int.cast_natCast, hm]
  rw [h2, ZMod.χ₄_int_eq_if_mod_four, ZMod.χ₄_int_eq_if_mod_four]
  have := Int.odd_iff.mp hd
  split_ifs <;> omega

theorem kroneckerSym_rankinDisc (k : ℕ) {t : ℕ} (ht : 1 ≤ t) (d : ℤ) (hd : Odd d) :
    TauCeti.kroneckerSym (rankinDisc k t) d =
      (ZMod.χ₄ (d : ZMod 4)) ^ k * jacobiSym t d.natAbs := by
  have hm : Odd d.natAbs := Int.natAbs_odd.mpr hd
  have hJ : jacobiSym (rankinDisc k t) d.natAbs =
      (ZMod.χ₄ (d.natAbs : ZMod 4)) ^ k * jacobiSym t d.natAbs := by
    rw [jacobiSym_rankinDisc k t hm, jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.at_neg_one hm]
  rw [TauCeti.kroneckerSym_of_odd _ hd, hJ]
  have hD : rankinDisc k t < 0 ↔ Odd k := by
    unfold rankinDisc
    have ht' : (0 : ℤ) < t := by exact_mod_cast ht
    rcases Nat.even_or_odd k with h | h
    · have hn : ¬ Odd k := Nat.not_odd_iff_even.mpr h
      rw [h.neg_one_pow]; simp only [hn, iff_false, not_lt]; positivity
    · rw [h.neg_one_pow]; simp only [h, iff_true]; nlinarith
  rcases lt_or_ge d 0 with hneg | hpos
  · rw [chi4_neg_natAbs d hd hneg]
    rcases Nat.even_or_odd k with h | h
    · have : ¬ rankinDisc k t < 0 := fun h' => (Nat.not_odd_iff_even.mpr h) (hD.mp h')
      simp [this, h.neg_pow]
    · have := hD.mpr h
      simp [this, hneg, h.neg_pow]
  · have : ((d.natAbs : ℕ) : ZMod 4) = (d : ZMod 4) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg hpos]
    rw [this]
    simp [not_lt.mpr hpos]

theorem rankinChar_intCast_coprime (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {t : ℕ} (ht : 1 ≤ t) {r : ℕ}
    (ψ : DirichletCharacter ℂ r) (a : ℤ) (ha : IsCoprime a (rankinLevel N t r : ℕ)) :
    rankinChar k N χ t ψ (a : ZMod (rankinLevel N t r)) =
      χ (a : ZMod (4 * N)) * (TauCeti.kroneckerSym (rankinDisc k t) a : ℂ) * ψ (a : ZMod r) := by
  unfold rankinChar
  rw [dif_neg (rankinDisc_ne_zero k ht)]
  simp only [MulChar.mul_apply]
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ ha, DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ ha,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ ha, TauCeti.kroneckerChar_intCast]

/-- $\omega(n) = \psi(n)\chi_t(n)$ for $n \in \mathbb N$, $t \ge 1$. -/
theorem rankinChar_natCast (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {t : ℕ} (ht : 1 ≤ t) {r : ℕ}
    (ψ : DirichletCharacter ℂ r) (n : ℕ) :
    rankinChar k N χ t ψ n = ψ n * shimuraChar k N χ t n := by
  by_cases h : n.Coprime (4 * N) ∧ n.Coprime t ∧ n.Coprime r
  · obtain ⟨h1, h2, h3⟩ := h
    have h4 : n.Coprime 4 := h1.coprime_dvd_right ⟨N, rfl⟩
    have h16 : n.Coprime 16 := by
      have := Nat.Coprime.mul_right h4 h4
      simpa using this
    have hN : n.Coprime N := h1.coprime_dvd_right ⟨4, by ring⟩
    have hL : IsCoprime (n : ℤ) (rankinLevel N t r : ℕ) := by
      rw [Nat.isCoprime_iff_coprime]
      unfold rankinLevel
      exact (((h16.mul_right hN).mul_right h2).mul_right (h3.pow_right 2))
    have hodd : Odd n := odd_of_coprime_four h4
    have := rankinChar_intCast_coprime k N χ ht ψ (n : ℤ) hL
    simp only [Int.cast_natCast] at this
    rw [this, TauCeti.kroneckerSym_eq_jacobiSym _ hodd, jacobiSym_rankinDisc k t hodd]
    unfold shimuraChar
    ring
  · have hL0 : rankinChar k N χ t ψ (n : ZMod (rankinLevel N t r)) = 0 := by
      apply MulChar.map_nonunit
      rw [ZMod.isUnit_iff_coprime]
      intro hc
      apply h
      refine ⟨hc.coprime_dvd_right (four_dvd_rankinLevel N t r), ?_, ?_⟩
      · exact hc.coprime_dvd_right ⟨16 * N * r ^ 2, by unfold rankinLevel; ring⟩
      · exact hc.coprime_dvd_right (mod_dvd_rankinLevel N t r)
    rw [hL0]
    symm
    by_cases c1 : n.Coprime (4 * N)
    · by_cases c2 : n.Coprime t
      · have c3 : ¬ n.Coprime r := fun c3 => h ⟨c1, c2, c3⟩
        have : ψ (n : ZMod r) = 0 := by
          apply MulChar.map_nonunit
          rwa [ZMod.isUnit_iff_coprime]
        rw [this, zero_mul]
      · have h4 : n.Coprime 4 := c1.coprime_dvd_right ⟨N, rfl⟩
        have hodd : Odd n := odd_of_coprime_four h4
        have : jacobiSym ((-1) ^ k * t) n = 0 := by
          rw [jacobiSym.eq_zero_iff]
          refine ⟨by rintro rfl; simp at hodd, ?_⟩
          intro hg
          apply c2
          have hc : IsCoprime (((-1 : ℤ) ^ k * t)) (n : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hg
          rw [IsCoprime.mul_left_iff] at hc
          have := hc.2
          rw [← Nat.isCoprime_iff_coprime]
          exact this.symm
        unfold shimuraChar
        rw [this]; simp
    · have : χ (n : ZMod (4 * N)) = 0 := by
        apply MulChar.map_nonunit
        rwa [ZMod.isUnit_iff_coprime]
      unfold shimuraChar
      rw [this]; simp

/-- The value of $\omega$ at the lower right entry of $\gamma \in \Gamma_0(16Ntr^2)$:
$\omega(d) = \chi(d)\psi(d)\,(t/|d|)\,\chi_4(d)^k$. -/
theorem rankinChar_intCast_of_mem (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {t : ℕ} (ht : 1 ≤ t) {r : ℕ}
    (ψ : DirichletCharacter ℂ r) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (rankinLevel N t r)) :
    rankinChar k N χ t ψ (γ 1 1 : ZMod (rankinLevel N t r)) =
      χ (γ 1 1 : ZMod (4 * N)) * ψ (γ 1 1 : ZMod r) * (jacobiSym t (γ 1 1).natAbs : ℂ) *
        (ZMod.χ₄ (γ 1 1 : ZMod 4) : ℂ) ^ k := by
  have hc : ((rankinLevel N t r : ℕ) : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  obtain ⟨c', hc'⟩ := hc
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  have hcop : IsCoprime (γ 1 1) (rankinLevel N t r : ℕ) :=
    ⟨γ 0 0, -(γ 0 1 * c'), by linear_combination hdet + (γ 0 1 : ℤ) * hc'⟩
  have hodd : Odd (γ 1 1) := by
    obtain ⟨u, v, huv⟩ := hcop
    have h2 : (2 : ℤ) ∣ ((rankinLevel N t r : ℕ) : ℤ) := by
      unfold rankinLevel; push_cast
      exact ⟨8 * N * t * r ^ 2, by ring⟩
    obtain ⟨w, hw⟩ := h2
    rw [Int.odd_iff]
    by_contra hne
    have h3 : (2 : ℤ) ∣ γ 1 1 := Int.dvd_of_emod_eq_zero (by omega)
    obtain ⟨z, hz⟩ := h3
    have : (2 : ℤ) ∣ 1 := by
      rw [← huv, hz, hw]; exact ⟨u * z + v * w, by ring⟩
    omega
  rw [rankinChar_intCast_coprime k N χ ht ψ _ hcop, kroneckerSym_rankinDisc k ht _ hodd]
  push_cast
  ring

/-- **The law of the Rankin kernel** on $\Gamma_0(16Ntr^2)$, for $r = 1$ or an odd prime $r$ and $\nu \le k$. -/
theorem unitaryLaw_rankinKernel (M : MultiplierSystem) (hT : ThetaTwistLaw M) {k N : ℕ}
    {χ : DirichletCharacter ℂ (4 * N)} {f : ℍ → ℂ} (hf : M.Transforms k N χ f) {t : ℕ} (ht : 1 ≤ t) {r : ℕ}
    (hr : r = 1 ∨ (r.Prime ∧ r ≠ 2)) (ψ : DirichletCharacter ℂ r) (hk : charParity ψ ≤ k) :
    UnitaryLaw (rankinLevel N t r) (k - charParity ψ) (rankinChar k N χ t ψ) (rankinKernel k ψ t f) := by
  intro γ hγ τ
  have hγ4N : γ ∈ Gamma0 (4 * N) := gamma0_mem_of_dvd (four_dvd_rankinLevel N t r) hγ
  have hγt : γ ∈ Gamma0 (4 * t * r ^ 2) :=
    gamma0_mem_of_dvd ⟨4 * N, by unfold rankinLevel; ring⟩ hγ
  have hγ4 : γ ∈ Gamma0 4 :=
    gamma0_mem_of_dvd ⟨4 * N * t * r ^ 2, by unfold rankinLevel; ring⟩ hγ
  rw [rankinChar_intCast_of_mem k N χ ht ψ hγ]
  have hf' := hf γ hγ4N τ
  have hr1 : 1 ≤ r := by
    rcases hr with rfl | ⟨hp, -⟩
    · exact le_rfl
    · exact hp.one_lt.le
  have hθ := hT.law r ψ t ht hr1 γ hγt τ
  have hj := hT.j_sq γ hγ4 τ
  have hn := M.norm_sq γ hγ4 τ
  have hD : ((γ 1 0 : ℂ) * τ + γ 1 1) ≠ 0 := by
    rw [← denom_SL_eq]; exact UpperHalfPlane.denom_ne_zero _ τ
  have hA : 0 < ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ := norm_pos_iff.mpr hD
  unfold rankinKernel
  rw [hf', hθ, im_smul_rpow]
  obtain ⟨m, hm⟩ : ∃ m, k = charParity ψ + m := ⟨k - charParity ψ, by omega⟩
  have hkm : k - charParity ψ = m := by omega
  rw [hkm]
  generalize hν : charParity ψ = ν at *
  generalize hDdef : ((γ 1 0 : ℂ) * τ + γ 1 1) = D at *
  generalize hJdef : M.j γ τ = J at *
  generalize hAdef : ‖D‖ = A at *
  generalize hed : (ZMod.χ₄ (γ 1 1 : ZMod 4) : ℂ) = e at *
  have hconj : ∀ x : ZMod r, (starRingEnd ℂ) (ψ⁻¹ x) = ψ x := by
    intro x
    have := MulChar.star_apply' ψ⁻¹ x
    rw [inv_inv] at this
    simpa using this
  have hJJ : J * (starRingEnd ℂ) J = (A : ℂ) := by
    rw [Complex.mul_conj']
    exact_mod_cast hn
  have hDD : D * (starRingEnd ℂ) D = (A : ℂ) ^ 2 := by
    rw [Complex.mul_conj', hAdef]
  have hreal : A ^ (-(((k + ν + 1 : ℕ) : ℝ) / 2)) * A ^ (-(((k + ν + 1 : ℕ) : ℝ) / 2)) * A ^ (1 + 2 * ν) =
      (A ^ m)⁻¹ := by
    rw [← Real.rpow_add hA, show -(((k + ν + 1 : ℕ) : ℝ) / 2) + -(((k + ν + 1 : ℕ) : ℝ) / 2) =
      -((k + ν + 1 : ℕ) : ℝ) by ring, Real.rpow_neg hA.le, Real.rpow_natCast]
    have hA0 : A ≠ 0 := hA.ne'
    subst hm
    field_simp
    ring
  obtain ⟨R, hR⟩ : ∃ R : ℂ, R = ((A ^ (-(((k + ν + 1 : ℕ) : ℝ) / 2)) *
      A ^ (-(((k + ν + 1 : ℕ) : ℝ) / 2)) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hreal' : R * (A : ℂ) ^ (1 + 2 * ν) = ((A : ℂ) ^ m)⁻¹ := by
    rw [hR]; exact_mod_cast hreal
  have key : J ^ (2 * k + 1) * (starRingEnd ℂ) J * (starRingEnd ℂ) D ^ ν * R =
      e ^ k * (D / (A : ℂ)) ^ m := by
    have hA0 : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
    calc J ^ (2 * k + 1) * (starRingEnd ℂ) J * (starRingEnd ℂ) D ^ ν * R
        = (J ^ 2) ^ k * (J * (starRingEnd ℂ) J) * (starRingEnd ℂ) D ^ ν * R := by ring
      _ = e ^ k * D ^ m * (D * (starRingEnd ℂ) D) ^ ν * (A : ℂ) * R := by
        rw [hj, hJJ, mul_pow, hm]; ring
      _ = e ^ k * D ^ m * (R * (A : ℂ) ^ (1 + 2 * ν)) := by
        rw [hDD]; ring
      _ = e ^ k * (D / (A : ℂ)) ^ m := by rw [hreal', div_pow]; ring
  rw [hR] at key
  simp only [map_mul, map_pow, hconj, map_intCast]
  push_cast at key ⊢
  linear_combination (χ (γ 1 1 : ZMod (4 * N)) * ψ (γ 1 1 : ZMod r) *
    (jacobiSym t (γ 1 1).natAbs : ℂ) * f τ * (starRingEnd ℂ) (thetaTwist ψ t τ) *
    ((τ.im ^ (((k : ℝ) + ν + 1) / 2) : ℝ) : ℂ)) * key

end ModularFormsKB.HalfIntegral
