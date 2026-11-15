/-
# The coset sum `heckeFun` satisfies the transformation law

Let $p \nmid 4N$ be prime, $\Gamma = \Gamma_0(4N)$ and
$H = \{\gamma \in \Gamma : p^2 \mid b\}$. Two elements $x, y \in \Gamma$ lie in the same right coset $Hx = Hy$ iff
$p^2 \mid x_{00}y_{01} - x_{01}y_{00}$ (their first rows are proportional mod $p^2$). The $p^2 + p$ elements
* $T^b$, $0 \le b < p^2$ (the classes with $p \nmid x_{00}$),
* $r_0$ (`repZero`; the class $p^2 \mid x_{00}$),
* $r_i$, $1 \le i < p$ (`repMid`; the classes with $p \,\|\, x_{00}$ and $x_{01} \equiv 4i\,x_{00}/p \bmod p$)

represent $H\backslash\Gamma$, and by `HeckeMult.lean`
$$p^2\,\texttt{heckeFun}\ f = \sum_{r} f_\alpha|_r .$$
For $\gamma \in \Gamma$, right multiplication by $\gamma$ permutes the classes, $f_\alpha$ is $H$-invariant (`slash_conj`) and
the slash action is a right action (`MultiplierSystem.slash_mul`), so the sum is invariant: `heckeFun_transforms`.
-/
import ModularFormsKB.HalfIntegral.HeckeMult

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup
open scoped Real

local notation "ℍ" => UpperHalfPlane

set_option linter.unusedSectionVars false

namespace HeckeCoset

lemma mul_inv_01 (x y : SL(2, ℤ)) : (x * y⁻¹) 0 1 = x 0 1 * y 0 0 - x 0 0 * y 0 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

lemma repZero_00 (N : ℕ) (p : ℕ+) (y w : ℤ) (h : (p : ℤ) ^ 2 * w - 4 * N * y = 1) :
    repZero N p y w h 0 0 = (p : ℤ) ^ 2 := by simp [repZero]
lemma repZero_01 (N : ℕ) (p : ℕ+) (y w : ℤ) (h : (p : ℤ) ^ 2 * w - 4 * N * y = 1) :
    repZero N p y w h 0 1 = y := by simp [repZero]
lemma repZero_10 (N : ℕ) (p : ℕ+) (y w : ℤ) (h : (p : ℤ) ^ 2 * w - 4 * N * y = 1) :
    repZero N p y w h 1 0 = 4 * N := by simp [repZero]
lemma repMid_00 (N : ℕ) (p : ℕ+) (i A B : ℤ) (h : A * (p + 16 * N * i) + 4 * N * p * B = 1) :
    repMid N p i A B h 0 0 = p * A := by simp [repMid]
lemma repMid_01 (N : ℕ) (p : ℕ+) (i A B : ℤ) (h : A * (p + 16 * N * i) + 4 * N * p * B = 1) :
    repMid N p i A B h 0 1 = 4 * i * A + p * B := by simp [repMid]
lemma repMid_10 (N : ℕ) (p : ℕ+) (i A B : ℤ) (h : A * (p + 16 * N * i) + 4 * N * p * B = 1) :
    repMid N p i A B h 1 0 = -4 * N := by simp [repMid]

lemma T_zpow_00 (b : ℕ) : (ModularGroup.T ^ (b : ℤ) : SL(2, ℤ)) 0 0 = 1 := by
  rw [ModularGroup.coe_T_zpow]; simp
lemma T_zpow_01 (b : ℕ) : (ModularGroup.T ^ (b : ℤ) : SL(2, ℤ)) 0 1 = b := by
  rw [ModularGroup.coe_T_zpow]; simp
lemma T_zpow_10 (b : ℕ) : (ModularGroup.T ^ (b : ℤ) : SL(2, ℤ)) 1 0 = 0 := by
  rw [ModularGroup.coe_T_zpow]; simp

/-- Two elements of $\mathrm{SL}_2(\mathbb Z)$ are related when $x y^{-1}$ has upper-right entry divisible by $p^2$. -/
def CRel (p : ℕ+) (x y : SL(2, ℤ)) : Prop := (p : ℤ) ^ 2 ∣ x 0 1 * y 0 0 - x 0 0 * y 0 1

lemma CRel_iff (p : ℕ+) (x y : SL(2, ℤ)) : CRel p x y ↔ (p : ℤ) ^ 2 ∣ (x * y⁻¹) 0 1 := by
  rw [mul_inv_01]; rfl

lemma CRel.symm {p : ℕ+} {x y : SL(2, ℤ)} (h : CRel p x y) : CRel p y x := by
  obtain ⟨c, hc⟩ := h
  exact ⟨-c, by linear_combination -hc⟩

lemma CRel.trans {p : ℕ+} {x y z : SL(2, ℤ)} (h1 : CRel p x y) (h2 : CRel p y z) : CRel p x z := by
  have hd := y.det_coe
  rw [Matrix.det_fin_two] at hd
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨(y 1 1 * z 0 0 - y 1 0 * z 0 1) * a + (y 1 1 * x 0 0 - y 1 0 * x 0 1) * b, ?_⟩
  linear_combination (y 1 1 * z 0 0 - y 1 0 * z 0 1) * ha + (y 1 1 * x 0 0 - y 1 0 * x 0 1) * hb
    - (x 0 1 * z 0 0 - x 0 0 * z 0 1) * hd

lemma CRel_mul_right (p : ℕ+) (x y γ : SL(2, ℤ)) : CRel p (x * γ) (y * γ) ↔ CRel p x y := by
  rw [CRel_iff, CRel_iff]
  have : x * γ * (y * γ)⁻¹ = x * y⁻¹ := by group
  rw [this]

section Coset

variable (N : ℕ) (p : ℕ+) (hp : (p : ℕ).Prime) (hpN : ¬ (p : ℕ) ∣ 4 * N)
include hp hpN

lemma prime_int : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp

lemma not_dvd_4N_int : ¬ ((p : ℕ) : ℤ) ∣ 4 * (N : ℤ) := by
  intro h
  apply hpN
  exact_mod_cast h

lemma not_dvd_4_int : ¬ ((p : ℕ) : ℤ) ∣ 4 :=
  fun h => not_dvd_4N_int N p hp hpN (dvd_mul_of_dvd_left h _)

lemma exists_zero : ∃ yw : ℤ × ℤ, (p : ℤ) ^ 2 * yw.2 - 4 * N * yw.1 = 1 := by
  have h : IsCoprime ((p : ℤ) ^ 2) (4 * (N : ℤ)) := by
    have : IsCoprime ((p : ℕ) : ℤ) (4 * (N : ℤ)) := by
      rw [(prime_int N p hp hpN).coprime_iff_not_dvd]
      exact not_dvd_4N_int N p hp hpN
    exact this.pow_left
  obtain ⟨u, v, huv⟩ := h
  exact ⟨(-v, u), by simp only; linear_combination huv⟩

lemma exists_mid (i : ℕ) (hi : ¬ (p : ℕ) ∣ i) :
    ∃ AB : ℤ × ℤ, AB.1 * ((p : ℤ) + 16 * N * i) + 4 * N * p * AB.2 = 1 := by
  have hz := prime_int N p hp hpN
  have h1 : IsCoprime ((p : ℕ) : ℤ) (4 * (N : ℤ)) := by
    rw [hz.coprime_iff_not_dvd]
    exact not_dvd_4N_int N p hp hpN
  have h2 : IsCoprime ((p : ℤ) + 16 * N * i) (4 * (N : ℤ)) := by
    have := h1.add_mul_left_left (4 * (i : ℤ))
    convert this using 2
    ring
  have h3 : IsCoprime ((p : ℤ) + 16 * N * i) ((p : ℕ) : ℤ) := by
    apply IsCoprime.symm
    rw [hz.coprime_iff_not_dvd]
    intro hd
    have hd2 : ((p : ℕ) : ℤ) ∣ (4 * (N : ℤ)) * (4 * (i : ℤ)) := by
      have := (dvd_add_right (dvd_refl ((p : ℕ) : ℤ))).mp hd
      convert this using 1
      ring
    rcases hz.dvd_or_dvd hd2 with h | h
    · exact not_dvd_4N_int N p hp hpN h
    · rcases hz.dvd_or_dvd h with h | h
      · exact not_dvd_4_int N p hp hpN h
      · exact hi (by exact_mod_cast h)
  have h4 := h2.mul_right h3
  obtain ⟨u, v, huv⟩ := h4
  exact ⟨(u, v), by simp only; linear_combination huv⟩

noncomputable def zeroYW : ℤ × ℤ := Classical.choose (exists_zero N p hp hpN)

lemma zeroYW_spec : (p : ℤ) ^ 2 * (zeroYW N p hp hpN).2 - 4 * N * (zeroYW N p hp hpN).1 = 1 :=
  Classical.choose_spec (exists_zero N p hp hpN)

noncomputable def midAB (i : ℕ) : ℤ × ℤ :=
  if h : ¬ (p : ℕ) ∣ i then Classical.choose (exists_mid N p hp hpN i h) else (0, 0)

lemma midAB_spec (i : ℕ) (h : ¬ (p : ℕ) ∣ i) :
    (midAB N p hp hpN i).1 * ((p : ℤ) + 16 * N * i) + 4 * N * p * (midAB N p hp hpN i).2 = 1 := by
  unfold midAB
  rw [dif_pos h]
  exact Classical.choose_spec (exists_mid N p hp hpN i h)

lemma not_dvd_of_fin (i : Fin (p : ℕ)) (h : (i : ℕ) ≠ 0) : ¬ (p : ℕ) ∣ (i : ℕ) :=
  Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero h) i.2

/-- The coset representatives, indexed by `Fin (p^2) ⊕ Fin p`. -/
noncomputable def rep : Fin ((p : ℕ) ^ 2) ⊕ Fin (p : ℕ) → SL(2, ℤ)
  | Sum.inl b => ModularGroup.T ^ ((b : ℕ) : ℤ)
  | Sum.inr i =>
    if h : (i : ℕ) = 0 then
      repZero N p (zeroYW N p hp hpN).1 (zeroYW N p hp hpN).2 (zeroYW_spec N p hp hpN)
    else repMid N p ((i : ℕ) : ℤ) (midAB N p hp hpN i).1 (midAB N p hp hpN i).2
      (midAB_spec N p hp hpN i (not_dvd_of_fin N p hp hpN i h))

lemma rep_inl (b : Fin ((p : ℕ) ^ 2)) :
    rep N p hp hpN (Sum.inl b) = ModularGroup.T ^ ((b : ℕ) : ℤ) := rfl

lemma rep_inr_zero (i : Fin (p : ℕ)) (h : (i : ℕ) = 0) :
    rep N p hp hpN (Sum.inr i) =
      repZero N p (zeroYW N p hp hpN).1 (zeroYW N p hp hpN).2 (zeroYW_spec N p hp hpN) := by
  simp [rep, h]

lemma rep_inr_pos (i : Fin (p : ℕ)) (h : (i : ℕ) ≠ 0) :
    rep N p hp hpN (Sum.inr i) =
      repMid N p ((i : ℕ) : ℤ) (midAB N p hp hpN i).1 (midAB N p hp hpN i).2
        (midAB_spec N p hp hpN i (not_dvd_of_fin N p hp hpN i h)) := by
  simp [rep, h]

lemma rep_mem (x : Fin ((p : ℕ) ^ 2) ⊕ Fin (p : ℕ)) : rep N p hp hpN x ∈ Gamma0 (4 * N) := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rcases x with b | i
  · rw [rep_inl, T_zpow_10]; simp
  · by_cases h : (i : ℕ) = 0
    · rw [rep_inr_zero N p hp hpN i h, repZero_10]; push_cast; exact dvd_refl _
    · rw [rep_inr_pos N p hp hpN i h, repMid_10]; push_cast
      exact ⟨-1, by ring⟩

lemma not_dvd_A (i A B : ℤ) (h : A * (p + 16 * N * i) + 4 * N * p * B = 1) : ¬ ((p : ℕ) : ℤ) ∣ A := by
  have hz := prime_int N p hp hpN
  intro hA
  apply hz.not_dvd_one
  rw [← h]
  refine dvd_add (Dvd.dvd.mul_right hA _) ?_
  exact (dvd_mul_left _ _).mul_right _

lemma not_rel_inl_zero (b : Fin ((p : ℕ) ^ 2)) (i : Fin (p : ℕ)) (hi : (i : ℕ) = 0) :
    ¬ CRel p (rep N p hp hpN (Sum.inl b)) (rep N p hp hpN (Sum.inr i)) := by
  have hz := prime_int N p hp hpN
  intro h
  unfold CRel at h
  rw [rep_inl, rep_inr_zero N p hp hpN i hi, T_zpow_00, T_zpow_01, repZero_00, repZero_01] at h
  have hy : (p : ℤ) ^ 2 ∣ (zeroYW N p hp hpN).1 := by
    have h' : (p : ℤ) ^ 2 ∣ ((b : ℕ) : ℤ) * (p : ℤ) ^ 2 - (zeroYW N p hp hpN).1 := by simpa using h
    exact (dvd_sub_right (dvd_mul_left _ _)).mp h'
  apply hz.not_dvd_one
  rw [← zeroYW_spec N p hp hpN]
  exact dvd_sub (Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _)
    (Dvd.dvd.mul_left ((dvd_pow_self _ two_ne_zero).trans hy) _)

lemma not_rel_inl_pos (b : Fin ((p : ℕ) ^ 2)) (i : Fin (p : ℕ)) (hi : (i : ℕ) ≠ 0) :
    ¬ CRel p (rep N p hp hpN (Sum.inl b)) (rep N p hp hpN (Sum.inr i)) := by
  have hz := prime_int N p hp hpN
  intro h
  unfold CRel at h
  rw [rep_inl, rep_inr_pos N p hp hpN i hi, T_zpow_00, T_zpow_01, repMid_00, repMid_01] at h
  have hspec := midAB_spec N p hp hpN i (not_dvd_of_fin N p hp hpN i hi)
  have hpA := not_dvd_A N p hp hpN _ _ _ hspec
  have h1 := (dvd_pow_self ((p : ℕ) : ℤ) two_ne_zero).trans h
  have h2 : ((p : ℕ) : ℤ) ∣ 4 * ((i : ℕ) : ℤ) * (midAB N p hp hpN i).1 := by
    have e : 4 * ((i : ℕ) : ℤ) * (midAB N p hp hpN i).1 = (p : ℤ) * (((b : ℕ) : ℤ) * (midAB N p hp hpN i).1
        - (midAB N p hp hpN i).2) - (((b : ℕ) : ℤ) * (p * (midAB N p hp hpN i).1)
        - 1 * (4 * ((i : ℕ) : ℤ) * (midAB N p hp hpN i).1 + p * (midAB N p hp hpN i).2)) := by ring
    rw [e]
    exact dvd_sub (dvd_mul_right _ _) h1
  rcases hz.dvd_or_dvd h2 with h3 | h3
  · rcases hz.dvd_or_dvd h3 with h4 | h4
    · exact not_dvd_4_int N p hp hpN h4
    · exact not_dvd_of_fin N p hp hpN i hi (by exact_mod_cast h4)
  · exact hpA h3

lemma not_rel_zero_pos (i i' : Fin (p : ℕ)) (hi : (i : ℕ) = 0) (hi' : (i' : ℕ) ≠ 0) :
    ¬ CRel p (rep N p hp hpN (Sum.inr i)) (rep N p hp hpN (Sum.inr i')) := by
  have hz := prime_int N p hp hpN
  intro h
  unfold CRel at h
  rw [rep_inr_zero N p hp hpN i hi, rep_inr_pos N p hp hpN i' hi', repZero_00, repZero_01, repMid_00,
    repMid_01] at h
  have hspec := midAB_spec N p hp hpN i' (not_dvd_of_fin N p hp hpN i' hi')
  have hpA := not_dvd_A N p hp hpN _ _ _ hspec
  have hy : ¬ ((p : ℕ) : ℤ) ∣ (zeroYW N p hp hpN).1 := by
    intro hd
    apply hz.not_dvd_one
    rw [← zeroYW_spec N p hp hpN]
    exact dvd_sub (Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _) (Dvd.dvd.mul_left hd _)
  have h1 := (dvd_sub_left (dvd_mul_right ((p : ℤ) ^ 2) _)).mp h
  rw [show (zeroYW N p hp hpN).1 * ((p : ℤ) * (midAB N p hp hpN i').1) =
    (p : ℤ) * ((zeroYW N p hp hpN).1 * (midAB N p hp hpN i').1) by ring, pow_two] at h1
  have h2 := (mul_dvd_mul_iff_left hz.ne_zero).mp h1
  rcases hz.dvd_or_dvd h2 with h3 | h3
  · exact hy h3
  · exact hpA h3

lemma rel_inr_inr (i i' : Fin (p : ℕ))
    (h : CRel p (rep N p hp hpN (Sum.inr i)) (rep N p hp hpN (Sum.inr i'))) : i = i' := by
  have hz := prime_int N p hp hpN
  by_cases hi : (i : ℕ) = 0 <;> by_cases hi' : (i' : ℕ) = 0
  · exact Fin.ext (hi.trans hi'.symm)
  · exact absurd h (not_rel_zero_pos N p hp hpN i i' hi hi')
  · exact absurd h.symm (not_rel_zero_pos N p hp hpN i' i hi' hi)
  · unfold CRel at h
    rw [rep_inr_pos N p hp hpN i hi, rep_inr_pos N p hp hpN i' hi', repMid_00, repMid_01, repMid_00,
      repMid_01] at h
    have hspec := midAB_spec N p hp hpN i (not_dvd_of_fin N p hp hpN i hi)
    have hspec' := midAB_spec N p hp hpN i' (not_dvd_of_fin N p hp hpN i' hi')
    have hpA := not_dvd_A N p hp hpN _ _ _ hspec
    have hpA' := not_dvd_A N p hp hpN _ _ _ hspec'
    generalize (midAB N p hp hpN i).1 = A at *
    generalize (midAB N p hp hpN i).2 = B at *
    generalize (midAB N p hp hpN i').1 = A' at *
    generalize (midAB N p hp hpN i').2 = B' at *
    have e : (4 * ((i : ℕ) : ℤ) * A + (p : ℤ) * B) * ((p : ℤ) * A') -
        (p : ℤ) * A * (4 * ((i' : ℕ) : ℤ) * A' + (p : ℤ) * B') =
        (p : ℤ) * (4 * A * A' * (((i : ℕ) : ℤ) - ((i' : ℕ) : ℤ))) + (p : ℤ) ^ 2 * (B * A' - A * B') := by
      ring
    rw [e] at h
    have h1 := (dvd_add_left (dvd_mul_right ((p : ℤ) ^ 2) _)).mp h
    rw [pow_two] at h1
    have h2 := (mul_dvd_mul_iff_left hz.ne_zero).mp h1
    have h3 : ((p : ℕ) : ℤ) ∣ ((i : ℕ) : ℤ) - ((i' : ℕ) : ℤ) := by
      rcases hz.dvd_or_dvd h2 with h3 | h3
      · rcases hz.dvd_or_dvd h3 with h4 | h4
        · rcases hz.dvd_or_dvd h4 with h5 | h5
          · exact absurd h5 (not_dvd_4_int N p hp hpN)
          · exact absurd h5 hpA
        · exact absurd h4 hpA'
      · exact h3
    have hl : ((i : ℕ) : ℤ) < (p : ℤ) := by exact_mod_cast i.2
    have hl' : ((i' : ℕ) : ℤ) < (p : ℤ) := by exact_mod_cast i'.2
    have h0 : (0 : ℤ) ≤ ((i : ℕ) : ℤ) := by positivity
    have h0' : (0 : ℤ) ≤ ((i' : ℕ) : ℤ) := by positivity
    have := Int.eq_zero_of_abs_lt_dvd h3 (abs_lt.mpr ⟨by linarith, by linarith⟩)
    exact Fin.ext (by exact_mod_cast sub_eq_zero.mp this)

lemma rep_inj (x y : Fin ((p : ℕ) ^ 2) ⊕ Fin (p : ℕ))
    (h : CRel p (rep N p hp hpN x) (rep N p hp hpN y)) : x = y := by
  rcases x with b | i <;> rcases y with b' | i'
  · unfold CRel at h
    rw [rep_inl, rep_inl, T_zpow_00, T_zpow_01, T_zpow_00, T_zpow_01] at h
    have hl : ((b : ℕ) : ℤ) < (p : ℤ) ^ 2 := by exact_mod_cast b.2
    have hl' : ((b' : ℕ) : ℤ) < (p : ℤ) ^ 2 := by exact_mod_cast b'.2
    have h0 : (0 : ℤ) ≤ ((b : ℕ) : ℤ) := by positivity
    have h0' : (0 : ℤ) ≤ ((b' : ℕ) : ℤ) := by positivity
    have h' : (p : ℤ) ^ 2 ∣ ((b : ℕ) : ℤ) - ((b' : ℕ) : ℤ) := by simpa using h
    have := Int.eq_zero_of_abs_lt_dvd h' (abs_lt.mpr ⟨by linarith, by linarith⟩)
    exact congrArg Sum.inl (Fin.ext (by exact_mod_cast sub_eq_zero.mp this))
  · exfalso
    by_cases hi' : (i' : ℕ) = 0
    · exact not_rel_inl_zero N p hp hpN b i' hi' h
    · exact not_rel_inl_pos N p hp hpN b i' hi' h
  · exfalso
    by_cases hi : (i : ℕ) = 0
    · exact not_rel_inl_zero N p hp hpN b' i hi h.symm
    · exact not_rel_inl_pos N p hp hpN b' i hi h.symm
  · rw [rel_inr_inr N p hp hpN i i' h]

end Coset

lemma aux_mid (q g00 g01 u i A B : ℤ) (hu : g00 = q * u) (hm : q ∣ g01 - 4 * i * u) :
    q ^ 2 ∣ g01 * (q * A) - g00 * (4 * i * A + q * B) := by
  obtain ⟨m, hm'⟩ := hm
  exact ⟨A * m - u * B, by rw [hu]; linear_combination (q * A) * hm'⟩

lemma aux_T (q g00 g01 u v Q : ℤ) (b : ℕ) (huv : u * g00 + v * q ^ 2 = 1)
    (hb : g01 * u = q ^ 2 * Q + b) : q ^ 2 ∣ g01 * 1 - g00 * b :=
  ⟨g01 * v + g00 * Q, by linear_combination (-g01) * huv + g00 * hb⟩

section Coset2

variable (N : ℕ) (p : ℕ+) (hp : (p : ℕ).Prime) (hpN : ¬ (p : ℕ) ∣ 4 * N)
include hp hpN

lemma exists_rel (g : SL(2, ℤ)) : ∃ j, CRel p g (rep N p hp hpN j) := by
  have hz := prime_int N p hp hpN
  have hd := g.det_coe
  rw [Matrix.det_fin_two] at hd
  have hP : (0 : ℤ) < ((p : ℕ) : ℤ) := by exact_mod_cast p.pos
  by_cases h1 : ((p : ℕ) : ℤ) ∣ g 0 0
  · by_cases h2 : ((p : ℕ) : ℤ) ^ 2 ∣ g 0 0
    · refine ⟨Sum.inr ⟨0, hp.pos⟩, ?_⟩
      unfold CRel
      rw [rep_inr_zero N p hp hpN ⟨0, hp.pos⟩ rfl, repZero_00, repZero_01]
      exact dvd_sub (dvd_mul_left _ _) (h2.mul_right _)
    · obtain ⟨u, hu⟩ := h1
      have hpu : ¬ ((p : ℕ) : ℤ) ∣ u := fun ⟨c, hc⟩ => h2 ⟨c, by rw [hu, hc]; ring⟩
      have hp01 : ¬ ((p : ℕ) : ℤ) ∣ g 0 1 := by
        intro h
        apply hz.not_dvd_one
        rw [← hd]
        exact dvd_sub (Dvd.dvd.mul_right ⟨u, hu⟩ _) (Dvd.dvd.mul_right h _)
      have hcop : IsCoprime ((p : ℕ) : ℤ) (4 * u) := by
        rw [hz.coprime_iff_not_dvd]
        intro h
        rcases hz.dvd_or_dvd h with h | h
        · exact not_dvd_4_int N p hp hpN h
        · exact hpu h
      obtain ⟨t, s, hts⟩ := hcop
      have e : g 0 1 * s % ((p : ℕ) : ℤ) + ((p : ℕ) : ℤ) * (g 0 1 * s / ((p : ℕ) : ℤ)) = g 0 1 * s := by rw [Int.emod_def]; ring
      have hi0 := Int.emod_nonneg (g 0 1 * s) hP.ne'
      have hip := Int.emod_lt_of_pos (g 0 1 * s) hP
      generalize (g 0 1 * s) / ((p : ℕ) : ℤ) = q at e
      generalize (g 0 1 * s) % ((p : ℕ) : ℤ) = i at e hi0 hip
      have hine : i ≠ 0 := by
        rintro rfl
        have : ((p : ℕ) : ℤ) ∣ g 0 1 * s := ⟨q, by linarith⟩
        rcases hz.dvd_or_dvd this with h | h
        · exact hp01 h
        · apply hz.not_dvd_one
          rw [← hts]
          exact dvd_add (dvd_mul_left _ _) (h.mul_right _)
      have hm : ((p : ℕ) : ℤ) ∣ g 0 1 - 4 * i * u :=
        ⟨g 0 1 * t + 4 * u * q, by linear_combination (-4 * u) * e + (-g 0 1) * hts⟩
      have hlt : i.toNat < (p : ℕ) := by omega
      refine ⟨Sum.inr ⟨i.toNat, hlt⟩, ?_⟩
      have hne : ((⟨i.toNat, hlt⟩ : Fin (p : ℕ)) : ℕ) ≠ 0 := by
        show i.toNat ≠ 0
        omega
      have hc : ((((⟨i.toNat, hlt⟩ : Fin (p : ℕ)) : ℕ)) : ℤ) = i := Int.toNat_of_nonneg hi0
      unfold CRel
      rw [rep_inr_pos N p hp hpN ⟨i.toNat, hlt⟩ hne, repMid_00, repMid_01, hc]
      exact aux_mid _ _ _ u i _ _ hu hm
  · have hcop : IsCoprime (g 0 0) (((p : ℕ) : ℤ) ^ 2) :=
      ((hz.coprime_iff_not_dvd.mpr h1).pow_left).symm
    obtain ⟨u, v, huv⟩ := hcop
    have hP2 : (0 : ℤ) < ((p : ℕ) : ℤ) ^ 2 := by positivity
    have e : g 0 1 * u % (((p : ℕ) : ℤ) ^ 2) + ((p : ℕ) : ℤ) ^ 2 * (g 0 1 * u / (((p : ℕ) : ℤ) ^ 2)) = g 0 1 * u := by rw [Int.emod_def]; ring
    have hb0 := Int.emod_nonneg (g 0 1 * u) hP2.ne'
    have hbp := Int.emod_lt_of_pos (g 0 1 * u) hP2
    generalize (g 0 1 * u) / (((p : ℕ) : ℤ) ^ 2) = Q at e
    generalize (g 0 1 * u) % (((p : ℕ) : ℤ) ^ 2) = b at e hb0 hbp
    have hlt : b.toNat < (p : ℕ) ^ 2 := by
      have : (b.toNat : ℤ) < (((p : ℕ) ^ 2 : ℕ) : ℤ) := by
        push_cast
        rw [Int.toNat_of_nonneg hb0]
        exact hbp
      exact_mod_cast this
    refine ⟨Sum.inl ⟨b.toNat, hlt⟩, ?_⟩
    unfold CRel
    rw [rep_inl, T_zpow_00, T_zpow_01]
    exact aux_T _ _ _ u v Q b.toNat huv (by rw [Int.toNat_of_nonneg hb0]; linarith)

lemma sum_slash_rep (k : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {f : ℍ → ℂ}
    (hf : thetaMultiplierSystem.Transforms k N χ f) (τ : ℍ) :
    ∑ x, thetaMultiplierSystem.slash k N χ (rep N p hp hpN x) (fAlpha p f) τ =
      ((p : ℕ) : ℂ) ^ 2 * heckeFun k N χ p f τ := by
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [Fintype.sum_sum_type]
  have h1 : ∑ b : Fin ((p : ℕ) ^ 2), thetaMultiplierSystem.slash k N χ (rep N p hp hpN (Sum.inl b))
      (fAlpha p f) τ = ∑ b ∈ Finset.range ((p : ℕ) ^ 2), f (affPt 1 (p ^ 2) b τ) := by
    rw [← Fin.sum_univ_eq_sum_range (fun b : ℕ => f (affPt 1 (p ^ 2) b τ)) ((p : ℕ) ^ 2)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [rep_inl]
    exact slash_T_pow k N χ p f b τ
  have h2 : ∀ i : Fin (p : ℕ), thetaMultiplierSystem.slash k N χ (rep N p hp hpN (Sum.inr i))
      (fAlpha p f) τ =
      χ (p : ℕ) * ((epsD (p : ℕ))⁻¹ * (Real.sqrt (p : ℕ) : ℂ)) ^ (2 * k + 1) *
        ((jacobiSym ((i : ℕ) : ℤ) p : ℂ) * f (affPt p p (4 * ((i : ℕ) : ℤ)) τ)) +
      (if i = (⟨0, hp.pos⟩ : Fin (p : ℕ)) then
        χ (p : ℕ) ^ 2 * ((p : ℕ) : ℂ) ^ (2 * k + 1) * f (affPt (p ^ 2) 1 0 τ) else 0) := by
    intro i
    by_cases hi : (i : ℕ) = 0
    · have hi' : i = (⟨0, hp.pos⟩ : Fin (p : ℕ)) := Fin.ext hi
      rw [rep_inr_zero N p hp hpN i hi, slash_repZero k N χ p hp hpN hf _ _ _ τ, if_pos hi', hi]
      simp [jacobiSym.zero_left (show 1 < (p : ℕ) from hp.one_lt)]
    · have hi' : ¬ i = (⟨0, hp.pos⟩ : Fin (p : ℕ)) := fun h => hi (by rw [h])
      rw [rep_inr_pos N p hp hpN i hi, slash_repMid k N χ p hp hpN hf (i : ℕ)
        (not_dvd_of_fin N p hp hpN i hi) _ _ _ τ, if_neg hi']
      ring
  rw [h1, Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_ite_eq' Finset.univ (⟨0, hp.pos⟩ : Fin (p : ℕ))]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (jacobiSym (i : ℤ) p : ℂ) * f (affPt p p (4 * (i : ℤ)) τ))
    (p : ℕ)]
  unfold heckeFun
  rw [zpow_neg]
  simp only [Finset.mem_univ, if_true]
  field_simp
  ring

end Coset2

end HeckeCoset

open HeckeCoset

/-- **$T(p^2)$ preserves the transformation law** for the theta multiplier, $p \nmid 4N$ prime. -/
theorem heckeFun_transforms (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (p : ℕ+) (hp : (p : ℕ).Prime)
    (hpN : ¬ (p : ℕ) ∣ 4 * N) {f : ℍ → ℂ} (hf : thetaMultiplierSystem.Transforms k N χ f) :
    thetaMultiplierSystem.Transforms k N χ (heckeFun k N χ p f) := by
  rw [MultiplierSystem.transforms_iff_slash]
  intro γ hγ
  set M := thetaMultiplierSystem with hM
  set F := fAlpha p f with hF
  have key : ∀ g : SL(2, ℤ), g ∈ Gamma0 (4 * N) → ∀ j, CRel p g (rep N p hp hpN j) →
      M.slash k N χ g F = M.slash k N χ (rep N p hp hpN j) F := by
    intro g hg j hj
    have hmem : g * (rep N p hp hpN j)⁻¹ ∈ Gamma0 (4 * N) :=
      Subgroup.mul_mem _ hg (inv_mem (rep_mem N p hp hpN j))
    have hb := (CRel_iff p g _).mp hj
    have hc := slash_conj k N χ p hp hpN hf hmem hb
    have hg' : g = (g * (rep N p hp hpN j)⁻¹) * rep N p hp hpN j := by group
    conv_lhs => rw [hg']
    rw [M.slash_mul k N χ hmem (rep_mem N p hp hpN j), hc]
  let σ : Fin ((p : ℕ) ^ 2) ⊕ Fin (p : ℕ) → Fin ((p : ℕ) ^ 2) ⊕ Fin (p : ℕ) := fun x =>
    Classical.choose (exists_rel N p hp hpN (rep N p hp hpN x * γ))
  have hσ : ∀ x, CRel p (rep N p hp hpN x * γ) (rep N p hp hpN (σ x)) := fun x =>
    Classical.choose_spec (exists_rel N p hp hpN (rep N p hp hpN x * γ))
  have hinj : Function.Injective σ := by
    intro x x' hxx
    have h1 := hσ x
    have h2 := hσ x'
    rw [hxx] at h1
    have h3 : CRel p (rep N p hp hpN x * γ) (rep N p hp hpN x' * γ) := h1.trans h2.symm
    exact rep_inj N p hp hpN x x' ((CRel_mul_right p _ _ γ).mp h3)
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hinj
  let e : (Fin ((p : ℕ) ^ 2) ⊕ Fin (p : ℕ)) ≃ (Fin ((p : ℕ) ^ 2) ⊕ Fin (p : ℕ)) := Equiv.ofBijective σ hbij
  set S : ℍ → ℂ := ∑ x, M.slash k N χ (rep N p hp hpN x) F with hS
  have hS' : S = ((p : ℕ) : ℂ) ^ 2 • heckeFun k N χ p f := by
    funext τ
    rw [hS, Finset.sum_apply]
    exact sum_slash_rep N p hp hpN k χ hf τ
  have hSinv : M.slash k N χ γ S = S := by
    have e1 : M.slash k N χ γ S = ∑ x, M.slash k N χ γ (M.slash k N χ (rep N p hp hpN x) F) :=
      map_sum (M.slashLin k N χ γ) (fun x => M.slash k N χ (rep N p hp hpN x) F) Finset.univ
    rw [e1]
    have e2 : ∀ x, M.slash k N χ γ (M.slash k N χ (rep N p hp hpN x) F) =
        M.slash k N χ (rep N p hp hpN (e x)) F := by
      intro x
      rw [← M.slash_mul k N χ (rep_mem N p hp hpN x) hγ]
      exact key _ (Subgroup.mul_mem _ (rep_mem N p hp hpN x) hγ) _ (hσ x)
    rw [Finset.sum_congr rfl fun x _ => e2 x]
    exact Equiv.sum_comp e (fun y => M.slash k N χ (rep N p hp hpN y) F)
  have hp2 : ((p : ℕ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hp.ne_zero)
  have h3 : ((p : ℕ) : ℂ) ^ 2 • M.slash k N χ γ (heckeFun k N χ p f) =
      ((p : ℕ) : ℂ) ^ 2 • heckeFun k N χ p f := by
    have := (M.slashLin k N χ γ).map_smul (((p : ℕ) : ℂ) ^ 2) (heckeFun k N χ p f)
    have hSinv' := hSinv
    rw [hS'] at hSinv'
    exact this.symm.trans hSinv'
  exact smul_right_injective _ hp2 h3

end ModularFormsKB.HalfIntegral
