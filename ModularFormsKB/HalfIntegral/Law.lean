/-
# The weight-½ transformation law of $\theta$ on all of $\Gamma_0(4)$

We prove `ThetaTransformationLaw`: $\theta(\gamma z) = j(\gamma, z)\,\theta(z)$ for every
$\gamma \in \Gamma_0(4)$ and $z \in \mathbb H$, with $j$ the explicit multiplier `thetaMult`.

**Route.** Write $\mathcal L(\gamma)$ for "the law holds for $\gamma$ at every $z$". For
$X \in \{T, U\}$, $T = \begin{pmatrix}1&1\\0&1\end{pmatrix}$, $U = \begin{pmatrix}1&0\\4&1\end{pmatrix}$, the identity
$j(\gamma X, z)\,\theta(z) = j(\gamma, Xz)\,\theta(Xz)$ (from `thetaMultCD_add_right`, `theta_add_one`, and from
`thetaMultCD_U`, `theta_U`) gives $\mathcal L(\gamma X) \iff \mathcal L(\gamma)$ (`lawAt_mul_T_iff`, `lawAt_mul_U_iff`).
Then a Euclidean descent on $|c| + |d|$: if $2|d| > |c|$ a step $d \mapsto d \pm c$ lowers $|d|$; if $2|d| < |c|$ a step
$c \mapsto c \pm 4d$ lowers $|c|$ ($2|d| = |c|$ is impossible since $4 \mid c$ and $d$ is odd); at $c = 0$,
$\gamma = \pm T^b$ and the law is periodicity of $\theta$ together with $j(\pm T^b, z) = 1$.
This amounts to $\Gamma_0(4) = \langle -1, T, U\rangle$ without stating it.

**Index shift.** Matrix entries are 0-based: $c = \gamma_{1,0}$, $d = \gamma_{1,1}$.
-/
import ModularFormsKB.HalfIntegral.Branch
import ModularFormsKB.HalfIntegral.Symbol

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup ModularGroup

local notation "ℍ" => UpperHalfPlane

/-- $U = \begin{pmatrix}1&0\\4&1\end{pmatrix} \in \Gamma_0(4)$. -/
def U4 : SL(2, ℤ) := ⟨!![1, 0; 4, 1], by norm_num [Matrix.det_fin_two]⟩

lemma coe_U4 : (U4 : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 4, 1] := rfl

lemma coe_U4_inv : ((U4⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -4, 1] := by
  simp [Matrix.SpecialLinearGroup.coe_inv, coe_U4, Matrix.adjugate_fin_two]

lemma U4_mem : U4 ∈ Gamma0 4 := by
  rw [Gamma0_mem]; simp [U4]; decide

lemma T_mem_Gamma0 (N : ℕ) : T ∈ Gamma0 N := by
  rw [Gamma0_mem]; simp [ModularGroup.coe_T]

lemma det_entries (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := Matrix.SpecialLinearGroup.det_coe γ
  rwa [Matrix.det_fin_two] at this

/-- For $\gamma \in \Gamma_0(4)$, $4 \mid c$. -/
lemma Gamma0_four_dvd {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) : (4 : ℤ) ∣ γ 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp (by exact_mod_cast (Gamma0_mem).mp hγ)

/-- For $\gamma \in \Gamma_0(4)$, $d$ is odd. -/
lemma Gamma0_four_odd {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) : Odd (γ 1 1) := by
  obtain ⟨k, hk⟩ := Gamma0_four_dvd hγ
  have h := det_entries γ
  rw [hk] at h
  rw [Int.odd_iff]
  rcases Int.emod_two_eq_zero_or_one (γ 1 1) with h2 | h2
  · obtain ⟨t, ht⟩ := Int.dvd_of_emod_eq_zero h2
    rw [ht] at h
    have h3 : 2 * (t * γ 0 0 - 2 * (γ 0 1 * k)) = 1 := by linarith
    omega
  · exact h2

lemma coe_T_smul' (τ : ℍ) : ((T • τ : ℍ) : ℂ) = τ + 1 := by
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]; push_cast; ring

lemma coe_U4_smul (τ : ℍ) : ((U4 • τ : ℍ) : ℂ) = τ / (4 * τ + 1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp [U4]

/-- The law for a single $\gamma$, at every point. -/
def LawAt (γ : SL(2, ℤ)) : Prop := ∀ τ : ℍ, theta ↑(γ • τ) = thetaMult γ τ * theta τ

/-- If $j(\gamma X, z)\theta(z) = j(\gamma, Xz)\theta(Xz)$ for all $z$, the law for $\gamma X$ and for $\gamma$ are equivalent. -/
lemma lawAt_mul_iff {γ X : SL(2, ℤ)}
    (hK : ∀ τ : ℍ, thetaMult (γ * X) τ * theta τ = thetaMult γ ↑(X • τ) * theta ↑(X • τ)) :
    LawAt (γ * X) ↔ LawAt γ := by
  constructor
  · intro h τ
    have := h (X⁻¹ • τ)
    rw [hK, mul_smul, smul_inv_smul] at this
    exact this
  · intro h τ
    rw [mul_smul, h, hK]

lemma mul_T_10 (γ : SL(2, ℤ)) : (γ * T) 1 0 = γ 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T]

lemma mul_T_11 (γ : SL(2, ℤ)) : (γ * T) 1 1 = γ 1 1 + γ 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T]; ring

lemma mul_Tinv_10 (γ : SL(2, ℤ)) : (γ * T⁻¹) 1 0 = γ 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma mul_Tinv_11 (γ : SL(2, ℤ)) : (γ * T⁻¹) 1 1 = γ 1 1 - γ 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

lemma mul_U4_10 (γ : SL(2, ℤ)) : (γ * U4) 1 0 = γ 1 0 + 4 * γ 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_U4]; simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

lemma mul_U4_11 (γ : SL(2, ℤ)) : (γ * U4) 1 1 = γ 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_U4]; simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma mul_U4inv_10 (γ : SL(2, ℤ)) : (γ * U4⁻¹) 1 0 = γ 1 0 - 4 * γ 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_U4_inv]; simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

lemma mul_U4inv_11 (γ : SL(2, ℤ)) : (γ * U4⁻¹) 1 1 = γ 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_U4_inv]; simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- $\mathcal L(\gamma T) \iff \mathcal L(\gamma)$ for $\gamma \in \Gamma_0(4)$. -/
theorem lawAt_mul_T_iff {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) : LawAt (γ * T) ↔ LawAt γ := by
  refine lawAt_mul_iff fun τ => ?_
  rw [coe_T_smul', theta_add_one]
  unfold thetaMult
  rw [mul_T_10, mul_T_11, thetaMultCD_add_right (Gamma0_four_dvd hγ) (Gamma0_four_odd hγ)]

/-- $\mathcal L(\gamma U) \iff \mathcal L(\gamma)$ for $\gamma \in \Gamma_0(4)$. -/
theorem lawAt_mul_U_iff {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) : LawAt (γ * U4) ↔ LawAt γ := by
  refine lawAt_mul_iff fun τ => ?_
  rw [coe_U4_smul, theta_U _ τ.im_pos]
  unfold thetaMult
  rw [mul_U4_10, mul_U4_11, thetaMultCD_U (Gamma0_four_odd hγ) _ τ.im_pos]
  ring

/-- $\theta(z + n) = \theta(z)$ for $n \in \mathbb Z$. -/
lemma theta_add_int (z : ℂ) (n : ℤ) : theta (z + n) = theta z := by
  have hp : Function.Periodic theta 1 := theta_add_one
  simpa using hp.int_mul n z

/-- The law when $c = 0$, i.e. $\gamma = \pm T^b$. -/
lemma lawAt_of_c_zero {γ : SL(2, ℤ)} (hc : γ 1 0 = 0) : LawAt γ := by
  intro τ
  have h := det_entries γ
  rw [hc, mul_zero, sub_zero] at h
  have hd : γ 1 1 = 1 ∨ γ 1 1 = -1 := Int.eq_one_or_neg_one_of_mul_eq_one' h |>.elim
    (fun h' => Or.inl h'.2) (fun h' => Or.inr h'.2)
  have ha : γ 0 0 = γ 1 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with h' | h' <;> rw [h'.1, h'.2]
  unfold thetaMult
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, hc]
  rcases hd with hd | hd
  · rw [hd, thetaMultCD_zero_one]
    rw [hd] at ha
    have : ((algebraMap ℤ ℝ (γ 0 0) : ℂ) * τ + (algebraMap ℤ ℝ (γ 0 1) : ℂ)) /
        ((algebraMap ℤ ℝ 0 : ℂ) * τ + (algebraMap ℤ ℝ 1 : ℂ)) = (τ : ℂ) + (γ 0 1 : ℤ) := by
      simp [ha]
    rw [this, theta_add_int, one_mul]
  · rw [hd, thetaMultCD_zero_neg_one]
    rw [hd] at ha
    have : ((algebraMap ℤ ℝ (γ 0 0) : ℂ) * τ + (algebraMap ℤ ℝ (γ 0 1) : ℂ)) /
        ((algebraMap ℤ ℝ 0 : ℂ) * τ + (algebraMap ℤ ℝ (-1) : ℂ)) = (τ : ℂ) + (-γ 0 1 : ℤ) := by
      simp [ha]; ring
    rw [this, theta_add_int, one_mul]

/-- **The weight-½ transformation law of $\theta$ on $\Gamma_0(4)$:** $\theta(\gamma z) = j(\gamma, z)\,\theta(z)$ for all
$\gamma \in \Gamma_0(4)$, $z \in \mathbb H$, with $j(\gamma,z) = \varepsilon_d^{-1}(c/d)(cz+d)^{1/2}$ (Shimura 1973 `shimura1973`,
Prop. 2.2). Proved by descent through `lawAt_mul_T_iff` and `lawAt_mul_U_iff`. -/
@[kb "shimura1973" "the weight-1/2 transformation law of theta on Gamma0(4) [unverified]"]
theorem theta_transformationLaw : ThetaTransformationLaw := by
  suffices H : ∀ n : ℕ, ∀ γ ∈ Gamma0 4, (γ 1 0).natAbs + (γ 1 1).natAbs = n → LawAt γ from
    fun γ hγ => H _ γ hγ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro γ hγ hn
  obtain ⟨k, hk⟩ := Gamma0_four_dvd hγ
  obtain ⟨t, ht⟩ := Gamma0_four_odd hγ
  rcases eq_or_ne (γ 1 0) 0 with hc0 | hc0
  · exact lawAt_of_c_zero hc0
  have hd0 : γ 1 1 ≠ 0 := by omega
  have hT := T_mem_Gamma0 4
  have hTi : T⁻¹ ∈ Gamma0 4 := inv_mem hT
  have hUi : U4⁻¹ ∈ Gamma0 4 := inv_mem U4_mem
  have sT : LawAt (γ * T) → LawAt γ := (lawAt_mul_T_iff hγ).mp
  have sU : LawAt (γ * U4) → LawAt γ := (lawAt_mul_U_iff hγ).mp
  have sTi : LawAt (γ * T⁻¹) → LawAt γ := fun h => by
    have e : γ = γ * T⁻¹ * T := by group
    rw [e]; exact (lawAt_mul_T_iff (mul_mem hγ hTi)).mpr h
  have sUi : LawAt (γ * U4⁻¹) → LawAt γ := fun h => by
    have e : γ = γ * U4⁻¹ * U4 := by group
    rw [e]; exact (lawAt_mul_U_iff (mul_mem hγ hUi)).mpr h
  rcases lt_or_gt_of_ne hc0 with hc | hc <;> rcases lt_or_gt_of_ne hd0 with hd | hd <;>
  by_cases h2 : (γ 1 0).natAbs < 2 * (γ 1 1).natAbs <;>
  first
  | exact sT (ih _ (by rw [mul_T_10, mul_T_11]; omega) _ (mul_mem hγ hT) rfl)
  | exact sTi (ih _ (by rw [mul_Tinv_10, mul_Tinv_11]; omega) _ (mul_mem hγ hTi) rfl)
  | exact sU (ih _ (by rw [mul_U4_10, mul_U4_11]; omega) _ (mul_mem hγ U4_mem) rfl)
  | exact sUi (ih _ (by rw [mul_U4inv_10, mul_U4inv_11]; omega) _ (mul_mem hγ hUi) rfl)

end ModularFormsKB.HalfIntegral
