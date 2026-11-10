import ModularFormsKB.Miyake.Sec4_3.Gauss
import Mathlib.Data.FunLike.Fintype
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Auxiliary results for Weil's converse theorem

* `Miyake.eq_of_sum_char_smul_eq_zero`: if $\sum_v \psi(v) H(v) = 0$ for every nontrivial Dirichlet
  character $\psi$ modulo $m$, then $H$ is constant on $(\mathbb Z/m)^\times$ (the orthogonality step at
  the end of the proof of Miyake Lemma 4.3.13).
* `Miyake.fricke_translate_eq_slash`: the function form of Miyake (4.3.23) and (4.3.26):
  $f|_k\alpha(u/m)\,\omega(Nm^2) = g|_k\gamma(m,v)\,\alpha(v/m)$ when $g = f|_k\omega_N$ and $mn - uvN = 1$.
-/

open Complex Filter Asymptotics CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm

noncomputable section

namespace Miyake

/-- **Character orthogonality.** Let $H : \mathbb Z/m \to E$ with $\sum_v \psi(v) H(v) = 0$ for every
nontrivial Dirichlet character $\psi$ modulo $m$. Then $H(v_1) = H(v_2)$ for all units $v_1, v_2$. -/
lemma eq_of_sum_char_smul_eq_zero {m : ℕ} [NeZero m] {E : Type*} [AddCommGroup E] [Module ℂ E]
    (H : ZMod m → E) (hH : ∀ ψ : DirichletCharacter ℂ m, ψ ≠ 1 → ∑ v : ZMod m, ψ v • H v = 0)
    {v₁ v₂ : ZMod m} (h₁ : IsUnit v₁) (h₂ : IsUnit v₂) : H v₁ = H v₂ := by
  have hS : ∑ ψ : DirichletCharacter ℂ m, (ψ v₁⁻¹ - ψ v₂⁻¹) • ∑ v : ZMod m, ψ v • H v = 0 := by
    refine Finset.sum_eq_zero fun ψ _ ↦ ?_
    by_cases hψ : ψ = 1
    · subst hψ
      obtain ⟨w₁, rfl⟩ := h₁
      obtain ⟨w₂, rfl⟩ := h₂
      rw [ZMod.inv_coe_unit, ZMod.inv_coe_unit, MulChar.one_apply (Units.isUnit _),
        MulChar.one_apply (Units.isUnit _), sub_self, zero_smul]
    · rw [hH ψ hψ, smul_zero]
  have hS' : ∑ ψ : DirichletCharacter ℂ m, (ψ v₁⁻¹ - ψ v₂⁻¹) • ∑ v : ZMod m, ψ v • H v =
      ((m.totient : ℂ)) • (H v₁ - H v₂) := by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, sub_mul, Finset.sum_sub_distrib,
      DirichletCharacter.sum_char_inv_mul_char_eq ℂ h₁,
      DirichletCharacter.sum_char_inv_mul_char_eq ℂ h₂, sub_smul, Finset.sum_sub_distrib]
    simp [ite_smul, smul_sub]
  rw [hS'] at hS
  have hφ : (m.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))).ne'
  exact sub_eq_zero.1 ((smul_eq_zero.1 hS).resolve_left hφ)

/-- Every nontrivial Dirichlet character modulo an odd prime or $4$ is primitive. -/
lemma isPrimitive_of_ne_one {m : ℕ} [NeZero m] (hm : IsOddPrimeOrFour m)
    {ψ : DirichletCharacter ℂ m} (hψ : ψ ≠ 1) : ψ.IsPrimitive := by
  have hc1 : ψ.conductor ≠ 1 := fun h ↦ hψ (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h)
  have hdvd := ψ.conductor_dvd_level
  rcases hm with ⟨hp, -⟩ | rfl
  · exact (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left hc1
  · obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show ψ.conductor ∣ 2 ^ 2 from hdvd)
    interval_cases i
    · exact absurd hci hc1
    · exfalso
      obtain ⟨h2, χ₀, hχ₀⟩ := hci ▸ ψ.factorsThrough_conductor
      have : χ₀ = 1 := by
        ext u
        have hu : (u : ZMod 2) = 1 := by
          have := u.isUnit
          generalize (u : ZMod 2) = x at this ⊢
          have : Fact (1 < 2 ^ 1) := ⟨by norm_num⟩
          fin_cases x
          · exact (not_isUnit_zero this).elim
          · rfl
        simp [hu]
      exact hψ (by rw [hχ₀, this, DirichletCharacter.changeLevel_one])
    · exact hci

/-- Translation by $r$ as a slash: $(\varphi|_k\alpha(r))(\tau) = \varphi(\tau + r)$. -/
lemma slash_transl_apply {k : ℤ} (φ : ℍ → ℂ) (r : ℝ) (τ : ℍ) :
    (φ ∣[k] transl r) τ = φ ⟨(τ : ℂ) + r, by simpa using τ.im_pos⟩ := by
  rw [ModularForm.slash_def]
  have hdet : (transl r).det.val = 1 := by simp [transl, Matrix.det_fin_two]
  have hden : denom (transl r) τ = 1 := by simp [denom, transl]
  have hsm : transl r • τ = ⟨(τ : ℂ) + r, by simpa using τ.im_pos⟩ := by
    ext
    rw [UpperHalfPlane.coe_smul_of_det_pos (by simp [hdet])]
    simp [num, denom, transl]
  simp [σ, hden, hsm, hdet]

lemma qSeries_add_int {a : ℕ → ℂ} (z : ℂ) (n : ℤ) : qSeries a (z + n) = qSeries a z := by
  rcases Int.eq_nat_or_neg n with ⟨n, rfl | rfl⟩
  · simpa using qSeries_add_nat (a := a) z n
  · have := qSeries_add_nat (a := a) (z - n) n
    simp only [sub_add_cancel] at this
    push_cast
    rw [← sub_eq_add_neg, this]

/-- `fricke` is linear: it commutes with finite linear combinations. -/
lemma fricke_sum {ι : Type*} (s : Finset ι) (k : ℤ) (M : ℝ) (c : ι → ℂ) (F : ι → ℂ → ℂ) (z : ℂ) :
    fricke k M (fun ζ ↦ ∑ i ∈ s, c i * F i ζ) z = ∑ i ∈ s, c i * fricke k M (F i) z := by
  simp only [fricke, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

lemma fricke_const_mul (k : ℤ) (M : ℝ) (c : ℂ) (F : ℂ → ℂ) (z : ℂ) :
    fricke k M (fun ζ ↦ c * F ζ) z = c * fricke k M F z := by
  simp only [fricke]; ring

lemma fricke_congr {k : ℤ} {M : ℝ} {F G : ℂ → ℂ} (h : ∀ ζ, F ζ = G ζ) (z : ℂ) :
    fricke k M F z = fricke k M G z := by
  simp only [fricke, h]

lemma denom_SL' (γ : SL(2, ℤ)) (w : ℂ) :
    denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map
      (Int.castRingHom ℝ)) γ)) w = ((γ 1 0 : ℤ) : ℂ) * w + ((γ 1 1 : ℤ) : ℂ) := by
  simp [denom]

/-- **Miyake (4.3.23), (4.3.26)** at the level of functions: if $g = f|_k\omega_N$ on $\mathbb H$ and
$mn - uvN = 1$, then
$$\bigl(f(\cdot + u/m)\bigr)\big|_k\omega(Nm^2)\,(z) = \bigl(g|_k\gamma(m,v)\bigr)(z + v/m).$$ -/
lemma fricke_translate_eq_slash {k : ℤ} {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a b : ℕ → ℂ}
    (hg : ∀ z : ℂ, 0 < z.im → fricke k N (qSeries a) z = qSeries b z)
    (u v n : ℤ) (h : (m : ℤ) * n - u * v * N = 1) {z : ℂ} (hz : 0 < z.im) :
    fricke k ((N : ℝ) * (m : ℝ) ^ 2) (fun ζ ↦ qSeries a (ζ + ((u : ℝ) / m : ℝ))) z =
      ((fun τ : ℍ ↦ qSeries b τ) ∣[k] gammaMV N m v u n h)
        ⟨z + ((v : ℝ) / m : ℝ), by simpa using hz⟩ := by
  set w : ℍ := ⟨z + (((v : ℝ) / m : ℝ) : ℂ), by simpa using hz⟩ with hwdef
  rw [ModularForm.SL_slash_apply]
  have hζ := UpperHalfPlane.coe_specialLinearGroup_apply (gammaMV N m v u n h) w
  have hden : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map
      (Int.castRingHom ℝ)) (gammaMV N m v u n h))) (w : ℂ) =
      -((u : ℂ) * N) * (z + v / m) + n := by
    rw [denom_SL']; simp [gammaMV, w]
  have hD0 : (-((u : ℂ) * N) * (z + v / m) + n) ≠ 0 := by
    rw [← hden]; exact denom_ne_zero _ _
  have hζ' : ((gammaMV N m v u n h • w : ℍ) : ℂ) =
      (m * (z + v / m) + -v) / (-((u : ℂ) * N) * (z + v / m) + n) := by
    rw [hζ]; simp [gammaMV, w]
  rw [hden, ← hg _ (gammaMV N m v u n h • w).im_pos, hζ']
  generalize hD : (-((u : ℂ) * N) * (z + v / m) + n) = D at hD0 ⊢
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  have hhC : (m : ℂ) * n - u * v * N = 1 := by exact_mod_cast h
  have hDm : (m : ℂ) * D = 1 - u * N * m * z := by
    rw [← hD]; field_simp; linear_combination hhC
  have hζ2 : (m * (z + v / m) + -v) / D = m * z / D := by
    congr 1; field_simp; ring
  rw [hζ2]
  have hsq : (√((N : ℝ) * (m : ℝ) ^ 2) : ℂ) = m * (√(N : ℝ) : ℂ) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]; push_cast; ring
  have harg : -1 / (((N : ℝ) * (m : ℝ) ^ 2 : ℝ) * z : ℂ) + (((u : ℝ) / m : ℝ) : ℂ) =
      -1 / ((N : ℂ) * (m * z / D)) := by
    push_cast
    field_simp
    linear_combination hDm
  unfold fricke
  beta_reduce
  rw [harg, hsq]
  have e : (m : ℂ) * (√(N : ℝ) : ℂ) * z = ((√(N : ℝ) : ℂ) * (m * z / D)) * D := by
    field_simp
  rw [e, mul_zpow]
  simp only [Complex.ofReal_natCast]
  ring

end Miyake
