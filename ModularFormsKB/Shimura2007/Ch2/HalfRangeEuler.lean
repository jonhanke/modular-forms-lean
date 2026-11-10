import ModularFormsKB.Shimura2007.Ch2.EulerPolynomialProps
import ModularFormsKB.Shimura2007.Ch1.PrimitiveCharacter

/-!
# Shimura 2007, §4.1 and Lemma 4.13: reflection of Euler polynomials and half-range sums

G. Shimura, *Elementary Dirichlet Series and Modular Forms* (Springer 2007), §4.1 (4.3f), (4.3g),
p. 25, and Lemma 4.13 (ii), (iii), (4.29), (4.30), p. 33.

* `eulerPoly_comp_one_sub`: $E_{c,n}(1-t) = (-1)^nE_{c^{-1},n}(t)$ (4.3f), proved by showing that
  both sides solve $p(t+1) + c^{-1}p(t) = (1+c^{-1})t^n$, whose solution is unique for
  $c \ne -1$ (a leading coefficient argument).
* `eulerPoly_eval_zero_inv`: $E_{c^{-1},n}(0) = (-1)^{n+1}cE_{c,n}(0)$ (4.3g).
* Lemma 4.13 (ii), (iii): pairing arguments for the half-range sums, using (4.3f) at $c = 1$,
  and for (iii) Lemma 1.12 (`primitive_apply_one_sub_half`).

$E_{1,n}(x)$ is written `(eulerPoly (1 : ℂ) n).eval x`.
-/

open Polynomial

namespace ModularFormsKB.Shimura2007

section Reflection

variable {K : Type*} [Field K] [CharZero K]

/-- Uniqueness of the solution of $p(t+1) + a\,p(t) = r$ for $a \ne -1$. -/
theorem eq_of_comp_add_one_eq (a : K) (ha : 1 + a ≠ 0) {p q r : K[X]}
    (hp : p.comp (X + 1) + C a * p = r) (hq : q.comp (X + 1) + C a * q = r) : p = q := by
  by_contra hne
  have hD : p - q ≠ 0 := sub_ne_zero.2 hne
  have h1 : (p - q).comp (X + 1) = C (-a) * (p - q) := by
    rw [sub_comp, map_neg]
    linear_combination hp - hq
  have hdeg : (X + 1 : K[X]).natDegree ≠ 0 := by
    have : (X + 1 : K[X]).natDegree = 1 := by compute_degree!
    omega
  have hlc : (X + 1 : K[X]).leadingCoeff = 1 := by
    have := monic_X_add_C (1 : K)
    simpa [Monic] using this
  have h2 := congrArg leadingCoeff h1
  rw [leadingCoeff_comp hdeg, hlc, one_pow, mul_one, leadingCoeff_mul, leadingCoeff_C] at h2
  have h3 : (1 + a) * (p - q).leadingCoeff = 0 := by linear_combination h2
  rcases mul_eq_zero.1 h3 with h | h
  · exact ha h
  · exact hD (leadingCoeff_eq_zero.1 h)

/-- **(4.3f)**: for $c \ne 0, -1$, $E_{c,n}(1-t) = (-1)^nE_{c^{-1},n}(t)$. -/
@[kb "shimura2007" "§4.1, (4.3f), p. 25"]
theorem eulerPoly_comp_one_sub (c : K) (hc0 : c ≠ 0) (hc : 1 + c ≠ 0) (n : ℕ) :
    (eulerPoly c n).comp (1 - X) = ((-1 : K) ^ n) • eulerPoly c⁻¹ n := by
  have hc' : 1 + c⁻¹ ≠ 0 := by
    intro h
    apply hc
    have : c * (1 + c⁻¹) = 0 := by rw [h, mul_zero]
    rw [mul_add, mul_inv_cancel₀ hc0] at this
    linear_combination this
  have h1 := eulerPoly_comp_add_one c hc n
  have h2 : (eulerPoly c n).comp (1 - X) + C c * (eulerPoly c n).comp (-X)
      = C (1 + c) * ((-1) ^ n * X ^ n) := by
    have := congrArg (fun p => p.comp (-X)) h1
    simp only [add_comp, mul_comp, C_comp, comp_assoc, X_pow_comp, X_comp, one_comp] at this
    rw [neg_pow] at this
    have e : (-X + 1 : K[X]) = 1 - X := by ring
    rw [e] at this
    simpa using this
  set E := eulerPoly c n with hE
  -- the candidate
  have hP1 : (C ((-1 : K) ^ n) * E.comp (1 - X)).comp (X + 1) = C ((-1 : K) ^ n) * E.comp (-X) := by
    rw [mul_comp, C_comp, comp_assoc]
    have : ((1 : K[X]) - X).comp (X + 1) = -X := by simp
    rw [this]
  have hu : C c⁻¹ * C c = (1 : K[X]) := by rw [← C_mul, inv_mul_cancel₀ hc0, C_1]
  have hs : (C ((-1 : K) ^ n)) * C ((-1 : K) ^ n) = (1 : K[X]) := by
    rw [← C_mul, ← mul_pow]; simp
  have key : (C ((-1 : K) ^ n) * E.comp (1 - X)).comp (X + 1)
      + C c⁻¹ * (C ((-1 : K) ^ n) * E.comp (1 - X)) = C (1 + c⁻¹) * X ^ n := by
    rw [hP1]
    have h2' : E.comp (1 - X) + C c * E.comp (-X)
        = C (1 + c) * (C ((-1 : K) ^ n) * X ^ n) := by
      rw [h2]; simp
    have hCa : C (1 + c) = 1 + C c := by simp
    have hCb : C (1 + c⁻¹) = 1 + C c⁻¹ := by simp
    rw [hCb]
    rw [hCa] at h2'
    linear_combination (C ((-1 : K) ^ n) * C c⁻¹) * h2'
      + (-(C ((-1 : K) ^ n)) * E.comp (-X) + X ^ n) * hu
      + (C c⁻¹ * (1 + C c) * X ^ n) * hs
  have hq := eulerPoly_comp_add_one c⁻¹ hc' n
  have heq := eq_of_comp_add_one_eq c⁻¹ hc' key hq
  rw [smul_eq_C_mul, ← heq, ← mul_assoc, ← C_mul, ← mul_pow]
  simp

/-- **(4.3g)**: $E_{c^{-1},n}(0) = (-1)^{n+1}c\,E_{c,n}(0)$ for $c \ne 0, -1$ and $n \ge 1$
(for $n = 0$ both sides of (4.3d) at $t=0$ give $E_{c,0}(1)+c = 1+c$ instead). -/
@[kb "shimura2007" "§4.1, (4.3g), p. 25"]
theorem eulerPoly_eval_zero_inv (c : K) (hc0 : c ≠ 0) (hc : 1 + c ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    (eulerPoly c⁻¹ n).eval 0 = (-1) ^ (n + 1) * c * (eulerPoly c n).eval 0 := by
  have h1 := congrArg (eval 0) (eulerPoly_comp_add_one c hc n)
  have h2 := congrArg (eval 0) (eulerPoly_comp_one_sub c hc0 hc n)
  simp only [eval_add, eval_comp, eval_mul, eval_C, eval_X, eval_one, eval_pow, eval_smul,
    smul_eq_mul, eval_sub, zero_add, sub_zero] at h1 h2
  rw [zero_pow (by omega), mul_zero] at h1
  have hsq : ((-1 : K) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  rw [pow_succ]
  linear_combination (-((-1 : K) ^ n)) * h2 + ((-1 : K) ^ n) * h1 + (-(eulerPoly c⁻¹ n).eval 0) * hsq

end Reflection

section HalfRange

private theorem sum_Ico_refl (f : ℕ → ℂ) (N A B : ℕ) (hB : B ≤ N + 1) :
    ∑ a ∈ Finset.Ico A B, f a = ∑ a ∈ Finset.Ico (N + 1 - B) (N + 1 - A), f (N - a) := by
  refine Finset.sum_nbij' (fun a => N - a) (fun a => N - a) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Ico] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Ico] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Ico] at ha; omega
  · intro a ha; simp only [Finset.mem_Ico] at ha; omega
  · intro a ha; simp only [Finset.mem_Ico] at ha; congr 1; omega

private theorem sum_pair_odd (d q : ℕ) (hd : d = 2 * q + 1) (f : ℕ → ℂ) (s : ℂ)
    (hf : ∀ a ∈ Finset.Icc 1 q, f (d - a) = s * f a) :
    ∑ a ∈ Finset.Ico 1 d, f a = (1 + s) * ∑ a ∈ Finset.Icc 1 q, f a := by
  have hI : Finset.Icc 1 q = Finset.Ico 1 (q + 1) := by ext; simp
  rw [hI] at hf ⊢
  rw [← Finset.sum_Ico_consecutive f (show 1 ≤ q + 1 by omega) (show q + 1 ≤ d by omega),
    sum_Ico_refl f d (q + 1) d (by omega)]
  have e1 : d + 1 - d = 1 := by omega
  have e2 : d + 1 - (q + 1) = q + 1 := by omega
  rw [e1, e2, Finset.sum_congr rfl hf, ← Finset.mul_sum]
  ring

private theorem sum_pair_even (m : ℕ) (hm : 1 ≤ m) (f : ℕ → ℂ) (s : ℂ) (h0 : f m = 0)
    (hf : ∀ a ∈ Finset.Ico 1 m, f (2 * m - a) = s * f a) :
    ∑ a ∈ Finset.Icc 1 (2 * m - 1), f a = (1 + s) * ∑ a ∈ Finset.Ico 1 m, f a := by
  have hI : Finset.Icc 1 (2 * m - 1) = Finset.Ico 1 (2 * m) := by ext; simp; omega
  rw [hI, ← Finset.sum_Ico_consecutive f (show 1 ≤ m by omega) (show m ≤ 2 * m by omega),
    Finset.sum_eq_sum_Ico_succ_bot (show m < 2 * m by omega), h0,
    sum_Ico_refl f (2 * m) (m + 1) (2 * m) (by omega)]
  have e1 : 2 * m + 1 - 2 * m = 1 := by omega
  have e2 : 2 * m + 1 - (m + 1) = m := by omega
  rw [e1, e2, Finset.sum_congr rfl hf, ← Finset.mul_sum]
  ring

private theorem eulerPoly_one_reflect (n : ℕ) (x : ℂ) :
    (eulerPoly (1 : ℂ) n).eval (1 - x) = (-1) ^ n * (eulerPoly (1 : ℂ) n).eval x := by
  have h := congrArg (eval x) (eulerPoly_comp_one_sub (1 : ℂ) one_ne_zero (by norm_num) n)
  simpa [eval_comp, inv_one] using h

private theorem neg_one_pow_sq (n : ℕ) : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by
  rw [← mul_pow]; simp

private theorem odd_pair_aux {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) {k : ℕ}
    (hχk : χ (-1) = (-1) ^ k) (hd : Odd d) (n a : ℕ) (ha : a ≤ d) :
    (-1 : ℂ) ^ (d - a) * χ ((d - a : ℕ) : ZMod d) *
        (eulerPoly (1 : ℂ) n).eval (((d - a : ℕ) : ℂ) / d)
      = -((-1) ^ k * (-1) ^ n) *
        ((-1 : ℂ) ^ a * χ (a : ZMod d) * (eulerPoly (1 : ℂ) n).eval ((a : ℂ) / d)) := by
  have hcast : ((d - a : ℕ) : ZMod d) = -(a : ZMod d) := by
    rw [Nat.cast_sub ha, ZMod.natCast_self, zero_sub]
  have hχ : χ (-(a : ZMod d)) = χ (-1) * χ (a : ZMod d) := by
    rw [← map_mul, neg_one_mul]
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  have hE : ((d - a : ℕ) : ℂ) / d = 1 - (a : ℂ) / d := by
    rw [Nat.cast_sub ha]; field_simp
  have e : (-1 : ℂ) ^ (d - a) = -(-1) ^ a := by
    have h := pow_add (-1 : ℂ) (d - a) a
    rw [Nat.sub_add_cancel ha, hd.neg_one_pow] at h
    have hyy := neg_one_pow_sq a
    linear_combination (-((-1 : ℂ) ^ a)) * h + (-((-1 : ℂ) ^ (d - a))) * hyy
  rw [hcast, hχ, hχk, hE, eulerPoly_one_reflect, e]
  ring

/-- **Lemma 4.13 (ii)**, (4.29), case $n = k-1$: for $\chi$ a nontrivial primitive character
modulo an odd $d$, $k \ge 1$, $\chi(-1) = (-1)^k$ and $q = (d-1)/2$,
$$\sum_{a=1}^{d-1}(-1)^a\chi(a)E_{1,k-1}(a/d) = 2\sum_{a=1}^{q}(-1)^a\chi(a)E_{1,k-1}(a/d).$$ -/
@[kb "shimura2007" "Lemma 4.13 (ii), (4.29), p. 33"]
theorem sum_alt_eulerPoly_pred {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    (_hχp : χ.IsPrimitive) (_hχ1 : χ ≠ 1) {k : ℕ} (hk : 1 ≤ k) (hχk : χ (-1) = (-1) ^ k)
    (hd : Odd d) {n : ℕ} (hn : n = k - 1) :
    ∑ a ∈ Finset.Ico 1 d, (-1 : ℂ) ^ a * χ a * (eulerPoly (1 : ℂ) n).eval ((a : ℂ) / d)
      = 2 * ∑ a ∈ Finset.Icc 1 ((d - 1) / 2),
          (-1 : ℂ) ^ a * χ a * (eulerPoly (1 : ℂ) n).eval ((a : ℂ) / d) := by
  obtain ⟨q, hq⟩ := hd
  have hq' : (d - 1) / 2 = q := by omega
  have hkn : k = n + 1 := by omega
  have hs : -((-1 : ℂ) ^ k * (-1) ^ n) = 1 := by
    rw [hkn, pow_succ]; linear_combination neg_one_pow_sq n
  rw [hq']
  have := sum_pair_odd d q hq
    (fun a : ℕ => (-1 : ℂ) ^ a * χ a * (eulerPoly (1 : ℂ) n).eval ((a : ℂ) / d)) 1 (by
      intro a ha
      have ha' := Finset.mem_Icc.1 ha
      have := odd_pair_aux χ hχk ⟨q, hq⟩ n a (by omega)
      rw [hs] at this
      simpa using this)
  rw [this]; ring

/-- **Lemma 4.13 (ii)**, (4.29), case $n = k$: with the same hypotheses,
$\sum_{a=1}^{d-1}(-1)^a\chi(a)E_{1,k}(a/d) = 0$. -/
@[kb "shimura2007" "Lemma 4.13 (ii), (4.29), p. 33"]
theorem sum_alt_eulerPoly_self {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    (_hχp : χ.IsPrimitive) (_hχ1 : χ ≠ 1) {k : ℕ} (_hk : 1 ≤ k) (hχk : χ (-1) = (-1) ^ k)
    (hd : Odd d) {n : ℕ} (hn : n = k) :
    ∑ a ∈ Finset.Ico 1 d, (-1 : ℂ) ^ a * χ a * (eulerPoly (1 : ℂ) n).eval ((a : ℂ) / d) = 0 := by
  obtain ⟨q, hq⟩ := hd
  have hs : -((-1 : ℂ) ^ k * (-1) ^ n) = -1 := by
    rw [hn]; linear_combination (-1 : ℂ) * neg_one_pow_sq k
  have := sum_pair_odd d q hq
    (fun a : ℕ => (-1 : ℂ) ^ a * χ a * (eulerPoly (1 : ℂ) n).eval ((a : ℂ) / d)) (-1) (by
      intro a ha
      have ha' := Finset.mem_Icc.1 ha
      have := odd_pair_aux χ hχk ⟨q, hq⟩ n a (by omega)
      rw [hs] at this
      simpa using this)
  rw [this]; ring

private theorem chi_one_sub_half (d₀ : ℕ) (hd₀ : 0 < d₀) (χ : DirichletCharacter ℂ (4 * d₀))
    (hχ : χ.IsPrimitive) :
    χ ((1 : ZMod (4 * d₀)) - ((2 * d₀ : ℕ) : ZMod (4 * d₀))) = -1 := by
  have key : ∀ (m : ℕ) (h : m = 2 * (2 * d₀)) (ψ : DirichletCharacter ℂ m), ψ.IsPrimitive →
      ψ ((1 : ZMod m) - ((2 * d₀ : ℕ) : ZMod m)) = -1 := by
    intro m h
    subst h
    intro ψ hψ
    exact primitive_apply_one_sub_half (by omega) ψ hψ
  exact key (4 * d₀) (by ring) χ hχ

private theorem chi_eq_zero_of_dvd (d₀ : ℕ) (χ : DirichletCharacter ℂ (4 * d₀)) (m g : ℕ)
    (hg : 1 < g) (h1 : g ∣ m) (h2 : g ∣ 4 * d₀) : χ (m : ZMod (4 * d₀)) = 0 := by
  apply MulChar.map_nonunit
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.not_coprime_of_dvd_of_dvd hg h1 h2

private theorem pair_aux_four (d₀ : ℕ) (hd₀ : 1 < d₀) (χ : DirichletCharacter ℂ (4 * d₀))
    (hχp : χ.IsPrimitive) {k : ℕ} (hχk : χ (-1) = (-1) ^ k) (n a : ℕ) (ha : a ≤ 2 * d₀) :
    χ ((2 * d₀ - a : ℕ) : ZMod (4 * d₀)) *
        (eulerPoly (1 : ℂ) n).eval (2 * ((2 * d₀ - a : ℕ) : ℂ) / ((4 * d₀ : ℕ) : ℂ))
      = -((-1) ^ k * (-1) ^ n) *
        (χ (a : ZMod (4 * d₀)) * (eulerPoly (1 : ℂ) n).eval (2 * (a : ℂ) / ((4 * d₀ : ℕ) : ℂ))) := by
  have hd0 : (d₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hE : 2 * ((2 * d₀ - a : ℕ) : ℂ) / ((4 * d₀ : ℕ) : ℂ)
      = 1 - 2 * (a : ℂ) / ((4 * d₀ : ℕ) : ℂ) := by
    rw [Nat.cast_sub ha]; push_cast; field_simp; ring
  rw [hE, eulerPoly_one_reflect]
  rcases Nat.even_or_odd a with he | ho
  · have h1 : χ (a : ZMod (4 * d₀)) = 0 := by
      obtain ⟨r, hr⟩ := he
      exact chi_eq_zero_of_dvd d₀ χ a 2 (by norm_num) ⟨r, by omega⟩ ⟨2 * d₀, by ring⟩
    have h2 : χ ((2 * d₀ - a : ℕ) : ZMod (4 * d₀)) = 0 := by
      obtain ⟨r, hr⟩ := he
      exact chi_eq_zero_of_dvd d₀ χ _ 2 (by norm_num) ⟨d₀ - r, by omega⟩ ⟨2 * d₀, by ring⟩
    rw [h1, h2]; ring
  · obtain ⟨t, ht⟩ := ho
    have h4 : (4 : ZMod (4 * d₀)) * (d₀ : ZMod (4 * d₀)) = 0 := by
      have := ZMod.natCast_self (4 * d₀)
      push_cast at this
      exact this
    have hcast : ((2 * d₀ - a : ℕ) : ZMod (4 * d₀))
        = ((1 : ZMod (4 * d₀)) - ((2 * d₀ : ℕ) : ZMod (4 * d₀))) * (-1) * (a : ZMod (4 * d₀)) := by
      rw [Nat.cast_sub ha, ht]
      push_cast
      linear_combination (-(t : ZMod (4 * d₀))) * h4
    rw [hcast, map_mul, map_mul, chi_one_sub_half d₀ (by omega) χ hχp, hχk]
    ring

/-- **Lemma 4.13 (iii)**, (4.30), case $n = k-1$: for $\chi$ a nontrivial primitive character
modulo $d = 4d_0$ with $d_0 > 1$, $k \ge 1$, $\chi(-1) = (-1)^k$ and $q = (d-1)/2$,
$$\sum_{a=1}^{q}\chi(a)E_{1,k-1}(2a/d) = 2\sum_{a=1}^{d_0-1}\chi(a)E_{1,k-1}(2a/d).$$ -/
@[kb "shimura2007" "Lemma 4.13 (iii), (4.30), p. 33"]
theorem sum_eulerPoly_four_pred {d₀ : ℕ} (hd₀ : 1 < d₀) [NeZero (4 * d₀)]
    (χ : DirichletCharacter ℂ (4 * d₀)) (hχp : χ.IsPrimitive) (_hχ1 : χ ≠ 1) {k : ℕ}
    (hk : 1 ≤ k) (hχk : χ (-1) = (-1) ^ k) {n : ℕ} (hn : n = k - 1) :
    ∑ a ∈ Finset.Icc 1 ((4 * d₀ - 1) / 2),
        χ a * (eulerPoly (1 : ℂ) n).eval (2 * (a : ℂ) / ((4 * d₀ : ℕ) : ℂ))
      = 2 * ∑ a ∈ Finset.Ico 1 d₀,
        χ a * (eulerPoly (1 : ℂ) n).eval (2 * (a : ℂ) / ((4 * d₀ : ℕ) : ℂ)) := by
  have hq : (4 * d₀ - 1) / 2 = 2 * d₀ - 1 := by omega
  have hkn : k = n + 1 := by omega
  have hs : -((-1 : ℂ) ^ k * (-1) ^ n) = 1 := by
    rw [hkn, pow_succ]; linear_combination neg_one_pow_sq n
  rw [hq]
  have h0 : χ (d₀ : ZMod (4 * d₀)) = 0 :=
    chi_eq_zero_of_dvd d₀ χ d₀ d₀ hd₀ dvd_rfl ⟨4, by ring⟩
  rw [sum_pair_even d₀ (by omega)
    (fun a : ℕ => χ a * (eulerPoly (1 : ℂ) n).eval (2 * (a : ℂ) / ((4 * d₀ : ℕ) : ℂ))) 1
    (by simp [h0]) (by
      intro a ha
      have ha' := Finset.mem_Ico.1 ha
      have := pair_aux_four d₀ hd₀ χ hχp hχk n a (by omega)
      rw [hs] at this
      simpa using this)]
  ring

/-- **Lemma 4.13 (iii)**, (4.30), case $n = k$: with the same hypotheses,
$\sum_{a=1}^{q}\chi(a)E_{1,k}(2a/d) = 0$. -/
@[kb "shimura2007" "Lemma 4.13 (iii), (4.30), p. 33"]
theorem sum_eulerPoly_four_self {d₀ : ℕ} (hd₀ : 1 < d₀) [NeZero (4 * d₀)]
    (χ : DirichletCharacter ℂ (4 * d₀)) (hχp : χ.IsPrimitive) (_hχ1 : χ ≠ 1) {k : ℕ}
    (_hk : 1 ≤ k) (hχk : χ (-1) = (-1) ^ k) {n : ℕ} (hn : n = k) :
    ∑ a ∈ Finset.Icc 1 ((4 * d₀ - 1) / 2),
        χ a * (eulerPoly (1 : ℂ) n).eval (2 * (a : ℂ) / ((4 * d₀ : ℕ) : ℂ)) = 0 := by
  have hq : (4 * d₀ - 1) / 2 = 2 * d₀ - 1 := by omega
  have hs : -((-1 : ℂ) ^ k * (-1) ^ n) = -1 := by
    rw [hn]; linear_combination (-1 : ℂ) * neg_one_pow_sq k
  rw [hq]
  have h0 : χ (d₀ : ZMod (4 * d₀)) = 0 :=
    chi_eq_zero_of_dvd d₀ χ d₀ d₀ hd₀ dvd_rfl ⟨4, by ring⟩
  rw [sum_pair_even d₀ (by omega)
    (fun a : ℕ => χ a * (eulerPoly (1 : ℂ) n).eval (2 * (a : ℂ) / ((4 * d₀ : ℕ) : ℂ))) (-1)
    (by simp [h0]) (by
      intro a ha
      have ha' := Finset.mem_Ico.1 ha
      have := pair_aux_four d₀ hd₀ χ hχp hχk n a (by omega)
      rw [hs] at this
      simpa using this)]
  ring

end HalfRange

end ModularFormsKB.Shimura2007
