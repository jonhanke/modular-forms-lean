/-
# Unary theta series: $q$-expansion, support on one square class, linear independence

For a Dirichlet character $\psi$ mod $r$ with parity $\nu$ (`charParity`: $\nu = 0$ if $\psi(-1) = 1$, else $\nu = 1$) and $t \ge 1$, the **unary theta series**
$$\theta_{\psi,t}(z) = \sum_{n\in\mathbb Z}\psi(n)\,n^\nu\,e(tn^2z) = \psi(0)0^\nu + \sum_{m\ge1}2\psi(m)m^\nu q^{tm^2}$$
(Serre–Stark 1977 `serrestark1977`, §2 for $\nu = 0$; Shimura 1973 `shimura1973`, §2 for both parities [unverified]).
It is `thetaTwist` of `Abstract/ShimuraRankin.lean` with $\psi$ replaced by $\bar\psi$ (`unaryTheta_eq_thetaTwist`);
Serre–Stark write the character without the bar, and so does this file.

Proved here, with no inputs:
- the $q$-expansion `hasQExp_unaryTheta`, with coefficients `unaryThetaCoeff`: $2\psi(m)m^\nu$ at $tm^2$ ($m \ge 1$), the
  constant $\psi(0)0^\nu$, and $0$ elsewhere (`unaryThetaCoeff_mul_sq`, `unaryThetaCoeff_eq_zero_of_not`);
- **linear independence** (`linearIndependent_unaryThetaCoeff`, `linearIndependent_unaryTheta`): for a level $L$ and
  a set of pairs $(\Phi, t)$ with $\Phi$ a character mod $L$ of parity $\nu$ and $1 \le t \mid L$, the series
  $\theta_{\Phi^\ast,t}$ ($\Phi^\ast$ the primitive character inducing $\Phi$) are linearly independent. This is the
  independence half of Serre–Stark's Theorem A. The proof (ours; Serre–Stark's §4 argument was not available to check
  [unverified]) takes a relation, the least $t_0$ with a nonzero coefficient, and reads the coefficient at $t_0m^2$ for $m$
  prime to $L$: only pairs with $t = t_0$ contribute, so $\sum c_\Phi\Phi(m) = 0$ on $(\mathbb Z/L)^\times$, and distinct
  characters are linearly independent (Dedekind, `linearIndependent_monoidHom`).
-/
import ModularFormsKB.HalfIntegral.Rankin.Theta
import ModularFormsKB.HalfIntegral.QExpUnique

namespace ModularFormsKB.HalfIntegral

open Complex
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- **The unary theta series** $\theta_{\psi,t}(z) = \sum_{n\in\mathbb Z}\psi(n)n^\nu e(tn^2z)$, $\nu$ the parity of $\psi$
(Serre–Stark 1977 `serrestark1977`, §2; Shimura 1973 `shimura1973`, §2 [unverified]). -/
noncomputable def unaryTheta {r : ℕ} (ψ : DirichletCharacter ℂ r) (t : ℕ) (z : ℂ) : ℂ :=
  ∑' n : ℤ, ψ (n : ZMod r) * (n : ℂ) ^ charParity ψ * cexp (2 * π * I * t * (n : ℂ) ^ 2 * z)

/-- The parity of $\bar\psi$ is that of $\psi$. -/
theorem charParity_inv {r : ℕ} (ψ : DirichletCharacter ℂ r) : charParity ψ⁻¹ = charParity ψ := by
  have h5 : ψ (-1) * ψ (-1) = 1 := by rw [← map_mul]; simp
  have h2 : ψ⁻¹ (-1) = ψ (-1) := by
    rw [MulChar.inv_apply_eq_inv']
    exact inv_eq_of_mul_eq_one_right h5
  unfold charParity
  rw [h2]

/-- $\theta_{\psi,t}$ is Shimura's twisted theta series for $\bar\psi$. -/
theorem unaryTheta_eq_thetaTwist {r : ℕ} (ψ : DirichletCharacter ℂ r) (t : ℕ) :
    unaryTheta ψ t = thetaTwist ψ⁻¹ t := by
  funext z
  unfold unaryTheta thetaTwist
  rw [charParity_inv, inv_inv]

/-- **The coefficients of $\theta_{\psi,t}$:** $\psi(0)0^\nu$ at $0$; $2\psi(m)m^\nu$ at $n = tm^2$ with $m \ge 1$, where
$m = \sqrt{n/t}$; $0$ at the other $n$. -/
noncomputable def unaryThetaCoeff {r : ℕ} (ψ : DirichletCharacter ℂ r) (t : ℕ) (n : ℕ) : ℂ :=
  if n = 0 then ψ 0 * (0 : ℂ) ^ charParity ψ
  else if t * Nat.sqrt (n / t) ^ 2 = n then
    2 * ψ (Nat.sqrt (n / t) : ZMod r) * (Nat.sqrt (n / t) : ℂ) ^ charParity ψ
  else 0

theorem unaryThetaCoeff_mul_sq {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t) {m : ℕ} (hm : 1 ≤ m) :
    unaryThetaCoeff ψ t (t * m ^ 2) = 2 * ψ (m : ZMod r) * (m : ℂ) ^ charParity ψ := by
  have hn : t * m ^ 2 ≠ 0 := by positivity
  have hd : t * m ^ 2 / t = m ^ 2 := Nat.mul_div_cancel_left _ ht
  have hs : Nat.sqrt (m ^ 2) = m := Nat.sqrt_eq' m
  unfold unaryThetaCoeff
  rw [if_neg hn, hd, hs, if_pos rfl]

/-- **Support on one square class:** $\theta_{\psi,t}$ has no coefficient outside $\{0\} \cup t\cdot\{m^2\}$. -/
theorem unaryThetaCoeff_eq_zero_of_not {r : ℕ} (ψ : DirichletCharacter ℂ r) {t n : ℕ} (hn : n ≠ 0)
    (h : ¬ ∃ m : ℕ, n = t * m ^ 2) : unaryThetaCoeff ψ t n = 0 := by
  unfold unaryThetaCoeff
  rw [if_neg hn, if_neg]
  intro h'
  exact h ⟨_, h'.symm⟩

/-- **The $q$-expansion of the unary theta series:** $\theta_{\psi,t} = \sum_n a(n)q^n$ with $a$ = `unaryThetaCoeff`. -/
theorem hasQExp_unaryTheta {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t) :
    Abstract.HasQExp (fun τ : ℍ ↦ unaryTheta ψ t τ) (unaryThetaCoeff ψ t) := by
  intro τ
  set T : ℤ → ℂ := fun n ↦
    ψ (n : ZMod r) * (n : ℂ) ^ charParity ψ * cexp (2 * π * I * t * (n : ℂ) ^ 2 * τ) with hTdef
  have hsum : Summable T := by
    have := summable_norm_thetaTwist ψ⁻¹ ht τ
    simp only [inv_inv, charParity_inv] at this
    exact this.of_norm
  have hT : HasSum T (unaryTheta ψ t τ) := by
    unfold unaryTheta
    exact hsum.hasSum
  have hneg : ∀ m : ℕ, T (-(m : ℤ)) = T m := by
    intro m
    have h := apply_neg_one_mul_pow_charParity ψ
    have e1 : (((-(m : ℤ) : ℤ)) : ZMod r) = (-1) * ((m : ℤ) : ZMod r) := by push_cast; ring
    have e2 : (((-(m : ℤ) : ℤ)) : ℂ) = (-1) * ((m : ℤ) : ℂ) := by push_cast; ring
    have e3 : (((-(m : ℤ) : ℤ)) : ℂ) ^ 2 = ((m : ℤ) : ℂ) ^ 2 := by push_cast; ring
    simp only [hTdef]
    rw [e3, e1, e2, map_mul, mul_pow]
    linear_combination (ψ ((m : ℤ) : ZMod r) * ((m : ℤ) : ℂ) ^ charParity ψ *
      cexp (2 * π * I * t * ((m : ℤ) : ℂ) ^ 2 * τ)) * h
  have hnat := hT.nat_add_neg
  have hg := hnat.sub (hasSum_ite_eq 0 (T 0))
  rw [add_sub_cancel_right] at hg
  have hinj : Function.Injective (fun m : ℕ ↦ t * m ^ 2) := by
    intro a b hab
    have : a ^ 2 = b ^ 2 := Nat.eq_of_mul_eq_mul_left ht hab
    exact (Nat.pow_left_injective (by norm_num)) this
  have hzero : ∀ n ∉ Set.range (fun m : ℕ ↦ t * m ^ 2),
      unaryThetaCoeff ψ t n * cexp (2 * π * I * n * τ) = 0 := by
    intro n hn
    by_cases h0 : n = 0
    · exact absurd ⟨0, by simp [h0]⟩ hn
    · rw [unaryThetaCoeff_eq_zero_of_not ψ h0 (fun ⟨m, hm⟩ ↦ hn ⟨m, hm.symm⟩), zero_mul]
  refine (hinj.hasSum_iff hzero).1 ?_
  convert hg using 1
  funext m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [unaryThetaCoeff, hTdef]
  · simp only [Function.comp_apply]
    rw [unaryThetaCoeff_mul_sq ψ ht hm, hneg, if_neg (by omega)]
    simp only [hTdef]
    push_cast
    ring_nf

private lemma charParity_primitive_aux {L : ℕ} [NeZero L] (Φ : DirichletCharacter ℂ L) :
    charParity Φ.primitiveCharacter = charParity Φ := by
  have h := DirichletCharacter.primitiveCharacter_apply_of_isCoprime (χ := Φ) (a := -1)
    isCoprime_one_left.neg_left
  simp only [Int.cast_neg, Int.cast_one] at h
  unfold charParity
  rw [h]

/-- A Dirichlet character restricted to the units, as a monoid hom. -/
private noncomputable def chiHom_aux {L : ℕ} (Φ : DirichletCharacter ℂ L) : (ZMod L)ˣ →* ℂ where
  toFun a := Φ (a : ZMod L)
  map_one' := by simp
  map_mul' a b := by simp [map_mul]

private lemma chiHom_aux_injective {L : ℕ} : Function.Injective (chiHom_aux (L := L)) := by
  intro Φ Φ' h
  refine MulChar.ext fun u ↦ ?_
  have := DFunLike.congr_fun h u
  simpa [chiHom_aux] using this

/-- **Linear independence of the unary theta coefficients.** For a level $L \ge 1$, a parity $\nu$ and a set $s$ of pairs
$(\Phi, t)$ with $\Phi$ a character mod $L$ of parity $\nu$ and $1 \le t \mid L$, the coefficient sequences of
$\theta_{\Phi^\ast,t}$ ($\Phi^\ast$ = `Φ.primitiveCharacter`) are linearly independent. -/
theorem linearIndependent_unaryThetaCoeff {L : ℕ} [NeZero L] (ν : ℕ) (s : Set (DirichletCharacter ℂ L × ℕ))
    (hs : ∀ p ∈ s, 1 ≤ p.2 ∧ p.2 ∣ L ∧ charParity p.1 = ν) :
    LinearIndependent ℂ (fun p : s ↦ unaryThetaCoeff p.1.1.primitiveCharacter p.1.2) := by
  classical
  rw [linearIndependent_iff']
  intro F c hsum i hi
  by_contra hci
  set F' := F.filter (fun j ↦ c j ≠ 0) with hF'
  have hne : F'.Nonempty := ⟨i, by simp [hF', hi, hci]⟩
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image F' (fun j : s ↦ j.1.2) hne
  set t0 := i0.1.2 with ht0
  have ht0pos : 1 ≤ t0 := (hs i0.1 i0.2).1
  set F0 := F'.filter (fun j ↦ j.1.2 = t0) with hF0
  have hsub : F0 ⊆ F := fun j hj ↦ (Finset.mem_filter.1 (Finset.mem_filter.1 hj).1).1
  have key : ∀ m : ℕ, 1 ≤ m → Nat.Coprime m L →
      ∑ j ∈ F0, c j * (2 * j.1.1 (m : ZMod L) * (m : ℂ) ^ ν) = 0 := by
    intro m hm hcop
    have h1 := congrFun hsum (t0 * m ^ 2)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    have hn0 : t0 * m ^ 2 ≠ 0 := by positivity
    have hz : ∀ j ∈ F, j ∉ F0 →
        c j * unaryThetaCoeff j.1.1.primitiveCharacter j.1.2 (t0 * m ^ 2) = 0 := by
      intro j hjF hjn
      by_cases hcj : c j = 0
      · simp [hcj]
      · have hjF' : j ∈ F' := Finset.mem_filter.2 ⟨hjF, hcj⟩
        have hne' : j.1.2 ≠ t0 := fun h ↦ hjn (Finset.mem_filter.2 ⟨hjF', h⟩)
        have hge : t0 ≤ j.1.2 := hmin j hjF'
        have hlt : t0 < j.1.2 := lt_of_le_of_ne hge (Ne.symm hne')
        obtain ⟨ht1, htL, hpar⟩ := hs j.1 j.2
        rw [mul_eq_zero]; right
        by_contra hnz
        obtain ⟨k, hk⟩ : ∃ k, t0 * m ^ 2 = j.1.2 * k ^ 2 := by
          by_contra hno
          exact hnz (unaryThetaCoeff_eq_zero_of_not _ hn0 (fun ⟨k, hk⟩ ↦ hno ⟨k, hk⟩))
        have hd : j.1.2 ∣ t0 * m ^ 2 := ⟨k ^ 2, hk⟩
        have hc : Nat.Coprime j.1.2 (m ^ 2) :=
          (Nat.Coprime.coprime_dvd_left htL hcop.symm).pow_right 2
        have := Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_right hd)
        omega
    rw [← Finset.sum_subset hsub hz] at h1
    refine Eq.trans ?_ h1
    apply Finset.sum_congr rfl
    intro j hj
    have hj2 : j.1.2 = t0 := (Finset.mem_filter.1 hj).2
    obtain ⟨ht1, htL, hpar⟩ := hs j.1 j.2
    rw [← hj2, unaryThetaCoeff_mul_sq _ ht1 hm, charParity_primitive_aux, hpar]
    have := DirichletCharacter.primitiveCharacter_apply_of_isCoprime (χ := j.1.1) (a := (m : ℤ))
      (Nat.isCoprime_iff_coprime.2 hcop)
    simp only [Int.cast_natCast] at this
    rw [this]
  have hunit : ∀ a : (ZMod L)ˣ, ∑ j ∈ F0, c j * j.1.1 (a : ZMod L) = 0 := by
    intro a
    have hLpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    have hcast : (((a : ZMod L).val + L : ℕ) : ZMod L) = a := by
      simp [ZMod.natCast_zmod_val]
    have hcop : Nat.Coprime ((a : ZMod L).val + L) L := by
      rw [← ZMod.isUnit_iff_coprime, hcast]; exact a.isUnit
    have h2 := key ((a : ZMod L).val + L) (by omega) hcop
    rw [hcast] at h2
    have hfac : (2 * (((a : ZMod L).val + L : ℕ) : ℂ) ^ ν) ≠ 0 :=
      mul_ne_zero two_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega)))
    have h3 : (2 * (((a : ZMod L).val + L : ℕ) : ℂ) ^ ν) * ∑ j ∈ F0, c j * j.1.1 (a : ZMod L) = 0 := by
      rw [Finset.mul_sum]
      refine Eq.trans ?_ h2
      apply Finset.sum_congr rfl
      intro j _
      ring
    exact (mul_eq_zero.1 h3).resolve_left hfac
  have hinjπ : Function.Injective (fun j : F0 ↦ chiHom_aux j.1.1.1) := by
    intro j k hjk
    have h1 : j.1.1.1 = k.1.1.1 := chiHom_aux_injective hjk
    have h2 : j.1.1.2 = k.1.1.2 := by
      rw [(Finset.mem_filter.1 j.2).2, (Finset.mem_filter.1 k.2).2]
    exact Subtype.ext (Subtype.ext (Prod.ext h1 h2))
  have hli := (linearIndependent_monoidHom (ZMod L)ˣ ℂ).comp _ hinjπ
  rw [Fintype.linearIndependent_iff] at hli
  have hi0F0 : i0 ∈ F0 := Finset.mem_filter.2 ⟨hi0, rfl⟩
  have hzero := hli (fun j ↦ c j) (by
    funext a
    have := hunit a
    rw [← Finset.sum_coe_sort F0] at this
    simpa [Finset.sum_apply, chiHom_aux] using this) ⟨i0, hi0F0⟩
  exact (Finset.mem_filter.1 hi0).2 hzero

/-- **Linear independence of the unary theta series** as functions on $\mathbb H$ (from the coefficient version and the
uniqueness of $q$-expansions, `Abstract.hasQExp_unique`). -/
theorem linearIndependent_unaryTheta {L : ℕ} [NeZero L] (ν : ℕ) (s : Set (DirichletCharacter ℂ L × ℕ))
    (hs : ∀ p ∈ s, 1 ≤ p.2 ∧ p.2 ∣ L ∧ charParity p.1 = ν) :
    LinearIndependent ℂ (fun p : s ↦ fun τ : ℍ ↦ unaryTheta p.1.1.primitiveCharacter p.1.2 τ) := by
  classical
  rw [linearIndependent_iff']
  intro F c hsum i hi
  have hq0 : Abstract.HasQExp
      (∑ j ∈ F, c j • fun τ : ℍ ↦ unaryTheta j.1.1.primitiveCharacter j.1.2 τ)
      (∑ j ∈ F, c j • unaryThetaCoeff j.1.1.primitiveCharacter j.1.2) := by
    intro τ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    refine hasSum_sum fun j _ ↦ ?_
    have := (hasQExp_unaryTheta j.1.1.primitiveCharacter (hs j.1 j.2).1 τ).mul_left (c j)
    simpa [mul_assoc] using this
  have e : (∑ j ∈ F, c j • fun τ : ℍ ↦ unaryTheta j.1.1.primitiveCharacter j.1.2 τ) = 0 := hsum
  rw [e] at hq0
  have hz : Abstract.HasQExp (0 : ℍ → ℂ) 0 := fun τ ↦ by simpa using hasSum_zero
  have h0 := Abstract.hasQExp_unique hq0 hz
  exact linearIndependent_iff'.1 (linearIndependent_unaryThetaCoeff ν s hs) F c h0 i hi

end ModularFormsKB.HalfIntegral
