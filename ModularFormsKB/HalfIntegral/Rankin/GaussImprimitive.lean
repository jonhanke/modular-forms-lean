/-
# The Gauss sum of an imprimitive character

Part of loose end LE-MF-0256.

For a Dirichlet character $\omega$ modulo $L$ induced by the primitive character $\omega^*$ modulo $f$ (the conductor),
$g_0 = L/f$, and every integer $m$,
$$G(\omega, m) = \tau(\omega^*)\sum_{e \mid (m, g_0)} e\,\mu(g_0/e)\,\omega^*(g_0/e)\,\overline{\omega^*}(m/e),$$
with $G(\omega,m) = \sum_{a=0}^{L-1}\omega(a)e(am/L)$ (`gaussAt`) and $\tau(\omega^*) = G(\omega^*, 1)$. For $f = 1$ this is
Ramanujan's sum $c_L(m) = \sum_{e \mid (m, L)} e\,\mu(L/e)$. Checked numerically
(408 798 cases). Source: Miyake 1989 `miyake1989`, Lemma 3.1.3
[unverified]; Iwaniec–Kowalski, Lemma 3.2 [unverified].

* `gaussAt_of_isPrimitive`: for primitive $\psi$ modulo $f$, $G(\psi, m) = \overline\psi(m)\,\tau(\psi)$ (Mathlib's
  `gaussSum_mulShift_of_isPrimitive`);
* `gaussAt_eq_sum_primitive`: the formula above (Möbius inversion of the coprimality condition, then the sum over the
  residues modulo $L/d$ reduced to the residues modulo $f$).

The proof route: $\omega(a) = \omega^*(a)\sum_{d \mid (a, g_0)}\mu(d)$; substitute $a = db$; for $h = g_0/d$,
$\sum_{b \bmod fh}\omega^*(b)e(bm/(fh)) = h\,[h \mid m]\,G(\omega^*, m/h)$.
-/
import ModularFormsKB.HalfIntegral.Abstract.ShimuraRankin
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

namespace ModularFormsKB.HalfIntegral

open Complex Real

namespace GaussImprimitive

/-- helper: `gaussAt` as a sum over `ZMod L`. -/
private lemma gaussAt_eq_sum_zmod' {L : ℕ} [NeZero L] (ω : DirichletCharacter ℂ L) (m : ℤ) :
    gaussAt L ω m = ∑ x : ZMod L, ω x * cexp (2 * π * I * ((x.val * m : ℤ) : ℂ) / L) := by
  unfold gaussAt
  refine Finset.sum_nbij' (fun a ↦ (a : ZMod L)) (fun x ↦ x.val) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro x _; exact Finset.mem_range.2 (ZMod.val_lt x)
  · intro a ha
    exact ZMod.val_cast_of_lt (Finset.mem_range.1 ha)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro a ha
    rw [ZMod.val_cast_of_lt (Finset.mem_range.1 ha)]
    push_cast
    ring_nf

private lemma gaussAt_eq_gaussSum {L : ℕ} [NeZero L] (ω : DirichletCharacter ℂ L) (m : ℤ) :
    gaussAt L ω m = gaussSum ω ((ZMod.stdAddChar : AddChar (ZMod L) ℂ).mulShift (m : ZMod L)) := by
  rw [gaussAt_eq_sum_zmod']
  unfold gaussSum
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [AddChar.mulShift_apply, ← ZMod.stdAddChar_coe]
  congr 2
  push_cast
  rw [ZMod.natCast_zmod_val]; ring

private lemma sum_mu (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) = if n = 1 then 1 else 0 := by
  have h := DFunLike.congr_fun ArithmeticFunction.moebius_mul_coe_zeta n
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

private lemma sum_mu_ite {g a : ℕ} (hg : g ≠ 0) :
    ∑ d ∈ g.divisors, (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) =
      if Nat.Coprime g a then 1 else 0 := by
  rw [← Finset.sum_filter]
  have hgcd : Nat.gcd g a ≠ 0 := Nat.gcd_ne_zero_left hg
  have : g.divisors.filter (· ∣ a) = (Nat.gcd g a).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    tauto
  rw [this]
  have h := sum_mu (Nat.gcd g a)
  have h' : ∑ d ∈ (Nat.gcd g a).divisors, (ArithmeticFunction.moebius d : ℂ) =
      if Nat.gcd g a = 1 then 1 else 0 := by
    have := congrArg (fun z : ℤ => (z : ℂ)) h
    simpa [apply_ite] using this
  rw [h']

private lemma omega_eq {L : ℕ} [NeZero L] (ω : DirichletCharacter ℂ L) (a : ℕ) :
    ω (a : ZMod L) = ω.primitiveCharacter (a : ZMod ω.conductor) *
      ∑ d ∈ (L / ω.conductor).divisors, (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) := by
  have hf : ω.conductor ∣ L := DirichletCharacter.conductor_dvd_level ω
  have hf0 : ω.conductor ≠ 0 := DirichletCharacter.conductor_ne_zero ω
  have hg0 : L / ω.conductor ≠ 0 := by
    intro h
    have := Nat.div_eq_zero_iff.mp h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne L)) hf
    omega
  have hLfg : L = ω.conductor * (L / ω.conductor) := (Nat.mul_div_cancel' hf).symm
  rw [sum_mu_ite hg0]
  by_cases hc : Nat.Coprime a L
  · have hg : Nat.Coprime (L / ω.conductor) a :=
      Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hf) hc.symm
    rw [if_pos hg, mul_one]
    have := DirichletCharacter.primitiveCharacter_apply_of_isCoprime ω
      (a := (a : ℤ)) (by simpa using Nat.isCoprime_iff_coprime.mpr hc)
    simpa using this.symm
  · have h0 : ω (a : ZMod L) = 0 := by
      apply MulChar.map_nonunit
      rwa [ZMod.isUnit_iff_coprime]
    rw [h0]
    by_cases hg : Nat.Coprime (L / ω.conductor) a
    · have hfa : ¬ Nat.Coprime a ω.conductor := by
        intro h
        apply hc
        rw [hLfg]
        exact Nat.Coprime.mul_right h hg.symm
      rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime]), zero_mul]
    · rw [if_neg hg, mul_zero]

private lemma geom_ite (h : ℕ) (hh : 0 < h) (m : ℤ) :
    ∑ j ∈ Finset.range h, cexp (2 * π * I * (j : ℂ) * (m : ℂ) / h) =
      if (h : ℤ) ∣ m then (h : ℂ) else 0 := by
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  set z : ℂ := cexp (2 * π * I * (m : ℂ) / h) with hz
  have hterm : ∀ j : ℕ, cexp (2 * π * I * (j : ℂ) * (m : ℂ) / h) = z ^ j := by
    intro j
    rw [hz, ← Complex.exp_nat_mul]
    congr 1
    ring
  simp_rw [hterm]
  split_ifs with hd
  · obtain ⟨k, rfl⟩ := hd
    have : z = 1 := by
      rw [hz, Complex.exp_eq_one_iff]
      exact ⟨k, by push_cast; field_simp⟩
    simp [this]
  · have hz1 : z ≠ 1 := by
      intro h1
      rw [hz, Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      apply hd
      refine ⟨n, ?_⟩
      have : (m : ℂ) = (h : ℂ) * n := by
        field_simp at hn
        linear_combination hn
      exact_mod_cast this
    have hzh : z ^ h = 1 := by
      rw [hz, ← Complex.exp_nat_mul]
      have : (h : ℂ) * (2 * π * I * (m : ℂ) / h) = (m : ℤ) * (2 * π * I) := by
        field_simp
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [geom_sum_eq hz1, hzh]
    simp

private lemma sum_range_mul_split (f : ℕ) (F : ℕ → ℂ) (h : ℕ) :
    ∑ b ∈ Finset.range (f * h), F b = ∑ j ∈ Finset.range h, ∑ i ∈ Finset.range f, F (f * j + i) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

private lemma sum_residues {f : ℕ} (hf : 0 < f) (ψ : DirichletCharacter ℂ f) (h : ℕ) (hh : 0 < h) (m : ℤ) :
    ∑ b ∈ Finset.range (f * h), ψ (b : ZMod f) * cexp (2 * π * I * (b : ℂ) * (m : ℂ) / ((f : ℂ) * h)) =
      if (h : ℤ) ∣ m then (h : ℂ) * gaussAt f ψ (m / (h : ℤ)) else 0 := by
  have hf' : (f : ℂ) ≠ 0 := by exact_mod_cast hf.ne'
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [sum_range_mul_split]
  have hterm : ∀ j i : ℕ, ψ (((f * j + i : ℕ)) : ZMod f) *
      cexp (2 * π * I * ((f * j + i : ℕ) : ℂ) * (m : ℂ) / ((f : ℂ) * h)) =
      (ψ (i : ZMod f) * cexp (2 * π * I * (i : ℂ) * (m : ℂ) / ((f : ℂ) * h))) *
        cexp (2 * π * I * (j : ℂ) * (m : ℂ) / h) := by
    intro j i
    have h1 : ψ (((f * j + i : ℕ)) : ZMod f) = ψ (i : ZMod f) := by
      push_cast
      simp
    rw [h1, mul_assoc (ψ (i : ZMod f)), ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have : ∀ i : ℕ, ∑ j ∈ Finset.range h, (ψ (i : ZMod f) * cexp (2 * π * I * (i : ℂ) * (m : ℂ) / ((f : ℂ) * h))) *
        cexp (2 * π * I * (j : ℂ) * (m : ℂ) / h) =
      (ψ (i : ZMod f) * cexp (2 * π * I * (i : ℂ) * (m : ℂ) / ((f : ℂ) * h))) *
        ∑ j ∈ Finset.range h, cexp (2 * π * I * (j : ℂ) * (m : ℂ) / h) := fun i ↦ by rw [Finset.mul_sum]
  simp_rw [this]
  rw [← Finset.sum_mul, geom_ite h hh m]
  split_ifs with hd
  · obtain ⟨k, rfl⟩ := hd
    rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hh.ne')]
    unfold gaussAt
    rw [mul_comm]
    refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
    refine congrArg _ (congrArg _ ?_)
    push_cast
    field_simp
  · simp

private lemma sum_dvd_block {L f d h : ℕ} (hf : 0 < f) (hd : 0 < d) (hh : 0 < h) (hL : L = d * (f * h))
    (ψ : DirichletCharacter ℂ f) (m : ℤ) :
    ∑ a ∈ Finset.range L, (if d ∣ a then ψ (a : ZMod f) * cexp (2 * π * I * (a : ℂ) * (m : ℂ) / L) else 0) =
      ψ (d : ZMod f) * (if (h : ℤ) ∣ m then (h : ℂ) * gaussAt f ψ (m / (h : ℤ)) else 0) := by
  subst hL
  rw [← Finset.sum_filter]
  have himg : (Finset.range (d * (f * h))).filter (fun a ↦ d ∣ a) =
      (Finset.range (f * h)).image (fun b ↦ d * b) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨ha, b, rfl⟩
      exact ⟨b, Nat.lt_of_mul_lt_mul_left ha, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_left hb hd, b, rfl⟩
  rw [himg, Finset.sum_image (fun x _ y _ hxy ↦ Nat.eq_of_mul_eq_mul_left hd hxy), ← sum_residues hf ψ h hh m,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hfC : (f : ℂ) ≠ 0 := by exact_mod_cast hf.ne'
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  push_cast
  rw [map_mul, mul_assoc]
  congr 3
  field_simp

/-- **The Gauss sum of a primitive character:** $G(\psi, m) = \overline\psi(m)\,\tau(\psi)$ for every integer $m$. -/
theorem gaussAt_of_isPrimitive {f : ℕ} [NeZero f] {ψ : DirichletCharacter ℂ f} (hψ : ψ.IsPrimitive) (m : ℤ) :
    gaussAt f ψ m = ψ⁻¹ (m : ZMod f) * gaussAt f ψ 1 := by
  rw [gaussAt_eq_gaussSum, gaussAt_eq_gaussSum]
  have h1 : ((1 : ℤ) : ZMod f) = 1 := by simp
  rw [h1, AddChar.mulShift_one]
  exact gaussSum_mulShift_of_isPrimitive _ hψ _

/-- **The Gauss sum of an imprimitive character** (Miyake 1989 `miyake1989`, Lemma 3.1.3 [unverified]): with
$f$ the conductor of $\omega$, $\omega^*$ its primitive character and $g_0 = L/f$,
$G(\omega, m) = \tau(\omega^*)\sum_{e \mid g_0,\ e \mid m} e\,\mu(g_0/e)\,\omega^*(g_0/e)\,\overline{\omega^*}(m/e)$. -/
@[kb "miyake1989" "Lemma 3.1.3: the Gauss sum of an imprimitive character through the primitive one [unverified]"]
theorem gaussAt_eq_sum_primitive {L : ℕ} [NeZero L] (ω : DirichletCharacter ℂ L) (m : ℤ) :
    gaussAt L ω m = gaussAt ω.conductor ω.primitiveCharacter 1 *
      ∑ e ∈ (L / ω.conductor).divisors.filter (fun e : ℕ ↦ (e : ℤ) ∣ m),
        (e : ℂ) * (ArithmeticFunction.moebius (L / ω.conductor / e) : ℂ) *
          ω.primitiveCharacter ((L / ω.conductor / e : ℕ) : ZMod ω.conductor) *
          ω.primitiveCharacter⁻¹ ((m / e : ℤ) : ZMod ω.conductor) := by
  have : NeZero ω.conductor := ⟨DirichletCharacter.conductor_ne_zero ω⟩
  have hf : ω.conductor ∣ L := DirichletCharacter.conductor_dvd_level ω
  have hf0 : 0 < ω.conductor := Nat.pos_of_ne_zero (NeZero.ne _)
  have hg0 : L / ω.conductor ≠ 0 := by
    intro h
    have := Nat.div_eq_zero_iff.mp h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne L)) hf
    omega
  have hLfg : L = ω.conductor * (L / ω.conductor) := (Nat.mul_div_cancel' hf).symm
  have hprim := DirichletCharacter.primitiveCharacter_isPrimitive ω
  -- step (b)
  have step1 : gaussAt L ω m = ∑ d ∈ (L / ω.conductor).divisors,
      ArithmeticFunction.moebius d * (ω.primitiveCharacter (d : ZMod ω.conductor) *
        (if ((L / ω.conductor / d : ℕ) : ℤ) ∣ m then
          ((L / ω.conductor / d : ℕ) : ℂ) *
            gaussAt ω.conductor ω.primitiveCharacter (m / ((L / ω.conductor / d : ℕ) : ℤ)) else 0)) := by
    unfold gaussAt
    have hterm : ∀ a ∈ Finset.range L, ω (a : ZMod L) * cexp (2 * π * I * (a : ℂ) * (m : ℂ) / L) =
        ∑ d ∈ (L / ω.conductor).divisors, (if d ∣ a then
          (ArithmeticFunction.moebius d : ℂ) * (ω.primitiveCharacter (a : ZMod ω.conductor) *
            cexp (2 * π * I * (a : ℂ) * (m : ℂ) / L)) else 0) := by
      intro a _
      rw [omega_eq, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ ↦ ?_
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    obtain ⟨hdv, -⟩ := Nat.mem_divisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdv (Nat.pos_of_ne_zero hg0)
    have hdiv : L / ω.conductor = d * (L / ω.conductor / d) := (Nat.mul_div_cancel' hdv).symm
    have hh0 : 0 < L / ω.conductor / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hg0) hdv) hd0
    have hLd : L = d * (ω.conductor * (L / ω.conductor / d)) := by
      have h1 : L = ω.conductor * (d * (L / ω.conductor / d)) := by rw [← hdiv]; exact hLfg
      calc L = ω.conductor * (d * (L / ω.conductor / d)) := h1
        _ = _ := by ring
    have key := sum_dvd_block hf0 hd0 hh0 hLd ω.primitiveCharacter m
    calc _ = (ArithmeticFunction.moebius d : ℂ) * ∑ x ∈ Finset.range L,
          (if d ∣ x then ω.primitiveCharacter (x : ZMod ω.conductor) *
            cexp (2 * π * I * (x : ℂ) * (m : ℂ) / L) else 0) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ ↦ by split_ifs <;> simp
      _ = _ := by rw [key]; rfl
  rw [step1, Finset.sum_filter, Finset.mul_sum]
  refine (Finset.sum_congr rfl ?_).trans (Nat.sum_div_divisors (L / ω.conductor)
    (fun e : ℕ ↦ gaussAt ω.conductor ω.primitiveCharacter 1 *
      (if (e : ℤ) ∣ m then (e : ℂ) * (ArithmeticFunction.moebius (L / ω.conductor / e) : ℂ) *
        ω.primitiveCharacter ((L / ω.conductor / e : ℕ) : ZMod ω.conductor) *
        ω.primitiveCharacter⁻¹ ((m / e : ℤ) : ZMod ω.conductor) else 0)))
  intro d hd
  have hdv : d ∣ L / ω.conductor := (Nat.mem_divisors.mp hd).1
  simp only [Nat.div_div_self hdv hg0]
  split_ifs with hdm
  · rw [gaussAt_of_isPrimitive hprim]
    ring
  · simp

end GaussImprimitive

end ModularFormsKB.HalfIntegral
