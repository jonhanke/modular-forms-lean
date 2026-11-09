import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination

/-!
# Milne, Chapter 8: an algebraic descent lemma on the affine line (for Theorem 8.4)

Used in the proof of the universal property in Milne's Theorem 8.4 (`milne2017mf`, Section 8, pdf p. 98). Let
$\pi : k[X] \to B$ be an injective map into a domain and $t : B \to k$ a point over $v = t(\pi X)$. Suppose a ring map
$\varphi : C \to k[X]_s$ ($s \ne 0$) and a ring map $\psi : C \to B_g$ ($t(g) \ne 0$) agree in $B_{g\pi(s)}$. Write
$s = (X - v)^e s'$ with $s'(v) \ne 0$. Then $\varphi$ takes values in $k[X]_{s'}$, and at $v$ it has the value of
$\psi$ at $t$ (`LineDescent.exists_descent`): an element $p/s^n$ whose image in $B$ is regular at $t$ cannot have a pole
at $v$, because $t$ lies over $v$.
-/

open Polynomial

noncomputable section

namespace ModularFormsKB.Milne.LineDescent

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [IsDomain B] [Algebra k B]

/-- The map $k[X]_s \to B_{g \pi(s)}$ induced by $\pi$. -/
def toAway (π : k[X] →ₐ[k] B) (g : B) (s : k[X]) : Localization.Away s →+* Localization.Away (g * π s) :=
  IsLocalization.Away.lift s (g := (algebraMap B (Localization.Away (g * π s))).comp π.toRingHom)
    (isUnit_of_mul_isUnit_right (by
      simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (g * π s)) (g * π s)))

/-- The map $B_g \to B_{g \pi(s)}$. -/
def fromAway (π : k[X] →ₐ[k] B) (g : B) (s : k[X]) : Localization.Away g →+* Localization.Away (g * π s) :=
  IsLocalization.Away.awayToAwayRight g (π s)

/-- Evaluation $k[X]_s \to k$ at a point $v$ with $s(v) \ne 0$. -/
def evalAway (s : k[X]) (v : k) (hv : s.eval v ≠ 0) : Localization.Away s →+* k :=
  IsLocalization.Away.lift s (g := evalRingHom v) (isUnit_iff_ne_zero.mpr hv)

/-- Evaluation $B_g \to k$ at a point $t : B \to k$ with $t(g) \ne 0$. -/
def evalAwayB (t : B →ₐ[k] k) (g : B) (hg : t g ≠ 0) : Localization.Away g →+* k :=
  IsLocalization.Away.lift g (g := t.toRingHom) (isUnit_iff_ne_zero.mpr hg)

/-- The map $k[X]_{s'} \to k[X]_s$ when $s' \mid s$. -/
def awayOfDvd {s' s : k[X]} (h : s' ∣ s) : Localization.Away s' →+* Localization.Away s :=
  IsLocalization.Away.lift s' (g := algebraMap k[X] (Localization.Away s))
    (isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit s))

omit [IsDomain B] in
theorem eval_of_algHom (π : k[X] →ₐ[k] B) (t : B →ₐ[k] k) {v : k} (htv : t (π X) = v) (q : k[X]) :
    t (π q) = q.eval v := by
  have : t.comp π = Polynomial.aeval v := Polynomial.algHom_ext (by simp [htv])
  rw [← Polynomial.coe_aeval_eq_eval, ← this]
  rfl

theorem awayOfDvd_injective {s' s : k[X]} (hs : s ≠ 0) (h : s' ∣ s) : Function.Injective (awayOfDvd h) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨p, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s') x
  have h1 : awayOfDvd h (IsLocalization.mk' _ p (⟨s' ^ n, n, rfl⟩ : Submonoid.powers s')) = 0 := hx
  rw [awayOfDvd, IsLocalization.Away.lift, IsLocalization.lift_mk'_spec, mul_zero,
    IsLocalization.map_eq_zero_iff (Submonoid.powers s)] at h1
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := h1
  have : p = 0 := (mul_eq_zero.mp hm).resolve_left (pow_ne_zero _ hs)
  simp [this]

/-- Element-wise descent. -/
theorem descent_elem (π : k[X] →ₐ[k] B) (hπ : Function.Injective π)
    (t : B →ₐ[k] k) (v : k) (htv : t (π X) = v) (s s' : k[X]) (e : ℕ) (hs : s ≠ 0)
    (hs' : s = (X - Polynomial.C v) ^ e * s') (hv : s'.eval v ≠ 0) (g : B) (hg : t g ≠ 0)
    (x : Localization.Away s) (y : Localization.Away g)
    (hxy : toAway π g s x = fromAway π g s y) :
    ∃ x' : Localization.Away s', awayOfDvd (Dvd.intro_left _ hs'.symm) x' = x ∧
      evalAway s' v hv x' = evalAwayB t g hg y := by
  have hev := eval_of_algHom π t htv
  have hg0 : g ≠ 0 := fun h ↦ hg (by simp [h])
  have hπs : π s ≠ 0 := fun h ↦ hs (hπ (by simpa using h))
  obtain ⟨⟨p, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) x
  obtain ⟨⟨b, ⟨_, m, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) y
  -- the cross-multiplied identity in `B`
  have key : π p * g ^ m = π s ^ n * b := by
    set z := toAway π g s (IsLocalization.mk' _ p (⟨s ^ n, n, rfl⟩ : Submonoid.powers s))
    have h1 : algebraMap B (Localization.Away (g * π s)) (π p) =
        algebraMap B (Localization.Away (g * π s)) (π (s ^ n)) * z := by
      have := (IsLocalization.lift_mk'_spec (S := Localization.Away s) (M := Submonoid.powers s) _ p z
        (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)).mp rfl
      simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using this
    have h2 : algebraMap B (Localization.Away (g * π s)) b =
        algebraMap B (Localization.Away (g * π s)) (g ^ m) * z := by
      rw [show z = fromAway π g s (IsLocalization.mk' _ b (⟨g ^ m, m, rfl⟩ : Submonoid.powers g)) from hxy]
      exact (IsLocalization.lift_mk'_spec (S := Localization.Away g) (M := Submonoid.powers g) _ b
        _ (⟨g ^ m, m, rfl⟩ : Submonoid.powers g)).mp rfl
    apply IsLocalization.injective (Localization.Away (g * π s))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (mul_ne_zero hg0 hπs))
    rw [map_mul, map_mul, h1, h2, map_pow π s n]
    ring
  have hsn : π s ^ n = π ((X - Polynomial.C v) ^ (e * n)) * π (s' ^ n) := by
    rw [← map_pow, hs', mul_pow, ← pow_mul, map_mul]
  have hπne : ∀ q : k[X], q ≠ 0 → π q ≠ 0 := fun q hq h ↦ hq (hπ (by simpa using h))
  have hXv : (X - Polynomial.C v : k[X]) ≠ 0 := X_sub_C_ne_zero v
  -- the numerator vanishes to order at least `e n` at `v`
  have hdvd : (X - Polynomial.C v) ^ (e * n) ∣ p := by
    by_contra hnd
    have hp : p ≠ 0 := by rintro rfl; exact hnd (dvd_zero _)
    obtain ⟨q, hq, hqn⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp v
    set a := rootMultiplicity v p
    have ha : a < e * n := by
      by_contra h
      exact hnd (hq ▸ dvd_mul_of_dvd_left (pow_dvd_pow _ (not_lt.mp h)) _)
    have hqv : q.eval v ≠ 0 := fun h0 ↦ hqn (dvd_iff_isRoot.mpr h0)
    have hsplit : (X - Polynomial.C v) ^ (e * n) = (X - Polynomial.C v) ^ a * (X - Polynomial.C v) ^ (e * n - a) := by
      rw [← pow_add, Nat.add_sub_cancel' ha.le]
    rw [hsn, hsplit, hq, map_mul, map_mul] at key
    have key' : π q * g ^ m = π ((X - Polynomial.C v) ^ (e * n - a)) * π (s' ^ n) * b := by
      apply mul_left_cancel₀ (hπne _ (pow_ne_zero a hXv))
      rw [← mul_assoc, key]
      ring
    have := congrArg t key'
    simp only [map_mul, map_pow, hev, eval_sub, eval_X, eval_C, sub_self] at this
    rw [zero_pow (Nat.sub_ne_zero_of_lt ha), zero_mul, zero_mul] at this
    exact mul_ne_zero hqv (pow_ne_zero _ hg) this
  obtain ⟨p'', hp''⟩ := hdvd
  have key2 : π p'' * g ^ m = π s' ^ n * b := by
    rw [hsn, hp'', map_mul] at key
    apply mul_left_cancel₀ (hπne _ (pow_ne_zero (e * n) hXv))
    rw [← map_pow π s' n, ← mul_assoc, key]
    ring
  refine ⟨IsLocalization.mk' _ p'' (⟨s' ^ n, n, rfl⟩ : Submonoid.powers s'), ?_, ?_⟩
  · rw [awayOfDvd, IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
    have hdv : (X - Polynomial.C v) ^ (e * n) ∣ s ^ n :=
      Dvd.intro _ (by rw [hs', mul_pow, ← pow_mul] : (X - Polynomial.C v) ^ (e * n) * s' ^ n = s ^ n)
    have hsu : IsUnit (algebraMap k[X] (Localization.Away s) (s ^ n)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit s).pow n
    have hu : IsUnit (algebraMap k[X] (Localization.Away s) ((X - Polynomial.C v) ^ (e * n))) :=
      isUnit_of_dvd_unit (map_dvd _ hdv) hsu
    apply hu.mul_left_cancel
    have hspec := IsLocalization.mk'_spec (Localization.Away s) p (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)
    rw [← map_mul, ← hp'', ← hspec]
    have : s ^ n = (X - Polynomial.C v) ^ (e * n) * s' ^ n := by rw [hs', mul_pow, ← pow_mul]
    simp only [this, map_mul]
    ring
  · have E1 := (IsLocalization.lift_mk'_spec (S := Localization.Away s') (M := Submonoid.powers s')
      (g := evalRingHom v) _ p'' (evalAway s' v hv (IsLocalization.mk' _ p'' (⟨s' ^ n, n, rfl⟩ :
        Submonoid.powers s'))) (⟨s' ^ n, n, rfl⟩ : Submonoid.powers s')).mp rfl
    have E2 := (IsLocalization.lift_mk'_spec (S := Localization.Away g) (M := Submonoid.powers g)
      (g := t.toRingHom) _ b (evalAwayB t g hg (IsLocalization.mk' _ b (⟨g ^ m, m, rfl⟩ :
        Submonoid.powers g))) (⟨g ^ m, m, rfl⟩ : Submonoid.powers g)).mp rfl
    have K := congrArg t key2
    simp only [map_mul, map_pow, hev] at K
    simp only [coe_evalRingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow] at E1 E2
    have hne : s'.eval v ^ n * t g ^ m ≠ 0 := mul_ne_zero (pow_ne_zero _ hv) (pow_ne_zero _ hg)
    apply mul_left_cancel₀ hne
    linear_combination (-(t g ^ m)) * E1 + K + (s'.eval v ^ n) * E2

/-- **Descent on the affine line.** -/
theorem exists_descent {C : Type*} [CommRing C] (π : k[X] →ₐ[k] B) (hπ : Function.Injective π)
    (t : B →ₐ[k] k) (v : k) (htv : t (π X) = v) (s : k[X]) (hs : s ≠ 0) (g : B) (hg : t g ≠ 0)
    (φ : C →+* Localization.Away s) (ψ : C →+* Localization.Away g)
    (hcomp : (toAway π g s).comp φ = (fromAway π g s).comp ψ) :
    ∃ (s' : k[X]) (e : ℕ) (hs' : s = (X - Polynomial.C v) ^ e * s') (hv : s'.eval v ≠ 0)
      (φ₀ : C →+* Localization.Away s'),
      (awayOfDvd (Dvd.intro_left _ hs'.symm)).comp φ₀ = φ ∧
      (evalAway s' v hv).comp φ₀ = (evalAwayB t g hg).comp ψ := by
  have hs' : s = (X - Polynomial.C v) ^ rootMultiplicity v s * (s /ₘ (X - Polynomial.C v) ^ rootMultiplicity v s) :=
    (pow_mul_divByMonic_rootMultiplicity_eq s v).symm
  have hv := eval_divByMonic_pow_rootMultiplicity_ne_zero v hs
  refine ⟨_, _, hs', hv, ?_⟩
  set ι := awayOfDvd (Dvd.intro_left _ hs'.symm)
  have hinj : Function.Injective ι := awayOfDvd_injective hs _
  have hmem : ∀ c, φ c ∈ ι.range := fun c ↦ by
    obtain ⟨x', hx', -⟩ := descent_elem π hπ t v htv s _ _ hs hs' hv g hg (φ c) (ψ c)
      (RingHom.congr_fun hcomp c)
    exact ⟨x', hx'⟩
  let eι := RingEquiv.ofBijective ι.rangeRestrict ⟨fun a b h ↦ hinj (congrArg Subtype.val h),
    ι.rangeRestrict_surjective⟩
  let φ₀ : C →+* Localization.Away _ := eι.symm.toRingHom.comp (φ.codRestrict ι.range hmem)
  have hφ₀ : ∀ c, ι (φ₀ c) = φ c := fun c ↦ by
    have := congrArg Subtype.val (eι.apply_symm_apply (φ.codRestrict ι.range hmem c))
    exact this
  refine ⟨φ₀, RingHom.ext hφ₀, RingHom.ext fun c ↦ ?_⟩
  obtain ⟨x', hx', hev⟩ := descent_elem π hπ t v htv s _ _ hs hs' hv g hg (φ c) (ψ c)
    (RingHom.congr_fun hcomp c)
  have : φ₀ c = x' := hinj (by rw [hφ₀, hx'])
  simp only [RingHom.comp_apply, this, hev]


end ModularFormsKB.Milne.LineDescent
