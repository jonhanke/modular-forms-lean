/-
# Hecke operators $T(p^2)$ and Kohnen's plus space, on coefficients

Everything here is stated on **coefficient sequences** $a : \mathbb N \to \mathbb C$ (the $q$-expansion
$f = \sum a(n) q^n$). The analytic fact that these operations preserve modular forms is the named input
`HeckeStable` in `ModularFormsKB/HalfIntegral/Abstract/Shimura.lean`; the identities proved here are formal. The Shimura lift on
coefficients is in `ModularFormsKB/HalfIntegral/ShimuraLift.lean`.

**Shimura's $T(p^2)$** (Shimura 1973 `shimura1973`, Thm. 1.7 [unverified]) on $M_{k+1/2}(4N,\chi)$, $p$ prime:
$$ (T(p^2)a)(n) = a(p^2 n) + \chi(p)\Big(\frac{(-1)^k n}{p}\Big)p^{k-1}a(n) + \chi(p)^2 p^{2k-1}a(n/p^2), $$
with $a(n/p^2) = 0$ unless $p^2 \mid n$. For $p \mid 4N$, $\chi(p) = 0$ and this is $U(p^2)$.

**Integral weight $T(p)$** on $M_{2k}(M, \psi)$: $(T(p)c)(n) = c(pn) + \psi(p)p^{2k-1}c(n/p)$.

**Kohnen's plus space** (Kohnen 1980 `kohnen1980`, level 4; Kohnen 1982, level $4N$, $N$ odd squarefree [unverified]):
forms with $a(n) = 0$ unless $(-1)^k n \equiv 0, 1 \bmod 4$.

**Proved here (formal).** `heckeTLin` ($T(p^2)$ is $\mathbb C$-linear), `heckeT_comm` ($T(p^2)T(q^2) = T(q^2)T(p^2)$ for
distinct primes), `plusSeq` (the plus condition cuts out a submodule) and `heckeT_plus` (for odd $p$, $T(p^2)$ preserves it).

**Conventions.** $\left(\frac{a}{p}\right)$ is Mathlib's `jacobiSym a p`; at $p = 2$ it is multiplied by $\chi(2) = 0$, so its
value there is irrelevant. Real powers $p^{k-1}$ use `zpow` so that $k = 0$ (weight ½) is allowed.
-/
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.DirichletCharacter.Basic
import ModularFormsKB.Citation
namespace ModularFormsKB.HalfIntegral

open Complex

/-- **Shimura's Hecke operator $T(p^2)$** in weight $k + \tfrac12$ with character $\chi$ mod $4N$, on coefficients. -/
noncomputable def heckeT (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (p ^ 2 * n) + χ p * (jacobiSym ((-1) ^ k * n) p : ℂ) * (p : ℂ) ^ ((k : ℤ) - 1) * a n +
    if p ^ 2 ∣ n then χ p ^ 2 * (p : ℂ) ^ (2 * (k : ℤ) - 1) * a (n / p ^ 2) else 0

/-- **The integral-weight Hecke operator $T(p)$** in weight $w$ with character $\psi$ mod $M$, on coefficients. -/
noncomputable def heckeTInt (w M : ℕ) (ψ : DirichletCharacter ℂ M) (p : ℕ) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  c (p * n) + if p ∣ n then ψ p * (p : ℂ) ^ ((w : ℤ) - 1) * c (n / p) else 0

/-- **$T(p^2)$ is $\mathbb C$-linear** on coefficient sequences. -/
noncomputable def heckeTLin (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (p : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun := heckeT k N χ p
  map_add' a b := by
    funext n
    simp only [heckeT, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c a := by
    funext n
    simp only [heckeT, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

@[simp] theorem heckeTLin_apply (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (p : ℕ) (a : ℕ → ℂ) :
    heckeTLin k N χ p a = heckeT k N χ p a := rfl

/-- **$T(p^2)$ and $T(q^2)$ commute** on coefficient sequences, for distinct primes $p \ne q$ (Shimura 1973 `shimura1973`,
§1 [unverified]). Purely formal: it uses only $\left(\frac{p^2 m}{q}\right) = \left(\frac{m}{q}\right)$ for $q \nmid p$. -/
private theorem jac_sq_mul {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (x : ℤ) (m : ℕ) :
    jacobiSym (x * ((p ^ 2 * m : ℕ) : ℤ)) q = jacobiSym (x * (m : ℤ)) q := by
  have h : (p : ℤ).gcd q = 1 := by
    simpa using (Nat.coprime_primes hp hq).2 hpq
  have : x * ((p ^ 2 * m : ℕ) : ℤ) = (p : ℤ) ^ 2 * (x * m) := by push_cast; ring
  rw [this, jacobiSym.mul_left, jacobiSym.sq_one' h, one_mul]

private theorem sq_dvd_mul_iff {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (n : ℕ) :
    q ^ 2 ∣ p ^ 2 * n ↔ q ^ 2 ∣ n := by
  have hc : Nat.Coprime (q ^ 2) (p ^ 2) := ((Nat.coprime_primes hq hp).2 hpq.symm).pow 2 2
  exact ⟨fun h => hc.dvd_of_dvd_mul_left h, fun h => Dvd.dvd.mul_left h _⟩

private theorem heckeT_def (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    heckeT k N χ p a n = a (p ^ 2 * n) + χ p * (jacobiSym ((-1) ^ k * n) p : ℂ) * (p : ℂ) ^ ((k : ℤ) - 1) * a n +
    if p ^ 2 ∣ n then χ p ^ 2 * (p : ℂ) ^ (2 * (k : ℤ) - 1) * a (n / p ^ 2) else 0 := rfl

private theorem heckeT_sq_mul (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (a : ℕ → ℂ) (n : ℕ) :
    heckeT k N χ q a (p ^ 2 * n) = a (p ^ 2 * (q ^ 2 * n)) +
      χ q * (jacobiSym ((-1) ^ k * n) q : ℂ) * (q : ℂ) ^ ((k : ℤ) - 1) * a (p ^ 2 * n) +
      if q ^ 2 ∣ n then χ q ^ 2 * (q : ℂ) ^ (2 * (k : ℤ) - 1) * a (p ^ 2 * (n / q ^ 2)) else 0 := by
  rw [heckeT_def, jac_sq_mul hp hq hpq, show q ^ 2 * (p ^ 2 * n) = p ^ 2 * (q ^ 2 * n) by ring]
  simp only [sq_dvd_mul_iff hp hq hpq]
  by_cases h : q ^ 2 ∣ n
  · obtain ⟨m, rfl⟩ := h
    have hq0 : 0 < q ^ 2 := pow_pos hq.pos 2
    rw [show p ^ 2 * (q ^ 2 * m) = q ^ 2 * (p ^ 2 * m) by ring, Nat.mul_div_cancel_left _ hq0,
      Nat.mul_div_cancel_left _ hq0]
  · simp [h]

theorem heckeT_comm (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (a : ℕ → ℂ) :
    heckeT k N χ p (heckeT k N χ q a) = heckeT k N χ q (heckeT k N χ p a) := by
  funext n
  have hqp : q ≠ p := hpq.symm
  rw [heckeT_def k N χ p (heckeT k N χ q a) n, heckeT_sq_mul k N χ hp hq hpq a n,
    heckeT_def k N χ q (heckeT k N χ p a) n, heckeT_sq_mul k N χ hq hp hqp a n]
  simp only [heckeT_def]
  have e : q ^ 2 * (p ^ 2 * n) = p ^ 2 * (q ^ 2 * n) := by ring
  rw [e]
  by_cases hpn : p ^ 2 ∣ n <;> by_cases hqn : q ^ 2 ∣ n
  · obtain ⟨m, hm⟩ := hpn
    have hp0 : 0 < p ^ 2 := pow_pos hp.pos 2
    have hq0 : 0 < q ^ 2 := pow_pos hq.pos 2
    have h1 : n / p ^ 2 = m := by rw [hm, Nat.mul_div_cancel_left _ hp0]
    have h2 : q ^ 2 ∣ m := (sq_dvd_mul_iff hp hq hpq m).1 (hm ▸ hqn)
    obtain ⟨r, hr⟩ := h2
    have h3 : n / q ^ 2 = p ^ 2 * r := by
      rw [hm, hr, show p ^ 2 * (q ^ 2 * r) = q ^ 2 * (p ^ 2 * r) by ring, Nat.mul_div_cancel_left _ hq0]
    have h4 : p ^ 2 ∣ n / q ^ 2 := ⟨r, h3⟩
    have h5 : n / p ^ 2 / q ^ 2 = r := by rw [h1, hr, Nat.mul_div_cancel_left _ hq0]
    have h6 : n / q ^ 2 / p ^ 2 = r := by rw [h3, Nat.mul_div_cancel_left _ hp0]
    have h7 : q ^ 2 ∣ n / p ^ 2 := ⟨r, by rw [h1, hr]⟩
    have j1 : jacobiSym ((-1) ^ k * ((n / p ^ 2 : ℕ) : ℤ)) q = jacobiSym ((-1) ^ k * (n : ℤ)) q := by
      rw [h1, hm, jac_sq_mul hp hq hpq]
    have j2 : jacobiSym ((-1) ^ k * ((n / q ^ 2 : ℕ) : ℤ)) p = jacobiSym ((-1) ^ k * (n : ℤ)) p := by
      rw [h3, show n = q ^ 2 * (p ^ 2 * r) by rw [hm, hr]; ring, jac_sq_mul hq hp hpq.symm]
    have hpn : p ^ 2 ∣ n := ⟨m, hm⟩
    simp only [hqn, hpn, h4, h7, ite_true, h5, h6, j1, j2]
    ring
  · obtain ⟨m, hm⟩ := hpn
    have hp0 : 0 < p ^ 2 := pow_pos hp.pos 2
    have h1 : n / p ^ 2 = m := by rw [hm, Nat.mul_div_cancel_left _ hp0]
    have h2 : ¬ q ^ 2 ∣ m := fun h => hqn (hm ▸ (sq_dvd_mul_iff hp hq hpq m).2 h)
    have j1 : jacobiSym ((-1) ^ k * (m : ℤ)) q = jacobiSym ((-1) ^ k * (n : ℤ)) q := by
      rw [hm, jac_sq_mul hp hq hpq]
    have hpn : p ^ 2 ∣ n := ⟨m, hm⟩
    simp only [hqn, hpn, h2, h1, j1, ite_true, ite_false]
    ring
  · obtain ⟨m, hm⟩ := hqn
    have hq0 : 0 < q ^ 2 := pow_pos hq.pos 2
    have h1 : n / q ^ 2 = m := by rw [hm, Nat.mul_div_cancel_left _ hq0]
    have h2 : ¬ p ^ 2 ∣ m := fun h => hpn (hm ▸ (sq_dvd_mul_iff hq hp hpq.symm m).2 h)
    have j1 : jacobiSym ((-1) ^ k * (m : ℤ)) p = jacobiSym ((-1) ^ k * (n : ℤ)) p := by
      rw [hm, jac_sq_mul hq hp hpq.symm]
    have hqn : q ^ 2 ∣ n := ⟨m, hm⟩
    simp only [hqn, hpn, h2, h1, j1, ite_true, ite_false]
    ring
  · simp [hpn, hqn]
    ring

/-- **The plus-space condition** $a(n) = 0$ unless $(-1)^k n \equiv 0, 1 \bmod 4$. -/
def PlusCond (k : ℕ) (a : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, ((-1) ^ k * (n : ℤ)) % 4 = 2 ∨ ((-1) ^ k * (n : ℤ)) % 4 = 3 → a n = 0

/-- **The plus space on coefficients:** the sequences satisfying `PlusCond k`, a $\mathbb C$-submodule. -/
def plusSeq (k : ℕ) : Submodule ℂ (ℕ → ℂ) where
  carrier := {a | PlusCond k a}
  zero_mem' := by
    intro n _
    rfl
  add_mem' := by
    intro a b ha hb n hn
    simp [ha n hn, hb n hn]
  smul_mem' := by
    intro c a ha n hn
    simp [ha n hn]

theorem mem_plusSeq {k : ℕ} {a : ℕ → ℂ} : a ∈ plusSeq k ↔ PlusCond k a := Iff.rfl

/-- **For odd $p$, $T(p^2)$ preserves the plus-space condition** (Kohnen 1980 `kohnen1980`, Prop. 2 [unverified]):
$p^2 \equiv 1 \bmod 8$, so $p^2 n$, $n$ and $n/p^2$ have the same class mod 4. -/
@[kb "kohnen1980" "§1, T(p²) preserves the plus space for odd p [unverified]"]
private theorem cls_sq_mul {p : ℕ} (hp : Odd p) (k m : ℕ) :
    ((-1) ^ k * ((p ^ 2 * m : ℕ) : ℤ)) % 4 = ((-1) ^ k * (m : ℤ)) % 4 := by
  obtain ⟨j, rfl⟩ := hp
  have : (-1 : ℤ) ^ k * (((2 * j + 1) ^ 2 * m : ℕ) : ℤ)
      = (-1) ^ k * (m : ℤ) + 4 * ((-1) ^ k * ((j : ℤ) ^ 2 + j) * m) := by push_cast; ring
  rw [this]
  omega

theorem heckeT_plus {k N : ℕ} (χ : DirichletCharacter ℂ (4 * N)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : ℕ → ℂ} (ha : PlusCond k a) : PlusCond k (heckeT k N χ p a) := by
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  intro n hn
  have h1 : a (p ^ 2 * n) = 0 := ha _ (by rw [cls_sq_mul hodd]; exact hn)
  have h2 : a n = 0 := ha n hn
  simp only [heckeT, h1, h2, mul_zero, zero_add]
  split_ifs with hd
  · obtain ⟨m, rfl⟩ := hd
    have hp0 : 0 < p ^ 2 := pow_pos hp.pos 2
    rw [Nat.mul_div_cancel_left _ hp0]
    rw [cls_sq_mul hodd] at hn
    rw [ha m hn, mul_zero]
  · rfl

/-- **$T(p^2)$ maps the plus space to itself** for odd primes $p$, as a statement about the submodule `plusSeq`. -/
theorem heckeT_mem_plusSeq {k N : ℕ} (χ : DirichletCharacter ℂ (4 * N)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : ℕ → ℂ} (ha : a ∈ plusSeq k) : heckeT k N χ p a ∈ plusSeq k :=
  heckeT_plus χ hp hp2 ha

end ModularFormsKB.HalfIntegral
