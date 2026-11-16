/-
# The Hecke recursion in the plus space: fundamental coefficients determine an eigenform

Everything here is formal, on coefficient sequences.

**Kohnen's $T^+(4)$** (Kohnen 1980 `kohnen1980`, Prop. 2 [unverified]; Kohnen–Zagier 1981 `kohnenzagier1981`, §I): on
the plus space of weight $k + \tfrac12$ and level $4$ the operator at $p = 2$ is given by the same formula as $T(p^2)$ for
odd $p$, with the Kronecker symbol at $2$ (`kroneckerTwo`):
$$ (T^+(4)a)(n) = a(4n) + \Big(\frac{(-1)^k n}{2}\Big)2^{k-1}a(n) + 2^{2k-1}a(n/4) $$
(`heckeTPlusFourFormula`), with $a(n/4) = 0$ unless $4 \mid n$, for $(-1)^k n \equiv 0, 1 \bmod 4$; at the other $n$ the
coefficient is $0$ (`heckeTPlusFour`, the plus projection of the formula; corrected, see the erratum below). Check: for the cusp form of weight $13/2$ with
$c(1) = 1$, $c(4) = -56$, $c(9) = 9$ one gets $-56 + 32 = -24 = \tau(2)$ and $9 + 243 = 252 = \tau(3)$.

**Proved here.**
- `heckeTPlusFour_plus`, `heckeTPlusFour_mem_plusSeq`: $T^+(4)$ preserves the plus condition;
  `heckeTPlusFour_of_not_minusIdx`: on plus indices it is Kohnen's formula.
- `not_minusIdx_kohnenDisc_mul_sq`: $|D|g^2$ is a plus index for $D$ fundamental with $(-1)^kD > 0$.
- `exists_kohnenDisc_mul_sq`: every $n \ge 1$ with $(-1)^k n \equiv 0, 1 \bmod 4$ is $|D|f^2$ with $D$ a fundamental
  discriminant, $(-1)^k D > 0$, $f \ge 1$.
- `coeff_mul_sq_eq_zero`: if $c$ satisfies the plus condition, is an eigenvector of $T(p^2)$ for every odd prime $p$ and of
  $T^+(4)$, and $c(|D|) = 0$, then $c(|D|f^2) = 0$ for all $f \ge 1$. The recursion
  $c(p^2 n) = \lambda_p c(n) - (\ldots)c(n) - p^{2k-1}c(n/p^2)$ at $n = |D|g^2$, $f = pg$; the last term is
  $c(|D|(g/p)^2)$ if $p \mid g$, and otherwise vanishes: for odd $p$ because $p^2 \nmid D$, for $p = 2$ because then
  $D = 4m$ and $|D|g^2/4 = |m|g^2$ is outside the plus space.
- `eq_zero_of_fundamental_coeff_eq_zero`: such a $c$ with $c(|D|) = 0$ for all fundamental $D$, $(-1)^kD > 0$, vanishes in
  every degree $n \ge 1$.
-/
import ModularFormsKB.HalfIntegral.Abstract.KohnenReduction

namespace ModularFormsKB.HalfIntegral

open Complex

/-- **Kohnen's formula for $T^+(4)$ on coefficients** (Kohnen 1980 `kohnen1980`, Prop. 2 [unverified]), applied at every
index: $a(4n) + \left(\frac{(-1)^k n}{2}\right)2^{k-1}a(n) + 2^{2k-1}a(n/4)$. This is the coefficient of $T^+(4)a$ only at
plus indices; `heckeTPlusFour` sets the other coefficients to $0$. -/
noncomputable def heckeTPlusFourFormula (k : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (4 * n) + (kroneckerTwo ((-1) ^ k * n) : ℂ) * (2 : ℂ) ^ ((k : ℤ) - 1) * a n +
    if 4 ∣ n then (2 : ℂ) ^ (2 * (k : ℤ) - 1) * a (n / 4) else 0

/-- **Kohnen's $T^+(4)$ on coefficients** (Kohnen 1980 `kohnen1980`, Prop. 2 [unverified]): on the plus space,
$(T^+(4)a)(n) = a(4n) + \left(\frac{(-1)^k n}{2}\right)2^{k-1}a(n) + 2^{2k-1}a(n/4)$ for $(-1)^k n \equiv 0, 1 \bmod 4$
(`heckeTPlusFourFormula`), and $(T^+(4)a)(n) = 0$ otherwise; that is, the plus projection (`plusProj`) of the formula.

Erratum: an earlier version applied the formula at every index. That operator does not preserve the plus
condition: for $k = 6$ and the generator $g = q - 56q^4 + 120q^5 - 240q^8 + 9q^9 + \cdots$ of $S^+_{13/2}(4)$, the
formula at $n = 2$ (where $(-1)^6 \cdot 2 \equiv 2 \bmod 4$) gives $a(8) = -240 \ne 0$. -/
noncomputable def heckeTPlusFour (k : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if MinusIdx k n then 0 else heckeTPlusFourFormula k a n

/-- **$T^+(4)$ is the plus projection of Kohnen's formula.** -/
theorem heckeTPlusFour_eq_plusProj (k : ℕ) (a : ℕ → ℂ) :
    heckeTPlusFour k a = plusProj k (heckeTPlusFourFormula k a) := rfl

/-- **On plus indices $T^+(4)$ is Kohnen's formula:** for $(-1)^k n \equiv 0, 1 \bmod 4$. -/
theorem heckeTPlusFour_of_not_minusIdx (k : ℕ) (a : ℕ → ℂ) {n : ℕ} (hn : ¬ MinusIdx k n) :
    heckeTPlusFour k a n = heckeTPlusFourFormula k a n := by
  simp [heckeTPlusFour, hn]

/-- **Off the plus indices $T^+(4)$ vanishes.** -/
theorem heckeTPlusFour_of_minusIdx (k : ℕ) (a : ℕ → ℂ) {n : ℕ} (hn : MinusIdx k n) : heckeTPlusFour k a n = 0 := by
  simp [heckeTPlusFour, hn]

/-- **$T^+(4)$ maps every sequence into the plus condition** (Kohnen 1980 `kohnen1980`, Prop. 2: $T^+(4)$ acts on the
plus space). -/
theorem heckeTPlusFour_mem_plusSeq (k : ℕ) (a : ℕ → ℂ) : heckeTPlusFour k a ∈ plusSeq k :=
  plusProj_mem k _

/-- **$T^+(4)$ preserves the plus-space condition.** -/
theorem heckeTPlusFour_plus {k : ℕ} {a : ℕ → ℂ} (_ha : PlusCond k a) : PlusCond k (heckeTPlusFour k a) :=
  heckeTPlusFour_mem_plusSeq k a

/-- **Kohnen's formula is $\mathbb C$-linear** on coefficient sequences. -/
noncomputable def heckeTPlusFourFormulaLin (k : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun := heckeTPlusFourFormula k
  map_add' a b := by
    funext n
    simp only [heckeTPlusFourFormula, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c a := by
    funext n
    simp only [heckeTPlusFourFormula, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- **$T^+(4)$ is $\mathbb C$-linear** on coefficient sequences. -/
noncomputable def heckeTPlusFourLin (k : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) :=
  (plusProj k).comp (heckeTPlusFourFormulaLin k)

@[simp] theorem heckeTPlusFourLin_apply (k : ℕ) (a : ℕ → ℂ) : heckeTPlusFourLin k a = heckeTPlusFour k a := rfl

/-! ### Every plus index is $|D|f^2$ -/

private theorem neg_one_pow_cases (k : ℕ) : (-1 : ℤ) ^ k = 1 ∨ (-1 : ℤ) ^ k = -1 := by
  rcases neg_one_pow_eq_or ℤ k with h | h <;> simp [h]

private theorem not_isUnit_two : ¬ IsUnit (2 : ℤ) := by
  rw [Int.isUnit_iff]; omega

/-- **Every plus index is $|D|f^2$** with $D$ fundamental, $(-1)^k D > 0$ and $f \ge 1$. -/
theorem exists_kohnenDisc_mul_sq (k : ℕ) {n : ℕ} (hn : 0 < n) (h : ¬ MinusIdx k n) :
    ∃ (D : ℤ) (f : ℕ), KohnenDisc k D ∧ 0 < f ∧ n = D.natAbs * f ^ 2 := by
  obtain ⟨s, b, hs0, hb0, hsb, hsq⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hσ := neg_one_pow_cases k
  set σ : ℤ := (-1) ^ k with hσdef
  set e : ℤ := σ * s with hedef
  have he_abs : e.natAbs = s := by rcases hσ with h | h <;> simp [e, h]
  have hσe : σ * e = s := by rcases hσ with h | h <;> simp [e, h]
  have he_sq : Squarefree e := by rw [← Int.squarefree_natAbs, he_abs]; exact hsq
  have hn' : σ * (n : ℤ) = e * (b : ℤ) ^ 2 := by rw [← hsb]; push_cast; ring
  have hmod : ¬ (σ * n % 4 = 2 ∨ σ * n % 4 = 3) := h
  have hs0' : (0 : ℤ) < s := by exact_mod_cast hs0
  have he4 : e % 4 ≠ 0 := by
    intro h4
    exact not_isUnit_two (he_sq 2 (by obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero h4; exact ⟨q, by rw [hq]; ring⟩))
  by_cases he1 : e % 4 = 1
  · refine ⟨e, b, ⟨Or.inl ⟨he1, he_sq⟩, by rw [hσe]; exact hs0'⟩, hb0, ?_⟩
    rw [he_abs, ← hsb, mul_comm]
  · have he23 : e % 4 = 2 ∨ e % 4 = 3 := by omega
    have hbeven : 2 ∣ b := by
      by_contra hbodd
      obtain ⟨t, rfl⟩ : Odd b := Nat.odd_iff.2 (by omega)
      have : σ * (n : ℤ) = e + 4 * (e * ((t : ℤ) ^ 2 + t)) := by rw [hn']; push_cast; ring
      generalize σ * (n : ℤ) = x at this hmod
      generalize e * ((t : ℤ) ^ 2 + t) = w at this
      omega
    obtain ⟨f, rfl⟩ := hbeven
    refine ⟨4 * e, f, ⟨Or.inr ⟨e, rfl, he23, he_sq⟩, ?_⟩, by omega, ?_⟩
    · rw [show σ * (4 * e) = 4 * (σ * e) by ring, hσe]; positivity
    · rw [Int.natAbs_mul, he_abs, ← hsb]; norm_num; ring

/-! ### The recursion -/

private theorem sq_dvd_natAbs {D : ℤ} {p : ℕ} (h : p ^ 2 ∣ D.natAbs) : ((p : ℤ) ^ 2) ∣ D := by
  have := Int.natCast_dvd.2 h
  simpa using this

/-- **$|D|g^2$ is a plus index** for $D$ fundamental with $(-1)^kD > 0$: $(-1)^k|D|g^2 = Dg^2$ with
$D, g^2 \equiv 0, 1 \bmod 4$. -/
theorem not_minusIdx_kohnenDisc_mul_sq {k : ℕ} {D : ℤ} (hD : KohnenDisc k D) (g : ℕ) :
    ¬ MinusIdx k (D.natAbs * g ^ 2) := by
  have hσ := neg_one_pow_cases k
  have hsign := hD.2
  have hD4 : D % 4 = 0 ∨ D % 4 = 1 := by
    rcases hD.1 with ⟨h1, _⟩ | ⟨m, rfl, _, _⟩
    · exact Or.inr h1
    · left; omega
  have hDabs : (-1) ^ k * (D.natAbs : ℤ) = D := by
    rcases hσ with h | h <;> rw [h] at hsign ⊢ <;> omega
  have hg : (g : ℤ) ^ 2 % 4 = 0 ∨ (g : ℤ) ^ 2 % 4 = 1 := by
    rcases Nat.even_or_odd g with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · left
      push_cast
      rw [show ((t : ℤ) + t) ^ 2 = 4 * (t * t) by ring]
      generalize (t : ℤ) * t = w
      omega
    · right
      push_cast
      rw [show (2 * (t : ℤ) + 1) ^ 2 = 4 * (t * t + t) + 1 by ring]
      generalize (t : ℤ) * t + t = w
      omega
  have he : (-1) ^ k * ((D.natAbs * g ^ 2 : ℕ) : ℤ) = D * (g : ℤ) ^ 2 := by
    calc (-1) ^ k * ((D.natAbs * g ^ 2 : ℕ) : ℤ) = ((-1) ^ k * (D.natAbs : ℤ)) * (g : ℤ) ^ 2 := by push_cast; ring
      _ = D * (g : ℤ) ^ 2 := by rw [hDabs]
  unfold MinusIdx
  rw [he, Int.mul_emod]
  rcases hD4 with h | h <;> rcases hg with h' | h' <;> simp [h, h']

/-- **The recursion from $|D|$ to $|D|f^2$:** a plus sequence that is an eigenvector of every $T(p^2)$, $p$ odd, and of
$T^+(4)$, with $c(|D|) = 0$, vanishes at every $|D|f^2$. -/
theorem coeff_mul_sq_eq_zero {k : ℕ} {c : ℕ → ℂ} (hplus : c ∈ plusSeq k) (μ : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → p ≠ 2 → heckeT k 1 1 p c = μ p • c) (t : ℂ) (h4 : heckeTPlusFour k c = t • c)
    {D : ℤ} (hD : KohnenDisc k D) (h0 : c D.natAbs = 0) :
    ∀ f : ℕ, 0 < f → c (D.natAbs * f ^ 2) = 0 := by
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ih =>
  intro hf
  by_cases hf1 : f = 1
  · subst hf1; simpa using h0
  have hp : f.minFac.Prime := Nat.minFac_prime hf1
  obtain ⟨g, hg⟩ : f.minFac ∣ f := Nat.minFac_dvd f
  set p := f.minFac with hpdef
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h | h
    · subst h; omega
    · exact h
  have hgf : g < f := by
    rw [hg]; nlinarith [hp.one_lt]
  have hcg : c (D.natAbs * g ^ 2) = 0 := ih g hgf hg0
  have hfn : D.natAbs * f ^ 2 = p ^ 2 * (D.natAbs * g ^ 2) := by rw [hg]; ring
  have hp0 : 0 < p ^ 2 := pow_pos hp.pos 2
  -- the term at $n/p^2$
  have hdiv : p ^ 2 ∣ D.natAbs * g ^ 2 → c (D.natAbs * g ^ 2 / p ^ 2) = 0 := by
    intro hpn
    by_cases hpg : p ∣ g
    · obtain ⟨h, rfl⟩ := hpg
      have hh0 : 0 < h := Nat.pos_of_mul_pos_left hg0
      rw [show D.natAbs * (p * h) ^ 2 = p ^ 2 * (D.natAbs * h ^ 2) by ring, Nat.mul_div_cancel_left _ hp0]
      exact ih h (by nlinarith [hp.one_lt, hgf]) hh0
    · have hcop : Nat.Coprime (p ^ 2) (g ^ 2) :=
        Nat.Coprime.pow 2 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpg)
      have hpD : p ^ 2 ∣ D.natAbs := hcop.dvd_of_dvd_mul_right hpn
      by_cases hp2 : p = 2
      · rw [hp2] at hpD hpg ⊢
        rcases hD.1 with ⟨hD1, _⟩ | ⟨m, rfl, hm23, _⟩
        · exfalso
          have := sq_dvd_natAbs hpD
          push_cast at this
          omega
        · have hσ := neg_one_pow_cases k
          have hsign := hD.2
          have hmabs : (-1) ^ k * (m.natAbs : ℤ) = m := by
            rcases hσ with h | h <;> rw [h] at hsign ⊢ <;> omega
          have hq : 4 * m.natAbs * g ^ 2 / 2 ^ 2 = m.natAbs * g ^ 2 := by
            rw [show 4 * m.natAbs * g ^ 2 = 2 ^ 2 * (m.natAbs * g ^ 2) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
          rw [Int.natAbs_mul, show (4 : ℤ).natAbs = 4 by rfl, hq]
          apply hplus
          obtain ⟨u, rfl⟩ : Odd g := Nat.odd_iff.2 (by omega)
          have : (-1) ^ k * ((m.natAbs * (2 * u + 1) ^ 2 : ℕ) : ℤ) = m + 4 * (m * ((u : ℤ) ^ 2 + u)) := by
            push_cast
            rw [Int.natCast_natAbs] at hmabs
            rw [show (-1 : ℤ) ^ k * (|m| * (2 * u + 1) ^ 2) = (-1) ^ k * |m| * (2 * u + 1) ^ 2 by ring, hmabs]
            ring
          rw [this]
          generalize m * ((u : ℤ) ^ 2 + u) = w
          omega
      · exact absurd (sq_dvd_natAbs hpD) (not_sq_dvd_of_fundamental hD.1 hp hp2)
  rw [hfn]
  by_cases hp2 : p = 2
  · have e := congrFun h4 (D.natAbs * g ^ 2)
    rw [Pi.smul_apply, heckeTPlusFour_of_not_minusIdx k c (not_minusIdx_kohnenDisc_mul_sq hD g)] at e
    simp only [heckeTPlusFourFormula, smul_eq_mul, hcg, mul_zero, add_zero] at e
    rw [hp2] at hdiv ⊢
    split_ifs at e with h4n
    · rw [show (4 : ℕ) = 2 ^ 2 by norm_num] at e h4n
      rw [hdiv h4n, mul_zero, add_zero] at e
      exact e
    · rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; simpa using e
  · have e := congrFun (hT p hp hp2) (D.natAbs * g ^ 2)
    simp only [heckeT, Pi.smul_apply, smul_eq_mul, hcg, mul_zero, add_zero] at e
    split_ifs at e with hpn
    · rw [hdiv hpn, mul_zero, add_zero] at e
      exact e
    · simpa using e

/-- **Fundamental coefficients determine a plus eigenvector:** if $c$ satisfies the plus condition, is an eigenvector
of every $T(p^2)$, $p$ odd, and of $T^+(4)$, and $c(|D|) = 0$ for every fundamental $D$ with $(-1)^kD > 0$, then $c(n) = 0$
for all $n \ge 1$. -/
theorem eq_zero_of_fundamental_coeff_eq_zero {k : ℕ} {c : ℕ → ℂ} (hplus : c ∈ plusSeq k) (μ : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → p ≠ 2 → heckeT k 1 1 p c = μ p • c) (t : ℂ) (h4 : heckeTPlusFour k c = t • c)
    (h : ∀ D : ℤ, KohnenDisc k D → c D.natAbs = 0) : ∀ n : ℕ, 0 < n → c n = 0 := by
  intro n hn
  by_cases hm : MinusIdx k n
  · exact hplus n hm
  · obtain ⟨D, f, hD, hf, rfl⟩ := exists_kohnenDisc_mul_sq k hn hm
    exact coeff_mul_sq_eq_zero hplus μ hT t h4 hD (h D hD) f hf

end ModularFormsKB.HalfIntegral
