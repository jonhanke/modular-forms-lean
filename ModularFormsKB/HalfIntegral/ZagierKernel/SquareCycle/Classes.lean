/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
-/
import ModularFormsKB.HalfIntegral.ZagierKernel.SquareCycle.SquareRep
import ModularFormsKB.HalfIntegral.Abstract.TwistContinuationProof

/-!
# Forms of square discriminant and their genus character

**Classes.** Every integral binary quadratic form of discriminant $n^2$, $n \ge 1$, is properly equivalent to exactly one
form $[0, n, c]$ with $0 \le c < n$ (`BinQF.squareRep`): a zero $(p, r)$ of $Q$ with $\gcd(p, r) = 1$ is the first column of
some $\gamma \in \mathrm{SL}_2(\mathbb Z)$, so $Q\circ\gamma = [0, \pm n, c']$; if the sign is $-$, the other zero is moved to the
first column instead; a translation then reduces $c'$ modulo $n$. Conversely $[0,n,c]\circ\gamma = [0,n,c']$ forces
$\gamma_{1,0} = 0$ (the other case gives middle coefficient $-n$), so $c' \equiv c \bmod n$.

**The genus character at $D^2$.** For $D$ a fundamental discriminant and $Q$ equivalent to $[0, |D|, c]$, every value of
$Q$ prime to $D$ is a value $y(|D|x + cy) \equiv cy^2 \pmod{|D|}$ of $[0,|D|,c]$, so $\chi_D(Q) = \left(\frac Dc\right)$
(Tau Ceti `kroneckerSym D c`; both sides vanish when $\gcd(c, D) > 1$, including $c = 0$ for $|D| > 1$; this library's
`kroneckerInt D 0` is $1$, the Jacobi convention, which is why `kroneckerSym` is used here). This uses only that $m \mapsto \left(\frac Dm\right)$ is a
character modulo $|D|$ on all of $\mathbb Z$ (Tau Ceti `kroneckerChar`), not the named input `GenusCharacterWellDefined`.
-/

namespace ModularFormsKB.HalfIntegral

namespace BinQF

open Matrix MatrixGroups

/-! ### Helper lemmas for the classes -/

private theorem exists_col (p r : ℤ) (h : IsCoprime p r) :
    ∃ γ : SL(2, ℤ), γ 0 0 = p ∧ γ 1 0 = r := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨⟨!![p, -v; r, u], ?_⟩, rfl, rfl⟩
  rw [Matrix.det_fin_two_of]
  linear_combination huv

private theorem det_eq (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.det_coe
  rwa [Matrix.det_fin_two] at this

private theorem exists_zero (Q : BinQF) {n : ℕ} (hn : 0 < n) (hQ : Q.disc = (n : ℤ) ^ 2) :
    ∃ p r : ℤ, IsCoprime p r ∧ Q.val p r = 0 := by
  by_cases ha : Q.a = 0
  · exact ⟨1, 0, isCoprime_one_left, by simp [val, ha]⟩
  · have hpos : 0 < Int.gcd ((n : ℤ) - Q.b) (2 * Q.a) := Int.gcd_pos_iff.mpr (Or.inr (by omega))
    have hcop := Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hpos)
    set g : ℤ := (Int.gcd ((n : ℤ) - Q.b) (2 * Q.a) : ℤ) with hg
    have hgpos : 0 < g := Int.natCast_pos.mpr hpos
    have e1 : ((n : ℤ) - Q.b) / g * g = (n : ℤ) - Q.b :=
      Int.ediv_mul_cancel (Int.gcd_dvd_left _ _)
    have e2 : (2 * Q.a) / g * g = 2 * Q.a := Int.ediv_mul_cancel (Int.gcd_dvd_right _ _)
    refine ⟨_, _, hcop, ?_⟩
    set p := ((n : ℤ) - Q.b) / g
    set r := (2 * Q.a) / g
    have key : g ^ 2 * Q.val p r =
        Q.a * (p * g) ^ 2 + Q.b * (p * g) * (r * g) + Q.c * (r * g) ^ 2 := by
      simp only [val]; ring
    rw [e1, e2] at key
    have hd := hQ
    simp only [disc] at hd
    have h0 : g ^ 2 * Q.val p r = 0 := by rw [key]; linear_combination (-Q.a) * hd
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (pow_ne_zero 2 hgpos.ne')
    · exact h

private theorem exists_a_zero (Q : BinQF) {n : ℕ} (hn : 0 < n) (hQ : Q.disc = (n : ℤ) ^ 2) :
    ∃ γ : SL(2, ℤ), (Q.comp γ).a = 0 := by
  obtain ⟨p, r, hc, hz⟩ := exists_zero Q hn hQ
  obtain ⟨γ, h1, h2⟩ := exists_col p r hc
  refine ⟨γ, ?_⟩
  show Q.val (γ 0 0) (γ 1 0) = 0
  rw [h1, h2]; exact hz

private theorem exists_flip {n : ℕ} (hn : 0 < n) (c : ℤ) :
    ∃ γ : SL(2, ℤ), ((⟨0, -(n : ℤ), c⟩ : BinQF).comp γ).a = 0 ∧
      ((⟨0, -(n : ℤ), c⟩ : BinQF).comp γ).b = n := by
  have hpos : 0 < Int.gcd c (n : ℤ) := Int.gcd_pos_iff.mpr (Or.inr (by omega))
  have hcop := Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hpos)
  set g : ℤ := (Int.gcd c (n : ℤ) : ℤ) with hg
  have hgpos : 0 < g := Int.natCast_pos.mpr hpos
  have e1 : c / g * g = c := Int.ediv_mul_cancel (Int.gcd_dvd_left _ _)
  have e2 : (n : ℤ) / g * g = n := Int.ediv_mul_cancel (Int.gcd_dvd_right _ _)
  set p := c / g
  set r := (n : ℤ) / g
  have hr : r ≠ 0 := by
    intro h0; rw [h0, zero_mul] at e2; omega
  have key : g ^ 2 * (-(n : ℤ) * p * r + c * r ^ 2) = 0 := by
    have : g ^ 2 * (-(n : ℤ) * p * r + c * r ^ 2) =
        -(n : ℤ) * (p * g) * (r * g) + c * (r * g) ^ 2 := by ring
    rw [this, e1, e2]; ring
  have hz : -(n : ℤ) * p * r + c * r ^ 2 = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h (pow_ne_zero 2 hgpos.ne')
    · exact h
  have E : c * r = n * p := by
    have : r * (c * r - n * p) = 0 := by linear_combination hz
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hr
    · linarith
  obtain ⟨γ, h1, h2⟩ := exists_col p r hcop
  have hdet := det_eq γ
  rw [h1, h2] at hdet
  refine ⟨γ, ?_, ?_⟩
  · show (0 : ℤ) * (γ 0 0) ^ 2 + (-(n : ℤ)) * γ 0 0 * γ 1 0 + c * (γ 1 0) ^ 2 = 0
    rw [h1, h2]; linear_combination hz
  · show 2 * (0 : ℤ) * γ 0 0 * γ 0 1 + (-(n : ℤ)) * (γ 0 0 * γ 1 1 + γ 0 1 * γ 1 0) +
      2 * c * γ 1 0 * γ 1 1 = n
    rw [h1, h2]
    linear_combination (2 * γ 1 1) * E + (n : ℤ) * hdet

private theorem exists_reduce {n : ℕ} (hn : 0 < n) (c : ℤ) :
    ∃ c' : ℕ, c' < n ∧ Equiv (⟨0, n, c⟩ : BinQF) (squareRep n c') := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnn : (0 : ℤ) ≤ c % n := Int.emod_nonneg _ hn'
  have hlt : c % (n : ℤ) < n := Int.emod_lt_of_pos _ (by exact_mod_cast hn)
  refine ⟨(c % (n : ℤ)).toNat, by omega, ⟨⟨!![1, -(c / n); 0, 1], by simp⟩, ?_⟩⟩
  have hc : (((c % (n : ℤ)).toNat : ℕ) : ℤ) = c % n := Int.toNat_of_nonneg hnn
  ext
  · simp [squareRep, comp, val]
  · simp [squareRep, comp, val]
  · simp only [squareRep, comp, val]
    rw [hc, Int.emod_def]
    simp
    ring

private theorem eq_b_cases (Q : BinQF) {n : ℕ} (hQ : Q.disc = (n : ℤ) ^ 2) (ha : Q.a = 0) :
    Q.b = n ∨ Q.b = -(n : ℤ) := by
  simp only [disc, ha] at hQ
  have : (Q.b - n) * (Q.b + n) = 0 := by linear_combination hQ
  rcases mul_eq_zero.mp this with h | h
  · left; linarith
  · right; linarith

/-- **Every form of discriminant $n^2$ is equivalent to some $[0, n, c]$ with $0 \le c < n$.** -/
theorem exists_equiv_squareRep (Q : BinQF) {n : ℕ} (hn : 0 < n) (hQ : Q.disc = (n : ℤ) ^ 2) :
    ∃ c : ℕ, c < n ∧ Equiv Q (squareRep n c) := by
  obtain ⟨γ, hγ⟩ := exists_a_zero Q hn hQ
  have hQ1 : (Q.comp γ).disc = (n : ℤ) ^ 2 := by rw [disc_comp_SL, hQ]
  have e1 : Equiv Q (Q.comp γ) := ⟨γ, rfl⟩
  rcases eq_b_cases _ hQ1 hγ with hb | hb
  · have : Q.comp γ = ⟨0, n, (Q.comp γ).c⟩ := by ext <;> simp [hγ, hb]
    obtain ⟨c', hc', he⟩ := exists_reduce hn (Q.comp γ).c
    rw [← this] at he
    exact ⟨c', hc', e1.trans he⟩
  · have h1 : Q.comp γ = ⟨0, -(n : ℤ), (Q.comp γ).c⟩ := by ext <;> simp [hγ, hb]
    obtain ⟨δ, hδa, hδb⟩ := exists_flip hn (Q.comp γ).c
    rw [← h1] at hδa hδb
    have h2 : (Q.comp γ).comp δ = ⟨0, n, ((Q.comp γ).comp δ).c⟩ := by
      ext
      · exact hδa
      · exact hδb
      · rfl
    obtain ⟨c', hc', he⟩ := exists_reduce hn ((Q.comp γ).comp δ).c
    rw [← h2] at he
    exact ⟨c', hc', (e1.trans ⟨δ, rfl⟩).trans he⟩

/-- **The forms $[0, n, c]$, $0 \le c < n$, are pairwise inequivalent.** -/
theorem eq_of_equiv_squareRep {n : ℕ} (hn : 0 < n) {c c' : ℕ} (hc : c < n) (hc' : c' < n)
    (h : Equiv (squareRep n c) (squareRep n c')) : c = c' := by
  obtain ⟨γ, hγ⟩ := h
  have hA := congrArg BinQF.a hγ
  have hB := congrArg BinQF.b hγ
  have hC := congrArg BinQF.c hγ
  simp only [squareRep, comp, val] at hA hB hC
  have hdet := det_eq γ
  generalize γ 0 0 = p at *
  generalize γ 0 1 = q at *
  generalize γ 1 0 = r at *
  generalize γ 1 1 = s at *
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hn
  have hr : r = 0 := by
    by_contra hr
    have h1 : n * p + c * r = 0 := by
      have : r * (n * p + c * r) = 0 := by linear_combination -hA
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hr
      · exact h
    have : (n : ℤ) = -n := by linear_combination hB - (n : ℤ) * hdet + 2 * s * h1
    omega
  subst hr
  have hs : s ^ 2 = 1 := by
    have : p * s = 1 := by linear_combination hdet
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' this with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> norm_num
  have hk : (c' : ℤ) = c + n * (q * s) := by linear_combination hC + c * hs
  have hc2 : (c : ℤ) < n := by exact_mod_cast hc
  have hc2' : (c' : ℤ) < n := by exact_mod_cast hc'
  have hc0 : (0 : ℤ) ≤ c := by positivity
  have hc0' : (0 : ℤ) ≤ c' := by positivity
  rcases lt_trichotomy (q * s) 0 with h | h | h
  · nlinarith
  · rw [h] at hk; omega
  · nlinarith

/-! ### The genus character -/

private theorem kroneckerInt_eq_kroneckerSym {D : ℤ} (hD0 : D ≠ 0) {m : ℤ} (hm : m ≠ 0) :
    kroneckerInt D m = TauCeti.kroneckerSym D m := by
  have hn : m.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm
  have hk := kroneckerDisc_eq_kroneckerSym D hn
  unfold kroneckerInt
  rw [hk]
  rcases lt_or_gt_of_ne hm with hneg | hpos
  · have h1 : TauCeti.kroneckerSym D m =
        TauCeti.kroneckerSym D (-1) * TauCeti.kroneckerSym D (m.natAbs : ℤ) := by
      rw [← TauCeti.kroneckerSym_mul_right D (by norm_num) (by exact_mod_cast hn)]
      congr 1; omega
    rw [h1, if_pos hneg, TauCeti.kroneckerSym_neg_one_right]
    rcases lt_or_gt_of_ne hD0 with hD | hD
    · rw [if_pos hD, Int.sign_eq_neg_one_of_neg hD]; ring
    · rw [if_neg (not_lt.mpr hD.le), Int.sign_eq_one_of_pos hD]; ring
  · rw [if_neg (not_lt.mpr hpos.le), mul_one]
    have : (m.natAbs : ℤ) = m := by omega
    rw [this]

private theorem kroneckerInt_zero (D : ℤ) : kroneckerInt D 0 = 1 := by
  simp [kroneckerInt, kroneckerDisc]

private theorem eq_one_of_coprime_zero {D : ℤ} (hmod : D ≡ 0 [ZMOD 4] ∨ D ≡ 1 [ZMOD 4])
    (h : IsCoprime (0 : ℤ) D) : D = 1 := by
  rcases Int.isUnit_iff.mp (isCoprime_zero_left.mp h) with h | h
  · exact h
  · subst h
    rcases hmod with h | h <;> unfold Int.ModEq at h <;> omega

private theorem kroneckerInt_of_val {D : ℤ} (hD0 : D ≠ 0)
    (hmod : D ≡ 0 [ZMOD 4] ∨ D ≡ 1 [ZMOD 4]) (c x y : ℤ)
    (hcop : IsCoprime ((D.natAbs : ℤ) * x * y + c * y ^ 2) D) :
    kroneckerInt D ((D.natAbs : ℤ) * x * y + c * y ^ 2) = TauCeti.kroneckerSym D c := by
  have hD1 : D ≠ -1 := by
    rintro rfl
    rcases hmod with h | h <;> unfold Int.ModEq at h <;> omega
  by_cases hm : (D.natAbs : ℤ) * x * y + c * y ^ 2 = 0
  · rw [hm] at hcop ⊢
    have := eq_one_of_coprime_zero hmod hcop
    subst this
    rw [kroneckerInt_zero, TauCeti.kroneckerSym_one_left]
  · rw [kroneckerInt_eq_kroneckerSym hD0 hm]
    have hy : IsCoprime y D := by
      have : (D.natAbs : ℤ) * x * y + c * y ^ 2 = y * (D.natAbs * x + c * y) := by ring
      rw [this] at hcop
      exact hcop.of_mul_left_left
    have hg : D.gcd y = 1 := Int.isCoprime_iff_gcd_eq_one.mp hy.symm
    have hmodeq : c * y ^ 2 ≡ (D.natAbs : ℤ) * x * y + c * y ^ 2 [ZMOD D] := by
      apply Int.modEq_iff_dvd.mpr
      have : (D.natAbs : ℤ) * x * y + c * y ^ 2 - c * y ^ 2 = D.natAbs * (x * y) := by ring
      rw [this]
      exact Dvd.dvd.mul_right (Int.dvd_natAbs.mpr dvd_rfl) _
    rw [TauCeti.kroneckerSym_mod_right' hmod hmodeq.symm,
      TauCeti.kroneckerSym_mul_right_of_ne_neg_one hD1, TauCeti.kroneckerSym_pow_right]
    have hne : TauCeti.kroneckerSym D y ≠ 0 := fun h0 ↦ TauCeti.kroneckerSym_eq_zero_iff.mp h0 hg
    rcases TauCeti.kroneckerSym_trichotomy D y with h | h | h
    · exact absurd h hne
    · rw [h]; ring
    · rw [h]; ring

private theorem squareRep_val (n : ℕ) (c : ℤ) (x y : ℤ) :
    (squareRep n c).val x y = (n : ℤ) * x * y + c * y ^ 2 := by
  simp [squareRep, val]

private theorem isFund_facts {D : ℤ} (hD : IsFundamentalDiscriminant D) :
    D ≠ 0 ∧ (D ≡ 0 [ZMOD 4] ∨ D ≡ 1 [ZMOD 4]) := by
  rcases hD with ⟨h, -⟩ | ⟨m, hm, h, -⟩
  · refine ⟨by omega, Or.inr ?_⟩
    unfold Int.ModEq; omega
  · refine ⟨by omega, Or.inl ?_⟩
    unfold Int.ModEq; omega

/-- **The genus character at the square discriminant $D^2$**: for $D$ a fundamental discriminant and $Q$ equivalent to
$[0, |D|, c]$, $\chi_D(Q) = \left(\frac Dc\right)$. -/
theorem genusChar_of_equiv_squareRep {D : ℤ} (hD : IsFundamentalDiscriminant D) {Q : BinQF} {c : ℕ}
    (h : Equiv Q (squareRep D.natAbs c)) : genusChar D Q = TauCeti.kroneckerSym D c := by
  obtain ⟨hD0, hmod⟩ := isFund_facts hD
  by_cases hex : ∃ x y : ℤ, IsCoprime (Q.val x y) D
  · obtain ⟨x, y, hxy⟩ := hex
    have h' : ∃ p : ℕ, IsCoprime (Q.val (Denumerable.ofNat (ℤ × ℤ) p).1
        (Denumerable.ofNat (ℤ × ℤ) p).2) D :=
      ⟨Encodable.encode (x, y), by rw [Denumerable.ofNat_encode]; exact hxy⟩
    have main : ∀ z : ℤ × ℤ, IsCoprime (Q.val z.1 z.2) D →
        kroneckerInt D (Q.val z.1 z.2) = TauCeti.kroneckerSym D c := by
      intro z hz
      obtain ⟨x', y', hv⟩ := h.symm.represents z.1 z.2
      rw [← hv, squareRep_val] at hz ⊢
      exact kroneckerInt_of_val hD0 hmod c x' y' hz
    rw [genusChar, dif_pos h']
    exact main _ (Nat.find_spec h')
  · push Not at hex
    rw [genusChar_eq_zero hex, eq_comm, TauCeti.kroneckerSym_eq_zero_iff]
    intro hg
    obtain ⟨x', y', hv⟩ := h.represents 0 1
    rw [squareRep_val] at hv
    apply hex x' y'
    rw [hv]
    have : IsCoprime D (c : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hg
    simpa using this.symm

end BinQF

end ModularFormsKB.HalfIntegral
