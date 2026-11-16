/-
# The Jacobi character $m \mapsto \left(\frac mn\right)$ modulo an odd $n$

For odd $n \ge 1$, `jacobiChar n` is the Dirichlet character modulo $n$ with $m \mapsto \left(\frac mn\right)$
(Jacobi symbol in the upper argument). It is real, and primitive when $n$ is squarefree (for each $p \mid n$ a
non-residue modulo $p$ that is $\equiv 1$ modulo $n/p$ has symbol $-1$).
-/
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Basic

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

private theorem jacobiSym_val_eq {n : ℕ} [NeZero n] (x : ZMod n) (m : ℤ) (h : (m : ZMod n) = x) :
    jacobiSym (x.val : ℤ) n = jacobiSym m n := by
  subst h
  apply jacobiSym.mod_left'
  rw [ZMod.val_intCast, Int.emod_emod]

/-- **The Jacobi character** $m \mapsto \left(\frac mn\right)$ modulo $n$ (meaningful for odd $n$). -/
noncomputable def jacobiChar (n : ℕ) [NeZero n] : DirichletCharacter ℂ n where
  toFun x := (jacobiSym (x.val : ℤ) n : ℂ)
  map_one' := by
    rw [jacobiSym_val_eq (1 : ZMod n) 1 (by simp)]; simp
  map_mul' x y := by
    rw [jacobiSym_val_eq (x * y) ((x.val : ℤ) * y.val) (by simp), jacobiSym.mul_left]
    push_cast; rfl
  map_nonunit' x hx := by
    have : jacobiSym (x.val : ℤ) n = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime]
      intro h
      refine hx ?_
      rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime]
      rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast] at h
      exact Nat.coprime_iff_gcd_eq_one.mpr h
    show ((jacobiSym (x.val : ℤ) n : ℤ) : ℂ) = 0
    rw [this]; simp

variable {n : ℕ} [NeZero n]

theorem jacobiChar_intCast (_hn : Odd n) (m : ℤ) : jacobiChar n m = (jacobiSym m n : ℂ) := by
  show ((jacobiSym (((m : ZMod n)).val : ℤ) n : ℤ) : ℂ) = _
  rw [jacobiSym_val_eq _ m rfl]

theorem jacobiChar_natCast (hn : Odd n) (m : ℕ) : jacobiChar n m = (jacobiSym m n : ℂ) := by
  have := jacobiChar_intCast hn (m : ℤ)
  simpa using this

/-- The Jacobi character is its own inverse. -/
theorem jacobiChar_inv (hn : Odd n) : (jacobiChar n)⁻¹ = jacobiChar n := by
  refine MulChar.ext' fun a => ?_
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective a
  rw [MulChar.inv_apply_eq_inv', jacobiChar_intCast hn]
  rcases jacobiSym.trichotomy m n with h | h | h <;> simp [h]

/-- **The Jacobi character of a squarefree odd modulus is primitive.** -/
theorem isPrimitive_jacobiChar (hn : Odd n) (hsq : Squarefree n) : (jacobiChar n).IsPrimitive := by
  set χ := jacobiChar n with hχ
  have hdvd : χ.conductor ∣ n := DirichletCharacter.conductor_dvd_level χ
  rw [DirichletCharacter.isPrimitive_def]
  by_contra hne
  set c := χ.conductor with hc
  obtain ⟨e, he⟩ := hdvd
  have hc0 : c ≠ 0 := DirichletCharacter.conductor_ne_zero χ
  have he1 : e ≠ 1 := by rintro rfl; apply hne; simpa using he.symm
  obtain ⟨p, hp, hpe⟩ := Nat.exists_prime_and_dvd he1
  have hpn : p ∣ n := he ▸ Dvd.dvd.mul_left hpe c
  obtain ⟨m, hm⟩ := hpn
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact NeZero.ne n hm
  have hpm : Nat.Coprime p m := by
    by_contra h
    have h' := (Nat.Prime.not_coprime_iff_dvd.mp h)
    obtain ⟨q, hq, hqp, hqm⟩ := h'
    have : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
    subst this
    have : q * q ∣ n := hm ▸ Nat.mul_dvd_mul_left q hqm
    exact hq.one_lt.ne' (Nat.isUnit_iff.mp (hsq q this))
  -- c ∣ m
  have hcm : c ∣ m := by
    have hcn : c ∣ p * m := hm ▸ ⟨e, he⟩
    have hpc : Nat.Coprime p c := by
      rcases (Nat.coprime_or_dvd_of_prime hp c) with h | h
      · exact h.symm.symm
      · exfalso
        obtain ⟨d, hd⟩ := h
        have : p * p ∣ n := by
          rw [he, hd]; exact ⟨d * (e / p), by
            obtain ⟨f, hf⟩ := hpe; subst hf
            rw [Nat.mul_div_cancel_left _ hp.pos]; ring⟩
        exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p this))
    exact (Nat.Coprime.dvd_of_dvd_mul_left hpc.symm hcn)
  have hpodd : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hn) (hm ▸ ⟨m, by omega⟩ : Even n) |>.elim
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hpm g.val 1
  have hnpm : p ∣ n ∧ m ∣ n := ⟨⟨m, hm⟩, ⟨p, by rw [hm, mul_comm]⟩⟩
  obtain ⟨a, hao, ha1, ha2⟩ : ∃ a : ℕ, Odd a ∧ a ≡ g.val [MOD p] ∧ a ≡ 1 [MOD m] := by
    rcases Nat.even_or_odd k with h | h
    · refine ⟨k + n, h.add_odd hn, ?_, ?_⟩
      · have : k + n ≡ k + 0 [MOD p] := Nat.ModEq.add_left _ ((Nat.modEq_zero_iff_dvd).mpr hnpm.1)
        exact this.trans (by simpa using hk1)
      · have : k + n ≡ k + 0 [MOD m] := Nat.ModEq.add_left _ ((Nat.modEq_zero_iff_dvd).mpr hnpm.2)
        exact this.trans (by simpa using hk2)
    · exact ⟨k, h, hk1, hk2⟩
  have hacop : a.Coprime n := by
    rw [hm]
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro hd
      have : (a : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff a p).mpr hd
      have h2 : (a : ZMod p) = g := by
        rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr ha1, ZMod.natCast_zmod_val]
      rw [this] at h2
      exact hg (h2 ▸ IsSquare.zero)
    · have := ha2.gcd_eq
      simpa [Nat.Coprime, Nat.gcd_comm m] using this
  have hmod : a ≡ 1 [MOD c] := ha2.of_dvd hcm
  have h1 := (DirichletCharacter.conductor_dvd_iff_forall_odd χ (d := c)).mp dvd_rfl a hao hacop hmod
  rw [hχ, jacobiChar_natCast hn] at h1
  have hJ : jacobiSym (a : ℤ) n = -1 := by
    rw [hm, jacobiSym.mul_right' _ hp.ne_zero hm0]
    have e1 : jacobiSym (a : ℤ) p = -1 := by
      rw [jacobiSym.mod_left' (a₂ := (g.val : ℤ)), ← jacobiSym.legendreSym.to_jacobiSym,
        legendreSym.eq_neg_one_iff]
      · simpa using hg
      · rw [← Int.natCast_mod, ← Int.natCast_mod]; exact_mod_cast ha1
    have e2 : jacobiSym (a : ℤ) m = 1 := by
      rw [jacobiSym.mod_left' (a₂ := 1), jacobiSym.one_left]
      rw [← Int.natCast_mod]; exact_mod_cast ha2
    rw [e1, e2]; rfl
  rw [hJ] at h1
  norm_num at h1

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
