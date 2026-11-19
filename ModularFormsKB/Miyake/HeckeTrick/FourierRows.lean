import ModularFormsKB.Miyake.HeckeTrick.FourierExpansion

/-!
# Miyake §7.2, proof of Theorem 7.2.9: the series $E_k(z,s;\chi,\psi)$ row by row

Miyake, *Modular Forms*, §7.2, pp. 283–285. For $k + 2\operatorname{Re}s > 2$ the series (7.2.1) is absolutely convergent,
so it is the sum over $m \in \mathbb Z$ of the rows $R(m) = \sum_n\chi(m)\psi(n)(mz+n)^{-k}|mz+n|^{-2s}$
(`heckeRow`). The row $m = 0$ is $C(s)$; the rows $\pm m$ agree when $\chi(-1)\psi(-1) = (-1)^k$; for $m = c \ge 1$,
splitting $n$ into residue classes mod $M$ and writing $(w+n)^{-k}|w+n|^{-2s} = (w+n)^{-k-s}(\bar w+n)^{-s}$
($w = cz \in \mathbf H$) gives $R(c) = \chi(c)M^{-k-2s}\sum_{a \bmod M}\psi(a)S((cz+a)/M;k+s,s)$, and Theorem 7.2.8
expands each $S$. The finite Fourier transform of $\psi$ is `charFourier`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped UpperHalfPlane
open scoped Real

noncomputable section

namespace ModularFormsKB.Miyake.HeckeTrick

open ModularFormsKB.Miyake.Wave2B

variable {L M : ℕ}

/-- The row $R(c) = \sum_n\chi(c)\psi(n)(cz+n)^{-k}|cz+n|^{-2s}$ of (7.2.1).
**Restriction:** the row converges absolutely for $k + 2\operatorname{Re}(s) > 1$ (terms of size $|cz +
n|^{-k-2\operatorname{Re}(s)}$). Elsewhere the value is $0$ by Lean's convention for a non-summable `∑'`, not an
analytic continuation or the intended value. -/
def heckeRow (k : ℤ) (s : ℂ) (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (z : ℍ) (c : ℤ) : ℂ :=
  ∑' n : ℤ, χ (c : ZMod L) * ψ (n : ZMod M) * heckeSummand k s ![c, n] z

/-- The finite Fourier transform $F(j) = \sum_{a=0}^{M-1}\psi(a)e^{2\pi iaj/M}$. -/
def charFourier (ψ : DirichletCharacter ℂ M) (j : ℤ) : ℂ :=
  ∑ a ∈ Finset.range M, ψ (a : ZMod M) * cexp (2 * π * I * a * j / M)

/-- The absolutely convergent series (7.2.1) is the sum of its rows. -/
theorem eisensteinCharS_eq_tsum_heckeRow {k : ℤ} {s : ℂ} (hs : 2 < (k : ℝ) + 2 * s.re)
    (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (z : ℍ) :
    eisensteinCharS k s χ ψ z = ∑' c : ℤ, heckeRow k s χ ψ z c := by
  have hW : Summable fun x : Fin 2 → ℤ ↦ χ (x 0) * ψ (x 1) * heckeSummand k s x z :=
    (summable_eisensteinCharS hs χ ψ z).of_norm
  have hsum : Summable fun p : ℤ × ℤ ↦ χ p.1 * ψ p.2 * heckeSummand k s ![p.1, p.2] z := by
    simpa [Function.comp_def] using (finTwoArrowEquiv ℤ).symm.summable_iff.mpr hW
  unfold heckeRow
  rw [eisensteinCharS, ← hsum.tsum_prod, ← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  refine tsum_congr fun p ↦ ?_
  simp

theorem summable_heckeRow {k : ℤ} {s : ℂ} (hs : 2 < (k : ℝ) + 2 * s.re)
    (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (z : ℍ) :
    Summable (heckeRow k s χ ψ z) := by
  have hW : Summable fun x : Fin 2 → ℤ ↦ χ (x 0) * ψ (x 1) * heckeSummand k s x z :=
    (summable_eisensteinCharS hs χ ψ z).of_norm
  have hsum : Summable fun p : ℤ × ℤ ↦ χ p.1 * ψ p.2 * heckeSummand k s ![p.1, p.2] z := by
    simpa [Function.comp_def] using (finTwoArrowEquiv ℤ).symm.summable_iff.mpr hW
  exact hsum.prod

/-- The rows $\pm c$ agree when $\chi(-1)\psi(-1) = (-1)^k$. -/
theorem heckeRow_neg {k : ℤ} (s : ℂ) (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (hpar : χ (-1) * ψ (-1) = (-1) ^ k) (z : ℍ) (c : ℤ) :
    heckeRow k s χ ψ z (-c) = heckeRow k s χ ψ z c := by
  unfold heckeRow
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n ↦ ?_
  have hv : (![-c, -n] : Fin 2 → ℤ) = -![c, n] := by
    ext i; fin_cases i <;> simp
  simp only [Equiv.neg_apply, hv, heckeSummand_neg, Int.cast_neg]
  rw [show -(c : ZMod L) = (-1) * c by ring, show -(n : ZMod M) = (-1) * n by ring,
    map_mul, map_mul]
  have hsq : ((-1 : ℂ) ^ k) * ((-1) ^ k) = 1 := by rw [← mul_zpow]; simp
  linear_combination (χ c * ψ n * heckeSummand k s ![c, n] z * (-1) ^ k) * hpar
    + χ c * ψ n * heckeSummand k s ![c, n] z * hsq

/-- **Miyake (7.2.6).** The row $c = 0$ is $C(s)$. -/
theorem heckeRow_zero {k : ℤ} {s : ℂ} (hs : 2 < (k : ℝ) + 2 * s.re) [NeZero M]
    (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (hpar : χ (-1) * ψ (-1) = (-1) ^ k) (z : ℍ) :
    heckeRow k s χ ψ z 0 = heckeC k L ψ s := by
  unfold heckeRow heckeC
  by_cases hL : L = 1
  · subst hL
    simp only [↓reduceIte]
    have h0 : χ (((0 : ℤ)) : ZMod 1) = 1 := by
      rw [show (((0 : ℤ)) : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
    have h1 : χ (-1) = 1 := by
      rw [show (-1 : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
    rw [h1, one_mul] at hpar
    simp only [h0, one_mul]
    have hW : Summable fun x : Fin 2 → ℤ ↦ χ (x 0) * ψ (x 1) * heckeSummand k s x z :=
      (summable_eisensteinCharS hs χ ψ z).of_norm
    have hsum : Summable fun p : ℤ × ℤ ↦ χ p.1 * ψ p.2 * heckeSummand k s ![p.1, p.2] z := by
      simpa [Function.comp_def] using (finTwoArrowEquiv ℤ).symm.summable_iff.mpr hW
    set g : ℤ → ℂ := fun n ↦ ψ (n : ZMod M) * heckeSummand k s ![0, n] z with hg
    have hgs : Summable g := by
      refine (hsum.comp_injective (i := fun n : ℤ ↦ ((0 : ℤ), n))
        (fun a b h ↦ by simpa using h)).congr fun n ↦ ?_
      simp only [Function.comp_apply, hg, Int.cast_zero]
      rw [show χ (0 : ZMod 1) = 1 from h0, one_mul]
    have hgE : Function.Even g := by
      intro n
      have hv : (![0, -n] : Fin 2 → ℤ) = -![0, n] := by
        ext i; fin_cases i <;> simp
      simp only [hg, hv, heckeSummand_neg, Int.cast_neg]
      rw [show -(n : ZMod M) = (-1) * n by ring, map_mul, hpar]
      have hsq : ((-1 : ℂ) ^ k) * ((-1) ^ k) = 1 := by rw [← mul_zpow]; simp
      linear_combination (ψ n * heckeSummand k s ![0, n] z) * hsq
    have hre : 1 < (2 * s + k).re := by simp; linarith
    rw [DirichletCharacter.LFunction_eq_LSeries ψ hre, tsum_int_eq_zero_add_two_mul_tsum_pnat hgE hgs]
    have hg0 : g 0 = 0 := by simp [hg, heckeSummand]
    have hsupp : Function.support (LSeries.term (fun n : ℕ ↦ ψ (n : ZMod M)) (2 * s + k)) ⊆
        Set.range ((↑) : ℕ+ → ℕ) := by
      intro n hn
      refine ⟨⟨n, Nat.pos_of_ne_zero ?_⟩, rfl⟩
      rintro rfl
      simp [LSeries.term] at hn
    rw [hg0, zero_add, LSeries, ← Function.Injective.tsum_eq PNat.coe_injective hsupp]
    · simp only [nsmul_eq_mul, Nat.cast_ofNat]
      congr 1
      refine tsum_congr fun m ↦ ?_
      have hm : ((m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast m.ne_zero
      have hv : (![0, ((m : ℕ) : ℤ)] : Fin 2 → ℤ) ≠ 0 := by
        intro h
        have := congrFun h 1
        simp at this
      simp only [hg, LSeries.term_def, m.ne_zero, ↓reduceIte, heckeSummand, hv, Int.cast_natCast,
        Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_zero, zero_mul, zero_add,
        Complex.norm_natCast, Complex.ofReal_natCast]
      rw [div_eq_mul_inv, ← Complex.cpow_neg, show -(2 * s + k) = ((-k : ℤ) : ℂ) + (-2 * s) by
        push_cast; ring, Complex.cpow_add _ _ hm, Complex.cpow_intCast]
  · have : Nontrivial (ZMod L) := ZMod.nontrivial_iff.mpr hL
    simp only [hL, ↓reduceIte]
    rw [show (((0 : ℤ)) : ZMod L) = 0 from Int.cast_zero, MulChar.map_zero]
    simp

/-- For $w \in \mathbf H$ (here $w = cz + n$, $c \ge 1$): $w^{-k}|w|^{-2s} = w^{-k-s}\bar w^{-s}$. -/
theorem cpow_mul_norm_cpow {w : ℂ} (hw : 0 < w.im) (k : ℤ) (s : ℂ) :
    w ^ (-k) * ((‖w‖ : ℝ) : ℂ) ^ (-2 * s) = w ^ (-((k : ℂ) + s)) * ((starRingEnd ℂ) w) ^ (-s) := by
  have hw0 : w ≠ 0 := fun h ↦ by simp [h] at hw
  have hcw0 : (starRingEnd ℂ) w ≠ 0 := (map_ne_zero _).mpr hw0
  have hn : (‖w‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hw0
  have harg : w.arg ≠ π := by
    have := Complex.arg_lt_pi_iff.mpr (Or.inr hw.ne')
    exact this.ne
  have hlog : Complex.log ((starRingEnd ℂ) w) = (starRingEnd ℂ) (Complex.log w) :=
    Complex.log_conj w (by
      intro h
      exact harg h)
  have hre : Complex.log w + (starRingEnd ℂ) (Complex.log w) = ((2 * Real.log ‖w‖ : ℝ) : ℂ) := by
    rw [Complex.add_conj, Complex.log_re]
  rw [show -((k : ℂ) + s) = ((-k : ℤ) : ℂ) + (-s) by push_cast; ring,
    Complex.cpow_add _ _ hw0, Complex.cpow_intCast, mul_assoc]
  congr 1
  rw [Complex.cpow_def_of_ne_zero hw0, Complex.cpow_def_of_ne_zero hcw0, ← Complex.exp_add,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), hlog, ← Complex.ofReal_log (norm_nonneg _),
    ← add_mul, hre]
  congr 1
  push_cast
  ring

/-- Splitting a summable series over `ℤ` into residue classes mod `M`. -/
lemma tsum_int_residues [NeZero M] {h : ℤ → ℂ} (hh : Summable h) :
    ∑' n : ℤ, h n = ∑ a ∈ Finset.range M, ∑' l : ℤ, h (l * M + ((a : ℕ) : ℤ)) := by
  let e : Fin M × ℤ ≃ ℤ := (Equiv.prodComm (Fin M) ℤ).trans (Int.divModEquiv M).symm
  have he : ∀ p : Fin M × ℤ, e p = p.2 * M + ((p.1 : ℕ) : ℤ) := fun p ↦ by
    simp [e, Int.divModEquiv_symm_apply]
  rw [← e.tsum_eq]
  have hs : Summable (h ∘ e) := e.summable_iff.mpr hh
  change ∑' p : Fin M × ℤ, (h ∘ e) p = _
  rw [hs.tsum_prod, tsum_fintype]
  simp only [Function.comp_apply, he]
  exact Fin.sum_univ_eq_sum_range (fun a ↦ ∑' l : ℤ, h (l * M + (a : ℤ))) M

lemma mul_natCast_cpow (M : ℕ) (u r : ℂ) : ((M : ℂ) * u) ^ r = (M : ℂ) ^ r * u ^ r := by
  have h0 : (M : ℂ).arg = 0 := by
    rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg _)]
  exact Complex.mul_cpow (by rw [h0, zero_add]; exact Complex.arg_mem_Ioc u) r

lemma residue_term [NeZero M] (ψ : DirichletCharacter ℂ M) (w α β : ℂ) (a : ℕ) :
    ∑' l : ℤ, ψ (((l * M + (a : ℤ) : ℤ)) : ZMod M) *
        ((w + (((l * M + (a : ℤ) : ℤ)) : ℂ)) ^ (-α) *
          ((starRingEnd ℂ) w + (((l * M + (a : ℤ) : ℤ)) : ℂ)) ^ (-β)) =
      ψ (a : ZMod M) * (M : ℂ) ^ (-(α + β)) * heckeS ((w + a) / M) α β := by
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  unfold heckeS
  rw [mul_assoc, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun l ↦ ?_
  have hψ : (((l * M + (a : ℤ) : ℤ)) : ZMod M) = (a : ZMod M) := by push_cast; simp
  have h1 : w + (((l * M + (a : ℤ) : ℤ)) : ℂ) = (M : ℂ) * ((w + a) / M + l) := by
    push_cast; field_simp; ring
  have h2 : (starRingEnd ℂ) w + (((l * M + (a : ℤ) : ℤ)) : ℂ) =
      (M : ℂ) * ((starRingEnd ℂ) ((w + a) / M) + l) := by
    simp only [map_div₀, map_add, Complex.conj_natCast]
    push_cast; field_simp; ring
  rw [hψ, h1, h2, mul_natCast_cpow, mul_natCast_cpow, neg_add, Complex.cpow_add _ _ hM]
  ring

lemma summable_heckeSTerm_of_im_pos {u α β : ℂ} (hu : 0 < u.im) :
    Summable (heckeSTerm u α β) := by
  obtain ⟨v, hv, hb⟩ := heckeSTerm_uniform (T := {(u, α, β)}) isCompact_singleton
    (by intro p hp; rw [Set.mem_singleton_iff] at hp; subst hp; exact hu)
  exact hv.of_norm_bounded fun m ↦ hb (u, α, β) rfl m

lemma fourier_part [NeZero M] (ψ : DirichletCharacter ℂ M) {x y : ℝ} (hy : 0 < y) (C : ℕ) (hC : 0 < C)
    (α β : ℂ) (u : ℕ → ℂ) (hre : ∀ a, (u a).re = (C * x + a) / M) (him : ∀ a, (u a).im = C * y / M) :
    ∑ a ∈ Finset.range M, ψ (a : ZMod M) * ∑' m : ℤ, heckeSTerm (u a) α β m =
      ∑' m : ℤ, if m = 0 then 0 else cexp (2 * π * I * m * C * x / M) * charFourier ψ m *
        xiCont (C * y / M) α β m := by
  have hM : (0 : ℝ) < M := Nat.cast_pos.mpr (NeZero.pos M)
  have hsum : ∀ a, Summable (heckeSTerm (u a) α β) := fun a ↦
    summable_heckeSTerm_of_im_pos (by
      rw [him a]; have : (0 : ℝ) < C := Nat.cast_pos.mpr hC; positivity)
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun a _ ↦ (hsum a).mul_left _)]
  refine tsum_congr fun m ↦ ?_
  by_cases hm : m = 0
  · simp [hm, heckeSTerm]
  · simp only [hm, ↓reduceIte, heckeSTerm, hre, him, charFourier, Finset.sum_mul]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [show (2 * π * I * m * (((C * x + a) / M : ℝ) : ℂ)) =
      2 * π * I * m * C * x / M + 2 * π * I * a * m / M by push_cast; ring, Complex.exp_add]
    ring

/-- **Miyake, p. 284.** For $c \ge 1$ and $k + 2\operatorname{Re}s > 2$:
$R(c) = \chi(c)M^{-k-2s}\big(F(0)\xi(cy/M;k+s,s;0) + \sum_{m\ne0}e^{2\pi imcx/M}F(m)\xi(cy/M;k+s,s;m)\big)$,
by residue classes mod $M$ and Theorem 7.2.8. -/
theorem heckeRow_pos {k : ℤ} {s : ℂ} (hs : 2 < (k : ℝ) + 2 * s.re) [NeZero M]
    (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (z : ℍ) (c : ℕ+) :
    heckeRow k s χ ψ z ((c : ℕ) : ℤ) = χ ((c : ℕ) : ZMod L) * (M : ℂ) ^ (-(k : ℂ) - 2 * s) *
      (charFourier ψ 0 * xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s 0 +
        ∑' m : ℤ, if m = 0 then 0 else
          cexp (2 * π * I * m * (c : ℕ) * z.re / M) * charFourier ψ m *
            xiCont ((c : ℕ) * z.im / M) ((k : ℂ) + s) s m) := by
  have hC : 0 < (c : ℕ) := c.pos
  have hCr : (0 : ℝ) < ((c : ℕ) : ℝ) := Nat.cast_pos.mpr hC
  have hMr : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (NeZero.pos M)
  have hy : 0 < z.im := z.im_pos
  set w : ℂ := ((c : ℕ) : ℂ) * z with hw
  have hwim : 0 < w.im := by
    have : w.im = ((c : ℕ) : ℝ) * z.im := by simp [hw]
    rw [this]; positivity
  have hαβ : 1 < (((k : ℂ) + s) + s).re := by simp; linarith
  -- the row as a series of `(w+n)^{-α} (w̄+n)^{-s}`
  have hA : heckeRow k s χ ψ z ((c : ℕ) : ℤ) = χ ((c : ℕ) : ZMod L) *
      ∑' n : ℤ, ψ (n : ZMod M) *
        ((w + n) ^ (-((k : ℂ) + s)) * ((starRingEnd ℂ) w + n) ^ (-s)) := by
    unfold heckeRow
    rw [← tsum_mul_left]
    refine tsum_congr fun n ↦ ?_
    have hv : (![((c : ℕ) : ℤ), n] : Fin 2 → ℤ) ≠ 0 := by
      intro h
      have := congrFun h 0
      simp at this
    have hu : 0 < (w + n).im := by simpa using hwim
    have h1 := cpow_mul_norm_cpow hu k s
    simp only [heckeSummand, hv, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one,
      Int.cast_natCast]
    rw [show (((c : ℕ) : ℂ) * z + n) = w + n from rfl, h1, map_add, map_intCast (starRingEnd ℂ) n]
    ring
  have hB : Summable fun n : ℤ ↦ ψ (n : ZMod M) *
      ((w + n) ^ (-((k : ℂ) + s)) * ((starRingEnd ℂ) w + n) ^ (-s)) := by
    refine (summable_heckeS hwim hαβ).of_norm_bounded fun n ↦ ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)
  have hC' : ∑' n : ℤ, ψ (n : ZMod M) *
      ((w + n) ^ (-((k : ℂ) + s)) * ((starRingEnd ℂ) w + n) ^ (-s)) =
      ∑ a ∈ Finset.range M, ψ (a : ZMod M) * (M : ℂ) ^ (-(((k : ℂ) + s) + s)) *
        heckeS ((w + a) / M) ((k : ℂ) + s) s := by
    rw [tsum_int_residues (M := M) hB]
    exact Finset.sum_congr rfl fun a _ ↦ residue_term ψ w ((k : ℂ) + s) s a
  have him : ∀ a : ℕ, ((w + a) / M).im = ((c : ℕ) : ℝ) * z.im / M := by
    intro a
    simp [hw, Complex.div_natCast_im]
  have hre : ∀ a : ℕ, ((w + a) / M).re = (((c : ℕ) : ℝ) * z.re + a) / M := by
    intro a
    simp [hw, Complex.div_natCast_re]
  have hD : ∀ a : ℕ, heckeS ((w + a) / M) ((k : ℂ) + s) s =
      xiCont (((c : ℕ) : ℝ) * z.im / M) ((k : ℂ) + s) s 0 +
        ∑' m : ℤ, heckeSTerm ((w + a) / M) ((k : ℂ) + s) s m := by
    intro a
    rw [heckeS_eq_heckeSCont (by rw [him]; positivity) hαβ, heckeSCont, him]
  have hF := fourier_part ψ hy (c : ℕ) hC ((k : ℂ) + s) s (fun a ↦ (w + a) / M) hre him
  have hK : (M : ℂ) ^ (-(((k : ℂ) + s) + s)) = (M : ℂ) ^ (-(k : ℂ) - 2 * s) := by
    congr 1; ring
  have hF0 : ∑ a ∈ Finset.range M, ψ (a : ZMod M) = charFourier ψ 0 := by
    unfold charFourier; simp
  rw [hA, hC']
  simp only [hD]
  rw [hK]
  set X := xiCont (((c : ℕ) : ℝ) * z.im / M) ((k : ℂ) + s) s 0
  set K := (M : ℂ) ^ (-(k : ℂ) - 2 * s)
  have key : ∀ a ∈ Finset.range M, ψ (a : ZMod M) * K *
      (X + ∑' m : ℤ, heckeSTerm ((w + a) / M) ((k : ℂ) + s) s m) =
      K * (ψ (a : ZMod M) * X + ψ (a : ZMod M) *
        ∑' m : ℤ, heckeSTerm ((w + a) / M) ((k : ℂ) + s) s m) := fun a _ ↦ by ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, hF0, hF]
  ring

lemma charFourier_eq_zmod [NeZero M] (ψ : DirichletCharacter ℂ M) (j : ℤ) :
    charFourier ψ j = ∑ x : ZMod M, ψ x * ZMod.stdAddChar (x * (j : ZMod M)) := by
  unfold charFourier
  rw [← ModularFormsKB.Miyake.sum_range_eq_sum_zmod (fun x : ZMod M ↦
    ψ x * ZMod.stdAddChar (x * (j : ZMod M)))]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [show ((a : ZMod M) * (j : ZMod M)) = (((a : ℤ) * j : ℤ) : ZMod M) by push_cast; ring,
    ZMod.stdAddChar_coe]
  push_cast
  ring_nf

/-- $F(m) = W(\psi^0)\,b(m)$ for $m \ge 0$ (Miyake (7.1.10)). -/
theorem charFourier_natCast [NeZero M] (ψ : DirichletCharacter ℂ M) (m : ℕ) :
    haveI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
    charFourier ψ m = gaussSum ψ.primitiveCharacter ZMod.stdAddChar *
      gaussCoeff ψ.primitiveCharacter (M / ψ.conductor) m := by
  haveI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  rw [← dft_dirichletCharacter, ZMod.dft_apply, charFourier_eq_zmod]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

theorem charFourier_neg (ψ : DirichletCharacter ℂ M) (j : ℤ) :
    charFourier ψ (-j) = ψ (-1) * charFourier ψ j := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [charFourier]
  haveI : NeZero M := ⟨hM.ne'⟩
  rw [charFourier_eq_zmod, charFourier_eq_zmod, Finset.mul_sum, ← Equiv.sum_comp (Equiv.neg (ZMod M))]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only [Equiv.neg_apply, Int.cast_neg]
  have : -x * -(j : ZMod M) = x * j := by ring
  rw [this, show -x = (-1) * x by ring, map_mul]
  ring

open scoped Classical in
/-- $F(0) = \varphi(M) = M\prod_{p\mid M}(1-p^{-1})$ if $\psi$ is trivial, $0$ otherwise. -/
theorem charFourier_zero [NeZero M] (ψ : DirichletCharacter ℂ M) :
    charFourier ψ 0 = if ψ = 1 then (M : ℂ) * ∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹) else 0 := by
  rw [charFourier_eq_zmod]
  simp only [Int.cast_zero, mul_zero, AddChar.map_zero_eq_one, mul_one]
  split_ifs with h
  · subst h
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
    have := Nat.totient_eq_mul_prod_factors M
    have h2 : ((Nat.totient M : ℚ) : ℂ) = (M : ℂ) * ∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹) := by
      rw [this]; push_cast; rfl
    rw [← h2]; push_cast; rfl
  · exact MulChar.sum_eq_zero_of_ne_one h

end ModularFormsKB.Miyake.HeckeTrick
