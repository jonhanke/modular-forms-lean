import ModularFormsKB.Miyake.Wave4.Notation
import TauCeti.NumberTheory.ModularForms.Newforms.CoprimeFilter.Basic

/-!
# Miyake, Lemma 4.6.5: keeping the Fourier coefficients of index prime to `L`

Miyake, *Modular Forms* (Springer 1989), §4.6, p. 157.

For `f(z) = Σ aₙ e^{2πinz} ∈ 𝒢_k(N, χ)` and a positive integer `L`, the series
`g(z) = Σ_{(n, L) = 1} aₙ e^{2πinz}` lies in `𝒢_k(M, χ)` with

  `M = N ∏_{p ∣ L, p ∣ N} p ∏_{p ∣ L, p ∤ N} p²`

(`filterLevel N L`), and `g` is a cusp form if `f` is.

Tau Ceti proves the cusp-form case when every prime of `L` divides `N`, at level
`∏_{p ∣ L} p · N` (`TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime`). For a
general `L`, read `f` first at level `N' = N ∏_{p ∣ L, p ∤ N} p` (every prime of `L` divides `N'`);
the filter then lands at `∏_{p ∣ L} p · N' = M`, Miyake's level. The character at level `M` is
`χ` read modulo `M` (`DirichletCharacter.changeLevel`).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave5

open ModularFormsKB.Miyake.Wave4

/-- Miyake's level `M = N ∏_{p ∣ L, p ∣ N} p ∏_{p ∣ L, p ∤ N} p²` of Lemma 4.6.5. -/
def filterLevel (N L : ℕ) : ℕ :=
  N * ∏ p ∈ L.primeFactors, if p ∣ N then p else p ^ 2

lemma dvd_filterLevel (N L : ℕ) : N ∣ filterLevel N L := Dvd.intro _ rfl

instance (N L : ℕ) [NeZero N] : NeZero (filterLevel N L) := by
  refine ⟨Nat.mul_ne_zero (NeZero.ne N) (Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_)⟩
  have := (Nat.prime_of_mem_primeFactors hp).ne_zero
  split_ifs <;> simp [this]

/-- `M = ∏ p · N'` with `N' = N ∏_{p ∣ L, p ∤ N} p`. -/
private lemma filterLevel_eq (N L : ℕ) :
    filterLevel N L = L.primeFactors.prod id *
      (N * ∏ p ∈ L.primeFactors, if p ∣ N then 1 else p) := by
  have h : ∏ p ∈ L.primeFactors, (if p ∣ N then p else p ^ 2) =
      L.primeFactors.prod id * ∏ p ∈ L.primeFactors, (if p ∣ N then 1 else p) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ ↦ ?_
    simp only [id]
    split_ifs <;> ring
  rw [filterLevel, h]
  ring

/-- Coprimality only sees the primes. -/
private theorem coprime_prod_primeFactors_iff' {n L : ℕ} (hL : L ≠ 0) :
    Nat.Coprime n (L.primeFactors.prod id) ↔ Nat.Coprime n L :=
  ⟨fun h ↦ (h.pow_right L).coprime_dvd_right (Nat.dvd_prod_primeFactors_pow_self hL),
    fun h ↦ h.coprime_dvd_right (Nat.prod_primeFactors_dvd L)⟩

private theorem ite_coprime_ite_dvd_eq_ite_coprime_mul' {α : Type*} [Zero α] {q : ℕ}
    (hq : q.Prime) (n m : ℕ) (a : α) :
    (if Nat.Coprime n m then (if q ∣ n then 0 else a) else 0) =
      if Nat.Coprime n (q * m) then a else 0 := by
  simp only [Nat.coprime_mul_iff_right, Nat.coprime_comm, hq.coprime_iff_not_dvd, ite_and]
  split_ifs <;> rfl

section ModPort

open TauCeti HeckeRing.GL2

/-- Modular-form analogue of Tau Ceti's single-prime filter `f - V_p (T_p f)`. -/
private theorem qExpansion_coeff_restrict_sub_levelRaise_heckeTNat {N : ℕ} [NeZero N] {k : ℤ}
    {p : ℕ} [NeZero p] (hpN : p.primeFactors ⊆ N.primeFactors)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion 1 (_root_.ModularForm.restrict
          (Gamma1_map_le_Gamma1_map_of_dvd (Nat.dvd_mul_left N p)) f -
        TauCeti.ModularForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL N p)
          (heckeTNat (N := N) k p f))).coeff n =
      if p ∣ n then 0 else (qExpansion 1 f).coeff n := by
  rw [_root_.ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _), map_sub,
    TauCeti.ModularForm.qExpansion_levelRaise_coeff_Gamma1 N _ n,
    qExpansion_coeff_heckeTNat_of_primeFactors_subset k p hpN f (n / p),
    ModularForm.coe_restrict]
  by_cases hpn : p ∣ n <;> simp [hpn, Nat.mul_div_cancel']

private theorem exists_modFormCharSpace_coeff_eq_ite_dvd {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) {p : ℕ}
    [NeZero p] (hpN : p.primeFactors ⊆ N.primeFactors) :
    ∃ g : ModularForm ((Gamma1 (p * N)).map (mapGL ℝ)) k,
      g ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N p))) ∧
      ∀ n, (qExpansion 1 g).coeff n = if p ∣ n then 0 else (qExpansion 1 f).coeff n :=
  ⟨_root_.ModularForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd (Nat.dvd_mul_left N p)) f -
      TauCeti.ModularForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL N p)
        (heckeTNat (N := N) k p f),
    Submodule.sub_mem _ (TauCeti.ModularForm.restrict_mem_modFormCharSpace χ _ hf)
      (TauCeti.ModularForm.levelRaise_mem_modFormCharSpace N p χ
        (heckeTNat_mem_modFormCharSpace_of_primeFactors_subset k χ p hpN hf)),
    qExpansion_coeff_restrict_sub_levelRaise_heckeTNat hpN f⟩

private theorem exists_modFormCharSpace_coeff_eq_ite_coprime_prod (m : ℕ) :
    ∀ {M : ℕ} [NeZero M] {k : ℤ} (χ : (ZMod M)ˣ →* ℂˣ)
      {g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k}, g ∈ modFormCharSpace k χ →
      ∀ S : Finset ℕ, S ⊆ M.primeFactors → S.card = m → ∃ (M' : ℕ) (hMM' : M ∣ M'),
        M' = S.prod id * M ∧ ∃ g' : ModularForm ((Gamma1 M').map (mapGL ℝ)) k,
          g' ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap hMM')) ∧
          ∀ n, (qExpansion 1 g').coeff n =
            if Nat.Coprime n (S.prod id) then (qExpansion 1 g).coeff n else 0 := by
  induction m with
  | zero =>
    intro M _ k χ g hg S _ hScard
    obtain rfl := Finset.card_eq_zero.mp hScard
    exact ⟨M, dvd_rfl, by simp, g, by simpa [ZMod.unitsMap_self] using hg,
      fun _ ↦ by simp [Nat.Coprime]⟩
  | succ m ih =>
    intro M _ k χ g hg S hS hScard
    obtain ⟨q, hqS⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    have hqM : q ∈ M.primeFactors := hS hqS
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hqM
    have : NeZero q := ⟨hq.ne_zero⟩
    have hMqM : M ∣ q * M := Nat.dvd_mul_left M q
    obtain ⟨g₁, hg₁, hg₁q⟩ :=
      exists_modFormCharSpace_coeff_eq_ite_dvd χ hg
        (Nat.primeFactors_mono (Nat.dvd_of_mem_primeFactors hqM) (NeZero.ne M))
    have hprod : S.prod id = q * (S.erase q).prod id := (Finset.mul_prod_erase _ _ hqS).symm
    obtain ⟨M', hM'dvd, hM'eq, g', hg', hg'q⟩ :=
      ih _ hg₁ (S.erase q)
        (fun _ hr ↦ Nat.primeFactors_mono hMqM (NeZero.ne _) (hS (Finset.mem_of_mem_erase hr)))
        (by rw [Finset.card_erase_of_mem hqS, hScard]; omega)
    refine ⟨M', hMqM.trans hM'dvd, by rw [hM'eq, hprod]; ring, g', ?_, fun n ↦ ?_⟩
    · simpa only [MonoidHom.comp_assoc, ZMod.unitsMap_comp] using hg'
    · rw [hg'q n, hg₁q n, hprod]
      exact ite_coprime_ite_dvd_eq_ite_coprime_mul' hq n _ _

private theorem exists_modFormCharSpace_coeff_eq_ite_coprime {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) {L : ℕ}
    [NeZero L] (hLN : L.primeFactors ⊆ N.primeFactors) :
    ∃ g : ModularForm ((Gamma1 (L.primeFactors.prod id * N)).map (mapGL ℝ)) k,
      g ∈ modFormCharSpace k
        (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N (L.primeFactors.prod id)))) ∧
      ∀ n, (qExpansion 1 g).coeff n = if Nat.Coprime n L then (qExpansion 1 f).coeff n else 0 := by
  obtain ⟨M', hM'dvd, hM'eq, g, hg, hgq⟩ :=
    exists_modFormCharSpace_coeff_eq_ite_coprime_prod L.primeFactors.card χ hf
      L.primeFactors hLN rfl
  subst hM'eq
  exact ⟨g, hg, fun n ↦ by simp only [hgq n, coprime_prod_primeFactors_iff' (NeZero.ne L)]⟩

end ModPort

/-- The intermediate level `N' = N ∏_{p ∣ L, p ∤ N} p`: every prime of `L` divides it. -/
private lemma exists_level (N L : ℕ) [NeZero N] :
    NeZero (N * ∏ p ∈ L.primeFactors, if p ∣ N then 1 else p) ∧
    L.primeFactors ⊆ (N * ∏ p ∈ L.primeFactors, if p ∣ N then 1 else p).primeFactors := by
  have hne : N * ∏ p ∈ L.primeFactors, (if p ∣ N then 1 else p) ≠ 0 := by
    refine Nat.mul_ne_zero (NeZero.ne N) (Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_)
    have := (Nat.prime_of_mem_primeFactors hp).ne_zero
    split_ifs <;> simp [this]
  refine ⟨⟨hne⟩, fun p hp ↦ ?_⟩
  rw [Nat.mem_primeFactors]
  refine ⟨Nat.prime_of_mem_primeFactors hp, ?_, hne⟩
  by_cases h : p ∣ N
  · exact Dvd.dvd.mul_right h _
  · refine Dvd.dvd.mul_left ?_ _
    have := Finset.dvd_prod_of_mem (fun p ↦ if p ∣ N then 1 else p) hp
    simpa [h] using this

variable {N : ℕ} [NeZero N]

/-- **Miyake, Lemma 4.6.5** (cusp forms): for `f ∈ 𝒮_k(N, χ)` and `L ≥ 1`, the series of the
coefficients of `f` of index prime to `L` is an element of `𝒮_k(M, χ)`, `M = filterLevel N L`. -/
@[kb "miyake1989" "Lemma 4.6.5, p. 157 (cusp forms)"]
theorem exists_cuspSpace_coeff_eq_ite_coprime {k : ℤ} {χ : DirichletCharacter ℂ N}
    (f : cuspSpace k χ) {L : ℕ} (hL : 0 < L) :
    ∃ g : cuspSpace (N := filterLevel N L) k (DirichletCharacter.changeLevel
        (dvd_filterLevel N L) χ),
      ∀ n, coeff g n = if n.Coprime L then coeff f n else 0 := by
  have : NeZero L := ⟨hL.ne'⟩
  obtain ⟨hN', hLN⟩ := exists_level N L
  have hNN' : N ∣ N * ∏ p ∈ L.primeFactors, if p ∣ N then 1 else p := dvd_mul_right _ _
  have key : ∀ (M : ℕ) [NeZero M] (hNM : N ∣ M),
      M = L.primeFactors.prod id * (N * ∏ p ∈ L.primeFactors, if p ∣ N then 1 else p) →
      ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
        g ∈ TauCeti.cuspFormCharSpace k (χ.toUnitHom.comp (ZMod.unitsMap hNM)) ∧
        ∀ n, (qExpansion 1 g).coeff n =
          if n.Coprime L then (qExpansion 1 (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n
          else 0 := by
    intro M _ hNM hM
    subst hM
    obtain ⟨g, hg, hgq⟩ := TauCeti.exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime
      (χ.toUnitHom.comp (ZMod.unitsMap hNN'))
      (TauCeti.CuspForm.restrict_mem_cuspFormCharSpace χ.toUnitHom hNN' f.2) hLN
    refine ⟨g, ?_, fun n ↦ ?_⟩
    · rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp] at hg
      exact hg
    · rw [hgq n, CuspForm.coe_restrict]
  obtain ⟨g, hg, hgq⟩ := key (filterLevel N L) (dvd_filterLevel N L) (filterLevel_eq N L)
  refine ⟨⟨g, ?_⟩, fun n ↦ ?_⟩
  · show g ∈ TauCeti.cuspFormCharSpace k _
    rw [DirichletCharacter.changeLevel_toUnitHom]
    exact hg
  · exact hgq n

/-- **Miyake, Lemma 4.6.5** (modular forms): for `f ∈ 𝒢_k(N, χ)` and `L ≥ 1`, the series of the
coefficients of `f` of index prime to `L` is an element of `𝒢_k(M, χ)`, `M = filterLevel N L`. -/
@[kb "miyake1989" "Lemma 4.6.5, p. 157"]
theorem exists_modSpace_coeff_eq_ite_coprime {k : ℤ} {χ : DirichletCharacter ℂ N}
    (f : modSpace k χ) {L : ℕ} (hL : 0 < L) :
    ∃ g : modSpace (N := filterLevel N L) k (DirichletCharacter.changeLevel
        (dvd_filterLevel N L) χ),
      ∀ n, coeffMod g n = if n.Coprime L then coeffMod f n else 0 := by
  have : NeZero L := ⟨hL.ne'⟩
  obtain ⟨hN', hLN⟩ := exists_level N L
  have hNN' : N ∣ N * ∏ p ∈ L.primeFactors, if p ∣ N then 1 else p := dvd_mul_right _ _
  have key : ∀ (M : ℕ) [NeZero M] (hNM : N ∣ M),
      M = L.primeFactors.prod id * (N * ∏ p ∈ L.primeFactors, if p ∣ N then 1 else p) →
      ∃ g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k,
        g ∈ TauCeti.modFormCharSpace k (χ.toUnitHom.comp (ZMod.unitsMap hNM)) ∧
        ∀ n, (qExpansion 1 g).coeff n =
          if n.Coprime L then (qExpansion 1 (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n
          else 0 := by
    intro M _ hNM hM
    subst hM
    obtain ⟨g, hg, hgq⟩ := exists_modFormCharSpace_coeff_eq_ite_coprime
      (χ.toUnitHom.comp (ZMod.unitsMap hNN'))
      (TauCeti.ModularForm.restrict_mem_modFormCharSpace χ.toUnitHom hNN' f.2) hLN
    refine ⟨g, ?_, fun n ↦ ?_⟩
    · rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp] at hg
      exact hg
    · rw [hgq n, ModularForm.coe_restrict]
  obtain ⟨g, hg, hgq⟩ := key (filterLevel N L) (dvd_filterLevel N L) (filterLevel_eq N L)
  refine ⟨⟨g, ?_⟩, fun n ↦ ?_⟩
  · show g ∈ TauCeti.modFormCharSpace k _
    rw [DirichletCharacter.changeLevel_toUnitHom]
    exact hg
  · exact hgq n

end ModularFormsKB.Miyake.Wave5
