import ModularFormsKB.Miyake.Wave4.Notation
import TauCeti.NumberTheory.ModularForms.Newforms.SquarefreeDecomposition

/-!
# Miyake, Lemma 4.6.7: a form whose coefficients vanish off the multiples of the primes of `l`

Miyake, *Modular Forms* (Springer 1989), §4.6, p. 159.

Let `l > 1` be squarefree and `f = Σ aₙ e^{2πinz} ∈ 𝒢_k(N, χ)` with `aₙ = 0` for every `n` prime
to `l`. Then `f(z) = Σ_{p ∣ l} g_p(pz)` with `g_p ∈ 𝒢_k(N l², χ)`; if `l ∣ N` the `g_p` can be
taken in `𝒢_k(N l, χ)`, and if `f` is a cusp form, so are the `g_p`.

Here the identity `f(z) = Σ_{p ∣ l} g_p(pz)` is written coefficient by coefficient,
`aₙ(f) = Σ_{p ∣ l, p ∣ n} a_{n/p}(g_p)`, which is equivalent to it (both sides are `q`-series
converging on the upper half-plane). This file treats cusp forms, from Tau Ceti's
`TauCeti.exists_qExpansion_coeff_eq_sum_primeFactors_of_squarefree` (pieces at the smaller
levels `N l² / p`, read here at Miyake's level `N l²`, character `χ` read modulo `N l²`).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave5

open ModularFormsKB.Miyake.Wave4

variable {N : ℕ} [NeZero N]

instance (N l : ℕ) [NeZero N] [NeZero l] : NeZero (N * l ^ 2) :=
  ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 (NeZero.ne l))⟩

instance (N l : ℕ) [NeZero N] [NeZero l] : NeZero (N * l) :=
  ⟨Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne l)⟩

/-- **Miyake, Lemma 4.6.7** (cusp forms): for squarefree `l > 1` and `f ∈ 𝒮_k(N, χ)` with
`aₙ(f) = 0` for all `n` prime to `l`, there are `g_p ∈ 𝒮_k(N l², χ)` (`p ∣ l` prime) with
`f(z) = Σ_{p ∣ l} g_p(pz)`, i.e. `aₙ(f) = Σ_{p ∣ l, p ∣ n} a_{n/p}(g_p)`. -/
@[kb "miyake1989" "Lemma 4.6.7, p. 159 (cusp forms)"]
theorem exists_coeff_eq_sum_of_squarefree {k : ℤ} {χ : DirichletCharacter ℂ N}
    (f : cuspSpace k χ) {l : ℕ} [NeZero l] (hl : 1 < l) (hsq : Squarefree l)
    (hvan : ∀ n, n.Coprime l → coeff f n = 0) :
    ∃ g : ℕ → cuspSpace (N := N * l ^ 2) k
        (DirichletCharacter.changeLevel (Nat.dvd_mul_right N (l ^ 2)) χ),
      ∀ n, coeff f n = ∑ p ∈ l.primeFactors, if p ∣ n then coeff (g p) (n / p) else 0 := by
  have hl0 : l ≠ 0 := NeZero.ne l
  obtain ⟨F, χ', hF, hχ', hcoeff⟩ :=
    TauCeti.exists_qExpansion_coeff_eq_sum_primeFactors_of_squarefree χ.toUnitHom f.2 hsq hvan
  have hqd : ∀ q ∈ l.primeFactors, q ∣ N * l ^ 2 := fun q hq ↦
    dvd_mul_of_dvd_right ((Nat.dvd_of_mem_primeFactors hq).trans (dvd_pow_self l two_ne_zero)) N
  have hne : ∀ q ∈ l.primeFactors, NeZero (N * l ^ 2 / q) := fun q hq ↦
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _)) (hqd q hq))
      (Nat.prime_of_mem_primeFactors hq).pos).ne'⟩
  classical
  let G : ∀ q ∈ l.primeFactors, cuspSpace (N := N * l ^ 2) k
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right N (l ^ 2)) χ) := fun q hq ↦
    haveI := hne q hq
    ⟨_root_.CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd (Nat.div_dvd_of_dvd (hqd q hq)))
        (F q hq), by
      show _ ∈ TauCeti.cuspFormCharSpace k _
      rw [DirichletCharacter.changeLevel_toUnitHom, ← hχ' q hq]
      exact TauCeti.CuspForm.restrict_mem_cuspFormCharSpace _ _ (hF q hq)⟩
  refine ⟨fun p ↦ if h : p ∈ l.primeFactors then G p h else 0, fun n ↦ ?_⟩
  rw [show coeff f n = _ from hcoeff n, ← Finset.sum_attach l.primeFactors]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have := hne q.1 q.2
  simp only [q.2, dite_true]
  split_ifs
  · show _ = (qExpansion 1 (_root_.CuspForm.restrict
      (Gamma1_map_le_Gamma1_map_of_dvd (Nat.div_dvd_of_dvd (hqd q.1 q.2))) (F q.1 q.2))).coeff _
    rw [CuspForm.coe_restrict]
  · rfl

open TauCeti in
/-- The induction behind the case `l ∣ N`: peel a prime `q` off `f` (complementary filter at level
`q M`, then `V_q`-descent at the same level), recurse on the rest at level `q M`. All pieces land
at level `M l`. -/
private theorem exists_pieces_of_squarefree_primeFactors_subset {k : ℤ} (m : ℕ) :
    ∀ (l : ℕ), l.primeFactors.card = m → ∀ (M : ℕ) [NeZero M] (χ : (ZMod M)ˣ →* ℂˣ)
      (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k), f ∈ cuspFormCharSpace k χ → Squarefree l →
      l.primeFactors ⊆ M.primeFactors →
      (∀ n, Nat.Coprime n l → (qExpansion 1 f).coeff n = 0) →
      ∃ G : ℕ → CuspForm ((Gamma1 (M * l)).map (mapGL ℝ)) k,
        (∀ p, G p ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M l)))) ∧
        ∀ n, (qExpansion 1 f).coeff n =
          ∑ p ∈ l.primeFactors, if p ∣ n then (qExpansion 1 (G p)).coeff (n / p) else 0 := by
  classical
  induction m with
  | zero =>
    intro l hcard M _ χ f hf hsq _ hvan
    rcases Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp hcard) with rfl | rfl
    · exact absurd rfl hsq.ne_zero
    · exact ⟨fun _ ↦ 0, fun _ ↦ Submodule.zero_mem _, fun n ↦ by
        rw [Nat.primeFactors_one, Finset.sum_empty]
        exact hvan n (Nat.coprime_one_right n)⟩
  | succ m ih =>
    intro l hcard M _ χ f hf hsq hlM hvan
    obtain ⟨q, hq⟩ : l.primeFactors.Nonempty := Finset.card_pos.mp (hcard ▸ Nat.succ_pos m)
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    obtain ⟨l', rfl⟩ : ∃ l', l = q * l' := Nat.dvd_of_mem_primeFactors hq
    have hl'0 : l' ≠ 0 := right_ne_zero_of_mul hsq.ne_zero
    have hql' : q ∉ l'.primeFactors := fun h ↦
      (Nat.squarefree_iff_prime_squarefree.mp hsq q hqp)
        (Nat.mul_dvd_mul_left q (Nat.dvd_of_mem_primeFactors h))
    have hpf : (q * l').primeFactors = insert q l'.primeFactors := by
      rw [Nat.primeFactors_mul hqp.ne_zero hl'0, hqp.primeFactors, Finset.singleton_union]
    have hcard' : l'.primeFactors.card = m := by
      rw [hpf, Finset.card_insert_of_notMem hql'] at hcard
      omega
    have hsq' : Squarefree l' := hsq.squarefree_of_dvd (dvd_mul_left l' q)
    have : NeZero q := ⟨hqp.ne_zero⟩
    have hqM : q ∈ M.primeFactors := hlM hq
    have hMne : q * M ≠ 0 := Nat.mul_ne_zero hqp.ne_zero (NeZero.ne M)
    have : NeZero (q * M) := ⟨hMne⟩
    have hNM : M ∣ q * M := Nat.dvd_mul_left M q
    -- the complementary filter at `q`, at level `q M`
    have hprod : q.primeFactors.prod id = q := by simp [hqp.primeFactors]
    have key : ∃ h : CuspForm ((Gamma1 (q * M)).map (mapGL ℝ)) k,
        h ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
        ∀ n, (qExpansion 1 h).coeff n =
          if Nat.Coprime n q then 0 else (qExpansion 1 f).coeff n := by
      have := exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_coprime_zero χ hf
        (L := q) (Nat.primeFactors_mono (Nat.dvd_of_mem_primeFactors hqM) (NeZero.ne M))
      rwa [hprod] at this
    obtain ⟨h, hhχ, hhc⟩ := key
    have hsupp : QExpansionSupportedOnDvd q h := by
      rw [qExpansionSupportedOnDvd_iff, PowerSeries.isSupportedOnDvd_iff]
      intro n hn
      rw [hhc n, if_pos (Nat.Coprime.symm (hqp.coprime_iff_not_dvd.mpr hn))]
    obtain ⟨F, hFχ, hFc⟩ :=
      exists_mem_cuspFormCharSpace_qExpansion_coeff_eq_ite_dvd hhχ hsupp
    -- the rest
    set f' : CuspForm ((Gamma1 (q * M)).map (mapGL ℝ)) k :=
      _root_.CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd hNM) f - h with hf'
    have hf'c (n : ℕ) : (qExpansion 1 f').coeff n =
        if Nat.Coprime n q then (qExpansion 1 f).coeff n else 0 := by
      rw [hf', FunLike.coe_sub,
        _root_.ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map _), map_sub,
        CuspForm.coe_restrict, hhc n]
      split_ifs <;> simp
    have hf'χ : f' ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) :=
      Submodule.sub_mem _ (CuspForm.restrict_mem_cuspFormCharSpace χ hNM hf) hhχ
    have hf'van (n : ℕ) (hn : Nat.Coprime n l') : (qExpansion 1 f').coeff n = 0 := by
      rw [hf'c n]
      split_ifs with hnq
      · exact hvan n (Nat.Coprime.mul_right hnq hn)
      · rfl
    have hl'sub : l'.primeFactors ⊆ (q * M).primeFactors := fun r hr ↦
      Nat.primeFactors_mono hNM hMne (hlM (by rw [hpf]; exact Finset.mem_insert_of_mem hr))
    obtain ⟨G', hG'χ, hG'c⟩ := ih l' hcard' (q * M) _ f' hf'χ hsq' hl'sub hf'van
    -- read everything at level `M * (q * l')`
    have hd1 : q * M ∣ M * (q * l') := ⟨l', by ring⟩
    have hd2 : q * M * l' ∣ M * (q * l') := dvd_of_eq (by ring)
    refine ⟨fun p ↦ if p = q then
        _root_.CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd hd1) F
      else _root_.CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd hd2) (G' p), fun p ↦ ?_,
      fun n ↦ ?_⟩
    · by_cases hp : p = q
      · simp only [hp, if_true]
        have := CuspForm.restrict_mem_cuspFormCharSpace _ hd1 hFχ
        rwa [MonoidHom.comp_assoc, ZMod.unitsMap_comp] at this
      · simp only [hp, if_false]
        have := CuspForm.restrict_mem_cuspFormCharSpace _ hd2 (hG'χ p)
        rwa [MonoidHom.comp_assoc, ZMod.unitsMap_comp, MonoidHom.comp_assoc,
          ZMod.unitsMap_comp] at this
    · have hsplit : (qExpansion 1 f).coeff n =
          (qExpansion 1 h).coeff n + (qExpansion 1 f').coeff n := by
        rw [hhc n, hf'c n]
        split_ifs <;> simp
      rw [hsplit, hFc n, hG'c n, hpf, Finset.sum_insert hql']
      congr 1
      · simp only [if_true, CuspForm.coe_restrict]
      · refine Finset.sum_congr rfl fun p hp ↦ ?_
        have hne : p ≠ q := fun h ↦ hql' (h ▸ hp)
        simp only [hne, if_false, CuspForm.coe_restrict]

/-- **Miyake, Lemma 4.6.7**, the case `l ∣ N` (cusp forms): the `g_p` can be taken in
`𝒮_k(N l, χ)`. -/
@[kb "miyake1989" "Lemma 4.6.7, p. 159 (l dividing N, cusp forms)"]
theorem exists_coeff_eq_sum_of_squarefree_of_dvd {k : ℤ} {χ : DirichletCharacter ℂ N}
    (f : cuspSpace k χ) {l : ℕ} [NeZero l] (hl : 1 < l) (hsq : Squarefree l) (hlN : l ∣ N)
    (hvan : ∀ n, n.Coprime l → coeff f n = 0) :
    ∃ g : ℕ → cuspSpace (N := N * l) k
        (DirichletCharacter.changeLevel (Nat.dvd_mul_right N l) χ),
      ∀ n, coeff f n = ∑ p ∈ l.primeFactors, if p ∣ n then coeff (g p) (n / p) else 0 := by
  obtain ⟨G, hG, hGc⟩ := exists_pieces_of_squarefree_primeFactors_subset _ l rfl N χ.toUnitHom
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) f.2 hsq
    (Nat.primeFactors_mono hlN (NeZero.ne N)) hvan
  refine ⟨fun p ↦ ⟨G p, ?_⟩, hGc⟩
  show G p ∈ TauCeti.cuspFormCharSpace k _
  rw [DirichletCharacter.changeLevel_toUnitHom]
  exact hG p

end ModularFormsKB.Miyake.Wave5
