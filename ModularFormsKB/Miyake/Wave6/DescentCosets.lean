import ModularFormsKB.Miyake.Wave6.LevelLowering
import Mathlib.GroupTheory.DoubleCoset

/-!
# Miyake, Lemma 4.5.11: the right cosets of `Γ₀(pN) [1 0; 0 p] Γ₀(N)`

Miyake, *Modular Forms* (Springer 1989), Lemma 4.5.11, p. 143. For a positive integer `N` and a
prime `p`,
`Γ₀(pN) [1 0; 0 p] Γ₀(N) = ⨆_{0 ≤ v < p} Γ₀(pN) [1 0; 0 p] γ_v` if `p ∣ N`, and
`= ⨆_{0 ≤ v ≤ p} Γ₀(pN) [1 0; 0 p] γ_v` if `p ∤ N`, where `γ_v ∈ Γ₀(N)` (`0 ≤ v < p`) is
congruent to `[1 v; 0 1]` modulo `p` and `γ_p ∈ Γ₀(N)` (`p ∤ N`) is congruent to `[0 -a; a⁻¹ 0]`
modulo `p` (`a` prime to `p`) and to `1` modulo `N`.

The double coset is taken in `GL₂(ℚ)` (Mathlib's `DoubleCoset.doubleCoset`), with `Γ₀(M)`
embedded by `mapGL ℚ`. Miyake's congruence of `γ_p` to `1` modulo `N` is not needed for the
decomposition and is not assumed in `doubleCoset_eq_iUnion`; the family `miyakeGamma` built
from Tau Ceti's `TauCeti.descendExtraGamma` satisfies it (`miyakeGamma_spec`).

## Results
* `mem_Gamma0_conj_iff` (Miyake (4.5.28)): `γ ∈ Γ₀(N)` lies in
  `[1 0; 0 p]⁻¹ Γ₀(pN) [1 0; 0 p]` exactly when `p` divides its upper right entry.
* `doubleCoset_eq_iUnion`, `pairwiseDisjoint_cosets`: Lemma 4.5.11.
* `descendMatrixRat_eq`, `doubleCoset_eq_iUnion_descendMatrixRat`,
  `pairwiseDisjoint_descendMatrixRat`: Tau Ceti's descent family `TauCeti.descendMatrixRat p (pN)`
  (over which `lowerSlash` of `Wave6/LevelLowering.lean` sums) is a complete set of
  representatives of the right cosets of `Γ₀(pN)` in the double coset, as Miyake's (4.6.7) uses.
-/

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise

noncomputable section

namespace ModularFormsKB.Miyake.Wave6

/-- `Γ₀(M)` as a subgroup of `GL₂(ℚ)`. -/
abbrev gamma0GL (M : ℕ) : Subgroup (GL (Fin 2) ℚ) := (Gamma0 M).map (mapGL ℚ)

/-- Miyake's `[1 0; 0 p]` in `GL₂(ℚ)` (Tau Ceti's `upperTriRep p 0`). -/
abbrev deltaP (p : ℕ) [NeZero p] : GL (Fin 2) ℚ := HeckeRing.GL2.upperTriRep p ⟨0, NeZero.pos p⟩

/-- Miyake's index set for the right cosets: `0 ≤ v < p` if `p ∣ N`, `0 ≤ v ≤ p` otherwise. -/
def cosetIndex (p N : ℕ) : Finset ℕ := Finset.range (if p ∣ N then p else p + 1)

/-- Miyake's conditions on the representatives `γ_v`, `0 ≤ v < p`: `γ_v ∈ Γ₀(N)` and
`γ_v ≡ [1 v; 0 1] mod p`. -/
def IsMiyakeGammaLt (p N : ℕ) (g : SL(2, ℤ)) (v : ℕ) : Prop :=
  g ∈ Gamma0 N ∧ ((g 0 0 : ℤ) : ZMod p) = 1 ∧ ((g 0 1 : ℤ) : ZMod p) = v ∧
    ((g 1 0 : ℤ) : ZMod p) = 0 ∧ ((g 1 1 : ℤ) : ZMod p) = 1

/-- Miyake's conditions on `γ_p` (`p ∤ N`) used by the decomposition: `γ_p ∈ Γ₀(N)` and
`γ_p ≡ [0 -a; a⁻¹ 0] mod p` for an integer `a` prime to `p` (`a'` is an inverse of `a` modulo
`p`). Miyake also asks `γ_p ≡ 1 mod N`; see `miyakeGamma_spec`. -/
def IsMiyakeGammaP (p N : ℕ) (g : SL(2, ℤ)) : Prop :=
  g ∈ Gamma0 N ∧ ∃ a a' : ℤ, ((a * a' : ℤ) : ZMod p) = 1 ∧ ((g 0 0 : ℤ) : ZMod p) = 0 ∧
    ((g 0 1 : ℤ) : ZMod p) = -a ∧ ((g 1 0 : ℤ) : ZMod p) = a' ∧ ((g 1 1 : ℤ) : ZMod p) = 0

/-- `g δ = δ γ` entrywise, for `g γ ∈ SL₂(ℤ)` and `δ = [1 0; 0 p]`. -/
private lemma conj_key {p : ℕ} [NeZero p] (g γ : SL(2, ℤ)) :
    mapGL ℚ g * deltaP p = deltaP p * mapGL ℚ γ ↔
      (g 0 0 = γ 0 0) ∧ ((p : ℤ) * g 0 1 = γ 0 1) ∧ (g 1 0 = (p : ℤ) * γ 1 0) ∧
        g 1 1 = γ 1 1 := by
  refine (Units.ext_iff.trans Matrix.ext_iff.symm).trans ?_
  simp [Matrix.mul_apply, Fin.sum_univ_two, HeckeRing.GL2.coe_upperTriRep, mapGL_coe_matrix,
    Fin.forall_fin_two]
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)
  rw [and_assoc]
  refine and_congr Iff.rfl (and_congr ?_ (and_congr ?_ ?_))
  · rw [mul_comm]; norm_cast
  · norm_cast
  · rw [mul_comm, mul_right_inj' hp0]; norm_cast

/-- **Miyake (4.5.28)**: for `γ ∈ Γ₀(N)`, `[1 0; 0 p] γ [1 0; 0 p]⁻¹ ∈ Γ₀(pN)` if and only if
`p` divides the upper right entry of `γ`. -/
@[kb "miyake1989" "(4.5.28), p. 144"]
theorem mem_Gamma0_conj_iff {p N : ℕ} [NeZero p] [NeZero N] {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) :
    deltaP p * mapGL ℚ γ * (deltaP p)⁻¹ ∈ gamma0GL (p * N) ↔ (p : ℤ) ∣ γ 0 1 := by
  constructor
  · intro h
    obtain ⟨g, -, hgx⟩ := Subgroup.mem_map.1 h
    have h1 : mapGL ℚ g * deltaP p = deltaP p * mapGL ℚ γ := by
      rw [hgx]; exact inv_mul_cancel_right _ _
    exact ⟨g 0 1, ((conj_key g γ).1 h1).2.1.symm⟩
  · rintro ⟨b', hb⟩
    have hdet := γ.det_coe
    rw [Matrix.det_fin_two] at hdet
    let g : SL(2, ℤ) := ⟨!![γ 0 0, b'; (p : ℤ) * γ 1 0, γ 1 1], by
      rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      rw [hb] at hdet
      linear_combination hdet⟩
    have hg0 : g ∈ Gamma0 (p * N) := by
      rw [Gamma0_mem] at hγ ⊢
      have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hγ
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 ?_
      show ((p * N : ℕ) : ℤ) ∣ (p : ℤ) * γ 1 0
      push_cast
      exact mul_dvd_mul_left _ h1
    refine Subgroup.mem_map.2 ⟨g, hg0, ?_⟩
    exact eq_mul_inv_of_mul_eq ((conj_key g γ).2 ⟨rfl, hb.symm, rfl, rfl⟩)

/-- The upper right entry of `h g⁻¹` in `SL₂(ℤ)`. -/
private lemma mulinv_01 (h g : SL(2, ℤ)) :
    (h * g⁻¹) 0 1 = -(h 0 0 * g 0 1) + h 0 1 * g 0 0 := by
  simp only [coe_mul, coe_inv]
  rw [Matrix.adjugate_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Membership in Miyake's index set. -/
private lemma mem_cosetIndex_iff {p N v : ℕ} :
    v ∈ cosetIndex p N ↔ v < p ∨ (v = p ∧ ¬ p ∣ N) := by
  unfold cosetIndex
  rw [Finset.mem_range]
  split_ifs with h
  · simp only [h, not_true_eq_false, and_false, or_false]
  · simp only [h, not_false_eq_true, and_true]
    omega

/-- All `γ_v` for `v` in the index set lie in `Γ₀(N)`. -/
private lemma gamma_mem {p N : ℕ} (γ : ℕ → SL(2, ℤ))
    (hlt : ∀ v < p, IsMiyakeGammaLt p N (γ v) v) (hP : ¬ p ∣ N → IsMiyakeGammaP p N (γ p))
    {v : ℕ} (hv : v ∈ cosetIndex p N) : γ v ∈ Gamma0 N := by
  rcases mem_cosetIndex_iff.1 hv with hv | ⟨rfl, hv⟩
  · exact (hlt v hv).1
  · exact (hP hv).1

/-- Every `h ∈ Γ₀(N)` is `γ_v`-close to the subgroup `p ∣ g 0 1`: some `v` in the index set has
`p ∣ (h γ_v⁻¹) 0 1`. -/
private lemma exists_index {p N : ℕ} [NeZero N] (hp : p.Prime) (γ : ℕ → SL(2, ℤ))
    (hlt : ∀ v < p, IsMiyakeGammaLt p N (γ v) v) (hP : ¬ p ∣ N → IsMiyakeGammaP p N (γ p))
    (h : SL(2, ℤ)) (hh : h ∈ Gamma0 N) :
    ∃ v ∈ cosetIndex p N, (p : ℤ) ∣ (h * (γ v)⁻¹) 0 1 := by
  have := Fact.mk hp
  have hdet := h.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hdetZ := congrArg (Int.cast : ℤ → ZMod p) hdet
  push_cast at hdetZ
  by_cases ha : ((h 0 0 : ℤ) : ZMod p) = 0
  · have hpN : ¬ p ∣ N := by
      intro hpN
      have hc : ((h 1 0 : ℤ) : ZMod p) = 0 := by
        obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (Gamma0_mem.1 hh)
        have hN : (N : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpN
        rw [hk]
        push_cast
        rw [hN, zero_mul]
      rw [ha, hc] at hdetZ
      simp at hdetZ
    refine ⟨p, mem_cosetIndex_iff.2 (Or.inr ⟨rfl, hpN⟩), ?_⟩
    obtain ⟨-, a, a', haa, g00, g01, g10, g11⟩ := hP hpN
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, mulinv_01]
    push_cast
    rw [g00, ha]
    simp
  · set v := (((h 0 1 : ℤ) : ZMod p) * ((h 0 0 : ℤ) : ZMod p)⁻¹).val with hv
    have hvp : v < p := ZMod.val_lt _
    obtain ⟨-, g00, g01, -, -⟩ := hlt v hvp
    refine ⟨v, mem_cosetIndex_iff.2 (Or.inl hvp), ?_⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, mulinv_01]
    push_cast
    rw [g00, g01, hv, ZMod.natCast_zmod_val]
    have key : ((h 0 0 : ℤ) : ZMod p) * (((h 0 1 : ℤ) : ZMod p) * ((h 0 0 : ℤ) : ZMod p)⁻¹) =
        ((h 0 1 : ℤ) : ZMod p) := by
      field_simp
    rw [key]
    ring

/-- Distinct members of the index set have `γ_v γ_w⁻¹` with upper right entry prime to `p`. -/
private lemma not_dvd_of_ne {p N : ℕ} (hp : p.Prime) (γ : ℕ → SL(2, ℤ))
    (hlt : ∀ v < p, IsMiyakeGammaLt p N (γ v) v) (hP : ¬ p ∣ N → IsMiyakeGammaP p N (γ p))
    {v w : ℕ} (hv : v ∈ cosetIndex p N) (hw : w ∈ cosetIndex p N) (hne : v ≠ w) :
    ¬ (p : ℤ) ∣ (γ v * (γ w)⁻¹) 0 1 := by
  have := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, mulinv_01]
  push_cast
  rcases mem_cosetIndex_iff.1 hv with hv | ⟨hvp, hvN⟩ <;>
    rcases mem_cosetIndex_iff.1 hw with hw | ⟨hwp, hwN⟩
  · obtain ⟨-, a0, a1, -, -⟩ := hlt v hv
    obtain ⟨-, b0, b1, -, -⟩ := hlt w hw
    rw [a0, a1, b0, b1]
    intro h
    apply hne
    have h1 : (v : ZMod p) = w := by linear_combination h
    have h2 := (ZMod.natCast_eq_natCast_iff' v w p).1 h1
    rwa [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hw] at h2
  · subst w
    obtain ⟨-, a0, a1, -, -⟩ := hlt v hv
    obtain ⟨-, a, a', haa, b0, b1, b2, b3⟩ := hP hwN
    rw [a0, a1, b0, b1]
    intro h
    have ha : ((a : ℤ) : ZMod p) = 0 := by linear_combination h
    push_cast at haa
    rw [ha, zero_mul] at haa
    exact zero_ne_one haa
  · subst v
    obtain ⟨-, b0, b1, -, -⟩ := hlt w hw
    obtain ⟨-, a, a', haa, a0, a1, a2, a3⟩ := hP hvN
    rw [a0, a1, b0, b1]
    intro h
    have ha : ((a : ℤ) : ZMod p) = 0 := by linear_combination -h
    push_cast at haa
    rw [ha, zero_mul] at haa
    exact zero_ne_one haa
  · exact absurd (hvp.trans hwp.symm) hne

/-- **Miyake, Lemma 4.5.11** (the union): the double coset `Γ₀(pN) [1 0; 0 p] Γ₀(N)` is the union
of the right cosets `Γ₀(pN) [1 0; 0 p] γ_v` over Miyake's index set. -/
@[kb "miyake1989" "Lemma 4.5.11, p. 143"]
theorem doubleCoset_eq_iUnion {p N : ℕ} [NeZero p] [NeZero N] (hp : p.Prime) (γ : ℕ → SL(2, ℤ))
    (hlt : ∀ v < p, IsMiyakeGammaLt p N (γ v) v) (hP : ¬ p ∣ N → IsMiyakeGammaP p N (γ p)) :
    DoubleCoset.doubleCoset (deltaP p) (gamma0GL (p * N)) (gamma0GL N) =
      ⋃ v ∈ cosetIndex p N, (gamma0GL (p * N) : Set (GL (Fin 2) ℚ)) *
        ({deltaP p * mapGL ℚ (γ v)} : Set (GL (Fin 2) ℚ)) := by
  ext x
  rw [DoubleCoset.mem_doubleCoset]
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨y, hy, k, hk, rfl⟩
    obtain ⟨κ, hκ, rfl⟩ := Subgroup.mem_map.1 hk
    obtain ⟨v, hv, hdvd⟩ := exists_index hp γ hlt hP κ hκ
    have hm : κ * (γ v)⁻¹ ∈ Gamma0 N := mul_mem hκ (inv_mem (gamma_mem γ hlt hP hv))
    have hc := (mem_Gamma0_conj_iff hm).2 hdvd
    refine ⟨v, hv, y * (deltaP p * mapGL ℚ (κ * (γ v)⁻¹) * (deltaP p)⁻¹),
      mul_mem hy hc, deltaP p * mapGL ℚ (γ v), rfl, ?_⟩
    simp only [map_mul, map_inv]
    group
  · rintro ⟨v, hv, y, hy, z, hz, rfl⟩
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨y, hy, mapGL ℚ (γ v), Subgroup.mem_map.2 ⟨γ v, gamma_mem γ hlt hP hv, rfl⟩,
      (mul_assoc _ _ _).symm⟩

/-- **Miyake, Lemma 4.5.11** (disjointness): the right cosets `Γ₀(pN) [1 0; 0 p] γ_v` over
Miyake's index set are pairwise disjoint. -/
@[kb "miyake1989" "Lemma 4.5.11, p. 143 (disjointness)"]
theorem pairwiseDisjoint_cosets {p N : ℕ} [NeZero p] [NeZero N] (hp : p.Prime) (γ : ℕ → SL(2, ℤ))
    (hlt : ∀ v < p, IsMiyakeGammaLt p N (γ v) v) (hP : ¬ p ∣ N → IsMiyakeGammaP p N (γ p)) :
    (cosetIndex p N : Set ℕ).PairwiseDisjoint
      (fun v ↦ (gamma0GL (p * N) : Set (GL (Fin 2) ℚ)) *
        ({deltaP p * mapGL ℚ (γ v)} : Set (GL (Fin 2) ℚ))) := by
  intro v hv w hw hne
  have hv' := Finset.mem_coe.1 hv
  have hw' := Finset.mem_coe.1 hw
  rw [Function.onFun, Set.disjoint_left]
  rintro x ⟨y1, hy1, z1, hz1, rfl⟩ ⟨y2, hy2, z2, hz2, h⟩
  rw [Set.mem_singleton_iff] at hz1 hz2
  subst hz1 hz2
  have hm : γ v * (γ w)⁻¹ ∈ Gamma0 N :=
    mul_mem (gamma_mem γ hlt hP hv') (inv_mem (gamma_mem γ hlt hP hw'))
  have hc : deltaP p * mapGL ℚ (γ v * (γ w)⁻¹) * (deltaP p)⁻¹ ∈ gamma0GL (p * N) := by
    have e : deltaP p * mapGL ℚ (γ v * (γ w)⁻¹) * (deltaP p)⁻¹ = y1⁻¹ * y2 := by
      calc deltaP p * mapGL ℚ (γ v * (γ w)⁻¹) * (deltaP p)⁻¹
          = y1⁻¹ * (y1 * (deltaP p * mapGL ℚ (γ v))) * (mapGL ℚ (γ w))⁻¹ * (deltaP p)⁻¹ := by
            simp only [map_mul, map_inv]; group
        _ = y1⁻¹ * (y2 * (deltaP p * mapGL ℚ (γ w))) * (mapGL ℚ (γ w))⁻¹ * (deltaP p)⁻¹ := by
            have h' : y2 * (deltaP p * mapGL ℚ (γ w)) = y1 * (deltaP p * mapGL ℚ (γ v)) := h
            rw [← h']
        _ = y1⁻¹ * y2 := by group
    rw [e]
    exact mul_mem (inv_mem hy1) hy2
  exact not_dvd_of_ne hp γ hlt hP hv' hw' hne ((mem_Gamma0_conj_iff hm).1 hc)

/-- The upper triangular unipotent `[1 v; 0 1]` in `SL₂(ℤ)`. -/
def unipotent (v : ℤ) : SL(2, ℤ) := ⟨!![1, v; 0, 1], by simp [Matrix.det_fin_two]⟩

/-- Entry `00` of `unipotent`. -/
private lemma unipotent_00 (v : ℤ) : unipotent v 0 0 = 1 := rfl
/-- Entry `01` of `unipotent`. -/
private lemma unipotent_01 (v : ℤ) : unipotent v 0 1 = v := rfl
/-- Entry `10` of `unipotent`. -/
private lemma unipotent_10 (v : ℤ) : unipotent v 1 0 = 0 := rfl
/-- Entry `11` of `unipotent`. -/
private lemma unipotent_11 (v : ℤ) : unipotent v 1 1 = 1 := rfl

/-- A family of representatives as in Lemma 4.5.11: `[1 v; 0 1]` for `v < p`, and Tau Ceti's
`TauCeti.descendExtraGamma p (pN)` at `v = p`. -/
def miyakeGamma (p N : ℕ) (v : ℕ) : SL(2, ℤ) :=
  if v < p then unipotent v else TauCeti.descendExtraGamma p (p * N)

/-- `miyakeGamma` satisfies all of Miyake's conditions, including `γ_p ≡ 1 mod N`. -/
theorem miyakeGamma_spec {p N : ℕ} [NeZero N] (hp : p.Prime) :
    (∀ v < p, IsMiyakeGammaLt p N (miyakeGamma p N v) v) ∧
      (¬ p ∣ N → IsMiyakeGammaP p N (miyakeGamma p N p) ∧
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) (miyakeGamma p N p) = 1) := by
  refine ⟨fun v hv => ?_, fun hpN => ?_⟩
  · simp only [miyakeGamma, hv, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Gamma0_mem]; simp [unipotent]
    all_goals simp [unipotent]
  · have hsq : ¬ p ^ 2 ∣ p * N := by
      rw [pow_two, Nat.mul_dvd_mul_iff_left hp.pos]; exact hpN
    have hdiv : p * N / p = N := Nat.mul_div_cancel_left _ hp.pos
    have hmem := TauCeti.descendExtraGamma_mem_Gamma0 hp (dvd_mul_right p N) hsq
    have hS := TauCeti.descendExtraGamma_map_intCast_zmod_eq_S hp (dvd_mul_right p N) hsq
    have h1 := TauCeti.descendExtraGamma_map_intCast_zmod_div_eq_one hp (dvd_mul_right p N) hsq
    rw [hdiv] at hmem h1
    have e : miyakeGamma p N p = TauCeti.descendExtraGamma p (p * N) := by
      simp only [miyakeGamma, lt_self_iff_false, ↓reduceIte]
    rw [e]
    have ent : ∀ i j : Fin 2, ((TauCeti.descendExtraGamma p (p * N) i j : ℤ) : ZMod p) =
        (((ModularGroup.S : SL(2, ℤ)) i j : ℤ) : ZMod p) := fun i j => by
      have := congrArg (fun g : SL(2, ZMod p) => (g : Matrix (Fin 2) (Fin 2) (ZMod p)) i j) hS
      simpa using this
    refine ⟨⟨hmem, 1, 1, by simp, ?_, ?_, ?_, ?_⟩, h1⟩
    · rw [ent]; simp [ModularGroup.S]
    · rw [ent]; simp [ModularGroup.S]
    · rw [ent]; simp [ModularGroup.S]
    · rw [ent]; simp [ModularGroup.S]

/-- Tau Ceti's descent family at level `pN` is `[1 0; 0 p] γ_v` for Miyake's representatives
`γ_v = miyakeGamma p N v` (the index sets agree: `descendMatrixCount p (pN)` is `p` if `p ∣ N`
and `p + 1` otherwise). -/
theorem descendMatrixRat_eq {p N : ℕ} [NeZero p] (v : Fin (TauCeti.descendMatrixCount p (p * N))) :
    TauCeti.descendMatrixRat p (p * N) v = deltaP p * mapGL ℚ (miyakeGamma p N v) := by
  by_cases h : v.val < p
  · rw [TauCeti.descendMatrixRat_of_lt h]
    simp only [miyakeGamma, h, ↓reduceIte]
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, HeckeRing.GL2.coe_upperTriRep, mapGL_coe_matrix,
        unipotent_00, unipotent_01, unipotent_10, unipotent_11]
  · rw [TauCeti.descendMatrixRat_of_le (not_lt.1 h)]
    simp only [miyakeGamma, h, ↓reduceIte]

/-- The size of Tau Ceti's descent family at level `pN` is Miyake's index count. -/
private lemma count_eq {p N : ℕ} (hp : p.Prime) :
    TauCeti.descendMatrixCount p (p * N) = if p ∣ N then p else p + 1 := by
  have h : p * p ∣ p * N ↔ p ∣ N := Nat.mul_dvd_mul_iff_left hp.pos
  simp only [TauCeti.descendMatrixCount, pow_two, h]

/-- Indices of Tau Ceti's family are exactly Miyake's index set. -/
private lemma fin_mem_cosetIndex {p N : ℕ} (hp : p.Prime)
    (v : Fin (TauCeti.descendMatrixCount p (p * N))) : v.val ∈ cosetIndex p N := by
  exact Finset.mem_range.2 (lt_of_lt_of_eq v.2 (count_eq hp))

/-- Conversely, Miyake's index set is the index set of Tau Ceti's family. -/
private lemma lt_count_of_mem {p N v : ℕ} (hp : p.Prime) (hv : v ∈ cosetIndex p N) :
    v < TauCeti.descendMatrixCount p (p * N) := by
  exact lt_of_lt_of_eq (Finset.mem_range.1 hv) (count_eq hp).symm

/-- **Miyake, Lemma 4.5.11** for Tau Ceti's descent family: the double coset
`Γ₀(pN) [1 0; 0 p] Γ₀(N)` is the union of the right cosets `Γ₀(pN) α_v`,
`α_v = TauCeti.descendMatrixRat p (pN) v`. -/
@[kb "miyake1989" "Lemma 4.5.11, p. 143 (Tau Ceti's descent family)"]
theorem doubleCoset_eq_iUnion_descendMatrixRat {p N : ℕ} [NeZero p] [NeZero N] (hp : p.Prime) :
    DoubleCoset.doubleCoset (deltaP p) (gamma0GL (p * N)) (gamma0GL N) =
      ⋃ v, (gamma0GL (p * N) : Set (GL (Fin 2) ℚ)) *
        ({TauCeti.descendMatrixRat p (p * N) v} : Set (GL (Fin 2) ℚ)) := by
  have hspec := miyakeGamma_spec (p := p) (N := N) hp
  rw [doubleCoset_eq_iUnion hp (miyakeGamma p N) hspec.1 (fun h => (hspec.2 h).1)]
  ext x
  simp only [Set.mem_iUnion, descendMatrixRat_eq]
  constructor
  · rintro ⟨v, hv, hx⟩
    exact ⟨⟨v, lt_count_of_mem hp hv⟩, hx⟩
  · rintro ⟨v, hx⟩
    exact ⟨v.val, fin_mem_cosetIndex hp v, hx⟩

/-- **Miyake, Lemma 4.5.11** for Tau Ceti's descent family: the right cosets `Γ₀(pN) α_v` are
pairwise disjoint. -/
@[kb "miyake1989" "Lemma 4.5.11, p. 143 (Tau Ceti's descent family, disjointness)"]
theorem pairwiseDisjoint_descendMatrixRat {p N : ℕ} [NeZero p] [NeZero N] (hp : p.Prime) :
    Pairwise (Function.onFun Disjoint
      (fun v : Fin (TauCeti.descendMatrixCount p (p * N)) ↦
        (gamma0GL (p * N) : Set (GL (Fin 2) ℚ)) *
        ({TauCeti.descendMatrixRat p (p * N) v} : Set (GL (Fin 2) ℚ)))) := by
  have hspec := miyakeGamma_spec (p := p) (N := N) hp
  have hd := pairwiseDisjoint_cosets hp (miyakeGamma p N) hspec.1 (fun h => (hspec.2 h).1)
  intro v w hvw
  simp only [Function.onFun, descendMatrixRat_eq]
  exact hd (Finset.mem_coe.2 (fin_mem_cosetIndex hp v)) (Finset.mem_coe.2 (fin_mem_cosetIndex hp w))
    (fun h => hvw (Fin.ext h))

end ModularFormsKB.Miyake.Wave6
