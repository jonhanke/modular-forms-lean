import ModularFormsKB.Miyake.Wave4.Newforms
import TauCeti.NumberTheory.ModularForms.Newforms.Associated

/-!
# Miyake, Theorem 4.6.19 and Corollary 4.6.20: eigenforms lie in the old space of one primitive form

Miyake, *Modular Forms* (Springer 1989), §4.6, pp. 173–175.

* **Corollary 4.6.20** (p. 175): if a nonzero `f ∈ 𝒮_k(N, χ)` satisfies `f ∣ T(n) = a_n f` for
  all `n` prime to `N`, there are a unique divisor `M` of `N` (with `m_χ ∣ M`) and a unique
  primitive form `g ∈ 𝒮_k^0(M, χ)` with `g ∣ T(n) = a_n g` for `n` prime to `N`, and
  `f ∈ ⊕_{l ∣ N/M} ℂ g(lz)`.
  Existence and uniqueness were proved in wave 4 (`Miyake.Wave4.exists_isPrimitive_of_eigen`,
  `Miyake.Wave4.isPrimitive_unique_of_eigen`); the span assertion is new here, as a bridge to Tau
  Ceti main's `HeckeRing.GL2.Newform.mem_span_levelRaise_of_comp_unitsMap_eq` (file
  `Newforms/Associated.lean`). The `g(lz)` are Tau Ceti's level raises
  `CuspForm.levelRaise l _ g`, `(V_l g)(z) = g(lz)`, indexed by `l` with `l M ∣ N`. That the sum is
  direct (the `g(lz)` are linearly independent) is not restated here.
* **Theorem 4.6.19** (p. 173): a primitive form `f = Σ a_n qⁿ` of `𝒮_k(N, χ)` and a common
  eigenfunction `g = Σ b_n qⁿ` of level `M` with `b_1 = 1` and `a_n = b_n` for all `n` prime to
  some `L ≥ 1`. Proved here (`theorem_4_6_19_span`): for `g` any eigenfunction of the `T(n)`,
  `n` prime to `M`, with `b_1 = 1` (not necessarily new), `N ∣ M` and `g` lies in the span of the
  `f(lz)`, `l N ∣ M`; and (`theorem_4_6_19_of_new`) if `g` is moreover new, `N = M` and `f = g`.
  Miyake's conclusion `N = M`, `f = g` for `g` an eigenfunction of all of `ℛ(M) ∪ ℛ*(M)` needs in
  addition that no nonzero combination `Σ c_l f(lz)` with `M ≠ N` is an eigenfunction of both the
  `T(q)` and the `T*(q)` for the primes `q ∣ M`; that step is loose end LE-MF-0183. (Without the
  `T*(q)` the conclusion fails: at level `Nq`, `q ∤ N`, the combinations `f(z) - β f(qz)` with `β`
  a root of `X² - a_q X + χ(q) q^{k-1}` are eigenfunctions of every `T(n)` with `b_1 = 1`.)
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Sec4_6

open Wave4

variable {N : ℕ} [NeZero N]

/-- Our `heckeT` at a prime agrees with Tau Ceti's `heckeTCuspNat`. -/
lemma heckeTCuspNat_eq_of_heckeT {k : ℤ} {χ : DirichletCharacter ℂ N} {f : cuspSpace k χ}
    {p : ℕ} (hp : p.Prime) {t : ℂ} (h : heckeT k χ p f = t • f) :
    HeckeRing.GL2.heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      t • (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  rw [← HeckeRing.GL2.coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k χ.toUnitHom hp f,
    ← HeckeRing.GL2.heckeTCompositeGamma0_prime N hp]
  exact congrArg Subtype.val h

/-- The level raises `g(lz)`, `l M ∣ N`, of a cusp form `g` of level `M`, as cusp forms of
level `N`. -/
def levelRaises (N : ℕ) [NeZero N] {M : ℕ} {k : ℤ} (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    Set (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  {G | ∃ (l : ℕ) (_ : NeZero l) (h : l * M ∣ N),
    TauCeti.CuspForm.levelRaise l (TauCeti.Gamma1_map_le_conjAct_scaleGL_of_dvd h) g = G}

/-- The eigenvalues of a primitive form `g` with `g ∣ T(n) = a_n g` are its coefficients. -/
lemma coeff_eq_of_isPrimitive {M : ℕ} [NeZero M] {k : ℤ} {ψ : DirichletCharacter ℂ M}
    {g : cuspSpace k ψ} (hg : IsPrimitive g) {n : ℕ} (hn : n ≠ 0) {t : ℂ}
    (h : heckeT k ψ n g = t • g) : coeff g n = t := by
  rw [coeff_eq_of_eigen hn h, hg.2.2, mul_one]

/-- **Miyake, Corollary 4.6.20**: let `f ∈ 𝒮_k(N, χ)`, `f ≠ 0`, with `f ∣ T(n) = a_n f` for all
`n` prime to `N`. Then there are a divisor `M` of `N`, a character `χ_M` modulo `M` inducing `χ`
and a primitive form `g ∈ 𝒮_k^0(M, χ_M)` with `g ∣ T(n) = a_n g` for `n` prime to `N`, such that
`f` lies in the span of the `g(lz)`, `l M ∣ N`. (Uniqueness of `(M, g)`:
`Miyake.Wave4.isPrimitive_unique_of_eigen`.) -/
@[kb "miyake1989" "Corollary 4.6.20, p. 175"]
theorem corollary_4_6_20 (k : ℤ) (χ : DirichletCharacter ℂ N) {f : cuspSpace k χ} (hf0 : f ≠ 0)
    (a : ℕ → ℂ) (h : ∀ n : ℕ, n ≠ 0 → n.Coprime N → heckeT k χ n f = a n • f) :
    ∃ (M : ℕ) (_ : NeZero M) (hM : M ∣ N) (χM : DirichletCharacter ℂ M) (g : cuspSpace k χM),
      χM.changeLevel hM = χ ∧ IsPrimitive g ∧
      (∀ n : ℕ, n ≠ 0 → n.Coprime N → heckeT k χM n g = a n • g) ∧
      (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
        Submodule.span ℂ (levelRaises N (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)) := by
  obtain ⟨M, hMne, hM, χM, g, hlev, hprim, heig⟩ := exists_isPrimitive_of_eigen k χ hf0 a h
  refine ⟨M, hMne, hM, χM, g, hlev, hprim, heig, ?_⟩
  obtain ⟨G, hGχ, hG⟩ := (isPrimitive_iff_exists_newform g).1 hprim
  have hGχN : G.χ.comp (ZMod.unitsMap hM) = χ.toUnitHom := by
    rw [hGχ, ← DirichletCharacter.changeLevel_toUnitHom, hlev]
  have key := HeckeRing.GL2.Newform.mem_span_levelRaise_of_comp_unitsMap_eq G hM hGχN f.2
    (fun p hp hpN ↦ by
      rw [← HeckeRing.GL2.Newform.qExpansion_coeff_eq_eigenvalue G ⟨p, hp.pos⟩, hG]
      show _ = coeff g p • _
      rw [coeff_eq_of_isPrimitive hprim hp.ne_zero (heig p hp.ne_zero hpN)]
      exact heckeTCuspNat_eq_of_heckeT hp (h p hp.ne_zero hpN))
  rw [hG] at key
  exact key

/-- **Miyake, Theorem 4.6.19**, span form: let `f = Σ a_n qⁿ` be a primitive form of
`𝒮_k^0(N, χ)` and `g = Σ b_n qⁿ ∈ 𝒮_k(M, ψ)` a common eigenfunction of the `T(n)`, `n` prime to
`M`, with `b_1 = 1`, where `χ` and `ψ` induce the same character modulo `lcm(N, M)`. If
`a_n = b_n` for all `n` prime to some `L ≥ 1`, then `N ∣ M` and `g` lies in the span of the
`f(lz)`, `l N ∣ M`. -/
@[kb "miyake1989" "Theorem 4.6.19, p. 173 (g an eigenfunction away from M: N | M, g in the span of the f(lz))"]
theorem theorem_4_6_19_span {M : ℕ} [NeZero M] {k : ℤ} {χ : DirichletCharacter ℂ N}
    {ψ : DirichletCharacter ℂ M}
    (hχψ : χ.changeLevel (Nat.dvd_lcm_left N M) = ψ.changeLevel (Nat.dvd_lcm_right N M))
    {f : cuspSpace k χ} {g : cuspSpace k ψ} (hf : IsPrimitive f)
    (hg : ∀ n : ℕ, n ≠ 0 → n.Coprime M → ∃ t : ℂ, heckeT k ψ n g = t • g) (hg1 : coeff g 1 = 1)
    {L : ℕ} (hL : L ≠ 0) (h : ∀ n : ℕ, n.Coprime L → coeff f n = coeff g n) :
    N ∣ M ∧ (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) ∈
      Submodule.span ℂ (levelRaises M (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [coeff_zero_elem] at hg1
    exact zero_ne_one hg1
  -- the eigenvalues of `g` are its coefficients
  have hgc : ∀ n : ℕ, n ≠ 0 → n.Coprime M → heckeT k ψ n g = coeff g n • g := by
    intro n hn hnM
    obtain ⟨t, ht⟩ := hg n hn hnM
    rw [ht, coeff_eq_of_eigen hn ht, hg1, mul_one]
  obtain ⟨M₀, hM₀ne, hM₀, χ₀, g₀, hlev, hprim, heig, hspan⟩ :=
    corollary_4_6_20 k ψ hg0 (fun n ↦ coeff g n) hgc
  -- `g₀` and `f` are primitive with the same coefficients away from `L M`
  have hcoef : ∀ n : ℕ, n.Coprime (L * M) → coeff f n = coeff g₀ n := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [coeff_zero_eq, coeff_zero_eq]
    have hnM := (Nat.coprime_mul_iff_right.mp hn).2
    rw [h n (Nat.coprime_mul_iff_right.mp hn).1,
      coeff_eq_of_isPrimitive hprim hn0.ne' (heig n hn0.ne' hnM)]
  have hχ₀ : χ.changeLevel (Nat.dvd_lcm_left N M₀) = χ₀.changeLevel (Nat.dvd_lcm_right N M₀) := by
    have hL1 : Nat.lcm N M₀ ∣ Nat.lcm N M :=
      Nat.lcm_dvd (Nat.dvd_lcm_left N M) (hM₀.trans (Nat.dvd_lcm_right N M))
    apply DirichletCharacter.changeLevel_injective hL1
    calc DirichletCharacter.changeLevel hL1 (χ.changeLevel (Nat.dvd_lcm_left N M₀))
        = χ.changeLevel (Nat.dvd_lcm_left N M) :=
          (DirichletCharacter.changeLevel_trans χ _ _).symm
      _ = ψ.changeLevel (Nat.dvd_lcm_right N M) := hχψ
      _ = (χ₀.changeLevel hM₀).changeLevel (Nat.dvd_lcm_right N M) := by rw [hlev]
      _ = χ₀.changeLevel (hM₀.trans (Nat.dvd_lcm_right N M)) :=
          (DirichletCharacter.changeLevel_trans χ₀ _ _).symm
      _ = DirichletCharacter.changeLevel hL1 (χ₀.changeLevel (Nat.dvd_lcm_right N M₀)) :=
          DirichletCharacter.changeLevel_trans χ₀ _ _
  have hLM : L * M ≠ 0 := mul_ne_zero hL (NeZero.ne M)
  obtain ⟨hNM, hfun⟩ := eq_of_isPrimitive hχ₀ hf hprim hLM hcoef
  subst hNM
  have hfg : (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = g₀ := DFunLike.coe_injective hfun
  exact ⟨hM₀, hfg ▸ hspan⟩

/-- **Miyake, Theorem 4.6.19** for `g` new: if in `theorem_4_6_19_span` the form `g` lies in
`𝒮_k^0(M, ψ)`, then `N = M` and `f = g` as functions on `ℍ`. -/
@[kb "miyake1989" "Theorem 4.6.19, p. 173 (g new)"]
theorem theorem_4_6_19_of_new {M : ℕ} [NeZero M] {k : ℤ} {χ : DirichletCharacter ℂ N}
    {ψ : DirichletCharacter ℂ M}
    (hχψ : χ.changeLevel (Nat.dvd_lcm_left N M) = ψ.changeLevel (Nat.dvd_lcm_right N M))
    {f : cuspSpace k χ} {g : cuspSpace k ψ} (hf : IsPrimitive f) (hgnew : g ∈ newSpace k ψ)
    (hg : ∀ n : ℕ, n ≠ 0 → n.Coprime M → ∃ t : ℂ, heckeT k ψ n g = t • g) (hg1 : coeff g 1 = 1)
    {L : ℕ} (hL : L ≠ 0) (h : ∀ n : ℕ, n.Coprime L → coeff f n = coeff g n) :
    N = M ∧ ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ⇑(g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :=
  eq_of_isPrimitive hχψ hf ⟨hgnew, hg, hg1⟩ hL h

end ModularFormsKB.Miyake.Sec4_6
