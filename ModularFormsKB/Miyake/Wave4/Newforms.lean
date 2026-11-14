import ModularFormsKB.Miyake.Wave4.HeckeCoefficients
import TauCeti.NumberTheory.ModularForms.Newforms.EigenvectorVanishing
import TauCeti.NumberTheory.ModularForms.Newforms.SupportAwayFromLevel
import TauCeti.NumberTheory.ModularForms.Newforms.Hecke.Stability
import TauCeti.NumberTheory.ModularForms.Newforms.OrthogonalBasis
import TauCeti.NumberTheory.ModularForms.Newforms.Decomposition
import TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform
import TauCeti.NumberTheory.ModularForms.Newforms.StrongMultiplicityOne.Basic

/-!
# Miyake §4.6: new forms and primitive forms

Miyake, *Modular Forms* (Springer 1989), §4.6, pp. 162–175.

## Miyake's spaces in Tau Ceti's terms
* Miyake's `𝒮_k^0(N, χ)` (p. 162) is the orthogonal complement in `𝒮_k(N, χ)` of the old space
  `𝒮_k^1(N, χ)` spanned by the `g(lz)`, `g ∈ 𝒮_k(M, χ)`, `m_χ ∣ M ∣ N`, `M ≠ N`, `l ∣ N/M`.
  Here `newSpace k χ` is Tau Ceti's new subspace `cuspFormsNew N k` of `S_k(Γ₁(N))` (the orthogonal
  complement of all old forms of all characters) intersected with `𝒮_k(N, χ)`. The two agree
  because the old space and the Petersson product are compatible with the decomposition of
  `S_k(Γ₁(N))` by characters; that identification is not proved in this file (loose end).
* A *primitive form* (p. 164) is an `f ∈ 𝒮_k^0(N, χ)` which is a common eigenfunction of the
  `T(n)` with `(n, N) = 1` and has `a_1 = 1` (`IsPrimitive`); these are Tau Ceti's `Newform`s
  with nebentypus `χ` (`isPrimitive_iff_exists_newform`).

## Results (all proved here from Tau Ceti)
* Lemma 4.6.10 (cusp part), Lemma 4.6.11 and Theorem 4.6.12 with Miyake's arbitrary `L`,
  Theorem 4.6.13 (1) for the `T(n)` and `T(n, n)`, Theorem 4.6.13 (2), Corollary 4.6.14 (first
  part), Theorem 4.6.19 for two primitive forms, Corollary 4.6.20 (existence and uniqueness of
  the primitive form, without the decomposition `f ∈ ⊕ ℂ g(lz)`).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave4

variable {N : ℕ} [NeZero N]

/-- Miyake's `𝒮_k^0(N, χ)` (p. 162): the new forms in `𝒮_k(N, χ)`. -/
abbrev newSpace (k : ℤ) (χ : DirichletCharacter ℂ N) : Submodule ℂ (cuspSpace k χ) :=
  (TauCeti.cuspFormsNew N k).comap (cuspSpace k χ).subtype

/-- Miyake's *primitive form* of `𝒮_k^0(N, χ)` (p. 164): a new form which is a common
eigenfunction of all `T(n)` with `(n, N) = 1`, normalised by `a_1 = 1`. -/
def IsPrimitive {k : ℤ} {χ : DirichletCharacter ℂ N} (f : cuspSpace k χ) : Prop :=
  f ∈ newSpace k χ ∧ (∀ n : ℕ, n ≠ 0 → n.Coprime N → ∃ a : ℂ, heckeT k χ n f = a • f) ∧
    coeff f 1 = 1

/-- A newform of nebentypus `χ` is an eigenfunction of every `T(n)`, `n ≥ 1`, with eigenvalue its
`n`-th coefficient. -/
lemma heckeT_eq_of_newform {k : ℤ} {χ : DirichletCharacter ℂ N} (g : HeckeRing.GL2.Newform N k)
    (hχ : g.χ = χ.toUnitHom) (f : cuspSpace k χ)
    (hf : g.toCuspForm = (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) {n : ℕ} (hn : n ≠ 0) :
    heckeT k χ n f = coeff f n • f := by
  have h := g.heckeRingHomCuspCharSpace_heckeTCompositeGamma0_eq_qExpansion_coeff_smul
    ⟨n, Nat.pos_of_ne_zero hn⟩
  have key : ∀ (χ' : (ZMod N)ˣ →* ℂˣ) (_ : g.χ = χ')
      (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (_ : g.toCuspForm = F)
      (hm : F ∈ TauCeti.cuspFormCharSpace k χ'),
      HeckeRing.GL2.heckeRingHomCuspCharSpace k χ' (HeckeRing.GL2.heckeTCompositeGamma0 N n)
          ⟨F, hm⟩ = (qExpansion 1 F).coeff n • (⟨F, hm⟩ : TauCeti.cuspFormCharSpace k χ') := by
    intro χ' hχ' F hF hm
    subst hχ' hF
    exact h
  exact key _ hχ _ hf f.2

/-- Primitive forms of `𝒮_k^0(N, χ)` are exactly Tau Ceti's newforms of nebentypus `χ`. -/
theorem isPrimitive_iff_exists_newform {k : ℤ} {χ : DirichletCharacter ℂ N} (f : cuspSpace k χ) :
    IsPrimitive f ↔ ∃ g : HeckeRing.GL2.Newform N k,
      g.χ = χ.toUnitHom ∧ g.toCuspForm = (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  constructor
  · rintro ⟨hnew, heig, h1⟩
    refine ⟨{ toCuspForm := f, χ := χ.toUnitHom, mem_charSpace := f.2,
               eigenvalue := fun n hn ↦ (heig n n.ne_zero hn).choose,
               isEigen := fun n hn ↦ (heig n n.ne_zero hn).choose_spec,
               ne_zero := ?_, isNew := hnew, isNorm := h1 }, rfl, rfl⟩
    intro h0
    have hf0 : f = 0 := Subtype.ext h0
    rw [hf0, coeff_zero_elem] at h1
    exact zero_ne_one h1
  · rintro ⟨g, hχ, hg⟩
    refine ⟨?_, fun n hn _ ↦ ⟨coeff f n, heckeT_eq_of_newform g hχ f hg hn⟩, ?_⟩
    · show (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ TauCeti.cuspFormsNew N k
      rw [← hg]; exact g.isNew
    · show (qExpansion 1 (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff 1 = 1
      rw [← hg]; exact g.isNorm

/-- **Miyake, Lemma 4.6.10** (cusp forms): `𝒮_k^0(N, χ)` is stable under `T(n)` for
`(n, N) = 1`. -/
@[kb "miyake1989" "Lemma 4.6.10, p. 163 (new space)"]
theorem heckeT_mem_newSpace (k : ℤ) (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : n.Coprime N)
    {f : cuspSpace k χ} (hf : f ∈ newSpace k χ) : heckeT k χ n f ∈ newSpace k χ :=
  HeckeRing.GL2.heckeRingHomCuspCharSpace_heckeTCompositeGamma0_mem_of_forall_prime_dvd
    (V := newSpace k χ)
    (fun _ hp hpn _ hF ↦
      TauCeti.coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0_mem_cuspFormsNew hp
        (Nat.Coprime.coprime_dvd_left hpn hn) hF) hf

/-- The coefficients of a difference. -/
lemma coeff_sub {k : ℤ} {χ : DirichletCharacter ℂ N} (f g : cuspSpace k χ) (n : ℕ) :
    coeff (f - g) n = coeff f n - coeff g n := by
  have := map_sub (CuspForm.qExpansionCoeffₗ one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map N) k n)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
  simp only [CuspForm.qExpansionCoeffₗ_apply] at this
  exact this

/-- Key step of Lemma 4.6.11 and Theorem 4.6.12: a new eigenvector with `a₁ = 0` vanishes. -/
lemma eq_zero_of_coeff_one_eq_zero (k : ℤ) (χ : DirichletCharacter ℂ N) {L : ℕ} (hL : L ≠ 0)
    {f : cuspSpace k χ} (hf : f ∈ newSpace k χ)
    (h : ∀ n : ℕ, n ≠ 0 → n.Coprime L → ∃ a : ℂ, heckeT k χ n f = a • f)
    (h1 : coeff f 1 = 0) : f = 0 := by
  have hvan : ∀ n : ℕ, n.Coprime (L * N) →
      (qExpansion 1 (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n = 0 := fun n hn ↦
    HeckeRing.GL2.qExpansion_coeff_eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_coprime
      (F := f) (L := L * N) (Dvd.intro_left L rfl)
      (fun p hp hpL ↦ by
        obtain ⟨a, ha⟩ := h p hp.ne_zero (Nat.coprime_mul_iff_right.mp hpL).1
        exact ⟨a, ha⟩)
      h1 n hn
  have hvan2 : ∀ n : ℕ, n.Coprime N →
      (qExpansion 1 (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n = 0 := fun n hn ↦
    TauCeti.qExpansion_coeff_eq_zero_of_forall_coprime_mul hL f.2 hvan n hn
  have hold := TauCeti.mem_cuspFormsOld_of_forall_coprime_qExpansion_coeff_eq_zero f.2 hvan2
  have := Submodule.disjoint_def.mp (TauCeti.disjoint_cuspFormsOld_cuspFormsNew N k) _ hold hf
  exact Subtype.ext this

/-- **Miyake, Lemma 4.6.11**: let `f = Σ a_n qⁿ ∈ 𝒮_k^0(N, χ)`, `f ≠ 0`. If `f` is a common
eigenfunction of the `T(n)` for all `n` prime to some integer `L ≥ 1`, then `a_1 ≠ 0`. -/
@[kb "miyake1989" "Lemma 4.6.11, p. 163"]
theorem coeff_one_ne_zero (k : ℤ) (χ : DirichletCharacter ℂ N) {L : ℕ} (hL : L ≠ 0)
    {f : cuspSpace k χ} (hf : f ∈ newSpace k χ) (hf0 : f ≠ 0)
    (h : ∀ n : ℕ, n ≠ 0 → n.Coprime L → ∃ a : ℂ, heckeT k χ n f = a • f) :
    coeff f 1 ≠ 0 := fun h1 ↦ hf0 (eq_zero_of_coeff_one_eq_zero k χ hL hf h h1)

/-- **Miyake, Theorem 4.6.12**: let `f, g ∈ 𝒮_k^0(N, χ)`, `f ≠ 0`. If `f` and `g` are common
eigenfunctions of `T(n)` with the same eigenvalue for each `n` prime to some integer `L ≥ 1`,
then `g` is a constant multiple of `f`. -/
@[kb "miyake1989" "Theorem 4.6.12, p. 163"]
theorem exists_eq_smul_of_eigen (k : ℤ) (χ : DirichletCharacter ℂ N) {L : ℕ} (hL : L ≠ 0)
    {f g : cuspSpace k χ} (hf : f ∈ newSpace k χ) (hg : g ∈ newSpace k χ) (hf0 : f ≠ 0)
    (h : ∀ n : ℕ, n ≠ 0 → n.Coprime L → ∃ a : ℂ, heckeT k χ n f = a • f ∧ heckeT k χ n g = a • g) :
    ∃ c : ℂ, g = c • f := by
  have hc1 := coeff_one_ne_zero k χ hL hf hf0 fun n hn hnL ↦
    (h n hn hnL).imp fun _ ha ↦ ha.1
  refine ⟨coeff g 1 / coeff f 1, ?_⟩
  have hz : g - (coeff g 1 / coeff f 1) • f = 0 := by
    refine eq_zero_of_coeff_one_eq_zero k χ hL (Submodule.sub_mem _ hg (Submodule.smul_mem _ _ hf))
      (fun n hn hnL ↦ ?_) ?_
    · obtain ⟨a, haf, hag⟩ := h n hn hnL
      refine ⟨a, ?_⟩
      rw [map_sub, map_smul, haf, hag]
      module
    · rw [coeff_sub, coeff_smul]
      field_simp
      ring
  exact sub_eq_zero.mp hz

/-- **Miyake, Theorem 4.6.13 (1)**, for the generators `T(n)` and `T(n, n)` of `ℛ(N)`: a
primitive form is an eigenfunction of every `T(n)` (`n ≥ 1`, including `n` not prime to `N`) and
every `T(n, n)`. (The other elements of `ℛ(N)` and the algebra `ℛ*(N)` are not treated.) -/
@[kb "miyake1989" "Theorem 4.6.13 (1), p. 165 (T(n) and T(n,n))"]
theorem IsPrimitive.heckeT_eigen {k : ℤ} {χ : DirichletCharacter ℂ N} {f : cuspSpace k χ}
    (hf : IsPrimitive f) {n : ℕ} (hn : n ≠ 0) :
    heckeT k χ n f = coeff f n • f ∧ ∃ c : ℂ, heckeTT k χ n n f = c • f := by
  obtain ⟨g, hχ, hg⟩ := (isPrimitive_iff_exists_newform f).1 hf
  refine ⟨heckeT_eq_of_newform g hχ f hg hn, χ n * (n : ℂ) ^ (k - 2), ?_⟩
  rw [heckeTT_self k χ (Nat.pos_of_ne_zero hn)]
  simp

/-- **Miyake, Theorem 4.6.13 (2)**: `𝒮_k^0(N, χ)` has a basis consisting of primitive forms. -/
@[kb "miyake1989" "Theorem 4.6.13 (2), p. 165"]
theorem exists_basis_isPrimitive (k : ℤ) (χ : DirichletCharacter ℂ N) :
    ∃ (ι : Type) (b : Module.Basis ι ℂ (newSpace k χ)), ∀ i, IsPrimitive ((b i : cuspSpace k χ)) := by
  refine ⟨{f : HeckeRing.GL2.Newform N k // f.χ = χ.toUnitHom},
    HeckeRing.GL2.Newform.basisCharSpace N k χ.toUnitHom, fun i ↦ ?_⟩
  exact (isPrimitive_iff_exists_newform _).2
    ⟨i.1, i.2, (HeckeRing.GL2.Newform.coe_coe_basisCharSpace_apply χ.toUnitHom i).symm⟩

section EigenFacts

variable {k : ℤ} {χ : DirichletCharacter ℂ N}

lemma ne_zero_of_isPrimitive {f : cuspSpace k χ} (hf : IsPrimitive f) : f ≠ 0 := by
  rintro rfl
  have := hf.2.2
  rw [coeff_zero_elem] at this
  exact zero_ne_one this

lemma eigen_one {f : cuspSpace k χ} (hf : f ≠ 0) {a : ℕ → ℂ}
    (h : ∀ n : ℕ, n ≠ 0 → n.Coprime N → heckeT k χ n f = a n • f) : a 1 = 1 := by
  have h1 := h 1 one_ne_zero (Nat.coprime_one_left N)
  rw [heckeT_one] at h1
  have h2 : (1 : ℂ) • f = a 1 • f := by simpa using h1
  exact (smul_left_injective ℂ hf h2).symm

lemma eigen_mul {f : cuspSpace k χ} (hf : f ≠ 0) {a : ℕ → ℂ}
    (h : ∀ n : ℕ, n ≠ 0 → n.Coprime N → heckeT k χ n f = a n • f) {x y : ℕ} (hx : x ≠ 0)
    (hy : y ≠ 0) (hxy : x.Coprime y) (hxN : x.Coprime N) (hyN : y.Coprime N) :
    a (x * y) = a x * a y := by
  have h1 := h (x * y) (mul_ne_zero hx hy)
    (Nat.coprime_mul_iff_left.mpr ⟨hxN, hyN⟩)
  rw [heckeT_mul_of_coprime' hxy, mul_apply_eq_comp, h y hy hyN, map_smul, h x hx hxN,
    smul_smul] at h1
  have := smul_left_injective ℂ hf h1
  rw [← this, mul_comm]

lemma eigen_rec {f : cuspSpace k χ} (hf : f ≠ 0) {a : ℕ → ℂ}
    (h : ∀ n : ℕ, n ≠ 0 → n.Coprime N → heckeT k χ n f = a n • f) {p : ℕ} (hp : p.Prime)
    (hpN : p.Coprime N) (r : ℕ) :
    a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - χ p * (p : ℂ) ^ (k - 1) * a (p ^ r) := by
  have h1 := congrArg (fun T : Module.End ℂ (cuspSpace k χ) ↦ T f)
    (heckeT_prime_pow_add_two (k := k) (χ := χ) hp r)
  simp only [LinearMap.sub_apply, mul_apply_eq_comp, LinearMap.smul_apply] at h1
  rw [h _ (pow_ne_zero _ hp.ne_zero) (hpN.pow_left _), h _ (pow_ne_zero _ hp.ne_zero)
    (hpN.pow_left _), h _ (pow_ne_zero _ hp.ne_zero) (hpN.pow_left _), map_smul,
    h _ hp.ne_zero hpN] at h1
  have h2 : a (p ^ (r + 2)) • f =
      (a p * a (p ^ (r + 1)) - χ p * (p : ℂ) ^ (k - 1) * a (p ^ r)) • f := by
    rw [h1]; module
  exact smul_left_injective ℂ hf h2

omit [NeZero N] in
lemma seq_eq_of_rec (X : ℕ → ℂ) {a b : ℕ → ℂ} (ha1 : a 1 = 1) (hb1 : b 1 = 1)
    (ham : ∀ x y : ℕ, x ≠ 0 → y ≠ 0 → x.Coprime y → x.Coprime N → y.Coprime N →
      a (x * y) = a x * a y)
    (hbm : ∀ x y : ℕ, x ≠ 0 → y ≠ 0 → x.Coprime y → x.Coprime N → y.Coprime N →
      b (x * y) = b x * b y)
    (har : ∀ p : ℕ, p.Prime → p.Coprime N → ∀ r : ℕ,
      a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - X p * a (p ^ r))
    (hbr : ∀ p : ℕ, p.Prime → p.Coprime N → ∀ r : ℕ,
      b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - X p * b (p ^ r))
    (hp : ∀ p : ℕ, p.Prime → p.Coprime N → a p = b p) :
    ∀ n : ℕ, n ≠ 0 → n.Coprime N → a n = b n := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p r hpr hr =>
    intro _ hc
    have hpN : p.Coprime N := Nat.Coprime.coprime_dvd_left (dvd_pow_self p hr.ne') hc
    have key : ∀ s : ℕ, a (p ^ s) = b (p ^ s) ∧ a (p ^ (s + 1)) = b (p ^ (s + 1)) := by
      intro s
      induction s with
      | zero => exact ⟨by simp [ha1, hb1], by simpa using hp p hpr hpN⟩
      | succ s ih =>
        refine ⟨ih.2, ?_⟩
        show a (p ^ (s + 2)) = b (p ^ (s + 2))
        rw [har p hpr hpN s, hbr p hpr hpN s, ih.1, ih.2, hp p hpr hpN]
    exact (key r).1
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; rw [ha1, hb1]
  | coprime x y hx hy hxy ihx ihy =>
    intro _ hc
    have hxN := (Nat.coprime_mul_iff_left.mp hc).1
    have hyN := (Nat.coprime_mul_iff_left.mp hc).2
    have hx0 : x ≠ 0 := by omega
    have hy0 : y ≠ 0 := by omega
    rw [ham x y hx0 hy0 hxy hxN hyN, hbm x y hx0 hy0 hxy hxN hyN, ihx hx0 hxN, ihy hy0 hyN]

end EigenFacts

/-- **Miyake, Corollary 4.6.14** (first part): if a nonzero `f ∈ 𝒮_k(N, χ)` is a common
eigenfunction of `T(n)` with eigenvalues `a_n` for all `n` prime to `N`, then there are a divisor
`M` of `N` with `m_χ ∣ M` (`χ` is induced by a character `χ_M` modulo `M`) and a primitive form
`g ∈ 𝒮_k^0(M, χ_M)` with `g ∣ T(n) = a_n g` for all `n` prime to `N`. -/
@[kb "miyake1989" "Corollary 4.6.14, p. 165 (existence)"]
theorem exists_isPrimitive_of_eigen (k : ℤ) (χ : DirichletCharacter ℂ N) {f : cuspSpace k χ}
    (hf0 : f ≠ 0) (a : ℕ → ℂ) (h : ∀ n : ℕ, n ≠ 0 → n.Coprime N → heckeT k χ n f = a n • f) :
    ∃ (M : ℕ) (_ : NeZero M) (hM : M ∣ N) (χM : DirichletCharacter ℂ M) (g : cuspSpace k χM),
      χM.changeLevel hM = χ ∧ IsPrimitive g ∧
        ∀ n : ℕ, n ≠ 0 → n.Coprime N → heckeT k χM n g = a n • g := by
  obtain ⟨M, hMne, hM, G, hGχ, hGev⟩ :=
    HeckeRing.GL2.Newform.exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul
      (k := k) (χ := χ.toUnitHom) (F := (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) f.2
      (fun h0 ↦ hf0 (Subtype.ext h0)) (a := fun p _ _ ↦ a p) (fun p hp hpN ↦ by
        rw [← HeckeRing.GL2.coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k χ.toUnitHom hp f,
          ← HeckeRing.GL2.heckeTCompositeGamma0_prime N hp]
        exact congrArg Subtype.val (h p hp.ne_zero hpN))
  obtain ⟨χM, hχM⟩ : ∃ χM : DirichletCharacter ℂ M, χM.toUnitHom = G.χ :=
    ⟨MulChar.ofUnitHom G.χ, MulChar.equivToUnitHom.apply_symm_apply G.χ⟩
  have hmem : G.toCuspForm ∈ TauCeti.cuspFormCharSpace k χM.toUnitHom := by
    rw [hχM]; exact G.mem_charSpace
  have hlev : χM.changeLevel hM = χ := by
    refine (DirichletCharacter.toUnitHom_inj _ _).1 ?_
    rw [DirichletCharacter.changeLevel_toUnitHom, hχM]
    exact hGχ
  have hprim : IsPrimitive (⟨G.toCuspForm, hmem⟩ : cuspSpace k χM) :=
    (isPrimitive_iff_exists_newform _).2 ⟨G, hχM.symm, rfl⟩
  refine ⟨M, hMne, hM, χM, ⟨G.toCuspForm, hmem⟩, hlev, hprim, ?_⟩
  set g' : cuspSpace k χM := ⟨G.toCuspForm, hmem⟩ with hg'
  have hg'ne := ne_zero_of_isPrimitive hprim
  have hb : ∀ n : ℕ, n ≠ 0 → n.Coprime M → heckeT k χM n g' = coeff g' n • g' :=
    fun n hn _ ↦ heckeT_eq_of_newform G hχM.symm g' rfl hn
  have hχp : ∀ p : ℕ, p.Coprime N → χM (p : ZMod M) = χ (p : ZMod N) := by
    intro p hp
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd' χM hM (a := (p : ℤ))
      (Nat.isCoprime_iff_coprime.mpr hp)
    rw [hlev] at this
    simpa using this.symm
  have hseq := seq_eq_of_rec (N := N) (fun p ↦ χ p * (p : ℂ) ^ (k - 1)) (a := a)
    (b := fun n ↦ coeff g' n) (eigen_one hf0 h) (eigen_one hg'ne hb)
    (fun x y hx hy hxy hxN hyN ↦ eigen_mul hf0 h hx hy hxy hxN hyN)
    (fun x y hx hy hxy hxN hyN ↦ eigen_mul hg'ne hb hx hy hxy (hxN.coprime_dvd_right hM)
      (hyN.coprime_dvd_right hM))
    (fun p hp hpN r ↦ eigen_rec hf0 h hp hpN r)
    (fun p hp hpN r ↦ by
      rw [eigen_rec hg'ne hb hp (hpN.coprime_dvd_right hM) r, hχp p hpN])
    (fun p hp hpN ↦ by
      have h1 := hb p hp.ne_zero (hpN.coprime_dvd_right hM)
      have h2 := hGev p hp hpN
      have h3 : coeff g' p = G.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hM) :=
        HeckeRing.GL2.Newform.qExpansion_coeff_eq_eigenvalue G ⟨p, hp.pos⟩ _
      rw [h3, h2])
  intro n hn hnN
  have e : coeff g' n = a n := (hseq n hn hnN).symm
  rw [hb n hn (hnN.coprime_dvd_right hM), e]

/-- **Miyake, Theorem 4.6.19** for two primitive forms: let `f = Σ a_n qⁿ` and `g = Σ b_n qⁿ` be
primitive forms of `𝒮_k^0(N, χ)` and `𝒮_k^0(M, ψ)`, where `χ` and `ψ` induce the same character
modulo `lcm(N, M)`. If `a_n = b_n` for all `n` prime to some integer `L ≥ 1`, then `N = M` and
`f = g` as functions on `ℍ`. (Miyake allows `g` to be any common eigenfunction of `ℛ(M) ∪ ℛ*(M)`
with `b_1 = 1`; that generality is not covered here.) -/
@[kb "miyake1989" "Theorem 4.6.19, p. 173 (g primitive)"]
theorem eq_of_isPrimitive {M : ℕ} [NeZero M] {k : ℤ} {χ : DirichletCharacter ℂ N}
    {ψ : DirichletCharacter ℂ M}
    (hχψ : χ.changeLevel (Nat.dvd_lcm_left N M) = ψ.changeLevel (Nat.dvd_lcm_right N M))
    {f : cuspSpace k χ} {g : cuspSpace k ψ} (hf : IsPrimitive f) (hg : IsPrimitive g) {L : ℕ}
    (hL : L ≠ 0) (h : ∀ n : ℕ, n.Coprime L → coeff f n = coeff g n) :
    N = M ∧ ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ⇑(g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) := by
  obtain ⟨F, hFχ, hF⟩ := (isPrimitive_iff_exists_newform f).1 hf
  obtain ⟨G, hGχ, hG⟩ := (isPrimitive_iff_exists_newform g).1 hg
  have hχ : F.χ.comp (ZMod.unitsMap (Nat.dvd_lcm_left N M)) =
      G.χ.comp (ZMod.unitsMap (Nat.dvd_lcm_right N M)) := by
    rw [hFχ, hGχ, ← DirichletCharacter.changeLevel_toUnitHom, ←
      DirichletCharacter.changeLevel_toUnitHom, hχψ]
  obtain ⟨h1, h2⟩ := HeckeRing.GL2.Newform.level_eq_and_coe_eq_of_forall_notMem_prime_eigenvalue_eq
    F G hχ (S := L.primeFactors) (fun p hp hpN hpM hpS ↦ by
      have hpL : p.Coprime L := by
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hd
        exact hpS (Nat.mem_primeFactors.2 ⟨hp, hd, hL⟩)
      rw [← HeckeRing.GL2.Newform.qExpansion_coeff_eq_eigenvalue F ⟨p, hp.pos⟩ hpN,
        ← HeckeRing.GL2.Newform.qExpansion_coeff_eq_eigenvalue G ⟨p, hp.pos⟩ hpM, hF, hG]
      exact h p hpL)
  refine ⟨h1, ?_⟩
  rw [← hF, ← hG]
  exact h2

/-- **Miyake, Corollary 4.6.20** (existence and uniqueness of the primitive form): if a nonzero
`f ∈ 𝒮_k(N, χ)` satisfies `f ∣ T(n) = a_n f` for all `n` prime to `N`, there is a unique pair of
a divisor `M` of `N` with `m_χ ∣ M` and a primitive form `g` of `𝒮_k^0(M, χ)` with
`g ∣ T(n) = a_n g` for all `n` prime to `N`: any two such `g` have the same level and are equal
as functions. (Miyake's further assertion `f ∈ ⊕_{l ∣ N/M} ℂ g(lz)` is not covered.) -/
@[kb "miyake1989" "Corollary 4.6.20, p. 175 (existence and uniqueness of g)"]
theorem isPrimitive_unique_of_eigen (k : ℤ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ)
    {M M' : ℕ} [NeZero M] [NeZero M'] (hM : M ∣ N) (hM' : M' ∣ N)
    {χM : DirichletCharacter ℂ M} {χM' : DirichletCharacter ℂ M'}
    (hχM : χM.changeLevel hM = χ) (hχM' : χM'.changeLevel hM' = χ)
    {g : cuspSpace k χM} {g' : cuspSpace k χM'} (hg : IsPrimitive g) (hg' : IsPrimitive g')
    (h : ∀ n : ℕ, n ≠ 0 → n.Coprime N → heckeT k χM n g = a n • g)
    (h' : ∀ n : ℕ, n ≠ 0 → n.Coprime N → heckeT k χM' n g' = a n • g') :
    M = M' ∧ ⇑(g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) =
      ⇑(g' : CuspForm ((Gamma1 M').map (mapGL ℝ)) k) := by
  obtain ⟨G, hGχ, hG⟩ := (isPrimitive_iff_exists_newform g).1 hg
  obtain ⟨G', hG'χ, hG'⟩ := (isPrimitive_iff_exists_newform g').1 hg'
  have hcoef : ∀ p : ℕ, p.Prime → p.Coprime N → coeff g p = a p := fun p hp hpN ↦
    smul_left_injective ℂ (ne_zero_of_isPrimitive hg)
      ((heckeT_eq_of_newform G hGχ g hG hp.ne_zero).symm.trans (h p hp.ne_zero hpN))
  have hcoef' : ∀ p : ℕ, p.Prime → p.Coprime N → coeff g' p = a p := fun p hp hpN ↦
    smul_left_injective ℂ (ne_zero_of_isPrimitive hg')
      ((heckeT_eq_of_newform G' hG'χ g' hG' hp.ne_zero).symm.trans (h' p hp.ne_zero hpN))
  obtain ⟨h1, h2⟩ := HeckeRing.GL2.Newform.level_eq_and_coe_eq_of_comp_unitsMap_eq G G' hM hM'
    (χ := χ.toUnitHom)
    (by rw [hGχ, ← DirichletCharacter.changeLevel_toUnitHom, hχM])
    (by rw [hG'χ, ← DirichletCharacter.changeLevel_toUnitHom, hχM'])
    (S := ∅) (fun p hp hpN _ ↦ by
      rw [← HeckeRing.GL2.Newform.qExpansion_coeff_eq_eigenvalue G ⟨p, hp.pos⟩
          (hpN.coprime_dvd_right hM),
        ← HeckeRing.GL2.Newform.qExpansion_coeff_eq_eigenvalue G' ⟨p, hp.pos⟩
          (hpN.coprime_dvd_right hM'), hG, hG']
      exact (hcoef p hp hpN).trans (hcoef' p hp hpN).symm)
  refine ⟨h1, ?_⟩
  rw [← hG, ← hG']
  exact h2

end ModularFormsKB.Miyake.Wave4
