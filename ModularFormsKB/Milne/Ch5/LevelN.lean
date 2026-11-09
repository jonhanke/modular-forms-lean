import ModularFormsKB.Milne.Ch5.HeckeAlgebra
import ModularFormsKB.Milne.Ch5.EulerFactor
import TauCeti.NumberTheory.ModularForms.HeckeSlash.ModularForm
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.LinearAlgebra.Eigenspace.Basic
import TauCeti.NumberTheory.ModularForms.Petersson.FiniteIndex
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.NumberTheory.HeckeRing.Multiplicity.Equiv

/-!
# Milne, Chapter 5: Hecke operators for $\Gamma(N)$ (Lemmas 5.33, 5.34, Proposition 5.35, Theorem 5.36,
Proposition 5.37)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf pp. 83–85.

Milne takes $\Delta(N)$ to be the integer matrices $\alpha$ with $n = \det\alpha > 0$ prime to $N$ and
$\alpha \equiv \begin{pmatrix} 1 & 0 \\ 0 & n \end{pmatrix} \bmod N$ (`DeltaN`), and $\Delta_0(N)$ the integer
matrices of positive determinant prime to $N$ (here `DeltaPrime`, to avoid a clash with Tau Ceti's
`HeckeRing.GL2.Delta0`). The Hecke algebras are Tau Ceti's `HeckeCosetModule`s with their convolution product, and a
double coset acts on $M_k(\Gamma(N))$ by Milne's rule (9), $[\alpha] f = \det(\alpha)^{k-1}\sum f|_k\alpha_i$, which is
Tau Ceti's slash sum `HeckeRing.GL2.heckeSlashModularFormEnd` in Mathlib's normalization (`heckeActN`).

Milne proves none of Lemmas 5.33, 5.34, Theorem 5.36, Proposition 5.37 (he refers to Ogg 1969), and proves
Proposition 5.35 by "essentially the same" argument as Proposition 5.1. They are stated here as named statements
(`HeckeLevelIso`, `DiamondCommutesHecke`, `EulerProductLevelN`, `EulerProductLevelNt`, `PeterssonHeckeLevelN`); what
follows from them is proved.

**Fourier expansions.** A form for $\Gamma(N)$ has period $N$, so Milne's expansion $f = \sum a_nq^n$ in 5.35–5.37 is
read with $q = q_N = e^{2\pi iz/N}$ (`qExpansion N f`); for $f$ of period $1$ it is the usual expansion.

## Items
- $\Delta(N)$, $\Delta_0(N)$ (`DeltaN`, `DeltaPrime`), the Hecke algebras $H(\Gamma(N), \Delta(N))$,
  $H(\Gamma(1), \Delta_0(N))$ and the map of Lemma 5.33 (`heckeLevelMap`); Lemma 5.33 (`HeckeLevelIso`).
- $T^N(a, d)$, $T^N(n)$ (`heckeTNDiag`, `heckeTN`), the action (9) (`heckeActN`), the operators $R_d$ (`diamondN`),
  the spaces $V(\varepsilon)$ (`charSpaceN`); Lemma 5.34 (`DiamondCommutesHecke`, `heckeActN_mem_charSpaceN`).
- Proposition 5.35 (`EulerProductLevelN`).
- The operators $U$, $T^t(m)$, $T^t(n)$ and the spaces $V(\zeta)$, $V(t)$, p. 84 (`translateOne`, `rootSpaceN`,
  `tSpaceN`, `heckeTtPrimeToLevel`); Theorem 5.36 (`EulerProductLevelNt`).
- Proposition 5.37 (`PeterssonHeckeLevelN`).
-/

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing HeckeRing.GLn HeckeRing.GL2
  DoubleCoset

open scoped MatrixGroups ModularForm Pointwise HeckeCosetModule

namespace ModularFormsKB.Milne

variable (N : ℕ)

/-- **$\Delta(N)$** (p. 83): integer matrices $\alpha$ with $n = \det\alpha > 0$ prime to $N$ and
$\alpha \equiv \begin{pmatrix} 1 & 0 \\ 0 & n\end{pmatrix} \bmod N$. -/
@[kb "milne2017mf" "Section 5, the monoid Delta(N) (pdf p. 83)"]
noncomputable def DeltaN : Submonoid (GL (Fin 2) ℚ) where
  carrier := {g | ∃ A : Matrix (Fin 2) (Fin 2) ℤ,
    (↑g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) ∧ 0 < A.det ∧ IsCoprime A.det N ∧
      A.map (Int.cast : ℤ → ZMod N) = !![1, 0; 0, (A.det : ZMod N)]}
  one_mem' := by
    refine ⟨1, by simp, by simp, by simpa using isCoprime_one_left, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  mul_mem' := by
    rintro a b ⟨A, hA, hdA, hcA, hmA⟩ ⟨B, hB, hdB, hcB, hmB⟩
    refine ⟨A * B, ?_, ?_, ?_, ?_⟩
    · ext i j
      simp [hA, hB, Matrix.mul_apply, Matrix.map_apply]
    · rw [Matrix.det_mul]; exact mul_pos hdA hdB
    · rw [Matrix.det_mul]; exact hcA.mul_left hcB
    · have h : (A * B).map (Int.cast : ℤ → ZMod N) =
          A.map (Int.cast : ℤ → ZMod N) * B.map (Int.cast : ℤ → ZMod N) :=
        Matrix.map_mul (f := Int.castRingHom (ZMod N))
      rw [h, hmA, hmB]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.det_mul]

/-- **$\Delta_0(N)$** of Lemma 5.33 (p. 83): integer matrices of positive determinant prime to $N$. -/
@[kb "milne2017mf" "Section 5, Lemma 5.33, the monoid Delta_0(N) (pdf p. 83)"]
noncomputable def DeltaPrime : Submonoid (GL (Fin 2) ℚ) where
  carrier := {g | ∃ A : Matrix (Fin 2) (Fin 2) ℤ,
    (↑g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) ∧ 0 < A.det ∧ IsCoprime A.det N}
  one_mem' := ⟨1, by simp, by simp, by simpa using isCoprime_one_left⟩
  mul_mem' := by
    rintro a b ⟨A, hA, hdA, hcA⟩ ⟨B, hB, hdB, hcB⟩
    refine ⟨A * B, ?_, ?_, ?_⟩
    · ext i j
      simp [hA, hB, Matrix.mul_apply, Matrix.map_apply]
    · rw [Matrix.det_mul]; exact mul_pos hdA hdB
    · rw [Matrix.det_mul]; exact hcA.mul_left hcB

theorem DeltaN_le_DeltaPrime : DeltaN N ≤ DeltaPrime N := by
  rintro g ⟨A, hA, hd, hc, -⟩
  exact ⟨A, hA, hd, hc⟩

/-- `Δ₀(N)` consists of integral matrices of positive determinant. -/
theorem DeltaPrime_le_posDetInt : DeltaPrime N ≤ posDetInt 2 := by
  intro g hg
  obtain ⟨A, hA, hdet, -⟩ := hg
  refine (mem_posDetInt_iff 2).mpr ⟨(hasIntEntries_iff 2).mpr ⟨A, hA⟩, ?_⟩
  rw [hA]
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.det_fin_two, Matrix.map_apply]
  exact_mod_cast hdet

instance isHeckeTriple_DeltaN [NeZero N] :
    IsHeckeTriple (DeltaN N) ((Gamma N).map (mapGL ℚ)) ((Gamma N).map (mapGL ℚ)) := by
  refine IsHeckeTriple.of_diagonal ?_ ?_
  · rintro g hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
    refine ⟨γ, ?_, ?_, ?_, ?_⟩
    · ext i j; simp [mapGL_coe_matrix]
    · simp
    · simpa using isCoprime_one_left
    · have h := Gamma_mem'.mp hγ
      have h2 : (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) = 1 := by
        simpa using congrArg (fun x : SL(2, ZMod N) => (x : Matrix (Fin 2) (Fin 2) (ZMod N))) h
      rw [h2]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  · rw [Subgroup.Commensurable.eq (commensurable_map_SLnZ 2 (Gamma N))]
    exact ((DeltaN_le_DeltaPrime N).trans (DeltaPrime_le_posDetInt N)).trans
      (posDetInt_le_commensurator 2)

instance isHeckeTriple_DeltaPrime : IsHeckeTriple (DeltaPrime N) (SLnZ 2) (SLnZ 2) := by
  refine IsHeckeTriple.of_diagonal ?_ ((DeltaPrime_le_posDetInt N).trans (posDetInt_le_commensurator 2))
  intro g hg
  obtain ⟨σ, rfl⟩ := (mem_SLnZ_iff 2).mp hg
  refine ⟨σ, ?_, ?_, ?_⟩
  · ext i j; simp [mapGL_coe_matrix]
  · simp
  · simpa using isCoprime_one_left

/-- The map on double cosets of Lemma 5.33: $\Gamma(N)\alpha\Gamma(N) \mapsto \Gamma(1)\alpha\Gamma(1)$. -/
noncomputable def toLevelOneCosetN (D : HeckeCoset (DeltaN N) ((Gamma N).map (mapGL ℚ)) ((Gamma N).map (mapGL ℚ))) :
    HeckeCoset (DeltaPrime N) (SLnZ 2) (SLnZ 2) :=
  HeckeCoset.mk _ _ ⟨D.rep, DeltaN_le_DeltaPrime N D.rep.2⟩

/-- The map of Lemma 5.33, $H(\Gamma(N), \Delta(N)) \to H(\Gamma(1), \Delta_0(N))$, extended linearly. -/
noncomputable def heckeLevelMap :
    𝕋 (DeltaN N) ((Gamma N).map (mapGL ℚ)) ℤ →ₗ[ℤ] 𝕋 (DeltaPrime N) (SLnZ 2) ℤ :=
  Finsupp.lmapDomain ℤ ℤ (toLevelOneCosetN N)

/-- **Milne, Lemma 5.33** (named statement; Milne: "Elementary. (See Ogg 1969, p. IV-10.)"). The map
$\Gamma(N)\alpha\Gamma(N) \mapsto \Gamma(1)\alpha\Gamma(1)$ is an isomorphism of rings
$H(\Gamma(N), \Delta(N)) \to H(\Gamma(1), \Delta_0(N))$. -/
@[kb "milne2017mf" "Section 5, Lemma 5.33 (pdf p. 83); Ogg 1969, p. IV-10 [unverified]"]
structure HeckeLevelIso [NeZero N] : Prop where
  bijective : Function.Bijective (heckeLevelMap N)
  map_mul : ∀ x y, heckeLevelMap N (x * y) = heckeLevelMap N x * heckeLevelMap N y

/-- **$T^N(a, d)$** (p. 83): the double coset $\Gamma(N)\alpha\Gamma(N)$, $\alpha \in \Delta(N)$, lying over
$T(a, d) = \Gamma(1)\begin{pmatrix} a & 0 \\ 0 & d\end{pmatrix}\Gamma(1)$ (under Lemma 5.33 there is exactly one); $0$
if there is none (when $ad$ is not prime to $N$). -/
@[kb "milne2017mf" "Section 5, the elements T^N(a, d) and T^N(n) (pdf p. 83)"]
noncomputable def heckeTNDiag [NeZero N] (a d : ℕ) : 𝕋 (DeltaN N) ((Gamma N).map (mapGL ℚ)) ℤ :=
  haveI := Classical.propDecidable
  if h : ∃ α : DeltaN N, α.1 ∈ doubleCoset (natDiagGL 2 ![a, d]) (SLnZ 2 : Set _) (SLnZ 2) then
    HeckeCosetModule.single ℤ (HeckeCoset.mk _ _ h.choose) 1
  else 0

/-- **$T^N(n) = \sum_{a \mid d,\, ad = n} T^N(a, d)$** (p. 83). -/
@[kb "milne2017mf" "Section 5, the elements T^N(a, d) and T^N(n) (pdf p. 83)"]
noncomputable def heckeTN [NeZero N] (n : ℕ) : 𝕋 (DeltaN N) ((Gamma N).map (mapGL ℚ)) ℤ :=
  ∑ ad ∈ n.divisorsAntidiagonal.filter (fun ad ↦ ad.1 ∣ ad.2), heckeTNDiag N ad.1 ad.2

/-- $\mathrm{diag}(a, d) \in \Delta_0(N)$ for $a, d \ge 1$ with $ad$ prime to $N$. -/
theorem natDiagGL_mem_DeltaPrime {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (hcop : (a * d).Coprime N) :
    natDiagGL 2 ![a, d] ∈ DeltaPrime N := by
  have ha' : ∀ i, 0 < (![a, d] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simpa
  refine ⟨Matrix.diagonal (fun i ↦ ((![a, d] : Fin 2 → ℕ) i : ℤ)), ?_, ?_, ?_⟩
  · rw [natDiagGL_coe 2 _ ha']
    ext i j
    simp [Matrix.diagonal, Matrix.map_apply, apply_ite (Int.cast : ℤ → ℚ)]
  · rw [Matrix.det_diagonal]
    simp [Fin.prod_univ_two]
    positivity
  · rw [Matrix.det_diagonal]
    simpa [Fin.prod_univ_two] using (Nat.isCoprime_iff_coprime.mpr hcop)

/-- $T(a, d) = \Gamma(1)\,\mathrm{diag}(a, d)\,\Gamma(1)$ as a double coset of $\Delta_0(N)$. -/
noncomputable def levelOneDiagCoset {a d : ℕ} (h : natDiagGL 2 ![a, d] ∈ DeltaPrime N) :
    HeckeCoset (DeltaPrime N) (SLnZ 2) (SLnZ 2) :=
  HeckeCoset.mk _ _ ⟨natDiagGL 2 ![a, d], h⟩

/-- Level-`N` elements with a given `Γ(1)`-double coset have the same image under `toLevelOneCosetN`. -/
theorem toLevelOneCosetN_eq_of_mem [NeZero N] (α : DeltaN N) {a d : ℕ}
    (h : natDiagGL 2 ![a, d] ∈ DeltaPrime N)
    (hα : α.1 ∈ doubleCoset (natDiagGL 2 ![a, d]) (SLnZ 2 : Set _) (SLnZ 2)) :
    toLevelOneCosetN N (HeckeCoset.mk _ _ α) = levelOneDiagCoset N h := by
  unfold toLevelOneCosetN levelOneDiagCoset
  apply HeckeCoset.mk_eq_mk_of_mem
  have hΓ : (Gamma N).map (mapGL ℚ) ≤ SLnZ 2 := by
    rintro _ ⟨γ, -, rfl⟩
    exact coe_mem_SLnZ 2 γ
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_doubleCoset.mp (HeckeCoset.rep_mk_mem_doubleCoset α)
  obtain ⟨p, hp, q, hq, hpq⟩ := mem_doubleCoset.mp hα
  refine mem_doubleCoset.mpr ⟨x * p, mul_mem (hΓ hx) hp, q * y, mul_mem hq (hΓ hy), ?_⟩
  show (((HeckeCoset.mk _ _ α).rep : DeltaN N) : GL (Fin 2) ℚ) = x * p * natDiagGL 2 ![a, d] * (q * y)
  rw [hxy, hpq]; group

/-- Lifting `diag(d⁻¹, d)` from `SL₂(ℤ/N)` to `SL₂(ℤ)` (strong approximation). -/
theorem exists_sl_diag_rep (d : (ZMod N)ˣ) :
    ∃ σ : SL(2, ℤ), (σ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) =
      !![((d⁻¹ : (ZMod N)ˣ) : ZMod N), 0; 0, (d : ZMod N)] := by
  let g : SL(2, ZMod N) := ⟨!![((d⁻¹ : (ZMod N)ˣ) : ZMod N), 0; 0, (d : ZMod N)], by
    simp [Matrix.det_fin_two]⟩
  obtain ⟨σ, hσ⟩ := Matrix.SpecialLinearGroup.map_intCast_zmod_surjective (d := N) g
  refine ⟨σ, ?_⟩
  have := congrArg (fun x : SL(2, ZMod N) => (x : Matrix (Fin 2) (Fin 2) (ZMod N))) hσ
  simpa [g] using this

/-- A witness in `Δ(N)` over `diag(a, d)`: `σ · diag(a, d)` with `σ ≡ diag(a⁻¹, a) mod N`. -/
theorem exists_DeltaN_mem_diag [NeZero N] {a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (hcop : (a * d).Coprime N) :
    ∃ α : DeltaN N, α.1 ∈ doubleCoset (natDiagGL 2 ![a, d]) (SLnZ 2 : Set _) (SLnZ 2) := by
  have ha' : ∀ i, 0 < (![a, d] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simpa
  have hacop : a.Coprime N := (Nat.coprime_mul_iff_left.mp hcop).1
  obtain ⟨σ, hσ⟩ := exists_sl_diag_rep N (ZMod.unitOfCoprime a hacop)
  have hu : ((ZMod.unitOfCoprime a hacop : (ZMod N)ˣ) : ZMod N) = (a : ZMod N) :=
    ZMod.coe_unitOfCoprime a hacop
  have hinv : (((ZMod.unitOfCoprime a hacop)⁻¹ : (ZMod N)ˣ) : ZMod N) * (a : ZMod N) = 1 := by
    rw [← hu]; exact Units.inv_mul _
  let D : Matrix (Fin 2) (Fin 2) ℤ := Matrix.diagonal (fun i ↦ ((![a, d] : Fin 2 → ℕ) i : ℤ))
  have hDq : (↑(natDiagGL 2 ![a, d]) : Matrix (Fin 2) (Fin 2) ℚ) = D.map (Int.cast : ℤ → ℚ) :=
    natDiagGL_coe_eq_map_intCast 2 _ ha'
  have hdetD : D.det = ((a * d : ℕ) : ℤ) := by
    simp [D, Matrix.det_diagonal, Fin.prod_univ_two]
  have hdet : ((σ : Matrix (Fin 2) (Fin 2) ℤ) * D).det = ((a * d : ℕ) : ℤ) := by
    rw [Matrix.det_mul, σ.det_coe, one_mul, hdetD]
  refine ⟨⟨mapGL ℚ σ * natDiagGL 2 ![a, d], ⟨(σ : Matrix (Fin 2) (Fin 2) ℤ) * D, ?_, ?_, ?_, ?_⟩⟩, ?_⟩
  · rw [Units.val_mul, hDq, Matrix.map_mul_intCast]
    congr 1
  · rw [hdet]; exact_mod_cast Nat.mul_pos ha hd
  · rw [hdet]; exact Nat.isCoprime_iff_coprime.mpr hcop
  · rw [Matrix.map_mul_intCast, hσ, hdet]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, Matrix.mul_apply, Matrix.diagonal, hinv]
  · exact mem_doubleCoset.mpr ⟨mapGL ℚ σ, coe_mem_SLnZ 2 σ, 1, one_mem _, by simp⟩

/-- Under the map of Lemma 5.33, $T^N(a, d)$ goes to $T(a, d)$ (when $a \mid d$ and $(ad, N) = 1$). -/
theorem heckeLevelMap_heckeTNDiag [NeZero N] {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (had : a ∣ d)
    (hcop : (a * d).Coprime N) :
    heckeLevelMap N (heckeTNDiag N a d) =
      HeckeCosetModule.single ℤ (levelOneDiagCoset N (natDiagGL_mem_DeltaPrime N ha hd hcop)) 1 := by
  have _ := had
  have hex := exists_DeltaN_mem_diag N ha hd hcop
  have key := toLevelOneCosetN_eq_of_mem N hex.choose (natDiagGL_mem_DeltaPrime N ha hd hcop)
    hex.choose_spec
  have hmap : ∀ D, heckeLevelMap N (HeckeCosetModule.single ℤ D 1) =
      HeckeCosetModule.single ℤ (toLevelOneCosetN N D) 1 := fun D ↦
    (Finsupp.lmapDomain_apply _ _ (toLevelOneCosetN N) _).trans (Finsupp.mapDomain_single)
  unfold heckeTNDiag
  split_ifs
  rw [hmap]
  exact congrArg (fun D ↦ HeckeCosetModule.single ℤ D (1 : ℤ)) key

/-- The rep of a double coset of $\Delta(N)$ has positive determinant. -/
theorem rep_mem_GLPos_DeltaN [NeZero N]
    (D : HeckeCoset (DeltaN N) ((Gamma N).map (mapGL ℚ)) ((Gamma N).map (mapGL ℚ))) :
    (D.out : GL (Fin 2) ℚ) ∈ Matrix.GLPos (Fin 2) ℚ := by
  have h := ((mem_posDetInt_iff 2).mp
    ((DeltaN_le_DeltaPrime N).trans (DeltaPrime_le_posDetInt N) (D.out).2)).2
  exact (Matrix.mem_glpos _).mpr (by simpa using h)

/-- **The action (9)** of $H(\Gamma(N), \Delta(N))$ on $M_{2k}(\Gamma(N))$: $[\alpha] f = \det(\alpha)^{k-1}\sum f|_k\alpha_i$
over $\Gamma(N)\alpha\Gamma(N) = \bigsqcup\Gamma(N)\alpha_i$ (Tau Ceti's slash sum, which is $\sum f \mid_{2k} \alpha_i$ in
Mathlib's normalization), extended linearly. -/
@[kb "milne2017mf" "Section 5, the action (9) of the Hecke algebra on M_k(Gamma(N)) (pdf pp. 83-84)"]
noncomputable def heckeActN [NeZero N] (k : ℕ) :
    𝕋 (DeltaN N) ((Gamma N).map (mapGL ℚ)) ℤ →ₗ[ℤ] Module.End ℂ (ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)) :=
  Finsupp.linearCombination ℤ fun D ↦ heckeSlashModularFormEnd (2 * k) D (rep_mem_GLPos_DeltaN N D)

/-- A matrix $R_d \in \Gamma(1)$ with $R_d \equiv \begin{pmatrix} d^{-1} & 0 \\ 0 & d\end{pmatrix} \bmod N$ (p. 83). -/
theorem exists_diamondRep [NeZero N] (d : (ZMod N)ˣ) :
    ∃ σ : SL(2, ℤ), (σ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) =
      !![((d⁻¹ : (ZMod N)ˣ) : ZMod N), 0; 0, (d : ZMod N)] := by
  let g : SL(2, ZMod N) := ⟨!![((d⁻¹ : (ZMod N)ˣ) : ZMod N), 0; 0, (d : ZMod N)], by
    simp [Matrix.det_fin_two]⟩
  obtain ⟨σ, hσ⟩ := Matrix.SpecialLinearGroup.map_intCast_zmod_surjective (d := N) g
  refine ⟨σ, ?_⟩
  have := congrArg (fun x : SL(2, ZMod N) => (x : Matrix (Fin 2) (Fin 2) (ZMod N))) hσ
  simpa [g] using this

/-- $\Gamma(N)$ is normalized by $\Gamma(1)$, as subgroups of $\mathrm{GL}_2(\mathbb R)$. -/
theorem conj_Gamma_map (σ : SL(2, ℤ)) :
    ConjAct.toConjAct (mapGL ℝ σ)⁻¹ • (Gamma N).map (mapGL ℝ) = (Gamma N).map (mapGL ℝ) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨σ⁻¹ * y * σ⁻¹⁻¹, (Gamma_normal N).conj_mem y hy σ⁻¹, ?_⟩
    have : x = (mapGL ℝ σ)⁻¹ * (mapGL ℝ y) * mapGL ℝ σ := by
      rw [hxy]; group
    rw [this]
    simp
  · rintro ⟨y, hy, rfl⟩
    refine ⟨σ * y * σ⁻¹, (Gamma_normal N).conj_mem y hy σ, ?_⟩
    simp

/-- Pointwise formula for translation by `σ`, transported back to level `Γ(N)`. -/
theorem mcast_translate_apply_N [NeZero N] (k : ℕ) (σ : SL(2, ℤ))
    (f : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)) (z : ℍ) :
    (ModularForm.mcast rfl (ModularForm.translate f (mapGL ℝ σ)) (conj_Gamma_map N σ).symm) z =
      (⇑f ∣[(2 * k : ℤ)] mapGL ℝ σ) z :=
  (ModularForm.mcast_apply rfl (ModularForm.translate f (mapGL ℝ σ))
    (conj_Gamma_map N σ).symm z).trans (congr_fun (ModularForm.coe_translate f _) z)

/-- **The operator $R_d$** on $M_{2k}(\Gamma(N))$ (p. 84): $f \mapsto f \mid_{2k} R_d$; it does not depend on the choice
of $R_d$ because $\Gamma(N)$ acts trivially. -/
@[kb "milne2017mf" "Section 5, the operators R_d on M_k(Gamma(N)) (pdf pp. 83-84)"]
noncomputable def diamondN [NeZero N] (k : ℕ) (d : (ZMod N)ˣ) :
    Module.End ℂ (ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)) where
  toFun f := ModularForm.mcast rfl (ModularForm.translate f (mapGL ℝ (exists_diamondRep N d).choose))
    (conj_Gamma_map N _).symm
  map_add' f₁ f₂ := by
    ext z
    exact congr_fun (SlashAction.add_slash (2 * (k : ℤ))
      (mapGL ℝ (exists_diamondRep N d).choose) ⇑f₁ ⇑f₂) z
  map_smul' c f := by
    refine ModularForm.ext fun z ↦ ((mcast_translate_apply_N N k _ (c • f) z).trans ?_).trans
      (congrArg (fun w : ℂ ↦ c • w) (mcast_translate_apply_N N k _ f z)).symm
    rw [FunLike.coe_smul, ModularForm.smul_slash]
    simp

/-- **$V(\varepsilon) = M_k(\Gamma(N), \varepsilon)$** (p. 84): the $f$ with $f|_kR_d = \varepsilon(d)f$ for all
$d \in (\mathbb Z/N\mathbb Z)^\times$. -/
@[kb "milne2017mf" "Section 5, the spaces V(epsilon) = M_k(Gamma(N), epsilon) (pdf p. 84)"]
noncomputable def charSpaceN [NeZero N] (k : ℕ) (ε : (ZMod N)ˣ →* ℂˣ) :
    Submodule ℂ (ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)) :=
  ⨅ d, Module.End.eigenspace (diamondN N k d) (ε d)

/-- **Milne, Lemma 5.34** (named statement; Milne: "See Ogg 1969, p. IV-13"). The operators $R_n$ and $T^N(m)$ on
$M_k(\Gamma(N))$ commute for $(nm, N) = 1$. -/
@[kb "milne2017mf" "Section 5, Lemma 5.34 (pdf p. 84); Ogg 1969, p. IV-13 [unverified]"]
structure DiamondCommutesHecke [NeZero N] (k : ℕ) : Prop where
  comm : ∀ (d : (ZMod N)ˣ) (m : ℕ), m.Coprime N → Commute (diamondN N k d) (heckeActN N k (heckeTN N m))

/-- **Milne, Lemma 5.34**, consequence: $V(\varepsilon)$ is invariant under $T^N(m)$, $(m, N) = 1$. -/
@[kb "milne2017mf" "Section 5, Lemma 5.34 (pdf p. 84)"]
theorem heckeActN_mem_charSpaceN [NeZero N] {k : ℕ} (h : DiamondCommutesHecke N k) (ε : (ZMod N)ˣ →* ℂˣ)
    {m : ℕ} (hm : m.Coprime N) {f : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)} (hf : f ∈ charSpaceN N k ε) :
    heckeActN N k (heckeTN N m) f ∈ charSpaceN N k ε := by
  rw [charSpaceN, Submodule.mem_iInf] at hf ⊢
  intro d
  have hf' := Module.End.mem_eigenspace_iff.mp (hf d)
  refine Module.End.mem_eigenspace_iff.mpr ?_
  have hc := (h.comm d m hm).eq
  calc diamondN N k d (heckeActN N k (heckeTN N m) f)
      = (diamondN N k d * heckeActN N k (heckeTN N m)) f := rfl
    _ = (heckeActN N k (heckeTN N m) * diamondN N k d) f := by rw [hc]
    _ = heckeActN N k (heckeTN N m) (diamondN N k d f) := rfl
    _ = _ := by rw [hf', map_smul]

/-- The character $\varepsilon$ extended to $\mathbb N$ by $0$ on integers not prime to $N$, times $n^{2k-2}$: the
completely multiplicative sequence $d$ of the Euler factor $1 - a_pX + \varepsilon(p)p^{2k-1}X^2 = 1 - a_pX + p\,d(p)X^2$. -/
noncomputable def charWeight [NeZero N] (k : ℕ) (ε : (ZMod N)ˣ →* ℂˣ) (n : ℕ) : ℂ :=
  (MulChar.ofUnitHom ε : DirichletCharacter ℂ N) n * (n : ℂ) ^ (2 * k - 2)

/-- **Milne, Proposition 5.35** (named statement; Milne: "Essentially the same as the proof of Proposition 5.1").
If $f \in M_k(\Gamma(N), \varepsilon)$ is an eigenform of every $T^N(n)$, $(n, N) = 1$, with $a_1 = 1$, then
$L_N(f, s) = \sum_{(n,N) = 1} a_nn^{-s} = \prod_{p \nmid N}(1 - a_pp^{-s} + \varepsilon(p)p^{2k-1-2s})^{-1}$, as formal
Dirichlet series. Here $a_n$ are the coefficients in $q_N = e^{2\pi iz/N}$, and the coefficients prime to $N$ are
kept (the sequence is $0$ at $n$ not prime to $N$, which makes the Euler factors at $p \mid N$ equal to $1$). -/
@[kb "milne2017mf" "Section 5, Proposition 5.35 (pdf p. 84)"]
structure EulerProductLevelN [NeZero N] (k : ℕ) : Prop where
  euler : ∀ (ε : (ZMod N)ˣ →* ℂˣ) (f : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)), f ∈ charSpaceN N k ε →
    (∀ n : ℕ, 0 < n → n.Coprime N → ∃ c : ℂ, heckeActN N k (heckeTN N n) f = c • f) →
    (qExpansion N f).coeff 1 = 1 →
    Miyake.HasHeckeEulerProduct (fun n ↦ if n.Coprime N then (qExpansion N f).coeff n else 0) (charWeight N k ε)

/-- **The operator $U$** (p. 84): $f \mapsto f(z + 1)$ on $M_{2k}(\Gamma(N))$, i.e. slashing by
$\begin{pmatrix} 1 & 1 \\ 0 & 1\end{pmatrix}$, which normalizes $\Gamma(N)$. -/
@[kb "milne2017mf" "Section 5, the operator U (pdf p. 84)"]
noncomputable def translateOne [NeZero N] (k : ℕ) : Module.End ℂ (ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)) where
  toFun f := ModularForm.mcast rfl (ModularForm.translate f (mapGL ℝ ModularGroup.T)) (conj_Gamma_map N _).symm
  map_add' f₁ f₂ := by
    ext z
    exact congr_fun (SlashAction.add_slash (2 * (k : ℤ)) (mapGL ℝ ModularGroup.T) ⇑f₁ ⇑f₂) z
  map_smul' c f := by
    refine ModularForm.ext fun z ↦ ((mcast_translate_apply_N N k _ (c • f) z).trans ?_).trans
      (congrArg (fun w : ℂ ↦ c • w) (mcast_translate_apply_N N k _ f z)).symm
    rw [FunLike.coe_smul, ModularForm.smul_slash]
    simp

/-- **$V(\zeta)$** (p. 84): the $f$ with $f|_kU^m = \zeta^mf$, i.e. $f(z + 1) = \zeta f(z)$, for an $N$-th root of
unity $\zeta$. -/
@[kb "milne2017mf" "Section 5, the spaces V(zeta) (pdf p. 84)"]
noncomputable def rootSpaceN [NeZero N] (k : ℕ) (ζ : ℂ) : Submodule ℂ (ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)) :=
  Module.End.eigenspace (translateOne N k) ζ

/-- **$V(t) = \bigoplus V(\zeta)$** over the primitive $(N/t)$-th roots of unity $\zeta$, for $t \mid N$ (p. 84). -/
@[kb "milne2017mf" "Section 5, the spaces V(t) (pdf p. 84)"]
noncomputable def tSpaceN [NeZero N] (k : ℕ) (t : ℕ) : Submodule ℂ (ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)) :=
  ⨆ (ζ : ℂ) (_ : IsPrimitiveRoot ζ (N / t)), rootSpaceN N k ζ

/-- **$T^t(m)$** (p. 84) for $m$ divisible only by primes dividing $N$:
$T^t(m)f = m^{k-1}\sum_{0 \le b < m} f|_k\begin{pmatrix} 1 & bN/t \\ 0 & m\end{pmatrix}$, on functions; in Mathlib's
normalization $m^{k-1}f|_k\alpha = f \mid_{2k} \alpha$ for $\det\alpha = m$.
(The value at m = 0, where the matrix is singular, is set to 0; Milne's m is positive.) -/
@[kb "milne2017mf" "Section 5, the operators T^t(m) (pdf p. 84)"]
noncomputable def heckeTtBad (k t m : ℕ) (f : ℍ → ℂ) : ℍ → ℂ :=
  if hm : m = 0 then 0 else
  ∑ b ∈ Finset.range m, f ∣[(2 * k : ℤ)]
    (Matrix.GeneralLinearGroup.mkOfDetNeZero (!![1, (b * N / t : ℚ); 0, (m : ℚ)].map (Rat.cast : ℚ → ℝ))
      (by
        simp [Matrix.det_fin_two, hm]) : GL (Fin 2) ℝ)

/-- The action (9) of $H(\Gamma(N), \Delta(N))$ on functions on $\mathbb H$ (Tau Ceti's slash sums), used to compose
with the explicit operators $T^t(m)$, whose values need not be forms for $\Gamma(N)$. -/
noncomputable def heckeActNFun [NeZero N] (k : ℕ) (x : 𝕋 (DeltaN N) ((Gamma N).map (mapGL ℚ)) ℤ) (f : ℍ → ℂ) :
    ℍ → ℂ :=
  x.sum fun D c ↦ (c : ℂ) • heckeSlashSum (2 * k) D f

/-- **$T^t(n) = T(n')\,T^t(m)$** (p. 84), for $n = mn'$ with $(n', N) = 1$ and $m$ divisible only by primes dividing
$N$; the factor $m$ is $\gcd(n, N^n)$. -/
@[kb "milne2017mf" "Section 5, the operators T^t(n) (pdf p. 84)"]
noncomputable def heckeTt [NeZero N] (k t n : ℕ) (f : ℍ → ℂ) : ℍ → ℂ :=
  heckeActNFun N k (heckeTN N (n / Nat.gcd n (N ^ n))) (heckeTtBad N k t (Nat.gcd n (N ^ n)) f)

/-- The inclusion $H(\Gamma(1), \Delta_0(N)) \subseteq H(\Gamma(1), \Delta)$ on double cosets. -/
noncomputable def inclCoset :
    HeckeCoset (DeltaPrime N) (SLnZ 2) (SLnZ 2) → HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2) :=
  HeckeCoset.map (DeltaPrime_le_posDetInt N) le_rfl le_rfl

theorem inclCoset_mk (g : DeltaPrime N) :
    inclCoset N (HeckeCoset.mk _ _ g) =
      HeckeCoset.mk _ _ (⟨g.1, DeltaPrime_le_posDetInt N g.2⟩ : posDetInt 2) := rfl

theorem inclCoset_toSet (D : HeckeCoset (DeltaPrime N) (SLnZ 2) (SLnZ 2)) :
    (inclCoset N D).toSet = D.toSet := by
  induction D using HeckeCoset.induction with | h g => rfl

theorem inclCoset_injective : Function.Injective (inclCoset N) := fun _ _ h ↦
  HeckeCoset.toSet_injective (by rw [← inclCoset_toSet, ← inclCoset_toSet, h])

theorem inclCoset_rep_mem (D : HeckeCoset (DeltaPrime N) (SLnZ 2) (SLnZ 2)) :
    ((inclCoset N D).rep : GL (Fin 2) ℚ) ∈
      doubleCoset (D.rep : GL (Fin 2) ℚ) (SLnZ 2 : Set _) (SLnZ 2) := by
  have := HeckeCoset.rep_mem (inclCoset N D)
  rwa [inclCoset_toSet, HeckeCoset.toSet_eq_doubleCoset_rep] at this

/-- The linear map $H(\Gamma(1), \Delta_0(N)) \to H(\Gamma(1), \Delta)$ induced by `inclCoset`. -/
noncomputable def inclHecke : 𝕋 (DeltaPrime N) (SLnZ 2) ℤ →ₗ[ℤ] IntegralHeckeRing 2 :=
  Finsupp.lmapDomain ℤ ℤ (inclCoset N)

theorem inclHecke_single (D : HeckeCoset (DeltaPrime N) (SLnZ 2) (SLnZ 2)) (c : ℤ) :
    inclHecke N (HeckeCosetModule.single ℤ D c) = HeckeCosetModule.single ℤ (inclCoset N D) c :=
  (Finsupp.lmapDomain_apply _ _ (inclCoset N) _).trans Finsupp.mapDomain_single

theorem inclHecke_apply (x : 𝕋 (DeltaPrime N) (SLnZ 2) ℤ)
    (D : HeckeCoset (DeltaPrime N) (SLnZ 2) (SLnZ 2)) :
    inclHecke N x (inclCoset N D) = x D :=
  (congrArg (fun f ↦ f (inclCoset N D)) (Finsupp.lmapDomain_apply _ _ (inclCoset N) x)).trans
    (Finsupp.mapDomain_apply_of_injective (inclCoset_injective N) x D)

theorem inclHecke_apply_of_notMem (x : 𝕋 (DeltaPrime N) (SLnZ 2) ℤ)
    {D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2)} (hD : D ∉ Set.range (inclCoset N)) :
    inclHecke N x D = 0 :=
  (congrArg (fun f ↦ f D) (Finsupp.lmapDomain_apply _ _ (inclCoset N) x)).trans
    (Finsupp.mapDomain_of_notMem_range x D hD)

theorem inclHecke_injective : Function.Injective (inclHecke N) := fun x y h ↦
  Finsupp.mapDomain_injective (inclCoset_injective N)
    ((Finsupp.lmapDomain_apply _ _ (inclCoset N) x).symm.trans
      (h.trans (Finsupp.lmapDomain_apply _ _ (inclCoset N) y)))

/-- Elements of the `Γ(1)`-double coset of an element of `Δ₀(N)` lie in `Δ₀(N)`. -/
theorem mem_DeltaPrime_of_mem_doubleCoset (g : DeltaPrime N) {g' : GL (Fin 2) ℚ}
    (h : g' ∈ doubleCoset (g : GL (Fin 2) ℚ) (SLnZ 2 : Set _) (SLnZ 2)) : g' ∈ DeltaPrime N := by
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_doubleCoset.mp h
  rw [hxy]
  exact mul_mem (mul_mem (IsHeckeTriple.mem_of_mem_left (SLnZ 2) hx) g.2)
    (IsHeckeTriple.mem_of_mem_right (SLnZ 2) hy)

/-- Shimura's multiplicity for `Γ(1)` and `Δ` depends on its first input only through its double
coset (by the commutativity of the Hecke ring). -/
theorem multiplicity_congr_first_SLnZ {g g' h d : GL (Fin 2) ℚ} (hg : g ∈ posDetInt 2)
    (hg' : g' ∈ posDetInt 2) (hh : h ∈ posDetInt 2) (hd : d ∈ posDetInt 2)
    (hgg : g' ∈ doubleCoset g (SLnZ 2 : Set _) (SLnZ 2)) :
    multiplicity (SLnZ 2) (SLnZ 2) (SLnZ 2) g' h d = multiplicity (SLnZ 2) (SLnZ 2) (SLnZ 2) g h d := by
  have hc := fun x y z : posDetInt 2 ↦ (transposeAntiInvolution 2).multiplicity_comm
    (transposeAntiInvolution_onHeckeCoset_eq_self 2) x y z
  calc multiplicity (SLnZ 2) (SLnZ 2) (SLnZ 2) g' h d
      = multiplicity (SLnZ 2) (SLnZ 2) (SLnZ 2) h g' d := hc ⟨g', hg'⟩ ⟨h, hh⟩ ⟨d, hd⟩
    _ = multiplicity (SLnZ 2) (SLnZ 2) (SLnZ 2) h g d :=
        multiplicity_doubleCoset_congr_second _ _ _ h d hgg
    _ = _ := (hc ⟨g, hg⟩ ⟨h, hh⟩ ⟨d, hd⟩).symm

/-- The inclusion `H(Γ(1), Δ₀(N)) → H(Γ(1), Δ)` respects structure constants. -/
theorem inclHecke_structureConstants (g₁ g₂ : DeltaPrime N) (g₁' g₂' : posDetInt 2)
    (h₁ : (g₁' : GL (Fin 2) ℚ) ∈ doubleCoset (g₁ : GL (Fin 2) ℚ) (SLnZ 2 : Set _) (SLnZ 2))
    (h₂ : (g₂' : GL (Fin 2) ℚ) ∈ doubleCoset (g₂ : GL (Fin 2) ℚ) (SLnZ 2 : Set _) (SLnZ 2)) :
    inclHecke N (HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2) g₁ g₂) =
      HeckeCosetModule.structureConstants ℤ (SLnZ 2) (SLnZ 2) (SLnZ 2) g₁' g₂' := by
  classical
  have hg₁' := mem_DeltaPrime_of_mem_doubleCoset N g₁ h₁
  have hg₂' := mem_DeltaPrime_of_mem_doubleCoset N g₂ h₂
  ext D'
  by_cases hD : D' ∈ Set.range (inclCoset N)
  · obtain ⟨D, rfl⟩ := hD
    rw [inclHecke_apply, HeckeCosetModule.structureConstants_apply,
      HeckeCosetModule.structureConstants_apply]
    congr 1
    have hrep := inclCoset_rep_mem N D
    have hDrep : (D.rep : GL (Fin 2) ℚ) ∈ posDetInt 2 := DeltaPrime_le_posDetInt N D.rep.2
    rw [multiplicity_doubleCoset_congr _ _ hrep,
      multiplicity_doubleCoset_congr_second _ _ _ (g₁' : GL (Fin 2) ℚ) _ h₂]
    exact (multiplicity_congr_first_SLnZ (DeltaPrime_le_posDetInt N g₁.2) g₁'.2
      (DeltaPrime_le_posDetInt N g₂.2) hDrep h₁).symm
  · rw [inclHecke_apply_of_notMem N _ hD, HeckeCosetModule.structureConstants_apply]
    by_contra hne
    have hne' : multiplicity (SLnZ 2) (SLnZ 2) (SLnZ 2) (g₁' : GL (Fin 2) ℚ) (g₂' : GL (Fin 2) ℚ)
        (D'.rep : GL (Fin 2) ℚ) ≠ 0 := fun h0 ↦ hne (by rw [h0]; simp)
    have hmem := (HeckeCoset.mem_image_mulMap_iff g₁' g₂' D').mpr hne'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hmem
    obtain ⟨p, hp⟩ := hmem
    refine hD ⟨HeckeCoset.mk _ _ ⟨(p.1.out : GL (Fin 2) ℚ) * g₁' * ((p.2.out : GL (Fin 2) ℚ) * g₂'),
      mul_mem (mul_mem (IsHeckeTriple.mem_of_mem_left (SLnZ 2) p.1.out.2) hg₁')
        (mul_mem (IsHeckeTriple.mem_of_mem_left (SLnZ 2) p.2.out.2) hg₂')⟩, ?_⟩
    exact (inclCoset_mk N _).trans hp

/-- The inclusion `H(Γ(1), Δ₀(N)) → H(Γ(1), Δ)` is multiplicative. -/
theorem inclHecke_mul (x y : 𝕋 (DeltaPrime N) (SLnZ 2) ℤ) :
    inclHecke N (x * y) = inclHecke N x * inclHecke N y := by
  induction x using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd f₁ f₂ h₁ h₂ => rw [add_mul, map_add, map_add, add_mul, h₁, h₂]
  | hsingle D₁ a =>
    induction y using HeckeCosetModule.induction_linear with
    | h0 => simp
    | hadd g₁ g₂ h₁ h₂ => rw [mul_add, map_add, map_add, mul_add, h₁, h₂]
    | hsingle D₂ b =>
      rw [HeckeCosetModule.single_mul_single, inclHecke_single, inclHecke_single,
        HeckeCosetModule.single_mul_single, map_smul, map_smul,
        inclHecke_structureConstants N D₁.rep D₂.rep (inclCoset N D₁).rep (inclCoset N D₂).rep
          (inclCoset_rep_mem N D₁) (inclCoset_rep_mem N D₂)]
      rfl

/-- `ψ = inclHecke ∘ heckeLevelMap` sends `T^N(a, d)` to `T(a, d)`. -/
theorem inclHecke_heckeLevelMap_heckeTNDiag [NeZero N] {a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (had : a ∣ d) (hcop : (a * d).Coprime N) :
    inclHecke N (heckeLevelMap N (heckeTNDiag N a d)) = heckeTDiag a d := by
  rw [heckeLevelMap_heckeTNDiag N ha hd had hcop, inclHecke_single, heckeTDiag_eq_diagElem ha hd had,
    diagElem_def]
  rfl

/-- `ψ = inclHecke ∘ heckeLevelMap` sends `T^N(n)` to `T(n)`. -/
theorem inclHecke_heckeLevelMap_heckeTN [NeZero N] {n : ℕ} (hn : 0 < n) (hcop : n.Coprime N) :
    inclHecke N (heckeLevelMap N (heckeTN N n)) = heckeT n := by
  rw [heckeT_eq_sum, heckeTN, map_sum, map_sum]
  refine Finset.sum_congr rfl fun ad had ↦ ?_
  obtain ⟨hmul, -⟩ := Nat.mem_divisorsAntidiagonal.mp (Finset.mem_filter.mp had).1
  have hdvd := (Finset.mem_filter.mp had).2
  have ha : 0 < ad.1 := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hmul; omega
  have hd : 0 < ad.2 := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hmul; omega
  exact inclHecke_heckeLevelMap_heckeTNDiag N ha hd hdvd (by rw [hmul]; exact hcop)

/-- **Relation (10)** (p. 83), assuming Lemma 5.33: in $H(\Gamma(N), \Delta(N))$,
$T^N(n)T^N(m) = \sum_{d \mid (n, m)} d\,T^N(d, d)\,T^N(mn/d^2)$ for $m, n \ge 1$ with $(mn, N) = 1$. -/
@[kb "milne2017mf" "Section 5, relation (10) (pdf p. 83)"]
theorem heckeTN_mul_heckeTN [NeZero N] (hiso : HeckeLevelIso N) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hcop : (m * n).Coprime N) :
    heckeTN N n * heckeTN N m =
      ∑ d ∈ (Nat.gcd n m).divisors, (d : ℤ) • (heckeTNDiag N d d * heckeTN N (m * n / d ^ 2)) := by
  have hψinj : Function.Injective (fun x ↦ inclHecke N (heckeLevelMap N x)) :=
    (inclHecke_injective N).comp hiso.bijective.1
  have hψmul : ∀ x y, inclHecke N (heckeLevelMap N (x * y)) =
      inclHecke N (heckeLevelMap N x) * inclHecke N (heckeLevelMap N y) := fun x y ↦ by
    rw [hiso.map_mul, inclHecke_mul]
  have hn' : n.Coprime N := Nat.Coprime.coprime_dvd_left (dvd_mul_left n m) hcop
  have hm' : m.Coprime N := Nat.Coprime.coprime_dvd_left (dvd_mul_right m n) hcop
  apply hψinj
  simp only [hψmul, map_sum, map_zsmul]
  rw [inclHecke_heckeLevelMap_heckeTN N hn hn', inclHecke_heckeLevelMap_heckeTN N hm hm']
  rw [heckeT_mul_heckeT hm hn, Nat.gcd_comm n m]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  obtain ⟨hdm, hdn⟩ := Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors hd)
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdN : d.Coprime N := Nat.Coprime.coprime_dvd_left hdn hn'
  have hdd : d ^ 2 ∣ m * n := by rw [sq]; exact mul_dvd_mul hdm hdn
  have hq : m * n / d ^ 2 ∣ m * n := Nat.div_dvd_of_dvd hdd
  have hqpos : 0 < m * n / d ^ 2 :=
    Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hm hn) hdd) (by positivity)
  rw [inclHecke_heckeLevelMap_heckeTNDiag N hdpos hdpos dvd_rfl (Nat.coprime_mul_iff_left.mpr ⟨hdN, hdN⟩),
    inclHecke_heckeLevelMap_heckeTN N hqpos (Nat.Coprime.coprime_dvd_left hq hcop.symm.symm),
    heckeTScalar_def, mul_comm n m]

/-- **Milne, Theorem 5.36** (named statement; Milne: "See Ogg 1969, p. IV-10"). Let $f \in V(t, \varepsilon) =
V(t) \cap V(\varepsilon)$ have the expansion $\sum a_nq_N^n$ with $a_1 = 1$ and be an eigenform of every $T^t(n)$. Then
$\sum a_nn^{-s} = \prod_p(1 - a_pp^{-s} + \varepsilon(p)p^{2k-1-2s})^{-1}$ (formally), with $\varepsilon(p) = 0$ for
$p \mid N$. Milne writes "an eigenform for all the $T^t(n)$ with $\gcd(n, N) = 1$"; that hypothesis says nothing
about the coefficients $a_{p^r}$, $p \mid N$, which the factors at $p \mid N$ involve, so the statement is taken with
all $n \ge 1$ [unverified against Ogg]. -/
@[kb "milne2017mf" "Section 5, Theorem 5.36 (pdf p. 85); Ogg 1969, p. IV-10 [unverified]"]
structure EulerProductLevelNt [NeZero N] (k : ℕ) : Prop where
  euler : ∀ (t : ℕ), t ∣ N → ∀ (ε : (ZMod N)ˣ →* ℂˣ) (f : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)),
    f ∈ tSpaceN N k t → f ∈ charSpaceN N k ε →
    (∀ n : ℕ, 0 < n → ∃ c : ℂ, heckeTt N k t n f = c • ⇑f) →
    (qExpansion N f).coeff 1 = 1 →
    Miyake.HasHeckeEulerProduct (fun n ↦ (qExpansion N f).coeff n) (charWeight N k ε)

/-- **Milne, Proposition 5.37** (named statement; Milne: "See Ogg 1969, p. IV-24"). For cusp forms $f, g$ of weight
$2k$ and character $\varepsilon$ for $\Gamma(N)$ and $(n, N) = 1$, $\langle T(n)f, g\rangle = \varepsilon(n)\langle f, T(n)g\rangle$.
In Tau Ceti's Petersson product `CuspForm.peterssonInnerCosets` (conjugate-linear in the first argument, so Milne's
$\langle a, b\rangle$ is `peterssonInnerCosets b a`) this reads `P(g, T f) = ε(n) P(T g, f)`; $T(n)f$ is a cusp form
`F` with the same underlying function as $T^N(n)f$. -/
@[kb "milne2017mf" "Section 5, Proposition 5.37 (pdf p. 85); Ogg 1969, p. IV-24 [unverified]"]
structure PeterssonHeckeLevelN [NeZero N] (k : ℕ) : Prop where
  adjoint : ∀ (ε : (ZMod N)ˣ →* ℂˣ) (n : ℕ), 0 < n → (hn : n.Coprime N) →
    ∀ f g F G : CuspForm ((Gamma N).map (mapGL ℝ)) (2 * k),
    (f : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)) ∈ charSpaceN N k ε →
    (g : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)) ∈ charSpaceN N k ε →
    ⇑F = ⇑(heckeActN N k (heckeTN N n) f) → ⇑G = ⇑(heckeActN N k (heckeTN N n) g) →
    CuspForm.peterssonInnerCosets g F = (ε (ZMod.unitOfCoprime n hn) : ℂ) * CuspForm.peterssonInnerCosets G f

end ModularFormsKB.Milne
