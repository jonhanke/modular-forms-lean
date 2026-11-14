import ModularFormsKB.Miyake.Wave4.MiyakeHecke
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.CosetMap
import TauCeti.NumberTheory.HeckeRing.GL2.MultiplicationTable
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.ElementaryDivisors
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Elem

/-!
# Miyake, Lemma 4.5.6 (2) and Lemma 4.5.7 (1) for a prime `p` prime to the level

Miyake, *Modular Forms* (Springer 1989), §4.5, pp. 138–140.

For a prime `p ∤ N`:

* Lemma 4.5.6 (2), via the comparison with level one (Shimura, Proposition 3.31): for a double
  coset `Γ₀(N) α Γ₀(N)` with `det α` prime to `N`, the left cosets of `Γ₀(N)` in it correspond
  bijectively to the left cosets of `SL₂(ℤ)` in `SL₂(ℤ) α SL₂(ℤ)`, so the two degrees agree
  (`degree_diagCosetGamma0_eq_degree_diagCoset`); at level one the degrees are Tau Ceti's
  `HeckeRing.GL2.degree_diagCoset_prime_pow`;
* Lemma 4.5.7 (1): `T(1, p) T(1, p^e) = T(1, p^{e+1}) + c T(p, p^e)` with `c = p + 1` if `e = 1`
  and `c = p` if `e ≥ 2` (`heckeTPair_one_prime_mul`).

The proof of Lemma 4.5.7 (1) is the level-one proof of Tau Ceti
(`HeckeRing.GL2.heckeT_prime_mul_heckeTDiag_one_prime_pow`, `GL2/MultiplicationTable.lean`)
carried to `Γ₀(N)`: the support of the product is `{T(1, p^{e+1}), T(p, p^e)}` (elementary
divisors, Miyake Lemma 4.5.2), `T(1, p^{e+1})` occurs, and the degree balance forces the two
multiplicities.
-/

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups HeckeCosetModule

noncomputable section

namespace ModularFormsKB.Miyake.Wave5

open ModularFormsKB.Miyake.Wave4

variable (N : ℕ) [NeZero N]

open HeckeRing HeckeRing.GLn HeckeRing.GL2 DoubleCoset

section DegreeComparison

open scoped Pointwise

/-- Counting cosets: if `A ≤ B`, `C₀ ≤ C₁`, `C₁ ∩ A ⊆ C₀`, and every `b ∈ B` is `a k` with `a ∈ A`,
`k ∈ C₁`, then `[A : C₀ ∩ A] = [B : C₁ ∩ B]`. -/
private lemma relIndex_eq_of_mul_eq {G : Type*} [Group G] {A B C₀ C₁ : Subgroup G}
    (hAB : A ≤ B) (hC : C₀ ≤ C₁) (h0 : ∀ a ∈ A, a ∈ C₁ → a ∈ C₀)
    (h1 : ∀ b ∈ B, ∃ a ∈ A, a⁻¹ * b ∈ C₁) : C₀.relIndex A = C₁.relIndex B := by
  unfold Subgroup.relIndex Subgroup.index
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.map' (Subgroup.inclusion hAB) ?_ :
      A ⧸ C₀.subgroupOf A → B ⧸ C₁.subgroupOf B) ⟨?_, ?_⟩)
  · intro x y hxy
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hxy ⊢
    exact hC hxy
  · intro x y
    refine Quotient.inductionOn' x fun x ↦ Quotient.inductionOn' y fun y ↦ ?_
    intro hxy
    have hxy' : (QuotientGroup.mk (Subgroup.inclusion hAB x) : B ⧸ C₁.subgroupOf B) =
        QuotientGroup.mk (Subgroup.inclusion hAB y) := hxy
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hxy'
    exact (QuotientGroup.eq (s := C₀.subgroupOf A)).mpr
      ((Subgroup.mem_subgroupOf).mpr (h0 _ (A.mul_mem (A.inv_mem x.2) y.2) hxy'))
  · intro y
    refine Quotient.inductionOn' y fun y ↦ ?_
    obtain ⟨a, ha, hab⟩ := h1 y y.2
    refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hAB ⟨a, ha⟩) : B ⧸ C₁.subgroupOf B) =
      QuotientGroup.mk y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hab

/-- Degree comparison at a representative (Shimura, Proposition 3.31, degree form). -/
private lemma degree_mk_eq_levelOne (g : Delta0 N) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (↑(g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hdet : Int.gcd A.det N = 1) :
    (HeckeCoset.mk ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) g).degree =
      (HeckeCoset.mk (SLnZ 2) (SLnZ 2) (Submonoid.inclusion (Delta0_le_posDetInt N) g)).degree := by
  rw [HeckeCoset.degree_mk, HeckeCoset.degree_mk]
  obtain ⟨B, hB, -, hBN, -⟩ := (mem_Delta0_iff N).mp g.2
  have hBA : B = A := Matrix.map_injective Int.cast_injective (hB.symm.trans hA)
  have hAN : (N : ℤ) ∣ A 1 0 := hBA ▸ hBN
  have hA11 : Int.gcd (A 1 1) N = 1 := gcd_apply_one_one_eq_one N A hAN hdet
  have hcop : IsCoprime (N : ℤ) (A 1 1) := (Int.isCoprime_iff_gcd_eq_one.mpr hA11).symm
  refine relIndex_eq_of_mul_eq (Gamma0_map_le_SLnZ N) ?_ ?_ ?_
  · intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx ⊢
    exact Gamma0_map_le_SLnZ N hx
  · intro x hx hx1
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx1 ⊢
    change (ConjAct.toConjAct (g : GL (Fin 2) ℚ))⁻¹ • x ∈ SLnZ 2 at hx1
    change (ConjAct.toConjAct (g : GL (Fin 2) ℚ))⁻¹ • x ∈ ((Gamma0 N).map (mapGL ℚ))
    rw [ConjAct.smul_def, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct] at hx1 ⊢
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨σ', hσ'⟩ := (mem_SLnZ_iff 2).mp hx1
    have hconj : (g : GL (Fin 2) ℚ) * mapGL ℚ σ' = mapGL ℚ γ * (g : GL (Fin 2) ℚ) := by
      rw [hσ']; group
    have h1 := mapGL_mul_coe_eq_intMatrix 2 1 σ' (g : GL (Fin 2) ℚ) A hA
    have h2 := mapGL_mul_coe_eq_intMatrix 2 γ 1 (g : GL (Fin 2) ℚ) A hA
    have h3 : mapGL ℚ (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) * (g : GL (Fin 2) ℚ) *
        mapGL ℚ σ' = mapGL ℚ γ * (g : GL (Fin 2) ℚ) *
          mapGL ℚ (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) := by
      rw [map_one, one_mul, mul_one, hconj]
    rw [h3, h2] at h1
    have h4 := Matrix.map_injective (f := (Int.cast : ℤ → ℚ)) Int.cast_injective h1
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.SpecialLinearGroup.coe_one] at h4
    have h5 := congrFun (congrFun h4 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h5
    have hγ10 : (N : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := mem_Gamma0_iff_dvd.mp hγ
    have hdvd : (N : ℤ) ∣ A 1 1 * (σ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
      have : A 1 1 * (σ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
          (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * A 0 0 +
            ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - (σ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0) *
              A 1 0 := by
        linarith
      rw [this]
      exact dvd_add (dvd_mul_of_dvd_left hγ10 _) (dvd_mul_of_dvd_right hAN _)
    have hσ'N : σ' ∈ Gamma0 N := mem_Gamma0_iff_dvd.mpr (hcop.dvd_of_dvd_mul_left hdvd)
    exact ⟨σ', hσ'N, hσ'⟩
  · intro b hb
    obtain ⟨σ, rfl⟩ := (mem_SLnZ_iff 2).mp hb
    have : (Gamma N).Normal := Gamma_normal N
    have h_top : Gamma N ⊔ Gamma A.det.natAbs = ⊤ := by
      have hc : N.Coprime A.det.natAbs := by
        rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one]; simpa [Int.gcd] using hdet
      unfold Gamma
      exact sup_ker_map_intCast_zmod_eq_top_of_coprime hc
    obtain ⟨τ_N, hτ_N, τ_a, hτ_a, hσ_eq⟩ :=
      Subgroup.mem_sup_of_normal_left.mp (h_top ▸ Subgroup.mem_top σ)
    have hτ_ker : τ_a ∈ (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod A.det.natAbs))).ker :=
      MonoidHom.mem_ker.mpr (Gamma_mem'.mp hτ_a)
    refine ⟨mapGL ℚ τ_N, Subgroup.mem_map.mpr ⟨τ_N, Gamma_le_Gamma0 N hτ_N, rfl⟩, ?_⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change (ConjAct.toConjAct (g : GL (Fin 2) ℚ))⁻¹ • ((mapGL ℚ τ_N)⁻¹ * mapGL ℚ σ) ∈ SLnZ 2
    rw [ConjAct.smul_def, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct,
      ← hσ_eq, map_mul, inv_mul_cancel_left, inv_inv]
    exact inv_conjugate_mem_SLnZ_of_mem_ker 2 (g : GL (Fin 2) ℚ) A hA τ_a hτ_ker

/-- `toLevelOneCoset` preserves the degree on coprime-determinant double cosets. -/
private lemma degree_toLevelOneCoset (D : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))
    (hD : CoprimeDetCoset N N D) : (toLevelOneCoset N D).degree = D.degree := by
  refine HeckeCoset.induction
    (motive := fun D ↦ CoprimeDetCoset N N D → (toLevelOneCoset N D).degree = D.degree)
    (fun g hg ↦ ?_) D hD
  rw [toLevelOneCoset_mk]
  obtain ⟨A, hA, -, -, -⟩ := (mem_Delta0_iff N).mp g.2
  exact (degree_mk_eq_levelOne N g A hA
    ((coprimeDet_iff N hA).mp ((coprimeDetCoset_self_mk N g).mp hg))).symm

private lemma degree_diagCosetGamma0_eq {a : Fin 2 → ℕ} (ha : ∀ i, 0 < a i)
    (hgcd : (∀ i, 0 < a i) → Nat.Coprime (a 0) N) (h : Nat.Coprime (a 0 * a 1) N) :
    (diagCosetGamma0 N a hgcd).degree = (diagCoset a).degree := by
  have := degree_toLevelOneCoset N _ (coprimeDetCoset_diagCosetGamma0_of_coprime N ha hgcd h)
  have h2 := congrArg HeckeCoset.degree (toLevelOneCoset_diagCosetGamma0 N a hgcd)
  exact this.symm.trans h2

end DegreeComparison

/-- **Miyake, Lemma 4.5.6 (2)** for `p ∤ N`: `T(1, p^e)` has degree `p^e + p^{e-1}` for `e ≥ 1`
(that is, `p^{e-1} (p + 1)`). -/
@[kb "miyake1989" "Lemma 4.5.6 (2), p. 138 (p prime to N)"]
theorem degree_one_prime_pow {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) {e : ℕ} (he : 1 ≤ e) :
    (HeckeRing.GL2.diagCosetGamma0 N ![1, p ^ e] fun _ ↦ Nat.coprime_one_left N).degree =
      p ^ (e - 1) * (p + 1) := by
  have hpc : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  have hpos : ∀ i, 0 < (![1, p ^ e] : Fin 2 → ℕ) i := fun i ↦ by
    fin_cases i <;> simp [pow_pos hp.pos]
  refine (degree_diagCosetGamma0_eq N hpos _ (by simpa using hpc.pow_left e)).trans ?_
  simpa using degree_diagCoset_prime_pow p hp 0 e he

section Support

private lemma dvd_entries_mul_left {e : ℤ} (X Y : Matrix (Fin 2) (Fin 2) ℤ)
    (hX : ∀ i j, e ∣ X i j) (i j : Fin 2) : e ∣ (Y * X) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ ↦ dvd_mul_of_dvd_right (hX k j) _

private lemma dvd_entries_mul_right {e : ℤ} (X Y : Matrix (Fin 2) (Fin 2) ℤ)
    (hX : ∀ i j, e ∣ X i j) (i j : Fin 2) : e ∣ (X * Y) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ ↦ dvd_mul_of_dvd_left (hX i k) _

/-- A common divisor of the entries of `a diag(1,p) b diag(1,p^k) c` divides `p`. -/
private lemma dvd_p_of_dvd_entries (p k : ℕ) (a b c : Matrix.SpecialLinearGroup (Fin 2) ℤ) (e : ℤ)
    (he : ∀ i j, e ∣ ((a : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.diagonal (fun i ↦ (((![1, p] : Fin 2 → ℕ) i : ℕ) : ℤ)) *
      (b : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.diagonal (fun i ↦ (((![1, p ^ k] : Fin 2 → ℕ) i : ℕ) : ℤ)) *
      (c : Matrix (Fin 2) (Fin 2) ℤ)) i j) : e ∣ (p : ℤ) := by
  set M := (a : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.diagonal (fun i ↦ (((![1, p] : Fin 2 → ℕ) i : ℕ) : ℤ)) *
      (b : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.diagonal (fun i ↦ (((![1, p ^ k] : Fin 2 → ℕ) i : ℕ) : ℤ)) *
      (c : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have ha : ((a⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
      (a : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← coe_mul, inv_mul_cancel, coe_one]
  have hc : (c : Matrix (Fin 2) (Fin 2) ℤ) *
      ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← coe_mul, mul_inv_cancel, coe_one]
  set W := Matrix.diagonal (fun i ↦ (((![1, p] : Fin 2 → ℕ) i : ℕ) : ℤ)) * (b : Matrix (Fin 2) (Fin 2) ℤ) *
      Matrix.diagonal (fun i ↦ (((![1, p ^ k] : Fin 2 → ℕ) i : ℕ) : ℤ)) with hW
  have hWeq : ((a⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * M *
      ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = W := by
    have : ((a⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * M *
        ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
        (((a⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
          (a : Matrix (Fin 2) (Fin 2) ℤ)) * W * ((c : Matrix (Fin 2) (Fin 2) ℤ) *
      ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)) := by
      simp only [hM, hW, Matrix.mul_assoc]
    rw [this, ha, hc, Matrix.one_mul, Matrix.mul_one]
  have hWdvd : ∀ i j, e ∣ W i j := fun i j ↦ by
    rw [← hWeq]
    exact dvd_entries_mul_right _ _ (fun i j ↦ dvd_entries_mul_left M _ he i j) i j
  have h00 : W 0 0 = (b : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
    simp [hW, Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : W 1 0 = (p : ℤ) * (b : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    simp [hW, Matrix.mul_apply, Fin.sum_univ_two]
  have hcop : IsCoprime ((b : Matrix (Fin 2) (Fin 2) ℤ) 0 0) ((b : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :=
    b.isCoprime_col 0
  have h1 : e ∣ (b : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := h00 ▸ hWdvd 0 0
  have h2 : e ∣ (p : ℤ) * (b : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := h10 ▸ hWdvd 1 0
  exact (hcop.of_isCoprime_of_dvd_left h1).dvd_of_dvd_mul_right h2

/-- Support step at integral level: an element of `Δ₀(N)` of the shape
`a diag(1,p) b diag(1,p^k) c` (with `a, b, c ∈ SL₂(ℤ)`) lies in the `Γ₀(N)`-double coset of
`diag(1, p^{k+1})` or of `diag(p, p^k)`. -/
private lemma mem_support_of_decomp {p : ℕ} (hp : p.Prime) (hpc : Nat.Coprime p N) {k : ℕ}
    (hk : 0 < k) (a b c : Matrix.SpecialLinearGroup (Fin 2) ℤ) (P : GL (Fin 2) ℚ)
    (hPΔ : P ∈ Delta0 N)
    (hP : P = mapGL ℚ a * natDiagGL 2 ![1, p] * mapGL ℚ b * natDiagGL 2 ![1, p ^ k] *
      mapGL ℚ c) :
    P ∈ doubleCoset (natDiagGL 2 ![1, p ^ (k + 1)]) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) ∨
      P ∈ doubleCoset (natDiagGL 2 ![p, p ^ k]) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
  have h1p : ∀ i : Fin 2, 0 < (![1, p] : Fin 2 → ℕ) i := fun i ↦ by
    fin_cases i <;> simp [hp.pos]
  have h1pk : ∀ i : Fin 2, 0 < (![1, p ^ k] : Fin 2 → ℕ) i := fun i ↦ by
    fin_cases i <;> simp [pow_pos hp.pos]
  have h1pk1 : ∀ i : Fin 2, 0 < (![1, p ^ (k + 1)] : Fin 2 → ℕ) i := fun i ↦ by
    fin_cases i <;> simp [pow_pos hp.pos]
  have hppk : ∀ i : Fin 2, 0 < (![p, p ^ k] : Fin 2 → ℕ) i := fun i ↦ by
    fin_cases i <;> simp [hp.pos, pow_pos hp.pos]
  set M : Matrix (Fin 2) (Fin 2) ℤ := (a : Matrix (Fin 2) (Fin 2) ℤ) *
      Matrix.diagonal (fun i ↦ (((![1, p] : Fin 2 → ℕ) i : ℕ) : ℤ)) *
      (b : Matrix (Fin 2) (Fin 2) ℤ) *
      Matrix.diagonal (fun i ↦ (((![1, p ^ k] : Fin 2 → ℕ) i : ℕ) : ℤ)) *
      (c : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hmm : ∀ X Y : Matrix (Fin 2) (Fin 2) ℤ, (X * Y).map (Int.cast : ℤ → ℚ) =
      X.map (Int.cast : ℤ → ℚ) * Y.map (Int.cast : ℤ → ℚ) := fun X Y ↦
    Matrix.map_mul (f := Int.castRingHom ℚ)
  have hPM : (↑P : Matrix (Fin 2) (Fin 2) ℚ) = M.map (Int.cast : ℤ → ℚ) := by
    rw [hP, hM]
    simp only [hmm, Units.val_mul, natDiagGL_coe_eq_map_intCast 2 _ h1p,
      natDiagGL_coe_eq_map_intCast 2 _ h1pk, mapGL_coe_matrix, map_apply_coe,
      RingHom.mapMatrix_apply, algebraMap_int_eq, Int.coe_castRingHom]
  have hdetM : M.det = (p : ℤ) ^ (k + 1) := by
    simp [hM, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_two, pow_succ]
    ring
  by_cases hall : ∀ i j, (p : ℤ) ∣ M i j
  · right
    refine mem_doubleCoset_of_det_eq_of_dvd_iff N
      (natDiagGL_mem_Delta0_of_coprime N ![p, p ^ k] fun _ ↦ hpc) hPΔ
      (natDiagGL_coe_eq_map_intCast 2 _ hppk) hPM ?_ ?_
    · rw [hdetM]
      simp [Matrix.det_diagonal, Fin.prod_univ_two, pow_succ']
    · intro e
      constructor
      · intro h i j
        have : e ∣ (p : ℤ) := by simpa using h 0 0
        exact this.trans (hall i j)
      · intro h i j
        have hep := dvd_p_of_dvd_entries p k a b c e h
        fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
        · exact hep
        · exact hep.trans (dvd_pow_self _ hk.ne')
  · left
    have hone : ∀ e : ℤ, (∀ i j, e ∣ M i j) → e ∣ 1 := by
      intro e h
      have hep := dvd_p_of_dvd_entries p k a b c e h
      have hnat : e.natAbs ∣ p := by simpa using Int.natAbs_dvd_natAbs.mpr hep
      rcases (Nat.dvd_prime hp).mp hnat with h1 | h1
      · exact (Int.isUnit_iff_natAbs_eq.mpr h1).dvd
      · exfalso
        have h2 : (e.natAbs : ℤ) ∣ e := Int.natAbs_dvd.mpr dvd_rfl
        rw [h1] at h2
        exact hall fun i j ↦ h2.trans (h i j)
    refine mem_doubleCoset_of_det_eq_of_dvd_iff N
      (natDiagGL_mem_Delta0_of_coprime N ![1, p ^ (k + 1)] fun _ ↦ Nat.coprime_one_left N) hPΔ
      (natDiagGL_coe_eq_map_intCast 2 _ h1pk1) hPM ?_ ?_
    · rw [hdetM]
      simp [Matrix.det_diagonal, Fin.prod_univ_two]
    · intro e
      constructor
      · intro h i j
        have : e ∣ 1 := by simpa using h 0 0
        exact this.trans (one_dvd _)
      · intro h i j
        have h1 := hone e h
        fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
        · exact h1
        · exact h1.trans (one_dvd _)

end Support

section Product

private lemma exists_SL_of_mem {x : GL (Fin 2) ℚ} (hx : x ∈ ((Gamma0 N).map (mapGL ℚ))) :
    ∃ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ, mapGL ℚ σ = x := by
  obtain ⟨σ, -, rfl⟩ := Subgroup.mem_map.mp hx
  exact ⟨σ, rfl⟩

private lemma decomp_aux (r₁ r₂ x y h₁ h₂ h₃ h₄ d₁ d₂ : GL (Fin 2) ℚ)
    (s₁ s₂ t₁ t₂ t₃ t₄ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hr₁ : r₁ = h₁ * d₁ * h₂) (hr₂ : r₂ = h₃ * d₂ * h₄)
    (hs₁ : mapGL ℚ s₁ = x) (hs₂ : mapGL ℚ s₂ = y) (ht₁ : mapGL ℚ t₁ = h₁)
    (ht₂ : mapGL ℚ t₂ = h₂) (ht₃ : mapGL ℚ t₃ = h₃) (ht₄ : mapGL ℚ t₄ = h₄) :
    x * r₁ * (y * r₂) = mapGL ℚ (s₁ * t₁) * d₁ * mapGL ℚ (t₂ * s₂ * t₃) * d₂ * mapGL ℚ t₄ := by
  subst hr₁ hr₂ hs₁ hs₂ ht₁ ht₂ ht₃ ht₄
  simp only [map_mul]
  group

/-- The support of `T(1,p) T(1,p^k)` at level `Γ₀(N)` lies in `{T(1,p^{k+1}), T(p,p^k)}`. -/
private lemma mulSupport_subset {p : ℕ} (hp : p.Prime) (hpc : Nat.Coprime p N) {k : ℕ}
    (hk : 0 < k) (A : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)))
    (hA : multiplicity ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      ((diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N).rep : GL (Fin 2) ℚ)
      ((diagCosetGamma0 N ![1, p ^ k] fun _ ↦ Nat.coprime_one_left N).rep : GL (Fin 2) ℚ)
      (A.rep : GL (Fin 2) ℚ) ≠ 0) :
    A = diagCosetGamma0 N ![1, p ^ (k + 1)] (fun _ ↦ Nat.coprime_one_left N) ∨
      A = diagCosetGamma0 N ![p, p ^ k] (fun _ ↦ hpc) := by
  have hmem := (HeckeCoset.mem_image_mulMap_iff
    (diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N).rep
    (diagCosetGamma0 N ![1, p ^ k] fun _ ↦ Nat.coprime_one_left N).rep A).mpr hA
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hmem
  obtain ⟨q, hq⟩ := hmem
  rw [HeckeCoset.mulMap_eq_mk] at hq
  obtain ⟨h₁, hh₁, h₂, hh₂, hD1⟩ := exists_rep_diagCosetGamma0_eq_mul_natDiagGL_mul N ![1, p]
    fun _ ↦ Nat.coprime_one_left N
  obtain ⟨h₃, hh₃, h₄, hh₄, hD2⟩ := exists_rep_diagCosetGamma0_eq_mul_natDiagGL_mul N
    ![1, p ^ k] fun _ ↦ Nat.coprime_one_left N
  obtain ⟨s₁, hs₁⟩ := exists_SL_of_mem N q.1.out.2
  obtain ⟨s₂, hs₂⟩ := exists_SL_of_mem N q.2.out.2
  obtain ⟨t₁, ht₁⟩ := exists_SL_of_mem N hh₁
  obtain ⟨t₂, ht₂⟩ := exists_SL_of_mem N hh₂
  obtain ⟨t₃, ht₃⟩ := exists_SL_of_mem N hh₃
  obtain ⟨t₄, ht₄⟩ := exists_SL_of_mem N hh₄
  have hP : ((q.1.out : GL (Fin 2) ℚ) *
      ((diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N).rep : GL (Fin 2) ℚ) *
      ((q.2.out : GL (Fin 2) ℚ) *
        ((diagCosetGamma0 N ![1, p ^ k] fun _ ↦ Nat.coprime_one_left N).rep : GL (Fin 2) ℚ))) =
      mapGL ℚ (s₁ * t₁) * natDiagGL 2 ![1, p] * mapGL ℚ (t₂ * s₂ * t₃) *
        natDiagGL 2 ![1, p ^ k] * mapGL ℚ t₄ := by
    exact decomp_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hD1 hD2 hs₁ hs₂ ht₁ ht₂ ht₃ ht₄
  have hPΔ : ((q.1.out : GL (Fin 2) ℚ) *
      ((diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N).rep : GL (Fin 2) ℚ) *
      ((q.2.out : GL (Fin 2) ℚ) *
        ((diagCosetGamma0 N ![1, p ^ k] fun _ ↦ Nat.coprime_one_left N).rep : GL (Fin 2) ℚ))) ∈
      Delta0 N :=
    (Delta0 N).mul_mem
      ((Delta0 N).mul_mem (Gamma0Image_le_Delta0 N q.1.out.2) (Subtype.property _))
      ((Delta0 N).mul_mem (Gamma0Image_le_Delta0 N q.2.out.2) (Subtype.property _))
  rw [← hq]
  rcases mem_support_of_decomp N hp hpc hk _ _ _ _ hPΔ hP with h | h
  · left
    refine Eq.trans ?_ (diagCosetGamma0_def N _ _).symm
    exact HeckeCoset.eq_iff.mpr (doubleCoset_eq_of_mem h)
  · right
    refine Eq.trans ?_ (diagCosetGamma0_def N _ _).symm
    exact HeckeCoset.eq_iff.mpr (doubleCoset_eq_of_mem h)

end Product

section Multiplicities

private lemma multiplicity_degree_sum_eq {G : Type*} [Group G] {Δ : Submonoid G}
    {H : Subgroup G} [IsHeckeTriple Δ H H] (D₁ D₂ Dout₁ Dout₂ : HeckeCoset Δ H H)
    (hne : Dout₁ ≠ Dout₂)
    (hzero : ∀ A : HeckeCoset Δ H H, A ≠ Dout₁ → A ≠ Dout₂ →
      multiplicity H H H (D₁.rep : G) (D₂.rep : G) (A.rep : G) = 0) :
    multiplicity H H H (D₁.rep : G) (D₂.rep : G) (Dout₁.rep : G) * Dout₁.degree +
      multiplicity H H H (D₁.rep : G) (D₂.rep : G) (Dout₂.rep : G) * Dout₂.degree =
      D₁.degree * D₂.degree := by
  classical
  have hSC2 : HeckeCosetModule.structureConstants ℤ H H H D₁.rep D₂.rep =
      HeckeCosetModule.single ℤ Dout₁
        (multiplicity H H H (D₁.rep : G) (D₂.rep : G) (Dout₁.rep : G) : ℤ) +
      HeckeCosetModule.single ℤ Dout₂
        (multiplicity H H H (D₁.rep : G) (D₂.rep : G) (Dout₂.rep : G) : ℤ) := by
    ext A
    rw [HeckeCosetModule.structureConstants_apply, HeckeCosetModule.add_apply,
      HeckeCosetModule.single_apply, HeckeCosetModule.single_apply]
    by_cases h1 : Dout₁ = A
    · rw [ite_eq_left h1, ite_eq_right (h1 ▸ fun h ↦ hne h.symm), add_zero, ← h1]
    · rw [ite_eq_right h1]
      by_cases h2 : Dout₂ = A
      · rw [ite_eq_left h2, zero_add, ← h2]
      · rw [ite_eq_right h2, add_zero,
          hzero A (fun h ↦ h1 h.symm) (fun h ↦ h2 h.symm), Nat.cast_zero]
  have h1 : LeftCosetModule.deg Δ H ℤ
      (HeckeCosetModule.single ℤ D₁ 1 * HeckeCosetModule.single ℤ D₂ 1) =
      (D₁.degree : ℤ) * D₂.degree := by
    rw [map_mul, LeftCosetModule.deg_single, LeftCosetModule.deg_single]
    simp
  have h2 : LeftCosetModule.deg Δ H ℤ
      (HeckeCosetModule.single ℤ D₁ 1 * HeckeCosetModule.single ℤ D₂ 1) =
      (multiplicity H H H (D₁.rep : G) (D₂.rep : G) (Dout₁.rep : G) : ℤ) * Dout₁.degree +
      (multiplicity H H H (D₁.rep : G) (D₂.rep : G) (Dout₂.rep : G) : ℤ) * Dout₂.degree := by
    have hmul : HeckeCosetModule.single ℤ D₁ 1 * HeckeCosetModule.single ℤ D₂ 1 =
        HeckeCosetModule.structureConstants ℤ H H H D₁.rep D₂.rep := by
      rw [HeckeCosetModule.single_mul_single]
      exact (one_smul ℤ _).trans (one_smul ℤ _)
    rw [hmul, hSC2, map_add, LeftCosetModule.deg_single, LeftCosetModule.deg_single]
    simp [mul_comm]
  exact_mod_cast (h1.symm.trans h2).symm

private lemma m1_eq_one_and_m2_eq_of_two_le (P m1 m2 : ℤ) (k : ℕ) (hk2 : 2 ≤ k)
    (hP : 2 ≤ P) (hm1 : 1 ≤ m1) (hm2 : 0 ≤ m2)
    (h_deg : m1 * (P ^ k * (P + 1)) + m2 * (P ^ (k - 2) * (P + 1)) =
      (P + 1) * (P ^ (k - 1) * (P + 1))) :
    m1 = 1 ∧ m2 = P := by
  have hpk : P ^ k = P ^ (k - 2) * P ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hpk1 : P ^ (k - 1) = P ^ (k - 2) * P := by
    rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
  have h_eq : m1 * P ^ 2 + m2 = P * (P + 1) := by
    have h := h_deg
    rw [hpk, hpk1] at h
    have key : P ^ (k - 2) * (P + 1) ≠ 0 := by positivity
    have hcancel := mul_right_cancel₀ key (show
      (m1 * P ^ 2 + m2) * (P ^ (k - 2) * (P + 1)) =
      (P * (P + 1)) * (P ^ (k - 2) * (P + 1)) by nlinarith)
    linarith
  have h_m1_eq : m1 = 1 := by
    nlinarith [show P ^ 2 ≥ 4 by nlinarith]
  exact ⟨h_m1_eq, by rw [h_m1_eq] at h_eq; linarith⟩

private lemma m1_eq_one_and_m2_eq_of_eq_one (P m1 m2 : ℤ) (hP : 2 ≤ P)
    (hm1 : 1 ≤ m1) (hm2 : 0 ≤ m2)
    (h_deg : m1 * (P ^ 1 * (P + 1)) + m2 * 1 = (P + 1) * (P + 1)) :
    m1 = 1 ∧ m2 = P + 1 := by
  have h_m1_eq : m1 = 1 := by nlinarith [mul_self_nonneg (P - 1)]
  exact ⟨h_m1_eq, by rw [h_m1_eq] at h_deg; nlinarith⟩

private lemma natDiagGL_one_p_mul_one_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    natDiagGL 2 (![1, p]) * natDiagGL 2 (![1, p ^ k]) = natDiagGL 2 (![1, p ^ (k + 1)]) := by
  rw [natDiagGL_mul 2 _ _ (fun i ↦ by fin_cases i <;> simp [hp.pos])
    (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos k])]
  exact congrArg (natDiagGL 2) (funext fun i ↦ by
    fin_cases i <;> simp [Pi.mul_apply, pow_succ'])

private lemma diagCosetGamma0_one_prime_pow_succ_ne {p : ℕ} (hp : p.Prime)
    (hpc : Nat.Coprime p N) (k : ℕ) (hk : 0 < k) :
    diagCosetGamma0 N ![1, p ^ (k + 1)] (fun _ ↦ Nat.coprime_one_left N) ≠
      diagCosetGamma0 N ![p, p ^ k] (fun _ ↦ hpc) := by
  intro heq0
  have heq := (toLevelOneCoset_diagCosetGamma0 N ![1, p ^ (k + 1)]
    (fun _ ↦ Nat.coprime_one_left N)).symm.trans
    ((congrArg (toLevelOneCoset N) heq0).trans
      (toLevelOneCoset_diagCosetGamma0 N ![p, p ^ k] (fun _ ↦ hpc)))
  have ha := eq_of_diagCoset_eq
    (fun i : Fin 2 ↦ by fin_cases i <;> simp [pow_pos hp.pos])
    (fun i : Fin 2 ↦ by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
    (isDvdChain_iff.mpr fun i j' hij ↦ by
      fin_cases i <;> fin_cases j' <;> first | exact absurd hij (by decide) | simp)
    (isDvdChain_iff.mpr fun i j' hij ↦ by
      fin_cases i <;> fin_cases j' <;>
        first
        | exact absurd hij (by decide)
        | simp [dvd_pow_self p (show k ≠ 0 by omega)])
    heq
  exact hp.one_lt.ne' (by simpa using (congr_fun ha 0).symm)

private lemma multiplicity_one_prime_pow_succ_pos {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 < multiplicity ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      ((diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N).rep : GL (Fin 2) ℚ)
      ((diagCosetGamma0 N ![1, p ^ k] fun _ ↦ Nat.coprime_one_left N).rep : GL (Fin 2) ℚ)
      ((diagCosetGamma0 N ![1, p ^ (k + 1)] fun _ ↦ Nat.coprime_one_left N).rep :
        GL (Fin 2) ℚ) := by
  refine Nat.pos_of_ne_zero (multiplicity_ne_zero_iff.mpr ?_)
  obtain ⟨L₁, hL₁, R₁, hR₁, hD1⟩ := exists_rep_diagCosetGamma0_eq_mul_natDiagGL_mul N ![1, p]
    fun _ ↦ Nat.coprime_one_left N
  obtain ⟨L₂, hL₂, R₂, hR₂, hD2⟩ := exists_rep_diagCosetGamma0_eq_mul_natDiagGL_mul N
    ![1, p ^ k] fun _ ↦ Nat.coprime_one_left N
  obtain ⟨L, hL, R, hR, hD⟩ := exists_rep_diagCosetGamma0_eq_mul_natDiagGL_mul N
    ![1, p ^ (k + 1)] fun _ ↦ Nat.coprime_one_left N
  rw [mem_doubleCoset]
  refine ⟨L * L₁⁻¹ * ((diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N).rep :
      GL (Fin 2) ℚ) * (R₁⁻¹ * L₂⁻¹),
    mem_doubleCoset.mpr ⟨L * L₁⁻¹,
      ((Gamma0 N).map (mapGL ℚ)).mul_mem hL (((Gamma0 N).map (mapGL ℚ)).inv_mem hL₁),
      R₁⁻¹ * L₂⁻¹,
      ((Gamma0 N).map (mapGL ℚ)).mul_mem (((Gamma0 N).map (mapGL ℚ)).inv_mem hR₁) (((Gamma0 N).map (mapGL ℚ)).inv_mem hL₂), rfl⟩,
    R₂⁻¹ * R, ((Gamma0 N).map (mapGL ℚ)).mul_mem (((Gamma0 N).map (mapGL ℚ)).inv_mem hR₂) hR, ?_⟩
  rw [hD, hD1, hD2, ← natDiagGL_one_p_mul_one_prime_pow hp k]
  group

private lemma degree_one_p {p : ℕ} (hp : p.Prime) (hpc : Nat.Coprime p N) :
    (diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N).degree = p + 1 := by
  have hpos : ∀ i : Fin 2, 0 < (![1, p] : Fin 2 → ℕ) i := fun i ↦ by
    fin_cases i <;> simp [hp.pos]
  refine (degree_diagCosetGamma0_eq N hpos _ (by simpa using hpc)).trans ?_
  simpa using degree_diagCoset_prime_pow p hp 0 1 one_pos

private lemma degree_p_pk {p : ℕ} (hp : p.Prime) (hpc : Nat.Coprime p N) {k : ℕ} (hk : 0 < k) :
    (diagCosetGamma0 N ![p, p ^ k] fun _ ↦ hpc).degree =
      if k = 1 then 1 else p ^ (k - 2) * (p + 1) := by
  have hpos : ∀ i : Fin 2, 0 < (![p, p ^ k] : Fin 2 → ℕ) i := fun i ↦ by
    fin_cases i <;> simp [hp.pos, pow_pos hp.pos]
  refine (degree_diagCosetGamma0_eq N hpos _
    (by simpa using Nat.coprime_mul_iff_left.mpr ⟨hpc, hpc.pow_left k⟩)).trans ?_
  by_cases hk1 : k = 1
  · subst hk1
    rw [if_pos rfl, show (![p, p ^ 1] : Fin 2 → ℕ) = fun _ ↦ p from by
      funext i; fin_cases i <;> simp, degree_diagCoset_const 2 p]
  · rw [ite_eq_right hk1]
    have h := degree_diagCoset_prime_pow p hp 1 (k - 1) (by omega)
    rw [show 1 + (k - 1) = k by omega, pow_one] at h
    rw [h, show k - 1 - 1 = k - 2 by omega]

private lemma multiplicity_values {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (hpc : Nat.Coprime p N)
    (k : ℕ) (hk : 0 < k) :
    multiplicity ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      ((diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N).rep : GL (Fin 2) ℚ)
      ((diagCosetGamma0 N ![1, p ^ k] fun _ ↦ Nat.coprime_one_left N).rep : GL (Fin 2) ℚ)
      ((diagCosetGamma0 N ![1, p ^ (k + 1)] fun _ ↦ Nat.coprime_one_left N).rep :
        GL (Fin 2) ℚ) = 1 ∧
    multiplicity ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      ((diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N).rep : GL (Fin 2) ℚ)
      ((diagCosetGamma0 N ![1, p ^ k] fun _ ↦ Nat.coprime_one_left N).rep : GL (Fin 2) ℚ)
      ((diagCosetGamma0 N ![p, p ^ k] fun _ ↦ hpc).rep : GL (Fin 2) ℚ) =
      if k = 1 then p + 1 else p := by
  classical
  have hm1_pos := multiplicity_one_prime_pow_succ_pos N hp k
  have h_deg := multiplicity_degree_sum_eq
    (diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N)
    (diagCosetGamma0 N ![1, p ^ k] fun _ ↦ Nat.coprime_one_left N)
    (diagCosetGamma0 N ![1, p ^ (k + 1)] fun _ ↦ Nat.coprime_one_left N)
    (diagCosetGamma0 N ![p, p ^ k] fun _ ↦ hpc)
    (diagCosetGamma0_one_prime_pow_succ_ne N hp hpc k hk)
    (fun A h1 h2 ↦ by
      by_contra h0
      exact (mulSupport_subset N hp hpc hk A h0).elim h1 h2)
  rw [degree_one_p N hp hpc, degree_one_prime_pow N hp hpN hk,
    degree_one_prime_pow N hp hpN (e := k + 1) (by omega), degree_p_pk N hp hpc hk] at h_deg
  simp only [Nat.add_sub_cancel] at h_deg
  generalize hm1 : multiplicity ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      ((diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N).rep : GL (Fin 2) ℚ)
      ((diagCosetGamma0 N ![1, p ^ k] fun _ ↦ Nat.coprime_one_left N).rep : GL (Fin 2) ℚ)
      ((diagCosetGamma0 N ![1, p ^ (k + 1)] fun _ ↦ Nat.coprime_one_left N).rep :
        GL (Fin 2) ℚ) = m1 at hm1_pos h_deg ⊢
  generalize hm2 : multiplicity ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
      ((diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N).rep : GL (Fin 2) ℚ)
      ((diagCosetGamma0 N ![1, p ^ k] fun _ ↦ Nat.coprime_one_left N).rep : GL (Fin 2) ℚ)
      ((diagCosetGamma0 N ![p, p ^ k] fun _ ↦ hpc).rep : GL (Fin 2) ℚ) = m2 at h_deg ⊢
  have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
  by_cases hk1 : k = 1
  · subst hk1
    simp only [ite_true] at h_deg ⊢
    obtain ⟨h1, h2⟩ := m1_eq_one_and_m2_eq_of_eq_one (p : ℤ) (m1 : ℤ) (m2 : ℤ) hp2
      (by exact_mod_cast hm1_pos) (by positivity) (by
        have h := congrArg (fun n : ℕ ↦ (n : ℤ)) h_deg
        push_cast at h
        linarith)
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · have hk2 : 2 ≤ k := by omega
    simp only [hk1, ite_false] at h_deg ⊢
    obtain ⟨h1, h2⟩ := m1_eq_one_and_m2_eq_of_two_le (p : ℤ) (m1 : ℤ) (m2 : ℤ) k hk2 hp2
      (by exact_mod_cast hm1_pos) (by positivity) (by
        have h := congrArg (fun n : ℕ ↦ (n : ℤ)) h_deg
        push_cast at h
        linarith)
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

end Multiplicities


/-- **Miyake, Lemma 4.5.7 (1)** for `p ∤ N`: in `ℛ(N)`,
`T(1, p) T(1, p^e) = T(1, p^{e+1}) + c T(p, p^e)` with `c = p + 1` for `e = 1` and `c = p` for
`e ≥ 2` (Miyake writes `p T(p, p) T(1, p^{e-1})` for the last term when `e ≥ 2`, which is
`p T(p, p^e)` by the scalar row). -/
@[kb "miyake1989" "Lemma 4.5.7 (1), p. 140 (p prime to N)"]
theorem heckeTPair_one_prime_mul {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) {e : ℕ} (he : 1 ≤ e) :
    heckeTPair N 1 p * heckeTPair N 1 (p ^ e) =
      heckeTPair N 1 (p ^ (e + 1)) + ((if e = 1 then p + 1 else p : ℕ) : ℤ) • heckeTPair N p (p ^ e) := by
  classical
  have hpc : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  have hk : 0 < e := he
  obtain ⟨hm1, hm2⟩ := multiplicity_values N hp hpN hpc e hk
  have hne := diagCosetGamma0_one_prime_pow_succ_ne N hp hpc e hk
  have hpos1 : ∀ i : Fin 2, 0 < (![1, p] : Fin 2 → ℕ) i := fun i ↦ by
    fin_cases i <;> simp [hp.pos]
  have hpos2 : ∀ i : Fin 2, 0 < (![1, p ^ e] : Fin 2 → ℕ) i := fun i ↦ by
    fin_cases i <;> simp [pow_pos hp.pos]
  have hpos3 : ∀ i : Fin 2, 0 < (![1, p ^ (e + 1)] : Fin 2 → ℕ) i := fun i ↦ by
    fin_cases i <;> simp [pow_pos hp.pos]
  have hpos4 : ∀ i : Fin 2, 0 < (![p, p ^ e] : Fin 2 → ℕ) i := fun i ↦ by
    fin_cases i <;> simp [hp.pos, pow_pos hp.pos]
  unfold heckeTPair
  rw [diagElemGamma0_of_pos_of_coprime N hpos1 (Nat.coprime_one_left N),
    diagElemGamma0_of_pos_of_coprime N hpos2 (Nat.coprime_one_left N),
    diagElemGamma0_of_pos_of_coprime N hpos3 (Nat.coprime_one_left N),
    diagElemGamma0_of_pos_of_coprime N hpos4 hpc]
  have hmul : HeckeCosetModule.single ℤ
        (diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N) 1 *
      HeckeCosetModule.single ℤ
        (diagCosetGamma0 N ![1, p ^ e] fun _ ↦ Nat.coprime_one_left N) 1 =
      HeckeCosetModule.structureConstants ℤ ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
        (diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N).rep
        (diagCosetGamma0 N ![1, p ^ e] fun _ ↦ Nat.coprime_one_left N).rep := by
    rw [HeckeCosetModule.single_mul_single]
    exact (one_smul ℤ _).trans (one_smul ℤ _)
  rw [hmul]
  ext A
  rw [HeckeCosetModule.structureConstants_apply, HeckeCosetModule.add_apply]
  have hsmul : (((if e = 1 then p + 1 else p : ℕ) : ℤ) •
      HeckeCosetModule.single ℤ (diagCosetGamma0 N ![p, p ^ e] fun _ ↦ hpc) 1) A
      = ((if e = 1 then p + 1 else p : ℕ) : ℤ) *
        HeckeCosetModule.single ℤ (diagCosetGamma0 N ![p, p ^ e] fun _ ↦ hpc) 1 A :=
    HeckeCosetModule.smul_apply _ _ _
  rw [hsmul, HeckeCosetModule.single_apply, HeckeCosetModule.single_apply]
  by_cases h1 : (diagCosetGamma0 N ![1, p ^ (e + 1)] fun _ ↦ Nat.coprime_one_left N) = A
  · have h12 : (diagCosetGamma0 N ![p, p ^ e] fun _ ↦ hpc) ≠ A := fun h ↦ hne (h1.trans h.symm)
    rw [ite_eq_left h1, ite_eq_right h12, mul_zero, add_zero, ← h1, hm1, Nat.cast_one]
  · rw [ite_eq_right h1]
    by_cases h2 : (diagCosetGamma0 N ![p, p ^ e] fun _ ↦ hpc) = A
    · rw [ite_eq_left h2, mul_one, zero_add, ← h2, hm2]
    · rw [ite_eq_right h2, mul_zero, add_zero,
        show multiplicity ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ))
          (diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N).rep
          (diagCosetGamma0 N ![1, p ^ e] fun _ ↦ Nat.coprime_one_left N).rep A.rep = 0 from by
          by_contra h0
          exact (mulSupport_subset N hp hpc hk A h0).elim (fun h ↦ h1 h.symm) (fun h ↦ h2 h.symm),
        Nat.cast_zero]

end ModularFormsKB.Miyake.Wave5
