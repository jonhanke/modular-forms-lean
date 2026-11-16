import ModularFormsKB.Miyake.Sec4_9.Spherical.Odd
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# Odd rank at the sharp level, with the character in Kronecker form

Miyake, *Modular Forms* (Springer 1989), Theorem 4.9.3 and Corollary 4.9.5 for odd rank
(loose end LE-MF-0238).

`thetaSph_mem_halfIntModularForms` puts the theta series of an even lattice `L`
of odd rank `2k + 1` in Shimura's `M_{k+ν+1/2}(4N, χ)` with `N = level L`, so at level `4 · level L`.
The true level is `level L` itself: an even lattice of odd rank has `4 ∣ level L`
(`four_dvd_level_of_odd`), and then `L ⊕ √2ℤ` has level `lcm (level L) 4 = level L`.

This file states the law for every `N` with `level L ∣ 4N` (`thetaSph_mem_halfIntModularForms_of_dvd`);
`N = level L / 4` is the sharp case (`thetaSph_mem_halfIntModularForms_sharp`). The character
`oddThetaCharOf` is, on odd `d > 0` prime to `N`, the Jacobi symbol
`((-1)^ν 2 |L^∨/L| / d)` (`oddThetaCharOf_natCast`), with `|L^∨/L| = det` of the Hessian in
Gram-matrix language. This is the character for Shimura's automorphy factor `j(γ, τ)^{2(k+ν)+1}`
(`HalfIntegral.HalfIntTransforms`). Miyake's character `((-1)^{(r-1)/2} 2 det A / d)` belongs to the
factor `(cτ + d)^{(r-1)/2} j(γ, τ)` (times the spherical degree); the two differ by `χ_{-4}^{(r-1)/2}`
because `j² = χ_{-4}(d)(cτ + d)`. Check: for `θ³` (`r = 3`, `H = 2·1`) ours is trivial and Miyake's
is `χ_{-4}`, and indeed `θ³(γτ) = j³ θ³(τ)`. The comparison with Miyake's normalization is by this
hand computation; the book was not reread for this job [unverified].

**Proof of `4 ∣ level L`.** Write `N = level L`, `V = L/2L` over `𝔽₂` with the alternating form
`b(x, y) = ⟪x, y⟫ mod 2` (alternating since `L` is even), and `M = √N L^∨`, even (Tau Ceti
`isEven_sqrt_level_smul_dual`). If `N` were odd, `b` would be nondegenerate on an odd-dimensional
space. If `N = 2m`, `m` odd, the radical of `b` on `L/2L` and the image of `M` give complementary
subspaces of even dimension. Either way the rank `2k + 1` would be even.
-/

open Complex Module
open scoped Real RealInnerProductSpace ModularForm UpperHalfPlane MatrixGroups

set_option linter.unusedSectionVars false

namespace ModularFormsKB.Miyake.Sec4_9

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

section FourDvdAux

open Matrix

theorem even_finrank_range_of_alt {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) (hs : A.IsSymm)
    (hd : ∀ i, A i i = 0) : Even (finrank (ZMod 2) (LinearMap.range A.mulVecLin)) := by
  classical
  have hBapply : ∀ x y : Fin n → ZMod 2, Matrix.toBilin' A x y = x ⬝ᵥ A *ᵥ y :=
    fun x y => Matrix.toBilin'_apply' A x y
  have hsymm : ∀ x y : Fin n → ZMod 2, Matrix.toBilin' A x y = Matrix.toBilin' A y x := by
    intro x y
    rw [hBapply, hBapply, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs.eq,
      dotProduct_comm]
  have halt : ∀ x : Fin n → ZMod 2, Matrix.toBilin' A x x = 0 := by
    intro x
    rw [hBapply]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [← Fintype.sum_prod_type']
    have h2 : (2 : ZMod 2) = 0 := by decide
    refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ (by simp) (by simp)
    · intro p _
      have := hs.apply p.1 p.2
      simp only [this]
      linear_combination (x p.1 * (A p.1 p.2 * x p.2)) * h2
    · intro p _ hp h
      apply hp
      have h1 : p.2 = p.1 := congrArg Prod.fst h
      have : A p.1 p.2 = 0 := by rw [h1]; exact hd _
      simp [this]
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.ker A.mulVecLin)
  have hrank : finrank (ZMod 2) W = finrank (ZMod 2) (LinearMap.range A.mulVecLin) := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hW
    have h2 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    simp only [finrank_fin_fun] at h1 h2
    omega
  rw [← hrank]
  have hnd : ((Matrix.toBilin' A).restrict W).Nondegenerate := by
    have key : ∀ w ∈ W, (∀ w' ∈ W, Matrix.toBilin' A w w' = 0) → w = 0 := by
      intro w hw hw0
      have hall : ∀ y, Matrix.toBilin' A y w = 0 := by
        intro y
        have hy : y ∈ LinearMap.ker A.mulVecLin ⊔ W := by rw [hW.sup_eq_top]; trivial
        obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
        rw [map_add, LinearMap.add_apply, hsymm u w, hsymm v w, hw0 v hv, hBapply]
        have : A *ᵥ u = 0 := hu
        simp [this]
      have hker : w ∈ LinearMap.ker A.mulVecLin := by
        rw [LinearMap.mem_ker]
        funext i
        have := hall (Pi.single i 1)
        rw [hBapply, single_dotProduct] at this
        simpa using this
      exact Submodule.disjoint_def.mp hW.disjoint w hker hw
    have left : ∀ w : W, (∀ w' : W, ((Matrix.toBilin' A).restrict W) w w' = 0) → w = 0 := by
      intro w h
      exact Subtype.ext (key w w.2 fun w' hw' => h ⟨w', hw'⟩)
    refine ⟨left, fun w h => left w fun w' => ?_⟩
    simpa [hsymm] using h w'
  exact LinearMap.BilinForm.IsAlt.even_finrank (B := (Matrix.toBilin' A).restrict W)
    (fun x => halt x) hnd

theorem map_two_zmod_isSymm {n : ℕ} {G : Matrix (Fin n) (Fin n) ℤ} (hG : G.IsSymm) :
    (G.map (Int.castRingHom (ZMod 2))).IsSymm := hG.map _

theorem map_two_zmod_diag {n : ℕ} {G : Matrix (Fin n) (Fin n) ℤ} (hGd : ∀ i, Even (G i i))
    (i : Fin n) : G.map (Int.castRingHom (ZMod 2)) i i = 0 := by
  obtain ⟨m, hm⟩ := hGd i
  simp only [Matrix.map_apply, hm, eq_intCast, Int.cast_add]
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [← two_mul, h2, zero_mul]

theorem four_dvd_of_gram_aux {n : ℕ} (hn : Odd n) (G M : Matrix (Fin n) (Fin n) ℤ)
    (hG : G.IsSymm) (hM : M.IsSymm) (hGd : ∀ i, Even (G i i)) (hMd : ∀ i, Even (M i i))
    (N : ℕ) (hGM : G * M = (N : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ))
    (hMG : M * G = (N : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) : 4 ∣ N := by
  by_contra h4
  set f := Int.castRingHom (ZMod 2)
  set Gb := G.map f with hGb
  set Mb := M.map f with hMb
  have hGM2 : Gb * Mb = (N : ZMod 2) • (1 : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    have := congrArg (fun X => X.map f) hGM
    simp only [Matrix.map_mul] at this
    rw [hGb, hMb, this]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hMG2 : Mb * Gb = (N : ZMod 2) • (1 : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    have := congrArg (fun X => X.map f) hMG
    simp only [Matrix.map_mul] at this
    rw [hGb, hMb, this]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hGe := even_finrank_range_of_alt Gb (map_two_zmod_isSymm hG) (map_two_zmod_diag hGd)
  have hMe := even_finrank_range_of_alt Mb (map_two_zmod_isSymm hM) (map_two_zmod_diag hMd)
  have hnk := LinearMap.finrank_range_add_finrank_ker Gb.mulVecLin
  simp only [finrank_fin_fun] at hnk
  rcases Nat.even_or_odd N with hN | hN
  · -- N = 2m with m odd
    obtain ⟨m, hm, hmo⟩ : ∃ m, N = 2 * m ∧ Odd m := by
      obtain ⟨r, hr⟩ := hN
      refine ⟨N / 2, by omega, ?_⟩
      rw [Nat.odd_iff]
      omega
    have h2 : (2 : ZMod 2) = 0 := by decide
    have hN0 : (N : ZMod 2) = 0 := by
      rw [hm]; push_cast; rw [h2, zero_mul]
    have hm1 : (m : ZMod 2) = 1 := by
      obtain ⟨r, hr⟩ := hmo
      rw [hr]; push_cast
      rw [h2]; simp
    have hrk : LinearMap.range Mb.mulVecLin = LinearMap.ker Gb.mulVecLin := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        rw [LinearMap.mem_ker]
        show Gb *ᵥ (Mb *ᵥ y) = 0
        rw [Matrix.mulVec_mulVec, hGM2, hN0, zero_smul, Matrix.zero_mulVec]
      · intro hx
        rw [LinearMap.mem_ker] at hx
        have hx' : Gb *ᵥ x = 0 := hx
        let X : Fin n → ℤ := fun i => ((x i).val : ℤ)
        have hX : f ∘ X = x := by
          funext i; simp [X, f]
        have hGX : ∀ i, ∃ t : ℤ, (G *ᵥ X) i = 2 * t := by
          intro i
          have h1 := RingHom.map_mulVec f G X i
          rw [hX] at h1
          have h2' : f ((G *ᵥ X) i) = 0 := by rw [h1]; exact congrFun hx' i
          have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((G *ᵥ X) i) 2).mp h2'
          obtain ⟨t, ht⟩ := h3
          exact ⟨t, by simpa using ht⟩
        choose y hy using hGX
        have hGXy : G *ᵥ X = (2 : ℤ) • y := by
          funext i; simp [hy i]
        have h5 : M *ᵥ (G *ᵥ X) = (N : ℤ) • X := by
          rw [Matrix.mulVec_mulVec, hMG, Matrix.smul_mulVec, Matrix.one_mulVec]
        rw [hGXy, Matrix.mulVec_smul, hm] at h5
        have h6 : (m : ℤ) • X = M *ᵥ y := by
          funext i
          have := congrFun h5 i
          simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
          push_cast at this
          linarith
        refine ⟨f ∘ y, ?_⟩
        show Mb *ᵥ (f ∘ y) = x
        have h7 := RingHom.map_mulVec f M y
        funext i
        have h8 := congrFun h6 i
        have h9 := congrArg f h8
        have := h7 i
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast] at h9
        rw [hm1, one_mul] at h9
        rw [← hMb] at this
        rw [← this, ← h9]
        simp [X, f]
    rw [hrk] at hMe
    have : Even n := by
      have := hGe.add hMe
      rwa [hnk] at this
    exact (Nat.not_even_iff_odd.mpr hn) this
  · have hN1 : (N : ZMod 2) = 1 := by
      obtain ⟨r, hr⟩ := hN
      rw [hr]; push_cast
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2]; simp
    have hsurj : LinearMap.range Gb.mulVecLin = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro x
      refine ⟨Mb *ᵥ x, ?_⟩
      show Gb *ᵥ (Mb *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, hGM2, hN1, one_smul, Matrix.one_mulVec]
    rw [hsurj, finrank_top, finrank_fin_fun] at hGe
    exact (Nat.not_even_iff_odd.mpr hn) hGe

end FourDvdAux

/-- **An even lattice of odd rank has level divisible by `4`.** -/
theorem four_dvd_level_of_odd (hL : ZLattice.IsEven L) {k : ℕ} (hk : finrank ℝ E = 2 * k + 1) :
    4 ∣ ZLattice.level L := by
  have hI := hL.isIntegral
  have hrank : finrank ℤ L = 2 * k + 1 := by rw [ZLattice.rank ℝ L, hk]
  let b := Module.finBasis ℤ L
  set n := finrank ℤ L with hn
  let G : Matrix (Fin n) (Fin n) ℤ := LinearMap.BilinForm.toMatrix b hI.integralForm
  have hGR : Matrix.gram ℝ (fun i ↦ (b i : E)) = G.map (Int.castRingHom ℝ) := by
    ext i j
    simp [G, LinearMap.BilinForm.toMatrix_apply, Matrix.gram_apply, hI.integralForm_cast]
  have hdet : G.det = Nat.card (ZLattice.DiscriminantGroup L) := hI.det_toMatrix_integralForm b
  have hfin := hI.finite_discriminantGroup
  have hdet0 : G.det ≠ 0 := by
    rw [hdet]; exact_mod_cast Nat.card_pos.ne'
  have hdetR : IsUnit (G.map (Int.castRingHom ℝ)).det := by
    have h : (G.map (Int.castRingHom ℝ)).det = ((G.det : ℤ) : ℝ) :=
      ((Int.castRingHom ℝ).map_det G).symm
    rw [h]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hdet0)
  obtain ⟨M, hMd, hM⟩ := (ZLattice.level_dvd_iff_gram hI b (ZLattice.level L)).mp dvd_rfl
  rw [hGR] at hM
  set GR := G.map (Int.castRingHom ℝ) with hGRdef
  have hGsymm : G.IsSymm := by
    ext i j
    simp only [Matrix.transpose_apply, G, LinearMap.BilinForm.toMatrix_apply]
    exact (hI.isSymm_integralForm.eq (b j) (b i))
  have hGRsymm : GR.IsSymm := hGsymm.map _
  have hMR : (M.map (Int.castRingHom ℝ)) = ((ZLattice.level L : ℕ) : ℝ) • GR⁻¹ := hM
  have hMsymm : M.IsSymm := by
    have h1 : (M.map (Int.castRingHom ℝ)).IsSymm := by
      rw [hMR]
      unfold Matrix.IsSymm
      rw [Matrix.transpose_smul, Matrix.transpose_nonsing_inv, hGRsymm.eq]
    ext i j
    have := congrFun (congrFun h1.eq i) j
    simp only [Matrix.transpose_apply, Matrix.map_apply] at this ⊢
    exact RingHom.injective_int (Int.castRingHom ℝ) this
  have hGM : G * M = (ZLattice.level L : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) := by
    refine Matrix.map_injective (f := Int.castRingHom ℝ) (RingHom.injective_int _) ?_
    beta_reduce
    rw [Matrix.map_mul, hMR]
    rw [← hGRdef, Matrix.mul_smul, Matrix.mul_nonsing_inv _ hdetR]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hMG : M * G = (ZLattice.level L : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) := by
    refine Matrix.map_injective (f := Int.castRingHom ℝ) (RingHom.injective_int _) ?_
    beta_reduce
    rw [Matrix.map_mul, hMR]
    rw [← hGRdef, Matrix.smul_mul, Matrix.nonsing_inv_mul _ hdetR]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hGd : ∀ i, Even (G i i) := by
    intro i
    obtain ⟨m, hm⟩ := hL (b i) (b i).2
    refine ⟨m, ?_⟩
    refine Int.cast_injective (α := ℝ) ?_
    have h1 : ((G i i : ℤ) : ℝ) = ⟪(b i : E), (b i : E)⟫ := by
      simp [G, LinearMap.BilinForm.toMatrix_apply, hI.integralForm_cast]
    rw [h1, real_inner_self_eq_norm_sq, hm]
    push_cast; ring
  exact four_dvd_of_gram_aux (hrank ▸ ⟨k, rfl⟩) G M hGsymm hMsymm hGd hMd _ hGM hMG

theorem level_orthSum_sqrtTwo_dvd_of_dvd {N : ℕ} (hN : ZLattice.level L ∣ 4 * N) :
    ZLattice.level (ZLattice.orthSum L sqrtTwoLattice) ∣ 4 * N := by
  rw [ZLattice.level_orthSum, level_sqrtTwoLattice]
  exact Nat.lcm_dvd hN (Dvd.intro N rfl)

/-- The discriminant group of `√2 ℤ` has order `2`. -/
theorem card_discriminantGroup_sqrtTwoLattice :
    Nat.card (ZLattice.DiscriminantGroup sqrtTwoLattice) = 2 := by
  have hli : LinearIndependent ℤ (sqrtTwoBasis : Fin 1 → ℝ) :=
    sqrtTwoBasis.linearIndependent.restrict_scalars' ℤ
  let b : Module.Basis (Fin 1) ℤ sqrtTwoLattice := Module.Basis.span hli
  have h := (isEven_sqrtTwoLattice.isIntegral).det_toMatrix_integralForm b
  have h2 : ((Nat.card (ZLattice.DiscriminantGroup sqrtTwoLattice) : ℕ) : ℤ) = 2 := by
    rw [← h, Matrix.det_unique]
    refine Int.cast_injective (α := ℝ) ?_
    rw [LinearMap.BilinForm.toMatrix_apply, (isEven_sqrtTwoLattice.isIntegral).integralForm_cast]
    have hb : ((b default : sqrtTwoLattice) : ℝ) = √2 := by
      simp only [b, Fin.default_eq_zero, Module.Basis.span_apply]
      simp [sqrtTwoBasis, Module.Basis.unitsSMul_apply]
    simp only [Fin.default_eq_zero] at hb ⊢
    rw [hb]
    simp
  exact_mod_cast h2

/-- The signed discriminant of `L ⊕ √2 ℤ` in odd rank `2k + 1`. -/
theorem signedDiscr_orthSum_sqrtTwo {k : ℕ} (hk : finrank ℝ E = 2 * k + 1) :
    ZLattice.signedDiscr (ZLattice.orthSum L sqrtTwoLattice) =
      (-1) ^ (k + 1) * 2 * Nat.card (ZLattice.DiscriminantGroup L) := by
  have hdim : finrank ℝ (WithLp 2 (E × ℝ)) = 2 * (k + 1) := by
    rw [finrank_withLp_prod_real, hk]; ring
  rw [ZLattice.signedDiscr_of_finrank_eq _ hdim, ZLattice.card_discriminantGroup_orthSum,
    card_discriminantGroup_sqrtTwoLattice]
  push_cast
  ring

/-- The character of the odd-rank spherical theta series modulo `4N`, for any `N` with
`level L ∣ 4N`: `χ(d) = χ'(d) χ_{-4}(d)^{k+ν+1}`, `χ'` the theta character of `L ⊕ √2ℤ`. -/
noncomputable def oddThetaCharOf (hL : ZLattice.IsEven L) {k : ℕ} (hk : finrank ℝ E = 2 * k + 1)
    (ν : ℕ) {N : ℕ} (hN : ZLattice.level L ∣ 4 * N) : DirichletCharacter ℂ (4 * N) :=
  ((isEven_orthSum_sqrtTwo hL).thetaCharacter
      ⟨k + 1, by rw [finrank_withLp_prod_real, hk]; ring⟩).changeLevel
      (level_orthSum_sqrtTwo_dvd_of_dvd hN) *
    (chi4C.changeLevel (Dvd.intro N rfl)) ^ (k + ν + 1)

/-- **The character in Kronecker form** (Shimura's normalization; see the module docstring for
Miyake's). On odd `d > 0` prime to `4N`,
`χ(d) = ((-1)^ν 2 |L^∨/L| / d)` (Jacobi symbol). -/
theorem oddThetaCharOf_natCast (hL : ZLattice.IsEven L) {k : ℕ} (hk : finrank ℝ E = 2 * k + 1)
    (ν : ℕ) {N : ℕ} (hN : ZLattice.level L ∣ 4 * N) {d : ℕ} (hd : d.Coprime (4 * N)) :
    oddThetaCharOf hL hk ν hN (d : ZMod (4 * N)) =
      (jacobiSym ((-1) ^ ν * 2 * Nat.card (ZLattice.DiscriminantGroup L)) d : ℂ) := by
  have hdZ : IsCoprime (d : ℤ) (4 * N : ℕ) := Nat.isCoprime_iff_coprime.mpr hd
  have hdL : IsCoprime (d : ℤ) (ZLattice.level (ZLattice.orthSum L sqrtTwoLattice)) :=
    hdZ.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr
      (level_orthSum_sqrtTwo_dvd_of_dvd hN))
  have hodd : Odd d := by
    have h2 : Nat.Coprime d 2 := Nat.Coprime.coprime_dvd_right
      (Dvd.intro (2 * N) (by ring) : 2 ∣ 4 * N) hd
    have h3 := (Nat.prime_two.coprime_iff_not_dvd).mp h2.symm
    exact Nat.odd_iff.mpr (by omega)
  rw [oddThetaCharOf, MulChar.mul_apply, MulChar.pow_apply' _ (by omega),
    show (d : ZMod (4 * N)) = ((d : ℤ) : ZMod (4 * N)) by simp,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hdZ,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hdZ]
  have key : ∀ hE : Even (finrank ℝ (WithLp 2 (E × ℝ))),
      (isEven_orthSum_sqrtTwo hL).thetaCharacter hE ((d : ℤ) : ZMod _) =
        (TauCeti.kroneckerSym (ZLattice.signedDiscr (ZLattice.orthSum L sqrtTwoLattice)) d : ℂ) :=
    fun hE ↦ (isEven_orthSum_sqrtTwo hL).thetaCharacter_intCast hE hdL
  erw [key, signedDiscr_orthSum_sqrtTwo hk]
  have hχ : chi4C (((d : ℤ) : ZMod 4)) = ((jacobiSym (-1) d : ℤ) : ℂ) := by
    rw [jacobiSym.at_neg_one hodd]; simp [chi4C]
  rw [hχ, TauCeti.kroneckerSym_eq_jacobiSym _ hodd]
  have hx : jacobiSym (-1) d ^ 2 = 1 := jacobiSym.sq_one (by simp)
  have hint : jacobiSym ((-1) ^ (k + 1) * 2 * (Nat.card (ZLattice.DiscriminantGroup L) : ℤ)) d *
      jacobiSym (-1) d ^ (k + ν + 1) =
        jacobiSym ((-1) ^ ν * 2 * (Nat.card (ZLattice.DiscriminantGroup L) : ℤ)) d := by
    rw [jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.mul_left,
      jacobiSym.pow_left, jacobiSym.pow_left]
    have : jacobiSym (-1) d ^ (k + 1) * jacobiSym (-1) d ^ (k + ν + 1) =
        jacobiSym (-1) d ^ ν := by
      rw [← pow_add, show k + 1 + (k + ν + 1) = 2 * (k + 1) + ν by ring, pow_add, pow_mul, hx,
        one_pow, one_mul]
    linear_combination (jacobiSym 2 d * jacobiSym (Nat.card (ZLattice.DiscriminantGroup L)) d) *
      this
  rw [← hint]
  push_cast
  ring

/-- **Miyake, Theorem 4.9.3 in odd rank at every admissible level:** for `level L ∣ 4N`, the
spherical theta series lies in Shimura's `M_{k+ν+1/2}(4N, χ)`. -/
theorem thetaSph_mem_halfIntModularForms_of_dvd (hL : ZLattice.IsEven L) {k : ℕ}
    (hk : finrank ℝ E = 2 * k + 1) {ν : ℕ} {u w : E} (hsph : IsSphericalDatum ν u w) {N : ℕ}
    (hN : ZLattice.level L ∣ 4 * N) :
    (fun τ : ℍ ↦ thetaSph L ν u w 0 τ) ∈
      HalfIntegral.halfIntModularForms (k + ν) N (oddThetaCharOf hL hk ν hN) := by
  borelize E
  refine ⟨mdifferentiable_thetaW L (polyBounded_isoForm_pow u w ν) 0, fun γ hγ τ ↦ ?_, fun γ ↦ ?_⟩
  · have hγ' : γ ∈ CongruenceSubgroup.Gamma0 (ZLattice.level (ZLattice.orthSum L sqrtTwoLattice)) := by
      have h := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hγ
      exact CongruenceSubgroup.mem_Gamma0_iff_dvd.mpr
        (dvd_trans (Int.natCast_dvd_natCast.mpr (level_orthSum_sqrtTwo_dvd_of_dvd hN)) h)
    have hd : IsCoprime (γ 1 1) (4 * N : ℕ) := by
      obtain ⟨t, ht⟩ := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hγ
      have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
        have h := γ.det_coe
        rwa [Matrix.det_fin_two] at h
      refine ⟨γ 0 0, -(γ 0 1 * t), ?_⟩
      linear_combination hdet + γ 0 1 * ht
    rw [thetaSph_smul_of_odd hL hk hsph hγ' τ, oddThetaCharOf, MulChar.mul_apply,
      MulChar.pow_apply' _ (by omega),
      DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hd,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hd]
    simp [chi4C, MulChar.ringHomComp_apply]
  · rw [cuspNorm_eq_absSlash hk]
    exact isBoundedAtImInfty_absSlash_thetaSph hL hsph γ (zero_mem _)

/-- The cusp-form version (`ν ≥ 1`) at every admissible level. -/
theorem thetaSph_mem_halfIntCuspForms_of_dvd (hL : ZLattice.IsEven L) {k : ℕ}
    (hk : finrank ℝ E = 2 * k + 1) {ν : ℕ} (hν : 1 ≤ ν) {u w : E} (hsph : IsSphericalDatum ν u w)
    {N : ℕ} (hN : ZLattice.level L ∣ 4 * N) :
    (fun τ : ℍ ↦ thetaSph L ν u w 0 τ) ∈
      HalfIntegral.halfIntCuspForms (k + ν) N (oddThetaCharOf hL hk ν hN) := by
  borelize E
  obtain ⟨h1, h2, -⟩ := thetaSph_mem_halfIntModularForms_of_dvd hL hk hsph hN
  refine ⟨h1, h2, fun γ ↦ ?_⟩
  rw [cuspNorm_eq_absSlash hk]
  exact isZeroAtImInfty_absSlash_thetaSph hL hν hsph γ (zero_mem _)

theorem level_dvd_four_mul_level_div_four (hL : ZLattice.IsEven L) {k : ℕ}
    (hk : finrank ℝ E = 2 * k + 1) : ZLattice.level L ∣ 4 * (ZLattice.level L / 4) := by
  rw [Nat.mul_div_cancel' (four_dvd_level_of_odd hL hk)]

/-- **Row 38: odd rank at the sharp level** `level L = 4 · (level L / 4)`. -/
@[kb "miyake1989" "Theorem 4.9.3 / Corollary 4.9.5 in odd rank at the sharp level: theta series of an even lattice of odd rank in M_{r/2+nu}(Gamma0(level L), chi), with 4 | level L"]
theorem thetaSph_mem_halfIntModularForms_sharp (hL : ZLattice.IsEven L) {k : ℕ}
    (hk : finrank ℝ E = 2 * k + 1) {ν : ℕ} {u w : E} (hsph : IsSphericalDatum ν u w) :
    (fun τ : ℍ ↦ thetaSph L ν u w 0 τ) ∈
      HalfIntegral.halfIntModularForms (k + ν) (ZLattice.level L / 4)
        (oddThetaCharOf hL hk ν (level_dvd_four_mul_level_div_four hL hk)) :=
  thetaSph_mem_halfIntModularForms_of_dvd hL hk hsph _

end ModularFormsKB.Miyake.Sec4_9
