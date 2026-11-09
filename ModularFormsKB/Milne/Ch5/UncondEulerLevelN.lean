import ModularFormsKB.Milne.Ch5.LevelN
import ModularFormsKB.Milne.Ch5.LevelNIso
import ModularFormsKB.Milne.Ch5.LevelNDiamond
import ModularFormsKB.Milne.Ch5.ExplicitHecke

/-!
# Milne, Proposition 5.35 unconditionally: the Euler product at level $\Gamma(N)$

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf p. 84.

Milne proves Proposition 5.35 by "essentially the same" argument as Proposition 5.1. We follow it. For a prime
$p \nmid N$ the double coset $T^N(p) = \Gamma(N)\alpha\Gamma(N)$ is the disjoint union of the $p + 1$ right cosets of
$$\begin{pmatrix} 1 & bN \\ 0 & p\end{pmatrix} \ (0 \le b < p), \qquad R_p\begin{pmatrix} p & 0 \\ 0 & 1\end{pmatrix},$$
where $R_p \in \Gamma(1)$ is congruent to $\mathrm{diag}(p^{-1}, p)$ modulo $N$ (`heckeSlashSum_heckeTNp`). On
$f = \sum a_nq_N^n$ of character $\varepsilon$ this gives $a_n(T^N(p)f) = a_{pn} + \varepsilon(p)p^{2k-1}a_{n/p}$
(`coeff_heckeTNp`), and the recursion and multiplicativity of the coefficients of a normalized eigenform follow
exactly as at level one; Miyake's Lemma 4.5.12 (`Miyake.heckeEulerFactor_iff`) turns them into the Euler product.

## Main results
- `exists_rep_of_det_prime`, `rep_injective`: the right-coset decomposition at the level of integer matrices.
- `heckeSlashSum_heckeTNp`: the explicit form of $T^N(p)$.
- `coeff_heckeTNp`: its action on $q_N$-expansions.
- `eulerProductLevelN`: **Proposition 5.35**, the named statement `EulerProductLevelN`, unconditionally.
-/

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing HeckeRing.GLn HeckeRing.GL2
  DoubleCoset

open scoped MatrixGroups ModularForm Pointwise HeckeCosetModule

namespace ModularFormsKB.Milne.UncondLevelN

variable {N p : ℕ}

def topRep (N p : ℕ) (b : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, (b : ℤ) * N; 0, p]

def botRep (p : ℕ) (σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  (σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(p : ℤ), 0; 0, 1]

theorem det_topRep (N p b : ℕ) : (topRep N p b).det = p := by
  simp [topRep, Matrix.det_fin_two]

theorem det_botRep (p : ℕ) (σ : SL(2, ℤ)) : (botRep p σ).det = p := by
  simp [botRep, Matrix.det_mul, Matrix.det_fin_two]

theorem eq_one_of_mul_eq {R : Type*} [CommRing R] {S D : Matrix (Fin 2) (Fin 2) R} (hD : IsUnit D.det)
    (h : S * D = D) : S = 1 := by
  have hinv : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D hD
  calc S = S * (D * D⁻¹) := by rw [hinv, Matrix.mul_one]
    _ = (S * D) * D⁻¹ := by rw [Matrix.mul_assoc]
    _ = 1 := by rw [h, hinv]

theorem mem_Gamma_of_mul {S : SL(2, ℤ)} {A B : Matrix (Fin 2) (Fin 2) ℤ} (hpN : p.Coprime N)
    (hA : A.map (Int.cast : ℤ → ZMod N) = !![1, 0; 0, (p : ZMod N)])
    (hB : B.map (Int.cast : ℤ → ZMod N) = !![1, 0; 0, (p : ZMod N)])
    (hSA : B = (S : Matrix (Fin 2) (Fin 2) ℤ) * A) : S ∈ Gamma N := by
  have hu : IsUnit (!![1, 0; 0, (p : ZMod N)] : Matrix (Fin 2) (Fin 2) (ZMod N)).det := by
    simpa [Matrix.det_fin_two] using (ZMod.unitOfCoprime p hpN).isUnit
  have hmap : (S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) * A.map (Int.cast : ℤ → ZMod N) =
      B.map (Int.cast : ℤ → ZMod N) := by
    rw [hSA]; exact (Matrix.map_mul (f := Int.castRingHom (ZMod N))).symm
  rw [hA, hB] at hmap
  have h1 := eq_one_of_mul_eq hu hmap
  rw [Gamma_mem']
  ext i j
  have := congrFun (congrFun h1 i) j
  simpa using this

/-- Solving for `b`: if `xw - yz ≡ 0 (mod p)` and `(x, z) ≢ 0`, some `0 ≤ b < p` has
`y ≡ xbN`, `w ≡ zbN`. -/
theorem exists_b (hp : p.Prime) (hpN : ¬ p ∣ N) {x y z w : ℤ} (hdet : x * w - y * z = p)
    (hxz : ¬ ((p : ℤ) ∣ x ∧ (p : ℤ) ∣ z)) :
    ∃ b : ℕ, b < p ∧ (p : ℤ) ∣ y - x * b * N ∧ (p : ℤ) ∣ w - z * b * N := by
  have := Fact.mk hp
  have hN : (N : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpN
  have hd : (x : ZMod p) * w - y * z = 0 := by
    have := congrArg (Int.cast : ℤ → ZMod p) hdet
    push_cast at this
    rw [this]; exact ZMod.natCast_self p
  have key : ∃ t : ZMod p, (y : ZMod p) = x * t ∧ (w : ZMod p) = z * t := by
    by_cases hx : (x : ZMod p) = 0
    · have hz : (z : ZMod p) ≠ 0 := by
        intro hz
        apply hxz
        exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp hx, (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hz⟩
      refine ⟨w / z, ?_, ?_⟩
      · rw [hx, zero_mul] at hd
        have : (y : ZMod p) * z = 0 := by linear_combination -hd
        rw [hx, zero_mul]
        exact (mul_eq_zero.mp this).resolve_right hz
      · field_simp
    · refine ⟨y / x, ?_, ?_⟩
      · field_simp
      · field_simp
        linear_combination hd
  obtain ⟨t, hy, hw⟩ := key
  refine ⟨(t / ((N : ℤ) : ZMod p)).val, ZMod.val_lt _, ?_, ?_⟩
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val]
    field_simp
    rw [hy]; ring
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val]
    field_simp
    rw [hw]; ring


theorem topRep_mod (N p b : ℕ) :
    (topRep N p b).map (Int.cast : ℤ → ZMod N) = !![1, 0; 0, (p : ZMod N)] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [topRep]

/-- **Cover**: every integer matrix of determinant `p` congruent to `diag(1, p)` lies in `Γ(N)` times one of the
representatives. -/
theorem exists_rep (hp : p.Prime) (hpN : ¬ p ∣ N) (σ : SL(2, ℤ))
    (hbot : (botRep p σ).map (Int.cast : ℤ → ZMod N) = !![1, 0; 0, (p : ZMod N)])
    {B : Matrix (Fin 2) (Fin 2) ℤ} (hdet : B.det = p)
    (hB : B.map (Int.cast : ℤ → ZMod N) = !![1, 0; 0, (p : ZMod N)]) :
    (∃ S : SL(2, ℤ), S ∈ Gamma N ∧ B = (S : Matrix (Fin 2) (Fin 2) ℤ) * botRep p σ) ∨
      ∃ b < p, ∃ S : SL(2, ℤ), S ∈ Gamma N ∧ B = (S : Matrix (Fin 2) (Fin 2) ℤ) * topRep N p b := by
  have hcop : p.Coprime N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [Matrix.det_fin_two] at hdet
  by_cases hxz : (p : ℤ) ∣ B 0 0 ∧ (p : ℤ) ∣ B 1 0
  · left
    obtain ⟨⟨x', hx'⟩, ⟨z', hz'⟩⟩ := hxz
    set B' : Matrix (Fin 2) (Fin 2) ℤ := !![x', B 0 1; z', B 1 1] with hB'
    have hdB' : B'.det = 1 := by
      have e : B'.det = x' * B 1 1 - B 0 1 * z' := by simp [hB', Matrix.det_fin_two]
      rw [e]
      apply mul_left_cancel₀ hp0
      rw [hx', hz'] at hdet
      linear_combination hdet
    have hdet' : (B' * (σ : Matrix (Fin 2) (Fin 2) ℤ).adjugate).det = 1 := by
      rw [Matrix.det_mul, Matrix.det_adjugate, hdB']
      simp
    let S : SL(2, ℤ) := ⟨_, hdet'⟩
    have hBS : B = (S : Matrix (Fin 2) (Fin 2) ℤ) * botRep p σ := by
      show B = (B' * (σ : Matrix (Fin 2) (Fin 2) ℤ).adjugate) * ((σ : Matrix (Fin 2) (Fin 2) ℤ) * _)
      have hinv : (σ : Matrix (Fin 2) (Fin 2) ℤ).adjugate * σ = 1 := by
        rw [Matrix.adjugate_mul]
        simp
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (σ : Matrix (Fin 2) (Fin 2) ℤ), hinv, Matrix.one_mul]
      ext i j; fin_cases i <;> fin_cases j <;> simp [hB', hx', hz'] <;> ring
    exact ⟨S, mem_Gamma_of_mul hcop hbot hB hBS, hBS⟩
  · right
    obtain ⟨b, hb, ⟨u, hu⟩, ⟨v, hv⟩⟩ := exists_b hp hpN hdet hxz
    set S0 : Matrix (Fin 2) (Fin 2) ℤ := !![B 0 0, u; B 1 0, v] with hS0
    have hprod : B = S0 * topRep N p b := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [hS0, topRep] <;> linarith
    have hdS : S0.det = 1 := by
      have h1 := congrArg Matrix.det hprod
      rw [Matrix.det_mul, det_topRep, Matrix.det_fin_two, hdet] at h1
      exact mul_right_cancel₀ hp0 (by rw [one_mul]; exact h1.symm)
    let S : SL(2, ℤ) := ⟨S0, hdS⟩
    exact ⟨b, hb, S, mem_Gamma_of_mul hcop (topRep_mod N p b) hB hprod, hprod⟩

/-- Distinct top representatives lie in distinct right cosets of `SL₂(ℤ)`. -/
theorem top_inj (hp : p.Prime) (hpN : ¬ p ∣ N) {b b' : ℕ} (hb : b < p) (hb' : b' < p) (S : SL(2, ℤ))
    (h : topRep N p b = (S : Matrix (Fin 2) (Fin 2) ℤ) * topRep N p b') : b = b' := by
  have := Fact.mk hp
  have h00 := congrFun (congrFun h 0) 0
  have h10 := congrFun (congrFun h 1) 0
  have h01 := congrFun (congrFun h 0) 1
  simp [topRep, Matrix.mul_apply, Fin.sum_univ_two] at h00 h10 h01
  rw [← h00] at h01
  have hz := congrArg (Int.cast : ℤ → ZMod p) h01
  push_cast at hz
  rw [ZMod.natCast_self, mul_zero, add_zero, one_mul] at hz
  have hN : (N : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpN
  have hbb := mul_right_cancel₀ hN hz
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] at hbb
  exact hbb

theorem top_ne_bot (hp : p.Prime) (b : ℕ) (σ S : SL(2, ℤ)) :
    topRep N p b ≠ (S : Matrix (Fin 2) (Fin 2) ℤ) * botRep p σ := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [topRep, botRep, Matrix.mul_apply, Fin.sum_univ_two] at h00
  have : (p : ℤ) ∣ 1 := ⟨S 0 0 * σ 0 0 + S 0 1 * σ 1 0, by linear_combination h00⟩
  have := Int.eq_one_of_dvd_one (by positivity) this
  exact hp.one_lt.ne' (by exact_mod_cast this)

theorem bot_ne_top (hp : p.Prime) (b : ℕ) (σ S : SL(2, ℤ)) :
    botRep p σ ≠ (S : Matrix (Fin 2) (Fin 2) ℤ) * topRep N p b := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  have h10 := congrFun (congrFun h 1) 0
  simp [topRep, botRep, Matrix.mul_apply, Fin.sum_univ_two] at h00 h10
  have hd := S.det_coe
  rw [Matrix.det_fin_two, ← h00, ← h10] at hd
  have : (p : ℤ) ∣ 1 := ⟨σ 0 0 * S 1 1 - S 0 1 * σ 1 0, by linear_combination -hd⟩
  have := Int.eq_one_of_dvd_one (by positivity) this
  exact hp.one_lt.ne' (by exact_mod_cast this)


/-! ### In `GL₂(ℚ)` -/

theorem det_map_ne {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det ≠ 0) :
    (A.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
  rw [show A.map (Int.cast : ℤ → ℚ) = (Int.castRingHom ℚ).mapMatrix A from rfl, ← RingHom.map_det]
  simpa using hA

/-- An integer matrix of nonzero determinant, in `GL₂(ℚ)`. -/
noncomputable def intGL (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (A.map (Int.cast : ℤ → ℚ)) (det_map_ne hA)

@[simp] theorem intGL_coe (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) :
    (intGL A hA : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) := rfl

theorem mapGL_mul_intGL (S : SL(2, ℤ)) {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det ≠ 0)
    (hSA : ((S : Matrix (Fin 2) (Fin 2) ℤ) * A).det ≠ 0) :
    mapGL ℚ S * intGL A hA = intGL ((S : Matrix (Fin 2) (Fin 2) ℤ) * A) hSA := by
  refine Units.ext ?_
  rw [Units.val_mul, intGL_coe, intGL_coe, Matrix.map_mul_intCast, mapGL_coe_matrix]
  congr 1

theorem det_mapGL (S : SL(2, ℤ)) : ((mapGL ℚ S : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
  rw [mapGL_coe_matrix]
  exact (SpecialLinearGroup.map (algebraMap ℤ ℚ) S).2

theorem det_eq_of_mem_dc {g y : GL (Fin 2) ℚ} (h : y ∈ doubleCoset g (SLnZ 2 : Set (GL (Fin 2) ℚ)) (SLnZ 2)) :
    (y : Matrix (Fin 2) (Fin 2) ℚ).det = (g : Matrix (Fin 2) (Fin 2) ℚ).det := by
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset.mp h
  obtain ⟨s, rfl⟩ := (mem_SLnZ_iff 2).mp hu
  obtain ⟨t, rfl⟩ := (mem_SLnZ_iff 2).mp hv
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
  have h1 := det_mapGL s
  have h2 := det_mapGL t
  simp only [mapGL] at h1 h2
  rw [show ((s : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = 1 from h1,
    show ((t : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = 1 from h2]
  ring


theorem intGL_mul {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det ≠ 0) (hB : B.det ≠ 0) (hAB : (A * B).det ≠ 0) :
    intGL A hA * intGL B hB = intGL (A * B) hAB := by
  refine Units.ext ?_
  rw [Units.val_mul, intGL_coe, intGL_coe, intGL_coe, Matrix.map_mul_intCast]

theorem mapGL_eq_intGL (S : SL(2, ℤ)) : mapGL ℚ S = intGL (S : Matrix (Fin 2) (Fin 2) ℤ) (by simp) := by
  refine Units.ext ?_
  rw [intGL_coe, mapGL_coe_matrix]
  rfl

theorem natDiagGL_eq_intGL (a d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    natDiagGL 2 ![a, d] = intGL !![(a : ℤ), 0; 0, d] (by simp [Matrix.det_fin_two_of, ha.ne', hd.ne']) := by
  have ha' : ∀ i, 0 < (![a, d] : Fin 2 → ℕ) i := by intro i; fin_cases i <;> simpa
  refine Units.ext ?_
  rw [natDiagGL_coe_eq_map_intCast 2 _ ha', intGL_coe]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem mem_DeltaN_intGL {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det = p) (hp : 0 < p) (hcop : p.Coprime N)
    (hmod : A.map (Int.cast : ℤ → ZMod N) = !![1, 0; 0, (p : ZMod N)]) :
    intGL A (by rw [hA]; exact_mod_cast hp.ne') ∈ DeltaN N :=
  ⟨A, rfl, by rw [hA]; exact_mod_cast hp, by rw [hA]; exact Nat.isCoprime_iff_coprime.mpr hcop,
    by rw [hmod, hA]; simp⟩

/-! ### The representatives -/

/-- `R_p ∈ SL₂(ℤ)`, congruent to `diag(p⁻¹, p)` modulo `N`: the matrix the operator `R_p` (`diamondN`) slashes by. -/
noncomputable def sigmaP (N p : ℕ) [NeZero N] (hcop : p.Coprime N) : SL(2, ℤ) :=
  (exists_diamondRep N (ZMod.unitOfCoprime p hcop)).choose

theorem botRep_mod [NeZero N] (hcop : p.Coprime N) :
    (botRep p (sigmaP N p hcop)).map (Int.cast : ℤ → ZMod N) = !![1, 0; 0, (p : ZMod N)] := by
  have hσ := (exists_diamondRep N (ZMod.unitOfCoprime p hcop)).choose_spec
  have hu : ((ZMod.unitOfCoprime p hcop : (ZMod N)ˣ) : ZMod N) = (p : ZMod N) := ZMod.coe_unitOfCoprime p hcop
  have hinv : (((ZMod.unitOfCoprime p hcop)⁻¹ : (ZMod N)ˣ) : ZMod N) * (p : ZMod N) = 1 := by
    rw [← hu]; exact Units.inv_mul _
  have h2 : ((sigmaP N p hcop : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) =
      !![(((ZMod.unitOfCoprime p hcop)⁻¹ : (ZMod N)ˣ) : ZMod N), 0; 0,
        ((ZMod.unitOfCoprime p hcop : (ZMod N)ˣ) : ZMod N)] := hσ
  rw [botRep, Matrix.map_mul_intCast, h2, hu]
  ext i j; fin_cases i <;> fin_cases j <;> simp [hinv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
    dotProduct]


theorem intGL_congr {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det ≠ 0) (hB : B.det ≠ 0) (h : A = B) :
    intGL A hA = intGL B hB := by subst h; rfl

theorem coprime_of (hp : p.Prime) (hpN : ¬ p ∣ N) : p.Coprime N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN

theorem det_ne_of_prime (hp : p.Prime) {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det = p) : A.det ≠ 0 := by
  rw [hA]; exact_mod_cast hp.ne_zero

/-- The `p + 1` representatives of the right cosets of `Γ(N)` in `T^N(p)`: `none` is `R_p diag(p, 1)`, `some b` is
`[[1, bN], [0, p]]`. -/
noncomputable def reps (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : ¬ p ∣ N) : Option (Fin p) → GL (Fin 2) ℚ
  | none => intGL (botRep p (sigmaP N p (coprime_of hp hpN))) (det_ne_of_prime hp (det_botRep _ _))
  | some b => intGL (topRep N p b) (det_ne_of_prime hp (det_topRep _ _ _))

section reps

variable [NeZero N] (hp : p.Prime) (hpN : ¬ p ∣ N)

theorem reps_mem_DeltaN (i : Option (Fin p)) : reps N p hp hpN i ∈ DeltaN N := by
  cases i with
  | none => exact mem_DeltaN_intGL (det_botRep _ _) hp.pos (coprime_of hp hpN) (botRep_mod _)
  | some b => exact mem_DeltaN_intGL (det_topRep _ _ _) hp.pos (coprime_of hp hpN) (topRep_mod _ _ _)

theorem reps_mem_dc_diag (i : Option (Fin p)) :
    reps N p hp hpN i ∈ doubleCoset (natDiagGL 2 ![1, p]) (SLnZ 2 : Set (GL (Fin 2) ℚ)) (SLnZ 2) := by
  have hdiag := natDiagGL_eq_intGL 1 p one_pos hp.pos
  cases i with
  | none =>
    refine mem_doubleCoset.mpr ⟨mapGL ℚ (sigmaP N p (coprime_of hp hpN) * ModularGroup.S), coe_mem_SLnZ 2 _,
      mapGL ℚ ModularGroup.S⁻¹, coe_mem_SLnZ 2 _, ?_⟩
    rw [hdiag, mapGL_eq_intGL, mapGL_eq_intGL, intGL_mul, intGL_mul]
    · exact intGL_congr (det_ne_of_prime hp (det_botRep _ _)) _ (by
        rw [botRep, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, Matrix.mul_assoc]
        congr 1
        rw [Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_S, Matrix.adjugate_fin_two]
        ext i j; fin_cases i <;> fin_cases j <;> simp)
    all_goals simp only [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, Matrix.det_fin_two_of]; simp [hp.ne_zero]
  | some b =>
    refine mem_doubleCoset.mpr ⟨1, one_mem _, mapGL ℚ (ModularGroup.T ^ ((b : ℤ) * N)), coe_mem_SLnZ 2 _, ?_⟩
    rw [one_mul, hdiag, mapGL_eq_intGL, intGL_mul]
    · exact intGL_congr (det_ne_of_prime hp (det_topRep _ _ _)) _ (by
        rw [show ((ModularGroup.T ^ ((b : ℤ) * N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
          !![1, (b : ℤ) * N; 0, 1] from ModularGroup.coe_T_zpow _]
        ext i j; fin_cases i <;> fin_cases j <;> simp [topRep])
    all_goals simp only [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, Matrix.det_fin_two_of]; simp [hp.ne_zero]


theorem det_map_int (A : Matrix (Fin 2) (Fin 2) ℤ) : (A.map (Int.cast : ℤ → ℚ)).det = (A.det : ℚ) :=
  ((Int.castRingHom ℚ).map_det A).symm

theorem eq_of_mapGL_mul {S : SL(2, ℤ)} {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (h : mapGL ℚ S * intGL B hB = intGL A hA) : A = (S : Matrix (Fin 2) (Fin 2) ℤ) * B := by
  have h1 := congrArg (fun g : GL (Fin 2) ℚ ↦ (g : Matrix (Fin 2) (Fin 2) ℚ)) h
  simp only [Units.val_mul, intGL_coe, mapGL_coe_matrix] at h1
  have h2 : ((S : Matrix (Fin 2) (Fin 2) ℤ) * B).map (Int.cast : ℤ → ℚ) = A.map (Int.cast : ℤ → ℚ) := by
    rw [Matrix.map_mul_intCast, ← h1]; rfl
  exact (Matrix.map_injective Int.cast_injective h2).symm

theorem mem_dc_imp {g0 : GL (Fin 2) ℚ} (hg0Δ : g0 ∈ DeltaN N)
    (hg0 : g0 ∈ doubleCoset (natDiagGL 2 ![1, p]) (SLnZ 2 : Set (GL (Fin 2) ℚ)) (SLnZ 2)) {x : GL (Fin 2) ℚ}
    (hx : x ∈ doubleCoset g0 (GammaGL N : Set (GL (Fin 2) ℚ)) (GammaGL N)) :
    ∃ (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det = p), x = intGL B (det_ne_of_prime hp hB) ∧
      B.map (Int.cast : ℤ → ZMod N) = !![1, 0; 0, (p : ZMod N)] := by
  have hxΔ : x ∈ DeltaN N := by
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset.mp hx
    exact mul_mem (mul_mem (IsHeckeTriple.mem_of_mem_left (GammaGL N) hu) hg0Δ)
      (IsHeckeTriple.mem_of_mem_right (GammaGL N) hv)
  have hdet : (x : Matrix (Fin 2) (Fin 2) ℚ).det = p := by
    rw [det_eq_of_mem_dc (mem_dc_SL_of_mem_dc_Gamma hx), det_eq_of_mem_dc hg0,
      natDiagGL_eq_intGL 1 p one_pos hp.pos, intGL_coe, det_map_int]
    simp [Matrix.det_fin_two_of]
  obtain ⟨A, hA, hdA, hcA, hmA⟩ := hxΔ
  have hAp : A.det = p := by
    have : ((A.det : ℤ) : ℚ) = p := by rw [← hdet, hA, det_map_int]
    exact_mod_cast this
  exact ⟨A, hAp, Units.ext (by rw [intGL_coe]; exact hA), by rw [hmA, hAp]; simp⟩

/-- **The cover**: the double coset of `T^N(p)` is the union of the right cosets `Γ(N) aᵢ`. -/
theorem dc_eq {g0 : GL (Fin 2) ℚ} (hg0Δ : g0 ∈ DeltaN N)
    (hg0 : g0 ∈ doubleCoset (natDiagGL 2 ![1, p]) (SLnZ 2 : Set (GL (Fin 2) ℚ)) (SLnZ 2)) :
    doubleCoset g0 (GammaGL N : Set (GL (Fin 2) ℚ)) (GammaGL N) =
      ⋃ i, MulOpposite.op (reps N p hp hpN i) • (GammaGL N : Set (GL (Fin 2) ℚ)) := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · intro hx
    obtain ⟨B, hB, rfl, hmod⟩ := mem_dc_imp hp hg0Δ hg0 hx
    rcases exists_rep hp hpN _ (botRep_mod (coprime_of hp hpN)) hB hmod with ⟨S, hS, hBS⟩ | ⟨b, hb, S, hS, hBS⟩
    · refine ⟨none, Set.mem_smul_set.mpr ⟨mapGL ℚ S, Subgroup.mem_map_of_mem _ hS, ?_⟩⟩
      rw [op_smul_eq_mul]
      exact (mapGL_mul_intGL S (det_ne_of_prime hp (det_botRep _ _))
        (by rw [← hBS]; exact det_ne_of_prime hp hB)).trans (intGL_congr _ _ hBS.symm)
    · refine ⟨some ⟨b, hb⟩, Set.mem_smul_set.mpr ⟨mapGL ℚ S, Subgroup.mem_map_of_mem _ hS, ?_⟩⟩
      rw [op_smul_eq_mul]
      exact (mapGL_mul_intGL S (det_ne_of_prime hp (det_topRep _ _ _))
        (by rw [← hBS]; exact det_ne_of_prime hp hB)).trans (intGL_congr _ _ hBS.symm)
  · rintro ⟨i, hi⟩
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hi
    rw [op_smul_eq_mul]
    refine mul_mem_doubleCoset_left hy (mem_doubleCoset_Gamma_of_SL hg0Δ (reps_mem_DeltaN hp hpN i) ?_)
    rw [DoubleCoset.doubleCoset_eq_of_mem hg0]
    exact reps_mem_dc_diag hp hpN i

/-- **Disjointness**: the right cosets `Γ(N) aᵢ` are pairwise distinct. -/
theorem reps_inj :
    Function.Injective fun i ↦ MulOpposite.op (reps N p hp hpN i) • (GammaGL N : Set (GL (Fin 2) ℚ)) := by
  intro i j hij
  have hmem : reps N p hp hpN i ∈ MulOpposite.op (reps N p hp hpN j) • (GammaGL N : Set (GL (Fin 2) ℚ)) := by
    have hij' : MulOpposite.op (reps N p hp hpN i) • (GammaGL N : Set (GL (Fin 2) ℚ)) =
        MulOpposite.op (reps N p hp hpN j) • (GammaGL N : Set (GL (Fin 2) ℚ)) := hij
    rw [← hij']
    exact Set.mem_smul_set.mpr ⟨1, one_mem _, by rw [op_smul_eq_mul, one_mul]⟩
  obtain ⟨y, hy, hyeq⟩ := Set.mem_smul_set.mp hmem
  rw [op_smul_eq_mul] at hyeq
  obtain ⟨S, -, rfl⟩ := Subgroup.mem_map.mp hy
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some b => exact absurd (eq_of_mapGL_mul (det_ne_of_prime hp (det_botRep _ _)) (det_ne_of_prime hp (det_topRep _ _ _)) hyeq) (bot_ne_top hp b _ S)
  | some b =>
    cases j with
    | none => exact absurd (eq_of_mapGL_mul (det_ne_of_prime hp (det_topRep _ _ _)) (det_ne_of_prime hp (det_botRep _ _)) hyeq) (top_ne_bot hp b _ S)
    | some b' =>
      have := top_inj hp hpN b.2 b'.2 S (eq_of_mapGL_mul (det_ne_of_prime hp (det_topRep _ _ _)) (det_ne_of_prime hp (det_topRep _ _ _)) hyeq)
      rw [Fin.ext this]

end reps


/-! ### The operator `T^N(p)` -/

section operator

theorem heckeTN_prime [NeZero N] (hp : p.Prime) : heckeTN N p = heckeTNDiag N 1 p := by
  have h : (p.divisorsAntidiagonal.filter (fun ad : ℕ × ℕ ↦ ad.1 ∣ ad.2)) = {(1, p)} := by
    ext ⟨a, d⟩
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨had, -⟩, hdvd⟩
      have ha : a ∣ p := ⟨d, had.symm⟩
      rcases (Nat.dvd_prime hp).mp ha with h1 | h1
      · rw [h1] at had ⊢
        exact ⟨rfl, by simpa using had⟩
      · rw [h1] at had hdvd
        have : d = 1 := Nat.eq_of_mul_eq_mul_left hp.pos (by rw [had, mul_one])
        rw [this] at hdvd
        exact absurd (Nat.le_of_dvd one_pos hdvd) (by have := hp.one_lt; omega)
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨one_mul _, hp.ne_zero⟩, one_dvd _⟩
  rw [heckeTN, h, Finset.sum_singleton]

theorem doubleCoset_out_mk [NeZero N] (g0 : DeltaN N) :
    doubleCoset ((Quotient.out (HeckeCoset.mk (GammaGL N) (GammaGL N) g0) : DeltaN N) : GL (Fin 2) ℚ)
      (GammaGL N : Set (GL (Fin 2) ℚ)) (GammaGL N) = doubleCoset (g0 : GL (Fin 2) ℚ) (GammaGL N : Set _) (GammaGL N) := by
  rw [← HeckeCoset.rep_def, ← HeckeCoset.toSet_eq_doubleCoset_rep, HeckeCoset.toSet_mk]

/-- **The explicit form of `T^N(p)`**: on a form of level `Γ(N)`, `T^N(p)` is the sum of the slashes by the `p + 1`
representatives `reps`. -/
theorem coe_heckeActN_heckeTN_prime [NeZero N] (hp : p.Prime) (hpN : ¬ p ∣ N) (k : ℕ) (f : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)) :
    ⇑(heckeActN N k (heckeTN N p) f) = ∑ i, ⇑f ∣[(2 * k : ℤ)] reps N p hp hpN i := by
  have hex := exists_DeltaN_mem_diag N one_pos hp.pos (by simpa using coprime_of hp hpN)
  rw [heckeTN_prime hp, heckeTNDiag, dite_eq_left hex, heckeActN, HeckeCosetModule.single]
  erw [Finsupp.linearCombination_single]
  rw [one_smul]
  refine coe_heckeSlashModularFormEnd_eq_sum _ _ _ _ ?_ (reps_inj hp hpN) f
  rw [doubleCoset_out_mk]
  exact dc_eq hp hpN hex.choose.2 hex.choose_spec

end operator


/-! ### Slash formulas -/

local notation "φ" => Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℚ ℝ)

theorem intGL_det_pos {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det ≠ 0) (hpos : 0 < A.det) :
    0 < ((intGL A hA : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
  rw [intGL_coe, det_map_int]; exact_mod_cast hpos

theorem phi_intGL_apply {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det ≠ 0) (i j : Fin 2) :
    (φ (intGL A hA) : GL (Fin 2) ℝ) i j = (A i j : ℝ) := by
  simp [Matrix.GeneralLinearGroup.map, intGL]

theorem coe_phi_intGL_smul {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det ≠ 0) (hpos : 0 < A.det) (z : ℍ) :
    ((φ (intGL A hA) • z : ℍ) : ℂ) = (A 0 0 * (z : ℂ) + A 0 1) / (A 1 0 * (z : ℂ) + A 1 1) := by
  rw [coe_smul_of_det_pos (ModularForm.det_map_ratCast_pos (intGL_det_pos hA hpos)), num, denom]
  simp [phi_intGL_apply]

theorem slash_intGL_apply (w : ℤ) {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det ≠ 0) (hpos : 0 < A.det)
    (F : ℍ → ℂ) (z : ℍ) :
    (F ∣[w] intGL A hA) z = F (φ (intGL A hA) • z) * (A.det : ℂ) ^ (w - 1) *
      (A 1 0 * (z : ℂ) + A 1 1) ^ (-w) := by
  rw [ModularForm.rat_slash_apply_of_det_pos w (intGL_det_pos hA hpos), denom]
  have hd : ((φ (intGL A hA)).det : ℝ) = (A.det : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two]
    simp [phi_intGL_apply]
  rw [hd, abs_of_pos (by exact_mod_cast hpos), phi_intGL_apply, phi_intGL_apply]
  simp only [Complex.ofReal_zpow, Complex.ofReal_intCast]


/-! ### `q_N`-expansions -/

theorem N_mem_strictPeriods (N : ℕ) : (N : ℝ) ∈ ((Gamma N).map (mapGL ℝ)).strictPeriods := by
  have := strictPeriods_Gamma N
  erw [this]
  exact AddSubgroup.mem_zmultiples _

theorem hasSum_qN [NeZero N] {w : ℤ} (f : ModularForm ((Gamma N).map (mapGL ℝ)) w) (τ : ℍ) :
    HasSum (fun m ↦ (qExpansion N f).coeff m * Function.Periodic.qParam N τ ^ m) (f τ) :=
  ModularForm.hasSum_qExpansion (f := f) (hh := by exact_mod_cast (NeZero.pos N))
    (hΓ := N_mem_strictPeriods N) τ


/-- The top representative `[[1, bN], [0, p]]` in `GL₂(ℚ)` (for any prime `p`). -/
noncomputable abbrev topGL (N p : ℕ) (hp : p.Prime) (b : ℕ) : GL (Fin 2) ℚ :=
  intGL (topRep N p b) (det_ne_of_prime hp (det_topRep _ _ _))

section expansion

variable [NeZero N] (hp : p.Prime) (hpN : ¬ p ∣ N) (k : ℕ)

theorem slash_top_apply (F : ℍ → ℂ) (b : Fin p) (z : ℍ) :
    (F ∣[(2 * k : ℤ)] topGL N p hp b) z = (p : ℂ)⁻¹ * F (φ (topGL N p hp b) • z) := by
  have hpos : 0 < (topRep N p b).det := by rw [det_topRep]; exact_mod_cast hp.pos
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [slash_intGL_apply _ _ hpos, det_topRep]
  simp only [topRep, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_zero, zero_mul, zero_add,
    Int.cast_natCast]
  rw [mul_assoc, ← zpow_add₀ hpC, show (2 * k : ℤ) - 1 + -(2 * k : ℤ) = -1 by ring, _root_.zpow_neg_one, mul_comm]
  rfl

theorem qParam_top (b : Fin p) (z : ℍ) :
    Function.Periodic.qParam N ((φ (topGL N p hp b) • z : ℍ) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (p * N)) *
        Complex.exp (2 * Real.pi * Complex.I * (((b : ℕ) : ℂ) / p)) := by
  have hpos : 0 < (topRep N p b).det := by rw [det_topRep]; exact_mod_cast hp.pos
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  rw [Function.Periodic.qParam, ← Complex.exp_add, coe_phi_intGL_smul _ hpos]
  congr 1
  simp only [topRep, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  push_cast
  field_simp
  rw [mul_zero, zero_add, mul_div_cancel_right₀ _ hpC]


/-- The top representatives contribute $\sum_n a_{pn}q_N^n$. -/
theorem hasSum_top (f : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)) (z : ℍ) :
    HasSum (fun j : ℕ ↦ (qExpansion N f).coeff (p * j) * Function.Periodic.qParam N (z : ℂ) ^ j)
      (∑ b : Fin p, (⇑f ∣[(2 * k : ℤ)] topGL N p hp b) z) := by
  set c : ℕ → ℂ := fun n ↦ (qExpansion N f).coeff n with hc
  set w := Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (p * N)) with hw
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hS : ∀ b ∈ (Finset.univ : Finset (Fin p)), HasSum
      (fun n ↦ (p : ℂ)⁻¹ * (c n * (w * Complex.exp (2 * Real.pi * Complex.I * (((b : ℕ) : ℂ) / p))) ^ n))
      ((⇑f ∣[(2 * k : ℤ)] topGL N p hp b) z) := by
    intro b _
    rw [slash_top_apply, ← qParam_top hp b z]
    exact (hasSum_qN f _).mul_left _
  have hT := hasSum_sum hS
  have hP : ∀ n : ℕ, ∑ b : Fin p, (p : ℂ)⁻¹ *
      (c n * (w * Complex.exp (2 * Real.pi * Complex.I * (((b : ℕ) : ℂ) / p))) ^ n) =
      if p ∣ n then c n * w ^ n else 0 := by
    intro n
    have h1 : ∑ b : Fin p, (p : ℂ)⁻¹ *
        (c n * (w * Complex.exp (2 * Real.pi * Complex.I * (((b : ℕ) : ℂ) / p))) ^ n) =
        (p : ℂ)⁻¹ * c n * w ^ n * ∑ b ∈ Finset.range p,
          (Complex.exp (2 * Real.pi * Complex.I * ((b : ℂ) / p))) ^ n := by
      rw [Finset.mul_sum, Finset.sum_range]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rw [mul_pow]; ring
    rw [h1, sum_exp_roots hp.pos n]
    split_ifs
    · field_simp
    · simp
  rw [show (fun n : ℕ ↦ ∑ b : Fin p, (p : ℂ)⁻¹ *
      (c n * (w * Complex.exp (2 * Real.pi * Complex.I * (((b : ℕ) : ℂ) / p))) ^ n)) =
      fun n ↦ if p ∣ n then c n * w ^ n else 0 from funext hP] at hT
  have hinj : Function.Injective (fun j : ℕ ↦ p * j) := fun x y h ↦ Nat.eq_of_mul_eq_mul_left hp.pos h
  have hoff : ∀ x, x ∉ Set.range (fun j : ℕ ↦ p * j) → (if p ∣ x then c x * w ^ x else 0) = 0 := by
    intro x hx
    rw [if_neg]
    rintro ⟨j, rfl⟩
    exact hx ⟨j, rfl⟩
  have hT2 := (hinj.hasSum_iff hoff).mpr hT
  refine hT2.congr_fun fun j ↦ ?_
  simp only [Function.comp_apply, if_pos (dvd_mul_right p j)]
  congr 1
  rw [pow_mul, hw, ← Complex.exp_nat_mul, Function.Periodic.qParam]
  congr 2
  push_cast
  field_simp


/-- `diag(p, 1)`. -/
def diagP (p : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(p : ℤ), 0; 0, 1]

theorem det_diagP (p : ℕ) : (diagP p).det = p := by simp [diagP, Matrix.det_fin_two]

theorem reps_none_eq : reps N p hp hpN none =
    mapGL ℚ (sigmaP N p (coprime_of hp hpN)) * intGL (diagP p) (det_ne_of_prime hp (det_diagP p)) :=
  (mapGL_mul_intGL _ _ (det_ne_of_prime hp (det_botRep _ _))).symm

theorem slash_diagP_apply (F : ℍ → ℂ) (z : ℍ) :
    (F ∣[(2 * k : ℤ)] intGL (diagP p) (det_ne_of_prime hp (det_diagP p))) z =
      (p : ℂ) ^ ((2 * k : ℤ) - 1) * F (φ (intGL (diagP p) (det_ne_of_prime hp (det_diagP p))) • z) := by
  have hpos : 0 < (diagP p).det := by rw [det_diagP]; exact_mod_cast hp.pos
  rw [slash_intGL_apply _ _ hpos, det_diagP]
  simp [diagP, mul_comm]

theorem qParam_diagP (z : ℍ) :
    Function.Periodic.qParam N ((φ (intGL (diagP p) (det_ne_of_prime hp (det_diagP p))) • z : ℍ) : ℂ) =
      Function.Periodic.qParam N (z : ℂ) ^ p := by
  have hpos : 0 < (diagP p).det := by rw [det_diagP]; exact_mod_cast hp.pos
  rw [coe_phi_intGL_smul _ hpos, Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  simp [diagP]
  ring

/-- The bottom representative: on a form of character `ε`, `f | R_p diag(p, 1) = ε(p) f | diag(p, 1)`. -/
theorem slash_reps_none {ε : (ZMod N)ˣ →* ℂˣ} (f : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k))
    (hf : f ∈ charSpaceN N k ε) :
    ⇑f ∣[(2 * k : ℤ)] reps N p hp hpN none = (ε (ZMod.unitOfCoprime p (coprime_of hp hpN)) : ℂ) •
      (⇑f ∣[(2 * k : ℤ)] intGL (diagP p) (det_ne_of_prime hp (det_diagP p))) := by
  rw [reps_none_eq, SlashAction.slash_mul]
  have h1 : ⇑f ∣[(2 * k : ℤ)] (mapGL ℚ (sigmaP N p (coprime_of hp hpN))) =
      ⇑(diamondN N k (ZMod.unitOfCoprime p (coprime_of hp hpN)) f) := by
    rw [ModularForm.rat_slash, map_mapGL_rat_real, coe_diamondN]
    rfl
  have hd := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hf (ZMod.unitOfCoprime p (coprime_of hp hpN)))
  rw [h1, hd, FunLike.coe_smul, ModularForm.rat_smul_slash_of_det_pos _
    (intGL_det_pos _ (by rw [det_diagP]; exact_mod_cast hp.pos))]


/-- The bottom representative contributes $\varepsilon(p)p^{2k-1}\sum_n a_nq_N^{pn}$. -/
theorem hasSum_bot {ε : (ZMod N)ˣ →* ℂˣ} (f : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k))
    (hf : f ∈ charSpaceN N k ε) (z : ℍ) :
    HasSum (fun m : ℕ ↦ if p ∣ m then (ε (ZMod.unitOfCoprime p (coprime_of hp hpN)) : ℂ) * (p : ℂ) ^ ((2 * k : ℤ) - 1) *
        (qExpansion N f).coeff (m / p) * Function.Periodic.qParam N (z : ℂ) ^ m else 0)
      ((⇑f ∣[(2 * k : ℤ)] reps N p hp hpN none) z) := by
  set e := (ε (ZMod.unitOfCoprime p (coprime_of hp hpN)) : ℂ)
  rw [slash_reps_none hp hpN k f hf, Pi.smul_apply, slash_diagP_apply hp k, smul_eq_mul]
  have h := ((hasSum_qN f (φ (intGL (diagP p) (det_ne_of_prime hp (det_diagP p))) • z)).mul_left
    ((p : ℂ) ^ ((2 * k : ℤ) - 1))).mul_left e
  rw [qParam_diagP hp z] at h
  have hinj : Function.Injective (fun j : ℕ ↦ p * j) := fun x y h ↦ Nat.eq_of_mul_eq_mul_left hp.pos h
  have hoff : ∀ x, x ∉ Set.range (fun j : ℕ ↦ p * j) → (if p ∣ x then e * (p : ℂ) ^ ((2 * k : ℤ) - 1) *
      (qExpansion N f).coeff (x / p) * Function.Periodic.qParam N (z : ℂ) ^ x else 0) = 0 := by
    intro x hx
    rw [ite_eq_right_iff]
    rintro ⟨j, rfl⟩
    exact absurd ⟨j, rfl⟩ hx
  refine (hinj.hasSum_iff hoff).mp ?_
  refine h.congr_fun fun j ↦ ?_
  simp only [Function.comp_apply, if_pos (dvd_mul_right p j), Nat.mul_div_cancel_left j hp.pos, ← pow_mul]
  ring

/-- **The action of `T^N(p)` on `q_N`-expansions**: for `f` of character `ε` and `p ∤ N` prime,
$a_n(T^N(p)f) = a_{pn}(f) + \varepsilon(p)p^{2k-1}a_{n/p}(f)$ (the last term only when $p \mid n$). -/
theorem coeff_heckeTNp {ε : (ZMod N)ˣ →* ℂˣ} (f : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k))
    (hf : f ∈ charSpaceN N k ε) (n : ℕ) :
    (qExpansion N (heckeActN N k (heckeTN N p) f)).coeff n = (qExpansion N f).coeff (p * n) +
      if p ∣ n then (ε (ZMod.unitOfCoprime p (coprime_of hp hpN)) : ℂ) * (p : ℂ) ^ ((2 * k : ℤ) - 1) *
        (qExpansion N f).coeff (n / p) else 0 := by
  refine (ModularFormClass.qExpansion_coeff_unique (by exact_mod_cast (NeZero.pos N)) (N_mem_strictPeriods N)
    (f := heckeActN N k (heckeTN N p) f) (c := fun n ↦ (qExpansion N f).coeff (p * n) +
      if p ∣ n then (ε (ZMod.unitOfCoprime p (coprime_of hp hpN)) : ℂ) * (p : ℂ) ^ ((2 * k : ℤ) - 1) *
        (qExpansion N f).coeff (n / p) else 0) (fun τ ↦ ?_) n).symm
  rw [coe_heckeActN_heckeTN_prime hp hpN, Finset.sum_apply, Fintype.sum_option, add_comm]
  refine ((hasSum_top hp k f τ).add (hasSum_bot hp hpN k f hf τ)).congr_fun fun m ↦ ?_
  split_ifs <;> simp [smul_eq_mul] <;> ring

end expansion


/-! ### From the recursion to multiplicativity -/

section mult

variable (N) (a cst : ℕ → ℂ) (ha1 : a 1 = 1)
  (hrec : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
    a (p * n) = a p * a n - if p ∣ n then cst p * a (n / p) else 0)
include ha1 hrec

theorem rec_prime_pow_mul {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) {n : ℕ} (hn : ¬ p ∣ n) (e : ℕ) :
    a (p ^ e * n) = a (p ^ e) * a n := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  match e, ih with
  | 0, _ => simp [ha1]
  | 1, _ => simp only [pow_one]; rw [hrec p hp hpN n, if_neg hn, sub_zero]
  | e + 2, ih =>
    have h1 : p ^ (e + 2) * n = p * (p ^ (e + 1) * n) := by ring
    have h2 : p ^ (e + 2) = p * (p ^ (e + 1)) := by ring
    have hd1 : p ∣ p ^ (e + 1) * n := ⟨p ^ e * n, by ring⟩
    have hd2 : p ∣ p ^ (e + 1) := ⟨p ^ e, by ring⟩
    have q1 : p ^ (e + 1) * n / p = p ^ e * n := by
      rw [show p ^ (e + 1) * n = p * (p ^ e * n) by ring, Nat.mul_div_cancel_left _ hp.pos]
    have q2 : p ^ (e + 1) / p = p ^ e := by
      rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
    rw [h1, hrec p hp hpN, if_pos hd1, q1, h2, hrec p hp hpN, if_pos hd2, q2, ih (e + 1) (by omega),
      ih e (by omega)]
    ring

theorem mult_of_rec : ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime N → m.Coprime n → a (m * n) = a m * a n := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro n hm hn hmN hmn
  by_cases h1 : m = 1
  · subst h1; simp [ha1]
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd h1
  obtain ⟨e, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp.ne_one
  have he : e ≠ 0 := by
    rintro rfl
    simp only [pow_zero, one_mul] at hpm
    exact hm' hpm
  have hm'pos : 0 < m' := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
  have hpN : ¬ p ∣ N := (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.Coprime.coprime_dvd_left hpm hmN)
  have hpn : ¬ p ∣ n := (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.Coprime.coprime_dvd_left hpm hmn)
  have hm'N : m'.Coprime N := Nat.Coprime.coprime_dvd_left (dvd_mul_left m' _) hmN
  have hm'n : m'.Coprime n := Nat.Coprime.coprime_dvd_left (dvd_mul_left m' _) hmn
  have hlt : m' < p ^ e * m' := by
    have : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow he p)
    nlinarith
  have hpmn : ¬ p ∣ m' * n := fun h ↦ (hp.dvd_mul.mp h).elim hm' hpn
  rw [mul_assoc, rec_prime_pow_mul N a cst ha1 hrec hp hpN hpmn, ih m' hlt n hm'pos hn hm'N hm'n,
    rec_prime_pow_mul N a cst ha1 hrec hp hpN hm']
  ring

end mult


/-! ### Proposition 5.35 -/

section euler

variable [NeZero N]

theorem charWeight_prime (k : ℕ) (hk : 1 ≤ k) (ε : (ZMod N)ˣ →* ℂˣ) (hcop : p.Coprime N) :
    (p : ℂ) * charWeight N k ε p = (ε (ZMod.unitOfCoprime p hcop) : ℂ) * (p : ℂ) ^ ((2 * k : ℤ) - 1) := by
  rw [charWeight, ← ZMod.coe_unitOfCoprime p hcop, MulChar.ofUnitHom_coe,
    show ((2 * k : ℤ) - 1) = ((2 * k - 2 + 1 : ℕ) : ℤ) by omega, zpow_natCast, pow_succ]
  ring

theorem charWeight_of_not_coprime (k : ℕ) (ε : (ZMod N)ˣ →* ℂˣ) {n : ℕ} (hn : ¬ n.Coprime N) :
    charWeight N k ε n = 0 := by
  rw [charWeight, MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime]), zero_mul]

theorem charWeight_one (k : ℕ) (ε : (ZMod N)ˣ →* ℂˣ) : charWeight N k ε 1 = 1 := by
  simp [charWeight]

theorem charWeight_mul (k : ℕ) (ε : (ZMod N)ˣ →* ℂˣ) (m n : ℕ) :
    charWeight N k ε (m * n) = charWeight N k ε m * charWeight N k ε n := by
  simp only [charWeight, Nat.cast_mul, map_mul, mul_pow]
  ring

/-- The prime recursion of the coefficients of a normalized eigenform. -/
theorem coeff_rec (k : ℕ) (hk : 1 ≤ k) {ε : (ZMod N)ˣ →* ℂˣ} (f : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k))
    (hf : f ∈ charSpaceN N k ε)
    (ha1 : (qExpansion N f).coeff 1 = 1) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (hc0 : ∃ c : ℂ, heckeActN N k (heckeTN N p) f = c • f) (n : ℕ) :
    (qExpansion N f).coeff (p * n) = (qExpansion N f).coeff p * (qExpansion N f).coeff n -
      if p ∣ n then (p : ℂ) * charWeight N k ε p * (qExpansion N f).coeff (n / p) else 0 := by
  obtain ⟨c, hc⟩ := hc0
  have key : ∀ m, c * (qExpansion N f).coeff m = (qExpansion N f).coeff (p * m) +
      if p ∣ m then (p : ℂ) * charWeight N k ε p * (qExpansion N f).coeff (m / p) else 0 := by
    intro m
    have h := coeff_heckeTNp hp hpN k f hf m
    rw [charWeight_prime k hk ε (coprime_of hp hpN), ← h, hc, FunLike.coe_smul,
      ModularForm.qExpansion_smul (by exact_mod_cast (NeZero.pos N)) (N_mem_strictPeriods N),
      PowerSeries.coeff_smul, smul_eq_mul]
  have hc1 : c = (qExpansion N f).coeff p := by
    have := key 1
    rw [ha1, mul_one, mul_one, if_neg (fun h ↦ hp.one_lt.ne' (Nat.eq_one_of_dvd_one h)), add_zero] at this
    exact this
  rw [← hc1, key n]
  ring

/-- **Milne, Proposition 5.35**, unconditionally: if $f \in M_{2k}(\Gamma(N), \varepsilon)$ is an eigenform of every
$T^N(n)$, $(n, N) = 1$, with $a_1 = 1$, then the coefficients prime to $N$ have the Euler product
$\prod_{p\nmid N}(1 - a_pp^{-s} + \varepsilon(p)p^{2k-1-2s})^{-1}$. -/
@[kb "milne2017mf" "Section 5, Proposition 5.35 (pdf p. 84)"]
theorem eulerProductLevelN (N : ℕ) [NeZero N] (k : ℕ) : EulerProductLevelN N k := by
  refine ⟨fun ε f hf heig ha1 ↦ ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exfalso
    obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero (show ModularForm ((Gamma N).map (mapGL ℝ)) 0 from f)
    have h0 := ModularFormClass.qExpansion_coeff_unique (by exact_mod_cast (NeZero.pos N))
      (N_mem_strictPeriods N) (f := f) (c := fun m ↦ if m = 0 then c else 0) (fun τ ↦ by
        have : (f : ℍ → ℂ) τ = c := by rw [show (f : ℍ → ℂ) = Function.const ℍ c from hc]; rfl
        rw [this]
        convert hasSum_ite_eq 0 c using 2 with m
        split_ifs with hm <;> simp [hm]) 1
    rw [← h0] at ha1
    simp at ha1
  set a : ℕ → ℂ := fun n ↦ (qExpansion N f).coeff n with ha
  have hrec : ∀ q : ℕ, q.Prime → ¬ q ∣ N → ∀ n : ℕ,
      a (q * n) = a q * a n - if q ∣ n then (q : ℂ) * charWeight N k ε q * a (n / q) else 0 :=
    fun q hq hqN n ↦ coeff_rec k hk f hf ha1 hq hqN (heig q hq.pos (coprime_of hq hqN)) n
  have hmult := mult_of_rec N a (fun q ↦ (q : ℂ) * charWeight N k ε q) ha1 hrec
  have htfae := Miyake.heckeRecursion_tfae (fun n ↦ if n.Coprime N then a n else 0) (charWeight N k ε)
    (by simp [ha, ha1]) (charWeight_one (N := N) k ε) (fun m n _ _ ↦ charWeight_mul (N := N) k ε m n)
  refine (htfae.out 1 2).mp ?_
  refine ⟨fun m n hm hn hmn ↦ ?_, fun q e hq he ↦ ?_⟩
  · by_cases hmN : m.Coprime N
    · by_cases hnN : n.Coprime N
      · simp only [if_pos (Nat.coprime_mul_iff_left.mpr ⟨hmN, hnN⟩), if_pos hmN, if_pos hnN]
        exact hmult m n hm hn hmN hmn
      · simp [hnN, Nat.coprime_mul_iff_left]
    · simp [hmN, Nat.coprime_mul_iff_left]
  · by_cases hqN : q ∣ N
    · have hnc : ∀ j, 0 < j → ¬ (q ^ j).Coprime N := fun j hj h ↦
        (Nat.Prime.coprime_iff_not_dvd hq).mp ((Nat.coprime_pow_left_iff hj _ _).mp h) hqN
      have hq' : ¬ q.Coprime N := fun h ↦ (Nat.Prime.coprime_iff_not_dvd hq).mp h hqN
      rw [charWeight_of_not_coprime (N := N) k ε hq']
      simp [hq', hnc (e + 1) (by omega)]
    · have hc : ∀ j, (q ^ j).Coprime N := fun j ↦ ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN).pow_left j
      have hq' : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqN
      simp only [if_pos (hc _), if_pos hq']
      have h := hrec q hq hqN (q ^ e)
      have hd : q ∣ q ^ e := dvd_pow_self q (by omega)
      have hdiv : q ^ e / q = q ^ (e - 1) := by
        have := Nat.pow_div he hq.pos
        rwa [pow_one] at this
      rw [if_pos hd, ← pow_succ', hdiv] at h
      rw [h]
      ring

end euler

end ModularFormsKB.Milne.UncondLevelN
