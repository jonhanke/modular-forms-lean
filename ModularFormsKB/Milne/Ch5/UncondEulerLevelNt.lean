import ModularFormsKB.Milne.Ch5.UncondEulerLevelN

/-!
# Milne, Theorem 5.36 unconditionally: the full Euler product at level $\Gamma(N)$

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf p. 85.

Let $f \in V(t, \varepsilon)$ with $a_1 = 1$ be an eigenform of every $T^t(n)$.

* **Only $t = 1$ occurs.** On $V(\zeta)$ the operator $U\colon f(z) \mapsto f(z + 1)$ multiplies $a_n$ by
  $e^{2\pi in/N}$ (`coeff_translateOne`), so a form in $V(\zeta)$ with $a_1 \ne 0$ has $\zeta = e^{2\pi i/N}$, a
  primitive $N$-th root of unity; in $V(t)$, a sum of the $V(\zeta)$ with $\zeta$ primitive of order $N/t$, this
  forces $t = 1$ (`coeff_one_eq_zero_of_mem_tSpaceN`).
* **Bad primes.** For $t = 1$ and $p \mid N$, $T^1(p) = U_p\colon f \mapsto \sum_{b<p}f|_k\begin{pmatrix}1 & bN\\
  0 & p\end{pmatrix}$ acts on $q_N$-expansions by $a_n \mapsto a_{pn}$, so $a_{pn} = a_pa_n$.
* **Good primes** are Proposition 5.35's computation (`coeff_heckeTNp`).

The recursion then holds at every prime with the Euler factor $1 - a_pX + \varepsilon(p)p^{2k-1}X^2$ ($\varepsilon(p) = 0$
for $p \mid N$), and Miyake's Lemma 4.5.12 gives the Euler product.
-/

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing HeckeRing.GLn HeckeRing.GL2
  DoubleCoset

open scoped MatrixGroups ModularForm Pointwise HeckeCosetModule

namespace ModularFormsKB.Milne.UncondLevelN

variable {N : ℕ} [NeZero N]

/-! ### The operator `U` on `q_N`-expansions -/

theorem translateOne_apply (k : ℕ) (g : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)) (z : ℍ) :
    (translateOne N k g) z = g (ModularGroup.T • z) := by
  rw [show (translateOne N k g) z = (⇑g ∣[(2 * k : ℤ)] mapGL ℝ ModularGroup.T) z from
    mcast_translate_apply_N N k _ g z, show mapGL ℝ ModularGroup.T = Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.T) from rfl,
    ← ModularForm.SL_slash, ModularForm.SL_slash_apply]
  simp [denom, ModularGroup.coe_T]

theorem coeff_translateOne (k : ℕ) (g : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)) (n : ℕ) :
    (qExpansion N (translateOne N k g)).coeff n =
      Complex.exp (2 * Real.pi * Complex.I / N) ^ n * (qExpansion N g).coeff n := by
  refine (ModularFormClass.qExpansion_coeff_unique (by exact_mod_cast (NeZero.pos N)) (N_mem_strictPeriods N)
    (f := translateOne N k g) (c := fun n ↦ Complex.exp (2 * Real.pi * Complex.I / N) ^ n * (qExpansion N g).coeff n)
    (fun τ ↦ ?_) n).symm
  rw [translateOne_apply]
  have h := hasSum_qN g (ModularGroup.T • τ)
  have hq : Function.Periodic.qParam N ((ModularGroup.T • τ : ℍ) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I / N) * Function.Periodic.qParam N (τ : ℂ) := by
    rw [modular_T_smul, UpperHalfPlane.coe_vadd, Function.Periodic.qParam, Function.Periodic.qParam,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hq] at h
  refine h.congr_fun fun m ↦ ?_
  simp only [smul_eq_mul, mul_pow]
  ring

theorem coeff_one_eq_zero_of_mem_rootSpaceN (k : ℕ) {t : ℕ} (ht1 : t ≠ 1) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (N / t)) {g : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)}
    (hg : g ∈ rootSpaceN N k ζ) : (qExpansion N g).coeff 1 = 0 := by
  by_contra h0
  have hU := Module.End.mem_eigenspace_iff.mp hg
  have h1 := coeff_translateOne k g 1
  rw [hU, FunLike.coe_smul, ModularForm.qExpansion_smul (by exact_mod_cast (NeZero.pos N)) (N_mem_strictPeriods N),
    PowerSeries.coeff_smul, smul_eq_mul, pow_one] at h1
  have hz : ζ = Complex.exp (2 * Real.pi * Complex.I / N) := mul_right_cancel₀ h0 h1
  have hprim := Complex.isPrimitiveRoot_exp N (NeZero.ne N)
  rw [← hz] at hprim
  have hNt : N / t = N := hζ.unique hprim
  rcases (Nat.div_eq_self.mp hNt) with h | h
  · exact NeZero.ne N h
  · exact ht1 h

/-- The coefficient `a_1`, as a linear functional. -/
noncomputable def coeffOne (k : ℕ) : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k) →ₗ[ℂ] ℂ where
  toFun f := (qExpansion N f).coeff 1
  map_add' f g := by
    rw [FunLike.coe_add, ModularForm.qExpansion_add (by exact_mod_cast (NeZero.pos N)) (N_mem_strictPeriods N) f g,
      map_add]
  map_smul' c f := by
    rw [FunLike.coe_smul, ModularForm.qExpansion_smul (by exact_mod_cast (NeZero.pos N)) (N_mem_strictPeriods N),
      PowerSeries.coeff_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul]

/-- **Only `t = 1` occurs**: on `V(t)`, `t ≠ 1`, the coefficient `a_1` vanishes. -/
theorem coeff_one_eq_zero_of_mem_tSpaceN (k : ℕ) {t : ℕ} (ht : t ∣ N) (ht1 : t ≠ 1)
    {f : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)} (hf : f ∈ tSpaceN N k t) : (qExpansion N f).coeff 1 = 0 := by
  have hle : tSpaceN N k t ≤ LinearMap.ker (coeffOne (N := N) k) :=
    iSup₂_le fun ζ hζ g hg ↦ coeff_one_eq_zero_of_mem_rootSpaceN k ht1 hζ hg
  exact hle hf


/-! ### `U_p` for `p ∣ N` preserves level `Γ(N)` -/

/-- The translate `b ↦ (b + y) mod p` of the top representatives under `γ ∈ Γ(N)`, `y = γ₀₁ / N`. -/
noncomputable def shiftB (N p : ℕ) (γ : SL(2, ℤ)) (b : ℕ) : ℕ :=
  (((b : ℤ) + (γ 0 1) / N) % p).toNat

theorem shiftB_spec {p : ℕ} (hp : 0 < p) (γ : SL(2, ℤ)) (b : ℕ) :
    shiftB N p γ b < p ∧ ((shiftB N p γ b : ℕ) : ℤ) = b + γ 0 1 / N - p * ((b + γ 0 1 / N) / p) := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have h1 := Int.emod_nonneg ((b : ℤ) + γ 0 1 / N) hp'.ne'
  have h2 := Int.emod_lt_of_pos ((b : ℤ) + γ 0 1 / N) hp'
  have h3 := Int.emod_def ((b : ℤ) + γ 0 1 / N) p
  simp only [shiftB]
  refine ⟨by omega, ?_⟩
  rw [Int.toNat_of_nonneg h1]
  linarith

theorem exists_gamma_shift {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma N) (b : ℕ) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma N ∧
      topRep N p b * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * topRep N p (shiftB N p γ b) := by
  obtain ⟨N1, hN1⟩ := hpN
  have hNz : (N : ℤ) = p * N1 := by exact_mod_cast hN1
  rw [Gamma_mem] at hγ
  obtain ⟨h00, h01, h10, h11⟩ := hγ
  have d01 : (N : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp h01
  have d10 : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp h10
  have d00 : (N : ℤ) ∣ γ 0 0 - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (by push_cast; rw [h00, sub_self])
  have d11 : (N : ℤ) ∣ γ 1 1 - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (by push_cast; rw [h11, sub_self])
  obtain ⟨u, hu⟩ := d00
  obtain ⟨v, hv⟩ := d11
  obtain ⟨w, hw⟩ := d10
  have hy' : γ 0 1 = N * (γ 0 1 / N) := (Int.mul_ediv_cancel' d01).symm
  obtain ⟨hlt, hb'⟩ := shiftB_spec (N := N) hp.pos γ b
  generalize γ 0 1 / N = y at hy' hb'
  generalize ((b : ℤ) + y) / p = t at hb'
  set b' := shiftB N p γ b
  have e00 : γ 0 0 = 1 + N * u := by linarith
  have e11 : γ 1 1 = 1 + N * v := by linarith
  set M : Matrix (Fin 2) (Fin 2) ℤ := !![γ 0 0 + b * N * γ 1 0, N * (t + N1 * (b * v - b' * u - b * b' * N * w));
    p * γ 1 0, γ 1 1 - γ 1 0 * b' * N] with hM
  have hid : topRep N p b * (γ : Matrix (Fin 2) (Fin 2) ℤ) = M * topRep N p b' := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [topRep, hM, Matrix.mul_apply, Fin.sum_univ_two]
    · rw [hy', e11, e00, hw, hb', hNz]; ring
    · ring
  have hdet : M.det = 1 := by
    have := congrArg Matrix.det hid
    rw [Matrix.det_mul, Matrix.det_mul, det_topRep, det_topRep, Matrix.SpecialLinearGroup.det_coe, mul_one] at this
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    exact (mul_right_cancel₀ hp0 (by rw [one_mul]; exact this.symm))
  let γ' : SL(2, ℤ) := ⟨M, hdet⟩
  refine ⟨γ', ?_, hid⟩
  show γ' ∈ Gamma N
  rw [Gamma_mem]
  simp only [γ', hM, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  push_cast
  simp [h00, h10, h11]


local notation "φ" => Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℚ ℝ)

theorem slash_topGL_Gamma {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) {w : ℤ} (f : ℍ → ℂ)
    (hf : ∀ γ ∈ Gamma N, f ∣[w] mapGL ℝ γ = f) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma N) (b : ℕ) :
    (f ∣[w] topGL N p hp b) ∣[w] mapGL ℝ γ = f ∣[w] topGL N p hp (shiftB N p γ b) := by
  obtain ⟨γ', hγ', hid⟩ := exists_gamma_shift hp hpN γ hγ b
  have hGL : topGL N p hp b * mapGL ℚ γ = mapGL ℚ γ' * topGL N p hp (shiftB N p γ b) := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, intGL_coe, intGL_coe, coe_mapGL_int, coe_mapGL_int,
      ← Matrix.map_mul_intCast, ← Matrix.map_mul_intCast, hid]
  calc (f ∣[w] topGL N p hp b) ∣[w] mapGL ℝ γ = f ∣[w] (φ (topGL N p hp b) * mapGL ℝ γ) := by
        rw [ModularForm.rat_slash, ← SlashAction.slash_mul]
    _ = f ∣[w] φ (topGL N p hp b * mapGL ℚ γ) := by rw [map_mul, map_mapGL_rat_real]
    _ = f ∣[w] φ (mapGL ℚ γ' * topGL N p hp (shiftB N p γ b)) := by rw [hGL]
    _ = (f ∣[w] mapGL ℝ γ') ∣[w] φ (topGL N p hp (shiftB N p γ b)) := by
        rw [map_mul, map_mapGL_rat_real, SlashAction.slash_mul]
    _ = f ∣[w] topGL N p hp (shiftB N p γ b) := by rw [hf γ' hγ', ModularForm.rat_slash]

theorem shiftB_injective {p : ℕ} (hp : 0 < p) (γ : SL(2, ℤ)) {b₁ b₂ : ℕ} (h₁ : b₁ < p) (h₂ : b₂ < p)
    (h : shiftB N p γ b₁ = shiftB N p γ b₂) : b₁ = b₂ := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have e : ((b₁ : ℤ) + γ 0 1 / N) % p = ((b₂ : ℤ) + γ 0 1 / N) % p := by
    have := congrArg (fun n : ℕ ↦ (n : ℤ)) h
    simp only [shiftB] at this
    rwa [Int.toNat_of_nonneg (Int.emod_nonneg _ hp'.ne'), Int.toNat_of_nonneg (Int.emod_nonneg _ hp'.ne')] at this
  have hm : (b₁ : ℤ) ≡ b₂ [ZMOD p] := Int.ModEq.add_right_cancel' _ e
  unfold Int.ModEq at hm
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast h₁),
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast h₂)] at hm
  exact_mod_cast hm

/-- `U_p` (`p ∣ N`) preserves `Γ(N)`-invariance. -/
theorem sum_topGL_slash_Gamma {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) {w : ℤ} (f : ℍ → ℂ)
    (hf : ∀ γ ∈ Gamma N, f ∣[w] mapGL ℝ γ = f) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma N) :
    (∑ b : Fin p, f ∣[w] topGL N p hp b) ∣[w] mapGL ℝ γ = ∑ b : Fin p, f ∣[w] topGL N p hp b := by
  rw [SlashAction.sum_slash]
  simp_rw [slash_topGL_Gamma hp hpN f hf γ hγ]
  let σ : Fin p → Fin p := fun b ↦ ⟨shiftB N p γ b, (shiftB_spec hp.pos γ b).1⟩
  have hσ : Function.Injective σ := fun b₁ b₂ h ↦
    Fin.ext (shiftB_injective hp.pos γ b₁.2 b₂.2 (congrArg Fin.val h))
  exact Fintype.sum_bijective σ (Finite.injective_iff_bijective.mp hσ) _ _ fun b ↦ rfl


/-! ### `T^t(n)` at primes, for `t = 1` -/

theorem coe_sum_mf' {𝒢 : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {ι : Type*} (s : Finset ι)
    (F : ι → ModularForm 𝒢 k) : ⇑(∑ i ∈ s, F i) = ∑ i ∈ s, ⇑(F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, FunLike.coe_add, ih]

theorem heckeActNFun_eq (k : ℕ) (x : 𝕋 (DeltaN N) ((Gamma N).map (mapGL ℚ)) ℤ)
    (f : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)) :
    heckeActNFun N k x ⇑f = ⇑(heckeActN N k x f) := by
  rw [heckeActNFun, heckeActN]
  erw [Finsupp.linearCombination_apply]
  simp only [Finsupp.sum]
  rw [LinearMap.sum_apply, coe_sum_mf']
  refine Finset.sum_congr rfl fun D _ ↦ ?_
  rw [LinearMap.smul_apply, FunLike.coe_smul, coe_heckeSlashModularFormEnd, ← Int.cast_smul_eq_zsmul ℂ]

theorem heckeTtBad_one (k t : ℕ) (f : ℍ → ℂ) : heckeTtBad N k t 1 f = f := by
  rw [heckeTtBad, dite_eq_right one_ne_zero, Finset.sum_range_one]
  convert SlashAction.slash_one (2 * k : ℤ) f
  refine Units.ext ?_
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- At a prime `p ∤ N`, `T^t(p) = T^N(p)`. -/
theorem heckeTt_prime_good (k t : ℕ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)) :
    heckeTt N k t p f = ⇑(heckeActN N k (heckeTN N p) f) := by
  have hg : Nat.gcd p (N ^ p) = 1 := Nat.Coprime.pow_right p ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN)
  rw [heckeTt, hg, Nat.div_one, heckeTtBad_one, heckeActNFun_eq]


theorem heckeTN_one : heckeTN N 1 = heckeTNDiag N 1 1 := by
  rw [heckeTN, Nat.divisorsAntidiagonal_one, Finset.filter_singleton, if_pos (dvd_refl 1), Finset.sum_singleton]

theorem mf_slash_Gamma {w : ℤ} (f : ModularForm ((Gamma N).map (mapGL ℝ)) w) :
    ∀ γ ∈ Gamma N, ⇑f ∣[w] mapGL ℝ γ = ⇑f := fun γ hγ ↦
  SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)

/-- `T^N(1)` acts as the identity on `Γ(N)`-invariant functions. -/
theorem heckeActNFun_one (k : ℕ) (F : ℍ → ℂ) (hF : ∀ γ ∈ Gamma N, F ∣[(2 * k : ℤ)] mapGL ℝ γ = F) :
    heckeActNFun N k (heckeTN N 1) F = F := by
  have hex := exists_DeltaN_mem_diag N one_pos one_pos (by simp)
  rw [heckeTN_one, heckeTNDiag, dite_eq_left hex, heckeActNFun, HeckeCosetModule.single]
  erw [Finsupp.sum_single_index (by simp)]
  rw [Int.cast_one, one_smul]
  obtain ⟨g0, hg0eq⟩ : ∃ g : DeltaN N, g = hex.choose := ⟨_, rfl⟩
  rw [← hg0eq]
  have hg0SL : (g0 : GL (Fin 2) ℚ) ∈ SLnZ 2 := by
    have h : (g0 : GL (Fin 2) ℚ) ∈ doubleCoset (natDiagGL 2 ![1, 1]) (SLnZ 2 : Set (GL (Fin 2) ℚ)) (SLnZ 2) :=
      hg0eq ▸ hex.choose_spec
    rw [natDiagGL_eq_intGL 1 1 one_pos one_pos, show intGL !![((1 : ℕ) : ℤ), 0; 0, ((1 : ℕ) : ℤ)] _ = 1 from
      Units.ext (by rw [intGL_coe]; ext i j; fin_cases i <;> fin_cases j <;> simp)] at h
    obtain ⟨u, hu, v, hv, huv⟩ := mem_doubleCoset.mp h
    rw [huv, mul_one]; exact mul_mem hu hv
  obtain ⟨s, hs⟩ := (mem_SLnZ_iff 2).mp hg0SL
  have hsN : s ∈ Gamma N := mem_Gamma_of_mul_mem (one_mem (DeltaN N)) s (by rw [one_mul, hs]; exact g0.2)
  have hg0Γ : (g0 : GL (Fin 2) ℚ) ∈ GammaGL N := by rw [← hs]; exact Subgroup.mem_map_of_mem _ hsN
  have hcover : doubleCoset ((Quotient.out (HeckeCoset.mk (GammaGL N) (GammaGL N) g0) : DeltaN N) : GL (Fin 2) ℚ)
      (GammaGL N : Set (GL (Fin 2) ℚ)) (GammaGL N) =
      ⋃ _ : Unit, MulOpposite.op (1 : GL (Fin 2) ℚ) • (GammaGL N : Set (GL (Fin 2) ℚ)) := by
    rw [doubleCoset_out_mk, Set.iUnion_const, MulOpposite.op_one, one_smul]
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hx
      exact mul_mem (mul_mem ha hg0Γ) hb
    · intro hx
      exact mem_doubleCoset.mpr ⟨x * (g0 : GL (Fin 2) ℚ)⁻¹, mul_mem hx (inv_mem hg0Γ), 1, one_mem _, by group⟩
  rw [heckeSlashSum_eq_sum_of_rightCosets (2 * k) _ (fun _ : Unit ↦ 1) hcover
    (Function.injective_of_subsingleton _) F (fun γ hγ ↦ ?_)]
  · simp
  · obtain ⟨s, hs', rfl⟩ := Subgroup.mem_map.mp hγ
    rw [ModularForm.rat_slash, map_mapGL_rat_real]; exact hF s hs'

theorem heckeTtBad_eq (k : ℕ) {p : ℕ} (hp : p.Prime) (f : ℍ → ℂ) :
    heckeTtBad N k 1 p f = ∑ b : Fin p, f ∣[(2 * k : ℤ)] topGL N p hp b := by
  rw [heckeTtBad, dite_eq_right hp.ne_zero, Finset.sum_range]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [ModularForm.rat_slash]
  congr 1
  refine Units.ext ?_
  ext i j; fin_cases i <;> fin_cases j <;> simp [phi_intGL_apply, topRep]

/-- At a prime `p ∣ N`, `T^1(p) = U_p`. -/
theorem heckeTt_prime_bad (k : ℕ) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (f : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k)) :
    heckeTt N k 1 p f = ∑ b : Fin p, ⇑f ∣[(2 * k : ℤ)] topGL N p hp b := by
  have hg : Nat.gcd p (N ^ p) = p := Nat.gcd_eq_left (dvd_pow hpN hp.ne_zero)
  rw [heckeTt, hg, Nat.div_self hp.pos, heckeTtBad_eq k hp]
  exact heckeActNFun_one k _ (sum_topGL_slash_Gamma hp hpN _ (mf_slash_Gamma f))


/-- At `p ∣ N`, an eigenform of `U_p` with eigenvalue `c` has `a_{pn} = c a_n`. -/
theorem coeff_Up (k : ℕ) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (f : ModularForm ((Gamma N).map (mapGL ℝ)) (2 * k))
    {c : ℂ} (hc : heckeTt N k 1 p f = c • ⇑f) (n : ℕ) :
    (qExpansion N f).coeff (p * n) = c * (qExpansion N f).coeff n := by
  have h := ModularFormClass.qExpansion_coeff_unique (by exact_mod_cast (NeZero.pos N)) (N_mem_strictPeriods N)
    (f := c • f) (c := fun j ↦ (qExpansion N f).coeff (p * j)) (fun τ ↦ by
      have h1 := hasSum_top hp k f τ
      rw [← Finset.sum_apply, ← heckeTt_prime_bad k hp hpN f, hc] at h1
      simpa [smul_eq_mul] using h1) n
  rw [h, FunLike.coe_smul, ModularForm.qExpansion_smul (by exact_mod_cast (NeZero.pos N)) (N_mem_strictPeriods N),
    PowerSeries.coeff_smul, smul_eq_mul]

/-- **Milne, Theorem 5.36**, unconditionally. Let `f ∈ V(t, ε)` have `a_1 = 1` and be an eigenform of every
`T^t(n)`. Then `∑ aₙ n^{-s} = ∏_p (1 - a_p p^{-s} + ε(p) p^{2k-1-2s})^{-1}` formally, with `ε(p) = 0` for `p ∣ N`.
(The hypotheses force `t = 1`, `coeff_one_eq_zero_of_mem_tSpaceN`.) -/
@[kb "milne2017mf" "Section 5, Theorem 5.36 (pdf p. 85)"]
theorem eulerProductLevelNt (N : ℕ) [NeZero N] (k : ℕ) : EulerProductLevelNt N k := by
  refine ⟨fun t ht ε f hft hf heig ha1 ↦ ?_⟩
  by_cases ht1 : t = 1
  swap
  · exact absurd (coeff_one_eq_zero_of_mem_tSpaceN k ht ht1 hft) (by rw [ha1]; exact one_ne_zero)
  subst ht1
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
  have hrec : ∀ q : ℕ, q.Prime → ¬ q ∣ 1 → ∀ n : ℕ,
      a (q * n) = a q * a n - if q ∣ n then (q : ℂ) * charWeight N k ε q * a (n / q) else 0 := by
    intro q hq _ n
    by_cases hqN : q ∣ N
    · obtain ⟨c, hc⟩ := heig q hq.pos
      have hU := coeff_Up k hq hqN f hc
      have hc1 : c = a q := by have := hU 1; rw [mul_one, ha1, mul_one] at this; exact this.symm
      have hw : charWeight N k ε q = 0 :=
        charWeight_of_not_coprime (N := N) k ε (fun h ↦ (Nat.Prime.coprime_iff_not_dvd hq).mp h hqN)
      simp only [ha, hU n, hc1, hw, mul_zero, zero_mul, ite_self, sub_zero]
    · obtain ⟨c, hc⟩ := heig q hq.pos
      exact coeff_rec k hk f hf ha1 hq hqN ⟨c, DFunLike.coe_injective
        ((heckeTt_prime_good k 1 hq hqN f).symm.trans (hc.trans (FunLike.coe_smul c f).symm))⟩ n
  have hmult := mult_of_rec 1 a (fun q ↦ (q : ℂ) * charWeight N k ε q) ha1 hrec
  have htfae := Miyake.heckeRecursion_tfae a (charWeight N k ε) ha1 (charWeight_one (N := N) k ε)
    (fun m n _ _ ↦ charWeight_mul (N := N) k ε m n)
  refine (htfae.out 1 2).mp ?_
  refine ⟨fun m n hm hn hmn ↦ hmult m n hm hn (Nat.coprime_one_right m) hmn, fun q e hq he ↦ ?_⟩
  have h := hrec q hq (Nat.Prime.not_dvd_one hq) (q ^ e)
  have hd : q ∣ q ^ e := dvd_pow_self q (by omega)
  have hdiv : q ^ e / q = q ^ (e - 1) := by
    have := Nat.pow_div he hq.pos
    rwa [pow_one] at this
  rw [if_pos hd, ← pow_succ', hdiv] at h
  rw [h]
  ring

end ModularFormsKB.Milne.UncondLevelN
