/-
# The Petersson inner product on $S_{k+1/2}(4N, \chi)$ for every $N \ge 1$

Part of loose ends LE-MF-0174 and LE-MF-0168.

For $f, g : \mathbb H \to \mathbb C$ we set
$$\langle f, g\rangle_{4N} = \frac1{[\mathrm{SL}_2(\mathbb Z):\Gamma_0(4N)]}\int_{\Gamma_0(4N)\backslash\mathbb H}
  \overline{f(\tau)}\,g(\tau)\,v^{k+1/2}\,\frac{du\,dv}{v^2}\qquad(\tau = u + iv),$$
computed through a fixed list `gamma0Reps (4 * N)` of right coset representatives (`peterssonLevel`). This is the
normalization of Kohnen–Zagier at level 4 (`peterssonFour`, factor $\tfrac16$) and of Kohnen 1985 at level $4N$
[unverified]. Conjugate-linear in the first argument, as `peterssonFour`.

Proved here, for any multiplier system $M$ (`MultiplierSystem`), $N \ge 1$ and $\chi$ modulo $4N$:
- `MultiplierSystem.peterssonIntegrand_smul`: for $f, g$ with the transformation law of weight $k + \tfrac12$, the
  integrand $\overline f\,g\,v^{k+1/2}$ is $\Gamma_0(4N)$-invariant ($|\chi(d)| = 1$, $|j(\gamma,\tau)|^2 = |c\tau+d|$,
  $\operatorname{Im}\gamma\tau = \operatorname{Im}\tau/|c\tau+d|^2$);
- `MultiplierSystem.peterssonLevel_eq_reps`: the product does not depend on the list of representatives
  (`RankinUnfold.repsIntegral_eq_sum_quotient`), and a list of representatives has length the index
  (`IsGamma0Reps.length_eq`);
- `MultiplierSystem.peterssonLevel_one`: at $N = 1$ it is `peterssonFour` (`isGamma0Reps_gamma0FourReps`);
- hermitian symmetry, sesquilinearity on $S_{k+1/2}(4N,\chi)$, and **definiteness**
  (`MultiplierSystem.peterssonLevel_self_re_pos`), from the convergence of 0.4.0
  (`MultiplierSystem.integrableOn_peterssonIntegrand`) and `eq_zero_of_setIntegral_fd_eq_zero`;
- `MultiplierSystem.posDefHermitian_peterssonLevel`, `MultiplierSystem.exists_orthogonal_decomposition_peterssonLevel`:
  the parameter `P` of `TernaryDecomposition.lean` instantiated with this product, so
  $S_{k+1/2}(4N,\chi) = U \oplus U^\perp$ for every finite-dimensional subspace $U$ (for example the unary theta space).
-/
import ModularFormsKB.HalfIntegral.Abstract.PeterssonDefinite
import ModularFormsKB.HalfIntegral.Rankin.Unfolding
import ModularFormsKB.HalfIntegral.Rankin.Factors
import ModularFormsKB.HalfIntegral.TernaryDecomposition

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup MeasureTheory
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- **A fixed list of right coset representatives** of $\Gamma_0(L)$ in $\mathrm{SL}_2(\mathbb Z)$ (`exists_isGamma0Reps`;
the empty list for $L = 0$, where none is used). -/
noncomputable def gamma0Reps (L : ℕ) : List SL(2, ℤ) :=
  if h : 1 ≤ L then (exists_isGamma0Reps L h).choose else []

theorem isGamma0Reps_gamma0Reps {L : ℕ} (hL : 1 ≤ L) : IsGamma0Reps L (gamma0Reps L) := by
  unfold gamma0Reps
  rw [dif_pos hL]
  exact (exists_isGamma0Reps L hL).choose_spec

/-- **A list of right coset representatives has the index as its length.** -/
theorem IsGamma0Reps.length_eq {L : ℕ} [NeZero L] {R : List SL(2, ℤ)} (hR : IsGamma0Reps L R) :
    R.length = (Gamma0 L).index := by
  classical
  have hmem : ∀ g : SL(2, ℤ), g ∈ (Gamma0 L).withCenter ↔ g ∈ Gamma0 L := by
    intro g; rw [RankinUnfold.withCenter_Gamma0]
  let e : Fin R.length → SL(2, ℤ) ⧸ (Gamma0 L).withCenter := fun i ↦ QuotientGroup.mk (R[i.1])⁻¹
  have he : Function.Bijective e := by
    constructor
    · intro i j hij
      have := QuotientGroup.eq.mp hij
      rw [inv_inv, hmem] at this
      obtain ⟨k, -, hk⟩ := hR R[i.1]
      have hi : R[i.1] * (R.get i)⁻¹ ∈ Gamma0 L := by simp
      have hj : R[i.1] * (R.get j)⁻¹ ∈ Gamma0 L := by simpa using this
      exact (hk i hi).trans (hk j hj).symm
    · intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        obtain ⟨i, hi, -⟩ := hR g⁻¹
        refine ⟨i, ?_⟩
        show QuotientGroup.mk (R[i.1])⁻¹ = QuotientGroup.mk g
        rw [QuotientGroup.eq, inv_inv, hmem]
        have := Subgroup.inv_mem _ hi
        simpa [mul_inv_rev] using this
  have h1 : Nat.card (Fin R.length) = Nat.card (SL(2, ℤ) ⧸ (Gamma0 L).withCenter) :=
    Nat.card_congr (Equiv.ofBijective e he)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, ← Subgroup.index, RankinUnfold.withCenter_Gamma0] at h1
  exact h1

/-- **The six matrices `gamma0FourReps` are right coset representatives of $\Gamma_0(4)$.** -/
theorem isGamma0Reps_gamma0FourReps : IsGamma0Reps 4 gamma0FourReps := by
  intro g
  show ∃! i : Fin 6, g * (gamma0FourReps.get i)⁻¹ ∈ Gamma0 4
  have hcop := RankinUnfold.isCoprime_row g
  have hnot : ¬ (2 ∣ g 1 0 ∧ 2 ∣ g 1 1) := by
    rintro ⟨h1, h2⟩
    have := hcop.isUnit_of_dvd' h1 h2
    have h3 := Int.isUnit_iff.1 this
    omega
  have hmul : ∀ R : SL(2, ℤ), (g * R⁻¹ ∈ Gamma0 4) ↔ (4 : ℤ) ∣ g 1 0 * R 1 1 - g 1 1 * R 1 0 := by
    intro R
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have : (g * R⁻¹) 1 0 = g 1 0 * R 1 1 - g 1 1 * R 1 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rw [this]
    norm_num
  have hrow : ∀ i : Fin 6, (gamma0FourReps.get i) 1 0 = (![0, 1, 1, 1, 1, 2] : Fin 6 → ℤ) i ∧
      (gamma0FourReps.get i) 1 1 = (![1, 0, 1, 2, 3, -1] : Fin 6 → ℤ) i := by decide
  have hF : ∀ i : Fin 6, g 1 0 * (![1, 0, 1, 2, 3, -1] : Fin 6 → ℤ) i -
      g 1 1 * (![0, 1, 1, 1, 1, 2] : Fin 6 → ℤ) i =
      (![g 1 0, -g 1 1, g 1 0 - g 1 1, 2 * g 1 0 - g 1 1, 3 * g 1 0 - g 1 1,
        -g 1 0 - 2 * g 1 1] : Fin 6 → ℤ) i := by
    intro i; fin_cases i <;> simp <;> ring
  have hf : ∀ i : Fin 6, (g * (gamma0FourReps.get i)⁻¹ ∈ Gamma0 4) ↔
      (4 : ℤ) ∣ (![g 1 0, -g 1 1, g 1 0 - g 1 1, 2 * g 1 0 - g 1 1, 3 * g 1 0 - g 1 1,
        -g 1 0 - 2 * g 1 1] : Fin 6 → ℤ) i := by
    intro i
    rw [hmul, (hrow i).1, (hrow i).2, hF i]
  have huniq : ∀ i j : Fin 6, (4 : ℤ) ∣ (![g 1 0, -g 1 1, g 1 0 - g 1 1, 2 * g 1 0 - g 1 1,
      3 * g 1 0 - g 1 1, -g 1 0 - 2 * g 1 1] : Fin 6 → ℤ) i →
      (4 : ℤ) ∣ (![g 1 0, -g 1 1, g 1 0 - g 1 1, 2 * g 1 0 - g 1 1, 3 * g 1 0 - g 1 1,
        -g 1 0 - 2 * g 1 1] : Fin 6 → ℤ) j → i = j := by
    intro i j hi hj
    fin_cases i <;> fin_cases j <;> simp at hi hj ⊢ <;> omega
  have hex : ∃ i : Fin 6, (4 : ℤ) ∣ (![g 1 0, -g 1 1, g 1 0 - g 1 1, 2 * g 1 0 - g 1 1,
      3 * g 1 0 - g 1 1, -g 1 0 - 2 * g 1 1] : Fin 6 → ℤ) i := by
    have hodd : g 1 0 % 2 = 1 ∨ g 1 1 % 2 = 1 := by
      by_contra hc
      exact hnot ⟨by omega, by omega⟩
    have key : ∀ c d : ℤ, (c % 2 = 1 ∨ d % 2 = 1) → ((4 : ℤ) ∣ c ∨ (4 : ℤ) ∣ -d ∨ (4 : ℤ) ∣ c - d ∨
        (4 : ℤ) ∣ 2 * c - d ∨ (4 : ℤ) ∣ 3 * c - d ∨ (4 : ℤ) ∣ -c - 2 * d) := by
      intro c d h
      simp only [Int.dvd_iff_emod_eq_zero]
      rcases (by omega : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3) with hc | hc | hc | hc <;>
        rcases (by omega : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3) with hd | hd | hd | hd <;>
        omega
    have hdisj := key _ _ hodd
    rcases hdisj with h | h | h | h | h | h
    exacts [⟨0, by simpa using h⟩, ⟨1, by simpa using h⟩, ⟨2, by simpa using h⟩,
      ⟨3, by simpa using h⟩, ⟨4, by simpa using h⟩, ⟨5, by simpa using h⟩]
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, (hf i).2 hi, fun j hj ↦ huniq j i ((hf j).1 hj) hi⟩

section Helpers

open Filter ModularForm
open scoped Manifold Topology

/-- **Identity theorem on $\mathbb H$:** a holomorphic function vanishing on a nonempty open set is zero. -/
private theorem eq_zero_of_eqOn_open {h : ℍ → ℂ} (hh : MDiff h) {U : Set ℍ} (hU : IsOpen U)
    (hne : U.Nonempty) (h0 : ∀ τ ∈ U, h τ = 0) : h = 0 := by
  have han : AnalyticOnNhd ℂ (h ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.1 hh).analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  obtain ⟨τ₀, hτ₀⟩ := hne
  have hev : (h ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (τ₀ : ℂ)] 0 := by
    have hopen : IsOpen ((↑) '' U : Set ℂ) :=
      UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ hU
    filter_upwards [hopen.mem_nhds ⟨τ₀, hτ₀, rfl⟩] with z hz
    obtain ⟨τ, hτ, rfl⟩ := hz
    simp [UpperHalfPlane.ofComplex_apply, h0 τ hτ]
  have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected (show 0 < (τ₀ : ℂ).im from τ₀.im_pos) hev
  funext τ
  have := hzero (show 0 < (τ : ℂ).im from τ.im_pos)
  simpa [UpperHalfPlane.ofComplex_apply] using this

private theorem fdo_nonempty : (ModularGroup.fdo : Set ℍ).Nonempty := by
  refine ⟨⟨2 * Complex.I, by simp⟩, ?_, ?_⟩
  · show 1 < Complex.normSq (2 * Complex.I)
    simp [Complex.normSq_apply]
    norm_num
  · show |(2 * Complex.I).re| < 1 / 2
    simp

private theorem norm_chi_eq_one {N : ℕ} (χ : DirichletCharacter ℂ (4 * N)) {γ : SL(2, ℤ)}
    (h : γ ∈ Gamma0 (4 * N)) : ‖χ (γ 1 1 : ZMod (4 * N))‖ = 1 := by
  have hc : ((γ 1 0 : ℤ) : ZMod (4 * N)) = 0 := by rwa [Gamma0_mem] at h
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have h1 : ((γ 0 0 : ℤ) : ZMod (4 * N)) * (γ 1 1 : ℤ) = 1 := by
    have := congrArg (fun x : ℤ ↦ (x : ZMod (4 * N))) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at this
    rw [hc] at this
    simpa using this
  have hu : IsUnit ((γ 1 1 : ℤ) : ZMod (4 * N)) :=
    IsUnit.of_mul_eq_one ((γ 0 0 : ℤ) : ZMod (4 * N)) (by rw [← h1]; ring)
  obtain ⟨u, hu'⟩ := hu
  rw [← hu']
  exact DirichletCharacter.unit_norm_eq_one χ u

private theorem gamma0_four_of {N : ℕ} {γ : SL(2, ℤ)} (h : γ ∈ Gamma0 (4 * N)) : γ ∈ Gamma0 4 := by
  rw [Gamma0_mem] at *
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at *
  exact dvd_trans (by push_cast; exact dvd_mul_right (4 : ℤ) N) h

private theorem peterssonReps_eq_repsIntegral (R : List SL(2, ℤ)) (w : ℝ) (f g : ℍ → ℂ) :
    peterssonReps R w f g = repsIntegral R (peterssonIntegrand 1 w f g) := by
  unfold peterssonReps repsIntegral
  congr 1
  refine List.map_congr_left fun γ _ ↦ ?_
  congr 1
  funext τ
  simp [peterssonIntegrand]

private theorem peterssonReps_eq_of_reps {L : ℕ} [NeZero L] {R R' : List SL(2, ℤ)} (hR : IsGamma0Reps L R)
    (hR' : IsGamma0Reps L R') (w : ℝ) (f g : ℍ → ℂ)
    (hh : ∀ γ ∈ Gamma0 L, ∀ z : ℍ, peterssonIntegrand 1 w f g (γ • z) = peterssonIntegrand 1 w f g z) :
    peterssonReps R w f g = peterssonReps R' w f g := by
  rw [peterssonReps_eq_repsIntegral, peterssonReps_eq_repsIntegral,
    RankinUnfold.repsIntegral_eq_sum_quotient hR _ hh, RankinUnfold.repsIntegral_eq_sum_quotient hR' _ hh]

end Helpers

/-- **The Petersson product on $S_{k+1/2}(4N,\chi)$**, normalized by the index:
$\langle f, g\rangle_{4N} = [\mathrm{SL}_2(\mathbb Z):\Gamma_0(4N)]^{-1}\int_{\Gamma_0(4N)\backslash\mathbb H}
\overline f\,g\,v^{k+1/2}\,d\mu$. -/
noncomputable def peterssonLevel (k N : ℕ) (f g : ℍ → ℂ) : ℂ :=
  (((Gamma0 (4 * N)).index : ℂ))⁻¹ * peterssonReps (gamma0Reps (4 * N)) ((k : ℝ) + 1 / 2) f g

namespace MultiplierSystem

variable (M : MultiplierSystem) {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)}

/-- **The Petersson integrand is $\Gamma_0(4N)$-invariant** for $f, g$ with the transformation law of weight
$k + \tfrac12$ and character $\chi$. -/
theorem peterssonIntegrand_smul {f g : ℍ → ℂ} (hf : M.Transforms k N χ f) (hg : M.Transforms k N χ g)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (4 * N)) (τ : ℍ) :
    peterssonIntegrand 1 ((k : ℝ) + 1 / 2) f g (γ • τ) = peterssonIntegrand 1 ((k : ℝ) + 1 / 2) f g τ := by
  set w : ℝ := (k : ℝ) + 1 / 2 with hw
  have hx : 0 < ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ := by
    rw [← ModularGroup.denom_apply]; exact norm_pos_iff.2 (UpperHalfPlane.denom_ne_zero _ τ)
  set x : ℝ := ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ with hxdef
  have hj : ‖M.j γ τ‖ ^ 2 = x := M.norm_sq γ (gamma0_four_of hγ) τ
  have hχ := norm_chi_eq_one χ hγ
  have him : (γ • τ).im ^ w = x ^ (-w) * x ^ (-w) * τ.im ^ w := im_smul_rpow γ w τ
  have hreal : x ^ (2 * k + 1) * (x ^ (-w) * x ^ (-w)) = 1 := by
    rw [← Real.rpow_add hx, ← Real.rpow_natCast, ← Real.rpow_add hx]
    have : ((2 * k + 1 : ℕ) : ℝ) + (-w + -w) = 0 := by rw [hw]; push_cast; ring
    rw [this, Real.rpow_zero]
  have hb : ‖M.j γ τ ^ (2 * k + 1)‖ ^ 2 = x ^ (2 * k + 1) := by
    rw [norm_pow, ← pow_mul, mul_comm, pow_mul, hj]
  set a : ℂ := χ (γ 1 1 : ZMod (4 * N))
  set b : ℂ := M.j γ τ ^ (2 * k + 1)
  have hfg : (starRingEnd ℂ) (f (γ • τ)) * g (γ • τ) =
      (((‖a‖ ^ 2 * ‖b‖ ^ 2 : ℝ)) : ℂ) * ((starRingEnd ℂ) (f τ) * g τ) := by
    rw [hf γ hγ τ, hg γ hγ τ]
    have h1 : (starRingEnd ℂ) a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']; push_cast; ring
    have h2 : (starRingEnd ℂ) b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']; push_cast; ring
    simp only [map_mul]
    rw [Complex.ofReal_mul, ← h1, ← h2]
    ring
  unfold peterssonIntegrand
  simp only [one_smul]
  rw [hfg, hχ, hb, him]
  have : (((1 : ℝ) ^ 2 * x ^ (2 * k + 1) : ℝ) : ℂ) *
      (((x ^ (-w) * x ^ (-w) * τ.im ^ w : ℝ)) : ℂ) = ((τ.im ^ w : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [one_pow, one_mul]
    calc x ^ (2 * k + 1) * (x ^ (-w) * x ^ (-w) * τ.im ^ w)
        = (x ^ (2 * k + 1) * (x ^ (-w) * x ^ (-w))) * τ.im ^ w := by ring
      _ = τ.im ^ w := by rw [hreal, one_mul]
  linear_combination ((starRingEnd ℂ) (f τ) * g τ) * this

/-- **Independence of the representatives:** for every list $R$ of right coset representatives of $\Gamma_0(4N)$,
$\langle f, g\rangle_{4N} = |R|^{-1}\sum_{\gamma\in R}\int_{\mathcal F}\overline{f(\gamma\tau)}g(\gamma\tau)
\operatorname{Im}(\gamma\tau)^{k+1/2}d\mu$. -/
theorem peterssonLevel_eq_reps (hN : 0 < N) {f g : ℍ → ℂ} (hf : M.Transforms k N χ f)
    (hg : M.Transforms k N χ g) {R : List SL(2, ℤ)} (hR : IsGamma0Reps (4 * N) R) :
    peterssonLevel k N f g = ((R.length : ℂ))⁻¹ * peterssonReps R ((k : ℝ) + 1 / 2) f g := by
  haveI : NeZero (4 * N) := ⟨by omega⟩
  have hR0 := isGamma0Reps_gamma0Reps (L := 4 * N) (by omega)
  have hinv : ∀ γ ∈ Gamma0 (4 * N), ∀ z : ℍ, peterssonIntegrand 1 ((k : ℝ) + 1 / 2) f g (γ • z) =
      peterssonIntegrand 1 ((k : ℝ) + 1 / 2) f g z := fun γ hγ z ↦ M.peterssonIntegrand_smul hf hg hγ z
  rw [peterssonLevel, peterssonReps_eq_of_reps hR0 hR _ f g hinv, hR.length_eq]

/-- **At level 4 it is Kohnen–Zagier's product** `peterssonFour`. -/
theorem peterssonLevel_one {χ : DirichletCharacter ℂ (4 * 1)} {f g : ℍ → ℂ} (hf : M.Transforms k 1 χ f)
    (hg : M.Transforms k 1 χ g) : peterssonLevel k 1 f g = peterssonFour k f g := by
  rw [M.peterssonLevel_eq_reps one_pos hf hg isGamma0Reps_gamma0FourReps, peterssonFour]
  have : (gamma0FourReps.length : ℂ) = 6 := by
    show ((6 : ℕ) : ℂ) = 6
    norm_num
  rw [this]
  ring

end MultiplierSystem

/-- **Hermitian symmetry:** $\langle g, f\rangle_{4N} = \overline{\langle f, g\rangle_{4N}}$. -/
theorem peterssonLevel_conj_symm (k N : ℕ) (f g : ℍ → ℂ) :
    peterssonLevel k N g f = (starRingEnd ℂ) (peterssonLevel k N f g) := by
  rw [peterssonLevel, peterssonLevel, peterssonReps_conj_symm, map_mul, map_inv₀, map_natCast]

/-- **Linearity in the second argument (scalars).** -/
theorem peterssonLevel_smul_right (k N : ℕ) (f g : ℍ → ℂ) (c : ℂ) :
    peterssonLevel k N f (c • g) = c * peterssonLevel k N f g := by
  rw [peterssonLevel, peterssonLevel, peterssonReps_smul_right]
  ring

/-- **Conjugate-linearity in the first argument (scalars).** -/
theorem peterssonLevel_smul_left (k N : ℕ) (f g : ℍ → ℂ) (c : ℂ) :
    peterssonLevel k N (c • f) g = (starRingEnd ℂ) c * peterssonLevel k N f g := by
  rw [peterssonLevel, peterssonLevel, peterssonReps_smul_left]
  ring

/-- **$\langle g, g\rangle_{4N}$ is a nonnegative real number.** -/
theorem peterssonLevel_self_eq_ofReal (k N : ℕ) (g : ℍ → ℂ) :
    peterssonLevel k N g g = ((peterssonLevel k N g g).re : ℂ) ∧ 0 ≤ (peterssonLevel k N g g).re := by
  have h : peterssonLevel k N g g = ((((Gamma0 (4 * N)).index : ℝ))⁻¹ *
      ((gamma0Reps (4 * N)).map fun γ ↦ ∫ τ in ModularGroup.fd,
        ‖g (γ • τ)‖ ^ 2 * (γ • τ).im ^ ((k : ℝ) + 1 / 2)).sum : ℝ) := by
    rw [peterssonLevel, peterssonReps_self_eq_ofReal]
    push_cast
    rfl
  rw [h, Complex.ofReal_re]
  exact ⟨rfl, mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    (peterssonReps_self_nonneg _ _ g)⟩

namespace MultiplierSystem

variable (M : MultiplierSystem) {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)}

/-- **Additivity in the second argument** on $S_{k+1/2}(4N,\chi)$. -/
theorem peterssonLevel_add_right (hN : 0 < N) {f g h : ℍ → ℂ} (hf : f ∈ M.cuspForms k N χ)
    (hg : g ∈ M.cuspForms k N χ) (hh : h ∈ M.cuspForms k N χ) :
    peterssonLevel k N f (g + h) = peterssonLevel k N f g + peterssonLevel k N f h := by
  rw [peterssonLevel, peterssonLevel, peterssonLevel, peterssonReps_add_right _ _ _ _ _
    (fun γ _ ↦ M.integrableOn_peterssonIntegrand k N hN χ hf hg γ)
    (fun γ _ ↦ M.integrableOn_peterssonIntegrand k N hN χ hf hh γ), mul_add]

/-- **Additivity in the first argument** on $S_{k+1/2}(4N,\chi)$. -/
theorem peterssonLevel_add_left (hN : 0 < N) {f g h : ℍ → ℂ} (hf : f ∈ M.cuspForms k N χ)
    (hg : g ∈ M.cuspForms k N χ) (hh : h ∈ M.cuspForms k N χ) :
    peterssonLevel k N (f + g) h = peterssonLevel k N f h + peterssonLevel k N g h := by
  rw [peterssonLevel, peterssonLevel, peterssonLevel, peterssonReps_add_left _ _ _ _ _
    (fun γ _ ↦ M.integrableOn_peterssonIntegrand k N hN χ hf hh γ)
    (fun γ _ ↦ M.integrableOn_peterssonIntegrand k N hN χ hg hh γ), mul_add]

/-- **Definiteness:** $\langle g, g\rangle_{4N} > 0$ for $0 \ne g \in S_{k+1/2}(4N,\chi)$. -/
theorem peterssonLevel_self_re_pos (hN : 0 < N) {g : ℍ → ℂ} (hg : g ∈ M.cuspForms k N χ) (hg0 : g ≠ 0) :
    0 < (peterssonLevel k N g g).re := by
  haveI : NeZero (4 * N) := ⟨by omega⟩
  set w : ℝ := (k : ℝ) + 1 / 2 with hw
  have hR := isGamma0Reps_gamma0Reps (L := 4 * N) (by omega)
  set R := gamma0Reps (4 * N) with hRdef
  set t : SL(2, ℤ) → ℝ := fun γ ↦ ∫ τ in ModularGroup.fd, ‖g (γ • τ)‖ ^ 2 * (γ • τ).im ^ w with ht
  have ht0 : ∀ γ, 0 ≤ t γ := fun γ ↦
    integral_nonneg fun τ ↦ mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (γ • τ).im_pos.le _)
  set S : ℝ := (R.map t).sum with hS
  have hS0 : 0 ≤ S := peterssonReps_self_nonneg R w g
  obtain ⟨i, -, -⟩ := hR 1
  have hlen : 0 < R.length := Fin.pos i
  have hSne : S ≠ 0 := by
    intro hS0'
    set γ : SL(2, ℤ) := R[i.1] with hγ
    have hγmem : γ ∈ R := List.getElem_mem _
    have htγ : t γ = 0 := by
      have hle : t γ ≤ S := List.single_le_sum (fun x hx ↦ by
        obtain ⟨γ', -, rfl⟩ := List.mem_map.1 hx
        exact ht0 γ') _ (List.mem_map_of_mem hγmem)
      linarith [ht0 γ]
    set φ : ℍ → ℝ := fun τ ↦ ‖g (γ • τ)‖ ^ 2 * (γ • τ).im ^ w with hφ
    have hφ0 : 0 ≤ φ := fun τ ↦ mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (γ • τ).im_pos.le _)
    have hφnorm : ∀ τ, ‖peterssonIntegrand γ w g g τ‖ = φ τ := by
      intro τ
      rw [peterssonIntegrand_self, Complex.norm_real, Real.norm_of_nonneg (hφ0 τ)]
    have hφc : Continuous φ := by
      have := (continuous_peterssonIntegrand γ w hg.holo.continuous hg.holo.continuous).norm
      exact this.congr hφnorm
    have hint : IntegrableOn φ ModularGroup.fd := by
      refine IntegrableOn.congr_fun
        ((M.integrableOn_peterssonIntegrand k N hN χ hg hg γ).norm : IntegrableOn _ _ _)
        (fun τ _ ↦ hφnorm τ) measurableSet_fd
    have hae : φ =ᵐ[volume.restrict ModularGroup.fd] 0 :=
      (integral_eq_zero_iff_of_nonneg hφ0 hint).1 htγ
    have hae' : φ =ᵐ[volume.restrict ModularGroup.fdo] 0 :=
      ae_restrict_of_ae_restrict_of_subset ModularGroup.fdo_subset_fd hae
    have heq := Measure.eqOn_open_of_ae_eq hae' ModularGroup.isOpen_fdo hφc.continuousOn continuousOn_const
    have hfdo : ∀ τ ∈ ModularGroup.fdo, g (γ • τ) = 0 := fun τ hτ ↦ by
      have := heq hτ
      simp only [φ, Pi.zero_apply, mul_eq_zero, ne_eq, pow_eq_zero_iff, norm_eq_zero, OfNat.ofNat_ne_zero,
        not_false_eq_true] at this
      rcases this with h1 | h1
      · exact h1
      · exact absurd h1 (Real.rpow_pos_of_pos (γ • τ).im_pos w).ne'
    refine hg0 (eq_zero_of_eqOn_open hg.holo (ModularGroup.isOpen_smul_fdo γ) ?_ ?_)
    · obtain ⟨τ, hτ⟩ := fdo_nonempty
      exact ⟨γ • τ, Set.smul_mem_smul_set hτ⟩
    · rintro _ ⟨τ, hτ, rfl⟩
      exact hfdo τ hτ
  have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hSne)
  have hidx : 0 < (Gamma0 (4 * N)).index := by rw [← hR.length_eq]; exact hlen
  have h : peterssonLevel k N g g = (((((Gamma0 (4 * N)).index : ℝ))⁻¹ * S : ℝ) : ℂ) := by
    rw [peterssonLevel, peterssonReps_self_eq_ofReal]
    push_cast
    rfl
  rw [h, Complex.ofReal_re]
  exact mul_pos (inv_pos.2 (Nat.cast_pos.2 hidx)) hSpos

/-- **The Petersson product is a positive definite Hermitian form on $S_{k+1/2}(4N,\chi)$**, in the convention of
`PosDefHermitian` (linear in the first argument): $P(f, g) = \langle g, f\rangle_{4N}$. -/
theorem posDefHermitian_peterssonLevel (hN : 0 < N) :
    PosDefHermitian (fun f g : M.cuspForms k N χ ↦ peterssonLevel k N (g : ℍ → ℂ) (f : ℍ → ℂ)) where
  add_left x y z := M.peterssonLevel_add_right hN z.2 x.2 y.2
  smul_left c x y := peterssonLevel_smul_right k N _ _ c
  conj_symm x y := peterssonLevel_conj_symm k N _ _
  pos x hx := M.peterssonLevel_self_re_pos hN x.2 (fun h ↦ hx (Subtype.ext h))

/-- **Orthogonal decomposition of $S_{k+1/2}(4N,\chi)$** along a finite-dimensional subspace $U$ (the parameter `P` of
`exists_orthogonal_decomposition` instantiated with the Petersson product): $f = u + (f - u)$ with $u \in U$ and
$\langle v, f - u\rangle_{4N} = 0$ for all $v \in U$. -/
theorem exists_orthogonal_decomposition_peterssonLevel (hN : 0 < N) (U : Submodule ℂ (M.cuspForms k N χ))
    [FiniteDimensional ℂ U] (f : M.cuspForms k N χ) :
    ∃ u ∈ U, ∀ v ∈ U, peterssonLevel k N (v : ℍ → ℂ) ((f - u : M.cuspForms k N χ) : ℍ → ℂ) = 0 :=
  (exists_orthogonal_decomposition (M.posDefHermitian_peterssonLevel hN) U f)

end MultiplierSystem

end ModularFormsKB.HalfIntegral
