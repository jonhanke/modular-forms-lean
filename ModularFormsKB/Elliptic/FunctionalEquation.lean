import ModularFormsKB.Elliptic.Bridge
import TauCeti.AlgebraicGeometry.EllipticCurve.BirchSwinnertonDyer.Statement
import TauCeti.NumberTheory.ModularForms.LFunction.Parity

/-!
# The functional equation of $L(E, s)$ for a curve with a newform

Let $E$ have the newform $f$ of level $N$ (`HasNewform E N f`). Put
$$\Lambda(E, s) = N^{s/2}(2\pi)^{-s}\Gamma(s)L(E, s)$$
(`completedLE f`, Tau Ceti's `CuspForm.frickeCompletedL` of $f$, an entire function) and $w_E = -\varepsilon_N(f)$
(`rootNumber f`, $\varepsilon_N(f)$ the Fricke sign). Then:
- `HasNewform.completedLE_eq`: $\Lambda(E, s)$ is given by the Dirichlet series of $E$ on $\operatorname{Re}s > 3/2$;
- `differentiable_completedLE`: it is entire;
- `HasNewform.completedLE_two_sub`: $\Lambda(E, 2 - s) = w_E\Lambda(E, s)$, with `rootNumber_eq_one_or_neg_one`;
- `HasNewform.hasEntireExtension`, `HasNewform.isContinuationOn`: $L(E, s)$ is entire, the extension being Mathlib's
  `ModularForm.L` of $f$;
- **parity**: `HasNewform.eq_zero_at_one_of_isContinuationOn`: if $w_E = -1$, every continuation of $L(E, s)$ to a
  connected open set containing $1$ vanishes at $1$; `HasNewform.rootNumber_eq_neg_one_pow`:
  $w_E = (-1)^{r}$ with $r$ the order of vanishing of $L(E, s)$ at $s = 1$;
- `HasNewform.finrank_pos_of_rootNumber_eq_neg_one`: under Tau Ceti's `BirchSwinnertonDyer E`, $w_E = -1$ forces
  $\operatorname{rank} E(\mathbb Q) \ge 1$.

The sign: Hecke's relation $\Lambda_N(2 - s, f) = i^2\varepsilon_N(f)\Lambda_N(s, f)$ (Tau Ceti
`Newform.frickeCompletedL_sub_eq`), so $w_E = -\varepsilon_N(f)$, as in Milne (Section 11, after Theorem 11.19:
$w = -\varepsilon$ where $f|_2 w_N = \varepsilon f$) [unverified against the book's sign convention].
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Complex
open scoped MatrixGroups Real

namespace ModularFormsKB.Elliptic

open HeckeRing.GL2

variable {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N] {f : Newform N 2}

/-- **The completed $L$-function** $\Lambda(E, s) = N^{s/2}(2\pi)^{-s}\Gamma(s)L(f, s)$ of the newform $f$ (Tau Ceti's
level-$N$ completion, the Mellin transform of $f(it/\sqrt N)$). -/
noncomputable def completedLE (f : Newform N 2) (s : ℂ) : ℂ :=
  CuspForm.frickeCompletedL f.toCuspForm (N.toPNat (NeZero.pos N)) s

/-- **The root number** $w = -\varepsilon_N(f)$ of a newform of weight $2$ and trivial nebentypus. -/
noncomputable def rootNumber (f : Newform N 2) (hχ : f.χ = 1) : ℂ :=
  -f.frickeSign hχ

private theorem rootNumber_eq (f : Newform N 2) (hχ : f.χ = 1) :
    rootNumber f hχ = Complex.I ^ (2 : ℤ) * f.frickeSign hχ := by
  simp [rootNumber]

theorem rootNumber_eq_one_or_neg_one (f : Newform N 2) (hχ : f.χ = 1) :
    rootNumber f hχ = 1 ∨ rootNumber f hχ = -1 := by
  rw [rootNumber_eq]
  exact Newform.I_zpow_mul_frickeSign_eq_one_or_neg_one f hχ

/-- $\Lambda(E, s)$ is entire. -/
theorem differentiable_completedLE (f : Newform N 2) : Differentiable ℂ (completedLE f) :=
  CuspForm.differentiable_frickeCompletedL f.toCuspForm (N.toPNat (NeZero.pos N))

private theorem L_eq_LSeries_of_two_lt (hf : HasNewform E N f) {s : ℂ} (hs : 2 < s.re) :
    ModularForm.L (by norm_num : (0 : ℤ) < 2) f.toCuspForm s = LSeries (coeffE E) s := by
  have h := CuspForm.hasSum_L (by norm_num : (0 : ℤ) < 2) f.toCuspForm (s := s)
    (by push_cast; linarith)
  simp only [strictWidthInfty_Gamma1, Complex.ofReal_one, Complex.one_cpow, one_mul] at h
  have hfun : (fun n : ℕ ↦ LSeries.term (coeffE E) s n) =
      fun n : ℕ ↦ (qExpansion 1 f.toCuspForm).coeff n / (n : ℂ) ^ s := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hf.coeff_eq 0]
    · rw [LSeries.term_of_ne_zero hn, hf.coeff_eq n]; rfl
  rw [LSeries, hfun]
  exact h.tsum_eq.symm

private theorem L_eq_LSeries (hf : HasNewform E N f) [E.IsElliptic] {s : ℂ} (hs : 3 / 2 < s.re) :
    ModularForm.L (by norm_num : (0 : ℤ) < 2) f.toCuspForm s = LSeries (coeffE E) s := by
  have hW : AnalyticOnNhd ℂ (LSeries (coeffE E)) {s : ℂ | 3 / 2 < s.re} :=
    (LSeries_analyticOnNhd (coeffE E)).mono fun z (hz : 3 / 2 < z.re) ↦
      (abscissaOfAbsConv_coeffE_le E).trans_lt (EReal.coe_lt_coe_iff.2 hz)
  have hL : AnalyticOnNhd ℂ (ModularForm.L (by norm_num : (0 : ℤ) < 2) f.toCuspForm)
      {s : ℂ | 3 / 2 < s.re} :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (CuspForm.differentiable_L (by norm_num : (0 : ℤ) < 2) f.toCuspForm)).mono (Set.subset_univ _)
  have h3 : ((3 : ℝ) : ℂ) ∈ {s : ℂ | 3 / 2 < s.re} := by simp
  have hev : ModularForm.L (by norm_num : (0 : ℤ) < 2) f.toCuspForm =ᶠ[nhds ((3 : ℝ) : ℂ)]
      LSeries (coeffE E) := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨{z : ℂ | 2 < z.re}, (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_,
        fun z hz ↦ L_eq_LSeries_of_two_lt hf hz⟩
    simp; norm_num
  exact hL.eqOn_of_preconnected_of_eventuallyEq hW (convex_halfSpace_re_gt (3 / 2 : ℝ)).isPreconnected
    h3 hev hs

/-- On $\operatorname{Re}s > 3/2$, $\Lambda(E, s) = N^{s/2}(2\pi)^{-s}\Gamma(s)\sum_n a_n(E)n^{-s}$. -/
theorem HasNewform.completedLE_eq (hf : HasNewform E N f) [E.IsElliptic] {s : ℂ} (hs : 3 / 2 < s.re) :
    completedLE f s = (N : ℂ) ^ (s / 2) * (2 * π : ℂ) ^ (-s) * Gamma s * LSeries (coeffE E) s := by
  have hk : (0 : ℤ) < 2 := by norm_num
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos (by linarith)
  have hG : Gammaℂ s ≠ 0 := by
    rw [Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos (by linarith))
    rw [Ne, Complex.cpow_eq_zero_iff]
    simp [Real.pi_ne_zero]
  have h1 : completedLE f s = (N : ℂ) ^ (s / 2) * ModularForm.Λ hk f.toCuspForm s :=
    CuspForm.frickeCompletedL_eq_cpow_mul_Λ f.toCuspForm (N.toPNat (NeZero.pos N)) hk s
  have h2 : ModularForm.Λ hk f.toCuspForm s =
      ModularForm.L hk f.toCuspForm s * Gammaℂ s / 2 := by
    rw [ModularForm.L_apply_of_ne_zero hk f.toCuspForm hs0]
    field_simp
  rw [h1, h2, L_eq_LSeries hf hs, Gammaℂ]
  ring

/-- **The functional equation** $\Lambda(E, 2 - s) = w_E\,\Lambda(E, s)$ (row 21). -/
theorem HasNewform.completedLE_two_sub (hf : HasNewform E N f) (s : ℂ) :
    completedLE f (2 - s) = rootNumber f hf.χ_eq_one * completedLE f s := by
  have := Newform.frickeCompletedL_sub_eq f hf.χ_eq_one s
  rw [rootNumber_eq]
  simpa [completedLE] using this

/-- **$L(E, s)$ is entire** (row 21): the Dirichlet series of $E$ has an entire extension. -/
theorem HasNewform.hasEntireExtension (hf : HasNewform E N f) [E.IsElliptic] :
    LSeries.HasEntireExtension (coeffE E) :=
  LSeries.HasEntireExtension.of_extension_of_eq_on_lt_re (c := 3 / 2)
    ((abscissaOfAbsConv_coeffE_le E).trans_lt (EReal.coe_lt_top _))
    (CuspForm.differentiable_L (by norm_num : (0 : ℤ) < 2) f.toCuspForm)
    (fun hs ↦ L_eq_LSeries hf hs)

/-- Mathlib's $L$-function of $f$ is a continuation of $L(E, s)$ to $\mathbb C$, in the sense of Tau Ceti's
Birch–Swinnerton-Dyer statement. -/
theorem HasNewform.isContinuationOn (hf : HasNewform E N f) [E.IsElliptic] :
    LSeries.IsContinuationOn ((↑) ∘ E.LFunction) (ModularForm.L (by norm_num : (0 : ℤ) < 2) f.toCuspForm)
      Set.univ := by
  obtain ⟨F, hFd, hFa⟩ := hf.hasEntireExtension.exists_extension
  have hLF : ModularForm.L (by norm_num : (0 : ℤ) < 2) f.toCuspForm = F := by
    have hL := (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (CuspForm.differentiable_L (by norm_num : (0 : ℤ) < 2) f.toCuspForm))
    have hF := Complex.analyticOnNhd_univ_iff_differentiable.mpr hFd
    have hlt : ∀ {s : ℂ}, 3 / 2 < s.re → LSeries.abscissaOfAbsConv (coeffE E) < s.re :=
      fun {s} (hs : 3 / 2 < s.re) ↦
        (abscissaOfAbsConv_coeffE_le E).trans_lt (EReal.coe_lt_coe_iff.2 hs)
    refine funext fun s ↦ hL.eqOn_of_preconnected_of_eventuallyEq hF isPreconnected_univ
      (Set.mem_univ ((3 : ℝ) : ℂ)) ?_ (Set.mem_univ s)
    refine Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨{z : ℂ | 3 / 2 < z.re}, (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_,
        fun z hz ↦ ?_⟩
    · simp
    · rw [hFa (hlt hz)]; exact L_eq_LSeries hf hz
  refine ⟨isOpen_univ, isPreconnected_univ, Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (CuspForm.differentiable_L (by norm_num : (0 : ℤ) < 2) f.toCuspForm),
    ⟨2, Set.mem_univ _, ?_⟩, fun s _ hs ↦ ?_⟩
  · exact (abscissaOfAbsConv_coeffE_le E).trans_lt (by simp; norm_num)
  · rw [hLF]; exact hFa hs

/-- **Parity, first form** (row 21): if $w_E = -1$, then every continuation of $L(E, s)$ to a connected open set
containing $1$ vanishes at $s = 1$. -/
theorem HasNewform.eq_zero_at_one_of_isContinuationOn (hf : HasNewform E N f) [E.IsElliptic]
    (hw : rootNumber f hf.χ_eq_one = -1) {F : ℂ → ℂ} {U : Set ℂ}
    (hF : LSeries.IsContinuationOn ((↑) ∘ E.LFunction) F U) (h1 : 1 ∈ U) : F 1 = 0 := by
  have hk : (0 : ℤ) < 2 := by norm_num
  have hε : f.frickeSign hf.χ_eq_one = 1 := by
    rw [rootNumber_eq] at hw
    have : Complex.I ^ (2 : ℤ) = -1 := by simp
    rw [this] at hw
    linear_combination -hw
  have hsign : Complex.I ^ (2 : ℤ) * f.frickeSign hf.χ_eq_one ≠ 1 := by
    have hI : Complex.I ^ (2 : ℤ) = -1 := by simp
    rw [hε, hI]; norm_num
  have hL0 := CuspForm.L_eq_zero_of_normalizedFrickeOperatorCusp_eq_smul f.toCuspForm hk
    (f.normalizedFrickeOperatorCusp_eq_frickeSign_smul hf.χ_eq_one) hsign
  have heq := hF.eqOn_of_subset hf.isContinuationOn (Set.subset_univ U) h1
  rw [heq]
  simpa using hL0

/-- **Parity** (row 21): $w_E = (-1)^r$, $r$ the order of vanishing of $L(E, s)$ at $s = 1$ (Tau Ceti's analytic rank
of $f$). -/
theorem HasNewform.rootNumber_eq_neg_one_pow (hf : HasNewform E N f) :
    rootNumber f hf.χ_eq_one = (-1) ^ f.analyticRank (by norm_num : (0 : ℤ) < 2) := by
  rw [rootNumber_eq]
  exact (Newform.neg_one_pow_analyticRank_eq_I_zpow_mul_frickeSign f hf.χ_eq_one
    (by norm_num)).symm

/-- Under the Birch–Swinnerton-Dyer conjecture for $E$ (Tau Ceti), $w_E = -1$ forces $E(\mathbb Q)$ to have positive
rank. -/
theorem HasNewform.finrank_pos_of_rootNumber_eq_neg_one (hf : HasNewform E N f) [E.IsElliptic]
    (hBSD : E.BirchSwinnertonDyer) (hw : rootNumber f hf.χ_eq_one = -1) :
    0 < Module.finrank ℤ E.toAffine.Point := by
  have h := hBSD.apply_one_ne_zero_iff hf.isContinuationOn (Set.mem_univ 1)
  exact Nat.pos_of_ne_zero fun h0 ↦
    h.mpr h0 (hf.eq_zero_at_one_of_isContinuationOn hw hf.isContinuationOn (Set.mem_univ 1))

end ModularFormsKB.Elliptic
