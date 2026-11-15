/-
# The lattice theta inversion formula, proved

This file proves the named input `LatticeThetaInversion` of
`Miyake/HeckeTrick/EisensteinFE.lean` (LE-MF-0242), hence `EisensteinFE` unconditionally (`eisensteinFE`).

**The formula.** For $L \ge 1$, $z = x+iy \in \mathbf H$, $u > 0$, $\lambda \ge 0$ and a character $\omega$ mod $L$:
$$\Theta(z,u) = \sum_{(c,d)}\omega(d)\,v^\lambda e^{-\pi u|v|^2} = (L^2y)^{-1}(Ly)^{-\lambda}u^{-1-\lambda}
\check\Theta\big(z, 1/(L^2y^2u)\big), \qquad v = Lcz + d.$$

**Proof.** Write $d = a + Le$ with $0 \le a < L$ (`splitEquiv`); then $v = a + \ell$ with $\ell$ in the lattice
$\Lambda = \mathbb Z\,Lz + \mathbb Z\,L$ (Mathlib's `PeriodPair.lattice`), and $\omega(d) = \omega(a)$. Poisson summation over
$\Lambda$ (Tau Ceti's `SchwartzMap.tsum_eq_tsum_dual_fourier`) applied to the Schwartz function
$f(x) = x^\lambda e^{-\pi u|x|^2}$ on $\mathbb C = \mathbb R^2$ (`sphGauss` of `Miyake/Sec4_9/Spherical/Inversion.lean` with the
isotropic pair $u = 1$, $w = i$, so that the spherical weight is $x \mapsto x$), whose Fourier transform is
$(-i/u)^\lambda u^{-1}\xi^\lambda e^{-\pi|\xi|^2/u}$ (`fourier_sphGauss_apply`). The covolume of $\Lambda$ is $L^2y$
(`ZLattice.covolume_eq_abs_im`) and its dual lattice is $\frac{i}{Ly}(\mathbb Zz + \mathbb Z)$ (`dual_lattice_eq`):
for $m = \frac{i}{Ly}(pz+q)$, $\langle m, Lz\rangle = q$ and $\langle m, L\rangle = -p$. The phase is
$e(\langle a, m\rangle) = e(-ap/L)$, and the sum over $a$ is the Gauss sum $G(\omega, -p)$ (`gaussAt`).
-/
import ModularFormsKB.Miyake.HeckeTrick.EisensteinFEMain
import ModularFormsKB.Miyake.Sec4_9.Spherical.Inversion
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import TauCeti.Algebra.Module.ZLattice.Complex
import TauCeti.Analysis.Fourier.PoissonSummation

open MeasureTheory Set Filter Topology Complex Module
open scoped UpperHalfPlane Real InnerProductSpace

noncomputable section

namespace ModularFormsKB.Miyake.HeckeTrick

open ModularFormsKB.HalfIntegral

namespace Inversion

variable {L : ℕ}

/-! ### The inner product on `ℂ` -/

lemma inner_eq (a b : ℂ) : ⟪a, b⟫_ℝ = (starRingEnd ℂ a * b).re := by
  rw [Complex.inner, mul_comm]

lemma isSpherical (ν : ℕ) : Sec4_9.IsSphericalDatum ν (1 : ℂ) I := by
  right
  refine ⟨by simp, ?_⟩
  rw [inner_eq]; simp

lemma isoForm_one_I (x : ℂ) : Sec4_9.isoForm (1 : ℂ) I x = x := by
  unfold Sec4_9.isoForm
  rw [inner_eq, inner_eq]
  apply Complex.ext <;> simp

/-! ### The lattice `Λ = ℤ Lz + ℤ L` and its dual -/

lemma indep_of_im {a b : ℂ} (h : (starRingEnd ℂ a * b).im ≠ 0) : LinearIndependent ℝ ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg Complex.re hst
  have h2 := congrArg Complex.im hst
  simp at h1 h2
  have hdet : a.re * b.im - a.im * b.re ≠ 0 := by
    intro h'
    apply h
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    linarith
  constructor
  · by_contra hs
    apply hdet
    have : s * (a.re * b.im - a.im * b.re) = 0 := by linear_combination b.im * h1 - b.re * h2
    exact (mul_eq_zero.mp this).resolve_left hs
  · by_contra ht
    apply hdet
    have : t * (a.re * b.im - a.im * b.re) = 0 := by linear_combination a.re * h2 - a.im * h1
    exact (mul_eq_zero.mp this).resolve_left ht

/-- The period pair $(Lz, L)$. -/
def pp (hL : 1 ≤ L) (z : ℍ) : PeriodPair where
  ω₁ := (L : ℂ) * z
  ω₂ := L
  indep := indep_of_im (by
    have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
    simp [Complex.mul_im]
    exact ⟨⟨by omega, z.im_ne_zero⟩, by omega⟩)

/-- The dual period pair $(iz/(Ly), i/(Ly))$. -/
def ppDual (hL : 1 ≤ L) (z : ℍ) : PeriodPair where
  ω₁ := I * z / ((L : ℂ) * z.im)
  ω₂ := I / ((L : ℂ) * z.im)
  indep := indep_of_im (by
    have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
    have hy := z.im_pos
    have hc : ((L : ℝ) * z.im) ≠ 0 := by positivity
    have hc' : (((L : ℝ) * z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
    have e1 : I * z / ((L : ℂ) * z.im) = (((1 / ((L : ℝ) * z.im) : ℝ)) : ℂ) * (I * z) := by
      push_cast at hc' ⊢; field_simp
    have e2 : I / ((L : ℂ) * z.im) = (((1 / ((L : ℝ) * z.im) : ℝ)) : ℂ) * I := by
      push_cast at hc' ⊢; field_simp
    rw [e1, e2]
    have : (starRingEnd ℂ ((((1 / ((L : ℝ) * z.im) : ℝ)) : ℂ) * (I * z)) *
        ((((1 / ((L : ℝ) * z.im) : ℝ)) : ℂ) * I)) =
        (((1 / ((L : ℝ) * z.im) : ℝ) ^ 2 : ℝ) : ℂ) * starRingEnd ℂ (z : ℂ) := by
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_pow]
      linear_combination (-(((1 / ((L : ℝ) * z.im) : ℝ) : ℂ) ^ 2 * starRingEnd ℂ (z : ℂ))) * I_sq
    rw [this, Complex.im_ofReal_mul]
    simp only [Complex.conj_im, UpperHalfPlane.coe_im]
    have : 0 < (1 / ((L : ℝ) * z.im)) ^ 2 := by positivity
    intro h0
    nlinarith)

lemma covolume_pp (hL : 1 ≤ L) (z : ℍ) :
    ZLattice.covolume (pp hL z).lattice = (L : ℝ) ^ 2 * z.im := by
  rw [ZLattice.covolume_eq_abs_im _ (pp hL z).latticeBasis]
  rw [PeriodPair.latticeBasis_zero, PeriodPair.latticeBasis_one]
  have : (starRingEnd ℂ ((L : ℂ) * z) * (L : ℂ)).im = -((L : ℝ) ^ 2 * z.im) := by
    simp [Complex.mul_im]; ring
  show |(starRingEnd ℂ ((L : ℂ) * z) * (L : ℂ)).im| = _
  rw [this, abs_neg, abs_of_pos (by have := z.im_pos; have : (0 : ℝ) < L := (by exact_mod_cast hL); positivity)]

/-- The pairings with the dual basis: $\langle\alpha\omega_1' + \beta\omega_2', aLz + bL\rangle = a\beta - b\alpha$. -/
lemma inner_dual (hL : 1 ≤ L) (z : ℍ) (α β a b : ℝ) :
    ⟪(α : ℂ) * (ppDual hL z).ω₁ + β * (ppDual hL z).ω₂, (a : ℂ) * (pp hL z).ω₁ + b * (pp hL z).ω₂⟫_ℝ =
      a * β - b * α := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  have hy := z.im_ne_zero
  rw [inner_eq]
  simp only [pp, ppDual]
  set x := z.re; set y := z.im
  have hz : (z : ℂ) = x + y * I := by apply Complex.ext <;> simp [x, y]
  rw [hz]
  simp [map_div₀, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq]
  field_simp
  ring

lemma dual_lattice_eq (hL : 1 ≤ L) (z : ℍ) :
    ZLattice.dual (pp hL z).lattice = (ppDual hL z).lattice := by
  ext m
  rw [ZLattice.mem_dual, PeriodPair.mem_lattice]
  -- coordinates of `m` in the dual basis
  obtain ⟨α, β, hm⟩ : ∃ α β : ℝ, (α : ℂ) * (ppDual hL z).ω₁ + β * (ppDual hL z).ω₂ = m := by
    have := (ppDual hL z).basis.sum_repr m
    refine ⟨(ppDual hL z).basis.repr m 0, (ppDual hL z).basis.repr m 1, ?_⟩
    rw [Fin.sum_univ_two] at this
    simpa [Complex.real_smul] using this
  subst hm
  constructor
  · intro h
    obtain ⟨q, hq⟩ := h ((pp hL z).ω₁) (pp hL z).ω₁_mem_lattice
    obtain ⟨p, hp⟩ := h ((pp hL z).ω₂) (pp hL z).ω₂_mem_lattice
    have e1 := inner_dual hL z α β 1 0
    have e2 := inner_dual hL z α β 0 1
    simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, add_zero, zero_add, sub_zero,
      zero_sub] at e1 e2
    rw [e1] at hq; rw [e2] at hp
    refine ⟨-p, q, ?_⟩
    rw [hq, show α = -(p : ℝ) by linarith]
    push_cast; ring
  · rintro ⟨p, q, hpq⟩ y hy
    obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.mp hy
    have hαβ : α = p ∧ β = q := by
      have := LinearIndependent.pair_iff.mp (ppDual hL z).indep (α - p) (β - q) (by
        simp only [Complex.real_smul]; push_cast; linear_combination -hpq)
      constructor <;> linarith [this.1, this.2]
    obtain ⟨rfl, rfl⟩ := hαβ
    refine ⟨a * q - b * p, ?_⟩
    have := inner_dual hL z p q a b
    push_cast at this ⊢
    exact this

/-! ### Splitting the second coordinate modulo `L` -/

/-- $(c, d) \mapsto (d \bmod L, (c, d \div L))$. -/
def splitEquiv (hL : 1 ≤ L) : ℤ × ℤ ≃ Fin L × (ℤ × ℤ) where
  toFun p := (⟨(p.2 % L).toNat, by
      have h1 := Int.emod_nonneg p.2 (show (L : ℤ) ≠ 0 by omega)
      have h2 := Int.emod_lt_of_pos p.2 (show (0 : ℤ) < L by omega)
      omega⟩, (p.1, p.2 / L))
  invFun q := (q.2.1, (q.1 : ℤ) + L * q.2.2)
  left_inv p := by
    have h1 := Int.emod_nonneg p.2 (show (L : ℤ) ≠ 0 by omega)
    simp only [Int.toNat_of_nonneg h1]
    ext
    · rfl
    · simp only; rw [Int.emod_def]; ring
  right_inv q := by
    obtain ⟨a, c, e⟩ := q
    have ha : (a : ℤ) < L := by exact_mod_cast a.2
    have hL' : (0 : ℤ) < L := by omega
    have hmod : ((a : ℤ) + L * e) % L = a := by
      rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) ha]
    have hdiv : ((a : ℤ) + L * e) / L = e := by
      rw [Int.add_mul_ediv_left _ _ (by omega), Int.ediv_eq_zero_of_lt (by omega) ha, zero_add]
    ext
    · simp [hmod]
    · simp [hdiv]
    · simp [hdiv]

/-! ### The Schwartz function and its Fourier transform -/

lemma hb {u : ℝ} (hu : 0 < u) : 0 < ((π * u : ℝ) : ℂ).re := by simpa using mul_pos Real.pi_pos hu

/-- $f(x) = x^\lambda e^{-\pi u|x|^2}$. -/
def f (lam : ℕ) {u : ℝ} (hu : 0 < u) : SchwartzMap ℂ ℂ := Sec4_9.sphGauss lam (1 : ℂ) I (hb hu)

lemma f_apply (lam : ℕ) {u : ℝ} (hu : 0 < u) (x : ℂ) :
    f lam hu x = x ^ lam * ((Real.exp (-π * u * ‖x‖ ^ 2) : ℝ) : ℂ) := by
  rw [f, Sec4_9.sphGauss_apply (isSpherical lam), isoForm_one_I]
  congr 1
  push_cast
  ring_nf

lemma fourier_f (lam : ℕ) {u : ℝ} (hu : 0 < u) (ξ : ℂ) :
    FourierTransform.fourier (f lam hu : ℂ → ℂ) ξ =
      ((-I / u) ^ lam * (u : ℂ)⁻¹) * (ξ ^ lam * ((Real.exp (-π / u * ‖ξ‖ ^ 2) : ℝ) : ℂ)) := by
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : ((-2 * ((π * u : ℝ) : ℂ)) ^ lam)⁻¹ * (2 * π * I * ξ) ^ lam = (-I / u) ^ lam * ξ ^ lam := by
    rw [← inv_pow, ← mul_pow, ← mul_pow]
    congr 1
    push_cast
    field_simp
  have h2 : (π : ℂ) / ((π * u : ℝ) : ℂ) = (u : ℂ)⁻¹ := by
    push_cast; field_simp
  have h3 : cexp (-(π : ℂ) ^ 2 * (‖ξ‖ : ℂ) ^ 2 / ((π * u : ℝ) : ℂ)) =
      ((Real.exp (-π / u * ‖ξ‖ ^ 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    field_simp
  rw [f, Sec4_9.fourier_sphGauss_apply, isoForm_one_I, Complex.finrank_real_complex,
    show ((2 : ℕ) : ℂ) / 2 = 1 by norm_num, Complex.cpow_one, h1, h2, h3]
  ring

/-! ### Assembly -/

/-- The coefficient bound for `ω`. -/
lemma norm_omega_le (hL : 1 ≤ L) (ω : DirichletCharacter ℂ L) (p : ℤ × ℤ) : ‖ω (p.2 : ZMod L)‖ ≤ 1 :=
  DirichletCharacter.norm_le_one ω _

theorem latticeThetaInversion : LatticeThetaInversion := by
  refine ⟨fun L lam ω hL z u hu ↦ ?_⟩
  have : NeZero L := ⟨by omega⟩
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hy := z.im_pos
  set Λ := (pp hL z).lattice
  -- step 1: split `d = a + L e`
  set g : ℤ × ℤ → ℂ := fun p ↦ ω (p.2 : ZMod L) * ((L : ℂ) * p.1 * z + p.2) ^ lam *
    ((Real.exp (-π * u * ‖(L : ℂ) * p.1 * z + p.2‖ ^ 2) : ℝ) : ℂ)
  have hg : Summable g := by
    have := summable_genTheta (a := L) (lam := lam) (c := fun p ↦ ω (p.2 : ZMod L)) (C := 1) hL
      (norm_omega_le hL ω) z hu
    exact this.of_norm
  have hsplit : latticeTheta L lam ω z u =
      ∑ a : Fin L, ω (a : ZMod L) * ∑' ℓ : Λ, f lam hu ((a : ℂ) + ℓ) := by
    rw [latticeTheta, ← (splitEquiv hL).symm.tsum_eq]
    have hg' : Summable (g ∘ (splitEquiv hL).symm) := (Equiv.summable_iff _).2 hg
    refine Eq.trans (hg'.tsum_prod' (fun a ↦ hg'.prod_factor a)) ?_
    rw [tsum_fintype]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← tsum_mul_left, ← (pp hL z).latticeEquivProd.symm.toEquiv.tsum_eq]
    refine tsum_congr fun ce ↦ ?_
    have hpt : ((pp hL z).latticeEquivProd.symm ce : ℂ) = ce.1 * ((L : ℂ) * z) + ce.2 * L :=
      (pp hL z).latticeEquiv_symm_apply ce
    simp only [Function.comp_apply, g, splitEquiv, Equiv.coe_fn_symm_mk, LinearEquiv.coe_toEquiv]
    rw [f_apply, hpt]
    have hω : ω ((((a : ℕ) : ℤ) + L * ce.2 : ℤ) : ZMod L) = ω ((a : ℕ) : ZMod L) := by
      congr 1; push_cast; simp
    rw [hω]
    have hv : (L : ℂ) * (ce.1 : ℂ) * z + (((a : ℕ) : ℤ) + L * ce.2 : ℤ) =
        ((a : ℕ) : ℂ) + (ce.1 * ((L : ℂ) * z) + ce.2 * L) := by push_cast; ring
    rw [hv]; ring
  -- step 2: Poisson summation on each coset
  have hpois : ∀ a : Fin L, ∑' ℓ : Λ, f lam hu ((a : ℂ) + ℓ) =
      ((L : ℂ) ^ 2 * z.im)⁻¹ * ∑' pq : ℤ × ℤ,
        ((-I / u) ^ lam * (u : ℂ)⁻¹) * ((I / ((L : ℂ) * z.im)) ^ lam *
          (((pq.1 : ℂ) * z + pq.2) ^ lam *
            ((Real.exp (-π * (1 / ((L : ℝ) ^ 2 * z.im ^ 2 * u)) * ‖(pq.1 : ℂ) * z + pq.2‖ ^ 2) : ℝ) : ℂ))) *
          cexp (2 * π * I * a * (-pq.1) / L) := by
    intro a
    rw [SchwartzMap.tsum_eq_tsum_dual_fourier, covolume_pp]
    push_cast
    congr 1
    -- reindex the dual lattice by `(p, q)`
    have hD := dual_lattice_eq hL z
    let e : ZLattice.dual Λ ≃ ℤ × ℤ :=
      (Equiv.subtypeEquivProp (by rw [hD])).trans (ppDual hL z).latticeEquivProd.toEquiv
    rw [← e.symm.tsum_eq]
    refine tsum_congr fun pq ↦ ?_
    have hm : ((e.symm pq : ZLattice.dual Λ) : ℂ) = pq.1 * (I * z / ((L : ℂ) * z.im)) +
        pq.2 * (I / ((L : ℂ) * z.im)) := by
      simp only [e, Equiv.symm_trans_apply]
      exact (ppDual hL z).latticeEquiv_symm_apply pq
    rw [hm, fourier_f]
    have hm' : (pq.1 : ℂ) * (I * z / ((L : ℂ) * z.im)) + pq.2 * (I / ((L : ℂ) * z.im)) =
        (I / ((L : ℂ) * z.im)) * ((pq.1 : ℂ) * z + pq.2) := by ring
    rw [hm', mul_pow]
    have hnorm : ‖(I / ((L : ℂ) * z.im)) * ((pq.1 : ℂ) * z + pq.2)‖ ^ 2 =
        ‖(pq.1 : ℂ) * z + pq.2‖ ^ 2 / ((L : ℝ) ^ 2 * z.im ^ 2) := by
      rw [norm_mul, norm_div, norm_I, norm_mul, Complex.norm_natCast, Complex.norm_real,
        Real.norm_of_nonneg hy.le]
      field_simp
    have hphase : ⟪((a : ℕ) : ℂ), (I / ((L : ℂ) * z.im)) * ((pq.1 : ℂ) * z + pq.2)⟫_ℝ =
        (a : ℝ) * (-pq.1) / L := by
      rw [← hm']
      have := inner_dual hL z pq.1 pq.2 0 0
      rw [inner_eq]
      set x := z.re
      have hz : (z : ℂ) = x + z.im * I := by apply Complex.ext <;> simp [x]
      rw [hz]
      simp [map_div₀, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq]
      field_simp
    have e1 : -π / u * (‖(pq.1 : ℂ) * z + pq.2‖ ^ 2 / ((L : ℝ) ^ 2 * z.im ^ 2)) =
        -π * (1 / ((L : ℝ) ^ 2 * z.im ^ 2 * u)) * ‖(pq.1 : ℂ) * z + pq.2‖ ^ 2 := by
      field_simp
    have e2 : cexp (2 * π * I * (((a : ℝ) * (-pq.1) / L : ℝ) : ℂ)) =
        cexp (2 * π * I * a * (-pq.1) / L) := by
      congr 1; push_cast; ring
    rw [hnorm, hphase, e1, e2]
    push_cast
    ring_nf
  -- step 3: collect the Gauss sums
  rw [hsplit]
  simp_rw [hpois]
  set K : ℂ := ((L : ℂ) ^ 2 * z.im)⁻¹ * ((-I / u) ^ lam * (u : ℂ)⁻¹) * (I / ((L : ℂ) * z.im)) ^ lam
  set D : ℤ × ℤ → ℂ := fun pq ↦ ((pq.1 : ℂ) * z + pq.2) ^ lam *
    ((Real.exp (-π * (1 / ((L : ℝ) ^ 2 * z.im ^ 2 * u)) * ‖(pq.1 : ℂ) * z + pq.2‖ ^ 2) : ℝ) : ℂ)
  have hD : Summable D := by
    have := summable_genTheta (a := 1) (lam := lam) (c := fun _ ↦ (1 : ℂ)) (C := 1) le_rfl
      (fun _ ↦ by simp) z (u := 1 / ((L : ℝ) ^ 2 * z.im ^ 2 * u)) (by positivity)
    refine this.of_norm.congr fun pq ↦ ?_
    simp [D, genVec]
  have hterm : ∀ a : Fin L, ω (a : ZMod L) * (((L : ℂ) ^ 2 * z.im)⁻¹ * ∑' pq : ℤ × ℤ,
        ((-I / u) ^ lam * (u : ℂ)⁻¹) * ((I / ((L : ℂ) * z.im)) ^ lam * D pq) *
          cexp (2 * π * I * a * (-pq.1) / L)) =
      ∑' pq : ℤ × ℤ, K * (ω (a : ZMod L) * cexp (2 * π * I * a * (-pq.1) / L)) * D pq := by
    intro a
    rw [← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun pq ↦ ?_
    simp only [K]; ring
  simp only [D] at hterm
  rw [Finset.sum_congr rfl fun a _ ↦ hterm a]
  have hsumm : ∀ a ∈ (Finset.univ : Finset (Fin L)), Summable fun pq : ℤ × ℤ ↦
      K * (ω (a : ZMod L) * cexp (2 * π * I * a * (-pq.1) / L)) * D pq := by
    intro a _
    refine Summable.of_norm_bounded (hD.norm.mul_left (‖K‖ * 1)) fun pq ↦ ?_
    rw [norm_mul, norm_mul, norm_mul]
    have h1 : ‖ω (a : ZMod L)‖ ≤ 1 := DirichletCharacter.norm_le_one ω _
    have h2 : ‖cexp (2 * π * I * a * (-pq.1) / L)‖ = 1 := by
      rw [Complex.norm_exp]; simp [Complex.div_re]
    rw [norm_mul (ω (a : ZMod L)), h2, mul_one]
    gcongr
  rw [← Summable.tsum_finsetSum hsumm]
  unfold dualTheta
  rw [← tsum_mul_left]
  refine tsum_congr fun pq ↦ ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hgauss : ∑ a : Fin L, ω (a : ZMod L) * cexp (2 * π * I * a * (-pq.1) / L) = gaussAt L ω (-pq.1) := by
    unfold gaussAt
    rw [← Fin.sum_univ_eq_sum_range (fun a ↦ ω a * cexp (2 * π * I * a * (-pq.1 : ℤ) / L))]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    push_cast; ring_nf
  rw [hgauss]
  simp only [K]
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hy0 : (z.im : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hL0' : (L : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
  simp only [D, Complex.ofReal_exp]
  push_cast
  have hI : (-I / u) ^ lam * (I / ((L : ℂ) * z.im)) ^ lam = (((L : ℂ) * z.im) ^ lam)⁻¹ * ((u : ℂ) ^ lam)⁻¹ := by
    rw [← mul_pow, ← inv_pow, ← inv_pow, ← mul_pow]
    congr 1
    field_simp
    rw [I_sq]; ring
  linear_combination (gaussAt L ω (-pq.1) * ((pq.1 : ℂ) * z + pq.2) ^ lam *
    cexp (-π * (1 / ((L : ℂ) ^ 2 * (z.im : ℂ) ^ 2 * u)) * ((‖(pq.1 : ℂ) * z + pq.2‖ : ℝ) : ℂ) ^ 2) *
    ((L : ℂ) ^ 2 * z.im)⁻¹ * (u : ℂ)⁻¹) * hI

end Inversion

/-- **Hecke's functional equation, unconditional** (Hecke 1927 `hecke1927`; Miyake 1989 `miyake1989`, §7.2): the
named input `EisensteinFE` holds. -/
@[kb "hecke1927" "functional equation of the lattice Eisenstein series with a character, proved by Poisson summation [unverified]"]
theorem eisensteinFE : EisensteinFE :=
  eisensteinFE_of_latticeThetaInversion Inversion.latticeThetaInversion

end ModularFormsKB.Miyake.HeckeTrick
