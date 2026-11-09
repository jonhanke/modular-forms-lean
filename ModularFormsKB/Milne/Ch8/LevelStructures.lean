import ModularFormsKB.Milne.Ch8.Lattices
import ModularFormsKB.Miyake.CongruenceModularGroups

/-!
# Milne, Chapter 8: $\Gamma(N)\backslash\mathbb H$ classifies lattices with a level-$N$ structure (Lemma 8.7)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 8, pdf p. 100.

Lattice form, as in `ModularFormsKB.Milne.Ch8.Lattices`. The Weil pairing on $\frac1N\Lambda/\Lambda$ is
$e_N(t_1, t_2) = \exp(2\pi i N \operatorname{Im}(t_1\bar t_2)/A)$, $A$ the covolume of $\Lambda$ (`weilPairing`;
$e_N(\omega_1/N, \omega_2/N) = e^{2\pi i/N}$ for a basis with $\operatorname{Im}(\omega_1/\omega_2) > 0$; this is one
of the two usual sign conventions, the one making Milne's Lemma 8.7 hold with $\zeta = e^{2\pi i/N}$).

- **Lemma 8.7**: `lemma_8_7_injective` and `lemma_8_7_surjective`.
-/

open Complex CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Real
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne

/-- The covolume $|\operatorname{Im}(\omega_1\bar\omega_2)|$ of the lattice of a period pair. -/
def covolume (P : PeriodPair) : ℝ :=
  |(P.ω₁ * (starRingEnd ℂ) P.ω₂).im|

/-- **The Weil pairing** on $\frac1N\Lambda/\Lambda$ for $\Lambda = $ `P.lattice`:
$e_N(t_1, t_2) = \exp(2\pi i N\operatorname{Im}(t_1 \bar t_2)/A)$. -/
def weilPairing (N : ℕ) (P : PeriodPair) (t₁ t₂ : ℂ) : ℂ :=
  cexp (2 * π * I * N * (t₁ * (starRingEnd ℂ) t₂).im / covolume P)

/-- A **level-$N$ structure** on $\mathbb C/\Lambda$ (Milne, Section 8, pdf p. 100): $t_1, t_2 \in \frac1N\Lambda$
whose classes form a basis of $\frac1N\Lambda/\Lambda \cong (\mathbb Z/N\mathbb Z)^2$, i.e. $\frac1N\Lambda$ is
spanned by $\Lambda$, $t_1$, $t_2$. -/
def IsLevelStructure (N : ℕ) (Λ : Submodule ℤ ℂ) (t₁ t₂ : ℂ) : Prop :=
  (N : ℂ) * t₁ ∈ Λ ∧ (N : ℂ) * t₂ ∈ Λ ∧
    Λ ⊔ Submodule.span ℤ {t₁, t₂} = homothety ((N : ℂ)⁻¹) Λ

/-! ### Helper lemmas -/

lemma lvl_mem_complexLatticeSpan_iff {u v x : ℂ} :
    x ∈ complexLatticeSpan u v ↔ ∃ m n : ℤ, (m : ℂ) * u + n * v = x := by
  simp only [complexLatticeSpan, Submodule.mem_span_pair, zsmul_eq_mul]

lemma lvl_homothety_complexLatticeSpan (c u v : ℂ) :
    homothety c (complexLatticeSpan u v) = complexLatticeSpan (c * u) (c * v) := by
  unfold homothety complexLatticeSpan
  rw [Submodule.map_span, Set.image_pair]
  rfl

lemma lvl_complexLatticeSpan_eq_of_det {u v u' v' : ℂ} (a b c d : ℤ) (hdet : a * d - b * c = 1)
    (hu : u' = a * u + b * v) (hv : v' = c * u + d * v) :
    complexLatticeSpan u' v' = complexLatticeSpan u v := by
  have hdet' : (a : ℂ) * d - b * c = 1 := by exact_mod_cast hdet
  apply le_antisymm
  · unfold complexLatticeSpan
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact lvl_mem_complexLatticeSpan_iff.2 ⟨a, b, hu.symm⟩
    · exact lvl_mem_complexLatticeSpan_iff.2 ⟨c, d, hv.symm⟩
  · unfold complexLatticeSpan
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact lvl_mem_complexLatticeSpan_iff.2 ⟨d, -b, by rw [hu, hv]; push_cast; linear_combination x * hdet'⟩
    · exact lvl_mem_complexLatticeSpan_iff.2 ⟨-c, a, by rw [hu, hv]; push_cast; linear_combination x * hdet'⟩

lemma lvl_int_ind {w : ℂ} (hw : w.im ≠ 0) {x y x' y' : ℤ}
    (h : (x : ℂ) * w + y = x' * w + y') : x = x' ∧ y = y' := by
  have him : (x : ℝ) * w.im = x' * w.im := by
    have := congrArg Complex.im h
    simpa using this
  have hx : x = x' := by
    have := mul_right_cancel₀ hw him
    exact_mod_cast this
  subst hx
  refine ⟨rfl, ?_⟩
  have := add_left_cancel h
  exact_mod_cast this

lemma lvl_dvd_of_div_mem {N : ℕ} (hN : 0 < N) {w : ℂ} (hw : w.im ≠ 0) (m n : ℤ)
    (h : ((m : ℂ) * w + n) / N ∈ complexLatticeSpan w 1) : (N : ℤ) ∣ m ∧ (N : ℤ) ∣ n := by
  obtain ⟨x, y, hxy⟩ := lvl_mem_complexLatticeSpan_iff.1 h
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2 : ((N * x : ℤ) : ℂ) * w + ((N * y : ℤ) : ℂ) = (m : ℂ) * w + n := by
    push_cast
    have : (m : ℂ) * w + n = N * (x * w + y * 1) := by rw [hxy]; field_simp
    rw [this]; ring
  obtain ⟨h3, h4⟩ := lvl_int_ind hw h2
  exact ⟨⟨x, h3.symm⟩, ⟨y, h4.symm⟩⟩

lemma lvl_zmod_one_of_dvd {N : ℕ} {x : ℤ} (h : (N : ℤ) ∣ x - 1) : (x : ZMod N) = 1 := by
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - 1) N).2 h
  push_cast at this
  exact sub_eq_zero.1 this

lemma lvl_zmod_zero_of_dvd {N : ℕ} {x : ℤ} (h : (N : ℤ) ∣ x) : (x : ZMod N) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd x N).2 h

lemma lvl_zmod_dvd_one {N : ℕ} {x : ℤ} (h : (x : ZMod N) = 1) : ∃ k : ℤ, x - 1 = N * k := by
  have : ((x - 1 : ℤ) : ZMod N) = 0 := by push_cast; rw [h]; ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 this

lemma lvl_zmod_dvd_zero {N : ℕ} {x : ℤ} (h : (x : ZMod N) = 0) : ∃ k : ℤ, x = N * k :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd x N).1 h

lemma lvl_weil_exp(N : ℕ) (hN : 0 < N) (ω₁ ω₂ t₁ t₂ : ℂ) (a b c d : ℤ)
    (h1 : (N : ℂ) * t₁ = a * ω₁ + b * ω₂) (h2 : (N : ℂ) * t₂ = c * ω₁ + d * ω₂) :
    (N : ℝ) * (t₁ * (starRingEnd ℂ) t₂).im =
      (a * d - b * c : ℤ) * (ω₁ * (starRingEnd ℂ) ω₂).im / N := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have key : ((N : ℂ) * t₁) * (starRingEnd ℂ) ((N : ℂ) * t₂) =
      (((N : ℝ) ^ 2 : ℝ) : ℂ) * (t₁ * (starRingEnd ℂ) t₂) := by
    simp only [map_mul, Complex.conj_natCast]; push_cast; ring
  have := congrArg Complex.im key
  rw [Complex.im_ofReal_mul, h1, h2] at this
  field_simp
  simp only [map_add, map_mul, map_intCast,Complex.add_im, Complex.mul_im,
    Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im] at this ⊢
  push_cast
  nlinarith [this]

lemma lvl_surj_core {N : ℕ} (hN : 0 < N) (ω₁ ω₂ : ℂ) (hs : 0 < (ω₁ * (starRingEnd ℂ) ω₂).im)
    (t₁ t₂ : ℂ) (a b c d a' b' c' d' : ℤ)
    (h1 : (N : ℂ) * t₁ = a * ω₁ + b * ω₂) (h2 : (N : ℂ) * t₂ = c * ω₁ + d * ω₂)
    (hdet : a' * d' - b' * c' = 1)
    (ka kb kc kd : ℤ) (hka : a' - a = N * ka) (hkb : b' - b = N * kb)
    (hkc : c' - c = N * kc) (hkd : d' - d = N * kd) :
    ∃ (z : ℍ) (c0 : ℂ), c0 ≠ 0 ∧ homothety c0 (complexLatticeSpan ω₁ ω₂) = complexLatticeSpan z 1 ∧
      c0 * t₁ - z / N ∈ complexLatticeSpan z 1 ∧ c0 * t₂ - 1 / N ∈ complexLatticeSpan z 1 := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hdet' : (a' : ℂ) * d' - b' * c' = 1 := by exact_mod_cast hdet
  set ω₁' : ℂ := a' * ω₁ + b' * ω₂ with hω₁'
  set ω₂' : ℂ := c' * ω₁ + d' * ω₂ with hω₂'
  have him : (ω₁' * (starRingEnd ℂ) ω₂').im = (ω₁ * (starRingEnd ℂ) ω₂).im := by
    have : (ω₁' * (starRingEnd ℂ) ω₂').im = ((a' * d' - b' * c' : ℤ) : ℝ) *
        (ω₁ * (starRingEnd ℂ) ω₂).im := by
      simp only [hω₁', hω₂', map_add, map_mul, map_intCast, Complex.add_im, Complex.mul_im,
        Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
        Complex.conj_im]
      push_cast
      ring
    rw [this, hdet]; simp
  have hω₂ne : ω₂' ≠ 0 := by
    intro h0
    have h00 : (ω₁' * (starRingEnd ℂ) ω₂').im = 0 := by rw [h0]; simp
    linarith
  set c0 : ℂ := (ω₂')⁻¹ with hc0
  have hc0ne : c0 ≠ 0 := inv_ne_zero hω₂ne
  have hω0 : c0 * ω₂' = 1 := inv_mul_cancel₀ hω₂ne
  have hpos : 0 < (ω₁' * c0).im := by
    have e : ω₁' * c0 = (ω₁' * (starRingEnd ℂ) ω₂') * (((Complex.normSq ω₂')⁻¹ : ℝ) : ℂ) := by
      rw [hc0, Complex.inv_def]; ring
    rw [e, Complex.im_mul_ofReal, him]
    exact mul_pos hs (inv_pos.2 (Complex.normSq_pos.2 hω₂ne))
  let z : ℍ := ⟨ω₁' * c0, hpos⟩
  have hz : (z : ℂ) = ω₁' * c0 := rfl
  have hA : ω₁ = d' * ω₁' - b' * ω₂' := by
    rw [hω₁', hω₂']; linear_combination (-ω₁) * hdet'
  have hB : ω₂ = -c' * ω₁' + a' * ω₂' := by
    rw [hω₁', hω₂']; linear_combination (-ω₂) * hdet'
  have e1 : c0 * ω₁ = d' * z - b' := by
    rw [hz]; linear_combination c0 * hA - b' * hω0
  have e2 : c0 * ω₂ = -c' * z + a' := by
    rw [hz]; linear_combination c0 * hB + a' * hω0
  refine ⟨z, c0, hc0ne, ?_, ?_, ?_⟩
  · rw [lvl_homothety_complexLatticeSpan]
    refine (lvl_complexLatticeSpan_eq_of_det a' b' c' d' hdet ?_ ?_).symm
    · rw [hz, hω₁']; ring
    · rw [hω₂'] at hω0; linear_combination (-1 : ℂ) * hω0
  · have hka' : (a' : ℂ) = a + N * ka := by
      have : a' = a + N * ka := by linarith
      exact_mod_cast this
    have hkb' : (b' : ℂ) = b + N * kb := by
      have : b' = b + N * kb := by linarith
      exact_mod_cast this
    have hdiv : (N : ℂ) * (ω₁' / N) = ω₁' := by field_simp
    have ht1 : t₁ - ω₁' / N = -ka * ω₁ - kb * ω₂ := by
      apply mul_left_cancel₀ hN'
      linear_combination h1 - hdiv - hω₁' - ω₁ * hka' - ω₂ * hkb'
    refine lvl_mem_complexLatticeSpan_iff.2 ⟨-ka * d' + kb * c', ka * b' - kb * a', ?_⟩
    push_cast
    linear_combination (-c0) * ht1 + (ka : ℂ) * e1 + (kb : ℂ) * e2 + (1 / (N : ℂ)) * hz
  · have hkc' : (c' : ℂ) = c + N * kc := by
      have : c' = c + N * kc := by linarith
      exact_mod_cast this
    have hkd' : (d' : ℂ) = d + N * kd := by
      have : d' = d + N * kd := by linarith
      exact_mod_cast this
    have hdiv : (N : ℂ) * (ω₂' / N) = ω₂' := by field_simp
    have ht2 : t₂ - ω₂' / N = -kc * ω₁ - kd * ω₂ := by
      apply mul_left_cancel₀ hN'
      linear_combination h2 - hdiv - hω₂' - ω₁ * hkc' - ω₂ * hkd'
    refine lvl_mem_complexLatticeSpan_iff.2 ⟨-kc * d' + kd * c', kc * b' - kd * a', ?_⟩
    push_cast
    linear_combination (-c0) * ht2 + (kc : ℂ) * e1 + (kd : ℂ) * e2 - (1 / (N : ℂ)) * hω0

lemma lvl_surj_oriented {N : ℕ} (hN : 0 < N) (ω₁ ω₂ : ℂ) (hs : 0 < (ω₁ * (starRingEnd ℂ) ω₂).im)
    (t₁ t₂ : ℂ) (ht1 : (N : ℂ) * t₁ ∈ complexLatticeSpan ω₁ ω₂) (ht2 : (N : ℂ) * t₂ ∈ complexLatticeSpan ω₁ ω₂)
    (he : cexp (2 * π * I * N * (t₁ * (starRingEnd ℂ) t₂).im / (ω₁ * (starRingEnd ℂ) ω₂).im) =
      cexp (2 * π * I / N)) :
    ∃ (z : ℍ) (c0 : ℂ), c0 ≠ 0 ∧ homothety c0 (complexLatticeSpan ω₁ ω₂) = complexLatticeSpan z 1 ∧
      c0 * t₁ - z / N ∈ complexLatticeSpan z 1 ∧ c0 * t₂ - 1 / N ∈ complexLatticeSpan z 1 := by
  have : NeZero N := ⟨hN.ne'⟩
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨a, b, h1⟩ := lvl_mem_complexLatticeSpan_iff.1 ht1
  obtain ⟨c, d, h2⟩ := lvl_mem_complexLatticeSpan_iff.1 ht2
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  have hw := lvl_weil_exp N hN ω₁ ω₂ t₁ t₂ a b c d h1.symm h2.symm
  have hwc := congrArg (fun x : ℝ => (x : ℂ)) hw
  push_cast at hwc
  have hsc : (((ω₁ * (starRingEnd ℂ) ω₂).im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hexp : 2 * π * I * N * (t₁ * (starRingEnd ℂ) t₂).im / (ω₁ * (starRingEnd ℂ) ω₂).im =
      2 * π * I * ((a * d - b * c : ℤ) : ℂ) / N := by
    calc 2 * π * I * N * (t₁ * (starRingEnd ℂ) t₂).im / (ω₁ * (starRingEnd ℂ) ω₂).im
        = 2 * π * I * ((N : ℂ) * (t₁ * (starRingEnd ℂ) t₂).im) /
            (ω₁ * (starRingEnd ℂ) ω₂).im := by ring
      _ = 2 * π * I * (((a * d - b * c : ℤ) : ℂ) * (ω₁ * (starRingEnd ℂ) ω₂).im / N) /
            (ω₁ * (starRingEnd ℂ) ω₂).im := by rw [hwc]; push_cast; try ring
      _ = _ := by push_cast; field_simp
  rw [hexp] at hn
  have h2piI : (2 * π * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hint : ((a * d - b * c : ℤ) : ℂ) = 1 + n * N := by
    apply mul_left_cancel₀ h2piI
    field_simp at hn
    linear_combination (2 * π * I : ℂ) * hn
  have hint' : a * d - b * c = 1 + n * N := by exact_mod_cast hint
  have hdetmod : a * d - b * c ≡ 1 [ZMOD N] :=
    (Int.modEq_iff_dvd).2 ⟨-n, by linarith⟩
  let g : SL(2, ZMod N) := ⟨!![(a : ZMod N), b; c, d], by
    rw [Matrix.det_fin_two_of]
    have := (ZMod.intCast_eq_intCast_iff _ _ N).2 hdetmod
    push_cast at this
    exact this⟩
  obtain ⟨A, hA⟩ := ModularFormsKB.Miyake.SL2_reduction_surjective N g
  have e : ∀ i j : Fin 2, ((A i j : ℤ) : ZMod N) = (g : Matrix (Fin 2) (Fin 2) (ZMod N)) i j := by
    intro i j
    have := congrArg (fun M : SL(2, ZMod N) => (M : Matrix (Fin 2) (Fin 2) (ZMod N)) i j) hA
    simpa using this
  have hdet1 : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := A.det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  obtain ⟨ka, hka⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub a (A 0 0) N).1 (by simpa [g] using (e 0 0).symm)
  obtain ⟨kb, hkb⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub b (A 0 1) N).1 (by simpa [g] using (e 0 1).symm)
  obtain ⟨kc, hkc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub c (A 1 0) N).1 (by simpa [g] using (e 1 0).symm)
  obtain ⟨kd, hkd⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub d (A 1 1) N).1 (by simpa [g] using (e 1 1).symm)
  exact lvl_surj_core hN ω₁ ω₂ hs t₁ t₂ a b c d (A 0 0) (A 0 1) (A 1 0) (A 1 1) h1.symm h2.symm hdet1
    ka kb kc kd hka hkb hkc hkd

/-- **Milne, Lemma 8.7** (injectivity, lattice form): $z \mapsto (\mathbb C/(z, 1), (z/N, 1/N))$; the data attached to
$z, w \in \mathbb H$ are isomorphic (a homothety carrying the lattices and the points modulo the lattices to each other)
iff $w \in \Gamma(N) z$. -/
@[kb "milne2017mf" "Section 8, Lemma 8.7 (pdf p. 100), lattice form, injectivity"]
theorem lemma_8_7_injective {N : ℕ} (hN : 0 < N) (z w : ℍ) :
    (∃ c : ℂ, c ≠ 0 ∧ homothety c (complexLatticeSpan z 1) = complexLatticeSpan w 1 ∧
      c * (z / N) - w / N ∈ complexLatticeSpan w 1 ∧ c * (1 / N) - 1 / N ∈ complexLatticeSpan w 1) ↔
      ∃ γ ∈ Gamma N, γ • z = w := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  constructor
  · rintro ⟨c, hc, hom, hm1, hm2⟩
    have hzmem : (z : ℂ) ∈ complexLatticeSpan z 1 := Submodule.subset_span (by simp)
    have h1mem : (1 : ℂ) ∈ complexLatticeSpan z 1 := Submodule.subset_span (by simp)
    have hcz : c * z ∈ complexLatticeSpan w 1 := by
      rw [← hom]; exact Submodule.mem_map.2 ⟨z, hzmem, by simp⟩
    have hc1 : c ∈ complexLatticeSpan w 1 := by
      rw [← hom]; exact Submodule.mem_map.2 ⟨1, h1mem, by simp⟩
    have hwmem : (w : ℂ) ∈ complexLatticeSpan w 1 := Submodule.subset_span (by simp)
    have h1w : (1 : ℂ) ∈ complexLatticeSpan w 1 := Submodule.subset_span (by simp)
    rw [← hom] at hwmem h1w
    obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 hwmem
    obtain ⟨y', hy', hyw'⟩ := Submodule.mem_map.1 h1w
    obtain ⟨α, β, hαβ⟩ := lvl_mem_complexLatticeSpan_iff.1 hy
    obtain ⟨γ, δ, hγδ⟩ := lvl_mem_complexLatticeSpan_iff.1 hy'
    obtain ⟨p, q, hp⟩ := lvl_mem_complexLatticeSpan_iff.1 hcz
    obtain ⟨r, s, hr⟩ := lvl_mem_complexLatticeSpan_iff.1 hc1
    have hyw2 : c * y = w := hyw
    have hyw2' : c * y' = 1 := hyw'
    have wim : (w : ℂ).im ≠ 0 := w.im_ne_zero
    have e12 := lvl_int_ind wim (x := α * p + β * r) (y := α * q + β * s) (x' := 1) (y' := 0) (by
      push_cast
      rw [← hαβ] at hyw2
      linear_combination (α : ℂ) * hp + (β : ℂ) * hr + hyw2)
    have e34 := lvl_int_ind wim (x := γ * p + δ * r) (y := γ * q + δ * s) (x' := 0) (y' := 1) (by
      push_cast
      rw [← hγδ] at hyw2'
      linear_combination (γ : ℂ) * hp + (δ : ℂ) * hr + hyw2')
    have hprod : (α * δ - β * γ) * (p * s - q * r) = 1 := by
      calc (α * δ - β * γ) * (p * s - q * r)
          = (α * p + β * r) * (γ * q + δ * s) - (α * q + β * s) * (γ * p + δ * r) := by ring
        _ = 1 := by rw [e12.1, e12.2, e34.1, e34.2]; ring
    have hunit : p * s - q * r = 1 ∨ p * s - q * r = -1 :=
      Int.isUnit_iff.1 (IsUnit.of_mul_eq_one (α * δ - β * γ) (by rw [mul_comm]; exact hprod))
    have hcne : (c : ℂ) ≠ 0 := hc
    have hor : (0 : ℝ) < ((p * s - q * r : ℤ) : ℝ) := by
      have hh1 : (c * z * (starRingEnd ℂ) c).im = z.im * Complex.normSq c := by
        have : c * z * (starRingEnd ℂ) c = ((Complex.normSq c : ℝ) : ℂ) * z := by
          rw [← Complex.mul_conj]; ring
        rw [this, Complex.im_ofReal_mul, mul_comm]
        rfl
      have hh2 : (c * z * (starRingEnd ℂ) c).im = ((p * s - q * r : ℤ) : ℝ) * w.im := by
        have : c * z * (starRingEnd ℂ) c =
            ((p : ℂ) * w + q * 1) * (starRingEnd ℂ) ((r : ℂ) * w + s * 1) := by
          rw [hp, hr]
        rw [this]
        simp only [map_add, map_mul, map_intCast, map_one, Complex.add_im, Complex.mul_im,
          Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
          Complex.conj_im, Complex.one_re, Complex.one_im]
        push_cast
        have hwi : ((w : ℂ)).im = w.im := rfl
        rw [hwi]
        ring
      have hpos : 0 < (c * z * (starRingEnd ℂ) c).im := by
        rw [hh1]
        exact mul_pos z.im_pos (Complex.normSq_pos.2 hcne)
      rw [hh2] at hpos
      exact (mul_pos_iff_of_pos_right w.im_pos).1 hpos
    have hdet1 : p * s - q * r = 1 := by
      rcases hunit with h | h
      · exact h
      · rw [h] at hor; norm_num at hor
    let γ0 : SL(2, ℤ) := ⟨!![p, q; r, s], by rw [Matrix.det_fin_two_of]; exact hdet1⟩
    have hden : (r : ℂ) * w + s ≠ 0 := by
      have := hr
      rw [mul_one] at this
      rw [this]; exact hcne
    have hγ0 : γ0 • w = z := by
      ext
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      simp only [γ0]
      simp
      rw [div_eq_iff hden]
      linear_combination hp - (z : ℂ) * hr
    have hd1 : (N : ℤ) ∣ p - 1 ∧ (N : ℤ) ∣ q := by
      apply lvl_dvd_of_div_mem hN wim (p - 1) q
      have : (((p - 1 : ℤ) : ℂ) * w + q) / N = c * (z / N) - w / N := by
        push_cast
        field_simp
        linear_combination hp
      rw [this]; exact hm1
    have hd2 : (N : ℤ) ∣ r ∧ (N : ℤ) ∣ s - 1 := by
      have := lvl_dvd_of_div_mem hN wim r (s - 1) (by
        have : ((r : ℂ) * w + ((s - 1 : ℤ) : ℂ)) / N = c * (1 / N) - 1 / N := by
          push_cast
          field_simp
          linear_combination hr
        rw [this]; exact hm2)
      exact this
    have hmem : γ0 ∈ Gamma N :=
      Gamma_mem.2 ⟨lvl_zmod_one_of_dvd hd1.1, lvl_zmod_zero_of_dvd hd1.2, lvl_zmod_zero_of_dvd hd2.1,
        lvl_zmod_one_of_dvd hd2.2⟩
    exact ⟨γ0⁻¹, Subgroup.inv_mem _ hmem, inv_smul_eq_iff.2 hγ0.symm⟩
  · rintro ⟨γ, hγ, rfl⟩
    rw [Gamma_mem] at hγ
    obtain ⟨h00, h01, h10, h11⟩ := hγ
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.det_coe
      rw [Matrix.det_fin_two] at this
      exact this
    obtain ⟨a, b, c, d, hdet, ha, hb, hc, hd, hw⟩ : ∃ a b c d : ℤ, a * d - b * c = 1 ∧
        (a : ZMod N) = 1 ∧ (b : ZMod N) = 0 ∧ (c : ZMod N) = 0 ∧ (d : ZMod N) = 1 ∧
        (((γ • z : ℍ)) : ℂ) = (a * z + b) / (c * z + d) :=
      ⟨γ 0 0, γ 0 1, γ 1 0, γ 1 1, hdet, h00, h01, h10, h11, by
        rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp⟩
    generalize γ • z = w at hw ⊢
    have hdet' : (a : ℂ) * d - b * c = 1 := by exact_mod_cast hdet
    have hD : (c : ℂ) * z + d ≠ 0 := by
      intro h0
      have := lvl_int_ind z.im_ne_zero (x := c) (y := d) (x' := 0) (y' := 0) (by
        push_cast; simpa using h0)
      obtain ⟨rfl, rfl⟩ := this
      simp at hdet
    have hwD : (w : ℂ) * (c * z + d) = a * z + b := by
      rw [hw, div_mul_cancel₀ _ hD]
    have hz1 : 1 / ((c : ℂ) * z + d) * z = d * w - b := by
      rw [div_mul_eq_mul_div, one_mul, div_eq_iff hD]
      linear_combination (-(d : ℂ)) * hwD - (z : ℂ) * hdet'
    have hc1 : 1 / ((c : ℂ) * z + d) = -c * w + a := by
      rw [div_eq_iff hD]
      linear_combination (c : ℂ) * hwD - hdet'
    refine ⟨1 / ((c : ℂ) * z + d), one_div_ne_zero hD, ?_, ?_, ?_⟩
    · rw [lvl_homothety_complexLatticeSpan]
      refine (lvl_complexLatticeSpan_eq_of_det a b c d hdet ?_ ?_).symm
      · rw [mul_one, hz1, hc1]; linear_combination (-(w : ℂ)) * hdet'
      · rw [mul_one, hz1, hc1]; linear_combination (-1 : ℂ) * hdet'
    · obtain ⟨k1, hk1⟩ := lvl_zmod_dvd_one hd
      obtain ⟨k2, hk2⟩ := lvl_zmod_dvd_zero hb
      refine lvl_mem_complexLatticeSpan_iff.2 ⟨k1, -k2, ?_⟩
      have e1 : (d : ℂ) = 1 + N * k1 := by exact_mod_cast (by linarith : d = 1 + N * k1)
      have e2 : (b : ℂ) = N * k2 := by exact_mod_cast hk2
      have : 1 / ((c : ℂ) * z + d) * (z / N) = (1 / ((c : ℂ) * z + d) * z) / N := by ring
      rw [this, hz1, e1, e2]
      push_cast
      field_simp
      ring
    · obtain ⟨k3, hk3⟩ := lvl_zmod_dvd_zero hc
      obtain ⟨k4, hk4⟩ := lvl_zmod_dvd_one ha
      refine lvl_mem_complexLatticeSpan_iff.2 ⟨-k3, k4, ?_⟩
      have e1 : (a : ℂ) = 1 + N * k4 := by exact_mod_cast (by linarith : a = 1 + N * k4)
      have e2 : (c : ℂ) = N * k3 := by exact_mod_cast hk3
      rw [hc1, e1, e2]
      push_cast
      field_simp
      ring

/-- **Milne, Lemma 8.7** (surjectivity, lattice form): every lattice $\Lambda = $ `P.lattice` with a level-$N$ structure
$(t_1, t_2)$ of Weil pairing $e^{2\pi i/N}$ is isomorphic to $((z, 1), (z/N, 1/N))$ for some $z \in \mathbb H$. -/
@[kb "milne2017mf" "Section 8, Lemma 8.7 (pdf p. 100), lattice form, surjectivity"]
theorem lemma_8_7_surjective {N : ℕ} (hN : 0 < N) (P : PeriodPair) (t₁ t₂ : ℂ)
    (ht : IsLevelStructure N P.lattice t₁ t₂) (he : weilPairing N P t₁ t₂ = cexp (2 * π * I / N)) :
    ∃ (z : ℍ) (c : ℂ), c ≠ 0 ∧ homothety c P.lattice = complexLatticeSpan z 1 ∧
      c * t₁ - z / N ∈ complexLatticeSpan z 1 ∧ c * t₂ - 1 / N ∈ complexLatticeSpan z 1 := by
  obtain ⟨ht1, ht2, -⟩ := ht
  have hL : P.lattice = complexLatticeSpan P.ω₁ P.ω₂ := rfl
  rw [hL] at ht1 ht2 ⊢
  unfold weilPairing covolume at he
  have hs0 : (P.ω₁ * (starRingEnd ℂ) P.ω₂).im ≠ 0 := by
    intro h0
    have hi := LinearIndependent.pair_iff.1 P.indep
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0
    have e1 := hi (P.ω₂.im) (-P.ω₁.im) (by
      apply Complex.ext <;> simp <;> linarith)
    have h21 : P.ω₂.im = 0 := e1.1
    have h11 : P.ω₁.im = 0 := by linarith [e1.2]
    have e2 := hi (P.ω₂.re) (-P.ω₁.re) (by
      apply Complex.ext <;> simp [h21, h11]; ring)
    have e3 := hi 1 0 (by
      apply Complex.ext <;> simp [h11]; linarith [e2.2])
    exact one_ne_zero e3.1
  rcases lt_or_gt_of_ne hs0 with hneg | hpos
  · have hL' : complexLatticeSpan P.ω₁ P.ω₂ = complexLatticeSpan P.ω₂ P.ω₁ := by
      unfold complexLatticeSpan; rw [Set.pair_comm]
    have hneg' : (P.ω₂ * (starRingEnd ℂ) P.ω₁).im = -(P.ω₁ * (starRingEnd ℂ) P.ω₂).im := by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
    rw [hL'] at ht1 ht2 ⊢
    refine lvl_surj_oriented hN P.ω₂ P.ω₁ (by rw [hneg']; linarith) t₁ t₂ ht1 ht2 ?_
    rw [abs_of_neg hneg] at he
    rw [hneg']
    exact he
  · rw [abs_of_pos hpos] at he
    exact lvl_surj_oriented hN P.ω₁ P.ω₂ hpos t₁ t₂ ht1 ht2 he

end ModularFormsKB.Milne
