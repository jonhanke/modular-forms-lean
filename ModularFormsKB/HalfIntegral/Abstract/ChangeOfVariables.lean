/-
# Change of variables over $\Gamma_0(L)\backslash\mathbb H$ under the normalizer of $\Gamma_0(L)$

First step of LE-MF-0256.

For a $\Gamma_0(L)$-invariant function $h$ on $\mathbb H$ the integral over $\Gamma_0(L)\backslash\mathbb H$ is computed
through a list $R$ of right coset representatives, $\int_{\Gamma_0(L)\backslash\mathbb H}h\,d\mu =
\sum_{\gamma\in R}\int_{\mathcal F}h(\gamma\tau)\,d\mu(\tau)$ (`repsIntegral`, `Abstract/ShimuraRankin.lean`), with
$\mathcal F$ = `ModularGroup.fd` and $d\mu = dx\,dy/y^2$. This file proves, with no weight and no multiplier:

* `repsIntegral_eq_of_reps`: the sum does not depend on $R$;
* `isFundamentalDomain_gamma0Domain`, `repsIntegral_eq_setIntegral`: it is the integral of $h$ over the fundamental
  domain $D_L = \bigcup_{q}(q^{\mathrm{out}})^{-1}\mathcal F^\circ$ of $\Gamma_0(L)$ (Tau Ceti
  `ModularGroup.isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter`), given integrability on $D_L$;
  `integrableOn_gamma0Domain` gives that integrability from the integrability of each term of the sum;
* `repsIntegral_comp_smul`: **the change of variables** $\int_{\Gamma_0(L)\backslash\mathbb H}h(\alpha\tau)\,d\mu =
  \int_{\Gamma_0(L)\backslash\mathbb H}h\,d\mu$ for every $\alpha \in \mathrm{GL}_2(\mathbb R)$ normalizing $\Gamma_0(L)$:
  $\alpha D_L$ is again a fundamental domain (Tau Ceti `ModularGroup.isFundamentalDomain_smul_of_inv_conjAct_eq`), the
  measure is $\mathrm{GL}_2(\mathbb R)$-invariant (Mathlib), and the integrals of an invariant function over two
  fundamental domains agree (Mathlib `IsFundamentalDomain.setIntegral_eq`);
* `gamma0_map_inv_conjAct_frickeGL_eq`, `repsIntegral_comp_fricke`: the Fricke matrix
  $W_L = \begin{psmallmatrix}0&-1\\L&0\end{psmallmatrix}$ (Tau Ceti `frickeGL`) normalizes $\Gamma_0(L)$, so the
  case $\alpha = W_L$, $\tau \mapsto -1/(L\tau)$, needed by the dual unfolding (LE-MF-0256).

The weighted form used by Tau Ceti for Atkin–Lehner adjointness (`peterssonInnerCosets_atkinLehnerOperatorCusp`) is the
special case $h = \overline{f}\,g\,v^{k}$; here $h$ is arbitrary, so the same statement serves half-integral weight.
-/
import ModularFormsKB.HalfIntegral.Rankin.Unfolding
import TauCeti.NumberTheory.Modular
import TauCeti.NumberTheory.ModularForms.Fricke.Conjugation
import TauCeti.NumberTheory.ModularForms.Fricke.Operator

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup MeasureTheory Set ModularGroup Matrix.SpecialLinearGroup
open scoped Real Pointwise

local notation "ℍ" => UpperHalfPlane

namespace ChangeOfVariables

/-- **The coset fundamental domain of $\Gamma_0(L)$**: $D_L = \bigcup_{q \in \mathrm{SL}_2(\mathbb Z)/\Gamma_0(L)}
(q^{\mathrm{out}})^{-1}\mathcal F^\circ$, with $\mathcal F^\circ$ = `ModularGroup.fdo` (the quotient is by
$\pm\Gamma_0(L)$, `withCenter`). -/
noncomputable def gamma0Domain (L : ℕ) : Set ℍ :=
  ⋃ q : SL(2, ℤ) ⧸ (Gamma0 L).withCenter, (q.out)⁻¹ • (ModularGroup.fdo : Set ℍ)

lemma integral_GL_smul (α : GL (Fin 2) ℝ) (S : Set ℍ) (h : ℍ → ℂ) :
    ∫ z in α • S, h z = ∫ z in S, h (α • z) := by
  rw [← Set.image_smul]
  exact (measurePreserving_smul α volume).setIntegral_image_emb (measurableEmbedding_const_smul α) _ _

lemma integrableOn_GL_smul (α : GL (Fin 2) ℝ) (S : Set ℍ) (h : ℍ → ℂ) :
    IntegrableOn h (α • S) ↔ IntegrableOn (fun z ↦ h (α • z)) S := by
  rw [← Set.image_smul]
  exact (measurePreserving_smul α volume).integrableOn_image (measurableEmbedding_const_smul α)

lemma exists_idx {L : ℕ} {R : List SL(2, ℤ)} (hR : IsGamma0Reps L R)
    (q : SL(2, ℤ) ⧸ (Gamma0 L).withCenter) :
    ∃ i : Fin R.length, R[i.1] * q.out ∈ Gamma0 L := by
  obtain ⟨i, hi, -⟩ := hR (q.out)⁻¹
  refine ⟨i, ?_⟩
  have := Subgroup.inv_mem _ hi
  simpa [mul_inv_rev] using this

lemma eq_of_idx {L : ℕ} {R : List SL(2, ℤ)} {h : ℍ → ℂ}
    (hh : ∀ γ ∈ Gamma0 L, ∀ z : ℍ, h (γ • z) = h z) (q : SL(2, ℤ) ⧸ (Gamma0 L).withCenter)
    (i : Fin R.length) (hi : R[i.1] * q.out ∈ Gamma0 L) (τ : ℍ) :
    h ((q.out)⁻¹ • τ) = h (R[i.1] • τ) := by
  have : (q.out)⁻¹ = (R[i.1] * q.out)⁻¹ * R[i.1] := by group
  rw [this, mul_smul, hh _ (Subgroup.inv_mem _ hi)]

lemma integrableOn_piece {L : ℕ} {R : List SL(2, ℤ)} (hR : IsGamma0Reps L R) {h : ℍ → ℂ}
    (hh : ∀ γ ∈ Gamma0 L, ∀ z : ℍ, h (γ • z) = h z)
    (hint : ∀ γ ∈ R, IntegrableOn (fun τ ↦ h (γ • τ)) ModularGroup.fd)
    (q : SL(2, ℤ) ⧸ (Gamma0 L).withCenter) :
    IntegrableOn h ((q.out)⁻¹ • (ModularGroup.fdo : Set ℍ)) := by
  obtain ⟨i, hi⟩ := exists_idx hR q
  have h1 : IntegrableOn (fun τ ↦ h (((q.out)⁻¹ : SL(2, ℤ)) • τ)) (ModularGroup.fdo : Set ℍ) := by
    have := (hint R[i.1] (List.getElem_mem _)).mono_set ModularGroup.fdo_subset_fd
    simpa only [eq_of_idx hh q i hi] using this
  rw [ModularGroup.sl_smul_set, integrableOn_GL_smul]
  exact h1

lemma hinvG {L : ℕ} {h : ℍ → ℂ} (hh : ∀ γ ∈ Gamma0 L, ∀ z : ℍ, h (γ • z) = h z)
    (g : ↥((Gamma0 L).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))))) (x : ℍ) :
    h (g • x) = h x := by
  obtain ⟨γ, hγ, hp⟩ := Subgroup.mem_map.1 g.2
  have : g • x = (γ : SL(2, ℤ)) • x := by
    rw [Subgroup.smul_def]
    have hp' : (g : PSL(2, ℤ)) = (γ : PSL(2, ℤ)) := hp.symm
    rw [hp']
    exact UpperHalfPlane.pslMk_smul γ x
  rw [this]; exact hh γ hγ x

/-- $D_L$ is a fundamental domain for the image of $\Gamma_0(L)$ in $\mathrm{PSL}_2(\mathbb Z)$. -/
theorem isFundamentalDomain_gamma0Domain (L : ℕ) :
    IsFundamentalDomain ((Gamma0 L).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) (gamma0Domain L) volume :=
  ModularGroup.isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter _

/-- **The integral over $\Gamma_0(L)\backslash\mathbb H$ does not depend on the representatives.** -/
theorem repsIntegral_eq_of_reps {L : ℕ} [NeZero L] {R R' : List SL(2, ℤ)} (hR : IsGamma0Reps L R)
    (hR' : IsGamma0Reps L R') (h : ℍ → ℂ) (hh : ∀ γ ∈ Gamma0 L, ∀ z : ℍ, h (γ • z) = h z) :
    repsIntegral R h = repsIntegral R' h := by
  rw [RankinUnfold.repsIntegral_eq_sum_quotient hR h hh, RankinUnfold.repsIntegral_eq_sum_quotient hR' h hh]

/-- **Integrability on $D_L$** from the integrability on $\mathcal F$ of every term $h(\gamma\,\cdot)$, $\gamma \in R$. -/
theorem integrableOn_gamma0Domain {L : ℕ} [NeZero L] {R : List SL(2, ℤ)} (hR : IsGamma0Reps L R) {h : ℍ → ℂ}
    (hh : ∀ γ ∈ Gamma0 L, ∀ z : ℍ, h (γ • z) = h z)
    (hint : ∀ γ ∈ R, IntegrableOn (fun τ ↦ h (γ • τ)) ModularGroup.fd) :
    IntegrableOn h (gamma0Domain L) :=
  integrableOn_finite_iUnion.mpr (integrableOn_piece hR hh hint)

/-- **The coset sum is the integral over the fundamental domain** $D_L$, for $h$ invariant and integrable on $D_L$. -/
theorem repsIntegral_eq_setIntegral {L : ℕ} [NeZero L] {R : List SL(2, ℤ)} (hR : IsGamma0Reps L R) (h : ℍ → ℂ)
    (hh : ∀ γ ∈ Gamma0 L, ∀ z : ℍ, h (γ • z) = h z) (hint : IntegrableOn h (gamma0Domain L)) :
    repsIntegral R h = ∫ z in gamma0Domain L, h z := by
  rw [RankinUnfold.repsIntegral_eq_sum_quotient hR h hh, gamma0Domain,
    integral_iUnion_fintype (fun q ↦ (ModularGroup.isOpen_smul_fdo _).measurableSet)
      (ModularGroup.pairwise_disjoint_smul_fdo_out_withCenter (Gamma0 L))
      (fun q ↦ hint.mono_set (Set.subset_iUnion (fun q : SL(2, ℤ) ⧸ (Gamma0 L).withCenter ↦
        (q.out)⁻¹ • (ModularGroup.fdo : Set ℍ)) q))]

/-- **Change of variables under the normalizer of $\Gamma_0(L)$:** for $\alpha \in \mathrm{GL}_2(\mathbb R)$ with
$\alpha^{-1}\Gamma_0(L)\alpha = \Gamma_0(L)$ and $h$ $\Gamma_0(L)$-invariant and integrable on $D_L$,
$\sum_{\gamma\in R}\int_{\mathcal F}h(\alpha\gamma\tau)\,d\mu = \sum_{\gamma\in R}\int_{\mathcal F}h(\gamma\tau)\,d\mu$. -/
theorem repsIntegral_comp_smul {L : ℕ} [NeZero L] {R : List SL(2, ℤ)} (hR : IsGamma0Reps L R)
    {α : GL (Fin 2) ℝ}
    (hα : ConjAct.toConjAct α⁻¹ • (Gamma0 L).map (mapGL ℝ) = (Gamma0 L).map (mapGL ℝ))
    (h : ℍ → ℂ) (hh : ∀ γ ∈ Gamma0 L, ∀ z : ℍ, h (γ • z) = h z) (hint : IntegrableOn h (gamma0Domain L)) :
    repsIntegral R (fun z ↦ h (α • z)) = repsIntegral R h := by
  have hnorm : ∀ x ∈ (Gamma0 L).map (mapGL ℝ), α * x * α⁻¹ ∈ (Gamma0 L).map (mapGL ℝ) := by
    intro x hx
    rw [← hα] at hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    simpa [ConjAct.smul_def] using hx
  have hh' : ∀ γ ∈ Gamma0 L, ∀ z : ℍ, (fun z ↦ h (α • z)) (γ • z) = (fun z ↦ h (α • z)) z := by
    intro γ hγ z
    obtain ⟨γ', hγ', he⟩ := Subgroup.mem_map.1 (hnorm _ ⟨γ, hγ, rfl⟩)
    have : α • (γ • z) = γ' • (α • z) := by
      have h2 : α * mapGL ℝ γ = mapGL ℝ γ' * α := by rw [he]; group
      calc α • (γ • z) = (α * mapGL ℝ γ) • z := by rw [mul_smul]; rfl
        _ = (mapGL ℝ γ' * α) • z := by rw [h2]
        _ = γ' • (α • z) := by rw [mul_smul]; rfl
    simp only [this]
    exact hh γ' hγ' _
  have hD := isFundamentalDomain_gamma0Domain L
  have hαD := ModularGroup.isFundamentalDomain_smul_of_inv_conjAct_eq hα hD
  have hint' : IntegrableOn (fun z ↦ h (α • z)) (gamma0Domain L) := by
    rw [← integrableOn_GL_smul]
    exact (hD.integrableOn_iff hαD (hinvG hh)).1 hint
  rw [repsIntegral_eq_setIntegral hR _ hh' hint', repsIntegral_eq_setIntegral hR h hh hint,
    ← integral_GL_smul]
  exact hαD.setIntegral_eq hD (hinvG hh)

/-- **The Fricke matrix $W_L$ normalizes $\Gamma_0(L)$** in $\mathrm{GL}_2(\mathbb R)$ (the $\Gamma_0$ analogue of Tau Ceti
`Gamma1_map_inv_conjAct_frickeGL_eq`). -/
theorem gamma0_map_inv_conjAct_frickeGL_eq (L : ℕ) [NeZero L] :
    ConjAct.toConjAct (TauCeti.frickeGL ℝ L)⁻¹ • (Gamma0 L).map (mapGL ℝ) = (Gamma0 L).map (mapGL ℝ) := by
  ext y
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    ConjAct.ofConjAct_toConjAct, map_inv, inv_inv, Subgroup.mem_map]
  constructor
  · rintro ⟨τ, hτ, hτy⟩
    refine ⟨TauCeti.frickeConjSL ⟨τ, hτ⟩, TauCeti.frickeConjSL_mem_Gamma0 _, ?_⟩
    have h : mapGL ℝ τ * TauCeti.frickeGL ℝ L
        = TauCeti.frickeGL ℝ L * mapGL ℝ (TauCeti.frickeConjSL ⟨τ, hτ⟩) :=
      TauCeti.mapGL_mul_frickeGL ℝ ⟨τ, hτ⟩
    rw [hτy] at h
    refine (mul_left_cancel (a := TauCeti.frickeGL ℝ L) ?_).symm
    rw [← h]
    group
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨TauCeti.frickeConjSL ⟨σ, hσ⟩, TauCeti.frickeConjSL_mem_Gamma0 _, ?_⟩
    have h : TauCeti.frickeGL ℝ L * mapGL ℝ σ
        = mapGL ℝ (TauCeti.frickeConjSL ⟨σ, hσ⟩) * TauCeti.frickeGL ℝ L :=
      TauCeti.frickeGL_mul_mapGL ℝ ⟨σ, hσ⟩
    rw [h]
    group

/-- **The Fricke change of variables** $\tau \mapsto W_L\tau = -1/(L\tau)$ over $\Gamma_0(L)\backslash\mathbb H$. -/
theorem repsIntegral_comp_fricke {L : ℕ} [NeZero L] {R : List SL(2, ℤ)} (hR : IsGamma0Reps L R) (h : ℍ → ℂ)
    (hh : ∀ γ ∈ Gamma0 L, ∀ z : ℍ, h (γ • z) = h z) (hint : IntegrableOn h (gamma0Domain L)) :
    repsIntegral R (fun z ↦ h (TauCeti.frickeGL ℝ L • z)) = repsIntegral R h :=
  repsIntegral_comp_smul hR (gamma0_map_inv_conjAct_frickeGL_eq L) h hh hint

end ChangeOfVariables

end ModularFormsKB.HalfIntegral
