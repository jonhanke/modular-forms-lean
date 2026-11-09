import ModularFormsKB.Milne.Ch12.CMDefs
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange
import ModularFormsKB.Citation
/-!
# Milne, Section 12: base change of complex multiplication

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, pdf p. 124.
These are steps in Milne's proof of Theorem 12.8: "if $E$ has CM by $R$, so does $\sigma E$ for
$\sigma \in \mathrm{Aut}(\mathbb C)$, and $j(\sigma E) = \sigma j(E)$".

**D127** ($E^\sigma$, the curve with $\sigma$ applied to the coefficients) is Mathlib's `WeierstrassCurve.map`, and
$j(E^\sigma) = \sigma j(E)$ is Mathlib's `WeierstrassCurve.map_j`.

* `homMapRingEquiv`: base change along a field isomorphism is an isomorphism of endomorphism rings;
* `hasCMBy_map`, `hasComplexMultiplication_map`: CM is preserved;
* `j_map_mem_ellCM`: $\mathrm{Ell}(R)$ is stable under $\mathrm{Aut}(\mathbb C)$.
-/

open NumberField TauCeti TauCeti.Isogeny TauCeti.GlobalNumberFields
open scoped WeierstrassCurve

namespace ModularFormsKB.Milne

/-- Surjectivity of base change along a field isomorphism. -/
theorem hom_map_surjective {k k' : Type*} [Field k] [Field k'] (σ : k ≃+* k')
    (W : WeierstrassCurve k) (g : Hom (W.map (σ : k →+* k')).toAffine (W.map (σ : k →+* k')).toAffine) :
    ∃ h : Hom W.toAffine W.toAffine, h.map (σ : k →+* k') = g := by
  have e : (W.map (σ : k →+* k')).map (σ.symm : k' →+* k) = W := by
    rw [WeierstrassCurve.map_map]
    have : (σ.symm : k' →+* k).comp (σ : k →+* k') = RingHom.id k := by ext; simp
    rw [this, WeierstrassCurve.map_id]
  have key : ∀ (V : WeierstrassCurve k) (_ : V = W) (h0 : Hom V.toAffine V.toAffine),
      HEq (h0.map (σ : k →+* k')) g → ∃ h : Hom W.toAffine W.toAffine, h.map (σ : k →+* k') = g := by
    intro V hV h0 hh
    subst hV
    exact ⟨h0, eq_of_heq hh⟩
  refine key _ e (g.map (σ.symm : k' →+* k)) ?_
  have c : (σ : k →+* k').comp (σ.symm : k' →+* k) = RingHom.id k' := by ext; simp
  refine (heq_of_eq (Hom.map_map g _ _)).trans ?_
  exact (congr_arg_heq (fun f => g.map f) c).trans (heq_of_eq (Hom.map_id g))

/-- Base change along a field isomorphism is a ring isomorphism of endomorphism rings. -/
noncomputable def homMapRingEquiv {k k' : Type*} [Field k] [Field k'] (σ : k ≃+* k')
    (W : WeierstrassCurve k) [W.IsElliptic] :
    Hom W.toAffine W.toAffine ≃+*
      Hom (W.map (σ : k →+* k')).toAffine (W.map (σ : k →+* k')).toAffine :=
  RingEquiv.ofBijective (Hom.mapRingHom (W₁ := W.toAffine) (σ : k →+* k'))
    ⟨Hom.map_injective _, fun g => hom_map_surjective σ W g⟩

/-- Complex multiplication by `O` is preserved by base change along a field isomorphism. -/
@[kb "milne2017mf" "Section 12, proof of Thm. 12.8 (pdf p. 124)"]
theorem hasCMBy_map {k k' : Type*} [Field k] [Field k'] (σ : k ≃+* k') (W : WeierstrassCurve k)
    [W.IsElliptic] {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K}
    (h : HasCMBy W O) : HasCMBy (W.map (σ : k →+* k')) O := by
  obtain ⟨h1, h2, ⟨e⟩⟩ := h
  exact ⟨h1, h2, ⟨e.trans (homMapRingEquiv σ W)⟩⟩

/-- Having complex multiplication is preserved by base change along a field isomorphism. -/
theorem hasComplexMultiplication_map {k k' : Type*} [Field k] [Field k'] (σ : k ≃+* k')
    (W : WeierstrassCurve k) [W.IsElliptic] (h : HasComplexMultiplication W) :
    HasComplexMultiplication (W.map (σ : k →+* k')) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨homMapRingEquiv σ W f, fun n hn => hf n ?_⟩
  apply (homMapRingEquiv σ W).injective
  rw [hn, map_zsmul, map_one]

/-- $\mathrm{Ell}(O)$ is stable under $\mathrm{Aut}(\mathbb C)$. -/
@[kb "milne2017mf" "Section 12, proof of Thm. 12.8 (pdf p. 124)"]
theorem j_map_mem_ellCM (σ : ℂ ≃+* ℂ) {K : Type*} [Field K] [NumberField K]
    {O : NumberFieldOrder K} {x : ℂ} (hx : x ∈ EllCM O) : σ x ∈ EllCM O := by
  obtain ⟨W, hW, hcm, rfl⟩ := hx
  exact ⟨W.map (σ : ℂ →+* ℂ), inferInstance, hasCMBy_map σ W hcm, WeierstrassCurve.map_j W _⟩

end ModularFormsKB.Milne
