import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.RingTheory.AlgebraicIndependent.RankAndCardinality
import Mathlib.RingTheory.SimpleRing.Principal
import ModularFormsKB.Citation
/-!
# Milne, Section 12: a complex number with finitely many conjugates under Aut(C) is algebraic

Used in the proof of Theorem 12.8 (Milne, *Modular Functions and Modular Forms*, `milne2017mf`, pdf p. 124:
"j(E) has only finitely many conjugates under Aut(C), hence is algebraic").
-/

open Cardinal

namespace ModularFormsKB.Milne

/-- The automorphism of $\mathbb C$ extending a permutation `e` of a transcendence basis `v` over $\mathbb Z$
(`IsAlgClosed.equivOfTranscendenceBasis`) sends `v i` to `v (e i)`. -/
theorem equivOfTranscendenceBasis_apply_self {ι : Type} (v : ι → ℂ) (hv : IsTranscendenceBasis ℤ v)
    (e : ι ≃ ι) (i : ι) :
    IsAlgClosed.equivOfTranscendenceBasis (R := ℤ) v v e hv hv (v i) = v (e i) := by
  unfold IsAlgClosed.equivOfTranscendenceBasis
  let _ := IsAlgClosed.isAlgClosure_of_transcendence_basis v hv
  dsimp only
  have h := IsAlgClosure.equivOfEquiv_algebraMap (L := ℂ) (M := ℂ)
    (S := Algebra.adjoin ℤ (Set.range v)) (R := Algebra.adjoin ℤ (Set.range v))
    (hv.1.aevalEquiv.symm.toRingEquiv.trans
          ((AlgEquiv.ofAlgHom (MvPolynomial.rename ⇑e) (MvPolynomial.rename ⇑e.symm)
            (by ext; simp) (by ext; simp)).toRingEquiv.trans
            hv.1.aevalEquiv.toRingEquiv))
    ⟨v i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  refine h.trans ?_
  have h2 : hv.1.aevalEquiv.symm ⟨v i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ = MvPolynomial.X i :=
    (AlgEquiv.symm_apply_eq _).2 (Subtype.ext (by simp [AlgebraicIndependent.aevalEquiv]))
  simp [h2]

/-- A complex number with only finitely many images under the field automorphisms of $\mathbb C$ is algebraic
over $\mathbb Q$. -/
@[kb "milne2017mf" "Section 12, proof of Thm. 12.8 (pdf p. 124)"]
theorem isAlgebraic_of_finite_range_ringEquiv (x : ℂ) (h : (Set.range fun σ : ℂ ≃+* ℂ => σ x).Finite) :
    IsAlgebraic ℚ x := by
  by_contra hx
  have hxZ : Transcendental ℤ x := fun hz => hx ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).1 hz)
  have hind : AlgebraicIndepOn ℤ id ({x} : Set ℂ) :=
    (algebraicIndependent_singleton_iff (R := ℤ) (x := fun i : ({x} : Set ℂ) => id (i : ℂ))
      ⟨x, rfl⟩).2 hxZ
  obtain ⟨B, hxB, hB⟩ := exists_isTranscendenceBasis_superset hind
  have hxB' : x ∈ B := hxB rfl
  have hinf : Infinite B := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    have : Nonempty B := ⟨⟨x, hxB'⟩⟩
    have := hB.lift_cardinalMk_eq_max_lift
    have h1 : ℵ₀ < #ℂ := by rw [Cardinal.mk_complex]; exact aleph0_lt_continuum
    have h2 : #ℂ ≤ ℵ₀ := by
      simp only [lift_id'] at this
      rw [this]
      exact max_le (max_le (by simp) Cardinal.mk_le_aleph0) le_rfl
    exact absurd h1 (not_lt.2 h2)
  have hsub : (Set.univ : Set B).Infinite := Set.infinite_univ
  have hsub2 : (((↑) : B → ℂ) '' Set.univ).Infinite :=
    hsub.image Subtype.val_injective.injOn
  refine hsub2 (h.subset ?_)
  rintro _ ⟨b, -, rfl⟩
  refine ⟨IsAlgClosed.equivOfTranscendenceBasis (R := ℤ) ((↑) : B → ℂ) ((↑) : B → ℂ)
    (Equiv.swap ⟨x, hxB'⟩ b) hB hB, ?_⟩
  have := equivOfTranscendenceBasis_apply_self ((↑) : B → ℂ) hB (Equiv.swap ⟨x, hxB'⟩ b) ⟨x, hxB'⟩
  simpa using this

end ModularFormsKB.Milne
