import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.WeilPairing
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Determinant
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Charpoly
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Torsion
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.PowTrace
import Mathlib.FieldTheory.Finite.Extension
import ModularFormsKB.Citation
import TauCeti.LinearAlgebra.Determinant.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Milne, Sections 11 and 12: the `ℓ`-adic representation of the endomorphisms of an elliptic curve

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 11, pdf p. 113, and
Section 12, pdf p. 124.

Let $E$ be an elliptic curve over a separably closed field $k$ and $\ell$ a prime invertible in $k$. An endomorphism
$\alpha$ of $E$ acts on the Tate module $T_\ell E = \varprojlim E_{\ell^n}$ (**D126**; Tau Ceti's `TateModule`); this is
Milne's $\rho_\ell(\alpha)$, here `tateRep`. Endomorphisms are Tau Ceti's morphisms `Hom W W` of the affine Weierstrass
model (zero included), with Tau Ceti's degree (`Hom.degree`, $0$ for the zero morphism) and dual (`Hom.dual`, Milne's
transpose $\alpha'$).

## Items

- **Proposition 11.7** `det_tateRep`: $\deg\alpha = \det\rho_\ell(\alpha)$ (also for $\alpha = 0$). Milne proves it over
  $\mathbb C$ and refers to his Abelian Varieties notes for general $k$; the proof here is characteristic-free: the
  $\ell$-adic Weil pairing is alternating, nondegenerate, and scaled by $\deg\alpha$.
- **Corollary 11.8** `charpoly_tateRep_frobenius`, `charpoly_tateRep_frobenius_eq`: for $E$ over a finite field
  $\mathbb F_q$ (Milne: $\mathbb F_p$; the proof is the same), the characteristic polynomial of the Frobenius on
  $T_\ell E$ is $X^2 - a_qX + q$, and the $\alpha_1,\alpha_2$ of Theorem 11.4 are its roots, for every prime
  $\ell \ne p$.
- **Proposition 11.9** `tateModuleWeilPairing_tateRep_dual`: $\rho_\ell(\alpha')$ is the transpose of
  $\rho_\ell(\alpha)$ for the Weil pairing: $e(\rho_\ell(\alpha)x, y) = e(x, \rho_\ell(\alpha')y)$.
- **D130** `milneTrace`: $\mathrm{Tr}(\alpha) = 1 + \deg\alpha - \deg(1-\alpha)$; `milneTrace_eq_polar` identifies it
  with Tau Ceti's degree polarization.
- **Proposition 12.10** (a) `mul_self_sub_milneTrace_add_degree`: $f_\alpha(\alpha) = 0$ for
  $f_\alpha = X^2 - \mathrm{Tr}(\alpha)X + \deg\alpha$; (b) `charpoly_tateRep`: $f_\alpha$ is the characteristic
  polynomial of $\rho_\ell(\alpha)$ on $T_\ell E$ (hence on $V_\ell E = T_\ell E\otimes\mathbb Q_\ell$).
-/

open TauCeti TauCeti.Isogeny Polynomial
open scoped WeierstrassCurve Classical

namespace ModularFormsKB.Milne

section TateRep

variable {K : Type*} [Field K] [IsSepClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
  (ℓ : ℕ) [Fact ℓ.Prime]

/-- Milne's $\rho_\ell(\alpha)$: the action of an endomorphism $\alpha$ of $E$ on the Tate module $T_\ell E$. -/
@[kb "milne2017mf" "Section 11, the l-adic representation (pdf p. 112)"]
noncomputable def tateRep (f : Hom W.toAffine W.toAffine) :
    Module.End ℤ_[ℓ] (TateModule ℓ W.toAffine.Point) :=
  TateModule.mapLinearMap f.pointMapHom

variable {W ℓ}

omit [IsSepClosed K] in
private theorem coe_proj_tateRep (f : Hom W.toAffine W.toAffine) (x : TateModule ℓ W.toAffine.Point)
    (n : ℕ) :
    ((TateModule.proj n (tateRep W ℓ f x) : TateModuleLevel ℓ W.toAffine.Point n) :
        W.toAffine.Point) = f.pointMap (TateModule.proj n x : W.toAffine.Point) := rfl

private theorem tateModuleWeilPairing_tateRep_tateRep (hℓ : (ℓ : K) ≠ 0)
    (f : Hom W.toAffine W.toAffine) (x y : TateModule ℓ W.toAffine.Point) :
    W.tateModuleWeilPairing hℓ (tateRep W ℓ f x) (tateRep W ℓ f y) =
      f.degree • W.tateModuleWeilPairing hℓ x y := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  apply PadicTateTwist.ext
  intro n
  rw [WeierstrassCurve.proj_tateModuleWeilPairing, map_nsmul,
    WeierstrassCurve.proj_tateModuleWeilPairing]
  rcases eq_or_ne f 0 with rfl | h
  · have h0 : ∀ z : TateModule ℓ W.toAffine.Point, TateModule.proj n (tateRep W ℓ 0 z) = 0 := by
      intro z
      apply Subtype.ext
      rw [coe_proj_tateRep]
      simp
    simp [h0]
  · have := (Hom.toIsogeny h).weilPairing_eq_degree_nsmul_weilPairing (ℓ ^ n)
      (by simpa using pow_ne_zero n hℓ) (S := TateModule.proj n x) (T := TateModule.proj n y)
      (S' := TateModule.proj n (tateRep W ℓ f x)) (T' := TateModule.proj n (tateRep W ℓ f y))
      (by rw [Hom.ofIsogeny_toIsogeny, coe_proj_tateRep])
      (by rw [Hom.ofIsogeny_toIsogeny, coe_proj_tateRep])
    rw [this, ← Hom.degree_ofIsogeny, Hom.ofIsogeny_toIsogeny]

/-- **Proposition 11.7** (Milne): the degree of an endomorphism $\alpha$ of $E$ is $\det\rho_\ell(\alpha)$. -/
@[kb "milne2017mf" "Section 11, Prop. 11.7 (pdf p. 113)"]
theorem det_tateRep (hℓ : (ℓ : K) ≠ 0) (f : Hom W.toAffine W.toAffine) :
    LinearMap.det (tateRep W ℓ f) = (f.degree : ℤ_[ℓ]) := by
  let : NeZero (ℓ : K) := ⟨hℓ⟩
  let e := (W.nonempty_linearEquiv_tateModule hℓ).some
  let b := (Pi.basisFun ℤ_[ℓ] (Fin 2)).map e.symm
  have hω : W.tateModuleWeilPairing hℓ ≠ 0 := by
    intro h
    apply b.ne_zero 0
    apply W.tateModuleWeilPairing_nondegenerate hℓ
    intro y
    simp [h]
  apply LinearMap.det_eq_of_compl₁₂_self_eq_smul b
    (W.tateModuleWeilPairing_self hℓ) hω
  apply LinearMap.ext₂
  intro x y
  simp only [LinearMap.compl₁₂_apply, LinearMap.smul_apply]
  rw [tateModuleWeilPairing_tateRep_tateRep, Nat.cast_smul_eq_nsmul]

/-- **Proposition 11.9** (Milne): $\rho_\ell(\alpha')$ is the transpose of $\rho_\ell(\alpha)$ with respect to the
$\ell$-adic Weil pairing, $\alpha'$ the dual (transpose) of $\alpha$. -/
@[kb "milne2017mf" "Section 11, Prop. 11.9 (pdf p. 113)"]
theorem tateModuleWeilPairing_tateRep_dual (hℓ : (ℓ : K) ≠ 0) (f : Hom W.toAffine W.toAffine)
    (x y : TateModule ℓ W.toAffine.Point) :
    W.tateModuleWeilPairing hℓ (tateRep W ℓ f x) y = W.tateModuleWeilPairing hℓ x (tateRep W ℓ f.dual y) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  apply PadicTateTwist.ext
  intro n
  rw [WeierstrassCurve.proj_tateModuleWeilPairing, WeierstrassCurve.proj_tateModuleWeilPairing]
  rcases eq_or_ne f 0 with rfl | h
  · have h0 : ∀ z : TateModule ℓ W.toAffine.Point, TateModule.proj n (tateRep W ℓ 0 z) = 0 := by
      intro z
      apply Subtype.ext
      rw [coe_proj_tateRep]
      simp
    simp [h0, Hom.dual_zero]
  · exact (Hom.toIsogeny h).weilPairing_eq_weilPairing_dual (ℓ ^ n)
      (by simpa using pow_ne_zero n hℓ) (S := TateModule.proj n x) (T := TateModule.proj n y)
      (S' := TateModule.proj n (tateRep W ℓ f x)) (T' := TateModule.proj n (tateRep W ℓ f.dual y))
      (by rw [Hom.ofIsogeny_toIsogeny, coe_proj_tateRep])
      (by rw [← Hom.dual_ofIsogeny, Hom.ofIsogeny_toIsogeny, coe_proj_tateRep])

end TateRep

section Trace

variable {K : Type*} [Field K] {W : WeierstrassCurve.Affine K} [W.IsElliptic]

/-- **D130** (Milne): the trace $\mathrm{Tr}(\alpha) = 1 + \deg\alpha - \deg(1-\alpha)$ of an endomorphism. -/
@[kb "milne2017mf" "Section 12, trace of an endomorphism (pdf p. 124)"]
noncomputable def milneTrace (f : Hom W W) : ℤ :=
  1 + (f.degree : ℤ) - ((1 - f).degree : ℤ)

/-- Milne's trace is Tau Ceti's degree polarization $\deg(\alpha+1) - \deg\alpha - 1$. -/
theorem milneTrace_eq_polar (f : Hom W W) :
    milneTrace f = QuadraticMap.polar (fun h : Hom W W ↦ (h.degree : ℤ)) f 1 := by
  have h := Hom.polar_degree_add_right f 1 (-1)
  rw [add_neg_cancel, Hom.polar_degree_zero_right] at h
  have h2 : QuadraticMap.polar (fun h : Hom W W ↦ (h.degree : ℤ)) f (-1) =
      ((1 - f).degree : ℤ) - f.degree - 1 := by
    have h3 : f + -1 = -(1 - f) := by abel
    rw [QuadraticMap.polar, h3, Hom.degree_neg, Hom.degree_neg, Hom.one_def, Hom.degree_id]
    simp
  unfold milneTrace
  linarith

/-- **Proposition 12.10 (a)** (Milne): an endomorphism is a root of $f_\alpha = X^2 - \mathrm{Tr}(\alpha)X +
\deg\alpha$. -/
@[kb "milne2017mf" "Section 12, Prop. 12.10(a) (pdf p. 124)"]
theorem mul_self_sub_milneTrace_add_degree (f : Hom W W) :
    f * f - milneTrace f • f + (f.degree : ℤ) • (1 : Hom W W) = 0 := by
  rw [milneTrace_eq_polar, Hom.mul_self_eq_polar_smul_sub_degree]
  abel

end Trace

section Charpoly

variable {K : Type*} [Field K] [IsSepClosed K] {W : WeierstrassCurve K} [W.IsElliptic]
  {ℓ : ℕ} [Fact ℓ.Prime]

/-- **Proposition 12.10 (b)** (Milne): $f_\alpha = X^2 - \mathrm{Tr}(\alpha)X + \deg\alpha$ is the characteristic
polynomial of $\rho_\ell(\alpha)$ on $T_\ell E$. -/
@[kb "milne2017mf" "Section 12, Prop. 12.10(b) (pdf p. 124)"]
theorem charpoly_tateRep (hℓ : (ℓ : K) ≠ 0) (f : Hom W.toAffine W.toAffine) :
    haveI := W.free_tateModule hℓ
    haveI := W.finite_tateModule hℓ
    (tateRep W ℓ f).charpoly =
      X ^ 2 - C (milneTrace f : ℤ_[ℓ]) * X + C (f.degree : ℤ_[ℓ]) := by
  have : NeZero (ℓ : K) := ⟨hℓ⟩
  have hfree := W.free_tateModule hℓ
  have hfin := W.finite_tateModule hℓ
  let e := (W.nonempty_linearEquiv_tateModule hℓ).some
  let b := (Pi.basisFun ℤ_[ℓ] (Fin 2)).map e.symm
  have hsub : tateRep W ℓ (1 - f) = 1 - tateRep W ℓ f := by
    apply LinearMap.ext
    intro x
    apply TateModule.ext
    intro n
    apply Subtype.ext
    simp [coe_proj_tateRep, Hom.sub_pointMap, Hom.one_def, Hom.id_pointMap]
  rw [← LinearMap.charpoly_toMatrix _ b]
  set M := LinearMap.toMatrix b b (tateRep W ℓ f) with hM
  have hdet : M.det = f.degree := by rw [hM, LinearMap.det_toMatrix, det_tateRep hℓ]
  have hdet1 : (1 - M).det = ((1 - f).degree : ℤ_[ℓ]) := by
    rw [← det_tateRep hℓ, hsub, ← LinearMap.det_toMatrix b, map_sub, Module.End.one_eq_id, LinearMap.toMatrix_id]
  have h := Matrix.det_one_sub_fin_two M
  rw [hdet1, hdet] at h
  rw [Matrix.charpoly_fin_two, hdet]
  have htr : M.trace = (milneTrace f : ℤ_[ℓ]) := by
    unfold milneTrace
    push_cast
    linear_combination h
  rw [htr]

end Charpoly

section Frobenius

variable {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve F) [W.IsElliptic]
  {K : Type*} [Field K] [IsSepClosed K] [Algebra F K] {ℓ : ℕ} [Fact ℓ.Prime]

/-- **Corollary 11.8** (Milne), characteristic polynomial: the Frobenius $\pi_q$ of an elliptic curve over a finite
field with $q$ elements acts on $T_\ell E$ with characteristic polynomial $X^2 - a_qX + q$, $a_q$ the Frobenius
trace, for every prime $\ell$ invertible in $F$. -/
@[kb "milne2017mf" "Section 11, Cor. 11.8 (pdf p. 113)"]
theorem charpoly_tateRep_frobenius (hℓ : (ℓ : K) ≠ 0) :
    haveI := (W⁄K).free_tateModule hℓ
    haveI := (W⁄K).finite_tateModule hℓ
    (tateRep (W⁄K) ℓ (Hom.ofIsogeny (baseChangeFrobenius K W.toAffine))).charpoly =
      X ^ 2 - C (W.frobeniusTrace : ℤ_[ℓ]) * X + C (Nat.card F : ℤ_[ℓ]) := by
  have hdeg : (Hom.ofIsogeny (baseChangeFrobenius K W.toAffine)).degree = Nat.card F := by
    rw [Hom.degree_ofIsogeny, baseChangeFrobenius_def]
    exact (TauCeti.Isogeny.degree_map _ _).trans (degree_frobeniusIsogeny W.toAffine)
  have htr : milneTrace (Hom.ofIsogeny (baseChangeFrobenius K W.toAffine)) =
      W.frobeniusTrace := by
    unfold milneTrace
    rw [Hom.one_def, Hom.degree_id_sub_ofIsogeny_baseChangeFrobenius_eq_pointCount (K := K) W,
      hdeg, WeierstrassCurve.frobeniusTrace_def]
    ring
  have := charpoly_tateRep (W := W⁄K) (ℓ := ℓ) hℓ (Hom.ofIsogeny (baseChangeFrobenius K W.toAffine))
  rw [htr, hdeg] at this
  simpa using this

/-- **Corollary 11.8** (Milne): the numbers $\alpha_1,\alpha_2$ of Theorem 11.4 (any complex numbers with
$N_n = 1 + q^n - \alpha_1^n - \alpha_2^n$ for the point counts over all finite extensions) are the eigenvalues of the
Frobenius on $T_\ell E$: its characteristic polynomial is the image of an integer polynomial $P$ with
$P = (X-\alpha_1)(X-\alpha_2)$ over $\mathbb C$. -/
@[kb "milne2017mf" "Section 11, Cor. 11.8 (pdf p. 113)"]
theorem charpoly_tateRep_frobenius_eq (hℓ : (ℓ : K) ≠ 0) (α₁ α₂ : ℂ)
    (hα : ∀ (E : Type) [Field E] [Finite E] [Algebra F E],
      ((W⁄E).pointCount : ℂ) = 1 + (Nat.card F : ℂ) ^ Module.finrank F E -
        α₁ ^ Module.finrank F E - α₂ ^ Module.finrank F E) :
    haveI := (W⁄K).free_tateModule hℓ
    haveI := (W⁄K).finite_tateModule hℓ
    ∃ P : ℤ[X], (tateRep (W⁄K) ℓ (Hom.ofIsogeny (baseChangeFrobenius K W.toAffine))).charpoly =
        P.map (Int.castRingHom ℤ_[ℓ]) ∧
      P.map (Int.castRingHom ℂ) = (X - C α₁) * (X - C α₂) := by
  have hp : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  have key : ∀ (n : ℕ) [NeZero n],
      (W.frobeniusPowTrace n : ℂ) = α₁ ^ n + α₂ ^ n := by
    intro n _
    have h := hα (FiniteField.Extension F (ringChar F) n)
    rw [FiniteField.finrank_extension] at h
    have h3 := W.frobeniusPowTrace_finrank (FiniteField.Extension F (ringChar F) n)
    rw [FiniteField.finrank_extension, WeierstrassCurve.frobeniusTrace_def,
      FiniteField.natCard_extension] at h3
    have h3' : (W.frobeniusPowTrace n : ℂ) =
        (Nat.card F : ℂ) ^ n + 1 - ((W⁄(FiniteField.Extension F (ringChar F) n)).pointCount : ℂ) := by
      rw [h3]
      push_cast
      ring
    linear_combination h3' - h
  have h1 : (W.frobeniusTrace : ℂ) = α₁ + α₂ := by
    have := key 1
    rw [W.frobeniusPowTrace_one] at this
    simpa using this
  have h2 : (W.frobeniusPowTrace 2 : ℂ) = (W.frobeniusTrace : ℂ) ^ 2 - 2 * (Nat.card F : ℂ) := by
    have := W.frobeniusPowTrace_add_two 0
    simp only [zero_add, WeierstrassCurve.frobeniusPowTrace_one,
      WeierstrassCurve.frobeniusPowTrace_zero] at this
    rw [show (2 : ℕ) = 0 + 2 from rfl, this]
    push_cast
    ring
  have h4 := key 2
  have hq : (Nat.card F : ℂ) = α₁ * α₂ := by
    rw [h2, h1] at h4
    linear_combination (-1 / 2 : ℂ) * h4
  refine ⟨X ^ 2 - C W.frobeniusTrace * X + C (Nat.card F : ℤ), ?_, ?_⟩
  · rw [charpoly_tateRep_frobenius W hℓ]
    simp
  · have : (X - C α₁) * (X - C α₂) = X ^ 2 - C (α₁ + α₂) * X + C (α₁ * α₂) := by
      simp only [C_add, C_mul]
      ring
    rw [this, ← h1, ← hq]
    simp

end Frobenius

end ModularFormsKB.Milne
