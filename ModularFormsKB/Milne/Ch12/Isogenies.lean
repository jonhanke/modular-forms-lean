import ModularFormsKB.Milne.Ch12.CMDefs
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Differential
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Factorisation
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Factorisation
import Mathlib.Algebra.MvPolynomial.PDeriv
import ModularFormsKB.Citation
/-!
# Milne, Section 12: $\mathfrak a$-isogenies, tangent spaces and the Frobenius map (12.19–12.24)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, pdf pp. 126–128.

## Items

- **D133** `cmKer`: $\mathrm{Ker}(\mathfrak a) = \bigcap_{a\in\mathfrak a}\mathrm{Ker}(a\colon E\to E)$ for $E$ with
  complex multiplication $i\colon R \cong \mathrm{End}(E)$ (points over the base field), and `cmKerAlg` (points over an
  algebraic closure).
- **Lemma 12.19** `ker_latticeQuotientMap`: for lattices $\Lambda$ (a proper $R$-ideal) and an invertible integral
  ideal $\mathfrak a$ of $R$, the canonical map $\mathbb C/\Lambda \to \mathbb C/\Lambda\mathfrak a^{-1}$ has kernel
  $\mathrm{Ker}(\mathfrak a) = \{z \bmod \Lambda \mid az \in \Lambda\ \forall a \in \mathfrak a\}$.
- **Proposition 12.20** `AIsogenyExists` (named): in characteristic zero, the $\mathfrak a$-isogeny
  $\varphi_{\mathfrak a}\colon E \to \mathfrak a * E$ with kernel $\mathrm{Ker}(\mathfrak a)$ and its universal property.
  **D136, D137**: `IsAIsogeny` (an isogeny with kernel $\mathrm{Ker}(\mathfrak a)$ over $k^{\mathrm{al}}$; Milne's
  construction as the image in $E^n$ needs products of curves, not available).
- **Proposition 12.21** `ClassGroupActionPrincipal` (named; Milne omits the proof): $\mathrm{Cl}(R)$ acts simply
  transitively on $\mathrm{Ell}_k(R)$. *Deviation*: stated for $k$ algebraically closed of characteristic zero,
  where isomorphism classes are $j$-invariants and kernels are groups of points; in characteristic $p$ the kernel
  of an inseparable isogeny is not determined by points.
- **D138, D139** `tangentAtOrigin`: the tangent line at $0$ of a Weierstrass equation over a ring $A$, computed in the
  chart $Y = 1$ (coordinates $X/Y$, $Z/Y$ of $Y^2Z + a_1XYZ + a_3YZ^2 = X^3 + a_2X^2Z + a_4XZ^2 + a_6Z^3$), as the
  submodule of $A^2$ cut out by $\frac{\partial F}{\partial X}(0,0)X + \frac{\partial F}{\partial Z}(0,0)Z = 0$.
- **Proposition 12.22** `tangentAtOrigin_eq_span`, `tangentAtOrigin_map`: it is free of rank one (spanned by
  $(1,0)$) and compatible with every base change (in particular to $K_v$ and to the residue field $\kappa(v)$).
- **D140, D141**: $E^{(p)}$ is Mathlib's `WeierstrassCurve.map` along the Frobenius `frobenius F p`, and
  $\mathrm{Frob}_p$ is Tau Ceti's `relativeFrobeniusIsogeny p W`.
- **Proposition 12.23** `relativeFrobenius_isPurelyInseparable_and_degree`, `exists_isIso_comp_relativeFrobenius`.
- **Remark 12.24** `isSeparable_iff_pullback_invariantDifferential_ne_zero` (Tau Ceti, in the dual form: an isogeny is
  separable iff it is nonzero on invariant differentials, which by Remark 11.6 is the transpose of the map on
  tangent spaces).
-/

open NumberField TauCeti TauCeti.Isogeny TauCeti.GlobalNumberFields
open scoped WeierstrassCurve Classical

namespace ModularFormsKB.Milne

/-! ### $\mathrm{Ker}(\mathfrak a)$ -/

section CMKer

variable {k : Type*} [Field k] {W : WeierstrassCurve.Affine k} [W.IsElliptic]
  {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K}

/-- **D133** (Milne): $\mathrm{Ker}(\mathfrak a) = \bigcap_{a\in\mathfrak a}\mathrm{Ker}(i(a))$ on the points of $E$
over $k$. -/
@[kb "milne2017mf" "Section 12, Ker(a) (pdf p. 126)"]
noncomputable def cmKer (i : O.toSubalgebra ≃+* Hom W W) (I : Ideal O.toSubalgebra) : AddSubgroup W.Point :=
  ⨅ a ∈ I, (i a).pointMapHom.ker

/-- $\mathrm{Ker}(\mathfrak a)$ on the points of $E$ over an algebraic closure of $k$. -/
noncomputable def cmKerAlg (i : O.toSubalgebra ≃+* Hom W W) (I : Ideal O.toSubalgebra) :
    AddSubgroup (W.map (algebraMap k (AlgebraicClosure k))).Point :=
  ⨅ a ∈ I, ((i a).map (algebraMap k (AlgebraicClosure k))).pointMapHom.ker

/-- **D136, D137** (Milne): an $\mathfrak a$-isogeny is a morphism $E \to E'$ whose kernel (on points over $k^{\mathrm
al}$) is $\mathrm{Ker}(\mathfrak a)$. -/
@[kb "milne2017mf" "Section 12, a-isogeny (pdf p. 126)"]
def IsAIsogeny (i : O.toSubalgebra ≃+* Hom W W) (I : Ideal O.toSubalgebra) {W' : WeierstrassCurve.Affine k}
    [W'.IsElliptic] (φ : Hom W W') : Prop :=
  (φ.map (algebraMap k (AlgebraicClosure k))).pointMapHom.ker = cmKerAlg i I

end CMKer

/-! ### Lemma 12.19 -/

section Lattice

variable {K : Type*} [Field K] [NumberField K] (ι : K →+* ℂ) (O : NumberFieldOrder K)

/-- Milne's $\mathrm{Ker}(\mathfrak a)$ on $E(\Lambda) = \mathbb C/\Lambda$, pulled back to $\mathbb C$:
$\{z \in \mathbb C \mid \iota(a)z \in \Lambda\ \forall a\in\mathfrak a\}$. -/
def latticeCMKer (Λ : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) (I : Ideal O.toSubalgebra) :
    AddSubgroup ℂ where
  carrier := {z | ∀ a ∈ I, ι (a : K) * z ∈ idealLattice ι O Λ}
  add_mem' ha hb a h := by simpa [mul_add] using (idealLattice ι O Λ).add_mem (ha a h) (hb a h)
  zero_mem' a _ := by simp
  neg_mem' ha a h := by simpa [mul_neg] using (idealLattice ι O Λ).neg_mem (ha a h)

theorem mem_idealLattice_iff (J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) (z : ℂ) :
    z ∈ idealLattice ι O J ↔ ∃ w ∈ J, ι w = z := by
  simp [idealLattice]

theorem mem_mul_inv_iff (Λ : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)
    (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) (hI : IsUnit I) (w : K) :
    w ∈ Λ * I⁻¹ ↔ ∀ a ∈ I, a * w ∈ Λ := by
  have hu : I * I⁻¹ = 1 := (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mpr hI
  constructor
  · intro hw a ha
    have h1 : a * w ∈ I * (Λ * I⁻¹) := FractionalIdeal.mul_mem_mul ha hw
    have h2 : I * (Λ * I⁻¹) = Λ := by rw [mul_left_comm, hu, mul_one]
    rwa [h2] at h1
  · intro h
    have h1 : FractionalIdeal.spanSingleton (nonZeroDivisors O.toSubalgebra) w * I ≤ Λ :=
      FractionalIdeal.spanSingleton_mul_le_iff.mpr fun z hz => by
        rw [mul_comm]; exact h z hz
    have h2 : FractionalIdeal.spanSingleton (nonZeroDivisors O.toSubalgebra) w ≤ Λ * I⁻¹ := by
      calc FractionalIdeal.spanSingleton (nonZeroDivisors O.toSubalgebra) w
          = FractionalIdeal.spanSingleton (nonZeroDivisors O.toSubalgebra) w * (I * I⁻¹) := by
            rw [hu, mul_one]
        _ = (FractionalIdeal.spanSingleton (nonZeroDivisors O.toSubalgebra) w * I) * I⁻¹ := by
            rw [mul_assoc]
        _ ≤ Λ * I⁻¹ := mul_le_mul' h1 le_rfl
    exact h2 (FractionalIdeal.mem_spanSingleton_self _ w)

theorem mem_idealLattice_mul_inv_iff (Λ : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)
    (I : Ideal O.toSubalgebra)
    (hI : IsUnit (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)) (z : ℂ) :
    z ∈ idealLattice ι O (Λ * (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)⁻¹) ↔
      z ∈ latticeCMKer ι O Λ I := by
  rw [mem_idealLattice_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩ a ha
    rw [mem_mul_inv_iff O Λ _ hI] at hw
    rw [mem_idealLattice_iff]
    exact ⟨_, hw (a : K) (FractionalIdeal.mem_coeIdeal_of_mem _ ha), by simp⟩
  · intro hz
    have hne : I ≠ ⊥ := by
      rintro rfl
      have : ((⊥ : Ideal O.toSubalgebra) : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) = 0 :=
        FractionalIdeal.coeIdeal_bot
      rw [this] at hI
      exact not_isUnit_zero hI
    obtain ⟨a0, ha0, ha0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨y, -, hy⟩ := (mem_idealLattice_iff ι O Λ _).mp (hz a0 ha0)
    have ha0K' : (a0 : K) ≠ 0 := fun h => ha0ne (Subtype.ext h)
    have ha0K : ι (a0 : K) ≠ 0 := by
      intro h
      exact ha0K' (ι.injective (h.trans (map_zero ι).symm))
    refine ⟨y / (a0 : K), ?_, ?_⟩
    · rw [mem_mul_inv_iff O Λ _ hI]
      intro a ha
      obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp ha
      obtain ⟨y', hy', hy'e⟩ := (mem_idealLattice_iff ι O Λ _).mp (hz x hx)
      have : y' = (algebraMap O.toSubalgebra K x) * (y / (a0 : K)) := by
        apply ι.injective
        rw [hy'e, map_mul, map_div₀, hy]
        field_simp
        exact mul_comm _ _
      rw [← this]; exact hy'
    · rw [map_div₀, hy]; field_simp

/-- **Lemma 12.19** (Milne): for a proper $R$-ideal $\Lambda$ and an invertible integral ideal $\mathfrak a$ of $R$,
$\Lambda \subseteq \Lambda\mathfrak a^{-1}$ and the canonical map $\mathbb C/\Lambda \to \mathbb C/\Lambda\mathfrak
a^{-1}$, $z + \Lambda \mapsto z + \Lambda\mathfrak a^{-1}$, has kernel $\mathrm{Ker}(\mathfrak a)$. -/
@[kb "milne2017mf" "Section 12, Lemma 12.19 (pdf p. 126)"]
theorem ker_latticeQuotientMap (Λ : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)
    (hΛ : O.IsProperFractionalIdeal Λ) (I : Ideal O.toSubalgebra)
    (hI : IsUnit (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)) :
    ∃ h : (idealLattice ι O Λ).toAddSubgroup ≤
        (idealLattice ι O (Λ * (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)⁻¹)).toAddSubgroup,
      (QuotientAddGroup.map (idealLattice ι O Λ).toAddSubgroup
        (idealLattice ι O (Λ * (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)⁻¹)).toAddSubgroup
        (AddMonoidHom.id ℂ) fun _ hx ↦ h hx).ker =
        (latticeCMKer ι O Λ I).map (QuotientAddGroup.mk' _) := by
  have hu : (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) *
      (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)⁻¹ = 1 :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mpr hI
  have hle : Λ ≤ Λ * (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)⁻¹ := by
    have h1 : (1 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) ≤
        (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)⁻¹ := by
      calc (1 : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)
          = (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) *
            (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)⁻¹ := hu.symm
        _ ≤ 1 * (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)⁻¹ :=
            mul_le_mul' FractionalIdeal.coeIdeal_le_one le_rfl
        _ = _ := one_mul _
    calc Λ = Λ * 1 := (mul_one Λ).symm
      _ ≤ _ := mul_le_mul' le_rfl h1
  have h : (idealLattice ι O Λ).toAddSubgroup ≤
      (idealLattice ι O (Λ * (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)⁻¹)).toAddSubgroup := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := (mem_idealLattice_iff ι O Λ _).mp hz
    exact (mem_idealLattice_iff ι O _ _).mpr ⟨w, hle hw, rfl⟩
  refine ⟨h, ?_⟩
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    rw [AddMonoidHom.mem_ker]
    simp only [AddSubgroup.mem_map, QuotientAddGroup.mk'_apply]
    change (QuotientAddGroup.mk z : ℂ ⧸ (idealLattice ι O (Λ * (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)⁻¹)).toAddSubgroup) = 0 ↔ _
    rw [QuotientAddGroup.eq_zero_iff]
    change z ∈ idealLattice ι O _ ↔ _
    rw [mem_idealLattice_mul_inv_iff ι O Λ I hI]
    constructor
    · intro hz; exact ⟨z, hz, rfl⟩
    · rintro ⟨y, hy, hyz⟩
      have hd : -y + z ∈ (idealLattice ι O Λ).toAddSubgroup := QuotientAddGroup.eq.mp hyz
      have hd' : -y + z ∈ latticeCMKer ι O Λ I :=
        (mem_idealLattice_mul_inv_iff ι O Λ I hI _).mp (h hd)
      have := add_mem hy hd'
      simpa using this

end Lattice

/-! ### Proposition 12.20 and Proposition 12.21 (named statements) -/

/-- **Proposition 12.20** (Milne; Silverman, *The Arithmetic of Elliptic Curves*, III.4.12, III.4.13.2): for an
elliptic curve $E$ over a field $k$ of characteristic zero with complex multiplication $i\colon R \cong
\mathrm{End}(E)$ and a proper integral ideal $\mathfrak a$ of $R$, there are an elliptic curve $\mathfrak a * E$ and a
morphism $\varphi_{\mathfrak a}\colon E \to \mathfrak a * E$ with kernel $\mathrm{Ker}(\mathfrak a)$ such that every
morphism $\varphi\colon E \to E'$ with $\mathrm{Ker}(\mathfrak a) \subseteq \mathrm{Ker}(\varphi)$ factors uniquely
through $\varphi_{\mathfrak a}$. Named statement. -/
@[kb "milne2017mf" "Section 12, Prop. 12.20 (pdf p. 126)"]
structure AIsogenyExists : Prop where
  exists_universal : ∀ (k : Type) [Field k] [CharZero k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
    (K : Type) [Field K] [NumberField K] (O : NumberFieldOrder K) (i : O.toSubalgebra ≃+* Hom W W)
    (I : Ideal O.toSubalgebra), I ≠ ⊥ →
      O.IsProperFractionalIdeal (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) →
    ∃ (W' : WeierstrassCurve.Affine k) (_ : W'.IsElliptic) (φ : Hom W W'), IsAIsogeny i I φ ∧
      ∀ (W'' : WeierstrassCurve.Affine k) [W''.IsElliptic] (ψ : Hom W W''),
        cmKerAlg i I ≤ (ψ.map (algebraMap k (AlgebraicClosure k))).pointMapHom.ker →
          ∃! χ : Hom W' W'', χ.comp φ = ψ

/-- $\mathrm{Ell}_k(R)$ for an algebraically closed field $k$: the $j$-invariants of the elliptic curves over $k$ with
complex multiplication by $R$ (over $k$ algebraically closed, curves are isomorphic iff their $j$-invariants agree). -/
def EllCMOver (k : Type*) [Field k] {K : Type*} [Field K] [NumberField K] (O : NumberFieldOrder K) : Set k :=
  {x | ∃ (W : WeierstrassCurve k) (_ : W.IsElliptic), HasCMBy W O ∧ W.j = x}

/-- **Proposition 12.21** (Milne; proof omitted in the book): the action $(\mathfrak a, E) \mapsto \mathfrak a * E$
makes $\mathrm{Ell}_k(R)$ a principal homogeneous space for $\mathrm{Cl}(R)$; the action is characterized by
$[\mathfrak a] \cdot j(E) = j(E')$ for every $\mathfrak a$-isogeny $E \to E'$, $\mathfrak a$ integral and invertible.
Named statement, for $k$ algebraically closed of characteristic zero (see the module docstring). -/
@[kb "milne2017mf" "Section 12, Prop. 12.21 (pdf p. 126)"]
structure ClassGroupActionPrincipal : Prop where
  principal : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (K : Type) [Field K] [NumberField K]
    (O : NumberFieldOrder K), Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∃ act : Pic O → EllCMOver k O → EllCMOver k O,
      (∀ (W W' : WeierstrassCurve.Affine k) [W.IsElliptic] [W'.IsElliptic] (i : O.toSubalgebra ≃+* Hom W W)
          (I : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ) (J : Ideal O.toSubalgebra),
          ((J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) = I) →
          (hW : W.j ∈ EllCMOver k O) → (hW' : W'.j ∈ EllCMOver k O) → (φ : Hom W W') → IsAIsogeny i J φ →
            act (ClassGroup.mk (K := K) I) ⟨W.j, hW⟩ = ⟨W'.j, hW'⟩) ∧
      ∀ x₀, Function.Bijective fun c ↦ act c x₀

/-! ### Tangent spaces (D138, D139, Proposition 12.22) -/

section Tangent

variable {A : Type*} [CommRing A]

/-- The Weierstrass equation in the chart $Y = 1$ at the origin $O = (0:1:0)$, in the coordinates $X$ (index $0$) and
$Z$ (index $1$): $F = Z + a_1XZ + a_3Z^2 - X^3 - a_2X^2Z - a_4XZ^2 - a_6Z^3$. -/
noncomputable def chartPolynomial (W : WeierstrassCurve A) : MvPolynomial (Fin 2) A :=
  let X := MvPolynomial.X 0
  let Z := MvPolynomial.X 1
  Z + MvPolynomial.C W.a₁ * X * Z + MvPolynomial.C W.a₃ * Z ^ 2 - X ^ 3 - MvPolynomial.C W.a₂ * X ^ 2 * Z -
    MvPolynomial.C W.a₄ * X * Z ^ 2 - MvPolynomial.C W.a₆ * Z ^ 3

/-- **D138, D139** (Milne): the tangent space at the origin of the curve defined by a Weierstrass equation over $A$:
the $A$-submodule of $A^2$ defined by $\frac{\partial F}{\partial X}(0,0)\,X + \frac{\partial F}{\partial Z}(0,0)\,Z
= 0$ (the origin of the chart is $O$, so $X - a = X$ and $Z - b = Z$). -/
@[kb "milne2017mf" "Section 12, tangent space at 0 (pdf p. 127)"]
noncomputable def tangentAtOrigin (W : WeierstrassCurve A) : Submodule A (A × A) :=
  LinearMap.ker ((MvPolynomial.eval 0 (MvPolynomial.pderiv 0 (chartPolynomial W))) • LinearMap.fst A A A +
    (MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (chartPolynomial W))) • LinearMap.snd A A A)

/-- **Proposition 12.22** (Milne), freeness: the tangent space at $0$ of a Weierstrass equation over $A$ is the line
$Z = 0$, free of rank one with basis $(1, 0)$. -/
@[kb "milne2017mf" "Section 12, Prop. 12.22 (pdf p. 127)"]
theorem tangentAtOrigin_eq_span (W : WeierstrassCurve A) :
    tangentAtOrigin W = Submodule.span A {((1 : A), (0 : A))} := by
  have h0 : MvPolynomial.eval 0 (MvPolynomial.pderiv 0 (chartPolynomial W)) = 0 := by
    simp [chartPolynomial, MvPolynomial.pderiv_X, Pi.single_apply]
  have h1 : MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (chartPolynomial W)) = 1 := by
    simp [chartPolynomial, MvPolynomial.pderiv_X, Pi.single_apply]
  ext ⟨x, y⟩
  simp only [tangentAtOrigin, h0, h1, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, smul_eq_mul, zero_mul, one_mul, zero_add,
    Submodule.mem_span_singleton, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Prod.mk.injEq]
  constructor
  · intro h; exact ⟨x, rfl, h.symm⟩
  · rintro ⟨a, rfl, h⟩; exact h.symm

/-- **Proposition 12.22** (Milne), freeness: $(1,0)$ is a basis of the tangent space, which is free of rank one. -/
@[kb "milne2017mf" "Section 12, Prop. 12.22 (pdf p. 127)"]
theorem tangentAtOrigin_free [Nontrivial A] (W : WeierstrassCurve A) :
    Module.Free A (tangentAtOrigin W) ∧ Module.finrank A (tangentAtOrigin W) = 1 := by
  rw [tangentAtOrigin_eq_span]
  have hinj : Function.Injective (LinearMap.toSpanSingleton A (A × A) ((1 : A), (0 : A))) := by
    intro r s h
    simpa using congrArg Prod.fst h
  let e : A ≃ₗ[A] Submodule.span A {((1 : A), (0 : A))} :=
    (LinearEquiv.ofInjective _ hinj).trans
      (LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range A (A × A) _).symm)
  exact ⟨Module.Free.of_equiv e, by rw [← e.finrank_eq]; simp⟩

/-- **Proposition 12.22** (Milne), base change: for every ring homomorphism $f\colon A \to B$ (e.g. $\mathcal O_v \to
K_v$ or $\mathcal O_v \to \kappa(v)$), the image of $\mathrm{Tgt}_0(\mathcal E)$ spans $\mathrm{Tgt}_0(\mathcal E
\otimes B)$, i.e. $\mathrm{Tgt}_0(\mathcal E) \otimes_A B = \mathrm{Tgt}_0(\mathcal E_B)$. -/
@[kb "milne2017mf" "Section 12, Prop. 12.22 (pdf p. 127)"]
theorem tangentAtOrigin_map {B : Type*} [CommRing B] (f : A →+* B) (W : WeierstrassCurve A) :
    tangentAtOrigin (W.map f) =
      Submodule.span B ((Prod.map f f) '' (tangentAtOrigin W : Set (A × A))) := by
  rw [tangentAtOrigin_eq_span (W.map f), tangentAtOrigin_eq_span W]
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem]
    apply Submodule.subset_span
    exact ⟨(1, 0), Submodule.mem_span_singleton_self _, by simp⟩
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    exact ⟨f a, by simp⟩

end Tangent

/-! ### The Frobenius map (D140, D141, Proposition 12.23, Remark 12.24) -/

section Frobenius

variable {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **Proposition 12.23** (Milne), first part: the Frobenius map $\mathrm{Frob}_p\colon E \to E^{(p)}$ (**D140**, **D141**:
Tau Ceti's relative Frobenius, $(x, y) \mapsto (x^p, y^p)$ onto the curve with coefficients raised to the $p$-th power)
is a purely inseparable isogeny of degree $p$. -/
@[kb "milne2017mf" "Section 12, Prop. 12.23 (pdf p. 128)"]
theorem relativeFrobenius_isPurelyInseparable_and_degree :
    IsPurelyInseparable (relativeFrobeniusIsogeny p W).fieldPullback.fieldRange W.FunctionField ∧
      (relativeFrobeniusIsogeny p W).degree = p :=
  ⟨inferInstance, degree_relativeFrobeniusIsogeny p W⟩

/-- **Proposition 12.23** (Milne), second part: every purely inseparable isogeny $\varphi\colon E \to E'$ of degree $p$
is $\alpha \circ \mathrm{Frob}_p$ for an isomorphism $\alpha\colon E^{(p)} \to E'$. -/
@[kb "milne2017mf" "Section 12, Prop. 12.23 (pdf p. 128)"]
theorem exists_isIso_comp_relativeFrobenius {W' : WeierstrassCurve.Affine F} [W'.IsElliptic] (φ : Isogeny W W')
    (hφ : IsPurelyInseparable φ.fieldPullback.fieldRange W.FunctionField) (hdeg : φ.degree = p) :
    ∃ α : Isogeny (W.map (frobenius F p)) W',
      (∃ β : Isogeny W' (W.map (frobenius F p)), β.comp α = Isogeny.id _ ∧ α.comp β = Isogeny.id _) ∧
        α.comp (relativeFrobeniusIsogeny p W) = φ := by
  have main : ∀ (g : F →+* F) (hg : frobenius F p = g) (χ : Isogeny (W.map g) W'),
      χ.degree = 1 →
      χ.comp (congrArg W.map hg ▸ relativeFrobeniusIsogeny p W) = φ →
      ∃ α : Isogeny (W.map (frobenius F p)) W',
        (∃ β : Isogeny W' (W.map (frobenius F p)), β.comp α = Isogeny.id _ ∧ α.comp β = Isogeny.id _) ∧
          α.comp (relativeFrobeniusIsogeny p W) = φ := by
    intro g hg χ hd h
    subst hg
    exact ⟨χ, exists_comp_eq_id_and_comp_eq_id_of_degree_eq_one χ hd, h⟩
  have hs : φ.separableDegree = 1 := separableDegree_eq_one_of_isPurelyInseparable φ
  have hr : φ.inseparableDegree = p ^ 1 := by
    have h := separableDegree_mul_inseparableDegree φ
    rw [hs, hdeg, one_mul] at h
    rw [pow_one, h]
  obtain ⟨χ, hχ, -⟩ := existsUnique_comp_iterateRelativeFrobeniusIsogeny_eq p φ hr
  haveI := isSeparable_of_comp_iterateRelativeFrobeniusIsogeny_eq hr hχ
  have hd : χ.degree = 1 := by
    rw [degree_eq_separableDegree_of_comp_iterateRelativeFrobeniusIsogeny_eq hχ, hs]
  rw [iterateRelativeFrobeniusIsogeny_one] at hχ
  exact main _ (iterateFrobenius_one (R := F) p).symm χ hd hχ

/-- **Remark 12.24** (Milne; Silverman II.4.2(c)): an isogeny is separable if and only if it is nonzero on invariant
differentials (the transpose of the map on tangent spaces, Remark 11.6). Tau Ceti's
`Isogeny.isSeparable_iff_pullbackDifferential_ne_zero`. -/
@[kb "milne2017mf" "Section 12, Rem. 12.24 (pdf p. 128)"]
theorem isSeparable_iff_pullback_invariantDifferential_ne_zero {W₁ W₂ : WeierstrassCurve.Affine F}
    [W₁.IsElliptic] [W₂.IsElliptic] (φ : Isogeny W₁ W₂) :
    Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField ↔
      φ.pullbackDifferential (WeierstrassCurve.Affine.invariantDifferential W₂) ≠ 0 :=
  φ.isSeparable_iff_pullbackDifferential_ne_zero

end Frobenius

end ModularFormsKB.Milne
