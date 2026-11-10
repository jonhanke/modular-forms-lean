import ModularFormsKB.Milne.Ch12.Corrected
import ModularFormsKB.Milne.Wave4B.IsogenyDescent
import ModularFormsKB.Milne.Wave4B.TateFreeAlgebra

/-!
# Milne, Remark 12.12 (corrected): $T_\ell E$ is free of rank one over $R \otimes \mathbb Z_\ell$

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, Remark 12.12
(pdf p. 125), in the corrected form `SerreTateFreeTateModuleQuadratic` (`ModularFormsKB/Milne/Ch12/Corrected.lean`):
for an elliptic curve $E$ over a field $k$ with complex multiplication $i\colon R \cong \mathrm{End}_k(E)$ by an order
$R = \mathbb Z + \mathbb Z\omega$ of a quadratic field, and a prime $\ell$ invertible in $k$, some $t \in T_\ell E$
makes $t, \omega t$ a $\mathbb Z_\ell$-basis of $T_\ell E$. Milne cites Serre–Tate (1968, p. 502).

## Proof (Serre–Tate's argument)
1. $\omega$ does not act on $E[\ell]$ as an integer $c$. Otherwise $\omega - c$ and $\omega - c - \ell$ both kill
   $E[\ell]$; one of them, call it $\varphi$, is separable (their difference $\ell$ pulls the invariant differential
   back to $\ell\,\omega_E \neq 0$). By the factorisation theorem with descent (`exists_eq_zsmul_of_torsion`),
   $\varphi = \ell\psi$ with $\psi \in \mathrm{End}_k(E) = R$, i.e. $\omega - c' = \ell(a + b\omega)$; comparing
   coefficients, $\omega$ would be rational, while $R$ spans the quadratic field $K$.
2. Hence $E[\ell]$ (a group of order $\ell^2$ killed by $\ell$) has a cyclic vector $P$ for $\omega$
   (`exists_cyclic_of_ne_smul`): $E[\ell] = \mathbb Z P + \mathbb Z\,\omega P$.
3. Lift $P$ to $t \in T_\ell E$. Then $t, \omega t$ span $T_\ell E$ modulo $\ell T_\ell E$ (the kernel of
   $T_\ell E \to E[\ell]$), so by Nakayama they are a basis of the free rank-two module $T_\ell E$
   (`basis_of_forall_mod`).

## Main result
* `serreTateFreeTateModuleQuadratic : SerreTateFreeTateModuleQuadratic`.
-/

open NumberField TauCeti TauCeti.Isogeny TauCeti.GlobalNumberFields WeierstrassCurve.Affine
open scoped WeierstrassCurve Classical

namespace ModularFormsKB.Milne.Wave4B

open ModularFormsKB.Milne

section Rational

variable {K : Type} [Field K] [NumberField K] {O : NumberFieldOrder K}

/-- In an order of a quadratic field, an element generating it together with $1$ is not rational. -/
theorem not_rational_of_generates (hK : Module.finrank ℚ K = 2) (ω : O.toSubalgebra)
    (hω : ∀ x : O.toSubalgebra, ∃ a b : ℤ, x = a + b * ω) (q : ℚ) :
    (ω : K) ≠ algebraMap ℚ K q := by
  intro hq
  have hsub : (O.toSubalgebra : Set K) ⊆ Set.range (algebraMap ℚ K) := by
    intro x hx
    obtain ⟨a, b, hab⟩ := hω ⟨x, hx⟩
    have : x = (a : K) + b * (ω : K) := by simpa using congrArg Subtype.val hab
    exact ⟨a + b * q, by rw [this, hq, map_add, map_mul, map_intCast, map_intCast]⟩
  have hspan : Submodule.span ℚ (O.toSubalgebra : Set K) ≤ Submodule.span ℚ {(1 : K)} := by
    refine Submodule.span_le.2 fun x hx ↦ ?_
    obtain ⟨r, rfl⟩ := hsub hx
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r (Submodule.subset_span rfl)
  rw [O.spans] at hspan
  have h1 := Submodule.finrank_mono hspan
  rw [finrank_top, finrank_span_singleton one_ne_zero, hK] at h1
  omega

end Rational

section Main

variable {k : Type} [Field k] (W : WeierstrassCurve k) [W.IsElliptic] (Ks : Type) [Field Ks] [IsSepClosed Ks]
  [Algebra k Ks] (ℓ : ℕ) [hℓp : Fact ℓ.Prime]

/-- **Step 1.** $\omega$ does not act on $E[\ell]$ as an integer $c$: otherwise $\omega - c'$ (for $c' = c$ or
$c + \ell$, whichever is separable) kills $E[\ell]$, hence equals $\ell\psi$ with $\psi \in \mathrm{End}_k(E) = R$, which
makes $\omega$ rational. -/
theorem not_forall_torsion_eq_zsmul (hℓ : (ℓ : Ks) ≠ 0) {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) {O : NumberFieldOrder K} (i : O.toSubalgebra ≃+* Hom W.toAffine W.toAffine)
    (ω : O.toSubalgebra) (hω : ∀ x : O.toSubalgebra, ∃ a b : ℤ, x = a + b * ω) (c : ℤ)
    (hact : ∀ P : (W.toAffine.map (algebraMap k Ks)).Point, (ℓ : ℤ) • P = 0 →
      ((i ω).map (algebraMap k Ks)).pointMap P = c • P) : False := by
  set f := algebraMap k Ks
  have hℓK : ((ℓ : ℤ) : Ks) ≠ 0 := by exact_mod_cast hℓ
  have hkill : ∀ c' : ℤ, (∃ m : ℤ, c' = c + m * ℓ) → ∀ P : (W.toAffine.map f).Point, (ℓ : ℤ) • P = 0 →
      ((i ω - c' • Hom.id W.toAffine).map f).pointMap P = 0 := by
    rintro c' ⟨m, rfl⟩ P hP
    rw [Hom.map_sub, Hom.map_zsmul, Hom.id_map, Hom.sub_pointMap, Hom.zsmul_pointMap, Hom.id_pointMap,
      hact P hP, add_smul, mul_smul, hP, smul_zero, add_zero, sub_self]
  -- one of `ω - c`, `ω - (c + ℓ)` is separable
  obtain ⟨c', hc', hsep⟩ : ∃ c' : ℤ, (∃ m : ℤ, c' = c + m * ℓ) ∧
      (i ω - c' • Hom.id W.toAffine).pullbackDifferential (invariantDifferential W.toAffine) ≠ 0 := by
    by_contra hno
    push Not at hno
    have h1 := hno c ⟨0, by ring⟩
    have h2 := hno (c + ℓ) ⟨1, by ring⟩
    have h3 := Hom.pullbackDifferential_sub_invariantDifferential (i ω - c • Hom.id W.toAffine)
      (i ω - (c + ℓ) • Hom.id W.toAffine)
    have hdiff : (i ω - c • Hom.id W.toAffine) - (i ω - (c + ℓ) • Hom.id W.toAffine) =
        (ℓ : ℤ) • Hom.id W.toAffine := by
      rw [add_smul]; abel
    rw [h1, h2, sub_zero, hdiff, Hom.pullbackDifferential_zsmul_id_invariantDifferential] at h3
    have h4 := (zsmul_invariantDifferential_eq_zero_iff W.toAffine (ℓ : ℤ)).1 h3
    apply hℓ
    have h5 : ((ℓ : ℤ) : Ks) = f ((ℓ : ℤ) : k) := by simp
    exact_mod_cast h5.trans (by rw [h4, map_zero])
  obtain ⟨ψ, hψ⟩ := exists_eq_zsmul_of_torsion f hℓK _ hsep (hkill c' hc')
  obtain ⟨x, rfl⟩ := i.surjective ψ
  have hO : ω - (c' : O.toSubalgebra) = (ℓ : ℤ) • x := by
    apply i.injective
    rw [map_sub, map_zsmul, ← hψ, map_intCast, ← zsmul_one, Hom.one_def]
  obtain ⟨a, b, rfl⟩ := hω x
  have hK' : ((1 - ℓ * b : ℤ) : K) * (ω : K) = ((c' + ℓ * a : ℤ) : K) := by
    have := congrArg (fun y : O.toSubalgebra ↦ (y : K)) hO
    simp only [Subalgebra.coe_sub, SubringClass.coe_intCast, Subalgebra.coe_add,
      Subalgebra.coe_mul, zsmul_eq_mul] at this
    push_cast at this ⊢
    linear_combination this
  have hne : (1 - ℓ * b : ℤ) ≠ 0 := by
    intro h0
    have h2 := hℓp.out.two_le
    have hd : (ℓ : ℤ) ∣ 1 := ⟨b, by linarith⟩
    have := Int.eq_one_of_dvd_one (by positivity) hd
    omega
  have hneK : ((1 - ℓ * b : ℤ) : K) ≠ 0 := by exact_mod_cast hne
  apply not_rational_of_generates hK ω hω ((c' + ℓ * a : ℤ) / (1 - ℓ * b : ℤ) : ℚ)
  rw [map_div₀, map_intCast, map_intCast, eq_div_iff hneK, mul_comm]
  exact hK'

/-- **Remark 12.12, corrected** (Milne; Serre–Tate 1968, p. 502), proved: for an order $R = \mathbb Z + \mathbb Z\omega$
of a quadratic field with $R \cong \mathrm{End}_k(E)$ and $\ell$ invertible, $T_\ell E$ is free of rank one over
$R \otimes \mathbb Z_\ell$, generated by some $t$: $t, \omega t$ is a $\mathbb Z_\ell$-basis. -/
@[kb "milne2017mf" "Section 12, Rem. 12.12 (pdf p. 125), corrected; proved"]
theorem serreTateFreeTateModuleQuadratic : SerreTateFreeTateModuleQuadratic := by
  constructor
  intro k _ W _ Ks _ _ _ ℓ hℓp hℓ K _ _ hK O i ω hω
  set f := algebraMap k Ks
  set E := (W⁄Ks).toAffine.Point
  set A := TateModuleLevel ℓ E 1
  set g₀ : Hom (W⁄Ks).toAffine (W⁄Ks).toAffine := (i ω).map f
  have hmemA : ∀ P : E, P ∈ AddSubgroup.torsionBy E ((ℓ ^ 1 : ℕ) : ℤ) ↔ (ℓ : ℤ) • P = 0 := by
    intro P; simp [Submodule.mem_torsionBy_iff]
  let g : A →+ A := (g₀.pointMapHom.comp (AddSubgroup.torsionBy E ((ℓ ^ 1 : ℕ) : ℤ)).subtype).codRestrict
      (AddSubgroup.torsionBy E ((ℓ ^ 1 : ℕ) : ℤ)) fun a ↦ by
    rw [hmemA]
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddSubgroup.coe_subtype, Hom.pointMapHom_apply]
    rw [← Hom.pointMap_zsmul, (hmemA _).1 a.2, Hom.pointMap_zero]
  have hA : ∀ a : A, ℓ • a = 0 := fun a ↦ Subtype.ext (by
    rw [AddSubgroup.coe_nsmul, ZeroMemClass.coe_zero, ← natCast_zsmul]
    exact (hmemA _).1 a.2)
  have hcardA : Nat.card A = ℓ ^ 2 := by
    have := (W⁄Ks).natCard_tateModuleLevel hℓ 1
    simpa using this
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcardA]; exact pow_ne_zero _ hℓp.out.ne_zero)
  -- Step 1
  have hstep1 : ∀ c : ℤ, ∃ a : A, g a ≠ c • a := by
    intro c
    by_contra hall
    push Not at hall
    refine not_forall_torsion_eq_zsmul W Ks ℓ hℓ hK i ω hω c fun P hP ↦ ?_
    have := congrArg Subtype.val (hall ⟨P, (hmemA P).2 hP⟩)
    rw [AddSubgroup.coe_zsmul] at this
    exact (Hom.pointMapHom_apply _ _).symm.trans this
  -- Step 2: a cyclic vector
  obtain ⟨P, hP⟩ := exists_cyclic_of_ne_smul hA hcardA g hstep1
  -- Step 3: lift and apply Nakayama
  have := (W⁄Ks).free_tateModule hℓ
  have := (W⁄Ks).finite_tateModule hℓ
  have hsurj := TateModule.proj_surjective (p := ℓ) (A := E)
    (TateModule.tateModuleTransition_surjective_of_natCard (r := 2) hℓp.out.ne_zero
      ((W⁄Ks).natCard_tateModuleLevel hℓ)) 1
  obtain ⟨t, ht⟩ := hsurj P
  refine ⟨t, basis_of_forall_mod ((W⁄Ks).finrank_tateModule hℓ) t _ fun x ↦ ?_⟩
  obtain ⟨a, b, hab⟩ := hP (TateModule.proj 1 x)
  have hu : TateModule.proj 1 (cmAction W Ks ℓ i ω t) = g P := by
    apply Subtype.ext
    change g₀.pointMap (TateModule.proj 1 t : E) = _
    rw [ht]
    exact (Hom.pointMapHom_apply _ _).symm
  have h0 : TateModule.proj 1 (x - (a • t + b • cmAction W Ks ℓ i ω t)) = 0 := by
    rw [map_sub, map_add, map_zsmul, map_zsmul, ht, hu, hab, sub_self]
  obtain ⟨y, hy⟩ := TateModule.proj_eq_zero_iff.1 h0
  refine ⟨a, b, y, ?_⟩
  rw [pow_one] at hy
  rw [← sub_eq_iff_eq_add', hy]

end Main

end ModularFormsKB.Milne.Wave4B
