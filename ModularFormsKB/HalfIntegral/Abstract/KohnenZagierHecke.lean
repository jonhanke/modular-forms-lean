/-
# `KohnenAdjointHecke` from two Hecke adjointness statements

For the theta multiplier. Let $D$ be admissible and $\mathcal S_D^*$
an adjoint (`KohnenAdjoint`). The adjoint is Hecke equivariant, $T(p^2)\mathcal S_D^* = \mathcal S_D^*T(p)$, by this argument
(Kohnen–Zagier 1981 §2 [unverified]). For $g' \in S^+$ with $g'' \leftrightarrow T(p^2)g'$, and $G_1 = \mathcal S_Dg'$:
$$\langle g', T(p^2)\mathcal S_D^*F\rangle = \langle T(p^2)g', \mathcal S_D^*F\rangle = \langle T(p)G_1, F\rangle
  = \langle G_1, T(p)F\rangle = b(p)\langle G_1, F\rangle = b(p)\langle g', \mathcal S_D^*F\rangle,$$
using, in order, that $T(p^2)$ is self-adjoint on $S^+$ (`PlusHeckeSelfAdjoint`), the adjoint property for the form $g''$
and $\mathcal S_D T(p^2) = T(p)\mathcal S_D$ (`kohnenLiftCoeff_heckeT_of_fundamental`), that $T(p)$ is self-adjoint on level one
(`LevelOneHeckeSelfAdjoint`), the eigen property of $F$, and the adjoint property again. Hence
$T(p^2)\mathcal S_D^*F - b(p)\mathcal S_D^*F$ is orthogonal to $S^+$, so zero by definiteness
(`kohnenAdjointHecke_of_adjoint`).

**The two named inputs.** `PlusHeckeSelfAdjoint` is not proved here (the route to Kohnen's
isomorphism goes through traces instead); `LevelOneHeckeSelfAdjoint` is Tau Ceti's `isAdjointPair_heckeTCuspNat` at level one
(the bridge between `heckeTCuspLevelOne`, `peterssonOne` and the cosets of `peterssonInnerCosets` is not written). Both are
loose ends.
-/
import ModularFormsKB.HalfIntegral.Abstract.KohnenZagierEigen
import ModularFormsKB.HalfIntegral.HeckeOperator

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup UpperHalfPlane ModularForm HeckeRing.GL2 TauCeti
open scoped Real ComplexConjugate

/-- **$T(p^2)$, $p$ odd, is self-adjoint on Kohnen's plus space** for the Petersson product of `peterssonFour` (Shimura
1973 `shimura1973`, §1 [unverified]; Kohnen 1980 `kohnen1980`, §1). Stated on $q$-expansions: if $g_1, g_2, g_1', g_2' \in S^+$
and $g_i'$ has the coefficients `heckeT k 1 1 p` of those of $g_i$, then $\langle g_1', g_2\rangle = \langle g_1, g_2'\rangle$. -/
@[kb "shimura1973" "T(p²), p odd, is self-adjoint on S⁺_{k+1/2}(4) for the Petersson product [unverified]"]
structure PlusHeckeSelfAdjoint (k : ℕ) : Prop where
  selfAdjoint : ∀ {p : ℕ}, p.Prime → p ≠ 2 → ∀ (g₁ g₂ g₁' g₂' : ℍ → ℂ) (c₁ c₂ : ℕ → ℂ),
    g₁ ∈ thetaMultiplierSystem.plusCuspForms k 1 1 → g₂ ∈ thetaMultiplierSystem.plusCuspForms k 1 1 →
    g₁' ∈ thetaMultiplierSystem.plusCuspForms k 1 1 → g₂' ∈ thetaMultiplierSystem.plusCuspForms k 1 1 →
    Abstract.HasQExp g₁ c₁ → Abstract.HasQExp g₂ c₂ → Abstract.HasQExp g₁' (heckeT k 1 1 p c₁) →
    Abstract.HasQExp g₂' (heckeT k 1 1 p c₂) → peterssonFour k g₁' g₂ = peterssonFour k g₁ g₂'

/-- **$T(p)$ is self-adjoint on $S_{2k}(\mathrm{SL}_2(\mathbb Z))$** for `peterssonOne` (Tau Ceti
`TauCeti.HeckeRing.GL2.isAdjointPair_heckeTCuspNat` for $\Gamma_1(1)$; Miyake Theorem 4.5.4 [unverified]). -/
@[kb "miyake1989" "T(p) is self-adjoint on S_{2k}(SL₂(ℤ)) for the Petersson product [unverified]"]
structure LevelOneHeckeSelfAdjoint (k : ℕ) : Prop where
  selfAdjoint : ∀ (p : ℕ) [NeZero p], p.Prime → ∀ F G : CuspForm 𝒮ℒ (2 * k : ℕ),
    peterssonOne k (heckeTCuspLevelOne ((2 * k : ℕ) : ℤ) p F) G =
      peterssonOne k F (heckeTCuspLevelOne ((2 * k : ℕ) : ℤ) p G)

/-- **$T(p^2)$ preserves $S^+$ and acts on $q$-expansions by `heckeT`** (theta multiplier, $p$ odd). -/
theorem plus_heckeStable (k : ℕ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {g : ℍ → ℂ}
    (hg : g ∈ thetaMultiplierSystem.plusCuspForms k 1 1) {c : ℕ → ℂ} (hc : Abstract.HasQExp g c) :
    ∃ g' ∈ thetaMultiplierSystem.plusCuspForms k 1 1, Abstract.HasQExp g' (heckeT k 1 1 p c) := by
  obtain ⟨hcusp, a, ha, hpl⟩ := hg
  have hnd : ¬ p ∣ 4 * 1 := by
    intro h
    have h4 : p ∣ 2 ^ 2 := by simpa using h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
  have hac : a = c := Abstract.hasQExp_unique ha hc
  subst hac
  exact ⟨_, ⟨(heckeOpCusp k 1 1 hp hnd ⟨g, hcusp⟩).2, heckeT k 1 1 p a,
    hasQExp_heckeOpCusp k 1 1 hp hnd ⟨g, hcusp⟩ ha, heckeT_plus 1 hp hp2 hpl⟩,
    hasQExp_heckeOpCusp k 1 1 hp hnd ⟨g, hcusp⟩ ha⟩

/-- **Row 21: `KohnenAdjointHecke` from the adjointness statements.** -/
theorem kohnenAdjointHecke_of_adjoint (k : ℕ) (hk : 1 ≤ k) {D : ℤ} (hD : KohnenDisc k D) (hL : KohnenDLift thetaMultiplierSystem k D)
    (hS : PlusHeckeSelfAdjoint k) (hO : LevelOneHeckeSelfAdjoint k)
    {Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ} (hadj : KohnenAdjoint thetaMultiplierSystem k D Sstar) :
    KohnenAdjointHecke thetaMultiplierSystem k Sstar := by
  refine ⟨fun F b hFb heig c' hc' p hp hp2 ↦ ?_⟩
  set θ := thetaMultiplierSystem
  have hh : Sstar F ∈ θ.plusCuspForms k 1 1 := hadj.mem_plus F
  obtain ⟨h', hh', hch'⟩ := plus_heckeStable k hp hp2 hh hc'
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hTF : heckeTCuspLevelOne ((2 * k : ℕ) : ℤ) p F = b p • F :=
    heckeTCuspLevelOne_eq_smul (2 * k) hp F hFb (heig p hp)
  -- the key identity: ⟨g', h'⟩ = b p ⟨g', h⟩ for all g' ∈ S⁺
  have key : ∀ g' ∈ θ.plusCuspForms k 1 1, peterssonFour k g' h' = b p * peterssonFour k g' (Sstar F) := by
    intro g' hg'
    obtain ⟨a, ha⟩ := exists_hasQExp_plus (⟨g', hg'⟩ : θ.plusCuspForms k 1 1)
    obtain ⟨g'', hg'', hcg''⟩ := plus_heckeStable k hp hp2 hg' ha
    obtain ⟨G₁, hG₁⟩ := hL.lift hk g' hg' a ha
    have e1 := hS.selfAdjoint hp hp2 g' (Sstar F) g'' h' a c' hg' hh hg'' hh' ha hc' hcg'' hch'
    have e2 := hadj.adjoint g'' hg'' (heckeT k 1 1 p a) hcg'' (heckeTCuspLevelOne ((2 * k : ℕ) : ℤ) p G₁)
      (heckeTInt (2 * k) 1 1 p (kohnenLiftCoeff k D a)) (hasQExp_heckeTCuspLevelOne (2 * k) hp G₁ hG₁)
      (fun n _ ↦ by rw [← kohnenLiftCoeff_heckeT_of_fundamental k hD.1 hD.2 hp hp2 a]; rfl) F
    have e3 := hadj.adjoint g' hg' a ha G₁ (kohnenLiftCoeff k D a) hG₁ (fun n _ ↦ rfl) F
    have hsm : ((b p • F : CuspForm 𝒮ℒ (2 * k : ℕ)) : ℍ → ℂ) = b p • ⇑F := rfl
    rw [← e1, ← e2, hO.selfAdjoint p hp G₁ F, hTF, hsm, ← e3]
    simp only [peterssonOne]
    exact peterssonReps_smul_right _ _ _ _ _
  -- orthogonality to S⁺ forces equality
  letI : NormedAddCommGroup (θ.plusCuspForms k 1 1) := (plusInnerCore θ k).toNormedAddCommGroup
  letI : InnerProductSpace ℂ (θ.plusCuspForms k 1 1) := InnerProductSpace.ofCore (plusInnerCore θ k).toCore
  set x : θ.plusCuspForms k 1 1 := ⟨h', hh'⟩
  set y : θ.plusCuspForms k 1 1 := ⟨Sstar F, hh⟩
  have hd : inner ℂ (x - b p • y) (x - b p • y) = 0 := by
    rw [inner_sub_right, inner_smul_right]
    have := key _ (x - b p • y).2
    exact sub_eq_zero.2 this
  have hxy : x = b p • y := sub_eq_zero.1 (inner_self_eq_zero.1 hd)
  have hfun : h' = b p • Sstar F := congrArg Subtype.val hxy
  have hc2 : Abstract.HasQExp h' (b p • c') := by
    rw [hfun]; exact Abstract.hasQExp_smul (b p) hc'
  exact Abstract.hasQExp_unique hch' hc2

end ModularFormsKB.HalfIntegral
