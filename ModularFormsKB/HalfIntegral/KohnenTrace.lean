/-
# Kohnen's trace identity, and what follows from it

**The named input** `KohnenTraceIdentity k` (Kohnen 1980 `kohnen1980`, §2–§4 [unverified]): the Hecke modules
$S^+_{k+1/2}(4)$ and $S_{2k}(\mathrm{SL}_2(\mathbb Z))$ have the same traces, $T(p^2) \leftrightarrow T(p)$ for odd
primes $p$ and $T^+(4) \leftrightarrow T(2)$. It is stated for finite products of these operators (lists of primes),
which by linearity is the same as equality of the traces of every element of the two Hecke algebras. Kohnen states the
identity as $\operatorname{tr}T^+(n^2) = \operatorname{tr}T(n)$ for all $n \ge 1$; the two forms are equivalent because
on both sides $T(n)$ (resp. $T^+(n^2)$) is a polynomial in the prime operators with the same recursions. The field
`trace_all` is stated for every operator `T4` acting on $q$-expansions by Kohnen's formula `heckeTPlusFour`; such an
operator exists (and is unique) when `KohnenTPlusFourStable` holds (`exists_isTPlusFour`).

**Proved here from the trace identity** (the linear algebra is `jointEigen_of_trace_eq`; the level one side is Tau
Ceti's newform basis with strong multiplicity one, `KohnenLevelOne.lean`):
- `kohnenDimensionLe_of_trace`: $\dim S_{2k}(1) \le \dim S^+_{k+1/2}(4)$ (the empty product; in fact equality,
  `finrank_plusSpace_eq_of_trace`);
- `kohnenPlusMultOne_of_trace` (row 18): multiplicity one in the plus space;
- `kohnenPlusEigenbasis_of_trace` (row 16): $S^+_{k+1/2}(4)$ has a basis of eigenforms of the odd $T(p^2)$. No
  Petersson product is needed: every joint generalized eigenspace has dimension at most one.
- `kohnenDLift_of_trace` (row 17): with `KohnenTPlusFourStable`, the $D$-th lift maps $S^+_{k+1/2}(4)$ into
  $S_{2k}(1)$ for every fundamental $D$ with $(-1)^kD > 0$. This is Kohnen's argument: for an eigenform $g$ of all
  $T(p^2)$ and of $T^+(4)$, with eigenvalue system $\nu$, the trace identity gives a level one newform $F$ with the same
  eigenvalues; the lift of $g$ is an eigen-sequence of every $T(p)$ (`kohnenLiftCoeff_heckeT_of_fundamental`,
  `kohnenLiftCoeff_heckeTPlusFour`) with first coefficient $c(|D|)$, hence equals $c(|D|)$ times the coefficients of
  $F$ (`eq_zero_of_heckeTInt_eigen`); eigenforms span the plus space. Shimura's theorem is not used.
- `kohnenIsomorphism_of_trace` (row 19, **H2**): Kohnen's isomorphism for the theta multiplier from
  `KohnenTraceIdentity` and `KohnenTPlusFourStable`; `kohnenIsomorphism_of_dLift_trace`: from `KohnenDLift`,
  `KohnenTraceIdentity` and `KohnenTPlusFourStable`.
-/
import ModularFormsKB.HalfIntegral.KohnenTraceAlgebra
import ModularFormsKB.HalfIntegral.KohnenLevelOne
import ModularFormsKB.HalfIntegral.KohnenTwoLift
import ModularFormsKB.HalfIntegral.KohnenFinite

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups ModularForm

local notation "ℍ" => UpperHalfPlane

/-- **Kohnen's trace identity** (Kohnen 1980 `kohnen1980`, §2–§4 [unverified]): for $k \ge 1$, the traces of every
finite product of the Hecke operators agree on $S^+_{k+1/2}(4)$ and on $S_{2k}(\mathrm{SL}_2(\mathbb Z))$, with
$T(p^2) \leftrightarrow T(p)$ for odd primes $p$ (`trace_odd`), and, including $p = 2$, with $T^+(4) \leftrightarrow T(2)$
for the operator `T4` acting on $q$-expansions by Kohnen's formula (`trace_all`). -/
@[kb "kohnen1980" "tr T⁺(n²) on S⁺_{k+1/2}(4) = tr T(n) on S_{2k}(1), here for products of prime Hecke operators [unverified]"]
structure KohnenTraceIdentity (k : ℕ) : Prop where
  trace_odd : 1 ≤ k → ∀ l : List OddPrime,
    LinearMap.trace ℂ (PlusSpace k) (l.map (plusHeckeOdd k)).prod =
      LinearMap.trace ℂ (CuspForm 𝒮ℒ (2 * k : ℕ)) (l.map (levelOneHeckeOdd k)).prod
  trace_all : 1 ≤ k → ∀ T4 : Module.End ℂ (PlusSpace k), IsTPlusFour k T4 → ∀ l : List Nat.Primes,
    LinearMap.trace ℂ (PlusSpace k) (l.map (plusHeckeAll k T4)).prod =
      LinearMap.trace ℂ (CuspForm 𝒮ℒ (2 * k : ℕ)) (l.map (levelOneHecke k)).prod

variable {k : ℕ}

/-! ### The algebra applied to the odd primes -/

private theorem odd_joint (h : KohnenTraceIdentity k) (hk : 1 ≤ k) :
    (∀ (ν : OddPrime → ℂ) (v w : PlusSpace k), IsJointEigenvector (plusHeckeOdd k) ν v →
        IsJointEigenvector (plusHeckeOdd k) ν w → v ≠ 0 → ∃ t : ℂ, w = t • v) ∧
    (∀ (ν : OddPrime → ℂ) (v : PlusSpace k), IsJointEigenvector (plusHeckeOdd k) ν v → v ≠ 0 →
        ∃ f, (fun p : OddPrime ↦ levelOneEigenvalue k f p.1) = ν) ∧
    Submodule.span ℂ {v : PlusSpace k | ∃ ν, IsJointEigenvector (plusHeckeOdd k) ν v} = ⊤ :=
  jointEigen_of_trace_eq (plusHeckeOdd k) (levelOneHeckeOdd k) (plusHeckeOdd_commute k) (h.trace_odd hk)
    (TauCeti.levelOneNewformBasis _) (fun f p ↦ levelOneEigenvalue k f p.1)
    (fun f p ↦ levelOneHecke_basis k p.1 f) (levelOneEigenvalue_odd_injective k)

/-- **The dimensions agree:** $\dim S^+_{k+1/2}(4) = \dim S_{2k}(1)$, from the trace of the identity. -/
theorem finrank_plusSpace_eq_of_trace (h : KohnenTraceIdentity k) (hk : 1 ≤ k) :
    Module.finrank ℂ (PlusSpace k) = Module.finrank ℂ (CuspForm 𝒮ℒ (2 * k : ℕ)) := by
  have h0 := h.trace_odd hk []
  simp only [List.map_nil, List.prod_nil, LinearMap.trace_one] at h0
  exact_mod_cast h0

/-- **`KohnenDimensionLe` from the trace identity** (row 18). -/
theorem kohnenDimensionLe_of_trace (h : KohnenTraceIdentity k) : KohnenDimensionLe thetaMultiplierSystem k :=
  ⟨fun hk ↦ (finrank_plusSpace_eq_of_trace h hk).ge⟩

/-- An eigenform of the odd $T(p^2)$ is a joint eigenvector of `plusHeckeOdd`. -/
private theorem isJointEigenvector_of_isPlusEigenform {g : ℍ → ℂ} {μ : ℕ → ℂ}
    (hg : IsPlusEigenform thetaMultiplierSystem k g μ) :
    IsJointEigenvector (plusHeckeOdd k) (fun p ↦ μ p.1) (⟨g, hg.1⟩ : PlusSpace k) := by
  obtain ⟨hplus, c, hc, heig⟩ := hg
  intro p
  have h1 := hasQExp_plusHecke k p.1.2 p.2 ⟨g, hplus⟩ hc
  rw [heig p.1 p.1.2 p.2] at h1
  exact plusSpace_ext_of_hasQExp h1 (Abstract.hasQExp_smul _ hc)

/-- **Multiplicity one in the plus space from the trace identity** (row 18). -/
theorem kohnenPlusMultOne_of_trace (h : KohnenTraceIdentity k) : KohnenPlusMultOne thetaMultiplierSystem k := by
  refine ⟨fun hk g g' μ hg hg' hne ↦ ?_⟩
  obtain ⟨t, ht⟩ := (odd_joint h hk).1 _ _ _ (isJointEigenvector_of_isPlusEigenform hg)
    (isJointEigenvector_of_isPlusEigenform hg') (fun h0 ↦ hne (congrArg Subtype.val h0))
  exact ⟨t, congrArg Subtype.val ht⟩

/-- A joint eigenvector of `plusHeckeOdd` is an eigenform, with the eigenvalues extended by $0$. -/
private theorem isPlusEigenform_of_isJointEigenvector {v : PlusSpace k} {ν : OddPrime → ℂ}
    (hv : IsJointEigenvector (plusHeckeOdd k) ν v) :
    IsPlusEigenform thetaMultiplierSystem k v
      (fun p ↦ if hp : p.Prime ∧ p ≠ 2 then ν ⟨⟨p, hp.1⟩, hp.2⟩ else 0) := by
  obtain ⟨c, hc⟩ := plusSpace_exists_hasQExp v
  refine ⟨v.2, c, hc, fun p hp hp2 ↦ ?_⟩
  have h1 := hasQExp_plusHecke k hp hp2 v hc
  have h2 := hv ⟨⟨p, hp⟩, hp2⟩
  have e : plusHeckeOdd k ⟨⟨p, hp⟩, hp2⟩ = plusHecke k hp hp2 := rfl
  rw [e] at h2
  rw [h2] at h1
  show _ = (if hp' : p.Prime ∧ p ≠ 2 then ν ⟨⟨p, hp'.1⟩, hp'.2⟩ else 0) • c
  rw [dif_pos ⟨hp, hp2⟩]
  exact Abstract.hasQExp_unique h1 (Abstract.hasQExp_smul _ hc)

/-- **$S^+_{k+1/2}(4)$ has a basis of eigenforms, from the trace identity** (row 16). -/
theorem kohnenPlusEigenbasis_of_trace (h : KohnenTraceIdentity k) :
    KohnenPlusEigenbasis thetaMultiplierSystem k := by
  classical
  refine ⟨fun hk ↦ ?_⟩
  obtain ⟨-, -, hspan⟩ := odd_joint h hk
  set s : Set (PlusSpace k) := {v | ∃ ν, IsJointEigenvector (plusHeckeOdd k) ν v}
  obtain ⟨t, hts, htspan, hli⟩ := exists_linearIndependent ℂ s
  have htfin : t.Finite := hli.setFinite
  let e : Fin htfin.toFinset.card ≃ t :=
    (htfin.toFinset.equivFin.symm).trans (Equiv.subtypeEquivRight fun x ↦ htfin.mem_toFinset)
  have hsys : ∀ i : Fin htfin.toFinset.card, ∃ ν, IsJointEigenvector (plusHeckeOdd k) ν (e i : PlusSpace k) :=
    fun i ↦ hts (e i).2
  choose ν hν using hsys
  refine ⟨htfin.toFinset.card, fun i ↦ ((e i : PlusSpace k) : ℍ → ℂ),
    fun i p ↦ if hp : p.Prime ∧ p ≠ 2 then ν i ⟨⟨p, hp.1⟩, hp.2⟩ else 0,
    fun i ↦ isPlusEigenform_of_isJointEigenvector (hν i), ?_, ?_⟩
  · have hli' : LinearIndependent ℂ (fun i ↦ (e i : PlusSpace k)) :=
      hli.comp (fun i ↦ e i) e.injective
    exact hli'.map' (PlusSpace k).subtype (Submodule.ker_subtype _)
  · intro g hg
    have hmem : (⟨g, hg⟩ : PlusSpace k) ∈ Submodule.span ℂ t := by
      rw [htspan, hspan]; exact Submodule.mem_top
    have hrange : Set.range (fun i ↦ (e i : PlusSpace k)) = t := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩; exact (e i).2
      · intro hx; exact ⟨e.symm ⟨x, hx⟩, by simp⟩
    rw [← hrange] at hmem
    have := Submodule.mem_map_of_mem (f := (PlusSpace k).subtype) hmem
    rw [Submodule.map_span, ← Set.range_comp] at this
    exact this

/-! ### The algebra at all primes, and the $D$-th lift -/

private theorem all_joint (h : KohnenTraceIdentity k) (hk : 1 ≤ k) {T4 : Module.End ℂ (PlusSpace k)}
    (h4 : IsTPlusFour k T4) :
    (∀ (ν : Nat.Primes → ℂ) (v w : PlusSpace k), IsJointEigenvector (plusHeckeAll k T4) ν v →
        IsJointEigenvector (plusHeckeAll k T4) ν w → v ≠ 0 → ∃ t : ℂ, w = t • v) ∧
    (∀ (ν : Nat.Primes → ℂ) (v : PlusSpace k), IsJointEigenvector (plusHeckeAll k T4) ν v → v ≠ 0 →
        ∃ f, levelOneEigenvalue k f = ν) ∧
    Submodule.span ℂ {v : PlusSpace k | ∃ ν, IsJointEigenvector (plusHeckeAll k T4) ν v} = ⊤ :=
  jointEigen_of_trace_eq (plusHeckeAll k T4) (levelOneHecke k) (plusHeckeAll_commute k h4) (h.trace_all hk T4 h4)
    (TauCeti.levelOneNewformBasis _) (levelOneEigenvalue k) (fun f p ↦ levelOneHecke_basis k p f)
    (levelOneEigenvalue_injective k)

/-- The coefficients of a plus form satisfy the plus condition. -/
private theorem mem_plusSeq_of_hasQExp (g : PlusSpace k) {c : ℕ → ℂ} (hc : Abstract.HasQExp g c) :
    c ∈ plusSeq k := by
  obtain ⟨-, a, ha, hap⟩ := g.2
  rw [Abstract.hasQExp_unique hc ha]
  exact hap

/-- **The lift of a joint eigenvector is a level one cusp form.** -/
private theorem lift_of_joint (h : KohnenTraceIdentity k) (hk : 1 ≤ k) {T4 : Module.End ℂ (PlusSpace k)}
    (h4 : IsTPlusFour k T4) {D : ℤ} (hD : KohnenDisc k D) {g : PlusSpace k} {ν : Nat.Primes → ℂ}
    (hg : IsJointEigenvector (plusHeckeAll k T4) ν g) {c : ℕ → ℂ} (hc : Abstract.HasQExp g c) :
    ∃ F : CuspForm 𝒮ℒ (2 * k : ℕ), Abstract.HasQExp F (kohnenLiftCoeff k D c) := by
  by_cases hg0 : g = 0
  · subst hg0
    have hc0 : c = 0 := Abstract.hasQExp_unique hc Abstract.hasQExp_zero
    subst hc0
    refine ⟨0, ?_⟩
    have : kohnenLiftCoeff k D 0 = 0 := (kohnenLiftLin k D).map_zero
    rw [this]
    exact Abstract.hasQExp_zero
  obtain ⟨f, hf⟩ := (all_joint h hk h4).2.1 ν g hg hg0
  obtain ⟨a, ha, ha0, ha1, haeig⟩ := exists_hasQExp_levelOneNewformBasis k f
  have hplus := mem_plusSeq_of_hasQExp g hc
  -- the eigen relations of `c`
  have hodd : ∀ p : Nat.Primes, (p : ℕ) ≠ 2 → heckeT k 1 1 p c = ν p • c := by
    intro p hp2
    have h1 := hasQExp_plusHecke k p.2 hp2 g hc
    have h2 := hg p
    rw [plusHeckeAll_of_ne_two k T4 hp2] at h2
    rw [h2] at h1
    exact Abstract.hasQExp_unique h1 (Abstract.hasQExp_smul _ hc)
  have htwo : ∀ p : Nat.Primes, (p : ℕ) = 2 → heckeTPlusFour k c = ν p • c := by
    intro p hp2
    have h1 := h4 g c hc
    have h2 := hg p
    rw [plusHeckeAll_two k T4 hp2] at h2
    rw [h2] at h1
    exact Abstract.hasQExp_unique h1 (Abstract.hasQExp_smul _ hc)
  -- the lift is an eigen-sequence of every `T(p)`
  set b := kohnenLiftCoeff k D c with hb
  have hbeig : ∀ p : Nat.Primes, heckeTInt (2 * k) 1 1 p b = ν p • b := by
    intro p
    by_cases hp2 : (p : ℕ) = 2
    · have e := kohnenLiftCoeff_heckeTPlusFour k hD hplus
      rw [htwo p hp2, show kohnenLiftCoeff k D (ν p • c) = ν p • kohnenLiftCoeff k D c from
        (kohnenLiftLin k D).map_smul _ c] at e
      rw [hb, hp2, ← e]
    · have e := kohnenLiftCoeff_heckeT_of_fundamental k hD.1 hD.2 p.2 hp2 c
      rw [hodd p hp2, show kohnenLiftCoeff k D (ν p • c) = ν p • kohnenLiftCoeff k D c from
        (kohnenLiftLin k D).map_smul _ c] at e
      rw [hb, ← e]
  -- compare with `c(|D|)` times the newform
  refine ⟨c D.natAbs • TauCeti.levelOneNewformBasis _ f, ?_⟩
  have hdiff : ∀ n, b n = (c D.natAbs • a) n := by
    have hfν : levelOneEigenvalue k f = ν := hf
    set e : ℕ → ℂ := b - c D.natAbs • a with he
    have heeig : ∀ p : ℕ, p.Prime → heckeTInt (2 * k) 1 1 p e = (fun q ↦ if hq : q.Prime then ν ⟨q, hq⟩ else 0) p • e := by
      intro p hp
      show heckeTInt (2 * k) 1 1 p e = (if hq : p.Prime then ν ⟨p, hq⟩ else 0) • e
      rw [dif_pos hp]
      have h1 := hbeig ⟨p, hp⟩
      have h2 := haeig ⟨p, hp⟩
      rw [hfν] at h2
      have hlin : ∀ x, heckeTInt (2 * k) 1 1 p x = heckeTIntLin (2 * k) 1 1 p x := fun _ ↦ rfl
      rw [hlin, he, map_sub, map_smul, ← hlin, ← hlin]
      change heckeTInt (2 * k) 1 1 (⟨p, hp⟩ : Nat.Primes) b - _ = _
      rw [h1]
      change _ - c D.natAbs • heckeTInt (2 * k) 1 1 (⟨p, hp⟩ : Nat.Primes) a = _
      rw [h2, smul_sub, smul_comm]
    have he1 : e 1 = 0 := by
      simp [he, hb, kohnenLiftCoeff_one, ha1]
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hb, ha0]
    · have := eq_zero_of_heckeTInt_eigen _ heeig he1 n hn
      simpa [he, sub_eq_zero] using this
  have hfun : b = c D.natAbs • a := funext hdiff
  rw [hfun]
  exact Abstract.hasQExp_smul _ ha

/-- **The $D$-th lift lands in $S_{2k}(1)$, from the trace identity and $T^+(4)$** (row 17). -/
@[kb "kohnen1980" "Thm. 1: the D-th lift of a plus form has level one, from the Hecke module isomorphism [unverified]"]
theorem kohnenDLift_of_trace (h : KohnenTraceIdentity k) (hS : KohnenTPlusFourStable thetaMultiplierSystem k)
    {D : ℤ} (hD : KohnenDisc k D) : KohnenDLift thetaMultiplierSystem k D := by
  refine ⟨fun hk f hf a ha ↦ ?_⟩
  obtain ⟨T4, h4⟩ := exists_isTPlusFour hk hS
  obtain ⟨-, -, hspan⟩ := all_joint h hk h4
  -- the property "every coefficient sequence of `g` lifts to a level one cusp form" is closed under span
  let P : PlusSpace k → Prop := fun g ↦ ∀ c, Abstract.HasQExp g c →
    ∃ F : CuspForm 𝒮ℒ (2 * k : ℕ), Abstract.HasQExp F (kohnenLiftCoeff k D c)
  have hP : ∀ g : PlusSpace k, P g := by
    intro g
    have hg : g ∈ Submodule.span ℂ {v : PlusSpace k | ∃ ν, IsJointEigenvector (plusHeckeAll k T4) ν v} := by
      rw [hspan]; exact Submodule.mem_top
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ν, hν⟩ := hx
      exact fun c hc ↦ lift_of_joint h hk h4 hD hν hc
    | zero =>
      intro c hc
      have hc0 : c = 0 := Abstract.hasQExp_unique hc Abstract.hasQExp_zero
      subst hc0
      refine ⟨0, ?_⟩
      rw [show kohnenLiftCoeff k D 0 = 0 from (kohnenLiftLin k D).map_zero]
      exact Abstract.hasQExp_zero
    | add x y _ _ hx hy =>
      intro c hc
      obtain ⟨cx, hcx⟩ := plusSpace_exists_hasQExp x
      obtain ⟨cy, hcy⟩ := plusSpace_exists_hasQExp y
      obtain ⟨Fx, hFx⟩ := hx cx hcx
      obtain ⟨Fy, hFy⟩ := hy cy hcy
      have hsum : Abstract.HasQExp ((x + y : PlusSpace k) : ℍ → ℂ) (cx + cy) := Abstract.hasQExp_add hcx hcy
      rw [Abstract.hasQExp_unique hc hsum]
      refine ⟨Fx + Fy, ?_⟩
      rw [show kohnenLiftCoeff k D (cx + cy) = kohnenLiftCoeff k D cx + kohnenLiftCoeff k D cy from
        (kohnenLiftLin k D).map_add cx cy]
      exact Abstract.hasQExp_add hFx hFy
    | smul r x _ hx =>
      intro c hc
      obtain ⟨cx, hcx⟩ := plusSpace_exists_hasQExp x
      obtain ⟨Fx, hFx⟩ := hx cx hcx
      have hsm : Abstract.HasQExp ((r • x : PlusSpace k) : ℍ → ℂ) (r • cx) := Abstract.hasQExp_smul r hcx
      rw [Abstract.hasQExp_unique hc hsm]
      refine ⟨r • Fx, ?_⟩
      rw [show kohnenLiftCoeff k D (r • cx) = r • kohnenLiftCoeff k D cx from (kohnenLiftLin k D).map_smul r cx]
      exact Abstract.hasQExp_smul r hFx
  exact hP ⟨f, hf⟩ a ha

/-- **H2: Kohnen's isomorphism for the theta multiplier from the trace identity and $T^+(4)$** (row 19):
$S^+_{k+1/2}(4) \cong S_{2k}(\mathrm{SL}_2(\mathbb Z))$, compatibly with $T(p^2) \mapsto T(p)$ for odd $p$. -/
@[kb "kohnen1980" "Thm. 1 for the theta multiplier, from the trace identity and T⁺(4) [unverified]"]
theorem kohnenIsomorphism_of_trace (h : KohnenTraceIdentity k) (hS : KohnenTPlusFourStable thetaMultiplierSystem k) :
    KohnenIsomorphism thetaMultiplierSystem k :=
  kohnenIsomorphism_of_tPlusFour thetaMultiplierSystem k (fun _ hD ↦ kohnenDLift_of_trace h hS hD)
    (kohnenDimensionLe_of_trace h) (kohnenPlusEigenbasis_of_trace h) (kohnenPlusMultOne_of_trace h) hS

/-- **Kohnen's isomorphism from the $D$-th lifts, the trace identity and $T^+(4)$** (`kohnenIsomorphism_of_trace` shows that the lifts follow from the other two). -/
theorem kohnenIsomorphism_of_dLift_trace (hL : ∀ D, KohnenDisc k D → KohnenDLift thetaMultiplierSystem k D)
    (h : KohnenTraceIdentity k) (hS : KohnenTPlusFourStable thetaMultiplierSystem k) :
    KohnenIsomorphism thetaMultiplierSystem k :=
  kohnenIsomorphism_of_tPlusFour thetaMultiplierSystem k hL (kohnenDimensionLe_of_trace h)
    (kohnenPlusEigenbasis_of_trace h) (kohnenPlusMultOne_of_trace h) hS

end ModularFormsKB.HalfIntegral
