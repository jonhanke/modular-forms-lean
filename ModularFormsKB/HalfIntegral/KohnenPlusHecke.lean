/-
# The Hecke operators of the plus space as linear operators

For the theta multiplier, level $4$, trivial character, weight $k+\tfrac12$:
- `plusHecke k hp hp2`: Shimura's $T(p^2)$, $p$ an odd prime, restricted to Kohnen's plus space $S^+_{k+1/2}(4)$
  (`heckeOpCusp` preserves the plus space because Shimura's coefficient formula `heckeT` preserves the plus condition,
  `heckeT_plus`);
- `IsTPlusFour k T4`: an endomorphism $T_4$ of $S^+_{k+1/2}(4)$ acting on $q$-expansions by Kohnen's $T^+(4)$
  (`heckeTPlusFour`). Such a $T_4$ exists exactly when `KohnenTPlusFourStable` holds (`exists_isTPlusFour`), and it is
  then unique (`isTPlusFour_unique`);
- the families indexed by the odd primes (`plusHeckeOdd`) and by all primes (`plusHeckeAll k T4`, with $T_4$ at $2$).
All of these operators commute (`plusHeckeOdd_commute`, `plusHeckeAll_commute`).
-/
import ModularFormsKB.HalfIntegral.HeckeOperator
import ModularFormsKB.HalfIntegral.Abstract.KohnenTwo

namespace ModularFormsKB.HalfIntegral

open Complex

local notation "ℍ" => UpperHalfPlane

/-- **The odd primes**, as a subtype of Mathlib's `Nat.Primes`. -/
abbrev OddPrime := {p : Nat.Primes // (p : ℕ) ≠ 2}

/-- Kohnen's plus space $S^+_{k+1/2}(4)$ of the theta multiplier. -/
noncomputable abbrev PlusSpace (k : ℕ) := thetaMultiplierSystem.plusCuspForms k 1 1

theorem not_dvd_four_of_prime_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 4 * 1 := by
  intro h
  have h4 : p ∣ 2 ^ 2 := by simpa using h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))

/-- **$T(p^2)$ preserves the plus space**, $p$ an odd prime. -/
theorem heckeFun_mem_plus (k : ℕ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {g : ℍ → ℂ}
    (hg : g ∈ PlusSpace k) : heckeFun k 1 1 ⟨p, hp.pos⟩ g ∈ PlusSpace k := by
  obtain ⟨hc, a, ha, hpl⟩ := hg
  exact ⟨(heckeOpCusp k 1 1 hp (not_dvd_four_of_prime_ne_two hp hp2) ⟨g, hc⟩).2, heckeT k 1 1 p a,
    hasQExp_heckeOpCusp k 1 1 hp (not_dvd_four_of_prime_ne_two hp hp2) ⟨g, hc⟩ ha, heckeT_plus 1 hp hp2 hpl⟩

/-- **Shimura's $T(p^2)$ on $S^+_{k+1/2}(4)$**, $p$ an odd prime. -/
noncomputable def plusHecke (k : ℕ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : Module.End ℂ (PlusSpace k) where
  toFun g := ⟨heckeFun k 1 1 ⟨p, hp.pos⟩ g, heckeFun_mem_plus k hp hp2 g.2⟩
  map_add' f g := Subtype.ext (heckeFun_add k 1 1 _ f g)
  map_smul' c f := Subtype.ext (heckeFun_smul k 1 1 _ c f)

theorem coe_plusHecke (k : ℕ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (g : PlusSpace k) :
    ((plusHecke k hp hp2 g : PlusSpace k) : ℍ → ℂ) = heckeFun k 1 1 ⟨p, hp.pos⟩ g := rfl

/-- **$T(p^2)$ on the plus space acts on $q$-expansions by Shimura's formula.** -/
theorem hasQExp_plusHecke (k : ℕ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (g : PlusSpace k) {a : ℕ → ℂ}
    (ha : Abstract.HasQExp g a) : Abstract.HasQExp (plusHecke k hp hp2 g) (heckeT k 1 1 p a) :=
  hasQExp_heckeOpCusp k 1 1 hp (not_dvd_four_of_prime_ne_two hp hp2) ⟨g, g.2.1⟩ ha

/-- Every element of the plus space has a $q$-expansion. -/
theorem plusSpace_exists_hasQExp {k : ℕ} (g : PlusSpace k) : ∃ a, Abstract.HasQExp g a := by
  obtain ⟨-, a, ha, -⟩ := g.2
  exact ⟨a, ha⟩

/-- Two elements of the plus space with the same $q$-expansion are equal. -/
theorem plusSpace_ext_of_hasQExp {k : ℕ} {g g' : PlusSpace k} {a : ℕ → ℂ} (h : Abstract.HasQExp g a)
    (h' : Abstract.HasQExp g' a) : g = g' :=
  Subtype.ext (Abstract.eq_of_hasQExp h h')

/-- **An endomorphism of $S^+_{k+1/2}(4)$ acting on $q$-expansions by Kohnen's $T^+(4)$** (`heckeTPlusFour`). -/
def IsTPlusFour (k : ℕ) (T4 : Module.End ℂ (PlusSpace k)) : Prop :=
  ∀ (g : PlusSpace k) (c : ℕ → ℂ), Abstract.HasQExp g c → Abstract.HasQExp (T4 g) (heckeTPlusFour k c)

/-- An operator acting on $q$-expansions by $T^+(4)$ is unique. -/
theorem isTPlusFour_unique {k : ℕ} {T T' : Module.End ℂ (PlusSpace k)} (h : IsTPlusFour k T)
    (h' : IsTPlusFour k T') : T = T' := by
  refine LinearMap.ext fun g ↦ ?_
  obtain ⟨c, hc⟩ := plusSpace_exists_hasQExp g
  exact plusSpace_ext_of_hasQExp (h g c hc) (h' g c hc)

/-- **`KohnenTPlusFourStable` gives the operator $T^+(4)$ on the plus space.** -/
theorem exists_isTPlusFour {k : ℕ} (hk : 1 ≤ k) (hS : KohnenTPlusFourStable thetaMultiplierSystem k) :
    ∃ T4 : Module.End ℂ (PlusSpace k), IsTPlusFour k T4 := by
  classical
  have hex : ∀ g : PlusSpace k, ∃ g' : PlusSpace k, ∀ c, Abstract.HasQExp g c →
      Abstract.HasQExp g' (heckeTPlusFour k c) := by
    intro g
    obtain ⟨c, hc⟩ := plusSpace_exists_hasQExp g
    obtain ⟨g', hg', hc'⟩ := hS.stable hk g g.2 c hc
    refine ⟨⟨g', hg'⟩, fun c' hc'' ↦ ?_⟩
    rw [Abstract.hasQExp_unique hc'' hc]
    exact hc'
  choose F hF using hex
  have hcoef : ∀ g : PlusSpace k, ∃ c, Abstract.HasQExp g c := fun g ↦ plusSpace_exists_hasQExp g
  refine ⟨{ toFun := F, map_add' := fun f g ↦ ?_, map_smul' := fun r f ↦ ?_ }, fun g c hc ↦ hF g c hc⟩
  · obtain ⟨a, ha⟩ := hcoef f
    obtain ⟨b, hb⟩ := hcoef g
    have hab : Abstract.HasQExp ((f + g : PlusSpace k) : ℍ → ℂ) (a + b) := Abstract.hasQExp_add ha hb
    refine plusSpace_ext_of_hasQExp (hF _ _ hab) ?_
    rw [show heckeTPlusFour k (a + b) = heckeTPlusFour k a + heckeTPlusFour k b from
      (heckeTPlusFourLin k).map_add a b]
    exact Abstract.hasQExp_add (hF f a ha) (hF g b hb)
  · obtain ⟨a, ha⟩ := hcoef f
    have hra : Abstract.HasQExp ((r • f : PlusSpace k) : ℍ → ℂ) (r • a) := Abstract.hasQExp_smul r ha
    refine plusSpace_ext_of_hasQExp (hF _ _ hra) ?_
    rw [show heckeTPlusFour k (r • a) = r • heckeTPlusFour k a from (heckeTPlusFourLin k).map_smul r a]
    exact Abstract.hasQExp_smul r (hF f a ha)

/-- **The odd Hecke family** $p \mapsto T(p^2)$ on $S^+_{k+1/2}(4)$. -/
noncomputable def plusHeckeOdd (k : ℕ) (p : OddPrime) : Module.End ℂ (PlusSpace k) :=
  plusHecke k p.1.2 p.2

/-- **The Hecke family at all primes:** $T(p^2)$ for odd $p$ and a given $T_4$ at $p = 2$. -/
noncomputable def plusHeckeAll (k : ℕ) (T4 : Module.End ℂ (PlusSpace k)) (p : Nat.Primes) :
    Module.End ℂ (PlusSpace k) :=
  if h : (p : ℕ) = 2 then T4 else plusHecke k p.2 h

theorem plusHeckeAll_of_ne_two (k : ℕ) (T4 : Module.End ℂ (PlusSpace k)) {p : Nat.Primes} (h : (p : ℕ) ≠ 2) :
    plusHeckeAll k T4 p = plusHecke k p.2 h := by unfold plusHeckeAll; simp [h]

theorem plusHeckeAll_two (k : ℕ) (T4 : Module.End ℂ (PlusSpace k)) {p : Nat.Primes} (h : (p : ℕ) = 2) :
    plusHeckeAll k T4 p = T4 := by unfold plusHeckeAll; simp [h]

/-- Endomorphisms of the plus space that are determined by a commuting coefficient action commute. -/
private theorem commute_of_coeff {k : ℕ} {A B : Module.End ℂ (PlusSpace k)} {α β : (ℕ → ℂ) → (ℕ → ℂ)}
    (hA : ∀ (g : PlusSpace k) c, Abstract.HasQExp g c → Abstract.HasQExp (A g) (α c))
    (hB : ∀ (g : PlusSpace k) c, Abstract.HasQExp g c → Abstract.HasQExp (B g) (β c))
    (hαβ : ∀ c, α (β c) = β (α c)) : Commute A B := by
  refine LinearMap.ext fun g ↦ ?_
  obtain ⟨c, hc⟩ := plusSpace_exists_hasQExp g
  have h1 := hA _ _ (hB g c hc)
  have h2 := hB _ _ (hA g c hc)
  rw [hαβ] at h1
  exact plusSpace_ext_of_hasQExp h1 h2

theorem plusHecke_commute (k : ℕ) {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2) :
    Commute (plusHecke k hp hp2) (plusHecke k hq hq2) := by
  by_cases hpq : p = q
  · subst hpq; exact Commute.refl _
  exact commute_of_coeff (fun g _ hc ↦ hasQExp_plusHecke k hp hp2 g hc)
    (fun g _ hc ↦ hasQExp_plusHecke k hq hq2 g hc) fun c ↦ heckeT_comm k 1 1 hp hq hpq c

theorem plusHecke_commute_tPlusFour (k : ℕ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {T4 : Module.End ℂ (PlusSpace k)} (h4 : IsTPlusFour k T4) : Commute (plusHecke k hp hp2) T4 :=
  commute_of_coeff (fun g _ hc ↦ hasQExp_plusHecke k hp hp2 g hc) h4
    fun c ↦ heckeTPlusFour_comm k hp hp2 c

/-- **The odd Hecke operators on the plus space commute.** -/
theorem plusHeckeOdd_commute (k : ℕ) (p q : OddPrime) : Commute (plusHeckeOdd k p) (plusHeckeOdd k q) :=
  plusHecke_commute k _ _ _ _

/-- **The Hecke operators at all primes commute**, for $T_4$ acting by $T^+(4)$. -/
theorem plusHeckeAll_commute (k : ℕ) {T4 : Module.End ℂ (PlusSpace k)} (h4 : IsTPlusFour k T4)
    (p q : Nat.Primes) : Commute (plusHeckeAll k T4 p) (plusHeckeAll k T4 q) := by
  by_cases hp : (p : ℕ) = 2 <;> by_cases hq : (q : ℕ) = 2
  · rw [plusHeckeAll_two k T4 hp, plusHeckeAll_two k T4 hq]
  · rw [plusHeckeAll_two k T4 hp, plusHeckeAll_of_ne_two k T4 hq]
    exact (plusHecke_commute_tPlusFour k q.2 hq h4).symm
  · rw [plusHeckeAll_of_ne_two k T4 hp, plusHeckeAll_two k T4 hq]
    exact plusHecke_commute_tPlusFour k p.2 hp h4
  · rw [plusHeckeAll_of_ne_two k T4 hp, plusHeckeAll_of_ne_two k T4 hq]
    exact plusHecke_commute k _ _ _ _

end ModularFormsKB.HalfIntegral
