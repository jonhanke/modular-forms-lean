/-
# Newforms in Kohnen's plus space of level $4N$

Setting (Kohnen 1982 `kohnen1982` [unverified]): $N$ odd and squarefree, $k \ge 1$, trivial character. The plus space
$S^+_{k+1/2}(4N)$ (`MultiplierSystem.plusCuspForms`: coefficients vanish unless $(-1)^kn \equiv 0,1 \bmod 4$) carries the
Hecke operators $T(p^2)$, $p \nmid 4N$ (`heckeT`), and Kohnen's $T^+(4)$ at $p = 2$ (`heckeTPlusFour`; Kohnen's formula
at level $4N$ is the one of level $4$ [unverified]). Together: `kohnenHecke`.

**Named input** `KohnenNewformTheory M k N` (Kohnen 1982, main theorem and its corollary [unverified]): there is a
subspace $S^{+,\mathrm{new}}_{k+1/2}(4N)$ of the plus space and a linear isomorphism onto the new space
$S^{\mathrm{new}}_{2k}(N)$ of Tau Ceti (`TauCeti.cuspFormsNew N (2k)` inside the trivial-character space
`HeckeRing.GL2.cuspFormCharSpace`) carrying `kohnenHecke p` to $T(p)$ for every prime $p \nmid N$. In Kohnen's paper
the new space is the orthogonal complement of the old forms (images of lower levels under $U(d^2)$ and $g(z)\mapsto
g(d^2z)$) and the isomorphism is a linear combination of the Shimura lifts $\mathcal S_D$ (here
`kohnenLiftCoeff`, whose Hecke equivariance is proved in `KohnenLift.lean`). Only the existence of the isomorphism is
recorded: the input does not pin down the subspace.

**Proved** (`kohnenNew_multiplicity_one`, conditional on the input; Tau Ceti's multiplicity one
`HeckeRing.GL2.exists_eq_smul_of_forall_prime_heckeRingHomCusp_of_mem_cuspFormsNew` does the integral-weight work):
**multiplicity one in the plus newspace**: two eigenforms of every `kohnenHecke p`, $p \nmid N$ prime, in
$S^{+,\mathrm{new}}_{k+1/2}(4N)$ with the same eigenvalues are proportional.
-/
import ModularFormsKB.HalfIntegral.KohnenRecursion
import TauCeti.NumberTheory.ModularForms.Newforms.MultiplicityOne

namespace ModularFormsKB.HalfIntegral

open HeckeRing.GL2 CongruenceSubgroup TauCeti

local notation "ℍ" => UpperHalfPlane

/-- **The Hecke operators of the plus space of level $4N$**: Shimura's $T(p^2)$ (`heckeT`, trivial character) for odd
$p$, Kohnen's $T^+(4)$ (`heckeTPlusFour`) at $p = 2$. -/
noncomputable def kohnenHecke (k N p : ℕ) (a : ℕ → ℂ) : ℕ → ℂ :=
  if p = 2 then heckeTPlusFour k a else heckeT k N 1 p a

/-- **Kohnen's newform theory for the plus space** (Kohnen 1982 `kohnen1982`, main theorem [unverified]): for $N$ odd
squarefree and $k \ge 1$ there are a subspace `S` of $S^+_{k+1/2}(4N)$ (the plus newspace) and a linear bijection
`Φ` from `S` onto the new part of $S_{2k}(\Gamma_0(N))$ such that, for every prime $p \nmid N$, if $g, g' \in S$ have
coefficients $a$ and `kohnenHecke k N p a`, then $\Phi(g') = T(p)\Phi(g)$. -/
@[kb "kohnen1982" "Main theorem: S^{+,new}_{k+1/2}(4N) is isomorphic to S^{new}_{2k}(N) as Hecke modules, N odd squarefree (via combinations of Shimura lifts) [unverified]"]
structure KohnenNewformTheory (M : MultiplierSystem) (k N : ℕ) [NeZero N] : Prop where
  iso : Odd N → Squarefree N → 1 ≤ k →
    ∃ (S : Submodule ℂ (ℍ → ℂ))
      (Φ : S →ₗ[ℂ] cuspFormCharSpace ((2 * k : ℕ) : ℤ) (1 : (ZMod N)ˣ →* ℂˣ)),
      S ≤ M.plusCuspForms k N 1 ∧ Function.Injective Φ ∧
      (∀ g : S, ((Φ g : cuspFormCharSpace _ _) : CuspForm ((Gamma1 N).map (Matrix.SpecialLinearGroup.mapGL ℝ))
          ((2 * k : ℕ) : ℤ)) ∈ cuspFormsNew N ((2 * k : ℕ) : ℤ)) ∧
      (∀ F : cuspFormCharSpace ((2 * k : ℕ) : ℤ) (1 : (ZMod N)ˣ →* ℂˣ),
        ((F : CuspForm ((Gamma1 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) ((2 * k : ℕ) : ℤ)) ∈
          cuspFormsNew N ((2 * k : ℕ) : ℤ)) → ∃ g : S, Φ g = F) ∧
      (∀ p : ℕ, p.Prime → Nat.Coprime p N → ∀ g g' : S, ∀ a : ℕ → ℂ,
        Abstract.HasQExp g a → Abstract.HasQExp g' (kohnenHecke k N p a) →
        Φ g' = heckeRingHomCuspCharSpace ((2 * k : ℕ) : ℤ) 1 (heckeTCompositeGamma0 N p) (Φ g))

/-- **Multiplicity one in the plus newspace** (Kohnen 1982 `kohnen1982`, corollary of the main theorem [unverified]).
Given Kohnen's newform theory, there is a plus newspace `S` in which two forms $g, g'$, both eigenvectors of every
`kohnenHecke p` ($p \nmid N$ prime) with the same eigenvalues $\lambda_p$, with $g \neq 0$, satisfy $g' = cg$. -/
theorem kohnenNew_multiplicity_one {M : MultiplierSystem} {k N : ℕ} [NeZero N] (h : KohnenNewformTheory M k N)
    (hN : Odd N) (hsq : Squarefree N) (hk : 1 ≤ k) :
    ∃ S : Submodule ℂ (ℍ → ℂ), S ≤ M.plusCuspForms k N 1 ∧
      ∀ g ∈ S, ∀ g' ∈ S, ∀ a a' : ℕ → ℂ, Abstract.HasQExp g a → Abstract.HasQExp g' a' →
        ∀ lam : ℕ → ℂ,
          (∀ p : ℕ, p.Prime → Nat.Coprime p N → kohnenHecke k N p a = lam p • a ∧
            kohnenHecke k N p a' = lam p • a') →
          g ≠ 0 → ∃ c : ℂ, g' = c • g := by
  obtain ⟨S, Φ, hS, hinj, hnew, -, hhecke⟩ := h.iso hN hsq hk
  refine ⟨S, hS, fun g hg g' hg' a a' ha ha' lam hlam hg0 ↦ ?_⟩
  -- $\Phi(g)$ and $\Phi(g')$ are $T(p)$-eigenvectors with eigenvalue $\lambda_p$
  have heig : ∀ (x : S) (b : ℕ → ℂ), Abstract.HasQExp x b → ∀ p : ℕ, p.Prime → Nat.Coprime p N →
      kohnenHecke k N p b = lam p • b →
      heckeRingHomCuspCharSpace ((2 * k : ℕ) : ℤ) 1 (heckeTCompositeGamma0 N p) (Φ x) = lam p • Φ x := by
    intro x b hb p hp hpN hb'
    have hx : Abstract.HasQExp ((lam p • x : S) : ℍ → ℂ) (kohnenHecke k N p b) := by
      rw [hb']
      exact Abstract.hasQExp_smul (lam p) hb
    rw [← hhecke p hp hpN x (lam p • x) b hb hx, map_smul]
  have hf0 : ((Φ ⟨g, hg⟩ : cuspFormCharSpace _ _) :
      CuspForm ((Gamma1 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) ((2 * k : ℕ) : ℤ)) ≠ 0 := by
    intro h0
    have : Φ ⟨g, hg⟩ = 0 := Subtype.ext h0
    rw [← map_zero Φ] at this
    exact hg0 (congrArg Subtype.val (hinj this))
  obtain ⟨c, hc⟩ := exists_eq_smul_of_forall_prime_heckeRingHomCusp_of_mem_cuspFormsNew
    (f := Φ ⟨g, hg⟩) (g := Φ ⟨g', hg'⟩)
    (fun p hp hpN ↦ ⟨lam p, heig _ a ha p hp hpN (hlam p hp hpN).1, heig _ a' ha' p hp hpN (hlam p hp hpN).2⟩)
    (hnew _) (hnew _) hf0
  refine ⟨c, ?_⟩
  have h2 : Φ ⟨g', hg'⟩ = Φ (c • ⟨g, hg⟩) := by
    rw [map_smul]
    exact Subtype.ext hc
  exact congrArg Subtype.val (hinj h2)

end ModularFormsKB.HalfIntegral
