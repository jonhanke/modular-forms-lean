/-
# Level one Hecke operators, read through $q$-expansions

The integral-weight side of Kohnen's trace identity is $S_{2k}(\mathrm{SL}_2(\mathbb Z))$ (Mathlib's
`CuspForm 𝒮ℒ (2 * k)`) with Tau Ceti's Hecke operators `TauCeti.heckeTCuspLevelOne`. This file
- names the families $p \mapsto T(p)$ over all primes (`levelOneHecke`) and over the odd primes (`levelOneHeckeOdd`);
- proves that $T(p)$ acts on $q$-expansions (`Abstract.HasQExp`) by the coefficient formula `heckeTInt` of this
  repository (`hasQExp_levelOneHecke`), from Tau Ceti's `qExpansion_coeff_heckeTCuspLevelOne`;
- records Tau Ceti's newform basis `TauCeti.levelOneNewformBasis` as a basis of joint eigenvectors
  (`levelOneHecke_basis`) with eigenvalues the prime coefficients (`levelOneEigenvalue`), pairwise distinct already on
  the odd primes by strong multiplicity one (`levelOneEigenvalue_odd_injective`, from Tau Ceti
  `eq_of_forall_notMem_eigenvalue_eq` with the exceptional set $\{2\}$);
- gives the $q$-expansion of a basis vector: constant term $0$, first coefficient $1$, and the eigen relations
  (`exists_hasQExp_levelOneNewformBasis`).
-/
import TauCeti.NumberTheory.ModularForms.LevelOne.Eigenbasis
import TauCeti.NumberTheory.ModularForms.Newforms.StrongMultiplicityOne.Nebentypus
import ModularFormsKB.HalfIntegral.KohnenPlusHecke
import ModularFormsKB.HalfIntegral.QExpUnique
import TauCeti.NumberTheory.ModularForms.Newforms.StrongMultiplicityOne.Basic

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups ModularForm UpperHalfPlane

local notation "ℍ" => UpperHalfPlane

/-- **$T(p)$ on $S_{2k}(\mathrm{SL}_2(\mathbb Z))$** (Tau Ceti `heckeTCuspLevelOne`), $p$ prime. -/
noncomputable def levelOneHecke (k : ℕ) (p : Nat.Primes) : Module.End ℂ (CuspForm 𝒮ℒ (2 * k : ℕ)) :=
  haveI : NeZero (p : ℕ) := ⟨p.2.ne_zero⟩
  TauCeti.heckeTCuspLevelOne ((2 * k : ℕ) : ℤ) (p : ℕ)

/-- **$T(p)$ on $S_{2k}(\mathrm{SL}_2(\mathbb Z))$ for odd primes $p$.** -/
noncomputable def levelOneHeckeOdd (k : ℕ) (p : OddPrime) : Module.End ℂ (CuspForm 𝒮ℒ (2 * k : ℕ)) :=
  levelOneHecke k p.1

/-- **The eigenvalue of $T(p)$ on the newform $f$**: its $p$-th coefficient. -/
noncomputable def levelOneEigenvalue (k : ℕ) (f : HeckeRing.GL2.Newform 1 ((2 * k : ℕ) : ℤ)) (p : Nat.Primes) : ℂ :=
  (qExpansion 1 f.toCuspForm).coeff (p : ℕ)

/-- The $q$-expansion coefficients of a level-one cusp form expand it. -/
theorem hasQExp_qExpansion {w : ℤ} (F : CuspForm 𝒮ℒ w) :
    Abstract.HasQExp F (fun n ↦ (qExpansion 1 F).coeff n) := by
  intro τ
  have := ModularForm.hasSum_qExpansion (f := F) one_pos one_mem_strictPeriods_SL τ
  convert this using 2 with n
  simp [Function.Periodic.qParam, ← Complex.exp_nat_mul, mul_assoc, mul_comm, mul_left_comm]

/-- The constant coefficient of a level-one cusp form vanishes. -/
theorem qExpansion_coeff_zero_cusp {w : ℤ} (F : CuspForm 𝒮ℒ w) : (qExpansion 1 F).coeff 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero F one_pos one_mem_strictPeriods_SL

/-- **$T(p)$ acts on $q$-expansions by `heckeTInt`** (weight $2k$, level one). -/
theorem hasQExp_levelOneHecke (k : ℕ) (p : Nat.Primes) {F : CuspForm 𝒮ℒ (2 * k : ℕ)} {b : ℕ → ℂ}
    (hF : Abstract.HasQExp F b) : Abstract.HasQExp (levelOneHecke k p F) (heckeTInt (2 * k) 1 1 p b) := by
  haveI : NeZero (p : ℕ) := ⟨p.2.ne_zero⟩
  have hb : b = fun n ↦ (qExpansion 1 F).coeff n := Abstract.hasQExp_unique hF (hasQExp_qExpansion F)
  have hT := hasQExp_qExpansion (levelOneHecke k p F)
  have hc : (fun n ↦ (qExpansion 1 (levelOneHecke k p F)).coeff n) = heckeTInt (2 * k) 1 1 p b := by
    funext m
    have hp := p.2
    have hone : ((1 : DirichletCharacter ℂ 1) (p : ℕ)) = 1 := by
      have : ((p : ℕ) : ZMod 1) = 1 := Subsingleton.elim _ _
      rw [this, map_one]
    simp only [levelOneHecke, TauCeti.qExpansion_coeff_heckeTCuspLevelOne, heckeTInt, hb, hone, one_mul]
    by_cases hd : (p : ℕ) ∣ m
    · obtain ⟨m', rfl⟩ := hd
      have hg : (p * m').gcd p = p := Nat.gcd_eq_right (dvd_mul_right _ _)
      have hpos := hp.pos
      rw [hg, hp.divisors, Finset.sum_pair hp.one_lt.ne, if_pos (dvd_mul_right _ _)]
      have e1 : (p : ℕ) * m' * p / 1 ^ 2 = p * (p * m') := by ring_nf; simp
      have e2 : (p : ℕ) * m' * p / p ^ 2 = m' := by
        rw [show (p : ℕ) * m' * p = p ^ 2 * m' by ring]; exact Nat.mul_div_cancel_left _ (by positivity)
      rw [e1, e2, Nat.mul_div_cancel_left _ hpos]
      simp
    · have hg : m.gcd p = 1 := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hd)
      rw [hg, if_neg hd]
      simp [mul_comm]
  rwa [hc] at hT


/-- **The newform basis consists of joint eigenvectors.** -/
theorem levelOneHecke_basis (k : ℕ) (p : Nat.Primes) (f : HeckeRing.GL2.Newform 1 ((2 * k : ℕ) : ℤ)) :
    levelOneHecke k p (TauCeti.levelOneNewformBasis _ f) =
      levelOneEigenvalue k f p • TauCeti.levelOneNewformBasis _ f := by
  haveI : NeZero (p : ℕ) := ⟨p.2.ne_zero⟩
  exact TauCeti.heckeTCuspLevelOne_levelOneNewformBasis _ (p : ℕ) f

/-- **Strong multiplicity one at level one, away from $2$:** newforms are determined by their eigenvalues at the odd
primes. -/
theorem levelOneEigenvalue_odd_injective (k : ℕ) :
    Function.Injective fun (f : HeckeRing.GL2.Newform 1 ((2 * k : ℕ) : ℤ)) (p : OddPrime) ↦
      levelOneEigenvalue k f p.1 := by
  intro f g h
  have hχ : f.χ = g.χ := MonoidHom.ext fun x ↦ by
    rw [Subsingleton.elim x 1]; simp
  refine HeckeRing.GL2.Newform.eq_of_forall_notMem_prime_eigenvalue_eq hχ (S := {2}) ?_
  intro p hp hpN hpS
  have h2 := congrFun h ⟨⟨p, hp⟩, by simpa using hpS⟩
  simp only [levelOneEigenvalue] at h2
  exact (f.qExpansion_coeff_eq_eigenvalue ⟨p, hp.pos⟩ hpN).symm.trans
    (h2.trans (g.qExpansion_coeff_eq_eigenvalue ⟨p, hp.pos⟩ hpN))

/-- **Newforms are determined by their eigenvalues at all primes.** -/
theorem levelOneEigenvalue_injective (k : ℕ) :
    Function.Injective fun (f : HeckeRing.GL2.Newform 1 ((2 * k : ℕ) : ℤ)) (p : Nat.Primes) ↦
      levelOneEigenvalue k f p := by
  intro f g h
  exact levelOneEigenvalue_odd_injective k (funext fun p ↦ congrFun h p.1)

/-- **The $q$-expansion of a newform:** $a(0) = 0$, $a(1) = 1$, and $T(p)a = \lambda_p a$ for every prime $p$. -/
theorem exists_hasQExp_levelOneNewformBasis (k : ℕ) (f : HeckeRing.GL2.Newform 1 ((2 * k : ℕ) : ℤ)) :
    ∃ a : ℕ → ℂ, Abstract.HasQExp (TauCeti.levelOneNewformBasis _ f) a ∧ a 0 = 0 ∧ a 1 = 1 ∧
      ∀ p : Nat.Primes, heckeTInt (2 * k) 1 1 p a = levelOneEigenvalue k f p • a := by
  set B := TauCeti.levelOneNewformBasis _ f with hB
  have hBf : (qExpansion 1 (⇑B)) = qExpansion 1 (⇑f.toCuspForm) := by
    rw [hB, TauCeti.coe_levelOneNewformBasis_apply]
  refine ⟨fun n ↦ (qExpansion 1 B).coeff n, hasQExp_qExpansion B, qExpansion_coeff_zero_cusp B, ?_, ?_⟩
  · show (qExpansion 1 (⇑B)).coeff 1 = 1
    rw [hBf]; exact f.isNorm
  · intro p
    have h1 := hasQExp_levelOneHecke k p (hasQExp_qExpansion B)
    rw [levelOneHecke_basis k p f] at h1
    have h2 : Abstract.HasQExp (levelOneEigenvalue k f p • B)
        (levelOneEigenvalue k f p • fun n ↦ (qExpansion 1 B).coeff n) := by
      intro τ
      have := (hasQExp_qExpansion B τ).mul_left (levelOneEigenvalue k f p)
      simpa [mul_assoc] using this
    exact Abstract.hasQExp_unique h1 h2

end ModularFormsKB.HalfIntegral
