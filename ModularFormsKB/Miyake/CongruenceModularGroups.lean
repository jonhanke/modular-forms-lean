import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.Cusps
import ModularFormsKB.Citation
/-!
# Miyake §4.2: congruence modular groups, counting lemmas

Miyake, *Modular Forms* (Springer 1989), §4.2, pp. 104–113: the reduction map
$\lambda_N : \mathrm{SL}_2(\mathbb Z) \to \mathrm{SL}_2(\mathbb Z/N\mathbb Z)$, the Chinese remainder
decomposition of $\mathrm{SL}_2(\mathbb Z/N\mathbb Z)$, the orders of $\mathrm{GL}_2(\mathbb Z/N\mathbb Z)$
and $\mathrm{SL}_2(\mathbb Z/N\mathbb Z)$, the indices of $\Gamma(N)$, $\Gamma_0(N)$, $\Gamma_1(N)$, and
the absence of elliptic elements in $\Gamma(N)$.

## Conventions
* $\Gamma(N)$, $\Gamma_0(N)$, $\Gamma_1(N)$ are Mathlib's `CongruenceSubgroup.Gamma`, `Gamma0`, `Gamma1`,
  subgroups of $\mathrm{SL}_2(\mathbb Z) = \Gamma(1)$. Matrix indices are 0-based: Miyake's
  $\begin{pmatrix} a & b \\ c & d\end{pmatrix}$ is `γ 0 0, γ 0 1, γ 1 0, γ 1 1`.
* Miyake writes $\bar\Gamma = \iota(\Gamma) \subset \mathrm{Aut}(\mathbb H)$, so
  $\bar\Gamma \cong \Gamma\{\pm1\}/\{\pm1\}$. Indices of barred groups are therefore indices of
  $\Gamma\{\pm 1\}$, written here `adjoinNegOne Γ` $= \Gamma \sqcup \langle -1\rangle$.
* Orders of finite groups are `Nat.card`; Miyake's products $\prod_{p\mid N}(1 - p^{-2})$ are taken in
  $\mathbb Q$ over `N.primeFactors`.
-/

open Matrix CongruenceSubgroup
open scoped MatrixGroups

namespace ModularFormsKB.Miyake

/-! ### Theorem 4.2.1 and Corollary 4.2.2 -/

/-- Coprime lift (Miyake (4.2.1)). -/
theorem exists_coprime_lift (c d : ℤ) (N : ℕ) (h : ∃ x y z : ℤ, x * c + y * d + z * N = 1) :
    ∃ u v : ℤ, IsCoprime (c + u * N) (d + v * N) := by
  obtain ⟨x, y, z, hxyz⟩ := h
  by_cases hc : c = 0
  · subst hc
    refine ⟨1, 0, ?_⟩
    refine ⟨z, y, ?_⟩
    simpa [add_comm, mul_comm] using (by linarith : z * (N : ℤ) + y * d = 1)
  · classical
    set S : Finset ℕ := c.natAbs.primeFactors.filter (fun p => ¬ (p : ℤ) ∣ d) with hS
    refine ⟨0, ∏ p ∈ S, (p : ℤ), ?_⟩
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : (p : ℤ) ∣ c + 0 * N := (Int.natCast_dvd_natCast.2 hpd).trans (Int.gcd_dvd_left ..)
    have h2 : (p : ℤ) ∣ d + (∏ p ∈ S, (p : ℤ)) * N :=
      (Int.natCast_dvd_natCast.2 hpd).trans (Int.gcd_dvd_right ..)
    have pp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    simp only [zero_mul, add_zero] at h1
    by_cases hd : (p : ℤ) ∣ d
    · have h3 : (p : ℤ) ∣ (∏ p ∈ S, (p : ℤ)) * N := (dvd_add_right hd).1 h2
      rcases pp.dvd_or_dvd h3 with h4 | h4
      · obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff pp _).1 h4
        have : p = q := by
          have hqp := (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hq).1)).1 (Int.natCast_dvd_natCast.1 hpq)
          exact hqp
        subst this
        exact (Finset.mem_filter.1 hq).2 hd
      · have : (p : ℤ) ∣ 1 := by
          rw [← hxyz]
          exact dvd_add (dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right hd _))
            (dvd_mul_of_dvd_right h4 _)
        exact pp.not_dvd_one this
    · have hpS : p ∈ S := by
        refine Finset.mem_filter.2 ⟨?_, hd⟩
        rw [Nat.mem_primeFactors]
        exact ⟨hp, Int.natCast_dvd.1 h1, Int.natAbs_ne_zero.2 hc⟩
      have h3 : (p : ℤ) ∣ (∏ p ∈ S, (p : ℤ)) * N :=
        dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ hpS) _
      exact hd ((dvd_add_left h3).1 h2)

/-- **Miyake, Theorem 4.2.1 (1).** For a positive integer $N$ the reduction map
$\lambda_N : \mathrm{SL}_2(\mathbb Z) \to \mathrm{SL}_2(\mathbb Z/N\mathbb Z)$ is surjective.
(Part (2), $\ker \lambda_N = \Gamma(N)$, is Mathlib's definition of `CongruenceSubgroup.Gamma`.) -/
@[kb "miyake1989" "Theorem 4.2.1 (1), p. 104"]
theorem SL2_reduction_surjective (N : ℕ) [NeZero N] :
    Function.Surjective (SpecialLinearGroup.map (Int.castRingHom (ZMod N)) :
      SL(2, ℤ) →* SL(2, ZMod N)) := by
  intro g
  obtain ⟨a1, ha1⟩ := ZMod.intCast_surjective (g 0 0)
  obtain ⟨b1, hb1⟩ := ZMod.intCast_surjective (g 0 1)
  obtain ⟨c1, hc1⟩ := ZMod.intCast_surjective (g 1 0)
  obtain ⟨d1, hd1⟩ := ZMod.intCast_surjective (g 1 1)
  have hdet : (a1 * d1 - b1 * c1 : ℤ) = ((1 : ℤ) : ZMod N) := by
    have := g.det_coe
    rw [Matrix.det_fin_two] at this
    push_cast
    rw [ha1, hb1, hc1, hd1]; simpa using this
  obtain ⟨n, hn⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 hdet.symm
  have hn' : a1 * d1 - b1 * c1 = 1 + n * N := by linarith
  obtain ⟨u, v, huv⟩ := exists_coprime_lift c1 d1 N ⟨-b1, a1, -n, by linarith⟩
  set c := c1 + u * N
  set d := d1 + v * N
  obtain ⟨p, q, hpq⟩ := huv
  set m : ℤ := n + a1 * v - b1 * u with hm
  have hdet2 : a1 * d - b1 * c = 1 + m * N := by
    simp only [c, d, hm]; linarith
  have hdA : (!![a1 + (-m * q) * N, b1 + (m * p) * N; c, d]).det = 1 := by
    rw [Matrix.det_fin_two_of]
    have : p * c + q * d = 1 := hpq
    calc _ = (a1 * d - b1 * c) + N * (-m * q * d - m * p * c) := by ring
      _ = 1 := by
        rw [hdet2]
        have : -m * q * d - m * p * c = -m * (p * c + q * d) := by ring
        rw [this, hpq]; ring
  obtain ⟨A, hA⟩ : ∃ A : SL(2, ℤ), (A : Matrix (Fin 2) (Fin 2) ℤ) =
      !![a1 + (-m * q) * N, b1 + (m * p) * N; c, d] := ⟨⟨_, hdA⟩, rfl⟩
  refine ⟨A, ?_⟩
  ext i j
  show ((A i j : ℤ) : ZMod N) = _
  have : A i j = (!![a1 + (-m * q) * N, b1 + (m * p) * N; c, d] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    rw [← hA]
  rw [this]
  fin_cases i <;> fin_cases j <;> simp [c, d, ← ha1, ← hb1, ← hc1, ← hd1]

/-- The reduction of the lower right entry, as a homomorphism $\Gamma_0(N) \to (\mathbb Z/N\mathbb Z)^\times$. -/
noncomputable def gamma0UnitMap (N : ℕ) : Gamma0 N →* (ZMod N)ˣ :=
  (Gamma0Map N).toHomUnits

theorem gamma0UnitMap_coe (N : ℕ) (γ : Gamma0 N) :
    ((gamma0UnitMap N γ : (ZMod N)ˣ) : ZMod N) = ((γ : SL(2, ℤ)) 1 1 : ZMod N) := rfl

/-- The kernel of `gamma0UnitMap` is $\Gamma_1(N)$ viewed inside $\Gamma_0(N)$. -/
theorem ker_gamma0UnitMap (N : ℕ) :
    (gamma0UnitMap N).ker = (Gamma1 N).subgroupOf (Gamma0 N) := by
  ext γ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Gamma1_mem, Units.ext_iff]
  have h1 : ((γ : SL(2, ℤ)) 1 0 : ZMod N) = 0 := Gamma0_mem.1 γ.2
  have hdet : ((γ : SL(2, ℤ)) 0 0 : ZMod N) * ((γ : SL(2, ℤ)) 1 1 : ZMod N) = 1 := by
    have := (γ : SL(2, ℤ)).det_coe
    rw [Matrix.det_fin_two] at this
    have := congrArg (Int.cast : ℤ → ZMod N) this
    push_cast at this
    rw [h1] at this
    simpa using this
  rw [gamma0UnitMap_coe, Units.val_one]
  constructor
  · intro h
    refine ⟨?_, h, h1⟩
    rw [h, mul_one] at hdet
    exact hdet
  · exact fun h => h.2.1

theorem gamma0UnitMap_surjective (N : ℕ) [NeZero N] : Function.Surjective (gamma0UnitMap N) := by
  intro u
  obtain ⟨g, hg⟩ : ∃ g : SL(2, ZMod N), (g : Matrix (Fin 2) (Fin 2) (ZMod N)) =
      !![((u⁻¹ : (ZMod N)ˣ) : ZMod N), 0; 0, (u : ZMod N)] :=
    ⟨⟨_, by simp [Matrix.det_fin_two_of]⟩, rfl⟩
  obtain ⟨A, hA⟩ := SL2_reduction_surjective N g
  have hA' : ∀ i j, ((A i j : ℤ) : ZMod N) = g i j := fun i j => by
    rw [← hA]; rfl
  have hmem : A ∈ Gamma0 N := by
    rw [Gamma0_mem, hA']
    simp [hg]
  refine ⟨⟨A, hmem⟩, ?_⟩
  apply Units.ext
  rw [gamma0UnitMap_coe]
  show ((A 1 1 : ℤ) : ZMod N) = _
  rw [hA']
  simp [hg]

/-- $\Gamma_1(N)$ is normal in $\Gamma_0(N)$: inside $\Gamma_0(N)$ it is the kernel of Mathlib's
`Gamma0Map` ($\gamma \mapsto d \bmod N$). -/
instance Gamma1_subgroupOf_Gamma0_normal (N : ℕ) :
    ((Gamma1 N).subgroupOf (Gamma0 N)).Normal := by
  rw [← ker_gamma0UnitMap]
  exact MonoidHom.normal_ker _

/-- **Miyake, Corollary 4.2.2.** The map $\gamma \mapsto d \bmod N$ on $\Gamma_0(N)$ induces an
isomorphism $\Gamma_0(N)/\Gamma_1(N) \cong (\mathbb Z/N\mathbb Z)^\times$; here $\Gamma_1(N)$ is viewed
inside $\Gamma_0(N)$ (`subgroupOf`). See `gamma0QuotGamma1Equiv_mk` for the value. -/
@[kb "miyake1989" "Corollary 4.2.2, p. 105"]
noncomputable def gamma0QuotGamma1Equiv (N : ℕ) [NeZero N] :
    Gamma0 N ⧸ (Gamma1 N).subgroupOf (Gamma0 N) ≃* (ZMod N)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_gamma0UnitMap N).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (gamma0UnitMap N) (gamma0UnitMap_surjective N))

/-- **Miyake, Corollary 4.2.2** (value): the isomorphism sends the class of
$\gamma = \begin{pmatrix} a & b \\ c & d\end{pmatrix} \in \Gamma_0(N)$ to $d \bmod N$. -/
@[kb "miyake1989" "Corollary 4.2.2, p. 105"]
theorem gamma0QuotGamma1Equiv_mk (N : ℕ) [NeZero N] (γ : Gamma0 N) :
    ((gamma0QuotGamma1Equiv N (γ : Gamma0 N ⧸ (Gamma1 N).subgroupOf (Gamma0 N)) : (ZMod N)ˣ) :
      ZMod N) = ((γ : SL(2, ℤ)) 1 1 : ZMod N) := by
  simp [gamma0QuotGamma1Equiv, ← gamma0UnitMap_coe]
  rfl

/-! ### Lemma 4.2.3 and Theorem 4.2.4 -/

section PrimePower

set_option linter.unusedSectionVars false

variable (p k : ℕ) [hp : Fact p.Prime]

/-- Reduction modulo `p` from `ZMod (p ^ (k+1))`. -/
private abbrev redHom : ZMod (p ^ (k + 1)) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p)

private lemma isUnit_redHom_iff (x : ZMod (p ^ (k + 1))) :
    IsUnit (redHom p k x) ↔ IsUnit x := by
  have hx : x = ((x.val : ℕ) : ZMod (p ^ (k + 1))) := (ZMod.natCast_zmod_val x).symm
  have hr : redHom p k x = ((x.val : ℕ) : ZMod p) := by
    rw [hx]; simp
  rw [hr]
  conv_rhs => rw [hx]
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp.out (Nat.succ_pos k), ZMod.isUnit_iff_coprime,
    Nat.coprime_comm, hp.out.coprime_iff_not_dvd]

private lemma isUnit_det_redHom_iff (M : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (k + 1)))) :
    IsUnit (((redHom p k).mapMatrix M).det) ↔ IsUnit M.det := by
  rw [← RingHom.map_det, isUnit_redHom_iff]

/-- Reduction mod `p` on matrices, as an additive group homomorphism. -/
private abbrev redAdd : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (k + 1))) →+
    Matrix (Fin 2) (Fin 2) (ZMod p) := ((redHom p k).mapMatrix : _ →+* _).toAddMonoidHom

private lemma redAdd_surjective : Function.Surjective (redAdd p k) := by
  intro m
  choose f hf using ZMod.ringHom_surjective (redHom p k)
  refine ⟨Matrix.of fun i j => f (m i j), ?_⟩
  ext i j
  simp [hf]

private lemma card_ker_redAdd : Nat.card (redAdd p k).ker = p ^ (4 * k) := by
  have h := AddSubgroup.card_ker_mul_card_of_surjective (redAdd_surjective p k)
  rw [Matrix.card_matrix, Matrix.card_matrix] at h
  simp only [Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin] at h
  have hp0 : 0 < p ^ 4 := pow_pos hp.out.pos 4
  refine Nat.eq_of_mul_eq_mul_right hp0 ?_
  rw [h, ← pow_mul, ← pow_add]
  congr 1
  ring

/-- Reduction mod `p` on `GL₂`. -/
private noncomputable abbrev redGL :
    GL (Fin 2) (ZMod (p ^ (k + 1))) →* GL (Fin 2) (ZMod p) :=
  Matrix.GeneralLinearGroup.map (redHom p k)

private lemma redGL_surjective : Function.Surjective (redGL p k) := by
  intro h
  obtain ⟨M, hM⟩ := redAdd_surjective p k (h : Matrix (Fin 2) (Fin 2) (ZMod p))
  have hu : IsUnit M.det := by
    rw [← isUnit_det_redHom_iff]
    exact (by simpa using hM : (redHom p k).mapMatrix M = h) ▸ (Matrix.isUnits_det_units h)
  refine ⟨Matrix.GeneralLinearGroup.mk'' M hu, ?_⟩
  ext i j
  have := congrFun (congrFun hM i) j
  simpa [redGL] using this

private lemma mapMatrix_one_add (m : (redAdd p k).ker) :
    (redHom p k).mapMatrix (1 + m.1) = 1 := by
  have hm : (redHom p k).mapMatrix m.1 = 0 := m.2
  rw [map_add, map_one, hm, add_zero]

/-- The kernel of reduction on `GL₂` is in bijection with the additive kernel (`g ↦ g - 1`). -/
private noncomputable def redGLKerEquiv : (redGL p k).ker ≃ (redAdd p k).ker where
  toFun g := ⟨(g.1 : Matrix (Fin 2) (Fin 2) _) - 1, by
    have h : (redHom p k).mapMatrix (g.1 : Matrix (Fin 2) (Fin 2) _) = 1 :=
      congrArg Units.val g.2
    show (redHom p k).mapMatrix _ = 0
    rw [map_sub, map_one, h, sub_self]⟩
  invFun m := ⟨Matrix.GeneralLinearGroup.mk'' (1 + m.1) (by
    rw [← isUnit_det_redHom_iff, mapMatrix_one_add]
    simp), Units.ext (by
      have := mapMatrix_one_add p k m
      simpa [redGL] using this)⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    simp
  right_inv m := by
    apply Subtype.ext
    simp

private lemma card_GL2_prime_pow :
    Nat.card (GL (Fin 2) (ZMod (p ^ (k + 1)))) =
      p ^ (4 * k) * ((p ^ 2 - 1) * (p ^ 2 - p)) := by
  rw [← Subgroup.card_ker_mul_card_of_surjective (redGL_surjective p k),
    Nat.card_congr (redGLKerEquiv p k), card_ker_redAdd]
  have h := Matrix.card_GL_field (𝔽 := ZMod p) 2
  rw [ZMod.card] at h
  rw [h, Fin.prod_univ_two]
  simp

/-- Order of `SL₂(ℤ/p^(k+1))`. -/
private lemma card_SL2_prime_pow :
    (Nat.card SL(2, ZMod (p ^ (k + 1))) : ℚ) = (p : ℚ) ^ (3 * k + 1) * ((p : ℚ) ^ 2 - 1) := by
  have h := Matrix.card_SL_mul_card_units (n := Fin 2) (R := ZMod (p ^ (k + 1)))
  rw [card_GL2_prime_pow, Nat.card_eq_fintype_card (α := (ZMod (p ^ (k + 1)))ˣ),
    ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hp.out] at h
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hp2 : p ≤ p ^ 2 := by nlinarith
  have hq : ((Nat.card SL(2, ZMod (p ^ (k + 1))) * (p ^ k * (p - 1)) : ℕ) : ℚ) =
      ((p ^ (4 * k) * ((p ^ 2 - 1) * (p ^ 2 - p)) : ℕ) : ℚ) := by rw [h]
  push_cast [Nat.cast_sub hp1, Nat.cast_sub hp2, Nat.cast_sub (le_trans hp1 hp2)] at hq
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hp1' : (p : ℚ) - 1 ≠ 0 := by
    have : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
    linarith
  have hk : (p : ℚ) ^ k * ((p : ℚ) - 1) ≠ 0 := mul_ne_zero (pow_ne_zero _ hp0) hp1'
  apply mul_right_cancel₀ hk
  rw [hq]
  have : (4 * k) = k + 3 * k := by ring
  rw [this, pow_add, pow_succ, pow_add]
  ring

end PrimePower

/-- `SL_n` of a ring equivalence. -/
private noncomputable def slMapEquiv {n : Type*} [Fintype n] [DecidableEq n] {R S : Type*}
    [CommRing R] [CommRing S] (e : R ≃+* S) :
    SpecialLinearGroup n R ≃* SpecialLinearGroup n S :=
  MonoidHom.toMulEquiv (SpecialLinearGroup.map (e : R →+* S))
    (SpecialLinearGroup.map (e.symm : S →+* R))
    (by ext1 g; ext i j; simp [SpecialLinearGroup.map_apply_coe])
    (by ext1 g; ext i j; simp [SpecialLinearGroup.map_apply_coe])

/-- `SL_n` of a product of rings is the product of the `SL_n`. -/
private noncomputable def slPiEquiv {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    [DecidableEq ι] (R : ι → Type*) [∀ i, CommRing (R i)] :
    SpecialLinearGroup n (Π i, R i) ≃* Π i, SpecialLinearGroup n (R i) where
  toFun A i := SpecialLinearGroup.map (Pi.evalRingHom R i) A
  invFun B := ⟨Matrix.of fun a b i => (B i : Matrix n n (R i)) a b, by
    ext i
    have h := (RingHom.map_det (Pi.evalRingHom R i)
      (Matrix.of fun a b i => (B i : Matrix n n (R i)) a b))
    simp only [Pi.evalRingHom_apply] at h
    rw [Pi.one_apply, h]
    have : (Pi.evalRingHom R i).mapMatrix (Matrix.of fun a b i => (B i : Matrix n n (R i)) a b)
        = (B i : Matrix n n (R i)) := by
      ext a b; rfl
    rw [this]; exact (B i).det_coe⟩
  left_inv A := by
    ext a b i; rfl
  right_inv B := by
    ext i a b; rfl
  map_mul' A B := by
    ext i; simp

/-- **Miyake, Lemma 4.2.3.** For $N = \prod_p p^{e_p}$,
$\mathrm{SL}_2(\mathbb Z/N\mathbb Z) \cong \prod_{p \mid N} \mathrm{SL}_2(\mathbb Z/p^{e_p}\mathbb Z)$, the
isomorphism being reduction modulo each $p^{e_p}$ (`SL2ZModEquivPi_apply`). Built from Mathlib's
`ZMod.prodEquivPi`. -/
@[kb "miyake1989" "Lemma 4.2.3, p. 105"]
noncomputable def SL2ZModEquivPi (N : ℕ) [NeZero N] :
    SL(2, ZMod N) ≃* Π p : N.primeFactors, SL(2, ZMod ((p : ℕ) ^ N.factorization p)) :=
  (slMapEquiv (ZMod.equivPi (n := N) (NeZero.ne N))).trans
    (slPiEquiv (fun p : N.primeFactors => ZMod ((p : ℕ) ^ N.factorization p)))

/-- **Miyake, Lemma 4.2.3** (value): the $p$-component of the isomorphism is reduction modulo
$p^{e_p}$. -/
@[kb "miyake1989" "Lemma 4.2.3, p. 105"]
theorem SL2ZModEquivPi_apply (N : ℕ) [NeZero N] (g : SL(2, ZMod N)) (p : N.primeFactors) :
    SL2ZModEquivPi N g p = SpecialLinearGroup.map
      (ZMod.castHom (Nat.ordProj_dvd N p) (ZMod ((p : ℕ) ^ N.factorization p))) g := by
  have h : (Pi.evalRingHom (fun p : N.primeFactors => ZMod ((p : ℕ) ^ N.factorization p)) p).comp
      (ZMod.equivPi (n := N) (NeZero.ne N) : ZMod N →+* _) =
      ZMod.castHom (Nat.ordProj_dvd N p) (ZMod ((p : ℕ) ^ N.factorization p)) :=
    Subsingleton.elim _ _
  rw [← h]
  ext i j
  rfl

/-- **Miyake, Theorem 4.2.4 (1).** $|\mathrm{GL}_2(\mathbb Z/N\mathbb Z)| =
\varphi(N)\,|\mathrm{SL}_2(\mathbb Z/N\mathbb Z)|$. -/
@[kb "miyake1989" "Theorem 4.2.4 (1), p. 105"]
theorem card_GL2_ZMod (N : ℕ) [NeZero N] :
    Nat.card (GL (Fin 2) (ZMod N)) = N.totient * Nat.card SL(2, ZMod N) := by
  rw [← Matrix.card_SL_mul_card_units, Nat.card_eq_fintype_card (α := (ZMod N)ˣ),
    ZMod.card_units_eq_totient, mul_comm]

/-- **Miyake, Theorem 4.2.4 (2).** $|\mathrm{SL}_2(\mathbb Z/N\mathbb Z)| =
N^3 \prod_{p \mid N} (1 - p^{-2})$, as an identity in $\mathbb Q$. -/
@[kb "miyake1989" "Theorem 4.2.4 (2), p. 105"]
theorem card_SL2_ZMod (N : ℕ) [NeZero N] :
    (Nat.card SL(2, ZMod N) : ℚ) = N ^ 3 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  have key : ∀ p : N.primeFactors, (Nat.card SL(2, ZMod ((p : ℕ) ^ N.factorization p)) : ℚ) =
      (((p : ℕ) : ℚ) ^ N.factorization p) ^ 3 * (1 - 1 / ((p : ℕ) : ℚ) ^ 2) := by
    rintro ⟨p, hpm⟩
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpm
    have : Fact p.Prime := ⟨hpp⟩
    have hpos : 0 < N.factorization p :=
      hpp.factorization_pos_of_dvd (NeZero.ne N) (Nat.dvd_of_mem_primeFactors hpm)
    obtain ⟨k, hk⟩ : ∃ k, N.factorization p = k + 1 := ⟨N.factorization p - 1, by omega⟩
    simp only
    rw [hk, card_SL2_prime_pow]
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hpp.ne_zero
    field_simp
    ring
  have hN : ∏ p : N.primeFactors, (((p : ℕ) : ℚ) ^ N.factorization p) = (N : ℚ) := by
    exact_mod_cast (Nat.prod_primeFactors_coe_pow_factorization (NeZero.ne N)).symm
  rw [Nat.card_congr (SL2ZModEquivPi N).toEquiv, Nat.card_pi]
  push_cast
  rw [Finset.prod_congr rfl (fun p _ => key p), Finset.prod_mul_distrib, Finset.prod_pow, hN,
    Finset.prod_coe_sort N.primeFactors (fun p : ℕ => (1 - 1 / (p : ℚ) ^ 2))]

/-! ### Theorem 4.2.5: indices -/

/-- The subgroup $\Gamma\{\pm 1\} = \Gamma \sqcup \langle -1 \rangle$ of $\mathrm{SL}_2(\mathbb Z)$. Its
image in $\mathrm{Aut}(\mathbb H)$ is Miyake's $\bar\Gamma = \iota(\Gamma)$, and
$[\bar\Gamma(1) : \bar\Gamma] = [\mathrm{SL}_2(\mathbb Z) : \Gamma\{\pm1\}]$ because the kernel
$\{\pm1\}$ of $\iota$ lies in $\Gamma\{\pm 1\}$. Compare Mathlib's `Subgroup.adjoinNegOne`
(for subgroups of `GL n R`). -/
def adjoinNegOne (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) :=
  Γ ⊔ Subgroup.zpowers (-1)

/-- The reduction map $\lambda_N : \mathrm{SL}_2(\mathbb Z) \to \mathrm{SL}_2(\mathbb Z/N\mathbb Z)$. -/
abbrev redMap (N : ℕ) : SL(2, ℤ) →* SL(2, ZMod N) :=
  SpecialLinearGroup.map (Int.castRingHom (ZMod N))

theorem ker_redMap (N : ℕ) : (redMap N).ker = Gamma N := rfl

/-- If $\Gamma(N) \le K$, then $K$ has the same index as its image under $\lambda_N$. -/
theorem index_eq_index_map_redMap (N : ℕ) [NeZero N] (K : Subgroup SL(2, ℤ)) (hK : Gamma N ≤ K) :
    K.index = (K.map (redMap N)).index := by
  rw [← Subgroup.index_comap_of_surjective _ (SL2_reduction_surjective N),
    Subgroup.comap_map_eq]
  have hK' : (redMap N).ker ≤ K := hK
  rw [sup_eq_left.2 hK']

theorem neg_one_zpow_cases (m : ℤ) :
    (-1 : SL(2, ℤ)) ^ m = 1 ∨ (-1 : SL(2, ℤ)) ^ m = -1 := by
  have hsq : (-1 : SL(2, ℤ)) * (-1) = 1 := by
    apply Subtype.ext; simp
  induction m using Int.induction_on with
  | zero => left; simp
  | succ i ih =>
    rw [_root_.zpow_add_one]
    rcases ih with h | h
    · right; rw [h]; simp
    · left; rw [h, hsq]
  | pred i ih =>
    rw [_root_.zpow_sub_one]
    have hinv : (-1 : SL(2, ℤ))⁻¹ = -1 := by
      rw [inv_eq_iff_mul_eq_one]; exact hsq
    rw [hinv]
    rcases ih with h | h
    · right; rw [h]; simp
    · left; rw [h, hsq]

instance zpowers_neg_one_normal : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal := by
  constructor
  intro n hn g
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
  rcases neg_one_zpow_cases k with h | h <;> rw [h]
  · simp
  · have : g * -1 = -1 * g := by apply Subtype.ext; simp
    rw [this, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.mem_zpowers _

/-- If $-1 \notin \Gamma$ then $[\Gamma\{\pm1\} : \Gamma] = 2$. -/
theorem relIndex_adjoinNegOne_eq_two (Γ : Subgroup SL(2, ℤ)) (h : (-1 : SL(2, ℤ)) ∉ Γ) :
    Γ.relIndex (adjoinNegOne Γ) = 2 := by
  have hmem : (-1 : SL(2, ℤ)) ∈ adjoinNegOne Γ :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hdvd : Γ.relIndex (adjoinNegOne Γ) ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    refine ⟨-1, hmem, fun b hb => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rcases neg_one_zpow_cases k with h' | h' <;> rw [h']
    · right; simpa using hx
    · left
      have : x * -1 * -1 = x := by apply Subtype.ext; simp
      rw [this]; exact hx
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
  · exfalso
    exact h ((Subgroup.relIndex_eq_one.1 h1) hmem)
  · exact h1

/-- Step in the proof of **Miyake, Theorem 4.2.5**: $[\Gamma(1) : \Gamma(N)] =
|\mathrm{SL}_2(\mathbb Z/N\mathbb Z)|$, by Theorem 4.2.1. -/
@[kb "miyake1989" "Theorem 4.2.5 (proof), p. 106"]
theorem index_Gamma (N : ℕ) [NeZero N] :
    (Gamma N).index = Nat.card SL(2, ZMod N) := by
  have h1 : Gamma N = (⊥ : Subgroup SL(2, ZMod N)).comap (redMap N) := by
    rw [MonoidHom.comap_bot]; rfl
  rw [h1, Subgroup.index_comap_of_surjective _ (SL2_reduction_surjective N), Subgroup.index_bot]

/-- **Miyake, Theorem 4.2.5 (1)**, $N > 2$: $[\bar\Gamma(1) : \bar\Gamma(N)] =
\tfrac12 N^3 \prod_{p\mid N}(1 - p^{-2})$. -/
@[kb "miyake1989" "Theorem 4.2.5 (1), p. 106"]
theorem index_adjoinNegOne_Gamma {N : ℕ} (hN : 2 < N) :
    ((adjoinNegOne (Gamma N)).index : ℚ) =
      N ^ 3 / 2 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  have : NeZero N := ⟨by omega⟩
  have : Fact (2 < N) := ⟨hN⟩
  have hn : (-1 : SL(2, ℤ)) ∉ Gamma N := by
    intro h
    have := (Gamma_mem.1 h).1
    simp at this
    exact ZMod.neg_one_ne_one this
  have h1 : (Gamma N).relIndex (adjoinNegOne (Gamma N)) * (adjoinNegOne (Gamma N)).index =
      (Gamma N).index := Subgroup.relIndex_mul_index le_sup_left
  rw [relIndex_adjoinNegOne_eq_two _ hn, index_Gamma] at h1
  have h2 : (2 : ℚ) * (adjoinNegOne (Gamma N)).index = Nat.card SL(2, ZMod N) := by
    exact_mod_cast h1
  rw [card_SL2_ZMod] at h2
  linarith

/-- **Miyake, Theorem 4.2.5 (1)**, $N = 2$: $[\bar\Gamma(1) : \bar\Gamma(2)] = 6$. -/
@[kb "miyake1989" "Theorem 4.2.5 (1), p. 106"]
theorem index_adjoinNegOne_Gamma_two : (adjoinNegOne (Gamma 2)).index = 6 := by
  have hm : (-1 : SL(2, ℤ)) ∈ Gamma 2 := by
    rw [Gamma_mem]; simp
  have h1 : adjoinNegOne (Gamma 2) = Gamma 2 :=
    sup_eq_left.2 ((Subgroup.zpowers_le).2 hm)
  have h2 := card_SL2_ZMod 2
  rw [Nat.Prime.primeFactors Nat.prime_two] at h2
  norm_num at h2
  rw [h1, index_Gamma, Nat.card_eq_fintype_card]
  exact_mod_cast h2

/-- The image of $\Gamma_0(N)$ in $\mathrm{SL}_2(\mathbb Z/N\mathbb Z)$: the matrices with lower left
entry $0$. -/
def Bsub (N : ℕ) : Subgroup SL(2, ZMod N) := (Gamma0 N).map (redMap N)

theorem mem_Bsub (N : ℕ) [NeZero N] (g : SL(2, ZMod N)) : g ∈ Bsub N ↔ g 1 0 = 0 := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact Gamma0_mem.1 hA
  · intro h
    obtain ⟨A, rfl⟩ := SL2_reduction_surjective N g
    exact ⟨A, Gamma0_mem.2 h, rfl⟩

/-- The upper triangular matrix with diagonal $(u, u^{-1})$ and upper right entry $b$. -/
def upperTri (N : ℕ) (x : (ZMod N)ˣ × ZMod N) : SL(2, ZMod N) :=
  ⟨!![(x.1 : ZMod N), x.2; 0, ((x.1⁻¹ : (ZMod N)ˣ) : ZMod N)], by
    simp [Matrix.det_fin_two_of]⟩

theorem card_Bsub (N : ℕ) [NeZero N] : Nat.card (Bsub N) = N * N.totient := by
  have hinj : Function.Injective (upperTri N) := by
    intro x y hxy
    have h00 := congrArg (fun g : SL(2, ZMod N) => (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0) hxy
    have h01 := congrArg (fun g : SL(2, ZMod N) => (g : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 1) hxy
    simp only [upperTri] at h00 h01
    simp at h00 h01
    exact Prod.ext (Units.ext h00) h01
  have hrange : (Bsub N : Set SL(2, ZMod N)) = Set.range (upperTri N) := by
    ext g
    rw [SetLike.mem_coe, mem_Bsub]
    constructor
    · intro h
      have hdet : g 0 0 * g 1 1 = 1 := by
        have := g.det_coe
        rw [Matrix.det_fin_two, h] at this
        simpa using this
      refine ⟨(Units.mk (g 0 0) (g 1 1) hdet (by rw [mul_comm]; exact hdet), g 0 1), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upperTri, h]
    · rintro ⟨x, rfl⟩
      simp [upperTri]
  have : Nat.card (Bsub N) = Nat.card (Set.range (upperTri N)) := by
    rw [← hrange]; rfl
  rw [this, Nat.card_range_of_injective hinj, Nat.card_prod, Nat.card_zmod, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, mul_comm]

/-- **Miyake, Theorem 4.2.5 (2).** $[\Gamma(1) : \Gamma_0(N)] = N \prod_{p \mid N}(1 + 1/p)$
(Miyake states it for $N \ge 2$ and for the barred groups, which have the same index since
$-1 \in \Gamma_0(N)$; see `adjoinNegOne_Gamma0`). Tau Ceti has the same count as
`Gamma0_index_eq_prod_factorization` (`NumberTheory/ModularForms/CongruenceSubgroups/Basic.lean`). -/
@[kb "miyake1989" "Theorem 4.2.5 (2), p. 106"]
theorem index_Gamma0 (N : ℕ) [NeZero N] :
    ((Gamma0 N).index : ℚ) = N * ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℚ)) := by
  have hle : Gamma N ≤ Gamma0 N := fun g hg => by
    rw [Gamma0_mem]; exact (Gamma_mem.1 hg).2.2.1
  rw [index_eq_index_map_redMap N _ hle]
  have h1 := Subgroup.card_mul_index (Bsub N)
  rw [card_Bsub] at h1
  have h2 : (N : ℚ) * N.totient * ((Gamma0 N).map (redMap N)).index = Nat.card SL(2, ZMod N) := by
    exact_mod_cast h1
  rw [card_SL2_ZMod] at h2
  have hφ := Nat.totient_eq_mul_prod_factors N
  have hprod : ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) =
      (∏ p ∈ N.primeFactors, (1 - (p : ℚ)⁻¹)) * ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℚ)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_primeFactors hp).ne'
    field_simp
    ring
  have hN : (N : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hφ0 : (N.totient : ℚ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  apply mul_left_cancel₀ (mul_ne_zero hN hφ0)
  rw [h2, hprod]
  have : (N : ℚ) ^ 3 * ((∏ p ∈ N.primeFactors, (1 - (p : ℚ)⁻¹)) * ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℚ)))
      = N ^ 2 * ((N : ℚ) * ∏ p ∈ N.primeFactors, (1 - (p : ℚ)⁻¹)) * ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℚ)) := by ring
  rw [this, ← hφ]
  ring

/-- $-1 \in \Gamma_0(N)$, so $\Gamma_0(N)\{\pm1\} = \Gamma_0(N)$ and
$[\bar\Gamma(1) : \bar\Gamma_0(N)] = [\Gamma(1) : \Gamma_0(N)]$ (Miyake, proof of Theorem 4.2.5). -/
theorem adjoinNegOne_Gamma0 (N : ℕ) : adjoinNegOne (Gamma0 N) = Gamma0 N := by
  have hm : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
    rw [Gamma0_mem]; simp
  exact sup_eq_left.2 ((Subgroup.zpowers_le).2 hm)

/-- Step in the proof of **Miyake, Theorem 4.2.5 (3)**: $[\Gamma_0(N) : \Gamma_1(N)] = \varphi(N)$,
by Corollary 4.2.2. -/
@[kb "miyake1989" "Theorem 4.2.5 (3) (proof), p. 107"]
theorem relIndex_Gamma1_Gamma0 (N : ℕ) [NeZero N] :
    (Gamma1 N).relIndex (Gamma0 N) = N.totient := by
  unfold Subgroup.relIndex Subgroup.index
  rw [Nat.card_congr (gamma0QuotGamma1Equiv N).toEquiv, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient]

/-- **Miyake, Theorem 4.2.5 (3)**, $N > 2$: $[\bar\Gamma_0(N) : \bar\Gamma_1(N)] = \varphi(N)/2$. -/
@[kb "miyake1989" "Theorem 4.2.5 (3), p. 106"]
theorem relIndex_adjoinNegOne_Gamma1 {N : ℕ} (hN : 2 < N) :
    ((adjoinNegOne (Gamma1 N)).relIndex (Gamma0 N) : ℚ) = N.totient / 2 := by
  have : NeZero N := ⟨by omega⟩
  have : Fact (2 < N) := ⟨hN⟩
  have hn : (-1 : SL(2, ℤ)) ∉ Gamma1 N := by
    intro h
    have := (Gamma1_mem N _ |>.1 h).1
    simp at this
    exact ZMod.neg_one_ne_one this
  have hm : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
    rw [Gamma0_mem]; simp
  have hle : adjoinNegOne (Gamma1 N) ≤ Gamma0 N :=
    sup_le (Gamma1_in_Gamma0 N) ((Subgroup.zpowers_le).2 hm)
  have h1 := Subgroup.relIndex_mul_relIndex (Gamma1 N) (adjoinNegOne (Gamma1 N)) (Gamma0 N)
    le_sup_left hle
  rw [relIndex_adjoinNegOne_eq_two _ hn, relIndex_Gamma1_Gamma0] at h1
  have h2 : (2 : ℚ) * ((adjoinNegOne (Gamma1 N)).relIndex (Gamma0 N) : ℕ) = N.totient := by
    exact_mod_cast h1
  linarith

/-- **Miyake, Theorem 4.2.5 (3)**, $N = 2$: $[\bar\Gamma_0(2) : \bar\Gamma_1(2)] = 1$
($= \varphi(2)$). -/
@[kb "miyake1989" "Theorem 4.2.5 (3), p. 106"]
theorem relIndex_adjoinNegOne_Gamma1_two : (adjoinNegOne (Gamma1 2)).relIndex (Gamma0 2) = 1 := by
  have hm : (-1 : SL(2, ℤ)) ∈ Gamma1 2 := by
    rw [Gamma1_mem]; simp
  have h1 : adjoinNegOne (Gamma1 2) = Gamma1 2 :=
    sup_eq_left.2 ((Subgroup.zpowers_le).2 hm)
  rw [h1, relIndex_Gamma1_Gamma0]
  exact Nat.totient_two

/-! ### Theorem 4.2.10 (elliptic part) -/

/-- **Miyake, Theorem 4.2.10**, first assertion: for $N \ge 2$ the group $\Gamma(N)$ has no
elliptic elements, i.e. no $\gamma \in \Gamma(N)$ has $\operatorname{disc}(\gamma) =
\operatorname{tr}(\gamma)^2 - 4 < 0$ as a real matrix (Mathlib's `Matrix.IsElliptic`). The
cusp count is `card_cuspOrbits_Gamma` and `card_cuspOrbits_Gamma_two`. -/
@[kb "miyake1989" "Theorem 4.2.10, p. 112"]
theorem not_isElliptic_of_mem_Gamma {N : ℕ} (hN : 2 ≤ N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma N) :
    ¬ ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ)).IsElliptic := by
  rw [Gamma_mem] at hγ
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  have d1 : (N : ℤ) ∣ γ 0 0 - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h1]; simp
  have d2 : (N : ℤ) ∣ γ 0 1 := by rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have d3 : (N : ℤ) ∣ γ 1 0 := by rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have d4 : (N : ℤ) ∣ γ 1 1 - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h4]; simp
  obtain ⟨a, ha⟩ := d1
  obtain ⟨b, hb⟩ := d2
  obtain ⟨c, hc⟩ := d3
  obtain ⟨d, hd⟩ := d4
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rwa [Matrix.det_fin_two] at this
  have hN0 : (0 : ℤ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℤ) ≤ N := by exact_mod_cast hN
  have e0 : γ 0 0 = 1 + N * a := by linarith
  have e3 : γ 1 1 = 1 + N * d := by linarith
  rw [e0, e3, hb, hc] at hdet
  have hs : a + d = -(N * (a * d - b * c)) := by
    have : (N : ℤ) * ((a + d) + N * (a * d - b * c)) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · omega
    · linarith
  have htr : γ 0 0 + γ 1 1 = 2 - N * N * (a * d - b * c) := by
    rw [e0, e3]; linarith
  intro hell
  unfold Matrix.IsElliptic at hell
  rw [Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two] at hell
  simp only [Matrix.map_apply] at hell
  have hdetR : ((γ 0 0 : ℤ) : ℝ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
    exact_mod_cast (by rw [e0, e3, hb, hc]; exact hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1)
  have hlt : (γ 0 0 + γ 1 1) ^ 2 < 4 := by
    have : (((γ 0 0 + γ 1 1 : ℤ) : ℝ)) ^ 2 < 4 := by
      push_cast; nlinarith
    exact_mod_cast this
  rw [htr] at hlt
  set t := a * d - b * c
  have hM : (4 : ℤ) ≤ N * N := by nlinarith
  rcases le_or_gt t 0 with ht | ht
  · have : 0 ≤ ((N : ℤ) * N) * (-t) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  · have : 4 ≤ ((N : ℤ) * N) * t := by nlinarith
    nlinarith

/-! ### Theorem 4.2.10 (cusp count) -/
/-- The stabiliser of the cusp `∞` in `SL(2, ℤ)`. -/
noncomputable def stabInfty : Subgroup SL(2, ℤ) :=
  (MulAction.stabilizer (GL (Fin 2) ℝ) (OnePoint.infty : OnePoint ℝ)).comap
    (SpecialLinearGroup.mapGL ℝ)

/-- Membership in `stabInfty` is vanishing of the lower-left entry. -/
lemma mem_stabInfty {g : SL(2, ℤ)} : g ∈ stabInfty ↔ g 1 0 = 0 := by
  simp [stabInfty, MulAction.mem_stabilizer_iff, OnePoint.smul_infty_eq_self_iff]

/-- The subgroup of `SL(2, ℤ)` of elements congruent mod `N` to an element fixing `∞`. -/
noncomputable def cuspK (N : ℕ) : Subgroup SL(2, ℤ) := (stabInfty.map (redMap N)).comap (redMap N)

/-- The cusp `g • ∞` is a cusp of `Γ(N)`. -/
lemma isCusp_mapGL (N : ℕ) [NeZero N] (g : SL(2, ℤ)) :
    IsCusp (SpecialLinearGroup.mapGL ℝ g • (OnePoint.infty : OnePoint ℝ))
      (Gamma N : Subgroup (GL (Fin 2) ℝ)) :=
  (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr (isCusp_SL2Z_iff'.mpr ⟨g, rfl⟩)

/-- The cusp orbit of `g • ∞`. -/
noncomputable def cuspPhi (N : ℕ) [NeZero N] (g : SL(2, ℤ)) :
    CuspOrbits (Gamma N : Subgroup (GL (Fin 2) ℝ)) :=
  ⟦⟨_, isCusp_mapGL N g⟩⟧

/-- Membership in `cuspK N`: `g` is congruent mod `N` (up to `Γ(N)`) to an element fixing `∞`. -/
lemma mem_cuspK {N : ℕ} {g : SL(2, ℤ)} : g ∈ cuspK N ↔ ∃ s ∈ stabInfty, g * s⁻¹ ∈ Gamma N := by
  simp only [cuspK, Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [← ker_redMap, MonoidHom.mem_ker, map_mul, map_inv, ← h, mul_inv_cancel]
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [← ker_redMap, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h
    exact h.symm

/-- Two cusps `g • ∞`, `g' • ∞` are `Γ(N)`-equivalent iff `g⁻¹ g' ∈ cuspK N`. -/
lemma cuspPhi_eq_iff {N : ℕ} [NeZero N] (g g' : SL(2, ℤ)) :
    cuspPhi N g = cuspPhi N g' ↔ g⁻¹ * g' ∈ cuspK N := by
  unfold cuspPhi
  rw [Quotient.eq_iff_equiv]
  constructor
  · rintro ⟨⟨a, ha⟩, h⟩
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 ha
    have h' : SpecialLinearGroup.mapGL ℝ γ • SpecialLinearGroup.mapGL ℝ g' • (OnePoint.infty : OnePoint ℝ) =
        SpecialLinearGroup.mapGL ℝ g • (OnePoint.infty : OnePoint ℝ) := congrArg Subtype.val h
    have hs : g⁻¹ * γ * g' ∈ stabInfty := by
      rw [stabInfty, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
      simp only [map_mul, map_inv, mul_smul]
      rw [h', inv_smul_smul]
    rw [mem_cuspK]
    refine ⟨g⁻¹ * γ * g', hs, ?_⟩
    have e : g⁻¹ * g' * (g⁻¹ * γ * g')⁻¹ = g⁻¹ * γ⁻¹ * g⁻¹⁻¹ := by group
    rw [e]
    exact Subgroup.Normal.conj_mem (self := Gamma_normal N) _ ((Gamma N).inv_mem hγ) _
  · rw [mem_cuspK]
    rintro ⟨s, hs, hΓ⟩
    have hγ : g * s * g'⁻¹ ∈ Gamma N := by
      have h1 := (Gamma N).inv_mem (Subgroup.Normal.conj_mem (self := Gamma_normal N) _ hΓ g)
      have e : (g * (g⁻¹ * g' * s⁻¹) * g⁻¹)⁻¹ = g * s * g'⁻¹ := by group
      rwa [e] at h1
    refine ⟨⟨SpecialLinearGroup.mapGL ℝ (g * s * g'⁻¹), Subgroup.mem_map_of_mem _ hγ⟩, ?_⟩
    apply Subtype.ext
    have hs' : SpecialLinearGroup.mapGL ℝ s • (OnePoint.infty : OnePoint ℝ) = OnePoint.infty :=
      MulAction.mem_stabilizer_iff.1 hs
    show SpecialLinearGroup.mapGL ℝ (g * s * g'⁻¹) • SpecialLinearGroup.mapGL ℝ g' • (OnePoint.infty : OnePoint ℝ) = _
    simp only [map_mul, map_inv, mul_smul, inv_smul_smul, hs']

/-- `CuspOrbits Γ(N)` is in bijection with `SL(2, ℤ) ⧸ cuspK N`. -/
lemma card_cuspOrbits_eq_index (N : ℕ) [NeZero N] :
    Nat.card (CuspOrbits (Gamma N : Subgroup (GL (Fin 2) ℝ))) = (cuspK N).index := by
  rw [Subgroup.index]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.lift (cuspPhi N) (fun a b hab => ?_)) ⟨?_, ?_⟩)
  · exact (cuspPhi_eq_iff a b).2 (QuotientGroup.leftRel_apply.1 hab)
  · intro x y
    refine Quotient.inductionOn₂ x y (fun a b h => ?_)
    exact Quotient.sound (QuotientGroup.leftRel_apply.2 ((cuspPhi_eq_iff a b).1 h))
  · intro q
    obtain ⟨⟨c, hc⟩, rfl⟩ := Quotient.exists_rep q
    have hc' : IsCusp c (Gamma N : Subgroup (GL (Fin 2) ℝ)) := hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff'] at hc'
    obtain ⟨g, rfl⟩ := hc'
    exact ⟨Quotient.mk'' g, rfl⟩

/-- The sign `±1` in `ZMod N` indexed by a boolean. -/
def sgn (N : ℕ) (s : Bool) : ZMod N := if s then 1 else -1

/-- The upper triangular matrix `±[[1, b], [0, 1]]` in `SL(2, ZMod N)`. -/
def eS (N : ℕ) (s : Bool) (b : ZMod N) : SL(2, ZMod N) :=
  ⟨!![sgn N s, b; 0, sgn N s], by
    cases s <;> simp [sgn, Matrix.det_fin_two]⟩

/-- The image of the stabiliser of `∞` in `SL(2, ZMod N)`. -/
noncomputable def hStab (N : ℕ) : Subgroup SL(2, ZMod N) := stabInfty.map (redMap N)

/-- Entries of the reduction. -/
lemma redMap_apply {N : ℕ} (g : SL(2, ℤ)) (i j : Fin 2) :
    ((redMap N g : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) i j = ((g i j : ℤ) : ZMod N) := rfl

lemma mem_hStab {N : ℕ} [NeZero N] (h : SL(2, ZMod N)) :
    h ∈ hStab N ↔ ∃ s b, h = eS N s b := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    replace hg := mem_stabInfty.1 hg
    have hdet : g 0 0 * g 1 1 = 1 := by
      have := g.det_coe
      rw [Matrix.det_fin_two, hg] at this
      simpa using this
    refine ⟨decide (g 0 0 = 1), ((g 0 1 : ℤ) : ZMod N), ?_⟩
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [eS, sgn, h1, h2, hg]
    · have : ¬ (g 0 0 = 1) := by rw [h1]; norm_num
      ext i j
      fin_cases i <;> fin_cases j <;> simp [eS, sgn, h1, h2, hg]
  · rintro ⟨s, b, rfl⟩
    let σ : ℤ := if s then 1 else -1
    refine ⟨⟨!![σ, (b.val : ℤ); 0, σ], by cases s <;> simp [σ, Matrix.det_fin_two]⟩, ?_, ?_⟩
    · exact mem_stabInfty.2 (by simp)
    · ext i j
      fin_cases i <;> fin_cases j <;> cases s <;> (erw [redMap_apply]; simp [eS, sgn, σ])

/-- The index of `cuspK N` times the order of `hStab N` is the order of `SL(2, ZMod N)`. -/
lemma card_hStab_mul_index (N : ℕ) [NeZero N] :
    Nat.card (hStab N) * Nat.card (CuspOrbits (Gamma N : Subgroup (GL (Fin 2) ℝ))) =
      Nat.card SL(2, ZMod N) := by
  rw [card_cuspOrbits_eq_index, cuspK, Subgroup.index_comap_of_surjective _
    (SL2_reduction_surjective N)]
  exact Subgroup.card_mul_index _

lemma card_hStab_of_three {N : ℕ} [NeZero N] (hN : 3 ≤ N) : Nat.card (hStab N) = 2 * N := by
  have : Fact (2 < N) := ⟨hN⟩
  have hinj : Function.Injective (fun p : Bool × ZMod N => eS N p.1 p.2) := by
    rintro ⟨s, b⟩ ⟨s', b'⟩ h
    have h1 := congrArg (fun m : SL(2, ZMod N) => (m : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 0) h
    have h2 := congrArg (fun m : SL(2, ZMod N) => (m : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 1) h
    simp only [eS] at h1 h2
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at h1 h2
    have hs : s = s' := by
      cases s <;> cases s' <;> simp [sgn] at h1 ⊢
      · exact ZMod.neg_one_ne_one h1
      · exact ZMod.neg_one_ne_one h1.symm
    subst hs
    simp_all
  have e : Nat.card (hStab N) = Nat.card (Set.range (fun p : Bool × ZMod N => eS N p.1 p.2)) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun h => by
      rw [mem_hStab]; simp [eq_comm]))
  rw [e, Nat.card_range_of_injective hinj, Nat.card_prod]
  simp [ZMod.card]

lemma card_hStab_two : Nat.card (hStab 2) = 2 := by
  have hm : (-1 : ZMod 2) = 1 := by decide
  have hinj : Function.Injective (fun b : ZMod 2 => eS 2 true b) := by
    intro b b' h
    have h2 := congrArg (fun m : SL(2, ZMod 2) => (m : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 1) h
    simpa [eS] using h2
  have e : Nat.card (hStab 2) = Nat.card (Set.range (fun b : ZMod 2 => eS 2 true b)) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun h => by
      rw [mem_hStab]
      constructor
      · rintro ⟨s, b, rfl⟩
        exact ⟨b, by cases s <;> simp [eS, sgn, hm] <;> rfl⟩
      · rintro ⟨b, rfl⟩
        exact ⟨true, b, rfl⟩))
  rw [e, Nat.card_range_of_injective hinj]
  simp [ZMod.card]

/-- **Miyake, Theorem 4.2.10**, cusp count for $N \ge 3$: $\Gamma(N)$ has
$\tfrac12 N^2 \prod_{p \mid N}(1 - p^{-2})$ inequivalent cusps (Mathlib's `CuspOrbits`, the orbits of
$\Gamma(N) \subset \mathrm{GL}_2(\mathbb R)$ on its cusps in $\mathbb P^1(\mathbb R)$). -/
@[kb "miyake1989" "Theorem 4.2.10, p. 112"]
theorem card_cuspOrbits_Gamma {N : ℕ} (hN : 3 ≤ N) :
    (Nat.card (CuspOrbits (Gamma N : Subgroup (GL (Fin 2) ℝ))) : ℚ) =
      N ^ 2 / 2 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by
  have : NeZero N := ⟨by omega⟩
  have h := card_hStab_mul_index N
  rw [card_hStab_of_three hN] at h
  have h' : ((2 * N : ℕ) : ℚ) * (Nat.card (CuspOrbits (Gamma N : Subgroup (GL (Fin 2) ℝ))) : ℚ) =
      (Nat.card SL(2, ZMod N) : ℚ) := by exact_mod_cast h
  rw [card_SL2_ZMod] at h'
  have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  push_cast at h'
  field_simp
  field_simp at h'
  nlinarith [h']

/-- **Miyake, Theorem 4.2.10**, cusp count for $N = 2$: $\Gamma(2)$ has three inequivalent cusps. -/
@[kb "miyake1989" "Theorem 4.2.10, p. 112"]
theorem card_cuspOrbits_Gamma_two :
    Nat.card (CuspOrbits (Gamma 2 : Subgroup (GL (Fin 2) ℝ))) = 3 := by
  have h := card_hStab_mul_index 2
  rw [card_hStab_two] at h
  have hc : Nat.card SL(2, ZMod 2) = 6 := by
    have := card_SL2_ZMod 2
    have h6 : (Nat.card SL(2, ZMod 2) : ℚ) = 6 := by
      rw [this]
      norm_num [Nat.primeFactors, Nat.primeFactorsList]
    exact_mod_cast h6
  omega

end ModularFormsKB.Miyake
