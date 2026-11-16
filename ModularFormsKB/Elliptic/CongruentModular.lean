import ModularFormsKB.Elliptic.F32Newform
import TauCeti.NumberTheory.ModularForms.Newforms.Twist
import TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform
import TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.Classification

/-!
# The congruent number curves have newforms

$E_n : y^2 = x^3 - n^2x$ (`congruentCurve n`). Its $L$-function has coefficients
$\left(\frac nm\right)b(m)$ with $b = $ `f32Coeff` the coefficients of $f_{32}$ (`LFunction_congruentCurve_eq`,
unconditional).
- `F32Newform` ($f_{32}$ is a Tau Ceti newform of level $32$) is proved in `F32Newform.lean` (`f32Newform`).
- `QuadraticTwistNewform` (for quadratic characters; Atkin–Li 1978, Theorem 3.1 [unverified]): the twist of
  a newform of level $N$, weight $2$ and trivial nebentypus by a primitive quadratic character of conductor $r$ prime
  to $N$ is a newform of level $Nr^2$ and trivial nebentypus. It is no longer used by the headline: the twist is
  Tau Ceti's `Newform.primitiveTwist`, its coefficients and its level at $2$ are proved here, and its level at the
  primes $p \mid n$ in `TwistLevel.lean`, so that the headline `hasNewform_congruentCurve`
  (in `TwistLevel.lean`) is unconditional. The general local statement `TwistLevelRamified` stays defined, unused.

Proved here:
- `hasNewform_congruentCurve_one`: $E_1$ has the newform $f_{32}$ of level $32$, unconditional;
- `jacobiChar`: for odd $n$, the Dirichlet character $m \mapsto \left(\frac mn\right)$ modulo $n$; primitive and
  quadratic for squarefree $n$ (`jacobiChar_isPrimitive`, `jacobiChar_sq`);
- `congruentCoeff_eq_jacobiChar`: $\left(\frac nm\right)b(m) = \left(\frac mn\right)b(m)$ for odd $n$, since $b(m) = 0$
  unless $m \equiv 1 \bmod 4$ (`mod_four_eq_one_of_f32Coeff_ne_zero`) and quadratic reciprocity;
- `thirtyTwo_dvd_f32TwistLevel`, `f32TwistLevel_eq`: the level of $f_{32} \otimes \chi_n$ is divisible by $32$
  (by twisting back), and is $32n^2$ given `TwistLevelRamified`;
- `hasNewform_of_level_eq`: a newform of level $32n^2$ with trivial nebentypus and $a_p = \chi_n(p)b(p)$ at the primes
  $p \nmid 2n$ has all the coefficients of $L(E_n, s)$;
- `hasNewform_congruentCurve_of_level_eq`: for odd squarefree $n$, $E_n$ has the newform $f_{32} \otimes \chi_n$ of
  level $32n^2$ once that is its level; `TwistLevel.lean` proves it is (`hasNewform_congruentCurve`, unconditional),
  and `hasNewform_congruentCurve_of_twistLevelRamified` keeps the earlier conditional form;
- `TwistLevelRamified.of_quadraticTwistNewform`: the remaining input is implied by the old one.

Not done here: that $32n^2$ is the geometric conductor of $E_n$ (Tate's algorithm at $2$ and at $p \mid n$), LE
recorded.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups

namespace ModularFormsKB.Elliptic

open HeckeRing.GL2 ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves TauCeti

/-- **Quadratic twists of newforms** (named statement, for quadratic characters; Atkin–Li 1978,
Theorem 3.1 [unverified], Shimura 1971, Proposition 3.64 [unverified]): for a newform $f$ of level $N$, weight $2$ and
trivial nebentypus and a primitive Dirichlet character $\chi$ modulo $r$ prime to $N$ with $\chi^2 = 1$,
$\sum\chi(m)a_m(f)q^m$ is a newform of level $Nr^2$ with trivial nebentypus. -/
structure QuadraticTwistNewform : Prop where
  exists_twist : ∀ (N r : ℕ) [NeZero N] [NeZero r] (f : Newform N 2), f.χ = 1 → r.Coprime N →
    ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive → χ ^ 2 = 1 →
      ∃ g : Newform (N * r ^ 2) 2, g.χ = 1 ∧
        ∀ m : ℕ, (qExpansion 1 g.toCuspForm).coeff m = χ m * (qExpansion 1 f.toCuspForm).coeff m

/-- **The newform of $E_1$**: $E_1 : y^2 = x^3 - x$ has the newform $f_{32}$ of level $32$. Unconditional
(`f32Newform`). -/
theorem hasNewform_congruentCurve_one :
    ∃ f : Newform 32 2, HasNewform (congruentCurve 1) 32 f := by
  obtain ⟨f, hχ, hc⟩ := f32Newform.exists_newform
  refine ⟨f, hχ, fun m ↦ ?_⟩
  rw [hc, LFunction_congruentCurve_eq squarefree_one]
  simp [congruentCoeff]

private lemma jac_congr {n : ℕ} {a b : ℤ} (h : (a : ZMod n) = (b : ZMod n)) :
    jacobiSym a n = jacobiSym b n :=
  jacobiSym.mod_left' ((ZMod.intCast_eq_intCast_iff' a b n).1 h)

private lemma jac_val_cast {n : ℕ} [NeZero n] (x : ZMod n) : (((x.val : ℕ) : ℤ) : ZMod n) = x := by
  simp

/-- The Jacobi symbol $m \mapsto \left(\frac mn\right)$ as a Dirichlet character modulo $n$ ($n$ odd). -/
noncomputable def jacobiChar (n : ℕ) (hn : Odd n) : DirichletCharacter ℂ n :=
  haveI : NeZero n := ⟨hn.pos.ne'⟩
  ({ toFun := fun x ↦ ((jacobiSym ((x.val : ℕ) : ℤ) n : ℤ) : ℂ)
     map_one' := by
       have : jacobiSym (((1 : ZMod n).val : ℕ) : ℤ) n = 1 := by
         rw [jac_congr (b := 1) (by rw [jac_val_cast]; simp), jacobiSym.one_left]
       rw [this, Int.cast_one]
     map_mul' := by
       intro x y
       have : jacobiSym (((x * y).val : ℕ) : ℤ) n =
           jacobiSym (((x.val : ℕ) : ℤ)) n * jacobiSym (((y.val : ℕ) : ℤ)) n := by
         rw [← jacobiSym.mul_left, jac_congr (b := ((x.val : ℕ) : ℤ) * ((y.val : ℕ) : ℤ))]
         push_cast
         simp
       rw [this, Int.cast_mul]
     map_nonunit' := by
       intro x hx
       have : jacobiSym (((x.val : ℕ) : ℤ)) n = 0 := by
         rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
         intro h1
         apply hx
         have := (ZMod.isUnit_iff_coprime x.val n).2 h1
         simpa using this
       rw [this, Int.cast_zero] } : MulChar (ZMod n) ℂ)

theorem jacobiChar_apply (n : ℕ) (hn : Odd n) (m : ℕ) : jacobiChar n hn m = (jacobiSym m n : ℂ) := by
  haveI : NeZero n := ⟨hn.pos.ne'⟩
  show ((jacobiSym (((m : ZMod n).val : ℕ) : ℤ) n : ℤ) : ℂ) = _
  rw [jac_congr (b := (m : ℤ)) (by simp)]

private lemma jacobiChar_unit_apply {n : ℕ} (hn : Odd n) (x : ZMod n) :
    haveI : NeZero n := ⟨hn.pos.ne'⟩
    jacobiChar n hn x = ((jacobiSym ((x.val : ℕ) : ℤ) n : ℤ) : ℂ) := rfl

/-- The key non-factorization: for squarefree odd $n$ and a proper divisor $d$, the Jacobi character does not
factor through level $d$. -/
private lemma jacobiChar_not_factorsThrough {n : ℕ} (hn : Odd n) (hsq : Squarefree n) {d : ℕ} (hd : d ∣ n)
    (hne : d ≠ n) : ¬ (jacobiChar n hn).FactorsThrough d := by
  haveI : NeZero n := ⟨hn.pos.ne'⟩
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
  obtain ⟨k, hk⟩ := hd
  have hk1 : k ≠ 1 := by rintro rfl; exact hne (by simpa using hk.symm)
  have hp : (Nat.minFac k).Prime := Nat.minFac_prime hk1
  obtain ⟨k', hk'⟩ := Nat.minFac_dvd k
  set p := Nat.minFac k with hpdef
  set r := d * k' with hr
  have hnr : n = p * r := by rw [hk, hk', hr]; ring
  have hp0 : p ≠ 0 := hp.ne_zero
  have hr0 : r ≠ 0 := by
    intro h0; rw [h0] at hnr; simp at hnr; exact hn.pos.ne' hnr
  have hcop : Nat.Coprime p r := (Nat.squarefree_mul_iff.1 (hnr ▸ hsq)).1
  have hp2 : p ≠ 2 := by
    rintro h2
    have : 2 ∣ n := by rw [hnr, h2]; exact dvd_mul_right _ _
    exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 this)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  obtain ⟨u, hu1, hu2⟩ := Nat.chineseRemainder hcop g.val 1
  have hJ : jacobiSym (u : ℤ) n = -1 := by
    rw [hnr, jacobiSym.mul_right' _ hp0 hr0]
    have h1 : jacobiSym (u : ℤ) r = 1 := by
      rw [jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast hu2), jacobiSym.one_left]
    have h2 : jacobiSym (u : ℤ) p = -1 := by
      rw [jacobiSym.mod_left' (a₂ := (g.val : ℤ)) (by exact_mod_cast hu1), ← jacobiSym.legendreSym.to_jacobiSym,
        legendreSym.eq_neg_one_iff]
      simpa using hg
    rw [h1, h2, mul_one]
  have hχu : jacobiChar n hn (u : ZMod n) = -1 := by
    rw [jacobiChar_apply, hJ]; simp
  have hunit : IsUnit (u : ZMod n) := by
    by_contra h
    have := MulChar.map_nonunit (jacobiChar n hn) h
    rw [hχu] at this
    simp at this
  intro hker
  have hmem : hunit.unit ∈ (ZMod.unitsMap (show d ∣ n from ⟨k, hk⟩)).ker := by
    rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val]
    have : ((hunit.unit : (ZMod n)ˣ) : ZMod n) = (u : ZMod n) := rfl
    rw [this, Units.val_one, ZMod.cast_natCast (show d ∣ n from ⟨k, hk⟩)]
    have hdr : d ∣ r := dvd_mul_right _ _
    have h3 := (ZMod.natCast_eq_natCast_iff u 1 d).2 (Nat.ModEq.of_dvd hdr hu2)
    simpa using h3
  have := hker hmem
  rw [MonoidHom.mem_ker] at this
  have h2 := congrArg (fun z : ℂˣ ↦ (z : ℂ)) this
  simp only [MulChar.coe_toUnitHom, Units.val_one] at h2
  have : (u : ZMod n) = ((hunit.unit : (ZMod n)ˣ) : ZMod n) := rfl
  rw [← this, hχu] at h2
  norm_num at h2

theorem jacobiChar_isPrimitive {n : ℕ} (hn : Odd n) (hsq : Squarefree n) : (jacobiChar n hn).IsPrimitive := by
  haveI : NeZero n := ⟨hn.pos.ne'⟩
  by_contra hne
  exact jacobiChar_not_factorsThrough hn hsq (DirichletCharacter.conductor_dvd_level _) hne
    (DirichletCharacter.factorsThrough_conductor _)

theorem jacobiChar_sq (n : ℕ) (hn : Odd n) : jacobiChar n hn ^ 2 = 1 := by
  haveI : NeZero n := ⟨hn.pos.ne'⟩
  refine MulChar.ext fun u ↦ ?_
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  have hx : ((u : ZMod n)) = ((u : ZMod n).val : ℕ) := by simp
  rw [hx, jacobiChar_apply, ← Int.cast_pow, jacobiSym.sq_one]
  · simp
  · rw [Int.gcd_natCast_natCast]
    have hc : Nat.Coprime ((u : ZMod n).val) n := by
      have := u.isUnit
      rw [hx] at this
      exact (ZMod.isUnit_iff_coprime _ _).1 this
    exact hc

/-- For odd $n$: $\left(\frac nm\right)b(m) = \left(\frac mn\right)b(m)$ for every $m$. -/
theorem congruentCoeff_eq_jacobiChar {n : ℕ} (hn : Odd n) (m : ℕ) :
    (congruentCoeff n m : ℂ) = jacobiChar n hn m * (f32Coeff m : ℂ) := by
  by_cases h0 : f32Coeff m = 0
  · simp [congruentCoeff, h0]
  · have h4 := mod_four_eq_one_of_f32Coeff_ne_zero h0
    rw [jacobiChar_apply, congruentCoeff]
    have := jacobiSym.quadratic_reciprocity_one_mod_four' hn h4
    push_cast
    rw [this]

/-- The newforms of $E_n$ from the general Atkin–Li input `QuadraticTwistNewform` (the first form of the
statement); superseded by `hasNewform_congruentCurve` (unconditional, `TwistLevel.lean`). -/
theorem hasNewform_congruentCurve_of_quadraticTwistNewform (hT : QuadraticTwistNewform) {n : ℕ} [NeZero n]
    (hn : Odd n) (hsq : Squarefree n) :
    ∃ f : Newform (32 * n ^ 2) 2, HasNewform (congruentCurve n) (32 * n ^ 2) f := by
  obtain ⟨f, hχ, hc⟩ := f32Newform.exists_newform
  have hcop : Nat.Coprime n 32 := by
    have := (hn.coprime_two_right).pow_right 5
    simpa using this
  obtain ⟨g, hg1, hg⟩ := hT.exists_twist 32 n f hχ hcop (jacobiChar n hn) (jacobiChar_isPrimitive hn hsq)
    (jacobiChar_sq n hn)
  refine ⟨g, hg1, fun m ↦ ?_⟩
  rw [hg m, hc m, ← congruentCoeff_eq_jacobiChar hn m, LFunction_congruentCurve_eq hsq]

/-! ### The twist of $f_{32}$ by $\chi_n$: Tau Ceti's primitive twist

Tau Ceti's `Newform.primitiveTwist f ψ` is the newform attached to $f \otimes \psi$, of a level dividing every common
multiple of $NM$ and $M^2$ (`primitiveTwistLevel_dvd`); its sharp level is not determined there. For $f = f_{32}$ and
$\psi = \chi_n$ the level $R$ divides $32n^2$. Twisting back by $\chi_n$ returns $f_{32}$ of level $32$, whose level
divides every common multiple of $Rn$ and $n^2$; if $32 \nmid R$ then $R \mid 16n^2$ and $32 \mid 16n^3$, impossible for
odd $n$. So $32 \mid R$. That $p^2 \mid R$ at the primes $p \mid n$ is the general statement `TwistLevelRamified`;
for $f_{32}$ it is proved in `TwistLevel.lean` (`f32TwistLevel_eq_of_odd`) from the Fricke involution. -/

/-- **Twists by a ramified quadratic character have level divisible by $p^2$** (named statement; Atkin–Li 1978,
Theorem 3.1 [unverified], the local part at a prime of the conductor; Shimura 1971, Proposition 3.64
[unverified]): for a newform $f$ of level $N$, weight $2$ and trivial nebentypus, a primitive Dirichlet character
$\chi$ modulo $r$ prime to $N$ with $\chi^2 = 1$, and a prime $p \mid r$, $p^2$ divides the level of the primitive
twist of $f$ by $\chi$ (Tau Ceti `Newform.primitiveTwistLevel`). Atkin–Li give the exact level $Nr^2$; this is the
part of it that the comparison of coefficients does not give. It follows from `QuadraticTwistNewform`
(`TwistLevelRamified.of_quadraticTwistNewform`). -/
structure TwistLevelRamified : Prop where
  sq_dvd : ∀ (N r : ℕ) [NeZero N] [NeZero r] (f : Newform N 2), f.χ = 1 → r.Coprime N →
    ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive → χ ^ 2 = 1 →
      ∀ p : ℕ, p.Prime → p ∣ r → p ^ 2 ∣ f.primitiveTwistLevel χ

/-- The square of the unit character of a quadratic Dirichlet character, read at a multiple, is trivial. -/
theorem toUnitHom_comp_sq_eq_one {r L : ℕ} (χ : DirichletCharacter ℂ r) (hχ2 : χ ^ 2 = 1) (h : r ∣ L) :
    (χ.toUnitHom.comp (ZMod.unitsMap h)) ^ 2 = 1 := by
  ext u
  have := congrArg (fun ψ : DirichletCharacter ℂ r ↦ ψ ((ZMod.unitsMap h u : (ZMod r)ˣ) : ZMod r)) hχ2
  simp only [MulChar.pow_apply_coe, MulChar.one_apply_coe] at this
  simpa [MulChar.coe_toUnitHom] using this

/-- `TwistLevelRamified` is weaker than `QuadraticTwistNewform`: the newform of level $Nr^2$ given by the latter is
the primitive twist (uniqueness, Tau Ceti `level_eq_primitiveTwistLevel_and_coe_eq_primitiveTwist`). -/
theorem TwistLevelRamified.of_quadraticTwistNewform (h : QuadraticTwistNewform) : TwistLevelRamified := by
  refine ⟨fun N r _ _ f hf hrN χ hχ hχ2 p hp hpr ↦ ?_⟩
  obtain ⟨g, hg1, hg⟩ := h.exists_twist N r f hf hrN χ hχ hχ2
  have hNL : N ∣ N * r ^ 2 := dvd_mul_right _ _
  have hML : r ∣ N * r ^ 2 := Dvd.dvd.mul_left (dvd_pow_self r two_ne_zero) N
  have hchi : g.χ.comp (ZMod.unitsMap (dvd_refl _)) =
      f.χ.comp (ZMod.unitsMap hNL) * (χ.toUnitHom.comp (ZMod.unitsMap hML)) ^ 2 := by
    rw [hg1, hf, toUnitHom_comp_sq_eq_one χ hχ2 hML]
    ext u
    simp
  obtain ⟨hR, -⟩ := Newform.level_eq_primitiveTwistLevel_and_coe_eq_primitiveTwist f χ g (dvd_refl _) hNL hML
    hchi (S := ∅) fun q _ _ _ ↦ by rw [hg q]
  rw [← hR]
  exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hpr 2) N

theorem coprime_n_thirtyTwo {n : ℕ} (hn : Odd n) : Nat.Coprime n 32 := by
  have := (hn.coprime_two_right).pow_right 5
  simpa using this

/-- The level of $f_{32} \otimes \chi_n$ divides $32n^2$. -/
theorem f32TwistLevel_dvd {n : ℕ} [NeZero n] (hn : Odd n) :
    f32NewformDef.primitiveTwistLevel (jacobiChar n hn) ∣ 32 * n ^ 2 :=
  Newform.primitiveTwistLevel_dvd _ _ ⟨n, by ring⟩ ⟨32, by ring⟩

/-- **The $2$-part of the level of $f_{32} \otimes \chi_n$ is $32$**, by twisting back. -/
theorem thirtyTwo_dvd_f32TwistLevel {n : ℕ} [NeZero n] (hn : Odd n) :
    32 ∣ f32NewformDef.primitiveTwistLevel (jacobiChar n hn) := by
  set R := f32NewformDef.primitiveTwistLevel (jacobiChar n hn) with hRdef
  by_contra h32
  have hcop : Nat.Coprime 32 (n ^ 2) := (coprime_n_thirtyTwo hn).symm.pow_right 2
  have hR := f32TwistLevel_dvd hn
  have hsplit : R = Nat.gcd R 32 * Nat.gcd R (n ^ 2) := by
    rw [← Nat.Coprime.gcd_mul R hcop, Nat.gcd_eq_left hR]
  have hg32 : Nat.gcd R 32 ∣ 16 := by
    have hd : Nat.gcd R 32 ∣ 2 ^ 5 := Nat.gcd_dvd_right R 32
    obtain ⟨i, hi, hiM⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    have hne : Nat.gcd R 32 ≠ 32 := fun h ↦ h32 (h ▸ Nat.gcd_dvd_left R 32)
    rw [hiM] at hne ⊢
    have : i ≠ 5 := by rintro rfl; exact hne rfl
    exact Nat.pow_dvd_pow 2 (by omega : i ≤ 4)
  have hR16 : R ∣ 16 * n ^ 2 := by
    rw [hsplit]
    exact Nat.mul_dvd_mul hg32 (Nat.gcd_dvd_right R (n ^ 2))
  have hback := Newform.primitiveTwistLevel_dvd (L := 16 * n ^ 3)
    (f32NewformDef.primitiveTwist (jacobiChar n hn)) (jacobiChar n hn)⁻¹
    (by rw [show 16 * n ^ 3 = (16 * n ^ 2) * n by ring]; exact Nat.mul_dvd_mul_right hR16 n)
    ⟨16 * n, by ring⟩
  rw [Newform.primitiveTwistLevel_primitiveTwist_inv] at hback
  have h2 : 2 ∣ n ^ 3 := by
    have : 16 * 2 ∣ 16 * n ^ 3 := by simpa using hback
    exact (Nat.mul_dvd_mul_iff_left (by norm_num)).1 this
  exact (Nat.not_even_iff_odd.2 (hn.pow (n := 3))) (even_iff_two_dvd.2 h2)

/-- With `TwistLevelRamified`, **the level of $f_{32} \otimes \chi_n$ is $32n^2$** ($n$ odd squarefree). -/
theorem f32TwistLevel_eq {n : ℕ} [NeZero n] (hn : Odd n) (hT : TwistLevelRamified) (hsq : Squarefree n) :
    f32NewformDef.primitiveTwistLevel (jacobiChar n hn) = 32 * n ^ 2 := by
  set R := f32NewformDef.primitiveTwistLevel (jacobiChar n hn) with hRdef
  have hR0 : R ≠ 0 := NeZero.ne R
  refine Nat.dvd_antisymm (f32TwistLevel_dvd hn) ?_
  have hn2 : n ^ 2 ∣ R := by
    rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 (NeZero.ne n)) hR0]
    intro p
    rw [Nat.factorization_pow]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    by_cases hp : p.Prime
    · by_cases hpn : p ∣ n
      · have h1 : n.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one (NeZero.ne n)).1 hsq p
        have h2 := hT.sq_dvd 32 n f32NewformDef f32Eigenform_χ (coprime_n_thirtyTwo hn)
          (jacobiChar n hn) (jacobiChar_isPrimitive hn hsq) (jacobiChar_sq n hn) p hp hpn
        have h3 := (hp.pow_dvd_iff_le_factorization hR0).1 h2
        calc 2 * n.factorization p ≤ 2 := by omega
          _ ≤ _ := h3
      · simp [Nat.factorization_eq_zero_of_not_dvd hpn]
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  exact ((coprime_n_thirtyTwo hn).symm.pow_right 2).mul_dvd_of_dvd_of_dvd
    (thirtyTwo_dvd_f32TwistLevel hn) hn2

/-- The coefficients $c(m) = \left(\frac nm\right)b(m)$ at prime powers $p^k$, $k \ge 1$, vanish for $p \mid 2n$. -/
theorem congruentCoeff_prime_pow_of_dvd {n p k : ℕ} (hp : p.Prime) (hpn : p ∣ 2 * n) (hk : 0 < k) :
    congruentCoeff n (p ^ k) = 0 := by
  rcases (Nat.Prime.dvd_mul hp).1 hpn with h2 | hpn'
  · have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
    subst this
    have : f32Coeff (2 ^ k) = 0 := f32Coeff_of_even (by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact ⟨2 ^ j, by ring⟩)
    simp [congruentCoeff, this]
  · have hJ : jacobiSym n p = 0 := by
      rw [jacobiSym.eq_zero_iff]
      refine ⟨hp.ne_zero, fun h1 ↦ ?_⟩
      have : (p : ℤ) ∣ Int.gcd n p := Int.dvd_coe_gcd (by exact_mod_cast hpn') dvd_rfl
      rw [h1] at this
      exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
    simp [congruentCoeff, jacobiSym.pow_right, hJ, zero_pow hk.ne']

/-- The Hecke recursion of $c(m) = \left(\frac nm\right)b(m)$ at a prime $p \nmid 2n$. -/
theorem congruentCoeff_prime_pow_add_two {n p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ 2 * n) (j : ℕ) :
    congruentCoeff n (p ^ (j + 2)) =
      congruentCoeff n p * congruentCoeff n (p ^ (j + 1)) - p * congruentCoeff n (p ^ j) := by
  have hp2 : p ≠ 2 := fun h ↦ hpn (h ▸ dvd_mul_right 2 n)
  have hpn' : ¬ p ∣ n := fun h ↦ hpn (dvd_mul_of_dvd_right h 2)
  have hJ2 : jacobiSym n p ^ 2 = 1 := by
    apply jacobiSym.sq_one
    rw [Int.gcd_natCast_natCast]
    exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn')
  simp only [congruentCoeff, jacobiSym.pow_right, f32Coeff_prime_pow_add_two hp hp2 j]
  linear_combination (-(p : ℤ) * jacobiSym n p ^ j * f32Coeff (p ^ j)) * hJ2

/-- **The coefficients of a newform of level $32n^2$ twisting $f_{32}$ by $\chi_n$**: a newform $g$ of level
$R = 32n^2$ with trivial nebentypus and $a_p(g) = \chi_n(p)b(p)$ at the primes $p \nmid 2n$ has
$a_m(g) = \left(\frac nm\right)b(m)$ for every $m$, i.e. $E_n$ has the newform $g$. Both sides are multiplicative
(Tau Ceti `Eigenform.qExpansion_coeff_mul`, through `Newform.toEigenform`), agree at the primes $p \nmid 2n$ and
satisfy the same Hecke recursion there; at $p \mid 2n$ both vanish on $p^k$, $k \ge 1$, since $p^2 \mid R$ and the
nebentypus is trivial (Tau Ceti `qExpansion_coeff_prime_ne_zero_iff`). -/
theorem hasNewform_of_level_eq {n : ℕ} [NeZero n] (hn : Odd n) (hsq : Squarefree n) {R : ℕ} [NeZero R]
    (g : Newform R 2) (hR : R = 32 * n ^ 2) (hgχ : g.χ = 1)
    (hgp : ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * n →
      (qExpansion 1 g.toCuspForm).coeff p = jacobiChar n hn p * (f32Coeff p : ℂ)) :
    HasNewform (congruentCurve n) R g := by
  refine ⟨hgχ, fun m ↦ ?_⟩
  rw [LFunction_congruentCurve_eq hsq]
  set a : ℕ → ℂ := fun m ↦ (qExpansion 1 g.toCuspForm).coeff m with ha
  have h₁ : a 1 = 1 := g.isNorm
  have hE1 : (qExpansion 1 g.toEigenform.toCuspForm).coeff 1 = 1 := by
    rw [Newform.toEigenform_toCuspForm]; exact g.isNorm
  have hmul : ∀ u v : ℕ, u.Coprime v → a (u * v) = a u * a v := fun u v huv ↦ by
    simpa [ha, Newform.toEigenform_toCuspForm] using g.toEigenform.qExpansion_coeff_mul hE1 huv
  have hrec : ∀ p : ℕ, p.Prime → ∀ r : ℕ, a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) -
      (MulChar.ofUnitHom g.χ : DirichletCharacter ℂ R) p * (p : ℂ) ^ ((2 : ℤ) - 1) * a (p ^ r) := by
    intro p hp r
    simpa [ha, Newform.toEigenform_toCuspForm, Newform.toEigenform_χ] using
      g.toEigenform.qExpansion_coeff_prime_pow_add_two hE1 hp r
  have h0 : a 0 = 0 := CuspFormClass.qExpansion_coeff_zero g.toCuspForm one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map R)
  let A : ArithmeticFunction ℂ := ⟨a, h0⟩
  have hA : A.IsMultiplicative := ⟨h₁, fun {u v} huv ↦ hmul u v huv⟩
  let C : ArithmeticFunction ℂ :=
    ⟨fun m ↦ (congruentCoeff n m : ℂ), by simp [congruentCoeff, f32Coeff_zero]⟩
  have hC : C.IsMultiplicative := by
    refine ⟨by simp [C, congruentCoeff, f32Coeff_one], fun {u v} huv ↦ ?_⟩
    have := (isMultiplicative_congruentArith n).map_mul_of_coprime huv
    simp only [congruentArith_apply] at this
    simp [C, this]
  have key : A = C := by
    refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hA _ hC).2 fun p k hp ↦ ?_
    show a (p ^ k) = (congruentCoeff n (p ^ k) : ℂ)
    by_cases hpn : p ∣ 2 * n
    · -- a prime of the level: both sides vanish on `p ^ k`, `k ≥ 1`
      have hpR : p ∣ R := by
        rw [hR]
        rcases (Nat.Prime.dvd_mul hp).1 hpn with h2 | h2
        · exact h2.trans ⟨16 * n ^ 2, by ring⟩
        · exact h2.trans ⟨32 * n, by ring⟩
      have hap : a p = 0 := by
        have hsqR : 2 ≤ R.factorization p := by
          rw [← hp.pow_dvd_iff_le_factorization (NeZero.ne R), hR]
          rcases (Nat.Prime.dvd_mul hp).1 hpn with h2 | h2
          · have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
            subst this
            exact ⟨8 * n ^ 2, by ring⟩
          · exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd h2 2) 32
        have hcond : g.dirichletLift.conductor.factorization p = 0 := by
          have h1 : g.dirichletLift = 1 := by
            ext u
            rw [Newform.dirichletLift_def, MulChar.ofUnitHom_coe, hgχ]
            simp
          rw [h1, DirichletCharacter.conductor_one]
          simp
        by_contra hne
        have := (g.qExpansion_coeff_prime_ne_zero_iff hp hpR).1 hne
        rw [hcond] at this
        omega
      have hχp : (MulChar.ofUnitHom g.χ : DirichletCharacter ℂ R) p = 0 := by
        apply MulChar.map_nonunit
        rw [ZMod.isUnit_iff_coprime]
        exact fun h ↦ hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h hpR)
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [h₁, congruentCoeff, f32Coeff_one]
      · rw [congruentCoeff_prime_pow_of_dvd hp hpn hk]
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        clear hk
        induction j with
        | zero => simpa using hap
        | succ j ih =>
          rw [show j + 1 + 1 = j + 2 by ring, hrec p hp j, hap, hχp]
          simp
    · -- a good prime: the same first two terms and the same recursion
      have hcopR : p.Coprime R := by
        rw [hR]
        refine Nat.Coprime.mul_right ?_ (Nat.Coprime.pow_right 2 ?_)
        · have : p.Coprime 2 :=
            (Nat.coprime_primes hp Nat.prime_two).2 (fun h ↦ hpn (h ▸ dvd_mul_right 2 n))
          simpa using this.pow_right 5
        · exact (Nat.Prime.coprime_iff_not_dvd hp).2 (fun h ↦ hpn (dvd_mul_of_dvd_right h 2))
      have hχp : (MulChar.ofUnitHom g.χ : DirichletCharacter ℂ R) p = 1 := by
        rw [← Newform.dirichletLift_def, g.dirichletLift_apply_of_coprime hcopR, hgχ]
        simp
      have hap : a p = (congruentCoeff n p : ℂ) := by
        show (qExpansion 1 g.toCuspForm).coeff p = _
        rw [hgp p hp hpn, congruentCoeff_eq_jacobiChar hn p]
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        match k with
        | 0 => simp [h₁, congruentCoeff, f32Coeff_one]
        | 1 => simpa using hap
        | j + 2 =>
          rw [hrec p hp j, ih (j + 1) (by omega), ih j (by omega), hχp, hap,
            congruentCoeff_prime_pow_add_two hp hpn j]
          push_cast
          norm_num
  have := congrArg (fun F : ArithmeticFunction ℂ ↦ F m) key
  simpa [A, C] using this

/-- The twist of $f_{32}$ by $\chi_n$ has trivial nebentypus ($\chi_n^2 = 1$). -/
theorem f32Twist_χ {n : ℕ} [NeZero n] (hn : Odd n) :
    (f32NewformDef.primitiveTwist (jacobiChar n hn)).χ = 1 := by
  have hnL : n ∣ 32 * n ^ 2 := ⟨32 * n, by ring⟩
  have h := Newform.primitiveTwist_χ_comp_unitsMap (L := 32 * n ^ 2) f32NewformDef (jacobiChar n hn)
    (f32TwistLevel_dvd hn) ⟨n ^ 2, rfl⟩ hnL
  have hf : f32NewformDef.χ = 1 := f32Eigenform_χ
  rw [hf, toUnitHom_comp_sq_eq_one _ (jacobiChar_sq n hn) hnL] at h
  refine (MonoidHom.cancel_right (ZMod.unitsMap_surjective (f32TwistLevel_dvd hn))).mp ?_
  rw [h]
  ext u
  simp

/-- The coefficients of the twist of $f_{32}$ by $\chi_n$ at the primes $p \nmid 2n$. -/
theorem qExpansion_coeff_f32Twist_prime {n : ℕ} [NeZero n] (hn : Odd n) {p : ℕ} (hp : p.Prime)
    (hpn : ¬ p ∣ 2 * n) :
    (qExpansion 1 (f32NewformDef.primitiveTwist (jacobiChar n hn)).toCuspForm).coeff p =
      jacobiChar n hn p * (f32Coeff p : ℂ) := by
  have hp2 : p.Coprime 32 := by
    have : p.Coprime 2 :=
      (Nat.coprime_primes hp Nat.prime_two).2 (fun h ↦ hpn (h ▸ dvd_mul_right 2 n))
    simpa using this.pow_right 5
  have hpn' : p.Coprime n :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (fun h ↦ hpn (dvd_mul_of_dvd_right h 2))
  rw [Newform.qExpansion_coeff_primitiveTwist _ _ hp hp2 hpn']
  congr 1
  show (qExpansion 1 f32Eigenform.toCuspForm).coeff p = _
  rw [f32Eigenform_toCuspForm, qExpansion_coeff_f32CuspGamma1]

/-- **The newforms of $E_n$ from the level**: if the twist of $f_{32}$ by $\chi_n$ has level $32n^2$, then $E_n$ has it as its
newform. The level is proved to be $32n^2$ in `TwistLevel.lean` (`f32TwistLevel_eq_of_odd`), which gives the
unconditional `hasNewform_congruentCurve`. -/
theorem hasNewform_congruentCurve_of_level_eq {n : ℕ} [NeZero n] (hn : Odd n) (hsq : Squarefree n)
    (hR : f32NewformDef.primitiveTwistLevel (jacobiChar n hn) = 32 * n ^ 2) :
    ∃ f : Newform (32 * n ^ 2) 2, HasNewform (congruentCurve n) (32 * n ^ 2) f := by
  have main : ∀ (R : ℕ) [NeZero R] (g : Newform R 2), R = 32 * n ^ 2 →
      HasNewform (congruentCurve n) R g →
        ∃ f : Newform (32 * n ^ 2) 2, HasNewform (congruentCurve n) (32 * n ^ 2) f := by
    intro R _ g hR' hg
    subst hR'
    exact ⟨g, hg⟩
  exact main _ _ hR (hasNewform_of_level_eq hn hsq _ hR (f32Twist_χ hn)
    fun p hp hpn ↦ qExpansion_coeff_f32Twist_prime hn hp hpn)

/-- **The newforms of $E_n$, conditional form**: for odd squarefree $n$, $E_n$ has the newform
$f_{32} \otimes \chi_n$ of level $32n^2$, given `TwistLevelRamified`. Superseded by the unconditional
`hasNewform_congruentCurve` (`TwistLevel.lean`). -/
theorem hasNewform_congruentCurve_of_twistLevelRamified (hT : TwistLevelRamified) {n : ℕ} [NeZero n]
    (hn : Odd n) (hsq : Squarefree n) :
    ∃ f : Newform (32 * n ^ 2) 2, HasNewform (congruentCurve n) (32 * n ^ 2) f :=
  hasNewform_congruentCurve_of_level_eq hn hsq (f32TwistLevel_eq hn hT hsq)

end ModularFormsKB.Elliptic
