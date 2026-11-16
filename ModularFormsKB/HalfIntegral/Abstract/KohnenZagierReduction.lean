/-
# The Kohnen–Zagier formula from smaller named inputs

Kohnen–Zagier 1981 `kohnenzagier1981` prove Thm. 1 (`KohnenZagier`) through the adjoint $\mathcal S_D^*$ of the
$D$-th Shimura lift $\mathcal S_D : S^+_{k+1/2}(4) \to S_{2k}(\mathrm{SL}_2(\mathbb Z))$ (Kohnen 1980 `kohnen1980`). This file
proves Thm. 1 from the following inputs, and contains no analysis itself (`kohnenZagier_of_inputs`).

Fix $k \ge 1$, a fundamental discriminant $D$ with $(-1)^kD > 0$, and let $g \leftrightarrow F$ correspond (`Corresponds`), with
coefficients $c$ and $b$.
1. **The $D$-th lift on coefficients** (`kzLiftCoeff`): $\mathcal S_D g$ has $n$-th coefficient
   $\sum_{d\mid n}\left(\frac Dd\right)d^{k-1}c(|D|n^2/d^2)$; for $g \leftrightarrow F$ this is $c(|D|)\,b(n)$ (`KohnenLiftEigen`).
2. **The adjoint** (`KohnenAdjoint`): a map $\mathcal S_D^* : S_{2k} \to S^+_{k+1/2}(4)$ with
   $\langle \mathcal S_D g', G\rangle = \langle g', \mathcal S_D^* G\rangle$, the products being `peterssonOne` and
   `peterssonFour` (Kohnen–Zagier's normalizations); it commutes with the Hecke operators $T(p^2) \leftrightarrow T(p)$,
   $p$ odd (`KohnenAdjointHecke`).
3. **The coefficient of the adjoint** (`KohnenAdjointCoeff`): the $|D|$-th coefficient of $\mathcal S_D^*F$ is
   $\frac{(k-1)!}{\pi^k}|D|^{k-1/2}L(F, D, k)$ (`kzConstant`). In Kohnen–Zagier this comes from the kernel function of
   $\mathcal S_D^*$, i.e. from the Rankin–Selberg unfolding of $\langle F, \mathcal S_D P_{|D|}\rangle$ against Poincaré series.
   **Its constant is derived**, not read off the source: given inputs 1, 2, 4 and 5 it is equivalent to Thm. 1 whenever
   $c(|D|) \neq 0$ [unverified against the source].
4. **Multiplicity one** in $S^+_{k+1/2}(4)$ (`PlusMultiplicityOne`): forms in $S^+$ with the same eigenvalues $b(p)$ for
   $T(p^2)$, $p$ odd, as $g \ne 0$ are multiples of $g$ (Kohnen 1980, from multiplicity one in level one).
5. **Definiteness** (`PeterssonDefinite`): $\langle g, g\rangle \ne 0$ for $0 \ne g \in S^+$ and $\langle F, F\rangle \ne 0$ for
   $0 \ne F \in S_{2k}$. This is a theorem (convergence and positivity of the Petersson integral), not yet proved here.

**The algebra.** Write $\mathcal S_D^*F = \alpha g$ (inputs 2 and 4). Adjointness with $\mathcal S_D g = c(|D|)F$ (input 1)
gives $\overline{c(|D|)}\langle F, F\rangle = \alpha\langle g, g\rangle$; input 3 gives $\alpha\,c(|D|) = K\,L(F,D,k)$.
Multiplying, $|c(|D|)|^2\langle F,F\rangle = K\,L(F,D,k)\,\langle g, g\rangle$, and input 5 lets us divide.
-/
import ModularFormsKB.HalfIntegral.Abstract.PeterssonFour
import ModularFormsKB.HalfIntegral.Abstract.TwistL
import ModularFormsKB.HalfIntegral.KohnenLift

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup ModularForm
open scoped Real
open scoped Manifold

local notation "ℍ" => UpperHalfPlane

/-- **The coefficients of Kohnen's $D$-th Shimura lift** $\mathcal S_D$ on $S^+_{k+1/2}(4)$:
$\sum_{d\mid n}\left(\frac Dd\right)d^{k-1}c(|D|n^2/d^2)$ for $n \ge 1$ (Kohnen 1980 `kohnen1980`, Kohnen–Zagier 1981, §1
[unverified]).

Originally named `kohnenLiftCoeff`; renamed because `KohnenLift.lean` already defines
the same function as `kohnenLiftCoeff`. The two agree (`kzLiftCoeff_eq_kohnenLiftCoeff`). -/
noncomputable def kzLiftCoeff (k : ℕ) (D : ℤ) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, (kroneckerDisc D d : ℂ) * (d : ℂ) ^ ((k : ℤ) - 1) * c (D.natAbs * (n / d) ^ 2)

/-- `kzLiftCoeff` is Kohnen's $D$-th lift `kohnenLiftCoeff` of `KohnenLift.lean`. -/
theorem kzLiftCoeff_eq_kohnenLiftCoeff (k : ℕ) (D : ℤ) : kzLiftCoeff k D = kohnenLiftCoeff k D := rfl

/-- The constant $\frac{(k-1)!}{\pi^k}|D|^{k-1/2}$ of the Kohnen–Zagier formula. -/
noncomputable def kzConstant (k : ℕ) (D : ℤ) : ℂ :=
  ((k - 1).factorial / (π : ℂ) ^ k) * ((D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ)

/-- **Input 1: the $D$-th lift of an eigenform** (Kohnen 1980 `kohnen1980`; Kohnen–Zagier 1981 `kohnenzagier1981`, §1
[unverified]). If $g \leftrightarrow F$ and $D$ is a fundamental discriminant with $(-1)^kD > 0$, then
$\mathcal S_D g = c(|D|)F$ on coefficients: $\sum_{d\mid n}\left(\frac Dd\right)d^{k-1}c(|D|n^2/d^2) = c(|D|)b(n)$ for $n \ge 1$.
(This uses Kohnen's operator at $p = 2$, which `Corresponds` does not record.) -/
@[kb "kohnen1980" "the D-th lift of a Hecke eigenform g in S⁺ corresponding to F is c(|D|) F [unverified]"]
structure KohnenLiftEigen (M : MultiplierSystem) (k : ℕ) : Prop where
  lift : 1 ≤ k → ∀ (g : ℍ → ℂ) (c : ℕ → ℂ) (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ),
    Corresponds M k g c F b → ∀ D : ℤ, IsFundamentalDiscriminant D → 0 < (-1) ^ k * D →
      ∀ n : ℕ, 1 ≤ n → kzLiftCoeff k D c n = c D.natAbs * b n

/-- **Input 2a: $\mathcal S_D^*$ is the adjoint of the $D$-th lift** (Kohnen–Zagier 1981 `kohnenzagier1981`, §2
[unverified]): $\mathcal S_D^*$ maps $S_{2k}$ to $S^+_{k+1/2}(4)$, and
$\langle \mathcal S_D g', G\rangle = \langle g', \mathcal S_D^* G\rangle$ whenever $G' \in S_{2k}$ has the coefficients
`kzLiftCoeff k D c'` of $g' \in S^+$ (for $n \ge 1$). -/
@[kb "kohnenzagier1981" "§2: the adjoint of the D-th Shimura lift for the Petersson products [unverified]"]
structure KohnenAdjoint (M : MultiplierSystem) (k : ℕ) (D : ℤ) (Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ) : Prop where
  mem_plus : ∀ G, Sstar G ∈ M.plusCuspForms k 1 1
  adjoint : ∀ g' ∈ M.plusCuspForms k 1 1, ∀ c' : ℕ → ℂ, Abstract.HasQExp g' c' →
    ∀ (G' : CuspForm 𝒮ℒ (2 * k : ℕ)) (b' : ℕ → ℂ), Abstract.HasQExp G' b' →
      (∀ n, 1 ≤ n → b' n = kzLiftCoeff k D c' n) →
        ∀ G : CuspForm 𝒮ℒ (2 * k : ℕ), peterssonOne k G' G = peterssonFour k g' (Sstar G)

/-- **Input 2b: $\mathcal S_D^*$ is Hecke-equivariant** (Kohnen–Zagier 1981 `kohnenzagier1981`, §2 [unverified]): if
$T(p)b = b(p)\,b$ for all primes $p$, then the coefficients of $\mathcal S_D^* F$ are $T(p^2)$-eigen with eigenvalue $b(p)$
for odd $p$. -/
@[kb "kohnenzagier1981" "§2: the adjoint of the D-th lift commutes with T(p²) ↔ T(p) [unverified]"]
structure KohnenAdjointHecke (M : MultiplierSystem) (k : ℕ) (Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ) : Prop where
  eigen : ∀ (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ), Abstract.HasQExp F b →
    (∀ p : ℕ, p.Prime → heckeTInt (2 * k) 1 1 p b = b p • b) →
      ∀ c' : ℕ → ℂ, Abstract.HasQExp (Sstar F) c' → ∀ p : ℕ, p.Prime → p ≠ 2 → heckeT k 1 1 p c' = b p • c'

/-- **Input 3: the $|D|$-th coefficient of $\mathcal S_D^*F$** (Kohnen–Zagier 1981 `kohnenzagier1981`, §2–3; constant
derived from Thm. 1, see the module docstring): for a normalized Hecke eigenform $F$ with coefficients $b$, every
$q$-expansion $c'$ of $\mathcal S_D^*F$ has $c'(|D|) = \frac{(k-1)!}{\pi^k}|D|^{k-1/2}L(F, D, k)$. -/
@[kb "kohnenzagier1981" "§2-3: the |D|-th coefficient of S_D^* F is (k-1)!/π^k |D|^{k-1/2} L(F,D,k) [unverified]"]
structure KohnenAdjointCoeff (M : MultiplierSystem) (k : ℕ) (D : ℤ) (Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ) : Prop
    where
  coeff : ∀ (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ), Abstract.HasQExp F b → b 1 = 1 →
    (∀ p : ℕ, p.Prime → heckeTInt (2 * k) 1 1 p b = b p • b) →
      ∀ L : ℂ → ℂ, IsEntireLSeries (twistCoeff D b) ((k : ℝ) + 1) L →
        ∀ c' : ℕ → ℂ, Abstract.HasQExp (Sstar F) c' → c' D.natAbs = kzConstant k D * L k

/-- **Inputs 2 and 3 together:** for every fundamental discriminant $D$ with $(-1)^kD > 0$ there is an adjoint
$\mathcal S_D^*$ with the three properties. -/
structure KohnenAdjointInputs (M : MultiplierSystem) (k : ℕ) : Prop where
  exists_adjoint : 1 ≤ k → ∀ D : ℤ, IsFundamentalDiscriminant D → 0 < (-1) ^ k * D →
    ∃ Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ,
      KohnenAdjoint M k D Sstar ∧ KohnenAdjointHecke M k Sstar ∧ KohnenAdjointCoeff M k D Sstar

/-- **Input 4: multiplicity one in the plus space** (Kohnen 1980 `kohnen1980`, from Kohnen's isomorphism and multiplicity
one in level one [unverified]): if $0 \ne g \in S^+$ and $g' \in S^+$ have $q$-expansions $c, c'$ that are $T(p^2)$-eigen
with the same eigenvalues $e(p)$ for all odd primes $p$, then $g'$ is a multiple of $g$. -/
@[kb "kohnen1980" "multiplicity one for the Hecke operators T(p²), p odd, on S⁺_{k+1/2}(4) [unverified]"]
structure PlusMultiplicityOne (M : MultiplierSystem) (k : ℕ) : Prop where
  mult_one : 1 ≤ k → ∀ g ∈ M.plusCuspForms k 1 1, g ≠ 0 → ∀ g' ∈ M.plusCuspForms k 1 1,
    ∀ (c c' : ℕ → ℂ) (e : ℕ → ℂ), Abstract.HasQExp g c → Abstract.HasQExp g' c' →
      (∀ p : ℕ, p.Prime → p ≠ 2 → heckeT k 1 1 p c = e p • c) →
      (∀ p : ℕ, p.Prime → p ≠ 2 → heckeT k 1 1 p c' = e p • c') → ∃ α : ℂ, g' = α • g

/-- **Input 5: the Petersson norms of nonzero cusp forms are nonzero** (a theorem: convergence and positivity of the
Petersson integral; Shimura 1973 `shimura1973` for half-integral weight [unverified]). Not yet proved here. -/
@[kb "shimura1973" "the Petersson product is positive definite on cusp forms [unverified]"]
structure PeterssonDefinite (M : MultiplierSystem) (k : ℕ) : Prop where
  four : ∀ g ∈ M.plusCuspForms k 1 1, g ≠ 0 → peterssonNormSqFour k g ≠ 0
  one : ∀ F : CuspForm 𝒮ℒ (2 * k : ℕ), F ≠ 0 → peterssonNormSqOne k F ≠ 0

theorem hasQExp_smul {f : ℍ → ℂ} {a : ℕ → ℂ} (h : Abstract.HasQExp f a) (α : ℂ) :
    Abstract.HasQExp (α • f) (α • a) := fun τ ↦ by
  simpa [mul_assoc] using (h τ).mul_left α

/-- A normalized form ($b(1) = 1$) is nonzero. -/
theorem cuspForm_ne_zero_of_coeff_one {w : ℤ} (F : CuspForm 𝒮ℒ w) {b : ℕ → ℂ} (hF : Abstract.HasQExp F b)
    (h1 : b 1 = 1) : F ≠ 0 := by
  rintro rfl
  have h0 : Abstract.HasQExp (⇑(0 : CuspForm 𝒮ℒ w)) 0 := fun τ ↦ by simp
  have := hasQExp_coeff_eq_qExpansion (0 : CuspForm 𝒮ℒ w) hF 1
  rw [← hasQExp_coeff_eq_qExpansion (0 : CuspForm 𝒮ℒ w) h0 1, h1] at this
  exact one_ne_zero this

/-- **The algebraic core** of Kohnen–Zagier's argument: from $\overline{c}\,N_F = \alpha N_g$ and $\alpha c = KL$ with
$N_F, N_g \ne 0$ it follows that $|c|^2/N_g = KL/N_F$. -/
theorem kz_algebra {c α K L NF Ng : ℂ} (hNF : NF ≠ 0) (hNg : Ng ≠ 0)
    (hadj : (starRingEnd ℂ) c * NF = α * Ng) (hcoeff : α * c = K * L) :
    ((‖c‖ ^ 2 : ℝ) : ℂ) / Ng = K * L / NF := by
  have hc : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * (starRingEnd ℂ) c := by
    rw [mul_conj, normSq_eq_norm_sq]
  rw [div_eq_div_iff hNg hNF, hc, ← hcoeff]
  linear_combination c * hadj

/-- **The Kohnen–Zagier formula from the named inputs 1–5.** -/
theorem kohnenZagier_of_inputs (M : MultiplierSystem) (k : ℕ) (h1 : KohnenLiftEigen M k)
    (h2 : KohnenAdjointInputs M k) (h4 : PlusMultiplicityOne M k) (h5 : PeterssonDefinite M k) :
    KohnenZagier M k := by
  refine ⟨fun hk g c F b hgF D hD hsign L hL ↦ ?_⟩
  obtain ⟨Sstar, hadj, hhecke, hcoeff⟩ := h2.exists_adjoint hk D hD hsign
  -- $\mathcal S_D^* F = \alpha g$.
  obtain ⟨c', hc', -⟩ := (hadj.mem_plus F).2
  obtain ⟨α, hα⟩ := h4.mult_one hk g hgF.plus hgF.ne_zero (Sstar F) (hadj.mem_plus F) c c' b hgF.coeff_g hc'
    hgF.eigen_g (hhecke.eigen F b hgF.coeff_F hgF.eigen_F c' hc')
  -- Adjointness with $\mathcal S_D g = c(|D|) F$.
  have hG' : Abstract.HasQExp (⇑(c D.natAbs • F)) (c D.natAbs • b) := by
    rw [FunLike.coe_smul]
    exact hasQExp_smul hgF.coeff_F _
  have hadj' := hadj.adjoint g hgF.plus c hgF.coeff_g (c D.natAbs • F) (c D.natAbs • b) hG'
    (fun n hn ↦ by rw [Pi.smul_apply, smul_eq_mul, h1.lift hk g c F b hgF D hD hsign n hn]) F
  rw [peterssonOne, FunLike.coe_smul, peterssonReps_smul_left, hα, peterssonFour,
    peterssonReps_smul_right] at hadj'
  -- The $|D|$-th coefficient of $\mathcal S_D^* F = \alpha g$.
  have hcf := hcoeff.coeff F b hgF.coeff_F hgF.normalized hgF.eigen_F L hL (α • c)
    (by rw [hα]; exact hasQExp_smul hgF.coeff_g α)
  rw [Pi.smul_apply, smul_eq_mul] at hcf
  have hNF := h5.one F (cuspForm_ne_zero_of_coeff_one F hgF.coeff_F hgF.normalized)
  have hNg := h5.four g hgF.plus hgF.ne_zero
  have key := kz_algebra (c := c D.natAbs) (α := α) (K := kzConstant k D) (L := L k) hNF hNg
    (by rw [peterssonNormSqOne, peterssonNormSqFour, hadj']; ring) hcf
  rw [key, kzConstant]

end ModularFormsKB.HalfIntegral
