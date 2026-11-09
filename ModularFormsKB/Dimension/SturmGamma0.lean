import Mathlib.NumberTheory.ArithmeticFunction.Defs
import TauCeti.NumberTheory.ModularForms.SturmBound
import TauCeti.NumberTheory.ModularForms.TrivialNebentypus
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import ModularFormsKB.Citation
/-!
# The Sturm bound and dimension bounds for $\Gamma_0(N)$, $\Gamma_1(N)$ and nebentypus $\chi$

For a finite-index subgroup $\Gamma \le \mathrm{SL}_2(\mathbb Z)$, Tau Ceti proves the Sturm bound
`ModularForm.sturm_bound_finiteIndex_SL2Z` (module `TauCeti.NumberTheory.ModularForms.SturmBound`,
a port of Chris Birkbeck's Mathlib PR #39000, through the norm map to level one): a weight $k$ form
whose $q$-expansion at $\infty$ vanishes to order $> k\,[\mathrm{SL}_2(\mathbb Z):\Gamma]/12$ is zero.
This file specializes it with explicit indices:

* $[\mathrm{SL}_2(\mathbb Z) : \Gamma_0(N)] = \psi(N) = N\prod_{p\mid N}(1 + 1/p)$, Dedekind's $\psi$
  (`dedekindPsi`, a multiplicative arithmetic function), from Tau Ceti's
  `CongruenceSubgroup.Gamma0_index_eq_prod_factorization`;
* $[\mathrm{SL}_2(\mathbb Z) : \Gamma_1(N)] = \psi(N)\,\varphi(N)$;

and derives $\dim M_k \le \lfloor k\,\mathrm{index}/12\rfloor + 1$ and $\dim S_k \le
\lfloor k\,\mathrm{index}/12\rfloor$.

For a Dirichlet character $\chi$ mod $N$, the space $M_k(\Gamma_0(N), \chi)$ is Tau Ceti's
`modFormCharSpace k χ.toUnitHom` (module `TauCeti.NumberTheory.ModularForms.DiamondOperators`), the
$\chi$-eigenspace of the diamond operators on $M_k(\Gamma_1(N))$. For it the Sturm bound holds with
$\psi(N)$ in place of the larger index of $\Gamma_1(N)$: for $m = \varphi(N)$, $\chi^m = 1$, so $f^m$ has trivial
nebentypus, so it is a form for $\Gamma_0(N)$ of weight $mk$ (Tau Ceti's
`TauCeti.modFormCharSpaceOneEquiv`, module `TauCeti.NumberTheory.ModularForms.TrivialNebentypus`), and its
order at $\infty$ is $m$ times that of $f$.

Sturm, *On the congruence of modular forms*, Lecture Notes in Math. 1240 (1987), 275–280 [unverified].

All bounds use natural-number floor division: `(k * ψ N).toNat / 12` is $\lfloor k\psi(N)/12 \rfloor$ for
$k \ge 0$ and $0$ for $k < 0$. Coefficient indices $n$ are the exponents of $q = e^{2\pi i\tau}$ (the strict
width of $\infty$ is $1$ for $\Gamma_0(N)$ and $\Gamma_1(N)$).
-/

open CongruenceSubgroup UpperHalfPlane Matrix.SpecialLinearGroup

open scoped MatrixGroups ModularForm
open TauCeti (modFormCharSpace cuspFormCharSpace mem_modFormCharSpace_iff_nebentypus
  mem_cuspFormCharSpace_iff_nebentypus)

namespace ModularFormsKB.Dimension

/-! ### Dedekind's $\psi$ and the indices of $\Gamma_0(N)$, $\Gamma_1(N)$ -/

/-- **Dedekind's $\psi$ function**, $\psi(N) = N\prod_{p \mid N}(1 + 1/p) = \prod_{p^e \| N}
p^{e-1}(p+1)$, as an arithmetic function ($\psi(0) = 0$ by the convention of `ArithmeticFunction`). -/
@[kb "sturm1987" "the index ψ(N) = [SL₂(ℤ) : Γ₀(N)]"]
def dedekindPsi : ArithmeticFunction ℕ :=
  ⟨fun N ↦ if N = 0 then 0 else N.factorization.prod fun p e ↦ p ^ (e - 1) * (p + 1), by simp⟩

/-- For $N \ne 0$, $\psi(N) = \prod_{p^e \| N} p^{e-1}(p+1)$. -/
@[kb "sturm1987" "the index ψ(N) = [SL₂(ℤ) : Γ₀(N)]"]
theorem dedekindPsi_apply {N : ℕ} (hN : N ≠ 0) :
    dedekindPsi N = N.factorization.prod fun p e ↦ p ^ (e - 1) * (p + 1) := by
  simp [dedekindPsi, hN]

/-- For $N \ne 0$, $\psi(N)$ is the index of $\Gamma_0(N)$ (Tau Ceti's
`CongruenceSubgroup.Gamma0_index_eq_prod_factorization`). -/
private lemma dedekindPsi_eq_index {N : ℕ} (hN : N ≠ 0) : dedekindPsi N = (Gamma0 N).index := by
  rw [dedekindPsi_apply hN, Gamma0_index_eq_prod_factorization hN]

/-- $\psi$ is multiplicative. -/
@[kb "sturm1987" "the index ψ(N) = [SL₂(ℤ) : Γ₀(N)]"]
theorem isMultiplicative_dedekindPsi : dedekindPsi.IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨by simp [dedekindPsi], ?_⟩
  intro m n hm hn hmn
  rw [dedekindPsi_eq_index hm, dedekindPsi_eq_index hn, dedekindPsi_eq_index (mul_ne_zero hm hn),
    Gamma0_index_mul_of_coprime hmn]

/-- $\psi(p^e) = p^{e-1}(p+1)$ for a prime $p$ and $e \ge 1$. -/
@[kb "sturm1987" "the index ψ(N) = [SL₂(ℤ) : Γ₀(N)]"]
theorem dedekindPsi_prime_pow {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    dedekindPsi (p ^ e) = p ^ (e - 1) * (p + 1) := by
  rw [dedekindPsi_eq_index (pow_ne_zero e hp.ne_zero),
    Gamma0_prime_power_index p hp e (Nat.pos_of_ne_zero he)]

/-- **The index of $\Gamma_0(N)$** in $\mathrm{SL}_2(\mathbb Z)$ is $\psi(N)$, for $N \ge 1$. From Tau Ceti's
`CongruenceSubgroup.Gamma0_index_eq_prod_factorization` (module
`TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic`). -/
@[kb "sturm1987" "the index ψ(N) = [SL₂(ℤ) : Γ₀(N)]"]
theorem Gamma0_index_eq_dedekindPsi (N : ℕ) [NeZero N] : (Gamma0 N).index = dedekindPsi N :=
  (dedekindPsi_eq_index (NeZero.ne N)).symm

/-- **The index of $\Gamma_1(N)$** in $\mathrm{SL}_2(\mathbb Z)$ is $\psi(N)\,\varphi(N)$, for $N \ge 1$
($\Gamma_0(N)/\Gamma_1(N) \cong (\mathbb Z/N\mathbb Z)^\times$ by the lower right entry). -/
@[kb "sturm1987" "the index of Γ₁(N)"]
theorem Gamma1_index_eq (N : ℕ) [NeZero N] : (Gamma1 N).index = dedekindPsi N * N.totient := by
  have hker : (Gamma1 N).subgroupOf (Gamma0 N) = (Gamma0Map N).toHomUnits.ker := by
    ext g
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, mem_Gamma1_iff_toHomUnits_eq_one]
  have hrel : (Gamma1 N).relIndex (Gamma0 N) = N.totient := by
    rw [Subgroup.relIndex, hker, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr Gamma0Map_toHomUnits_surjective, Subgroup.card_top,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rw [← Subgroup.relIndex_mul_index (Gamma1_in_Gamma0 N), hrel, Gamma0_index_eq_dedekindPsi, mul_comm]

/-! ### Finite-index subgroups containing $T$ -/

section OfTMem

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

omit [Γ.FiniteIndex] in
private lemma one_mem_strictPeriods (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simpa [Subgroup.strictWidthInfty_eq_one_of_T_mem hT] using
    (Γ : Subgroup (GL (Fin 2) ℝ)).strictWidthInfty_mem_strictPeriods

/-- The Sturm bound for a finite-index $\Gamma \ni T$, from Tau Ceti's
`ModularForm.sturm_bound_finiteIndex_SL2Z`. -/
private lemma sturm_bound_of_T_mem (hT : ModularGroup.T ∈ Γ) {k : ℤ} (f : ModularForm Γ k)
    (h : ∀ n ≤ (k * Γ.index).toNat / 12, (qExpansion 1 f).coeff n = 0) : f = 0 := by
  refine ModularForm.sturm_bound_finiteIndex_SL2Z f ?_
  rw [Subgroup.strictWidthInfty_eq_one_of_T_mem hT]
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _)
    (PowerSeries.nat_le_order _ _ fun i hi ↦ h i (Nat.lt_succ_iff.mp hi))

private lemma eq_of_sturm_bound_of_T_mem (hT : ModularGroup.T ∈ Γ) {k : ℤ} (f g : ModularForm Γ k)
    (h : ∀ n ≤ (k * Γ.index).toNat / 12, (qExpansion 1 f).coeff n = (qExpansion 1 g).coeff n) :
    f = g := by
  rw [← sub_eq_zero]
  refine sturm_bound_of_T_mem hT _ fun n hn ↦ ?_
  rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods hT), map_sub,
    sub_eq_zero]
  exact h n hn

end OfTMem

/-- A space with a linear map to power series, injective on the vectors whose first $B + 1$
coefficients vanish, has dimension at most $B + 1$. -/
private lemma finrank_le_of_coeff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (q : V →ₗ[ℂ] PowerSeries ℂ) (B : ℕ) (hq : ∀ v, (∀ n ≤ B, (q v).coeff n = 0) → v = 0) :
    Module.finrank ℂ V ≤ B + 1 := by
  let L : V →ₗ[ℂ] (Fin (B + 1) → ℂ) := LinearMap.pi fun i ↦ PowerSeries.coeff (i : ℕ) ∘ₗ q
  have hL : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).mpr fun v hv ↦ hq v fun n hn ↦ ?_
    simpa [L] using congrFun hv ⟨n, Nat.lt_succ_iff.mpr hn⟩
  simpa using LinearMap.finrank_le_finrank_of_injective hL

/-- The cusp-form version of `finrank_le_of_coeff`: if moreover every constant coefficient
vanishes, the dimension is at most $B$. -/
private lemma finrank_le_of_coeff_of_coeff_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (q : V →ₗ[ℂ] PowerSeries ℂ) (B : ℕ) (h0 : ∀ v, (q v).coeff 0 = 0)
    (hq : ∀ v, (∀ n ≤ B, (q v).coeff n = 0) → v = 0) :
    Module.finrank ℂ V ≤ B := by
  let L : V →ₗ[ℂ] (Fin B → ℂ) := LinearMap.pi fun i ↦ PowerSeries.coeff ((i : ℕ) + 1) ∘ₗ q
  have hL : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).mpr fun v hv ↦ hq v fun n hn ↦ ?_
    rcases n with _ | n
    · exact h0 v
    · simpa [L] using congrFun hv ⟨n, hn⟩
  simpa using LinearMap.finrank_le_finrank_of_injective hL

/-! ### $\Gamma_0(N)$ -/

private lemma T_mem_Gamma0 (N : ℕ) : ModularGroup.T ∈ Gamma0 N := by
  rw [Gamma0_mem]; simp [ModularGroup.T]

private lemma T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  rw [Gamma1_mem]; simp [ModularGroup.T]

/-- **Sturm bound for $\Gamma_0(N)$.** A modular form $f \in M_k(\Gamma_0(N))$ whose $q$-expansion
coefficients $a_n$ vanish for all $n \le k\psi(N)/12$ is zero. From Tau Ceti's
`ModularForm.sturm_bound_finiteIndex_SL2Z` (module `TauCeti.NumberTheory.ModularForms.SturmBound`). -/
@[kb "sturm1987" "Sturm bound, Γ₀(N)"]
theorem sturm_bound_Gamma0 {N : ℕ} [NeZero N] {k : ℤ} (f : ModularForm (Gamma0 N) k)
    (h : ∀ n ≤ (k * dedekindPsi N).toNat / 12, (qExpansion 1 f).coeff n = 0) : f = 0 :=
  sturm_bound_of_T_mem (T_mem_Gamma0 N) f (by rwa [Gamma0_index_eq_dedekindPsi])

/-- Two forms in $M_k(\Gamma_0(N))$ whose $q$-expansions agree up to $n \le k\psi(N)/12$ are equal. -/
@[kb "sturm1987" "Sturm bound, Γ₀(N)"]
theorem eq_of_sturm_bound_Gamma0 {N : ℕ} [NeZero N] {k : ℤ} (f g : ModularForm (Gamma0 N) k)
    (h : ∀ n ≤ (k * dedekindPsi N).toNat / 12, (qExpansion 1 f).coeff n = (qExpansion 1 g).coeff n) :
    f = g :=
  eq_of_sturm_bound_of_T_mem (T_mem_Gamma0 N) f g (by rwa [Gamma0_index_eq_dedekindPsi])

/-- $M_k(\Gamma_0(N))$ is finite-dimensional. Tau Ceti's instance
`TauCeti.finiteDimensional_modularForm_finiteIndex`. -/
@[kb "sturm1987" "finite dimension, Γ₀(N)"]
theorem finiteDimensional_modularForm_Gamma0 (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (ModularForm (Gamma0 N) k) :=
  inferInstance

/-- $S_k(\Gamma_0(N))$ is finite-dimensional. Tau Ceti's instance
`TauCeti.finiteDimensional_cuspForm_finiteIndex`. -/
@[kb "sturm1987" "finite dimension, Γ₀(N)"]
theorem finiteDimensional_cuspForm_Gamma0 (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (Gamma0 N) k) :=
  inferInstance

/-- **Dimension bound for $\Gamma_0(N)$**: $\dim M_k(\Gamma_0(N)) \le \lfloor k\psi(N)/12 \rfloor + 1$. -/
@[kb "sturm1987" "dimension bound, Γ₀(N)"]
theorem finrank_modularForm_Gamma0_le (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (ModularForm (Gamma0 N) k) ≤ (k * dedekindPsi N).toNat / 12 + 1 :=
  finrank_le_of_coeff (TauCeti.ModularForm.qExpansionLinearMap one_pos
    (one_mem_strictPeriods (T_mem_Gamma0 N)) k) _ fun f hf ↦ sturm_bound_Gamma0 f (by simpa using hf)

/-- $\dim S_k(\Gamma_0(N)) \le \lfloor k\psi(N)/12 \rfloor$. -/
@[kb "sturm1987" "dimension bound, Γ₀(N)"]
theorem finrank_cuspForm_Gamma0_le (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (CuspForm (Gamma0 N) k) ≤ (k * dedekindPsi N).toNat / 12 :=
  finrank_le_of_coeff_of_coeff_zero (TauCeti.ModularForm.qExpansionLinearMap one_pos
      (one_mem_strictPeriods (T_mem_Gamma0 N)) k ∘ₗ CuspForm.toModularFormₗ) _
    (fun f : CuspForm (Gamma0 N) k ↦ CuspFormClass.qExpansion_coeff_zero f one_pos
        (one_mem_strictPeriods (T_mem_Gamma0 N)))
    fun f hf ↦ CuspForm.toModularFormₗ_injective (by
      simpa using sturm_bound_Gamma0 (CuspForm.toModularFormₗ f) (by simpa using hf))

/-! ### $\Gamma_1(N)$ -/

/-- **Sturm bound for $\Gamma_1(N)$**, with the index $\psi(N)\varphi(N)$. -/
@[kb "sturm1987" "Sturm bound, Γ₁(N)"]
theorem sturm_bound_Gamma1 {N : ℕ} [NeZero N] {k : ℤ} (f : ModularForm (Gamma1 N) k)
    (h : ∀ n ≤ (k * (dedekindPsi N * N.totient)).toNat / 12, (qExpansion 1 f).coeff n = 0) :
    f = 0 :=
  sturm_bound_of_T_mem (T_mem_Gamma1 N) f (by rwa [Gamma1_index_eq])

/-- Two forms in $M_k(\Gamma_1(N))$ whose $q$-expansions agree up to $n \le k\psi(N)\varphi(N)/12$ are
equal. -/
@[kb "sturm1987" "Sturm bound, Γ₁(N)"]
theorem eq_of_sturm_bound_Gamma1 {N : ℕ} [NeZero N] {k : ℤ} (f g : ModularForm (Gamma1 N) k)
    (h : ∀ n ≤ (k * (dedekindPsi N * N.totient)).toNat / 12,
      (qExpansion 1 f).coeff n = (qExpansion 1 g).coeff n) :
    f = g :=
  eq_of_sturm_bound_of_T_mem (T_mem_Gamma1 N) f g (by rwa [Gamma1_index_eq])

/-- $M_k(\Gamma_1(N))$ is finite-dimensional. -/
@[kb "sturm1987" "finite dimension, Γ₁(N)"]
theorem finiteDimensional_modularForm_Gamma1 (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (ModularForm (Gamma1 N) k) :=
  inferInstance

/-- $S_k(\Gamma_1(N))$ is finite-dimensional. -/
@[kb "sturm1987" "finite dimension, Γ₁(N)"]
theorem finiteDimensional_cuspForm_Gamma1 (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (Gamma1 N) k) :=
  inferInstance

/-- **Dimension bound for $\Gamma_1(N)$**: $\dim M_k(\Gamma_1(N)) \le \lfloor k\psi(N)\varphi(N)/12\rfloor + 1$. -/
@[kb "sturm1987" "dimension bound, Γ₁(N)"]
theorem finrank_modularForm_Gamma1_le (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (ModularForm (Gamma1 N) k) ≤
      (k * (dedekindPsi N * N.totient)).toNat / 12 + 1 :=
  finrank_le_of_coeff (TauCeti.ModularForm.qExpansionLinearMap one_pos
    (one_mem_strictPeriods (T_mem_Gamma1 N)) k) _ fun f hf ↦ sturm_bound_Gamma1 f (by simpa using hf)

/-- $\dim S_k(\Gamma_1(N)) \le \lfloor k\psi(N)\varphi(N)/12\rfloor$. -/
@[kb "sturm1987" "dimension bound, Γ₁(N)"]
theorem finrank_cuspForm_Gamma1_le (N : ℕ) [NeZero N] (k : ℤ) :
    Module.finrank ℂ (CuspForm (Gamma1 N) k) ≤ (k * (dedekindPsi N * N.totient)).toNat / 12 :=
  finrank_le_of_coeff_of_coeff_zero (TauCeti.ModularForm.qExpansionLinearMap one_pos
      (one_mem_strictPeriods (T_mem_Gamma1 N)) k ∘ₗ CuspForm.toModularFormₗ) _
    (fun f : CuspForm (Gamma1 N) k ↦ CuspFormClass.qExpansion_coeff_zero f one_pos
        (one_mem_strictPeriods (T_mem_Gamma1 N)))
    fun f hf ↦ CuspForm.toModularFormₗ_injective (by
      simpa using sturm_bound_Gamma1 (CuspForm.toModularFormₗ f) (by simpa using hf))

/-! ### Nebentypus $\chi$ -/

/-- $\lfloor m a/12 \rfloor < m(\lfloor a/12 \rfloor + 1)$ for $m > 0$ (with `toNat` truncation). -/
private lemma toNat_mul_div_lt {m : ℕ} (hm : 0 < m) (a : ℤ) :
    ((m : ℤ) * a).toNat / 12 < m * (a.toNat / 12 + 1) := by
  have htoNat : ((m : ℤ) * a).toNat = m * a.toNat := by
    rcases le_or_gt 0 a with ha | ha
    · lift a to ℕ using ha
      rw [← Nat.cast_mul, Int.toNat_natCast, Int.toNat_natCast]
    · rw [Int.toNat_of_nonpos ha.le, Int.toNat_of_nonpos (by nlinarith), mul_zero]
  rw [htoNat, Nat.div_lt_iff_lt_mul (by norm_num), mul_assoc]
  exact Nat.mul_lt_mul_of_pos_left (by omega) hm

/-- A cusp form of nebentypus $\chi$ is a modular form of nebentypus $\chi$. -/
private lemma toModularFormₗ_mem_modFormCharSpace {N : ℕ} {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}
    {f : CuspForm (Gamma1 N) k} (hf : f ∈ cuspFormCharSpace k χ) :
    CuspForm.toModularFormₗ f ∈ modFormCharSpace k χ := by
  rw [mem_cuspFormCharSpace_iff_nebentypus] at hf
  rw [mem_modFormCharSpace_iff_nebentypus]
  exact hf

/-- **Sturm bound for $M_k(\Gamma_0(N), \chi)$**, with $\psi(N)$: a form of nebentypus $\chi$ (an element of
Tau Ceti's `modFormCharSpace k χ.toUnitHom`) whose coefficients $a_n$ vanish for $n \le
k\psi(N)/12$ is zero. -/
@[kb "sturm1987" "Sturm bound with character"]
theorem sturm_bound_char {N : ℕ} [NeZero N] {k : ℤ} (χ : DirichletCharacter ℂ N)
    (f : ModularForm (Gamma1 N) k) (hf : f ∈ modFormCharSpace k χ.toUnitHom)
    (h : ∀ n ≤ (k * dedekindPsi N).toNat / 12, (qExpansion 1 f).coeff n = 0) : f = 0 := by
  set m := Fintype.card (ZMod N)ˣ
  have hm : 0 < m := Fintype.card_pos
  have hF : f.pow m ∈ modFormCharSpace ((m : ℤ) * k) (1 : (ZMod N)ˣ →* ℂˣ) := by
    rw [mem_modFormCharSpace_iff_nebentypus] at hf ⊢
    intro g
    have hu : (χ.toUnitHom ((Gamma0Map N).toHomUnits g) : ℂ) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
    rw [ModularForm.coe_pow, ModularForm.pow_slash, hf g, smul_pow, hu, one_smul]
    simp
  set G := TauCeti.modFormCharSpaceOneEquiv N _ ⟨f.pow m, hF⟩
  have hG : ⇑G = ⇑f ^ m := by simp [G]
  have hG0 : G = 0 := by
    refine sturm_bound_Gamma0 G fun n hn ↦ ?_
    rw [hG, ← ModularForm.coe_pow,
      ModularForm.qExpansion_pow one_pos (one_mem_strictPeriods (T_mem_Gamma1 N))]
    refine PowerSeries.coeff_of_lt_order _ ?_
    rw [PowerSeries.order_pow]
    have hord : (((k * dedekindPsi N).toNat / 12 + 1 : ℕ) : ℕ∞) ≤ (qExpansion 1 f).order :=
      PowerSeries.nat_le_order _ _ fun i hi ↦ h i (Nat.lt_succ_iff.mp hi)
    have hlt : n < m * ((k * dedekindPsi N).toNat / 12 + 1) :=
      lt_of_le_of_lt (by rwa [mul_assoc] at hn) (toNat_mul_div_lt hm _)
    calc (n : ℕ∞) < ((m * ((k * dedekindPsi N).toNat / 12 + 1) : ℕ) : ℕ∞) := by exact_mod_cast hlt
      _ ≤ m • (qExpansion 1 f).order := by
        rw [Nat.cast_mul, nsmul_eq_mul]
        gcongr
  ext z
  have := congrFun hG z
  rw [hG0] at this
  simpa [hm.ne'] using this.symm

/-- Two forms in $M_k(\Gamma_0(N), \chi)$ whose $q$-expansions agree up to $n \le k\psi(N)/12$ are equal. -/
@[kb "sturm1987" "Sturm bound with character"]
theorem eq_of_sturm_bound_char {N : ℕ} [NeZero N] {k : ℤ} (χ : DirichletCharacter ℂ N)
    (f g : ModularForm (Gamma1 N) k) (hf : f ∈ modFormCharSpace k χ.toUnitHom)
    (hg : g ∈ modFormCharSpace k χ.toUnitHom)
    (h : ∀ n ≤ (k * dedekindPsi N).toNat / 12, (qExpansion 1 f).coeff n = (qExpansion 1 g).coeff n) :
    f = g := by
  rw [← sub_eq_zero]
  refine sturm_bound_char χ (f - g) (sub_mem hf hg) fun n hn ↦ ?_
  rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods (T_mem_Gamma1 N)),
    map_sub, sub_eq_zero]
  exact h n hn

/-- **Dimension bound with character**: $\dim M_k(\Gamma_0(N), \chi) \le \lfloor k\psi(N)/12 \rfloor + 1$. -/
@[kb "sturm1987" "dimension bound with character"]
theorem finrank_modFormCharSpace_le {N : ℕ} [NeZero N] (k : ℤ) (χ : DirichletCharacter ℂ N) :
    Module.finrank ℂ (modFormCharSpace k χ.toUnitHom) ≤ (k * dedekindPsi N).toNat / 12 + 1 := by
  refine finrank_le_of_coeff (TauCeti.ModularForm.qExpansionLinearMap one_pos
      (one_mem_strictPeriods (T_mem_Gamma1 N)) k ∘ₗ (modFormCharSpace k χ.toUnitHom).subtype) _
    fun f hf ↦ ?_
  have hf' : ∀ n ≤ (k * dedekindPsi N).toNat / 12,
      (qExpansion 1 (f : ModularForm (Gamma1 N) k)).coeff n = 0 := by
    intro n hn
    have := hf n hn
    rwa [LinearMap.comp_apply, Submodule.subtype_apply,
      TauCeti.ModularForm.qExpansionLinearMap_apply] at this
  have h0 : (f : ModularForm (Gamma1 N) k) = 0 := sturm_bound_char χ _ f.2 hf'
  exact Subtype.ext h0

/-- $\dim S_k(\Gamma_0(N), \chi) \le \lfloor k\psi(N)/12 \rfloor$, for Tau Ceti's
`cuspFormCharSpace k χ.toUnitHom`. -/
@[kb "sturm1987" "dimension bound with character"]
theorem finrank_cuspFormCharSpace_le {N : ℕ} [NeZero N] (k : ℤ) (χ : DirichletCharacter ℂ N) :
    Module.finrank ℂ (cuspFormCharSpace k χ.toUnitHom) ≤ (k * dedekindPsi N).toNat / 12 :=
  finrank_le_of_coeff_of_coeff_zero (TauCeti.ModularForm.qExpansionLinearMap one_pos
      (one_mem_strictPeriods (T_mem_Gamma1 N)) k ∘ₗ CuspForm.toModularFormₗ ∘ₗ
      (cuspFormCharSpace k χ.toUnitHom).subtype) _
    (fun f ↦ CuspFormClass.qExpansion_coeff_zero (f : CuspForm (Gamma1 N) k) one_pos
      (one_mem_strictPeriods (T_mem_Gamma1 N)))
    fun f hf ↦ Subtype.ext <| CuspForm.toModularFormₗ_injective <| by
      simpa using sturm_bound_char χ _ (toModularFormₗ_mem_modFormCharSpace f.2) hf

end ModularFormsKB.Dimension
