import ModularFormsKB.Milne.Ch6.LevelTwo
import ModularFormsKB.Milne.Ch6.CosetProduct
import ModularFormsKB.Milne.Ch6.X0Degree
import TauCeti.Analysis.Complex.RiemannSurface.IdentityTheorem
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The degree of $j(Nz)$ over $\mathbb C(j)$ is $\psi$

Milne, Section 6, proof of Theorem 6.1 (pdf p. 88). Let $K = \mathbb C(j) \subset \mathbb C(X_0(N))$ and $m$ the minimum
polynomial of $j_N = j(Nz)$ over $K$.

- $m$ divides $F(j, Y)$, $F$ the coset polynomial (`ModularFormsKB.Milne.LevelTwo.exists_coset_polynomial`), so
  $\deg m \le \psi$.
- Clearing denominators, $m$ gives $G \in \mathbb C[X][Y]$ with $G(j(z), j(Nz)) = 0$ on $\mathbb H$ and leading coefficient
  $b(X) \ne 0$. Replacing $z$ by $\gamma z$, every $j(N\gamma z)$ is a root of $G(j(z), Y)$. The $\psi$ functions
  $z \mapsto j(N\gamma_c z)$ are pairwise distinct (the stabilizer of $j(Nz)$ is $\Gamma_0(N)$,
  `ModularFormsKB.Milne.LevelTwo.mem_Gamma0_of_j_scale_smul`), so at a point $z_0$ off the (nowhere dense) coincidence
  sets and off the zeros of $b(j(z))$ (identity theorem), $G(j(z_0), Y)$ has $\psi$ distinct roots: $\deg m \ge \psi$.

Main result: `natDegree_minpoly_jNX`.
-/

open UpperHalfPlane CongruenceSubgroup Polynomial Filter Topology
open scoped MatrixGroups Manifold

noncomputable section

namespace ModularFormsKB.Milne.LevelTwo

open TauCeti.ModularForm TauCeti.RiemannSurface

/-! ### Values of polynomial expressions -/

section Values

variable {N : ℕ} {f g : MeromorphicFunction (X0 N)} {x : X0 N} {a b : ℂ}

theorem HasVal.algebraMap' (c : ℂ) (x : X0 N) :
    HasVal (algebraMap ℂ (MeromorphicFunction (X0 N)) c) x c := by
  rw [HasVal, MeromorphicFunction.coe_algebraMap]

theorem HasVal.zero' (x : X0 N) : HasVal (0 : MeromorphicFunction (X0 N)) x 0 := by
  rw [HasVal, MeromorphicFunction.coe_zero]

theorem HasVal.sum {ι : Type*} (s : Finset ι) {F : ι → MeromorphicFunction (X0 N)} {A : ι → ℂ}
    (h : ∀ i ∈ s, HasVal (F i) x (A i)) : HasVal (∑ i ∈ s, F i) x (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasVal.zero' x
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun k hk ↦ h k (Finset.mem_insert_of_mem hk))

theorem HasVal.aeval (hf : HasVal f x a) (p : ℂ[X]) : HasVal (Polynomial.aeval f p) x (p.eval a) := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.eval_eq_sum_range]
  refine HasVal.sum _ fun i _ ↦ ?_
  rw [Algebra.smul_def]
  exact (HasVal.algebraMap' _ x).mul (hf.pow i)

/-- The value of $G(f, g)$ at a point where $f = a$, $g = b$ is $G(a, b)$. -/
theorem HasVal.eval_map_aeval (hf : HasVal f x a) (hg : HasVal g x b) (G : ℂ[X][X]) :
    HasVal ((G.map (Polynomial.aeval f).toRingHom).eval g) x ((G.map (evalRingHom a)).eval b) := by
  rw [eval_eq_sum_range' (n := G.natDegree + 1) (lt_of_le_of_lt (natDegree_map_le) (Nat.lt_succ_self _)),
    eval_eq_sum_range' (n := G.natDegree + 1) (lt_of_le_of_lt (natDegree_map_le) (Nat.lt_succ_self _))]
  refine HasVal.sum _ fun i _ ↦ ?_
  simp only [coeff_map]
  exact (hf.aeval _).mul (hg.pow i)

end Values

/-! ### The identity theorem on $X_0(N)$ -/

/-- The class in $X_0(N)$ of $z \in \mathbb H$. -/
abbrev ptN (N : ℕ) (z : ℍ) : X0 N := Subgroup.CompactifiedQuotient.ofQuotient (Quotient.mk _ z)

/-- A meromorphic function on $X_0(N)$ vanishing at every non-cusp point is $0$. -/
theorem eq_zero_of_hasVal {N : ℕ} {E : MeromorphicFunction (X0 N)} (h : ∀ z : ℍ, HasVal E (ptN N z) 0) :
    E = 0 := by
  have hU : IsOpen (Set.range (Subgroup.CompactifiedQuotient.ofQuotient
      (Γ := (CongruenceSubgroup.Gamma0 N).map sl2zToPSL2R))) :=
    Subgroup.CompactifiedQuotient.isOpen_range_ofQuotient
  have hconst : EventuallyConst E (nhds (ptN N UpperHalfPlane.I)) := by
    refine eventuallyConst_iff_exists_eventuallyEq.2 ⟨((0 : ℂ) : OnePoint ℂ), ?_⟩
    filter_upwards [hU.mem_nhds ⟨_, rfl⟩] with y hy
    obtain ⟨p, rfl⟩ := hy
    induction p using Quotient.inductionOn with
    | h z => exact h z
  ext y
  rw [apply_eq_of_eventuallyConst E.mdifferentiable hconst y, h, MeromorphicFunction.coe_zero]

theorem eval_eq_zero_of_hasVal {N : ℕ} {E : MeromorphicFunction (X0 N)} (hE : E = 0) {z : ℍ} {a : ℂ}
    (h : HasVal E (ptN N z) a) : a = 0 := by
  rw [HasVal, hE, MeromorphicFunction.coe_zero] at h
  exact (OnePoint.coe_injective h).symm

/-! ### Nonvanishing on a dense set -/

/-- A holomorphic function on $\mathbb H$ that is not identically zero is nonzero on a dense open set. -/
theorem dense_setOf_ne_zero {g : ℍ → ℂ} (hg : MDiff g) (hne : ∃ z, g z ≠ 0) :
    Dense {z | g z ≠ 0} := by
  obtain ⟨z₁, hz₁⟩ := hne
  rw [dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  by_contra hempty
  have hzero : ∀ z ∈ U, g z = 0 := fun z hz ↦ by
    by_contra h
    exact hempty ⟨z, hz, h⟩
  have hconst : EventuallyConst g (𝓝 u) :=
    eventuallyConst_iff_exists_eventuallyEq.2 ⟨0, Filter.eventually_of_mem (hU.mem_nhds hu) hzero⟩
  have := apply_eq_of_eventuallyConst hg hconst z₁
  rw [hzero u hu] at this
  exact hz₁ this

theorem isOpen_setOf_ne_zero {g : ℍ → ℂ} (hg : MDiff g) : IsOpen {z | g z ≠ 0} :=
  isOpen_ne_fun hg.continuous continuous_const

/-- Finitely many holomorphic functions on $\mathbb H$, none identically zero, are simultaneously nonzero at some
point. -/
theorem exists_forall_ne_zero {ι : Type*} (s : Finset ι) (g : ι → ℍ → ℂ) (hg : ∀ i ∈ s, MDiff (g i))
    (hne : ∀ i ∈ s, ∃ z, g i z ≠ 0) : ∃ z, ∀ i ∈ s, g i z ≠ 0 := by
  classical
  have key : Dense {z | ∀ i ∈ s, g i z ≠ 0} ∧ IsOpen {z | ∀ i ∈ s, g i z ≠ 0} := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      obtain ⟨hd, ho⟩ := ih (fun i hi ↦ hg i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hne i (Finset.mem_insert_of_mem hi))
      have hda := dense_setOf_ne_zero (hg a (Finset.mem_insert_self _ _))
        (hne a (Finset.mem_insert_self _ _))
      have hoa := isOpen_setOf_ne_zero (hg a (Finset.mem_insert_self _ _))
      have heq : {z | ∀ i ∈ insert a s, g i z ≠ 0} =
          {z | g a z ≠ 0} ∩ {z | ∀ i ∈ s, g i z ≠ 0} := by
        ext z; simp
      rw [heq]
      exact ⟨hda.inter_of_isOpen_left hd hoa, hoa.inter ho⟩
  obtain ⟨z, hz⟩ := key.1.nonempty
  exact ⟨z, hz⟩

/-! ### The minimum polynomial -/

variable {N : ℕ} [NeZero N] (hN : 0 < N)

omit [NeZero N] in
/-- The coset functions are pairwise distinct. -/
theorem exists_cosetVal_ne {c c' : Cosets N} (h : c ≠ c') : ∃ z, cosetVal hN c z - cosetVal hN c' z ≠ 0 := by
  by_contra hall
  push Not at hall
  apply h
  induction c using Quotient.inductionOn with
  | h γ =>
  induction c' using Quotient.inductionOn with
  | h γ' =>
  have hst : ∀ w : ℍ, j (scaleH N hN ((γ * γ'⁻¹) • w)) = j (scaleH N hN w) := fun w ↦ by
    have := hall (γ'⁻¹ • w)
    rw [sub_eq_zero, cosetVal_mk, cosetVal_mk, ← mul_smul, ← mul_smul, mul_inv_cancel, one_smul] at this
    simpa [jN, mul_smul] using this
  have hmem := mem_Gamma0_of_j_scale_smul hN _ hst
  apply Quotient.sound
  show QuotientGroup.rightRel _ γ γ'
  rw [QuotientGroup.rightRel_apply]
  simpa using inv_mem hmem

/-- $b(j(z))$ is not identically zero for $b \ne 0$. -/
theorem exists_eval_j_ne_zero {b : ℂ[X]} (hb : b ≠ 0) : ∃ z : ℍ, b.eval (j z) ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨C, hC⟩ := (finite_setOfPred_isRoot hb).isBounded.exists_norm_le
  obtain ⟨A, hA⟩ := norm_j_bounds
  set t : ℝ := max A (max C 1)
  have ht : 0 < t := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_right _ _))
  let w : ℍ := ⟨Complex.I * t, by simpa using ht⟩
  have hw : w.im = t := by simp [w, UpperHalfPlane.im]
  have h1 := (hA w (by rw [hw]; exact le_max_left _ _)).1
  have h2 : ‖j w‖ ≤ C := hC _ (hall w)
  have h3 : 2 * Real.pi * t + 1 ≤ Real.exp (2 * Real.pi * t) := by
    linarith [Real.add_one_le_exp (2 * Real.pi * t)]
  have hCt : C ≤ t := le_trans (le_max_left _ _) (le_max_right _ _)
  rw [hw] at h1
  nlinarith [Real.pi_gt_three]

/-- **$[\mathbb C(j, j_N) : \mathbb C(j)] = \psi$**: the minimum polynomial of $j(Nz)$ over $\mathbb C(j)$ has degree
$\psi = (\Gamma(1) : \Gamma_0(N))$. -/
theorem natDegree_minpoly_jNX :
    (minpoly (IntermediateField.adjoin ℂ {jX N}) (jNX N hN)).natDegree = (Gamma0 N).index := by
  classical
  set K := IntermediateField.adjoin ℂ {jX N}
  obtain ⟨F, hFm, hFdeg, hF⟩ := exists_coset_polynomial hN
  let gen := IntermediateField.AdjoinSimple.gen ℂ (jX N)
  let φ : ℂ[X] →+* K := (Polynomial.aeval gen).toRingHom
  have hφ : (algebraMap K (MeromorphicFunction (X0 N))).comp φ =
      (Polynomial.aeval (jX N)).toRingHom := by
    refine RingHom.ext fun p ↦ ?_
    simp only [RingHom.coe_comp, Function.comp_apply, φ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact (Polynomial.aeval_algHom_apply (IntermediateField.val K) gen p).symm
  -- Step 1: `j_N` is a root of `F(j, Y)`.
  have hroot : (F.map (Polynomial.aeval (jX N)).toRingHom).eval (jNX N hN) = 0 := by
    apply eq_zero_of_hasVal
    intro z
    have := HasVal.eval_map_aeval (isJOnX0_jX N z) (isJNOnX0_jNX N hN z) F
    rw [hF z] at this
    have h0 : (Φ hN z).eval (TauCeti.ModularForm.j (scaleH N hN z)) = 0 := Φ_eval_jN hN z
    rwa [h0] at this
  have hFK : aeval (jNX N hN) (F.map φ) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, Polynomial.map_map, hφ, hroot]
  have hFKm : (F.map φ).Monic := hFm.map φ
  have hint : IsIntegral K (jNX N hN) := ⟨F.map φ, hFKm, hFK⟩
  have hle : (minpoly K (jNX N hN)).natDegree ≤ (Gamma0 N).index := by
    have := natDegree_le_natDegree (minpoly.min K (jNX N hN) hFKm hFK)
    rwa [hFm.natDegree_map, hFdeg] at this
  refine le_antisymm hle ?_
  -- Step 2: clear denominators.
  have htr := ModularFormsKB.Milne.transcendental_jX N
  let e := RatFunc.algEquivOfTranscendental (jX N) htr
  set m := minpoly K (jNX N hN)
  let m₀ : (RatFunc ℂ)[X] := m.map (e.symm : K →+* RatFunc ℂ)
  let ι : RatFunc ℂ →+* MeromorphicFunction (X0 N) :=
    (algebraMap K (MeromorphicFunction (X0 N))).comp (e : RatFunc ℂ →+* K)
  have hm₀ : eval₂ ι (jNX N hN) m₀ = 0 := by
    have hc : ι.comp (e.symm : K →+* RatFunc ℂ) = algebraMap K (MeromorphicFunction (X0 N)) := by
      refine RingHom.ext fun x ↦ ?_
      simp [ι]
    rw [eval₂_map, hc, ← aeval_def, minpoly.aeval]
  have hG := IsLocalization.integerNormalization_eval₂_eq_zero (nonZeroDivisors ℂ[X]) ι m₀ hm₀
  set G := IsLocalization.integerNormalization (nonZeroDivisors ℂ[X]) m₀
  have hι : ι.comp (algebraMap ℂ[X] (RatFunc ℂ)) = (Polynomial.aeval (jX N)).toRingHom := by
    refine RingHom.ext fun p ↦ ?_
    simp only [ι, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
    rw [show e (algebraMap ℂ[X] (RatFunc ℂ) p) = Polynomial.aeval gen p from
      RatFunc.algEquivOfTranscendental_algebraMap _ _ p]
    exact congrArg (fun r ↦ r p) (congrArg DFunLike.coe hφ)
  rw [hι, eval₂_eq_eval_map] at hG
  have hGz : ∀ z : ℍ, (G.map (evalRingHom (j z))).eval (jN hN z) = 0 := fun z ↦
    eval_eq_zero_of_hasVal hG (HasVal.eval_map_aeval (isJOnX0_jX N z) (isJNOnX0_jNX N hN z) G)
  have hGc : ∀ (c : Cosets N) (z : ℍ), (G.map (evalRingHom (j z))).eval (cosetVal hN c z) = 0 := by
    intro c z
    induction c using Quotient.inductionOn with
    | h γ =>
      have := hGz (γ • z)
      rw [jSL] at this
      simpa using this
  -- Degree and leading coefficient of `G`.
  obtain ⟨b, hbM, hbG⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℂ[X]) m₀
  have hmmonic : m.Monic := minpoly.monic hint
  have hm₀monic : m₀.Monic := hmmonic.map _
  have hm₀deg : m₀.natDegree = m.natDegree := hmmonic.natDegree_map _
  have hinj : Function.Injective (algebraMap ℂ[X] (RatFunc ℂ)) := IsFractionRing.injective _ _
  have hGcoeff : G.coeff m.natDegree = b := by
    apply hinj
    rw [← coeff_map, hbG, coeff_smul, ← hm₀deg, hm₀monic.coeff_natDegree, Algebra.smul_def, mul_one]
  have hGdeg : G.natDegree ≤ m.natDegree := by
    have h := congrArg natDegree hbG
    rw [natDegree_map_eq_of_injective hinj] at h
    rw [h, ← hm₀deg]
    exact natDegree_smul_le _ _
  have hb0 : (b : ℂ[X]) ≠ 0 := nonZeroDivisors.ne_zero hbM
  -- Step 3: a point separating the cosets.
  let g : Option {p : Cosets N × Cosets N // p.1 ≠ p.2} → ℍ → ℂ := fun i ↦ match i with
    | none => fun z ↦ (b : ℂ[X]).eval (j z)
    | some p => fun z ↦ cosetVal hN p.1.1 z - cosetVal hN p.1.2 z
  obtain ⟨z₀, hz₀⟩ := exists_forall_ne_zero Finset.univ g
    (fun i _ ↦ by
      rcases i with _ | p
      · exact (b : ℂ[X]).differentiable.mdifferentiable.comp j_mdifferentiable
      · exact (mdiff_cosetVal hN _).sub (mdiff_cosetVal hN _))
    (fun i _ ↦ by
      rcases i with _ | p
      · exact exists_eval_j_ne_zero hb0
      · exact exists_cosetVal_ne hN p.2)
  have hbz : (b : ℂ[X]).eval (j z₀) ≠ 0 := hz₀ none (Finset.mem_univ _)
  have hinjc : Function.Injective fun c : Cosets N ↦ cosetVal hN c z₀ := by
    intro c c' hcc
    by_contra hne
    exact hz₀ (some ⟨(c, c'), hne⟩) (Finset.mem_univ _) (sub_eq_zero.2 hcc)
  set P := G.map (evalRingHom (j z₀))
  have hP0 : P ≠ 0 := by
    intro h
    have := congrArg (fun q ↦ q.coeff m.natDegree) h
    simp only [P, coeff_map, hGcoeff, coe_evalRingHom, coeff_zero] at this
    exact hbz this
  have hsub : (Finset.univ.image fun c : Cosets N ↦ cosetVal hN c z₀).val ⊆ P.roots := by
    intro x hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    exact (mem_roots hP0).2 (hGc c z₀)
  have hcard := card_le_degree_of_subset_roots hsub
  rw [Finset.card_image_of_injective _ hinjc, Finset.card_univ, card_cosets] at hcard
  exact hcard.trans ((natDegree_map_le).trans hGdeg)

end ModularFormsKB.Milne.LevelTwo
