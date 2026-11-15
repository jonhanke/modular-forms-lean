/-
# The Serre–Stark basis of $M_{1/2}(4N,\chi)$, and the unary theta spaces

**Index set.** For a parity $\nu \in \{0,1\}$, $N \ge 1$ and a character $\chi$ mod $4N$, `unaryIndex ν N χ` is the set
of pairs $(\Phi, t)$ with $\Phi$ a character mod $4N$ of parity $\nu$, $t \ge 1$, $4r^2t \mid 4N$ where $r$ is the
conductor of $\Phi$, and
$$\chi(d) = \Phi(d)\,\chi_{-4}(d)^\nu\Big(\frac t{|d|}\Big) \qquad (d \text{ prime to } 4N).$$
The series attached to $(\Phi,t)$ is $\theta_{\Phi^\ast,t}$ with $\Phi^\ast$ the primitive character inducing $\Phi$
(`unaryThetaOf`). For $\nu = 0$ this is Serre–Stark's set $\Omega(4N,\chi)$ of pairs $(\psi, t)$, $\psi$ even primitive
(Serre–Stark 1977 `serrestark1977`, §1 [unverified]); a primitive $\psi$ is recorded through the character
$\Phi$ mod $4N$ it induces, which determines it. The character relation is the one of Shimura's law for
$\theta_{\psi,t}$ (Shimura 1973 `shimura1973`, Prop. 2.2 [unverified]; the form used in `ThetaTwistLaw`, where the
weight $\tfrac32$ factor $(cz+d)$ is $\chi_{-4}(d)\,j(\gamma,z)^2$).

**Named inputs.**
- `UnaryThetaModular ν N χ`: the series of `unaryIndex ν N χ` lie in $M_{\nu+1/2}(4N,\chi)$; in weight $\tfrac12$,
  $\theta_{\psi,t}$ is a cusp form exactly when $\psi$ is not totally even; in weight $\tfrac32$ all are cusp forms
  (Shimura 1973, Prop. 2.2 for the law; Serre–Stark 1977, §3 for the cusps [unverified]).
- `SerreStarkSpan N χ` (Theorem A, the spanning half) and `SerreStarkCuspSpan N χ` (Theorem B, the spanning half):
  Serre–Stark 1977, Theorems A and B [unverified].

**Proved.**
- `serreStark_basis`: the $\theta_{\psi,t}$, $(\psi,t) \in \Omega(4N,\chi)$, form a basis of $M_{1/2}(4N,\chi)$ (Serre–Stark's
  Theorem A); `serreStark_finrank`.
- `serreStark_cusp_basis`: those with $\psi$ not totally even form a basis of $S_{1/2}(4N,\chi)$ (Theorem B).
- `serreStark_coeff_support`: every $f \in M_{1/2}(4N,\chi)$ has its nonzero coefficients $a(n)$, $n \ge 1$, on the square
  classes $t\cdot\square$ with $(\psi, t) \in \Omega(4N,\chi)$, so on finitely many square classes, with $t \mid N$.
- `unaryThetaSpace_le_cuspForms`, `unaryThetaSpace_coeff_support`, `linearIndependent_unaryThetaOf`: the weight $\tfrac32$
  span $U_{3/2}(4N,\chi)$ of the $\sum\psi(n)nq^{tn^2}$ is a space of cusp forms whose elements are supported on finitely
  many square classes.

The independence half of Theorems A and B is proved (`linearIndependent_unaryTheta`); only the spanning halves are named.
-/
import ModularFormsKB.HalfIntegral.UnaryTheta
import ModularFormsKB.HalfIntegral.Forms
import ModularFormsKB.HalfIntegral.Abstract.KohnenReduction
import ModularFormsKB.HalfIntegral.Abstract.KohnenEigen

namespace ModularFormsKB.HalfIntegral

open Complex
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- **Totally even** (Serre–Stark 1977 `serrestark1977`, §1 [unverified]): every local component $\psi_p$ of $\psi$ is even.
Stated without the decomposition: $\psi(a) = 1$ for every integer $a \equiv -1 \bmod p^{e}$, $a \equiv 1 \bmod r/p^{e}$,
$p^e \parallel r$ (such an $a$ represents $-1$ in the $p$-component and $1$ elsewhere). -/
def IsTotallyEven {r : ℕ} (ψ : DirichletCharacter ℂ r) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ a : ℤ, a ≡ -1 [ZMOD ((p ^ r.factorization p : ℕ) : ℤ)] →
    a ≡ 1 [ZMOD ((r / p ^ r.factorization p : ℕ) : ℤ)] → ψ (a : ZMod r) = 1

/-- **The index set** $\Omega_\nu(4N,\chi)$: pairs $(\Phi, t)$, $\Phi$ mod $4N$ of parity $\nu$, $t \ge 1$,
$4\,\mathrm{cond}(\Phi)^2t \mid 4N$, $\chi(d) = \Phi(d)\chi_{-4}(d)^\nu(t/|d|)$ for $d$ prime to $4N$. -/
def unaryIndex (ν N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Set (DirichletCharacter ℂ (4 * N) × ℕ) :=
  {p | charParity p.1 = ν ∧ 1 ≤ p.2 ∧ 4 * p.1.conductor ^ 2 * p.2 ∣ 4 * N ∧
    ∀ d : ℤ, IsCoprime d (4 * N : ℤ) →
      χ (d : ZMod (4 * N)) = p.1 (d : ZMod (4 * N)) * (ZMod.χ₄ (d : ZMod 4) : ℂ) ^ ν * (jacobiSym p.2 d.natAbs : ℂ)}

/-- The unary theta series attached to $(\Phi, t)$: $\theta_{\Phi^\ast,t}$ as a function on $\mathbb H$. -/
noncomputable def unaryThetaOf {L : ℕ} (p : DirichletCharacter ℂ L × ℕ) : ℍ → ℂ :=
  fun τ ↦ unaryTheta p.1.primitiveCharacter p.2 τ

/-- The pairs of $\Omega_0(4N,\chi)$ whose primitive character is not totally even. -/
def unaryIndexCusp (N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Set (DirichletCharacter ℂ (4 * N) × ℕ) :=
  {p | p ∈ unaryIndex 0 N χ ∧ ¬ IsTotallyEven p.1.primitiveCharacter}

/-- **Membership of the unary theta series** (Shimura 1973 `shimura1973`, Prop. 2.2: the law; Serre–Stark 1977
`serrestark1977`, §3: behaviour at the cusps [unverified]). For $(\Phi, t) \in \Omega_\nu(4N,\chi)$,
$\theta_{\Phi^\ast,t} \in M_{\nu+1/2}(4N,\chi)$; for $\nu = 0$ it is a cusp form iff $\Phi^\ast$ is not totally even; for
$\nu = 1$ it is a cusp form. -/
@[kb "serrestark1977" "§3 (with Shimura 1973, Prop. 2.2): theta_{psi,t} lies in M_{1/2}(N, chi) for (psi,t) in Omega(N,chi), and is a cusp form iff psi is not totally even [unverified]"]
structure UnaryThetaModular (ν N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop where
  mem : ∀ p ∈ unaryIndex ν N χ, unaryThetaOf p ∈ halfIntModularForms ν N χ
  cusp_iff : ν = 0 → ∀ p ∈ unaryIndex ν N χ,
    (unaryThetaOf p ∈ halfIntCuspForms ν N χ ↔ ¬ IsTotallyEven p.1.primitiveCharacter)
  cusp_odd : ν = 1 → ∀ p ∈ unaryIndex ν N χ, unaryThetaOf p ∈ halfIntCuspForms ν N χ

/-- **Serre–Stark, Theorem A, spanning half** (Serre–Stark 1977 `serrestark1977`, Theorem A [unverified]): every
$f \in M_{1/2}(4N,\chi)$ is a linear combination of the $\theta_{\psi,t}$, $(\psi,t) \in \Omega(4N,\chi)$. -/
@[kb "serrestark1977" "Theorem A: the theta_{psi,t}, (psi,t) in Omega(N,chi), span M_{1/2}(N,chi) (and form a basis) [unverified]"]
structure SerreStarkSpan (N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop where
  span : halfIntModularForms 0 N χ ≤ Submodule.span ℂ (unaryThetaOf '' unaryIndex 0 N χ)

/-- **Serre–Stark, Theorem B, spanning half** (Serre–Stark 1977 `serrestark1977`, Theorem B [unverified]): every
$f \in S_{1/2}(4N,\chi)$ is a linear combination of the $\theta_{\psi,t}$ with $\psi$ not totally even. -/
@[kb "serrestark1977" "Theorem B: the theta_{psi,t} with psi not totally even span S_{1/2}(N,chi) [unverified]"]
structure SerreStarkCuspSpan (N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Prop where
  span : halfIntCuspForms 0 N χ ≤ Submodule.span ℂ (unaryThetaOf '' unaryIndexCusp N χ)

theorem unaryIndex_props {ν N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ (4 * N)} :
    ∀ p ∈ unaryIndex ν N χ, 1 ≤ p.2 ∧ p.2 ∣ 4 * N ∧ charParity p.1 = ν := by
  rintro p ⟨hν, ht, hdvd, -⟩
  exact ⟨ht, dvd_trans (Dvd.intro_left _ rfl) hdvd, hν⟩

/-- **Linear independence of the series of $\Omega_\nu(4N,\chi)$** (unconditional). -/
theorem linearIndependent_unaryThetaOf {ν N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ (4 * N))
    (s : Set (DirichletCharacter ℂ (4 * N) × ℕ)) (hs : s ⊆ unaryIndex ν N χ) :
    LinearIndependent ℂ (fun p : s ↦ unaryThetaOf p.1) :=
  linearIndependent_unaryTheta ν s fun p hp ↦ unaryIndex_props p (hs hp)

/-- A family of elements of a submodule that is linearly independent and spans it is a basis of it. -/
private noncomputable def basisOfSpan {ι : Type*} {V : Submodule ℂ (ℍ → ℂ)} (v : ι → ℍ → ℂ) (hv : ∀ i, v i ∈ V)
    (hli : LinearIndependent ℂ v) (hsp : V ≤ Submodule.span ℂ (Set.range v)) : Module.Basis ι ℂ V :=
  Module.Basis.mk (v := fun i ↦ (⟨v i, hv i⟩ : V))
    (LinearIndependent.of_comp V.subtype hli)
    (by
      rintro ⟨f, hf⟩ -
      have h : f ∈ Submodule.map V.subtype
          (Submodule.span ℂ (Set.range fun i ↦ (⟨v i, hv i⟩ : V))) := by
        rw [Submodule.map_span, ← Set.range_comp]
        exact hsp hf
      obtain ⟨w, hw, hwf⟩ := h
      have : w = ⟨f, hf⟩ := Subtype.ext hwf
      rw [← this]
      exact hw)

private theorem basisOfSpan_apply {ι : Type*} {V : Submodule ℂ (ℍ → ℂ)} (v : ι → ℍ → ℂ) (hv : ∀ i, v i ∈ V)
    (hli : LinearIndependent ℂ v) (hsp : V ≤ Submodule.span ℂ (Set.range v)) (i : ι) :
    (basisOfSpan v hv hli hsp i : ℍ → ℂ) = v i := by
  simp [basisOfSpan]

private theorem image_eq_range' {L : ℕ} (s : Set (DirichletCharacter ℂ L × ℕ)) :
    unaryThetaOf '' s = Set.range (fun p : s ↦ unaryThetaOf p.1) :=
  Set.image_eq_range _ _

/-- **Serre–Stark, Theorem A** (Serre–Stark 1977 `serrestark1977`, Theorem A [unverified]): for $N \ge 1$ the unary
theta series $\theta_{\psi,t}$, $(\psi,t) \in \Omega(4N,\chi)$, form a basis of $M_{1/2}(4N,\chi)$. Conditional on
`UnaryThetaModular` (membership) and `SerreStarkSpan` (spanning); linear independence is proved. -/
theorem serreStark_basis {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ (4 * N)} (hmem : UnaryThetaModular 0 N χ)
    (hA : SerreStarkSpan N χ) :
    ∃ b : Module.Basis (unaryIndex 0 N χ) ℂ (halfIntModularForms 0 N χ),
      ∀ p, (b p : ℍ → ℂ) = unaryThetaOf p.1 := by
  have hsp := hA.span
  rw [image_eq_range'] at hsp
  exact ⟨basisOfSpan _ (fun p ↦ hmem.mem p.1 p.2) (linearIndependent_unaryThetaOf χ _ subset_rfl) hsp,
    basisOfSpan_apply _ _ _ _⟩

/-- **Serre–Stark, Theorem B** (Serre–Stark 1977 `serrestark1977`, Theorem B [unverified]): the $\theta_{\psi,t}$ with
$(\psi,t) \in \Omega(4N,\chi)$ and $\psi$ not totally even form a basis of $S_{1/2}(4N,\chi)$. -/
theorem serreStark_cusp_basis {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ (4 * N)} (hmem : UnaryThetaModular 0 N χ)
    (hB : SerreStarkCuspSpan N χ) :
    ∃ b : Module.Basis (unaryIndexCusp N χ) ℂ (halfIntCuspForms 0 N χ),
      ∀ p, (b p : ℍ → ℂ) = unaryThetaOf p.1 := by
  have hsp := hB.span
  rw [image_eq_range'] at hsp
  exact ⟨basisOfSpan _ (fun p ↦ (hmem.cusp_iff rfl p.1 p.2.1).2 p.2.2)
    (linearIndependent_unaryThetaOf (ν := 0) χ _ fun p hp ↦ hp.1) hsp, basisOfSpan_apply _ _ _ _⟩

/-- $\dim M_{1/2}(4N,\chi) = \#\Omega(4N,\chi)$. -/
theorem serreStark_finrank {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ (4 * N)} (hmem : UnaryThetaModular 0 N χ)
    (hA : SerreStarkSpan N χ) :
    Module.finrank ℂ (halfIntModularForms 0 N χ) = Nat.card (unaryIndex 0 N χ) := by
  obtain ⟨b, -⟩ := serreStark_basis hmem hA
  exact Module.finrank_eq_nat_card_basis b

/-- **Coefficients on finitely many square classes.** If $f = \sum_p c_p\,\theta_p$ is a finite combination of unary theta
series of a set $s$ of pairs with $t \ge 1$, its coefficients $a(n)$, $n \ge 1$, vanish off $\bigcup_{(\Phi,t)\in s}t\cdot\square$. -/
theorem coeff_support_of_mem_span {L : ℕ} {s : Set (DirichletCharacter ℂ L × ℕ)} (hs : ∀ p ∈ s, 1 ≤ p.2)
    {f : ℍ → ℂ} (hf : f ∈ Submodule.span ℂ (unaryThetaOf '' s)) {a : ℕ → ℂ} (ha : Abstract.HasQExp f a)
    {n : ℕ} (hn : n ≠ 0) (han : a n ≠ 0) : ∃ p ∈ s, ∃ m : ℕ, n = p.2 * m ^ 2 := by
  -- every element of the span has a $q$-expansion supported on the square classes of `s`
  have key : ∃ b : ℕ → ℂ, Abstract.HasQExp f b ∧
      ∀ n : ℕ, n ≠ 0 → b n ≠ 0 → ∃ p ∈ s, ∃ m : ℕ, n = p.2 * m ^ 2 := by
    clear ha han
    induction hf using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨p, hp, rfl⟩ := hg
      refine ⟨unaryThetaCoeff p.1.primitiveCharacter p.2, hasQExp_unaryTheta _ (hs p hp), fun n hn hb ↦ ?_⟩
      by_contra h
      push Not at h
      exact hb (unaryThetaCoeff_eq_zero_of_not _ hn fun ⟨m, hm⟩ ↦ h p hp m hm)
    | zero => exact ⟨0, Abstract.hasQExp_zero, fun n _ h ↦ absurd rfl h⟩
    | add g₁ g₂ _ _ h₁ h₂ =>
      obtain ⟨b₁, hb₁, hs₁⟩ := h₁
      obtain ⟨b₂, hb₂, hs₂⟩ := h₂
      refine ⟨b₁ + b₂, Abstract.hasQExp_add hb₁ hb₂, fun n hn hb ↦ ?_⟩
      by_cases h : b₁ n = 0
      · exact hs₂ n hn (by simpa [h] using hb)
      · exact hs₁ n hn h
    | smul c g _ h =>
      obtain ⟨b, hb, hsb⟩ := h
      refine ⟨c • b, Abstract.hasQExp_smul c hb, fun n hn h ↦ hsb n hn ?_⟩
      intro h0
      exact h (by simp [h0])
  obtain ⟨b, hb, hsb⟩ := key
  rw [Abstract.hasQExp_unique ha hb] at han
  exact hsb n hn han

/-- **Serre–Stark: the coefficients of a weight-$\tfrac12$ form lie on finitely many square classes.** For
$f = \sum a(n)q^n \in M_{1/2}(4N,\chi)$ and $n \ge 1$ with $a(n) \ne 0$, $n = tm^2$ for some $(\psi,t) \in \Omega(4N,\chi)$;
in particular $t \mid N$. Conditional on `SerreStarkSpan`. -/
theorem serreStark_coeff_support {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ (4 * N)} (hA : SerreStarkSpan N χ)
    {f : ℍ → ℂ} (hf : f ∈ halfIntModularForms 0 N χ) {a : ℕ → ℂ} (ha : Abstract.HasQExp f a)
    {n : ℕ} (hn : n ≠ 0) (han : a n ≠ 0) :
    ∃ t : ℕ, t ∣ N ∧ (∃ p ∈ unaryIndex 0 N χ, p.2 = t) ∧ ∃ m : ℕ, n = t * m ^ 2 := by
  obtain ⟨p, hp, m, hm⟩ := coeff_support_of_mem_span (s := unaryIndex 0 N χ) (fun p hp ↦ hp.2.1) (hA.span hf) ha hn han
  refine ⟨p.2, ?_, ⟨p, hp, rfl⟩, m, hm⟩
  have h := hp.2.2.1
  have h4 : 4 * p.2 ∣ 4 * N :=
    dvd_trans ⟨p.1.conductor ^ 2, by ring⟩ h
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h4

/-! ### Weight $\tfrac32$: the unary theta space -/

/-- **The unary theta space** $U_{3/2}(4N,\chi)$: the span of the $\theta_{\psi,t} = \sum\psi(n)nq^{tn^2}$, $\psi$ odd,
$(\psi, t) \in \Omega_1(4N,\chi)$ (Duke–Schulze-Pillot 1990 `dukeschulzepillot1990`, §1; Schulze-Pillot 1984
`schulzepillot1984` [unverified]). -/
noncomputable def unaryThetaSpace (N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : Submodule ℂ (ℍ → ℂ) :=
  Submodule.span ℂ (unaryThetaOf '' unaryIndex 1 N χ)

/-- $U_{3/2}(4N,\chi) \subseteq S_{3/2}(4N,\chi)$, given the membership input. -/
theorem unaryThetaSpace_le_cuspForms {N : ℕ} {χ : DirichletCharacter ℂ (4 * N)} (hmem : UnaryThetaModular 1 N χ) :
    unaryThetaSpace N χ ≤ halfIntCuspForms 1 N χ := by
  rw [unaryThetaSpace, Submodule.span_le]
  rintro _ ⟨p, hp, rfl⟩
  exact hmem.cusp_odd rfl p hp

/-- **The unary theta space is supported on finitely many square classes**: for $g \in U_{3/2}(4N,\chi)$ with
$q$-expansion $a$ and $n \ge 1$, $a(n) \ne 0$ forces $n = tm^2$ with $(\psi, t) \in \Omega_1(4N,\chi)$, so $t \mid N$. -/
theorem unaryThetaSpace_coeff_support {N : ℕ} {χ : DirichletCharacter ℂ (4 * N)} {g : ℍ → ℂ}
    (hg : g ∈ unaryThetaSpace N χ) {a : ℕ → ℂ} (ha : Abstract.HasQExp g a) {n : ℕ} (hn : n ≠ 0) (han : a n ≠ 0) :
    ∃ p ∈ unaryIndex 1 N χ, ∃ m : ℕ, n = p.2 * m ^ 2 :=
  coeff_support_of_mem_span (s := unaryIndex 1 N χ) (fun p hp ↦ hp.2.1) hg ha hn han

/-- $U_{3/2}(4N,\chi)$ is finite-dimensional, of dimension $\#\Omega_1(4N,\chi)$: the series are linearly independent. -/
theorem finrank_unaryThetaSpace {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ (4 * N)) :
    Module.finrank ℂ (unaryThetaSpace N χ) = Nat.card (unaryIndex 1 N χ) := by
  have hsp : unaryThetaSpace N χ ≤ Submodule.span ℂ (Set.range fun p : unaryIndex 1 N χ ↦ unaryThetaOf p.1) := by
    rw [unaryThetaSpace, image_eq_range']
  have hv : ∀ p : unaryIndex 1 N χ, unaryThetaOf p.1 ∈ unaryThetaSpace N χ :=
    fun p ↦ Submodule.subset_span ⟨p.1, p.2, rfl⟩
  exact Module.finrank_eq_nat_card_basis
    (basisOfSpan _ hv (linearIndependent_unaryThetaOf χ _ subset_rfl) hsp)

end ModularFormsKB.HalfIntegral
