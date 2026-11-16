/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.Gross

/-!
# Gross's formula for prime level, and the ratio at $p = 11$ derived from it

Gross 1987 `gross1987` (Prop. 11.2 and Cor. 11.6 [unverified]) attaches to a weight 2 newform $f$ of prime level $p$ a
weight $3/2$ form $g_f = \tfrac12\sum_i e_i\,\theta_i$: here $R_1, \dots, R_n$ are the maximal orders of the quaternion
algebra ramified at $p$ and $\infty$ up to conjugacy, $w_i = |R_i^\times|/2$, $\theta_i$ is the theta series of Gross's ternary
lattice $S_i$, and $e$ is the eigenvector of the Brandt matrices with the eigenvalues of $f$. His formula: for a
fundamental discriminant $D < 0$ with $p$ inert in $\mathbb Q(\sqrt D)$,
$$ L(f, 1)\,L(f, D, 1)\,\sqrt{|D|} = \kappa_f\,c_f(|D|)^2,\qquad \kappa_f = \frac{(f, f)}{\langle e, e\rangle} > 0, $$
with $c_f(N)$ the $N$-th coefficient of $g_f$.

No library has quaternion orders, so the Brandt module is **data** (`BrandtModule p n`): the weights, the ternary forms
and the Brandt matrices $B(m)$, with Gross's row sums $\sum_j B(m)_{ij} = \sigma(m)$ (Gross 1987, Prop. 2.7 [unverified])
as a field. `GrossFormula` is the formula for every newform and every eigenvector, in the existential form
$\exists \kappa > 0$ (the value $(f,f)/\langle e,e\rangle$ is not stated; loose end LE-MF-0312). The eigenvector convention
($B(m)^{\mathsf T}e = a_m e$, $g_f = \tfrac12\sum e_i\theta_i$, no factor $1/w_i$) is the one of `Gross.lean` at $p = 11$,
which was checked numerically there, including $D = -3, -4$.

**Proved here.**
- `brandt_transpose_eigen_of_rowSum`: with two classes, equal row sums make $e = (1, -1)$ an eigenvector of every
  $B(m)^{\mathsf T}$, with eigenvalue $B(m)_{00} - B(m)_{10}$;
- `repCount_eq_thetaCount₁`, `repCount_eq_thetaCount₂`, `grossCoeff_eq`: the coefficient $c_f(N)$ of `GrossFormula` at
  $p = 11$ is `grossCoeff N`;
- `grossRatio_of_grossFormula`: **`GrossRatio` derived from `GrossFormula 11`**. The only extra input is that the
  eigenvalue $B(m)_{00} - B(m)_{10}$ of $e$ is the coefficient $a_m$ of the newform (Eichler, Gross 1987 §4; proved for
  $m = 2, 3, 5$ on the explicit matrices, `brandt_eigen`). $L(f, 1) \ne 0$ is not needed: the formula at $D_1$
  and $D_2$ gives $\kappa\,(c_1^2\sqrt{|D_2|}L(D_2) - c_2^2\sqrt{|D_1|}L(D_1)) = 0$, and $\kappa > 0$.
-/

namespace ModularFormsKB.HalfIntegral.Waldspurger.Gross

open Complex MatrixGroups CongruenceSubgroup ModularForm

local notation "ℍ" => UpperHalfPlane

/-- **A Brandt module of prime level $p$ with $n$ classes, as data**: weights $w_i = |R_i^\times|/2 > 0$, positive definite
ternary forms $Q_i$ (Gross's lattices $S_i$ with the norm form, in coordinates), and Brandt matrices $B(m)$ whose rows
sum to $\sigma(m) = \sum_{d\mid m}d$ for $(m, p) = 1$ (Gross 1987 `gross1987`, Prop. 2.7 [unverified]). -/
structure BrandtModule (p n : ℕ) where
  w : Fin n → ℕ
  w_pos : ∀ i, 0 < w i
  Q : Fin n → ℤ × ℤ × ℤ → ℤ
  Q_pos : ∀ i x, x ≠ 0 → 0 < Q i x
  B : ℕ → Matrix (Fin n) (Fin n) ℤ
  rowSum : ∀ m, 1 ≤ m → m.Coprime p → ∀ i, ∑ j, B m i j = ∑ d ∈ m.divisors, (d : ℤ)

/-- The number of representations $r_Q(N) = \#\{x \in \mathbb Z^3 : Q(x) = N\}$ (finite for positive definite $Q$;
`Nat.card` is $0$ for an infinite set). -/
noncomputable def repCount (Q : ℤ × ℤ × ℤ → ℤ) (N : ℕ) : ℕ :=
  Nat.card {x : ℤ × ℤ × ℤ // Q x = N}

/-- **The coefficient** $c_e(N) = \tfrac12\sum_i e_i\,r_{Q_i}(N)$ of $g_e = \tfrac12\sum_i e_i\theta_i$. -/
noncomputable def grossCoeffOf {p n : ℕ} (B : BrandtModule p n) (e : Fin n → ℤ) (N : ℕ) : ℝ :=
  (∑ i, (e i : ℝ) * repCount (B.Q i) N) / 2

/-- **Gross's formula for prime level** (Gross 1987 `gross1987`, Prop. 11.2, Cor. 11.6 [unverified]): let $p$ be prime,
$B$ a Brandt module of level $p$, $e \ne 0$ with $\sum e_i = 0$ (orthogonal to the Eisenstein vector), and
$F \in S_2(\Gamma_0(p))$ with coefficients $a$, $a(1) = 1$, such that $B(m)^{\mathsf T}e = a(m)e$ for all $(m, p) = 1$. Then
there is $\kappa > 0$ such that for every fundamental $D < 0$ with $\left(\frac Dp\right) = -1$, and entire continuations
$L_0$ of $\sum a(n)n^{-s}$ and $L$ of $\sum\left(\frac Dn\right)a(n)n^{-s}$,
$$ L_0(1)\,L(1)\,\sqrt{|D|} = \kappa\, c_e(|D|)^2. $$
In Gross, $\kappa = (F, F)/\langle e, e\rangle$, $\langle e, e\rangle = \sum w_ie_i^2$ (not stated here: LE-MF-0312). -/
@[kb "gross1987" "Prop. 11.2, Cor. 11.6: L(f,1) L(f,D,1) √|D| = (f,f)/⟨e,e⟩ · c(|D|)² for p inert in Q(√D) [unverified]"]
structure GrossFormula (p n : ℕ) (B : BrandtModule p n) : Prop where
  formula : p.Prime → ∀ e : Fin n → ℤ, e ≠ 0 → ∑ i, e i = 0 →
    ∀ (F : CuspForm ((Gamma0 p).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2) (a : ℕ → ℂ),
      Abstract.HasQExp F a → a 1 = 1 →
      (∀ m, 1 ≤ m → m.Coprime p → ∀ i, (((B.B m).transpose.mulVec e i : ℤ) : ℂ) = a m * e i) →
      ∃ κ : ℝ, 0 < κ ∧ ∀ L₀ : ℂ → ℂ, IsEntireLSeries a 2 L₀ →
        ∀ D : ℤ, IsFundamentalDiscriminant D → D < 0 → jacobiSym D p = -1 →
          ∀ L : ℂ → ℂ, IsEntireLSeries (fun n ↦ (kroneckerDisc D n : ℂ) * a n) 2 L →
            L₀ 1 * L 1 * (Real.sqrt D.natAbs : ℂ) = ((κ * grossCoeffOf B e D.natAbs ^ 2 : ℝ) : ℂ)

/-- A finset of triples closed under negation and avoiding `0` has even cardinality. -/
theorem even_card_of_neg (s : Finset (ℤ × ℤ × ℤ)) (hs : ∀ x ∈ s, -x ∈ s) (h0 : (0 : ℤ × ℤ × ℤ) ∉ s) :
    Even s.card := by
  have : ∑ _x ∈ s, (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun x _ ↦ -x) (fun x _ ↦ by decide) (fun x hx _ ↦ ?_)
      (fun x hx ↦ hs x hx) (fun x _ ↦ neg_neg x)
    intro h
    have : x = 0 := by
      have h2 : x + x = 0 := by nth_rewrite 1 [← h]; simp
      obtain ⟨a, b, c⟩ := x
      simp only [Prod.mk_add_mk, Prod.mk_eq_zero] at h2
      simp only [Prod.mk_eq_zero]
      omega
    exact h0 (this ▸ hx)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
  exact (ZMod.natCast_eq_zero_iff_even).mp this

theorem thetaCount_even (Q : ℤ × ℤ × ℤ → ℤ) (hQ : ∀ x, Q (-x) = Q x) (hQ0 : Q 0 = 0) {N : ℕ} (hN : 1 ≤ N) :
    Even (thetaCount Q N) := by
  unfold thetaCount
  apply even_card_of_neg
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    refine ⟨?_, by rw [hQ]; exact hx.2⟩
    simp only [box, Finset.mem_product, Finset.mem_Icc, Prod.fst_neg, Prod.snd_neg] at hx ⊢
    omega
  · intro h
    simp only [Finset.mem_filter] at h
    have h2 := h.2
    omega

/-- **With two classes, $e = (1, -1)$ is an eigenvector of every $B(m)^{\mathsf T}$** whose rows have equal sums, with
eigenvalue $B_{00} - B_{10}$. -/
theorem brandt_transpose_eigen_of_rowSum (M : Matrix (Fin 2) (Fin 2) ℤ) (s : ℤ) (h : ∀ i, ∑ j, M i j = s) :
    M.transpose.mulVec grossEigen = (M 0 0 - M 1 0) • grossEigen := by
  have h0 := h 0
  have h1 := h 1
  simp only [Fin.sum_univ_two] at h0 h1
  ext i
  fin_cases i <;>
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, grossEigen]
    omega

/-- $r_{Q_1}(N)$ is the box count `thetaCount grossQ₁ N`. -/
theorem repCount_eq_thetaCount₁ (N : ℕ) : repCount grossQ₁ N = thetaCount grossQ₁ N := by
  unfold repCount thetaCount
  have e : {x : ℤ × ℤ × ℤ // grossQ₁ x = N} ≃ {x // x ∈ (box N).filter (fun x ↦ grossQ₁ x = N)} :=
    Equiv.subtypeEquivRight (fun x ↦ by
      simp only [Finset.mem_filter]
      exact ⟨fun h ↦ ⟨mem_box_of_grossQ₁ h, h⟩, fun h ↦ h.2⟩)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

/-- $r_{Q_2}(N)$ is the box count `thetaCount grossQ₂ N`. -/
theorem repCount_eq_thetaCount₂ (N : ℕ) : repCount grossQ₂ N = thetaCount grossQ₂ N := by
  unfold repCount thetaCount
  have e : {x : ℤ × ℤ × ℤ // grossQ₂ x = N} ≃ {x // x ∈ (box N).filter (fun x ↦ grossQ₂ x = N)} :=
    Equiv.subtypeEquivRight (fun x ↦ by
      simp only [Finset.mem_filter]
      exact ⟨fun h ↦ ⟨mem_box_of_grossQ₂ h, h⟩, fun h ↦ h.2⟩)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

/-- **The coefficient of `GrossFormula` at $p = 11$ is `grossCoeff`**, for $N \ge 1$ (both counts are even: $x \mapsto -x$
has no fixed point on $Q_i(x) = N$). -/
theorem grossCoeff_eq (B : BrandtModule 11 2) (hQ : B.Q = ![grossQ₁, grossQ₂]) {N : ℕ} (hN : 1 ≤ N) :
    grossCoeffOf B grossEigen N = (grossCoeff N : ℝ) := by
  have hc1 := thetaCount_even grossQ₁ (fun x ↦ by simp [grossQ₁]) (by simp [grossQ₁]) hN
  have hc2 := thetaCount_even grossQ₂ (fun x ↦ by simp [grossQ₂]) (by simp [grossQ₂]) hN
  unfold grossCoeffOf
  rw [hQ, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, grossEigen, repCount_eq_thetaCount₁,
    repCount_eq_thetaCount₂]
  obtain ⟨a, ha⟩ := hc1
  obtain ⟨b, hb⟩ := hc2
  unfold grossCoeff
  rw [ha, hb]
  have : ((a + a : ℕ) : ℤ) - ((b + b : ℕ) : ℤ) = 2 * ((a : ℤ) - b) := by push_cast; ring
  rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]
  push_cast
  simp
  ring

/-- **`GrossRatio` derived from `GrossFormula 11`** (row 37): for a Brandt module of level $11$ with Gross's ternary forms,
a form $F \in S_2(\Gamma_0(11))$ with $a(1) = 1$ whose coefficients $a(m)$, $(m, 11) = 1$, are the eigenvalues
$B(m)_{00} - B(m)_{10}$ of $e = (1, -1)$, and entire continuations $L_0$, $L(D, \cdot)$ of its $L$-series, `GrossRatio`
holds for $D \mapsto \operatorname{Re}L(D, 1)$. -/
theorem grossRatio_of_grossFormula (B : BrandtModule 11 2) (hQ : B.Q = ![grossQ₁, grossQ₂])
    (hG : GrossFormula 11 2 B) (F : CuspForm ((Gamma0 11).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2) (a : ℕ → ℂ)
    (hF : Abstract.HasQExp F a) (h1 : a 1 = 1)
    (heig : ∀ m, 1 ≤ m → m.Coprime 11 → ((B.B m 0 0 - B.B m 1 0 : ℤ) : ℂ) = a m)
    (L₀ : ℂ → ℂ) (hL₀ : IsEntireLSeries a 2 L₀) (L : ℤ → ℂ → ℂ)
    (hL : ∀ D, IsEntireLSeries (fun n ↦ (kroneckerDisc D n : ℂ) * a n) 2 (L D)) :
    GrossRatio (fun D ↦ (L D 1).re) := by
  have hsum : ∑ i, grossEigen i = 0 := by simp [grossEigen, Fin.sum_univ_two]
  have hne : grossEigen ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [grossEigen] at this
  have heig' : ∀ m, 1 ≤ m → m.Coprime 11 → ∀ i,
      (((B.B m).transpose.mulVec grossEigen i : ℤ) : ℂ) = a m * grossEigen i := by
    intro m hm hc i
    rw [brandt_transpose_eigen_of_rowSum (B.B m) _ (B.rowSum m hm hc)]
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [← heig m hm hc]
    push_cast
    ring
  obtain ⟨κ, hκ, key⟩ := hG.formula (by decide) grossEigen hne hsum F a hF h1 heig'
  have key' : ∀ D : ℤ, IsFundamentalDiscriminant D → D < 0 → jacobiSym D 11 = -1 →
      L₀ 1 * L D 1 * (Real.sqrt D.natAbs : ℂ) = ((κ * (grossCoeff D.natAbs : ℝ) ^ 2 : ℝ) : ℂ) := by
    intro D h1 h2 h3
    have := key L₀ hL₀ D h1 h2 h3 (L D) (hL D)
    rwa [grossCoeff_eq B hQ (by omega)] at this
  refine ⟨fun D₁ D₂ f₁ f₂ n₁ n₂ j₁ j₂ ↦ ?_⟩
  have e1 := key' D₁ f₁ n₁ j₁
  have e2 := key' D₂ f₂ n₂ j₂
  have hz : (κ : ℂ) * (((grossCoeff D₁.natAbs : ℝ) ^ 2 * Real.sqrt D₂.natAbs : ℝ) * L D₂ 1 -
      ((grossCoeff D₂.natAbs : ℝ) ^ 2 * Real.sqrt D₁.natAbs : ℝ) * L D₁ 1) = 0 := by
    push_cast at e1 e2 ⊢
    linear_combination (-((Real.sqrt D₂.natAbs : ℂ) * L D₂ 1)) * e1 + ((Real.sqrt D₁.natAbs : ℂ) * L D₁ 1) * e2
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hz' := (mul_eq_zero.mp hz).resolve_left hκ'
  have hre := congrArg Complex.re (sub_eq_zero.mp hz')
  rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul] at hre
  exact hre

end ModularFormsKB.HalfIntegral.Waldspurger.Gross
