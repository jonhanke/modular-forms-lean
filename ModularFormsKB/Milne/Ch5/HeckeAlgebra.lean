import TauCeti.NumberTheory.HeckeRing.GL2.Recurrence
import TauCeti.NumberTheory.HeckeRing.GL2.MultiplicationTable
import TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets
import ModularFormsKB.Miyake.HeckeAlgebras

/-!
# Milne, Chapter 5: the Hecke algebra $H(\Gamma(1), \Delta)$ (pp. 81–82, Example 5.32)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf pp. 81–82.

Milne's Hecke algebra $H(\Gamma, \Delta)$ (the free $\mathbb Z$-module on the double cosets $\Gamma\alpha\Gamma$,
$\alpha \in \Delta$, with the product $[\alpha][\beta] = \sum_\gamma c^\gamma_{\alpha\beta}[\gamma]$) is Tau Ceti's
`HeckeCosetModule` with its convolution product (`TauCeti/NumberTheory/HeckeRing/Multiplication.lean`), for any
Hecke triple; for $\Gamma = \Gamma(1)$ and $\Delta$ the integer matrices of positive determinant it is
`HeckeRing.GLn.IntegralHeckeRing 2`. Milne counts the structure constants with right cosets,
$c^\gamma_{\alpha\beta} = \#\{(i, j) : \alpha_i\beta_j \in \Gamma\gamma\}$ for $\Gamma\alpha\Gamma = \bigsqcup\Gamma\alpha_i$,
$\Gamma\beta\Gamma = \bigsqcup\Gamma\beta_j$; Tau Ceti counts with left cosets (Shimura's multiplicity). For
$\Gamma(1)$ the two agree (`coeff_single_mul_single_eq_card`). Milne's $T(a, d)$, $T(p)$ and $T(n)$ are Tau Ceti's
`HeckeRing.GL2.heckeTDiag a d`, `heckeT p` and `heckeT n`.

## Items
- The structure constants of $H(\Gamma(1), \Delta)$, p. 81 (`coeff_single_mul_single_eq_card`).
- Example 5.32 (`heckeBasis`, `heckeBasis_apply`).
- $T(p) = T(1, p)$ and $T(n) = \sum_{a \mid d,\, ad = n} T(a, d)$, p. 82 (`heckeT_prime_eq`, `heckeT_eq_sum`).
- The relation (8), p. 82 (`heckeT_mul_heckeT`, `heckeT_mul_of_coprime'`, `heckeRingT_prime_mul_prime_pow`).
-/

open HeckeRing HeckeRing.GLn HeckeRing.GL2 DoubleCoset

namespace ModularFormsKB.Milne


/-- Transposition on `GL₂(ℚ)` (helper for `coeff_single_mul_single_eq_card`). -/
private noncomputable abbrev trG (g : GL (Fin 2) ℚ) : GL (Fin 2) ℚ := (Matrix.GeneralLinearGroup.transposeMulEquiv (Fin 2) g).unop

private lemma trG_mul (x y : GL (Fin 2) ℚ) : trG (x * y) = trG y * trG x := by simp [trG]

private lemma trG_inv (x : GL (Fin 2) ℚ) : trG x⁻¹ = (trG x)⁻¹ := by simp [trG]

private lemma trG_trG (x : GL (Fin 2) ℚ) : trG (trG x) = x := Matrix.GeneralLinearGroup.transposeMulEquiv_transposeMulEquiv x

private lemma trG_mem_Γ {x : GL (Fin 2) ℚ} : trG x ∈ SLnZ 2 ↔ x ∈ SLnZ 2 :=
  ⟨fun h ↦ by simpa [trG_trG] using transposeMulEquiv_mem_SLnZ 2 h, transposeMulEquiv_mem_SLnZ 2⟩

/-- Transposition preserves every double coset of the arithmetic Hecke triple. -/
private lemma trG_mem_toSet (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))
    {x : GL (Fin 2) ℚ} (hx : x ∈ D.toSet) : trG x ∈ D.toSet := by
  have hxΔ : x ∈ posDetInt 2 := by
    rw [HeckeCoset.toSet_eq_doubleCoset_rep] at hx
    exact IsHeckeTriple.mem_of_mem_doubleCoset D.rep.2 hx
  have h1 := HeckeCoset.mem_toSet_iff.mp (show ((⟨x, hxΔ⟩ : posDetInt 2) : GL (Fin 2) ℚ) ∈ D.toSet
    from hx)
  have h2 := (transposeAntiInvolution 2).onHeckeCoset_mk (⟨x, hxΔ⟩ : posDetInt 2)
  rw [h1, transposeAntiInvolution_onHeckeCoset_eq_self] at h2
  have h3 := HeckeCoset.mem_toSet_iff.mpr h2.symm
  simpa [transposeAntiInvolution_bar] using h3

private lemma trG_mem_toSet_iff (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))
    {x : GL (Fin 2) ℚ} : trG x ∈ D.toSet ↔ x ∈ D.toSet :=
  ⟨fun h ↦ by simpa [trG_trG] using trG_mem_toSet D h, trG_mem_toSet D⟩

/-- A double coset is stable under multiplication by `SL₂(ℤ)` on either side. -/
private lemma mul_mem_toSet' {D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2)}
    {x u : GL (Fin 2) ℚ} (hx : x ∈ D.toSet) (hu : u ∈ SLnZ 2) :
    u * x ∈ D.toSet ∧ x * u ∈ D.toSet := by
  rw [HeckeCoset.toSet_eq_doubleCoset_rep] at hx ⊢
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hx
  exact ⟨mem_doubleCoset.mpr ⟨u * a, mul_mem hu ha, b, hb, by simp [mul_assoc]⟩,
    mem_doubleCoset.mpr ⟨a, ha, b * u, mul_mem hb hu, by simp [mul_assoc]⟩⟩

private lemma exists_out_aux (D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2)) {z : GL (Fin 2) ℚ}
    (hz : z ∈ D.toSet) :
    ∃ i : DecompQuotient (SLnZ 2) (SLnZ 2) (D.rep : GL (Fin 2) ℚ),
      ((i.out : GL (Fin 2) ℚ) * (D.rep : GL (Fin 2) ℚ))⁻¹ * z ∈ SLnZ 2 := by
  rw [HeckeCoset.toSet_eq_doubleCoset_rep, doubleCoset_eq_iUnion_leftCosets, Set.mem_iUnion] at hz
  obtain ⟨i, hi⟩ := hz
  obtain ⟨k, hk, hkz⟩ := hi
  exact ⟨i, by rw [← hkz]; simp only [smul_eq_mul, inv_mul_cancel_left]; exact hk⟩

private lemma out_unique_aux (g z : GL (Fin 2) ℚ)
    {i j : DecompQuotient (SLnZ 2) (SLnZ 2) g}
    (hi : ((i.out : GL (Fin 2) ℚ) * g)⁻¹ * z ∈ SLnZ 2)
    (hj : ((j.out : GL (Fin 2) ℚ) * g)⁻¹ * z ∈ SLnZ 2) : i = j := by
  refine mk_out_mul_injective _ _ g ?_
  show (((i.out : GL (Fin 2) ℚ) * g : GL (Fin 2) ℚ) : GL (Fin 2) ℚ ⧸ SLnZ 2) =
    (((j.out : GL (Fin 2) ℚ) * g : GL (Fin 2) ℚ) : GL (Fin 2) ℚ ⧸ SLnZ 2)
  rw [QuotientGroup.eq]
  have := mul_mem hi (inv_mem hj)
  simpa [mul_assoc] using this

/-- Milne's right-coset count is the number of right-coset representatives `β_j` with
`γ β_j⁻¹ ∈ D₁`. -/
private lemma card_pairs_eq_card_right (D₁ : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))
    {ι κ : Type*} (α : ι → GL (Fin 2) ℚ) (β : κ → GL (Fin 2) ℚ)
    (hα : ∀ x ∈ D₁.toSet, ∃! i, x * (α i)⁻¹ ∈ SLnZ 2) (hα' : ∀ i, α i ∈ D₁.toSet)
    (γ : GL (Fin 2) ℚ) :
    Nat.card {p : ι × κ | α p.1 * β p.2 * γ⁻¹ ∈ SLnZ 2} =
      Nat.card {j : κ | γ * (β j)⁻¹ ∈ D₁.toSet} := by
  have key : ∀ i j, α i * β j * γ⁻¹ ∈ SLnZ 2 → γ * (β j)⁻¹ * (α i)⁻¹ ∈ SLnZ 2 := fun i j h ↦ by
    simpa [mul_assoc] using inv_mem h
  refine Nat.card_congr (Equiv.ofBijective
    (fun p ↦ (⟨p.1.2, ?_⟩ : {j : κ | γ * (β j)⁻¹ ∈ D₁.toSet})) ⟨?_, ?_⟩)
  · have h := (mul_mem_toSet' (hα' p.1.1) (key _ _ p.2)).1
    simpa [mul_assoc] using h
  · rintro ⟨⟨i, j⟩, h⟩ ⟨⟨i', j'⟩, h'⟩ hf
    have hj : j = j' := congrArg Subtype.val hf
    subst hj
    have hx : γ * (β j)⁻¹ ∈ D₁.toSet := by
      have h := (mul_mem_toSet' (hα' i) (key _ _ h)).1
      simpa [mul_assoc] using h
    obtain ⟨i0, -, hu⟩ := hα _ hx
    have e1 := hu i (key _ _ h)
    have e2 := hu i' (key _ _ h')
    exact Subtype.ext (Prod.ext (e1.trans e2.symm) rfl)
  · rintro ⟨j, hj⟩
    obtain ⟨i, hi, -⟩ := hα _ hj
    refine ⟨⟨(i, j), ?_⟩, rfl⟩
    simpa [mul_assoc] using inv_mem hi

/-- Right-coset representatives `β_j` with `γ β_j⁻¹ ∈ D₁` correspond (by transposition) to
left-coset representatives `x_i` of `D₂` with `x_i⁻¹ γᵀ ∈ D₁`. -/
private lemma card_right_eq_card_left (D₁ D₂ : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))
    {κ : Type*} [Finite κ] (β : κ → GL (Fin 2) ℚ)
    (hβ : ∀ x ∈ D₂.toSet, ∃! j, x * (β j)⁻¹ ∈ SLnZ 2) (hβ' : ∀ j, β j ∈ D₂.toSet)
    (γ : GL (Fin 2) ℚ) :
    Nat.card {j : κ | γ * (β j)⁻¹ ∈ D₁.toSet} =
      Nat.card {i : DecompQuotient (SLnZ 2) (SLnZ 2) (D₂.rep : GL (Fin 2) ℚ) |
        ((i.out : GL (Fin 2) ℚ) * (D₂.rep : GL (Fin 2) ℚ))⁻¹ * trG γ ∈ D₁.toSet} := by
  choose f hf using fun j ↦ exists_out_aux D₂ (trG_mem_toSet D₂ (hβ' j))
  have hmem : ∀ j, γ * (β j)⁻¹ ∈ D₁.toSet ↔
      ((f j).out * (D₂.rep : GL (Fin 2) ℚ))⁻¹ * trG γ ∈ D₁.toSet := by
    intro j
    have e : ((f j).out * (D₂.rep : GL (Fin 2) ℚ))⁻¹ * trG γ =
        (((f j).out * (D₂.rep : GL (Fin 2) ℚ))⁻¹ * trG (β j)) * trG (γ * (β j)⁻¹) := by
      simp [trG_mul, trG_inv, mul_assoc]
    rw [e, ← trG_mem_toSet_iff D₁]
    constructor
    · intro h
      exact (mul_mem_toSet' h (hf j)).1
    · intro h
      have := (mul_mem_toSet' h (inv_mem (hf j))).1
      simpa [mul_assoc, trG_trG] using this
  have finj : Function.Injective f := by
    intro j j' h
    have h1 := hf j
    have h2 := hf j'
    rw [← h] at h2
    have h3 := mul_mem (inv_mem h1) h2
    have h3' : (trG (β j))⁻¹ * trG (β j') ∈ SLnZ 2 := by simpa [mul_assoc] using h3
    have h4 : β j' * (β j)⁻¹ ∈ SLnZ 2 := by
      have := trG_mem_Γ.mpr h3'
      simpa [trG_mul, trG_inv, trG_trG, mul_assoc] using this
    obtain ⟨j0, -, hu⟩ := hβ (β j') (hβ' j')
    exact (hu j h4).trans (hu j' (by simp)).symm
  refine Nat.card_congr (Equiv.ofBijective (fun j ↦ ⟨f j, (hmem j.1).mp j.2⟩) ⟨?_, ?_⟩)
  · intro a b h
    exact Subtype.ext (finj (congrArg Subtype.val h))
  · rintro ⟨i, hi⟩
    have hz : trG ((i.out : GL (Fin 2) ℚ) * D₂.rep) ∈ D₂.toSet := by
      apply trG_mem_toSet
      rw [HeckeCoset.toSet_eq_doubleCoset_rep]
      exact mem_doubleCoset.mpr ⟨i.out, i.out.2, 1, one_mem _, by simp⟩
    obtain ⟨j, hj, -⟩ := hβ _ hz
    have hk : ((i.out : GL (Fin 2) ℚ) * D₂.rep)⁻¹ * trG (β j) ∈ SLnZ 2 := by
      have := inv_mem (trG_mem_Γ.mpr hj)
      simpa [trG_mul, trG_inv, trG_trG, mul_assoc] using this
    have hij : i = f j := out_unique_aux _ (trG (β j)) hk (hf j)
    subst hij
    exact ⟨⟨j, (hmem j).mpr hi⟩, rfl⟩

/-- **Milne's structure constants** (p. 81) for $H(\Gamma(1), \Delta)$: if $\alpha_i$ and $\beta_j$ are
representatives of the right cosets in $D_1 = \Gamma\alpha\Gamma$ and $D_2 = \Gamma\beta\Gamma$, the coefficient of
$[D] = [\Gamma\gamma\Gamma]$ in $[D_1][D_2]$ is $\#\{(i, j) : \alpha_i\beta_j \in \Gamma\gamma\}$. -/
@[kb "milne2017mf" "Section 5, the Hecke algebra H(Gamma, Delta) and its multiplication (pdf pp. 81-82)"]
theorem coeff_single_mul_single_eq_card (D₁ D₂ D : HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2))
    {ι κ : Type*} [Finite ι] [Finite κ] (α : ι → GL (Fin 2) ℚ) (β : κ → GL (Fin 2) ℚ)
    (hα : ∀ x ∈ D₁.toSet, ∃! i, x * (α i)⁻¹ ∈ SLnZ 2) (hα' : ∀ i, α i ∈ D₁.toSet)
    (hβ : ∀ x ∈ D₂.toSet, ∃! j, x * (β j)⁻¹ ∈ SLnZ 2) (hβ' : ∀ j, β j ∈ D₂.toSet)
    {γ : GL (Fin 2) ℚ} (hγ : γ ∈ D.toSet) :
    (HeckeCosetModule.single ℤ D₁ 1 * HeckeCosetModule.single ℤ D₂ 1 : IntegralHeckeRing 2) D =
      Nat.card {p : ι × κ | α p.1 * β p.2 * γ⁻¹ ∈ SLnZ 2} := by
  have hcomm := HeckeCosetModule.mul_comm_of_antiInvolution ℤ (transposeAntiInvolution 2)
    (transposeAntiInvolution_onHeckeCoset_eq_self 2)
    (HeckeCosetModule.single ℤ D₁ 1) (HeckeCosetModule.single ℤ D₂ 1)
  rw [hcomm, card_pairs_eq_card_right D₁ α β hα hα' γ, card_right_eq_card_left D₁ D₂ β hβ hβ' γ,
    HeckeCosetModule.single_mul_single]
  simp only [HeckeCosetModule.smul_apply, one_mul,
    HeckeCosetModule.structureConstants_apply]
  have hd : trG γ ∈ doubleCoset (D.rep : GL (Fin 2) ℚ) (SLnZ 2 : Set (GL (Fin 2) ℚ)) (SLnZ 2) := by
    rw [← HeckeCoset.toSet_eq_doubleCoset_rep]
    exact trG_mem_toSet D hγ
  rw [← multiplicity_doubleCoset_congr (Γ₁ := SLnZ 2) (Γ₂ := SLnZ 2) (Γ₃ := SLnZ 2)
    (D₂.rep : GL (Fin 2) ℚ) (D₁.rep : GL (Fin 2) ℚ) hd, multiplicity_eq_card_filter,
    HeckeCoset.toSet_eq_doubleCoset_rep]

/-- **Milne, Example 5.32.** $H(\Gamma(1), \Delta)$ is the free abelian group on the double cosets
$T(a, d) = \Gamma(1)\begin{pmatrix} a & 0 \\ 0 & d\end{pmatrix}\Gamma(1)$, $a \mid d$, $a \ge 1$: a $\mathbb Z$-basis
indexed by the positive divisibility chains $(a, d)$ (`HeckeRing.GLn.CanonicalDiagonal 2`), from Tau Ceti's
classification of double cosets `HeckeRing.GLn.diagCoset_bijective`. -/
@[kb "milne2017mf" "Section 5, Example 5.32 (pdf p. 82)"]
noncomputable def heckeBasis : Module.Basis (CanonicalDiagonal 2) ℤ (IntegralHeckeRing 2) :=
  (Finsupp.basisSingleOne).reindex diagCosetEquiv.symm

@[kb "milne2017mf" "Section 5, Example 5.32 (pdf p. 82)"]
theorem heckeBasis_apply (a : CanonicalDiagonal 2) : heckeBasis a = heckeTDiag (a.1 0) (a.1 1) := by
  obtain ⟨a, hpos, hchain⟩ := a
  have h0 : 0 < a 0 := hpos 0
  have h1 : 0 < a 1 := hpos 1
  have hd : a 0 ∣ a 1 := hchain (by decide : (0 : Fin 2) ≤ 1)
  have hv : a = ![a 0, a 1] := by
    funext i
    fin_cases i <;> rfl
  rw [heckeTDiag_eq_diagElem h0 h1 hd, ← hv, diagElem_def]
  unfold heckeBasis HeckeCosetModule.single
  exact (Module.Basis.reindex_apply (Finsupp.basisSingleOne (R := ℤ)) diagCosetEquiv.symm _).trans
    (by simp)

/-- Milne, p. 82: $T(p) = T(1, p)$ for $p$ prime (Tau Ceti's `HeckeRing.GL2.heckeT_prime`). -/
@[kb "milne2017mf" "Section 5, T(p) = T(1, p) (pdf p. 82)"]
theorem heckeT_prime_eq {p : ℕ} (hp : p.Prime) : heckeT p = heckeTDiag 1 p := heckeT_prime p hp

/-- Milne, p. 82: $T(n) = \sum T(a, d)$ over $a \mid d$, $ad = n$, $a \ge 1$. -/
@[kb "milne2017mf" "Section 5, T(n) as a sum of T(a, d) (pdf p. 82)"]
theorem heckeT_eq_sum (n : ℕ) :
    heckeT n = ∑ ad ∈ n.divisorsAntidiagonal.filter (fun ad ↦ ad.1 ∣ ad.2), heckeTDiag ad.1 ad.2 := by
  rw [heckeT_def]
  rw [Finset.sum_filter, Nat.sum_divisorsAntidiagonal (fun a d ↦ if a ∣ d then heckeTDiag a d else 0)]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  split_ifs with h
  · rfl
  · exact heckeTDiag_eq_zero fun ⟨_, _, h'⟩ ↦ h h'

/-- Helper: the prime-power recurrence in the form of relation (8). -/
theorem heckeT_prime_mul_prime_pow_aux {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 1 ≤ n) :
    heckeT p * heckeT (p ^ n) = heckeT (p ^ (n + 1)) + (p : ℤ) • (heckeTScalar p * heckeT (p ^ (n - 1))) := by
  have h := heckeT_prime_pow_recurrence p hp n (by omega)
  rw [h]
  abel

/-- **Milne, relation (8)** (p. 82): in $H(\Gamma(1), \Delta)$,
$T(n)T(m) = \sum_{d \mid \gcd(m, n)} d\,T(d, d)\,T(nm/d^2)$ for $m, n \ge 1$. -/
@[kb "milne2017mf" "Section 5, relation (8) (pdf p. 82)"]
theorem heckeT_mul_heckeT {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    heckeT n * heckeT m = ∑ d ∈ (Nat.gcd m n).divisors, (d : ℤ) • (heckeTScalar d * heckeT (n * m / d ^ 2)) := by
  let _ : CommRing (IntegralHeckeRing 2) :=
    { (inferInstance : Ring (IntegralHeckeRing 2)) with
      mul_comm := HeckeCosetModule.mul_comm_of_antiInvolution ℤ (transposeAntiInvolution 2)
        (transposeAntiInvolution_onHeckeCoset_eq_self 2) }
  have key := Miyake.heckeRecursion_tfae (K := IntegralHeckeRing 2) heckeT heckeTScalar heckeT_one
    heckeTScalar_one (fun m n _ _ ↦ by
      show heckeTScalar (m * n) = heckeTScalar m * heckeTScalar n
      rw [heckeTScalar_def n, heckeTScalar_mul_heckeTDiag]
      rfl)
  have h1 : Miyake.HeckeRecursion (K := IntegralHeckeRing 2) heckeT heckeTScalar := by
    refine ⟨fun m n hm hn hmn ↦ (heckeT_mul_of_coprime m n hmn).symm, fun p e hp he ↦ ?_⟩
    rw [heckeT_prime_mul_prime_pow_aux hp he, zsmul_eq_mul, Int.cast_natCast, mul_assoc]
  have h3 := (key.out 1 3).1 h1
  have := h3 n m hn hm
  rw [this, Nat.gcd_comm]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [zsmul_eq_mul, Int.cast_natCast, mul_assoc]

/-- Relation (8) for coprime $m, n$: $T(n)T(m) = T(nm)$ (Tau Ceti's `HeckeRing.GL2.heckeT_mul_of_coprime`). -/
@[kb "milne2017mf" "Section 5, relation (8), coprime case (pdf p. 82)"]
theorem heckeT_mul_of_coprime' {m n : ℕ} (h : n.Coprime m) : heckeT n * heckeT m = heckeT (n * m) :=
  heckeT_mul_of_coprime n m h

/-- Relation (8) for $p$ prime: $T(p)T(p^n) = T(p^{n+1}) + p\,T(p, p)\,T(p^{n-1})$, $n \ge 1$. -/
@[kb "milne2017mf" "Section 5, relation (8), prime powers (pdf p. 82)"]
theorem heckeRingT_prime_mul_prime_pow {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 1 ≤ n) :
    heckeT p * heckeT (p ^ n) = heckeT (p ^ (n + 1)) + (p : ℤ) • (heckeTScalar p * heckeT (p ^ (n - 1))) := by
  exact heckeT_prime_mul_prime_pow_aux hp hn

end ModularFormsKB.Milne
