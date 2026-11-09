import TauCeti.Analysis.Complex.ModularForms.LevelOne.JInputs
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Meromorphic
import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import ModularFormsKB.Citation
/-!
# Milne, Chapter 6: the modular equation for $\Gamma_0(N)$ (Theorem 6.1, Example 6.2)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 6, pdf pp. 87–90.

## Setting

$X_0(N) = \Gamma_0(N)\backslash\mathbb H^*$ is Tau Ceti's compactified quotient `X0 N` of the image of $\Gamma_0(N)$ in
$\mathrm{PSL}_2(\mathbb R)$, a compact connected Riemann surface, and $\mathbb C(X_0(N))$, the field of modular functions
for $\Gamma_0(N)$, is Tau Ceti's field `TauCeti.RiemannSurface.MeromorphicFunction (X0 N)` of meromorphic functions on it
(a modular function for $\Gamma$ is a meromorphic function on $X(\Gamma)$; the comparison with Milne's definition by
$q$-expansions at the cusps is the chapter 4 job's `isModularFunction_iff_compactifiedQuotient`). The function
$j$ is Tau Ceti's `TauCeti.ModularForm.j` $= E_4^3/\Delta$.

## Items

- Running text: $\Gamma_0(N) = \Gamma(1) \cap \alpha^{-1}\Gamma(1)\alpha$ for $\alpha = \operatorname{diag}(N, 1)$
  (`mem_Gamma0_iff_conj`), and $\psi = (\Gamma(1) : \Gamma_0(N)) = N\prod_{p \mid N}(1 + 1/p)$ (`index_Gamma0_eq`, from
  Tau Ceti's `CongruenceSubgroup.Gamma0_index_mul_prod_primeFactors`).
- First step of the proof of Theorem 6.1: $j(Nz)$ is invariant under $\Gamma_0(N)$ (`j_scale_smul`).
- **Theorem 6.1** (named statement): `ModularEquation`; the property of the polynomial is `IsModularPolynomial`.
- **Example 6.2** (named statement): `ModularEquationLevelTwo`, the explicit polynomial `modularPolynomialTwo`.
-/

open UpperHalfPlane CongruenceSubgroup Matrix
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne

/-- $X_0(N) = \Gamma_0(N)\backslash\mathbb H^*$ as a compact Riemann surface (Tau Ceti's compactified quotient). -/
abbrev X0 (N : ℕ) : Type :=
  ((Gamma0 N).map sl2zToPSL2R).CompactifiedQuotient

/-- $X_0(N)$ is connected (Tau Ceti proves it preconnected; it is nonempty). -/
instance (N : ℕ) : ConnectedSpace (X0 N) where
  toNonempty := ⟨Subgroup.CompactifiedQuotient.ofQuotient (Quotient.mk _ ⟨Complex.I, by simp⟩)⟩

/-- The point $Nz$ of $\mathbb H$, $N \ge 1$. -/
def scaleH (N : ℕ) (hN : 0 < N) (z : ℍ) : ℍ :=
  ⟨(N : ℂ) * z, by simpa using mul_pos (Nat.cast_pos.2 hN : (0 : ℝ) < N) z.im_pos⟩

lemma exists_delta_of_mem_Gamma0 {N : ℕ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    ∃ δ : SL(2, ℤ), δ 0 0 = γ 0 0 ∧ δ 0 1 = N * γ 0 1 ∧ (N : ℤ) * δ 1 0 = γ 1 0 ∧ δ 1 1 = γ 1 1 := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
  obtain ⟨c, hc⟩ := hγ
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  refine ⟨⟨!![γ 0 0, N * γ 0 1; c, γ 1 1], ?_⟩, rfl, rfl, ?_, rfl⟩
  · rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hc] at hdet
    linear_combination hdet
  · simpa using hc.symm

lemma conj_eq {N : ℕ} (hN : 0 < N) (γ : SL(2, ℤ)) :
    !![(N : ℚ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) * !![(N : ℚ)⁻¹, 0; 0, 1] =
      !![(γ 0 0 : ℚ), N * (γ 0 1 : ℚ); (γ 1 0 : ℚ) * (N : ℚ)⁻¹, (γ 1 1 : ℚ)] := by
  rw [Matrix.eta_fin_two ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ))]
  have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  simp
  field_simp

/-- **$\Gamma_0(N) = \Gamma(1) \cap \alpha^{-1}\Gamma(1)\alpha$**, $\alpha = \begin{pmatrix}N&0\\0&1\end{pmatrix}$
(Milne, Section 6, pdf p. 87): $\gamma \in \mathrm{SL}_2(\mathbb Z)$ lies in $\Gamma_0(N)$ iff $\alpha\gamma\alpha^{-1}$
has integer entries (it is then in $\mathrm{SL}_2(\mathbb Z)$). -/
@[kb "milne2017mf" "Section 6, Γ0(N) = Γ(1) ∩ α⁻¹Γ(1)α (pdf p. 87)"]
theorem mem_Gamma0_iff_conj {N : ℕ} (hN : 0 < N) (γ : SL(2, ℤ)) :
    γ ∈ Gamma0 N ↔ ∃ δ : SL(2, ℤ), ((δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) =
      !![(N : ℚ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) * !![(N : ℚ)⁻¹, 0; 0, 1] := by
  have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  constructor
  · intro hγ
    obtain ⟨δ, h00, h01, h10, h11⟩ := exists_delta_of_mem_Gamma0 γ hγ
    refine ⟨δ, ?_⟩
    have h10q : (N : ℚ) * (δ 1 0 : ℚ) = (γ 1 0 : ℚ) := by exact_mod_cast h10
    have h01q : (δ 0 1 : ℚ) = N * (γ 0 1 : ℚ) := by exact_mod_cast h01
    rw [conj_eq hN]
    have h10q' : (δ 1 0 : ℚ) = (γ 1 0 : ℚ) * (N : ℚ)⁻¹ := by
      rw [← h10q]; field_simp
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11, h01q, h10q']
  · rintro ⟨δ, h⟩
    rw [conj_eq hN] at h
    have h10 := congrFun (congrFun h 1) 0
    simp at h10
    have : (γ 1 0 : ℚ) = N * (δ 1 0 : ℚ) := by
      rw [h10]; field_simp
    have h' : γ 1 0 = N * δ 1 0 := by exact_mod_cast this
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨_, h'⟩

/-- **The index** $\psi = (\Gamma(1) : \Gamma_0(N)) = N \prod_{p \mid N}(1 + 1/p)$ (Milne, Section 6, pdf p. 87). -/
@[kb "milne2017mf" "Section 6, ψ = (Γ(1) : Γ0(N)) = N ∏ (1 + 1/p) (pdf p. 87)"]
theorem index_Gamma0_eq {N : ℕ} (hN : 0 < N) :
    ((Gamma0 N).index : ℚ) = N * ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℚ)) := by
  have h := Gamma0_index_mul_prod_primeFactors (N := N)
  have hq : ((Gamma0 N).index : ℚ) * ∏ p ∈ N.primeFactors, (p : ℚ) =
      N * ∏ p ∈ N.primeFactors, ((p : ℚ) + 1) := by
    have := congrArg (Nat.cast : ℕ → ℚ) h
    push_cast at this
    exact this
  have hp : ∏ p ∈ N.primeFactors, (p : ℚ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp => Nat.cast_ne_zero.2 (Nat.prime_of_mem_primeFactors hp).ne_zero
  have e : ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℚ)) =
      (∏ p ∈ N.primeFactors, ((p : ℚ) + 1)) / ∏ p ∈ N.primeFactors, (p : ℚ) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.prime_of_mem_primeFactors hp).ne_zero
    field_simp
  rw [e, mul_div_assoc', eq_div_iff hp, hq]

/-- **$j(Nz)$ is a modular function for $\Gamma_0(N)$** (Milne, proof of Theorem 6.1, pdf p. 88, first step):
$j(N\gamma z) = j(Nz)$ for $\gamma \in \Gamma_0(N)$, because
$\begin{pmatrix}a & Nb\\ c/N & d\end{pmatrix} \in \Gamma(1)$. -/
@[kb "milne2017mf" "Section 6, proof of Theorem 6.1: j(Nz) is invariant under Γ0(N) (pdf p. 88)"]
theorem j_scale_smul {N : ℕ} (hN : 0 < N) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) (z : ℍ) :
    TauCeti.ModularForm.j (scaleH N hN (γ • z)) = TauCeti.ModularForm.j (scaleH N hN z) := by
  obtain ⟨δ, h00, h01, h10, h11⟩ := exists_delta_of_mem_Gamma0 γ hγ
  have hNq : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have key : (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) δ) • scaleH N hN z =
      scaleH N hN (γ • z) := by
    have h10r : (N : ℝ) * (δ 1 0 : ℝ) = (γ 1 0 : ℝ) := by exact_mod_cast h10
    have h01r : (δ 0 1 : ℝ) = N * (γ 0 1 : ℝ) := by exact_mod_cast h01
    apply UpperHalfPlane.ext
    rw [coe_specialLinearGroup_apply]
    show _ = (N : ℂ) * ((γ • z : ℍ) : ℂ)
    rw [coe_specialLinearGroup_apply γ z]
    dsimp only [scaleH]
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      eq_intCast, Int.coe_castRingHom, h00, h11, h01r, algebraMap_int_eq]
    have hz : ((γ 1 0 : ℝ) : ℂ) * (z : ℂ) + ((γ 1 1 : ℤ) : ℝ) ≠ 0 := by
      have := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) z
      exact this
    have hd : ((δ 1 0 : ℝ) : ℂ) * ((N : ℂ) * z) + ((γ 1 1 : ℤ) : ℝ) ≠ 0 := by
      have e : ((δ 1 0 : ℝ) : ℂ) * ((N : ℂ) * z) = ((γ 1 0 : ℝ) : ℂ) * z := by
        rw [← h10r]; push_cast; ring
      rw [e]; exact hz
    have e : ((δ 1 0 : ℝ) : ℂ) * ((N : ℂ) * z) = ((γ 1 0 : ℝ) : ℂ) * z := by
      rw [← h10r]; push_cast; ring
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [e]
    push_cast
    field_simp
  rw [← key]
  exact TauCeti.ModularForm.j_smul δ _

/-- The polynomial $F(X, Y) \in \mathbb Z[X, Y]$ (variables `X 0`, `X 1`) is **the modular polynomial of level $N$**
relative to meromorphic functions $j, j_N$ on $X_0(N)$: $F(j, Y) \in \mathbb C(j)[Y]$ is the minimum polynomial of $j_N$
over $\mathbb C(j)$. -/
def IsModularPolynomial (N : ℕ) (jX jNX : TauCeti.RiemannSurface.MeromorphicFunction (X0 N))
    (F : MvPolynomial (Fin 2) ℤ) : Prop :=
  (minpoly (IntermediateField.adjoin ℂ {jX}) jNX).map (algebraMap _ _) =
    MvPolynomial.eval₂ (Int.castRingHom _) ![Polynomial.C jX, Polynomial.X] F

/-- The function $j$ on $X_0(N)$: the meromorphic function whose value at the class of $z \in \mathbb H$ is $j(z)$. -/
def IsJOnX0 (N : ℕ) (jX : TauCeti.RiemannSurface.MeromorphicFunction (X0 N)) : Prop :=
  ∀ z : ℍ, jX (Subgroup.CompactifiedQuotient.ofQuotient (Quotient.mk _ z)) = (TauCeti.ModularForm.j z : ℂ)

/-- The function $j_N(z) = j(Nz)$ on $X_0(N)$. -/
def IsJNOnX0 (N : ℕ) (hN : 0 < N) (jNX : TauCeti.RiemannSurface.MeromorphicFunction (X0 N)) : Prop :=
  ∀ z : ℍ, jNX (Subgroup.CompactifiedQuotient.ofQuotient (Quotient.mk _ z)) =
    (TauCeti.ModularForm.j (scaleH N hN z) : ℂ)

/-- **Milne, Theorem 6.1** (named statement; Kronecker's modular equation). The functions $j(z)$ and $j(Nz)$ are
meromorphic functions on $X_0(N)$, and:
- the field $\mathbb C(X_0(N))$ of modular functions for $\Gamma_0(N)$ is generated over $\mathbb C$ by $j(z)$ and
  $j(Nz)$;
- the minimum polynomial of $j(Nz)$ over $\mathbb C(j)$ has degree $\psi = (\Gamma(1) : \Gamma_0(N))$;
- it is $F(j, Y)$ for a polynomial $F(X, Y) \in \mathbb Z[X, Y]$;
- when $N > 1$, $F(X, Y)$ is symmetric in $X$ and $Y$;
- when $N = p$ is prime, $F(X, Y) \equiv X^{p+1} + Y^{p+1} - X^pY^p - XY \pmod p$. -/
@[kb "milne2017mf" "Section 6, Theorem 6.1 (pdf p. 88)"]
structure ModularEquation (N : ℕ) (hN : 0 < N) : Prop where
  statement : ∃ jX jNX : TauCeti.RiemannSurface.MeromorphicFunction (X0 N), IsJOnX0 N jX ∧ IsJNOnX0 N hN jNX ∧
    IntermediateField.adjoin ℂ {jX, jNX} = ⊤ ∧
    (minpoly (IntermediateField.adjoin ℂ {jX}) jNX).natDegree = (Gamma0 N).index ∧
    ∃ F : MvPolynomial (Fin 2) ℤ, IsModularPolynomial N jX jNX F ∧
      (1 < N → MvPolynomial.rename (Equiv.swap 0 1) F = F) ∧
      (N.Prime → MvPolynomial.map (Int.castRingHom (ZMod N)) F =
        MvPolynomial.X 0 ^ (N + 1) + MvPolynomial.X 1 ^ (N + 1) -
          MvPolynomial.X 0 ^ N * MvPolynomial.X 1 ^ N - MvPolynomial.X 0 * MvPolynomial.X 1)

/-- The level-2 modular polynomial of Example 6.2:
$X^3 + Y^3 - X^2Y^2 + 1488XY(X+Y) - 162000(X^2+Y^2) + 40773375XY + 8748000000(X+Y) - 157464000000000$. -/
def modularPolynomialTwo : MvPolynomial (Fin 2) ℤ :=
  let X := MvPolynomial.X (R := ℤ) (0 : Fin 2)
  let Y := MvPolynomial.X (R := ℤ) (1 : Fin 2)
  X ^ 3 + Y ^ 3 - X ^ 2 * Y ^ 2 + 1488 * X * Y * (X + Y) - 162000 * (X ^ 2 + Y ^ 2) + 40773375 * X * Y +
    8748000000 * (X + Y) - 157464000000000

/-- **Milne, Example 6.2** (named statement): for $N = 2$ the modular equation is `modularPolynomialTwo`: for the
functions $j(z)$, $j(2z)$ on $X_0(2)$, the minimum polynomial of $j(2z)$ over $\mathbb C(j)$ is
$F_2(j, Y)$ with $F_2 = $ `modularPolynomialTwo`. -/
@[kb "milne2017mf" "Section 6, Example 6.2 (pdf p. 90)"]
structure ModularEquationLevelTwo : Prop where
  statement : ∀ jX jNX : TauCeti.RiemannSurface.MeromorphicFunction (X0 2), IsJOnX0 2 jX →
    IsJNOnX0 2 (by norm_num) jNX → IsModularPolynomial 2 jX jNX modularPolynomialTwo

end ModularFormsKB.Milne
