import TauCeti.Algebra.CentralSimple.SkolemNoether
import TauCeti.Algebra.CentralSimple.Bimodule
import TauCeti.Algebra.CentralSimple.TensorProduct
import TauCeti.RingTheory.Semisimple.SimpleArtinian
import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
import ModularFormsKB.Miyake.CongruenceModularGroups
import ModularFormsKB.Citation
/-!
# Miyake §5.2–§5.3: Skolem–Noether, Eichler orders of $M_2(\mathbb Q)$ and their unit groups

Miyake, *Modular Forms* (Springer 1989), §5.2–§5.3 and p. 244, pp. 198–213.

* **Theorem 5.2.1** (Skolem–Noether, p. 198) in Miyake's form: $B$ central simple over $F$, $C_1, C_2$
  *simple* (not necessarily central) subalgebras, then every $F$-isomorphism $C_1 \to C_2$ is the
  restriction of an inner automorphism of $B$. Tau Ceti's `TauCeti.skolemNoether` asks the *source*
  to be central (so it does not cover a quadratic subfield of a quaternion algebra, the case Miyake
  uses); we prove the classical form `skolemNoether_of_isCentral` by the same bimodule argument,
  getting simplicity of $C \otimes_F B^{\mathrm{op}}$ from the centrality of $B$ instead
  (Tau Ceti's `IsSimpleRing.tensorProduct_of_isCentral_right`).
* For $B = M_2(\mathbb Q)$ (Miyake p. 244): the order $R = \{\begin{pmatrix}a&b\\c&d\end{pmatrix} \in
  M_2(\mathbb Z) : c \equiv 0 \bmod N\}$ of level $N$ (`eichlerOrder`), the unit group of norm one
  $\Gamma_R = \{\gamma \in R : \det\gamma = 1\}$ (`normOneUnits`), and $\Gamma_R = \Gamma_0(N)$
  (`normOneUnits_eichlerOrder`).
* **Theorem 5.2.13** for $B = M_2(\mathbb Q)$ and orders $R \subseteq M_2(\mathbb Z)$: $\Gamma_R$ is a
  cofinite (= first kind) Fuchsian group (`normOneUnits_isCofinite`), following Miyake's proof
  ($N M_2(\mathbb Z) \subseteq R$ gives $\Gamma(N) \subseteq \Gamma_R \subseteq SL_2(\mathbb Z)$),
  with Tau Ceti's cofiniteness of finite-index subgroups of $SL_2(\mathbb Z)$.
* **Lemma 5.3.2** for $B = M_2(\mathbb Q)$, $S = M_2(\mathbb Z)$:
  $[\Gamma_S : \Gamma_R] = N\prod_{p\mid N}(1 + 1/p)$ (`relIndex_normOneUnits_eichlerOrder`).
-/

open Matrix MatrixGroups CongruenceSubgroup
open scoped TensorProduct MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave2B

/-! ### Skolem–Noether (Theorem 5.2.1) -/

section SkolemNoether

variable (F : Type*) {A B : Type*} [Field F] [Ring A] [Algebra F A] [Ring B] [Algebra F B]

/-- **Skolem–Noether, classical form.** If $A$ is a finite-dimensional central simple $F$-algebra
and $B$ is a simple $F$-algebra, any two $F$-algebra homomorphisms $f, g : B \to A$ are conjugate by
a unit of $A$. -/
theorem skolemNoether_of_isCentral [Algebra.IsCentral F A] [IsSimpleRing A] [FiniteDimensional F A]
    [IsSimpleRing B] (f g : B →ₐ[F] A) :
    ∃ u : Aˣ, ∀ x : B, g x = (u : A) * f x * (↑u⁻¹ : A) := by
  have hf : Function.Injective f := f.toRingHom.injective
  have : FiniteDimensional F B := FiniteDimensional.of_injective f.toLinearMap hf
  have : FiniteDimensional F Aᵐᵒᵖ := Module.Finite.equiv (MulOpposite.opLinearEquiv F)
  have hrank : Module.finrank F (TauCeti.Bimodule f) = Module.finrank F (TauCeti.Bimodule g) :=
    ((TauCeti.Bimodule.of f).symm.trans (TauCeti.Bimodule.of g)).finrank_eq
  obtain ⟨φ⟩ := IsSimpleRing.nonempty_linearEquiv_of_finrank_eq (R := B ⊗[F] Aᵐᵒᵖ) F hrank
  set ψ : TauCeti.Bimodule f →ₗ[B ⊗[F] Aᵐᵒᵖ] TauCeti.Bimodule g := φ.toLinearMap with hψ
  have hψsurj : Function.Surjective ψ := by rw [hψ]; simpa using φ.surjective
  obtain ⟨v, huv⟩ := TauCeti.Bimodule.exists_symm_apply_one_mul_eq_one ψ (hψsurj _)
  have : IsArtinianRing A := IsArtinianRing.of_finite F A
  set u : A := (TauCeti.Bimodule.of g).symm (ψ (TauCeti.Bimodule.of f 1))
  have hUval : ((Units.mkOfMulEqOne u v huv : Aˣ) : A) = u := Units.val_mkOfMulEqOne huv
  have hUinv : (↑(Units.mkOfMulEqOne u v huv)⁻¹ : A) = v :=
    Units.inv_eq_of_mul_eq_one_right (by rw [hUval]; exact huv)
  have hb : ∀ b : B, u * f b = g b * u :=
    TauCeti.Bimodule.symm_apply_one_mul_eq_mul_symm_apply_one ψ
  refine ⟨Units.mkOfMulEqOne u v huv, fun x ↦ ?_⟩
  rw [hUval, hUinv, hb x, mul_assoc, huv, mul_one]

/-- **Miyake, Theorem 5.2.1 (Skolem–Noether).** Let $B$ be a (finite-dimensional) central simple
algebra over a field $F$ and $C_1, C_2$ simple $F$-subalgebras of $B$. Every $F$-isomorphism
$\sigma : C_1 \to C_2$ is the restriction of an inner automorphism of $B$:
$\sigma(x) = u x u^{-1}$ for some $u \in B^\times$. -/
@[kb "miyake1989" "Theorem 5.2.1, p. 198"]
theorem skolemNoether_subalgebra [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B]
    (C₁ C₂ : Subalgebra F B) [IsSimpleRing C₁] (σ : C₁ ≃ₐ[F] C₂) :
    ∃ u : Bˣ, ∀ x : C₁, ((σ x : C₂) : B) = (u : B) * (x : B) * (↑u⁻¹ : B) :=
  skolemNoether_of_isCentral F C₁.val (C₂.val.comp σ.toAlgHom)

/-- **Miyake, Theorem 5.2.1, last assertion.** Every $F$-automorphism of a central simple algebra
is inner (Tau Ceti `TauCeti.exists_unit_conj_of_algEquiv`). -/
@[kb "miyake1989" "Theorem 5.2.1, p. 198"]
theorem algEquiv_inner [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B]
    (e : B ≃ₐ[F] B) : ∃ u : Bˣ, ∀ x : B, e x = (u : B) * x * (↑u⁻¹ : B) :=
  TauCeti.exists_unit_conj_of_algEquiv F e

end SkolemNoether

/-! ### Orders of $M_2(\mathbb Q)$ inside $M_2(\mathbb Z)$ and their unit groups of norm one -/

/-- For $\gamma \in SL_2(\mathbb Z)$, $\gamma^{-1} = (\operatorname{tr}\gamma)\cdot 1 - \gamma$. -/
lemma coe_inv_eq_trace_sub (γ : SL(2, ℤ)) :
    ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      ((γ 0 0 + γ 1 1 : ℤ) : Matrix (Fin 2) (Fin 2) ℤ) - (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.intCast_apply]

/-- **The unit group of norm one** $\Gamma_R = \{\gamma \in R : \det \gamma = 1\}$ of a subring
$R \subseteq M_2(\mathbb Z)$ (Miyake (5.2.11); for $B = M_2(\mathbb Q)$ the reduced norm is the
determinant), as a subgroup of $SL_2(\mathbb Z)$. Inverses stay in $R$ because
$\gamma^{-1} = (\operatorname{tr}\gamma) - \gamma$. -/
@[kb "miyake1989" "(5.2.11), p. 209"]
def normOneUnits (R : Subring (Matrix (Fin 2) (Fin 2) ℤ)) : Subgroup SL(2, ℤ) where
  carrier := {γ | (γ : Matrix (Fin 2) (Fin 2) ℤ) ∈ R}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by simpa using R.mul_mem ha hb
  inv_mem' {γ} hγ := by
    simp only [Set.mem_ofPred_eq, coe_inv_eq_trace_sub] at hγ ⊢
    exact R.sub_mem (intCast_mem R _) hγ

@[simp] lemma mem_normOneUnits {R : Subring (Matrix (Fin 2) (Fin 2) ℤ)} {γ : SL(2, ℤ)} :
    γ ∈ normOneUnits R ↔ (γ : Matrix (Fin 2) (Fin 2) ℤ) ∈ R := Iff.rfl

/-- **The order of level $N$ in $M_2(\mathbb Q)$** (Miyake p. 244):
$R = \{\begin{pmatrix}a&b\\c&d\end{pmatrix} \in M_2(\mathbb Z) : c \equiv 0 \bmod N\}$. -/
@[kb "miyake1989" "§6.5, p. 244 (B = M2(Q))"]
def eichlerOrder (N : ℕ) : Subring (Matrix (Fin 2) (Fin 2) ℤ) where
  carrier := {A | (N : ℤ) ∣ A 1 0}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Matrix.mul_apply, Fin.sum_univ_two] at ha hb ⊢
    exact dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hb _)
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Matrix.add_apply] at ha hb ⊢
    exact dvd_add ha hb
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, Matrix.neg_apply] at ha ⊢
    exact (dvd_neg).mpr ha

/-- **Miyake p. 244.** For the order $R$ of level $N$ in $M_2(\mathbb Q)$, $\Gamma_R = \Gamma_0(N)$. -/
@[kb "miyake1989" "§6.5, p. 244 (B = M2(Q))"]
theorem normOneUnits_eichlerOrder (N : ℕ) : normOneUnits (eichlerOrder N) = Gamma0 N := by
  ext γ
  rw [mem_normOneUnits, Gamma0_mem]
  change (N : ℤ) ∣ γ 1 0 ↔ _
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm

/-- If $N M_2(\mathbb Z) \subseteq R$ then $\Gamma(N) \subseteq \Gamma_R$. -/
lemma Gamma_le_normOneUnits {R : Subring (Matrix (Fin 2) (Fin 2) ℤ)} {N : ℕ}
    (hN : ∀ X : Matrix (Fin 2) (Fin 2) ℤ, (N : ℤ) • X ∈ R) : Gamma N ≤ normOneUnits R := by
  intro γ hγ
  obtain ⟨h00, h01, h10, h11⟩ := Gamma_mem.mp hγ
  have hent : ∀ i j, (N : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    intro i j
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  choose X hX using hent
  have hγX : (γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 + (N : ℤ) • Matrix.of X := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← hX i j]; ring
  rw [mem_normOneUnits, hγX]
  exact R.add_mem R.one_mem (hN _)

/-- **Miyake, Theorem 5.2.13, for $B = M_2(\mathbb Q)$.** For an order $R \subseteq M_2(\mathbb Z)$
of $M_2(\mathbb Q)$ (a subring of finite additive index), the unit group of norm one $\Gamma_R$ is a
Fuchsian group of the first kind: its image in $PSL_2(\mathbb R)$ is discrete of finite covolume
(Tau Ceti's `Subgroup.IsCofinite`). -/
@[kb "miyake1989" "Theorem 5.2.13, p. 209 (B = M2(Q), R ⊆ M2(Z))"]
theorem normOneUnits_isCofinite (R : Subring (Matrix (Fin 2) (Fin 2) ℤ))
    [hR : R.toAddSubgroup.FiniteIndex] :
    ((normOneUnits R).map sl2zToPSL2R).IsCofinite := by
  set N := R.toAddSubgroup.index with hNdef
  have hN0 : N ≠ 0 := hR.index_ne_zero
  have : NeZero N := ⟨hN0⟩
  have hN : ∀ X : Matrix (Fin 2) (Fin 2) ℤ, (N : ℤ) • X ∈ R := by
    intro X
    have := AddSubgroup.nsmul_index_mem R.toAddSubgroup X
    rw [natCast_zsmul]
    exact this
  have hle := Gamma_le_normOneUnits hN
  have : (normOneUnits R).FiniteIndex := Subgroup.finiteIndex_of_le hle
  exact Subgroup.isCofinite_map_sl2zToPSL2R (normOneUnits R)

/-- $\Gamma_0(N)$, the unit group of norm one of the order of level $N$, is a Fuchsian group of
the first kind (Theorem 5.2.13 for $B = M_2(\mathbb Q)$). -/
@[kb "miyake1989" "Theorem 5.2.13, p. 209 (B = M2(Q))"]
theorem normOneUnits_eichlerOrder_isCofinite (N : ℕ) [NeZero N] :
    ((normOneUnits (eichlerOrder N)).map sl2zToPSL2R).IsCofinite := by
  rw [normOneUnits_eichlerOrder]
  exact Subgroup.isCofinite_map_sl2zToPSL2R (Gamma0 N)

/-- **Miyake, Lemma 5.3.2, for $B = M_2(\mathbb Q)$.** With $S = M_2(\mathbb Z)$ the maximal order
containing the order $R$ of level $N$, $[\Gamma_S : \Gamma_R] = N\prod_{p \mid N}(1 + 1/p)$. -/
@[kb "miyake1989" "Lemma 5.3.2, p. 212 (B = M2(Q))"]
theorem relIndex_normOneUnits_eichlerOrder (N : ℕ) [NeZero N] :
    (((normOneUnits (eichlerOrder N)).relIndex (normOneUnits ⊤) : ℕ) : ℚ) =
      N * ∏ p ∈ N.primeFactors, (1 + 1 / (p : ℚ)) := by
  have htop : normOneUnits (⊤ : Subring (Matrix (Fin 2) (Fin 2) ℤ)) = ⊤ := by
    ext γ; simp
  rw [htop, Subgroup.relIndex_top_right, normOneUnits_eichlerOrder]
  exact ModularFormsKB.Miyake.index_Gamma0 N

end ModularFormsKB.Miyake.Wave2B
