import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.CoefficientFormula
import TauCeti.NumberTheory.ModularForms.TrivialNebentypus
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import ModularFormsKB.Citation
/-!
# Milne, Chapter 5: the Hecke operators $T(n)$ on $M_{2k}(\Gamma(1))$

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf pp. 73–75.

Milne's operator $T(n)$ on modular forms of weight $2k$ for $\Gamma(1) = \mathrm{SL}_2(\mathbb Z)$ is the classical
Hecke operator. It exists in Tau Ceti as the action of the Hecke-ring element
`HeckeRing.GL2.heckeTCompositeGamma0 1 n` on the nebentypus space `modFormCharSpace (N := 1) w 1`
(`HeckeRing.GL2.heckeRingHomCharSpace`); at level one the nebentypus space is the whole space of modular forms for
$\Gamma_1(1)$, which is $\mathrm{SL}_2(\mathbb Z)$ (`TauCeti.Gamma1_one_map_eq_SL`). This file transports that
operator to Mathlib's `ModularForm 𝒮ℒ w` and `CuspForm 𝒮ℒ w` (`heckeT`, `heckeTCusp`); it introduces no new
operator.

**Weight and normalization.** Mathlib's weight `w` is Milne's $2k$. Tau Ceti's $T_n$ carries no extra factor: its
$q$-expansion is $a_m(T_n f) = \sum_{d \mid (m,n)} d^{w-1} a_{mn/d^2}(f)$, which is Milne's formula of
Proposition 5.16(b) with $w = 2k$. Milne's factor $n^{2k-1}$ is absorbed by Mathlib's slash action, whose factor
$\det(\alpha)^{w-1}$ for $\alpha = \begin{pmatrix} a & b \\ 0 & d\end{pmatrix}$ gives
$f \mid_w \alpha\,(z) = n^{2k-1}d^{-2k}f\big(\frac{az+b}{d}\big)$.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2
open scoped MatrixGroups ModularForm
open TauCeti (modFormCharSpace cuspFormCharSpace diamondOp_one diamondOpCusp_one)

namespace ModularFormsKB.Milne

variable (w : ℤ)

/-- At level one every modular form for $\Gamma_1(1)$ has trivial nebentypus: $(\mathbb Z/1)^\times$ is trivial. -/
theorem mem_modFormCharSpace_levelOne (f : ModularForm ((Gamma1 1).map (mapGL ℝ)) w) :
    f ∈ modFormCharSpace (N := 1) w 1 := by
  rw [TauCeti.mem_modFormCharSpace_one_iff_diamondOp]
  intro d
  rw [Subsingleton.elim d 1, diamondOp_one]
  rfl

/-- The cusp-form version of `mem_modFormCharSpace_levelOne`. -/
theorem mem_cuspFormCharSpace_levelOne (f : CuspForm ((Gamma1 1).map (mapGL ℝ)) w) :
    f ∈ cuspFormCharSpace (N := 1) w 1 := by
  rw [TauCeti.mem_cuspFormCharSpace_one_iff_diamondOpCusp]
  intro d
  rw [Subsingleton.elim d 1, diamondOpCusp_one]
  rfl

/-- The level-one nebentypus space of Tau Ceti is Mathlib's space `ModularForm 𝒮ℒ w`; the equivalence does not
change the underlying function (`coe_levelOneEquiv`). -/
noncomputable def levelOneEquiv : modFormCharSpace (N := 1) w 1 ≃ₗ[ℂ] ModularForm 𝒮ℒ w where
  toFun f := ModularForm.mcast rfl (f : ModularForm ((Gamma1 1).map (mapGL ℝ)) w)
    TauCeti.Gamma1_one_map_eq_SL.symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨ModularForm.mcast rfl f TauCeti.Gamma1_one_map_eq_SL, mem_modFormCharSpace_levelOne w _⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_levelOneEquiv (f : modFormCharSpace (N := 1) w 1) :
    ⇑(levelOneEquiv w f) = ⇑(f : ModularForm ((Gamma1 1).map (mapGL ℝ)) w) := rfl

@[simp]
theorem coe_levelOneEquiv_symm (f : ModularForm 𝒮ℒ w) :
    ⇑((levelOneEquiv w).symm f : ModularForm ((Gamma1 1).map (mapGL ℝ)) w) = ⇑f := rfl

/-- The cusp-form version of `levelOneEquiv`. -/
noncomputable def levelOneCuspEquiv : cuspFormCharSpace (N := 1) w 1 ≃ₗ[ℂ] CuspForm 𝒮ℒ w where
  toFun f := CuspForm.mcast rfl (f : CuspForm ((Gamma1 1).map (mapGL ℝ)) w)
    TauCeti.Gamma1_one_map_eq_SL.symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨CuspForm.mcast rfl f TauCeti.Gamma1_one_map_eq_SL, mem_cuspFormCharSpace_levelOne w _⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_levelOneCuspEquiv (f : cuspFormCharSpace (N := 1) w 1) :
    ⇑(levelOneCuspEquiv w f) = ⇑(f : CuspForm ((Gamma1 1).map (mapGL ℝ)) w) := rfl

@[simp]
theorem coe_levelOneCuspEquiv_symm (f : CuspForm 𝒮ℒ w) :
    ⇑((levelOneCuspEquiv w).symm f : CuspForm ((Gamma1 1).map (mapGL ℝ)) w) = ⇑f := rfl

/-- **Milne's Hecke operator $T(n)$ on $M_w(\Gamma(1))$** ($w = 2k$): Tau Ceti's classical $T_n$
(`heckeTCompositeGamma0 1 n` acting through `heckeRingHomCharSpace`), transported to `ModularForm 𝒮ℒ w`.
Milne's defining formula $T(n)f(z) = n^{2k-1}\sum d^{-2k} f\big(\frac{az+b}{d}\big)$ is `heckeT_apply`. -/
@[kb "milne2017mf" "Section 5, the operators T(n) on M_k(Gamma(1)) (pdf pp. 68, 73)"]
noncomputable def heckeT (n : ℕ) : Module.End ℂ (ModularForm 𝒮ℒ w) :=
  (levelOneEquiv w).conj (heckeRingHomCharSpace (N := 1) w 1 (heckeTCompositeGamma0 1 n))

/-- Milne's $T(n)$ on cusp forms $S_w(\Gamma(1))$, transported in the same way. -/
@[kb "milne2017mf" "Section 5, the operators T(n) on S_k(Gamma(1)) (pdf p. 74)"]
noncomputable def heckeTCusp (n : ℕ) : Module.End ℂ (CuspForm 𝒮ℒ w) :=
  (levelOneCuspEquiv w).conj (heckeRingHomCuspCharSpace (N := 1) w 1 (heckeTCompositeGamma0 1 n))

theorem heckeT_apply_eq (n : ℕ) (f : ModularForm 𝒮ℒ w) :
    heckeT w n f = levelOneEquiv w
      (heckeRingHomCharSpace (N := 1) w 1 (heckeTCompositeGamma0 1 n) ((levelOneEquiv w).symm f)) := rfl

theorem heckeTCusp_apply_eq (n : ℕ) (f : CuspForm 𝒮ℒ w) :
    heckeTCusp w n f = levelOneCuspEquiv w
      (heckeRingHomCuspCharSpace (N := 1) w 1 (heckeTCompositeGamma0 1 n)
        ((levelOneCuspEquiv w).symm f)) := rfl

end ModularFormsKB.Milne
