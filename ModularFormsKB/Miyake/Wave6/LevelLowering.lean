import ModularFormsKB.Miyake.Wave6.LevelChange
import TauCeti.NumberTheory.ModularForms.Newforms.Descent.LevelCommute
import TauCeti.NumberTheory.ModularForms.Newforms.Descent.CuspForm
import TauCeti.NumberTheory.ModularForms.Newforms.Descent.LevelRaise.Commute

/-!
# Miyake §4.6: the level-lowering operator `Γ₀(pN) [1 0; 0 p] Γ₀(N)`, Lemma 4.6.6

Miyake, *Modular Forms* (Springer 1989), Lemma 4.6.6, p. 158. Let `χ` be a Dirichlet character
modulo `N`, `l` a positive integer, `p` a prime not dividing `l`, and `M = lN`. The operator
`f ↦ f | Γ₀(pN) [1 0; 0 p] Γ₀(N)` from `𝒢_k(pN, χ)` to `𝒢_k(N, χ)` commutes with
(1) the natural embeddings `𝒢_k(pN, χ) ⊂ 𝒢_k(pM, χ)`, `𝒢_k(N, χ) ⊂ 𝒢_k(M, χ)`, and
(2) the maps `f ↦ f ∣_k δ_l`, `δ_l = [l 0; 0 1]` (that is, `f(z) ↦ f(lz)` up to a constant);
similarly for cusp forms.

## The operator
Following Miyake's proof (Lemma 4.5.11 and (4.6.7)), the double coset
`Γ₀(pN) [1 0; 0 p] Γ₀(N)` is the union of the `Γ₀(pN) [1 v; 0 p]` (`0 ≤ v < p`) and, when
`p ∤ N`, of `Γ₀(pN) [1 0; 0 p] γ_p` with `γ_p ∈ SL₂(ℤ)` congruent to `[0 -1; 1 0]` modulo `p`
and to `1` modulo `N`. Tau Ceti's descent family `TauCeti.descendMatrix p (pN)` is exactly
this list, and `lowerSlash k p N f` is the sum `∑ f ∣_k α_v` over it: Miyake's operator without
his normalizing factor `p^{k/2 - 1}` (Mathlib's slash is normalized by `det^{k-1}`; the
factors are constants and play no role in the commutativity). That the family is a complete set
of representatives of the right cosets in the double coset (Miyake (4.6.7), from Lemma 4.5.11)
is proved in `Wave6/DescentCosets.lean` (`doubleCoset_eq_iUnion_descendMatrixRat`,
`pairwiseDisjoint_descendMatrixRat`).

## Results
* `lowerSlash_mul_left` (Lemma 4.6.6 (1), on functions): for `f` invariant under `Γ₁(pN)`,
  the operator at level `pM → M` equals the one at level `pN → N`. This is Tau Ceti's
  `TauCeti.descendSlash_mul_left_of_coprime`.
* `lowerSlash_embedMod`, `lowerSlash_raiseMod` (modular forms) and `lowerSlash_embed`,
  `lowerSlash_raise` (cusp forms): the two diagrams on Miyake's spaces, with the embeddings
  `embedMod`, `embed` and the maps `f(z) ↦ f(lz)` (`raiseMod`, `raise`) of
  `Wave6/LevelChange.lean`. Diagram (2) is Tau Ceti's
  `TauCeti.descendSlash_coe_levelRaise_mul_left_of_comp_of_mem_modFormCharSpace` (and its cusp
  form version), transported to Miyake's level presentation `pN`.
* `exists_cuspSpace_lowerSlash`: on `𝒮_k(pN, χ)` the operator lands in `𝒮_k(N, χ)` (Tau Ceti's
  `TauCeti.descendCuspForm`); `exists_modSpace_lowerSlash`: on `𝒢_k(pN, χ)` it lands in
  `𝒢_k(N, χ)` (`descendModularForm`, Tau Ceti's construction copied for modular forms).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

noncomputable section

namespace ModularFormsKB.Miyake.Wave6

open Wave4

/-- Miyake's level-lowering operator `f ↦ f | Γ₀(pN) [1 0; 0 p] Γ₀(N)` on functions, without
the factor `p^{k/2-1}`: the slash sum over Miyake's representatives of Lemma 4.5.11 (Tau Ceti's
descent family at level `pN`). -/
def lowerSlash (k : ℤ) (p N : ℕ) [NeZero p] (f : ℍ → ℂ) : ℍ → ℂ :=
  TauCeti.descendSlash k p (p * N) f

/-- **Miyake, Lemma 4.6.6 (1)**, on functions: for a prime `p ∤ l` and `f` invariant under
`Γ₁(pN)`, lowering from `pM` to `M = lN` is lowering from `pN` to `N`. -/
@[kb "miyake1989" "Lemma 4.6.6 (1), p. 158 (on functions)"]
theorem lowerSlash_mul_left (k : ℤ) {p l N : ℕ} [NeZero p] (hp : p.Prime) (hpl : p.Coprime l)
    {f : ℍ → ℂ} (hf : ∀ ε ∈ Gamma1 (p * N), f ∣[k] (mapGL ℝ ε : GL (Fin 2) ℝ) = f) :
    lowerSlash k p (l * N) f = lowerSlash k p N f := by
  unfold lowerSlash
  rw [show p * (l * N) = l * (p * N) by ring]
  exact TauCeti.descendSlash_mul_left_of_coprime k hp (dvd_mul_right p N) hpl hf

/-- A form in `𝒢_k(pN, χ)`, `χ` modulo `N`, transforms trivially under `Γ₀(pN) ∩ Γ₁(N)`. -/
theorem slash_eq_self_of_mem_modSpace (k : ℤ) {p N : ℕ} [NeZero p] [NeZero N]
    (χ : DirichletCharacter ℂ N)
    (f : modSpace (N := p * N) k (DirichletCharacter.changeLevel (dvd_mul_left N p) χ))
    (γ : SL(2, ℤ)) (h0 : γ ∈ Gamma0 (p * N)) (h1 : γ ∈ Gamma1 N) :
    ⇑f.1 ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑f.1 := by
  have hcomp := toUnitHom_changeLevel (dvd_mul_left N p) χ
  exact TauCeti.slash_mapGL_eq_self_of_comp_of_mem_modFormCharSpace (dvd_mul_left N p) hcomp f.2 h0
    (mem_Gamma1_iff.mp h1).2

/-- A form in `𝒮_k(pN, χ)`, `χ` modulo `N`, transforms trivially under `Γ₀(pN) ∩ Γ₁(N)`. -/
theorem slash_eq_self_of_mem_cuspSpace (k : ℤ) {p N : ℕ} [NeZero p] [NeZero N]
    (χ : DirichletCharacter ℂ N)
    (f : cuspSpace (N := p * N) k (DirichletCharacter.changeLevel (dvd_mul_left N p) χ))
    (γ : SL(2, ℤ)) (h0 : γ ∈ Gamma0 (p * N)) (h1 : γ ∈ Gamma1 N) :
    ⇑f.1 ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑f.1 := by
  have hcomp := toUnitHom_changeLevel (dvd_mul_left N p) χ
  exact TauCeti.slash_mapGL_eq_self_of_comp_of_mem_cuspFormCharSpace (dvd_mul_left N p) hcomp f.2 h0
    (mem_Gamma1_iff.mp h1).2

/-- Descent of a cusp form, with the target level `N` presented as `N' / p`. -/
private theorem descend_aux (k : ℤ) {p N' N : ℕ} [NeZero p] [NeZero N'] [NeZero N] (hp : p.Prime)
    (hpN : p ∣ N') (e : N' / p = N) (hdvd : N ∣ N') (χ' : (ZMod N')ˣ →* ℂˣ)
    (χ : (ZMod N)ˣ →* ℂˣ) (hcomp : χ' = χ.comp (ZMod.unitsMap hdvd))
    (f : CuspForm ((Gamma1 N').map (mapGL ℝ)) k) (hf : f ∈ TauCeti.cuspFormCharSpace k χ') :
    ∃ g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k, g ∈ TauCeti.cuspFormCharSpace k χ ∧
      ⇑g = TauCeti.descendSlash k p N' ⇑f := by
  subst e
  exact ⟨TauCeti.descendCuspForm k hp hpN hcomp hf,
    TauCeti.descendCuspForm_mem_cuspFormCharSpace k hp hpN hcomp hf, rfl⟩

/-- **Miyake, Lemma 4.6.6**, cusp forms: lowering `𝒮_k(pN, χ) → 𝒮_k(N, χ)` is well defined
(`χ` modulo `N`, `p` prime). -/
@[kb "miyake1989" "Lemma 4.6.6, p. 158 (the operator on cusp forms)"]
theorem exists_cuspSpace_lowerSlash (k : ℤ) {p N : ℕ} [NeZero p] [NeZero N] (hp : p.Prime)
    (χ : DirichletCharacter ℂ N)
    (f : cuspSpace (N := p * N) k (DirichletCharacter.changeLevel (dvd_mul_left N p) χ)) :
    ∃ g : cuspSpace k χ, ⇑g.1 = lowerSlash k p N ⇑f.1 := by
  obtain ⟨g, hg, hgf⟩ := descend_aux k hp (dvd_mul_right p N) (Nat.mul_div_cancel_left N hp.pos)
    (dvd_mul_left N p) (DirichletCharacter.changeLevel (dvd_mul_left N p) χ).toUnitHom χ.toUnitHom
    (toUnitHom_changeLevel (dvd_mul_left N p) χ) f.1 f.2
  exact ⟨⟨g, hg⟩, hgf⟩

/-- **The descent of a modular form.** For `p ∣ N` prime and `f ∈ M_k(Γ₁(N), χ)` with `χ` the
pull-back of `χ₀` modulo `N / p`, the descent slash sum of `f` as a modular form of level
`Γ₁(N / p)`. This is Tau Ceti's `TauCeti.descendCuspForm` (Chris Birkbeck and the Tau Ceti
contributors, Apache-2.0), whose construction is copied with boundedness at the cusps
(`TauCeti.isBoundedAt_descendSlash`) in place of vanishing. -/
def descendModularForm (k : ℤ) {p N : ℕ} [NeZero N] (hp : p.Prime) (hpN : p ∣ N)
    {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ TauCeti.modFormCharSpace k χ) :
    ModularForm ((Gamma1 (N / p)).map (mapGL ℝ)) k :=
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (N / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hpN) hp.pos).ne'⟩
  { toFun := TauCeti.descendSlash k p N f
    slash_action_eq' := fun γ hγ ↦ by
      obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.mp hγ
      rw [TauCeti.descendSlash_slash_mapGL_of_nebentypus_of_prime k hp hpN hcomp
        ⟨δ, Gamma1_in_Gamma0 (N / p) hδ⟩
        ((TauCeti.mem_modFormCharSpace_iff_nebentypus k χ f).mp hf)]
      have h1 : (Gamma0Map (N / p)).toHomUnits ⟨δ, Gamma1_in_Gamma0 (N / p) hδ⟩ = 1 :=
        Units.ext (by
          rw [MonoidHom.coe_toHomUnits, Gamma0Map_apply]
          exact (mem_Gamma1_iff.mp hδ).2)
      rw [h1, map_one, Units.val_one, one_smul]
    holo' := TauCeti.mdifferentiable_descendSlash k p N (ModularFormClass.holo f)
    bdd_at_cusps' := fun hc ↦ TauCeti.isBoundedAt_descendSlash k
      (fun c hc ↦ f.bdd_at_cusps' (Subgroup.IsArithmetic.isCusp_of_isCusp c hc)) hc }

/-- The underlying function of the descent of a modular form is the descent slash sum. -/
theorem coe_descendModularForm (k : ℤ) {p N : ℕ} [NeZero N] (hp : p.Prime) (hpN : p ∣ N)
    {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ TauCeti.modFormCharSpace k χ) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    ⇑(descendModularForm k hp hpN hcomp hf) = TauCeti.descendSlash k p N f :=
  rfl

/-- The descent of `f ∈ M_k(Γ₁(N), χ)` lies in `M_k(Γ₁(N / p), χ₀)` (the proof of Tau Ceti's
`TauCeti.descendCuspForm_mem_cuspFormCharSpace`). -/
theorem descendModularForm_mem_modFormCharSpace (k : ℤ) {p N : ℕ} [NeZero N] (hp : p.Prime)
    (hpN : p ∣ N) {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ TauCeti.modFormCharSpace k χ) :
    haveI : NeZero (N / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hpN) hp.pos).ne'⟩
    descendModularForm k hp hpN hcomp hf ∈ TauCeti.modFormCharSpace k χ₀ := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (N / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hpN) hp.pos).ne'⟩
  rw [TauCeti.mem_modFormCharSpace_iff_nebentypus, coe_descendModularForm]
  intro γ
  exact TauCeti.descendSlash_slash_mapGL_of_nebentypus_of_prime k hp hpN hcomp γ
    ((TauCeti.mem_modFormCharSpace_iff_nebentypus k χ f).mp hf)

/-- Descent of a modular form, with the target level `N` presented as `N' / p`. -/
private theorem descendMod_aux (k : ℤ) {p N' N : ℕ} [NeZero p] [NeZero N'] [NeZero N]
    (hp : p.Prime) (hpN : p ∣ N') (e : N' / p = N) (hdvd : N ∣ N') (χ' : (ZMod N')ˣ →* ℂˣ)
    (χ : (ZMod N)ˣ →* ℂˣ) (hcomp : χ' = χ.comp (ZMod.unitsMap hdvd))
    (f : ModularForm ((Gamma1 N').map (mapGL ℝ)) k) (hf : f ∈ TauCeti.modFormCharSpace k χ') :
    ∃ g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k, g ∈ TauCeti.modFormCharSpace k χ ∧
      ⇑g = TauCeti.descendSlash k p N' ⇑f := by
  subst e
  exact ⟨descendModularForm k hp hpN hcomp hf,
    descendModularForm_mem_modFormCharSpace k hp hpN hcomp hf, rfl⟩

/-- **Miyake, Lemma 4.6.6**, modular forms: lowering `𝒢_k(pN, χ) → 𝒢_k(N, χ)` is well defined
(`χ` modulo `N`, `p` prime). -/
@[kb "miyake1989" "Lemma 4.6.6, p. 158 (the operator on modular forms)"]
theorem exists_modSpace_lowerSlash (k : ℤ) {p N : ℕ} [NeZero p] [NeZero N] (hp : p.Prime)
    (χ : DirichletCharacter ℂ N)
    (f : modSpace (N := p * N) k (DirichletCharacter.changeLevel (dvd_mul_left N p) χ)) :
    ∃ g : modSpace k χ, ⇑g.1 = lowerSlash k p N ⇑f.1 := by
  obtain ⟨g, hg, hgf⟩ := descendMod_aux k hp (dvd_mul_right p N)
    (Nat.mul_div_cancel_left N hp.pos) (dvd_mul_left N p)
    (DirichletCharacter.changeLevel (dvd_mul_left N p) χ).toUnitHom χ.toUnitHom
    (toUnitHom_changeLevel (dvd_mul_left N p) χ) f.1 f.2
  exact ⟨⟨g, hg⟩, hgf⟩

/-- **Miyake, Lemma 4.6.6 (1)**, modular forms: lowering commutes with the natural embeddings
`𝒢_k(pN, χ) ⊂ 𝒢_k(pM, χ)` (and `𝒢_k(N, χ) ⊂ 𝒢_k(M, χ)`, the identity on functions). -/
@[kb "miyake1989" "Lemma 4.6.6 (1), p. 158"]
theorem lowerSlash_embedMod (k : ℤ) {p l N : ℕ} [NeZero p] [NeZero l] [NeZero N]
    (hp : p.Prime) (hpl : p.Coprime l) (χ : DirichletCharacter ℂ N)
    (f : modSpace (N := p * N) k (DirichletCharacter.changeLevel (dvd_mul_left N p) χ)) :
    lowerSlash k p (l * N)
        ⇑(embedMod (M := p * (l * N)) k _ (Nat.mul_dvd_mul_left p (dvd_mul_left N l)) f).1 =
      lowerSlash k p N ⇑f.1 := by
  rw [show ⇑(embedMod (M := p * (l * N)) k _ (Nat.mul_dvd_mul_left p (dvd_mul_left N l)) f).1
    = ⇑f.1 from rfl]
  exact lowerSlash_mul_left k hp hpl (fun ε hε ↦
    slash_eq_self_of_mem_modSpace k χ f ε (Gamma1_in_Gamma0 _ hε)
      (Gamma1_le_Gamma1_of_dvd (dvd_mul_left N p) hε))

/-- **Miyake, Lemma 4.6.6 (1)**, cusp forms. -/
@[kb "miyake1989" "Lemma 4.6.6 (1), p. 158 (cusp forms)"]
theorem lowerSlash_embed (k : ℤ) {p l N : ℕ} [NeZero p] [NeZero l] [NeZero N]
    (hp : p.Prime) (hpl : p.Coprime l) (χ : DirichletCharacter ℂ N)
    (f : cuspSpace (N := p * N) k (DirichletCharacter.changeLevel (dvd_mul_left N p) χ)) :
    lowerSlash k p (l * N)
        ⇑(embed (M := p * (l * N)) k _ (Nat.mul_dvd_mul_left p (dvd_mul_left N l)) f).1 =
      lowerSlash k p N ⇑f.1 := by
  rw [show ⇑(embed (M := p * (l * N)) k _ (Nat.mul_dvd_mul_left p (dvd_mul_left N l)) f).1
    = ⇑f.1 from rfl]
  exact lowerSlash_mul_left k hp hpl (fun ε hε ↦
    slash_eq_self_of_mem_cuspSpace k χ f ε (Gamma1_in_Gamma0 _ hε)
      (Gamma1_le_Gamma1_of_dvd (dvd_mul_left N p) hε))

/-- The descent commutes with `f ↦ f(lz)`, with the lowered level `N` presented as `N' / p`. -/
private theorem descend_raise_aux (k : ℤ) {p N' N l : ℕ} [NeZero p] [NeZero N'] [NeZero N]
    [NeZero l] (hp : p.Prime) (hpN : p ∣ N') (e : N' / p = N) (hdvd : N ∣ N') (hpl : p.Coprime l)
    (χ' : (ZMod N')ˣ →* ℂˣ) (χ : (ZMod N)ˣ →* ℂˣ) (hcomp : χ' = χ.comp (ZMod.unitsMap hdvd))
    (f : ModularForm ((Gamma1 N').map (mapGL ℝ)) k) (hf : f ∈ TauCeti.modFormCharSpace k χ') :
    TauCeti.descendSlash k p (l * N')
        ⇑(TauCeti.ModularForm.levelRaise l (TauCeti.Gamma1_map_le_conjAct_scaleGL N' l) f) =
      (l : ℂ) ^ (1 - k) • (TauCeti.descendSlash k p N' ⇑f ∣[k] TauCeti.scaleGL l) := by
  subst e
  exact TauCeti.descendSlash_coe_levelRaise_mul_left_of_comp_of_mem_modFormCharSpace k hp hpN hpl
    hcomp hf

/-- **Miyake, Lemma 4.6.6 (2)**, modular forms: lowering from `pM` to `M` of `f(lz)` is
`g(lz)` for `g` the lowering of `f` from `pN` to `N` (`f ↦ f(lz)` is `raiseMod`, and on
functions `g ↦ l^{1-k} (g ∣_k δ_l)`). -/
@[kb "miyake1989" "Lemma 4.6.6 (2), p. 158"]
theorem lowerSlash_raiseMod (k : ℤ) {p l N : ℕ} [NeZero p] [NeZero l] [NeZero N]
    (hp : p.Prime) (hpl : p.Coprime l) (χ : DirichletCharacter ℂ N)
    (f : modSpace (N := p * N) k (DirichletCharacter.changeLevel (dvd_mul_left N p) χ)) :
    lowerSlash k p (l * N) ⇑(raiseMod k _ l f).1 =
      (l : ℂ) ^ (1 - k) • (lowerSlash k p N ⇑f.1 ∣[k] TauCeti.scaleGL l) := by
  unfold lowerSlash
  rw [show p * (l * N) = l * (p * N) by ring]
  exact descend_raise_aux k hp (dvd_mul_right p N) (Nat.mul_div_cancel_left N hp.pos)
    (dvd_mul_left N p) hpl _ χ.toUnitHom (toUnitHom_changeLevel (dvd_mul_left N p) χ) f.1 f.2

/-- **Miyake, Lemma 4.6.6 (2)**, cusp forms. -/
@[kb "miyake1989" "Lemma 4.6.6 (2), p. 158 (cusp forms)"]
theorem lowerSlash_raise (k : ℤ) {p l N : ℕ} [NeZero p] [NeZero l] [NeZero N]
    (hp : p.Prime) (hpl : p.Coprime l) (χ : DirichletCharacter ℂ N)
    (f : cuspSpace (N := p * N) k (DirichletCharacter.changeLevel (dvd_mul_left N p) χ)) :
    lowerSlash k p (l * N) ⇑(raise k _ l f).1 =
      (l : ℂ) ^ (1 - k) • (lowerSlash k p N ⇑f.1 ∣[k] TauCeti.scaleGL l) := by
  have h := lowerSlash_raiseMod k hp hpl χ ⟨(f.1 : ModularForm _ k),
    (TauCeti.coe_mem_modFormCharSpace_iff k _ f.1).mpr f.2⟩
  exact h

end ModularFormsKB.Miyake.Wave6
