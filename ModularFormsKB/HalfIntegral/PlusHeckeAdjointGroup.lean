/-
# The group theory behind the self-adjointness of $T(p^2)$ on $S_{k+1/2}(4)$

Loose end LE-MF-0269.

Let $p$ be an odd prime, $\Gamma = \Gamma_0(4)$, $H = \{\gamma \in \Gamma : p^2 \mid b\}$ and
$r_0 = \begin{pmatrix}p^2 & y\\ 4 & w\end{pmatrix}$ (`repZero`, $p^2w - 4y = 1$). With $L = 4p^2$:

* `mem_Gamma0_iff_conj`: $u \in \Gamma_0(4p^2) \iff r_0ur_0^{-1} \in H$. Writing $u = \begin{pmatrix}a&b\\c&d\end{pmatrix}$, the
  lower-left entry of $r_0ur_0^{-1}$ is $\equiv w^2c \bmod 4$ and the upper-right entry is $\equiv -y^2c \bmod p^2$, and
  $w$, $y$ are units modulo $4$, $p^2$ respectively.
* `isGamma0Reps_conjReps`: if $r_x$ are the $p^2 + p$ representatives of $H\backslash\Gamma$ (`HeckeCoset.rep`) and $\gamma_i$
  the six representatives of $\Gamma\backslash\mathrm{SL}_2(\mathbb Z)$ (`gamma0FourReps`), the $6(p^2+p)$ elements
  $r_0^{-1}r_x\gamma_i$ represent $\Gamma_0(4p^2)\backslash\mathrm{SL}_2(\mathbb Z)$.
* `conjAct_normalizer`: $M = A\,r_0$ with $A = \mathrm{diag}(1, p^2)$, the Atkin–Lehner matrix
  $\begin{pmatrix}p^2&y\\4p^2&p^2w\end{pmatrix}$ of $\Gamma_0(4p^2)$ at $p^2$, normalizes $\Gamma_0(4p^2)$ in
  $\mathrm{GL}_2(\mathbb R)$. On $\mathbb H$ it acts by $z \mapsto (r_0z)/p^2$ (`M_smul`).

**Index shift.** Matrix entries are 0-based: $c = \gamma_{1,0}$, $d = \gamma_{1,1}$.
-/
import ModularFormsKB.HalfIntegral.HeckeCoset
import ModularFormsKB.HalfIntegral.Abstract.ChangeOfVariables
import ModularFormsKB.HalfIntegral.Abstract.PeterssonLevel

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped Pointwise

local notation "ℍ" => UpperHalfPlane

namespace PlusHeckeAdjoint

open ModularFormsKB.HalfIntegral.HeckeCoset

/-! ### Conjugation by $r_0$ -/

section Conj

variable (P : ℕ+) {y w : ℤ} (h : (P : ℤ) ^ 2 * w - 4 * ((1 : ℕ) : ℤ) * y = 1)

lemma conj_10 (u : SL(2, ℤ)) :
    (repZero 1 P y w h * u * (repZero 1 P y w h)⁻¹) 1 0 =
      4 * w * u 0 0 + w ^ 2 * u 1 0 - 16 * u 0 1 - 4 * w * u 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two, repZero, Matrix.vecMul, dotProduct]
  ring

lemma conj_01 (u : SL(2, ℤ)) :
    (repZero 1 P y w h * u * (repZero 1 P y w h)⁻¹) 0 1 =
      -((P : ℤ) ^ 2 * y * u 0 0) - y ^ 2 * u 1 0 + (P : ℤ) ^ 4 * u 0 1 + (P : ℤ) ^ 2 * y * u 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two, repZero, Matrix.vecMul, dotProduct]
  ring

lemma gamma0_mem_iff_dvd (L : ℕ) (u : SL(2, ℤ)) : u ∈ Gamma0 L ↔ (L : ℤ) ∣ u 1 0 := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- **$u \in \Gamma_0(4p^2)$ iff $r_0ur_0^{-1} \in H$.** -/
theorem mem_Gamma0_iff_conj (u : SL(2, ℤ)) :
    u ∈ Gamma0 (4 * (P : ℕ) ^ 2) ↔
      repZero 1 P y w h * u * (repZero 1 P y w h)⁻¹ ∈ Gamma0 (4 * 1) ∧
        (P : ℤ) ^ 2 ∣ (repZero 1 P y w h * u * (repZero 1 P y w h)⁻¹) 0 1 := by
  rw [gamma0_mem_iff_dvd, gamma0_mem_iff_dvd, conj_10, conj_01]
  have h' : (P : ℤ) ^ 2 * w - 4 * y = 1 := by simpa using h
  push_cast
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨⟨w * u 0 0 + w ^ 2 * (P : ℤ) ^ 2 * q - 4 * u 0 1 - w * u 1 1, ?_⟩,
      ⟨-(y * u 0 0) - 4 * y ^ 2 * q + (P : ℤ) ^ 2 * u 0 1 + y * u 1 1, ?_⟩⟩
    · rw [hq]; ring
    · rw [hq]; ring
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    -- `4 ∣ c`
    have h4 : (4 : ℤ) ∣ u 1 0 :=
      ⟨(P : ℤ) ^ 4 * (s - w * u 0 0 + 4 * u 0 1 + w * u 1 1) - y * ((P : ℤ) ^ 2 * w + 1) * u 1 0, by
        linear_combination (-(u 1 0) * ((P : ℤ) ^ 2 * w + 1)) * h' + (P : ℤ) ^ 4 * hs⟩
    -- `p² ∣ c`
    have hp2 : (P : ℤ) ^ 2 ∣ u 1 0 :=
      ⟨16 * (-t - y * u 0 0 + (P : ℤ) ^ 2 * u 0 1 + y * u 1 1) - w * ((P : ℤ) ^ 2 * w - 2) * u 1 0, by
        linear_combination (u 1 0 * ((P : ℤ) ^ 2 * w - 1 + 4 * y)) * h' - 16 * ht⟩
    have hcop : IsCoprime (4 : ℤ) ((P : ℤ) ^ 2) := ⟨-y, w, by linear_combination h'⟩
    exact hcop.mul_dvd h4 hp2

end Conj

/-! ### Representatives of $\Gamma_0(4p^2)\backslash\mathrm{SL}_2(\mathbb Z)$ -/

/-- A list built from a family $s : \iota \to \mathrm{SL}_2(\mathbb Z)$ such that every $g$ lies in exactly one coset
$\Gamma_0(L)s_j$ is a list of right coset representatives. -/
theorem isGamma0Reps_of_unique {ι : Type*} [Fintype ι] (L : ℕ) (s : ι → SL(2, ℤ))
    (hs : ∀ g : SL(2, ℤ), ∃! j, g * (s j)⁻¹ ∈ Gamma0 L) :
    IsGamma0Reps L ((Finset.univ : Finset ι).toList.map s) := by
  classical
  intro g
  set l := (Finset.univ : Finset ι).toList with hl
  let e : Fin l.length ≃ ι := List.Nodup.getEquivOfForallMemList l (Finset.nodup_toList _)
    (fun x ↦ Finset.mem_toList.2 (Finset.mem_univ x))
  have hlen : (l.map s).length = l.length := List.length_map _
  have hget : ∀ i : Fin (l.map s).length, (l.map s).get i = s (e (Fin.cast hlen i)) := by
    intro i
    simp [e]
  obtain ⟨j, hj, hju⟩ := hs g
  refine ⟨Fin.cast hlen.symm (e.symm j), ?_, ?_⟩
  · show g * ((l.map s).get _)⁻¹ ∈ Gamma0 L
    rw [hget]
    simpa using hj
  · intro i hi
    change g * ((l.map s).get i)⁻¹ ∈ Gamma0 L at hi
    rw [hget] at hi
    have h1 := hju _ hi
    apply Fin.ext
    have h2 : Fin.cast hlen i = e.symm j := by rw [← h1, Equiv.symm_apply_apply]
    simpa using congrArg Fin.val h2

section Reps

variable (P : ℕ+) (hp : (P : ℕ).Prime) (hpN : ¬ (P : ℕ) ∣ 4 * 1)

/-- The index set $(H\backslash\Gamma) \times (\Gamma\backslash\mathrm{SL}_2(\mathbb Z))$. -/
abbrev Idx := (Fin ((P : ℕ) ^ 2) ⊕ Fin (P : ℕ)) × Fin gamma0FourReps.length

/-- The representative $r_0$ of `HeckeCoset.rep` at the class $p^2 \mid x_{00}$. -/
noncomputable def r0 : SL(2, ℤ) :=
  repZero 1 P (zeroYW 1 P hp hpN).1 (zeroYW 1 P hp hpN).2 (zeroYW_spec 1 P hp hpN)

lemma rep_inr_zero_eq : rep 1 P hp hpN (Sum.inr ⟨0, hp.pos⟩) = r0 P hp hpN :=
  rep_inr_zero 1 P hp hpN _ rfl

lemma r0_mem : r0 P hp hpN ∈ Gamma0 (4 * 1) := by
  rw [← rep_inr_zero_eq P hp hpN]; exact rep_mem 1 P hp hpN _

/-- The representatives $r_0^{-1}r_x\gamma_i$. -/
noncomputable def conjRep (j : Idx P) : SL(2, ℤ) :=
  (r0 P hp hpN)⁻¹ * rep 1 P hp hpN j.1 * gamma0FourReps.get j.2

lemma gamma0_four_one : Gamma0 (4 * 1) = Gamma0 4 := rfl

theorem conjRep_unique (g : SL(2, ℤ)) :
    ∃! j : Idx P, g * (conjRep P hp hpN j)⁻¹ ∈ Gamma0 (4 * (P : ℕ) ^ 2) := by
  set r := r0 P hp hpN with hr
  have key : ∀ j : Idx P, g * (conjRep P hp hpN j)⁻¹ ∈ Gamma0 (4 * (P : ℕ) ^ 2) ↔
      (r * g * (gamma0FourReps.get j.2)⁻¹ * (rep 1 P hp hpN j.1)⁻¹ ∈ Gamma0 (4 * 1) ∧
        CRel P (r * g * (gamma0FourReps.get j.2)⁻¹) (rep 1 P hp hpN j.1)) := by
    intro j
    rw [mem_Gamma0_iff_conj P (zeroYW_spec 1 P hp hpN), CRel_iff]
    have e : repZero 1 P (zeroYW 1 P hp hpN).1 (zeroYW 1 P hp hpN).2 (zeroYW_spec 1 P hp hpN) *
        (g * (conjRep P hp hpN j)⁻¹) *
          (repZero 1 P (zeroYW 1 P hp hpN).1 (zeroYW 1 P hp hpN).2 (zeroYW_spec 1 P hp hpN))⁻¹ =
        r * g * (gamma0FourReps.get j.2)⁻¹ * (rep 1 P hp hpN j.1)⁻¹ := by
      rw [hr, r0, conjRep, r0]; group
    rw [e]
  obtain ⟨i, hi, hiu⟩ := isGamma0Reps_gamma0FourReps (r * g)
  obtain ⟨x, hx⟩ := exists_rel 1 P hp hpN (r * g * (gamma0FourReps.get i)⁻¹)
  have hmem : r * g * (gamma0FourReps.get i)⁻¹ * (rep 1 P hp hpN x)⁻¹ ∈ Gamma0 (4 * 1) :=
    Subgroup.mul_mem _ (by rw [gamma0_four_one]; exact hi) (inv_mem (rep_mem 1 P hp hpN x))
  refine ⟨(x, i), (key (x, i)).2 ⟨hmem, hx⟩, ?_⟩
  rintro ⟨x', i'⟩ hj
  obtain ⟨hm, hc⟩ := (key (x', i')).1 hj
  have h4 : r * g * (gamma0FourReps.get i')⁻¹ ∈ Gamma0 4 := by
    have := Subgroup.mul_mem _ hm (rep_mem 1 P hp hpN x')
    rw [gamma0_four_one] at this
    simpa using this
  have hi' : i' = i := hiu i' h4
  subst hi'
  have hx' : x' = x := rep_inj 1 P hp hpN x' x (hc.symm.trans hx)
  rw [hx']

/-- **The $6(p^2+p)$ elements $r_0^{-1}r_x\gamma_i$ represent $\Gamma_0(4p^2)\backslash\mathrm{SL}_2(\mathbb Z)$.** -/
theorem isGamma0Reps_conjReps :
    IsGamma0Reps (4 * (P : ℕ) ^ 2) ((Finset.univ : Finset (Idx P)).toList.map (conjRep P hp hpN)) :=
  isGamma0Reps_of_unique _ _ (conjRep_unique P hp hpN)

end Reps

/-! ### The normalizer $M = A r_0$ -/

section Normalizer

variable (P : ℕ+)

/-- $A = \mathrm{diag}(1, p^2) \in \mathrm{GL}_2(\mathbb R)$, acting by $z \mapsto z/p^2$. -/
noncomputable def Amat : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, ((P : ℕ) : ℝ) ^ 2]
    (by simp [Matrix.det_fin_two_of])

lemma coe_Amat : ((Amat P : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; 0, ((P : ℕ) : ℝ) ^ 2] := by
  simp [Amat]

/-- $\begin{pmatrix}a & p^2b\\ c' & d\end{pmatrix}$ for $u = \begin{pmatrix}a&b\\p^2c'&d\end{pmatrix}$. -/
def lowerDiv (u : SL(2, ℤ)) {c' : ℤ} (hc : u 1 0 = (P : ℤ) ^ 2 * c') : SL(2, ℤ) :=
  ⟨!![u 0 0, (P : ℤ) ^ 2 * u 0 1; c', u 1 1], by
    have hd := u.det_coe
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of]; linear_combination hd + (u 0 1) * hc⟩

@[simp] lemma lowerDiv_00 (u : SL(2, ℤ)) {c' : ℤ} (hc : u 1 0 = (P : ℤ) ^ 2 * c') :
    lowerDiv P u hc 0 0 = u 0 0 := rfl
@[simp] lemma lowerDiv_01 (u : SL(2, ℤ)) {c' : ℤ} (hc : u 1 0 = (P : ℤ) ^ 2 * c') :
    lowerDiv P u hc 0 1 = (P : ℤ) ^ 2 * u 0 1 := rfl
@[simp] lemma lowerDiv_10 (u : SL(2, ℤ)) {c' : ℤ} (hc : u 1 0 = (P : ℤ) ^ 2 * c') :
    lowerDiv P u hc 1 0 = c' := rfl
@[simp] lemma lowerDiv_11 (u : SL(2, ℤ)) {c' : ℤ} (hc : u 1 0 = (P : ℤ) ^ 2 * c') :
    lowerDiv P u hc 1 1 = u 1 1 := rfl

lemma mapGL_mul_Amat (u : SL(2, ℤ)) {c' : ℤ} (hc : u 1 0 = (P : ℤ) ^ 2 * c') :
    mapGL ℝ u * Amat P = Amat P * mapGL ℝ (lowerDiv P u hc) := by
  ext i j
  have hc' : ((u 1 0 : ℤ) : ℝ) = ((P : ℕ) : ℝ) ^ 2 * (c' : ℝ) := by rw [hc]; push_cast; ring
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.mapGL_coe_matrix, coe_Amat, hc'] <;> ring

end Normalizer

section Normalizer2

variable (P : ℕ+) (hp : (P : ℕ).Prime) (hpN : ¬ (P : ℕ) ∣ 4 * 1)

lemma mem_iff_r0 (u : SL(2, ℤ)) :
    u ∈ Gamma0 (4 * (P : ℕ) ^ 2) ↔
      r0 P hp hpN * u * (r0 P hp hpN)⁻¹ ∈ Gamma0 (4 * 1) ∧
        (P : ℤ) ^ 2 ∣ (r0 P hp hpN * u * (r0 P hp hpN)⁻¹) 0 1 :=
  mem_Gamma0_iff_conj P (zeroYW_spec 1 P hp hpN) u

/-- $M = A r_0 = \begin{pmatrix}p^2&y\\4p^2&p^2w\end{pmatrix}$. -/
noncomputable def Mmat : GL (Fin 2) ℝ := Amat P * mapGL ℝ (r0 P hp hpN)

lemma normalizer_left {τ : SL(2, ℤ)} (hτ : τ ∈ Gamma0 (4 * (P : ℕ) ^ 2)) :
    ∃ τ' ∈ Gamma0 (4 * (P : ℕ) ^ 2), mapGL ℝ τ * Mmat P hp hpN = Mmat P hp hpN * mapGL ℝ τ' := by
  obtain ⟨q, hq⟩ := (gamma0_mem_iff_dvd _ τ).1 hτ
  have hc : τ 1 0 = (P : ℤ) ^ 2 * (4 * q) := by rw [hq]; push_cast; ring
  set r := r0 P hp hpN
  refine ⟨r⁻¹ * lowerDiv P τ hc * r, (mem_iff_r0 P hp hpN _).2 ⟨?_, ?_⟩, ?_⟩
  · have e : r * (r⁻¹ * lowerDiv P τ hc * r) * r⁻¹ = lowerDiv P τ hc := by group
    rw [e, gamma0_mem_iff_dvd, lowerDiv_10]
    exact ⟨q, by push_cast; ring⟩
  · have e : r * (r⁻¹ * lowerDiv P τ hc * r) * r⁻¹ = lowerDiv P τ hc := by group
    rw [e, lowerDiv_01]
    exact dvd_mul_right _ _
  · show mapGL ℝ τ * (Amat P * mapGL ℝ r) = (Amat P * mapGL ℝ r) * mapGL ℝ (r⁻¹ * lowerDiv P τ hc * r)
    rw [map_mul, map_mul, map_inv, ← mul_assoc, mapGL_mul_Amat P τ hc]
    group

/-- $\begin{pmatrix}a & b'\\ p^2c & d\end{pmatrix}$ for $v = \begin{pmatrix}a&p^2b'\\c&d\end{pmatrix}$. -/
def upperDiv (v : SL(2, ℤ)) {b' : ℤ} (hb : v 0 1 = (P : ℤ) ^ 2 * b') : SL(2, ℤ) :=
  ⟨!![v 0 0, b'; (P : ℤ) ^ 2 * v 1 0, v 1 1], by
    have hd := v.det_coe
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of]; linear_combination hd + (v 1 0) * hb⟩

lemma lowerDiv_upperDiv (v : SL(2, ℤ)) {b' : ℤ} (hb : v 0 1 = (P : ℤ) ^ 2 * b') :
    lowerDiv P (upperDiv P v hb) (c' := v 1 0) rfl = v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerDiv, upperDiv, hb]

lemma normalizer_right {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 (4 * (P : ℕ) ^ 2)) :
    ∃ σ' ∈ Gamma0 (4 * (P : ℕ) ^ 2), Mmat P hp hpN * mapGL ℝ σ = mapGL ℝ σ' * Mmat P hp hpN := by
  set r := r0 P hp hpN
  obtain ⟨hv4, b', hb'⟩ := (mem_iff_r0 P hp hpN σ).1 hσ
  set v := r * σ * r⁻¹ with hv
  obtain ⟨q, hq⟩ := (gamma0_mem_iff_dvd _ v).1 hv4
  refine ⟨upperDiv P v hb', ?_, ?_⟩
  · rw [gamma0_mem_iff_dvd]
    refine ⟨q, ?_⟩
    change (P : ℤ) ^ 2 * v 1 0 = _
    rw [hq]; push_cast; ring
  · have h1 := mapGL_mul_Amat P (upperDiv P v hb') (c' := v 1 0) rfl
    rw [lowerDiv_upperDiv] at h1
    have h2 : mapGL ℝ r * mapGL ℝ σ = mapGL ℝ v * mapGL ℝ r := by
      rw [hv, map_mul, map_mul, map_inv]; group
    show (Amat P * mapGL ℝ r) * mapGL ℝ σ = mapGL ℝ (upperDiv P v hb') * (Amat P * mapGL ℝ r)
    rw [mul_assoc, h2, ← mul_assoc, ← h1, mul_assoc]

/-- **$M = A r_0$ normalizes $\Gamma_0(4p^2)$** in $\mathrm{GL}_2(\mathbb R)$. -/
theorem conjAct_normalizer :
    ConjAct.toConjAct (Mmat P hp hpN)⁻¹ • (Gamma0 (4 * (P : ℕ) ^ 2)).map (mapGL ℝ) =
      (Gamma0 (4 * (P : ℕ) ^ 2)).map (mapGL ℝ) := by
  ext y
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    ConjAct.ofConjAct_toConjAct, map_inv, inv_inv, Subgroup.mem_map]
  constructor
  · rintro ⟨τ, hτ, hτy⟩
    obtain ⟨τ', hτ', h⟩ := normalizer_left P hp hpN hτ
    refine ⟨τ', hτ', ?_⟩
    rw [hτy] at h
    refine (mul_left_cancel (a := Mmat P hp hpN) ?_).symm
    rw [← h]
    group
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨σ', hσ', h⟩ := normalizer_right P hp hpN hσ
    refine ⟨σ', hσ', ?_⟩
    rw [h]
    group

lemma Amat_smul (z : ℍ) : Amat P • z = affPt 1 (P ^ 2) 0 z := by
  have hdet : 0 < (Amat P).det.val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_Amat, Matrix.det_fin_two_of]
    have : (0 : ℝ) < (P : ℕ) := by exact_mod_cast P.pos
    nlinarith
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet, coe_affPt]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, coe_Amat]

lemma Mmat_smul (z : ℍ) : Mmat P hp hpN • z = affPt 1 (P ^ 2) 0 (r0 P hp hpN • z) := by
  rw [Mmat, mul_smul, ← Amat_smul]
  rfl

end Normalizer2

end PlusHeckeAdjoint

end ModularFormsKB.HalfIntegral
