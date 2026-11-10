import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Basic.Complex.Basic
import ModularFormsKB.Citation
/-!
# Shimura 2007, Lemma 1.12: primitive characters of conductor $2g$

G. Shimura, *Elementary Dirichlet Series and Modular Forms* (Springer 2007), Lemma 1.12, p. 13
(pdf p. 19).

If $\chi$ is a primitive Dirichlet character of conductor $2g$ with $0 < g \in \mathbb Z$, then
$g$ is even (`even_of_isPrimitive_two_mul`) and $\chi(1-g) = -1$ (`primitive_apply_one_sub_half`).

The proof follows Shimura: the kernel of $(\mathbb Z/2g)^\times \to (\mathbb Z/g)^\times$ is
contained in $\{1, 1+g\}$, and a primitive character cannot be trivial on this kernel.
-/

namespace ModularFormsKB.Shimura2007

open DirichletCharacter

/-- A unit $u$ of $\mathbb Z/2g$ in the kernel of the reduction map to $\mathbb Z/g$ has
representative $1$ or $1+g$, and the representative is odd. -/
lemma unit_ker_val_cases {g : ℕ} (hg : 0 < g) (u : (ZMod (2 * g))ˣ)
    (hu : ZMod.unitsMap (dvd_mul_left g 2) u = 1) :
    ((u : ZMod (2 * g)).val = 1 ∨ (u : ZMod (2 * g)).val = 1 + g) ∧
      Odd (u : ZMod (2 * g)).val := by
  have : NeZero (2 * g) := ⟨by omega⟩
  set x := (u : ZMod (2 * g)).val with hx
  have hodd : Odd x := by
    have h := ZMod.val_coe_unit_coprime u
    have h2 : Nat.Coprime x 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 g) h
    exact Nat.coprime_two_right.mp h2
  have hlt : x < 2 * g := ZMod.val_lt _
  refine ⟨?_, hodd⟩
  have hcast : ((x : ℕ) : ZMod g) = 1 := by
    have h1 := congrArg Units.val hu
    rw [ZMod.unitsMap_val] at h1
    have h2 : (u : ZMod (2 * g)) = (x : ZMod (2 * g)) := (ZMod.natCast_zmod_val _).symm
    rw [h2, ZMod.cast_natCast (dvd_mul_left g 2)] at h1
    simpa using h1
  have hmod : x % g = 1 % g := by
    have : (x : ZMod g) = ((1 : ℕ) : ZMod g) := by simpa using hcast
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this
  have hdm := Nat.div_add_mod x g
  have hq : x / g < 2 := by
    exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hlt)
  by_cases hg1 : g = 1
  · subst hg1; obtain ⟨k, hk⟩ := hodd; omega
  · have : 1 % g = 1 := Nat.mod_eq_of_lt (by omega)
    rw [this] at hmod
    interval_cases h : x / g <;> omega

/-- **Shimura, Lemma 1.12 (first step)**: a primitive Dirichlet character of level $2g$ has
$g$ even (there is no primitive character of conductor $2m$ with $m$ odd). -/
theorem even_of_isPrimitive_two_mul {g : ℕ} (hg : 0 < g)
    (χ : DirichletCharacter ℂ (2 * g)) (hχ : χ.IsPrimitive) : Even g := by
  have : NeZero (2 * g) := ⟨by omega⟩
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  apply absurd hχ
  have hf : χ.FactorsThrough g := by
    rw [factorsThrough_iff_ker_unitsMap (dvd_mul_left g 2)]
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    obtain ⟨h1, hxo⟩ := unit_ker_val_cases hg u hu
    have hu1 : u = 1 := by
      rcases h1 with h1 | h1
      · apply Units.ext
        rw [← ZMod.natCast_zmod_val (u : ZMod (2 * g)), h1]; simp
      · exfalso
        rw [h1] at hxo
        have : _root_.Even (1 + g) := by
          rw [add_comm]; exact hodd.add_one
        exact (Nat.not_even_iff_odd.mpr hxo) this
    rw [MonoidHom.mem_ker, hu1, map_one]
  have hle : χ.conductor ≤ g := Nat.sInf_le ((mem_conductorSet_iff χ).mpr hf)
  intro h
  unfold IsPrimitive at h
  omega

/-- **Shimura, Lemma 1.12**: if $\chi$ is a primitive Dirichlet character of conductor $2g$,
$0 < g \in \mathbb Z$, then $\chi(1-g) = -1$. -/
@[kb "shimura2007" "Lemma 1.12, p. 13"]
theorem primitive_apply_one_sub_half {g : ℕ} (hg : 0 < g)
    (χ : DirichletCharacter ℂ (2 * g)) (hχ : χ.IsPrimitive) :
    χ ((1 : ZMod (2 * g)) - g) = -1 := by
  have : NeZero (2 * g) := ⟨by omega⟩
  obtain ⟨r, hr⟩ := even_of_isPrimitive_two_mul hg χ hχ
  have h2g : (2 : ZMod (2 * g)) * g = 0 := by
    have := ZMod.natCast_self (2 * g)
    push_cast at this
    exact this
  have hgg : (g : ZMod (2 * g)) * g = 0 := by
    have hn : g * g = r * (2 * g) := by
      nth_rewrite 1 [hr]; ring
    rw [← Nat.cast_mul, hn, Nat.cast_mul, ZMod.natCast_self, mul_zero]
  have hmul : ((1 : ZMod (2 * g)) - g) * (1 - g) = 1 := by
    have : ((1 : ZMod (2 * g)) - g) * (1 - g) = 1 - (2 * g) + g * g := by ring
    rw [this, h2g, hgg]; simp
  let w : (ZMod (2 * g))ˣ := ⟨1 - g, 1 - g, hmul, hmul⟩
  have hw : χ ((1 : ZMod (2 * g)) - g) * χ ((1 : ZMod (2 * g)) - g) = 1 := by
    rw [← map_mul, hmul, map_one]
  rcases mul_self_eq_one_iff.mp hw with h | h
  · exfalso
    apply absurd hχ
    have hf : χ.FactorsThrough g := by
      rw [factorsThrough_iff_ker_unitsMap (dvd_mul_left g 2)]
      intro u hu
      rw [MonoidHom.mem_ker] at hu
      obtain ⟨h1, -⟩ := unit_ker_val_cases hg u hu
      rw [MonoidHom.mem_ker]
      rcases h1 with h1 | h1
      · have : u = 1 := by
          apply Units.ext
          rw [← ZMod.natCast_zmod_val (u : ZMod (2 * g)), h1]; simp
        rw [this, map_one]
      · have : u = w := by
          apply Units.ext
          rw [← ZMod.natCast_zmod_val (u : ZMod (2 * g)), h1]
          show _ = (1 : ZMod (2 * g)) - g
          have : (1 : ZMod (2 * g)) + g = 1 - g + (2 * g) := by ring
          push_cast
          rw [this, h2g, add_zero]
        rw [this]; apply Units.ext; rw [MulChar.coe_toUnitHom]
        simpa [w] using h
    have hle : χ.conductor ≤ g := Nat.sInf_le ((mem_conductorSet_iff χ).mpr hf)
    intro h
    unfold IsPrimitive at h
    omega
  · exact h

end ModularFormsKB.Shimura2007
