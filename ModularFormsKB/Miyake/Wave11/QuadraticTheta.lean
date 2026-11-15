import ModularFormsKB.Miyake.Wave4.Newforms
import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import ModularFormsKB.Citation
/-!
# Miyake §4.8: cusp forms attached to Hecke characters of quadratic fields (Theorems 4.8.2–4.8.3)

Miyake, *Modular Forms* (Springer 1989), §3.3 (pp. 90–91) and §4.8 (pp. 182–185).

**Hecke characters (Miyake §3.3).** For a number field `F`, an integral ideal `𝔪 ≠ 0` and the group
`I(𝔪)` of fractional ideals prime to `𝔪`, a *Hecke character mod `𝔪`* is a character
`ξ : I(𝔪) → ℂ¹` with `ξ((a)) = Π_v (a_v/|a_v|)^{u_v} |a_v|^{i v_v}` for `(a) ∈ P(𝔪)`, i.e.
`a ≡ 1 mod^× 𝔪` (3.3.1); it is extended to all ideals by `ξ(𝔞) = 0` for `𝔞 ∉ I(𝔪)`.

Here (`IdealHeckeChar`) `ξ` is recorded by its values on integral ideals: a multiplicative function
`Ideal (𝓞 K) → ℂ` of absolute value `1` on the nonzero ideals prime to `𝔪` and `0` elsewhere. A
character of the group `I(𝔪)` is determined by these values and every such function extends
(each element of `I(𝔪)` is a quotient of integral ideals prime to `𝔪`), so this is Miyake's
notion. The infinity condition (3.3.1) is imposed for integral generators `a ≡ 1 mod 𝔫`
(`SatisfiesInfinityType`); this is equivalent to the condition for all `a ∈ K^×` with
`a ≡ 1 mod^× 𝔫` (write such `a` as `b/c` with `b, c ∈ 𝓞_K`, `b ≡ c ≡ 1 mod 𝔫`, by the Chinese
remainder theorem). Miyake's set `M` of moduli for which (3.3.1) holds and his notion of
*primitive* (`𝔪 = 𝔪_ξ`, the greatest common divisor of `M`; as `𝔪 ∈ M` this says that `𝔪` divides
every element of `M`) are `IdealHeckeChar.IsPrimitive`.

Tau Ceti has Hecke characters in idelic form (`TauCeti.GlobalNumberFields.HeckeCharacter`, with
its ideal character `idealCharacter` on ideals prime to the conductor) and finite-order ray class
characters; Miyake's characters mod `𝔪` (a modulus that need not be the conductor, values `0`
off `I(𝔪)`) are not identified with them here (LE-MF-0223).

**The series.** For `ξ` and `u ≥ 0`, `f(z; ξ) = Σ_𝔞 ξ(𝔞) N(𝔞)^{u/2} e^{2πi N(𝔞) z}`, the sum over
the nonzero integral ideals; its `n`-th coefficient is `thetaCoeff ξ u n`
`= Σ_{N(𝔞) = n} ξ(𝔞) n^{u/2}` (`n ≥ 1`), and `0` for `n = 0`.

**Statements.** `ImaginaryQuadraticThetaStatement` (Theorem 4.8.2) and
`RealQuadraticThetaStatement` (Theorem 4.8.3) are **stated, not proved**. Miyake proves them by
Weil's converse theorem (Theorem 4.3.15) applied to the functional equations of the Hecke
`L`-functions `L(s, ξ(ψ ∘ N_K))` (Theorem 3.3.1, with Lemma 4.8.1), none of which is available in
the library (LE-MF-0229, LE-MF-0222).

**Proved.**
* `thetaCoeff_one`: `a(1) = 1` (the only integral ideal of norm `1` is `𝓞_K`).
* `thetaCoeff_restrict`: the first step of Miyake's proof, which reduces the theorem to primitive
  characters, `f(z; ξ') = f(z; ξ) - ξ(𝔭) N(𝔭)^{u/2} f(N(𝔭) z; ξ)` for a prime `𝔭` and the
  character `ξ'` mod `𝔭𝔫` induced by `ξ` (`IdealHeckeChar.restrict`), in coefficient form.
-/

open NumberField

noncomputable section

namespace ModularFormsKB.Miyake.Wave11

variable {K : Type*} [Field K] [NumberField K]

/-- **Miyake §3.3**: a character of `I(𝔪)` into `ℂ¹`, extended by `0` to the ideals not prime to
`𝔪`, recorded on the integral ideals of `K` (see the module docstring). The infinity type is
imposed separately (`SatisfiesInfinityType`). -/
@[kb "miyake1989" "Section 3.3, p. 91 (Hecke character mod m, values on integral ideals)"]
structure IdealHeckeChar (𝔪 : Ideal (𝓞 K)) where
  /-- The value `ξ(𝔞)` at an integral ideal. -/
  toFun : Ideal (𝓞 K) → ℂ
  map_top : toFun ⊤ = 1
  map_mul : ∀ 𝔞 𝔟, toFun (𝔞 * 𝔟) = toFun 𝔞 * toFun 𝔟
  norm_eq_one : ∀ 𝔞, 𝔞 ≠ ⊥ → IsCoprime 𝔞 𝔪 → ‖toFun 𝔞‖ = 1
  eq_zero_of_not_isCoprime : ∀ 𝔞, ¬ IsCoprime 𝔞 𝔪 → toFun 𝔞 = 0
  map_bot : toFun ⊥ = 0

namespace IdealHeckeChar

variable {𝔪 : Ideal (𝓞 K)}

instance : CoeFun (IdealHeckeChar 𝔪) fun _ ↦ Ideal (𝓞 K) → ℂ := ⟨IdealHeckeChar.toFun⟩

/-- Miyake (3.3.1) for the modulus `𝔫`: `ξ((a)) = ε(a)` for every nonzero integral `a ≡ 1 mod 𝔫`
with `(a)` prime to `𝔪` (the infinity type `ε` is a function on `𝓞_K`). For `𝔫 = 𝔪` this is the
defining condition of a Hecke character mod `𝔪` of infinity type `ε`; the moduli `𝔫` for which
it holds form Miyake's set `M`. -/
def SatisfiesInfinityType (ξ : IdealHeckeChar 𝔪) (ε : 𝓞 K → ℂ) (𝔫 : Ideal (𝓞 K)) : Prop :=
  ∀ a : 𝓞 K, a ≠ 0 → a - 1 ∈ 𝔫 → IsCoprime (Ideal.span {a}) 𝔪 → ξ (Ideal.span {a}) = ε a

/-- **Miyake §3.3**: `ξ` (of infinity type `ε`) is *primitive*: its conductor, the greatest common
divisor of the nonzero moduli `𝔫` for which (3.3.1) holds, is `𝔪`; as `𝔪` is such a modulus, this
says that `𝔪` divides (contains) each of them. -/
@[kb "miyake1989" "Section 3.3, p. 91 (conductor, primitive Hecke character)"]
def IsPrimitive (ξ : IdealHeckeChar 𝔪) (ε : 𝓞 K → ℂ) : Prop :=
  ∀ 𝔫 : Ideal (𝓞 K), 𝔫 ≠ ⊥ → ξ.SatisfiesInfinityType ε 𝔫 → 𝔫 ≤ 𝔪

/-- `ξ` is *induced from a Dirichlet character through `N_K`* (Miyake, Theorem 4.8.2): there is a
Dirichlet character `ψ` (of some modulus `M`) with `ξ(𝔞) = ψ(N_K(𝔞))` for all nonzero integral
`𝔞` prime to `𝔪` with `N_K(𝔞)` prime to `M`, i.e. `ξ` and `ψ ∘ N_K` are characters inducing the
same primitive character. -/
def IsInducedFromDirichlet (ξ : IdealHeckeChar 𝔪) : Prop :=
  ∃ (M : ℕ) (ψ : DirichletCharacter ℂ M), ∀ 𝔞 : Ideal (𝓞 K), 𝔞 ≠ ⊥ → IsCoprime 𝔞 𝔪 →
    (Ideal.absNorm 𝔞).Coprime M → ξ 𝔞 = ψ (Ideal.absNorm 𝔞)

end IdealHeckeChar

/-- The `n`-th coefficient of Miyake's `f(z; ξ) = Σ_𝔞 ξ(𝔞) N_K(𝔞)^{u/2} e^{2πi N_K(𝔞) z}` (the sum
over the nonzero integral ideals): `Σ_{N_K(𝔞) = n} ξ(𝔞) n^{u/2}` for `n ≥ 1`, and `0` for `n = 0`. -/
@[kb "miyake1989" "Theorem 4.8.2, p. 183 (the series f(z; xi))"]
def thetaCoeff {𝔪 : Ideal (𝓞 K)} (ξ : IdealHeckeChar 𝔪) (u n : ℕ) : ℂ :=
  if n = 0 then 0 else
    ∑ 𝔞 ∈ (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 K) n).toFinset,
      ξ 𝔞 * (Real.sqrt n : ℂ) ^ u

open ModularFormsKB.Miyake.Wave4

/-- The level `N = |d| N_K(𝔫)` of Theorems 4.8.2 and 4.8.3 is positive. -/
lemma level_ne_zero {𝔫 : Ideal (𝓞 K)} (h𝔫 : 𝔫 ≠ ⊥) :
    (discr K).natAbs * Ideal.absNorm 𝔫 ≠ 0 :=
  mul_ne_zero (Int.natAbs_ne_zero.2 (discr_ne_zero K))
    (fun h ↦ h𝔫 (Ideal.absNorm_eq_zero_iff.1 h))

/-- **Miyake, Theorem 4.8.2** (stated, not proved). Let `K` be an imaginary quadratic field of
discriminant `d`, embedded in `ℂ` by `σ`, and `ξ` a Hecke character mod `𝔫` with
`ξ((a)) = (a/|a|)^u` for `a ≡ 1 mod 𝔫` (`u ≥ 0`). Put `N = |d| N_K(𝔫)`. Then
`χ(m) = χ_d(m) ξ((m)) sgn(m)^u` is a Dirichlet character modulo `N` (`χ_d` the Kronecker symbol),
`f(z; ξ) ∈ 𝒢_{u+1}(N, χ)`, `f(z; ξ) ∈ 𝒮_{u+1}(N, χ)` unless `u = 0` and `ξ` is induced from a
Dirichlet character through `N_K`, and if `ξ` is primitive then `f(z; ξ)` is a primitive form. -/
@[kb "miyake1989" "Theorem 4.8.2, p. 183 (stated)"]
def ImaginaryQuadraticThetaStatement (K : Type*) [Field K] [NumberField K] : Prop :=
  Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (σ : K →+* ℂ) (𝔫 : Ideal (𝓞 K)) (h𝔫 : 𝔫 ≠ ⊥) (u : ℕ) (ξ : IdealHeckeChar 𝔫),
    ξ.SatisfiesInfinityType (fun a ↦ (σ a / (‖σ a‖ : ℂ)) ^ u) 𝔫 →
    haveI : NeZero ((discr K).natAbs * Ideal.absNorm 𝔫) := ⟨level_ne_zero h𝔫⟩
    ∃ χ : DirichletCharacter ℂ ((discr K).natAbs * Ideal.absNorm 𝔫),
      (∀ m : ℤ, χ m = (TauCeti.kroneckerSym (discr K) m : ℂ) * ξ (Ideal.span {(m : 𝓞 K)}) *
        (Int.sign m : ℂ) ^ u) ∧
      ∃ f : modSpace ((u + 1 : ℕ) : ℤ) χ, (∀ n : ℕ, coeffMod f n = thetaCoeff ξ u n) ∧
        (¬ (u = 0 ∧ ξ.IsInducedFromDirichlet) →
          f ∈ LinearMap.range (TauCeti.cuspToModFormCharSpace ((u + 1 : ℕ) : ℤ) χ.toUnitHom)) ∧
        (ξ.IsPrimitive (fun a ↦ (σ a / (‖σ a‖ : ℂ)) ^ u) →
          ∃ g : cuspSpace ((u + 1 : ℕ) : ℤ) χ, Wave4.IsPrimitive g ∧
            TauCeti.cuspToModFormCharSpace ((u + 1 : ℕ) : ℤ) χ.toUnitHom g = f)

/-- **Miyake, Theorem 4.8.3** (stated, not proved). Let `K` be a real quadratic field of
discriminant `d`, `σ : K → ℝ` one of its two embeddings, and `ξ` a Hecke character mod `𝔫` with
`ξ((a)) = sgn(σ(a))` for `a ≡ 1 mod 𝔫` (Miyake's two cases `sgn(a)`, `sgn(a')` are the two
choices of `σ`). Put `N = d N_K(𝔫)`. Then `χ(m) = χ_d(m) ξ((m))` is a Dirichlet character modulo
`N`, `f(z; ξ) = Σ_𝔞 ξ(𝔞) e^{2πi N_K(𝔞) z} ∈ 𝒮₁(N, χ)`, and if `ξ` is primitive then `f(z; ξ)` is a
primitive form. -/
@[kb "miyake1989" "Theorem 4.8.3, pp. 184-185 (stated)"]
def RealQuadraticThetaStatement (K : Type*) [Field K] [NumberField K] : Prop :=
  Module.finrank ℚ K = 2 → IsTotallyReal K →
  ∀ (σ : K →+* ℝ) (𝔫 : Ideal (𝓞 K)) (h𝔫 : 𝔫 ≠ ⊥) (ξ : IdealHeckeChar 𝔫),
    ξ.SatisfiesInfinityType (fun a ↦ ((SignType.sign (σ a) : ℤ) : ℂ)) 𝔫 →
    haveI : NeZero ((discr K).natAbs * Ideal.absNorm 𝔫) := ⟨level_ne_zero h𝔫⟩
    ∃ χ : DirichletCharacter ℂ ((discr K).natAbs * Ideal.absNorm 𝔫),
      (∀ m : ℤ, χ m = (TauCeti.kroneckerSym (discr K) m : ℂ) * ξ (Ideal.span {(m : 𝓞 K)})) ∧
      ∃ g : cuspSpace 1 χ, (∀ n : ℕ, coeff g n = thetaCoeff ξ 0 n) ∧
        (ξ.IsPrimitive (fun a ↦ ((SignType.sign (σ a) : ℤ) : ℂ)) → Wave4.IsPrimitive g)

/-! ### What is proved -/

/-- The first coefficient of `f(z; ξ)` is `1`: `𝓞_K` is the only integral ideal of norm `1`. -/
theorem thetaCoeff_one {𝔪 : Ideal (𝓞 K)} (ξ : IdealHeckeChar 𝔪) (u : ℕ) :
    thetaCoeff ξ u 1 = 1 := by
  rw [thetaCoeff, if_neg one_ne_zero]
  have : (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 K) 1).toFinset = {⊤} := by
    ext 𝔞
    simp [Ideal.absNorm_eq_one_iff]
  rw [this, Finset.sum_singleton, ξ.map_top]
  simp

namespace IdealHeckeChar

open scoped Classical

variable {𝔪 : Ideal (𝓞 K)}

/-- The character `ξ'` mod `𝔭𝔪` induced by `ξ` mod `𝔪` (Miyake, proof of Theorem 4.8.2):
`ξ'(𝔞) = ξ(𝔞)` for `𝔞` prime to `𝔭`, and `0` otherwise. -/
def restrict (ξ : IdealHeckeChar 𝔪) (𝔭 : Ideal (𝓞 K)) : IdealHeckeChar (𝔭 * 𝔪) where
  toFun 𝔞 := if IsCoprime 𝔞 𝔭 then ξ 𝔞 else 0
  map_top := by
    rw [if_pos (by rw [← Ideal.one_eq_top]; exact isCoprime_one_left)]
    exact ξ.map_top
  map_mul 𝔞 𝔟 := by
    by_cases ha : IsCoprime 𝔞 𝔭 <;> by_cases hb : IsCoprime 𝔟 𝔭 <;>
      simp [IsCoprime.mul_left_iff, ha, hb, ξ.map_mul]
  norm_eq_one 𝔞 h0 h := by
    have h' := IsCoprime.mul_right_iff.1 h
    simp only [if_pos h'.1]
    exact ξ.norm_eq_one 𝔞 h0 h'.2
  eq_zero_of_not_isCoprime 𝔞 h := by
    split_ifs with hp
    · exact ξ.eq_zero_of_not_isCoprime 𝔞 fun hm ↦ h (IsCoprime.mul_right hp hm)
    · rfl
  map_bot := by
    split_ifs
    · exact ξ.map_bot
    · rfl

lemma restrict_apply (ξ : IdealHeckeChar 𝔪) (𝔭 𝔞 : Ideal (𝓞 K)) :
    ξ.restrict 𝔭 𝔞 = if IsCoprime 𝔞 𝔭 then ξ 𝔞 else 0 := rfl

end IdealHeckeChar

open scoped Classical in
private lemma not_isCoprime_iff_dvd {𝔭 : Ideal (𝓞 K)} (h𝔭 : 𝔭.IsMaximal) (𝔞 : Ideal (𝓞 K)) :
    ¬ IsCoprime 𝔞 𝔭 ↔ 𝔭 ∣ 𝔞 := by
  rw [Ideal.dvd_iff_le]
  constructor
  · intro h
    by_contra h'
    apply h
    rw [Ideal.isCoprime_iff_sup_eq]
    exact h𝔭.1.2 _ (lt_of_le_of_ne le_sup_right fun e ↦ h' (e ▸ le_sup_left))
  · intro h hc
    rw [Ideal.isCoprime_iff_sup_eq] at hc
    exact h𝔭.ne_top (top_le_iff.1 (hc ▸ sup_le h le_rfl))

open scoped Classical in
/-- **Miyake, proof of Theorem 4.8.2** (first step, reduction to primitive characters), in
coefficient form: for a nonzero prime `𝔭` and the character `ξ'` mod `𝔭𝔪` induced by `ξ`,
`f(z; ξ') = f(z; ξ) - ξ(𝔭) N(𝔭)^{u/2} f(N(𝔭) z; ξ)`. -/
@[kb "miyake1989" "Theorem 4.8.2, proof, p. 184 (f(z, xi') = f(z, xi) - xi(p) N(p)^{u/2} f(N(p) z, xi))"]
theorem thetaCoeff_restrict {𝔪 : Ideal (𝓞 K)} (ξ : IdealHeckeChar 𝔪) {𝔭 : Ideal (𝓞 K)}
    (h𝔭 : 𝔭.IsMaximal) (h𝔭0 : 𝔭 ≠ ⊥) (u n : ℕ) :
    thetaCoeff (ξ.restrict 𝔭) u n = thetaCoeff ξ u n -
      (if Ideal.absNorm 𝔭 ∣ n then
        ξ 𝔭 * (Real.sqrt (Ideal.absNorm 𝔭) : ℂ) ^ u * thetaCoeff ξ u (n / Ideal.absNorm 𝔭)
      else 0) := by
  have hN : Ideal.absNorm 𝔭 ≠ 0 := fun h ↦ h𝔭0 (Ideal.absNorm_eq_zero_iff.1 h)
  by_cases hn : n = 0
  · subst hn
    simp [thetaCoeff]
  set S := (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 K) n).toFinset with hS
  have key : ∑ 𝔞 ∈ S, ξ.restrict 𝔭 𝔞 * (Real.sqrt n : ℂ) ^ u =
      ∑ 𝔞 ∈ S, ξ 𝔞 * (Real.sqrt n : ℂ) ^ u -
        ∑ 𝔞 ∈ S.filter (fun 𝔞 ↦ ¬ IsCoprime 𝔞 𝔭), ξ 𝔞 * (Real.sqrt n : ℂ) ^ u := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun 𝔞 ↦ IsCoprime 𝔞 𝔭),
      ← Finset.sum_filter_add_sum_filter_not S (fun 𝔞 ↦ IsCoprime 𝔞 𝔭) (fun 𝔞 ↦ ξ 𝔞 * (Real.sqrt n : ℂ) ^ u)]
    have h1 : ∑ 𝔞 ∈ S.filter (fun 𝔞 ↦ IsCoprime 𝔞 𝔭), ξ.restrict 𝔭 𝔞 * (Real.sqrt n : ℂ) ^ u =
        ∑ 𝔞 ∈ S.filter (fun 𝔞 ↦ IsCoprime 𝔞 𝔭), ξ 𝔞 * (Real.sqrt n : ℂ) ^ u :=
      Finset.sum_congr rfl fun 𝔞 h ↦ by
        rw [ξ.restrict_apply, if_pos (Finset.mem_filter.1 h).2]
    have h2 : ∑ 𝔞 ∈ S.filter (fun 𝔞 ↦ ¬ IsCoprime 𝔞 𝔭), ξ.restrict 𝔭 𝔞 * (Real.sqrt n : ℂ) ^ u = 0 :=
      Finset.sum_eq_zero fun 𝔞 h ↦ by
        rw [ξ.restrict_apply, if_neg (Finset.mem_filter.1 h).2, zero_mul]
    rw [h1, h2]; ring
  unfold thetaCoeff
  simp only [hn, if_false]
  rw [key]
  congr 1
  by_cases hd : Ideal.absNorm 𝔭 ∣ n
  · rw [if_pos hd]
    have hm : n / Ideal.absNorm 𝔭 ≠ 0 := by
      intro h
      rw [Nat.div_eq_zero_iff] at h
      rcases h with h | h
      · exact hN h
      · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) (not_le.2 h)
    rw [if_neg hm, Finset.mul_sum]
    symm
    refine Finset.sum_bij (fun 𝔟 _ ↦ 𝔭 * 𝔟) ?_ ?_ ?_ ?_
    · intro 𝔟 h𝔟
      simp only [hS, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h𝔟
      simp only [Finset.mem_filter, hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      refine ⟨?_, (not_isCoprime_iff_dvd h𝔭 _).2 (dvd_mul_right _ _)⟩
      rw [map_mul, h𝔟, Nat.mul_div_cancel' hd]
    · intro a _ b _ h
      exact mul_left_cancel₀ h𝔭0 h
    · intro 𝔞 h𝔞
      simp only [Finset.mem_filter, hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h𝔞
      obtain ⟨hn', hdv⟩ := h𝔞
      obtain ⟨𝔟, rfl⟩ := (not_isCoprime_iff_dvd h𝔭 _).1 hdv
      refine ⟨𝔟, ?_, rfl⟩
      simp only [hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      rw [map_mul] at hn'
      rw [← hn', Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hN)]
    · intro 𝔟 h𝔟
      simp only [hS, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h𝔟
      have hsq : (Real.sqrt n : ℂ) = (Real.sqrt (Ideal.absNorm 𝔭) : ℂ) *
          (Real.sqrt ((n / Ideal.absNorm 𝔭 : ℕ)) : ℂ) := by
        rw [← Complex.ofReal_mul, ← Real.sqrt_mul (Nat.cast_nonneg _)]
        congr 2
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hd]
      rw [ξ.map_mul, hsq, mul_pow]
      ring
  · rw [if_neg hd]
    refine Finset.sum_eq_zero ?_
    intro 𝔞 h𝔞
    simp only [Finset.mem_filter, hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h𝔞
    obtain ⟨hn', hdv⟩ := h𝔞
    exfalso
    apply hd
    rw [← hn']
    exact map_dvd Ideal.absNorm ((not_isCoprime_iff_dvd h𝔭 _).1 hdv)

end ModularFormsKB.Miyake.Wave11
