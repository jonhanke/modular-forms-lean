import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import ModularFormsKB.Citation
/-!
# Clausen's transformation of the divisor series

Jacobi, *Fundamenta nova* (1829), § 66, pp. 187–188, reports Clausen's observation (Crelle's Journal 3, p. 95):
for `‖q‖ < 1`,
`∑_{n ≥ 1} qⁿ/(1 - qⁿ) = ∑_{n ≥ 1} q^{n²} (1 + qⁿ)/(1 - qⁿ)`.
Both sides are `∑_N d(N) q^N`: on the right, `q^{n²}(1 + qⁿ)/(1 - qⁿ) = q^{n²} + 2 ∑_{k ≥ 1} q^{n(n+k)}` counts the
divisor pairs `(n, n + k)` of `N = n(n + k)` with `n ≤ n + k`.
-/

noncomputable section

namespace ModularFormsKB.Historical.Jacobi

/-- **Clausen's transformation** (Jacobi, *Fundamenta nova*, § 66, pp. 187–188):
for `‖q‖ < 1`, `∑_{n ≥ 1} qⁿ/(1 - qⁿ) = ∑_{n ≥ 1} q^{n²}(1 + qⁿ)/(1 - qⁿ)`. Indices shifted to start at `0`. -/
@[kb "jacobi1829" "§ 66, pp. 187-188"]
def ClausenTransformation : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 →
    HasSum (fun n : ℕ ↦ q ^ ((n + 1) ^ 2) * (1 + q ^ (n + 1)) / (1 - q ^ (n + 1)))
      (∑' n : ℕ, q ^ (n + 1) / (1 - q ^ (n + 1)))

/-- The double family `q^{(a+1)(b+1)}`. -/
private def clF (q : ℂ) (p : ℕ × ℕ) : ℂ := q ^ ((p.1 + 1) * (p.2 + 1))

private def clg1 (x : ℕ × ℕ) : ℕ × ℕ := (x.1, x.1 + x.2 + 1)
private def clg2 (a : ℕ) : ℕ × ℕ := (a, a)
private def clg3 (x : ℕ × ℕ) : ℕ × ℕ := (x.1 + x.2 + 1, x.1)

private lemma clF_summable {q : ℂ} (hq : ‖q‖ < 1) : Summable (clF q) := by
  have h := summable_prod_mul_pow (𝕜 := ℂ) 0 hq
  let e : ℕ+ × ℕ+ ≃ ℕ × ℕ := Equiv.prodCongr Equiv.pnatEquivNat Equiv.pnatEquivNat
  rw [← e.summable_iff]
  refine h.congr fun c ↦ ?_
  simp only [Function.comp, clF, e, Equiv.prodCongr_apply, Equiv.pnatEquivNat_apply, Prod.map,
    pow_zero, one_mul]
  rw [← PNat.natPred_add_one c.1, ← PNat.natPred_add_one c.2]

private lemma clF_symm (q : ℂ) (a b : ℕ) : clF q (a, b) = clF q (b, a) := by
  simp [clF, mul_comm]

private lemma cl_mem1 (p : ℕ × ℕ) : p ∈ Set.range clg1 ↔ p.1 < p.2 := by
  constructor
  · rintro ⟨x, rfl⟩; simp [clg1]
  · intro h; exact ⟨(p.1, p.2 - p.1 - 1), by ext <;> simp [clg1]; omega⟩

private lemma cl_mem2 (p : ℕ × ℕ) : p ∈ Set.range clg2 ↔ p.1 = p.2 := by
  constructor
  · rintro ⟨x, rfl⟩; simp [clg2]
  · intro h; exact ⟨p.1, by ext <;> simp [clg2, h]⟩

private lemma cl_mem3 (p : ℕ × ℕ) : p ∈ Set.range clg3 ↔ p.2 < p.1 := by
  constructor
  · rintro ⟨x, rfl⟩; simp [clg3]
  · intro h; exact ⟨(p.2, p.1 - p.2 - 1), by ext <;> simp [clg3]; omega⟩

private lemma cl_inj1 : Function.Injective clg1 := fun x y h ↦ by
  simp only [clg1, Prod.mk.injEq] at h; ext <;> omega

private lemma cl_inj2 : Function.Injective clg2 := fun x y h ↦ by simpa [clg2] using h

private lemma cl_inj3 : Function.Injective clg3 := fun x y h ↦ by
  simp only [clg3, Prod.mk.injEq] at h; ext <;> omega

private lemma cl_piece {q : ℂ} {ι : Type} (g : ι → ℕ × ℕ) (hg : Function.Injective g)
    (S : ℂ) (hS : HasSum (clF q ∘ g) S) :
    HasSum (Set.indicator (Set.range g) (clF q)) S := by
  rw [← hg.hasSum_iff (fun x hx ↦ Set.indicator_of_notMem hx _)]
  convert hS using 1
  funext x; simp

private lemma cl_geom {q : ℂ} (hq : ‖q‖ < 1) (a : ℕ) :
    HasSum (fun k : ℕ ↦ q ^ ((a + 1) ^ 2) * (q ^ (a + 1) * (q ^ (a + 1)) ^ k))
      (q ^ ((a + 1) ^ 2) * (q ^ (a + 1) / (1 - q ^ (a + 1)))) := by
  have hr : ‖q ^ (a + 1)‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have := ((hasSum_geometric_of_norm_lt_one hr).mul_left (q ^ (a + 1))).mul_left (q ^ ((a + 1) ^ 2))
  simpa [div_eq_mul_inv] using this

/-- **Clausen's transformation** (Jacobi, *Fundamenta nova*, § 66, pp. 187–188):
both sides equal `∑ d(N) q^N`, proved by splitting `∑_{(n,m)} q^{nm}` into `n < m`, `n = m`, `n > m`. -/
@[kb "jacobi1829" "§ 66, pp. 187-188"]
theorem clausenTransformation : ClausenTransformation := by
  intro q hq
  have hF := clF_summable hq
  have s1 : Summable (clF q ∘ clg1) := hF.comp_injective cl_inj1
  have s2 : Summable (clF q ∘ clg2) := hF.comp_injective cl_inj2
  have e13 : clF q ∘ clg3 = clF q ∘ clg1 := by
    funext x; simp only [Function.comp, clg1, clg3]; exact (clF_symm q _ _).symm
  set S1 := ∑' x, clF q (clg1 x) with hS1
  set S2 := ∑' a, clF q (clg2 a) with hS2
  have hdec : HasSum (clF q) (S1 + S2 + S1) := by
    have k1 := cl_piece clg1 cl_inj1 S1 s1.hasSum
    have k2 := cl_piece clg2 cl_inj2 S2 s2.hasSum
    have k3 := cl_piece clg3 cl_inj3 S1 (by rw [e13]; exact s1.hasSum)
    have hf : clF q = Set.indicator (Set.range clg1) (clF q) + Set.indicator (Set.range clg2) (clF q)
        + Set.indicator (Set.range clg3) (clF q) := by
      funext p
      simp only [Pi.add_apply]
      have m1 := cl_mem1 p
      have m2 := cl_mem2 p
      have m3 := cl_mem3 p
      rcases lt_trichotomy p.1 p.2 with h | h | h
      · rw [Set.indicator_of_mem (m1.2 h), Set.indicator_of_notMem (fun hh ↦ by have := m2.1 hh; omega),
          Set.indicator_of_notMem (fun hh ↦ by have := m3.1 hh; omega)]
        simp
      · rw [Set.indicator_of_notMem (fun hh ↦ by have := m1.1 hh; omega), Set.indicator_of_mem (m2.2 h),
          Set.indicator_of_notMem (fun hh ↦ by have := m3.1 hh; omega)]
        simp
      · rw [Set.indicator_of_notMem (fun hh ↦ by have := m1.1 hh; omega),
          Set.indicator_of_notMem (fun hh ↦ by have := m2.1 hh; omega), Set.indicator_of_mem (m3.2 h)]
        simp
    rw [hf]
    exact (k1.add k2).add k3
  have hr : ∀ a : ℕ, ‖q ^ (a + 1)‖ < 1 := fun a ↦ by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have hne : ∀ a : ℕ, 1 - q ^ (a + 1) ≠ 0 := fun a h ↦ by
    have := hr a
    have h1 : q ^ (a + 1) = 1 := by linear_combination -h
    rw [h1] at this; simp at this
  -- left side
  have hL : ∑' n : ℕ, q ^ (n + 1) / (1 - q ^ (n + 1)) = S1 + S2 + S1 := by
    refine (hdec.prod_fiberwise fun a ↦ ?_).tsum_eq
    have := ((hasSum_geometric_of_norm_lt_one (hr a)).mul_left (q ^ (a + 1)))
    simp only [clF]
    convert this using 1
    · funext b; rw [← pow_mul, ← pow_add]; congr 1; ring
    · simp [div_eq_mul_inv]
  rw [hL]
  have hfib := s1.hasSum.prod_fiberwise (g := fun a ↦ q ^ ((a + 1) ^ 2) * (q ^ (a + 1) / (1 - q ^ (a + 1))))
    fun a ↦ by
      convert cl_geom hq a using 1
      funext k
      simp only [Function.comp, clF, clg1]
      rw [← pow_mul, ← pow_add, ← pow_add]
      congr 1; ring
  have hT := (s2.hasSum.add (hfib.mul_left 2))
  convert hT using 1
  · funext a
    simp only [Function.comp, clF, clg2]
    field_simp [hne a]
    ring
  · show S1 + S2 + S1 = S2 + 2 * S1
    ring

end ModularFormsKB.Historical.Jacobi
