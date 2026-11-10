import ModularFormsKB.Milne.Ch11.SchmidtCount
import ModularFormsKB.Milne.Ch11.WeilNewton
import ModularFormsKB.Milne.Ch11.WeilConstantExtensionExists
import ModularFormsKB.Milne.Ch11.WeilRationality
import Mathlib.Algebra.Lie.OfAssociative

/-!
# F. K. Schmidt's theorem: constant field extensions

Let $F/k$ be a function field over a finite field with $q$ elements, $k$ algebraically closed in $F$, and let
$\delta$ divide the degree of every place (Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed.,
Lemma 5.1.9 – Corollary 5.1.11).

- `effectiveDivisorCount_mul_eq_sum_of_degree`: for a divisor $D$ of degree $\delta$ and representatives $R_c$ of
  $\mathrm{Cl}^0(F)$, $(q-1)A_{\delta m} = \sum_c (q^{\ell(mD + R_c)} - 1)$ (as `effectiveDivisorCount_mul_eq_sum`, with
  $D$ in place of a divisor of degree one).
- `effectiveDivisorCount_eq_zero_of_not_dvd`, `curvePointCount_eq_zero_of_not_dvd`: $A_n = N_n = 0$ for $\delta \nmid n$.
- `curvePointCount_constantCompositum`: $N_m(F\cdot k') = N_{[k':k]m}(F)$, from `card_degree_one_constantCompositum` in
  the tower $F \subseteq F\cdot k' \subseteq F\cdot k''$, $[k'':k'] = m$.
- `zeta_constantCompositum_eq_pow`: for $[k':k] = \delta$, $Z_{F\cdot k'}(u) = Y(u)^\delta$ with
  $Y(u) = \sum_m A_{\delta m}(F)u^m$ (both sides have constant term $1$ and the same logarithmic derivative
  $\sum_m N_m(F\cdot k')u^m = \sum_m N_{\delta m}(F)u^m$; Newton recursion, `effectiveDivisorCount_newton`).
-/

open Finset TauCeti TauCeti.AlgebraicGeometry

namespace ModularFormsKB.Milne

universe u u' v v'

section PS

open PowerSeries in
lemma xd_eq (a N : ℕ → ℚ) (h : ∀ n : ℕ, (n : ℚ) * a n = ∑ j ∈ range n, N (j + 1) * a (n - 1 - j)) :
    X * derivative (PowerSeries.mk a) = PowerSeries.mk a * PowerSeries.mk (fun n => if n = 0 then 0 else N n) := by
  ext n
  rcases n with _ | n
  · simp [PowerSeries.coeff_mul]
  · rw [coeff_succ_X_mul, coeff_derivative, PowerSeries.coeff_mul]
    rw [← Finset.Nat.sum_antidiagonal_swap, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ']
    simp only [Prod.swap, PowerSeries.coeff_mk, Nat.succ_ne_zero, ite_false, if_true, mul_zero, add_zero]
    have := h (n + 1)
    push_cast at this
    rw [mul_comm, this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, Nat.add_sub_add_right]

open PowerSeries in
lemma ps_uniq (G H M : PowerSeries ℚ) (hM : coeff 0 M = 0) (h0 : coeff 0 G = coeff 0 H)
    (hG : X * derivative G = G * M) (hH : X * derivative H = H * M) : G = H := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · exact h0
    · have e1 := congrArg (coeff (n + 1)) hG
      have e2 := congrArg (coeff (n + 1)) hH
      rw [coeff_succ_X_mul, coeff_derivative] at e1 e2
      rw [coeff_mul] at e1 e2
      have : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), coeff p.1 G * coeff p.2 M =
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), coeff p.1 H * coeff p.2 M := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        by_cases hp2 : p.2 = 0
        · rw [hp2, hM]; simp
        · rw [ih p.1 (by omega)]
      rw [this, ← e2] at e1
      have hne : ((n : ℚ) + 1) ≠ 0 := by positivity
      exact mul_right_cancel₀ hne e1

lemma sum_reindex (δ m : ℕ) (hδ : 0 < δ) (a N : ℕ → ℚ)
    (hN : ∀ n, ¬ δ ∣ n → N n = 0) :
    ∑ j ∈ range (δ * m), N (j + 1) * a (δ * m - 1 - j) =
      ∑ i ∈ range m, N (δ * (i + 1)) * a (δ * (m - 1 - i)) := by
  have hsub : ∑ j ∈ (range m).image (fun i => δ * i + δ - 1), N (j + 1) * a (δ * m - 1 - j) =
      ∑ j ∈ range (δ * m), N (j + 1) * a (δ * m - 1 - j) := by
    refine Finset.sum_subset ?_ ?_
    · intro j hj
      simp only [Finset.mem_image, Finset.mem_range] at hj ⊢
      obtain ⟨i, hi, rfl⟩ := hj
      obtain ⟨t, rfl⟩ : ∃ t, m = i + 1 + t := ⟨m - i - 1, by omega⟩
      have : δ * (i + 1 + t) = δ * i + δ + δ * t := by ring
      rw [this]
      omega
    · intro j hj hj'
      by_cases hd : δ ∣ j + 1
      · exfalso
        apply hj'
        obtain ⟨c, hc⟩ := hd
        have hc0 : c ≠ 0 := by rintro rfl; simp at hc
        simp only [Finset.mem_image, Finset.mem_range]
        refine ⟨c - 1, ?_, ?_⟩
        · have hj1 := Finset.mem_range.mp hj
          have : δ * c ≤ δ * m := by omega
          have := Nat.le_of_mul_le_mul_left this hδ
          omega
        · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
          have : δ * (c' + 1) = δ * c' + δ := by ring
          simp only [Nat.add_sub_cancel]
          omega
      · rw [hN _ hd, zero_mul]
  rw [← hsub, Finset.sum_image]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.mp hi
    obtain ⟨t, rfl⟩ : ∃ t, m = i + 1 + t := ⟨m - i - 1, by omega⟩
    have e1 : δ * i + δ - 1 + 1 = δ * (i + 1) := by
      have : δ * (i + 1) = δ * i + δ := by ring
      omega
    have e2 : δ * (i + 1 + t) - 1 - (δ * i + δ - 1) = δ * (i + 1 + t - 1 - i) := by
      have h3 : i + 1 + t - 1 - i = t := by omega
      have : δ * (i + 1 + t) = δ * i + δ + δ * t := by ring
      rw [h3]; omega
    rw [e1, e2]
  · intro i _ j _ hij
    simp only at hij
    have : δ * i = δ * j := by omega
    exact Nat.eq_of_mul_eq_mul_left hδ this

end PS

section Extension

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
  [Field k] [Field k'] [Field F] [Field F'] [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F']
  [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F'] [Finite k] [FiniteDimensional k k']

/-- $N_m(F \cdot k') = N_{[k':k]\,m}(F)$. -/
theorem curvePointCount_constantCompositum (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (m : ℕ) (hm : 1 ≤ m) :
    curvePointCount k' F' m = curvePointCount k F (Module.finrank k k' * m) := by
  have : Finite k' := Module.finite_of_finite k
  have hF' : IsFunctionField k' F' := IsFunctionField.of_constantCompositum_eq_top (k := k) hF h
  have hex' : IsIntegrallyClosedIn k' F' := IsIntegrallyClosedIn.of_constantCompositum_eq_top (k := k) hex h
  obtain ⟨F'', k'', hfd, hfr, hc⟩ := exists_constantCompositum_finrank_eq (k := k') (F := F') m hm
  have h1 := card_degree_one_constantCompositum (k := k') (F := F') (k' := k'') (F' := F'') hF' hex' hc
  let : Algebra k k'' := ((algebraMap k' k'').comp (algebraMap k k')).toAlgebra
  let : Algebra F F'' := ((algebraMap F' F'').comp (algebraMap F F')).toAlgebra
  let : Algebra k F'' := ((algebraMap F' F'').comp (algebraMap k F')).toAlgebra
  have i3 : IsScalarTower F F' F'' := IsScalarTower.of_algebraMap_eq fun c => rfl
  have i4 : IsScalarTower k k' k'' := IsScalarTower.of_algebraMap_eq fun c => rfl
  have i5 : IsScalarTower k k' F'' := IsScalarTower.of_algebraMap_eq fun c => by
    show algebraMap F' F'' (algebraMap k F' c) = algebraMap k' F'' (algebraMap k k' c)
    rw [IsScalarTower.algebraMap_apply k' F' F'' (algebraMap k k' c), ← IsScalarTower.algebraMap_apply k k' F']
  have i6 : IsScalarTower k k'' F'' := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k k' F'' c, IsScalarTower.algebraMap_apply k k' k'' c,
      ← IsScalarTower.algebraMap_apply k' k'' F'']
  have i7 : IsScalarTower k F F'' := IsScalarTower.of_algebraMap_eq fun c => by
    show algebraMap F' F'' (algebraMap k F' c) = algebraMap F' F'' (algebraMap F F' (algebraMap k F c))
    rw [← IsScalarTower.algebraMap_apply k F F']
  have : FiniteDimensional k' k'' := hfd
  have : FiniteDimensional k k'' := Module.Finite.trans k' k''
  have hcomp : constantCompositum F k'' F'' = ⊤ := by
    set C := constantCompositum F k'' F'' with hC
    have h1' : constantCompositum F k' F' ≤ C.comap (IsScalarTower.toAlgHom F F' F'') := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨c, rfl⟩
      show algebraMap F' F'' (algebraMap k' F' c) ∈ C
      rw [← IsScalarTower.algebraMap_apply k' F' F'' c, IsScalarTower.algebraMap_apply k' k'' F'' c]
      exact algebraMap_mem_constantCompositum F k'' F'' _
    have h2 : ∀ y : F', algebraMap F' F'' y ∈ C := fun y => by
      have : y ∈ constantCompositum F k' F' := h ▸ IntermediateField.mem_top
      exact h1' this
    let D : IntermediateField F' F'' := { C.toSubfield with algebraMap_mem' := h2 }
    have h3 : constantCompositum F' k'' F'' ≤ D := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨c, rfl⟩
      exact algebraMap_mem_constantCompositum F k'' F'' _
    rw [hc] at h3
    exact eq_top_iff.mpr fun z _ => h3 IntermediateField.mem_top
  have h2 := card_degree_one_constantCompositum hF hex hcomp
  have hfin : Module.finrank k k'' = Module.finrank k k' * m := by
    rw [← hfr]; exact (Module.finrank_mul_finrank k k' k'').symm
  rw [hfin] at h2
  rw [hfr] at h1
  exact h1.symm.trans h2

/-- $Z_{F\cdot k'}(u) = \bigl(\sum_m A_{\delta m}(F)\,u^m\bigr)^\delta$ for $[k':k] = \delta$, when $\delta$ divides every
place degree of $F$. -/
theorem zeta_constantCompositum_eq_pow (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (δ : ℕ) (hδk : Module.finrank k k' = δ)
    (hδ : ∀ P : Place k F, δ ∣ P.degree) :
    PowerSeries.mk (fun n => (effectiveDivisorCount k' F' n : ℤ)) =
      (PowerSeries.mk (fun m => (effectiveDivisorCount k F (δ * m) : ℤ))) ^ δ := by
  have : Finite k' := Module.finite_of_finite k
  have hF' : IsFunctionField k' F' := IsFunctionField.of_constantCompositum_eq_top (k := k) hF h
  have hδpos : 0 < δ := hδk ▸ Module.finrank_pos
  obtain ⟨d, rfl⟩ : ∃ d, δ = d + 1 := ⟨δ - 1, by omega⟩
  apply PowerSeries.map_injective (Int.castRingHom ℚ) Int.cast_injective
  have emk : ∀ f : ℕ → ℤ, PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk f) =
      PowerSeries.mk (fun n => (f n : ℚ)) := fun f => by ext; simp
  rw [map_pow, emk, emk]
  simp only [Int.cast_natCast]
  set Z : PowerSeries ℚ := PowerSeries.mk (fun n => (effectiveDivisorCount k' F' n : ℚ)) with hZ
  set Y : PowerSeries ℚ := PowerSeries.mk (fun m => (effectiveDivisorCount k F ((d + 1) * m) : ℚ)) with hY
  set M : PowerSeries ℚ := PowerSeries.mk
    (fun n => if n = 0 then 0 else (curvePointCount k' F' n : ℚ)) with hM
  have hZd : PowerSeries.X * PowerSeries.derivative Z = Z * M := by
    refine xd_eq _ _ fun n => ?_
    exact_mod_cast effectiveDivisorCount_newton k' F' hF' n
  have hYd : PowerSeries.X * PowerSeries.derivative Y = Y * PowerSeries.mk
      (fun i => if i = 0 then 0 else (curvePointCount k F ((d + 1) * i) : ℚ) / (d + 1)) := by
    refine xd_eq (fun m => (effectiveDivisorCount k F ((d + 1) * m) : ℚ))
      (fun i => (curvePointCount k F ((d + 1) * i) : ℚ) / (d + 1)) fun m => ?_
    have hn := effectiveDivisorCount_newton k F hF ((d + 1) * m)
    have hn' : (((d + 1) * m : ℕ) : ℚ) * (effectiveDivisorCount k F ((d + 1) * m) : ℚ) =
        ∑ j ∈ range ((d + 1) * m), (curvePointCount k F (j + 1) : ℚ) *
          (effectiveDivisorCount k F ((d + 1) * m - 1 - j) : ℚ) := by exact_mod_cast hn
    rw [sum_reindex (d + 1) m hδpos (fun n => (effectiveDivisorCount k F n : ℚ))
      (fun n => (curvePointCount k F n : ℚ)) (fun n hn => by
        simp [curvePointCount_eq_zero_of_not_dvd (d + 1) hδ n hn])] at hn'
    have hd : ((d : ℚ) + 1) ≠ 0 := by positivity
    have e : ∑ i ∈ range m, (curvePointCount k F ((d + 1) * (i + 1)) : ℚ) / (d + 1) *
          (effectiveDivisorCount k F ((d + 1) * (m - 1 - i)) : ℚ) =
        (∑ i ∈ range m, (curvePointCount k F ((d + 1) * (i + 1)) : ℚ) *
          (effectiveDivisorCount k F ((d + 1) * (m - 1 - i)) : ℚ)) / (d + 1) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, ← hn', eq_div_iff hd]
    push_cast
    ring
  have hM0 : PowerSeries.coeff 0 M = 0 := by simp [hM]
  have hMd : ((d + 1 : ℕ) : PowerSeries ℚ) * PowerSeries.mk
      (fun i => if i = 0 then 0 else (curvePointCount k F ((d + 1) * i) : ℚ) / (d + 1)) = M := by
    have hc : ((d + 1 : ℕ) : PowerSeries ℚ) = PowerSeries.C ((d + 1 : ℕ) : ℚ) := by simp
    ext n
    rw [hc, PowerSeries.coeff_C_mul]
    by_cases hn : n = 0
    · simp [hM, hn]
    · have := curvePointCount_constantCompositum hF hex h n (Nat.pos_of_ne_zero hn)
      rw [hδk] at this
      simp only [hM, PowerSeries.coeff_mk, hn, if_false, this]
      have hd : ((d : ℚ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
  have hYpow : PowerSeries.X * PowerSeries.derivative (Y ^ (d + 1)) = Y ^ (d + 1) * M := by
    rw [Derivation.leibniz_pow]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
    rw [← hMd]
    calc PowerSeries.X * (((d + 1 : ℕ) : PowerSeries ℚ) * (Y ^ d * PowerSeries.derivative Y))
        = ((d + 1 : ℕ) : PowerSeries ℚ) * Y ^ d * (PowerSeries.X * PowerSeries.derivative Y) := by ring
      _ = _ := by rw [hYd]; ring
  refine ps_uniq Z (Y ^ (d + 1)) M hM0 ?_ hZd hYpow
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
  have h1 : PowerSeries.constantCoeff Z = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [hZ, effectiveDivisorCount_zero hF']
  have h2 : PowerSeries.constantCoeff Y = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [hY, effectiveDivisorCount_zero hF]
  rw [h1, h2, one_pow]

end Extension

end ModularFormsKB.Milne
