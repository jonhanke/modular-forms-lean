/-
# Tunnell's forms: the $q$-series identities

With $\theta_{\mathrm{odd}}(\tau) = \theta(\tau) - \theta(4\tau) = \sum_{x \text{ odd}} q^{x^2}$ and
$\phi_8(\tau) = 2\theta(32\tau) - \theta(8\tau)$ we prove
$$\tfrac12\theta_{\mathrm{odd}}(\tau)\,\theta(a\tau)\,\phi_8(\tau) = \sum_{m \text{ odd}}
\Bigl(\#\{x^2 + a y^2 + 32 z^2 = m\} - \tfrac12\#\{x^2 + a y^2 + 8 z^2 = m\}\Bigr) q^m$$
for $a \in \{2, 4\}$ (more generally for even $a \ge 2$), whence `tunnellOdd_eq_theta` and `tunnellEven_eq_theta`.

The proof multiplies out the three theta series as a sum over $\mathbb Z^3$ (all norm-summable), groups the terms by the
value of the exponent, and identifies each fibre with the finite set counted by `repCount`. For odd $m$ every
representation has $x$ odd (the other two coefficients are even), and for even $m$ none does.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.TunnellTheta
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.Coefficients

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open Complex Tunnell
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- The $n$-th term $e^{2\pi i n^2 w}$ of $\theta(w)$. -/
private noncomputable def thTerm (w : ℂ) (n : ℤ) : ℂ := cexp (2 * π * I * (n : ℂ) ^ 2 * w)

private theorem thTerm_summable_norm {w : ℂ} (hw : 0 < w.im) : Summable fun n : ℤ ↦ ‖thTerm w n‖ := by
  have h := (summable_jacobiTheta₂_term_iff 0 (2 * w)).mpr (by simpa using hw)
  have h2 : (fun n : ℤ ↦ jacobiTheta₂_term n 0 (2 * w)) = thTerm w := by
    funext n
    simp only [jacobiTheta₂_term, thTerm]
    congr 1
    ring
  rw [h2] at h
  exact summable_norm_iff.mpr h

private theorem thTerm_hasSum {w : ℂ} (hw : 0 < w.im) : HasSum (thTerm w) (HalfIntegral.theta w) := by
  have h := (thTerm_summable_norm hw).of_norm.hasSum
  rw [HalfIntegral.theta_eq_tsum]
  exact h

private theorem oddTerm_hasSum {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun x : ℤ ↦ if Odd x then thTerm z x else 0)
      (HalfIntegral.theta z - HalfIntegral.theta (4 * z)) := by
  have h4 : 0 < (4 * z).im := by simp; linarith
  have h1 := thTerm_hasSum hz
  have h2 := thTerm_hasSum h4
  have hinj : Function.Injective (fun n : ℤ ↦ 2 * n) := fun a b h ↦ by simpa using h
  have h3 : HasSum (fun x : ℤ ↦ if Even x then thTerm z x else 0) (HalfIntegral.theta (4 * z)) := by
    rw [← hinj.hasSum_iff]
    · convert h2 using 1
      funext n
      have : Even (2 * n) := ⟨n, by ring⟩
      simp only [Function.comp, this, ite_true, thTerm]
      congr 1
      push_cast
      ring
    · intro x hx
      have : ¬ Even x := by
        rintro ⟨k, rfl⟩
        exact hx ⟨k, by ring⟩
      simp [this]
  convert h1.sub h3 using 1
  funext x
  by_cases h : Even x
  · simp [h, Int.not_odd_iff_even.mpr h]
  · have ho : Odd x := Int.not_even_iff_odd.mp h
    simp [h, ho]

/-- Fibre-sum lemma over any index type. -/
private theorem hasSum_fiber' {β : Type*} {f : β → ℂ} {a : ℂ} (h : HasSum f a) (N : β → ℕ) :
    HasSum (fun m : ℕ ↦ ∑' b : {x // N x = m}, f b) a := by
  have h1 := (Equiv.sigmaFiberEquiv N).hasSum_iff.mpr h
  exact h1.sigma fun m ↦ (h1.summable.sigma_factor m).hasSum

/-- The finite set of representations, as in `repCount`. -/
private def repSet (a b m : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (-(m : ℤ)) m ×ˢ Finset.Icc (-(m : ℤ)) m ×ˢ Finset.Icc (-(m : ℤ)) m).filter
    (fun v : ℤ × ℤ × ℤ ↦ v.1 ^ 2 + (a : ℤ) * v.2.1 ^ 2 + (b : ℤ) * v.2.2 ^ 2 = (m : ℤ))

private theorem repSet_card (a b m : ℕ) : (repSet a b m).card = repCount a b m := rfl

private theorem mem_repSet {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (m : ℕ) (p : ℤ × ℤ × ℤ) :
    p ∈ repSet a b m ↔ p.1 ^ 2 + (a : ℤ) * p.2.1 ^ 2 + (b : ℤ) * p.2.2 ^ 2 = (m : ℤ) := by
  unfold repSet
  rw [Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    obtain ⟨h1, h2, h3⟩ := mem_box_of_rep ha hb h
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨abs_le.mp h1, abs_le.mp h2, abs_le.mp h3⟩, h⟩

/-- The exponent map. -/
private def expo (a b : ℕ) (p : ℤ × ℤ × ℤ) : ℕ :=
  (p.1 ^ 2 + (a : ℤ) * p.2.1 ^ 2 + (b : ℤ) * p.2.2 ^ 2).toNat

private theorem expo_eq_iff (a b m : ℕ) (p : ℤ × ℤ × ℤ) :
    expo a b p = m ↔ p.1 ^ 2 + (a : ℤ) * p.2.1 ^ 2 + (b : ℤ) * p.2.2 ^ 2 = (m : ℤ) := by
  unfold expo
  have h0 : 0 ≤ p.1 ^ 2 + (a : ℤ) * p.2.1 ^ 2 + (b : ℤ) * p.2.2 ^ 2 := by positivity
  generalize p.1 ^ 2 + (a : ℤ) * p.2.1 ^ 2 + (b : ℤ) * p.2.2 ^ 2 = s at h0 ⊢
  omega

/-- Parity: with `a`, `b` even, `x` is odd iff `m` is odd. -/
private theorem odd_iff_of_rep {a b : ℕ} (ha : Even a) (hb : Even b) {x y w : ℤ} {m : ℕ}
    (h : x ^ 2 + (a : ℤ) * y ^ 2 + (b : ℤ) * w ^ 2 = m) : Odd x ↔ Odd m := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  have h' : x ^ 2 + 2 * ((a' : ℤ) * y ^ 2 + (b' : ℤ) * w ^ 2) = m := by
    push_cast at h
    linarith
  have hx : Odd x ↔ Odd (x ^ 2) := by
    rw [Int.odd_pow]; simp
  rw [hx, ← Int.odd_natCast, ← h']
  generalize (a' : ℤ) * y ^ 2 + (b' : ℤ) * w ^ 2 = t
  rw [Int.odd_iff, Int.odd_iff]
  omega

/-- The number of representations with `x` odd. -/
private def oddCount (a b m : ℕ) : ℕ := ((repSet a b m).filter (fun v ↦ Odd v.1)).card

private theorem oddCount_odd {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (ha' : Even a) (hb' : Even b) {m : ℕ}
    (hm : Odd m) : oddCount a b m = repCount a b m := by
  unfold oddCount
  rw [Finset.filter_true_of_mem, repSet_card]
  intro p hp
  rw [mem_repSet ha hb] at hp
  exact (odd_iff_of_rep ha' hb' hp).mpr hm

private theorem oddCount_even {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (ha' : Even a) (hb' : Even b) {m : ℕ}
    (hm : ¬ Odd m) : oddCount a b m = 0 := by
  unfold oddCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp ho
  rw [mem_repSet ha hb] at hp
  exact hm ((odd_iff_of_rep ha' hb' hp).mp ho)

/-- The triple product of theta series, as a series in `q`. -/
private theorem main_hasSum {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun m : ℕ ↦ (oddCount a b m : ℂ) * cexp (2 * π * I * (m : ℂ) * z))
      ((HalfIntegral.theta z - HalfIntegral.theta (4 * z)) *
        (HalfIntegral.theta ((a : ℂ) * z) * HalfIntegral.theta ((b : ℂ) * z))) := by
  have hza : 0 < ((a : ℂ) * z).im := by
    simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero]
    positivity
  have hzb : 0 < ((b : ℂ) * z).im := by
    simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero]
    positivity
  set u : ℤ → ℂ := fun x ↦ if Odd x then thTerm z x else 0 with hu
  have hun : Summable fun x : ℤ ↦ ‖u x‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun x ↦ ?_) (thTerm_summable_norm hz)
    by_cases h : Odd x <;> simp [hu, h]
  have hv := thTerm_summable_norm hza
  have hw := thTerm_summable_norm hzb
  have hvw : Summable fun p : ℤ × ℤ ↦ thTerm ((a : ℂ) * z) p.1 * thTerm ((b : ℂ) * z) p.2 :=
    summable_mul_of_summable_norm hv hw
  have hvwn : Summable fun p : ℤ × ℤ ↦ ‖thTerm ((a : ℂ) * z) p.1 * thTerm ((b : ℂ) * z) p.2‖ := by
    simpa only [norm_mul] using Summable.mul_norm hv hw
  have hvw' := (thTerm_hasSum hza).mul (thTerm_hasSum hzb) hvw
  have hall : Summable fun p : ℤ × ℤ × ℤ ↦
      u p.1 * (thTerm ((a : ℂ) * z) p.2.1 * thTerm ((b : ℂ) * z) p.2.2) := by
    exact summable_mul_of_summable_norm (f := u)
      (g := fun p : ℤ × ℤ ↦ thTerm ((a : ℂ) * z) p.1 * thTerm ((b : ℂ) * z) p.2) hun hvwn
  have hP := (oddTerm_hasSum hz).mul hvw' hall
  have hF := hasSum_fiber' hP (expo a b)
  convert hF using 1
  funext m
  symm
  have hset : ∑' q : {x : ℤ × ℤ × ℤ // expo a b x = m},
      u (q : ℤ × ℤ × ℤ).1 * (thTerm ((a : ℂ) * z) (q : ℤ × ℤ × ℤ).2.1 *
        thTerm ((b : ℂ) * z) (q : ℤ × ℤ × ℤ).2.2) =
      ∑ p ∈ repSet a b m, u p.1 * (thTerm ((a : ℂ) * z) p.2.1 * thTerm ((b : ℂ) * z) p.2.2) := by
    rw [← Finset.tsum_subtype (repSet a b m)
      (fun p : ℤ × ℤ × ℤ ↦ u p.1 * (thTerm ((a : ℂ) * z) p.2.1 * thTerm ((b : ℂ) * z) p.2.2))]
    exact (Equiv.subtypeEquivRight (fun p ↦ by
      rw [expo_eq_iff, mem_repSet ha hb])).tsum_eq
      (fun q : {x : ℤ × ℤ × ℤ // x ∈ repSet a b m} ↦
        u (q : ℤ × ℤ × ℤ).1 * (thTerm ((a : ℂ) * z) (q : ℤ × ℤ × ℤ).2.1 *
          thTerm ((b : ℂ) * z) (q : ℤ × ℤ × ℤ).2.2))
  refine hset.trans ?_
  have hterm : ∀ p ∈ repSet a b m,
      u p.1 * (thTerm ((a : ℂ) * z) p.2.1 * thTerm ((b : ℂ) * z) p.2.2) =
        if Odd p.1 then cexp (2 * π * I * (m : ℂ) * z) else 0 := by
    intro p hp
    rw [mem_repSet ha hb] at hp
    have hp' : (p.1 : ℂ) ^ 2 + (a : ℂ) * (p.2.1 : ℂ) ^ 2 + (b : ℂ) * (p.2.2 : ℂ) ^ 2 = (m : ℂ) := by
      exact_mod_cast hp
    by_cases ho : Odd p.1
    · simp only [hu, ho, ite_true, thTerm]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      linear_combination (2 * π * I * z) * hp'
    · simp [hu, ho]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- **The combination**: $\tfrac12\theta_{\mathrm{odd}}\,\theta(az)\,\phi_8$ has the coefficients
$B - A/2$ at odd $m$ and $0$ at even $m$, for even $a \ge 2$. -/
private theorem combo_hasSum {a : ℕ} (ha : 1 ≤ a) (ha' : Even a) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun m : ℕ ↦ (if Odd m then (repCount a 32 m : ℂ) - (repCount a 8 m : ℂ) / 2 else 0) *
        cexp (2 * π * I * (m : ℂ) * z))
      ((HalfIntegral.theta z - HalfIntegral.theta (4 * z)) * HalfIntegral.theta ((a : ℂ) * z) *
        (2 * HalfIntegral.theta (32 * z) - HalfIntegral.theta (8 * z)) / 2) := by
  have hB := main_hasSum (a := a) (b := 32) ha (by norm_num) hz
  have hA := main_hasSum (a := a) (b := 8) ha (by norm_num) hz
  have h := ((hB.mul_left 2).sub hA).div_const 2
  convert h using 1
  · funext m
    by_cases hm : Odd m
    · rw [oddCount_odd ha (by norm_num) ha' (by decide) hm,
        oddCount_odd ha (by norm_num) ha' (by decide) hm]
      simp only [hm, ite_true]
      ring
    · rw [oddCount_even ha (by norm_num) ha' (by decide) hm,
        oddCount_even ha (by norm_num) ha' (by decide) hm]
      simp [hm]
  · push_cast
    ring

/-- **Tunnell's odd form equals its theta product.** -/
theorem tunnellOdd_eq_theta : tunnellOdd = tunnellOddTheta := by
  funext τ
  have h := combo_hasSum (a := 2) (by norm_num) (by decide) (z := (τ : ℂ)) τ.im_pos
  simp only [Nat.cast_ofNat] at h
  have h' : HasSum (fun m : ℕ ↦ tunnellOddCoeff m * cexp (2 * π * I * (m : ℂ) * (τ : ℂ)))
      (tunnellOddTheta τ) := by
    unfold tunnellOddTheta thetaOddPart thetaSignPart
    convert h using 1
    funext m
    unfold tunnellOddCoeff tunnellA tunnellB
    rfl
  exact h'.tsum_eq

/-- **Tunnell's even form equals its theta product.** -/
theorem tunnellEven_eq_theta : tunnellEven = tunnellEvenTheta := by
  funext τ
  have h := combo_hasSum (a := 4) (by norm_num) (by decide) (z := (τ : ℂ)) τ.im_pos
  simp only [Nat.cast_ofNat] at h
  have h' : HasSum (fun m : ℕ ↦ tunnellEvenCoeff m * cexp (2 * π * I * (m : ℂ) * (τ : ℂ)))
      (tunnellEvenTheta τ) := by
    unfold tunnellEvenTheta thetaOddPart thetaSignPart
    convert h using 1
    funext m
    unfold tunnellEvenCoeff tunnellC tunnellD
    rw [Nat.mul_div_cancel_left m (by norm_num)]
  exact h'.tsum_eq

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
