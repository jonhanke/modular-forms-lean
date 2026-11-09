import ModularFormsKB.Milne.Ch3.Uniformization

/-!
# Milne, Chapter 3: principal divisors (Abel–Jacobi) and the function field

A divisor on the torus `ℂ ⧸ Λ` is the divisor of an elliptic function exactly when its degree and its sum
vanish. Necessity is Proposition 3.1 (`degT_ellDiv`, `sumT_ellDiv`); sufficiency is proved here with functions
that are rational in `℘` and `℘'`: the divisors of `℘ - ℘(v)` and of the line functions show that
`x ↦ [(x) - (0)]` is an additive map to divisors modulo principal divisors.

Consequences: Milne's Theorem 3.8 (`prescribedDivisorStatement`) and Proposition 3.11, first part
(`ellipticFunctionFieldStatement`).
-/

open Complex Filter Topology Set PeriodPair

namespace ModularFormsKB.Milne

noncomputable section

variable {L : PeriodPair}

/-! ### Functions rational in `℘` and `℘'` -/

variable (L) in
/-- The value `P(℘(z), ℘'(z))` of a polynomial in two variables. -/
def evalWP (P : MvPolynomial (Fin 2) ℂ) (z : ℂ) : ℂ := MvPolynomial.eval ![℘[L] z, ℘'[L] z] P

theorem meromorphicOn_evalWP (P : MvPolynomial (Fin 2) ℂ) : MeromorphicOn (evalWP L P) univ := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have e : evalWP L (MvPolynomial.C a) = fun _ ↦ a := by funext z; simp [evalWP]
    exact fun z _ ↦ by rw [e]; exact MeromorphicAt.const a z
  | add p q hp hq =>
    have e : evalWP L (p + q) = evalWP L p + evalWP L q := by funext z; simp [evalWP]
    exact fun z hz ↦ by rw [e]; exact (hp z hz).add (hq z hz)
  | mul_X p i hp =>
    intro z hz
    have hX : MeromorphicAt (fun z ↦ ![℘[L] z, ℘'[L] z] i) z := by
      fin_cases i
      · simpa using L.meromorphic_weierstrassP z
      · simpa using L.meromorphic_derivWeierstrassP z
    have e : evalWP L (p * MvPolynomial.X i) = evalWP L p * fun z ↦ ![℘[L] z, ℘'[L] z] i := by
      funext z; simp [evalWP]
    rw [e]; exact (hp z hz).mul hX

theorem not_eventually_zero_iff_ne_top {f : ℂ → ℂ} (hf : MeromorphicOn f univ) :
    ¬ (∀ᶠ z in codiscrete ℂ, f z = 0) ↔ ∀ z, meromorphicOrderAt f z ≠ ⊤ := by
  have := (meromorphicOn_univ.1 hf).exists_meromorphicOrderAt_eq_top_iff_eventually_zero
  constructor
  · intro h z hz; exact h (this.1 ⟨z, hz⟩)
  · intro h hev; obtain ⟨z, hz⟩ := this.2 hev; exact h z hz

theorem not_eventually_zero_mul {f g : ℂ → ℂ} (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ)
    (hf0 : ¬ (∀ᶠ z in codiscrete ℂ, f z = 0)) (hg0 : ¬ (∀ᶠ z in codiscrete ℂ, g z = 0)) :
    ¬ (∀ᶠ z in codiscrete ℂ, f z * g z = 0) := by
  rw [not_eventually_zero_iff_ne_top hf] at hf0
  rw [not_eventually_zero_iff_ne_top hg] at hg0
  rw [not_eventually_zero_iff_ne_top (f := fun z ↦ f z * g z) (fun z hz ↦ (hf z hz).mul (hg z hz))]
  intro z
  rw [show (fun z ↦ f z * g z) = f * g from rfl, meromorphicOrderAt_mul (hf z (mem_univ z))
    (hg z (mem_univ z))]
  exact WithTop.add_ne_top.2 ⟨hf0 z, hg0 z⟩

variable (L) in
/-- `f` is a rational function of `℘` and `℘'` (off a discrete set), in the form of Proposition 3.11. -/
def IsRatWP (f : ℂ → ℂ) : Prop :=
  ∃ P Q : MvPolynomial (Fin 2) ℂ, ¬ (∀ᶠ z in codiscrete ℂ, evalWP L Q z = 0) ∧
    ∀ᶠ z in codiscrete ℂ, f z * evalWP L Q z = evalWP L P z

theorem isRatWP_poly (P : MvPolynomial (Fin 2) ℂ) : IsRatWP L (evalWP L P) := by
  refine ⟨P, 1, ?_, Eventually.of_forall fun z ↦ by simp [evalWP]⟩
  classical
  rw [not_eventually_zero_iff_ne_top (meromorphicOn_evalWP 1)]
  intro z
  have e : evalWP L 1 = fun _ ↦ (1 : ℂ) := by funext z; simp [evalWP]
  rw [e, meromorphicOrderAt_const]; simp

theorem IsRatWP.congr {f g : ℂ → ℂ} (hf : IsRatWP L f) (h : ∀ᶠ z in codiscrete ℂ, f z = g z) :
    IsRatWP L g := by
  obtain ⟨P, Q, hQ, hPQ⟩ := hf
  exact ⟨P, Q, hQ, by filter_upwards [hPQ, h] with z h1 h2; rw [← h2, h1]⟩

theorem IsRatWP.mul {f g : ℂ → ℂ} (hf : IsRatWP L f) (hg : IsRatWP L g) :
    IsRatWP L (fun z ↦ f z * g z) := by
  obtain ⟨P₁, Q₁, hQ₁, h₁⟩ := hf
  obtain ⟨P₂, Q₂, hQ₂, h₂⟩ := hg
  refine ⟨P₁ * P₂, Q₁ * Q₂, ?_, ?_⟩
  · have := not_eventually_zero_mul (meromorphicOn_evalWP Q₁) (meromorphicOn_evalWP Q₂) hQ₁ hQ₂
    simpa [evalWP] using this
  · filter_upwards [h₁, h₂] with z hz₁ hz₂
    simp only [evalWP, map_mul] at hz₁ hz₂ ⊢
    rw [← hz₁, ← hz₂]; ring

theorem IsRatWP.inv {f : ℂ → ℂ} (hf : IsRatWP L f) (hmf : MeromorphicOn f univ)
    (hf0 : ¬ (∀ᶠ z in codiscrete ℂ, f z = 0)) : IsRatWP L (fun z ↦ (f z)⁻¹) := by
  obtain ⟨P, Q, hQ, hPQ⟩ := hf
  refine ⟨Q, P, ?_, ?_⟩
  · intro hP
    apply not_eventually_zero_mul hmf (meromorphicOn_evalWP Q) hf0 hQ
    filter_upwards [hPQ, hP] with z h1 h2; rw [h1, h2]
  · have hne := hmf.codiscreteWithin_setOfPred_ne_zero
      (fun u _ ↦ (not_eventually_zero_iff_ne_top hmf).1 hf0 u)
    filter_upwards [hPQ, hne] with z h1 h2
    rw [← h1]; field_simp

theorem isRatWP_const (c : ℂ) : IsRatWP L (fun _ ↦ c) := by
  have := isRatWP_poly (L := L) (MvPolynomial.C c)
  exact this.congr (Eventually.of_forall fun z ↦ by simp [evalWP])

theorem isRatWP_weierstrassP_sub (c : ℂ) : IsRatWP L (fun z ↦ ℘[L] z - c) := by
  have := isRatWP_poly (L := L) (MvPolynomial.X 0 - MvPolynomial.C c)
  exact this.congr (Eventually.of_forall fun z ↦ by simp [evalWP])

theorem isRatWP_line (a b : ℂ) : IsRatWP L (fun z ↦ ℘'[L] z - a * ℘[L] z - b) := by
  have := isRatWP_poly (L := L) (MvPolynomial.X 1 - MvPolynomial.C a * MvPolynomial.X 0 -
    MvPolynomial.C b)
  exact this.congr (Eventually.of_forall fun z ↦ by simp [evalWP])

/-! ### Principal divisors -/

variable (L) in
/-- The group of divisors of elliptic functions rational in `℘, ℘'`. -/
def prinT : AddSubgroup (Torus L →₀ ℤ) where
  carrier := {D | ∃ f : ℂ → ℂ, ∃ hf : EllFun L f, IsRatWP L f ∧ ellDiv hf.1 = D}
  zero_mem' := ⟨fun _ ↦ 1, ellFun_const one_ne_zero, isRatWP_const 1, ellDiv_const one_ne_zero⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, hfr, rfl⟩ ⟨g, hg, hgr, rfl⟩
    exact ⟨_, hf.mul hg, hfr.mul hgr, ellDiv_mul hf hg⟩
  neg_mem' := by
    rintro _ ⟨f, hf, hfr, rfl⟩
    exact ⟨_, hf.inv, hfr.inv hf.1.1 hf.not_eventually_zero, ellDiv_inv hf⟩

theorem ellDiv_mem_prinT_weierstrassP_sub {v : ℂ} (hv : v ∉ L.lattice) :
    Finsupp.single (tmk L v) 1 + Finsupp.single (-tmk L v) 1 - Finsupp.single 0 2 ∈ prinT L :=
  ⟨_, ellFun_weierstrassP_sub (℘[L] v), isRatWP_weierstrassP_sub _, ellDiv_weierstrassP_sub hv⟩

/-- The basic relation `(x) + (y) - (x + y) - (0)` is principal. -/
def basicRel (x y : Torus L) : Torus L →₀ ℤ :=
  Finsupp.single x 1 + Finsupp.single y 1 - Finsupp.single (x + y) 1 - Finsupp.single 0 1

theorem basicRel_mem_generic {p q : ℂ} (hp : p ∉ L.lattice) (hq : q ∉ L.lattice) (hpq : p + q ∉ L.lattice)
    (h1 : tmk L p ≠ tmk L q) (h2 : tmk L p ≠ -tmk L q) : basicRel (tmk L p) (tmk L q) ∈ prinT L := by
  have hne : ℘[L] p ≠ ℘[L] q := fun h ↦ by
    rcases tmk_eq_or_eq_neg_of_weierstrassP_eq hp hq h with h | h
    · exact h1 h
    · exact h2 h
  set a := (℘'[L] p - ℘'[L] q) / (℘[L] p - ℘[L] q)
  set b := ℘'[L] p - a * ℘[L] p
  have hd : ℘[L] p - ℘[L] q ≠ 0 := sub_ne_zero.2 hne
  have hap : ℘'[L] p = a * ℘[L] p + b := by simp only [b]; ring
  have haq : ℘'[L] q = a * ℘[L] q + b := by simp only [b, a]; field_simp; ring
  have hl := ellDiv_line hp hq h1 hap haq
  have hv := ellDiv_mem_prinT_weierstrassP_sub (L := L) hpq
  have hline : Finsupp.single (tmk L p) 1 + Finsupp.single (tmk L q) 1 +
      Finsupp.single (-tmk L p - tmk L q) 1 - Finsupp.single 0 3 ∈ prinT L :=
    ⟨_, ellFun_line a b, isRatWP_line a b, hl⟩
  have := (prinT L).sub_mem hline hv
  convert this using 1
  simp only [basicRel, tmk_add]
  have h3 : (Finsupp.single (0 : Torus L) (3 : ℤ)) = Finsupp.single 0 2 + Finsupp.single 0 1 := by
    rw [← Finsupp.single_add]; norm_num
  rw [h3, show -tmk L p - tmk L q = -(tmk L p + tmk L q) by abel]
  abel

theorem exists_avoid {C : Set ℂ} (hC : C.Countable) : ∃ z : ℂ, z ∉ C :=
  (hC.dense_compl ℝ).nonempty

theorem countable_lattice : (L.lattice : Set ℂ).Countable := by
  have : (L.lattice : Set ℂ) = Set.range (fun p : ℤ × ℤ ↦ (p.1 : ℂ) * L.ω₁ + p.2 * L.ω₂) := by
    ext z; simp only [SetLike.mem_coe, L.mem_lattice, mem_range, Prod.exists]
  rw [this]; exact countable_range _

theorem basicRel_mem (x y : Torus L) : basicRel x y ∈ prinT L := by
  classical
  obtain ⟨p, rfl⟩ := tmk_surjective x
  obtain ⟨q, rfl⟩ := tmk_surjective y
  by_cases hp : p ∈ L.lattice
  · rw [tmk_eq_zero_iff.2 hp]
    convert zero_mem (prinT L) using 1; simp only [basicRel, zero_add]; abel
  by_cases hq : q ∈ L.lattice
  · rw [tmk_eq_zero_iff.2 hq]
    convert zero_mem (prinT L) using 1; simp only [basicRel, add_zero]; abel
  by_cases hpq : p + q ∈ L.lattice
  · have hqp : tmk L q = -tmk L p := by
      rw [← tmk_neg, tmk_eq_tmk_iff]; simpa [add_comm] using hpq
    have := ellDiv_mem_prinT_weierstrassP_sub (L := L) hp
    convert this using 1
    simp only [basicRel, hqp, add_neg_cancel]
    have h2 : (Finsupp.single (0 : Torus L) (2 : ℤ)) = Finsupp.single 0 1 + Finsupp.single 0 1 := by
      rw [← Finsupp.single_add]; norm_num
    rw [h2]; abel
  by_cases h1 : tmk L p = tmk L q
  · -- the doubling relation, from three generic relations
    rw [← h1]
    have h2p : p + p ∉ L.lattice := by
      intro h; apply hpq; rw [← tmk_eq_zero_iff] at h ⊢; rw [tmk_add, ← h1, ← tmk_add, h]
    -- choose `z` avoiding `Λ`, `±p + Λ` and the half lattice
    set C : Set ℂ := (L.lattice : Set ℂ) ∪ ((fun ω ↦ p + ω) '' L.lattice) ∪
      ((fun ω ↦ -p + ω) '' L.lattice) ∪ ((fun ω ↦ ω / 2) '' L.lattice)
    have hC : C.Countable :=
      ((countable_lattice.union (countable_lattice.image _)).union (countable_lattice.image _)).union
        (countable_lattice.image _)
    obtain ⟨z, hz⟩ := exists_avoid hC
    simp only [C, mem_union, mem_image, SetLike.mem_coe, not_or, not_exists, not_and] at hz
    obtain ⟨⟨⟨hzΛ, hzp⟩, hzm⟩, hz2⟩ := hz
    have hzp' : tmk L p ≠ tmk L z := fun h ↦ hzp (z - p) (by rw [← tmk_eq_tmk_iff]; exact h.symm)
      (by ring)
    have hzm' : tmk L p ≠ -tmk L z := fun h ↦ hzm (z + p) (by
      rw [← sub_neg_eq_add, ← tmk_eq_tmk_iff, tmk_neg, h, neg_neg]) (by ring)
    have hpz : p + z ∉ L.lattice := fun h ↦ hzm (z + p) (by rwa [add_comm]) (by ring)
    have hpmz : p + -z ∉ L.lattice := fun h ↦ hzp (z - p) (by
      have := L.lattice.neg_mem h; convert this using 1; ring) (by ring)
    have hnz : -z ∉ L.lattice := by simpa using hzΛ
    have hz2' : z + z ∉ L.lattice := fun h ↦ hz2 (z + z) h (by ring)
    have r1 := basicRel_mem_generic hp hzΛ hpz hzp' hzm'
    have r2 := basicRel_mem_generic (L := L) hp hnz hpmz (by rwa [tmk_neg]) (by rwa [tmk_neg, neg_neg])
    have r3 : basicRel (tmk L (p + z)) (tmk L (p + -z)) ∈ prinT L := by
      refine basicRel_mem_generic hpz hpmz (by convert h2p using 2; ring) ?_ ?_
      · intro h; apply hz2'; rw [← tmk_eq_zero_iff]
        have := congrArg (· - tmk L (p + -z)) h
        simp only [sub_self, tmk_add, tmk_neg] at this ⊢; rw [← this]; abel
      · intro h; apply h2p; rw [← tmk_eq_zero_iff]
        have := congrArg (· + tmk L (p + -z)) h
        simp only [neg_add_cancel, tmk_add, tmk_neg] at this ⊢; rw [← this]; abel
    have r4 := ellDiv_mem_prinT_weierstrassP_sub (L := L) hzΛ
    have := (prinT L).sub_mem ((prinT L).add_mem ((prinT L).add_mem r1 r2) r3) r4
    convert this using 1
    simp only [basicRel, tmk_add, tmk_neg]
    have h2 : (Finsupp.single (0 : Torus L) (2 : ℤ)) = Finsupp.single 0 1 + Finsupp.single 0 1 := by
      rw [← Finsupp.single_add]; norm_num
    rw [h2, show tmk L p + tmk L z + (tmk L p + -tmk L z) = tmk L p + tmk L p by abel]
    abel
  by_cases h2 : tmk L p = -tmk L q
  · exact absurd (by rw [← tmk_eq_zero_iff, tmk_add, h2, neg_add_cancel]) hpq
  exact basicRel_mem_generic hp hq hpq h1 h2

/-! ### The Abel–Jacobi map -/

variable (L) in
/-- `x ↦ [(x) - (0)]`, an additive map to divisors modulo principal divisors. -/
def abelJacobiInv : Torus L →+ (Torus L →₀ ℤ) ⧸ prinT L where
  toFun x := QuotientAddGroup.mk (Finsupp.single x 1 - Finsupp.single 0 1)
  map_zero' := by simp
  map_add' x y := by
    rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq]
    convert basicRel_mem x y using 1
    simp only [basicRel]; abel

theorem mk_eq_abelJacobiInv (D : Torus L →₀ ℤ) :
    (QuotientAddGroup.mk D : (Torus L →₀ ℤ) ⧸ prinT L) =
      abelJacobiInv L (sumT L D) + degT L D • QuotientAddGroup.mk (Finsupp.single 0 1) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE =>
    rw [QuotientAddGroup.mk_add, hD, hE, map_add, map_add, map_add, add_zsmul]; abel
  | single x n =>
    rw [sumT_single, degT_single, map_zsmul]
    simp only [abelJacobiInv, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_add]
    congr 1
    rw [smul_sub, sub_add_cancel, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- **Abel–Jacobi**: a divisor of degree zero and sum zero is the divisor of an elliptic function rational in
`℘` and `℘'`. -/
theorem mem_prinT_of_degT_sumT {D : Torus L →₀ ℤ} (hd : degT L D = 0) (hs : sumT L D = 0) :
    D ∈ prinT L := by
  have := mk_eq_abelJacobiInv D
  rw [hd, hs, map_zero, zero_zsmul, add_zero] at this
  exact (QuotientAddGroup.eq_zero_iff D).1 this

/-! ### Theorem 3.8 and Proposition 3.11 -/

theorem ellFun_of_not_eventually_zero {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f)
    (h0 : ¬ (∀ᶠ z in codiscrete ℂ, f z = 0)) : EllFun L f :=
  ⟨hf, (not_eventually_zero_iff_ne_top hf.1).1 h0⟩

/-- Every elliptic function is rational in `℘`, `℘'`. -/
theorem isRatWP_of_isDoublyPeriodic {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f) : IsRatWP L f := by
  by_cases h0 : ∀ᶠ z in codiscrete ℂ, f z = 0
  · exact (isRatWP_const 0).congr (by filter_upwards [h0] with z hz; rw [hz])
  have hF := ellFun_of_not_eventually_zero hf h0
  obtain ⟨r, hr, hrr, hdiv⟩ := mem_prinT_of_degT_sumT (degT_ellDiv hf h0) (sumT_ellDiv hf h0)
  obtain ⟨c, -, hc⟩ := eq_const_mul_of_ellDiv_eq hr hF hdiv
  exact ((isRatWP_const c).mul hrr).congr (by filter_upwards [hc] with z hz; rw [hz])

/-- **Milne, Proposition 3.11** (first part): the field of elliptic functions is `ℂ(℘, ℘')`. -/
theorem ellipticFunctionFieldStatement : EllipticFunctionFieldStatement :=
  ⟨fun _ _ hf ↦ isRatWP_of_isDoublyPeriodic hf⟩

/-- **Milne, Theorem 3.8**: existence and uniqueness of an elliptic function with prescribed zeros and
poles. -/
theorem prescribedDivisorStatement : PrescribedDivisorStatement := by
  classical
  refine ⟨fun L n P Q _ _ hsum ↦ ?_⟩
  set D : Torus L →₀ ℤ :=
    (∑ j, Finsupp.single (tmk L (Q j)) 1) - ∑ i, Finsupp.single (tmk L (P i)) 1
  have hD : ∀ z : ℂ, D (tmk L z) =
      ((Finset.univ.filter fun j ↦ Q j - z ∈ L.lattice).card : ℤ) -
        ((Finset.univ.filter fun i ↦ P i - z ∈ L.lattice).card : ℤ) := by
    intro z
    simp only [D, Finsupp.sub_apply, Finsupp.finsetSum_apply, Finsupp.single_apply,
      tmk_eq_tmk_iff]
    rw [Finset.sum_boole, Finset.sum_boole]
  have hdeg : degT L D = 0 := by simp [D]
  have hsumD : sumT L D = 0 := by
    simp only [D, map_sub, map_sum, sumT_single, one_smul]
    have hs : ∀ s : Fin n → ℂ, ∑ x, tmk L (s x) = tmk L (∑ x, s x) := fun s ↦
      (map_sum (QuotientAddGroup.mk' L.lattice.toAddSubgroup) s Finset.univ).symm
    rw [hs, hs, ← tmk_sub, tmk_eq_zero_iff]
    have := L.lattice.neg_mem hsum
    simpa using this
  have hord : ∀ (f : ℂ → ℂ) (hf : EllFun L f), ellDiv hf.1 = D → ∀ z,
      meromorphicOrderAt f z = (((Finset.univ.filter fun j ↦ Q j - z ∈ L.lattice).card : ℤ) -
        ((Finset.univ.filter fun i ↦ P i - z ∈ L.lattice).card : ℤ) : ℤ) := by
    intro f hf h z
    rw [hf.ordZ_eq, ← ellDiv_tmk hf.1, h, hD]
  have hconv : ∀ (f : ℂ → ℂ), IsDoublyPeriodic L.lattice f → (∀ z, meromorphicOrderAt f z =
      ((((Finset.univ.filter fun j ↦ Q j - z ∈ L.lattice).card : ℤ) -
        ((Finset.univ.filter fun i ↦ P i - z ∈ L.lattice).card : ℤ) : ℤ) : WithTop ℤ)) →
      ∃ hf : EllFun L f, ellDiv hf.1 = D := by
    intro f hf h
    have hF : EllFun L f := ⟨hf, fun z ↦ by rw [h z]; exact WithTop.coe_ne_top⟩
    refine ⟨hF, ?_⟩
    ext x
    obtain ⟨z, rfl⟩ := tmk_surjective x
    rw [ellDiv_tmk, ordZ, h z, WithTop.untop₀_coe, hD]
  refine ⟨?_, ?_⟩
  · obtain ⟨f, hf, -, hfD⟩ := mem_prinT_of_degT_sumT hdeg hsumD
    refine ⟨f, hf.1, fun z ↦ ?_⟩
    rw [hord f hf hfD z]
  · intro f g hf hfo hg hgo
    obtain ⟨hF, hFD⟩ := hconv f hf (fun z ↦ hfo z)
    obtain ⟨hG, hGD⟩ := hconv g hg (fun z ↦ hgo z)
    exact eq_const_mul_of_ellDiv_eq hF hG (hFD.trans hGD.symm)

end

end ModularFormsKB.Milne
