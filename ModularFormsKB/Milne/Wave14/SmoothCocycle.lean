import ModularFormsKB.Milne.Wave14.SmoothLog
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Smooth trivializations of a multiplicative cocycle: gluing along chains

Part of the proof of Milne, Remark 4.26. Let $\{U_i\}$ be open subsets of $\mathbb C$ and $G_{ij}$ a real-smooth
nowhere-vanishing multiplicative cocycle on the overlaps ($G_{ik} = G_{ij} G_{jk}$, `IsSmoothCocycle`). A *smooth
trivialization on $S$* (`SmoothTriv U G S`) is a family $s_i$, smooth and nowhere zero on $U_i \cap S$, with
$G_{ij} = s_i / s_j$ on $U_i \cap U_j \cap S$.

* On a set inside one $U_{i_0}$, $s_j = G_{j i_0}$ trivializes (`smoothTriv_of_subset`).
* Disjoint unions (`smoothTriv_iUnion`).
* **Two-set gluing** (`smoothTriv_union`): if $G$ is trivialized on open $V$ and $W$ and $V \cap W$ has smooth
  logarithms, the quotient $s^V_i / s^W_i = e^{\psi}$ is independent of $i$; splitting $\psi = a - b$ with a smooth
  cut-off $\rho$ ($a = \rho\psi$, $b = -(1 - \rho)\psi$) gives $s_i = s^V_i e^{-a} = s^W_i e^{-b}$ on $V \cup W$.
* **Chains** (`smoothTriv_chain`): if $T$ is cut by a smooth function $\ell$ into the pieces
  $P_k = T \cap \ell^{-1}(c + (k-1)h, c + (k+1)h)$, $k \in \mathbb Z$, each trivialized, with consecutive overlaps
  having smooth logarithms, then $G$ is trivialized on $T$: glue the even pieces to the odd ones with the cut-off
  $\rho = \sigma(-\cos(\pi(\ell - c)/h))$.
-/

open Set Topology Filter
open scoped ContDiff

noncomputable section

namespace ModularFormsKB.Milne.Wave14

variable {ι : Type*} (U : ι → Set ℂ) (G : ι → ι → ℂ → ℂ)

/-- A real-smooth nowhere-vanishing multiplicative cocycle on an open cover. -/
structure IsSmoothCocycle : Prop where
  isOpen : ∀ i, IsOpen (U i)
  smooth : ∀ i j, ContDiffOn ℝ ∞ (G i j) (U i ∩ U j)
  ne_zero : ∀ i j, ∀ x ∈ U i ∩ U j, G i j x ≠ 0
  mul : ∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k, G i k x = G i j x * G j k x

/-- A smooth trivialization of the cocycle `G` on `S`. -/
def SmoothTriv (S : Set ℂ) : Prop :=
  ∃ s : ι → ℂ → ℂ, (∀ i, ContDiffOn ℝ ∞ (s i) (U i ∩ S)) ∧ (∀ i, ∀ x ∈ U i ∩ S, s i x ≠ 0) ∧
    ∀ i j, ∀ x ∈ U i ∩ U j ∩ S, G i j x = s i x / s j x

variable {U G}

theorem SmoothTriv.mono {S S' : Set ℂ} (h : SmoothTriv U G S) (hS : S' ⊆ S) : SmoothTriv U G S' := by
  obtain ⟨s, h1, h2, h3⟩ := h
  exact ⟨s, fun i ↦ (h1 i).mono (inter_subset_inter_right _ hS),
    fun i x hx ↦ h2 i x ⟨hx.1, hS hx.2⟩, fun i j x hx ↦ h3 i j x ⟨hx.1, hS hx.2⟩⟩

/-- On a subset of one member of the cover, `s_j = G_{j i₀}` trivializes `G`. -/
theorem smoothTriv_of_subset (hG : IsSmoothCocycle U G) {S : Set ℂ} {i₀ : ι} (hS : S ⊆ U i₀) :
    SmoothTriv U G S := by
  refine ⟨fun j ↦ G j i₀, fun j ↦ (hG.smooth j i₀).mono fun x hx ↦ ⟨hx.1, hS hx.2⟩,
    fun j x hx ↦ hG.ne_zero j i₀ x ⟨hx.1, hS hx.2⟩, fun i j x hx ↦ ?_⟩
  show G i j x = G i i₀ x / G j i₀ x
  have hx0 : x ∈ U i ∩ U j ∩ U i₀ := ⟨⟨hx.1.1, hx.1.2⟩, hS hx.2⟩
  rw [hG.mul i j i₀ x hx0, mul_div_cancel_right₀ _ (hG.ne_zero j i₀ x ⟨hx.1.2, hS hx.2⟩)]

/-- A union of pairwise disjoint open sets on which `G` is trivialized. -/
theorem smoothTriv_iUnion {κ : Type*} {S : κ → Set ℂ} (hSo : ∀ k, IsOpen (S k))
    (hd : Pairwise (Function.onFun Disjoint S)) (hT : ∀ k, SmoothTriv U G (S k)) (hU : ∀ i, IsOpen (U i)) :
    SmoothTriv U G (⋃ k, S k) := by
  choose s hs1 hs2 hs3 using hT
  classical
  let t : ι → ℂ → ℂ := fun i x ↦ if h : ∃ k, x ∈ S k then s h.choose i x else 1
  have ht : ∀ k i, ∀ x ∈ S k, t i x = s k i x := by
    intro k i x hx
    have h : ∃ k, x ∈ S k := ⟨k, hx⟩
    have hk : h.choose = k := by
      by_contra hne
      exact (hd hne).le_bot ⟨h.choose_spec, hx⟩
    simp only [t, dif_pos h, hk]
  refine ⟨t, fun i ↦ ?_, fun i x hx ↦ ?_, fun i j x hx ↦ ?_⟩
  · refine contDiffOn_of_locally_contDiffOn fun x hx ↦ ?_
    obtain ⟨k, hk⟩ := mem_iUnion.1 hx.2
    refine ⟨U i ∩ S k, (hU i).inter (hSo k), ⟨hx.1, hk⟩, ?_⟩
    have : U i ∩ (⋃ k, S k) ∩ (U i ∩ S k) = U i ∩ S k :=
      inter_eq_right.2 fun y hy ↦ ⟨hy.1, mem_iUnion.2 ⟨k, hy.2⟩⟩
    rw [this]
    exact (hs1 k i).congr fun y hy ↦ ht k i y hy.2
  · obtain ⟨k, hk⟩ := mem_iUnion.1 hx.2
    rw [ht k i x hk]
    exact hs2 k i x ⟨hx.1, hk⟩
  · obtain ⟨k, hk⟩ := mem_iUnion.1 hx.2
    rw [ht k i x hk, ht k j x hk]
    exact hs3 k i j x ⟨hx.1, hk⟩

/-- **Two-set gluing.** If `G` is trivialized on open sets `V` and `W` covered by the `U i`, `V ∩ W` has smooth
logarithms, and `ρ` is a smooth cut-off on `V ∪ W` vanishing near the points of `V ∖ W` and equal to `1` near the
points of `W ∖ V`, then `G` is trivialized on `V ∪ W`. -/
theorem smoothTriv_union (hG : IsSmoothCocycle U G) {V W : Set ℂ} (hV : IsOpen V) (hW : IsOpen W)
    (hcov : ∀ x ∈ V ∪ W, ∃ i, x ∈ U i) (hTV : SmoothTriv U G V) (hTW : SmoothTriv U G W)
    (hL : HasSmoothLog (V ∩ W)) {ρ : ℂ → ℝ} (hρ : ContDiffOn ℝ ∞ ρ (V ∪ W))
    (hρ0 : ∀ x ∈ V, x ∉ W → ρ =ᶠ[𝓝 x] 0) (hρ1 : ∀ x ∈ W, x ∉ V → ρ =ᶠ[𝓝 x] 1) :
    SmoothTriv U G (V ∪ W) := by
  obtain ⟨sV, hV1, hV2, hV3⟩ := hTV
  obtain ⟨sW, hW1, hW2, hW3⟩ := hTW
  classical
  -- the quotient `sV i / sW i`, independent of `i`
  let φ : ℂ → ℂ := fun x ↦ if h : ∃ i, x ∈ U i then sV h.choose x / sW h.choose x else 1
  have hφi : ∀ i, ∀ x ∈ U i ∩ (V ∩ W), φ x = sV i x / sW i x := by
    intro i x hx
    have h : ∃ i, x ∈ U i := ⟨i, hx.1⟩
    simp only [φ, dif_pos h]
    set j := h.choose
    have hj : x ∈ U j := h.choose_spec
    have e1 := hV3 j i x ⟨⟨hj, hx.1⟩, hx.2.1⟩
    have e2 := hW3 j i x ⟨⟨hj, hx.1⟩, hx.2.2⟩
    have a1 := hV2 i x ⟨hx.1, hx.2.1⟩
    have a2 := hW2 i x ⟨hx.1, hx.2.2⟩
    have a3 := hW2 j x ⟨hj, hx.2.2⟩
    have e := e1.symm.trans e2
    rw [div_eq_div_iff a1 a2] at e
    rw [div_eq_div_iff a3 a2]
    linear_combination e
  have hφs : ContDiffOn ℝ ∞ φ (V ∩ W) := by
    refine contDiffOn_of_locally_contDiffOn fun x hx ↦ ?_
    obtain ⟨i, hi⟩ := hcov x (Or.inl hx.1)
    refine ⟨U i, hG.isOpen i, hi, ?_⟩
    have hs : V ∩ W ∩ U i = U i ∩ (V ∩ W) := inter_comm _ _
    rw [hs]
    refine ContDiffOn.congr (contDiffOn_div' ((hV1 i).mono ?_) ((hW1 i).mono ?_) ?_) (hφi i)
    · exact fun y hy ↦ ⟨hy.1, hy.2.1⟩
    · exact fun y hy ↦ ⟨hy.1, hy.2.2⟩
    · exact fun y hy ↦ hW2 i y ⟨hy.1, hy.2.2⟩
  have hφ0 : ∀ x ∈ V ∩ W, φ x ≠ 0 := by
    intro x hx
    obtain ⟨i, hi⟩ := hcov x (Or.inl hx.1)
    rw [hφi i x ⟨hi, hx⟩]
    exact div_ne_zero (hV2 i x ⟨hi, hx.1⟩) (hW2 i x ⟨hi, hx.2⟩)
  obtain ⟨ψ, hψs, hψe⟩ := hL φ hφs hφ0
  -- the splitting `ψ = a - b`
  let a : ℂ → ℂ := fun x ↦ if x ∈ W then (ρ x : ℂ) * ψ x else 0
  let b : ℂ → ℂ := fun x ↦ if x ∈ V then -(1 - (ρ x : ℂ)) * ψ x else 0
  have hρc : ContDiffOn ℝ ∞ (fun x ↦ (ρ x : ℂ)) (V ∪ W) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hρ
  have ha : ContDiffOn ℝ ∞ a V := by
    intro x hx
    by_cases hxW : x ∈ W
    · have hn : V ∩ W ∈ 𝓝 x := (hV.inter hW).mem_nhds ⟨hx, hxW⟩
      have hev : a =ᶠ[𝓝 x] fun y ↦ (ρ y : ℂ) * ψ y := by
        filter_upwards [hW.mem_nhds hxW] with y hy
        simp only [a, if_pos hy]
      refine (ContDiffAt.contDiffWithinAt ?_).congr_of_eventuallyEq
        (hev.filter_mono nhdsWithin_le_nhds) hev.eq_of_nhds
      exact ((hρc.mono (inter_subset_left.trans subset_union_left)).mul hψs).contDiffAt hn
    · have hev : a =ᶠ[𝓝 x] fun _ ↦ 0 := by
        filter_upwards [hρ0 x hx hxW] with y hy
        by_cases hyW : y ∈ W
        · simp [a, if_pos hyW, hy]
        · simp [a, if_neg hyW]
      exact (contDiffAt_const.contDiffWithinAt).congr_of_eventuallyEq
        (hev.filter_mono nhdsWithin_le_nhds) hev.eq_of_nhds
  have hb : ContDiffOn ℝ ∞ b W := by
    intro x hx
    by_cases hxV : x ∈ V
    · have hn : V ∩ W ∈ 𝓝 x := (hV.inter hW).mem_nhds ⟨hxV, hx⟩
      have hev : b =ᶠ[𝓝 x] fun y ↦ -(1 - (ρ y : ℂ)) * ψ y := by
        filter_upwards [hV.mem_nhds hxV] with y hy
        simp only [b, if_pos hy]
      refine (ContDiffAt.contDiffWithinAt ?_).congr_of_eventuallyEq
        (hev.filter_mono nhdsWithin_le_nhds) hev.eq_of_nhds
      exact (((contDiffOn_const.sub (hρc.mono (inter_subset_left.trans subset_union_left))).neg).mul hψs).contDiffAt hn
    · have hev : b =ᶠ[𝓝 x] fun _ ↦ 0 := by
        filter_upwards [hρ1 x hx hxV] with y hy
        by_cases hyV : y ∈ V
        · simp [b, if_pos hyV, hy]
        · simp [b, if_neg hyV]
      exact (contDiffAt_const.contDiffWithinAt).congr_of_eventuallyEq
        (hev.filter_mono nhdsWithin_le_nhds) hev.eq_of_nhds
  have hab : ∀ x ∈ V ∩ W, ψ x - a x = -b x := by
    intro x hx
    simp only [a, b, if_pos hx.1, if_pos hx.2]
    ring
  -- the glued trivialization
  let s : ι → ℂ → ℂ := fun i x ↦
    if x ∈ V then sV i x * Complex.exp (-a x) else sW i x * Complex.exp (-b x)
  have hsV : ∀ i, ∀ x ∈ V, s i x = sV i x * Complex.exp (-a x) := fun i x hx ↦ if_pos hx
  have hsW : ∀ i, ∀ x ∈ U i ∩ W, s i x = sW i x * Complex.exp (-b x) := by
    intro i x hx
    by_cases hxV : x ∈ V
    · rw [hsV i x hxV]
      have hφx := hφi i x ⟨hx.1, hxV, hx.2⟩
      have hsVx : sV i x = sW i x * Complex.exp (ψ x) := by
        rw [← hψe x ⟨hxV, hx.2⟩, hφx]
        field_simp [hW2 i x hx]
      rw [hsVx, mul_assoc, ← Complex.exp_add, ← sub_eq_add_neg, hab x ⟨hxV, hx.2⟩]
    · exact if_neg hxV
  have hexpa : ContDiffOn ℝ ∞ (fun x ↦ Complex.exp (-a x)) V :=
    ((Complex.contDiff_exp : ContDiff ℂ ∞ Complex.exp).restrict_scalars ℝ).comp_contDiffOn ha.neg
  have hexpb : ContDiffOn ℝ ∞ (fun x ↦ Complex.exp (-b x)) W :=
    ((Complex.contDiff_exp : ContDiff ℂ ∞ Complex.exp).restrict_scalars ℝ).comp_contDiffOn hb.neg
  refine ⟨s, fun i ↦ ?_, fun i x hx ↦ ?_, fun i j x hx ↦ ?_⟩
  · refine contDiffOn_of_locally_contDiffOn fun x hx ↦ ?_
    by_cases hxV : x ∈ V
    · refine ⟨U i ∩ V, (hG.isOpen i).inter hV, ⟨hx.1, hxV⟩, ?_⟩
      have : U i ∩ (V ∪ W) ∩ (U i ∩ V) = U i ∩ V := by
        ext y; simp only [mem_inter_iff, mem_union]; tauto
      rw [this]
      exact ((hV1 i).mul (hexpa.mono inter_subset_right)).congr fun y hy ↦ hsV i y hy.2
    · have hxW : x ∈ W := hx.2.resolve_left hxV
      refine ⟨U i ∩ W, (hG.isOpen i).inter hW, ⟨hx.1, hxW⟩, ?_⟩
      have : U i ∩ (V ∪ W) ∩ (U i ∩ W) = U i ∩ W := by
        ext y; simp only [mem_inter_iff, mem_union]; tauto
      rw [this]
      exact ((hW1 i).mul (hexpb.mono inter_subset_right)).congr fun y hy ↦ hsW i y hy
  · by_cases hxV : x ∈ V
    · rw [hsV i x hxV]
      exact mul_ne_zero (hV2 i x ⟨hx.1, hxV⟩) (Complex.exp_ne_zero _)
    · have hxW : x ∈ W := hx.2.resolve_left hxV
      rw [hsW i x ⟨hx.1, hxW⟩]
      exact mul_ne_zero (hW2 i x ⟨hx.1, hxW⟩) (Complex.exp_ne_zero _)
  · by_cases hxV : x ∈ V
    · rw [hsV i x hxV, hsV j x hxV, mul_div_mul_right _ _ (Complex.exp_ne_zero _)]
      exact hV3 i j x ⟨hx.1, hxV⟩
    · have hxW : x ∈ W := hx.2.resolve_left hxV
      rw [hsW i x ⟨hx.1.1, hxW⟩, hsW j x ⟨hx.1.2, hxW⟩,
        mul_div_mul_right _ _ (Complex.exp_ne_zero _)]
      exact hW3 i j x ⟨hx.1, hxW⟩

/-- The `k`-th piece of a chain: `T ∩ ℓ⁻¹(c + (k-1)h, c + (k+1)h)`. -/
def chainPiece (T : Set ℂ) (ℓ : ℂ → ℝ) (c h : ℝ) (k : ℤ) : Set ℂ :=
  T ∩ ℓ ⁻¹' Ioo (c + (k - 1) * h) (c + (k + 1) * h)

theorem isOpen_chainPiece {T : Set ℂ} (hT : IsOpen T) {ℓ : ℂ → ℝ} (hℓ : ContinuousOn ℓ T) (c h : ℝ)
    (k : ℤ) : IsOpen (chainPiece T ℓ c h k) :=
  hℓ.isOpen_inter_preimage hT isOpen_Ioo

/-- Every value lies in one of the intervals `(c + (k-1)h, c + (k+1)h)`. -/
theorem exists_mem_chain_interval (c h t : ℝ) (hh : 0 < h) :
    ∃ k : ℤ, t ∈ Ioo (c + (k - 1) * h) (c + (k + 1) * h) := by
  refine ⟨⌊(t - c) / h⌋, ?_, ?_⟩
  · have h1 := Int.lt_floor_add_one ((t - c) / h)
    have h2 := Int.floor_le ((t - c) / h)
    rcases h2.lt_or_eq with h2 | h2
    · have : ((⌊(t - c) / h⌋ : ℝ) - 1) * h < (t - c) / h * h := by nlinarith
      rw [div_mul_cancel₀ _ hh.ne'] at this
      linarith
    · have : ((⌊(t - c) / h⌋ : ℝ) - 1) * h < (t - c) / h * h := by rw [h2]; nlinarith
      rw [div_mul_cancel₀ _ hh.ne'] at this
      linarith
  · have h1 := Int.lt_floor_add_one ((t - c) / h)
    have : (t - c) / h * h < ((⌊(t - c) / h⌋ : ℝ) + 1) * h := by nlinarith
    rw [div_mul_cancel₀ _ hh.ne'] at this
    linarith

/-- Two of the intervals meet only when their indices differ by at most one. -/
theorem chain_interval_index {c h t : ℝ} (hh : 0 < h) {k l : ℤ}
    (hk : t ∈ Ioo (c + (k - 1) * h) (c + (k + 1) * h)) (hl : t ∈ Ioo (c + (l - 1) * h) (c + (l + 1) * h)) :
    |((k : ℝ) - l)| < 2 := by
  obtain ⟨hk1, hk2⟩ := hk
  obtain ⟨hl1, hl2⟩ := hl
  rw [abs_lt]
  constructor
  · by_contra hc
    push Not at hc
    have : ((k : ℝ) + 1) * h ≤ ((l : ℝ) - 1) * h := by nlinarith
    linarith
  · by_contra hc
    push Not at hc
    have : ((l : ℝ) + 1) * h ≤ ((k : ℝ) - 1) * h := by nlinarith
    linarith

theorem chain_index_eq {k l : ℤ} (h : |((k : ℝ) - l)| < 2) : k = l - 1 ∨ k = l ∨ k = l + 1 := by
  have h' : |k - l| < 2 := by exact_mod_cast h
  rw [abs_lt] at h'
  omega

/-- The smooth cut-off of a chain: `0` near points lying only in even pieces, `1` near points lying only in odd
pieces. -/
def chainCutoff (ℓ : ℂ → ℝ) (c h : ℝ) (x : ℂ) : ℝ :=
  Real.smoothTransition (-Real.cos (Real.pi * (ℓ x - c) / h) + 1 / 2)

theorem chainCutoff_contDiffOn {T : Set ℂ} {ℓ : ℂ → ℝ} (hℓ : ContDiffOn ℝ ∞ ℓ T) (c h : ℝ) :
    ContDiffOn ℝ ∞ (chainCutoff ℓ c h) T := by
  unfold chainCutoff
  refine (Real.smoothTransition.contDiff (n := ⊤)).comp_contDiffOn ?_
  refine ContDiffOn.add ?_ contDiffOn_const
  refine ContDiffOn.neg ?_
  refine Real.contDiff_cos.comp_contDiffOn ?_
  exact ((contDiffOn_const.mul (hℓ.sub contDiffOn_const)).div_const _)

/-- Near a point where `cos (π (ℓ - c)/h) = ε` with `ε = ±1`, the cut-off is locally constant. -/
theorem chainCutoff_eventually {T : Set ℂ} (hT : IsOpen T) {ℓ : ℂ → ℝ} (hℓ : ContinuousOn ℓ T) (c h : ℝ)
    {x : ℂ} (hx : x ∈ T) (m : ℤ) (hm : ℓ x = c + m * h) (hh : 0 < h) :
    chainCutoff ℓ c h =ᶠ[𝓝 x] fun _ ↦ if Even m then 0 else 1 := by
  have hcx : Real.cos (Real.pi * (ℓ x - c) / h) = if Even m then 1 else -1 := by
    rw [hm, show Real.pi * (c + m * h - c) / h = m * Real.pi by rw [add_sub_cancel_left]; field_simp]
    rcases Int.even_or_odd m with he | ho
    · rw [if_pos he]
      obtain ⟨r, rfl⟩ := he
      push_cast
      rw [show ((r : ℝ) + r) * Real.pi = (r : ℤ) * (2 * Real.pi) by ring]
      exact Real.cos_int_mul_two_pi r
    · rw [if_neg (Int.not_even_iff_odd.2 ho)]
      obtain ⟨r, rfl⟩ := ho
      push_cast
      rw [show (2 * (r : ℝ) + 1) * Real.pi = Real.pi + (r : ℤ) * (2 * Real.pi) by ring,
        Real.cos_add_int_mul_two_pi, Real.cos_pi]
  have hcont : ContinuousAt (fun y ↦ Real.cos (Real.pi * (ℓ y - c) / h)) x :=
    Real.continuous_cos.continuousAt.comp
      ((continuousAt_const.mul ((hℓ.continuousAt (hT.mem_nhds hx)).sub continuousAt_const)).div_const _)
  rcases Int.even_or_odd m with he | ho
  · have hev : ∀ᶠ y in 𝓝 x, 1 / 2 < Real.cos (Real.pi * (ℓ y - c) / h) := by
      refine hcont.eventually (lt_mem_nhds ?_)
      beta_reduce
      rw [hcx, if_pos he]; norm_num
    filter_upwards [hev] with y hy
    rw [if_pos he]
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · have hev : ∀ᶠ y in 𝓝 x, Real.cos (Real.pi * (ℓ y - c) / h) < -1 / 2 := by
      refine hcont.eventually (gt_mem_nhds ?_)
      beta_reduce
      rw [hcx, if_neg (Int.not_even_iff_odd.2 ho)]; norm_num
    filter_upwards [hev] with y hy
    rw [if_neg (Int.not_even_iff_odd.2 ho)]
    exact Real.smoothTransition.one_of_one_le (by linarith)

theorem mem_Ioo_cast {t c h : ℝ} {a b : ℤ} (hab : a = b)
    (ht : t ∈ Ioo (c + ((a : ℝ) - 1) * h) (c + ((a : ℝ) + 1) * h)) :
    t ∈ Ioo (c + ((b : ℝ) - 1) * h) (c + ((b : ℝ) + 1) * h) := by
  subst hab; exact ht

/-- A point of a piece `P_m` that lies in neither neighbouring piece sits at the centre `ℓ = c + m h`. -/
theorem eq_center_of_not_mem {c h t : ℝ} (hh : 0 < h) {m : ℤ}
    (hm : t ∈ Ioo (c + (m - 1) * h) (c + (m + 1) * h))
    (h1 : t ∉ Ioo (c + ((m - 1 : ℤ) - 1) * h) (c + ((m - 1 : ℤ) + 1) * h))
    (h2 : t ∉ Ioo (c + ((m + 1 : ℤ) - 1) * h) (c + ((m + 1 : ℤ) + 1) * h)) : t = c + m * h := by
  push_cast at h1 h2
  simp only [mem_Ioo, not_and_or, not_lt] at h1 h2 hm
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · nlinarith
  · nlinarith
  · linarith
  · nlinarith

/-- **Chains.** If `T` (open, covered by the `U i`) is cut by a smooth `ℓ` into the pieces `chainPiece T ℓ c h k`,
each trivialized, with consecutive overlaps having smooth logarithms, then `G` is trivialized on `T`. -/
theorem smoothTriv_chain (hG : IsSmoothCocycle U G) {T : Set ℂ} (hT : IsOpen T)
    (hcov : ∀ x ∈ T, ∃ i, x ∈ U i) {ℓ : ℂ → ℝ} (hℓ : ContDiffOn ℝ ∞ ℓ T) {c h : ℝ} (hh : 0 < h)
    (hP : ∀ k, SmoothTriv U G (chainPiece T ℓ c h k))
    (hL : ∀ k, HasSmoothLog (chainPiece T ℓ c h k ∩ chainPiece T ℓ c h (k + 1))) :
    SmoothTriv U G T := by
  have hℓc : ContinuousOn ℓ T := hℓ.continuousOn
  set P := chainPiece T ℓ c h
  have hPo : ∀ k, IsOpen (P k) := isOpen_chainPiece hT hℓc c h
  have hPT : ∀ k, P k ⊆ T := fun k ↦ inter_subset_left
  -- pieces with indices differing by two or more are disjoint
  have hdisj : ∀ k l : ℤ, (k - l ≥ 2 ∨ l - k ≥ 2) → Disjoint (P k) (P l) := by
    intro k l hkl
    rw [Set.disjoint_left]
    intro x hk hl
    have := chain_index_eq (chain_interval_index hh hk.2 hl.2)
    omega
  let V := ⋃ m : ℤ, P (2 * m)
  let W := ⋃ m : ℤ, P (2 * m + 1)
  have hVo : IsOpen V := isOpen_iUnion fun m ↦ hPo _
  have hWo : IsOpen W := isOpen_iUnion fun m ↦ hPo _
  have hVW : V ∪ W = T := by
    apply subset_antisymm
    · exact union_subset (iUnion_subset fun m ↦ hPT _) (iUnion_subset fun m ↦ hPT _)
    · intro x hx
      obtain ⟨k, hk⟩ := exists_mem_chain_interval c h (ℓ x) hh
      rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
      · exact Or.inl (mem_iUnion.2 ⟨m, hx, hk⟩)
      · exact Or.inr (mem_iUnion.2 ⟨m, hx, hk⟩)
  have hTV : SmoothTriv U G V := smoothTriv_iUnion (fun m ↦ hPo _)
    (fun m m' hne ↦ hdisj _ _ (by omega)) (fun m ↦ hP _) hG.isOpen
  have hTW : SmoothTriv U G W := smoothTriv_iUnion (fun m ↦ hPo _)
    (fun m m' hne ↦ hdisj _ _ (by omega)) (fun m ↦ hP _) hG.isOpen
  -- the overlap is the disjoint union of the consecutive overlaps
  have hint : V ∩ W = ⋃ k : ℤ, P k ∩ P (k + 1) := by
    apply subset_antisymm
    · rintro x ⟨hxV, hxW⟩
      obtain ⟨m, hm⟩ := mem_iUnion.1 hxV
      obtain ⟨m', hm'⟩ := mem_iUnion.1 hxW
      have := chain_index_eq (chain_interval_index hh hm.2 hm'.2)
      rcases this with h1 | h1 | h1
      · exact mem_iUnion.2 ⟨2 * m, hm, by rw [show 2 * m + 1 = 2 * m' + 1 by omega]; exact hm'⟩
      · omega
      · exact mem_iUnion.2 ⟨2 * m' + 1, hm', by rw [← h1]; exact hm⟩
    · intro x hx
      obtain ⟨k, hk1, hk2⟩ := mem_iUnion.1 hx
      rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
      · exact ⟨mem_iUnion.2 ⟨m, hk1⟩, mem_iUnion.2 ⟨m, hk2⟩⟩
      · refine ⟨mem_iUnion.2 ⟨m + 1, ?_⟩, mem_iUnion.2 ⟨m, hk1⟩⟩
        convert hk2 using 2; ring
  have hLVW : HasSmoothLog (V ∩ W) := by
    rw [hint]
    refine hasSmoothLog_iUnion (fun k ↦ (hPo k).inter (hPo (k + 1))) ?_ hL
    intro k l hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · by_cases h2 : l = k + 1
      · subst h2
        exact Disjoint.mono inter_subset_left inter_subset_right (hdisj k (k + 1 + 1) (by omega))
      · exact Disjoint.mono inter_subset_left inter_subset_left (hdisj k l (by omega))
    · by_cases h2 : k = l + 1
      · subst h2
        exact Disjoint.mono inter_subset_right inter_subset_left (hdisj (l + 1 + 1) l (by omega))
      · exact Disjoint.mono inter_subset_left inter_subset_left (hdisj k l (by omega))
  have hρ := chainCutoff_contDiffOn hℓ c h
  rw [← hVW] at hρ hcov ⊢
  refine smoothTriv_union hG hVo hWo hcov hTV hTW hLVW hρ ?_ ?_
  · intro x hxV hxW
    obtain ⟨m, hm⟩ := mem_iUnion.1 hxV
    have hc : ℓ x = c + ((2 * m : ℤ) : ℝ) * h :=
      eq_center_of_not_mem hh hm.2
        (fun h1 ↦ hxW (mem_iUnion.2 ⟨m - 1, hm.1, mem_Ioo_cast (by ring) h1⟩))
        (fun h2 ↦ hxW (mem_iUnion.2 ⟨m, hm.1, mem_Ioo_cast (by ring) h2⟩))
    have := chainCutoff_eventually hT hℓc c h (hPT _ hm) (2 * m) hc hh
    simp only [even_two_mul, if_true] at this
    exact this
  · intro x hxW hxV
    obtain ⟨m, hm⟩ := mem_iUnion.1 hxW
    have hc : ℓ x = c + ((2 * m + 1 : ℤ) : ℝ) * h :=
      eq_center_of_not_mem hh hm.2
        (fun h1 ↦ hxV (mem_iUnion.2 ⟨m, hm.1, mem_Ioo_cast (by ring) h1⟩))
        (fun h2 ↦ hxV (mem_iUnion.2 ⟨m + 1, hm.1, mem_Ioo_cast (by ring) h2⟩))
    have := chainCutoff_eventually hT hℓc c h (hPT _ hm) (2 * m + 1) hc hh
    have hodd : ¬ Even (2 * m + 1) := by rw [Int.not_even_iff_odd]; exact odd_two_mul_add_one m
    simp only [hodd, if_false] at this
    exact this

end ModularFormsKB.Milne.Wave14
