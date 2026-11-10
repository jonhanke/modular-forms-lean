import ModularFormsKB.Miyake.Wave2B.EisensteinSeries
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import ModularFormsKB.Citation
/-!
# Miyake §7.1: the two spanning sets of Eisenstein series for $\Gamma(N)$ (Lemma 7.1.4)

Miyake, *Modular Forms* (Springer 1989), §7.1, pp. 271–272.

For $k \ge 3$ and $N \ge 1$, Miyake puts (7.1.20)
$\mathcal E^{(1)}_k(\Gamma(N)) = \langle E_k(z;\mu,\nu;N) \mid 0 \le \mu,\nu < N\rangle$ and (7.1.21)
$\mathcal E^{(2)}_k(\Gamma(N)) = \langle E_k(uz/v;\chi,\psi)\rangle$, where (7.1.22) $\chi$ and $\psi$
are Dirichlet characters mod $L$ and mod $M$ and (7.1.23) $u, v$ are positive integers with
$uL \mid N$ and $vM \mid N$. Lemma 7.1.4 says the two spans coincide. Both spans are taken in the
complex vector space of functions $\mathbb H \to \mathbb C$.
-/

open UpperHalfPlane ModularForm EisensteinSeries Complex
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave2B

/-- The point $uz/v$ of the upper half-plane, for positive integers $u$, $v$. -/
def scalePoint {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (z : ℍ) : ℍ :=
  ⟨(u : ℂ) * z / v, by
    have : ((u : ℂ) * z / v).im = (u : ℝ) * z.im / v := by
      simp [Complex.div_natCast_im]
    rw [this]
    exact div_pos (mul_pos (Nat.cast_pos.mpr hu) z.2) (Nat.cast_pos.mpr hv)⟩

lemma coe_scalePoint {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (z : ℍ) :
    (scalePoint hu hv z : ℂ) = (u : ℂ) * z / v :=
  rfl

/-- **Miyake (7.1.20).** $\mathcal E^{(1)}_k(\Gamma(N))$, spanned by the series
$E_k(z;\mu,\nu;N)$ over the residue pairs $(\mu,\nu)$ mod $N$. -/
@[kb "miyake1989" "(7.1.20), p. 271"]
def eisensteinSpanResidue (k : ℤ) (N : ℕ) : Submodule ℂ (ℍ → ℂ) :=
  Submodule.span ℂ (Set.range fun a : Fin 2 → ZMod N ↦ eisensteinResidue k N a)

/-- **Miyake (7.1.21)–(7.1.23).** $\mathcal E^{(2)}_k(\Gamma(N))$, spanned by the functions
$z \mapsto E_k(uz/v;\chi,\psi)$ with $\chi$ mod $L$, $\psi$ mod $M$ Dirichlet characters and
$u, v > 0$, $uL \mid N$, $vM \mid N$. -/
@[kb "miyake1989" "(7.1.21), p. 271"]
def eisensteinSpanChar (k : ℤ) (N : ℕ) : Submodule ℂ (ℍ → ℂ) :=
  Submodule.span ℂ {f | ∃ (L M u v : ℕ) (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (hu : 0 < u) (hv : 0 < v), u * L ∣ N ∧ v * M ∣ N ∧
      f = fun z ↦ eisensteinChar k χ ψ (scalePoint hu hv z)}

/-- Summability of weighted lattice terms for weights of norm at most one. -/
lemma summable_weight_term {k : ℤ} (hk : 3 ≤ k) (f : (Fin 2 → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (z : ℍ) : Summable fun x : Fin 2 → ℤ ↦ f x * eisSummand k x z := by
  refine Summable.of_norm_bounded (summable_norm_eisSummand hk z) (fun x ↦ ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hf x)

/-- The summand at $uz/v$ is $v^k$ times the summand at $z$ of the vector $(u x_0, v x_1)$. -/
lemma eisSummand_scalePoint (k : ℤ) {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (x : Fin 2 → ℤ) (z : ℍ) :
    eisSummand k x (scalePoint hu hv z) =
      (v : ℂ) ^ k * eisSummand k ![(u : ℤ) * x 0, (v : ℤ) * x 1] z := by
  have hv' : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  simp only [eisSummand, coe_scalePoint, Matrix.cons_val_zero, Matrix.cons_val_one]
  have : (x 0 : ℂ) * ((u : ℂ) * z / v) + x 1 =
      ((((u : ℤ) * x 0 : ℤ) : ℂ) * (z : ℂ) + (((v : ℤ) * x 1 : ℤ) : ℂ)) / v := by
    push_cast; field_simp
  rw [this, div_zpow, zpow_neg (v : ℂ) k, div_inv_eq_mul, mul_comm]

/-- Scaling the argument of a lattice series by $u/v$ reindexes the weight onto the sublattice
$u\mathbb Z \times v\mathbb Z$ and multiplies by $v^k$. -/
lemma latticeSeries_scalePoint (k : ℤ) {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (f : (Fin 2 → ℤ) → ℂ) (z : ℍ) :
    latticeSeries k f (scalePoint hu hv z) = (v : ℂ) ^ k *
      latticeSeries k (fun x ↦ if (u : ℤ) ∣ x 0 ∧ (v : ℤ) ∣ x 1 then
        f ![x 0 / u, x 1 / v] else 0) z := by
  have hu' : (u : ℤ) ≠ 0 := by exact_mod_cast hu.ne'
  have hv' : (v : ℤ) ≠ 0 := by exact_mod_cast hv.ne'
  set φ : (Fin 2 → ℤ) → (Fin 2 → ℤ) := fun x ↦ ![(u : ℤ) * x 0, (v : ℤ) * x 1] with hφ
  have hinj : Function.Injective φ := by
    intro x y h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [hφ, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    funext i; fin_cases i
    · exact mul_left_cancel₀ hu' h0
    · exact mul_left_cancel₀ hv' h1
  unfold latticeSeries
  simp_rw [eisSummand_scalePoint k hu hv]
  rw [← tsum_mul_left]
  rw [← hinj.tsum_eq (f := fun y ↦ (v : ℂ) ^ k * ((if (u : ℤ) ∣ y 0 ∧ (v : ℤ) ∣ y 1 then
    f ![y 0 / u, y 1 / v] else 0) * eisSummand k y z))]
  · refine tsum_congr fun x ↦ ?_
    have hx : (![(u : ℤ) * x 0 / u, (v : ℤ) * x 1 / v] : Fin 2 → ℤ) = x := by
      funext i; fin_cases i
      · simpa using Int.mul_ediv_cancel_left (x 0) hu'
      · simpa using Int.mul_ediv_cancel_left (x 1) hv'
    have hc : (u : ℤ) ∣ φ x 0 ∧ (v : ℤ) ∣ φ x 1 := by
      simp [hφ]
    simp only [hφ, Matrix.cons_val_zero, Matrix.cons_val_one] at hc ⊢
    rw [if_pos hc, hx]
    ring
  · intro y hy
    by_contra hne
    have hc : (u : ℤ) ∣ y 0 ∧ (v : ℤ) ∣ y 1 := by
      by_contra hc
      apply hy
      simp [hc]
    obtain ⟨⟨m, hm⟩, ⟨n, hn'⟩⟩ := hc
    refine hne ⟨![m, n], ?_⟩
    funext i; fin_cases i
    · simp [hφ, hm]
    · simp [hφ, hn']

/-- The weight of $E_k(uz/v;\chi,\psi)$ transported to $z$ (up to the factor $v^k$). -/
def scaledChar (u v : ℕ) {L M : ℕ} (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (x : Fin 2 → ℤ) : ℂ :=
  (if (u : ℤ) ∣ x 0 then χ ((x 0 / u : ℤ) : ZMod L) else 0) *
    (if (v : ℤ) ∣ x 1 then ψ ((x 1 / v : ℤ) : ZMod M) else 0)

lemma norm_scaledChar_le (u v : ℕ) {L M : ℕ} (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (x : Fin 2 → ℤ) : ‖scaledChar u v χ ψ x‖ ≤ 1 := by
  unfold scaledChar
  rw [norm_mul]
  have h1 : ‖if (u : ℤ) ∣ x 0 then χ ((x 0 / u : ℤ) : ZMod L) else 0‖ ≤ 1 := by
    split_ifs
    · exact DirichletCharacter.norm_le_one _ _
    · simp
  have h2 : ‖if (v : ℤ) ∣ x 1 then ψ ((x 1 / v : ℤ) : ZMod M) else 0‖ ≤ 1 := by
    split_ifs
    · exact DirichletCharacter.norm_le_one _ _
    · simp
  calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma eisensteinChar_scalePoint (k : ℤ) {L M u v : ℕ} (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (hu : 0 < u) (hv : 0 < v) (z : ℍ) :
    eisensteinChar k χ ψ (scalePoint hu hv z) = (v : ℂ) ^ k * latticeSeries k (scaledChar u v χ ψ) z := by
  unfold eisensteinChar
  rw [latticeSeries_scalePoint k hu hv]
  congr 2
  funext x
  by_cases h : (u : ℤ) ∣ x 0 ∧ (v : ℤ) ∣ x 1
  · simp [scaledChar, h.1, h.2]
  · rw [if_neg h]
    unfold scaledChar
    by_cases h1 : (u : ℤ) ∣ x 0
    · have h2 : ¬ (v : ℤ) ∣ x 1 := fun h2 ↦ h ⟨h1, h2⟩
      simp [h2]
    · simp [h1]

/-- The canonical integer lift of a residue pair mod $N$. -/
def liftZMod (N : ℕ) (a : Fin 2 → ZMod N) : Fin 2 → ℤ := fun i ↦ ((a i).val : ℤ)

/-- A lattice series whose weight factors through $\mathbb Z^2 \to (\mathbb Z/N)^2$ is a finite
combination of the series $E_k(z;a;N)$. -/
lemma latticeSeries_factor {k : ℤ} (hk : 3 ≤ k) (N : ℕ) [NeZero N] (W : (Fin 2 → ℤ) → ℂ)
    (hW : ∀ x y : Fin 2 → ℤ, ((↑) ∘ x : Fin 2 → ZMod N) = ((↑) ∘ y) → W x = W y) (z : ℍ) :
    latticeSeries k W z =
      ∑ a : Fin 2 → ZMod N, W (liftZMod N a) * eisensteinResidue k N a z := by
  have hlift : ∀ x : Fin 2 → ℤ,
      ((↑) ∘ liftZMod N ((↑) ∘ x) : Fin 2 → ZMod N) = (↑) ∘ x := by
    intro x; funext i; simp [liftZMod]
  have hind : ∀ a : Fin 2 → ZMod N, Summable fun x : Fin 2 → ℤ ↦
      (if ((↑) ∘ x : Fin 2 → ZMod N) = a then (1 : ℂ) else 0) * eisSummand k x z := fun a ↦
    summable_weight_term hk _ (fun x ↦ by split_ifs <;> simp) z
  unfold eisensteinResidue latticeSeries
  have h1 : ∀ x : Fin 2 → ℤ, W x * eisSummand k x z = ∑ a : Fin 2 → ZMod N,
      W (liftZMod N a) * ((if ((↑) ∘ x : Fin 2 → ZMod N) = a then (1 : ℂ) else 0) *
        eisSummand k x z) := by
    intro x
    rw [Finset.sum_eq_single ((↑) ∘ x)]
    · rw [if_pos rfl, hW x _ (hlift x).symm, one_mul]
    · intro a _ ha; rw [if_neg (Ne.symm ha)]; simp
    · simp
  rw [tsum_congr h1, Summable.tsum_finsetSum (fun a _ ↦ (hind a).mul_left _)]
  simp_rw [tsum_mul_left]

/-- Divisibility-twisted character values only depend on the residue mod $N$ when $uL \mid N$. -/
lemma ite_dvd_congr {N u L : ℕ} (hu : 0 < u) (huL : u * L ∣ N) (χ : DirichletCharacter ℂ L)
    (x y : ℤ) (h : (N : ℤ) ∣ y - x) :
    (if (u : ℤ) ∣ x then χ ((x / u : ℤ) : ZMod L) else 0) =
      (if (u : ℤ) ∣ y then χ ((y / u : ℤ) : ZMod L) else 0) := by
  have hu' : (u : ℤ) ≠ 0 := by exact_mod_cast hu.ne'
  have hd : (u : ℤ) ∣ y - x := dvd_trans (by exact_mod_cast dvd_trans (dvd_mul_right u L) huL) h
  by_cases hx : (u : ℤ) ∣ x
  · have hy : (u : ℤ) ∣ y := by simpa using dvd_add hd hx
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨m', rfl⟩ := hy
    rw [if_pos (dvd_mul_right _ _), if_pos (dvd_mul_right _ _), Int.mul_ediv_cancel_left _ hu',
      Int.mul_ediv_cancel_left _ hu']
    have h2 : ((u * L : ℕ) : ℤ) ∣ (u : ℤ) * (m' - m) := by
      have : (u : ℤ) * (m' - m) = u * m' - u * m := by ring
      rw [this]; exact dvd_trans (by exact_mod_cast huL) h
    push_cast at h2
    have h3 : ((m : ℤ) : ZMod L) = ((m' : ℤ) : ZMod L) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr ((mul_dvd_mul_iff_left hu').mp h2)
    rw [h3]
  · have hy : ¬ (u : ℤ) ∣ y := fun hy ↦ hx (by simpa using dvd_sub hy hd)
    rw [if_neg hx, if_neg hy]

/-- Miyake (7.1.25): the generators of $\mathcal E^{(2)}_k$ lie in $\mathcal E^{(1)}_k$. -/
lemma mem_span_residue_of_char {k : ℤ} (hk : 3 ≤ k) (N : ℕ) [NeZero N] {L M u v : ℕ}
    (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (hu : 0 < u) (hv : 0 < v)
    (huL : u * L ∣ N) (hvM : v * M ∣ N) :
    (fun z ↦ eisensteinChar k χ ψ (scalePoint hu hv z)) ∈ eisensteinSpanResidue k N := by
  have hW : ∀ x y : Fin 2 → ℤ, ((↑) ∘ x : Fin 2 → ZMod N) = ((↑) ∘ y) →
      scaledChar u v χ ψ x = scaledChar u v χ ψ y := by
    intro x y hxy
    have h0 : (N : ℤ) ∣ y 0 - x 0 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (congrFun hxy 0)
    have h1 : (N : ℤ) ∣ y 1 - x 1 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (congrFun hxy 1)
    unfold scaledChar
    rw [ite_dvd_congr hu huL χ _ _ h0, ite_dvd_congr hv hvM ψ _ _ h1]
  have : (fun z ↦ eisensteinChar k χ ψ (scalePoint hu hv z)) = ∑ a : Fin 2 → ZMod N,
      ((v : ℂ) ^ k * scaledChar u v χ ψ (liftZMod N a)) • eisensteinResidue k N a := by
    funext z
    rw [eisensteinChar_scalePoint, latticeSeries_factor hk N _ hW, Finset.mul_sum,
      Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp [mul_assoc]
  rw [this]
  exact Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/-- Linearity of lattice series over a finite double sum of bounded weights. -/
lemma latticeSeries_sum_sum {k : ℤ} (hk : 3 ≤ k) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → κ → ℂ) (G : ι → κ → (Fin 2 → ℤ) → ℂ) (hG : ∀ i j x, ‖G i j x‖ ≤ 1) (z : ℍ) :
    latticeSeries k (fun x ↦ ∑ i, ∑ j, c i j * G i j x) z =
      ∑ i, ∑ j, c i j * latticeSeries k (G i j) z := by
  unfold latticeSeries
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Summable.tsum_finsetSum (fun i _ ↦ summable_sum fun j _ ↦
    (summable_weight_term hk (G i j) (hG i j) z).mul_left (c i j))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Summable.tsum_finsetSum (fun j _ ↦
    (summable_weight_term hk (G i j) (hG i j) z).mul_left (c i j))]
  simp_rw [tsum_mul_left]

/-- For $N = uL$: $x \equiv u\mu' \pmod N$ for $x = um$ iff $m \equiv \mu' \pmod L$. -/
lemma coord_iff {N u L : ℕ} (huL : u * L = N) (hu : 0 < u) (μ' : ℕ) (m : ℤ) :
    ((((u : ℤ) * m : ℤ)) : ZMod N) = ((u * μ' : ℕ) : ZMod N) ↔
      (m : ZMod L) = (μ' : ZMod L) := by
  have hu' : (u : ℤ) ≠ 0 := by exact_mod_cast hu.ne'
  have e : ((u * μ' : ℕ) : ZMod N) = ((((u : ℤ) * (μ' : ℤ) : ℤ)) : ZMod N) := by
    push_cast; ring
  have e2 : (μ' : ZMod L) = ((μ' : ℤ) : ZMod L) := by simp
  rw [e, e2, ZMod.intCast_eq_intCast_iff_dvd_sub, ZMod.intCast_eq_intCast_iff_dvd_sub]
  have : (u : ℤ) * μ' - u * m = u * (μ' - m) := by ring
  rw [this, ← huL]
  push_cast
  exact mul_dvd_mul_iff_left hu'

/-- If $u \nmid x$ then $x \not\equiv u\mu' \pmod N$ (for $u \mid N$). -/
lemma coord_ne {N u L : ℕ} (huL : u * L = N) (μ' : ℕ) (x : ℤ) (hx : ¬ (u : ℤ) ∣ x) :
    (x : ZMod N) ≠ ((u * μ' : ℕ) : ZMod N) := by
  intro h
  have e : ((u * μ' : ℕ) : ZMod N) = ((((u : ℤ) * (μ' : ℤ) : ℤ)) : ZMod N) := by
    push_cast; ring
  rw [e, ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  apply hx
  have huN : (u : ℤ) ∣ N := by rw [← huL]; push_cast; exact dvd_mul_right _ _
  have h2 : (u : ℤ) ∣ (u : ℤ) * μ' - x := dvd_trans huN h
  simpa using dvd_sub (dvd_mul_right (u : ℤ) (μ' : ℤ)) h2

/-- One-coordinate orthogonality: the character sum picks out the residue class of $u\mu'$. -/
lemma coord_sum {N u L : ℕ} [NeZero L] (huL : u * L = N) (hu : 0 < u) (μ' : ℕ)
    (hcop : μ'.Coprime L) (x : ℤ) :
    ∑ χ : DirichletCharacter ℂ L, χ ((μ' : ZMod L)⁻¹) *
        (if (u : ℤ) ∣ x then χ ((x / u : ℤ) : ZMod L) else 0) =
      if (x : ZMod N) = ((u * μ' : ℕ) : ZMod N) then (L.totient : ℂ) else 0 := by
  have hu' : (u : ℤ) ≠ 0 := by exact_mod_cast hu.ne'
  have hunit : IsUnit (μ' : ZMod L) := (ZMod.isUnit_iff_coprime μ' L).mpr hcop
  by_cases hx : (u : ℤ) ∣ x
  · obtain ⟨m, rfl⟩ := hx
    have hdiv : ∀ m : ℤ, (u : ℤ) * m / u = m := fun m ↦ Int.mul_ediv_cancel_left m hu'
    simp only [hdiv, dvd_mul_right, ↓reduceIte]
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hunit]
    by_cases h : ((m : ℤ) : ZMod L) = μ'
    · rw [if_pos h.symm, if_pos ((coord_iff huL hu μ' m).mpr h)]
    · rw [if_neg (Ne.symm h), if_neg (fun h' ↦ h ((coord_iff huL hu μ' m).mp h'))]
  · rw [if_neg (coord_ne huL μ' x hx)]
    simp [hx]

/-- Two-coordinate orthogonality for the characters $\chi$ mod $L$, $\psi$ mod $M$. -/
lemma weight_identity {N u v L M : ℕ} [NeZero L] [NeZero M] (huL : u * L = N) (hvM : v * M = N)
    (hu : 0 < u) (hv : 0 < v) (μ' ν' : ℕ) (hcop : μ'.Coprime L) (hcop' : ν'.Coprime M)
    (a : Fin 2 → ZMod N) (ha : a = ![((u * μ' : ℕ) : ZMod N), ((v * ν' : ℕ) : ZMod N)])
    (x : Fin 2 → ℤ) :
    ∑ χ : DirichletCharacter ℂ L, ∑ ψ : DirichletCharacter ℂ M,
        (χ ((μ' : ZMod L)⁻¹) * ψ ((ν' : ZMod M)⁻¹)) * scaledChar u v χ ψ x =
      ((L.totient : ℂ) * (M.totient : ℂ)) *
        (if ((↑) ∘ x : Fin 2 → ZMod N) = a then (1 : ℂ) else 0) := by
  have key : ∑ χ : DirichletCharacter ℂ L, ∑ ψ : DirichletCharacter ℂ M,
        (χ ((μ' : ZMod L)⁻¹) * ψ ((ν' : ZMod M)⁻¹)) * scaledChar u v χ ψ x =
      (∑ χ : DirichletCharacter ℂ L, χ ((μ' : ZMod L)⁻¹) *
        (if (u : ℤ) ∣ x 0 then χ ((x 0 / u : ℤ) : ZMod L) else 0)) *
      (∑ ψ : DirichletCharacter ℂ M, ψ ((ν' : ZMod M)⁻¹) *
        (if (v : ℤ) ∣ x 1 then ψ ((x 1 / v : ℤ) : ZMod M) else 0)) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun χ _ ↦ Finset.sum_congr rfl fun ψ _ ↦ ?_
    unfold scaledChar
    ring
  have hiff : (((↑) ∘ x : Fin 2 → ZMod N) = a) ↔
      ((x 0 : ZMod N) = ((u * μ' : ℕ) : ZMod N) ∧ (x 1 : ZMod N) = ((v * ν' : ℕ) : ZMod N)) := by
    rw [ha, funext_iff, Fin.forall_fin_two]
    simp
  rw [key, coord_sum huL hu μ' hcop, coord_sum hvM hv ν' hcop']
  by_cases hp : (x 0 : ZMod N) = ((u * μ' : ℕ) : ZMod N) <;>
    by_cases hq : (x 1 : ZMod N) = ((v * ν' : ℕ) : ZMod N) <;>
      simp only [hiff, hp, hq, and_self, and_true, true_and, and_false, false_and, ↓reduceIte,
        mul_one, mul_zero, zero_mul]

/-- Every residue class $\mu$ mod $N$ is $u\mu'$ with $u \mid N$ and $\mu'$ coprime to $N/u$. -/
lemma exists_decomp (N : ℕ) [NeZero N] (μ : ℕ) :
    ∃ u L μ' : ℕ, 0 < u ∧ u * L = N ∧ μ = u * μ' ∧ μ'.Coprime L := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hu : 0 < Nat.gcd μ N := Nat.gcd_pos_of_pos_right _ hN
  exact ⟨Nat.gcd μ N, N / Nat.gcd μ N, μ / Nat.gcd μ N, hu,
    Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _),
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm, Nat.coprime_div_gcd_div_gcd hu⟩

/-- Miyake (7.1.26): the generators of $\mathcal E^{(1)}_k$ lie in $\mathcal E^{(2)}_k$. -/
lemma mem_span_char_of_residue {k : ℤ} (hk : 3 ≤ k) (N : ℕ) [NeZero N] (a : Fin 2 → ZMod N) :
    eisensteinResidue k N a ∈ eisensteinSpanChar k N := by
  obtain ⟨u, L, μ', hu, huL, hμ, hcop⟩ := exists_decomp N (a 0).val
  obtain ⟨v, M, ν', hv, hvM, hν, hcop'⟩ := exists_decomp N (a 1).val
  have hL : NeZero L := ⟨by rintro rfl; simp at huL; exact NeZero.ne N huL.symm⟩
  have hM : NeZero M := ⟨by rintro rfl; simp at hvM; exact NeZero.ne N hvM.symm⟩
  have ha : a = ![((u * μ' : ℕ) : ZMod N), ((v * ν' : ℕ) : ZMod N)] := by
    funext i; fin_cases i
    · simp [← hμ]
    · simp [← hν]
  have hφL : (L.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hL.out)).ne'
  have hφM : (M.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hM.out)).ne'
  have hvk : (v : ℂ) ^ k ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hv.ne')
  let c0 : DirichletCharacter ℂ L → DirichletCharacter ℂ M → ℂ := fun χ ψ ↦
    ((L.totient : ℂ) * (M.totient : ℂ))⁻¹ * (χ ((μ' : ZMod L)⁻¹) * ψ ((ν' : ZMod M)⁻¹))
  have hind : (fun x : Fin 2 → ℤ ↦ if ((↑) ∘ x : Fin 2 → ZMod N) = a then (1 : ℂ) else 0) =
      fun x ↦ ∑ χ : DirichletCharacter ℂ L, ∑ ψ : DirichletCharacter ℂ M,
        c0 χ ψ * scaledChar u v χ ψ x := by
    funext x
    have h := weight_identity huL hvM hu hv μ' ν' hcop hcop' a ha x
    have : ∑ χ : DirichletCharacter ℂ L, ∑ ψ : DirichletCharacter ℂ M,
        c0 χ ψ * scaledChar u v χ ψ x = ((L.totient : ℂ) * (M.totient : ℂ))⁻¹ *
        ∑ χ : DirichletCharacter ℂ L, ∑ ψ : DirichletCharacter ℂ M,
        (χ ((μ' : ZMod L)⁻¹) * ψ ((ν' : ZMod M)⁻¹)) * scaledChar u v χ ψ x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ψ _ ↦ ?_
      simp only [c0]; ring
    rw [this, h]
    field_simp
  have hfun : eisensteinResidue k N a = ∑ χ : DirichletCharacter ℂ L, ∑ ψ : DirichletCharacter ℂ M,
      (c0 χ ψ * ((v : ℂ) ^ k)⁻¹) • (fun z ↦ eisensteinChar k χ ψ (scalePoint hu hv z)) := by
    funext z
    unfold eisensteinResidue
    rw [hind, latticeSeries_sum_sum hk c0 (fun χ ψ ↦ scaledChar u v χ ψ)
      (fun χ ψ x ↦ norm_scaledChar_le u v χ ψ x) z]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, eisensteinChar_scalePoint]
    refine Finset.sum_congr rfl fun χ _ ↦ Finset.sum_congr rfl fun ψ _ ↦ ?_
    field_simp
  rw [hfun]
  refine Submodule.sum_mem _ fun χ _ ↦ Submodule.sum_mem _ fun ψ _ ↦ Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨L, M, u, v, χ, ψ, hu, hv, dvd_of_eq huL, dvd_of_eq hvM, rfl⟩

/-- **Miyake, Lemma 7.1.4.** For $k \ge 3$ and $N \ge 1$,
$\mathcal E^{(1)}_k(\Gamma(N)) = \mathcal E^{(2)}_k(\Gamma(N))$. -/
@[kb "miyake1989" "Lemma 7.1.4, p. 272"]
theorem eisensteinSpanResidue_eq_eisensteinSpanChar {k : ℤ} (hk : 3 ≤ k) (N : ℕ) [NeZero N] :
    eisensteinSpanResidue k N = eisensteinSpanChar k N := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    exact mem_span_char_of_residue hk N a
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨L, M, u, v, χ, ψ, hu, hv, h1, h2, rfl⟩
    exact mem_span_residue_of_char hk N χ ψ hu hv h1 h2

end ModularFormsKB.Miyake.Wave2B
