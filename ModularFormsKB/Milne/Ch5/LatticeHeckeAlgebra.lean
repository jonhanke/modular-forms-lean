import ModularFormsKB.Milne.Ch5.LatticeHecke
import Mathlib.RingTheory.Adjoin.Basic
import ModularFormsKB.Miyake.HeckeAlgebras

/-!
# Milne, Chapter 5: the algebra of lattice Hecke operators (Corollaries 5.10, 5.11, Proposition 5.12)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf pp. 71–72.
Notation as in `LatticeHecke.lean`.

## Items
- Corollary 5.10 (`latticeT_mul`).
- Corollary 5.11 (`latticeHeckeAlgebra_comm`, `latticeTD_mem_latticeHeckeAlgebra`).
- Functions on lattices, p. 71: $T\cdot F$ (`latticeOpFun`), $R(n)\cdot F = n^{-2k}F$ (`latticeOpFun_latticeR`).
- Proposition 5.12 (`latticeOpFun_latticeT_isWeight`, `latticeOpFun_latticeT_mul`).
-/

open Finsupp

namespace ModularFormsKB.Milne

section General

variable {V : Type*} [AddCommGroup V]

lemma range_pair {α : Type*} (a b : α) : Set.range ![a, b] = {a, b} := by
  ext x; simp [eq_comm, or_comm]

/-- A `ℤ`-independent pair spans a subgroup with a basis of two elements. -/
lemma nonempty_basis_span_pair {ω₁ ω₂ : V} (h : LinearIndependent ℤ ![ω₁, ω₂]) :
    Nonempty (Module.Basis (Fin 2) ℤ (Submodule.span ℤ {ω₁, ω₂})) := by
  have : Submodule.span ℤ (Set.range ![ω₁, ω₂]) = Submodule.span ℤ {ω₁, ω₂} := by
    rw [range_pair]
  exact ⟨(Module.Basis.span h).map (LinearEquiv.ofEq _ _ this)⟩

/-- A subgroup with a basis of two elements is spanned by a `ℤ`-independent pair. -/
lemma exists_pair_of_basis {Λ : Submodule ℤ V} (h : Nonempty (Module.Basis (Fin 2) ℤ Λ)) :
    ∃ ω₁ ω₂ : V, LinearIndependent ℤ ![ω₁, ω₂] ∧ Λ = Submodule.span ℤ {ω₁, ω₂} := by
  obtain ⟨b⟩ := h
  have hv : ![((b 0 : Λ) : V), ((b 1 : Λ) : V)] = Λ.subtype ∘ b := by
    funext i; fin_cases i <;> rfl
  refine ⟨b 0, b 1, ?_, ?_⟩
  · rw [hv]
    exact b.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ)
  · have h1 : Submodule.map Λ.subtype (Submodule.span ℤ (Set.range b)) = Λ := by
      rw [b.span_eq, Submodule.map_subtype_top]
    rw [Submodule.map_span, ← Set.range_comp] at h1
    have h2 : Set.range (Λ.subtype ∘ b) = {((b 0 : Λ) : V), ((b 1 : Λ) : V)} := by
      rw [← hv, range_pair]
    rw [h2] at h1
    exact h1.symm

/-- Explicit form of `T(n)[Λ]` for `Λ = ℤω₁ + ℤω₂` (Remark 5.14). -/
lemma latticeT_span_pair {ω₁ ω₂ : V} (hli : LinearIndependent ℤ ![ω₁, ω₂]) {n : ℕ} (hn : 0 < n) :
    latticeT n (single (Submodule.span ℤ {ω₁, ω₂}) 1) =
      ∑ t ∈ hermiteTriples n,
        single (Submodule.span ℤ {(t.1 : ℤ) • ω₁ + (t.2.1 : ℤ) • ω₂, (t.2.2 : ℤ) • ω₂}) (1 : ℤ) := by
  have hb := bijOn_hermiteTriples_subOfIndex hli hn
  unfold latticeT
  rw [Finsupp.linearCombination_single, one_smul]
  rw [← finsum_mem_eq_of_bijOn _ hb (fun x _ ↦ rfl), finsum_mem_coe_finset]

/-- The triple sublattices are again spanned by independent pairs. -/
lemma triple_li {ω₁ ω₂ : V} (hli : LinearIndependent ℤ ![ω₁, ω₂]) {n : ℕ} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ hermiteTriples n) (hn : 0 < n) :
    LinearIndependent ℤ ![(t.1 : ℤ) • ω₁ + (t.2.1 : ℤ) • ω₂, (t.2.2 : ℤ) • ω₂] := by
  rw [mem_hermiteTriples] at ht
  have ha : 0 < t.1 := Nat.pos_of_ne_zero (by intro h; rw [h] at ht; omega)
  have hd : 0 < t.2.2 := Nat.pos_of_ne_zero (by intro h; rw [h] at ht; omega)
  rw [LinearIndependent.pair_iff] at hli ⊢
  intro s u h
  have h' : (s * t.1) • ω₁ + (s * t.2.1 + u * t.2.2) • ω₂ = 0 := by
    rw [← h]; simp only [smul_add, smul_smul, add_smul, mul_comm, Nat.cast_mul]; abel
  obtain ⟨h1, h2⟩ := hli _ _ h'
  have hs : s = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact h
    · exact absurd (by exact_mod_cast h) ha.ne'
  subst hs
  simp only [zero_mul, zero_add] at h2
  refine ⟨rfl, ?_⟩
  rcases mul_eq_zero.1 h2 with h | h
  · exact h
  · exact absurd (by exact_mod_cast h) hd.ne'

/-- Scaling a pair by a positive integer keeps independence. -/
lemma smul_li {ω₁ ω₂ : V} (hli : LinearIndependent ℤ ![ω₁, ω₂]) {c : ℕ} (hc : 0 < c) :
    LinearIndependent ℤ ![(c : ℤ) • ω₁, (c : ℤ) • ω₂] := by
  rw [LinearIndependent.pair_iff] at hli ⊢
  intro s u h
  have h' : (s * c) • ω₁ + (u * c) • ω₂ = 0 := by
    rw [← h]; simp only [smul_smul, mul_comm]
  obtain ⟨h1, h2⟩ := hli _ _ h'
  have hc' : (c : ℤ) ≠ 0 := by exact_mod_cast hc.ne'
  exact ⟨(mul_eq_zero.1 h1).resolve_right hc', (mul_eq_zero.1 h2).resolve_right hc'⟩

/-- `n[Λ]`: the operator `R(n)` on a generator. -/
lemma latticeR_single (n : ℕ) (Λ : Submodule ℤ V) :
    latticeR n (single Λ 1) = single (scaleSub (n : ℤ) Λ) 1 := by
  simp [latticeR]

lemma scaleSub_span_pair (c : ℤ) (ω₁ ω₂ : V) :
    scaleSub c (Submodule.span ℤ {ω₁, ω₂}) = Submodule.span ℤ {c • ω₁, c • ω₂} := by
  simp [scaleSub, Submodule.map_span, Set.image_pair]


lemma scaleSub_scaleSub (m n : ℤ) (Λ : Submodule ℤ V) : scaleSub m (scaleSub n Λ) = scaleSub (m * n) Λ := by
  unfold scaleSub
  rw [← Submodule.map_comp]
  congr 1
  ext x
  simp [mul_smul]

lemma scaleSub_one (Λ : Submodule ℤ V) : scaleSub 1 Λ = Λ := by
  simp [scaleSub]

/-- `R(1)` is the identity. -/
lemma latticeR_one (x : Submodule ℤ V →₀ ℤ) : latticeR 1 x = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single a b =>
    have : single a b = b • single a (1 : ℤ) := by simp
    rw [this, map_zsmul, latticeR_single]
    simp [scaleSub_one]

/-- `R(m n) = R(m) R(n)`. -/
lemma latticeR_mul (m n : ℕ) (x : Submodule ℤ V →₀ ℤ) : latticeR (m * n) x = latticeR m (latticeR n x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single a b =>
    have : single a b = b • single a (1 : ℤ) := by simp
    rw [this, map_zsmul, map_zsmul, map_zsmul, latticeR_single, latticeR_single, latticeR_single]
    simp [scaleSub_scaleSub]

/-- `T(1)` is the identity on generators. -/
lemma latticeT_one (Λ : Submodule ℤ V) : latticeT 1 (single Λ 1) = single Λ 1 := by
  unfold latticeT
  rw [Finsupp.linearCombination_single, one_smul]
  have : subOfIndex Λ 1 = {Λ} := by
    ext Λ'
    simp only [subOfIndex, Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [AddSubgroup.relIndex_eq_one]
    constructor
    · rintro ⟨h1, h2⟩
      exact le_antisymm h1 h2
    · rintro rfl
      exact ⟨le_rfl, le_rfl⟩
  rw [this, finsum_mem_singleton]

/-- `T(n)[cΛ] = R(c) T(n)[Λ]` for `Λ` of rank two. -/
lemma latticeT_scaleSub {ω₁ ω₂ : V} (hli : LinearIndependent ℤ ![ω₁, ω₂]) {c : ℕ} (hc : 0 < c) {n : ℕ}
    (hn : 0 < n) :
    latticeT n (single (scaleSub (c : ℤ) (Submodule.span ℤ {ω₁, ω₂})) 1) =
      latticeR c (latticeT n (single (Submodule.span ℤ {ω₁, ω₂}) 1)) := by
  rw [scaleSub_span_pair, latticeT_span_pair (smul_li hli hc) hn, latticeT_span_pair hli hn, map_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [latticeR_single, scaleSub_span_pair, smul_add, smul_comm (c : ℤ) (t.1 : ℤ),
    smul_comm (c : ℤ) (t.2.1 : ℤ), smul_comm (c : ℤ) (t.2.2 : ℤ)]

/-- The subgroup $D \subseteq$ `Submodule ℤ V →₀ ℤ` spanned by the $[\Lambda]$ with $\Lambda$ free of rank $2$; for
$V = \mathbb C$ it contains Milne's $D$ (spanned by the lattices) as a subgroup stable under all $T(n)$, $R(n)$. -/
noncomputable def latticeSpan (V : Type*) [AddCommGroup V] : Submodule ℤ (Submodule ℤ V →₀ ℤ) :=
  Submodule.span ℤ {x | ∃ Λ : Submodule ℤ V, Nonempty (Module.Basis (Fin 2) ℤ Λ) ∧ x = single Λ 1}

lemma single_mem_latticeSpan {Λ : Submodule ℤ V} (h : Nonempty (Module.Basis (Fin 2) ℤ Λ)) :
    single Λ (1 : ℤ) ∈ latticeSpan V :=
  Submodule.subset_span ⟨Λ, h, rfl⟩

/-- Two linear maps agreeing on the generators of rank two agree on `latticeSpan V`. -/
lemma eqOn_latticeSpan {f g : (Submodule ℤ V →₀ ℤ) →ₗ[ℤ] (Submodule ℤ V →₀ ℤ)}
    (h : ∀ Λ : Submodule ℤ V, Nonempty (Module.Basis (Fin 2) ℤ Λ) → f (single Λ 1) = g (single Λ 1))
    {x : Submodule ℤ V →₀ ℤ} (hx : x ∈ latticeSpan V) : f x = g x :=
  LinearMap.eqOn_span (s := {x | ∃ Λ : Submodule ℤ V, Nonempty (Module.Basis (Fin 2) ℤ Λ) ∧ x = single Λ 1})
    (by rintro _ ⟨Λ, hΛ, rfl⟩; exact h Λ hΛ) hx

/-- $T(n)$, $n \ge 1$, maps `latticeSpan V` into itself. -/
theorem latticeT_mem_latticeSpan {n : ℕ} (hn : 0 < n) {x : Submodule ℤ V →₀ ℤ} (hx : x ∈ latticeSpan V) :
    latticeT n x ∈ latticeSpan V := by
  unfold latticeSpan at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Λ, hΛ, rfl⟩ := hx
    obtain ⟨ω₁, ω₂, hli, rfl⟩ := exists_pair_of_basis hΛ
    rw [latticeT_span_pair hli hn]
    exact Submodule.sum_mem _ fun t ht ↦
      single_mem_latticeSpan (nonempty_basis_span_pair (triple_li hli ht hn))
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- $R(n)$, $n \ge 1$, maps `latticeSpan V` into itself. -/
theorem latticeR_mem_latticeSpan {n : ℕ} (hn : 0 < n) {x : Submodule ℤ V →₀ ℤ} (hx : x ∈ latticeSpan V) :
    latticeR n x ∈ latticeSpan V := by
  unfold latticeSpan at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Λ, hΛ, rfl⟩ := hx
    obtain ⟨ω₁, ω₂, hli, rfl⟩ := exists_pair_of_basis hΛ
    rw [latticeR_single, scaleSub_span_pair]
    exact single_mem_latticeSpan (nonempty_basis_span_pair (smul_li hli hn))
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- $T(n)$ as an endomorphism of `latticeSpan V` ($T(0)$ is set to $0$). -/
noncomputable def latticeTD (V : Type*) [AddCommGroup V] (n : ℕ) : Module.End ℤ (latticeSpan V) :=
  if hn : 0 < n then (latticeT n).restrict fun _ hx ↦ latticeT_mem_latticeSpan hn hx else 0

/-- $R(n)$ as an endomorphism of `latticeSpan V` ($R(0)$ is set to $0$). -/
noncomputable def latticeRD (V : Type*) [AddCommGroup V] (n : ℕ) : Module.End ℤ (latticeSpan V) :=
  if hn : 0 < n then (latticeR n).restrict fun _ hx ↦ latticeR_mem_latticeSpan hn hx else 0

/-- Milne's algebra $H$ of Corollary 5.11: the $\mathbb Z$-subalgebra of $\mathrm{End}(D)$ generated by the $T(p)$ and
$R(p)$, $p$ prime. -/
noncomputable def latticeHeckeAlgebra (V : Type*) [AddCommGroup V] : Subalgebra ℤ (Module.End ℤ (latticeSpan V)) :=
  Algebra.adjoin ℤ (Set.range (fun p : Nat.Primes ↦ latticeTD V p) ∪ Set.range (fun p : Nat.Primes ↦ latticeRD V p))

lemma coe_latticeTD {n : ℕ} (hn : 0 < n) (x : latticeSpan V) :
    ((latticeTD V n x : latticeSpan V) : Submodule ℤ V →₀ ℤ) = latticeT n x := by
  simp [latticeTD, hn]

lemma coe_latticeRD {n : ℕ} (hn : 0 < n) (x : latticeSpan V) :
    ((latticeRD V n x : latticeSpan V) : Submodule ℤ V →₀ ℤ) = latticeR n x := by
  simp [latticeRD, hn]

lemma latticeTD_zero : latticeTD V 0 = 0 := by simp [latticeTD]

lemma latticeRD_zero : latticeRD V 0 = 0 := by simp [latticeRD]

/-- Proposition 5.9(a), extended linearly to `latticeSpan V`. -/
lemma latticeT_mul_of_coprime_span {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n)
    {x : Submodule ℤ V →₀ ℤ} (hx : x ∈ latticeSpan V) :
    latticeT m (latticeT n x) = latticeT (m * n) x := by
  have h := eqOn_latticeSpan (f := (latticeT m).comp (latticeT n)) (g := latticeT (m * n))
    (fun _ hΛ ↦ by rw [LinearMap.comp_apply]; exact latticeT_mul_of_coprime hΛ hm hn hmn) hx
  rwa [LinearMap.comp_apply] at h

/-- Proposition 5.9(b), extended linearly to `latticeSpan V`. -/
lemma latticeT_prime_pow_mul_prime_span {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 1 ≤ n)
    {x : Submodule ℤ V →₀ ℤ} (hx : x ∈ latticeSpan V) :
    latticeT (p ^ n) (latticeT p x) =
      latticeT (p ^ (n + 1)) x + (p : ℤ) • latticeR p (latticeT (p ^ (n - 1)) x) := by
  have h := eqOn_latticeSpan (f := (latticeT (p ^ n)).comp (latticeT p))
    (g := latticeT (p ^ (n + 1)) + (p : ℤ) • (latticeR p).comp (latticeT (p ^ (n - 1))))
    (fun _ hΛ ↦ by
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply]
      exact latticeT_prime_pow_mul_prime hΛ hp hn) hx
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] using h

/-- `R(c)` and `T(n)` commute on `latticeSpan V`. -/
lemma latticeR_latticeT_comm {c n : ℕ} (hc : 0 < c) (hn : 0 < n) {x : Submodule ℤ V →₀ ℤ}
    (hx : x ∈ latticeSpan V) : latticeR c (latticeT n x) = latticeT n (latticeR c x) := by
  refine eqOn_latticeSpan (f := (latticeR c).comp (latticeT n)) (g := (latticeT n).comp (latticeR c))
    (fun Λ hΛ ↦ ?_) hx
  obtain ⟨ω₁, ω₂, hli, rfl⟩ := exists_pair_of_basis hΛ
  simp only [LinearMap.comp_apply]
  rw [latticeR_single, latticeT_scaleSub hli hc hn]

lemma latticeTD_mul_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) :
    latticeTD V m * latticeTD V n = latticeTD V (m * n) := by
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  rw [Module.End.mul_apply, coe_latticeTD hm, coe_latticeTD hn, coe_latticeTD (Nat.mul_pos hm hn)]
  exact latticeT_mul_of_coprime_span hm hn hmn x.2

lemma latticeRD_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    latticeRD V (m * n) = latticeRD V m * latticeRD V n := by
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  rw [Module.End.mul_apply, coe_latticeRD hm, coe_latticeRD hn, coe_latticeRD (Nat.mul_pos hm hn),
    latticeR_mul]

lemma latticeRD_one : latticeRD V 1 = 1 := by
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  rw [coe_latticeRD one_pos]
  exact latticeR_one _

lemma latticeTD_one : latticeTD V 1 = 1 := by
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  rw [coe_latticeTD one_pos]
  exact eqOn_latticeSpan (f := latticeT 1) (g := LinearMap.id) (fun Λ _ ↦ latticeT_one Λ) x.2

lemma latticeRD_comm_latticeTD {c n : ℕ} (hc : 0 < c) (hn : 0 < n) :
    latticeRD V c * latticeTD V n = latticeTD V n * latticeRD V c := by
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, coe_latticeRD hc, coe_latticeTD hn, coe_latticeTD hn,
    coe_latticeRD hc]
  exact latticeR_latticeT_comm hc hn x.2

/-- Proposition 5.9(b) in `End (latticeSpan V)`. -/
lemma latticeTD_pow_mul_prime {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 1 ≤ e) :
    latticeTD V (p ^ e) * latticeTD V p =
      latticeTD V (p ^ (e + 1)) + (p : Module.End ℤ (latticeSpan V)) * latticeRD V p * latticeTD V (p ^ (e - 1)) := by
  have h1 : 0 < p ^ e := pow_pos hp.pos e
  have h2 : 0 < p ^ (e - 1) := pow_pos hp.pos _
  have h3 : 0 < p ^ (e + 1) := pow_pos hp.pos _
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  rw [LinearMap.add_apply, Submodule.coe_add, Module.End.mul_apply, Module.End.mul_apply,
    Module.End.mul_apply, coe_latticeTD h1, coe_latticeTD hp.pos, coe_latticeTD h3, Module.End.natCast_apply]
  rw [latticeT_prime_pow_mul_prime_span hp he x.2]
  simp [coe_latticeRD hp.pos, coe_latticeTD h2]

lemma latticeTD_comm_prime {p q : Nat.Primes} :
    latticeTD V p * latticeTD V q = latticeTD V q * latticeTD V p := by
  by_cases h : p = q
  · rw [h]
  · have hc : (p : ℕ).Coprime q := (Nat.coprime_primes p.2 q.2).2 (fun h' ↦ h (Subtype.ext h'))
    rw [latticeTD_mul_coprime p.2.pos q.2.pos hc, mul_comm (p : ℕ) q,
      latticeTD_mul_coprime q.2.pos p.2.pos hc.symm]

lemma latticeRD_comm_prime {p q : Nat.Primes} :
    latticeRD V p * latticeRD V q = latticeRD V q * latticeRD V p := by
  rw [← latticeRD_mul p.2.pos q.2.pos, ← latticeRD_mul q.2.pos p.2.pos, mul_comm]

/-- **Milne, Corollary 5.11**, first part: $H$ is commutative. -/
@[kb "milne2017mf" "Section 5, Corollary 5.11 (pdf p. 71)"]
theorem latticeHeckeAlgebra_comm (x y : latticeHeckeAlgebra V) : x * y = y * x := by
  have hc : (Set.range (fun p : Nat.Primes ↦ latticeTD V p) ∪
      Set.range (fun p : Nat.Primes ↦ latticeRD V p)).Pairwise Commute := by
    rintro a (⟨p, rfl⟩ | ⟨p, rfl⟩) b (⟨q, rfl⟩ | ⟨q, rfl⟩) _
    · exact latticeTD_comm_prime
    · exact (latticeRD_comm_latticeTD q.2.pos p.2.pos).symm
    · exact latticeRD_comm_latticeTD p.2.pos q.2.pos
    · exact latticeRD_comm_prime
  exact isMulCommutative_iff.1 (Algebra.isMulCommutative_adjoin ℤ hc) x y

lemma latticeRD_mem (n : ℕ) : latticeRD V n ∈ latticeHeckeAlgebra V := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => rw [latticeRD_zero]; exact zero_mem _
  | one => rw [latticeRD_one]; exact one_mem _
  | prime_pow p k hp hk =>
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [zero_add, pow_one]
        exact Algebra.subset_adjoin (Or.inr ⟨⟨p, hp⟩, rfl⟩)
      · rw [pow_succ, latticeRD_mul (pow_pos hp.pos k) hp.pos]
        exact mul_mem (ih hk0) (Algebra.subset_adjoin (Or.inr ⟨⟨p, hp⟩, rfl⟩))
  | coprime a b ha hb _ iha ihb =>
    rw [latticeRD_mul (by omega) (by omega)]
    exact mul_mem iha ihb

lemma latticeTD_mem_all (n : ℕ) : latticeTD V n ∈ latticeHeckeAlgebra V := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => rw [latticeTD_zero]; exact zero_mem _
  | one => rw [latticeTD_one]; exact one_mem _
  | prime_pow p k hp hk =>
    have hgen : latticeTD V p ∈ latticeHeckeAlgebra V := Algebra.subset_adjoin (Or.inl ⟨⟨p, hp⟩, rfl⟩)
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · obtain rfl : k = 1 := by omega
        rwa [pow_one]
      · obtain ⟨e, rfl⟩ : ∃ e, k = e + 1 := ⟨k - 1, by omega⟩
        have h1 := ih e (by omega) (by omega)
        have h2 : latticeTD V (p ^ (e - 1)) ∈ latticeHeckeAlgebra V := by
          rcases Nat.eq_zero_or_pos (e - 1) with h | h
          · rw [h, pow_zero, latticeTD_one]; exact one_mem _
          · exact ih (e - 1) (by omega) h
        have := latticeTD_pow_mul_prime (V := V) hp (e := e) (by omega)
        have h3 : latticeTD V (p ^ (e + 1)) =
            latticeTD V (p ^ e) * latticeTD V p -
              (p : Module.End ℤ (latticeSpan V)) * latticeRD V p * latticeTD V (p ^ (e - 1)) := by
          rw [this]; abel
        rw [h3]
        refine sub_mem (mul_mem h1 hgen) (mul_mem (mul_mem ?_ (latticeRD_mem _)) h2)
        exact natCast_mem _ _
  | coprime a b ha hb hab iha ihb =>
    rw [← latticeTD_mul_coprime (by omega) (by omega) hab]
    exact mul_mem iha ihb

/-- **Milne, Corollary 5.11**, second part: $H$ contains $T(n)$ for all $n \ge 1$. -/
@[kb "milne2017mf" "Section 5, Corollary 5.11 (pdf p. 71)"]
theorem latticeTD_mem_latticeHeckeAlgebra {n : ℕ} (hn : 0 < n) : latticeTD V n ∈ latticeHeckeAlgebra V :=
  latticeTD_mem_all n

/-- **Milne, Corollary 5.10.** For all $m, n \ge 1$,
$T(m) \circ T(n) = \sum_{d \mid \gcd(m,n),\, d > 0} d\,R(d) \circ T(mn/d^2)$ (on the generator of a lattice). -/
@[kb "milne2017mf" "Section 5, Corollary 5.10 (pdf p. 71)"]
theorem latticeT_mul {Λ : Submodule ℤ V} (hΛ : Nonempty (Module.Basis (Fin 2) ℤ Λ)) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) :
    latticeT m (latticeT n (single Λ 1)) =
      ∑ d ∈ (Nat.gcd m n).divisors, (d : ℤ) • latticeR d (latticeT (m * n / d ^ 2) (single Λ 1)) := by
  letI : CommRing (latticeHeckeAlgebra V) :=
    { (inferInstance : Ring (latticeHeckeAlgebra V)) with mul_comm := latticeHeckeAlgebra_comm }
  let t : ℕ → latticeHeckeAlgebra V := fun n ↦ ⟨latticeTD V n, latticeTD_mem_all n⟩
  let d : ℕ → latticeHeckeAlgebra V := fun n ↦ ⟨latticeRD V n, latticeRD_mem n⟩
  have key := ModularFormsKB.Miyake.heckeS_eq t d (Subtype.ext latticeTD_one) (Subtype.ext latticeRD_one)
    (fun a b ha hb ↦ Subtype.ext (latticeRD_mul ha hb))
    (fun a b ha hb hab ↦ Subtype.ext (latticeTD_mul_coprime ha hb hab).symm)
    (fun p e hp he ↦ Subtype.ext (by
      show latticeTD V p * latticeTD V (p ^ e) = latticeTD V (p ^ (e + 1)) +
        (p : Module.End ℤ (latticeSpan V)) * latticeRD V p * latticeTD V (p ^ (e - 1))
      rw [← latticeTD_pow_mul_prime hp he]
      exact congrArg Subtype.val (latticeHeckeAlgebra_comm (t p) (t (p ^ e)))))
    (m * n) m n rfl hm hn
  have h2 := congrArg (fun a : latticeHeckeAlgebra V =>
    ((a : Module.End ℤ (latticeSpan V)) ⟨single Λ 1, single_mem_latticeSpan hΛ⟩ : latticeSpan V).1) key
  simp only [ModularFormsKB.Miyake.heckeS] at h2
  simp only [Subalgebra.coe_mul, Module.End.mul_apply] at h2
  have hs : ∀ (s : Finset ℕ) (f : ℕ → latticeHeckeAlgebra V) (x : latticeSpan V),
      ((((∑ l ∈ s, f l : latticeHeckeAlgebra V) : Module.End ℤ (latticeSpan V)) x : latticeSpan V) :
        Submodule ℤ V →₀ ℤ) =
      ∑ l ∈ s, ((((f l : latticeHeckeAlgebra V) : Module.End ℤ (latticeSpan V)) x : latticeSpan V) :
        Submodule ℤ V →₀ ℤ) := by
    intro s f x
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [Finset.sum_insert ha, ih]
  rw [hs] at h2
  have hmn : 0 < m * n := Nat.mul_pos hm hn
  have h1 : (((t m : latticeHeckeAlgebra V) : Module.End ℤ (latticeSpan V))
      (((t n : latticeHeckeAlgebra V) : Module.End ℤ (latticeSpan V)) ⟨single Λ 1, single_mem_latticeSpan hΛ⟩) :
        latticeSpan V).1 = latticeT m (latticeT n (single Λ 1)) := by
    have e : (((t m : latticeHeckeAlgebra V) : Module.End ℤ (latticeSpan V))
      (((t n : latticeHeckeAlgebra V) : Module.End ℤ (latticeSpan V)) ⟨single Λ 1, single_mem_latticeSpan hΛ⟩)) =
        latticeTD V m (latticeTD V n ⟨single Λ 1, single_mem_latticeSpan hΛ⟩) := rfl
    rw [e, coe_latticeTD hm, coe_latticeTD hn]
  rw [h1] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have hl0 : 0 < l := Nat.pos_of_mem_divisors hl
  have hlg : l ∣ Nat.gcd m n := Nat.dvd_of_mem_divisors hl
  have hu : 0 < m * n / l ^ 2 := by
    apply Nat.div_pos _ (pow_pos hl0 2)
    exact Nat.le_of_dvd hmn (by
      rw [pow_two]; exact mul_dvd_mul (hlg.trans (Nat.gcd_dvd_left _ _)) (hlg.trans (Nat.gcd_dvd_right _ _)))
  have e : ((((l : latticeHeckeAlgebra V) * d l * t (m * n / l ^ 2) : latticeHeckeAlgebra V) :
      Module.End ℤ (latticeSpan V)) ⟨single Λ 1, single_mem_latticeSpan hΛ⟩) =
      ((l : Module.End ℤ (latticeSpan V)) * latticeRD V l * latticeTD V (m * n / l ^ 2)) ⟨single Λ 1,
        single_mem_latticeSpan hΛ⟩ := rfl
  rw [e, Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply]
  simp [coe_latticeRD hl0, coe_latticeTD hu]

/-- **Functions on lattices acted on by operators on $D$** (p. 71): $F$ is extended linearly to $D$ and
$(T \cdot F)(\Lambda) = F(T[\Lambda])$. -/
@[kb "milne2017mf" "Section 5, the action T · F on functions on lattices (pdf p. 71)"]
noncomputable def latticeOpFun (T : (Submodule ℤ V →₀ ℤ) →ₗ[ℤ] (Submodule ℤ V →₀ ℤ)) (F : Submodule ℤ V → ℂ) :
    Submodule ℤ V → ℂ :=
  fun Λ ↦ (T (single Λ 1)).sum fun Λ' c ↦ (c : ℂ) * F Λ'

/-- The linear extension of `F` to the free abelian group on subgroups. -/
noncomputable def linExt (F : Submodule ℤ V → ℂ) : (Submodule ℤ V →₀ ℤ) →ₗ[ℤ] ℂ :=
  Finsupp.linearCombination ℤ F

lemma linExt_single (F : Submodule ℤ V → ℂ) (Λ : Submodule ℤ V) : linExt F (single Λ 1) = F Λ := by
  simp [linExt]

lemma latticeOpFun_eq (T : (Submodule ℤ V →₀ ℤ) →ₗ[ℤ] (Submodule ℤ V →₀ ℤ)) (F : Submodule ℤ V → ℂ)
    (Λ : Submodule ℤ V) : latticeOpFun T F Λ = linExt F (T (single Λ 1)) := by
  simp [latticeOpFun, linExt, Finsupp.linearCombination_apply, zsmul_eq_mul]

lemma latticeOpFun_comp (T S : (Submodule ℤ V →₀ ℤ) →ₗ[ℤ] (Submodule ℤ V →₀ ℤ)) (F : Submodule ℤ V → ℂ)
    (Λ : Submodule ℤ V) :
    latticeOpFun T (latticeOpFun S F) Λ = linExt F (S (T (single Λ 1))) := by
  rw [latticeOpFun_eq]
  have : linExt (latticeOpFun S F) = (linExt F).comp S := by
    refine Finsupp.lhom_ext fun a b ↦ ?_
    rw [show single a b = b • single a (1 : ℤ) by simp, map_zsmul, map_zsmul, linExt_single,
      LinearMap.comp_apply, latticeOpFun_eq]
  rw [this]
  rfl

lemma latticeOpFun_span_pair {ω₁ ω₂ : V} (hli : LinearIndependent ℤ ![ω₁, ω₂]) {n : ℕ} (hn : 0 < n)
    (F : Submodule ℤ V → ℂ) :
    latticeOpFun (latticeT n) F (Submodule.span ℤ {ω₁, ω₂}) =
      ∑ t ∈ hermiteTriples n,
        F (Submodule.span ℤ {(t.1 : ℤ) • ω₁ + (t.2.1 : ℤ) • ω₂, (t.2.2 : ℤ) • ω₂}) := by
  rw [latticeOpFun_eq, latticeT_span_pair hli hn, map_sum]
  simp only [linExt_single]

end General

section Complex

/-- The lattice $c\Lambda$ for $c \in \mathbb C^\times$. -/
def scaleC (c : ℂ) (Λ : Submodule ℤ ℂ) : Submodule ℤ ℂ := Λ.map (LinearMap.mulLeft ℤ c)

lemma scaleSub_eq_scaleC (n : ℕ) (Λ : Submodule ℤ ℂ) : scaleSub (n : ℤ) Λ = scaleC (n : ℂ) Λ := by
  unfold scaleSub scaleC
  congr 1
  ext x
  simp

lemma scaleC_span_pair (c x y : ℂ) :
    scaleC c (Submodule.span ℤ {x, y}) = Submodule.span ℤ {c * x, c * y} := by
  simp [scaleC, Submodule.map_span, Set.image_pair]

/-- The `ℤ`-independence of the periods of a `PeriodPair`. -/
lemma PeriodPair_li (L : PeriodPair) : LinearIndependent ℤ ![L.ω₁, L.ω₂] :=
  L.indep.restrict_scalars' ℤ

/-- Scaling a `PeriodPair` by a nonzero complex number. -/
noncomputable def scalePP (c : ℂˣ) (L : PeriodPair) : PeriodPair where
  ω₁ := (c : ℂ) * L.ω₁
  ω₂ := (c : ℂ) * L.ω₂
  indep := by
    have h := L.indep.map' (LinearMap.mulLeft ℝ (c : ℂ)) (by
      rw [LinearMap.ker_eq_bot]
      exact mul_right_injective₀ c.ne_zero)
    convert h using 1
    funext i; fin_cases i <;> rfl

lemma lattice_scalePP (c : ℂˣ) (L : PeriodPair) :
    (scalePP c L).lattice = scaleC c L.lattice := by
  unfold PeriodPair.lattice
  rw [scaleC_span_pair]
  rfl

/-- The sublattice of a `PeriodPair` attached to a Hermite triple is again a lattice. -/
lemma exists_periodPair_triple (L : PeriodPair) {n : ℕ} (hn : 0 < n) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ hermiteTriples n) :
    ∃ L' : PeriodPair, L'.lattice =
      Submodule.span ℤ {(t.1 : ℤ) • L.ω₁ + (t.2.1 : ℤ) • L.ω₂, (t.2.2 : ℤ) • L.ω₂} := by
  rw [mem_hermiteTriples] at ht
  have ha : (t.1 : ℝ) ≠ 0 := by
    have : 0 < t.1 := Nat.pos_of_ne_zero (by intro h; rw [h] at ht; omega)
    exact_mod_cast this.ne'
  have hd : (t.2.2 : ℝ) ≠ 0 := by
    have : 0 < t.2.2 := Nat.pos_of_ne_zero (by intro h; rw [h] at ht; omega)
    exact_mod_cast this.ne'
  refine ⟨⟨(t.1 : ℤ) • L.ω₁ + (t.2.1 : ℤ) • L.ω₂, (t.2.2 : ℤ) • L.ω₂, ?_⟩, rfl⟩
  have hli := L.indep
  rw [LinearIndependent.pair_iff] at hli ⊢
  intro s u h
  have h' := hli (s * t.1) (s * t.2.1 + u * t.2.2) (by
    simp only [Complex.real_smul, zsmul_eq_mul, Int.cast_natCast] at h ⊢
    push_cast
    linear_combination h)
  obtain ⟨h1, h2⟩ := h'
  have hs : s = 0 := (mul_eq_zero.1 h1).resolve_right ha
  subst hs
  simp only [zero_mul, zero_add] at h2
  exact ⟨rfl, (mul_eq_zero.1 h2).resolve_right hd⟩

lemma latticeOpFun_periodPair (L : PeriodPair) {n : ℕ} (hn : 0 < n) (F : Submodule ℤ ℂ → ℂ) :
    latticeOpFun (latticeT n) F L.lattice =
      ∑ t ∈ hermiteTriples n,
        F (Submodule.span ℤ {(t.1 : ℤ) • L.ω₁ + (t.2.1 : ℤ) • L.ω₂, (t.2.2 : ℤ) • L.ω₂}) :=
  latticeOpFun_span_pair (PeriodPair_li L) hn F

/-- **$R(n) \cdot F = n^{-2k}F$** for $F$ of weight $2k$, i.e. $F(c\Lambda) = c^{-2k}F(\Lambda)$ on lattices (p. 71). -/
@[kb "milne2017mf" "Section 5, R(n) · F for F of weight 2k (pdf p. 71)"]
theorem latticeOpFun_latticeR {k : ℕ} {F : Submodule ℤ ℂ → ℂ}
    (hF : ∀ (c : ℂˣ) (L : PeriodPair), F (scaleC c L.lattice) = (c : ℂ) ^ (-(2 * k : ℤ)) * F L.lattice)
    {n : ℕ} (hn : 0 < n) (L : PeriodPair) :
    latticeOpFun (latticeR n) F L.lattice = (n : ℂ) ^ (-(2 * k : ℤ)) * F L.lattice := by
  rw [latticeOpFun_eq, latticeR_single, linExt_single, scaleSub_eq_scaleC]
  have := hF (Units.mk0 (n : ℂ) (Nat.cast_ne_zero.2 hn.ne')) L
  simpa using this

/-- **Milne, Proposition 5.12**, first part: if $F$ is of weight $2k$ then so is $T(n) \cdot F$. -/
@[kb "milne2017mf" "Section 5, Proposition 5.12 (pdf p. 72)"]
theorem latticeOpFun_latticeT_isWeight {k : ℕ} {F : Submodule ℤ ℂ → ℂ}
    (hF : ∀ (c : ℂˣ) (L : PeriodPair), F (scaleC c L.lattice) = (c : ℂ) ^ (-(2 * k : ℤ)) * F L.lattice)
    {n : ℕ} (hn : 0 < n) (c : ℂˣ) (L : PeriodPair) :
    latticeOpFun (latticeT n) F (scaleC c L.lattice) =
      (c : ℂ) ^ (-(2 * k : ℤ)) * latticeOpFun (latticeT n) F L.lattice := by
  rw [← lattice_scalePP, latticeOpFun_periodPair _ hn, latticeOpFun_periodPair _ hn,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  obtain ⟨L', hL'⟩ := exists_periodPair_triple L hn ht
  have e : Submodule.span ℤ {(t.1 : ℤ) • (scalePP c L).ω₁ + (t.2.1 : ℤ) • (scalePP c L).ω₂,
      (t.2.2 : ℤ) • (scalePP c L).ω₂} = scaleC c L'.lattice := by
    rw [hL', scaleC_span_pair]
    have h1 : (t.1 : ℤ) • (scalePP c L).ω₁ + (t.2.1 : ℤ) • (scalePP c L).ω₂ =
        (c : ℂ) * ((t.1 : ℤ) • L.ω₁ + (t.2.1 : ℤ) • L.ω₂) := by
      simp only [scalePP, zsmul_eq_mul]; ring
    have h2 : (t.2.2 : ℤ) • (scalePP c L).ω₂ = (c : ℂ) * ((t.2.2 : ℤ) • L.ω₂) := by
      simp only [scalePP, zsmul_eq_mul]; ring
    rw [h1, h2]
  rw [e, hF c L', hL']

/-- `R(d)` acts on `T(u)[L]` by the scalar `d^(-2k)` after applying a weight-`2k` function. -/
lemma linExt_latticeR_latticeT {k : ℕ} {F : Submodule ℤ ℂ → ℂ}
    (hF : ∀ (c : ℂˣ) (L : PeriodPair), F (scaleC c L.lattice) = (c : ℂ) ^ (-(2 * k : ℤ)) * F L.lattice)
    {d u : ℕ} (hd : 0 < d) (hu : 0 < u) (L : PeriodPair) :
    linExt F (latticeR d (latticeT u (single L.lattice 1))) =
      (d : ℂ) ^ (-(2 * k : ℤ)) * latticeOpFun (latticeT u) F L.lattice := by
  rw [latticeOpFun_periodPair L hu]
  show linExt F (latticeR d (latticeT u (single (Submodule.span ℤ {L.ω₁, L.ω₂}) 1))) = _
  rw [latticeT_span_pair (PeriodPair_li L) hu, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  obtain ⟨L', hL'⟩ := exists_periodPair_triple L hu ht
  rw [latticeR_single, linExt_single, ← hL', scaleSub_eq_scaleC]
  have := hF (Units.mk0 (d : ℂ) (Nat.cast_ne_zero.2 hd.ne')) L'
  simpa using this

/-- **Milne, Proposition 5.12**, second part: for $F$ of weight $2k$ and $m, n \ge 1$,
$T(m) \cdot T(n) \cdot F = \sum_{d \mid \gcd(m,n),\, d > 0} d^{1-2k}\,T(mn/d^2) \cdot F$ (on lattices). In particular
$T(m) \cdot T(n) \cdot F = T(mn) \cdot F$ for coprime $m, n$ and
$T(p) \cdot T(p^n) \cdot F = T(p^{n+1}) \cdot F + p^{1-2k}\,T(p^{n-1}) \cdot F$. -/
@[kb "milne2017mf" "Section 5, Proposition 5.12 (pdf p. 72)"]
theorem latticeOpFun_latticeT_mul {k : ℕ} {F : Submodule ℤ ℂ → ℂ}
    (hF : ∀ (c : ℂˣ) (L : PeriodPair), F (scaleC c L.lattice) = (c : ℂ) ^ (-(2 * k : ℤ)) * F L.lattice)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (L : PeriodPair) :
    latticeOpFun (latticeT m) (latticeOpFun (latticeT n) F) L.lattice =
      ∑ d ∈ (Nat.gcd m n).divisors, (d : ℂ) ^ (1 - 2 * k : ℤ) * latticeOpFun (latticeT (m * n / d ^ 2)) F L.lattice := by
  rw [latticeOpFun_comp]
  have hΛ : Nonempty (Module.Basis (Fin 2) ℤ L.lattice) := nonempty_basis_span_pair (PeriodPair_li L)
  rw [latticeT_mul hΛ hn hm, map_sum, Nat.gcd_comm, mul_comm n m]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hlg : d ∣ Nat.gcd m n := Nat.dvd_of_mem_divisors hd
  have hu : 0 < m * n / d ^ 2 := by
    apply Nat.div_pos _ (pow_pos hd0 2)
    exact Nat.le_of_dvd (Nat.mul_pos hm hn) (by
      rw [pow_two]; exact mul_dvd_mul (hlg.trans (Nat.gcd_dvd_left _ _)) (hlg.trans (Nat.gcd_dvd_right _ _)))
  rw [map_zsmul, linExt_latticeR_latticeT hF hd0 hu, zsmul_eq_mul, Int.cast_natCast, ← mul_assoc]
  congr 1
  have : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd0.ne'
  rw [show (1 - 2 * k : ℤ) = 1 + (-(2 * k : ℤ)) by ring, zpow_add₀ this, zpow_one]

end Complex

end ModularFormsKB.Milne
