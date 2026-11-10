import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Weighted
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import ModularFormsKB.Miyake.DirichletCharacters
import ModularFormsKB.Citation
/-!
# Miyake §7.1: Eisenstein series of weight $k \ge 3$ with two characters

Miyake, *Modular Forms* (Springer 1989), §7.1, pp. 268–274.

For Dirichlet characters $\chi$ mod $L$ and $\psi$ mod $M$ and $k \ge 3$, Miyake (7.1.1) puts
$$E_k(z;\chi,\psi) = \sideset{}{'}\sum_{m,n} \chi(m)\,\psi(n)\,(mz+n)^{-k},$$
the sum over all integer pairs $(m,n) \ne (0,0)$. Miyake's Dirichlet characters are maps
$\mathbb Z \to \mathbb C$ vanishing off the units (§3.1, p. 80), and his principal character
$\chi_0$ is the character mod $1$; both conventions agree with Mathlib's `DirichletCharacter`
evaluated at integer casts.

We define the more general lattice series `latticeSeries k f z = ∑' v, f v (v₀ z + v₁)^{-k}`
for a weight $f : \mathbb Z^2 \to \mathbb C$ (Mathlib's `eisSummand` vanishes at $v = 0$ for
$k \ne 0$, so the sum over all pairs is Miyake's $\sum'$), prove its slash rule, and deduce
Lemma 7.1.1, Lemma 7.1.2 and (7.1.6). Miyake's series $E_k(z;\mu,\nu;N)$ of (7.1.14), over a
residue class mod $N$, is Tau Ceti's weighted series for the indicator weight
(`TauCeti.EisensteinSeries.weightedEisensteinSeries`), which gives Lemma 7.1.5: each lies in
$M_k(\Gamma(N))$.
-/

open UpperHalfPlane ModularForm EisensteinSeries Matrix Complex CongruenceSubgroup ZMod
open scoped MatrixGroups Real

noncomputable section

namespace ModularFormsKB.Miyake.Wave2B

/-- The lattice series $\sum_{v \in \mathbb Z^2} f(v)\,(v_0 z + v_1)^{-k}$ with weight
$f : \mathbb Z^2 \to \mathbb C$ (the term $v = 0$ is $0$ for $k \ne 0$). -/
def latticeSeries (k : ℤ) (f : (Fin 2 → ℤ) → ℂ) (z : ℍ) : ℂ :=
  ∑' v : Fin 2 → ℤ, f v * eisSummand k v z

/-- Slash rule for lattice series: $(\sum_v f(v)(v_0z+v_1)^{-k})|_k\gamma
= \sum_w f(w\gamma^{-1})(w_0z+w_1)^{-k}$ for $\gamma \in SL_2(\mathbb Z)$. -/
theorem latticeSeries_slash (k : ℤ) (f : (Fin 2 → ℤ) → ℂ) (γ : SL(2, ℤ)) :
    latticeSeries k f ∣[k] γ =
      latticeSeries k (fun w ↦ f (w ᵥ* ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))) := by
  ext1 z
  simp_rw [SL_slash_apply, _root_.zpow_neg,
    mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| denom_ne_zero _ z), latticeSeries,
    eisSummand_SL2_apply, mul_left_comm _ (_ ^ k), tsum_mul_left, mul_comm (_ ^ k)]
  congr 1
  have h1 : ∀ v : Fin 2 → ℤ, (v ᵥ* ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ᵥ*
      (γ : Matrix (Fin 2) (Fin 2) ℤ) = v := by
    intro v
    rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  have h2 : ∀ v : Fin 2 → ℤ, (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) ᵥ*
      ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = v := by
    intro v
    rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  let e : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) :=
    { toFun := fun v ↦ v ᵥ* ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      invFun := fun v ↦ v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)
      left_inv := h1
      right_inv := h2 }
  conv_lhs => rw [← e.tsum_eq]
  refine tsum_congr fun v ↦ ?_
  simp only [e, Equiv.coe_fn_mk, h1]

/-- **Miyake (7.1.1).** The Eisenstein series with characters
$E_k(z;\chi,\psi) = \sum'_{m,n} \chi(m)\psi(n)(mz+n)^{-k}$, for Dirichlet characters $\chi$ mod $L$
and $\psi$ mod $M$. It converges absolutely for $k \ge 3$. -/
@[kb "miyake1989" "(7.1.1), p. 268"]
def eisensteinChar (k : ℤ) {L M : ℕ} (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (z : ℍ) : ℂ :=
  latticeSeries k (fun v ↦ χ (v 0) * ψ (v 1)) z

/-- Miyake's group (7.1.3): $\Gamma_0(L,M) = \{\gamma \in SL_2(\mathbb Z) : b \equiv 0 \bmod M,
\ c \equiv 0 \bmod L\}$, as a predicate on $\gamma$. -/
def IsGamma0LM (L M : ℕ) (γ : SL(2, ℤ)) : Prop :=
  (M : ℤ) ∣ γ 0 1 ∧ (L : ℤ) ∣ γ 1 0

lemma inv_apply_SL2 (γ : SL(2, ℤ)) :
    ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![γ 1 1, -γ 0 1; -γ 1 0, γ 0 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

/-- For $\gamma \in \Gamma_0(L,M)$, $\psi(a) = \overline{\psi(d)}$ (since $ad \equiv 1 \bmod M$). -/
lemma char_a_eq_conj_char_d {M : ℕ} (ψ : DirichletCharacter ℂ M) {γ : SL(2, ℤ)}
    (hb : (M : ℤ) ∣ γ 0 1) : ψ (γ 0 0) = starRingEnd ℂ (ψ (γ 1 1)) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  have hu : ((γ 0 0 : ℤ) : ZMod M) * ((γ 1 1 : ℤ) : ZMod M) = 1 := by
    have h1 : ((γ 0 1 : ℤ) : ZMod M) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb
    have := congrArg (fun x : ℤ ↦ (x : ZMod M)) hdet
    push_cast at this
    rw [h1, zero_mul, sub_zero] at this
    exact this
  have hd : IsUnit ((γ 1 1 : ℤ) : ZMod M) := ⟨⟨_, _, by rw [mul_comm]; exact hu, hu⟩, rfl⟩
  have hψd : ψ (γ 1 1) * starRingEnd ℂ (ψ (γ 1 1)) = 1 := by
    have hn : ‖ψ ((γ 1 1 : ℤ) : ZMod M)‖ = 1 := by
      simpa using DirichletCharacter.unit_norm_eq_one ψ hd.unit
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    simp
  have hψ : ψ (γ 0 0) * ψ (γ 1 1) = 1 := by
    rw [← map_mul, hu, map_one]
  have hne : ψ (γ 1 1) ≠ 0 := left_ne_zero_of_mul_eq_one hψd
  have := hψ.trans hψd.symm
  rw [mul_comm (ψ (γ 1 1))] at this
  exact mul_right_cancel₀ hne (by rw [this, mul_comm])

/-- **Miyake, Lemma 7.1.1.** For $\gamma = \begin{pmatrix} a&b\\c&d\end{pmatrix} \in
\Gamma_0(L,M)$, $E_k(z;\chi,\psi)|_k\gamma = \chi(d)\overline{\psi(d)}\,E_k(z;\chi,\psi)$. -/
@[kb "miyake1989" "Lemma 7.1.1, p. 269"]
theorem eisensteinChar_slash (k : ℤ) {L M : ℕ} (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) {γ : SL(2, ℤ)} (hγ : IsGamma0LM L M γ) :
    eisensteinChar k χ ψ ∣[k] γ =
      (χ (γ 1 1) * starRingEnd ℂ (ψ (γ 1 1))) • eisensteinChar k χ ψ := by
  have hfun : eisensteinChar k χ ψ = latticeSeries k (fun v ↦ χ (v 0) * ψ (v 1)) := rfl
  rw [hfun, latticeSeries_slash]
  ext z
  simp only [latticeSeries, Pi.smul_apply, smul_eq_mul, ← tsum_mul_left]
  refine tsum_congr fun w ↦ ?_
  rw [inv_apply_SL2]
  have hc : ((γ 1 0 : ℤ) : ZMod L) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hγ.2
  have hb : ((γ 0 1 : ℤ) : ZMod M) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hγ.1
  have h0 : (((w ᵥ* !![γ 1 1, -γ 0 1; -γ 1 0, γ 0 0]) 0 : ℤ) : ZMod L) =
      (w 0 : ZMod L) * (γ 1 1 : ZMod L) := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hc]
  have h1 : (((w ᵥ* !![γ 1 1, -γ 0 1; -γ 1 0, γ 0 0]) 1 : ℤ) : ZMod M) =
      (w 1 : ZMod M) * (γ 0 0 : ZMod M) := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hb]
  rw [h0, h1, map_mul, map_mul, char_a_eq_conj_char_d ψ hγ.1]
  ring

/-- **Miyake, Lemma 7.1.2.** $E_k(z;\chi,\psi)|_k\begin{pmatrix}0&-1\\1&0\end{pmatrix}
= \chi(-1)\,E_k(z;\psi,\chi)$. -/
@[kb "miyake1989" "Lemma 7.1.2, p. 269"]
theorem eisensteinChar_slash_S (k : ℤ) {L M : ℕ} (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) :
    eisensteinChar k χ ψ ∣[k] ModularGroup.S = χ (-1) • eisensteinChar k ψ χ := by
  have hfun : eisensteinChar k χ ψ = latticeSeries k (fun v ↦ χ (v 0) * ψ (v 1)) := rfl
  rw [hfun, latticeSeries_slash]
  ext z
  simp only [latticeSeries, eisensteinChar, Pi.smul_apply, smul_eq_mul, ← tsum_mul_left]
  refine tsum_congr fun w ↦ ?_
  rw [inv_apply_SL2]
  simp only [ModularGroup.S, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have : χ (-(w 1 : ZMod L)) = χ (-1) * χ (w 1) := by
    rw [← map_mul, neg_one_mul]
  rw [this]
  ring

/-- **Miyake (7.1.6).** If $\chi(-1)\psi(-1) \ne (-1)^k$ then $E_k(z;\chi,\psi) = 0$. -/
@[kb "miyake1989" "(7.1.6), p. 269"]
theorem eisensteinChar_eq_zero_of_parity (k : ℤ) {L M : ℕ} (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (h : χ (-1) * ψ (-1) ≠ (-1) ^ k) :
    eisensteinChar k χ ψ = 0 := by
  ext z
  have hneg : ∀ v : Fin 2 → ℤ, eisSummand k (-v) z = (-1) ^ k * eisSummand k v z := by
    intro v
    simp only [eisSummand, Pi.neg_apply, Int.cast_neg]
    rw [show -(v 0 : ℂ) * z + -(v 1 : ℂ) = (-1) * ((v 0 : ℂ) * z + v 1) by ring, mul_zpow]
    congr 1
    rw [_root_.zpow_neg, ← _root_.inv_zpow, inv_neg, inv_one]
  have hE : eisensteinChar k χ ψ z = (χ (-1) * ψ (-1) * (-1) ^ k) * eisensteinChar k χ ψ z := by
    simp only [eisensteinChar, latticeSeries]
    rw [← tsum_mul_left]
    conv_lhs => rw [← (Equiv.neg (Fin 2 → ℤ)).tsum_eq]
    refine tsum_congr fun v ↦ ?_
    simp only [Equiv.neg_apply, Pi.neg_apply, Int.cast_neg, hneg]
    rw [show -(v 0 : ZMod L) = (-1) * v 0 by ring, show -(v 1 : ZMod M) = (-1) * v 1 by ring,
      map_mul, map_mul]
    ring
  have hsq : ((-1 : ℂ) ^ k) * ((-1) ^ k) = 1 := by
    rw [← mul_zpow]; simp
  have hc : χ (-1) * ψ (-1) * (-1) ^ k ≠ 1 := by
    intro h1
    apply h
    calc χ (-1) * ψ (-1) = χ (-1) * ψ (-1) * ((-1) ^ k * (-1) ^ k) := by rw [hsq, mul_one]
      _ = (-1) ^ k := by rw [← mul_assoc, h1, one_mul]
  have : (1 - χ (-1) * ψ (-1) * (-1) ^ k) * eisensteinChar k χ ψ z = 0 := by
    rw [sub_mul, one_mul, ← hE, sub_self]
  simpa [sub_eq_zero, Ne.symm hc] using this

/-! ### Theorem 7.1.3: the Fourier expansion of $E_k(z;\chi,\psi)$ -/

/-- Miyake's constant term $C$ of Theorem 7.1.3: $2L_M(k,\psi) = 2\sum_{n \ge 1}\psi(n)n^{-k}$ if
$\chi$ is the principal character $\chi_0$ (the character mod $1$), and $0$ otherwise. -/
def eisensteinCharConst (k : ℕ) {L M : ℕ} (ψ : DirichletCharacter ℂ M) : ℂ :=
  if L = 1 then 2 * ∑' n : ℕ+, ψ (n : ℕ) * ((n : ℕ) : ℂ) ^ (-(k : ℤ)) else 0

/-- Miyake's constant $A = 2(-2\pi i)^k W(\psi^0) / (M^k (k-1)!)$ of Theorem 7.1.3, with $\psi^0$
the primitive character associated with $\psi$ and $W$ its Gauss sum. -/
def eisensteinCharA (k : ℕ) {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) : ℂ :=
  haveI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  2 * (-2 * π * Complex.I) ^ k * gaussSum ψ.primitiveCharacter ZMod.stdAddChar /
    ((M : ℂ) ^ k * (k - 1).factorial)

/-- Miyake's divisor sum $b(n)$ of (7.1.11), for a character $\chi_0$ mod $m$ (primitive in use)
and $l > 0$: $b(n) = \sum_{0 < d \mid (l, n)} d\,\mu(l/d)\,\chi_0(l/d)\,\overline{\chi_0}(n/d)$. -/
@[kb "miyake1989" "(7.1.11), p. 270"]
def gaussCoeff {m : ℕ} (χ₀ : DirichletCharacter ℂ m) (l n : ℕ) : ℂ :=
  ∑ d ∈ (Nat.gcd l n).divisors,
    (d : ℂ) * (ArithmeticFunction.moebius (l / d) : ℂ) * χ₀ ((l / d : ℕ) : ZMod m) *
      starRingEnd ℂ (χ₀ ((n / d : ℕ) : ZMod m))

/-- Lemma 3.1.3 (2) as a finite Fourier transform, for the induced character mod $lm$. -/
lemma dft_changeLevel_aux {m l : ℕ} [NeZero m] [NeZero l] {χ₀ : DirichletCharacter ℂ m}
    (hχ : χ₀.IsPrimitive) (n : ℕ) :
    𝓕 ⇑(χ₀.changeLevel (dvd_mul_left m l)) (-(n : ZMod (l * m))) =
      gaussSum χ₀ ZMod.stdAddChar * gaussCoeff χ₀ l n := by
  have h := ModularFormsKB.Miyake.sum_changeLevel_mul_exp (l := l) hχ (n : ℤ)
  have hg : Int.gcd l (n : ℤ) = Nat.gcd l n := rfl
  rw [hg] at h
  have h2 : ∀ d : ℕ, (((n : ℤ) / d : ℤ) : ZMod m) = ((n / d : ℕ) : ZMod m) := by
    intro d; rw [← Int.natCast_div, Int.cast_natCast]
  simp only [h2] at h
  rw [dft_apply, gaussCoeff, ← h, ← ModularFormsKB.Miyake.sum_range_eq_sum_zmod]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [smul_eq_mul, mul_comm, show -((a : ZMod (l * m)) * -(n : ZMod (l * m))) =
    (((a * n : ℕ) : ℤ) : ZMod (l * m)) by push_cast; ring, stdAddChar_coe]
  push_cast
  ring_nf

/-- `dft_changeLevel_aux` for any level `M` divisible by `m`. -/
lemma dft_changeLevel_aux' {M m : ℕ} [NeZero M] [NeZero m] {χ₀ : DirichletCharacter ℂ m}
    (hχ : χ₀.IsPrimitive) (h : m ∣ M) (ψ : DirichletCharacter ℂ M)
    (hψ : ψ = χ₀.changeLevel h) (n : ℕ) :
    𝓕 ⇑ψ (-(n : ZMod M)) = gaussSum χ₀ ZMod.stdAddChar * gaussCoeff χ₀ (M / m) n := by
  obtain ⟨l, hl⟩ := h
  rw [mul_comm] at hl
  subst hl
  subst hψ
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have : NeZero l := ⟨fun h0 ↦ NeZero.ne (l * m) (by simp [h0])⟩
  rw [Nat.mul_div_cancel _ hm]
  exact dft_changeLevel_aux hχ n

/-- Miyake (7.1.10): the finite Fourier transform of a Dirichlet character `ψ` mod `M` is the
Gauss sum of its primitive character times the divisor sum `b(n)` of (7.1.11). -/
@[kb "miyake1989" "(7.1.10), p. 270"]
lemma dft_dirichletCharacter {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M) (n : ℕ) :
    haveI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
    𝓕 ⇑ψ (-(n : ZMod M)) = gaussSum ψ.primitiveCharacter ZMod.stdAddChar *
      gaussCoeff ψ.primitiveCharacter (M / ψ.conductor) n :=
  haveI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  dft_changeLevel_aux' ψ.primitiveCharacter_isPrimitive ψ.conductor_dvd_level ψ
    ψ.changeLevel_primitiveCharacter.symm n

/-- Negating the lattice vector multiplies `eisSummand` by $(-1)^k$. -/
lemma eisSummand_neg' (k : ℤ) (v : Fin 2 → ℤ) (z : ℍ) :
    eisSummand k (-v) z = (-1) ^ k * eisSummand k v z := by
  simp only [eisSummand, Pi.neg_apply, Int.cast_neg]
  rw [show -(v 0 : ℂ) * z + -(v 1 : ℂ) = (-1) * ((v 0 : ℂ) * z + v 1) by ring, mul_zpow]
  congr 1
  rw [_root_.zpow_neg, ← _root_.inv_zpow, inv_neg, inv_one]

/-- Miyake's coefficient $a(n)$ of Theorem 7.1.3: with $m_\psi$ the conductor of $\psi$,
$l = M/m_\psi$ and $\mu$ the Möbius function,
$$a(n) = \sum_{0 < c \mid n} \chi(n/c)\, c^{k-1} \sum_{0 < d \mid (l, c)} d\,\mu(l/d)\,
  \psi^0(l/d)\,\overline{\psi^0}(c/d),$$
the inner sum being `gaussCoeff` (Miyake's $b(c)$ of (7.1.11)). -/
def eisensteinCharCoeff (k : ℕ) {L M : ℕ} (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (n : ℕ) : ℂ :=
  ∑ c ∈ n.divisors, χ ((n / c : ℕ) : ZMod L) * (c : ℂ) ^ (k - 1) *
    gaussCoeff ψ.primitiveCharacter (M / ψ.conductor) c

/-- The Eisenstein series with characters summed row by row ("Eisenstein summation"):
$\sum_{m}\big(\sum_{n}\chi(m)\psi(n)(mz+n)^{-k}\big)$. For $k \ge 3$ it is `eisensteinChar`; for
$k = 2$ the double series is not absolutely convergent, but the iterated sum converges. -/
def eisensteinCharRowSum (k : ℤ) {L M : ℕ} (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (z : ℍ) : ℂ :=
  ∑' m : ℤ, ∑' n : ℤ, χ m * ψ n * eisSummand k ![m, n] z

/-- **Theorem 7.1.3 for the row-wise sum, $k \ge 2$.** Let $k \ge 2$ and
$\chi(-1)\psi(-1) = (-1)^k$. Then
$\sum_m \sum_n \chi(m)\psi(n)(mz+n)^{-k} = C + A\sum_{n \ge 1} a(n)e^{2\pi i nz/M}$, with Miyake's
$C$, $A$, $a(n)$. Miyake's proof (pp. 269–270) only sums row by row, so it applies verbatim for
$k = 2$, where the double series is not absolutely convergent. (Miyake's weight-two series of
Theorem 7.2.12 is defined instead by Hecke's limit $s \to 0$; it differs from this row-wise sum
by $D/y$, with $D \ne 0$ only for $\chi$, $\psi$ both principal; that comparison is not proved
here.) -/
@[kb "miyake1989" "Theorem 7.1.3, p. 270"]
theorem hasSum_eisensteinCharRowSum {k : ℕ} (hk : 2 ≤ k) {L M : ℕ} [NeZero L] [NeZero M]
    (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (hpar : χ (-1) * ψ (-1) = (-1) ^ k) (z : ℍ) :
    HasSum (fun n : ℕ+ ↦ eisensteinCharA k ψ * eisensteinCharCoeff k χ ψ n *
        cexp (2 * π * Complex.I * (n : ℕ) * z / M))
      (eisensteinCharRowSum k χ ψ z - eisensteinCharConst k (L := L) ψ) := by
  have hk2 : 2 ≤ k := hk
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  set K : ℂ := (-2 * π * Complex.I) ^ k / ((k - 1).factorial * M ^ k) with hK
  set q : ℂ := cexp (2 * π * Complex.I * z / M) with hq
  set F : ℕ → ℂ := fun m ↦ 𝓕 ⇑ψ (-(m : ZMod M)) with hF
  -- the double series, its rows
  set G : ℤ × ℤ → ℂ := fun p ↦ χ p.1 * ψ p.2 * eisSummand k ![p.1, p.2] z with hG
  set R : ℤ → ℂ := fun c ↦ ∑' n : ℤ, G (c, n) with hR
  -- parity: the rows `c` and `-c` agree
  have hREven : Function.Even R := by
    intro c
    simp only [hR, hG]
    rw [← (Equiv.neg ℤ).tsum_eq]
    refine tsum_congr fun n ↦ ?_
    have hv : (![-c, -n] : Fin 2 → ℤ) = -![c, n] := by
      ext i; fin_cases i <;> simp
    simp only [Equiv.neg_apply, hv, eisSummand_neg', Int.cast_neg]
    rw [show -(c : ZMod L) = (-1) * c by ring, show -(n : ZMod M) = (-1) * n by ring,
      map_mul, map_mul]
    have hsq : ((-1 : ℂ) ^ k) * ((-1) ^ k) = 1 := by rw [← mul_pow]; simp
    rw [zpow_natCast]
    linear_combination (χ c * ψ n * eisSummand k ![c, n] z * (-1) ^ k) * hpar
      + χ c * ψ n * eisSummand k ![c, n] z * hsq
  -- summability of the inner sums
  have hin (c : ℤ) : Summable fun n : ℤ ↦ G (c, n) := by
    refine (summable_norm_iff.mpr (linear_right_summable (z : ℂ) c (k := (k : ℤ))
      (by exact_mod_cast hk))).of_norm_bounded fun n ↦ ?_
    simp only [hG, eisSummand, norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans_eq ?_
    · exact (mul_le_mul (DirichletCharacter.norm_le_one _ _) (DirichletCharacter.norm_le_one _ _)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    · simp [_root_.zpow_neg]
  -- the row `c = 0` is the constant term
  have hR0 : R 0 = eisensteinCharConst k (L := L) ψ := by
    have hR0' : R 0 = χ 0 * ∑' n : ℤ, ψ n * (n : ℂ) ^ (-(k : ℤ)) := by
      simp only [hR, hG, ← tsum_mul_left]
      refine tsum_congr fun n ↦ ?_
      simp [eisSummand, mul_assoc]
    rw [hR0', eisensteinCharConst]
    by_cases hL : L = 1
    · subst hL
      have h0 : χ 0 = 1 := by
        rw [show (0 : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
      have h1 : χ (-1) = 1 := by
        rw [show (-1 : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
      rw [h1, one_mul] at hpar
      set g : ℤ → ℂ := fun n ↦ ψ n * (n : ℂ) ^ (-(k : ℤ)) with hg
      have hgs : Summable g := by
        refine (hin 0).congr fun n ↦ ?_
        simp [hG, hg, eisSummand]
      have hgE : Function.Even g := by
        intro n
        simp only [hg, Int.cast_neg]
        rw [show -(n : ZMod M) = (-1) * n by ring, map_mul, hpar,
          show -(n : ℂ) = (-1) * n by ring, mul_zpow, _root_.zpow_neg, _root_.zpow_neg, zpow_natCast,
          zpow_natCast]
        have hne : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
        field_simp
      simp only [↓reduceIte]
      rw [h0, one_mul, tsum_int_eq_zero_add_two_mul_tsum_pnat hgE hgs]
      simp [hg, nsmul_eq_mul, show k ≠ 0 by omega]
    · have : Fact (1 < L) := ⟨by have := NeZero.ne L; omega⟩
      simp only [hL, ↓reduceIte]
      rw [MulChar.map_zero, zero_mul]
  -- the rows `c ≥ 1`, by the Lipschitz formula along residue classes
  set T : ℕ → ℕ → ℂ := fun c m ↦ χ c * F m * (m : ℂ) ^ (k - 1) * q ^ (c * m) with hT
  have hrow (c : ℕ+) : R c = K * ∑' m : ℕ+, T c m := by
    let w : ℍ := ⟨((c : ℕ) : ℂ) * z, by
      simpa using mul_pos (Nat.cast_pos.mpr c.pos) z.2⟩
    have H := TauCeti.EisensteinSeries.qExpansion_identity_zmod (⇑ψ) hk2 w
    simp only [hR, hG]
    have h1 : ∀ n : ℤ, χ ((c : ℕ) : ℤ) * ψ n * eisSummand k ![((c : ℕ) : ℤ), n] z =
        χ ((c : ℕ) : ZMod L) * (ψ n * ((w : ℂ) + n) ^ (-(k : ℤ))) := by
      intro n
      simp [eisSummand, w, mul_assoc]
    simp_rw [h1]
    rw [tsum_mul_left, H, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun m ↦ ?_
    have h2 : cexp (2 * π * Complex.I * w / M) ^ (m : ℕ) = q ^ ((c : ℕ) * m) := by
      rw [hq, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
      congr 1
      simp only [w]
      push_cast
      ring
    rw [h2]
    simp only [hT, hF]
    ring
  -- the double series over `(c, m)` converges absolutely
  have hqn : ‖q‖ < 1 := by
    have h := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨(z : ℂ) / M, by
      simpa [Complex.div_natCast_im] using div_pos z.2 (Nat.cast_pos.mpr (NeZero.pos M))⟩
    simpa [hq, mul_div_assoc] using h
  have hTsn : Summable fun p : ℕ+ × ℕ+ ↦ ‖T p.1 p.2‖ := by
    have hr : ‖‖q‖‖ < 1 := by simpa using hqn
    refine ((summable_prod_mul_pow (k - 1) hr).mul_left
      (∑ j, ‖𝓕 ⇑ψ j‖)).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun p ↦ ?_
    simp only [hT, hF, norm_mul, norm_pow, Complex.norm_natCast]
    have h1 := DirichletCharacter.norm_le_one χ (p.1 : ℕ)
    have h2 : ‖𝓕 ⇑ψ (-(p.2 : ℕ))‖ ≤ ∑ j, ‖𝓕 ⇑ψ j‖ :=
      Finset.single_le_sum (f := fun j ↦ ‖𝓕 ⇑ψ j‖) (fun _ _ ↦ norm_nonneg _)
        (Finset.mem_univ _)
    calc ‖χ (p.1 : ℕ)‖ * ‖𝓕 ⇑ψ (-(p.2 : ℕ))‖ * ((p.2 : ℕ) : ℝ) ^ (k - 1) *
          ‖q‖ ^ ((p.1 : ℕ) * p.2)
        ≤ 1 * (∑ j, ‖𝓕 ⇑ψ j‖) * ((p.2 : ℕ) : ℝ) ^ (k - 1) * ‖q‖ ^ ((p.1 : ℕ) * p.2) := by
          gcongr
      _ = _ := by ring
  have hTs : Summable fun p : ℕ+ × ℕ+ ↦ T p.1 p.2 := hTsn.of_norm
  -- the rows are summable: they decay exponentially in `|c|`
  have hRs : Summable R := by
    have hpnat : Summable fun c : ℕ+ ↦ R c := by
      refine (hTsn.prod.mul_left ‖K‖).of_norm_bounded fun c ↦ ?_
      rw [hrow c, norm_mul]
      gcongr
      exact norm_tsum_le_tsum_norm (hTsn.prod_factor c)
    have hnat : Summable fun n : ℕ ↦ R n := by
      exact (summable_pnat_iff_summable_nat (f := fun n : ℕ ↦ R n)).mp hpnat
    exact .of_nat_of_neg hnat (hnat.congr fun n ↦ (hREven n).symm)
  rw [eisensteinCharRowSum, tsum_int_eq_zero_add_two_mul_tsum_pnat hREven hRs]
  rw [hR0, add_sub_cancel_left, tsum_congr hrow, tsum_mul_left]
  have H := (hTs.hasSum.sum_divisorsAntidiagonal).mul_left (2 * K)
  convert H using 1
  · funext n
    have hgroup : ∑ x ∈ (n : ℕ).divisorsAntidiagonal, T x.1 x.2 =
        (∑ x ∈ (n : ℕ).divisorsAntidiagonal, χ (x.1 : ZMod L) * F x.2 * (x.2 : ℂ) ^ (k - 1)) *
          q ^ (n : ℕ) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      simp only [hT]
      rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
    have hqn' : q ^ (n : ℕ) = cexp (2 * π * Complex.I * (n : ℕ) * z / M) := by
      rw [hq, ← Complex.exp_nat_mul]
      ring_nf
    rw [hgroup, Nat.sum_divisorsAntidiagonal' (f := fun a b ↦
      χ (a : ZMod L) * F b * (b : ℂ) ^ (k - 1)), hqn']
    have hC : eisensteinCharCoeff k χ ψ n = ∑ c ∈ (n : ℕ).divisors,
        χ (((n : ℕ) / c : ℕ) : ZMod L) * (c : ℂ) ^ (k - 1) *
          gaussCoeff ψ.primitiveCharacter (M / ψ.conductor) c := rfl
    simp only [hF, dft_dirichletCharacter, eisensteinCharA, hC, hK,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    field_simp
  · rw [hTs.tsum_prod, nsmul_eq_mul]
    push_cast
    ring



/-- For $k \ge 3$ the absolutely convergent double series is the row-wise sum. -/
lemma eisensteinChar_eq_eisensteinCharRowSum {k : ℤ} (hk : 3 ≤ k) {L M : ℕ}
    (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M) (z : ℍ) :
    eisensteinChar k χ ψ z = eisensteinCharRowSum k χ ψ z := by
  have hW : Summable fun x : Fin 2 → ℤ ↦ χ (x 0) * ψ (x 1) * eisSummand k x z := by
    refine (summable_norm_eisSummand hk z).of_norm_bounded fun x ↦ ?_
    rw [norm_mul, norm_mul]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    exact (mul_le_mul (DirichletCharacter.norm_le_one _ _) (DirichletCharacter.norm_le_one _ _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hsum : Summable fun p : ℤ × ℤ ↦ χ p.1 * ψ p.2 * eisSummand k ![p.1, p.2] z := by
    simpa [Function.comp_def] using (finTwoArrowEquiv ℤ).symm.summable_iff.mpr hW
  rw [eisensteinChar, latticeSeries, eisensteinCharRowSum, ← hsum.tsum_prod,
    ← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  refine tsum_congr fun p ↦ ?_
  simp

/-- **Miyake, Theorem 7.1.3.** Let $k \ge 3$ and $\chi$, $\psi$ Dirichlet characters mod $L$ and
mod $M$ with $\chi(-1)\psi(-1) = (-1)^k$. Then
$$E_k(z;\chi,\psi) = C + A\sum_{n=1}^\infty a(n)\, e^{2\pi i n z/M}$$
with $C$ = `eisensteinCharConst`, $A$ = `eisensteinCharA`, $a(n)$ = `eisensteinCharCoeff`
(the series converging). In particular $E_k(z;\chi,\psi)$ is holomorphic at $\infty$. -/
@[kb "miyake1989" "Theorem 7.1.3, p. 270"]
theorem hasSum_eisensteinChar {k : ℕ} (hk : 3 ≤ k) {L M : ℕ} [NeZero L] [NeZero M]
    (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (hpar : χ (-1) * ψ (-1) = (-1) ^ k) (z : ℍ) :
    HasSum (fun n : ℕ+ ↦ eisensteinCharA k ψ * eisensteinCharCoeff k χ ψ n *
        cexp (2 * π * Complex.I * (n : ℕ) * z / M))
      (eisensteinChar k χ ψ z - eisensteinCharConst k (L := L) ψ) := by
  rw [eisensteinChar_eq_eisensteinCharRowSum (by exact_mod_cast hk)]
  exact hasSum_eisensteinCharRowSum (by omega) χ ψ hpar z

/-- For primitive $\psi$, its primitive character is $\psi$ itself (on natural numbers). -/
lemma primitiveCharacter_natCast_of_isPrimitive {M : ℕ} [NeZero M] {ψ : DirichletCharacter ℂ M}
    (hψ : ψ.IsPrimitive) (c : ℕ) :
    ψ.primitiveCharacter (c : ZMod ψ.conductor) = ψ (c : ZMod M) := by
  by_cases hc : IsCoprime (c : ℤ) M
  · have := ψ.primitiveCharacter_apply_of_isCoprime hc
    simpa using this
  · have hu : ¬ IsUnit (c : ZMod M) := by
      rw [ZMod.isUnit_iff_coprime, ← Nat.isCoprime_iff_coprime]
      exact hc
    have hu' : ¬ IsUnit (c : ZMod ψ.conductor) := by
      rw [ZMod.isUnit_iff_coprime, ← Nat.isCoprime_iff_coprime, hψ]
      exact hc
    rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu']

/-- **Miyake (7.1.12).** If $\psi$ is primitive, then
$a(n) = \sum_{0 < c \mid n} \chi(n/c)\,\overline{\psi}(c)\,c^{k-1}$. -/
@[kb "miyake1989" "(7.1.12), p. 270"]
theorem eisensteinCharCoeff_of_isPrimitive (k : ℕ) {L M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ L) {ψ : DirichletCharacter ℂ M} (hψ : ψ.IsPrimitive) (n : ℕ) :
    eisensteinCharCoeff k χ ψ n =
      ∑ c ∈ n.divisors, χ ((n / c : ℕ) : ZMod L) * starRingEnd ℂ (ψ (c : ZMod M)) *
        (c : ℂ) ^ (k - 1) := by
  have hl : M / ψ.conductor = 1 := by
    rw [hψ, Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne M))]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  simp only [gaussCoeff, hl, Nat.gcd_one_left, Nat.divisors_one, Finset.sum_singleton,
    Nat.div_one, Nat.cast_one, ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul,
    map_one, primitiveCharacter_natCast_of_isPrimitive hψ]
  ring

/-! ### Lemma 7.1.5: the series $E_k(z;\mu,\nu;N)$ are modular forms for $\Gamma(N)$ -/

/-- **Miyake (7.1.14).** $E_k(z;\mu,\nu;N) = \sum'_{(m,n) \equiv (\mu,\nu) \bmod N}(mz+n)^{-k}$,
for a residue pair $a = (\mu, \nu)$ mod $N$. -/
@[kb "miyake1989" "(7.1.14), p. 271"]
def eisensteinResidue (k : ℤ) (N : ℕ) (a : Fin 2 → ZMod N) (z : ℍ) : ℂ :=
  latticeSeries k (fun x ↦ if ((↑) ∘ x : Fin 2 → ZMod N) = a then 1 else 0) z

/-- **Miyake, Lemma 7.1.5** (for the generators $E_k(z;\mu,\nu;N)$ of $\mathcal E^{(1)}_k(\Gamma(N))$).
For $k \ge 3$, $E_k(z;\mu,\nu;N)$ is a modular form of weight $k$ for $\Gamma(N)$ (holomorphic at
every cusp). It is Tau Ceti's weighted Eisenstein series for the indicator weight of $(\mu,\nu)$. -/
@[kb "miyake1989" "Lemma 7.1.5, p. 272"]
theorem exists_modularForm_eisensteinResidue {k : ℤ} (hk : 3 ≤ k) (N : ℕ) [NeZero N]
    (a : Fin 2 → ZMod N) :
    ∃ f : ModularForm Γ(N) k, ⇑f = eisensteinResidue k N a :=
  ⟨TauCeti.EisensteinSeries.weightedEisensteinSeriesMF (fun b ↦ if b = a then 1 else 0) hk, rfl⟩

/-- **Miyake (7.1.17).** For $\gamma \in SL_2(\mathbb Z)$,
$E_k(z;\mu,\nu;N)|_k\gamma = E_k(z;\mu',\nu';N)$ with $(\mu',\nu') = (\mu,\nu)\gamma$. -/
@[kb "miyake1989" "(7.1.17), p. 271"]
theorem eisensteinResidue_slash (k : ℤ) (N : ℕ) (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) :
    eisensteinResidue k N a ∣[k] γ =
      eisensteinResidue k N (a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) := by
  have h : ∀ b : Fin 2 → ZMod N, eisensteinResidue k N b =
      TauCeti.EisensteinSeries.weightedEisensteinSeries (fun c ↦ if c = b then 1 else 0) k :=
    fun _ ↦ rfl
  rw [h, h, TauCeti.EisensteinSeries.weightedEisensteinSeries_slash_apply]
  congr 1
  funext b
  have hinv : (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) =
      (((γ : SL(2, ZMod N))⁻¹ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
    rw [map_inv]
  have hiff : b ᵥ* (((γ : SL(2, ZMod N))⁻¹ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = a ↔
      b = a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
    constructor
    · rintro rfl
      rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
    · rintro rfl
      rw [Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  simp only [hinv, hiff]

end ModularFormsKB.Miyake.Wave2B
