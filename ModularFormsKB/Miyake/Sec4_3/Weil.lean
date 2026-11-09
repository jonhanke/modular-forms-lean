import ModularFormsKB.Miyake.Sec4_3.Twist
import ModularFormsKB.Miyake.Sec4_3.Growth
import ModularFormsKB.Miyake.Sec4_3.Gauss
import ModularFormsKB.Miyake.Sec4_3.WeilAux
import ModularFormsKB.Miyake.Sec4_3.Elliptic
import ModularFormsKB.Miyake.Sec4_3.WeilPrep

/-!
# Miyake §4.3: Weil's converse theorem

* `Miyake.weil_lemma_4_3_13` (Lemma 4.3.13), `Miyake.weil_lemma_4_3_14` (Lemma 4.3.14).
* Theorem 4.3.15 itself is in `ModularFormsKB.Miyake.Sec4_3.WeilTheorem`.
-/

open Complex Filter Asymptotics CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold

noncomputable section

namespace Miyake

/-- Condition $(A_\psi)$ of Miyake Lemma 4.3.9 with Weil's constant, for every primitive Dirichlet
character $\psi$ modulo $m$:
$f_\psi|_k\omega(Nm^2) = C_\psi\, g_{\bar\psi}$ with $C_\psi = \chi(m)\psi(-N)W(\psi)/W(\bar\psi)$. -/
def TwistedFrickeRelations (k N m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ N)
    (a b : ℕ → ℂ) : Prop :=
  ∀ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive → ∀ z : ℂ, 0 < z.im →
    fricke k (N * m ^ 2) (qSeries (twist ψ a)) z = weilConstant χ ψ * qSeries (twist ψ⁻¹ b) z

/-- The function $H(v) = \chi(m)\, g|_k\alpha(v/m) - f|_k\alpha(u/m)\,\omega(Nm^2)$ (with
$uvN \equiv -1 \bmod m$) of the proof of Miyake Lemma 4.3.13, indexed by $v \in \mathbb Z/m$. -/
def weilH (k N m : ℕ) (χ : DirichletCharacter ℂ N) (a b : ℕ → ℂ) (w : ZMod m) : ℍ → ℂ :=
  fun τ ↦ χ m * qSeries b (τ + (((w.val : ℕ) : ℝ) / m : ℝ)) -
    fricke k ((N : ℝ) * (m : ℝ) ^ 2)
      (fun ζ ↦ qSeries a (ζ + (((((-(w * N)⁻¹ : ZMod m)).val : ℕ) : ℝ) / m : ℝ))) τ

/-- Shifting the argument of `qSeries` by `x / m` only depends on `x` modulo `m`. -/
lemma qSeries_add_div_congr {a : ℕ → ℂ} {m : ℕ} (hm : 0 < m) {x y : ℤ}
    (hxy : (x : ZMod m) = y) (z : ℂ) :
    qSeries a (z + ((x : ℝ) / m : ℝ)) = qSeries a (z + ((y : ℝ) / m : ℝ)) := by
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub y x m).1 hxy.symm
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have this : (((x : ℝ) / m : ℝ) : ℂ) = (((y : ℝ) / m : ℝ) : ℂ) + (t : ℂ) := by
    have hx : (x : ℂ) = y + m * t := by
      have := congrArg (Int.cast : ℤ → ℂ) ht
      push_cast at this
      linear_combination this
    push_cast
    rw [hx]
    field_simp
  rw [this, ← add_assoc, qSeries_add_int]

lemma val_cast_eq {m : ℕ} [NeZero m] (w : ZMod m) : ((w.val : ℕ) : ℤ) = ((w.val : ℤ)) := rfl

/-- The key identity behind Miyake (4.3.26): the expression of Lemma 4.3.13 for a given
$\gamma(m,v)$ is `weilH` at $v \bmod m$. -/
lemma weil_slash_eq_weilH {k N m : ℕ} [NeZero m] (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) {a b : ℕ → ℂ}
    (hg : ∀ z : ℂ, 0 < z.im → fricke k N (qSeries a) z = qSeries b z)
    (u v n : ℤ) (h : (m : ℤ) * n - u * v * N = 1) :
    χ m • ((fun τ : ℍ ↦ qSeries b τ) ∣[(k : ℤ)] transl (v / m)) -
        (fun τ : ℍ ↦ qSeries b τ) ∣[(k : ℤ)]
          (Matrix.SpecialLinearGroup.mapGL ℝ (gammaMV N m v u n h) * transl (v / m)) =
      weilH k N m χ a b (v : ZMod m) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  funext τ
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, weilH]
  rw [SlashAction.slash_mul, slash_transl_apply, slash_transl_apply]
  have h1 := fricke_translate_eq_slash (k := (k : ℤ)) hN hm hg u v n h τ.im_pos
  have h1' : ((fun τ : ℍ ↦ qSeries b τ) ∣[(k : ℤ)]
      (Matrix.SpecialLinearGroup.mapGL ℝ (gammaMV N m v u n h)))
      ⟨(τ : ℂ) + ((v : ℝ) / m : ℝ), by simpa using τ.im_pos⟩ =
      fricke k ((N : ℝ) * (m : ℝ) ^ 2) (fun ζ ↦ qSeries a (ζ + ((u : ℝ) / m : ℝ))) τ := by
    rw [h1]; rfl
  simp only at h1' ⊢
  rw [h1']
  -- reduce `v` and `u` modulo `m`
  have hv : qSeries b ((τ : ℂ) + ((v : ℝ) / m : ℝ)) =
      qSeries b ((τ : ℂ) + (((((v : ZMod m)).val : ℕ) : ℝ) / m : ℝ)) := by
    have := qSeries_add_div_congr (a := b) hm (x := v) (y := ((((v : ZMod m)).val : ℕ) : ℤ))
      (by rw [Int.cast_natCast, ZMod.natCast_zmod_val]) τ
    simpa using this
  set w' : ZMod m := -(((v : ZMod m)) * N)⁻¹ with hw'
  have hu : w' = (u : ZMod m) := by
    have hh : ((v : ZMod m) * N) * (-(u : ZMod m)) = 1 := by
      have := congrArg (fun r : ℤ ↦ (r : ZMod m)) h
      push_cast at this
      rw [ZMod.natCast_self, zero_mul, zero_sub] at this
      linear_combination this
    rw [hw', ZMod.inv_eq_of_mul_eq_one _ _ _ hh, neg_neg]
  have hfu : ∀ ζ : ℂ, qSeries a (ζ + ((u : ℝ) / m : ℝ)) =
      qSeries a (ζ + (((w'.val : ℕ) : ℝ) / m : ℝ)) := by
    intro ζ
    have := qSeries_add_div_congr (a := a) hm (x := u) (y := ((w'.val : ℕ) : ℤ))
      (by rw [Int.cast_natCast, ZMod.natCast_zmod_val, hu]) ζ
    simpa using this
  rw [hv, fricke_congr hfu]

/-- **Miyake Lemma 4.3.13.** Let $k, N$ be positive integers, $\chi$ a Dirichlet character modulo
$N$ with $\chi(-1) = (-1)^k$, and $f, g$ satisfying (4.3.7) with $g = f|_k\omega_N$. Let $m$ be an
odd prime or $4$, prime to $N$. If $f, g$ satisfy $(A_\psi)$ for all primitive $\psi$ modulo $m$
with $C_\psi = \chi(m)\psi(-N)W(\psi)/W(\bar\psi)$, then
$$g|_k(\chi(m) - \gamma(m, v_1))\alpha(v_1/m) = g|_k(\chi(m) - \gamma(m, v_2))\alpha(v_2/m)$$
for all integers $v_1, v_2$ prime to $m$, where
$\gamma(m,v) = \begin{pmatrix} m & -v\\ -uN & n\end{pmatrix}$ with $mn - uvN = 1$ (any choice) and the
slash is extended linearly to $\mathbb C[\mathrm{GL}_2(\mathbb R)]$. Relation: same. -/
@[kb "miyake1989" "§4.3, Lemma 4.3.13, p. 125"]
theorem weil_lemma_4_3_13 {k N m : ℕ} [NeZero m] (hk : 0 < k) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (hχ : χ (-1) = (-1) ^ k) {a b : ℕ → ℂ}
    (ha : CoeffGrowth a) (hb : CoeffGrowth b)
    (hA : ∀ z : ℂ, 0 < z.im → qSeries b z = fricke k N (qSeries a) z)
    (hm : IsOddPrimeOrFour m) (hmN : m.Coprime N) (hAψ : TwistedFrickeRelations k N m χ a b)
    (u₁ v₁ n₁ u₂ v₂ n₂ : ℤ) (h₁ : m * n₁ - u₁ * v₁ * N = 1) (h₂ : m * n₂ - u₂ * v₂ * N = 1) :
    let g : ℍ → ℂ := fun τ ↦ qSeries b τ
    χ m • (g ∣[(k : ℤ)] transl (v₁ / m)) -
        g ∣[(k : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (gammaMV N m v₁ u₁ n₁ h₁) * transl (v₁ / m)) =
      χ m • (g ∣[(k : ℤ)] transl (v₂ / m)) -
        g ∣[(k : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (gammaMV N m v₂ u₂ n₂ h₂) * transl (v₂ / m)) := by
  intro g
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hg : ∀ z : ℂ, 0 < z.im → fricke k N (qSeries a) z = qSeries b z := fun z hz ↦ (hA z hz).symm
  rw [weil_slash_eq_weilH hN χ hg u₁ v₁ n₁ h₁, weil_slash_eq_weilH hN χ hg u₂ v₂ n₂ h₂]
  have hunit : ∀ (u v n : ℤ), (m : ℤ) * n - u * v * N = 1 → IsUnit (v : ZMod m) := by
    intro u v n h
    have := congrArg (fun r : ℤ ↦ (r : ZMod m)) h
    push_cast at this
    rw [ZMod.natCast_self, zero_mul, zero_sub] at this
    exact (Units.mkOfMulEqOne _ (-(u : ZMod m) * N) (by linear_combination this)).isUnit
  refine eq_of_sum_char_smul_eq_zero _ (fun ψ hψ ↦ ?_) (hunit _ _ _ h₁) (hunit _ _ _ h₂)
  have hψp : ψ.IsPrimitive := isPrimitive_of_ne_one hm hψ
  have hψi : ψ⁻¹.IsPrimitive := isPrimitive_inv_aux hψp
  have hWi : gaussW ψ⁻¹ ≠ 0 := gaussW_ne_zero hψi
  funext τ
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, weilH, Pi.zero_apply, mul_sub, Finset.sum_sub_distrib]
  set c : ℝ := (N : ℝ) * (m : ℝ) ^ 2 with hc
  -- the `g` side, by Lemma 4.3.10 for `ψ⁻¹`
  have hB := sum_transl_eq_gaussW_twist ψ⁻¹ hψi hb τ.im_pos
  simp only [inv_inv] at hB
  have hG : ∑ w : ZMod m, ψ w * (χ m * qSeries b (τ + ((((w.val : ℕ) : ℝ)) / m : ℝ))) =
      χ m * (gaussW ψ * qSeries (twist ψ⁻¹ b) τ) := by
    rw [← hB, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ ↦ by ring
  -- the `f` side: reindex by `u = -(wN)⁻¹`, then Lemma 4.3.10 for `ψ` and the relation `(A_ψ)`
  have hz0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hcpos : 0 < c := by positivity
  have hζ : 0 < (-1 / ((c : ℂ) * τ)).im := im_neg_one_div_pos hcpos τ.im_pos
  have hA4 := sum_transl_eq_gaussW_twist ψ hψp ha hζ
  have hF : ∑ u : ZMod m, ψ⁻¹ u * fricke k c
      (fun ζ ↦ qSeries a (ζ + ((u.val : ℝ) / m : ℝ))) τ =
      gaussW ψ⁻¹ * fricke k c (qSeries (twist ψ a)) τ := by
    unfold fricke
    beta_reduce
    have e : ∀ u : ZMod m, ψ⁻¹ u * (((√c : ℝ) * (τ : ℂ) : ℂ) ^ (-(k : ℤ)) *
        qSeries a (-1 / ((c : ℂ) * τ) + (((u.val : ℝ) / m : ℝ) : ℂ))) =
        ((√c : ℝ) * (τ : ℂ) : ℂ) ^ (-(k : ℤ)) * (ψ⁻¹ u *
        qSeries a (-1 / ((c : ℂ) * τ) + (((u.val : ℝ) / m : ℝ) : ℂ))) := fun u ↦ by ring
    simp only [e]
    rw [← Finset.mul_sum, hA4]
    ring
  have hreindex : ∑ w : ZMod m, ψ w * fricke k c
      (fun ζ ↦ qSeries a (ζ + (((((-(w * N)⁻¹ : ZMod m)).val : ℕ) : ℝ) / m : ℝ))) τ =
      ψ⁻¹ (-(N : ZMod m)) * ∑ u : ZMod m, ψ⁻¹ u * fricke k c
        (fun ζ ↦ qSeries a (ζ + ((u.val : ℝ) / m : ℝ))) τ := by
    rw [sum_units_eq _ (fun w hw ↦ by simp [ψ.map_nonunit hw]),
      sum_units_eq (fun u : ZMod m ↦ ψ⁻¹ u * fricke k c
        (fun ζ ↦ qSeries a (ζ + ((u.val : ℝ) / m : ℝ))) τ)
        (fun u hu ↦ by simp [(ψ⁻¹).map_nonunit hu]), Finset.mul_sum]
    rw [← Equiv.sum_comp (phiEq hmN)]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    have hspec := phiEq_spec hmN u
    have hinv : (-(((phiEq hmN u : (ZMod m)ˣ) : ZMod m) * N)⁻¹ : ZMod m) = u := by
      have hh : (((phiEq hmN u : (ZMod m)ˣ) : ZMod m) * N) * (-(u : ZMod m)) = 1 := by
        linear_combination -hspec
      rw [ZMod.inv_eq_of_mul_eq_one _ _ _ hh, neg_neg]
    rw [hinv]
    have hψu : ψ ((phiEq hmN u : (ZMod m)ˣ) : ZMod m) = ψ⁻¹ (-(N : ZMod m)) * ψ⁻¹ (u : ZMod m) := by
      rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', ← mul_inv, ← map_mul]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← map_mul, show ((phiEq hmN u : (ZMod m)ˣ) : ZMod m) * (-(N : ZMod m) * u) = 1 by
        linear_combination -hspec, map_one]
    rw [hψu]
    ring
  rw [hG, hreindex, hF, hAψ ψ hψp τ τ.im_pos]
  have hNunit : IsUnit (-(N : ZMod m)) :=
    ((ZMod.isUnit_iff_coprime N m).2 hmN.symm).neg
  have hψN : ψ⁻¹ (-(N : ZMod m)) * ψ (-(N : ZMod m)) = 1 := by
    rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply hNunit]
  have hW : gaussW ψ⁻¹ * (weilConstant χ ψ * qSeries (twist ψ⁻¹ b) τ) =
      χ m * ψ (-(N : ZMod m)) * gaussW ψ * qSeries (twist ψ⁻¹ b) τ := by
    unfold weilConstant; field_simp
  rw [hW]
  linear_combination (-(χ m * gaussW ψ * qSeries (twist ψ⁻¹ b) τ)) * hψN

lemma transl_mul_transl (x y : ℝ) : transl x * transl y = transl (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transl, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.GeneralLinearGroup.mkOfDetNeZero, add_comm]

lemma transl_zero' : transl 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transl, Matrix.GeneralLinearGroup.mkOfDetNeZero]

lemma sub_slash_aux (k : ℤ) (A : GL (Fin 2) ℝ) (f g : ℍ → ℂ) :
    (f - g) ∣[k] A = f ∣[k] A - g ∣[k] A := by
  rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ← sub_eq_add_neg]

lemma smul_slash_aux (k : ℤ) (c : ℂ) (f : ℍ → ℂ) (B : GL (Fin 2) ℝ) (hB : 0 < B.det.val) :
    (c • f) ∣[k] B = c • (f ∣[k] B) := by
  rw [ModularForm.smul_slash]
  have hB' : 0 < (B : Matrix (Fin 2) (Fin 2) ℝ).det := by simpa using hB
  simp [σ, hB']

lemma comb_slash_aux (k : ℤ) (c : ℂ) (f : ℍ → ℂ) (A B : GL (Fin 2) ℝ) (hB : 0 < B.det.val) :
    (c • f - f ∣[k] A) ∣[k] B = c • (f ∣[k] B) - f ∣[k] (A * B) := by
  rw [sub_slash_aux, smul_slash_aux k c f B hB, SlashAction.slash_mul]

lemma det_transl_pos (x : ℝ) : 0 < (transl x).det.val := by
  simp [transl, Matrix.det_fin_two]

lemma det_mapGL_pos (A : SL(2, ℤ)) : 0 < (Matrix.SpecialLinearGroup.mapGL ℝ A).det.val := by
  simp

lemma beta_trace_det {N m n : ℕ} (hm : 0 < m) (hn : 0 < n) {u v : ℤ}
    (h : (m : ℤ) * n - u * v * N = 1) (h2 : (n : ℤ) * m - (-u) * (-v) * N = 1) (x y : ℝ)
    (hx : x = -2 * v / m) (hy : y = -2 * v / n) :
    ((transl x * Matrix.SpecialLinearGroup.mapGL ℝ (gammaMV N n (-v) (-u) m h2) * transl y *
        Matrix.SpecialLinearGroup.mapGL ℝ (gammaW N m n u v h) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ).det = 1 ∧
    ((transl x * Matrix.SpecialLinearGroup.mapGL ℝ (gammaMV N n (-v) (-u) m h2) * transl y *
        Matrix.SpecialLinearGroup.mapGL ℝ (gammaW N m n u v h) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ).trace = ((4 / ((m : ℚ) * n) - 2 : ℚ) : ℝ) := by
  have hR : (m : ℝ) * n - u * v * N = 1 := by exact_mod_cast h
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hcoe : ((transl x * Matrix.SpecialLinearGroup.mapGL ℝ (gammaMV N n (-v) (-u) m h2) *
      transl y * Matrix.SpecialLinearGroup.mapGL ℝ (gammaW N m n u v h) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      !![1, x; 0, 1] * !![(n : ℝ), v; u * N, m] * !![1, y; 0, 1] * !![(m : ℝ), v; u * N, n] := by
    simp only [Units.val_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    have e1 : (gammaMV N n (-v) (-u) m h2).map (algebraMap ℤ ℝ) = !![(n : ℝ), v; u * N, m] := by
      rw [Matrix.SpecialLinearGroup.map_apply_coe]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [gammaMV]
    have e2 : (gammaW N m n u v h).map (algebraMap ℤ ℝ) = !![(m : ℝ), v; u * N, n] := by
      rw [Matrix.SpecialLinearGroup.map_apply_coe]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [gammaW]
    rw [e1, e2]
    simp [transl, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  rw [hcoe]
  have hX : (u : ℝ) * v * N = m * n - 1 := by linarith
  constructor
  · simp only [Matrix.det_mul, Matrix.det_fin_two_of]
    linear_combination ((m : ℝ) * n - v * (u * N)) * hR + hR
  · have e : ((n : ℝ) + x * u * N) * (m + y * u * N) + (v + x * m) * (u * N) +
        u * N * (v + y * n) + m * n =
        2 * m * n - 6 * ((u : ℝ) * v * N) + 4 * ((u : ℝ) * v * N) ^ 2 / (m * n) := by
      subst hx hy
      field_simp
      ring
    have e2 : 2 * (m : ℝ) * n - 6 * ((u : ℝ) * v * N) + 4 * ((u : ℝ) * v * N) ^ 2 / (m * n) =
        4 / (m * n) - 2 := by
      rw [hX]
      field_simp
      ring
    push_cast
    simp only [Matrix.trace_fin_two, Matrix.mul_fin_two]
    simp
    linear_combination e + e2

/-- **Miyake Lemma 4.3.14.** Under the standing hypotheses of Lemma 4.3.13, let $m$ and $n$ be odd
primes or $4$, both prime to $N$, and suppose $(A_\psi)$ holds (with $C_\psi$ as there) for every
primitive $\psi$ of conductor $m$ or $n$. Then
$$g|_k\gamma = \chi(m)\, g = \bar\chi(\gamma)\, g\qquad\text{for }
\gamma = \begin{pmatrix} m & v \\ uN & n\end{pmatrix} \in \Gamma_0(N)$$
(`Miyake.gammaW`; any integers $u, v$ with $mn - uvN = 1$; $\chi(m) = \bar\chi(n)$ since
$mn \equiv 1 \bmod N$).
Relation: same. -/
@[kb "miyake1989" "§4.3, Lemma 4.3.14, p. 126"]
theorem weil_lemma_4_3_14 {k N m n : ℕ} [NeZero m] [NeZero n] (hk : 0 < k) (hN : 0 < N)
    (χ : DirichletCharacter ℂ N) (hχ : χ (-1) = (-1) ^ k) {a b : ℕ → ℂ}
    (ha : CoeffGrowth a) (hb : CoeffGrowth b)
    (hA : ∀ z : ℂ, 0 < z.im → qSeries b z = fricke k N (qSeries a) z)
    (hm : IsOddPrimeOrFour m) (hn : IsOddPrimeOrFour n) (hmN : m.Coprime N) (hnN : n.Coprime N)
    (hAm : TwistedFrickeRelations k N m χ a b) (hAn : TwistedFrickeRelations k N n χ a b)
    (u v : ℤ) (h : (m : ℤ) * n - u * v * N = 1) :
    (fun τ : ℍ ↦ qSeries b τ) ∣[(k : ℤ)]
        Matrix.SpecialLinearGroup.mapGL ℝ (gammaW N m n u v h) =
      χ m • fun τ : ℍ ↦ qSeries b τ := by
  classical
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hm3 : 3 ≤ m := by
    rcases hm with ⟨hp, h2⟩ | rfl
    · have := hp.two_le; omega
    · norm_num
  have hn3 : 3 ≤ n := by
    rcases hn with ⟨hp, h2⟩ | rfl
    · have := hp.two_le; omega
    · norm_num
  have h' : (n : ℤ) * m - u * v * N = 1 := by rw [← h]; ring
  have h1 : (m : ℤ) * n - (-u) * (-v) * N = 1 := by rw [← h]; ring
  have h2 : (n : ℤ) * m - (-u) * (-v) * N = 1 := by rw [← h']; ring
  -- group identities
  have e1 : gammaMV N m (-v) (-u) n h1 = gammaW N m n u v h :=
    Subtype.ext (by ext i j; fin_cases i <;> fin_cases j <;> simp [gammaMV, gammaW])
  have e2 : gammaW N m n u v h * gammaMV N n v u m h' = 1 := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gammaMV, gammaW, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination h | ring
  have e3 : gammaMV N m v u n h * gammaMV N n (-v) (-u) m h2 = 1 := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gammaMV, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination h | ring
  have e2' : gammaMV N n v u m h' * gammaW N m n u v h = 1 := mul_eq_one_comm.1 e2
  have g2 : Matrix.SpecialLinearGroup.mapGL ℝ (gammaW N m n u v h) *
      Matrix.SpecialLinearGroup.mapGL ℝ (gammaMV N n v u m h') = 1 := by
    rw [← map_mul, e2, map_one]
  have g2' : Matrix.SpecialLinearGroup.mapGL ℝ (gammaMV N n v u m h') *
      Matrix.SpecialLinearGroup.mapGL ℝ (gammaW N m n u v h) = 1 := by
    rw [← map_mul, e2', map_one]
  have g3 : Matrix.SpecialLinearGroup.mapGL ℝ (gammaMV N m v u n h) *
      Matrix.SpecialLinearGroup.mapGL ℝ (gammaMV N n (-v) (-u) m h2) = 1 := by
    rw [← map_mul, e3, map_one]
  -- characters
  have hχmn : χ m * χ n = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod N) h
    push_cast at this
    rw [ZMod.natCast_self, mul_zero, sub_zero] at this
    rw [← map_mul, this, map_one]
  have hχn0 : χ n ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hχmn
    exact zero_ne_one hχmn
  -- Lemma 4.3.13 at modulus m and n
  have key_m : χ m • ((fun τ : ℍ ↦ qSeries b τ) ∣[(k : ℤ)] transl (((-v : ℤ) : ℝ) / m)) -
        (fun τ : ℍ ↦ qSeries b τ) ∣[(k : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ
          (gammaW N m n u v h) * transl (((-v : ℤ) : ℝ) / m)) =
      χ m • ((fun τ : ℍ ↦ qSeries b τ) ∣[(k : ℤ)] transl ((v : ℝ) / m)) -
        (fun τ : ℍ ↦ qSeries b τ) ∣[(k : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ
          (gammaMV N m v u n h) * transl ((v : ℝ) / m)) := by
    have := weil_lemma_4_3_13 hk hN χ hχ ha hb hA hm hmN hAm (-u) (-v) n u v n h1 h
    rw [e1] at this
    exact this
  have key_n : χ n • ((fun τ : ℍ ↦ qSeries b τ) ∣[(k : ℤ)] transl ((v : ℝ) / n)) -
        (fun τ : ℍ ↦ qSeries b τ) ∣[(k : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ
          (gammaMV N n v u m h') * transl ((v : ℝ) / n)) =
      χ n • ((fun τ : ℍ ↦ qSeries b τ) ∣[(k : ℤ)] transl (((-v : ℤ) : ℝ) / n)) -
        (fun τ : ℍ ↦ qSeries b τ) ∣[(k : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ
          (gammaMV N n (-v) (-u) m h2) * transl (((-v : ℤ) : ℝ) / n)) :=
    weil_lemma_4_3_13 hk hN χ hχ ha hb hA hn hnN hAn u v m (-u) (-v) m h' h2
  generalize hGdef : (fun τ : ℍ ↦ qSeries b τ) = G at key_m key_n ⊢
  have hGm : MDiff G := by rw [← hGdef]; exact mdifferentiable_qSeries hb
  generalize hγ : Matrix.SpecialLinearGroup.mapGL ℝ (gammaW N m n u v h) = γ at *
  generalize hγ' : Matrix.SpecialLinearGroup.mapGL ℝ (gammaMV N m v u n h) = γ' at *
  generalize hδ : Matrix.SpecialLinearGroup.mapGL ℝ (gammaMV N n v u m h') = δ at *
  generalize hδ' : Matrix.SpecialLinearGroup.mapGL ℝ (gammaMV N n (-v) (-u) m h2) = δ' at *
  have hβ := beta_trace_det hm0 hn0 h h2 (((-v : ℤ) : ℝ) / m + ((-v : ℤ) : ℝ) / m)
    (-((v : ℝ) / n) + -((v : ℝ) / n)) (by push_cast; ring) (by ring)
  rw [hδ', hγ] at hβ
  have hvm : (v : ℝ) / m = -(((-v : ℤ) : ℝ) / m) := by push_cast; ring
  rw [hvm] at key_m
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = ((-v : ℤ) : ℝ) / m := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (v : ℝ) / n := ⟨_, rfl⟩
  have hvn : ((-v : ℤ) : ℝ) / n = -y := by rw [hy]; push_cast; ring
  rw [hvn, ← hy] at key_n
  rw [← hx] at key_m hβ
  rw [← hy] at hβ
  have hdetδ : 0 < δ.det.val := by rw [← hδ]; exact det_mapGL_pos _
  have hdetδ' : 0 < δ'.det.val := by rw [← hδ']; exact det_mapGL_pos _
  have hP : (χ m • G - G ∣[(k : ℤ)] γ) ∣[(k : ℤ)] transl x =
      (χ m • G - G ∣[(k : ℤ)] γ') ∣[(k : ℤ)] transl (-x) := by
    rw [comb_slash_aux _ _ _ _ _ (det_transl_pos _), comb_slash_aux _ _ _ _ _ (det_transl_pos _)]
    exact key_m
  have hP' : (χ m • G - G ∣[(k : ℤ)] γ') = (χ m • G - G ∣[(k : ℤ)] γ) ∣[(k : ℤ)] transl (x + x) := by
    rw [← transl_mul_transl, SlashAction.slash_mul, hP, ← SlashAction.slash_mul,
      transl_mul_transl, neg_add_cancel, transl_zero', SlashAction.slash_one]
  have hQ : (χ n • G - G ∣[(k : ℤ)] δ) ∣[(k : ℤ)] transl y =
      (χ n • G - G ∣[(k : ℤ)] δ') ∣[(k : ℤ)] transl (-y) := by
    rw [comb_slash_aux _ _ _ _ _ (det_transl_pos _), comb_slash_aux _ _ _ _ _ (det_transl_pos _)]
    exact key_n
  have hQ' : (χ n • G - G ∣[(k : ℤ)] δ) = (χ n • G - G ∣[(k : ℤ)] δ') ∣[(k : ℤ)] transl (-y + -y) := by
    rw [← transl_mul_transl, SlashAction.slash_mul, ← hQ, ← SlashAction.slash_mul,
      transl_mul_transl, add_neg_cancel, transl_zero', SlashAction.slash_one]
  have hQP : (χ n • G - G ∣[(k : ℤ)] δ) =
      -(χ n) • ((χ m • G - G ∣[(k : ℤ)] γ) ∣[(k : ℤ)] δ) := by
    rw [comb_slash_aux _ _ _ _ _ hdetδ, g2, SlashAction.slash_one]
    funext τ
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination ((G ∣[(k : ℤ)] δ) τ) * hχmn
  have hQP' : (χ n • G - G ∣[(k : ℤ)] δ') =
      -(χ n) • ((χ m • G - G ∣[(k : ℤ)] γ') ∣[(k : ℤ)] δ') := by
    rw [comb_slash_aux _ _ _ _ _ hdetδ', g3, SlashAction.slash_one]
    funext τ
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination ((G ∣[(k : ℤ)] δ') τ) * hχmn
  rw [hQP, hQP', smul_slash_aux _ _ _ _ (det_transl_pos _)] at hQ'
  have hmain := smul_right_injective _ (neg_ne_zero.2 hχn0) hQ'
  rw [hP'] at hmain
  have hMD : MDiff (χ m • G - G ∣[(k : ℤ)] γ) :=
    (mdifferentiable_const.mul hGm).sub (hGm.slash _ _)
  generalize hPd : χ m • G - G ∣[(k : ℤ)] γ = P at hmain hMD
  have hfix : P = P ∣[(k : ℤ)] (transl (x + x) * δ' * transl (-y + -y) * γ) := by
    have := congrArg (fun F => F ∣[(k : ℤ)] γ) hmain
    simp only [← SlashAction.slash_mul] at this
    rw [g2', SlashAction.slash_one] at this
    exact this
  have hmn : (9 : ℚ) ≤ (m : ℚ) * n := by
    have h3m : (3 : ℚ) ≤ m := by exact_mod_cast hm3
    have h3n : (3 : ℚ) ≤ n := by exact_mod_cast hn3
    nlinarith
  have hpos : 0 < 4 / ((m : ℚ) * n) := by positivity
  have hlt : 4 / ((m : ℚ) * n) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have hposR : (0 : ℝ) < 4 / ((m : ℝ) * n) := by positivity
  have hltR : 4 / ((m : ℝ) * n) < 1 := by
    have : (4 / ((m : ℚ) * n) : ℚ) < 1 := hlt
    have h2 := (Rat.cast_lt (K := ℝ)).2 this
    push_cast at h2
    exact h2
  have ht2 : |(((4 / ((m : ℚ) * n) - 2 : ℚ)) : ℝ)| < 2 := by
    rw [abs_lt]
    push_cast
    constructor <;> linarith
  have htZ : ∀ z : ℤ, (4 / ((m : ℚ) * n) - 2 : ℚ) ≠ z := by
    intro z hz
    have h1 : (z : ℚ) < -1 := by linarith
    have h2 : -2 < (z : ℚ) := by linarith
    have h1' : z < -1 := by exact_mod_cast h1
    have h2' : -2 < z := by exact_mod_cast h2
    omega
  have hP0 : P = 0 :=
    eq_zero_of_slash_elliptic (by exact_mod_cast hk) hMD hβ.1 hβ.2 ht2 htZ hfix.symm
  rw [← hPd] at hP0
  exact (sub_eq_zero.1 hP0).symm

end Miyake

