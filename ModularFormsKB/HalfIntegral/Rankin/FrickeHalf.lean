/-
# The Fricke involution $W_{4N}$ on $S_{k+1/2}(4N,\chi)$ for the theta multiplier

Item (iii) of loose end LE-MF-0256.

For $N \ge 1$ put
$$(f|W_{4N})(\tau) = (-2iN\tau)^{-k-1/2}\,f\Big(-\frac1{4N\tau}\Big) = (f|W_4)(N\tau)$$
(`frickeHalf`, `frickeHalf_eq`; the factor $(-2iN\tau)^{-k-1/2}$ is $N^{-(2k+1)/4}$ times the usual
$(-2i\sqrt N\tau)^{-k-1/2}$, a nonzero constant; principal branches). The main result is `frickeHalf_mem_cuspForms`:
$$f \in S_{k+1/2}(4N,\chi) \implies f|W_{4N} \in S_{k+1/2}\big(4N,\ \bar\chi\cdot(\tfrac{4N}{\cdot})\big)$$
for the theta multiplier (`frickeChar N χ` $= \chi^{-1}$ times Tau Ceti's Kronecker character of $4N$). Hence $f|W_{4N}$
has a $q$-expansion $b$ with $b(0) = 0$ and polynomial growth (`exists_hasQExp_frickeHalf`).

**Proof.** Since $W_{4N}\tau = W_4(N\tau)$, everything reduces to the level-4 computations of `KohnenW4U4.lean`. For
$\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \Gamma_0(4N)$, $c = 4Nc_0$, the matrix
$\gamma_N = \begin{pmatrix}a&Nb\\4c_0&d\end{pmatrix} \in \Gamma_0(4)$ satisfies $N(\gamma\tau) = \gamma_N(N\tau)$
(`exists_gammaN`), and $\gamma_N^* = W_4\gamma_NW_4^{-1}$ has bottom row $(-4Nb, a)$, so lies in $\Gamma_0(4N)$. The factor
identity of $W_4$ (`thetaMult_fricke_factor`, from the Fricke law of $\theta$) then gives
$(f|W_{4N})(\gamma\tau) = \chi(a)\,j(\gamma_N, N\tau)^{2k+1}(f|W_{4N})(\tau)$ (`kohnenW4_smul_of`), and
$j(\gamma_N, N\tau) = \big(\tfrac N{|d|}\big)j(\gamma,\tau)$ (`thetaMult_gammaN`: Shimura's symbol is multiplicative in the
top entry, `shimuraSym_natMul`), with $\chi(a) = \bar\chi(d)$. The cusp condition follows from that of $f|W_4$
(`kohnenW4_zero`) and the decomposition `affPt_decomp`.

**Index shift.** Matrix entries are 0-based: `γ 1 0` is $c$, `γ 1 1` is $d$.
-/
import ModularFormsKB.HalfIntegral.KohnenW4U4
import ModularFormsKB.HalfIntegral.HeckeBound
import ModularFormsKB.HalfIntegral.HeckeOperator
import ModularFormsKB.HalfIntegral.Rankin.Assembly

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup
open scoped Manifold

local notation "ℍ" => UpperHalfPlane

namespace FrickeHalf

/-- The point $N\tau$ (for $N = 0$, the point $\tau$). -/
noncomputable def scalePt (N : ℕ) (τ : ℍ) : ℍ := affPt (Nat.toPNat' N) 1 0 τ

lemma coe_scalePt {N : ℕ} (hN : 0 < N) (τ : ℍ) : (scalePt N τ : ℂ) = N * τ := by
  simp [scalePt, Nat.toPNat'_coe, hN]

lemma mdiff_scalePt (N : ℕ) : MDiff (scalePt N) := mdiff_affPt _ _ _

end FrickeHalf

open FrickeHalf

/-- **The Fricke involution in weight $k + \tfrac12$, level $4N$:**
$(f|W_{4N})(\tau) = (f|W_4)(N\tau) = (-2iN\tau)^{-k-1/2}f(-1/(4N\tau))$ (`frickeHalf_eq`). -/
noncomputable def frickeHalf (k N : ℕ) (f : ℍ → ℂ) : ℍ → ℂ := fun τ ↦ kohnenW4 k f (scalePt N τ)

theorem frickeHalf_eq {k N : ℕ} (hN : 0 < N) (f : ℍ → ℂ) (τ : ℍ) :
    frickeHalf k N f τ = (-2 * I * (N * τ)) ^ (-((k : ℂ) + 1 / 2)) * f (frickePt (scalePt N τ)) ∧
      ((frickePt (scalePt N τ) : ℍ) : ℂ) = -1 / (4 * N * τ) := by
  refine ⟨?_, ?_⟩
  · simp only [frickeHalf, kohnenW4, coe_scalePt hN]
  · rw [coe_frickePt, coe_scalePt hN, mul_assoc]

namespace FrickeHalf

lemma four_mul_modEq (N : ℕ) : (4 * N : ℤ) ≡ 0 [ZMOD 4] ∨ (4 * N : ℤ) ≡ 1 [ZMOD 4] :=
  Or.inl (Int.modEq_zero_iff_dvd.2 ⟨N, rfl⟩)

lemma natAbs_four_mul (N : ℕ) : (4 * N : ℤ).natAbs = 4 * N := by
  rw [Int.natAbs_mul]; simp

/-- The Kronecker character $\big(\tfrac{4N}{\cdot}\big)$ modulo $4N$ (trivial for $N = 0$). -/
noncomputable def kronFour (N : ℕ) : DirichletCharacter ℂ (4 * N) :=
  if h : (4 * N : ℤ) = 0 then 1 else
    DirichletCharacter.changeLevel (by rw [natAbs_four_mul])
      (TauCeti.kroneckerChar ℂ (4 * N : ℤ) (four_mul_modEq N) h)

end FrickeHalf

/-- **The character of $f|W_{4N}$:** $\bar\chi\cdot\big(\tfrac{4N}{\cdot}\big)$, that is $\chi^{-1}$ times the Kronecker
character of $4N$. On odd $d$ prime to $N$ it is $\chi(d)^{-1}\big(\tfrac N{|d|}\big)$ (`frickeChar_intCast`). -/
noncomputable def frickeChar (N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) : DirichletCharacter ℂ (4 * N) :=
  χ⁻¹ * kronFour N

namespace FrickeHalf

lemma jacobiSym_four_mul {N : ℕ} {m : ℕ} (hm : Odd m) : jacobiSym (4 * N : ℤ) m = jacobiSym N m := by
  have hg : (2 : ℤ).gcd m = 1 := by
    have : ¬ (2 ∣ m) := by
      have := Nat.odd_iff.mp hm; omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr this
  rw [show (4 * N : ℤ) = 2 ^ 2 * N by ring, jacobiSym.mul_left, jacobiSym.sq_one' hg, one_mul]

end FrickeHalf

theorem frickeChar_intCast {N : ℕ} (hN : 0 < N) (χ : DirichletCharacter ℂ (4 * N)) (d : ℤ) (hd : Odd d)
    (hcop : IsCoprime d (4 * N : ℕ)) :
    frickeChar N χ (d : ZMod (4 * N)) = (χ (d : ZMod (4 * N)))⁻¹ * (jacobiSym N d.natAbs : ℂ) := by
  have h0 : (4 * N : ℤ) ≠ 0 := by positivity
  unfold frickeChar kronFour
  rw [MulChar.mul_apply, dif_neg h0, MulChar.inv_apply_eq_inv',
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcop, TauCeti.kroneckerChar_intCast,
    TauCeti.kroneckerSym_of_odd _ hd, jacobiSym_four_mul (Int.natAbs_odd.mpr hd)]
  have : ¬ ((4 * N : ℤ) < 0 ∧ d < 0) := fun h ↦ by have := h.1; omega
  simp [this]

namespace FrickeHalf

/-- **Shimura's symbol is multiplicative in the top entry** for a positive factor:
$\big(\tfrac{nc}d\big) = \big(\tfrac n{|d|}\big)\big(\tfrac cd\big)$. -/
lemma shimuraSym_natMul {n : ℕ} (hn : 0 < n) (c d : ℤ) :
    shimuraSym (n * c) d = jacobiSym n d.natAbs * shimuraSym c d := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hneg : (n : ℤ) * c < 0 ↔ c < 0 :=
    ⟨fun h ↦ by by_contra h'; push_neg at h'; nlinarith, fun h ↦ by nlinarith⟩
  unfold shimuraSym
  simp only [hneg, jacobiSym.mul_left]
  split_ifs <;> ring

lemma gamma0_dvd {M : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : (M : ℤ) ∣ γ 1 0 := by
  rw [Gamma0_mem] at hγ
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp hγ

lemma mem_gamma0_of_dvd {M : ℕ} {γ : SL(2, ℤ)} (h : (M : ℤ) ∣ γ 1 0) : γ ∈ Gamma0 M := by
  rw [Gamma0_mem]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr h

/-- **$\gamma_N$:** for $\gamma \in \Gamma_0(4N)$, $\gamma_N = \begin{pmatrix}a&Nb\\c/N&d\end{pmatrix} \in \Gamma_0(4)$ with
$N(\gamma\tau) = \gamma_N(N\tau)$. -/
lemma exists_gammaN {N : ℕ} (hN : 0 < N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (4 * N)) :
    ∃ γN : SL(2, ℤ), γN ∈ Gamma0 4 ∧ γN 0 0 = γ 0 0 ∧ γN 0 1 = N * γ 0 1 ∧ (N : ℤ) * γN 1 0 = γ 1 0 ∧
      γN 1 1 = γ 1 1 ∧ ∀ τ : ℍ, scalePt N (γ • τ) = γN • scalePt N τ := by
  obtain ⟨c0, hc0⟩ := gamma0_dvd hγ
  push_cast at hc0
  have hdet := det_entries γ
  rw [hc0] at hdet
  let γN : SL(2, ℤ) := ⟨!![γ 0 0, N * γ 0 1; 4 * c0, γ 1 1], by
    simp [Matrix.det_fin_two]; linear_combination hdet⟩
  have e00 : γN 0 0 = γ 0 0 := by simp [γN]
  have e01 : γN 0 1 = N * γ 0 1 := by simp [γN]
  have e10 : γN 1 0 = 4 * c0 := by simp [γN]
  have e11 : γN 1 1 = γ 1 1 := by simp [γN]
  refine ⟨γN, mem_gamma0_of_dvd (by rw [e10]; push_cast; exact ⟨c0, rfl⟩), e00, e01,
    by rw [e10, hc0]; ring, e11, fun τ ↦ ?_⟩
  have hs := cd_ne_zero γ τ
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  ext
  rw [coe_scalePt hN, UpperHalfPlane.coe_specialLinearGroup_apply,
    UpperHalfPlane.coe_specialLinearGroup_apply, coe_scalePt hN]
  simp only [eq_intCast, Complex.ofReal_intCast]
  rw [e00, e01, e10, e11]
  have hc : ((γ 1 0 : ℤ) : ℂ) = 4 * N * c0 := by exact_mod_cast hc0
  rw [hc] at hs ⊢
  have hs' : ((4 * c0 : ℤ) : ℂ) * (N * (τ : ℂ)) + γ 1 1 ≠ 0 := by
    push_cast; convert hs using 1; ring
  rw [mul_div_assoc', div_eq_div_iff hs hs']
  push_cast
  ring

/-- **The theta multiplier of $\gamma_N$ at $N\tau$:** $j(\gamma_N, N\tau) = \big(\tfrac N{|d|}\big)j(\gamma, \tau)$. -/
lemma thetaMult_gammaN {N : ℕ} (hN : 0 < N) {γ γN : SL(2, ℤ)} (h10 : (N : ℤ) * γN 1 0 = γ 1 0)
    (h11 : γN 1 1 = γ 1 1) (hcop : IsCoprime (γ 1 0) (γ 1 1)) (τ : ℍ) :
    thetaMult γN ((scalePt N τ : ℍ) : ℂ) = (jacobiSym N (γ 1 1).natAbs : ℂ) * thetaMult γ τ := by
  have hJ : (jacobiSym N (γ 1 1).natAbs : ℂ) ^ 2 = 1 := by
    have hg : (N : ℤ).gcd (γ 1 1).natAbs = 1 := by
      have : IsCoprime (N : ℤ) (γ 1 1) := by
        rw [← h10] at hcop; exact hcop.of_mul_left_left
      simpa [Int.gcd, Int.natAbs_abs] using Int.isCoprime_iff_gcd_eq_one.mp this
    exact_mod_cast jacobiSym.sq_one hg
  unfold thetaMult thetaMultCD
  rw [← h10, h11, shimuraSym_natMul hN, coe_scalePt hN]
  push_cast
  have : ((γN 1 0 : ℤ) : ℂ) * (N * (τ : ℂ)) = (N : ℂ) * (γN 1 0 : ℂ) * τ := by ring
  rw [this]
  linear_combination -(epsD (γ 1 1))⁻¹ * (shimuraSym (γN 1 0) (γ 1 1) : ℂ) *
    ((N : ℂ) * (γN 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ (1 / 2 : ℂ) * hJ

end FrickeHalf

/-- **The $W_4$ law with a constant:** if $f(\gamma^*W\tau) = C\,j(\gamma^*,W\tau)^{2k+1}f(W\tau)$ for
$\gamma^* = W\gamma W^{-1}$, then $(f|W_4)(\gamma\tau) = C\,j(\gamma,\tau)^{2k+1}(f|W_4)(\tau)$. -/
lemma kohnenW4_smul_of (k : ℕ) {f : ℍ → ℂ} {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma0 4) (hγ' : γ' ∈ Gamma0 4)
    (hpt : ∀ τ : ℍ, frickePt (γ • τ) = γ' • frickePt τ) (C : ℂ) (τ : ℍ)
    (hf : f (γ' • frickePt τ) = C * thetaMult γ' ((frickePt τ : ℍ) : ℂ) ^ (2 * k + 1) * f (frickePt τ)) :
    kohnenW4 k f (γ • τ) = C * thetaMult γ (τ : ℂ) ^ (2 * k + 1) * kohnenW4 k f τ := by
  have key := thetaMult_fricke_factor hγ hγ' hpt τ
  have ha := cpow_half_fricke_ne_zero τ
  have hP := cpow_half_fricke_ne_zero (γ • τ)
  unfold kohnenW4
  rw [hpt τ, hf, cpow_neg_half_pow, cpow_neg_half_pow]
  have hk := congrArg (fun x : ℂ ↦ x ^ (2 * k + 1)) key
  simp only [mul_pow] at hk
  generalize thetaMult γ' ((frickePt τ : ℍ) : ℂ) = J at *
  generalize thetaMult γ (τ : ℂ) = j at *
  generalize (-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ) = a at *
  generalize (-2 * I * ((γ • τ : ℍ) : ℂ)) ^ (1 / 2 : ℂ) = P at *
  generalize f (frickePt τ) = fW
  field_simp
  linear_combination C * fW * hk

/-- **The transformation law of $f|W_{4N}$:** for $f$ with the law of $S_{k+1/2}(4N,\chi)$, $f|W_{4N}$ has the law with
character `frickeChar N χ`. -/
theorem frickeHalf_transforms {k N : ℕ} (hN : 0 < N) {χ : DirichletCharacter ℂ (4 * N)} {f : ℍ → ℂ}
    (hf : thetaMultiplierSystem.Transforms k N χ f) :
    thetaMultiplierSystem.Transforms k N (frickeChar N χ) (frickeHalf k N f) := by
  intro γ hγ τ
  obtain ⟨γN, hγN, h00, h01, h10, h11, hsc⟩ := exists_gammaN hN hγ
  obtain ⟨γ', hγ', h'10, h'11, hpt⟩ := exists_gamma_star hγN
  have hγ'N : γ' ∈ Gamma0 (4 * N) :=
    mem_gamma0_of_dvd (by rw [h'10, h01]; push_cast; exact ⟨-(γ 0 1), by ring⟩)
  have hdet := det_entries γ
  have hcop : IsCoprime (γ 1 0) (γ 1 1) := ⟨-(γ 0 1), γ 0 0, by linear_combination hdet⟩
  have hdodd : Odd (γ 1 1) := by
    obtain ⟨c0, hc0⟩ := gamma0_dvd hγ
    rw [hc0] at hdet; push_cast at hdet
    have hodd : Odd (γ 0 0 * γ 1 1) := ⟨2 * N * c0 * γ 0 1, by linear_combination hdet⟩
    exact (Int.odd_mul.mp hodd).2
  have hdcop : IsCoprime (γ 1 1) ((4 * N : ℕ) : ℤ) := by
    obtain ⟨c0, hc0⟩ := gamma0_dvd hγ
    exact ⟨γ 0 0, -(γ 0 1) * c0, by rw [hc0] at hdet; linear_combination hdet⟩
  -- χ(a) = χ(d)⁻¹
  have hχ : χ ((γ 0 0 : ℤ) : ZMod (4 * N)) * χ ((γ 1 1 : ℤ) : ZMod (4 * N)) = 1 := by
    rw [← map_mul]
    have : ((γ 0 0 : ℤ) : ZMod (4 * N)) * ((γ 1 1 : ℤ) : ZMod (4 * N)) = 1 := by
      obtain ⟨c0, hc0⟩ := gamma0_dvd hγ
      have e : γ 0 0 * γ 1 1 = 1 + ((4 * N : ℕ) : ℤ) * (c0 * γ 0 1) := by
        rw [hc0] at hdet; push_cast at hdet ⊢; linear_combination hdet
      have h4 : ((4 * N : ℕ) : ZMod (4 * N)) = 0 := ZMod.natCast_self _
      have := congrArg (fun x : ℤ ↦ (x : ZMod (4 * N))) e
      simp only [Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_natCast, h4, zero_mul, add_zero] at this
      exact this
    rw [this, map_one]
  have hlaw := hf γ' hγ'N (frickePt (scalePt N τ))
  rw [h'11, h00] at hlaw
  have step := kohnenW4_smul_of k hγN hγ' hpt _ (scalePt N τ) hlaw
  have hj := thetaMult_gammaN hN h10 h11 hcop τ
  show kohnenW4 k f (scalePt N (γ • τ)) = _ * thetaMult γ (τ : ℂ) ^ (2 * k + 1) * kohnenW4 k f (scalePt N τ)
  rw [hsc τ, step, hj, frickeChar_intCast hN χ _ hdodd hdcop]
  have hJ2 : (jacobiSym N (γ 1 1).natAbs : ℂ) ^ (2 * k + 1) = jacobiSym N (γ 1 1).natAbs := by
    have hg : (N : ℤ).gcd (γ 1 1).natAbs = 1 := by
      have : IsCoprime (N : ℤ) (γ 1 1) := by
        have h := hdcop.symm
        push_cast at h
        exact h.of_mul_left_right
      simpa [Int.gcd, Int.natAbs_abs] using Int.isCoprime_iff_gcd_eq_one.mp this
    have h1 : (jacobiSym N (γ 1 1).natAbs : ℂ) ^ 2 = 1 := by exact_mod_cast jacobiSym.sq_one hg
    rw [pow_succ, pow_mul, h1, one_pow, one_mul]
  have hχ' : χ ((γ 0 0 : ℤ) : ZMod (4 * N)) = (χ ((γ 1 1 : ℤ) : ZMod (4 * N)))⁻¹ :=
    eq_inv_of_mul_eq_one_left hχ
  rw [mul_pow, hJ2, hχ']
  ring

theorem frickeHalf_mdiff (k N : ℕ) {f : ℍ → ℂ} (hf : MDiff f) : MDiff (frickeHalf k N f) :=
  (kohnenW4_mdiff k hf).comp (mdiff_scalePt N)

theorem frickeHalf_zero {k N : ℕ} {f : ℍ → ℂ}
    (hf : ∀ γ : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty (Abstract.cuspNorm k f γ)) (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty (Abstract.cuspNorm k (frickeHalf k N f) γ) := by
  obtain ⟨η, A', D', B', hsm, hden⟩ := affPt_decomp (Nat.toPNat' N) 1 0 γ
  have hD' : (0 : ℝ) < ((D' : ℕ) : ℝ) := by exact_mod_cast D'.pos
  refine zero_of_comp_W (((D' : ℕ) : ℝ) ^ (-((k : ℝ) + 1 / 2))) (by positivity) A' D' B'
    (kohnenW4_zero k hf η) (fun τ ↦ by unfold Abstract.cuspNorm; positivity) fun τ ↦ ?_
  have h := hden τ
  simp only [PNat.one_coe, Nat.cast_one, one_mul] at h
  have hn := congrArg norm h
  rw [norm_mul] at hn
  simp only [Complex.norm_natCast] at hn
  have hw : 0 < ‖(η 1 0 : ℂ) * (affPt A' D' B' τ : ℂ) + η 1 1‖ := norm_pos_iff.mpr (cd_ne_zero η _)
  unfold Abstract.cuspNorm
  show _ * ‖kohnenW4 k f (affPt (Nat.toPNat' N) 1 0 (γ • τ))‖ = _
  rw [hsm τ, ← hn, Real.mul_rpow hD'.le hw.le]
  ring

/-- **Row 5: $W_{4N}$ maps $S_{k+1/2}(4N,\chi)$ to $S_{k+1/2}(4N,\bar\chi(\tfrac{4N}\cdot))$** for the theta multiplier,
$N \ge 1$ (Shimura 1973 `shimura1973`, §1, the operator W(4N) [unverified]). -/
@[kb "shimura1973" "§1: f|W(4N) lies in S_{k+1/2}(4N, conj(chi) (4N/.)) for the theta multiplier [unverified]"]
theorem frickeHalf_mem_cuspForms {k N : ℕ} (hN : 0 < N) {χ : DirichletCharacter ℂ (4 * N)} {f : ℍ → ℂ}
    (hf : f ∈ thetaMultiplierSystem.cuspForms k N χ) :
    frickeHalf k N f ∈ thetaMultiplierSystem.cuspForms k N (frickeChar N χ) :=
  ⟨frickeHalf_mdiff k N hf.holo, frickeHalf_transforms hN hf.transforms, frickeHalf_zero hf.zero_at_cusps⟩

/-- **The $q$-expansion of $f|W_{4N}$:** for $f \in S_{k+1/2}(4N,\chi)$, $N \ge 1$, the form $f|W_{4N}$ has a $q$-expansion
$b$ with $b(0) = 0$ and $b(n) = O(n^{(2k+1)/4})$ (Hecke's bound, `heckeCoeffBound`). -/
theorem exists_hasQExp_frickeHalf {k N : ℕ} (hN : 0 < N) {χ : DirichletCharacter ℂ (4 * N)} {f : ℍ → ℂ}
    (hf : f ∈ thetaMultiplierSystem.cuspForms k N χ) :
    ∃ b : ℕ → ℂ, Abstract.HasQExp (frickeHalf k N f) b ∧ b 0 = 0 ∧ CoeffGrowth b := by
  have hW := frickeHalf_mem_cuspForms hN hf
  obtain ⟨b, hb⟩ := MultiplierSystem.exists_hasQExp_of_mem_cuspForms _ hW
  refine ⟨b, hb, MultiplierSystem.coeff_zero_eq_zero _ hW hb, ?_⟩
  obtain ⟨C, hC⟩ := (heckeCoeffBound thetaMultiplierSystem k N (frickeChar N χ) hN).bound _ hW b hb
  refine ⟨((2 * k + 1 : ℕ) : ℝ) / 4, Asymptotics.IsBigO.of_bound C ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [Real.norm_of_nonneg (by positivity)]
  exact hC n hn

end ModularFormsKB.HalfIntegral
