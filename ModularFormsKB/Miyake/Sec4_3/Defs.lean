import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.ModularForms.Basic

/-!
# Miyake §4.3: definitions for the converse theorems

Definitions used to state Hecke's and Weil's converse theorems (Miyake, *Modular Forms*, 1989,
§4.3, pp. 116–128).

* `Miyake.CoeffGrowth a`: the coefficients satisfy $a_n = O(n^\nu)$ (Miyake (4.3.8)).
* `Miyake.qSeries a z`: $f(z) = \sum_{n \ge 0} a_n e^{2\pi i n z}$ (Miyake (4.3.7)).
* `Miyake.completedL N a s`: $\Lambda_N(s; f) = (2\pi/\sqrt N)^{-s}\,\Gamma(s)\,L(s; f)$
  (Miyake (4.3.12)).
* `Miyake.HeckeCondition k N C a b`: condition (B) of Miyake Theorems 4.3.5 and 4.3.6.
* `Miyake.fricke k N f`: $(f|_k\omega_N)(z) = (\sqrt N z)^{-k} f(-1/(Nz))$ in Miyake's normalization.
* `Miyake.twist ψ a`, `Miyake.twistedCompletedL`, `Miyake.TwistedHeckeCondition`: the twisted
  series of Miyake (4.3.17)–(4.3.19) and condition $(B_\psi)$ of Lemma 4.3.9.
* `Miyake.gaussW ψ`: the Gauss sum $W(\psi) = \sum_{u \bmod m} \psi(u) e^{2\pi i u/m}$.
* `Miyake.weilConstant χ ψ`: $C_\psi = \chi(m)\psi(-N)W(\psi)/W(\bar\psi)$ (Theorem 4.3.11).
* `Miyake.IsModularFormChar k N χ f`, `Miyake.IsCuspFormChar k N χ f`: $f \in M_k(N,\chi)$,
  $f \in S_k(N,\chi)$.

## Conventions

Functions are $\mathbb C \to \mathbb C$ and statements quantify over $z$ with $\operatorname{Im} z > 0$,
except where a Mathlib `ModularForm` is involved (functions $\mathbb H \to \mathbb C$). Matrix indices
are 0-based: Miyake's $d$ in $\gamma = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$ is `γ 1 1`.

Miyake's slash operator is $(f|_k\alpha)(z) = \det(\alpha)^{k/2} j(\alpha,z)^{-k} f(\alpha z)$; Mathlib's
`f ∣[k] α` uses $\det(\alpha)^{k-1}$ instead. The two agree on $\mathrm{SL}_2$, so only the Fricke
involution $\omega_N$ (determinant $N$) needs Miyake's normalization, which `Miyake.fricke` provides.
-/

open Complex Filter Asymptotics CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm CongruenceSubgroup

noncomputable section

namespace Miyake

/-- **Polynomial growth of coefficients** (Miyake (4.3.8)): there is a real $\nu$ with
$a_n = O(n^{\nu})$ as $n \to \infty$.

By Miyake Lemma 4.3.3 and (4.3.8), a holomorphic function on $\mathbb H$ with a Fourier expansion
$\sum_{n\ge0} a_n e^{2\pi i n z}$ satisfies Miyake's condition (4.3.7) exactly when its coefficients
satisfy this; the theorems of §4.3 are stated here in this coefficient form. Miyake also asks
$\nu > 0$, which is no restriction (enlarge $\nu$). -/
def CoeffGrowth (a : ℕ → ℂ) : Prop :=
  ∃ ν : ℝ, a =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ν

/-- **The $q$-series** $f(z) = \sum_{n \ge 0} a_n e^{2\pi i n z}$ of a coefficient sequence
$a : \mathbb N \to \mathbb C$ (Miyake (4.3.7)), as a function on $\mathbb C$ (a `tsum`, so it is $0$
where the series does not converge; it converges absolutely on $\operatorname{Im} z > 0$ when
`CoeffGrowth a`, see `Miyake.qSeries_lemma_4_3_3`). -/
def qSeries (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, a n * cexp (2 * π * I * n * z)

/-- **The completed Dirichlet series** of Miyake (4.3.12):
$$\Lambda_N(s; f) = \left(\frac{2\pi}{\sqrt N}\right)^{-s} \Gamma(s)\, L(s; f),\qquad
L(s;f) = \sum_{n \ge 1} a_n n^{-s}$$
for $N > 0$ real. $L(s; f)$ is Mathlib's `LSeries a s` (the term $n = 0$ is omitted); it is a
`tsum`, so the formula is meaningful only where the series converges ($\operatorname{Re} s > \nu+1$
under `CoeffGrowth a`). -/
def completedL (N : ℝ) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  ((2 * π / √N : ℝ) : ℂ) ^ (-s) * Gamma s * LSeries a s

/-- A function $\Phi : \mathbb C \to \mathbb C$ is **bounded on every vertical strip**
$\sigma_1 \le \operatorname{Re} s \le \sigma_2$. -/
def BoundedOnVerticalStrips (Φ : ℂ → ℂ) : Prop :=
  ∀ σ₁ σ₂ : ℝ, ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖Φ s‖ ≤ C

/-- **Condition (B) of Hecke's theorem** (Miyake Theorems 4.3.5 and 4.3.6), with a root number $C$:
there is an entire function $\Phi$, bounded on every vertical strip, such that
$$\Phi(s) = \Lambda_N(s; f) + \frac{a_0}{s} + \frac{C\,b_0}{k - s}\quad(\operatorname{Re} s \gg 0),
\qquad
\Phi(s) = C\,\Lambda_N(k - s; g) + \frac{a_0}{s} + \frac{C\,b_0}{k - s}\quad(\operatorname{Re} s \ll 0),$$
where $f$, $g$ have coefficients $a$, $b$.

This says exactly what Miyake's (B) says: $\Lambda_N(s;f)$ and $\Lambda_N(s;g)$ continue analytically
(meromorphically) to the whole plane, they satisfy $\Lambda_N(s; f) = C\,\Lambda_N(k - s; g)$, and
$\Lambda_N(s;f) + a_0/s + C b_0/(k-s)$ is entire and bounded on vertical strips. Theorem 4.3.5 has
$C = 1$; Theorem 4.3.6 has $C = i^k$. The half-planes are where the Dirichlet series converge; an
entire function is determined by its values on one half-plane, so "some $\sigma_0$" loses nothing. -/
def HeckeCondition (k N : ℝ) (C : ℂ) (a b : ℕ → ℂ) : Prop :=
  ∃ Φ : ℂ → ℂ, Differentiable ℂ Φ ∧ BoundedOnVerticalStrips Φ ∧ ∃ σ₀ : ℝ,
    (∀ s : ℂ, σ₀ < s.re → Φ s = completedL N a s + a 0 / s + C * b 0 / (k - s)) ∧
    (∀ s : ℂ, σ₀ < k - s.re → Φ s = C * completedL N b (k - s) + a 0 / s + C * b 0 / (k - s))

/-- **The Fricke transform in Miyake's normalization**:
$$(f|_k\omega_N)(z) = (\sqrt N z)^{-k} f\!\left(-\frac{1}{Nz}\right),\qquad
\omega_N = \begin{pmatrix} 0 & -1 \\ N & 0 \end{pmatrix},$$
for an integer weight $k$ and real $N > 0$. Miyake's slash is
$\det(\alpha)^{k/2} j(\alpha, z)^{-k} f(\alpha z)$, so this is $f|_k\omega_N$ in the book; Mathlib's
`f ∣[k] ω_N` (normalized by $\det^{k-1}$) is $N^{k/2 - 1}$ times it. -/
def fricke (k : ℤ) (N : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((√N : ℂ) * z) ^ (-k) * f (-1 / (N * z))

/-- **Twisted coefficients** (Miyake (4.3.17)): $n \mapsto \psi(n)\,a_n$ for a Dirichlet character
$\psi$ modulo $m$ (with $\psi(n) = 0$ when $\gcd(n, m) > 1$). The twisted function is
$f_\psi = $ `qSeries (twist ψ a)`. -/
def twist {m : ℕ} (ψ : DirichletCharacter ℂ m) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ψ n * a n

/-- **The twisted completed Dirichlet series** (Miyake (4.3.19)):
$$\Lambda_N(s; f, \psi) = \left(\frac{2\pi}{m\sqrt N}\right)^{-s} \Gamma(s)\, L(s; f, \psi),\qquad
L(s;f,\psi) = \sum_{n\ge1}\psi(n)a_n n^{-s},$$
where $m$ is the modulus of $\psi$ (its conductor, for the primitive characters of §4.3).
By (4.3.20) it equals $\Lambda_{Nm^2}(s; f_\psi)$. -/
def twistedCompletedL (N : ℝ) {m : ℕ} (ψ : DirichletCharacter ℂ m) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  ((2 * π / (m * √N) : ℝ) : ℂ) ^ (-s) * Gamma s * LSeries (twist ψ a) s

/-- **Condition $(B_\psi)$ of Miyake Lemma 4.3.9**: $\Lambda_N(s; f, \psi)$ continues to an entire
function, bounded on every vertical strip, satisfying
$$\Lambda_N(s; f, \psi) = i^k\, C\, \Lambda_N(k - s; g, \bar\psi).$$
Here $\bar\psi$ is `ψ⁻¹` (the inverse character, equal to the complex conjugate). -/
def TwistedHeckeCondition (k : ℕ) (N : ℝ) {m : ℕ} (ψ : DirichletCharacter ℂ m) (C : ℂ)
    (a b : ℕ → ℂ) : Prop :=
  ∃ Φ : ℂ → ℂ, Differentiable ℂ Φ ∧ BoundedOnVerticalStrips Φ ∧ ∃ σ₀ : ℝ,
    (∀ s : ℂ, σ₀ < s.re → Φ s = twistedCompletedL N ψ a s) ∧
    (∀ s : ℂ, σ₀ < k - s.re → Φ s = I ^ k * C * twistedCompletedL N ψ⁻¹ b (k - s))

/-- **The Gauss sum** $W(\psi) = \sum_{u \in \mathbb Z/m} \psi(u)\, e^{2\pi i u/m}$ of a Dirichlet
character modulo $m \ge 1$ (Miyake §3.1); Mathlib's `gaussSum ψ ZMod.stdAddChar`. -/
def gaussW {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) : ℂ :=
  gaussSum ψ ZMod.stdAddChar

/-- **Weil's constant** (Miyake Theorem 4.3.11):
$C_\psi = \chi(m)\,\psi(-N)\,W(\psi)/W(\bar\psi)$ for $\chi$ modulo $N$ and $\psi$ modulo $m$. -/
def weilConstant {N m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ m) : ℂ :=
  χ m * ψ (-(N : ZMod m)) * gaussW ψ / gaussW ψ⁻¹

/-- **$f \in M_k(N, \chi)$** (Miyake §4.3, after Lemma 4.3.1): $f$ is a modular form of weight $k$ for
$\Gamma_1(N)$ and $f|_k\gamma = \chi(d)\, f$ for every
$\gamma = \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \Gamma_0(N)$ (0-based: $d$ = `γ 1 1`).
Holomorphy at the cusps of $\Gamma_0(N)$ is that at the cusps of $\Gamma_1(N)$ (same cusps). Built on
Mathlib's `ModularForm`; Mathlib has no spaces with character. -/
def IsModularFormChar (k : ℤ) (N : ℕ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) : Prop :=
  (∃ F : ModularForm (Gamma1 N) k, ⇑F = f) ∧
    ∀ γ ∈ Gamma0 N, f ∣[k] γ = χ (γ 1 1 : ZMod N) • f

/-- **$f \in S_k(N, \chi)$**: as `Miyake.IsModularFormChar`, with a cusp form for $\Gamma_1(N)$. -/
def IsCuspFormChar (k : ℤ) (N : ℕ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) : Prop :=
  (∃ F : CuspForm (Gamma1 N) k, ⇑F = f) ∧
    ∀ γ ∈ Gamma0 N, f ∣[k] γ = χ (γ 1 1 : ZMod N) • f

/-- The translation matrix $\alpha(r) = \begin{pmatrix} 1 & r \\ 0 & 1 \end{pmatrix}$ of Miyake
§4.3 (before Lemma 4.3.10), in $\mathrm{GL}_2(\mathbb R)$; $(f|_k\alpha(r))(z) = f(z + r)$. -/
def transl (r : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, r; 0, 1] (by simp)

/-- The matrix $\gamma(m, v) = \begin{pmatrix} m & -v \\ -uN & n \end{pmatrix} \in \Gamma_0(N)$ of
Miyake §4.3 (before (4.3.23)), for integers with $mn - uvN = 1$. -/
def gammaMV (N m v u n : ℤ) (h : m * n - u * v * N = 1) : SL(2, ℤ) :=
  ⟨!![m, -v; -u * N, n], by simp [Matrix.det_fin_two]; linear_combination h⟩

/-- $m$ is an odd prime or $m = 4$ (the moduli used in Miyake Lemmas 4.3.13, 4.3.14 and
Theorem 4.3.15). -/
def IsOddPrimeOrFour (m : ℕ) : Prop :=
  (m.Prime ∧ m ≠ 2) ∨ m = 4

/-- The conditions of Miyake §4.3 (before Theorem 4.3.15) on a set $\mathcal M$ of moduli:
every element is an odd prime or $4$, (i) prime to $N$, and (ii) $\mathcal M$ meets every arithmetic
progression $A(c, d) = \{c + td : t \in \mathbb Z\}$ with $c, d$ coprime positive integers. -/
def IsWeilSet (N : ℕ) (M : Set ℕ) : Prop :=
  (∀ m ∈ M, IsOddPrimeOrFour m) ∧ (∀ m ∈ M, m.Coprime N) ∧
    ∀ c d : ℕ, 0 < c → 0 < d → c.Coprime d → ∃ m ∈ M, ∃ t : ℤ, (m : ℤ) = c + t * d

end Miyake
