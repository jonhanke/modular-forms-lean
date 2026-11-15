import TauCeti.NumberTheory.NumberField.Quadratic.DedekindZeta
import ModularFormsKB.Citation
/-!
# Miyake, Theorem 3.3.3: the Dedekind zeta function of a quadratic field

Miyake, *Modular Forms* (Springer 1989), §3.3, p. 94, Theorem 3.3.3: for a quadratic field `K`
of discriminant `d` with Kronecker symbol `χ_d`, `ζ_K(s) = ζ(s) L(s, χ_d)`.

**Status: proved, as a bridge to Tau Ceti main** (`TauCeti.NumberField.dedekindZeta_eq_riemannZeta_mul_LFunction`,
file `NumberTheory/NumberField/Quadratic/DedekindZeta.lean`). Tau Ceti's `χ_d` is
`TauCeti.Multiquadratic.fundamentalDiscriminantChar (discr K)`, the primitive quadratic Dirichlet
character of conductor `|d|`, which is the Kronecker symbol `(d / ·)`
(`TauCeti.Multiquadratic.fundamentalDiscriminantChar_intCast`). The identity is proved on the
half plane `Re s > 1` where both sides are given by their Dirichlet series; Miyake states it
there too and then reads it as an identity of meromorphic functions. The second form below, the
coefficient identity `#{𝔞 : N𝔞 = n} = Σ_{m ∣ n} χ_d(m)`, is the content of Miyake's proof.

Tau Ceti main has the statement, so no port is needed.
-/

open NumberField TauCeti.Multiquadratic

namespace ModularFormsKB.Miyake.Sec3_3

variable {K : Type*} [Field K] [NumberField K]

/-- **Miyake, Theorem 3.3.3**: for a quadratic field `K` of discriminant `d`,
`ζ_K(s) = ζ(s) L(s, χ_d)` for `Re s > 1`, where `χ_d` is the Kronecker character of `d`. -/
@[kb "miyake1989" "Theorem 3.3.3, p. 94"]
theorem theorem_3_3_3 (hK : Module.finrank ℚ K = 2) {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction
      ((fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK)).ringHomComp
        (Int.castRingHom ℂ)) s :=
  TauCeti.NumberField.dedekindZeta_eq_riemannZeta_mul_LFunction hK hs

/-- **Miyake, Theorem 3.3.3**, coefficient form (the content of the proof): the number of
integral ideals of `𝓞 K` of norm `n ≠ 0` is `Σ_{m ∣ n} χ_d(m)`. -/
@[kb "miyake1989" "Theorem 3.3.3, p. 94 (Dirichlet coefficients)"]
theorem theorem_3_3_3_coeff (hK : Module.finrank ℚ K = 2) {n : ℕ} (hn : n ≠ 0) :
    (TauCeti.dedekindZetaCoeff K n : ℤ) =
      ∑ m ∈ n.divisors, fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) m :=
  TauCeti.NumberField.dedekindZetaCoeff_eq_sum_divisors hK hn

end ModularFormsKB.Miyake.Sec3_3
