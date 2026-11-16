import ModularFormsKB.Historical.Eisenstein.LatticeSums
import ModularFormsKB.Historical.Eisenstein.ThetaProducts
import ModularFormsKB.Historical.Eisenstein.WeierstrassRelations
import ModularFormsKB.Historical.Eisenstein.DirichletSeries
import ModularFormsKB.Historical.Eisenstein.ReducedMatrices
import ModularFormsKB.Historical.Eisenstein.GaussianLattices

/-!
# Eisenstein, *Mathematische Abhandlungen* (1847): historical library

Eisenstein's Crelle papers on elliptic functions, as reprinted in his *Mathematische Abhandlungen* (1847);
page numbers are those of the *Abhandlungen*.

* `LatticeSums`: *Beiträge* VI (*Genaue Untersuchung der unendlichen Doppelproducte …*, Crelle 35):
  discreteness of the lattice coset (§ 1), order-independent sums and Eisenstein's order of summation in
  weights one and two (§ 3), the cotangent formula and Theorem B (§ 4).
* `ThetaProducts`: Gauss's triangular-number identity (paper 5, p. 175) and the quasi-periodicity of the
  product `χ` (*Beiträge* VI, § 4, (VII.)).
* `WeierstrassRelations`: the lattice sums `(g, x)`, their differentiation rule, and the relations of `(3, x)`,
  `(4, x)`, `(5, x)`, `(7, x)` to Mathlib's `℘` (*Beiträge* VI, §§ 5 and 8).
-/
