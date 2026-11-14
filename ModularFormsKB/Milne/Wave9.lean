import ModularFormsKB.Milne.Wave9.PuncturedSphere
import ModularFormsKB.Milne.Wave9.HomDescent
import ModularFormsKB.Milne.Wave9.ClassGroupActionDescent
import ModularFormsKB.Milne.Wave9.ClassGroupActionAll

/-!
# Milne wave 9

* The named topological input `PuncturedSphereFiniteCWType` (the Riemann sphere minus finitely many points has finite
  CW type) is proved, through a triangulation of the sphere; Theorem 2.22 / Remark 1.28 in punctured
  Euler-characteristic form become unconditional (`Wave9/PuncturedSphere.lean`).
* Morphisms of elliptic curves descend along extensions of algebraically closed fields of characteristic zero
  (`Wave9/FixedDescent.lean`, `Wave9/HomDescent.lean`): Tau Ceti's Galois descent of isogenies redone under the
  fixed-field hypothesis alone, and rigidity on torsion points.
* Proposition 12.21 in the corrected named form `ClassGroupActionPrincipalNormalized` for every algebraically closed
  field of characteristic zero embeddable in `ℂ`, i.e. of cardinality at most that of `ℂ`, for example `ℚ̄`
  (`Wave9/ClassGroupActionDescent.lean`), then for every algebraically closed field of characteristic zero: the named
  statement is proved (`classGroupActionPrincipalNormalized`, `Wave9/ClassGroupActionAll.lean`).
-/
