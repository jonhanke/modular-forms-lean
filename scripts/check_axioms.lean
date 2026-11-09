/-
Prints the axioms of every headline theorem (run in CI: `lake env lean scripts/check_axioms.lean`).
Each must depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/
import Solution

#print axioms ModularFormsKB.Headlines.weil_riemannHypothesis_curves
#print axioms ModularFormsKB.Headlines.kronecker_modularEquation
#print axioms ModularFormsKB.Headlines.j_isIntegral_of_imaginaryQuadratic
#print axioms ModularFormsKB.Headlines.doublyPeriodic_sums
#print axioms ModularFormsKB.Headlines.prescribedDivisor
#print axioms ModularFormsKB.Headlines.ellipticFunctionField
#print axioms ModularFormsKB.Headlines.ellipticModuli_jLine
#print axioms ModularFormsKB.Headlines.cyclicModuli
#print axioms ModularFormsKB.Headlines.hecke_converse
#print axioms ModularFormsKB.Headlines.hecke_converse_levelOne
#print axioms ModularFormsKB.Headlines.weil_converse
#print axioms ModularFormsKB.Headlines.weil_converse_cusp
