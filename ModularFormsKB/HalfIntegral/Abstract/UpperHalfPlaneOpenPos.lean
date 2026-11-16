/-
# Nonempty open subsets of the upper half-plane have positive invariant volume

The instance `IsOpenPosMeasure (volume : Measure ℍ)` for Mathlib's invariant measure `dx dy / y²` is
Tau Ceti's (`TauCeti.Analysis.Complex.UpperHalfPlane.Measure`). This file used to declare its own copy as a global
instance; since Tau Ceti has it, the copy is removed (release 0.5.0: no global instance duplicating one of a
dependency) and this module only imports Tau Ceti's.
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import TauCeti.Analysis.Complex.UpperHalfPlane.Measure
