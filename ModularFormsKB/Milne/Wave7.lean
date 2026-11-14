import ModularFormsKB.Milne.Wave7.OggTame
import ModularFormsKB.Milne.Wave7.HomLift
import ModularFormsKB.Milne.Wave7.LatticeIsogeny
import ModularFormsKB.Milne.Wave7.CMComplex

/-!
# Milne wave 7

* D116, the geometric conductor: the exponent is exactly `2` at a cusp for `p ≠ 2, 3` (Milne's "with equality unless
  `p = 2, 3`"), checked on Tau Ceti's Tate algorithm (`Wave7/OggTame.lean`).
* Proposition 3.3 with 3.12 between two lattices: morphisms `E(Λ) → E(Λ')` are `z ↦ αz` with `αΛ ⊆ Λ'`, and every
  such `α` gives one (`Wave7/HomLift.lean`, `Wave7/LatticeIsogeny.lean`).
* Propositions 12.20 and 12.21 over `ℂ` for the curves `E(Λ)` (`Wave7/CMComplex.lean`).
-/
