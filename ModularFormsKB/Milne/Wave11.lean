import ModularFormsKB.Milne.Wave11.PointPlace
import ModularFormsKB.Milne.Wave11.Surjective
import ModularFormsKB.Milne.Wave11.Bijection
import ModularFormsKB.Milne.Wave11.RiemannRochTransfer
import ModularFormsKB.Milne.Wave11.Separation
import ModularFormsKB.Milne.Wave11.X0RiemannRoch

/-!
# Milne wave 11

Riemann–Roch (Theorem 1.20) on a compact Riemann surface `X` from the algebraic Riemann–Roch theorem of Tau Ceti for
the function field `M(X)/ℂ`, through the bijection of `X` with the places of `M(X)`:

* `Wave11/PointPlace.lean`: the place `P_x` of a point; `ord_x = e_x · ord_{P_x}`.
* `Wave11/Surjective.lean`: every place of `M(X)/ℂ` is some `P_x` (approximation theorem and the fibre polynomial).
* `Wave11/Bijection.lean`: if `[M(X) : ℂ(f)] = valence f`, `x ↦ P_x` is bijective and `ord_{P_x} = ord_x`.
* `Wave11/RiemannRochTransfer.lean`: `riemannRoch_of_finrank_eq`.
* `Wave11/Separation.lean`: Riemann–Roch from the separation of points (the existence theorem).
* `Wave11/X0RiemannRoch.lean`: Riemann–Roch on `X₀(N)`, and Theorems 1.27, 2.22, 4.9 and Proposition 4.12 for
  `Γ₀(N)`, unconditional.
-/
