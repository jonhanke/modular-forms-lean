import ModularFormsKB.Milne.Wave15.Cochains
import ModularFormsKB.Milne.Wave15.Splitting
import ModularFormsKB.Milne.Wave15.Finiteness
import ModularFormsKB.Milne.Wave15.AdaptedSystem
import ModularFormsKB.Milne.Wave15.MittagLeffler
import ModularFormsKB.Milne.Wave15.Existence
import ModularFormsKB.Milne.Wave15.Corollaries
import ModularFormsKB.Milne.Wave15.PointsPlaces

/-!
# Milne wave 15

The existence theorem on every compact Riemann surface (Forster, §14), and with it Milne's Theorems 1.17 and 1.20 and
their consequences, unconditional:

* `Wave15/Cochains.lean`: disc systems; bounded holomorphic Čech cochains `C⁰(t)`, `C¹(t)`, cocycles `Z¹(t)`, the
  coboundary, and compactness of restriction (Montel).
* `Wave15/Splitting.lean`: a partition of unity in the charts, the smooth splitting `ξᵢⱼ = gⱼ - gᵢ`, the glued
  `(0,1)`-form and its Dolbeault solutions on each disc.
* `Wave15/Finiteness.lean`: `Z¹(1/2) × C⁰(1/4) → Z¹(1/4)` is onto; Schwartz's lemma gives
  `dim Z¹(1/4) / δC⁰(1/4) < ∞` (Forster 14.9).
* `Wave15/AdaptedSystem.lean`: a disc system adapted to a point.
* `Wave15/MittagLeffler.lean`: principal parts at a point as bounded cocycles.
* `Wave15/Existence.lean`: a meromorphic function with a single prescribed pole (Forster 14.12), separation of points,
  `existsNonconstantStatement` (Theorem 1.17), `riemannRochStatement` (Theorem 1.20).
* `Wave15/Corollaries.lean`: Proposition 1.12 (b), Theorem 1.17 (function field), Corollaries 1.21 and 1.22,
  Theorem 1.27 for every compact Riemann surface.
* `Wave15/PointsPlaces.lean`: Theorem 0.5 (b), points of `X` and places of `M(X)/ℂ` (`places`).
-/
