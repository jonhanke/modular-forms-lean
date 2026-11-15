import ModularFormsKB.Milne.Wave13.PolePoincare
import ModularFormsKB.Milne.Wave13.PoleSeries
import ModularFormsKB.Milne.Wave13.AllFiniteIndex
import ModularFormsKB.Milne.Wave13.MiyakeDimension

/-!
# Milne wave 13

Riemann–Roch (Theorem 1.20) on `X(Γ)` for every subgroup `Γ` of finite index in `SL₂(ℤ)`, congruence or not:

* `Wave13/PolePoincare.lean`: the terms `((az + b) - u(cz + d))^{-2k}` of a Poincaré series with a pole at `u`, their
  estimates and locally uniform convergence away from the orbit of `u`.
* `Wave13/PoleSeries.lean`: the series `S_u`; it is a meromorphic modular form of weight `2k` (`k ≥ 3`) for every
  finite-index `Γ`, continuous off `Γu`, with `|S_u| → ∞` at a non-elliptic `u`.
* `Wave13/AllFiniteIndex.lean`: `S_{γτ}/E₆` separates a generic fibre of `j`; Riemann–Roch, Corollary 1.21,
  Theorems 1.27, 2.22, 4.9 and Proposition 4.12 for every finite-index `Γ`, unconditional.
* `Wave13/MiyakeDimension.lean`: Miyake's Theorems 2.5.2 and 4.2.11 for every modular group, unconditional.
-/
