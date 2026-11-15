import ModularFormsKB.Milne.Wave12.FiberDescent
import ModularFormsKB.Milne.Wave12.ScalarRiemannRoch
import ModularFormsKB.Milne.Wave12.PrimePower
import ModularFormsKB.Milne.Wave12.EisensteinLimit
import ModularFormsKB.Milne.Wave12.GammaNRiemannRoch

/-!
# Milne wave 12

Riemann–Roch (Theorem 1.20) on the modular curves `X(Γ)` beyond `Γ₀(N)`:

* `Wave12/FiberDescent.lean`: symmetric functions of a meromorphic function along the fibres of a finite holomorphic
  map are meromorphic; separation of points descends along finite holomorphic maps.
* `Wave12/ScalarRiemannRoch.lean`: the group `Γ_sc(M)` of matrices scalar modulo `M`; the functions `j(Mδz)` separate
  a generic fibre of `j` on `X(Γ_sc(M))`; Riemann–Roch on `X(Γ)` whenever `Γ̄ ⊇ Γ̄_sc(M)`.
* `Wave12/PrimePower.lean`: every `Γ ⊇ Γ(pᵏ)` qualifies; Theorems 1.20, 1.27, 2.22, 4.9 and Proposition 4.12 for these
  `Γ`, unconditional.
* `Wave12/EisensteinLimit.lean`: the limit at `i∞` of the Eisenstein series of level `N`.
* `Wave12/GammaNRiemannRoch.lean`: quotients `E_4^a / D` of Eisenstein series as meromorphic functions on `X(N)`; they
  separate what the `j(Mδz)` do not; Riemann–Roch and Theorems 1.27, 2.22, 4.9, Proposition 4.12 for every congruence
  subgroup, unconditional.
-/
