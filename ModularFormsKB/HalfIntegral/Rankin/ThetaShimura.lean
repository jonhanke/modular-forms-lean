/-
# Shimura's theorem for the theta multiplier: what is left

`shimuraTheorem_of_rankin` (`Rankin/Assembly.lean`) proves Shimura's theorem from four named inputs. For the theta
multiplier `thetaMultiplierSystem` (`Abstract/ThetaInstance.lean`) three of them are now settled:
- `ThetaTwistLaw thetaMultiplierSystem` is proved (`thetaTwistLaw_thetaMultiplierSystem`);
- `RankinUnfolding` is proved (`RankinUnfold.rankinUnfolding`);
- `EisensteinFE` is proved from the lattice theta inversion formula `Miyake.HeckeTrick.LatticeThetaInversion`
  (`Miyake.HeckeTrick.eisensteinFE_of_latticeThetaInversion`; LE-MF-0242),
  and `LatticeThetaInversion` is proved (`Miyake.HeckeTrick.Inversion.latticeThetaInversion`), so
`EisensteinFE` holds (`Miyake.HeckeTrick.eisensteinFE`). Hence Shimura's theorem for the theta multiplier holds
conditional on `ShimuraDualUnfolding thetaMultiplierSystem k N χ` alone (`shimuraTheorem_theta_of_dualUnfolding`).
-/
import ModularFormsKB.HalfIntegral.Rankin.Assembly
import ModularFormsKB.HalfIntegral.Rankin.Unfolding
import ModularFormsKB.Miyake.HeckeTrick.LatticeInversion
import ModularFormsKB.Miyake.Sec4_9.Spherical.UnaryLaw

namespace ModularFormsKB.HalfIntegral

/-- **Shimura's theorem for the theta multiplier, from Hecke's functional equation and the dual unfolding**
(Shimura 1973 `shimura1973`, Main Theorem): the theta twist law and the unfolding principle are proved. -/
@[kb "shimura1973" "Main Theorem for the theta multiplier, conditional on EisensteinFE and ShimuraDualUnfolding [unverified]"]
theorem shimuraTheorem_theta_of_eisensteinFE_of_dualUnfolding (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N))
    (hN : 0 < N) (hE : EisensteinFE) (hD : ShimuraDualUnfolding thetaMultiplierSystem k N χ) :
    ShimuraTheorem thetaMultiplierSystem k N χ :=
  shimuraTheorem_of_rankin thetaMultiplierSystem k N χ hN thetaTwistLaw_thetaMultiplierSystem hE
    RankinUnfold.rankinUnfolding hD

/-- **Shimura's theorem for the theta multiplier, conditional on the dual unfolding alone** (Shimura 1973
`shimura1973`, Main Theorem): `ThetaTwistLaw`, `EisensteinFE` and
`RankinUnfolding` are proved; the only named input left is `ShimuraDualUnfolding thetaMultiplierSystem k N χ`. -/
@[kb "shimura1973" "Main Theorem for the theta multiplier, conditional on ShimuraDualUnfolding alone [unverified]"]
theorem shimuraTheorem_theta_of_dualUnfolding (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (hN : 0 < N)
    (hD : ShimuraDualUnfolding thetaMultiplierSystem k N χ) :
    ShimuraTheorem thetaMultiplierSystem k N χ :=
  shimuraTheorem_theta_of_eisensteinFE_of_dualUnfolding k N χ hN Miyake.HeckeTrick.eisensteinFE hD

end ModularFormsKB.HalfIntegral
