import ModularFormsKB.Milne.Wave14.SmoothLog
import ModularFormsKB.Milne.Wave14.SmoothCocycle
import ModularFormsKB.Milne.Wave14.HalfPlaneTriv
import ModularFormsKB.Milne.Wave14.DbarUpper
import ModularFormsKB.Milne.Wave14.LineBundles

/-!
# Milne wave 14

Remark 4.26 (every holomorphic line bundle on `ℍ` is trivial), unconditional, through the multiplicative Cousin
problem on `ℍ` (`MultiplicativeCousinStatement`, before a named input):

* `Wave14/SmoothLog.lean`: smooth logarithms on convex open sets (covering-space lift of `exp`).
* `Wave14/SmoothCocycle.lean`: smooth trivializations of a cocycle; gluing two sets; gluing along chains.
* `Wave14/HalfPlaneTriv.lean`: a smooth cocycle on an open cover of the half-plane is smoothly trivial.
* `Wave14/DbarUpper.lean`: `∂̄u = α` on the half-plane (Tau Ceti's Dolbeault lemma and the Cayley transform).
* `Wave14/LineBundles.lean`: the holomorphic Cousin problem, `multiplicativeCousinStatement`,
  `lineBundlesOnHTrivial`.
-/
