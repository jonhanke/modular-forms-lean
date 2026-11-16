import ModularFormsKB.Historical.Weber.ThetaEta
import ModularFormsKB.Historical.Weber.ClassInvariantTable
import ModularFormsKB.Historical.Weber.TableRow3
import ModularFormsKB.Historical.Weber.FirstValues
import ModularFormsKB.Historical.Weber.ThetaDuplication
import ModularFormsKB.Historical.Weber.SecondOrder

/-!
# Weber, *Elliptische Functionen und algebraische Zahlen* (1891) and *Lehrbuch der Algebra* III (1908):
historical library

* `ThetaEta`: `ϑ₀₀ = η f²`, `ϑ₀₁ = η f₁²`, `ϑ₁₀ = η f₂²` (1891, § 21 (9)).
* `ClassInvariantTable`: the first rows of Weber's table of class invariants (1908, Tabelle VI).
* `TableRow3`: proof of Tabelle VI, `m = 3`: `f(√-3) = ∛2`.

The Weber–Heegner–Stark pilot (`ModularFormsKB.Historical.WeberHeegnerStark`) is a separate library; its
definitions of `f`, `f₂`, `j` are reused here.
-/
