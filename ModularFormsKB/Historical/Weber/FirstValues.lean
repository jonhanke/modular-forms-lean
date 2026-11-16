import ModularFormsKB.Historical.Weber.TableRow3
import ModularFormsKB.Citation
/-!
# Weber, *Lehrbuch der Algebra* III (1908), § 128: the first values of `f`

Weber obtains `f(i) = ⁴√2`, `f₁(√-2) = ⁴√2`, `f(√-3) = ∛2` and `f(√-7) = √2` from the cubic
`u³ - γ₂ u - 16 = 0` satisfied by `u = f⁸`. The first three are proved in this
library (`tableRow1`, `tableRow2`, `tableRow3`, by other routes: the `η` inversion formula and
`f f₁ f₂ = √2`); the fourth is `TableRow7`, still stated (loose end LE-MF-0193).
-/

namespace ModularFormsKB.Historical.Weber

/-- **Weber, Lehrbuch III, § 128, (2)–(4)** (first three values):
`f(i) = ⁴√2`, `f₁(√-2) = ⁴√2`, `f(√-3) = ∛2`. Wrapper of `tableRow1`, `tableRow2`, `tableRow3`. The fourth
value of the row, `f(√-7) = √2`, is `TableRow7` (stated). -/
@[kb "weber1908" "§ 128, (2)–(4)"]
theorem weber_first_values : TableRow1 ∧ TableRow2 ∧ TableRow3 :=
  ⟨tableRow1, tableRow2, tableRow3⟩

end ModularFormsKB.Historical.Weber
