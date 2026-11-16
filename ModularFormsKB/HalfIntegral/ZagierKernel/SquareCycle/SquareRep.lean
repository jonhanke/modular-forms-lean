/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
-/
import ModularFormsKB.HalfIntegral.Abstract.Shintani

/-!
# The forms $[0, n, c]$ of square discriminant

The representatives of the classes of discriminant $n^2$ (`Classes.lean`).
-/

namespace ModularFormsKB.HalfIntegral

namespace BinQF

/-- The form $[0, n, c]$, i.e. $Q(x, y) = y(nx + cy)$, of discriminant $n^2$. -/
def squareRep (n : ℕ) (c : ℤ) : BinQF := ⟨0, n, c⟩

theorem disc_squareRep (n : ℕ) (c : ℤ) : (squareRep n c).disc = (n : ℤ) ^ 2 := by
  simp [squareRep, disc]

end BinQF

end ModularFormsKB.HalfIntegral
