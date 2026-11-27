import Erdos272.Board
import Erdos272Bounds
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

namespace E272.Board

/-- For the one-based board `[14]`, `95` is attained and every valid family
    has at most `95` members. -/
theorem greatest14 :
    IsGreatest {n : ℕ | ∃ F : Finset (Finset ℕ), F.card = n ∧ ValidFamily F} 95 :=
  exact_of_upper Search.Run95.upper95

/-- The extremal cardinality for problem 272 on fourteen points. -/
noncomputable def t14 : ℕ :=
  sSup {n : ℕ | ∃ F : Finset (Finset ℕ), F.card = n ∧ ValidFamily F}

theorem t14_eq_95 : t14 = 95 := greatest14.csSup_eq

end E272.Board
