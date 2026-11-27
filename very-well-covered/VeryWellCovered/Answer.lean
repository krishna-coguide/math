module

public import VeryWellCovered.Coefficients
public import VeryWellCovered.Core
public import VeryWellCovered.Graph

@[expose] public section

/-! A connected counterexample to unimodality after attaching one leaf at each vertex. -/

namespace VeryWellCovered

/-- The leafy extension has one original vertex and one leaf per core vertex. -/
theorem card_whisker_core : Fintype.card (CoreV ⊕ CoreV) = 14592 := by
  rw [Fintype.card_sum, card_coreV]

/-- The binomial formula computes counts of actual independent sets of the leafy extension. -/
theorem independentCount_whisker_core (k : ℕ) :
    independentCount (whisker coreGraph) k = leafyCount 7296 baseCount k := by
  rw [independentCount_whisker, card_coreV, funext independentCount_core]

/-- The independent-set count at 3789 falls strictly below the counts at 3738 and 3840. -/
theorem whisker_core_valley :
    independentCount (whisker coreGraph) 3789 < independentCount (whisker coreGraph) 3738 ∧
    independentCount (whisker coreGraph) 3789 < independentCount (whisker coreGraph) 3840 := by
  simpa only [independentCount_whisker_core] using leafyCount_valley

theorem whisker_core_not_isUnimodal : ¬ IsUnimodal (independentCount (whisker coreGraph)) := by
  rw [funext independentCount_whisker_core]
  exact leafyCount_not_isUnimodal

/-- The concrete connected core has independence number 768 (in particular, at least 5).
Its single leafy extension is connected and very well-covered, but the sequence of
coefficients of its independence polynomial is not unimodal. -/
theorem counterexample :
    Fintype.card CoreV = 7296 ∧ coreGraph.Connected ∧ coreGraph.indepNum = 768 ∧
    Fintype.card (CoreV ⊕ CoreV) = 14592 ∧ (whisker coreGraph).Connected ∧
    IsVeryWellCovered (whisker coreGraph) ∧ ¬ IsUnimodal (independentCount (whisker coreGraph)) :=
  ⟨card_coreV, coreGraph_connected, coreGraph_indepNum, card_whisker_core,
    whisker_connected coreGraph_connected, whisker_veryWellCovered coreGraph,
    whisker_core_not_isUnimodal⟩

end VeryWellCovered
