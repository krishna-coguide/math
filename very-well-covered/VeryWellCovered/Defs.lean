module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

/-! Counting conventions for the leafy-extension counterexample. -/

namespace VeryWellCovered

/-- Number of independent vertex sets of size `k`. -/
noncomputable def independentCount {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : ℕ := by
  classical exact (G.indepSetFinset k).card

/-- The count is independent of the decidability instances used to enumerate the sets. -/
theorem independentCount_eq_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj] (k : ℕ) :
    independentCount G k = (G.indepSetFinset k).card := by
  unfold independentCount
  congr 1
  ext s
  simp only [SimpleGraph.mem_indepSetFinset_iff]

/-- Choose `j` old vertices and supplement them with `k-j` eligible leaves. -/
def leafyCount (n : ℕ) (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1), a j * (n - j).choose (k - j)

/-- Independent-set counts on the join of 192 disjoint 30-cliques and 768 disjoint edges. -/
def baseCount (j : ℕ) : ℕ :=
  if j = 0 then 1 else (192 : ℕ).choose j * 30^j + (768 : ℕ).choose j * 2^j

/-- The coefficients are weakly increasing up to a mode and weakly decreasing after it. -/
def IsUnimodal (a : ℕ → ℕ) : Prop :=
  ∃ m : ℕ, MonotoneOn a (Set.Iic m) ∧ AntitoneOn a (Set.Ici m)

end VeryWellCovered
