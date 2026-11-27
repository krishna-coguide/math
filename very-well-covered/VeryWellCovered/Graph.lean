module

public import VeryWellCovered.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Fintype.Sum

@[expose] public section

/-! # Attaching one leaf to each vertex

In a leafy extension, an independent set is determined by an independent set of
original vertices and a set of leaves whose original vertices were not selected.
-/

namespace VeryWellCovered

open Finset SimpleGraph

variable {V : Type*}

/-- Keep the original vertices on the left, and attach one leaf on the right to each. -/
def whisker (G : SimpleGraph V) : SimpleGraph (V ⊕ V) where
  Adj
    | .inl x, .inl y => G.Adj x y
    | .inl x, .inr y => x = y
    | .inr x, .inl y => x = y
    | .inr _, .inr _ => False
  symm := ⟨by rintro (x | x) (y | y) h; exacts [G.adj_symm h, h.symm, h.symm, h]⟩
  loopless := ⟨by rintro (x | x); exacts [G.loopless.irrefl x, id]⟩

/-- There are no isolated vertices, and every inclusion-maximal independent set
has exactly half the order of the graph. -/
def IsVeryWellCovered [Fintype V] (G : SimpleGraph V) : Prop :=
  (∀ x, ∃ y, G.Adj x y) ∧
    ∀ s : Finset V, Maximal G.IsIndepSet (s : Set V) → 2 * s.card = Fintype.card V

section Fintype

variable [Fintype V]

private theorem indep_iff_parts [DecidableEq V] (G : SimpleGraph V) (u : Finset (V ⊕ V)) :
    (whisker G).IsIndepSet u ↔ G.IsIndepSet u.toLeft ∧ u.toRight ⊆ u.toLeftᶜ := by
  constructor
  · intro h
    constructor
    · intro x hx y hy hxy
      exact h (mem_toLeft.mp hx) (mem_toLeft.mp hy) (by simpa using hxy)
    · intro x hx
      apply mem_compl.mpr
      intro hx'
      exact h (mem_toLeft.mp hx') (mem_toRight.mp hx) (by simp) rfl
  · rintro ⟨hi, hd⟩ (x | x) hx (y | y) hy hxy
    · exact hi (mem_toLeft.mpr hx) (mem_toLeft.mpr hy) (fun h => hxy (congrArg Sum.inl h))
    · rintro (rfl : x = y)
      exact mem_compl.mp (hd (mem_toRight.mpr hy)) (mem_toLeft.mpr hx)
    · rintro (rfl : x = y)
      exact mem_compl.mp (hd (mem_toRight.mpr hx)) (mem_toLeft.mpr hy)
    · exact id

/-- Count the independent `k`-sets by their number of original vertices. -/
theorem independentCount_whisker (G : SimpleGraph V) (k : ℕ) :
    independentCount (whisker G) k = leafyCount (Fintype.card V) (independentCount G) k := by
  classical
  simp only [leafyCount, independentCount_eq_card]
  have maps : Set.MapsTo (fun u : Finset (V ⊕ V) => u.toLeft.card)
      ((whisker G).indepSetFinset k) (range (k + 1)) := by
    intro u hu
    have h := (mem_indepSetFinset_iff.mp hu).card_eq
    exact mem_range.mpr (Nat.lt_succ_of_le (card_toLeft_le.trans_eq h))
  refine (card_eq_sum_card_fiberwise maps).trans ?_
  apply sum_congr rfl
  intro j hj
  let choices := (G.indepSetFinset j).sigma (fun s => sᶜ.powersetCard (k - j))
  calc
    _ = choices.card := by
      apply card_nbij' (fun u => ⟨u.toLeft, u.toRight⟩) (fun st => st.1.disjSum st.2)
      · intro u hu
        obtain ⟨hu, hj'⟩ := mem_filter.mp hu
        obtain ⟨hind, hk⟩ := mem_indepSetFinset_iff.mp hu
        obtain ⟨hleft, hright⟩ := (indep_iff_parts G u).mp hind
        change u.toLeft.card = j at hj'
        have hsum := card_toLeft_add_card_toRight (u := u)
        exact mem_sigma.mpr ⟨mem_indepSetFinset_iff.mpr ⟨hleft, hj'⟩,
          mem_powersetCard.mpr ⟨hright, by change u.toRight.card = k - j; omega⟩⟩
      · rintro ⟨s, t⟩ hst
        obtain ⟨hs, ht⟩ := mem_sigma.mp hst
        obtain ⟨hind, hs⟩ := mem_indepSetFinset_iff.mp hs
        obtain ⟨hsub, ht⟩ := mem_powersetCard.mp ht
        apply mem_filter.mpr
        constructor
        · apply mem_indepSetFinset_iff.mpr
          constructor
          · simpa [indep_iff_parts] using And.intro hind hsub
          · rw [card_disjSum, hs, ht, Nat.add_sub_of_le (mem_range_succ_iff.mp hj)]
        · simpa using hs
      · intro u _
        exact toLeft_disjSum_toRight
      · rintro ⟨s, t⟩ _
        simp
    _ = _ := by
      rw [show choices.card = _ from card_sigma _ _]
      apply sum_const_nat
      intro s hs
      rw [card_powersetCard, card_compl, (mem_indepSetFinset_iff.mp hs).card_eq]

/-- In a maximal independent set, every missing original vertex has its leaf present. -/
theorem whisker_veryWellCovered (G : SimpleGraph V) : IsVeryWellCovered (whisker G) := by
  classical
  constructor
  · rintro (x | x)
    · exact ⟨.inr x, rfl⟩
    · exact ⟨.inl x, rfl⟩
  · intro s hs
    obtain ⟨hi, hmax⟩ := isMaximalIndepSet_iff.mp hs
    obtain ⟨hleft, hright⟩ := (indep_iff_parts G s).mp hi
    let full := s.toLeft.disjSum s.toLeftᶜ
    have hfull : (whisker G).IsIndepSet full := by
      simpa [indep_iff_parts, full] using hleft
    have hsub : s ⊆ full := subset_disjSum.mpr ⟨Subset.rfl, hright⟩
    have heq : s = full := Subset.antisymm hsub (hmax full hfull hsub)
    have hcard : s.card = Fintype.card V := (congrArg card heq).trans (by simp [full])
    simp [hcard, two_mul]

end Fintype

/-- Paths between original vertices remain paths, and each leaf meets its original vertex. -/
theorem whisker_connected {G : SimpleGraph V} (hG : G.Connected) : (whisker G).Connected := by
  have : Nonempty V := hG.nonempty
  let f : G →g whisker G := ⟨Sum.inl, fun h => h⟩
  have old (x y : V) : (whisker G).Reachable (.inl x) (.inl y) := (hG x y).map f
  have leaf (x : V) : (whisker G).Reachable (.inl x) (.inr x) :=
    (show (whisker G).Adj (.inl x) (.inr x) from rfl).reachable
  constructor
  rintro (x | x) (y | y)
  · exact old x y
  · exact (old x y).trans (leaf y)
  · exact (leaf x).symm.trans (old x y)
  · exact ((leaf x).symm.trans (old x y)).trans (leaf y)

end VeryWellCovered
