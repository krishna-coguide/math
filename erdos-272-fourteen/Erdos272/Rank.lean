import Erdos272.RankLocal

namespace E272

/-- At most 92 members of a nonstar family are free of seven-term progressions. -/
theorem short_bound (F : Finset Mask)
    (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false) :
    (F.filter (fun a => short a = true)).card ≤ 92 := by
  apply local_rank_bound (Finset.filter_subset _ _) hg hne
  · intro a ha
    have hs := (Finset.mem_filter.mp ha).2
    cases e : ap a with
    | false => exact Or.inr (score_bad hs e)
    | true => exact Or.inl ⟨rfl,hs⟩
  · intro a ha b hb hn
    exact score_good (short_inter_left (Finset.mem_filter.mp ha).2)
      (hg _ (Finset.mem_filter.mp ha).1 _ (Finset.mem_filter.mp hb).1 hn)

end E272
