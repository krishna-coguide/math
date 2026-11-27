import Erdos272.Construction
import Mathlib.Data.Fintype.Basic

namespace E272

/-- All pairs and triples through 4 except {4,9}, plus [14] \ {4,9}. -/
private def nearFamily : List Mask := [
  9, 10, 11, 12, 13, 14, 24, 25, 26, 28, 40, 41,
  42, 44, 56, 72, 73, 74, 76, 88, 104, 136, 137, 138,
  140, 152, 168, 200, 265, 266, 268, 280, 296, 328, 392, 520,
  521, 522, 524, 536, 552, 584, 648, 776, 1032, 1033, 1034, 1036,
  1048, 1064, 1096, 1160, 1288, 1544, 2056, 2057, 2058, 2060, 2072, 2088,
  2120, 2184, 2312, 2568, 3080, 4104, 4105, 4106, 4108, 4120, 4136, 4168,
  4232, 4360, 4616, 5128, 6152, 8200, 8201, 8202, 8204, 8216, 8232, 8264,
  8328, 8456, 8712, 9224, 10248, 12296, 16119
]

private theorem neardup : nearFamily.Nodup := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem nearvalid :
    nearFamily.all (fun a => nearFamily.all (fun b => a == b || ap (a &&& b))) = true := by
  decide +kernel

/-- The nonstar all-short bound of 92 is tight to within one. -/
theorem short_example : ∃ F : Finset Mask, F.card = 91 ∧ Valid F ∧
    (∀ a ∈ F, short a = true) ∧ (∀ x : Fin 14, ∃ a ∈ F, a.getLsbD x = false) := by
  refine ⟨nearFamily.toFinset, ?_, ?_, ?_, ?_⟩
  · rw [List.toFinset_card_of_nodup neardup]; rfl
  · intro a ha b hb hab
    have h := List.all_eq_true.mp (List.all_eq_true.mp nearvalid a (List.mem_toFinset.mp ha))
      b (List.mem_toFinset.mp hb)
    simpa [hab] using h
  · have hc : nearFamily.all short = true := by decide +kernel
    intro a ha; exact List.all_eq_true.mp hc _ (List.mem_toFinset.mp ha)
  · have hc : ∀ x : Fin 14, nearFamily.any (fun a => !a.getLsbD x) = true := by decide +kernel
    intro x; obtain ⟨a,ha,hx⟩ := List.any_eq_true.mp (hc x)
    exact ⟨a,List.mem_toFinset.mpr ha,by simpa using hx⟩

end E272
