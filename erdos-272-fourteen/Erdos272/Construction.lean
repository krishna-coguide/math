import Erdos272.Basic
import Mathlib.Data.Finset.Card

namespace E272

/-- The property is tested only on distinct members; there is no common-point hypothesis. -/
def Valid (F : Finset Mask) : Prop := ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true

/-- Szabó’s construction at 14, centred on the integer 7 (bit 6). -/
def construction : List Mask := [
  64, 65, 66, 67, 68, 69, 70, 72, 73, 74, 76, 80,
  81, 82, 84, 88, 96, 97, 98, 100, 104, 112, 192, 193,
  194, 196, 200, 224, 240, 320, 321, 322, 328, 336, 340, 448,
  480, 496, 576, 578, 580, 584, 585, 592, 608, 704, 832, 1088,
  1089, 1090, 1092, 1096, 1120, 1216, 1344, 1360, 1364, 1600, 2112, 2113,
  2114, 2116, 2120, 2128, 2144, 2240, 2368, 2624, 3136, 4160, 4161, 4162,
  4164, 4176, 4192, 4288, 4416, 4672, 4680, 4681, 5184, 6208, 8256, 8257,
  8258, 8260, 8264, 8272, 8288, 8384, 8512, 8768, 9280, 10304, 12352
]

private theorem construction_nodup : construction.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem checked_pairs :
    construction.all (fun a => construction.all (fun b => a == b || ap (a &&& b))) = true := by
  decide +kernel

theorem lower_bound : ∃ F : Finset Mask, F.card = 95 ∧ Valid F := by
  refine ⟨construction.toFinset, ?_, ?_⟩
  · rw [List.toFinset_card_of_nodup construction_nodup]
    rfl
  · intro a ha b hb hab
    have h := List.all_eq_true.mp (List.all_eq_true.mp checked_pairs a (List.mem_toFinset.mp ha))
      b (List.mem_toFinset.mp hb)
    simpa [hab] using h

end E272
