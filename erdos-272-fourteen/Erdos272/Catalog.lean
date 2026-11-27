import Erdos272.Score
import Mathlib.Data.Finset.Card

namespace E272

def maskCard (a : Mask) : Nat := (List.range 14).countP a.getLsbD

set_option maxRecDepth 10000 in
theorem sevens_spec : sevens.toFinset = (apMasks.filter (fun a => maskCard a == 7)).toFinset := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem feature_spec :
    pos.Nodup ∧ neg.Nodup ∧
    pos.toFinset = (0 :: apMasks.filter (fun a => maskCard a == 2)).toFinset ∧
    neg.toFinset = (apMasks.filter (fun a => [1,3,4,6].contains (maskCard a))).toFinset := by
  decide +kernel

/-- The 38 long APs and 16 nonprogressions with nonpositive score. -/
def special : List Mask := [
  127, 254, 255, 508, 510, 511, 1016, 1020, 1022, 1023, 1535, 2032,
  2040, 2044, 2045, 2046, 2047, 3070, 4064, 4080, 4088, 4090, 4092, 4094,
  4095, 5461, 6140, 6141, 6143, 8128, 8160, 8176, 8180, 8184, 8188, 8189,
  8190, 8191, 10922, 12280, 12282, 12286, 12287, 16256, 16320, 16352, 16360, 16368,
  16376, 16378, 16380, 16381, 16382, 16383
]

theorem special_card : special.toFinset.card = 54 := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem long_population :
    (List.range 16384).countP (fun i => !short (BitVec.ofNat 14 i)) = 752 := by decide +kernel

set_option maxRecDepth 10000 in
theorem special_split : (special.filter ap).length = 38 ∧
    (special.filter (fun a => !ap a)).length = 16 := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem special_bits : unionTable (fun t => 2^t.toNat) special =
    (apTable &&& (board ^^^ shortTable)) ||| ((board ^^^ apTable) &&& (board ^^^ eqgt.2)) := by
  decide +kernel

theorem healthy_of_not_special {a : Mask} (ha : a ∉ special) :
    (ap a = true ∧ short a = true) ∨ 0 < score a := by
  have hm : (unionTable (fun t => 2^t.toNat) special).testBit a.toNat = false := by
    rw [unionTable_bit]
    simp [Nat.testBit_two_pow, BitVec.toNat_inj, List.any_eq_false]
    intro x hx he; exact ha (he ▸ hx)
  rw [special_bits] at hm
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, board_bit, apTable_bit, shortTable_bit] at hm
  cases h : ap a <;> simp_all
  exact (eqgt_correct a).2.mp hm

end E272
