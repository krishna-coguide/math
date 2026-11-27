import Erdos272.FullRank

namespace E272.Neutral
open Finset RankProof
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

/-- This nonstar of thirty APs has four independent neutral dependencies.
    (The last member is the pair {3,9}.) -/
def sharpFamily : Fin 30 → Mask := ![84, 85, 254, 255, 336, 340, 341, 510, 511, 1016, 1020, 1344, 1360, 1364, 1365, 2040, 2044, 4064, 4080, 4094, 4095, 5440, 5456, 5460, 5461, 8160, 8176, 8190, 8191, 260]
def relations : Fin 4 → Fin 30 → ℚ := ![![1, -1, -1, 1, 0, -1, 1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, -1, 0, 0, 0, -1, 1, 0, -1, 1, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, -1, 1, 0, 0, -1, 1, 0, 0, 1, -1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 1, -1, 0, 0, 1, -1, 0, 0, -1, 1, 0]]

theorem sharp_valid : Function.Injective sharpFamily ∧
    (∀ i j : Fin 30, i ≠ j → ap (sharpFamily i &&& sharpFamily j) = true) ∧
    (∀ x : Fin 14, ∃ i : Fin 30, (sharpFamily i).getLsbD x = false) := by
  change (∀ i j : Fin 30, sharpFamily i = sharpFamily j → i = j) ∧ _
  decide +kernel

theorem sharp_kernel :
    (∀ k : Fin 4, ∀ j : Fin fullPos.length, ∑ i, relations k i * feature fullPos (sharpFamily i) j = 0) ∧
    (∀ k : Fin 4, ∀ j : Fin fullNeg.length, ∑ i, relations k i * feature fullNeg (sharpFamily i) j = 0) := by
  decide +kernel

theorem sharp_independent : LinearIndependent ℚ relations := by
  let piv : Fin 4 → Fin 30 := ![0,4,11,14]
  have units : ∀ i j, relations i (piv j) = if i = j then 1 else 0 := by decide +kernel
  apply Fintype.linearIndependent_iff.mpr
  intro c h v
  have H := congrFun h (piv v)
  simpa [Finset.sum_apply,units,mul_ite] using H

end E272.Neutral
