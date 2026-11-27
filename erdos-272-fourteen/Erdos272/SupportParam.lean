import Erdos272.NeutralRows
import Erdos272.ParityPlane
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace E272.Neutral.SupportProof
open Finset RankProof
open scoped Matrix

set_option maxRecDepth 20000
set_option maxHeartbeats 15000000

/-- Singleton constraints on the parities of the 31 neutral coefficients. -/
def eqWords : Fin 14 → Nat := ![0, 0, 1, 2, 20, 72, 536875296, 1073775744, 8704, 67584, 16384, 131072, 0, 0]
def eqMatrix : Matrix (Fin 14) (Fin 31) (ZMod 2) := fun j i => bitVal ((eqWords j).testBit i.val)
theorem eq_entry : ∀ j i, eqMatrix j i = (coeff i ((1 : Mask) <<< j.val) : ZMod 2) := by
  have tab : ∀ (j : Fin 14) (i : Fin 31), (eqMatrix j i).val = (coeff i ((1 : Mask) <<< j.val) : ZMod 2).val := by decide +kernel
  intro j i; exact Fin.ext (tab j i)
def free : Fin 21 → Fin 31 := ![2, 3, 5, 7, 8, 9, 10, 11, 12, 15, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]
def pick : Matrix (Fin 21) (Fin 31) (ZMod 2) := fun j i => if free j = i then 1 else 0
def generate : Matrix (Fin 31) (Fin 21) (ZMod 2) := fun i k => bitVal ((BROW i).testBit k.val)
  where BROW : Fin 31 → Nat := ![0, 0, 1, 2, 1, 4, 2, 8, 16, 32, 64, 128, 256, 32, 0, 512, 128, 0, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 276, 584]
def comb : Matrix (Fin 31) (Fin 14) (ZMod 2) := fun i j => bitVal ((CROW i).testBit j.val)
  where CROW : Fin 31 → Nat := ![4, 8, 0, 0, 16, 0, 32, 0, 0, 0, 0, 0, 0, 256, 1024, 0, 512, 2048, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 128]

private theorem decode : generate * pick + comb * eqMatrix = 1 := by
  ext i j
  have H : ∀ (i j : Fin 31), ((generate * pick + comb * eqMatrix) i j).val = ((1 : Matrix (Fin 31) (Fin 31) (ZMod 2)) i j).val := by decide +kernel
  exact Fin.ext (H i j)

theorem parametrize (b : Fin 31 → ZMod 2) (hh : eqMatrix *ᵥ b = 0) : ∃ v : Fin 21 → ZMod 2, b = generate *ᵥ v := by
  refine ⟨pick *ᵥ b,?_⟩
  calc
    b = (1 : Matrix _ _ (ZMod 2)) *ᵥ b := (Matrix.one_mulVec _).symm
    _ = _ := by rw [← decode,Matrix.add_mulVec,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,hh,Matrix.mulVec_zero,add_zero]

/-- Only these AP coefficients are needed by the parity certificate. -/
abbrev XI := Fin 112
def testRow : XI → Mask := ![17, 20, 34, 40, 56, 65, 68, 72, 73, 80, 84, 85, 112, 120, 124, 130, 136, 144, 146, 160, 168, 170, 224, 248, 254, 255, 272, 288, 292, 320, 336, 340, 341, 448, 480, 496, 508, 510, 511, 544, 576, 584, 585, 640, 672, 680, 682, 896, 992, 1016, 1020, 1022, 1023, 1088, 1152, 1168, 1170, 1280, 1344, 1360, 1364, 1365, 1792, 1920, 1984, 2032, 2040, 2044, 2046, 2176, 2336, 2340, 2560, 2688, 2720, 2728, 2730, 3968, 4064, 4080, 4088, 4092, 4094, 4095, 4160, 4672, 4680, 4681, 5440, 5456, 5460, 5461, 8128, 8160, 8176, 8184, 8188, 8190, 8191, 8320, 9344, 9360, 9362, 10880, 10912, 10920, 10922, 16320, 16352, 16368, 16380, 16382]
def names : XI → List (Fin 21) := ![[0], [0], [1], [1], [0], [2, 4], [4], [16], [16], [0, 2], [10], [0, 10], [1], [0, 1], [0], [3, 6], [6], [17], [17], [1, 3], [11], [1, 11], [2], [1], [10], [10], [0, 5], [18], [18], [2, 5], [2, 4, 12], [0, 4, 10, 12], [0, 10], [3], [2, 3], [2], [11], [10, 11, 16], [10, 16], [1, 7], [19], [2, 4, 16, 19], [2, 4, 16], [3, 7], [3, 6, 13], [1, 6, 11, 13], [1, 11], [5], [3], [12], [11, 12, 17], [11, 16, 17], [16], [4], [20], [3, 6, 17, 20], [3, 6, 17], [5], [14], [4, 5, 12, 14], [2, 8, 12], [2, 4, 8], [7], [5, 7], [5], [13], [12, 13, 18], [12, 17, 18], [17], [6], [18], [18], [7], [15], [6, 7, 13, 15], [3, 9, 13], [3, 6, 9], [7], [14], [13, 14, 19], [13, 18, 19], [18], [2, 4, 8], [2, 4, 8], [2, 4], [19], [2, 4, 19], [2, 4], [5, 14], [5, 14], [2, 4, 8], [2, 4, 8], [15], [14, 15, 20], [14, 19, 20], [19], [3, 6, 9], [2, 3, 4, 6, 8, 9], [2, 4, 8], [3, 6], [20], [3, 6, 20], [3, 6], [7, 15], [7, 15], [3, 6, 9], [3, 6, 9], [15], [15, 20], [20], [3, 6, 9], [3, 6, 9]]
def testWords : XI → Nat := ![16, 5, 64, 10, 4, 536875008, 256, 16777216, 16777216, 36, 262164, 262160, 8, 12, 4, 1073774592, 1024, 33554432, 33554432, 136, 524360, 524352, 32, 8, 262144, 262144, 8208, 67108864, 67108864, 544, 1048864, 1310992, 262160, 128, 160, 32, 524288, 17563648, 17039360, 65600, 134217728, 687869952, 553652224, 2176, 2098304, 2622528, 524352, 512, 128, 1048576, 35127296, 50855936, 16777216, 256, 268435456, 1375764480, 1107329024, 16896, 4203008, 5251328, 537919744, 536870912, 2048, 2560, 512, 2097152, 70254592, 101711872, 33554432, 1024, 67108864, 67108864, 133120, 8456192, 10552320, 1075840000, 1073741824, 2048, 4194304, 140509184, 203423744, 67108864, 536870912, 536870912, 536875008, 134217728, 671092736, 536875008, 4202496, 4202496, 536870912, 536870912, 8388608, 281018368, 406847488, 134217728, 1073741824, 1610612736, 536870912, 1073774592, 268435456, 1342210048, 1073774592, 8454144, 8454144, 1073741824, 1073741824, 8388608, 276824064, 268435456, 1073741824, 1073741824]
def testMatrix : Matrix XI (Fin 31) (ZMod 2) := fun j i => bitVal ((testWords j).testBit i.val)
theorem test_entry : ∀ j i, testMatrix j i = (coeff i (testRow j) : ZMod 2) := by
  have tab : ∀ (j : XI) (i : Fin 31), (testMatrix j i).val = (coeff i (testRow j) : ZMod 2).val := by decide +kernel
  intro j i; exact Fin.ext (tab j i)
def signatures : Matrix XI (Fin 21) (ZMod 2) := fun j i => if i ∈ names j then 1 else 0
private theorem sig_cert : testMatrix * generate = signatures := by
  ext i j
  have H : ∀ (i : XI) (j : Fin 21), ((testMatrix * generate) i j).val = (signatures i j).val := by decide +kernel
  exact Fin.ext (H i j)

private theorem list_sum_eq (l : List (Fin 21)) (hl : l.Nodup) (v : Fin 21 → ZMod 2) :
    (l.map v).sum = ∑ i, (if i ∈ l then (1 : ZMod 2) else 0) * v i := by
  simp only [ite_mul,one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hh : Finset.univ.filter (fun i : Fin 21 => i ∈ l) = l.toFinset := by ext i; simp
  rw [hh]; exact (List.sum_toFinset v hl).symm

def samplePlane (xs : List (Fin 21)) : Nat := xs.foldr (fun j w => (plane 21 j) ^^^ w) 0
private theorem samplePlane_correct (xs : List (Fin 21)) (a : ℕ) (ha : a < 2^21) :
    bitVal ((samplePlane xs).testBit a) = (xs.map (fun j : Fin 21 => bitVal (a.testBit j))).sum := by
  have add (a b : Bool) : bitVal (a ^^ b) = bitVal a + bitVal b := by cases a <;> cases b <;> decide
  induction xs with
  | nil => simp [samplePlane,bitVal]
  | cons i xs ih =>
    change bitVal (((plane 21 i) ^^^ samplePlane xs).testBit a) = _
    rw [Nat.testBit_xor,add,plane_correct 21 i a ha i.isLt,ih]; rfl

theorem row_value (j : XI) (v : Fin 21 → ZMod 2) (b : Fin 31 → ZMod 2) (he : b = generate *ᵥ v)
    (a : ℕ) (ha : a < 2^21) (hv : ∀ i : Fin 21, bitVal (a.testBit i) = v i) :
    bitVal ((samplePlane (names j)).testBit a) = (testMatrix *ᵥ b) j := by
  rw [samplePlane_correct _ _ ha]
  have hv' : (fun j : Fin 21 => bitVal (a.testBit j)) = v := funext hv
  rw [hv']
  have no : ∀ j : XI, (names j).Nodup := by decide +kernel
  rw [he, Matrix.mulVec_mulVec,sig_cert,list_sum_eq _ (no j)]; rfl

end E272.Neutral.SupportProof
