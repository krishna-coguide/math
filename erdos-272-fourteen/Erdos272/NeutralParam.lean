import Erdos272.NeutralRows
import Erdos272.ParityPlane
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace E272.Neutral
open Finset RankProof
open scoped Matrix

set_option maxRecDepth 20000
set_option maxHeartbeats 15000000

/-- Four extra rational columns: prescribed sums of neutral incidences. -/
def checkWords : Fin 4 → Nat := ![441277647, 30924084, 1952939697, 1170906229]
def checkWeight (j : Fin 4) (i : Fin 31) : Int := if (checkWords j).testBit i.val then 1 else 0
def checkCol (a : Mask) (j : Fin 4) : ℚ := ∑ i, (checkWeight j i : ℚ) * inc (neutral i) a

def eqWords : Fin 18 → Nat := ![0, 0, 1, 2, 20, 72, 536875296, 1073775744, 8704, 67584, 16384, 131072, 0, 0, 441277647, 30924084, 1952939697, 1170906229]
def eqMatrix : Matrix (Fin 18) (Fin 31) (ZMod 2) := fun j i => bitVal ((eqWords j).testBit i.val)
theorem eq_entry : ∀ j i, eqMatrix j i = if h : j.val < 14 then (coeff i ((1 : Mask) <<< j.val) : ZMod 2) else
    (checkWeight ⟨j.val-14,by omega⟩ i : ZMod 2) := by
  have tab : ∀ (j : Fin 18) (i : Fin 31), (eqMatrix j i).val = (if h : j.val < 14 then (coeff i ((1 : Mask) <<< j.val) : ZMod 2) else
    (checkWeight ⟨j.val-14,by omega⟩ i : ZMod 2)).val := by decide +kernel
  intro j i; exact Fin.ext (tab j i)

def free : Fin 17 → Fin 31 := ![2, 3, 5, 7, 8, 9, 10, 11, 12, 15, 18, 19, 20, 21, 22, 23, 25]
def pick : Matrix (Fin 17) (Fin 31) (ZMod 2) := fun j i => if free j = i then 1 else 0
def generate : Matrix (Fin 31) (Fin 17) (ZMod 2) := fun i k => bitVal ((BROW i).testBit k.val)
  where BROW : Fin 31 → Nat := ![0, 0, 1, 2, 1, 4, 2, 8, 16, 32, 64, 128, 256, 32, 0, 512, 128, 0, 1024, 2048, 4096, 8192, 16384, 32768, 55124, 65536, 7898, 79234, 30923, 276, 584]
def comb : Matrix (Fin 31) (Fin 18) (ZMod 2) := fun i j => bitVal ((CROW i).testBit j.val)
  where CROW : Fin 31 → Nat := ![4, 8, 0, 0, 16, 0, 32, 0, 0, 0, 0, 0, 0, 256, 1024, 0, 512, 2048, 0, 0, 0, 0, 0, 0, 36368, 0, 165540, 249692, 231792, 64, 128]

private theorem decode : generate * pick + comb * eqMatrix = 1 := by
  ext i j
  have H : ∀ (i j : Fin 31), ((generate * pick + comb * eqMatrix) i j).val = ((1 : Matrix (Fin 31) (Fin 31) (ZMod 2)) i j).val := by decide +kernel
  exact Fin.ext (H i j)

theorem parametrize (b : Fin 31 → ZMod 2) (hh : eqMatrix *ᵥ b = 0) : ∃ v : Fin 17 → ZMod 2, b = generate *ᵥ v := by
  refine ⟨pick *ᵥ b,?_⟩
  calc
    b = (1 : Matrix _ _ (ZMod 2)) *ᵥ b := (Matrix.one_mulVec _).symm
    _ = _ := by rw [← decode,Matrix.add_mulVec,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,hh,Matrix.mulVec_zero,add_zero]

/-- Only these AP coefficients are needed by the parity certificate. -/
abbrev XI := Fin 80
def testRow : XI → Mask := ![17, 20, 34, 40, 65, 68, 72, 73, 80, 84, 85, 120, 130, 136, 144, 146, 160, 168, 170, 224, 272, 273, 288, 320, 336, 340, 448, 480, 511, 544, 576, 584, 585, 640, 672, 680, 896, 960, 1016, 1023, 1088, 1092, 1152, 1168, 1170, 1280, 1344, 1360, 1364, 1365, 1920, 1984, 2032, 2044, 2046, 2176, 2340, 2560, 2688, 2720, 2728, 2730, 4088, 4092, 4160, 4672, 4680, 5440, 5460, 8160, 8184, 8190, 8191, 8320, 8704, 9360, 10880, 16352, 16368, 16382]
def names : XI → List (Fin 17) := ![[0], [0], [1], [1], [2, 4], [4], [2, 4, 6, 8, 9, 10, 12, 14, 15], [2, 4, 6, 8, 9, 10, 12, 14, 15], [0, 2], [10], [0, 10], [0, 1], [3, 6], [6], [16], [16], [1, 3], [11], [1, 11], [2], [0, 5], [0], [1, 3, 4, 6, 7, 9, 10, 11, 12], [2, 5], [2, 4, 12], [0, 4, 10, 12], [3], [2, 3], [2, 4, 6, 8, 9, 12, 14, 15], [1, 7], [1, 7, 8, 10, 12, 13, 16], [1, 6, 7, 9, 13, 14, 15, 16], [6, 8, 9, 10, 12, 14, 15], [3, 7], [3, 6, 13], [1, 6, 11, 13], [5], [3, 5], [12], [2, 4, 6, 8, 9, 10, 12, 14, 15], [4], [4], [0, 1, 3, 6, 7, 11, 12, 13, 14], [0, 1, 7, 11, 12, 13, 14, 16], [3, 6, 16], [5], [14], [4, 5, 12, 14], [2, 8, 12], [2, 4, 8], [5, 7], [5], [13], [1, 3, 4, 6, 7, 9, 10, 11, 16], [16], [6], [1, 3, 4, 6, 7, 9, 10, 11, 12], [7], [15], [6, 7, 13, 15], [3, 9, 13], [3, 6, 9], [3, 4, 6, 8, 9, 11, 16], [1, 3, 4, 6, 7, 9, 10, 11, 12], [2, 4], [1, 7, 8, 10, 12, 13, 16], [1, 2, 4, 7, 8, 10, 12, 13, 16], [5, 14], [2, 4, 8], [0, 1, 3, 6, 7, 11, 12, 13, 15], [1, 7, 8, 10, 12, 13, 16], [2, 3, 4, 6, 8, 9], [2, 4, 8], [3, 6], [7], [0, 1, 7, 11, 12, 13, 14], [7, 15], [0, 1, 3, 6, 7, 11, 12, 13, 14, 15], [0, 1, 3, 6, 7, 11, 12, 13, 14], [3, 6, 9]]
def testWords : XI → Nat := ![16, 5, 64, 10, 536875008, 256, 16777216, 16777216, 36, 262164, 262160, 12, 1073774592, 1024, 33554432, 33554432, 136, 524360, 524352, 32, 8208, 16, 67108864, 544, 1048864, 1310992, 128, 160, 17039360, 65600, 134217728, 687869952, 553652224, 2176, 2098304, 2622528, 512, 640, 1048576, 16777216, 256, 256, 268435456, 1375764480, 1107329024, 16896, 4203008, 5251328, 537919744, 536870912, 2560, 512, 2097152, 101711872, 33554432, 1024, 67108864, 133120, 8456192, 10552320, 1075840000, 1073741824, 203423744, 67108864, 536875008, 134217728, 671092736, 4202496, 536870912, 281018368, 134217728, 1610612736, 536870912, 1073774592, 65536, 1342210048, 8454144, 276824064, 268435456, 1073741824]
def testMatrix : Matrix XI (Fin 31) (ZMod 2) := fun j i => bitVal ((testWords j).testBit i.val)
theorem test_entry : ∀ j i, testMatrix j i = (coeff i (testRow j) : ZMod 2) := by
  have tab : ∀ (j : XI) (i : Fin 31), (testMatrix j i).val = (coeff i (testRow j) : ZMod 2).val := by decide +kernel
  intro j i; exact Fin.ext (tab j i)
def signatures : Matrix XI (Fin 17) (ZMod 2) := fun j i => if i ∈ names j then 1 else 0
private theorem sig_cert : testMatrix * generate = signatures := by
  ext i j
  have H : ∀ (i : XI) (j : Fin 17), ((testMatrix * generate) i j).val = (signatures i j).val := by decide +kernel
  exact Fin.ext (H i j)

private theorem list_sum_eq (l : List (Fin 17)) (hl : l.Nodup) (v : Fin 17 → ZMod 2) :
    (l.map v).sum = ∑ i, (if i ∈ l then (1 : ZMod 2) else 0) * v i := by
  simp only [ite_mul,one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hh : Finset.univ.filter (fun i : Fin 17 => i ∈ l) = l.toFinset := by ext i; simp
  rw [hh]; exact (List.sum_toFinset v hl).symm

theorem row_value (j : XI) (v : Fin 17 → ZMod 2) (b : Fin 31 → ZMod 2) (he : b = generate *ᵥ v)
    (a : ℕ) (ha : a < 2^17) (hv : ∀ i : Fin 17, bitVal (a.testBit i) = v i) :
    bitVal ((evalPlane (names j)).testBit a) = (testMatrix *ᵥ b) j := by
  rw [evalPlane_correct _ _ ha]
  have hv' : (fun j : Fin 17 => bitVal (a.testBit j)) = v := funext hv
  rw [hv']
  have no : ∀ j : XI, (names j).Nodup := by decide +kernel
  rw [he, Matrix.mulVec_mulVec,sig_cert,list_sum_eq _ (no j)]; rfl

end E272.Neutral
