import Erdos272.Tables
import Erdos272.Buckets

namespace E272

set_option exponentiation.threshold 32768

def allBits : Nat := 2^16384-1

theorem allBits_bit (a : Mask) : allBits.testBit a.toNat = true := by
  change (2^16384-1 : Nat).testBit a.toNat = true
  rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
  exact a.isLt

def Bucket.table (c : Bucket) : Nat :=
  2^c.rep.toNat ||| (supers 14 c.need.toNat &&& (allBits ^^^ supers 14 c.hull.toNat))

theorem Bucket.table_bit (c : Bucket) (a : Mask) : c.table.testBit a.toNat = c.covers a := by
  simp only [table, covers, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow,
    allBits_bit, supers_bit]
  have he : decide (c.rep.toNat = a.toNat) = (a == c.rep) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, beq_iff_eq, BitVec.toNat_inj]
    exact eq_comm
  rw [he]
  cases sub c.hull a <;> rfl

def paletteTable (cs : List Bucket) : Nat := cs.foldr (fun c s => c.table ||| s) 0

theorem paletteTable_bit (cs : List Bucket) (a : Mask) :
    (paletteTable cs).testBit a.toNat = cs.any (fun c => c.covers a) := by
  induction cs with
  | nil => simp [paletteTable]
  | cons hd tl ih => simp [paletteTable, Nat.testBit_or, Bucket.table_bit, ← ih]

theorem bound_through (F : Finset Mask) (bit : Mask) (cs : List Bucket)
    (hF : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hstar : ∀ a ∈ F, sub bit a = true) (hs : cs.all Bucket.sound = true)
    (hc : (supers 14 bit.toNat &&& paletteTable cs) = supers 14 bit.toNat) : F.card ≤ cs.length := by
  apply bound_of_buckets F hF cs hs
  intro a ha
  have h := congrArg (fun x : Nat => x.testBit a.toNat) hc
  simpa [Nat.testBit_and, supers_bit, paletteTable_bit, hstar a ha] using h

end E272
