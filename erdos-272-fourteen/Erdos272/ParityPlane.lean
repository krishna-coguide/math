import Erdos272.FullRank
import Mathlib.Data.ZMod.Basic

namespace E272.Neutral
open Finset
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 262144

/-- Every Boolean word is represented by the low bits of some integer. -/
theorem exists_bits (n : ℕ) (f : Fin n → Bool) : ∃ a < 2^n, ∀ j : Fin n, a.testBit j = f j := by
  induction n with
  | zero => exact ⟨0,by decide,fun j => Fin.elim0 j⟩
  | succ n ih =>
    obtain ⟨a,ha,hf⟩ := ih (fun j => f j.castSucc)
    cases h : f (Fin.last n) with
    | false =>
      refine ⟨a,by rw [Nat.pow_succ]; omega,?_⟩
      intro i; refine Fin.lastCases ?_ (fun j => hf j) i
      simpa [h] using Nat.testBit_lt_two_pow ha
    | true =>
      refine ⟨2^n+a,by rw [Nat.pow_succ]; omega,?_⟩
      intro i; refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [h,Nat.testBit_two_pow_add_eq,Nat.testBit_lt_two_pow ha]
      · simpa only [Fin.coe_castSucc,Nat.testBit_two_pow_add_gt j.isLt] using hf j

/-- The bit at row `a` of `plane n j` is the `j`th bit of `a`. -/
def plane : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, j => if j = n then (2^(2^n)-1) <<< (2^n) else
      let v := plane n j
      (v % 2^(2^n)) ||| (v <<< (2^n))

theorem plane_correct (n j a : ℕ) (ha : a < 2^n) (hj : j < n) :
    (plane n j).testBit a = a.testBit j := by
  induction n generalizing a with
  | zero => omega
  | succ n ih =>
    by_cases h : a < 2^n
    · have hb := Nat.testBit_lt_two_pow h
      by_cases e : j = n
      · subst j; simp [plane,Nat.testBit_shiftLeft,h,hb]
      · simp [plane,e,Nat.testBit_or,Nat.testBit_mod_two_pow,Nat.testBit_shiftLeft,h,
          ih a h (by omega)]
    · let b := a-2^n
      have eb : a = 2^n+b := by dsimp [b]; omega
      have hb : b < 2^n := by dsimp [b]; rw [Nat.pow_succ] at ha; omega
      by_cases e : j = n
      · subst j
        have hh : a.testBit n = true := by rw [eb,Nat.testBit_two_pow_add_eq,Nat.testBit_lt_two_pow hb]; rfl
        simp [plane,Nat.testBit_shiftLeft,h,hh,Nat.testBit_two_pow_sub_one,show a-2^n<2^n from hb, Nat.le_of_not_gt h]
      · have hh : a.testBit j = b.testBit j := by rw [eb,Nat.testBit_two_pow_add_gt (by omega)]
        simp [plane,e,Nat.testBit_or,Nat.testBit_mod_two_pow,Nat.testBit_shiftLeft,h,hh,ih b hb (by omega),← show b = a-2^n from rfl, Nat.le_of_not_gt h]

/-- Big integers as parallel truth tables for linear forms on 17 binary parameters. -/
def evalPlane (is : List (Fin 17)) : Nat := is.foldr (fun j x => (plane 17 j) ^^^ x) 0


def bitVal (b : Bool) : ZMod 2 := if b then 1 else 0
private theorem xor_add (a b : Bool) : bitVal (a ^^ b) = bitVal a + bitVal b := by
  cases a <;> cases b <;> decide

theorem evalPlane_correct (xs : List (Fin 17)) (a : ℕ) (ha : a < 2^17) :
    bitVal ((evalPlane xs).testBit a) = (xs.map (fun j : Fin 17 => bitVal (a.testBit j))).sum := by
  induction xs with
  | nil => simp [evalPlane,bitVal]
  | cons i xs ih =>
    change bitVal (((plane 17 i) ^^^ evalPlane xs).testBit a) = _
    rw [Nat.testBit_xor,xor_add,plane_correct 17 i a ha i.isLt,ih]; rfl

end E272.Neutral
