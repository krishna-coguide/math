import Erdos272.Basic

namespace E272

/-- Bit `a` of this table records whether `a` contains the low `n` bits of `t`. -/
def supers : Nat → Nat → Nat
  | 0, _ => 1
  | n+1, t =>
    let s := supers n t
    ((if t.testBit n then 0 else s) % (2^(2^n))) ||| (s <<< (2^n))

private theorem supers_iff (n t a : Nat) (ha : a < 2^n) :
    (supers n t).testBit a = true ↔ ∀ j < n, t.testBit j = true → a.testBit j = true := by
  induction n generalizing a with
  | zero =>
    have : a = 0 := by simpa using ha
    subst a
    simp [supers]
  | succ n ih =>
    simp only [supers, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
    by_cases h : a < 2^n
    · have hbit := Nat.testBit_lt_two_pow h
      have hn : ¬ a ≥ 2^n := Nat.not_le.mpr h
      cases ht : t.testBit n <;> simp [h, hn, ih a h, Nat.lt_succ_iff_lt_or_eq, ht, hbit] <;> grind
    · let b := a - 2^n
      have e : a = 2^n + b := by dsimp [b]; omega
      have hb : b < 2^n := by dsimp [b]; rw [Nat.pow_succ] at ha; omega
      have hi : a.testBit n = true := by rw [e, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hb]; rfl
      have hj (j : Nat) (hjn : j < n) : a.testBit j = b.testBit j := by
        rw [e, Nat.testBit_two_pow_add_gt hjn]
      have he : a ≥ 2^n := Nat.le_of_not_gt h
      simp only [h, he, decide_false, decide_true, Bool.false_and, Bool.true_and, Bool.false_or]
      change (supers n t).testBit b = true ↔ _
      rw [ih b hb]
      constructor
      · intro hh j hjs ht
        rcases Nat.lt_succ_iff_lt_or_eq.mp hjs with hjn | rfl
        · rw [hj j hjn]; exact hh j hjn ht
        · exact hi
      · intro hh j hjn ht; rw [← hj j hjn]; exact hh j (Nat.lt_succ_of_lt hjn) ht

theorem supers_bit (t a : Mask) : (supers 14 t.toNat).testBit a.toNat = sub t a := by
  apply Bool.eq_iff_iff.mpr
  rw [supers_iff _ _ _ a.isLt]
  simp only [sub, beq_iff_eq]
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_and]
    cases ht : t.getLsbD j with
    | false => rfl
    | true => simpa [BitVec.testBit_toNat] using h j hj ht
  · intro h j hj ht
    have eq := congrArg (fun z : Mask => z.getLsbD j) h
    change t.getLsbD j = true at ht
    simpa [BitVec.getLsbD_and, BitVec.testBit_toNat, ht] using eq

end E272
