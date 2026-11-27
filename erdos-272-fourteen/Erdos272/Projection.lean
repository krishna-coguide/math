import Erdos272.ScoreTables

namespace E272

/-- Reindex a truth table by `b ↦ a ∩ b`, copying half-blocks for bits missing in `a`. -/
def projectTable : Nat → Nat → Nat → Nat
  | 0, _, t => t % 2
  | n+1, a, t =>
    if t = 0 then 0 else
    let half := 2^n
    let lo := projectTable n a (t % (2^half))
    let hi := if a.testBit n then projectTable n a (t >>> half) else lo
    lo % (2^half) ||| (hi <<< half)

private theorem and_high (a n b : Nat) (hb : b < 2^n) :
    a &&& (2^n + b) = (if a.testBit n then 2^n else 0) + (a &&& b) := by
  have hb' : 2^n + b = 2^n ||| b := by simpa using Nat.two_pow_add_eq_or_of_lt hb 1
  have he : a &&& (2^n) = if a.testBit n then 2^n else 0 := by
    apply Nat.eq_of_testBit_eq; intro j
    by_cases h : j = n
    · subst j; cases hn : a.testBit n <;> simp [Nat.testBit_and,hn]
    · cases hn : a.testBit n <;> simp [Nat.testBit_and, Ne.symm h]
  rw [hb', Nat.and_or_distrib_left, he]
  split
  · simpa using (Nat.two_pow_add_eq_or_of_lt (Nat.and_lt_two_pow (x := a) hb) 1).symm
  · simp

theorem project_spec (n a t b : Nat) (hb : b < 2^n) :
    (projectTable n a t).testBit b = t.testBit (a &&& b) := by
  induction n generalizing t b with
  | zero =>
    have h : b = 0 := by simpa using hb
    subst b
    change (t % 2^1).testBit 0 = t.testBit (a &&& 0)
    simp only [Nat.testBit_mod_two_pow, Nat.and_zero]; rfl
  | succ n ih =>
    rw [projectTable]
    by_cases ht : t = 0
    · simp [ht]
    simp only [ht, ↓reduceIte, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
    by_cases h : b < 2^n
    · simp [h, Nat.not_le.mpr h, ih _ _ h, Nat.testBit_mod_two_pow, Nat.and_lt_two_pow (x := a) h]
    · let d := b - 2^n
      have e : b = 2^n + d := by dsimp [d]; omega
      have hd : d < 2^n := by dsimp [d]; rw [Nat.pow_succ] at hb; omega
      have hle : b ≥ 2^n := Nat.le_of_not_gt h
      simp only [h, hle, decide_false, decide_true, Bool.false_and, Bool.true_and, Bool.false_or]
      change (if a.testBit n then projectTable n a (t >>> 2^n) else projectTable n a (t % 2^(2^n))).testBit d = _
      rw [e, and_high _ _ _ hd]
      cases ht' : a.testBit n <;> simp [ih _ _ hd, Nat.testBit_mod_two_pow, Nat.and_lt_two_pow (x := a) hd]

/-- Row includes a loop exactly when the vertex is an AP. Distinctness is handled separately. -/
def apRow (a : Mask) : Nat := projectTable 14 a.toNat apTable

theorem apRow_bit (a b : Mask) : (apRow a).testBit b.toNat = ap (a &&& b) := by
  rw [apRow, project_spec _ _ _ _ b.isLt]
  exact apTable_bit (a &&& b)

end E272
