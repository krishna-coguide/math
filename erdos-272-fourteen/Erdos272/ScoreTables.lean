import Erdos272.Tables

namespace E272

set_option maxRecDepth 12000
set_option exponentiation.threshold 32768

/-- Binary addition on many independent inputs. Bit `i` in each word is one input. -/
def ripple (flag : Nat) : List Nat → List Nat
  | [] => [flag]
  | x::xs => (x ^^^ flag) :: ripple (x &&& flag) xs

def valueAt (i : Nat) : List Nat → Nat
  | [] => 0
  | x::xs => (x.testBit i).toNat + 2 * valueAt i xs

theorem value_ripple (i f : Nat) (xs : List Nat) :
    valueAt i (ripple f xs) = valueAt i xs + (f.testBit i).toNat := by
  induction xs generalizing f with
  | nil => simp [ripple, valueAt]
  | cons x xs ih =>
    simp only [ripple, valueAt, ih, Nat.testBit_xor, Nat.testBit_and]
    cases x.testBit i <;> cases f.testBit i <;> simp <;> omega

def tallies (cs : List Mask) : List Nat := cs.foldr (fun c xs => ripple (supers 14 c.toNat) xs) []

theorem value_tallies (a : Mask) (cs : List Mask) :
    valueAt a.toNat (tallies cs) = cs.countP (fun t => sub t a) := by
  induction cs with
  | nil => rfl
  | cons x xs ih =>
    change valueAt a.toNat (ripple _ (tallies xs)) = _
    rw [value_ripple, supers_bit, ih, List.countP_cons]
    cases sub x a <;> simp

def board : Nat := 2^16384-1

theorem board_bit (a : Mask) : board.testBit a.toNat = true := by
  change (2^16384-1 : Nat).testBit a.toNat = true
  rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
  exact a.isLt

/-- Pad at the high end. Padding may add zero digits but cannot change a tally. -/
def align : List Nat → List Nat → List (Nat × Nat)
  | [], ys => ys.map (fun y => (0,y))
  | x::xs, [] => (x,0) :: align xs []
  | x::xs, y::ys => (x,y) :: align xs ys

private theorem align_values (i : Nat) (xs ys : List Nat) :
    valueAt i ((align xs ys).map Prod.fst) = valueAt i xs ∧
    valueAt i ((align xs ys).map Prod.snd) = valueAt i ys := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => exact ⟨rfl,rfl⟩
    | cons y ys ih =>
      change ((0:Nat).testBit i).toNat + 2 * valueAt i ((align [] ys).map Prod.fst) = 0 ∧
        (y.testBit i).toNat + 2 * valueAt i ((align [] ys).map Prod.snd) = _
      rw [ih.1, ih.2]; simp [valueAt]
  | cons x xs ih =>
    cases ys with
    | nil =>
      simp only [align, List.map_cons, valueAt, (ih []).1, (ih []).2, Nat.zero_testBit, Bool.toNat_false]
      simp
    | cons y ys =>
      simp only [align, List.map_cons, valueAt, (ih ys).1, (ih ys).2, and_self]

/-- Equal and greater-than masks, comparing the most significant bits first. -/
def cmp : List (Nat × Nat) → Nat × Nat
  | [] => (board,0)
  | (x,y)::xs =>
    let (eq,gt) := cmp xs
    (eq &&& (board ^^^ (x ^^^ y)), gt ||| (eq &&& x &&& (board ^^^ y)))

private theorem cmp_correct (a : Mask) (zs : List (Nat × Nat)) :
    ((cmp zs).1.testBit a.toNat = true ↔ valueAt a.toNat (zs.map Prod.fst) = valueAt a.toNat (zs.map Prod.snd)) ∧
    ((cmp zs).2.testBit a.toNat = true ↔ valueAt a.toNat (zs.map Prod.fst) > valueAt a.toNat (zs.map Prod.snd)) := by
  induction zs with
  | nil =>
    change (board.testBit a.toNat = true ↔ (0:Nat) = 0) ∧ ((0:Nat).testBit a.toNat = true ↔ (0:Nat) > 0)
    rw [board_bit]; simp
  | cons xy zs ih =>
    rcases xy with ⟨x,y⟩
    simp only [cmp, List.map_cons, valueAt, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or,
      board_bit, Bool.or_eq_true, Bool.and_eq_true, ih.1, ih.2]
    cases hx : x.testBit a.toNat <;> cases hy : y.testBit a.toNat <;> simp <;> omega

/-- The first table marks equal positive and negative tallies; the second marks surplus. -/
def eqgt : Nat × Nat := cmp (align (tallies pos) (tallies neg))

theorem eqgt_correct (a : Mask) :
    (eqgt.1.testBit a.toNat = true ↔ score a = 0) ∧
    (eqgt.2.testBit a.toNat = true ↔ 0 < score a) := by
  have hv := align_values a.toNat (tallies pos) (tallies neg)
  have h := cmp_correct a (align (tallies pos) (tallies neg))
  rw [hv.1, hv.2, value_tallies, value_tallies] at h
  change ((cmp _).1.testBit _ = true ↔ _) ∧ ((cmp _).2.testBit _ = true ↔ _)
  simp only [h.1, h.2, score]
  omega

def unionTable (f : Mask → Nat) (ts : List Mask) : Nat := ts.foldr (fun t s => f t ||| s) 0

theorem unionTable_bit (a : Mask) (f : Mask → Nat) (ts : List Mask) :
    (unionTable f ts).testBit a.toNat = ts.any (fun t => (f t).testBit a.toNat) := by
  induction ts with
  | nil => simp [unionTable]
  | cons x xs ih => simpa only [unionTable, List.foldr_cons, Nat.testBit_or, List.any_cons] using (congrArg (fun b => (f x).testBit a.toNat || b) ih)

def apTable : Nat := unionTable (fun t => 2^t.toNat) apMasks
def shortTable : Nat := board ^^^ unionTable (fun t => supers 14 t.toNat) sevens

theorem apTable_bit (a : Mask) : apTable.testBit a.toNat = ap a := by
  rw [apTable, unionTable_bit, ap]
  simp only [Nat.testBit_two_pow, BitVec.toNat_inj]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, decide_eq_true_eq, List.contains_iff_mem, exists_eq_right]

theorem shortTable_bit (a : Mask) : shortTable.testBit a.toNat = short a := by
  simp only [shortTable, Nat.testBit_xor, board_bit, unionTable_bit, supers_bit, short]
  cases sevens.any (fun t => sub t a) <;> rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem good_cert : shortTable &&& apTable &&& eqgt.1 = shortTable &&& apTable := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bad_cert : shortTable &&& (board ^^^ apTable) &&& eqgt.2 =
    shortTable &&& (board ^^^ apTable) := by decide +kernel

theorem tab_score_good {a : Mask} (hs : short a = true) (ha : ap a = true) : score a = 0 := by
  apply (eqgt_correct a).1.mp
  have h := congrArg (fun n : Nat => n.testBit a.toNat) good_cert
  simpa [Nat.testBit_and, shortTable_bit, apTable_bit, hs, ha] using h

theorem tab_score_bad {a : Mask} (hs : short a = true) (ha : ap a = false) : 0 < score a := by
  apply (eqgt_correct a).2.mp
  have h := congrArg (fun n : Nat => n.testBit a.toNat) bad_cert
  simpa [Nat.testBit_and, Nat.testBit_xor, board_bit, shortTable_bit, apTable_bit, hs, ha] using h

end E272
