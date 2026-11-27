import Erdos272.ScoreTables
import Erdos272.Buckets

namespace E272

namespace Paint

def independent : List Mask → Bool
  | [] => true
  | x :: xs => xs.all (fun y => !apTable.testBit (x &&& y).toNat) && independent xs

def covers (cs : List (List Mask)) : Nat :=
  cs.foldr (fun xs r => unionTable (fun a => 2^a.toNat) xs ||| r) 0

private theorem mem_of_bit (a : Mask) (cs : List (List Mask))
    (h : (covers cs).testBit a.toNat = true) : ∃ xs ∈ cs, a ∈ xs := by
  induction cs with
  | nil => simp [covers] at h
  | cons c cs ih =>
    change (_ ||| covers cs).testBit a.toNat = true at h
    rw [Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · refine ⟨c, List.mem_cons_self, ?_⟩
      rw [unionTable_bit, List.any_eq_true] at h
      obtain ⟨b,hb,hab⟩ := h
      simp only [Nat.testBit_two_pow, decide_eq_true_eq, BitVec.toNat_inj] at hab
      subst b; exact hb
    · obtain ⟨zs,hm,ha⟩ := ih h
      exact ⟨zs,List.mem_cons_of_mem _ hm,ha⟩

private theorem separates {c : List Mask} (h : independent c = true)
    {a b : Mask} (ha : a ∈ c) (hb : b ∈ c) (hp : ap (a &&& b) = true) : a = b := by
  induction c with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨h,hs⟩ := Bool.and_eq_true_iff.mp h
    rcases List.mem_cons.mp ha with hax | has
    · subst x
      rcases List.mem_cons.mp hb with rfl | hbs
      · rfl
      · have hm := List.all_eq_true.mp h _ hbs
        simp only [apTable_bit, hp, Bool.not_true, Bool.false_eq_true] at hm
    · rcases List.mem_cons.mp hb with hbx | hbs
      · subst x
        have hm := List.all_eq_true.mp h _ has
        rw [apTable_bit, BitVec.and_comm, hp] at hm
        contradiction
      · exact ih hs has hbs

theorem card_le (F : Finset Mask)
    (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (P K : Nat) (hp : ∀ a ∈ F, P.testBit a.toNat = true) (cs : List (List Mask))
    (hK : cs.length ≤ K) (hi : cs.all independent = true) (hc : P &&& covers cs = P) :
    F.card ≤ K := by
  classical
  have ex (a : F) : ∃ c ∈ cs, a.val ∈ c := by
    apply mem_of_bit
    have h := congrArg (fun n : Nat => n.testBit a.val.toNat) hc
    simpa [Nat.testBit_and, hp _ a.property] using h
  let f (a : F) : cs.toFinset := ⟨(ex a).choose, List.mem_toFinset.mpr (ex a).choose_spec.1⟩
  apply le_trans (Finset.card_le_card_of_injective (f := f) ?_) ((List.toFinset_card_le _).trans hK)
  intro a b he
  apply Subtype.ext
  by_contra hne
  have he' : (ex a).choose = (ex b).choose := congrArg Subtype.val he
  have hb := (ex b).choose_spec.2
  rw [← he'] at hb
  exact hne (separates (List.all_eq_true.mp hi _ (ex a).choose_spec.1)
    (ex a).choose_spec.2 hb (hg _ a.property _ b.property hne))

end Paint

namespace Paint

/-- A class is encoded by its size, then its vertices. All digits are 14 bits. -/
def readClass : Nat → Nat → List Mask
  | 0, _ => []
  | n+1, data => BitVec.ofNat 14 data :: readClass n (data >>> 14)

def readClasses : Nat → Nat → List (List Mask)
  | 0, _ => []
  | k+1, data =>
    let n := data % 16384
    let tail := data >>> 14
    readClass n tail :: readClasses k (tail >>> (14*n))

end Paint

def checkPackedPaint (P K data : Nat) : Bool :=
  let cs := Paint.readClasses K data
  decide (cs.length ≤ K) && cs.all Paint.independent && (P &&& Paint.covers cs == P)

theorem packed_paint_bound {P K code : Nat} (F : Finset Mask)
    (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hp : ∀ a ∈ F, P.testBit a.toNat = true) (ok : checkPackedPaint P K code = true) : F.card ≤ K := by
  simp only [checkPackedPaint, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ok
  exact Paint.card_le F hg P K hp _ ok.1.1 ok.1.2 ok.2

end E272
