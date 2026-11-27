import Erdos272.Basic
import Mathlib.Data.Finset.Card

namespace E272

/-- A bucket contains one representative, and sets containing `need` but not its AP hull. -/
structure Bucket where
  rep : Mask
  need : Mask
  hull : Mask
  deriving DecidableEq

def Bucket.covers (c : Bucket) (a : Mask) : Bool :=
  a == c.rep || (sub c.need a && !sub c.hull a)

def Bucket.sound (c : Bucket) : Bool :=
  sub c.need c.rep && apMasks.all (fun p => !sub c.need p || sub c.hull p)

theorem Bucket.separates {c : Bucket} (hs : c.sound = true) {a b : Mask}
    (ha : c.covers a = true) (hb : c.covers b = true) (hp : ap (a &&& b) = true) : a = b := by
  obtain ⟨hr, hh⟩ := Bool.and_eq_true_iff.mp hs
  have hm : a &&& b ∈ apMasks := List.contains_iff_mem.mp hp
  have hk := List.all_eq_true.mp hh _ hm
  simp only [covers, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true'] at ha hb
  have hn : sub c.need (a &&& b) = true := sub_inter.mpr ⟨by rcases ha with h | h <;> simp_all,
    by rcases hb with h | h <;> simp_all⟩
  have hhull : sub c.hull (a &&& b) = true := by simpa [hn] using hk
  obtain ⟨ha',hb'⟩ := sub_inter.mp hhull
  rcases ha with h | h <;> rcases hb with k | k <;> simp_all

/-- A valid family injects into any sound list of buckets covering it. -/
theorem bound_of_buckets (F : Finset Mask)
    (hF : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (cs : List Bucket) (hs : cs.all Bucket.sound = true)
    (hc : ∀ a ∈ F, cs.any (fun c => c.covers a) = true) : F.card ≤ cs.length := by
  classical
  have ex (a : F) : ∃ c ∈ cs, c.covers a.val = true := List.any_eq_true.mp (hc _ a.property)
  let f (a : F) : cs.toFinset := ⟨(ex a).choose, List.mem_toFinset.mpr (ex a).choose_spec.1⟩
  apply le_trans (Finset.card_le_card_of_injective (f := f) ?_) (List.toFinset_card_le _)
  intro a b he
  apply Subtype.ext
  by_contra hne
  have he' : (ex a).choose = (ex b).choose := congrArg Subtype.val he
  have hb := (ex b).choose_spec.2
  rw [← he'] at hb
  exact hne (Bucket.separates (List.all_eq_true.mp hs _ (ex a).choose_spec.1)
    (ex a).choose_spec.2 hb (hF _ a.property _ b.property hne))

end E272
