import Erdos272.Search
import Erdos272.ColorProof

namespace E272.Search

inductive Cert where
  | rank
  | paint (code : Nat)
  | mem (a : Mask) (yes no : Cert)
  | tok (t : Mask) (yes no : Cert)

def verify (K P : Nat) (req : List Mask) : Cert → Bool
  | .rank => autoCut K P req
  | .paint code => checkPackedPaint P K code
  | .mem a yes no => verify K (yesMem P a) req yes && verify K (noMem P a) req no
  | .tok t yes no => posLong.contains t && verify K (yesToken P t) (t::req) yes &&
      verify K (noToken P t) req no

theorem verified (K P : Nat) (req : List Mask) (c : Cert) (h : verify K P req c = true) : Safe K P req := by
  induction c generalizing P req with
  | rank => exact auto_sound h
  | paint code =>
    intro F hg _ hp _; exact packed_paint_bound F hg hp h
  | mem a _ _ ih ih' =>
    obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp h
    exact member a (ih _ _ l) (ih' _ _ r)
  | tok t _ _ ih ih' =>
    obtain ⟨hl,r⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨ht,l⟩ := Bool.and_eq_true_iff.mp hl
    exact token (List.contains_iff_mem.mp ht) (ih _ _ l) (ih' _ _ r)

end E272.Search
