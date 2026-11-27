import Erdos272.NeutralBound
import Erdos272.Projection
import Erdos272.Construction

namespace E272.Search

/-- `P` is an overestimate of the family; `req` records progressions that
are known to be contained in some member, not necessarily themselves members. -/
def Safe (K P : Nat) (req : List Mask) : Prop := ∀ F : Finset Mask, Valid F →
    (∀ x : Fin 14, ∃ a ∈ F, a.getLsbD x = false) →
    (∀ a ∈ F, P.testBit a.toNat = true) →
    (∀ t ∈ req, ∃ a ∈ F, sub t a = true) → F.card ≤ K

def live (P : Nat) (t : Mask) : Bool := P &&& supers 14 t.toNat != 0

private theorem live_of {a t : Mask} {P : Nat} (hp : P.testBit a.toNat = true) (ht : sub t a = true) :
    live P t = true := by
  simp only [live, bne_iff_ne]; intro he
  have h := congrArg (fun v : Nat => v.testBit a.toNat) he
  simp [Nat.testBit_and, hp, supers_bit, ht] at h

def noOmitter (P : Nat) (i : Fin 14) : Bool :=
  (P &&& (board ^^^ supers 14 (((1 : Mask) <<< i.val).toNat))) == 0

private theorem sub_point_false {a : Mask} {i : Fin 14} (ha : a.getLsbD i = false) :
    sub ((1 : Mask) <<< i.val) a = false := by
  apply Bool.eq_false_iff.mpr; intro h
  simp only [sub, beq_iff_eq] at h
  have he := congrArg (fun t : Mask => t.getLsbD i) h
  simp [i.isLt] at he
  rw [BitVec.getLsbD_eq_getElem i.isLt, he] at ha
  contradiction

/-- The cardinality bound used at rank leaves, needed only above the search target. -/
def RankBound (K cap : Nat) : Prop := ∀ F : Finset Mask, Valid F →
    (∀ x : Fin 14, ∃ a ∈ F, a.getLsbD x = false) → K < F.card →
    F.card ≤ 92 + (activeLong F).length + min cap (F ∩ zeroLong.toFinset).card

theorem rankBoundFour (K : Nat) : RankBound K 4 :=
  fun F hf hn _ => Neutral.capped_mobius_cost F hf hn

def autoCut (cap K P : Nat) (req : List Mask) : Bool :=
  decide (92 + posLong.countP (live P) + min cap (zeroLong.countP (fun a => P.testBit a.toNat)) ≤ K) ||
  req.any (fun t => !live P t) || (List.finRange 14).any (noOmitter P)

theorem auto_sound {cap K P : Nat} {req : List Mask} (rk : RankBound K cap) (h : autoCut cap K P req = true) : Safe K P req := by
  intro F hf hn hp hr
  simp only [autoCut,Bool.or_eq_true,decide_eq_true_eq,List.any_eq_true] at h
  rcases h with (h | ⟨t,ht,hm⟩) | ⟨i,_,hi⟩
  · have hA : (activeLong F).length ≤ posLong.countP (live P) := by
      unfold activeLong; rw [← List.countP_eq_length_filter]
      apply List.countP_mono_left; intro t _ hpos
      obtain ⟨a,ha,had⟩ := of_decide_eq_true hpos
      exact live_of (hp a ha) had
    have hZ : (F ∩ zeroLong.toFinset).card ≤ zeroLong.countP (fun a => P.testBit a.toNat) := by
      apply (Finset.card_le_card (t := (zeroLong.filter (fun a => P.testBit a.toNat)).toFinset) ?_).trans
      · simpa only [← List.countP_eq_length_filter] using (List.toFinset_card_le (l := zeroLong.filter (fun a => P.testBit a.toNat)))
      · intro a ha; obtain ⟨hF,hz⟩ := Finset.mem_inter.mp ha
        exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_toFinset.mp hz,hp a hF⟩)
    by_cases hsmall : F.card ≤ K
    · exact hsmall
    · have hh := rk F hf hn (by omega); omega
  · obtain ⟨a,ha,hs⟩ := hr t ht
    simp [live_of (hp a ha) hs] at hm
  · obtain ⟨a,ha,hs⟩ := hn i
    have he := congrArg (fun b : Nat => b.testBit a.toNat) (beq_iff_eq.mp hi)
    simp only [Nat.testBit_and,Nat.testBit_xor,board_bit,supers_bit,hp a ha,sub_point_false hs,
      Nat.zero_testBit] at he
    contradiction

def yesToken (P : Nat) (t : Mask) : Nat :=
  P &&& (apRow t ||| projectTable 14 t.toNat 1)

def noToken (P : Nat) (t : Mask) : Nat := P &&& (board ^^^ supers 14 t.toNat)

theorem token {K P req} {t : Mask} (ht : t ∈ posLong)
    (hy : Safe K (yesToken P t) (t::req)) (hn : Safe K (noToken P t) req) : Safe K P req := by
  intro F hf hstar hp hr
  by_cases h : ∃ a ∈ F, sub t a = true
  · apply hy F hf hstar
    · intro b hb; obtain ⟨a,ha,hA⟩ := h
      rcases active_posLong_trace hf ht ha hA hb with h0 | hAP
      · simp only [yesToken,Nat.testBit_and,Nat.testBit_or,apRow_bit,hp b hb,Bool.true_and,project_spec _ _ _ _ b.isLt]
        change (ap (t &&& b) || (1:Nat).testBit (t &&& b).toNat) = true
        simp [h0]
      · simp [yesToken,Nat.testBit_and,Nat.testBit_or,apRow_bit,hp b hb,hAP]
    · intro z hz; rcases List.mem_cons.mp hz with rfl | hz; exact h; exact hr z hz
  · apply hn F hf hstar _ hr
    intro b hb; have he : sub t b = false := Bool.eq_false_iff.mpr (fun e => h ⟨b,hb,e⟩)
    simp [noToken,Nat.testBit_and,Nat.testBit_xor,board_bit,supers_bit,hp b hb,he]

def yesMem (P : Nat) (a : Mask) : Nat := P &&& ((2^a.toNat) ||| apRow a)
def noMem (P : Nat) (a : Mask) : Nat := P &&& (board ^^^ (2^a.toNat))

theorem member {K P req} (a : Mask) (hy : Safe K (yesMem P a) req)
    (hn : Safe K (noMem P a) req) : Safe K P req := by
  intro F hf hstar hp hr
  by_cases ha : a ∈ F
  · apply hy F hf hstar _ hr; intro b hb
    by_cases he : a = b
    · subst b; simp [yesMem,Nat.testBit_and,Nat.testBit_or,hp a ha]
    · simp [yesMem,Nat.testBit_and,Nat.testBit_or,apRow_bit,hf a ha b hb he,hp b hb]
  · apply hn F hf hstar _ hr; intro b hb
    have he : a ≠ b := fun e => ha (e.symm ▸ hb)
    simp [noMem,Nat.testBit_and,Nat.testBit_xor,BitVec.toNat_inj,he,board_bit,hp b hb]

/-- The pool obtained by requiring each listed mask to be a family member. -/
def seeded : List Mask → Nat
  | [] => board
  | a :: s => yesMem (seeded s) a

theorem seeded_covers {F : Finset Mask} (hf : Valid F) {s : List Mask}
    (hs : ∀ t ∈ s, t ∈ F) : ∀ a ∈ F, (seeded s).testBit a.toNat = true := by
  induction s with
  | nil => exact fun a _ => board_bit a
  | cons t s ih =>
    intro a ha
    have hp := ih (fun v hv => hs v (List.mem_cons_of_mem _ hv)) a ha
    by_cases he : t = a
    · subst t; simp [seeded,yesMem,Nat.testBit_and,Nat.testBit_or,hp]
    · simp [seeded,yesMem,Nat.testBit_and,Nat.testBit_or,apRow_bit,hp,
        hf t (hs _ List.mem_cons_self) a ha he]

end E272.Search
