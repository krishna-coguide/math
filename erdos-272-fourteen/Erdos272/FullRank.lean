import Erdos272.Rank
import Erdos272.Catalog

namespace E272
open Finset RankProof
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

/-- Positive long features of the full Möbius score on the AP poset. -/
def elevens : List Mask := [2047, 4094, 8188, 16376]
def posLong : List Mask := sevens ++ elevens
def negLong : List Mask := [255, 510, 1020, 2040, 4080, 4095, 8160, 8190, 16320, 16380, 16383]
def zeroLong : List Mask := [511, 1022, 1023, 2044, 2046, 4088, 4092, 8176, 8184, 8191, 16352, 16368, 16382]
def fullPos := pos ++ posLong
def fullNeg := neg ++ negLong

def fullScore (a : Mask) : Int :=
  (fullPos.countP (fun t => sub t a) : Int) - (fullNeg.countP (fun t => sub t a) : Int)

/-- Adding the long features never decreases the score: charge each 8- or 12-interval
    to its prefix, and the 14-interval to the progression of odd points. -/
private theorem charge_long (a : Mask) : negLong.countP (fun t => sub t a) ≤ posLong.countP (fun t => sub t a) := by
  let charged : List Mask := [127, 254, 508, 1016, 2032, 2047, 4064, 4094, 8128, 8188, 5461]
  let rest : List Mask := [10922, 16256, 16376]
  have perm : posLong.Perm (charged ++ rest) := by decide +kernel
  have sublists : List.Forall₂ (fun p q => sub p q = true) charged negLong := by decide +kernel
  have H : ∀ {ps qs : List Mask}, List.Forall₂ (fun p q => sub p q = true) ps qs →
      qs.countP (fun t => sub t a) ≤ ps.countP (fun t => sub t a) := by
    intro ps qs h
    induction h with
    | nil => simp
    | @cons p q ps qs h hs ih =>
      simp only [List.countP_cons]
      have tr (hq : sub q a = true) : sub p a = true := by
        simp only [sub,beq_iff_eq] at *
        calc
          p &&& a = (p &&& q) &&& a := by rw [h]
          _ = p &&& (q &&& a) := BitVec.and_assoc ..
          _ = p := by rw [hq,h]
      cases hp : sub p a <;> cases hq : sub q a <;> simp_all; omega
  rw [perm.countP_eq, List.countP_append]
  exact (H sublists).trans (Nat.le_add_right _ _)

theorem fullScore_ap {a : Mask} (ha : ap a = true) : fullScore a = 0 := by
  have tab : ∀ i : Fin apMasks.length, fullScore apMasks[i] = 0 := by decide +kernel
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem (List.contains_iff_mem.mp ha : a ∈ apMasks)
  exact tab ⟨i,hi⟩

theorem fullScore_not_ap {a : Mask} (ha : ap a = false) : 0 < fullScore a := by
  by_cases hs : a ∈ special
  · have tab : ∀ i : Fin special.length, ap special[i] = false → 0 < fullScore special[i] := by decide +kernel
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hs
    exact tab ⟨i,hi⟩ ha
  · rcases healthy_of_not_special hs with ⟨h,_⟩ | h
    · simp_all
    · have hh := charge_long a
      simp only [score] at h
      simp only [fullScore,fullPos,fullNeg,List.countP_append,Nat.cast_add]
      omega

private theorem long_covered {a : Mask} (ha : ap a = true) (hs : short a = false) (hz : a ∉ zeroLong) :
    a ∈ posLong ∨ a ∈ negLong := by
  have tab : ∀ i : Fin apMasks.length, short apMasks[i] = false → apMasks[i] ∉ zeroLong →
      apMasks[i] ∈ posLong ∨ apMasks[i] ∈ negLong := by decide +kernel
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem (List.contains_iff_mem.mp ha : a ∈ apMasks)
  exact tab ⟨i,hi⟩ hs hz

private theorem inc_long_short {t a : Mask} (ht : short t = false) (ha : short a = true) : inc t a = 0 := by
  by_cases h : sub t a = true
  · have hs := short_inter_left (b := t) ha
    rw [BitVec.and_comm] at hs
    simp only [sub,beq_iff_eq] at h
    simp_all
  · simp [inc,h]

/-- All of the possible long-AP kernel rows disappear if the zero-weight long APs
    are excluded as *members*. They need not be excluded as intersections. -/
private theorem long_elim (c : Mask → ℚ)
    (hc : ∀ a, c a ≠ 0 → ap a = true ∧ a ∉ zeroLong)
    (hann : ∀ t, (t ∈ posLong ∨ t ∈ negLong) → ∑ a, c a * inc t a = 0) :
    ∀ a, c a ≠ 0 → short a = true := by
  let b := fun a => if short a then 0 else c a
  have hz := zeta_unique b (by
    intro t ht
    have hs : short t = false := by cases e : short t <;> simp_all [b]
    have hct : c t ≠ 0 := by simpa [b,hs] using ht
    rw [← hann t (long_covered (hc t hct).1 hs (hc t hct).2)]
    apply Finset.sum_congr rfl; intro a _
    cases e : short a with
    | false => simp [b,e]
    | true => simp [b,e,inc_long_short hs e])
  intro a ha
  cases h : short a <;> simp_all [b]

/-- Cost one dimension per *active* positive long feature. Removing zero-weight
    long AP members is sufficient; other long AP members are allowed. -/
theorem mobius_rank_bound {F S : Finset Mask} (hSF : S ⊆ F)
    (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false)
    (hz : ∀ a ∈ S, a ∉ zeroLong) (L : List Mask)
    (hL : ∀ t ∈ posLong, ∀ a ∈ S, sub t a = true → t ∈ L) :
    S.card ≤ 92 + L.length := by
  classical
  let U : S → Fin pos.length ⊕ Fin L.length → ℚ := fun a => Sum.elim (feature pos a) (feature L a)
  have hli : LinearIndependent ℚ U := by
    apply Fintype.linearIndependent_iff.mpr
    intro cs hup v
    have hu (t : Mask) (ht : t ∈ fullPos) : ∑ a : S, cs a * inc t a = 0 := by
      rcases List.mem_append.mp ht with hp | hl
      · obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hp
        simpa [U,feature] using congrFun hup (Sum.inl ⟨i,hi⟩)
      · by_cases hm : t ∈ L
        · obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hm
          simpa [U,feature] using congrFun hup (Sum.inr ⟨i,hi⟩)
        · apply Finset.sum_eq_zero; intro a _
          have hh : ¬ sub t a = true := fun e => hm (hL _ hl _ a.2 e)
          simp [inc,hh]
    let d := fun a : S => (fullScore a : ℚ)
    have hd (a : S) : 0 ≤ d a := by
      dsimp [d]; cases h : ap a with
      | true => simp [fullScore_ap h]
      | false => exact_mod_cast (fullScore_not_ap h).le
    have gg (a b : S) : (∑ i, feature fullPos a i * feature fullPos b i) =
        (∑ j, feature fullNeg a j * feature fullNeg b j) + if a = b then d a else 0 := by
      have h : (fullScore (a.val &&& b.val) : ℚ) = if a = b then d a else 0 := by
        by_cases e : a = b
        · subst b; simp [d]
        · simp [e,fullScore_ap (hg _ (hSF a.2) _ (hSF b.2) (fun eq => e (Subtype.ext eq)))]
      rw [dot_count,dot_count,←h]; simp [fullScore]
    obtain ⟨hv,hk⟩ := gram_kernel (fun a : S => feature fullPos a) (fun a : S => feature fullNeg a) d cs hd gg
      (fun i => hu _ (List.getElem_mem ..))
    let c : Mask → ℚ := fun a => ∑ b : S, if b.val = a then cs b else 0
    have hsum (t : Mask) : (∑ a, c a * inc t a) = ∑ b : S, cs b * inc t b := collapse _ _ _
    have coff (a : Mask) (ha : a ∉ S) : c a = 0 := by
      apply Finset.sum_eq_zero; intro b _
      have hh : b.val ≠ a := fun h => ha (h ▸ b.2)
      simp [hh]
    have con (a : S) : c a = cs a := by
      change (∑ b : S, if b.val = a.val then cs b else 0) = _
      simp
    have hcov (a : Mask) (ha : c a ≠ 0) : ap a = true ∧ a ∉ zeroLong := by
      by_cases hm : a ∈ S
      · refine ⟨?_,hz a hm⟩
        cases e : ap a with
        | false =>
          let b : S := ⟨a,hm⟩
          have H : 0 < d b := by change 0 < (fullScore a : ℚ); exact_mod_cast fullScore_not_ap e
          exact False.elim (ha ((con b).trans (hk b H)))
        | true => rfl
      · exact False.elim (ha (coff _ hm))
    have hann (t : Mask) (ht : t ∈ fullPos ∨ t ∈ fullNeg) : ∑ a, c a * inc t a = 0 := by
      rw [hsum]; obtain h | h := ht
      · exact hu _ h
      · obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem h
        exact hv ⟨i,hi⟩
    have hs := long_elim c hcov (fun t h => hann t (h.imp (List.mem_append_right _) (List.mem_append_right _)))
    have eqn := resolve c (fun a h => ⟨(hcov a h).1,hs a h⟩)
      (fun t h => hann t (h.imp (List.mem_append_left _) (List.mem_append_left _)))
    let z := fun p => c (five p)
    have hproj : ∀ a ∉ F, proj z a = 0 := by
      intro a ha; rw [← eqn a]; exact coff _ (fun hm => ha (hSF hm))
    have hall := center_elim F hg hne z hproj
    rw [← con v,eqn]; change proj z _ = 0; simp [proj,hall]
  have h := hli.fintype_card_le_finrank
  rw [Fintype.card_coe,Module.finrank_pi,Fintype.card_sum,Fintype.card_fin,Fintype.card_fin] at h
  exact h


/-- The positive long features that are nonzero on at least one full family member. -/
def activeLong (F : Finset Mask) : List Mask :=
  posLong.filter (fun t => decide (∃ a ∈ F, sub t a = true))

/-- Unconditional full Möbius rank bound for a nonstar. Only the actual zero-weight
    AP *members* cost a dimension, not all of the zero-weight APs they contain. -/
theorem mobius_cost_bound (F : Finset Mask)
    (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false) :
    F.card ≤ 92 + (activeLong F).length + (F ∩ zeroLong.toFinset).card := by
  classical
  let S := F \ zeroLong.toFinset
  have hSF : S ⊆ F := Finset.sdiff_subset
  have H := mobius_rank_bound hSF hg hne (fun a ha => by simpa using (Finset.mem_sdiff.mp ha).2)
    (activeLong F) (by
      intro t ht a ha hs
      apply List.mem_filter.mpr
      exact ⟨ht,decide_eq_true ⟨a, hSF ha, hs⟩⟩)
  have eq := Finset.card_sdiff_add_card_inter F zeroLong.toFinset
  change (F \ zeroLong.toFinset).card ≤ _ at H
  omega

/-- An active positive AP restricts every family member on its positions to an AP or empty. -/
theorem active_posLong_trace {F : Finset Mask}
    (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    {p : Mask} (hp : p ∈ posLong) {a : Mask} (ha : a ∈ F) (ht : sub p a = true)
    {b : Mask} (hb : b ∈ F) : (p &&& b) = 0 ∨ ap (p &&& b) = true := by
  have htab : ∀ i : Fin posLong.length, ∀ j : Fin apMasks.length,
      posLong[i] &&& apMasks[j] = 0 ∨ ap (posLong[i] &&& apMasks[j]) = true := by decide +kernel
  have hp' : ∀ i : Fin posLong.length, ap posLong[i] = true := by decide +kernel
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hp
  simp only [sub,beq_iff_eq] at ht
  by_cases e : a = b
  · subst b; rw [ht]; exact Or.inr (hp' ⟨i,hi⟩)
  have hab := hg _ ha _ hb e
  rw [← ht,BitVec.and_assoc]
  obtain ⟨j,hj,he⟩ := List.getElem_of_mem (List.contains_iff_mem.mp hab : a &&& b ∈ apMasks)
  rw [←he]; exact htab ⟨i,hi⟩ ⟨j,hj⟩

/-- The 102 bound outside explicitly anchored families. -/
theorem no_anchor_bound (F : Finset Mask)
    (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false)
    (hz : ∀ a ∈ F, a ∉ zeroLong)
    (he : ∀ p ∈ elevens, ∀ a ∈ F, sub p a = false) : F.card ≤ 102 := by
  apply mobius_rank_bound (F := F) (S := F) (by rfl) hg hne hz sevens
  intro t ht a ha hs
  rcases List.mem_append.mp ht with h | h
  · exact h
  · simp_all

end E272
