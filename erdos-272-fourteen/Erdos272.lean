import Erdos272.Construction
import Erdos272.ShortExample
import Erdos272.Rank
import Erdos272.RankLocal
import Erdos272.Stars
import Erdos272.Catalog
import Mathlib.Tactic.Tauto

namespace E272

/-- The whole family has no common point; no assumption about the intersection
of the subfamily of short masks is needed. -/
theorem nonstar_of_large {F : Finset Mask} (hf : Valid F) (hn : 96 ≤ F.card) :
    ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false := by
  classical
  intro x
  by_contra! h
  have hs := star_bound F hf x (fun a ha => by simpa using h a ha)
  omega

/-- Every hypothetical counterexample must use at least four sets which each
contain a seven-term AP. They need not contain the same progression. -/
theorem four_long {F : Finset Mask} (hf : Valid F) (hn : 96 ≤ F.card) :
    4 ≤ (F.filter (fun a => short a = false)).card := by
  classical
  have h := short_bound F hf (nonstar_of_large hf hn)
  have he := Finset.card_filter_add_card_filter_not (s := F) (p := fun a => short a = true)
  simp only [Bool.not_eq_true] at he
  omega

/-- The stronger obstruction persists after any choice of three deletions. -/
theorem unavoidable_after_three {F : Finset Mask} (hf : Valid F) (hn : 96 ≤ F.card)
    (D : Finset Mask) (hd : D.card ≤ 3) :
    (∃ a ∈ F \ D, ap a = true ∧ short a = false) ∨
    (∃ a ∈ F \ D, ap a = false ∧ score a ≤ 0) ∨
    (∃ a ∈ F \ D, ∃ b ∈ F \ D, a ≠ b ∧ short (a &&& b) = false) :=
  obstruction_after_deletion hf (nonstar_of_large hf hn) hn D hd

/-- The 38 long progressions in the board, and those which actually occur
as the intersection of two distinct members. -/
def longAPs : Finset Mask := (apMasks.filter (fun p => !short p)).toFinset

theorem longAPs_card : longAPs.card = 38 := by decide +kernel

def realized (F : Finset Mask) : Finset Mask := longAPs.filter (fun p =>
  ∃ a ∈ F, ∃ b ∈ F, a ≠ b ∧ a &&& b = p)

private theorem mem_longAPs {a : Mask} : a ∈ longAPs ↔ longProgression a := by
  simp only [longAPs, List.mem_toFinset, List.mem_filter, longProgression, ap, List.contains_iff_mem,
    Bool.not_eq_true']

private theorem ordered_trio {s : Finset Mask} (hs : s.card = 3) :
    ∃ p q r : Mask, p.toNat < q.toNat ∧ q.toNat < r.toNat ∧ s = {p,q,r} := by
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hs
  simp only [← BitVec.toNat_inj, ne_eq] at hab hac hbc
  by_cases h₁ : a.toNat < b.toNat <;> by_cases h₂ : a.toNat < c.toNat <;>
    by_cases h₃ : b.toNat < c.toNat <;> first
    | omega
    | exact ⟨a,b,c,by omega,by omega,rfl⟩
    | exact ⟨a,c,b,by omega,by omega,by ext; simp; tauto⟩
    | exact ⟨b,a,c,by omega,by omega,by ext; simp; tauto⟩
    | exact ⟨b,c,a,by omega,by omega,by ext; simp; tauto⟩
    | exact ⟨c,a,b,by omega,by omega,by ext; simp; tauto⟩
    | exact ⟨c,b,a,by omega,by omega,by ext; simp; tauto⟩

/-- A 96-member family must hit the 54-entry list or realize at least four
*distinct* long progressions as actual pairwise intersections. -/
theorem special_or_four_intersections {F : Finset Mask} (hf : Valid F) (hn : 96 ≤ F.card) :
    (∃ a ∈ F, a ∈ special) ∨ 4 ≤ (realized F).card := by
  classical
  by_contra! h
  obtain ⟨hnone,hfew⟩ := h
  have hle : (realized F).card ≤ 3 := by omega
  obtain ⟨s,hsub,hsU,hs⟩ := Finset.exists_subsuperset_card_eq
    (show realized F ⊆ longAPs from Finset.filter_subset _ _) hle (by rw [longAPs_card]; decide)
  obtain ⟨p,q,r,hpq,hqr,he⟩ := ordered_trio hs
  have hp : longProgression p := mem_longAPs.mp (hsU (by simp [he]))
  have hq : longProgression q := mem_longAPs.mp (hsU (by simp [he]))
  have hr : longProgression r := mem_longAPs.mp (hsU (by simp [he]))
  have h95 := three_pattern_bound (Finset.Subset.refl F) hf (nonstar_of_large hf hn)
    (fun a ha => healthy_of_not_special (hnone a ha)) p q r hp hq hr hpq hqr (by
      intro a ha b hb hab
      cases hsh : short (a &&& b) with
      | true => exact Or.inl rfl
      | false =>
        apply Or.inr
        have hi : a &&& b ∈ realized F := Finset.mem_filter.mpr ⟨
          mem_longAPs.mpr ⟨hf a ha b hb hab,hsh⟩, a,ha,b,hb,hab,rfl⟩
        simpa [he] using hsub hi)
  omega

end E272
