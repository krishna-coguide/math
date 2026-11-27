import Erdos272.Construction
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Tauto

namespace E272.Board
open Finset

/-- A nonempty arithmetic progression with last index `n`. -/
def progression (a d n : ℕ) : Finset ℕ :=
  (range (n+1)).image fun j => a + j*d

def IsAP (s : Finset ℕ) : Prop := ∃ a d n : ℕ, 0 < d ∧ s = progression a d n

/-- A family of subsets of the ordinary one-based board. -/
def ValidFamily (F : Finset (Finset ℕ)) : Prop :=
  (∀ s ∈ F, s ⊆ Icc 1 14) ∧ ∀ s ∈ F, ∀ t ∈ F, s ≠ t → IsAP (s ∩ t)

def points (a : Mask) : Finset ℕ := (Icc 1 14).filter fun x => a.getLsbD (x-1)

private theorem points_inj : Function.Injective points := by
  intro a b he
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h := Finset.ext_iff.mp he (i+1)
  apply Bool.eq_iff_iff.mpr
  simpa [points, show i+1 ≤ 14 by omega] using h

private theorem points_inter (a b : Mask) : points (a &&& b) = points a ∩ points b := by
  ext x; simp [points, BitVec.getLsbD_and]; tauto

private def maskOf (s : Finset ℕ) : Mask :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin 14 => decide (i.val+1 ∈ s))).cast (by simp)

private theorem points_maskOf {s : Finset ℕ} (hs : s ⊆ Icc 1 14) : points (maskOf s) = s := by
  ext x
  by_cases hx : x ∈ Icc 1 14
  · have h := Finset.mem_Icc.mp hx
    have hi : x-1 < 14 := by omega
    have hx' : x-1+1 = x := by omega
    have hi' : x-1 < (List.ofFn fun i : Fin 14 => decide (i.val+1 ∈ s)).length := by
      simpa only [List.length_ofFn] using hi
    simp only [points,mem_filter,hx,true_and,maskOf,BitVec.getLsbD_cast,
      BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi',
      Option.getD_some,List.getElem_ofFn,hx',decide_eq_true_eq]
  · have hnot : x ∉ s := fun h => hx (hs h)
    simp [points,hx,hnot]

private def catalogue : Finset (Finset ℕ) :=
  (Icc 1 14).biUnion fun a => (Icc 1 13).biUnion fun d =>
    ((range 14).filter fun n => a+n*d ≤ 14).image (progression a d)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem table : apMasks.toFinset.image points = catalogue := by decide +kernel

private theorem catalogue_iff {s : Finset ℕ} (hs : s ⊆ Icc 1 14) : s ∈ catalogue ↔ IsAP s := by
  simp only [catalogue,mem_biUnion, mem_Icc, mem_image,mem_filter,mem_range]
  constructor
  · rintro ⟨a,_,d,hd,n,_,rfl⟩; exact ⟨a,d,n,by omega,rfl⟩
  · rintro ⟨a,d,n,hd,rfl⟩
    have ends (j : ℕ) (hj : j ≤ n) : 1 ≤ a+j*d ∧ a+j*d ≤ 14 :=
      Finset.mem_Icc.mp (hs (mem_image.mpr ⟨j,mem_range.mpr (by omega),rfl⟩))
    have ha : 1 ≤ a ∧ a ≤ 14 := by simpa using ends 0 (Nat.zero_le _)
    have hn := ends n le_rfl
    have hn' : n ≤ n*d := Nat.le_mul_of_pos_right _ hd
    cases n with
    | zero => exact ⟨a,ha,1,by decide,0,by simp [ha.2],by simp [progression]⟩
    | succ n =>
      have hle : d ≤ (n+1)*d := Nat.le_mul_of_pos_left _ (by omega)
      exact ⟨a,ha,d,by omega,n+1,by omega,rfl⟩

theorem ap_iff (m : Mask) : ap m = true ↔ IsAP (points m) := by
  have hs : points m ⊆ Icc 1 14 := filter_subset _ _
  rw [← catalogue_iff hs, ← table]
  simp [ap, points_inj.eq_iff]

theorem lower : ∃ F : Finset (Finset ℕ), F.card = 95 ∧ ValidFamily F := by
  obtain ⟨G,hg,hv⟩ := E272.lower_bound
  refine ⟨G.image points, (card_image_of_injective _ points_inj).trans hg, ?_, ?_⟩
  · intro s hs; obtain ⟨m,_,rfl⟩ := mem_image.mp hs; exact filter_subset _ _
  · intro s hs t ht hne
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hs; obtain ⟨n,hn,rfl⟩ := mem_image.mp ht
    rw [← points_inter]; exact (ap_iff _).mp (hv _ hm _ hn (fun h => hne (congrArg points h)))

theorem upper_of_masks {K : ℕ} (bound : ∀ G : Finset Mask, Valid G → G.card ≤ K)
    (F : Finset (Finset ℕ)) (hf : ValidFamily F) : F.card ≤ K := by
  have hp {s} (hs : s ∈ F) := points_maskOf (hf.1 s hs)
  have inj : Set.InjOn maskOf (F : Set (Finset ℕ)) := by
    intro s hs t ht he; simpa [hp hs,hp ht] using congrArg points he
  rw [← card_image_of_injOn inj]
  apply bound; intro a ha b hb hne
  obtain ⟨s,hs,rfl⟩ := mem_image.mp ha; obtain ⟨t,ht,rfl⟩ := mem_image.mp hb
  apply (ap_iff _).mpr; rw [points_inter,hp hs,hp ht]
  exact hf.2 s hs t ht (fun he => hne (congrArg maskOf he))

/-- The exact optimum stated without masks, lookup tables, or search hypotheses
    other than the separately checked upper theorem. -/
theorem exact_of_upper (bound : ∀ G : Finset Mask, Valid G → G.card ≤ 95) :
    IsGreatest {n : ℕ | ∃ F : Finset (Finset ℕ), F.card = n ∧ ValidFamily F} 95 := by
  refine ⟨lower, ?_⟩
  rintro n ⟨F,rfl,hf⟩; exact upper_of_masks bound F hf

end E272.Board
