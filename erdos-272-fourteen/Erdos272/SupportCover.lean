import Erdos272.SupportParam
import Erdos272.KernelSupports

namespace E272.Neutral.SupportProof
open Finset RankProof
open scoped Matrix
set_option maxRecDepth 20000
set_option maxHeartbeats 15000000
set_option exponentiation.threshold 4194304

private def pairs : List (XI × XI) := [(0,2), (13,15), (5,16), (6,17), (34,72), (7,26), (10,20), (27,40), (45,60), (31,75), (88,103), (13,63), (9,19), (43,61), (41,55), (59,74), (30,76), (29,54), (13,73), (44,58), (42,56), (27,55), (39,58), (6,26), (86,101), (27,41), (31,45), (7,44), (16,39), (17,27), (16,59), (5,73), (26,76), (21,40), (10,63), (17,58), (20,61), (5,27), (27,43), (39,55), (60,73), (7,74), (0,93), (6,75), (27,73), (5,26), (9,27), (45,59), (2,40), (5,54), (10,15), (10,27), (10,54), (17,39), (19,41), (29,55), (60,76), (26,40), (15,60), (37,72), (29,75), (15,40), (6,45), (10,74), (30,54), (15,27), (7,69), (19,31), (21,29), (58,75), (6,74), (7,39), (15,88), (0,54), (2,60), (26,73)]
private def hulls : List ((Fin 14) × XI × List XI) := [(4,14,[1, 4, 9]), (5,23,[3, 12, 19]), (6,35,[9, 22, 29]), (8,64,[29, 47, 57]), (7,48,[19, 33, 43]), (9,77,[43, 62, 72]), (7,75,[16, 44, 69]), (7,80,[16, 65, 69]), (6,60,[6, 30, 53]), (6,67,[6, 49, 53]), (6,52,[8, 31, 40]), (6,80,[7, 40, 59]), (7,94,[17, 54, 74]), (7,68,[18, 45, 54]), (6,98,[6, 59, 84]), (7,111,[16, 74, 99]), (6,67,[10, 41, 58]), (7,80,[20, 55, 73]), (6,52,[8, 30, 40]), (7,68,[18, 44, 54]), (7,111,[16, 73, 102]), (6,98,[6, 58, 87])]
private def blocks : List (List XI) := (pairs.map (fun p => [p.1,p.2])) ++ (hulls.map (fun r => r.2.1 :: r.2.2))

private theorem all_compat {F : Finset Mask} (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    {a b : Mask} (ha : a ∈ F) (hb : b ∈ F) (hap : ap a = true) : ap (b &&& a) = true := by
  by_cases e : b = a
  · simpa [e] using hap
  · exact hg _ hb _ ha e

private theorem hull_bad {F : Finset Mask} (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false) (r : (Fin 14) × XI × List XI)
    (hr : r ∈ hulls) : ¬ (∀ i ∈ r.2.1 :: r.2.2, testRow i ∈ F) := by
  intro hd
  have tab : ∀ j : Fin hulls.length,
      let g := hulls[j]
      (g.2.2.all (fun i => sub (testRow i) (testRow g.2.1))) = true ∧
      apMasks.all (fun a => a.getLsbD g.1 || !(g.2.2.all (fun i => a &&& testRow i != 0))) = true := by decide +kernel
  have good : ∀ i : XI, ap (testRow i) = true := by decide +kernel
  obtain ⟨j,hj,er⟩ := List.getElem_of_mem hr
  have H := tab ⟨j,hj⟩; change (_ ∧ _) at H
  obtain ⟨hs,hc⟩ := H
  change (hulls[j].2.2.all (fun i => sub (testRow i) (testRow hulls[j].2.1))) = true at hs
  change apMasks.all (fun a => a.getLsbD hulls[j].1 || !(hulls[j].2.2.all (fun i => a &&& testRow i != 0))) = true at hc
  rw [er] at hs hc
  obtain ⟨b,hb,hx⟩ := hne r.1
  have hh := all_compat hg (hd _ (by simp)) hb (good r.2.1)
  have hf := List.all_eq_true.mp hc _ (List.contains_iff_mem.mp hh)
  have hit : r.2.2.all (fun i => (b &&& testRow r.2.1) &&& testRow i != 0) = true := by
    apply List.all_eq_true.mpr; intro i hi
    have h := List.all_eq_true.mp hs i hi
    simp only [sub,beq_iff_eq] at h
    have H' := all_compat hg (hd _ (by simp [hi])) hb (good i)
    apply bne_iff_ne.mpr; intro eq
    have e : b &&& testRow i = 0 := by simpa [BitVec.and_assoc,BitVec.and_comm (testRow r.2.1) _,h] using eq
    rw [e] at H'; exact (by decide : ap 0 ≠ true) H'
  have hno : (b &&& testRow r.2.1).getLsbD r.1 = false := by rw [BitVec.getLsbD_and,hx]; rfl
  rw [hno,hit] at hf; contradiction

private theorem impossible {F : Finset Mask} (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false) (g : List XI) (hg' : g ∈ blocks) :
    ¬ (∀ j ∈ g, testRow j ∈ F) := by
  rcases List.mem_append.mp hg' with hp | hh
  · obtain ⟨⟨a,b⟩,ht,rfl⟩ := List.mem_map.mp hp
    have tab : ∀ i : Fin pairs.length, testRow pairs[i].1 ≠ testRow pairs[i].2 ∧
        ap (testRow pairs[i].1 &&& testRow pairs[i].2) = false := by decide +kernel
    obtain ⟨i,hi,e⟩ := List.getElem_of_mem ht
    have H := tab ⟨i,hi⟩
    change testRow pairs[i].1 ≠ testRow pairs[i].2 ∧ ap (testRow pairs[i].1 &&& testRow pairs[i].2) = false at H
    rw [e] at H; intro hb
    have h := hg _ (hb a (by simp)) _ (hb b (by simp)) H.1
    simp_all
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hh; exact hull_bad hg hne r hr

private def supports : List (List XI) := [
  [10, 11, 24, 25, 31, 32, 37, 38],
  [20, 21, 36, 37, 45, 46, 50, 51],
  [30, 31, 49, 50, 59, 60, 66, 67],
  [10, 11, 24, 25, 30, 32, 37, 38, 49, 50, 59, 60, 66, 67],
  [44, 45, 65, 66, 74, 75, 79, 80],
  [20, 21, 36, 37, 44, 46, 50, 51, 65, 66, 74, 75, 79, 80],
  [58, 59, 78, 79, 88, 89, 93, 94],
  [30, 31, 49, 50, 58, 60, 66, 67, 78, 79, 88, 89, 93, 94],
  [10, 11, 24, 25, 30, 32, 37, 38, 49, 50, 58, 60, 66, 67, 78, 79, 88, 89, 93, 94],
  [73, 74, 92, 93, 103, 104, 107, 108],
  [44, 45, 65, 66, 73, 75, 79, 80, 92, 93, 103, 104, 107, 108],
  [20, 21, 36, 37, 44, 46, 50, 51, 65, 66, 73, 75, 79, 80, 92, 93, 103, 104, 107, 108],
  [7, 8, 37, 38, 41, 42, 51, 52],
  [7, 8, 10, 11, 24, 25, 31, 32, 41, 42, 51, 52],
  [7, 8, 20, 21, 36, 38, 41, 42, 45, 46, 50, 52],
  [7, 8, 10, 11, 24, 25, 30, 32, 41, 42, 49, 50, 51, 52, 59, 60, 66, 67],
  [17, 18, 50, 51, 55, 56, 67, 68],
  [17, 18, 20, 21, 36, 37, 45, 46, 55, 56, 67, 68],
  [17, 18, 30, 31, 49, 51, 55, 56, 59, 60, 66, 68],
  [10, 11, 17, 18, 24, 25, 30, 32, 37, 38, 49, 51, 55, 56, 59, 60, 66, 68],
  [17, 18, 20, 21, 36, 37, 44, 46, 55, 56, 65, 66, 67, 68, 74, 75, 79, 80],
  [27, 28, 66, 67, 70, 71, 80, 81],
  [27, 28, 30, 31, 49, 50, 59, 60, 70, 71, 80, 81],
  [27, 28, 44, 45, 65, 67, 70, 71, 74, 75, 79, 81],
  [20, 21, 27, 28, 36, 37, 44, 46, 50, 51, 65, 67, 70, 71, 74, 75, 79, 81],
  [27, 28, 30, 31, 49, 50, 58, 60, 70, 71, 78, 79, 80, 81, 88, 89, 93, 94],
  [40, 41, 79, 80, 85, 86, 94, 95],
  [40, 41, 44, 45, 65, 66, 74, 75, 85, 86, 94, 95],
  [40, 41, 58, 59, 78, 80, 85, 86, 88, 89, 93, 95],
  [30, 31, 40, 41, 49, 50, 58, 60, 66, 67, 78, 80, 85, 86, 88, 89, 93, 95],
  [40, 41, 44, 45, 65, 66, 73, 75, 85, 86, 92, 93, 94, 95, 103, 104, 107, 108],
  [7, 8, 37, 38, 40, 42, 51, 52, 79, 80, 85, 86, 94, 95],
  [54, 55, 93, 94, 100, 101, 108, 109],
  [54, 55, 58, 59, 78, 79, 88, 89, 100, 101, 108, 109],
  [54, 55, 73, 74, 92, 94, 100, 101, 103, 104, 107, 109],
  [44, 45, 54, 55, 65, 66, 73, 75, 79, 80, 92, 94, 100, 101, 103, 104, 107, 109],
  [17, 18, 50, 51, 54, 56, 67, 68, 93, 94, 100, 101, 108, 109],
  [60, 61, 82, 83, 90, 91, 97, 98],
  [30, 31, 49, 50, 59, 61, 66, 67, 82, 83, 90, 91, 97, 98],
  [10, 11, 24, 25, 30, 32, 37, 38, 49, 50, 59, 61, 66, 67, 82, 83, 90, 91, 97, 98],
  [30, 31, 49, 50, 58, 61, 66, 67, 78, 79, 82, 83, 88, 89, 90, 91, 93, 94, 97, 98],
  [10, 11, 24, 25, 30, 32, 37, 38, 49, 50, 58, 61, 66, 67, 78, 79, 82, 83, 88, 89, 90, 91, 93, 94, 97, 98],
  [7, 8, 10, 11, 24, 25, 30, 32, 41, 42, 49, 50, 51, 52, 59, 61, 66, 67, 82, 83, 90, 91, 97, 98],
  [17, 18, 30, 31, 49, 51, 55, 56, 59, 61, 66, 68, 82, 83, 90, 91, 97, 98],
  [10, 11, 17, 18, 24, 25, 30, 32, 37, 38, 49, 51, 55, 56, 59, 61, 66, 68, 82, 83, 90, 91, 97, 98],
  [27, 28, 30, 31, 49, 50, 59, 61, 70, 71, 80, 81, 82, 83, 90, 91, 97, 98],
  [27, 28, 30, 31, 49, 50, 58, 61, 70, 71, 78, 79, 80, 81, 82, 83, 88, 89, 90, 91, 93, 94, 97, 98],
  [30, 31, 40, 41, 49, 50, 58, 61, 66, 67, 78, 80, 82, 83, 85, 86, 88, 89, 90, 91, 93, 95, 97, 98],
  [75, 76, 96, 97, 105, 106, 110, 111],
  [44, 45, 65, 66, 74, 76, 79, 80, 96, 97, 105, 106, 110, 111],
  [20, 21, 36, 37, 44, 46, 50, 51, 65, 66, 74, 76, 79, 80, 96, 97, 105, 106, 110, 111],
  [44, 45, 65, 66, 73, 76, 79, 80, 92, 93, 96, 97, 103, 104, 105, 106, 107, 108, 110, 111],
  [20, 21, 36, 37, 44, 46, 50, 51, 65, 66, 73, 76, 79, 80, 92, 93, 96, 97, 103, 104, 105, 106, 107, 108, 110, 111],
  [17, 18, 20, 21, 36, 37, 44, 46, 55, 56, 65, 66, 67, 68, 74, 76, 79, 80, 96, 97, 105, 106, 110, 111],
  [27, 28, 44, 45, 65, 67, 70, 71, 74, 76, 79, 81, 96, 97, 105, 106, 110, 111],
  [20, 21, 27, 28, 36, 37, 44, 46, 50, 51, 65, 67, 70, 71, 74, 76, 79, 81, 96, 97, 105, 106, 110, 111],
  [40, 41, 44, 45, 65, 66, 74, 76, 85, 86, 94, 95, 96, 97, 105, 106, 110, 111],
  [40, 41, 44, 45, 65, 66, 73, 76, 85, 86, 92, 93, 94, 95, 96, 97, 103, 104, 105, 106, 107, 108, 110, 111],
  [44, 45, 54, 55, 65, 66, 73, 76, 79, 80, 92, 94, 96, 97, 100, 101, 103, 104, 105, 106, 107, 109, 110, 111]]
private theorem supports_spec : supports.map (fun x => x.map testRow) = kernelSupports := by decide +kernel
private def all21 := 2^(2^21)-1
private def blockPlane (g : List XI) := g.foldr (fun j w => samplePlane (names j) &&& w) all21
private def covered := (blocks ++ supports).foldr (fun g w => blockPlane g ||| w) 0
private theorem cover_all : covered = all21 ^^^ 1 := by decide +kernel

private theorem block_bit (g : List XI) {a : ℕ} (ha : a < 2^21) :
    (blockPlane g).testBit a = g.all (fun j => (samplePlane (names j)).testBit a) := by
  induction g with
  | nil => change (2^(2^21)-1 : Nat).testBit a = true; rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true ha
  | cons x xs ih => change (_ &&& blockPlane xs).testBit a = _; simp [Nat.testBit_and,ih]

private theorem find_bad {a : ℕ} (ha : a < 2^21) (hn : a ≠ 0) :
    ∃ g ∈ blocks ++ supports, ∀ j ∈ g, (samplePlane (names j)).testBit a = true := by
  have cert := congrArg (fun w : Nat => w.testBit a) cover_all
  have H (xs : List (List XI)) : (xs.foldr (fun g (w : Nat) => blockPlane g ||| w) 0).testBit a =
      xs.any (fun g => (blockPlane g).testBit a) := by
    induction xs with
    | nil => simp
    | cons g gs ih => simp [Nat.testBit_or,ih]
  simp only [covered,H,Nat.testBit_xor,all21,Nat.testBit_two_pow_sub_one,decide_eq_true ha] at cert
  have b1 : (1 : Nat).testBit a = false := by change (2^0 : Nat).testBit a = false; rw [Nat.testBit_two_pow]; simp [Ne.symm hn]
  rw [b1] at cert
  obtain ⟨g,hg,hh⟩ := List.any_eq_true.mp cert
  exact ⟨g,hg,List.all_eq_true.mp (by simpa [block_bit g ha] using hh)⟩

/-- A nonzero parity relation in a valid nonstar forces one of the certified AP supports. -/
theorem binary_zero_of_avoids {F : Finset Mask} (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false)
    (avoid : ¬ ∃ s ∈ kernelSupports, ∀ t ∈ s, t ∈ F)
    (b : Fin 31 → ZMod 2) (hz : eqMatrix *ᵥ b = 0)
    (hF : ∀ j : XI, (testMatrix *ᵥ b) j ≠ 0 → testRow j ∈ F) : b = 0 := by
  obtain ⟨v,hv⟩ := parametrize b hz
  let f := fun i : Fin 21 => (v i).val == 1
  obtain ⟨a,ha,he⟩ := exists_bits 21 f
  have hbit (i : Fin 21) : bitVal (a.testBit i) = v i := by
    rw [he]; change bitVal ((v i).val == 1) = v i
    have H : ∀ x : Fin 2, bitVal (x.val == 1) = x := by intro x; fin_cases x <;> rfl
    exact H (v i)
  by_cases e : a = 0
  · have h0 : v = 0 := by funext i; simpa [e,bitVal] using (hbit i).symm
    simp [hv,h0]
  · obtain ⟨g,hm,hh⟩ := find_bad ha e
    have inc : ∀ j ∈ g, testRow j ∈ F := by
      intro j hj; apply hF; rw [← row_value j v b hv a ha hbit,hh j hj]; decide
    rcases List.mem_append.mp hm with hp | hs
    · exact False.elim (impossible hg hne g hp inc)
    · apply False.elim (avoid ?_)
      refine ⟨g.map testRow, ?_, ?_⟩
      · rw [← supports_spec]; exact List.mem_map.mpr ⟨g, hs, rfl⟩
      · intro t ht; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht; exact inc j hj

end E272.Neutral.SupportProof
