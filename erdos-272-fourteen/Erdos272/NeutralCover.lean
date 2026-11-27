import Erdos272.NeutralParam

namespace E272.Neutral
open Finset RankProof
open scoped Matrix
set_option maxRecDepth 20000
set_option maxHeartbeats 15000000
set_option exponentiation.threshold 262144

private def pairs : List (XI × XI) := [(0,2), (11,12), (4,13), (5,14), (27,57), (6,20), (9,17), (22,30), (35,48), (25,60), (67,76), (11,50), (8,16), (33,49), (31,43), (47,59), (24,61), (23,42), (11,58), (34,46), (32,44), (22,43), (29,46), (5,20), (66,75), (22,31), (25,35), (6,34), (13,29), (14,22), (13,47), (4,58), (20,61), (18,30), (9,50), (14,46), (17,49), (4,22), (22,33), (29,43), (48,58), (6,59), (0,69), (5,60), (22,58), (4,20), (8,22), (35,47), (2,30), (4,42), (9,12), (9,22), (9,42), (14,29)]
private def hulls : List ((Fin 14) × XI × List XI) := [(4,28,[1, 8, 21]), (6,39,[10, 27, 30]), (6,48,[5, 24, 40]), (6,49,[5, 24, 40]), (8,51,[23, 36, 45]), (6,53,[5, 38, 40]), (6,53,[9, 31, 46]), (7,54,[15, 35, 42]), (7,54,[16, 26, 33]), (7,54,[16, 37, 42]), (7,60,[13, 34, 55]), (7,62,[13, 52, 55]), (5,63,[3, 29, 56]), (6,70,[8, 30, 64]), (6,70,[8, 40, 66]), (6,71,[8, 31, 67]), (7,71,[18, 37, 42]), (7,71,[18, 43, 55]), (7,71,[18, 43, 58]), (6,72,[7, 30, 68]), (6,72,[7, 41, 65]), (6,72,[8, 19, 64]), (6,72,[10, 23, 40]), (6,72,[10, 31, 67]), (7,77,[16, 33, 55]), (7,78,[16, 42, 76]), (7,79,[18, 43, 55]), (7,79,[18, 43, 73]), (7,79,[18, 43, 76]), (9,79,[35, 57, 74])]
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

private def all17 := 2^(2^17)-1
private def blockPlane (g : List XI) := g.foldr (fun j w => evalPlane (names j) &&& w) all17
private def covered := blocks.foldr (fun g w => blockPlane g ||| w) 0
private theorem cover_all : covered = all17 ^^^ 1 := by decide +kernel

private theorem block_bit (g : List XI) {a : ℕ} (ha : a < 2^17) :
    (blockPlane g).testBit a = g.all (fun j => (evalPlane (names j)).testBit a) := by
  induction g with
  | nil => change (2^(2^17)-1 : Nat).testBit a = true; rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true ha
  | cons x xs ih => change (_ &&& blockPlane xs).testBit a = _; simp [Nat.testBit_and,ih]

private theorem find_bad {a : ℕ} (ha : a < 2^17) (hn : a ≠ 0) :
    ∃ g ∈ blocks, ∀ j ∈ g, (evalPlane (names j)).testBit a = true := by
  have cert := congrArg (fun w : Nat => w.testBit a) cover_all
  have H (xs : List (List XI)) : (xs.foldr (fun g (w : Nat) => blockPlane g ||| w) 0).testBit a =
      xs.any (fun g => (blockPlane g).testBit a) := by
    induction xs with
    | nil => simp
    | cons g gs ih => simp [Nat.testBit_or,ih]
  simp only [covered,H,Nat.testBit_xor,all17,Nat.testBit_two_pow_sub_one,decide_eq_true ha] at cert
  have b1 : (1 : Nat).testBit a = false := by change (2^0 : Nat).testBit a = false; rw [Nat.testBit_two_pow]; simp [Ne.symm hn]
  rw [b1] at cert
  obtain ⟨g,hg,hh⟩ := List.any_eq_true.mp cert
  exact ⟨g,hg,List.all_eq_true.mp (by simpa [block_bit g ha] using hh)⟩

/-- Four checks plus the singleton constraints kill every nonzero parity relation
    with all odd AP coefficients present in one valid nonstar. -/
theorem binary_zero {F : Finset Mask} (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false)
    (b : Fin 31 → ZMod 2) (hz : eqMatrix *ᵥ b = 0)
    (hF : ∀ j : XI, (testMatrix *ᵥ b) j ≠ 0 → testRow j ∈ F) : b = 0 := by
  obtain ⟨v,hv⟩ := parametrize b hz
  let f := fun i : Fin 17 => (v i).val == 1
  obtain ⟨a,ha,he⟩ := exists_bits 17 f
  have hbit (i : Fin 17) : bitVal (a.testBit i) = v i := by
    rw [he]; change bitVal ((v i).val == 1) = v i
    have H : ∀ x : Fin 2, bitVal (x.val == 1) = x := by intro x; fin_cases x <;> rfl
    exact H (v i)
  by_cases e : a = 0
  · have h0 : v = 0 := by funext i; simpa [e,bitVal] using (hbit i).symm
    simp [hv,h0]
  · obtain ⟨g,hm,hh⟩ := find_bad ha e
    apply False.elim (impossible hg hne g hm ?_)
    intro j hj; apply hF; rw [← row_value j v b hv a ha hbit,hh j hj]; decide

end E272.Neutral
