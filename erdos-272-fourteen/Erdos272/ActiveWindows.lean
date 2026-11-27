import Erdos272.FullRank

namespace E272
open Finset RankProof
set_option exponentiation.threshold 32768
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

/-- The two parity progressions cannot both be represented in a family realizing
    all eight contiguous seven-term windows, unless a member contains the interval [2,12]. -/
theorem some_seven_absent {F : Finset Mask}
    (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true) (hw : ∀ a ∈ F, sub 4094 a = false) :
    ∃ t ∈ sevens, ∀ a ∈ F, sub t a = false := by
  by_contra! all
  have supply (t : Mask) (ht : t ∈ sevens) : ∃ a ∈ F, sub t a = true := by simpa using all t ht
  have trace (i : Fin sevens.length) {b : Mask} (hb : b ∈ F) :
      sevens[i] &&& b = 0 ∨ ap (sevens[i] &&& b) = true := by
    obtain ⟨a,ha,hta⟩ := supply _ (List.getElem_mem ..)
    exact active_posLong_trace hg (List.mem_append_left _ (List.getElem_mem ..)) ha hta hb
  let pool : List Mask := [5461, 5463, 5469, 5471, 5493, 5495, 5501, 5503, 5589, 5591, 5597, 5599, 5621, 5623, 5629, 5631, 5973, 5975, 5981, 5983, 6005, 6007, 6013, 6015, 6101, 6103, 6109, 6111, 6133, 6135, 6141, 6143, 7509, 7511, 7517, 7519, 7541, 7543, 7549, 7551, 7637, 7639, 7645, 7647, 7669, 7671, 7677, 7679, 8021, 8023, 8029, 8031, 8053, 8055, 8061, 8063, 8149, 8151, 8157, 8159, 8181, 8183, 8189, 8191, 10922, 10923, 10926, 10927, 10938, 10939, 10942, 10943, 10986, 10987, 10990, 10991, 11002, 11003, 11006, 11007, 11178, 11179, 11182, 11183, 11194, 11195, 11198, 11199, 11242, 11243, 11246, 11247, 11258, 11259, 11262, 11263, 11946, 11947, 11950, 11951, 11962, 11963, 11966, 11967, 12010, 12011, 12014, 12015, 12026, 12027, 12030, 12031, 12202, 12203, 12206, 12207, 12218, 12219, 12222, 12223, 12266, 12267, 12270, 12271, 12282, 12283, 12286, 12287, 13653, 13655, 13661, 13663, 13685, 13687, 13693, 13695, 13781, 13783, 13789, 13791, 13813, 13815, 13821, 13823, 14165, 14167, 14173, 14175, 14197, 14199, 14205, 14207, 14293, 14295, 14301, 14303, 14325, 14327, 14333, 14335, 15018, 15019, 15022, 15023, 15034, 15035, 15038, 15039, 15082, 15083, 15086, 15087, 15098, 15099, 15102, 15103, 15274, 15275, 15278, 15279, 15290, 15291, 15294, 15295, 15338, 15339, 15342, 15343, 15354, 15355, 15358, 15359, 15701, 15703, 15709, 15711, 15733, 15735, 15741, 15743, 15829, 15831, 15837, 15839, 15861, 15863, 15869, 15871, 16042, 16043, 16046, 16047, 16058, 16059, 16062, 16063, 16106, 16107, 16110, 16111, 16122, 16123, 16126, 16127, 16213, 16215, 16221, 16223, 16245, 16247, 16253, 16255, 16298, 16299, 16302, 16303, 16314, 16315, 16318, 16319, 16341, 16343, 16349, 16351, 16362, 16363, 16366, 16367, 16373, 16375, 16378, 16379, 16381, 16382, 16383]
  have mark : unionTable (fun t => 2^t.toNat) pool = supers 14 5461 ||| supers 14 10922 := by
    decide +kernel
  have classify : ∀ (i : Fin pool.length) (j : Fin 2), let t : Mask := [5461,10922][j.val]'(j.isLt)
      let v := pool[i]
      sub t v = true → sub 4094 v = false →
      (∀ k : Fin sevens.length, sevens[k] &&& v = 0 ∨ ap (sevens[k] &&& v) = true) → v = t := by
    decide +kernel
  have hpair (j : Fin 2) : [5461,10922][j.val]'(j.isLt) ∈ F := by
    let t : Mask := [5461,10922][j.val]'(j.isLt)
    have ht : t ∈ sevens := by fin_cases j <;> decide
    obtain ⟨a,ha,hs⟩ := supply _ ht
    have hmark := congrArg (fun n : Nat => n.testBit a.toNat) mark
    change _ = (supers 14 (5461 : Mask).toNat ||| supers 14 (10922 : Mask).toNat).testBit _ at hmark
    rw [unionTable_bit,Nat.testBit_or,supers_bit,supers_bit] at hmark
    have hl : a ∈ pool := by
      have hh : (sub 5461 a || sub 10922 a) = true := by fin_cases j <;> simp_all [t]
      rw [hh] at hmark
      simpa [Nat.testBit_two_pow,BitVec.toNat_inj] using hmark
    obtain ⟨k,hk,he⟩ := List.getElem_of_mem hl
    have H := classify ⟨k,hk⟩ j
    change sub t pool[k] = true → sub 4094 pool[k] = false → (∀ i : Fin sevens.length, sevens[i] &&& pool[k] = 0 ∨ ap (sevens[i] &&& pool[k]) = true) → pool[k] = t at H
    rw [he] at H
    specialize H hs (hw a ha) (fun i => trace i ha)
    change a = t at H; change t ∈ F; rwa [← H]
  have no : ap ((5461 : Mask) &&& 10922) = false := by decide
  have h := hg 5461 (hpair 0) 10922 (hpair 1) (by decide)
  simp_all

theorem no_anchor_bound_101 (F : Finset Mask)
    (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false)
    (hz : ∀ a ∈ F, a ∉ zeroLong)
    (he : ∀ p ∈ elevens, ∀ a ∈ F, sub p a = false) : F.card ≤ 101 := by
  obtain ⟨t,ht,habs⟩ := some_seven_absent hg (he 4094 (by decide))
  have hlen : (sevens.erase t).length = 9 := by
    rw [List.length_erase_of_mem ht]; decide
  have H := mobius_rank_bound (F := F) (S := F) (by rfl) hg hne hz (sevens.erase t) (by
    intro p hp a ha hsub
    rcases List.mem_append.mp hp with h | h
    · have hne : p ≠ t := by rintro rfl; simp [habs a ha] at hsub
      rwa [List.mem_erase_of_ne hne]
    · simp_all)
  simpa [hlen] using H

end E272
