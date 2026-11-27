import Erdos272.FullRank

namespace E272.Neutral
open Finset RankProof
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000

/-- Zero Möbius weights (lengths 5, 9, 10, 13), in length-and-mask order. -/
def neutral : Fin 31 → Mask := ![31, 62, 124, 248, 341, 496, 682, 992, 1364, 1984, 2728, 3968, 4681, 5456, 7936, 9362, 10912, 15872, 511, 1022, 2044, 4088, 8176, 16352, 1023, 2046, 4092, 8184, 16368, 8191, 16382]
/-- Columns of the inverse inclusion matrix, padded by terms of coefficient zero. -/
def terms : Fin 31 → Fin 16 → Mask := ![![4, 5, 14, 15, 20, 21, 30, 31, 1, 1, 1, 1, 1, 1, 1, 1], ![8, 10, 28, 30, 40, 42, 60, 62, 1, 1, 1, 1, 1, 1, 1, 1], ![16, 20, 56, 60, 80, 84, 120, 124, 1, 1, 1, 1, 1, 1, 1, 1], ![32, 40, 112, 120, 160, 168, 240, 248, 1, 1, 1, 1, 1, 1, 1, 1], ![16, 17, 84, 85, 272, 273, 340, 341, 1, 1, 1, 1, 1, 1, 1, 1], ![64, 80, 224, 240, 320, 336, 480, 496, 1, 1, 1, 1, 1, 1, 1, 1], ![32, 34, 168, 170, 544, 546, 680, 682, 1, 1, 1, 1, 1, 1, 1, 1], ![128, 160, 448, 480, 640, 672, 960, 992, 1, 1, 1, 1, 1, 1, 1, 1], ![64, 68, 336, 340, 1088, 1092, 1360, 1364, 1, 1, 1, 1, 1, 1, 1, 1], ![256, 320, 896, 960, 1280, 1344, 1920, 1984, 1, 1, 1, 1, 1, 1, 1, 1], ![128, 136, 672, 680, 2176, 2184, 2720, 2728, 1, 1, 1, 1, 1, 1, 1, 1], ![512, 640, 1792, 1920, 2560, 2688, 3840, 3968, 1, 1, 1, 1, 1, 1, 1, 1], ![64, 65, 584, 585, 4160, 4161, 4680, 4681, 1, 1, 1, 1, 1, 1, 1, 1], ![256, 272, 1344, 1360, 4352, 4368, 5440, 5456, 1, 1, 1, 1, 1, 1, 1, 1], ![1024, 1280, 3584, 3840, 5120, 5376, 7680, 7936, 1, 1, 1, 1, 1, 1, 1, 1], ![128, 130, 1168, 1170, 8320, 8322, 9360, 9362, 1, 1, 1, 1, 1, 1, 1, 1], ![512, 544, 2688, 2720, 8704, 8736, 10880, 10912, 1, 1, 1, 1, 1, 1, 1, 1], ![2048, 2560, 7168, 7680, 10240, 10752, 15360, 15872, 1, 1, 1, 1, 1, 1, 1, 1], ![84, 85, 254, 255, 340, 341, 510, 511, 1, 1, 1, 1, 1, 1, 1, 1], ![168, 170, 508, 510, 680, 682, 1020, 1022, 1, 1, 1, 1, 1, 1, 1, 1], ![336, 340, 1016, 1020, 1360, 1364, 2040, 2044, 1, 1, 1, 1, 1, 1, 1, 1], ![672, 680, 2032, 2040, 2720, 2728, 4080, 4088, 1, 1, 1, 1, 1, 1, 1, 1], ![1344, 1360, 4064, 4080, 5440, 5456, 8160, 8176, 1, 1, 1, 1, 1, 1, 1, 1], ![2688, 2720, 8128, 8160, 10880, 10912, 16320, 16352, 1, 1, 1, 1, 1, 1, 1, 1], ![72, 73, 510, 511, 584, 585, 1022, 1023, 1, 1, 1, 1, 1, 1, 1, 1], ![144, 146, 1020, 1022, 1168, 1170, 2044, 2046, 1, 1, 1, 1, 1, 1, 1, 1], ![288, 292, 2040, 2044, 2336, 2340, 4088, 4092, 1, 1, 1, 1, 1, 1, 1, 1], ![576, 584, 4080, 4088, 4672, 4680, 8176, 8184, 1, 1, 1, 1, 1, 1, 1, 1], ![1152, 1168, 8160, 8176, 9344, 9360, 16352, 16368, 1, 1, 1, 1, 1, 1, 1, 1], ![64, 65, 584, 585, 1364, 1365, 4094, 4095, 4160, 4161, 4680, 4681, 5460, 5461, 8190, 8191], ![128, 130, 1168, 1170, 2728, 2730, 8188, 8190, 8320, 8322, 9360, 9362, 10920, 10922, 16380, 16382]]
def weights : Fin 31 → Fin 16 → Int := ![![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1], ![1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1]]
def coeff (i : Fin 31) (a : Mask) : Int := ∑ j, if terms i j = a then weights i j else 0
def rowQ (i : Fin 31) (a : Mask) : ℚ := (coeff i a : ℚ)
def eval (z : Fin 31 → ℚ) (a : Mask) := ∑ i, z i * rowQ i a

private theorem row_sum (i : Fin 31) (t : Mask) :
    (∑ a : Mask, rowQ i a * inc t a) = (∑ j, (weights i j : ℚ) * inc t (terms i j)) := by
  simp only [rowQ,coeff,Int.cast_sum,Int.cast_ite,Int.cast_zero]
  exact collapse (terms i) (fun j => (weights i j : ℚ)) _

private theorem gram_table (i : Fin 31) (t : Mask) (ht : t = 0 ∨ ap t = true) :
    ∑ a : Mask, rowQ i a * inc t a = if neutral i = t then 1 else 0 := by
  rw [row_sum]
  have hh : ∀ i : Fin 31, ∀ k : Fin (0 :: apMasks).length,
      (∑ j, if sub ((0 :: apMasks)[k]) (terms i j) then weights i j else 0) =
      if neutral i = (0 :: apMasks)[k] then 1 else 0 := by decide +kernel
  have hm : t ∈ (0 :: apMasks) := by
    rcases ht with rfl | h <;> simp_all [ap,List.contains_iff_mem]
  obtain ⟨k,hk,rfl⟩ := List.getElem_of_mem hm
  have H := congrArg (fun z : Int => (z : ℚ)) (hh i ⟨k,hk⟩)
  simpa [inc,mul_ite] using H

private theorem maybe_covered {t : Mask} (ht : ap t = true) :
    t ∈ fullPos ∨ t ∈ fullNeg ∨ ∃ i, neutral i = t := by
  have h : ∀ j : Fin apMasks.length, apMasks[j] ∈ fullPos ∨ apMasks[j] ∈ fullNeg ∨
      ∃ i, neutral i = apMasks[j] := by decide +kernel
  obtain ⟨k,hk,rfl⟩ := List.getElem_of_mem (List.contains_iff_mem.mp ht : t ∈ apMasks)
  exact h ⟨k,hk⟩

/-- The 31 inverse columns span the joint incidence kernel on AP rows. -/
theorem reconstruct (c : Mask → ℚ) (hap : ∀ a, c a ≠ 0 → ap a = true)
    (hann : ∀ t, (t ∈ fullPos ∨ t ∈ fullNeg) → ∑ a, c a * inc t a = 0) :
    let z := fun i => ∑ a, c a * inc (neutral i) a
    ∀ a, c a = eval z a := by
  dsimp only
  let z := fun i => ∑ a, c a * inc (neutral i) a
  suffices ∀ a, c a - eval z a = 0 by simpa [sub_eq_zero,z] using this
  apply zeta_unique; intro t ht
  have htA : ap t = true := by
    by_contra hna
    have hc : c t = 0 := by by_contra h; exact hna (hap t h)
    have tr : ∀ i j, ap (terms i j) = true := by decide +kernel
    have tt : ∀ i j, terms i j ≠ t := fun i j e => hna (e ▸ tr i j)
    exact ht (by simp [hc,eval,rowQ,coeff,tt])
  have he (i : Fin 31) := gram_table i t (Or.inr htA)
  have idn : ∀ i j, (neutral i = neutral j) ↔ i = j := by decide +kernel
  have hn (t : Mask) (ht : t ∈ fullPos ∨ t ∈ fullNeg) : ∀ i, neutral i ≠ t := by
    have H : ∀ i, neutral i ∉ fullPos ∧ neutral i ∉ fullNeg := by decide +kernel
    intro i e; rcases e ▸ ht with h | h
    · exact (H i).1 h
    · exact (H i).2 h
  have mom : (∑ a, eval z a * inc t a) = ∑ i, z i * (if neutral i = t then 1 else 0) := by
    simp only [eval,Finset.sum_mul,mul_assoc]; rw [Finset.sum_comm]; simp_rw [←Finset.mul_sum,he]
  simp only [sub_mul,Finset.sum_sub_distrib,mom]
  rcases maybe_covered htA with h | h | ⟨i,rfl⟩
  · simp [hann t (Or.inl h), hn t (Or.inl h)]
  · simp [hann t (Or.inr h), hn t (Or.inr h)]
  · simp [idn,mul_ite,z]

end E272.Neutral
