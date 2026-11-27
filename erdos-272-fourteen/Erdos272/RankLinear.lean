import Erdos272.RankGram

namespace E272
namespace RankProof
open Finset
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

def wMasks : Fin 18 → Fin 8 → Mask := ![
  ![31, 5, 14, 20, 4, 15, 21, 30],
  ![62, 10, 28, 40, 8, 30, 42, 60],
  ![124, 20, 56, 80, 16, 60, 84, 120],
  ![248, 40, 112, 160, 32, 120, 168, 240],
  ![341, 17, 84, 272, 16, 85, 273, 340],
  ![496, 80, 224, 320, 64, 240, 336, 480],
  ![682, 34, 168, 544, 32, 170, 546, 680],
  ![992, 160, 448, 640, 128, 480, 672, 960],
  ![1364, 68, 336, 1088, 64, 340, 1092, 1360],
  ![1984, 320, 896, 1280, 256, 960, 1344, 1920],
  ![2728, 136, 672, 2176, 128, 680, 2184, 2720],
  ![3968, 640, 1792, 2560, 512, 1920, 2688, 3840],
  ![4681, 65, 584, 4160, 64, 585, 4161, 4680],
  ![5456, 272, 1344, 4352, 256, 1360, 4368, 5440],
  ![7936, 1280, 3584, 5120, 1024, 3840, 5376, 7680],
  ![9362, 130, 1168, 8320, 128, 1170, 8322, 9360],
  ![10912, 544, 2688, 8704, 512, 2720, 8736, 10880],
  ![15872, 2560, 7168, 10240, 2048, 7680, 10752, 15360]]
def sgn (j : Fin 8) : ℚ := if j.val < 4 then 1 else -1
def w (p : Fin 18) (a : Mask) : ℚ := ∑ j, if wMasks p j = a then sgn j else 0
def five (p : Fin 18) := wMasks p 0
def proj (z : Fin 18 → ℚ) (a : Mask) := ∑ p, z p * w p a

theorem collapse {J : Type*} [Fintype J] (p : J → Mask) (s : J → ℚ) (f : Mask → ℚ) :
    (∑ a : Mask, (∑ j, if p j = a then s j else 0) * f a) = ∑ j, s j * f (p j) := by
  classical
  simp only [Finset.sum_mul, ite_mul, zero_mul]; rw [Finset.sum_comm]; simp

theorem w_gram (p : Fin 18) (t : Mask) :
    (∑ a : Mask, w p a * inc t a) = ∑ j, sgn j * inc t (wMasks p j) := collapse _ _ _
theorem w_ann (p : Fin 18) (t : Mask) (ht : t ∈ pos ∨ t ∈ neg) :
    (∑ a : Mask, w p a * inc t a) = 0 := by
  rw [w_gram]
  -- The checks use only the eight summands of each sparse row.
  have hu : ∀ (p : Fin 18), ∀ i : Fin pos.length, ∑ j, sgn j * inc pos[i] (wMasks p j) = 0 := by decide +kernel
  have hv : ∀ (p : Fin 18), ∀ i : Fin neg.length, ∑ j, sgn j * inc neg[i] (wMasks p j) = 0 := by decide +kernel
  obtain h | h := ht
  · obtain ⟨k,hk,e⟩ := List.getElem_of_mem h; simpa [e] using hu p ⟨k,hk⟩
  · obtain ⟨k,hk,e⟩ := List.getElem_of_mem h; simpa [e] using hv p ⟨k,hk⟩

theorem proj_ann (z : Fin 18 → ℚ) (t : Mask) (ht : t ∈ pos ∨ t ∈ neg) :
    (∑ a : Mask, proj z a * inc t a) = 0 := by
  simp only [proj, Finset.sum_mul, mul_assoc]; rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, w_ann _ _ ht]; simp

theorem zeta_unique (c : Mask → ℚ)
    (h : ∀ t, c t ≠ 0 → ∑ a : Mask, c a * inc t a = 0) : ∀ a, c a = 0 := by
  classical
  by_contra! hn
  let s := Finset.univ.filter (fun a => c a ≠ 0)
  obtain ⟨t,ht,hm⟩ := Finset.exists_max_image s BitVec.toNat (by obtain ⟨a,ha⟩ := hn; exact ⟨a, by simp [s,ha]⟩)
  have hct : c t ≠ 0 := (Finset.mem_filter.mp ht).2
  have he : (∑ a : Mask, c a * inc t a) = c t := by
    rw [Finset.sum_eq_single t]
    · simp [inc, sub]
    · intro b _ hb
      by_cases hc : c b = 0
      · simp [hc]
      · have hle := hm b (by simp [s,hc])
        have hnsub : sub t b = false := by
          simp only [sub, beq_eq_false_iff_ne]
          intro eq
          have hle' : t.toNat ≤ b.toNat := by rw [← eq]; exact Nat.and_le_right
          exact hb (BitVec.toNat_inj.mp (by omega))
        simp [inc,hnsub]
    · simp
  exact hct (he.symm.trans (h t hct))

theorem covered {a : Mask} (ha : ap a = true) (hs : short a = true) :
    a ∈ pos ∨ a ∈ neg ∨ ∃ p, a = five p := by
  have tbl : ∀ i : Fin apMasks.length, short apMasks[i] = true →
      apMasks[i] ∈ pos ∨ apMasks[i] ∈ neg ∨ ∃ p, apMasks[i] = five p := by decide +kernel
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem (List.contains_iff_mem.mp ha : a ∈ apMasks)
  exact tbl ⟨j,hj⟩ hs

theorem proj_five (z : Fin 18 → ℚ) (p : Fin 18) : proj z (five p) = z p := by
  have ht : ∀ p i, w i (five p) = if i = p then 1 else 0 := by decide +kernel
  simp [proj, ht, mul_ite]

theorem resolve (c : Mask → ℚ)
    (hcov : ∀ a, c a ≠ 0 → ap a = true ∧ short a = true)
    (hann : ∀ t, (t ∈ pos ∨ t ∈ neg) → ∑ a, c a * inc t a = 0) :
    ∀ a, c a = proj (fun p => c (five p)) a := by
  let z := fun p => c (five p)
  suffices H : ∀ a, c a - proj z a = 0 by simpa [sub_eq_zero, z] using H
  apply zeta_unique
  intro t ht
  suffices hj : t ∈ pos ∨ t ∈ neg by
    simp only [sub_mul, Finset.sum_sub_distrib, hann t hj, proj_ann z t hj, sub_self]
  by_contra h
  have hnf : ∀ p, t ≠ five p := by
    intro p e; apply ht; subst t; simp [proj_five,z]
  have hc : c t = 0 := by
    by_contra hct
    obtain ⟨hap,hs⟩ := hcov t hct
    rcases covered hap hs with hp | hn | ⟨p, he⟩
    · exact h (Or.inl hp)
    · exact h (Or.inr hn)
    · exact hnf p he
  have tbl : ∀ p j, wMasks p j ∈ pos ∨ wMasks p j ∈ neg ∨ wMasks p j = five p := by decide +kernel
  have no : ∀ p j, wMasks p j ≠ t := by
    intro p j e; rcases tbl p j with hp | hn | hf
    · exact h (Or.inl (e ▸ hp))
    · exact h (Or.inr (e ▸ hn))
    · exact hnf p (e ▸ hf)
  exact ht (by simp [hc,proj,w,no])


end RankProof
end E272
