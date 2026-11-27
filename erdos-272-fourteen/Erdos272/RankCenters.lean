import Erdos272.RankLinear

namespace E272
namespace RankProof
open Finset
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

private theorem sub_inter_eq {a p b : Mask} (h : sub a p = true) : (b &&& p) &&& a = b &&& a := by
  simp only [sub, beq_iff_eq] at h
  calc
    _ = b &&& (a &&& p) := by ac_rfl
    _ = _ := by rw [h]

private theorem all_compat {F : Finset Mask} (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    {b a : Mask} (hb : b ∈ F) (ha : a ∈ F) (hp : ap a = true) : ap (b &&& a) = true := by
  by_cases h : b = a
  · simpa [h] using hp
  · exact hg b hb a ha h

private theorem forbidden {F : Finset Mask} (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false)
    (x : Fin 14) (p : Mask) (D : List Mask)
    (hap : ap p = true) (hD : D.all (fun a => ap a && sub a p) = true)
    (cert : apMasks.all (fun r => r.getLsbD x || !(D.all (fun a => (r &&& a) != 0))) = true)
    (hp : p ∈ F) (hd : ∀ a ∈ D, a ∈ F) : False := by
  obtain ⟨b,hb,hx⟩ := hne x
  have hr := all_compat hg hb hp hap
  have hmem : b &&& p ∈ apMasks := List.contains_iff_mem.mp hr
  have eqn := List.all_eq_true.mp cert (b &&& p) hmem
  have no : (b &&& p).getLsbD x = false := by rw [BitVec.getLsbD_and, hx]; rfl
  have yes : D.all (fun a => ((b &&& p) &&& a) != 0) = true := by
    apply List.all_eq_true.mpr; intro a ha
    have hh := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hD a ha)
    rw [sub_inter_eq hh.2]
    have h := all_compat hg hb (hd a ha) hh.1
    simp only [bne_iff_ne]; intro e; rw [e] at h
    exact (by decide : ap 0 ≠ true) h
  rw [no,yes] at eqn
  contradiction

private theorem disjoint_kills {F : Finset Mask} (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    {b a : Mask} (hb : b ∈ F) (h : ap (b &&& a) = false) (hh : b ≠ a) : a ∉ F := by
  intro ha; have := hg b hb a ha hh; simp_all

private theorem singleton_kills {F : Finset Mask} (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false) (x : Fin 14) :
    ((1 : Mask) <<< x.val) ∉ F := by
  have cert : ∀ x : Fin 14, apMasks.all (fun r => r.getLsbD x || !([((1 : Mask) <<< x.val)].all (fun a => (r &&& a) != 0))) = true := by decide +kernel
  have hh : ∀ x : Fin 14, ap ((1 : Mask) <<< x.val) = true := by decide +kernel
  intro h
  exact forbidden hg hne x _ [((1 : Mask) <<< x.val)] (hh x) (by simp only [List.all_cons, List.all_nil, Bool.and_true, hh x, sub, BitVec.and_self, beq_self_eq_true]) (cert x) h (by simpa)
private theorem row4 (z : Fin 18 → ℚ) : proj z 4 = -z 0 := by
  have h : ∀ i, w i 4 = (if i = 0 then (-1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row8 (z : Fin 18 → ℚ) : proj z 8 = -z 1 := by
  have h : ∀ i, w i 8 = (if i = 1 then (-1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row16 (z : Fin 18 → ℚ) : proj z 16 = -z 2 + -z 4 := by
  have h : ∀ i, w i 16 = (if i = 2 then (-1 : ℚ) else 0) + (if i = 4 then (-1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]; simp

private theorem row17 (z : Fin 18 → ℚ) : proj z 17 = z 4 := by
  have h : ∀ i, w i 17 = (if i = 4 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row20 (z : Fin 18 → ℚ) : proj z 20 = z 0 + z 2 := by
  have h : ∀ i, w i 20 = (if i = 0 then (1 : ℚ) else 0) + (if i = 2 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]; simp

private theorem row32 (z : Fin 18 → ℚ) : proj z 32 = -z 3 + -z 6 := by
  have h : ∀ i, w i 32 = (if i = 3 then (-1 : ℚ) else 0) + (if i = 6 then (-1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]; simp

private theorem row34 (z : Fin 18 → ℚ) : proj z 34 = z 6 := by
  have h : ∀ i, w i 34 = (if i = 6 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row40 (z : Fin 18 → ℚ) : proj z 40 = z 1 + z 3 := by
  have h : ∀ i, w i 40 = (if i = 1 then (1 : ℚ) else 0) + (if i = 3 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]; simp

private theorem row56 (z : Fin 18 → ℚ) : proj z 56 = z 2 := by
  have h : ∀ i, w i 56 = (if i = 2 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row64 (z : Fin 18 → ℚ) : proj z 64 = -z 5 + -z 8 + -z 12 := by
  have h : ∀ i, w i 64 = (if i = 5 then (-1 : ℚ) else 0) + (if i = 8 then (-1 : ℚ) else 0) + (if i = 12 then (-1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]; simp

private theorem row65 (z : Fin 18 → ℚ) : proj z 65 = z 12 := by
  have h : ∀ i, w i 65 = (if i = 12 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row68 (z : Fin 18 → ℚ) : proj z 68 = z 8 := by
  have h : ∀ i, w i 68 = (if i = 8 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row80 (z : Fin 18 → ℚ) : proj z 80 = z 2 + z 5 := by
  have h : ∀ i, w i 80 = (if i = 2 then (1 : ℚ) else 0) + (if i = 5 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]; simp

private theorem row112 (z : Fin 18 → ℚ) : proj z 112 = z 3 := by
  have h : ∀ i, w i 112 = (if i = 3 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row124 (z : Fin 18 → ℚ) : proj z 124 = z 2 := by
  have h : ∀ i, w i 124 = (if i = 2 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row128 (z : Fin 18 → ℚ) : proj z 128 = -z 7 + -z 10 + -z 15 := by
  have h : ∀ i, w i 128 = (if i = 7 then (-1 : ℚ) else 0) + (if i = 10 then (-1 : ℚ) else 0) + (if i = 15 then (-1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]; simp

private theorem row130 (z : Fin 18 → ℚ) : proj z 130 = z 15 := by
  have h : ∀ i, w i 130 = (if i = 15 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row136 (z : Fin 18 → ℚ) : proj z 136 = z 10 := by
  have h : ∀ i, w i 136 = (if i = 10 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row160 (z : Fin 18 → ℚ) : proj z 160 = z 3 + z 7 := by
  have h : ∀ i, w i 160 = (if i = 3 then (1 : ℚ) else 0) + (if i = 7 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]; simp

private theorem row224 (z : Fin 18 → ℚ) : proj z 224 = z 5 := by
  have h : ∀ i, w i 224 = (if i = 5 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row248 (z : Fin 18 → ℚ) : proj z 248 = z 3 := by
  have h : ∀ i, w i 248 = (if i = 3 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row256 (z : Fin 18 → ℚ) : proj z 256 = -z 9 + -z 13 := by
  have h : ∀ i, w i 256 = (if i = 9 then (-1 : ℚ) else 0) + (if i = 13 then (-1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]; simp

private theorem row320 (z : Fin 18 → ℚ) : proj z 320 = z 5 + z 9 := by
  have h : ∀ i, w i 320 = (if i = 5 then (1 : ℚ) else 0) + (if i = 9 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]; simp

private theorem row336 (z : Fin 18 → ℚ) : proj z 336 = -z 5 + z 8 := by
  have h : ∀ i, w i 336 = (if i = 5 then (-1 : ℚ) else 0) + (if i = 8 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]; simp

private theorem row448 (z : Fin 18 → ℚ) : proj z 448 = z 7 := by
  have h : ∀ i, w i 448 = (if i = 7 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row496 (z : Fin 18 → ℚ) : proj z 496 = z 5 := by
  have h : ∀ i, w i 496 = (if i = 5 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row512 (z : Fin 18 → ℚ) : proj z 512 = -z 11 + -z 16 := by
  have h : ∀ i, w i 512 = (if i = 11 then (-1 : ℚ) else 0) + (if i = 16 then (-1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]; simp

private theorem row640 (z : Fin 18 → ℚ) : proj z 640 = z 7 + z 11 := by
  have h : ∀ i, w i 640 = (if i = 7 then (1 : ℚ) else 0) + (if i = 11 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]; simp

private theorem row672 (z : Fin 18 → ℚ) : proj z 672 = -z 7 + z 10 := by
  have h : ∀ i, w i 672 = (if i = 7 then (-1 : ℚ) else 0) + (if i = 10 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]; simp

private theorem row896 (z : Fin 18 → ℚ) : proj z 896 = z 9 := by
  have h : ∀ i, w i 896 = (if i = 9 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row992 (z : Fin 18 → ℚ) : proj z 992 = z 7 := by
  have h : ∀ i, w i 992 = (if i = 7 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row1024 (z : Fin 18 → ℚ) : proj z 1024 = -z 14 := by
  have h : ∀ i, w i 1024 = (if i = 14 then (-1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row1088 (z : Fin 18 → ℚ) : proj z 1088 = z 8 := by
  have h : ∀ i, w i 1088 = (if i = 8 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row1280 (z : Fin 18 → ℚ) : proj z 1280 = z 9 + z 14 := by
  have h : ∀ i, w i 1280 = (if i = 9 then (1 : ℚ) else 0) + (if i = 14 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]; simp

private theorem row1364 (z : Fin 18 → ℚ) : proj z 1364 = z 8 := by
  have h : ∀ i, w i 1364 = (if i = 8 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row1792 (z : Fin 18 → ℚ) : proj z 1792 = z 11 := by
  have h : ∀ i, w i 1792 = (if i = 11 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row1984 (z : Fin 18 → ℚ) : proj z 1984 = z 9 := by
  have h : ∀ i, w i 1984 = (if i = 9 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row2048 (z : Fin 18 → ℚ) : proj z 2048 = -z 17 := by
  have h : ∀ i, w i 2048 = (if i = 17 then (-1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row2176 (z : Fin 18 → ℚ) : proj z 2176 = z 10 := by
  have h : ∀ i, w i 2176 = (if i = 10 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row2560 (z : Fin 18 → ℚ) : proj z 2560 = z 11 + z 17 := by
  have h : ∀ i, w i 2560 = (if i = 11 then (1 : ℚ) else 0) + (if i = 17 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_add, mul_ite, mul_zero, Finset.sum_add_distrib]; simp

private theorem row2728 (z : Fin 18 → ℚ) : proj z 2728 = z 10 := by
  have h : ∀ i, w i 2728 = (if i = 10 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row3968 (z : Fin 18 → ℚ) : proj z 3968 = z 11 := by
  have h : ∀ i, w i 3968 = (if i = 11 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row4160 (z : Fin 18 → ℚ) : proj z 4160 = z 12 := by
  have h : ∀ i, w i 4160 = (if i = 12 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row4352 (z : Fin 18 → ℚ) : proj z 4352 = z 13 := by
  have h : ∀ i, w i 4352 = (if i = 13 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row8320 (z : Fin 18 → ℚ) : proj z 8320 = z 15 := by
  have h : ∀ i, w i 8320 = (if i = 15 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

private theorem row8704 (z : Fin 18 → ℚ) : proj z 8704 = z 16 := by
  have h : ∀ i, w i 8704 = (if i = 16 then (1 : ℚ) else 0) := by decide +kernel
  simp only [proj, h, mul_ite, mul_zero]; simp

theorem center_elim (F : Finset Mask) (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false) (z : Fin 18 → ℚ)
    (vanished : ∀ a ∉ F, proj z a = 0) : ∀ p, z p = 0 := by
  have single3 : proj z 4 = 0 := vanished 4 (singleton_kills hg hne 2)
  have eq3 : z 0 = 0 := by linarith only [single3, (row4 z)]
  have single4 : proj z 8 = 0 := vanished 8 (singleton_kills hg hne 3)
  have eq4 : z 1 = 0 := by linarith only [single4, (row8 z)]
  have single5 : proj z 16 = 0 := vanished 16 (singleton_kills hg hne 4)
  have eq5 : z 2 + z 4 = 0 := by linarith only [single5, (row16 z)]
  have single6 : proj z 32 = 0 := vanished 32 (singleton_kills hg hne 5)
  have eq6 : z 3 + z 6 = 0 := by linarith only [single6, (row32 z)]
  have single7 : proj z 64 = 0 := vanished 64 (singleton_kills hg hne 6)
  have eq7 : z 5 + z 8 + z 12 = 0 := by linarith only [single7, (row64 z)]
  have single8 : proj z 128 = 0 := vanished 128 (singleton_kills hg hne 7)
  have eq8 : z 7 + z 10 + z 15 = 0 := by linarith only [single8, (row128 z)]
  have single9 : proj z 256 = 0 := vanished 256 (singleton_kills hg hne 8)
  have eq9 : z 9 + z 13 = 0 := by linarith only [single9, (row256 z)]
  have single10 : proj z 512 = 0 := vanished 512 (singleton_kills hg hne 9)
  have eq10 : z 11 + z 16 = 0 := by linarith only [single10, (row512 z)]
  have single11 : proj z 1024 = 0 := vanished 1024 (singleton_kills hg hne 10)
  have eq11 : z 14 = 0 := by linarith only [single11, (row1024 z)]
  have single12 : proj z 2048 = 0 := vanished 2048 (singleton_kills hg hne 11)
  have eq12 : z 17 = 0 := by linarith only [single12, (row2048 z)]
  have no4 : z 4 = 0 := by
    by_contra hact
    have hxE : 17 ∈ F := by by_contra hm; exact hact (by linarith only [vanished 17 hm, (row17 z), hact, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have kill34 : proj z 34 = 0 := vanished _ (disjoint_kills hg hxE (a := 34) (by decide) (by decide))
    have kill40 : proj z 40 = 0 := vanished _ (disjoint_kills hg hxE (a := 40) (by decide) (by decide))
    have y3 : z 3 = 0 := by linarith only [kill34, (row34 z), kill40, (row40 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y6 : z 6 = 0 := by linarith only [kill34, (row34 z), kill40, (row40 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill68 : proj z 68 = 0 := vanished _ (disjoint_kills hg hxE (a := 68) (by decide) (by decide))
    have kill1088 : proj z 1088 = 0 := vanished _ (disjoint_kills hg hxE (a := 1088) (by decide) (by decide))
    have kill4160 : proj z 4160 = 0 := vanished _ (disjoint_kills hg hxE (a := 4160) (by decide) (by decide))
    have y5 : z 5 = 0 := by linarith only [kill68, (row68 z), kill1088, (row1088 z), kill4160, (row4160 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y8 : z 8 = 0 := by linarith only [kill68, (row68 z), kill1088, (row1088 z), kill4160, (row4160 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y12 : z 12 = 0 := by linarith only [kill68, (row68 z), kill1088, (row1088 z), kill4160, (row4160 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill130 : proj z 130 = 0 := vanished _ (disjoint_kills hg hxE (a := 130) (by decide) (by decide))
    have kill136 : proj z 136 = 0 := vanished _ (disjoint_kills hg hxE (a := 136) (by decide) (by decide))
    have kill2176 : proj z 2176 = 0 := vanished _ (disjoint_kills hg hxE (a := 2176) (by decide) (by decide))
    have kill8320 : proj z 8320 = 0 := vanished _ (disjoint_kills hg hxE (a := 8320) (by decide) (by decide))
    have y7 : z 7 = 0 := by linarith only [kill130, (row130 z), kill136, (row136 z), kill2176, (row2176 z), kill8320, (row8320 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y10 : z 10 = 0 := by linarith only [kill130, (row130 z), kill136, (row136 z), kill2176, (row2176 z), kill8320, (row8320 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y15 : z 15 = 0 := by linarith only [kill130, (row130 z), kill136, (row136 z), kill2176, (row2176 z), kill8320, (row8320 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill1280 : proj z 1280 = 0 := vanished _ (disjoint_kills hg hxE (a := 1280) (by decide) (by decide))
    have kill4352 : proj z 4352 = 0 := vanished _ (disjoint_kills hg hxE (a := 4352) (by decide) (by decide))
    have y9 : z 9 = 0 := by linarith only [kill1280, (row1280 z), kill4352, (row4352 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y13 : z 13 = 0 := by linarith only [kill1280, (row1280 z), kill4352, (row4352 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill2560 : proj z 2560 = 0 := vanished _ (disjoint_kills hg hxE (a := 2560) (by decide) (by decide))
    have kill8704 : proj z 8704 = 0 := vanished _ (disjoint_kills hg hxE (a := 8704) (by decide) (by decide))
    have y11 : z 11 = 0 := by linarith only [kill2560, (row2560 z), kill8704, (row8704 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y16 : z 16 = 0 := by linarith only [kill2560, (row2560 z), kill8704, (row8704 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have hit124 : 124 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 124 hh, (row124 z), hact, y3, y6, y5, y8, y12, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have hit20 : 20 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 20 hh, (row20 z), hact, y3, y6, y5, y8, y12, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have hit80 : 80 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 80 hh, (row80 z), hact, y3, y6, y5, y8, y12, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have hit56 : 56 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 56 hh, (row56 z), hact, y3, y6, y5, y8, y12, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    exact forbidden hg hne 4 124 [20,80,56] (by decide) (by decide) (by decide +kernel) hit124 (List.forall_mem_cons.mpr ⟨hit20, List.forall_mem_cons.mpr ⟨hit80, List.forall_mem_cons.mpr ⟨hit56, List.forall_mem_nil _⟩⟩⟩)
  have no6 : z 6 = 0 := by
    by_contra hact
    have hxE : 34 ∈ F := by by_contra hm; exact hact (by linarith only [vanished 34 hm, (row34 z), hact, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have kill17 : proj z 17 = 0 := vanished _ (disjoint_kills hg hxE (a := 17) (by decide) (by decide))
    have kill20 : proj z 20 = 0 := vanished _ (disjoint_kills hg hxE (a := 20) (by decide) (by decide))
    have y2 : z 2 = 0 := by linarith only [kill17, (row17 z), kill20, (row20 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y4 : z 4 = 0 := by linarith only [kill17, (row17 z), kill20, (row20 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill65 : proj z 65 = 0 := vanished _ (disjoint_kills hg hxE (a := 65) (by decide) (by decide))
    have kill68 : proj z 68 = 0 := vanished _ (disjoint_kills hg hxE (a := 68) (by decide) (by decide))
    have kill1088 : proj z 1088 = 0 := vanished _ (disjoint_kills hg hxE (a := 1088) (by decide) (by decide))
    have kill4160 : proj z 4160 = 0 := vanished _ (disjoint_kills hg hxE (a := 4160) (by decide) (by decide))
    have y5 : z 5 = 0 := by linarith only [kill65, (row65 z), kill68, (row68 z), kill1088, (row1088 z), kill4160, (row4160 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y8 : z 8 = 0 := by linarith only [kill65, (row65 z), kill68, (row68 z), kill1088, (row1088 z), kill4160, (row4160 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y12 : z 12 = 0 := by linarith only [kill65, (row65 z), kill68, (row68 z), kill1088, (row1088 z), kill4160, (row4160 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill136 : proj z 136 = 0 := vanished _ (disjoint_kills hg hxE (a := 136) (by decide) (by decide))
    have kill2176 : proj z 2176 = 0 := vanished _ (disjoint_kills hg hxE (a := 2176) (by decide) (by decide))
    have kill8320 : proj z 8320 = 0 := vanished _ (disjoint_kills hg hxE (a := 8320) (by decide) (by decide))
    have y7 : z 7 = 0 := by linarith only [kill136, (row136 z), kill2176, (row2176 z), kill8320, (row8320 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y10 : z 10 = 0 := by linarith only [kill136, (row136 z), kill2176, (row2176 z), kill8320, (row8320 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y15 : z 15 = 0 := by linarith only [kill136, (row136 z), kill2176, (row2176 z), kill8320, (row8320 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill1280 : proj z 1280 = 0 := vanished _ (disjoint_kills hg hxE (a := 1280) (by decide) (by decide))
    have kill4352 : proj z 4352 = 0 := vanished _ (disjoint_kills hg hxE (a := 4352) (by decide) (by decide))
    have y9 : z 9 = 0 := by linarith only [kill1280, (row1280 z), kill4352, (row4352 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y13 : z 13 = 0 := by linarith only [kill1280, (row1280 z), kill4352, (row4352 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill2560 : proj z 2560 = 0 := vanished _ (disjoint_kills hg hxE (a := 2560) (by decide) (by decide))
    have kill8704 : proj z 8704 = 0 := vanished _ (disjoint_kills hg hxE (a := 8704) (by decide) (by decide))
    have y11 : z 11 = 0 := by linarith only [kill2560, (row2560 z), kill8704, (row8704 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y16 : z 16 = 0 := by linarith only [kill2560, (row2560 z), kill8704, (row8704 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have hit248 : 248 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 248 hh, (row248 z), hact, y2, y4, y5, y8, y12, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have hit40 : 40 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 40 hh, (row40 z), hact, y2, y4, y5, y8, y12, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have hit160 : 160 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 160 hh, (row160 z), hact, y2, y4, y5, y8, y12, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have hit112 : 112 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 112 hh, (row112 z), hact, y2, y4, y5, y8, y12, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    exact forbidden hg hne 5 248 [40,160,112] (by decide) (by decide) (by decide +kernel) hit248 (List.forall_mem_cons.mpr ⟨hit40, List.forall_mem_cons.mpr ⟨hit160, List.forall_mem_cons.mpr ⟨hit112, List.forall_mem_nil _⟩⟩⟩)
  have no8 : z 8 = 0 := by
    by_contra hact
    have hxE : 68 ∈ F := by by_contra hm; exact hact (by linarith only [vanished 68 hm, (row68 z), hact, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have kill17 : proj z 17 = 0 := vanished _ (disjoint_kills hg hxE (a := 17) (by decide) (by decide))
    have y2 : z 2 = 0 := by linarith only [kill17, (row17 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y4 : z 4 = 0 := by linarith only [kill17, (row17 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill34 : proj z 34 = 0 := vanished _ (disjoint_kills hg hxE (a := 34) (by decide) (by decide))
    have kill40 : proj z 40 = 0 := vanished _ (disjoint_kills hg hxE (a := 40) (by decide) (by decide))
    have y3 : z 3 = 0 := by linarith only [kill34, (row34 z), kill40, (row40 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y6 : z 6 = 0 := by linarith only [kill34, (row34 z), kill40, (row40 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill130 : proj z 130 = 0 := vanished _ (disjoint_kills hg hxE (a := 130) (by decide) (by decide))
    have kill136 : proj z 136 = 0 := vanished _ (disjoint_kills hg hxE (a := 136) (by decide) (by decide))
    have kill2176 : proj z 2176 = 0 := vanished _ (disjoint_kills hg hxE (a := 2176) (by decide) (by decide))
    have kill8320 : proj z 8320 = 0 := vanished _ (disjoint_kills hg hxE (a := 8320) (by decide) (by decide))
    have y7 : z 7 = 0 := by linarith only [kill130, (row130 z), kill136, (row136 z), kill2176, (row2176 z), kill8320, (row8320 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y10 : z 10 = 0 := by linarith only [kill130, (row130 z), kill136, (row136 z), kill2176, (row2176 z), kill8320, (row8320 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y15 : z 15 = 0 := by linarith only [kill130, (row130 z), kill136, (row136 z), kill2176, (row2176 z), kill8320, (row8320 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill1280 : proj z 1280 = 0 := vanished _ (disjoint_kills hg hxE (a := 1280) (by decide) (by decide))
    have kill4352 : proj z 4352 = 0 := vanished _ (disjoint_kills hg hxE (a := 4352) (by decide) (by decide))
    have y9 : z 9 = 0 := by linarith only [kill1280, (row1280 z), kill4352, (row4352 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y13 : z 13 = 0 := by linarith only [kill1280, (row1280 z), kill4352, (row4352 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill2560 : proj z 2560 = 0 := vanished _ (disjoint_kills hg hxE (a := 2560) (by decide) (by decide))
    have kill8704 : proj z 8704 = 0 := vanished _ (disjoint_kills hg hxE (a := 8704) (by decide) (by decide))
    have y11 : z 11 = 0 := by linarith only [kill2560, (row2560 z), kill8704, (row8704 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y16 : z 16 = 0 := by linarith only [kill2560, (row2560 z), kill8704, (row8704 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    by_cases hz1 : z 5 = 0
    ·
      have hit1364 : 1364 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 1364 hh, (row1364 z), hact, hz1, y2, y4, y3, y6, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit68 : 68 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 68 hh, (row68 z), hact, hz1, y2, y4, y3, y6, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit1088 : 1088 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 1088 hh, (row1088 z), hact, hz1, y2, y4, y3, y6, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit336 : 336 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 336 hh, (row336 z), hact, hz1, y2, y4, y3, y6, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      exact forbidden hg hne 6 1364 [68,1088,336] (by decide) (by decide) (by decide +kernel) hit1364 (List.forall_mem_cons.mpr ⟨hit68, List.forall_mem_cons.mpr ⟨hit1088, List.forall_mem_cons.mpr ⟨hit336, List.forall_mem_nil _⟩⟩⟩)
    ·
      have hit496 : 496 ∈ F := by by_contra hh; exact hz1 (by linarith only [vanished 496 hh, (row496 z), hz1, y2, y4, y3, y6, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit80 : 80 ∈ F := by by_contra hh; exact hz1 (by linarith only [vanished 80 hh, (row80 z), hz1, y2, y4, y3, y6, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit320 : 320 ∈ F := by by_contra hh; exact hz1 (by linarith only [vanished 320 hh, (row320 z), hz1, y2, y4, y3, y6, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit224 : 224 ∈ F := by by_contra hh; exact hz1 (by linarith only [vanished 224 hh, (row224 z), hz1, y2, y4, y3, y6, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      exact forbidden hg hne 6 496 [80,320,224] (by decide) (by decide) (by decide +kernel) hit496 (List.forall_mem_cons.mpr ⟨hit80, List.forall_mem_cons.mpr ⟨hit320, List.forall_mem_cons.mpr ⟨hit224, List.forall_mem_nil _⟩⟩⟩)
  have no12 : z 12 = 0 := by
    by_contra hact
    have hxE : 65 ∈ F := by by_contra hm; exact hact (by linarith only [vanished 65 hm, (row65 z), hact, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have kill20 : proj z 20 = 0 := vanished _ (disjoint_kills hg hxE (a := 20) (by decide) (by decide))
    have y2 : z 2 = 0 := by linarith only [kill20, (row20 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y4 : z 4 = 0 := by linarith only [kill20, (row20 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill34 : proj z 34 = 0 := vanished _ (disjoint_kills hg hxE (a := 34) (by decide) (by decide))
    have kill40 : proj z 40 = 0 := vanished _ (disjoint_kills hg hxE (a := 40) (by decide) (by decide))
    have y3 : z 3 = 0 := by linarith only [kill34, (row34 z), kill40, (row40 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y6 : z 6 = 0 := by linarith only [kill34, (row34 z), kill40, (row40 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill130 : proj z 130 = 0 := vanished _ (disjoint_kills hg hxE (a := 130) (by decide) (by decide))
    have kill136 : proj z 136 = 0 := vanished _ (disjoint_kills hg hxE (a := 136) (by decide) (by decide))
    have kill2176 : proj z 2176 = 0 := vanished _ (disjoint_kills hg hxE (a := 2176) (by decide) (by decide))
    have kill8320 : proj z 8320 = 0 := vanished _ (disjoint_kills hg hxE (a := 8320) (by decide) (by decide))
    have y7 : z 7 = 0 := by linarith only [kill130, (row130 z), kill136, (row136 z), kill2176, (row2176 z), kill8320, (row8320 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y10 : z 10 = 0 := by linarith only [kill130, (row130 z), kill136, (row136 z), kill2176, (row2176 z), kill8320, (row8320 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y15 : z 15 = 0 := by linarith only [kill130, (row130 z), kill136, (row136 z), kill2176, (row2176 z), kill8320, (row8320 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill1280 : proj z 1280 = 0 := vanished _ (disjoint_kills hg hxE (a := 1280) (by decide) (by decide))
    have kill4352 : proj z 4352 = 0 := vanished _ (disjoint_kills hg hxE (a := 4352) (by decide) (by decide))
    have y9 : z 9 = 0 := by linarith only [kill1280, (row1280 z), kill4352, (row4352 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y13 : z 13 = 0 := by linarith only [kill1280, (row1280 z), kill4352, (row4352 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill2560 : proj z 2560 = 0 := vanished _ (disjoint_kills hg hxE (a := 2560) (by decide) (by decide))
    have kill8704 : proj z 8704 = 0 := vanished _ (disjoint_kills hg hxE (a := 8704) (by decide) (by decide))
    have y11 : z 11 = 0 := by linarith only [kill2560, (row2560 z), kill8704, (row8704 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y16 : z 16 = 0 := by linarith only [kill2560, (row2560 z), kill8704, (row8704 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    by_cases hz1 : z 5 = 0
    ·
      have hit1364 : 1364 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 1364 hh, (row1364 z), hact, hz1, y2, y4, y3, y6, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit68 : 68 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 68 hh, (row68 z), hact, hz1, y2, y4, y3, y6, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit1088 : 1088 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 1088 hh, (row1088 z), hact, hz1, y2, y4, y3, y6, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit336 : 336 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 336 hh, (row336 z), hact, hz1, y2, y4, y3, y6, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      exact forbidden hg hne 6 1364 [68,1088,336] (by decide) (by decide) (by decide +kernel) hit1364 (List.forall_mem_cons.mpr ⟨hit68, List.forall_mem_cons.mpr ⟨hit1088, List.forall_mem_cons.mpr ⟨hit336, List.forall_mem_nil _⟩⟩⟩)
    ·
      have hit496 : 496 ∈ F := by by_contra hh; exact hz1 (by linarith only [vanished 496 hh, (row496 z), hz1, y2, y4, y3, y6, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit80 : 80 ∈ F := by by_contra hh; exact hz1 (by linarith only [vanished 80 hh, (row80 z), hz1, y2, y4, y3, y6, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit320 : 320 ∈ F := by by_contra hh; exact hz1 (by linarith only [vanished 320 hh, (row320 z), hz1, y2, y4, y3, y6, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit224 : 224 ∈ F := by by_contra hh; exact hz1 (by linarith only [vanished 224 hh, (row224 z), hz1, y2, y4, y3, y6, y7, y10, y15, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      exact forbidden hg hne 6 496 [80,320,224] (by decide) (by decide) (by decide +kernel) hit496 (List.forall_mem_cons.mpr ⟨hit80, List.forall_mem_cons.mpr ⟨hit320, List.forall_mem_cons.mpr ⟨hit224, List.forall_mem_nil _⟩⟩⟩)
  have no10 : z 10 = 0 := by
    by_contra hact
    have hxE : 136 ∈ F := by by_contra hm; exact hact (by linarith only [vanished 136 hm, (row136 z), hact, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have kill17 : proj z 17 = 0 := vanished _ (disjoint_kills hg hxE (a := 17) (by decide) (by decide))
    have kill20 : proj z 20 = 0 := vanished _ (disjoint_kills hg hxE (a := 20) (by decide) (by decide))
    have y2 : z 2 = 0 := by linarith only [kill17, (row17 z), kill20, (row20 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y4 : z 4 = 0 := by linarith only [kill17, (row17 z), kill20, (row20 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill34 : proj z 34 = 0 := vanished _ (disjoint_kills hg hxE (a := 34) (by decide) (by decide))
    have y3 : z 3 = 0 := by linarith only [kill34, (row34 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y6 : z 6 = 0 := by linarith only [kill34, (row34 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill65 : proj z 65 = 0 := vanished _ (disjoint_kills hg hxE (a := 65) (by decide) (by decide))
    have kill68 : proj z 68 = 0 := vanished _ (disjoint_kills hg hxE (a := 68) (by decide) (by decide))
    have kill1088 : proj z 1088 = 0 := vanished _ (disjoint_kills hg hxE (a := 1088) (by decide) (by decide))
    have kill4160 : proj z 4160 = 0 := vanished _ (disjoint_kills hg hxE (a := 4160) (by decide) (by decide))
    have y5 : z 5 = 0 := by linarith only [kill65, (row65 z), kill68, (row68 z), kill1088, (row1088 z), kill4160, (row4160 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y8 : z 8 = 0 := by linarith only [kill65, (row65 z), kill68, (row68 z), kill1088, (row1088 z), kill4160, (row4160 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y12 : z 12 = 0 := by linarith only [kill65, (row65 z), kill68, (row68 z), kill1088, (row1088 z), kill4160, (row4160 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill1280 : proj z 1280 = 0 := vanished _ (disjoint_kills hg hxE (a := 1280) (by decide) (by decide))
    have kill4352 : proj z 4352 = 0 := vanished _ (disjoint_kills hg hxE (a := 4352) (by decide) (by decide))
    have y9 : z 9 = 0 := by linarith only [kill1280, (row1280 z), kill4352, (row4352 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y13 : z 13 = 0 := by linarith only [kill1280, (row1280 z), kill4352, (row4352 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill2560 : proj z 2560 = 0 := vanished _ (disjoint_kills hg hxE (a := 2560) (by decide) (by decide))
    have kill8704 : proj z 8704 = 0 := vanished _ (disjoint_kills hg hxE (a := 8704) (by decide) (by decide))
    have y11 : z 11 = 0 := by linarith only [kill2560, (row2560 z), kill8704, (row8704 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y16 : z 16 = 0 := by linarith only [kill2560, (row2560 z), kill8704, (row8704 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    by_cases hz1 : z 7 = 0
    ·
      have hit2728 : 2728 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 2728 hh, (row2728 z), hact, hz1, y2, y4, y3, y6, y5, y8, y12, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit136 : 136 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 136 hh, (row136 z), hact, hz1, y2, y4, y3, y6, y5, y8, y12, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit2176 : 2176 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 2176 hh, (row2176 z), hact, hz1, y2, y4, y3, y6, y5, y8, y12, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit672 : 672 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 672 hh, (row672 z), hact, hz1, y2, y4, y3, y6, y5, y8, y12, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      exact forbidden hg hne 7 2728 [136,2176,672] (by decide) (by decide) (by decide +kernel) hit2728 (List.forall_mem_cons.mpr ⟨hit136, List.forall_mem_cons.mpr ⟨hit2176, List.forall_mem_cons.mpr ⟨hit672, List.forall_mem_nil _⟩⟩⟩)
    ·
      have hit992 : 992 ∈ F := by by_contra hh; exact hz1 (by linarith only [vanished 992 hh, (row992 z), hz1, y2, y4, y3, y6, y5, y8, y12, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit160 : 160 ∈ F := by by_contra hh; exact hz1 (by linarith only [vanished 160 hh, (row160 z), hz1, y2, y4, y3, y6, y5, y8, y12, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit640 : 640 ∈ F := by by_contra hh; exact hz1 (by linarith only [vanished 640 hh, (row640 z), hz1, y2, y4, y3, y6, y5, y8, y12, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit448 : 448 ∈ F := by by_contra hh; exact hz1 (by linarith only [vanished 448 hh, (row448 z), hz1, y2, y4, y3, y6, y5, y8, y12, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      exact forbidden hg hne 7 992 [160,640,448] (by decide) (by decide) (by decide +kernel) hit992 (List.forall_mem_cons.mpr ⟨hit160, List.forall_mem_cons.mpr ⟨hit640, List.forall_mem_cons.mpr ⟨hit448, List.forall_mem_nil _⟩⟩⟩)
  have no15 : z 15 = 0 := by
    by_contra hact
    have hxE : 130 ∈ F := by by_contra hm; exact hact (by linarith only [vanished 130 hm, (row130 z), hact, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have kill17 : proj z 17 = 0 := vanished _ (disjoint_kills hg hxE (a := 17) (by decide) (by decide))
    have kill20 : proj z 20 = 0 := vanished _ (disjoint_kills hg hxE (a := 20) (by decide) (by decide))
    have y2 : z 2 = 0 := by linarith only [kill17, (row17 z), kill20, (row20 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y4 : z 4 = 0 := by linarith only [kill17, (row17 z), kill20, (row20 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill40 : proj z 40 = 0 := vanished _ (disjoint_kills hg hxE (a := 40) (by decide) (by decide))
    have y3 : z 3 = 0 := by linarith only [kill40, (row40 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y6 : z 6 = 0 := by linarith only [kill40, (row40 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill65 : proj z 65 = 0 := vanished _ (disjoint_kills hg hxE (a := 65) (by decide) (by decide))
    have kill68 : proj z 68 = 0 := vanished _ (disjoint_kills hg hxE (a := 68) (by decide) (by decide))
    have kill1088 : proj z 1088 = 0 := vanished _ (disjoint_kills hg hxE (a := 1088) (by decide) (by decide))
    have kill4160 : proj z 4160 = 0 := vanished _ (disjoint_kills hg hxE (a := 4160) (by decide) (by decide))
    have y5 : z 5 = 0 := by linarith only [kill65, (row65 z), kill68, (row68 z), kill1088, (row1088 z), kill4160, (row4160 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y8 : z 8 = 0 := by linarith only [kill65, (row65 z), kill68, (row68 z), kill1088, (row1088 z), kill4160, (row4160 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y12 : z 12 = 0 := by linarith only [kill65, (row65 z), kill68, (row68 z), kill1088, (row1088 z), kill4160, (row4160 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill1280 : proj z 1280 = 0 := vanished _ (disjoint_kills hg hxE (a := 1280) (by decide) (by decide))
    have kill4352 : proj z 4352 = 0 := vanished _ (disjoint_kills hg hxE (a := 4352) (by decide) (by decide))
    have y9 : z 9 = 0 := by linarith only [kill1280, (row1280 z), kill4352, (row4352 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y13 : z 13 = 0 := by linarith only [kill1280, (row1280 z), kill4352, (row4352 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill2560 : proj z 2560 = 0 := vanished _ (disjoint_kills hg hxE (a := 2560) (by decide) (by decide))
    have kill8704 : proj z 8704 = 0 := vanished _ (disjoint_kills hg hxE (a := 8704) (by decide) (by decide))
    have y11 : z 11 = 0 := by linarith only [kill2560, (row2560 z), kill8704, (row8704 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y16 : z 16 = 0 := by linarith only [kill2560, (row2560 z), kill8704, (row8704 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    by_cases hz1 : z 7 = 0
    ·
      have hit2728 : 2728 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 2728 hh, (row2728 z), hact, hz1, y2, y4, y3, y6, y5, y8, y12, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit136 : 136 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 136 hh, (row136 z), hact, hz1, y2, y4, y3, y6, y5, y8, y12, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit2176 : 2176 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 2176 hh, (row2176 z), hact, hz1, y2, y4, y3, y6, y5, y8, y12, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit672 : 672 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 672 hh, (row672 z), hact, hz1, y2, y4, y3, y6, y5, y8, y12, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      exact forbidden hg hne 7 2728 [136,2176,672] (by decide) (by decide) (by decide +kernel) hit2728 (List.forall_mem_cons.mpr ⟨hit136, List.forall_mem_cons.mpr ⟨hit2176, List.forall_mem_cons.mpr ⟨hit672, List.forall_mem_nil _⟩⟩⟩)
    ·
      have hit992 : 992 ∈ F := by by_contra hh; exact hz1 (by linarith only [vanished 992 hh, (row992 z), hz1, y2, y4, y3, y6, y5, y8, y12, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit160 : 160 ∈ F := by by_contra hh; exact hz1 (by linarith only [vanished 160 hh, (row160 z), hz1, y2, y4, y3, y6, y5, y8, y12, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit640 : 640 ∈ F := by by_contra hh; exact hz1 (by linarith only [vanished 640 hh, (row640 z), hz1, y2, y4, y3, y6, y5, y8, y12, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      have hit448 : 448 ∈ F := by by_contra hh; exact hz1 (by linarith only [vanished 448 hh, (row448 z), hz1, y2, y4, y3, y6, y5, y8, y12, y9, y13, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
      exact forbidden hg hne 7 992 [160,640,448] (by decide) (by decide) (by decide +kernel) hit992 (List.forall_mem_cons.mpr ⟨hit160, List.forall_mem_cons.mpr ⟨hit640, List.forall_mem_cons.mpr ⟨hit448, List.forall_mem_nil _⟩⟩⟩)
  have no13 : z 13 = 0 := by
    by_contra hact
    have hxE : 4352 ∈ F := by by_contra hm; exact hact (by linarith only [vanished 4352 hm, (row4352 z), hact, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have kill17 : proj z 17 = 0 := vanished _ (disjoint_kills hg hxE (a := 17) (by decide) (by decide))
    have kill20 : proj z 20 = 0 := vanished _ (disjoint_kills hg hxE (a := 20) (by decide) (by decide))
    have y2 : z 2 = 0 := by linarith only [kill17, (row17 z), kill20, (row20 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y4 : z 4 = 0 := by linarith only [kill17, (row17 z), kill20, (row20 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill34 : proj z 34 = 0 := vanished _ (disjoint_kills hg hxE (a := 34) (by decide) (by decide))
    have kill40 : proj z 40 = 0 := vanished _ (disjoint_kills hg hxE (a := 40) (by decide) (by decide))
    have y3 : z 3 = 0 := by linarith only [kill34, (row34 z), kill40, (row40 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y6 : z 6 = 0 := by linarith only [kill34, (row34 z), kill40, (row40 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill65 : proj z 65 = 0 := vanished _ (disjoint_kills hg hxE (a := 65) (by decide) (by decide))
    have kill68 : proj z 68 = 0 := vanished _ (disjoint_kills hg hxE (a := 68) (by decide) (by decide))
    have kill1088 : proj z 1088 = 0 := vanished _ (disjoint_kills hg hxE (a := 1088) (by decide) (by decide))
    have y5 : z 5 = 0 := by linarith only [kill65, (row65 z), kill68, (row68 z), kill1088, (row1088 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y8 : z 8 = 0 := by linarith only [kill65, (row65 z), kill68, (row68 z), kill1088, (row1088 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y12 : z 12 = 0 := by linarith only [kill65, (row65 z), kill68, (row68 z), kill1088, (row1088 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill130 : proj z 130 = 0 := vanished _ (disjoint_kills hg hxE (a := 130) (by decide) (by decide))
    have kill136 : proj z 136 = 0 := vanished _ (disjoint_kills hg hxE (a := 136) (by decide) (by decide))
    have kill2176 : proj z 2176 = 0 := vanished _ (disjoint_kills hg hxE (a := 2176) (by decide) (by decide))
    have kill8320 : proj z 8320 = 0 := vanished _ (disjoint_kills hg hxE (a := 8320) (by decide) (by decide))
    have y7 : z 7 = 0 := by linarith only [kill130, (row130 z), kill136, (row136 z), kill2176, (row2176 z), kill8320, (row8320 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y10 : z 10 = 0 := by linarith only [kill130, (row130 z), kill136, (row136 z), kill2176, (row2176 z), kill8320, (row8320 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y15 : z 15 = 0 := by linarith only [kill130, (row130 z), kill136, (row136 z), kill2176, (row2176 z), kill8320, (row8320 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill2560 : proj z 2560 = 0 := vanished _ (disjoint_kills hg hxE (a := 2560) (by decide) (by decide))
    have kill8704 : proj z 8704 = 0 := vanished _ (disjoint_kills hg hxE (a := 8704) (by decide) (by decide))
    have y11 : z 11 = 0 := by linarith only [kill2560, (row2560 z), kill8704, (row8704 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y16 : z 16 = 0 := by linarith only [kill2560, (row2560 z), kill8704, (row8704 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have hit1984 : 1984 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 1984 hh, (row1984 z), hact, y2, y4, y3, y6, y5, y8, y12, y7, y10, y15, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have hit320 : 320 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 320 hh, (row320 z), hact, y2, y4, y3, y6, y5, y8, y12, y7, y10, y15, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have hit1280 : 1280 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 1280 hh, (row1280 z), hact, y2, y4, y3, y6, y5, y8, y12, y7, y10, y15, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have hit896 : 896 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 896 hh, (row896 z), hact, y2, y4, y3, y6, y5, y8, y12, y7, y10, y15, y11, y16, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    exact forbidden hg hne 8 1984 [320,1280,896] (by decide) (by decide) (by decide +kernel) hit1984 (List.forall_mem_cons.mpr ⟨hit320, List.forall_mem_cons.mpr ⟨hit1280, List.forall_mem_cons.mpr ⟨hit896, List.forall_mem_nil _⟩⟩⟩)
  have no16 : z 16 = 0 := by
    by_contra hact
    have hxE : 8704 ∈ F := by by_contra hm; exact hact (by linarith only [vanished 8704 hm, (row8704 z), hact, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have kill17 : proj z 17 = 0 := vanished _ (disjoint_kills hg hxE (a := 17) (by decide) (by decide))
    have kill20 : proj z 20 = 0 := vanished _ (disjoint_kills hg hxE (a := 20) (by decide) (by decide))
    have y2 : z 2 = 0 := by linarith only [kill17, (row17 z), kill20, (row20 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y4 : z 4 = 0 := by linarith only [kill17, (row17 z), kill20, (row20 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill34 : proj z 34 = 0 := vanished _ (disjoint_kills hg hxE (a := 34) (by decide) (by decide))
    have kill40 : proj z 40 = 0 := vanished _ (disjoint_kills hg hxE (a := 40) (by decide) (by decide))
    have y3 : z 3 = 0 := by linarith only [kill34, (row34 z), kill40, (row40 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y6 : z 6 = 0 := by linarith only [kill34, (row34 z), kill40, (row40 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill65 : proj z 65 = 0 := vanished _ (disjoint_kills hg hxE (a := 65) (by decide) (by decide))
    have kill68 : proj z 68 = 0 := vanished _ (disjoint_kills hg hxE (a := 68) (by decide) (by decide))
    have kill1088 : proj z 1088 = 0 := vanished _ (disjoint_kills hg hxE (a := 1088) (by decide) (by decide))
    have kill4160 : proj z 4160 = 0 := vanished _ (disjoint_kills hg hxE (a := 4160) (by decide) (by decide))
    have y5 : z 5 = 0 := by linarith only [kill65, (row65 z), kill68, (row68 z), kill1088, (row1088 z), kill4160, (row4160 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y8 : z 8 = 0 := by linarith only [kill65, (row65 z), kill68, (row68 z), kill1088, (row1088 z), kill4160, (row4160 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y12 : z 12 = 0 := by linarith only [kill65, (row65 z), kill68, (row68 z), kill1088, (row1088 z), kill4160, (row4160 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill130 : proj z 130 = 0 := vanished _ (disjoint_kills hg hxE (a := 130) (by decide) (by decide))
    have kill136 : proj z 136 = 0 := vanished _ (disjoint_kills hg hxE (a := 136) (by decide) (by decide))
    have kill2176 : proj z 2176 = 0 := vanished _ (disjoint_kills hg hxE (a := 2176) (by decide) (by decide))
    have y7 : z 7 = 0 := by linarith only [kill130, (row130 z), kill136, (row136 z), kill2176, (row2176 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y10 : z 10 = 0 := by linarith only [kill130, (row130 z), kill136, (row136 z), kill2176, (row2176 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y15 : z 15 = 0 := by linarith only [kill130, (row130 z), kill136, (row136 z), kill2176, (row2176 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have kill1280 : proj z 1280 = 0 := vanished _ (disjoint_kills hg hxE (a := 1280) (by decide) (by decide))
    have kill4352 : proj z 4352 = 0 := vanished _ (disjoint_kills hg hxE (a := 4352) (by decide) (by decide))
    have y9 : z 9 = 0 := by linarith only [kill1280, (row1280 z), kill4352, (row4352 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have y13 : z 13 = 0 := by linarith only [kill1280, (row1280 z), kill4352, (row4352 z), eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12]
    have hit3968 : 3968 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 3968 hh, (row3968 z), hact, y2, y4, y3, y6, y5, y8, y12, y7, y10, y15, y9, y13, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have hit640 : 640 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 640 hh, (row640 z), hact, y2, y4, y3, y6, y5, y8, y12, y7, y10, y15, y9, y13, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have hit2560 : 2560 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 2560 hh, (row2560 z), hact, y2, y4, y3, y6, y5, y8, y12, y7, y10, y15, y9, y13, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    have hit1792 : 1792 ∈ F := by by_contra hh; exact hact (by linarith only [vanished 1792 hh, (row1792 z), hact, y2, y4, y3, y6, y5, y8, y12, y7, y10, y15, y9, y13, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12])
    exact forbidden hg hne 9 3968 [640,2560,1792] (by decide) (by decide) (by decide +kernel) hit3968 (List.forall_mem_cons.mpr ⟨hit640, List.forall_mem_cons.mpr ⟨hit2560, List.forall_mem_cons.mpr ⟨hit1792, List.forall_mem_nil _⟩⟩⟩)
  have zero0 : z 0 = 0 := by linarith only [eq3]
  have zero1 : z 1 = 0 := by linarith only [eq4]
  have zero2 : z 2 = 0 := by linarith only [eq5, no4]
  have zero3 : z 3 = 0 := by linarith only [eq6, no6]
  have zero4 : z 4 = 0 := by linarith only [eq5, no4]
  have zero5 : z 5 = 0 := by linarith only [eq7, no8, no12]
  have zero6 : z 6 = 0 := by linarith only [eq6, no6]
  have zero7 : z 7 = 0 := by linarith only [eq8, no10, no15]
  have zero8 : z 8 = 0 := by linarith only [eq7, no8, no12]
  have zero9 : z 9 = 0 := by linarith only [eq9, no13]
  have zero10 : z 10 = 0 := by linarith only [eq8, no10, no15]
  have zero11 : z 11 = 0 := by linarith only [eq10, no16]
  have zero12 : z 12 = 0 := by linarith only [eq7, no8, no12]
  have zero13 : z 13 = 0 := by linarith only [eq9, no13]
  have zero14 : z 14 = 0 := by linarith only [eq11]
  have zero15 : z 15 = 0 := by linarith only [eq8, no10, no15]
  have zero16 : z 16 = 0 := by linarith only [eq10, no16]
  have zero17 : z 17 = 0 := by linarith only [eq12]
  intro p; fin_cases p <;> first | exact zero0 | exact zero1 | exact zero2 | exact zero3 | exact zero4 | exact zero5 | exact zero6 | exact zero7 | exact zero8 | exact zero9 | exact zero10 | exact zero11 | exact zero12 | exact zero13 | exact zero14 | exact zero15 | exact zero16 | exact zero17

end RankProof
end E272
