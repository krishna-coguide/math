import Erdos272.NeutralCover
import Erdos272.Primitive

namespace E272.Neutral
open Finset RankProof
open scoped Matrix
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

private theorem no_singleton {F : Finset Mask} (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false) (x : Fin 14) : ((1 : Mask) <<< x.val) ∉ F := by
  intro hh
  obtain ⟨b,hb,hx⟩ := hne x
  have ne : b ≠ (1 : Mask) <<< x.val := by rintro rfl; simp [x.isLt] at hx
  have h := hg b hb _ hh ne
  have he : b &&& ((1 : Mask) <<< x.val) = 0 := by
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    by_cases e : j = x.val
    · subst j; rw [BitVec.getLsbD_and,hx]; simp
    · simp [hj]; omega
  rw [he] at h; exact (by decide : ap 0 ≠ true) h

private theorem kernel_elim {F : Finset Mask} (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false) {c : Mask → ℚ} {z : Fin 31 → ℚ}
    (hr : ∀ a, c a = eval z a) (hF : ∀ a ∉ F, c a = 0)
    (hz : ∀ j : Fin 4, ∑ i, (checkWeight j i : ℚ) * z i = 0) : c = 0 := by
  by_cases h : ∀ i, z i = 0
  · funext a; simp [hr,eval,h]
  push Not at h; obtain ⟨k,hk⟩ := h
  obtain ⟨r,b,hr₀,hb,j,hj⟩ := primitive_parity z hk
  have coeff_sum (a : Mask) : ((∑ i, coeff i a * b i : ℤ) : ℚ) = r * c a := by
    rw [hr]; simp only [eval,rowQ,Int.cast_sum,Int.cast_mul,hb,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
  have off (a : Mask) (ha : a ∉ F) : ∑ i, coeff i a * b i = 0 := by
    have hh := coeff_sum a; rw [hF a ha,mul_zero] at hh; exact_mod_cast hh
  have ck (j : Fin 4) : ∑ i, checkWeight j i * b i = 0 := by
    apply Int.cast_injective (α := ℚ)
    calc
      _ = r * (∑ i, (checkWeight j i : ℚ) * z i) := by
        simp only [Int.cast_sum,Int.cast_mul,hb,Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring
      _ = _ := by rw [hz,mul_zero]; simp
  let m : Fin 31 → ZMod 2 := fun i => (b i : ZMod 2)
  have hc : eqMatrix *ᵥ m = 0 := by
    funext i
    change ∑ j, eqMatrix i j * (b j : ZMod 2) = 0
    simp_rw [eq_entry]; by_cases h14 : i.val < 14
    · simp only [dite_eq_left h14]; exact_mod_cast congrArg (fun t : ℤ => (t : ZMod 2)) (off _ (no_singleton hg hne ⟨i.val,h14⟩))
    · simp only [dite_eq_right h14]; exact_mod_cast congrArg (fun t : ℤ => (t : ZMod 2)) (ck ⟨i.val-14,by omega⟩)
  have hB := binary_zero hg hne m hc (by
    intro w hw; by_contra ha; apply hw
    change ∑ j, testMatrix w j * (b j : ZMod 2) = 0
    simp_rw [test_entry]; exact_mod_cast congrArg (fun t : ℤ => (t : ZMod 2)) (off _ ha))
  exact False.elim (hj (congrFun hB j))

/-- Only four fixed neutral checks suffice, even when every neutral AP is a member candidate. -/
theorem four_check_bound {F S : Finset Mask} (hSF : S ⊆ F)
    (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false)
    (L : List Mask) (hL : ∀ t ∈ posLong, ∀ a ∈ S, sub t a = true → t ∈ L) :
    S.card ≤ 92 + L.length + 4 := by
  classical
  let U : S → (Fin pos.length ⊕ Fin L.length) ⊕ Fin 4 → ℚ := fun a => Sum.elim (Sum.elim (feature pos a) (feature L a)) (checkCol a)
  have hli : LinearIndependent ℚ U := by
    apply Fintype.linearIndependent_iff.mpr
    intro cs hup v
    have hu (t : Mask) (ht : t ∈ fullPos) : ∑ a : S, cs a * inc t a = 0 := by
      rcases List.mem_append.mp ht with hp | hl
      · obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hp
        simpa [U,feature] using congrFun hup (Sum.inl (Sum.inl ⟨i,hi⟩))
      · by_cases hm : t ∈ L
        · obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hm
          simpa [U,feature] using congrFun hup (Sum.inl (Sum.inr ⟨i,hi⟩))
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
    have coffF (a : Mask) (ha : a ∉ F) := coff a (fun h => ha (hSF h))
    have hcov (a : Mask) (ha : c a ≠ 0) : ap a = true := by
      by_cases hm : a ∈ S
      · cases e : ap a with
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
    let z := fun i => ∑ a, c a * inc (neutral i) a
    have hz (j : Fin 4) : ∑ i, (checkWeight j i : ℚ) * z i = 0 := by
      have h0 : ∑ a : S, cs a * checkCol a j = 0 := by simpa [U] using congrFun hup (Sum.inr j)
      simp only [checkCol, Finset.mul_sum] at h0
      rw [Finset.sum_comm] at h0
      dsimp only [z]; simp_rw [hsum]
      simp_rw [mul_left_comm (cs _) (checkWeight j _ : ℚ), ← Finset.mul_sum] at h0
      exact h0
    have H := kernel_elim hg hne (reconstruct c hcov hann) coffF hz
    rw [←con v,H]; rfl
  have h := hli.fintype_card_le_finrank
  rw [Fintype.card_coe,Module.finrank_pi,Fintype.card_sum,Fintype.card_sum,Fintype.card_fin,Fintype.card_fin,Fintype.card_fin] at h
  exact h


theorem capped_mobius_cost (F : Finset Mask)
    (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false) :
    F.card ≤ 92 + (activeLong F).length + min 4 (F ∩ zeroLong.toFinset).card := by
  have h := four_check_bound (F := F) (S := F) (by rfl) hg hne (activeLong F) (by
    intro t ht a ha hs
    exact List.mem_filter.mpr ⟨ht,decide_eq_true ⟨a,ha,hs⟩⟩)
  have hh := mobius_cost_bound F hg hne; omega

end E272.Neutral
