import Mathlib.LinearAlgebra.Dimension.Finite
import Erdos272.RankCenters
import Erdos272.Score

namespace E272
open Finset RankProof
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

/-! Local rank bounds do not require the individual members to be short. -/

private theorem local_aux {F S : Finset Mask} (hSF : S ⊆ F)
    (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false)
    {n : ℕ} (extra : S → Fin n → ℚ)
    (ker : ∀ (c : S → ℚ), (∀ j, ∑ a, c a * feature pos a j = 0) →
      (∀ k, ∑ a, c a * extra a k = 0) →
      (∀ j, ∑ a, c a * feature neg a j = 0) ∧ ∀ a, c a ≠ 0 → ap a = true ∧ short a = true) :
    S.card ≤ 92 + n := by
  classical
  let U : S → Fin pos.length ⊕ Fin n → ℚ := fun a => Sum.elim (feature pos a) (extra a)
  have hli : LinearIndependent ℚ U := by
    apply Fintype.linearIndependent_iff.mpr
    intro coeffs hup v
    have h0 (j : Fin pos.length) : ∑ a, coeffs a * feature pos a j = 0 := by
      simpa [U] using congrFun hup (Sum.inl j)
    have h1 (j : Fin n) : ∑ a, coeffs a * extra a j = 0 := by
      simpa [U] using congrFun hup (Sum.inr j)
    obtain ⟨hn, hcS⟩ := ker coeffs h0 h1
    let c : Mask → ℚ := fun a => ∑ b : S, if b.val = a then coeffs b else 0
    have hsum (t : Mask) : (∑ a, c a * inc t a) = ∑ b : S, coeffs b * inc t b := collapse _ _ _
    have coff (a : Mask) (ha : a ∉ S) : c a = 0 := by
      apply Finset.sum_eq_zero; intro b _
      have hh : b.val ≠ a := fun h => ha (h ▸ b.2)
      simp [hh]
    have con (a : S) : c a = coeffs a := by
      change (∑ b : S, if b.val = a.val then coeffs b else 0) = _
      simp
    have hcov (a : Mask) (ha : c a ≠ 0) : ap a = true ∧ short a = true := by
      by_cases hm : a ∈ S
      · let b : S := ⟨a,hm⟩
        exact hcS b (fun h => ha ((con b).trans h))
      · exact False.elim (ha (coff a hm))
    have hann (t : Mask) (ht : t ∈ pos ∨ t ∈ neg) : ∑ a, c a * inc t a = 0 := by
      rw [hsum]; obtain h | h := ht
      · obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem h; exact h0 ⟨i,hi⟩
      · obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem h; exact hn ⟨i,hi⟩
    have eqn := resolve c hcov hann
    let z := fun p => c (five p)
    have hz : ∀ a ∉ F, proj z a = 0 := by
      intro a ha; rw [← eqn a]; exact coff _ (fun hm => ha (hSF hm))
    have hall := center_elim F hg hne z hz
    rw [← con v, eqn]; change proj z _ = 0; simp [proj,hall]
  have h := hli.fintype_card_le_finrank
  rw [Fintype.card_coe, Module.finrank_pi, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
  exact h

/-- A short progression is allowed to have zero diagonal score; every other
member must have positive score. Only the off-diagonal intersections need score zero. -/
theorem local_rank_bound {F S : Finset Mask} (hSF : S ⊆ F)
    (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false)
    (hdiag : ∀ a ∈ S, (ap a = true ∧ short a = true) ∨ 0 < score a)
    (hoff : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → score (a &&& b) = 0) : S.card ≤ 92 := by
  apply local_aux hSF hg hne (n := 0) (fun _ _ => 0)
  intro c hu _
  let d : S → ℚ := fun a => score a
  have hnn (a : S) : 0 ≤ d a := by
    rcases hdiag a a.2 with ⟨h,s⟩ | h
    · simp [d,score_good s h]
    · change 0 ≤ (score a : ℚ); exact_mod_cast h.le
  have hh (a b : S) : (∑ j, feature pos a j * feature pos b j) = (∑ j, feature neg a j * feature neg b j) + if a = b then d a else 0 := by
    rw [gram]; by_cases e : a = b
    · subst b; simp [d]
    · have h := hoff a a.2 b b.2 (fun h => e (Subtype.ext h)); simp [e,h]
  obtain ⟨hn,hd⟩ := gram_kernel (fun a : S => feature pos a) (fun a : S => feature neg a) d c hnn hh hu
  refine ⟨hn, ?_⟩; intro a hc
  rcases hdiag a a.2 with h | h
  · exact h
  · exact False.elim (hc (hd a (by change 0 < (score a : ℚ); exact_mod_cast h)))

/-- After any three deletions a putative 96-member nonstar must retain a bad
member or a pair with a long intersection. -/
theorem obstruction_after_deletion {F : Finset Mask}
    (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false) (hsize : 96 ≤ F.card)
    (D : Finset Mask) (hd : D.card ≤ 3) :
    (∃ a ∈ F \ D, ap a = true ∧ short a = false) ∨
    (∃ a ∈ F \ D, ap a = false ∧ score a ≤ 0) ∨
    (∃ a ∈ F \ D, ∃ b ∈ F \ D, a ≠ b ∧ short (a &&& b) = false) := by
  classical
  by_contra! h
  obtain ⟨hA,hB,hP⟩ := h
  have hSF : F \ D ⊆ F := Finset.sdiff_subset
  have hbound := local_rank_bound hSF hg hne (fun a ha => by
    cases e : ap a with
    | true => exact Or.inl ⟨rfl, by simpa using hA a ha e⟩
    | false => exact Or.inr (by simpa using hB a ha e))
    (fun a ha b hb hab => score_good (by simpa using hP a ha b hb hab) (hg a (hSF ha) b (hSF hb) hab))
  have hh := Finset.le_card_sdiff D F
  omega


/-- Signed interpolation of intersection scores on a family of AP masks. -/
def correctedScore {n : ℕ} (t : Fin n → Mask) (w : Fin n → ℚ) (a : Mask) : ℚ :=
  (score a : ℚ) + ∑ i, w i * inc (t i) a

private theorem local_adjusted {F S : Finset Mask} (hSF : S ⊆ F)
    (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false) {n : ℕ} (t : Fin n → Mask) (w : Fin n → ℚ)
    (hdiag : ∀ a ∈ S, (ap a = true ∧ short a = true ∧ correctedScore t w a = 0) ∨ 0 < correctedScore t w a)
    (hoff : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → correctedScore t w (a &&& b) = 0) : S.card ≤ 92 + n := by
  classical
  apply local_aux hSF hg hne (fun a j => inc (t j) a)
  intro c hu ha
  let left := fun (a : S) (i : Fin n) => ((w i + 1) / 2) * inc (t i) a
  let right := fun (a : S) (i : Fin n) => ((w i - 1) / 2) * inc (t i) a
  let u := fun a : S => Sum.elim (feature pos a) (left a)
  let v := fun a : S => Sum.elim (feature neg a) (right a)
  let d := fun a : S => correctedScore t w a
  have hd (a : S) : 0 ≤ d a := by
    rcases hdiag a a.2 with ⟨_,_,h⟩ | h
    · exact h.ge
    · exact h.le
  have hzi : ∀ i, (∑ a, c a * u a i) = 0 := by
    intro i; cases i with
    | inl i => exact hu i
    | inr i =>
      change ∑ a, c a * (((w i + 1) / 2) * inc (t i) a) = 0
      simp_rw [mul_left_comm (c _) ((w i + 1) / 2), ← Finset.mul_sum, ha]; simp
  have hh (a b : S) : (∑ j, u a j * u b j) = (∑ j, v a j * v b j) + if a = b then d a else 0 := by
    have hterm (k : Fin n) : left a k * left b k = right a k * right b k + w k * inc (t k) (a.val &&& b.val) := by
      rw [← inc_inter]; dsimp [left,right]; ring
    have hq : correctedScore t w (a.val &&& b.val) = if a = b then d a else 0 := by
      by_cases e : a = b
      · subst b; simp [d]
      · simpa [e] using hoff a a.2 b b.2 (fun h => e (Subtype.ext h))
    rw [← hq]; simp only [u,v, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hterm, Finset.sum_add_distrib, gram, correctedScore]; ring
  obtain ⟨hv, hk⟩ := gram_kernel u v d c hd hh hzi
  refine ⟨fun j => hv (.inl j), ?_⟩
  intro a hca
  rcases hdiag a a.2 with ⟨h,s,_⟩ | h
  · exact ⟨h,s⟩
  · exact False.elim (hca (hk a h))

/-- A long progression is an AP mask which contains seven terms. -/
def longProgression (a : Mask) : Prop := ap a = true ∧ short a = false

private def cost (a : Mask) : ℚ := -(score a : ℚ)
private lemma cost_pos {a : Mask} (ha : longProgression a) : 0 < cost a := by
  have ht : ∀ i : Fin apMasks.length, short apMasks[i] = false → score apMasks[i] < 0 := by decide +kernel
  obtain ⟨h,s⟩ := ha
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem (List.contains_iff_mem.mp h : a ∈ apMasks)
  unfold cost; apply neg_pos.mpr; exact_mod_cast ht ⟨i,hi⟩ s
private lemma cost_mono {a b : Mask} (ha : longProgression a) (hb : longProgression b)
    (he : sub a b = true) : cost a ≤ cost b := by
  have ht : ∀ i : Fin apMasks.length, short apMasks[i] = false →
      ∀ j : Fin apMasks.length, short apMasks[j] = false → sub apMasks[i] apMasks[j] = true →
      score apMasks[j] ≤ score apMasks[i] := by decide +kernel
  obtain ⟨h,s⟩ := ha; obtain ⟨k,t⟩ := hb
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem (List.contains_iff_mem.mp h : a ∈ apMasks)
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem (List.contains_iff_mem.mp k : b ∈ apMasks)
  unfold cost; apply neg_le_neg; exact_mod_cast ht ⟨i,hi⟩ s ⟨j,hj⟩ t he

private theorem sub_chain {p q r : Mask} (h : sub p q = true) (k : sub q r = true) : sub p r = true := by
  simp only [sub, beq_iff_eq] at *
  calc
    p &&& r = (p &&& q) &&& r := by rw [h]
    _ = p &&& (q &&& r) := BitVec.and_assoc ..
    _ = p := by rw [k,h]

private theorem inc_le {a b t : Mask} (h : sub a b = true) : inc t a ≤ inc t b := by
  by_cases e : sub t a = true
  · simp only [inc,e,sub_chain e h,ite_true,le_refl]
  · by_cases f : sub t b = true <;> simp [inc,e,f]
private theorem inc_nonneg (p a : Mask) : 0 ≤ inc p a := by unfold inc; split <;> norm_num
private theorem inc_short {p a : Mask} (h : longProgression p) (hs : short a = true) : inc p a = 0 := by
  have hh := short_inter_left (b := p) hs
  by_contra! he
  have e : sub p a = true := by by_contra hu; simp [inc,hu] at he
  rw [BitVec.and_comm] at hh; simp only [sub,beq_iff_eq] at e; rw [e,h.2] at hh; contradiction
private theorem inc_self (p : Mask) : inc p p = 1 := by simp [inc,sub]
private theorem inc_lt {p q : Mask} (h : p.toNat < q.toNat) : inc q p = 0 := by
  by_cases e : sub q p = true
  · simp only [sub,beq_iff_eq] at e
    have hl : q.toNat ≤ p.toNat := by rw [←e]; exact Nat.and_le_right
    omega
  · simp [inc,e]

/-- Three prescribed long progression masks cannot cover every long pairwise
intersection of a 96-member nonstar with healthy diagonal scores. -/
theorem three_pattern_bound {F S : Finset Mask} (hSF : S ⊆ F)
    (hg : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → ap (a &&& b) = true)
    (hne : ∀ x : Fin 14, ∃ b ∈ F, b.getLsbD x = false)
    (hdiag : ∀ a ∈ S, (ap a = true ∧ short a = true) ∨ 0 < score a)
    (p q r : Mask) (hp : longProgression p) (hq : longProgression q) (hr : longProgression r)
    (hpq : p.toNat < q.toNat) (hqr : q.toNat < r.toNat)
    (hcover : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → short (a &&& b) = true ∨ a &&& b = p ∨ a &&& b = q ∨ a &&& b = r) : S.card ≤ 95 := by
  let w₁ := cost p
  let w₂ := cost q - w₁ * inc p q
  let firstTwo := fun a => w₁ * inc p a + w₂ * inc q a
  let w₃ := cost r - firstTwo r
  let t : Fin 3 → Mask := ![p,q,r]
  let w : Fin 3 → ℚ := ![w₁,w₂,w₃]
  have f₁ : 0 ≤ w₁ := (cost_pos hp).le
  have f₂ : 0 ≤ w₂ := by
    by_cases e : sub p q = true
    · simpa only [w₂,w₁,inc,e,ite_true,mul_one,sub_nonneg] using cost_mono hp hq e
    · simpa [w₂,inc,e] using (cost_pos hq).le
  have prefpos (a : Mask) : 0 ≤ firstTwo a := add_nonneg (mul_nonneg f₁ (inc_nonneg _ _)) (mul_nonneg f₂ (inc_nonneg _ _))
  have prefmono {a b : Mask} (h : sub a b = true) : firstTwo a ≤ firstTwo b :=
    add_le_add (mul_le_mul_of_nonneg_left (inc_le h) f₁) (mul_le_mul_of_nonneg_left (inc_le h) f₂)
  have health (a : Mask) : 0 ≤ firstTwo a + w₃ * inc r a := by
    by_cases e : sub r a = true
    · have hh := prefmono e; have hn := cost_pos hr
      simp only [w₃,inc,e,ite_true,mul_one]; linarith
    · simpa [inc,e] using prefpos a
  have formula (a : Mask) : correctedScore t w a = (score a : ℚ) + (firstTwo a + w₃ * inc r a) := by
    simp only [correctedScore, Fin.sum_univ_three]; dsimp [firstTwo,t,w]
  have shorts {a : Mask} (s : short a = true) (u : ap a = true) : correctedScore t w a = 0 := by
    rw [formula, score_good s u]; simp [firstTwo,inc_short hp s,inc_short hq s,inc_short hr s]
  have ep : correctedScore t w p = 0 := by
    rw [formula]; simp [firstTwo, inc_self, inc_lt hpq, inc_lt (hpq.trans hqr), w₁, cost]
  have eq : correctedScore t w q = 0 := by
    rw [formula]; simp [firstTwo, inc_self, inc_lt hqr, w₂,cost]
  have er : correctedScore t w r = 0 := by rw [formula]; simp [w₃, inc_self, cost]
  apply local_adjusted hSF hg hne t w
  · intro a ha; rcases hdiag a ha with ⟨u,s⟩ | h
    · exact Or.inl ⟨u,s,shorts s u⟩
    · exact Or.inr (by rw [formula]; exact add_pos_of_pos_of_nonneg (by exact_mod_cast h) (health _))
  · intro a ha b hb hab
    rcases hcover a ha b hb hab with hs | e | e | e
    · exact shorts hs (hg _ (hSF ha) _ (hSF hb) hab)
    · rwa [e]
    · rwa [e]
    · rwa [e]

end E272
